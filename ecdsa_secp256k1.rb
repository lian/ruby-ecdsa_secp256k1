require 'securerandom'

class Curve < Struct.new(:p, :a, :b)
  def contains_point(x, y)
    return (y*y - (x*x*x + a*x + b)) % p == 0
  end
end

class Point < Struct.new(:curve, :x, :y, :order)
  INF = Point.new(nil, nil, nil)

  def +(other)
    return self  if other == INF
    return other if self  == INF

    if x == other.x
      if (y+other.y) % p == 0
        return INF
      else
        return double
      end
    end

    p = curve.p
    l = ((other.y - y) * NumberTheory.inverse_mod(other.x - x, p)) % p
    x3 = (l * l - x - other.x) % p
    y3 = (l * (x - x3) - y) % p
    Point.new(curve, x3, y3)
  end

  def *(other)
    e = other
    e %= order  if order
    return INF  if e == 0 || self == INF
    #raise "foo" unless e > 0
    
    e3 = 3 * e
    neg_self = Point.new(curve, x, -y, order)
    i = leftmost_bit(e3) / 2
    r = self
    while i > 1
      r = r.double
      r += self      if (e3 & i) != 0 && (e & i) == 0
      r += neg_self  if (e3 & i) == 0 && (e & i) != 0
      i = i/2
    end
    
    r
  end

  def double
    #return INF if self == INF
    p = curve.p; a = curve.a
    l = ((3*x * x + a) * NumberTheory.inverse_mod(2*y, p)) % p
    x3 = (l * l - 2*x) % p
    y3 = (l * (x-x3) - y) % p
    return Point.new(curve, x3, y3)
  end

  private
  def leftmost_bit(n)
    r = 1
    r <<= 1  while r <= n
    return r >> 1
  end

end

module NumberTheory
  def self.inverse_mod(a, m)
    a = a % m  if a < 0 || m <= a 

    # From Ferguson and Schneier, roughly:
    c, d, uc, vc, ud, vd = a, m, 1, 0, 0, 1
    while c != 0
      q, c, d = d.divmod(c) << c
      uc, vc, ud, vd = ud - q*uc, vd - q*vc, uc, vc
    end

    ud > 0 ? ud : ud + m
  end
end

class PublicKey < Struct.new(:generator, :point)
  def to_s
    "04%064x%064x" % [point.x, point.y]
  end

  def initialize(generator, point)
    super
    @curve = generator.curve
    n = generator.order
    raise "Generator point must have order." unless n
    if (point.x < 0) or (n <= point.x) or (point.y < 0) or (n <= point.y)
      raise "Generator point has x or y out of range."
    end
  end

  def verifies(hash, signature)
    g, n = generator, generator.order
    r, s = signature.r, signature.s
    return false  if r < 1 || r > n-1 || s < 1 || s > n-1
    c = NumberTheory.inverse_mod(s, n)
    u1 = (hash * c) % n
    u2 = (r * c) % n
    xy = g * u1 + point * u2
    v = xy.x % n
    v == r
  end
end

class Signature < Struct.new(:r, :s)
  def parse(str)
    new(*str.unpack("m*").first.unpack("w2"))
  end

  def to_s(pubkey=nil)
    [r, s].pack("w*").unpack("H*")[0]
  end
end

class PrivateKey < Struct.new(:public_key, :secret_multiplier)
  def to_s
    "%064x" % secret_multiplier
  end

  # uncompressed DER format in binary
  def to_der
    # private keys are 279 bytes long (see crypto/ec/cec_asn1.c)
    [ '308201130201010420' +
      '%064x' % secret_multiplier +
      'a081a53081a2020101302c06072a8648ce3d0101022100' +
      '%064x' % public_key.generator.curve.p +
      '3006040100040107044104' +
      '%064x' % public_key.generator.x +
      '%064x' % public_key.generator.y +
      '022100' +
      '%064x' % public_key.generator.order +
      '020101a14403420004' +
      '%064x' % public_key.point.x +
      '%064x' % public_key.point.y ].pack("H*")
  end

  # # compressed DER format in binary
  # def to_der_compressed
  #   [ '06052b8104000a30740201010420' +
  #     '%064x' % secret_multiplier +
  #     'a00706052b8104000aa14403420004' +
  #     '%064x' % public_key.point.x +
  #     '%064x' % public_key.point.y ].pack("H*")
  # end

  def sign(hash, nonce=nil)
    g, n = public_key.generator, public_key.generator.order
    nonce = SecureRandom.random_number(n) + 1 unless nonce
    k = nonce % n
    p1 = g * k
    r = p1.x
    raise "amazingly unlucky random number r"  if r == 0
    s = (NumberTheory.inverse_mod(k, n) * (hash + (secret_multiplier * r) % n)) % n
    raise "amazingly unlucky random number s"  if s == 0
    return Signature.new(r, s)
  end
end

module Secp256k1
  P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
  A  = 0x0000000000000000000000000000000000000000000000000000000000000000
  B  = 0x0000000000000000000000000000000000000000000000000000000000000007
  Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
  Gy = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
  R  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
  Curve     = Curve.new(P, A, B)
  Generator = Point.new(Curve, Gx, Gy, R)

  def self.nonce; SecureRandom.random_number(Generator.order) + 1; end

  def self.generate(secret=nil)
    g = Generator
    secret  = nonce unless secret
    pubkey  = PublicKey.new( g, g * secret )
    privkey = PrivateKey.new( pubkey, secret )
    [pubkey, privkey]
  end
end


pubkey, privkey = Secp256k1.generate

hash = Secp256k1.nonce
signature = privkey.sign(hash)

p [privkey.to_s, pubkey.to_s]
p hash.to_s(16)
p signature.to_s

p privkey.to_der.size
p privkey.to_der.unpack("H*")[0]

require 'openssl'
p OpenSSL::PKey::EC.new(privkey.to_der).private_key.to_i.to_s(16).rjust(64, '0')
p OpenSSL::PKey::EC.new(privkey.to_der).public_key.to_bn.to_i.to_s(16).rjust(130, '0')

p pubkey.verifies(hash, signature)
p pubkey.verifies(hash-1, signature)
