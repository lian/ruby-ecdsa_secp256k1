## /home/chris/mess/2009/08/e.rb
require 'zlib'

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
        INF
      else
        double
      end
    else
      p = curve.p
      l = ((other.y - y) * NumberTheory.inverse_mod(other.x - x, p)) % p
      x3 = (l * l - x - other.x) % p
      y3 = (l * (x - x3) - y) % p
      Point.new(curve, x3, y3)
    end
  end

  def *(other)
    e = other
    e %= order  if order
    return INF  if e == 0 || self == INF
    
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
    
    c, d = a, m
    uc, vc, ud, vd = 1, 0, 0, 1
    while c != 0
      q, c, d = d.divmod(c) << c
      uc, vc, ud, vd = ud - q*uc, vd - q*vc, uc, vc
    end

    if ud > 0
      ud
    else
      ud + m
    end
  end
end

class PublicKey < Struct.new(:generator, :point)
  def initialize(generator, point)
    super
    @curve = generator.curve
  end

  def verifies(hash, signature)
    g = generator
    n = g.order
    r = signature.r
    s = signature.s
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

  def to_s(pubkey)
    p Math.log(r)/Math.log(2)
    p Math.log(s)/Math.log(2)
    p Math.log(pubkey.point.x)/Math.log(2)
    p Math.log(pubkey.point.y)/Math.log(2)
    p [r, s, pubkey.point.x, pubkey.point.y].pack("w*").size
    [[r, s, pubkey.point.x, pubkey.point.y].pack("w*")].pack("m*")
  end
end

class PrivateKey < Struct.new(:public_key, :secret_multiplier)
  def sign(hash, nonce)
    g = public_key.generator
    n = g.order
    k = nonce % n
    p1 = g * k
    r = p1.x
    raise "amazingly unlucky random number r"  if r == 0
    s = (NumberTheory.inverse_mod(k, n) * (hash + (secret_multiplier * r) % n)) % n
    raise "amazingly unlucky random number s"  if s == 0
    return Signature.new(r, s)
  end
end

# NIST Curve P-192:
_p = 6277101735386680763835789423207666416083908700390324961279
_r = 6277101735386680763835789423176059013767194773182842284081
# s = 0x3045ae6fc8422f64ed579528d38120eae12196d5
# c = 0x3099d2bbbfcb2538542dcd5fb078b6ef5f3d6fe2c745de65
_b = 0x64210519e59c80e70fa7e9ab72243049feb8deecc146b9b1
_Gx = 0x188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012
_Gy = 0x07192b95ffc8da78631011ed6b24cdd573f977a11e794811

curve_192 = Curve.new( _p, -3, _b )
generator_192 = Point.new( curve_192, _Gx, _Gy, _r )


  g = generator_192
  n = g.order
  secret = rand(n) + 1
  pubkey = PublicKey.new( g, g * secret )
  privkey = PrivateKey.new( pubkey, secret )

p [pubkey, privkey]

  hash = rand(n) + 1
  signature = privkey.sign(hash, rand(n) + 1)

p hash
p signature
puts signature.to_s(pubkey)

p pubkey.verifies(hash, signature)
p pubkey.verifies(hash-1, signature)

