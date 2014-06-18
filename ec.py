#!/usr/bin/python3
# -*- coding: utf-8 -*-
##### ECDSA NIST CURVE P-521 #####

import os, hashlib, base64
PAD = lambda s:(len(s)%2)*'0'+s[2:]

def i2b(x, n=1):
    "int to bytes with n padding"
    z = bytes.fromhex(PAD(hex(x)))
    return ((n-len(z))%n)*bytes.fromhex('00') + z

def b2i(x):
    "bytes to int"
    return int.from_bytes(x, 'big')

def b64toi(c):
    "base64 to int"
    if c == '': return 0
    return int.from_bytes(base64.urlsafe_b64decode(c + b'='*((4-(len(c)%4))%4)), 'big')

def H(*tab):
    "hash"
    return int(hashlib.sha256(b''.join(tab)).hexdigest(), 16)

def random_b64():
    "20 chars url safe"
    return base64.urlsafe_b64encode(bytes.fromhex(hashlib.sha1(os.urandom(32)).hexdigest()[:30]))    

_B = b'UZU-uWGOHJofkpohoLaFQO6i2nJbmbMV87i0iZGO8QnhVhk5Uex-k3sWUsC9O7G_BzVz34g9LDTx70Uf1GtQPwA'
_GX = b'xoWOBrcEBOnNnj7LZiOVtEKcZIE5BT-1Ifgor2BrTT26oUted-_nWSj-HcEnov-o3jNIs8GFakKb-X5-McLlvWY'
_GY = b'ARg5KWp4mjvABFyKX7QsfRvZmPVESVebRGgXr70XJz5mLJfucple9CZAxVC5AT-tB2E1PHCGonLCQIi-lHaf0WZQ'
_R = b'Af' + b'_'*42 + b'-lGGh4O_L5Zrf8wBSPcJpdA7tcm4iZxHrrtvtx6ROGQJ'

class Curve(): 
    "The curve of points satisfying y^2 = x^3 + a*x + b (mod p)"
    def __init__(self, p, a, b): self.p, self.a, self.b = p, a, b
    def has_pt(self, x, y): return (y*y - (x*x*x + self.a*x + self.b)) % self.p == 0

c521 = Curve(b64toi(b'Af' + b'_'*86), -3, b64toi(_B))

class Point():
    def __init__(self, curve, x, y, order = None):
        self.curve, self.x, self.y, self.order = curve, x, y, order
    def __add__(self, other):
        if other == INFINITY: return self
        if self == INFINITY: return other
        if self.x == other.x:
            if (self.y + other.y) % self.curve.p == 0: return INFINITY
            else: return self.double()
        p = self.curve.p
        l = ((other.y - self.y) * inverse_mod(other.x - self.x, p)) % p
        x3 = (l*l - self.x - other.x) % p
        y3 = (l*(self.x - x3) - self.y) % p
        return Point(self.curve, x3, y3)
    def __mul__(self, e):
        if self.order: e = e % self.order
        if e == 0 or self == INFINITY: return INFINITY
        e3, neg_self = 3*e, Point(self.curve, self.x, -self.y, self.order)
        i = 1 << (len(bin(e3))-4)
        result = self
        while i > 1:
            result = result.double()
            if (e3 & i) != 0 and (e & i) == 0: result = result + self
            if (e3 & i) == 0 and (e & i) != 0: result = result + neg_self
            i //= 2
        return result
    def __rmul__(self, other): return self * other
    def double(self):
        if self == INFINITY: return INFINITY
        p, a = self.curve.p, self.curve.a
        l = ((3 * self.x * self.x + a) * inverse_mod(2 * self.y, p)) % p
        x3 = (l*l - 2 * self.x) % p
        y3 = (l*(self.x - x3) - self.y) % p
        return Point(self.curve, x3, y3)

INFINITY = Point(None, None, None)  

class ecdsa:
    def __init__(self):
        self.gen = Point(c521, b64toi(_GX), b64toi(_GY), b64toi(_R))
        self.pkgenerator, self.pkorder = self.gen, self.gen.order

    def generate(self):
        secexp = randrange(self.gen.order)
        pp = self.gen*secexp
        self.pt, n = pp, self.gen.order
        if not n: raise 'Generator point must have order!'
        if not n * pp == INFINITY: raise 'Bad Generator point order!'
        if pp.x < 0 or n <= pp.x or pp.y < 0 or n <= pp.y: raise 'Out of range!'
        self.privkey = secexp

    def verify(self, sig, data):
        r, s, G, n = b2i(sig[:66]), b2i(sig[66:]), self.pkgenerator, self.pkorder
        if r < 1 or r > n-1 or s < 1 or s > n-1: return False
        c = inverse_mod(s, n)
        u1, u2 = (H(data) * c) % n, (r * c) % n
        z = u1 * G + u2 * self.pt
        return z.x % n == r

    def sign(self, data):
        rk, G, n = randrange(self.pkorder), self.pkgenerator, self.pkorder
        k = rk % n
        p1 = k * G
        r = p1.x
        s = (inverse_mod(k, n) * (H(data) + (self.privkey * r) % n)) % n
        assert s != 0 and r != 0
        return i2b(r, 66) + i2b(s, 66)

    def find_offset(self, x):
        p, a, b = b64toi(b'Af' + b'_'*86), -3, b64toi(_B)
        for offset in range(64):
            Mx = x + offset
            My2 = pow(Mx, 3, p) + a * Mx + b % p
            My = pow(My2, (p+1)//4, p)
            if c521.has_pt(Mx, My): return offset, My
        raise Exception('Y Not found')

    def encrypt(self, data):
        p, a, b, G, x = b64toi(b'Af' + b'_'*86), -3, b64toi(_B), self.pkgenerator, int.from_bytes(data, 'big')
        offset, y = self.find_offset(x)
        M, k = Point(c521, x + offset, y), randrange(self.pkorder)        
        p1, p2 = k*G, M + k*self.pt
        o1, o2 = p1.y&1, p2.y&1
        return bytes('%02X' % ((o1<<7) + (o2<<6) + offset), 'ascii') + i2b(p1.x, 66) + i2b(p2.x, 66)

    def decrypt(self, enctxt):
        oo, x1, x2 =  int(enctxt[:2], 16), b2i(enctxt[2:68]), b2i(enctxt[68:])
        o1, o2, offset, p, a, b = (oo & 0x80)>>7,(oo & 0x40)>>6, oo & 0x3F, b64toi(b'Af' + b'_'*86), -3, b64toi(_B)
        z1, z2 = pow(x1, 3, p) + a * x1 + b % p, pow(x2, 3, p) + a * x2 + b % p
        t1, t2 = pow(z1, (p+1)//4, p), pow(z2, (p+1)//4, p)
        y1, y2 = t1 if int(o1) == t1&1 else (-t1)%p, t2 if int(o2) == t2&1 else (-t2)%p
        p1, p2 = Point(c521, x1, - y1), Point(c521, x2, y2)
        u = p2 + self.privkey * p1
        return i2b(u.x-offset)

def inverse_mod(a, m):
    if a < 0 or m <= a: a = a % m
    c, d = a, m
    uc, vc, ud, vd = 1, 0, 0, 1
    while c != 0:
        q, c, d = divmod(d, c) + (c,)
        uc, vc, ud, vd = ud - q*uc, vd - q*vc, uc, vc
    if ud > 0: return ud
    else: return ud + m

def randrange(order):
    byts = (1+len('%x' % order))//2
    cand = b2i(os.urandom(byts))
    return cand//2 if cand >= order else cand

if __name__ == '__main__':
    k = ecdsa()
    k.generate()
    msg = b'Hello World!'
    print (b2i(k.sign(msg)))
    assert k.verify(k.sign(msg), msg) and msg == k.decrypt(k.encrypt(msg))

# End ⊔net!

