#!/usr/bin/python3
# -*- coding: utf-8 -*-
# Welcome to ⊔net!
#-----------------------------------------------------------------------------
#  © Copyright 2013 ⊔Foundation
#    This file is part of ⊔net.
#
#    ⊔net is free software: you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation, either version 3 of the License, or
#    (at your option) any later version.
#
#    ⊔net is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with ⊔net.  If not, see <http://www.gnu.org/licenses/>.
#
#    Acknowledgements:
#    * ECDSA has been adapted to Python3 and simplified for 512P curve only 
#      code inspired from:
#      Brian Warner  
#    * The PyCrypt library is far too complex for our needs so we used a code 
#      for AES inspired from:
#      Josh Davis ( http://www.josh-davis.org )
#      Laurent Haan (http://www.progressive-coding.com)
#    * QRcode is extented to PDF and SVG from the inspired code of:
#      Sam Curren (porting from Javascript)
#    * Encryption with ECC use an idea of jackjack-jj on github
#-----------------------------------------------------------------------------

import re, os, sys, urllib.parse, hashlib, http.client, base64, dbm.ndbm, datetime, functools, subprocess, time, smtplib, operator, random, getpass

__digest__ = base64.urlsafe_b64encode(hashlib.sha1(open(__file__, 'r', encoding='utf8').read().encode('utf8')).digest())[:10]
__app__    = os.path.basename(__file__)[:-3]
__dfprt__  = 80
__base__   = '/%s/%s_%s/' % (__app__,__app__,__dfprt__)
__ppc__    = 'pingpongcash'
__email__  = 'info@%s.fr' % __ppc__
__url__    = 'http://%s.fr' % __ppc__

_SVGNS     = 'xmlns="http://www.w3.org/2000/svg"'

##### ENCODING #####
PAD = lambda s:(len(s)%2)*'0'+s[2:]

def i2b(x, n=1):
    "int to bytes with n padding"
    z = bytes.fromhex(PAD(hex(x)))
    return ((n-len(z))%n)*bytes.fromhex('00') + z

def b2i(x):
    "bytes to int"
    return int.from_bytes(x, 'big')

def s2b(x, n=1):
    "signed int to bytes with n padding"
    z = bytes.fromhex(PAD(hex(x + (1<<(8*n-1)))))
    return ((n-len(z))%n)*bytes.fromhex('00') + z

def b2s(x, n=1):
    "signed bytes to int"
    return int.from_bytes(x, 'big') - (1<<(8*n-1)) 

def itob64(n):
    "transform int to base64"
    return re.sub(b'=*$', b'', base64.urlsafe_b64encode(bytes.fromhex(PAD(hex(n)))))

def b64toi(c):
    "transform base64 to int"
    if c == '': return 0
    return int.from_bytes(base64.urlsafe_b64decode(c + b'='*((4-(len(c)%4))%4)), 'big')

def btob64(c):
    "bytes to base64"
    return base64.urlsafe_b64encode(c).decode('ascii').strip('=')

def b64tob(c):
    "base64 to bytes"
    return base64.urlsafe_b64decode(c + b'='*((4-(len(c)%4))%4))

def H(*tab):
    "hash"
    return int(hashlib.sha1(b''.join(tab)).hexdigest(), 16)

def datencode(n=0):
    "4 chars"
    return i2b(int(time.mktime(time.gmtime()) + 3600*24*n), 4)

def datdecode(tt):
    "4 chars"
    return time.strftime('%d/%m/%y %H:%M:%S', time.localtime(float(b2i(tt))))

def is_after(d1, d2): 
    "_"
    return datdecode(d1) > datdecode(d2)

def random_b64():
    "20 chars url safe"
    return base64.urlsafe_b64encode(bytes.fromhex(hashlib.sha1(os.urandom(32)).hexdigest()[:30]))    

def hcode(m, s=10):
    "_"
    return (hashlib.sha1(m.encode('utf8')).digest())[:s]

def valencode(xi, p1, pf):
    "xi:7p1:15pf:26"
    assert (p1 <= pf or xi==0) and xi<=100 and p1<(1<<15) and pf<(1<<26)
    return i2b((xi<<41) + (p1<<26) + pf, 6)

def valdecode(code):
    "xi:7p1:15pf:26"
    e = int.from_bytes(code, 'big')
    return ((e>>41) & 0x7F), ((e>>26) & 0x7FFF), (e & 0x3FFFFFF)

##### ECDSA NIST CURVE P-521 #####

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

def inverse_mod(a, m):
    "_"
    if a < 0 or m <= a: a = a % m
    c, d = a, m
    uc, vc, ud, vd = 1, 0, 0, 1
    while c != 0:
        q, c, d = divmod(d, c) + (c,)
        uc, vc, ud, vd = ud - q*uc, vd - q*vc, uc, vc
    if ud > 0: return ud
    else: return ud + m

def randrange(order):
    "_"
    byts = (1+len('%x' % order))//2
    cand = b2i(os.urandom(byts))
    return cand//2 if cand >= order else cand

##### LOCAL AES-256 ##### (replace PyCrypto AES)
_IV = b'ABCDEFGHIJKLMNOP'

class AES:
    sbox =  [
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
        0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
        0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
        0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
        0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
        0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
        0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
        0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
        0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
        0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
        0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
        0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
        0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
        0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
        0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
        0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16 ]

    rsbox = [
        0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
        0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
        0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
        0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
        0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
        0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
        0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
        0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
        0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
        0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
        0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
        0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
        0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
        0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
        0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
        0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d ]

    Rcon = [
        0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 
        0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 
        0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 
        0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 
        0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 
        0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 
        0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 
        0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 
        0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 
        0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 
        0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 
        0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 
        0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04,
        0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 
        0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 
        0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb ]

    def rotate(self, word):
        c = word[0]
        for i in range(3): word[i] = word[i+1]
        word[3] = c	
        return word

    def core(self, word, iteration):
        word = self.rotate(word)
        for i in range(4): word[i] = self.sbox[word[i]]
        word[0] = word[0]^self.Rcon[iteration]
        return word

    def expandKey(self, key, expandedKeySize):
        currentSize, rconIteration, t, expandedKey = 32, 1, [0]*4, [0]*expandedKeySize
        for j in range(32): expandedKey[j] = key[j]
        while currentSize < expandedKeySize:
            for k in range(4): t[k] = expandedKey[(currentSize - 4) + k]
            if currentSize % 32 == 0:
                t = self.core(t, rconIteration)
                rconIteration += 1;
            if (currentSize % 32) == 16:
                for l in range(4): t[l] = self.sbox[t[l]]
            for m in range(4):
                expandedKey[currentSize] = expandedKey[currentSize - 32] ^ t[m]
                currentSize += 1
        return expandedKey

    def addRoundKey(self, state, roundKey):
        for i in range(16): state[i] ^= roundKey[i]
        return state

    def createRoundKey(self, expandedKey, roundKeyPointer):
        return [expandedKey[roundKeyPointer+i*4+j] for j in range(4) for i in range(4)]

    def g_mult(self, a, b):
        p = 0
        for counter in range(8):
            if (b & 1) == 1: p ^= a
            if p > 0x100: p ^= 0x100
            hi_bit_set = (a & 0x80)
            a <<= 1
            if a > 0x100: a ^= 0x100
            if hi_bit_set == 0x80: a ^= 0x1b
            if a > 0x100: a ^= 0x100
            b >>= 1
            if b > 0x100: b ^= 0x100
        return p

    def subBytes(self, state):
        for i in range(16): state[i] = self.sbox[state[i]]
        return state

    def shiftRows(self, state):
        for i in range(4): state = self.shiftRow(state, i*4, i)
        return state

    def shiftRow(self, state, pointer, nbr):
        for i in range(nbr):
            tmp = state[pointer]
            for j in range(3): state[pointer + j] = state[pointer + j+1]
            state[pointer + 3] = tmp
        return state

    def mixColumns(self, state):
        column = [0]*4
        for i in range(4):
            for j in range(4): column[j] = state[(j*4)+i]
            column = self.mixColumn(column)
            for k in range(4): state[(k*4)+i] = column[k]		
        return state;

    def mixColumn(self, col):
        mult, cpy = [2,1,1,3], [0]*4
        for i in range(4): cpy[i] = col[i]
        col[0] = self.g_mult(cpy[0],mult[0]) ^ self.g_mult(cpy[3],mult[1]) ^ self.g_mult(cpy[2],mult[2]) ^ self.g_mult(cpy[1],mult[3])
        col[1] = self.g_mult(cpy[1],mult[0]) ^ self.g_mult(cpy[0],mult[1]) ^ self.g_mult(cpy[3],mult[2]) ^ self.g_mult(cpy[2],mult[3])
        col[2] = self.g_mult(cpy[2],mult[0]) ^ self.g_mult(cpy[1],mult[1]) ^ self.g_mult(cpy[0],mult[2]) ^ self.g_mult(cpy[3],mult[3])
        col[3] = self.g_mult(cpy[3],mult[0]) ^ self.g_mult(cpy[2],mult[1]) ^ self.g_mult(cpy[1],mult[2]) ^ self.g_mult(cpy[0],mult[3])
        return col
	
    def aes_round(self, state, roundKey):
        state = self.subBytes(state)
        state = self.shiftRows(state)
        state = self.mixColumns(state)
        state = self.addRoundKey(state, roundKey)
        return state
	
    def aes_main(self, state, expandedKey, nbrRounds):
        state, i = self.addRoundKey(state, self.createRoundKey(expandedKey,0)), 1
        for i in range(1, nbrRounds): state = self.aes_round(state, self.createRoundKey(expandedKey,16*i))
        state = self.subBytes(state)
        state = self.shiftRows(state)
        state = self.addRoundKey(state, self.createRoundKey(expandedKey,16*nbrRounds))
        return state
	
    def enc(self, iput, key):
        output, block, nbrRounds = [0]*16, [0]*16, 14
        expandedKeySize = (16*(nbrRounds+1))
        for i in range(4):
            for j in range(4): block[(i+(j*4))] = iput[(i*4)+j]
        expandedKey = self.expandKey(key, expandedKeySize)
        block = self.aes_main(block, expandedKey, nbrRounds)
        for k in range(4):
            for l in range(4): output[(k*4)+l] = block[(k+(l*4))]
        return output
	
    def encrypt(self, stringIn, key):
        plain, iput, output, cipher  = [], [], [], [0]*16
        cipherOut, firstRound = [], True
        if stringIn != None:
            for j in range(1+(len(stringIn)-1)//16):
                start, end = j*16, j*16+16
                if j*16+16 > len(stringIn): end = len(stringIn)
                plain = (stringIn.encode('utf8'))[start:end]
                if firstRound: output, firstRound = self.enc(_IV, key), False
                else: output = self.enc(iput, key)
                for i in range(16):
                    if len(plain)-1 < i: cipher[i] = 0 ^ output[i]
                    elif len(output)-1 < i: cipher[i] = plain[i] ^ 0
                    elif len(plain)-1 < i and len(output) < i: cipher[i] = 0 ^ 0
                    else: cipher[i] = plain[i] ^ output[i]
                for k in range(end-start): cipherOut.append(cipher[k])
                iput = output
        return base64.urlsafe_b64encode(bytes(cipherOut))

    def decrypt(self, cIn, key):
        cipher, iput, output, plain, stringOut, fround, cipherIn = [], [], [], [0]*16, '', True, [i for i in base64.urlsafe_b64decode(cIn)]
        if cipherIn != None:
            for j in range(1+(len(cipherIn)-1)//16):
                start, end = j*16, j*16+16
                if j*16+16 > len(cipherIn): end = len(cipherIn)
                cipher = cipherIn[start:end]
                if fround: output, fround = self.enc(_IV, key), False
                else: output = self.enc(iput, key)
                for i in range(16):
                    if len(output)-1 < i: plain[i] = 0 ^ cipher[i]
                    elif len(cipher)-1 < i: plain[i] = output[i] ^ 0
                    elif len(output)-1 < i and len(cipher) < i: plain[i] = 0 ^ 0
                    else: plain[i] = output[i] ^ cipher[i]
                for k in range(end-start): stringOut += chr(plain[k])
                iput = output
        return stringOut.rstrip('@');

##### QRCODE #####

ERR_COR_L, ERR_COR_M, ERR_COR_Q, ERR_COR_H = 1, 0, 3, 2
MODE_NUMBER, MODE_ALPHA_NUM, MODE_8BIT_BYTE, MODE_KANJI = 1, 2, 4, 8
MODE_SIZE_SMALL  = { MODE_NUMBER: 10, MODE_ALPHA_NUM: 9,  MODE_8BIT_BYTE: 8,  MODE_KANJI: 8,}
MODE_SIZE_MEDIUM = { MODE_NUMBER: 12, MODE_ALPHA_NUM: 11, MODE_8BIT_BYTE: 16, MODE_KANJI: 10,}
MODE_SIZE_LARGE  = { MODE_NUMBER: 14, MODE_ALPHA_NUM: 13, MODE_8BIT_BYTE: 16, MODE_KANJI: 12,}
ALPHA_NUM = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:'
TEXP = list(range(256))
TLOG = list(range(256))
for i in range(8): TEXP[i] = 1 << i
for i in range(8, 256): TEXP[i] = (TEXP[i - 4] ^ TEXP[i - 5] ^ TEXP[i - 6] ^ TEXP[i - 8])
for i in range(255): TLOG[TEXP[i]] = i
NUMBER_LENGTH = {3: 10, 2: 7, 1: 4}
RS_BLOCK_OFFSET = { ERR_COR_L: 0, ERR_COR_M: 1, ERR_COR_Q: 2, ERR_COR_H: 3 }
RS_BLOCK_TABLE = [ # L M Q H
    [1, 26, 19], [1, 26, 16], [1, 26, 13], [1, 26, 9],
    [1, 44, 34], [1, 44, 28], [1, 44, 22], [1, 44, 16],
    [1, 70, 55], [1, 70, 44], [2, 35, 17], [2, 35, 13],
    [1, 100, 80],[2, 50, 32], [2, 50, 24], [4, 25, 9],
    [1, 134, 108], [2, 67, 43], [2, 33, 15, 2, 34, 16], [2, 33, 11, 2, 34, 12], 
    [2, 86, 68], [4, 43, 27], [4, 43, 19], [4, 43, 15], 
    [2, 98, 78], [4, 49, 31], [2, 32, 14, 4, 33, 15], [4, 39, 13, 1, 40, 14], 
    [2, 121, 97], [2, 60, 38, 2, 61, 39], [4, 40, 18, 2, 41, 19], [4, 40, 14, 2, 41, 15], 
    [2, 146, 116], [3, 58, 36, 2, 59, 37], [4, 36, 16, 4, 37, 17], [4, 36, 12, 4, 37, 13], 
    [2, 86, 68, 2, 87, 69], [4, 69, 43, 1, 70, 44], [6, 43, 19, 2, 44, 20], [6, 43, 15, 2, 44, 16], 
    [4, 101, 81], [1, 80, 50, 4, 81, 51], [4, 50, 22, 4, 51, 23], [3, 36, 12, 8, 37, 13], 
    [2, 116, 92, 2, 117, 93], [6, 58, 36, 2, 59, 37], [4, 46, 20, 6, 47, 21], [7, 42, 14, 4, 43, 15], 
    [4, 133, 107], [8, 59, 37, 1, 60, 38], [8, 44, 20, 4, 45, 21], [12, 33, 11, 4, 34, 12], 
    [3, 145, 115, 1, 146, 116], [4, 64, 40, 5, 65, 41], [11, 36, 16, 5, 37, 17], [11, 36, 12, 5, 37, 13], 
    [5, 109, 87, 1, 110, 88], [5, 65, 41, 5, 66, 42], [5, 54, 24, 7, 55, 25], [11, 36, 12], 
    [5, 122, 98, 1, 123, 99], [7, 73, 45, 3, 74, 46], [15, 43, 19, 2, 44, 20], [3, 45, 15, 13, 46, 16], 
    [1, 135, 107, 5, 136, 108], [10, 74, 46, 1, 75, 47], [1, 50, 22, 15, 51, 23], [2, 42, 14, 17, 43, 15], 
    [5, 150, 120, 1, 151, 121], [9, 69, 43, 4, 70, 44], [17, 50, 22, 1, 51, 23], [2, 42, 14, 19, 43, 15], 
    [3, 141, 113, 4, 142, 114], [3, 70, 44, 11, 71, 45], [17, 47, 21, 4, 48, 22], [9, 39, 13, 16, 40, 14], 
    [3, 135, 107, 5, 136, 108], [3, 67, 41, 13, 68, 42], [15, 54, 24, 5, 55, 25], [15, 43, 15, 10, 44, 16], 
    [4, 144, 116, 4, 145, 117], [17, 68, 42], [17, 50, 22, 6, 51, 23], [19, 46, 16, 6, 47, 17], 
    [2, 139, 111, 7, 140, 112], [17, 74, 46], [7, 54, 24, 16, 55, 25], [34, 37, 13], 
    [4, 151, 121, 5, 152, 122], [4, 75, 47, 14, 76, 48], [11, 54, 24, 14, 55, 25], [16, 45, 15, 14, 46, 16], 
    [6, 147, 117, 4, 148, 118], [6, 73, 45, 14, 74, 46], [11, 54, 24, 16, 55, 25], [30, 46, 16, 2, 47, 17], 
    [8, 132, 106, 4, 133, 107], [8, 75, 47, 13, 76, 48], [7, 54, 24, 22, 55, 25], [22, 45, 15, 13, 46, 16], 
    [10, 142, 114, 2, 143, 115], [19, 74, 46, 4, 75, 47], [28, 50, 22, 6, 51, 23], [33, 46, 16, 4, 47, 17], 
    [8, 152, 122, 4, 153, 123], [22, 73, 45, 3, 74, 46], [8, 53, 23, 26, 54, 24], [12, 45, 15, 28, 46, 16], 
    [3, 147, 117, 10, 148, 118], [3, 73, 45, 23, 74, 46], [4, 54, 24, 31, 55, 25], [11, 45, 15, 31, 46, 16], 
    [7, 146, 116, 7, 147, 117], [21, 73, 45, 7, 74, 46], [1, 53, 23, 37, 54, 24], [19, 45, 15, 26, 46, 16], 
    [5, 145, 115, 10, 146, 116], [19, 75, 47, 10, 76, 48], [15, 54, 24, 25, 55, 25], [23, 45, 15, 25, 46, 16], 
    [13, 145, 115, 3, 146, 116], [2, 74, 46, 29, 75, 47], [42, 54, 24, 1, 55, 25], [23, 45, 15, 28, 46, 16], 
    [17, 145, 115], [10, 74, 46, 23, 75, 47], [10, 54, 24, 35, 55, 25], [19, 45, 15, 35, 46, 16], 
    [17, 145, 115, 1, 146, 116], [14, 74, 46, 21, 75, 47], [29, 54, 24, 19, 55, 25], [11, 45, 15, 46, 46, 16], 
    [13, 145, 115, 6, 146, 116], [14, 74, 46, 23, 75, 47], [44, 54, 24, 7, 55, 25], [59, 46, 16, 1, 47, 17], 
    [12, 151, 121, 7, 152, 122], [12, 75, 47, 26, 76, 48], [39, 54, 24, 14, 55, 25], [22, 45, 15, 41, 46, 16], 
    [6, 151, 121, 14, 152, 122], [6, 75, 47, 34, 76, 48], [46, 54, 24, 10, 55, 25], [2, 45, 15, 64, 46, 16],
    [17, 152, 122, 4, 153, 123], [29, 74, 46, 14, 75, 47], [49, 54, 24, 10, 55, 25], [24, 45, 15, 46, 46, 16],
    [4, 152, 122, 18, 153, 123], [13, 74, 46, 32, 75, 47], [48, 54, 24, 14, 55, 25], [42, 45, 15, 32, 46, 16],
    [20, 147, 117, 4, 148, 118], [40, 75, 47, 7, 76, 48], [43, 54, 24, 22, 55, 25], [10, 45, 15, 67, 46, 16],
    [19, 148, 118, 6, 149, 119], [18, 75, 47, 31, 76, 48], [34, 54, 24, 34, 55, 25], [20, 45, 15, 61, 46, 16]
]
PATTERN_POSITION_TABLE = [
    [], [6, 18], [6, 22], [6, 26], [6, 30], [6, 34],
    [6, 22, 38], [6, 24, 42], [6, 26, 46], [6, 28, 50], [6, 30, 54], [6, 32, 58], [6, 34, 62],
    [6, 26, 46, 66], [6, 26, 48, 70], [6, 26, 50, 74], [6, 30, 54, 78], [6, 30, 56, 82], [6, 30, 58, 86], [6, 34, 62, 90],
    [6, 28, 50, 72, 94], [6, 26, 50, 74, 98], [6, 30, 54, 78, 102], [6, 28, 54, 80, 106], [6, 32, 58, 84, 110], [6, 30, 58, 86, 114], [6, 34, 62, 90, 118],
    [6, 26, 50, 74, 98, 122], [6, 30, 54, 78, 102, 126], [6, 26, 52, 78, 104, 130], [6, 30, 56, 82, 108, 134],
    [6, 34, 60, 86, 112, 138], [6, 30, 58, 86, 114, 142], [6, 34, 62, 90, 118, 146],
    [6, 30, 54, 78, 102, 126, 150], [6, 24, 50, 76, 102, 128, 154], [6, 28, 54, 80, 106, 132, 158], [6, 32, 58, 84, 110, 136, 162],
    [6, 26, 54, 82, 110, 138, 166], [6, 30, 58, 86, 114, 142, 170]
]
G15 = ((1 << 10) | (1 << 8) | (1 << 5) | (1 << 4) | (1 << 2) | (1 << 1) | (1 << 0))
G18 = ((1 << 12) | (1 << 11) | (1 << 10) | (1 << 9) | (1 << 8) | (1 << 5) | (1 << 2) | (1 << 0))
G15_MASK = (1 << 14) | (1 << 12) | (1 << 10) | (1 << 4) | (1 << 1)

def BCH_type_info(data):
    d = data << 10
    while BCH_digit(d) - BCH_digit(G15) >= 0: d ^= (G15 << (BCH_digit(d) - BCH_digit(G15)))
    return ((data << 10) | d) ^ G15_MASK

def BCH_type_number(data):
    d = data << 12
    while BCH_digit(d) - BCH_digit(G18) >= 0: d ^= (G18 << (BCH_digit(d) - BCH_digit(G18)))
    return (data << 12) | d

def BCH_digit(data):
    digit = 0
    while data != 0:
        digit += 1
        data >>= 1
    return digit

def pattern_position(version):
    return PATTERN_POSITION_TABLE[version - 1]

def mask_func(pattern):
    if pattern == 0: return lambda i, j: (i + j) % 2 == 0 
    if pattern == 1: return lambda i, j: i % 2 == 0 
    if pattern == 2: return lambda i, j: j % 3 == 0
    if pattern == 3: return lambda i, j: (i + j) % 3 == 0
    if pattern == 4: return lambda i, j: (int(i / 2) + int(j / 3)) % 2 == 0
    if pattern == 5: return lambda i, j: (i * j) % 2 + (i * j) % 3 == 0
    if pattern == 6: return lambda i, j: ((i * j) % 2 + (i * j) % 3) % 2 == 0
    if pattern == 7: return lambda i, j: ((i * j) % 3 + (i + j) % 2) % 2 == 0

def length_in_bits(mode, version):
    if version < 10: mode_size = MODE_SIZE_SMALL
    elif version < 27: mode_size = MODE_SIZE_MEDIUM
    else: mode_size = MODE_SIZE_LARGE
    return mode_size[mode]

def lost_point1(modules):
    modules_count, lost_point, darkCount = len(modules), 0, 0
    for row in range(modules_count):
        for col in range(modules_count):
            sameCount, dark = 0, modules[row][col]
            for r in range(-1, 2):
                if row + r < 0 or modules_count <= row + r: continue
                for c in range(-1, 2):
                    if col + c < 0 or modules_count <= col + c: continue
                    if r == 0 and c == 0: continue
                    if dark == modules[row + r][col + c]: sameCount += 1
            if sameCount > 5: lost_point += (3 + sameCount - 5)
    for row in range(modules_count - 1):
        for col in range(modules_count - 1):
            count = 0
            if modules[row][col]: count += 1
            if modules[row + 1][col]: count += 1
            if modules[row][col + 1]: count += 1
            if modules[row + 1][col + 1]: count += 1
            if count == 0 or count == 4: lost_point += 3
    for row in range(modules_count):
        for col in range(modules_count - 6):
            if (modules[row][col]
                    and not modules[row][col + 1]
                    and modules[row][col + 2]
                    and modules[row][col + 3]
                    and modules[row][col + 4]
                    and not modules[row][col + 5]
                    and modules[row][col + 6]):
                lost_point += 40
    for col in range(modules_count):
        for row in range(modules_count - 6):
            if (modules[row][col]
                    and not modules[row + 1][col]
                    and modules[row + 2][col]
                    and modules[row + 3][col]
                    and modules[row + 4][col]
                    and not modules[row + 5][col]
                    and modules[row + 6][col]):
                lost_point += 40
    for col in range(modules_count):
        for row in range(modules_count):
            if modules[row][col]: darkCount += 1
    return lost_point + abs(100 * darkCount / modules_count / modules_count - 50) * 2

class QRData:
    def __init__(self, data, mode=None):
        if data.isdigit(): auto_mode = MODE_NUMBER
        elif re.match('^[%s]*$' % re.escape(ALPHA_NUM), data): auto_mode = MODE_ALPHA_NUM
        else: auto_mode = MODE_8BIT_BYTE
        self.mode, self.data = auto_mode if mode is None else mode, data
    def __len__(self):
        return len(self.data)
    def write(self, buffer):
        if self.mode == MODE_NUMBER:
            for i in range(0, len(self.data), 3):
                chars = self.data[i:i + 3]
                bit_length = NUMBER_LENGTH[len(chars)]
                buffer.put(int(chars), bit_length)
        elif self.mode == MODE_ALPHA_NUM:
            for i in range(0, len(self.data), 2):
                chars = self.data[i:i + 2]
                if len(chars) > 1: buffer.put(ALPHA_NUM.find(chars[0]) * 45 + ALPHA_NUM.find(chars[1]), 11)
                else: buffer.put(ALPHA_NUM.find(chars), 6)
        else:
            for c in self.data:
                buffer.put(ord(c), 8)

class BitBuffer:
    def __init__(self): self.buffer, self.length = [], 0
    def get(self, index): return ((self.buffer[int(index/8)] >> (7 - index % 8)) & 1) == 1
    def put(self, num, length): 
        for i in range(length): self.put_bit(((num >> (length - i - 1)) & 1) == 1)
    def __len__(self): return self.length
    def put_bit(self, bit):
        buf_index = self.length // 8
        if len(self.buffer) <= buf_index: self.buffer.append(0)
        if bit: self.buffer[buf_index] |= (0x80 >> (self.length % 8))
        self.length += 1

def create_bytes(buffer, rs_b):
    offset, maxDcCount, maxEcCount, totalCodeCount, dcdata, ecdata = 0, 0, 0, 0, [0] * len(rs_b), [0] * len(rs_b)
    for r in range(len(rs_b)):
        dcCount = rs_b[r].data_count
        ecCount = rs_b[r].total_count - dcCount
        maxDcCount, maxEcCount, dcdata[r] = max(maxDcCount, dcCount), max(maxEcCount, ecCount), [0] * dcCount
        for i in range(len(dcdata[r])): dcdata[r][i] = 0xff & buffer.buffer[i + offset]
        offset += dcCount
        rsPoly = Poly([1], 0) 
        for i in range(ecCount): rsPoly = rsPoly * Poly([1, TEXP[i]], 0)
        modPoly = Poly(dcdata[r], len(rsPoly) - 1) % rsPoly
        ecdata[r] = [0] * (len(rsPoly) - 1)
        for i in range(len(ecdata[r])):
            modIndex = i + len(modPoly) - len(ecdata[r])
            ecdata[r][i] = modPoly[modIndex] if (modIndex >= 0) else 0
    for b in rs_b: totalCodeCount += b.total_count
    data, index = [None] * totalCodeCount, 0
    for i in range(maxDcCount):
        for r in range(len(rs_b)):
            if i < len(dcdata[r]):
                data[index] = dcdata[r][i]
                index += 1
    for i in range(maxEcCount):
        for r in range(len(rs_b)):
            if i < len(ecdata[r]):
                data[index] = ecdata[r][i]
                index += 1
    return data

class DataOverflowError(Exception):
    pass

def create_data(version, error_correction, data_list):
    rs_b, buffer, total_data_count, PAD0, PAD1 = rs_blocks(version, error_correction), BitBuffer(), 0, 0xEC, 0x11
    for data in data_list:
        buffer.put(data.mode, 4)
        buffer.put(len(data), length_in_bits(data.mode, version))
        data.write(buffer)
    for block in rs_b: total_data_count += block.data_count
    if len(buffer) > total_data_count * 8: raise DataOverflowError()
    if len(buffer) + 4 <= total_data_count * 8: buffer.put(0, 4)
    while len(buffer) % 8: buffer.put_bit(False)
    while True:
        if len(buffer) >= total_data_count * 8: break
        buffer.put(PAD0, 8)
        if len(buffer) >= total_data_count * 8: break
        buffer.put(PAD1, 8)
    return create_bytes(buffer, rs_b)

class Poly:
    def __init__(self, num, shift):
        offset = 0
        while offset < len(num) and num[offset] == 0: offset += 1
        self.num = [0] * (len(num) - offset + shift)
        for i in range(len(num) - offset): self.num[i] = num[i + offset]
    def __getitem__(self, index):
        return self.num[index]
    def __len__(self): return len(self.num)
    def __mul__(self, e):
        num = [0] * (len(self) + len(e) - 1)
        for i in range(len(self)):
            for j in range(len(e)): num[i + j] ^= TEXP[(TLOG[self[i]] + TLOG[e[j]]) % 255]
        return Poly(num, 0)
    def __mod__(self, e):
        if len(self) - len(e) < 0: return self
        ratio, num = TLOG[self[0]] - TLOG[e[0]], [0] * len(self)
        for i in range(len(self)): num[i] = self[i]
        for i in range(len(e)): num[i] ^= TEXP[(TLOG[e[i]] + ratio) % 255]
        return Poly(num, 0) % e

class RSBlock:
    def __init__(self, total_c, data_c):
        self.total_count, self.data_count = total_c, data_c

def rs_blocks(version, error_correction):
    offset = RS_BLOCK_OFFSET[error_correction]
    rs_b, blocks = RS_BLOCK_TABLE[(version - 1) * 4 + offset], []
    for i in range(0, len(rs_b), 3):
        count, total_count, data_count = rs_b[i:i + 3]
        for j in range(count): blocks.append(RSBlock(total_count, data_count))
    return blocks

class QRCode:
    def __init__(self, data='hello', error_co=0):
        self.version, self.error_co, size, self.m, self.m_count, self.data_cache, self.data_list = None, int(error_co), 1, None, 0, None, []
        self.data_list.append(QRData(data))
        while True:
            try: self.data_cache = create_data(size, self.error_co, self.data_list)
            except: size += 1
            else:
                self.version = size
                break
        self.makeImpl(False, self.best_mask_pattern())

    def makeImpl(self, test, mask_pattern):
        self.m_count = self.version * 4 + 17
        self.m = [None] * self.m_count
        for row in range(self.m_count):
            self.m[row] = [None] * self.m_count
            for col in range(self.m_count): self.m[row][col] = None   
        self.setup_position_probe_pattern(0, 0)
        self.setup_position_probe_pattern(self.m_count - 7, 0)
        self.setup_position_probe_pattern(0, self.m_count - 7)
        self.setup_position_adjust_pattern()
        self.setup_timing_pattern()
        self.setup_type_info(test, mask_pattern)
        if self.version >= 7: self.setup_type_number(test)
        if self.data_cache is None: self.data_cache = create_data(self.version, self.error_co, self.data_list)
        self.map_data(self.data_cache, mask_pattern)

    def setup_position_probe_pattern(self, row, col):
        for r in range(-1, 8):
            if row + r <= -1 or self.m_count <= row + r: continue
            for c in range(-1, 8):
                if col + c <= -1 or self.m_count <= col + c: continue
                self.m[row + r][col + c] = True if (0 <= r and r <= 6 and (c == 0 or c == 6) or (0 <= c and c <= 6 and (r == 0 or r == 6)) or (2 <= r and r <= 4 and 2 <= c and c <= 4)) else False

    def best_mask_pattern(self):
        min_lost_point, pattern = 0, 0
        for i in range(8):
            self.makeImpl(True, i)
            lost_point = lost_point1(self.m)
            if i == 0 or min_lost_point > lost_point: min_lost_point, pattern = lost_point, i
        return pattern

    def svg(self, ox=0, oy=0, d=2, txt=''):
        o, mc = '<svg %s width="%s" height="%s">\n' % (_SVGNS, ox+d*self.m_count, oy+d*self.m_count), self.m_count
        for r in range(mc):
            k = 0
            for c in range(mc):
                if self.m[r][c]: k += 1
                elif k>0:
                    o += '<rect x="%d" y="%d" width="%d" height="%d"/>\n' % (ox+(c-k)*d, oy+r*d, k*d, d)
                    k = 0
            if k>0: o += '<rect x="%d" y="%d" width="%d" height="%d"/>\n' % (ox+(mc-k)*d, oy+r*d, k*d, d)
        if txt:
            o += '<text x="%s" y="%s" style="font-size:32;fill:gray" >%s</text>\n' % (ox, oy + 40 + d*mc, txt)
        return o + '</svg>\n'

    def pdf(self, ox=0, oy=0, d=10, size=False, color = b'0 0 0'):
        o, mc = color + b' rg ', self.m_count
        if size:
            o += bytes('q .9 .9 .9 rg BT 1 0 0 1 2 2 Tm /F1 3 Tf (%d) Tj ET Q ' % self.m_count, 'ascii')
        for r in range(mc):
            k = 0
            for c in range(mc):
                if self.m[r][c]: k += 1
                elif k>0:
                    o += bytes('%d %d %d %d re ' % (ox+(c-k)*d, oy-r*d, k*d, d), 'ascii')
                    k = 0
            if k>0: o += bytes('%d %d %d %d re ' % (ox+(mc-k)*d, oy-r*d, k*d, d), 'ascii')
        return o + b'f '

    def setup_timing_pattern(self):
        for r in range(8, self.m_count - 8):
            if self.m[r][6] != None: continue
            self.m[r][6] = (r % 2 == 0)
        for c in range(8, self.m_count - 8):
            if self.m[6][c] != None: continue
            self.m[6][c] = (c % 2 == 0)

    def setup_position_adjust_pattern(self):
        pos = pattern_position(self.version)
        for i in range(len(pos)):
            for j in range(len(pos)):
                row, col = pos[i], pos[j]
                if self.m[row][col] != None: continue
                for r in range(-2, 3):
                    for c in range(-2, 3):
                        self.m[row + r][col + c] = True if (r == -2 or r == 2 or c == -2 or c == 2 or (r == 0 and c == 0)) else False

    def setup_type_number(self, test):
        bits = BCH_type_number(self.version)
        for i in range(18): self.m[i // 3][i % 3 + self.m_count - 8 - 3] = (not test and ((bits >> i) & 1) == 1)
        for i in range(18): self.m[i % 3 + self.m_count - 8 - 3][i // 3] = (not test and ((bits >> i) & 1) == 1)

    def setup_type_info(self, test, mask_pattern):
        bits = BCH_type_info((self.error_co << 3) | mask_pattern)
        for i in range(15): 
            mod = (not test and ((bits >> i) & 1) == 1)
            if i < 6: self.m[i][8] = mod
            elif i < 8: self.m[i + 1][8] = mod
            else: self.m[self.m_count - 15 + i][8] = mod
        for i in range(15): 
            mod = (not test and ((bits >> i) & 1) == 1)
            if i < 8: self.m[8][self.m_count - i - 1] = mod
            elif i < 9: self.m[8][15 - i - 1 + 1] = mod
            else: self.m[8][15 - i - 1] = mod
        self.m[self.m_count - 8][8] = (not test) 

    def map_data(self, data, mask_pattern):
        inc, row, bitIndex, byteIndex, mask_func1 = -1, self.m_count - 1, 7, 0, mask_func(mask_pattern)
        for col in range(self.m_count - 1, 0, -2):
            if col == 6: col -= 1
            while True:
                for c in range(2):
                    if self.m[row][col - c] == None:
                        dark = False
                        if byteIndex < len(data): dark = (((data[byteIndex] >> bitIndex) & 1) == 1)
                        if mask_func1(row, col - c): dark = not dark
                        self.m[row][col - c] = dark
                        bitIndex -= 1
                        if bitIndex == -1:
                            byteIndex += 1
                            bitIndex = 7
                row += inc
                if row < 0 or self.m_count <= row:
                    row -= inc
                    inc = -inc
                    break

##### API #####

def register(name='root'):
    "_"
    pp1, pp2, cm = '', '', ''
    dv, du = dbm.open('private', 'c'), dbm.open(__base__ + 'pub', 'c')
    while bytes(name, 'utf8') in dv: name = input('Find a public name:')
    print ('Hi! \'%s\'' % name)
    while pp1 != pp2 or len(pp1) < 4:
        pp1 = getpass.getpass('Select a passphrase? ')
        pp2 = getpass.getpass('The passphrase again? ')
    print ('...wait')
    k = ecdsa()
    k.generate()
    cm = i2b(k.pt.y, 66)[-9:]
    while cm in du:
        k = ecdsa()
        k.generate()
        cm = i2b(k.pt.y, 66)[-9:]
    du[cm], dv[name], dv[cm] = i2b(k.pt.x, 66) + i2b(k.pt.y, 66)[:-9], cm, AES().encrypt('%s' % k.privkey, hashlib.sha256(pp1.encode('utf8')).digest())
    dv.close(), du.close()
    print ('Your personnal keys have been generated. Id: %s' % (btob64(cm)))
    return name    

def certif(name, value=10000):
    "_"
    pp = getpass.getpass('Root passphrase to generate certificat for \'%s\'? ' % name)
    dv, dc = dbm.open('private', 'c'), dbm.open(__base__+'crt', 'c')
    dat, k, cm, root = datencode(365), ecdsa(), dv[name], dv['root']
    k.privkey = int(AES().decrypt(dv[root], hashlib.sha256(pp.encode('utf8')).digest())) 
    msg = dat + i2b(value, 8)
    if b'_' in dc:
        assert dc[b'_'] == root
    else:
        dc[b'_'] = root
    dc[cm] = msg + k.sign(cm + msg)
    dv.close(), dc.close()

def debt(base, cm):
    "_"
    du, dc, dbt = dbm.open(base+'pub'), dbm.open(base+'crt'), 0
    if cm in dc:
        root, k = dc[b'_'], ecdsa()
        k.pt = Point(c521, b2i(du[root][:66]), b2i(du[root][66:]+root))
        if is_after(dc[cm][:4], datencode()): dbt = b2i(dc[cm][4:12]) if k.verify(dc[cm][12:], cm + dc[cm][:12]) else 0
    du.close(), dc.close()
    return dbt

def ndebt(d, cm):
    "_"
    du, dc, dbt = d['pub'], d['crt'], 0
    if cm in dc:
        #root, k = dc[b'_'], ecdsa()
        #k.pt = Point(c521, b2i(du[root][:66]), b2i(du[root][66:]+root))
        #if is_after(dc[cm][:4], datencode()): 
        #if k.verify(dc[cm][12:], cm + dc[cm][:12]):
        dbt = b2i(dc[cm][4:12])
    return dbt

def buy(src, price):
    "_"
    dv, du, dt, u, tab = dbm.open('private'), dbm.open(__base__+'pub'), dbm.open(__base__+'trx', 'c'), bytes(src, 'utf8'), []
    if u in dv:
        if balance(__base__, dv[u]) + debt(__base__, dv[u]) < price: return
    pp = getpass.getpass('Passphrase for \'%s\'? ' % src)
    for p in du.keys():
        if p != dv[u]: 
            tab.append(p)
            print ('(%d) %s' % (len(tab), btob64(p)))
    c = input('Select a recipient: ')
    dst = tab[int(c)-1]
    if u in dv and dst in du:
        cm, dat, k = dv[u], datencode(), ecdsa()
        k.privkey = int(AES().decrypt(dv[cm], hashlib.sha256(pp.encode('utf8')).digest())) 
        msg, u = dst + i2b(price, 3), dat + cm
        if u not in dt:
            dt[u] = msg + k.sign(u + msg)
            print ('transaction recorded')
    dv.close(), du.close(), dt.close()

def allcut():
    "_"
    du, dv, dc, k = dbm.open(__base__+'pub'), dbm.open('private'), dbm.open(__base__ +'crt', 'c'), ecdsa()
    pp = getpass.getpass('Passphrase for root? ')
    k.privkey = int(AES().decrypt(dv[dv['root']], hashlib.sha256(pp.encode('utf8')).digest()))
    for u in du.keys():
        if is_active(u):
            print ('...for user %s' % btob64(u))
            msg = datencode() + s2b(balance(__base__, u), 4)
            dc[b'%'+u] = msg + k.sign(u + msg)
    du.close(), dv.close(), dc.close()

def is_active(cm):
    "_"
    du, dt, k = dbm.open(__base__+'pub'), dbm.open(__base__+'trx'), ecdsa()
    for t in dt.keys():
        src, dst = t[4:], dt[t][:9]
        k.pt = Point(c521, b2i(du[src][:66]), b2i(du[src][66:]+src))
        if (src == cm or dst == cm) and k.verify(dt[t][13:], t + dt[t][:13]):
            du.close(), dt.close()
            return True
    du.close(), dt.close()
    return False

def style_html(bg=True):
    "_"
    o = '<style type="text/css">@import url(http://fonts.googleapis.com/css?family=Schoolbell);h1,h2,p,li,i,b,a,div,input,td,th,footer{font-family:"Lucida Grande", "Lucida Sans Unicode", Helvetica, Arial, Verdana, sans-serif;}a.mono,p.mono,td.mono,b.mono{font-family:"Lucida Concole",Courier;font-weight:bold;}a.name{margin:50}a{color:DodgerBlue;text-decoration:none}p.alpha{font-family:Schoolbell;color:#F87217;font-size:26pt;position:absolute;top:115;left:80;}div.qr,a.qr{position:absolute;top:0;right:0;margin:15;}p.note{font-size:9;}p.msg{font-size:12;position:absolute;top:0;right:120;color:#F87217;}p.stat{font-size:9;position:absolute;top:0;right:20;color:#999;}input{font-size:28;margin:3}input.txt{width:200}input.digit{width:120;text-align:right}input[type=checkbox]{width:50}input[type=submit]{color:white;background-color:#AAA;border:none;border-radius:8px;padding:3}p,li{margin:10;font-size:18;color:#333;}b.red{color:red;}b.green{color:green;}b.blue{color:blue;}b.bigorange{font-size:32;color:#F87217;}b.biggreen{font-size:32;color:green;}#wrap{overflow:hidden;}a.ppc{font-weight:bold;font-size:.9em}a.ppc:after{font-weight:normal;content:"Cash"}#lcol{float:left;width:360;padding:4}#rcol{margin-left:368;padding:4}footer{bottom:0;color:#444;font-size:10;padding:4}table{margin:2;border:2px solid #999;border-collapse:collapse; background-color:white; opacity:.7}td,th{font-size:11pt;border:1px solid #666;padding:3pt;}th{background-color:#DDD}td.num{font-size:11;text-align:right}#c1{float:left;width:23%;padding:1%}#c2{float:left;width:23%;padding:1%}#c3{float:left;width:23%;padding:1%}#c4{float:left;width:23%;padding:1%}h1{color:#888;font-size:22;margin:20 0 0 20;}h2{font-size:18;margin:5 0 0 30;}svg{background-color:white;}img{border:2px outset}'
    if bg:
        o += 'body{color:black; background-color:white;background-image:url(http://cupfoundation.net/fond.png);background-repeat:no-repeat;}' 
    return o + '</style>'

def favicon():
    "_"
    return '<link rel="shortcut icon" type="www/image/png" href="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAFAAAABQCAIAAAABc2X6AAAABmJLR0QA/wD/AP+gvaeTAAAAoklEQVR4nO3csQ0CMRAAQR6R0wk1URo1UYnpgA4M0iNA65n0kltdankbYxxWcvz1At8muE5wneA6wXWn+fhyO0+m9+vjo8u8a89Wy11YcJ3gOsF1gusE1wmuE1wnuE5wneA6wXWC6wTXCa4TXCe4TnCd4DrBdYLrBNcJrhNcJ7juxYv4ufnL9P+03IUF1wmuE1wnuG7zy0Oc4DrBdYLrBNc9AUj0DSD4QMJ7AAAAAElFTkSuQmCC"/>'

def header():
    "_"
    o = '<a href="%s"><img title="Enfin un moyen de paiement numérique, simple, gratuit et sécurisé !" src="%s"/></a>\n' % (__url__, get_image('www/header.png'))
    return o + '<p class="alpha" title="still in security test phase!">Beta</p>'

def get_image(img):
    "_"
    here = os.path.dirname(os.path.abspath(__file__))
    return 'data:image/png;base64,%s' % base64.b64encode(open('%s/%s' % (here, img), 'rb').read()).decode('ascii')

def footer(dg=''):
    "_"
    dg = ' %s' % dg if dg else ''
    return '<footer>Contact: <a href="mailto:%s">%s</a>%s<br/><a href="http://cupfoundation.net">⊔FOUNDATION</a> is registered in Toulouse/France SIREN: 399 661 602 00025</footer>' % (__email__, __email__, dg)

def report(d, cm):
    "_"
    du, dt, dc, bal, o = d['pub'], d['trx'], d['crt'], 0, '<table><tr><th colspan="2">Date</th><th>Type</th><th>Référence</th><th>Description</th><th>Débit</th><th>Crédit</th></tr>'
    z, root, dar, n , tmp = b'%'+cm, dc[b'_'], None, 0, []
    if z in dc: 
        dar, bal = dc[z][:4], b2s(dc[z][4:8], 4)
        o += '<tr><th></th><th>%s</th><th colspan="3">Ancien solde</th><th></th><th class="num">%s&nbsp;€</th></tr>' % (datdecode(dar), (bal/100))
    for t in dt.keys():
        if len(t) == 13 and (dar==None or is_after(t[:4], dar)):
            src, dst, prc = t[4:], dt[t][:9], b2i(dt[t][9:12])
            if cm in (dst, src):
                if src == cm: 
                    one, t1, t2, bal = dst, '<td class="num">%7.2f&nbsp;€</td>' % (prc/100), '<td></td>', bal-prc 
                else: 
                    one, t1, t2, bal = src, '<td></td>', '<td class="num">%7.2f&nbsp;€</td>' % (prc/100), bal+prc
                typ = '<td title="Autorité">admin.</td>' if one == root else '<td title="banque Internet">ibank</td>' if one in dc else '<td title="particulier ou commerçant">part.</td>'
                desc = dt[t][12:-132].decode('utf8')
                tmp.append((t[:4], '<td class="num">%s</td>%s<td><a class="mono" href="?%s">%s</a></td><td>%s</td>%s%s</tr>' % (datdecode(t[:4]), typ, btob64(one), btob64(one), desc, t1, t2)))
    for i, (d, x) in enumerate(sorted(tmp)): o += '<tr><td class="num">%03d</td>' % (i+1) + x
    o += '<tr><th colspan="2">%s</th><th colspan="3"><b>Nouveau solde</b></th>' % datdecode(datencode())
    if bal<0:
        o += '<th></th><th class="num"><b>%7.2f&nbsp;€</b></th></tr>' % (-bal/100)
    else:
        o += '<th class="num"><b>%7.2f&nbsp;€</b></th><th></th></tr>' % (bal/100)
    return o + '</table>\n', bal

def report_cup(d, cm):
    "_"
    du, dt, dc, di,bal, o = d['pub'], d['trx'], d['crt'], d['igs'], 0, '<table><tr><th colspan="2">Date</th><th>Type</th><th>IG</th><th>Référence</th><th>Débit</th><th>Crédit</th></tr>'
    z, root, n , tmp, listig = b'%'+cm, dc[b'_'], 0, [], []
    for t in dt.keys():
        if len(t) == 15: 
            if cm == dt[t][:9]:
                listig.append(t[4:14])
    for t in dt.keys():        
        if len(t) == 15:
            nb, ig = b2i(t[:4]), t[4:14]
            src, dst, prc = dt[t][:9], dt[t][:9], get_price(di, ig, nb)
            if cm == src:
                one, t1, t2, bal = dst, '<td class="num">%7d&nbsp;⊔</td>' % prc, '<td></td>', bal-prc 
                typ = '<td title="particulier ou commerçant">part.</td>'
                auth = di[ig][:9]
                dat = datdecode(dt[t][9:13])
                tmp.append((dt[t][9:13], '<td class="num">%s</td>%s<td><a class="mono" href="?%s">%s</a></td><td><a class="mono" href="?%s">%s</a></td>%s%s</tr>' % (dat, typ, btob64(ig), btob64(ig), btob64(auth), btob64(auth), t1, t2)))
    for i, (d, x) in enumerate(sorted(tmp)): o += '<tr><td class="num">%03d</td>' % (i+1) + x
    o += '<tr><th colspan="2">%s</th><th colspan="3"><b>Nouveau solde</b></th>' % datdecode(datencode())
    if bal<0:
        o += '<th></th><th class="num"><b>%7d&nbsp;⊔</b></th></tr>' % (-bal)
    else:
        o += '<th class="num"><b>%7d&nbsp;⊔</b></th><th></th></tr>' % (bal)
    return o + '</table>\n', bal

def balance(base, cm):
    "_"
    du, dt, dc, bal, k = dbm.open(base+'pub'), dbm.open(base+'trx'), dbm.open(base+'crt'), 0, ecdsa()
    z, root, dar = b'%'+cm, dc[b'_'], None
    k.pt = Point(c521, b2i(du[root][:66]), b2i(du[root][66:]+root))
    if z in dc and k.verify(dc[z][8:], cm + dc[z][:8]): dar, bal = dc[z][:4], b2s(dc[z][4:8], 4)
    for t in dt.keys():
        if dar==None or is_after(t[:4], dar):
            src, dst, prc = t[4:], dt[t][:9], b2i(dt[t][9:12])
            k.pt = Point(c521, b2i(du[src][:66]), b2i(du[src][66:]+src))
            if (src == cm or dst == cm) and k.verify(dt[t][12:], t + dt[t][:12]):
                if src == cm: bal -= prc
                if dst == cm: bal += prc 
    du.close(), dt.close(), dc.close()
    return bal

def nblc(d, cm):
    "_"
    du, dt, dc, bal = d['pub'], d['trx'], d['crt'], 0
    z, root, dar = b'%'+cm, dc[b'_'], None
    #k = ecdsa()
    #k.pt = Point(c521, b2i(du[root][:66]), b2i(du[root][66:]+root))
    #if z in dc and k.verify(dc[z][8:], cm + dc[z][:8]): dar, bal = dc[z][:4], b2s(dc[z][4:8], 4)
    if z in dc: dar, bal = dc[z][:4], b2s(dc[z][4:8], 4)
    for t in dt.keys():
        if (len(t) == 13) and (dar==None or is_after(t[:4], dar)):
            src, dst, prc = t[4:], dt[t][:9], b2i(dt[t][9:12])
            #k.pt = Point(c521, b2i(du[src][:66]), b2i(du[src][66:]+src))
            if (src == cm or dst == cm):# and k.verify(dt[t][12:], t + dt[t][:12]):
                if src == cm: bal -= prc
                if dst == cm: bal += prc 
    return bal

def cleantr():
    "_"
    du, dt, dc, k = dbm.open(__base__+'pub'), dbm.open(__base__+'trx', 'c'), dbm.open(__base__+'crt'), ecdsa()
    for u in du.keys(): 
        z, root, dar = b'%'+u, dc[b'_'], None
        k.pt = Point(c521, b2i(du[root][:66]), b2i(du[root][66:]+root))
        if z in dc and k.verify(dc[z][8:], u + dc[z][:8]): dar, bal = dc[z][:4], b2s(dc[z][4:8], 4)
        for t in dt.keys():
            if dar and is_after(dar, t[:4]): del dt[t]
    du.close(), dt.close(), dc.close()

### Tmp ###

def get_random_ibank(dc): # if there is only one ibank
    for x in dc.keys():
        if len(x) == 9: return btob64(x)

def get_random_user(dc, du):
    for x in du.keys():
        if x != dc[b'_'] and x not in dc.keys(): return x

##### WEB APP #####

def peers_req(host='localhost'):
    "_"
    co, serv = http.client.HTTPConnection(host), '/' #+ __app__
    co.request('POST', serv, urllib.parse.quote('PEERS'))
    return eval(co.getresponse().read().decode('utf8'))    

def req(host='localhost', data=''):
    "_"
    co, serv = http.client.HTTPConnection(host), '/' #+ __app__
    co.request('POST', serv, urllib.parse.quote(data))
    return eval(co.getresponse().read())    

def digest_req(host='localhost'):
    "_"
    co, serv = http.client.HTTPConnection(host), '/' #+ __app__
    co.request('POST', serv, urllib.parse.quote('DIGEST'))
    return co.getresponse().read()    

def reg(value):
    " function attribute is a way to access matching group in one line test "
    reg.v = value
    return value

def init_dbs(dbs, port):
    "_"
    di = '/%s/%s_%s' % (__app__, __app__, port)
    if not os.path.exists(di): os.makedirs(di)
    for dbn in dbs:
        db = '%s/%s' % (di, dbn)
        if not (os.path.isfile(db) or os.path.isfile(db+'.db')):
            d = dbm.open(db, 'c')
            d.close()
            os.chmod(db, 511)
    return {b:dbm.open('%s/%s' % (di, b), 'c') for b in dbs}

def update_peers(env, d, li):
    "_"
    now = '%s' % datetime.datetime.now()
    for p in li:
        if p != env['HTTP_HOST'] and bytes(p, 'utf8') not in d: d[p] = now[:19]
    return 'Peers: %s\nDigest: %s' % ({x.decode('utf8'):d[x].decode('utf8') for x in d.keys()}, rdigest(env['SERVER_PORT']))

def update_db(db, d, li):
    "_"
    if li and db == 'crt' and b'_' in d[db] and d[db][b'_'] != li[b'_']: return # manage root first
    for x in li:
        if x not in d[db]: d[db][x] = li[x]

def hmerge(d, port, tab):
    "_"
    trx, crt, pub, k = {}, {}, {}, ecdsa()
    for p in tab: 
        trx.update(req(p.decode('utf8'), 'TRX%s' % {x: d['trx'][x] for x in d['trx'].keys()}))
        crt.update(req(p.decode('utf8'), 'CRT%s' % {x: d['crt'][x] for x in d['crt'].keys()}))
        pub.update(req(p.decode('utf8'), 'PUB%s' % {x: d['pub'][x] for x in d['pub'].keys()}))
    if b'_' in d['crt'] and b'_' in crt: assert crt[b'_'] == d['crt'][b'_']
    if not b'_' in d['crt']: d['crt'][b'_'] = crt[b'_']
    root = d['crt'][b'_']
    for u in pub: 
        if len(u) !=9 and len(pub[u]) != 123: del pub[u]
        if u not in d['pub']: d['pub'][u] = pub[u]
    for t in trx:
        if len(t) !=13 and len(trx[t]) != 144: del trx[t]
        src = t[4:]
        k.pt = Point(c521, b2i(d['pub'][src][:66]), b2i(d['pub'][src][66:]+src))
        if not k.verify(trx[t][12:], t + trx[t][:12]): del trx[t]
        if t not in d['trx']: d['trx'][t] = trx[t]
    for c in crt:
        k.pt = Point(c521, b2i(d['pub'][root][:66]), b2i(d['pub'][root][66:]+root))
        if len(c) == 9: # bank certificat
            if k.verify(crt[c][12:], c + crt[c][:12]) and c not in d['crt']: d['crt'][c] = crt[c]
        elif len(c) == 10: # cut
            if k.verify(crt[c][8:], c[1:] + crt[c][:8]) and c not in d['crt']: d['crt'][c] = crt[c]
    wdigest(d, port)

def app_update(host):
    "_"
    cd = 'cd %s; git pull origin' % os.path.dirname(os.path.abspath(__file__))
    out, err = subprocess.Popen((cd), shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
    o = '<html><pre>Application Update...\n'
    o += '%s\n' % err.decode('utf8') if err else 'Message:%s\n' % out.decode('utf8')
    o += '</pre><br/><a href="/">Reload the new version</a>'
    return o + footer() + '</html>'

def capture_id(d, arg):
    "_"
    res = []
    for u in d['pub'].keys():
        if re.match(arg, btob64(u)): res.append(btob64(u))            
    if len(res) == 1: return res[0]
    return None

def capture_ig(d, arg):
    "_"
    res = []
    for i in d['igs'].keys():
        if re.match(arg, btob64(i)): res.append(i)
    if len(res) == 1:
        return '%s:%s' % (btob64(res[0]), (len(d['igs'][res[0]])-151)//9)
    return None

def bank(d, env):
    o, mime = '<?xml version="1.0" encoding="utf8"?>\n<html>\n', 'text/html; charset=utf-8'
    o += '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
    o += favicon() + style_html() + '<body><div class="bg"></div>' + header()
    o += '<p class="msg" title="une offre par personne!"><a href="mailto:%s">Contactez nous,</a> nous offrons 1€ sur tout compte créé avant 2014!</p>' % __email__
    bnk = get_random_ibank(d['crt'])
    o += '<h1>La première <b class="red">iBanque</b> offrant ce nouveau moyen de paiement</h1>'
    o += '<h1>Notre ID:&nbsp;<b class="green"><b class="mono">%s</b></b></h1>' % bnk
    o += '<p>Créez un compte <a class="ppc">PingPong</a> sur votre téléphone portable (iPhone ou Android-Phone).</p><p>Le solde est initialement nul. Pour le créditer:<ul><li>demandez à vos débiteurs de vous rembourser sur votre compte <a class="ppc">PingPong</a> ou,'
    o += '<li>faites un virement SEPA vers notre <i>iBanque</i>: <br/>Nom: CUP-FOUNDATION<br/>BIC: CMCIFR2A <br/>IBAN: FR76 1027 8022 3300 0202 8350 157,<li>ajoutez votre ID en message de virement oubien envoyez-nous un <a href="mailto:%s">email</a> contenant votre ID associé à la référence du virement,<li>nous créditerons votre compte <a class="ppc">PingPong</a> dans la journée (7j/7) dès reception du virement,<li>aucune commission n\'est retenue mais le compte <a class="ppc">PingPong</a> n\'est pas rémunéré.</ul>' % __email__
    o += '<p>Inversement, à tout moment, vous pouvez récuperer toute somme de votre compte <a class="ppc">PingPong</a>,</p><ul><li>faites un paiement vers notre <i>iBanque</i> (ID %s ou scannez le QRcode) du montant à retirer,<li><a href="mailto:%s">envoyez nous</a> votre IBAN+BIC ainsi que l\'ID de votre compte,<li>dans la journée (7j/7), la somme sera tranférée par virement SEPA au crédit de votre compte bancaire,<li>vous pouvez aussi régler vos créanciers avec le compte <a class="ppc">PingPong</a>,<li>aucune commission n\'est retenue et vous pouvez consulter votre compte depuis n\'importe quel point connecté au Net.</ul>' % (bnk, __email__)

    o += '<p class="note">Aucune personne autre que vous, muni du téléphone sur lequel vous avez créé un compte, ne peut payer depuis votre compte <a class="ppc">PingPong</a>.<br/>Strictement personne ne peut retrouver votre passphrase si vous la perdez.<br/>A la création de votre compte, pensez à générer un <b>i-chèque</b> vers notre <i>iBanque</i> (%s) du montant que vous estimez vous assurer et gardez le fichier dans un endroit sécurisé, autre que le téléphone.<br/>Si vous perdez ou vous faites voler votre téléphone ou si vous oubiez votre passphrase, <a href="mailto:%s">Envoyez nous</a> l\'ID d\'un nouveau compte crée.<br>Nous créditerons ce nouveau compte dès que vous aurez posté l\'<b>i-chèque</b> de réserve à l\'encaissement.<br/>L\'ancien compte ainsi vidé ne peut plus être débité. Pensez à avertir vos débiteurs du changement de compte car les sommes qui depasseraient le montant de l\'<b>i-chèque</b> de réserve sur le compte perdu ou qui surviendraient après l\'encaissement seraient non récupérables.</p>' % (bnk, __email__)

    o += '<p class="note">Pour maintenir la confidentialité de vos comptes, nous <i>iBanque</i> ne pouvons pas associer votre identité à l\'un ou à l\'ensemble de vos comptes. L\'utilisation de plusieurs comptes vous assure un anonymat de vos transactions. Cependant vos débiteurs peuvent vous demander cette association afin qu\'ils puissent prouver devant un tier du remboursement de leur dette à la bonne personne et que vous ne puissiez pas contester ne pas avoir été payé.</p>' 

    o += '<div class="qr" title="%s">%s</div>\n' % (bnk, QRCode(bnk, 2).svg(0, 0, 4))
    atrt = btob64(d['crt'][b'_'])[:5] if b'_' in d['crt'] else 'None'
    return o + footer('Authority: %s' % (atrt) ) + '</body></html>\n'

def index(d, env, cm64='', prc=0):
    o, mime = '<?xml version="1.0" encoding="utf8"?>\n<html>\n', 'text/html; charset=utf-8'
    o += '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
    o += favicon() + style_html() + '<body><div class="bg"></div>' + header()
    o1 = '<ul><li><a title="moins de 1200 lignes Python3!" href="?src">Téléchargez</a> et <a title="sur GitHub" href="https://github.com/pelinquin/pingpongcash">analysez</a> le code du client <i>pair-à-pair</i></li>'
    o1 += '<li>Installez un <a href="?install">serveur</a> <i>Linux</i> ou <a href="?ios">l\'application</a> <i>iOS</i></li>' 
    o1 += '<li><form method="post">Consultez votre compte :<br/><input class="txt" name="cm" placeholder="...votre ID"/></form></li></ul>\n'
    if cm64 == '' and 'HTTP_COOKIE' in env: cm64 = env['HTTP_COOKIE'][3:]
    cm = b64tob(bytes(cm64, 'ascii'))
    if cm in d['pub']:
        rpt, bal = report(d, cm)
        rpt1, bal1 = report_cup(d, cm)
        o += '<h1 title="Effacer le cookie pour changer d\'ID">Compte:&nbsp;<b class="green"><b class="mono">%s</b></b></h1>' % cm64
        v = ' value="%7.2f€"' % (prc/100) if prc else '' 
        o += '<form method="post"><input type="hidden" name="cm" value="%s"/>' % cm64
        o += '<input class="digit" name="prc" pattern="[0-9]{1,4}([\.\,][0-9]{2}|)\s*€?" placeholder="---,-- €"%s/></form>' % v
        o += '<h1>Solde:&nbsp;&nbsp;&nbsp;<b class="green">%7.2f&nbsp;€&nbsp;&nbsp;%7d&nbsp;⊔</b></h1>' % (bal/100, bal1) + rpt + rpt1
        da = btob64(cm) + ':%d' % prc if prc else ''
        o += '<div class="qr" title="%s">%s</div>\n' % (da, QRCode(da, 2).svg(0, 0, 4))
        o += '<p class="note">Découvrez notre <a href="?bank">iBanque</a> pour mieux profiter de ce moyen de paiement</p>' 
    else:
        o += o1
    atrt = btob64(d['crt'][b'_'])[:5] if b'_' in d['crt'] else 'None'
    return o + footer('%s %s Auth:%s' % (rdigest(env['SERVER_PORT']), stat(d), atrt)) + '</body></html>\n'

def stat(d):
    "_"
    return '[%d:%d:%d:%d]' % (len(d['pub']), len(d['crt']), len(d['igs']), len(d['trx']))

def get_price(digs, ig, i):
    "_"
    xi, p1, pf = valdecode(digs[ig][12:21])
    k = ((pf-p1)/(pf-2*p1))**(xi/100)
    return int((pf+(p1-pf)/k**i)/(i+1))

def dashboard(d, env):
    "_"
    o, mime = '<?xml version="1.0" encoding="utf8"?>\n<html>\n', 'text/html; charset=utf-8'
    o += '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
    o += favicon() + style_html() + '<body><div class="bg"></div>' + header()
    o += '<table><tr><th>Compte</th><th>Solde</th><th>dette</th></tr>'
    for u in d['pub'].keys():
        o += '<tr><td class="mono">%s</td><td class="num">%7.2f&nbsp;€</td><td class="num">%7.2f&nbsp;€</td></tr> ' % (btob64(u), nblc(d, u)/100, ndebt(d, u)/100 ) 
    o += '</table>'
    o += '<table><tr><th>Certificat</th><th>Date</th><th>Dette maxi</th></tr>'
    for c in d['crt'].keys():
        if len(c) == 9:
            dat, dbt = datdecode(d['crt'][c][:4]), b2i(d['crt'][c][4:12])
            o += '<tr><td class="mono">%s</td><td class="num">%s</td><td class="num">%7.2f&nbsp;€</td></tr>' % (btob64(c), dat, dbt)
        else:
            o += '<tr><td class="mono">%s</td><td colspan="2">Autorité</td></tr>' % btob64(d['crt'][c])
    o += '</table>'
    o += '<table><tr><th>IG</th><th>Autheur</th><th>Date</th><th>Prix</th><th>N</th></tr>'
    for i in d['igs'].keys():
        if len(i) == 10:
            src, dat = btob64(d['igs'][i][:9]), datdecode(d['igs'][i][9:13])
            xi, p1, pf = valdecode(d['igs'][i][13:19])
            o += '<tr><td class="mono">%s</td><td class="num">%s</td><td class="num">%s</td><td class="num">%d/%d&nbsp;⊔ (%d%%)</td><td class="num">%s</td></tr>' % (btob64(i), src, dat, p1, pf, xi, (len(d['igs'][i])-151)//9)
        else:
            o += '<tr><td class="mono">%s</td><td colspan="3">Erreur</td></tr>' % btob64(d['igs'][i])
    o += '</table>'
    o += '<table><tr><th>Trans. src</th><th>Date</th><th>Destinataire</th><th>Message</th><th>Montant</th></tr>'
    for t in d['trx'].keys():
        if len(t) == 13:
            dat, src, dst, val = datdecode(t[:4]), btob64(t[4:13]), btob64(d['trx'][t][:9]), b2i(d['trx'][t][9:12])/100
            desc = d['trx'][t][12:-132].decode('utf8')
            o += '<tr><td class="mono">%s</td><td class="num">%s</td><td class="mono">%s</td><td>%s</td><td class="num">%7.2f&nbsp;€</td></tr> ' % (src, dat, dst, desc, val)
    o += '</table>'
    o += '<table><tr><th>Trans. src</th><th>Date</th><th>No</th><th>IG</th><th>Destinataire</th><th>Montant</th></tr>'
    for t in d['trx'].keys():
        if len(t) == 15:
            nb, ig, hig, src, dat = b2i(t[0:4]), t[4:14], btob64(t[4:14]), btob64(d['trx'][t][:9]), datdecode(d['trx'][t][9:13])
            dst = btob64(d['igs'][ig][:9])
            prc = get_price(d['igs'], ig, nb)
            o += '<tr><td class="mono">%s</td><td class="num">%s</td><td class="num">%05d</td><td class="mono">%s</td><td class="mono">%s</td><td class="num">%d&nbsp;⊔</td></tr> ' % (src, dat, nb, hig, dst, prc)
    o += '</table>'
    o += '<table><tr><th>Errors</th></tr>'
    su =  sum([nblc(d, u) for u in d['pub'].keys()])     
    if su != 0: o += '<tr><td class="mono">%s</td></tr> ' % su
    k = ecdsa()
    #for i in d['igs'].keys(): del d['igs'][i]
    for t in d['trx'].keys():
        if len(t) == 13:
            src, dst, msg, sig = t[4:], d['trx'][t][:9], t + d['trx'][t][:-132], d['trx'][t][-132:]
            k.pt = Point(c521, b2i(d['pub'][src][:66]), b2i(d['pub'][src][66:]+src))
            if src in d['pub'] and dst in d['pub'] and src != dst:
                if not k.verify(sig, msg): 
                    o += '<tr><td class="mono">%s %s</td></tr>' % (datdecode(t[:4]), btob64(t[4:]))
                    #del d['trx'][t]
            else:
                '<tr><td class="mono">Pb!</td></tr>'
        #elif len(t) == 15: del d['trx'][t]
    root = d['crt'][b'_']
    k.pt = Point(c521, b2i(d['pub'][root][:66]), b2i(d['pub'][root][66:]+root))
    for c in d['crt'].keys():
        if len(c) == 9 and not k.verify(d['crt'][c][12:], c + d['crt'][c][:12]): 
            o += '<tr><td class="mono">certificat</td></tr>'
            #del d['crt'][c]
    o += '</table>'
    atrt = btob64(d['crt'][b'_'])[:5] if b'_' in d['crt'] else 'None'
    return o + footer('%s %s Auth:%s' % (rdigest(env['SERVER_PORT']), stat(d), atrt)) + '</body></html>\n'

def publish(d, env, url):
    "_"
    o, mime = '<?xml version="1.0" encoding="utf8"?>\n<html>\n', 'text/html; charset=utf-8'
    o += '<meta name="viewport" content="width=device-width, initial-scale=1"/>'
    o += favicon() + style_html(False) 
    ign = re.sub('publish/', '', url)
    di = '/%s/%s_%s' % (__app__, __app__, env['SERVER_PORT'])
    fpdf, fpng, lpng = re.sub('publish', di, url) + '.pdf', re.sub('publish', di, url) + '.png', re.sub('publish', di, url) + '_.png'
    if os.path.isfile(fpdf):
        p = subprocess.Popen(('pdfinfo', fpdf), stdout=subprocess.PIPE).communicate()
        nump = int(reg.v.group(1)) if reg(re.search('Pages:\s+(\d+)', p[0].decode('ascii'))) else 0
        if not os.path.isfile (bytes(fpng, 'utf8')): subprocess.call(('convert', 'x300', (fpdf + '[0]').encode('utf8') , fpng.encode('utf8')))
        if not os.path.isfile (bytes(lpng, 'utf8')): subprocess.call(('convert', 'x300', (fpdf + '[%s]' % (nump-1)).encode('utf8') , lpng.encode('utf8')))
        data = base64.b64encode(open(fpng.encode('utf8'), 'rb').read()).decode('ascii')
        datb = base64.b64encode(open(lpng.encode('utf8'), 'rb').read()).decode('ascii')
        o += '<h1>%s (%d pages)</h1>' % (ign, nump)
        o += '<a href="/%s.png" title="page de couverture"><image width="150" src="data:image/png;base64,%s"/></a>\n' % (ign, data)
        o += '<a href="/%s_.png" title="quatrième de couverture"><image width="150" src="data:image/png;base64,%s"/></a>\n' % (ign, datb)
        hig = hcode('cup/publish/%s' % ign)
        if hig in d['igs']:
            src = d['igs'][hig][:9]
            o += '<p>Code IG: %s</p>' % btob64(hig)
            o += '<p>ID autheur: %s</p>' % btob64(src)
            o += '<p>Date de publication: %s</p>' % ('31/10/13')
            o += '<p>Prix Initial: %d&nbsp;⊔</p>' % (10)
            o += '<p>Revenu cumulé maximum escompté: %d&nbsp;⊔</p>' % (10000)
            o += '<p>Paramètre de vitesse: %d%%</p>' % 35
            o += "<p>Nombre d'acheteurs: %06d</p>" % 1
    else:
        o += 'IG not found' 
    atrt = btob64(d['crt'][b'_'])[:5] if b'_' in d['crt'] else 'None'
    return o + '</body></html>\n'

def diff_dbs(d, port):
    "_"
    tab = []
    for p in d['prs'].keys(): 
        if rdigest(port) != digest_req(p.decode('utf8')).decode('utf8'): 
            tab.append(p)
    if tab: hmerge(d, port, tab)

def push_dbs(d, port):
    "_"
    tab = []
    for p in d['prs'].keys(): 
        if rdigest(port) != digest_req(p.decode('utf8')).decode('utf8'): 
            tab.append(p)
    for p in tab: 
        req(p.decode('utf8'), 'TRX%s' % {x: d['trx'][x] for x in d['trx'].keys()})
        req(p.decode('utf8'), 'CRT%s' % {x: d['crt'][x] for x in d['crt'].keys()})
        req(p.decode('utf8'), 'PUB%s' % {x: d['pub'][x] for x in d['pub'].keys()})

def valid_pub(d, pub):
    "_"
    cm, key = pub[-9:], pub[:-9]
    if cm not in d['pub']:
        d['pub'][cm] = key
        return True
    return False

def valid_ig_old(d, dig):
    "_"
    k, src, h, i, r, msg, sig = ecdsa(), dig[:9], dig[9:19], dig[:19], dig[19:], dig[:29], dig[29:]
    k.pt = Point(c521, b2i(d['pub'][src][:66]), b2i(d['pub'][src][66:]+src))
    if i not in d['igs']:
        if k.verify(sig, msg):
            d['igs'][i] = r
            return True
    return False

def valid_ig(d, dig):
    "_"
    k, h, src, r, msg, sig = ecdsa(), dig[:10], dig[10:19], dig[10:], dig[:29], dig[29:]
    k.pt = Point(c521, b2i(d['pub'][src][:66]), b2i(d['pub'][src][66:]+src))
    if h not in d['igs']:
        if k.verify(sig, msg):
            d['igs'][h] = r
            return True
    return False

def valid_big(d, r):
    "_"
    k, nb, hig, kk, src, dat, msg, sig = ecdsa(), r[:4], r[4:14], r[:14], r[14:23], r[23:27], r[:27], r[27:]
    if src in d['pub'] and hig in d['igs']:
        k.pt, ssrc = Point(c521, b2i(d['pub'][src][:66]), b2i(d['pub'][src][66:]+src)), b'&'+src
        if k.verify(sig, msg):
            decal = (len(d['igs'][hig]) - 151)//9 - b2i(nb)
            d['trx'][nb + hig + i2b(decal, 1)] = src + dat + sig
            d['igs'][hig] += src 
            d['trx'][ssrc] = d['trx'][ssrc] + hig if ssrc in d['trx'] else hig # shortcut
            return True
    return False

def valid_trx(d, r):
    "_"
    u, dat, src, v, dst, prc, msg, sig, k = r[:13], r[:4], r[4:13], r[13:-132], r[13:22], r[22:25], r[:-132], r[-132:], ecdsa()
    k.pt, ddst = Point(c521, b2i(d['pub'][src][:66]), b2i(d['pub'][src][66:]+src)), b'%'+dst
    if src in d['pub'] and dst in d['pub'] and src != dst and u not in d['trx'] and k.verify(sig, msg):
        if nblc(d, src) + ndebt(d, src) > b2i(prc): 
            d['trx'][u] = v + sig
            d['trx'][src] = d['trx'][src] + dat if src in d['trx'] else dat # shortcut
            d['trx'][ddst] = d['trx'][ddst] + u if ddst in d['trx'] else u  # shortcut
            return True
    return False

#### TMP
def init_igs(d):
    h, k = hcode('cup/pub/ig1'), ecdsa()
    #k.privkey = int(AES().decrypt(d['prv'][cm], hashlib.sha256(pp.encode('utf8')).digest())) 
    u = get_random_user(d['crt'], d['pub'])
    dat = datencode()
    val = valencode(35, 54, 10000)
    msg = u + dat + val
    #digs[h] = msg + k.sign(msg + h)
# TMP

def application(environ, start_response):
    "wsgi server app"
    mime, o, now, fname, port = 'text/plain; charset=utf8', 'Error:', '%s' % datetime.datetime.now(), 'default.txt', environ['SERVER_PORT']
    d = init_dbs(('prs', 'trx', 'pub', 'crt', 'igs'), port)
    wdigest(d, port)
    (raw, way) = (environ['wsgi.input'].read(), 'post') if environ['REQUEST_METHOD'].lower() == 'post' else (urllib.parse.unquote(environ['QUERY_STRING']), 'get')
    base, ncok = environ['PATH_INFO'][1:], []
    if way == 'post':
        arg = urllib.parse.unquote_plus(raw.decode('utf8'))
        if arg == 'PEERS': o = '%s' % {x.decode('utf8'): d['prs'][x].decode('utf8') for x in d['prs'].keys()}
        elif reg(re.match(r'(TRX|CRT|PUB|IGS)', arg)):
            li, la, db = eval(urllib.parse.unquote(arg[3:])), {}, reg.v.group(1).lower()
            # not used for for pushing! 
            #for x in d[db].keys():
            #    if x not in li: la[x] = d[db][x]
            if li: update_db(db, d, li)
            wdigest(d, port)
            o = '%s' % la
        elif arg == 'DIGEST': o = rdigest(port)
        elif arg == 'IBANK': o = get_random_ibank(d['crt'])
        elif reg(re.match('(cm=(\S{1,12})&)prc=([\d\.\,]{1,7})\s*€?$', arg)):
            prc = int(float(re.sub(',', '.', reg.v.group(3)))*100)
            r = capture_id(d, reg.v.group(2))
            o, mime = index(d, environ, r, prc), 'text/html; charset=utf-8'
        elif re.match('cm=\S{1,12}$', arg):
            r = capture_id(d, arg[3:])
            if r: 
                ncok.append(('set-cookie', 'cm=%s' % r))
                environ['HTTP_COOKIE'] = 'cm=%s' % r
                o, mime = index(d, environ), 'text/html; charset=utf-8'
            else:
                o += 'Id not found! |%s|' % arg 
        elif re.match('IG:\S{1,25}$', arg):
            r = capture_ig(d, arg[3:])
            o = r if r != None else 'IG not found!' 
        elif re.match('\S{1,12}$', arg):
            r = capture_id(d, arg)
            o = r if r else 'Id not found!' 
        elif re.match('P:\S{174,176}$', arg): 
            if valid_pub(d, b64tob(bytes(arg[2:], 'ascii'))): o = 'New public key registered [%s]' % len(d['pub'])
            else: o += 'public key already registered!'
        elif re.match('I:\S{215}$', arg): 
            if valid_ig(d, b64tob(bytes(arg[2:], 'ascii'))): o = 'New IG registered [%s]' % len(d['igs'])
            else: o += 'IG already registered!'
        elif re.match('B:\S{212}$', arg): 
            if valid_big(d, b64tob(bytes(arg[2:], 'ascii'))): o = 'New transaction recorded [%s]' % len(d['trx'])
            else: o += 'not valid ig transaction !'
        elif re.match('A:\S{210,236}$', arg): 
            if valid_trx(d, b64tob(bytes(arg[2:], 'ascii'))) : o = 'New transaction recorded [%s]' % len(d['trx'])
            else: o += 'not valid transaction !' 
        elif re.match('[^:]{20}:\S+$', arg):
            t, ig = b64tob(bytes(arg[:20], 'ascii')), arg[21:]
            k, nb, hig = ecdsa(), b2i(t[:4]), t[4:14]
            if t in d['trx'] and hig in d['igs']:
                dst = d['igs'][hig][151+(nb-1)*9:151+nb*9]
                k.pt = Point(c521, b2i(d['pub'][dst][:66]), b2i(d['pub'][dst][66:]+dst))
                dr = dbm.open('/%s/%s_%s/url' % (__app__, __app__, port), 'c')                
                if t in dr:
                    eurl = dr[t]
                else:
                    rurl = random_b64()
                    eurl = k.encrypt(rurl)
                    dr[rurl], dr[t] = ig, eurl
                dr.close()
                o = btob64(eurl)
        else: o += 'not valid args |%s|' % arg
    else:
        if base == 'peers': # propagation
            fullbase, li = urllib.parse.unquote(environ['REQUEST_URI'])[1:], {}
            for p in d['prs'].keys(): li.update(peers_req(p.decode('utf8')))
            o = update_peers(environ, d['prs'], li)
            #diff_dbs(d, port)
        elif base == '_update': o, mime = app_update(environ['SERVER_NAME']), 'text/html; charset=utf-8'
        elif base == 'dashboard': o, mime = dashboard(d, environ), 'text/html; charset=utf-8'
        elif reg(re.match('(\S+)\.png$', base)): 
            mime, o = 'image/png', open('/%s/%s_%s/%s.png' % (__app__, __app__, port, reg.v.group(1)), 'rb').read()
        elif re.match('publish', base): o, mime = publish(d, environ, base), 'text/html; charset=utf-8'
        elif re.match('\S{20}$', base): 
            dr = dbm.open('/%s/%s_%s/url' % (__app__, __app__, port))
            url = bytes(base, 'utf8')
            if url in dr: 
                o, mime = open('/%s/%s_%s/%s.pdf' % (__app__, __app__, port, dr[url].decode('utf8')), 'rb').read(), 'application/pdf'
            else:
                o += 'bad url!'
            dr.close()
        elif base == '':
            if raw == 'install': o = install()
            elif raw == 'ios': o = 'Toujours en phase de test!\nBientôt disponible sur appStore\n\nNous contacter pour toute question.'
            elif raw == 'src': o = open(__file__, 'r', encoding='utf-8').read() 
            elif raw == 'download': o, mime = open(__file__, 'r', encoding='utf-8').read(), 'application/octet-stream' 
            elif raw == 'bank': o, mime = bank(d, environ), 'text/html; charset=utf-8'
            else:
                o, mime = index(d, environ, raw), 'text/html; charset=utf-8'
                #diff_dbs(d, port)
        elif re.match(r'\S{2,40}', base) and base != environ['HTTP_HOST']: # bootstrap
            li = peers_req(base) 
            li.update({base:now[:19]})
            o = update_peers(environ, d['prs'], li)
            #diff_dbs(d, port)
            push_dbs(d, port)
        else:
            o += 'request not valid!'
    for db in d: d[db].close()
    start_response('200 OK', [('Content-type', mime)] + ncok)
    return [o if mime in ('application/pdf', 'image/png') else o.encode('utf8')] 

def wdigest(d, port):
    "computes digest for all databases"
    dbs = ('pub', 'trx', 'crt')
    s = b''.join([b''.join([x + d[a][x] for x in sorted(d[a].keys())]) for a in dbs])
    open('/%s/%s_%s/digest.txt' % (__app__, __app__, port) , 'w').write(hashlib.sha1(s).hexdigest()[:10])

def rdigest(port):
    "return db digest"
    return open('/%s/%s_%s/digest.txt' % (__app__, __app__, port)).read()

def install():
    """Quelques instructions d'installation sous Linux\n
- Sauvegarder le fichier source avec le nom 'mini.py'
- Créez un répertoire /mini à la racine avec les droits d'écriture pour www-data
- Installer un serveur Web; le plus simple est Apache2 le mod 'wsgi' pour Python3 
sudo apt-get install apache2 libapache2-mod-wsgi-py3
- Configurer Apache en ajoutant un fichier ppc.conf sous /etc/apache/conf.d avec la ligne:
WSGIScriptAlias / /home/mon_repertoire_install/mini.py
- Relancer le serveur Apache
sudo /etc/init.d/apache restart
- Ouvrez la page installée 
"http://mon_serveur/"
une copie des bases 'peers', 'transactions', 'publickeys' et 'certificats' est installée dans le répertoire /mini
- enfin lancez 'mini.py' en ligne de commande pour générer vos clés
votre clé privée est dans le fichier 'private'...à protéger absolument des intrus et à ne pas perdre.\n
Pour tout problème, nous contacter à 'contact@cupfoundation.net'
"""
    return install.__doc__

##### MAIN #####

if __name__ == '__main__':
    if len(sys.argv)==1:
        if not (os.path.isfile('private') or os.path.isfile('private.db')):
            root = register()
            bank = register('banker')
            certif('banker', 100000)
        else:
            buy('banker', 10000)
    else:
        if sys.argv[1] == 'cut':
            allcut()
        else:
            buy('user', int(float(sys.argv[1])*100))
    sys.exit()    

# End ⊔net!
