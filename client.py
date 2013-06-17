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
#-----------------------------------------------------------------------------
"""
This code simulates the device used to store user's private key...usually a smartPhone
"""

import re, os, sys, math, urllib.parse, hashlib, http.client, base64, dbm, binascii, datetime, zlib, functools, time, smtplib, getpass, argparse

__db__ = 'keys.db'

# NIST Curve P-521:
_B = b'UZU-uWGOHJofkpohoLaFQO6i2nJbmbMV87i0iZGO8QnhVhk5Uex-k3sWUsC9O7G_BzVz34g9LDTx70Uf1GtQPwA'
_GX = b'xoWOBrcEBOnNnj7LZiOVtEKcZIE5BT-1Ifgor2BrTT26oUted-_nWSj-HcEnov-o3jNIs8GFakKb-X5-McLlvWY'
_GY = b'ARg5KWp4mjvABFyKX7QsfRvZmPVESVebRGgXr70XJz5mLJfucple9CZAxVC5AT-tB2E1PHCGonLCQIi-lHaf0WZQ'
_P = b'Af' + b'_'*86
_R = b'Af' + b'_'*42 + b'-lGGh4O_L5Zrf8wBSPcJpdA7tcm4iZxHrrtvtx6ROGQJ'

_IV = b'ABCDEFGHIJKLMNOP'

def itob64(n):
    "utility to transform int to base64"
    c = hex(n)[2:]
    if len(c)%2: c = '0'+c
    return re.sub(b'=*$', b'', base64.urlsafe_b64encode(bytes.fromhex(c)))

def itob32(n):
    "utility to transform int to base64"
    c = hex(n)[2:]
    if len(c)%2: c = '0'+c
    return re.sub(b'=*$', b'', base64.b32encode(bytes.fromhex(c))).lower()

def b64toi(c):
    "transform base64 to int"
    if c == '': return 0
    return int.from_bytes(base64.urlsafe_b64decode(c + b'='*((4-(len(c)%4))%4)), 'big')

def b32toi(c):
    "transform base64 to int"
    c = c.upper()
    if c == '': return 0
    return int.from_bytes(base64.b32decode(c + b'='*((4-(len(c)%4))%4)), 'big')

def H(*tab):
    "hash"
    return int(hashlib.sha1(b''.join(bytes('%s' % i, 'utf8') for i in tab)).hexdigest(), 16)

##### ECDSA ####
def encode_oid(first, second, *pieces):
    assert first <= 2
    assert second <= 39
    encoded_pieces = [chr(40*first+second)] + [encode_number(p) for p in pieces]
    body = "".join(encoded_pieces)
    return "\x06" + encode_length(len(body)) + body

def encode_number(n):
    b128_digits = []
    while n:
        b128_digits.insert(0, (n & 0x7f) | 0x80)
        n = n >> 7
    if not b128_digits: b128_digits.append(0)
    b128_digits[-1] &= 0x7f
    return "".join([chr(d) for d in b128_digits])

def encode_length(l):
    assert l >= 0
    if l < 0x80: return chr(l)
    s = "%x" % l
    if len(s)%2: s = "0"+s
    s = binascii.unhexlify(s)
    llen = len(s)
    return chr(0x80|llen) + s

class CurveFp( object ):
    def __init__( self, p, a, b ):
        "The curve of points satisfying y^2 = x^3 + a*x + b (mod p)."
        self.__p, self.__a, self.__b = p, a, b
    def p( self ):
        return self.__p
    def a( self ):
        return self.__a
    def b( self ):
        return self.__b
    def contains_point( self, x, y ):
        return ( y * y - ( x * x * x + self.__a * x + self.__b ) ) % self.__p == 0

class Point(object):
    def __init__( self, curve, x, y, order = None ):
        "curve, x, y, order; order (optional) is the order of this point"
        self.__curve = curve
        self.__x = x
        self.__y = y
        self.__order = order
        if self.__curve: assert self.__curve.contains_point( x, y )
        if order: assert self * order == INFINITY
    def __cmp__( self, other ):
        "Return 0 if the points are identical, 1 otherwise"
        if self.__curve == other.__curve and self.__x == other.__x and self.__y == other.__y: return 0
        else: return 1
    def __add__( self, other ):
        "Add one point to another point"
        if other == INFINITY: return self
        if self == INFINITY: return other
        assert self.__curve == other.__curve
        if self.__x == other.__x:
            if ( self.__y + other.__y ) % self.__curve.p() == 0: return INFINITY
            else: return self.double()
        p = self.__curve.p()
        l = ( ( other.__y - self.__y ) * inverse_mod( other.__x - self.__x, p ) ) % p
        x3 = ( l * l - self.__x - other.__x ) % p
        y3 = ( l * ( self.__x - x3 ) - self.__y ) % p
        return Point( self.__curve, x3, y3 )
    def __mul__( self, other ):
        "Multiply a point by an integer"
        def leftmost_bit( x ):
            assert x > 0
            result = 1
            while result <= x: result = 2 * result
            return result // 2
        e = other
        if self.__order: e = e % self.__order
        if e == 0: return INFINITY
        if self == INFINITY: return INFINITY
        assert e > 0
        e3 = 3 * e
        negative_self = Point( self.__curve, self.__x, -self.__y, self.__order )
        i = leftmost_bit( e3 ) // 2
        result = self
        while i > 1:
            result = result.double()
            if ( e3 & i ) != 0 and ( e & i ) == 0: result = result + self
            if ( e3 & i ) == 0 and ( e & i ) != 0: result = result + negative_self
            i = i // 2
        return result
    def __rmul__( self, other ):
        "Multiply a point by an integer"
        return self * other
    def double( self ):
        if self == INFINITY: return INFINITY
        p = self.__curve.p()
        a = self.__curve.a()
        l = ( ( 3 * self.__x * self.__x + a ) * inverse_mod( 2 * self.__y, p ) ) % p
        x3 = ( l * l - 2 * self.__x ) % p
        y3 = ( l * ( self.__x - x3 ) - self.__y ) % p
        return Point( self.__curve, x3, y3 )
    def x( self ):
        return self.__x
    def y( self ):
        return self.__y
    def curve( self ):
        return self.__curve  
    def order( self ):
        return self.__order

def orderlen(order):
    return (1+len("%x"%order))//2 # bytes

class Curve:
    def __init__(self, name, curve, generator, oid):
        self.name = name
        self.curve = curve
        self.generator = generator
        self.order = generator.order()
        self.baselen = orderlen(self.order)
        self.verifying_key_length = 2*self.baselen
        self.signature_length = 2*self.baselen
        self.oid = oid
        self.encoded_oid = encode_oid(*oid)

INFINITY = Point( None, None, None )  
curve_521 = CurveFp( b64toi(_P), -3, b64toi(_B) )
#encoded_oid_ecPublicKey = encode_oid(*(1, 2, 840, 10045, 2, 1))
NIST521p = Curve("NIST521p", curve_521, Point( curve_521, b64toi(_GX), b64toi(_GY), b64toi(_R) ), (1, 3, 132, 0, 35))

class ecdsa:
    def __init__(self):
        curve=NIST521p
        secexp = randrange(curve.order)
        pp = curve.generator*secexp
        self.pkgenerator = curve.generator
        self.pt, n = pp, curve.generator.order()
        if not n: raise "Generator point must have order"
        if not n * pp == INFINITY: raise "Generator point order is bad"
        if pp.x() < 0 or n <= pp.x() or pp.y() < 0 or n <= pp.y(): raise "Out of range"
        self.pkorder, self.privkey = n, secexp

    def verify(self, s, data):
        nb, [r, s], G, n = H(data), [b64toi(x) for x in s.encode('ascii').split(b'/')], self.pkgenerator, self.pkorder
        if r<1 or r>n-1: return False
        if s<1 or s>n-1: return False
        c = inverse_mod(s, n)
        u1, u2 = (nb*c)%n, (r*c)%n
        xy = u1*G+u2*self.pt
        return xy.x() % n == r

    def sign(self, data):
        nb, rk, G, n = H(data), randrange(self.pkorder), self.pkgenerator, self.pkorder
        k = rk % n
        p1 = k * G
        r = p1.x()
        if r == 0: raise "amazingly unlucky random number r"
        s = (inverse_mod(k, n)*(nb+(self.privkey*r)%n))%n
        if s == 0: raise "amazingly unlucky random number s"
        return '%s/%s' % (itob64(r).decode('ascii'), itob64(s).decode('ascii'))

def inverse_mod( a, m ):
    "_"
    if a < 0 or m <= a: a = a % m
    c, d = a, m
    uc, vc, ud, vd = 1, 0, 0, 1
    while c != 0:
        q, c, d = divmod(d, c) + (c,)
        uc, vc, ud, vd = ud - q*uc, vd - q*vc, uc, vc
    assert d == 1
    if ud > 0: return ud
    else: return ud + m

def randrange(order):
    "_"
    entropy = os.urandom
    assert order > 1
    byts = orderlen(order)
    dont_try_forever = 10000 
    while dont_try_forever > 0:
        dont_try_forever -= 1
        cand = int(binascii.hexlify(entropy(byts)), 16)
        if 1 <= cand < order: return cand
        continue
    raise "randrange() tried hard but gave up. Order was %x" % order

################
def h10 (code):
    "_"
    return base64.urlsafe_b64encode(hashlib.sha1(code.encode('utf8')).digest())[:10].decode('ascii')

### LOCAL AES ### (replace PyCrypto AES mainly for macOSX)

class AES0:
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

###########

def gen_pwd ():
    "_"
    code = '%s' % time.mktime(time.gmtime())
    return base64.urlsafe_b64encode(hashlib.sha1(code.encode('ascii')).digest())[:4]

def cmd(post, cd, host='localhost', binary=False):
    "_"
    #print (cd, host)
    co, serv = http.client.HTTPConnection(host), '/'
    if post:
        co.request('POST', serv, urllib.parse.quote(cd))
    else:
        co.request('GET', serv + '?' + urllib.parse.quote(cd))
    return co.getresponse().read() if binary else co.getresponse().read().decode('utf8')    

def agency():
    "_"
    k, host, user, fi, t = get_k()
    src = t[2][-6:].decode('utf8')
    # for instance:
    n, v = '10278/02233', 'Crédit Mutuel/6, Route de Castres/31130/Quint Fonsegrives/0562572138/02233@creditmutuel.fr'
    msg = '/'.join([src, n, v])    
    return cmd(True, '/'.join(['AG', msg, k.sign(msg)]), host.decode('utf8'))

def listday(theday):
    "_"
    k, host, user, fi, t = get_k()
    src = t[2][-6:].decode('utf8')
    d = ('%s' % datetime.datetime.now())[:10]
    msg = '/'.join([src, d])    
    return cmd(True, '/'.join(['LD', msg, k.sign(msg)]), host.decode('utf8'))    

def generate():
    "_"
    email = input('E-mail: ')
    pp1, pp2 = '', ''
    print ('Enter a PassPhrase > 4 characters: ')
    while pp1 != pp2 or len(pp1) < 4:
        pp1 = getpass.getpass('Pass Phrase ?')
        pp2 = getpass.getpass('Retype Pass Phrase ?')
    db = 'keys.db'
    print ('...wait')
    kt = []
    for i in range(10):
        k = ecdsa()
        cm = itob64(k.pt.y())[-6:].decode('utf8')
        kt.append(k)
        print ('(%d)' %i, cm)
    sk = input('Select one key: ')
    k = kt[int(sk)]
    cm = itob64(k.pt.y())[-6:].decode('utf8')
    d = dbm.open(db[:-3], 'c')
    pw = hashlib.sha256(pp1.encode('utf8')).digest()
    #pad = lambda s:s+(32-len(s)%32)*'@'
    #EncodeAES = lambda c,s: base64.urlsafe_b64encode(c.encrypt(pad(s)))
    #ci = EncodeAES(AES.new(pw, AES.MODE_OFB, _IV), '%s' % k.privkey) # AES from PyCrypto
    ci = AES0().encrypt('%s' % k.privkey, pw) # included AES
    d[email] = gen_pwd() + b'/' + b'/'.join([itob64(x) for x in [k.pt.x(), k.pt.y()]]) + b'/' + ci
    d.close()
    os.chmod(db, 511)  
    print ('%s file generated for code %s user: %s' % (db, cm, email))

def find_best():
    "_"
    db = 'search.db'
    d = dbm.open(db[:-3], 'c')
    i = 0
    while True:
        k = ecdsa()
        i += 1
        cm = itob64(k.pt.y())[-6:].decode('utf8')
        if re.search('(cash|ppc|ping|pong|cup|money|france)', cm, re.I):
            d[cm] = b'/'.join([itob64(x) for x in [k.pt.x(), k.pt.y()]]) + b'/' + itob64(k.privkey)
            break
        else:
            sys.stdout.write('.')
            sys.stdout.flush()
            if i%100==0 : print (i)
    d.close()
    os.chmod(db, 511)  
    print ('%s CM found' % db)

def register():
    "_"
    k, host, user, fi, t = get_k()
    today = '%s' % datetime.datetime.now()
    raw = '/'.join([user, t[1].decode('ascii'), t[2].decode('ascii')])    
    msg = '/'.join([today[:10], h10(t[0].decode('ascii')), raw])
    return cmd(True, '/'.join(['PK', '1', raw, k.sign(msg)]), host.decode('utf8'))    

def get_k():
    "_"
    d = dbm.open(__db__[:-3])
    user = d['user'].decode('utf8')
    pp = getpass.getpass('Pass Phrase ?')
    k = ecdsa()
    tab = d[user].split(b'/')
    k.pt = Point(curve_521, b64toi(tab[1]), b64toi(tab[2]))
    pw = hashlib.sha256(pp.encode('utf8')).digest()
    #DecodeAES = lambda c,e: c.decrypt(base64.urlsafe_b64decode(e)).rstrip(b'@')
    #k.privkey = int(DecodeAES(AES.new(pw, AES.MODE_OFB, _IV), tab[3])) # AES from PyCrypto
    k.privkey = int(AES0().decrypt(tab[3], pw)) # included AES
    host, fi = d['host'], d['file']
    d.close()
    return (k, host, user, fi, tab)

def set(k, h):
    "_"
    d = dbm.open(__db__[:-3], 'c')
    d[k] = h
    print ('%s->%s' % (k, h))
    d.close()

def info():
    "_"
    d = dbm.open(__db__[:-3])
    print ('user:%s host:%s file:%s' % (d['user'].decode('utf8'), d['host'].decode('utf8'), d['file'].decode('utf8')))
    d.close()
    
def buy(dest, value, var1='', var2=''):
    "_"
    evalue, txt = '00000', ''
    if var2 != '': txt = var2
    if re.match('[\d\.]{1,6}', var1): evalue = '%05d' % int(float(var1)*100)
    else: txt = var1
    k, host, user, fi , t = get_k()
    src = t[2][-6:].decode('utf8')
    print (src)
    epoch = '%s' % time.mktime(time.gmtime())
    msg = '/'.join([epoch[:-2], src, dest, '%05d' % int(float(value)*100)])
    print('/'.join(['TR', '1', msg, k.sign(msg), evalue, txt]))

    o = cmd(True, '/'.join(['TR', '1', msg, k.sign(msg), evalue, txt]), host.decode('utf8'), True)

    if o[:5].decode('ascii') == 'Error':
        print (o.decode('utf8'))
    else:
        open(fi.decode('utf8'), 'bw').write(o)    
        print ('%s GENERATED' % fi.decode('utf8'))

def proof(dest, status):
    "_"
    k, host, user, fi, t = get_k()
    src = t[2][-6:].decode('utf8')
    epoch = '%s' % time.mktime(time.gmtime())
    msg = '/'.join([epoch[:-2], src, dest, status])
    o = cmd(True, '/'.join(['VD', '1', msg, k.sign(msg)]), host.decode('utf8'), True)
    if o[:5].decode('ascii') == 'Error':
        print (o.decode('utf8'))
    else:
        open(fi.decode('utf8'), 'bw').write(o)    
        print ('%s CERTIFICATE GENERATED' % fi.decode('utf8'))

def usage():
    "_"
    print ('usage TODO!')

def compare():
    from Crypto.Cipher import AES
    pp = 'this is a password'
    msg = 'X'*32
    pw = hashlib.sha256(pp.encode('utf8')).digest()
    pad = lambda s:s+(32-len(s)%32)*'@'
    EncodeAES = lambda c,s: base64.urlsafe_b64encode(c.encrypt(pad(s)))
    DecodeAES = lambda c,e: c.decrypt(base64.urlsafe_b64decode(e)).rstrip(b'@')
    ci1 = EncodeAES(AES.new(pw, AES.MODE_OFB, _IV), msg) # AES from PyCrypto
    ci2 = AES0().encrypt(msg, pw) # included AES
    kp1 = DecodeAES(AES.new(pw, AES.MODE_OFB, _IV), ci1).decode('ascii') # AES from PyCrypto
    kp2 = AES0().decrypt(ci2, pw) # included AES
    kp3 = DecodeAES(AES.new(pw, AES.MODE_OFB, _IV), ci2).decode('ascii') # AES mixed
    kp4 = AES0().decrypt(ci1, pw) # AES mixed
    assert msg==kp1==kp2==kp3==kp4
    

if __name__ == '__main__':
    #compare()
    #find_best()
    if len(sys.argv)==1: info()
    elif len(sys.argv)==2:
        if sys.argv[1] == 'generate': generate()
        elif sys.argv[1] == 'register' : print (register())
        elif sys.argv[1] == 'agency' : agency()
        elif sys.argv[1] == 'test' : set('host','localhost')
        elif sys.argv[1] == 'real' : set('host','pingpongcash.net')
        else: usage()
    elif len(sys.argv)== 3: 
        if sys.argv[1] == 'ld': print (listday(sys.argv[2]))
        elif sys.argv[1] in ('host', 'user', 'file'): set(sys.argv[1], sys.argv[2])
        else: usage()
    elif len(sys.argv) == 4: 
        if sys.argv[1] == 'buy': buy(sys.argv[2], sys.argv[3])
        elif sys.argv[1] == 'proof': proof(sys.argv[2], sys.argv[3])
        else: usage()
    elif len(sys.argv) == 5 and sys.argv[1] == 'buy': buy(sys.argv[2], sys.argv[3], sys.argv[4])
    elif len(sys.argv) == 6 and sys.argv[1] == 'buy': buy(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5])
    else:
        usage()
    #s, f = 'Jun 1 2005', '%b %d %Y'
    #z1 = time.strptime(s, f)
    #z2 = datetime.datetime.strptime(s, f).date() + datetime.timedelta(days=1)
    #print (int(time.mktime(z1)), z2)


    #p = argparse.ArgumentParser(description='Process')
    #p.add_argument('generate', metavar='G')

    sys.exit()
# End ⊔net!
