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
#    * Encryption with ECC use an idea of jackjack-jj on github
#-----------------------------------------------------------------------------

import re, os, sys, urllib.parse, hashlib, http.client, base64, dbm.ndbm, datetime, functools, subprocess, time, smtplib, operator, random, getpass

__digest__ = base64.urlsafe_b64encode(hashlib.sha1(open(__file__, 'r', encoding='utf8').read().encode('utf8')).digest())[:10]
__app__    = os.path.basename(__file__)[:-3]
__dfprt__  = 36368
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
        secexp = randrange(self.gen.order)
        pp = self.gen*secexp
        self.pkgenerator, self.pt, n = self.gen, pp, self.gen.order
        if not n: raise 'Generator point must have order!'
        if not n * pp == INFINITY: raise 'Bad Generator point order!'
        if pp.x < 0 or n <= pp.x or pp.y < 0 or n <= pp.y: raise 'Out of range!'
        self.pkorder, self.privkey = n, secexp

    def sign(self, data):
        rk, G, n = randrange(self.pkorder), self.pkgenerator, self.pkorder
        k = rk % n
        p1 = k * G
        r = p1.x
        s = (inverse_mod(k, n) * (H(data) + (self.privkey * r) % n)) % n
        assert s != 0 and r != 0
        return i2b(r, 66) + i2b(s, 66)

def inverse_mod(a, m):
    "_"
    if a < 0 or m <= a: a = a % m
    c, d = a, m
    uc, vc, ud, vd = 1, 0, 0, 1
    while c != 0:
        q, c, d = divmod(d, c) + (c,)
        uc, vc, ud, vd = ud - q*uc, vd - q*vc, uc, vc
    #assert d == 1
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
        return bytes(cipherOut)

    def decrypt(self, cIn, key):
        cipher, iput, output, plain, stringOut, fround, cipherIn = [], [], [], [0]*16, '', True, [i for i in cIn]
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

###### API #####

def register():
    "_"
    pp1, pp2, cm = '', '', ''
    db = dbm.open('keys', 'c')
    while pp1 != pp2 or len(pp1) < 4:
        pp1 = getpass.getpass('Select a passphrase? ')
        pp2 = getpass.getpass('The passphrase again? ')
    print ('...wait')
    k = ecdsa()
    cm = i2b(k.pt.y)[-9:]
    while cm in db:
        k = ecdsa()
        cm = i2b(k.pt.y)[-9:]
    pub, priv = i2b(k.pt.x, 66) + i2b(k.pt.y, 66), AES().encrypt('%s' % k.privkey, hashlib.sha256(pp1.encode('utf8')).digest())
    db[cm] = pub+priv
    db.close()
    print ('Your personnal keys generated in keys.db file. Id: %s' % (btob64(cm)))
    return btob64(pub)

def getpub():
    "_"
    db = dbm.open('keys')
    pub = None 
    for u in db.keys():  pub = db[u][:132]    
    return btob64(pub)

def buy(dst, prc):
    "_"
    db, src, k, dat = dbm.open('keys'), None, ecdsa(), datencode()
    assert(len(dst) == 9)
    for u in db.keys():  src, val, pub = u, db[u][132:], db[u][:132]
    pp = getpass.getpass('Passphrase for \'%s\'? ' % btob64(src))
    print ('...please wait')
    k.privkey, msg = int(AES().decrypt(val, hashlib.sha256(pp.encode('utf8')).digest())), datencode() + src + dst + i2b(prc, 3)
    db.close()
    return btob64(msg + k.sign(msg))

def send(host='localhost', data=''):
    "_"
    app = ''
    co, serv = http.client.HTTPConnection(host), '/' + app
    co.request('POST', serv, urllib.parse.quote(data))
    return co.getresponse().read().decode('utf8')    

def readdb(arg):
    "_"
    d = dbm.open(arg)
    for x in d.keys(): print ('%02d:%03d' % (len(x), len(d[x])), btob64(x),'->', btob64(d[x]))

##### MAIN #####

def usage():
    """If 'keys.db' or 'keys' file does not exist\n'./client.py' creates a new private key in this file and sent public key to a public node
'./client.pt <dbfile>' displays any gnu_berkeley-database content in base64 format
'./client.pt <price> <recipient>' generates and sent a transaction of a float <price> for a string valid <recipient> id
Bad transactions may result from:\n- recipient is unknown or yourself\n- price is higher than your balance\n- signature verification returns false
Connect to %s to see balance report\nContact %s for any question"""
    return usage.__doc__ % (__url__, __email__)

if __name__ == '__main__':
    localnode = 'cup:36368' # for debugging
    node = '%s.fr' % __ppc__
    #node = localnode
    if len(sys.argv)==2:
        if os.path.isfile(sys.argv[1]):
            readdb(sys.argv[1])
        elif re.match(r'\d{1,5}', sys.argv[1]):
            bnk = send(node, 'IBANK')
            aa = buy(b64tob(bytes(bnk, 'ascii')), int(sys.argv[1]))
            open('icheck.txt', 'w').write(aa)
            print ('Transaction generated to %s ibank in \'icheck.txt\' file' % bnk)
        else:
            print (send(node, sys.argv[1]))
    elif len(sys.argv)==1: 
        r = getpub() if (os.path.isfile('keys') or os.path.isfile('keys.db')) else register()
        print(send(node, r)) # need Net connexion
    elif len(sys.argv)==3:
        s = buy(b64tob(bytes(bnk, 'ascii')), int(float(sys.argv[1])*100))
        print (send(node, s)) # need Net connexion
    else:
        print (usage())
# End ⊔net!

