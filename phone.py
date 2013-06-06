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
This code simulates the iPhone
"""

import re, os, sys, math, urllib.parse, hashlib, http.client, base64, dbm, binascii, datetime, zlib, functools, time, smtplib, unidecode

# NIST Curve P-521:

_B = b'UZU-uWGOHJofkpohoLaFQO6i2nJbmbMV87i0iZGO8QnhVhk5Uex-k3sWUsC9O7G_BzVz34g9LDTx70Uf1GtQPwA'
_GX = b'xoWOBrcEBOnNnj7LZiOVtEKcZIE5BT-1Ifgor2BrTT26oUted-_nWSj-HcEnov-o3jNIs8GFakKb-X5-McLlvWY'
_GY = b'ARg5KWp4mjvABFyKX7QsfRvZmPVESVebRGgXr70XJz5mLJfucple9CZAxVC5AT-tB2E1PHCGonLCQIi-lHaf0WZQ'
_P = b'Af' + b'_'*86
_R = b'Af' + b'_'*42 + b'-lGGh4O_L5Zrf8wBSPcJpdA7tcm4iZxHrrtvtx6ROGQJ'


def reg(value):
    " function attribute is a way to access matching group in one line test "
    reg.v = value
    return value

def itob64(n):
    " utility to transform int to base64"
    c = hex(n)[2:]
    if len(c)%2: c = '0'+c
    return re.sub(b'=*$', b'', base64.urlsafe_b64encode(bytes.fromhex(c)))

def itob32(n):
    " utility to transform int to base64"
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
        """The curve of points satisfying y^2 = x^3 + a*x + b (mod p)."""
        self.__p, self.__a, self.__b = p, a, b
    def p( self ):
        return self.__p
    def a( self ):
        return self.__a
    def b( self ):
        return self.__b
    def contains_point( self, x, y ):
        return ( y * y - ( x * x * x + self.__a * x + self.__b ) ) % self.__p == 0

class Point( object ):
    def __init__( self, curve, x, y, order = None ):
        """curve, x, y, order; order (optional) is the order of this point."""
        self.__curve = curve
        self.__x = x
        self.__y = y
        self.__order = order
        if self.__curve: assert self.__curve.contains_point( x, y )
        if order: assert self * order == INFINITY
    def __cmp__( self, other ):
        """Return 0 if the points are identical, 1 otherwise."""
        if self.__curve == other.__curve and self.__x == other.__x and self.__y == other.__y: return 0
        else: return 1
    def __add__( self, other ):
        """Add one point to another point."""
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
        """Multiply a point by an integer."""
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
        """Multiply a point by an integer."""
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
encoded_oid_ecPublicKey = encode_oid(*(1, 2, 840, 10045, 2, 1))
NIST521p = Curve("NIST521p", curve_521, Point( curve_521, b64toi(_GX), b64toi(_GY), b64toi(_R) ), (1, 3, 132, 0, 35))

class ecdsa:
    def __init__(self):
        curve=NIST521p
        secexp = randrange(curve.order)
        pp = curve.generator*secexp
        self.pkgenerator = curve.generator
        self.pt, n = pp, curve.generator.order()
        if not n: raise "Generator point must have order."
        if not n * pp == INFINITY: raise "Generator point order is bad."
        if pp.x() < 0 or n <= pp.x() or pp.y() < 0 or n <= pp.y(): raise "Out of range."
        self.pkorder, self.privkey = n, secexp

    def verify(self, s, data):
        nb, [r, s], G, n = H(data), [b64toi(x) for x in s.encode('ascii').split(b'/')], self.pkgenerator, self.pkorder
        if r < 1 or r > n-1: return False
        if s < 1 or s > n-1: return False
        c = inverse_mod( s, n )
        u1, u2 = ( nb * c ) % n, ( r * c ) % n
        xy = u1 * G + u2 * self.pt
        return xy.x() % n == r

    def sign(self, data):
        nb, rk, G, n = H(data), randrange(self.pkorder), self.pkgenerator, self.pkorder
        k = rk % n
        p1 = k * G
        r = p1.x()
        if r == 0: raise "amazingly unlucky random number r"
        s = ( inverse_mod( k, n ) * ( nb + ( self.privkey * r ) % n ) ) % n
        if s == 0: raise "amazingly unlucky random number s"
        return '%s/%s' % (itob64(r).decode('ascii'), itob64(s).decode('ascii'))

def inverse_mod( a, m ):
    if a < 0 or m <= a: a = a % m
    c, d = a, m
    uc, vc, ud, vd = 1, 0, 0, 1
    while c != 0:
        q, c, d = divmod( d, c ) + ( c, )
        uc, vc, ud, vd = ud - q*uc, vd - q*vc, uc, vc
    assert d == 1
    if ud > 0: return ud
    else: return ud + m

def randrange(order):
    entropy = os.urandom
    assert order > 1
    byts = orderlen(order)
    dont_try_forever = 10000 # gives about 2**-60 failures for worst case
    while dont_try_forever > 0:
        dont_try_forever -= 1
        candidate = int(binascii.hexlify(entropy(byts)), 16)
        if 1 <= candidate < order: return candidate
        continue
    raise "randrange() tried hard but gave up. Order was %x" % order

################
def h10 (code):
    "_"
    return base64.urlsafe_b64encode(hashlib.sha1(code.encode('utf8')).digest())[:10].decode('ascii')

def test_ecdsa():
    k = ecdsa()
    msg = 'Hello World!'
    s = k.sign(msg) 
    print (s, len(s))
    print(k.verify(s, msg))

def gen_pwd ():
    "_"
    code = '%s' % time.mktime(time.gmtime())
    return base64.urlsafe_b64encode(hashlib.sha1(code.encode('ascii')).digest())[:4]

def generate(name):
    "_"
    db = 'secret.db'
    if not os.path.isfile(db):
        d = dbm.open(db[:-3], 'c')
        d['__N'] = '0'
        d.close()
        os.chmod(db, 511)
    d = dbm.open(db[:-3], 'c')
    k = ecdsa()
    d[name] = gen_pwd() + b'/' + b'/'.join([itob64(x) for x in [k.pt.x(), k.pt.y(), k.privkey]])
    d.close()

def cmd(post, cd, host='localhost', binary=False):
    "_"
    co, serv = http.client.HTTPConnection(host), '/cup/' if host == 'àà.eu' else '/'
    if post:
        co.request('POST', serv, urllib.parse.quote(cd))
    else:
        co.request('GET', serv + '?' + urllib.parse.quote(cd))
    return co.getresponse().read() if binary else co.getresponse().read().decode('utf8')    

def register(mail, host):
    "_"
    today = '%s' % datetime.datetime.now()
    db = 'secret.db'
    d, k = dbm.open(db[:-3]), ecdsa()
    tab = d[mail].split(b'/')
    k.pt, k.privkey = Point(curve_521, b64toi(tab[1]), b64toi(tab[2])), b64toi(tab[3]) 
    d.close()
    raw = '/'.join([mail, tab[1].decode('ascii'), tab[2].decode('ascii')])    
    msg = '/'.join([today[:10], h10(tab[0].decode('ascii')), raw])
    print (cmd(True, '/'.join(['PK', '1', raw, k.sign(msg)]), host))    

def transaction(mail, src, dest, value, fi, host):
    "_"
    epoch = '%s' % time.mktime(time.gmtime())
    db = 'secret.db'
    d, k = dbm.open(db[:-3]), ecdsa()
    tab = d[mail].split(b'/')
    k.pt, k.privkey = Point(curve_521, b64toi(tab[1]), b64toi(tab[2])), b64toi(tab[3]) 
    d.close()
    msg = '/'.join([epoch[:-2], src, dest, '%05d' % value])
    sig = k.sign(msg)
    o = cmd(True, '/'.join(['TR', '1', msg, sig]), host, True)
    assert k.verify(sig, msg) # for utf8!
    if o[:5].decode('ascii') == 'Error':
        print (o.decode('utf8'))
    else:
        open('%s.pdf' % fi, 'bw').write(o)    
        print ('%s.pdf GENERATED' % fi)

def validate(mail, src, dest, status, fi, host):
    "_"
    epoch = '%s' % time.mktime(time.gmtime())
    db = 'secret.db'
    d, k = dbm.open(db[:-3]), ecdsa()
    tab = d[mail].split(b'/')
    k.pt, k.privkey = Point(curve_521, b64toi(tab[1]), b64toi(tab[2])), b64toi(tab[3]) 
    d.close()
    msg = '/'.join([epoch[:-2], src, dest, status])    
    o = cmd(True, '/'.join(['VD', '1', msg, k.sign(msg)]), host, True)    
    if o[:5].decode('ascii') == 'Error':
        print (o.decode('utf8'))
    else:
        open('%s.pdf' % fi, 'bw').write(o)    
        print ('%s.pdf CERTIFICATE GENERATED' % fi)

def agency(mail, src, host):
    "_"
    db = 'secret.db'
    d, k = dbm.open(db[:-3]), ecdsa()
    tab = d[mail].split(b'/')
    k.pt, k.privkey = Point(curve_521, b64toi(tab[1]), b64toi(tab[2])), b64toi(tab[3]) 
    d.close()
    n, v = '10278/02233', 'Crédit Mutuel/6, Route de Castres/31130/Quint Fonsegrives/0562572138/02233@creditmutuel.fr'
    msg = '/'.join([src, n, v])    
    print (cmd(True, '/'.join(['AG', msg, k.sign(msg)]), host))    

def listday(mail, src, host):
    "_"
    db = 'secret.db'
    d, k = dbm.open(db[:-3]), ecdsa()
    tab = d[mail].split(b'/')
    k.pt, k.privkey = Point(curve_521, b64toi(tab[1]), b64toi(tab[2])), b64toi(tab[3]) 
    d.close()
    msg = '/'.join([src, '2013-06-05'])    
    print (cmd(True, '/'.join(['LD', msg, k.sign(msg)]), host))    

def run_local():
    host = 'cup'
    #agency('contact@pingpongcash.net', 'to2TyF', host)
    #register('ct@àà.eu', host)
    #register('contact@pingpongcash.net', host)
    #register('tom.fournier@free.fr', host)
    #transaction('ct@àà.eu', 'Sxlhri', 'Sxlhri', 375, host) 
    transaction('contact@pingpongcash.net', 'BkN5g0', 'BkN5g0', 94375, 'test', host)
    transaction('contact@pingpongcash.net', 'BkN5g0', 'Valérie Fournier', 99999, 'mac', host) 
    validate('contact@pingpongcash.net', 'BkN5g0', 'BkN5g0', 'B', 'certif', host) 
    
    #transaction('contact@pingpongcash.net', 'BkN5g0', 'é ç è à ä â î ï ô öûü', 1, 'accent', host) 
    #transaction('contact@pingpongcash.net', 'BkN5g0', 'Spécimen XXXX Annulé', 12318, 'specimen', host) 
    listday('contact@pingpongcash.net', 'BkN5g0', host) 

def run_rpi():
    host = 'àà.eu'
    agency('contact@pingpongcash.net', 'CwPJa4', host)
    #register('ct@àà.eu', host)
    #register('contact@pingpongcash.net', host)
    #transaction('ct@àà.eu', 'Sxlhri', 'Sxlhri', 375, host) 
    #transaction('contact@pingpongcash.net', 'to2TyF', 'to2TyF', 94375, 'test', host)
    transaction('contact@pingpongcash.net', 'CwPJa4', 'éèàçêùï', 311, 'mac1', host) 

    #transaction('contact@pingpongcash.net', 'to2TyF', 'Dorian Litvine', 13, 'dorian', host) 

if __name__ == '__main__':
    #test_ecdsa()
    #generate('contact@pingpongcash.net')
    #generate('pelinquin@gmail.com')
    #generate('lfournier@free.fr')
    #generate('ct@àà.eu')
    #generate('tom.fournier@free.fr')

    run_local()
    #run_rpi()
    print (unidecode.unidecode('éçeràù'))
    sys.exit()
# End ⊔net!
