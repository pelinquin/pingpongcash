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

import re, os, sys, urllib.parse, hashlib, http.client, base64, dbm.ndbm, datetime, functools, subprocess, time, smtplib, operator, getpass
import gmpy2 # for inverse_mod fast computing

__app__    = os.path.basename(__file__)[:-3]
__dfprt__  = 80
__base__   = '/%s/%s_%s/' % (__app__, __app__, __dfprt__)
__ef__     = 'eurofranc'
__email__  = 'contact@%s.fr' % __ef__

_SVGNS     = 'xmlns="http://www.w3.org/2000/svg"'
_b58char   = '123456789abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ'
_root_id   = 'AdminJqjFdcY'
_root_pkey = 'AdMctT3bXbwrTBGkB5eKAG74qIqShRRy1nHa_NWCHsxmKhmZeE_aWgo_S251td8d6C5uti6TymQSSZvhmO1b19pI/AYYPFxkKL_13dnhBGXdFdmDQhQEZZbc1P7GDDrZZwU0FSGuwc53_AxHk1vVRte7bdmhzIcOUMUvO' 

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
    #return b2i(hashlib.sha256(b''.join(tab)).digest()) 
    return int(hashlib.sha256(b''.join(tab)).hexdigest(), 16)

def datdecode(tt):
    "4 chars (minute precision)"
    return time.strftime('%d/%m/%y %H:%M', time.localtime(float(b2i(tt)*60)))

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

    def verify(self, sig, data):
        r, s, G, n = b2i(sig[:66]), b2i(sig[66:]), self.pkgenerator, self.pkorder
        if r < 1 or r > n-1 or s < 1 or s > n-1: return False
        c = inverse_mod(s, n)
        u1, u2 = (H(data) * c) % n, (r * c) % n
        z = u1 * G + u2 * self.pt
        return z.x % n == r

def inverse_mod2(a, m):
    if a < 0 or m <= a: a = a % m
    c, d = a, m
    uc, vc, ud, vd = 1, 0, 0, 1
    while c != 0:
        q, c, d = divmod(d, c) + (c,)
        uc, vc, ud, vd = ud - q*uc, vd - q*vc, uc, vc
    if ud > 0: return ud
    else: return ud + m

def inverse_mod1(a, m):
    return pow(a, m-2, m)

def inverse_mod(a, m):
    return gmpy2.invert(a, m)

##### API #####

def send_post(host='localhost', data=''):
    "_"
    co, serv = http.client.HTTPConnection(host), '/ef/' 
    co.request('POST', serv, data)
    return co.getresponse().read().decode('ascii')    

def send_get(host='localhost', data=''):
    "_"
    co = http.client.HTTPConnection(host)
    co.request('GET', '/ef/?' + urllib.parse.quote(data))
    return co.getresponse().read()    

##### WEB APP #####

def blc(d, cm):
    "get balance"
    if cm in d['blc']: return int(d['blc'][cm])
    bal = 0
    for t in [x for x in d['txn'].keys() if len(x) == 13]:
        v = b2i(d['txn'][t][9:11])
        if cm == d['txn'][t][:9]: bal += v 
        if cm == t[4:]:           bal -= v
    return bal

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

def application(environ, start_response):
    "wsgi server app"
    mime, o, now, fname, port = 'text/plain; charset=utf8', 'error', '%s' % datetime.datetime.now(), 'default.txt', environ['SERVER_PORT']
    (raw, way) = (environ['wsgi.input'].read(), 'post') if environ['REQUEST_METHOD'].lower() == 'post' else (urllib.parse.unquote(environ['QUERY_STRING']), 'get')
    base, ncok = environ['PATH_INFO'][1:], []
    d = init_dbs(('pbk', 'txn', 'blc'), port)
    if way == 'post':
        s = raw.decode('ascii')
        r = b64tob(bytes(s, 'ascii'))            
        if re.match('\S{12}$', s) and r in d['pbk']: # get balance
            o = '%d' % blc(d, r)
        elif re.match('\S{16}$', s): # get last transaction
            src, pos = r[:9], b2i(r[9:])
            if src in d['pbk']:
                if src in d['txn']:
                    li = d['txn'][src].split(b':')
                    if pos > 0 and pos < len(li):
                        key = li[pos] + src if len(li[pos]) == 4 else li[pos] 
                        o = btob64(i2b(len(li), 2) + key + d['txn'][key][:24]).decode('ascii') # len: 39->52
                else:
                    o = 'none'
        elif re.match('\S{20}$', s): # check transaction (short)
            u, dat, src, val = r[:13], r[:4], r[4:13], r[:-2]
            if u in d['txn'] and d['txn'][9:11] == val: 
                o = 'valid'
        elif re.match('\S{32}$', s): # check transaction (long)
            u, dst, val = r[:13], r[13:22], r[:-2]
            if u in d['txn'] and d['txn'][:9] == dst and d['txn'][9:11] == val: 
                o = 'valid'
        elif re.match('\S{176}$', s): # register publickey
            pbk, src, v = r, r[-9:], r[:-9]
            if src in d['pbk']: 
                o = 'old'
            else:
                d['pbk'][src], o = v, 'new'
        elif re.match('\S{208}$', s): # add transaction
            u, dat, v, src, dst, val, msg, sig, k = r[:13], r[:4], r[13:-132], r[4:13], r[13:22], b2i(r[22:24]), r[:-132], r[-132:], ecdsa()
            if src in d['pbk'] and dst in d['pbk'] and src != dst:
                k.pt = Point(c521, b2i(d['pbk'][src][:66]), b2i(d['pbk'][src][66:]+src))
                if k.verify(sig, msg): 
                    if u in d['txn']: 
                        o = 'old' 
                    else:
                        b = blc(d, src)
                        if b + 10000 > val: # allows temporary 100 €f for testing !
                            sep = b':'
                            d['txn'][u], o = v + sig, 'new' #'%d' (b-val)
                            d['txn'][src] = d['txn'][src] + sep + dat if src in d['txn'] else dat # shortcut
                            d['txn'][dst] = d['txn'][dst] + sep + u if dst in d['txn'] else u  # shortcut
                            d['blc'][src] = '%d' % ((int(d['blc'][src])-val) if src in d['blc'] else (-val)) # shortcut
                            d['blc'][dst] = '%d' % ((int(d['blc'][dst])+val) if dst in d['blc'] else val)  # shortcut
                        else:
                            o += ' balance!'
                else:
                    o += ' signature!'
            else:
                o += ' ids!'
    else: # get
        s = raw # use directory or arygument
        if s == '': o = 'Attention !\nLe site est temporairement en phase de test de l\'application iOS8 pour iPhone4-6\nVeuillez nous en excuser\nPour toute question: contact@eurofranc.fr'
        else:
            r = b64tob(bytes(s, 'ascii'))            
            if re.match('\S{12}$', s) and r in d['pbk']: # get balance
                o = '%d' % blc(d, r)
            elif re.match('\S{20}$', s): # check transaction (short)
                u, dat, src, val = r[:13], r[:4], r[4:13], r[:-2]
                if u in d['txn'] and d['txn'][9:11] == val: 
                    o = 'valid'
            elif re.match('\S{32}$', s): # check transaction (long)
                u, dst, val = r[:13], r[13:22], r[:-2]
                if u in d['txn'] and d['txn'][:9] == dst and d['txn'][9:11] == val: 
                    o = 'valid'
            elif re.match('\S{176}$', s): # register publickey
                pbk, src, v = r, r[-9:], r[:-9]
                if src in d['pbk']: 
                    o = 'old'
                else: 
                    d['pbk'][src], o = v, 'new'
            elif re.match('\S{208}$', s): # add transaction
                u, v, src, dst, val, msg, sig, k = r[:13], r[13:-132], r[4:13], r[13:22], r[22:24], r[:-132], r[-132:], ecdsa()
                if src in d['pbk']:
                    k.pt = Point(c521, b2i(d['pbk'][src][:66]), b2i(d['pbk'][src][66:]+src))
                    if k.verify(sig, msg): 
                        if u in d['txn']: 
                            o = 'old' 
                        else:
                            d['txn'][u], o = v + sig, 'new'
                    else:
                        o += ' signature!'
                else:
                    o += ' id!'
    for db in d: d[db].close()
    start_response('200 OK', [('Content-type', mime)] + ncok)
    return [o if mime in ('application/pdf', 'image/png', 'image/jpg') else o.encode('utf8')] 

def test():
    print (send_get('cup', ''))
    print (send_post('cup', btob64(b'h'*9)))
    print (send_post('cup', btob64(b'h'*12)))
    print (send_post('cup', btob64(b'h'*15)))
    print (send_post('cup', btob64(b'h'*24)))
    print (send_post('cup', btob64(b'h'*132)))

    print (send_post('cup', btob64(b'h'*156)))

    id1 = '5eI6gg80GKtF'
    id2 = '5eKgP0ah3mrv'
    id3 = 'SVahsR_yhTxl'

    print (send_get('eurofranc.fr', id3))

if __name__ == '__main__':
    #test()
    import cProfile
    k = ecdsa()
    kx, ky = 1497626729486698250092836588258522241576986267962509549806031472029777015910199567058370933525287831904420674640244116785460336785990307731327653260061341184, 3913334906008739579549527439581844548577377240182775572287928609736407393883660334541807646401094599739670101579293967007613985154383349376877321098382392173
    k.pt = Point(c521, kx, ky)
    k.privkey = 454086624460063511464984254936031011189294057512315937409637584344757371137
    s = b'AG-ytve_8p-xCFnL-u5iyg9hWPr-8zSj5Ruvu7Ki9XZdqDUzOCa_nq1c87efPEWaLxBs6o-B1mUJNEvb-2Rp4HYAAbxKVzub8ltEjGDi10ncGtrWUMZU41ziHgfsWdtRGZj48RwB-8hpKncK3BBhH7Jj-PErJXCKNEvWIQ0UuLLtlzpv'
    cProfile.run ("k.verify(b64tob(s), b'hello')")
    #assert k.verify(b64tob(s), b'hello')

    print (inverse_mod(42, 2017))
    print (inverse_mod1(42, 2017))
    print (gmpy2.invert(42,2017))
    
# End ⊔net!