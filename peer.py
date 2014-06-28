#!/usr/bin/python3
# -*- coding: utf-8 -*-

import os, re, sys, datetime, urllib.parse, hashlib, http.client, dbm.ndbm, base64, random, urllib.request, urllib.error
__app__  = os.path.basename(__file__)[:-3]

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
    return int(hashlib.sha256(b''.join(tab)).hexdigest(), 16) 

def datencode(n=0):
    "4 chars (minute precision)"
    return i2b(int(time.mktime(time.gmtime())/60 + 60*24*n), 4)

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

#######

def H(*tab):
    return hashlib.sha1(b''.join(bytes('%s' % i, 'utf8') for i in tab)).hexdigest()[:10]

def dist(ua, ub):
    a, b = int(H(ua), 16), int(H(ub), 16)
    return b-a if a<b else (2<<80) + b-a

def near(ca, l, s=[]):
    return min(set(l) - set(s) , key=lambda x:dist(ca, x))

def clp(port, v):
    di = '/%s/%s_%s' % (__app__, __app__, port)
    if not os.path.exists(di): os.makedirs(di)
    db = '%s/pub' % di
    if not os.path.isfile(db):
        d = dbm.open(db, 'c')
        d.close()
        os.chmod(db, 511)
    if not os.path.isfile(di+'/lp'): 
        open(di+'/lp', 'wb').write(bytes("{'%s'}" % v, 'utf8'))
    return dbm.open('%s/pub' % di, 'c')

def rlp(port):
    return open('/%s/%s_%s/lp' % (__app__, __app__, port)).read()   

def wlp(port, v):
    return open('/%s/%s_%s/lp' % (__app__, __app__, port), 'wb').write(bytes(v, 'utf8'))

def reg(value):
    reg.v = value
    return value

def application(env, resp):
    "wsgi server app"
    mime, o, ncok, pst = 'text/plain; charset=utf8', 'Error:', [], (env['REQUEST_METHOD'].lower() == 'post')
    host, server, port = env['HTTP_HOST'], env['SERVER_NAME'], env['SERVER_PORT']
    d = clp(port, host)
    if pst:
        arg = urllib.parse.unquote_plus(env['wsgi.input'].read().decode('utf8'))
        if re.match(r'\{[^\}]*\}$', arg):
            l1, l2 = eval(arg), eval(rlp(port))
            wlp(port, '%s' % (l1|l2))
            o = '%s' % (l2-l1)
        elif reg(re.match(r'\+(.*):(.*)$', arg)):
            l, k = eval(rlp(port)), reg.v.group(1)
            r1 = near(k, l)
            r2 = near(k, l, [r1])
            d[reg.v.group(1)] = reg.v.group(2)
            o = 'ok post ADD'
        else: o = 'POST |%s|' % arg
    else: # get
        base, arg = env['PATH_INFO'][1:], urllib.parse.unquote(env['QUERY_STRING'])
        if re.match(r'\S{2,40}$', base) and base != host and check(base):
            l1, l2 = eval(post(base, rlp(port))), eval(rlp(port))
            wlp(port, '%s' % (l1|l2))
            o = '%s updated' % (l1|l2)
        elif base == 'check':
            l = {x for x in filter(lambda i:check(i), eval(rlp(port))-{host})}
            if l: wlp(port, '%s' % (l|{host}))
            o = '%s checked' % l 
        else:
            o = 'GET |%s|%s| %s' % (base, arg, eval(rlp(port)) - {host} )
    d.close()
    resp('200 OK', [('Content-type', mime)] + ncok)
    return [o if mime in ('application/pdf', 'image/png', 'image/jpg') else o.encode('utf8')] 

def check(sv):
    try:
        res = urllib.request.urlopen('http://%s' % sv, timeout=1)
        return True
    except urllib.error.URLError as err: pass
    return False

def post(host, data=''):
    co, serv = http.client.HTTPConnection(host), '/' 
    co.request('POST', serv, urllib.parse.quote(data))
    return co.getresponse().read().decode('utf8')    

if __name__ == '__main__':
    print ('connected') if check('cup') else print ('error')
    print (post('cup:8000', '+jfgdfhdfj:dssdsd'))
