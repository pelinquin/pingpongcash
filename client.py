#!/usr/bin/python3
# -*- coding: utf-8 -*-

import re, os, sys, math, urllib.parse, hashlib, http.client, base64, dbm, binascii, datetime, zlib, functools, subprocess, time
from Crypto.PublicKey import RSA

RSA_E = 65537

def itob64(n):
    "utility to transform int to base64"
    c = hex(n)[2:]
    if len(c)%2: c = '0'+c
    return re.sub(b'=*$', b'', base64.urlsafe_b64encode(bytes.fromhex(c)))

def b64toi(c):
    "transform base64 to int"
    if c == '': return 0
    return int.from_bytes(base64.urlsafe_b64decode(c + b'='*((4-(len(c)%4))%4)), 'big')

def H(*tab):
    "hash"
    return int(hashlib.sha1(b''.join(bytes('%s' % i, 'utf8') for i in tab)).hexdigest(), 16)
 
def sign(d, n, msg):
    "_"
    return itob64(pow(H(msg), d, n))

def verify(e, n, msg, s):
    "_"
    return (pow(b64toi(s), e, n) == H(msg)) 

def format_cmd(post, cmd, binary=False, host='localhost'):
    co, serv = http.client.HTTPConnection(host), '/ppc'    
    if post:
        co.request('POST', serv, urllib.parse.quote(cmd))
    else:
        co.request('GET', serv + '?' + urllib.parse.quote(cmd))
    if binary:
        return co.getresponse().read()    
    else:
        return co.getresponse().read().decode('utf8')    

def register(liban):
    "for testing"
    d = dbm.open('/cup/ppc/keys', 'c')
    for y in liban:
        k = RSA.generate(1024, os.urandom)        
        ref = compact(y)
        d[ref] = bytes('/'.join([liban[y], y] + [itob64(x).decode('ascii') for x in (k.d, k.n)]), 'ascii')
    d.close()

CHAR_MAP = {"A":"10", "B":"11", "C":"12", "D":"13", "E":"14", "F":"15", "G":"16", "H":"17", "I":"18", "J":"19", 
            "K":"20", "L":"21", "M":"22", "N":"23", "O":"24", "P":"25", "Q":"26", "R":"27", "S":"28", "T":"29", 
            "U":"30", "V":"31", "W":"32", "X":"33", "Y":"34", "Z":"35"}
 
def compact (iban):
    "_"
    assert len(iban) == 33
    ll = re.sub(' ', '', iban[4:]) + iban[:4]
    for x in CHAR_MAP: ll = re.sub(x, CHAR_MAP[x], ll)
    assert int(ll) % 97 == 1
    bic, cnt = iban[5:17], iban[17:]
    for x in CHAR_MAP: cnt = re.sub(x, CHAR_MAP[x], cnt)
    ibic, icnt = itob64(int(re.sub(' ', '', bic))), itob64(int(re.sub(' ', '', cnt)))
    return '%s/%s' % (ibic.decode('ascii'), icnt.decode('ascii'))

def findiban (iban):
    "_"
    for z in range (99):
        ll = iban[4:] + '%02d' % z + iban[:4]
        for x in CHAR_MAP: ll = re.sub(x, CHAR_MAP[x], ll)
        if int(ll) % 97 == 1:
            return z

if __name__ == '__main__':

    liban = {
        'FR76 1780 7000 1445 3199 4029 836': 'BPU1',
        'FR76 1780 7000 1445 6208 6047 866': 'BPUB',        
        'FR76 1820 6002 1054 8726 6700 217': 'CRAG',
        'FR76 1027 8022 3300 0202 8350 157': 'CRMT',
        'FR19 2004 1100 2000 5874 1005 T15': 'POST',
        }
    #register(liban)

    CRAG = 'bIQnkg/BP2alRu5'
    POST = 'd3RKxA/iMReFzM'
    CRMT = 'PUMEeQ/eOYqzQ'
    BPU1 = 'aiNTbg/BB8v5O8M'
    BPUB = 'aiNTbg/BCYxhLB6' 

    d = dbm.open('/cup/ppc/keys')
    kCRAG = [b64toi(x) for x in d[CRAG].split(b'/')[2:]]
    kPOST = [b64toi(x) for x in d[POST].split(b'/')[2:]]
    kCRMT = [b64toi(x) for x in d[CRMT].split(b'/')[2:]]
    kBPU1 = [b64toi(x) for x in d[BPU1].split(b'/')[2:]]
    kBPUB = [b64toi(x) for x in d[BPUB].split(b'/')[2:]]
    d.close()

    epoch, today = '%s' % time.mktime(time.gmtime()), '%s' % datetime.datetime.now()

    # 1/ register account
    msg = '/'.join([BPU1[7:], itob64(H('hero'))[:10].decode('ascii'), itob64(kBPU1[1]).decode('ascii')])
    s = sign(kBPU1[0], kBPU1[1], msg)
    print (1, 'REGISTER', format_cmd(True, '/'.join(['R', '1', msg, s.decode('ascii')]), False))

    msg = '/'.join([epoch[:-2], BPUB[:6], BPUB[7:], BPU1[:6], BPU1[7:], '000.00'])    
    s = sign(kBPUB[0], kBPUB[1], msg)
    print (2, 'VALIDATE', format_cmd(True, '/'.join(['T', '1', msg, s.decode('ascii')]), False))

    msg = '/'.join([epoch[:-2], BPU1[:6], BPU1[7:], CRMT[:6], CRMT[7:], '018.45'])    
    s = sign(kBPU1[0], kBPU1[1], msg)
    print (3,'PAY TO ADMIN', format_cmd(True, '/'.join(['T', '1', msg, s.decode('ascii')]), False))

    msg = '/'.join([epoch[:-2], BPU1[:6], BPU1[7:]])
    s = sign(kBPU1[0], kBPU1[1], msg+today[:-10])
    print (4, 'STATUS', format_cmd(True, '/'.join(['S', '1', msg, s.decode('ascii')]), False))

    msg = '/'.join([epoch[:-2], POST[:6], POST[7:], BPU1[:6], BPU1[7:], '10.00'])    
    s = sign(kPOST[0], kPOST[1], msg)
    print (5, 'OUTSIDE', format_cmd(True, '/'.join(['T', '1', msg, s.decode('ascii')]), False))

    msg = epoch[:-2]
    s = sign(kCRMT[0], kCRMT[1], msg+today[:-10])
    print (6, 'LIST', format_cmd(True, '/'.join(['A', '1', msg, s.decode('ascii')]), False))

    # change pubkey
    # block transactions on the web
    # new pubkey old lost 

# End ⊔net!
