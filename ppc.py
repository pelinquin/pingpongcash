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
"_"

import re, os, sys, math, urllib.parse, hashlib, http.client, base64, dbm, binascii, datetime, zlib, functools, subprocess, time

__digest__ = base64.urlsafe_b64encode(hashlib.sha1(open(__file__, 'r', encoding='utf8').read().encode('utf8')).digest())[:5]
__app__    = os.path.basename(__file__)[:-3]
__ppc__    = 'pingpongcash'
__email__  = 'contact@%s.net' % __ppc__
__url__    = 'http://%s.net' % __ppc__
_XHTMLNS   = 'xmlns="http://www.w3.org/1999/xhtml"'
_SVGNS     = 'xmlns="http://www.w3.org/2000/svg"'
_XLINKNS   = 'xmlns:xlink="http://www.w3.org/1999/xlink"'

RSA_E = 65537

"""
Small is beautiful!
"""

def reg(value):
    " function attribute is a way to access matching group in one line test "
    reg.v = value
    return value

def init_db(db):
    "_"
    di = '/cup/%s' % __app__
    if not os.path.exists(di):
        os.makedirs(di)
    if not os.path.isfile(db):
        d = dbm.open(db[:-3], 'c')
        d.close()
        os.chmod(db, 511)

def log(s, ip=''):
    "Append to head log file"
    logf, now = '/cup/%s/log' % __app__, '%s' % datetime.datetime.now()
    if not os.path.isfile(logf): open(logf, 'w', encoding='utf8').write('%s|%s Logfile Creation\n' % (now[:-7], ip) )     
    cont = open(logf, 'r', encoding='utf8').read()
    open(logf, 'w', encoding='utf8').write('%s|%s|%s\n%s' % (now[:-7], ip, s, cont))

def app_update(host):
    "_"
    here = os.path.dirname(os.path.abspath(__file__))
    cmd = 'cd %s; ls' % here  if host == 'cup' else 'cd %s/..; rm -rf %s; git clone https://github.com/pelinquin/%s.git' % (here, __ppc__, __ppc__) 
    out, err = subprocess.Popen((cmd), shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
    o = '<html><pre>Application Update...\n'
    o += 'Error:%s\n' % err if err else 'Message:%s\nUpdate OK\n' % out.decode('utf-8')
    o += '</pre><br/><a href="%s">Reload the new version</a></html>' % __app__
    return o

def application(environ, start_response):
    "wsgi server app"
    mime, o, db, now, fname = 'text/plain; charset=utf8', 'Error:', '/cup/%s/trx.db' % __app__, '%s' % datetime.datetime.now(), 'default.txt'
    init_db(db)
    init_db('/cup/ppc/keys.db')
    (raw, way) = (environ['wsgi.input'].read(), 'post') if environ['REQUEST_METHOD'].lower() == 'post' else (urllib.parse.unquote(environ['QUERY_STRING']), 'get')
    d = dbm.open(db[:-3], 'c')
    if way == 'post':
        arg = urllib.parse.unquote_plus(raw.decode('utf8'))
        # REGULAR TRANSACTION
        # if bicb:
        #   if $ and date and (bics == admin or date > now):
        #     total(bics) += val
        #     set transaction ok
        #     if bics == admin:
        #       set date bicb == deadline(val)
        #   else:
        #     E validation date passed or locked
        # if bics:
        #   if bicb == bank 
        #      !->$
        #      if date == '':
        #        set date bics = now
        #   if bicb:
        #     total(bicb) += val
        # if not bicb or not bics:
        #   E not validated
        #
        # (T)ransaction
        if reg(re.match(r'^T/1/((\d{10,16})/([^/]{3,20})/([^/]{3,20})/([^/]{3,20})/([^/]{3,20})/(\d{3}\.\d{2}))/([^/]{150,200})(|\d{3}\.\d{2})$', arg)):
            msg = reg.v.group(1)
            epoch = reg.v.group(2)
            bicb = bytes(reg.v.group(3), 'ascii')
            s_cntb, cntb = reg.v.group(4), bytes(reg.v.group(4), 'ascii')
            bics = bytes(reg.v.group(5), 'ascii')
            s_cnts, cnts = reg.v.group(6), bytes(reg.v.group(6), 'ascii')
            val1 = reg.v.group(7)
            s_sig, sig = reg.v.group(8), bytes(reg.v.group(8), 'ascii')
            val2 = reg.v.group(9)
            if bicb == d['$bic']:
                if cntb in d.keys():
                    argb = d[cntb].decode('ascii').split('/')
                    if verify(RSA_E, b64toi(argb[5].encode('ascii')), msg, sig):
                        k = '</%s/%s' % (epoch, s_cntb)
                        if k.encode('ascii') in d.keys():
                            o += 'transaction already done'
                        else:
                            if argb[0] == '*':
                                if float(val1) <= float(argb[1]):
                                    adm = d['$admin'].split(b'/')
                                    now = datetime.datetime.now().date()
                                    if (argb[3] and datetime.datetime.strptime(argb[3], '%Y-%m-%d').date() > now) or (bics == adm[0] and cnts == adm[1]):
                                        d[cntb] = '*/%6.2f/%s' % (float(argb[1]) - float(val1), '/'.join(argb[2:]))
                                        d[k] = '/'.join([bics.decode('ascii'), cnts.decode('ascii'), val1, val2, s_sig])
                                        o = 'TRANSACTION OK'
                                    else:
                                        o += 'validation date passed'
                                    if bics == adm[0] and cnts == adm[1]:
                                        argb = d[cntb].decode('ascii').split('/')
                                        ds = int(float(val1)*100)
                                        start = datetime.datetime.now() if argb[3] == '' else datetime.datetime.strptime(argb[3], '%Y-%m-%d').date()
                                        deadline = '%s' % (start + datetime.timedelta(days=ds))
                                        d[cntb] = '/'.join(argb[:3] + [deadline[:10],] + argb[4:])
                                        o = 'PAYED'
                                else:
                                    o += 'not balanced'
                            elif argb[0] == '$' and bics == d['$bic'] and cnts in d.keys():
                                args = d[cnts].decode('ascii').split('/')
                                now = '%s' % datetime.datetime.now()
                                dl = now[:10] if args[3] == '' else args[3] 
                                d[cnts] = '*/' + '/'.join(args[1:3] + [dl,] + args[4:])
                            else:
                                o += 'locked account'
                    else:
                        o += 'bad signature'
                else:
                    o += '%s not registered !' % cntb
            if bics == d['$bic'] and cnts in d.keys():
                k = '>/%s/%s' % (epoch, s_cnts)
                args = d[cnts].decode('ascii').split('/')
                d[cnts] = '%s/%6.2f/%s' % (args[0], float(args[1]) + float(val1), '/'.join(args[2:]))
                d[k] = '/'.join([bics.decode('ascii'), cntb.decode('ascii'), val1, val2, s_sig])
                o = 'RECEIVED TRX'
            if bicb != d['$bic'] and bics != d['$bic']:
                o += 'not valid iban' 
        # GET PERSONAL (S)TATUS
        elif reg(re.match(r'^S/1/((\d{10,16})/([^/]{3,20})/([^/]{3,20}))/([^/]{150,200})$', arg)):
            today = '%s' % datetime.datetime.now()
            msg = reg.v.group(1)
            epoch = reg.v.group(2)
            bic = bytes(reg.v.group(3), 'ascii')
            cnt = bytes(reg.v.group(4), 'ascii')
            sig = bytes(reg.v.group(5), 'ascii')
            o += 'balance request'
            if bic == d['$bic'] and cnt in d.keys():
                argb = d[cnt].decode('ascii').split('/')
                if verify(RSA_E, b64toi(argb[5].encode('ascii')), msg + today[:-10], sig):
                    status = 'Locked' if argb[0].encode('ascii') == b'!' else 'Active'
                    o = '%s %s %s' % (status, argb[1], argb[3])
        # LIST TRANSACTIONS FOR (A)DMIN
        elif reg(re.match(r'^A/1/(\d{10,16})/([^/]{150,200})$', arg)):
            today = '%s' % datetime.datetime.now()
            msg = reg.v.group(1)
            sig = bytes(reg.v.group(2), 'ascii')
            adm = d['$admin'].split(b'/')
            if verify(RSA_E, b64toi(adm[2]), msg + today[:-10], sig):
                o = ''
                for x in d.keys():
                    if reg(re.match(r'^(<|>)/\d{10,16}/[^/]{5,40}$', x.decode('ascii'))):
                        tab = x.decode('ascii').split('/')
                        trx = time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(float(tab[1])))
                        tab = d[x].decode('utf-8').split('/')
                        o += '%s %s %s\n' % (x.decode('ascii'), trx, ' '.join(tab[:2]))
            else:
                o += 'admin'
        # PUBLIC KEY (R)EGISTRATION
        elif reg(re.match(r'^R/1/(([^/]{5,30})/([^/]{8,20})/([^/]{50,200}))/([^/]{150,200})$', arg, re.U)):
            msg = reg.v.group(1)
            cnt = reg.v.group(2)
            pw = reg.v.group(3)
            pubkey = reg.v.group(4)
            sig = bytes(reg.v.group(5), 'ascii')
            if cnt.encode('ascii') in d.keys():
                if d[cnt].decode('ascii')[-2:] == '//':                
                    if verify(RSA_E, b64toi(pubkey.encode('ascii')), msg, sig):
                        d[cnt] = d[cnt][:-1] + itob64(H(pw))[:10] + b'/' + bytes(pubkey, 'ascii')
                        o = 'REGISTRATION OK'
                    else:
                        o += 'bad reg signature'
                else:
                    o += 'already registered'
            else:
                o += 'account not defined'
        else:
            o += 'cmd not found'
    else:
        log(raw, environ['REMOTE_ADDR'])
        if raw.lower() == 'update':
            o, mime = app_update(environ['SERVER_NAME']), 'text/html'
        elif raw.lower() in ('log',):
            o = open('/cup/%s/log' % __app__, 'r', encoding='utf8').read()                
        else:
            #o, mime = frontpage(), 'application/xhtml+xml; charset=utf8'
            o, mime = frontpage_html(), 'text/html; charset=utf8'
    d.close()
    start_response('200 OK', [('Content-type', mime), ('Content-Disposition', 'filename={}'.format(fname))])
    return [o if mime == 'application/pdf' else o.encode('utf8')] 

def favicon():
    "_"
    code = '<svg %s n="%s"><path stroke-width="4" fill="none" stroke="Dodgerblue" d="M3,1L3,14L13,14L13,1"/></svg>' % (_SVGNS, datetime.datetime.now())
    tmp = base64.b64encode(code.encode('utf8'))
    return '<link %s rel="shortcut icon" type="image/svg+xml" href="data:image/svg+xml;base64,%s"/>\n' % (_XHTMLNS, tmp.decode('utf8'))

def frontpage():
    "svg"
    o = '<?xml version="1.0" encoding="utf8"?>\n' 
    o += '<svg %s %s>\n' % (_SVGNS, _XLINKNS) + favicon()
    o += '<style type="text/css"></style>\n'
    o += '<text x="80" y="70" font-size="45">TEST %s %s</text>\n' % (__app__, __digest__.decode('ascii'))
    return o + '</svg>'

def frontpage_html():
    "_"
    o = '<?xml version="1.0" encoding="utf8"?>\n' 
    o += '<html>\n' + favicon()
    o += '<style type="text/css"></style>\n'
    o += '<p>Digest: %s</p>\n' % __digest__.decode('ascii')
    o += '<input class="sh" type="text" name="iban" placeholder="Votre IBAN"/>'
    o += "<p>Communiquer votre numéro IBAN ne court aucun risque. Personne ne peut retirer de l'argent sur votre compte, on peut seulement en déposer. Voir pour plus de détails les documents sur le virement SEPA, plus exactement le SEPA Credit Transfert. Toute demande de prélèvement avec votre numéro IBAN serait refusée par votre banque. <br/>Pour vous en convaincre, voici l'IBAN de notre société:  <a>FR76 1027 8022 3300 0202 8350 157</a><br/>Essayez de faire un retrait sur notre compte !</p>" 
    o += '<p>Pour optimisez les transactions, nous utilisons une forme plus compact pour déclarer un IBAN et elle est représentée par un QRcode: <br/> Voici par exemple notre IBAN: <a>frhvbqi6i/eOYqzQ</a><p>'
    #import qrc
    return o + '</html>'

# crypto primitives
from Crypto.PublicKey import RSA

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
    return int(hashlib.sha1(b''.join(bytes('%s' % i, 'ascii') for i in tab)).hexdigest(), 16)

def sign(d, n, msg):
    return itob64(pow(H(msg), d, n))

def verify(e, n, msg, s):
    return (pow(b64toi(s), e, n) == H(msg)) 

def luhn(num):
    s = 0
    for i, c in enumerate('%s' % x):
        ci = int(c)
        s += (1 + 2*(ci-5) if ci>=5 else 2*ci) if i%2 == 0 else ci
    return (s % 10 == 0)

def register():
    BPU1 = 'frnirvg3q/BB8v5O8M' 
    CRMT = 'frhvbqi6i/eOYqzQ'
    BPUB = 'frnirvg3q/BCYxhLB6'
    CRAG = 'frnsccpeq/BP2alRu5'
    POST = 'fro52evra/iMReFzM'

    d = dbm.open('/cup/ppc/keys')
    kCRAG = [b64toi(x) for x in d[CRAG].split(b'/')[2:]]
    kPOST = [b64toi(x) for x in d[POST].split(b'/')[2:]]
    kCRMT = [b64toi(x) for x in d[CRMT].split(b'/')[2:]]
    kBPU1 = [b64toi(x) for x in d[BPU1].split(b'/')[2:]]
    kBPUB = [b64toi(x) for x in d[BPUB].split(b'/')[2:]]
    d.close()

    db, now = '/cup/%s/trx.db' % __app__, '%s' % datetime.datetime.now()
    d = dbm.open(db[:-3], 'c')
    deadline = '%s' % (datetime.datetime.now() + datetime.timedelta(days=365))
    d['$bic'] = BPU1[:9]
    d['$admin'] = CRMT + '/' + itob64(kCRMT[1]).decode('ascii')

    # 1/ preparation
    # !$/Balance/Name/SID/email/Date/pw/Key
    #  0   1      2    3    4    5   6   7
    # 1 banker list   ->  !/100/toto///
    # 2 user register ->  !/100/toto//pw1/pubkey1
    # 3 banker valid  ->  */100/toto/today/pw1/pubkey1
    # 4 buy to admin  ->  */95/toto/future/pw1/pubkey1
    # 5 lock account  ->  !/95/toto/future/pw1/pubkey1
    # 6 reopen        ->  !/95/toto/future/pw2/pubkey2
    # 7 valid again   ->  */95/toto/future/pw2/pubkey2

    d[BPU1[10:]] = '!/300.00/MY SUPER HERO/fr269072927202807/toto@free.fr///' # regular user
    d[BPUB[10:]] = '$/800.00/BANKER 1/fr167071927202809/bestbank@gmail.com/%s/DTlbuslcLG/%s' % (deadline[:10], itob64(kBPUB[1]).decode('ascii')) # banker
    #print (itob64(H("hero"))[:10], itob64(H("banker"))[:10]) # 'CRGu1iGhRf' 'DTlbuslcLG'
    d.close()

if __name__ == '__main__':
    #register()

    arg = '/cup/%s/trx.db' % __app__
    if os.path.isfile(arg):
        m = re.search(r'^(.+)\.(dat|db)', arg)
        if m:
            d = dbm.open(m.group(1))
            for x in d.keys():
                print (x.decode('utf-8') ,'->', d[x].decode('utf-8'))
            d.close()

    sys.exit()

    CHAR_MAP = {"A":"10", "B":"11", "C":"12", "D":"13", "E":"14", "F":"15", "G":"16", "H":"17", "I":"18", "J":"19", 
                "K":"20", "L":"21", "M":"22", "N":"23", "O":"24", "P":"25", "Q":"26", "R":"27", "S":"28", "T":"29", 
                "U":"30", "V":"31", "W":"32", "X":"33", "Y":"34", "Z":"35"}

    t = 66000
    for i in range(t,t+10):
        a = itob32(i)
        j = b32toi(a)
        #print (i, a, j)

    
    #for x in [4059390430395175, 4417123456789113, 4971520044037525]: print (luhn(x))



# End ⊔net!
