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
Status:
'X' Iban registered 
'Y' Email registered
'Z' PubKey validated
'A' Administrator (only one)
'B' Banker (at least one per agency)
'C' Validated by banquer and payed to admin

# blocked 

# status/bic/account/name/email/date/passwd/pubkey
#   0     1     2     3    4     5     6      7
"""

_ST_   = 0
_BIC_  = 1
_ACNB_ = 2
_NAME_ = 3
_MAIL_ = 4
_DAT_  = 5
_PW_   = 6
_PK_   = 7

import re, os, sys, math, urllib.parse, hashlib, http.client, base64, dbm, binascii, datetime, zlib, functools, subprocess, time, smtplib

__digest__ = base64.urlsafe_b64encode(hashlib.sha1(open(__file__, 'r', encoding='utf8').read().encode('utf8')).digest())[:5]
__app__    = os.path.basename(__file__)[:-3]
__ppc__    = 'pingpongcash'
__email__  = 'contact@%s.net' % __ppc__
__url__    = 'http://%s.net' % __ppc__
_XHTMLNS   = 'xmlns="http://www.w3.org/1999/xhtml"'
_SVGNS     = 'xmlns="http://www.w3.org/2000/svg"'
_XLINKNS   = 'xmlns:xlink="http://www.w3.org/1999/xlink"'

RSA_E       = 65537
MAX_TR_ADAY = 200
FREE_DAYS   = 30
ID_SIZE     = 7

IBAN_FORMAT = {
    'FR': 10,
    'DE': 8,
    'BE': 3,
    'ES': 8,
    'PT': 8,
}

"""
Small is beautiful!
"""

def reg(value):
    " function attribute is a way to access matching group in one line test "
    reg.v = value
    return value

def qr_admin():
    "_"
    return 'iVBORw0KGgoAAAANSUhEUgAAAIwAAACMCAIAAAAhotZpAAACJklEQVR42u3d623DIBQG0OyRUbpW928maOTclyGcT/3pyIETyXAN9PEny+ehCyAJJEgCSSBBEkgCCZJAgiSQBBIkgSTFSM+f36a/K3fJf8n/LptvIyRIkCBBqkRKPhIDDbj4kWSX5Xu2sMcgQYIECdLHt8yPDgKNbOrxwIgmMDyBBAkSJEiQIBUhJV1r2wIJEiRIkCB9VkWeKYVAggQJEqQNkGb64mK1u2/g4FUFJEiQIC2KNLNaqG/+a0kXJEiQIEGC1Iw0k0CVYWZAOB9IkCBBglQ5fy6sKAfAZgZB25eFIEGCBGl3pMDa0tq9lQH+wuFJX+EcEiRIkCDdXGAt7MraHk9eBgkSJEiQIB2MVFhlyP8sAh8PlELmqyeQIEGCBKlMJX+ET7Jh9x7Kd//WF0iQIEE6BKlvUc46k9m+lwCQIEGCBGmhyezMnLFvajm/ABYSJEiQIEE6ACmAlzyVPXCXwnHjV23HhAQJEqRdkAqn3H3vTGe2vkCCBAkSpONOROnbLVO4tfSrJrOQIEGCtAvSskepFc6s+/5LMSRIkCBBgnQwUu0QrqnyXbsAeH5rJiRIkCBBqvyWM7seay+bP+IAEiRIkCAtitQ3opl58i/0+hwSJEiQIBUibfF4P3EyCwkSJEiQIK1YBU/+YmZGepAgQYIE6Wak+aPk8pP85A7OZLdAggQJEqRKJBkOJEgCCZJAEkiQBJJAgiSQIAkkgQRJIMm7vAC6a+kW1XzFvQAAAABJRU5ErkJg'

def log(s, ip=''):
    "Append to head log file"
    logf, now = '/cup/%s/log' % __app__, '%s' % datetime.datetime.now()
    if not os.path.isfile(logf): open(logf, 'w', encoding='utf8').write('%s|%s Logfile Creation\n' % (now[:-7], ip) )     
    cont = open(logf, 'r', encoding='utf8').read()
    open(logf, 'w', encoding='utf8').write('%s|%s|%s\n%s' % (now[:-7], ip, s, cont))

def app_update(host):
    "_"
    cd = 'cd %s; git pull origin' % os.path.dirname(os.path.abspath(__file__))
    out, err = subprocess.Popen((cd), shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
    o = '<html><pre>Application Update...\n'
    o += 'Error: %s\n' % err.decode('utf8') if err else 'Message:%s\n' % out.decode('utf8')
    o += '</pre><br/><a href="%s">Reload the new version</a></html>' % __app__
    return o

def get_image(img):
    "_"
    here = os.path.dirname(os.path.abspath(__file__))
    return 'data:image/png;base64,%s' % base64.b64encode(open('%s/%s' % (here, img), 'rb').read()).decode('ascii')

def help_register():
    "_"
    o = "<p>Le mot de passe choisi ne permet que d'accéder au statut de votre compte et éventuellement de bloquer l'autorisation de dépenser de l'argent si vous perdez votre <i>iPhone</i>, mais en aucun cas de faire des achâts. Pour donner de l'argent à autre personne, il vous faut obligatoirement utiliser le code <b>alpha-pin</b> de votre <i>iPhone</i>, après création d'un jeux de clés cryptographiques, uniquement sur téléphone, déconnecté de l'Internet et enfin après acquisition du certificat de votre banquier qui confirmera le lien avec votre compte bancaire. Personne (ni l'opérateur téléphonique, ni le banquier, ni nos administrateurs informatique, ni l'Etat et aucun hacker) à part vous ne connaît ou ne doit connaître votre code <b>alpha-pin</b>, et si vous le perdez ou vi vous changez de téléphone, vous devrez simplement re-suivre la procédure d'enregistrement. Vous récupérez bien entendu le délai de cotisation de votre ancien compte.</p>"
    o += "<p>Vous pouvez vous enregistrer même si vous ne possédez pas d'<i>iPhone</i>. Vous ne pourrez que recevoir de l'argent et pas en donner.</p>"
    o += "<p>Le fait de nous communiquer votre IBAN+BIC ne permet à personne, nous compris, de retirer de l'argent sur votre compte. Il faudrait pour cela votre signature numérique réalisée uniquement par votre <i>iPhone</i> et avec la connaissance de votre code <b>alpha-pin</b>. Votre banquier doit respecter les directives du virement SEPA et toute transaction n'est utilisable qu'une seule fois. Afin de mieux encore garantir votre confidentialité, aucun de vos correspondants autre que les banquiers et nous, n'aura accès à votre IBAN, BIC, ni à votre e-mail. Vous utilisez et diffusez un <i>code marchand</i> représenté par un QRcode reçu par e-mail si l'enregistrement est validé. En revanche, ce <i>code marchand</i> permet à la personne qui le possède de vous verser de l'argent et vous en êtes notifiés. Nous référençons ce jour 21065 agences bancaires en France et si par malchance votre agence n'est pas trouvée par votre IBAN, un email vous invitera à nous donner l'adresse exacte de votre agence.</p>"
    o += "<p>Le numéro de sécurité sociale est optionel. Il vous permet de demander la validation (un certificat) de votre identité numérique à une administration locale, et ainsi guarantir l'unicité de cette identité. Ce qui sera requis pour de futures opérations citoyenne comme le vote par Internet. Cette fonction est indépendante du moyen de paiement numérique mais ellesuit le même principe de sécurité, en particulier une authentification forte par votre <i>iPhone</i> et la connaissance du code 'alpha-pin' associé.</p>"
    o += "<p>Le nom et le(s) prénom(s) doivent correspondre strictement à ceux déclarés auprès de votre banquier lors de l'ouverture du compte identifié par l'IBAN, sinon le conseiller financier ne vous validera pas votre identité et vous ne pourrez pas payer, seulement recevoir de l'argent. De même, pour utiliser votre <i>iPhone</i> lors de démarches citoyennes, il faudra que les noms et prénoms soient ceux de vos papiers d'identité officiels pour avoir une validation de l'administration.</p>"
    o += "<p>Le code BIC n'est pas utile dans le mesure où il est retrouvé à partir de l'IBAN, mais nous nous en servons seulement pour vérification. Toute demande d'enregistrement avec un IBAN+BIC incohérents est refusée. Nous référençons 538 codes BIC pour la France, et si selon une très faible probabilité, votre BIC est inconnu à l'enregistrement, merci de nous le communiquer afin que nous puissions vérifier et corriger.<p>"
    o += '<p>Pour vérifier que vous utiliser la dernière version du site, vous pouvez comparer le code du condensé : <b>%s</b> avec celui affiché sur <a href="">github</a>. Cette page ne contient aucun code <i>JavaScript</i>, ni <i>cookies</i>.</p>\n' % __digest__.decode('ascii')
    return o


def front_html(login='', tab = []):
    "_"
    o = '<?xml version="1.0" encoding="utf8"?>\n' 
    o += '<html>\n' + favicon()
    o += '<style type="text/css">h1,h6,p,i,li,a {font-family:"Lucida Grande", "Lucida Sans Unicode", Helvetica, Arial, Verdana, sans-serif;}input{font-size:18;margin:3}input.txt{width:330}input[type=submit]{color:white;background-color:#AAA;border:none;border-radius:8px;padding:3}p,li{font-size:10;color:#333;}div{position:absolute;top:150;left:350;margin:20}h6{text-align:right;color:#AAA;}</style>\n'
    if tab:
        o += '<h6>Bonjour %s %s !</h6>' % (tab[2], tab[3])
    
    o += '<img title="Enfin un moyen de paiement numérique, simple, gratuit et sécurisé !" src="%s"/>\n' % get_image('www/header.png')
    o += '<img title="...notre QRcode \'%s\'" src="data:image/png;base64,%s"/>\n' % (hiban('frhvbqi6i/eOYqzQ'), qr_admin())    

    if login == '':
        o += '<form method="post">\n'
        o += '<input class="txt" type="text" name="mail" placeholder="E-mail" required="yes"/><br/>'
        o += '<input class="txt" type="password" name="pw" placeholder="Mot de passe"/><br/>'
        o += '<input class="sh" type="submit" value="Se connecter"/> '
        o += '<input class="sh" type="submit" name="lost" value="Mot de passe oublié"/>\n'
        o += '</form>\n'
 
        o += '<form method="post">\n'
        o += '<input class="txt" type="text" name="first" placeholder="Prénom(s)" title="liste complète" required="yes"/><br/>'
        o += '<input class="txt" type="text" name="last" placeholder="Nom de famille" required="yes"/><br/>'
        o += '<input class="txt" type="text" name="mail" placeholder="E-mail" title="n\'est pas communiqué" required="yes"/><br/>'
        o += '<input class="txt" type="text" name="iban" placeholder="IBAN" required="yes"/><br/>'
        o += '<input class="txt" type="text" name="bic" placeholder="Code BIC" pattern="[A-Z0-9]{8,11}" title="pour vérification" required="yes"/><br/>'
        o += '<input class="txt" type="text" name="ssid" placeholder="[Optionel] Numéro de sécurité sociale"/><br/>'
        o += '<input class="txt" type="text" name="name" placeholder="[Optionel] Nom affiché de marchand"/><br/>'
        o += '<input class="txt" type="password" name="pw" placeholder="Mot de passe" title="de plus de 4 caractères" required="yes"/><br/>'
        o += '<input class="txt" type="password" name="pw2" placeholder="Confirmation de mot de passe" required="yes"/><br/>'
        o += '<input class="txt" type="checkbox" name="read" title="j\'ai lu les avertissements ci contre" required="yes"/>'
        o += '<input class="sh" type="submit" value="S\'enregistrer"/>\n'
        o += '</form>\n'

        o += '<div>'
        o += help_register()

    else:
        o += '<p>Identifiant: %s</p>' % login
        o += '<p>Status: %s</p>' % 'Récection: Valide | Achât: en attente de validation par le banquier'
        o += '<p>Seuils d\'achâts : %d€/jour maximum %d€</p>' % (100, 3000) 
        today = '%s' % datetime.datetime.now()
        o += '<p>Montant autorisé le %s : %d€</p>' % (today[:10],0) 
        o += '<p>Code marchand: <b>%s</b></p>' % tab[0]
        #o += '<p>Nom affiché de marchand: <b>%s</b></p>' % tab1[1]
        o += '<p>Date d\'enregistrement: %s</p>' % time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(float(tab[1])))
              
        o += '<form method="post">\n'
        o += '<input class="txt" type="password" name="pw" placeholder="Nouveau mot de passe" required="yes"/><br/>'
        o += '<input class="txt" type="password" name="pw2" placeholder="Confirmation de mot de passe" required="yes"/><br/>'
        o += '<input class="sh" type="submit" name="new" value="Changer votre mot de passe"/> '
        o += '</form>\n'
        
        o += '<form method="post">\n'
        o += '<input class="txt" type="password" name="pw" placeholder="Mot de passe" required="yes"/><br/>'
        o += '<input class="sh" type="submit" name="lock" value="Bloquer tout achât" %s/>\n' % 'disabled="yes"'
        o += '</form>\n'

        o += '<div>'
        o += "<p>Attention: le bloquage du compte doit être utilisé si vous perdez ou vous faites voler votre <i>iPhone</i> et il n'a de sens que si vous avez autorisation d'achât délivrée par votre banquier.</p>"
        o += "<p>Nous n'avons pas accès au solde de votre compte. La limite des montants d'achât est encadrée par les deux valeurs de seuils fournies par votre banquier. Vous pouvez le contacter votre négocier des valeur différentes.</p>"
    o += '<h6>Contact: <a href="mailto:contact@pingpongcash.net">contact@pingpongcash.net</a><br/><a href="http://cupfoundation.net">⊔FOUNDATION</a> is registered in Toulouse/France SIREN: 399 661 602 00025<br/></h6>'
    o += '</div>'
    return o + '</html>'

def compact (iban):
    "_"
    CHAR_MAP = {
        "A":"10", "B":"11", "C":"12", "D":"13", "E":"14", "F":"15", "G":"16", "H":"17", "I":"18", "J":"19", "K":"20", "L":"21", "M":"22", 
        "N":"23", "O":"24", "P":"25", "Q":"26", "R":"27", "S":"28", "T":"29", "U":"30", "V":"31", "W":"32", "X":"33", "Y":"34", "Z":"35"
        }
    iban = iban.upper()
    bank = re.sub(' ', '', iban[4:])
    ll = bank + iban[:4]
    for x in CHAR_MAP: ll = re.sub(x, CHAR_MAP[x], ll)
    if iban[:2] not in IBAN_FORMAT: return 'Error: country not supported!'
    if int(ll) % 97 != 1: return 'Error: non valid IBAN!'
    limit = IBAN_FORMAT[iban[:2]]
    bic, cnt = bank[:limit], bank[limit:]
    for x in CHAR_MAP: cnt = re.sub(x, CHAR_MAP[x], cnt)
    ibic, icnt = itob32(int(re.sub(' ', '', bic))), itob64(int(re.sub(' ', '', cnt)))
    return 'fr%s/%s' % (ibic.decode('ascii'), icnt.decode('ascii'))

def hiban (code):
    "_"
    return base64.urlsafe_b64encode(hashlib.sha1(code.encode('ascii')).digest())[:ID_SIZE].decode('ascii')

def h6 (code):
    "_"
    return base64.urlsafe_b64encode(hashlib.sha1(code.encode('ascii')).digest())[:6].decode('ascii')

def h10 (code):
    "_"
    return base64.urlsafe_b64encode(hashlib.sha1(code.encode('utf8')).digest())[:10].decode('ascii')

def gbic (code):
    "_"
    return code.split('/')[0]

def init_db(db):
    "_"
    di = '/cup/%s' % __app__
    if not os.path.exists(di): os.makedirs(di)
    if not os.path.isfile(db):
        d = dbm.open(db[:-3], 'c')
        d['He8Tx-d'] = 'A/frhvbqi6i/eOYqzQ/Laurent Fournier/pelinquin@gmail.com//nopw/uGhhu3XsnKNDfCOW0cISKmsx_ML_jN5bA7A5ViSm7AhMm-Upu-S24UfH8hznnWpDKuEswnZsI96_TfBVQDkkn4DlhhnUR1fPm2pYs5if5Q51RWua5k8M7sPnWzsrbF3NPkcc_-XtHo6YhRlGrvFj1I9ogYO3Ha0ooVjNQN-Ca3c' 
        d.close()
        os.chmod(db, 511)

def init_dbs(dbs):
    "_"
    di = '/cup/%s' % __app__
    if not os.path.exists(di): os.makedirs(di)
    for dbn in dbs:
        db = '/cup/%s/%s.db' % (__app__, dbn)
        if not os.path.isfile(db):
            d = dbm.open(db[:-3], 'c')
            d.close()
            os.chmod(db, 511)

def same_bic(d, biban, siban):
    "_"
    bs = d[biban].decode('utf8').split('/')
    ps = d[siban].decode('utf8').split('/')
    return bs[1] == ps[1]

def register_pk(d, msg, iban, pw, pk, sig):
    "_"
    o, pb = '', d[iban].decode('utf8').split('/')
    if verify(RSA_E, b64toi(pk.encode('ascii')), msg, sig):
        if pb[_ST_] == 'X':
            pb[_PW_], pb[_PK_], pb[_ST_] = pw, pk, 'Y' 
            d[iban] = '/'.join(pb)
            o = 'Register public key OK'
        else:
            o += 'email not validated'
    else:
        o = 'Error:Bad signature'
    return o

def daylist(d, msg, day, iban, sig):
    "_"
    o, pb = '', d[iban].decode('utf8').split('/')
    if verify(RSA_E, b64toi(pb[_PK_].encode('ascii')), msg, sig):
        bic = pb[_BIC_]
        for x in d[bic].decode('ascii').split('/'):
            ee = hiban('%s/%s' % (bic, x))
            cc = '%s/%s' % (day, ee)
            if cc.encode('ascii') in d.keys():
                for t in d[cc].decode('ascii').split('/'):
                    o += '%s/%s\n' % (t, d['%s/%s' % (t, ee)].decode('ascii'))
        #smail (pb[_MAIL_], 'THIS IS A LIST \n %s' % o)
        #smail (pb[_MAIL_], 'THIS IS A \nSIMPLE MAIL TEST \n')
        #o = 'mail send! to %s' % pb[_MAIL_]
    else:
        o = 'Error:Bad signature'
    return o

def smail(dest, content):
    s = smtplib.SMTP('cup')
    print (dest)
    #s.sendmail ('contact@pingpongcash.net', [dest], content)
    s.sendmail (b'contact@pingpongcash.net', [dest], content)
    s.quit()

def transaction (d, msg, epoch, s_biban, s_siban, val, s_sig):
    "_"
    o, biban, siban, sig = 'Error:', bytes(s_biban, 'ascii'), bytes(s_siban, 'ascii'), bytes(s_sig,'ascii')
    if biban in d.keys():
        pb = d[biban].decode('utf8').split('/')
        if '%s/%s' % (epoch, s_biban) in d.keys():
            o += 'already send'
        elif verify(RSA_E, b64toi(pb[_PK_].encode('ascii')), msg, sig):
            if siban in d.keys():
                ps = d[siban].decode('utf8').split('/')
                if pb[_ST_] == 'Y' and ps[_ST_] in ['A', 'B'] and val == 0: # Y show how to sign to Admin or to Banquer
                    pb[_ST_] = 'Z'
                    d[biban] = '/'.join(pb)
                    o = 'Y->Z'
                elif pb[_ST_] == 'A' and ps[_ST_] in ['Z', 'B'] and val == 0: # Admin valid to Banker for one year
                    ps[_ST_], ps[_DAT_] = 'B', ('%s' % (datetime.datetime.now() + datetime.timedelta(days=365)))[:10]
                    d[siban] = '/'.join(ps)
                    o = 'Y->B'
                elif pb[_ST_] == 'B' and ps[_ST_] == 'Z' and val == 0: # Bank valid to custumer for one month (from the same agency)
                    if (datetime.datetime.strptime(pb[_DAT_], '%Y-%m-%d').date() > datetime.datetime.now().date()):
                        if same_bic(d, biban, siban):
                            ps[_ST_], ps[_DAT_] = 'C', ('%s' % (datetime.datetime.now() + datetime.timedelta(days=FREE_DAYS)))[:10]
                            d[siban] = '/'.join(ps)
                            o = 'Z->C'
                        else:
                            o += 'not the same agency'
                    else:
                        o += 'Bank valid date expire'
                elif pb[_ST_] == 'C' and ps[_ST_] in ['X', 'Y', 'Z', 'A', 'C', 'B'] and val > 0: # Normal sold
                    if ps[_ST_] == 'A': # pay date
                        pb[_DAT_] = ('%s' % (datetime.datetime.strptime(pb[_DAT_], '%Y-%m-%d').date() + datetime.timedelta(days=int(val*100))))[:10]
                        d[biban] = '/'.join(pb)
                    if (datetime.datetime.strptime(pb[_DAT_], '%Y-%m-%d').date() > datetime.datetime.now().date()):
                        today = '%s' % datetime.datetime.now()
                        k, l = '%s/%s' % (today[:10], s_biban), 0
                        if k.encode('ascii') in d.keys(): l = len(d[k].decode('ascii').split('/')) # verifier
                        if l < MAX_TR_ADAY:
                            d[k] = d[k] + bytes('/%s' % epoch, 'ascii') if k.encode('ascii') in d.keys() else epoch
                            d['%s/%s' % (epoch, s_biban)] = '/'.join([s_siban, '%06.2f'%val, s_sig])
                            o = 'transaction OK, %s' % l
                        else:
                            o += 'too many transactions a day'
                    else:
                        o += 'validation date passed'
                else:
                    o += 'NOT ALLOWED %s %s' % (pb[_ST_], ps[_ST_]) 
            else:
                o += 'SELLER NOT REGISTERED'
        else:
            o += 'BAD SIGNATURE'
    else:
        o += 'BUYER NOT KNOWN'
    return o

_PAT_LOGIN_ = r'mail=([^&/]{2,40}@[^&/]{2,30}\.[^&/]{2,10})&pw=(\w{4,30})$'
_PAT_LOST_  = r'mail=([^&/]{2,40}@[^&/]{2,30}\.[^&/]{2,10})&pw=&lost=Mot de passe oublié$'
_PAT_REGISTER_ = r'first=([^&/]{3,80})&last=([^&/]{3,80})&mail=([^&/]{2,40}@[^&/]{3,40})&iban=([a-zA-Z\d ]{16,38})&bic=([A-Z\d]{8,11})&ssid=([^&/]*)&name=([^&/]{1,100})&pw=([^&]{2,20})&pw2=([^&]{2,20})&read=on$'

def application(environ, start_response):
    "wsgi server app"
    mime, o, db, now, fname = 'text/plain; charset=utf8', 'Error:', '/cup/%s/trx.db' % __app__, '%s' % datetime.datetime.now(), 'default.txt'
    init_db(db)
    dbs = ('ags', 'bic', 'usr')
    init_dbs(dbs)
    (raw, way) = (environ['wsgi.input'].read(), 'post') if environ['REQUEST_METHOD'].lower() == 'post' else (urllib.parse.unquote(environ['QUERY_STRING']), 'get')
    base = environ['PATH_INFO'][1:]
    d = dbm.open(db[:-3], 'c')
    if way == 'post':
        arg = urllib.parse.unquote_plus(raw.decode('utf8'))
        if reg(re.match(_PAT_LOGIN_, arg)):
            #smail ('pelinquin@gmail.com', 'LOGIN OK \n')
            mail = reg.v.group(1)
            dusr = dbm.open('/cup/pp/usr', 'c')
            if mail.encode('ascii') in dusr.keys():
                tab = dusr[mail].decode('utf8').split('/')
                if h10(reg.v.group(2)).encode('utf8').decode('ascii') == tab[5]:
                    o, mime = front_html(mail, tab), 'text/html; charset=utf8'
                else:
                    o += 'bad password'
            dusr.close()
            #o = 'enter OK! %s' % reg.v.group(1)
        elif reg(re.match(_PAT_LOST_, arg)):
            o = 'pw resent!'
        elif reg(re.match(_PAT_REGISTER_, arg)):
            dusr = dbm.open('/cup/pp/usr', 'c')
            mail = reg.v.group(3)
            if reg.v.group(8) == reg.v.group(9):
                if mail.encode('ascii') in dusr.keys():
                    o += 'already registered'
                else:
                    while True:
                        epoch = '%s' % time.mktime(time.gmtime())
                        cid = compact(reg.v.group(4))
                        k = h6(cid + '/' + epoch[:-2])
                        if k not in dusr.keys(): break
                    dusr[cid] = dusr[cid] + bytes('/%s' % k, 'ascii') if cid.encode('ascii') in dusr.keys() else k
                    dusr[mail] = '/'.join([k, epoch[:-2], reg.v.group(1).title(), reg.v.group(2).title(), reg.v.group(6), h10(reg.v.group(8))])
                    dusr[k] = '/'.join([mail, reg.v.group(7), compact(reg.v.group(4)), reg.v.group(5)])
                    o = 'register OK'
            else:
                o += 'not the same password!'                
            dusr.close()
            # check valid IBAN, IBAN == BIC, valid email, valid ssid, pw=pw2
        elif reg(re.match(r'^name=([^&/]{3,80})&mail=([^&/]{2,40}@[^&/]{3,40})&iban=([a-zA-Z\d ]{16,38})$', arg)):
            cc = compact(reg.v.group(3))
            bic, anb = cc.split('/') # verifier
            d[bic] = d[bic] + anb if bic in d.keys() else anb # verifier 
            d[hiban(cc)] = 'X/%s/%s/%s///' % (cc, reg.v.group(1), reg.v.group(2))
            o = 'web register OK %s' % cc
            #smail ('pelinquin@gmail.com', 'THIS IS A \nSIMPLE MAIL TEST \n')
        elif reg(re.match(r'^name=([^&/]{3,80})&mail=([^&/]{2,40}@[^&/]{3,40})&iban=([a-zA-Z\d ]{16,38})&pw=(.{2,20})$', arg)):
            x = hiban(compact(reg.v.group(3)))
            if x.encode('ascii') in d.keys(): 
                px = d[x].decode('utf8').split('/')
                if px[_NAME_] == reg.v.group(1) and px[_MAIL_] == reg.v.group(2):
                    o = 'BLOCAGE email or not found'
                else:
                    o = 'BLOCAGE account found'
            else:
                o = 'BLOCAGE account not found'
        elif reg(re.match(r'^R1/(([^/]{3,20})/([^/]{6,15})/([^/]{60,500}))/([^/]{150,200})$', arg)):
            o = register_pk(d, reg.v.group(1), reg.v.group(2), reg.v.group(3), reg.v.group(4), bytes(reg.v.group(5),'ascii'))
        elif reg(re.match(r'^T1/((\d{10,16})/([^/]{3,20})/([^/]{3,20})/(\d{3}\.\d{2}))/([^/]{150,200})$', arg)):
            o = transaction(d, reg.v.group(1), reg.v.group(2), reg.v.group(3), reg.v.group(4), float(reg.v.group(5)), reg.v.group(6))
        elif reg(re.match(r'^D1/(([^/]{10})/([^/]{3,20}))/([^/]{150,200})$', arg)):
            o = daylist(d, reg.v.group(1), reg.v.group(2), reg.v.group(3), bytes(reg.v.group(4),'ascii'))
        else:
            o += 'not valid args %s' % arg
    else:
        if raw.lower() == '_update':
            o, mime = app_update(environ['SERVER_NAME']), 'text/html'
        elif base == '':
            o, mime = front_html(), 'text/html; charset=utf8'
        else:
            dusr = dbm.open('/cup/pp/usr', 'c')
            if base.encode('ascii') in dusr.keys():
                tab = dusr[base].decode('utf8').split('/')
                o = 'code %s \nThis IBAN is well registered.\n Using it will pay to "%s"' % (base, tab[1])
            else:
                o += 'IBAN NOT registered'                
            dusr.close()
    d.close()
    start_response('200 OK', [('Content-type', mime), ('Content-Disposition', 'filename={}'.format(fname))])
    return [o if mime == 'application/pdf' else o.encode('utf8')] 

def favicon():
    "_"
    code = '<svg %s n="%s"><path stroke-width="4" fill="none" stroke="Dodgerblue" d="M3,1L3,14L13,14L13,1"/></svg>' % (_SVGNS, datetime.datetime.now())
    tmp = base64.b64encode(code.encode('utf8'))
    return '<link %s rel="shortcut icon" type="image/svg+xml" href="data:image/svg+xml;base64,%s"/>\n' % (_XHTMLNS, tmp.decode('utf8'))

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

def sign(d, n, msg):
    return itob64(pow(H(msg), d, n))

def verify(e, n, msg, s):
    return (pow(b64toi(s), e, n) == H(msg)) 

def luhn(num):
    "_"
    s = 0
    for i, c in enumerate('%s' % x):
        ci = int(c)
        s += (1 + 2*(ci-5) if ci>=5 else 2*ci) if i%2 == 0 else ci
    return (s % 10 == 0)

def cmd(post, cd, host='localhost'):
    "_"
    co, serv = http.client.HTTPConnection(host), '/'    
    if post:
        co.request('POST', serv, urllib.parse.quote(cd))
    else:
        co.request('GET', serv + '?' + urllib.parse.quote(cd))
    return co.getresponse().read().decode('utf8')    

def test():
    "_"
    lb = {
        'BPU1': 'FR76 1780 7000 1445 3199 4029 836',
        'BPUB': 'fr76 1780 7000 1445 6208 6047 866',        
        'CRAG': 'FR7618206002105487266700217',
        'POST': 'FR19 2004 1100 2000 5874 1005 T15',
        'CRMT': 'FR76 1027 8022 3300 0202 8350 157',
        'BELG': 'BEkkBBBCCCCCCCKK',
        'ALLM': 'DEkk BBBB BBBB CCCC CCCC CC',
        'MALT': 'MTkk BBBB SSSS SCCC CCCC CCCC CCCC CCC',
        }
    CRAG = compact(lb['CRAG'])
    POST = compact(lb['POST'])
    BPU1 = compact(lb['BPU1'])
    BPUB = compact(lb['BPUB'])
    CRMT = compact(lb['CRMT'])
    d = dbm.open('/cup/ppc/keys')
    kCRAG = [b64toi(x) for x in d[CRAG].split(b'/')[2:]]
    kPOST = [b64toi(x) for x in d[POST].split(b'/')[2:]]
    kBPU1 = [b64toi(x) for x in d[BPU1].split(b'/')[2:]]
    kBPUB = [b64toi(x) for x in d[BPUB].split(b'/')[2:]]
    kCRMT = [b64toi(x) for x in d[CRMT].split(b'/')[2:]]
    d.close()

    # 1/ register accounts on web site
    msg = 'name=%s&mail=%s&iban=%s' % ('banker', 'contact@pingpongcash.net', lb['BPUB'])
    print ('WEB REGISTER', cmd(True, msg))
    msg = 'name=%s&mail=%s&iban=%s' % ('valérie', 'ttoto@gmail.com', lb['POST'])
    print ('WEB REGISTER', cmd(True, msg))
    msg = 'name=%s&mail=%s&iban=%s' % ('tata', 'tata@gmail.com', lb['CRAG'])
    print ('WEB REGISTER', cmd(True, msg))
    msg = 'name=%s&mail=%s&iban=%s' % ('main', 'user@gmail.com', lb['BPU1'])
    print ('WEB REGISTER', cmd(True, msg))

    epoch, today = '%s' % time.mktime(time.gmtime()), '%s' % datetime.datetime.now()

    # 2/Register PubKey
    msg = '/'.join([hiban(BPUB), itob64(H('héro'))[:10].decode('utf8'), itob64(kBPUB[1]).decode('ascii')])    
    print ('REG_PK:', cmd(True, '/'.join(['R1', msg, sign(kBPUB[0], kBPUB[1], msg).decode('ascii')])))
    msg = '/'.join([hiban(BPU1), itob64(H('zéro'))[:10].decode('utf8'), itob64(kBPU1[1]).decode('ascii')])    
    print ('REG_PK:', cmd(True, '/'.join(['R1', msg, sign(kBPU1[0], kBPU1[1], msg).decode('ascii')])))
    msg = '/'.join([hiban(POST), itob64(H('toto'))[:10].decode('utf8'), itob64(kPOST[1]).decode('ascii')])    
    print ('REG_PK:', cmd(True, '/'.join(['R1', msg, sign(kPOST[0], kPOST[1], msg).decode('ascii')])))
    #msg = '/'.join([hiban(CRMT), itob64(H('&éçà'))[:10].decode('utf8'), itob64(kCRMT[1]).decode('ascii')])    
    #print ('REG_PK:', cmd(True, '/'.join(['R1', msg, sign(kCRMT[0], kCRMT[1], msg).decode('ascii')])))

    # 2/ valid banker
    msg = '/'.join([epoch[:-2], hiban(BPUB), hiban(CRMT), '000.00'])    
    s = sign(kBPUB[0], kBPUB[1], msg)
    print ('BANKER SHOW HOW TO SIGN TO ADMIN:', cmd(True, '/'.join(['T1', msg, s.decode('ascii')])))

    msg = '/'.join([epoch[:-2], hiban(CRMT), hiban(BPUB), '000.00'])    
    s = sign(kCRMT[0], kCRMT[1], msg)
    print ('ADMIN VALID BANKER:', cmd(True, '/'.join(['T1', msg, s.decode('ascii')])))

    msg = '/'.join([epoch[:-2], hiban(POST), hiban(BPUB), '000.00'])    
    s = sign(kPOST[0], kPOST[1], msg)
    print ('X SHOW HOW TO SIGN TO BANKER:', cmd(True, '/'.join(['T1', msg, s.decode('ascii')])))

    msg = '/'.join([epoch[:-2], hiban(BPU1), hiban(BPUB), '000.00'])    
    s = sign(kBPU1[0], kBPU1[1], msg)
    print ('X SHOW HOW TO SIGN TO BANKER:', cmd(True, '/'.join(['T1', msg, s.decode('ascii')])))

    msg = '/'.join([epoch[:-2], hiban(BPUB), hiban(BPU1), '000.00'])    
    s = sign(kBPUB[0], kBPUB[1], msg)
    print ('BANKER VALIDATE:', cmd(True, '/'.join(['T1', msg, s.decode('ascii')])))

    msg = '/'.join([epoch[:-2], hiban(BPU1), hiban(CRMT), '001.00'])    
    s = sign(kBPU1[0], kBPU1[1], msg)
    print ('CUSTOMER BUY DATE:', cmd(True, '/'.join(['T1', msg, s.decode('ascii')])))

    msg = '/'.join([epoch[:-2], hiban(BPU1), hiban(CRAG), '010.00'])    
    s = sign(kBPU1[0], kBPU1[1], msg)
    print ('NORMAL BUY:', cmd(True, '/'.join(['T1', msg, s.decode('ascii')])))

    msg = '/'.join([epoch[:-2], hiban(BPU1), hiban(POST), '005.00'])    
    s = sign(kBPU1[0], kBPU1[1], msg)
    print ('NORMAL BUY:', cmd(True, '/'.join(['T1', msg, s.decode('ascii')])))

    msg = '/'.join([today[:10], hiban(BPUB)])    
    s = sign(kBPUB[0], kBPUB[1], msg)
    #print ('GET LIST:\n', cmd(True, '/'.join(['D1', msg, s.decode('ascii')])))


def print_db():
    arg, o = '/cup/%s/trx.db' % __app__, ''
    if os.path.isfile(arg):
        m = re.search(r'^(.+)\.(dat|db)', arg)
        if m:
            d = dbm.open(m.group(1))
            nt = 0
            for x in d.keys():
                tv, tk = d[x].decode('utf8').split('/'), x.decode('utf8').split('/')
                if reg(re.match(r'^\d{10,16}/[^/]{%s}$' % ID_SIZE, x.decode('ascii'))):
                    nt += 1
                    trx = time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(float(tk[0])))
                    o += '>%s %s %s %s\n' % (trx, tk[1], tv[0], tv[1])
                elif reg(re.match(r'^.{%s}$' % ID_SIZE, x.decode('ascii'))):
                    o += 'USER %s -> %s "%s" %s %s\n'  % (x.decode('utf8') , tv[0], tv[3], tv[4], tv[5])
                elif reg(re.match(r'^[\d\-]{10}/.{%s}$' % ID_SIZE, x.decode('ascii'))):
                    o += 'NB_TR %s -> %s\n'  % (x.decode('utf8') , len(tv))
                elif reg(re.match(r'^\w{5,10}$', x.decode('ascii'))):
                    o += 'AGENCY %s -> %s\n'  % (x.decode('utf8') , len(tv))
                else:
                    o += '%s -> %s\n'  % (x.decode('utf8') , d[x].decode('utf8'))
            o += 'NB_TRANSACTIONS: %s\n' % nt 
            d.close()
    return o
#################### QR CODE ################


############################################

if __name__ == '__main__':
    #test()
    #print (print_db())
    test2()
    sys.exit()
# End ⊔net!
