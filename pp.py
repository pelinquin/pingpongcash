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

codeM -> mail/status/lock/regDate/FirstName/LastName/DisplayName/Secu/numbank/iban/bic/Threhold1/Threhold2/balance/expiredate/pw/pubk1/pubk2
          0     1      2     3       4         5           6      7      8     9    10    11        12       13       14      15   16   17
"""

_MAIL = 0
_STAT = 1
_LOCK = 2
_DREG = 3
_FRST = 4
_LAST = 5
_PUBN = 6
_SECU = 7
_NBNK = 8
_IBAN = 9
_CBIC = 10
_THR1 = 11
_THR2 = 12
_BALA = 13
_DEXP = 14
_PAWD = 15
_PBK1 = 16
_PBK2 = 17

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

__embedded_fonts__ = ('cmr10', 'cmr17')
__fonts__ = ('Helvetica', 'Times-Roman', 'Courier', 'Times-Bold', 'Helvetica-Bold', 'Courier-Bold', 'Times-Italic', 'Helvetica-Oblique', 
             'Courier-Oblique', 'Times-BoldItalic', 'Helvetica-BoldOblique', 'Courier-BoldOblique', 'Symbol') + __embedded_fonts__

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

def help_private(cm):
    "_"
    o = "<p>Cette page est votre page privée. Elle contient des informations qui ne sont pas divulguées aux personnes ou commerçants avec qui vous faites des transactions financières <a class=\"ppc\">Ping-Pong&nbsp;</a>.</p>"
    o += "<p>Votre page puplique est <a href=\"./%s\">ici</a>. Elle est accessible directement depuis le code marchand en QRcode. Diffusez cette page publique ou ce QRcode à toute personne susceptible de vous verser de l'argent.</p>" % cm
    o += '<p></p>'
    o += "<p>Attention: le bloquage du compte doit être utilisé si vous perdez ou vous faites voler votre <i>iPhone</i> et il n'a de sens que si vous avez autorisation d'achât délivrée par votre banquier.</p>"
    o += "<p>Nous n'avons pas accès au solde de votre compte. La limite des montants d'achât est encadrée par les deux valeurs de seuils fournies par votre banquier. Vous pouvez le contacter votre négocier des valeur différentes.</p>"
    return o

def help_register():
    "_"
    o = "<p>Le mot de passe choisi ne permet que d'accéder au statut de votre compte et éventuellement de bloquer l'autorisation de dépenser de l'argent si vous perdez votre <i>iPhone</i>, mais en aucun cas ce mot de passe permet de faire des achâts. Pour donner de l'argent à autre personne, il vous faut obligatoirement utiliser le code <b>alpha-pin</b> de votre <i>iPhone</i>, après création d'un jeux de clés cryptographiques, uniquement sur téléphone, déconnecté de l'Internet et enfin après acquisition du certificat de votre banquier qui confirmera le lien avec votre compte bancaire. Personne (ni l'opérateur téléphonique, ni le banquier, ni nos administrateurs informatique, ni l'Etat et aucun hacker) à part vous ne connaît ou ne doit connaître votre code <b>alpha-pin</b>, et si vous le perdez ou vi vous changez de téléphone, vous devrez simplement re-suivre la procédure d'enregistrement. Vous récupérez bien entendu le délai de cotisation de votre ancien compte.</p>"
    o += "<p>Vous pouvez vous enregistrer même si vous ne possédez pas d'<i>iPhone</i>. Vous ne pourrez que recevoir de l'argent et pas en donner.</p>"
    o += "<p>Le fait de nous communiquer votre IBAN+BIC ne permet à personne, nous compris, de retirer de l'argent sur votre compte. Il faudrait pour cela votre signature numérique réalisée uniquement par votre <i>iPhone</i> et avec la connaissance de votre code <b>alpha-pin</b>. Votre banquier doit respecter les directives du virement SEPA et toute transaction n'est utilisable qu'une seule fois. Afin de mieux encore garantir votre confidentialité, aucun de vos correspondants autre que les banquiers et nous, n'aura accès à votre IBAN, BIC, ni à votre e-mail. Vous utilisez et diffusez un <i>code marchand</i> représenté par un QRcode reçu par e-mail si l'enregistrement est validé. En revanche, ce <i>code marchand</i> permet à la personne qui le possède de vous verser de l'argent et vous en êtes notifiés. Nous référençons ce jour 21065 agences bancaires en France et si par malchance votre agence n'est pas trouvée par votre IBAN, un email vous invitera à nous donner l'adresse exacte de celle ci.</p>"
    o += "<p>Le numéro de sécurité sociale est optionel. Il vous permet de demander la validation (un certificat) de votre identité numérique à une administration locale, et ainsi guarantir l'unicité de cette identité. Ce qui sera requis pour de futures opérations citoyenne comme le vote par Internet. Cette fonction est indépendante du moyen de paiement numérique mais elle suit le même principe de sécurité, en particulier une authentification forte par votre <i>iPhone</i> et la connaissance du code <b>alpha-pin</b> associé.</p>"
    o += "<p>Le nom et le(s) prénom(s) doivent correspondre strictement à ceux déclarés auprès de votre banquier lors de l'ouverture du compte identifié par l'IBAN, sinon le conseiller financier ne vous validera pas votre identité et vous ne pourrez pas payer, seulement recevoir de l'argent. De même, pour utiliser votre <i>iPhone</i> lors de démarches citoyennes, il faudra que les noms et prénoms soient ceux de vos papiers d'identité officiels pour avoir une validation de l'administration.</p>"
    o += "<p>Le code BIC n'est pas utile dans le mesure où il est retrouvé à partir de l'IBAN, mais nous nous en servons seulement pour vérification. Toute demande d'enregistrement avec un IBAN+BIC incohérents est refusée. Nous référençons 538 codes BIC pour la France, et si selon une très faible probabilité, votre BIC est inconnu à l'enregistrement, merci de nous le communiquer afin que nous puissions vérifier et corriger.<p>"
    o += '<p>Pour vérifier que vous utilisez la dernière version du site, vous pouvez comparer le code du condensé : <b>%s</b> avec celui affiché sur <a href="https://github.com/pelinquin/pingpongcash">github</a>. Notez enfin que cette page ne contient aucun code <i>JavaScript</i>, ni <i>cookies</i>.</p>\n' % __digest__.decode('ascii')
    return o


def front_html(nb, cm='', t=[], pub=False, total='', msg=''):
    "_"
    today = '%s' % datetime.datetime.now()
    o = '<?xml version="1.0" encoding="utf8"?>\n' 
    o += '<html>\n<link rel="shortcut icon" type="www/image/png" href="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAFAAAABQCAIAAAABc2X6AAAABmJLR0QA/wD/AP+gvaeTAAAAoklEQVR4nO3csQ0CMRAAQR6R0wk1URo1UYnpgA4M0iNA65n0kltdankbYxxWcvz1At8muE5wneA6wXWn+fhyO0+m9+vjo8u8a89Wy11YcJ3gOsF1gusE1wmuE1wnuE5wneA6wXWC6wTXCa4TXCe4TnCd4DrBdYLrBNcJrhNcJ7juxYv4ufnL9P+03IUF1wmuE1wnuG7zy0Oc4DrBdYLrBNc9AUj0DSD4QMJ7AAAAAElFTkSuQmCC"/>'
    o += '<style type="text/css">@import url(http://fonts.googleapis.com/css?family=Schoolbell);p,li,i,b,a,div,input {font-family:"Lucida Grande", "Lucida Sans Unicode", Helvetica, Arial, Verdana, sans-serif;}a{color:DodgerBlue;text-decoration:none}p.alpha{font-family:Schoolbell;color:#F87217;font-size:26pt;position:absolute;top:95;left:80;}a.qr{position:absolute;top:0;right:0;margin:15}p.msg{font-size:20;position:absolute;top:100;right:20;color:#999;}p.stat{font-size:9;position:absolute;top:0;right:20;color:#999;}input{font-size:18;margin:3}input.txt{width:350}input.digit{width:120}input[type=checkbox]{width:50}input[type=submit]{color:white;background-color:#AAA;border:none;border-radius:8px;padding:3}p,li{font-size:11;color:#333;}b.red{color:red;}b.green{color:green;}b.bigorange{font-size:32;color:#F87217;}#wrap{overflow:hidden;}a.ppc{font-weight:bold;font-size:.9em}a.ppc:after{font-weight:normal;content:"Cash"}#lcol{float:left; width:360;padding:4}#rcol{margin-left:368;padding:4}#footer{background:#EEE;color:#999;text-align:right;font-size:10;padding:4}table{border:1px solid #666;border-collapse:collapse}td,th{border:1px solid #666;padding:2pt;}</style>'
    o += '<a href="http://pingpongcash.net"><img title="Enfin un moyen de paiement numérique, simple, gratuit et sécurisé !" src="%s"/></a>\n' % get_image('www/header.png')
    o += '<p class="alpha" title="still in security test phase!">Beta</p>'
    data = 'àà.eu/zgnZQW' # give the real one!
    o += '<a class="qr" href="http://%s" title="...notre code marchand \'%s\'">%s</a>\n' % (data, data, QRCode(data=data).svg(10, 10, 4))    

    o += '<p class="stat">%s inscrits | %s transactions</p>' % (nb[0].decode('ascii'), nb[1].decode('ascii'))
    dmsg = '| %s' % msg if msg else ''
    if t and not pub:
        dmsg += 'Bonjour %s %s !' % (t[_FRST], t[_LAST])
        o += '<p class="msg">%s</p>' % dmsg


    o += '<div id="wrap">'
    if cm == '':
        if not pub:
            o += '<div id="lcol">'
            o += '<form method="post">\n'
            o += '<input class="txt" type="text" name="name" placeholder="E-mail" required="yes"/><br/>'
            o += '<input class="txt" type="password" name="pw" placeholder="Mot de passe"/><br/>'
            o += '<input class="sh" type="submit" value="Se connecter"/> '
            o += '<input class="sh" type="submit" name="lost" value="Mot de passe oublié"/>\n'
            o += '</form>\n'
            o += '<form method="post">\n'
            o += '<input class="txt" type="text" name="first" placeholder="Prénom(s)" title="liste complète" required="yes"/><br/>'
            o += '<input class="txt" type="text" name="last" placeholder="Nom de famille" required="yes"/><br/>'
            o += '<input class="txt" type="text" name="name" placeholder="E-mail" title="n\'est pas communiqué" required="yes"/><br/>'
            o += '<input class="txt" type="text" name="iban" placeholder="IBAN" required="yes"/><br/>'
            o += '<input class="txt" type="text" name="bic" placeholder="Code BIC" pattern="[A-Z0-9]{8,11}" title="pour vérification" required="yes"/><br/>'
            o += '<input class="txt" type="text" name="ssid" placeholder="[Optionel] Numéro de sécurité sociale"/><br/>'
            o += '<input class="txt" type="text" name="dname" placeholder="[Optionel] Nom affiché de marchand"/><br/>'
            o += '<input class="txt" type="password" name="pw" placeholder="Mot de passe" title="de plus de 4 caractères" required="yes"/><br/>'
            o += '<input class="txt" type="password" name="pw2" placeholder="Confirmation de mot de passe" required="yes"/><br/>'
            o += '<input class="txt" type="checkbox" name="read" title="j\'ai lu les avertissements ci contre" required="yes"/>'
            o += '<input class="sh" type="submit" value="S\'enregistrer"/>\n'
            o += '</form>\n'
            o += '</div>'
            o += '<div id="rcol">%s</div>' % help_register()
    else:
        if pub:
            o += '<div id="lcol">'
            o += '<form method="post">\n'
            v = 'value="%s"' % total if total else 'placeholder="000.00"'
            o += '<input class="digit" type="text" name="total" pattern="\d\d\d\.\d\d" %s required="yes"/> €<br/>'% v
            #o += '<input class="digit" type="text" name="total" %s required="yes"/> €<br/>'% v
            o += '<input class="sh" type="submit" name="income" value="Editer une facture"/><br/>\n'
            o += '<input class="sh" type="submit" name="send"   value="Envoyer par e-mail" disabled="yes"/><br/>\n'
            o += '<input class="sh" type="submit" name="tweet"  value="Poster un tweet" disabled="yes"/>\n'
            o += '</form>\n'
            o += '</div>'
            o += '<div id="rcol">'
            if t[_PUBN] != '':
                o += '<b class="bigorange" title="Nom affiché de marchand">\"%s\"</b>' % t[_PUBN]
            total = re.sub('€', '', total)
            data = '%s?%06.2f€' % (cm, float(total)) if total != '' else cm
            o += '<p title="...code marchand \'%s\' en QRcode">%s</p>\n' % (data, QRCode(data=data).svg(100, 50, 12, data))    
            o += '</div>'
        else:
            o += '<div id="lcol">' 
            o += '<p>Identifiant: <b class="green">%s</b></p>' % t[_MAIL]
            st = 'Admistrateur' if t[_STAT] == 'A' else 'Banquier' if t[_STAT] == 'B' else 'Particulier' 
            o += '<p>Statut utilisateur: <b class="green">%s</b></p>' % st
            o += '<p>Statut crédit: <b class="green">%s</b></p>' % 'valide'
            o += '<p>Statut débit: <b class="red">%s</b></p>' % 'en attente de validation par le banquier'
            o += '<p title="Identité Numérique Citoyenne">Statut INC: <b class="red">%s</b></p>' % 'en attente de validation par une adminnistration'
            o += '<p>Seuils d\'achâts : <b class="green">%d€/jour</b> maximum <b class="green">%d€</b></p>' % (int(t[_THR1]), int(t[_THR2])) 
            o += '<p>Montant autorisé le <b class="green">%s</b> : <b class="green">%d€</b></p>' % (today[:10],0) 
            o += '<p>Code marchand: <b class="green">%s</b></p>' % cm
            o += '<p>Nom affiché de marchand: <b class="green">%s</b></p>' % t[_PUBN]
            o += '<p>Date d\'enregistrement: <b class="green">%s</b></p>' % time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(float(t[_DREG])))
            o += '<form method="post">\n'
            o += '<input type="hidden" name="name" value="%s"/>' % t[_MAIL]
            o += '<input class="txt" type="password" name="pw" placeholder="Mot de passe" required="yes"/><br/>'
            o += '<input class="txt" type="password" name="pw1" placeholder="Nouveau mot de passe" required="yes"/><br/>'
            o += '<input class="txt" type="password" name="pw2" placeholder="Confirmation de mot de passe" required="yes"/><br/>'
            o += '<input class="sh" type="submit" name="new" value="Changer votre mot de passe"/> '
            o += '</form>\n'        
            o += '<form method="post">\n'
            o += '<input class="txt" type="password" name="pw" placeholder="Mot de passe" required="yes"/><br/>'
            o += '<input class="sh" type="submit" name="lock" value="Bloquer tout achât" %s/>\n' % 'disabled="yes"'
            o += '</form>\n'
            o += '</div>'
            o += '<div id="rcol">%s</div>' % help_private(cm)
            o += '<table title="historique des opérations"><tr><th width="100">Date</th><th width="20">+/-</th><th width="150">Opération</th><th width="280">Message</th><th width="100">Montant</th></tr><tr><td colspan="5"><p align="center">Aucune opération</p></td></tr></table>'

            o += '</div>'

    o += '</div>'
    o += '<div id="footer">Contact: <a href="mailto:contact@pingpongcash.net">contact@pingpongcash.net</a><br/><a href="http://cupfoundation.net">⊔FOUNDATION</a> is registered in Toulouse/France SIREN: 399 661 602 00025</div>'
    return o + '</html>'

def old_style_html():
    o = '@import url(http://fonts.googleapis.com/css?family=Schoolbell);h1,h6,p,i,li,a {font-family:"Lucida Grande", "Lucida Sans Unicode", Helvetica, Arial, Verdana, sans-serif;}input{font-size:18;margin:3}input.txt{width:350}input[type=checkbox]{width:50}input[type=submit]{color:white;background-color:#AAA;border:none;border-radius:8px;padding:3}p,li{font-size:10;color:#333;}div.col{position:absolute;top:150;left:360;margin:20}a.qr{position:absolute;top:0;right:50;margin:10}h6.login{font-size:20;position:absolute;top:100;right:100;}h6{text-align:right;color:#AAA;}rect{fill:darkBlue;}b.green{color:green;}b.biggreen{font-size:32;color:green;}b.red{color:red;}p.alpha{position:absolute;top:100;left:80;font-size:24pt;font-family:Schoolbell;color:#F87217} a.ppc{color:RoyalBlue;font-weight:bold;font-size:.9em}a.ppc:after{font-weight:normal;content:"Cash";}'

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


#pelinquin@gmail.com -> gtMVi0
#frhvbqi6i/eOYqzQ -> gtMVi0
#gtMVi0 -> pelinquin@gmail.com/X//1369814966/Laurent/Fournier/Cup Foundation/167071927202809/frhvbqi6i/eOYqzQ/CMCIFR29/100/3000/0//0s1BeDEvqU/


def init_dbs(dbs):
    "_"
    di = '/cup/%s' % __app__
    if not os.path.exists(di): os.makedirs(di)
    for dbn in dbs:
        db = '/cup/%s/%s.db' % (__app__, dbn)
        if not os.path.isfile(db):
            d = dbm.open(db[:-3], 'c')
            d['__N'] = '0'
            d.close()
            os.chmod(db, 511)

def same_bic(d, biban, siban):
    "_"
    bs = d[biban].decode('utf8').split('/')
    ps = d[siban].decode('utf8').split('/')
    return bs[1] == ps[1]

def old_daylist(d, msg, day, iban, sig):
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
    else:
        o = 'Error:Bad signature'
    return o

def smail(dest, content):
    s = smtplib.SMTP('cup')
    print (dest)
    #s.sendmail ('contact@pingpongcash.net', [dest], content)
    s.sendmail (b'contact@pingpongcash.net', [dest], content)
    s.quit()

def old_transaction (d, msg, epoch, s_biban, s_siban, val, s_sig):
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

def log(s, ip=''):
    "Append to head log file"
    logf, now = '/cup/%s/log' % __app__, '%s' % datetime.datetime.now()
    if not os.path.isfile(logf): open(logf, 'w', encoding='utf8').write('%s|%s Logfile Creation\n' % (now[:-7], ip) )     
    cont = open(logf, 'r', encoding='utf8').read()
    open(logf, 'w', encoding='utf8').write('%s|%s|%s\n%s' % (now[:-7], ip, s, cont))

_PAT_LOGIN_  = r'name=([^&/]{2,40}@[^&/]{2,30}\.[^&/]{2,10})&pw=(\S{4,30})$'
_PAT_LOST_   = r'name=([^&/]{2,40}@[^&/]{2,30}\.[^&/]{2,10})&pw=&lost=Mot de passe oublié$'
_PAT_INCOME_ = r'total=([\d\.]{1,7})&income=Editer une facture$'
_PAT_CHPWD_  = r'name=([^&/]{2,40}@[^&/]{2,30}\.[^&/]{2,10})&pw=(\S{4,30})&pw1=(\S{4,30})&pw2=(\S{4,30})&new=Changer votre mot de passe$'
_PAT_REG_    = r'first=([^&/]{3,80})&last=([^&/]{3,80})&name=([^&/]{2,40}@[^&/]{3,40})&iban=([a-zA-Z\d ]{16,38})&bic=([A-Z\d]{8,11})&ssid=([^&/]{,50})&dname=([^&/]{,100})&pw=([^&]{2,20})&pw2=([^&]{2,20})&read=on$'
_PAT_PUBKEY_ = r'PK/1/(([^&/]{2,40}@[^&/]{2,30}\.[^&/]{2,10})/([^/]{80,100})/([^/]{80,100}))/(\S{160,200})$'
_PAT_TRANS_  = r'(TR|VD)/1/((\d{10})/([^/]{6})/([^/]{6})/(B|C|\d{3}\.\d{2}))/(\S{160,200})$'

def transaction_match(dusr, dtrx, gr):
    "_"
    o = ''
    today = '%s' % datetime.datetime.now()
    trvd, msg, epoch, src, dst, val, sig = gr[0], gr[1], gr[2], gr[3], gr[4], gr[5], gr[6] 
    if src.encode('ascii') in dusr.keys() and dst.encode('ascii') in dusr.keys(): 
        tb, ts, k = dusr[src].decode('utf8').split('/'),dusr[dst].decode('utf8').split('/'), ecdsa()
        k.pt = Point(curve_521, b64toi(tb[_PBK1].encode('ascii')), b64toi(tb[_PBK2].encode('ascii')))
        if k.verify(sig, msg):
            if trvd == 'VD' and tb[_STAT] == 'A':
                ts[_STAT] = 'B'
            dusr[src], dusr[dst] = '/'.join(tb), '/'.join(ts)
            dtrx['__N'] = '%d' % (int(dtrx['__N']) + 1)
            dtrx['%s/%s' % (epoch, src)] = '/'.join([dst, val, val, sig])
            x, tx = '%s/%s' % (today[:10], tb[_NBNK]), '/'.join([epoch, src])
            dtrx[x] = dtrx[x] + b'/' + tx.encode('ascii') if x.encode('ascii') in dtrx.keys() else tx
        else:
            o = 'Wrong signature!'
    else:
        o = 'unknown cm'
    return o

def pubkey_match(dusr, gr):
    "_"
    o = ''
    today = '%s' % datetime.datetime.now()
    raw, mail, pk1, pk2, sig = gr[0], gr[1], gr[2], gr[3], gr[4] 
    if mail.encode('ascii') in dusr.keys(): 
        t, k = dusr[dusr[mail]].decode('utf8').split('/'), ecdsa()
        k.pt = Point(curve_521, b64toi(pk1.encode('ascii')), b64toi(pk2.encode('ascii')))
        msg = '/'.join([today[:10], t[_PAWD], raw])
        if k.verify(sig, msg): 
            cm = dusr[mail] # ! CAN SOMEONE CHANGE PUBKEY?
            t = dusr[cm].decode('utf8').split('/')
            t[_PBK1], t[_PBK2] = pk1, pk2 
            dusr[cm] = '/'.join(t)
        else:
            o = 'Wrong signature!'
    else:
        o = 'e-mail unknown!'
    return o

def register_match(dusr, gr):
    "_"
    k, o = None, ''
    mail = gr[2]
    if gr[7] == gr[8]:
        if mail.encode('ascii') in dusr.keys(): o = 'this e-mail is already registered!'
        else:
            while True:
                epoch = '%s' % time.mktime(time.gmtime())
                cid = compact(gr[3])
                k = h6(cid + '/' + epoch[:-2])
                if k not in dusr.keys(): break
            dusr['__N'] = '%d' % (int(dusr['__N']) + 1)
            dusr[mail] = k
            dusr[cid] = dusr[cid] + bytes('/%s' % k, 'ascii') if cid.encode('ascii') in dusr.keys() else k
            st = 'A' if mail == __email__ else 'X'
            dusr[k] = '/'.join([  
                    mail,           #_MAIL 
                    'X',            #_STAT
                    st,             #_LOCK
                    epoch[:-2],     #_DREG
                    gr[0].title(),  #_FRST 
                    gr[1].title(),  #_LSAT
                    gr[6],          #_PUBN
                    gr[5],          #_SECU
                    compact(gr[3]), #_NBNK_IBAN 
                    gr[4],          # CBIC
                    '100',          #_THR1
                    '3000',         #_THR2
                    '0',            #_BALA
                    '',             #_DEXP
                    h10(gr[7]),     #_PAWD
                    '',''])         #_PBK1_PBK2
    else:
        o = 'not the same password!'
    # check valid IBAN, IBAN == BIC, valid email, valid ssid
    return k, o

def login_match(dusr, gr):
    "_"
    cm, o = None, ''
    mail = gr[0]
    if mail.encode('ascii') in dusr.keys():
        if h10(gr[1]).encode('utf8').decode('ascii') == (dusr[dusr[mail]].decode('utf8').split('/'))[_PAWD]: 
            if len(gr) > 2:
                if gr[2] == gr[3]:
                    cm = dusr[mail]
                    t = dusr[cm].decode('utf8').split('/')
                    t[_PAWD] = h10(gr[2])
                    dusr[cm] = '/'.join(t)
                else:
                    o = 'different new passwords'
            else:
                cm = dusr[mail]
        else:
            o = 'bad password'
    else:
        o = 'this e-mail is not registered! %s' % mail
    return cm, o

def application(environ, start_response):
    "wsgi server app"
    mime, o, now, fname = 'text/plain; charset=utf8', 'Error:', '%s' % datetime.datetime.now(), 'default.txt'
    init_dbs(('trx', 'ags', 'bic', 'usr'))
    (raw, way) = (environ['wsgi.input'].read(), 'post') if environ['REQUEST_METHOD'].lower() == 'post' else (urllib.parse.unquote(environ['QUERY_STRING']), 'get')
    base = environ['PATH_INFO'][1:]
    dusr, dtrx = dbm.open('/cup/pp/usr', 'c'), dbm.open('/cup/pp/trx', 'c')
    nb = [dusr['__N'], dtrx['__N']]
    if way == 'post':
        arg = urllib.parse.unquote_plus(raw.decode('utf8'))
        if reg(re.match(_PAT_LOGIN_, arg)):
            #smail ('pelinquin@gmail.com', 'LOGIN OK \n')
            cm, res = login_match(dusr, reg.v.groups())
            if cm:
                t = dusr[cm].decode('utf8').split('/')
                o, mime = front_html(nb, cm.decode('ascii'), t), 'text/html; charset=utf8'
            else:
                o += res
        elif reg(re.match(_PAT_LOST_, arg)):
            o = 'you will receive an e-mail to reset your password !'
        elif reg(re.match(_PAT_CHPWD_, arg)):
            cm, res = login_match(dusr, reg.v.groups())
            if cm:
                t = dusr[cm].decode('utf8').split('/')
                o, mime = front_html(nb, cm.decode('ascii'), t, False, '', 'Mot de passe changé!'), 'text/html; charset=utf8'
            else:
                o += res
        elif reg(re.match(_PAT_REG_, arg)):
            k, res = register_match(dusr, reg.v.groups())
            if k:
                t = dusr[k].decode('utf8').split('/')
                o, mime = front_html(nb, k, t), 'text/html; charset=utf8'
            else:
                o += res
        elif reg(re.match(_PAT_INCOME_, arg)):
            o = 'facture! %s' % base
            t = dusr[base].decode('utf8').split('/')
            o, mime = front_html(nb, base, t, True, reg.v.group(1), 'Facture'), 'text/html; charset=utf8'
        elif reg(re.match(_PAT_PUBKEY_, arg)):
            res = pubkey_match(dusr, reg.v.groups())
            if res: o += res
            else: o = 'PUBKEY OK' 
        elif reg(re.match(_PAT_TRANS_, arg)):
            res = transaction_match(dusr, dtrx, reg.v.groups())
            if res: o += res
            #else: o = 'TRANSACTION OK (%s)' % reg.v.group(1)
            else: o, mime = pdf_digital_check(), 'application/pdf'
        else:
            o += 'not valid args %s' % arg
    else:
        log(raw, environ['REMOTE_ADDR'])
        if raw.lower() == '_update':
            o, mime = app_update(environ['SERVER_NAME']), 'text/html'
        elif raw.lower() == '_log':
            o = open('/cup/%s/log' % __app__, 'r', encoding='utf8').read()                
        elif raw.lower() == '_usr':
            d, o = dbm.open('/cup/pp/usr'), ''
            for x in d.keys(): o += '%s -> %s\n'  % (x.decode('utf8') , d[x].decode('utf8'))
            d.close()
        elif raw.lower() == '_trx':
            d, o = dbm.open('/cup/pp/trx'), ''
            for x in d.keys(): o += '%s -> %s\n'  % (x.decode('utf8') , d[x].decode('utf8'))
            d.close()
        elif raw.lower() == '_reset_usr': # DEBUG!
            os.remove('/cup/pp/usr.db')
            o = 'reset USR OK'
        elif raw.lower() == '_reset_trx': # DEBUG!
            os.remove('/cup/pp/trx.db')
            o = 'reset TRX OK'
        elif base == '': # public pages
            o, mime = front_html(nb), 'text/html; charset=utf8'
        else:
            if base.encode('ascii') in dusr.keys():
                t = dusr[base].decode('utf8').split('/')
                o, mime = front_html(nb, base, t, True, raw, 'Facture'), 'text/html; charset=utf8'
            else:
                o += 'IBAN NOT registered'                
    dtrx.close()
    dusr.close()    
    start_response('200 OK', [('Content-type', mime)])
    #start_response('200 OK', [('Content-type', mime), ('Content-Disposition', 'filename={}'.format(fname))])
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

##### RSA #####

def sign(d, n, msg):
    return itob64(pow(H(msg), d, n))

def verify(e, n, msg, s):
    return (pow(b64toi(s), e, n) == H(msg)) 

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

# NIST Curve P-521:
_p = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151
_r = 6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449
_b = 0x051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00
_Gx = 0xc6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66
_Gy = 0x11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650

INFINITY = Point( None, None, None )  
curve_521 = CurveFp( _p, -3, _b )
encoded_oid_ecPublicKey = encode_oid(*(1, 2, 840, 10045, 2, 1))
NIST521p = Curve("NIST521p", curve_521, Point( curve_521, _Gx, _Gy, _r ), (1, 3, 132, 0, 35))

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

####### PDF #########

class updf:
    def __init__(self, pagew, pageh, binary=True):
        self.pw = pagew
        self.ph = pageh
        self.mx, self.my = 25, 25
        self.binary = binary
        self.i = 0
        self.pos = []
        self.o = b'%PDF-1.4\n%'
        fpath = '/cup/fonts/'
        self.afm = [AFM(open(fpath + '%s.afm' % f)) for f in __fonts__]
        self.pfb = [open(fpath + '%s.pfb' % f, 'rb').read() for f in __embedded_fonts__]
    
    def add(self, line):
        self.pos.append(len(self.o))
        self.i += 1
        self.o += bytes('%d 0 obj<<%s>>endobj\n' % (self.i, line), 'ascii')
    
    def addnull(self):
        self.pos.append(len(self.o))
        self.i += 1
        self.o += bytes('%d 0 obj 0 endobj\n' % (self.i), 'ascii')
    
    def addarray(self, a):
        self.pos.append(len(self.o))
        self.i += 1
        self.o += bytes('%d 0 obj [%s] endobj\n' % (self.i, ''.join(['%s '%i for i in a])), 'ascii')
    
    def adds(self, stream):
        self.pos.append(len(self.o))
        self.i += 1
        if self.binary: stream = zlib.compress(stream) 
        fil = '/Filter/FlateDecode' if self.binary else ''
        self.o += bytes('%d 0 obj<</Length %d%s>>stream\n' % (self.i, len(stream), fil), 'ascii')
        self.o += stream
        self.o += b'endstream endobj\n'

    def adds3(self, stream):
        self.pos.append(len(self.o))
        self.i += 1
        fil = '/Filter/FlateDecode' if self.binary else ''
        len1, len2, len3 = 0, 0, 0
        m = re.search(b'currentfile eexec', stream)
        if m: len1 = m.start()+18
        m = re.search(b'0000000000', stream)
        if m: len2 = m.start() - len1
        len3 = len(stream) - len1 - len2
        if self.binary: stream = zlib.compress(stream) 
        ltot = len(stream)
        self.o += bytes('%d 0 obj<</Length1 %d/Length2 %d/Length3 %d/Length %d%s>>stream\n' % (self.i, len1, len2, len3, ltot, fil), 'ascii')
        self.o += stream
        self.o += b'endstream endobj\n'

    def kern(self, s, a):
        ""
        return ')-338('.join([a.k(l) for l in s.split()])

    def sgen(self, par):
        "stream parser"
        if par[3] == '⊔':
            w, x, y = int(par[2].split('F')[0]), par[0]+self.mx, self.ph-par[1]-self.my
            o = '.11 .35 1.0 rg %s %s %s %s re %s %s %s %s re %s %s %s %s re f 0 0 0 rg ' % (x, y, w, w/4, x, y, w/4, 1.5*w, x+w, y, w/4, 1.5*w)
        else:
            ff, other = par[2].split('F'), False
            o = '1 0 0 1 %s %s Tm /F%s %s Tf %s TL ' % (par[0]+self.mx, self.ph-par[1]-self.my, ff[1], ff[0], 1.2*int(ff[0]))
            for m in re.compile(r'([^\n]+)').finditer(par[3]):
                o += '%s[(%s)]TJ ' % ('T* ' if other else '', self.kern(m.group(1), self.afm[int(ff[1])-1])) 
                other = True
        return o

    def qrcode(self, ox, oy, w, content="none"):
        o = b'0 0 0 rg '
        m = ['1111111010011000001111111', 
             '1000001001110011101000001', 
             '1011101000000101001011101', 
             '1011101000001101101011101', 
             '1011101000000100101011101', 
             '1000001001110001001000001', 
             '1111111010101010101111111', 
             '0000000000101100100000000', 
             '0111001110111101110000001', 
             '0000010100101011000011110', 
             '0000101001101001011010100', 
             '0000010010000011101000110', 
             '0100011110011010010110100', 
             '0110000001111000010100001', 
             '1100001100100000010011011', 
             '1010000011110111000010000', 
             '1010111100011100111110111', 
             '0000000011100001100011010', 
             '1111111010111001101011000', 
             '1000001001101101100010100', 
             '1011101001000001111110010', 
             '1011101010111111110101011', 
             '1011101011000011110011000', 
             '1000001011110111000101000',
             '1111111000111010101111111'] 
        for i in range(len(m)):
            for j in range(len(m)):
                if m[i][j] == '1': o += bytes('%d %d %d %d re ' % (ox+i*w, oy-j*w, w, w), 'ascii')
        return o + b'f '

    def gen(self, document):
        "generate a valid binary PDF file, ready for printing!"
        np = len(document)
        self.o += b'\xBF\xF7\xA2\xFE\n' if self.binary else b'ASCII!\n'
        self.add('/Linearized 1.0/L 1565/H [570 128]/O 11/E 947/N 111/T 1367')
        ref, kids, seenall, fref, h, firstp = [], '', {}, [], {}, 0
        for p, page in enumerate(document):
            w, x, y = 12, 26, 798
            t = bytes('.11 .35 1 rg %s %s %s %s re %s %s %s %s re %s %s %s %s re f ' % (x, y, w, w/4, x, y, w/4, 1.5*w, x+w, y, w/4, 1.5*w),'ascii')
            t += bytes('BT 1 w 0.9 0.9 0.9 RG %s %s %s %s re S 0 0 0 RG 0 Tc ' % (self.mx, self.my, self.pw-2*self.mx, self.ph-2*self.my), 'ascii')
            t += b'0.99 0.99 0.99 rg 137 150 50 400 re f 137 100 321 50 re f 408 150 50 400 re f '
            t += b'0.88 0.95 1.0 rg 44 600 505 190 re f '
            t += self.qrcode(498, 788, 2)
            t += b'1.0 1.0 1.0 rg 1 0 0 1 60 680 Tm /F1 60 Tf (Put your Ads here)Tj 0.0 0.0 0.0 rg '
            for par in page: t += bytes(self.sgen(par), 'ascii')
            t += b'ET\n'
            self.adds(t)
            ref.append('%s 0 R' % self.i)
        for p, page in enumerate(document):
            seen = {}
            for par in page:
                for m in re.compile('/\d+F(\d+)\{').finditer('/%s{%s' % (par[2], par[3])):
                    seen[m.group(1)] = True
            fref.append(' '.join(seen))
            seenall.update(seen)
        fc, lc = 0, 255 
        for f in seenall:
            #print (f, len(__fonts__)-3)
            if int(f) > len(__fonts__)-1:
            #if int(f) > len(__fonts__)-3:
                print (f)
                self.addarray([self.afm[int(f)-1].w(i) for i in range(fc, lc+1)])
                indice = int(f)-len(__fonts__)+2
                self.adds3(self.pfb[int(f)-len(__fonts__)+2])
                bb = self.afm[int(f)-1]._header[b'FontBBox']
                self.add('/Type/FontDescriptor/FontName/%s/Flags 4/FontBBox[%s]/Ascent 704/CapHeight 674/Descent -194/ItalicAngle 0/StemV 109/FontFile %s 0 R' % (__fonts__[int(f)-1], ''.join(['%s '% i for i in bb]), self.i))
                self.add('/Type/Font/Subtype/Type1/BaseFont/%s/FirstChar %d/LastChar %s/Widths %s 0 R/FontDescriptor %d 0 R'% (__fonts__[int(f)-1], fc, lc, self.i-2 , self.i))
            else:
                self.addnull()
                self.addnull()
                self.addnull()
                self.add('/Type/Font/Subtype/Type1/BaseFont/%s' % (__fonts__[int(f)-1]))
            h[f] = self.i
        #nba = ['www.google.com']
        nba = []
        for a in nba:
            #self.add('/Type/Annot/Subtype/Link/Border[16 16 1]/Rect[150 600 270 640]/Dest[10 0 R/Fit]')
            self.add('/Type/Annot/Subtype/Link/Border[16 16 1]/Rect[150 600 270 640]/A<</Type/Action/S/URI/URI(http://pelinquin/u?beamer)>> ')
            #self.add('/Type/Annot/Subtype/Link/Border[16 16 1]/Rect[150 600 270 640]/A<</S/URL/URL(./u?beamer)>> ')
            #self.add('/Type/Annot/Subtype/Link/Border[16 16 1]/K<</Type/MCR/MCID 0/Pg 10 0 R>>/A<</S/URL/URL(http://pelinquin/u?beamer)>> ')
        aref = self.i
        pref = np + self.i + 1
        for p, page in enumerate(document):
            fo = functools.reduce(lambda y, i: y+'/F%s %d 0 R' % (i, h[i]), fref[p].split(), '')
            #self.add('/Type/Page/Parent %d 0 R/Contents %s/Annots[%d 0 R]/Resources<</Font<<%s>> >> ' % (pref, ref[p], aref, fo))
            self.add('/Type/Page/Parent %d 0 R/Contents %s/Resources<</Font<<%s>> >> ' % (pref, ref[p], fo))
            kids += '%s 0 R ' % self.i
            if p == 1: firstp = self.i
        self.add('/Type/Pages/MediaBox[0 0 %s %s]/Count %d/Kids[%s]' % (self.pw, self.ph, np, kids[:-1]))
        pagesid = self.i
        self.add('/Type/Outlines/First %s 0 R/Last %s 0 R/Count 1' % (self.i+2, self.i+2))
        self.add('/Title (Document)/Parent %d 0 R/Dest [%d 0 R /Fit]' % (self.i, firstp)) 
        #self.add('/FS /URL /F (http://www.google.com)')
        #self.add('/URLS[%s 0 R]' % self.i)
        self.add('/Type/Catalog/Pages %d 0 R/Outlines %d 0 R/Names %d 0 R' % (pagesid, self.i-3, self.i))  
        n, size = len(self.pos), len(self.o)
        self.o += functools.reduce(lambda y, i: y+bytes('%010d 00000 n \n' % i, 'ascii'), self.pos, bytes('xref\n0 %d\n0000000000 65535 f \n' % (n+1), 'ascii'))
        self.o += bytes('trailer<</Size %d/Root %d 0 R>>startxref %s\n' % (n+1, self.i, size), 'ascii') + b'%%EOF'
        return self.o

## AFM PARSING

def _to_int(x):
    return int(float(x))

def _to_str(x):
    return x.decode('utf8')

def _to_list_of_ints(s):
    s = s.replace(b',', b' ')
    return [_to_int(val) for val in s.split()]

def _to_list_of_floats(s):
    return [float(val) for val in s.split()]

def _to_bool(s):
    if s.lower().strip() in (b'false', b'0', b'no'): return False
    else: return True

def _sanity_check(fh):
    """Check if the file at least looks like AFM. If not, raise :exc:`RuntimeError`."""
    pos = fh.tell()
    try:
        line = bytes(fh.readline(), 'ascii')
    finally:
        fh.seek(pos, 0)
    # AFM spec, Section 4: The StartFontMetrics keyword [followed by a version number] must be the first line in the file, and the
    # EndFontMetrics keyword must be the last non-empty line in the file. We just check the first line.
    if not line.startswith(b'StartFontMetrics'): raise RuntimeError('Not an AFM file')

def _parse_header(fh):
    """Reads the font metrics header (up to the char metrics) and returns
    a dictionary mapping *key* to *val*.  *val* will be converted to the
    appropriate python type as necessary; eg:
        * 'False'->False
        * '0'->0
        * '-168 -218 1000 898'-> [-168, -218, 1000, 898]
    Dictionary keys are
      StartFontMetrics, FontName, FullName, FamilyName, Weight,ItalicAngle, IsFixedPitch, FontBBox, UnderlinePosition, UnderlineThickness, Version, Notice, EncodingScheme, CapHeight, XHeight, Ascender, Descender, StartCharMetrics"""
    headerConverters = {
        b'StartFontMetrics': float,
        b'FontName': _to_str,
        b'FullName': _to_str,
        b'FamilyName': _to_str,
        b'Weight': _to_str,
        b'ItalicAngle': float,
        b'IsFixedPitch': _to_bool,
        b'FontBBox': _to_list_of_ints,
        b'UnderlinePosition': _to_int,
        b'UnderlineThickness': _to_int,
        b'Version': _to_str,
        b'Notice': _to_str,
        b'EncodingScheme': _to_str,
        b'CapHeight': float, # Is the second version a mistake, or
        b'Capheight': float, # do some AFM files contain 'Capheight'? -JKS
        b'XHeight': float,
        b'Ascender': float,
        b'Descender': float,
        b'StdHW': float,
        b'StdVW': float,
        b'StartCharMetrics': _to_int,
        b'CharacterSet': _to_str,
        b'Characters': _to_int,
        }
    d = {}
    while 1:
        line = bytes(fh.readline(), 'ascii')
        if not line: break
        line = line.rstrip()
        if line.startswith(b'Comment'): continue
        lst = line.split(b' ', 1 )
        key = lst[0]
        if len( lst ) == 2:
            val = lst[1]
        else:
            val = b''
        #key, val = line.split(' ', 1)
        try: d[key] = headerConverters[key](val)
        except ValueError:
            continue
        except KeyError:
            continue
        if key==b'StartCharMetrics': return d
    raise RuntimeError('Bad parse')

def _parse_char_metrics(fh):
    """Return a character metric dictionary.  Keys are the ASCII num of
    the character, values are a (*wx*, *name*, *bbox*) tuple, where
    *wx* is the character width, *name* is the postscript language
    name, and *bbox* is a (*llx*, *lly*, *urx*, *ury*) tuple.
    This function is incomplete per the standard, but thus far parses all the sample afm files tried."""
    ascii_d = {}
    name_d  = {}
    while 1:
        line = bytes(fh.readline(), 'ascii')
        if not line: break
        line = line.rstrip()
        if line.startswith(b'EndCharMetrics'): return ascii_d, name_d
        vals = line.split(b';')[:4]
        if len(vals) !=4 : raise RuntimeError('Bad char metrics line: %s' % line)
        num = _to_int(vals[0].split()[1])
        wx = float(vals[1].split()[1])
        name = vals[2].split()[1]
        name = name.decode('ascii')
        bbox = _to_list_of_floats(vals[3][2:])
        bbox = list(map(int, bbox))
        # Workaround: If the character name is 'Euro', give it the corresponding
        # character code, according to WinAnsiEncoding (see PDF Reference).
        if name == 'Euro':
            num = 128
        if num != -1:
            ascii_d[num] = (wx, name, bbox)
        name_d[name] = (wx, bbox)
    raise RuntimeError('Bad parse')

def _parse_kern_pairs(fh):
    """Return a kern pairs dictionary; keys are (*char1*, *char2*) tuples and values are the kern pair value.  For example, a kern pairs line like
    ``KPX A y -50`` will be represented as:: d[ ('A', 'y') ] = -50"""
    line = bytes(fh.readline(), 'ascii')
    if not line.startswith(b'StartKernPairs'): raise RuntimeError('Bad start of kern pairs data: %s'%line)
    d = {}
    while 1:
        line = bytes(fh.readline(), 'ascii')
        if not line: break
        line = line.rstrip()
        if len(line)==0: continue
        if line.startswith(b'EndKernPairs'):
            fh.readline()  # EndKernData
            return d
        vals = line.split()
        if len(vals)!=4 or vals[0]!=b'KPX':
            raise RuntimeError('Bad kern pairs line: %s'%line)
        c1, c2, val = _to_str(vals[1]), _to_str(vals[2]), float(vals[3])
        d[(c1,c2)] = val
    raise RuntimeError('Bad kern pairs parse')

def _parse_composites(fh):
    """Return a composites dictionary.  Keys are the names of the
    composites.  Values are a num parts list of composite information,
    with each element being a (*name*, *dx*, *dy*) tuple.  Thus a
    composites line reading: CC Aacute 2 ; PCC A 0 0 ; PCC acute 160 170 ;
    will be represented as:: d['Aacute'] = [ ('A', 0, 0), ('acute', 160, 170) ]"""
    d = {}
    while 1:
        line = fh.readline()
        if not line: break
        line = line.rstrip()
        if len(line)==0: continue
        if line.startswith(b'EndComposites'):
            return d
        vals = line.split(b';')
        cc = vals[0].split()
        name, numParts = cc[1], _to_int(cc[2])
        pccParts = []
        for s in vals[1:-1]:
            pcc = s.split()
            name, dx, dy = pcc[1], float(pcc[2]), float(pcc[3])
            pccParts.append( (name, dx, dy) )
        d[name] = pccParts
    raise RuntimeError('Bad composites parse')

def _parse_optional(fh):
    """Parse the optional fields for kern pair data and composites
    return value is a (*kernDict*, *compositeDict*) which are the
    return values from :func:`_parse_kern_pairs`, and
    :func:`_parse_composites` if the data exists, or empty dicts
    otherwise"""
    optional = { b'StartKernData' : _parse_kern_pairs, b'StartComposites' :  _parse_composites}
    d = {b'StartKernData':{}, b'StartComposites':{}}
    while 1:
        line = bytes(fh.readline(), 'ascii')
        if not line: break
        line = line.rstrip()
        if len(line)==0: continue
        key = line.split()[0]
        if key in optional: d[key] = optional[key](fh)
    l = ( d[b'StartKernData'], d[b'StartComposites'] )
    return l

def parse_afm(fh):
    """Parse the Adobe Font Metics file in file handle *fh*. Return value is a (*dhead*, *dcmetrics*, *dkernpairs*, *dcomposite*) tuple where
    *dhead* is a :func:`_parse_header` dict, *dcmetrics* is a
    :func:`_parse_composites` dict, *dkernpairs* is a
    :func:`_parse_kern_pairs` dict (possibly {}), and *dcomposite* is a
    :func:`_parse_composites` dict (possibly {}) """
    _sanity_check(fh)
    dhead =  _parse_header(fh)
    dcmetrics_ascii, dcmetrics_name = _parse_char_metrics(fh)
    doptional = _parse_optional(fh)
    return dhead, dcmetrics_ascii, dcmetrics_name, doptional[0], doptional[1]

class AFM:

    def __init__(self, fh):
        """Parse the AFM file in file object *fh*"""
        (dhead, dcmetrics_ascii, dcmetrics_name, dkernpairs, dcomposite) = parse_afm(fh)
        self._header = dhead
        self._kern = dkernpairs
        self._metrics = dcmetrics_ascii
        self._metrics_by_name = dcmetrics_name
        self._composite = dcomposite

    def stw(self, s):
        """ Return the string width (including kerning) """
        totalw = 0
        namelast = None
        for c in s:
            wx, name, bbox = self._metrics[ord(c)]
            l,b,w,h = bbox
            try: kp = self._kern[ (namelast, name) ]
            except KeyError: kp = 0
            totalw += wx + kp
            namelast = name
        return totalw 

    def w(self, c):
        """ Return the string width (including kerning) """
        try: w = self._metrics[c][0]
        except KeyError: w = 0
        return w

    def k0(self, s):
        """ Return PDF kerning string """
        o, l = '(', None
        for c in s + ' ':
            try: kp = - self._kern[(l, c)]
            except KeyError: kp = 0
            if l: o += '%s)%d(' % (l, kp) if kp else l
            l = c
        return o + ')'

    def k(self, s):
        """ Return PDF kerning string """
        o, l = '', None
        for c in s + ' ':
            try: kp = - self._kern[(l, c)]
            except KeyError: kp = 0
            if l: o += '%s)%d(' % (l, kp) if kp else l
            l = c
        return o 


##### PDF BUILD #####

def pdf_digital_check():
    "_"
    own = 'toto'
    today = '%s' % datetime.datetime.now()
    page = [
        (410,  18, '12F1', today[:19]), 
        (30, 20, '14F1', own), 
        (20, 260, '14F1', 'Intangible Good:'), 
        ] 
    a = updf(595, 842)
    return a.gen([page])


def pdf_digital_check1():
    "_"
    td, ig, slr, byr, url, ncl, sig = 'A', 'B', 'C', 'D', 'E', 'F', 'G'

    try: ig.encode('ascii')
    except: ig = '%s' % bytes(ig, 'utf8')
    content = [[(100, 300, '32F1', 'Invoice'),
                (420,  18, '12F1', td), 
                (20,  400, '14F1', 'Buyer: %s' % byr), 
                (20,  430, '14F1', 'Seller: %s' % slr), 
                (20,  460, '14F1', 'Intangible Good:'), 
                (300, 460, '18F1', ig), 
                (300, 500, '9F1',  '%s instances sold' % ncl), 
                (10,  630, '12F1', 'Digital Signature of dedicated IG \(ECDSA-521P\):'),
                (10,  650, '10F3', sig),
                (10,  782, '8F1',  url),
                ]]
    a = updf(595, 842)
    return a.gen(content)

def pdf_digital_check2():
    content = [[(100, 300, '32F1', 'Invoice'), ]]
    a = updf(595, 842)
    return a.gen(content)

#################### QR CODE ################

ERR_COR_L = 1
ERR_COR_M = 0
ERR_COR_Q = 3
ERR_COR_H = 2

MODE_NUMBER    = 1 << 0
MODE_ALPHA_NUM = 1 << 1
MODE_8BIT_BYTE = 1 << 2
MODE_KANJI     = 1 << 3

MODE_SIZE_SMALL  = { MODE_NUMBER: 10, MODE_ALPHA_NUM: 9,  MODE_8BIT_BYTE: 8,  MODE_KANJI: 8,}
MODE_SIZE_MEDIUM = { MODE_NUMBER: 12, MODE_ALPHA_NUM: 11, MODE_8BIT_BYTE: 16, MODE_KANJI: 10,}
MODE_SIZE_LARGE  = { MODE_NUMBER: 14, MODE_ALPHA_NUM: 13, MODE_8BIT_BYTE: 16, MODE_KANJI: 12,}

ALPHA_NUM = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:'
EXP_TABLE = list(range(256))
LOG_TABLE = list(range(256))
for i in range(8): EXP_TABLE[i] = 1 << i
for i in range(8, 256): EXP_TABLE[i] = (EXP_TABLE[i - 4] ^ EXP_TABLE[i - 5] ^ EXP_TABLE[i - 6] ^ EXP_TABLE[i - 8])
for i in range(255): LOG_TABLE[EXP_TABLE[i]] = i

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
    [],
    [6, 18],
    [6, 22],
    [6, 26],
    [6, 30],
    [6, 34],
    [6, 22, 38],
    [6, 24, 42],
    [6, 26, 46],
    [6, 28, 50],
    [6, 30, 54],
    [6, 32, 58],
    [6, 34, 62],
    [6, 26, 46, 66],
    [6, 26, 48, 70],
    [6, 26, 50, 74],
    [6, 30, 54, 78],
    [6, 30, 56, 82],
    [6, 30, 58, 86],
    [6, 34, 62, 90],
    [6, 28, 50, 72, 94],
    [6, 26, 50, 74, 98],
    [6, 30, 54, 78, 102],
    [6, 28, 54, 80, 106],
    [6, 32, 58, 84, 110],
    [6, 30, 58, 86, 114],
    [6, 34, 62, 90, 118],
    [6, 26, 50, 74, 98, 122],
    [6, 30, 54, 78, 102, 126],
    [6, 26, 52, 78, 104, 130],
    [6, 30, 56, 82, 108, 134],
    [6, 34, 60, 86, 112, 138],
    [6, 30, 58, 86, 114, 142],
    [6, 34, 62, 90, 118, 146],
    [6, 30, 54, 78, 102, 126, 150],
    [6, 24, 50, 76, 102, 128, 154],
    [6, 28, 54, 80, 106, 132, 158],
    [6, 32, 58, 84, 110, 136, 162],
    [6, 26, 54, 82, 110, 138, 166],
    [6, 30, 58, 86, 114, 142, 170]
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
    "_"
    if pattern == 0: return lambda i, j: (i + j) % 2 == 0 
    if pattern == 1: return lambda i, j: i % 2 == 0 
    if pattern == 2: return lambda i, j: j % 3 == 0
    if pattern == 3: return lambda i, j: (i + j) % 3 == 0
    if pattern == 4: return lambda i, j: (int(i / 2) + int(j / 3)) % 2 == 0
    if pattern == 5: return lambda i, j: (i * j) % 2 + (i * j) % 3 == 0
    if pattern == 6: return lambda i, j: ((i * j) % 2 + (i * j) % 3) % 2 == 0
    if pattern == 7: return lambda i, j: ((i * j) % 3 + (i + j) % 2) % 2 == 0
    raise TypeError("Bad mask pattern: " + pattern)

def length_in_bits(mode, version):
    if mode not in (MODE_NUMBER, MODE_ALPHA_NUM, MODE_8BIT_BYTE, MODE_KANJI):
        raise TypeError("Invalid mode (%s)" % mode)
    if version < 1 or version > 40:
        raise ValueError("Invalid version (was %s, expected 1 to 40)" % version)
    if version < 10: mode_size = MODE_SIZE_SMALL
    elif version < 27: mode_size = MODE_SIZE_MEDIUM
    else: mode_size = MODE_SIZE_LARGE
    return mode_size[mode]

def lost_point1(modules):
    modules_count = len(modules)
    lost_point = 0
    # LEVEL1
    for row in range(modules_count):
        for col in range(modules_count):
            sameCount = 0
            dark = modules[row][col]
            for r in range(-1, 2):
                if row + r < 0 or modules_count <= row + r: continue
                for c in range(-1, 2):
                    if col + c < 0 or modules_count <= col + c: continue
                    if r == 0 and c == 0: continue
                    if dark == modules[row + r][col + c]: sameCount += 1
            if sameCount > 5:
                lost_point += (3 + sameCount - 5)
    # LEVEL2
    for row in range(modules_count - 1):
        for col in range(modules_count - 1):
            count = 0
            if modules[row][col]: count += 1
            if modules[row + 1][col]: count += 1
            if modules[row][col + 1]: count += 1
            if modules[row + 1][col + 1]: count += 1
            if count == 0 or count == 4: lost_point += 3
    # LEVEL3
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
    # LEVEL4
    darkCount = 0
    for col in range(modules_count):
        for row in range(modules_count):
            if modules[row][col]: darkCount += 1
    ratio = abs(100 * darkCount / modules_count / modules_count - 50) / 5
    lost_point += ratio * 10
    return lost_point

class QRData:
    """ Data held in a QR compatible format. """
    def __init__(self, data, mode=None):
        """ If ``mode`` isn't provided, the most compact QR data type possible is chosen. """
        if data.isdigit(): auto_mode = MODE_NUMBER
        elif re.match('^[%s]*$' % re.escape(ALPHA_NUM), data): auto_mode = MODE_ALPHA_NUM
        else: auto_mode = MODE_8BIT_BYTE
        if mode is None:
            self.mode = auto_mode
        else:
            if mode not in (MODE_NUMBER, MODE_ALPHA_NUM, MODE_8BIT_BYTE):
                raise TypeError("Invalid mode (%s)" % mode)
            if mode < auto_mode:
                raise ValueError("Provided data can not be represented in mode %s" % mode)
            self.mode = mode
        self.data = data

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
                if len(chars) > 1:
                    buffer.put(ALPHA_NUM.find(chars[0]) * 45 + ALPHA_NUM.find(chars[1]), 11)
                else:
                    buffer.put(ALPHA_NUM.find(chars), 6)
        else:
            for c in self.data:
                buffer.put(ord(c), 8)

class BitBuffer:
    def __init__(self):
        self.buffer, self.length = [], 0

    def get(self, index):
        buf_index = int(index/8)
        return ((self.buffer[buf_index] >> (7 - index % 8)) & 1) == 1

    def put(self, num, length):
        for i in range(length): self.put_bit(((num >> (length - i - 1)) & 1) == 1)

    def __len__(self):
        return self.length

    def put_bit(self, bit):
        buf_index = self.length // 8
        if len(self.buffer) <= buf_index: self.buffer.append(0)
        if bit: self.buffer[buf_index] |= (0x80 >> (self.length % 8))
        self.length += 1

def create_bytes(buffer, rs_b):
    offset, maxDcCount, maxEcCount = 0, 0, 0
    dcdata, ecdata = [0] * len(rs_b), [0] * len(rs_b)
    for r in range(len(rs_b)):
        dcCount = rs_b[r].data_count
        ecCount = rs_b[r].total_count - dcCount
        maxDcCount, maxEcCount = max(maxDcCount, dcCount), max(maxEcCount, ecCount)
        dcdata[r] = [0] * dcCount
        for i in range(len(dcdata[r])): dcdata[r][i] = 0xff & buffer.buffer[i + offset]
        offset += dcCount
        rsPoly = Poly([1], 0) # Get error correction polynomial.
        for i in range(ecCount): rsPoly = rsPoly * Poly([1, gexp(i)], 0)
        rawPoly = Poly(dcdata[r], len(rsPoly) - 1)
        modPoly = rawPoly % rsPoly
        ecdata[r] = [0] * (len(rsPoly) - 1)
        for i in range(len(ecdata[r])):
            modIndex = i + len(modPoly) - len(ecdata[r])
            ecdata[r][i] = modPoly[modIndex] if (modIndex >= 0) else 0
    totalCodeCount = 0
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
    rs_b = rs_blocks(version, error_correction)
    buffer = BitBuffer()
    for data in data_list:
        buffer.put(data.mode, 4)
        buffer.put(len(data),
            length_in_bits(data.mode, version))
        data.write(buffer)
    # calc num max data.
    total_data_count = 0
    for block in rs_b:
        total_data_count += block.data_count
    if len(buffer) > total_data_count * 8:
        raise DataOverflowError("Code length overflow. Data size (%s) > size available (%s)" % (len(buffer), total_data_count * 8))
    # end code
    if len(buffer) + 4 <= total_data_count * 8: buffer.put(0, 4)
    # padding
    while len(buffer) % 8: buffer.put_bit(False)
    # padding
    PAD0, PAD1 = 0xEC, 0x11
    while True:
        if len(buffer) >= total_data_count * 8:
            break
        buffer.put(PAD0, 8)
        if len(buffer) >= total_data_count * 8:
            break
        buffer.put(PAD1, 8)
    return create_bytes(buffer, rs_b)

def glog(n):
    return LOG_TABLE[n]

def gexp(n):
    return EXP_TABLE[n % 255]

class Poly:
    def __init__(self, num, shift):
        offset = 0
        while offset < len(num) and num[offset] == 0: offset += 1
        self.num = [0] * (len(num) - offset + shift)
        for i in range(len(num) - offset):
            self.num[i] = num[i + offset]

    def __getitem__(self, index):
        return self.num[index]

    def __len__(self):
        return len(self.num)

    def __mul__(self, e):
        num = [0] * (len(self) + len(e) - 1)
        for i in range(len(self)):
            for j in range(len(e)):
                num[i + j] ^= gexp(glog(self[i]) + glog(e[j]))
        return Poly(num, 0)

    def __mod__(self, e):
        if len(self) - len(e) < 0: return self
        ratio = glog(self[0]) - glog(e[0])
        num = [0] * len(self)
        for i in range(len(self)):
            num[i] = self[i]
        for i in range(len(e)):
            num[i] ^= gexp(glog(e[i]) + ratio)
        return Poly(num, 0) % e

class RSBlock:
    def __init__(self, total_count, data_count):
        self.total_count, self.data_count = total_count, data_count

def rs_blocks(version, error_correction):
    if error_correction not in RS_BLOCK_OFFSET:
        raise Exception("bad rs block @ version: %s / error_correction: %s" % (version, error_correction))
    offset = RS_BLOCK_OFFSET[error_correction]
    rs_b, blocks = RS_BLOCK_TABLE[(version - 1) * 4 + offset], []
    for i in range(0, len(rs_b), 3):
        count, total_count, data_count = rs_b[i:i + 3]
        for j in range(count): blocks.append(RSBlock(total_count, data_count))
    return blocks

class QRCode:
    def __init__(self, version=None, error_correction=ERR_COR_M, data="hello"):
        self.version = version and int(version)
        self.error_correction = int(error_correction)
        self.m, self.m_count = None, 0
        self.data_cache, self.data_list = None, []
        self.data_list.append(QRData(data))
        self.best_fit(start=self.version)
        self.makeImpl(False, self.best_mask_pattern())

    def makeImpl(self, test, mask_pattern):
        self.m_count = self.version * 4 + 17
        self.m = [None] * self.m_count
        for row in range(self.m_count):
            self.m[row] = [None] * self.m_count
            for col in range(self.m_count): self.m[row][col] = None   # (col + row) % 3
        self.setup_position_probe_pattern(0, 0)
        self.setup_position_probe_pattern(self.m_count - 7, 0)
        self.setup_position_probe_pattern(0, self.m_count - 7)
        self.sutup_position_adjust_pattern()
        self.setup_timing_pattern()
        self.setup_type_info(test, mask_pattern)
        if self.version >= 7: self.setup_type_number(test)
        if self.data_cache is None: self.data_cache = create_data(self.version, self.error_correction, self.data_list)
        self.map_data(self.data_cache, mask_pattern)

    def setup_position_probe_pattern(self, row, col):
        for r in range(-1, 8):
            if row + r <= -1 or self.m_count <= row + r: continue
            for c in range(-1, 8):
                if col + c <= -1 or self.m_count <= col + c: continue
                self.m[row + r][col + c] = True if (0 <= r and r <= 6 and (c == 0 or c == 6) or (0 <= c and c <= 6 and (r == 0 or r == 6)) or (2 <= r and r <= 4 and 2 <= c and c <= 4)) else False

    def best_fit(self, start=None):
        size = start or 1
        while True:
            try:
                self.data_cache = create_data(size, self.error_correction, self.data_list)
            except DataOverflowError:
                size += 1
            else:
                self.version = size
                return size

    def best_mask_pattern(self):
        """ Find the most efficient mask pattern. """
        min_lost_point, pattern = 0, 0
        for i in range(8):
            self.makeImpl(True, i)
            lost_point = lost_point1(self.m)
            if i == 0 or min_lost_point > lost_point: min_lost_point, pattern = lost_point, i
        return pattern

    def svg(self, ox=0, oy=0, d=10, txt=''):
        "_"
        o, mc = '<svg %s width="%s" height="%s">\n' % (_SVGNS, ox+d*25, oy+d*25), self.m_count
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

    def setup_timing_pattern(self):
        for r in range(8, self.m_count - 8):
            if self.m[r][6] != None: continue
            self.m[r][6] = (r % 2 == 0)
        for c in range(8, self.m_count - 8):
            if self.m[6][c] != None: continue
            self.m[6][c] = (c % 2 == 0)

    def sutup_position_adjust_pattern(self):
        pos = pattern_position(self.version)
        for i in range(len(pos)):
            for j in range(len(pos)):
                row = pos[i]
                col = pos[j]
                if self.m[row][col] != None: continue
                for r in range(-2, 3):
                    for c in range(-2, 3):
                        self.m[row + r][col + c] = True if (r == -2 or r == 2 or c == -2 or c == 2 or (r == 0 and c == 0)) else False

    def setup_type_number(self, test):
        bits = BCH_type_number(self.version)
        for i in range(18):
            mod = (not test and ((bits >> i) & 1) == 1)
            self.m[i // 3][i % 3 + self.m_count - 8 - 3] = mod
        for i in range(18):
            mod = (not test and ((bits >> i) & 1) == 1)
            self.m[i % 3 + self.m_count - 8 - 3][i // 3] = mod

    def setup_type_info(self, test, mask_pattern):
        data = (self.error_correction << 3) | mask_pattern
        bits = BCH_type_info(data)
        for i in range(15): # vertical
            mod = (not test and ((bits >> i) & 1) == 1)
            if i < 6: self.m[i][8] = mod
            elif i < 8: self.m[i + 1][8] = mod
            else: self.m[self.m_count - 15 + i][8] = mod
        for i in range(15): # horizontal
            mod = (not test and ((bits >> i) & 1) == 1)
            if i < 8: self.m[8][self.m_count - i - 1] = mod
            elif i < 9: self.m[8][15 - i - 1 + 1] = mod
            else: self.m[8][15 - i - 1] = mod
        self.m[self.m_count - 8][8] = (not test) # fixed module

    def map_data(self, data, mask_pattern):
        inc = -1
        row = self.m_count - 1
        bitIndex, byteIndex = 7, 0
        mask_func1 = mask_func(mask_pattern)
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

############### TEST ############

def test_crypto():
    k = ecdsa()
    msg = 'Hello World!'
    s = k.sign(msg) 
    print (s, len(s))
    print(k.verify(s, msg))
    BPUB = compact('FR76 1780 7000 1445 6208 6047 866')
    d = dbm.open('/cup/ppc/keys')
    kBPUB = [b64toi(x) for x in d[BPUB].split(b'/')][2:]
    d.close()
    s = sign(kBPUB[0], kBPUB[1], msg)
    print (s, len(s))    
    print (verify(RSA_E, kBPUB[1], msg, s))    

def test_pdf():
    pass

############################################

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


if __name__ == '__main__':
    #test()
    #print (print_db())
    #test2()
    #qr = QRCode(data='hvbqi6i/eOYqzQ')
    #print (qr.svg(50,50,3))
    #test_crypto()
    #test_pdf()
    
    #toto = b'%PDF-1.4\n%\xbf\xf7\xa2\xfe\n'
    #print (toto, toto.decode('latin1'))
    #print (''.join(map(chr,toto)))

    sys.exit()
# End ⊔net!
