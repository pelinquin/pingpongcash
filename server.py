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
Small is beautiful!

Status:
'X' Iban registered 
'Y' Email registered
'Z' PubKey validated
'A' Administrator (only one)
'B' Banker (at least one per agency)
'C' Validated by banquer and payed to admin
"""

_STAT = 0  # Status
_LOCK = 1  # locked/unlocked
_DREG = 2  # Registration Date
_MAIL = 3  # unique e-mail address
_FRST = 4  # First Name
_LAST = 5  # Last name
_PUBN = 6  # Public Marchant Name
_SECU = 7  # Social Security Number
_NBNK = 8  # Bank+Agency Number in iban
_IBAN = 9  # Account Number in iban
_CBIC = 10 # Bic (just for verification)
_THR1 = 11 # Threshold 1
_THR2 = 12 # Threshold 2
_BALA = 13 # Balance value
_DEXP = 14 # Expiration Date
_PAWD = 15 # Hashed Password for locking
_PBK1 = 16 # Public Key part 1
_PBK2 = 17 # Public Key part 2

import re, os, sys, math, urllib.parse, hashlib, http.client, base64, dbm, binascii, datetime, zlib, functools, subprocess, time, smtplib, operator

__digest__ = base64.urlsafe_b64encode(hashlib.sha1(open(__file__, 'r', encoding='utf8').read().encode('utf8')).digest())[:5]
__app__    = os.path.basename(__file__)[:-3]
__ppc__    = 'pingpongcash'
__email__  = 'contact@%s.net' % __ppc__
__url__    = 'http://%s.net' % __ppc__
__acm__    = 'JHTmFk'
_XHTMLNS   = 'xmlns="http://www.w3.org/1999/xhtml"'
_SVGNS     = 'xmlns="http://www.w3.org/2000/svg"'
_XLINKNS   = 'xmlns:xlink="http://www.w3.org/1999/xlink"'

_AD1 = 'Enfin un moyen de paiement numérique,' 
_AD2 = 'simple, gratuit et sécurisé !'

_COLOR = {'g': '.7 .7 .7', 'd':'.1 .1 .6', 'b':'.5 .5 .9'}

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

__fonts__ = ('Helvetica', 'Times-Roman', 'Courier', 'Times-Bold', 'Helvetica-Bold', 'Courier-Bold', 'Times-Italic', 'Helvetica-Oblique', 
             'Courier-Oblique', 'Times-BoldItalic', 'Helvetica-BoldOblique', 'Courier-BoldOblique', 'Symbol')

__e__ = '/Euro /ccedilla /' + ' /'.join(['%s%s' % (x,y) for x in ('a','e','i','o','u','y') for y in ('acute', 'grave', 'circumflex', 'dieresis')])

def reg(value):
    " function attribute is a way to access matching group in one line test "
    reg.v = value
    return value

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
    o += '</pre><br/><a href="/">Reload the new version</a></html>'
    return o

def get_image(img):
    "_"
    here = os.path.dirname(os.path.abspath(__file__))
    return 'data:image/png;base64,%s' % base64.b64encode(open('%s/%s' % (here, img), 'rb').read()).decode('ascii')

def help_private(cm):
    "_"
    o = "<p>Cette page est votre page privée. Elle contient des informations qui ne sont pas divulguées aux personnes ou commerçants avec qui vous faites des transactions financières <a class=\"ppc\">Ping-Pong&nbsp;</a>.</p>"
    o += "<p>Votre page puplique est <a href=\"%s\">ici</a>. Elle est accessible directement depuis le code marchand en QRcode. Diffusez cette page publique ou ce QRcode à toute personne susceptible de vous verser de l'argent.</p>" % cm
    o += '<p></p>'
    o += "<p>Attention: le bloquage du compte doit être utilisé si vous perdez ou vous faites voler votre <i>iPhone</i> et il n'a de sens que si vous avez autorisation d'achât délivrée par votre banquier.</p>"
    o += "<p>Nous n'avons pas accès au solde de votre compte. La limite des montants d'achât est encadrée par les deux valeurs de seuils fournies par votre banquier. Vous pouvez le contacter votre négocier des valeur différentes.</p>"
    return o

def help_register():
    "_"
    o = "<p>Le mot de passe choisi ne permet que d'accéder au statut de votre compte et éventuellement de bloquer l'autorisation de dépenser de l'argent si vous perdez votre <i>iPhone</i>, mais en aucun cas ce mot de passe permet de faire des achâts. Pour donner de l'argent à une autre personne, il vous faut obligatoirement utiliser le code <b>alpha-pin</b> de votre <i>iPhone</i>, après création d'un jeux de clés cryptographiques, uniquement sur téléphone, déconnecté de l'Internet et enfin après acquisition du certificat de votre banquier qui confirmera le lien avec votre compte bancaire. Personne (ni l'opérateur téléphonique, ni le banquier, ni nos administrateurs informatique, ni l'Etat et aucun hacker) à part vous ne connaît ou ne doit connaître votre code <b>alpha-pin</b>, et si vous le perdez ou vi vous changez de téléphone, vous devrez simplement re-suivre la procédure d'enregistrement. Vous récupérez bien entendu le délai de cotisation de votre ancien compte.</p>"
    o += "<p>Vous pouvez vous enregistrer même si vous ne possédez pas d'<i>iPhone</i>. Vous ne pourrez que recevoir de l'argent et pas en donner.</p>"
    o += "<p>Le fait de nous communiquer votre IBAN+BIC ne permet à personne, nous compris, de retirer de l'argent sur votre compte. Il faudrait pour cela votre signature numérique réalisée uniquement par votre <i>iPhone</i> et avec la connaissance de votre code <b>alpha-pin</b>. Votre banquier doit respecter les directives du virement SEPA et toute transaction n'est utilisable qu'une seule fois. Afin de mieux encore garantir votre confidentialité, aucun de vos correspondants autre que les banquiers et nous, n'aura accès à votre IBAN, BIC, ni à votre e-mail. Vous utilisez et diffusez un <i>code marchand</i> représenté par un QRcode reçu par e-mail si l'enregistrement est validé. En revanche, ce <i>code marchand</i> permet à la personne qui le possède de vous verser de l'argent et vous en êtes notifiés. Nous référençons ce jour 21065 agences bancaires en France et si par malchance votre agence n'est pas trouvée par votre IBAN, un email vous invitera à nous donner l'adresse exacte de celle ci.</p>"
    o += "<p>Le numéro de sécurité sociale est optionel. Il vous permet de demander la validation (un certificat) de votre identité numérique à une administration locale, et ainsi guarantir l'unicité de cette identité. Ce qui sera requis pour de futures opérations citoyenne comme le vote par Internet. Cette fonction est indépendante du moyen de paiement numérique mais elle suit le même principe de sécurité, en particulier une authentification forte par votre <i>iPhone</i> et la connaissance du code <b>alpha-pin</b> associé.</p>"
    o += "<p>Le nom et le(s) prénom(s) doivent correspondre strictement à ceux déclarés auprès de votre banquier lors de l'ouverture du compte identifié par l'IBAN, sinon le conseiller financier ne vous validera pas votre identité et vous ne pourrez pas payer, seulement recevoir de l'argent. De même, pour utiliser votre <i>iPhone</i> lors de démarches citoyennes, il faudra que les noms et prénoms soient ceux de vos papiers d'identité officiels pour avoir une validation de l'administration.</p>"
    o += "<p>Le code BIC n'est pas utile dans le mesure où il est retrouvé à partir de l'IBAN, mais nous nous en servons seulement pour vérification. Toute demande d'enregistrement avec un IBAN+BIC incohérents est refusée. Nous référençons 538 codes BIC pour la France, et si selon une très faible probabilité, votre BIC est inconnu à l'enregistrement, merci de nous le communiquer afin que nous puissions vérifier et corriger.<p>"
    o += '<p>Pour vérifier que vous utilisez la dernière version du site, vous pouvez comparer le code du condensé : <b>%s</b> avec celui affiché sur <a href="https://github.com/pelinquin/pingpongcash">github</a>. Notez enfin que cette page ne contient aucun code <i>JavaScript</i>, ni <i>cookies</i>.</p>\n' % __digest__.decode('ascii')
    return o

def style_html():
    o = '<style type="text/css">@import url(http://fonts.googleapis.com/css?family=Schoolbell);h1,h2,p,li,i,b,a,div,input{font-family:"Lucida Grande", "Lucida Sans Unicode", Helvetica, Arial, Verdana, sans-serif;}a.mono,p.mono{font-family:"Lucida Concole", Courier}a.name{margin:50}a{color:DodgerBlue;text-decoration:none}p.alpha{font-family:Schoolbell;color:#F87217;font-size:26pt;position:absolute;top:95;left:80;}a.qr{position:absolute;top:0;right:0;margin:15}p.msg{font-size:20;position:absolute;top:110;right:20;color:#999;}p.stat{font-size:9;position:absolute;top:0;right:20;color:#999;}input{font-size:18;margin:3}input.txt{width:350}input.digit{width:120}input[type=checkbox]{width:50}input[type=submit]{color:white;background-color:#AAA;border:none;border-radius:8px;padding:3}p,li{font-size:11;color:#333;}b.red{color:red;}b.green{color:green;}b.bigorange{font-size:32;color:#F87217;}#wrap{overflow:hidden;}a.ppc{font-weight:bold;font-size:.9em}a.ppc:after{font-weight:normal;content:"Cash"}#lcol{float:left;width:360;padding:4}#rcol{margin-left:368;padding:4}#footer{background:#EEE;color:#999;text-align:right;font-size:10;padding:4}table{border:1px solid #666;border-collapse:collapse}td,th{border:1px solid #666;padding:2pt;}td.num{font-size:9;text-align:right}#c1{float:left;width:23%;padding:1%}#c2{float:left;width:23%;padding:1%}#c3{float:left;width:23%;padding:1%}#c4{float:left;width:23%;padding:1%}h1{color:DodgerBlue;font-size:22;margin:20 0 0 20;}h2{font-size:18;margin:5 0 0 30;}</style>'
    return o

def change_html(email, secid, dusr):
    "_"
    today = '%s' % datetime.datetime.now()
    o = '<?xml version="1.0" encoding="utf8"?>\n<html>\n' + favicon() + style_html()
    #o += '<a href="http://pingpongcash.net"><img title="Enfin un moyen de paiement numérique, simple, gratuit et sécurisé !" src="%s"/></a>\n' % get_image('www/header.png')
    #o += '<p class="alpha" title="still in security test phase!">Beta</p>'

    o += '<div id="wrap">'
    o += '<div id="lcol">'
    o += '<h1>Nouveau mot de passe</h1>'
    o += '<form method="post">\n'    
    o += '<input type="hidden" name="name" value="%s"/>'% email
    o += '<input type="hidden" name="id" value="%s"/>'% secid
    o += '<input class="txt" type="password" name="pw1" placeholder="Mot de passe" title="de plus de 4 caractères" required="yes"/><br/>'
    o += '<input class="txt" type="password" name="pw2" placeholder="Confirmation de mot de passe" required="yes"/><br/>'
    o += '<input class="sh" type="submit" value="Changer le mot de passe"/> '
    o += '</form>\n'
    o += '</div>'
    o += '<div id="rcol">'
    o += '<h1>%s</h1>' % email
    o += '</div>'    
    o += '</div>'    

    return o + footer() + '</html>'
    

def front_html(dusr, dtrx, cm='', pub=False, total='', msg='', listcm=[]):
    "_"
    nb = [dusr['__N'], dtrx['__N']]
    t = dusr[cm].decode('utf8').split('/') if cm else []
    today = '%s' % datetime.datetime.now()
    o = '<?xml version="1.0" encoding="utf8"?>\n<html>\n' + favicon() + style_html()
    o += '<a href="http://pingpongcash.net"><img title="Enfin un moyen de paiement numérique, simple, gratuit et sécurisé !" src="%s"/></a>\n' % get_image('www/header.png')
    o += '<p class="alpha" title="still in security test phase!">Beta</p>'
    data = 'pingpongcash.net/%s' % __acm__ 
    o += '<a class="qr" href="http://%s" title="...notre code marchand \'%s\'">%s</a>\n' % (data, data, QRCode(data=data).svg(10, 10, 4))    
    o += '<p class="stat">%s inscrits | %s transactions courantes</p>' % (nb[0].decode('ascii'), nb[1].decode('ascii'))
    dmsg = ' %s' % msg if msg else ''
    if t and not pub:
        dmsg = 'Bonjour %s %s, ' % (t[_FRST], t[_LAST]) + dmsg 
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
            o += '<input class="txt" type="text" name="iban" placeholder="IBAN" title="voir un RIB pour retrouver l\'IBAN" required="yes"/><br/>'
            o += '<input class="txt" type="text" name="bic" placeholder="Code BIC" pattern="[A-Z0-9]{8,11}" title="pour vérification seulement" required="yes"/><br/>'
            o += '<input class="txt" type="text" name="ssid" placeholder="[Optionel] Numéro de sécurité sociale"/><br/>'
            o += '<input class="txt" type="text" name="dname" placeholder="[Optionel] Nom affiché de marchand"/><br/>'
            o += '<input class="txt" type="password" name="pw" placeholder="Mot de passe" title="de plus de 4 caractères" required="yes"/><br/>'
            o += '<input class="txt" type="password" name="pw2" placeholder="Confirmation de mot de passe" required="yes"/><br/>'
            o += '<input class="txt" type="checkbox" name="read" title="j\'ai lu les avertissements (CGU) ci contre" required="yes"/>'
            o += '<input class="sh" type="submit" value="S\'enregistrer"/>\n'
            o += '</form>\n'
            o += '</div>'
            o += '<div id="rcol">'
            o += '<form method="post">\n'
            o += '<input class="txt" type="text" name="req" placeholder="" title="tapez un nom de marchand ou un code marchand" required="yes"/>'
            o += '<input class="sh" type="submit" value="Recherche" title="code marchand"/> '
            o += '</form>\n'
            if listcm:
                for x in listcm:
                    o += '<h2><a class="mono" href="./%s">%s</a> <a class="name" href="./%s">%s</a></h2>' % (x[0], x[0], x[0], x[1])
            else:
                o += help_register() 
            o += '</div>'
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
            if t[_PUBN] != '': o += '<b class="bigorange" title="Nom affiché de marchand">\"%s\"</b>' % t[_PUBN]
            total = re.sub('€', '', total)
            data = '%s?%06.2f€' % (cm, float(total)) if total != '' else cm
            o += '<p title="...code marchand \'%s\' en QRcode">%s</p>\n' % (data, QRCode(data=data).svg(100, 50, 12, data))    
            if t[_PBK1] != '': o += 'Public Key: <p title="Pulic Key">%s<br/>%s <b>%s</b></p>' % (t[_PBK1], t[_PBK2][:-6], t[_PBK2][-6:])
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
            o += '<p>IBAN : <b class="green">%s</b></p>' % format_iban(t)            
            o += '<p>BIC : <b class="green">%s</b></p>' % t[_CBIC]            
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
            
            o += '<table title="historique des opérations"><tr><th width="15"> </th><th width="150">Date</th><th width="20">+/-</th><th width="250">Opération</th><th width="120">Signature</th><th width="100">Montant</th></tr>'
            if cm.encode('utf8') in dtrx.keys():
                t = dtrx[cm].decode('utf8').split('/')
                n = 0
                for x in t:
                    dat, dest = time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(float(x))), ''
                    l = dtrx['%s/%s' % (x,cm)].decode('utf8').split('/')
                    if l[0].encode('utf8') in dusr.keys():
                        t1 = dusr[l[0]].decode('utf8').split('/')
                        dest = t1[_PUBN]
                    val = '%6.2f €' % float(int(l[1])/100) if re.match(r'\d+$', l[1]) else l[1] 
                    n += 1 
                    o += '<tr><td class="num">%04d</td><td>%s</td><td>-</td><td>%s [%s]</td><td><p class="mono">%s...</p></td><td align="right">%s</td></tr>' % (n, dat, l[0], dest, l[3][:16], val)
                        
            o += '</table>\n'              
            o += '</div>'
    o += '</div>'
    return o + footer() + '</html>'

def text_particulier():
    return """Déposez pour encaissement à votre banque tout <a href="specimen">chèque</a> <a class="ppc">Ping-Pong&nbsp;</a> imprimé. Vérifiez à tout moment sa validité avec toute application mobile qui flash les QRcodes. <a href="login">Inscrivez vous</a> pour obtenir votre <i>code marchand</i> et recevoir des chèques numériques. Plus besoin de vous déplacer, tout est transmis à votre banque. Pour émettre des chèques <a class="ppc">Ping-Pong&nbsp;</a>, utilisez l'application gratuite (bientôt disponible) pour <i>iPhone</i>. Crééz vos clés (déconnecté de l'Internet) et demandez un certificat à votre banquier afin qu'il associe votre numéro de compte à vos clés. Vous pouvez alors payer avec votre téléphone tout autre particulier, commerçant ou administration, même par Internet.<br/> 
Pas besoin de <i>cartes de crédit</i> (<i>CB</i>, <i>Visa</i>, <i>Mastercard</i>). Nous proposons un mécanisme de virement interbancaire automatisé (SEPA CT), sans passer par <i>Bitcoin</i>, sans puce NFC, sans vous géolocaliser, et sans vous inonder de publicités.
"""
def text_prix():
    return """C'est simplement gratuit !
L'investissement pour ce service est très faible, aucun terminal de paiement à développer, aucune carte, ni puce à produire, aucune publicité, ni structure commerciale couteuse. L'authentification forte des utilisateurs est directement assurée par leur smartphone, sans NFS. Les signatures numériques sont basées sur un algorithme fiable et reconnu; ECDSA-521P et les noeuds des serveurs sont conçus sur une distribution Linux+Apache épurée et sécurisée. La maintenance/recherche en sécurité/cryptographie est financée par des aides publiques de programmes de recherche et soutenue par des partenaires académiques.<br/>
Ainsi, la très importante économie réalisée permet de proposer aux citoyens, particuliers ou commerçants, un service de paiement numérique gratuit. Une cotisation annuelle de 3€65 est demandée (un centime par jour), pour la fondation <a href="http://cupfoundation.net">⊔FOUNDATION</a>. Face aux grands groupes spécialisés dans la monétique et disposant de moyens gigantesques de communication, notre petite structure ne peut offrir <a class="ppc">Ping-Pong&nbsp;</a> que si les internautes le demandent, l'utilisent et le font savoir sur le Net.
Pour autant, la <b>qualité de service et la sécurité</b> ne sont jamais impactées par ce prix.
"""

def text_commercant():
    return """Vous êtes les plus avantagés, car <a class="ppc">Ping-Pong&nbsp;</a> n'impose aucun terminal de paiement et ne demande aucune commission quels que soient le nombre de transactions et leur fréquence. Vous êtes même libres d'offrir à vos clients des avantages compte tenu des commissions <i>CB</i> évitées. Bien entendu, <i href="login">l'inscription</i> est requise pour avoir votre <i>code marchand</i> et le nom public que vous désirez donner à votre commerce. Si un client vous donne un chèque <a class="ppc">Ping-Pong&nbsp;</a> imprimé, un simple scan du QRcode valide la transaction, mais le plus souvent, elle est directement envoyée à votre banque depuis le téléphone du client parallèlement à votre ordinateur de caisse.
Pensez à avertir votre clientèle (autocollants disponibles gratuitement en nous contactant), que vous offrez un service de paiement <a class="ppc">Ping-Pong&nbsp;</a>.
"""

def text_banque():
    return """Nous sommes vos partenaires pour offrir un moyen de paiement numérique à tous vos clients. Pour les clients non encore inscrits, le chèque  
<a class="ppc">Ping-Pong&nbsp;</a> imprimé est traité comme tout autre chèque avec saisie manuelle du numéro de compte au dos et  le simple flash du QRcode lance la transaction SEPA, sans erreur possible de somme manuscriptes. Pour vos clients inscrits, tout est numérisé et automatisé à partir de l'instant où l'identité numérique du client associée à son compte a été certifiée par un des conseillers financiers. L'impression du chèque PDF et son dépos en banque est inutile. <a class="ppc">Ping-Pong&nbsp;</a> fait diminuer l'usage des chèques papiers (cout de environ 30€/an/client) et donc des économies plus importantes que le baisse éventuelle de versement du GIE à votre agence, en fonction du montant d'opération CB, qui lui aussi diminue à l'usage de <a class="ppc">Ping-Pong&nbsp;</a>. 
"""

def text_administration():
    return """En plus d'être un moyen de paiement numérique, <a class="ppc">Ping-Pong&nbsp;</a> est une solution de création d'une identité numérique citoyenne. Une simple validation <a class="ppc">Ping-Pong&nbsp;</a> par un agent adminnistratif habilité, avec présence physique obligatoire et papiers d'identités, permet de certifier de l'unicité du citoyen (personne ne peut disposer de deux identités valides). L'identité numérique peut servir à de futures opérations de vote par Internet (non opérationel en 2013) et au déploiement d'une monnaie dédié aux <i>biens immatériels</i> (voir <a href="http://cupfoundation.net">⊔FOUNDATION</a>). Chaque citoyen créant seul et déconnecté du Net, son jeu de clé cryptographique, aucun tiers, même un agent de l'Etat ne peux usurper son identité numérique. La perte ou le vol du téléphone implique simplement de repasser l'enregistrement administratif.
"""

def text_securite():
    return """L'argument <i>sécurité</i> est avancé par toutes les solutions <i>Visa</i>, <i>Mastercard</i>, <i>Paypal</i>, <i>Gemalto</i>, ou <i>Google wallet</i> alors même que leur sécurité réelle reste très faible par rapport à l'état de l'art en cryptographie. Cette situation est volontaire pour justifier, proposer et vendre des services et contrats d'assurance inclus dans les frais de gestion. Votre numéro de carte (+ date d'expiration + cryptogramme) peut se retrouver facilement sur un marché frauduleux. Ces organismes gèrent en plus à votre place, votre mot de passe et votre PIN, donc leurs serveurs sont la cible d'attaques. Avec <a class="ppc">Ping-Pong&nbsp;</a>, l'utilisateur choisit son <i class="red0">alpha-pin</i> seul, chez lui, déconnecté de l'<i>Internet</i>, ni le banquier, ni l'opérateur téléphonique, ni l'Etat ne peut le retrouver. Il faudrait en plus voler physiquement le téléphone pour faire une transaction car un seul équipement n'est associé au même compte. De plus, le réseau de noeuds <a class="box">ping-pong&nbsp;</a> est fortement distribué si bien qu'il est impossible de s'attaquer au réseau entier au même moment. Enfin, seul votre conseiller financier à une vue sur les opérations effectuées et il ne gère qu'un nombre limité de comptes. Il n'y a donc pas de groupe d'administrateurs informatique ayant un pouvoir d'accès à une base de données centralisée. A l'inverse, <i>Visa</i> et <i>Mastercard</i> doivent protéger un mot de passe maître au niveau mondial. Les cartes RFID/NFC pour de petites transactions sont très facilement piratées avec un simple lecteur qui scanne les poches des gens dans une foule alors qu'avec <a class="ppc">Ping-Pong&nbsp;</a>, même pour acheter une baguette de pain, vous devez saisir votre <i class="red0">alpha-pin</i> de quatre caractères sur votre smartphone. La transaction complète <a class="ppc">Ping-Pong&nbsp;</a> s'effectue entre une et cinq secondes selon la dextérité des intervenants."""

def text_ethique():
    return """
De même que l'utilisation d'un billet de banque est gratuit, un paiement à l'aire du numérique doit aussi être gratuit. Ce sont les ordinateurs qui travaillent et ils ont été ammortis par d'autres activités. Nous restons une très petite équipe, en contact privilégier avec le milieu académique et recherche en cryptographie et sécurité informatique, afin de maintenir une offre de qualité. Nous pensons que l'arrivée du numérique ne doit pas créer de nouveaux services complexes, artificiels et financés par le citoyen. Dans le pur état d'esprit de l'Internet à sa conception, chacun a le droit de donner ou recevoir de l'argent par un moyen électronique, sans verser une commision, ni aux banques, ni aux opérateurs de télécommunication, ni aux groupes de la grande distribution. La petite contribution que nous demandons (3,65€/an TTC) permet justement de maintenir une fondation garante de la protection de ce droit, independamment de l'Etat. Parce que l'<i>Internet</i> est un bien commun, offrir au citoyen un moyen de paiement gratuit, ouvert et sécurisé est simplement une <b>nouvelle exigence démocratique</b>."""

def text_propos():
    return """Notre métier initial est la recherche en informatique. Historiquement, nous travaillons avec des industriels de l'<i>aéronautique</i> et des académiques du domaine du <i>temps réel embarqué critique</i>. Bien que <a class="ppc">Ping-Pong&nbsp;</a> utilise des algorithmes cryptographiques et des protocoles éprouvés, nous sommes principalement sensibles à la sécurité informatique du système complet. Nos développements sont obligatoirement open-source pour rassurer les utilisateurs et nos clients et pour nous décharger d'un quelconque secret à protéger.<br/>Notre petite structure est en pleine phase de recrutement sur toute la France. <a href="mailto:contact@pingpongcash.net">Contactez nous</a> pour savoir si nos besoins peuvent correspondre à vos compétences, votre expérience et vos motivations.Nous envisageons à terme une internationalisation, avec le support de taux de change entre monnaies, mais nos efforts se concentrent actuellement sur la couverture de <a class="ppc">Ping-Pong&nbsp;</a> en €, en France, puis en Europe (zone SEPA).
"""


def index_html(nb):
    "_"
    today = '%s' % datetime.datetime.now()
    o = '<?xml version="1.0" encoding="utf8"?>\n<html>\n' + favicon() + style_html()
    o += '<a href="http://pingpongcash.net"><img title="Enfin un moyen de paiement numérique, simple, gratuit et sécurisé !" src="%s"/></a>\n' % get_image('www/header.png')
    o += '<p class="alpha" title="still in security test phase!">Beta</p>'
    data = 'pingpongcash.net/%s' % __acm__ 
    o += '<a class="qr" href="http://%s" title="...notre code marchand \'%s\'">%s</a>\n' % (data, data, QRCode(data=data).svg(10, 10, 4))    
    o += '<p class="stat">%s inscrits | %s transactions</p>' % (nb[0].decode('ascii'), nb[1].decode('ascii'))
    #o += '<p>Enregistrement <a href="login">ici</a></p>\n'

    o += '<p><i>Juin 2013:</i> L\'<a href="login">inscription</a> sur le serveur est ouverte. Nous offons un petit chèque symbolique aux premiers inscrits. En revanche, pour payer avec <a class="ppc">Ping-Pong&nbsp;</a>, il faut attendre la sortie de l\'application mobile. La version <i>iOS</i> pour <i>iPhone</i> est actuellement en phase de test. <a href="mailto:contact@pingpongcash.net">Contactez nous</a> pour participer.</p>'

    o += '<div id="wrap">'
    o += '<div id="c1"><h1>Particulier</h1><p>%s</p></div>' % text_particulier()
    o += '<div id="c2"><h1>Commerçant</h1><p>%s</p></div>' % text_commercant()
    o += '<div id="c3"><h1>Banque</h1><p>%s</p></div>' % text_banque()
    o += '<div id="c4"><h1>Administration</h1><p>%s</p></div>' % text_administration()
    o += '</div>'
    o += '<div id="wrap">'
    o += '<div id="c1"><h1>Prix</h1><p>%s</p></div>' % text_prix()
    o += '<div id="c2"><h1>Sécurité</h1><p>%s</p></div>' % text_securite()
    o += '<div id="c3"><h1>Ethique</h1><p>%s</p></div>' % text_ethique()
    o += '<div id="c4"><h1>A propos</h1><p>%s</p></div>' % text_propos()
    o += '</div>'
    return o + footer() + '</html>'

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
    #db = '/cup/%s/usr.db' % __app__
    #d = dbm.open(db[:-3], 'c')
    #d['to2TyF'] = re.sub('CMCIFR29', 'CMCIFR2A', d['to2TyF'].decode('utf8'))
    #d['to2TyF'] = d['TOTO'].decode('utf8')
    #del(d['TOTO'])
    #d.close()

def same_bic(d, biban, siban):
    "_"
    bs = d[biban].decode('utf8').split('/')
    ps = d[siban].decode('utf8').split('/')
    return bs[1] == ps[1]

def smail(dest, content):
    s = smtplib.SMTP('pingpongcash')
    s.sendmail ('dudule@pingpongcash.net', [dest], content)
    s.quit()

def old_transaction (d, msg, epoch, s_biban, s_siban, val, s_sig): # a enlever!
    "_"
    o, biban, siban, sig = 'Error:', bytes(s_biban, 'ascii'), bytes(s_siban, 'ascii'), bytes(s_sig,'ascii')
    if biban in d.keys():
        pb = d[biban].decode('utf8').split('/')
        if '%s/%s' % (epoch, s_biban) in d.keys():
            o += 'already send'
        elif True: #verify(RSA_E, b64toi(pb[_PK_].encode('ascii')), msg, sig):
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
_PAT_INCOME_ = r'total=(\d{3}\.\d{2})&income=Editer une facture$'
_PAT_CHPWD_  = r'name=([^&/]{2,40}@[^&/]{2,30}\.[^&/]{2,10})&pw=(\S{4,30})&pw1=(\S{4,30})&pw2=(\S{4,30})&new=Changer votre mot de passe$'
_PAT_REG_    = r'first=([^&/]{3,80})&last=([^&/]{3,80})&name=([^&/]{2,40}@[^&/]{3,40})&iban=([a-zA-Z\d ]{16,38})&bic=([A-Z\d]{8,11})&ssid=([^&/]{,50})&dname=([^&/]{,100})&pw=([^&]{2,20})&pw2=([^&]{2,20})&read=on$'
_PAT_PUBKEY_ = r'PK/1/(([^&/]{2,40}@[^&/]{2,30}\.[^&/]{2,10})/([^/]{80,100})/([^/]{80,100}))/(\S{160,200})$'
_PAT_TRANS_  = r'(TR|VD)/1/((\d{10})/([^/]{6})/([^/]{4,60}|[^/]{6})/([A-Za-z]{5}|\d{5}))/(\S{160,200})/(\d{5})/(.{,160})$'
_PAT_AGENCY_ = r'AG/(([^/]{6})/(\d{5}/\d{5})/([^/]{,40}/[^/]{,60}/\d{5}/[^/]{,60}/\d{10}/[^/]{,60}))/(\S{160,200})$'
_PAT_VERIF_  = r'((\d{10})/([^/]{6})/([^/]{4,60}|[^/]{6})/(\d{5}))/(\S{160,200})$'
_PAT_LIST_   = r'LD/(([^/]{6})/([\d-]{10}))/(\S{160,200})$'
_PAT_REQ_    = r'req=(.{1,200})$'
_PAT_SECURL_ = r'([^&/]{2,40}@[^&/]{2,30}\.[^&/]{2,10})&(\S{40,50})$'
_PAT_RESET_  = r'name=([^&/]{2,40}@[^&/]{2,30}\.[^&/]{2,10})&id=([^&]{40,50})&pw1=(\S{4,30})&pw2=(\S{4,30})$'
_PAT_PRINT_  = r'((\d{10})/(\S{6}))$'

def transaction_match(dusr, dtrx, gr):
    "_"
    o = ''
    today = '%s' % datetime.datetime.now()
    trvd, msg, epoch, src, dst, val, sig, efv = gr[0], gr[1], gr[2], gr[3], gr[4], gr[5], gr[6], gr[7] 
    if src.encode('ascii') in dusr.keys():
        tb, k = dusr[src].decode('utf8').split('/'), ecdsa()
        k.pt = Point(curve_521, b64toi(tb[_PBK1].encode('ascii')), b64toi(tb[_PBK2].encode('ascii')))
        if k.verify(sig, msg):
            if tb[_STAT] in ('X', 'Y'): return 'not allowed !'
            if dst.encode('utf8') in dusr.keys(): 
                ts = dusr[dst].decode('utf8').split('/')
                if trvd == 'VD' and tb[_STAT] == 'A' and ts[_STAT] == 'X': ts[_STAT] = 'B'
                if src != dst:
                    dusr[src], dusr[dst] = '/'.join(tb), '/'.join(ts)            
                if trvd == 'VD' and tb[_STAT] == 'A':
                    a = '@'+dst
                    if a.encode('utf8') in dusr.keys():
                        if src.encode('ascii') not in dusr[a].decode('utf8').split('/'): 
                            dusr[a] = dusr[a] + b'/' + src.encode('ascii')
                    else:
                        dusr[a] = src  
            dtrx['__N'] = '%d' % (int(dtrx['__N']) + 1)
            #if re.match('\d{5}$',
            dtrx['%s/%s' % (epoch, src)] = '/'.join([dst, val, efv, sig])
            dtrx[src] = dtrx[src] + b'/' + epoch.encode('ascii') if src.encode('ascii') in dtrx.keys() else epoch
            x, tx = '%s/%s' % (today[:10], tb[_NBNK]), '/'.join([epoch, src])
            dtrx[x] = dtrx[x] + b'/' + tx.encode('ascii') if x.encode('ascii') in dtrx.keys() else tx
        else:
            o = 'Wrong signature!'
    else:
        o = 'unknown cm'
    return o

def agency_match(dusr, dags, gr):
    "_"
    o = ''
    msg, src, key, val = gr[0], gr[1], gr[2], gr[3] 
    if src.encode('ascii') in dusr.keys():
        ta = dusr[src].decode('utf8').split('/')
        if ta[_STAT] == 'A':
            if key.encode('ascii') not in dags.keys():
                dags['__N'] = '%d' % (int(dags['__N']) + 1)
            dags[key] = val        
        else:
            o = 'operation not allowed'
    else:
        o = 'user not known'
    return o

def req_match(dusr, dags, gr):
    "_"
    req, r, n = gr[0], {}, len(gr[0])
    for x in dusr.keys():
        if re.match('\w{6}$', x.decode('utf8')):
            t = dusr[x].decode('utf8').split('/')
            a, b = x.decode('utf8'), t[_PUBN]
            if a == req or b == req: r[a] = (1, b)
            elif a[:n] == req or b[:n] == req: r[a] = (2, b)
            elif a[:n].lower() == req.lower() or b[:n].lower() == req.lower(): r[a] = (3, b)
            else: r[a] = (4, b)
    return [(a[0],a[2]) for a in sorted([(y, r[y][0], r[y][1]) for y in r], key=operator.itemgetter(1))]

def listday_match(dusr, dtrx, gr):
    "_"
    o = ''
    msg, src, dat, sig = gr[0], gr[1], gr[2], gr[3]
    if src.encode('ascii') in dusr.keys(): 
        t, k = dusr[src].decode('utf8').split('/'), ecdsa()
        pk1, pk2, status = t[_PBK1], t[_PBK2], t[_STAT] 
        k.pt = Point(curve_521, b64toi(pk1.encode('ascii')), b64toi(pk2.encode('ascii')))
        if status in ('A','B'):
            if k.verify(sig, msg):
                x = '%s/%s' % (dat, t[_NBNK])
                if x.encode('ascii') in dtrx.keys():
                    l = dtrx[x].decode('utf8').split('/')
                    o = 'Date:%s\n' % dat
                    for a in range(len(l)//2):
                        src = l[2*a+1]
                        y = dusr[src].decode('utf8').split('/')
                        acc = '%s' % b64toi(bytes(y[_IBAN],'ascii'))
                        z = '%s/%s' % (l[2*a], l[2*a+1])
                        he =  time.strftime('%H:%M:%S', time.localtime(float(l[2*a])))
                        j = dtrx[z].decode('utf8').split('/')
                        bnk2, acc2 = '?'*14, '?'*10
                        if j[0].encode('utf8') in dusr.keys():
                            v = dusr[j[0]].decode('utf8').split('/')
                            acc2 = '%s' % b64toi(bytes(v[_IBAN],'ascii'))
                            bnk2 = 'FR76%s' % b32toi(bytes(v[_NBNK][2:],'ascii'))
                        val = '%6.2f €' % float(int(j[1])/100) if re.match(r'\d+$', j[1]) else j[1]  
                        o += '%s %s[%s]->%30s[%s%s] %s...\t%s\n' % (he, l[2*a+1], acc, j[0], bnk2, acc2, j[3][:10], val)
                else:
                    o = 'no operation for this day'
            else:
                o = 'bad signature listday'
        else:
            o = 'not allowed'
    else:
        o = 'unknown user'
    return o

def verif_match(dusr, gr):
    "_"
    o = ''
    msg, epoch, src, dst, val, sig = gr[0], gr[1], gr[2], gr[3], gr[4], gr[5]
    if src.encode('ascii') in dusr.keys(): 
        t, k = dusr[src].decode('utf8').split('/'), ecdsa()
        pk1, pk2 = t[_PBK1], t[_PBK2] 
        k.pt = Point(curve_521, b64toi(pk1.encode('ascii')), b64toi(pk2.encode('ascii')))
        if not k.verify(sig, msg):
            o = 'bad signature verif'
    else:
        o = 'unknown user'
    return o

def do_sepa(dusr, gr):
    "_"
    o = ''
    msg, epoch, src, dst, val, sig = gr[0], gr[1], gr[2], gr[3], gr[4], gr[5]
    if src.encode('ascii') in dusr.keys(): 
        t = dusr[src].decode('utf8').split('/')
        o = 'SEPA CREDIT TRANSFER (share mode)\n\n'
        o += 'Status:\t\t%s\n' % 'Validated'
        o += 'Amount(€):\t%s\n' % (int(val)/100)
        o += 'Date:\t\t%s\n' % time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(float(epoch)))
        o += 'Debit Account:\t[%s] %s %s (%s)\n' % (src, t[_FRST], t[_LAST], t[_PUBN])
        o += 'Debit IBAN:\t%s\n' % format_iban(t)
        s, ib = '[] (%s)' % dst, ' - IBAN Unknown before deposit -'
        if dst.encode('utf8') in dusr.keys(): 
            t = dusr[dst].decode('utf8').split('/')
            ib = 'FR76%d%012d' % (b32toi(bytes(t[_NBNK][2:],'ascii')), b64toi(bytes(t[_IBAN],'ascii')))
            s = '%s %s (%s) %s\n' % (dst, t[_FRST], t[_LAST], t[_PUBN]) 
        o += 'Credit Account:\t%s\n' % s
        o += 'Credit IBAN:\t%s\n' % ib
        o += 'Proof Message:\t%s\n' % msg
        o += 'Public Key :\n%s\n%s\n%s\n%s\n' % (t[_PBK1][:44], t[_PBK1][44:], t[_PBK2][:44], t[_PBK2][44:])        
        o += 'ECDSA-P521 Signature:\n%s\n%s\n%s\n\n' % (sig[:59], sig[59:118], sig[118:])
        o += 'Any question:\tcontact@pingpongcash.net\n'
    return o

def pubkey_match(dusr, gr):
    "_"
    o = ''
    today = '%s' % datetime.datetime.now()
    raw, mail, pk1, pk2, sig = gr[0], gr[1], gr[2], gr[3], gr[4] 
    if mail.encode('utf8') in dusr.keys(): 
        t, k = dusr[dusr[mail]].decode('utf8').split('/'), ecdsa()
        k.pt = Point(curve_521, b64toi(pk1.encode('ascii')), b64toi(pk2.encode('ascii')))
        msg = '/'.join([today[:10], t[_PAWD], raw])
        if k.verify(sig, msg):
            cm1, cm = pk2[-6:], dusr[mail] 
            if cm1.encode('utf8') not in dusr.keys():
                dusr[mail] = cm1
                dusr[cm1] = dusr[cm]
                cm = cm1
            t = dusr[cm].decode('utf8').split('/')
            if t[_PBK1] == '': 
                t[_PBK1], t[_PBK2] = pk1, pk2 
                dusr[cm] = '/'.join(t)
                cid = '%s/%s' % (t[_NBNK], t[_IBAN])
                dusr[cid] = dusr[cid].decode('ascii') + '/%s' % cm if cid.encode('ascii') in dusr.keys() else cm
            else:
                o = 'PubKey already exists'
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
        if mail.encode('utf8') in dusr.keys(): o = 'this e-mail is already registered!'
        else:
            while True:
                epoch = '%s' % time.mktime(time.gmtime())
                cid = compact(gr[3])
                k = h6(cid + '/' + epoch[:-2])
                if k not in dusr.keys(): break
            dusr['__N'] = '%d' % (int(dusr['__N']) + 1)
            dusr[mail] = k
            #dusr[cid] = dusr[cid] + bytes('/%s' % k, 'ascii') if cid.encode('ascii') in dusr.keys() else k
            st = 'A' if mail == __email__ else 'X'
            dusr[k] = '/'.join([  
                    st,             #_STAT
                    '',             #_LOCK
                    epoch[:-2],     #_DREG
                    mail,           #_MAIL 
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
    if mail.encode('utf8') in dusr.keys():
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
    dbs = ('trx', 'ags', 'bic', 'usr')
    init_dbs(dbs)
    (raw, way) = (environ['wsgi.input'].read(), 'post') if environ['REQUEST_METHOD'].lower() == 'post' else (urllib.parse.unquote(environ['QUERY_STRING']), 'get')
    base = environ['PATH_INFO'][1:]
    base1 = urllib.parse.unquote(environ['REQUEST_URI'])[1:]
    [dtrx, dags, dbic, dusr] = [dbm.open('/cup/%s/%s' % (__app__, b), 'c') for b in dbs]
    nb = [dusr['__N'], dtrx['__N']]
    if way == 'post':
        arg = urllib.parse.unquote_plus(raw.decode('utf8'))
        if reg(re.match(_PAT_LOGIN_, arg)):
            #smail ('pelinquin@gmail.com', 'LOGIN OK \n')
            cm, res = login_match(dusr, reg.v.groups())
            if cm: o, mime = front_html(dusr, dtrx, cm.decode('ascii')), 'text/html; charset=utf8'
            else: o += res
        elif reg(re.match(_PAT_LOST_, arg)):
            url = itob64(int('0x' + hashlib.sha256(os.urandom(32)).hexdigest(), 16))
            today = '%s' % datetime.datetime.now()
            dusr ['%' + reg.v.group(1)] = url + b'/' + bytes(today[:10], 'ascii')
            o = 'url: %s %s' % (url.decode('ascii'), len(url.decode('ascii')))
        elif reg(re.match(_PAT_CHPWD_, arg)):
            cm, res = login_match(dusr, reg.v.groups())
            if cm: o, mime = front_html(dusr, dtrx, cm.decode('ascii'), False, '', 'votre mot de passe a été changé!'), 'text/html; charset=utf8'
            else: o += res
        elif reg(re.match(_PAT_REG_, arg)):
            k, res = register_match(dusr, reg.v.groups())
            if k: o, mime = front_html(dusr, dtrx, k), 'text/html; charset=utf8'
            else: o += res
        elif reg(re.match(_PAT_INCOME_, arg)):
            o = 'facture! %s' % base
            o, mime = front_html(dusr, dtrx, base, True, reg.v.group(1), 'Facture'), 'text/html; charset=utf8'
        elif reg(re.match(_PAT_PUBKEY_, arg)):
            res = pubkey_match(dusr, reg.v.groups())
            if res: o += res
            else: o = 'PUBKEY OK' 
        elif reg(re.match(_PAT_TRANS_, arg)):
            res = transaction_match(dusr, dtrx, reg.v.groups())
            if res: o += res
            else: o, mime = pdf_digital_check(dusr, dtrx, dags, reg.v.groups()), 'application/pdf'
        elif reg(re.match(_PAT_AGENCY_, arg)):
            smail ('pelinquin@gmail.com', 'LOGIN OK \n')
            res = agency_match(dusr, dags, reg.v.groups())
            if res: o += res
            else: o = 'AGENCY OK' 
        elif reg(re.match(_PAT_LIST_, arg)):
            o = listday_match(dusr, dtrx, reg.v.groups())
        elif reg(re.match(_PAT_REQ_, arg)):
            v = req_match(dusr, dtrx, reg.v.groups())
            o, mime = front_html(dusr, dtrx, listcm=v), 'text/html; charset=utf8'
        elif reg(re.match(_PAT_RESET_, arg)):
            gr = reg.v.groups()
            a = '%' + gr[0]
            o += 'Something wrong !'
            if a.encode('utf8') in dusr:
                t = dusr[a].decode('utf8').split('/')
                if t[0] == gr[1] and gr[2] == gr[3]:
                    del(dusr[a])
                    cm = dusr[gr[0]]
                    t = dusr[cm].decode('utf8').split('/')
                    t[_PAWD] = h10(gr[2])
                    dusr[cm] = '/'.join(t)                    
                    o, mime = front_html(dusr, dtrx, cm.decode('ascii'), False, '', 'votre mot de passe a été changé!'), 'text/html; charset=utf8'
        else:
            o += 'not valid args %s' % arg
    else:
        log(raw, environ['REMOTE_ADDR'])
        if raw.lower() == '_update':
            o, mime = app_update(environ['SERVER_NAME']), 'text/html'
        elif raw.lower() == '_log':
            o = open('/cup/%s/log' % __app__, 'r', encoding='utf8').read()                
        elif raw.lower() in ['_%s' % x for x in dbs]: # Just for debug!
            d, o = dbm.open('/cup/%s/%s' % (__app__, raw.lower()[1:])), ''
            for x in d.keys(): o += '%s -> %s\n'  % (x.decode('utf8') , d[x].decode('utf8'))
            d.close()
        elif raw.lower() in ['_reset_%s' % x for x in dbs]: # Do not allow that in production!
            #os.remove('/cup/%s/%s.db' % (__app__, raw.lower()[7:]))
            #o = 'reset database %s OK' % raw.lower()[7:]
            o = 'reset database %s NOT ALLOWED !' % raw.lower()[7:]
        elif base == '':
            o, mime = index_html(nb), 'text/html; charset=utf8'
        elif base == 'login': # public pages
            o, mime = front_html(dusr, dtrx), 'text/html; charset=utf8'
        elif base == 'specimen': # public pages
            here = os.path.dirname(os.path.abspath(__file__))
            o, mime = open('%s/www/specimen.pdf' % here, 'rb').read(), 'application/pdf'
        elif reg(re.match(_PAT_VERIF_, base1)):
            res = verif_match(dusr, reg.v.groups())
            if res: o += res
            else: o = do_sepa(dusr, reg.v.groups())
        elif reg(re.match(_PAT_SECURL_, base)):
            o, mime = change_html(reg.v.group(1), reg.v.group(2), dusr), 'text/html; charset=utf8'
        elif reg(re.match(_PAT_PRINT_, base)):
            o += 'problem !'
            gr = reg.v.groups()
            if gr[0].encode('utf8') in dtrx:
                t = dtrx[gr[0]].decode('utf8').split('/')
                g = ['TR', '/'.join([gr[0]] + t[0:2]), gr[1], gr[2], t[0], t[1], '/'.join(t[3:5])]
                o, mime = pdf_digital_check(dusr, dtrx, dags, g), 'application/pdf'
        #elif reg(re.match(r'zz(.)', base)): o = 'é %s' % urllib.parse.unquote(environ['REQUEST_URI'])
        else:
            if base.encode('ascii') in dusr.keys(): o, mime = front_html(dusr, dtrx, base, True, raw, 'Facture'), 'text/html; charset=utf8'
            else: o += 'Request not valid! %s' % base1
    dbic.close()
    dags.close()
    dtrx.close()
    dusr.close()
    start_response('200 OK', [('Content-type', mime)])
    return [o if mime == 'application/pdf' else o.encode('utf8')] 

def favicon():
    "_"
    return '<link rel="shortcut icon" type="www/image/png" href="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAFAAAABQCAIAAAABc2X6AAAABmJLR0QA/wD/AP+gvaeTAAAAoklEQVR4nO3csQ0CMRAAQR6R0wk1URo1UYnpgA4M0iNA65n0kltdankbYxxWcvz1At8muE5wneA6wXWn+fhyO0+m9+vjo8u8a89Wy11YcJ3gOsF1gusE1wmuE1wnuE5wneA6wXWC6wTXCa4TXCe4TnCd4DrBdYLrBNcJrhNcJ7juxYv4ufnL9P+03IUF1wmuE1wnuG7zy0Oc4DrBdYLrBNc9AUj0DSD4QMJ7AAAAAElFTkSuQmCC"/>'

def favicon_svg():
    "_"
    code = '<svg %s n="%s"><path stroke-width="4" fill="none" stroke="Dodgerblue" d="M3,1L3,14L13,14L13,1"/></svg>' % (_SVGNS, datetime.datetime.now())
    tmp = base64.b64encode(code.encode('utf8'))
    return '<link %s rel="shortcut icon" type="image/svg+xml" href="data:image/svg+xml;base64,%s"/>\n' % (_XHTMLNS, tmp.decode('utf8'))

def footer():
    "_"
    return '<div id="footer">Contact: <a href="mailto:contact@pingpongcash.net">contact@pingpongcash.net</a><br/><a href="http://cupfoundation.net">⊔FOUNDATION</a> is registered in Toulouse/France SIREN: 399 661 602 00025</div>'

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
        "The curve of points satisfying y^2 = x^3 + a*x + b (mod p)"
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
    return (1+len("%x" % order))//2 # bytes

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
_B = b'UZU-uWGOHJofkpohoLaFQO6i2nJbmbMV87i0iZGO8QnhVhk5Uex-k3sWUsC9O7G_BzVz34g9LDTx70Uf1GtQPwA'
_GX = b'xoWOBrcEBOnNnj7LZiOVtEKcZIE5BT-1Ifgor2BrTT26oUted-_nWSj-HcEnov-o3jNIs8GFakKb-X5-McLlvWY'
_GY = b'ARg5KWp4mjvABFyKX7QsfRvZmPVESVebRGgXr70XJz5mLJfucple9CZAxVC5AT-tB2E1PHCGonLCQIi-lHaf0WZQ'
_P = b'Af' + b'_'*86
_R = b'Af' + b'_'*42 + b'-lGGh4O_L5Zrf8wBSPcJpdA7tcm4iZxHrrtvtx6ROGQJ'

INFINITY = Point(None, None, None)  
curve_521 = CurveFp(b64toi(_P), -3, b64toi(_B))
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

####### UTILITIES #########

def luhn(num):
    "_"
    s = 0
    for i, c in enumerate('%s' % x):
        ci = int(c)
        s += (1 + 2*(ci-5) if ci>=5 else 2*ci) if i%2 == 0 else ci
    return (s % 10 == 0)

def format_iban(t):
    bnk = 'FR76%010d%013d ' % (b32toi(bytes(t[_NBNK][2:], 'ascii')), b64toi(bytes(t[_IBAN], 'ascii')))
    tiban = ' '.join([bnk[4*i:4*(i+1)] for i in range(7)]) 
    return tiban[:-1]

####### PDF #########

class updf:
    def __init__(self, pagew, pageh, letterw=595, letterh=842, binary=True):
        self.pw, self.ph = pagew, pageh
        self.mx, self.my = 0, 0
        self.binary = binary
        self.i = 0
        self.pos = []
        self.o = b'%PDF-1.4\n%'
    
    def add(self, line):
        self.pos.append(len(self.o))
        self.i += 1
        self.o += bytes('%d 0 obj<<%s>>endobj\n' % (self.i, line), 'ascii')

    def addi(self, img, binary=True):
        self.pos.append(len(self.o))
        tf = open(img, 'rb').read()
        if binary: tf = zlib.compress(tf) 
        fil = '/Filter/FlateDecode' if binary else ''
        self.i += 1
        self.o += bytes('%s 0 obj<</Type/XObject/Subtype/Form/BBox[0 0 500 500]/FormType 1/Length %s%s>>stream\n' % (self.i, len(tf), fil), 'ascii')
        self.o += tf + bytes('endstream endobj\n', 'ascii')

    def adds(self, stream):
        self.pos.append(len(self.o))
        self.i += 1
        if self.binary: stream = zlib.compress(stream) 
        fil = '/Filter/FlateDecode' if self.binary else ''
        self.o += bytes('%d 0 obj<</Length %d%s>>stream\n' % (self.i, len(stream), fil), 'ascii')
        self.o += stream
        self.o += b'endstream endobj\n'

    def ltext(self, tab, r):
        "_"
        o = b'BT '
        for (x, y, ft, sz, s) in tab: 
            s = re.sub('@ppc@', ') Tj .1 .1 .6 rg /F5 %s Tf (Ping-Pong) Tj /F1 %s Tf ( Cash) Tj 0 0 0 rg /F%d %d Tf (' % (sz-1, sz-1, ft, sz), s)
            o += bytes('1 0 0 1 %d %d Tm /F%d %d Tf %s TL ' % (x+self.mx+r[0], r[3]-self.my-y+r[1], ft, sz, 1.2*sz), 'ascii')
            for l in s.split('\n'): o += bytes('(%s) Tj T* ' % (l), 'ascii')
            o = o[:-3]
        return o + b' ET '

    def ctext(self, tab, r):
        "_"
        o = b'BT '
        for (x, y, ft, sz, c, s) in tab: 
            if c == 1: # vertical left
                o += bytes('.8 .8 .8 rg 0 -1 1 0 %d %d Tm /F%d %d Tf (%s) Tj ' % (x+self.mx+r[0], r[3]-self.my-y+r[1], ft, sz, s), 'ascii')
            elif c == 2: # vertical right
                o += bytes('.5 .5 .5 rg 0 1 -1 0 %d %d Tm /F%d %d Tf (%s) Tj ' % (x+self.mx+r[0], r[3]-self.my-y+r[1], ft, sz, s), 'ascii')
            else:
                o += bytes('%s rg 1 0 0 1 %d %d Tm /F%d %d Tf (%s) Tj ' % (c, x+self.mx+r[0], r[3]-self.my-y+r[1], ft, sz, s), 'ascii')
        return o + b' 0 0 0 rg ET '

    def rect(self, x, y, w, h, r=0):
        if r == 0:
            return bytes ('%s %s m %s %s l %s %s l %s %s l h B' %(x, y, x, y+h, x+w, y+h, x+w, y), 'ascii')  
        else:
            return bytes (re.sub('l','m', '%s %s l %s %s %s %s v '*4, 1) % (x+r, y, x, y,  x, y+r, 
                                                                            x, y+h-r, x, y+h, x+r, y+h,
                                                                            x+w-r, y+h, x+w, y+h, x+w, y+h-r,
                                                                            x+w, y+r, x+w, y, x+w-r, y,
                                                                            ), 'ascii') + b'h B'  

    def gen(self, pages, qrt):
        "_"
        ft = (1, 3, 5, 6, 8)
        self.o += b'\xBF\xF7\xA2\xFE\n' if self.binary else b'ASCII!\n'
        self.add('/Type/Catalog/Pages 2 0 R')
        self.add('/Type/Pages/MediaBox[0 0 %d %d]/Count 1/Kids[3 0 R]' % (self.pw, self.ph))
        fonts = '/Font<<' + ''.join(['/F%d %d 0 R' % (f, i+4)  for i,f in enumerate(ft)]) + ' >>'
        ann = '/Annots[%d 0 R %d 0 R %d 0 R]' % (len(ft)+6, len(ft)+7, len(ft)+8) 
        self.add('/Type/Page/Parent 2 0 R%s/Resources<<%s/XObject<</Im1 %d 0 R>>>>/Contents %d 0 R' % (ann, fonts, len(ft)+4, len(ft)+5))
        enc = '/Encoding<</Type/Encoding /Differences[1 %s]>> ' % __e__
        for f in ft: self.add('/Type/Font/Subtype/Type1/BaseFont/%s %s' % (__fonts__[f-1], enc))
        self.addi('%s/www/logo.txt' % os.path.dirname(os.path.abspath(__file__))) 
        o, urlink = b'', []
        for (pa, pc, gr, rect) in pages: o += gr + self.ctext(pc, rect) + self.ltext(pa, rect)
        for (q, h, ur) in qrt:
            o += q
            urlink.append('/Border[0 0 1]/Subtype/Link/C[0 1 1]/A<</URI(http://%s)/Type/Action/S/URI>>/Type/Annot/Rect[%s]/H/I' % (ur, h))
        self.adds(o)
        for ur in urlink: self.add(ur)
        n, size = len(self.pos), len(self.o)
        self.o += functools.reduce(lambda y, i: y+bytes('%010d 00000 n \n' % i, 'ascii'), self.pos, bytes('xref\n0 %d\n0000000000 65535 f \n' % (n+1), 'ascii'))
        self.o += bytes('trailer <</Size %d/Root 1 0 R>>startxref %s\n' % (n+1, size), 'ascii') + b'%%EOF'
        return self.o

def sanity(s):
    __o__ = r'([çáàâäéèêëíìîïóòôöúùûüŷÿ])'
    return re.sub(__o__, lambda m: r'\%03o' % __o__.index(m.group(1)), s)

def pdf_digital_check(dusr, dtrx, dags, gr):
    "_"
    trvd, msg, epoch, src, dst, val, sig, efv, txt = gr[0], gr[1], gr[2], gr[3], gr[4], gr[5], gr[6], gr[7], gr[8]
    #import locale
    #locale.setlocale(locale.LC_TIME, ('fr_FR', 'IS8859-15'))
    date_gen = time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(float(epoch)))
    date_en = time.strftime('%c', time.localtime(float(epoch)))
    tb = dusr[src].decode('utf8').split('/')
    pubname, info1, info2 = '', sanity('Reçu - Receipt - '*10), ''
    info1 = info1[:-3]
    msgraw = msg
    if dst.encode('utf8') in dusr.keys(): 
        ts = dusr[dst].decode('utf8').split('/')
        pubname = ts[_PUBN]
    else:
        dst, msg, pubname = 'X'*6, sanity(msg), sanity(dst)
        bnk = '%s' % b32toi(bytes(tb[_NBNK][2:],'ascii'))
        key = '%s/%s' % (bnk[:5], bnk[5:])
        if key.encode('utf8') in dags.keys():
            info1, info2 = '%s %s - %s - %s' % (tb[_FRST], tb[_LAST], format_iban(tb), tb[_CBIC]), re.sub('/', ' ', sanity(dags[key].decode('utf8')))
    dpubname = pubname + ' ' + '*'*(30-len(pubname))
    if trvd == 'TR':
        if efv != '00000' and int(efv) < int(val):
            v1, v2 = efv[:3], efv[3:]
        else:
            v1, v2 = val[:3], val[3:]
        (vv1, vv2) = ((413, 36, 1, 18, v1), (460, 32, 1, 12, v2)) 
        manu_fr, manu_en = num2word_fr(int(v1), int(v2)), num2word(int(v1), int(v2))
    else:
        v1, v2 = '000', '000'
        manu_fr, manu_en = sanity('Preuve de signature électronique'),'Proof of Digital Signature'
        (vv1, vv2) = ((413, 26, 1, 18, ''), (460, 22, 1, 12, '')) 
    tab = msg.split('/')
    pk1, pk2 = tb[_PBK1], tb[_PBK2]
    page1 = [
        (52, 20, 1, 12, '@ppc@'),
        (195, 154, 1, 12, date_gen),
        vv1, vv2,
        (233, 168, 3, 7, sig[:59]), 
        (233, 176, 3, 7, sig[59:118]), 
        (233, 184, 3, 7, sig[118:]), 
        (233, 203, 3, 7, msg),
        (393, 78, 1, 6, 'http://pingpongcash.net/%s' % src),
        (70, 50, 5, 14, dst), (140, 50, 6, 12, dpubname),
        (10, 69, 6, 11, manu_fr), (10, 79, 3, 8, manu_en),
        (190, 100, 5, 14, src), 
        (266, 100, 6, 12, sanity(tb[_PUBN])), 
        (202, 110, 3, 7, pk1[:44]), (202, 118, 3, 7, pk1[44:]), 
        (202, 126, 3, 7, pk2[:44]), (202, 134, 3, 7, pk2[44:-6]), (362, 134, 6, 7, pk2[-6:]),
        ] 
    rtxt = """Vous trouverez ci dessous un chèque @ppc@,
signé le %s par "%s" de code marchand: %s\n
Vous pouvez vérifier sa validité et l'encaisser en ligne sur l'Internet,
simplement en suivant le lien du large QRcode.Vérifiez que vous êtes bien 
sur le site dont l'adresse commence par : "pingpongcash.net".
Mais vous pouvez aussi l'utiliser comme un chèque classique.
Découpez-le et déposez-le à votre banque après l'avoir signé au verso,
ou bien pliez le petit formulaire de remise ci-joint.\n
Pour payer avec un chèque @ppc@, enregistrez-vous sur le site 
et demandez un certificat @ppc@ à votre conseiller financier.
Il nous contactera au besoin pour valider son agence bancaire.
Ensuite envoyez par e-mail ou imprimez vos chèques @ppc@ émis,
avec obligatoirement le nom du bénéficiaire.
Si enfin votre créancier est déjà enregistré, gardez le chèque comme reçu,
l'encaissement auprès de votre banque est alors automatique.\n
N'hésitez pas à nous poser des questions et à nous faire part de vos remarques.
Merci pour l'utilisation de @ppc@, 
...pour un véritable moyen de paiement numérique citoyen!
\n\n\nwww.pingpongcash.net\nwww.cupfoundation.net\ncontact@pingpongcash.net
""" % (date_gen[:10], tb[_PUBN], src)
    if txt != '': txt = '\n'.join([txt[80*i:80*(i+1)] for i in range(3)]) 
    unmsg = [] if txt == '' else [(10, 510, 1, 8, sanity('Message de l\'acheteur (%s) :' % sanity(tb[_PUBN]) )), (20, 520, 5, 8, sanity(txt))]
    page2 = [(114, 38, 1, 28, '@ppc@'),(75, 120, 1, 9, 'Bonjour %s,' % pubname), (20, 160, 1, 9, sanity(rtxt))] + unmsg
    gray, dodger, bluel = '.7 .7 .7', '.1 .1 .6', '.5 .5 .9'
    sign = (195, 198, 1, 240, '.95 .95 .95', '\001') if trvd == 'TR' else (155, 85, 5, 60, '.9 .9 .9', 'PROOF') 
    eurs = (445, 36, 1, 18, '.1 .2 .7', '\001') if trvd == 'TR' else (408, 38, 1, 20, '.1 .2 .7', val)
    bars = [(325, 118, 1, 120, '.9 .9 .9', '/'), (340, 118, 1, 120, '.9 .9 .9', '/')] if trvd == 'TR' else []
    pagec1 = [
        (52, 29, 5, 6, _COLOR['b'], sanity(_AD1)), (52, 36, 5, 5, _COLOR['b'], sanity(_AD2)), 
        (44, 50, 1, 10, gray, 'PAY:' if trvd== 'TR' else 'TO:'), eurs,
        (155, 100, 1, 10, gray, 'FROM:'), 
        (360, 78, 1, 5, gray, 'Anti-Phishing:'), 
        (155, 154, 1, 8, gray, 'Date:'), 
        (155, 168, 1, 4, gray, 'EC-DSA-521P'),
        (155, 177, 1, 9, gray, 'Digital Signature:'), 
        #(155, 15, 1, 6, gray, 'Enregistrement, aide ou question:'), 
        (250, 11, 5, 8, gray, 'http://pingpongcash.net'),
        (250, 20, 5, 8, gray, 'contact@pingpongcash.net'), 
        (155, 110, 1, 7, gray, 'Public key:'),
        (155, 203, 1, 8, gray, 'Signed message:'),  
        #sign,
        (155, 215, 1, 6, '.05 .46 .8', sanity(info1)), (155, 223, 1, 6, '.05 .46 .8', sanity(info2)), 
        (475, 10, 1, 4, '.8 .7 .9', __digest__.decode('ascii')), 
        ] + bars
    pagec3 = [(70, 40, 1, 64, 1, 'Encart publicitaire'),] 
    pagec2 = [(5, 5, 1, 6, 1, date_en ),(80, 760, 1, 10, 2, 'Signature' ), (53, 816, 1, 10, 2, 'Date' ),
              (19, 816, 1, 10, 2, sanity('Numéro') ), (28, 816, 1, 10, 2, 'de compte' ),
              (20, 570, 1, 7, '.6 .6 .6 ', sanity('Après détachement et encaissement manuel du chèque, il peut être re-imprimé ici: ')),
              (20, 581, 1, 10, '.6 .6 .6 ', 'www.pingpongcash.net/%s/%s' % (epoch, src)),
              (114, 58, 5, 10, bluel, sanity(_AD1)), (114, 69, 5, 10, bluel, sanity(_AD2)), 
              ] 
    url = (urllib.parse.quote('www.pingpongcash.net/%s/%s' % (msgraw, sig)), 'www.pingpongcash.net/%s' % src, 'www.pingpongcash.net/%s/%s' % (epoch,src))
    qr1, qr2, qr3 = QRCode(data=url[0]), QRCode(data=url[1]), QRCode(data=url[2])
    dx1, dy1, w1, h1 = 99, 0, 496, 227
    dx2, dy2, w2, h2 = 0, 600, 496, 227
    dx3, dy3, w3, h3 = 393, 229, 200, 611
    graph1 = bytes('.5 .5 .5 RG 1 1 .9 rg %s %s %s %s re S ' % (dx1, dy1, 496, 227), 'ascii') 
    graph1 +=  b'q .3 .5 .9 rg .22 0 0 .22 20 722  cm /Im1 Do Q '
    graph1 += b'q .9 .5 .1 rg .12 0 0 .12 100 170 cm /Im1 Do Q '
    graph1 += b'q .95 .95 .95 rg .6 0 0 .6 220 -50 cm /Im1 Do Q '    
    graph1 += bytes('.9 .9 .9 rg %s %s %s %s re f 0 0 0 rg ' % (dx1+402, dy1+184, 78, 25), 'ascii')
    cases = '1w 1 1 1 rg .6 .6 .6 RG ' + ' '.join(['10 %d 24 14 re' % (62+14*i) for i in range(11)]) + ' b 40 116 53 100 re 40 36 20 70 re f '
    graph2  = bytes('.9 .9 .9 rg %s %s %s %s re f %s b 0 0 0 rg ' % (0, 0, 99, 227, cases), 'ascii')
    graph3  = bytes('.7 .8 1 RG 1 1 .96 rg %s %s %s %s re B 0 0 0 RG 0 0 0 rg ' % (dx3, dy3, w3, h3), 'ascii')
    pas = 2
    x1, y1, w1, x2, y2, w2 = dx1+17, dy1+14, (61*pas), dx1+420, dy1+80, (29*pas)
    qrt = ( (qr1.pdf(x1, y1+121, pas, True), '%s %s %s %s' % (x1-1, y1-1, x1+w1+2, y1+w1+2), url[0]),
            (qr2.pdf(x2, y2+56, pas), '%s %s %s %s' % (x2-1, y2-1, x2+w2+2, y2+w2+2), url[1]),
            (qr3.pdf(300, 400, pas, False), '%s %s %s %s' % (299, 342, 360, 403), url[2]) )
    pages = ((page1, pagec1, graph1, (dx1, dy1, w1, h1)), 
             (page2, pagec2, graph2, (dx2, dy2, w2, h2)),
             ([], pagec3, graph3, (dx3, dy3, w3, h3)),
             )
    #a = updf(496, 227) # 175mmx80mm
    a = updf(595, 842) # A4
    return a.gen(pages, qrt)

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
    "_"
    def __init__(self, data, mode=None):
        "If mode isn't provided, the most compact QR data type possible is chosen"
        if data.isdigit(): auto_mode = MODE_NUMBER
        elif re.match('^[%s]*$' % re.escape(ALPHA_NUM), data): auto_mode = MODE_ALPHA_NUM
        else: auto_mode = MODE_8BIT_BYTE
        if mode is None:
            self.mode = auto_mode
        else:
            if mode not in (MODE_NUMBER, MODE_ALPHA_NUM, MODE_8BIT_BYTE): raise TypeError("Invalid mode (%s)" % mode)
            if mode < auto_mode: raise ValueError("Provided data can not be represented in mode %s" % mode)
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
                if len(chars) > 1: buffer.put(ALPHA_NUM.find(chars[0]) * 45 + ALPHA_NUM.find(chars[1]), 11)
                else: buffer.put(ALPHA_NUM.find(chars), 6)
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
        buffer.put(len(data), length_in_bits(data.mode, version))
        data.write(buffer)
    total_data_count = 0
    for block in rs_b:
        total_data_count += block.data_count
    if len(buffer) > total_data_count * 8:
        raise DataOverflowError("Code length overflow. Data size (%s) > size available (%s)" % (len(buffer), total_data_count * 8))
    if len(buffer) + 4 <= total_data_count * 8: buffer.put(0, 4)
    while len(buffer) % 8: buffer.put_bit(False)
    PAD0, PAD1 = 0xEC, 0x11
    while True:
        if len(buffer) >= total_data_count * 8: break
        buffer.put(PAD0, 8)
        if len(buffer) >= total_data_count * 8: break
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
        for i in range(len(num) - offset): self.num[i] = num[i + offset]

    def __getitem__(self, index):
        return self.num[index]

    def __len__(self):
        return len(self.num)

    def __mul__(self, e):
        num = [0] * (len(self) + len(e) - 1)
        for i in range(len(self)):
            for j in range(len(e)): num[i + j] ^= gexp(glog(self[i]) + glog(e[j]))
        return Poly(num, 0)

    def __mod__(self, e):
        if len(self) - len(e) < 0: return self
        ratio = glog(self[0]) - glog(e[0])
        num = [0] * len(self)
        for i in range(len(self)): num[i] = self[i]
        for i in range(len(e)): num[i] ^= gexp(glog(e[i]) + ratio)
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
        "Find the most efficient mask pattern"
        min_lost_point, pattern = 0, 0
        for i in range(8):
            self.makeImpl(True, i)
            lost_point = lost_point1(self.m)
            if i == 0 or min_lost_point > lost_point: min_lost_point, pattern = lost_point, i
        return pattern

    def svg(self, ox=0, oy=0, d=2, txt=''):
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

    def pdf(self, ox=0, oy=0, d=10, size=False):
        "_"
        o, mc = b'0 0 0 rg ', self.m_count
        if size:
            o += bytes('BT 1 0 0 1 4 6 Tm /F1 4 Tf (%d) Tj ET ' % self.m_count, 'ascii')
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

def num2word(n, c):
    elm = {1:'one', 2:'two', 3:'three', 4:'four', 5:'five', 6:'six', 7:'seven', 8:'eight', 9:'nine', 10:'ten', 
           11:'eleven', 12:'twelve', 13:'thirteen', 14:'fourteen', 15:'fifteen', 16:'sixteen', 17:'seventeen', 18:'eighteen', 
           19:'nineteen', 20:'twenty', 30:'thirty', 40:'forty', 50:'fifty', 60:'sixty', 70:'seventy', 80:'eighty', 90:'ninety'}
    o, u1, u2, op = '', '' if n == 0 else 'euro' if n == 1 else 'euros', '' if c == 0 else 'cent' if c == 1 else 'cents', ' and '
    q, r = n//100, n%100
    if q > 0:
        o = '%s hundred' % elm[q] 
        if r == 0: o+= ' %s' % u1
        if r>0 or c>0: o += op 
    n -= 100*q
    if n in elm:
        o += '%s %s' % (elm[n], u1)
    else: 
        p, r = (n//10)*10, n%10
        if p in elm:
            o += '%s %s %s' % (elm[p], elm[r], u1)
    if c > 0:
        if n > 0: o += op
        if c in elm:
            o += '%s %s' % (elm[c], u2)
        else: 
            p, r = (c//10)*10, c%10
            o += '%s %s %s' % (elm[p], elm[r], u2)
    return o.title() + ' ' + '-'*(71-len(o))

def cent(n):
    elm = {1:'un', 2:'deux', 3:'trois', 4:'quatre', 5:'cinq', 6:'six', 7:'sept', 8:'huit', 9:'neuf', 10:'dix', 
           11:'onze', 12:'douze', 13:'treize', 14:'quatorze', 15:'quinze', 16:'seize', 17:'dix-sept', 18:'dix-huit', 
           19:'dix-neuf', 20:'vingt', 30:'trente', 40:'quarante', 50:'cinquante', 60:'soixante', 80:'quatre-vingt'}
    op, o = 'et', ''
    if n == 80: o += '%ss' % elm[80]
    elif n in elm: o += '%s' % (elm[n])
    elif n == 71: o += '%s-%s-%s' % (elm[60], op, elm[11])
    elif n in range(22,30): o += '%s-%s' % (elm[20], elm[n-20])
    elif n in range(32,40): o += '%s-%s' % (elm[30], elm[n-30])
    elif n in range(42,50): o += '%s-%s' % (elm[40], elm[n-40])
    elif n in range(52,60): o += '%s-%s' % (elm[50], elm[n-50])
    elif n in range(62,80): o += '%s-%s' % (elm[60], elm[n-60])
    elif n in range(81,100): o += '%s-%s' % (elm[80], elm[n-80])
    elif n%10 == 1: o += '%s-%s-%s' % (elm[n-1], op, elm[1])
    return o

def num2word_fr(n, c):
    o, u1, u2, op = '', '' if n == 0 else 'euro' if n == 1 else 'euros', '' if c == 0 else 'centime' if c == 1 else 'centimes', ' et '
    q, r = n//100, n%100
    ct = 'cents' if r == 0 else 'cent'
    if q > 1: o += '%s %s ' % (cent(q), ct)
    elif q == 1: o += 'cent '
    m = n
    n -= 100*q
    if n > 0: o += '%s ' % cent(n) 
    o += u1
    if c > 0:
        if m > 0: o += op
        o += '%s %s' % (cent(c), u2)
    return o.capitalize() + ' ' + '-'*(71-len(o))

def test_num():
    "max at 494.94€: 73bytes"
    m,s = 0, None
    for e in range(1000):
        for i in range(100):
            x = num2word(e, i)
            if len(x) > m: m,s = len(x),x
            print (x)
    print (m, s)

def test_pdf():
    ele = (55, 100, 1, 20, 'FROM')
    pages = (([ele,], [], b'', (10, 10, 200, 200)), )
    a = updf(595, 842) # A4
    raw = a.gen(pages, [])
    open('toto.pdf', 'bw').write(raw)    

if __name__ == '__main__':
    #test_num()
    test_pdf()

# End ⊔net!
