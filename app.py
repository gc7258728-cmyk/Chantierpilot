# -*- coding: utf-8 -*-
"""ChantierPilot - suivi multichantier pédagogique, données hors du dossier source."""
from __future__ import annotations

import base64
import copy
import hashlib
import io
import json
import math
import os
from pathlib import Path
import re
import sqlite3
import uuid
import warnings
from contextlib import closing
from datetime import date, datetime, timedelta
from html import escape
from zoneinfo import ZoneInfo

import networkx as nx
import numpy as np
import pandas as pd
import plotly.graph_objects as go
from PIL import Image, ImageOps
from scipy import stats
import streamlit as st
from openpyxl import Workbook
from reportlab.lib import colors
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import getSampleStyleSheet
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle

VERSION='1.1'
YELLOW, INK, BLUE, GREEN, ROSE='#F0CA45','#25282B','#285DB0','#237655','#AE345D'
CATEGORIES=['Matériaux','Main-d’œuvre','Transport','Location','Autres']
UNITS=['m³','m²','m','u','forfait']
DAYS=['Lundi','Mardi','Mercredi','Jeudi','Vendredi','Samedi','Dimanche']
MAX_BYTES=12*1024*1024
TASK_CSV=['code','name','start','duration','quantity','done','unit','budget','workers','team','responsible','optimistic','pessimistic','predecessors']
DEFAULT_STYLE=dict(color='#EDF0F2',image='',opacity=.18)


def today():return datetime.now(ZoneInfo('Europe/Paris')).date()
def uid():return uuid.uuid4().hex
def nfmt(v,d=0):return f'{float(v):,.{d}f}'.replace(',',' ').replace('.',',')
def money(v):return nfmt(v)+' FCFA'
def iso(value):
    try:
        if isinstance(value,datetime):value=value.date()
        result=value if isinstance(value,date) else date.fromisoformat(str(value))
    except (TypeError,ValueError):raise ValueError('Date attendue au format AAAA-MM-JJ.') from None
    if not date(2000,1,1)<=result<=date(2100,12,31):raise ValueError('Dates autorisées : 2000 à 2100.')
    return result
def num(value,label,low=0,high=1e12,integer=False):
    if isinstance(value,(bool,np.bool_)):raise ValueError(label+' : nombre attendu.')
    try:v=float(value)
    except (TypeError,ValueError,OverflowError):raise ValueError(label+' : renseigner un nombre.') from None
    if not math.isfinite(v) or not low<=v<=high or integer and not v.is_integer():raise ValueError(label+' : valeur hors limites ou non entière.')
    return int(v) if integer else v
def text(value,label,limit=100,optional=False):
    if not isinstance(value,str):raise ValueError(label+' : texte attendu.')
    v=value.strip()
    if (not v and not optional) or len(v)>limit or any(ord(c)<32 and c not in '\n\t' for c in v):raise ValueError(label+f' : de 1 à {limit} caractères attendus.')
    return v
def ident(v):
    if not isinstance(v,str) or not re.fullmatch('[a-f0-9]{32}',v):raise ValueError('Identifiant invalide.')
    return v
def fresh():return dict(version=1,projects=[],style=copy.deepcopy(DEFAULT_STYLE))
def blank_project(name='Nouveau chantier',start=None):
    start=start or today()
    return dict(id=uid(),name=name,location='',client='',start=str(start),deadline=str(start+timedelta(days=60)),
        budget=0,capacity=20,weekmask='1111100',holidays=[],tasks=[],expenses=[],journal=[],archived=False,origin='Saisie utilisateur')
def blank_task(p):
    used={t['code'].casefold() for t in p['tasks']};index=1
    while ('T'+str(index)).casefold() in used:index+=1
    return dict(id=uid(),code='T'+str(index),name='',start=p['start'],duration=5,optimistic=3,pessimistic=8,
        quantity=100.,done=0.,unit='m³',budget=0,workers=3,team='',responsible='',predecessors=[])


def image_data(data):
    if len(data)>3*1024*1024:raise ValueError('Image limitée à 3 Mo.')
    try:
        with warnings.catch_warnings():
            warnings.simplefilter('error',Image.DecompressionBombWarning)
            with Image.open(io.BytesIO(data)) as original:
                if original.format not in ('JPEG','PNG') or original.width*original.height>20000000:raise ValueError('Image JPEG/PNG de 20 millions de pixels maximum.')
                im=ImageOps.exif_transpose(original).convert('RGB');im.thumbnail((1600,1600))
                out=io.BytesIO();im.save(out,'JPEG',quality=82)
        if len(out.getvalue())>1024*1024:raise ValueError('Image encore trop volumineuse après réduction.')
        return base64.b64encode(out.getvalue()).decode('ascii')
    except (OSError,Image.DecompressionBombError,Image.DecompressionBombWarning):raise ValueError('Image illisible ou trop grande.') from None


def checked_image(encoded):
    if encoded=='':return ''
    try:
        b=base64.b64decode(encoded,validate=True)
        if len(b)>1024*1024:raise ValueError()
        with Image.open(io.BytesIO(b)) as im:
            if im.format not in ('JPEG','PNG') or im.width*im.height>20000000:raise ValueError()
            im.verify()
    except Exception:raise ValueError('Image de sauvegarde invalide.') from None
    return encoded


def calendar(p):return np.busdaycalendar(weekmask=p['weekmask'],holidays=np.array(p['holidays'],dtype='datetime64[D]'))
def workday(value,offset,p):return np.busday_offset(str(value),offset,roll='forward',busdaycal=calendar(p)).astype(object)
def graph(p):
    g=nx.DiGraph();g.add_nodes_from(t['id'] for t in p['tasks'])
    for t in p['tasks']:
        for pred in t['predecessors']:
            if pred not in g:raise ValueError('Prédécesseur absent du chantier.')
            g.add_edge(pred,t['id'])
    if not nx.is_directed_acyclic_graph(g):raise ValueError('Les dépendances forment une boucle : modifier les prédécesseurs.')
    return g


def schedule(p):
    g=graph(p);cal=calendar(p);base=np.datetime64(workday(p['start'],0,p));byid={t['id']:t for t in p['tasks']};out={}
    for key in nx.topological_sort(g):
        t=byid[key];release=int(np.busday_count(base,np.datetime64(workday(t['start'],0,p)),busdaycal=cal))
        begin=max([release,0]+[out[k]['finish_index'] for k in g.predecessors(key)])
        end=begin+t['duration']
        if end>5000:raise ValueError('Planning limité à 5 000 jours travaillés après le début.')
        out[key]=dict(start=workday(base,begin,p),end=workday(base,end-1,p),start_index=begin,finish_index=end)
    return out


def validate(data):
    if not isinstance(data,dict) or data.get('version')!=1:raise ValueError('Sauvegarde ChantierPilot version 1 attendue.')
    d=copy.deepcopy(data);projects=d.get('projects')
    if not isinstance(projects,list) or len(projects)>50:raise ValueError('Maximum 50 chantiers.')
    seen=set()
    def unique(key):
        ident(key)
        if key in seen:raise ValueError('Identifiant répété dans la sauvegarde.')
        seen.add(key)
    style=d.get('style',{})
    if not isinstance(style,dict):raise ValueError('Paramètres d’apparence invalides.')
    color=style.get('color','')
    if not isinstance(color,str) or not re.fullmatch('#[a-fA-F0-9]{6}',color):raise ValueError('Couleur au format #RRGGBB attendue.')
    d['style']=dict(color=color,image=checked_image(style.get('image','')),opacity=num(style.get('opacity'),'Opacité',0,.65))
    for p in projects:
        unique(p['id']);p['name']=text(p.get('name'),'Nom',80)
        for key in ['location','client']:p[key]=text(p.get(key,''),key,100,True)
        p['start']=str(iso(p['start']));p['deadline']=str(iso(p['deadline']))
        if p['deadline']<p['start']:raise ValueError('Échéance antérieure au début du chantier.')
        if (iso(p['deadline'])-iso(p['start'])).days>3660:raise ValueError('Horizon de chantier limité à dix ans.')
        p['budget']=num(p['budget'],'Budget',0,1e12,True);p['capacity']=num(p['capacity'],'Capacité',0,10000,True)
        mask=p.get('weekmask')
        if not isinstance(mask,str) or not re.fullmatch('[01]{7}',mask) or '1' not in mask:raise ValueError('Choisir au moins un jour travaillé par semaine.')
        if not isinstance(p['holidays'],list) or len(p['holidays'])>100:raise ValueError('Maximum 100 jours non travaillés exceptionnels.')
        p['holidays']=sorted(set(str(iso(x)) for x in p['holidays']))
        if not isinstance(p.get('archived'),bool):raise ValueError('État archivé invalide.')
        p['origin']=text(p.get('origin','Import'),'Origine',80)
        if not isinstance(p.get('tasks'),list) or len(p['tasks'])>100:raise ValueError('Maximum 100 tâches par chantier.')
        codes=set();taskids=set()
        for t in p['tasks']:
            unique(t['id']);taskids.add(t['id']);t['code']=text(t['code'],'Code',20)
            if t['code'].casefold() in codes:raise ValueError('Code de tâche répété dans le chantier.')
            codes.add(t['code'].casefold());t['name']=text(t['name'],'Tâche',100)
            t['start']=str(iso(t['start']))
            if t['start']<p['start']:raise ValueError('Une tâche ne peut pas démarrer avant le chantier.')
            for key in ['duration','optimistic','pessimistic']:t[key]=num(t[key],key,1,730,True)
            if not t['optimistic']<=t['duration']<=t['pessimistic']:raise ValueError('Durées attendues : optimiste ≤ probable ≤ pessimiste.')
            t['quantity']=num(t['quantity'],'Quantité prévue',.001,1e9);t['done']=num(t['done'],'Quantité réalisée',0,1e9)
            if t['unit'] not in UNITS:raise ValueError('Unité de quantité invalide.')
            t['budget']=num(t['budget'],'Budget tâche',0,1e12,True);t['workers']=num(t['workers'],'Effectif',0,10000,True)
            for key in ['team','responsible']:t[key]=text(t.get(key,''),key,80,True)
            if not isinstance(t['predecessors'],list) or len(set(t['predecessors']))!=len(t['predecessors']):raise ValueError('Liste de prédécesseurs invalide.')
        schedule(p)
        for listname in ['expenses','journal']:
            if not isinstance(p.get(listname),list) or len(p[listname])>1000:raise ValueError('Maximum 1 000 dépenses ou journées par chantier.')
        for e in p['expenses']:
            unique(e['id']);e['date']=str(iso(e['date']))
            if iso(e['date'])>today():raise ValueError('Une dépense réelle ne peut pas être datée dans le futur.')
            e['label']=text(e['label'],'Libellé',120);e['amount']=num(e['amount'],'Montant',1,1e12,True)
            if e['category'] not in CATEGORIES:raise ValueError('Catégorie de dépense inconnue.')
            if e.get('task_id','') not in taskids|{''}:raise ValueError('Tâche de dépense inconnue.')
        dates=set()
        for j in p['journal']:
            unique(j['id']);j['date']=str(iso(j['date']))
            if iso(j['date'])>today() or j['date'] in dates:raise ValueError('Une seule fiche par date, non future, dans chaque chantier.')
            dates.add(j['date']);j['workers']=num(j['workers'],'Effectif présent',0,10000,True)
            for key in ['note','delivery','incident','decision']:j[key]=text(j.get(key,''),key,1500,True)
            j['photo']=checked_image(j.get('photo',''))
    try:payload=json.dumps(d,ensure_ascii=False,allow_nan=False).encode('utf-8')
    except (ValueError,TypeError):raise ValueError('Sauvegarde non sérialisable.') from None
    if len(payload)>MAX_BYTES:raise ValueError('Sauvegarde limitée à 12 Mo : réduire les photos.')
    return d


def db_path():return Path(os.environ.get('CHANTIERPILOT_DATA_DIR',str(Path.home()/'Documents/Codex/data/chantierpilot')))/'chantierpilot.sqlite3'
def load_store(path=None):
    target=Path(path) if path else db_path();target.parent.mkdir(parents=True,exist_ok=True)
    with closing(sqlite3.connect(target,timeout=10)) as c, c:
        c.execute('CREATE TABLE IF NOT EXISTS workspace (id INTEGER PRIMARY KEY CHECK(id=1),revision INTEGER NOT NULL,payload TEXT NOT NULL)')
        c.execute('INSERT OR IGNORE INTO workspace VALUES(1,0,?)',(json.dumps(fresh()),))
        revision,payload=c.execute('SELECT revision,payload FROM workspace WHERE id=1').fetchone()
    return validate(json.loads(payload)),revision
def save_store(data,revision,path=None):
    clean=validate(data);target=Path(path) if path else db_path()
    with closing(sqlite3.connect(target,timeout=10)) as c, c:
        c.execute('BEGIN IMMEDIATE')
        changed=c.execute('UPDATE workspace SET payload=?,revision=revision+1 WHERE id=1 AND revision=?',
            (json.dumps(clean,ensure_ascii=False,allow_nan=False),revision)).rowcount
        if changed!=1:raise ValueError('Données modifiées dans une autre session. Recharger la page avant de réessayer.')
    return revision+1


def ratio(t):return min(1.,t['done']/t['quantity'])
def progress(p):
    tasks=p['tasks'];weights=np.array([t['budget'] for t in tasks],float)
    if not tasks:return 0.,'aucune tâche'
    if np.any(weights<=0):weights=np.ones(len(tasks));label='pondération égale (budgets de tâches incomplets)'
    else:label='pondération par les budgets de tâches'
    return float(np.average([ratio(t) for t in tasks],weights=weights)),label
def summary(p,reference=None):
    ref=reference or today();sc=schedule(p);v,label=progress(p)
    spent=sum(e['amount'] for e in p['expenses'] if iso(e['date'])<=ref)
    late=sum(sc[t['id']]['end']<ref and ratio(t)<1 for t in p['tasks'])
    status='Archivé' if p['archived'] else 'Sans tâches' if not p['tasks'] else 'Terminé' if all(ratio(t)>=1 for t in p['tasks']) else 'En retard' if late or ref>iso(p['deadline']) else 'En cours'
    return dict(progress=v,weight=label,spent=spent,remaining=p['budget']-spent,late=late,status=status,
        planned_end=max((x['end'] for x in sc.values()),default=iso(p['start'])))


def workforce(p):
    sc=schedule(p)
    if not sc and not p['journal']:return pd.DataFrame(columns=['date','prévu','présent','conflits_équipes'])
    starts=[x['start'] for x in sc.values()]+[iso(j['date']) for j in p['journal']]
    ends=[x['end'] for x in sc.values()]+[iso(j['date']) for j in p['journal']]
    lo,hi=min(starts),max(ends)
    if (hi-lo).days>15000:raise ValueError('Période trop longue pour les effectifs.')
    days=pd.date_range(lo,hi,freq='D').date;records=[];cal=calendar(p)
    actual={j['date']:j['workers'] for j in p['journal']}
    for d in days:
        active=[t for t in p['tasks'] if sc[t['id']]['start']<=d<=sc[t['id']]['end'] and np.is_busday(str(d),busdaycal=cal)]
        teams=[t['team'].strip().casefold() for t in active if t['team'].strip() and t['workers']>0]
        conflicts=sorted({x for x in teams if teams.count(x)>1})
        records.append(dict(date=d,prévu=sum(t['workers'] for t in active),présent=actual.get(str(d),np.nan),conflits_équipes=', '.join(conflicts)))
    return pd.DataFrame(records)


def finance_curve(p,reference=None):
    ref=reference or today();sc=schedule(p)
    points=[iso(p['start']),ref]+[iso(e['date']) for e in p['expenses']]+[x['end'] for x in sc.values()]
    lo,hi=min(points),max(points)
    if (hi-lo).days>15000:raise ValueError('Période trop longue pour les finances.')
    ds=pd.date_range(lo,hi,freq='D').date;planned=np.zeros(len(ds));actual=np.zeros(len(ds));index={str(d):i for i,d in enumerate(ds)};cal=calendar(p)
    for t in p['tasks']:
        for d in pd.date_range(sc[t['id']]['start'],sc[t['id']]['end']).date:
            if np.is_busday(str(d),busdaycal=cal):planned[index[str(d)]]+=t['budget']/t['duration']
    for e in p['expenses']:actual[index[e['date']]]+=e['amount']
    observed=np.cumsum(actual);observed=np.where(np.array([d<=ref for d in ds]),observed,np.nan)
    return pd.DataFrame({'date':ds,'prévisionnel_cumulé':np.cumsum(planned),'dépenses_cumulées':observed,'budget_total':p['budget']})


@st.cache_data(max_entries=8,show_spinner=False)
def simulate(p,reference,count=10000,seed=42):
    count=num(count,'Simulations',1000,50000,True);seed=num(seed,'Graine',0,2147483647,True);ref=iso(reference)
    g=graph(p);cal=calendar(p);base=np.datetime64(workday(ref,0,p));rng=np.random.default_rng(seed)
    tasks={t['id']:t for t in p['tasks']};end={};durations={}
    if not tasks or all(ratio(t)>=1 for t in tasks.values()):raise ValueError('Aucune tâche restante à simuler.')
    for key in nx.topological_sort(g):
        t=tasks[key];remaining=1-ratio(t)
        if remaining<=0:end[key]=np.zeros(count,dtype=int);continue
        a,m,b=t['optimistic'],t['duration'],t['pessimistic']
        draws=np.full(count,m,float) if a==b else rng.triangular(a,m,b,count)
        duration=np.maximum(1,np.ceil(draws*remaining).astype(int));durations[key]=duration
        release=max(0,int(np.busday_count(base,np.datetime64(workday(t['start'],0,p)),busdaycal=cal)))
        begin=np.maximum.reduce([np.full(count,release)]+[end[k] for k in g.predecessors(key)])
        end[key]=begin+duration
    finish=np.maximum.reduce(list(end.values()))
    if finish.max()>5000:raise ValueError('Durées simulées supérieures à 5 000 jours travaillés.')
    limit=int(np.busday_count(base,np.datetime64(iso(p['deadline'])+timedelta(days=1)),busdaycal=cal))
    hits=int(np.count_nonzero(finish<=limit));interval=stats.binomtest(hits,count).proportion_ci(.95,method='exact')
    sensitivity=[]
    for key,ds in durations.items():
        if np.ptp(ds)>0 and np.ptp(finish)>0:
            coef=float(stats.spearmanr(ds,finish).statistic)
            sensitivity.append(dict(tâche=tasks[key]['name'],corrélation=coef))
    q50,q90=[int(np.quantile(finish,q,method='higher')) for q in [.5,.9]]
    dates=np.busday_offset(base,finish-1,busdaycal=cal)
    return dict(probability=hits/count,low=float(interval.low),high=float(interval.high),q50=str(workday(base,q50-1,p)),
        q90=str(workday(base,q90-1,p)),finish=finish,dates=dates.astype(str),count=count,seed=seed,
        sensitivity=sorted(sensitivity,key=lambda x:abs(x['corrélation']),reverse=True),reference=str(ref),deadline=p['deadline'])


def task_frame(p):
    sc=schedule(p);names={t['id']:t['code'] for t in p['tasks']}
    return pd.DataFrame([dict(Code=t['code'],Tâche=t['name'],Début=sc[t['id']]['start'],Fin=sc[t['id']]['end'],
        Durée=t['duration'],Prévu=t['quantity'],Réalisé=t['done'],Unité=t['unit'],Avancement=100*ratio(t),
        Budget=t['budget'],Effectif=t['workers'],Équipe=t['team'],Journées_personnes=t['workers']*t['duration'],
        Prédécesseurs=' | '.join(names[k] for k in t['predecessors'])) for t in p['tasks']])
def safe_frame(frame):
    f=frame.copy()
    for key in f.columns:
        f[key]=f[key].map(lambda x:"'"+x if isinstance(x,str) and x.lstrip().startswith(('=','+','-','@')) else x)
    return f
def csv_bytes(frame):return safe_frame(frame).to_csv(index=False).encode('utf-8-sig')
def task_csv(p):
    names={t['id']:t['code'] for t in p['tasks']}
    return pd.DataFrame([{k:('|'.join(names[i] for i in t[k]) if k=='predecessors' else t[k]) for k in TASK_CSV} for t in p['tasks']],columns=TASK_CSV)
def import_tasks(p,data):
    if len(data)>2*1024*1024:raise ValueError('CSV limité à 2 Mo.')
    try:f=pd.read_csv(io.StringIO(data.decode('utf-8-sig')),sep=None,engine='python',dtype=str,keep_default_na=False,nrows=101)
    except Exception:raise ValueError('CSV UTF-8 illisible.') from None
    if not set(TASK_CSV).issubset(f.columns) or not 1<=len(f)<=100:raise ValueError('Utiliser les colonnes du modèle CSV, de 1 à 100 tâches.')
    q=copy.deepcopy(p);mapping={t['code']:t['id'] for t in q['tasks']};new=[]
    for row in f.to_dict('records'):
        code=row['code'].strip()
        if code in mapping or any(code.casefold()==x.casefold() for x in mapping):raise ValueError('Un code de tâche existe déjà : import entièrement refusé.')
        t={k:row[k] for k in TASK_CSV};t['id']=uid();mapping[code]=t['id'];new.append(t)
    for t in new:
        try:t['predecessors']=[mapping[x.strip()] for x in t['predecessors'].split('|') if x.strip()]
        except KeyError:raise ValueError('Code de prédécesseur inconnu dans le CSV.') from None
        for k in ['quantity','done']:t[k]=num(str(t[k]).replace(',','.'),k,0,1e9)
    q['tasks']+=new
    return validate(dict(version=1,style=DEFAULT_STYLE,projects=[q]))['projects'][0]


def merge_backup(current,data):
    if len(data)>MAX_BYTES:raise ValueError('Sauvegarde limitée à 12 Mo.')
    try:incoming=validate(json.loads(data.decode('utf-8')))
    except (json.JSONDecodeError,UnicodeError,KeyError,TypeError):raise ValueError('Sauvegarde JSON invalide.') from None
    merged=copy.deepcopy(current)
    for p in incoming['projects']:
        p['id']=uid();mapping={t['id']:uid() for t in p['tasks']}
        for t in p['tasks']:
            t['id']=mapping[t['id']];t['predecessors']=[mapping[k] for k in t['predecessors']]
        for e in p['expenses']:
            e['id']=uid();e['task_id']=mapping.get(e.get('task_id',''),'')
        for j in p['journal']:j['id']=uid()
        p['origin']='Import / '+p['origin'][:70];merged['projects'].append(p)
    return validate(merged)


def excel_bytes(p):
    out=io.BytesIO();wb=Workbook();wb.remove(wb.active)
    tables=[('Taches',task_frame(p)),('Effectifs',workforce(p)),('Finances',finance_curve(p)),
        ('Depenses',pd.DataFrame(p['expenses']).drop(columns=['id','task_id'],errors='ignore')),
        ('Journal',pd.DataFrame(p['journal']).drop(columns=['id','photo'],errors='ignore'))]
    for name,frame in tables:
        ws=wb.create_sheet(name);frame=safe_frame(frame);ws.append(list(frame.columns) or ['Aucune donnée'])
        for row in frame.itertuples(index=False,name=None):ws.append([None if pd.isna(x) else x for x in row])
        ws.freeze_panes='A2'
        for col in ws.columns:
            ws.column_dimensions[col[0].column_letter].width=min(48,max(15,max(len(str(c.value or '')) for c in col)+2))
    wb.save(out);return out.getvalue()


def pdf_report(p):
    out=io.BytesIO();styles=getSampleStyleSheet();styles['BodyText'].fontSize=10;styles['BodyText'].leading=14;styles['Heading2'].keepWithNext=True
    P=lambda s:Paragraph(escape(str(s)),styles['BodyText'])
    d=summary(p);story=[Paragraph('ChantierPilot',styles['Title']),P('Rapport de suivi · '+p['name']),P(p['location']),
        P('Situation au '+str(today())+' · '+p['origin']),Spacer(1,12)]
    def table(headers,rows,widths):
        t=Table([[P(x) for x in headers]]+[[P(x) for x in r] for r in rows],colWidths=widths,repeatRows=1,hAlign='LEFT')
        t.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),colors.HexColor(YELLOW)),('GRID',(0,0),(-1,-1),.4,colors.HexColor('#CDD5DA')),
            ('VALIGN',(0,0),(-1,-1),'TOP'),('LEFTPADDING',(0,0),(-1,-1),7),('TOPPADDING',(0,0),(-1,-1),7),('BOTTOMPADDING',(0,0),(-1,-1),7)]));story.extend([t,Spacer(1,14)])
    table(['Indicateur','Valeur'],[['État',d['status']],['Avancement',nfmt(100*d['progress'],1)+' % · '+d['weight']],
        ['Budget',money(p['budget'])],['Dépenses enregistrées',money(d['spent'])],['Budget restant',money(d['remaining'])],
        ['Échéance',p['deadline']],['Fin du planning probable',d['planned_end']]],[190,305])
    story.append(Paragraph('Travaux et effectifs prévus',styles['Heading2']))
    sc=schedule(p)
    table(['Tâche','Période','Avancement','Effectif'],[[t['code']+' · '+t['name'],str(sc[t['id']]['start'])+' / '+str(sc[t['id']]['end']),nfmt(100*ratio(t),1)+' %',str(t['workers'])] for t in p['tasks']],[176,150,85,84])
    story.append(Paragraph('Dépenses par catégorie',styles['Heading2']))
    table(['Catégorie','Montant'],[[cat,money(sum(e['amount'] for e in p['expenses'] if e['category']==cat))] for cat in CATEGORIES],[240,255])
    story.append(Paragraph('Dernières observations',styles['Heading2']))
    for j in sorted(p['journal'],key=lambda x:x['date'],reverse=True)[:10]:
        story.extend([P(j['date']+' · '+str(j['workers'])+' personnes présentes'),P(j['note']),P('Incident : '+j['incident']),P('Décision : '+j['decision']),Spacer(1,8)])
    story.extend([P('Les photos, les tirages et les scénarios probabilistes ne sont pas inclus dans ce rapport. Le prévisionnel financier répartit uniformément les budgets des tâches sur leurs jours travaillés ; ce n’est ni un solde bancaire ni une prévision certifiée de trésorerie.'),P('Suivi pédagogique : aucun contrôle réglementaire, aucune validation de sécurité ou de conformité. Avancement : dernier état saisi, non reconstitution historique.')])
    def footer(c,doc):c.setFont('Helvetica',8);c.drawString(48,23,'ChantierPilot · Rapport pédagogique');c.drawRightString(A4[0]-48,23,str(doc.page))
    SimpleDocTemplate(out,pagesize=A4,leftMargin=48,rightMargin=48,topMargin=40,bottomMargin=44).build(story,onFirstPage=footer,onLaterPages=footer)
    return out.getvalue()


def demo_data(reference=None):
    ref=reference or today();base=ref-timedelta(days=ref.weekday()+14);d=fresh()
    for i,name in enumerate(['Villa Horizon','Bloc scolaire','Drainage Campus']):
        p=blank_project(name,base+timedelta(days=7*i));p.update(location=['Yaoundé · site fictif','Campus · site fictif','Parcelle C · site fictif'][i],budget=[2000000,3500000,1200000][i],capacity=[8,12,6][i],origin='Exemple fictif')
        a=blank_task(p);a.update(code='T1',name='Terrassement',duration=5,optimistic=4,pessimistic=7,quantity=100.,done=[100.,50.,100.][i],budget=200000,team='Équipe A')
        b=blank_task(p);b.update(code='T2',name='Fondations',duration=4,optimistic=3,pessimistic=7,quantity=50.,done=[25.,10.,40.][i],budget=600000,workers=4,team='Équipe B',predecessors=[a['id']])
        c=blank_task(p);c.update(code='T3',name='Élévation' if i<2 else 'Maçonnerie de drainage',duration=6,optimistic=4,pessimistic=10,quantity=120.,done=[0.,0.,60.][i],budget=700000,workers=5,team='Équipe C',predecessors=[b['id']])
        p['tasks']=[a,b,c]
        for k,(cat,amount) in enumerate([('Matériaux',250000),('Main-d’œuvre',100000),('Transport',25000)]):
            p['expenses'].append(dict(id=uid(),date=str(min(ref,iso(p['start'])+timedelta(days=k+1))),category=cat,label='Dépense fictive '+str(k+1),amount=amount,task_id=a['id']))
        p['journal']=[dict(id=uid(),date=str(min(ref,iso(p['start'])+timedelta(days=2))),workers=3,note='Visite pédagogique fictive.',delivery='Livraison de matériaux fictive.',incident='',decision='Vérifier les quantités réalisées.',photo='')]
        d['projects'].append(p)
    return validate(d)


def css(style):
    rgb=[int(style['color'][i:i+2],16)/255 for i in (1,3,5)]
    luminance=sum(w*(x/12.92 if x<=.04045 else ((x+.055)/1.055)**2.4) for x,w in zip(rgb,[.2126,.7152,.0722]))
    fore='#25282B' if luminance>.179 else '#FFFFFF'
    picture=f'url("data:image/jpeg;base64,{style["image"]}")' if style['image'] else 'none'
    st.html('''<style>
:root{color-scheme:light} .stApp,[data-testid="stAppViewContainer"]{background:VAR_BG;color:VAR_FG}
[data-testid="stAppViewContainer"]::before{content:"";position:fixed;inset:0;background-image:VAR_IMG;background-position:center;background-size:cover;opacity:VAR_ALPHA;pointer-events:none;z-index:0}
[data-testid="stMain"]{position:relative;z-index:1}
[data-testid="stMainBlockContainer"]{max-width:1580px;padding:4.6rem 2rem 3rem}
[data-testid="stHeader"]{background:VAR_BG}
[data-testid="stSidebar"]{background:#25282b;color:#f5f6f6}
[data-testid="stSidebar"] button{color:#f5f6f6;background:transparent;border:1px solid #667078;min-height:43px}
[data-testid="stSidebar"] button p,[data-testid="stSidebar"] button span{color:inherit}
[data-testid="stSidebar"] button[kind="primary"]{background:#f0ca45!important;border-color:#f0ca45!important;color:#25282b!important}
[data-testid="stSidebar"] [data-testid="stWidgetLabel"] p,[data-testid="stSidebar"] [data-testid="stCaptionContainer"] p{color:#e1e5e8!important}
.cp-logo{font:800 24px Arial;color:#fff;margin:12px 0 7px}.cp-logo span{color:#f0ca45}.cp-side-sub{font-size:11px;color:#c9d0d5;margin-bottom:24px}
.cp-header{background:#f0ca45;color:#25282b;display:flex;align-items:center;justify-content:space-between;gap:14px;padding:20px 24px;border-bottom:5px solid #25282b;margin-bottom:18px}
.cp-header h1{font:800 30px/1.15 Arial;margin:0;padding:0;letter-spacing:0;overflow-wrap:anywhere}.cp-header p{margin:7px 0 0;font-size:13px}.cp-header small{font-size:12px;white-space:normal}
.cp-kpis{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:12px;margin:15px 0 24px}
.cp-kpi{background:#fff;color:#25282b;border-top:4px solid #285db0;padding:16px;border-radius:6px;min-width:0}
.cp-kpi:nth-child(2){background:#25282b;color:#fff;border-color:#f0ca45}.cp-kpi:nth-child(3){background:#e4f0e8;border-color:#237655}.cp-kpi:nth-child(4){background:#f7e7ee;border-color:#ae345d}
.cp-kpi span,.cp-kpi small{display:block;font-size:12px;line-height:1.5}.cp-kpi strong{display:block;font-size:24px;line-height:1.25;margin:9px 0;overflow-wrap:anywhere}
.cp-site{display:flex;align-items:center;gap:17px;min-height:128px;color:#25282b}.cp-site h3{font:700 18px/1.35 Arial!important;margin:0 0 8px;padding:0;overflow-wrap:anywhere;color:#25282b!important}
.cp-site p{font-size:12px;line-height:1.6;margin:0;color:#4e5b65;overflow-wrap:anywhere}
.cp-ring{flex:0 0 84px;width:84px;height:84px;position:relative;border-radius:50%;background:conic-gradient(#237655 VAR_PERCENT,#e2e7e9 0);display:grid;place-items:center}
.cp-ring::before{content:"";position:absolute;inset:8px;border-radius:50%;background:#fff}.cp-ring b{position:relative;font-size:20px;color:#25282b}
.cp-site-stats{font-size:12px;line-height:1.8;color:#4e5b65;padding:8px 0 14px;border-top:1px solid #e0e5e8;margin-top:10px;overflow-wrap:anywhere}
div[class*="st-key-sitecard_"]{background:#fff!important;border-radius:7px!important;min-height:260px}
.cp-note{background:#e9eef8;border-left:4px solid #285db0;padding:13px 15px;color:#233d68;font-size:13px;line-height:1.65;margin:12px 0}
.cp-note.warn{background:#f7e7ee;color:#70233f;border-color:#ae345d}
.cp-context{background:#fff;border-left:5px solid #237655;padding:13px 16px;color:#25282b;margin:8px 0 20px;overflow-wrap:anywhere}.cp-context strong{font-size:19px}.cp-context small{font-size:12px;line-height:1.6}
.cp-foot{border-top:1px solid #9ca7af;margin-top:28px;padding-top:16px;font-size:12px;color:VAR_FG}
h2{font-size:24px!important;letter-spacing:0!important;color:VAR_FG}h3{font-size:19px!important;letter-spacing:0!important}
[data-testid="stMain"] [data-testid="stWidgetLabel"] p,[data-testid="stMain"] [data-testid="stMarkdownContainer"]{color:VAR_FG}
[data-testid="stCaptionContainer"]{opacity:1!important}[data-testid="stMain"] [data-testid="stCaptionContainer"] p{color:VAR_FG}
[data-testid="stForm"]{background:#fff;color:#25282b;border:1px solid #c4cdd3;border-radius:6px}
[data-testid="stForm"] [data-testid="stWidgetLabel"] p,[data-testid="stForm"] [data-testid="stCaptionContainer"] p{color:#25282b!important}
[data-testid="stForm"] h3,[data-testid="stForm"] h2{color:#25282b!important}
[data-testid="stForm"] [data-testid="stMarkdownContainer"]{color:#25282b!important}
[data-testid="stMain"] .stButton button,[data-testid="stMain"] .stDownloadButton button{background:#fff;color:#25282b}
[data-testid="stMain"] .stButton button p,[data-testid="stMain"] .stDownloadButton button p{color:#25282b!important}
.stButton button,.stDownloadButton button,[data-testid="stFormSubmitButton"] button{border-radius:5px;min-height:42px;white-space:normal}
.stButton button p,.stDownloadButton button p,[data-testid="stFormSubmitButton"] button p{white-space:normal;overflow-wrap:anywhere}
.stButton button[kind="primary"],[data-testid="stFormSubmitButton"] button{background:#f0ca45!important;border-color:#967600!important;color:#25282b!important}
.stButton button[kind="primary"] p,[data-testid="stFormSubmitButton"] button p{color:#25282b!important}
.stButton button:disabled{opacity:.45!important}
@media(max-width:1050px){[data-testid="stMainBlockContainer"]{padding:4.5rem 1.2rem 2rem}.cp-kpi{padding:13px}.cp-kpi strong{font-size:21px}}
@media(max-width:740px){.cp-header{align-items:flex-start;flex-direction:column;padding:18px}.cp-header h1{font-size:28px}.cp-kpis{grid-template-columns:repeat(2,minmax(0,1fr));gap:8px}.cp-kpi strong{font-size:20px}[data-testid="stHorizontalBlock"]{flex-wrap:wrap}[data-testid="stHorizontalBlock"]>[data-testid="stColumn"]{width:100%!important;min-width:100%!important}.cp-site{min-height:110px}}
@media(prefers-reduced-motion:reduce){*{animation:none!important;transition:none!important}}
</style>'''.replace('VAR_BG',style['color']).replace('VAR_FG',fore).replace('VAR_IMG',picture).replace('VAR_ALPHA',str(style['opacity'])))
    if style['image'] or style['color']!=DEFAULT_STYLE['color']:
        st.html('''<style>
[data-testid="stMain"] h2,[data-testid="stMain"] [data-testid="stHeadingWithActionElements"] h3{background:#fff;color:#25282b!important;padding:10px 12px;border-left:4px solid #f0ca45}
[data-testid="stMain"] [data-testid="stWidgetLabel"]{background:#fff}
[data-testid="stMain"] [data-testid="stWidgetLabel"] p{color:#25282b!important}
[data-testid="stMain"] [data-testid="stCaptionContainer"]{background:#fff;padding:6px 10px}
[data-testid="stMain"] [data-testid="stCaptionContainer"] p{color:#25282b!important}
[data-testid="stMain"] [data-testid="stExpander"]{background:#fff;color:#25282b}
[data-testid="stMain"] [data-testid="stExpander"] [data-testid="stMarkdownContainer"]{color:#25282b!important}
.cp-foot{background:#fff;color:#25282b;padding:14px}
</style>''')


def note(message,warn=False):st.html('<div class="cp-note '+('warn' if warn else '')+'">'+escape(message)+'</div>')
def kpis(items):st.html('<div class="cp-kpis">'+''.join('<div class="cp-kpi"><span>'+escape(a)+'</span><strong>'+escape(b)+'</strong><small>'+escape(c)+'</small></div>' for a,b,c in items)+'</div>')
def plot(fig,key,height=350):
    fig.update_layout(template='plotly_white',height=height,paper_bgcolor='#ffffff',plot_bgcolor='#ffffff',
        font=dict(family='Arial',size=12,color=INK),margin=dict(l=45,r=20,t=90 if len(fig.data)>1 else 35,b=65),
        legend=dict(orientation='h',y=1.06,yanchor='bottom',x=0,font=dict(size=11)))
    fig.update_xaxes(automargin=True);fig.update_yaxes(automargin=True)
    st.plotly_chart(fig,width='stretch',theme=None,key=key,alt=key.replace('_',' '),config={'displaylogo':False,'responsive':True,'scrollZoom':False})
def signature(p):return hashlib.sha256(json.dumps(p,sort_keys=True,ensure_ascii=False).encode()).hexdigest()
def commit(data,revision,message):
    try:
        clean=validate(data)
        if st.session_state.get('workspace')=='Exemple fictif':st.session_state.demo=clean
        else:save_store(clean,revision)
        st.session_state.flash=message;st.rerun()
    except (ValueError,TypeError,KeyError) as exc:st.error(str(exc))
    except (OSError,sqlite3.Error):st.error('Enregistrement indisponible. Vérifier le dossier de données et réessayer.')
def replace_project(data,p):
    q=copy.deepcopy(data);q['projects']=[p if x['id']==p['id'] else x for x in q['projects']];return q
def select_site(key):st.session_state.site_id=key;st.session_state.page='Vue chantier';st.rerun()


def project_form(data,revision,existing=None):
    p=copy.deepcopy(existing) if existing else blank_project()
    form_key=('project_'+p['id'] if existing else 'new_project')+'_'+str(revision)
    with st.form(form_key,clear_on_submit=not bool(existing)):
        a,b=st.columns(2)
        name=a.text_input('Nom du chantier',p['name'] if existing else '',max_chars=80)
        location=b.text_input('Localisation',p['location'],max_chars=100)
        client=st.text_input('Maître d’ouvrage / client',p['client'],max_chars=100)
        a,b=st.columns(2);start=a.date_input('Début du chantier',iso(p['start']));deadline=b.date_input('Échéance du chantier',iso(p['deadline']))
        a,b=st.columns(2);budget=a.number_input('Budget du chantier (FCFA)',0,10**12,p['budget'],1000);capacity=b.number_input('Effectif disponible par jour',0,10000,p['capacity'],1)
        working=st.multiselect('Jours travaillés',DAYS,default=[d for i,d in enumerate(DAYS) if p['weekmask'][i]=='1'])
        holidays=st.text_area('Dates non travaillées exceptionnelles (AAAA-MM-JJ, une par ligne)','\n'.join(p['holidays']))
        run=st.form_submit_button('Enregistrer le chantier' if existing else 'Créer le chantier',icon=':material/save:' if existing else ':material/add:',type='primary')
    if run:
        p.update(name=name,location=location,client=client,start=str(start),deadline=str(deadline),budget=budget,capacity=capacity,
            weekmask=''.join('1' if x in working else '0' for x in DAYS),holidays=[x.strip() for x in holidays.splitlines() if x.strip()])
        if not existing and st.session_state.workspace=='Exemple fictif':p['origin']='Exemple fictif'
        q=replace_project(data,p) if existing else copy.deepcopy(data)
        if not existing:q['projects'].append(p)
        commit(q,revision,'Chantier enregistré.')


def dashboard(data,revision):
    st.header('Mes chantiers')
    active=[p for p in data['projects'] if not p['archived']];summaries=[summary(p) for p in active]
    kpis([('Chantiers actifs',str(len(active)),'Portefeuille sélectionné'),('Budget total',money(sum(p['budget'] for p in active)),'Budgets initiaux'),
        ('Dépenses enregistrées',money(sum(x['spent'] for x in summaries)),'Montants réels cumulés'),('Chantiers en retard',str(sum(x['status']=='En retard' for x in summaries)),'Planning ou échéance dépassés')])
    with st.container(horizontal=True):
        show_archive=st.toggle('Inclure les archives',False)
        if st.button('Nouveau chantier',icon=':material/add:',type='primary'):
            st.session_state.page='Créer un chantier';st.rerun()
    projects=data['projects'] if show_archive else active
    search=st.text_input('Rechercher un chantier',placeholder='Nom ou localisation',max_chars=100)
    projects=[p for p in projects if search.casefold() in (p['name']+' '+p['location']).casefold()]
    if not data['projects']:
        note('Aucun chantier enregistré dans cet espace.')
        if st.button('Explorer les 3 chantiers fictifs',icon=':material/science:'):
            st.session_state.demo=demo_data();st.session_state.pending_workspace='Exemple fictif';st.session_state.site_id=None;st.rerun()
        project_form(data,revision)
        return
    for offset in range(0,len(projects),3):
        for col,p in zip(st.columns(3),projects[offset:offset+3]):
            r=summary(p);pct=100*r['progress']
            with col:
                with st.container(border=True,key='sitecard_'+p['id']):
                    st.html(f'<div class="cp-site"><div class="cp-ring" role="img" aria-label="Avancement {pct:.0f} pour cent" style="background:conic-gradient(#237655 {pct:.3f}%,#e2e7e9 0)"><b>{pct:.0f}%</b></div><div><h3>{escape(p["name"])}</h3><p>{escape(p["location"] or "Localisation non renseignée")}<br>{escape(r["status"])} · {escape(p["origin"])}</p></div></div><div class="cp-site-stats">{len(p["tasks"])} tâches · {r["late"]} en retard<br>Dépensé : <b>{escape(money(r["spent"]))}</b><br>Budget restant : {escape(money(r["remaining"]))}</div>')
                    if st.button('Ouvrir '+p['name'],icon=':material/construction:',key='open_'+p['id'],width='stretch',wrap=True):select_site(p['id'])
    if not projects:st.info('Aucun chantier ne correspond à la recherche.')
    if len(active)>1:
        st.subheader('Comparaison des chantiers')
        fig=go.Figure()
        fig.add_trace(go.Bar(x=[p['name'] for p in active],y=[p['budget'] for p in active],name='Budget',marker_color=BLUE))
        fig.add_trace(go.Bar(x=[p['name'] for p in active],y=[r['spent'] for r in summaries],name='Dépenses',marker_color=ROSE))
        fig.update_layout(barmode='group',yaxis_title='FCFA');plot(fig,'budgets_des_chantiers')


def site_overview(p):
    r=summary(p)
    kpis([('Avancement',nfmt(100*r['progress'],1)+' %',r['weight']),('Budget restant',money(r['remaining']),'Budget initial - dépenses'),
        ('Tâches terminées',f'{sum(ratio(t)>=1 for t in p["tasks"])} / {len(p["tasks"])}','Dernières quantités saisies'),('Tâches en retard',str(r['late']),'Fin prévue dépassée, non terminées')])
    st.caption('État : '+r['status']+' · Échéance : '+p['deadline']+' · Fin du planning : '+str(r['planned_end']))
    if p['tasks']:
        fig=go.Figure(go.Bar(x=[100*ratio(t) for t in p['tasks']],y=[t['code']+' · '+t['name'] for t in p['tasks']],orientation='h',marker_color=GREEN))
        fig.update_layout(xaxis_title='Avancement physique (%)',xaxis_range=[0,100],yaxis_autorange='reversed');plot(fig,'avancement_des_travaux',max(300,min(700,70+len(p['tasks'])*38)))
        st.dataframe(task_frame(p),hide_index=True,width='stretch',alt='Avancement, dates et moyens par tâche')
    else:note('Aucune tâche dans ce chantier.')
    over=sum(t['budget'] for t in p['tasks'])-p['budget']
    if over>0:note('Les budgets de tâches dépassent le budget du chantier de '+money(over)+'.',True)
    if any(t['done']>t['quantity'] for t in p['tasks']):note('Une quantité réalisée dépasse la quantité prévue. Le pourcentage visuel est plafonné à 100 %, les quantités restent affichées.',True)
    st.caption('L’avancement est le dernier état saisi, pas une reconstitution historique. Les quantités de différentes unités ne sont pas additionnées. Si un budget de tâche est nul, toutes les tâches reçoivent le même poids.')


def tasks_page(data,revision,p):
    st.header('Travaux et planning')
    if p['tasks']:
        sc=schedule(p);fig=go.Figure()
        for t in p['tasks']:
            begin=sc[t['id']]['start'];end=sc[t['id']]['end'];span=(end-begin).days+1
            fig.add_trace(go.Bar(x=[span*86400000],base=[pd.Timestamp(begin).isoformat()],y=[t['code']+' · '+t['name']],orientation='h',
                marker_color=GREEN if ratio(t)>=1 else BLUE,name=t['code'],showlegend=False,
                customdata=[[t['duration'],100*ratio(t)]],hovertemplate='%{y}<br>%{customdata[0]} jours travaillés<br>%{customdata[1]:.1f} %<extra></extra>'))
        fig.update_layout(barmode='overlay',xaxis_type='date',yaxis_autorange='reversed',xaxis_title='Date')
        plot(fig,'planning_gantt',max(330,min(850,90+len(p['tasks'])*40)))
        st.caption('Les barres couvrent les périodes calendaires ; les durées de tâches excluent les jours non travaillés.')
    options=['new']+[t['id'] for t in p['tasks']];labels={t['id']:t['code']+' · '+t['name'] for t in p['tasks']}
    chosen=st.selectbox('Tâche à créer ou modifier',options,format_func=lambda k:'Nouvelle tâche' if k=='new' else labels[k],key='task_choice_'+p['id'])
    t=copy.deepcopy(next((t for t in p['tasks'] if t['id']==chosen),blank_task(p)))
    with st.form('task_form_'+p['id']+'_'+chosen+'_'+str(revision),clear_on_submit=chosen=='new'):
        a,b=st.columns([1,3]);code=a.text_input('Code de tâche',t['code'],max_chars=20);name=b.text_input('Nom de la tâche',t['name'],max_chars=100)
        a,b=st.columns(2);start=a.date_input('Début au plus tôt',iso(t['start']));duration=b.number_input('Durée probable (jours travaillés)',1,730,t['duration'])
        a,b=st.columns(2);op=a.number_input('Durée optimiste (jours)',1,730,t['optimistic']);pess=b.number_input('Durée pessimiste (jours)',1,730,t['pessimistic'])
        a,b,c=st.columns(3);quantity=a.number_input('Quantité prévue',.001,1e9,float(t['quantity']));done=b.number_input('Quantité réalisée',0.,1e9,float(t['done']));unit=c.selectbox('Unité',UNITS,index=UNITS.index(t['unit']))
        a,b=st.columns(2);budget=a.number_input('Budget de tâche (FCFA)',0,10**12,t['budget'],1000);workers=b.number_input('Effectif prévu (personnes)',0,10000,t['workers'])
        a,b=st.columns(2);team=a.text_input('Équipe affectée',t['team'],max_chars=80);responsible=b.text_input('Responsable',t['responsible'],max_chars=80)
        pred_options=[x['id'] for x in p['tasks'] if x['id']!=t['id']]
        preds=st.multiselect('Tâches à terminer avant celle-ci',pred_options,default=t['predecessors'],format_func=lambda k:labels[k])
        run=st.form_submit_button('Enregistrer la tâche',icon=':material/save:',type='primary')
    if run:
        t.update(code=code,name=name,start=str(start),duration=duration,optimistic=op,pessimistic=pess,quantity=quantity,done=done,unit=unit,budget=budget,workers=workers,team=team,responsible=responsible,predecessors=preds)
        q=copy.deepcopy(p);q['tasks']=[x for x in q['tasks'] if x['id']!=t['id']]+[t]
        commit(replace_project(data,q),revision,'Tâche enregistrée.')
    with st.expander('Importer ou exporter les tâches CSV'):
        template=task_csv(p) if p['tasks'] else task_csv({**p,'tasks':[{**blank_task(p),'name':'Tâche exemple fictif'}]})
        st.download_button('Modèle / tâches CSV',csv_bytes(template),'chantierpilot-taches.csv','text/csv',icon=':material/download:')
        uploaded=st.file_uploader('Importer des tâches CSV',type='csv',max_upload_size=2,key='tasks_csv_'+p['id'])
        if uploaded:
            try:
                q=import_tasks(p,uploaded.getvalue());st.dataframe(task_frame(q).tail(len(q['tasks'])-len(p['tasks'])),hide_index=True,width='stretch',alt='Nouvelles tâches à importer')
                confirmed=st.checkbox('Ajouter ces tâches à ce chantier',key='confirm_tasks_'+p['id'])
                if st.button('Valider l’import des tâches',disabled=not confirmed,icon=':material/upload:'):commit(replace_project(data,q),revision,'Tâches importées.')
            except (ValueError,KeyError,TypeError) as exc:st.error(str(exc))
    st.caption('Liens fin-début : la tâche suivante commence au prochain jour travaillé après la fin des prédécesseurs. Les jours non travaillés sont reportés en avant. Modifier les quantités met à jour l’avancement, pas les dépenses.')


def update_staffing(p,task_id,workers,team,responsible,capacity):
    q=copy.deepcopy(p)
    q['capacity']=num(capacity,'Capacité journalière',0,10000,True)
    if task_id is None and not q['tasks']:return q
    task=next((t for t in q['tasks'] if t['id']==task_id),None)
    if task is None:raise ValueError('Tâche introuvable. Sélectionner une tâche du chantier.')
    task.update(workers=num(workers,'Effectif prévu',0,10000,True),
        team=text(team,'Équipe',80,True),responsible=text(responsible,'Responsable',80,True))
    return q


def update_attendance(p,day,workers):
    day=iso(day)
    if day>today():raise ValueError('Une présence réelle ne peut pas être enregistrée à une date future.')
    workers=num(workers,'Présence réelle',0,10000,True)
    q=copy.deepcopy(p)
    entry=next((j for j in q['journal'] if j['date']==str(day)),None)
    if entry is None:
        entry=dict(id=uid(),date=str(day),workers=workers,note='',delivery='',incident='',decision='',photo='')
        q['journal'].append(entry)
    else:entry['workers']=workers
    return q


def workforce_page(data,revision,p):
    st.header('Effectifs et durée des tâches');frame=workforce(p)
    planned=sum(t['workers']*t['duration'] for t in p['tasks'])
    kpis([('Charge prévue',nfmt(planned),'Journées-personnes'),('Pic de besoin',nfmt(frame['prévu'].max() if not frame.empty else 0),'Personnes prévues simultanément'),
        ('Capacité journalière',str(p['capacity']),'Personnes disponibles déclarées'),('Jours en surcharge',str(int((frame['prévu']>p['capacity']).sum())),'Besoin supérieur à la capacité')])
    context=st.session_state.workspace+'_'+p['id']
    stamp=context+'_'+str(revision)+'_'+signature(p)[:16]
    left,right=st.columns(2)
    with left:
        st.subheader('Modifier les effectifs prévus')
        task=None
        if p['tasks']:
            labels={t['id']:t['code']+' · '+t['name'] for t in p['tasks']}
            chosen=st.selectbox('Tâche concernée',list(labels),format_func=labels.get,key='staff_task_'+context)
            task=next(t for t in p['tasks'] if t['id']==chosen)
        with st.form('staff_plan_'+stamp+'_'+(task['id'] if task else 'capacity')):
            capacity=st.number_input('Capacité disponible par jour (personnes)',0,10000,p['capacity'],1)
            if task:
                workers=st.number_input('Effectif prévu pour cette tâche (personnes)',0,10000,task['workers'],1)
                team=st.text_input('Équipe',task['team'],max_chars=80)
                responsible=st.text_input('Responsable de l’équipe',task['responsible'],max_chars=80)
            save_plan=st.form_submit_button('Enregistrer les effectifs prévus',icon=':material/save:',type='primary',width='stretch')
        if save_plan:
            q=update_staffing(p,task['id'] if task else None,workers if task else None,team if task else '',responsible if task else '',capacity)
            commit(replace_project(data,q),revision,'Effectifs prévus et capacité enregistrés.')
    with right:
        st.subheader('Présence réelle par journée')
        day=st.date_input('Date de présence',today(),min_value=date(2000,1,1),max_value=today(),key='staff_day_'+context)
        if day is not None:
            entry=next((j for j in p['journal'] if j['date']==str(day)),None)
            with st.form('staff_actual_'+stamp+'_'+str(day)):
                actual=st.number_input('Personnes réellement présentes',0,10000,entry['workers'] if entry else None,1,placeholder='Effectif du jour')
                save_actual=st.form_submit_button('Enregistrer la présence',icon=':material/save:',type='primary',width='stretch')
            if save_actual:
                q=update_attendance(p,day,actual)
                commit(replace_project(data,q),revision,'Présence enregistrée. Le journal de chantier est également à jour.')
    st.subheader('Évolution des effectifs')
    if frame.empty:note('Aucune tâche ou journée renseignée.');return
    conflicts=frame[frame['conflits_équipes']!='']
    fig=go.Figure(go.Bar(x=frame['date'],y=frame['prévu'],name='Besoin prévu',marker_color=BLUE))
    fig.add_trace(go.Scatter(x=frame['date'],y=frame['présent'],mode='lines+markers',connectgaps=False,name='Présence observée',line=dict(color=GREEN,width=3)))
    fig.add_hline(y=p['capacity'],line_dash='dash',line_color=ROSE);fig.update_layout(xaxis_title='Date',yaxis_title='Personnes');plot(fig,'effectifs_journaliers')
    if len(conflicts):note(f'{len(conflicts)} jours comportent la même équipe sur plusieurs tâches. Le total est un besoin par tâche, pas un décompte dédoublonné de personnes.',True)
    st.subheader('Charge par tâche')
    if p['tasks']:st.dataframe(task_frame(p)[['Code','Tâche','Début','Fin','Durée','Effectif','Équipe','Journées_personnes']],hide_index=True,width='stretch',alt='Effectifs, durée travaillée et journées-personnes par tâche')
    st.dataframe(frame,hide_index=True,width='stretch',alt='Besoin quotidien, présence observée et conflits d’équipes')
    st.download_button('Exporter les effectifs CSV',csv_bytes(frame),'chantierpilot-effectifs.csv','text/csv',icon=':material/download:')
    st.caption('Charge = effectif × durée travaillée. Une date sans fiche journal a une présence inconnue, pas zéro. Les tâches superposées additionnent leurs besoins ; aucune affectation nominative ni optimisation de ressources n’est effectuée.')


def finance_page(data,revision,p):
    st.header('Finances du chantier');r=summary(p);allocated=sum(t['budget'] for t in p['tasks'])
    kpis([('Budget initial',money(p['budget']),'Enveloppe du chantier'),('Dépenses réelles',money(r['spent']),'Montants enregistrés'),
        ('Budget restant',money(r['remaining']),'Pas un solde bancaire'),('Budget non affecté',money(p['budget']-allocated),'Budget initial - budgets de tâches')])
    curve=finance_curve(p);fig=go.Figure()
    for col,label,color in [('prévisionnel_cumulé','Prévisionnel des tâches',BLUE),('dépenses_cumulées','Dépenses réelles',ROSE),('budget_total','Budget initial',GREEN)]:
        fig.add_trace(go.Scatter(x=curve['date'],y=curve[col],name=label,mode='lines',line=dict(color=color,width=2,dash='dash' if col=='budget_total' else 'solid')))
    fig.update_layout(yaxis_title='FCFA cumulés',xaxis_title='Date');plot(fig,'evolution_financiere',390)
    st.caption('Prévisionnel : budget de chaque tâche réparti uniformément sur ses jours travaillés. Les dépenses réelles s’arrêtent à aujourd’hui. Modifier le planning recalcule cette référence ; il ne s’agit pas d’une prévision de trésorerie ou d’une baseline figée.')
    totals=[sum(e['amount'] for e in p['expenses'] if e['category']==cat) for cat in CATEGORIES]
    if any(totals):
        fig=go.Figure(go.Bar(x=CATEGORIES,y=totals,marker_color=[BLUE,GREEN,ROSE,'#8A6414','#63717D']));fig.update_layout(yaxis_title='Dépenses (FCFA)');plot(fig,'repartition_des_depenses')
    choices=['new']+[e['id'] for e in p['expenses']];labels={e['id']:e['date']+' · '+e['label'] for e in p['expenses']}
    chosen=st.selectbox('Dépense à saisir ou modifier',choices,format_func=lambda k:'Nouvelle dépense' if k=='new' else labels[k],key='expense_choice_'+p['id'])
    e=copy.deepcopy(next((x for x in p['expenses'] if x['id']==chosen),dict(id=uid(),date=str(today()),category=CATEGORIES[0],label='',amount=1000,task_id='')))
    with st.form('expense_form_'+p['id']+'_'+chosen+'_'+str(revision),clear_on_submit=chosen=='new'):
        a,b=st.columns(2);day=a.date_input('Date de dépense',iso(e['date']),max_value=today());category=b.selectbox('Catégorie',CATEGORIES,index=CATEGORIES.index(e['category']))
        label=st.text_input('Libellé de dépense',e['label'],max_chars=120);amount=st.number_input('Montant dépensé (FCFA)',1,10**12,e['amount'],1000)
        labels_t={t['id']:t['code']+' · '+t['name'] for t in p['tasks']};opts=['']+list(labels_t)
        task=st.selectbox('Tâche concernée',opts,index=opts.index(e.get('task_id','')),format_func=lambda k:labels_t.get(k,'Dépense générale'))
        run=st.form_submit_button('Enregistrer la dépense',type='primary',icon=':material/save:')
    if run:
        e.update(date=str(day),category=category,label=label,amount=amount,task_id=task);q=copy.deepcopy(p);q['expenses']=[x for x in q['expenses'] if x['id']!=e['id']]+[e]
        commit(replace_project(data,q),revision,'Dépense enregistrée.')
    if p['expenses']:st.dataframe(pd.DataFrame(p['expenses']).drop(columns=['id','task_id']),hide_index=True,width='stretch',alt='Dépenses enregistrées du chantier')
    st.download_button('Exporter les dépenses CSV',csv_bytes(pd.DataFrame(p['expenses']).drop(columns=['id','task_id'],errors='ignore')),'chantierpilot-depenses.csv','text/csv',icon=':material/download:')
    if r['remaining']<0:note('Dépassement du budget initial : '+money(-r['remaining'])+'.',True)


def journal_page(data,revision,p):
    st.header('Journal de chantier')
    selected=st.date_input('Journée du chantier',today(),max_value=today(),key='journal_day_'+p['id'])
    if selected is None:return
    j=copy.deepcopy(next((x for x in p['journal'] if x['date']==str(selected)),dict(id=uid(),date=str(selected),workers=0,note='',delivery='',incident='',decision='',photo='')))
    with st.form('journal_form_'+p['id']+'_'+str(selected)+'_'+str(revision)):
        workers=st.number_input('Effectif réellement présent',0,10000,j['workers'])
        content=st.text_area('Travaux effectués / observations',j['note'],max_chars=1500)
        delivery=st.text_area('Livraisons reçues',j['delivery'],max_chars=1500)
        a,b=st.columns(2);incident=a.text_area('Difficultés / incidents',j['incident'],max_chars=1500);decision=b.text_area('Décisions prises',j['decision'],max_chars=1500)
        image=st.file_uploader('Photo de la journée (JPEG / PNG)',type=['jpg','jpeg','png'],max_upload_size=3,key='photo_'+p['id']+'_'+str(selected))
        remove=st.checkbox('Retirer la photo de cette fiche',False)
        run=st.form_submit_button('Enregistrer la journée',type='primary',icon=':material/save:')
    if run:
        try:
            photo='' if remove else image_data(image.getvalue()) if image else j['photo']
            j.update(workers=workers,note=content,delivery=delivery,incident=incident,decision=decision,photo=photo)
            q=copy.deepcopy(p);q['journal']=[x for x in q['journal'] if x['date']!=str(selected)]+[j]
            commit(replace_project(data,q),revision,'Journée enregistrée.')
        except ValueError as exc:st.error(str(exc))
    for entry in sorted(p['journal'],key=lambda x:x['date'],reverse=True)[:20]:
        with st.expander(entry['date']+' · '+str(entry['workers'])+' personnes',expanded=entry['date']==str(selected)):
            st.text(entry['note'] or 'Aucune observation.');st.text('Livraisons : '+(entry['delivery'] or 'Non renseignées'))
            st.text('Incidents : '+(entry['incident'] or 'Non renseignés'));st.text('Décisions : '+(entry['decision'] or 'Non renseignées'))
            if entry['photo']:st.image(base64.b64decode(entry['photo']),width='stretch',alt='Photo enregistrée de la journée '+entry['date'])
    st.caption('Une seule fiche par date et par chantier : une modification remplace cette fiche. La présence observée alimente le graphique des effectifs sans modifier les besoins prévus.')


def risk_page(p):
    st.header('Probabilité de finir à temps')
    if not p['tasks'] or all(ratio(t)>=1 for t in p['tasks']):note('Aucune tâche restante à simuler. La date réelle de réception n’est pas déduite des quantités.');return
    with st.form('risk_form_'+p['id']):
        a,b=st.columns(2);count=a.select_slider('Nombre de simulations',[1000,5000,10000,20000,50000],value=10000);seed=b.number_input('Graine aléatoire',0,2147483647,42)
        run=st.form_submit_button('Simuler la fin du chantier',type='primary',icon=':material/play_arrow:')
    sig=signature(p)+str(today())
    if run:
        try:
            with st.spinner('Simulation des tâches restantes…'):st.session_state.risk=(sig,simulate(p,str(today()),count,seed))
        except (ValueError,TypeError) as exc:st.error(str(exc))
    saved=st.session_state.get('risk')
    if saved and saved[0]==sig:
        r=saved[1]
        kpis([('Fin dans les délais',nfmt(100*r['probability'],1)+' %','Échéance : '+r['deadline']),('Fin médiane P50',r['q50'],'50 % des tirages au plus tard'),
            ('Fin P90',r['q90'],'90 % des tirages au plus tard'),('IC 95 % de Monte-Carlo',nfmt(100*r['low'],3)+' à '+nfmt(100*r['high'],3)+' %','Erreur des tirages uniquement')])
        fig=go.Figure(go.Histogram(x=pd.to_datetime(r['dates']),marker_color=BLUE,name='Fins simulées'));fig.add_vline(x=pd.Timestamp(p['deadline']).timestamp()*1000,line_dash='dash',line_color=ROSE)
        fig.update_layout(xaxis_title='Date de fin simulée',yaxis_title='Nombre de tirages');plot(fig,'distribution_des_dates_de_fin')
        if r['sensitivity']:
            sf=pd.DataFrame(r['sensitivity'][:8]);fig=go.Figure(go.Bar(x=sf['corrélation'],y=sf['tâche'],orientation='h',marker_color=GREEN));fig.update_layout(xaxis_title='Corrélation de rang avec la fin',yaxis_autorange='reversed');plot(fig,'sensibilite_des_durees')
        st.download_button('Exporter les simulations CSV',csv_bytes(pd.DataFrame({'fin_simulée':r['dates'],'jours_travaillés_restants':r['finish']})),'chantierpilot-simulations.csv','text/csv',icon=':material/download:')
        st.caption(f'{r["count"]} tirages · graine {r["seed"]} · situation au {r["reference"]}. Corrélation descriptive, pas preuve de causalité.')
    note('Modèle pédagogique : lois triangulaires indépendantes entre durées optimiste, probable et pessimiste. Durée restante = durée tirée × fraction non réalisée, arrondie au jour travaillé supérieur. Les tâches terminées ne sont plus simulées. Liens fin-début et calendrier sont respectés ; ressources supposées disponibles, sans nivellement, météo commune ni validation contractuelle.',True)


def appearance_page(data,revision):
    st.header('Apparence');s=data['style']
    themes={'Signal clair':'#EDF0F2','Graphite':'#303438','Blanc atelier':'#FFFFFF','Vert profond':'#173E35'}
    with st.form('appearance_form_'+str(revision)):
        preset=st.selectbox('Palette de fond',['Personnalisée']+list(themes))
        color=st.color_picker('Couleur personnalisée',s['color'])
        opacity=st.slider('Visibilité de l’image d’arrière-plan',0.,.65,float(s['opacity']),.05)
        image=st.file_uploader('Image d’arrière-plan (JPEG / PNG)',type=['jpg','jpeg','png'],max_upload_size=3,key='background_upload')
        remove=st.checkbox('Retirer l’image d’arrière-plan',False)
        run=st.form_submit_button('Appliquer l’apparence',type='primary',icon=':material/palette:')
    if run:
        try:
            q=copy.deepcopy(data);q['style']=dict(color=themes.get(preset,color),image='' if remove else image_data(image.getvalue()) if image else s['image'],opacity=opacity)
            commit(q,revision,'Apparence enregistrée.')
        except ValueError as exc:st.error(str(exc))
    if st.button('Rétablir l’apparence initiale',icon=':material/restart_alt:'):
        q=copy.deepcopy(data);q['style']=copy.deepcopy(DEFAULT_STYLE);commit(q,revision,'Apparence initiale rétablie.')
    if s['image']:st.image(base64.b64decode(s['image']),width=280,alt='Image d’arrière-plan actuelle')


def settings_page(data,revision,p):
    st.header('Paramètres du chantier');project_form(data,revision,p)
    with st.expander('Archivage du chantier'):
        confirmed=st.checkbox('Confirmer le changement d’état du chantier',key='confirm_archive_'+p['id'])
        if st.button('Restaurer le chantier' if p['archived'] else 'Archiver le chantier',disabled=not confirmed,icon=':material/archive:'):
            q=copy.deepcopy(p);q['archived']=not q['archived'];commit(replace_project(data,q),revision,'État du chantier mis à jour.')


def exports_page(data,revision,p):
    st.header('Rapports et sauvegardes')
    if p:
        st.subheader(p['name'])
        sig=signature(p)+str(today())
        if st.button('Préparer le rapport PDF et Excel',type='primary',icon=':material/picture_as_pdf:'):
            st.session_state.reports=(sig,pdf_report(p),excel_bytes(p))
        saved=st.session_state.get('reports')
        if saved and saved[0]==sig:
            with st.container(horizontal=True):
                st.download_button('Rapport PDF',saved[1],'chantierpilot-rapport.pdf','application/pdf',icon=':material/download:')
                st.download_button('Classeur Excel',saved[2],'chantierpilot-suivi.xlsx','application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',icon=':material/download:')
        st.caption('Rapport : situation, tâches, finances et dix dernières observations. Photos et tirages non inclus. Excel : tâches, effectifs, courbe financière, dépenses et journal.')
    st.subheader('Sauvegarde de l’espace sélectionné')
    st.download_button('Sauvegarde complète JSON',json.dumps(data,ensure_ascii=False,indent=2).encode('utf-8'),'chantierpilot-sauvegarde.json','application/json',icon=':material/save:')
    uploaded=st.file_uploader('Importer une sauvegarde JSON',type='json',max_upload_size=12,key='backup_file')
    if uploaded:
        try:
            merged=merge_backup(data,uploaded.getvalue());n=len(merged['projects'])-len(data['projects'])
            st.info(f'{n} chantiers seront ajoutés. Les chantiers existants et l’apparence actuelle seront conservés.')
            confirmed=st.checkbox('Confirmer l’ajout de ces chantiers dans cet espace')
            if st.button('Ajouter les chantiers de la sauvegarde',disabled=not confirmed,icon=':material/upload:'):commit(merged,revision,'Sauvegarde importée sans écraser les chantiers existants.')
        except (ValueError,KeyError,TypeError) as exc:st.error(str(exc))
    with st.expander('Tests et hypothèses'):
        st.markdown('**Test manuel fictif :** terrassement 100 m³ prévus, 40 réalisés → 40 %. Budget 200 000 FCFA, dépense 110 000 FCFA → 55 % consommés, 90 000 FCFA restants. Les deux pourcentages ont des sens différents.')
        st.markdown('**Effectifs :** A = 3 personnes sur 5 jours ; B = 2 personnes sur les jours 3 à 5. Besoins : 3, 3, 5, 5, 5 personnes ; charge = 21 journées-personnes. Équipes distinctes supposées.')
        st.markdown('**Délais :** A = 2 jours puis B = 3 jours, durées optimiste/probable/pessimiste identiques. Départ lundi sans jour férié : fin vendredi. La simulation est déterministe dans ce cas.')
        st.caption('Outil pédagogique de suivi, pas de validation réglementaire ou de gestion de paie. Stockage local SQLite hors du dossier livré. Sur un hébergement éphémère, une sauvegarde externe est indispensable.')


def main():
    st.set_page_config(page_title='ChantierPilot · Suivi de chantier',page_icon=':material/construction:',layout='wide')
    for key,value in dict(page='Tableau de bord',workspace='Mes chantiers',site_id=None).items():
        if key not in st.session_state:st.session_state[key]=value
    if st.session_state.get('workspace')=='Exemple fictif':
        if 'demo' not in st.session_state:st.session_state.demo=fresh()
        data=copy.deepcopy(st.session_state.demo);revision=0
    else:
        try:data,revision=load_store()
        except (OSError,sqlite3.Error,ValueError,KeyError,TypeError,json.JSONDecodeError):
            st.error('Le registre local est indisponible ou invalide. Aucun remplacement automatique des données n’a été effectué.');st.stop()
    css(data['style'])
    pages=[('Tableau de bord','dashboard'),('Vue chantier','construction'),('Travaux et planning','calendar_month'),('Effectifs','groups'),
        ('Finances','account_balance_wallet'),('Journal','edit_note'),('Délais et probabilités','query_stats'),('Apparence','palette'),('Rapports et sauvegardes','folder_open'),('Paramètres chantier','settings')]
    with st.sidebar:
        st.html('<div class="cp-logo">Chantier<span>Pilot</span></div><div class="cp-side-sub">TRAVAUX / ÉQUIPES / FINANCES</div>')
        for name,icon in pages:
            if st.button(name,icon=f':material/{icon}:',width='stretch',wrap=True,type='primary' if st.session_state.page==name else 'secondary'):
                st.session_state.page=name;st.rerun()
        st.space(15)
        st.segmented_control('Espace de travail',['Mes chantiers','Exemple fictif'],key='workspace',required=True,wrap=True)
        if st.button('Charger les 3 chantiers fictifs',icon=':material/science:',width='stretch',wrap=True):
            st.session_state.demo=demo_data();st.session_state.pending_workspace='Exemple fictif';st.session_state.site_id=None;st.session_state.page='Tableau de bord';st.rerun()
        st.caption('v'+VERSION+' · suivi pédagogique')
    st.html('<header class="cp-header"><div><h1>ChantierPilot</h1><p>Suivi des travaux, des équipes et des finances</p></div><small>'+str(today())+'<br>'+escape(st.session_state.workspace)+'</small></header>')
    if st.session_state.workspace=='Mes chantiers' and st.session_state.get('displayed_revision',revision)!=revision:
        st.info('Le registre a changé dans une autre opération. Les formulaires ont été actualisés ; vérifier les valeurs avant de valider.')
    if st.session_state.get('flash'):st.success(st.session_state.pop('flash'))
    p=next((p for p in data['projects'] if p['id']==st.session_state.site_id),None)
    if p and st.session_state.page!='Tableau de bord':
        st.html('<div class="cp-context"><strong>'+escape(p['name'])+'</strong><br><small>'+escape(p['location'])+' · '+escape(p['origin'])+'</small></div>')
        if st.button('Tous les chantiers',icon=':material/arrow_back:'):
            st.session_state.page='Tableau de bord';st.rerun()
    try:
        page=st.session_state.page
        if page=='Tableau de bord':dashboard(data,revision)
        elif page=='Créer un chantier':st.header('Nouveau chantier');project_form(data,revision)
        elif page=='Apparence':appearance_page(data,revision)
        elif page=='Rapports et sauvegardes':exports_page(data,revision,p)
        elif not p:note('Aucun chantier sélectionné dans cet espace.');dashboard(data,revision)
        elif page=='Vue chantier':site_overview(p)
        elif page=='Travaux et planning':tasks_page(data,revision,p)
        elif page=='Effectifs':workforce_page(data,revision,p)
        elif page=='Finances':finance_page(data,revision,p)
        elif page=='Journal':journal_page(data,revision,p)
        elif page=='Délais et probabilités':risk_page(p)
        else:settings_page(data,revision,p)
    except (ValueError,TypeError,KeyError) as exc:st.error(str(exc))
    st.html('<div class="cp-foot">ChantierPilot · Quantités observées, besoins prévus et scénarios simulés distincts · Aucune validation réglementaire</div>')
    if st.session_state.workspace=='Mes chantiers':st.session_state.displayed_revision=revision


if __name__=='__main__':
    if st.session_state.get('pending_workspace'):st.session_state.workspace=st.session_state.pop('pending_workspace')
    main()
