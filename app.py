"""
Heat-Stress & Cold-Wave Neuroinflammation Simulator Platform
MSc Neuroscience Research Platform | Final Unified Master Edition

Author: Tasnim (TiaGassem) | Computational Neuroscience Research Project
Copyright (c) 2026 Tasnim (TiaGassem). All rights reserved. See LICENSE.

v2 additions (original architecture preserved): computed Past/Present/Future comparison, ozone & PM2.5 load,
2050 microvascular frailty, transparent e-mail pipeline, risk map, dual-region comparison tools, climate-causes
lessons, awareness campaign toolkit, guide assistant, sources library, SEO/PWA, mobile layout.

Features & Architecture
------------------------
* Universal Geocoding Engine with Strict Bidirectional Map-Text Synchronization
* Integrated Neuro-Assistant Hub with Dynamic State Telemetry & Multi-Epoch Models
* Dual Thermal Anomaly Modeling: Hyperthermia (>25°C) & Hypothermia (<10°C)
* Coupled Biophysical ODE Kinetics (BBB Permeability & Microglial M1 Polarization)
* Multi-Path HTTP (Resend API) & SMTP Email Dispatch Pipeline + Screen Fallback
* Multi-Language Support: English (EN), Français (FR), Arabic (AR)
* Unicode-Safe FPDF2 Clinical Diagnostic Report Export Engine
"""
from __future__ import annotations

import base64
import html as html_lib
import io
import json
import re
import smtplib
import ssl
import time
import unicodedata
from urllib.parse import quote
from datetime import date, datetime, timedelta, timezone
from email.message import EmailMessage

import folium
import matplotlib.dates as mdates
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import requests
import seaborn as sns
import streamlit as st
from fpdf import FPDF
from geopy.geocoders import Nominatim
from scipy.integrate import odeint
from streamlit_folium import st_folium

try:
    import streamlit.components.v1 as components
except Exception:  # pragma: no cover
    components = None

# ---------------------------------------------------------------------------
# GLOBAL CONSTANTS & ENGINE CONFIGURATION
# ---------------------------------------------------------------------------
FORECAST_URL = "https://api.open-meteo.com/v1/forecast"
ARCHIVE_URL = "https://archive-api.open-meteo.com/v1/archive"
AIR_URL = "https://air-quality-api.open-meteo.com/v1/air-quality"

O3_REF, PM_REF = 60.0, 15.0            # WHO 2021 AQG: ozone peak-season (ug/m3), PM2.5 24-h (ug/m3)
DT_2050 = 2.45                         # warming shift used by the 2050 engine (degC)
O3_PER_C, PM_PER_C = 2.0, 0.5          # assumed ozone "climate penalty" / PM2.5 change per degC (editable assumption)
EPOCHS = ["Past", "Present", "Future"]
EPOCH_LABELS = {"Past": "Past - Copernicus ERA5", "Present": "Present - Open-Meteo 7-day", "Future": "Future - Climate 2050"}

BBB_ALERT, M1_ALERT = 0.50, 0.40      # Critical hazard threshold
BBB_MOD, M1_MOD = 0.20, 0.15          # Moderate hazard threshold
SPINUP_DAYS = 3                        

# ---------------------------------------------------------------------------
# TRANSLATION DICTIONARY
# ---------------------------------------------------------------------------
I18N = {
    "EN": {
        "title": "Thermal Stress & Cold-Wave Neuroinflammation Simulator",
        "subtitle": "MSc Neuroscience Research Platform | Copernicus ERA5 & Biophysical Engine",
        "disclaimer": "Academic Research Notice: Computational model derived from peer-reviewed ODE kinetics. Intended for risk evaluation and research analysis, not as a primary clinical diagnostic instrument.",
        "mode_fc": "Predictive Forecast (7-Day Proactive Model)",
        "mode_ar": "Copernicus ERA5 Archive (Historical Reanalysis)",
        "mode_cc": "Climate Change 2050 Projection Model (Future Trend)",
        "lang_select": "Interface Language",
        "single_view": "Single Region Analysis",
        "dual_view": "Comparative Dual-Region Analysis",
        "run_btn": "Run Simulation",
        "reset_btn": "Reset Inputs",
        "search_label": "Search ANY City, Region, or Country in the World:",
        "high_hazard": "CRITICAL HAZARD: Severe blood-brain barrier disruption projected.",
        "mod_hazard": "MODERATE HAZARD: Elevated microglial M1 neuroinflammatory polarization projected.",
        "stable_hazard": "PHYSIOLOGICAL BASELINE: All modeled kinetics remain within homeostatic tolerance.",
        "max_bbb": "Peak BBB Permeability",
        "max_m1": "Peak M1 Polarization",
        "max_heat": "Thermal Stress Index",
        "protocol_title": "Preventative Interventions & Clinical Protocols",
        "pdf_btn": "Export Clinical Diagnostic Report (PDF)",
        "email_title": "Automated Early-Warning Email & Mobile Dispatch",
        "email_placeholder": "Enter clinical or institutional email...",
        "email_send": "Dispatch Early Warning Notice",
        "lit_title": "Peer-Reviewed Literature & Bibliography",
        "expander_title": "Mathematical Formulation & Differential Equations",
        "guide_title": "How to Use This Simulator & Climate Engine Purpose",
        "conclusion_title": "Simulation Synthesis & Clinical Conclusion",
        "interp_title": "Specific Pathokinetic Trajectory Analysis",
        "tab_sim": "🧪 Simulator", "tab_causes": "🌍 Heatwave Causes & Climate Lessons", "tab_aware": "📣 Awareness Campaign",
        "tab_guide": "💬 Guide Assistant", "tab_src": "📚 Sources",
        "epoch_title": "Past · Present · Future Comparison (computed)", "compare_title": "Dual-Region Comparison Tools",
        "assistant_title": "Guide Assistant",
    },
    "FR": {
        "title": "Simulateur de Neuroinflammation (Stress Thermique & Vagues de Froid)",
        "subtitle": "Plateforme de Recherche Master Neuroscience | Moteur Copernicus ERA5",
        "disclaimer": "Avertissement Académique : Modèle informatique dérivé de la littérature scientifique. Destiné à l'évaluation des risques et à l'enseignement, non à un diagnostic clinique direct.",
        "mode_fc": "Prévision Proactive (Modèle 7 Jours)",
        "mode_ar": "Archive Historique Copernicus ERA5 (Réanalyse)",
        "mode_cc": "Projection Réchauffement Climatique 2050 (Tendance)",
        "lang_select": "Langue de l'interface",
        "single_view": "Analyse Zone Unique",
        "dual_view": "Analyse Comparative Deux Zones",
        "run_btn": "Lancer la Simulation",
        "reset_btn": "Réinitialiser",
        "search_label": "Rechercher N'IMPORTE QUELLE ville ou pays dans le monde :",
        "high_hazard": "ALERTE CRITIQUE : Rupture significative de la barrière hémato-encéphalique projetée.",
        "mod_hazard": "ALERTE MODÉRÉE : Neuroinflammation microgliale M1 accrue.",
        "stable_hazard": "SITUATION STABLE : Paramètres physiologiques dans les limites tolérées.",
        "max_bbb": "Fuite BHE Max",
        "max_m1": "Activation M1 Max",
        "max_heat": "Indice de Stress Thermique",
        "protocol_title": "Protocole Préventif et Recommandations Cliniques",
        "pdf_btn": "Exporter le Rapport Diagnostique (PDF)",
        "email_title": "Envoi d'Alerte Automatique Email & Mobile",
        "email_placeholder": "Entrez l'adresse email institutionnelle...",
        "email_send": "Envoyer l'Alerte",
        "lit_title": "Références Scientifiques et Bibliographie",
        "expander_title": "Formulation Mathématique et Équations Différentielles",
        "guide_title": "Guide d'Utilisation & Utilité des Moteurs Climatiques",
        "conclusion_title": "Synthèse Clinique & Conclusion de la Simulation",
        "interp_title": "Analyse Pathocinétique Spécifique de la Zone",
        "tab_sim": "🧪 Simulateur", "tab_causes": "🌍 Causes des vagues de chaleur & Leçons climatiques", "tab_aware": "📣 Campagne de sensibilisation",
        "tab_guide": "💬 Assistant guide", "tab_src": "📚 Sources",
        "epoch_title": "Comparaison Passé · Présent · Futur (calculée)", "compare_title": "Outils de comparaison de deux régions",
        "assistant_title": "Assistant guide",
    },
    "AR": {
        "title": "محاكي التهاب الأعصاب والإجهاد الحراري وموجات البرد",
        "subtitle": "منصة بحثية في ماجستير علم الأعصاب | محرك كوبرنيكوس ERA5 الفيزيائي",
        "disclaimer": "إخلاء مسؤولية أكاديمي: نموذج حاسوبي مبني على الأدبيات العلمية المحكمة. مخصص لأغراض البحث والتقييم وليس جهازاً تشخيصياً طبياً.",
        "mode_fc": "التنبؤ الاستباقي (نموذج الـ 7 أيام)",
        "mode_ar": "الأرشيف التاريخي كوبرنيكوس ERA5 (إعادة التحليل)",
        "mode_cc": "نموذج توقعات التغير المناخي 2050 (المستقبل)",
        "lang_select": "لغة الواجهة",
        "single_view": "تحليل منطقة واحدة",
        "dual_view": "تحليل مقارن لمنطقتين",
        "run_btn": "تشغيل المحاكاة",
        "reset_btn": "إعادة ضبط",
        "search_label": "ابحث عن أي مدينة أو بلد في العالم:",
        "high_hazard": "تنبيه حرج: توقع اختراق حاد للحاجز الدموي الدماغي.",
        "mod_hazard": "تنبيه متوسط: ارتفاع نشاط الخلايا الدبقية المجهرية M1.",
        "stable_hazard": "استقرار فيزيولوجي: المؤشرات ضمن الحدود الطبيعية.",
        "max_bbb": "أقصى تسرب للحاجز الدماغي",
        "max_m1": "أقصى تنشيط للخلايا M1",
        "max_heat": "مؤشر الإجهاد الحراري",
        "protocol_title": "البروتوكولات الوقائية والتوصيات السريرية",
        "pdf_btn": "تصدير التقرير التشخيصي (PDF)",
        "email_title": "إرسال التنبيه المبكر عبر البريد الإلكتروني والهاتف",
        "email_placeholder": "أدخل البريد الإلكتروني المؤسسي...",
        "email_send": "إرسال التنبيه",
        "lit_title": "المراجع والمصادر العلمية المحكمة",
        "expander_title": "المعادلات التفاضلية والصياغة الرياضية",
        "guide_title": "دليل الاستخدام وأهمية محركات المناخ",
        "conclusion_title": "الاستنتاج السريري وملخص المحاكاة",
        "interp_title": "تحليل المسار الفيزيائي المحدد للمنطقة",
        "tab_sim": "🧪 المحاكي", "tab_causes": "🌍 أسباب موجات الحر ودروس مناخية", "tab_aware": "📣 حملة التوعية",
        "tab_guide": "💬 المساعد الإرشادي", "tab_src": "📚 المصادر",
        "epoch_title": "مقارنة الماضي · الحاضر · المستقبل (محسوبة)", "compare_title": "أدوات مقارنة منطقتين",
        "assistant_title": "المساعد الإرشادي",
    },
}

SHEAR_MULT = {
    "Normotensive (~120 mmHg)": 1.0,
    "Elevated BP (~135 mmHg)": 1.35,
    "Severely Elevated (~180 mmHg)": 2.10,
}

COHORTS = {
    "Baseline (Young, Healthy)": dict(bbb=0.08, m1=0.12, older=False, metabolic=False),
    "Senior Population (65+ yrs)": dict(bbb=0.16, m1=0.15, older=True, metabolic=False),
    "Chronic Metabolic/Vascular Risk": dict(bbb=0.12, m1=0.30, older=False, metabolic=True),
    "Compounded Risk (Senior + Metabolic)": dict(bbb=0.24, m1=0.36, older=True, metabolic=True),
}

CITATIONS = [
    "Kiyatkin EA (2010). Brain temperature homeostasis: physiological fluctuations and pathological shifts. Front Biosci 15:73-92.",
    "Sharma HS, Johanson CE (1998). Heat stress and blood-brain barrier permeability under physiological variations. Med Intell Unit 12:112-134.",
    "Montagne A, et al. (2015). Blood-brain barrier breakdown in the aging human hippocampus. Neuron 85(2):296-302.",
    "Perry VH, Holmes C (2014). Microglial priming in neurodegenerative disease. Nat Rev Neurol 10(4):217-224.",
]

EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")

# ---------------------------------------------------------------------------
# CLINICAL STYLING & LAYOUT CONFIGURATION
# ---------------------------------------------------------------------------
st.set_page_config(page_title="Heat & Cold-Wave Neuroinflammation Simulator | Neuro-Protection", page_icon="🧠", layout="wide")
sns.set_theme(style="whitegrid")

st.markdown(
    """
    <style>
        html, body, [class*="css"] {
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif !important;
            color: #0F172A;
        }
        .stButton>button {
            font-weight: 600 !important;
            border-radius: 6px !important;
            background-color: #0F172A !important;
            color: #FFFFFF !important;
            border: 1px solid #1E293B !important;
            transition: all 0.15s ease-in-out !important;
        }
        .stButton>button:hover {
            background-color: #1E293B !important;
            border-color: #334155 !important;
            color: #FFFFFF !important;
        }
        .clinical-card {
            background-color: #F8FAFC;
            border-left: 4px solid #0F172A;
            border-radius: 4px;
            padding: 14px 18px;
            margin-bottom: 12px;
            box-shadow: 0 1px 2px 0 rgba(0, 0, 0, 0.03);
        }
        .clinical-card-title {
            font-size: 0.925rem;
            font-weight: 700;
            color: #0F172A;
            text-transform: uppercase;
            letter-spacing: 0.03em;
            margin-bottom: 4px;
        }
        .clinical-card-body {
            font-size: 0.90rem;
            color: #334155;
            line-height: 1.5;
        }
        .conclusion-box {
            background-color: #F1F5F9;
            border: 1px solid #CBD5E1;
            border-radius: 6px;
            padding: 16px;
            margin-top: 15px;
            font-size: 0.925rem;
            line-height: 1.6;
            color: #0F172A;
        }
        [data-testid="stMetricValue"] {
            font-size: 1.5rem !important;
            font-weight: 700 !important;
            color: #0F172A !important;
        }
        .stButton>button, .stDownloadButton>button { min-height: 2.8rem; }
        @media (max-width: 640px) {
            .block-container { padding: 1rem 0.6rem 3rem !important; }
            h1 { font-size: 1.45rem !important; } h2, h3 { font-size: 1.15rem !important; }
            [data-testid="stMetricValue"] { font-size: 1.25rem !important; }
            button[data-baseweb="tab"] { padding: 0.4rem 0.55rem; font-size: 0.8rem; }
            [data-testid="stDataFrame"] { overflow-x: auto; }
        }
    </style>
    """,
    unsafe_allow_html=True,
)

lang = st.sidebar.selectbox(I18N["EN"]["lang_select"], ["EN", "FR", "AR"], index=0)
t = I18N[lang]

if lang == "AR":
    st.markdown("<style>body { direction: rtl; text-align: right; }</style>", unsafe_allow_html=True)

st.title(t["title"])
st.caption(t["subtitle"])
st.info(t["disclaimer"])

# ---------------------------------------------------------------------------
# SIDEBAR NEURO-ASSISTANT HUB
# ---------------------------------------------------------------------------

SOURCES = {
    "Brain, blood-brain barrier & microglia (model basis)": [
        "Kiyatkin EA (2010). Brain temperature homeostasis: physiological fluctuations and pathological shifts. Front Biosci 15:73-92.",
        "Sharma HS, Johanson CE (1998). Heat stress and blood-brain barrier permeability under physiological variations. Med Intell Unit 12:112-134.",
        "Sharma HS, Hoopes PJ (2003). Hyperthermia induced pathophysiology of the central nervous system. Int J Hyperthermia 19(3):325-354.",
        "Montagne A, et al. (2015). Blood-brain barrier breakdown in the aging human hippocampus. Neuron 85(2):296-302.",
        "Perry VH, Holmes C (2014). Microglial priming in neurodegenerative disease. Nat Rev Neurol 10(4):217-224.",
    ],
    "Heatwaves, climate change & health": [
        "IPCC (2021). Climate Change 2021: The Physical Science Basis. Working Group I contribution to the Sixth Assessment Report. Cambridge University Press.",
        "IPCC (2022). Climate Change 2022: Impacts, Adaptation and Vulnerability. Working Group II contribution to the Sixth Assessment Report. Cambridge University Press.",
        "Meehl GA, Tebaldi C (2004). More intense, more frequent, and longer lasting heat waves in the 21st century. Science 305:994-997.",
        "Perkins-Kirkpatrick SE, Lewis SC (2020). Increasing trends in regional heatwaves. Nat Commun 11:3357.",
        "Fischer EM, Schaer C (2010). Consistent geographical patterns of changes in high-impact European heatwaves. Nat Geosci 3:398-403.",
        "Seneviratne SI, et al. (2006). Land-atmosphere coupling and climate change in Europe. Nature 443:205-209.",
        "Philip SY, et al. (2022). Rapid attribution analysis of the extraordinary heat wave on the Pacific Coast of the US and Canada in June 2021. Earth Syst Dyn 13:1689-1713.",
        "Sherwood SC, Huber M (2010). An adaptability limit to climate change due to heat stress. PNAS 107:9552-9555.",
        "Oke TR (1982). The energetic basis of the urban heat island. Q J R Meteorol Soc 108:1-24.",
        "Robine JM, et al. (2008). Death toll exceeded 70,000 in Europe during the summer of 2003. C R Biol 331(2):171-178.",
        "Ballester J, et al. (2023). Heat-related mortality in Europe during the summer of 2022. Nat Med 29:1857-1866.",
        "Gasparrini A, et al. (2015). Mortality risk attributable to high and low ambient temperature: a multicountry observational study. Lancet 386:369-375.",
        "Zhao Q, et al. (2021). Global, regional, and national burden of mortality associated with non-optimal ambient temperatures from 2000 to 2019. Lancet Planet Health 5:e415-e425.",
        "Kovats RS, Hajat S (2008). Heat stress and public health: a critical review. Annu Rev Public Health 29:41-55.",
        "Romanello M, et al. (2023). The 2023 report of the Lancet Countdown on health and climate change. Lancet 402:2346-2394.",
    ],
    "Air pollution, tropospheric ozone & the ozone layer": [
        "WHO (2021). WHO global air quality guidelines: particulate matter (PM2.5 and PM10), ozone, nitrogen dioxide, sulfur dioxide and carbon monoxide. Geneva: World Health Organization.",
        "Jacob DJ, Winner DA (2009). Effect of climate change on air quality. Atmos Environ 43:51-63.",
        "WMO/UNEP (2022). Scientific Assessment of Ozone Depletion: 2022. GAW Report No. 278. World Meteorological Organization.",
        "UNEP (1987). Montreal Protocol on Substances that Deplete the Ozone Layer.",
    ],
    "Data, prevention & occupational guidance": [
        "Hersbach H, et al. (2020). The ERA5 global reanalysis. Q J R Meteorol Soc 146:1999-2049 (Copernicus Climate Change Service).",
        "Zippenfenig P (2023). Open-Meteo.com Weather API (forecast, archive and air-quality endpoints; air quality based on Copernicus CAMS).",
        "WHO Regional Office for Europe (2021). Heat and health in the WHO European Region: updated evidence for effective prevention.",
        "Matthies F, et al. (2008). Heat-Health Action Plans: guidance. WHO Regional Office for Europe.",
        "Jacklitsch B, et al. (2016). Criteria for a Recommended Standard: Occupational Exposure to Heat and Hot Environments. NIOSH, DHHS (NIOSH) Publication 2016-106.",
        "ISO 7243:2017. Ergonomics of the thermal environment - Assessment of heat stress using the WBGT (wet bulb globe temperature) index.",
    ],
}
ALL_SOURCES = [x for grp in SOURCES.values() for x in grp]

SEO_DESC = ("Interactive computational-neuroscience simulator: heat waves, cold waves, ozone and PM2.5 pollution and climate "
            "change 2050 versus blood-brain barrier leakage and M1 microglial neuroinflammation. Copernicus ERA5, Open-Meteo, "
            "two-region comparison, 48-hour prevention, alerts and PDF reports.")
SEO_KEYWORDS = ("neuroinflammation, blood-brain barrier, BBB leakage, microglia M1, heat wave, cold wave, heat stress, "
                "climate change 2050, ozone, PM2.5, ERA5, Open-Meteo, heat stroke prevention, computational neuroscience, "
                "heatwave health risk, climate and brain health")


def embed_html(html: str, height: int = 0) -> None:
    """Embed a small HTML/JS snippet; never crash the app if the component API changes."""
    if hasattr(st, "iframe"):          # Streamlit >= 1.5x (components.v1.html is deprecated)
        try:
            st.iframe(html, height=max(1, int(height)))
            return
        except Exception:
            pass
    if components is None:
        return
    try:
        components.html(html, height=height)
    except Exception:
        pass


def inject_seo() -> None:
    meta = {"title": "Heat & Cold-Wave Neuroinflammation Simulator", "description": SEO_DESC, "keywords": SEO_KEYWORDS}
    ld = {"@context": "https://schema.org", "@type": "WebApplication", "name": meta["title"], "description": SEO_DESC,
          "applicationCategory": "EducationalApplication", "keywords": SEO_KEYWORDS, "inLanguage": ["en", "fr", "ar"]}
    js = """<script>
    try {
      const m = __META__, ld = __LD__, d = window.parent.document;
      d.title = m.title;
      const add = (k, n, c) => { let e = d.head.querySelector('meta[' + k + '="' + n + '"]');
        if (!e) { e = d.createElement('meta'); e.setAttribute(k, n); d.head.appendChild(e); }
        e.setAttribute('content', c); };
      add('name','description',m.description); add('name','keywords',m.keywords); add('name','robots','index, follow');
      add('property','og:title',m.title); add('property','og:description',m.description); add('property','og:type','website');
      add('name','twitter:card','summary'); add('name','theme-color','#0F172A'); add('name','mobile-web-app-capable','yes');
      add('name','apple-mobile-web-app-capable','yes');
      if (!d.head.querySelector('link[rel="manifest"]')) { const l = d.createElement('link'); l.rel = 'manifest';
        l.href = '/app/static/manifest.json'; d.head.appendChild(l); }
      let s = d.getElementById('ld-json');
      if (!s) { s = d.createElement('script'); s.id = 'ld-json'; s.type = 'application/ld+json'; d.head.appendChild(s); }
      s.textContent = JSON.stringify(ld);
    } catch (e) {}
    </script>"""
    embed_html(js.replace("__META__", json.dumps(meta)).replace("__LD__", json.dumps(ld)), 0)


inject_seo()


def push_component(title: str, body: str, nonce: str, fire: bool) -> None:
    html = """<div style="font-family:sans-serif;font-size:14px">
    <button id="b" style="padding:10px 14px;border-radius:8px;border:1px solid #888;cursor:pointer">
    🔔 Enable browser / mobile notifications</button> <span id="s"></span></div>
    <script>
    const T=__T__, B=__B__, N=__N__, F=__F__, st=document.getElementById('s');
    let P=window.parent; try { P.document; } catch(e) { P=window; }
    const fire=()=>{ try { new P.Notification(T,{body:B}); return true; } catch(e) { return false; } };
    if(!('Notification' in P)){ st.textContent='Push not supported on this device/browser - use e-mail.'; }
    else {
      st.textContent='Permission: '+P.Notification.permission;
      try { if(F && P.Notification.permission==='granted' && P.sessionStorage.getItem('n')!==N){
        if(fire()){ P.sessionStorage.setItem('n',N); st.textContent='Notification sent.'; } } } catch(e){}
      document.getElementById('b').onclick=()=>{ P.Notification.requestPermission().then(r=>{
        st.textContent='Permission: '+r; if(r==='granted' && F){ fire(); } }); };
    }
    </script>"""
    html = (html.replace("__T__", json.dumps(title)).replace("__B__", json.dumps(body))
            .replace("__N__", json.dumps(nonce)).replace("__F__", "true" if fire else "false"))
    embed_html(html, 70)


def oxidative_load(o3: float, pm: float) -> float:
    """Pollution multiplier (1.0 = at or below WHO 2021 reference levels)."""
    return 1.0 + 0.6 * max(0.0, o3 - O3_REF) / 100.0 + 0.25 * max(0.0, pm - PM_REF) / 15.0


def frailty_2050(d_t: float) -> float:
    return 1.0 + 0.08 * d_t + 0.004 * O3_PER_C * d_t


def epoch_mode_key(mode: str) -> str:
    return {t["mode_fc"]: "Present", t["mode_ar"]: "Past", t["mode_cc"]: "Future"}[mode]


HUB_BLURB = {
    "Past": "**Copernicus ERA5 historical engine** - reconstructs archived heat/cold events over your archive window "
            "(default 1-20 Jul 2025). Pollution is not applied to archive runs.",
    "Present": "**Open-Meteo real-time engine** - 7-day forecast plus live ozone / PM2.5. Flags the 48-hour pre-cooling window.",
    "Future": "**Climate 2050 engine** - +2.45 °C, humidity x1.08, ozone +2.0 and PM2.5 +0.5 µg/m³ per °C, and a "
              "microvascular-frailty factor that slows barrier repair.",
}


def hub_epoch(data: dict, key: str) -> None:
    for i, r in enumerate(data["reports"]):
        e = r["epochs"].get(key)
        st.markdown(f"**Region {i + 1} ({r['name']})**")
        if not e:
            st.caption("Epoch unavailable (data source error): " + str(r["epochs"].get("errors", {}).get(key, "")))
            continue
        a = e["assessment"]
        st.markdown(f"* Peak BBB permeability: **{a['max_bbb'] * 100:.1f}%**\n* Peak M1 polarization: **{a['max_m1'] * 100:.1f}%**\n"
                    f"* Risk level: **{a['level']}**\n* Tmax / Tmin: {a['max_temp']:.1f} / {a['min_temp']:.1f} °C")


# ----------------------------------------------------------------- knowledge pages
def render_causes() -> None:
    st.header("🌍 Why heatwaves happen - and why it matters for the brain")
    st.caption("Educational lessons linked to the simulator's engines. Sources are listed in the 📚 Sources tab.")
    with st.expander("1. What is a heatwave (and a cold wave)?", expanded=True):
        st.markdown(
            "There is no single global definition. Most services call it a **heatwave** when temperatures stay above a local "
            "threshold (for example the local 90th-95th percentile) for **at least 2-3 consecutive days**; a **cold wave** is the "
            "mirror case. Danger depends on **humidity, night-time temperature, duration and who is exposed** - not only the daily "
            "maximum. This simulator therefore combines temperature, humidity, duration, blood pressure and risk cohort "
            "(Sherwood & Huber 2010; Kovats & Hajat 2008).")
    with st.expander("2. Physical causes of heatwaves"):
        st.markdown(
            "* **Atmospheric blocking / heat domes** - a persistent high-pressure ridge causes subsiding, clear, stagnant air that "
            "heats up day after day (e.g. the 2021 Pacific North-West event, Philip et al. 2022).\n"
            "* **Dry soils** - when soil moisture is gone, solar energy heats the air instead of evaporating water; drought and "
            "heatwaves reinforce each other (Seneviratne et al. 2006).\n"
            "* **Warm advection** - hot air masses carried from deserts or heated regions.\n"
            "* **Humidity** - moist heat reduces sweat evaporation; the physiological limit is set by wet-bulb conditions "
            "(Sherwood & Huber 2010).\n"
            "* **Urban heat island** - concrete, asphalt and lack of vegetation store heat and keep nights hot (Oke 1982).\n"
            "* **Large-scale modes** (e.g. ENSO) shift where and when extremes occur.")
    with st.expander("3. How climate change loads the dice"):
        st.markdown(
            "Greenhouse gases (CO₂, CH₄, N₂O) trap heat and raise the baseline. The IPCC AR6 concludes it is **virtually certain** "
            "that hot extremes have become more frequent and more intense across most land regions since the 1950s, and that "
            "human influence is the main driver. Heatwaves are projected to become longer, hotter and more frequent "
            "(Meehl & Tebaldi 2004; Perkins-Kirkpatrick & Lewis 2020; IPCC 2021). The simulator's **2050 engine** adds "
            "+2.45 °C, a humidity shift and a pollution/frailty penalty as an explicit, editable scenario - not a forecast.")
    with st.expander("4. Ozone: the 'ozone hole' is NOT the same as ground-level ozone"):
        st.markdown(
            "* **Stratospheric ozone layer (10-50 km)** - protective: absorbs harmful UV-B. Chlorine/bromine from CFCs created the "
            "'ozone hole' over Antarctica. The **Montreal Protocol (1987)** phased out these substances; the WMO/UNEP 2022 "
            "assessment projects recovery to 1980 levels around **2040 (global), 2045 (Arctic) and 2066 (Antarctic)**.\n"
            "* **Tropospheric (ground-level) ozone** - harmful pollutant. Formed when NOx and volatile organic compounds react in "
            "**sunlight and heat**, so it **peaks during heatwaves** (the *climate penalty*, Jacob & Winner 2009). "
            "WHO 2021 guidelines: **60 µg/m³ peak-season** and 100 µg/m³ 8-hour mean.\n"
            "* The ozone hole is mainly a UV problem and a success story of international action; ground-level ozone is the one "
            "that interacts with heat and is used as a pollution input in this simulator.")
    with st.expander("5. Particulate matter (PM2.5) and compound hazards"):
        st.markdown(
            "PM2.5 comes from traffic, industry, wildfires, desert dust and stagnant air. Heatwaves often bring **wildfire smoke, "
            "dust and stagnation**, so heat and pollution hit together. WHO 2021 guidelines: **15 µg/m³ (24 h)** and **5 µg/m³ "
            "(annual)**. In the model, ozone and PM2.5 above these references raise the barrier-opening gain and microglial "
            "response (oxidative-load multiplier).")
    with st.expander("6. Health burden: heat AND cold"):
        st.markdown(
            "* Europe: **> 70,000** excess deaths in the 2003 summer (Robine et al. 2008); about **61,600** heat-related deaths in "
            "summer 2022 (Ballester et al. 2023).\n"
            "* Across 13 countries, **most temperature-related deaths were attributed to moderate cold** rather than extreme heat "
            "(Gasparrini et al. 2015); global estimates agree that cold still dominates but heat's share is growing (Zhao et al. 2021).\n"
            "* Most at risk: **older adults, people with hypertension, diabetes, cardiovascular or kidney disease, outdoor and "
            "industrial workers, children, people living alone, and low-income households without cooling** (Lancet Countdown 2023).\n"
            "* Brain mechanism studied here: thermal stress opens the **blood-brain barrier**; leaked proteins prime **M1 microglia** "
            "(Sharma & Johanson 1998; Kiyatkin 2010; Perry & Holmes 2014); ageing and hypertension amplify vulnerability "
            "(Montagne et al. 2015).")
    with st.expander("7. Solutions: adaptation and mitigation"):
        st.markdown(
            "* **Early warning + Heat-Health Action Plans** (WHO Europe 2008, 2021).\n"
            "* **Cool the city:** trees, parks, blue spaces, cool/white roofs, shaded streets, public cooling centres.\n"
            "* **Protect workers:** WBGT-based work/rest cycles, water, shade, acclimatisation (NIOSH 2016; ISO 7243).\n"
            "* **Clean the air:** cut NOx/VOC and particulate emissions; limit open burning.\n"
            "* **Cut emissions:** the only lever that reduces the long-term trend (Paris Agreement, IPCC AR6).\n"
            "* **Look after each other:** check on older and isolated neighbours during every heatwave and cold wave.")
    st.markdown("#### 🎛️ Climate lever explorer (what-if)")
    c1, c2, c3 = st.columns(3)
    d_t = c1.slider("Warming ΔT (°C)", 0.0, 4.0, DT_2050, 0.05, key="lever_dt")
    o3 = c2.slider("Ambient ozone today (µg/m³)", 20, 200, 60, key="lever_o3")
    pm = c3.slider("PM2.5 today (µg/m³)", 2, 100, 15, key="lever_pm")
    ox_now, ox_fut = oxidative_load(o3, pm), oxidative_load(o3 + O3_PER_C * d_t, pm + PM_PER_C * d_t)
    m1, m2, m3 = st.columns(3)
    m1.metric("Pollution load today", f"x{ox_now:.2f}")
    m2.metric("Pollution load with warming", f"x{ox_fut:.2f}", f"{ox_fut - ox_now:+.2f}", delta_color="inverse")
    m3.metric("Microvascular frailty (barrier repair slower by)", f"x{frailty_2050(d_t):.2f}")
    st.caption("These multipliers feed the ODE gains and repair rates of the 2050 engine (assumptions, not fitted to patient data).")


CAMPAIGN_AUDIENCES = {
    "General public": [
        "Check the 7-day forecast every morning in a heatwave or cold wave; act **48 hours before** the peak.",
        "Heat: keep rooms below 24 °C (close shutters by day, ventilate at night), drink regularly, light clothes, avoid 11:00-17:00 exertion.",
        "Cold: heat rooms **gradually above 19 °C**, layer clothing, avoid sudden hot-cold switches.",
        "Never leave children, pets or people in parked vehicles.",
    ],
    "Older adults & caregivers": [
        "Thirst and temperature sensing weaken with age: **drink on a schedule**, do not wait for thirst (within doctor's fluid limits).",
        "Agree a **daily check-in call**; visit isolated neighbours twice a day in a heatwave.",
        "Ask the doctor/pharmacist how heat or dehydration affects your medicines (blood-pressure drugs, diuretics).",
        "Log blood pressure twice a day if hypertensive; sleep in the coolest room.",
    ],
    "Parents & schools": [
        "Move sport and play to early morning; provide shade and water stations; shorten outdoor time at the peak.",
        "Teach the warning signs: dizziness, headache, nausea, confusion, very hot dry or red skin.",
        "Class activity: read the local forecast, predict the risk level, then compare with the simulator.",
    ],
    "Workers & industry": [
        "Use **WBGT-based work/rest cycles**, acclimatise new workers over 1-2 weeks, provide water, shade and cooling breaks (NIOSH 2016; ISO 7243).",
        "Shift heavy tasks to cooler hours; buddy system; supervisors trained to spot heat illness.",
        "Employers: integrate the 48-hour alert into shift planning; review PPE heat load; record incidents.",
    ],
    "Clinicians & health facilities": [
        "Flag high-risk patients (age, hypertension, diabetes, renal, psychiatric medication) before the window opens.",
        "Review medicines that impair thermoregulation or hydration; plan extra capacity at the forecast peak.",
        "Use the PDF report and alert e-mail as a briefing note (research tool - not a diagnostic device).",
    ],
    "Authorities & NGOs": [
        "Trigger the local Heat-Health Action Plan when the model flags a prevention window; open cooling centres and extend pool/park hours.",
        "Target outreach by neighbourhood heat and vulnerability maps; multilingual messages (EN/FR/AR below).",
        "Measure the campaign: alerts sent, check-ins completed, ER heat visits, hospital admissions, awareness surveys.",
    ],
}
SLOGANS = {
    "EN": "Cool early. Drink early. Check on others early. #HeatSafe48",
    "FR": "Rafraîchir tôt. Boire tôt. Veiller sur les autres tôt. #HeatSafe48",
    "AR": "برّد مبكراً. اشرب مبكراً. تفقّد الآخرين مبكراً. #HeatSafe48",
}


def share_text(data: dict) -> str:
    parts = []
    for r in data["reports"]:
        a = r["assessment"]
        parts.append(f"{r['name']}: risk {a['level']}, peak BBB {a['max_bbb'] * 100:.0f}%, peak M1 {a['max_m1'] * 100:.0f}%")
    return ("⚠️ Neuro-Protection alert - " + " | ".join(parts) + ". Act 48 h before the peak: cool the home below 24 °C, "
            "hydrate, protect seniors. " + SLOGANS["EN"])


def render_campaign() -> None:
    st.header("📣 #HeatSafe48 - Awareness Campaign Toolkit")
    st.markdown("**Idea:** the brain's protective barrier can be shielded if people act **48 hours before** the peak. "
                "One simple, memorable message - adapted to every audience, language and weather extreme.")
    for lng, txt in SLOGANS.items():
        st.markdown(f"**{lng}** - {txt}")
    aud = st.selectbox("Choose the audience", list(CAMPAIGN_AUDIENCES.keys()), key="aud_pick")
    for tip in CAMPAIGN_AUDIENCES[aud]:
        st.markdown(f"* {tip}")
    st.markdown("#### 🚦 Alert levels (aligned with the simulator)")
    st.markdown("| Level | Model trigger | Public message |\n|---|---|---|\n"
                "| 🟢 Baseline | BBB ≤ 20 % and M1 ≤ 15 % | Routine hydration and comfort |\n"
                "| 🟠 Moderate | BBB > 20 % or M1 > 15 % | Start pre-cooling / re-warming, protect vulnerable people |\n"
                "| 🔴 High | BBB > 50 % or M1 > 40 % | Act now: cool space, fluids, check-ins, limit exertion, alert clinicians |")
    st.markdown("#### 🚑 Know the warning signs")
    st.markdown("* **Heat exhaustion:** heavy sweating, weakness, headache, nausea, cramps - move to a cool place, drink, cool the skin.\n"
                "* **Heat stroke (emergency):** confusion, fainting, seizures, very high body temperature, hot dry skin - **call local "
                "emergency services immediately**, cool the person actively while waiting.\n"
                "* **Cold exposure:** shivering, slurred speech, drowsiness - warm gradually, seek medical help.")
    st.markdown("#### 🧰 Campaign ideas that work")
    st.markdown("* **Neighbour check-in buddy:** every older resident has two named buddies.\n"
                "* **Cool-room map:** libraries, malls, mosques/churches, community centres listed on one shared map.\n"
                "* **School challenge:** pupils track the forecast and the simulator's risk level for a week.\n"
                "* **Workplace '10-minute rule':** water-shade-rest every hour at high WBGT.\n"
                "* **Pharmacy window stickers** with the three-line message in local languages.\n"
                "* **Radio/WhatsApp/SMS alerts** with the 48-hour window date (text generator below).")
    d = st.session_state.get("last_analysis")
    if d:
        st.markdown("#### ✉️ Ready-to-share message from your latest simulation")
        msg = share_text(d)
        st.text_area("Copy and share", msg, height=110, key="campaign_share")
        st.link_button("Share on WhatsApp", "https://wa.me/?text=" + quote(msg))
    else:
        st.info("Run a simulation to generate a ready-to-share alert message.")


def render_sources() -> None:
    st.header("📚 Sources & Bibliography")
    for grp, items in SOURCES.items():
        st.subheader(grp)
        for c in items:
            st.markdown(f"* {c}")
    st.caption("Please verify volume/page/DOI details on the publisher's page before formal citation. "
               "The model is phenomenological: rate constants are illustrative and not fitted to patient data. "
               "Research and educational use only; not medical advice.")


def _snapshot():
    d = st.session_state.get("last_analysis")
    if not d:
        return None
    out = []
    for r in d["reports"]:
        a = r["assessment"]
        out.append(f"**{r['name']}** - risk **{a['level']}**, peak BBB leakage **{a['max_bbb'] * 100:.1f}%**, peak M1 "
                   f"**{a['max_m1'] * 100:.1f}%**, Tmax {a['max_temp']:.1f} °C / Tmin {a['min_temp']:.1f} °C.")
    return "\n\n".join(out)


def _ans_result():
    snap = _snapshot()
    return ("Your latest simulation:\n\n" + snap) if snap else "Run a simulation first (sidebar → Run Simulation), then ask again."


KB = [
    (("how to use", "how do i", "start", "guide", "tutorial", "use the app", "use this"),
     "1) Pick a **Climate Engine** (7-day forecast, ERA5 archive or 2050). 2) Choose **single or dual region**, search a place or "
     "click the map to drop the pin. 3) Select blood-pressure and population profiles. 4) Press **Run Simulation**. You get the "
     "trajectory, protocols, Past/Present/Future comparison, PDF and alert e-mail."),
    (("bbb", "blood-brain", "blood brain", "barrier"),
     "The **blood-brain barrier** is the tightly sealed endothelium that protects the brain. Heat above ~25 °C or cold below ~10 °C "
     "and high blood pressure can loosen tight junctions (claudin-5, occludin), letting plasma proteins leak in "
     "(Sharma & Johanson 1998; Kiyatkin 2010)."),
    (("m1", "microglia", "neuroinflammation", "inflammation"),
     "**Microglia** are the brain's immune cells. Leaked proteins push them toward the pro-inflammatory **M1** state; ageing makes "
     "them 'primed' and more reactive (Perry & Holmes 2014)."),
    (("risk level", "threshold", "high risk", "moderate", "baseline", "classif"),
     "**High:** BBB > 50 % or M1 > 40 %. **Moderate:** BBB > 20 % or M1 > 15 %. Otherwise **Baseline**."),
    (("prevent", "pre-cool", "precool", "48", "protect"),
     "Act **48 h before the peak**: cool living space below 24 °C, start regular electrolyte hydration, avoid exertion 11:00-17:00, "
     "keep nights below 24 °C. For cold waves, re-warm gradually above 19 °C. (Modelling-based guidance, not medical advice.)"),
    (("senior", "elder", "old", "65", "aged"),
     "Older adults have blunted thirst and temperature sensing and primed microglia: drink on a schedule, arrange daily check-ins, "
     "keep the bedroom cool, review medicines with a clinician."),
    (("hypertens", "blood pressure", "shear"),
     "Higher blood pressure raises shear stress on the barrier (model multiplier 1.0 → 2.10). Log blood pressure twice daily and ask "
     "your prescriber how dehydration affects antihypertensive drugs."),
    (("cold", "winter", "hypotherm", "freez"),
     "Cold waves trigger vasoconstriction and blood-pressure spikes. Keep rooms above 19 °C, re-warm gradually, layer clothes."),
    (("ozone hole", "ozone layer", "montreal", "uv"),
     "The **ozone hole** is stratospheric ozone loss from CFCs (UV-B problem). The Montreal Protocol is healing it: recovery projected "
     "~2040 global, ~2045 Arctic, ~2066 Antarctic (WMO/UNEP 2022). It is different from ground-level ozone."),
    (("ozone", "o3", "smog"),
     "**Ground-level ozone** forms from NOx + VOCs in sunlight and heat, so it peaks in heatwaves. WHO: 60 µg/m³ peak-season. "
     "In the simulator, ozone above 60 µg/m³ increases barrier-opening and microglial gain."),
    (("pm2.5", "pm", "particulate", "wildfire", "smoke", "dust", "pollution", "air quality"),
     "PM2.5 (WHO: 15 µg/m³ 24-h, 5 annual) rises with traffic, industry, wildfires and dust, and often coincides with heatwaves. Values above the "
     "reference raise the model's oxidative-load multiplier."),
    (("2050", "future", "climate change", "warming", "projection"),
     "The **2050 engine** adds +2.45 °C, humidity ×1.08, ozone +2 µg/m³ and PM2.5 +0.5 µg/m³ per °C, and a frailty factor (1 + 0.08·ΔT + "
     "0.004·ΔO₃) that slows barrier repair. It is a scenario, not a forecast."),
    (("cause", "why heat", "heatwave", "heat wave", "heat dome", "urban heat"),
     "Heatwaves come from blocking high pressure (heat domes), dry soils, warm advection, humidity and urban heat islands, made more frequent and "
     "intense by greenhouse-gas warming. See the 🌍 causes tab."),
    (("worker", "industry", "factory", "outdoor work", "wbgt", "employer"),
     "Use WBGT-based work/rest cycles, acclimatisation, water-shade-rest breaks, buddy systems (NIOSH 2016; ISO 7243). Schedule heavy tasks in cooler hours."),
    (("heat stroke", "emergency", "faint", "confus", "ambulance", "symptom", "sign"),
     "Heat stroke is an **emergency**: confusion, fainting, seizures, hot dry skin, very high body temperature. Call local emergency services "
     "and cool the person actively. This app cannot diagnose."),
    (("email", "mail", "alert", "notification", "notify"),
     "Open the **Automated Early-Warning Email** section after a run, enter a recipient and press Dispatch. Real sending needs a Resend key or "
     "SMTP credentials in Streamlit Secrets; otherwise the app runs in simulation mode and shows the exact error of the provider if one occurs."),
    (("source", "paper", "reference", "citation", "cite", "bibliograph"),
     "See the 📚 Sources tab: model basis (Kiyatkin, Sharma, Montagne, Perry), climate/health (IPCC AR6, Robine, Ballester, Gasparrini, Zhao...), "
     "air/ozone (WHO 2021, WMO/UNEP 2022, Jacob & Winner) and data (ERA5, Open-Meteo)."),
    (("accurate", "valid", "limit", "reliable", "diagnos", "medical advice", "trust"),
     "It is a **phenomenological research/education model**: rate constants are illustrative and not fitted to patient data; it is not a "
     "medical device or diagnosis. Use it for risk awareness and teaching."),
    (("my result", "my risk", "result", "summary", "analysis", "simulation", "output"), _ans_result),
]


def assistant_answer(q: str) -> str:
    ql = q.lower()
    best, score = None, 0
    for kws, ans in KB:
        sc = sum(1 for k in kws if k in ql)
        if sc > score:
            best, score = ans, sc
    if best is None:
        return ("I can help with: how to use the app, BBB and microglia, risk levels, prevention (heat and cold), seniors, "
                "hypertension, ozone vs the ozone hole, PM2.5, climate 2050, heatwave causes, workers, emergencies, e-mail alerts, "
                "sources and model limits. Try one of those.")
    return best() if callable(best) else best


def render_assistant() -> None:
    st.header("💬 " + t["assistant_title"])
    st.caption("Rule-based guide (no external AI service): answers come from the model documentation, the cited sources and your "
               "latest simulation. Not medical advice.")
    if "chat" not in st.session_state:
        st.session_state["chat"] = [{"role": "assistant", "content":
                                     "Hello! Ask me about heatwaves, brain risk, prevention, ozone, or how to use the simulator."}]
    for m in st.session_state["chat"]:
        with st.chat_message(m["role"]):
            st.markdown(m["content"])
    q = st.chat_input("Ask a question...", key="guide_chat")
    if q:
        ans = assistant_answer(q)
        st.session_state["chat"] += [{"role": "user", "content": q}, {"role": "assistant", "content": ans}]
        with st.chat_message("user"):
            st.markdown(q)
        with st.chat_message("assistant"):
            st.markdown(ans)


st.sidebar.markdown("---")
st.sidebar.subheader("Neuro-Assistant Hub")

with st.sidebar.popover("Dynamic Hub & Multi-Epoch Reports", width="stretch"):
    st.markdown("### Dynamic Reports & Climate Hub")
    data_hub = st.session_state.get("last_analysis")
    tab_rep, tab_past, tab_pres, tab_fut = st.tabs(["Live Report", "Past (ERA5)", "Present", "Future (2050)"])

    with tab_rep:
        st.markdown("**Session Telemetry & Live Analysis:**")
        if data_hub:
            st.caption(f"**Engine Active:** {data_hub['mode']} · {data_hub.get('stamp', '')}")
            for idx_r, r_hub in enumerate(data_hub["reports"]):
                a_h = r_hub["assessment"]
                st.markdown(f"**Region {idx_r+1} ({r_hub['name']}):**")
                st.markdown(f"* Peak BBB Permeability: **{a_h['max_bbb']*100:.1f}%**")
                st.markdown(f"* Peak M1 Polarization: **{a_h['max_m1']*100:.1f}%**")
                st.markdown(f"* Risk Level: **{a_h['level']}**")
        else:
            st.info("Run a simulation to populate the live report.")

    for tab_x, key_x in ((tab_past, "Past"), (tab_pres, "Present"), (tab_fut, "Future")):
        with tab_x:
            st.markdown(HUB_BLURB[key_x])
            if data_hub:
                hub_epoch(data_hub, key_x)
            else:
                st.info("Run a simulation to compute this epoch.")

# ---------------------------------------------------------------------------
# UNIVERSAL GEOCODING & CLIMATE ENGINE
# ---------------------------------------------------------------------------
def fmt(ts) -> str:
    return pd.Timestamp(ts).strftime("%a %d %b %Y")

@st.cache_data(ttl=3600, show_spinner=False)
def search_location_query(query: str) -> tuple[float, float, str]:
    if not query or not query.strip():
        return 36.8065, 10.1815, "Tunis, Tunisia"
    try:
        geolocator = Nominatim(user_agent="tasnim_copernicus_neuro_v24")
        loc = geolocator.geocode(query, timeout=6, language="en")
        if loc:
            parts = [p.strip() for p in loc.address.split(",")]
            city = parts[0]
            country = parts[-1]
            return float(loc.latitude), float(loc.longitude), f"{city}, {country}"
    except Exception:
        pass
    return 36.8065, 10.1815, query.title()

@st.cache_data(ttl=3600, show_spinner=False)
def reverse_geocode(lat: float, lon: float) -> str:
    try:
        geolocator = Nominatim(user_agent="tasnim_copernicus_neuro_v24")
        loc = geolocator.reverse((lat, lon), timeout=5, language="en")
        if loc and loc.raw.get("address"):
            addr = loc.raw["address"]
            city = addr.get("city") or addr.get("town") or addr.get("village") or addr.get("state")
            country = addr.get("country", "")
            if city and country:
                return f"{city}, {country}"
            if country:
                return f"{country} ({lat:.2f}, {lon:.2f})"
    except Exception:
        pass
    return f"Region ({lat:.2f}, {lon:.2f})"

@st.cache_data(ttl=1800, show_spinner=False)
def fetch_climate(lat: float, lon: float, mode: str, start_iso: str, end_iso: str) -> pd.DataFrame:
    params = {"latitude": lat, "longitude": lon, "daily": "temperature_2m_max,relative_humidity_2m_max", "timezone": "auto"}
    if mode == t["mode_ar"]:
        url = ARCHIVE_URL
        params.update({"start_date": start_iso, "end_date": end_iso})
    else:
        url = FORECAST_URL
        params.update({"forecast_days": 7, "past_days": SPINUP_DAYS})

    resp = requests.get(url, params=params, timeout=15)
    resp.raise_for_status()
    payload = resp.json()
    daily = payload.get("daily")
    if not daily or not daily.get("time"):
        raise RuntimeError("Open-Meteo climate engine returned an empty payload.")

    df = pd.DataFrame({
        "Date": pd.to_datetime(daily["time"]),
        "Max_Temp": pd.to_numeric(daily["temperature_2m_max"], errors="coerce"),
        "Max_Humidity": pd.to_numeric(daily["relative_humidity_2m_max"], errors="coerce"),
    }).interpolate(limit_direction="both")

    if mode == t["mode_cc"]:
        df["Max_Temp"] = df["Max_Temp"] + DT_2050
        df["Max_Humidity"] = np.clip(df["Max_Humidity"] * 1.08, 0, 100)

    return df

# ---------------------------------------------------------------------------
# ODE SIMULATION KINETICS (HEAT & COLD WAVE COUPLING)
# ---------------------------------------------------------------------------
def _rhs(y, t, anomaly, k_bbb, k_m1, bbb_gain, m1_gain, shear):
    bbb, m1 = y
    d_bbb = bbb_gain * anomaly * shear * (1.0 - bbb) - k_bbb * bbb
    d_m1 = m1_gain * bbb * (1.0 - m1) - k_m1 * m1
    return [d_bbb, d_m1]

def _integrate(anomaly_series, bbb_gain, m1_gain, shear, frailty=1.0):
    y = np.array([0.05, 0.01])
    out = []
    for a in anomaly_series:
        k_bbb = (0.28 if a == 0 else 0.05) / frailty
        k_m1 = 0.23 if a == 0 else 0.08
        y = odeint(_rhs, y, [0.0, 1.0], args=(a, k_bbb, k_m1, bbb_gain, m1_gain, shear))[-1]
        y = np.clip(y, 0.0, 1.0)
        out.append(y.copy())
    return np.array(out)

def classify(bbb: float, m1: float) -> str:
    if bbb > BBB_ALERT or m1 > M1_ALERT:
        return "High"
    if bbb > BBB_MOD or m1 > M1_MOD:
        return "Moderate"
    return "Baseline"

def simulate(raw: pd.DataFrame, bbb_gain: float, m1_gain: float, shear: float, mode: str,
             ox: float = 1.0, frailty: float = 1.0) -> pd.DataFrame:
    df = raw.copy()
    bbb_gain, m1_gain = bbb_gain * ox, m1_gain * (1.0 + 0.5 * (ox - 1.0))  # ozone/PM2.5 oxidative load
    
    heat_idx = df["Max_Temp"] + 0.55 * (df["Max_Humidity"] / 100) * (df["Max_Temp"] - 14.5)
    heat_anomaly = np.clip(heat_idx - 25, 0, None)
    cold_anomaly = np.clip(10.0 - df["Max_Temp"], 0, None) * 0.75
    
    df["Heat_Stress_Index"] = heat_idx
    df["Anomaly"] = heat_anomaly + cold_anomaly
    a = df["Anomaly"].values

    std = _integrate(a, bbb_gain, m1_gain, shear, frailty)
    low = _integrate(a, bbb_gain * 0.8, m1_gain * 0.8, shear, frailty)
    high = _integrate(a, bbb_gain * 1.2, m1_gain * 1.2, shear, frailty)

    df["BBB_Leakage"], df["Microglia_M1"] = std[:, 0], std[:, 1]
    df["BBB_Low"], df["BBB_High"] = low[:, 0], high[:, 0]
    df["M1_Low"], df["M1_High"] = low[:, 1], high[:, 1]

    if mode != t["mode_ar"] and len(df) > 7:
        df = df.iloc[-7:].reset_index(drop=True)
    df["Risk"] = [classify(b, m) for b, m in zip(df["BBB_Leakage"], df["Microglia_M1"])]
    return df

def assess(df: pd.DataFrame) -> dict:
    high = df[df["Risk"] == "High"]
    elevated = df[df["Risk"] != "Baseline"]
    min_temp = float(df["Max_Temp"].min())
    max_temp = float(df["Max_Temp"].max())
    is_cold = min_temp < 10.0
    
    return dict(
        level="High" if len(high) else ("Moderate" if len(elevated) else "Baseline"),
        max_anomaly=float(df["Anomaly"].max()),
        max_bbb=float(df["BBB_Leakage"].max()),
        max_m1=float(df["Microglia_M1"].max()),
        min_temp=min_temp,
        max_temp=max_temp,
        is_cold=is_cold,
        peak_bbb_date=df.loc[df["BBB_Leakage"].idxmax(), "Date"],
        peak_m1_date=df.loc[df["Microglia_M1"].idxmax(), "Date"],
        hazard_dates=list(high["Date"]),
        first_risk_date=elevated["Date"].iloc[0] if len(elevated) else None,
        window_start=df["Date"].iloc[0],
    )

def build_protocol(a: dict, cohort_key: str) -> list[tuple[str, str]]:
    c = COHORTS[cohort_key]
    steps: list[tuple[str, str]] = []
    
    if a["is_cold"]:
        steps.append(("Cold-Wave Thermal Protection Protocol", "Maintain indoor ambient temperatures above 19 °C. Rapid cold exposure causes cerebral vasoconstriction and transient blood pressure spikes."))
        steps.append(("Gradual Re-warming Schedule", "Avoid sudden extreme heat exposure after severe cold to prevent reperfusion microvascular stress."))
    
    if a["level"] == "Baseline" and not a["is_cold"]:
        steps.append(("Routine Monitoring Protocol", "Maintain standard hydration schedules and track local daily thermal variations."))
    elif a["level"] != "Baseline":
        start = a["first_risk_date"] - pd.Timedelta(days=2)
        when = "Initiate immediately" if start <= a["window_start"] else f"Initiate on {fmt(start)}"
        steps.append((f"Pre-cooling / Climate Window ({when})", "Cool living quarters (<24 °C) 48h prior to projected thermal peaks to protect barrier structural integrity."))
        steps.append(("Osmotic Hydration Protocol", "Administer 150-250 mL fluids containing electrolytes every 20-30 minutes during acute heat stress."))
        steps.append(("Diurnal Exertion Caps", "Restrict strenuous physical exertion and direct solar exposure between 11:00 and 17:00."))
        steps.append(("Nighttime Recovery & Glymphatic Support", "Maintain ambient sleeping temperatures below 24 °C to preserve glymphatic BBB repair mechanisms."))

    if c["metabolic"]:
        steps.append(("Vascular Hemodynamic Caution", "Log systemic blood pressure twice daily. Dehydration alters antihypertensive drug pharmacokinetics."))
    if c["older"]:
        steps.append(("Senior Clinical Precaution", "Thirst and shivering sensitivities are blunted in older cohorts; do not rely solely on peripheral sensation."))
    return steps

def generate_specific_interpretation(a: dict, location_name: str) -> str:
    max_bbb_pct = a["max_bbb"] * 100
    max_m1_pct = a["max_m1"] * 100
    
    if a["level"] == "High":
        return (
            f"**Pathokinetic Profile for {location_name}:** High-intensity thermal stress resulted in severe endothelial junction opening "
            f"reaching a peak of **{max_bbb_pct:.1f}%** leakage. This caused microglial M1 pro-inflammatory activation (**{max_m1_pct:.1f}%**), "
            f"indicating acute neurovascular risk."
        )
    elif a["level"] == "Moderate":
        return (
            f"**Pathokinetic Profile for {location_name}:** Moderate thermal deviation caused partial tight-junction degradation "
            f"(Peak BBB Leakage: **{max_bbb_pct:.1f}%**). Downstream microglial M1 polarization reached **{max_m1_pct:.1f}%**, requiring cautionary monitoring."
        )
    else:
        return (
            f"**Pathokinetic Profile for {location_name}:** Ambient temperatures remained within homeostatic tolerance. "
            f"BBB permeability stayed minimal at **{max_bbb_pct:.1f}%** and microglial M1 activation at **{max_m1_pct:.1f}%**, reflecting healthy physiological baseline."
        )

def generate_conclusion(a: dict, location_name: str, cohort_key: str, bp_state: str) -> str:
    level = a["level"]
    max_bbb_pct = a["max_bbb"] * 100
    max_m1_pct = a["max_m1"] * 100
    max_heat = a["max_anomaly"]
    
    cold_str = " (with Cold-Wave Stress)" if a["is_cold"] else ""
    
    if level == "High":
        return (
            f"**Synthesis for {location_name}:** Under the selected profile (**{cohort_key}** with **{bp_state}**), "
            f"a severe thermal anomaly peak of **{max_heat:.1f} °C-eq**{cold_str} was modeled. This triggers a critical "
            f"blood-brain barrier disruption of **{max_bbb_pct:.1f}%** and microglial M1 neuroinflammatory activation of **{max_m1_pct:.1f}%**. "
            f"**Conclusion:** Immediate preventive action is required to prevent heat/cold-induced central nervous system stress."
        )
    elif level == "Moderate":
        return (
            f"**Synthesis for {location_name}:** A moderate thermal anomaly of **{max_heat:.1f} °C-eq**{cold_str} was observed. "
            f"BBB permeability increased to **{max_bbb_pct:.1f}%**, accompanied by moderate M1 polarization (**{max_m1_pct:.1f}%**). "
            f"**Conclusion:** Vulnerable individuals (seniors, hypertensive patients) should initiate cautionary pre-cooling/re-warming measures."
        )
    else:
        return (
            f"**Synthesis for {location_name}:** Environmental conditions remained near physiological equilibrium (**{max_heat:.1f} °C-eq** anomaly). "
            f"BBB permeability leakage stayed within baseline bounds (**{max_bbb_pct:.1f}%**). "
            f"**Conclusion:** No acute neuroinflammatory hazard detected. Routine physiological care is sufficient."
        )

# ---------------------------------------------------------------------------
# CHARTS & UNICODE-SAFE FPDF2 ENGINE
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# AIR QUALITY, MULTI-EPOCH ENGINE, COMPARISON TOOLS, RISK MAP
# ---------------------------------------------------------------------------
@st.cache_data(ttl=1800, show_spinner=False)
def fetch_air(lat: float, lon: float):
    """Current ozone and PM2.5 (Open-Meteo / CAMS). Falls back to WHO reference levels (neutral load)."""
    try:
        r = requests.get(AIR_URL, params={"latitude": lat, "longitude": lon, "current": "ozone,pm2_5"}, timeout=12)
        r.raise_for_status()
        c = r.json()["current"]
        return float(c["ozone"]), float(c["pm2_5"]), True
    except Exception:
        return O3_REF, PM_REF, False


def compute_epochs(lat: float, lon: float, c: dict, shear: float, s_iso: str, e_iso: str) -> dict:
    o3, pm, air_ok = fetch_air(lat, lon)
    out = {"air": dict(o3=o3, pm=pm, ok=air_ok), "errors": {}}
    cfg = {
        "Past": (t["mode_ar"], 1.0, 1.0),
        "Present": (t["mode_fc"], oxidative_load(o3, pm), 1.0),
        "Future": (t["mode_cc"], oxidative_load(o3 + O3_PER_C * DT_2050, pm + PM_PER_C * DT_2050), frailty_2050(DT_2050)),
    }
    for key, (mode, oxv, fr) in cfg.items():
        try:
            raw = fetch_climate(lat, lon, mode, s_iso if key == "Past" else "", e_iso if key == "Past" else "")
            df = simulate(raw, c["bbb"], c["m1"], shear, mode, oxv, fr)
            out[key] = dict(df=df, assessment=assess(df), ox=oxv, frailty=fr, mode=mode)
        except Exception as exc:
            out[key] = None
            out["errors"][key] = str(exc)
    return out


def epoch_table(r: dict) -> pd.DataFrame:
    rows = []
    for k in EPOCHS:
        e = r["epochs"].get(k)
        if not e:
            rows.append({"Epoch": EPOCH_LABELS[k], "Peak BBB (%)": None, "Peak M1 (%)": None, "Risk": "unavailable"})
            continue
        a = e["assessment"]
        rows.append({"Epoch": EPOCH_LABELS[k], "Tmax (°C)": round(a["max_temp"], 1), "Tmin (°C)": round(a["min_temp"], 1),
                     "Peak BBB (%)": round(a["max_bbb"] * 100, 1), "Peak M1 (%)": round(a["max_m1"] * 100, 1),
                     "Risk": a["level"], "Pollution load x": round(e["ox"], 2), "Vascular frailty x": round(e["frailty"], 2)})
    return pd.DataFrame(rows)


def plot_epochs(ep: dict, name: str):
    fig, ax = plt.subplots(figsize=(8, 3.6))
    xs, w = np.arange(3), 0.36
    bbb = [ep[k]["assessment"]["max_bbb"] * 100 if ep.get(k) else 0 for k in EPOCHS]
    m1 = [ep[k]["assessment"]["max_m1"] * 100 if ep.get(k) else 0 for k in EPOCHS]
    ax.bar(xs - w / 2, bbb, w, color="#2563EB", label="Peak BBB leakage (%)")
    ax.bar(xs + w / 2, m1, w, color="#0F172A", label="Peak M1 polarization (%)")
    ax.axhline(50, color="#2563EB", ls=":", lw=1)
    ax.axhline(40, color="#0F172A", ls=":", lw=1)
    for i, k in enumerate(EPOCHS):
        if ep.get(k):
            ax.text(i, max(bbb[i], m1[i]) + 2, ep[k]["assessment"]["level"], ha="center", fontsize=9, fontweight="bold")
            ax.text(i - w / 2, bbb[i] / 2, f"{bbb[i]:.0f}", ha="center", color="white", fontsize=8)
            ax.text(i + w / 2, m1[i] / 2, f"{m1[i]:.0f}", ha="center", color="white", fontsize=8)
    ax.set_xticks(xs)
    ax.set_xticklabels(["Past\n(ERA5)", "Present\n(7-day)", "Future\n(2050)"])
    ax.set_ylim(0, 105)
    ax.set_ylabel("%")
    ax.set_title(f"Past · Present · Future: {name}", fontweight="bold")
    ax.legend(fontsize=8, loc="upper left")
    fig.tight_layout()
    return fig


def plot_comparison(reports: list):
    fig, axes = plt.subplots(1, 2, figsize=(11, 3.8))
    cols = ["#2563EB", "#B91C1C"]
    for ax, key, title, thr in ((axes[0], "BBB_Leakage", "BBB permeability", 0.50), (axes[1], "Microglia_M1", "Microglial M1", 0.40)):
        for r, col in zip(reports, cols):
            ax.plot(r["df"]["Date"], r["df"][key] * 100, color=col, lw=2.2, label=r["name"])
        ax.axhline(thr * 100, color="grey", ls=":", lw=1)
        ax.set_title(title, fontweight="bold")
        ax.set_ylabel("%")
        ax.xaxis.set_major_formatter(mdates.DateFormatter("%d %b"))
        ax.tick_params(axis="x", rotation=30)
        ax.legend(fontsize=8)
    fig.tight_layout()
    return fig


def region_table(data: dict) -> pd.DataFrame:
    rows = []
    for i, r in enumerate(data["reports"]):
        a = r["assessment"]
        rows.append({"Region": f"{i + 1}. {r['name']}", "Peak BBB (%)": round(a["max_bbb"] * 100, 1),
                     "Peak M1 (%)": round(a["max_m1"] * 100, 1), "Thermal index (°C-eq)": round(a["max_anomaly"], 1),
                     "Tmax (°C)": round(a["max_temp"], 1), "Tmin (°C)": round(a["min_temp"], 1), "Risk": a["level"],
                     "Peak BBB date": fmt(a["peak_bbb_date"])})
    r1, r2 = data["reports"][0]["assessment"], data["reports"][1]["assessment"]
    rows.append({"Region": "Difference (1 - 2)", "Peak BBB (%)": round((r1["max_bbb"] - r2["max_bbb"]) * 100, 1),
                 "Peak M1 (%)": round((r1["max_m1"] - r2["max_m1"]) * 100, 1),
                 "Thermal index (°C-eq)": round(r1["max_anomaly"] - r2["max_anomaly"], 1),
                 "Tmax (°C)": round(r1["max_temp"] - r2["max_temp"], 1), "Tmin (°C)": round(r1["min_temp"] - r2["min_temp"], 1)})
    return pd.DataFrame(rows)


def compare_sentence(data: dict) -> str:
    r1, r2 = data["reports"][0], data["reports"][1]
    sc = lambda r: 0.55 * r["assessment"]["max_bbb"] + 0.45 * r["assessment"]["max_m1"]
    hi, lo = (r1, r2) if sc(r1) >= sc(r2) else (r2, r1)
    ah, al = hi["assessment"], lo["assessment"]
    return (f"**{hi['name']}** shows the higher modelled neurovascular burden: peak BBB {ah['max_bbb'] * 100:.1f}% vs "
            f"{al['max_bbb'] * 100:.1f}% and peak M1 {ah['max_m1'] * 100:.1f}% vs {al['max_m1'] * 100:.1f}% in **{lo['name']}** "
            f"(risk {ah['level']} vs {al['level']}). Same engine, same cohort and blood-pressure profile for both regions.")


def results_map(data: dict):
    reps = data["reports"]
    fmap = folium.Map(location=[reps[0]["lat"], reps[0]["lon"]], zoom_start=5)
    colors = {"High": "red", "Moderate": "orange", "Baseline": "green"}
    for r in reps:
        a = r["assessment"]
        pop = (f"<b>{html_lib.escape(r['name'])}</b><br>Risk: {a['level']}<br>Peak BBB: {a['max_bbb'] * 100:.1f}%"
               f"<br>Peak M1: {a['max_m1'] * 100:.1f}%")
        folium.Marker([r["lat"], r["lon"]], popup=folium.Popup(pop, max_width=260), tooltip=f"{r['name']} - {a['level']}",
                      icon=folium.Icon(color=colors.get(a["level"], "blue"), icon="info-sign")).add_to(fmap)
    if len(reps) > 1:
        fmap.fit_bounds([[r["lat"], r["lon"]] for r in reps], padding=(30, 30))
    return fmap


def fig_png(fig) -> bytes:
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=140, bbox_inches="tight")
    plt.close(fig)
    return buf.getvalue()

def plot_trajectory(df: pd.DataFrame, name: str):
    fig, ax1 = plt.subplots(figsize=(10, 4.5))
    ax1.plot(df["Date"], df["Anomaly"], color="#991B1B", lw=2, label="Thermal Anomaly Index (°C-eq)")
    ax1.set_ylabel("Thermal Anomaly (°C-eq)", color="#991B1B", fontweight="bold")
    ax1.set_ylim(bottom=0)

    ax2 = ax1.twinx()
    ax2.plot(df["Date"], df["BBB_Leakage"], color="#2563EB", lw=2.5, ls="--", label="BBB Permeability Breakdown")
    ax2.plot(df["Date"], df["Microglia_M1"], color="#0F172A", lw=3, label="Microglial M1 Polarization")
    ax2.fill_between(df["Date"], df["BBB_Low"], df["BBB_High"], color="#2563EB", alpha=0.12)
    ax2.fill_between(df["Date"], df["M1_Low"], df["M1_High"], color="#0F172A", alpha=0.12)
    ax2.axhline(BBB_ALERT, color="#2563EB", ls=":", lw=1, label="BBB Critical Threshold (0.50)")
    
    ax2.set_ylabel("Activation Index (0.00 - 1.00)", color="#0F172A", fontweight="bold")
    ax2.set_ylim(-0.02, 1.05)
    
    ax1.xaxis.set_major_formatter(mdates.DateFormatter("%a %d %b"))
    fig.autofmt_xdate(rotation=30, ha="right")
    ax1.set_title(f"Pathokinetic Trajectory Analysis: {name}", fontweight="bold", color="#0F172A")
    
    h1, l1 = ax1.get_legend_handles_labels()
    h2, l2 = ax2.get_legend_handles_labels()
    ax1.legend(h1 + h2, l1 + l2, loc="upper center", bbox_to_anchor=(0.5, -0.22), ncol=3, fontsize=8)
    fig.tight_layout()
    return fig

def _clean_pdf_text(text) -> str:
    if not text:
        return ""
    text = str(text)
    repl = {"–": "-", "—": "-", "−": "-", "‑": "-", "’": "'", "‘": "'", "“": '"', "”": '"', "…": "...", "•": "-",
            "≥": ">=", "≤": "<=", "°": " deg ", "µ": "u", "μ": "u", "²": "2", "³": "3", "₂": "2", "₃": "3", "→": "->",
            "×": "x", "±": "+/-", "·": "-", "≈": "~", " ": " ", " ": " ", "🧠": "", "⚠️": "", "**": ""}
    for orig, new in repl.items():
        text = text.replace(orig, new)
    text = unicodedata.normalize("NFKD", text)
    text = "".join(ch for ch in text if not unicodedata.combining(ch))
    return text.encode("latin-1", errors="ignore").decode("latin-1")

class PDFReport(FPDF):
    def header(self):
        self.set_font("Helvetica", "B", 12)
        self.cell(0, 8, "Neuro-Protection Clinical Diagnostic Report", align="C", new_x="LMARGIN", new_y="NEXT")
        self.ln(2)

    def footer(self):
        self.set_y(-12)
        self.set_font("Helvetica", "I", 7)
        self.cell(0, 6, f"Research and educational tool - not a medical device or diagnosis | Page {self.page_no()}", align="C")

def build_pdf(analysis: dict) -> bytes:
    pdf = PDFReport()
    pdf.set_auto_page_break(True, 15)
    pdf.add_page()
    epw = pdf.epw

    def head(txt):
        pdf.set_font("Helvetica", "B", 10)
        pdf.cell(epw, 6, _clean_pdf_text(txt), new_x="LMARGIN", new_y="NEXT")

    def body(txt, size=9, style="", h=5):
        pdf.set_font("Helvetica", style, size)
        pdf.multi_cell(epw, h, _clean_pdf_text(txt), new_x="LMARGIN", new_y="NEXT")

    head("1. Executive Summary & Parameters")
    body(f"Engine: {analysis['mode']}\nCohort Profile: {analysis['cohort']}\nHemodynamics: {analysis['bp']}\n"
         f"Generated: {analysis.get('stamp', '')}")
    pdf.ln(2)

    for r in analysis["reports"]:
        a = r["assessment"]
        head(f"Target Region: {r['name'] or ('Region (%.2f, %.2f)' % (r['lat'], r['lon']))} (Risk Status: {a['level']})")
        body(f"Peak BBB Permeability Leakage: {a['max_bbb']*100:.1f}% (peak {fmt(a['peak_bbb_date'])})\n"
             f"Peak M1 Microglial Polarization: {a['max_m1']*100:.1f}% (peak {fmt(a['peak_m1_date'])})\n"
             f"Temperature range: {a['min_temp']:.1f} to {a['max_temp']:.1f} C")
        pdf.ln(1)
        pdf.image(io.BytesIO(r["png"]), w=epw)
        pdf.ln(2)

        head("Past - Present - Future comparison")
        widths = [epw * 0.36, epw * 0.16, epw * 0.16, epw * 0.14, epw * 0.18]
        pdf.set_font("Helvetica", "B", 8)
        for lab, w in zip(["Epoch", "Peak BBB %", "Peak M1 %", "Risk", "Tmax/Tmin C"], widths):
            pdf.cell(w, 6, lab, border=1)
        pdf.ln()
        pdf.set_font("Helvetica", "", 8)
        for k in EPOCHS:
            e = r["epochs"].get(k)
            vals = [EPOCH_LABELS[k], "-", "-", "n/a", "-"] if not e else [
                EPOCH_LABELS[k], f"{e['assessment']['max_bbb']*100:.1f}", f"{e['assessment']['max_m1']*100:.1f}",
                e["assessment"]["level"], f"{e['assessment']['max_temp']:.0f}/{e['assessment']['min_temp']:.0f}"]
            for v, w in zip(vals, widths):
                pdf.cell(w, 6, _clean_pdf_text(v), border=1)
            pdf.ln()
        pdf.ln(2)
        pdf.image(io.BytesIO(r["png_epochs"]), w=epw * 0.8)
        pdf.ln(2)

        head("Preventative interventions & clinical protocols")
        for title, desc in r["protocol"]:
            body(f"- {title}: {desc}", 8, "", 4)
        pdf.ln(1)
        head("Interpretation & conclusion")
        body(r["interpretation"], 8, "", 4)
        body(r["conclusion"], 8, "", 4)
        pdf.ln(3)

    if analysis.get("comparison_png"):
        head("Dual-region comparison")
        pdf.image(io.BytesIO(analysis["comparison_png"]), w=epw)
        pdf.ln(2)
        body(analysis.get("comparison_text", ""), 8, "", 4)

    head("Academic Citations & Sources")
    pdf.set_font("Helvetica", "", 7)
    for c in ALL_SOURCES:
        pdf.multi_cell(epw, 3.8, "- " + _clean_pdf_text(c), new_x="LMARGIN", new_y="NEXT")
    pdf.ln(2)
    body("Phenomenological model; parameters are illustrative and not fitted to patient data. Not medical advice.", 7, "I", 4)
    return bytes(pdf.output())

# ---------------------------------------------------------------------------
# UNIVERSAL EMAIL DISPATCH ENGINE
# ---------------------------------------------------------------------------
def build_email(data: dict):
    """Subject, plain text and HTML built only from st.session_state['last_analysis']."""
    reports = data["reports"]
    level = "CRITICAL" if any(r["assessment"]["level"] == "High" for r in reports) else (
        "MODERATE" if any(r["assessment"]["level"] == "Moderate" for r in reports) else "ADVISORY")
    subject = f"[Neuro-Protection {level}] " + " / ".join(r["name"] for r in reports)
    txt, htm = [f"Neuroinflammatory Early-Warning Notice ({level})", f"Engine: {data['mode']}", ""], [
        f"<h3>Neuroinflammatory Early-Warning Notice ({level})</h3><p><i>Engine: {html_lib.escape(str(data['mode']))}</i></p>"]
    for r in reports:
        a = r["assessment"]
        window = ""
        if a["first_risk_date"] is not None:
            w0 = a["first_risk_date"] - pd.Timedelta(days=2)
            window = "Start NOW" if w0 <= a["window_start"] else f"Start {fmt(w0)}"
        actions = [f"{ti}: {de}" for ti, de in r["protocol"][:4]]
        ep = []
        for k in EPOCHS:
            e = r["epochs"].get(k)
            if e:
                ep.append(f"{k}: BBB {e['assessment']['max_bbb'] * 100:.0f}% / M1 {e['assessment']['max_m1'] * 100:.0f}% ({e['assessment']['level']})")
        txt += [f"TARGET LOCATION: {r['name']}", f"Date of peak hazard (BBB): {fmt(a['peak_bbb_date'])}",
                f"Peak BBB permeability leakage: {a['max_bbb'] * 100:.1f}%", f"Peak microglial M1 activation: {a['max_m1'] * 100:.1f}%",
                f"Risk level: {a['level']}" + (f" | 48-h prevention window: {window}" if window else ""),
                "Immediate action steps:"] + [f"  - {x}" for x in actions] + ["Epoch comparison: " + "; ".join(ep), ""]
        htm.append(f"<h4>{html_lib.escape(r['name'])}</h4><ul><li><b>Date of peak hazard:</b> {fmt(a['peak_bbb_date'])}</li>"
                   f"<li><b>Peak BBB permeability leakage:</b> {a['max_bbb'] * 100:.1f}%</li>"
                   f"<li><b>Peak microglial M1 activation:</b> {a['max_m1'] * 100:.1f}%</li>"
                   f"<li><b>Risk level:</b> {a['level']} {('- 48-h window: ' + window) if window else ''}</li></ul>"
                   "<p><b>Immediate action steps</b></p><ul>" + "".join(f"<li>{html_lib.escape(x)}</li>" for x in actions) + "</ul>"
                   f"<p><i>{html_lib.escape('; '.join(ep))}</i></p>")
    foot = "Research and educational tool - not a medical device, diagnosis or medical advice."
    txt.append(foot)
    htm.append(f"<p><small>{foot}</small></p>")
    return subject, "\n".join(txt), "".join(htm)


def _secret(key):
    try:
        return st.secrets[key]
    except Exception:
        return None


def send_alert_email(to_addr: str, subject: str, text_body: str, html_body: str, pdf_bytes=None):
    """Returns (status, message); status in {'sent', 'error', 'sim'}. Provider errors are shown verbatim."""
    api_key, smtp_cfg = _secret("resend_api_key"), _secret("smtp")
    if not api_key and not smtp_cfg:
        return "sim", ("Mode Simulation : Ajoutez votre clé Resend ou identifiants SMTP dans Streamlit Secrets "
                       "pour activer l'envoi réel.")
    errors = []
    if api_key:
        payload = {"from": _secret("resend_from") or "Neuro-Protection Alert <onboarding@resend.dev>", "to": [to_addr],
                   "subject": subject, "text": text_body, "html": html_body}
        if pdf_bytes:
            payload["attachments"] = [{"filename": "neuro_protection_report.pdf", "content": base64.b64encode(pdf_bytes).decode()}]
        try:
            r = requests.post("https://api.resend.com/emails", json=payload, timeout=30,
                              headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"})
            if r.status_code in (200, 201):
                return "sent", f"Alert dispatched to {to_addr} via Resend. Response: {r.text}"
            hint = ""
            if r.status_code == 403:
                hint = " (Resend testing mode: the free 'onboarding@resend.dev' sender only delivers to your own Resend account e-mail; verify a domain and set resend_from.)"
            elif r.status_code == 401:
                hint = " (Invalid or revoked API key: create a new key in Resend.)"
            errors.append(f"Resend error HTTP {r.status_code}. Exact response: {r.text}{hint}")
        except requests.RequestException as exc:
            errors.append(f"Resend network error: {type(exc).__name__}: {exc}")
    if smtp_cfg:
        try:
            cfg = dict(smtp_cfg)
            user = cfg.get("username") or cfg.get("user")
            host, port, pwd = cfg["host"], int(cfg.get("port", 587)), cfg["password"]
        except KeyError as exc:
            errors.append(f"SMTP secrets incomplete: missing key {exc} (need host, username, password; port defaults to 587).")
        else:
            msg = EmailMessage()
            msg["Subject"], msg["From"], msg["To"] = subject, cfg.get("sender", user), to_addr
            msg.set_content(text_body)
            msg.add_alternative(html_body, subtype="html")
            if pdf_bytes:
                msg.add_attachment(pdf_bytes, maintype="application", subtype="pdf", filename="neuro_protection_report.pdf")
            try:
                with smtplib.SMTP(host, port, timeout=25) as srv:
                    srv.ehlo()
                    srv.starttls(context=ssl.create_default_context())
                    srv.ehlo()
                    srv.login(user, pwd)
                    srv.send_message(msg)
                return "sent", f"Alert dispatched to {to_addr} via SMTP ({host}:{port}, TLS)."
            except smtplib.SMTPAuthenticationError as exc:
                detail = exc.smtp_error.decode(errors="replace") if isinstance(exc.smtp_error, bytes) else str(exc.smtp_error)
                errors.append(f"SMTP authentication failed (code {exc.smtp_code}): {detail} "
                              "(Gmail needs an App Password with 2-step verification enabled.)")
            except smtplib.SMTPException as exc:
                errors.append(f"SMTP error: {type(exc).__name__}: {exc}")
            except (OSError, TimeoutError) as exc:
                errors.append(f"SMTP connection error ({host}:{port}): {type(exc).__name__}: {exc}")
    return "error", "\n\n".join(errors)

# ---------------------------------------------------------------------------
# SIDEBAR CONTROL PANEL
# ---------------------------------------------------------------------------
st.sidebar.header("Simulation Settings")
climate_mode = st.sidebar.radio("Climate Engine:", [t["mode_fc"], t["mode_ar"], t["mode_cc"]])
view_mode = st.sidebar.radio("View Mode:", [t["single_view"], t["dual_view"]])

start_date = end_date = None
if climate_mode == t["mode_ar"]:
    st.sidebar.header("Copernicus Archive Window")
    latest_archive = date.today() - timedelta(days=5)
    start_date = st.sidebar.date_input("Start Date", value=date(2025, 7, 1), max_value=latest_archive)
    end_date = st.sidebar.date_input("End Date", value=date(2025, 7, 20), max_value=latest_archive)

bp_state = st.sidebar.selectbox("Blood Pressure Profile:", list(SHEAR_MULT.keys()))
cohort_key = st.sidebar.selectbox("Target Population Profile:", list(COHORTS.keys()))

st.sidebar.markdown("---")
col_s1, col_s2 = st.sidebar.columns(2)
run_btn = col_s1.button(t["run_btn"], width="stretch")
reset_btn = col_s2.button(t["reset_btn"], width="stretch")

if reset_btn:
    st.session_state.clear()
    st.rerun()

# ---------------------------------------------------------------------------
# STRICT BIDIRECTIONAL LOCATION PICKER
# ---------------------------------------------------------------------------
def location_picker(prefix: str, default_query: str):
    k_query = f"{prefix}_query"
    k_lat, k_lon = f"{prefix}_lat", f"{prefix}_lon"
    k_name = f"{prefix}_name"

    if k_query not in st.session_state:
        st.session_state[k_query] = default_query
        lat0, lon0, name0 = search_location_query(default_query)
        st.session_state[k_lat], st.session_state[k_lon], st.session_state[k_name] = lat0, lon0, name0

    query_input = st.text_input(t["search_label"], value=st.session_state[k_query], key=f"inp_{prefix}")
    
    if query_input != st.session_state[k_query]:
        st.session_state[k_query] = query_input
        lat_res, lon_res, name_res = search_location_query(query_input)
        st.session_state[k_lat], st.session_state[k_lon], st.session_state[k_name] = lat_res, lon_res, name_res
        st.rerun()

    lat0, lon0 = st.session_state[k_lat], st.session_state[k_lon]
    
    fmap = folium.Map(location=[lat0, lon0], zoom_start=6)
    folium.Marker([lat0, lon0], popup=st.session_state[k_name], icon=folium.Icon(color="red")).add_to(fmap)
    out = st_folium(fmap, height=220, key=f"map_{prefix}", returned_objects=["last_clicked"], use_container_width=True)
    
    click = out.get("last_clicked") if out else None
    if click and click["lat"] != -90.0 and click["lng"] != -180.0:
        c_lat, c_lon = round(click["lat"], 4), round(((click["lng"] + 180) % 360) - 180, 4)
        if (c_lat, c_lon) != st.session_state.get(f"{prefix}_last_click"):
            st.session_state[f"{prefix}_last_click"] = (c_lat, c_lon)
            st.session_state[k_lat], st.session_state[k_lon] = c_lat, c_lon
            new_name = reverse_geocode(c_lat, c_lon)
            st.session_state[k_name] = new_name
            st.session_state[k_query] = new_name
            st.rerun()

    c1, c2 = st.columns(2)
    lat = c1.number_input("Lat", min_value=-90.0, max_value=90.0, format="%.4f", key=k_lat)
    lon = c2.number_input("Lon", min_value=-180.0, max_value=180.0, format="%.4f", key=k_lon)
    name = st.session_state[k_name]
    st.caption(f"Selected Region: **{name}**")
    return lat, lon, name

# ---------------------------------------------------------------------------
# MAIN APPLICATION INTERFACE
# ---------------------------------------------------------------------------
tab_sim, tab_causes, tab_aware, tab_guide, tab_src = st.tabs(
    [t["tab_sim"], t["tab_causes"], t["tab_aware"], t["tab_guide"], t["tab_src"]])

with tab_sim:
    if view_mode == t["single_view"]:
        lat, lon, loc_name = location_picker("loc1", "Tunis, Tunisia")
        locs = [(loc_name, lat, lon)]
    else:
        c1, c2 = st.columns(2)
        with c1:
            st.subheader("Region 1")
            lat1, lon1, name1 = location_picker("loc1", "Tunis, Tunisia")
        with c2:
            st.subheader("Region 2")
            lat2, lon2, name2 = location_picker("loc2", "Brussels, Belgium")
        locs = [(name1, lat1, lon1), (name2, lat2, lon2)]

    st.markdown("---")

    with st.expander(t["guide_title"], expanded=False):
        st.markdown(r"""
        ### Climate Engines & Physiological Relevance
        1. **Predictive Forecast (7-Day Proactive Model):**
           * Evaluates short-term atmospheric stress to allow caregivers and clinicians to implement preventative cooling protocols 48 hours prior to acute heat peaks.
        2. **Copernicus ERA5 Archive (Historical Reanalysis):**
           * Reconstructs historic heatwaves and cold waves (e.g., Summer 2003, 2022) using ECMWF Copernicus reanalysis datasets to validate kinetic predictions against clinical admission trends.
        3. **Climate Change 2050 Projections:**
           * Models baseline global temperature shifts ($+2.45\,^{\circ}\text{C}$) combined with relative humidity changes to evaluate long-term population neurovascular risk.
        """)

    with st.expander(t["expander_title"], expanded=False):
        st.markdown("""
        ### Coupled Ordinary Differential Equations (ODEs)
        * **Blood-Brain Barrier Degradation Rate ($BBB$):**
          $$\\frac{d(BBB)}{dt} = g_b \\cdot \\text{Anomaly} \\cdot \\text{Shear} \\cdot (1 - BBB) - k_{bbb} \\cdot BBB$$
        * **Microglial M1 Neuroinflammatory Activation ($M1$):**
          $$\\frac{d(M1)}{dt} = g_m \\cdot BBB \\cdot (1 - M1) - k_{m1} \\cdot M1$$
        """)

    with st.expander("Pollution, ozone & Climate-2050 extensions of the model", expanded=False):
        st.markdown("""
        * **Oxidative load:** $Ox = 1 + 0.6\\,\\max(0, O_3-60)/100 + 0.25\\,\\max(0, PM_{2.5}-15)/15$ (WHO 2021 reference levels, µg/m³) multiplies the barrier-opening gain $g_b$ and, with half weight, the microglial gain $g_m$.
        * **2050 microvascular frailty:** $F = 1 + 0.08\\,\\Delta T + 0.004\\,\\Delta O_3$ divides the repair rate $k_{bbb}$ (slower recovery). Scenario: $\\Delta T = +2.45\\,^{\\circ}C$, $RH \\times 1.08$, $O_3 +2.0$ and $PM_{2.5} +0.5\\ \\mu g/m^3$ per $^{\\circ}C$.
        * Parameters are phenomenological assumptions, not fitted to patient data. Archive (ERA5) runs use no pollution term.
        """)

    # EXECUTION CONTROLLER
    if run_btn:
        try:
            with st.spinner("Calculating biophysical kinetics (Past · Present · Future)..."):
                sd = start_date or date(2025, 7, 1)
                ed = end_date or date(2025, 7, 20)
                c, shear = COHORTS[cohort_key], SHEAR_MULT[bp_state]
                key_sel = epoch_mode_key(climate_mode)
                reports = []

                for name, lat, lon in locs:
                    resolved_name = reverse_geocode(lat, lon) if "Region (" in name else name
                    ep = compute_epochs(lat, lon, c, shear, str(sd), str(ed))
                    if ep.get(key_sel) is None:
                        raise RuntimeError(f"{resolved_name}: {ep['errors'].get(key_sel, 'climate engine unavailable')}")
                    df, a = ep[key_sel]["df"], ep[key_sel]["assessment"]
                    fig = plot_trajectory(df, resolved_name)
                    reports.append(dict(
                        name=resolved_name, lat=lat, lon=lon, df=df, assessment=a, epochs=ep,
                        protocol=build_protocol(a, cohort_key),
                        interpretation=generate_specific_interpretation(a, resolved_name),
                        conclusion=generate_conclusion(a, resolved_name, cohort_key, bp_state),
                        png=fig_png(fig), png_epochs=fig_png(plot_epochs(ep, resolved_name))
                    ))

                analysis = dict(mode=climate_mode, mode_key=key_sel, cohort=cohort_key, bp=bp_state, reports=reports,
                                stamp=datetime.now().strftime("%Y-%m-%d %H:%M"), window=(str(sd), str(ed)),
                                comparison_png=None, comparison_text="")
                if len(reports) > 1:
                    analysis["comparison_png"] = fig_png(plot_comparison(reports))
                    analysis["comparison_text"] = compare_sentence(analysis)
                st.session_state["last_analysis"] = analysis

        except Exception as e:
            st.error(f"Execution Exception: {str(e)}")

    # RENDER SIMULATION RESULTS
    if "last_analysis" in st.session_state:
        data = st.session_state["last_analysis"]
        high_h = any(r["assessment"]["level"] == "High" for r in data["reports"])
        mod_h = any(r["assessment"]["level"] == "Moderate" for r in data["reports"])

        if high_h:
            st.error(t["high_hazard"])
        elif mod_h:
            st.warning(t["mod_hazard"])
        else:
            st.success(t["stable_hazard"])

        if len(data["reports"]) > 1:
            cols = st.columns(len(data["reports"]))
            for idx, r in enumerate(data["reports"]):
                with cols[idx]:
                    st.subheader(f"Region {idx+1}: {r['name']}")
                    st.image(r["png"], width="stretch")
                
                    a = r["assessment"]
                    m1, m2, m3 = st.columns(3)
                    m1.metric(t["max_bbb"], f"{a['max_bbb']*100:.1f}%")
                    m2.metric(t["max_m1"], f"{a['max_m1']*100:.1f}%")
                    m3.metric(t["max_heat"], f"{a['max_anomaly']:.1f} °C-eq")

                    with st.expander(f"{t['interp_title']} ({r['name']})", expanded=True):
                        st.markdown(r["interpretation"])

                    st.markdown(f"#### {t['protocol_title']}")
                    for title, desc in r["protocol"]:
                        st.markdown(f"""
                        <div class="clinical-card">
                            <div class="clinical-card-title">{title}</div>
                            <div class="clinical-card-body">{desc}</div>
                        </div>
                        """, unsafe_allow_html=True)

                    st.markdown(f"#### {t['conclusion_title']}")
                    st.markdown(f"""
                    <div class="conclusion-box">
                        {r['conclusion']}
                    </div>
                    """, unsafe_allow_html=True)
        else:
            for r in data["reports"]:
                st.subheader(f"Pathokinetic Trajectory: {r['name']}")
                st.image(r["png"], width="stretch")
            
                a = r["assessment"]
                m1, m2, m3 = st.columns(3)
                m1.metric(t["max_bbb"], f"{a['max_bbb']*100:.1f}%")
                m2.metric(t["max_m1"], f"{a['max_m1']*100:.1f}%")
                m3.metric(t["max_heat"], f"{a['max_anomaly']:.1f} °C-eq")

                with st.expander(f"{t['interp_title']} ({r['name']})", expanded=True):
                    st.markdown(r["interpretation"])

                st.markdown(f"### {t['protocol_title']}")
                for title, desc in r["protocol"]:
                    st.markdown(f"""
                    <div class="clinical-card">
                        <div class="clinical-card-title">{title}</div>
                        <div class="clinical-card-body">{desc}</div>
                    </div>
                    """, unsafe_allow_html=True)

                st.markdown(f"### {t['conclusion_title']}")
                st.markdown(f"""
                <div class="conclusion-box">
                    {r['conclusion']}
                </div>
                """, unsafe_allow_html=True)

        # EPOCH COMPARISON (computed on every run)
        st.markdown("---")
        st.subheader(t["epoch_title"])
        st.caption(f"Past epoch = ERA5 archive window {data['window'][0]} → {data['window'][1]}. Present = Open-Meteo 7-day forecast with live "
                   "ozone/PM2.5. Future = 2050 scenario (+2.45 °C, humidity, ozone/PM2.5, vascular frailty).")
        for r in data["reports"]:
            st.markdown(f"**{r['name']}**")
            st.dataframe(epoch_table(r), width="stretch", hide_index=True)
            st.image(r["png_epochs"], width="stretch")
            air = r["epochs"]["air"]
            st.caption((f"Live air quality: ozone {air['o3']:.0f} µg/m³, PM2.5 {air['pm']:.1f} µg/m³ (WHO references 60 / 15)."
                        if air["ok"] else "Live air-quality data unavailable: neutral pollution load used.")
                       + "".join(f" · {k} epoch unavailable: {v}" for k, v in r["epochs"]["errors"].items()))

        # DUAL-REGION COMPARISON TOOLS
        if len(data["reports"]) > 1:
            st.markdown("---")
            st.subheader(t["compare_title"])
            st.dataframe(region_table(data), width="stretch", hide_index=True)
            st.image(data["comparison_png"], width="stretch")
            st.markdown(data["comparison_text"])

        # RISK MAP
        st.markdown("---")
        st.subheader("Risk map")
        st_folium(results_map(data), height=320, key=f"result_map_{data['stamp']}", returned_objects=[], use_container_width=True)

        # PDF EXPORT
        st.markdown("---")
        pdf_bytes = build_pdf(data)
        st.download_button(t["pdf_btn"], data=pdf_bytes, file_name="neuro_protection_clinical_report.pdf", mime="application/pdf", width="stretch")

        # EMAIL DISPATCH, PUSH NOTIFICATION & SHARE
        st.markdown("---")
        st.subheader(t["email_title"])
        subj, body_txt, body_html = build_email(data)
        top = data["reports"][0]
        push_component("NEURO-PROTECTION ALERT" if high_h else "Neuro-Protection update",
                       f"{top['name']}: peak BBB {top['assessment']['max_bbb']*100:.0f}% / M1 {top['assessment']['max_m1']*100:.0f}%",
                       data["stamp"], high_h)
        if not high_h:
            st.info("No critical hazard in this run: you can still send an advisory update.")
        with st.expander("Preview of the alert message (same data source as screen, hub and PDF)"):
            st.text(body_txt)
        user_email = st.text_input(t["email_placeholder"], key="alert_email")
        attach_pdf = st.checkbox("Attach the PDF clinical report", value=True)
        if st.button(t["email_send"]):
            now = time.time()
            log = [x for x in st.session_state.get("mail_log", []) if now - x < 3600]
            if not EMAIL_RE.match(user_email or ""):
                st.error("Invalid email address format.")
            elif log and now - log[-1] < 30:
                st.error("Please wait 30 seconds between dispatches.")
            elif len(log) >= 5:
                st.error("Limit reached: 5 dispatches per hour per session.")
            else:
                status, msg = send_alert_email(user_email, subj, body_txt, body_html, pdf_bytes if attach_pdf else None)
                if status == "sent":
                    st.success(msg)
                    log.append(now)
                elif status == "sim":
                    st.info(msg)
                else:
                    st.error(msg)
                    _m = re.search(r"own email address \(([^)\s]+)\)", msg)
                    if _m:
                        st.session_state["resend_owner"] = _m.group(1)
            st.session_state["mail_log"] = log
        owner = st.session_state.get("resend_owner")
        if owner:
            st.warning(f"Resend is in testing mode: it can only deliver to {owner}. Permanent fix: verify a domain at resend.com/domains and set resend_from, or use Gmail SMTP (App Password) in Secrets.")
            if st.button(f"Send the alert to {owner} now"):
                status2, msg2 = send_alert_email(owner, subj, body_txt, body_html, pdf_bytes if attach_pdf else None)
                (st.success if status2 == "sent" else st.error)(msg2)
        share = share_text(data)
        st.text_area("Shareable alert text (SMS / WhatsApp / social)", share, height=100)
        st.link_button("Share on WhatsApp", "https://wa.me/?text=" + quote(share))

with tab_causes:
    render_causes()
with tab_aware:
    render_campaign()
with tab_guide:
    render_assistant()
with tab_src:
    render_sources()

st.caption("© 2026 Tasnim (TiaGassem). All rights reserved. Research and educational tool - not a medical device, not a diagnosis, "
           "not a substitute for professional medical advice. In an emergency contact local emergency services.")
