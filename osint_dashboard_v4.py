"""
Global & KRG OSINT Command Center  (v4 - powered by Google News search)

Instead of polling ~70 separate RSS feeds, every panel is a handful of Google News
searches (site: / OR / topic operators). Google does the collecting and ranking;
the script only merges, removes duplicates and sorts by time.

Requires: streamlit>=1.37, feedparser, requests
Run:      streamlit run osint_dashboard_v4.py
"""
import calendar
import html
import re
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from html.parser import HTMLParser
from urllib.parse import urlencode, urljoin, urlparse

import feedparser
import requests
import streamlit as st

# ───────────────────────── SETTINGS ─────────────────────────
TIMEOUT = (5, 12)        # (connect, read) seconds
CACHE_TTL = 300          # keep good results 5 minutes
FAIL_TTL = 60            # retry a failed search after 1 minute
AUTO_REFRESH = 300       # auto-refresh the active view every 5 minutes
G_COOLDOWN = 120         # after a Google HTTP 429, use direct RSS fallbacks for 2 minutes
MAX_WORKERS = 4          # be gentle with Google
RETRY_ATTEMPTS = 1       # only for HTTP 429 / 5xx, never for timeouts
RETRY_BACKOFF = 2.0
PER_QUERY_LIMIT = 100    # Google News returns up to ~100 items per search
PANEL_LIMIT = 150
ALL = "★ All searches (merged)"
HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"),
    "Accept": "application/rss+xml, application/xml;q=0.9, text/xml;q=0.8, */*;q=0.5",
}

WINDOWS = {"1 hour": "1h", "6 hours": "6h", "24 hours": "1d", "3 days": "3d", "7 days": "7d", "30 days": "30d"}
EDITIONS = {  # key -> (hl, gl, ceid)
    "en": ("en-US", "US", "US:en"),
    "ar": ("ar", "IQ", "IQ:ar"),     # Arabic-script edition: best chance for Kurdish (Sorani) keywords
}


def gnews_url(query: str, window: str, edition: str = "en") -> str:
    """One Google News RSS search. Supports: "exact phrase", OR, -exclude, site:, intitle:"""
    hl, gl, ceid = EDITIONS[edition]
    return "https://news.google.com/rss/search?" + urlencode(
        {"q": f"{query} when:{window}", "hl": hl, "gl": gl, "ceid": ceid}
    )


# ───────────────────────── SEARCH PRESETS ─────────────────────────
# Direct RSS feeds used ONLY when Google News is rate-limiting (label, url).
FB_BBC = ("BBC World", "https://feeds.bbci.co.uk/news/world/rss.xml")
FB_AJ = ("Al Jazeera", "https://www.aljazeera.com/xml/rss/all.xml")
FB_GUARDIAN = ("The Guardian", "https://www.theguardian.com/world/rss")
FB_NYT = ("New York Times", "https://rss.nytimes.com/services/xml/rss/nyt/World.xml")
FB_DW = ("DW", "https://rss.dw.com/rdf/rss-en-all")
FB_F24 = ("France 24", "https://www.france24.com/en/rss")
FB_WSJ = ("Wall Street Journal", "https://feeds.content.dowjones.io/public/rss/RSSWorldNews")
FB_WAPO = ("Washington Post", "https://feeds.washingtonpost.com/rss/world")
FB_WAPO_ME = ("Washington Post · Middle East", "https://feeds.washingtonpost.com/rss/world/middle-east")
FB_AXIOS = ("Axios", "https://api.axios.com/feed/top/")
FB_ECON = ("The Economist", "https://www.economist.com/international/rss.xml")
FB_ECON_ME = ("The Economist · Middle East", "https://www.economist.com/middle-east-and-africa/rss.xml")
FB_FP = ("Foreign Policy", "https://foreignpolicy.com/feed/")
FB_FA = ("Foreign Affairs", "https://www.foreignaffairs.com/rss.xml")
FB_WOTR = ("War on the Rocks", "https://warontherocks.com/feed/")
FB_BELLINGCAT = ("Bellingcat", "https://www.bellingcat.com/feed/")
FB_LWJ = ("Long War Journal", "https://www.longwarjournal.org/feed")
FB_BD = ("Breaking Defense", "https://breakingdefense.com/feed/")
FB_TWZ = ("The War Zone", "https://www.twz.com/feed")
FB_SHAFAQ = ("Shafaq News", "https://shafaq.com/en/rss")
FB_TOI = ("Times of Israel", "https://www.timesofisrael.com/feed/")

# group -> {panel name: (Google News query, edition[, fallback feeds])}.  Edit freely.
GLOBAL_PRESETS = {
    "Major outlets": {
        "Wires · Reuters, AP, BBC, Al Jazeera": ("site:reuters.com OR site:apnews.com OR site:bbc.com OR site:aljazeera.com", "en", (FB_BBC, FB_AJ)),
        "US press · WSJ, Washington Post, NYT, Axios": ("site:wsj.com OR site:washingtonpost.com OR site:nytimes.com OR site:axios.com", "en", (FB_WSJ, FB_WAPO, FB_NYT, FB_AXIOS)),
        "Europe · Guardian, DW, France 24, FT": ("site:theguardian.com OR site:dw.com OR site:france24.com OR site:ft.com", "en", (FB_GUARDIAN, FB_DW, FB_F24)),
        "Analysis · Economist, Foreign Policy, Foreign Affairs": ("site:economist.com OR site:foreignpolicy.com OR site:foreignaffairs.com OR site:warontherocks.com OR site:nationalinterest.org", "en", (FB_ECON, FB_FP, FB_FA, FB_WOTR)),
        "Defense & OSINT · Bellingcat, LWJ, ISW, TWZ": ("site:bellingcat.com OR site:longwarjournal.org OR site:understandingwar.org OR site:twz.com OR site:breakingdefense.com", "en", (FB_BELLINGCAT, FB_LWJ, FB_BD, FB_TWZ)),
    },
    "Topics": {
        "Iran – US": ("Iran (US OR Washington OR sanctions OR strike OR nuclear)", "en"),
        "Israel – Gaza – Lebanon": ("Israel (Gaza OR Hezbollah OR Lebanon OR Hamas)", "en"),
        "Russia – Ukraine": ("Russia Ukraine", "en"),
        "World breaking": ("breaking news world", "en"),
    },
}

LOCAL_PRESETS = {
    "Iraq & Kurdistan": {
        "Kurdistan Region": ("Kurdistan OR Erbil OR Sulaymaniyah OR Duhok OR Halabja", "en", (FB_SHAFAQ,)),
        "Kirkuk · Baghdad · Mosul · Basra": ("Kirkuk OR Baghdad OR Mosul OR Basra", "en"),
        "Kurdish outlets · Rudaw, Kurdistan24, Shafaq…": ("site:rudaw.net OR site:kurdistan24.net OR site:shafaq.com OR site:thenewregion.com OR site:basnews.com OR site:964media.com OR site:iraqinews.com", "en", (FB_SHAFAQ,)),
    },
    "Kurdish politics (leaders & parties)": {
        "KDP · Masoud, Masrour & Nechirvan Barzani": ('"Kurdistan Democratic Party" OR KDP OR "Masoud Barzani" OR "Masrour Barzani" OR "Nechirvan Barzani"', "en"),
        "PUK · Bafel & Qubad Talabani": ('"Patriotic Union of Kurdistan" OR PUK OR "Bafel Talabani" OR "Qubad Talabani"', "en"),
        "Iraq's Kurdish leaders · Nizar Amedi, Fuad Hussein": ('"Nizar Amedi" OR "Nizar Amidi" OR "Fuad Hussein" OR "Muthanna Amin"', "en"),
        "KRG government & 10th cabinet": ('"Kurdistan Regional Government" OR KRG OR "tenth cabinet" OR "10th cabinet"', "en"),
        "Other KRG parties · New Generation, Gorran, Islamic Union": ('"New Generation" Kurdistan OR "Shaswar Abdulwahid" OR Gorran OR "Change Movement" OR "Kurdistan Islamic Union" OR "Kurdistan Justice Group"', "en"),
        "Syria · SDF, Mazloum Abdi, Ilham Ahmed": ('"Mazloum Abdi" OR "Ilham Ahmed" OR SDF OR PYD OR Rojava', "en"),
        "Turkey · PKK, Ocalan, DEM Party": ('PKK OR Ocalan OR "DEM Party" OR Qandil', "en"),
        "Iran Kurds · KDPI, Komala, PJAK": ('KDPI OR Komala OR PJAK OR "Mustafa Hijri" OR "Kurdish opposition" Iran', "en"),
    },
    "Middle East": {
        "Regional outlets · MEE, Al-Monitor, New Arab…": ("site:middleeasteye.net OR site:al-monitor.com OR site:newarab.com OR site:aawsat.com OR site:alarabiya.net OR site:iranintl.com OR site:timesofisrael.com OR site:aa.com.tr", "en", (FB_TOI, FB_ECON_ME, FB_WAPO_ME)),
        "Syria · Damascus & Rojava": ("Syria OR Rojava OR Damascus", "en"),
        "Iran – Iraq militias": ("(Iran OR Iraq) (militia OR PMF OR Hezbollah OR Houthi)", "en"),
    },
    "Security & energy": {
        "Drones · missiles · strikes": ("(drone OR missile OR rocket OR airstrike) (Iraq OR Kurdistan OR Syria OR Iran)", "en"),
        "Oil · gas · pipeline": ("Kurdistan (oil OR gas OR pipeline OR Ceyhan)", "en"),
    },
}

# Sorani sites. Google News barely indexes Sorani, so these are read DIRECTLY:
# 1) RSS auto-discovery from the homepage  2) common /feed /rss paths  3) headline scan of the homepage
# 4) Google News site: search as the last fallback.  Name -> (homepage URL, "site")
KURDISH_SITES = {
    "ماڵپەڕە سەرەکییەکان": {
        "ڕووداو": ("https://www.rudaw.net/sorani", "site"),
        "کوردستان٢٤": ("https://www.kurdistan24.net/ckb", "site"),
        "کەناڵ٨": ("https://channel8.com", "site"),
        "NRT": ("https://www.nrttv.com", "site"),
        "کوردسات نیوز": ("https://kurdsatnews.com", "site"),
        "باسنیوز": ("https://www.basnews.com/so", "site"),
        "ئاڤا میدیا": ("https://www.avamedia.tv", "site"),
        "گەلی کوردستان (GK)": ("https://gksat.tv", "site"),
    },
    "ئاژانس و ماڵپەڕە هەواڵییەکان": {
        "خەندان": ("https://www.xendan.org", "site"),
        "پوکمیدیا": ("https://www.pukmedia.com", "site"),
        "شەفەق (کوردی)": ("https://shafaq.com/ku", "site"),
        "٩٦٤ (کوردی)": ("https://964media.com/ku", "site"),
        "ڕاچڵەکین": ("https://www.rachlaken.com", "site"),
        "شارپرێس": ("https://www.sharpress.net", "site"),
        "کوردستان تیڤی": ("https://kurdistantv.net", "site"),
    },
}

# Topics are keyword filters over everything fetched above (Arabic-script words match by prefix).
KURDISH_TOPICS = {
    "هەرێمی کوردستان": ["هەولێر", "سلێمانی", "دهۆک", "کەرکووک", "هەڵەبجە", "هەرێمی کوردستان", "حکومەتی هەرێم", "پێشمەرگە"],
    "پارتی · بارزانی": ["بارزانی", "پارتی دیموکراتی", "مەسرور", "نێچیرڤان", "مەسعود"],
    "یەکێتی · تاڵەبانی": ["تاڵەبانی", "یەکێتیی نیشتمانی", "یەکێتی نیشتمانی", "بافڵ", "قوباد", "ئامێدی"],
    "پارتە دیکەکان": ["نەوەی نوێ", "بزووتنەوەی گۆڕان", "یەکگرتووی ئیسلامی", "کۆمەڵی دادگەری", "شاسوار"],
    "حکومەت و کابینە": ["کابینە", "حکومەتی هەرێم", "پەرلەمان", "وەزیر", "ئەنجومەنی وەزیران"],
    "ئەمنی و سەربازی": ["درۆن", "مووشەک", "هێرش", "بۆردومان", "تەقینەوە", "ئاسایش", "پێشمەرگە"],
    "ئێران و ئەمریکا": ["ئێران", "ئەمریکا", "تاران", "واشنتۆن", "ترەمپ"],
    "سوریا و ڕۆژئاوا": ["سوریا", "ڕۆژئاوا", "هەسەدە", "دەمەشق", "مەزڵوم"],
    "پەکەکە و تورکیا": ["پەکەکە", "تورکیا", "ئۆجەلان", "ئەنقەرە"],
    "نەوت و ئابووری": ["نەوت", "گاز", "بودجە", "ئابووری", "مووچە"],
}
KU_ALL = "★ هەموو هەواڵەکان"

DEFAULT_WATCHLIST = "drone, Erbil, Sulaymaniyah, Kirkuk, missile, هەولێر, سلێمانی, کەرکووک, درۆن, مووشەک"
IRAN_TERMS = ("iran", "iranian", "tehran", "ئێران", "تاران")
US_TERMS = ("american", "united states", "u.s.", "washington", "ئەمریکا", "واشنتۆن")
CONFLICT_TERMS = ("war", "strike", "attack", "missile", "drone", "military", "conflict", "جەنگ", "هێرش", "مووشەک", "درۆن", "بۆردومان", "تەقینەوە")
SYRIA_TERMS = ("syria", "syrian", "damascus", "rojava", "sdf", "idlib", "سوریا", "دەمەشق", "ڕۆژئاوا", "هەسەدە")
KURDISTAN_TERMS = ("kurdistan", "erbil", "sulaymaniyah", "duhok", "kirkuk", "halabja",
                   "کوردستان", "هەولێر", "سلێمانی", "دهۆک", "کەرکووک", "هەڵەبجە", "پێشمەرگە")

st.set_page_config(
    page_title="Global & KRG OSINT Command Center",
    page_icon="🛰️",
    layout="wide",
    initial_sidebar_state="collapsed",
)

# ───────────────────────── DESIGN SYSTEM ─────────────────────────
# Calm, low-glare palettes: no pure black/white, soft saturation, warm "danger" colours
# (coral instead of alarm-red), slow motion, generous spacing.
NIGHT = {
    "bg": "#0f1420", "bg2": "#16203a", "panel": "#151c2c", "panel-hover": "#1b2438", "line": "#26314a",
    "text": "#e3e8f2", "muted": "#93a0ba",
    "iran": "#8aa8ff", "krg": "#e6b673", "sec": "#ee9a8a", "global": "#7fb2ff", "local": "#e6b673",
    "kurdish": "#6fd3b7", "deep": "#b7a1f5", "alert": "#ee9a8a",
    "lv0": "#6fd3b7", "lv1": "#8aa8ff", "lv2": "#e6b673", "lv3": "#ee9a8a",
}
DAY = {
    "bg": "#f4f1ea", "bg2": "#e9e4d8", "panel": "#fffdf8", "panel-hover": "#f6f2e9", "line": "#ddd6c6",
    "text": "#2a3042", "muted": "#667085",
    "iran": "#3d63c9", "krg": "#a8681a", "sec": "#b4533f", "global": "#2f6fd0", "local": "#a8681a",
    "kurdish": "#14806a", "deep": "#6f52c4", "alert": "#b4533f",
    "lv0": "#14806a", "lv1": "#3d63c9", "lv2": "#a8681a", "lv3": "#b4533f",
}

BASE_CSS = """
@import url('https://fonts.googleapis.com/css2?family=Vazirmatn:wght@400;500;700&display=swap');
html, body, .stApp, .stApp [class*="st-"]:not([data-testid="stIconMaterial"]) { font-family:'Vazirmatn', system-ui, -apple-system, 'Segoe UI', sans-serif; }
.stApp { background: radial-gradient(1100px 520px at 12% -8%, var(--bg2), var(--bg) 70%) fixed, var(--bg); color:var(--text); }
.stApp, .stApp p, .stApp label, [data-testid="stExpander"] summary *, .stRadio label *, .stCheckbox label *,
[data-testid="stToggle"] label * { color:var(--text); }
#MainMenu, footer, header[data-testid="stHeader"] { display:none; }
.block-container { padding:clamp(.75rem,2.5vw,2rem) clamp(.75rem,3vw,2.5rem) 2.5rem !important; max-width:1600px; }

/* ── header ── */
.topbar { display:flex; align-items:center; gap:14px; flex-wrap:nowrap; padding:16px 20px; margin-bottom:6px;
    background:linear-gradient(135deg, color-mix(in srgb, var(--panel) 96%, transparent), color-mix(in srgb, var(--panel-hover) 80%, transparent));
    border:1px solid var(--line); border-radius:18px; box-shadow:0 10px 30px rgba(0,0,0,.14); }
.topbar > div { min-width:0; }
.topbar h1 { margin:0; padding:0; font-size:clamp(1.1rem,2.4vw,1.6rem); font-weight:700; letter-spacing:.01em; line-height:1.4; color:var(--text); }
.topbar .sub { color:var(--muted); font-size:.88rem; margin-top:2px; }
.live-dot { width:10px; height:10px; border-radius:50%; flex:none; background:var(--lv0); animation:breathe 3.8s ease-in-out infinite; }
@keyframes breathe { 0%,100%{box-shadow:0 0 0 0 color-mix(in srgb, var(--lv0) 45%, transparent);} 50%{box-shadow:0 0 0 8px transparent;} }
.updated { color:var(--muted); font-size:.8rem; margin:6px 2px 14px; }

/* ── pill navigation (the view radio) ── */
div[role="radiogroup"] { gap:8px !important; flex-wrap:wrap; }
[data-testid="stRadioOption"], label[data-baseweb="radio"] { background:var(--panel); border:1px solid var(--line); border-radius:999px; padding:7px 18px; margin:0 !important; transition:background .2s, border-color .2s; cursor:pointer; }
[data-testid="stRadioOption"]:hover, label[data-baseweb="radio"]:hover { background:var(--panel-hover); }
[data-testid="stRadioOption"][data-selected="true"], label[data-baseweb="radio"]:has(input:checked) { border-color:var(--iran); background:color-mix(in srgb, var(--iran) 15%, var(--panel)); }
[data-testid="stRadioOption"] > div > div:first-child, label[data-baseweb="radio"] > div:first-child { display:none !important; }

/* ── briefing: topic cards ── */
.sec-title { font-size:1.02rem; font-weight:700; margin:26px 2px 12px; color:var(--text); display:flex; align-items:center; gap:10px; }
.sec-title small { color:var(--muted); font-weight:400; font-size:.8rem; }
.briefing { display:grid; grid-template-columns:repeat(auto-fit, minmax(min(100%, 330px), 1fr)); gap:18px; }
.topic { position:relative; overflow:hidden; border:1px solid var(--line); border-radius:20px; padding:20px 20px 10px;
    background:radial-gradient(520px 170px at 0% 0%, color-mix(in srgb, var(--accent) 13%, transparent), transparent 70%), var(--panel);
    box-shadow:0 10px 28px rgba(0,0,0,.12); }
.topic::before { content:""; position:absolute; inset:0 0 auto 0; height:3px; background:linear-gradient(90deg, var(--accent), transparent 80%); }
.topic-head { display:flex; align-items:center; gap:12px; }
.topic-icon { font-size:1.55rem; line-height:1; flex:none; }
.topic-title { font-weight:700; font-size:1.12rem; line-height:1.35; }
.topic-sub { color:var(--muted); font-size:.85rem; }
.topic-head .level { margin-inline-start:auto; }
.level { --lvc:var(--lv0); flex:none; padding:3px 12px; border-radius:999px; font-size:.76rem; font-weight:700; white-space:nowrap;
    color:var(--lvc); border:1px solid color-mix(in srgb, var(--lvc) 60%, transparent); background:color-mix(in srgb, var(--lvc) 12%, transparent); }
.lv0{--lvc:var(--lv0);} .lv1{--lvc:var(--lv1);} .lv2{--lvc:var(--lv2);} .lv3{--lvc:var(--lv3);}
.meter { display:flex; gap:5px; margin:16px 0 8px; }
.meter i { flex:1; height:6px; border-radius:6px; background:var(--line); }
.meter i.on { background:var(--lvc); }
.topic-stats { color:var(--muted); font-size:.8rem; margin-bottom:8px; }
.topic-list { margin-top:6px; }
a.topic-item { display:block; padding:12px 0; border-top:1px solid var(--line); text-decoration:none !important; transition:padding .2s; }
a.topic-item:hover .t { color:var(--accent) !important; }
a.topic-item .t { display:block; color:var(--text) !important; font-weight:500; font-size:.97rem; line-height:1.7; overflow-wrap:anywhere; }
a.topic-item .m { display:block; color:var(--muted); font-size:.76rem; margin-top:2px; }
.topic-empty { color:var(--muted); padding:18px 0 12px; font-size:.88rem; }

.latest { display:flex; flex-direction:column; border:1px solid var(--line); border-radius:18px; background:var(--panel); overflow:hidden; }
.lrow { display:grid; grid-template-columns:78px 1fr auto; gap:6px 14px; align-items:baseline; padding:12px 18px; border-top:1px solid var(--line); }
.lrow:first-child { border-top:0; }
.lrow:hover { background:var(--panel-hover); }
.lrow .when { color:var(--muted); font-size:.78rem; }
.lrow a.what { color:var(--text) !important; font-size:.95rem; line-height:1.65; overflow-wrap:anywhere; text-decoration:none !important; }
.lrow a.what:hover { color:var(--accent) !important; }
.lrow .acts { display:flex; gap:8px; align-items:center; flex-wrap:wrap; justify-content:flex-end; }
.translate-action.inline { margin:0; }
.topic .translate-action { margin:-6px 0 10px 0; }
.chip { font-size:.72rem; padding:2px 10px; border-radius:999px; color:var(--accent); border:1px solid color-mix(in srgb, var(--accent) 50%, transparent); white-space:nowrap; }
.fine { color:var(--muted); font-size:.76rem; margin:12px 4px 0; line-height:1.7; }

/* ── list panels ── */
.section-header { display:flex; align-items:baseline; justify-content:space-between; gap:8px; font-size:clamp(1rem,1.7vw,1.15rem); font-weight:700;
    padding:12px 16px; margin:6px 0 12px; border:1px solid var(--line); border-inline-start:4px solid var(--accent, var(--line)); border-radius:12px;
    background:linear-gradient(90deg, color-mix(in srgb, var(--accent, var(--line)) 10%, var(--panel)), var(--panel)); }
.section-header small { color:var(--muted); font-weight:400; font-size:.78rem; }
.section-header small b { color:var(--alert); font-weight:700; }
.feed-scroll { max-height:72vh; overflow-y:auto; padding-right:6px; scrollbar-width:thin; scrollbar-color:var(--line) transparent; }
.feed-scroll::-webkit-scrollbar { width:6px; } .feed-scroll::-webkit-scrollbar-thumb { background:var(--line); border-radius:6px; }
a.feed-card { display:block; text-decoration:none !important; background:var(--panel); border:1px solid var(--line);
    border-inline-start:4px solid var(--accent); border-radius:14px; padding:14px 18px; margin-bottom:10px;
    transition:background .2s, border-color .2s, box-shadow .2s; }
a.feed-card:hover, a.feed-card:focus-visible { background:var(--panel-hover); border-color:var(--accent); box-shadow:0 8px 22px rgba(0,0,0,.14); outline:none; }
a.feed-card.hit { border-inline-start-color:var(--alert); }
a.feed-card.rtl-card { direction:rtl; text-align:right; }
.feed-title { display:block; color:var(--text) !important; font-weight:600; font-size:clamp(.97rem,1.4vw,1.06rem); line-height:1.75; overflow-wrap:anywhere; }
.feed-meta { display:flex; flex-wrap:wrap; gap:6px 14px; margin-top:8px; color:var(--muted); font-size:.8rem; }
.feed-meta b { color:var(--accent); font-weight:600; }
.badge { display:inline-block; margin-top:8px; color:var(--alert); border:1px solid color-mix(in srgb, var(--alert) 55%, transparent); border-radius:999px; padding:1px 11px; font-size:.74rem; font-weight:600; }
.translate-action { margin:-4px 0 12px 10px; font-size:.78rem; }
.translate-action a { display:inline-block; padding:3px 10px; border:1px solid color-mix(in srgb, var(--global) 40%, transparent); border-radius:999px;
    color:var(--global) !important; background:color-mix(in srgb, var(--global) 8%, transparent); text-decoration:none !important; }
.translate-action a:hover { background:color-mix(in srgb, var(--global) 16%, transparent); }
.empty { color:var(--muted); text-align:center; padding:40px 12px; border:1px dashed var(--line); border-radius:14px; }
.warn { color:var(--lv2); background:color-mix(in srgb, var(--lv2) 10%, var(--panel)); border:1px solid color-mix(in srgb, var(--lv2) 40%, transparent); border-radius:10px; padding:9px 13px; margin-bottom:10px; font-size:.82rem; }
.note { color:var(--lv1); background:color-mix(in srgb, var(--lv1) 10%, var(--panel)); border:1px solid color-mix(in srgb, var(--lv1) 40%, transparent); border-radius:10px; padding:9px 13px; margin-bottom:10px; font-size:.82rem; }

.global{--accent:var(--global);} .local{--accent:var(--local);} .kurdish{--accent:var(--kurdish);} .deep{--accent:var(--deep);}
.t-iran{--accent:var(--iran);} .t-krg{--accent:var(--krg);} .t-sec{--accent:var(--sec);}

/* ── widgets ── */
div[data-baseweb="select"] > div, .stTextInput input, .stTextArea textarea,
[data-testid="stSelectbox"] div:has(> input), [data-testid="stTextInput"] div:has(> input), [data-testid="stTextArea"] div:has(> textarea)
{ background-color:var(--panel) !important; border-color:var(--line) !important; color:var(--text) !important; border-radius:12px !important; }
div[data-baseweb="select"] *, [data-testid="stSelectbox"] input, [data-testid="stSelectbox"] [role="combobox"] * { color:var(--text) !important; -webkit-text-fill-color:var(--text); }
input::placeholder, textarea::placeholder { color:var(--muted) !important; opacity:.85; -webkit-text-fill-color:var(--muted); }
.stButton > button { background:var(--panel); color:var(--text); border:1px solid var(--line); border-radius:12px; font-weight:600; min-height:2.6rem; transition:border-color .2s, color .2s; }
.stButton > button:hover { border-color:var(--iran); color:var(--iran); }

@media (max-width:900px) {
    div[data-testid="stHorizontalBlock"] { flex-wrap:wrap !important; gap:.6rem !important; }
    div[data-testid="stColumn"], div[data-testid="column"] { min-width:100% !important; flex:1 1 100% !important; }
    .feed-scroll { max-height:60vh; }
    .lrow { grid-template-columns:1fr; } .lrow .acts { justify-content:flex-start; }
    .topic { padding:16px 16px 6px; }
    .topic-head { flex-wrap:wrap; row-gap:10px; } .topic-icon { font-size:1.3rem; } .topic-head .level { margin-inline-start:0; }
}
@media (prefers-reduced-motion:reduce) { * { animation:none !important; transition:none !important; } }
"""

CALM_CSS = """
.badge, .alert-n, .meter, .level, .stats-sec { display:none !important; }
a.feed-card.hit { border-inline-start-color:var(--accent) !important; }
"""


def inject_css():
    theme = DAY if st.session_state.get("day_mode") else NIGHT
    root = ":root{" + ";".join(f"--{k}:{v}" for k, v in theme.items()) + ";}"
    scheme = "color-scheme:light;" if st.session_state.get("day_mode") else "color-scheme:dark;"
    calm = CALM_CSS if st.session_state.get("calm") else ""
    st.markdown(f"<style>{root} .stApp{{{scheme}}} {BASE_CSS} {calm}</style>", unsafe_allow_html=True)


inject_css()


# ───────────────────────── DATA LAYER ─────────────────────────
@st.cache_resource
def get_store():
    return {"data": {}, "fail": {}, "disc": {}, "lock": threading.Lock()}


def _short(exc: Exception) -> str:
    if isinstance(exc, requests.Timeout):
        return f"timed out after {TIMEOUT[1]}s"
    if isinstance(exc, requests.HTTPError) and exc.response is not None:
        code = exc.response.status_code
        return "HTTP 429 (Google is limiting requests, wait a minute)" if code == 429 else f"HTTP {code}"
    if isinstance(exc, requests.ConnectionError):
        return "connection failed"
    return str(exc)[:160] or type(exc).__name__


def _fetch_feed(url: str, default_source: str):
    r = None
    for attempt in range(RETRY_ATTEMPTS + 1):
        r = requests.get(url, headers=HEADERS, timeout=TIMEOUT)     # a timeout raises immediately
        if r.status_code in (429, 500, 502, 503, 504) and attempt < RETRY_ATTEMPTS:
            time.sleep(RETRY_BACKOFF * (attempt + 1))
            continue
        r.raise_for_status()
        break

    data = feedparser.parse(r.content)
    if not data.entries:
        ctype = r.headers.get("Content-Type", "?").split(";")[0]
        if "xml" not in ctype.lower() and b"<rss" not in r.content[:2000]:
            raise ValueError(f"not a feed (got {ctype})")
        return []                                   # a valid search with simply no results

    items = []
    for e in data.entries[:PER_QUERY_LIMIT]:
        parsed = e.get("published_parsed") or e.get("updated_parsed")
        source = e.get("source", {}).get("title", default_source)
        title = e.get("title", "(no title)")
        if title.endswith(f" - {source}"):
            title = title[: -len(source) - 3]
        items.append({
            "title": title,
            "link": e.get("link", "#"),
            "source": source,
            "ts": calendar.timegm(parsed) if parsed else None,
            "raw_date": (e.get("published") or e.get("updated") or "")[:22],
        })
    return items


def _target(target):
    return (target, ()) if isinstance(target, str) else (target[0], tuple(target[1]))


def _is_429(exc) -> bool:
    return isinstance(exc, requests.HTTPError) and exc.response is not None and exc.response.status_code == 429


def fetch_fallbacks(fallbacks):
    """Download the direct RSS feeds (label, url) in parallel and merge what answers."""
    def one(fb):
        try:
            return fetch_raw(fb[1], fb[0])
        except Exception:  # noqa: BLE001
            return []
    with ThreadPoolExecutor(max_workers=min(MAX_WORKERS, len(fallbacks))) as ex:
        return [it for chunk in ex.map(one, fallbacks) for it in chunk]


class _Links(HTMLParser):
    """Collects (href, visible text) for every <a>."""
    def __init__(self):
        super().__init__()
        self.links, self._href, self._buf = [], None, []

    def handle_starttag(self, tag, attrs):
        if tag == "a":
            self._href, self._buf = dict(attrs).get("href"), []

    def handle_data(self, data):
        if self._href is not None:
            self._buf.append(data)

    def handle_endtag(self, tag):
        if tag == "a" and self._href is not None:
            self.links.append((self._href, " ".join("".join(self._buf).split())))
            self._href = None


_MENU = re.compile(r"/(category|categories|tag|tags|author|authors|page|live|about|contact|search|video|videos|archive)(/|$)", re.I)


def _looks_like_article(path: str) -> bool:
    return bool(re.search(r"\d{3,}", path)) or path.strip("/").count("/") >= 2 or len(path.strip("/")) >= 18


def _page_text(r) -> str:
    try:
        return r.content.decode("utf-8")
    except UnicodeDecodeError:
        return r.text


def scan_headlines(page: str, base: str, name: str):
    """Last resort: read the headline links straight off a news homepage (no dates available)."""
    parser = _Links()
    parser.feed(page)
    host = urlparse(base).netloc.replace("www.", "")
    items, seen = [], set()
    for href, text in parser.links:
        if not href or href.startswith(("#", "javascript:", "mailto:", "tel:")):
            continue
        url = urljoin(base, href)
        u = urlparse(url)
        if host.split(".")[-2] not in u.netloc or _MENU.search(u.path) or not _looks_like_article(u.path):
            continue
        if not (22 <= len(text) <= 220) or text.count(" ") < 2 or url in seen or text in seen:
            continue
        seen.update((url, text))
        items.append({"title": text, "link": url, "source": name, "ts": None, "raw_date": "homepage", "via": "scan"})
        if len(items) >= PER_QUERY_LIMIT:
            break
    return items


def fetch_site(home: str, name: str, store=None):
    """RSS auto-discovery -> common feed paths -> homepage headline scan."""
    disc = store.setdefault("disc", {}) if store is not None else {}
    known = disc.get(home)
    if known and time.time() - known[0] < 86400 and known[1] != "scan":
        try:
            items = _fetch_feed(known[1], name)
            for it in items:
                it["via"] = "rss"
            return items
        except Exception:  # noqa: BLE001
            disc.pop(home, None)

    r = requests.get(home, headers=HEADERS, timeout=TIMEOUT)
    r.raise_for_status()
    page = _page_text(r)
    root = f"{urlparse(r.url).scheme}://{urlparse(r.url).netloc}"

    cands = []
    for m in re.finditer(r"<link\b[^>]*>", page, re.I):
        tag = m.group(0)
        if re.search(r'rel=["\']?alternate', tag, re.I) and re.search(r'type=["\']?application/(rss|atom)\+xml', tag, re.I):
            h = re.search(r'href=["\']([^"\']+)', tag, re.I)
            if h and "comment" not in h.group(1).lower():
                cands.append(urljoin(r.url, h.group(1).replace("&amp;", "&")))
    cands += [home.rstrip("/") + "/feed", home.rstrip("/") + "/rss", root + "/feed", root + "/rss"]
    if known and known[1] == "scan" and time.time() - known[0] < 86400:
        cands = []                                  # we already know this site has no usable feed

    tried = set()
    for c in cands:
        if c in tried:
            continue
        tried.add(c)
        try:
            items = _fetch_feed(c, name)
        except Exception:  # noqa: BLE001
            continue
        if items:
            disc[home] = (time.time(), c)
            for it in items:
                it["via"] = "rss"
            return items

    items = scan_headlines(page, r.url, name)
    if not items:
        raise ValueError("no feed and no headlines found")
    disc[home] = (time.time(), "scan")
    return items


def fetch_raw(url: str, default_source: str, store=None):
    if url.startswith("site::"):
        return fetch_site(url[6:], default_source, store)
    return _fetch_feed(url, default_source)


def load(store, target, name: str):
    """Return (items, message). message is None when fine, "↪ ..." when direct feeds were used
    instead of Google, or an error text. Never raises; serves stale data if everything fails."""
    url, fallbacks = _target(target)
    now = time.time()
    hit = store["data"].get(url)
    if hit and now - hit[0] < CACHE_TTL:
        return hit[1], hit[2]
    bad = store["fail"].get(url)
    if bad and now - bad[0] < FAIL_TTL:
        return (hit[1] if hit else []), bad[1]

    def save(items, note):
        with store["lock"]:
            if len(store["data"]) > 400:                       # keep memory bounded
                for k in sorted(store["data"], key=lambda k: store["data"][k][0])[:100]:
                    store["data"].pop(k, None)
            store["data"][url] = (time.time(), items, note)
            store["fail"].pop(url, None)

    is_google = "news.google.com" in url
    if is_google and now < store.get("g_block", 0):
        err = f"Google cooldown ({int(store['g_block'] - now)}s left)"
    else:
        try:
            items = fetch_raw(url, name, store)
            save(items, None)
            return items, None
        except Exception as exc:  # noqa: BLE001
            err = _short(exc)
            if is_google and _is_429(exc):
                store["g_block"] = time.time() + G_COOLDOWN

    if fallbacks:
        items = fetch_fallbacks(fallbacks)
        if items:
            note = f"↪ {name}: {err} - showing direct RSS feeds"
            save(items, note)
            return items, note

    with store["lock"]:
        store["fail"][url] = (time.time(), err)
    return (hit[1] if hit else []), err


_SUFFIX = re.compile(r"\s[-–|]\s[^-–|]{2,40}$")
_NON_WORD = re.compile(r"[^a-z0-9\u0600-\u06FF]+")
_ARABIC = re.compile(r"[\u0600-\u06FF]")


def dedup_key(title: str) -> str:
    return _NON_WORD.sub("", _SUFFIX.sub("", title).lower())


def collect(store, sources: dict):
    """Run the searches in parallel, merge, drop duplicates, newest first.
    Returns (items, errors, ok_count, notes)."""
    with ThreadPoolExecutor(max_workers=min(MAX_WORKERS, max(1, len(sources)))) as ex:
        results = list(ex.map(lambda kv: (kv[0], *load(store, kv[1], kv[0])), sources.items()))
    errors = [(n, m) for n, _, m in results if m and not m.startswith("↪")]
    notes = [(n, m) for n, _, m in results if m and m.startswith("↪")]
    seen, merged = set(), []
    for _, items, _ in results:
        for it in items:
            k = dedup_key(it["title"])
            if k and k not in seen:
                seen.add(k)
                merged.append(it)
    merged.sort(key=lambda i: i["ts"] or 0, reverse=True)
    return merged, errors, len(results) - len(errors), notes


def time_ago(ts, fallback=""):
    if not ts:
        return fallback or "—"
    d = max(0, int(time.time() - ts))
    if d < 60:
        return "just now"
    if d < 3600:
        return f"{d // 60}m ago"
    if d < 86400:
        return f"{d // 3600}h ago"
    return f"{d // 86400}d ago"


# ───────────────────────── MATCHING ─────────────────────────
def _norm(text: str) -> str:
    text = text.lower().replace("ي", "ی").replace("ى", "ی").replace("ك", "ک").replace("\u200c", "")
    return " " + _NON_WORD.sub(" ", text).strip() + " "


def term_in(term: str, hay: str) -> bool:
    """Latin words match whole words (plus plural -s); Arabic-script words match by prefix,
    because Kurdish/Arabic attach suffixes (هەولێر -> هەولێری)."""
    t = _norm(term).strip()
    if not t:
        return False
    if _ARABIC.search(t):
        return f" {t}" in hay
    return f" {t} " in hay or f" {t}s " in hay


def topic_match(title: str, words) -> bool:
    hay = _norm(title)
    return any(term_in(w, hay) for w in words)


def match_watchlist(title: str, keywords: list) -> list:
    hay = _norm(title)
    return [k for k in keywords if term_in(k, hay)]


def red_alert_tags(title: str):
    hay = _norm(title)

    def has(terms):
        return any(term_in(t, hay) for t in terms)

    tags = []
    if has(IRAN_TERMS) and (has(US_TERMS) or has(CONFLICT_TERMS)):
        tags.append("IRAN–US")
    if has(SYRIA_TERMS) and has(CONFLICT_TERMS):
        tags.append("SYRIA")
    if has(KURDISTAN_TERMS) and has(CONFLICT_TERMS):
        tags.append("KRG-SECURITY")
    return tags


def parse_keywords(text: str):
    return [k.strip().lower() for k in re.split(r"[,،\n]", text) if k.strip()]


def parse_custom(text: str, window: str):
    """Lines of `Name | Google News query` (or `Name | https://rss-url`)."""
    out = {}
    for line in text.splitlines():
        if "|" not in line:
            continue
        name, value = (p.strip() for p in line.split("|", 1))
        if not (name and value):
            continue
        if value.startswith(("http://", "https://")):
            out[name] = value
        else:
            ed = "ar" if _ARABIC.search(value) else "en"
            out[name] = gnews_url(value, window, ed)
    return out


def build_groups(presets: dict, window: str, extra=None):
    """Value = Google News URL, or (URL, fallback feeds) when fallbacks exist.
    Edition "site" = read a news site directly (homepage URL), with Google News as the fallback."""
    groups = {}
    for g, items in presets.items():
        groups[g] = {}
        for name, spec in items.items():
            q, ed, *fb = spec
            if ed == "site":
                host = urlparse(q).netloc.replace("www.", "")
                groups[g][name] = ("site::" + q, (("Google News", gnews_url(f"site:{host}", window, "ar")),))
                continue
            url = gnews_url(q, window, ed)
            groups[g][name] = (url, tuple(fb[0])) if fb and fb[0] else url
    if extra:
        groups["Custom"] = extra
    return groups


def flatten(groups: dict) -> dict:
    return {n: u for g in groups.values() for n, u in g.items()}


# ───────────────────────── UI ─────────────────────────
BRIEFING = [
    {"cls": "t-iran", "icon": "🇮🇷 ↔ 🇺🇸", "title": "Iran – US", "sub": "ئێران و ئەمریکا",
     "refs": [(GLOBAL_PRESETS, "Topics", "Iran – US")]},
    {"cls": "t-krg", "icon": "🏔️", "title": "Kurdistan Region & Iraq", "sub": "هەرێمی کوردستان و عێراق",
     "refs": [(LOCAL_PRESETS, "Iraq & Kurdistan", "Kurdistan Region"), (LOCAL_PRESETS, "Iraq & Kurdistan", "Kirkuk · Baghdad · Mosul · Basra")]},
    {"cls": "t-sec", "icon": "🛰️", "title": "Middle East security", "sub": "گرژییە ئەمنییەکانی ڕۆژهەڵاتی ناوەڕاست",
     "refs": [(LOCAL_PRESETS, "Security & energy", "Drones · missiles · strikes"), (LOCAL_PRESETS, "Middle East", "Iran – Iraq militias"),
              (LOCAL_PRESETS, "Middle East", "Syria · Damascus & Rojava")]},
]
LEVELS = [("Quiet", "ئارام"), ("Watch", "چاودێری"), ("Elevated", "بەرزبووەوە"), ("High", "توند")]
RECENT = 6 * 3600


def is_security(title: str) -> bool:
    hay = _norm(title)
    return any(term_in(t, hay) for t in CONFLICT_TERMS)


def activity(items, now, trend_ok):
    """Heuristic only: counts security-related headlines of the last 6 h (and compares with the 6 h before)."""
    recent = [i for i in items if i["ts"] and now - i["ts"] <= RECENT]
    prev = [i for i in items if i["ts"] and RECENT < now - i["ts"] <= 2 * RECENT]
    sec = sum(1 for i in recent if is_security(i["title"]))
    sec_prev = sum(1 for i in prev if is_security(i["title"]))
    level = 0 if sec < 2 else 1 if sec < 6 else 2 if sec < 12 else 3
    trend = ""
    if trend_ok:
        trend = "↑" if sec - sec_prev >= 2 else "↓" if sec_prev - sec >= 2 else "→"
    return level, len(recent), sec, trend


def briefing(store, window):
    now = time.time()
    trend_ok = window not in ("1h", "6h")
    cards, latest = [], []
    for t in BRIEFING:
        sources = {}
        for presets, group, name in t["refs"]:
            q, ed, *fb = presets[group][name]
            url = gnews_url(q, window, ed)
            sources[name] = (url, tuple(fb[0])) if fb and fb[0] else url
        items, errors, ok, notes = collect(store, sources)
        level, n_recent, n_sec, trend = activity(items, now, trend_ok)
        lname, lku = LEVELS[level]
        meter = "".join(f'<i class="{"on" if k <= level else ""}"></i>' for k in range(4))
        rows = ""
        for it in items[:5]:
            rows += (f'<a class="topic-item" href="{html.escape(it["link"], quote=True)}" target="_blank" rel="noopener noreferrer">'
                     f'<span class="t" dir="auto">{html.escape(it["title"])}</span>'
                     f'<span class="m"><bdi>{html.escape(it["source"])}</bdi> · <bdi>{html.escape(time_ago(it["ts"], it["raw_date"]))}</bdi></span></a>'
                     f'{translate_chip(it["title"])}')
        if not rows:
            rows = '<div class="topic-empty">No headlines right now. Google may be limiting requests — it retries automatically.</div>'
        stats = (f'{len(items)} headlines · {n_recent} in the last 6 h'
                 + (f'<span class="stats-sec"> · {n_sec} security-related {trend}</span>' if items else ""))
        cards.append(
            f'<div class="topic {t["cls"]}"><div class="topic-head"><span class="topic-icon">{t["icon"]}</span>'
            f'<div><div class="topic-title">{html.escape(t["title"])}</div><div class="topic-sub" dir="rtl">{t["sub"]}</div></div>'
            f'<span class="level lv{level}">{lname} · {lku}</span></div>'
            f'<div class="meter lv{level}">{meter}</div><div class="topic-stats">{stats}</div>'
            f'<div class="topic-list">{rows}</div></div>')
        for it in items[:12]:
            latest.append({**it, "chip": t["title"], "cls": t["cls"]})

    st.markdown(f'<div class="briefing">{cards[0]}{cards[1]}{cards[2]}</div>', unsafe_allow_html=True)

    seen, rows = set(), ""
    for it in sorted(latest, key=lambda i: i["ts"] or 0, reverse=True):
        k = dedup_key(it["title"])
        if k in seen:
            continue
        seen.add(k)
        rows += (f'<div class="lrow {it["cls"]}"><span class="when">{html.escape(time_ago(it["ts"], it["raw_date"]))}</span>'
                 f'<a class="what" href="{html.escape(it["link"], quote=True)}" target="_blank" rel="noopener noreferrer" dir="auto">'
                 f'{html.escape(it["title"])} <span style="color:var(--muted)">· <bdi>{html.escape(it["source"])}</bdi></span></a>'
                 f'<span class="acts"><span class="chip">{html.escape(it["chip"])}</span>{translate_chip(it["title"], inline=True)}</span></div>')
        if len(seen) >= 10:
            break
    st.markdown(f'<div class="sec-title">Latest across the three topics <small>newest first</small></div>'
                f'<div class="latest">{rows or "<div class=topic-empty style=padding:16px>—</div>"}</div>'
                f'<div class="fine">The level shows how many <b>security-related headlines</b> appeared in the last 6 hours (keyword-based, '
                f'compared with the 6 hours before). It reflects news volume, <b>not an assessment of real risk</b>. '
                f'نیشانەکە تەنها ژمارەی هەواڵە، نەک هەڵسەنگاندنی مەترسیی ڕاستەقینە.</div>', unsafe_allow_html=True)


def translate_chip(title: str, inline: bool = False) -> str:
    """The 'translate with Google' pill, shown for headlines that are not already in Arabic script."""
    if _ARABIC.search(title):
        return ""
    a = (f'<a href="{html.escape(translate_link(title), quote=True)}" target="_blank" rel="noopener noreferrer">'
         f'🌐 وەرگێڕان بە Google</a>')
    return f'<span class="translate-action inline">{a}</span>' if inline else f'<div class="translate-action">{a}</div>'


def translate_link(text: str) -> str:
    return "https://translate.google.com/?" + urlencode({"sl": "en", "tl": "ckb", "text": text, "op": "translate"})


def render_cards(items, kind: str, icon: str, is_rtl: bool = False):
    if not items:
        body = '<div class="empty">هیچ هەواڵێک نەدۆزرایەوە / No items. Try a longer time window or another search.</div>'
    else:
        cards = []
        for i in items:
            tags = i["red_tags"] + [h for h in i["hits"] if h not in i["red_tags"]]
            badge = f'<span class="badge">🔴 {html.escape(" · ".join(tags))}</span>' if tags else ""
            btn = ""
            if not _ARABIC.search(i["title"]):
                btn = (f'<div class="translate-action"><a href="{html.escape(translate_link(i["title"]), quote=True)}" '
                       f'target="_blank" rel="noopener noreferrer">🌐 وەرگێڕان بە Google</a></div>')
            cls = f'feed-card {kind}{" rtl-card" if is_rtl else ""}{" hit" if tags else ""}'
            cards.append(
                f'<a class="{cls}" href="{html.escape(i["link"], quote=True)}" target="_blank" rel="noopener noreferrer">'
                f'<span class="feed-title" dir="auto">{html.escape(i["title"])}</span>'
                f'<span class="feed-meta"><span>{icon} <b><bdi>{html.escape(i["source"])}</bdi></b></span>'
                f'<span>🕒 <bdi>{html.escape(time_ago(i["ts"], i["raw_date"]))}</bdi></span></span>{badge}</a>{btn}'
            )
        body = "".join(cards)
    st.markdown(f'<div class="feed-scroll">{body}</div>', unsafe_allow_html=True)


def render_block(items, errors, ok, notes, total, head, title, kind, icon, keywords, only_hits, is_rtl=False):
    for it in items:
        it["hits"] = match_watchlist(it["title"], keywords)
        it["red_tags"] = red_alert_tags(it["title"])
    alert_count = sum(1 for i in items if i["hits"] or i["red_tags"])
    if only_hits:
        items = [i for i in items if i["hits"] or i["red_tags"]]

    alerts = f' · <b class="alert-n">{alert_count} alerts</b>' if alert_count else ""
    head.markdown(
        f'<div class="section-header {kind}">{title}'
        f'<small>{len(items)} items · {ok}/{total} sources{alerts}</small></div>',
        unsafe_allow_html=True,
    )
    if notes:
        names = ", ".join(html.escape(n) for n, _ in notes[:4]) + (f" and {len(notes) - 4} more" if len(notes) > 4 else "")
        st.markdown(f'<div class="note">ℹ️ Backup source used for: {names}.</div>', unsafe_allow_html=True)
    if errors:
        shown = ", ".join(f"{html.escape(n)} ({html.escape(e)})" for n, e in errors[:5])
        more = f" and {len(errors) - 5} more" if len(errors) > 5 else ""
        st.markdown(f'<div class="warn">⚠️ {len(errors)} source(s) not refreshed: {shown}{more}.</div>', unsafe_allow_html=True)
    render_cards(items[:PANEL_LIMIT], kind, icon, is_rtl)


def show_results(store, sources, head, title, kind, icon, keywords, only_hits, is_rtl=False):
    items, errors, ok, notes = collect(store, sources)
    render_block(items, errors, ok, notes, len(sources), head, title, kind, icon, keywords, only_hits, is_rtl)


def panel(store, title, kind, icon, groups, key, keywords, only_hits, is_rtl=False):
    head = st.empty()
    flat = flatten(groups)
    choice = st.selectbox("Search", [ALL] + [f"▸ {g}" for g in groups] + list(flat),
                          key=key, label_visibility="collapsed")
    if choice == ALL:
        sources = flat
    elif choice.startswith("▸ "):
        sources = groups[choice[2:]]
    else:
        sources = {choice: flat[choice]}
    show_results(store, sources, head, title, kind, icon, keywords, only_hits, is_rtl)


def deep_search(store, query, window, keywords, only_hits):
    if not query.strip():
        st.markdown('<div class="empty">🔎 Type a topic in the search box above.<br>'
                    'Operators: <code>"exact phrase"</code> · <code>OR</code> · <code>-exclude</code> · '
                    '<code>site:rudaw.net</code> · <code>intitle:drone</code></div>', unsafe_allow_html=True)
        return
    head = st.empty()
    edition = st.selectbox("Language edition", ["en", "ar"], key="deep_edition", label_visibility="collapsed",
                           format_func=lambda k: "English (US edition)" if k == "en" else "Arabic-script · Iraq edition (عربی / کوردی)")
    sources = {f"Google News: {query}": gnews_url(query, window, edition)}
    show_results(store, sources, head, f"🔎 Deep search · {html.escape(query)}", "deep", "🔎", keywords, only_hits,
                 is_rtl=(edition == "ar"))


def dashboard(view, window, query, keywords, only_hits, custom_text):
    store = get_store()
    st.markdown(f'<div class="updated">Updated {datetime.now().strftime("%H:%M:%S")} · window {window} · '
                f'auto-refresh every {AUTO_REFRESH // 60} min · only the open view is fetched</div>',
                unsafe_allow_html=True)

    if view == VIEWS[0]:
        briefing(store, window)
    elif view == VIEWS[1]:
        custom = parse_custom(custom_text, window)
        c1, c2 = st.columns(2, gap="large")
        with c1:
            panel(store, "🌍 Global news &amp; geopolitics", "global", "🌐",
                  build_groups(GLOBAL_PRESETS, window), "global_select", keywords, only_hits)
        with c2:
            panel(store, "🇮🇶 Iraq, KRG &amp; Middle East", "local", "📡",
                  build_groups(LOCAL_PRESETS, window, custom), "local_select", keywords, only_hits)
    elif view == VIEWS[2]:
        sites = build_groups(KURDISH_SITES, window)
        flat_sites = flatten(sites)
        pool, p_err, p_ok, p_notes = collect(store, flat_sites)          # fetched once, shared by both panels
        c1, c2 = st.columns(2, gap="large")
        with c1:
            head = st.empty()
            topic = st.selectbox("Topic", [KU_ALL] + list(KURDISH_TOPICS), key="ku_topic", label_visibility="collapsed")
            if topic == KU_ALL:
                chosen = pool
            else:
                chosen = [i for i in pool if topic_match(i["title"], KURDISH_TOPICS[topic])]
            render_block(chosen, [], p_ok, [], len(flat_sites), head, "📍 بابەتەکان", "kurdish", "☀️", keywords, only_hits, True)
        with c2:
            panel(store, "📺 ماڵپەڕە کوردییەکان", "kurdish", "📰", sites, "ku_sites_select", keywords, only_hits, is_rtl=True)
    else:
        deep_search(store, query, window, keywords, only_hits)


VIEWS = ["🧭 Briefing", "🌍 Global & Regional", "☀️ کوردی (Kurdish)", "🔎 Deep search"]

if hasattr(st, "fragment"):
    dashboard = st.fragment(run_every=AUTO_REFRESH)(dashboard)

# ───────────────────────── PAGE ─────────────────────────
c_title, c_search, c_theme, c_btn = st.columns([5, 3, 1.6, 1.6], vertical_alignment="center")
with c_title:
    st.markdown(
        '<div class="topbar"><span class="live-dot"></span><div><h1>🛰️ Global &amp; KRG OSINT Command Center</h1>'
        '<div class="sub" dir="rtl">ناوەندی زانیاریی سەرچاوە کراوەکانی جیهان و هەرێمی کوردستان</div></div></div>',
        unsafe_allow_html=True)
with c_search:
    query = st.text_input("Deep search", key="q", label_visibility="collapsed",
                          placeholder="🔎 قووڵ بگەڕێ لە Google News / Deep search…")
with c_theme:
    st.toggle("☀️ Day", key="day_mode", help="Soft light theme for daytime reading")
with c_btn:
    if st.button("🔄 Refresh", use_container_width=True):
        store = get_store()
        with store["lock"]:
            store["data"].clear()
            store["fail"].clear()
        st.rerun()

# typing a new search jumps to the Deep search view automatically
if query.strip() and query != st.session_state.get("_last_q"):
    st.session_state["view"] = VIEWS[3]
st.session_state["_last_q"] = query

c_view, c_window = st.columns([5, 2], vertical_alignment="center")
with c_view:
    view = st.radio("View", VIEWS, key="view", horizontal=True, label_visibility="collapsed")
with c_window:
    window_label = st.selectbox("Time window", list(WINDOWS), index=2, key="window",
                                label_visibility="collapsed", help="How far back Google News should look")
window = WINDOWS[window_label]

with st.expander("⚙️ Watchlist & custom searches"):
    wl_text = st.text_input("Watchlist keywords (comma separated)", value=DEFAULT_WATCHLIST,
                            help="Matching headlines are highlighted. Kurdish/Arabic words match by prefix.")
    st.toggle("🕊️ Calm mode", key="calm",
              help="Hides red alert badges, alert counts and the activity meter. Same headlines, quieter look.")
    only_hits = st.checkbox("Show only headlines that match the watchlist or a red-alert pattern")
    custom_text = st.text_area("Extra searches for the regional panel (one per line: Name | Google News query or RSS URL)",
                               placeholder='Halabja water | Halabja AND (water OR dam)', height=90)

dashboard(view, window, query, parse_keywords(wl_text), only_hits, custom_text)

with st.expander("🩺 Search health (test every search)"):
    st.caption("Runs every preset search once and shows how many headlines each returned.")
    if st.button("Check all searches now"):
        store = get_store()
        everything = {}
        for presets in (GLOBAL_PRESETS, LOCAL_PRESETS, KURDISH_SITES):
            everything.update(flatten(build_groups(presets, window)))
        with store["lock"]:
            store.pop("g_block", None)
            for t in everything.values():
                u = _target(t)[0]
                store["data"].pop(u, None)
                store["fail"].pop(u, None)
        with st.spinner(f"Running {len(everything)} searches…"):
            with ThreadPoolExecutor(max_workers=MAX_WORKERS) as ex:
                res = list(ex.map(lambda kv: (kv[0], *load(store, kv[1], kv[0])), everything.items()))
        rows = []
        for n, items, m in res:
            via = {"rss": " (RSS)", "scan": " (homepage scan)"}.get(items[0].get("via"), "") if items else ""
            status = ("✅ OK" + via) if not m else ("↪ backup used" if m.startswith("↪") else f"❌ {m}")
            rows.append({"Search": n, "Status": status, "Items": len(items),
                         "Newest": time_ago(max((i["ts"] or 0 for i in items), default=0)) if items else "—"})
        rows.sort(key=lambda r: (r["Status"] == "✅ OK", r["Search"]))
        st.dataframe(rows, use_container_width=True, hide_index=True)
