#!/usr/bin/env python3
"""
NBA player prop model + local dashboard.  Standard library only.

  export ODDS_API_KEY=your_key        (SportsGameOdds by default; --provider theoddsapi for The Odds API)
  python3 props.py                    -> open http://localhost:8000
  python3 props.py --demo             -> fake data, no key, no API credits
  python3 props.py --host 0.0.0.0     -> also reachable from your phone on the same Wi-Fi
  python3 props.py --build site       -> write a static site/index.html (used by the GitHub workflow)

Pipeline
  1. Box scores for this season and last (ESPN, cached on disk; first run takes a minute).
  2. Projection = projected minutes x per-minute rate x opponent factor.
  3. Negative-binomial distribution around the projection -> P(over), P(under), P(push).
  4. Prop lines from the odds provider -> no-vig market probability, best price per side.
  5. Dashboard blends model and market probability and ranks bets by expected value.
"""
import argparse, gzip, json, math, os, random, re, threading, time, unicodedata
import urllib.error, urllib.parse, urllib.request
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# ----------------------------------------------------------------- settings
MARKETS = {                       # Odds API market key -> (label, stat field)
    "player_points": ("Points", "PTS"),
    "player_rebounds": ("Rebounds", "REB"),
    "player_assists": ("Assists", "AST"),
    "player_threes": ("Threes", "FG3M"),
    "player_points_rebounds_assists": ("PRA", "PRA"),
}
REGIONS = "us"
RATE_HALF_LIFE = 15      # games; how fast old games fade from per-minute rates
MIN_HALF_LIFE = 5        # games; minutes react faster to role changes
PRIOR_SEASON_W = 0.5     # extra discount on last season's games
RATE_PRIOR_MIN = 40      # pseudo-minutes of league-average rate (shrinkage)
OPP_PRIOR_GAMES = 10     # shrinkage on the opponent factor
ALPHA_PRIOR_GAMES = 10   # shrinkage on each player's dispersion
ALPHA_DEFAULT = {"PTS": 0.07, "REB": 0.08, "AST": 0.09, "FG3M": 0.06, "PRA": 0.055}
LOOKAHEAD_HOURS = 30     # which upcoming games to pull props for
ODDS_TTL = 600           # seconds; each refresh costs credits (markets x regions per game)
STATS_TTL = 6 * 3600
CACHE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "cache")


# ----------------------------------------------------------------- helpers
def http_json(url, headers=None, timeout=45, tries=3):
    last = None
    for i in range(tries):
        try:
            req = urllib.request.Request(url, headers=headers or {})
            with urllib.request.urlopen(req, timeout=timeout) as r:
                raw = r.read()
                if r.headers.get("Content-Encoding") == "gzip":
                    raw = gzip.decompress(raw)
                return json.loads(raw), dict(r.headers)
        except urllib.error.HTTPError as e:
            body = e.read()[:200].decode("utf-8", "replace")
            raise RuntimeError(f"HTTP {e.code} from {urllib.parse.urlsplit(url).netloc}: {body}")
        except Exception as e:                      # timeouts, resets: retry
            last = e
            time.sleep(1.5 * (i + 1))
    raise RuntimeError(f"{urllib.parse.urlsplit(url).netloc} unreachable: {last}")


def cache_path(name):
    os.makedirs(CACHE_DIR, exist_ok=True)
    return os.path.join(CACHE_DIR, name)


def cache_read(name, ttl=None):
    p = cache_path(name)
    if not os.path.exists(p) or (ttl is not None and time.time() - os.path.getmtime(p) > ttl):
        return None
    with open(p) as f:
        return json.load(f)


def cache_write(name, obj):
    with open(cache_path(name), "w") as f:
        json.dump(obj, f)


def norm_name(s):
    s = unicodedata.normalize("NFKD", s or "")
    s = "".join(c for c in s if not unicodedata.combining(c)).lower()
    toks = re.sub(r"[^a-z ]", "", s.replace("-", " ")).split()
    return " ".join(t for t in toks if t not in {"jr", "sr", "ii", "iii", "iv", "v"})


def norm_team(s):
    s = (s or "").lower().strip()
    return "los angeles clippers" if s == "la clippers" else s


def season_str(d):
    y = d.year if d.month >= 10 else d.year - 1
    return f"{y}-{(y + 1) % 100:02d}"


def dec_odds(american):
    return 1 + (american / 100 if american > 0 else 100 / -american)


# ----------------------------------------------------------------- data: box scores (ESPN)
ESPN = "https://site.api.espn.com/apis/site/v2/sports/basketball/nba/"
ESPN_HEADERS = {"User-Agent": "Mozilla/5.0", "Accept": "application/json"}


def _espn_day(day):
    """Completed regular-season games on one date -> [(event_id, season_year)]."""
    data, _ = http_json(f"{ESPN}scoreboard?dates={day}", ESPN_HEADERS, timeout=30)
    return [(e["id"], e["season"]["year"]) for e in data.get("events", [])
            if e["season"].get("type") == 2 and e["status"]["type"].get("completed")]


def _espn_box(eid, season):
    """One game's box score -> list of player rows."""
    data, _ = http_json(f"{ESPN}summary?event={eid}", ESPN_HEADERS, timeout=30)
    date = data["header"]["competitions"][0]["date"][:10]
    rows = []
    for t in data.get("boxscore", {}).get("players", []):
        st = t["statistics"][0]
        ix = {k: i for i, k in enumerate(st.get("labels") or st["names"])}
        for a in st["athletes"]:
            v = a.get("stats") or []
            if a.get("didNotPlay") or len(v) <= max(ix.values()):
                continue
            try:
                mins = float(v[ix["MIN"]])
                row = {"season": season, "pid": a["athlete"]["id"], "name": a["athlete"]["displayName"],
                       "team": t["team"]["abbreviation"], "team_name": t["team"]["displayName"],
                       "gid": eid, "date": date, "matchup": "", "MIN": mins,
                       "PTS": int(v[ix["PTS"]]), "REB": int(v[ix["REB"]]), "AST": int(v[ix["AST"]]),
                       "FG3M": int(v[ix["3PT"]].split("-")[0])}
            except (ValueError, KeyError):
                continue
            if mins > 0:
                rows.append(row)
    return rows


def fetch_gamelog(season):
    """All player box-score lines for one regular season, as a list of dicts.

    Walks ESPN's daily scoreboards and per-game box scores, keeping everything on disk so
    each run only fetches games it has not seen (the first run pulls a full prior season).
    """
    from concurrent.futures import ThreadPoolExecutor
    name = f"espn_{season}.json"
    y = int(season[:4])
    today = datetime.now().date()
    c = cache_read(name) or {"days": {}, "games": {}, "done": False}
    fresh = os.path.exists(cache_path(name)) and time.time() - os.path.getmtime(cache_path(name)) < STATS_TTL
    if not (c["done"] or (fresh and c["games"])):
        start, end = datetime(y, 10, 15).date(), min(today, datetime(y + 1, 4, 20).date())
        days = [(start + timedelta(days=i)) for i in range((end - start).days + 1)]
        need = [d.strftime("%Y%m%d") for d in days
                if d.strftime("%Y%m%d") not in c["days"] or (today - d).days <= 2]
        with ThreadPoolExecutor(12) as ex:
            for d, res in zip(need, ex.map(lambda d: _safe(_espn_day, d), need)):
                if res is not None:
                    c["days"][d] = [eid for eid, yr in res if yr == y + 1]
            todo = sorted({e for ids in c["days"].values() for e in ids} - set(c["games"]))
            got = list(ex.map(lambda e: _safe(_espn_box, e, season), todo))
        failed = 0
        for eid, rows in zip(todo, got):
            if rows:
                c["games"][eid] = rows
            else:
                failed += 1
        if todo and failed > max(3, len(todo) // 10) and not c["games"]:
            raise RuntimeError(f"ESPN box scores unavailable ({failed}/{len(todo)} failed)")
        c["done"] = today > datetime(y + 1, 4, 20).date() and failed == 0 and len(c["days"]) >= len(days)
        cache_write(name, c)
    return [dict(r) for rows in c["games"].values() for r in rows]


def _safe(fn, *a):
    try:
        return fn(*a)
    except Exception:
        return None


# ----------------------------------------------------------------- data: odds
def fetch_odds(key, force=False):
    """Upcoming NBA events with player-prop odds. Returns (events, quota_info)."""
    if not force:
        c = cache_read("odds.json", ODDS_TTL)
        if c is not None:
            return c["events"], c["quota"]
    base = "https://api.the-odds-api.com/v4/sports/basketball_nba"
    events, _ = http_json(f"{base}/events?apiKey={key}")
    now = datetime.now(timezone.utc)
    out, quota = [], {}
    for ev in events:
        t = datetime.fromisoformat(ev["commence_time"].replace("Z", "+00:00"))
        if not (now < t < now + timedelta(hours=LOOKAHEAD_HOURS)):
            continue
        q = urllib.parse.urlencode({"apiKey": key, "regions": REGIONS, "oddsFormat": "american",
                                    "markets": ",".join(MARKETS)})
        data, hdr = http_json(f"{base}/events/{ev['id']}/odds?{q}")
        h = {k.lower(): v for k, v in hdr.items()}
        quota = {"remaining": h.get("x-requests-remaining"), "used": h.get("x-requests-used")}
        out.append(data)
    cache_write("odds.json", {"events": out, "quota": quota})
    return out, quota


SGO_STATS = {"points": "player_points", "rebounds": "player_rebounds", "assists": "player_assists",
             "threePointersMade": "player_threes",
             "points+rebounds+assists": "player_points_rebounds_assists"}
SGO_SKIP_BOOKS = {"prizepicks", "underdog", "sleeper", "parlayplay", "betr", "dabble", "unknown"}  # DFS apps, not prices
DEBUG = {}


def _player_name(ev, pid):
    p = (ev.get("players") or {}).get(pid) or {}
    name = p.get("name") or " ".join(x for x in (p.get("firstName"), p.get("lastName")) if x)
    if name:
        return name
    parts = pid.split("_")
    while parts and (parts[-1].isdigit() or parts[-1].isupper() and len(parts[-1]) <= 5 and len(parts) > 2
                     and parts[-2].isdigit()):
        parts.pop()
    return " ".join(parts).title()


def fetch_odds_sgo(key, force=False):
    """Upcoming NBA events from SportsGameOdds, reshaped to the bookmakers/markets/outcomes layout."""
    if not force:
        c = cache_read("odds_sgo.json", ODDS_TTL)
        if c is not None:
            return c["events"], c["quota"]
    q = urllib.parse.urlencode({"leagueID": "NBA", "oddsAvailable": "true", "limit": 30})
    data, _ = http_json("https://api.sportsgameodds.com/v2/events?" + q,
                        {"x-api-key": key, "Accept": "application/json", "User-Agent": "props-model/1.0"})
    now = datetime.now(timezone.utc)
    out, seen_stats, raw = [], set(), data.get("data") or []
    for ev in raw:
        st = ev.get("status") or {}
        try:
            t = datetime.fromisoformat(str(st.get("startsAt")).replace("Z", "+00:00"))
        except ValueError:
            continue
        if not (now < t < now + timedelta(hours=LOOKAHEAD_HOURS)) or st.get("started") or st.get("cancelled"):
            continue
        books = defaultdict(lambda: defaultdict(list))            # book -> market -> outcomes
        for odd in (ev.get("odds") or {}).values():
            pid = odd.get("playerID") or ""
            if not pid or pid in ("all", "home", "away") or odd.get("periodID") != "game" \
                    or odd.get("betTypeID") != "ou":
                continue
            seen_stats.add(odd.get("statID"))
            mkey = SGO_STATS.get(odd.get("statID"))
            side = odd.get("sideID")
            if not mkey or side not in ("over", "under"):
                continue
            player = _player_name(ev, pid)
            for bk, b in (odd.get("byBookmaker") or {}).items():
                if bk in SGO_SKIP_BOOKS or b.get("available") is False:
                    continue
                try:
                    price, point = int(str(b["odds"]).replace("+", "")), float(b["overUnder"])
                except (KeyError, ValueError, TypeError):
                    continue
                if price == 0:
                    continue
                books[bk][mkey].append({"name": side.title(), "description": player,
                                        "price": price, "point": point})
        tm = ev.get("teams") or {}
        nm = lambda side: ((tm.get(side) or {}).get("names") or {}).get("long") or ""
        out.append({"id": ev.get("eventID"), "commence_time": t.strftime("%Y-%m-%dT%H:%M:%SZ"),
                    "home_team": nm("home"), "away_team": nm("away"),
                    "bookmakers": [{"key": bk, "title": bk, "markets": [{"key": k, "outcomes": o}
                                                                        for k, o in m.items()]}
                                   for bk, m in books.items()]})
    DEBUG.update(raw_events=len(raw), kept=len(out), player_ou_stats=sorted(x for x in seen_stats if x),
                 books=sorted({b["key"] for e in out for b in e["bookmakers"]}),
                 games=[f"{e['away_team']} @ {e['home_team']}" for e in out])
    if raw and not out:
        e0 = raw[0]
        DEBUG["sample_status"] = e0.get("status")
        DEBUG["sample_keys"] = sorted(e0.keys())
    if raw and not any(e["bookmakers"] for e in out):
        e0 = raw[0]
        DEBUG["sample_odd"] = next(iter((e0.get("odds") or {}).values()), None)
        DEBUG["sample_teams"] = e0.get("teams")
    cache_write("odds_sgo.json", {"events": out, "quota": {}})
    return out, {}


# ----------------------------------------------------------------- model
def nb_pmf(k, mu, alpha):
    """Negative binomial with mean mu and variance mu + alpha*mu^2 (Poisson if alpha ~ 0)."""
    if mu <= 0:
        return 1.0 if k == 0 else 0.0
    if alpha < 1e-6:
        return math.exp(k * math.log(mu) - mu - math.lgamma(k + 1))
    r = 1 / alpha
    p = r / (r + mu)
    return math.exp(math.lgamma(k + r) - math.lgamma(k + 1) - math.lgamma(r)
                    + r * math.log(p) + k * math.log(1 - p))


def line_probs(mu, alpha, line):
    """P(over), P(under), P(push) for a prop line."""
    under = sum(nb_pmf(k, mu, alpha) for k in range(0, math.ceil(line)))   # X < line
    push = nb_pmf(int(line), mu, alpha) if float(line).is_integer() else 0.0
    return max(0.0, 1 - under - push), under, push


class Model:
    def __init__(self, rows, current_season):
        for r in rows:
            r["PRA"] = r["PTS"] + r["REB"] + r["AST"]
        self.stats = ["PTS", "REB", "AST", "FG3M", "PRA"]
        self.by_player = defaultdict(list)
        for r in rows:
            self.by_player[norm_name(r["name"])].append(r)
        for g in self.by_player.values():
            g.sort(key=lambda r: r["date"], reverse=True)          # newest first
        tot_min = sum(r["MIN"] for r in rows) or 1
        self.lg_rate = {s: sum(r[s] for r in rows) / tot_min for s in self.stats}
        self._opp_factors([r for r in rows if r["season"] == current_season])
        self.current = current_season

    def _opp_factors(self, cur):
        """How much of each stat a team allows per game, relative to league average."""
        team_game = defaultdict(lambda: defaultdict(float))        # (gid, team) -> stat totals
        names = {}
        for r in cur:
            names[r["team"]] = norm_team(r["team_name"])
            for s in self.stats:
                team_game[(r["gid"], r["team"])][s] += r[s]
        allowed = defaultdict(lambda: defaultdict(list))           # defender -> stat -> [totals]
        by_gid = defaultdict(list)
        for (gid, team) in team_game:
            by_gid[gid].append(team)
        for gid, teams in by_gid.items():
            if len(teams) != 2:
                continue
            a, b = teams
            for s in self.stats:
                allowed[a][s].append(team_game[(gid, b)][s])
                allowed[b][s].append(team_game[(gid, a)][s])
        self.opp = {}
        for s in self.stats:
            allv = [v for t in allowed for v in allowed[t][s]]
            lg = sum(allv) / len(allv) if allv else 0
            for t in allowed:
                v = allowed[t][s]
                f = ((sum(v) + lg * OPP_PRIOR_GAMES) / (len(v) + OPP_PRIOR_GAMES) / lg) if lg else 1.0
                self.opp[(names[t], s)] = f

    def project(self, player, stat, opp_team=None):
        games = self.by_player.get(norm_name(player))
        if not games:
            return None
        w_rate, w_min = [], []
        for i, g in enumerate(games):
            disc = 1.0 if g["season"] == self.current else PRIOR_SEASON_W
            w_rate.append(disc * 0.5 ** (i / RATE_HALF_LIFE))
            w_min.append(disc * 0.5 ** (i / MIN_HALF_LIFE))
        proj_min = sum(w * g["MIN"] for w, g in zip(w_min, games)) / sum(w_min)
        wm = sum(w * g["MIN"] for w, g in zip(w_rate, games))
        ws = sum(w * g[stat] for w, g in zip(w_rate, games))
        rate = (ws + RATE_PRIOR_MIN * self.lg_rate[stat]) / (wm + RATE_PRIOR_MIN)
        team = norm_team(games[0]["team_name"])
        opp_f = self.opp.get((norm_team(opp_team), stat), 1.0) if opp_team else 1.0
        mu = proj_min * rate * opp_f
        # dispersion: player's own game-to-game variance, shrunk to a per-stat default
        sw = sum(w_rate)
        m = ws / sw
        var = sum(w * (g[stat] - m) ** 2 for w, g in zip(w_rate, games)) / sw
        n_eff = sw ** 2 / sum(w * w for w in w_rate)
        a_p = max(0.0, (var - m) / (m * m)) if m > 0 else ALPHA_DEFAULT[stat]
        alpha = (n_eff * a_p + ALPHA_PRIOR_GAMES * ALPHA_DEFAULT[stat]) / (n_eff + ALPHA_PRIOR_GAMES)
        last5 = [g[stat] for g in games[:5]]
        return {"mu": mu, "alpha": alpha, "min": proj_min, "opp_f": opp_f, "team": team,
                "games": len(games), "cur_games": sum(g["season"] == self.current for g in games),
                "last5": last5, "season_avg": m}


# ----------------------------------------------------------------- pricing
def build_rows(model, events):
    rows, unmatched = [], set()
    for ev in events:
        home, away = ev.get("home_team", ""), ev.get("away_team", "")
        groups = defaultdict(lambda: {"over": {}, "under": {}})    # (player, market, line)
        for bk in ev.get("bookmakers", []):
            for mk in bk.get("markets", []):
                if mk["key"] not in MARKETS:
                    continue
                for o in mk.get("outcomes", []):
                    side = (o.get("name") or "").lower()
                    if side in ("over", "under") and o.get("point") is not None and o.get("description"):
                        g = groups[(o["description"], mk["key"], float(o["point"]))]
                        g[side][bk.get("title") or bk["key"]] = o["price"]
        for (player, mkey, line), g in groups.items():
            label, stat = MARKETS[mkey]
            base = model.project(player, stat)
            if base is None:
                unmatched.add(player)
                continue
            teams = {norm_team(home): away, norm_team(away): home}
            opp = teams.get(base["team"])
            pr = model.project(player, stat, opp) if opp else base
            p_over, p_under, p_push = line_probs(pr["mu"], pr["alpha"], line)
            fair = []                                              # no-vig P(over) per book
            for b in set(g["over"]) & set(g["under"]):
                io, iu = 1 / dec_odds(g["over"][b]), 1 / dec_odds(g["under"][b])
                fair.append(io / (io + iu))
            best = {}
            for side in ("over", "under"):
                if g[side]:
                    b = max(g[side], key=lambda k: dec_odds(g[side][k]))
                    best[side] = {"book": b, "price": g[side][b], "dec": round(dec_odds(g[side][b]), 4)}
            rows.append({
                "player": player, "game": f"{away} @ {home}", "opp": opp or "?",
                "tip": ev.get("commence_time"), "market": label, "line": line,
                "proj": round(pr["mu"], 2), "min": round(pr["min"], 1),
                "opp_f": round(pr["opp_f"], 3), "p_over": round(p_over, 4),
                "p_under": round(p_under, 4), "p_push": round(p_push, 4),
                "mkt_over": round(sum(fair) / len(fair), 4) if fair else None,
                "books": len(set(g["over"]) | set(g["under"])), "best": best,
                "last5": pr["last5"], "avg": round(pr["season_avg"], 1),
                "cur_games": pr["cur_games"], "games": pr["games"]})
    return rows, sorted(unmatched)


# ----------------------------------------------------------------- demo data
def demo_data():
    rnd = random.Random(7)
    teams = [("BOS", "Boston Celtics"), ("LAL", "Los Angeles Lakers"),
             ("DEN", "Denver Nuggets"), ("NYK", "New York Knicks")]
    cur = season_str(datetime.now())
    y = int(cur[:4])
    prev = f"{y - 1}-{y % 100:02d}"
    players, rows = [], []
    for ab, tn in teams:
        for j in range(9):
            mins = max(12, 36 - 3 * j + rnd.uniform(-2, 2))
            players.append({"name": f"{tn.split()[-1][:-1]} {'Adams Brooks Carter Dixon Ellis Foster Grant Hayes Irving'.split()[j]}", "team": ab, "tn": tn, "min": mins,
                            "r": {"PTS": rnd.uniform(.35, .8), "REB": rnd.uniform(.1, .35),
                                  "AST": rnd.uniform(.06, .28), "FG3M": rnd.uniform(.02, .11)}})

    def pois(lam):
        L, k, p = math.exp(-lam), 0, 1.0
        while True:
            p *= rnd.random()
            if p <= L:
                return k
            k += 1

    gid = 0
    for season, n, start in ((prev, 60, datetime(y - 1, 10, 25)), (cur, 9, datetime(y, 10, 22))):
        for g in range(n):
            for a, b in ((0, 1), (2, 3)) if g % 2 == 0 else ((0, 2), (1, 3)):
                gid += 1
                d = (start + timedelta(days=2 * g)).strftime("%Y-%m-%d")
                for ti, oi in ((a, b), (b, a)):
                    for p in [p for p in players if p["team"] == teams[ti][0]]:
                        m = max(4, rnd.gauss(p["min"], 4))
                        hot = rnd.lognormvariate(0, .22)
                        rows.append({"season": season, "pid": 0, "name": p["name"], "team": p["team"],
                                     "team_name": p["tn"], "gid": gid, "date": d,
                                     "matchup": f"{teams[ti][0]} vs. {teams[oi][0]}", "MIN": round(m),
                                     **{s: pois(m * r * hot) for s, r in p["r"].items()}})
    tip = (datetime.now(timezone.utc) + timedelta(hours=5)).strftime("%Y-%m-%dT%H:%M:%SZ")
    events = []
    for h, a in ((0, 1), (2, 3)):
        books = []
        for bname in ("DraftKings", "FanDuel", "BetMGM"):
            mks = []
            for mkey, (_, stat) in MARKETS.items():
                outs = []
                for p in [p for p in players if p["team"] in (teams[h][0], teams[a][0])][:14]:
                    mean = p["min"] * (sum(p["r"][s] for s in ("PTS", "REB", "AST")) if stat == "PRA" else p["r"][stat])
                    line = max(0.5, round(mean * rnd.uniform(.93, 1.07)) - 0.5)
                    lean = rnd.choice([-12, -6, 0, 6, 12])
                    outs += [{"name": "Over", "description": p["name"], "price": -112 - lean, "point": line},
                             {"name": "Under", "description": p["name"], "price": -112 + lean, "point": line}]
                mks.append({"key": mkey, "outcomes": outs})
            books.append({"key": bname.lower(), "title": bname, "markets": mks})
        events.append({"id": f"demo{h}", "commence_time": tip, "home_team": teams[h][1],
                       "away_team": teams[a][1], "bookmakers": books})
    return rows, events


# ----------------------------------------------------------------- server
STATE = {"key": None, "demo": False, "provider": "sgo"}
LOCK = threading.Lock()


def build_payload(force=False):
    now = datetime.now()
    cur = season_str(now)
    y = int(cur[:4])
    notes = []
    if STATE["demo"]:
        logs, events = demo_data()
        quota = {}
        notes.append("Demo mode: players, stats and odds are made up.")
    else:
        if not STATE["key"]:
            raise RuntimeError("No API key. Set ODDS_API_KEY or pass --key (or run with --demo).")
        logs = list(fetch_gamelog(cur))
        try:
            logs += fetch_gamelog(f"{y - 1}-{y % 100:02d}")
        except Exception as e:
            notes.append(f"Last season's logs unavailable ({e}); projections use this season only.")
        fetch = fetch_odds_sgo if STATE["provider"] == "sgo" else fetch_odds
        events, quota = fetch(STATE["key"], force)
        if not events:
            notes.append(f"No NBA games with odds in the next {LOOKAHEAD_HOURS} hours.")
    model = Model(logs, cur)
    rows, unmatched = build_rows(model, events)
    if unmatched:
        notes.append("No stats match for: " + ", ".join(unmatched[:12]) + ("..." if len(unmatched) > 12 else ""))
    return {"rows": rows, "quota": quota, "notes": notes, "games": len(events),
            "updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), "markets": [v[0] for v in MARKETS.values()]}


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _send(self, code, body, ctype):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        u = urllib.parse.urlsplit(self.path)
        if u.path == "/":
            return self._send(200, PAGE.encode(), "text/html; charset=utf-8")
        if u.path == "/api/props":
            force = "refresh=1" in u.query
            try:
                with LOCK:
                    payload = build_payload(force)
                return self._send(200, json.dumps(payload).encode(), "application/json")
            except Exception as e:
                msg = str(e).replace(STATE["key"] or "\0", "***")
                return self._send(500, json.dumps({"error": msg}).encode(), "application/json")
        self._send(404, b"not found", "text/plain")


PAGE = r"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>NBA Props Model</title>
<style>
:root{--bg:#0f1115;--card:#181b22;--line:#272b35;--tx:#e8eaf0;--mut:#8b91a1;--pos:#3ecf8e;--neg:#f0616d;--acc:#6ea8fe}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--tx);font:14px/1.4 system-ui,-apple-system,Segoe UI,sans-serif}
header{padding:14px 16px;border-bottom:1px solid var(--line);display:flex;flex-wrap:wrap;gap:10px;align-items:center;justify-content:space-between}
h1{font-size:17px;margin:0}.mut{color:var(--mut)}.small{font-size:12px}
.bar{display:flex;flex-wrap:wrap;gap:10px;padding:12px 16px;align-items:end;border-bottom:1px solid var(--line)}
label{display:flex;flex-direction:column;gap:4px;font-size:11px;color:var(--mut);text-transform:uppercase;letter-spacing:.04em}
select,input,button{background:var(--card);color:var(--tx);border:1px solid var(--line);border-radius:8px;padding:8px 10px;font:inherit}
button{cursor:pointer}button:hover{border-color:var(--acc)}input[type=range]{padding:0;width:150px}
#notes{padding:8px 16px;color:#e7c46a;font-size:12px}#err{padding:16px;color:var(--neg)}
#list{padding:12px 16px;display:grid;gap:10px;grid-template-columns:repeat(auto-fill,minmax(310px,1fr))}
.c{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:12px}
.top{display:flex;justify-content:space-between;gap:8px;align-items:baseline}
.pl{font-weight:600;font-size:15px}.pick{font-weight:700}.ev{font-weight:700;font-variant-numeric:tabular-nums}
.pos{color:var(--pos)}.neg{color:var(--neg)}
.grid{display:grid;grid-template-columns:repeat(4,1fr);gap:6px;margin-top:10px}
.k{font-size:10px;color:var(--mut);text-transform:uppercase;letter-spacing:.04em}.v{font-variant-numeric:tabular-nums}
.foot{margin-top:8px;font-size:12px;color:var(--mut)}
</style></head><body>
<header><div><h1>NBA Props Model</h1><div class="mut small" id="meta">Loading...</div></div>
<button id="refresh">Refresh odds</button></header>
<div class="bar">
<label>Market<select id="mk"><option value="">All</option></select></label>
<label>Min EV %<input id="minev" type="number" value="0" step="0.5" style="width:80px"></label>
<label>Player<input id="q" placeholder="Search" style="width:130px"></label>
<label><span>Trust in market: <b id="wv">50</b>%</span><input id="w" type="range" min="0" max="100" value="50"></label>
</div>
<div id="notes"></div><div id="err"></div><div id="list"></div>
<script>
const STATIC=/*DATA*/null;let DATA=null;const $=id=>document.getElementById(id);
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const pct=x=>(100*x).toFixed(1)+'%';const am=p=>p>0?'+'+p:''+p;
function evaluate(r,w){
  // blend model with the no-vig market, then price each side at the best available odds
  const live=1-r.p_push, m=r.mkt_over;
  const po=m==null?r.p_over:(1-w)*r.p_over+w*m*live;
  const pu=m==null?r.p_under:(1-w)*r.p_under+w*(1-m)*live;
  let best=null;
  for(const [side,p] of [['over',po],['under',pu]]){
    const b=r.best[side];if(!b)continue;
    const ev=p*(b.dec-1)-(1-p-r.p_push);
    if(!best||ev>best.ev)best={side,p,ev,book:b.book,price:b.price,kelly:Math.max(0,ev/(b.dec-1))};
  }
  return best;
}
function render(){
  if(!DATA)return;const w=$('w').value/100;$('wv').textContent=$('w').value;
  const mk=$('mk').value,minev=parseFloat($('minev').value)||0,q=$('q').value.toLowerCase();
  const rows=DATA.rows.map(r=>({r,e:evaluate(r,w)})).filter(x=>x.e&&(!mk||x.r.market===mk)
    &&100*x.e.ev>=minev&&x.r.player.toLowerCase().includes(q)).sort((a,b)=>b.e.ev-a.e.ev);
  $('list').innerHTML=rows.slice(0,300).map(({r,e})=>`<div class="c">
   <div class="top"><span class="pl">${esc(r.player)}</span><span class="ev ${e.ev>=0?'pos':'neg'}">${e.ev>=0?'+':''}${(100*e.ev).toFixed(1)}% EV</span></div>
   <div class="top"><span class="pick">${e.side==='over'?'Over':'Under'} ${r.line} ${esc(r.market)}</span><span>${am(e.price)} <span class="mut">${esc(e.book)}</span></span></div>
   <div class="grid">
    <div><div class="k">Proj</div><div class="v">${r.proj}</div></div>
    <div><div class="k">Model</div><div class="v">${pct(e.side==='over'?r.p_over:r.p_under)}</div></div>
    <div><div class="k">Market</div><div class="v">${r.mkt_over==null?'n/a':pct(e.side==='over'?r.mkt_over:1-r.mkt_over)}</div></div>
    <div><div class="k">1/4 Kelly</div><div class="v">${(25*e.kelly).toFixed(1)}%</div></div>
   </div>
   <div class="foot">vs ${esc(r.opp)} (x${r.opp_f}) · ${r.min} min · avg ${r.avg} · last 5: ${r.last5.join(', ')} · ${r.cur_games} gms this season · ${r.books} books</div>
  </div>`).join('')||'<div class="mut">Nothing matches these filters.</div>';
}
async function load(force){
  $('err').textContent='';$('meta').textContent='Loading...';
  try{
    let d=STATIC;
    if(!d){const res=await fetch('/api/props'+(force?'?refresh=1':''));d=await res.json();}
    if(d.error)throw new Error(d.error);DATA=d;
    if($('mk').options.length===1)d.markets.forEach(m=>$('mk').add(new Option(m,m)));
    const qt=d.quota&&d.quota.remaining?` · ${d.quota.remaining} API credits left`:'';
    $('meta').textContent=`${d.games} games · ${d.rows.length} lines · updated ${new Date(d.updated).toLocaleString([], {month:'short',day:'numeric',hour:'numeric',minute:'2-digit'})}${qt}`;
    $('notes').textContent=d.notes.join('  ');render();
  }catch(e){$('meta').textContent='';$('err').textContent=e.message;}
}
['mk','minev','q','w'].forEach(id=>$(id).addEventListener('input',render));
if(STATIC)$('refresh').style.display='none';
$('refresh').addEventListener('click',()=>load(true));load(false);
</script></body></html>"""


def main():
    ap = argparse.ArgumentParser(description="NBA player prop model + dashboard")
    ap.add_argument("--key", default=os.environ.get("ODDS_API_KEY"))
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=8000)
    ap.add_argument("--demo", action="store_true", help="synthetic data, no network")
    ap.add_argument("--provider", default=os.environ.get("ODDS_PROVIDER", "sgo"), choices=["sgo", "theoddsapi"],
                    help="odds source: SportsGameOdds (default) or The Odds API")
    ap.add_argument("--build", metavar="DIR", help="write a static index.html to DIR and exit")
    a = ap.parse_args()
    a.key = (a.key or "").strip() or None
    STATE.update(key=a.key, demo=a.demo, provider=a.provider)
    if a.build:
        try:
            payload = build_payload(force=True)
        except Exception as e:
            raise SystemExit("Build failed: " + str(e).replace(a.key or "\0", "***"))
        os.makedirs(a.build, exist_ok=True)
        blob = json.dumps(payload).replace("</", "<\\/")
        with open(os.path.join(a.build, "index.html"), "w") as f:
            f.write(PAGE.replace("/*DATA*/null", blob))
        print(f"Wrote {a.build}/index.html: {payload['games']} games, {len(payload['rows'])} lines")
        print("DEBUG", json.dumps(DEBUG, default=str)[:3000])
        print("NOTES", payload["notes"])
        return
    print(f"NBA props dashboard: http://{'localhost' if a.host == '127.0.0.1' else a.host}:{a.port}"
          + ("  (demo data)" if a.demo else ""))
    ThreadingHTTPServer((a.host, a.port), Handler).serve_forever()


if __name__ == "__main__":
    main()
