#!/usr/bin/env python3
"""Analytic ranks of the newform factors of J_1(N).

For each level N the weight-2 newforms of every level M | N and every character are collected,
each with multiplicity sigma_0(N/M), and the ones of positive analytic rank are listed.  The
consistency check is that the dimensions add up to the genus of X_1(N): if they do, no factor
has been missed, and the levels whose list of positive-rank forms is empty are exactly those
where Kato's theorem gives J_1(N)(Q) finite.

By default the script runs OFFLINE: it reads the archived newform records in
data/lmfdb_newforms_cache.json, recomputes everything from them, and checks the result against
the committed data/lmfdb_ranks.json and data/lmfdb_ranks_summary.txt.  It prints the summary
table and exits non-zero if anything disagrees, so the rank data used in the paper can be
verified without network access.

  python3 lmfdb_ranks.py              verify the committed data against the archived records
  python3 lmfdb_ranks.py --fetch      refetch from the LMFDB and rewrite all three data files

Run from the repository root.
"""
import json, os, sys, time, urllib.request, urllib.error
from math import gcd

# The levels of the paper: those of Table 3 and Table 5, and the levels of the quartic paper
# reused in Section 9.
LEVELS = [26, 27, 28, 30, 32, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 48, 49, 50, 51, 55, 57,
          63, 65, 75, 77, 85, 91, 95, 119, 121, 125, 133, 143, 169, 187, 209, 221, 247, 289,
          323, 361]

CACHE   = "data/lmfdb_newforms_cache.json"
RANKS   = "data/lmfdb_ranks.json"
SUMMARY = "data/lmfdb_ranks_summary.txt"

FIELDS = ("label,char_orbit_label,char_order,char_conductor,dim,relative_dim,"
          "analytic_rank,analytic_rank_proved,is_cm,nf_label")


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def phi(n):
    return sum(1 for k in range(1, n + 1) if gcd(k, n) == 1)


def sigma0(n):
    return len(divisors(n))


def genus_X1(N):
    """Genus of X_1(N), from the index of Gamma_1(N) and its number of cusps."""
    if N <= 4:
        return 0
    idx = N * N
    for p in set(f for f in range(2, N + 1)
                 if N % f == 0 and all(f % q for q in range(2, f))):
        idx = idx * (p * p - 1) // (p * p)
    idx //= 2                                   # index of Gamma_1(N) in PSL_2(Z), N >= 3
    cusps = sum(phi(d) * phi(N // d) for d in divisors(N)) // 2
    return 1 + idx // 12 - cusps // 2


def analyse(N, cache):
    """The newform decomposition of J_1(N) as read off from the cached records."""
    rows, dimJ, dim_pos, unproved = [], 0, 0, []
    for M in divisors(N):
        if str(M) not in cache:
            raise KeyError("level %d missing from %s; rerun with --fetch" % (M, CACHE))
        mult = sigma0(N // M)
        for f in cache[str(M)]:
            dimJ += f["dim"] * mult
            if f["analytic_rank"] is None or not f["analytic_rank_proved"]:
                unproved.append(f["label"])
            if f["analytic_rank"]:
                dim_pos += f["dim"] * mult
                rows.append([f["label"], f["char_order"], f["dim"], f["analytic_rank"], mult])
    g = genus_X1(N)
    return {"genus_formula": g, "dim_sum": dimJ, "check": "OK" if g == dimJ else "MISMATCH",
            "dim_positive_rank": dim_pos, "positive_rank_forms": rows, "unproved": unproved}


def summary_line(N, r):
    forms = ", ".join("%s(chi ord %d, dim %d, rk %d)" % (lab, ordc, dim, rk)
                      for lab, ordc, dim, rk, _ in r["positive_rank_forms"]) or "-"
    return "N=%4d genus=%5d check=%s  rk>0 dim=%3d  forms: %s" % (
        N, r["genus_formula"], r["check"], r["dim_positive_rank"], forms)


# ---------------------------------------------------------------- fetching (needs the network)

def get(url):
    for attempt in range(12):
        try:
            with urllib.request.urlopen(url, timeout=120) as r:
                return json.loads(r.read().decode())
        except (urllib.error.HTTPError, urllib.error.URLError, ValueError):
            time.sleep(15 * (attempt + 1))
    raise RuntimeError("LMFDB fetch failed: " + url)


def fetch_level(M):
    out, offset, LIMIT = [], 0, 100  # the LMFDB API returns at most 100 records per page
    while True:
        url = ("https://www.lmfdb.org/api/mf_newforms/?level=%d&weight=2&_format=json"
               "&_fields=%s&_limit=%d&_offset=%d") % (M, FIELDS, LIMIT, offset)
        data = get(url)["data"]
        out += data
        if len(data) < LIMIT:
            return out
        offset += len(data)
        time.sleep(2.0)


def fetch(levels):
    cache = {}
    for N in levels:
        for M in divisors(N):
            if str(M) not in cache:
                cache[str(M)] = fetch_level(M)
                time.sleep(2.0)
    return cache


# ------------------------------------------------------------------------------------- driver

def main(argv):
    refetch = "--fetch" in argv
    if refetch:
        cache = fetch(LEVELS)
    else:
        if not os.path.exists(CACHE):
            sys.exit("%s not found; run from the repository root, or use --fetch" % CACHE)
        cache = json.load(open(CACHE))

    res = {}
    for N in LEVELS:
        res[N] = analyse(N, cache)
        print(summary_line(N, res[N]))
        sys.stdout.flush()

    bad = [N for N in LEVELS if res[N]["check"] != "OK"]
    unproved = sorted(set(f for N in LEVELS for f in res[N]["unproved"]))
    print("GENUS CHECK: %s" % ("all %d levels OK" % len(LEVELS) if not bad else "FAILED at %s" % bad))
    print("ANALYTIC RANKS: %s" % ("all proved in the LMFDB" if not unproved
                                  else "not proved for %s" % unproved))
    ok = not bad and not unproved

    if refetch:
        if not ok:
            print("rank checks failed; archived data files were not changed")
            return 1
        json.dump({str(k): v for k, v in res.items()}, open(RANKS, "w"), indent=1)
        json.dump(cache, open(CACHE, "w"), indent=1)
        open(SUMMARY, "w").write("".join(summary_line(N, res[N]) + "\n" for N in LEVELS))
        print("rewrote %s, %s and %s" % (CACHE, RANKS, SUMMARY))
        return 0 if ok else 1

    # offline: the recomputed values must agree with what is committed
    old = json.load(open(RANKS))
    diffs = [N for N in LEVELS if json.loads(json.dumps(res[N])) != old.get(str(N))]
    if diffs:
        print("MISMATCH against %s at N = %s" % (RANKS, diffs)); ok = False
    else:
        print("AGREES with %s at all %d levels" % (RANKS, len(LEVELS)))
    want = "".join(summary_line(N, res[N]) + "\n" for N in LEVELS)
    if open(SUMMARY).read() != want:
        print("MISMATCH against %s" % SUMMARY); ok = False
    else:
        print("AGREES with %s" % SUMMARY)
    print("RANKS_DONE %s" % ("OK" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
