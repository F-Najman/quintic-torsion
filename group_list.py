#!/usr/bin/env python3
"""group_list.py -- re-derives the list of 45 groups of Lemma 3.1 of the paper.

A group G = Z/m x Z/n (m | n) belongs to the set  G  of the lemma iff
  (1) G is not in Phi^infty(5) but every proper subgroup of G is,
  (2) phi(m) | 5,
  (3) every prime divisor of mn is at most 19  (= max S(5), Derickx-Kamienny-Stein-Stoll).
"""
from sympy import divisors, primefactors

Phi_inf = {(1, n) for n in range(1, 26) if n != 23} | {(2, 2*n) for n in range(1, 9)}
S5 = {2, 3, 5, 7, 11, 13, 17, 19}

def proper_subgroups(m, n):
    return {(a, b) for a in divisors(m) for b in divisors(n)
            if b % a == 0 and (a, b) != (m, n)}

cands = []
for m in (1, 2):
    for n in range(1, 400):
        if n % m:
            continue
        G = (m, n)
        if G in Phi_inf:
            continue
        if any(p not in S5 for p in primefactors(m * n)):
            continue
        if all(H in Phi_inf for H in proper_subgroups(m, n)):
            cands.append(G)

cyc = [n for (m, n) in cands if m == 1]
non = [(m, n) for (m, n) in cands if m == 2]
print("cyclic (%d): %s" % (len(cyc), cyc))
print("m = 2  (%d): %s" % (len(non), non))
print("total: %d" % len(cands))
assert len(cands) == 45
print("OK")
print("GROUPLIST_DONE")
