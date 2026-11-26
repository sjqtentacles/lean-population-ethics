"""Brute-force check of the `lex` axiology against the five conditions as worded in
Arrhenius (2011) section 1.3 (exact formulations), plus the informal variants where
they differ.  Populations are sorted tuples of integer welfare levels.  Written
independently of the Lean file: the conditions are coded from the paper's wording.
"""
from itertools import combinations_with_replacement as cwr
import sys, time

EXC = 4


def bad(X):
    return sum(-w for w in X if w < 0)


def exc(X):
    return sum(1 for w in X if w >= EXC)


def comp(X):
    return bad(X) <= exc(X)


def R(X, Y):
    """X is at least as good as Y (literal transcription of the model's prose)."""
    cx, cy = comp(X), comp(Y)
    return (cx and not cy) or ((cx == cy) and sum(Y) <= sum(X))


def better(X, Y):
    return R(X, Y) and not R(Y, X)


def U(*parts):
    out = []
    for p in parts:
        out.extend(p)
    return tuple(sorted(out))


def msets(levels, maxsize, minsize=0):
    for k in range(minsize, maxsize + 1):
        for c in cwr(levels, k):
            yield c


LO, HI = -5, 8
LEVELS = list(range(LO, HI + 1))
viol = {}
count = {}


def record(name, ok, witness):
    count[name] = count.get(name, 0) + 1
    if not ok:
        viol.setdefault(name, []).append(witness)


t0 = time.time()

# ---- quasi-order sanity (reflexive, complete, transitive) on small populations
small = list(msets(range(-3, 6), 3))
for X in small:
    record("reflexive", R(X, X), X)
for X in small:
    for Y in small:
        record("complete", R(X, Y) or R(Y, X), (X, Y))
key = {X: (comp(X), sum(X)) for X in small}
for X in small:
    for Y in small:
        # R coincides with a lexicographic key order, hence transitive
        record("R == key order", R(X, Y) == (key[X] >= key[Y]), (X, Y))

# ---- Egalitarian Dominance (exact): N(A)=N(B), all of B below Wx, A in Wx => A better than B
for B in msets(LEVELS, 5, 0):
    for x in range(LO, HI + 3):
        if all(w < x for w in B):
            A = (x,) * len(B)
            nm = "ED (N>=1)" if len(B) >= 1 else "ED (N=0, hyper-literal empty case)"
            record(nm, better(A, B), (A, B))

# ---- General Non-Extreme Priority (exact): for any z exist u>y, R(1,y), n>0 ...
# model's witnesses: u=4, y=3, n=1 (uniform in z, so the informal "n first" order holds too)
u, y, n = 4, 3, 1
assert u > y and y >= 3 and n > 0
for z in range(LO - 3, HI + 3):
    for x in range(u, HI + 4):
        A = (x,) * n
        for B in msets(range(1, y + 1), n, n):
            for E in msets(LEVELS, 4):
                record("GNEP", R(U(A, (z,), E), U(B, (z + 1,), E)), (z, x, B, E))

# ---- Non-Elitism (exact): for any x-1>y exists n>0: C(n+1 at x-1) u D >= A(1 at x) u B(n at y) u D, D in R(y,x)
n = 1
for x in range(LO, HI + 1):
    for yy in range(LO, x - 1):
        rng = range(yy, x + 1)
        maxsz = 5 if len(rng) <= 8 else 4
        for D in msets(rng, maxsz):
            record("NE", R(U((x - 1,) * (n + 1), D), U((x,), (yy,) * n, D)), (x, yy, D))

# ---- Weak Non-Sadism (exact): exists x<0, n: B in Wy (y>0, any size) u C >= A(n at x) u C, any C
xneg, n = -1, 1
for yy in range(1, HI + 3):
    for k in range(0, 8):
        for C in msets(LEVELS, 4):
            record("WNS", R(U((yy,) * k, C), U((xneg,) * n, C)), (yy, k, C))
# informal variant: B any population with positive welfare (mixed levels)
for B in msets(range(1, HI + 1), 4):
    for C in msets(LEVELS, 3):
        record("WNS informal (mixed positive B)", R(U(B, C), U((xneg,) * n, C)), (B, C))

# ---- Weak Quality Addition (exact): for any X exist x<0, R(u,v), R(1,y), u>y, n,m>0:
#      A in Wz, z>=u, N(A)=n ; B in R(1,y) any size ; C in Wx, N(C)=m  =>  A u X >= B u C u X
xneg, u, v, y = -1, 4, 6, 3
assert xneg < 0 and v >= u + 2 and y >= 3 and u > y
for X in msets(LEVELS, 4):
    n = bad(X) + 1
    m = exc(X) + 1
    assert n > 0 and m > 0
    Bs = list(msets(range(1, y + 1), 4)) + [(3,) * k for k in (10, 50, 200, 2000)]
    for z in list(range(u, HI + 2)) + [50]:
        AX = U((z,) * n, X)
        for B in Bs:
            record("WQA", R(AX, U(B, (xneg,) * m, X)), (X, z, B))

# ---- consistency probes with the paper's proof (not conditions of the theorem)
# Restricted Quality Addition must FAIL for the model if Lemma 1.4 is sound.  Probe X = ():
rqa_fail = all(
    any(not R((zz,) * nn, (3,) * p) for p in range(mm, mm + 4 * nn * zz + 5))
    for nn in range(1, 6) for mm in range(0, 6) for zz in range(4, 9)
)
# Lemma 1.3 step (12): A1 u A2 u X >= A1 u B2 u C u X with the WQA witnesses for X = ()
# n=1 (A2 size), m=1 (C size), and A1 of size n' (from Condition delta) at the same level.
step12_fail = [
    (n1, q) for n1 in range(1, 4) for q in range(0, 40)
    if not R(U((4,) * n1, (4,) * 1), U((4,) * n1, (3,) * q, (-1,) * 1))
]

print("elapsed %.1fs" % (time.time() - t0))
for k in sorted(count):
    v_ = viol.get(k, [])
    print("%-40s instances=%-9d violations=%d %s" % (k, count[k], len(v_), ("e.g. %r" % (v_[0],)) if v_ else ""))
print("RQA fails at X=() for all probed (n,m,z):", rqa_fail)
print("Lemma 1.3 step (12) counter-instances in model (n1, q), first 5:", step12_fail[:5])
