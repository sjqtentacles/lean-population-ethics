"""Finite-domain SAT search over population axiologies.

A population is a multiset of integer welfare levels (a descending tuple). The
domain is every population of size at most N over a fixed list of levels. There is
one Boolean variable per ordered pair of populations: R(A, B), "A is at least as
good as B". Every adequacy condition is a universal statement, so it becomes a set
of ground instances, each a small set of clauses over these variables.

Soundness. Each ground instance is an instance of the general condition, so if a set
of conditions is unsatisfiable here, no axiology on all populations satisfies them.
A satisfiable result says only that the instances inside this domain are consistent.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field

from pysat.solvers import Cadical153

Pop = tuple  # descending tuple of ints


def mk(xs) -> Pop:
    return tuple(sorted(xs, reverse=True))


@dataclass(frozen=True)
class Params:
    levels: tuple = (-1, 1, 2, 3, 4)
    max_size: int = 4
    # Avoid-Repugnant-Conclusion instance: no population at level `low` is better
    # than `rc_n` people at level `high`.
    rc_n: int = 1
    high: int = 4
    low: int = 2
    # Non-Elitism: one person at level b+1 and `ne_m` people at a lower level c are
    # no better than everyone at level b.
    ne_m: int = 1
    # Non-Extreme Priority: `nep_n` people at `high` plus one at `slightly_neg` are
    # at least as good as `nep_n + 1` people at `barely`.
    nep_n: int = 1
    slightly_neg: int = -1
    barely: int = 1


CONDITIONS = [
    "Trans",
    "Complete",
    "EgalDom",
    "MereAddition",
    "NAE",
    "PigouDalton",
    "AvoidRC",
    "AvoidSadistic",
    "Dominance",
    "NonElitism",
    "NonExtremePriority",
]


@dataclass
class Instance:
    cond: str
    args: tuple  # condition-specific, see `instances`
    clauses: list  # list of clauses; a literal is (sign, A, B) with sign in {+1, -1}


def better(a: Pop, b: Pop):
    """Clauses asserting that `a` is strictly better than `b`."""
    return [[(1, a, b)], [(-1, b, a)]]


def not_better(a: Pop, b: Pop):
    """The clause asserting that `a` is not strictly better than `b`."""
    return [[(-1, a, b), (1, b, a)]]


class Domain:
    def __init__(self, p: Params):
        self.p = p
        self.pops = [
            mk(c)
            for n in range(p.max_size + 1)
            for c in itertools.combinations_with_replacement(p.levels, n)
        ]
        self.index = {a: i for i, a in enumerate(self.pops)}

    def has(self, a: Pop) -> bool:
        return a in self.index

    def positive(self):
        return [a for a in self.pops if a and all(w > 0 for w in a)]

    def negative(self):
        return [a for a in self.pops if a and all(w < 0 for w in a)]

    def instances(self, cond: str):
        """Yield every ground instance of `cond` that lies inside the domain."""
        p, pops = self.p, self.pops
        if cond == "Trans":
            for a in pops:
                for b in pops:
                    if a == b:
                        continue
                    for c in pops:
                        if b == c:
                            continue
                        yield Instance(cond, (a, b, c), [[(-1, a, b), (-1, b, c), (1, a, c)]])
        elif cond == "Complete":
            for i, a in enumerate(pops):
                for b in pops[i:]:
                    yield Instance(cond, (a, b), [[(1, a, b), (1, b, a)]])
        elif cond == "EgalDom":
            # A perfectly equal population in which everyone is better off than
            # everyone in a same-sized population `b` is better than `b`.
            for b in pops:
                if not b:
                    continue
                for w in p.levels:
                    if w > max(b):
                        yield Instance(cond, (b, w), better((w,) * len(b), b))
        elif cond == "MereAddition":
            for a in pops:
                for b in self.positive():
                    c = mk(a + b)
                    if self.has(c):
                        yield Instance(cond, (a, b, c), [[(1, c, a)]])
        elif cond == "NAE":
            for a in pops:
                if len(set(a)) < 2:
                    continue
                for w in p.levels:
                    if sum(a) < len(a) * w:
                        yield Instance(cond, (a, w), better((w,) * len(a), a))
        elif cond == "PigouDalton":
            # A transfer of `d` from someone at `hi` to someone at `lo` that does not
            # reverse their order is not a worsening.
            for rest in pops:
                for hi in p.levels:
                    for lo in p.levels:
                        for d in range(1, hi - lo):
                            if lo + d > hi - d:
                                continue
                            if hi - d not in p.levels or lo + d not in p.levels:
                                continue
                            before = mk(rest + (hi, lo))
                            after = mk(rest + (hi - d, lo + d))
                            if self.has(before) and self.has(after):
                                yield Instance(
                                    cond, (rest, hi, lo, d, before, after), [[(1, after, before)]]
                                )
        elif cond == "AvoidRC":
            top = (p.high,) * p.rc_n
            for m in range(1, p.max_size + 1):
                yield Instance(cond, (m,), not_better((p.low,) * m, top))
        elif cond == "AvoidSadistic":
            # Adding people with negative welfare is never better than adding people
            # with positive welfare.
            for a in pops:
                for pos in self.positive():
                    ap = mk(a + pos)
                    if not self.has(ap):
                        continue
                    for neg in self.negative():
                        an = mk(a + neg)
                        if self.has(an):
                            yield Instance(cond, (a, pos, neg, ap, an), not_better(an, ap))
        elif cond == "Dominance":
            # Same size, everyone (after matching by rank) at least as well off and
            # someone better off.
            for a in pops:
                for b in pops:
                    if len(a) == len(b) and a != b and all(x >= y for x, y in zip(a, b)):
                        yield Instance(cond, (a, b), better(a, b))
        elif cond == "NonElitism":
            for x in pops:
                for b in p.levels:
                    if b + 1 not in p.levels:
                        continue
                    for c in p.levels:
                        if c >= b or any(w < c or w > b + 1 for w in x):
                            continue
                        equal = mk(x + (b,) * (p.ne_m + 1))
                        elite = mk(x + (b + 1,) + (c,) * p.ne_m)
                        if self.has(equal) and self.has(elite):
                            yield Instance(cond, (x, b, c, equal, elite), [[(1, equal, elite)]])
        elif cond == "NonExtremePriority":
            for x in pops:
                good = mk(x + (p.high,) * p.nep_n + (p.slightly_neg,))
                flat = mk(x + (p.barely,) * (p.nep_n + 1))
                if self.has(good) and self.has(flat):
                    yield Instance(cond, (x, good, flat), [[(1, good, flat)]])
        else:
            raise ValueError(cond)


# --- reference theories, used to sanity-check the encoding -----------------------


def total(a):
    return sum(a)


def average(a):
    return sum(a) / len(a) if a else 0.0


THEORIES = {
    "totalism": lambda a, b: total(a) >= total(b),
    "averagism": lambda a, b: average(a) >= average(b),
    "critical-level (c=2)": lambda a, b: sum(w - 2 for w in a) >= sum(w - 2 for w in b),
    "maximin (empty=0)": lambda a, b: (min(a) if a else 0) >= (min(b) if b else 0),
}


def satisfies(dom: Domain, theory, cond: str) -> bool:
    for inst in dom.instances(cond):
        for clause in inst.clauses:
            if not any((theory(a, b) if s > 0 else not theory(a, b)) for s, a, b in clause):
                return False
    return True


# --- SAT encoding ---------------------------------------------------------------


class Encoding:
    """One selector variable per condition; `solve(S)` asks whether S is satisfiable."""

    def __init__(self, dom: Domain, conds=CONDITIONS):
        self.dom = dom
        self.conds = list(conds)
        n = len(dom.pops)
        self.n = n
        self.sel = {c: n * n + 1 + i for i, c in enumerate(self.conds)}
        self.solver = Cadical153()
        self.counts = {}
        for c in self.conds:
            s = self.sel[c]
            k = 0
            for inst in dom.instances(c):
                k += 1
                for clause in inst.clauses:
                    self.solver.add_clause([-s] + [self.lit(l) for l in clause])
            self.counts[c] = k

    def var(self, a: Pop, b: Pop) -> int:
        return self.dom.index[a] * self.n + self.dom.index[b] + 1

    def lit(self, l) -> int:
        s, a, b = l
        return s * self.var(a, b)

    def solve(self, subset) -> bool:
        return self.solver.solve(assumptions=[self.sel[c] for c in subset])

    def model_relation(self):
        m = self.solver.get_model()
        pops, n = self.dom.pops, self.n
        return {(a, b) for i, a in enumerate(pops) for j, b in enumerate(pops) if m[i * n + j] > 0}


def conflict_map(enc: Encoding):
    """All minimal unsatisfiable and maximal satisfiable subsets of the conditions.

    MARCO-style enumeration: a second solver tracks which subsets are still
    unexplored; each seed is grown to a maximal consistent set or shrunk to a
    minimal conflicting one, and its supersets or subsets are then blocked.
    """
    conds = enc.conds
    var = {c: i + 1 for i, c in enumerate(conds)}
    mus, mss = [], []
    with Cadical153() as unexplored:
        while unexplored.solve():
            model = set(unexplored.get_model() or [])
            seed = {c for c in conds if -var[c] not in model}
            if enc.solve(seed):
                for c in conds:
                    if c not in seed and enc.solve(seed | {c}):
                        seed.add(c)
                mss.append(seed)
                block = [var[c] for c in conds if c not in seed]
                if not block:
                    break
                unexplored.add_clause(block)
            else:
                core = set(enc.solver.get_core() or [])
                seed = {c for c in seed if enc.sel[c] in core}
                for c in sorted(seed, key=conds.index):
                    if not enc.solve(seed - {c}):
                        seed.discard(c)
                mus.append(seed)
                unexplored.add_clause([-var[c] for c in seed])
    return mus, mss


# --- ground cores ---------------------------------------------------------------


class FineEncoding:
    """One selector per ground instance of every non-transitivity condition, with
    transitivity as a single switchable block. Used to find which instances matter."""

    def __init__(self, dom, conds):
        self.dom = dom
        n = len(dom.pops)
        self.n = n
        self.solver = Cadical153()
        self.trans_sel = n * n + 1
        nxt = n * n + 2
        self.by_cond = {}
        self.inst = {}
        for c in conds:
            if c == "Trans":
                for inst in dom.instances(c):
                    for cl in inst.clauses:
                        self.solver.add_clause([-self.trans_sel] + [self.lit(l) for l in cl])
                continue
            sels = []
            for inst in dom.instances(c):
                for cl in inst.clauses:
                    self.solver.add_clause([-nxt] + [self.lit(l) for l in cl])
                self.inst[nxt] = inst
                sels.append(nxt)
                nxt += 1
            self.by_cond[c] = sels

    def lit(self, l):
        s, a, b = l
        return s * (self.dom.index[a] * self.n + self.dom.index[b] + 1)

    def facts(self, conds):
        """A minimal set of non-transitivity instances of `conds` that conflicts,
        given all of transitivity (when `conds` includes it)."""
        fixed = [self.trans_sel] if "Trans" in conds else []
        sels = [s for c in conds if c != "Trans" for s in self.by_cond[c]]
        if self.solver.solve(assumptions=fixed + sels):
            return None
        while True:
            core = set(self.solver.get_core() or [])
            smaller = [s for s in sels if s in core]
            if len(smaller) == len(sels):
                break
            sels = smaller
            assert not self.solver.solve(assumptions=fixed + sels)
        i = 0
        while i < len(sels):
            trial = sels[:i] + sels[i + 1 :]
            if self.solver.solve(assumptions=fixed + trial):
                i += 1
            else:
                core = set(self.solver.get_core() or [])
                sels = [s for s in trial if s in core]
        return [self.inst[s] for s in sels]


def instance_pops(inst):
    return {p for cl in inst.clauses for _, a, b in cl for p in (a, b)}


def ground_core(dom, conds, fine: FineEncoding | None = None):
    """A minimal set of ground instances of `conds` that is already unsatisfiable.

    With a `FineEncoding`, first find the non-transitivity instances that matter,
    then take transitivity only over the populations they mention.
    """
    if fine is not None:
        facts = fine.facts(conds)
        if facts is None:
            return None
        nodes = sorted(set().union(*(instance_pops(i) for i in facts)), key=dom.index.get)
        pool = list(facts)
        if "Trans" in conds:
            pool += [
                Instance("Trans", ("trans", a, b, c), [[(-1, a, b), (-1, b, c), (1, a, c)]])
                for a in nodes for b in nodes if a != b for c in nodes if b != c
            ]
        core = _minimise(pool)
        if core is not None:
            return core
    return _minimise([inst for c in conds for inst in dom.instances(c)])


def _minimise(pool):
    def shrink(insts):
        idx = {}

        def var(a, b):
            return idx.setdefault((a, b), len(idx) + 1)

        for inst in insts:
            for cl in inst.clauses:
                for _, a, b in cl:
                    var(a, b)
        base = len(idx)
        with Cadical153() as solver:
            for i, inst in enumerate(insts):
                for cl in inst.clauses:
                    solver.add_clause([-(base + 1 + i)] + [s * var(a, b) for s, a, b in cl])
            assumptions = [base + 1 + i for i in range(len(insts))]
            if solver.solve(assumptions=assumptions):
                return None
            core = set(solver.get_core())
        return [inst for i, inst in enumerate(insts) if base + 1 + i in core]

    core = shrink(pool)
    if core is None:
        return None
    while True:
        smaller = shrink(core)
        if len(smaller) == len(core):
            break
        core = smaller
    # Deletion-based minimisation: drop any instance that is not needed.
    i = 0
    while i < len(core):
        trial = core[:i] + core[i + 1 :]
        reduced = shrink(trial)
        if reduced is None:
            i += 1
        else:
            # Instances before position i are each necessary, so they survive.
            core = reduced
    return core
