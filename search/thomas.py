"""Arrhenius's adequacy conditions, as reconstructed by Teruji Thomas
("Reconstructing Arrhenius's Impossibility Theorems", 2016).

Welfare levels are the integers from Z (abominable) to T, with 0 neutral, 1..3 "barely
worth living" and A and above "excellent". Each condition of the form "there is a
number such that ..." is encoded with an explicit witness (see `Witnesses`), so that
every condition is a universal statement and finite unsatisfiability is sound.

Each ground instance carries the Lean term that proves it from the general condition.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass

from popsat import Instance, better, mk, not_better


@dataclass(frozen=True)
class Scale:
    levels: tuple = (-1, 0, 1, 2, 3, 4)
    max_size: int = 4
    Z: int = -1
    A: int = 4
    T: int = 4


@dataclass(frozen=True)
class Witnesses:
    """Witness numbers, calibrated so that totalism satisfies every condition other
    than the avoidance ones. `LEAN` gives the same functions as Lean terms."""

    nep_b: int = 4  # needs nep_b * (A - 3) >= 4
    g: int = 1  # (General) Non-Elitism and General Non-Extreme Priority
    wns_d: int = 1
    # Instances at which a repugnant conclusion is avoided.
    rc_m: int = 1
    ra_n: int = 1
    vr_z: int = -1
    vr_m: int = 1
    vr_n: int = 1

    @staticmethod
    def q(w, m):  # Quantity
        return 2 * m

    @staticmethod
    def c(x, y, z, m):  # Inequality Aversion and its variants
        return m * (x - y)

    @staticmethod
    def st_b(z, m):  # Sufficient Tradeoffs
        return m * (3 - z)


LEAN_WITNESS = {
    "q": "(fun _ m => 2 * m)",
    "c": "(fun x y _ m => m * (x - y).toNat)",
    "st_b": "(fun z m => m * (3 - z).toNat)",
    "g2": "(fun _ _ => 1)",
    "g1": "(fun _ => 1)",
}


CONDITIONS = [
    "Trans", "Refl", "ED", "Quantity", "DA", "IA", "NS", "WNS", "NEP",
    "GNE", "NE", "GIAA", "IAA", "GNEP", "ST",
    "AvoidRC", "AvoidRA", "AvoidVRC", "AvoidVRA",
]  # fmt: skip

# stronger condition -> the weaker condition whose instances it includes
WEAKER = {"NS": "WNS", "GNE": "NE", "GIAA": "IAA", "AvoidRA": "AvoidRC", "AvoidVRA": "AvoidVRC"}


def num(x: int) -> str:
    return f"({x})" if x < 0 else str(x)


def lst(xs) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


class ThomasDomain:
    def __init__(self, s: Scale = Scale(), w: Witnesses = Witnesses()):
        self.s, self.w = s, w
        self.L = set(s.levels)
        self.pops = [
            mk(c)
            for n in range(s.max_size + 1)
            for c in itertools.combinations_with_replacement(s.levels, n)
        ]
        self.index = {a: i for i, a in enumerate(self.pops)}

    def has(self, a) -> bool:
        return a in self.index

    def _fact(self, cond, kind, call, ndec, x, y):
        """`kind` is 'rel' (x at least as good as y), 'better' or 'notbetter'."""
        x, y = mk(x), mk(y)
        if not (self.has(x) and self.has(y)):
            return None
        clauses = {"rel": [[(1, x, y)]], "better": better(x, y), "notbetter": not_better(x, y)}[kind]
        return Instance(cond, (kind, call, ndec, x, y), clauses)

    def instances(self, cond: str):
        for inst in self._instances(cond):
            if inst is not None:
                yield inst

    def _instances(self, cond: str):
        s, w, L, pops = self.s, self.w, self.L, self.pops
        sizes = range(1, s.max_size + 1)
        lv = sorted(L)
        f = self._fact
        if cond == "Trans":
            for a in pops:
                for b in pops:
                    if a == b:
                        continue
                    for c in pops:
                        if b != c:
                            yield Instance(cond, ("trans", a, b, c), [[(-1, a, b), (-1, b, c), (1, a, c)]])
        elif cond == "Refl":
            for a in pops:
                yield Instance(cond, ("refl", a), [[(1, a, a)]])
        elif cond == "ED":
            for x in lv:
                for y in lv:
                    if x < y:
                        for n in sizes:
                            yield f(cond, "better", f"{num(x)} {num(y)} {n}", 4, (y,) * n, (x,) * n)
        elif cond == "Quantity":
            for x in lv:
                if x > 1 and x - 1 in L:
                    for m in sizes:
                        yield f(cond, "rel", f"{num(x)} {m}", 3, (x - 1,) * w.q(x, m), (x,) * m)
        elif cond == "DA":
            for x in lv:
                for y in lv:
                    for z in lv:
                        if x > y and z > 0:
                            for m in sizes:
                                for n in sizes:
                                    yield f(cond, "rel", f"{num(x)} {num(y)} {num(z)} {m} {n}", 7,
                                            (x,) * m + (z,) * n, (y,) * m)  # fmt: skip
        elif cond == "IA":
            for x, y, z, m in self._xyzm():
                yield f(cond, "rel", f"{num(x)} {num(y)} {num(z)} {m}", 6,
                        (y,) * (m + w.c(x, y, z, m)), (x,) * m + (z,) * w.c(x, y, z, m))  # fmt: skip
        elif cond in ("NS", "WNS"):
            for p in pops:
                for x in lv:
                    if x <= 0:
                        continue
                    for m in sizes:
                        if cond == "WNS":
                            yield f(cond, "rel", f"{lst(p)} {num(x)} {m}", 4,
                                    p + (x,) * m, p + (s.Z,) * w.wns_d)  # fmt: skip
                            continue
                        for z in lv:
                            if z < 0:
                                for n in sizes:
                                    yield f(cond, "rel", f"{lst(p)} {num(x)} {num(z)} {m} {n}", 7,
                                            p + (x,) * m, p + (z,) * n)  # fmt: skip
        elif cond == "NEP":
            if {-1, 3, s.A} <= L:
                for p in pops:
                    yield f(cond, "rel", f"{lst(p)}", 1,
                            p + (-1,) + (s.A,) * w.nep_b, p + (3,) + (3,) * w.nep_b)  # fmt: skip
        elif cond in ("GNE", "NE"):
            for p in pops:
                for x in lv:
                    for z in lv:
                        if x > z + 1 and x - 1 in L:
                            if cond == "NE" and any(v < z or v > x for v in p):
                                continue
                            yield f(cond, "rel", f"{lst(p)} {num(x)} {num(z)}", 4 if cond == "GNE" else 5,
                                    p + (x - 1,) * (1 + w.g), p + (x,) + (z,) * w.g)  # fmt: skip
        elif cond in ("GIAA", "IAA"):
            for p in pops:
                for x, y, z, m in self._xyzm():
                    if cond == "IAA" and any(v < z or v > y + 1 for v in p):
                        continue
                    yield f(cond, "rel", f"{lst(p)} {num(x)} {num(y)} {num(z)} {m}", 7 if cond == "GIAA" else 8,
                            p + (y,) * (m + w.c(x, y, z, m)), p + (x,) * m + (z,) * w.c(x, y, z, m))  # fmt: skip
        elif cond == "GNEP":
            for p in pops:
                for z in lv:
                    if z - 1 not in L:
                        continue
                    for x in lv:
                        for y in lv:
                            if x >= s.A and 0 < y <= 3:
                                yield f(cond, "rel", f"{lst(p)} {num(z)} {num(x)} {num(y)}", 7,
                                        p + (z - 1,) + (x,) * w.g, p + (z,) + (y,) * w.g)  # fmt: skip
        elif cond == "ST":
            for p in pops:
                for z in lv:
                    for y in lv:
                        for x in lv:
                            if z < 0 < y <= 3 and x >= s.A:
                                for m in sizes:
                                    yield f(cond, "rel", f"{lst(p)} {num(z)} {num(y)} {num(x)} {m}", 8,
                                            p + (z,) * m + (x,) * w.st_b(z, m), p + (y,) * (m + w.st_b(z, m)))  # fmt: skip
        elif cond == "AvoidRC":
            for big in sizes:
                yield f(cond, "notbetter", f"{big}", 1, (3,) * big, (s.A,) * w.rc_m)
        elif cond == "AvoidRA":
            for p in pops:
                for big in sizes:
                    yield f(cond, "notbetter", f"{lst(p)} {big}", 2, p + (3,) * big, p + (s.A,) * w.ra_n)
        elif cond == "AvoidVRC":
            for big in sizes:
                yield f(cond, "notbetter", f"{big}", 1,
                        (w.vr_z,) * w.vr_m + (3,) * big, (s.A,) * w.vr_n)  # fmt: skip
        elif cond == "AvoidVRA":
            for p in pops:
                for big in sizes:
                    yield f(cond, "notbetter", f"{lst(p)} {big}", 2,
                            p + (w.vr_z,) * w.vr_m + (3,) * big, p + (s.A,) * w.vr_n)  # fmt: skip
        else:
            raise ValueError(cond)

    def _xyzm(self):
        lv = sorted(self.L)
        for x in lv:
            for y in lv:
                for z in lv:
                    if x > y > z:
                        for m in range(1, self.s.max_size + 1):
                            yield x, y, z, m


def strongest(mus):
    """Drop a conflict if weakening one of its conditions still gives a conflict."""
    keep = []
    for m in mus:
        dominated = False
        for other in mus:
            if other == m:
                continue
            if all(c in m or any(WEAKER.get(d) == c for d in m) for c in other) and len(other) <= len(m):
                # `other` uses only conditions of `m` or weaker counterparts of them
                if any(c not in m for c in other):
                    dominated = True
                    break
        if not dominated:
            keep.append(m)
    return keep
