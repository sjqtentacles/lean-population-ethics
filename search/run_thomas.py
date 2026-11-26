"""Conflict map for Arrhenius's conditions (Thomas's reconstruction) on one domain.

Usage: python3 search/run_thomas.py [max_size] [T] [skipped level ...]
  T is the top welfare level (default 4 = A); use 6 to include A+1 and A+2.
"""

import sys
import time

from popsat import THEORIES, Encoding, conflict_map, satisfies
from thomas import CONDITIONS, Scale, ThomasDomain, strongest


def main():
    args = [int(x) for x in sys.argv[1:]]
    max_size = args[0] if args else 4
    top = args[1] if len(args) > 1 else 4
    skip = set(args[2:])  # levels to leave out of the search domain
    s = Scale(levels=tuple(x for x in range(-1, top + 1) if x not in skip), max_size=max_size, T=top)
    dom = ThomasDomain(s)
    print(f"levels {list(s.levels)} (A = {s.A}), populations of size <= {s.max_size}: {len(dom.pops)} populations\n")

    print("Reference theories (conditions violated in this domain):")
    for name, theory in THEORIES.items():
        bad = [c for c in CONDITIONS if not satisfies(dom, theory, c)]
        print(f"  {name:22s} violates {bad or 'nothing'}")

    t = time.time()
    enc = Encoding(dom, CONDITIONS)
    print(f"\nencoded in {time.time() - t:.1f}s; ground instances per condition:")
    print("  " + ", ".join(f"{c} {enc.counts[c]}" for c in CONDITIONS))

    t = time.time()
    mus, mss = conflict_map(enc)
    print(f"\nsearch took {time.time() - t:.1f}s: {len(mus)} minimal conflicting sets, {len(mss)} maximal consistent sets")
    best = strongest(mus)
    print(f"\nMinimal conflicting sets, weakest conditions only ({len(best)}):")
    for m in sorted(best, key=lambda x: (len(x), [CONDITIONS.index(c) for c in CONDITIONS if c in x])):
        print("  " + ", ".join(c for c in CONDITIONS if c in m))
    return dom, mus, mss


if __name__ == "__main__":
    main()
