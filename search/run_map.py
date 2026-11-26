"""Print the conflict map for one finite domain.

Usage: python3 search/run_map.py [max_size] [level ...]
"""

import sys
import time

from popsat import CONDITIONS, THEORIES, Domain, Encoding, Params, conflict_map, satisfies


def main():
    args = [int(x) for x in sys.argv[1:]]
    p = Params()
    if args:
        p = Params(max_size=args[0], levels=tuple(args[1:]) or p.levels)
    dom = Domain(p)
    print(f"levels {list(p.levels)}, populations of size <= {p.max_size}: {len(dom.pops)} populations")
    print(f"AvoidRC instance: no population at level {p.low} is better than {p.rc_n} at level {p.high}\n")

    print("Reference theories (conditions violated in this domain):")
    profile = {}
    for name, theory in THEORIES.items():
        ok = {c for c in CONDITIONS if satisfies(dom, theory, c)}
        profile[name] = ok
        print(f"  {name:22s} violates {sorted(set(CONDITIONS) - ok) or 'nothing'}")

    t = time.time()
    enc = Encoding(dom)
    print(f"\nencoded in {time.time() - t:.1f}s; ground instances per condition:")
    for c in CONDITIONS:
        print(f"  {c:14s} {enc.counts[c]}")

    t = time.time()
    mus, mss = conflict_map(enc)
    print(f"\nsearch took {time.time() - t:.1f}s")
    print(f"\nMinimal conflicting sets ({len(mus)}):")
    for m in sorted(mus, key=lambda s: (len(s), sorted(s))):
        print("  " + ", ".join(c for c in CONDITIONS if c in m))
    print(f"\nMaximal consistent sets ({len(mss)}), by what they give up:")
    for s in sorted(mss, key=lambda s: (-len(s), sorted(s))):
        dropped = [c for c in CONDITIONS if c not in s]
        witnesses = [n for n, ok in profile.items() if s <= ok]
        note = f"  [satisfied by {', '.join(witnesses)}]" if witnesses else "  [solver model only]"
        print("  drop " + ", ".join(dropped) + note)


if __name__ == "__main__":
    main()
