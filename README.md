# PopEthics

Population ethics in Lean 4: adequacy conditions for population axiologies,
machine-checked impossibility results, and reference axiologies showing which
conditions can hold together.

**Main result.** Arrhenius's sixth impossibility theorem is false as stated: there
is a reflexive, transitive and complete population axiology on a discrete welfare
scale that satisfies all five of its conditions. See the note
[`paper/sixth-theorem.pdf`](paper/sixth-theorem.pdf) and the proof in
[`PopEthics/SixthTheorem.lean`](PopEthics/SixthTheorem.lean).

## Contents

- `PopEthics/Basic.lean`: populations, axiologies, and the adequacy conditions.
- `PopEthics/MereAddition.lean`: transitivity, Mere Addition and
  Non-Anti-Egalitarianism imply the Repugnant Conclusion.
- `PopEthics/Models.lean`: totalism satisfies all the premises; averagism avoids
  the Repugnant Conclusion by violating Mere Addition.
- `PopEthics/Finite.lean`: ground instances of the conditions over integer levels.
- `PopEthics/Certificates.lean`: conflicts found by SAT search, as Lean theorems
  (generated).
- `PopEthics/Arrhenius.lean`: Arrhenius's conditions, following Thomas's
  reconstruction, with each "there is a number" as an explicit parameter.
- `PopEthics/ArrheniusCertificates.lean`: conflicts among those conditions found by
  SAT search (generated).
- `PopEthics/SixthTheorem.lean`: Arrhenius's sixth impossibility theorem in its
  exact published formulation, and a population axiology that satisfies all five
  of its conditions, so the theorem is false as stated. The same axiology violates
  a strengthened form of Weak Quality Addition, and falsifies Lemma 1.3 of the
  published proof.

Build with `lake build`.

## SAT search

`search/` needs Python with `python-sat`.

- `python3 search/run_map.py [max_size] [level ...]` prints which sets of conditions
  conflict on a finite domain and which are jointly consistent there.
- `python3 search/make_certificates.py` regenerates `PopEthics/Certificates.lean`.
- `python3 search/run_thomas.py [max_size] [top_level] [skipped level ...]` and
  `python3 search/make_thomas_certificates.py` do the same for Arrhenius's conditions.

A conflict found on a finite domain is a conflict for all populations, and the
generated Lean proof checks this. A set that is consistent on a finite domain may
still conflict on a larger one.

## Paper

`paper/sixth-theorem.typ` is a draft note on the sixth-theorem result. Build it with
`typst compile paper/sixth-theorem.typ`.

## Citation

Sarkisyan, A. (2026). *Arrhenius's Sixth Impossibility Theorem Is False as Stated:
A Machine-Checked Counterexample* (Version 1.0). Zenodo.
https://doi.org/10.5281/zenodo.24549569

The DOI [10.5281/zenodo.24549568](https://doi.org/10.5281/zenodo.24549568) always
resolves to the latest version.

## Licence

Code is under the MIT licence (`LICENSE`). The paper in `paper/` is under CC BY 4.0
(`paper/LICENSE`).
