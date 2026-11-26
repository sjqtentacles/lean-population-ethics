import Mathlib

/-!
# Population axiologies: basic definitions

A population is recorded only by the welfare levels of its members, so two
populations with the same welfare distribution are identified (anonymity is built in).
Welfare levels are rationals; level `0` is the neutral level, and a life with
positive welfare is a life worth living.

An axiology is a binary relation on populations, read "at least as good as".
The adequacy conditions below are properties of such a relation.
-/

namespace PopEthics

/-- A population: the multiset of its members' welfare levels. -/
abbrev Population := Multiset ℚ

/-- A population axiology. `R A B` reads "`A` is at least as good as `B`". -/
abbrev Axiology := Population → Population → Prop

/-- `n` people, all at welfare level `w`. -/
abbrev equalPop (n : ℕ) (w : ℚ) : Population := Multiset.replicate n w

/-- A population in which at least two people differ in welfare. -/
def Unequal (A : Population) : Prop := ∃ a ∈ A, ∃ b ∈ A, a ≠ b

variable (R : Axiology)

/-- `A` is strictly better than `B`. -/
def Better (A B : Population) : Prop := R A B ∧ ¬ R B A

/-- Transitivity of "at least as good as". -/
def Trans : Prop := ∀ A B C : Population, R A B → R B C → R A C

/-- **Mere Addition.** Adding people whose lives are worth living, without
affecting anyone else, does not make a population worse. -/
def MereAddition : Prop :=
  ∀ A B : Population, (∀ w ∈ B, 0 < w) → R (A + B) A

/-- **Non-Anti-Egalitarianism.** A perfectly equal population is better than an
unequal population of the same size with lower total (hence lower average) welfare. -/
def NonAntiEgalitarianism : Prop :=
  ∀ (A : Population) (w : ℚ), Unequal A → A.sum < A.card * w →
    Better R (equalPop A.card w) A

/-- **The Repugnant Conclusion.** For any perfectly equal population, however high
its welfare level `h`, and any positive welfare level `ε`, however low, there is a
non-empty population of people all at level `ε` that is strictly better. -/
def RepugnantConclusion : Prop :=
  ∀ (n : ℕ) (h ε : ℚ), 0 < n → 0 < ε →
    ∃ m : ℕ, 0 < m ∧ Better R (equalPop m ε) (equalPop n h)

/-- One way of avoiding the Repugnant Conclusion: no population at level `ε` is
better than `n` people at level `h`. -/
def AvoidsRepugnance (n : ℕ) (h ε : ℚ) : Prop :=
  ∀ m : ℕ, 0 < m → ¬ Better R (equalPop m ε) (equalPop n h)

/-- The Repugnant Conclusion holds exactly when it is avoided at no instance. -/
theorem repugnantConclusion_iff :
    RepugnantConclusion R ↔
      ∀ (n : ℕ) (h ε : ℚ), 0 < n → 0 < ε → ¬ AvoidsRepugnance R n h ε := by
  simp only [RepugnantConclusion, AvoidsRepugnance]
  push Not
  rfl

/-- **Dominance.** If two populations of the same size can be matched person to
person so that everyone in the first is at least as well off, and they are not
identical, the first is better. -/
def Dominance : Prop :=
  ∀ a b : List ℚ, List.Forall₂ (fun x y => y ≤ x) a b → a ≠ b →
    Better R (a : Multiset ℚ) (b : Multiset ℚ)

/-- **Pigou–Dalton.** A transfer of `d` from a better-off person to a worse-off
person that does not reverse their order does not make things worse. -/
def PigouDalton : Prop :=
  ∀ (X : Population) (hi lo d : ℚ), 0 < d → lo + d ≤ hi - d →
    R (X + {hi - d, lo + d}) (X + {hi, lo})

/-- **Non-Elitism**, at group size `m` and welfare step `s`. Raising one person from
`b` to `b + s` does not outweigh lowering `m` others from `b` to a lower level `c`,
whatever the rest of the population `X` (with levels between `c` and `b + s`). -/
def NonElitism (m : ℕ) (s : ℚ) : Prop :=
  ∀ (X : Population) (b c : ℚ), c < b → (∀ w ∈ X, c ≤ w ∧ w ≤ b + s) →
    R (X + equalPop (m + 1) b) (X + ((b + s) ::ₘ equalPop m c))

end PopEthics
