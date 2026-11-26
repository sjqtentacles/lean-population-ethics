import PopEthics.Finite

/-!
# Arrhenius's adequacy conditions

The conditions of Arrhenius's impossibility theorems, following Teruji Thomas,
"Reconstructing Arrhenius's Impossibility Theorems" (2016).

Welfare levels are the integers from `Z` (an abominable life) up to `T`. Level `0`
is neutral, levels `1`, `2`, `3` are barely worth living, and levels from `A` up are
excellent. Populations are lists of such levels, compared through `pop`.

Where a condition says "there is a number such that ...", the number is an explicit
parameter here (a *witness*). The condition as Arrhenius states it is the existence
of some witness for which the parametrised condition holds.

`R X Y` reads "`X` is at least as good as `Y`".
-/

namespace PopEthics.Arrhenius

/-- `n` people at level `x`. -/
abbrev rep (n : ℕ) (x : ℤ) : List ℤ := List.replicate n x

section Perm

variable {R : Axiology} {a b a' b' : List ℤ}

theorem rel_perm (h : R (pop a) (pop b)) (ha : a.Perm a') (hb : b.Perm b') :
    R (pop a') (pop b') := by
  rwa [← pop_perm ha, ← pop_perm hb]

theorem better_perm (h : Better R (pop a) (pop b)) (ha : a.Perm a') (hb : b.Perm b') :
    R (pop a') (pop b') ∧ ¬ R (pop b') (pop a') := by
  rw [← pop_perm ha, ← pop_perm hb]
  exact h

theorem not_better_perm (h : ¬ Better R (pop a) (pop b)) (ha : a.Perm a')
    (hb : b.Perm b') : ¬ (R (pop a') (pop b') ∧ ¬ R (pop b') (pop a')) := by
  rw [← pop_perm ha, ← pop_perm hb]
  exact h

end Perm

variable (R : Axiology) (Z A T : ℤ)

/-- `x` is one of the welfare levels. -/
abbrev InW (x : ℤ) : Prop := Z ≤ x ∧ x ≤ T

/-- Every member of `P` is at one of the welfare levels. -/
abbrev AllInW (P : List ℤ) : Prop := ∀ w ∈ P, Z ≤ w ∧ w ≤ T

/-- Every member of `P` has welfare between `lo` and `hi`. -/
abbrev Between (lo hi : ℤ) (P : List ℤ) : Prop := ∀ w ∈ P, lo ≤ w ∧ w ≤ hi

/-- Reflexivity, on populations over the welfare levels. -/
def Refl : Prop := ∀ P : List ℤ, R (pop P) (pop P)

/-- **Egalitarian Dominance.** Of two perfectly equal populations of the same
size, the one with higher welfare is better. -/
def ED : Prop :=
  ∀ (x y : ℤ) (n : ℕ), InW Z T x → InW Z T y → x < y → 0 < n →
    Better R (pop (rep n y)) (pop (rep n x))

/-- **Quantity.** A small drop in welfare for everyone can be made up for by a
larger population: `q w m` people at `w - 1` are at least as good as `m` at `w`. -/
def Quantity (q : ℤ → ℕ → ℕ) : Prop :=
  ∀ (w : ℤ) (m : ℕ), InW Z T w → 1 < w → 0 < m →
    R (pop (rep (q w m) (w - 1))) (pop (rep m w))

/-- **Dominance Addition.** Improving everyone's welfare and adding people with
positive welfare does not make things worse. -/
def DA : Prop :=
  ∀ (x y z : ℤ) (m n : ℕ), InW Z T x → InW Z T y → InW Z T z → y < x → 0 < z →
    0 < m → 0 < n → R (pop (rep m x ++ rep n z)) (pop (rep m y))

/-- **Inequality Aversion.** Lowering `m` people from `x` to `y` can be made up for
by raising `c x y z m` people from `z` to `y`. -/
def IA (c : ℤ → ℤ → ℤ → ℕ → ℕ) : Prop :=
  ∀ (x y z : ℤ) (m : ℕ), InW Z T x → InW Z T y → InW Z T z → z < y → y < x → 0 < m →
    R (pop (rep m y ++ rep (c x y z m) y)) (pop (rep m x ++ rep (c x y z m) z))

/-- **General Inequality-Averse Addition.** Inequality Aversion with an unaffected
background population `P`. -/
def GIAA (c : ℤ → ℤ → ℤ → ℕ → ℕ) : Prop :=
  ∀ (P : List ℤ) (x y z : ℤ) (m : ℕ), AllInW Z T P → InW Z T x → InW Z T y →
    InW Z T z → z < y → y < x → 0 < m →
    R (pop (P ++ rep m y ++ rep (c x y z m) y)) (pop (P ++ rep m x ++ rep (c x y z m) z))

/-- **Inequality-Averse Addition.** As `GIAA`, with the background population's
welfare restricted to lie between `z` and `y + 1`. -/
def IAA (c : ℤ → ℤ → ℤ → ℕ → ℕ) : Prop :=
  ∀ (P : List ℤ) (x y z : ℤ) (m : ℕ), AllInW Z T P → Between z (y + 1) P → InW Z T x →
    InW Z T y → InW Z T z → z < y → y < x → 0 < m →
    R (pop (P ++ rep m y ++ rep (c x y z m) y)) (pop (P ++ rep m x ++ rep (c x y z m) z))

/-- **Non-Sadism.** Adding any number of people with positive welfare is at least
as good as adding any number with negative welfare. -/
def NS : Prop :=
  ∀ (P : List ℤ) (x z : ℤ) (m n : ℕ), AllInW Z T P → InW Z T x → InW Z T z → z < 0 →
    0 < x → 0 < m → 0 < n → R (pop (P ++ rep m x)) (pop (P ++ rep n z))

/-- **Weak Non-Sadism.** Adding any number of people with positive welfare is at
least as good as adding `d` abominable lives. -/
def WNS (d : ℕ) : Prop :=
  ∀ (P : List ℤ) (x : ℤ) (m : ℕ), AllInW Z T P → InW Z T x → 0 < x → 0 < m →
    R (pop (P ++ rep m x)) (pop (P ++ rep d Z))

/-- **Non-Extreme Priority.** Raising one person from just below neutral to barely
worth living does not outweigh raising `b` people from barely worth living to
excellent. -/
def NEP (b : ℕ) : Prop :=
  ∀ P : List ℤ, AllInW Z T P →
    R (pop (P ++ [-1] ++ rep b A)) (pop (P ++ [3] ++ rep b 3))

/-- **General Non-Extreme Priority.** Raising one person by one level does not
outweigh raising `g z` others from barely worth living to excellent. -/
def GNEP (g : ℤ → ℕ) : Prop :=
  ∀ (P : List ℤ) (z x y : ℤ), AllInW Z T P → InW Z T z → InW Z T (z - 1) → InW Z T x →
    A ≤ x → 0 < y → y ≤ 3 →
    R (pop (P ++ [z - 1] ++ rep (g z) x)) (pop (P ++ [z] ++ rep (g z) y))

/-- **Sufficient Tradeoffs.** Raising `m` people from a negative level `z` to barely
worth living does not outweigh raising `b z m` others from barely worth living to
excellent. -/
def ST (b : ℤ → ℕ → ℕ) : Prop :=
  ∀ (P : List ℤ) (z y x : ℤ) (m : ℕ), AllInW Z T P → InW Z T z → InW Z T x → z < 0 →
    0 < y → y ≤ 3 → A ≤ x → 0 < m →
    R (pop (P ++ rep m z ++ rep (b z m) x)) (pop (P ++ rep m y ++ rep (b z m) y))

/-- **General Non-Elitism.** Raising one person from `x - 1` to `x` does not
outweigh raising `g x z` worse-off people from `z` to `x - 1`. -/
def GNE (g : ℤ → ℤ → ℕ) : Prop :=
  ∀ (P : List ℤ) (x z : ℤ), AllInW Z T P → InW Z T x → InW Z T z → z + 1 < x →
    R (pop (P ++ [x - 1] ++ rep (g x z) (x - 1))) (pop (P ++ [x] ++ rep (g x z) z))

/-- **Non-Elitism.** As `GNE`, with the background population's welfare restricted
to lie between `z` and `x`. -/
def NE (g : ℤ → ℤ → ℕ) : Prop :=
  ∀ (P : List ℤ) (x z : ℤ), AllInW Z T P → Between z x P → InW Z T x → InW Z T z →
    z + 1 < x →
    R (pop (P ++ [x - 1] ++ rep (g x z) (x - 1))) (pop (P ++ [x] ++ rep (g x z) z))

/-! ## Avoiding the repugnant conclusions

Each conclusion Arrhenius wants to avoid says that some huge barely-worth-living
population is *better* than an excellent one. The conditions below deny this at one
explicit instance. -/

/-- No population at level `3` is better than `m` people at level `A`. -/
def AvoidRC (m : ℕ) : Prop :=
  ∀ M : ℕ, 0 < M → ¬ Better R (pop (rep M 3)) (pop (rep m A))

/-- For every background `P`, adding any number of people at level `3` is not
better than adding `n` at level `A`. -/
def AvoidRA (n : ℕ) : Prop :=
  ∀ (P : List ℤ) (M : ℕ), AllInW Z T P → 0 < M →
    ¬ Better R (pop (P ++ rep M 3)) (pop (P ++ rep n A))

/-- `m` people at negative level `z` plus any number at level `3` are not better
than `n` people at level `A`. -/
def AvoidVRC (z : ℤ) (m n : ℕ) : Prop :=
  ∀ M : ℕ, 0 < M → ¬ Better R (pop (rep m z ++ rep M 3)) (pop (rep n A))

/-- `AvoidVRC` with an unaffected background population. -/
def AvoidVRA (z : ℤ) (m n : ℕ) : Prop :=
  ∀ (P : List ℤ) (M : ℕ), AllInW Z T P → 0 < M →
    ¬ Better R (pop (P ++ rep m z ++ rep M 3)) (pop (P ++ rep n A))

end PopEthics.Arrhenius
