import PopEthics.Finite

/-!
# Arrhenius's sixth impossibility theorem, as stated, is false

Gustaf Arrhenius, "The Impossibility of a Satisfactory Population Ethics" (2011),
states (§1.4): *there is no population axiology which satisfies the Egalitarian
Dominance, the General Non-Extreme Priority, the Non-Elitism, the Weak Non-Sadism,
and the Weak Quality Addition Condition.*

This file formalises the five conditions in their "exact formulations" (§1.3 of
that paper) and exhibits a population axiology that satisfies all of them. The
axiology is moreover reflexive, transitive and complete, and welfare levels are the
integers, so Arrhenius's Discreteness assumption holds.

The gap is a quantifier order. Weak Quality Addition begins "for any population X,
there is a negative welfare level and a number of lives at this level ...", so the
number of bad lives may depend on `X`. Teruji Thomas and Elliott Thornley have
noted that the argument needs a stronger condition, in which the negative level and
the number are chosen first, for all `X` at once. `StrongQualityAddition` below is
the corresponding strengthening of the exact formulation; the axiology constructed
here violates it. This file does not prove that the theorem holds with the
strengthened condition.

One side condition is added to the published wording. Egalitarian Dominance is
stated for non-empty populations: read literally at size zero it would require the
empty population to be better than itself, which no reflexive relation allows.

`R X Y` reads "`X` is at least as good as `Y`". Populations are lists of integer
welfare levels, compared through `pop`; level `0` is neutral.
-/

namespace PopEthics.Sixth

/-- Every member of `P` has welfare between `lo` and `hi`. -/
def Within (lo hi : ℤ) (P : List ℤ) : Prop := ∀ w ∈ P, lo ≤ w ∧ w ≤ hi

section Conditions

variable (R : Axiology)

/-- **Egalitarian Dominance** (exact formulation). If `A` is perfectly equal at
level `x`, `B` has the same size, and every member of `B` has welfare below `x`,
then `A` is better than `B`. The hypothesis `B ≠ []` is not in the published
wording; without it the instance `A = B = ∅` would contradict reflexivity. -/
def EgalitarianDominance : Prop :=
  ∀ (B : List ℤ) (x : ℤ), B ≠ [] → (∀ w ∈ B, w < x) →
    Better R (pop (List.replicate B.length x)) (pop B)

/-- **General Non-Extreme Priority** (exact formulation). For any level `z` there
are a positive level `u`, a positive range `1..y` below `u`, and a number `n > 0`
such that: `n` lives at any one level `x ≥ u` together with one life at `z` are at
least as good as `n` lives in the range `1..y` together with one life at `z + 1`,
whatever the rest of the population `E`. -/
def GeneralNonExtremePriority : Prop :=
  ∀ z : ℤ, ∃ (u y : ℤ) (n : ℕ), 3 ≤ y ∧ y < u ∧ 0 < n ∧
    ∀ (x : ℤ) (B E : List ℤ), u ≤ x → B.length = n → Within 1 y B →
      R (pop (List.replicate n x ++ [z] ++ E)) (pop (B ++ [z + 1] ++ E))

/-- **Non-Elitism** (exact formulation). For any levels `x`, `y` with `x - 1 > y`
there is a number `n > 0` such that `n + 1` lives at `x - 1` are at least as good
as one life at `x` and `n` lives at `y`, whatever the rest of the population `D`
with welfare between `y` and `x`. -/
def NonElitism : Prop :=
  ∀ x y : ℤ, y < x - 1 → ∃ n : ℕ, 0 < n ∧ ∀ D : List ℤ, Within y x D →
    R (pop (List.replicate (n + 1) (x - 1) ++ D)) (pop ([x] ++ List.replicate n y ++ D))

/-- **Weak Non-Sadism** (exact formulation). There are a negative level `x` and a
number `n` such that adding any number of lives at any positive level `y` is at
least as good as adding `n` lives at `x`, whatever the rest of the population `C`. -/
def WeakNonSadism : Prop :=
  ∃ (x : ℤ) (n : ℕ), x < 0 ∧ 0 < n ∧ ∀ (y : ℤ) (k : ℕ) (C : List ℤ), 0 < y →
    R (pop (List.replicate k y ++ C)) (pop (List.replicate n x ++ C))

/-- **Weak Quality Addition** (exact formulation). For any population `X` there are
a negative level `x`, positive ranges `u..v` and `1..y` with `u > y`, and sizes
`n, m > 0` such that adding `n` lives at any one level `z ≥ u` to `X` is at least as
good as adding `m` lives at `x` together with any population `B` in the range `1..y`. -/
def WeakQualityAddition : Prop :=
  ∀ X : List ℤ, ∃ (x u v y : ℤ) (n m : ℕ),
    x < 0 ∧ 3 ≤ y ∧ y < u ∧ u + 2 ≤ v ∧ 0 < n ∧ 0 < m ∧
    ∀ (z : ℤ) (B : List ℤ), u ≤ z → Within 1 y B →
      R (pop (List.replicate n z ++ X)) (pop (B ++ List.replicate m x ++ X))

/-- Weak Quality Addition with the negative level and the number of lives at it
chosen before the population `X`. Line (12) of the published proof of Lemma 1.3
treats these as independent of the background population, which only this
stronger condition licenses. -/
def StrongQualityAddition : Prop :=
  ∃ (x : ℤ) (m : ℕ), x < 0 ∧ 0 < m ∧ ∀ X : List ℤ, ∃ (u v y : ℤ) (n : ℕ),
    3 ≤ y ∧ y < u ∧ u + 2 ≤ v ∧ 0 < n ∧
    ∀ (z : ℤ) (B : List ℤ), u ≤ z → Within 1 y B →
      R (pop (List.replicate n z ++ X)) (pop (B ++ List.replicate m x ++ X))

/-- The strong condition implies the weak one. -/
theorem StrongQualityAddition.weak (h : StrongQualityAddition R) :
    WeakQualityAddition R := by
  obtain ⟨x, m, hx, hm, h⟩ := h
  intro X
  obtain ⟨u, v, y, n, hy, hyu, huv, hn, H⟩ := h X
  exact ⟨x, u, v, y, n, m, hx, hy, hyu, huv, hn, hm, H⟩

end Conditions

/-! ## The axiology

Call a life *excellent* if its welfare is at least `4`, and let the *suffering* in a
population be the sum of `-w` over its lives with negative welfare `w`. A
population is *compensated* if it has at least as many excellent lives as it has
suffering. Compensated populations are better than uncompensated ones, and within
each class populations are ranked by total welfare. -/

/-- The suffering in a life. -/
def bad (w : ℚ) : ℚ := if w < 0 then -w else 0

/-- `1` if the life is excellent, else `0`. -/
def exc (w : ℚ) : ℚ := if 4 ≤ w then 1 else 0

/-- At least as many excellent lives as there is suffering. -/
def Compensated (X : Population) : Prop := (X.map bad).sum ≤ (X.map exc).sum

/-- Compensated populations first; then total welfare. -/
def lex : Axiology := fun X Y =>
  (Compensated X ∧ ¬ Compensated Y) ∨ ((Compensated X ↔ Compensated Y) ∧ Y.sum ≤ X.sum)

theorem lex_refl (X : Population) : lex X X := Or.inr ⟨Iff.rfl, le_rfl⟩

theorem lex_trans : Trans lex := by
  rintro X Y W (⟨hx, hy⟩ | ⟨hxy, h1⟩) (⟨hy', hw⟩ | ⟨hyw, h2⟩)
  · exact absurd hy' hy
  · exact Or.inl ⟨hx, fun hw => hy (hyw.2 hw)⟩
  · exact Or.inl ⟨hxy.2 hy', hw⟩
  · exact Or.inr ⟨hxy.trans hyw, le_trans h2 h1⟩

theorem lex_total (X Y : Population) : lex X Y ∨ lex Y X := by
  unfold lex
  rcases le_total Y.sum X.sum with h | h <;> by_cases hx : Compensated X <;>
    by_cases hy : Compensated Y <;> simp [hx, hy, h]

/-! ### Integer bookkeeping -/

/-- The suffering in a life at integer level `w`. -/
def negZ (w : ℤ) : ℤ := if w < 0 then -w else 0

/-- `1` if the integer level `w` is excellent, else `0`. -/
def excZ (w : ℤ) : ℤ := if 4 ≤ w then 1 else 0

/-- Total suffering. -/
def νZ (l : List ℤ) : ℤ := (l.map negZ).sum

/-- Number of excellent lives. -/
def eZ (l : List ℤ) : ℤ := (l.map excZ).sum

@[simp] theorem νZ_nil : νZ [] = 0 := rfl
@[simp] theorem eZ_nil : eZ [] = 0 := rfl
@[simp] theorem νZ_cons (a : ℤ) (l : List ℤ) : νZ (a :: l) = negZ a + νZ l := by simp [νZ]
@[simp] theorem eZ_cons (a : ℤ) (l : List ℤ) : eZ (a :: l) = excZ a + eZ l := by simp [eZ]
@[simp] theorem νZ_append (a b : List ℤ) : νZ (a ++ b) = νZ a + νZ b := by simp [νZ]
@[simp] theorem eZ_append (a b : List ℤ) : eZ (a ++ b) = eZ a + eZ b := by simp [eZ]

theorem νZ_replicate (n : ℕ) (a : ℤ) : νZ (List.replicate n a) = n * negZ a := by
  simp [νZ, List.sum_replicate]

theorem eZ_replicate (n : ℕ) (a : ℤ) : eZ (List.replicate n a) = n * excZ a := by
  simp [eZ, List.sum_replicate]

theorem negZ_nonneg (w : ℤ) : 0 ≤ negZ w := by unfold negZ; split_ifs <;> omega

theorem excZ_nonneg (w : ℤ) : 0 ≤ excZ w := by unfold excZ; split_ifs <;> omega

theorem νZ_nonneg (l : List ℤ) : 0 ≤ νZ l := by
  induction l with
  | nil => simp
  | cons a t ih => have := negZ_nonneg a; simp only [νZ_cons]; omega

theorem eZ_nonneg (l : List ℤ) : 0 ≤ eZ l := by
  induction l with
  | nil => simp
  | cons a t ih => have := excZ_nonneg a; simp only [eZ_cons]; omega

theorem νZ_eq_zero {l : List ℤ} (h : ∀ w ∈ l, 0 ≤ w) : νZ l = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha := h a (by simp)
    have ht := ih fun w hw => h w (by simp [hw])
    simp only [νZ_cons, ht, negZ]
    split_ifs <;> omega

theorem eZ_eq_zero {l : List ℤ} (h : ∀ w ∈ l, w < 4) : eZ l = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha := h a (by simp)
    have ht := ih fun w hw => h w (by simp [hw])
    simp only [eZ_cons, ht, excZ]
    split_ifs <;> omega

theorem eZ_eq_length {l : List ℤ} (h : ∀ w ∈ l, 4 ≤ w) : eZ l = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha := h a (by simp)
    have ht := ih fun w hw => h w (by simp [hw])
    simp only [eZ_cons, ht, excZ, List.length_cons, ha, ↓reduceIte]
    push_cast
    omega

theorem νZ_pos {l : List ℤ} (h : ∀ w ∈ l, w < 0) (hl : l ≠ []) : 0 < νZ l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t =>
    have ha := h a (by simp)
    have := νZ_nonneg t
    simp only [νZ_cons, negZ, ha, ↓reduceIte]
    omega

theorem sum_nonneg' {l : List ℤ} (h : ∀ w ∈ l, 0 ≤ w) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a (by simp)
    have ht := ih fun w hw => h w (by simp [hw])
    simp only [List.sum_cons]; omega

theorem sum_le_three {l : List ℤ} (h : ∀ w ∈ l, w ≤ 3) : l.sum ≤ 3 * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a (by simp)
    have ht := ih fun w hw => h w (by simp [hw])
    simp only [List.sum_cons, List.length_cons]; push_cast; omega

theorem sum_lt_replicate {l : List ℤ} {x : ℤ} (h : ∀ w ∈ l, w < x) (hl : l ≠ []) :
    l.sum < (List.replicate l.length x).sum := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a t ih =>
    have ha := h a (by simp)
    by_cases ht : t = []
    · subst ht; simpa using ha
    · have := ih (fun w hw => h w (by simp [hw])) ht
      simp only [List.sum_cons, List.length_cons, List.replicate_succ] at this ⊢
      omega

/-! ### From rational populations to integer bookkeeping -/

theorem bad_cast (z : ℤ) : bad (z : ℚ) = (negZ z : ℚ) := by
  unfold bad negZ
  by_cases h : z < 0
  · have h' : (z : ℚ) < 0 := by exact_mod_cast h
    simp [h, h']
  · have h' : ¬ (z : ℚ) < 0 := by exact_mod_cast h
    simp [h, h']

theorem exc_cast (z : ℤ) : exc (z : ℚ) = (excZ z : ℚ) := by
  unfold exc excZ
  by_cases h : 4 ≤ z
  · have h' : (4 : ℚ) ≤ z := by exact_mod_cast h
    simp [h, h']
  · have h' : ¬ (4 : ℚ) ≤ z := by exact_mod_cast h
    simp [h, h']

theorem bad_sum_pop (l : List ℤ) : ((pop l).map bad).sum = ((νZ l : ℤ) : ℚ) := by
  induction l with
  | nil => simp [pop]
  | cons a t ih => rw [pop_cons]; simp [ih, bad_cast]

theorem exc_sum_pop (l : List ℤ) : ((pop l).map exc).sum = ((eZ l : ℤ) : ℚ) := by
  induction l with
  | nil => simp [pop]
  | cons a t ih => rw [pop_cons]; simp [ih, exc_cast]

theorem compensated_pop (l : List ℤ) : Compensated (pop l) ↔ νZ l ≤ eZ l := by
  rw [Compensated, bad_sum_pop, exc_sum_pop]
  exact Int.cast_le

theorem lex_pop (a b : List ℤ) :
    lex (pop a) (pop b) ↔
      (νZ a ≤ eZ a ∧ ¬ νZ b ≤ eZ b) ∨ ((νZ a ≤ eZ a ↔ νZ b ≤ eZ b) ∧ b.sum ≤ a.sum) := by
  simp only [lex, compensated_pop, sum_pop, Int.cast_le]

/-- To show `a` at least as good as `b`: being compensated carries over from `b`
to `a`, and `a` has at least as much total welfare. -/
theorem lex_pop_of {a b : List ℤ} (hc : νZ b ≤ eZ b → νZ a ≤ eZ a) (hs : b.sum ≤ a.sum) :
    lex (pop a) (pop b) := by
  rw [lex_pop]
  by_cases hb : νZ b ≤ eZ b
  · exact Or.inr ⟨⟨fun _ => hb, fun _ => hc hb⟩, hs⟩
  · by_cases ha : νZ a ≤ eZ a
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨⟨fun h => absurd h ha, fun h => absurd h hb⟩, hs⟩

/-! ### The five conditions hold -/

theorem lex_egalitarianDominance : EgalitarianDominance lex := by
  intro B x hB hlt
  have hsum := sum_lt_replicate hlt hB
  have hcomp : νZ B ≤ eZ B →
      νZ (List.replicate B.length x) ≤ eZ (List.replicate B.length x) := by
    intro hc
    by_cases hx : 0 ≤ x
    · rw [νZ_eq_zero fun w hw => by rw [List.eq_of_mem_replicate hw]; exact hx]
      exact eZ_nonneg _
    · exfalso
      have h1 := νZ_pos (l := B) (fun w hw => by have := hlt w hw; omega) hB
      have h2 := eZ_eq_zero (l := B) fun w hw => by have := hlt w hw; omega
      omega
  refine ⟨lex_pop_of hcomp hsum.le, ?_⟩
  rw [lex_pop]
  rintro (⟨h1, h2⟩ | ⟨-, h⟩)
  · exact h2 (hcomp h1)
  · omega

theorem lex_generalNonExtremePriority : GeneralNonExtremePriority lex := by
  intro z
  refine ⟨4, 3, 1, le_rfl, by norm_num, one_pos, ?_⟩
  intro x B E hx hB hw
  have hν := νZ_eq_zero (l := B) fun w h => by have := hw w h; omega
  have he := eZ_eq_zero (l := B) fun w h => by have := hw w h; omega
  have hs := sum_le_three (l := B) fun w h => (hw w h).2
  rw [hB] at hs
  apply lex_pop_of
  · simp only [νZ_append, eZ_append, νZ_cons, eZ_cons, νZ_nil, eZ_nil, νZ_replicate,
      eZ_replicate, hν, he, negZ, excZ]
    split_ifs <;> push_cast <;> omega
  · simp only [List.sum_append, List.sum_cons, List.sum_nil, List.sum_replicate, nsmul_eq_mul]
    push_cast at hs ⊢
    omega

theorem lex_nonElitism : NonElitism lex := by
  intro x y hxy
  refine ⟨1, one_pos, ?_⟩
  intro D hD
  apply lex_pop_of
  · by_cases hy : 0 ≤ y
    · intro _
      have hν := νZ_eq_zero (l := D) fun w h => by have := (hD w h).1; omega
      have he := eZ_nonneg D
      simp only [νZ_append, eZ_append, νZ_replicate, eZ_replicate, hν, negZ, excZ]
      split_ifs <;> push_cast <;> omega
    · simp only [νZ_append, eZ_append, νZ_cons, eZ_cons, νZ_nil, eZ_nil, νZ_replicate,
        eZ_replicate, negZ, excZ]
      split_ifs <;> push_cast <;> omega
  · simp only [List.sum_append, List.sum_cons, List.sum_nil, List.sum_replicate, nsmul_eq_mul]
    push_cast
    omega

theorem lex_weakNonSadism : WeakNonSadism lex := by
  refine ⟨-1, 1, by norm_num, one_pos, ?_⟩
  intro y k C hy
  have hmem : ∀ w ∈ List.replicate k y, 0 ≤ w := fun w hw => by
    rw [List.eq_of_mem_replicate hw]; omega
  have hν := νZ_eq_zero hmem
  have he := eZ_nonneg (List.replicate k y)
  have hs := sum_nonneg' hmem
  apply lex_pop_of
  · simp only [νZ_append, eZ_append, hν, νZ_replicate, eZ_replicate, negZ, excZ]
    split_ifs <;> push_cast <;> omega
  · have h1 : (List.replicate 1 (-1 : ℤ)).sum = -1 := by simp
    simp only [List.sum_append, h1]
    omega

theorem lex_weakQualityAddition : WeakQualityAddition lex := by
  intro X
  refine ⟨-1, 4, 6, 3, (νZ X).toNat + 1, (eZ X).toNat + 1, by norm_num, le_rfl, by norm_num,
    by norm_num, Nat.succ_pos _, Nat.succ_pos _, ?_⟩
  intro z B hz hB
  have h1 := νZ_nonneg X
  have h2 := eZ_nonneg X
  have hνB := νZ_eq_zero (l := B) fun w h => by have := hB w h; omega
  have heB := eZ_eq_zero (l := B) fun w h => by have := hB w h; omega
  have hmem : ∀ w ∈ List.replicate ((νZ X).toNat + 1) z, 4 ≤ w := fun w hw => by
    rw [List.eq_of_mem_replicate hw]; exact hz
  have hνA := νZ_eq_zero fun w hw => by have := hmem w hw; omega
  have heA := eZ_eq_length hmem
  rw [lex_pop]
  left
  constructor
  · simp only [νZ_append, eZ_append, hνA, heA, List.length_replicate]
    push_cast
    omega
  · simp only [νZ_append, eZ_append, hνB, heB, νZ_replicate, eZ_replicate, negZ, excZ]
    split_ifs <;> push_cast <;> omega

/-- **Arrhenius's sixth impossibility theorem fails as stated.** There is a
reflexive, transitive and complete population axiology that satisfies Egalitarian
Dominance, General Non-Extreme Priority, Non-Elitism, Weak Non-Sadism and Weak
Quality Addition, in their exact formulations. -/
theorem sixth_theorem_fails_as_stated :
    ∃ R : Axiology, (∀ X, R X X) ∧ Trans R ∧ (∀ X Y, R X Y ∨ R Y X) ∧
      EgalitarianDominance R ∧ GeneralNonExtremePriority R ∧ NonElitism R ∧
      WeakNonSadism R ∧ WeakQualityAddition R :=
  ⟨lex, lex_refl, lex_trans, lex_total, lex_egalitarianDominance,
    lex_generalNonExtremePriority, lex_nonElitism, lex_weakNonSadism,
    lex_weakQualityAddition⟩

/-! ### The strengthened condition fails

The axiology above does not contradict the repaired theorem: it violates the
strengthened form of Weak Quality Addition. Whatever negative level `x` and number
`m` are fixed in advance, a background population with enough excellent lives to
compensate `m` lives at `x` makes the comparison turn on total welfare, and then
enough lives at level `3` win. -/

theorem lex_not_strongQualityAddition : ¬ StrongQualityAddition lex := by
  rintro ⟨x, m, hx, -, h⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = m * (-x) :=
    ⟨m * (-x).toNat, by push_cast; rw [Int.toNat_of_nonneg (by omega)]⟩
  obtain ⟨u, v, y, n, hy, -, -, -, H⟩ := h (List.replicate k 4)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, n * u - m * x < N :=
    ⟨(n * u - m * x).toNat + 1, by
      have := Int.self_le_toNat (n * u - m * x)
      push_cast
      omega⟩
  have hB : Within 1 y (List.replicate N 3) := fun w hw => by
    rw [List.eq_of_mem_replicate hw]; omega
  have key := H u (List.replicate N 3) le_rfl hB
  rw [lex_pop] at key
  have hX4 : ∀ w ∈ List.replicate k (4 : ℤ), 4 ≤ w := fun w hw => by
    rw [List.eq_of_mem_replicate hw]
  have hνX := νZ_eq_zero (l := List.replicate k 4) fun w hw => by
    have := hX4 w hw; omega
  have heX := eZ_eq_length hX4
  have hν3 := νZ_eq_zero (l := List.replicate N 3) fun w hw => by
    rw [List.eq_of_mem_replicate hw]; omega
  have he3 := eZ_eq_zero (l := List.replicate N 3) fun w hw => by
    rw [List.eq_of_mem_replicate hw]; omega
  have hx4 : ¬ 4 ≤ x := by omega
  have hνC : νZ (List.replicate m x) = m * (-x) := by simp [νZ_replicate, negZ, hx]
  have heC : eZ (List.replicate m x) = 0 := by simp [eZ_replicate, excZ, hx4]
  have hcomp : νZ (List.replicate N 3 ++ List.replicate m x ++ List.replicate k 4) ≤
      eZ (List.replicate N 3 ++ List.replicate m x ++ List.replicate k 4) := by
    simp only [νZ_append, eZ_append, hν3, he3, hνC, heC, hνX, heX, List.length_replicate]
    omega
  rcases key with ⟨-, h2⟩ | ⟨-, hs⟩
  · exact h2 hcomp
  · simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul] at hs
    omega

/-- The axiology separates the two forms of Weak Quality Addition: it satisfies the
form Arrhenius states and violates the form his proof needs. -/
theorem weak_but_not_strong :
    ∃ R : Axiology, WeakQualityAddition R ∧ ¬ StrongQualityAddition R :=
  ⟨lex, lex_weakQualityAddition, lex_not_strongQualityAddition⟩

/-! ### Sanity check: the formal condition has teeth

Weak Quality Addition as formalised here is not vacuous: plain totalism, which
ranks populations by total welfare, violates it. -/

/-- Totalism: rank populations by total welfare. -/
def total : Axiology := fun X Y => Y.sum ≤ X.sum

theorem total_not_weakQualityAddition : ¬ WeakQualityAddition total := by
  intro h
  obtain ⟨x, u, v, y, n, m, -, hy, -, -, -, -, H⟩ := h []
  obtain ⟨N, hN⟩ : ∃ N : ℕ, n * u - m * x < N :=
    ⟨(n * u - m * x).toNat + 1, by
      have := Int.self_le_toNat (n * u - m * x)
      push_cast
      omega⟩
  have hB : Within 1 y (List.replicate N 3) := fun w hw => by
    rw [List.eq_of_mem_replicate hw]; omega
  have key := H u (List.replicate N 3) le_rfl hB
  simp only [total, sum_pop, Int.cast_le, List.sum_append, List.sum_replicate, nsmul_eq_mul,
    List.sum_nil, add_zero] at key
  omega

/-! ## Where the published proof fails

The proof derives two intermediate conditions (β and δ) from Non-Elitism and
General Non-Extreme Priority, and then claims, as Lemma 1.3, that Weak Quality
Addition and Condition δ imply the *Restricted Quality Addition Condition*.

Lemma 1.3 is false. Line (12) of its proof applies Weak Quality Addition to the
background population `A₁ ∪ X`, using the negative level and the numbers that were
chosen for `X`. The axiology `lex` satisfies both hypotheses of the lemma and
violates its conclusion. -/

/-- **Condition δ** (exact formulation). For any negative level `z` and any `m > 0`
there are a positive level `u`, a positive range `1..y` below `u`, and `n > 0` such
that `n` lives at any one level `x ≥ u` together with `m` lives at `z` are at least
as good as `n` lives in the range `1..y` together with `m` lives at level `3`,
whatever the rest of the population `E`. -/
def ConditionDelta (R : Axiology) : Prop :=
  ∀ (z : ℤ) (m : ℕ), z < 0 → 0 < m → ∃ (u y : ℤ) (n : ℕ), 3 ≤ y ∧ y < u ∧ 0 < n ∧
    ∀ (x : ℤ) (B E : List ℤ), u ≤ x → B.length = n → Within 1 y B →
      R (pop (List.replicate n x ++ List.replicate m z ++ E))
        (pop (B ++ List.replicate m 3 ++ E))

/-- **Restricted Quality Addition** (exact formulation). For any population `X`
there are a positive level `x`, a positive range `1..y` below `x`, and sizes `n`,
`m` such that adding `n` lives at any one level `z ≥ x` to `X` is at least as good
as adding any population in the range `1..y` of size at least `m`. -/
def RestrictedQualityAddition (R : Axiology) : Prop :=
  ∀ X : List ℤ, ∃ (x y : ℤ) (n m : ℕ), 3 ≤ y ∧ y < x ∧
    ∀ (z : ℤ) (B : List ℤ), x ≤ z → Within 1 y B → m ≤ B.length →
      R (pop (List.replicate n z ++ X)) (pop (B ++ X))

theorem lex_conditionDelta : ConditionDelta lex := by
  intro z m hz hm
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = 3 * m - m * z :=
    ⟨m * (3 - z).toNat, by push_cast; rw [Int.toNat_of_nonneg (by omega)]; ring⟩
  have hmz : (m : ℤ) * z ≤ -m := by nlinarith
  refine ⟨4, 3, n, le_rfl, by norm_num, by omega, ?_⟩
  intro x B E hx hB hw
  have hνB := νZ_eq_zero (l := B) fun w h => by have := hw w h; omega
  have heB := eZ_eq_zero (l := B) fun w h => by have := hw w h; omega
  have hsB := sum_le_three (l := B) fun w h => (hw w h).2
  rw [hB] at hsB
  have hA4 : ∀ w ∈ List.replicate n x, 4 ≤ w := fun w hw => by
    rw [List.eq_of_mem_replicate hw]; exact hx
  have hνA := νZ_eq_zero (l := List.replicate n x) fun w hw => by
    have := hA4 w hw; omega
  have heA := eZ_eq_length hA4
  have hz4 : ¬ 4 ≤ z := by omega
  have hνC : νZ (List.replicate m z) = -(m * z) := by simp [νZ_replicate, negZ, hz]
  have heC : eZ (List.replicate m z) = 0 := by simp [eZ_replicate, excZ, hz4]
  have hνD : νZ (List.replicate m 3) = 0 := by simp [νZ_replicate, negZ]
  have heD : eZ (List.replicate m 3) = 0 := by simp [eZ_replicate, excZ]
  have hnx : (n : ℤ) * 4 ≤ n * x := by nlinarith
  apply lex_pop_of
  · simp only [νZ_append, eZ_append, hνA, heA, hνB, heB, hνC, heC, hνD, heD,
      List.length_replicate]
    omega
  · simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul]
    omega

theorem lex_not_restrictedQualityAddition : ¬ RestrictedQualityAddition lex := by
  intro h
  obtain ⟨x, y, n, m, hy, -, H⟩ := h []
  obtain ⟨N, hN⟩ : ∃ N : ℕ, n * x < N ∧ (m : ℤ) ≤ N :=
    ⟨(n * x).toNat + m + 1, by
      have := Int.self_le_toNat (n * x)
      push_cast
      omega⟩
  have hmem : ∀ w ∈ List.replicate N (1 : ℤ), 1 ≤ w ∧ w ≤ y := fun w hw => by
    rw [List.eq_of_mem_replicate hw]; omega
  have key := H x (List.replicate N 1) le_rfl hmem (by simp; omega)
  rw [lex_pop] at key
  have hν := νZ_eq_zero (l := List.replicate N 1 ++ []) fun w hw => by
    have := hmem w (by simpa using hw); omega
  rcases key with ⟨-, h2⟩ | ⟨-, hs⟩
  · exact h2 (by rw [hν]; exact eZ_nonneg _)
  · simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul, List.sum_nil, add_zero,
      mul_one] at hs
    omega

/-- The failing step, at the empty background population. For `X = ∅` the axiology's
witnesses for Weak Quality Addition are one life at `-1` against one excellent life,
and its witness for Condition δ at that level is four excellent lives. Line (12)
then asserts that five lives at `4` are at least as good as four lives at `4`, two
at `3` and one at `-1`. They are not. -/
theorem line_12_fails : ¬ lex (pop [4, 4, 4, 4, 4]) (pop [4, 4, 4, 4, 3, 3, -1]) := by
  rw [lex_pop]
  decide

/-- **Lemma 1.3 of the published proof is false.** Weak Quality Addition and
Condition δ do not imply Restricted Quality Addition, even for a reflexive,
transitive and complete axiology. -/
theorem lemma_1_3_fails :
    ∃ R : Axiology, (∀ X, R X X) ∧ Trans R ∧ (∀ X Y, R X Y ∨ R Y X) ∧
      WeakQualityAddition R ∧ ConditionDelta R ∧ ¬ RestrictedQualityAddition R :=
  ⟨lex, lex_refl, lex_trans, lex_total, lex_weakQualityAddition, lex_conditionDelta,
    lex_not_restrictedQualityAddition⟩

end PopEthics.Sixth
