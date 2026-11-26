import PopEthics.MereAddition

/-!
# Two reference axiologies

* **Totalism** ranks populations by total welfare. It satisfies every premise of the
  Mere Addition Paradox, so the premises are jointly consistent, and it accepts the
  Repugnant Conclusion.
* **Averagism** ranks populations by average welfare. It avoids the Repugnant
  Conclusion, and the price is Mere Addition.

These are the first two entries in the map of which conditions can hold together.
-/

namespace PopEthics

/-! ## Totalism -/

/-- Totalism: `A` is at least as good as `B` when its total welfare is at least as high. -/
def totalism : Axiology := fun A B => B.sum ≤ A.sum

theorem totalism_trans : Trans totalism :=
  fun _ _ _ h1 h2 => le_trans h2 h1

theorem totalism_mereAddition : MereAddition totalism := by
  intro A B hB
  have hnonneg : 0 ≤ B.sum := Multiset.sum_nonneg fun w hw => (hB w hw).le
  simp only [totalism, Multiset.sum_add]
  linarith

theorem totalism_nonAntiEgalitarianism : NonAntiEgalitarianism totalism := by
  intro A w _ hlt
  have hsum : (equalPop A.card w).sum = A.card * w := by
    simp [Multiset.sum_replicate]
  refine ⟨?_, ?_⟩
  · change A.sum ≤ (equalPop A.card w).sum
    rw [hsum]; exact hlt.le
  · change ¬ (equalPop A.card w).sum ≤ A.sum
    rw [hsum]; exact not_le.2 hlt

/-- Totalism accepts the Repugnant Conclusion. -/
theorem totalism_repugnantConclusion : RepugnantConclusion totalism :=
  repugnantConclusion_of_mereAddition totalism_trans totalism_mereAddition
    totalism_nonAntiEgalitarianism

/-! ## Averagism -/

/-- Average welfare, with the empty population assigned `0`. -/
def average (A : Population) : ℚ := A.sum / A.card

/-- Averagism: `A` is at least as good as `B` when its average welfare is at least as high. -/
def averagism : Axiology := fun A B => average B ≤ average A

theorem averagism_trans : Trans averagism :=
  fun _ _ _ h1 h2 => le_trans h2 h1

/-- Averagism violates Mere Addition: adding one person at level `1` to one person
at level `10` lowers the average. -/
theorem averagism_not_mereAddition : ¬ MereAddition averagism := by
  intro h
  have := h {10} {1} (by simp)
  norm_num [averagism, average] at this

/-- Averagism avoids the Repugnant Conclusion: no population of people at level `1`
is better than one person at level `10`. -/
theorem averagism_not_repugnantConclusion : ¬ RepugnantConclusion averagism := by
  intro h
  obtain ⟨m, hpos, hm, -⟩ := h 1 10 1 one_pos one_pos
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  norm_num [averagism, average, Multiset.sum_replicate, hm'] at hm

end PopEthics
