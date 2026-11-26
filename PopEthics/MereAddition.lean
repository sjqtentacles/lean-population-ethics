import PopEthics.Basic

/-!
# The Mere Addition Paradox

Any transitive axiology that satisfies Mere Addition and Non-Anti-Egalitarianism
is committed to the Repugnant Conclusion (Parfit; in this form, Ng 1989).

The argument, for a population `A` of `n` people at level `h` and a low level `ε`:

* `A⁺` adds `k` people at a positive level `δ ≤ ε / 2` to `A`. By Mere Addition,
  `A⁺` is at least as good as `A`.
* `Z` has `n + k` people, all at level `ε`. For `k` large enough `Z` has a higher
  total than `A⁺`, so by Non-Anti-Egalitarianism `Z` is better than `A⁺`.
* By transitivity `Z` is better than `A`.
-/

namespace PopEthics

variable {R : Axiology}

theorem repugnantConclusion_of_mereAddition
    (htrans : Trans R) (hMA : MereAddition R) (hNAE : NonAntiEgalitarianism R) :
    RepugnantConclusion R := by
  intro n h ε hn hε
  -- A positive level for the added people, at most `ε / 2` and different from `h`
  -- (so that `A⁺` is genuinely unequal).
  obtain ⟨δ, hδ0, hδε, hδh⟩ : ∃ δ : ℚ, 0 < δ ∧ δ ≤ ε / 2 ∧ δ ≠ h := by
    by_cases hh : h = ε / 2
    · exact ⟨ε / 3, by positivity, by linarith, by rw [hh]; intro h3; linarith⟩
    · exact ⟨ε / 2, by positivity, le_rfl, fun h' => hh h'.symm⟩
  -- Enough added people for the equalised population to have the higher total.
  obtain ⟨k, hk⟩ := exists_nat_gt (max (2 * n * (h - ε) / ε) 0)
  have hk0 : (0 : ℚ) < k := lt_of_le_of_lt (le_max_right _ _) hk
  have hk1 : 2 * n * (h - ε) / ε < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hkey : n * (h - ε) < k * (ε / 2) := by
    rw [div_lt_iff₀ hε] at hk1
    linarith
  have hkpos : 0 < k := Nat.cast_pos.1 hk0
  let Aplus : Population := equalPop n h + equalPop k δ
  have hcard : Aplus.card = n + k := by simp [Aplus]
  have hsum : Aplus.sum = n * h + k * δ := by simp [Aplus, Multiset.sum_replicate]
  have hunequal : Unequal Aplus :=
    ⟨h, Multiset.mem_add.2 (Or.inl (Multiset.mem_replicate.2 ⟨hn.ne', rfl⟩)),
      δ, Multiset.mem_add.2 (Or.inr (Multiset.mem_replicate.2 ⟨hkpos.ne', rfl⟩)),
      hδh.symm⟩
  -- Step 1: Mere Addition.
  have h1 : R Aplus (equalPop n h) :=
    hMA _ _ fun w hw => by rw [Multiset.eq_of_mem_replicate hw]; exact hδ0
  -- Step 2: Non-Anti-Egalitarianism.
  have h2 : Better R (equalPop (n + k) ε) Aplus := by
    have hlt : Aplus.sum < Aplus.card * ε := by
      rw [hsum, hcard]
      push_cast
      nlinarith [mul_nonneg hk0.le (sub_nonneg.2 hδε)]
    have := hNAE Aplus ε hunequal hlt
    rwa [hcard] at this
  -- Step 3: transitivity.
  exact ⟨n + k, by omega, htrans _ _ _ h2.1 h1, fun h3 => h2.2 (htrans _ _ _ h1 h3)⟩

end PopEthics
