import PopEthics.Basic

/-!
# Ground instances of the adequacy conditions

The SAT search works with populations over integer welfare levels. `pop l` is the
population with the integer levels in the list `l`. Each lemma below states one
ground instance of a general condition in terms of `pop`, with side conditions that
are decidable statements about integer lists. A solver certificate is a list of such
instances whose conjunction is propositionally contradictory.
-/

namespace PopEthics

/-- The population with the given integer welfare levels. -/
def pop (l : List ℤ) : Population := ((l.map fun z : ℤ => (z : ℚ) : List ℚ) : Multiset ℚ)

theorem pop_perm {a b : List ℤ} (h : a.Perm b) : pop a = pop b :=
  Multiset.coe_eq_coe.2 (h.map _)

theorem pop_append (a b : List ℤ) : pop a + pop b = pop (a ++ b) := by
  simp [pop]

theorem pop_cons (z : ℤ) (l : List ℤ) : pop (z :: l) = (z : ℚ) ::ₘ pop l :=
  rfl

theorem pop_replicate (n : ℕ) (w : ℤ) : pop (List.replicate n w) = equalPop n (w : ℚ) := by
  simp only [pop, List.map_replicate]
  exact Multiset.coe_replicate n _

theorem mem_pop {l : List ℤ} {q : ℚ} : q ∈ pop l ↔ ∃ z ∈ l, (z : ℚ) = q := by
  simp [pop]

theorem card_pop (l : List ℤ) : (pop l).card = l.length := by
  simp [pop]

theorem sum_pop (l : List ℤ) : (pop l).sum = ((l.sum : ℤ) : ℚ) := by
  simp [pop, Int.cast_list_sum]

variable {R : Axiology}

theorem Trans.inst (h : Trans R) (a b c : List ℤ) :
    R (pop a) (pop b) → R (pop b) (pop c) → R (pop a) (pop c) :=
  h _ _ _

theorem MereAddition.inst (h : MereAddition R) (a b c : List ℤ)
    (hb : ∀ w ∈ b, 0 < w) (hc : (a ++ b).Perm c) : R (pop c) (pop a) := by
  rw [← pop_perm hc, ← pop_append]
  refine h _ _ fun w hw => ?_
  obtain ⟨z, hz, rfl⟩ := mem_pop.1 hw
  exact_mod_cast hb z hz

theorem NonAntiEgalitarianism.inst (h : NonAntiEgalitarianism R) (a e : List ℤ) (w : ℤ)
    (hu : ∃ x ∈ a, ∃ y ∈ a, x ≠ y) (hlt : a.sum < a.length * w)
    (he : e = List.replicate a.length w) :
    R (pop e) (pop a) ∧ ¬ R (pop a) (pop e) := by
  subst he
  have hU : Unequal (pop a) := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hu
    exact ⟨x, mem_pop.2 ⟨x, hx, rfl⟩, y, mem_pop.2 ⟨y, hy, rfl⟩, by exact_mod_cast hxy⟩
  have key := h (pop a) w hU (by rw [sum_pop, card_pop]; exact_mod_cast hlt)
  rw [card_pop, ← pop_replicate] at key
  exact key

theorem AvoidsRepugnance.inst {n : ℕ} {h ε : ℚ} (hA : AvoidsRepugnance R n h ε)
    (hi lo : ℤ) (z t : List ℤ) (m : ℕ)
    (hh : (hi : ℚ) = h) (hε : (lo : ℚ) = ε) (hm : 0 < m)
    (hz : z = List.replicate m lo) (ht : t = List.replicate n hi) :
    ¬ (R (pop z) (pop t) ∧ ¬ R (pop t) (pop z)) := by
  subst hz ht hh hε
  rw [pop_replicate, pop_replicate]
  exact hA m hm

theorem Dominance.inst (h : Dominance R) (a b : List ℤ)
    (hlen : a.length = b.length) (hge : ∀ p ∈ a.zip b, p.2 ≤ p.1) (hne : a ≠ b) :
    R (pop a) (pop b) ∧ ¬ R (pop b) (pop a) := by
  refine h _ _ ?_ ?_
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_iff_zip]
    exact ⟨hlen, fun {x y} hxy => by exact_mod_cast hge (x, y) hxy⟩
  · intro heq
    exact hne (List.map_injective_iff.2 Int.cast_injective heq)

theorem PigouDalton.inst (h : PigouDalton R) (x before after : List ℤ) (hi lo d : ℤ)
    (hd : 0 < d) (hle : lo + d ≤ hi - d)
    (hb : (x ++ [hi, lo]).Perm before) (ha : (x ++ [hi - d, lo + d]).Perm after) :
    R (pop after) (pop before) := by
  rw [← pop_perm hb, ← pop_perm ha, ← pop_append, ← pop_append]
  have key := h (pop x) hi lo d (by exact_mod_cast hd) (by exact_mod_cast hle)
  have e1 : pop [hi - d, lo + d] = ({(hi : ℚ) - d, (lo : ℚ) + d} : Multiset ℚ) := by
    simp only [pop, List.map, Int.cast_sub, Int.cast_add]
    rfl
  have e2 : pop [hi, lo] = ({(hi : ℚ), (lo : ℚ)} : Multiset ℚ) := rfl
  rw [e1, e2]
  exact key

theorem NonElitism.inst {m : ℕ} {s : ℚ} (h : NonElitism R m s) (si : ℤ)
    (x equal elite : List ℤ) (b c : ℤ)
    (hs : (si : ℚ) = s) (hcb : c < b) (hx : ∀ w ∈ x, c ≤ w ∧ w ≤ b + si)
    (he : (x ++ List.replicate (m + 1) b).Perm equal)
    (hl : (x ++ (b + si) :: List.replicate m c).Perm elite) :
    R (pop equal) (pop elite) := by
  subst hs
  rw [← pop_perm he, ← pop_perm hl, ← pop_append, ← pop_append]
  have key := h (pop x) b c (by exact_mod_cast hcb) fun w hw => by
    obtain ⟨z, hz, rfl⟩ := mem_pop.1 hw
    exact_mod_cast hx z hz
  rw [pop_cons, pop_replicate, pop_replicate, Int.cast_add]
  exact key

end PopEthics
