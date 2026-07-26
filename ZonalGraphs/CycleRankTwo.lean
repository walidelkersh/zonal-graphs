import ZonalGraphs.DutchWindmill

namespace ZonalGraphs

/-!
# Graphs of cycle rank two, type (1)

Theorem 3.1 of Bowling–Zhang, *Zonal Graphs of Small Cycle Rank* (2023), which is Theorem 3.2.1 of
Bowling's dissertation: a graph of cycle rank two and type (1) is zonal if and only if it is not
minimal.

A graph of cycle rank two has type (1) when it contains `C ⋆ C'`, two cycles identified at a single
vertex `u`, and every embedding of it has exactly three regions: one bounded by `C`, one by `C'`, and the
exterior bounded by the whole graph.  Minimal means the graph *is* `C ⋆ C'`, with nothing outside the two
cycles.

The minimal case is already settled: it is exactly `PlaneGraph.not_isZonal_of_isTwoBladedWindmill`, two
blades meeting at a hub whose union bounds the third region, so no zonal labeling exists.

The non-minimal case is proved here.  Writing `U` for the vertices outside `C ⋆ C'`, split the vertices
into four pairwise disjoint blocks `{u}`, `V(C) ∖ u`, `V(C') ∖ u` and `U`, and prescribe the label sums
`1`, `2`, `2`, `1`.  Then each cycle has value `1 + 2 = 0`, while the exterior has value
`(0 + 0 - 1) + 1 = 0`, the `-1` correcting for the shared vertex `u` being counted twice.  Only
nonemptiness of `U` is needed, which is precisely non-minimality.
-/

universe u v w

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face] [DecidableEq Vertex]

/-- A block with at least one vertex absorbs the flips needed to reach any nonzero target: a single
vertex needs at most one flip when the target is nonzero, and larger blocks have room for the at most
two flips that are ever required. -/
theorem val_sub_le_of_ne_zero (t : ZMod 3) (ht : t ≠ 0) (c : ℕ) (hc : 1 ≤ c) :
    (t - (c : ZMod 3)).val ≤ c := by
  rcases Nat.lt_or_ge c 2 with hsmall | hlarge
  · obtain rfl : c = 1 := by omega
    have hdec : ∀ s : ZMod 3, s ≠ 0 → (s - ((1 : ℕ) : ZMod 3)).val ≤ 1 := by decide
    exact hdec t ht
  · have := ZMod.val_lt (t - (c : ZMod 3))
    omega

/-- **The non-minimal case of Theorem 3.2.1.** A plane graph of cycle rank two and type (1) that is not
minimal is zonal.

The two cycles bound two of the three regions and meet exactly in `u`; `U` collects the vertices outside
both, and non-minimality says `U` is nonempty. -/
theorem isZonal_of_cycleRankTwo_typeOne (P : PlaneGraph Vertex Face) {R₁ R₂ R₃ : Face}
    {S₁ S₂ : Finset Vertex} {w : Vertex} (h₁ : P.boundary R₁ = S₁) (h₂ : P.boundary R₂ = S₂)
    (h₃ : P.boundary R₃ = Finset.univ) (hfaces : ∀ R : Face, R = R₁ ∨ R = R₂ ∨ R = R₃)
    (hmeet : S₁ ∩ S₂ = {w}) (hS₁ : 3 ≤ S₁.card) (hS₂ : 3 ≤ S₂.card)
    (hU : (Finset.univ \ (S₁ ∪ S₂)).Nonempty) : P.IsZonal := by
  have hwmem : w ∈ S₁ ∩ S₂ := hmeet ▸ Finset.mem_singleton_self w
  obtain ⟨hw₁, hw₂⟩ := Finset.mem_inter.mp hwmem
  set U : Finset Vertex := Finset.univ \ (S₁ ∪ S₂) with hUdef
  -- Four pairwise disjoint blocks with targets `1`, `2`, `2`, `1`.
  have hdisjoint : ∀ i j : Fin 4, i ≠ j →
      Disjoint (![{w}, S₁.erase w, S₂.erase w, U] i) (![{w}, S₁.erase w, S₂.erase w, U] j) := by
    have hwU : w ∉ U := by simp [hUdef, hw₁]
    have h₁₂ : Disjoint (S₁.erase w) (S₂.erase w) := by
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      have : x ∈ S₁ ∩ S₂ :=
        Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase hx₁, Finset.mem_of_mem_erase hx₂⟩
      exact Finset.ne_of_mem_erase hx₁ (Finset.mem_singleton.mp (hmeet ▸ this))
    have he₁ : Disjoint (S₁.erase w) U := by
      rw [Finset.disjoint_left]
      intro x hx hxU
      exact (Finset.mem_sdiff.mp hxU).2
        (Finset.mem_union_left _ (Finset.mem_of_mem_erase hx))
    have he₂ : Disjoint (S₂.erase w) U := by
      rw [Finset.disjoint_left]
      intro x hx hxU
      exact (Finset.mem_sdiff.mp hxU).2
        (Finset.mem_union_right _ (Finset.mem_of_mem_erase hx))
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [h₁₂.symm, Finset.disjoint_singleton_left, Finset.disjoint_singleton_right] <;>
      first
        | exact he₁.symm
        | exact he₂.symm
  have hfit : ∀ i : Fin 4,
      (((![1, 2, 2, 1] : Fin 4 → ZMod 3) i) -
          ((![{w}, S₁.erase w, S₂.erase w, U] i).card : ZMod 3)).val
        ≤ (![{w}, S₁.erase w, S₂.erase w, U] i).card := by
    have hcard₁ : 2 ≤ (S₁.erase w).card := by
      rw [Finset.card_erase_of_mem hw₁]; omega
    have hcard₂ : 2 ≤ (S₂.erase w).card := by
      rw [Finset.card_erase_of_mem hw₂]; omega
    intro i
    fin_cases i
    · simp
    · simpa using val_sub_le_of_ne_zero 2 (by decide) _ (by omega)
    · simpa using val_sub_le_of_ne_zero 2 (by decide) _ (by omega)
    · simpa using val_sub_le_of_ne_zero 1 (by decide) U.card (Finset.card_pos.mpr hU)
  obtain ⟨labeling, hsum⟩ :=
    exists_labeling_blockSum_eq ![{w}, S₁.erase w, S₂.erase w, U] hdisjoint ![1, 2, 2, 1] hfit
  have hw : (labeling w : ZMod 3) = 1 := by simpa using hsum 0
  have he₁ : (∑ v ∈ S₁.erase w, (labeling v : ZMod 3)) = 2 := by simpa using hsum 1
  have he₂ : (∑ v ∈ S₂.erase w, (labeling v : ZMod 3)) = 2 := by simpa using hsum 2
  have hUsum : (∑ v ∈ U, (labeling v : ZMod 3)) = 1 := by simpa using hsum 3
  -- Each cycle: the shared vertex plus the rest.
  have hcyc₁ : (∑ v ∈ S₁, (labeling v : ZMod 3)) = 0 := by
    rw [← Finset.add_sum_erase _ _ hw₁, hw, he₁]; decide
  have hcyc₂ : (∑ v ∈ S₂, (labeling v : ZMod 3)) = 0 := by
    rw [← Finset.add_sum_erase _ _ hw₂, hw, he₂]; decide
  -- The exterior: the union of the cycles, corrected for the doubly counted shared vertex, plus `U`.
  have hunion : (∑ v ∈ S₁ ∪ S₂, (labeling v : ZMod 3)) = -1 := by
    have hui := Finset.sum_union_inter (s₁ := S₁) (s₂ := S₂)
      (f := fun v => (labeling v : ZMod 3))
    rw [hmeet, Finset.sum_singleton, hw, hcyc₁, hcyc₂] at hui
    linear_combination hui
  have hall : (∑ v ∈ Finset.univ, (labeling v : ZMod 3)) = 0 := by
    have hsd := Finset.sum_sdiff (f := fun v => (labeling v : ZMod 3))
      (Finset.subset_univ (S₁ ∪ S₂))
    rw [← hUdef, hUsum, hunion] at hsd
    linear_combination -hsd
  refine ⟨labeling, fun R => ?_⟩
  rcases hfaces R with rfl | rfl | rfl
  · rw [zoneValue, h₁]; exact hcyc₁
  · rw [zoneValue, h₂]; exact hcyc₂
  · rw [zoneValue, h₃]; exact hall

/-- **The minimal case of Theorem 3.2.1.** A minimal plane graph of cycle rank two and type (1) is not
zonal.

Minimality says the two cycles exhaust the vertices, so the exterior boundary is their union while they
meet exactly in `w`.  That is the two-bladed windmill of Proposition 2.2.1: the two cycle regions force
the exterior to have value `-ℓ(w)`, which is nonzero. -/
theorem not_isZonal_of_cycleRankTwo_typeOne_minimal (P : PlaneGraph Vertex Face) {R₁ R₂ R₃ : Face}
    {S₁ S₂ : Finset Vertex} {w : Vertex} (h₁ : P.boundary R₁ = S₁) (h₂ : P.boundary R₂ = S₂)
    (h₃ : P.boundary R₃ = Finset.univ) (hmeet : S₁ ∩ S₂ = {w})
    (hminimal : S₁ ∪ S₂ = Finset.univ) : ¬P.IsZonal :=
  not_isZonal_of_isTwoBladedWindmill
    (P := P) (blade₁ := R₁) (blade₂ := R₂) (exterior := R₃) (hub := w)
    { boundary_union := by rw [h₃, h₁, h₂, hminimal]
      boundary_inter := by rw [h₁, h₂]; exact hmeet }

/-- **Theorem 3.2.1 (Bowling–Zhang, 2023).** A plane graph of cycle rank two and type (1) is zonal if
and only if it is not minimal, that is, if and only if some vertex lies outside the two cycles. -/
theorem isZonal_iff_not_minimal_cycleRankTwo_typeOne (P : PlaneGraph Vertex Face) {R₁ R₂ R₃ : Face}
    {S₁ S₂ : Finset Vertex} {w : Vertex} (h₁ : P.boundary R₁ = S₁) (h₂ : P.boundary R₂ = S₂)
    (h₃ : P.boundary R₃ = Finset.univ) (hfaces : ∀ R : Face, R = R₁ ∨ R = R₂ ∨ R = R₃)
    (hmeet : S₁ ∩ S₂ = {w}) (hS₁ : 3 ≤ S₁.card) (hS₂ : 3 ≤ S₂.card) :
    P.IsZonal ↔ S₁ ∪ S₂ ≠ Finset.univ := by
  refine ⟨fun hzonal hmin =>
      not_isZonal_of_cycleRankTwo_typeOne_minimal P h₁ h₂ h₃ hmeet hmin hzonal, fun hne => ?_⟩
  refine isZonal_of_cycleRankTwo_typeOne P h₁ h₂ h₃ hfaces hmeet hS₁ hS₂ ?_
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset,
    Finset.univ_subset_iff] at hempty
  exact hne hempty

end PlaneGraph

end ZonalGraphs
