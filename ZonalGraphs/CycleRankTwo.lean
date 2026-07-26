import ZonalGraphs.BoundaryDifference
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

/-- A block absorbs the flips needed to reach the target `0` exactly when it is not a single vertex: an
empty block needs none, a block of two or more has room, but one vertex would need two flips. -/
theorem val_neg_le_of_ne_one {c : ℕ} (hc : c ≠ 1) : ((0 : ZMod 3) - (c : ZMod 3)).val ≤ c := by
  rcases Nat.lt_or_ge c 2 with hsmall | hlarge
  · obtain rfl : c = 0 := by omega
    decide
  · have := ZMod.val_lt ((0 : ZMod 3) - (c : ZMod 3))
    omega

/-- Splitting the total label sum of a type (2) graph over its two cycles and the vertices lying on no
cycle. -/
theorem sum_univ_eq_of_cover {S₁ S₂ W : Finset Vertex} (hd₁₂ : Disjoint S₁ S₂)
    (hd₁W : Disjoint S₁ W) (hd₂W : Disjoint S₂ W) (hcover : S₁ ∪ S₂ ∪ W = Finset.univ)
    (labeling : VertexLabeling Vertex) :
    (∑ v ∈ Finset.univ, (labeling v : ZMod 3))
      = (∑ v ∈ S₁, (labeling v : ZMod 3)) + (∑ v ∈ S₂, (labeling v : ZMod 3))
        + ∑ v ∈ W, (labeling v : ZMod 3) := by
  rw [← hcover, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hd₁W, hd₂W⟩),
    Finset.sum_union hd₁₂]

/-- **Theorem 3.2.3 (Bowling–Zhang, 2023).** A plane graph of cycle rank two and type (2) is zonal if and
only if either every vertex lies on a cycle or at least two vertices lie on no cycle.

Type (2) means the graph contains two *disjoint* cycles joined by a path, so its three regions are
bounded by the two cycles and by the whole graph.  Writing `W` for the vertices on no cycle, both cycle
regions can be made to vanish and the exterior value is then exactly the sum over `W`.  That sum can be
made zero precisely when `W` is not a single vertex — empty needs nothing, two or more can be balanced,
but one vertex contributes its own nonzero label.

The shape of the argument is the same as for unicyclic graphs in Theorem 3.1.1: the obstruction is always
a lone vertex off the cycles. -/
theorem isZonal_iff_card_ne_one_cycleRankTwo_typeTwo (P : PlaneGraph Vertex Face) {R₁ R₂ R₃ : Face}
    {S₁ S₂ W : Finset Vertex} (h₁ : P.boundary R₁ = S₁) (h₂ : P.boundary R₂ = S₂)
    (h₃ : P.boundary R₃ = Finset.univ) (hfaces : ∀ R : Face, R = R₁ ∨ R = R₂ ∨ R = R₃)
    (hd₁₂ : Disjoint S₁ S₂) (hd₁W : Disjoint S₁ W) (hd₂W : Disjoint S₂ W)
    (hcover : S₁ ∪ S₂ ∪ W = Finset.univ) (hS₁ : 3 ≤ S₁.card) (hS₂ : 3 ≤ S₂.card) :
    P.IsZonal ↔ W.card ≠ 1 := by
  constructor
  · -- A lone vertex off the cycles is the whole obstruction.
    rintro ⟨labeling, hlabeling⟩ hone
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
    have hv₁ : (∑ v ∈ S₁, (labeling v : ZMod 3)) = 0 := by
      have h := hlabeling R₁; rwa [zoneValue, h₁] at h
    have hv₂ : (∑ v ∈ S₂, (labeling v : ZMod 3)) = 0 := by
      have h := hlabeling R₂; rwa [zoneValue, h₂] at h
    have hv₃ : (∑ v ∈ Finset.univ, (labeling v : ZMod 3)) = 0 := by
      have h := hlabeling R₃; rwa [zoneValue, h₃] at h
    have hsplit := sum_univ_eq_of_cover hd₁₂ hd₁W hd₂W hcover labeling
    rw [hx, Finset.sum_singleton, hv₁, hv₂, hv₃] at hsplit
    exact (labeling x).2 (by linear_combination -hsplit)
  · intro hne
    have hdisjoint : ∀ i j : Fin 3, i ≠ j →
        Disjoint (![S₁, S₂, W] i) (![S₁, S₂, W] j) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [hd₁₂.symm, hd₁W.symm, hd₂W.symm]
    have hfit : ∀ i : Fin 3,
        (((![0, 0, 0] : Fin 3 → ZMod 3) i) - ((![S₁, S₂, W] i).card : ZMod 3)).val
          ≤ (![S₁, S₂, W] i).card := by
      intro i
      fin_cases i
      · simpa using val_neg_le_of_ne_one (c := S₁.card) (by omega)
      · simpa using val_neg_le_of_ne_one (c := S₂.card) (by omega)
      · simpa using val_neg_le_of_ne_one hne
    obtain ⟨labeling, hsum⟩ :=
      exists_labeling_blockSum_eq ![S₁, S₂, W] hdisjoint ![0, 0, 0] hfit
    have hc₁ : (∑ v ∈ S₁, (labeling v : ZMod 3)) = 0 := by simpa using hsum 0
    have hc₂ : (∑ v ∈ S₂, (labeling v : ZMod 3)) = 0 := by simpa using hsum 1
    have hcW : (∑ v ∈ W, (labeling v : ZMod 3)) = 0 := by simpa using hsum 2
    refine ⟨labeling, fun R => ?_⟩
    rcases hfaces R with rfl | rfl | rfl
    · rw [zoneValue, h₁]; exact hc₁
    · rw [zoneValue, h₂]; exact hc₂
    · rw [zoneValue, h₃, sum_univ_eq_of_cover hd₁₂ hd₁W hd₂W hcover, hc₁, hc₂, hcW]
      decide

/-- **The non-zonal case of Theorem 3.3 (Bowling–Zhang, 2023).** A minimal plane graph of cycle rank two
and type (3) with `(n₁, n₂) = (2, 3)` is not zonal.

Type (3) consists of three internally disjoint `u`–`v` paths `P₁, P₂, P₃`, and the three regions are
bounded by the three pairs of paths.  With `n₁ = 2` the first path is the edge `uv` alone, so it has no
interior vertex and the region bounded by `P₁` and `P₃` has boundary `{u, v} ∪ Q₃`.  With `n₂ = 3` the
middle path has exactly one interior vertex `w`, so the region bounded by `P₂` and `P₃` has boundary that
same set with `w` adjoined.

Two regions differing by one vertex cannot both vanish, so the whole case is one application of
`not_isZonal_of_boundary_insert`. -/
theorem not_isZonal_of_cycleRankTwo_typeThree_minimal (P : PlaneGraph Vertex Face) {R₂ R₃ : Face}
    {T Q₃ : Finset Vertex} {w : Vertex} (h₂ : P.boundary R₂ = insert w (T ∪ Q₃))
    (h₃ : P.boundary R₃ = T ∪ Q₃) (hw : w ∉ T ∪ Q₃) : ¬P.IsZonal :=
  P.not_isZonal_of_boundary_insert h₃ h₂ hw

/-- **Zonality of a type (3) graph from prescribed block sums.**

Type (3) has three internally disjoint `u`–`v` paths, so with `T = {u, v}` and `Qᵢ` the interior of the
`i`-th path, the three regions are bounded by `T ∪ Qᵢ ∪ Qⱼ` for the three pairs.  Prescribing a sum for
each of the four blocks makes every region value a sum of three of the four prescribed values, so the
three equations `t T + t Qᵢ + t Qⱼ = 0` suffice.

Both cases of Theorem 3.3 use a *constant* assignment: all four blocks get `0`, or all four get `1`.  The
three equations then read `0 + 0 + 0 = 0` and `1 + 1 + 1 = 0` respectively. -/
theorem isZonal_of_theta_blocks (P : PlaneGraph Vertex Face) {R₁ R₂ R₃ : Face}
    {T Q₁ Q₂ Q₃ : Finset Vertex} (h₁ : P.boundary R₁ = T ∪ Q₁ ∪ Q₂)
    (h₂ : P.boundary R₂ = T ∪ Q₂ ∪ Q₃) (h₃ : P.boundary R₃ = T ∪ Q₁ ∪ Q₃)
    (hfaces : ∀ R : Face, R = R₁ ∨ R = R₂ ∨ R = R₃)
    (hdT₁ : Disjoint T Q₁) (hdT₂ : Disjoint T Q₂) (hdT₃ : Disjoint T Q₃)
    (hd₁₂ : Disjoint Q₁ Q₂) (hd₁₃ : Disjoint Q₁ Q₃) (hd₂₃ : Disjoint Q₂ Q₃)
    (t : ZMod 3) (hthree : t + t + t = 0)
    (hfitT : (t - (T.card : ZMod 3)).val ≤ T.card)
    (hfit₁ : (t - (Q₁.card : ZMod 3)).val ≤ Q₁.card)
    (hfit₂ : (t - (Q₂.card : ZMod 3)).val ≤ Q₂.card)
    (hfit₃ : (t - (Q₃.card : ZMod 3)).val ≤ Q₃.card) : P.IsZonal := by
  have hdisjoint : ∀ i j : Fin 4, i ≠ j →
      Disjoint (![T, Q₁, Q₂, Q₃] i) (![T, Q₁, Q₂, Q₃] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] <;>
      first
        | exact absurd rfl hij
        | exact hdT₁ | exact hdT₂ | exact hdT₃
        | exact hd₁₂ | exact hd₁₃ | exact hd₂₃
        | exact hdT₁.symm | exact hdT₂.symm | exact hdT₃.symm
        | exact hd₁₂.symm | exact hd₁₃.symm | exact hd₂₃.symm
  obtain ⟨labeling, hsum⟩ :=
    exists_labeling_blockSum_eq ![T, Q₁, Q₂, Q₃] hdisjoint (fun _ => t) (by
      intro i
      fin_cases i <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons] <;>
        first
          | exact hfitT | exact hfit₁ | exact hfit₂ | exact hfit₃)
  have hT : (∑ v ∈ T, (labeling v : ZMod 3)) = t := by simpa using hsum 0
  have hv₁ : (∑ v ∈ Q₁, (labeling v : ZMod 3)) = t := by simpa using hsum 1
  have hv₂ : (∑ v ∈ Q₂, (labeling v : ZMod 3)) = t := by simpa using hsum 2
  have hv₃ : (∑ v ∈ Q₃, (labeling v : ZMod 3)) = t := by simpa using hsum 3
  -- Each region boundary is a disjoint union of three of the four blocks.
  have hsplit : ∀ A B : Finset Vertex, Disjoint T A → Disjoint T B → Disjoint A B →
      (∑ v ∈ T ∪ A ∪ B, (labeling v : ZMod 3))
        = (∑ v ∈ T, (labeling v : ZMod 3)) + (∑ v ∈ A, (labeling v : ZMod 3))
          + ∑ v ∈ B, (labeling v : ZMod 3) := by
    intro A B hTA hTB hAB
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hTB, hAB⟩), Finset.sum_union hTA]
  refine ⟨labeling, fun R => ?_⟩
  rcases hfaces R with rfl | rfl | rfl
  · rw [zoneValue, h₁, hsplit Q₁ Q₂ hdT₁ hdT₂ hd₁₂, hT, hv₁, hv₂]; exact hthree
  · rw [zoneValue, h₂, hsplit Q₂ Q₃ hdT₂ hdT₃ hd₂₃, hT, hv₂, hv₃]; exact hthree
  · rw [zoneValue, h₃, hsplit Q₁ Q₃ hdT₁ hdT₃ hd₁₃, hT, hv₁, hv₃]; exact hthree

end PlaneGraph

end ZonalGraphs
