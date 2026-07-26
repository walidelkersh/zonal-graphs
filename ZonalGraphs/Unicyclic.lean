import ZonalGraphs.DutchWindmill

namespace ZonalGraphs

/-!
# Unicyclic plane graphs

Theorem 2.3 of Bowling–Zhang, *Zonal Graphs of Small Cycle Rank* (2023), which is Theorem 3.1.1 of
Bowling's dissertation: a unicyclic graph `G` is zonal if and only if `G ≠ C ⋆ K₂` for every cycle `C`,
where `C ⋆ K₂` is the cycle with a single pendant edge attached.

A unicyclic plane graph has exactly two regions: one bounded by the cycle `C`, the other by the whole
graph.  Writing `S = V(C)`, the value of the first region is the label sum over `S` and the value of the
second is the sum over all vertices, so the two values differ by the sum over `V(G) \ S` — the vertices
off the cycle.  Zonality therefore forces that sum to vanish, and it can vanish exactly when the number
of off-cycle vertices is not one: none at all gives an empty sum, two or more can be balanced by
Lemma 2.0.4, but a single vertex contributes its own label, which is nonzero.

The case of exactly one off-cycle vertex is `G = C ⋆ K₂`, and that direction is proved here as
`PlaneGraph.not_isZonal_of_card_sdiff_boundary_eq_one`.  It needs no construction, only the two region
values, and it is the direction that does the work in the characterization.
-/

universe u v

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face] [DecidableEq Vertex]

/-- **The non-zonal half of Theorem 3.1.1.** A plane graph carrying a region bounded by `S` and a region
bounded by every vertex is not zonal when exactly one vertex lies outside `S`.

For a unicyclic graph, `S` is the vertex set of the cycle and the hypothesis says `G = C ⋆ K₂`: the
cycle bounds a region of value zero, so the other region has value `ℓ(u)` for the pendant vertex `u`,
and zonal labels are nonzero. -/
theorem not_isZonal_of_card_sdiff_boundary_eq_one (P : PlaneGraph Vertex Face) {R₁ R₂ : Face}
    {S : Finset Vertex} (h₁ : P.boundary R₁ = S) (h₂ : P.boundary R₂ = Finset.univ)
    (hcard : (Finset.univ \ S).card = 1) : ¬P.IsZonal := by
  rintro ⟨labeling, hlabeling⟩
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard
  have hcycle : (∑ v ∈ S, (labeling v : ZMod 3)) = 0 := h₁ ▸ hlabeling R₁
  have hall : (∑ v ∈ Finset.univ, (labeling v : ZMod 3)) = 0 := h₂ ▸ hlabeling R₂
  have hsplit : (∑ v ∈ Finset.univ \ S, (labeling v : ZMod 3)) + ∑ v ∈ S, (labeling v : ZMod 3)
      = ∑ v ∈ Finset.univ, (labeling v : ZMod 3) :=
    Finset.sum_sdiff (Finset.subset_univ S)
  rw [hu, Finset.sum_singleton, hcycle, hall, add_zero] at hsplit
  exact (labeling u).2 hsplit

/-- Restated for a plane graph with exactly two regions, which is the shape of a unicyclic embedding:
the region bounded by the cycle and the region bounded by the whole graph. -/
theorem not_isZonal_of_unicyclicLike (P : PlaneGraph Vertex Face) (R₁ R₂ : Face)
    (hpendant : (Finset.univ \ P.boundary R₁).card = 1)
    (hall : P.boundary R₂ = Finset.univ) : ¬P.IsZonal :=
  P.not_isZonal_of_card_sdiff_boundary_eq_one rfl hall hpendant

/-- **Prescribing the label sums on a set and on its complement.**

Both sums can be made to vanish exactly when neither block is a single vertex: label everything `1`, then
flip `(-|B|).val ≤ 2` vertices inside each block `B` from `1` to `2`, each flip raising that block's sum
by one.  A block needs at least as many vertices as the flips it must absorb, and `(-|B|).val ≤ 2` fails
to fit only when `|B| = 1`, since then one flip too many is required.  An empty block already sums to
zero and needs none.

This is the construction behind the zonal direction of Theorem 3.1.1. -/
theorem exists_labeling_sum_eq_zero_on_and_off (S : Finset Vertex) (hS : S.card ≠ 1)
    (hcompl : (Finset.univ \ S).card ≠ 1) :
    ∃ labeling : VertexLabeling Vertex,
      (∑ v ∈ S, (labeling v : ZMod 3)) = 0 ∧
        (∑ v ∈ Finset.univ \ S, (labeling v : ZMod 3)) = 0 := by
  -- The number of flips each block must absorb fits inside it.
  have hfit : ∀ B : Finset Vertex, B.card ≠ 1 → (-(B.card : ZMod 3)).val ≤ B.card := by
    intro B hB
    have hlt := ZMod.val_lt (-(B.card : ZMod 3))
    rcases Nat.lt_or_ge B.card 2 with hsmall | hlarge
    · interval_cases h : B.card
      · simp
      · omega
    · omega
  obtain ⟨F₁, hF₁sub, hF₁card⟩ := Finset.exists_subset_card_eq (hfit S hS)
  obtain ⟨F₂, hF₂sub, hF₂card⟩ := Finset.exists_subset_card_eq (hfit _ hcompl)
  refine ⟨flipLabeling (F₁ ∪ F₂), ?_, ?_⟩
  · rw [sum_flipLabeling, show S ∩ (F₁ ∪ F₂) = F₁ from ?_, hF₁card, ZMod.natCast_zmod_val]
    · ring
    · rw [Finset.inter_union_distrib_left, Finset.inter_eq_right.mpr hF₁sub,
        Finset.eq_empty_of_forall_notMem fun x hx => absurd
          (Finset.mem_sdiff.mp (hF₂sub (Finset.mem_inter.mp hx).2)).2
          (not_not.mpr (Finset.mem_inter.mp hx).1),
        Finset.union_empty]
  · rw [sum_flipLabeling, show Finset.univ \ S ∩ (F₁ ∪ F₂) = F₂ from ?_, hF₂card,
      ZMod.natCast_zmod_val]
    · ring
    · rw [Finset.inter_union_distrib_left, Finset.inter_eq_right.mpr hF₂sub,
        Finset.eq_empty_of_forall_notMem fun x hx => absurd
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).1).2
          (not_not.mpr (hF₁sub (Finset.mem_inter.mp hx).2)),
        Finset.empty_union]

/-- **Theorem 3.1.1 (Bowling–Zhang, 2023).** A unicyclic graph is zonal if and only if it is not
`C ⋆ K₂`, a cycle with a single pendant edge.

A unicyclic plane graph has two regions, one bounded by the cycle's vertex set `S` and one by every
vertex.  Both region values vanish for some labeling exactly when neither `S` nor its complement is a
single vertex; as `S` is a cycle it has at least three vertices, so the condition reduces to the
complement — the vertices off the cycle — not being a single vertex, which is exactly `G ≠ C ⋆ K₂`. -/
theorem isZonal_iff_card_sdiff_boundary_ne_one (P : PlaneGraph Vertex Face) {R₁ R₂ : Face}
    {S : Finset Vertex} (h₁ : P.boundary R₁ = S) (h₂ : P.boundary R₂ = Finset.univ)
    (hS : S.card ≠ 1) (hfaces : ∀ R : Face, R = R₁ ∨ R = R₂) :
    P.IsZonal ↔ (Finset.univ \ S).card ≠ 1 := by
  refine ⟨fun hzonal hone => P.not_isZonal_of_card_sdiff_boundary_eq_one h₁ h₂ hone hzonal,
    fun hne => ?_⟩
  obtain ⟨labeling, hon, hoff⟩ := exists_labeling_sum_eq_zero_on_and_off S hS hne
  refine ⟨labeling, fun R => ?_⟩
  rcases hfaces R with rfl | rfl
  · rw [zoneValue, h₁]; exact hon
  · rw [zoneValue, h₂, ← Finset.sum_sdiff (Finset.subset_univ S), hon, hoff, add_zero]

/-- **Theorem 3.1.3 (Bowling–Zhang, 2023).** Every zonal unicyclic graph is absolutely zonal: each of
its planar embeddings is zonal.

This is Proposition 2.4 of *Zonal Graphs of Small Cycle Rank*.  In an arbitrary planar embedding the two
regions have boundaries `S ∪ U₁` and `S ∪ U₂`, where `S` is the cycle and the off-cycle vertices split as
`U₁`, `U₂` according to which region their tree hangs into.  Give the cycle the sum `1` and each `Uᵢ` the
sum `2`; both region values are then `1 + 2 = 0`.

Only nonemptiness of each `Uᵢ` is needed, since one vertex already absorbs the single flip required to
reach the target `2`.  That is the sense in which zonality is embedding-independent here: the previous
theorem's exceptional case, one vertex off the cycle, cannot split into two nonempty parts. -/
theorem isZonal_of_boundary_eq_union (P : PlaneGraph Vertex Face) {R₁ R₂ : Face}
    {S U₁ U₂ : Finset Vertex} (h₁ : P.boundary R₁ = S ∪ U₁) (h₂ : P.boundary R₂ = S ∪ U₂)
    (hfaces : ∀ R : Face, R = R₁ ∨ R = R₂)
    (hSU₁ : Disjoint S U₁) (hSU₂ : Disjoint S U₂) (hU : Disjoint U₁ U₂)
    (hScard : 2 ≤ S.card) (hU₁ : U₁.Nonempty) (hU₂ : U₂.Nonempty) : P.IsZonal := by
  -- Three pairwise disjoint blocks, with targets `1`, `2`, `2`.
  have hfitTwo : ∀ c : ℕ, 1 ≤ c → ((2 : ZMod 3) - (c : ZMod 3)).val ≤ c := by
    intro c hc
    rcases Nat.lt_or_ge c 2 with hsmall | hlarge
    · obtain rfl : c = 1 := by omega
      decide
    · have := ZMod.val_lt ((2 : ZMod 3) - (c : ZMod 3))
      omega
  have hfitAny : ∀ (t : ZMod 3) (c : ℕ), 2 ≤ c → (t - (c : ZMod 3)).val ≤ c := by
    intro t c hc
    have := ZMod.val_lt (t - (c : ZMod 3))
    omega
  have hdisjoint : ∀ i j : Fin 3, i ≠ j → Disjoint (![S, U₁, U₂] i) (![S, U₁, U₂] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hSU₁.symm, hSU₂.symm, hU.symm]
  have hfit : ∀ i : Fin 3,
      (((![1, 2, 2] : Fin 3 → ZMod 3) i) - ((![S, U₁, U₂] i).card : ZMod 3)).val
        ≤ (![S, U₁, U₂] i).card := by
    intro i
    fin_cases i
    · simpa using hfitAny 1 S.card hScard
    · simpa using hfitTwo U₁.card (Finset.card_pos.mpr hU₁)
    · simpa using hfitTwo U₂.card (Finset.card_pos.mpr hU₂)
  obtain ⟨labeling, hsum⟩ :=
    exists_labeling_blockSum_eq ![S, U₁, U₂] hdisjoint ![1, 2, 2] hfit
  have hS : (∑ v ∈ S, (labeling v : ZMod 3)) = 1 := by simpa using hsum 0
  have hV₁ : (∑ v ∈ U₁, (labeling v : ZMod 3)) = 2 := by simpa using hsum 1
  have hV₂ : (∑ v ∈ U₂, (labeling v : ZMod 3)) = 2 := by simpa using hsum 2
  refine ⟨labeling, fun R => ?_⟩
  rcases hfaces R with rfl | rfl
  · rw [zoneValue, h₁, Finset.sum_union hSU₁, hS, hV₁]; decide
  · rw [zoneValue, h₂, Finset.sum_union hSU₂, hS, hV₂]; decide

end PlaneGraph

end ZonalGraphs
