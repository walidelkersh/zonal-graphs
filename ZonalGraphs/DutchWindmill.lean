import ZonalGraphs.Definitions
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Dutch windmill graphs with two blades

This module formalizes Proposition 2.2.1 of Bowling, *Zonality in Graphs* (2023): for every
multiset `S` of two cycles, the Dutch windmill graph `D(S)` is not zonal.

For a two-element `S`, the graph `D(S)` consists of two cycles meeting in a single vertex, the
*hub*.  Its plane embedding has three regions: each cycle bounds one interior region, and the two
cycles together bound the exterior region.

The obstruction depends only on the region boundaries, so it is isolated in
`PlaneGraph.not_isZonal_of_isTwoBladedWindmill`.  The exterior boundary is the union of the two
blade boundaries, and those meet exactly in the hub.  Summing labels over a union together with a
sum over the intersection counts every vertex exactly twice, so the three region values satisfy
`0 + ℓ(hub) = 0 + 0`.  That forces `ℓ(hub) = 0`, which is impossible because zonal labels are the
*nonzero* elements of `ZMod 3`.  Note that no property of cycles is used: only the shape of the
face data.

Mathlib provides no windmill construction, so the canonical three-region realization is built here
as `PlaneGraph.ofTwoBladedWindmill`.

`PlaneGraph.IsWindmillEmbedding` then records the face data shared by *every* planar embedding of a
Dutch windmill with any number of blades: deleting the hub leaves pairwise disjoint *petals*, and
each region is bounded by the hub together with a set of whole petals.  Region values reduce to
`ℓ(hub) + Σ qᵢ` over the petal sums `qᵢ`, which yields the congruence
`IsWindmillEmbedding.card_eq_one_of_isZonal`: an embedding having a region per petal and a region
bounded by all petals — the standard embedding — is zonal only if the number of blades is `1`
modulo `3`.
-/

universe u v w

namespace PlaneGraph

variable {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]

section FaceStructure

variable {Face : Type v} [Fintype Face]

/-- The face structure of a two-bladed windmill: two regions whose boundaries meet in exactly one
vertex, the hub, together bounding a third region. -/
structure IsTwoBladedWindmill (P : PlaneGraph Vertex Face) (blade₁ blade₂ exterior : Face)
    (hub : Vertex) : Prop where
  /-- The two blades together bound the third region. -/
  boundary_union : P.boundary exterior = P.boundary blade₁ ∪ P.boundary blade₂
  /-- The two blades meet exactly in the hub. -/
  boundary_inter : P.boundary blade₁ ∩ P.boundary blade₂ = {hub}

/-- A plane graph carrying the face structure of a two-bladed windmill is not zonal.

If the two blade regions both had value zero, the value of the third region would be the negative
of the hub's label, and hence nonzero. -/
theorem not_isZonal_of_isTwoBladedWindmill {P : PlaneGraph Vertex Face}
    {blade₁ blade₂ exterior : Face} {hub : Vertex}
    (hwindmill : P.IsTwoBladedWindmill blade₁ blade₂ exterior hub) : ¬ P.IsZonal := by
  rintro ⟨labeling, hlabeling⟩
  have hval : ∀ R : Face, (∑ v ∈ P.boundary R, (labeling v : ZMod 3)) = 0 := hlabeling
  have hsum : (∑ v ∈ P.boundary exterior, (labeling v : ZMod 3)) +
      ∑ v ∈ P.boundary blade₁ ∩ P.boundary blade₂, (labeling v : ZMod 3) =
      (∑ v ∈ P.boundary blade₁, (labeling v : ZMod 3)) +
        ∑ v ∈ P.boundary blade₂, (labeling v : ZMod 3) := by
    rw [hwindmill.boundary_union]
    exact Finset.sum_union_inter
  rw [hwindmill.boundary_inter, Finset.sum_singleton] at hsum
  simp only [hval, zero_add, add_zero] at hsum
  exact (labeling hub).property hsum

end FaceStructure

section WindmillEmbedding

variable {Face : Type v} [Fintype Face] {Blade : Type w}

/-- The face data common to *every* planar embedding of a Dutch windmill.

All cycles of a Dutch windmill meet in the hub, so deleting the hub leaves the pairwise disjoint
*petals* `C - hub`.  However the cycles are nested in the plane, each region is bounded by the hub
together with a set of whole petals, recorded by `regionPetals`.  This covers the standard
embedding, the nested embeddings, and the hybrids of the two. -/
structure IsWindmillEmbedding (P : PlaneGraph Vertex Face) (hub : Vertex)
    (petal : Blade → Finset Vertex) (regionPetals : Face → Finset Blade) : Prop where
  /-- The hub has been deleted from every petal. -/
  hub_notMem_petal : ∀ b, hub ∉ petal b
  /-- Distinct cycles meet only in the hub, so distinct petals are disjoint. -/
  petal_disjoint : ∀ b c, b ≠ c → Disjoint (petal b) (petal c)
  /-- Each region is bounded by the hub together with a set of whole petals. -/
  boundary_eq : ∀ R, P.boundary R = insert hub ((regionPetals R).biUnion petal)

namespace IsWindmillEmbedding

variable {P : PlaneGraph Vertex Face} {hub : Vertex} {petal : Blade → Finset Vertex}
  {regionPetals : Face → Finset Blade}

/-- The value of a region of a windmill embedding is the hub's label plus the petal sums of the
petals bounding it. -/
theorem zoneValue_eq (h : P.IsWindmillEmbedding hub petal regionPetals)
    (labeling : VertexLabeling Vertex) (R : Face) :
    P.zoneValue labeling R =
      (labeling hub : ZMod 3) + ∑ b ∈ regionPetals R, ∑ v ∈ petal b, (labeling v : ZMod 3) := by
  have hnot : hub ∉ (regionPetals R).biUnion petal := by
    simp only [Finset.mem_biUnion]
    push_neg
    exact fun b _ => h.hub_notMem_petal b
  rw [zoneValue, h.boundary_eq R, Finset.sum_insert hnot,
    Finset.sum_biUnion fun b _ c _ hbc => h.petal_disjoint b c hbc]

/-- **The windmill congruence.** If a windmill embedding has a region bounded by each single petal
and also a region bounded by all the petals at once, then it is zonal only when the number of
petals is congruent to `1` modulo `3`.

Each single-petal region forces its petal sum to be `-ℓ(hub)`, so the all-petal region has value
`ℓ(hub) * (1 - k)` for `k` petals.  Since `ZMod 3` is a field and zonal labels are nonzero, `k = 1`
in `ZMod 3`. -/
theorem card_eq_one_of_isZonal [Fintype Blade]
    (h : P.IsWindmillEmbedding hub petal regionPetals) {single : Blade → Face} {full : Face}
    (hsingle : ∀ b, regionPetals (single b) = {b}) (hfull : regionPetals full = Finset.univ)
    (hzonal : P.IsZonal) : (Fintype.card Blade : ZMod 3) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨labeling, hlabeling⟩ := hzonal
  have hval : ∀ R : Face, P.zoneValue labeling R = 0 := hlabeling
  have hpetal : ∀ b, (∑ v ∈ petal b, (labeling v : ZMod 3)) = -(labeling hub : ZMod 3) := by
    intro b
    have hb := h.zoneValue_eq labeling (single b)
    rw [hval, hsingle b, Finset.sum_singleton] at hb
    linear_combination -hb
  have hfullval := h.zoneValue_eq labeling full
  rw [hval, hfull] at hfullval
  simp only [hpetal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hfullval
  have hmul : (labeling hub : ZMod 3) * (1 - (Fintype.card Blade : ZMod 3)) = 0 := by
    linear_combination -hfullval
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact absurd hzero (labeling hub).property
  · linear_combination -hzero

/-- A windmill embedding with a region per petal and a region bounded by all petals is not zonal
once the number of petals is not `1` modulo `3`.  This is the non-zonal half of Theorem 2.2.2 for
the standard embedding, and it subsumes Proposition 2.2.1, where there are two petals. -/
theorem not_isZonal_of_card_ne_one [Fintype Blade]
    (h : P.IsWindmillEmbedding hub petal regionPetals) {single : Blade → Face} {full : Face}
    (hsingle : ∀ b, regionPetals (single b) = {b}) (hfull : regionPetals full = Finset.univ)
    (hcard : (Fintype.card Blade : ZMod 3) ≠ 1) : ¬ P.IsZonal :=
  fun hzonal => hcard (h.card_eq_one_of_isZonal hsingle hfull hzonal)

end IsWindmillEmbedding

end WindmillEmbedding

/-- The canonical three-region realization of a two-bladed windmill: a connected graph whose vertex
set is covered by two blades meeting exactly in the hub.

Region `0` is bounded by the first blade, region `1` by the second, and the exterior region `2` by
both blades together.  That this face data really describes a windmill is expressed separately, by
`isTwoBladedWindmill_ofTwoBladedWindmill`. -/
def ofTwoBladedWindmill (G : SimpleGraph Vertex) (hG : G.Connected)
    (blade₁ blade₂ : Finset Vertex)
    (bladeEdges₁ bladeEdges₂ : Finset (Sym2 Vertex)) : PlaneGraph Vertex (Fin 3) where
  graph := G
  connected := hG
  boundary := fun R => if R = 0 then blade₁ else if R = 1 then blade₂ else Finset.univ
  boundaryEdges := fun R =>
    if R = 0 then bladeEdges₁ else if R = 1 then bladeEdges₂ else bladeEdges₁ ∪ bladeEdges₂
  exterior := 2

variable (G : SimpleGraph Vertex) (hG : G.Connected) (blade₁ blade₂ : Finset Vertex)
  (bladeEdges₁ bladeEdges₂ : Finset (Sym2 Vertex))

/-- Two blades covering the vertex set and meeting exactly in the hub do give the canonical
realization the face structure of a two-bladed windmill. -/
theorem isTwoBladedWindmill_ofTwoBladedWindmill {hub : Vertex}
    (hcover : blade₁ ∪ blade₂ = Finset.univ) (hmeet : blade₁ ∩ blade₂ = {hub}) :
    (ofTwoBladedWindmill G hG blade₁ blade₂ bladeEdges₁ bladeEdges₂).IsTwoBladedWindmill
      0 1 2 hub where
  boundary_union := by simpa [ofTwoBladedWindmill] using hcover.symm
  boundary_inter := by simpa [ofTwoBladedWindmill] using hmeet

/-- **Proposition 2.2.1 (Bowling, 2023).** For every multiset `S` of two cycles the Dutch windmill
graph `D(S)` is not zonal: two cycles meeting in a single hub admit no zonal labeling. -/
theorem not_isZonal_ofTwoBladedWindmill {hub : Vertex}
    (hcover : blade₁ ∪ blade₂ = Finset.univ) (hmeet : blade₁ ∩ blade₂ = {hub}) :
    ¬ (ofTwoBladedWindmill G hG blade₁ blade₂ bladeEdges₁ bladeEdges₂).IsZonal :=
  not_isZonal_of_isTwoBladedWindmill
    (isTwoBladedWindmill_ofTwoBladedWindmill G hG blade₁ blade₂ bladeEdges₁ bladeEdges₂
      hcover hmeet)

end PlaneGraph

end ZonalGraphs
