import ZonalGraphs.AbelianGroups
import ZonalGraphs.CycleRankTwo

namespace ZonalGraphs

/-!
# Labelings constant on prescribed blocks

Chapter 4 of the dissertation needs zonal labelings that are *constant* on each of a prescribed set of
edges, rather than merely realizing prescribed block sums. Lemma 4.3.3 is the case of a cycle carrying
`k` pairwise nonadjacent edges, and it feeds the inner-zonal results on Hamiltonian cubic maps.

The engines in `DutchWindmill` fix the sum over each block and leave the individual labels free, which
is the wrong currency here. What replaces them is `exists_labeling_constant_on_blocks`: given a
partition of the vertices into blocks of size one or two, there is a labeling constant on every block
whose total is zero. The proof needs no case analysis on the blocks beyond their size, because the
arithmetic of `ZMod 3` absorbs it. Pick nonzero values `g b` summing to zero over the blocks, which
`exists_labeling_sum_eq_zero` supplies as soon as there are at least two blocks, then give every
vertex of `b` the label `g b` when `b` is a singleton and `-g b` when `b` is a pair. A pair then
contributes `2 • (-g b) = g b`, since `-2 = 1` in `ZMod 3`, so each block contributes exactly `g b`
and the total is the sum of the `g b`.

Nonadjacency of the prescribed edges is what makes them disjoint, so it enters only as the
disjointness hypothesis on the blocks.
-/

universe u v

variable {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]

/-- Doubling a negated element of `ZMod 3` returns the element, because `-2 = 1`. This is the whole
reason a pair of equal labels can realize any prescribed nonzero block value. -/
theorem two_nsmul_neg (x : ZMod 3) : (2 : ℕ) • (-x) = x := by
  have h : ((2 : ℕ) : ZMod 3) * (-1) = 1 := by decide
  rw [nsmul_eq_mul, neg_eq_neg_one_mul, ← mul_assoc, h, one_mul]

/-- Negation preserves nonzeroness, so `-g b` is a legal label. -/
theorem neg_ne_zero_of_ne_zero {x : ZMod 3} (hx : x ≠ 0) : -x ≠ 0 := neg_ne_zero.mpr hx

/-- **A labeling constant on each block of a partition into singletons and pairs, with total zero.**

The blocks partition the vertices and each has one or two elements. Choosing nonzero values summing to
zero over the blocks and spreading each value over its block, negated on the pairs, gives a labeling
that is constant on every block and sums to zero over all vertices.

At least two blocks are needed, exactly as in `exists_labeling_sum_eq_zero`: a single block would ask
for one nonzero element of `ZMod 3` equal to zero. -/
theorem exists_labeling_constant_on_blocks (blocks : Finset (Finset Vertex))
    (hcover : ∀ v : Vertex, ∃ b ∈ blocks, v ∈ b)
    (hdisj : ∀ b ∈ blocks, ∀ c ∈ blocks, b ≠ c → Disjoint b c)
    (hcard : ∀ b ∈ blocks, b.card = 1 ∨ b.card = 2) (hnum : 2 ≤ blocks.card) :
    ∃ labeling : VertexLabeling Vertex,
      (∑ v : Vertex, (labeling v : ZMod 3)) = 0 ∧
        ∀ b ∈ blocks, ∀ u ∈ b, ∀ v ∈ b, labeling u = labeling v := by
  obtain ⟨g, hgne, hgsum⟩ :=
    exists_labeling_sum_eq_zero (g := (1 : ZMod 3)) (h := (2 : ZMod 3)) (by decide) (by decide)
      (by decide) blocks hnum
  -- the value carried by every vertex of a block, negated on the pairs so that the block totals `g b`
  set c : Finset Vertex → ZMod 3 := fun b => if b.card = 1 then g b else -g b with hc
  have hcne : ∀ b, c b ≠ 0 := by
    intro b
    by_cases hb : b.card = 1
    · simpa [hc, hb] using hgne b
    · simpa [hc, hb] using neg_ne_zero_of_ne_zero (hgne b)
  -- the block of a vertex, well defined because the blocks are disjoint
  set blk : Vertex → Finset Vertex := fun v => (hcover v).choose with hblk
  have hblk_mem : ∀ v, blk v ∈ blocks := fun v => (hcover v).choose_spec.1
  have hblk_self : ∀ v, v ∈ blk v := fun v => (hcover v).choose_spec.2
  have hblk_eq : ∀ (b : Finset Vertex), b ∈ blocks → ∀ v ∈ b, blk v = b := by
    intro b hb v hv
    by_contra hne
    exact (Finset.disjoint_left.mp (hdisj _ (hblk_mem v) b hb hne) (hblk_self v)) hv
  refine ⟨fun v => ⟨c (blk v), hcne _⟩, ?_, ?_⟩
  · have huniv : (Finset.univ : Finset Vertex) = blocks.biUnion id := by
      ext v
      simpa using ⟨blk v, hblk_mem v, hblk_self v⟩
    have hpd : (blocks : Set (Finset Vertex)).PairwiseDisjoint id :=
      fun b hb d hd hbd => hdisj b hb d hd hbd
    rw [huniv, Finset.sum_biUnion hpd]
    have hinner : ∀ b ∈ blocks, (∑ v ∈ id b, c (blk v)) = g b := by
      intro b hb
      rw [id_eq, Finset.sum_congr rfl fun v hv => by rw [hblk_eq b hb v hv], Finset.sum_const]
      rcases hcard b hb with h1 | h2
      · rw [h1, one_nsmul, hc]
        simp [h1]
      · rw [h2, hc]
        simpa [h2] using two_nsmul_neg (g b)
    rw [Finset.sum_congr rfl hinner]
    exact hgsum
  · intro b hb u hu v hv
    have : blk u = blk v := by rw [hblk_eq b hb u hu, hblk_eq b hb v hv]
    simp [this]

namespace PlaneGraph

variable {Face : Type v} [Fintype Face]

/-- **Lemma 4.3.3 (Bowling, 2025).** A cycle carrying `k` pairwise nonadjacent edges has a zonal
labeling giving both endpoints of each of those edges the same label.

Both regions of a cycle are bounded by every vertex, which is the hypothesis `hboundary`, so a zonal
labeling is exactly a labeling of all the vertices summing to zero. The prescribed edges are pairwise
nonadjacent, hence disjoint as vertex pairs, and together with the singletons of the remaining
vertices they partition the vertex set into blocks of size one or two. The count `n ≥ 2k` with `k ≥ 2`
gives `n - k ≥ k ≥ 2` blocks, which is the hypothesis `hnum`.

Constancy on a block of size two is the requirement `ℓ x = ℓ y` on each prescribed edge `xy`. -/
theorem exists_isZonalLabeling_constant_on_blocks (P : PlaneGraph Vertex Face)
    (hboundary : ∀ R : Face, P.boundary R = Finset.univ) (blocks : Finset (Finset Vertex))
    (hcover : ∀ v : Vertex, ∃ b ∈ blocks, v ∈ b)
    (hdisj : ∀ b ∈ blocks, ∀ c ∈ blocks, b ≠ c → Disjoint b c)
    (hcard : ∀ b ∈ blocks, b.card = 1 ∨ b.card = 2) (hnum : 2 ≤ blocks.card) :
    ∃ labeling : VertexLabeling Vertex,
      P.IsZonalLabeling labeling ∧ ∀ b ∈ blocks, ∀ u ∈ b, ∀ v ∈ b, labeling u = labeling v := by
  obtain ⟨labeling, hsum, hconst⟩ :=
    exists_labeling_constant_on_blocks blocks hcover hdisj hcard hnum
  refine ⟨labeling, fun R => ?_, hconst⟩
  rw [zoneValue, hboundary R]
  exact hsum

end PlaneGraph

end ZonalGraphs
