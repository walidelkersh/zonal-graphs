import ZonalGraphs.DutchWindmill

namespace ZonalGraphs

/-!
# Bicubic maps with a Hamiltonian exterior boundary

Theorem 4.3.1 of the dissertation, which is Theorem 6.16 of Chartrand, Egan and Zhang, says a bicubic map
whose exterior boundary is a Hamiltonian cycle with `k` pairwise nonadjacent chords has an inner zonal
labeling giving both ends of every chord the same label. Its proof runs by induction on `k`, and the
induction step deletes the interior vertices of one region to produce a smaller bicubic map with `k - 1`
chords.

The base case is proved here. One chord `xy` splits the interior into two regions whose boundaries meet
exactly in `x` and `y` and cover every vertex. Give `x` and `y` the label `1`, and give the remaining
vertices of each boundary labels summing to `1`; each boundary then totals `1 + 1 + 1 = 0`. Both regions
vanish, the chord ends agree, and the exterior is left free, which is what inner zonality allows.

The induction step is not formalized, and the obstruction is the interface rather than any missing
mathematics. `PlaneGraph` carries its face data as given, so "deleting the interior vertices of this
region leaves a bicubic map whose exterior boundary is a Hamiltonian cycle with one fewer chord" is not
derivable from the structure; it would have to be assumed, and assuming it would concede most of the
statement. Reaching the full theorem wants a `PlaneGraph` built from a rotation system, where deletion
acts on the darts and the new faces are computed rather than posited. The same obstruction blocks
Theorems 4.3.5, 4.3.6 and 4.3.8, which are inductions over classes of cubic maps with the same kind of
surgery.
-/

universe u v

variable {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]

omit [Fintype Vertex] in
/-- **The base case of Theorem 4.3.1.** Two boundaries meeting in exactly two vertices `x` and `y`, and
covering the vertex set between them, carry a labeling that vanishes on both and gives `x` and `y` a
common label.

Both `x` and `y` take `1`, and the vertices private to each boundary take labels summing to `1`, so each
boundary totals `3`. The engine behind it is `exists_labeling_blockSum_eq` on four blocks: the two
private parts and the two singletons. -/
theorem exists_labeling_pair_eq_of_two_boundaries (B₁ B₂ : Finset Vertex) {x y : Vertex} (hxy : x ≠ y)
    (hinter : B₁ ∩ B₂ = {x, y}) (h₁ : 3 ≤ B₁.card) (h₂ : 3 ≤ B₂.card) :
    ∃ labeling : VertexLabeling Vertex,
      labeling x = labeling y ∧ (∑ v ∈ B₁, (labeling v : ZMod 3)) = 0 ∧
        (∑ v ∈ B₂, (labeling v : ZMod 3)) = 0 := by
  classical
  have hpair₁ : ({x, y} : Finset Vertex) ⊆ B₁ := hinter ▸ Finset.inter_subset_left
  have hpair₂ : ({x, y} : Finset Vertex) ⊆ B₂ := hinter ▸ Finset.inter_subset_right
  set blk : Fin 4 → Finset Vertex :=
    fun p => if p = 0 then B₁ \ {x, y} else if p = 1 then B₂ \ {x, y} else if p = 2 then {x} else {y}
    with hblk
  -- the four blocks are pairwise disjoint, the two big ones because they meet only in `x` and `y`
  have hcross : Disjoint (B₁ \ ({x, y} : Finset Vertex)) (B₂ \ ({x, y} : Finset Vertex)) := by
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    simp only [Finset.mem_sdiff] at hv₁ hv₂
    have : v ∈ B₁ ∩ B₂ := Finset.mem_inter.mpr ⟨hv₁.1, hv₂.1⟩
    rw [hinter] at this
    exact hv₁.2 this
  have hcross' : Disjoint (B₂ \ ({x, y} : Finset Vertex)) (B₁ \ ({x, y} : Finset Vertex)) :=
    hcross.symm
  have hyx : y ≠ x := Ne.symm hxy
  have hdisj : ∀ p q : Fin 4, p ≠ q → Disjoint (blk p) (blk q) := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [Finset.disjoint_left]
  -- both large blocks keep at least one vertex, since each boundary has three
  have hpairCard : ({x, y} : Finset Vertex).card = 2 := Finset.card_pair hxy
  have hcard₁ : 1 ≤ (B₁ \ ({x, y} : Finset Vertex)).card := by
    have := Finset.card_sdiff_add_card_eq_card hpair₁
    omega
  have hcard₂ : 1 ≤ (B₂ \ ({x, y} : Finset Vertex)).card := by
    have := Finset.card_sdiff_add_card_eq_card hpair₂
    omega
  have hone : ∀ p : Fin 4, 1 ≤ (blk p).card := by
    intro p
    fin_cases p <;> simp_all
  -- every block can absorb the target `1`
  have hfit : ∀ p : Fin 4, ((1 : ZMod 3) - ((blk p).card : ZMod 3)).val ≤ (blk p).card := by
    intro p
    have hval : ((1 : ZMod 3) - ((blk p).card : ZMod 3)).val < 3 := ZMod.val_lt _
    have h1 := hone p
    rcases Nat.lt_or_ge (blk p).card 2 with hlt | hge
    · have hc1 : (blk p).card = 1 := by omega
      rw [hc1]
      decide
    · omega
  obtain ⟨labeling, hsum⟩ := PlaneGraph.exists_labeling_blockSum_eq blk hdisj (fun _ => 1) hfit
  have hx : ((labeling x : ZonalLabel) : ZMod 3) = 1 := by
    have := hsum 2
    simpa [hblk] using this
  have hy : ((labeling y : ZonalLabel) : ZMod 3) = 1 := by
    have := hsum 3
    simpa [hblk] using this
  have hboundary : ∀ (B : Finset Vertex) (p : Fin 4), blk p = B \ ({x, y} : Finset Vertex) →
      ({x, y} : Finset Vertex) ⊆ B → (∑ v ∈ B, ((labeling v : ZonalLabel) : ZMod 3)) = 0 := by
    intro B p hp hsubset
    have hsplit := Finset.sum_sdiff (f := fun v => ((labeling v : ZonalLabel) : ZMod 3)) hsubset
    rw [← hsplit, ← hp, hsum p, Finset.sum_pair hxy, hx, hy]
    decide
  refine ⟨labeling, Subtype.ext (hx.trans hy.symm), ?_, ?_⟩
  · exact hboundary B₁ 0 (by simp [hblk]) hpair₁
  · exact hboundary B₂ 1 (by simp [hblk]) hpair₂

namespace PlaneGraph

variable {Face : Type v} [Fintype Face]

/-- **Theorem 4.3.1, base case.** A plane graph with one chord, so with two interior regions meeting in
the chord's ends and covering the vertices, is inner zonal by a labeling giving the chord's ends a common
label.

The exterior is the exceptional region that inner zonality permits. -/
theorem isInnerZonal_of_one_chord (P : PlaneGraph Vertex Face) {R₁ R₂ exterior : Face}
    (hfaces : ∀ R : Face, R = R₁ ∨ R = R₂ ∨ R = exterior) {x y : Vertex} (hxy : x ≠ y)
    (hR₁ : R₁ ≠ exterior) (hR₂ : R₂ ≠ exterior)
    (hinter : P.boundary R₁ ∩ P.boundary R₂ = {x, y}) (h₁ : 3 ≤ (P.boundary R₁).card)
    (h₂ : 3 ≤ (P.boundary R₂).card) :
    ∃ labeling : VertexLabeling Vertex,
      P.IsInnerZonalLabeling labeling ∧ labeling x = labeling y := by
  obtain ⟨labeling, hpair, hs₁, hs₂⟩ :=
    exists_labeling_pair_eq_of_two_boundaries (P.boundary R₁) (P.boundary R₂) hxy hinter h₁ h₂
  refine ⟨labeling, ⟨exterior, fun R hR => ?_⟩, hpair⟩
  rcases hfaces R with rfl | rfl | rfl
  · exact hs₁
  · exact hs₂
  · exact absurd rfl hR

end PlaneGraph

end ZonalGraphs
