import ZonalGraphs.AbelianGroups
import ZonalGraphs.TreesAndCycles

namespace ZonalGraphs

/-!
# Zonal labelings valued in an arbitrary abelian group

Bowling (2025) replaces `ZMod 3` by an arbitrary abelian group `Γ`: a `Γ`-zonal labeling assigns each
vertex a nonzero element of `Γ` so that the labels bounding every region sum to `0`.  Taking
`Γ = ZMod 3` recovers the classical notion, since the nonzero elements there are exactly `1` and `2`.

`ZonalLabel` is hardwired to `ZMod 3`, so the group-valued notion needs its own definitions rather than a
reuse of the existing ones.  They are given here.

Proposition 2.4 then follows from the purely group-theoretic labeling lemma: a cycle has both of its two
regions bounded by every vertex, so being `Γ`-zonal is exactly the existence of a nonzero labeling of the
vertices summing to zero.
-/

universe u v

/-- A labeling of vertices by nonzero elements of an abelian group. -/
abbrev GroupLabeling (Vertex : Type u) (Γ : Type*) [AddCommGroup Γ] := Vertex → {x : Γ // x ≠ 0}

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face]
  {Γ : Type*} [AddCommGroup Γ]

/-- The value of a region under a group-valued labeling. -/
def groupZoneValue (P : PlaneGraph Vertex Face) (labeling : GroupLabeling Vertex Γ) (R : Face) : Γ :=
  ∑ v ∈ P.boundary R, (labeling v : Γ)

/-- A plane graph is `Γ`-zonal when some labeling by nonzero elements of `Γ` gives every region the
value `0`. -/
def IsGroupZonal (P : PlaneGraph Vertex Face) (Γ : Type*) [AddCommGroup Γ] : Prop :=
  ∃ labeling : GroupLabeling Vertex Γ, ∀ R : Face, P.groupZoneValue labeling R = 0

/-- A plane graph all of whose regions are bounded by every vertex is `Γ`-zonal as soon as the vertices
number at least two and `Γ` has two distinct nonzero elements.

Both regions of a cycle are of this shape, which is what Proposition 2.4 needs. -/
theorem isGroupZonal_of_boundary_eq_univ [DecidableEq Vertex] (P : PlaneGraph Vertex Face)
    (hboundary : ∀ R : Face, P.boundary R = Finset.univ) {g h : Γ} (hg : g ≠ 0) (hh : h ≠ 0)
    (hne : g ≠ h) (hcard : 2 ≤ Fintype.card Vertex) : P.IsGroupZonal Γ := by
  obtain ⟨f, hfne, hfsum⟩ :=
    exists_labeling_sum_eq_zero hg hh hne (Finset.univ : Finset Vertex) (by simpa using hcard)
  refine ⟨fun v => ⟨f v, hfne v⟩, fun R => ?_⟩
  rw [groupZoneValue, hboundary R]
  exact hfsum

/-- **Proposition 2.4 (Bowling, 2025).** For `n ≥ 3` the cycle `Cₙ` is `Γ`-zonal whenever `Γ` has two
distinct nonzero elements, that is, whenever `Γ` is neither trivial nor `ZMod 2`.

The excluded case is exactly the failure of that hypothesis: over `ZMod 2` the only available label is
`1`, so the sum over an odd cycle is `1`. -/
theorem isGroupZonal_ofCycle {g h : Γ} (hg : g ≠ 0) (hh : h ≠ 0) (hne : g ≠ h) (n : ℕ)
    (hn : 3 ≤ n) : (ofCycle n hn).IsGroupZonal Γ :=
  isGroupZonal_of_boundary_eq_univ _ (fun _ => rfl) hg hh hne (by simpa using by omega)

end PlaneGraph

end ZonalGraphs
