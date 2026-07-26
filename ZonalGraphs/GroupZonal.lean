import ZonalGraphs.AbelianGroups
import ZonalGraphs.BipartiteZonal
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

/-- The regions having a given vertex on their boundary, written `X_v` in the literature. -/
def regionsAt [DecidableEq Vertex] (P : PlaneGraph Vertex Face) (v : Vertex) : Finset Face :=
  {R ∈ Finset.univ | v ∈ P.boundary R}

/-- A plane graph is `Γ`-*cozonal* when some labeling of its **regions** by nonzero elements of `Γ` gives
every vertex the value `0`, the value of a vertex being the sum over the regions on whose boundary it
lies.

This is the exact dual of zonality: zonal labels vertices and sums over each region's boundary, cozonal
labels regions and sums over each vertex's incident regions. -/
def IsGroupCozonal [DecidableEq Vertex] (P : PlaneGraph Vertex Face) (Γ : Type*)
    [AddCommGroup Γ] : Prop :=
  ∃ labeling : Face → {x : Γ // x ≠ 0},
    ∀ v : Vertex, ∑ R ∈ P.regionsAt v, (labeling R : Γ) = 0

/-- **Observation 2.2 (Bowling, 2025).** A group homomorphism carries a `Γ`-zonal labeling avoiding its
kernel to a `Γ'`-zonal labeling.

No vertex label lies in the kernel, so the images are again nonzero, and a homomorphism commutes with the
sum defining a region's value. -/
theorem isGroupZonal_map {Γ' : Type*} [AddCommGroup Γ'] (φ : Γ →+ Γ')
    (P : PlaneGraph Vertex Face) (labeling : GroupLabeling Vertex Γ)
    (hkernel : ∀ v, φ (labeling v) ≠ 0)
    (hzonal : ∀ R : Face, P.groupZoneValue labeling R = 0) : P.IsGroupZonal Γ' := by
  refine ⟨fun v => ⟨φ (labeling v), hkernel v⟩, fun R => ?_⟩
  simp only [groupZoneValue] at hzonal ⊢
  rw [← map_sum, hzonal R, map_zero]

/-- **The generalization is faithful.** At `Γ = ZMod 3` the group-valued notion *is* the original one, on
the nose rather than up to translation.

`ZonalLabel` unfolds to the nonzero elements of `ZMod 3`, so `GroupLabeling Vertex (ZMod 3)` and
`VertexLabeling Vertex` are the same type and the two region values are the same sum.  Anything proved
about `IsGroupZonal` therefore specializes to `IsZonal` with no translation step. -/
theorem isGroupZonal_zmod_three_iff (P : PlaneGraph Vertex Face) :
    P.IsGroupZonal (ZMod 3) ↔ P.IsZonal := Iff.rfl

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

/-- **The zonal half of Proposition 2.7 (Bowling, 2025).** A plane graph carrying a proper two-colouring
whose every facial boundary is balanced is `Γ`-zonal, for any abelian `Γ` with a nonzero element.

Label one colour class `g` and the other `-g`.  A balanced boundary has equally many vertices of each
colour, so its value is `n • g + n • (-g) = 0`.  Nothing about `ZMod 3` is used, and no facial parity
argument beyond balance.

This does not discharge the todo entry for Proposition 2.7, which is a conjunction whose dual half
concerns cozonal labelings of Eulerian plane graphs and is not proved here. -/
theorem isGroupZonal_of_facialBalance [DecidableEq Vertex] (P : PlaneGraph Vertex Face)
    (coloring : P.graph.Coloring (Fin 2)) {g : Γ} (hg : g ≠ 0)
    (hbalance : ∀ R : Face, SimpleGraph.IsBalanced coloring (P.boundary R)) : P.IsGroupZonal Γ := by
  refine ⟨fun v => ⟨if coloring v = 0 then g else -g, ?_⟩, fun R => ?_⟩
  · by_cases hv : coloring v = 0 <;> simp [hv, hg]
  · have hb : {x ∈ P.boundary R | coloring x = 0}.card
        = {x ∈ P.boundary R | coloring x = 1}.card := hbalance R
    have hzero : ∀ x ∈ {x ∈ P.boundary R | coloring x = 0},
        (if coloring x = 0 then g else -g) = g := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      simp [hx.2]
    have hone : ∀ x ∈ {x ∈ P.boundary R | coloring x = 1},
        (if coloring x = 0 then g else -g) = -g := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      simp [hx.2]
    rw [groupZoneValue,
      ← Finset.sum_filter_add_sum_filter_not (P.boundary R) fun x => coloring x = 0,
      SimpleGraph.filter_color_ne_zero coloring (P.boundary R),
      Finset.sum_congr rfl hzero, Finset.sum_congr rfl hone, Finset.sum_const, Finset.sum_const,
      hb, ← smul_add, add_neg_cancel, smul_zero]

end PlaneGraph

end ZonalGraphs
