import ZonalGraphs.GroupZonal

namespace ZonalGraphs

/-!
# Zonal and cozonal are dual, without constructing a dual graph

Proposition 1.3 of Bowling (2025): a connected plane graph is zonal exactly when its plane dual is
cozonal.

Building the plane dual as a `PlaneGraph` is not possible here, since the dual of a plane graph is in
general a multigraph while `PlaneGraph` carries a `SimpleGraph`. That obstruction is avoidable. Zonality
and cozonality never mention the underlying graph: they refer only to which vertices bound which regions.
Abstracting that incidence data makes duality a transposition, and the proposition becomes a matter of
unfolding.

`Incidence` records exactly the boundary function. Its dual sends a vertex to the set of regions it
bounds, and a labeling of one side is literally a labeling of the other, so a zonal labeling of an
incidence structure *is* a cozonal labeling of its dual.
-/

universe u v

/-- The data that zonality depends on: finitely many vertices, finitely many regions, and the boundary
vertices of each region. The underlying graph plays no role. -/
structure Incidence (Vertex : Type u) (Face : Type v) [Fintype Vertex] [Fintype Face] where
  /-- The vertices on the boundary of a region. -/
  boundary : Face → Finset Vertex

namespace Incidence

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face]
  {Γ : Type*} [AddCommGroup Γ]

/-- Labelling vertices by nonzero group elements so that every region sums to zero. -/
def IsZonal (I : Incidence Vertex Face) (Γ : Type*) [AddCommGroup Γ] : Prop :=
  ∃ labeling : Vertex → {x : Γ // x ≠ 0},
    ∀ R : Face, ∑ v ∈ I.boundary R, (labeling v : Γ) = 0

/-- Labelling regions by nonzero group elements so that every vertex sums to zero, the sum for a vertex
running over the regions it bounds. -/
def IsCozonal [DecidableEq Vertex] (I : Incidence Vertex Face) (Γ : Type*) [AddCommGroup Γ] : Prop :=
  ∃ labeling : Face → {x : Γ // x ≠ 0},
    ∀ v : Vertex, ∑ R ∈ {R ∈ Finset.univ | v ∈ I.boundary R}, (labeling R : Γ) = 0

/-- The dual incidence structure: vertices and regions swap, and a vertex is bounded by the regions it
used to bound. -/
def dual [DecidableEq Vertex] (I : Incidence Vertex Face) : Incidence Face Vertex where
  boundary := fun v => {R ∈ Finset.univ | v ∈ I.boundary R}

/-- Dualizing twice restores the boundary data. -/
theorem dual_dual_boundary [DecidableEq Vertex] [DecidableEq Face] (I : Incidence Vertex Face)
    (R : Face) : I.dual.dual.boundary R = I.boundary R := by
  ext v
  simp [dual]

/-- **Proposition 1.3 (Bowling, 2025).** An incidence structure is zonal exactly when its dual is
cozonal, for every abelian group.

A labeling of the vertices is the same thing as a labeling of the dual's regions, and the set of vertices
bounding a region equals the set of dual-regions that the region bounds. So the two statements are the
same sum, region by region. -/
theorem isZonal_iff_dual_isCozonal [DecidableEq Vertex] [DecidableEq Face]
    (I : Incidence Vertex Face) : I.IsZonal Γ ↔ I.dual.IsCozonal Γ := by
  have hset : ∀ R : Face,
      {v ∈ (Finset.univ : Finset Vertex) | R ∈ I.dual.boundary v} = I.boundary R := by
    intro R
    ext v
    simp [dual]
  constructor
  · rintro ⟨labeling, hlabeling⟩
    exact ⟨labeling, fun R => by rw [hset R]; exact hlabeling R⟩
  · rintro ⟨labeling, hlabeling⟩
    exact ⟨labeling, fun R => by rw [← hset R]; exact hlabeling R⟩

end Incidence

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face]
  {Γ : Type*} [AddCommGroup Γ]

/-- The incidence data of a plane graph, forgetting the graph. -/
def toIncidence (P : PlaneGraph Vertex Face) : Incidence Vertex Face where
  boundary := P.boundary

/-- Group-valued zonality of a plane graph is zonality of its incidence data: the graph itself is never
consulted. -/
theorem isGroupZonal_iff_toIncidence_isZonal (P : PlaneGraph Vertex Face) :
    P.IsGroupZonal Γ ↔ P.toIncidence.IsZonal Γ := Iff.rfl

/-- Likewise for cozonality. -/
theorem isGroupCozonal_iff_toIncidence_isCozonal [DecidableEq Vertex]
    (P : PlaneGraph Vertex Face) : P.IsGroupCozonal Γ ↔ P.toIncidence.IsCozonal Γ := Iff.rfl

end PlaneGraph

end ZonalGraphs
