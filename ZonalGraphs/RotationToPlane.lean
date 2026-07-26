import ZonalGraphs.Embedding

namespace ZonalGraphs

/-!
# From a rotation system to a plane graph

`PlaneGraph` carries its faces as given data. That is what lets the results in this project be stated
without a theory of planarity, and it is also what stops any argument that has to *change* an embedding,
since a modified face structure has to be posited rather than computed. The inductions of section 4.3 of
the dissertation delete vertices and read off the faces of what remains, so they cannot be stated
faithfully against the interface.

This module closes that gap in the direction that matters: it builds a `PlaneGraph` out of a
`RotationSystem`, where the faces are *defined* as the orbits of `faceMap` rather than assumed. Two darts
lie on the same face when a power of `faceMap` carries one to the other, which is an equivalence, and the
faces are its quotient. The boundary of a face is the image of its darts under `vertexOf`, and its
boundary edges are the edges those darts span.

The immediate payoff is `isBalanced_boundary_darts`. Facial colour balance was available for any
`faceMap`-invariant set of darts, but on the interface nothing said a face *was* such a set. Here it is
one by construction, so the balance holds of the faces of an actual embedding with no hypothesis at all.

Deletion is not treated here. What it needs is the effect on darts of removing a vertex, after which the
new faces come out of this same quotient; that is the remaining step for the section 4.3 inductions.
-/

universe u w

namespace RotationSystem

variable {Vertex : Type u} {Dart : Type w} [Fintype Vertex] [Fintype Dart]
  (E : RotationSystem Vertex Dart)

/-- Two darts lie on the same face when a power of `faceMap` carries one to the other. -/
def faceSetoid : Setoid Dart where
  r d₁ d₂ := ∃ k : ℤ, (E.faceMap ^ k) d₁ = d₂
  iseqv :=
    { refl := fun d => ⟨0, by simp⟩
      symm := fun ⟨k, hk⟩ => ⟨-k, by rw [← hk, ← Equiv.Perm.mul_apply, ← zpow_add, neg_add_cancel,
        zpow_zero, Equiv.Perm.one_apply]⟩
      trans := fun ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ =>
        ⟨k₂ + k₁, by rw [zpow_add, Equiv.Perm.mul_apply, h₁, h₂]⟩ }

/-- The faces of the embedding: the orbits of `faceMap`. -/
abbrev Face := Quotient E.faceSetoid

noncomputable instance : Fintype E.Face := Fintype.ofFinite _

/-- The face a dart lies on. -/
def faceOf (d : Dart) : E.Face := Quotient.mk E.faceSetoid d

/-- Advancing along a face does not leave it. This is the fact the interface could not supply. -/
theorem faceOf_faceMap (d : Dart) : E.faceOf (E.faceMap d) = E.faceOf d :=
  Quotient.sound ⟨-1, by simp⟩

/-- The darts of a face. -/
noncomputable def darts (R : E.Face) : Finset Dart := by
  classical
  exact {d ∈ Finset.univ | E.faceOf d = R}

/-- A face's darts form a `faceMap`-invariant set, by construction rather than by assumption. -/
theorem faceMap_mem_darts_iff (R : E.Face) (d : Dart) :
    E.faceMap d ∈ E.darts R ↔ d ∈ E.darts R := by
  classical
  simp [darts, E.faceOf_faceMap]

/-- The boundary of a face: the vertices its darts point out of. -/
noncomputable def boundary (R : E.Face) : Finset Vertex := by
  classical
  exact (E.darts R).image E.vertexOf

/-- The boundary edges of a face: the edges its darts span. -/
noncomputable def boundaryEdges (R : E.Face) : Finset (Sym2 Vertex) := by
  classical
  exact (E.darts R).image fun d => s(E.vertexOf d, E.vertexOf (E.dartRev d))

/-- **A plane graph whose faces are computed, not assumed.**

Connectivity of the embedded graph is the one thing a rotation system does not already carry, so it is a
hypothesis. A dart is needed to name an exterior face. -/
noncomputable def toPlaneGraph [Nonempty Dart] (hconn : E.graph.Connected) :
    PlaneGraph Vertex E.Face where
  graph := E.graph
  connected := hconn
  boundary := E.boundary
  boundaryEdges := E.boundaryEdges
  exterior := E.faceOf (Classical.arbitrary Dart)

@[simp] theorem toPlaneGraph_boundary [Nonempty Dart] (hconn : E.graph.Connected) (R : E.Face) :
    (E.toPlaneGraph hconn).boundary R = E.boundary R := rfl

/-- **Facial colour balance for the faces of an actual embedding.**

`isBalanced_of_faceMap_invariant` needed a `faceMap`-invariant set of darts. A face is one by
construction here, so for a proper two-colouring every face carries equally many darts of each colour,
with no hypothesis about the face structure. -/
theorem isBalanced_boundary_darts (coloring : E.graph.Coloring (Fin 2)) (R : E.Face) :
    {d ∈ E.darts R | coloring (E.vertexOf d) = 0}.card =
      {d ∈ E.darts R | coloring (E.vertexOf d) = 1}.card :=
  E.isBalanced_of_faceMap_invariant coloring (E.darts R) (E.faceMap_mem_darts_iff R)

/-- The same balance at the level of boundary vertices, when the face's darts point at distinct vertices.

That injectivity is the statement that the facial boundary is a cycle rather than a closed walk revisiting
a vertex, which is where 2-connectedness of the embedded graph enters. -/
theorem isBalanced_boundary [DecidableEq Vertex] (coloring : E.graph.Coloring (Fin 2)) (R : E.Face)
    (hinj : Set.InjOn E.vertexOf (E.darts R)) :
    {v ∈ (E.darts R).image E.vertexOf | coloring v = 0}.card =
      {v ∈ (E.darts R).image E.vertexOf | coloring v = 1}.card :=
  E.isBalanced_image_of_faceMap_invariant coloring (E.darts R) (E.faceMap_mem_darts_iff R) hinj

end RotationSystem

end ZonalGraphs
