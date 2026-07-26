import ZonalGraphs.Embedding
import ZonalGraphs.BipartiteZonal

namespace ZonalGraphs

/-!
# Facial balance is a theorem, not a hypothesis

`PlaneGraph.HasFacialBipartitionBalance` asserts that a proper two-colouring of a plane graph splits
the boundary of every region into two classes of equal size.  Proposition 2.1.1 needs it, and
`PlaneRealization` currently carries it as a field because `PlaneGraph` is an interface of
hand-supplied face data with nothing to derive it from.

This module removes that assumption for every plane graph that comes from an actual combinatorial
embedding.  Given a `RotationSystem` and an indexing of its faces by `faceMap`-invariant sets of
darts, `RotationSystem.toPlaneGraph` builds the corresponding `PlaneGraph`, and
`RotationSystem.hasFacialBipartitionBalance_toPlaneGraph` proves the balance condition outright.

One hypothesis remains, and it is a different statement from the conclusion: the darts of each face
must point out of distinct vertices, that is, each facial boundary is a cycle rather than a closed
walk revisiting a vertex.  This is the standard consequence of 2-connectedness, and it is the only
part of Proposition 2.1.1's geometric input still left open.
-/

universe u w

namespace RotationSystem

variable {Vertex : Type u} {Dart : Type w} [Fintype Vertex] [Fintype Dart] [DecidableEq Vertex]
  {Face : Type u} [Fintype Face] (E : RotationSystem Vertex Dart)

/-- The plane graph determined by a rotation system together with an indexing of its faces by sets
of darts.  A region's boundary is the set of vertices its darts point out of. -/
def toPlaneGraph (hconnected : E.graph.Connected) (faceDarts : Face → Finset Dart)
    (faceEdges : Face → Finset (Sym2 Vertex)) (exterior : Face) : PlaneGraph Vertex Face where
  graph := E.graph
  connected := hconnected
  boundary := fun R => (faceDarts R).image E.vertexOf
  boundaryEdges := faceEdges
  exterior := exterior

/-- **Facial bipartition balance, proved.** If every face of a rotation system is a
`faceMap`-invariant set of darts pointing out of distinct vertices, then the resulting plane graph
satisfies `PlaneGraph.HasFacialBipartitionBalance`.

No planarity is used.  `faceMap` sends each dart to a dart at the other end of its edge, so it
exchanges the two colour classes, forcing them to be equinumerous on every invariant set of darts;
injectivity then carries that from darts to boundary vertices. -/
theorem hasFacialBipartitionBalance_toPlaneGraph (hconnected : E.graph.Connected)
    (faceDarts : Face → Finset Dart) (faceEdges : Face → Finset (Sym2 Vertex)) (exterior : Face)
    (hinvariant : ∀ (R : Face) (d : Dart), E.faceMap d ∈ faceDarts R ↔ d ∈ faceDarts R)
    (hinjOn : ∀ R : Face, Set.InjOn E.vertexOf (faceDarts R)) :
    (E.toPlaneGraph hconnected faceDarts faceEdges
      exterior).HasFacialBipartitionBalance := fun coloring R =>
  E.isBalanced_image_of_faceMap_invariant coloring (faceDarts R) (hinvariant R) (hinjOn R)

omit [DecidableEq Vertex] in
/-- **Facial vanishing over an arbitrary abelian group.**

Fix an abelian group `Γ` and an element `g`.  Label one colour class of a proper two-colouring by `g` and
the other by `-g`.  Every `faceMap`-invariant set of darts then sums to zero, because the two classes are
equinumerous there, so the sum is `n • g + n • (-g)`.

This is the group-valued form of facial balance, and it is what Proposition 2.7 of Bowling (2025) needs:
a 2-connected bipartite plane graph is `Γ`-zonal for every abelian `Γ`.  Nothing about `ZMod 3` is used;
the argument only needs `g` and its negative to cancel. -/
theorem sum_colourLabel_eq_zero {Γ : Type*} [AddCommGroup Γ] (coloring : E.graph.Coloring (Fin 2))
    (g : Γ) (faceDarts : Finset Dart)
    (hinvariant : ∀ d, E.faceMap d ∈ faceDarts ↔ d ∈ faceDarts) :
    ∑ d ∈ faceDarts, (if coloring (E.vertexOf d) = 0 then g else -g) = 0 := by
  have hnot : {d ∈ faceDarts | ¬coloring (E.vertexOf d) = 0}
      = {d ∈ faceDarts | coloring (E.vertexOf d) = 1} :=
    Finset.filter_congr fun d _ => by
      have hc : ∀ c : Fin 2, ¬c = 0 ↔ c = 1 := by decide
      exact hc _
  have hpos : ∀ d ∈ {d ∈ faceDarts | coloring (E.vertexOf d) = 0},
      (if coloring (E.vertexOf d) = 0 then g else -g) = g := by
    intro d hd
    simp only [Finset.mem_filter] at hd
    simp [hd.2]
  have hneg : ∀ d ∈ {d ∈ faceDarts | coloring (E.vertexOf d) = 1},
      (if coloring (E.vertexOf d) = 0 then g else -g) = -g := by
    intro d hd
    simp only [Finset.mem_filter] at hd
    simp [hd.2]
  rw [← Finset.sum_filter_add_sum_filter_not faceDarts fun d => coloring (E.vertexOf d) = 0, hnot,
    Finset.sum_congr rfl hpos, Finset.sum_congr rfl hneg, Finset.sum_const, Finset.sum_const,
    E.isBalanced_of_faceMap_invariant coloring faceDarts hinvariant, ← smul_add,
    add_neg_cancel, smul_zero]

end RotationSystem

end ZonalGraphs
