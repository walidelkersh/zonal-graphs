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

end RotationSystem

end ZonalGraphs
