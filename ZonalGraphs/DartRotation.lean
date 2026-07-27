import ZonalGraphs.Realizability

namespace ZonalGraphs

/-!
# Rotation systems from a single permutation

Four of the six fields of `RotationSystem` are forced by the graph and need not be invented. Mathlib's
`SimpleGraph.Dart` is the type of directed edges, `SimpleGraph.Dart.symm` reverses one and is involutive by
`Dart.symm_involutive`, and a dart's two ends are adjacent by `Dart.adj`. Only the rotation is embedding data.

`RotationSystem.ofRotation` packages that: an embedding of a fixed graph is specified by one permutation of its
darts that fixes each dart's tail. Everything else is supplied.

This is what the remaining work on Corollaries 2.5.10 and 2.5.12 and Theorem 2.5.13 has to produce. Those need
realizable embeddings of `Gn`, so by `isRealizable_toPlaneGraphOfOrbits` it is enough to give a rotation for each
`k`, and the faces then come out as the `faceMap` orbits rather than being asserted.
-/

universe u

variable {Vertex : Type u} [Fintype Vertex] (G : SimpleGraph Vertex) [DecidableRel G.Adj]

/-- **An embedding of a fixed graph is one vertex-preserving permutation of its darts.**

Reversal, the tail map and the adjacency of a dart's ends are all determined by the graph, so a rotation system
over `SimpleGraph.Dart` needs only the rotation. -/
def RotationSystem.ofRotation (rot : Equiv.Perm G.Dart) (hrot : ∀ d : G.Dart, (rot d).fst = d.fst) :
    RotationSystem Vertex G.Dart where
  graph := G
  vertexOf := fun d => d.fst
  dartRev := Function.Involutive.toPerm _ SimpleGraph.Dart.symm_involutive
  rotate := rot
  dartRev_involutive := SimpleGraph.Dart.symm_symm
  vertexOf_rotate := hrot
  adj_vertexOf_dartRev := fun d => d.adj

@[simp] theorem RotationSystem.ofRotation_graph (rot : Equiv.Perm G.Dart)
    (hrot : ∀ d : G.Dart, (rot d).fst = d.fst) :
    (RotationSystem.ofRotation G rot hrot).graph = G := rfl

@[simp] theorem RotationSystem.ofRotation_vertexOf (rot : Equiv.Perm G.Dart)
    (hrot : ∀ d : G.Dart, (rot d).fst = d.fst) (d : G.Dart) :
    (RotationSystem.ofRotation G rot hrot).vertexOf d = d.fst := rfl

/-- Advancing along a face, in this presentation: reverse the dart, then rotate. -/
theorem RotationSystem.ofRotation_faceMap (rot : Equiv.Perm G.Dart)
    (hrot : ∀ d : G.Dart, (rot d).fst = d.fst) (d : G.Dart) :
    (RotationSystem.ofRotation G rot hrot).faceMap d = rot d.symm := rfl

end ZonalGraphs
