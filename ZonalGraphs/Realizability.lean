import ZonalGraphs.EmbeddingCounts
import ZonalGraphs.RotationToPlane

namespace ZonalGraphs

/-!
# Which plane graphs come from an actual embedding

`PlaneGraph` accepts any face assignment, which is what lets the results in this project be stated without a
theory of planarity. It is also why a claim of the form "this graph has at least `m` distinct planar embeddings"
cannot be stated faithfully against it: a family of arbitrary face assignments satisfies such a claim vacuously.

`IsRealizable` closes that gap. A plane graph is realizable when its faces are, up to relabelling, the orbits of
`faceMap` for some rotation system on the same graph. `RotationToPlane` already builds a `PlaneGraph` whose faces
are computed that way, so realizability says exactly that the given face data agrees with some genuine embedding
rather than being posited.

Darts are indexed by `Fin d` for some `d`, which costs nothing and avoids carrying a `Fintype` instance through an
existential.

Counting embeddings should quantify over realizable plane graphs. That is the missing ingredient for Corollaries
2.5.10 and 2.5.12 and Theorem 2.5.13: their content is a count of genuine embeddings, and without realizability a
count is satisfied by face assignments that no embedding produces.
-/

universe u v

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face]

/-- A plane graph is *realizable* when its face data agrees, up to relabelling of the faces, with the orbits of
`faceMap` for some rotation system on the same graph. -/
def IsRealizable (P : PlaneGraph Vertex Face) : Prop :=
  ∃ (d : ℕ) (E : RotationSystem Vertex (Fin d)) (φ : Face ≃ E.Face),
    E.graph = P.graph ∧ ∀ R : Face, P.boundary R = E.boundary (φ R)

/-- The plane graph built from a rotation system is realizable, by the identity relabelling. -/
theorem isRealizable_toPlaneGraphOfOrbits {d : ℕ} (E : RotationSystem Vertex (Fin d))
    [Nonempty (Fin d)] (hconn : E.graph.Connected) :
    (E.toPlaneGraphOfOrbits hconn).IsRealizable :=
  ⟨d, E, Equiv.refl _, rfl, fun _ => rfl⟩

/-- Realizability transfers along a relabelling of the faces that preserves boundaries. -/
theorem IsRealizable.of_boundary_eq {P Q : PlaneGraph Vertex Face} (h : P.IsRealizable)
    (hgraph : Q.graph = P.graph) (hbd : ∀ R, Q.boundary R = P.boundary R) : Q.IsRealizable := by
  obtain ⟨d, E, φ, hE, hb⟩ := h
  exact ⟨d, E, φ, hE.trans hgraph.symm, fun R => (hbd R).trans (hb R)⟩

end PlaneGraph

variable {Vertex : Type u} [Fintype Vertex]

/-- A graph has at least `m` distinct zonal planar embeddings when some family of `m` *realizable* plane graphs on
it is pairwise non-isomorphic with every member zonal.

This is the form Corollaries 2.5.10 and 2.5.12 and Theorem 2.5.13 need. Dropping realizability would make the
claim vacuous, since arbitrary face assignments would qualify. -/
def SimpleGraph.HasAtLeastRealizableZonalEmbeddings (G : SimpleGraph Vertex) (m : ℕ) : Prop :=
  ∃ (r : ℕ) (P : Fin m → PlaneGraph Vertex (Fin r)),
    (∀ t, (P t).graph = G) ∧ (∀ t, (P t).IsRealizable) ∧ (∀ t, (P t).IsZonal) ∧
      ∀ t t', t ≠ t' → ¬ Nonempty ((P t).Iso (P t'))

/-- Realizable counts are counts: forgetting realizability weakens the claim. -/
theorem SimpleGraph.HasAtLeastRealizableZonalEmbeddings.toHasAtLeast {G : SimpleGraph Vertex} {m : ℕ}
    (h : SimpleGraph.HasAtLeastRealizableZonalEmbeddings G m) :
    SimpleGraph.HasAtLeastZonalEmbeddings G m := by
  obtain ⟨r, P, hgraph, _, hzonal, hiso⟩ := h
  exact ⟨r, P, hgraph, hzonal, hiso⟩

end ZonalGraphs
