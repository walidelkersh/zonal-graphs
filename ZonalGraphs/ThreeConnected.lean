import ZonalGraphs.BipartiteZonal

namespace ZonalGraphs

/-!
# Three-connected planar graphs

This module formalizes Theorem 2.1.3 of Bowling, *Zonality in Graphs* (2023): every 3-connected
planar zonal graph is absolutely zonal, so no 3-connected planar graph is conditionally zonal.

The mathematical input is Whitney's Theorem (2.1.2): a 3-connected planar graph is uniquely
embeddable in the plane.  Whitney's theorem is a statement about drawings in the plane and lies
outside the combinatorial embedding interface used here, so it is recorded as the named proposition
`WhitneyUniqueEmbedding` and carried as an explicit hypothesis, keeping the logical dependency
visible.

Everything else is genuine content proved here: `PlaneGraph.Iso` says that two embeddings agree
after relabeling vertices and regions, and `PlaneGraph.IsZonal.of_iso` shows that zonality is
invariant under such a relabeling.  Given unique embeddability, one zonal embedding therefore
forces every embedding to be zonal.
-/

universe u v u' v'

namespace PlaneGraph

variable {V₁ : Type u} {F₁ : Type v} {V₂ : Type u'} {F₂ : Type v'}
  [Fintype V₁] [Fintype F₁] [Fintype V₂] [Fintype F₂]

/-- An isomorphism of plane graphs: an isomorphism of the underlying graphs together with a
matching relabeling of the regions that carries facial boundaries to facial boundaries.

Only the facial *vertex* sets are constrained, since these are what the value of a region depends
on. -/
structure Iso (P : PlaneGraph V₁ F₁) (Q : PlaneGraph V₂ F₂) where
  /-- The relabeling of vertices, an isomorphism of the underlying graphs. -/
  graphIso : P.graph ≃g Q.graph
  /-- The matching relabeling of regions. -/
  faceEquiv : F₁ ≃ F₂
  /-- Corresponding regions have corresponding boundary vertices. -/
  boundary_map : ∀ R : F₁,
    (P.boundary R).map graphIso.toEquiv.toEmbedding = Q.boundary (faceEquiv R)

/-- Zonality is invariant under an isomorphism of plane graphs: transport a zonal labeling along
the vertex relabeling. -/
theorem IsZonal.of_iso {P : PlaneGraph V₁ F₁} {Q : PlaneGraph V₂ F₂} (hP : P.IsZonal)
    (e : P.Iso Q) : Q.IsZonal := by
  obtain ⟨labeling, hlabeling⟩ := hP
  refine ⟨labeling ∘ e.graphIso.toEquiv.symm, ?_⟩
  intro R
  have hboundary : Q.boundary R =
      (P.boundary (e.faceEquiv.symm R)).map e.graphIso.toEquiv.toEmbedding := by
    rw [e.boundary_map, Equiv.apply_symm_apply]
  have hzero := hlabeling (e.faceEquiv.symm R)
  simp only [zoneValue, hboundary, Finset.sum_map, Equiv.coe_toEmbedding, Function.comp_apply,
    Equiv.symm_apply_apply]
  simpa [zoneValue] using hzero

end PlaneGraph

variable {Vertex : Type u} [Fintype Vertex]

/-- A finite graph is 3-connected when it has at least four vertices and deleting any two vertices
leaves a connected induced graph. -/
def SimpleGraph.IsThreeConnected (G : SimpleGraph Vertex) : Prop :=
  4 ≤ Fintype.card Vertex ∧ ∀ u v : Vertex, (G.induce ({u, v}ᶜ : Set Vertex)).Connected

/-- An abstract graph is zonal when at least one of its plane realizations is zonal.  A graph that
is zonal but not absolutely zonal is called *conditionally* zonal. -/
def SimpleGraph.IsZonalGraph (G : SimpleGraph Vertex) : Prop :=
  ∃ E : PlaneRealization G, E.plane.IsZonal

/-- A graph is uniquely embeddable in the plane when any two of its plane realizations are
isomorphic as plane graphs. -/
def SimpleGraph.UniquelyEmbeddable (G : SimpleGraph Vertex) : Prop :=
  ∀ E F : PlaneRealization G, Nonempty (E.plane.Iso F.plane)

/-- For a uniquely embeddable graph, one zonal embedding forces every embedding to be zonal. -/
theorem SimpleGraph.IsZonalGraph.isAbsolutelyZonal {G : SimpleGraph Vertex}
    (hzonal : SimpleGraph.IsZonalGraph G) (huniq : SimpleGraph.UniquelyEmbeddable G) :
    SimpleGraph.IsAbsolutelyZonal G := by
  obtain ⟨E, hE⟩ := hzonal
  refine ⟨⟨E⟩, ?_⟩
  intro F
  obtain ⟨e⟩ := huniq E F
  exact hE.of_iso e

/-- **Theorem 2.1.2 (Whitney's Theorem).** Every 3-connected planar graph is uniquely embeddable
in the plane.

This is a topological statement about drawings in the plane, outside the combinatorial embedding
interface used in this development.  It is recorded here as a named proposition and carried as an
explicit hypothesis by the results depending on it. -/
def WhitneyUniqueEmbedding : Prop :=
  ∀ (Vertex : Type u) [Fintype Vertex] (G : SimpleGraph Vertex),
    SimpleGraph.IsThreeConnected G → SimpleGraph.IsPlanar G → SimpleGraph.UniquelyEmbeddable G

/-- **Theorem 2.1.3 (Bowling, 2023).** Every 3-connected planar zonal graph is absolutely zonal.
Consequently no 3-connected planar graph is conditionally zonal. -/
theorem threeConnected_zonal_isAbsolutelyZonal (whitney : WhitneyUniqueEmbedding.{u})
    (G : SimpleGraph Vertex) (h3 : SimpleGraph.IsThreeConnected G)
    (hzonal : SimpleGraph.IsZonalGraph G) : SimpleGraph.IsAbsolutelyZonal G := by
  obtain ⟨E, hE⟩ := hzonal
  exact SimpleGraph.IsZonalGraph.isAbsolutelyZonal ⟨E, hE⟩ (whitney Vertex G h3 ⟨E⟩)

end ZonalGraphs
