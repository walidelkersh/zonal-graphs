import ZonalGraphs.BipartiteZonal
import Mathlib.GroupTheory.Perm.Fin

namespace ZonalGraphs

/-!
# Three-connected planar graphs

This module isolates the formal implication behind Theorem 2.1.3 of Bowling, *Zonality in Graphs*
(2023): every 3-connected planar zonal graph is absolutely zonal.

The intended input is Whitney's unique-embedding theorem. The current `PlaneRealization` type
certifies each facial boundary cycle, but does not yet say that the faces exhaust a genus-zero
rotation system. Consequently the unrestricted surrogate `WhitneyUniqueEmbedding` is false;
`not_whitneyUniqueEmbedding` gives a counterexample below.

The reusable content remains valid. `PlaneGraph.Iso` describes agreement after relabeling vertices
and regions, and `PlaneGraph.IsZonal.of_iso` proves that zonality is invariant under that
relabeling. The conditional transfer theorem records this dependency, but does not prove Theorem
2.1.3 until realizations certify genuine planar embeddings.
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

/-- Corresponding regions of isomorphic plane graphs have boundaries of equal size.

Consequently the multiset of boundary cardinalities is an invariant of an embedding, which is how
distinct embeddings of one graph are told apart. -/
theorem Iso.card_boundary {P : PlaneGraph V₁ F₁} {Q : PlaneGraph V₂ F₂} (e : P.Iso Q) (R : F₁) :
    (P.boundary R).card = (Q.boundary (e.faceEquiv R)).card := by
  rw [← e.boundary_map R, Finset.card_map]

/-- An isomorphism of plane graphs preserves, for every `n`, the number of regions whose boundary
has exactly `n` vertices.

This is the usable form of the boundary-size invariant: two embeddings of one graph that disagree on
some such count cannot be isomorphic. -/
theorem Iso.card_filter_boundary_card {P : PlaneGraph V₁ F₁} {Q : PlaneGraph V₂ F₂} (e : P.Iso Q)
    (n : ℕ) :
    {R ∈ (Finset.univ : Finset F₁) | (P.boundary R).card = n}.card
      = {S ∈ (Finset.univ : Finset F₂) | (Q.boundary S).card = n}.card := by
  refine Finset.card_bij' (fun R _ => e.faceEquiv R) (fun S _ => e.faceEquiv.symm S) ?_ ?_ ?_ ?_
  · intro R hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR ⊢
    rw [← e.card_boundary R, hR]
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    rw [e.card_boundary (e.faceEquiv.symm S), Equiv.apply_symm_apply, hS]
  · intro R _
    exact e.faceEquiv.symm_apply_apply R
  · intro S _
    exact e.faceEquiv.apply_symm_apply S

/-- An isomorphism of plane graphs preserves the sum of the squares of the region boundary sizes.

This is a sharper invariant than the plain sum, which is often forced to agree for combinatorial
reasons, and it is easier to use than the per-size counts of `Iso.card_filter_boundary_card`, since it
needs no care about distinct regions happening to share a boundary size. -/
theorem Iso.sum_boundary_card_sq {P : PlaneGraph V₁ F₁} {Q : PlaneGraph V₂ F₂} (e : P.Iso Q) :
    ∑ R : F₁, ((P.boundary R).card) ^ 2 = ∑ S : F₂, ((Q.boundary S).card) ^ 2 := by
  rw [← Equiv.sum_comp e.faceEquiv fun S => ((Q.boundary S).card) ^ 2]
  exact Finset.sum_congr rfl fun R _ => by rw [e.card_boundary R]

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

/-- The unrestricted supplied-face surrogate for **Theorem 2.1.2 (Whitney's Theorem)**.

For certified planar embeddings, the intended theorem says that every 3-connected planar graph is
uniquely embeddable. This proposition quantifies over the weaker `PlaneRealization` interface and
is false; see `not_whitneyUniqueEmbedding`. It is retained only to expose the conditional
dependency. -/
def WhitneyUniqueEmbedding : Prop :=
  ∀ (Vertex : Type u) [Fintype Vertex] (G : SimpleGraph Vertex),
    SimpleGraph.IsThreeConnected G → SimpleGraph.IsPlanar G → SimpleGraph.UniquelyEmbeddable G

/-- The conditional transfer underlying **Theorem 2.1.3 (Bowling, 2023)**: unique embeddability
would carry one zonal realization to every realization. -/
theorem threeConnected_zonal_isAbsolutelyZonal (whitney : WhitneyUniqueEmbedding.{u})
    (G : SimpleGraph Vertex) (h3 : SimpleGraph.IsThreeConnected G)
    (hzonal : SimpleGraph.IsZonalGraph G) : SimpleGraph.IsAbsolutelyZonal G := by
  obtain ⟨E, hE⟩ := hzonal
  exact SimpleGraph.IsZonalGraph.isAbsolutelyZonal ⟨E, hE⟩ (whitney Vertex G h3 ⟨E⟩)

/-!
## Why the Whitney carrier cannot be proved against `PlaneRealization`

`PlaneRealization` certifies that every face of a two-connected graph has a cyclic boundary, but it
does not yet certify that the listed faces exhaust one planar embedding. The same triangular cycle
of `K₄` can therefore be supplied once or twice, giving alleged realizations with different numbers
of faces. Thus `WhitneyUniqueEmbedding` is false for the current interface, independently of the
genuine topological Whitney theorem.
-/

/-- The triangular boundary used by both invalid `K₄` realizations. -/
def invalidK4Boundary : Finset (Fin 4) := {0, 1, 2}

/-- The cyclic successor `0 ↦ 1 ↦ 2 ↦ 0`, fixing vertex `3`. -/
def invalidK4BoundaryCycle : Equiv.Perm (Fin 4) := (2 : Fin 4).cycleRange

/-- The chosen successor is one cycle. -/
theorem invalidK4BoundaryCycle_isCycle : invalidK4BoundaryCycle.IsCycle :=
  Fin.isCycle_cycleRange (by decide)

/-- Its support is exactly the supplied triangular boundary, independently of the chosen equality
decision procedure. -/
theorem invalidK4BoundaryCycle_support (inst : DecidableEq (Fin 4)) :
    @Equiv.Perm.support (Fin 4) inst (Fin.fintype 4) invalidK4BoundaryCycle =
      invalidK4Boundary := by
  have hinst : inst = instDecidableEqFin 4 := Subsingleton.elim _ _
  subst inst
  decide

/-- `K₄` with one alleged triangular face. -/
def invalidK4UnitPlane : PlaneGraph (Fin 4) Unit where
  graph := ⊤
  connected := SimpleGraph.connected_top
  boundary := fun _ => invalidK4Boundary
  boundaryEdges := fun _ => ∅
  exterior := ()

/-- `K₄` with the same alleged triangular face listed twice. -/
def invalidK4BoolPlane : PlaneGraph (Fin 4) Bool where
  graph := ⊤
  connected := SimpleGraph.connected_top
  boundary := fun _ => invalidK4Boundary
  boundaryEdges := fun _ => ∅
  exterior := false

/-- The one-face data satisfies the structural facial-cycle contract. -/
theorem invalidK4UnitPlane_hasFacialBoundaryCycles :
    invalidK4UnitPlane.HasFacialBoundaryCycles := by
  classical
  letI : DecidableEq (Fin 4) := Classical.decEq _
  change ∀ _ : Unit, ∃ next : Equiv.Perm (Fin 4),
    next.IsCycle ∧ next.support = invalidK4Boundary ∧
      ∀ v ∈ invalidK4Boundary, (⊤ : SimpleGraph (Fin 4)).Adj v (next v)
  intro R
  have hsupport : invalidK4BoundaryCycle.support = invalidK4Boundary :=
    invalidK4BoundaryCycle_support (inferInstance : DecidableEq (Fin 4))
  refine ⟨invalidK4BoundaryCycle, invalidK4BoundaryCycle_isCycle, hsupport,
    fun v hv => ?_⟩
  rw [SimpleGraph.top_adj]
  have hmem : v ∈ invalidK4BoundaryCycle.support := by
    rw [hsupport]
    exact hv
  exact (Equiv.Perm.mem_support.mp hmem).symm

/-- The duplicated two-face data also satisfies the structural facial-cycle contract. -/
theorem invalidK4BoolPlane_hasFacialBoundaryCycles :
    invalidK4BoolPlane.HasFacialBoundaryCycles := by
  classical
  letI : DecidableEq (Fin 4) := Classical.decEq _
  change ∀ _ : Bool, ∃ next : Equiv.Perm (Fin 4),
    next.IsCycle ∧ next.support = invalidK4Boundary ∧
      ∀ v ∈ invalidK4Boundary, (⊤ : SimpleGraph (Fin 4)).Adj v (next v)
  intro R
  have hsupport : invalidK4BoundaryCycle.support = invalidK4Boundary :=
    invalidK4BoundaryCycle_support (inferInstance : DecidableEq (Fin 4))
  refine ⟨invalidK4BoundaryCycle, invalidK4BoundaryCycle_isCycle, hsupport,
    fun v hv => ?_⟩
  rw [SimpleGraph.top_adj]
  have hmem : v ∈ invalidK4BoundaryCycle.support := by
    rw [hsupport]
    exact hv
  exact (Equiv.Perm.mem_support.mp hmem).symm

/-- The one-face supplied data packaged as a `PlaneRealization`. -/
def invalidK4UnitRealization : PlaneRealization (⊤ : SimpleGraph (Fin 4)) where
  Face := Unit
  instFintypeFace := inferInstance
  plane := invalidK4UnitPlane
  graph_eq := rfl
  facial_cycles_of_twoConnected := by
    intro _
    exact invalidK4UnitPlane_hasFacialBoundaryCycles

/-- The two-face supplied data packaged as a `PlaneRealization`. -/
def invalidK4BoolRealization : PlaneRealization (⊤ : SimpleGraph (Fin 4)) where
  Face := Bool
  instFintypeFace := inferInstance
  plane := invalidK4BoolPlane
  graph_eq := rfl
  facial_cycles_of_twoConnected := by
    intro _
    exact invalidK4BoolPlane_hasFacialBoundaryCycles

/-- `K₄` satisfies this development's deletion-based definition of three-connectivity. -/
theorem completeGraph_fin_four_isThreeConnected :
    SimpleGraph.IsThreeConnected (⊤ : SimpleGraph (Fin 4)) := by
  refine ⟨by decide, fun u v => ?_⟩
  obtain ⟨w, hwu, hwv⟩ := Fin.exists_ne_and_ne_of_two_lt u v (by omega)
  letI : Nonempty ({u, v}ᶜ : Set (Fin 4)) := ⟨⟨w, by simp [hwu, hwv]⟩⟩
  rw [SimpleGraph.induce_top]
  exact SimpleGraph.connected_top

/-- The two supplied realizations are not isomorphic because their face types have different
cardinalities. -/
theorem completeGraph_fin_four_not_uniquelyEmbeddable :
    ¬ SimpleGraph.UniquelyEmbeddable (⊤ : SimpleGraph (Fin 4)) := by
  intro h
  obtain ⟨e⟩ := h invalidK4UnitRealization invalidK4BoolRealization
  have hcard := Fintype.card_congr e.faceEquiv
  change Fintype.card Unit = Fintype.card Bool at hcard
  norm_num at hcard

/-- The unrestricted Whitney carrier is false for the supplied-face realization interface. -/
theorem not_whitneyUniqueEmbedding : ¬ WhitneyUniqueEmbedding.{0} := by
  intro h
  have huniq := h (Fin 4) (⊤ : SimpleGraph (Fin 4)) completeGraph_fin_four_isThreeConnected
    ⟨invalidK4UnitRealization⟩
  exact completeGraph_fin_four_not_uniquelyEmbeddable huniq

end ZonalGraphs
