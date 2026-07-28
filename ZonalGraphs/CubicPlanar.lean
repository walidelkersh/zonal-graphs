import ZonalGraphs.FourColor
import ZonalGraphs.ThreeConnected

namespace ZonalGraphs

/-!
# Bridgeless cubic planar graphs

This module isolates the formal implication behind Theorem 2.1.4 of Bowling, *Zonality in Graphs*
(2023): every connected bridgeless cubic planar graph is absolutely zonal.

The intended mathematical input is Theorem 1.3.2 (restated as Theorem 4.1.1): a connected cubic
plane graph is zonal if and only if it is bridgeless. Its converse has the strength of the Four
Color Theorem. The current `PlaneGraph` type, however, accepts arbitrary supplied face data, so the
unrestricted surrogate `CubicZonalIffBridgeless` is false; `not_cubicZonalIffBridgeless` gives a
counterexample below.

What remains valid is the dependency calculation: cubicity and bridgelessness belong to the
underlying graph and hence hold in every supplied realization. The conditional transfer theorem is
kept for reuse, but it is not a formalization of Theorem 2.1.4 until realizations certify their face
data as planar embeddings.
-/

universe u v

variable {Vertex : Type u} [Fintype Vertex]

/-- A graph is cubic when it is regular of degree three. -/
noncomputable def SimpleGraph.IsCubicGraph (G : SimpleGraph Vertex) : Prop := by
  letI := Classical.decRel G.Adj
  exact G.IsRegularOfDegree 3

/-- A graph is bridgeless when none of its edges is a bridge, using Mathlib's
`SimpleGraph.IsBridge`. -/
def SimpleGraph.IsBridgelessGraph (G : SimpleGraph Vertex) : Prop :=
  ∀ e, ¬ G.IsBridge e

/-- Cubicity depends only on the underlying graph, hence holds of every plane realization. -/
theorem SimpleGraph.IsCubicGraph.plane {G : SimpleGraph Vertex}
    (hcubic : SimpleGraph.IsCubicGraph G) (E : PlaneRealization G) : E.plane.IsCubic := by
  obtain ⟨_, _, _, rfl, _⟩ := E
  exact hcubic

/-- Being bridgeless depends only on the underlying graph, hence holds of every plane
realization. -/
theorem SimpleGraph.IsBridgelessGraph.plane {G : SimpleGraph Vertex}
    (hbridgeless : SimpleGraph.IsBridgelessGraph G) (E : PlaneRealization G) :
    E.plane.IsBridgeless := by
  obtain ⟨_, _, _, rfl, _⟩ := E
  exact hbridgeless

/-- The unrestricted supplied-face surrogate for **Theorem 1.3.2 (= Theorem 4.1.1)**.

For certified plane embeddings, the intended equivalence says that a connected cubic plane graph
is zonal exactly when it is bridgeless. This unrestricted proposition is false for `PlaneGraph`;
see `not_cubicZonalIffBridgeless`. It is retained only to expose the conditional dependency. -/
def CubicZonalIffBridgeless : Prop :=
  ∀ (V : Type u) (F : Type v) [Fintype V] [Fintype F] (P : PlaneGraph V F),
    P.IsCubic → (P.IsZonal ↔ P.IsBridgeless)

/-- The conditional transfer underlying **Theorem 2.1.4 (Bowling, 2023)**: if the unrestricted
carrier held, its embedding-independent hypotheses would make every realization zonal. -/
theorem bridgeless_cubic_planar_isAbsolutelyZonal (hzonal : CubicZonalIffBridgeless.{u, u})
    (G : SimpleGraph Vertex) (hcubic : SimpleGraph.IsCubicGraph G)
    (hbridgeless : SimpleGraph.IsBridgelessGraph G) (hplanar : SimpleGraph.IsPlanar G) :
    SimpleGraph.IsAbsolutelyZonal G := by
  refine ⟨hplanar, ?_⟩
  intro E
  exact (hzonal Vertex E.Face E.plane (hcubic.plane E)).mpr (hbridgeless.plane E)

/-!
## Why the carrier cannot be proved against `PlaneGraph`

`PlaneGraph` intentionally accepts supplied face data without validating it against the graph. The
unrestricted proposition `CubicZonalIffBridgeless` is therefore false: give `K₄` one alleged face
whose boundary is a singleton. The graph is cubic and bridgeless, but that face can never sum to zero
under a nonzero vertex labeling.
-/

/-- `K₄` equipped with deliberately invalid supplied face data. This is not a geometric plane
embedding; it witnesses the exact gap between the `PlaneGraph` interface and the intended theorem. -/
def invalidK4PlaneGraph : PlaneGraph (Fin 4) Unit where
  graph := ⊤
  connected := SimpleGraph.connected_top
  boundary := fun _ => {0}
  boundaryEdges := fun _ => ∅
  exterior := ()

/-- The underlying `K₄` of `invalidK4PlaneGraph` is cubic. -/
theorem invalidK4PlaneGraph_isCubic : invalidK4PlaneGraph.IsCubic := by
  classical
  unfold PlaneGraph.IsCubic SimpleGraph.IsRegularOfDegree
  intro v
  simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, invalidK4PlaneGraph]
  fin_cases v <;> decide

/-- The underlying `K₄` of `invalidK4PlaneGraph` is bridgeless. -/
theorem invalidK4PlaneGraph_isBridgeless : invalidK4PlaneGraph.IsBridgeless := by
  intro e
  refine Sym2.inductionOn e fun u v hbridge => ?_
  obtain ⟨w, hwu, hwv⟩ := Fin.exists_ne_and_ne_of_two_lt u v (by omega)
  let p : (⊤ : SimpleGraph (Fin 4)).Walk u v :=
    .cons (by simpa using hwu.symm) (.cons (by simpa using hwv) .nil)
  have hmem := (SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges.mp hbridge).2 p
  simp [invalidK4PlaneGraph, p] at hmem
  rcases hmem with (hvw | ⟨huw, _⟩) | huw | ⟨_, hvw⟩
  · exact hwv hvw.symm
  · exact hwu huw.symm
  · exact hwu huw.symm
  · exact hwv hvw.symm

/-- The singleton alleged face makes `invalidK4PlaneGraph` non-zonal. -/
theorem invalidK4PlaneGraph_not_isZonal : ¬ invalidK4PlaneGraph.IsZonal := by
  rintro ⟨labeling, hlabeling⟩
  have hface := hlabeling ()
  simp [PlaneGraph.zoneValue, invalidK4PlaneGraph] at hface
  exact (labeling 0).2 hface

/-- The unrestricted carrier is false for the supplied-face interface. Any faithful version must
quantify only over face data certified to come from a planar embedding. -/
theorem not_cubicZonalIffBridgeless : ¬ CubicZonalIffBridgeless.{0, 0} := by
  intro h
  have hzonal :=
    (h (Fin 4) Unit invalidK4PlaneGraph invalidK4PlaneGraph_isCubic).mpr
      invalidK4PlaneGraph_isBridgeless
  exact invalidK4PlaneGraph_not_isZonal hzonal

end ZonalGraphs
