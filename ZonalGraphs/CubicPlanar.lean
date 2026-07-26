import ZonalGraphs.FourColor
import ZonalGraphs.ThreeConnected

namespace ZonalGraphs

/-!
# Bridgeless cubic planar graphs

This module formalizes Theorem 2.1.4 of Bowling, *Zonality in Graphs* (2023): every connected
bridgeless cubic planar graph is absolutely zonal.

The mathematical input is Theorem 1.3.2 (restated as Theorem 4.1.1): a connected cubic plane graph
is zonal if and only if it is bridgeless.  That equivalence is of the same strength as the Four
Color Theorem, so it is recorded as the named proposition `CubicZonalIffBridgeless` and carried as
an explicit hypothesis, exactly as `PlaneGraph.FourColorZonalStatement` records the four-coloring
formulation.

The content proved here is that the hypotheses of Theorem 2.1.4 are embedding-independent: being
cubic and being bridgeless are properties of the underlying graph, so they hold of *every* plane
realization, and Theorem 1.3.2 then makes every realization zonal.  Connectedness needs no
hypothesis, as `PlaneGraph` carries it as a field.
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

/-- **Theorem 1.3.2 (= Theorem 4.1.1).** A connected cubic plane graph is zonal if and only if it
is bridgeless.

The forward implication is elementary, but the converse is of the same strength as the Four Color
Theorem.  The equivalence is therefore recorded as a named proposition rather than assumed as an
axiom, and is carried as an explicit hypothesis by the results depending on it. -/
def CubicZonalIffBridgeless : Prop :=
  ∀ (V : Type u) (F : Type v) [Fintype V] [Fintype F] (P : PlaneGraph V F),
    P.IsCubic → (P.IsZonal ↔ P.IsBridgeless)

/-- **Theorem 2.1.4 (Bowling, 2023).** Every connected bridgeless cubic planar graph is absolutely
zonal: its hypotheses are embedding-independent, so Theorem 1.3.2 applies to every realization. -/
theorem bridgeless_cubic_planar_isAbsolutelyZonal (hzonal : CubicZonalIffBridgeless.{u, u})
    (G : SimpleGraph Vertex) (hcubic : SimpleGraph.IsCubicGraph G)
    (hbridgeless : SimpleGraph.IsBridgelessGraph G) (hplanar : SimpleGraph.IsPlanar G) :
    SimpleGraph.IsAbsolutelyZonal G := by
  refine ⟨hplanar, ?_⟩
  intro E
  exact (hzonal Vertex E.Face E.plane (hcubic.plane E)).mpr (hbridgeless.plane E)

end ZonalGraphs
