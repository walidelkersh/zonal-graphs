import ZonalGraphs.Basic
import Mathlib.Data.ZMod.Basic

namespace ZonalGraphs

/-!
# Zonal and inner zonal labelings

These definitions formalize the foundational notions in Bowling, *Zonality in Graphs* (2023).
A vertex receives one of the two nonzero elements of `ZMod 3`.  The value of a region is the sum
of the labels of the vertices on its boundary.  A labeling is zonal when every region has value
zero, and inner zonal when there is at most one exceptional region.  For a fixed plane embedding,
the exceptional region can be selected as the exterior region, so the latter condition is
equivalent to requiring all interior regions to have value zero.
-/

universe u v

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face]

/-- The two permitted vertex labels, namely the nonzero elements of `ZMod 3`. -/
abbrev ZonalLabel := {x : ZMod 3 // x ≠ 0}

/-- A labeling of the vertices of a plane graph by the nonzero elements of `ZMod 3`. -/
abbrev VertexLabeling (Vertex : Type u) := Vertex → ZonalLabel

namespace PlaneGraph

variable (P : PlaneGraph Vertex Face)

/-- The value of a region (or zone): the sum in `ZMod 3` of the labels of the vertices on its
boundary. -/
def zoneValue (labeling : VertexLabeling Vertex) (R : Face) : ZMod 3 :=
  ∑ v ∈ P.boundary R, (labeling v : ZMod 3)

/-- A zonal labeling assigns nonzero elements of `ZMod 3` to the vertices so that every region
has value zero. -/
def IsZonalLabeling (labeling : VertexLabeling Vertex) : Prop :=
  ∀ R : Face, P.zoneValue labeling R = 0

/-- A plane graph is zonal when it possesses a zonal labeling. -/
def IsZonal : Prop :=
  ∃ labeling : VertexLabeling Vertex, P.IsZonalLabeling labeling

/-- An inner zonal labeling has region value zero with at most one exception.

This is the embedding-independent wording used in the dissertation: after choosing the exceptional
region as exterior, it says exactly that every interior region has value zero. -/
def IsInnerZonalLabeling (labeling : VertexLabeling Vertex) : Prop :=
  ∃ exceptional : Face, ∀ R : Face, R ≠ exceptional → P.zoneValue labeling R = 0

/-- A plane graph is inner zonal when it possesses an inner zonal labeling. -/
def IsInnerZonal : Prop :=
  ∃ labeling : VertexLabeling Vertex, P.IsInnerZonalLabeling labeling

/-- The equivalent fixed-embedding formulation: all interior regions have value zero. -/
def IsInteriorZonalLabeling [DecidableEq Face] (labeling : VertexLabeling Vertex) : Prop :=
  ∀ R : Face, P.IsInterior R → P.zoneValue labeling R = 0

end PlaneGraph

end ZonalGraphs
