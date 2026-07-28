import ZonalGraphs.Definitions
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Logic.Equiv.Basic

namespace ZonalGraphs

/-!
# Rotation systems and facial colour balance

Mathlib has no notion of a planar graph, a combinatorial embedding, or the faces of an embedding.
`PlaneGraph` therefore records face data as an interface, which leaves geometric facts about
embeddings with nothing to be derived from.  This module supplies the missing structure for one such
fact.

A `RotationSystem` is the standard combinatorial model of an embedding.  Its *darts* are the
directed edges; the involution `dartRev` reverses a dart, and the permutation `rotate` advances a
dart to the next one around its own vertex.  Their composite `faceMap = rotate ∘ dartRev` advances a
dart to the next dart along the face on its left, so the faces of the embedding are exactly the
orbits of `faceMap`.

The point of the module is `RotationSystem.isBalanced_of_faceMap_invariant`: for a proper
two-colouring, every `faceMap`-invariant set of darts carries equally many darts of each colour.
This is the fact that Proposition 2.1.1 needs about the boundary of a region of a bipartite plane
graph, and it holds with *no* planarity hypothesis whatsoever.  The reason is short: `dartRev d`
points at the other end of the same edge, so its colour differs, while `rotate` never changes a
dart's vertex.  Hence `faceMap` exchanges the two colour classes, and a permutation exchanging two
classes of a finite invariant set forces them to have equal size.
-/

universe u w

/-- A combinatorial embedding of a finite graph, in the rotation-system model.

`dartRev` pairs each dart with its reverse, and `rotate` cyclically advances a dart around its
vertex.  The faces of the embedding are the orbits of `faceMap = rotate ∘ dartRev`. -/
structure RotationSystem (Vertex : Type u) (Dart : Type w) [Fintype Vertex] [Fintype Dart] where
  /-- The embedded graph. -/
  graph : SimpleGraph Vertex
  /-- The vertex a dart points out of. -/
  vertexOf : Dart → Vertex
  /-- Reversal of darts, exchanging the two ends of an edge. -/
  dartRev : Equiv.Perm Dart
  /-- Rotation of darts, advancing a dart around its own vertex. -/
  rotate : Equiv.Perm Dart
  /-- Reversing a dart twice is the identity. -/
  dartRev_involutive : ∀ d, dartRev (dartRev d) = d
  /-- Rotating a dart keeps it at the same vertex. -/
  vertexOf_rotate : ∀ d, vertexOf (rotate d) = vertexOf d
  /-- A dart and its reverse span an edge of the graph. -/
  adj_vertexOf_dartRev : ∀ d, graph.Adj (vertexOf d) (vertexOf (dartRev d))

namespace RotationSystem

variable {Vertex : Type u} {Dart : Type w} [Fintype Vertex] [Fintype Dart]
  (E : RotationSystem Vertex Dart)

/-- The next dart along the face lying to the left of a given dart. -/
def faceMap : Equiv.Perm Dart := E.dartRev.trans E.rotate

/-- `faceMap` first reverses a dart and then rotates it. -/
theorem faceMap_apply (d : Dart) : E.faceMap d = E.rotate (E.dartRev d) := rfl

/-- Advancing along a face moves to the other end of the current edge. -/
theorem vertexOf_faceMap (d : Dart) : E.vertexOf (E.faceMap d) = E.vertexOf (E.dartRev d) := by
  rw [faceMap_apply, E.vertexOf_rotate]

/-- Under a proper colouring, advancing along a face changes the colour, because the next dart sits
at the other end of the current edge. -/
theorem coloring_vertexOf_faceMap_ne {Colour : Type*} (coloring : E.graph.Coloring Colour)
    (d : Dart) :
    coloring (E.vertexOf (E.faceMap d)) ≠ coloring (E.vertexOf d) := by
  rw [E.vertexOf_faceMap]
  exact (coloring.valid (E.adj_vertexOf_dartRev d)).symm

/-- Reversal has no fixed dart.  This is not assumed: a dart and its reverse have adjacent endpoints, and
adjacency in a simple graph is irreflexive, so the endpoints differ and the darts cannot coincide. -/
theorem dartRev_ne (d : Dart) : E.dartRev d ≠ d := by
  intro hfix
  have hadj := E.adj_vertexOf_dartRev d
  rw [hfix] at hadj
  exact E.graph.irrefl hadj

include E in
/-- **The dart count is even, and half of it is the number of edges.**

Reversal is a fixed-point-free involution, so it pairs the darts off.  This is the edge count entering
Euler's identity: an embedding has `Fintype.card Dart / 2` edges. -/
theorem two_dvd_card_dart [DecidableEq Dart] : 2 ∣ Fintype.card Dart := by
  have hsq : E.dartRev ^ 2 = 1 := by
    ext d
    simp [pow_two, E.dartRev_involutive]
  have hsupport : E.dartRev.support = Finset.univ := by
    ext d
    simp [Equiv.Perm.mem_support, E.dartRev_ne d]
  have hdvd := Equiv.Perm.two_dvd_card_support hsq
  rwa [hsupport, Finset.card_univ] at hdvd

/-- The number of edges of an embedding: half the darts, well defined by `two_dvd_card_dart`. -/
def edgeCount [DecidableEq Dart] (_E : RotationSystem Vertex Dart) : ℕ := Fintype.card Dart / 2

include E in
/-- Twice the edge count is the dart count. -/
theorem two_mul_edgeCount [DecidableEq Dart] : 2 * E.edgeCount = Fintype.card Dart := by
  rw [edgeCount, Nat.mul_div_cancel' E.two_dvd_card_dart]

/-- The Euler characteristic of an embedding, given the number of its faces: vertices minus edges plus
faces.

This is where the Euler identity has to be confronted honestly. Genus is *defined* by
`χ = 2 - 2g`, so declaring an embedding planar when `g = 0` makes `χ = 2` a definition rather than a
theorem, and Theorem 1.1.1 of the dissertation is then unprovable as stated. Getting it as a theorem
requires planarity fixed independently of `χ`, either topologically in the plane, which wants the Jordan
curve theorem, or combinatorially by excluded minors, which wants Kuratowski. Neither exists in mathlib.

What is recorded here is the arithmetic: the counts and the fact that the edge count is genuinely half the
darts. The classification that would turn `χ` into a statement about planarity is not. -/
def eulerChar [DecidableEq Dart] (E : RotationSystem Vertex Dart) (faceCount : ℕ) : ℤ :=
  (Fintype.card Vertex : ℤ) - (E.edgeCount : ℤ) + (faceCount : ℤ)

include E in
/-- The characteristic in terms of darts rather than edges, clearing the division. -/
theorem two_mul_eulerChar [DecidableEq Dart] (faceCount : ℕ) :
    2 * E.eulerChar faceCount
      = 2 * (Fintype.card Vertex : ℤ) - (Fintype.card Dart : ℤ) + 2 * (faceCount : ℤ) := by
  have h := E.two_mul_edgeCount
  simp only [eulerChar]
  push_cast [← h]
  ring

section Balance

variable {D : Type w}

/-- A permutation of a finite invariant set that always changes the value of a two-valued function
forces the two value classes to have equal size: the permutation itself is the bijection between
them. -/
theorem card_filter_eq_of_perm_ne (φ : Equiv.Perm D) (s : Finset D)
    (hinvariant : ∀ d, φ d ∈ s ↔ d ∈ s) (colour : D → Fin 2)
    (hne : ∀ d ∈ s, colour (φ d) ≠ colour d) :
    {d ∈ s | colour d = 0}.card = {d ∈ s | colour d = 1}.card := by
  have hzero : ∀ c : Fin 2, c ≠ 0 ↔ c = 1 := by decide
  have hone : ∀ c : Fin 2, c ≠ 1 ↔ c = 0 := by decide
  refine Finset.card_bij' (fun d _ => φ d) (fun d _ => φ.symm d) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter] at hd ⊢
    refine ⟨(hinvariant d).mpr hd.1, (hzero _).mp ?_⟩
    rw [← hd.2]
    exact hne d hd.1
  · intro d hd
    simp only [Finset.mem_filter] at hd ⊢
    have hmem : φ.symm d ∈ s :=
      (hinvariant _).mp (by rw [Equiv.apply_symm_apply]; exact hd.1)
    refine ⟨hmem, (hone _).mp fun hcontra => ?_⟩
    have hstep := hne (φ.symm d) hmem
    rw [Equiv.apply_symm_apply, hd.2, hcontra] at hstep
    exact hstep rfl
  · intro d _
    exact φ.symm_apply_apply d
  · intro d _
    exact φ.apply_symm_apply d

end Balance

/-- **Facial colour balance.** For a proper two-colouring of the embedded graph, every
`faceMap`-invariant set of darts carries equally many darts of each colour.

The faces of the embedding are the `faceMap`-orbits, so in particular the darts of every face are
balanced.  No planarity is used: `faceMap` exchanges the two colour classes, which alone forces
them to be equinumerous. -/
theorem isBalanced_of_faceMap_invariant (coloring : E.graph.Coloring (Fin 2))
    (faceDarts : Finset Dart) (hinvariant : ∀ d, E.faceMap d ∈ faceDarts ↔ d ∈ faceDarts) :
    {d ∈ faceDarts | coloring (E.vertexOf d) = 0}.card =
      {d ∈ faceDarts | coloring (E.vertexOf d) = 1}.card :=
  card_filter_eq_of_perm_ne E.faceMap faceDarts hinvariant (fun d => coloring (E.vertexOf d))
    (fun d _ => E.coloring_vertexOf_faceMap_ne coloring d)

/-- Facial colour balance for the *boundary vertices* of a face.

`PlaneGraph.boundary` records the boundary of a region as a `Finset` of vertices, so carrying balance
from darts over to vertices needs the darts of the face to be in bijection with the vertices they
point out of.  That is exactly the statement that the facial boundary is a cycle rather than a closed
walk revisiting a vertex, which is where 2-connectedness of the embedded graph enters. -/
theorem isBalanced_image_of_faceMap_invariant [DecidableEq Vertex]
    (coloring : E.graph.Coloring (Fin 2)) (faceDarts : Finset Dart)
    (hinvariant : ∀ d, E.faceMap d ∈ faceDarts ↔ d ∈ faceDarts)
    (hinjOn : Set.InjOn E.vertexOf faceDarts) :
    {v ∈ faceDarts.image E.vertexOf | coloring v = 0}.card =
      {v ∈ faceDarts.image E.vertexOf | coloring v = 1}.card := by
  rw [Finset.filter_image, Finset.filter_image,
    Finset.card_image_of_injOn (hinjOn.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))),
    Finset.card_image_of_injOn (hinjOn.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
  exact E.isBalanced_of_faceMap_invariant coloring faceDarts hinvariant

end RotationSystem

end ZonalGraphs
