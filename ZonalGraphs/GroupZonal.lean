import ZonalGraphs.AbelianGroups
import ZonalGraphs.BipartiteZonal
import ZonalGraphs.FourColor
import ZonalGraphs.TreesAndCycles

namespace ZonalGraphs

/-!
# Zonal labelings valued in an arbitrary abelian group

Bowling (2025) replaces `ZMod 3` by an arbitrary abelian group `Γ`: a `Γ`-zonal labeling assigns each
vertex a nonzero element of `Γ` so that the labels bounding every region sum to `0`.  Taking
`Γ = ZMod 3` recovers the classical notion, since the nonzero elements there are exactly `1` and `2`.

`ZonalLabel` is hardwired to `ZMod 3`, so the group-valued notion needs its own definitions rather than a
reuse of the existing ones.  They are given here.

Proposition 2.4 then follows from the purely group-theoretic labeling lemma: a cycle has both of its two
regions bounded by every vertex, so being `Γ`-zonal is exactly the existence of a nonzero labeling of the
vertices summing to zero.
-/

universe u v

/-- A labeling of vertices by nonzero elements of an abelian group. -/
abbrev GroupLabeling (Vertex : Type u) (Γ : Type*) [AddCommGroup Γ] := Vertex → {x : Γ // x ≠ 0}

namespace PlaneGraph

variable {Vertex : Type u} {Face : Type v} [Fintype Vertex] [Fintype Face]
  {Γ : Type*} [AddCommGroup Γ]

/-- The value of a region under a group-valued labeling. -/
def groupZoneValue (P : PlaneGraph Vertex Face) (labeling : GroupLabeling Vertex Γ) (R : Face) : Γ :=
  ∑ v ∈ P.boundary R, (labeling v : Γ)

/-- A plane graph is `Γ`-zonal when some labeling by nonzero elements of `Γ` gives every region the
value `0`. -/
def IsGroupZonal (P : PlaneGraph Vertex Face) (Γ : Type*) [AddCommGroup Γ] : Prop :=
  ∃ labeling : GroupLabeling Vertex Γ, ∀ R : Face, P.groupZoneValue labeling R = 0

/-- The regions having a given vertex on their boundary, written `X_v` in the literature. -/
def regionsAt [DecidableEq Vertex] (P : PlaneGraph Vertex Face) (v : Vertex) : Finset Face :=
  {R ∈ Finset.univ | v ∈ P.boundary R}

/-- A plane graph is `Γ`-*cozonal* when some labeling of its **regions** by nonzero elements of `Γ` gives
every vertex the value `0`, the value of a vertex being the sum over the regions on whose boundary it
lies.

This is the exact dual of zonality: zonal labels vertices and sums over each region's boundary, cozonal
labels regions and sums over each vertex's incident regions. -/
def IsGroupCozonal [DecidableEq Vertex] (P : PlaneGraph Vertex Face) (Γ : Type*)
    [AddCommGroup Γ] : Prop :=
  ∃ labeling : Face → {x : Γ // x ≠ 0},
    ∀ v : Vertex, ∑ R ∈ P.regionsAt v, (labeling R : Γ) = 0

/-- The supplied-data formulation of Theorem 1.4: a plane triangulation is tricolorable exactly
when it is `ZMod 3`-cozonal. -/
def TricoloringCozonalStatement [DecidableEq Vertex] (P : PlaneGraph Vertex Face) : Prop :=
  (∃ coloring : Sym2 Vertex → Fin 3, P.IsTricoloring coloring) ↔
    P.IsGroupCozonal (ZMod 3)

/-- The unrestricted universal carrier for Theorem 1.4.

This proposition is useful for exposing the interface boundary, but it is false because
`PlaneGraph.boundaryEdges` is not yet certified by `IsTriangulation`; see
`not_tricoloringCozonalTheorem`. -/
def TricoloringCozonalTheorem : Prop :=
  ∀ (V : Type u) (F : Type v) [Fintype V] [Fintype F] [DecidableEq V]
    (P : PlaneGraph V F), P.IsTriangulation → P.TricoloringCozonalStatement

/-!
## Why the unrestricted tricoloring carrier is false

Give `K₃` two copies of its triangular vertex boundary but no supplied boundary edges. Label the
two faces by `1` and `2`; every vertex then sees both labels, whose sum is zero. Thus the data is
cozonal. A tricoloring is impossible because its definition asks each face to contain an edge of
every color, while both alleged boundary-edge sets are empty.
-/

/-- `K₃` with two alleged triangular faces whose boundary-edge sets are empty. -/
def invalidDoubleTriangle : PlaneGraph (Fin 3) Bool where
  graph := ⊤
  connected := SimpleGraph.connected_top
  boundary := fun _ => Finset.univ
  boundaryEdges := fun _ => ∅
  exterior := false

/-- The supplied vertex boundaries make `invalidDoubleTriangle` a triangulation under the current
definition. -/
theorem invalidDoubleTriangle_isTriangulation : invalidDoubleTriangle.IsTriangulation := by
  intro R
  constructor
  · simp [invalidDoubleTriangle]
  · rw [SimpleGraph.isClique_iff]
    intro u _ v _ huv
    simpa [invalidDoubleTriangle] using huv

/-- Labeling the two faces by `1` and `2` makes every vertex sum to zero. -/
theorem invalidDoubleTriangle_isGroupCozonal :
    invalidDoubleTriangle.IsGroupCozonal (ZMod 3) := by
  classical
  refine ⟨fun R => if R then ⟨2, by decide⟩ else ⟨1, by decide⟩, fun v => ?_⟩
  simpa [regionsAt, invalidDoubleTriangle] using
    (show (2 : ZMod 3) + 1 = 0 from by decide)

/-- Empty supplied boundary-edge sets rule out a tricoloring. -/
theorem invalidDoubleTriangle_not_tricolorable :
    ¬ ∃ coloring : Sym2 (Fin 3) → Fin 3, invalidDoubleTriangle.IsTricoloring coloring := by
  rintro ⟨coloring, hcoloring⟩
  simpa [invalidDoubleTriangle] using hcoloring false 0

/-- Theorem 1.4 is false when stated against unrestricted supplied face data. -/
theorem invalidDoubleTriangle_not_tricoloringCozonalStatement :
    ¬ invalidDoubleTriangle.TricoloringCozonalStatement := by
  intro h
  exact invalidDoubleTriangle_not_tricolorable (h.mpr invalidDoubleTriangle_isGroupCozonal)

/-- The unrestricted universal carrier for Theorem 1.4 is false. A faithful version must connect
each face's `boundaryEdges` to its cyclic vertex boundary. -/
theorem not_tricoloringCozonalTheorem : ¬ TricoloringCozonalTheorem.{0, 0} := by
  intro h
  exact invalidDoubleTriangle_not_tricoloringCozonalStatement
    (h (Fin 3) Bool invalidDoubleTriangle invalidDoubleTriangle_isTriangulation)

/-!
## Why the unrestricted Heawood carrier is false

For a connected plane triangulation, Heawood's theorem says that all vertex degrees are even if
and only if the graph is three-colourable. The current `PlaneGraph` interface does not certify
planarity: `K₅` can be paired with one supplied triangular face. It then satisfies the current
triangulation predicate and has even degree four at every vertex, but its five-vertex clique cannot
be coloured with three colours.
-/

/-- A connected supplied plane graph is Eulerian when every vertex has even degree. Connectedness
is already a field of `PlaneGraph`. -/
noncomputable def IsEulerian (P : PlaneGraph Vertex Face) : Prop := by
  letI := Classical.decRel P.graph.Adj
  exact ∀ v, Even (P.graph.degree v)

/-- The unrestricted universal carrier for the forward direction of Heawood's theorem. A faithful
version must quantify over certified genus-zero triangulations. -/
def HeawoodThreeColorTheorem : Prop :=
  ∀ (V : Type u) (F : Type v) [Fintype V] [Fintype F] (P : PlaneGraph V F),
    P.IsTriangulation → P.IsEulerian → P.graph.Colorable 3

/-- `K₅` with one alleged triangular face. This is supplied face data, not a planar embedding. -/
def invalidK5Triangle : PlaneGraph (Fin 5) Unit where
  graph := ⊤
  connected := SimpleGraph.connected_top
  boundary := fun _ => {0, 1, 2}
  boundaryEdges := fun _ => ∅
  exterior := ()

/-- The supplied boundary makes `invalidK5Triangle` a triangulation under the current predicate. -/
theorem invalidK5Triangle_isTriangulation : invalidK5Triangle.IsTriangulation := by
  intro R
  constructor
  · simp [invalidK5Triangle]
  · rw [SimpleGraph.isClique_iff]
    intro u _ v _ huv
    simpa [invalidK5Triangle] using huv

/-- Every vertex of the underlying `K₅` has even degree four. -/
theorem invalidK5Triangle_isEulerian : invalidK5Triangle.IsEulerian := by
  classical
  unfold IsEulerian
  intro v
  refine ⟨2, ?_⟩
  simp [invalidK5Triangle, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  fin_cases v <;> decide

/-- The five-vertex clique cannot be coloured with only three colours. -/
theorem invalidK5Triangle_not_colorable : ¬ invalidK5Triangle.graph.Colorable 3 := by
  intro hcolor
  have hclique : invalidK5Triangle.graph.IsClique (Finset.univ : Finset (Fin 5)) := by
    rw [SimpleGraph.isClique_iff]
    intro u _ v _ huv
    simpa [invalidK5Triangle] using huv
  have hle := hclique.card_le_of_colorable hcolor
  simp at hle

/-- The unrestricted Heawood carrier is false because supplied triangular face data does not imply
that the underlying graph is planar. -/
theorem not_heawoodThreeColorTheorem : ¬ HeawoodThreeColorTheorem.{0, 0} := by
  intro h
  exact invalidK5Triangle_not_colorable
    (h (Fin 5) Unit invalidK5Triangle invalidK5Triangle_isTriangulation
      invalidK5Triangle_isEulerian)

/-- **Observation 2.2 (Bowling, 2025).** A group homomorphism carries a `Γ`-zonal labeling avoiding its
kernel to a `Γ'`-zonal labeling.

No vertex label lies in the kernel, so the images are again nonzero, and a homomorphism commutes with the
sum defining a region's value. -/
theorem isGroupZonal_map {Γ' : Type*} [AddCommGroup Γ'] (φ : Γ →+ Γ')
    (P : PlaneGraph Vertex Face) (labeling : GroupLabeling Vertex Γ)
    (hkernel : ∀ v, φ (labeling v) ≠ 0)
    (hzonal : ∀ R : Face, P.groupZoneValue labeling R = 0) : P.IsGroupZonal Γ' := by
  refine ⟨fun v => ⟨φ (labeling v), hkernel v⟩, fun R => ?_⟩
  simp only [groupZoneValue] at hzonal ⊢
  rw [← map_sum, hzonal R, map_zero]

/-- On every triangular face, a proper three-colouring uses each colour exactly once.

This is the local graph-theoretic step in Proposition 2.8. It used to be carried by that result as
the hypothesis `hface`; it follows from the definition of a triangulation and properness of the
colouring. -/
theorem IsTriangulation.card_filter_coloring_eq_one [DecidableEq Vertex]
    {P : PlaneGraph Vertex Face} (htri : P.IsTriangulation)
    (colouring : P.graph.Coloring (Fin 3)) (R : Face) (i : Fin 3) :
    {v ∈ P.boundary R | colouring v = i}.card = 1 := by
  obtain ⟨hcard, hclique⟩ := htri R
  have hsurj : Set.SurjOn colouring ↑(P.boundary R) Set.univ :=
    SimpleGraph.Coloring.surjOn_of_card_le_isClique hclique (by simp [hcard]) colouring
  obtain ⟨v, hv, hvi⟩ := hsurj (Set.mem_univ i)
  rw [Finset.card_eq_one]
  refine ⟨v, Finset.ext fun w => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hw, hwi⟩
    by_contra hwv
    exact (colouring.valid (hclique hw hv hwv)) (hwi.trans hvi.symm)
  · rintro rfl
    exact ⟨hv, hvi⟩

/-- **Zonality from a three-colouring meeting every region once per colour.**

Give the three colour classes three nonzero elements summing to zero, which exist for any abelian group
with two distinct nonzero elements by `exists_three_nonzero_add_eq_zero`.  A region whose boundary holds
exactly one vertex of each colour then sums to `g 0 + g 1 + g 2 = 0`.

This is the incidence-level engine for the labelling half of Proposition 2.8 of Bowling (2025).
`isGroupZonal_of_threeColourable_triangulation` below derives `hface` rather than carrying it. -/
theorem isGroupZonal_of_threeColouring [DecidableEq Vertex] (P : PlaneGraph Vertex Face)
    (colouring : Vertex → Fin 3) {g : Fin 3 → Γ} (hg : ∀ i, g i ≠ 0)
    (hsum : g 0 + g 1 + g 2 = 0)
    (hface : ∀ (R : Face) (i : Fin 3), {v ∈ P.boundary R | colouring v = i}.card = 1) :
    P.IsGroupZonal Γ := by
  refine ⟨fun v => ⟨g (colouring v), hg _⟩, fun R => ?_⟩
  rw [groupZoneValue, ← Finset.sum_fiberwise (P.boundary R) colouring
    fun v => (g (colouring v) : Γ)]
  have hfib : ∀ i : Fin 3,
      (∑ v ∈ {v ∈ P.boundary R | colouring v = i}, (g (colouring v) : Γ)) = g i := by
    intro i
    rw [Finset.sum_congr rfl fun v hv => by
      rw [(Finset.mem_filter.mp hv).2], Finset.sum_const, hface R i, one_smul]
  rw [Fin.sum_univ_three, hfib 0, hfib 1, hfib 2]
  exact hsum

/-- **The labelling half of Proposition 2.8 (Bowling, 2025), without a facial-count
hypothesis.**

A proper three-colouring of a plane triangulation uses every colour exactly once on each face, so
three nonzero group elements summing to zero give a group-zonal labelling. For a certified plane
triangulation, Heawood's theorem supplies that colouring from the Eulerian hypothesis. The current
unrestricted carrier is false; see `not_heawoodThreeColorTheorem`. -/
theorem isGroupZonal_of_threeColourable_triangulation [DecidableEq Vertex]
    (P : PlaneGraph Vertex Face) (htri : P.IsTriangulation)
    (colouring : P.graph.Coloring (Fin 3)) {g h : Γ} (hg : g ≠ 0) (hh : h ≠ 0)
    (hne : g ≠ h) : P.IsGroupZonal Γ := by
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ := exists_three_nonzero_add_eq_zero hg hh hne
  let values : Fin 3 → Γ := ![a, b, c]
  refine isGroupZonal_of_threeColouring P colouring (g := values) ?_ ?_ ?_
  · intro i
    fin_cases i <;> simp [values, ha, hb, hc]
  · simpa [values] using habc
  · exact fun R i => htri.card_filter_coloring_eq_one colouring R i

/-- **Observation 2.1 (Bowling, 2025).** Zonality passes to a larger group along any injective
homomorphism, so in particular a subgroup inclusion.

The images of nonzero labels stay nonzero because the map is injective, and the region sums transport by
`isGroupZonal_map`. -/
theorem isGroupZonal_of_injective {Γ' : Type*} [AddCommGroup Γ'] (φ : Γ →+ Γ')
    (hinj : Function.Injective φ) (P : PlaneGraph Vertex Face) (h : P.IsGroupZonal Γ) :
    P.IsGroupZonal Γ' := by
  obtain ⟨labeling, hlabeling⟩ := h
  exact isGroupZonal_map φ P labeling
    (fun v hz => (labeling v).2 (hinj (by rw [hz, map_zero]))) hlabeling

/-- Cozonality transports along an injective homomorphism, the dual of `isGroupZonal_of_injective`.

A homomorphism commutes with the sum over the regions at a vertex, and injectivity keeps the images of
nonzero region labels nonzero. -/
theorem isGroupCozonal_of_injective [DecidableEq Vertex] {Γ' : Type*} [AddCommGroup Γ']
    (φ : Γ →+ Γ') (hinj : Function.Injective φ) (P : PlaneGraph Vertex Face)
    (h : P.IsGroupCozonal Γ) : P.IsGroupCozonal Γ' := by
  obtain ⟨labeling, hlabeling⟩ := h
  refine ⟨fun R => ⟨φ (labeling R), fun hz => (labeling R).2 (hinj (by rw [hz, map_zero]))⟩,
    fun v => ?_⟩
  rw [← map_sum, hlabeling v, map_zero]

/-- **The generalization is faithful.** At `Γ = ZMod 3` the group-valued notion *is* the original one, on
the nose rather than up to translation.

`ZonalLabel` unfolds to the nonzero elements of `ZMod 3`, so `GroupLabeling Vertex (ZMod 3)` and
`VertexLabeling Vertex` are the same type and the two region values are the same sum.  Anything proved
about `IsGroupZonal` therefore specializes to `IsZonal` with no translation step. -/
theorem isGroupZonal_zmod_three_iff (P : PlaneGraph Vertex Face) :
    P.IsGroupZonal (ZMod 3) ↔ P.IsZonal := Iff.rfl

/-- A plane graph all of whose regions are bounded by every vertex is `Γ`-zonal as soon as the vertices
number at least two and `Γ` has two distinct nonzero elements.

Both regions of a cycle are of this shape, which is what Proposition 2.4 needs. -/
theorem isGroupZonal_of_boundary_eq_univ [DecidableEq Vertex] (P : PlaneGraph Vertex Face)
    (hboundary : ∀ R : Face, P.boundary R = Finset.univ) {g h : Γ} (hg : g ≠ 0) (hh : h ≠ 0)
    (hne : g ≠ h) (hcard : 2 ≤ Fintype.card Vertex) : P.IsGroupZonal Γ := by
  obtain ⟨f, hfne, hfsum⟩ :=
    exists_labeling_sum_eq_zero hg hh hne (Finset.univ : Finset Vertex) (by simpa using hcard)
  refine ⟨fun v => ⟨f v, hfne v⟩, fun R => ?_⟩
  rw [groupZoneValue, hboundary R]
  exact hfsum

/-- **Proposition 2.4 (Bowling, 2025).** For `n ≥ 3` the cycle `Cₙ` is `Γ`-zonal whenever `Γ` has two
distinct nonzero elements, that is, whenever `Γ` is neither trivial nor `ZMod 2`.

The excluded case is exactly the failure of that hypothesis: over `ZMod 2` the only available label is
`1`, so the sum over an odd cycle is `1`. -/
theorem isGroupZonal_ofCycle {g h : Γ} (hg : g ≠ 0) (hh : h ≠ 0) (hne : g ≠ h) (n : ℕ)
    (hn : 3 ≤ n) : (ofCycle n hn).IsGroupZonal Γ :=
  isGroupZonal_of_boundary_eq_univ _ (fun _ => rfl) hg hh hne (by simpa using by omega)

/-- **The zonal half of Proposition 2.7 (Bowling, 2025).** A plane graph carrying a proper two-colouring
whose every facial boundary is balanced is `Γ`-zonal, for any abelian `Γ` with a nonzero element.

Label one colour class `g` and the other `-g`.  A balanced boundary has equally many vertices of each
colour, so its value is `n • g + n • (-g) = 0`.  Nothing about `ZMod 3` is used, and no facial parity
argument beyond balance.

This does not discharge the todo entry for Proposition 2.7, which is a conjunction whose dual half
concerns cozonal labelings of Eulerian plane graphs and is not proved here. -/
theorem isGroupZonal_of_facialBalance [DecidableEq Vertex] (P : PlaneGraph Vertex Face)
    (coloring : P.graph.Coloring (Fin 2)) {g : Γ} (hg : g ≠ 0)
    (hbalance : ∀ R : Face, SimpleGraph.IsBalanced coloring (P.boundary R)) : P.IsGroupZonal Γ := by
  refine ⟨fun v => ⟨if coloring v = 0 then g else -g, ?_⟩, fun R => ?_⟩
  · by_cases hv : coloring v = 0 <;> simp [hv, hg]
  · have hb : {x ∈ P.boundary R | coloring x = 0}.card
        = {x ∈ P.boundary R | coloring x = 1}.card := hbalance R
    have hzero : ∀ x ∈ {x ∈ P.boundary R | coloring x = 0},
        (if coloring x = 0 then g else -g) = g := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      simp [hx.2]
    have hone : ∀ x ∈ {x ∈ P.boundary R | coloring x = 1},
        (if coloring x = 0 then g else -g) = -g := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      simp [hx.2]
    rw [groupZoneValue,
      ← Finset.sum_filter_add_sum_filter_not (P.boundary R) fun x => coloring x = 0,
      SimpleGraph.filter_color_ne_zero coloring (P.boundary R),
      Finset.sum_congr rfl hzero, Finset.sum_congr rfl hone, Finset.sum_const, Finset.sum_const,
      hb, ← smul_add, add_neg_cancel, smul_zero]

end PlaneGraph

end ZonalGraphs
