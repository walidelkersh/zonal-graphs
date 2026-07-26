import ZonalGraphs.Definitions
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# The family `Gn` and Theorem 2.5.9

`Gn` is built from `n` copies of the wheel `W4`. Block `i` has outer cycle `(ri, si, ti, ui)` and hub
`vi`; the edge `si-ti` is subdivided by `wi, xi` and the edge `ri-ui` by `y(i-1), z(i-1)`, and
consecutive blocks are joined by the edges `wi-yi` and `xi-zi`. The five core vertices are indexed by
the blocks and the four connector vertices by the gaps between them, which is why `Gn` has
`5n + 4(n-1) = 9n - 4` vertices.

Zonality reads the boundary function and never the adjacency, so what Theorem 2.5.9 needs is the region
structure rather than the graph. The regions come in six shapes: two triangles per block, a quadrilateral
per gap, two pentagons, and the two long regions of the embedding `Gn,k`, of boundary lengths `8k` and
`8(n-k)`, each carrying the eight non-hub labels of a range of blocks.

The labeling is the one from the source. All five core vertices of block `i` take a common value `a i`,
while `w` and `y` take `1` and `x` and `z` take `2`. Every short region then vanishes outright: the
triangles contribute `3 * a i`, the quadrilateral `1 + 1 + 2 + 2`, and each pentagon `3 * a i + 3`. The
two long regions contribute `4 * a i + 6` per block, which is the sum of the `a i` over their blocks
because `4 = 1` in `ZMod 3`. Those two are the only places a hypothesis is needed, and the required
splitting of the blocks into two ranges of zero sum is Lemma 2.0.4.

Region shapes are carried as a hypothesis, as they are for the results on graphs of cycle rank two:
`PlaneGraph` supplies face data as an interface, so an embedding's shape is an assumption about that
data rather than something derivable.
-/

universe v

/-- Vertices of `Gn`: five core vertices per block and four connector vertices per gap. -/
abbrev GnVertex (n : ℕ) := (Fin 5 × Fin n) ⊕ (Fin 4 × Fin (n - 1))

namespace GnVertex

/-- Core vertex `j` of block `i`, with `j` running `r, s, t, u, v`. -/
def core {n : ℕ} (j : Fin 5) (i : Fin n) : GnVertex n := Sum.inl (j, i)

/-- Connector vertex `j` of gap `g`, with `j` running `w, x, y, z`. -/
def gap {n : ℕ} (j : Fin 4) (g : Fin (n - 1)) : GnVertex n := Sum.inr (j, g)

/-- The labeling of Theorem 2.5.9: the core of block `i` carries `a i`, while `w` and `y` carry `1` and
`x` and `z` carry `2`. -/
def labeling {n : ℕ} (a : Fin n → ZonalLabel) : VertexLabeling (GnVertex n)
  | Sum.inl (_, i) => a i
  | Sum.inr (j, _) => if j.val % 2 = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩

/-- The eight non-hub vertices of the blocks in `B`, together with the connectors of the gaps in `G`.
This is the shape of the two long regions of `Gn,k`. -/
def blocks {n : ℕ} (B : Finset (Fin n)) (G : Finset (Fin (n - 1))) : Finset (GnVertex n) :=
  (B.biUnion fun i => {core 0 i, core 1 i, core 2 i, core 3 i}) ∪
    (G.biUnion fun g => {gap 0 g, gap 1 g, gap 2 g, gap 3 g})

variable {n : ℕ} {a : Fin n → ZonalLabel}

@[simp] theorem labeling_core (j : Fin 5) (i : Fin n) :
    ((labeling a (core j i) : ZonalLabel) : ZMod 3) = (a i : ZMod 3) := rfl

/-- A triangle on the core of one block sums to `3 * a i`, hence to zero. -/
theorem sum_triangle (j₁ j₂ j₃ : Fin 5) (hj : j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) (i : Fin n) :
    (∑ v ∈ ({core j₁ i, core j₂ i, core j₃ i} : Finset (GnVertex n)),
      ((labeling a v : ZonalLabel) : ZMod 3)) = 0 := by
  obtain ⟨h12, h13, h23⟩ := hj
  rw [Finset.sum_insert (by simp [core, h12, h13]), Finset.sum_insert (by simp [core, h23]),
    Finset.sum_singleton, labeling_core, labeling_core, labeling_core]
  have h : ((a i : ZMod 3)) + (a i : ZMod 3) + (a i : ZMod 3) = (a i : ZMod 3) * 3 := by ring
  rw [← add_assoc, h, show (3 : ZMod 3) = 0 from by decide, mul_zero]

/-- The quadrilateral on the connectors of one gap sums to `1 + 1 + 2 + 2`, hence to zero. -/
theorem sum_quad (g : Fin (n - 1)) :
    (∑ v ∈ ({gap 0 g, gap 2 g, gap 3 g, gap 1 g} : Finset (GnVertex n)),
      ((labeling a v : ZonalLabel) : ZMod 3)) = 0 := by
  rw [Finset.sum_insert (by simp [gap]), Finset.sum_insert (by simp [gap]),
    Finset.sum_insert (by simp [gap]), Finset.sum_singleton]
  simp only [labeling, gap]
  decide

/-- A pentagon carrying the core of one block and two connectors sums to `3 * a i + 3`, hence to zero.
Both pentagon shapes of the source have this form, one taking `y, z` and the other `w, x`. -/
theorem sum_pentagon (j₁ j₂ j₃ : Fin 5) (hj : j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) (i : Fin n) (k₁ k₂ : Fin 4)
    (hk : k₁ ≠ k₂) (hpar : k₁.val % 2 ≠ k₂.val % 2) (g : Fin (n - 1)) :
    (∑ v ∈ ({core j₁ i, core j₂ i, core j₃ i, gap k₁ g, gap k₂ g} : Finset (GnVertex n)),
      ((labeling a v : ZonalLabel) : ZMod 3)) = 0 := by
  obtain ⟨h12, h13, h23⟩ := hj
  rw [Finset.sum_insert (by simp [core, gap, h12, h13]),
    Finset.sum_insert (by simp [core, gap, h23]), Finset.sum_insert (by simp [core, gap]),
    Finset.sum_insert (by simp [gap, hk]), Finset.sum_singleton, labeling_core, labeling_core,
    labeling_core]
  have hsum : ((labeling a (gap k₁ g) : ZonalLabel) : ZMod 3)
      + ((labeling a (gap k₂ g) : ZonalLabel) : ZMod 3) = 0 := by
    rcases Nat.even_or_odd k₁.val with he | ho
    · have h1 : k₁.val % 2 = 0 := Nat.even_iff.mp he
      have h2 : k₂.val % 2 = 1 := by omega
      simp [labeling, gap, h1, h2]
      decide
    · have h1 : k₁.val % 2 = 1 := Nat.odd_iff.mp ho
      have h2 : k₂.val % 2 = 0 := by omega
      simp [labeling, gap, h1, h2]
      decide
  have h3 : ((a i : ZMod 3)) + ((a i : ZMod 3) + ((a i : ZMod 3)
      + (((labeling a (gap k₁ g) : ZonalLabel) : ZMod 3)
        + ((labeling a (gap k₂ g) : ZonalLabel) : ZMod 3))))
      = (a i : ZMod 3) * 3
        + (((labeling a (gap k₁ g) : ZonalLabel) : ZMod 3)
          + ((labeling a (gap k₂ g) : ZonalLabel) : ZMod 3)) := by ring
  rw [h3, hsum, show (3 : ZMod 3) = 0 from by decide, mul_zero, add_zero]

/-- A long region sums to the sum of the `a i` over its blocks: each block contributes `4 * a i` and
each gap contributes `1 + 2 + 1 + 2`, and `4 = 1` while `6 = 0` in `ZMod 3`. -/
theorem sum_blocks (B : Finset (Fin n)) (G : Finset (Fin (n - 1))) :
    (∑ v ∈ blocks B G, ((labeling a v : ZonalLabel) : ZMod 3)) = ∑ i ∈ B, (a i : ZMod 3) := by
  classical
  rw [blocks, Finset.sum_union (by simp [Finset.disjoint_left, core, gap]),
    Finset.sum_biUnion (fun i _ j _ hij => by simp [Finset.disjoint_left, core, hij]),
    Finset.sum_biUnion (fun i _ j _ hij => by simp [Finset.disjoint_left, gap, hij])]
  have hcore : ∀ i : Fin n,
      (∑ v ∈ ({core 0 i, core 1 i, core 2 i, core 3 i} : Finset (GnVertex n)),
        ((labeling a v : ZonalLabel) : ZMod 3)) = (a i : ZMod 3) := by
    intro i
    rw [Finset.sum_insert (by simp [core]), Finset.sum_insert (by simp [core]),
      Finset.sum_insert (by simp [core]), Finset.sum_singleton, labeling_core, labeling_core,
      labeling_core, labeling_core]
    have h : ((a i : ZMod 3)) + ((a i : ZMod 3) + ((a i : ZMod 3) + (a i : ZMod 3)))
        = (a i : ZMod 3) * 3 + (a i : ZMod 3) := by ring
    rw [h, show (3 : ZMod 3) = 0 from by decide, mul_zero, zero_add]
  have hgap : ∀ g : Fin (n - 1),
      (∑ v ∈ ({gap 0 g, gap 1 g, gap 2 g, gap 3 g} : Finset (GnVertex n)),
        ((labeling a v : ZonalLabel) : ZMod 3)) = 0 := by
    intro g
    rw [Finset.sum_insert (by simp [gap]), Finset.sum_insert (by simp [gap]),
      Finset.sum_insert (by simp [gap]), Finset.sum_singleton]
    simp only [labeling, gap]
    decide
  rw [Finset.sum_congr rfl fun i _ => hcore i, Finset.sum_congr rfl fun g _ => hgap g,
    Finset.sum_const_zero, add_zero]

end GnVertex

namespace PlaneGraph

open GnVertex

variable {n : ℕ} {Face : Type v} [Fintype Face]

/-- The six region shapes of the embedding `Gn,k`, relative to a choice of block values `a`.

The last shape is the pair of long regions, whose vanishing is exactly the requirement that the block
values sum to zero over the blocks each one covers. -/
def IsGnRegion (a : Fin n → ZonalLabel) (S : Finset (GnVertex n)) : Prop :=
  (∃ i, S = {core 0 i, core 1 i, core 4 i}) ∨
  (∃ i, S = {core 4 i, core 2 i, core 3 i}) ∨
  (∃ g, S = {gap 0 g, gap 2 g, gap 3 g, gap 1 g}) ∨
  (∃ i g, S = {core 0 i, core 4 i, core 3 i, gap 3 g, gap 2 g}) ∨
  (∃ i g, S = {core 1 i, core 2 i, core 4 i, gap 0 g, gap 1 g}) ∨
  (∃ B G, S = blocks B G ∧ ∑ i ∈ B, (a i : ZMod 3) = 0)

/-- **Theorem 2.5.9 (Bowling, 2023).** The plane graph `Gn,k` has a zonal labeling.

Every region of the embedding is one of the six shapes, and the labeling of the source makes each vanish.
The short shapes vanish outright. The two long ones vanish exactly when the block values sum to zero over
the blocks they cover, which is the splitting supplied by Lemma 2.0.4 and is carried here inside
`IsGnRegion`. -/
theorem isZonal_of_forall_isGnRegion (P : PlaneGraph (GnVertex n) Face) (a : Fin n → ZonalLabel)
    (hregions : ∀ R : Face, IsGnRegion a (P.boundary R)) : P.IsZonal := by
  refine ⟨labeling a, fun R => ?_⟩
  rw [zoneValue]
  rcases hregions R with ⟨i, hR⟩ | ⟨i, hR⟩ | ⟨g, hR⟩ | ⟨i, g, hR⟩ | ⟨i, g, hR⟩ | ⟨B, G, hR, hsum⟩
  · rw [hR]; exact sum_triangle 0 1 4 (by decide) i
  · rw [hR]; exact sum_triangle 4 2 3 (by decide) i
  · rw [hR]; exact sum_quad g
  · rw [hR]; exact sum_pentagon 0 4 3 (by decide) i 3 2 (by decide) (by decide) g
  · rw [hR]; exact sum_pentagon 1 2 4 (by decide) i 0 1 (by decide) (by decide) g
  · rw [hR, sum_blocks]; exact hsum

end PlaneGraph

end ZonalGraphs
