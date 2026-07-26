import ZonalGraphs.Definitions
import ZonalGraphs.TriangleForcing
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

/-- **Theorem 2.5.11 (Bowling, 2023).** The embedding `Gn,k` has no zonal labeling for `1 <= k <= n-2`.

The forcing chain of the source, with its normalization removed. Two triangles on the last block force
its five core vertices onto a common value `d`. The pentagon on `y, z` then forces `y` and `z` to cancel,
after which the eight-vertex region forces `w + x = -d`, since four copies of `d` is one copy in
`ZMod 3`. Two triangles on the previous block force its core onto a common value, and the pentagon on
`w, x` there sums to three copies of that value plus `w + x`, which is `-d`. A zonal labeling would make
that zero, forcing `d = 0`, and no label is zero.

The source normalizes the hub label to `1` and argues numerically from there. Carrying `d` symbolically
removes the need for that step, so `exists_isZonalLabeling_apply_eq_one` is not required here. -/
theorem not_isZonal_of_gn_forcing (P : PlaneGraph (GnVertex n) Face) (i j : Fin n) (g : Fin (n - 1))
    (Rv Ru Rw Rl Rv' Ru' Rp : Face)
    (hRv : P.boundary Rv = {core 4 i, core 1 i, core 0 i})
    (hRu : P.boundary Ru = {core 4 i, core 3 i, core 2 i})
    (hRw : P.boundary Rw = {gap 2 g, gap 3 g, core 3 i, core 4 i, core 0 i})
    (hRl : P.boundary Rl
      = {core 0 i, core 1 i, core 2 i, core 3 i, gap 3 g, gap 1 g, gap 0 g, gap 2 g})
    (hRv' : P.boundary Rv' = {core 4 j, core 1 j, core 0 j})
    (hRu' : P.boundary Ru' = {core 4 j, core 3 j, core 2 j})
    (hRp : P.boundary Rp = {core 4 j, core 1 j, gap 0 g, gap 1 g, core 3 j}) : ¬ P.IsZonal := by
  rintro ⟨l, hl⟩
  -- the two triangles on a block force its five core vertices onto one value
  have hforce : ∀ (R : Face) (k : Fin n) (b c : Fin 5),
      P.boundary R = {core 4 k, core b k, core c k} → b ≠ c → (4 : Fin 5) ≠ b → (4 : Fin 5) ≠ c →
      (l (core 4 k) : ZMod 3) = (l (core b k) : ZMod 3)
        ∧ (l (core 4 k) : ZMod 3) = (l (core c k) : ZMod 3) := by
    intro R k b c hR hbc h4b h4c
    have hc : (P.boundary R).card = 3 := by
      rw [hR, Finset.card_insert_of_notMem (by simp [core, h4b, h4c]),
        Finset.card_insert_of_notMem (by simp [core, hbc]), Finset.card_singleton]
    have hmem : ∀ d : Fin 5, (d = 4 ∨ d = b ∨ d = c) → core d k ∈ P.boundary R := by
      rintro d (rfl | rfl | rfl) <;> rw [hR] <;> simp
    exact ⟨congrArg _ (P.eq_of_zoneValue_eq_zero_of_card_boundary_eq_three (hl R) hc
        (hmem 4 (Or.inl rfl)) (hmem b (Or.inr (Or.inl rfl)))),
      congrArg _ (P.eq_of_zoneValue_eq_zero_of_card_boundary_eq_three (hl R) hc
        (hmem 4 (Or.inl rfl)) (hmem c (Or.inr (Or.inr rfl))))⟩
  obtain ⟨h1, h0⟩ := hforce Rv i 1 0 hRv (by decide) (by decide) (by decide)
  obtain ⟨h3, h2⟩ := hforce Ru i 3 2 hRu (by decide) (by decide) (by decide)
  obtain ⟨h1', h0'⟩ := hforce Rv' j 1 0 hRv' (by decide) (by decide) (by decide)
  obtain ⟨h3', h2'⟩ := hforce Ru' j 3 2 hRu' (by decide) (by decide) (by decide)
  set d : ZMod 3 := (l (core 4 i) : ZMod 3) with hd
  set c : ZMod 3 := (l (core 4 j) : ZMod 3) with hc
  set w : ZMod 3 := (l (gap 0 g) : ZMod 3) with hw
  set x : ZMod 3 := (l (gap 1 g) : ZMod 3) with hx
  set y : ZMod 3 := (l (gap 2 g) : ZMod 3) with hy
  set z : ZMod 3 := (l (gap 3 g) : ZMod 3) with hz
  -- the pentagon on y and z makes them cancel
  have hyz : y + z = 0 := by
    have := hl Rw
    rw [zoneValue, hRw, Finset.sum_insert (by simp [core, gap]),
      Finset.sum_insert (by simp [core, gap]), Finset.sum_insert (by simp [core]),
      Finset.sum_insert (by simp [core]), Finset.sum_singleton, ← h3, ← h0] at this
    have hring : y + (z + (d + (d + d))) = y + z + d * 3 := by ring
    rw [hring, show (3 : ZMod 3) = 0 from by decide, mul_zero, add_zero] at this
    exact this
  -- the eight-vertex region then pins w + x
  have hwx : w + x = -d := by
    have := hl Rl
    rw [zoneValue, hRl, Finset.sum_insert (by simp [core, gap]),
      Finset.sum_insert (by simp [core, gap]), Finset.sum_insert (by simp [core, gap]),
      Finset.sum_insert (by simp [core, gap]), Finset.sum_insert (by simp [gap]),
      Finset.sum_insert (by simp [gap]), Finset.sum_insert (by simp [gap]),
      Finset.sum_singleton, ← h1, ← h2, ← h3, ← h0] at this
    have hring : d + (d + (d + (d + (z + (x + (w + y)))))) = d * 3 + d + (w + x) + (y + z) := by
      ring
    rw [hring, show (3 : ZMod 3) = 0 from by decide, mul_zero, zero_add, hyz, add_zero] at this
    linear_combination this
  -- the pentagon on w and x in the previous block then cannot vanish
  have hfinal := hl Rp
  rw [zoneValue, hRp, Finset.sum_insert (by simp [core, gap]),
    Finset.sum_insert (by simp [core, gap]), Finset.sum_insert (by simp [core, gap]),
    Finset.sum_insert (by simp [core, gap]), Finset.sum_singleton, ← h1', ← h3'] at hfinal
  have hring : c + (c + (w + (x + c))) = c * 3 + (w + x) := by ring
  rw [hring, show (3 : ZMod 3) = 0 from by decide, mul_zero, zero_add, hwx, neg_eq_zero] at hfinal
  exact (l (core 4 i)).2 hfinal

end PlaneGraph

end ZonalGraphs
