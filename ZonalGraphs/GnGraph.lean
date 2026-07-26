import ZonalGraphs.GnFamily

namespace ZonalGraphs

/-!
# The graph `Gn`

`GnFamily` needed only the region structure of `Gn,k`, since zonality reads the boundary function and never
the adjacency. Theorem 2.5.1 is about the graph itself, so the adjacency has to be built.

Block `i` is the wheel `W4` with outer cycle `(r, s, t, u)` and hub `v`, and the hub is joined to all four.
The edge `s-t` of block `i` is subdivided by `w` and `x` of gap `i`, and the edge `r-u` of block `i` is
subdivided by `y` and `z` of gap `i - 1`. Consecutive blocks are then joined by `w-y` and `x-z` inside each
gap. Gap `i` exists only for `i + 1 < n`, so block `n - 1` keeps its `s-t` edge undivided and block `0`
keeps its `r-u` edge, which is where the two irregular ends come from.

Indices are compared as natural numbers throughout, following `windmillGraph` and `thetaGraph`, so that no
dependent casts appear.
-/

universe u

variable {n : ℕ}

open GnVertex

/-- Adjacency of two core vertices of the same block: the hub meets all four rim vertices, `r-s` and `t-u`
are always present, and `s-t` and `r-u` are present exactly at the ends where their subdividing gap is
absent. -/
def gnCoreAdj (n : ℕ) (j₁ j₂ : Fin 5) (i : Fin n) : Prop :=
  (j₁ = 4 ∧ j₂ ≠ 4) ∨ (j₂ = 4 ∧ j₁ ≠ 4) ∨
    (j₁ = 0 ∧ j₂ = 1) ∨ (j₁ = 1 ∧ j₂ = 0) ∨ (j₁ = 2 ∧ j₂ = 3) ∨ (j₁ = 3 ∧ j₂ = 2) ∨
    (((j₁ = 1 ∧ j₂ = 2) ∨ (j₁ = 2 ∧ j₂ = 1)) ∧ i.val + 1 = n) ∨
    (((j₁ = 0 ∧ j₂ = 3) ∨ (j₁ = 3 ∧ j₂ = 0)) ∧ i.val = 0)

/-- Adjacency of two connector vertices of the same gap: the path `w-x`, the path `y-z`, and the two joining
edges `w-y` and `x-z`. -/
def gnGapAdj (k₁ k₂ : Fin 4) : Prop :=
  (k₁ = 0 ∧ k₂ = 1) ∨ (k₁ = 1 ∧ k₂ = 0) ∨ (k₁ = 2 ∧ k₂ = 3) ∨ (k₁ = 3 ∧ k₂ = 2) ∨
    (k₁ = 0 ∧ k₂ = 2) ∨ (k₁ = 2 ∧ k₂ = 0) ∨ (k₁ = 1 ∧ k₂ = 3) ∨ (k₁ = 3 ∧ k₂ = 1)

/-- Adjacency between the core vertex `j` of block `i` and the connector `k` of gap `g`: `s` meets `w` and
`t` meets `x` in the gap of the same index, while `r` meets `y` and `u` meets `z` in the previous gap. -/
def gnMixedAdj (j : Fin 5) (i : Fin n) (k : Fin 4) (g : Fin (n - 1)) : Prop :=
  (j = 1 ∧ k = 0 ∧ g.val = i.val) ∨ (j = 2 ∧ k = 1 ∧ g.val = i.val) ∨
    (j = 0 ∧ k = 2 ∧ g.val + 1 = i.val) ∨ (j = 3 ∧ k = 3 ∧ g.val + 1 = i.val)

/-- Adjacency in `Gn`. -/
def gnAdj (n : ℕ) : GnVertex n → GnVertex n → Prop
  | Sum.inl (j₁, i₁), Sum.inl (j₂, i₂) => i₁ = i₂ ∧ gnCoreAdj n j₁ j₂ i₁
  | Sum.inl (j, i), Sum.inr (k, g) => gnMixedAdj j i k g
  | Sum.inr (k, g), Sum.inl (j, i) => gnMixedAdj j i k g
  | Sum.inr (k₁, g₁), Sum.inr (k₂, g₂) => g₁ = g₂ ∧ gnGapAdj k₁ k₂

theorem gnCoreAdj_symm {j₁ j₂ : Fin 5} {i : Fin n} (h : gnCoreAdj n j₁ j₂ i) :
    gnCoreAdj n j₂ j₁ i := by
  unfold gnCoreAdj at h ⊢
  tauto

theorem gnGapAdj_symm {k₁ k₂ : Fin 4} (h : gnGapAdj k₁ k₂) : gnGapAdj k₂ k₁ := by
  unfold gnGapAdj at h ⊢
  tauto

theorem gnCoreAdj_irrefl {j : Fin 5} {i : Fin n} : ¬ gnCoreAdj n j j i := by
  unfold gnCoreAdj
  rintro (⟨h, hne⟩ | ⟨h, hne⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ |
    ⟨⟨h₁, h₂⟩ | ⟨h₁, h₂⟩, -⟩ | ⟨⟨h₁, h₂⟩ | ⟨h₁, h₂⟩, -⟩) <;> simp_all

theorem gnGapAdj_irrefl {k : Fin 4} : ¬ gnGapAdj k k := by
  unfold gnGapAdj
  rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;>
    simp_all

/-- The graph `Gn`. -/
def gnGraph (n : ℕ) : SimpleGraph (GnVertex n) where
  Adj := gnAdj n
  symm := by
    rintro (⟨j₁, i₁⟩ | ⟨k₁, g₁⟩) (⟨j₂, i₂⟩ | ⟨k₂, g₂⟩) hadj
    · obtain ⟨hi, hcore⟩ := hadj
      subst hi
      exact ⟨rfl, gnCoreAdj_symm hcore⟩
    · exact hadj
    · exact hadj
    · obtain ⟨hg, hgap⟩ := hadj
      subst hg
      exact ⟨rfl, gnGapAdj_symm hgap⟩
  loopless := ⟨by
    rintro (⟨j, i⟩ | ⟨k, g⟩) hadj
    · exact gnCoreAdj_irrefl hadj.2
    · exact gnGapAdj_irrefl hadj.2⟩

/-- Every rim vertex of a block reaches that block's hub, since the hub meets all four. -/
theorem gnGraph_reachable_hub (j : Fin 5) (i : Fin n) : (gnGraph n).Reachable (core j i) (core 4 i) := by
  by_cases hj : j = 4
  · subst hj
    exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable
      (show (gnGraph n).Adj (core j i) (core 4 i) from ⟨rfl, Or.inr (Or.inl ⟨rfl, hj⟩)⟩)

/-- Crossing one gap: the hub of block `g + 1` reaches the hub of block `g`, along the path
`v - r - y - w - s - v`. -/
theorem gnGraph_reachable_prev (g : Fin (n - 1)) (i i' : Fin n) (hi : i.val = g.val + 1)
    (hi' : i'.val = g.val) : (gnGraph n).Reachable (core 4 i) (core 4 i') := by
  have h₁ : (gnGraph n).Adj (core 0 i) (gap 2 g) :=
    Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hi.symm⟩))
  have h₂ : (gnGraph n).Adj (gap 2 g) (gap 0 g) :=
    ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩
  have h₃ : (gnGraph n).Adj (gap 0 g) (core 1 i') := Or.inl ⟨rfl, rfl, hi'.symm⟩
  exact (((gnGraph_reachable_hub 0 i).symm.trans h₁.reachable).trans
    (h₂.reachable.trans h₃.reachable)).trans (gnGraph_reachable_hub 1 i')

/-- Every hub reaches the hub of block `0`, by walking down one gap at a time. -/
theorem gnGraph_reachable_hub_zero (hn : 0 < n) :
    ∀ (m : ℕ) (i : Fin n), i.val = m → (gnGraph n).Reachable (core 4 i) (core 4 ⟨0, hn⟩) := by
  intro m
  induction m with
  | zero =>
    intro i hi
    have : i = ⟨0, hn⟩ := Fin.ext hi
    subst this
    exact SimpleGraph.Reachable.refl _
  | succ m ih =>
    intro i hi
    have hlt : m < n - 1 := by omega
    have hm : m < n := by omega
    exact (gnGraph_reachable_prev ⟨m, hlt⟩ i ⟨m, hm⟩ hi rfl).trans (ih ⟨m, hm⟩ rfl)

/-- Every connector is adjacent to a core vertex: `w` and `x` meet their own block, `y` and `z` the next. -/
theorem gnGraph_exists_adj_core (k : Fin 4) (g : Fin (n - 1)) :
    ∃ (j : Fin 5) (i : Fin n), (gnGraph n).Adj (gap k g) (core j i) := by
  have hg : g.val < n - 1 := g.isLt
  have hsame : g.val < n := by omega
  have hnext : g.val + 1 < n := by omega
  fin_cases k
  · exact ⟨1, ⟨g.val, hsame⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · exact ⟨2, ⟨g.val, hsame⟩, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  · exact ⟨0, ⟨g.val + 1, hnext⟩, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩
  · exact ⟨3, ⟨g.val + 1, hnext⟩, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩

/-- **`Gn` is connected.** Every vertex walks to its own block's hub, or through a gap to a neighbouring
block's hub, and the hubs chain down to block `0`. -/
theorem gnGraph_connected (hn : 0 < n) : (gnGraph n).Connected := by
  have hbase : ∀ z : GnVertex n, (gnGraph n).Reachable z (core 4 ⟨0, hn⟩) := by
    rintro (⟨j, i⟩ | ⟨k, g⟩)
    · exact (gnGraph_reachable_hub j i).trans (gnGraph_reachable_hub_zero hn i.val i rfl)
    · obtain ⟨j, i, hadj⟩ := gnGraph_exists_adj_core k g
      exact (hadj.reachable.trans (gnGraph_reachable_hub j i)).trans (gnGraph_reachable_hub_zero hn i.val i rfl)
  rw [SimpleGraph.connected_iff]
  exact ⟨fun x y => (hbase x).trans (hbase y).symm, ⟨core 4 ⟨0, hn⟩⟩⟩


/-- `Gn` has `5n + 4(n-1)` vertices, five per block and four per gap, which is `9n - 4` for `n` at least
one. This is the count stated in the source. -/
theorem card_gnVertex : Fintype.card (GnVertex n) = 5 * n + 4 * (n - 1) := by
  simp [GnVertex, Fintype.card_sum, Fintype.card_prod]

theorem card_gnVertex_eq (hn : 1 ≤ n) : Fintype.card (GnVertex n) = 9 * n - 4 := by
  rw [card_gnVertex]
  omega

/-- The first half of 2-connectedness: `Gn` has at least three vertices. Even `G1`, a single wheel, has
five. -/
theorem three_le_card_gnVertex (hn : 1 ≤ n) : 3 ≤ Fintype.card (GnVertex n) := by
  rw [card_gnVertex]
  omega


end ZonalGraphs
