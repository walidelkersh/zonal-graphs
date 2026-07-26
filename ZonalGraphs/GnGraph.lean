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


theorem core_ne_gap {j : Fin 5} {i : Fin n} {k : Fin 4} {g : Fin (n - 1)} : core j i ≠ gap k g := by
  simp [core, gap]

/-- Core vertices with different roles differ, whatever their blocks. -/
theorem core_ne_core {j₁ j₂ : Fin 5} {i₁ i₂ : Fin n} (h : j₁ ≠ j₂) : core j₁ i₁ ≠ core j₂ i₂ := by
  simp [core, h]

/-- A connector is never a core vertex. -/
theorem gap_ne_core {j : Fin 5} {i : Fin n} {k : Fin 4} {g : Fin (n - 1)} : gap k g ≠ core j i := by
  simp [core, gap]

/-- Connectors with different roles differ, whatever their gaps. -/
theorem gap_ne_gap {k₁ k₂ : Fin 4} {g₁ g₂ : Fin (n - 1)} (h : k₁ ≠ k₂) : gap k₁ g₁ ≠ gap k₂ g₂ := by
  simp [gap, h]

/-- Core vertices of different blocks differ, whatever their roles. -/
theorem core_ne_core_block {j₁ j₂ : Fin 5} {i₁ i₂ : Fin n} (h : i₁ ≠ i₂) :
    core j₁ i₁ ≠ core j₂ i₂ := by
  simp [core, h]

section Deletion

variable {c : GnVertex n}

/-- Adjacency survives into the graph with `c` removed, provided neither end is `c`. -/
theorem gnGraph_induce_adj {a b : GnVertex n} (ha : a ∈ ({c}ᶜ : Set (GnVertex n)))
    (hb : b ∈ ({c}ᶜ : Set (GnVertex n))) (hadj : (gnGraph n).Adj a b) :
    ((gnGraph n).induce ({c}ᶜ : Set (GnVertex n))).Adj ⟨a, ha⟩ ⟨b, hb⟩ := hadj

/-- The route `v - r - y - w - s - v` between the hubs of consecutive blocks, usable when none of its four
interior vertices is the deleted vertex. -/
theorem gnGraph_route_rw (g : Fin (n - 1)) (i i' : Fin n) (hi : i.val = g.val + 1)
    (hi' : i'.val = g.val) (hc : (core 4 i) ∈ ({c}ᶜ : Set (GnVertex n)))
    (hc' : (core 4 i') ∈ ({c}ᶜ : Set (GnVertex n)))
    (h₁ : (core 0 i) ∈ ({c}ᶜ : Set (GnVertex n))) (h₂ : (gap 2 g) ∈ ({c}ᶜ : Set (GnVertex n)))
    (h₃ : (gap 0 g) ∈ ({c}ᶜ : Set (GnVertex n))) (h₄ : (core 1 i') ∈ ({c}ᶜ : Set (GnVertex n))) :
    ((gnGraph n).induce ({c}ᶜ : Set (GnVertex n))).Reachable ⟨core 4 i, hc⟩ ⟨core 4 i', hc'⟩ :=
  (gnGraph_induce_adj hc h₁ ⟨rfl, Or.inl ⟨rfl, by decide⟩⟩).reachable.trans
    ((gnGraph_induce_adj h₁ h₂ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hi.symm⟩)))).reachable.trans
      ((gnGraph_induce_adj h₂ h₃
          ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩).reachable.trans
        ((gnGraph_induce_adj h₃ h₄ (Or.inl ⟨rfl, rfl, hi'.symm⟩)).reachable.trans
          (gnGraph_induce_adj h₄ hc' ⟨rfl, Or.inr (Or.inl ⟨rfl, by decide⟩)⟩).reachable)))

/-- The route `v - u - z - x - t - v`, vertex-disjoint from `gnGraph_route_rw`. -/
theorem gnGraph_route_ux (g : Fin (n - 1)) (i i' : Fin n) (hi : i.val = g.val + 1)
    (hi' : i'.val = g.val) (hc : (core 4 i) ∈ ({c}ᶜ : Set (GnVertex n)))
    (hc' : (core 4 i') ∈ ({c}ᶜ : Set (GnVertex n)))
    (h₁ : (core 3 i) ∈ ({c}ᶜ : Set (GnVertex n))) (h₂ : (gap 3 g) ∈ ({c}ᶜ : Set (GnVertex n)))
    (h₃ : (gap 1 g) ∈ ({c}ᶜ : Set (GnVertex n))) (h₄ : (core 2 i') ∈ ({c}ᶜ : Set (GnVertex n))) :
    ((gnGraph n).induce ({c}ᶜ : Set (GnVertex n))).Reachable ⟨core 4 i, hc⟩ ⟨core 4 i', hc'⟩ :=
  (gnGraph_induce_adj hc h₁ ⟨rfl, Or.inl ⟨rfl, by decide⟩⟩).reachable.trans
    ((gnGraph_induce_adj h₁ h₂ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hi.symm⟩)))).reachable.trans
      ((gnGraph_induce_adj h₂ h₃
          ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))⟩).reachable.trans
        ((gnGraph_induce_adj h₃ h₄ (Or.inr (Or.inl ⟨rfl, rfl, hi'.symm⟩))).reachable.trans
          (gnGraph_induce_adj h₄ hc' ⟨rfl, Or.inr (Or.inl ⟨rfl, by decide⟩)⟩).reachable)))

/-- **The redundancy across a gap.** If the hubs of two consecutive blocks both survive the deletion of a
single vertex `c`, they remain connected.

The two routes are vertex-disjoint, so `c` lies on at most one and the other is intact. This is what makes
`Gn` 2-connected between blocks, and it is the only inter-block route there is, `Gn` being a path of blocks
rather than a cycle. -/
theorem gnGraph_induce_reachable_hubs (g : Fin (n - 1)) (i i' : Fin n) (hi : i.val = g.val + 1)
    (hi' : i'.val = g.val) (hc : (core 4 i) ∈ ({c}ᶜ : Set (GnVertex n)))
    (hc' : (core 4 i') ∈ ({c}ᶜ : Set (GnVertex n))) :
    ((gnGraph n).induce ({c}ᶜ : Set (GnVertex n))).Reachable ⟨core 4 i, hc⟩ ⟨core 4 i', hc'⟩ := by
  classical
  by_cases h₁ : core 0 i = c
  · refine gnGraph_route_ux g i i' hi hi' hc hc' ?_ ?_ ?_ ?_ <;> subst h₁ <;>
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] <;>
      first
        | exact core_ne_core (by decide)
        | exact gap_ne_core
  by_cases h₂ : gap 2 g = c
  · refine gnGraph_route_ux g i i' hi hi' hc hc' ?_ ?_ ?_ ?_ <;> subst h₂ <;>
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] <;>
      first
        | exact core_ne_gap
        | exact gap_ne_gap (by decide)
  by_cases h₃ : gap 0 g = c
  · refine gnGraph_route_ux g i i' hi hi' hc hc' ?_ ?_ ?_ ?_ <;> subst h₃ <;>
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] <;>
      first
        | exact core_ne_gap
        | exact gap_ne_gap (by decide)
  by_cases h₄ : core 1 i' = c
  · refine gnGraph_route_ux g i i' hi hi' hc hc' ?_ ?_ ?_ ?_ <;> subst h₄ <;>
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] <;>
      first
        | exact core_ne_core (by decide)
        | exact gap_ne_core
  exact gnGraph_route_rw g i i' hi hi' hc hc' (by simpa using h₁) (by simpa using h₂)
    (by simpa using h₃) (by simpa using h₄)

/-- Any surviving core vertex of a block reaches that block's hub, provided the hub itself survives. -/
theorem gnGraph_induce_reachable_hub (j : Fin 5) (i : Fin n)
    (hx : core j i ∈ ({c}ᶜ : Set (GnVertex n)))
    (hv : core 4 i ∈ ({c}ᶜ : Set (GnVertex n))) :
    ((gnGraph n).induce ({c}ᶜ : Set (GnVertex n))).Reachable ⟨core j i, hx⟩ ⟨core 4 i, hv⟩ := by
  by_cases hj : j = 4
  · subst hj
    exact SimpleGraph.Reachable.refl _
  · exact (gnGraph_induce_adj hx hv ⟨rfl, Or.inr (Or.inl ⟨rfl, hj⟩)⟩).reachable


/-- **The escape route when a hub is deleted.** With the hub of block `g` removed, every rim vertex of that
block still reaches the hub of block `g + 1`.

No case analysis is needed here, unlike the gap redundancy: the deleted vertex is known to be the hub, so
every other vertex survives automatically. The rim vertices `s` and `t` leave through their own gap, along
`s - w - y - r - v` and `t - x - z - u - v`, and `r` and `u` join them across the surviving rim edges `r-s`
and `t-u`. -/
theorem gnGraph_induce_rim_reachable_next (i i' : Fin n) (g : Fin (n - 1)) (hi : i.val = g.val)
    (hi' : i'.val = g.val + 1) (j : Fin 5) (hj : j ≠ 4)
    (hx : core j i ∈ (({core 4 i}ᶜ) : Set (GnVertex n)))
    (hv : core 4 i' ∈ (({core 4 i}ᶜ) : Set (GnVertex n))) :
    ((gnGraph n).induce (({core 4 i}ᶜ) : Set (GnVertex n))).Reachable ⟨core j i, hx⟩
      ⟨core 4 i', hv⟩ := by
  have hne : i ≠ i' := by
    intro h
    subst h
    omega
  -- memberships: everything other than the hub of block `i` survives
  have m₁ : core 1 i ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by
    simpa using core_ne_core (by decide : (1 : Fin 5) ≠ 4)
  have m₂ : core 2 i ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by
    simpa using core_ne_core (by decide : (2 : Fin 5) ≠ 4)
  have mw : gap 0 g ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by simpa using gap_ne_core
  have mx : gap 1 g ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by simpa using gap_ne_core
  have my : gap 2 g ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by simpa using gap_ne_core
  have mz : gap 3 g ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by simpa using gap_ne_core
  have mr : core 0 i' ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by
    simpa using core_ne_core_block hne.symm
  have mu : core 3 i' ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by
    simpa using core_ne_core_block hne.symm
  -- the route out of `s`, and the route out of `t`
  have routeS : ((gnGraph n).induce (({core 4 i}ᶜ) : Set (GnVertex n))).Reachable
      ⟨core 1 i, m₁⟩ ⟨core 4 i', hv⟩ :=
    (gnGraph_induce_adj m₁ mw (Or.inl ⟨rfl, rfl, hi.symm⟩)).reachable.trans
      ((gnGraph_induce_adj mw my
          ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩).reachable.trans
        ((gnGraph_induce_adj my mr
            (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hi'.symm⟩)))).reachable.trans
          (gnGraph_induce_adj mr hv ⟨rfl, Or.inr (Or.inl ⟨rfl, by decide⟩)⟩).reachable))
  have routeT : ((gnGraph n).induce (({core 4 i}ᶜ) : Set (GnVertex n))).Reachable
      ⟨core 2 i, m₂⟩ ⟨core 4 i', hv⟩ :=
    (gnGraph_induce_adj m₂ mx (Or.inr (Or.inl ⟨rfl, rfl, hi.symm⟩))).reachable.trans
      ((gnGraph_induce_adj mx mz
          ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))⟩).reachable.trans
        ((gnGraph_induce_adj mz mu
            (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hi'.symm⟩)))).reachable.trans
          (gnGraph_induce_adj mu hv ⟨rfl, Or.inr (Or.inl ⟨rfl, by decide⟩)⟩).reachable))
  -- the four rim vertices, `r` and `u` joining across the surviving rim edges
  fin_cases j
  · exact (gnGraph_induce_adj hx m₁ ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩).reachable.trans routeS
  · exact routeS
  · exact routeT
  · exact (gnGraph_induce_adj hx m₂ ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨rfl, rfl⟩)))))⟩).reachable.trans routeT
  · exact absurd rfl hj


/-- **The mirror escape route.** With the hub of block `g + 1` removed, every rim vertex of that block still
reaches the hub of block `g`, through the previous gap rather than the next one.

This is the reflection of `gnGraph_induce_rim_reachable_next`, needed for the last block, which has no next
gap. Here `r` and `u` leave along `r - y - w - s - v` and `u - z - x - t - v`, and `s` and `t` join them
across the rim edges. -/
theorem gnGraph_induce_rim_reachable_prev (i i' : Fin n) (g : Fin (n - 1))
    (hi : i.val = g.val + 1) (hi' : i'.val = g.val) (j : Fin 5) (hj : j ≠ 4)
    (hx : core j i ∈ (({core 4 i}ᶜ) : Set (GnVertex n)))
    (hv : core 4 i' ∈ (({core 4 i}ᶜ) : Set (GnVertex n))) :
    ((gnGraph n).induce (({core 4 i}ᶜ) : Set (GnVertex n))).Reachable ⟨core j i, hx⟩
      ⟨core 4 i', hv⟩ := by
  have hne : i ≠ i' := by
    intro h
    subst h
    omega
  have m₀ : core 0 i ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by
    simpa using core_ne_core (by decide : (0 : Fin 5) ≠ 4)
  have m₃ : core 3 i ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by
    simpa using core_ne_core (by decide : (3 : Fin 5) ≠ 4)
  have mw : gap 0 g ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by simpa using gap_ne_core
  have mx : gap 1 g ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by simpa using gap_ne_core
  have my : gap 2 g ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by simpa using gap_ne_core
  have mz : gap 3 g ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by simpa using gap_ne_core
  have ms : core 1 i' ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by
    simpa using core_ne_core_block hne.symm
  have mt : core 2 i' ∈ (({core 4 i}ᶜ) : Set (GnVertex n)) := by
    simpa using core_ne_core_block hne.symm
  have routeR : ((gnGraph n).induce (({core 4 i}ᶜ) : Set (GnVertex n))).Reachable
      ⟨core 0 i, m₀⟩ ⟨core 4 i', hv⟩ :=
    (gnGraph_induce_adj m₀ my (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hi.symm⟩)))).reachable.trans
      ((gnGraph_induce_adj my mw
          ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩).reachable.trans
        ((gnGraph_induce_adj mw ms (Or.inl ⟨rfl, rfl, hi'.symm⟩)).reachable.trans
          (gnGraph_induce_adj ms hv ⟨rfl, Or.inr (Or.inl ⟨rfl, by decide⟩)⟩).reachable))
  have routeU : ((gnGraph n).induce (({core 4 i}ᶜ) : Set (GnVertex n))).Reachable
      ⟨core 3 i, m₃⟩ ⟨core 4 i', hv⟩ :=
    (gnGraph_induce_adj m₃ mz (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hi.symm⟩)))).reachable.trans
      ((gnGraph_induce_adj mz mx
          ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))⟩).reachable.trans
        ((gnGraph_induce_adj mx mt (Or.inr (Or.inl ⟨rfl, rfl, hi'.symm⟩))).reachable.trans
          (gnGraph_induce_adj mt hv ⟨rfl, Or.inr (Or.inl ⟨rfl, by decide⟩)⟩).reachable))
  fin_cases j
  · exact routeR
  · exact (gnGraph_induce_adj hx m₀ ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩).reachable.trans
      routeR
  · exact (gnGraph_induce_adj hx m₃
      ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩).reachable.trans routeU
  · exact routeU
  · exact absurd rfl hj


/-- With no hub deleted, every hub still reaches the hub of block `0`, by the gap redundancy one gap at a
time. -/
theorem gnGraph_induce_reachable_hub_zero (hn : 0 < n) (hnohub : ∀ k : Fin n, c ≠ core 4 k) :
    ∀ (m : ℕ) (i : Fin n), i.val = m →
      ((gnGraph n).induce ({c}ᶜ : Set (GnVertex n))).Reachable
        ⟨core 4 i, by simpa using (hnohub i).symm⟩
        ⟨core 4 ⟨0, hn⟩, by simpa using (hnohub ⟨0, hn⟩).symm⟩ := by
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
    exact (gnGraph_induce_reachable_hubs ⟨m, hlt⟩ i ⟨m, hm⟩ hi rfl _ _).trans (ih ⟨m, hm⟩ rfl)


/-- One step from a connector to a hub, through a surviving core attachment point. -/
theorem gnGraph_induce_gap_via_core {k : Fin 4} {g : Fin (n - 1)} {j : Fin 5} {i : Fin n}
    (hadj : (gnGraph n).Adj (gap k g) (core j i)) (hj : j ≠ 4)
    (hk : gap k g ∈ ({c}ᶜ : Set (GnVertex n))) (hjm : core j i ∈ ({c}ᶜ : Set (GnVertex n)))
    (hv : core 4 i ∈ ({c}ᶜ : Set (GnVertex n))) :
    ((gnGraph n).induce ({c}ᶜ : Set (GnVertex n))).Reachable ⟨gap k g, hk⟩ ⟨core 4 i, hv⟩ :=
  (gnGraph_induce_adj hk hjm hadj).reachable.trans
    (gnGraph_induce_adj hjm hv ⟨rfl, Or.inr (Or.inl ⟨rfl, hj⟩)⟩).reachable

/-- **A surviving connector reaches some surviving hub.**

Each connector has its own core attachment point: `w` meets `s` and `x` meets `t` in their own block, `y`
meets `r` and `z` meets `u` in the next. When that point survives the connector uses it; when it is the
deleted vertex the connector crosses to its gap partner, `w` to `y` and `x` to `z`, whose own attachment then
certainly survives, the deleted vertex being already accounted for.

No hub is deleted here, so every hub is an available target. -/
theorem gnGraph_induce_gap_reachable_some_hub (hnohub : ∀ k : Fin n, c ≠ core 4 k) (k : Fin 4)
    (g : Fin (n - 1)) (hx : gap k g ∈ ({c}ᶜ : Set (GnVertex n))) :
    ∃ i : Fin n, ((gnGraph n).induce ({c}ᶜ : Set (GnVertex n))).Reachable ⟨gap k g, hx⟩
      ⟨core 4 i, by simpa using (hnohub i).symm⟩ := by
  have hg : g.val < n - 1 := g.isLt
  have h0 : g.val < n := by omega
  have h1 : g.val + 1 < n := by omega
  have hblk : (⟨g.val, h0⟩ : Fin n) ≠ (⟨g.val + 1, h1⟩ : Fin n) := by
    simp [Fin.ext_iff]
  -- the two candidate attachment points for each connector, and the crossing between the partners
  have wy : (gnGraph n).Adj (gap 0 g) (gap 2 g) :=
    ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
  have xz : (gnGraph n).Adj (gap 1 g) (gap 3 g) :=
    ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))⟩
  have aS : (gnGraph n).Adj (gap 0 g) (core 1 ⟨g.val, h0⟩) := Or.inl ⟨rfl, rfl, rfl⟩
  have aT : (gnGraph n).Adj (gap 1 g) (core 2 ⟨g.val, h0⟩) := Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  have aR : (gnGraph n).Adj (gap 2 g) (core 0 ⟨g.val + 1, h1⟩) :=
    Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have aU : (gnGraph n).Adj (gap 3 g) (core 3 ⟨g.val + 1, h1⟩) :=
    Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  fin_cases k
  · by_cases h : core 1 ⟨g.val, h0⟩ = c
    · have mr : core 0 (⟨g.val + 1, h1⟩ : Fin n) ∈ ({c}ᶜ : Set (GnVertex n)) := by
        rw [← h]
        simpa using core_ne_core_block hblk.symm
      have my : gap 2 g ∈ ({c}ᶜ : Set (GnVertex n)) := by rw [← h]; simpa using gap_ne_core
      exact ⟨⟨g.val + 1, h1⟩, (gnGraph_induce_adj hx my wy).reachable.trans
        (gnGraph_induce_gap_via_core aR (by decide) my mr _)⟩
    · exact ⟨⟨g.val, h0⟩, gnGraph_induce_gap_via_core aS (by decide) hx (by simpa using h) _⟩
  · by_cases h : core 2 ⟨g.val, h0⟩ = c
    · have mu : core 3 (⟨g.val + 1, h1⟩ : Fin n) ∈ ({c}ᶜ : Set (GnVertex n)) := by
        rw [← h]
        simpa using core_ne_core_block hblk.symm
      have mz : gap 3 g ∈ ({c}ᶜ : Set (GnVertex n)) := by rw [← h]; simpa using gap_ne_core
      exact ⟨⟨g.val + 1, h1⟩, (gnGraph_induce_adj hx mz xz).reachable.trans
        (gnGraph_induce_gap_via_core aU (by decide) mz mu _)⟩
    · exact ⟨⟨g.val, h0⟩, gnGraph_induce_gap_via_core aT (by decide) hx (by simpa using h) _⟩
  · by_cases h : core 0 ⟨g.val + 1, h1⟩ = c
    · have ms : core 1 (⟨g.val, h0⟩ : Fin n) ∈ ({c}ᶜ : Set (GnVertex n)) := by
        rw [← h]
        simpa using core_ne_core_block hblk
      have mw : gap 0 g ∈ ({c}ᶜ : Set (GnVertex n)) := by rw [← h]; simpa using gap_ne_core
      exact ⟨⟨g.val, h0⟩, (gnGraph_induce_adj hx mw wy.symm).reachable.trans
        (gnGraph_induce_gap_via_core aS (by decide) mw ms _)⟩
    · exact ⟨⟨g.val + 1, h1⟩,
        gnGraph_induce_gap_via_core aR (by decide) hx (by simpa using h) _⟩
  · by_cases h : core 3 ⟨g.val + 1, h1⟩ = c
    · have mt : core 2 (⟨g.val, h0⟩ : Fin n) ∈ ({c}ᶜ : Set (GnVertex n)) := by
        rw [← h]
        simpa using core_ne_core_block hblk
      have mx : gap 1 g ∈ ({c}ᶜ : Set (GnVertex n)) := by rw [← h]; simpa using gap_ne_core
      exact ⟨⟨g.val, h0⟩, (gnGraph_induce_adj hx mx xz.symm).reachable.trans
        (gnGraph_induce_gap_via_core aT (by decide) mx mt _)⟩
    · exact ⟨⟨g.val + 1, h1⟩,
        gnGraph_induce_gap_via_core aU (by decide) hx (by simpa using h) _⟩

/-- **Range-restricted hub chaining.** A hub reaches a lower hub provided every hub at or above the lower
index survives. Chaining all the way to block `0` is not always possible, since a deleted hub blocks the way,
so the range is a hypothesis. -/
theorem gnGraph_induce_hub_down (lo : ℕ) (hsurv : ∀ k : Fin n, lo ≤ k.val → c ≠ core 4 k) :
    ∀ (d : ℕ) (i i' : Fin n) (hi : i.val = lo + d) (hi' : i'.val = lo),
      ((gnGraph n).induce ({c}ᶜ : Set (GnVertex n))).Reachable
        ⟨core 4 i, by simpa using (hsurv i (by omega)).symm⟩
        ⟨core 4 i', by simpa using (hsurv i' (by omega)).symm⟩ := by
  intro d
  induction d with
  | zero =>
    intro i i' hi hi'
    have : i = i' := Fin.ext (by omega)
    subst this
    exact SimpleGraph.Reachable.refl _
  | succ d ih =>
    intro i i' hi hi'
    have hlt : lo + d < n - 1 := by omega
    have hm : lo + d < n := by omega
    exact (gnGraph_induce_reachable_hubs ⟨lo + d, hlt⟩ i ⟨lo + d, hm⟩ hi rfl _ _).trans
      (ih ⟨lo + d, hm⟩ i' rfl hi')


/-- **The deleted vertex is not a hub.** Then every hub survives, so every core vertex reaches its own hub,
every connector reaches some hub, and the hubs chain to block `0`. -/
theorem gnGraph_induce_connected_of_nohub (hn : 0 < n) (hnohub : ∀ k : Fin n, c ≠ core 4 k) :
    ((gnGraph n).induce ({c}ᶜ : Set (GnVertex n))).Connected := by
  have manchor : core 4 (⟨0, hn⟩ : Fin n) ∈ ({c}ᶜ : Set (GnVertex n)) := by
    simpa using (hnohub ⟨0, hn⟩).symm
  have hall : ∀ z : {x : GnVertex n // x ∈ ({c}ᶜ : Set (GnVertex n))},
      ((gnGraph n).induce ({c}ᶜ : Set (GnVertex n))).Reachable z
        ⟨core 4 ⟨0, hn⟩, manchor⟩ := by
    rintro ⟨(⟨j, i⟩ | ⟨k, g⟩), hz⟩
    · exact (gnGraph_induce_reachable_hub j i hz (by simpa using (hnohub i).symm)).trans
        (gnGraph_induce_reachable_hub_zero hn hnohub i.val i rfl)
    · obtain ⟨i, hreach⟩ := gnGraph_induce_gap_reachable_some_hub hnohub k g hz
      exact hreach.trans (gnGraph_induce_reachable_hub_zero hn hnohub i.val i rfl)
  rw [SimpleGraph.connected_iff]
  exact ⟨fun x y => (hall x).trans (hall y).symm, ⟨⟨core 4 ⟨0, hn⟩, manchor⟩⟩⟩


end Deletion

end ZonalGraphs
