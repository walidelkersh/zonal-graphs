import ZonalGraphs.CycleRankTwo

namespace ZonalGraphs

/-!
# The theta graph

A graph of cycle rank two and type (3) consists of three internally disjoint paths joining two branch
vertices.  This module builds it, following `windmillGraph`: indices are compared as natural numbers so
that no dependent casts appear, and connectivity is proved by walking each interior vertex down its own
path to a branch vertex.

Vertices are `Bool ⊕ (Σ i : Fin 3, Fin (len i))`, with `inl false` and `inl true` the two branch vertices
and `len i` the number of interior vertices of the `i`-th path.  A path with no interior vertex is a
single edge between the branch vertices, which is why they are adjacent exactly when some `len i` is zero.
-/

universe u

variable {len : Fin 3 → ℕ}

/-- Vertices of a theta graph: two branch vertices and the interiors of three paths. -/
abbrev ThetaVertex (len : Fin 3 → ℕ) := Bool ⊕ (Σ i : Fin 3, Fin (len i))

/-- Adjacency in a theta graph. -/
def thetaAdj (len : Fin 3 → ℕ) : ThetaVertex len → ThetaVertex len → Prop
  | .inl a, .inl b => a ≠ b ∧ ∃ i, len i = 0
  | .inl false, .inr p => p.2.val = 0
  | .inl true, .inr p => p.2.val + 1 = len p.1
  | .inr p, .inl false => p.2.val = 0
  | .inr p, .inl true => p.2.val + 1 = len p.1
  | .inr p, .inr q => p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)

/-- The theta graph on the interior sizes `len`. -/
def thetaGraph (len : Fin 3 → ℕ) : SimpleGraph (ThetaVertex len) where
  Adj := thetaAdj len
  symm := by
    rintro (a | p) (b | q) hadj
    · exact ⟨Ne.symm hadj.1, hadj.2⟩
    · cases a <;> exact hadj
    · cases b <;> exact hadj
    · exact ⟨hadj.1.symm, hadj.2.symm⟩
  loopless := ⟨by
    rintro (a | p) hadj
    · exact hadj.1 rfl
    · have := hadj.2; omega⟩

/-- Every interior vertex reaches the branch vertex `inl false`, by walking down its own path. -/
theorem reachable_branch (len : Fin 3 → ℕ) (i : Fin 3) :
    ∀ (k : ℕ) (x : Fin (len i)), x.val = k →
      (thetaGraph len).Reachable (.inr ⟨i, x⟩) (.inl false) := by
  intro k
  induction k with
  | zero =>
    intro x hx
    exact SimpleGraph.Adj.reachable (show thetaAdj len (.inr ⟨i, x⟩) (.inl false) from hx)
  | succ k ih =>
    intro x hx
    have hk : k < len i := by omega
    refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) (ih ⟨k, hk⟩ rfl)
    show thetaAdj len (.inr ⟨i, x⟩) (.inr ⟨i, ⟨k, hk⟩⟩)
    refine ⟨rfl, Or.inr ?_⟩
    show k + 1 = x.val
    omega

/-- The two branch vertices are joined, directly when some path is a single edge and otherwise through the
last interior vertex of any path. -/
theorem reachable_branches (len : Fin 3 → ℕ) :
    (thetaGraph len).Reachable (.inl true) (.inl false) := by
  by_cases hzero : ∃ i, len i = 0
  · exact SimpleGraph.Adj.reachable
      (show thetaAdj len (.inl true) (.inl false) from ⟨by decide, hzero⟩)
  · push_neg at hzero
    have hpos : 0 < len 0 := Nat.pos_of_ne_zero (hzero 0)
    have hlt : len 0 - 1 < len 0 := by omega
    refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_)
      (reachable_branch len 0 (len 0 - 1) ⟨len 0 - 1, hlt⟩ rfl)
    show thetaAdj len (.inl true) (.inr ⟨0, ⟨len 0 - 1, hlt⟩⟩)
    show len 0 - 1 + 1 = len 0
    omega

/-- The theta graph is connected. -/
theorem thetaGraph_connected (len : Fin 3 → ℕ) : (thetaGraph len).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun x y => ?_, ⟨.inl false⟩⟩
  have hbase : ∀ z : ThetaVertex len, (thetaGraph len).Reachable z (.inl false) := by
    rintro (a | p)
    · cases a
      · exact SimpleGraph.Reachable.refl _
      · exact reachable_branches len
    · exact reachable_branch len p.1 p.2.val p.2 rfl
  exact (hbase x).trans (hbase y).symm

end ZonalGraphs
