import ZonalGraphs.DutchWindmill

namespace ZonalGraphs

/-!
# The Dutch windmill graph

`D(S)` for a multiset `S` of cycles is built by taking one cycle per element of `S` and identifying
one vertex of each, the *hub*.  This module constructs it.

A blade of length `len b` contributes `len b` non-hub vertices, so its cycle has `len b + 1`
vertices; requiring `2 ≤ len b` makes every blade a cycle of length at least three.  Vertices are
indexed by `Option (Σ b, Fin (len b))`, with `none` the hub, and a blade's vertices form a path whose
two ends are joined to the hub.

The point of the module is that this really is a connected graph, `windmillGraph_connected`, so it
can be fed to `PlaneGraph`, together with the petal data — `windmillPetal` — that the results in
`ZonalGraphs.DutchWindmill` consume.  Connectivity is proved by walking each vertex down its own
blade to the hub.
-/

universe w

variable {Blade : Type w} [DecidableEq Blade]

/-- The vertices of a Dutch windmill: the hub `none`, together with the `len b` non-hub vertices of
each blade `b`. -/
abbrev WindmillVertex (len : Blade → ℕ) := Option (Σ b : Blade, Fin (len b))

/-- A blade vertex is an *end* of its blade when it is the first or the last vertex along it.  The
two ends are precisely the blade vertices joined to the hub. -/
def IsBladeEnd (len : Blade → ℕ) (b : Blade) (i : Fin (len b)) : Prop :=
  i.val = 0 ∨ i.val + 1 = len b

instance (len : Blade → ℕ) (b : Blade) (i : Fin (len b)) : Decidable (IsBladeEnd len b i) := by
  unfold IsBladeEnd; infer_instance

/-- Adjacency in the Dutch windmill: consecutive vertices along a common blade, and the hub joined
to both ends of every blade. -/
def windmillAdj (len : Blade → ℕ) : WindmillVertex len → WindmillVertex len → Prop
  | none, none => False
  | none, some p => IsBladeEnd len p.1 p.2
  | some p, none => IsBladeEnd len p.1 p.2
  | some p, some q => p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)

/-- The Dutch windmill graph on the blade lengths `len`. -/
def windmillGraph (len : Blade → ℕ) : SimpleGraph (WindmillVertex len) where
  Adj := windmillAdj len
  symm := by
    rintro (_ | ⟨b, i⟩) (_ | ⟨c, j⟩) hadj <;>
      simp only [windmillAdj] at hadj ⊢ <;> try exact hadj
    exact ⟨hadj.1.symm, hadj.2.symm⟩
  loopless := ⟨by
    rintro (_ | ⟨b, i⟩) hadj <;> simp only [windmillAdj] at hadj
    omega⟩

omit [DecidableEq Blade] in
/-- Every blade vertex reaches the hub, by walking down its own blade. -/
theorem reachable_hub (len : Blade → ℕ) (b : Blade) :
    ∀ (k : ℕ) (i : Fin (len b)), i.val = k →
      (windmillGraph len).Reachable (some ⟨b, i⟩) none := by
  intro k
  induction k with
  | zero =>
    intro i hi
    exact SimpleGraph.Adj.reachable (by simp only [windmillGraph, windmillAdj, IsBladeEnd]; omega)
  | succ k ih =>
    intro i hi
    have hk : k < len b := by omega
    refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) (ih ⟨k, hk⟩ rfl)
    show windmillAdj len (some ⟨b, i⟩) (some ⟨b, ⟨k, hk⟩⟩)
    refine ⟨rfl, Or.inr ?_⟩
    show k + 1 = i.val
    omega

omit [DecidableEq Blade] in
/-- The Dutch windmill graph is connected. -/
theorem windmillGraph_connected (len : Blade → ℕ) : (windmillGraph len).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun x y => ?_, ⟨none⟩⟩
  have hhub : ∀ z : WindmillVertex len, (windmillGraph len).Reachable z none := by
    rintro (_ | ⟨b, i⟩)
    · exact SimpleGraph.Reachable.refl _
    · exact reachable_hub len b i.val i rfl
  exact (hhub x).trans (hhub y).symm

/-- The petal of a blade: its non-hub vertices, that is, the blade's cycle with the hub deleted. -/
def windmillPetal (len : Blade → ℕ) (b : Blade) : Finset (WindmillVertex len) :=
  Finset.univ.image fun i : Fin (len b) => some ⟨b, i⟩

@[simp] theorem mem_windmillPetal (len : Blade → ℕ) (b : Blade) (x : WindmillVertex len) :
    x ∈ windmillPetal len b ↔ ∃ i : Fin (len b), x = some ⟨b, i⟩ := by
  simp [windmillPetal, eq_comm]

/-- The hub lies on no petal. -/
theorem hub_notMem_windmillPetal (len : Blade → ℕ) (b : Blade) :
    (none : WindmillVertex len) ∉ windmillPetal len b := by
  simp

/-- Petals of distinct blades are disjoint: distinct cycles meet only in the hub. -/
theorem windmillPetal_disjoint (len : Blade → ℕ) (b c : Blade) (hbc : b ≠ c) :
    Disjoint (windmillPetal len b) (windmillPetal len c) := by
  rw [Finset.disjoint_left]
  rintro x hb hc
  obtain ⟨i, rfl⟩ := (mem_windmillPetal len b x).mp hb
  obtain ⟨j, hj⟩ := (mem_windmillPetal len c _).mp hc
  exact hbc (congrArg Sigma.fst (Option.some_injective _ hj))

/-- A petal has exactly `len b` vertices, so blades that are cycles give petals with at least two
vertices — enough to prescribe any petal sum. -/
theorem card_windmillPetal (len : Blade → ℕ) (b : Blade) :
    (windmillPetal len b).card = len b := by
  have hinj : Function.Injective fun i : Fin (len b) => (some ⟨b, i⟩ : WindmillVertex len) := by
    intro i j hij
    simpa using Option.some_injective _ hij
  rw [windmillPetal, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

end ZonalGraphs
