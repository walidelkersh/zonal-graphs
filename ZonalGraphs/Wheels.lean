import ZonalGraphs.Definitions
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Wheel graphs

This file formalizes Theorem 2.1.5 of Bowling, *Zonality in Graphs* (2023), for the
standard plane realization of the wheel.  The rim vertices are `some i`, the hub is `none`,
the interior face `some i` is the triangle at rim edge `i`, and `none` is the exterior face.
-/

open scoped Classical

namespace PlaneGraph

/-- Cyclic successor on the rim of a wheel. -/
def wheelSucc (n : ℕ) (hn : 3 ≤ n) (i : Fin n) : Fin n :=
  ⟨(i + 1) % n, Nat.mod_lt _ (by omega)⟩

/-- The abstract wheel graph: a cycle on `Fin n` together with a hub adjacent to every
rim vertex.  Thus this is the graph join `Cₙ ∨ K₁`, represented on `Option (Fin n)`. -/
def wheelGraph (n : ℕ) : SimpleGraph (Option (Fin n)) where
  Adj x y := match x, y with
    | some i, some j => (SimpleGraph.cycleGraph n).Adj i j
    | none, some _ => True
    | some _, none => True
    | none, none => False
  symm := by
    intro x y
    cases x <;> cases y <;> simp_all [SimpleGraph.adj_comm]
  loopless := ⟨by
    intro x
    cases x <;> simp⟩

lemma wheelGraph_connected (n : ℕ) : (wheelGraph n).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨none, fun v => ?_⟩
  cases v with
  | none => exact SimpleGraph.Reachable.rfl
  | some i => exact (show (wheelGraph n).Adj none (some i) by simp [wheelGraph]).reachable

/-- The standard plane wheel `Wₙ`: its `n` interior faces are triangles and its exterior
boundary is precisely the rim cycle. -/
noncomputable def ofWheel (n : ℕ) (hn : 3 ≤ n) :
    PlaneGraph (Option (Fin n)) (Option (Fin n)) where
  graph := wheelGraph n
  connected := wheelGraph_connected n
  boundary
    | none => Finset.univ.erase none
    | some i => {none, some i, some (wheelSucc n hn i)}
  boundaryEdges := fun _ => ∅
  exterior := none

lemma wheelSucc_ne (n : ℕ) (hn : 3 ≤ n) (i : Fin n) : wheelSucc n hn i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [wheelSucc] at hv
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi] at hv
    omega
  · have hieq : i.val + 1 = n := by omega
    rw [hieq, Nat.mod_self] at hv
    omega

/-- Three permitted labels sum to zero modulo three only when they are all equal. -/
lemma zonalLabel_eq_of_three_sum_eq_zero (a b c : ZonalLabel)
    (h : (a : ZMod 3) + b + c = 0) : a = b ∧ b = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals first | (constructor <;> rfl) | (exfalso; revert h; native_decide)

/-- A zero-valued triangular wheel face forces both rim labels to equal the hub label. -/
lemma labels_equal_on_wheel_triangle (n : ℕ) (hn : 3 ≤ n)
    (labeling : VertexLabeling (Option (Fin n))) (i : Fin n)
    (h : (ofWheel n hn).zoneValue labeling (some i) = 0) :
    labeling none = labeling (some i) ∧
      labeling (some i) = labeling (some (wheelSucc n hn i)) := by
  apply zonalLabel_eq_of_three_sum_eq_zero
  have hs : (some i : Option (Fin n)) ≠ some (wheelSucc n hn i) := by
    simpa using (wheelSucc_ne n hn i).symm
  simpa [zoneValue, ofWheel, hs, add_assoc] using h

/-- If every interior triangle of a wheel has value zero, every vertex has the hub's label. -/
lemma wheel_labels_constant_of_interior_zonal (n : ℕ) (hn : 3 ≤ n)
    (labeling : VertexLabeling (Option (Fin n)))
    (h : ∀ i : Fin n, (ofWheel n hn).zoneValue labeling (some i) = 0) :
    ∀ v, labeling v = labeling none := by
  intro v
  cases v with
  | none => rfl
  | some i => exact (labels_equal_on_wheel_triangle n hn labeling i (h i)).1.symm

/-- The value of the exterior face under a constant labeling is `n` times that label. -/
lemma wheel_exterior_value_of_constant (n : ℕ) (hn : 3 ≤ n)
    (labeling : VertexLabeling (Option (Fin n)))
    (h : ∀ v, labeling v = labeling none) :
    (ofWheel n hn).zoneValue labeling none = (n : ZMod 3) * (labeling none : ZMod 3) := by
  simp only [zoneValue, ofWheel, h]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ none)]
  simp [Fintype.card_option, nsmul_eq_mul]

/-- The constant-one labeling is zonal when the rim length is divisible by three. -/
lemma wheel_constant_one_is_zonal (n : ℕ) (hn : 3 ≤ n) (hmod : n ≡ 0 [MOD 3]) :
    (ofWheel n hn).IsZonalLabeling (fun _ => (⟨1, by decide⟩ : ZonalLabel)) := by
  intro R
  cases R with
  | none =>
      rw [wheel_exterior_value_of_constant n hn]
      · rw [show (n : ZMod 3) = 0 by
          rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff]
          exact hmod]
        simp
      · intro v
        rfl
  | some i =>
      have hs : (some i : Option (Fin n)) ≠ some (wheelSucc n hn i) := by
        simpa using (wheelSucc_ne n hn i).symm
      simp only [zoneValue, ofWheel]
      rw [Finset.sum_insert (by simp), Finset.sum_insert (by simpa using hs), Finset.sum_singleton]
      native_decide

/-- **Theorem 2.1.5.** For `n ≥ 3`, the standard wheel graph
`Wₙ = Cₙ ∨ K₁` is zonal if and only if `n ≡ 0 (mod 3)`. -/
theorem wheel_isZonal_iff_modEq_zero (n : ℕ) (hn : 3 ≤ n) :
    (ofWheel n hn).IsZonal ↔ n ≡ 0 [MOD 3] := by
  constructor
  · rintro ⟨labeling, hlabeling⟩
    have hconst : ∀ v, labeling v = labeling none :=
      wheel_labels_constant_of_interior_zonal n hn labeling (fun i => hlabeling (some i))
    have hext := hlabeling none
    rw [wheel_exterior_value_of_constant n hn labeling hconst] at hext
    have hc : (labeling none : ZMod 3) ≠ 0 := (labeling none).property
    have hnzero : (n : ZMod 3) = 0 := by
      exact (mul_eq_zero.mp hext).resolve_right hc
    rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff] at hnzero
    exact hnzero
  · intro hmod
    exact ⟨_, wheel_constant_one_is_zonal n hn hmod⟩

end PlaneGraph
end ZonalGraphs
