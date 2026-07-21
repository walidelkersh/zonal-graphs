import ZonalGraphs.Definitions
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Prescribed sums of labels

This file formalizes Lemma 2.0.4 of Bowling, *Zonality in Graphs*.  The graph
structure plays no role in the result, so the vertex set is represented by an
arbitrary finite type.
-/

universe u

open scoped Classical

/-- The sum in `ZMod 3` of a labeling of a finite vertex type.  This is the
quantity denoted `P(ℓ, X)` in Lemma 2.0.4. -/
def labelingSum {X : Type u} [Fintype X] (labeling : VertexLabeling X) : ZMod 3 :=
  ∑ x : X, (labeling x : ZMod 3)

/-- The permitted label represented by `1` in `ZMod 3`. -/
def labelOne : ZonalLabel := ⟨1, by decide⟩

/-- The permitted label represented by `2` in `ZMod 3`. -/
def labelTwo : ZonalLabel := ⟨2, by decide⟩

/-- Change the label at one specified vertex, leaving all other labels fixed. -/
def changeLabel {X : Type u} [DecidableEq X] (labeling : VertexLabeling X)
    (x : X) (newLabel : ZonalLabel) : VertexLabeling X :=
  Function.update labeling x newLabel

/-
Changing one vertex replaces its old contribution by its new contribution.
-/
lemma labelingSum_changeLabel {X : Type u} [Fintype X] [DecidableEq X]
    (labeling : VertexLabeling X) (x : X) (newLabel : ZonalLabel) :
    labelingSum (changeLabel labeling x newLabel) =
      labelingSum labeling - (labeling x : ZMod 3) + (newLabel : ZMod 3) := by
  unfold labelingSum changeLabel; simp;
  rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ x ) ];
  rw [ Finset.sum_congr rfl fun y hy => by rw [ Function.update_of_ne ( by aesop ) ] ] ; simp [ add_comm ]

/-
In particular, changing a label from `1` to `2` shifts the total by `1`
modulo three.
-/
lemma labelingSum_change_one_to_two {X : Type u} [Fintype X] [DecidableEq X]
    (labeling : VertexLabeling X) (x : X) (hx : (labeling x : ZMod 3) = 1) :
    labelingSum (changeLabel labeling x labelTwo) = labelingSum labeling + 1 := by
  rw [ labelingSum_changeLabel, hx ];
  erw [ show ( labelTwo : ZMod 3 ) = 2 from rfl ] ; ring

/-
Adding a new first vertex to a finite labeling adds precisely its label to
the total.  This is the structural induction step used below.
-/
lemma labelingSum_fin_cons {n : ℕ} (head : ZonalLabel)
    (tail : VertexLabeling (Fin n)) :
    labelingSum (Fin.cons head tail) = (head : ZMod 3) + labelingSum tail := by
  unfold labelingSum; simp [ Fin.sum_univ_succ ] ;

/-
On every `Fin n` with `n ≥ 2`, every residue in `ZMod 3` is the sum of a
permitted labeling.
-/
lemma exists_fin_labelingSum_eq (n : ℕ) (hn : 2 ≤ n) (target : ZMod 3) :
    ∃ labeling : VertexLabeling (Fin n), labelingSum labeling = target := by
  induction' hn with n hn ih generalizing target;
  · fin_cases target <;> decide;
  · obtain ⟨ labeling, h ⟩ := ih ( target - 1 );
    use Fin.cons labelOne labeling;
    erw [ labelingSum_fin_cons, h ] ; simp [ labelOne ]

/-
Transporting a labeling along an equivalence preserves its total sum.
-/
lemma labelingSum_comp_equiv {X Y : Type u} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (labeling : VertexLabeling Y) :
    labelingSum (fun x => labeling (e x)) = labelingSum labeling := by
  unfold labelingSum; exact Equiv.sum_comp e fun x => ( labeling x : ZMod 3 ) ;

/-
Lemma 2.0.4(1): a nonempty finite vertex set can be labeled with total
`1`, and can also be labeled with total `2`.
-/
theorem exists_labelingSum_one_and_two (X : Type u) [Fintype X] [Nonempty X] :
    (∃ labeling : VertexLabeling X, labelingSum labeling = 1) ∧
      ∃ labeling : VertexLabeling X, labelingSum labeling = 2 := by
  cases' lt_or_ge ( Fintype.card X ) 2 with h h <;> simp_all [ labelingSum ]
  · have hpos : 0 < Fintype.card X := Fintype.card_pos
    have hcard : Fintype.card X = 1 := by omega
    obtain ⟨ x, hx ⟩ := Fintype.card_eq_one_iff.mp hcard
    haveI : Unique X := ⟨⟨x⟩, fun y => hx y⟩
    constructor
    · use fun _ => labelOne; simp
    · use fun _ => labelTwo; simp
  · obtain ⟨labeling1, h1⟩ := exists_fin_labelingSum_eq (Fintype.card X) h 1
    obtain ⟨labeling2, h2⟩ := exists_fin_labelingSum_eq (Fintype.card X) h 2;
    refine' ⟨ ⟨ fun x => labeling1 ( Fintype.equivFin X x ), _ ⟩, ⟨ fun x => labeling2 ( Fintype.equivFin X x ), _ ⟩ ⟩ <;> simp_all [ labelingSum ];
    · rw [ ← h1, ← Equiv.sum_comp ( Fintype.equivFin X ) ];
    · rw [ ← h2, ← Equiv.sum_comp ( Fintype.equivFin X ) ]

/-
Lemma 2.0.4(2): a finite vertex set of cardinality at least two can be
labeled with total `0`.
-/
theorem exists_labelingSum_zero_of_two_le (X : Type u) [Fintype X]
    (hcard : 2 ≤ Fintype.card X) :
    ∃ labeling : VertexLabeling X, labelingSum labeling = 0 := by
  have h := exists_fin_labelingSum_eq ( Fintype.card X ) hcard 0;
  obtain ⟨labeling, hlabeling⟩ := h;
  use fun x => labeling (Fintype.equivFin X x);
  simp [labelingSum];
  convert hlabeling using 1;
  convert Equiv.sum_comp ( Fintype.equivFin X ) ( fun x => ( labeling x : ZMod 3 ) ) using 1

/-- **Lemma 2.0.4.** Combined formulation of both parts. -/
theorem lemma_2_0_4 (X : Type u) [Fintype X] [Nonempty X] :
    ((∃ labeling : VertexLabeling X, labelingSum labeling = 1) ∧
      ∃ labeling : VertexLabeling X, labelingSum labeling = 2) ∧
    (2 ≤ Fintype.card X →
      ∃ labeling : VertexLabeling X, labelingSum labeling = 0) := by
  exact ⟨exists_labelingSum_one_and_two X, exists_labelingSum_zero_of_two_le X⟩

end ZonalGraphs