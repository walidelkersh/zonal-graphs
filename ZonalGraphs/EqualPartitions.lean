import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Partition.Finpartition

namespace ZonalGraphs

/-!
# Equal-sized finite set partitions

This file formalizes Lemma 2.3.1 of Bowling, *Zonality in Graphs* (2023). The counting
argument repeatedly selects the unique part containing a distinguished remaining element.
`Finpartition` supplies the unordered partition object; the equivalence below exposes that
recursive choice directly.
-/

open Finset Fintype

universe u

variable {α : Type u} [DecidableEq α]

noncomputable section

/-- Finite partitions of `s` into exactly `m` parts, each of cardinality `k`. -/
def EqualFinpartition (s : Finset α) (m k : ℕ) :=
  {P : Finpartition s // P.parts.card = m ∧ ∀ t ∈ P.parts, t.card = k}

noncomputable instance (s : Finset α) (m k : ℕ) : Fintype (EqualFinpartition s m k) := by
  unfold EqualFinpartition
  classical
  infer_instance

/-- The product appearing in the count of unordered equal-sized partitions. -/
def equalFinpartitionCount (m k : ℕ) : ℕ :=
  ∏ i ∈ range m, ((i + 1) * k - 1).choose (k - 1)

@[simp]
theorem equalFinpartitionCount_zero (k : ℕ) : equalFinpartitionCount 0 k = 1 := by
  simp [equalFinpartitionCount]

theorem equalFinpartitionCount_succ (m k : ℕ) :
    equalFinpartitionCount (m + 1) k =
      (((m + 1) * k - 1).choose (k - 1)) * equalFinpartitionCount m k := by
  simp [equalFinpartitionCount, prod_range_succ, mul_comm]

/-- Removing a whole part from a finite partition simply erases that part. -/
theorem parts_avoid_of_mem_parts {s A : Finset α} (P : Finpartition s)
    (hA : A ∈ P.parts) : (P.avoid A).parts = P.parts.erase A := by
  ext C
  rw [Finpartition.mem_avoid, Finset.mem_erase]
  constructor
  · rintro ⟨D, hD, hDA, hDC⟩
    have hne : D ≠ A := fun h ↦ hDA (h ▸ le_rfl)
    have hdisjoint : Disjoint D A := P.disjoint hD hA hne
    rw [Finset.sdiff_eq_self_of_disjoint hdisjoint] at hDC
    subst C
    exact ⟨hne, hD⟩
  · rintro ⟨hne, hC⟩
    have hdisjoint : Disjoint C A := P.disjoint hC hA hne
    refine ⟨C, hC, ?_, Finset.sdiff_eq_self_of_disjoint hdisjoint⟩
    intro hCA
    exact P.ne_empty hC ((disjoint_of_le_iff_left_eq_bot hCA).mp hdisjoint)

/-- The possible tails of a `k`-element part containing `a`: choose the other `k - 1`
elements from `s.erase a`. -/
def EqualFinpartition.BlockTail (s : Finset α) (a : α) (k : ℕ) :=
  ↥((s.erase a).powersetCard (k - 1))

instance (s : Finset α) (a : α) (k : ℕ) : Fintype (EqualFinpartition.BlockTail s a k) := by
  unfold EqualFinpartition.BlockTail
  infer_instance

namespace EqualFinpartition.BlockTail

variable {s : Finset α} {a : α} {k : ℕ}

/-- Restore the distinguished element to a block tail. -/
def block (A : BlockTail s a k) : Finset α := insert a A.1

/-- Remove the distinguished element from a known `k`-element block. -/
def ofFinset {A : Finset α} (hAs : A ⊆ s) (haA : a ∈ A)
    (hcard : A.card = k) : BlockTail s a k := by
  refine ⟨A.erase a, mem_powersetCard.mpr ⟨?_, ?_⟩⟩
  · intro x hx
    rw [mem_erase] at hx ⊢
    exact ⟨hx.1, hAs hx.2⟩
  · rw [card_erase_of_mem haA, hcard]

@[simp]
theorem block_ofFinset {A : Finset α} (hAs : A ⊆ s) (haA : a ∈ A)
    (hcard : A.card = k) : (ofFinset hAs haA hcard).block = A := by
  exact insert_erase haA

@[simp]
theorem mem_block (A : BlockTail s a k) : a ∈ A.block := mem_insert_self _ _

theorem block_subset (ha : a ∈ s) (A : BlockTail s a k) : A.block ⊆ s := by
  intro x hx
  unfold block at hx
  rcases mem_insert.mp hx with rfl | hx
  · exact ha
  · exact (mem_erase.mp (mem_of_subset (mem_powersetCard.mp A.2).1 hx)).2

theorem not_mem_tail (A : BlockTail s a k) : a ∉ A.1 := by
  intro ha
  exact (mem_erase.mp (mem_of_subset (mem_powersetCard.mp A.2).1 ha)).1 rfl

theorem card_block (hk : 0 < k) (A : BlockTail s a k) : A.block.card = k := by
  rw [block, card_insert_of_notMem A.not_mem_tail]
  rw [(mem_powersetCard.mp A.2).2]
  omega

theorem card_type (ha : a ∈ s) :
    Fintype.card (BlockTail s a k) = (s.card - 1).choose (k - 1) := by
  change Fintype.card ↥((s.erase a).powersetCard (k - 1)) = _
  rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_erase_of_mem ha]

end EqualFinpartition.BlockTail

namespace EqualFinpartition

variable {s : Finset α} {m k : ℕ}

/-- Equal partitions over equal carrier finsets are heterogeneously equal when their unordered
part collections agree. -/
theorem heq_of_parts_eq {t : Finset α} (P : EqualFinpartition s m k)
    (Q : EqualFinpartition t m k) (hst : s = t) (hparts : P.1.parts = Q.1.parts) : P ≍ Q := by
  subst t
  cases Subtype.ext (Finpartition.ext hparts)
  rfl

/-- A fixed distinguished element of a nonempty finite set. -/
def pivot (hs : s.Nonempty) : α := Classical.choose hs

omit [DecidableEq α] in
theorem pivot_mem (hs : s.Nonempty) : pivot hs ∈ s := Classical.choose_spec hs

/-- The tail of the unique part containing a fixed distinguished element of `s`. -/
def head (hs : s.Nonempty) (P : EqualFinpartition s (m + 1) k) :
    BlockTail s (pivot hs) k :=
  BlockTail.ofFinset (P.1.part_subset (pivot hs))
    (P.1.mem_part (pivot_mem hs))
    (P.2.2 _ (P.1.part_mem.mpr (pivot_mem hs)))

@[simp]
theorem head_block (hs : s.Nonempty) (P : EqualFinpartition s (m + 1) k) :
    (head hs P).block = P.1.part (pivot hs) := by
  simp [head]

/-- Delete the distinguished part from an equal-sized partition. -/
def rest (hs : s.Nonempty) (P : EqualFinpartition s (m + 1) k) :
    EqualFinpartition (s \ (head hs P).block) m k := by
  have hpart : P.1.part (pivot hs) ∈ P.1.parts :=
    P.1.part_mem.mpr (pivot_mem hs)
  have hhead : (head hs P).block ∈ P.1.parts := by
    simpa using hpart
  refine ⟨P.1.avoid (head hs P).block, ?_, ?_⟩
  · rw [parts_avoid_of_mem_parts P.1 hhead, card_erase_of_mem hhead, P.2.1]
    omega
  · intro t ht
    apply P.2.2 t
    rw [parts_avoid_of_mem_parts P.1 hhead] at ht
    exact mem_of_mem_erase ht

/-- Add the selected distinguished block back to a partition of its complement. -/
def prepend (hs : s.Nonempty) (hk : 0 < k) (A : BlockTail s (pivot hs) k)
    (Q : EqualFinpartition (s \ A.block) m k) : EqualFinpartition s (m + 1) k := by
  have hsubset : A.block ⊆ s := A.block_subset (pivot_mem hs)
  have hne : A.block ≠ ∅ := fun h ↦ by simpa [h] using A.mem_block
  have hdisjoint : Disjoint (s \ A.block) A.block := Finset.sdiff_disjoint
  have hunion : (s \ A.block) ∪ A.block = s := Finset.sdiff_union_of_subset hsubset
  let P := Q.1.extend hne hdisjoint hunion
  refine ⟨P, ?_, ?_⟩
  · simpa [P, Q.2.1] using
      (Finpartition.card_extend Q.1 A.block s (hb := hne) (hab := hdisjoint) (hc := hunion))
  · intro t ht
    change t ∈ insert A.block Q.1.parts at ht
    rcases mem_insert.mp ht with rfl | ht
    · exact A.card_block hk
    · exact Q.2.2 t ht

@[simp]
theorem head_prepend (hs : s.Nonempty) (hk : 0 < k) (A : BlockTail s (pivot hs) k)
    (Q : EqualFinpartition (s \ A.block) m k) : head hs (prepend hs hk A Q) = A := by
  apply Subtype.ext
  have hpart : (prepend hs hk A Q).1.part (pivot hs) = A.block := by
    apply (prepend hs hk A Q).1.part_eq_of_mem
    · change A.block ∈ insert A.block Q.1.parts
      exact mem_insert_self _ _
    · exact A.mem_block
  have hblock := head_block hs (prepend hs hk A Q)
  have herase := congr_arg (fun B : Finset α ↦ B.erase (pivot hs)) (hblock.trans hpart)
  simpa [BlockTail.block, BlockTail.not_mem_tail] using herase

@[simp]
theorem prepend_head_rest (hs : s.Nonempty) (hk : 0 < k)
    (P : EqualFinpartition s (m + 1) k) : prepend hs hk (head hs P) (rest hs P) = P := by
  apply Subtype.ext
  apply Finpartition.ext
  have hpart : P.1.part (pivot hs) ∈ P.1.parts := P.1.part_mem.mpr (pivot_mem hs)
  have hhead : (head hs P).block ∈ P.1.parts := by simpa using hpart
  change insert (head hs P).block (P.1.avoid (head hs P).block).parts = P.1.parts
  rw [parts_avoid_of_mem_parts P.1 hhead, insert_erase hhead]

/-- Choosing the distinguished part is an equivalence between equal partitions into `m + 1`
blocks and a block tail together with an equal partition of its complement. -/
def succEquiv (hs : s.Nonempty) (hk : 0 < k) :
    EqualFinpartition s (m + 1) k ≃
      Σ A : BlockTail s (pivot hs) k, EqualFinpartition (s \ A.block) m k where
  toFun P := ⟨head hs P, rest hs P⟩
  invFun X := prepend hs hk X.1 X.2
  left_inv P := prepend_head_rest hs hk P
  right_inv := by
    rintro ⟨A, Q⟩
    have hhead : head hs (prepend hs hk A Q) = A := head_prepend hs hk A Q
    apply Sigma.ext hhead
    apply heq_of_parts_eq
    · exact congr_arg (fun B : BlockTail s (pivot hs) k ↦ s \ B.block) hhead
    · change ((prepend hs hk A Q).1.avoid (head hs (prepend hs hk A Q)).block).parts =
        Q.1.parts
      rw [congr_arg BlockTail.block hhead]
      have hadded : A.block ∈ (prepend hs hk A Q).1.parts := by
        change A.block ∈ insert A.block Q.1.parts
        exact mem_insert_self _ _
      have hnot : A.block ∉ Q.1.parts := by
        intro hmem
        have hpivot := Q.1.subset hmem A.mem_block
        exact (mem_sdiff.mp hpivot).2 A.mem_block
      rw [parts_avoid_of_mem_parts _ hadded]
      change (insert A.block Q.1.parts).erase A.block = Q.1.parts
      simp [hnot]

/-- The number of unordered partitions of an `m * k`-element finset into `m` parts of size
`k`. This is the recursive counting engine behind Lemma 2.3.1. -/
theorem card_equalFinpartition (m k : ℕ) (hk : 0 < k) {s : Finset α}
    (hcard : s.card = m * k) :
    Fintype.card (EqualFinpartition s m k) = equalFinpartitionCount m k := by
  induction m generalizing s with
  | zero =>
      have hs : s = ∅ := card_eq_zero.mp (by simpa using hcard)
      subst s
      rw [equalFinpartitionCount_zero]
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨Finpartition.empty (Finset α), by simp⟩, ?_⟩
      intro P
      apply Subtype.ext
      apply Finpartition.ext
      exact (Finpartition.parts_eq_empty_iff (P := P.1)).2 rfl
  | succ m ih =>
      have hs : s.Nonempty := card_pos.mp (by
        rw [hcard]
        exact Nat.mul_pos (Nat.succ_pos _) hk)
      have hrest (A : BlockTail s (pivot hs) k) : (s \ A.block).card = m * k := by
        rw [card_sdiff_of_subset (A.block_subset (pivot_mem hs)), A.card_block hk, hcard]
        simp [Nat.add_mul]
      calc
        Fintype.card (EqualFinpartition s (m + 1) k) =
            Fintype.card (Σ A : BlockTail s (pivot hs) k,
              EqualFinpartition (s \ A.block) m k) :=
          Fintype.card_congr (succEquiv hs hk)
        _ = ∑ A : BlockTail s (pivot hs) k,
              Fintype.card (EqualFinpartition (s \ A.block) m k) :=
          Fintype.card_sigma
        _ = ∑ _A : BlockTail s (pivot hs) k, equalFinpartitionCount m k := by
          apply sum_congr rfl
          intro A _
          exact ih (hrest A)
        _ = Fintype.card (BlockTail s (pivot hs) k) * equalFinpartitionCount m k := by
          simp
        _ = (((m + 1) * k - 1).choose (k - 1)) * equalFinpartitionCount m k := by
          rw [BlockTail.card_type (pivot_mem hs), hcard]
        _ = equalFinpartitionCount (m + 1) k := (equalFinpartitionCount_succ m k).symm

/-- **Lemma 2.3.1 (Bowling, 2023).** The number of partitions of a `4k`-element
set into four unordered `k`-element subsets. -/
theorem lemma_2_3_1 (k : ℕ) (hk : 0 < k) {s : Finset α} (hcard : s.card = 4 * k) :
    Fintype.card (EqualFinpartition s 4 k) =
      ((4 * k - 1).choose (k - 1)) * ((3 * k - 1).choose (k - 1)) *
        ((2 * k - 1).choose (k - 1)) := by
  rw [card_equalFinpartition 4 k hk hcard]
  simp [equalFinpartitionCount, prod_range_succ, mul_comm, mul_assoc]

end EqualFinpartition

end

end ZonalGraphs
