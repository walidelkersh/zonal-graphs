import ZonalGraphs.ThreeConnected

namespace ZonalGraphs

/-!
# Telling embeddings apart by their region sizes

`Iso.card_filter_boundary_card` says an isomorphism of plane graphs preserves, for each `n`, the number
of regions whose boundary has `n` vertices. That is already the invariant needed to separate embeddings;
what was missing is the contrapositive in usable form, and the arithmetic that applies it to `Gn,k`.

Theorems 2.5.5 and 2.5.8 assert the embeddings `Gn,k` are pairwise distinct. Observation 2.5.4 supplies
the profile: for `k >= 1`, the embedding `Gn,k` has one region of boundary length `8k`, one of length
`8(n-k)`, and every other region of length `3`, `4` or `5`. A size present in one profile and absent from
another separates the two embeddings, and the restriction `2k <= n` in the source is exactly what stops
`8k` and `8(n-k)` from coinciding across different `k`.
-/

universe u₁ u₂ v₁ v₂

namespace PlaneGraph

variable {V₁ : Type u₁} {V₂ : Type u₂} {F₁ : Type v₁} {F₂ : Type v₂}
  [Fintype V₁] [Fintype V₂] [Fintype F₁] [Fintype F₂]

/-- **Embeddings disagreeing on some region-size count are distinct.** The contrapositive of
`Iso.card_filter_boundary_card`. -/
theorem not_nonempty_iso_of_card_filter_ne {P : PlaneGraph V₁ F₁} {Q : PlaneGraph V₂ F₂} (n : ℕ)
    (h : {R ∈ (Finset.univ : Finset F₁) | (P.boundary R).card = n}.card
      ≠ {S ∈ (Finset.univ : Finset F₂) | (Q.boundary S).card = n}.card) : ¬ Nonempty (P.Iso Q) := by
  rintro ⟨e⟩
  exact h (e.card_filter_boundary_card n)

/-- A region size that no region of `Q` attains is counted zero times. -/
theorem card_filter_boundary_card_eq_zero {Q : PlaneGraph V₂ F₂} {n : ℕ}
    (h : ∀ S : F₂, (Q.boundary S).card ≠ n) :
    {S ∈ (Finset.univ : Finset F₂) | (Q.boundary S).card = n}.card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun {S} _ => h S

/-- **A size present in one embedding and absent from the other separates them.** -/
theorem not_nonempty_iso_of_size_present_absent {P : PlaneGraph V₁ F₁} {Q : PlaneGraph V₂ F₂} {n : ℕ}
    (hP : ∃ R : F₁, (P.boundary R).card = n) (hQ : ∀ S : F₂, (Q.boundary S).card ≠ n) :
    ¬ Nonempty (P.Iso Q) := by
  refine not_nonempty_iso_of_card_filter_ne n ?_
  obtain ⟨R, hR⟩ := hP
  rw [card_filter_boundary_card_eq_zero hQ]
  have hne : {R ∈ (Finset.univ : Finset F₁) | (P.boundary R).card = n}.Nonempty :=
    ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_univ R, hR⟩⟩
  exact Finset.card_ne_zero_of_mem hne.choose_spec

/-- **Theorems 2.5.5 and 2.5.8 (Bowling, 2023).** The embeddings `Gn,k` are pairwise distinct.

The region-size profile of Observation 2.5.4 is carried as the hypothesis `hQ`: every region of the second
embedding has boundary length `3`, `4`, `5`, `8 * k₂` or `8 * (n - k₂)`. The first embedding has a region
of length `8 * k₁`, and that size appears nowhere in the profile. It exceeds `5` because `k₁ >= 1`; it is
not `8 * k₂` because `k₁ < k₂`; and it is not `8 * (n - k₂)` because `2 * k₂ <= n` forces `n - k₂ >= k₂`,
which is already larger than `k₁`.

That last step is where the source's restriction to `k <= n / 2` does its work: without it, `Gn,k` and
`Gn,(n-k)` share the pair of long region sizes and the invariant cannot separate them. -/
theorem not_nonempty_iso_of_gn_profile {P : PlaneGraph V₁ F₁} {Q : PlaneGraph V₂ F₂} {n k₁ k₂ : ℕ}
    (hk₁ : 1 ≤ k₁) (hlt : k₁ < k₂) (hhalf : 2 * k₂ ≤ n)
    (hP : ∃ R : F₁, (P.boundary R).card = 8 * k₁)
    (hQ : ∀ S : F₂, (Q.boundary S).card = 3 ∨ (Q.boundary S).card = 4 ∨ (Q.boundary S).card = 5
      ∨ (Q.boundary S).card = 8 * k₂ ∨ (Q.boundary S).card = 8 * (n - k₂)) :
    ¬ Nonempty (P.Iso Q) := by
  refine not_nonempty_iso_of_size_present_absent hP fun S => ?_
  rcases hQ S with h | h | h | h | h <;> rw [h] <;> omega

end PlaneGraph

end ZonalGraphs
