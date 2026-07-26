import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Three nonzero elements summing to zero

Lemma 2.3 of Bowling (2025): an abelian group not isomorphic to `ZMod 2` contains three nonzero elements,
not necessarily distinct, summing to zero.

The hypothesis is stated here as the existence of two distinct nonzero elements, which for an abelian
group is the same as having more than two elements, hence the same as being neither trivial nor `ZMod 2`.
Phrasing it that way avoids carrying an isomorphism around.

The proof splits on whether the chosen element has order two. If `g + g ≠ 0` then `g, g, -(g + g)` works.
Otherwise `-g = g`, so a second nonzero element `h` distinct from `g` cannot be `-g`, and `g + h ≠ 0`
gives `g, h, -(g + h)`.  Note the group is not assumed finite.
-/

/-- **Lemma 2.3 (Bowling, 2025).** An abelian group with two distinct nonzero elements contains three
nonzero elements, not necessarily distinct, whose sum is zero. -/
theorem exists_three_nonzero_add_eq_zero {Γ : Type*} [AddCommGroup Γ] {g h : Γ} (hg : g ≠ 0)
    (hh : h ≠ 0) (hne : g ≠ h) :
    ∃ a b c : Γ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a + b + c = 0 := by
  by_cases hgg : g + g = 0
  · -- `g` has order two, so `-g = g` and therefore `h ≠ -g`, giving `g + h ≠ 0`.
    refine ⟨g, h, -(g + h), hg, hh, ?_, by abel⟩
    rw [neg_ne_zero]
    intro hzero
    have hhg : h = -g := eq_neg_of_add_eq_zero_right hzero
    rw [neg_eq_of_add_eq_zero_left hgg] at hhg
    exact hne hhg.symm
  · exact ⟨g, g, -(g + g), hg, hg, by rwa [neg_ne_zero], by abel⟩

/-- A set of even size admits a labeling by nonzero group elements summing to zero: split it in half,
give one half `g` and the other `-g`.

With `exists_three_nonzero_add_eq_zero` this covers the odd case too, one triple absorbing the parity and
pairs handling the rest, which is what the cycle results over abelian groups need. -/
theorem exists_labeling_sum_eq_zero_of_even_card {Γ : Type*} [AddCommGroup Γ] {g : Γ} (hg : g ≠ 0)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : Even s.card) :
    ∃ f : ι → Γ, (∀ i, f i ≠ 0) ∧ ∑ i ∈ s, f i = 0 := by
  obtain ⟨k, hk⟩ := hs
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (s := s) (n := k) (by omega)
  have hsdiff : (s \ t).card = k := by
    have hadd := Finset.card_sdiff_add_card_eq_card hts
    omega
  refine ⟨fun i => if i ∈ t then g else -g, fun i => ?_, ?_⟩
  · by_cases hi : i ∈ t <;> simp [hi, hg]
  · rw [← Finset.sum_sdiff hts]
    have hone : ∀ i ∈ t, (if i ∈ t then g else -g) = g := fun i hi => by simp [hi]
    have htwo : ∀ i ∈ s \ t, (if i ∈ t then g else -g) = -g := fun i hi => by
      simp [(Finset.mem_sdiff.mp hi).2]
    rw [Finset.sum_congr rfl hone, Finset.sum_congr rfl htwo, Finset.sum_const,
      Finset.sum_const, htcard, hsdiff, ← smul_add, neg_add_cancel, smul_zero]

/-- **Any set of at least two elements admits a nonzero labeling summing to zero, provided the group has
two distinct nonzero elements.**

Even sizes pair off. Odd sizes are at least three, so three elements carry a triple summing to zero and
the rest, now of even size, pair off. This is the labeling side of the cycle results over abelian groups:
a cycle plane graph has both of its regions bounded by every vertex, so being `Γ`-zonal is exactly the
existence of such a labeling. The excluded case `Γ ≃ ZMod 2` with odd order is where the hypothesis on `Γ`
fails, its only nonzero element forcing an odd sum. -/
theorem exists_labeling_sum_eq_zero {Γ : Type*} [AddCommGroup Γ] {g h : Γ} (hg : g ≠ 0) (hh : h ≠ 0)
    (hne : g ≠ h) {ι : Type*} [DecidableEq ι] (s : Finset ι) (hcard : 2 ≤ s.card) :
    ∃ f : ι → Γ, (∀ i, f i ≠ 0) ∧ ∑ i ∈ s, f i = 0 := by
  rcases Nat.even_or_odd s.card with heven | hodd
  · exact exists_labeling_sum_eq_zero_of_even_card hg s heven
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ := exists_three_nonzero_add_eq_zero hg hh hne
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (s := s) (n := 3) (by omega)
  obtain ⟨x, y, z, hxy, hxz, hyz, hteq⟩ := Finset.card_eq_three.mp htcard
  have hadd := Finset.card_sdiff_add_card_eq_card hts
  obtain ⟨f₀, hf₀ne, hf₀sum⟩ :=
    exists_labeling_sum_eq_zero_of_even_card hg (s \ t) ⟨m - 1, by omega⟩
  classical
  set F : ι → Γ := fun i => if i = x then a else if i = y then b else if i = z then c else f₀ i
    with hF
  have hFx : F x = a := by simp [hF]
  have hFy : F y = b := by simp [hF, Ne.symm hxy]
  have hFz : F z = c := by simp [hF, Ne.symm hxz, Ne.symm hyz]
  have hFout : ∀ i ∈ s \ t, F i = f₀ i := by
    intro i hi
    have hnotin : i ∉ t := (Finset.mem_sdiff.mp hi).2
    rw [hteq] at hnotin
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotin
    simp [hF, hnotin.1, hnotin.2.1, hnotin.2.2]
  refine ⟨F, fun i => ?_, ?_⟩
  · simp only [hF]
    split_ifs <;> first | exact ha | exact hb | exact hc | exact hf₀ne i
  · rw [← Finset.sum_sdiff hts, Finset.sum_congr rfl hFout, hf₀sum, hteq,
      Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
      Finset.sum_singleton, hFx, hFy, hFz, zero_add,
      show a + (b + c) = a + b + c from by abel]
    exact habc

end ZonalGraphs
