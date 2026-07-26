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

end ZonalGraphs
