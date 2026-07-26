import ZonalGraphs.StandardWindmill
import ZonalGraphs.ThreeConnected

namespace ZonalGraphs

/-!
# Nested embeddings of a Dutch windmill

The published proof of Theorem 2.2.2 splits into three constructions: the standard embedding, a
fully nested chain when the number of blades is odd, and a hybrid of four side-by-side blades with a
chain when it is even.  All three are instances of one family, which is what this module builds.

Fix a blade `outer` and a set `N` of blades not containing it, and draw the blades of `N` inside
`outer`'s cycle, side by side, all still meeting at the hub.  The regions are then: the disk bounded
by each blade other than `outer`, the part of `outer`'s disk lying outside the nested blades, and the
exterior region bounded by `outer` together with the blades that were not nested.

Give the hub the label `1` and every blade but `outer` the petal sum `2`, letting `outer` absorb a
correction.  The disk of a blade `b ≠ outer` then has value `1 + 2 = 0` automatically, and the two
remaining regions pin down the correction and force a single congruence: writing `m = |N|` and `k` for
the number of blades, the embedding is zonal exactly when `m = 2k + 1` in `ZMod 3`.

Since `m` ranges over `0, 1, 2` for `k ≥ 3`, one of those values satisfies the congruence and another
does not.  So a Dutch windmill with at least three blades has both a zonal and a non-zonal embedding
in this single family — Theorem 2.2.2 — with no case split on the parity of `k`.  Taking `N = ∅`
recovers the standard embedding of `ZonalGraphs.StandardWindmill`.
-/

universe w

namespace PlaneGraph

variable {Blade : Type w} [Fintype Blade] [DecidableEq Blade]

/-- The regions of the embedding nesting the blades of `N` inside the blade `outer`.

`inl outer` is the part of `outer`'s disk outside the nested blades, `inl b` for `b ≠ outer` is the
disk bounded by blade `b`, and `inr ()` is the exterior region. -/
def nestedRegionPetals (outer : Blade) (N : Finset Blade) : Blade ⊕ Unit → Finset Blade
  | .inl b => if b = outer then insert outer N else {b}
  | .inr _ => Finset.univ \ N

@[simp] theorem nestedRegionPetals_inl_self (outer : Blade) (N : Finset Blade) :
    nestedRegionPetals outer N (.inl outer) = insert outer N := by
  simp [nestedRegionPetals]

@[simp] theorem nestedRegionPetals_inl_of_ne (outer : Blade) (N : Finset Blade) {b : Blade}
    (hb : b ≠ outer) : nestedRegionPetals outer N (.inl b) = {b} := by
  simp [nestedRegionPetals, hb]

@[simp] theorem nestedRegionPetals_inr (outer : Blade) (N : Finset Blade) (u : Unit) :
    nestedRegionPetals outer N (.inr u) = Finset.univ \ N := rfl

/-- The plane embedding of the Dutch windmill nesting the blades of `N` inside the blade `outer`. -/
def nestedWindmill (len : Blade → ℕ) (outer : Blade) (N : Finset Blade)
    (faceEdges : Blade ⊕ Unit → Finset (Sym2 (WindmillVertex len))) :
    PlaneGraph (WindmillVertex len) (Blade ⊕ Unit) :=
  { graph := windmillGraph len
    connected := windmillGraph_connected len
    boundary := fun R =>
      insert none ((nestedRegionPetals outer N R).biUnion (windmillPetal len))
    boundaryEdges := faceEdges
    exterior := .inr () }

variable (len : Blade → ℕ) (outer : Blade) (N : Finset Blade)
  (faceEdges : Blade ⊕ Unit → Finset (Sym2 (WindmillVertex len)))

/-- A nested embedding carries the face data of a Dutch windmill. -/
theorem isWindmillEmbedding_nestedWindmill :
    (nestedWindmill len outer N faceEdges).IsWindmillEmbedding none (windmillPetal len)
      (nestedRegionPetals outer N) where
  hub_notMem_petal := hub_notMem_windmillPetal len
  petal_disjoint := windmillPetal_disjoint len
  boundary_eq := fun _ => rfl

/-- The petal sums witnessing zonality: every blade except `outer` is given the sum `2`, while
`outer` absorbs the correction `-1 - 2|N|`. -/
def nestedTarget (outer : Blade) (N : Finset Blade) : Blade → ZMod 3 :=
  Function.update (fun _ => 2) outer (-1 - 2 * (N.card : ZMod 3))

/-- **Zonality of a nested Dutch windmill embedding.** Nesting `m = |N|` blades inside `outer`
gives a zonal embedding as soon as `m = 2k + 1` in `ZMod 3`, where `k` is the number of blades. -/
theorem isZonal_nestedWindmill (hlen : ∀ b, 2 ≤ len b) (houter : outer ∉ N)
    (hm : (N.card : ZMod 3) = 2 * (Fintype.card Blade : ZMod 3) + 1) :
    (nestedWindmill len outer N faceEdges).IsZonal := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  have houterMem : outer ∈ Finset.univ \ N := by simp [houter]
  refine (isWindmillEmbedding_nestedWindmill len outer N faceEdges).isZonal_of_forall_sum_eq_zero
    (fun b => by rw [card_windmillPetal]; exact hlen b) (nestedTarget outer N) ?_
  intro R
  cases R with
  | inl b =>
    by_cases hb : b = outer
    · rw [hb, nestedRegionPetals_inl_self, nestedTarget,
        Finset.sum_update_of_mem (Finset.mem_insert_self outer N),
        Finset.sdiff_singleton_eq_erase, Finset.erase_insert houter, Finset.sum_const,
        nsmul_eq_mul]
      ring
    · rw [nestedRegionPetals_inl_of_ne outer N hb, Finset.sum_singleton, nestedTarget,
        Function.update_of_ne hb]
      decide
  | inr u =>
    -- Card bookkeeping by addition, avoiding truncated natural subtraction.
    have hsum : (Finset.univ \ N).card + N.card = Fintype.card Blade := by
      rw [← Finset.card_univ]
      exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ N)
    have herase : ((Finset.univ \ N).erase outer).card + 1 = (Finset.univ \ N).card :=
      Finset.card_erase_add_one houterMem
    have hcast : (((Finset.univ \ N).erase outer).card : ZMod 3) + 1 + (N.card : ZMod 3)
        = (Fintype.card Blade : ZMod 3) := by
      have hnat : ((Finset.univ \ N).erase outer).card + 1 + N.card = Fintype.card Blade := by
        omega
      exact_mod_cast congrArg (fun n : ℕ => (n : ZMod 3)) hnat
    rw [nestedRegionPetals_inr outer N u, nestedTarget, Finset.sum_update_of_mem houterMem,
      Finset.sdiff_singleton_eq_erase, Finset.sum_const, nsmul_eq_mul]
    linear_combination 2 * hcast - 4 * hm + (-2 * (Fintype.card Blade : ZMod 3) - 2) * h3

/-- **Converse: a zonal nested embedding forces the congruence.**

The disk of each blade other than `outer` forces that blade's petal sum to be `-ℓ(hub)`.  The two
remaining regions then read `ℓ(hub) + q(outer) - m·ℓ(hub) = 0` and
`ℓ(hub) + q(outer) - e·ℓ(hub) = 0`, where `e = k - m - 1` counts the blades left outside besides
`outer`.  Subtracting eliminates the unknown `q(outer)`, and since `ZMod 3` is a field with
`ℓ(hub) ≠ 0` we get `e = m`, hence `2m + 1 = k` and so `m = 2k + 1`. -/
theorem card_eq_of_isZonal_nestedWindmill (houter : outer ∉ N)
    (hzonal : (nestedWindmill len outer N faceEdges).IsZonal) :
    (N.card : ZMod 3) = 2 * (Fintype.card Blade : ZMod 3) + 1 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hemb := isWindmillEmbedding_nestedWindmill len outer N faceEdges
  obtain ⟨labeling, hlabeling⟩ := hzonal
  have hval : ∀ R, (nestedWindmill len outer N faceEdges).zoneValue labeling R = 0 := hlabeling
  have houterMem : outer ∈ Finset.univ \ N := by simp [houter]
  -- Each blade other than `outer` bounds a disk of its own, fixing its petal sum.
  have hsingle : ∀ b, b ≠ outer →
      (∑ v ∈ windmillPetal len b, (labeling v : ZMod 3)) = -(labeling none : ZMod 3) := by
    intro b hb
    have hstep := hemb.zoneValue_eq labeling (.inl b)
    rw [hval, nestedRegionPetals_inl_of_ne outer N hb, Finset.sum_singleton] at hstep
    linear_combination -hstep
  -- The part of `outer`'s disk outside the nested blades.
  have hinner : (labeling none : ZMod 3) + (∑ v ∈ windmillPetal len outer, (labeling v : ZMod 3))
      + (N.card : ZMod 3) * (-(labeling none : ZMod 3)) = 0 := by
    have hstep := hemb.zoneValue_eq labeling (.inl outer)
    rw [hval, nestedRegionPetals_inl_self, Finset.sum_insert houter,
      Finset.sum_congr rfl (fun b hb => hsingle b fun hbo => houter (hbo ▸ hb)),
      Finset.sum_const, nsmul_eq_mul] at hstep
    linear_combination -hstep
  -- The exterior region.
  have hext : (labeling none : ZMod 3) + (∑ v ∈ windmillPetal len outer, (labeling v : ZMod 3))
      + (((Finset.univ \ N).erase outer).card : ZMod 3) * (-(labeling none : ZMod 3)) = 0 := by
    have hstep := hemb.zoneValue_eq labeling (.inr ())
    rw [hval, nestedRegionPetals_inr,
      ← Finset.add_sum_erase _ (fun b => ∑ v ∈ windmillPetal len b, (labeling v : ZMod 3))
        houterMem,
      Finset.sum_congr rfl (fun b hb => hsingle b (Finset.ne_of_mem_erase hb)),
      Finset.sum_const, nsmul_eq_mul] at hstep
    linear_combination -hstep
  -- Eliminate the outer petal sum and cancel the nonzero hub label.
  have hmul : ((((Finset.univ \ N).erase outer).card : ZMod 3) - (N.card : ZMod 3))
      * (labeling none : ZMod 3) = 0 := by linear_combination hinner - hext
  have hem : (((Finset.univ \ N).erase outer).card : ZMod 3) = (N.card : ZMod 3) := by
    rcases mul_eq_zero.mp hmul with hzero | hzero
    · linear_combination hzero
    · exact absurd hzero (labeling none).2
  -- Card bookkeeping by addition, as in the forward direction.
  have hsum : (Finset.univ \ N).card + N.card = Fintype.card Blade := by
    rw [← Finset.card_univ]
    exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ N)
  have herase : ((Finset.univ \ N).erase outer).card + 1 = (Finset.univ \ N).card :=
    Finset.card_erase_add_one houterMem
  have hcast : (((Finset.univ \ N).erase outer).card : ZMod 3) + 1 + (N.card : ZMod 3)
      = (Fintype.card Blade : ZMod 3) := by
    have hnat : ((Finset.univ \ N).erase outer).card + 1 + N.card = Fintype.card Blade := by omega
    exact_mod_cast congrArg (fun n : ℕ => (n : ZMod 3)) hnat
  linear_combination -2 * hem + 2 * hcast + (-(N.card : ZMod 3) - 1) * h3

/-- **The nested Dutch windmill embedding is zonal exactly when `m = 2k + 1` in `ZMod 3`.** -/
theorem isZonal_nestedWindmill_iff (hlen : ∀ b, 2 ≤ len b) (houter : outer ∉ N) :
    (nestedWindmill len outer N faceEdges).IsZonal ↔
      (N.card : ZMod 3) = 2 * (Fintype.card Blade : ZMod 3) + 1 :=
  ⟨card_eq_of_isZonal_nestedWindmill len outer N faceEdges houter,
    isZonal_nestedWindmill len outer N faceEdges hlen houter⟩

/-- The boundary of a region of a nested embedding consists of the hub together with the petals
bounding it, so its size is `1` plus the total length of those blades.

Combined with `Iso.card_boundary` this is what separates nested embeddings with different nesting
sets, and hence counts distinct embeddings. -/
theorem card_boundary_nestedWindmill (R : Blade ⊕ Unit) :
    ((nestedWindmill len outer N faceEdges).boundary R).card
      = (∑ b ∈ nestedRegionPetals outer N R, len b) + 1 := by
  show (insert none ((nestedRegionPetals outer N R).biUnion (windmillPetal len))).card = _
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_biUnion
    (fun b _ c _ hbc => windmillPetal_disjoint len b c hbc)]
  simp [card_windmillPetal]

/-- The region inside `outer` has boundary size `len outer + Σ_{b ∈ N} len b + 1`.

This is the region whose size varies with the nesting set, so it is the one that distinguishes
nested embeddings from one another. -/
theorem card_boundary_inl_self (houter : outer ∉ N) :
    ((nestedWindmill len outer N faceEdges).boundary (.inl outer)).card
      = len outer + (∑ b ∈ N, len b) + 1 := by
  rw [card_boundary_nestedWindmill, nestedRegionPetals_inl_self, Finset.sum_insert houter]

/-- The exterior region has boundary size `Σ_{b ∉ N} len b + 1`. -/
theorem card_boundary_inr (u : Unit) :
    ((nestedWindmill len outer N faceEdges).boundary (.inr u)).card
      = (∑ b ∈ Finset.univ \ N, len b) + 1 := by
  rw [card_boundary_nestedWindmill, nestedRegionPetals_inr]

/-- The disk bounded by a blade other than `outer` has boundary size `len b + 1`, independently of
the nesting set. -/
theorem card_boundary_inl_of_ne {b : Blade} (hb : b ≠ outer) :
    ((nestedWindmill len outer N faceEdges).boundary (.inl b)).card = len b + 1 := by
  rw [card_boundary_nestedWindmill, nestedRegionPetals_inl_of_ne outer N hb, Finset.sum_singleton]

/-- Blades other than `outer` are plentiful enough to nest any of `0`, `1` or `2` of them, once
there are at least three blades in all. -/
theorem exists_nested_card_eq (hk : 3 ≤ Fintype.card Blade) (outer : Blade) {m : ℕ} (hm : m ≤ 2) :
    ∃ N : Finset Blade, outer ∉ N ∧ N.card = m := by
  have hcard : (Finset.univ.erase outer).card = Fintype.card Blade - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ outer), Finset.card_univ]
  obtain ⟨N, hsubset, hNcard⟩ :=
    Finset.exists_subset_card_eq (s := Finset.univ.erase outer) (n := m) (by omega)
  exact ⟨N, fun hmem => Finset.ne_of_mem_erase (hsubset hmem) rfl, hNcard⟩

/-- **Theorem 2.2.2 (Bowling–Zhang, 2022).** For every multiset `S` of three or more cycles the
Dutch windmill graph `D(S)` is conditionally zonal: it has both a zonal and a non-zonal planar
embedding.

Both witnesses come from the single nested family.  Nesting `m` blades inside a fixed blade is zonal
exactly when `m = 2k + 1` in `ZMod 3`, and with at least three blades each of `m = 0, 1, 2` is
available.  Those three values are distinct in `ZMod 3`, so exactly one of them meets the congruence
and the other two fail it.  This replaces the published case split on the parity of `k`. -/
theorem conditionallyZonal_windmill (hk : 3 ≤ Fintype.card Blade) (hlen : ∀ b, 2 ≤ len b)
    (outer : Blade) :
    (∃ N : Finset Blade, outer ∉ N ∧ (nestedWindmill len outer N faceEdges).IsZonal) ∧
      ∃ N : Finset Blade, outer ∉ N ∧ ¬(nestedWindmill len outer N faceEdges).IsZonal := by
  obtain ⟨N₁, hout₁, hcard₁⟩ := exists_nested_card_eq hk outer
    (m := (2 * (Fintype.card Blade : ZMod 3) + 1).val)
    (by have := ZMod.val_lt (2 * (Fintype.card Blade : ZMod 3) + 1); omega)
  obtain ⟨N₂, hout₂, hcard₂⟩ := exists_nested_card_eq hk outer
    (m := (2 * (Fintype.card Blade : ZMod 3) + 2).val)
    (by have := ZMod.val_lt (2 * (Fintype.card Blade : ZMod 3) + 2); omega)
  refine ⟨⟨N₁, hout₁, ?_⟩, ⟨N₂, hout₂, ?_⟩⟩
  · refine (isZonal_nestedWindmill_iff len outer N₁ faceEdges hlen hout₁).mpr ?_
    rw [hcard₁, ZMod.natCast_zmod_val]
  · rw [isZonal_nestedWindmill_iff len outer N₂ faceEdges hlen hout₂, hcard₂,
      ZMod.natCast_zmod_val]
    intro hcontra
    have hone : (1 : ZMod 3) = 0 := by linear_combination hcontra
    exact absurd hone (by decide)

/-- Blade lengths given by distinct powers of two make the total length over a nesting set determine
that set.

This is what makes a Dutch windmill *irregular* in the sense of Theorem 2.3.2, and it is why distinct
nesting sets give regions of distinct boundary size. -/
theorem sum_two_pow_val_injective {k : ℕ} :
    Function.Injective fun N : Finset (Fin k) => ∑ b ∈ N, 2 ^ (b : ℕ) := by
  intro N₁ N₂ hsum
  have himage : N₁.image Fin.val = N₂.image Fin.val := by
    refine Finset.geomSum_injective (n := 2) le_rfl ?_
    simpa [Finset.sum_image, Fin.val_injective.injOn] using hsum
  exact Finset.image_injective Fin.val_injective himage

/-- Blade lengths `2 ^ i + 1` also determine a nesting set from its total length, provided the size
of the set is known: the two totals differ from the power-of-two totals by exactly the size.

These lengths are preferable to bare powers of two for Theorem 2.3.2, because they are odd, which lets
the unwanted case in the separating argument be excluded by parity rather than by a bound on the sum
of the largest blades. -/
theorem sum_two_pow_succ_inj_of_card_eq {k : ℕ} {N₁ N₂ : Finset (Fin k)}
    (hcard : N₁.card = N₂.card)
    (hsum : ∑ b ∈ N₁, (2 ^ (b : ℕ) + 1) = ∑ b ∈ N₂, (2 ^ (b : ℕ) + 1)) : N₁ = N₂ := by
  have hpow : ∑ b ∈ N₁, 2 ^ (b : ℕ) = ∑ b ∈ N₂, 2 ^ (b : ℕ) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hsum
    omega
  exact sum_two_pow_val_injective hpow

/-- A sum of odd terms has the parity of the number of terms.

This is the parity input to Theorem 2.3.2.  With every blade length odd, the total over a nesting set
has the parity of the set's size, so for two nesting sets of equal size the sum of their totals is
even, while the total over all blades but `outer` has the parity of `k - 1`.  Taking `k` even
therefore rules out the unwanted case of the separating argument with no size estimate at all. -/
theorem even_sum_iff_even_card_of_forall_odd {α : Type*} {s : Finset α} {f : α → ℕ}
    (hodd : ∀ b ∈ s, Odd (f b)) : Even (∑ b ∈ s, f b) ↔ Even s.card := by
  rw [Finset.even_sum_iff_even_card_odd f, Finset.filter_true_of_mem hodd]

/-- The blade lengths used for Theorem 2.3.2: pairwise distinct, all odd, and all at least three, so
every blade is a cycle and no two blades have the same length — an *irregular* Dutch windmill. -/
def irregularLen (k : ℕ) : Fin k → ℕ := fun b => 2 ^ ((b : ℕ) + 1) + 1

theorem irregularLen_odd (k : ℕ) (b : Fin k) : Odd (irregularLen k b) := by
  refine ⟨2 ^ (b : ℕ), ?_⟩
  simp only [irregularLen, pow_succ]
  ring

theorem two_le_irregularLen (k : ℕ) (b : Fin k) : 2 ≤ irregularLen k b := by
  have hpow : 1 ≤ 2 ^ ((b : ℕ) + 1) := Nat.one_le_two_pow
  simp only [irregularLen]
  omega

/-- **The swap case is impossible for an even number of blades.**

If two nesting sets of equal size had totals satisfying `S₁ + S₂ = Σ_{b ≠ outer} len b`, then the left
side would be even — a sum of two totals of odd terms over sets of equal size — while the right side
has the parity of `k - 1`.  For `k` even that is odd, a contradiction.

This is what lets the separating argument for Theorem 2.3.2 avoid any estimate on the largest
blades. -/
theorem not_sum_add_sum_eq_of_even {k : ℕ} (hk : Even k) (outer : Fin k)
    {N₁ N₂ : Finset (Fin k)} (hcard : N₁.card = N₂.card) :
    (∑ b ∈ N₁, irregularLen k b) + ∑ b ∈ N₂, irregularLen k b
      ≠ ∑ b ∈ Finset.univ.erase outer, irregularLen k b := by
  intro hcontra
  have hpos : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le (outer : ℕ)) outer.isLt
  have hleft : Even ((∑ b ∈ N₁, irregularLen k b) + ∑ b ∈ N₂, irregularLen k b) := by
    rw [Nat.even_add, even_sum_iff_even_card_of_forall_odd fun b _ => irregularLen_odd k b,
      even_sum_iff_even_card_of_forall_odd fun b _ => irregularLen_odd k b, hcard]
  have hcard_erase : (Finset.univ.erase outer).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ outer), Finset.card_univ, Fintype.card_fin]
  have hright : ¬Even (∑ b ∈ Finset.univ.erase outer, irregularLen k b) := by
    have hk2 : k % 2 = 0 := Nat.even_iff.mp hk
    rw [even_sum_iff_even_card_of_forall_odd fun b _ => irregularLen_odd k b, hcard_erase,
      Nat.even_sub (by omega : 1 ≤ k), Nat.even_iff, Nat.even_iff]
    omega
  exact hright (hcontra ▸ hleft)

/-- The sum of squares of the region boundary sizes of a nested embedding splits into a part fixed by
the blade lengths and the two varying terms.

The `Blade ⊕ Unit` face type sums as a sum over the blades plus the single exterior term, and the
blade summand at `outer` is the region inside `outer`, which is the first varying term. -/
theorem sum_boundary_card_sq_nestedWindmill (houter : outer ∉ N) :
    ∑ R : Blade ⊕ Unit, (((nestedWindmill len outer N faceEdges).boundary R).card) ^ 2
      = (∑ b ∈ Finset.univ.erase outer, (len b + 1) ^ 2)
        + (len outer + (∑ b ∈ N, len b) + 1) ^ 2
        + ((∑ b ∈ Finset.univ \ N, len b) + 1) ^ 2 := by
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ outer),
      card_boundary_inl_self len outer N faceEdges houter,
      Finset.sum_congr rfl fun b hb =>
        congrArg (· ^ 2) (card_boundary_inl_of_ne len outer N faceEdges
          (Finset.ne_of_mem_erase hb))]
    ring
  · simp [card_boundary_inr len outer N faceEdges]

/-- **The sum-of-squares invariant factors into exactly two cases.**

For two nested embeddings, the varying region boundary sizes are `a + x` and `y + 1`, where `x` is the
total length over the nesting set, `y` the total off it, `x + y = T` the total over all blades, and
`a = len outer + 1`.  Equality of the sums of squares expands and factors as
`(x₁ - x₂) * (x₁ + x₂ + a - T - 1) = 0`, so either the two nesting sets have the same total or their
totals sum to `T + 1 - a`, which is the total over all blades but `outer`.

The first case identifies the nesting sets, the second is the swap case excluded by parity. -/
theorem eq_or_add_eq_of_sq_add_sq_nat {L T x₁ y₁ x₂ y₂ : ℕ} (h₁ : x₁ + y₁ = T) (h₂ : x₂ + y₂ = T)
    (hsq : (L + x₁ + 1) ^ 2 + (y₁ + 1) ^ 2 = (L + x₂ + 1) ^ 2 + (y₂ + 1) ^ 2) :
    x₁ = x₂ ∨ x₁ + x₂ + L = T := by
  have h₁' : (x₁ : ℤ) + y₁ = T := by exact_mod_cast h₁
  have h₂' : (x₂ : ℤ) + y₂ = T := by exact_mod_cast h₂
  have hsq' : ((L : ℤ) + x₁ + 1) ^ 2 + ((y₁ : ℤ) + 1) ^ 2
      = ((L : ℤ) + x₂ + 1) ^ 2 + ((y₂ : ℤ) + 1) ^ 2 := by exact_mod_cast hsq
  have hy₁ : (y₁ : ℤ) = (T : ℤ) - x₁ := by linarith
  have hy₂ : (y₂ : ℤ) = (T : ℤ) - x₂ := by linarith
  rw [hy₁, hy₂] at hsq'
  have hdouble : (2 : ℤ) * (((x₁ : ℤ) - x₂) * ((x₁ : ℤ) + x₂ + L - T)) = 0 := by
    linear_combination hsq'
  have hfac : ((x₁ : ℤ) - x₂) * ((x₁ : ℤ) + x₂ + L - T) = 0 := by linarith
  rcases mul_eq_zero.mp hfac with hzero | hzero
  · left; omega
  · right; omega

theorem eq_or_add_eq_of_sq_add_sq {a T x₁ y₁ x₂ y₂ : ℤ} (h₁ : x₁ + y₁ = T) (h₂ : x₂ + y₂ = T)
    (hsq : (a + x₁) ^ 2 + (y₁ + 1) ^ 2 = (a + x₂) ^ 2 + (y₂ + 1) ^ 2) :
    x₁ = x₂ ∨ x₁ + x₂ = T + 1 - a := by
  have hy₁ : y₁ = T - x₁ := by linarith
  have hy₂ : y₂ = T - x₂ := by linarith
  subst hy₁
  subst hy₂
  have hfac2 : (2 : ℤ) * ((x₁ - x₂) * (x₁ + x₂ + a - T - 1)) = 0 := by linear_combination hsq
  have hfac : (x₁ - x₂) * (x₁ + x₂ + a - T - 1) = 0 := by linarith
  rcases mul_eq_zero.mp hfac with hzero | hzero
  · left; linarith
  · right; linarith

/-- **Distinct nesting sets give non-isomorphic embeddings.**

Take `k` even, the irregular blade lengths, and two nesting sets of equal size avoiding `outer`.  An
isomorphism would equate the sums of squares of region boundary sizes; the fixed part cancels, and the
factoring lemma leaves either equal nesting-set totals — which identifies the sets, the totals being
injective at fixed size — or the swap case, which parity forbids for even `k`.

Since the admissible nesting sets of a given size are numerous, this is Theorem 2.3.2: an irregular
Dutch windmill with arbitrarily many pairwise non-isomorphic zonal embeddings. -/
theorem nestingSet_eq_of_iso {k : ℕ} (hk : Even k) (outer : Fin k)
    {N₁ N₂ : Finset (Fin k)} (hout₁ : outer ∉ N₁) (hout₂ : outer ∉ N₂)
    (hcard : N₁.card = N₂.card)
    (faceEdges₁ faceEdges₂ : Fin k ⊕ Unit → Finset (Sym2 (WindmillVertex (irregularLen k))))
    (e : (nestedWindmill (irregularLen k) outer N₁ faceEdges₁).Iso
      (nestedWindmill (irregularLen k) outer N₂ faceEdges₂)) : N₁ = N₂ := by
  -- The two sums of squares agree, and the part fixed by the blade lengths cancels.
  have hsq := e.sum_boundary_card_sq
  rw [sum_boundary_card_sq_nestedWindmill (irregularLen k) outer N₁ faceEdges₁ hout₁,
    sum_boundary_card_sq_nestedWindmill (irregularLen k) outer N₂ faceEdges₂ hout₂] at hsq
  -- Totals of the nesting sets and of their complements.
  have htotal : ∀ N : Finset (Fin k),
      (∑ b ∈ N, irregularLen k b) + ∑ b ∈ Finset.univ \ N, irregularLen k b
        = ∑ b : Fin k, irregularLen k b := by
    intro N
    rw [add_comm, Finset.sum_sdiff (Finset.subset_univ N)]
  -- Cancel the fixed part and factor over the naturals.
  rcases eq_or_add_eq_of_sq_add_sq_nat (L := irregularLen k outer)
      (T := ∑ b : Fin k, irregularLen k b) (htotal N₁) (htotal N₂) (by omega) with hEq | hSwap
  · -- Equal totals identify the nesting sets.
    have hdouble : ∑ b ∈ N₁, (2 * 2 ^ (b : ℕ) + 1) = ∑ b ∈ N₂, (2 * 2 ^ (b : ℕ) + 1) := by
      simpa [irregularLen, pow_succ, mul_comm] using hEq
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      hcard] at hdouble
    have hpow : ∑ b ∈ N₁, 2 ^ (b : ℕ) = ∑ b ∈ N₂, 2 ^ (b : ℕ) := by omega
    exact sum_two_pow_val_injective hpow
  · -- The swap case is impossible for even `k`.
    refine absurd ?_ (not_sum_add_sum_eq_of_even hk outer hcard)
    have hsplit : irregularLen k outer + ∑ b ∈ Finset.univ.erase outer, irregularLen k b
        = ∑ b : Fin k, irregularLen k b :=
      Finset.add_sum_erase _ _ (Finset.mem_univ outer)
    omega

end PlaneGraph

end ZonalGraphs
