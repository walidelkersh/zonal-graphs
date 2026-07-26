import ZonalGraphs.StandardWindmill

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

end PlaneGraph

end ZonalGraphs
