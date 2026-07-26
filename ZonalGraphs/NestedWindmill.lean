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

end PlaneGraph

end ZonalGraphs
