import ZonalGraphs.WindmillGraph

namespace ZonalGraphs

/-!
# The standard embedding of a Dutch windmill

The *standard* planar embedding of `D(S)` is the one in which the boundary of every region is either
a single cycle of `S` or the whole graph: the blades are arranged side by side around the hub, none
nested inside another.

This module builds that embedding of `windmillGraph` and settles its zonality completely:
`isZonal_standardWindmill_iff` says it is zonal exactly when the number of blades is `1` modulo `3`.

Both directions come from the engines in `ZonalGraphs.DutchWindmill`.  Each blade region forces its
petal sum to be `-ℓ(hub)`, so the exterior region has value `ℓ(hub) · (1 - k)`, which vanishes only
for `k ≡ 1 (mod 3)`; conversely, when `k ≡ 1 (mod 3)` giving every petal the sum `2` and the hub the
label `1` makes every region vanish, since `1 + 2 = 0` and `1 + 2k = 1 + 2 = 0`.

At `k = 2` this recovers Proposition 2.2.1, and for `k ≥ 3` it is the standard-embedding half of
Theorem 2.2.2: the standard embedding is the non-zonal witness whenever `k ≢ 1 (mod 3)`, and the
zonal witness whenever `k ≡ 1 (mod 3)`.
-/

universe w

namespace PlaneGraph

variable {Blade : Type w} [Fintype Blade] [DecidableEq Blade]

/-- The regions of the standard embedding: one inside each blade, written `some b`, together with
the exterior region `none` bounded by all the blades at once. -/
abbrev StandardFace (Blade : Type w) := Option Blade

/-- Which petals bound each region of the standard embedding. -/
def standardRegionPetals : StandardFace Blade → Finset Blade
  | some b => {b}
  | none => Finset.univ

/-- The standard plane embedding of the Dutch windmill graph.  A region inside a blade is bounded by
the hub together with that blade's petal; the exterior region is bounded by the hub together with
every petal. -/
def standardWindmill (len : Blade → ℕ)
    (faceEdges : StandardFace Blade → Finset (Sym2 (WindmillVertex len))) :
    PlaneGraph (WindmillVertex len) (StandardFace Blade) :=
  { graph := windmillGraph len
    connected := windmillGraph_connected len
    boundary := fun R =>
      insert none ((standardRegionPetals R).biUnion (windmillPetal len))
    boundaryEdges := faceEdges
    exterior := none }

variable (len : Blade → ℕ)
  (faceEdges : StandardFace Blade → Finset (Sym2 (WindmillVertex len)))

/-- The standard embedding has the face data of a Dutch windmill, with the hub as hub and the blade
petals as petals. -/
theorem isWindmillEmbedding_standardWindmill :
    (standardWindmill len faceEdges).IsWindmillEmbedding none (windmillPetal len)
      standardRegionPetals where
  hub_notMem_petal := hub_notMem_windmillPetal len
  petal_disjoint := windmillPetal_disjoint len
  boundary_eq := fun _ => rfl

/-- **The standard Dutch windmill embedding is zonal exactly when the number of blades is `1` modulo
`3`.**

At two blades this is Proposition 2.2.1; for three or more it supplies the standard-embedding half
of Theorem 2.2.2. -/
theorem isZonal_standardWindmill_iff (hlen : ∀ b, 2 ≤ len b) :
    (standardWindmill len faceEdges).IsZonal ↔ (Fintype.card Blade : ZMod 3) = 1 := by
  refine ⟨fun hzonal => ?_, fun hcard => ?_⟩
  · exact (isWindmillEmbedding_standardWindmill len faceEdges).card_eq_one_of_isZonal
      (single := some) (full := none) (fun _ => rfl) rfl hzonal
  · refine (isWindmillEmbedding_standardWindmill len faceEdges).isZonal_of_forall_sum_eq_zero
      (fun b => by rw [card_windmillPetal]; exact hlen b) (fun _ => 2) ?_
    intro R
    cases R with
    | none =>
      simp only [standardRegionPetals, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hcard]
      decide
    | some b =>
      simp only [standardRegionPetals, Finset.sum_singleton]
      decide

end PlaneGraph

end ZonalGraphs
