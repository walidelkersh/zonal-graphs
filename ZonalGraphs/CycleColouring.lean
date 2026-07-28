import ZonalGraphs.TreesAndCycles

namespace ZonalGraphs

/-!
# The Tait correspondence on a cycle

Theorems 3.1 and 3.2 of Chartrand, Egan and Zhang, *Zonal graphs revisited*: the proper
3-edge-colourings of a cycle and its zonal labelings are the same data, read two ways.

Traverse the cycle `C = (v₀, v₁, …, v_{n-1}, v₀)` and index its edges so that edge `i` joins `vᵢ`
to `vᵢ₊₁`.  The two edges meeting at `vᵢ` are then edge `i - 1` and edge `i`, and a proper
colouring is one that gives them different colours.  The source calls `vᵢ` *of type 1* when the
colour of `vᵢvᵢ₊₁` follows that of `vᵢ₋₁vᵢ` numerically — `2` after `1`, `3` after `2`, `1` after
`3` — and *of type 2* otherwise.

Reading the three colours in `ZMod 3` with `3` as `0`, following numerically is exactly advancing
by one, so the type of `vᵢ` is the difference `c i - c (i - 1)`.  Both theorems fall out of that
identification:

* the types are nonzero because the colouring is proper, and they sum to zero because the
  difference telescopes around the cycle, which is Theorem 3.1;
* conversely the partial sums of a zonal labeling colour the edges, properly because the labels
  are nonzero and consistently around the cycle because they sum to zero, which is Theorem 3.2.

This is the cycle case of `colourStep_ne` and `colourWalk_closes` in `FacialWalks`, carried out
against the standard plane cycle `PlaneGraph.ofCycle` so that "zonal labeling" is the one this
development already uses.
-/

variable {n : ℕ}

/-- A colouring of the edges of the standard `n`-cycle with the three colours `1`, `2`, `3`, read
in `ZMod 3` with `3` as `0`.  Edge `i` joins `vᵢ` to `vᵢ₊₁`. -/
abbrev CycleColouring (n : ℕ) := Fin n → ZMod 3

variable [NeZero n]

/-- A colouring of the cycle's edges is proper when the two edges meeting at each vertex, namely
`vᵢ₋₁vᵢ` and `vᵢvᵢ₊₁`, receive different colours. -/
def IsProperCycleColouring (c : CycleColouring n) : Prop :=
  ∀ i : Fin n, c i ≠ c (i - 1)

/-- The type of the vertex `vᵢ`, as the difference of the colours of the two edges meeting there.
It is `1` when the second colour follows the first numerically and `2` otherwise. -/
def vertexType (c : CycleColouring n) (i : Fin n) : ZMod 3 :=
  c i - c (i - 1)

/-- Vertex types are nonzero exactly because the colouring is proper. -/
theorem vertexType_ne_zero {c : CycleColouring n} (hc : IsProperCycleColouring c) (i : Fin n) :
    vertexType c i ≠ 0 :=
  sub_ne_zero_of_ne (hc i)

/-- The vertex types of a proper colouring, as a labeling by nonzero elements of `ZMod 3`. -/
def typeLabeling {c : CycleColouring n} (hc : IsProperCycleColouring c) :
    VertexLabeling (Fin n) :=
  fun i => ⟨vertexType c i, vertexType_ne_zero hc i⟩

/-- The types sum to zero around the cycle: each edge colour is added once, at the vertex the edge
enters, and subtracted once, at the vertex it leaves. -/
theorem sum_vertexType (c : CycleColouring n) : ∑ i : Fin n, vertexType c i = 0 := by
  simp only [vertexType, Finset.sum_sub_distrib]
  rw [Fintype.sum_equiv (Equiv.subRight (1 : Fin n)) (fun i => c (i - 1)) c fun _ => rfl]
  simp

namespace PlaneGraph

/-- **Theorem 3.1** (Chartrand, Egan and Zhang). For every proper edge colouring of a cycle with
the colours `1`, `2`, `3`, the resulting vertex types are a zonal labeling of the cycle. -/
theorem isZonalLabeling_typeLabeling (hn : 3 ≤ n) {c : CycleColouring n}
    (hc : IsProperCycleColouring c) :
    (ofCycle n hn).IsZonalLabeling (typeLabeling hc) := by
  intro R
  simpa [zoneValue, ofCycle, typeLabeling] using sum_vertexType c

/-- The colouring built from a labeling: the colour of edge `i` is the sum of the labels of
`v₀, …, vᵢ`. -/
def partialSumColouring (labeling : VertexLabeling (Fin n)) : CycleColouring n :=
  fun i => ∑ j ∈ Finset.Iic i, (labeling j : ZMod 3)

/-- Each colour step of `partialSumColouring` is the label of the vertex it crosses.  Away from
`v₀` this is one term of the partial sum; at `v₀` it is where the labels summing to zero is
used, since the colour of the last edge is the whole sum. -/
theorem partialSumColouring_step {labeling : VertexLabeling (Fin n)}
    (hsum : ∑ v : Fin n, (labeling v : ZMod 3) = 0) (i : Fin n) :
    vertexType (partialSumColouring labeling) i = (labeling i : ZMod 3) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rcases eq_or_ne i 0 with rfl | hi
  · have hlast : ((0 : Fin (m + 1)) - 1) = Fin.last m := by
      simp [Fin.ext_iff]
    have hIic : Finset.Iic (0 : Fin (m + 1)) = {0} := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_singleton]
      exact ⟨fun h => le_antisymm h (Fin.zero_le j), fun h => h.le⟩
    simp [vertexType, partialSumColouring, hlast, hIic, ← Fin.top_eq_last, Finset.Iic_top, hsum]
  · have hIic : Finset.Iic (i - 1) = Finset.Iio i := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_Iio, Fin.le_def, Fin.lt_def, Fin.coe_sub_one, hi,
        if_false]
      have : i.val ≠ 0 := fun h => hi (Fin.ext h)
      omega
    simp only [vertexType, partialSumColouring, hIic]
    rw [← Finset.Iio_insert i, Finset.sum_insert Finset.notMem_Iio_self]
    ring

/-- **Theorem 3.2** (Chartrand, Egan and Zhang). For each zonal labeling of a cycle there is a
proper edge colouring with the colours `1`, `2`, `3` whose vertex types are that labeling. -/
theorem exists_isProperCycleColouring_vertexType_eq (hn : 3 ≤ n)
    {labeling : VertexLabeling (Fin n)} (h : (ofCycle n hn).IsZonalLabeling labeling) :
    ∃ c : CycleColouring n, IsProperCycleColouring c ∧
      ∀ i : Fin n, vertexType c i = (labeling i : ZMod 3) := by
  have hsum : ∑ v : Fin n, (labeling v : ZMod 3) = 0 := by
    simpa [zoneValue, ofCycle] using h (ofCycle n hn).exterior
  refine ⟨partialSumColouring labeling, fun i => ?_,
    fun i => partialSumColouring_step hsum i⟩
  refine sub_ne_zero.mp ?_
  show vertexType (partialSumColouring labeling) i ≠ 0
  rw [partialSumColouring_step hsum i]
  exact (labeling i).2

/-- The existence-level corollary of the two theorems: a cycle has a zonal labeling exactly when
its edges have a proper 3-colouring.  Both sides hold, so what the statement records is that each
is obtained from the other by the vertex types, not that either is in doubt. -/
theorem isZonal_ofCycle_iff_exists_isProperCycleColouring (hn : 3 ≤ n) :
    (ofCycle n hn).IsZonal ↔ ∃ c : CycleColouring n, IsProperCycleColouring c := by
  constructor
  · rintro ⟨labeling, h⟩
    obtain ⟨c, hc, -⟩ := exists_isProperCycleColouring_vertexType_eq hn h
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨typeLabeling hc, isZonalLabeling_typeLabeling hn hc⟩

end PlaneGraph

end ZonalGraphs
