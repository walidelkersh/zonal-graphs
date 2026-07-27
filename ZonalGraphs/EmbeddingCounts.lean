import ZonalGraphs.EmbeddingDistinctness

namespace ZonalGraphs

/-!
# Counting distinct embeddings

Corollaries 2.5.10 and 2.5.12 and Theorem 2.5.13 assert that a graph has *at least* so many distinct zonal or
non-zonal planar embeddings. Distinctness of a given pair is already available from
`not_nonempty_iso_of_card_filter_ne`, but a count is a different kind of claim: it needs a family of embeddings
exhibited, all on the same graph, pairwise non-isomorphic, and each zonal or each non-zonal.

That is what the two predicates here say. The region type is taken to be `Fin r` for some `r`, which costs
nothing and avoids carrying a `Fintype` instance through an existential.

What these definitions do not supply is the family itself. For `Gn` the embeddings `Gn,k` have to be built as
`PlaneGraph`s, with their region structure written out rather than assumed, and that is the step still missing:
`isZonal_of_forall_isGnRegion` and `not_nonempty_iso_of_gn_profile` take the region structure as a hypothesis, so
they establish each `Gn,k` is zonal and that different `k` give non-isomorphic embeddings, but neither exhibits
the face data.
-/

universe u

variable {V : Type u} [Fintype V]

/-- A graph has at least `m` distinct zonal planar embeddings when some family of `m` plane graphs on it is
pairwise non-isomorphic with every member zonal. -/
def SimpleGraph.HasAtLeastZonalEmbeddings (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (r : ℕ) (P : Fin m → PlaneGraph V (Fin r)),
    (∀ t, (P t).graph = G) ∧ (∀ t, (P t).IsZonal) ∧
      ∀ t t', t ≠ t' → ¬ Nonempty ((P t).Iso (P t'))

/-- A graph has at least `m` distinct non-zonal planar embeddings when some family of `m` plane graphs on it is
pairwise non-isomorphic with no member zonal. -/
def SimpleGraph.HasAtLeastNonZonalEmbeddings (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (r : ℕ) (P : Fin m → PlaneGraph V (Fin r)),
    (∀ t, (P t).graph = G) ∧ (∀ t, ¬ (P t).IsZonal) ∧
      ∀ t t', t ≠ t' → ¬ Nonempty ((P t).Iso (P t'))

/-- A count can be lowered: exhibiting more embeddings than needed still gives the smaller bound. -/
theorem SimpleGraph.HasAtLeastZonalEmbeddings.mono {G : SimpleGraph V} {m m' : ℕ} (hle : m' ≤ m)
    (h : SimpleGraph.HasAtLeastZonalEmbeddings G m) : SimpleGraph.HasAtLeastZonalEmbeddings G m' := by
  obtain ⟨r, P, hgraph, hzonal, hiso⟩ := h
  refine ⟨r, fun t => P ⟨t.val, lt_of_lt_of_le t.isLt hle⟩, fun t => hgraph _, fun t => hzonal _,
    fun t t' hne => hiso _ _ ?_⟩
  intro hcon
  exact hne (by simpa [Fin.ext_iff] using hcon)

/-- The same for non-zonal embeddings. -/
theorem SimpleGraph.HasAtLeastNonZonalEmbeddings.mono {G : SimpleGraph V} {m m' : ℕ} (hle : m' ≤ m)
    (h : SimpleGraph.HasAtLeastNonZonalEmbeddings G m) : SimpleGraph.HasAtLeastNonZonalEmbeddings G m' := by
  obtain ⟨r, P, hgraph, hzonal, hiso⟩ := h
  refine ⟨r, fun t => P ⟨t.val, lt_of_lt_of_le t.isLt hle⟩, fun t => hgraph _, fun t => hzonal _,
    fun t t' hne => hiso _ _ ?_⟩
  intro hcon
  exact hne (by simpa [Fin.ext_iff] using hcon)

end ZonalGraphs
