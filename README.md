# Zonal Graphs Formalization

[![Build Project](https://github.com/walidelkersh/zonal-graphs/actions/workflows/build.yml/badge.svg)](https://github.com/walidelkersh/zonal-graphs/actions/workflows/build.yml)

A formalization of zonal labelings, inner zonal labelings, and zonal graphs in
[Lean 4](https://lean-lang.org/), built on [mathlib4](https://github.com/leanprover-community/mathlib4).

## Mathematical background

A **zonal labeling** of a connected plane graph `G` assigns to each vertex one of the two nonzero
elements of `ZMod 3`, so that the labels on the boundary of every region sum to zero. A graph admitting
such a labeling is **zonal**. A graph is **absolutely zonal** when every planar embedding of it is zonal,
and **conditionally zonal** when some embedding is and some is not.

An **inner zonal labeling** asks the same of every region except one. The existence of zonal and inner
zonal labelings is tied closely to the Four Color Theorem: a cubic map is zonal exactly when its regions
are 4-colorable, so a proof that every cubic map is zonal *without* invoking the Four Color Theorem would
constitute a new proof of it.

## Progress

Tracked in the [master to-do list](todo.md), which carries an index from each completed statement to the
Lean declaration proving it, so every checkmark is auditable. A statement is checked off only once the
GitHub build is green.

Formalized so far: Theorems 2.0.1, 2.0.2, 2.1.3, 2.1.4, 2.1.5, 2.2.2, 2.3.2, 3.1.1, 3.1.3, 3.2.1, 3.2.3;
Lemmas 2.0.3, 2.0.4; Propositions 2.0.5, 2.1.1, 2.2.1; Corollaries 3.2.2, 3.2.4; and the label-complement
normalization used throughout the literature. The library has no `sorry` and depends only on the three
standard axioms `propext`, `Quot.sound` and `Classical.choice`.

Three results are deliberately **carried as explicit hypotheses** rather than proved, each recorded as a
named proposition so that the dependency is visible in the statement of every theorem using it:

* **Theorem 1.3.2** — a connected cubic plane graph is zonal iff bridgeless. A theorem in the literature,
  but its proof invokes the Four Color Theorem, which mathlib does not have.
* **Theorem 2.1.2** (Whitney) — unique embeddability of 3-connected planar graphs. Not out of reach
  mathematically, but not expressible until the embedding layer below is developed further.
* **Lemma 2.3.1** — a count of set partitions into four equal blocks, for which mathlib has no
  supporting theory. Deferred rather than blocking, since Theorem 2.3.2 was proved without it.

## Structure

Mathlib provides no notion of a planar graph, a combinatorial embedding, or the faces of an embedding, so
this development supplies its own.

**Foundations**

* `Basic.lean` — `PlaneGraph`, an interface recording the face data of a chosen embedding: the underlying
  connected graph, the regions, their boundary vertices and edges, and the exterior region.
* `Definitions.lean` — `zoneValue`, `IsZonalLabeling`, `IsZonal`, `IsInnerZonal`.
* `Embedding.lean` — `RotationSystem`, the standard combinatorial model of an embedding by darts, a
  reversal involution and a rotation at each vertex, whose faces are the orbits of `rotate ∘ dartRev`.
* `FacialBalance.lean` — facial colour balance proved from a rotation system rather than assumed.

**Labeling machinery**

* `LabelingSums.lean` — prescribed labeling sums over a finite vertex set (Lemma 2.0.4).
* `LabelComplement.lean` — exchanging the two labels preserves zonality, giving the normalization that
  fixes a chosen vertex to the label `1`.
* `RegionBoundary.lean` — the label-count congruence on a region boundary (Lemma 2.0.3).
* `DivisibleBoundary.lean` — a plane graph is zonal when every region boundary has size divisible by
  three, which covers triangulations.

**Results**

* `TreesAndCycles.lean` — trees and cycles are zonal.
* `Subdivisions.lean` — subdividing edges preserves zonality.
* `BipartiteZonal.lean` — 2-connected bipartite planar graphs are absolutely zonal.
* `ThreeConnected.lean` — `PlaneGraph.Iso` and its invariants; 3-connected planar zonal graphs are
  absolutely zonal.
* `CubicPlanar.lean` — bridgeless cubic planar graphs are absolutely zonal.
* `Wheels.lean` — the wheel `Wₙ` is zonal iff `n ≡ 0 (mod 3)`.
* `DutchWindmill.lean` — windmill face data, the blade-count congruence, and prescribed label sums over
  pairwise disjoint blocks.
* `WindmillGraph.lean`, `StandardWindmill.lean`, `NestedWindmill.lean` — the Dutch windmill graph with its
  connectivity, its standard embedding, and the nested family that settles Theorems 2.2.2 and 2.3.2.
* `Unicyclic.lean` — unicyclic graphs are zonal unless they are a cycle with one pendant edge, and zonal
  unicyclic graphs are absolutely zonal.
* `CycleRankTwo.lean` — graphs of cycle rank two, types (1) and (2).
* `FourColor.lean` — the equivalence connecting zonal labelings of cubic maps to the Four Color Theorem.

## Building

```bash
lake exe cache get   # prebuilt mathlib oleans
lake build
```

## References

* Bowling, A. (2023). *Zonality in Graphs* (Dissertation). Western Michigan University.
* Bowling, A., & Zhang, P. (2022). *Absolutely and Conditionally Zonal Graphs*. Electron. J. Math. 4.
* Bowling, A., & Zhang, P. (2023). *Zonal Graphs of Small Cycle Rank*. Electron. J. Graph Theory Appl.
* Bowling, A., & Zhang, P. (2023). *Zonal and Inner Zonal Graphs of Maximum Degree 3*. Discrete Math. Lett. 12.
* Bowling, A. (2025). *Zonal and Cozonal Labelings over Abelian Groups*.
* Barrientos, C., & Minion, S. (2024). *Zonal Labeling of Graphs*. Indones. J. Combin.
* Chartrand, G., Egan, C., & Zhang, P. (2023). *Zonal Graphs Revisited*.
