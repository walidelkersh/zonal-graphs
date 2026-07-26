# Zonal Graphs Formalization

[![Build Project](https://github.com/walidelkersh/zonal-graphs/actions/workflows/build.yml/badge.svg)](https://github.com/walidelkersh/zonal-graphs/actions/workflows/build.yml)

Lean 4 formalization of zonal labelings and zonal graphs, built on mathlib4.

## Definitions

Fix a connected plane graph `G`. A *zonal labeling* assigns to every vertex one of the two nonzero
elements of `ZMod 3` so that the labels bounding each region sum to zero. `G` is *zonal* if such a
labeling exists. Since a graph admits many planar embeddings, two refinements matter: `G` is *absolutely
zonal* when every embedding is zonal, and *conditionally zonal* when some embedding is zonal and some is
not. An *inner* zonal labeling relaxes the condition at one region, typically the exterior.

The subject earns its attention from a coincidence with map coloring. A cubic map is zonal precisely when
its regions admit a proper 4-coloring, so proving every cubic map zonal without appealing to the Four
Color Theorem would yield a new proof of that theorem. None of the arguments here attempt that.

## The planarity problem

Mathlib has no planar graphs. No combinatorial embeddings, no faces, no Euler formula. `SimpleGraph.Embedding`
is a graph monomorphism and unrelated. Everything about embeddings in this repository is therefore built
here, and the choice of foundation constrains what can be stated at all.

Two layers coexist, deliberately.

`PlaneGraph` records the face data of a chosen embedding as an interface: the underlying connected graph,
an index type for regions, the boundary vertices and edges of each, and a distinguished exterior region.
Geometric validity of that data is a precondition on values of the structure, not something the structure
enforces. This buys a great deal of progress cheaply. It also means certain facts cannot be derived, only
assumed, since arbitrary boundary data satisfies the signature.

`RotationSystem` is the honest model: darts, a reversal involution `dartRev`, a rotation `rotate` at each
vertex, faces as orbits of `rotate ∘ dartRev`. Its purpose became clear only after the interface layer
started assuming things it should have proved. Facial colour balance for bipartite graphs was carried as a
hypothesis field on plane realizations; on a rotation system it is a theorem, and the proof needs no
planarity whatsoever. `dartRev` crosses an edge, so it flips colour; `rotate` fixes the vertex, so it
preserves colour. Their composite exchanges the two colour classes, and a permutation exchanging two
classes of a finite invariant set forces them equinumerous. The bijection is the permutation itself.

Migrating the remaining interface-level results onto rotation systems is unfinished.

## What is proved

Progress lives in [`todo.md`](todo.md), which indexes each completed statement against the Lean
declaration establishing it. Nothing is checked off before the GitHub build is green.

Numbering below follows Bowling's dissertation. The same results appear in the journal papers under other
numbers, listed in the third column, and one Lean proof discharges every alias.

| Dissertation | Content | Also numbered |
| --- | --- | --- |
| Thm 2.0.1 | every nontrivial tree is zonal | Thm 1.4 (small cycle rank), Prop 2.1 (abs./cond.), both stating 2.0.1 and 2.0.2 together |
| Thm 2.0.2 | every cycle is zonal | as above |
| Lem 2.0.3 | on a region boundary the two label counts agree mod 3 | Obs. 2.3 (revisited) |
| Lem 2.0.4 | a vertex set admits prescribed label sums | Lem 2.2 (small cycle rank), Lem 3.1 (abs./cond.) |
| Prop 2.0.5 | subdividing edges twice or more preserves zonality | |
| Prop 2.1.1 | 2-connected bipartite planar graphs are absolutely zonal | Prop 4.1 (small cycle rank), Prop 2.2 (abs./cond.) |
| Thm 2.1.3 | 3-connected planar zonal graphs are absolutely zonal | |
| Thm 2.1.4 | bridgeless cubic planar graphs are absolutely zonal | |
| Thm 2.1.5 | the wheel `Wₙ` is zonal iff `n ≡ 0 (mod 3)` | Thm 2.2 (abs./cond.) |
| Prop 2.2.1 | a Dutch windmill on two cycles is never zonal | Prop 3.1 (abs./cond.) |
| Thm 2.2.2 | on three or more cycles it is conditionally zonal | Thm 3.1 (abs./cond.) |
| Thm 2.3.2 | some irregular Dutch windmill has arbitrarily many zonal embeddings | Thm 4.1 (abs./cond.) |
| Thm 3.1.1 | a unicyclic graph is zonal unless it is a cycle with one pendant edge | Thm 2.3 (small cycle rank) |
| Thm 3.1.3 | zonal unicyclic graphs are absolutely zonal | Prop 2.4 (small cycle rank) |
| Thm 3.2.1 | cycle rank 2, type (1): zonal iff not minimal | Thm 3.1 (small cycle rank) |
| Cor 3.2.2 | the graph-level restatement of 3.2.1 | |
| Thm 3.2.3 | cycle rank 2, type (2): zonal iff no lone vertex off the cycles | Thm 3.2 (small cycle rank) |
| Cor 3.2.4 | the graph-level restatement of 3.2.3 | |
| Obs. 1.4.2 | complementing a zonal labeling stays zonal | Obs. 2.1 (abs./cond.) |

Short titles above: *abs./cond.* is Bowling and Zhang (2022), *small cycle rank* is Bowling and Zhang
(2023), *revisited* is Chartrand, Egan and Zhang (2023). Watch the collisions: `Thm 3.1` names the
cycle-rank-two result in one paper and the windmill result in another, so a bare number identifies nothing.
Declaration names live in `todo.md` rather than here, so that renaming a lemma does not silently falsify
this file.

No `sorry` appears in the library. Axiom dependencies reduce to `propext`, `Quot.sound` and
`Classical.choice`.

Two formalizations diverge from the published arguments, in both cases shortening them. Bowling and Zhang
prove Theorem 2.2.2 through three constructions: the standard windmill embedding, a fully nested chain for
odd blade count, and a hybrid of four side-by-side blades with a chain for even count at least six.
Nesting `m` blades inside one fixed blade covers all three, and zonality of the resulting embedding
reduces to a single congruence, `m = 2k + 1` in `ZMod 3` with `k` blades. The parity split disappears. For
Theorem 2.3.2 the published proof bounds a sum of the largest blade lengths; choosing odd blade lengths
instead kills the unwanted case by parity, with no estimate required.

## What is assumed

Three statements are passed in as hypotheses rather than proved. Each is a named proposition, so any
theorem depending on one says so in its own signature.

* Theorem 1.3.2, that a connected cubic plane graph is zonal exactly when bridgeless, holds in the
  literature. Its proof invokes the Four Color Theorem, which mathlib lacks. A 4CT-free proof would
  itself constitute a new proof of 4CT, so this is not a gap that closing is cheap.
* Whitney's unique-embedding theorem (2.1.2) is not hard mathematics. On `PlaneGraph` as an interface of
  supplied face data it is not expressible, because nothing constrains one realization against another.
  `Embedding.lean` starts the layer that would make it sayable.
* Lemma 2.3.1 counts partitions of a `4k`-set into four unordered `k`-blocks. Mathlib offers
  `Nat.multinomial` and nothing about unordered equal-size set partitions, so a faithful proof means
  building that theory. It was scaffolding: Theorem 2.3.2 went through without it.

## Modules

Foundations:

* `Basic.lean`, `Definitions.lean` hold `PlaneGraph`, `zoneValue`, `IsZonal`, `IsInnerZonal`.
* Rotation systems and the facial balance theorem sit in `Embedding.lean` and `FacialBalance.lean`.

Labeling machinery, which most later proofs route through:

* `LabelingSums.lean` realizes prescribed sums over a finite vertex set (Lemma 2.0.4).
* Complementing a labeling negates every region value, hence preserves zonality: `LabelComplement.lean`.
* `RegionBoundary.lean` proves the label-count congruence on a boundary.
* Where every region boundary has size divisible by three, the constant labeling `1` already works.
  `DivisibleBoundary.lean` records this, which covers triangulations.
* One observation recurs across the non-zonality proofs and is isolated in `BoundaryDifference.lean`: two
  regions whose boundaries differ by a single vertex cannot both have value zero.
* The general prescription lemma, in `DutchWindmill.lean`, fixes label sums on any family of pairwise
  disjoint blocks. Label everything `1`, then flip `(target − |block|).val` vertices per block. A block
  must hold as many vertices as the flips it absorbs, and that count never exceeds two, so the single
  obstruction is a block of size exactly one. Theorems 3.1.1, 3.1.3, 3.2.1 and 3.2.3 all bottom out here.

Results:

* Trees and cycles: `TreesAndCycles.lean`. Subdivisions: `Subdivisions.lean`.
* `BipartiteZonal.lean`, `ThreeConnected.lean`, `CubicPlanar.lean` handle the 2-connected bipartite,
  3-connected, and bridgeless cubic cases. `ThreeConnected.lean` also carries `PlaneGraph.Iso` and the
  invariants used to separate embeddings.
* `Wheels.lean` settles `Wₙ`.
* Windmills occupy four files: face data and the blade-count congruence in `DutchWindmill.lean`, the graph
  with its connectivity proof in `WindmillGraph.lean`, then `StandardWindmill.lean` and
  `NestedWindmill.lean`.
* `Unicyclic.lean` and `CycleRankTwo.lean` cover cycle rank one and two.
* `FourColor.lean` states the cubic-map equivalence without claiming it.

## Building

```bash
lake exe cache get
lake build
```

## References

* Bowling, A. (2023). *Zonality in Graphs*. Dissertation, Western Michigan University.
* Bowling, A., & Zhang, P. (2022). *Absolutely and Conditionally Zonal Graphs*. Electron. J. Math. 4, 1–11.
* Bowling, A., & Zhang, P. (2023). *Zonal Graphs of Small Cycle Rank*. Electron. J. Graph Theory Appl.
* Bowling, A., & Zhang, P. (2023). *Zonal and Inner Zonal Graphs of Maximum Degree 3*. Discrete Math. Lett. 12, 130–137.
* Bowling, A. (2025). *Zonal and cozonal labelings using arbitrary abelian groups*. Utilitas Math. 124, 83–100. DOI 10.61091/um124-05.
* Barrientos, C., & Minion, S. (2024). *Zonal Labeling of Graphs*. Indones. J. Combin.
* Chartrand, G., Egan, C., & Zhang, P. (2023). *Zonal Graphs Revisited*. Bull. Inst. Combin. Appl. 99.
