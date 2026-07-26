# Master Formalization To-Do List

## How to read this list

`- [x]` means the statement is formalized **and** the GitHub build was green at the time it was
checked. Every checked item is listed in the index below with the Lean declaration that proves it, so
a checkmark can be audited.

Two caveats about the list itself, both consequences of extracting it from PDFs. A third, a verbatim
duplicate of the dissertation section, has been removed: the former section `00` was byte-identical to
`01`, so it doubled every count and forced every checkmark to be applied twice.

* **The same theorem recurs across papers under different numbers.** For instance "every 2-connected
  bipartite planar graph is absolutely zonal" is Proposition 2.1.1 in `01`, Proposition 4.1 in `02`
  and Proposition 2.2 in `04`. One Lean proof discharges all of its aliases.
* **Extraction artifacts have now been triaged against the sources.** Ten entries are tagged
  `[ARTIFACT: ...]` with the reason: proof excerpts, discussion prose, or a pointer to a result listed
  elsewhere. Two were recoverable and are tagged `[RECOVERED: ...]` with the statement restored, namely
  the size of a maximal outerplanar graph and the graph form of the Four Color Theorem. One further entry
  turned out to be a definitions paragraph rather than a theorem. Anything tagged `ARTIFACT` should be
  dropped from the denominator; it is not work.

  Re-verified against the sources with `pdftotext`. The tags are correct and none of the ten hides a
  statement. The one worth naming is the entry sitting between Theorems 4.3.1 and 4.3.2, which reads as
  though a corollary were being stated. It is not: the source says "This establishes the following
  corollary, the truth of which is independent of the Four Color Theorem", and the corollary it announces
  is Theorem 4.3.2, already listed. So the honest denominator is 181 provable entries, not 191.

The count of genuinely distinct statements is therefore well below the number of lines here.

## Proved in Lean

| Statement | Declaration |
| --- | --- |
| Theorem 2.0.1 | `PlaneGraph.every_nontrivial_tree_is_zonal` |
| Theorem 2.0.2 | `PlaneGraph.every_cycle_is_zonal` |
| Lemma 2.0.3 | `zonal_boundary_label_counts_modEq` |
| Lemma 2.0.4 | `lemma_2_0_4` |
| Proposition 2.0.5 | `zonal_of_isSubdivision` |
| Proposition 2.1.1 | `every_twoConnected_bipartite_planar_isAbsolutelyZonal` |
| Theorem 2.1.3 | `threeConnected_zonal_isAbsolutelyZonal` |
| Theorem 2.1.4 | `bridgeless_cubic_planar_isAbsolutelyZonal` |
| Theorem 2.1.5 | `wheel_isZonal_iff_modEq_zero` |
| Proposition 2.2.1 | `PlaneGraph.not_isZonal_ofTwoBladedWindmill` |
| Theorem 2.2.2 | `PlaneGraph.conditionallyZonal_windmill` |
| Theorem 2.3.2 | `PlaneGraph.exists_irregular_windmill_many_zonal_embeddings` |
| Theorem 3.1.1 | `PlaneGraph.isZonal_iff_card_sdiff_boundary_ne_one` |
| Theorem 3.1.3 | `PlaneGraph.isZonal_of_boundary_eq_union` |
| Theorem 3.2.1 | `PlaneGraph.isZonal_iff_not_minimal_cycleRankTwo_typeOne` |
| Corollary 3.2.2 | the two halves above, per embedding |
| Theorem 3.2.3 | `PlaneGraph.isZonal_iff_card_ne_one_cycleRankTwo_typeTwo` |
| Corollary 3.2.4 | the theorem above, per embedding |
| Thm 3.3 (small cycle rank) | `PlaneGraph.isZonal_iff_cycleRankTwo_typeThree` |
| Thm 3.4 (small cycle rank) | `PlaneGraph.isZonal_of_contains_minimal_nonZonal` |
| Thm 3.5 (small cycle rank) | `PlaneGraph.isZonal_thetaPendant_of_nonempty` and `isZonal_thetaPendant_of_empty` |
| Thm 3.6 (small cycle rank) | `PlaneGraph.isZonal_cycleRankTwo_typeThree_proper` |
| Cor 3.7, Thm 3.8 (small cycle rank) | collections of the six theorems above: 3.2.1 and 3.2.3 for types (1) and (2), Thm 3.3 for minimal type (3), Thms 3.4, 3.5 and 3.6 for the non-minimal cases |
| Thm 3.2.5, Cor 3.2.6 (dissertation) | the same type (3) characterization as Thms 3.6 and 3.8 above, in the dissertation's numbering: `isZonal_iff_cycleRankTwo_typeThree`, `isZonal_of_contains_minimal_nonZonal`, `isZonal_thetaPendant_of_nonempty`, `isZonal_cycleRankTwo_typeThree_proper` |
| Lemma 4.3.3 | `PlaneGraph.exists_isZonalLabeling_constant_on_blocks`, on `exists_labeling_constant_on_blocks` |
| Prop 3.3.2, Prop 4.3 | `PlaneGraph.isZonal_of_subdivide_all_edges`, on `isZonal_of_uniform_subdivision` |
| Thm 4.4.5, Cor 4.4.6 | `PlaneGraph.isZonal_of_isInnerZonal_of_three_regionsAt` and `isZonal_iff_isInnerZonal_of_three_regionsAt`, on `sum_zoneValue_eq_sum_regionsAt` |
| Thm 2.5.9 | `PlaneGraph.isZonal_of_forall_isGnRegion`, on `GnVertex.sum_triangle`, `sum_quad`, `sum_pentagon` and `sum_blocks` |
| Thm 2.5.11 | `PlaneGraph.not_isZonal_of_gn_forcing`, on `eq_of_zoneValue_eq_zero_of_card_boundary_eq_three` |
| Thm 2.5.5, Thm 2.5.8 | `PlaneGraph.not_nonempty_iso_of_gn_profile`, on `Iso.card_filter_boundary_card` |
| Prop 2.4.1 | `PlaneGraph.isZonal_of_card_boundary_eq_three_or_nine` |
| Prop 1.1, 1.2 (zonal labeling) | Theorems 2.0.1 and 2.0.2 above |
| Lem 2.1, Prop 2.2 (zonal labeling) | `PlaneGraph.isZonal_iff_card_sdiff_boundary_ne_one`, the off-cycle count being `n - g` |
| Prop 2.4 (zonal labeling) | Proposition 2.0.5 above, even counts being at least two |
| Prop 2.3 (zonal labeling) | `PlaneGraph.isZonal_of_card_boundary_eq_three` and `isInnerZonal_of_card_boundary_interior_eq_three` |
| Thm 3.3 (max degree 3) | `PlaneGraph.zonal_of_isSubdivision` and `innerZonal_of_isSubdivision` |
| Prop 3.2 (zonal labeling) | `PlaneGraph.isZonal_edgeAmalgamation` |
| Lem 2.3 (abelian groups) | `exists_three_nonzero_add_eq_zero` |
| Prop 2.4 (abelian groups) | `PlaneGraph.isGroupZonal_ofCycle` |
| Prop 1.3 (abelian groups) | `Incidence.isZonal_iff_dual_isCozonal` |
| Thm 1.4 (small cycle rank) | Theorems 2.0.1 and 2.0.2 above, stated together |
| Lem 2.2 (small cycle rank) | `lemma_2_0_4`, the same statement |
| Corollary 3.1.2 | `lemma_2_0_4` at a cycle, which has at least three vertices so all three targets are reachable |
| Observation 2.1 | `PlaneGraph.exists_isZonalLabeling_apply_eq_one` |

Supporting results with no todo entry of their own: `RotationSystem.isBalanced_of_faceMap_invariant`
(facial colour balance, proved rather than assumed), `windmillGraph_connected`,
`PlaneGraph.isZonal_of_three_dvd_card_boundary`, `PlaneGraph.isZonal_of_blockDecomposition`,
`PlaneGraph.not_isZonal_of_boundary_insert`, and on the abelian-group side `IsGroupZonal` with
`isGroupZonal_zmod_three_iff` showing it is definitionally the classical notion, `IsGroupCozonal`,
`isGroupZonal_of_facialBalance` (the zonal half of Prop 2.7) and `isGroupZonal_map` (Observation 2.2).

## Carried as explicit hypotheses, not proved

These are deliberately *not* checked. Each is recorded as a named proposition and passed in where
needed, so the logical dependency is visible in the statement of every result that uses it.

* **Theorem 1.3.2 / 4.1.1** (`CubicZonalIffBridgeless`) — a connected cubic plane graph is zonal iff
  bridgeless. A theorem in the literature, but its proof invokes the Four Color Theorem, and a
  4CT-free proof would itself constitute a new proof of 4CT.
* **Theorem 2.1.2** (`WhitneyUniqueEmbedding`) — Whitney's unique-embedding theorem. Not out of reach
  mathematically; it is not expressible while `PlaneGraph` is an interface of supplied face data.
  `ZonalGraphs.Embedding` begins the combinatorial-embedding layer that would make it expressible.
* **Lemma 2.3.1** — the count of partitions of a `4k`-set into four unordered `k`-subsets. Mathlib has
  no counting theorem for unordered equal-size set partitions. Deferred rather than blocking:
  Theorem 2.3.2 was proved without it.
* **The Gn family, Theorems 2.5.1 and 2.5.5 to 2.5.13** — no longer blocked on unread sources. The
  construction, recovered from pages 38 to 43 of the dissertation, is this. Take W4, the wheel of order
  five, as Fi with outer cycle (ri, si, ti, ui) and hub vi. Replace the edge si-ti by the path
  (si, wi, xi, ti) for i at most n-1, replace the edge ri-ui by the path (ri, y(i-1), z(i-1), ui) for i at
  least 2, then add the edges wi-yi and xi-zi joining consecutive blocks. So Gn has 9n-4 vertices, and the
  irregular cases are i = 1 and i = n, where one of the two subdivided edges is absent. The embeddings
  Gn,k are obtained by turning the sub-embedding on the first k blocks inside out, and Observation 2.5.4
  records that Gn,k then has an exterior region of boundary length 8(n-k), an interior region of length
  8k, and all other regions of length 3, 4 or 5, with 5n regions in total.

  What each entry needs from here:
  - **Theorem 2.5.9** (Gn,k is zonal for k in {0, 2, 3, ..., n/2}) needs only the region structure, since
    zonality reads the boundary function and never the adjacency. The labeling is explicit: ri, si, ti, ui
    and vi all take a common value ai, while wi and yi take 1 and xi and zi take 2. The coefficients ai
    come from Lemma 2.0.4, which is already proved here, applied to split the indices at k. The region
    list is now recovered in full, so nothing outstanding remains to be read. Writing ai for the common
    value on block i, the regions and their sums are: n of boundary (ri, si, vi) summing to 3ai; n of
    boundary (vi, ti, ui) summing to 3ai; n-2 of boundary (wi, yi, zi, xi) summing to 1+1+2+2 = 6, and
    n-1 of them when k = 0; n-1 of boundary (ri, vi, ui, z(i-1), y(i-1)) summing to 3ai+3; and n-1 of
    boundary (si, wi, xi, ti, vi) summing to 3ai+3. The exterior region of length 8(n-k) carries the
    eight labels r, s, t, u, w, x, y, z of each block above k, contributing 4ai+6 per block, so its total
    is the sum of the ai above k because 4 = 1 in ZMod 3. The interior region of length 8k is the same
    with the blocks at or below k. Those two are exactly where the split condition from Lemma 2.0.4 is
    used, and every other region vanishes outright.
  - **Theorem 2.5.1** (Gn is 2-connected) needs Gn built as a SimpleGraph and connectivity of every
    vertex-deleted subgraph. That is harder than the windmill and theta constructions already here,
    because those needed plain connectivity rather than deletion-robust connectivity.
  - **Theorem 2.5.11** (Gn,k is not zonal for 1 <= k <= n-2) is a forcing chain, and its engine is now
    proved as `eq_of_zoneValue_eq_zero_of_card_boundary_eq_three`: a region with three boundary vertices
    forces a zonal labeling to be constant on it, because three nonzero elements of ZMod 3 summing to
    zero must coincide. The chain runs: vn lies on three triangles, so rn, sn, tn, un and vn share a
    label, taken to be 1; the region (y(n-1), z(n-1), un, vn, rn) then forces the two remaining labels to
    sum to 0; the nine-vertex region forces w(n-1) and x(n-1) to be 1; the triangles at v(n-1) force its
    block onto one label; and the region (v(n-1), s(n-1), w(n-1), x(n-1), u(n-1)) then sums to three
    times that label plus 2, which never vanishes.
  - **Theorems 2.5.5, 2.5.8 and Corollaries 2.5.10, 2.5.12** rest on the embeddings being
    distinct, which is an isomorphism-invariant argument of the kind `nestingSet_eq_of_iso` already
    carries for windmills.

  The method that recovered this is worth recording: `pdftotext -f <first> -l <last>` on the PDFs in
  `C:\ProjectsCT & ZONAL`. Printed page numbers lag the PDF indices by about six, so search by
  theorem number rather than by page. The same method should be used to repair the entries tagged
  `[ARTIFACT: ...]`, most of which are truncations rather than genuine non-statements.

* **Theorems 4.3.1, 4.3.2, 4.3.5, 4.3.6 and 4.3.8 — a new kind of obstruction, and it is the interface.**
  The proof of 4.3.1 is Theorem 6.16 of Chartrand, Egan and Zhang, in `chartrand2019.pdf`, and it runs by
  induction on the number of chords: the step deletes the interior vertices of one region to reach a
  smaller bicubic map with one fewer chord. Its base case is proved here as
  `exists_labeling_pair_eq_of_two_boundaries` and `isInnerZonal_of_one_chord`, so the entry is not
  checked off, since only the base case is done.

  The step cannot be stated faithfully on `PlaneGraph`. Face data is carried as given, so "deleting the
  interior vertices of this region leaves a bicubic map whose exterior boundary is a Hamiltonian cycle
  with one fewer chord" is not derivable; it would have to be assumed, and that assumption concedes most
  of the statement. This is unlike the other blockers, which are missing mathlib content. The fix is
  structural: build `PlaneGraph` from a `RotationSystem`, where vertex deletion acts on the darts and the
  new faces are computed as `faceMap` orbits rather than posited. `Embedding.lean` already has the
  rotation system, `faceMap` and the orbit view, so the missing piece is the bridge from a rotation
  system to a `PlaneGraph`, plus the effect of deletion on it. That one construction would unblock all
  five of these entries, and it is the highest-leverage piece of infrastructure left in the project.

* **Theorem 2.5.1, the 2-connectedness of Gn — half done, and the rest is volume rather than a blocker.**
  `Gn` is now a real graph, `gnGraph`, with symmetry, looplessness, connectivity (`gnGraph_connected`) and
  the vertex count `5n + 4(n-1) = 9n - 4` all proved. `IsTwoConnected` is a conjunction and its first
  half, `3 <= card`, is `three_le_card_gnVertex`.

  What remains is the second half: for every vertex `c`, the induced graph on the complement of `{c}` is
  connected. Nothing is missing from mathlib for this; it is case volume. The redundancy that makes it true
  is worth writing down, because it is what the paths must use. Inside a block the hub meets all four rim
  vertices, so losing one rim vertex still leaves the rim connected through the hub, and losing the hub
  leaves the rim connected through its own cycle. Across a gap there are two vertex-disjoint connections,
  `w-y` and `x-z`, so no single deletion separates consecutive blocks. Note `Gn` is a path of blocks rather
  than a cycle, so the gap redundancy is doing all the work between blocks and there is no second route
  around.

  The practical cost is that `SimpleGraph.induce` puts the work in the subtype `{x // x != c}`, so each
  path has to be built there. Nine vertex families and the two irregular ends give a wide case split. This
  is the largest single remaining proof in the Gn group.

  **A failed attempt, and a correction to how it was first recorded.** The gap-redundancy lemma was
  written and did not build. The first note here claimed it elaborated clean under `lean-lsp` while
  exceeding 570 seconds under `lake build`, and offered that as a discrepancy between the two tools. That
  reading was wrong. Bisecting the file down to a single helper lemma produced a real type error: a
  misapplied `Sum.noConfusion`, whose expected type is a `noConfusionType` rather than `False`. The long
  builds were failing elaboration retrying against unsolved metavariables, not honest proof cost. This is
  the same mistake as the earlier false performance claim in this project, drawn from timing a failure.

  What is established: the module builds in about ten seconds without the attempt, the attempt does not
  build, and `lean-lsp` reported the file clean when it contained a type error, so a clean LSP diagnostic
  did not reflect the file's real state here. What is *not* established is any claim about proof cost. After
  the type error was corrected the module still did not build inside the time allowed, but given the
  measurement history that number should not be trusted until the file compiles at all.

  The attempt is parked at `GnGraph_deletion_attempt.lean` in the session scratchpad, and it contains the
  bad `Sum.noConfusion` proofs. Anyone resuming should get it compiling first, by ordinary means and checked
  with a build rather than with LSP diagnostics, before drawing any conclusion about performance.

* **Proposition 2.8** — the labelling half is proved as `isGroupZonal_of_threeColouring`: give the three
  colour classes a triple of nonzero elements summing to zero and a region holding one vertex of each
  colour vanishes. What is missing is Heawood's theorem, that a plane triangulation is vertex 3-colourable
  exactly when it is Eulerian, which enters as a hypothesis rather than being proved. The entry also pairs
  the claim with a cozonal dual about bipartite cubic maps.

* **The remaining dual halves** — the cozonal side is now available. Duality needed no multigraphs after
  all: zonality and cozonality never consult the underlying graph, only which vertices bound which
  regions, so abstracting that incidence data makes the dual a transposition and Proposition 1.3 a matter
  of unfolding. What is still missing for entries such as Theorem 1.4 and Proposition 2.8 is not duality
  but tricolorings and Eulerian plane graphs, which are separate notions.

* **Theorem 1.1.1** (the Euler identity) — a finding, not an excuse. In the rotation-system model a map's
  Euler characteristic is `V - E + F` with `V`, `E`, `F` the orbit counts of `rotate`, `dartRev` and
  `faceMap`, and genus is *defined* by `V - E + F = 2 - 2g`. Planarity is genus zero, so `V - E + F = 2`
  is the definition of planar rather than a theorem about it. Proving Euler as stated needs planarity
  defined independently, either topologically in the plane, which needs the Jordan curve theorem, or
  combinatorially via Kuratowski. Until one of those exists the entry is not provable as written, and the
  same applies to Theorems 1.1.2, 1.1.3 and the outerplanarity results that rest on it.
  `RotationSystem.two_dvd_card_dart` is the first genuine ingredient: reversal is a fixed-point-free
  involution, so the darts pair off and `E` is `Fintype.card Dart / 2`.


## 01_Bowling_2023_Zonality_in_Graphs_Dissertation.pdf

- [ ] **Theorem 1.1.1**: (The Euler Identity) If G is a connected plane graph of order n, size m, and having r regions, then n − m + r = 2. 2
- [ ] **Theorem 1.1.2**: If G is a planar graph of order n ≥ 3 and size m, then m ≤ 3n − 6.
- [ ] **Theorem 1.1.3**: Every planar graph contains a vertex of degree 5 or less. A graph H is a subdivision of a graph G if either H ∼= G or H can be obtained from G by inserting vertices of degree 2 into edges of G. Con...
- [ ] **Theorem 1.1.4**: A graph G is planar if and only if G contains no subgraph that is a subdivision of K5 or K3,3. A planar graph G is maximal planar if the addition to G of any edge joining two nonadjacent vertices o...
- [ ] **Theorem 1.2.1**: A graph G is outerplanar if and only if the join G ∨ K1 of G and K1 is planar.
- [ ] **Theorem 1.2.2**: If G is an outerplanar graph of order n ≥ 2 and size m, then m ≤ 2n − 3.
- [ ] **Theorem 1.2.3**: Every nontrivial outerplanar graph contains at least two vertices of degree 2 or less. The graphs K4 and K2,3 and their subdivisions (see Figure 1.2) play a pivotal role in the study of outerplanar...
- [ ] **Theorem 1.2.4**: A graph G is outerplanar if and only if G contains no subgraph that is a subdivision of K4 or K2,3. We have seen that a graph G is planar if and only if a subdivision of G is planar. However, this ...
- [ ] **Corollary to Theorem 1.2.2**: The size of a maximal outerplanar graph of order n ≥ 2 is exactly 2n − 3. [RECOVERED: the original entry began mid-sentence at "by Theorem 1.2.2, ..."]
- [ ] **Definitions (not a theorem)**: cut-vertex, vertex-cut, connectivity, bridge, edge-cut, edge-connectivity, cubic map. [ARTIFACT: a definitions paragraph, nothing to prove; mathlib already has SimpleGraph.IsBridge and IsRegularOfDegree]
- [ ] **Theorem 1.3.1**: (Tait’s Theorem) The regions of a cubic map M can be colored with four or fewer colors so that every two adjacent regions are colored differently if and only if there is a proper edge coloring of M...
- [ ] **Theorem 1.3.2**: A connected cubic plane graph G is zonal if and only if G is bridgeless.
- [ ] **Theorem 1.3.3**: There exists a 4-coloring of the zones of a cubic map M if and only if M has a zonal labeling. 7 As described in [5], the argument given that establishes the truth of Theo- rem 1.3.2 makes use of t...
- [ ] **Proposition 1.4.1**: For every cubic map, there is a region whose boundary cycle has length 5 or less.
- [ ] **Theorem 1.4.3**: Let G be a cubic map (2-edge-connected cubic plane graph) with a region RT having a triangle T as its boundary, and let H be the graph obtained from G by contracting the three edges of T into a sin...
- [x] **Theorem 2.0.1**: Every nontrivial tree is zonal.
- [x] **Theorem 2.0.2**: Every cycle is zonal. For example, two zonal labelings of the cycles C3, C4, and C5 are shown in Figure 2.1. In fact, they are the only zonal labelings of these cycles. That is, a zonal labeling of...
- [x] **Lemma 2.0.3**: Let H be the boundary of a region R in a plane graph G with a zonal labeling ℓ. If ni vertices of H are labeled i by ℓ for i = 1 , 2, then n1 ≡ n2 (mod 3).
- [x] **Lemma 2.0.4**: Let X be a nonempty set of vertices of a graph. (1) For each i = 1 , 2, there is a labeling ℓi : X → {1, 2} ⊆Z3 of X such thatP(ℓi, X) = i in Z3. 15 (2) If |X| ≥2, then there is a labeling ℓ0 : X →...
- [x] **Proposition 2.0.5**: Let G be a zonal graph and let X be a set of edges of G. If H is a graph obtained by subdividing each edge of X two or more times, then H is zonal. 2.1 Absolutely Zonal Graphs Since there is only o...
- [x] **Proposition 2.1.1**: Every 2-connected bipartite planar graph is absolutely zonal.
- [ ] **Theorem 2.1.2**: (Whitney’s Theorem) Every 3-connected planar graph is uniquely embeddable in the plane. As a consequence of Theorem 2.1.2, every 3-connected planar graph is either absolutely zonal or non-zonal. Th...
- [x] **Theorem 2.1.3**: Every 3-connected planar zonal graph G is absolutely zonal. Thus, no 3-connected planar graph is conditionally zonal. By Theorem 2.1.2, every 3-connected cubic planar graph is uniquely embed- dable...
- [x] **Theorem 2.1.4**: Every connected bridgeless cubic planar graph is absolutely zonal. 18 M2 : ..................................................................................... .......................................
- [x] **Theorem 2.1.5**: For an integer n ≥ 3, the wheel Wn = Cn ∨ K1 is zonal if and only if n ≡ 0 (mod 3) .
- [ ] **Theorem 2.1.8**: For every positive integer k, there exists a connected bridgeless cubic planar graph having at least k distinct (zonal) planar embeddings.
- [x] **Proposition 2.2.1**: For every multiset S of two cycles, the Dutch windmill graph D(S) is not zonal.
- [x] **Theorem 2.2.2**: For every multiset S of three or more cycles, the Dutch windmill graph D(S) is conditionally zonal.
- [ ] **Lemma 2.3.1**: Let S be a set with 4k elements for some positive integer k. The number of partitions of S into four k-element subsets is 4Y i=1 ik − 1 k − 1  = 4k − 1 k − 1 3k − 1 k − 1 2k − 1 k − 1  . (2.1)
- [x] **Theorem 2.3.2**: There is an irregular Dutch windmill graph that has an arbitrarily large number of distinct zonal planar embeddings.
- [x] **Proposition 2.4.1**: For a positive integer k, the plane graph Fk is zonal.
- [ ] **Theorem 2.4.2**: There is a regular Dutch windmill graph that has an arbitrarily large number of distinct zonal planar embeddings.
- [ ] **Proposition 2.4.3**: Let k be a positive integer. ⋆ If µ(k) ≡ 1 (mod 3), then the zonal Dutch windmill graph Dµ(k) 3 is condition- ally zonal and has at least k distinct zonal planar embeddings. ⋆ If µ(k) ≡ 2 (mod 3), ...
- [ ] **Theorem 2.5.1**: The graph Gn is 2-connected.
- [x] **Theorem 2.5.5**: For 0 ≤ k ≤ n/2, the embeddings Gn,k are distinct.
- [x] **Theorem 2.5.8**: For 0 ≤ k ≤ n − 2 n ≥ 3 the embeddings G∗ n,k are distinct.
- [x] **Theorem 2.5.9**: For each k ∈ {0, 2, 3, . . . ,⌊n/2⌋}, the plane graph Gn,k has a zonal labeling.
- [ ] **Corollary 2.5.10**: The plane graph Gn has at least ⌊n/2⌋ zonal embeddings.
- [x] **Theorem 2.5.11**: If 1 ≤ k ≤ n − 2, then G∗ n,k does not have a zonal labeling.
- [ ] **Corollary 2.5.12**: The plane graph Gn has at least n − 1 non-zonal embeddings.
- [ ] **Theorem 2.5.13**: The plane graph Gn is a 2-connected graph having at least ⌊n/2⌋ distinct zonal planar embeddings and at least n − 1 distinct non-zonal planar em- beddings. 47 Chapter 3 Graphs of Small Cycle Rank I...
- [x] **Theorem 3.1.1**: A unicyclic graph G is zonal if and only if G ̸= C ⋆ K2 for any cycle C.
- [x] **Corollary 3.1.2**: For each cycle C and each integer i ∈ {0, 1, 2}, there is a label- ing ℓ : V (C) → {1, 2} of C such that P(ℓ, C) = i in Z3. We are now prepared to verify the following result. 49
- [x] **Theorem 3.1.3**: Every zonal unicyclic graph is absolutely zonal.
- [x] **Theorem 3.2.1**: Let G be a plane graph of cycle rank 2 and type (1). Then G is zonal if and only if G is not minimal.
- [x] **Corollary 3.2.2**: Let G be a graph of cycle rank 2 and type (1). If G is minimal, then G is not zonal. Otherwise, G is absolutely zonal. 53
- [x] **Theorem 3.2.3**: Let G be a plane graph of cycle rank 2 and type (2). Then G is zonal if and only if either every vertex of G belongs to a cycle of G or at least two vertices of G belong to no cycle of G.
- [x] **Corollary 3.2.4**: Let G be a graph of cycle rank 2 and type (2). If G has exactly one vertex that does not lie on a cycle, then G is not zonal. Otherwise, G is absolutely zonal.
- [x] **Theorem 3.2.5**: Let F be a minimal plane graph of cycle rank 2 and type (3), and let G be a plane graph of cycle rank 2 and type (3) containing F as a subgraph. Then, G is zonal if and only if there is no region R...
- [x] **Corollary 3.2.6**: Let F be a minimal graph of cycle rank 2 and type (3), and let G be a graph of cycle rank 2 and type (3) containing F as a subgraph. If G is minimal and contains a triangle, then G is not zonal. Ot...
- [ ] **Proposition 3.3.1**: There are infinitely many 2-connected zonal graphs of cycle rank 3.
- [ ] **Lemma 2.0.4.**: Hence, there are infinitely many 2-connected zonal bipartite or non-bipartite graphs of cycle rank 3. Let H be a 2-connected bipartite graph of cycle rank 3. If all edges of H are subdivided a numb...
- [x] **Proposition 3.3.2**: Let H be a 2-connected bipartite graph of cycle rank 3. If all edges of H are subdivided a number of times of the same parity, then the resulting graph is zonal.
- [ ] **Proposition 3.3.3**: There are infinitely many 2-connected non-zonal graphs of cy- cle rank 3.
- [ ] **Theorem 4.1.1**: A connected cubic plane graph G is zonal if and only if G is bridgeless.
- [ ] **Theorem 4.1.2**: There exists a 4-coloring of the regions of a cubic map M if and only if M has a zonal labeling. Since it is known that there exists a 4-coloring of the regions of every plane graph (the Four Color...
- [ ] [ARTIFACT: proof/discussion prose about inner zonal labelings of bicubic maps, not a statement; rewrite against the dissertation if a theorem is wanted]
- [ ] [ARTIFACT: discussion prose posing a question about bicubic maps with few interior vertices, not a statement]
- [ ] [ARTIFACT: the sentence "The following result was established in [5] without the aid of the Four Color Theorem", a pointer rather than a statement]
- [ ] **Theorem 4.3.1**: [5] Let G be a bicubic map where the boundary of the exterior region is a Hamiltonian cycle C with k pairwise nonadjacent chords for some pos- itive integer k. There exists an inner zonal labeling ...
- [ ] [ARTIFACT: prose noting a corollary is independent of the Four Color Theorem, followed by the definition of a Hamiltonian path; not a statement]
- [ ] **Theorem 4.3.2**: [5] Every plane graph G with ∆(G) ≤ 3 where the boundary cycle of the exterior zone is a Hamiltonian cycle of G is inner zonal. Let G1 be the set of all bicubic maps having exactly one vertex inter...
- [x] **Lemma 4.3.3**: Let C be an n-cycle where n ≥ 2k for some integer k ≥ 2, and let X be a set of k pairwise nonadjacent edges of C. Then there exists a zonal labeling ℓ of C such that ℓ(x) = ℓ(y) for each edge xy ∈ X.
- [ ] **Theorem 4.3.5**: Every graph G ∈ G1 is inner zonal.
- [ ] **Theorem 4.3.6**: Let Ck be the collection of all cubic maps that have exactly k vertices interior to their exterior cycle, and further let C∗ k ⊂ Ck be the subset of all such graphs where the graph formed by deleti...
- [ ] **Theorem 4.3.8**: For 1 ≤ k ≤ 3, every graph G ∈ Gk is inner zonal.
- [ ] **Theorem 4.4.3**: If G is a connected cubic plane graph with bridges, then G is not zonal. A connected plane graph G is a nearly cubic plane graph if all vertices of G have degree 3 except for one vertex having degr...
- [ ] **Lemma 4.4.4**: Let G be a nearly cubic plane graph, and let R be a region having the vertex of degree 2 on its boundary. Then G does not have an inner zonal labeling where every region, with the possible exceptio...
- [x] **Theorem 4.4.5**: Every inner zonal cubic map is zonal.
- [x] **Corollary 4.4.6**: A cubic map is zonal if and only if it is inner zonal. Combining well-known results on graph colorings, results on zonal graphs, and
- [ ] [ARTIFACT: the phrase "we have the following"; the actual result is Theorem 2.5.13, already listed in this section]
- [ ] **Theorem 4.4.7**: The following seven statements are equivalent. 1. The Four Color Theorem: The regions of every plane graph can be colored with four or fewer colors so that every two regions with a common boundary ...



## 02_Bowling_Zhang_2023_Zonal_Graphs_Small_Cycle_Rank.pdf

- [ ] **Theorem 1.1.**: [3] A connected cubic plane graph G is zonal if and only if G is bridgeless.
- [ ] **Theorem 1.2.**: [3] There exists a 4-coloring of the regions of a cubic map M if and only if M has a zonal labeling. Since it is known that there exists a 4-coloring of the regions of every plane map (the Four Col...
- [x] **Theorem 1.4.**: [3] Every nontrivial tree and every cycle is zonal. The cycle rank of a connected graph of order n size m is the number m − n + 1. Thus, cycles have cycle rank 1. In general, the graphs of cycle ra...
- [x] **Lemma 2.2.**: Let X be a nonempty set of vertices of a graph. (1) For each i = 1, 2, there is a labeling ℓi : X → {1, 2} ⊆Z3 of X such that P(ℓi, X) = i in Z3. (2) If |X| ≥2, then there is a labeling ℓ0 : X → {1...
- [x] **Theorem 2.3.**: A unicyclic graph G is zonal if and only if G ̸= C ⋆ K2 for any cycle C.
- [x] **Proposition 2.4.**: Every planar embedding of a zonal graph of cycle rank 1 is zonal.
- [x] **Theorem 3.1.**: Let G be a graph of cycle rank 2 and type (1). Then G is zonal if and only if G is not minimal.
- [x] **Theorem 3.2.**: Let G be a graph of cycle rank 2 and type (2). Then G is zonal if and only if either every vertex of G belongs to a cycle of G or at least two vertices of G belong to no cycle of G.
- [x] **Theorem 3.3.**: Let G be a minimal graph of cycle rank2 and type (3) consisting of three internally disjoint u − v paths Pi of order ni for i = 1, 2, 3 where 2 ≤ n1 ≤ n2 ≤ n3 and n2 ≥ 3. Then G is zonal if and onl...
- [x] **Theorem 3.4.**: Let F be a minimal non-zonal graph of cycle rank 2 and type (3) and let G be a graph of cycle rank 2. If G contains F as a proper subgraph, then G is zonal. 7 www.ejgta.org Zonal graphs of small cy...
- [x] **Theorem 3.5.**: If F is a minimal zonal graph of cycle rank 2 and type (3), then F ⋆ K2 is zonal.
- [x] **Theorem 3.6.**: Let F be a minimal zonal graph of cycle rank 2 and type (3) and let G be a graph of cycle rank 2. If G contains F as a proper subgraph and G ̸= F ⋆ K2, then G is zonal.
- [ ] [ARTIFACT: an excerpt from the proof of Theorem 3.6, not a statement]
- [x] **Corollary 3.7.**: Let G be a graph of a cycle rank2 and type (3) containing three internally disjoint paths of order ni for i = 1, 2, 3 where 2 ≤ n1 ≤ n2 ≤ n3 and n2 ≥ 3. Then G is zonal if and only if G is not mini...
- [x] **Theorem 3.8.**: Let G be a graph of a cycle rank 2. (1) If G is of type (1), then G is zonal if and only if G is not minimal. (2) If G is of type (2), then G is zonal if and only if either every vertex of G belong...
- [ ] **Theorem 3.9.**: Let F be a minimal graph of cycle rank 2. (1) If F is of type (1), then every planar embedding of F ⋆ K2 is zonal. (2) If F is of type (2) such that at least one vertex of F belongs to no cycle in ...
- [x] **Proposition 4.1.**: Every 2-connected bipartite plane graph is zonal. We now present some observations on 2-connected graphs of cycle rank 3.
- [ ] **Proposition 4.2.**: There are infinitely many 2-connected zonal graphs of cycle rank 3.
- [x] **Proposition 4.3.**: Let H be a 2-connected bipartite graph of cycle rank 3. If all edges of H are subdivided a number of times of the same parity, then the resulting graph is zonal.
- [ ] **Proposition 4.4.**: There are infinitely many 2-connected non-zonal graphs of cycle rank 3.

## 03_Bowling_Zhang_2023_Zonal_Inner_Zonal_MaxDeg3.pdf

- [ ] **Theorem 1.1.**: The Four Color Conjecture is true if and only if the regions of every cubic map can be colored with four or fewer colors so that every two regions with a common boundary line are colored diﬀerently.
- [ ] [ARTIFACT: commentary that Theorem 1.1 reduces the Four Color Problem to cubic maps; the theorem itself is listed separately in this section]
- [ ] **Theorem 1.2.**: (Tait’s Theorem) The regions of a cubic map G can be colored with four or fewer colors so that every two adjacent regions are colored diﬀerently if and only if the chromatic index ofG is 3. Tait th...
- [ ] **Theorem 1.3.**: A cubic map M has chromatic index3 if and only ifM is zonal. By Theorems 1.1, 1.2, and 1.3, the Four Color Problem deals with (1) coloring the regions of a map or the vertices of a planar graph wit...
- [ ] **Theorem 2.1.**: Every inner zonal cubic map is zonal.
- [ ] **Corollary 2.1.**: A cubic map is zonal if and only if it is inner zonal. Since an inner zonal labeling is less restrictive than a zonal labeling, it may be less challenging to determine the existence of an inner zon...
- [ ] **Theorem 2.2.**: The following six statements are equivalent. 1. The Four Color Theorem: The regions of every plane graph can be colored with four or fewer colors so that every two regions with a common boundary ar...
- [ ] **Theorem 3.1.**: Every plane graph G with maximum degree ∆(G)≤ 3 where the boundary cycle of the exterior zone is a Hamiltonian cycle of G is inner zonal. There are nonzonal plane graphs that satisfy the conditions...
- [ ] [ARTIFACT: an excerpt from the proof following Theorem 3.1, not a statement]
- [ ] **Proposition 3.1.**: No nearly cubic plane graph is zonal. 133 A. Bowling and P. Zhang/ Discrete Math. Lett. 12 (2023) 130–137 134
- [ ] **Theorem 3.2.**: Every 2-connected nearly cubic plane graph is inner zonal.
- [x] **Theorem 3.3.**: Let H be a plane graph, letZ be a nonempty set of edges ofH and let G be the graph obtained by subdividing each edge inZ at least twice. Then (1) G is zonal if H is zonal and (2) G is inner zonal i...
- [ ] **Theorem 3.4.**: If G is a connected cubic plane graph with bridges, thenG is not zonal. By Theorem 3.4, no connected cubic plane graph with bridges is zonal. We also saw that the nearly cubic plane graph of Figure...
- [ ] **Theorem 3.5.**: If G is a connected cubic plane graph with bridges, thenG is not inner zonal.
- [ ] **Proposition 3.2.**: Let G be a nearly cubic plane graph. Ifℓ is an inner zonal labeling ofG, then there exists a regionR all of whose boundary vertices have degree3 such that ℓ(R)̸= 0.
- [ ] **Lemma 4.1.**: Let G be a plane graph. If there exist distinct regions R0, R1, . . . , Rk of G where the boundary Ri is Bi for 0≤ i≤ k such that{V (B1), V (B2), . . ., V (Bk)} form a partition ofV (B0)−{ v} for s...
- [ ] **Theorem 4.1.**: For each pairn, m of integers withn≥ 4 and n < m < 3n/2, there is a2-connected plane graph G of order n and size m with ∆(G) = 3 such that G is not zonal.
- [ ] **Conjecture 4.1.**: Every 2-connected plane graph with maximum degree3 is inner zonal.

## 04_Bowling_Zhang_2022_Absolutely_Conditionally_Zonal_Graphs.pdf

- [ ] **Theorem 1.1.**: A connected cubic plane graph G is zonal if and only if G is bridgeless. ∗Corresponding author (ping.zhang@wmich.edu).  A. Bowling and P. Zhang/ Electron. J. Math. 4 (2022) 1–11 2 Consequently, by ...
- [ ] **Theorem 1.2.**: If every cubic map is zonal, then the chromatic number of every planar graph is at most 4. Thus, if it could be shown that every cubic map is zonal without using the Four Color Theorem, then the Fo...
- [ ] **Theorem would**: follow. This shows that studying zonal labelings of planar graphs are of interest, especially cubic planar graphs, and cubic maps in particular. 2. Absolutely zonal graphs The following result was ...
- [ ] **Proposition 2.1.**: Every nontrivial tree and every cycle is zonal. Since there is only one planar embedding of a nontrivial tree or a cycle, it follows that every nontrivial tree and every cycle is absolutely zonal. ...
- [x] **Proposition 2.2.**: Every 2-connected bipartite planar graph is absolutely zonal.
- [ ] **Theorem 2.1.**: (Whitney’s Theorem) Every 3-connected planar graph is uniquely embeddable in the plane. As a consequence of Theorem 2.1, every 3-connected planar graph is either absolutely zonal or non-zonal. Ever...
- [ ] **Theorem 2.2.**: For an integer n≥ 3, the wheel Wn =Cn∨K1 is zonal if and only if n≡ 0 (mod 3) .
- [ ] **Theorem 2.3.**: For every positive integerk, there exists a connected bridgeless cubic planar graph having at least k distinct (zonal) planar embeddings. 2 A. Bowling and P. Zhang/ Electron. J. Math. 4 (2022) 1–11...
- [x] **Proposition 3.1.**: For every multiset S of two cycles, the Dutch windmill graph D(S) is not zonal.
- [ ] **Lemma 3.1.**: LetX be a nonempty set of vertices of a graph. (1) For eachi = 1, 2, there is a labeling ℓi :X→{ 1, 2}⊆ Z3 ofX such that∑(ℓi,X ) =i in Z3. (2) If|X|≥ 2, then there is a labeling ℓ0 :X→{ 1, 2}⊆ Z3 o...
- [x] **Theorem 3.1.**: For every multiset S of three or more cycles, the Dutch windmill graph D(S) is conditionally zonal. 4 A. Bowling and P. Zhang/ Electron. J. Math. 4 (2022) 1–11 5
- [ ] **Lemma 4.1.**: LetS be a set with 4k elements for some positive integer k. The number of partitions of S into four k-element subsets is 4∏ i=1 (ik− 1 k− 1 ) = (4k− 1 k− 1 )(3k− 1 k− 1 )(2k− 1 k− 1 ) . (1) 7 A. Bo...
- [x] **Theorem 4.1.**: There is an irregular Dutch windmill graph that has an arbitrarily large number of distinct zonal planar embeddings.
- [ ] **Proposition 5.1.**: For a positive integer k, the plane graph Fk is zonal.
- [ ] **Theorem 5.1.**: There is a regular Dutch windmill graph that has an arbitrarily large number of distinct zonal planar embeddings.
- [ ] **Proposition 5.2.**: Letk be a positive integer . ⋆ Ifµ(k)≡ 1 (mod 3), then the zonal Dutch windmill graph Dµ(k) 3 is conditionally zonal and has at least k distinct zonal planar embeddings. ⋆ Ifµ(k)≡ 2 (mod 3), then t...

## 05_Barrientos_Minion_2024_Zonal_Labeling_of_Graphs.pdf

- [x] **Proposition 1.1.**: IfT is a nontrivial tree, then T is zonal. The proof of this result, given in [1], is very informative, that is the reason why we sketch it here. Suppose that T is a tree of order n. A plane repres...
- [x] **Proposition 1.2.**: IfC is a cycle, then C is zonal. As we did before, we do not prove this result, but provide a sketch of a procedure used to obtain a zonal labeling of Cn+1 if a zonal labeling of Cn is known. The f...
- [ ] **Proposition 1.3.**: The prismDn =Cn×P2 is zonal. After this result, Chartrand et al. [1] characterized the family of connected zonal cubic graphs.
- [ ] **Theorem 1.1.**: A connected cubic plane graph G is zonal if and only if G is bridgeless. Motivated by these results, Chartrand et al. [1] posed the following question: 95 www.ijc.or.id Zonal labeling of graphs | C...
- [ ] **Proposition 2.1.**: IfG is a 2-connected bipartite graph with both stable sets of cardinality n, then G is zonal.
- [x] **Lemma 2.1.**: IfG is a unicyclic graph of order n and girthn− 1, thenG is not zonal.
- [x] **Proposition 2.2.**: A unicyclic graph of order n and girthg is zonal if and only if n−g̸= 1.
- [ ] **Proposition 1.1.**: Thus, the sum of the labels of all these vertices is 0 in Z3; consequently, the label of the exterior zone is 0 in Z3, which implies that the labeling ofG is zonal. In Figure 2 we show an example o...
- [x] **Proposition 2.3.**: Every triangulation is zonal. Every near-triangulation is inner zonal.
- [x] **Proposition 2.4.**: If any edge of a zonal graph G is subdivided an even number of times, then the resulting graph is zonal.
- [ ] **Theorem 3.1.**: Every plane graphG with ∆(G)≤ 3 where the boundary cycle of the exterior zone is a Hamiltonian cycle of G is inner zonal. Thus, we need to study the existence of a zonal labeling for all outerplana...
- [ ] **Proposition 3.1.**: Let G be an outerplanar graph of order n and size m = n + 1. If G has an interior zone with boundary C3, thenG is not zonal.
- [x] **Proposition 3.2.**: IfG1 andG2 are cycles other than C3, then the edge amalgamation of G1 and G2 is zonal.
- [ ] **Proposition 3.3.**: F ori∈{ 1, 2}, let Gi be a zonal graph. If there exists a zonal labeling of each Gi, that assigns the labels 1 and 2 on the vertices that form the boundary of the exterior zone, then there is an ed...
- [ ] **Proposition 3.4.**: Let G be an outerplanar graph of order n with χ− 2 chords such that the subgraph induced by v1,v 2,...,v χ is a near-triangulation. The graph G is zonal if and only if χ≡ 2(mod 3).
- [ ] **Proposition 3.5.**: F or eachi∈{ 1, 2}, letGi be an outerplanar graph of order ni and size 2ni− 3, and ei = uivi be any edge on the boundary of the exterior zone of Gi. The outerplanar graph G, obtained from G1 and G2...
- [ ] **Proposition 3.6.**: Any outerplanar graph that contains M1,M2, orM3, as an induced subgraph, is neither zonal nor inner zonal. In Figure 6 we show all outerplanar graphs of order 9 that are neither zonal nor inner zon...
- [ ] **Proposition 4.1.**: IfT is any tree, then T×P2 is zonal.
- [ ] **Proposition 4.2.**: IfG is a zonal outerplanar graph, then G×P2 is zonal.
- [ ] **Proposition 4.3.**: IfG is a unicyclic graph, then G×P2 is zonal. As we mentioned in the introduction, the prism Dn =Cn×P2 is zonal. This graph ﬁts in the category of cubic graphs studied in [1]. The technique used to...
- [ ] **Proposition 4.4.**: The graphCn×Pm is zonal for every m≥ 2. 106 www.ijc.or.id Zonal labeling of graphs | C. Barrientos and S. Minion
- [ ] **Proposition 5.1.**: The number of zonal labelings of the cycle Cn is z(n) = ∑ r∈R T (n,r ). In Table 3 we show the values ofz(n), for 3≤n≤ 32. n z(n) n z(n) n z(n) n z(n) n z(n) 3 2 9 16 15 410 21 16,992 27 831,256 4 ...

## 06_Bowling_2025_Zonal_Cozonal_Abelian_Groups.pdf

- [ ] **Theorem 1.1.**: Let M be a cubic map. Then M has a proper edge 3-coloring if and only if M admits a zonal labeling. In 1880, Peter Tait proved that a cubic map has a proper edge 3-coloring if and only if it has a ...
- [ ] **Theorem 1.2.**: Let M be a cubic map. Then M has a proper region 4-coloring if and only if M admits a zonal labeling. In 1976 it was proven that every plane graph admits a proper region 4-coloring, resulting in th...
- [ ] **Theorem would**: constitute a new proof of the Four Color Theorem. In order to gain a new perspective on zonal labelings, cozonal labelings were introduced in [2]. Based on the denition of cozonal labelings, there...
- [x] **Proposition 1.3.**: A connected plane graph G is zonal if and only if its plane dual G∗ is cozonal. Therefore, there is a nice dualization of Theorem 1.1. A plane triangulation is a plane graph where the boundary of e...
- [ ] **Theorem 1.4.**: Let T be a plane triangualtion. Then T has a tricoloring if and only if T admits a cozonal labeling. While the choice of the group Z3 for our labels is deeply connected with the study of the Four C...
- [x] **Lemma 2.3.**: Let Γ ̸≃ Z2 be an abelian group. Then Γ contains three nonzero elements g1, g2, g3 (not necessarily distinct) such that g1 + g2 + g3 = 0.
- [x] **Proposition 2.4.**: Let Cn be a cycle with n ≥ 3, and let Γ be an abelian group. Then Cn has a Γ-zonal labeling in all cases except when Γ ≃ Z2 and n is odd.
- [ ] **Proposition 2.5.**: Let Γ ̸≃ Z2 be an abelian group, and let n ≥ 4 be even. Then Wn has a Γ-zonal labeling if and only if Γ has an element g of order k ≥ 2 such that k divides n/2. zonal labelings with abelian groups ...
- [ ] **Proposition 2.6.**: Let Γ ̸≃ Z2 be an abelian group, and let n ≥ 3 be odd. Then Wn has a Γ-zonal labeling if and only if Γ has an element g of order k ≥ 3 such that k divides n.
- [ ] **Proposition 2.7.**: Let Γ be an abelian group. If G is a 2-connected bipartite plane graph, then G is Γ-zonal. Dually, if G is a 2-connected Eulerian plane graph, then G is Γ-cozonal. 88 a. bowling
- [ ] **Proposition 2.8.**: Let Γ ̸≃ Z2 be an abelian group. If G is an Eulerian plane triangulation, then G is Γ-zonal. Dually, if G is a bipartite cubic map, then G is Γ-cozonal.
- [ ] **Theorem 3.2.**: Let Cn be a cycle for n ≥ 3, and let Γ ̸≃ Z2 be an abelian group. If Γ is generated by at most n − 1 elements, then Cn is generative Γ-zonal.
- [ ] **Theorem 3.4.**: Let Γ be an abelian group, and let n ≥ 3 be odd. Then Wn is generative Γ-zonal if and only if Γ ≃ Zk, where k divides n.
- [ ] **Corollary 3.5.**: Let n ≥ 3 be prime. Then Wn is generative Γ-zonal if and only if Γ ≃ Zn. Thus, there are a nite number of groups (up to isomorphism) for which a given odd wheel is generative Γ-zonal. The case for...
- [ ] **Theorem 3.6.**: Let Γ be an abelian group, and let n ≥ 4 be even. Then Wn is generative Γ- zonal if and only if Γ can be generated by two nonzero elements g1, g2 such that g1 + g2 ̸= 0 and the order of g1 + g2 div...
- [ ] **Corollary 3.7.**: Let n ≥ 4 be even, and let k ≥ 1 be an integer. Then Wn is generative Zkn/2-zonal in all cases except for when n = 4 and k = 1.
- [ ] **Proposition 4.1.**: Let G be a plane triangulation or inner triangulation, let B be the boundary of the exterior region, and let ℓ∗ be an inner Z3-cozonal labeling of G. Then X v∈V (B) ℓ∗(v) = 0.
- [ ] **Proposition 4.2.**: Let G be a 2-connected plane triangulation or inner triangulation, let G have a Z3-cozonal or inner Z3-cozonal labeling ℓ∗, and let e, e′ ∈ E(G). Let W1, W2 be two walks (u0, e0 = e, u1, ..., en−1 ...
- [ ] **Lemma 4.3.**: Let G be a 2-connected plane graph, let B be the boundary of the exterior region, and let ℓ∗ be a strong inner Γ-cozonal labeling of G. Then X v∈V (B) ℓ∗(v) = 0.
- [ ] **Lemma 4.4.**: Let G be a 2-connected plane graph, let G have a strong Γ-cozonal or inner Γ-cozonal labeling ℓ∗, and let e, e′ ∈ E(G). Let W1, W2 be two walks (u0, e0 = e, u1, ..., en−1 = e′, un) and (v0, f0 = e,...
- [ ] **Theorem 4.5.**: Let G be 2-connected, and let Γ be an abelian group. Then there exists a proper vertex cyclic edge coloring f : E(G) → Γ if and only if G admits a strong Γ-zonal labeling. Dually, there exists a pr...
- [ ] **Theorem 4.8.**: Let n >3. Then the wheel Wn does not have a strong Γ-zonal labeling for any abelian group Γ.
- [ ] **Theorem 4.9.**: Let G be a 3-connected plane graph having no vertices of degree 3 or 5, and let G be strong Γ-zonal for some abelian group Γ. Then Γ must contain a subgroup isomorphic to Z4 ⊕ Z4.
- [ ] **Theorem 4.10.**: Let Γ be an abelian group. Then there exists a 3-connected plane graph G which is strong Γ-zonal if and only if Γ contains a subgroup isomorphic to either Z3, Z4 ⊕ Z4, or Z5.
- [ ] **Corollary 4.11.**: Let Γ be an abelian group. Then there exists a 3-connected plane graph G which is strong Γ-cozonal if and only if Γ contains a subgroup isomorphic to either Z3, Z4 ⊕ Z4, or Z5. 5. Further remarks T...
- [ ] **Proposition 5.3.**: Let Cn be a cycle with n ≥ 3, and let Γ be an abelian group. 1. Cn is generative strong Γ-cozonal if and only if Γ ≃ Zn. 2. Cn is generative strong Γ-zonal if and only if Γ ≃ Lk i=1 Z2 for some k, ...

## 07_Chartrand_Egan_Zhang_2023_Zonal_Graphs_Revisited.pdf

- [ ] **The Four Color Theorem (graph form)**: The chromatic number of every planar graph is at most 4. [RECOVERED: the original entry began mid-sentence at "...in terms of graphs is the following"; equivalent to 4CT and so out of reach here]
- [ ] **Proposition 2.2.**: Every nontrivial tree and every cycle is zonal. The zonal labelings of the graphs of Figure 1 illustrate the following obser- vation. Observation 2.3. Let H be the boundary of a region R in a plane...
- [ ] **Theorem 3.1.**: For every proper edge coloring of a cycle C with the col- ors 1, 2, 3, the resulting types of the vertices of C produce a zonal labeling of C.
- [ ] **Theorem 3.2.**: For each zonal labeling ℓ of a cycle C, there is a proper edge coloring of C with the colors 1, 2, 3 such that the resulting type of each vertex v of C is ℓ(v).
- [ ] **Theorem 4.1.**: A connected cubic plane graph G is zonal if and only if G is bridgeless. By Theorem 4.1, all cubic maps are absolutely zonal. Clearly, every cubic map has even order. The cubic maps of order 6 or l...
- [ ] **Theorem 4.2.**: For every two even integers r and n such that n≥ 10 and 2≤ r≤ n− 2, there exists a cubic map M of order n with a zonal labeling and an r-element subset Sr of V (G) such that if the labels of all ve...
- [ ] **Lemma 4.3.**: No set of three vertices in a cubic map M lie on three different boundary cycles of M.
- [ ] **Proposition 4.4.**: For any zonal labeling of a cubic map M, the label- ing obtained by replacing the labels of exactly three vertices of M by their complementary labels is not a zonal labeling of M.
- [ ] **Conjecture 4.5.**: For any zonal labeling of a cubic map M and any odd positive integer r, the labeling obtained by replacing the labels of exactly r vertices of M by their complementary labels is not a zonal labelin...
- [ ] **Theorem 5.1.**: The vertex types of every proper edge coloring of a cubic map M with the colors 1, 2, 3 produce a zonal labeling of M.
- [ ] **Lemma 5.2.**: Let G be a cubic map with a zonal labeling ℓ. For a cycle C of G, let S ={v∈ V (C) : G contains an edge incident with v lying outside of C} T ={v∈ V (C) : G contains an edge incident with v lying i...
- [ ] **Theorem 5.3.**: Let G be a cubic map with a zonal labeling ℓ and let C be a cycle of G. If an edge of C is assigned a color from {1, 2, 3} in Z3, then there is a unique proper edge coloring of C with the colors 1,...
- [ ] **Theorem 5.4.**: Let G be a cubic map with a zonal labeling ℓ. If an edge of G is assigned a color from Z3 ={1, 2, 3}, then there is a unique proper edge coloring of G with the colors 1, 2, 3 such that the type of ...
- [ ] **Theorem 5.3.**: Hence, we may assume that P does not lie on a cycle in G. Since G is a cubic map, it follows that there is a sequenceP (1), P (2), . . . , P(t) of subpaths of P (proceeding from e to f ) such that ...
- [ ] [ARTIFACT: the phrase "gives us the following result"; the actual result is Corollary 5.5, listed separately]
- [ ] **Corollary 5.5.**: Every zonal cubic map has a proper edge coloring with three colors. 6 In closing Cubic maps have been encountered in the study of graph theory as far back as the 19th century. In 1884, Tait made a ...
- [ ] **Theorem 6.1.**: There is a proper edge coloring of every cubic map with three colors if and only if there is a proper edge coloring of every3-connected cubic planar graph. Therefore, if Tait’s Conjecture had been ...