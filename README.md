# Zonal Graphs Formalization

[![Build Project](https://github.com/walidelkersh/zonal-graphs/actions/workflows/build.yml/badge.svg)](https://github.com/walidelkersh/zonal-graphs/actions/workflows/build.yml)

A comprehensive formalization of Zonal Labelings, Inner Zonal Labelings, and Zonal Graphs in [Lean 4](https://lean-lang.org/), built entirely on top of [mathlib4](https://github.com/leanprover-community/mathlib4).

## Goals & Workflow

Our primary goal is to formalize the entire corpus of recent literature on Zonal Graphs. We have systematically extracted **264 mathematical statements** (Definitions, Theorems, Lemmas, Propositions, and Conjectures) across 7 major papers in the field. 

Our progress is rigorously tracked in the [Master Formalization To-Do List](todo.md). The formalization follows a strict workflow:
1. Targeted statements are drawn chronologically from `todo.md`.
2. Existing `mathlib` components are leveraged to prevent wheel-reinventing (e.g., using native `IsRegularOfDegree` and `IsBridge`).
3. Completed formalizations are merged and checked off the master list.

## Mathematical Background

In graph theory, a **zonal labeling** is a vertex labeling of a connected plane graph $G$ using the non-zero elements of the ring $\mathbb{Z}_3$ (the integers modulo 3), such that the sum of the labels on the boundary of every region of $G$ is the zero element of $\mathbb{Z}_3$. A graph possessing such a labeling is called a **zonal graph**. 

A closely related concept is an **inner zonal labeling**, which restricts this requirement to the interior regions of the plane graph. The existence of zonal and inner zonal labelings on planar graphs is deeply connected to the famous **Four Color Theorem**.

## Structure

The project root contains `todo.md`, the master tracker for all unproven and proven theorems. The Lean definitions and proofs are located in the `ZonalGraphs/` directory:

* `Basic.lean`: Foundational imports and combinatorial definitions.
* `Definitions.lean`: Formal definitions of zonal labelings over plane graphs (`IsZonalLabeling`, `IsInnerZonalLabeling`, etc).
* `FourColor.lean`: The structural equivalence connecting zonal labelings of cubic maps to the 4CT.
* `TreesAndCycles.lean`: Formalizations of foundational zonal properties (e.g., all nontrivial trees and cycles are zonal).

## Building

This project is managed with `lake`. To build the project locally, run:

```bash
lake exe cache get # Download mathlib pre-compiled cache
lake build
```

## References

The theorems tracked in `todo.md` and formalized in this repository are sourced from the following literature:
* Bowling, A. (2023). *Zonality in Graphs* (Dissertation). Western Michigan University.
* Egan, C. (2014). *Zonality in Graphs* (Dissertation).
* Bowling, A., & Zhang, P. (2023). *Zonal Graphs of Small Cycle Rank*.
* Bowling, A., & Zhang, P. (2023). *Zonal and Inner Zonal Graphs of Maximum Degree 3*.
* Bowling, A., & Zhang, P. (2022). *Absolutely and Conditionally Zonal Graphs*.
* Barrientos, C., & Minion, S. (2024). *Zonal Labeling of Graphs*.
* Bowling, A. (2025). *Zonal and Cozonal Labelings over Abelian Groups*.
* Chartrand, G., Egan, C., & Zhang, P. (2019). *Zonal Graphs Revisited*.
