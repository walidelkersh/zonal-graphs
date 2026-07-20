# Zonal Graphs Formalization

This repository contains the formalization of Zonal Labelings, Inner Zonal Labelings, and Zonal Graphs in [Lean 4](https://lean-lang.org/). It is built on top of [mathlib4](https://github.com/leanprover-community/mathlib4).

## Mathematical Background

In graph theory, a **zonal labeling** is a vertex labeling of a connected plane graph $G$ using the non-zero elements of the ring $\mathbb{Z}_3$ (the integers modulo 3), such that the sum of the labels on the boundary of every region of $G$ is the zero element of $\mathbb{Z}_3$. A graph possessing such a labeling is called a **zonal graph**. 

A closely related concept is an **inner zonal labeling**, which restricts this requirement to the interior regions of the plane graph. 

The existence of zonal and inner zonal labelings on planar graphs is deeply connected to the famous **Four Color Theorem**.

This repository aims to:
1. Formalize the definitions of Zonal and Inner Zonal Labelings.
2. Prove recent theorems on the structure of zonal graphs and cycle ranks.
3. Establish the formal connection between inner zonal graphs and the Four Color Theorem.

### References
* Bowling, A. (2023). *Zonality in Graphs* (Dissertation). Western Michigan University.
* Egan, C. (2014). *Zonality in Graphs* (Dissertation).
* Bowling, A., & Zhang, P. (2023). *Zonal Graphs of Small Cycle Rank*.
* Bowling, A., & Zhang, P. (2023). *Zonal and Inner Zonal Graphs of Maximum Degree 3*.
* Bowling, A., & Zhang, P. (2022). *Absolutely and Conditionally Zonal Graphs*.
* Barrientos, C., & Minion, S. (2024). *Zonal Labeling of Graphs*.
* Bowling, A. (2025). *Zonal and Cozonal Labelings over Abelian Groups*.
* Chartrand, G., Egan, C., & Zhang, P. (2019). *Zonal Graphs Revisited*.

## Structure

The Lean definitions and proofs are located in the `ZonalGraphs/` directory.

* `Basic.lean`: Foundational imports and combinatorial definitions.
* `Definitions.lean`: Formal definitions of zonal labelings over plane graphs.

## Building

This project uses `lake`. To build the project locally, run:

```bash
lake exe cache get # Download mathlib pre-compiled cache
lake build
```
