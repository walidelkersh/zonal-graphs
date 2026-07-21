import ZonalGraphs.Definitions
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Tactic

namespace ZonalGraphs

/-!
# Trees and cycles are zonal

This file realizes Mathlib trees and cycle graphs as `PlaneGraph`s with their standard planar
embeddings.  A tree has one face, whose boundary-vertex set contains every vertex.  A cycle has
two faces (interior and exterior), both with the full vertex set as boundary.

Because `PlaneGraph` is an interface containing face data rather than a certified topological
embedding, the theorems below concern these canonical realizations.  An arbitrary `PlaneGraph`
whose underlying graph is a tree need not have valid tree face data.
-/

universe u

open scoped Classical

/-- Every finite type other than a singleton can be labeled by nonzero elements of `ZMod 3`
so that the sum of all labels is zero. -/
lemma exists_zonalLabeling_sum_univ_zero (Vertex : Type u) [Fintype Vertex]
    [Nonempty Vertex] (hcard : Fintype.card Vertex ≠ 1) :
    ∃ labeling : VertexLabeling Vertex,
      ∑ v : Vertex, (labeling v : ZMod 3) = 0 := by
  by_contra! h'
  simp_all
  -- We'll use induction on the number of vertices to show that there exists a labeling such that the sum of the labels is zero.
  have h_ind : ∀ (n : ℕ), n ≥ 2 → ∃ labeling : Fin n → ZonalLabel, ∑ i, (labeling i : ZMod 3) = 0 := by
    intro n hn; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all ;
    by_cases hn : n ≥ 2;
    · obtain ⟨labeling, hlabeling⟩ := ih n (by linarith) hn
      use Fin.cons (⟨1, by decide⟩ : ZonalLabel)
        (Fin.cons (⟨2, by decide⟩ : ZonalLabel) labeling)
      simp_all [Fin.sum_univ_succ]
      decide
    · interval_cases n <;> native_decide
  -- Apply the induction hypothesis to the cardinality of the vertex set.
  obtain ⟨labeling, hlabeling⟩ : ∃ labeling : Fin (Fintype.card Vertex) → ZonalLabel, ∑ i, (labeling i : ZMod 3) = 0 := h_ind (Fintype.card Vertex) (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt (Fintype.card_pos)) (Ne.symm hcard));
  -- Use the equivalence between `Vertex` and `Fin (Fintype.card Vertex)` to transfer the labeling.
  let equiv := Fintype.equivFin Vertex
  exact h' (fun v => labeling (equiv v))
    (by simpa only [← Equiv.sum_comp equiv fun v => (labeling v : ZMod 3)] using hlabeling)

namespace PlaneGraph

/-- The standard one-face plane realization of a finite tree. -/
noncomputable def ofTree {Vertex : Type u} [Fintype Vertex]
    (G : SimpleGraph Vertex) (hG : G.IsTree) : PlaneGraph Vertex PUnit where
  graph := G
  connected := hG.isConnected
  boundary := fun _ => Finset.univ
  boundaryEdges := fun _ => G.edgeFinset
  exterior := PUnit.unit

/-- **Theorem 2.0.1.** Every nontrivial finite tree, in its standard plane realization, is
zonal. -/
theorem every_nontrivial_tree_is_zonal {Vertex : Type u} [Fintype Vertex] [Nontrivial Vertex]
    (G : SimpleGraph Vertex) (hG : G.IsTree) : (ofTree G hG).IsZonal := by
  obtain ⟨f, hf⟩ := exists_zonalLabeling_sum_univ_zero Vertex (by
    exact ne_of_gt Fintype.one_lt_card)
  use f
  intro R
  fin_cases R
  aesop

/-- The standard two-face plane realization of the cycle graph on `n` vertices. -/
noncomputable def ofCycle (n : ℕ) (hn : 3 ≤ n) : PlaneGraph (Fin n) (Fin 2) where
  graph := SimpleGraph.cycleGraph n
  connected := by
    rw [show n = (n - 1) + 1 by omega]
    exact SimpleGraph.cycleGraph_connected
  boundary := fun _ => Finset.univ
  boundaryEdges := fun _ => (SimpleGraph.cycleGraph n).edgeFinset
  exterior := 0

/-- **Theorem 2.0.2.** Every cycle (of length at least three), in its standard plane
realization, is zonal. -/
theorem every_cycle_is_zonal (n : ℕ) (hn : 3 ≤ n) : (ofCycle n hn).IsZonal := by
  obtain ⟨labeling, hlabeling⟩ : ∃ labeling : Fin n → ZonalLabel, ∑ i, (labeling i : ZMod 3) = 0 := by
    convert exists_zonalLabeling_sum_univ_zero (Fin n) _
    · exact ⟨⟨0, by linarith⟩⟩
    · aesop
  use labeling
  intro R
  fin_cases R <;> simp_all [ofCycle]
  · exact hlabeling;
  · exact hlabeling

end PlaneGraph
end ZonalGraphs