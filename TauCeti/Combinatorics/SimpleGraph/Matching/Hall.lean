/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Matching.Konig

import TauCeti.Combinatorics.SimpleGraph.Bipartite
import TauCeti.Combinatorics.SimpleGraph.Finite

/-!
# The Kőnig–Ore deficiency formula and Hall's theorem for simple graphs

This file derives the Kőnig–Ore deficiency formula and the biconditional finite forms of Hall's
marriage theorem for bipartite simple graphs from Kőnig's theorem
(`TauCeti.Combinatorics.SimpleGraph.Matching.Konig`).

Let `G : SimpleGraph V` satisfy `G.IsBipartiteWith L R`. Every matching `M : G.Subgraph` and
every subset `S ⊆ L` satisfy the Kőnig–Ore inequality

`M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard`

with no finiteness assumptions. Equality in `ℕ∞` is always attained by some matching `M` and
subset `S ⊆ L` (`SimpleGraph.IsBipartiteWith.exists_isMatching_encard_add_encard_eq`); when `L`
is finite (without requiring `G` to be locally finite or `G.edgeSet` to be finite), the witness
`S` automatically has finite neighbourhood, giving the `Set.ncard` witness equality and the
biconditional Hall theorem in `ℕ∞`. When `G.edgeSet` is also finite, every neighbourhood is
finite, giving the `Set.ncard` deficiency formula
`L.ncard - ⨆ S ⊆ L, (S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard)` and the biconditional `Set.ncard`
Hall theorems.

Mathlib's `SimpleGraph.exists_isMatching_of_forall_ncard_le` and
`SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le` remain the library's general Hall
interfaces (covering locally finite infinite graphs as well); the closing examples verify that
the finite specializations agree with the extremal development here.

## Main definitions

* `SimpleGraph.Subgraph.IsMatching.vertsInterEquivEdgeSet`: the canonical equivalence between
  `M.verts ∩ L` and `M.edgeSet` for a matching `M` of a bipartite simple graph.

## Main results

* `SimpleGraph.IsBipartiteWith.isVertexCover_sdiff_union_biUnion_neighborSet`: for any `S`,
  `(L \ S) ∪ ⋃ x ∈ S, G.neighborSet x` is a vertex cover of `G`.
* `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_eq_encard_verts_inter`: in a bipartite graph
  with sides `L` and `R`, `M.edgeSet.encard = (M.verts ∩ L).encard` for every matching `M`.
* `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_add_encard_le` and
  `SimpleGraph.Subgraph.IsMatching.ncard_edgeSet_add_ncard_le`: the **Kőnig–Ore inequality**.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_encard_add_encard_eq` and
  `SimpleGraph.IsBipartiteWith.exists_isMatching_ncard_add_ncard_eq`: the **Kőnig–Ore formula**
  in witness form.
* `SimpleGraph.IsBipartiteWith.matchingNum_eq_sub_iSup_encard`,
  `SimpleGraph.IsBipartiteWith.isGreatest_ncard_isMatching`, and
  `SimpleGraph.IsBipartiteWith.matchingNum_eq_sub_iSup`: the **numerical deficiency formulas**.
* `SimpleGraph.IsBipartiteWith.exists_isMatching_subset_verts_iff_encard`,
  `SimpleGraph.IsBipartiteWith.exists_isMatching_subset_verts_iff`, and
  `SimpleGraph.IsBipartiteWith.exists_isPerfectMatching_iff`: **Hall's marriage theorem** as an
  equivalence for bipartite simple graphs with finite side(s).

## Implementation notes

Weak duality follows by applying matching–cover weak duality to the vertex cover
`(L \ S) ∪ ⋃ x ∈ S, G.neighborSet x`. Attainment takes a matching `M` and vertex cover `C` of
equal cardinality in `ℕ∞` from Kőnig's theorem
(`SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_encard_eq`) and sets `S := L \ C`, whose
neighbours all lie in `C ∩ R` and are therefore disjoint from `L ∩ C`. Exchanging the sides via
`SimpleGraph.IsBipartiteWith.symm` yields the symmetric forms on `R`.

## References

* P. Hall, *On representatives of subsets*, J. London Math. Soc. 10 (1935).
* Ø. Ore, *Graphs and matching theorems*, Duke Math. J. 22 (1955).
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 2.1.
-/

public section

open Function Set

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {L R : Set V}

/-! ### Bipartite vertex-cover and matching-size lemmas -/

namespace IsBipartiteWith

/-- The left side of a bipartition is a vertex cover. -/
theorem isVertexCover_left (h : G.IsBipartiteWith L R) : G.IsVertexCover L :=
  fun _ _ hadj ↦ (h.mem_of_adj hadj).imp And.left And.right

/-- The right side of a bipartition is a vertex cover. -/
theorem isVertexCover_right (h : G.IsBipartiteWith L R) : G.IsVertexCover R :=
  h.symm.isVertexCover_left

/-- The matching number is at most the size of the left side of a bipartition. -/
theorem matchingNum_le_encard_left (h : G.IsBipartiteWith L R) : G.matchingNum ≤ L.encard :=
  G.matchingNum_le_vertexCoverNum.trans h.isVertexCover_left.vertexCoverNum_le

/-- For any vertex set `S`, the vertices of `L` outside `S` together with the neighbours of `S`
form a vertex cover of `G`. -/
theorem isVertexCover_sdiff_union_biUnion_neighborSet (h : G.IsBipartiteWith L R) (S : Set V) :
    G.IsVertexCover ((L \ S) ∪ ⋃ x ∈ S, G.neighborSet x) := by
  intro u v huv
  rcases h.mem_of_adj huv with ⟨huL, _⟩ | ⟨_, hvL⟩
  · by_cases huS : u ∈ S
    · exact Or.inr <| Or.inr <| mem_biUnion huS huv
    · exact Or.inl <| Or.inl ⟨huL, huS⟩
  · by_cases hvS : v ∈ S
    · exact Or.inl <| Or.inr <| mem_biUnion hvS huv.symm
    · exact Or.inr <| Or.inl ⟨hvL, hvS⟩

end IsBipartiteWith

namespace Subgraph.IsMatching

variable {M : G.Subgraph}

/-- **Hall's necessary condition.** Any set of vertices saturated by a matching has at least as
many neighbours in `G` as elements, measured in `ℕ∞`. -/
theorem encard_le_encard_biUnion_neighborSet (hM : M.IsMatching) {S : Set V} (hS : S ⊆ M.verts) :
    S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard := by
  let f : S → (⋃ x ∈ S, G.neighborSet x : Set V) := fun x ↦
    ⟨(hM (hS x.2)).choose, mem_biUnion x.2 (M.adj_sub (hM (hS x.2)).choose_spec.1)⟩
  refine Function.Embedding.encard_le ⟨f, fun x y hxy ↦ Subtype.ext ?_⟩
  have hxw : M.Adj x.1 (f x).1 := (hM (hS x.2)).choose_spec.1
  have hyw : M.Adj y.1 (f y).1 := (hM (hS y.2)).choose_spec.1
  exact hM.eq_of_adj_right hxw (congrArg Subtype.val hxy ▸ hyw)

/-- Hall's necessary condition in `ℕ` when the neighbourhood of `S` is finite. -/
theorem ncard_le_ncard_biUnion_neighborSet (hM : M.IsMatching) {S : Set V} (hS : S ⊆ M.verts)
    (hNf : (⋃ x ∈ S, G.neighborSet x).Finite) :
    S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard :=
  ENat.natCast_le_natCast.1 <| (Set.ncard_le_encard S).trans <|
    (hM.encard_le_encard_biUnion_neighborSet hS).trans_eq hNf.cast_ncard_eq.symm

/-- Canonical equivalence pairing each vertex of `M` in `L` with its incident edge in `M`. -/
noncomputable def vertsInterEquivEdgeSet (hM : M.IsMatching) (h : G.IsBipartiteWith L R) :
    (M.verts ∩ L : Set V) ≃ M.edgeSet :=
  Equiv.ofBijective (fun v ↦ hM.toEdge ⟨v.1, v.2.1⟩)
    ⟨by
      intro u v huv
      dsimp only at huv
      have hu : u.1 ∈ (hM.toEdge ⟨u.1, u.2.1⟩ : Sym2 V) := hM.mem_coe_toEdge u.2.1
      have hv : v.1 ∈ (hM.toEdge ⟨u.1, u.2.1⟩ : Sym2 V) :=
        congrArg Subtype.val huv ▸ hM.mem_coe_toEdge v.2.1
      obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.1 hu
      rw [hw, Sym2.mem_iff] at hv
      rcases hv with hvu | hvw
      · exact Subtype.ext hvu.symm
      · exfalso
        have hedge : s(u.1, w) ∈ M.edgeSet := hw ▸ (hM.toEdge ⟨u.1, u.2.1⟩).2
        have hadj : G.Adj u.1 v.1 := hvw ▸ M.adj_sub (M.mem_edgeSet.1 hedge)
        exact Set.disjoint_left.1 h.disjoint v.2.2 (h.mem_of_mem_adj u.2.2 hadj),
    by
      rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ u v =>
        have huv : M.Adj u v := M.mem_edgeSet.1 he
        rcases h.mem_of_adj (M.adj_sub huv) with ⟨huL, _⟩ | ⟨_, hvL⟩
        · refine ⟨⟨u, huv.fst_mem, huL⟩, ?_⟩
          exact hM.toEdge_eq_of_adj huv
        · refine ⟨⟨v, huv.snd_mem, hvL⟩, ?_⟩
          dsimp only
          rw [hM.toEdge_eq_of_adj huv.symm]
          exact Subtype.ext Sym2.eq_swap⟩

/-- Applying `vertsInterEquivEdgeSet` maps a vertex in `M.verts ∩ L` to its incident edge in `M`. -/
@[simp]
theorem vertsInterEquivEdgeSet_apply (hM : M.IsMatching) (h : G.IsBipartiteWith L R)
    (v : (M.verts ∩ L : Set V)) :
    hM.vertsInterEquivEdgeSet h v = hM.toEdge ⟨v.1, v.2.1⟩ :=
  (rfl)

/-- In a bipartite graph with sides `L` and `R`, every matching has as many edges as vertices
saturated in `L`, measured in `ℕ∞`. -/
theorem encard_edgeSet_eq_encard_verts_inter (hM : M.IsMatching) (h : G.IsBipartiteWith L R) :
    M.edgeSet.encard = (M.verts ∩ L).encard := by
  have heq := ENat.card_congr (hM.vertsInterEquivEdgeSet h).symm
  simpa only [Set.encard] using heq

/-- In a bipartite graph with sides `L` and `R`, every matching has as many edges as vertices
saturated in `L`, measured by `Set.ncard`. -/
theorem ncard_edgeSet_eq_ncard_verts_inter (hM : M.IsMatching) (h : G.IsBipartiteWith L R) :
    M.edgeSet.ncard = (M.verts ∩ L).ncard := by
  rw [Set.ncard_def, Set.ncard_def, hM.encard_edgeSet_eq_encard_verts_inter h]

/-- Every matching in a bipartite graph has at most `L.encard` edges. -/
theorem encard_edgeSet_le_encard_left (hM : M.IsMatching) (h : G.IsBipartiteWith L R) :
    M.edgeSet.encard ≤ L.encard :=
  hM.encard_edgeSet_le_encard_of_isVertexCover h.isVertexCover_left

/-- Every matching in a bipartite graph with finite side `L` has at most `L.ncard` edges. -/
theorem ncard_edgeSet_le_ncard_left (hM : M.IsMatching) (h : G.IsBipartiteWith L R)
    (hLf : L.Finite) : M.edgeSet.ncard ≤ L.ncard :=
  hM.ncard_edgeSet_le_ncard_of_isVertexCover h.isVertexCover_left hLf

/-- A matching saturating `L` has `L.encard` edges. -/
theorem encard_edgeSet_eq_of_subset_verts (hM : M.IsMatching) (h : G.IsBipartiteWith L R)
    (hLM : L ⊆ M.verts) : M.edgeSet.encard = L.encard := by
  rw [hM.encard_edgeSet_eq_encard_verts_inter h, Set.inter_eq_right.2 hLM]

/-- When `L` is finite, a matching saturates `L` if and only if it has `L.encard` edges. -/
theorem subset_verts_iff_encard_edgeSet_eq (hM : M.IsMatching) (h : G.IsBipartiteWith L R)
    (hLf : L.Finite) : L ⊆ M.verts ↔ M.edgeSet.encard = L.encard := by
  refine ⟨hM.encard_edgeSet_eq_of_subset_verts h, fun heq ↦ ?_⟩
  rw [hM.encard_edgeSet_eq_encard_verts_inter h] at heq
  have hsub := hLf.eq_of_subset_of_encard_le' Set.inter_subset_right heq.symm.le
  exact hsub ▸ Set.inter_subset_left

/-- When `L` is finite, a matching saturates `L` if and only if it has `L.ncard` edges. -/
theorem subset_verts_iff_ncard_edgeSet_eq (hM : M.IsMatching) (h : G.IsBipartiteWith L R)
    (hLf : L.Finite) : L ⊆ M.verts ↔ M.edgeSet.ncard = L.ncard := by
  have hMf : M.edgeSet.Finite := Set.encard_lt_top_iff.1 <|
    (hM.encard_edgeSet_le_encard_left h).trans_lt hLf.encard_lt_top
  rw [hM.subset_verts_iff_encard_edgeSet_eq h hLf, ← hMf.cast_ncard_eq, ← hLf.cast_ncard_eq,
    ENat.natCast_inj]

/-! ### The Kőnig–Ore inequality -/

/-- **The Kőnig–Ore inequality in `ℕ∞`.** In a bipartite simple graph with sides `L` and `R`,
every matching `M` and every `S ⊆ L` satisfy
`M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard`. -/
theorem encard_edgeSet_add_encard_le (hM : M.IsMatching) (h : G.IsBipartiteWith L R)
    {S : Set V} (hS : S ⊆ L) :
    M.edgeSet.encard + S.encard ≤ L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
  have hcov := hM.encard_edgeSet_le_encard_of_isVertexCover
    (h.isVertexCover_sdiff_union_biUnion_neighborSet S)
  calc M.edgeSet.encard + S.encard
      ≤ ((L \ S) ∪ ⋃ x ∈ S, G.neighborSet x).encard + S.encard := add_le_add hcov le_rfl
    _ ≤ ((L \ S).encard + (⋃ x ∈ S, G.neighborSet x).encard) + S.encard :=
        add_le_add (Set.encard_union_le _ _) le_rfl
    _ = ((L \ S).encard + S.encard) + (⋃ x ∈ S, G.neighborSet x).encard := add_right_comm _ _ _
    _ = L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
        rw [Set.encard_sdiff_add_encard_of_subset hS]

/-- **The Kőnig–Ore inequality in `ℕ`.** When `L` and the neighbourhood of `S ⊆ L` are finite,
every matching `M` satisfies
`M.edgeSet.ncard + S.ncard ≤ L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem ncard_edgeSet_add_ncard_le (hM : M.IsMatching) (h : G.IsBipartiteWith L R)
    {S : Set V} (hS : S ⊆ L) (hLf : L.Finite) (hNf : (⋃ x ∈ S, G.neighborSet x).Finite) :
    M.edgeSet.ncard + S.ncard ≤ L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard := by
  have hMf : M.edgeSet.Finite := Set.encard_lt_top_iff.1 <|
    (hM.encard_edgeSet_le_encard_left h).trans_lt hLf.encard_lt_top
  have hSf : S.Finite := hLf.subset hS
  refine ENat.natCast_le_natCast.1 ?_
  push_cast
  rw [hMf.cast_ncard_eq, hSf.cast_ncard_eq, hLf.cast_ncard_eq, hNf.cast_ncard_eq]
  exact hM.encard_edgeSet_add_encard_le h hS

end Subgraph.IsMatching

/-! ### The Kőnig–Ore formula and Hall's marriage theorem -/

namespace IsBipartiteWith

/-- **The Kőnig–Ore formula (witness form in `ℕ∞`).** In every bipartite simple graph with sides
`L, R`, some matching `M` and some `S ⊆ L` attain
`M.edgeSet.encard + S.encard = L.encard + (⋃ x ∈ S, G.neighborSet x).encard` in `ℕ∞`. -/
theorem exists_isMatching_encard_add_encard_eq (h : G.IsBipartiteWith L R) :
    ∃ (M : G.Subgraph) (S : Set V), M.IsMatching ∧ S ⊆ L ∧
      M.edgeSet.encard + S.encard = L.encard + (⋃ x ∈ S, G.neighborSet x).encard := by
  obtain ⟨M, C, hM, hC, hMC⟩ := h.isBipartite.exists_isMatching_isVertexCover_encard_eq
  refine ⟨M, L \ C, hM, Set.sdiff_subset,
    le_antisymm (hM.encard_edgeSet_add_encard_le h Set.sdiff_subset) ?_⟩
  -- Every neighbour of `L \ C` lies in `C ∩ R`, hence is disjoint from `L ∩ C`.
  have hNC : (⋃ x ∈ L \ C, G.neighborSet x) ⊆ C := by
    rintro y hy
    obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.1 hy
    exact (hC hxy).resolve_left hx.2
  have hNR : (⋃ x ∈ L \ C, G.neighborSet x) ⊆ R := by
    rintro y hy
    obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.1 hy
    exact h.mem_of_mem_adj hx.1 hxy
  have hdisj : Disjoint (L ∩ C) (⋃ x ∈ L \ C, G.neighborSet x) :=
    h.disjoint.mono Set.inter_subset_left hNR
  have hsub : (L ∩ C) ∪ (⋃ x ∈ L \ C, G.neighborSet x) ⊆ C :=
    Set.union_subset Set.inter_subset_right hNC
  calc L.encard + (⋃ x ∈ L \ C, G.neighborSet x).encard
      = ((L \ C).encard + (L ∩ C).encard) + (⋃ x ∈ L \ C, G.neighborSet x).encard := by
        rw [Set.encard_sdiff_add_encard_inter]
    _ = ((L ∩ C).encard + (⋃ x ∈ L \ C, G.neighborSet x).encard) + (L \ C).encard := by
        rw [add_assoc, add_comm]
    _ = ((L ∩ C) ∪ ⋃ x ∈ L \ C, G.neighborSet x).encard + (L \ C).encard := by
        rw [Set.encard_union_eq hdisj]
    _ ≤ C.encard + (L \ C).encard := add_le_add (Set.encard_le_encard hsub) le_rfl
    _ = M.edgeSet.encard + (L \ C).encard := by rw [hMC]

/-- **The Kőnig–Ore formula (witness form in `ℕ`).** In a bipartite simple graph with a finite
side `L`, some matching `M` and some `S ⊆ L` with finite neighbourhood attain
`M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard`. -/
theorem exists_isMatching_ncard_add_ncard_eq [Finite L] (h : G.IsBipartiteWith L R) :
    ∃ (M : G.Subgraph) (S : Set V), M.IsMatching ∧ S ⊆ L ∧
      (⋃ x ∈ S, G.neighborSet x).Finite ∧
      M.edgeSet.ncard + S.ncard = L.ncard + (⋃ x ∈ S, G.neighborSet x).ncard := by
  obtain ⟨M, S, hM, hS, hEq⟩ := h.exists_isMatching_encard_add_encard_eq
  have hLf : L.Finite := Set.toFinite L
  have hSf : S.Finite := hLf.subset hS
  have hMf : M.edgeSet.Finite := Set.encard_lt_top_iff.1 <|
    (hM.encard_edgeSet_le_encard_left h).trans_lt hLf.encard_lt_top
  have hNf : (⋃ x ∈ S, G.neighborSet x).Finite := by
    refine Set.encard_ne_top_iff.1 fun htop ↦ ?_
    have hlhs : M.edgeSet.encard + S.encard ≠ ⊤ := by
      rw [← hMf.cast_ncard_eq, ← hSf.cast_ncard_eq, ← Nat.cast_add]
      exact ENat.natCast_ne_top _
    rw [htop, add_top] at hEq
    exact hlhs hEq
  refine ⟨M, S, hM, hS, hNf, ENat.natCast_inj.1 ?_⟩
  push_cast
  rw [hMf.cast_ncard_eq, hSf.cast_ncard_eq, hLf.cast_ncard_eq, hNf.cast_ncard_eq]
  exact hEq

/-- **The Kőnig–Ore deficiency formula in `ℕ∞`.** When `L` is finite (without assuming local
finiteness or finitely many edges), the matching number equals
`L.encard - ⨆ (S ⊆ L), (S.encard - (⋃ x ∈ S, G.neighborSet x).encard)`. -/
theorem matchingNum_eq_sub_iSup_encard [Finite L] (h : G.IsBipartiteWith L R) :
    G.matchingNum =
      L.encard - ⨆ (S : Set V) (_ : S ⊆ L),
        (S.encard - (⋃ x ∈ S, G.neighborSet x).encard) := by
  have hLf : L.Finite := Set.toFinite L
  set d : ℕ∞ := ⨆ (S : Set V) (_ : S ⊆ L), (S.encard - (⋃ x ∈ S, G.neighborSet x).encard)
  refine le_antisymm ?_ ?_
  · refine matchingNum_le_iff.2 fun M hM ↦ ?_
    have hML : M.edgeSet.encard ≤ L.encard := hM.encard_edgeSet_le_encard_left h
    have hMf : M.edgeSet.Finite := Set.encard_lt_top_iff.1 (hML.trans_lt hLf.encard_lt_top)
    have hdle : d ≤ L.encard - M.edgeSet.encard := by
      refine iSup₂_le fun S hS ↦ ?_
      have hSf : S.Finite := hLf.subset hS
      by_cases hNf : (⋃ x ∈ S, G.neighborSet x).Finite
      · have hineq := hM.ncard_edgeSet_add_ncard_le h hS hLf hNf
        rw [← hSf.cast_ncard_eq, ← hNf.cast_ncard_eq, ← hLf.cast_ncard_eq, ← hMf.cast_ncard_eq,
          ← ENat.natCast_sub, ← ENat.natCast_sub]
        exact ENat.natCast_le_natCast.2 (by omega)
      · rw [Set.Infinite.encard_eq hNf, tsub_eq_zero_of_le le_top]
        exact zero_le
    have hMLn : M.edgeSet.ncard ≤ L.ncard := hM.ncard_edgeSet_le_ncard_left h hLf
    rw [← hLf.cast_ncard_eq, ← hMf.cast_ncard_eq] at hdle ⊢
    have hdne : d ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [← ENat.natCast_sub]; exact ENat.natCast_ne_top _) hdle
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hdne
    rw [← hk, ← ENat.natCast_sub] at hdle ⊢
    have hkn : k ≤ L.ncard - M.edgeSet.ncard := ENat.natCast_le_natCast.1 hdle
    exact ENat.natCast_le_natCast.2 (by omega)
  · obtain ⟨M, S, hM, hS, hNf, hEq⟩ := h.exists_isMatching_ncard_add_ncard_eq
    have hSf : S.Finite := hLf.subset hS
    have hMf : M.edgeSet.Finite := Set.encard_lt_top_iff.1 <|
      (hM.encard_edgeSet_le_encard_left h).trans_lt hLf.encard_lt_top
    have hSle : S.encard - (⋃ x ∈ S, G.neighborSet x).encard ≤ d := le_iSup₂ (f := fun S _ ↦
      S.encard - (⋃ x ∈ S, G.neighborSet x).encard) S hS
    have hsub_le : L.encard - d ≤ L.encard - (S.encard - (⋃ x ∈ S, G.neighborSet x).encard) :=
      tsub_le_tsub_left hSle _
    refine hsub_le.trans ?_
    rw [← hLf.cast_ncard_eq, ← hSf.cast_ncard_eq, ← hNf.cast_ncard_eq, ← ENat.natCast_sub,
      ← ENat.natCast_sub]
    have hML : M.edgeSet.ncard ≤ L.ncard := hM.ncard_edgeSet_le_ncard_left h hLf
    have hle : L.ncard - (S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard) ≤ M.edgeSet.ncard := by omega
    exact (ENat.natCast_le_natCast.2 hle).trans
      (hMf.cast_ncard_eq ▸ hM.encard_edgeSet_le_matchingNum)

/-- **The numerical Kőnig–Ore deficiency formula in `ℕ`.** In a bipartite simple graph with
finitely many edges and finite side `L`, the greatest size of a matching is
`L.ncard - ⨆ (S ⊆ L), (S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard)`. -/
theorem isGreatest_ncard_isMatching [Finite L] [Finite G.edgeSet] (h : G.IsBipartiteWith L R) :
    IsGreatest {n : ℕ | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = n}
      (L.ncard - ⨆ (S : Set V) (_ : S ⊆ L),
        (S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard)) := by
  have hLf : L.Finite := Set.toFinite L
  let d : ℕ := ⨆ (S : Set V) (_ : S ⊆ L), (S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard)
  have hbdd : BddAbove (Set.range fun S : Set V ↦
      ⨆ (_ : S ⊆ L), (S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard)) := by
    refine ⟨L.ncard, ?_⟩
    rintro _ ⟨S, rfl⟩
    dsimp only
    by_cases hS : S ⊆ L
    · rw [ciSup_pos hS]
      exact (Nat.sub_le _ _).trans (Set.ncard_le_ncard hS hLf)
    · rw [ciSup_neg hS, csSup_empty]
      exact bot_le
  have hub : ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.ncard ≤ L.ncard - d := by
    intro M hM
    have hML : M.edgeSet.ncard ≤ L.ncard := hM.ncard_edgeSet_le_ncard_left h hLf
    have hdle : d ≤ L.ncard - M.edgeSet.ncard := by
      refine ciSup_le fun S ↦ ?_
      by_cases hS : S ⊆ L
      · rw [ciSup_pos hS]
        have hNf : (⋃ x ∈ S, G.neighborSet x).Finite :=
          G.finite_support.subset <| Set.iUnion₂_subset fun x _ ↦ G.neighborSet_subset_support x
        have hineq := hM.ncard_edgeSet_add_ncard_le h hS hLf hNf
        omega
      · rw [ciSup_neg hS, csSup_empty]
        exact bot_le
    omega
  refine ⟨?_, ?_⟩
  · obtain ⟨M, S, hM, hS, _, hEq⟩ := h.exists_isMatching_ncard_add_ncard_eq
    have hSle : S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard ≤ d := by
      have h1 : (⨆ (_ : S ⊆ L), (S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard)) =
          S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard := ciSup_pos hS
      exact h1.symm.le.trans (le_ciSup hbdd S)
    have hMle := hub M hM
    exact ⟨M, hM, by omega⟩
  · rintro n ⟨M, hM, rfl⟩
    exact hub M hM

/-- The matching number expressed by the Kőnig–Ore deficiency formula in `ℕ`. -/
theorem matchingNum_eq_sub_iSup [Finite L] [Finite G.edgeSet] (h : G.IsBipartiteWith L R) :
    G.matchingNum =
      ((L.ncard - ⨆ (S : Set V) (_ : S ⊆ L),
        (S.ncard - (⋃ x ∈ S, G.neighborSet x).ncard) : ℕ) : ℕ∞) := by
  obtain ⟨⟨M, hM, hMeq⟩, hmax⟩ := h.isGreatest_ncard_isMatching
  have hMf : M.edgeSet.Finite := (Set.toFinite G.edgeSet).subset M.edgeSet_subset
  refine le_antisymm ?_ ?_
  · refine matchingNum_le_iff.2 fun M' hM' ↦ ?_
    have hM'f : M'.edgeSet.Finite := (Set.toFinite G.edgeSet).subset M'.edgeSet_subset
    rw [← hM'f.cast_ncard_eq]
    exact ENat.natCast_le_natCast.2 (hmax ⟨M', hM', rfl⟩)
  · rw [← hMeq, hMf.cast_ncard_eq]
    exact hM.encard_edgeSet_le_matchingNum

/-- **Hall's marriage theorem in `ℕ∞` for a finite side.** When `L` is finite (without assuming
local finiteness or finitely many edges), there is a matching saturating `L` if and only if every
`S ⊆ L` has `S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard`. -/
theorem exists_isMatching_subset_verts_iff_encard [Finite L] (h : G.IsBipartiteWith L R) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.encard ≤ (⋃ x ∈ S, G.neighborSet x).encard := by
  have hLf : L.Finite := Set.toFinite L
  constructor
  · rintro ⟨M, hLM, hM⟩ S hS
    exact hM.encard_le_encard_biUnion_neighborSet (hS.trans hLM)
  · intro hHall
    obtain ⟨M, S, hM, hS, hNf, hEq⟩ := h.exists_isMatching_ncard_add_ncard_eq
    have hSf : S.Finite := hLf.subset hS
    have hle : S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
      have := hHall S hS
      rw [← hSf.cast_ncard_eq, ← hNf.cast_ncard_eq] at this
      exact ENat.natCast_le_natCast.1 this
    have hML := hM.ncard_edgeSet_le_ncard_left h hLf
    exact ⟨M, (hM.subset_verts_iff_ncard_edgeSet_eq h hLf).2 (by omega), hM⟩

/-- **Hall's marriage theorem for finite bipartite simple graphs.** When `L` and `G.edgeSet` are
finite, there is a matching saturating `L` if and only if every `S ⊆ L` has at least `S.ncard`
neighbours. -/
theorem exists_isMatching_subset_verts_iff [Finite L] [Finite G.edgeSet]
    (h : G.IsBipartiteWith L R) :
    (∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching) ↔
      ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  rw [h.exists_isMatching_subset_verts_iff_encard]
  have hLf : L.Finite := Set.toFinite L
  refine forall₂_congr fun S hS ↦ ?_
  have hSf : S.Finite := hLf.subset hS
  have hNf : (⋃ x ∈ S, G.neighborSet x).Finite :=
    G.finite_support.subset <| Set.iUnion₂_subset fun x _ ↦ G.neighborSet_subset_support x
  rw [← hSf.cast_ncard_eq, ← hNf.cast_ncard_eq, ENat.natCast_le_natCast]

/-- **Hall's perfect-matching theorem for finite bipartite simple graphs.** When `L` and `R` are
finite and cover `V`, there is a perfect matching if and only if `L` and `R` have equal size and
every `S ⊆ L` has at least `S.ncard` neighbours. -/
theorem exists_isPerfectMatching_iff [Finite L] [Finite R] (h : G.IsBipartiteWith L R)
    (hcover : L ∪ R = Set.univ) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      L.ncard = R.ncard ∧ ∀ S ⊆ L, S.ncard ≤ (⋃ x ∈ S, G.neighborSet x).ncard := by
  have hLf : L.Finite := Set.toFinite L
  have hRf : R.Finite := Set.toFinite R
  have : Finite V := Set.finite_univ_iff.1 (hcover ▸ hLf.union hRf)
  constructor
  · rintro ⟨M, hM, hspan⟩
    have hLM : L ⊆ M.verts := fun v _ ↦ hspan v
    have hRM : R ⊆ M.verts := fun v _ ↦ hspan v
    refine ⟨?_, h.exists_isMatching_subset_verts_iff.1 ⟨M, hLM, hM⟩⟩
    have hL := (hM.subset_verts_iff_ncard_edgeSet_eq h hLf).1 hLM
    have hR := (hM.subset_verts_iff_ncard_edgeSet_eq h.symm hRf).1 hRM
    exact hL.symm.trans hR
  · rintro ⟨hLR, hHall⟩
    obtain ⟨M, hLM, hM⟩ := h.exists_isMatching_subset_verts_iff.2 hHall
    have hML : M.edgeSet.ncard = L.ncard := (hM.subset_verts_iff_ncard_edgeSet_eq h hLf).1 hLM
    have hRM : R ⊆ M.verts :=
      (hM.subset_verts_iff_ncard_edgeSet_eq h.symm hRf).2 (hML.trans hLR)
    refine ⟨M, hM, Subgraph.isSpanning_iff.2 (Set.eq_univ_of_forall fun v ↦ ?_)⟩
    have hv : v ∈ L ∪ R := hcover.symm ▸ Set.mem_univ v
    exact hv.elim (fun hvL ↦ hLM hvL) (fun hvR ↦ hRM hvR)

end IsBipartiteWith

/-! ### Compatibility with Mathlib's Hall interface -/

-- Recovering the finite specialization of `SimpleGraph.exists_isMatching_of_forall_ncard_le`
-- from the Kőnig–Ore development via `IsBipartiteWith.finite_edgeSet`.
example [G.LocallyFinite] [Finite L] (h : G.IsBipartiteWith L R)
    (hHall : ∀ s ⊆ L, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : G.Subgraph, L ⊆ M.verts ∧ M.IsMatching := by
  have : Finite G.edgeSet := h.finite_edgeSet.to_subtype
  exact h.exists_isMatching_subset_verts_iff.2 hHall

-- Recovering the finite specialization of
-- `SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le`.
example [Finite V] (h : G.IsBipartiteWith L R)
    (hHall : ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  have hcover : L ∪ R = Set.univ := by
    refine Set.eq_univ_of_forall fun v ↦ ?_
    have hv : ({v} : Set V).ncard ≤ (⋃ x ∈ ({v} : Set V), G.neighborSet x).ncard := hHall {v}
    rw [Set.ncard_singleton, Set.biUnion_singleton] at hv
    obtain ⟨w, hw⟩ := Set.nonempty_of_ncard_ne_zero (Nat.pos_iff_ne_zero.1 hv)
    exact isBipartiteWith_support_subset h hw.mem_support_left
  have hLR : L.ncard = R.ncard := by
    refine le_antisymm ?_ ?_
    · exact (hHall L).trans <| Set.ncard_le_ncard
        (Set.iUnion₂_subset fun x hx ↦ isBipartiteWith_neighborSet_subset h hx) (Set.toFinite R)
    · exact (hHall R).trans <| Set.ncard_le_ncard
        (Set.iUnion₂_subset fun x hx ↦ isBipartiteWith_neighborSet_subset h.symm hx)
        (Set.toFinite L)
  exact (h.exists_isPerfectMatching_iff hcover).2 ⟨hLR, fun s _ ↦ hHall s⟩

end SimpleGraph
