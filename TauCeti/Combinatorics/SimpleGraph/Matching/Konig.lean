/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

import Mathlib.Data.Set.Card.Arithmetic
import TauCeti.Combinatorics.Graph.Matching.Capacitated
import TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph
import TauCeti.Combinatorics.Graph.VertexCover.SimpleGraph
import TauCeti.Combinatorics.SimpleGraph.Finite

/-!
# Kőnig's theorem and matching–cover extremality for simple graphs

This file defines the matching number `SimpleGraph.matchingNum`, maximum matchings
`SimpleGraph.Subgraph.IsMaximumMatching`, and minimum vertex covers
`SimpleGraph.IsMinimumVertexCover` for simple graphs, develops their basic API and weak duality
in `ℕ∞`, and proves Kőnig's theorem in `ℕ∞` for all bipartite simple graphs.

Sizes are measured in `ℕ∞` via `Set.encard`, matching Mathlib's `SimpleGraph.vertexCoverNum`.
Because `ℕ∞` collapses all infinite cardinals to `⊤`, the results in `ℕ∞` require no finiteness
assumptions on the vertex or edge sets:

* Every simple graph attains its matching number (`SimpleGraph.matchingNum_exists`) and satisfies
  the sandwich `G.matchingNum ≤ G.vertexCoverNum ≤ 2 * G.matchingNum`.
* Every bipartite simple graph satisfies `G.matchingNum = G.vertexCoverNum` and admits a matching
  and a vertex cover with equal `encard` in `ℕ∞`. When `G.matchingNum ≠ ⊤` (in particular whenever
  `G.edgeSet` is finite, or `G` has a finite vertex cover such as a finite bipartition side), both
  witnesses are finite and attain the same finite `Set.ncard`. When `G.matchingNum = ⊤`, both
  witnesses are infinite (`encard = ⊤`); this is equality in `ℕ∞`, not Aharoni's cardinal-valued
  infinite Kőnig theorem.

## Main definitions

* `SimpleGraph.matchingNum G`: the matching number of `G`, defined in `ℕ∞` as the supremum of
  `M.edgeSet.encard` over all matchings `M : G.Subgraph`.
* `SimpleGraph.Subgraph.IsMaximumMatching M`: `M` is a matching whose edge set has maximum
  `encard` among all matchings of `G`.
* `SimpleGraph.IsMinimumVertexCover G c`: `c` is a vertex cover of `G` with minimum `encard`
  among all vertex covers of `G`.

## Main results

* `SimpleGraph.Subgraph.IsMatching.two_mul_encard_edgeSet`: `2 * M.edgeSet.encard = M.verts.encard`
  for every matching `M`.
* `SimpleGraph.Subgraph.IsMatching.encard_edgeSet_le_encard_of_isVertexCover` and
  `SimpleGraph.matchingNum_le_vertexCoverNum`: **weak duality** between matchings and vertex
  covers.
* `SimpleGraph.matchingNum_exists` and `SimpleGraph.exists_isMaximumMatching`: every simple graph
  attains its matching number in `ℕ∞`.
* `SimpleGraph.vertexCoverNum_le_two_mul_matchingNum`: `G.vertexCoverNum ≤ 2 * G.matchingNum` for
  every simple graph `G`.
* `SimpleGraph.Subgraph.IsPerfectMatching.isMaximumMatching`: every perfect matching is maximum.
* `SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_encard_eq` and
  `SimpleGraph.IsBipartite.exists_isMatching_isVertexCover_ncard_eq`: **Kőnig's theorem** in
  witness form.
* `SimpleGraph.IsBipartite.matchingNum_eq_vertexCoverNum`: `G.matchingNum = G.vertexCoverNum` for
  every bipartite simple graph `G`.
* `SimpleGraph.IsBipartite.exists_isMaximumMatching_isMinimumVertexCover`: every bipartite simple
  graph has a maximum matching and a minimum vertex cover with equal `encard`.

## Implementation notes

The proof of Kőnig's theorem reduces in two steps:

1. For a bipartite simple graph with `[Finite G.edgeSet]`, inducing on the finite set `G.support`
   eliminates isolated vertices and yields a finite covering bipartition of
   `Graph.ofSimpleGraph (G.induce G.support)`. Applying the unit-capacity multigraph Kőnig theorem
   (`Graph.IsBipartition.exists_isCapacitatedMatching_isVertexCover_sum_eq`) and transporting back
   along the support embedding proves the finite-edge case.
2. For an arbitrary bipartite simple graph with a finite vertex cover `C₀` of size `k`, grouping
   vertices outside `C₀` by their neighbourhood in `C₀` and keeping at most `k + 1` vertices per
   twin class yields a finite induced subgraph whose Kőnig matching and cover lift back to `G`.
3. When `G.matchingNum = ⊤`, an infinite matching is built recursively by picking edges disjoint
   from previously used vertices (`Subgraph.IsMatching.iSup`), matching `c = Set.univ` in `ℕ∞`.

## References

* D. Kőnig, *Gráfok és mátrixok*, Mat. Fiz. Lapok 38 (1931).
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 2.1.
-/

public section

open Function Set
open scoped Graph

namespace SimpleGraph

variable {V W : Type*} {G G' : SimpleGraph V} {H : SimpleGraph W}

/-! ### Matching cardinality helpers -/

namespace Subgraph

/-- The empty subgraph is a matching. -/
@[simp]
theorem isMatching_bot : (⊥ : G.Subgraph).IsMatching :=
  fun _ h ↦ False.elim h

namespace IsMatching

variable {M : G.Subgraph}

/-- Two edges of a matching that share a vertex are equal. -/
theorem eq_of_mem_edgeSet (hM : M.IsMatching) {e₁ e₂ : Sym2 V} (he₁ : e₁ ∈ M.edgeSet)
    (he₂ : e₂ ∈ M.edgeSet) {v : V} (hv₁ : v ∈ e₁) (hv₂ : v ∈ e₂) : e₁ = e₂ := by
  obtain ⟨w₁, rfl⟩ := Sym2.mem_iff_exists.1 hv₁
  obtain ⟨w₂, rfl⟩ := Sym2.mem_iff_exists.1 hv₂
  rw [hM.eq_of_adj_left (M.mem_edgeSet.1 he₁) (M.mem_edgeSet.1 he₂)]

/-- Every matching covers twice as many vertices as it has edges, measured in `ℕ∞`. -/
theorem two_mul_encard_edgeSet (hM : M.IsMatching) :
    2 * M.edgeSet.encard = M.verts.encard := by
  by_cases hfin : M.edgeSet.Finite
  · rw [hM.verts_eq_biUnion_edgeSet]
    have hdisj : M.edgeSet.PairwiseDisjoint (fun e : Sym2 V ↦ (e : Set V)) :=
      fun _ he₁ _ he₂ hne ↦ Set.disjoint_left.2 fun _ hv₁ hv₂ ↦
        hne (hM.eq_of_mem_edgeSet he₁ he₂ hv₁ hv₂)
    rw [hfin.encard_biUnion hdisj, finsum_mem_eq_finite_toFinset_sum _ hfin]
    have htwo : ∀ e ∈ hfin.toFinset, (e : Set V).encard = 2 := fun e he ↦ by
      have he' : e ∈ M.edgeSet := hfin.mem_toFinset.1 he
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := (M.mem_edgeSet.1 he').ne
        rw [Sym2.coe_mk, Set.encard_pair huv]
    rw [Finset.sum_congr rfl htwo, Finset.sum_const, nsmul_eq_mul, mul_comm,
      ← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset]
  · have hinfE : M.edgeSet.Infinite := hfin
    have hinfV : M.verts.Infinite := by
      intro hVfin
      have : Finite M.verts := hVfin.to_subtype
      exact hinfE (Set.finite_coe_iff.1
        (Finite.of_surjective hM.toEdge (Subgraph.IsMatching.toEdge.surjective hM)))
    rw [hinfE.encard_eq, hinfV.encard_eq]
    exact ENat.mul_top (by decide)

/-- Every matching covers twice as many vertices as it has edges, measured by `Set.ncard`. -/
theorem two_mul_ncard_edgeSet (hM : M.IsMatching) :
    2 * M.edgeSet.ncard = M.verts.ncard := by
  rw [Set.ncard_def, Set.ncard_def, ← hM.two_mul_encard_edgeSet, ENat.toNat_mul]
  simp

end IsMatching

end Subgraph

/-! ### The matching number -/

section matchingNum

/-- The matching number of `G` is the supremum in `ℕ∞` of the sizes of all matchings of `G`. -/
noncomputable def matchingNum (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard

/-- Restatement of `SimpleGraph.matchingNum` without unfolding. -/
theorem matchingNum_def (G : SimpleGraph V) :
    G.matchingNum = ⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard :=
  (rfl)

/-- The matching number is at most `n` if and only if every matching has at most `n` edges. -/
theorem matchingNum_le_iff {n : ℕ∞} :
    G.matchingNum ≤ n ↔ ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.encard ≤ n := by
  simp [matchingNum_def]

/-- The size of any matching is at most the matching number. -/
theorem Subgraph.IsMatching.encard_edgeSet_le_matchingNum {M : G.Subgraph} (hM : M.IsMatching) :
    M.edgeSet.encard ≤ G.matchingNum :=
  matchingNum_le_iff.1 le_rfl M hM

/-- The `ncard` size of any matching is at most the matching number. -/
theorem Subgraph.IsMatching.ncard_edgeSet_le_matchingNum {M : G.Subgraph} (hM : M.IsMatching) :
    (M.edgeSet.ncard : ℕ∞) ≤ G.matchingNum :=
  (Set.ncard_le_encard M.edgeSet).trans hM.encard_edgeSet_le_matchingNum

/-- The empty graph has matching number zero. -/
@[simp]
theorem matchingNum_bot : (⊥ : SimpleGraph V).matchingNum = 0 := by
  refine nonpos_iff_eq_zero.1 (matchingNum_le_iff.2 fun M _ ↦ ?_)
  have : M.edgeSet = ∅ := Set.eq_empty_of_subset M.edgeSet_subset edgeSet_bot
  simp [this]

/-- A graph on a subsingleton vertex type has matching number zero. -/
@[simp]
theorem matchingNum_of_subsingleton [Subsingleton V] : G.matchingNum = 0 := by
  have : G = ⊥ := Subsingleton.elim G ⊥
  simp [this]

/-- The matching number vanishes if and only if the graph has no edges. -/
@[simp]
theorem matchingNum_eq_zero : G.matchingNum = 0 ↔ G = ⊥ := by
  refine ⟨fun h ↦ eq_bot_iff_forall_not_adj.2 fun u v huv ↦ ?_, fun h ↦ by simp [h]⟩
  have hle := (Subgraph.IsMatching.subgraphOfAdj huv).encard_edgeSet_le_matchingNum
  rw [edgeSet_subgraphOfAdj, Set.encard_singleton, h] at hle
  exact absurd hle (by decide)

/-- The matching number is at most the number of edges. -/
theorem matchingNum_le_encard_edgeSet : G.matchingNum ≤ G.edgeSet.encard :=
  matchingNum_le_iff.2 fun M _ ↦ Set.encard_le_encard M.edgeSet_subset

/-- A graph with finitely many edges has finite matching number. -/
@[simp]
theorem matchingNum_ne_top_of_finite_edgeSet (h : G.edgeSet.Finite) : G.matchingNum ≠ ⊤ :=
  ne_top_of_le_ne_top (Set.encard_ne_top_iff.2 h) matchingNum_le_encard_edgeSet

/-- A graph on a finite vertex type has finite matching number. -/
@[simp]
theorem matchingNum_ne_top_of_finite [Finite V] : G.matchingNum ≠ ⊤ :=
  matchingNum_ne_top_of_finite_edgeSet (Set.toFinite G.edgeSet)

/-- If `G` is contained in `H`, then `G.matchingNum ≤ H.matchingNum`. -/
theorem IsContained.matchingNum_le_matchingNum (h : G ⊑ H) : G.matchingNum ≤ H.matchingNum := by
  obtain ⟨f⟩ := h
  refine matchingNum_le_iff.2 fun M hM ↦ ?_
  have hMf : (M.map f.toHom).IsMatching := hM.map f.toHom f.injective
  have hinj : Function.Injective f.toHom := f.injective
  have he : (M.map f.toHom).edgeSet.encard = M.edgeSet.encard := by
    rw [Subgraph.edgeSet_map, (Sym2.map.injective hinj).encard_image]
  exact he ▸ hMf.encard_edgeSet_le_matchingNum

/-- The matching number is monotone in the graph. -/
@[gcongr]
theorem matchingNum_mono (h : G ≤ G') : G.matchingNum ≤ G'.matchingNum :=
  (IsContained.of_le h).matchingNum_le_matchingNum

/-- Isomorphic graphs have the same matching number. -/
theorem matchingNum_congr (f : G ≃g H) : G.matchingNum = H.matchingNum :=
  le_antisymm f.isContained.matchingNum_le_matchingNum
    f.symm.isContained.matchingNum_le_matchingNum

end matchingNum

/-! ### Weak duality and attainment -/

section WeakDuality

/-- **Weak duality between matchings and vertex covers.** Every matching has at most as many edges
as any vertex cover has vertices, measured in `ℕ∞`. -/
theorem Subgraph.IsMatching.encard_edgeSet_le_encard_of_isVertexCover {M : G.Subgraph}
    {c : Set V} (hM : M.IsMatching) (hc : G.IsVertexCover c) :
    M.edgeSet.encard ≤ c.encard := by
  have hex : ∀ e : M.edgeSet, ∃ v : c, v.1 ∈ e.1 := fun e ↦ by
    have hadj : G.Adj e.1.out.1 e.1.out.2 := by
      have hmem : s(e.1.out.1, e.1.out.2) ∈ M.edgeSet := by
        rw [Sym2.mk_fst_out_snd_out]
        exact e.2
      exact M.adj_sub (M.mem_edgeSet.1 hmem)
    rcases hc hadj with h1 | h2
    · exact ⟨⟨e.1.out.1, h1⟩, Sym2.out_fst_mem e.1⟩
    · exact ⟨⟨e.1.out.2, h2⟩, Sym2.out_snd_mem e.1⟩
  choose f hf using hex
  refine Function.Embedding.encard_le ⟨f, fun e₁ e₂ h ↦ Subtype.ext ?_⟩
  exact hM.eq_of_mem_edgeSet e₁.2 e₂.2 (hf e₁) (h ▸ hf e₂)

/-- Weak duality in `ℕ` for a finite vertex cover. -/
theorem Subgraph.IsMatching.ncard_edgeSet_le_ncard_of_isVertexCover {M : G.Subgraph}
    {c : Set V} (hM : M.IsMatching) (hc : G.IsVertexCover c) (hcf : c.Finite) :
    M.edgeSet.ncard ≤ c.ncard :=
  ENat.natCast_le_natCast.1 <| (Set.ncard_le_encard M.edgeSet).trans <|
    (hM.encard_edgeSet_le_encard_of_isVertexCover hc).trans_eq hcf.cast_ncard_eq.symm

/-- **Weak duality for numerical invariants.** The matching number is at most the vertex cover
number. -/
theorem matchingNum_le_vertexCoverNum (G : SimpleGraph V) :
    G.matchingNum ≤ G.vertexCoverNum := by
  obtain ⟨c, hcard, hc⟩ := G.vertexCoverNum_exists
  rw [← hcard, matchingNum_le_iff]
  exact fun M hM ↦ hM.encard_edgeSet_le_encard_of_isVertexCover hc

private theorem matchingNum_exists_of_ne_top (h : G.matchingNum ≠ ⊤) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = G.matchingNum := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h
  cases n with
  | zero =>
    exact ⟨⊥, Subgraph.isMatching_bot, by simp [← hn]⟩
  | succ k =>
    have hnot : ¬ G.matchingNum ≤ (k : ℕ∞) := by
      rw [← hn]
      exact not_le.2 (by exact_mod_cast Nat.lt_succ_self k)
    rw [matchingNum_le_iff] at hnot
    push Not at hnot
    obtain ⟨M, hM, hlt⟩ := hnot
    refine ⟨M, hM, le_antisymm hM.encard_edgeSet_le_matchingNum ?_⟩
    rw [← hn]
    exact Order.add_one_le_of_lt hlt

/-- When `G.matchingNum = ⊤`, no finite vertex set is a vertex cover of `G`. -/
private theorem exists_adj_disjoint_finset_of_matchingNum_eq_top (h : G.matchingNum = ⊤)
    (S : Finset V) : ∃ p : V × V, G.Adj p.1 p.2 ∧ p.1 ∉ S ∧ p.2 ∉ S := by
  by_contra hcov
  push Not at hcov
  have hvc : G.IsVertexCover (S : Set V) := fun u v huv ↦ by
    by_contra hmem
    push Not at hmem
    exact hmem.2 (hcov (u, v) huv hmem.1)
  have hle : G.matchingNum ≤ (S : Set V).encard :=
    G.matchingNum_le_vertexCoverNum.trans hvc.vertexCoverNum_le
  rw [h, top_le_iff] at hle
  exact S.finite_toSet.encard_lt_top.ne hle

/-- When `G.matchingNum = ⊤`, picking edges greedily avoids all previously used endpoints and
produces an infinite matching. -/
private theorem exists_infinite_matching_of_matchingNum_eq_top (h : G.matchingNum = ⊤) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = ⊤ := by
  classical
  have hstep := exists_adj_disjoint_finset_of_matchingNum_eq_top h
  let next (S : Finset V) : V × V := (hstep S).choose
  let used : ℕ → Finset V := Nat.rec ∅ fun _ S ↦ insert (next S).1 (insert (next S).2 S)
  have hmono : Monotone used := monotone_nat_of_le_succ fun _ ↦
    (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  let u (n : ℕ) : V := (next (used n)).1
  let v (n : ℕ) : V := (next (used n)).2
  have hadj (n : ℕ) : G.Adj (u n) (v n) := (hstep (used n)).choose_spec.1
  have hu_not (n : ℕ) : u n ∉ used n := (hstep (used n)).choose_spec.2.1
  have hv_not (n : ℕ) : v n ∉ used n := (hstep (used n)).choose_spec.2.2
  have hu_mem (n : ℕ) : u n ∈ used (n + 1) := Finset.mem_insert_self _ _
  have hv_mem (n : ℕ) : v n ∈ used (n + 1) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hlt_disj {i j : ℕ} (hij : i < j) :
      Disjoint (G.subgraphOfAdj (hadj i)).verts (G.subgraphOfAdj (hadj j)).verts := by
    rw [Set.disjoint_left]
    intro x hxi hxj
    rw [subgraphOfAdj_verts] at hxi hxj
    have hx_in : x ∈ used j := by
      rcases hxi with rfl | rfl
      · exact hmono hij (hu_mem i)
      · exact hmono hij (hv_mem i)
    rcases hxj with rfl | rfl
    · exact hu_not j hx_in
    · exact hv_not j hx_in
  have hdisj : Pairwise fun i j ↦
      Disjoint (G.subgraphOfAdj (hadj i)).support (G.subgraphOfAdj (hadj j)).support := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt' | hlt'
    · exact (hlt_disj hlt').mono (Subgraph.support_subset_verts _) (Subgraph.support_subset_verts _)
    · exact (hlt_disj hlt').symm.mono (Subgraph.support_subset_verts _)
        (Subgraph.support_subset_verts _)
  refine ⟨⨆ n : ℕ, G.subgraphOfAdj (hadj n),
    Subgraph.IsMatching.iSup (fun n ↦ Subgraph.IsMatching.subgraphOfAdj (hadj n)) hdisj, ?_⟩
  refine Set.Infinite.encard_eq ?_
  have hne_of_lt {i j : ℕ} (hlt : i < j) : s(u i, v i) ≠ s(u j, v j) := fun heq ↦ by
    have hmem : u i ∈ s(u j, v j) := heq ▸ Sym2.mem_mk_left (u i) (v i)
    rcases Sym2.mem_iff.1 hmem with h1 | h1
    · exact hu_not j (h1 ▸ hmono hlt (hu_mem i))
    · exact hv_not j (h1 ▸ hmono hlt (hu_mem i))
  have hinj : Function.Injective fun n : ℕ ↦ s(u n, v n) := fun i j heq ↦ by
    by_contra hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hne_of_lt hlt heq
    · exact hne_of_lt hlt heq.symm
  refine Set.infinite_of_injective_forall_mem hinj fun n ↦ ?_
  exact Subgraph.mem_edgeSet.2 <| Subgraph.iSup_adj.2 ⟨n, by simp [subgraphOfAdj_adj]⟩

/-- Every simple graph has a matching attaining its matching number in `ℕ∞`. -/
theorem matchingNum_exists (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.encard = G.matchingNum := by
  by_cases h : G.matchingNum = ⊤
  · obtain ⟨M, hM, hcard⟩ := exists_infinite_matching_of_matchingNum_eq_top h
    exact ⟨M, hM, hcard.trans h.symm⟩
  · exact matchingNum_exists_of_ne_top h

/-- Twice the matching number is at most the number of vertices. -/
theorem two_mul_matchingNum_le_card (G : SimpleGraph V) :
    2 * G.matchingNum ≤ ENat.card V := by
  obtain ⟨M, hM, hEq⟩ := G.matchingNum_exists
  rw [← hEq, hM.two_mul_encard_edgeSet, ← Set.encard_univ]
  exact Set.encard_le_encard (Set.subset_univ _)

end WeakDuality

/-! ### Maximum matchings and minimum vertex covers -/

section Extremal

/-- A subgraph `M` of `G` is a *maximum matching* if it is a matching and no matching of `G` has
more edges, measured in `ℕ∞`. -/
def Subgraph.IsMaximumMatching (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.encard ≤ M.edgeSet.encard

/-- Restatement of `Subgraph.IsMaximumMatching` without unfolding. -/
theorem Subgraph.isMaximumMatching_def {M : G.Subgraph} :
    M.IsMaximumMatching ↔
      M.IsMatching ∧ ∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.encard ≤ M.edgeSet.encard :=
  (Iff.rfl)

namespace Subgraph.IsMaximumMatching

variable {M M' : G.Subgraph}

/-- A maximum matching is a matching. -/
theorem isMatching (hM : M.IsMaximumMatching) : M.IsMatching :=
  hM.1

/-- Every matching has at most as many edges as a maximum matching, in `ℕ∞`. -/
theorem encard_edgeSet_le (hM : M.IsMaximumMatching) (hM' : M'.IsMatching) :
    M'.edgeSet.encard ≤ M.edgeSet.encard :=
  hM.2 M' hM'

/-- Every matching has at most as many edges as a finite maximum matching, in `ℕ`. -/
theorem ncard_edgeSet_le (hM : M.IsMaximumMatching) (hM' : M'.IsMatching)
    (hf : M.edgeSet.Finite) : M'.edgeSet.ncard ≤ M.edgeSet.ncard :=
  ENat.natCast_le_natCast.1 <| (Set.ncard_le_encard M'.edgeSet).trans <|
    (hM.encard_edgeSet_le hM').trans_eq hf.cast_ncard_eq.symm

/-- The saturated vertices of a finite maximum matching form a vertex cover of `G`. -/
theorem isVertexCover_verts (hM : M.IsMaximumMatching) (hf : M.edgeSet.Finite) :
    G.IsVertexCover M.verts := by
  intro u v huv
  by_contra hnot
  push Not at hnot
  have hdisj : Disjoint M.support (G.subgraphOfAdj huv).support := by
    refine Set.disjoint_left.2 fun x hxM hxE ↦ ?_
    have hxM' : x ∈ M.verts := M.support_subset_verts hxM
    have hxE' : x ∈ (G.subgraphOfAdj huv).verts := Subgraph.support_subset_verts _ hxE
    rw [subgraphOfAdj_verts] at hxE'
    rcases hxE' with rfl | rfl
    · exact hnot.1 hxM'
    · exact hnot.2 hxM'
  have hM' : (M ⊔ G.subgraphOfAdj huv).IsMatching :=
    hM.1.sup (Subgraph.IsMatching.subgraphOfAdj huv) hdisj
  have hnotmem : s(u, v) ∉ M.edgeSet := fun hmem ↦
    hnot.1 (M.mem_verts_of_mem_edge hmem (Sym2.mem_mk_left u v))
  have hedges : (M ⊔ G.subgraphOfAdj huv).edgeSet = insert s(u, v) M.edgeSet := by
    rw [Subgraph.edgeSet_sup, edgeSet_subgraphOfAdj, Set.union_singleton]
  have hle := hM.encard_edgeSet_le hM'
  rw [hedges, Set.encard_insert_of_notMem hnotmem] at hle
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (Set.encard_ne_top_iff.2 hf)
  rw [← hn] at hle
  have hnat : n + 1 ≤ n := by exact_mod_cast hle
  omega

end Subgraph.IsMaximumMatching

/-- A subgraph is a maximum matching if and only if it is a matching whose size equals the
matching number. -/
theorem Subgraph.isMaximumMatching_iff_encard_edgeSet_eq_matchingNum {M : G.Subgraph} :
    M.IsMaximumMatching ↔ M.IsMatching ∧ M.edgeSet.encard = G.matchingNum := by
  refine ⟨fun hM ↦ ⟨hM.1, le_antisymm hM.1.encard_edgeSet_le_matchingNum
    (matchingNum_le_iff.2 hM.2)⟩, fun ⟨hM, heq⟩ ↦ ⟨hM, fun M' hM' ↦
    heq ▸ hM'.encard_edgeSet_le_matchingNum⟩⟩

/-- A maximum matching attains the matching number. -/
theorem Subgraph.IsMaximumMatching.encard_edgeSet_eq {M : G.Subgraph} (hM : M.IsMaximumMatching) :
    M.edgeSet.encard = G.matchingNum :=
  (Subgraph.isMaximumMatching_iff_encard_edgeSet_eq_matchingNum.1 hM).2

/-- When the matching number is finite, maximum matchings are characterized by `Set.ncard`. -/
theorem Subgraph.isMaximumMatching_iff_forall_ncard_le (h : G.matchingNum ≠ ⊤) {M : G.Subgraph} :
    M.IsMaximumMatching ↔
      M.IsMatching ∧ ∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard := by
  have hfin : ∀ {N : G.Subgraph}, N.IsMatching → N.edgeSet.Finite := fun hN ↦
    Set.encard_lt_top_iff.1 (hN.encard_edgeSet_le_matchingNum.trans_lt (lt_top_iff_ne_top.2 h))
  refine ⟨fun hM ↦ ⟨hM.1, fun M' hM' ↦ hM.ncard_edgeSet_le hM' (hfin hM.1)⟩,
    fun ⟨hM, hmax⟩ ↦ ⟨hM, fun M' hM' ↦ ?_⟩⟩
  rw [← (hfin hM').cast_ncard_eq, ← (hfin hM).cast_ncard_eq]
  exact ENat.natCast_le_natCast.2 (hmax M' hM')

/-- Every simple graph has a maximum matching in `ℕ∞`. -/
theorem exists_isMaximumMatching (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMaximumMatching := by
  obtain ⟨M, hM, hcard⟩ := G.matchingNum_exists
  exact ⟨M, Subgraph.isMaximumMatching_iff_encard_edgeSet_eq_matchingNum.2 ⟨hM, hcard⟩⟩

/-- Every perfect matching is a maximum matching. -/
theorem Subgraph.IsPerfectMatching.isMaximumMatching {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    M.IsMaximumMatching := by
  refine ⟨hM.1, fun M' hM' ↦ ?_⟩
  by_cases hinf : M.edgeSet.encard = ⊤
  · rw [hinf]
    exact le_top
  · have hle : 2 * M'.edgeSet.encard ≤ 2 * M.edgeSet.encard := by
      rw [hM'.two_mul_encard_edgeSet, hM.1.two_mul_encard_edgeSet,
        Subgraph.isSpanning_iff.1 hM.2]
      exact Set.encard_le_encard (Set.subset_univ _)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hinf
    have hM'ne : M'.edgeSet.encard ≠ ⊤ := by
      intro htop
      rw [htop, ← hn] at hle
      have htop2 : (2 : ℕ∞) * ⊤ = ⊤ := ENat.mul_top (by decide)
      have hne : (2 : ℕ∞) * (n : ℕ∞) ≠ ⊤ := by
        exact_mod_cast ENat.natCast_ne_top (2 * n)
      exact hne (top_unique (htop2 ▸ hle))
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hM'ne
    rw [← hm, ← hn] at hle ⊢
    have hnat : 2 * m ≤ 2 * n := by
      exact_mod_cast hle
    exact_mod_cast (by omega : m ≤ n)

/-- Graph isomorphisms preserve maximum matchings. -/
@[simp]
theorem Subgraph.Iso.isMaximumMatching_map (f : G ≃g H) {M : G.Subgraph} :
    (M.map f.toHom).IsMaximumMatching ↔ M.IsMaximumMatching := by
  have hinj : Function.Injective f.toHom := f.injective
  rw [Subgraph.isMaximumMatching_iff_encard_edgeSet_eq_matchingNum,
    Subgraph.isMaximumMatching_iff_encard_edgeSet_eq_matchingNum,
    Subgraph.Iso.isMatching_map, Subgraph.edgeSet_map,
    (Sym2.map.injective hinj).encard_image, matchingNum_congr f]

/-- The vertex cover number is at most twice the matching number. -/
theorem vertexCoverNum_le_two_mul_matchingNum (G : SimpleGraph V) :
    G.vertexCoverNum ≤ 2 * G.matchingNum := by
  by_cases h : G.matchingNum = ⊤
  · rw [h, ENat.mul_top (by decide)]
    exact le_top
  · obtain ⟨M, hM⟩ := G.exists_isMaximumMatching
    have hMf : M.edgeSet.Finite := Set.encard_lt_top_iff.1 <| by
      rw [hM.encard_edgeSet_eq]
      exact lt_top_iff_ne_top.2 h
    calc G.vertexCoverNum
        ≤ M.verts.encard := (hM.isVertexCover_verts hMf).vertexCoverNum_le
      _ = 2 * M.edgeSet.encard := hM.1.two_mul_encard_edgeSet.symm
      _ = 2 * G.matchingNum := by rw [hM.encard_edgeSet_eq]

/-- The matching number is finite if and only if the vertex cover number is finite. -/
theorem matchingNum_ne_top_iff_vertexCoverNum_ne_top (G : SimpleGraph V) :
    G.matchingNum ≠ ⊤ ↔ G.vertexCoverNum ≠ ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ne_top_of_le_ne_top h G.matchingNum_le_vertexCoverNum⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h
  have h2 : (2 : ℕ∞) * G.matchingNum ≠ ⊤ := by
    rw [← hn]
    exact_mod_cast ENat.natCast_ne_top (2 * n)
  exact ne_top_of_le_ne_top h2 G.vertexCoverNum_le_two_mul_matchingNum

/-- A vertex set `c` is a *minimum vertex cover* of `G` if it is a vertex cover and no vertex
cover of `G` has fewer vertices, measured in `ℕ∞`. -/
def IsMinimumVertexCover (G : SimpleGraph V) (c : Set V) : Prop :=
  G.IsVertexCover c ∧ ∀ c' : Set V, G.IsVertexCover c' → c.encard ≤ c'.encard

/-- Restatement of `SimpleGraph.IsMinimumVertexCover` without unfolding. -/
theorem isMinimumVertexCover_def {c : Set V} :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∀ c' : Set V, G.IsVertexCover c' → c.encard ≤ c'.encard :=
  (Iff.rfl)

namespace IsMinimumVertexCover

variable {c c' : Set V}

/-- A minimum vertex cover is a vertex cover. -/
theorem isVertexCover (hc : G.IsMinimumVertexCover c) : G.IsVertexCover c :=
  hc.1

/-- A minimum vertex cover is no larger than any vertex cover, in `ℕ∞`. -/
theorem encard_le (hc : G.IsMinimumVertexCover c) (hc' : G.IsVertexCover c') :
    c.encard ≤ c'.encard :=
  hc.2 c' hc'

/-- A minimum vertex cover is no larger than any finite vertex cover, in `ℕ`. -/
theorem ncard_le (hc : G.IsMinimumVertexCover c) (hc' : G.IsVertexCover c') (hf : c'.Finite) :
    c.ncard ≤ c'.ncard :=
  ENat.natCast_le_natCast.1 <| (Set.ncard_le_encard c).trans <|
    (hc.encard_le hc').trans_eq hf.cast_ncard_eq.symm

end IsMinimumVertexCover

/-- A set is a minimum vertex cover if and only if it is a vertex cover whose size equals the
vertex cover number. -/
theorem isMinimumVertexCover_iff_encard_eq_vertexCoverNum {c : Set V} :
    G.IsMinimumVertexCover c ↔ G.IsVertexCover c ∧ c.encard = G.vertexCoverNum := by
  refine ⟨fun hc ↦ ⟨hc.1, le_antisymm ?_ hc.1.vertexCoverNum_le⟩,
    fun ⟨hc, heq⟩ ↦ ⟨hc, fun c' hc' ↦ heq.symm ▸ hc'.vertexCoverNum_le⟩⟩
  rw [vertexCoverNum]
  exact le_iInf₂ hc.2

/-- A minimum vertex cover attains the vertex cover number. -/
theorem IsMinimumVertexCover.encard_eq {c : Set V} (hc : G.IsMinimumVertexCover c) :
    c.encard = G.vertexCoverNum :=
  (isMinimumVertexCover_iff_encard_eq_vertexCoverNum.1 hc).2

/-- A finite vertex set is a minimum vertex cover if and only if it has minimal `ncard` among all
finite vertex covers. -/
theorem isMinimumVertexCover_iff_forall_ncard_le_of_finite {c : Set V} (hcf : c.Finite) :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∀ c' : Set V, G.IsVertexCover c' → c'.Finite → c.ncard ≤ c'.ncard := by
  refine ⟨fun hc ↦ ⟨hc.1, fun c' hc' hf' ↦ hc.ncard_le hc' hf'⟩,
    fun ⟨hc, hmin⟩ ↦ ⟨hc, fun c' hc' ↦ ?_⟩⟩
  by_cases hf' : c'.Finite
  · rw [← hcf.cast_ncard_eq, ← hf'.cast_ncard_eq]
    exact ENat.natCast_le_natCast.2 (hmin c' hc' hf')
  · rw [Set.Infinite.encard_eq hf']
    exact le_top

/-- On a finite vertex type, minimum vertex covers are characterized by `Set.ncard`. -/
theorem isMinimumVertexCover_iff_forall_ncard_le [Finite V] {c : Set V} :
    G.IsMinimumVertexCover c ↔
      G.IsVertexCover c ∧ ∀ c' : Set V, G.IsVertexCover c' → c.ncard ≤ c'.ncard := by
  rw [isMinimumVertexCover_iff_forall_ncard_le_of_finite (Set.toFinite c)]
  exact and_congr_right fun _ ↦
    ⟨fun h c' hc' ↦ h c' hc' (Set.toFinite c'), fun h c' hc' _ ↦ h c' hc'⟩

/-- Every simple graph has a minimum vertex cover. -/
theorem exists_isMinimumVertexCover (G : SimpleGraph V) :
    ∃ c : Set V, G.IsMinimumVertexCover c := by
  obtain ⟨c, hcard, hc⟩ := G.vertexCoverNum_exists
  exact ⟨c, isMinimumVertexCover_iff_encard_eq_vertexCoverNum.2 ⟨hc, hcard⟩⟩

/-- Graph isomorphisms preserve minimum vertex covers under images. -/
@[simp]
theorem isMinimumVertexCover_image_iso (f : G ≃g H) {c : Set V} :
    H.IsMinimumVertexCover (f '' c) ↔ G.IsMinimumVertexCover c := by
  rw [isMinimumVertexCover_iff_encard_eq_vertexCoverNum,
    isMinimumVertexCover_iff_encard_eq_vertexCoverNum,
    isVertexCover_image_iso, f.injective.encard_image, vertexCoverNum_congr f]

/-- Graph isomorphisms preserve minimum vertex covers under preimages. -/
@[simp]
theorem isMinimumVertexCover_preimage_iso (f : G ≃g H) {c : Set W} :
    G.IsMinimumVertexCover (f ⁻¹' c) ↔ H.IsMinimumVertexCover c := by
  simpa [RelIso.image_eq_preimage_symm] using isMinimumVertexCover_image_iso f.symm (c := c)

/-- A matching whose size equals the size of some vertex cover is maximum. -/
theorem Subgraph.IsMatching.isMaximumMatching_of_encard_eq {M : G.Subgraph} {c : Set V}
    (hM : M.IsMatching) (hc : G.IsVertexCover c) (h : M.edgeSet.encard = c.encard) :
    M.IsMaximumMatching :=
  ⟨hM, fun _ hM' ↦ (hM'.encard_edgeSet_le_encard_of_isVertexCover hc).trans_eq h.symm⟩

/-- A vertex cover whose size equals the size of some matching is minimum. -/
theorem IsVertexCover.isMinimumVertexCover_of_encard_eq {M : G.Subgraph} {c : Set V}
    (hc : G.IsVertexCover c) (hM : M.IsMatching) (h : M.edgeSet.encard = c.encard) :
    G.IsMinimumVertexCover c :=
  ⟨hc, fun _ hc' ↦ h.symm.trans_le (hM.encard_edgeSet_le_encard_of_isVertexCover hc')⟩

/-- Equal sizes of a matching and a vertex cover certify equality of `matchingNum` and
`vertexCoverNum`. -/
theorem matchingNum_eq_vertexCoverNum_of_encard_eq {M : G.Subgraph} {c : Set V}
    (hM : M.IsMatching) (hc : G.IsVertexCover c) (h : M.edgeSet.encard = c.encard) :
    G.matchingNum = G.vertexCoverNum :=
  le_antisymm G.matchingNum_le_vertexCoverNum <|
    hc.vertexCoverNum_le.trans (h.symm.trans_le hM.encard_edgeSet_le_matchingNum)

/-- A matching whose `ncard` equals the `ncard` of a finite vertex cover is maximum. -/
theorem Subgraph.IsMatching.isMaximumMatching_of_ncard_eq {M : G.Subgraph} {c : Set V}
    (hM : M.IsMatching) (hc : G.IsVertexCover c) (hcf : c.Finite)
    (h : M.edgeSet.ncard = c.ncard) : M.IsMaximumMatching := by
  have hMf : M.edgeSet.Finite := Set.encard_lt_top_iff.1 <|
    (hM.encard_edgeSet_le_encard_of_isVertexCover hc).trans_lt hcf.encard_lt_top
  exact hM.isMaximumMatching_of_encard_eq hc <| by
    rw [← hMf.cast_ncard_eq, ← hcf.cast_ncard_eq, h]

/-- A finite vertex cover whose `ncard` equals the `ncard` of some matching is minimum. -/
theorem IsVertexCover.isMinimumVertexCover_of_ncard_eq {M : G.Subgraph} {c : Set V}
    (hc : G.IsVertexCover c) (hM : M.IsMatching) (hcf : c.Finite)
    (h : M.edgeSet.ncard = c.ncard) : G.IsMinimumVertexCover c := by
  have hMf : M.edgeSet.Finite := Set.encard_lt_top_iff.1 <|
    (hM.encard_edgeSet_le_encard_of_isVertexCover hc).trans_lt hcf.encard_lt_top
  exact hc.isMinimumVertexCover_of_encard_eq hM <| by
    rw [← hMf.cast_ncard_eq, ← hcf.cast_ncard_eq, h]

end Extremal

/-! ### Kőnig's theorem for bipartite simple graphs -/

section Konig

/-- Restricting a bipartition of `G` to `G.induce G.support` yields a covering finite bipartition
of `Graph.ofSimpleGraph (G.induce G.support)`. -/
private theorem isBipartition_ofSimpleGraph_induce_support {L R : Set V}
    (hLR : G.IsBipartiteWith L R) [Fintype V(Graph.ofSimpleGraph (G.induce G.support))]
    [DecidablePred (· ∈ L)] [DecidablePred (· ∈ R)] :
    (Graph.ofSimpleGraph (G.induce G.support)).IsBipartition
      (Finset.univ.filter fun x : V(Graph.ofSimpleGraph (G.induce G.support)) ↦ x.1.1 ∈ L)
      (Finset.univ.filter fun x : V(Graph.ofSimpleGraph (G.induce G.support)) ↦ x.1.1 ∈ R) := by
  refine ⟨Finset.disjoint_left.2 fun x hxL hxR ↦ ?_, fun x ↦ ?_, fun {e x y} he ↦ ?_⟩
  · exact Set.disjoint_left.1 hLR.disjoint (Finset.mem_filter.1 hxL).2
      (Finset.mem_filter.1 hxR).2
  · rcases isBipartiteWith_support_subset hLR x.1.2 with hxL | hxR
    · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxL⟩)
    · exact Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxR⟩)
  · have hxy : G.Adj x.1.1 y.1.1 :=
      (Graph.ofSimpleGraph_adj_iff (G := G.induce G.support) x.1 y.1).1 ⟨e, he⟩
    rcases hLR.mem_of_adj hxy with ⟨hxL, hyR⟩ | ⟨hxR, hyL⟩
    · exact Or.inl ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hxL⟩,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hyR⟩⟩
    · exact Or.inr ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hxR⟩,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hyL⟩⟩

/-- Finite-edge case of Kőnig's theorem via the multigraph capacitated matching theorem on
`G.induce G.support`. -/
private theorem exists_isMatching_isVertexCover_encard_eq_of_finite_edgeSet [Finite G.edgeSet]
    (hbip : G.IsBipartite) :
    ∃ (M : G.Subgraph) (c : Set V),
      M.IsMatching ∧ G.IsVertexCover c ∧ M.edgeSet.encard = c.encard := by
  classical
  let H : SimpleGraph G.support := G.induce G.support
  have : Finite G.support := G.finite_support.to_subtype
  let _ : Fintype G.support := Fintype.ofFinite G.support
  let _ : Fintype V(Graph.ofSimpleGraph H) := Fintype.ofFinite _
  let _ : Fintype E(Graph.ofSimpleGraph H) := Fintype.ofFinite _
  obtain ⟨L, R, hLR⟩ := hbip.exists_isBipartiteWith
  have hBip := isBipartition_ofSimpleGraph_induce_support hLR
  obtain ⟨x, C₀, hx, hC₀, hxC₀⟩ :=
    hBip.exists_isCapacitatedMatching_isVertexCover_sum_eq (fun _ ↦ 1)
  let M_edges : Finset E(Graph.ofSimpleGraph H) := Finset.univ.filter fun e ↦ x e ≠ 0
  have hM_graph : (Graph.ofSimpleGraph H).IsMatching (M_edges : Set E(Graph.ofSimpleGraph H)) :=
    hx.supportFinset_isMatching hBip.loopless
  have hcard : M_edges.card = C₀.card := by
    simpa [M_edges, hx.sum_eq_card_support] using hxC₀
  let M₀ : H.Subgraph := H.matchingSubgraph (M_edges : Set E(Graph.ofSimpleGraph H))
  have hM₀ : M₀.IsMatching := (matchingSubgraph_isMatching_iff (H := H) _).2 hM_graph
  let emb : H ↪g G := Embedding.induce G.support
  have hinj : Function.Injective emb.toHom := emb.injective
  let M : G.Subgraph := M₀.map emb.toHom
  let C₁ : Set G.support := Subtype.val '' (C₀ : Set V(Graph.ofSimpleGraph H))
  let C : Set V := Subtype.val '' C₁
  refine ⟨M, C, hM₀.map emb.toHom emb.injective, fun u v huv ↦ ?_, ?_⟩
  · have hC₁ : H.IsVertexCover C₁ :=
      (isVertexCover_ofSimpleGraph_image_iff (H := H)).2 hC₀
    have huv' : H.Adj ⟨u, huv.mem_support_left⟩ ⟨v, huv.mem_support_right⟩ := huv
    rcases hC₁ huv' with hu | hv
    · exact Or.inl ⟨⟨u, huv.mem_support_left⟩, hu, rfl⟩
    · exact Or.inr ⟨⟨v, huv.mem_support_right⟩, hv, rfl⟩
  · have hM_enc : M.edgeSet.encard = (M_edges.card : ℕ∞) := by
      rw [Subgraph.edgeSet_map, (Sym2.map.injective hinj).encard_image,
        edgeSet_matchingSubgraph, Subtype.val_injective.encard_image,
        Set.encard_coe_eq_coe_finsetCard]
    have hC_enc : C.encard = (C₀.card : ℕ∞) := by
      rw [Subtype.val_injective.encard_image, Subtype.val_injective.encard_image,
        Set.encard_coe_eq_coe_finsetCard]
    rw [hM_enc, hC_enc, hcard]

/-- Given a finite vertex cover `F`, builds a finite vertex set `U ⊇ F` such that every vertex
outside `U` shares its neighbourhood in `F` with strictly more than `F.card` vertices of `U`. -/
private theorem exists_finite_twin_window [DecidableEq V] [DecidableRel G.Adj] (F : Finset V) :
    ∃ U : Finset V, F ⊆ U ∧ ∀ v ∉ U,
      F.card < (U.filter fun w ↦ F.filter (G.Adj w) = F.filter (G.Adj v)).card := by
  classical
  let fiber (A : Finset V) : Set V := {v : V | F.filter (G.Adj v) = A}
  have hT_ex : ∀ A : Finset V,
      ∃ T : Finset V, (T : Set V) ⊆ fiber A ∧ ((T : Set V) = fiber A ∨ F.card < T.card) := by
    intro A
    by_cases hfin : (fiber A).Finite
    · exact ⟨hfin.toFinset, hfin.coe_toFinset.subset, Or.inl hfin.coe_toFinset⟩
    · obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hfin (F.card + 1)
      exact ⟨T, hTsub, Or.inr (by omega)⟩
  choose T hTsub hTprop using hT_ex
  refine ⟨F ∪ F.powerset.biUnion T, Finset.subset_union_left, fun v hvU ↦ ?_⟩
  let A : Finset V := F.filter (G.Adj v)
  have hApow : A ∈ F.powerset := Finset.mem_powerset.2 (Finset.filter_subset _ _)
  have hTU : T A ⊆ F ∪ F.powerset.biUnion T :=
    (Finset.subset_biUnion_of_mem T hApow).trans Finset.subset_union_right
  have hgt : F.card < (T A).card := (hTprop A).resolve_left fun hEq ↦
    hvU <| hTU <| Finset.mem_coe.1 <| hEq.symm ▸ (rfl : F.filter (G.Adj v) = A)
  refine hgt.trans_le (Finset.card_le_card fun w hw ↦ ?_)
  exact Finset.mem_filter.2 ⟨hTU hw, hTsub A hw⟩

/-- Lifting a vertex cover of the twin-window induced subgraph `G.induce U` back to `G`
whenever its cardinality does not exceed the reference cover `F`. -/
private theorem isVertexCover_image_of_twin_window [DecidableEq V] [DecidableRel G.Adj]
    {F U : Finset V} (hF : G.IsVertexCover (F : Set V)) (hFU : F ⊆ U)
    (htwin : ∀ v ∉ U,
      F.card < (U.filter fun w ↦ F.filter (G.Adj w) = F.filter (G.Adj v)).card)
    {C' : Set (U : Set V)} (hC' : (G.induce (U : Set V)).IsVertexCover C')
    (hC'le : C'.encard ≤ (F.card : ℕ∞)) :
    G.IsVertexCover (Subtype.val '' C') := by
  let C : Set V := Subtype.val '' C'
  have hC_enc : C.encard = C'.encard := Subtype.val_injective.encard_image C'
  have hCf : C.Finite := Set.encard_lt_top_iff.1 <|
    hC_enc ▸ hC'le.trans_lt (ENat.natCast_lt_top F.card)
  have hCcard : C.ncard ≤ F.card := ENat.natCast_le_natCast.1 <| by
    rw [hCf.cast_ncard_eq, hC_enc]
    exact hC'le
  have hcov_left : ∀ {u v : V}, G.Adj u v → u ∈ F → u ∈ C ∨ v ∈ C := by
    intro u v huv huF
    have huU : u ∈ (U : Set V) := Finset.mem_coe.2 (hFU huF)
    by_cases hvU : v ∈ U
    · rcases hC' (v := ⟨u, huU⟩) (w := ⟨v, Finset.mem_coe.2 hvU⟩) huv with hu | hv
      · exact Or.inl ⟨⟨u, huU⟩, hu, rfl⟩
      · exact Or.inr ⟨⟨v, Finset.mem_coe.2 hvU⟩, hv, rfl⟩
    · let S : Finset V := U.filter fun w ↦ F.filter (G.Adj w) = F.filter (G.Adj v)
      have hnot_sub : ¬ (S : Set V) ⊆ C := fun hsub ↦ by
        have h1 := Set.ncard_le_ncard hsub hCf
        rw [Set.ncard_coe_finset] at h1
        have hgt : F.card < S.card := htwin v hvU
        omega
      obtain ⟨w, hwS, hwC⟩ := Set.not_subset.1 hnot_sub
      obtain ⟨hwU, hweq⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hwS)
      have huN : u ∈ F.filter (G.Adj v) := Finset.mem_filter.2 ⟨huF, huv.symm⟩
      have hwu : G.Adj w u := (Finset.mem_filter.1 (hweq.symm ▸ huN)).2
      rcases hC' (v := ⟨u, huU⟩) (w := ⟨w, Finset.mem_coe.2 hwU⟩) hwu.symm with hu | hw
      · exact Or.inl ⟨⟨u, huU⟩, hu, rfl⟩
      · exact absurd ⟨⟨w, Finset.mem_coe.2 hwU⟩, hw, rfl⟩ hwC
  intro u v huv
  rcases hF huv with hu | hv
  · exact hcov_left huv hu
  · exact (hcov_left huv.symm hv).symm

/-- Twin-reduction step: given a finite vertex cover `C₀` of a bipartite graph `G`, apply Kőnig's
theorem to the finite induced subgraph `G.induce U` given by `exists_finite_twin_window` and lift
its matching and vertex cover back to `G`. -/
private theorem exists_isMatching_isVertexCover_encard_eq_of_finite_cover
    (hbip : G.IsBipartite) {C₀ : Set V} (hC₀ : G.IsVertexCover C₀) (hC₀f : C₀.Finite) :
    ∃ (M : G.Subgraph) (c : Set V),
      M.IsMatching ∧ G.IsVertexCover c ∧ M.edgeSet.encard = c.encard := by
  classical
  let F : Finset V := hC₀f.toFinset
  have hF : G.IsVertexCover (F : Set V) := by simpa [F] using hC₀
  obtain ⟨U, hFU, htwin⟩ := exists_finite_twin_window (G := G) F
  let H : SimpleGraph (U : Set V) := G.induce (U : Set V)
  let emb : H ↪g G := Embedding.induce (U : Set V)
  have hHbip : H.IsBipartite := let ⟨col⟩ := hbip; ⟨col.comp emb.toHom⟩
  obtain ⟨M', C', hM', hC', hEq'⟩ :=
    exists_isMatching_isVertexCover_encard_eq_of_finite_edgeSet hHbip
  have hC'min : H.IsMinimumVertexCover C' := hC'.isMinimumVertexCover_of_encard_eq hM' hEq'
  have hC₀' : H.IsVertexCover {x : (U : Set V) | x.1 ∈ C₀} := fun _ _ hxy ↦ hC₀ hxy
  have hC'le : C'.encard ≤ (F.card : ℕ∞) := by
    refine (hC'min.encard_le hC₀').trans ?_
    rw [← Subtype.val_injective.encard_image, ← Set.encard_coe_eq_coe_finsetCard]
    refine Set.encard_le_encard ?_
    rintro _ ⟨_, hx, rfl⟩
    exact hC₀f.mem_toFinset.2 hx
  refine ⟨M'.map emb.toHom, Subtype.val '' C', hM'.map emb.toHom emb.injective,
    isVertexCover_image_of_twin_window hF hFU htwin hC' hC'le, ?_⟩
  have hinj : Function.Injective emb.toHom := emb.injective
  rw [Subgraph.edgeSet_map, (Sym2.map.injective hinj).encard_image,
    Subtype.val_injective.encard_image, hEq']

/-- **Kőnig's theorem for simple graphs (witness form in `ℕ∞`).** Every bipartite simple graph has
a matching and a vertex cover of equal cardinality in `ℕ∞`. When `G.matchingNum ≠ ⊤` both witnesses
are finite; when `G.matchingNum = ⊤` both are infinite (`encard = ⊤`). -/
theorem IsBipartite.exists_isMatching_isVertexCover_encard_eq (hbip : G.IsBipartite) :
    ∃ (M : G.Subgraph) (c : Set V),
      M.IsMatching ∧ G.IsVertexCover c ∧ M.edgeSet.encard = c.encard := by
  by_cases h : G.matchingNum = ⊤
  · obtain ⟨M, hM, hcard⟩ := exists_infinite_matching_of_matchingNum_eq_top h
    have huniv : (Set.univ : Set V).encard = ⊤ := top_unique <| by
      rw [← hcard]
      exact hM.encard_edgeSet_le_encard_of_isVertexCover isVertexCover_univ
    exact ⟨M, Set.univ, hM, isVertexCover_univ, hcard.trans huniv.symm⟩
  · have hvc : G.vertexCoverNum ≠ ⊤ := G.matchingNum_ne_top_iff_vertexCoverNum_ne_top.1 h
    obtain ⟨C₀, hcard, hC₀⟩ := G.vertexCoverNum_exists
    have hC₀f : C₀.Finite := Set.encard_ne_top_iff.1 (hcard.symm ▸ hvc)
    exact exists_isMatching_isVertexCover_encard_eq_of_finite_cover hbip hC₀ hC₀f

/-- **Kőnig's theorem for simple graphs (witness form in `ℕ`).** Every bipartite simple graph with
finite matching number has a finite matching and a finite vertex cover of equal `ncard`. -/
theorem IsBipartite.exists_isMatching_isVertexCover_ncard_eq (hbip : G.IsBipartite)
    (h : G.matchingNum ≠ ⊤) :
    ∃ (M : G.Subgraph) (c : Set V),
      M.IsMatching ∧ G.IsVertexCover c ∧ M.edgeSet.Finite ∧ c.Finite ∧
        M.edgeSet.ncard = c.ncard := by
  obtain ⟨M, c, hM, hc, heq⟩ := hbip.exists_isMatching_isVertexCover_encard_eq
  have hMf : M.edgeSet.Finite := Set.encard_lt_top_iff.1 <|
    hM.encard_edgeSet_le_matchingNum.trans_lt (lt_top_iff_ne_top.2 h)
  have hcf : c.Finite := Set.encard_lt_top_iff.1 (heq ▸ hMf.encard_lt_top)
  refine ⟨M, c, hM, hc, hMf, hcf, ENat.natCast_inj.1 ?_⟩
  rw [hMf.cast_ncard_eq, hcf.cast_ncard_eq, heq]

/-- **Kőnig's theorem for simple graphs (numerical form).** In every bipartite simple graph, the
matching number equals the vertex cover number in `ℕ∞`. -/
theorem IsBipartite.matchingNum_eq_vertexCoverNum (hbip : G.IsBipartite) :
    G.matchingNum = G.vertexCoverNum := by
  obtain ⟨M, c, hM, hc, heq⟩ := hbip.exists_isMatching_isVertexCover_encard_eq
  exact matchingNum_eq_vertexCoverNum_of_encard_eq hM hc heq

/-- **Kőnig's theorem for simple graphs (extremal form).** Every bipartite simple graph has a
maximum matching and a minimum vertex cover with equal `encard` in `ℕ∞`. -/
theorem IsBipartite.exists_isMaximumMatching_isMinimumVertexCover (hbip : G.IsBipartite) :
    ∃ (M : G.Subgraph) (c : Set V),
      M.IsMaximumMatching ∧ G.IsMinimumVertexCover c ∧ M.edgeSet.encard = c.encard := by
  obtain ⟨M, c, hM, hc, heq⟩ := hbip.exists_isMatching_isVertexCover_encard_eq
  exact ⟨M, c, hM.isMaximumMatching_of_encard_eq hc heq,
    hc.isMinimumVertexCover_of_encard_eq hM heq, heq⟩

end Konig

/-! ### Concrete example -/

-- Non-degenerate witness on `K_{1, 2}`: a single edge is a maximum matching, `{Sum.inl ()}` is a
-- minimum vertex cover, and both `matchingNum` and `vertexCoverNum` equal `1`.
example :
    let G := completeBipartiteGraph Unit (Fin 2)
    have hadj : G.Adj (Sum.inl ()) (Sum.inr 0) := Or.inl ⟨rfl, rfl⟩
    (G.subgraphOfAdj hadj).IsMaximumMatching ∧
      G.IsMinimumVertexCover {Sum.inl ()} ∧
      G.matchingNum = 1 ∧ G.vertexCoverNum = 1 := by
  intro G hadj
  have hM : (G.subgraphOfAdj hadj).IsMatching := Subgraph.IsMatching.subgraphOfAdj hadj
  have hC : G.IsVertexCover {Sum.inl ()} := by
    rintro (⟨⟩ | j) (⟨⟩ | k) huv
    · simp [G] at huv
    · exact Or.inl rfl
    · exact Or.inr rfl
    · simp [G] at huv
  have heq :
      (G.subgraphOfAdj hadj).edgeSet.encard = ({Sum.inl ()} : Set (Unit ⊕ Fin 2)).encard := by
    rw [edgeSet_subgraphOfAdj, Set.encard_singleton, Set.encard_singleton]
  have hMmax := hM.isMaximumMatching_of_encard_eq hC heq
  have hCmin := hC.isMinimumVertexCover_of_encard_eq hM heq
  refine ⟨hMmax, hCmin, ?_, ?_⟩
  · rw [← hMmax.encard_edgeSet_eq, edgeSet_subgraphOfAdj, Set.encard_singleton]
  · rw [← hCmin.encard_eq, Set.encard_singleton]

end SimpleGraph
