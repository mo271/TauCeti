/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Combinatorics.Hypergraph.PairColor.Approximation
public import TauCeti.Combinatorics.Hypergraph.PairColor.Graph.Energy
public import TauCeti.Combinatorics.Regularity.Graph.StrongRegularity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Data.Finset.Basic

/-!
# Pair-color regularity and strong approximation on simple graphs

This module compares the irregular-pair sets, strong regularity witnesses, and regular
approximation theorem of pair-color systems with the corresponding graph-regularity notions on a
simple graph.

In one direction, any self-dual color `c₀` (`T.rev c₀ = c₀`) of a pair-color system `T` defines a
simple graph `T.toSimpleGraph c₀ hc₀`. This is a left inverse to `SimpleGraph.toPairColorSystem`
on the edge color `true` (and recovers the complement `Gᶜ` on `false`), translates `c₀`-density
between disjoint sets into `SimpleGraph.edgeDensity`, and transfers pair-color regularity on
disjoint pairs to both `SimpleGraph.IsUniform` (at any strictly larger parameter) and graph
pair-color regularity (at the same parameter).

In the other direction, for a simple graph `G` and vertex partition `P`, the irregular pairs
`G.toPairColorSystem.irregularPairs ε P` are sandwiched between `P.nonUniforms G ε` and
`P.nonUniforms G ε'` for any `ε < ε'`. For an equipartition `P`, this translates between
`Finpartition.IsUniform G ε` and the pair-color irregular-pair mass bound up to explicit universal
constants (`4` forward, `8` backward), with no host-size threshold. Combining this with the energy
comparison in `TauCeti.Combinatorics.Hypergraph.PairColor.Graph.Energy` translates strong
regularity witnesses `SimpleGraph.StrongRegular` into pair-color strong regularity bounds.

Finally, specializing `TauCeti.PairColorSystem.exists_refining_equipartition_lowerSkeletonRegular`
to `G.toPairColorSystem` yields the two-dimensional graph shadow
`SimpleGraph.exists_strong_regular_approximation`: an equitable refinement `P ≤ P₀` of bounded
size and an approximating simple graph `G'` differing from `G` in at most `(α / 2) |V|²` edges
such that every pair of distinct cells of `P` is regular for `G'` at the scheduled scale
`F (#P.parts + 3)` and `P.nonUniforms G' ε' = ∅` for every `ε' > F (#P.parts + 3)`.

## Main declarations

* `TauCeti.PairColorSystem.toSimpleGraph`: the simple graph of a self-dual pair color.
* `TauCeti.PairColorSystem.IsRegularPair.toSimpleGraph` and
  `TauCeti.PairColorSystem.IsRegularPair.isUniform_toSimpleGraph`: regularity transfer to
  `toSimpleGraph` on disjoint pairs.
* `SimpleGraph.irregularPairs_toPairColorSystem_subset_nonUniforms` and
  `SimpleGraph.nonUniforms_subset_irregularPairs_toPairColorSystem`: inclusion sandwich between
  pair-color irregular pairs and graph non-uniform pairs.
* `SimpleGraph.sum_irregularPairs_toPairColorSystem_le_of_isUniform` and
  `SimpleGraph.isUniform_of_sum_irregularPairs_toPairColorSystem_le`: quantitative equivalence
  between `Finpartition.IsUniform` and small irregular-pair mass for equipartitions.
* `SimpleGraph.two_mul_card_symmDiff_edgeFinset`: exact factor-of-two relation between graph edge
  edits and pair-color edits.
* `SimpleGraph.exists_strong_regular_approximation`: graph regular approximation from lower-skeleton
  strong regular approximation.

## References

* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
* Y. Zhao, *Graph Theory and Additive Combinatorics*, Cambridge University Press (2023), ch. 2.
-/

public section

open Finset TauCeti

/-! ### Simple graphs extracted from a self-dual pair color -/

namespace TauCeti.PairColorSystem

variable {κ V : Type*}

/-- The simple graph whose edges are the vertex pairs assigned a fixed self-dual color `c₀`
(`T.rev c₀ = c₀`) by a pair-color system `T`. -/
def toSimpleGraph (T : PairColorSystem κ V) (c₀ : κ) (hc₀ : T.rev c₀ = c₀) : SimpleGraph V where
  Adj u v := ∃ h : u ≠ v, T.color ⟨(u, v), h⟩ = c₀
  symm := ⟨fun u v ⟨hne, hc⟩ ↦
    ⟨hne.symm, by simpa [hc, hc₀] using T.color_rev ⟨(u, v), hne⟩⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ ↦ h rfl⟩

/-- Adjacency in `T.toSimpleGraph c₀ hc₀` unfolds to having pair color `c₀`. -/
theorem toSimpleGraph_adj_iff (T : PairColorSystem κ V) (c₀ : κ) (hc₀ : T.rev c₀ = c₀)
    (u v : V) :
    (T.toSimpleGraph c₀ hc₀).Adj u v ↔ ∃ h : u ≠ v, T.color ⟨(u, v), h⟩ = c₀ :=
  Iff.rfl

instance instDecidableRelToSimpleGraph [DecidableEq V] [DecidableEq κ] (T : PairColorSystem κ V)
    (c₀ : κ) (hc₀ : T.rev c₀ = c₀) : DecidableRel (T.toSimpleGraph c₀ hc₀).Adj :=
  fun u v ↦ decidable_of_iff (∃ h : u ≠ v, T.color ⟨(u, v), h⟩ = c₀)
    (toSimpleGraph_adj_iff T c₀ hc₀ u v).symm

/-- Adjacency in `T.toSimpleGraph c₀ hc₀` is equivalent to `T.colorOfPair u v = some c₀`. -/
@[simp]
theorem toSimpleGraph_adj (T : PairColorSystem κ V) (c₀ : κ) (hc₀ : T.rev c₀ = c₀) (u v : V) :
    (T.toSimpleGraph c₀ hc₀).Adj u v ↔ T.colorOfPair u v = some c₀ :=
  (T.colorOfPair_eq_some_iff u v c₀).symm

/-- Between disjoint sets, the edge density of `T.toSimpleGraph c₀ hc₀` equals the pair-color
density of `c₀` in `T`. -/
theorem edgeDensity_toSimpleGraph (T : PairColorSystem κ V) (c₀ : κ) (hc₀ : T.rev c₀ = c₀)
    [DecidableRel (T.toSimpleGraph c₀ hc₀).Adj] {s t : Finset V} (hst : Disjoint s t) :
    (T.toSimpleGraph c₀ hc₀).edgeDensity s t = pairColorDensity T c₀ s t := by
  classical
  rw [pairColorDensity_def, filter_ne_product_of_disjoint hst, SimpleGraph.edgeDensity_def,
    SimpleGraph.interedges_def, card_product, Nat.cast_mul]
  congr 3
  ext p
  simp [toSimpleGraph_adj]

/-- A pair of disjoint sets that is `ε`-regular for `T` is `ε'`-uniform for `T.toSimpleGraph c₀ hc₀`
at every strictly larger parameter `ε' > ε`. -/
theorem IsRegularPair.isUniform_toSimpleGraph {T : PairColorSystem κ V} {ε ε' : ℝ}
    {s t : Finset V} (h : T.IsRegularPair ε s t) (c₀ : κ) (hc₀ : T.rev c₀ = c₀)
    [DecidableRel (T.toSimpleGraph c₀ hc₀).Adj] (hst : Disjoint s t) (hε : ε < ε') :
    (T.toSimpleGraph c₀ hc₀).IsUniform ε' s t := by
  intro s' hs' t' ht' hs ht
  have hs₀ : ε * #s ≤ #s' :=
    (mul_le_mul_of_nonneg_right hε.le (Nat.cast_nonneg _)).trans (by rwa [mul_comm])
  have ht₀ : ε * #t ≤ #t' :=
    (mul_le_mul_of_nonneg_right hε.le (Nat.cast_nonneg _)).trans (by rwa [mul_comm])
  have hd := isRegularPair_iff.mp h c₀ s' hs' t' ht' hs₀ ht₀
  rw [T.edgeDensity_toSimpleGraph c₀ hc₀ (hst.mono hs' ht'),
    T.edgeDensity_toSimpleGraph c₀ hc₀ hst]
  exact hd.trans_lt hε

/-- Projecting a regular pair of disjoint sets onto a single self-dual color `c₀` yields a regular
pair for the resulting simple graph's two-color system at the exact same parameter `ε`. -/
theorem IsRegularPair.toSimpleGraph {T : PairColorSystem κ V} {ε : ℝ} {s t : Finset V}
    (h : T.IsRegularPair ε s t) (c₀ : κ) (hc₀ : T.rev c₀ = c₀)
    [DecidableRel (T.toSimpleGraph c₀ hc₀).Adj] (hst : Disjoint s t) :
    (T.toSimpleGraph c₀ hc₀).toPairColorSystem.IsRegularPair ε s t := by
  classical
  have hε0 : 0 ≤ ε := have : Nonempty κ := ⟨c₀⟩; h.nonneg
  refine isRegularPair_iff.mpr fun c s' hs' t' ht' hs ht ↦ ?_
  have htrue : |((T.toSimpleGraph c₀ hc₀).edgeDensity s' t' : ℝ) -
      (T.toSimpleGraph c₀ hc₀).edgeDensity s t| ≤ ε := by
    rw [T.edgeDensity_toSimpleGraph c₀ hc₀ (hst.mono hs' ht'),
      T.edgeDensity_toSimpleGraph c₀ hc₀ hst]
    exact isRegularPair_iff.mp h c₀ s' hs' t' ht' hs ht
  cases c
  · rw [(T.toSimpleGraph c₀ hc₀).pairColorDensity_toPairColorSystem_false (hst.mono hs' ht'),
      (T.toSimpleGraph c₀ hc₀).pairColorDensity_toPairColorSystem_false hst]
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · simp [subset_empty.1 hs', hε0]
    rcases t.eq_empty_or_nonempty with rfl | htne
    · simp [subset_empty.1 ht', hε0]
    have ⟨x, hx⟩ := hsne
    have ⟨y, hy⟩ := htne
    obtain ⟨hs'ne, ht'ne⟩ := h.nonempty_of_exists_ne
      ⟨x, hx, y, hy, fun hxy ↦ Finset.disjoint_left.1 hst hx (hxy ▸ hy)⟩ hs' ht' hs ht
    -- Complement densities sum to `1` with edge densities on disjoint nonempty sets.
    have h1 : ((T.toSimpleGraph c₀ hc₀).edgeDensity s' t' : ℝ) +
        (T.toSimpleGraph c₀ hc₀)ᶜ.edgeDensity s' t' = 1 := by
      exact_mod_cast (T.toSimpleGraph c₀ hc₀).edgeDensity_add_edgeDensity_compl
        hs'ne ht'ne (hst.mono hs' ht')
    have h2 : ((T.toSimpleGraph c₀ hc₀).edgeDensity s t : ℝ) +
        (T.toSimpleGraph c₀ hc₀)ᶜ.edgeDensity s t = 1 := by
      exact_mod_cast (T.toSimpleGraph c₀ hc₀).edgeDensity_add_edgeDensity_compl hsne htne hst
    have hsub : ((T.toSimpleGraph c₀ hc₀)ᶜ.edgeDensity s' t' : ℝ) -
        (T.toSimpleGraph c₀ hc₀)ᶜ.edgeDensity s t =
        -(((T.toSimpleGraph c₀ hc₀).edgeDensity s' t' : ℝ) -
          (T.toSimpleGraph c₀ hc₀).edgeDensity s t) := by linarith
    rwa [hsub, abs_neg]
  · rw [(T.toSimpleGraph c₀ hc₀).pairColorDensity_toPairColorSystem_true (hst.mono hs' ht'),
      (T.toSimpleGraph c₀ hc₀).pairColorDensity_toPairColorSystem_true hst]
    exact htrue

end TauCeti.PairColorSystem

namespace TauCeti.PairSkeleton3

variable {κ V : Type*} [Fintype V] [DecidableEq V]

/-- Every pair of distinct cells in an `ε`-regular lower skeleton is `ε'`-uniform for the simple
graph of any self-dual color, whenever `ε < ε'`. -/
theorem IsPairColorRegular.nonUniforms_toSimpleGraph_eq_empty {S : PairSkeleton3 κ V} {ε ε' : ℝ}
    (h : S.IsPairColorRegular ε) (c₀ : κ) (hc₀ : S.pairColors.rev c₀ = c₀)
    [DecidableRel (S.pairColors.toSimpleGraph c₀ hc₀).Adj] (hε : ε < ε') :
    S.vertexPart.nonUniforms (S.pairColors.toSimpleGraph c₀ hc₀) ε' = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun ⟨A, B⟩ hAB ↦ ?_
  obtain ⟨hA, hB, hne, hnu⟩ := (S.vertexPart.mk_mem_nonUniforms _).1 hAB
  exact hnu ((h.isRegularPair hA hB).isUniform_toSimpleGraph c₀ hc₀
    (S.vertexPart.disjoint hA hB hne) hε)

/-- An `ε`-regular lower skeleton yields an `ε'`-uniform partition for the simple graph of any
self-dual color, whenever `ε < ε'`. -/
theorem IsPairColorRegular.isUniform_toSimpleGraph {S : PairSkeleton3 κ V} {ε ε' : ℝ}
    (h : S.IsPairColorRegular ε) (c₀ : κ) (hc₀ : S.pairColors.rev c₀ = c₀)
    [DecidableRel (S.pairColors.toSimpleGraph c₀ hc₀).Adj] (hε : ε < ε') :
    S.vertexPart.IsUniform (S.pairColors.toSimpleGraph c₀ hc₀) ε' := by
  rw [Finpartition.IsUniform, h.nonUniforms_toSimpleGraph_eq_empty c₀ hc₀ hε, card_empty,
    Nat.cast_zero]
  rcases isEmpty_or_nonempty V with hV | hV
  · have hP : S.vertexPart.parts = ∅ :=
      Finpartition.parts_eq_empty_iff.2 (by simp [univ_eq_empty])
    simp [hP]
  · have : Nonempty κ := ⟨c₀⟩
    exact mul_nonneg (Nat.cast_nonneg _) (h.nonneg.trans hε.le)

/-- A lower skeleton regular for a schedule `F` yields an `ε'`-uniform partition for the simple
graph of any self-dual color at every parameter `ε'` strictly exceeding the scheduled value. -/
theorem LowerSkeletonRegular.isUniform_toSimpleGraph [Fintype κ] {S : PairSkeleton3 κ V}
    {F : ℕ → ℝ} (h : S.LowerSkeletonRegular F) (c₀ : κ) (hc₀ : S.pairColors.rev c₀ = c₀)
    [DecidableRel (S.pairColors.toSimpleGraph c₀ hc₀).Adj] {ε' : ℝ}
    (hε : F (#S.vertexPart.parts + Fintype.card κ) < ε') :
    S.vertexPart.IsUniform (S.pairColors.toSimpleGraph c₀ hc₀) ε' :=
  IsPairColorRegular.isUniform_toSimpleGraph (lowerSkeletonRegular_iff.mp h) c₀ hc₀ hε

end TauCeti.PairSkeleton3

/-! ### Irregular pairs, non-uniform pairs, and strong regular approximation -/

namespace SimpleGraph

variable {V : Type*}

/-- Recovering the edge color `true` from `G.toPairColorSystem` returns `G`. -/
@[simp]
theorem toSimpleGraph_toPairColorSystem_true (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.toPairColorSystem.toSimpleGraph true (G.toPairColorSystem_rev true) = G := by
  ext u v
  simp

/-- Recovering the non-edge color `false` from `G.toPairColorSystem` returns the complement `Gᶜ`. -/
@[simp]
theorem toSimpleGraph_toPairColorSystem_false (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.toPairColorSystem.toSimpleGraph false (G.toPairColorSystem_rev false) = Gᶜ := by
  ext u v
  simp

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every pair of distinct cells that fails pair-color `ε`-regularity for `G.toPairColorSystem`
also fails `G.IsUniform ε`. -/
theorem irregularPairs_toPairColorSystem_subset_nonUniforms (P : Finpartition (univ : Finset V))
    (ε : ℝ) :
    G.toPairColorSystem.irregularPairs ε P ⊆ P.nonUniforms G ε := by
  intro ⟨A, B⟩ hAB
  obtain ⟨hA, hB, hne, hirreg⟩ := G.toPairColorSystem.mem_irregularPairs.1 hAB
  refine (P.mk_mem_nonUniforms G).2 ⟨hA, hB, hne, fun hunif ↦ ?_⟩
  exact hirreg (hunif.isRegularPair_ofGraph (P.disjoint hA hB hne))

/-- Every pair of distinct cells that fails `G.IsUniform ε'` fails pair-color `ε`-regularity at
every strictly smaller parameter `ε < ε'`. -/
theorem nonUniforms_subset_irregularPairs_toPairColorSystem (P : Finpartition (univ : Finset V))
    {ε ε' : ℝ} (hε : ε < ε') :
    P.nonUniforms G ε' ⊆ G.toPairColorSystem.irregularPairs ε P := by
  intro ⟨A, B⟩ hAB
  obtain ⟨hA, hB, hne, hnu⟩ := (P.mk_mem_nonUniforms G).1 hAB
  refine G.toPairColorSystem.mem_irregularPairs.2 ⟨hA, hB, hne, fun hreg ↦ ?_⟩
  exact hnu (hreg.isUniform (P.disjoint hA hB hne) hε)

/-- For an equipartition `P` that is `ε`-uniform for `G` (`0 ≤ ε`), the ordered pairs of vertices
in irregular blocks of `G.toPairColorSystem` have total mass at most `4 ε |V|²`. -/
theorem sum_irregularPairs_toPairColorSystem_le_of_isUniform {P : Finpartition (univ : Finset V)}
    (hP : P.IsEquipartition) {ε : ℝ} (hε : 0 ≤ ε) (hU : P.IsUniform G ε) :
    ∑ AB ∈ G.toPairColorSystem.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤
      4 * ε * (Fintype.card V : ℝ) ^ 2 := by
  rcases lt_or_ge #P.parts 2 with ht | ht
  · have hirreg : G.toPairColorSystem.irregularPairs ε P = ∅ :=
      eq_empty_iff_forall_notMem.2 fun ⟨A, B⟩ hAB ↦ by
        obtain ⟨hA, hB, hne, -⟩ := G.toPairColorSystem.mem_irregularPairs.1 hAB
        exact ht.not_ge (one_lt_card.2 ⟨A, hA, B, hB, hne⟩)
    rw [hirreg, sum_empty]; positivity
  · -- Each cell of an equipartition with `≥ 2` parts has size at most `2 |V| / #P.parts`.
    have : (0 : ℝ) < #P.parts := Nat.cast_pos.2 (by omega)
    have hq_pos : 1 ≤ Fintype.card V / #P.parts :=
      Nat.div_pos (P.card_parts_le_card.trans_eq card_univ) (by omega)
    have hpart_le (A : Finset V) (hA : A ∈ P.parts) :
        (#A : ℝ) * #P.parts ≤ 2 * (Fintype.card V : ℝ) := by
      have h1 : #A ≤ Fintype.card V / #P.parts + 1 := by
        simpa [card_univ] using hP.card_part_le_average_add_one hA
      have h2 : #A * #P.parts ≤ 2 * Fintype.card V :=
        (Nat.mul_le_mul_right _ (by omega : #A ≤ 2 * (Fintype.card V / #P.parts))).trans <| by
          rw [mul_assoc]; exact Nat.mul_le_mul_left 2 (Nat.div_mul_le_self _ _)
      exact_mod_cast h2
    -- Multiply by `(#P.parts)²` and bound `#(irregularPairs) ≤ #(nonUniforms) ≤ ε * (#P.parts)²`.
    have hmul : (∑ AB ∈ G.toPairColorSystem.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ)) *
        (#P.parts : ℝ) ^ 2 ≤ (4 * ε * (Fintype.card V : ℝ) ^ 2) * (#P.parts : ℝ) ^ 2 := by
      calc (∑ AB ∈ G.toPairColorSystem.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ)) *
              (#P.parts : ℝ) ^ 2
          = ∑ AB ∈ G.toPairColorSystem.irregularPairs ε P,
              ((#AB.1 : ℝ) * #P.parts) * ((#AB.2 : ℝ) * #P.parts) := by
            rw [sum_mul]; exact sum_congr rfl fun _ _ ↦ by ring
        _ ≤ ∑ _AB ∈ G.toPairColorSystem.irregularPairs ε P,
              (2 * (Fintype.card V : ℝ)) * (2 * (Fintype.card V : ℝ)) :=
            sum_le_sum fun AB hAB ↦
              let ⟨hA, hB, _, _⟩ := G.toPairColorSystem.mem_irregularPairs.1 hAB
              mul_le_mul (hpart_le AB.1 hA) (hpart_le AB.2 hB) (by positivity) (by positivity)
        _ = (#(G.toPairColorSystem.irregularPairs ε P) : ℝ) * (4 * (Fintype.card V : ℝ) ^ 2) := by
            rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ (#(P.nonUniforms G ε) : ℝ) * (4 * (Fintype.card V : ℝ) ^ 2) := by
            gcongr; exact G.irregularPairs_toPairColorSystem_subset_nonUniforms P ε
        _ ≤ ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) * ε * (4 * (Fintype.card V : ℝ) ^ 2) := by
            gcongr; exact hU
        _ ≤ ((#P.parts : ℝ) ^ 2) * ε * (4 * (Fintype.card V : ℝ) ^ 2) := by
            have hleR : ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) ≤ (#P.parts : ℝ) ^ 2 := by
              rw [sq]; exact_mod_cast Nat.mul_le_mul_left #P.parts (Nat.sub_le _ _)
            gcongr
        _ = (4 * ε * (Fintype.card V : ℝ) ^ 2) * (#P.parts : ℝ) ^ 2 := by ring
    exact le_of_mul_le_mul_right hmul (by positivity)

/-- Conversely, for an equipartition `P`, if the irregular pairs of `G.toPairColorSystem` at scale
`ε` cover at most `η |V|²` ordered vertex pairs, then `P` is `δ`-uniform for `G` whenever `ε < δ`
and `8 η ≤ δ`. -/
theorem isUniform_of_sum_irregularPairs_toPairColorSystem_le {P : Finpartition (univ : Finset V)}
    (hP : P.IsEquipartition) {ε η δ : ℝ} (hε : ε < δ) (hη : 8 * η ≤ δ)
    (hsum : ∑ AB ∈ G.toPairColorSystem.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤
      η * (Fintype.card V : ℝ) ^ 2) :
    P.IsUniform G δ := by
  rw [Finpartition.IsUniform]
  rcases lt_or_ge #P.parts 2 with ht | ht
  · have hnu : P.nonUniforms G δ = ∅ := eq_empty_iff_forall_notMem.2 fun ⟨A, B⟩ hAB ↦ by
      obtain ⟨hA, hB, hne, -⟩ := (P.mk_mem_nonUniforms G).1 hAB
      exact ht.not_ge (one_lt_card.2 ⟨A, hA, B, hB, hne⟩)
    have hzero : #P.parts - 1 = 0 := by omega
    simp [hnu, hzero]
  · -- Each cell of an equipartition with `≥ 2` parts has size at least `|V| / (2 #P.parts)`.
    have hcard : #P.parts ≤ Fintype.card V := P.card_parts_le_card.trans_eq card_univ
    have hVpos : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 (by omega)
    have hq_pos : 1 ≤ Fintype.card V / #P.parts := Nat.div_pos hcard (by omega)
    have hn_le_part (A : Finset V) (hA : A ∈ P.parts) :
        (Fintype.card V : ℝ) ≤ 2 * (#A : ℝ) * #P.parts := by
      have h1 : Fintype.card V / #P.parts ≤ #A := by
        simpa [card_univ] using hP.average_le_card_part hA
      have hmod : Fintype.card V % #P.parts < #P.parts := Nat.mod_lt _ (by omega)
      have hdiv := Nat.div_add_mod (Fintype.card V) #P.parts
      exact_mod_cast (by nlinarith : Fintype.card V ≤ 2 * #A * #P.parts)
    have ht2_le : (#P.parts : ℝ) ^ 2 ≤ 2 * ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) := by
      have hnat : #P.parts * #P.parts ≤ 2 * (#P.parts * (#P.parts - 1)) := by
        rw [← mul_left_comm]; exact Nat.mul_le_mul_left _ (by omega)
      rw [sq]; exact_mod_cast hnat
    have hsub_sum : ∑ AB ∈ P.nonUniforms G δ, (#AB.1 * #AB.2 : ℝ) ≤ η * (Fintype.card V : ℝ) ^ 2 :=
      (sum_le_sum_of_subset_of_nonneg (G.nonUniforms_subset_irregularPairs_toPairColorSystem P hε)
        fun _ _ _ ↦ by positivity).trans hsum
    have : 0 ≤ ∑ AB ∈ P.nonUniforms G δ, (#AB.1 * #AB.2 : ℝ) :=
      sum_nonneg fun _ _ ↦ by positivity
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2)
    calc (#(P.nonUniforms G δ) : ℝ) * (Fintype.card V : ℝ) ^ 2
        = ∑ _AB ∈ P.nonUniforms G δ, (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := by
          rw [sum_const, nsmul_eq_mul, sq]
      _ ≤ ∑ AB ∈ P.nonUniforms G δ,
            (2 * (#AB.1 : ℝ) * #P.parts) * (2 * (#AB.2 : ℝ) * #P.parts) :=
          sum_le_sum fun AB hAB ↦
            let ⟨hA, hB, _, _⟩ := (P.mk_mem_nonUniforms G).1 hAB
            mul_le_mul (hn_le_part AB.1 hA) (hn_le_part AB.2 hB) hVpos.le (by positivity)
      _ = 4 * (#P.parts : ℝ) ^ 2 * ∑ AB ∈ P.nonUniforms G δ, (#AB.1 * #AB.2 : ℝ) := by
          rw [mul_sum]; exact sum_congr rfl fun _ _ ↦ by ring
      _ ≤ 4 * (2 * ((#P.parts * (#P.parts - 1) : ℕ) : ℝ)) * (η * (Fintype.card V : ℝ) ^ 2) := by
          gcongr
      _ = ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) * (8 * η) * (Fintype.card V : ℝ) ^ 2 := by ring
      _ ≤ ((#P.parts * (#P.parts - 1) : ℕ) : ℝ) * δ * (Fintype.card V : ℝ) ^ 2 := by gcongr

/-- Specialization of `isUniform_of_sum_irregularPairs_toPairColorSystem_le` at equal mass and
regularity tolerance `ε > 0`: small pair-color irregular mass implies `8 ε`-uniformity. -/
theorem isUniform_of_sum_irregularPairs_toPairColorSystem_le_self
    {P : Finpartition (univ : Finset V)} (hP : P.IsEquipartition) {ε : ℝ} (hε : 0 < ε)
    (hsum : ∑ AB ∈ G.toPairColorSystem.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤
      ε * (Fintype.card V : ℝ) ^ 2) :
    P.IsUniform G (8 * ε) :=
  G.isUniform_of_sum_irregularPairs_toPairColorSystem_le hP (by linarith) le_rfl hsum

variable {G} in
/-- A strong graph regularity witness gives the pair-color irregular-pair mass bound on its coarse
partition. -/
theorem StrongRegular.sum_irregularPairs_toPairColorSystem_le_coarse
    {P Q : Finpartition (univ : Finset V)} {ε : ℝ} {F : ℕ → ℝ} {l₀ : ℕ}
    (h : G.StrongRegular P Q ε F l₀) :
    ∑ AB ∈ G.toPairColorSystem.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤
      4 * ε * (Fintype.card V : ℝ) ^ 2 :=
  G.sum_irregularPairs_toPairColorSystem_le_of_isUniform h.equitP
    ((sub_nonneg.2 (G.weightedEnergy_mono_of_refines h.refines)).trans h.energyClose) h.regP

variable {G} in
/-- A strong graph regularity witness gives the pair-color irregular-pair mass bound on its fine
partition at the scheduled scale `F #P.parts`. -/
theorem StrongRegular.sum_irregularPairs_toPairColorSystem_le_fine
    {P Q : Finpartition (univ : Finset V)} {ε : ℝ} {F : ℕ → ℝ} {l₀ : ℕ}
    (h : G.StrongRegular P Q ε F l₀) (hF : 0 ≤ F #P.parts) :
    ∑ AB ∈ G.toPairColorSystem.irregularPairs (F #P.parts) Q, (#AB.1 * #AB.2 : ℝ) ≤
      4 * F #P.parts * (Fintype.card V : ℝ) ^ 2 :=
  G.sum_irregularPairs_toPairColorSystem_le_of_isUniform h.equitQ hF h.regQ

variable {G} in
/-- A strong graph regularity witness bounds the pair-color energy increment by `2 ε + 4 / |V|`. -/
theorem StrongRegular.energy_toPairColorSystem_sub_le
    {P Q : Finpartition (univ : Finset V)} {ε : ℝ} {F : ℕ → ℝ} {l₀ : ℕ}
    (h : G.StrongRegular P Q ε F l₀) :
    G.toPairColorSystem.energy Q - G.toPairColorSystem.energy P ≤ 2 * ε + 4 / Fintype.card V :=
  G.energy_toPairColorSystem_sub_le_of_weightedEnergy_sub_le h.energyClose

/-- Twice the number of edges in the symmetric difference of two graphs equals the number of
ordered distinct vertex pairs on which their pair-color systems disagree. -/
theorem two_mul_card_symmDiff_edgeFinset (G' : SimpleGraph V) [DecidableRel G'.Adj] :
    2 * #(symmDiff G.edgeFinset G'.edgeFinset) =
      #{p : {p : V × V // p.1 ≠ p.2} |
        G.toPairColorSystem.color p ≠ G'.toPairColorSystem.color p} := by
  have hdisj : Disjoint (G.edgeFinset \ G'.edgeFinset) (G'.edgeFinset \ G.edgeFinset) :=
    disjoint_sdiff_sdiff
  have h1 : 2 * #(G.edgeFinset \ G'.edgeFinset) =
      #((univ : Finset (V × V)).filter fun (x, y) ↦ (G \ G').Adj x y) := by
    rw [← edgeFinset_sdiff]
    convert (G \ G').two_mul_card_edgeFinset
  have h2 : 2 * #(G'.edgeFinset \ G.edgeFinset) =
      #((univ : Finset (V × V)).filter fun (x, y) ↦ (G' \ G).Adj x y) := by
    rw [← edgeFinset_sdiff]
    convert (G' \ G).two_mul_card_edgeFinset
  have hfilt_disj : Disjoint
      ((univ : Finset (V × V)).filter fun (x, y) ↦ (G \ G').Adj x y)
      ((univ : Finset (V × V)).filter fun (x, y) ↦ (G' \ G).Adj x y) := by
    rw [disjoint_filter]
    intro p _ hA hB
    exact hA.2 hB.1
  have h2mul : 2 * #(symmDiff G.edgeFinset G'.edgeFinset) =
      #((univ : Finset (V × V)).filter fun p ↦ ¬(G.Adj p.1 p.2 ↔ G'.Adj p.1 p.2)) := by
    rw [symmDiff_def, card_union_of_disjoint hdisj, mul_add, h1, h2,
      ← card_union_of_disjoint hfilt_disj]
    congr 1
    ext ⟨x, y⟩
    simp only [mem_union, mem_filter, mem_univ, true_and, sdiff_adj]
    tauto
  rw [h2mul]
  refine Finset.card_bij (fun p hp ↦ ⟨p, ?_⟩) ?_ ?_ ?_
  · have hiff := (mem_filter.1 hp).2
    intro heq
    rw [heq] at hiff
    exact hiff ⟨fun h ↦ (G.loopless.irrefl _ h).elim, fun h ↦ (G'.loopless.irrefl _ h).elim⟩
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, toPairColorSystem_color, ne_eq,
      decide_eq_decide]
    exact (mem_filter.1 hp).2
  · intro p₁ _ p₂ _ h
    exact congrArg Subtype.val h
  · intro ⟨p, hne⟩ hp
    refine ⟨p, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
    simpa [toPairColorSystem_color, decide_eq_decide] using (mem_filter.1 hp).2

/-- **Two-dimensional graph shadow of pair-color strong regular approximation.** Given an
equipartition `P₀` of a simple graph `G` on at least `pairApproximationBound 2 α F #P₀.parts`
vertices, an edit budget `α > 0`, and a positive schedule `F`, there exist an equitable refinement
`P ≤ P₀` of bounded size and an approximating simple graph `G'` differing from `G` on at most
`(α / 2) |V|²` edges such that every pair of distinct cells of `P` is `F (#P.parts + 3)`-regular
for `G'.toPairColorSystem`, and `P` has no `ε'`-non-uniform pairs for `G'` at any parameter
`ε' > F (#P.parts + 3)`. -/
theorem exists_strong_regular_approximation (P₀ : Finpartition (univ : Finset V))
    (hP₀ : P₀.IsEquipartition) {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    (hV : pairApproximationBound 2 α F #P₀.parts ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (G' : SimpleGraph V),
      P ≤ P₀ ∧ P.IsEquipartition ∧
      #P.parts ≤ pairApproximationPartsBound 2 α F #P₀.parts ∧
      ∀ [DecidableRel G'.Adj],
        (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B →
          G'.toPairColorSystem.IsRegularPair (F (#P.parts + 3)) A B) ∧
        (∀ ε', F (#P.parts + 3) < ε' → P.nonUniforms G' ε' = ∅ ∧ P.IsUniform G' ε') ∧
        (#(symmDiff G'.edgeFinset G.edgeFinset) : ℝ) ≤ α / 2 * (Fintype.card V : ℝ) ^ 2 := by
  have hV' : pairApproximationBound (Fintype.card Bool) α F #P₀.parts ≤ Fintype.card V := by
    simpa using hV
  -- Obtain a lower-skeleton regular pair-color approximation on the `Option Bool` palette.
  obtain ⟨P, T, hPP₀, hP, hPcard, hrev, hlower, hedit⟩ :=
    G.toPairColorSystem.exists_refining_equipartition_lowerSkeletonRegular P₀ hP₀ hα hF hV'
  have hrev_true : T.rev (some true) = some true := by rw [hrev]; simp
  set G' := T.toSimpleGraph (some true) hrev_true
  refine ⟨P, G', hPP₀, hP, by simpa using hPcard, ?_⟩
  intro _
  -- Transfer lower-skeleton regularity to `G'`.
  have hreg_all :
      (⟨P, T⟩ : PairSkeleton3 (Option Bool) V).IsPairColorRegular (F (#P.parts + 3)) := by
    simpa [PairSkeleton3.lowerSkeletonRegular_iff] using hlower
  refine ⟨fun A hA B hB hAB ↦
      (hreg_all.isRegularPair hA hB).toSimpleGraph (some true) hrev_true (P.disjoint hA hB hAB),
    fun ε' hε' ↦ ⟨hreg_all.nonUniforms_toSimpleGraph_eq_empty (some true) hrev_true hε',
      hreg_all.isUniform_toSimpleGraph (some true) hrev_true hε'⟩, ?_⟩
  -- Every graph edge edit corresponds to two ordered pair-color edits of `T` against `G`.
  have hsub :
      {p ∈ (univ : Finset {p : V × V // p.1 ≠ p.2}) |
          G'.toPairColorSystem.color p ≠ G.toPairColorSystem.color p} ⊆
        {p ∈ (univ : Finset {p : V × V // p.1 ≠ p.2}) |
          T.color p ≠ some (G.toPairColorSystem.color p)} := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    intro hEq
    apply hp
    rw [toPairColorSystem_color, toPairColorSystem_color, decide_eq_decide,
      T.toSimpleGraph_adj, T.colorOfPair_eq_some_iff]
    refine ⟨fun ⟨_, hc⟩ ↦ ?_, fun h ↦ ⟨p.2, by simpa [h] using hEq⟩⟩
    exact of_decide_eq_true (Option.some.inj (by rw [← toPairColorSystem_color, ← hEq]; exact hc))
  have hcard_nat := (G'.two_mul_card_symmDiff_edgeFinset G).le.trans (card_le_card hsub)
  have hle : 2 * (#(symmDiff G'.edgeFinset G.edgeFinset) : ℝ) ≤ α * (Fintype.card V : ℝ) ^ 2 := by
    refine le_trans ?_ hedit
    exact (by exact_mod_cast hcard_nat :
      2 * (#(symmDiff G'.edgeFinset G.edgeFinset) : ℝ) ≤
        (#{p ∈ (univ : Finset {p : V × V // p.1 ≠ p.2}) |
          T.color p ≠ some (G.toPairColorSystem.color p)} : ℝ)).trans_eq
      (by congr 2; ext p; simp)
  linarith

end SimpleGraph
