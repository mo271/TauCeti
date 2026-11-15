/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Diagonal
public import TauCeti.Combinatorics.Hypergraph.PairColor.StrongRegularization
import TauCeti.Combinatorics.Hypergraph.PairColor.Cleanup
import TauCeti.Combinatorics.Regularity.Partition.Equitabilise
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Regular approximation of pair-color systems and lower skeletons

Cleaning up irregular cell pairs of a single regular partition
(`PairColorSystem.exists_recoloring_isPairColorRegular`) achieves regularity at a fixed tolerance
`2 * ε` while editing at most an `O(ε)`-proportion of the pairs. A lower-skeleton regular
approximation for an arbitrary positive schedule `F : ℕ → ℝ` demands much more: every pair of cells
of the returned equipartition `P` must be regular at the scale `F #P.parts` (or
`F (#P.parts + card (Option κ))` for `PairSkeleton3.LowerSkeletonRegular F`), while the proportion
of edited pairs remains bounded by an independent `ε > 0`.

This file proves the lower-skeleton edited regular approximation lemma by combining three
ingredients:

1. **Coupled regular recoloring** (`PairColorSystem.exists_coupled_recoloring_isRegularPair` in
   `PairColor/Recoloring.lean`): if `(s, t)` is already `η`-regular for `S` with
   `card κ * η ≤ δ ^ 3 / 2`, pushing `S` on `s ×ˢ t` through the optimal transition coupling yields
   a `(2 * δ)`-regular pair with color densities within `δ` of `p` while editing at most
   `((∑ c, |d_c(s, t) - p c|) / 2 + δ / 2) * (#s * #t)` pairs of `s ×ˢ t`.
2. **Refinement-guided recoloring** (`PairColorSystem.exists_recoloring_of_refinement`): given a
   refinement `Q ≤ P`, regular fine blocks `(A', B')` between distinct coarse cells `(A, B)` are
   coupled-recolored toward the coarse densities `d_c(A, B)`, while irregular fine blocks receive
   independent quasi-random recolorings (`PairColorSystem.exists_recoloring_isRegularPair`), glued
   via `PairColorSystem.exists_cellwise_recoloring`. The total edit count is controlled by the `L¹`
   energy-gap drift plus the fine irregular mass.
3. **Strong regularity + amalgamation + diagonal cleanup**
   (`PairColorSystem.exists_regular_approximation` and
   `PairSkeleton3.exists_lowerSkeletonRegular_approximation`): applying strong equitable regularity
   (`PairColorSystem.exists_strong_equipartition`), amalgamating fine `(2 * δ)`-regular blocks onto
   `P` (`PairColorSystem.isRegularPair_of_refinement`), and filling diagonal coarse cells with a
   fresh reversal-fixed color (`PairColorSystem.fillDiagonal`) produces an everywhere regular lower
   skeleton within `ε |V|²` pair edits.

## Main definitions

* `TauCeti.pairColorApproxScale`: internal fine-block discrepancy target
  `(min 1 (min ε (F m)))³ / 8`.
* `TauCeti.pairColorApproxFineSchedule`: internal fine-partition regularity schedule.
* `TauCeti.pairColorApproximationBound`: host-independent upper bound on the coarse cell count.
* `TauCeti.pairColorApproximationFloor`: host-size threshold ensuring fine cells pass the
  exponential discrepancy union bound.

## Main results

* `TauCeti.PairColorSystem.exists_recoloring_of_refinement`: refinement-guided off-diagonal
  recoloring controlled by the energy gap and fine irregular mass.
* `TauCeti.PairColorSystem.exists_regular_approximation`: edited regular approximation of a
  pair-color system at scheduled regularity `F #P.parts`.
* `TauCeti.PairSkeleton3.exists_lowerSkeletonRegular_approximation`: edited regular approximation
  satisfying `PairSkeleton3.LowerSkeletonRegular F`.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Lemma 4.2.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), 451–476.
-/

public section

open Finset Finpartition Real

namespace TauCeti

section Bounds

/-- Internal fine-block target discrepancy scale `(min 1 (min ε (F m)))³ / 8` at `m` coarse cells.
-/
noncomputable def pairColorApproxScale (ε : ℝ) (F : ℕ → ℝ) (m : ℕ) : ℝ :=
  (min 1 (min ε (F m))) ^ 3 / 8

/-- Unfolding lemma for `TauCeti.pairColorApproxScale`. -/
theorem pairColorApproxScale_def (ε : ℝ) (F : ℕ → ℝ) (m : ℕ) :
    pairColorApproxScale ε F m = (min 1 (min ε (F m))) ^ 3 / 8 :=
  (rfl)

private theorem pairColorApproxScale_pos {ε : ℝ} {F : ℕ → ℝ} {m : ℕ} (hε : 0 < ε) (hF : 0 < F m) :
    0 < pairColorApproxScale ε F m := by
  have : 0 < min 1 (min ε (F m)) := lt_min zero_lt_one (lt_min hε hF)
  rw [pairColorApproxScale_def]
  positivity

private theorem pairColorApproxScale_le_one_div_eight {ε : ℝ} {F : ℕ → ℝ} {m : ℕ} (hε : 0 < ε)
    (hF : 0 < F m) : pairColorApproxScale ε F m ≤ 1 / 8 := by
  have hm0 : 0 ≤ min 1 (min ε (F m)) := le_min zero_le_one (le_min hε.le hF.le)
  have hm1 : min 1 (min ε (F m)) ≤ 1 := min_le_left _ _
  have hpow : (min 1 (min ε (F m))) ^ 3 ≤ 1 := pow_le_one₀ hm0 hm1
  rw [pairColorApproxScale_def]
  linarith

/-- Internal fine-partition regularity schedule `(pairColorApproxScale ε F m)³ / (2 (k + 1))` for a
palette of size `k`. -/
noncomputable def pairColorApproxFineSchedule (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (m : ℕ) : ℝ :=
  (pairColorApproxScale ε F m) ^ 3 / (2 * (k + 1 : ℝ))

/-- Unfolding lemma for `TauCeti.pairColorApproxFineSchedule`. -/
theorem pairColorApproxFineSchedule_def (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (m : ℕ) :
    pairColorApproxFineSchedule k ε F m =
      (pairColorApproxScale ε F m) ^ 3 / (2 * (k + 1 : ℝ)) :=
  (rfl)

private theorem pairColorApproxFineSchedule_pos (k : ℕ) {ε : ℝ} {F : ℕ → ℝ} {m : ℕ} (hε : 0 < ε)
    (hF : 0 < F m) : 0 < pairColorApproxFineSchedule k ε F m := by
  have hδ := pairColorApproxScale_pos hε hF
  rw [pairColorApproxFineSchedule_def]
  positivity

/-- Upper bound on the number of cells of the approximating equipartition in
`PairColorSystem.exists_regular_approximation`, for a palette of size `k`, edit tolerance `ε`,
regularity schedule `F`, requested minimum cell count `l`, and seed cell count `m₀`. -/
noncomputable def pairColorApproximationBound (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l m₀ : ℕ) : ℕ :=
  strongPairColorRegularityBound (ε ^ 2 / (4 * (k + 1 : ℝ)))
    (pairColorApproxFineSchedule k ε F) (max l ⌈4 / ε⌉₊ * m₀)

/-- Unfolding lemma for `TauCeti.pairColorApproximationBound`. -/
theorem pairColorApproximationBound_def (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l m₀ : ℕ) :
    pairColorApproximationBound k ε F l m₀ =
      strongPairColorRegularityBound (ε ^ 2 / (4 * (k + 1 : ℝ)))
        (pairColorApproxFineSchedule k ε F) (max l ⌈4 / ε⌉₊ * m₀) :=
  (rfl)

/-- `pairColorApproximationBound` is monotone in the seed cell count `m₀`. -/
theorem pairColorApproximationBound_mono (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l : ℕ) :
    Monotone (pairColorApproximationBound k ε F l) := fun _ _ h ↦
  strongPairColorRegularityBound_mono _ _ (Nat.mul_le_mul_left _ h)

/-- Host-size threshold for `PairColorSystem.exists_regular_approximation`: ensures both the initial
equitable split and the discrepancy union bound on every fine cell at all reachable coarse cell
counts up to `pairColorApproximationBound k ε F l m₀`. -/
noncomputable def pairColorApproximationFloor (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l m₀ : ℕ) : ℕ :=
  let M := pairColorApproximationBound k ε F l m₀
  max (max l ⌈4 / ε⌉₊ * m₀)
    (max 1 ((range (M + 1)).sup fun j ↦ ⌈8 * (k + 1 : ℝ) ^ 3 / (pairColorApproxScale ε F j) ^ 6⌉₊) *
      max 1 (strongPairColorRegularityStep (pairColorApproxFineSchedule k ε F) M))

/-- Unfolding lemma for `TauCeti.pairColorApproximationFloor`. -/
theorem pairColorApproximationFloor_def (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l m₀ : ℕ) :
    pairColorApproximationFloor k ε F l m₀ =
      max (max l ⌈4 / ε⌉₊ * m₀)
        (max 1 ((range (pairColorApproximationBound k ε F l m₀ + 1)).sup fun j ↦
            ⌈8 * (k + 1 : ℝ) ^ 3 / (pairColorApproxScale ε F j) ^ 6⌉₊) *
          max 1 (strongPairColorRegularityStep (pairColorApproxFineSchedule k ε F)
            (pairColorApproximationBound k ε F l m₀))) :=
  (rfl)

/-- `pairColorApproximationFloor` is always at least `1`. -/
theorem one_le_pairColorApproximationFloor (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l m₀ : ℕ) :
    1 ≤ pairColorApproximationFloor k ε F l m₀ :=
  (Nat.mul_le_mul (le_max_left 1 _) (le_max_left 1 _)).trans (le_max_right _ _)

/-- `pairColorApproximationFloor` is monotone in the seed cell count `m₀`. -/
theorem pairColorApproximationFloor_mono (k : ℕ) (ε : ℝ) (F : ℕ → ℝ) (l : ℕ) :
    Monotone (pairColorApproximationFloor k ε F l) := by
  intro m₁ m₂ hm
  have hM := pairColorApproximationBound_mono k ε F l hm
  refine max_le_max (Nat.mul_le_mul_left _ hm) (Nat.mul_le_mul ?_ ?_)
  · exact max_le_max le_rfl (Finset.sup_mono (range_mono (Nat.succ_le_succ hM)))
  · exact max_le_max le_rfl (strongPairColorRegularityStep_mono _ hM)

end Bounds

namespace PairColorSystem

section RefinementRecoloring

private theorem card_colorOfPair_ne_swap_eq {κ V : Type*} {S R T₀ : PairColorSystem κ V}
    {s t : Finset V}
    [DecidablePred fun q : V × V ↦ R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2]
    [DecidablePred fun q : V × V ↦ T₀.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2]
    (hRrev : R.rev = S.rev)
    (hlocal : ∀ y ∈ t, ∀ x ∈ s, R.colorOfPair y x = T₀.colorOfPair y x) :
    #{q ∈ s ×ˢ t | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
      #{q ∈ t ×ˢ s | T₀.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} := by
  refine card_bij (fun q _ ↦ q.swap) (fun ⟨x, y⟩ hq ↦ ?_)
    (fun _ _ _ _ h ↦ Prod.swap_injective h) (fun ⟨y, x⟩ hq ↦ ⟨(x, y), ?_, rfl⟩)
  · obtain ⟨hxy, hne'⟩ := mem_filter.1 hq
    obtain ⟨hx, hy⟩ := mem_product.1 hxy
    refine mem_filter.2 ⟨mem_product.2 ⟨hy, hx⟩, fun heq ↦ hne' ?_⟩
    dsimp only [Prod.fst_swap, Prod.snd_swap] at heq ⊢
    rw [R.colorOfPair_swap y x, S.colorOfPair_swap y x, hRrev, hlocal y hy x hx, heq]
  · obtain ⟨hyx, hne'⟩ := mem_filter.1 hq
    obtain ⟨hy, hx⟩ := mem_product.1 hyx
    refine mem_filter.2 ⟨mem_product.2 ⟨hx, hy⟩, fun heq ↦ hne' ?_⟩
    dsimp only at heq ⊢
    have h1 := congrArg (Option.map S.rev) heq
    have hmap (o : Option κ) : (o.map S.rev).map S.rev = o := by cases o <;> simp [S.rev_rev]
    rwa [R.colorOfPair_swap y x, hRrev, hmap, ← S.colorOfPair_swap x y, hlocal y hy x hx] at h1

variable {κ V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- Local recoloring of a single pair `(A', B')` of fine parts: leaves within-coarse-cell pairs
untouched, applies coupled recoloring when `(A', B')` is `η`-regular, and falls back to independent
quasi-random recoloring when `(A', B')` is `η`-irregular. -/
private theorem exists_local_refinement_recoloring [Fintype κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {η δ : ℝ} (hδ : 0 < δ)
    (hηδ : Fintype.card κ * η ≤ δ ^ 3 / 2)
    (hsize : ∀ A' ∈ Q.parts, 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #A')
    (A' B' : Q.parts) :
    ∃ T : PairColorSystem κ V, T.rev = S.rev ∧
      (refinementParent hQP A' = refinementParent hQP B' → T = S) ∧
      (refinementParent hQP A' ≠ refinementParent hQP B' →
        T.IsRegularPair (2 * δ) A'.1 B'.1 ∧
        (∀ c, |(pairColorDensity T c A'.1 B'.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1| ≤ δ) ∧
        (#{q ∈ A'.1 ×ˢ B'.1 | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
          ((∑ c, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
              pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) / 2 +
            δ / 2) * (#A'.1 * #B'.1) +
            if (A'.1, B'.1) ∈ S.irregularPairs η Q then (#A'.1 * #B'.1 : ℝ) else 0) := by
  classical
  by_cases hpar : refinementParent hQP A' = refinementParent hQP B'
  · exact ⟨S, rfl, fun _ ↦ rfl, fun hne ↦ (hne hpar).elim⟩
  have hAB : (refinementParent hQP A').1 ≠ (refinementParent hQP B').1 :=
    fun h ↦ hpar (Subtype.ext h)
  have hdisjP : Disjoint (refinementParent hQP A').1 (refinementParent hQP B').1 :=
    P.disjoint (refinementParent hQP A').2 (refinementParent hQP B').2 hAB
  have hdisj : Disjoint A'.1 B'.1 :=
    hdisjP.mono (le_refinementParent hQP A') (le_refinementParent hQP B')
  obtain ⟨u₀, hu₀⟩ := P.nonempty_of_mem_parts (refinementParent hQP A').2
  obtain ⟨v₀, hv₀⟩ := P.nonempty_of_mem_parts (refinementParent hQP B').2
  have hne_supp : (((refinementParent hQP A').1 ×ˢ (refinementParent hQP B').1).filter
      fun q ↦ q.1 ≠ q.2).Nonempty :=
    ⟨(u₀, v₀), mem_filter.2 ⟨mem_product.2 ⟨hu₀, hv₀⟩, hdisjP.forall_ne_finset hu₀ hv₀⟩⟩
  have hp (c : κ) : 0 ≤ (pairColorDensity S c (refinementParent hQP A').1
      (refinementParent hQP B').1 : ℝ) := mod_cast pairColorDensity_nonneg S c _ _
  have hp1 : ∑ c, (pairColorDensity S c (refinementParent hQP A').1
      (refinementParent hQP B').1 : ℝ) = 1 := mod_cast sum_pairColorDensity S _ _ hne_supp
  by_cases hreg : S.IsRegularPair η A'.1 B'.1
  · obtain ⟨T, hrev, -, hTreg, hTdens, hTedit⟩ := S.exists_coupled_recoloring_isRegularPair
      hdisj hp hp1 hreg hδ hηδ (hsize A'.1 A'.2) (hsize B'.1 B'.2)
    refine ⟨T, hrev, fun hh ↦ (hpar hh).elim, fun _ ↦ ⟨hTreg, hTdens, ?_⟩⟩
    exact hTedit.trans (le_add_of_nonneg_right (by split_ifs <;> positivity))
  · have hsmall (u : Finset V) (hu : u ∈ Q.parts) : Fintype.card κ + 1 ≤ δ ^ 6 * #u := by
      have : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
      have hsq : 1 ≤ (Fintype.card κ + 1 : ℝ) ^ 2 := by nlinarith
      nlinarith [hsize u hu]
    obtain ⟨T, hrev, -, hTreg, hTdens⟩ := S.exists_recoloring_isRegularPair hdisj hp hp1 hδ
      (hsmall A'.1 A'.2) (hsmall B'.1 B'.2)
    have hirr : (A'.1, B'.1) ∈ S.irregularPairs η Q :=
      S.mem_irregularPairs.2 ⟨A'.2, B'.2, fun h ↦ hpar (congrArg (refinementParent hQP)
        (Subtype.ext h)), hreg⟩
    refine ⟨T, hrev, fun hh ↦ (hpar hh).elim, fun _ ↦ ⟨hTreg, hTdens, ?_⟩⟩
    rw [ite_eq_left_iff.2 fun h ↦ (h hirr).elim]
    have htriv : (#{q ∈ A'.1 ×ˢ B'.1 | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        #A'.1 * #B'.1 := mod_cast (card_filter_le _ _).trans_eq (card_product _ _)
    have hnonneg : 0 ≤ ((∑ c, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
        pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) / 2 +
        δ / 2) * (#A'.1 * #B'.1) :=
      mul_nonneg (add_nonneg (div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num))
        (by positivity)) (by positivity)
    linarith

open Classical in
/-- Bound the edits of the glued system `R` on every fine block `A'.1 ×ˢ B'.1` in both orientations.
-/
private theorem card_edits_of_cellwise_refinement_le [Fintype κ] (S R : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {η δ : ℝ} (order : LinearOrder Q.parts)
    (T : Q.parts → Q.parts → PairColorSystem κ V) (hRrev : R.rev = S.rev)
    (hlocal : ∀ A' B' : Q.parts, order.le A' B' → ∀ x ∈ A'.1, ∀ y ∈ B'.1,
      R.colorOfPair x y = (T A' B').colorOfPair x y)
    (hkeep : ∀ A' B', refinementParent hQP A' = refinementParent hQP B' → T A' B' = S)
    (hedit : ∀ A' B', refinementParent hQP A' ≠ refinementParent hQP B' →
      (#{q ∈ A'.1 ×ˢ B'.1 | (T A' B').colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        ((∑ c, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) / 2 +
          δ / 2) * (#A'.1 * #B'.1) +
          if (A'.1, B'.1) ∈ S.irregularPairs η Q then (#A'.1 * #B'.1 : ℝ) else 0)
    (A' B' : Q.parts) :
    (#{q ∈ A'.1 ×ˢ B'.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
      if refinementParent hQP A' = refinementParent hQP B' then 0
      else ((∑ c, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) / 2 +
        δ / 2) * (#A'.1 * #B'.1) +
        if (A'.1, B'.1) ∈ S.irregularPairs η Q then (#A'.1 * #B'.1 : ℝ) else 0 := by
  classical
  let : LinearOrder Q.parts := order
  let : LE Q.parts := order.toLE
  by_cases hpar : refinementParent hQP A' = refinementParent hQP B'
  · rw [ite_eq_left_iff.2 fun h ↦ (h hpar).elim]
    have hzero : {q ∈ A'.1 ×ˢ B'.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} = ∅ := by
      ext ⟨x, y⟩
      simp only [mem_filter, mem_product, notMem_empty, iff_false, not_and, Classical.not_not]
      rintro ⟨hx, hy⟩
      rcases le_total A' B' with hle | hle
      · rw [hlocal A' B' hle x hx y hy, hkeep A' B' hpar]
      · rw [R.colorOfPair_swap y x, S.colorOfPair_swap y x, hRrev, hlocal B' A' hle y hy x hx,
          hkeep B' A' hpar.symm]
    simp [hzero]
  · rw [ite_eq_right_iff.2 fun h ↦ (hpar h).elim]
    rcases le_total A' B' with hle | hle
    · have heq : {q ∈ A'.1 ×ˢ B'.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
          {q ∈ A'.1 ×ˢ B'.1 | (T A' B').colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} :=
        filter_congr fun ⟨x, y⟩ hxy ↦ by
          rw [hlocal A' B' hle x (mem_product.1 hxy).1 y (mem_product.1 hxy).2]
      rw [heq]
      exact hedit A' B' hpar
    · have hirr_iff : (B'.1, A'.1) ∈ S.irregularPairs η Q ↔
          (A'.1, B'.1) ∈ S.irregularPairs η Q := by
        simp only [mem_irregularPairs, B'.2, A'.2, true_and, ne_comm, isRegularPair_comm]
      rw [card_colorOfPair_ne_swap_eq hRrev (hlocal B' A' hle)]
      refine (hedit B' A' (Ne.symm hpar)).trans_eq ?_
      rw [sum_abs_pairColorDensity_swap S A'.1 B'.1, mul_comm (#B'.1 : ℝ) #A'.1]
      by_cases hi : (A'.1, B'.1) ∈ S.irregularPairs η Q <;> simp [hirr_iff, hi, mul_comm]

open Classical in
/-- Sum the cellwise edit bounds over off-diagonal fine block pairs into the energy-gap drift term
plus the fine irregular mass. -/
private theorem sum_refinement_edit_bound_le [Fintype κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {η δ : ℝ} (hδ : 0 < δ) :
    ∑ AB ∈ univ.filter (fun AB : Q.parts × Q.parts ↦
        refinementParent hQP AB.1 ≠ refinementParent hQP AB.2),
      (((∑ c, |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1|) / 2 +
        δ / 2) * (#AB.1.1 * #AB.2.1) +
        if (AB.1.1, AB.2.1) ∈ S.irregularPairs η Q then (#AB.1.1 * #AB.2.1 : ℝ) else 0) ≤
      (√(Fintype.card κ * (S.energy Q - S.energy P)) / 2 + δ / 2) * (Fintype.card V : ℝ) ^ 2 +
        ∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ) := by
  classical
  let F := univ.filter fun AB : Q.parts × Q.parts ↦
    refinementParent hQP AB.1 ≠ refinementParent hQP AB.2
  have hdrift := S.sum_refinementParent_ne_abs_pairColorDensity_sub_le hQP le_rfl
  have hmass : ∑ AB ∈ F, (#AB.1.1 * #AB.2.1 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    refine (sum_le_univ_sum_of_nonneg fun _ ↦ by positivity).trans_eq ?_
    rw [Fintype.sum_prod_type]
    dsimp only
    rw [← sum_mul_sum, Q.sum_card_subtype, card_univ, sq]
  have hirr_le : (∑ AB ∈ F, if (AB.1.1, AB.2.1) ∈ S.irregularPairs η Q then
        (#AB.1.1 * #AB.2.1 : ℝ) else 0) ≤ ∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ) := by
    rw [← sum_filter, ← sum_image (f := fun ab : Finset V × Finset V ↦ (#ab.1 * #ab.2 : ℝ))
      fun _ _ _ _ h ↦ Prod.ext (Subtype.ext (Prod.mk.inj h).1) (Subtype.ext (Prod.mk.inj h).2)]
    refine sum_le_sum_of_subset_of_nonneg (fun ab hab ↦ ?_) fun _ _ _ ↦ by positivity
    obtain ⟨AB, hAB, rfl⟩ := mem_image.1 hab
    exact (mem_filter.1 hAB).2
  have hsplit : ∑ AB ∈ F, (((∑ c, |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1|) / 2 +
        δ / 2) * (#AB.1.1 * #AB.2.1)) =
      (1 / 2) * (∑ AB ∈ F, (#AB.1.1 * #AB.2.1 : ℝ) * ∑ c,
          |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1|) +
        (δ / 2) * ∑ AB ∈ F, (#AB.1.1 * #AB.2.1 : ℝ) := by
    rw [sum_congr rfl fun _ _ ↦ add_mul _ _ _, sum_add_distrib, mul_sum, mul_sum]
    congr 1; refine sum_congr rfl fun _ _ ↦ by ring
  rw [sum_add_distrib, hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ δ / 2)]

open Classical in
/-- **Refinement-guided off-diagonal recoloring.** Let `Q ≤ P` be vertex partitions and suppose
every fine cell `A' ∈ Q.parts` satisfies `8 (card κ + 1)³ ≤ δ⁶ #A'` with `card κ * η ≤ δ ^ 3 / 2`.
Then there exists `R : PairColorSystem κ V` with `R.rev = S.rev` such that every fine block
`(A', B')` inside an off-diagonal coarse block `(A, B)` is `(2 * δ)`-regular for `R` with color
densities within `δ` of `d_c(A, B)` in `S`, and the total ordered-pair edits are at most
`(√(card κ * (S.energy Q - S.energy P)) / 2 + δ / 2) * |V|²` plus the `η`-irregular mass of `Q`. -/
theorem exists_recoloring_of_refinement [Fintype κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {η δ : ℝ} (hδ : 0 < δ)
    (hηδ : Fintype.card κ * η ≤ δ ^ 3 / 2)
    (hsize : ∀ A' ∈ Q.parts, 8 * (Fintype.card κ + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #A') :
    ∃ R : PairColorSystem κ V, R.rev = S.rev ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B →
        ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B →
          R.IsRegularPair (2 * δ) A' B' ∧
          ∀ c, |(pairColorDensity R c A' B' : ℝ) - pairColorDensity S c A B| ≤ δ) ∧
      (#{q : V × V | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        (√(Fintype.card κ * (S.energy Q - S.energy P)) / 2 + δ / 2) * (Fintype.card V : ℝ) ^ 2 +
          ∑ AB ∈ S.irregularPairs η Q, (#AB.1 * #AB.2 : ℝ) := by
  classical
  let order : LinearOrder Q.parts := LinearOrder.lift' (Fintype.equivFin Q.parts)
    (Fintype.equivFin Q.parts).injective
  choose T hrev hkeep hprop using S.exists_local_refinement_recoloring hQP hδ hηδ hsize
  obtain ⟨R, hRrev, hlocal⟩ := S.exists_cellwise_recoloring Q order T hrev
  refine ⟨R, hRrev, fun A hA B hB hAB A' hA' hA'A B' hB' hB'B ↦ ?_, ?_⟩
  · have hpA : refinementParent hQP ⟨A', hA'⟩ = ⟨A, hA⟩ := (refinementParent_eq_iff hQP).2 hA'A
    have hpB : refinementParent hQP ⟨B', hB'⟩ = ⟨B, hB⟩ := (refinementParent_eq_iff hQP).2 hB'B
    have hne : refinementParent hQP ⟨A', hA'⟩ ≠ refinementParent hQP ⟨B', hB'⟩ := by
      rw [hpA, hpB]; exact fun h ↦ hAB (congrArg Subtype.val h)
    obtain ⟨hr, hd⟩ := S.isRegularPair_of_cellwise Q order T R hlocal hRrev (fun _ _ ↦ Ne.symm)
      (p := fun U W c ↦
        (pairColorDensity S c (refinementParent hQP U).1 (refinementParent hQP W).1 : ℝ))
      (fun U W c _ ↦ congrArg Rat.cast (pairColorDensity_swap S c _ _))
      (fun U W h ↦ ⟨(hprop U W h).1, (hprop U W h).2.1⟩) hne
    exact ⟨hr, fun c ↦ by simpa only [hpA, hpB] using hd c⟩
  · have hcover : (univ.filter fun q : V × V ↦ R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2) ⊆
        (univ : Finset (Q.parts × Q.parts)).biUnion fun AB ↦
          {q ∈ AB.1.1 ×ˢ AB.2.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} := fun q hq ↦
      mem_biUnion.2 ⟨(⟨Q.part q.1, Q.part_mem.2 (mem_univ _)⟩,
        ⟨Q.part q.2, Q.part_mem.2 (mem_univ _)⟩), mem_univ _,
        mem_filter.2 ⟨mem_product.2 ⟨Q.mem_part_self.2 (mem_univ _),
          Q.mem_part_self.2 (mem_univ _)⟩, (mem_filter.1 hq).2⟩⟩
    have hbi : (#{q : V × V | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        ∑ AB : Q.parts × Q.parts,
          (#{q ∈ AB.1.1 ×ˢ AB.2.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) :=
      mod_cast (card_le_card hcover).trans card_biUnion_le
    refine (hbi.trans ((sum_le_sum fun AB _ ↦ S.card_edits_of_cellwise_refinement_le R hQP order T
      hRrev hlocal hkeep (fun U W h ↦ (hprop U W h).2.2) AB.1 AB.2).trans_eq ?_)).trans
      (S.sum_refinement_edit_bound_le hQP hδ)
    rw [sum_filter]
    refine sum_congr rfl fun AB _ ↦ ?_
    by_cases h : refinementParent hQP AB.1 = refinementParent hQP AB.2 <;> simp [h]

end RefinementRecoloring

section Main

variable {κ V : Type*} [Fintype V] [DecidableEq V]

/-- Extract the fine-cell size threshold from `pairColorApproximationFloor`. -/
private theorem fine_part_size_of_floor {k l m₀ m : ℕ} {ε : ℝ} {F : ℕ → ℝ}
    {Q : Finpartition (univ : Finset V)} (hε : 0 < ε) (hF : 0 < F m)
    (hcard : pairColorApproximationFloor k ε F l m₀ ≤ Fintype.card V)
    (hQ : Q.IsEquipartition) (hmM : m ≤ pairColorApproximationBound k ε F l m₀)
    (hQstep : #Q.parts ≤ strongPairColorRegularityStep (pairColorApproxFineSchedule k ε F) m)
    {A' : Finset V} (hA' : A' ∈ Q.parts) :
    8 * (k + 1 : ℝ) ^ 3 ≤ (pairColorApproxScale ε F m) ^ 6 * #A' := by
  let M := pairColorApproximationBound k ε F l m₀
  let c := ⌈8 * (k + 1 : ℝ) ^ 3 / (pairColorApproxScale ε F m) ^ 6⌉₊
  have hc_le : c ≤ max 1 ((range (M + 1)).sup fun j ↦
      ⌈8 * (k + 1 : ℝ) ^ 3 / (pairColorApproxScale ε F j) ^ 6⌉₊) :=
    (le_sup (f := fun j ↦ ⌈8 * (k + 1 : ℝ) ^ 3 / (pairColorApproxScale ε F j) ^ 6⌉₊)
      (mem_range.2 (Nat.lt_succ_of_le hmM))).trans (le_max_right 1 _)
  have hQ_le : #Q.parts ≤ max 1 (strongPairColorRegularityStep
      (pairColorApproxFineSchedule k ε F) M) :=
    (hQstep.trans (strongPairColorRegularityStep_mono _ hmM)).trans (le_max_right 1 _)
  have hmul : c * #Q.parts ≤ #(univ : Finset V) := by
    rw [card_univ]
    exact (Nat.mul_le_mul hc_le hQ_le).trans ((le_max_right _ _).trans hcard)
  have hc_card : c ≤ #A' :=
    ((Nat.le_div_iff_mul_le (card_pos.2 ⟨A', hA'⟩)).2 hmul).trans (hQ.average_le_card_part hA')
  have hδ : 0 < pairColorApproxScale ε F m := pairColorApproxScale_pos hε hF
  have hceil : 8 * (k + 1 : ℝ) ^ 3 / (pairColorApproxScale ε F m) ^ 6 ≤ #A' :=
    (Nat.le_ceil _).trans (Nat.cast_le.2 hc_card)
  linarith [(div_le_iff₀ (pow_pos hδ 6)).1 hceil]

/-- Combine the four `ε / 4` error contributions (energy drift, coupled discrepancy, fine irregular
mass, and diagonal cleanup) into `ε * |V|²`. -/
private theorem approx_edit_budget_le {k m : ℕ} {ε g₀ : ℝ} {F : ℕ → ℝ} (n : ℝ) (hε : 0 < ε)
    (hF : 0 < F m) (hg₀ : 0 ≤ g₀) (hgap : g₀ ≤ ε ^ 2 / (4 * (k + 1 : ℝ)))
    (hm_ceil : ⌈4 / ε⌉₊ ≤ m) :
    (√((k : ℝ) * g₀) / 2 + pairColorApproxScale ε F m / 2) * n ^ 2 +
        pairColorApproxFineSchedule k ε F m * n ^ 2 + n ^ 2 / m ≤ ε * n ^ 2 := by
  have hsqrt : √((k : ℝ) * g₀) ≤ ε / 2 := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc (k : ℝ) * g₀ ≤ (k + 1 : ℝ) * (ε ^ 2 / (4 * (k + 1 : ℝ))) :=
          mul_le_mul (by linarith) hgap hg₀ (by positivity)
      _ = (ε / 2) ^ 2 := by field_simp; ring
  have hs0 : 0 ≤ min 1 (min ε (F m)) := le_min zero_le_one (le_min hε.le hF.le)
  have hs1 : min 1 (min ε (F m)) ≤ 1 := min_le_left _ _
  have hsε : min 1 (min ε (F m)) ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_pos := pairColorApproxScale_pos hε hF
  have hδ_one : pairColorApproxScale ε F m ≤ 1 :=
    (pairColorApproxScale_le_one_div_eight hε hF).trans (by norm_num)
  have hδ_ε : pairColorApproxScale ε F m ≤ ε / 8 := by
    have hp : (min 1 (min ε (F m))) ^ 3 ≤ ε := (pow_le_of_le_one hs0 hs1 (by norm_num)).trans hsε
    rw [pairColorApproxScale_def]; linarith
  have hη_ε : pairColorApproxFineSchedule k ε F m ≤ ε / 4 := by
    have hp : (pairColorApproxScale ε F m) ^ 3 ≤ pairColorApproxScale ε F m :=
      pow_le_of_le_one hδ_pos.le hδ_one (by norm_num)
    have hden : (2 : ℝ) ≤ 2 * (k + 1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hdiv := div_le_div_of_nonneg_left (pow_nonneg hδ_pos.le 3) (by positivity) hden
    rw [pairColorApproxFineSchedule_def]; linarith
  have hm_real : 4 / ε ≤ m := (Nat.le_ceil _).trans (Nat.cast_le.2 hm_ceil)
  have hm_pos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm_real
  have hdiag : n ^ 2 / m ≤ (ε / 4) * n ^ 2 := by
    rw [div_le_iff₀ hm_pos]
    have h1 : 1 ≤ (ε / 4) * m := by
      calc (1 : ℝ) = (ε / 4) * (4 / ε) := by field_simp
        _ ≤ (ε / 4) * m := mul_le_mul_of_nonneg_left hm_real (by positivity)
    nlinarith [sq_nonneg n]
  nlinarith [sq_nonneg n]

/-- Amalgamate fine `(2 * δ)`-regular blocks onto `P` and fill diagonal cells to obtain scheduled
regularity and coarse density preservation. -/
private theorem isPairColorRegular_fillDiagonal_of_refinement {k : ℕ} {ε : ℝ} {F : ℕ → ℝ}
    {P Q : Finpartition (univ : Finset V)} (S R : PairColorSystem κ V) (hQP : Q ≤ P) (hε : 0 < ε)
    (hF : 0 < F #P.parts)
    (hsize : ∀ A' ∈ Q.parts,
      8 * (k + 1 : ℝ) ^ 3 ≤ (pairColorApproxScale ε F #P.parts) ^ 6 * #A')
    (hRfine : ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B →
      ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B →
        R.IsRegularPair (2 * pairColorApproxScale ε F #P.parts) A' B' ∧
        ∀ c, |(pairColorDensity R c A' B' : ℝ) - pairColorDensity S c A B| ≤
          pairColorApproxScale ε F #P.parts) :
    (⟨P, R.fillDiagonal P⟩ : PairSkeleton3 (Option κ) V).IsPairColorRegular (F #P.parts) ∧
      ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c,
        |(pairColorDensity (R.fillDiagonal P) c A B : ℝ) -
          c.elim 0 (fun c ↦ (pairColorDensity S c A B : ℝ))| ≤ min ε (F #P.parts) := by
  set δ := pairColorApproxScale ε F #P.parts with hδdef
  have hδ : 0 < δ := pairColorApproxScale_pos hε hF
  have hτ : 0 < min ε (F #P.parts) := lt_min hε hF
  have h4δ : 4 * δ ≤ min ε (F #P.parts) := by
    have hp := (pow_le_of_le_one (le_min zero_le_one hτ.le) (min_le_left _ _) (n := 3)
      (by norm_num)).trans (min_le_right 1 _)
    rw [hδdef, pairColorApproxScale_def]; linarith
  have hlarge (A : Finset V) (hA : A ∈ P.parts) : 1 < F #P.parts * #A := by
    obtain ⟨A', hA', hA'A⟩ := exists_le_of_le hQP hA
    have hk1 : (1 : ℝ) ≤ (k + 1 : ℝ) ^ 3 :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hδF : δ ^ 6 ≤ F #P.parts := (pow_le_of_le_one hδ.le
      ((pairColorApproxScale_le_one_div_eight hε hF).trans (by norm_num)) (by norm_num)).trans
      (by linarith [min_le_right ε (F #P.parts)])
    have hcard_le : (#A' : ℝ) ≤ #A := mod_cast card_le_card hA'A
    nlinarith [hsize A' hA', mul_le_mul hδF hcard_le (by positivity) hF.le]
  have hRreg (A : Finset V) (hA : A ∈ P.parts) (B : Finset V) (hB : B ∈ P.parts) (hAB : A ≠ B) :
      R.IsRegularPair (F #P.parts) A B := by
    refine (R.isRegularPair_of_refinement hQP hA hB hAB hτ ?_
      (fun A' hA' hA'A B' hB' hB'B ↦ (hRfine A hA B hB hAB A' hA' hA'A B' hB' hB'B).1)
      (fun A' hA' hA'A B' hB' hB'B c ↦
        ((hRfine A hA B hB hAB A' hA' hA'A B' hB' hB'B).2 c).trans (by linarith))).mono
      (min_le_right _ _)
    have hp := pow_le_pow_left₀ (by positivity) (min_le_right 1 (min ε (F #P.parts))) 3
    rw [hδdef, pairColorApproxScale_def]; linarith
  refine ⟨R.isPairColorRegular_fillDiagonal P hlarge hRreg, fun A hA B hB hAB c ↦ ?_⟩
  rw [R.pairColorDensity_fillDiagonal_of_ne P hA hB hAB subset_rfl subset_rfl]
  cases c with
  | none => simp [hτ.le]
  | some c =>
    have hc := R.abs_pairColorDensity_sub_le_of_refinement hQP hA hB hAB
      (fun A' hA' hA'A B' hB' hB'B ↦ (hRfine A hA B hB hAB A' hA' hA'A B' hB' hB'B).1)
      (fun A' hA' hA'A B' hB' hB'B c₀ ↦
        ((hRfine A hA B hB hAB A' hA' hA'A B' hB' hB'B).2 c₀).trans (by linarith)) c
    simp only [Option.elim_some]
    linarith [hc, h4δ]

open Classical in
/-- **Edited regular approximation of a pair-color system.** Given an equipartition `P₀`, an edit
tolerance `ε > 0`, a positive regularity schedule `F : ℕ → ℝ`, and a minimum cell count `l`, once
`pairColorApproximationFloor (card κ) ε F l #P₀.parts ≤ card V` there exist an equipartition
`P ≤ P₀` with `l ≤ #P.parts ≤ pairColorApproximationBound (card κ) ε F l #P₀.parts` and a
pair-color system `T` on `Option κ` with `T.rev = Option.map S.rev` such that `(P, T)` is
`(F #P.parts)`-regular everywhere, off-diagonal coarse color densities stay within
`min ε (F #P.parts)` of those of `S`, and at most `ε |V|²` ordered pairs are edited. -/
theorem exists_regular_approximation [Fintype κ] (S : PairColorSystem κ V)
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {ε : ℝ} (hε : 0 < ε)
    {F : ℕ → ℝ} (hF : ∀ n, 0 < F n) {l : ℕ}
    (hcard : pairColorApproximationFloor (Fintype.card κ) ε F l #P₀.parts ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem (Option κ) V),
      P ≤ P₀ ∧ P.IsEquipartition ∧ l ≤ #P.parts ∧
      #P.parts ≤ pairColorApproximationBound (Fintype.card κ) ε F l #P₀.parts ∧
      T.rev = Option.map S.rev ∧
      (⟨P, T⟩ : PairSkeleton3 (Option κ) V).IsPairColorRegular (F #P.parts) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c,
        |(pairColorDensity T c A B : ℝ) -
          c.elim 0 (fun c ↦ (pairColorDensity S c A B : ℝ))| ≤ min ε (F #P.parts)) ∧
      (#{p : V × V | T.colorOfPair p.1 p.2 ≠ (S.colorOfPair p.1 p.2).map some} : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  let k := Fintype.card κ
  let t₀ := max l ⌈4 / ε⌉₊
  -- Phase 1: split each seed cell equitably into `t₀ = max l ⌈4 / ε⌉₊` parts so `#P.parts` meets
  -- both `l` and the `⌈4 / ε⌉₊` diagonal-cleanup threshold.
  have hVpos : 0 < Fintype.card V :=
    (one_le_pairColorApproximationFloor k ε F l #P₀.parts).trans hcard
  have hne_univ : (univ : Finset V).Nonempty := card_pos.1 (by rwa [card_univ])
  have hP₀_pos : 1 ≤ #P₀.parts := card_pos.2 (P₀.parts_nonempty hne_univ.ne_empty)
  have ht₀_pos : 1 ≤ t₀ := (Nat.one_le_ceil_iff.2 (by positivity)).trans (le_max_right l _)
  obtain ⟨P₁, hP₁, hP₁card, hP₁P₀, -⟩ := hP₀.exists_refining_equipartition_card_eq_mul P₀ le_rfl
    (by omega : t₀ ≠ 0) (by rw [card_univ]; exact (le_max_left _ _).trans hcard)
  -- Phase 2: apply two-scale strong regularity on `P₁` to obtain equipartitions `Q ≤ P ≤ P₁` with
  -- energy gap at most `ε² / (4 (k + 1))` and small fine irregular mass.
  obtain ⟨P, Q, hQP, hPP₁, hP, hQ, hPcard, hQcard, hgap, hirr⟩ := S.exists_strong_equipartition P₁
    hP₁ (g := ε ^ 2 / (4 * (k + 1 : ℝ))) (by positivity)
    (fun m ↦ pairColorApproxFineSchedule_pos k hε (hF m))
  have hmM : #P.parts ≤ pairColorApproximationBound k ε F l #P₀.parts := by
    rwa [hP₁card] at hPcard
  have ht₀_P : t₀ ≤ #P.parts :=
    (Nat.le_mul_of_pos_right t₀ hP₀_pos).trans (hP₁card.symm.trans_le (card_mono hPP₁))
  -- Phase 3: recolor off-diagonal fine blocks of `Q ≤ P` toward the coarse densities of `P`,
  -- coupling on regular fine blocks and resampling independently on irregular fine blocks.
  let δ := pairColorApproxScale ε F #P.parts
  have hδ : 0 < δ := pairColorApproxScale_pos hε (hF #P.parts)
  have hsize : ∀ A' ∈ Q.parts, 8 * (k + 1 : ℝ) ^ 3 ≤ δ ^ 6 * #A' := fun _ hA' ↦
    fine_part_size_of_floor hε (hF #P.parts) hcard hQ hmM hQcard hA'
  have hηδ : (k : ℝ) * pairColorApproxFineSchedule k ε F #P.parts ≤ δ ^ 3 / 2 := by
    rw [pairColorApproxFineSchedule_def, mul_div_assoc',
      div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [show 0 ≤ δ ^ 3 by positivity]
  obtain ⟨R, hRrev, hRfine, hRedit⟩ := S.exists_recoloring_of_refinement hQP hδ hηδ hsize
  -- Phase 4: amalgamate the fine `(2 * δ)`-regular blocks onto `P` and fill diagonal coarse cells.
  obtain ⟨hTreg, hTdens⟩ :=
    isPairColorRegular_fillDiagonal_of_refinement S R hQP hε (hF #P.parts) hsize hRfine
  refine ⟨P, R.fillDiagonal P, hPP₁.trans hP₁P₀, hP, (le_max_left l _).trans ht₀_P, hmM,
    funext fun c ↦ by simp [hRrev], hTreg, hTdens, ?_⟩
  -- Phase 5: bound total pair edits by off-diagonal recoloring edits plus diagonal cleanup edits.
  have htri : (#{p : V × V | (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
        (S.colorOfPair p.1 p.2).map some} : ℝ) ≤
      (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) +
        (#{p : V × V | (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
          (R.colorOfPair p.1 p.2).map some} : ℝ) :=
    mod_cast S.card_fillDiagonal_colorOfPair_ne_le_add P R
  have hdiag := R.card_fillDiagonal_colorOfPair_ne_le_of_isEquipartition hP
  have hbud := approx_edit_budget_le (Fintype.card V : ℝ) hε (hF #P.parts)
    (sub_nonneg.2 (S.energy_mono_of_refines hQP)) hgap ((le_max_right l _).trans ht₀_P)
  linarith

end Main

end PairColorSystem

namespace PairSkeleton3

variable {κ V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- **Lower-skeleton regular approximation.** Given a lower skeleton `S` whose vertex partition is
equitable, an edit tolerance `ε > 0`, a positive schedule `F : ℕ → ℝ`, and a minimum cell count `l`,
once `V` exceeds `pairColorApproximationFloor` at the shifted schedule `m ↦ F (m + (card κ + 1))`
there exists an approximating lower skeleton `S'` on palette `Option κ` whose vertex equipartition
refines `S.vertexPart` into between `l` and `pairColorApproximationBound` cells, satisfies
`S'.LowerSkeletonRegular F`, preserves off-diagonal coarse color densities within
`min ε (F (#S'.vertexPart.parts + (card κ + 1)))`, and edits at most `ε |V|²` ordered distinct
vertex pairs. -/
theorem exists_lowerSkeletonRegular_approximation [Fintype κ] (S : PairSkeleton3 κ V)
    (hS : S.vertexPart.IsEquipartition) {ε : ℝ} (hε : 0 < ε) {F : ℕ → ℝ} (hF : ∀ n, 0 < F n)
    {l : ℕ}
    (hcard : pairColorApproximationFloor (Fintype.card κ) ε
      (fun m ↦ F (m + (Fintype.card κ + 1))) l #S.vertexPart.parts ≤ Fintype.card V) :
    ∃ S' : PairSkeleton3 (Option κ) V,
      S'.vertexPart ≤ S.vertexPart ∧ S'.vertexPart.IsEquipartition ∧
      l ≤ #S'.vertexPart.parts ∧
      #S'.vertexPart.parts ≤ pairColorApproximationBound (Fintype.card κ) ε
        (fun m ↦ F (m + (Fintype.card κ + 1))) l #S.vertexPart.parts ∧
      S'.pairColors.rev = Option.map S.pairColors.rev ∧
      S'.LowerSkeletonRegular F ∧
      (∀ A ∈ S'.vertexPart.parts, ∀ B ∈ S'.vertexPart.parts, A ≠ B → ∀ c,
        |(pairColorDensity S'.pairColors c A B : ℝ) -
          c.elim 0 (fun c ↦ (pairColorDensity S.pairColors c A B : ℝ))| ≤
            min ε (F (#S'.vertexPart.parts + (Fintype.card κ + 1)))) ∧
      (#{q : {p : V × V // p.1 ≠ p.2} |
          S'.pairColors.color q ≠ some (S.pairColors.color q)} : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  obtain ⟨P, T, hPP₀, hP, hlP, hPM, hrev, hreg, hdens, hedit⟩ :=
    S.pairColors.exists_regular_approximation S.vertexPart hS hε
      (F := fun m ↦ F (m + (Fintype.card κ + 1))) (fun m ↦ hF _) hcard
  refine ⟨⟨P, T⟩, hPP₀, hP, hlP, hPM, hrev, ?_, hdens, ?_⟩
  · rw [lowerSkeletonRegular_iff, Fintype.card_option]
    exact hreg
  · rwa [S.pairColors.card_color_ne_eq_card_colorOfPair_ne T some]

end PairSkeleton3

end TauCeti
