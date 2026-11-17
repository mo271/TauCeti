/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Graph.Basic
public import TauCeti.Combinatorics.Hypergraph.PairColor.Energy
public import TauCeti.Combinatorics.Regularity.Partition.Energy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pair-color energy of a simple graph versus size-weighted graph energy

For a finite simple graph `G` on `V` and a partition `P` of the vertices, the two-color system
`G.toPairColorSystem` has palette `Bool`, with edge color `true` and non-edge color `false`. On
every block with at least one distinct pair, the two color densities satisfy `d_false = 1 - d_true`,
so `d_true² + d_false² = 2 d_true² - 2 d_true + 1`. Averaging over all ordered distinct pairs shows
that `G.toPairColorSystem.energy P` is affine in the mean square of the block edge densities taken
among distinct pairs (`SimpleGraph.energy_toPairColorSystem_eq`).

Comparing this mean square with the size-weighted graph energy `G.weightedEnergy P` isolates the
two normalization differences between the two energies: off-diagonal blocks `A ≠ B` match
identically, while on diagonal blocks `A = B` the pair-color density excludes loops (denominator
`|A| (|A| - 1)`) and the global average divides by `|V| (|V| - 1)` rather than `|V|²`. Together
these discrepancies lie in `[0, 4 / |V|]` (`SimpleGraph.zero_le_energy_toPairColorSystem_sub`,
`SimpleGraph.energy_toPairColorSystem_sub_le`), which is asymptotically sharp on complete graphs
with the trivial partition. When every cell of `P` is an independent set of `G`, the diagonal
terms vanish and the two energies satisfy an exact identity
(`SimpleGraph.energy_toPairColorSystem_eq_of_forall_not_adj`).

Taking the difference between two partitions `P` and `Q` cancels the global edge density, so the
pair-color energy gap equals twice the weighted graph energy gap up to `4 / |V|`
(`SimpleGraph.abs_energy_toPairColorSystem_sub_sub_two_mul_weightedEnergy_sub_le`). This transfers
energy-gap hypotheses between pair-color strong regularization and strong graph regularity.

## Main results

* `SimpleGraph.energy_toPairColorSystem_eq`: exact expansion of `G.toPairColorSystem.energy P`
  in terms of the edge-color block densities.
* `SimpleGraph.energy_toPairColorSystem_eq_of_forall_not_adj`: exact relation with
  `G.weightedEnergy P` when every cell is an independent set.
* `SimpleGraph.zero_le_energy_toPairColorSystem_sub` and
  `SimpleGraph.energy_toPairColorSystem_sub_le`: sharp `[0, 4 / |V|]` comparison with
  `1 - 2 d_off(G) + 2 G.weightedEnergy P` (with the upper bound unconditional on `|V|`).
* `SimpleGraph.abs_energy_toPairColorSystem_sub_le`: comparison with
  `1 - 2 G.edgeDensity univ univ + 2 G.weightedEnergy P` on any nonempty host.
* `SimpleGraph.abs_energy_toPairColorSystem_sub_sub_two_mul_weightedEnergy_sub_le`: comparison of
  energy gaps for any two partitions `P` and `Q`, with no host-size hypothesis.

## References

* Y. Zhao, *Graph Theory and Additive Combinatorics*, Cambridge University Press (2023), ch. 2.
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset TauCeti

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The ordered pairs of color `true` in `s ×ˢ t` are exactly the edges of `G` between `s` and `t`,
even when `s` and `t` overlap, since `G` is loopless. -/
private theorem filter_toPairColorSystem_true (s t : Finset V) :
    (s ×ˢ t).filter (fun p ↦ G.toPairColorSystem.colorOfPair p.1 p.2 = some true) =
      G.interedges s t := by
  ext p
  simp [G.mem_interedges_iff, and_assoc]

/-- On a diagonal cell `A`, the squared distinct-pair edge density exceeds the squared
Cartesian-product edge density by between `0` and `#A - 1`. -/
private theorem diagonal_sq_density_bounds (A : Finset V) :
    0 ≤ (#A.offDiag : ℝ) * (pairColorDensity G.toPairColorSystem true A A : ℝ) ^ 2 -
          (#A : ℝ) ^ 2 * (G.edgeDensity A A : ℝ) ^ 2 ∧
      (#A.offDiag : ℝ) * (pairColorDensity G.toPairColorSystem true A A : ℝ) ^ 2 -
          (#A : ℝ) ^ 2 * (G.edgeDensity A A : ℝ) ^ 2 ≤ (#A - 1 : ℕ) := by
  classical
  have hsub : G.interedges A A ⊆ A.offDiag := fun p hp ↦
    let ⟨h1, h2, hadj⟩ := G.mem_interedges_iff.1 hp
    mem_offDiag.2 ⟨h1, h2, G.ne_of_adj hadj⟩
  have hoff : (A ×ˢ A).filter (fun p ↦ p.1 ≠ p.2) = A.offDiag := by
    ext p; simp [mem_offDiag, and_assoc]
  rcases lt_or_ge #A 2 with hA | hA
  · have hoff_empty : A.offDiag = ∅ := by
      rw [← card_eq_zero, offDiag_card]
      exact Nat.sub_eq_zero_of_le (by nlinarith)
    have he_empty : G.interedges A A = ∅ := subset_empty.1 (hoff_empty ▸ hsub)
    simp [hoff_empty, SimpleGraph.edgeDensity_def, he_empty]
  · have : (0 : ℝ) < (#A : ℝ) := Nat.cast_pos.2 (by omega)
    have : (0 : ℝ) < (#A : ℝ) - 1 := sub_pos.2 (Nat.one_lt_cast.2 (by omega))
    have hcard_off : (#A.offDiag : ℝ) = (#A : ℝ) * ((#A : ℝ) - 1) := by
      rw [offDiag_card, Nat.cast_sub (Nat.le_mul_self #A)]; push_cast; ring
    have h1 : (pairColorDensity G.toPairColorSystem true A A : ℝ) =
        (#(G.interedges A A) : ℝ) / ((#A : ℝ) * ((#A : ℝ) - 1)) := by
      have hmul : pairColorDensity G.toPairColorSystem true A A * #A.offDiag =
          #(G.interedges A A) := by
        rw [← hoff, pairColorDensity_mul_card_support, G.filter_toPairColorSystem_true]
      exact eq_div_of_mul_eq (by positivity) (by rw [← hcard_off]; exact_mod_cast hmul)
    have h2 : (G.edgeDensity A A : ℝ) = (#(G.interedges A A) : ℝ) / ((#A : ℝ) * (#A : ℝ)) :=
      eq_div_of_mul_eq (by positivity) (by linarith [G.card_mul_card_mul_edgeDensity_real A A])
    have hdiff : (#A.offDiag : ℝ) * (pairColorDensity G.toPairColorSystem true A A : ℝ) ^ 2 -
        (#A : ℝ) ^ 2 * (G.edgeDensity A A : ℝ) ^ 2 =
        (#(G.interedges A A) : ℝ) ^ 2 / ((#A : ℝ) ^ 2 * ((#A : ℝ) - 1)) := by
      rw [hcard_off, h1, h2]; field_simp; ring
    rw [hdiff]
    refine ⟨by positivity, ?_⟩
    have he_le : (#(G.interedges A A) : ℝ) ≤ (#A : ℝ) * ((#A : ℝ) - 1) := by
      rw [← hcard_off]; exact_mod_cast card_le_card hsub
    rw [Nat.cast_sub (by omega), Nat.cast_one, div_le_iff₀ (by positivity)]
    have hsq : (#(G.interedges A A) : ℝ) ^ 2 ≤ ((#A : ℝ) * ((#A : ℝ) - 1)) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) #(G.interedges A A)]
    nlinarith

variable [DecidableEq V]

/-- On any block `s ×ˢ t`, multiplying the edge-color density by the number of distinct pairs
recovers the edge count `#(G.interedges s t)`. -/
theorem pairColorDensity_toPairColorSystem_true_mul_card_support (s t : Finset V) :
    pairColorDensity G.toPairColorSystem true s t * #((s ×ˢ t).filter fun p ↦ p.1 ≠ p.2) =
      #(G.interedges s t) := by
  rw [pairColorDensity_mul_card_support, G.filter_toPairColorSystem_true]

variable [Fintype V]

/-- The difference between the off-diagonal sum of squared distinct-pair edge densities and
`|V|² * G.weightedEnergy P` is the sum of the diagonal block discrepancies. -/
private theorem sum_sq_pairColorDensity_true_sub_weightedEnergy_eq
    (P : Finpartition (univ : Finset V)) :
    (∑ p ∈ (univ : Finset V).offDiag,
        (pairColorDensity G.toPairColorSystem true (P.part p.1) (P.part p.2) : ℝ) ^ 2) -
      (Fintype.card V : ℝ) ^ 2 * G.weightedEnergy P =
    ∑ A ∈ P.parts,
      ((#A.offDiag : ℝ) * (pairColorDensity G.toPairColorSystem true A A : ℝ) ^ 2 -
        (#A : ℝ) ^ 2 * (G.edgeDensity A A : ℝ) ^ 2) := by
  rcases isEmpty_or_nonempty V with hV | hV
  · have hP : P.parts = ∅ := Finpartition.parts_eq_empty_iff.2 (by simp [univ_eq_empty])
    simp [hP, weightedEnergy_def]
  have hVpos : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let d (A B : Finset V) : ℝ := (pairColorDensity G.toPairColorSystem true A B : ℝ) ^ 2
  have hdiag : ∑ p ∈ (univ : Finset V).diag, d (P.part p.1) (P.part p.2) =
      ∑ A ∈ P.parts, (#A : ℝ) * d A A := by
    rw [sum_diag, P.sum_apply_part fun A ↦ d A A]
    exact sum_congr rfl fun _ _ ↦ nsmul_eq_mul _ _
  have hfull : ∑ p ∈ (univ : Finset V) ×ˢ (univ : Finset V), d (P.part p.1) (P.part p.2) =
      ∑ A ∈ P.parts, ∑ B ∈ P.parts, (#A : ℝ) * #B * d A B := by
    rw [sum_product, sum_congr rfl fun x _ ↦ P.sum_apply_part fun B ↦ d (P.part x) B,
      P.sum_apply_part fun A ↦ ∑ B ∈ P.parts, #B • d A B]
    refine sum_congr rfl fun A _ ↦ ?_
    rw [nsmul_eq_mul, mul_sum]
    exact sum_congr rfl fun B _ ↦ by rw [nsmul_eq_mul]; ring
  have hoff : ∑ p ∈ (univ : Finset V).offDiag, d (P.part p.1) (P.part p.2) =
      (∑ A ∈ P.parts, ∑ B ∈ P.parts, (#A : ℝ) * #B * d A B) -
      ∑ A ∈ P.parts, (#A : ℝ) * d A A := by
    have hsplit : ∑ p ∈ (univ : Finset V).diag, d (P.part p.1) (P.part p.2) +
        ∑ p ∈ (univ : Finset V).offDiag, d (P.part p.1) (P.part p.2) =
        ∑ p ∈ (univ : Finset V) ×ˢ (univ : Finset V), d (P.part p.1) (P.part p.2) := by
      rw [← sum_union (disjoint_diag_offDiag _), diag_union_offDiag]
    linarith
  have hW : (Fintype.card V : ℝ) ^ 2 * G.weightedEnergy P =
      ∑ A ∈ P.parts, ∑ B ∈ P.parts, (#A : ℝ) * #B * (G.edgeDensity A B : ℝ) ^ 2 := by
    rw [weightedEnergy_def, mul_sum]
    refine sum_congr rfl fun A _ ↦ ?_
    rw [mul_sum]
    exact sum_congr rfl fun B _ ↦ by field_simp
  -- Off-diagonal blocks `A ≠ B` cancel identically, leaving only diagonal blocks `A = B`.
  have hrew : (∑ p ∈ (univ : Finset V).offDiag,
        (pairColorDensity G.toPairColorSystem true (P.part p.1) (P.part p.2) : ℝ) ^ 2) =
      ∑ p ∈ (univ : Finset V).offDiag, d (P.part p.1) (P.part p.2) := rfl
  rw [hrew, hoff, hW, sub_right_comm, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun A hA ↦ ?_
  rw [← sum_sub_distrib, sum_eq_single A]
  · have hcard : (#A.offDiag : ℝ) = (#A : ℝ) ^ 2 - #A := by
      rw [offDiag_card, Nat.cast_sub (Nat.le_mul_self #A)]; push_cast; ring
    simp only [d]; rw [hcard]; ring
  · intro B hB hBA
    have hdisj : Disjoint A B := P.disjoint hA hB hBA.symm
    simp only [d]; rw [G.pairColorDensity_toPairColorSystem_true hdisj, sub_self]
  · intro hnot; exact (hnot hA).elim

/-- The unnormalized pair-color edge sum exceeds `|V|² * G.weightedEnergy P` by between `0` and
`|V| - #P.parts`. -/
private theorem sum_sq_pairColorDensity_true_sub_weightedEnergy_bounds
    (P : Finpartition (univ : Finset V)) :
    0 ≤ (∑ p ∈ (univ : Finset V).offDiag,
            (pairColorDensity G.toPairColorSystem true (P.part p.1) (P.part p.2) : ℝ) ^ 2) -
          (Fintype.card V : ℝ) ^ 2 * G.weightedEnergy P ∧
      (∑ p ∈ (univ : Finset V).offDiag,
            (pairColorDensity G.toPairColorSystem true (P.part p.1) (P.part p.2) : ℝ) ^ 2) -
          (Fintype.card V : ℝ) ^ 2 * G.weightedEnergy P ≤
        (Fintype.card V : ℝ) - #P.parts := by
  rw [G.sum_sq_pairColorDensity_true_sub_weightedEnergy_eq P]
  refine ⟨sum_nonneg fun A _ ↦ (G.diagonal_sq_density_bounds A).1, ?_⟩
  calc ∑ A ∈ P.parts,
          ((#A.offDiag : ℝ) * (pairColorDensity G.toPairColorSystem true A A : ℝ) ^ 2 -
            (#A : ℝ) ^ 2 * (G.edgeDensity A A : ℝ) ^ 2)
      ≤ ∑ A ∈ P.parts, ((#A - 1 : ℕ) : ℝ) :=
        sum_le_sum fun A _ ↦ (G.diagonal_sq_density_bounds A).2
    _ = ∑ A ∈ P.parts, ((#A : ℝ) - 1) := sum_congr rfl fun A hA ↦ by
        rw [Nat.cast_sub (P.nonempty_of_mem_parts hA).card_pos, Nat.cast_one]
    _ = (Fintype.card V : ℝ) - #P.parts := by
        rw [sum_sub_distrib, ← Nat.cast_sum, P.sum_card_parts, card_univ, sum_const, nsmul_one]

/-- On a host with fewer than two vertices, a simple graph has no edges, so its pair-color energy,
weighted graph energy, and both global edge densities vanish. -/
private theorem energy_and_densities_eq_zero_of_card_lt_two
    (P : Finpartition (univ : Finset V)) (hV : Fintype.card V < 2) :
    G.toPairColorSystem.energy P = 0 ∧ G.weightedEnergy P = 0 ∧
      pairColorDensity G.toPairColorSystem true univ univ = 0 ∧
      G.edgeDensity univ univ = 0 := by
  have hoff : (univ : Finset V).offDiag = ∅ := by
    rw [← card_eq_zero, offDiag_card, card_univ]
    exact Nat.sub_eq_zero_of_le (by nlinarith)
  have hempty : G.interedges univ univ = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun p hp ↦ ?_
    have : p ∈ (univ : Finset V).offDiag :=
      mem_offDiag.2 ⟨mem_univ _, mem_univ _, G.ne_of_adj (G.mem_interedges_iff.1 hp).2.2⟩
    simp [hoff] at this
  have hd : G.edgeDensity univ univ = 0 := by simp [SimpleGraph.edgeDensity_def, hempty]
  refine ⟨by simp [PairColorSystem.energy_def, hoff],
    le_antisymm ((G.weightedEnergy_le_edgeDensity_univ P).trans (by simp [hd]))
      (G.weightedEnergy_nonneg P),
    by rw [pairColorDensity_def, G.filter_toPairColorSystem_true, hempty]; simp, hd⟩

/-- **Exact expansion of the pair-color energy of a graph.** On a host with at least two vertices,
the pair-color energy of `G.toPairColorSystem` on `P` is `1 - 2 d_off(G)` plus twice the mean
square of the distinct-pair block edge densities, where `d_off(G)` is the global edge density among
distinct pairs. -/
theorem energy_toPairColorSystem_eq (P : Finpartition (univ : Finset V))
    (hV : 2 ≤ Fintype.card V) :
    G.toPairColorSystem.energy P =
      1 - 2 * (pairColorDensity G.toPairColorSystem true univ univ : ℝ) +
        2 * (∑ p ∈ (univ : Finset V).offDiag,
          (pairColorDensity G.toPairColorSystem true (P.part p.1) (P.part p.2) : ℝ) ^ 2) /
          #(univ : Finset V).offDiag := by
  have hoff_ne : (#(univ : Finset V).offDiag : ℝ) ≠ 0 := by
    refine Nat.cast_ne_zero.2 (Nat.ne_of_gt ?_)
    rw [offDiag_card, card_univ]
    have : Fintype.card V < Fintype.card V * Fintype.card V := by nlinarith
    omega
  -- On every block through an ordered distinct pair, `d_true + d_false = 1`.
  have hpoint (p : V × V) (hp : p ∈ (univ : Finset V).offDiag) :
      ∑ c : Bool, (pairColorDensity G.toPairColorSystem c (P.part p.1) (P.part p.2) : ℝ) ^ 2 =
        2 * (pairColorDensity G.toPairColorSystem true (P.part p.1) (P.part p.2) : ℝ) ^ 2 -
          2 * (pairColorDensity G.toPairColorSystem true (P.part p.1) (P.part p.2) : ℝ) + 1 := by
    have hsupp : ((P.part p.1 ×ˢ P.part p.2).filter fun q ↦ q.1 ≠ q.2).Nonempty :=
      ⟨p, mem_filter.2 ⟨mem_product.2 ⟨P.mem_part_self.2 (mem_univ _),
        P.mem_part_self.2 (mem_univ _)⟩, (mem_offDiag.1 hp).2.2⟩⟩
    have hsum : (pairColorDensity G.toPairColorSystem true (P.part p.1) (P.part p.2) : ℝ) +
        (pairColorDensity G.toPairColorSystem false (P.part p.1) (P.part p.2) : ℝ) = 1 := by
      have h := sum_pairColorDensity G.toPairColorSystem (P.part p.1) (P.part p.2) hsupp
      rw [Fintype.sum_bool] at h
      exact_mod_cast h
    have hf : (pairColorDensity G.toPairColorSystem false (P.part p.1) (P.part p.2) : ℝ) =
        1 - (pairColorDensity G.toPairColorSystem true (P.part p.1) (P.part p.2) : ℝ) := by
      linarith
    rw [Fintype.sum_bool, hf]; ring
  -- The average of the block edge densities equals the global distinct-pair edge density.
  have hmean : ∑ p ∈ (univ : Finset V).offDiag,
        (pairColorDensity G.toPairColorSystem true (P.part p.1) (P.part p.2) : ℝ) =
      (pairColorDensity G.toPairColorSystem true univ univ : ℝ) * #(univ : Finset V).offDiag := by
    have h1 := G.toPairColorSystem.sum_pairColorDensity_part_mul P true (fun _ ↦ (1 : ℝ))
      fun _ _ _ _ ↦ rfl
    simp only [mul_one, sum_const, nsmul_one] at h1
    have hfilt : ((univ : Finset V).offDiag.filter
        fun p ↦ G.toPairColorSystem.colorOfPair p.1 p.2 = some true) = G.interedges univ univ := by
      ext p
      simp only [mem_filter, mem_offDiag, mem_univ, true_and,
        colorOfPair_toPairColorSystem_eq_some_true, G.mem_interedges_iff, and_iff_right_iff_imp]
      exact G.ne_of_adj
    have hoff : ((univ : Finset V) ×ˢ (univ : Finset V)).filter (fun p ↦ p.1 ≠ p.2) =
        (univ : Finset V).offDiag := by ext p; simp [mem_offDiag]
    rw [h1, hfilt, ← hoff]
    exact_mod_cast (G.pairColorDensity_toPairColorSystem_true_mul_card_support univ univ).symm
  rw [PairColorSystem.energy_def, sum_congr rfl hpoint]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_one, hmean]
  field_simp; ring

/-- **Exact energy identity for independent cells.** When every vertex cell of `P` is an
independent set of `G` (for instance, for the discrete partition `⊥` or a proper coloring), the
diagonal blocks have zero edge density and `G.toPairColorSystem.energy P` is determined exactly
by `G.weightedEnergy P`. -/
theorem energy_toPairColorSystem_eq_of_forall_not_adj (P : Finpartition (univ : Finset V))
    (hV : 2 ≤ Fintype.card V) (hind : ∀ A ∈ P.parts, ∀ u ∈ A, ∀ v ∈ A, ¬G.Adj u v) :
    G.toPairColorSystem.energy P =
      1 - 2 * (pairColorDensity G.toPairColorSystem true univ univ : ℝ) +
        2 * ((Fintype.card V : ℝ) / (Fintype.card V - 1)) * G.weightedEnergy P := by
  have : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 (by omega)
  have hV1 : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := sub_pos.2 (Nat.one_lt_cast.2 (by omega))
  have hcard_off : (#(univ : Finset V).offDiag : ℝ) =
      (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
    rw [offDiag_card, card_univ, Nat.cast_sub (Nat.le_mul_self _)]; push_cast; ring
  have hdiag_zero : ∑ A ∈ P.parts,
      ((#A.offDiag : ℝ) * (pairColorDensity G.toPairColorSystem true A A : ℝ) ^ 2 -
        (#A : ℝ) ^ 2 * (G.edgeDensity A A : ℝ) ^ 2) = 0 := by
    refine sum_eq_zero fun A hA ↦ ?_
    have hempty : G.interedges A A = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun p hp ↦ ?_
      obtain ⟨h1, h2, hadj⟩ := G.mem_interedges_iff.1 hp
      exact hind A hA p.1 h1 p.2 h2 hadj
    have hd1 : pairColorDensity G.toPairColorSystem true A A = 0 := by
      rw [pairColorDensity_def, G.filter_toPairColorSystem_true, hempty]; simp
    have hd2 : G.edgeDensity A A = 0 := by simp [SimpleGraph.edgeDensity_def, hempty]
    simp [hd1, hd2]
  have hsum : ∑ p ∈ (univ : Finset V).offDiag,
        (pairColorDensity G.toPairColorSystem true (P.part p.1) (P.part p.2) : ℝ) ^ 2 =
      (Fintype.card V : ℝ) ^ 2 * G.weightedEnergy P :=
    sub_eq_zero.1 ((G.sum_sq_pairColorDensity_true_sub_weightedEnergy_eq P).trans hdiag_zero)
  rw [G.energy_toPairColorSystem_eq P hV, hsum, hcard_off]
  field_simp

/-- Lower bound comparing `G.toPairColorSystem.energy P` with `G.weightedEnergy P`: the pair-color
energy is at least `1 - 2 d_off(G) + 2 G.weightedEnergy P`, where `d_off(G)` is the global edge
density among distinct pairs. -/
theorem zero_le_energy_toPairColorSystem_sub (P : Finpartition (univ : Finset V))
    (hV : 2 ≤ Fintype.card V) :
    0 ≤ G.toPairColorSystem.energy P -
      (1 - 2 * (pairColorDensity G.toPairColorSystem true univ univ : ℝ) +
        2 * G.weightedEnergy P) := by
  have : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 (by omega)
  have hV1 : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := sub_pos.2 (Nat.one_lt_cast.2 (by omega))
  have hcard_off : (#(univ : Finset V).offDiag : ℝ) =
      (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
    rw [offDiag_card, card_univ, Nat.cast_sub (Nat.le_mul_self _)]; push_cast; ring
  have hE := (G.sum_sq_pairColorDensity_true_sub_weightedEnergy_bounds P).1
  have hW0 : 0 ≤ G.weightedEnergy P := G.weightedEnergy_nonneg P
  rw [G.energy_toPairColorSystem_eq P hV, hcard_off, mul_div_assoc]
  have hstep : G.weightedEnergy P ≤
      (∑ p ∈ (univ : Finset V).offDiag,
          (pairColorDensity G.toPairColorSystem true (P.part p.1) (P.part p.2) : ℝ) ^ 2) /
        ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Upper bound comparing `G.toPairColorSystem.energy P` with `G.weightedEnergy P`: the pair-color
energy exceeds `1 - 2 d_off(G) + 2 G.weightedEnergy P` by at most `4 / |V|`. This constant is
asymptotically sharp on complete graphs with the one-part partition, and holds for every finite
host without a size threshold. -/
theorem energy_toPairColorSystem_sub_le (P : Finpartition (univ : Finset V)) :
    G.toPairColorSystem.energy P -
      (1 - 2 * (pairColorDensity G.toPairColorSystem true univ univ : ℝ) +
        2 * G.weightedEnergy P) ≤ 4 / Fintype.card V := by
  rcases lt_or_ge (Fintype.card V) 2 with hV | hV
  · obtain ⟨hE, hW, hd, -⟩ := G.energy_and_densities_eq_zero_of_card_lt_two P hV
    rw [hE, hW, hd]
    have : (0 : ℝ) ≤ 4 / Fintype.card V := by positivity
    norm_num; linarith
  · have hVpos : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 (by omega)
    have hV1 : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := sub_pos.2 (Nat.one_lt_cast.2 (by omega))
    have hcard_off : (#(univ : Finset V).offDiag : ℝ) =
        (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
      rw [offDiag_card, card_univ, Nat.cast_sub (Nat.le_mul_self _)]; push_cast; ring
    have hparts : (1 : ℝ) ≤ #P.parts := by
      have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
      exact_mod_cast (P.parts_nonempty univ_nonempty.ne_empty).card_pos
    have hE := (G.sum_sq_pairColorDensity_true_sub_weightedEnergy_bounds P).2
    -- Since `G` is loopless, `G.weightedEnergy P ≤ G.edgeDensity univ univ ≤ (|V| - 1) / |V|`.
    have hWle : G.weightedEnergy P * (Fintype.card V : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by
      have hsub : G.interedges univ univ ⊆ (univ : Finset V).offDiag := fun p hp ↦
        mem_offDiag.2 ⟨mem_univ _, mem_univ _, G.ne_of_adj (G.mem_interedges_iff.1 hp).2.2⟩
      have hm : ((Fintype.card V : ℝ) * Fintype.card V) * (G.edgeDensity univ univ : ℝ) =
          #(G.interedges univ univ) := by
        simpa [card_univ] using G.card_mul_card_mul_edgeDensity_real univ univ
      have hcard : (#(G.interedges univ univ) : ℝ) ≤
          (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
        rw [← hcard_off]; exact_mod_cast card_le_card hsub
      have hdens : (G.edgeDensity univ univ : ℝ) * (Fintype.card V : ℝ) ≤
          (Fintype.card V : ℝ) - 1 := by nlinarith
      exact (mul_le_mul_of_nonneg_right (G.weightedEnergy_le_edgeDensity_univ P) hVpos.le).trans
        hdens
    rw [G.energy_toPairColorSystem_eq P hV, hcard_off, mul_div_assoc]
    have hstep : (∑ p ∈ (univ : Finset V).offDiag,
            (pairColorDensity G.toPairColorSystem true (P.part p.1) (P.part p.2) : ℝ) ^ 2) /
          ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) -
        G.weightedEnergy P ≤ 2 / Fintype.card V := by
      rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
      have : (2 / (Fintype.card V : ℝ)) * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) =
          2 * ((Fintype.card V : ℝ) - 1) := by field_simp
      nlinarith
    have : 2 * (2 / (Fintype.card V : ℝ)) = 4 / Fintype.card V := by ring
    linarith

/-- Comparison of `G.toPairColorSystem.energy P` directly with the graph quantities
`G.edgeDensity univ univ` and `G.weightedEnergy P`: on any nonempty host, the discrepancy is at
most `4 / |V|`. -/
theorem abs_energy_toPairColorSystem_sub_le [Nonempty V] (P : Finpartition (univ : Finset V)) :
    |G.toPairColorSystem.energy P -
        (1 - 2 * (G.edgeDensity univ univ : ℝ) + 2 * G.weightedEnergy P)| ≤
      4 / Fintype.card V := by
  rcases lt_or_ge (Fintype.card V) 2 with hV | hV
  · obtain ⟨hE, hW, -, hd⟩ := G.energy_and_densities_eq_zero_of_card_lt_two P hV
    have h1 : Fintype.card V = 1 := by have := Fintype.card_pos (α := V); omega
    rw [hE, hW, hd, h1]
    norm_num
  · have hVpos : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 (by omega)
    have hV1 : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := sub_pos.2 (Nat.one_lt_cast.2 (by omega))
    have hcard_off : (#(univ : Finset V).offDiag : ℝ) =
        (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
      rw [offDiag_card, card_univ, Nat.cast_sub (Nat.le_mul_self _)]; push_cast; ring
    have hoff : ((univ : Finset V) ×ˢ (univ : Finset V)).filter (fun p ↦ p.1 ≠ p.2) =
        (univ : Finset V).offDiag := by ext p; simp [mem_offDiag]
    have hdoff_mul : (pairColorDensity G.toPairColorSystem true univ univ : ℝ) *
        ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) = #(G.interedges univ univ) := by
      rw [← hcard_off, ← hoff]
      exact_mod_cast G.pairColorDensity_toPairColorSystem_true_mul_card_support univ univ
    have hdall_mul : ((Fintype.card V : ℝ) * Fintype.card V) * (G.edgeDensity univ univ : ℝ) =
        #(G.interedges univ univ) := by
      simpa [card_univ] using G.card_mul_card_mul_edgeDensity_real univ univ
    have hd_diff : (pairColorDensity G.toPairColorSystem true univ univ : ℝ) -
        (G.edgeDensity univ univ : ℝ) =
        (G.edgeDensity univ univ : ℝ) / ((Fintype.card V : ℝ) - 1) := by
      rw [eq_div_iff hV1.ne']; nlinarith
    have hd_nonneg : 0 ≤ (pairColorDensity G.toPairColorSystem true univ univ : ℝ) -
        (G.edgeDensity univ univ : ℝ) :=
      hd_diff ▸ div_nonneg (mod_cast G.edgeDensity_nonneg univ univ) hV1.le
    have hd_le : (pairColorDensity G.toPairColorSystem true univ univ : ℝ) -
        (G.edgeDensity univ univ : ℝ) ≤ 1 / Fintype.card V := by
      rw [hd_diff, div_le_div_iff₀ hV1 hVpos]
      have hsub : G.interedges univ univ ⊆ (univ : Finset V).offDiag := fun p hp ↦
        mem_offDiag.2 ⟨mem_univ _, mem_univ _, G.ne_of_adj (G.mem_interedges_iff.1 hp).2.2⟩
      have hcard : (#(G.interedges univ univ) : ℝ) ≤
          (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
        rw [← hcard_off]; exact_mod_cast card_le_card hsub
      nlinarith
    have hlo := G.zero_le_energy_toPairColorSystem_sub P hV
    have hhi := G.energy_toPairColorSystem_sub_le P
    have : 4 / (Fintype.card V : ℝ) = 4 * (1 / Fintype.card V) := by ring
    have : (0 : ℝ) ≤ 1 / Fintype.card V := by positivity
    rw [abs_le]
    constructor <;> linarith

/-- **Comparison of pair-color and weighted graph energy gaps.** For any two partitions `P` and `Q`
of the vertices of `G`, the pair-color energy gap differs from twice the size-weighted graph energy
gap by at most `4 / |V|`. No host-size or refinement hypothesis is needed. -/
theorem abs_energy_toPairColorSystem_sub_sub_two_mul_weightedEnergy_sub_le
    (P Q : Finpartition (univ : Finset V)) :
    |(G.toPairColorSystem.energy Q - G.toPairColorSystem.energy P) -
        2 * (G.weightedEnergy Q - G.weightedEnergy P)| ≤ 4 / Fintype.card V := by
  rcases lt_or_ge (Fintype.card V) 2 with hV | hV
  · obtain ⟨hEQ, hWQ, -, -⟩ := G.energy_and_densities_eq_zero_of_card_lt_two Q hV
    obtain ⟨hEP, hWP, -, -⟩ := G.energy_and_densities_eq_zero_of_card_lt_two P hV
    rw [hEQ, hEP, hWQ, hWP]
    simp only [sub_self, mul_zero, abs_zero]
    positivity
  · have hP0 := G.zero_le_energy_toPairColorSystem_sub P hV
    have hP1 := G.energy_toPairColorSystem_sub_le P
    have hQ0 := G.zero_le_energy_toPairColorSystem_sub Q hV
    have hQ1 := G.energy_toPairColorSystem_sub_le Q
    rw [abs_le]
    constructor <;> linarith

/-- A weighted graph energy gap of at most `ε` implies a pair-color energy gap of at most
`2 ε + 4 / |V|`. -/
theorem energy_toPairColorSystem_sub_le_of_weightedEnergy_sub_le
    {P Q : Finpartition (univ : Finset V)} {ε : ℝ}
    (h : G.weightedEnergy Q - G.weightedEnergy P ≤ ε) :
    G.toPairColorSystem.energy Q - G.toPairColorSystem.energy P ≤ 2 * ε + 4 / Fintype.card V := by
  have hgap := (abs_le.1
    (G.abs_energy_toPairColorSystem_sub_sub_two_mul_weightedEnergy_sub_le P Q)).2
  linarith

/-- A pair-color energy gap of at most `ε` implies a weighted graph energy gap of at most
`ε / 2 + 2 / |V|`. -/
theorem weightedEnergy_sub_le_of_energy_toPairColorSystem_sub_le
    {P Q : Finpartition (univ : Finset V)} {ε : ℝ}
    (h : G.toPairColorSystem.energy Q - G.toPairColorSystem.energy P ≤ ε) :
    G.weightedEnergy Q - G.weightedEnergy P ≤ ε / 2 + 2 / Fintype.card V := by
  have hgap := (abs_le.1
    (G.abs_energy_toPairColorSystem_sub_sub_two_mul_weightedEnergy_sub_le P Q)).1
  have h24 : 4 / (Fintype.card V : ℝ) = 2 * (2 / Fintype.card V) := by ring
  linarith

end SimpleGraph
