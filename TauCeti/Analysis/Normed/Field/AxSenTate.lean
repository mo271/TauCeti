/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Log
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.RingTheory.Polynomial.Vieta
import TauCeti.Analysis.Normed.Field.GaloisAction
import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# The Ax–Sen lemma and the Ax–Sen–Tate fixed-point theorem

Let `L` be an algebraically closed ultrametric normed field of mixed characteristic `(0, p)` (that
is, `(p : L) ≠ 0` and `‖(p : L)‖ < 1` for a prime `p`), and let `F` be a subfield over which `L`
is algebraic and whose `F`-automorphisms act by isometries.

The **Ax–Sen lemma** (`TauCeti.exists_norm_sub_algebraMap_le_of_forall_norm_sub_le`) gives a
quantitative descent estimate: if every `F`-conjugate of `α ∈ L` lies within distance `M` of `α`,
then there is an element `a ∈ F` within distance `‖(p : L)‖⁻¹ ^ (p / (p - 1)²) * M` of `α`.

The proof proceeds by strong induction on `d = [F(α) : F]` using Hasse derivatives of the minimal
polynomial `f = minpoly F α`. Evaluating the `k`-th Hasse derivative `Dᵏ f` at `α` expresses
`(Dᵏ f)(α)` as a signed elementary symmetric polynomial in `{r - α}` over the roots `r` of `f`,
so `‖(Dᵏ f)(α)‖ ≤ M ^ (d - k)`, while its leading coefficient is `d.choose k`.
* When `d` is not a power of `p`, choosing `k = p ^ v_p(d)` gives `p ∤ d.choose k` by Lucas's
  theorem, so `‖d.choose k‖ = 1` and `Dᵏ f` has a root `β` of strictly smaller degree with
  `‖α - β‖ ≤ M` (no loss).
* When `d = p ^ r` (`r ≥ 1`), choosing `k = p ^ (r - 1)` gives `v_p(d.choose k) = 1`, so `Dᵏ f` has
  a root `β` of degree `≤ (p - 1) p ^ (r - 1) < p ^ r` with
  `‖α - β‖ ≤ ‖p‖⁻¹ ^ (((p - 1) p ^ (r - 1))⁻¹) * M`.
Summing the exponents over `j < ⌊log_p d⌋` yields a geometric series strictly below
`p / (p - 1)²`.

Approximating elements of `UniformSpace.Completion L` by elements of `L` yields the **Ax–Sen–Tate
theorem**:
* For any closed subgroup `H` of `L ≃ₐ[K] L`, the `H`-fixed points of `UniformSpace.Completion L`
  equal the closure of the fixed field `L ^ H`
  (`TauCeti.forall_completion_map_eq_iff_mem_closure_fixedField`).
* When `K` is complete and `E` is a finite-dimensional intermediate field of `L / K`, `E` is
  complete and hence closed in `UniformSpace.Completion L`, so the `(L ≃ₐ[E] L)`-fixed points are
  exactly `E` (`TauCeti.forall_completion_map_eq_iff_exists_of_finiteDimensional`) and the
  `(L ≃ₐ[K] L)`-fixed points are exactly `K`
  (`TauCeti.forall_completion_map_eq_iff_exists_algebraMap`).

## Main results

* `TauCeti.exists_norm_sub_algebraMap_le_of_forall_norm_sub_le`: the Ax–Sen lemma with constant
  `‖(p : L)‖⁻¹ ^ ((p : ℝ) / ((p : ℝ) - 1) ^ 2)`.
* `TauCeti.forall_completion_map_eq_iff_mem_closure_fixedField`: Ax–Sen–Tate for a closed subgroup
  `H` of `L ≃ₐ[K] L`.
* `TauCeti.forall_completion_map_eq_iff_exists_of_finiteDimensional`: Ax–Sen–Tate for a
  finite-dimensional intermediate field `E` over a complete ultrametric field `K`.
* `TauCeti.forall_completion_map_eq_iff_exists_algebraMap`: Ax–Sen–Tate over a complete
  ultrametric field `K`.

## References

* J. Ax, *Zeros of polynomials over local fields — the Galois action*, J. Algebra 15 (1970),
  417–428.
* O. Brinon and B. Conrad, *CMI Summer School Notes on `p`-adic Hodge Theory*, §2.1,
  Proposition 2.1.2, p. 12.
* J.-M. Fontaine and Y. Ouyang, *Theory of `p`-adic Galois Representations*, §4.1.2,
  Propositions 4.3 and 4.9, pp. 89–91.
-/

public section

namespace TauCeti

open Polynomial

section Helpers

/-- Evaluating the `k`-th Hasse derivative of `∏_{r ∈ s} (X - r)` at `α` in an ultrametric normed
field is bounded by `M ^ (s.card - k)` whenever `‖r - α‖ ≤ M` for all `r ∈ s`. -/
private theorem norm_eval_hasseDeriv_prod_X_sub_C_le {L : Type*} [NormedField L]
    [IsUltrametricDist L] (s : Multiset L) (α : L) {k : ℕ} (hk : k ≤ s.card) {M : ℝ}
    (hM : 0 ≤ M) (hs : ∀ r ∈ s, ‖r - α‖ ≤ M) :
    ‖(hasseDeriv k (s.map fun r ↦ X - C r).prod).eval α‖ ≤ M ^ (s.card - k) := by
  rw [← taylor_coeff]
  have htaylor : taylor α (s.map fun r ↦ X - C r).prod =
      ((s.map (· - α)).map fun y ↦ X - C y).prod := by
    rw [← taylorAlgHom_apply, map_multiset_prod, Multiset.map_map, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun r _ ↦ ?_)
    rw [Function.comp_apply, Function.comp_apply, taylorAlgHom_apply, map_sub, taylor_X, taylor_C,
      map_sub]
    ring
  rw [htaylor, Multiset.prod_X_sub_C_coeff (s.map (· - α)) (by simpa using hk),
    Multiset.card_map, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Multiset.esymm]
  set t := s.map (· - α)
  set m := s.card - k
  obtain ⟨u, hu_mem, hle⟩ :=
    IsUltrametricDist.exists_norm_multiset_sum_le (t.powersetCard m) (f := Multiset.prod)
  by_cases hne : t.powersetCard m = 0
  · simp [hne, pow_nonneg hM]
  · refine hle.trans ?_
    obtain ⟨hut, hcard⟩ := Multiset.mem_powersetCard.mp (hu_mem hne)
    rw [Multiset.norm_prod]
    calc (u.map norm).prod ≤ (u.map fun _ ↦ M).prod :=
          Multiset.prod_map_le_prod_map₀ norm (fun _ ↦ M) (fun _ _ ↦ norm_nonneg _) fun y hy ↦ by
            obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp (Multiset.subset_of_le hut hy)
            exact hs r hr
      _ = M ^ m := by rw [Multiset.map_const', Multiset.prod_replicate, hcard]

/-- If a polynomial `Q` splits over a normed field `L` with `1 ≤ Q.natDegree` and
`‖Q.eval α‖ ≤ B`, then `Q` has a root `β` satisfying
`‖α - β‖ ≤ (B / ‖Q.leadingCoeff‖) ^ (1 / (Q.natDegree : ℝ))`. -/
private theorem exists_root_norm_sub_le {L : Type*} [NormedField L] {Q : L[X]}
    (hQ : Q.Splits) (hdeg : 1 ≤ Q.natDegree) (α : L) {B : ℝ} (heval : ‖Q.eval α‖ ≤ B) :
    ∃ β ∈ Q.roots, ‖α - β‖ ≤ (B / ‖Q.leadingCoeff‖) ^ (1 / (Q.natDegree : ℝ)) := by
  classical
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hlc : 0 < ‖Q.leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hQ0)
  have hcard : Q.roots.card = Q.natDegree := hQ.natDegree_eq_card_roots.symm
  have hne : Q.roots.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty, ← Multiset.card_pos, hcard]
    omega
  obtain ⟨β, hβ_mem, hβ_min⟩ := Q.roots.toFinset.exists_min_image (fun r ↦ ‖α - r‖) hne
  refine ⟨β, Multiset.mem_toFinset.mp hβ_mem, ?_⟩
  have hpow : ‖α - β‖ ^ Q.natDegree ≤ B / ‖Q.leadingCoeff‖ := by
    rw [le_div_iff₀ hlc]
    calc ‖α - β‖ ^ Q.natDegree * ‖Q.leadingCoeff‖
        = ‖Q.leadingCoeff‖ * (Q.roots.map fun _ ↦ ‖α - β‖).prod := by
          rw [mul_comm, Multiset.map_const', Multiset.prod_replicate, hcard]
      _ ≤ ‖Q.leadingCoeff‖ * (Q.roots.map fun r ↦ ‖α - r‖).prod := by
          refine mul_le_mul_of_nonneg_left ?_ hlc.le
          exact Multiset.prod_map_le_prod_map₀ (fun _ ↦ ‖α - β‖) (fun r ↦ ‖α - r‖)
            (fun _ _ ↦ norm_nonneg _) fun r hr ↦ hβ_min r (Multiset.mem_toFinset.mpr hr)
      _ = ‖Q.eval α‖ := by
          rw [hQ.eval_eq_prod_roots α, norm_mul, Multiset.norm_prod, Multiset.map_map]
          rfl
      _ ≤ B := heval
  have hm : (0 : ℝ) < (Q.natDegree : ℝ) := by exact_mod_cast hdeg
  calc ‖α - β‖ = (‖α - β‖ ^ (Q.natDegree : ℝ)) ^ (1 / (Q.natDegree : ℝ)) := by
        rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hm.ne', Real.rpow_one]
    _ = (‖α - β‖ ^ Q.natDegree) ^ (1 / (Q.natDegree : ℝ)) := by rw [Real.rpow_natCast]
    _ ≤ (B / ‖Q.leadingCoeff‖) ^ (1 / (Q.natDegree : ℝ)) :=
        Real.rpow_le_rpow (pow_nonneg (norm_nonneg _) _) hpow (by positivity)

/-- For `f = minpoly F α` of degree `d` and any `k < d` with `(d.choose k : L) ≠ 0`, the `k`-th
Hasse derivative `Dᵏ f` has a root `β : L` of degree `≤ d - k` satisfying
`‖α - β‖ ≤ ‖(d.choose k : L)‖⁻¹ ^ ((d - k : ℕ) : ℝ)⁻¹ * M`. -/
private theorem exists_root_hasseDeriv_norm_sub_le {F L : Type*} [Field F] [NormedField L]
    [IsUltrametricDist L] [Algebra F L] [IsAlgClosed L] [Algebra.IsAlgebraic F L]
    (α : L) {M : ℝ} (hα : ∀ σ : L ≃ₐ[F] L, ‖σ α - α‖ ≤ M) {k : ℕ}
    (hkd : k < (minpoly F α).natDegree)
    (hchoose0 : (((minpoly F α).natDegree.choose k : ℕ) : L) ≠ 0) :
    ∃ β : L, (minpoly F β).natDegree ≤ (minpoly F α).natDegree - k ∧
      ‖α - β‖ ≤ ‖(((minpoly F α).natDegree.choose k : ℕ) : L)‖⁻¹ ^
        (((minpoly F α).natDegree - k : ℕ) : ℝ)⁻¹ * M := by
  have hM : 0 ≤ M := by simpa using hα 1
  have hnorm : Normal F L := ⟨fun _ ↦ IsAlgClosed.splits _⟩
  have hint : IsIntegral F α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set f : F[X] := minpoly F α
  set d : ℕ := f.natDegree
  have hf_monic : f.Monic := minpoly.monic hint
  set P : L[X] := f.map (algebraMap F L)
  have hP_splits : P.Splits := IsAlgClosed.splits P
  have hP_monic : P.Monic := hf_monic.map (algebraMap F L)
  have hP_roots : ∀ r ∈ P.roots, ‖r - α‖ ≤ M := fun r hr ↦ by
    have hconj : IsConjRoot F α r := (isConjRoot_iff_mem_minpoly_aroots hint).mpr hr
    obtain ⟨σ, hσ⟩ := isConjRoot_iff_exists_algEquiv.mp hconj.symm
    exact hσ ▸ hα σ
  have hP_card : P.roots.card = d := by
    rw [← hP_splits.natDegree_eq_card_roots,
      Polynomial.natDegree_map_eq_of_injective (algebraMap F L).injective]
  set g : F[X] := hasseDeriv k f
  set Q : L[X] := g.map (algebraMap F L)
  have hchooseF : ((d.choose k : ℕ) : F) ≠ 0 := fun h0 ↦
    hchoose0 (by simpa using congrArg (algebraMap F L) h0)
  have hg_coeff_top : g.coeff (d - k) = (d.choose k : F) := by
    rw [Polynomial.hasseDeriv_coeff, Nat.sub_add_cancel hkd.le, hf_monic.coeff_natDegree, mul_one]
  have hg_deg : g.natDegree = d - k := by
    refine le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦ ?_) ?_
    · rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        mul_zero]
    · exact Polynomial.le_natDegree_of_ne_zero (by rw [hg_coeff_top]; exact hchooseF)
  have hQ_deg : Q.natDegree = d - k := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap F L).injective, hg_deg]
  have hQ_lc : Q.leadingCoeff = ((d.choose k : ℕ) : L) := by
    rw [Polynomial.leadingCoeff, hQ_deg, Polynomial.coeff_map, hg_coeff_top, map_natCast]
  have hQ_eq : Q = hasseDeriv k P := (Polynomial.hasseDeriv_map (algebraMap F L) k f).symm
  have hQ_eval : ‖Q.eval α‖ ≤ M ^ (d - k) := by
    rw [hQ_eq, hP_splits.eq_prod_roots_of_monic hP_monic]
    simpa only [hP_card] using
      norm_eval_hasseDeriv_prod_X_sub_C_le P.roots α (hP_card.symm ▸ hkd.le) hM hP_roots
  obtain ⟨β, hβ_root, hβ_dist⟩ :=
    exists_root_norm_sub_le (IsAlgClosed.splits Q) (by omega) α hQ_eval
  have hg0 : g ≠ 0 := fun h0 ↦ by
    rw [h0, Polynomial.natDegree_zero] at hg_deg
    omega
  have hβ_aeval : aeval β g = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact Polynomial.isRoot_of_mem_roots hβ_root
  refine ⟨β, hg_deg ▸ Polynomial.natDegree_le_of_dvd (minpoly.dvd F β hβ_aeval) hg0,
    hβ_dist.trans_eq ?_⟩
  rw [hQ_deg, hQ_lc, one_div, div_eq_inv_mul,
    Real.mul_rpow (inv_nonneg.mpr (norm_nonneg _)) (pow_nonneg hM _),
    ← Real.rpow_natCast M (d - k), ← Real.rpow_mul hM]
  have hdk_pos : (0 : ℝ) < ((d - k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d - k)
  rw [mul_inv_cancel₀ hdk_pos.ne', Real.rpow_one]

/-- If every `F`-conjugate of `α` lies within `M ≤ Δ` of `α` and `‖α - β‖ ≤ Δ`, then every
`F`-conjugate of `β` lies within `Δ` of `β`. -/
private theorem forall_norm_sub_le_of_norm_sub_le {F L : Type*} [Field F] [NormedField L]
    [IsUltrametricDist L] [Algebra F L] (hiso : ∀ σ : L ≃ₐ[F] L, Isometry σ)
    {α β : L} {M Δ : ℝ} (hα : ∀ σ : L ≃ₐ[F] L, ‖σ α - α‖ ≤ M) (hMΔ : M ≤ Δ)
    (hαβ : ‖α - β‖ ≤ Δ) (σ : L ≃ₐ[F] L) : ‖σ β - β‖ ≤ Δ := by
  have heq : σ β - β = (σ β - σ α) + (σ α - α) + (α - β) := by ring
  rw [heq]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hαβ)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ((hα σ).trans hMΔ))
  rw [← dist_eq_norm, (hiso σ).dist_eq, dist_comm, dist_eq_norm]
  exact hαβ

/-- The finite partial-sum exponent appearing in the Ax–Sen induction for degree `d` at prime `p`:
`∑ j < Nat.log p d, ((p - 1) * p ^ j)⁻¹`. -/
private noncomputable def axSenExponent (p d : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log p d), (((p - 1 : ℕ) : ℝ) * (p : ℝ) ^ j)⁻¹

private theorem axSenExponent_nonneg (p d : ℕ) : 0 ≤ axSenExponent p d :=
  Finset.sum_nonneg fun _ _ ↦ by positivity

private theorem axSenExponent_mono {p d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    axSenExponent p d₁ ≤ axSenExponent p d₂ :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.log_mono_right h))
    fun _ _ _ ↦ by positivity

private theorem axSenExponent_add_inv_le {p r d' : ℕ} (hp : p.Prime) (hr1 : 1 ≤ r)
    (hd' : d' < p ^ r) :
    axSenExponent p d' + (((p ^ r - p ^ (r - 1) : ℕ) : ℝ))⁻¹ ≤ axSenExponent p (p ^ r) := by
  have hdk_eq : p ^ r - p ^ (r - 1) = (p - 1) * p ^ (r - 1) := by
    have hpr : p ^ r = p * p ^ (r - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hr1, pow_succ']
    rw [hpr]
    calc p * p ^ (r - 1) - p ^ (r - 1) = p * p ^ (r - 1) - 1 * p ^ (r - 1) := by rw [one_mul]
      _ = (p - 1) * p ^ (r - 1) := (Nat.sub_mul p 1 (p ^ (r - 1))).symm
  have hlog_d' : Nat.log p d' ≤ r - 1 := by
    have hlt : Nat.log p d' < r := Nat.log_lt_of_lt_pow' (by omega) hd'
    omega
  have hsum_le : axSenExponent p d' ≤
      ∑ j ∈ Finset.range (r - 1), (((p - 1 : ℕ) : ℝ) * (p : ℝ) ^ j)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hlog_d')
      fun _ _ _ ↦ by positivity
  have hsum_d : axSenExponent p (p ^ r) =
      (∑ j ∈ Finset.range (r - 1), (((p - 1 : ℕ) : ℝ) * (p : ℝ) ^ j)⁻¹) +
        (((p - 1 : ℕ) : ℝ) * (p : ℝ) ^ (r - 1))⁻¹ := by
    conv_lhs => rw [axSenExponent, Nat.log_pow hp.one_lt, ← Nat.sub_add_cancel hr1,
      Finset.sum_range_succ]
  rw [hsum_d, hdk_eq, Nat.cast_mul, Nat.cast_pow]
  linarith

private theorem axSenExponent_lt {p : ℕ} (hp : p.Prime) (d : ℕ) :
    axSenExponent p d < (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hsub : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  have hfactor : axSenExponent p d =
      ((p : ℝ) - 1)⁻¹ * ∑ j ∈ Finset.range (Nat.log p d), ((p : ℝ)⁻¹) ^ j := by
    rw [axSenExponent, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hsub, mul_inv, inv_pow]
  have hinv_ne : (p : ℝ)⁻¹ ≠ 1 := ne_of_lt (inv_lt_one_of_one_lt₀ hp1)
  have hpos : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)
  have hgeom : ∑ j ∈ Finset.range (Nat.log p d), ((p : ℝ)⁻¹) ^ j =
      (1 - ((p : ℝ)⁻¹) ^ (Nat.log p d)) / (1 - (p : ℝ)⁻¹) := by
    rw [geom_sum_eq hinv_ne, ← neg_div_neg_eq, neg_sub, neg_sub]
  have hpow_pos : (0 : ℝ) < ((p : ℝ)⁻¹) ^ (Nat.log p d) := by positivity
  rw [hfactor, hgeom]
  calc ((p : ℝ) - 1)⁻¹ * ((1 - ((p : ℝ)⁻¹) ^ (Nat.log p d)) / (1 - (p : ℝ)⁻¹))
      < ((p : ℝ) - 1)⁻¹ * (1 / (1 - (p : ℝ)⁻¹)) := by
        gcongr
        linarith
    _ = (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
        have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
        have h2 : (p : ℝ) ≠ 0 := by linarith
        field_simp

/-- Prime-power reduction step in the Ax–Sen induction: if `(minpoly F α).natDegree = p ^ r` with
`r ≥ 1`, then `D^{p ^ (r - 1)} (minpoly F α)` has a root `β` of strictly smaller degree within
distance `‖(p : L)‖⁻¹ ^ ((p ^ r - p ^ (r - 1) : ℕ) : ℝ)⁻¹ * M` of `α`. -/
private theorem exists_lt_natDegree_of_prime_pow {F L : Type*} [Field F] [NormedField L]
    [IsUltrametricDist L] [Algebra F L] [IsAlgClosed L] [Algebra.IsAlgebraic F L]
    {p r : ℕ} (hp : p.Prime) (hp0 : (p : L) ≠ 0) (hp1 : ‖(p : L)‖ < 1) (hr1 : 1 ≤ r)
    (α : L) {M : ℝ} (hd : (minpoly F α).natDegree = p ^ r)
    (hα : ∀ σ : L ≃ₐ[F] L, ‖σ α - α‖ ≤ M) :
    ∃ β : L, (minpoly F β).natDegree < p ^ r ∧
      ‖α - β‖ ≤ ‖(p : L)‖⁻¹ ^ (((p ^ r - p ^ (r - 1) : ℕ) : ℝ))⁻¹ * M := by
  set k := p ^ (r - 1)
  have hk1 : 1 ≤ k := Nat.one_le_pow _ _ hp.pos
  have hkd : k < p ^ r := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hchoose_pos : 0 < (p ^ r).choose k := Nat.choose_pos hkd.le
  have hchoose_fact : ((p ^ r).choose k).factorization p = 1 := by
    rw [Nat.factorization_choose_prime_pow hp hkd.le (by omega),
      hp.factorization_pow, Finsupp.single_eq_same]
    omega
  have hchoose_norm : ‖(((p ^ r).choose k : ℕ) : L)‖ = ‖(p : L)‖ := by
    rw [IsUltrametricDist.norm_natCast_eq_pow_factorization hp hp1 hchoose_pos.ne',
      hchoose_fact, pow_one]
  have hchoose0 : (((p ^ r).choose k : ℕ) : L) ≠ 0 := by
    rw [← norm_ne_zero_iff, hchoose_norm]
    exact norm_ne_zero_iff.mpr hp0
  obtain ⟨β, hβ_deg, hβ_dist⟩ :=
    exists_root_hasseDeriv_norm_sub_le α hα (hd ▸ hkd) (hd ▸ hchoose0)
  rw [hd] at hβ_deg hβ_dist
  rw [hchoose_norm] at hβ_dist
  exact ⟨β, by omega, hβ_dist⟩

/-- Non-prime-power reduction step in the Ax–Sen induction: if `d = (minpoly F α).natDegree` has
`p`-free part `m ≥ 2`, then `D^{p ^ v_p(d)} (minpoly F α)` has a root `β` of strictly smaller
degree within distance `M` of `α`. -/
private theorem exists_lt_natDegree_of_not_prime_pow {F L : Type*} [Field F] [NormedField L]
    [IsUltrametricDist L] [Algebra F L] [IsAlgClosed L] [Algebra.IsAlgebraic F L]
    {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : L)‖ < 1)
    (α : L) {M : ℝ} (hd_pos : 0 < (minpoly F α).natDegree)
    (hm : ordCompl[p] (minpoly F α).natDegree ≠ 1)
    (hα : ∀ σ : L ≃ₐ[F] L, ‖σ α - α‖ ≤ M) :
    ∃ β : L, (minpoly F β).natDegree < (minpoly F α).natDegree ∧ ‖α - β‖ ≤ M := by
  set d := (minpoly F α).natDegree
  set r := d.factorization p
  set m := ordCompl[p] d
  have hdm : p ^ r * m = d := Nat.ordProj_mul_ordCompl_eq_self d p
  have hnd_m : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hd_pos.ne'
  have hm_pos : 0 < m := Nat.pos_of_ne_zero fun hm0 ↦ by rw [hm0, mul_zero] at hdm; omega
  set k := p ^ r
  have hk1 : 1 ≤ k := Nat.one_le_pow _ _ hp.pos
  have hkd : k < d := by rw [← hdm]; exact lt_mul_of_one_lt_right hk1 (by omega)
  have hmod : d.choose k ≡ m [MOD p] := by
    have : Fact p.Prime := ⟨hp⟩
    have h1 : d.choose k = (p ^ r * m).choose (p ^ r * 1) := by rw [hdm, mul_one]
    rw [h1]
    simpa only [Nat.choose_one_right] using
      (Choose.choose_pow_mul_pow_mul_modEq_choose_nat (p := p) (k := r) (a := m) (b := 1))
  have hnd_choose : ¬ p ∣ d.choose k := fun hdvd ↦
    hnd_m ((Nat.ModEq.dvd_iff hmod (dvd_refl p)).mp hdvd)
  have hchoose_norm : ‖((d.choose k : ℕ) : L)‖ = 1 :=
    IsUltrametricDist.norm_natCast_eq_one_of_coprime (hp.coprime_iff_not_dvd.mpr hnd_choose) hp1
  have hchoose0 : ((d.choose k : ℕ) : L) ≠ 0 := by
    rw [← norm_ne_zero_iff, hchoose_norm]
    exact one_ne_zero
  obtain ⟨β, hβ_deg, hβ_dist⟩ := exists_root_hasseDeriv_norm_sub_le α hα hkd hchoose0
  rw [hchoose_norm, inv_one, Real.one_rpow, one_mul] at hβ_dist
  exact ⟨β, by omega, hβ_dist⟩

/-- The degree-dependent Ax–Sen bound proved by strong induction on `(minpoly F α).natDegree`. -/
private theorem axSen_induction {F L : Type*} [Field F] [NormedField L] [IsUltrametricDist L]
    [Algebra F L] [IsAlgClosed L] [Algebra.IsAlgebraic F L]
    {p : ℕ} (hp : p.Prime) (hp0 : (p : L) ≠ 0) (hp1 : ‖(p : L)‖ < 1)
    (hiso : ∀ σ : L ≃ₐ[F] L, Isometry σ) :
    ∀ n : ℕ, ∀ (α : L) (M : ℝ), (minpoly F α).natDegree = n →
      (∀ σ : L ≃ₐ[F] L, ‖σ α - α‖ ≤ M) →
      ∃ a : F, ‖α - algebraMap F L a‖ ≤ ‖(p : L)‖⁻¹ ^ axSenExponent p n * M := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind d ih =>
    intro α M hd hα
    have hM : 0 ≤ M := by simpa using hα 1
    have hq_pos : 0 < ‖(p : L)‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hp0)
    have hq_ge : 1 ≤ ‖(p : L)‖⁻¹ := (one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hp0, hp1⟩).le
    have hd_pos : 0 < d := hd ▸ minpoly.natDegree_pos (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
    -- Base case `d = 1`: `α` already lies in the image of `F`.
    by_cases hd1 : d = 1
    · obtain ⟨a, ha⟩ := (minpoly.natDegree_eq_one_iff (A := F) (x := α)).mp (hd.trans hd1)
      exact ⟨a, by rw [ha, sub_self, norm_zero]; positivity⟩
    -- Inductive step: split according to whether `d` is a power of `p`.
    by_cases hm1 : ordCompl[p] d = 1
    · set r := d.factorization p
      have hdr : d = p ^ r := by
        simpa [r, hm1] using (Nat.ordProj_mul_ordCompl_eq_self d p).symm
      have hr1 : 1 ≤ r := by
        by_contra! hr0
        have hr_eq : r = 0 := by omega
        rw [hr_eq, pow_zero] at hdr
        omega
      obtain ⟨β, hβ_lt, hβ_dist⟩ :=
        exists_lt_natDegree_of_prime_pow hp hp0 hp1 hr1 α (hd.trans hdr) hα
      set c := ‖(p : L)‖⁻¹ ^ (((p ^ r - p ^ (r - 1) : ℕ) : ℝ))⁻¹
      have hM_le : M ≤ c * M := le_mul_of_one_le_left hM (Real.one_le_rpow hq_ge (by positivity))
      obtain ⟨a, ha⟩ := ih (minpoly F β).natDegree (hdr ▸ hβ_lt) β (c * M) rfl
        (forall_norm_sub_le_of_norm_sub_le hiso hα hM_le hβ_dist)
      have hexp := axSenExponent_add_inv_le hp hr1 hβ_lt
      have hbound_β : ‖β - algebraMap F L a‖ ≤ ‖(p : L)‖⁻¹ ^ axSenExponent p d * M := by
        rw [hdr]
        calc ‖β - algebraMap F L a‖
            ≤ ‖(p : L)‖⁻¹ ^ axSenExponent p (minpoly F β).natDegree * (c * M) := ha
          _ = ‖(p : L)‖⁻¹ ^ (axSenExponent p (minpoly F β).natDegree +
                (((p ^ r - p ^ (r - 1) : ℕ) : ℝ))⁻¹) * M := by
              rw [← mul_assoc, ← Real.rpow_add hq_pos]
          _ ≤ ‖(p : L)‖⁻¹ ^ axSenExponent p (p ^ r) * M := by gcongr
      have hbound_αβ : ‖α - β‖ ≤ ‖(p : L)‖⁻¹ ^ axSenExponent p d * M := by
        rw [hdr]
        have hle : (((p ^ r - p ^ (r - 1) : ℕ) : ℝ))⁻¹ ≤ axSenExponent p (p ^ r) := by
          linarith [axSenExponent_nonneg p (minpoly F β).natDegree]
        exact hβ_dist.trans (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hq_ge hle) hM)
      refine ⟨a, ?_⟩
      rw [← sub_add_sub_cancel α β (algebraMap F L a)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hbound_αβ hbound_β)
    · obtain ⟨β, hβ_lt, hβ_dist⟩ :=
        exists_lt_natDegree_of_not_prime_pow hp hp1 α (hd ▸ hd_pos) (hd ▸ hm1) hα
      obtain ⟨a, ha⟩ := ih (minpoly F β).natDegree (hd ▸ hβ_lt) β M rfl
        (forall_norm_sub_le_of_norm_sub_le hiso hα le_rfl hβ_dist)
      have hbound_β : ‖β - algebraMap F L a‖ ≤ ‖(p : L)‖⁻¹ ^ axSenExponent p d * M :=
        ha.trans (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hq_ge (axSenExponent_mono (hd ▸ hβ_lt).le)) hM)
      have hbound_αβ : ‖α - β‖ ≤ ‖(p : L)‖⁻¹ ^ axSenExponent p d * M :=
        hβ_dist.trans (le_mul_of_one_le_left hM (Real.one_le_rpow hq_ge (axSenExponent_nonneg p d)))
      refine ⟨a, ?_⟩
      rw [← sub_add_sub_cancel α β (algebraMap F L a)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hbound_αβ hbound_β)

/-- If an isometric automorphism `σ` of `L` fixes `x : UniformSpace.Completion L`, then
`‖σ α - α‖ ≤ 2 * dist x α` for every `α : L`. -/
private theorem norm_sub_le_two_mul_dist_of_completion_map_eq {K L : Type*} [Field K]
    [NormedField L] [Algebra K L] {σ : L ≃ₐ[K] L} (hiso : Isometry σ)
    {x : UniformSpace.Completion L} (hx : UniformSpace.Completion.map σ x = x) (α : L) :
    ‖σ α - α‖ ≤ 2 * dist x (α : UniformSpace.Completion L) := by
  calc ‖σ α - α‖
      = dist (σ α) α := (dist_eq_norm _ _).symm
    _ = dist (σ α : UniformSpace.Completion L) (α : UniformSpace.Completion L) :=
        (UniformSpace.Completion.coe_isometry.dist_eq _ _).symm
    _ = dist (UniformSpace.Completion.map σ (α : UniformSpace.Completion L))
          (α : UniformSpace.Completion L) := by
        rw [UniformSpace.Completion.map_coe hiso.uniformContinuous]
    _ ≤ dist (UniformSpace.Completion.map σ (α : UniformSpace.Completion L)) x +
        dist x (α : UniformSpace.Completion L) := dist_triangle _ _ _
    _ = dist (α : UniformSpace.Completion L) x + dist x (α : UniformSpace.Completion L) := by
        conv_lhs => arg 1; rw [← hx, hiso.completion_map.dist_eq]
    _ = 2 * dist x (α : UniformSpace.Completion L) := by rw [dist_comm _ x]; ring

end Helpers

/-- **The Ax–Sen lemma.** Let `L / F` be an algebraic extension with `L` an algebraically closed
ultrametric normed field in which a prime `p` satisfies `(p : L) ≠ 0` and `‖(p : L)‖ < 1`. If every
`σ : L ≃ₐ[F] L` is an isometry and `‖σ α - α‖ ≤ M` for all `σ`, then there exists `a : F` such that
`‖α - algebraMap F L a‖ ≤ ‖(p : L)‖⁻¹ ^ (p / (p - 1)²) * M`. -/
theorem exists_norm_sub_algebraMap_le_of_forall_norm_sub_le
    {F L : Type*} [Field F] [NormedField L] [IsUltrametricDist L] [Algebra F L]
    [IsAlgClosed L] [Algebra.IsAlgebraic F L]
    {p : ℕ} (hp : p.Prime) (hp0 : (p : L) ≠ 0) (hp1 : ‖(p : L)‖ < 1)
    (hiso : ∀ σ : L ≃ₐ[F] L, Isometry σ) (α : L) {M : ℝ}
    (hα : ∀ σ : L ≃ₐ[F] L, ‖σ α - α‖ ≤ M) :
    ∃ a : F, ‖α - algebraMap F L a‖ ≤ ‖(p : L)‖⁻¹ ^ ((p : ℝ) / ((p : ℝ) - 1) ^ 2) * M := by
  have hM : 0 ≤ M := by simpa using hα 1
  have hq_ge : 1 ≤ ‖(p : L)‖⁻¹ := (one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hp0, hp1⟩).le
  obtain ⟨a, ha⟩ := axSen_induction hp hp0 hp1 hiso (minpoly F α).natDegree α M rfl hα
  exact ⟨a, ha.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hq_ge (axSenExponent_lt hp _).le) hM)⟩

/-- **The Ax–Sen–Tate theorem for closed subgroups.** Let `L / K` be an algebraic extension with `L`
an algebraically closed ultrametric normed field in which a prime `p` satisfies `(p : L) ≠ 0` and
`‖(p : L)‖ < 1`, and assume every `σ : L ≃ₐ[K] L` is an isometry. Then for every closed subgroup
`H` of `L ≃ₐ[K] L`, the `H`-fixed points of `UniformSpace.Completion L` are the closure of the
image of the algebraic fixed field `IntermediateField.fixedField H.toSubgroup`. -/
theorem forall_completion_map_eq_iff_mem_closure_fixedField
    {K L : Type*} [Field K] [NormedField L] [IsUltrametricDist L] [Algebra K L]
    [IsAlgClosed L] [Algebra.IsAlgebraic K L]
    {p : ℕ} (hp : p.Prime) (hp0 : (p : L) ≠ 0) (hp1 : ‖(p : L)‖ < 1)
    (hiso : ∀ σ : L ≃ₐ[K] L, Isometry σ)
    (H : ClosedSubgroup (L ≃ₐ[K] L)) (x : UniformSpace.Completion L) :
    (∀ σ ∈ H, UniformSpace.Completion.map σ x = x) ↔
      x ∈ closure (((↑) : L → UniformSpace.Completion L) ''
        (IntermediateField.fixedField H.toSubgroup : Set L)) := by
  set F := IntermediateField.fixedField H.toSubgroup
  constructor
  · intro hx
    have hcharL : CharZero L :=
      IsUltrametricDist.charZero_of_norm_prime_lt_one hp (norm_ne_zero_iff.mpr hp0) hp1
    have hcharK : CharZero K := (RingHom.charZero_iff (algebraMap K L).injective).mpr hcharL
    have hnorm : Normal K L := ⟨fun _ ↦ IsAlgClosed.splits _⟩
    have hgal : IsGalois K L := {}
    have hfix : F.fixingSubgroup = H.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField H
    have halg : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.tower_top (K := K) F
    rw [Metric.mem_closure_iff]
    intro ε hε
    set C : ℝ := ‖(p : L)‖⁻¹ ^ ((p : ℝ) / ((p : ℝ) - 1) ^ 2)
    have : 0 < C := Real.rpow_pos_of_pos (inv_pos.mpr (norm_pos_iff.mpr hp0)) _
    set δ : ℝ := ε / (2 * (1 + 2 * C))
    have hδ_pos : 0 < δ := by positivity
    obtain ⟨_, ⟨α, rfl⟩, hαx⟩ :=
      Metric.mem_closure_iff.mp (UniformSpace.Completion.denseRange_coe (α := L) x) δ hδ_pos
    have hconj : ∀ τ : L ≃ₐ[F] L, ‖τ α - α‖ ≤ 2 * δ := fun τ ↦ by
      have hτ_mem : τ.restrictScalars K ∈ H := by
        have hmem : τ.restrictScalars K ∈ H.toSubgroup :=
          hfix ▸ (IntermediateField.mem_fixingSubgroup_iff F _).mpr fun y hy ↦ τ.commutes ⟨y, hy⟩
        exact hmem
      exact (norm_sub_le_two_mul_dist_of_completion_map_eq
        (hiso (τ.restrictScalars K)) (hx _ hτ_mem) α).trans (by linarith)
    obtain ⟨y, hy⟩ := exists_norm_sub_algebraMap_le_of_forall_norm_sub_le hp hp0 hp1
      (fun τ : L ≃ₐ[F] L ↦ hiso (τ.restrictScalars K)) α hconj
    rw [IntermediateField.algebraMap_apply] at hy
    refine ⟨((y : L) : UniformSpace.Completion L), ⟨y, y.2, rfl⟩, ?_⟩
    calc dist x ((y : L) : UniformSpace.Completion L)
        ≤ dist x (α : UniformSpace.Completion L) +
          dist (α : UniformSpace.Completion L) ((y : L) : UniformSpace.Completion L) :=
          dist_triangle _ _ _
      _ = dist x (α : UniformSpace.Completion L) + ‖α - (y : L)‖ := by
          conv_lhs => arg 2; rw [UniformSpace.Completion.coe_isometry.dist_eq, dist_eq_norm]
      _ < δ + C * (2 * δ) := by linarith
      _ = ε / 2 := by
          dsimp only [δ]
          have hden : (1 : ℝ) + 2 * C ≠ 0 := by positivity
          field_simp
      _ < ε := half_lt_self hε
  · intro hx σ hσ
    have hclosed : IsClosed {z : UniformSpace.Completion L | UniformSpace.Completion.map σ z = z} :=
      isClosed_eq (hiso σ).completion_map.continuous continuous_id
    have hsub : (((↑) : L → UniformSpace.Completion L) '' (F : Set L)) ⊆
        {z : UniformSpace.Completion L | UniformSpace.Completion.map σ z = z} := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Set.mem_ofPred_eq, UniformSpace.Completion.map_coe (hiso σ).uniformContinuous,
        (IntermediateField.mem_fixedField_iff _ _).mp hy σ hσ]
    exact closure_minimal hsub hclosed hx

section CompleteUltrametric

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NormedField L] [NormedAlgebra K L] [IsAlgClosed L] [Algebra.IsAlgebraic K L]

/-- **The Ax–Sen–Tate theorem for finite extensions of a complete ultrametric field.** If `K` is
complete, nontrivially normed, and ultrametric with `(p : K) ≠ 0` and `‖(p : K)‖ < 1` for a prime
`p`, and `E` is a finite-dimensional intermediate field of an algebraic closure `L / K`, then the
`(L ≃ₐ[E] L)`-fixed points of `UniformSpace.Completion L` are precisely `E`. -/
theorem forall_completion_map_eq_iff_exists_of_finiteDimensional
    {p : ℕ} (hp : p.Prime) (hp0 : (p : K) ≠ 0) (hp1 : ‖(p : K)‖ < 1)
    (E : IntermediateField K L) [FiniteDimensional K E] (x : UniformSpace.Completion L) :
    (∀ σ : L ≃ₐ[E] L, UniformSpace.Completion.map σ x = x) ↔
      ∃ a : E, x = ((a : L) : UniformSpace.Completion L) := by
  have : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  have hp0L : (p : L) ≠ 0 := by
    rw [← map_natCast (algebraMap K L)]
    exact (_root_.map_ne_zero _).mpr hp0
  have hp1L : ‖(p : L)‖ < 1 := by
    rwa [← map_natCast (algebraMap K L), norm_algebraMap']
  have hcharL : CharZero L :=
    IsUltrametricDist.charZero_of_norm_prime_lt_one hp (norm_ne_zero_iff.mpr hp0L) hp1L
  have hcharK : CharZero K := (RingHom.charZero_iff (algebraMap K L).injective).mpr hcharL
  have hnorm : Normal K L := ⟨fun _ ↦ IsAlgClosed.splits _⟩
  have hgal : IsGalois K L := {}
  let H : ClosedSubgroup (L ≃ₐ[K] L) := ⟨E.fixingSubgroup, E.fixingSubgroup_isClosed⟩
  have hiff_H : (∀ σ : L ≃ₐ[E] L, UniformSpace.Completion.map σ x = x) ↔
      (∀ σ ∈ H, UniformSpace.Completion.map σ x = x) :=
    ⟨fun h σ hσ ↦ h (IntermediateField.fixingSubgroupEquiv E ⟨σ, hσ⟩),
      fun h σ ↦ h (σ.restrictScalars K) ((IntermediateField.mem_fixingSubgroup_iff E _).mpr
        fun y hy ↦ σ.commutes ⟨y, hy⟩)⟩
  rw [hiff_H, forall_completion_map_eq_iff_mem_closure_fixedField hp hp0L hp1L
    (fun σ ↦ σ.isometry) H x, InfiniteGalois.fixedField_fixingSubgroup E]
  have hrange : ((↑) : L → UniformSpace.Completion L) '' (E : Set L) =
      Set.range fun a : E ↦ ((a : L) : UniformSpace.Completion L) := by
    ext z
    simp
  have : CompleteSpace E := FiniteDimensional.completeSpace K E
  have hiso : Isometry fun a : E ↦ ((a : L) : UniformSpace.Completion L) :=
    UniformSpace.Completion.coe_isometry.comp isometry_subtype_coe
  rw [hrange, hiso.isClosedEmbedding.isClosed_range.closure_eq]
  simp only [Set.mem_range, eq_comm]

/-- **The Ax–Sen–Tate theorem over a complete ultrametric field.** If `K` is complete, nontrivially
normed, and ultrametric with `(p : K) ≠ 0` and `‖(p : K)‖ < 1` for a prime `p`, and `L / K` is an
algebraically closed algebraic normed field extension, then the `(L ≃ₐ[K] L)`-fixed points of
`UniformSpace.Completion L` are precisely the image of `K`. -/
theorem forall_completion_map_eq_iff_exists_algebraMap
    {p : ℕ} (hp : p.Prime) (hp0 : (p : K) ≠ 0) (hp1 : ‖(p : K)‖ < 1)
    (x : UniformSpace.Completion L) :
    (∀ σ : L ≃ₐ[K] L, UniformSpace.Completion.map σ x = x) ↔
      ∃ k : K, x = algebraMap K (UniformSpace.Completion L) k := by
  have : FiniteDimensional K (⊥ : IntermediateField K L) :=
    (IntermediateField.botEquiv K L).symm.toLinearEquiv.finiteDimensional
  have hiff_bot : (∀ σ : L ≃ₐ[K] L, UniformSpace.Completion.map σ x = x) ↔
      (∀ σ : L ≃ₐ[(⊥ : IntermediateField K L)] L, UniformSpace.Completion.map σ x = x) :=
    ⟨fun h σ ↦ h (σ.restrictScalars K),
      fun h σ ↦ h (IntermediateField.fixingSubgroupEquiv (⊥ : IntermediateField K L)
        ⟨σ, (IntermediateField.mem_fixingSubgroup_iff ⊥ _).mpr fun y hy ↦ by
          obtain ⟨k, rfl⟩ := IntermediateField.mem_bot.mp hy
          exact σ.commutes k⟩)⟩
  rw [hiff_bot, forall_completion_map_eq_iff_exists_of_finiteDimensional hp hp0 hp1 ⊥ x]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp a.2
    exact ⟨k, by rw [UniformSpace.Completion.algebraMap_def, hk]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨algebraMap K L k, IntermediateField.algebraMap_mem ⊥ k⟩,
      by rw [UniformSpace.Completion.algebraMap_def]⟩

end CompleteUltrametric

end TauCeti
