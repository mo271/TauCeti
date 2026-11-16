/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm
public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Irreducible

import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Spectral-norm contractivity of algebra homomorphisms out of Banach algebras

Let `K` be a complete nontrivially normed ultrametric field, let `B` be a complete normed
`K`-algebra (not necessarily commutative, unital-normalised, noetherian, or ultrametric), and let
`L` be any field extension of `K`. Every `K`-algebra homomorphism `φ : B → L` is contractive for
`spectralNorm K L` — with no continuity assumption on `φ` and no algebraicity assumption on `L`:

* `AlgHomClass.spectralNorm_apply_le_norm`: `spectralNorm K L (φ b) ≤ ‖b‖`.
* `AlgHomClass.spectralNorm_apply_le_norm_pow_rpow`:
  `spectralNorm K L (φ b) ≤ ‖b ^ n‖ ^ (1 / n)` for `n ≠ 0`.
* `AlgHomClass.spectralNorm_apply_le_smoothingFun`: for commutative `B`,
  `spectralNorm K L (φ b) ≤ smoothingFun (normRingSeminorm B) b`.

When `φ b` is transcendental over `K`, its spectral norm is `0`. Otherwise `K⟮φ b⟯ / K` is finite
of degree `r`, and for every `N ≥ 1` the minimal polynomial `P_N` of `(φ b) ^ N` over `K` has
degree `d_N ≤ r`, nonzero constant term of norm `|φ b| ^ (N d_N)`, and coefficients bounded by
`|φ b| ^ (N (d_N - i))`. If `‖b‖ < |φ b|`, rescaling `P_N(b ^ N)` by `P_N(0)⁻¹` produces `1 - u_N`
with `‖u_N‖ ≤ r (‖b‖ / |φ b|) ^ N < 1` for large `N`, a geometric-series unit of `B` sent to `0` by
`φ`.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §3.8.2 and §6.2.4.
-/

public section

open Filter Polynomial
open scoped IntermediateField Topology

namespace AlgHomClass

/-- Normalized evaluation of a polynomial `p` with nonzero constant term:
`p(0)⁻¹ • p(x) = 1 + ∑_{1 ≤ i ≤ d} (p(0)⁻¹ * pᵢ) • x ^ i`. -/
private theorem inv_coeff_zero_smul_aeval_eq_one_add {K B : Type*} [Field K] [Ring B]
    [Algebra K B] {p : K[X]} (hp0 : p.coeff 0 ≠ 0) (x : B) :
    (p.coeff 0)⁻¹ • aeval x p =
      1 + ∑ i ∈ Finset.Icc 1 p.natDegree, ((p.coeff 0)⁻¹ * p.coeff i) • x ^ i := by
  have heval : aeval x p =
      ∑ i ∈ Finset.range (p.natDegree + 1), aeval x (C (p.coeff i) * X ^ i) := by
    conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
    exact map_sum (aeval x) _ _
  rw [heval, Finset.sum_range_eq_add_Ico _ (Nat.succ_pos _), smul_add]
  have h0 : (p.coeff 0)⁻¹ • aeval x (C (p.coeff 0) * X ^ 0) = 1 := by
    simp [aeval_C, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hp0]
  have hIco : Finset.Ico 1 (p.natDegree + 1) = Finset.Icc 1 p.natDegree := rfl
  rw [h0, hIco, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, aeval_C, map_pow, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    smul_smul]

/-- Sum bound on the higher terms of a monic polynomial `p` whose constant term has norm
`s ^ (N * d)` and whose coefficients satisfy `‖pᵢ‖ ≤ s ^ (N * (d - i))`. -/
private theorem norm_sum_inv_coeff_zero_smul_pow_le {K B : Type*} [NormedField K]
    [NormedRing B] [NormedAlgebra K B] {p : K[X]} (hmon : p.Monic) {s : ℝ} (hs : 0 < s)
    {N : ℕ} (hN : 0 < N) (hspecp : spectralValue p = s ^ N)
    (hp0_norm : ‖p.coeff 0‖ = s ^ (N * p.natDegree)) {b : B} (hb : ‖b‖ < s) :
    ‖∑ i ∈ Finset.Icc 1 p.natDegree, ((p.coeff 0)⁻¹ * p.coeff i) • (b ^ N) ^ i‖ ≤
      (p.natDegree : ℝ) * (‖b‖ / s) ^ N := by
  have hratio_nn : 0 ≤ ‖b‖ / s := div_nonneg (norm_nonneg b) hs.le
  have hratio_lt : ‖b‖ / s < 1 := (div_lt_one hs).mpr hb
  calc ‖∑ i ∈ Finset.Icc 1 p.natDegree, ((p.coeff 0)⁻¹ * p.coeff i) • (b ^ N) ^ i‖
      ≤ ∑ i ∈ Finset.Icc 1 p.natDegree, ‖((p.coeff 0)⁻¹ * p.coeff i) • (b ^ N) ^ i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.Icc 1 p.natDegree, (‖b‖ / s) ^ N := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        obtain ⟨hi1, hid⟩ := Finset.mem_Icc.mp hi
        rw [norm_smul, norm_mul, norm_inv, hp0_norm, ← pow_mul]
        have hci : ‖p.coeff i‖ ≤ s ^ (N * (p.natDegree - i)) := by
          simpa only [hspecp, ← pow_mul] using hmon.norm_coeff_le_spectralValue_pow i
        have hbi : ‖b ^ (N * i)‖ ≤ ‖b‖ ^ (N * i) :=
          norm_pow_le' b (Nat.mul_pos hN (Nat.pos_of_ne_zero (by omega)))
        calc (s ^ (N * p.natDegree))⁻¹ * ‖p.coeff i‖ * ‖b ^ (N * i)‖
            ≤ (s ^ (N * p.natDegree))⁻¹ * s ^ (N * (p.natDegree - i)) * ‖b‖ ^ (N * i) := by
              gcongr
          _ = (‖b‖ / s) ^ (N * i) := by
              have hadd : N * (p.natDegree - i) + N * i = N * p.natDegree := by
                rw [← Nat.mul_add, Nat.sub_add_cancel hid]
              rw [div_pow, ← hadd, pow_add]
              field_simp [hs.ne']
          _ ≤ (‖b‖ / s) ^ N :=
              pow_le_pow_of_le_one hratio_nn hratio_lt.le (Nat.le_mul_of_pos_right N hi1)
    _ = (p.natDegree : ℝ) * (‖b‖ / s) ^ N := by simp [Nat.card_Icc]

section NormedRing

variable {K B L F : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedRing B] [NormedAlgebra K B] [CompleteSpace B]
  [Field L] [Algebra K L] [FunLike F B L] [AlgHomClass F K B L]

/-- For an algebraic element `α` of a finite field extension `E / K` and `b : B` with
`‖b‖ < spectralNorm K E α`, evaluating `minpoly K (α ^ N)` at `b ^ N` gives a unit of `B` for a
sufficiently large positive exponent `N`. -/
private theorem exists_isUnit_aeval_pow_of_norm_lt {E : Type*} [Field E] [Algebra K E]
    [FiniteDimensional K E] {α : E} {b : B} (hb : ‖b‖ < spectralNorm K E α) :
    ∃ N : ℕ, 0 < N ∧ IsUnit (aeval (b ^ N) (minpoly K (α ^ N))) := by
  set s := spectralNorm K E α
  have hs : 0 < s := (norm_nonneg b).trans_lt hb
  have hlim : Tendsto (fun N : ℕ ↦ (Module.finrank K E : ℝ) * (‖b‖ / s) ^ N) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg (norm_nonneg b) hs.le)
        ((div_lt_one hs).mpr hb))
  obtain ⟨N₀, hN₀⟩ := (hlim.eventually (gt_mem_nhds one_pos)).exists_forall_of_atTop
  set N := max N₀ 1
  have hN : 0 < N := lt_of_lt_of_le one_pos (le_max_right _ _)
  let p := minpoly K (α ^ N)
  have hint : IsIntegral K (α ^ N) := Algebra.IsIntegral.isIntegral _
  have hmon : p.Monic := minpoly.monic hint
  have hd_pos : 0 < p.natDegree := minpoly.natDegree_pos hint
  have hspecp : spectralValue p = s ^ N := isPowMul_spectralNorm α hN
  have hp0_norm : ‖p.coeff 0‖ = s ^ (N * p.natDegree) := by
    have h1 := Polynomial.spectralValue_eq_norm_coeff_zero_rpow_of_irreducible hmon
      (minpoly.irreducible hint)
    rw [hspecp] at h1
    have hdR : (p.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
    have hpow := congrArg (fun x : ℝ ↦ x ^ p.natDegree) h1
    rw [← pow_mul, ← Real.rpow_natCast (‖p.coeff 0‖ ^ _),
      ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hdR, Real.rpow_one] at hpow
    exact hpow.symm
  have hp0_ne : p.coeff 0 ≠ 0 := norm_ne_zero_iff.mp (hp0_norm.trans_gt (pow_pos hs _)).ne'
  let u : B := -∑ i ∈ Finset.Icc 1 p.natDegree, ((p.coeff 0)⁻¹ * p.coeff i) • (b ^ N) ^ i
  have hu_norm : ‖u‖ < 1 := by
    rw [norm_neg]
    have hd_le : p.natDegree ≤ Module.finrank K E := minpoly.natDegree_le (α ^ N)
    have h1 := norm_sum_inv_coeff_zero_smul_pow_le hmon hs hN hspecp hp0_norm hb
    have h2 : (p.natDegree : ℝ) * (‖b‖ / s) ^ N ≤ (Module.finrank K E : ℝ) * (‖b‖ / s) ^ N := by
      have : 0 ≤ (‖b‖ / s) ^ N := pow_nonneg (div_nonneg (norm_nonneg b) hs.le) N
      gcongr
    exact (h1.trans h2).trans_lt (hN₀ N (le_max_left _ _))
  refine ⟨N, hN, ?_⟩
  have hu_unit : IsUnit ((p.coeff 0)⁻¹ • aeval (b ^ N) p) := by
    rw [inv_coeff_zero_smul_aeval_eq_one_add hp0_ne, ← sub_neg_eq_add]
    exact (Units.oneSub u hu_norm).isUnit
  have heq : aeval (b ^ N) p = p.coeff 0 • ((p.coeff 0)⁻¹ • aeval (b ^ N) p) := by
    rw [smul_smul, mul_inv_cancel₀ hp0_ne, one_smul]
  rw [heq, Algebra.smul_def]
  exact ((IsUnit.mk0 (p.coeff 0) hp0_ne).map (algebraMap K B)).mul hu_unit

/-- **Spectral-norm contractivity out of a Banach algebra.** Let `B` be a complete normed
`K`-algebra over a complete nontrivially normed ultrametric field `K`, and let `φ : B → L` be any
`K`-algebra homomorphism into a field extension `L / K`. Then `spectralNorm K L (φ b) ≤ ‖b‖` for
every `b : B`, with no continuity assumption on `φ`. -/
theorem spectralNorm_apply_le_norm (φ : F) (b : B) :
    spectralNorm K L (φ b) ≤ ‖b‖ := by
  by_cases halg : IsAlgebraic K (φ b)
  · have hint : IsIntegral K (φ b) := halg.isIntegral
    let E : IntermediateField K L := K⟮φ b⟯
    have : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hint
    let α : E := IntermediateField.AdjoinSimple.gen K (φ b)
    have hα : E.val α = φ b := rfl
    have hspec : spectralNorm K L (φ b) = spectralNorm K E α := by
      rw [← hα, E.val.spectralNorm_map]
    rw [hspec]
    by_contra! hlt
    obtain ⟨N, _, hunit⟩ := exists_isUnit_aeval_pow_of_norm_lt hlt
    let ψ : B →ₐ[K] L := AlgHom.ofClass φ
    have hmap : IsUnit (ψ (aeval (b ^ N) (minpoly K (α ^ N)))) :=
      hunit.map ψ.toRingHom
    have hzero : ψ (aeval (b ^ N) (minpoly K (α ^ N))) = 0 := by
      have hψ : ψ (b ^ N) = E.val (α ^ N) := by
        rw [map_pow, map_pow]
        exact congrArg (· ^ N) hα.symm
      rw [← aeval_algHom_apply ψ, hψ, aeval_algHom_apply E.val, minpoly.aeval, map_zero]
    exact hmap.ne_zero hzero
  · rw [TauCeti.spectralNorm_eq_zero_of_not_isAlgebraic halg]
    exact norm_nonneg b

/-- Every `K`-algebra homomorphism `φ : B → L` out of a complete normed `K`-algebra satisfies
`spectralNorm K L (φ b) ≤ ‖b ^ n‖ ^ (1 / n)` for `n ≠ 0`. -/
theorem spectralNorm_apply_le_norm_pow_rpow (φ : F) (b : B) {n : ℕ} (hn : n ≠ 0) :
    spectralNorm K L (φ b) ≤ ‖b ^ n‖ ^ (1 / n : ℝ) := by
  by_cases halg : IsAlgebraic K (φ b)
  · have hint : IsIntegral K (φ b) := halg.isIntegral
    let E : IntermediateField K L := K⟮φ b⟯
    have : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hint
    let α : E := IntermediateField.AdjoinSimple.gen K (φ b)
    have hα : E.val α = φ b := rfl
    have hpow : spectralNorm K L (φ b) ^ n = spectralNorm K L (φ (b ^ n)) := by
      have hαn : E.val (α ^ n) = φ (b ^ n) := by rw [map_pow, map_pow, hα]
      rw [← hα, E.val.spectralNorm_map, ← hαn, E.val.spectralNorm_map,
        isPowMul_spectralNorm α (Nat.pos_of_ne_zero hn)]
    rw [← Real.pow_rpow_inv_natCast (spectralNorm_nonneg (φ b)) hn, hpow, one_div]
    exact Real.rpow_le_rpow (spectralNorm_nonneg _)
      (spectralNorm_apply_le_norm φ (b ^ n)) (by positivity)
  · rw [TauCeti.spectralNorm_eq_zero_of_not_isAlgebraic halg]
    positivity

end NormedRing

section NormedCommRing

variable {K B L F : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
  [Field L] [Algebra K L] [FunLike F B L] [AlgHomClass F K B L]

/-- Every `K`-algebra homomorphism `φ : B → L` out of a complete commutative normed `K`-algebra is
bounded by the smoothing of the norm on `B`:
`spectralNorm K L (φ b) ≤ smoothingFun (normRingSeminorm B) b`. -/
theorem spectralNorm_apply_le_smoothingFun (φ : F) (b : B) :
    spectralNorm K L (φ b) ≤ smoothingFun (normRingSeminorm B) b :=
  le_ciInf fun n : PNat ↦ spectralNorm_apply_le_norm_pow_rpow φ b n.ne_zero

end NormedCommRing

end AlgHomClass

namespace AlgHom

section NormedRing

variable {K B L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedRing B] [NormedAlgebra K B] [CompleteSpace B]
  [Field L] [Algebra K L]

/-- A `K`-algebra homomorphism from a complete normed `K`-algebra into a field extension of `K` is
contractive for `spectralNorm K L`, with no continuity assumption on the homomorphism. -/
theorem spectralNorm_apply_le_norm (φ : B →ₐ[K] L) (b : B) :
    spectralNorm K L (φ b) ≤ ‖b‖ :=
  AlgHomClass.spectralNorm_apply_le_norm φ b

/-- A `K`-algebra homomorphism from a complete normed `K`-algebra into a field extension of `K`
satisfies `spectralNorm K L (φ b) ≤ ‖b ^ n‖ ^ (1 / n)` for `n ≠ 0`. -/
theorem spectralNorm_apply_le_norm_pow_rpow (φ : B →ₐ[K] L) (b : B) {n : ℕ} (hn : n ≠ 0) :
    spectralNorm K L (φ b) ≤ ‖b ^ n‖ ^ (1 / n : ℝ) :=
  AlgHomClass.spectralNorm_apply_le_norm_pow_rpow φ b hn

end NormedRing

section NormedCommRing

variable {K B L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
  [Field L] [Algebra K L]

/-- A `K`-algebra homomorphism from a complete commutative normed `K`-algebra into a field
extension of `K` is bounded by `smoothingFun (normRingSeminorm B)`. -/
theorem spectralNorm_apply_le_smoothingFun (φ : B →ₐ[K] L) (b : B) :
    spectralNorm K L (φ b) ≤ smoothingFun (normRingSeminorm B) b :=
  AlgHomClass.spectralNorm_apply_le_smoothingFun φ b

end NormedCommRing

end AlgHom
