/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform
public import Mathlib.RingTheory.PowerSeries.Binomial
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Transform
public import TauCeti.NumberTheory.Padics.Distribution.Convolution

/-!
# Convolution and the Amice transform of locally analytic distributions

Additive convolution on `TauCeti.LocallyAnalyticDistribution p K`, constructed in
`TauCeti.NumberTheory.Padics.Distribution.Convolution` from the bounded two-variable stage pairing
and stage comultiplication `TauCeti.AnalyticStage.comul`, corresponds under the Amice transform to
formal power-series multiplication.

At the diagonal level `h = n`, where `⌊n / pⁿ⌋! = 1`, Amice's vector `amiceTerm p n n e` represents
the Mahler term `x ↦ (x choose n) • e`. Over `ℤ_p`, injectivity of stage evaluation together with
Vandermonde's identity `(x + y choose n) = ∑_{i + j = n} (x choose i) (y choose j)` yields

`comul ℤ_p (amiceTerm p n n 1) = ∑_{i + j = n} amiceTerm p n i (amiceTerm p n j 1)`.

Pushing forward along `ContinuousLinearMap.toSpanSingleton ℤ_p e` extends this identity to any
complete ultrametric normed `ℤ_p`-module `E` (`TauCeti.AnalyticStage.comul_amiceTerm_self`),
without any torsion-freeness assumption on `E`.

Descending to the direct limit `LA(ℤ_p, K)` computes right convolution on Mahler terms
(`convolveRight_mahlerTerm`), from which `amiceTransform (μ * ν) = amiceTransform μ *
amiceTransform ν` and `amiceTransform 1 = 1` follow directly on moments. Bundling gives the
injective `K`-algebra homomorphism `amiceTransformAlgHom`, compatible via
`ofMultiplicativeMeasure` with Mathlib's `AbstractMeasure.amiceTransformₐ`. When `K` is a normed
`ℚ_p`-algebra, `amiceTransformAlgEquiv` upgrades `amiceTransformEquiv` to a `K`-algebra isomorphism
with the open-unit-disc power series `PowerSeries.OnOpenDisc.subring K 1`.

## Main definitions

* `TauCeti.LocallyAnalyticDistribution.amiceTransformAlgHom`: the Amice transform as an injective
  `K`-algebra homomorphism `LocallyAnalyticDistribution p K →ₐ[K] PowerSeries K`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransformAlgEquiv`: for `[NormedAlgebra ℚ_[p] K]`,
  the `K`-algebra isomorphism between `LocallyAnalyticDistribution p K` and
  `PowerSeries.OnOpenDisc.subring K 1`.

## Main results

* `TauCeti.AnalyticStage.comul_amiceTerm_self`: Vandermonde comultiplication of `amiceTerm p n n e`
  for arbitrary coefficient modules `E`.
* `TauCeti.LocallyAnalyticDistribution.convolveRight_mahlerTerm`: right convolution of locally
  analytic Mahler terms.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_dirac`,
  `TauCeti.LocallyAnalyticDistribution.amiceTransform_one`,
  `TauCeti.LocallyAnalyticDistribution.amiceTransform_mul`: moments of Dirac distributions, `1`,
  and convolutions.
* `TauCeti.LocallyAnalyticDistribution.amiceTransformAlgHom_comp_ofMultiplicativeMeasure`:
  compatibility with `AbstractMeasure.amiceTransformₐ`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3,
  Theorem 3.43.
-/

public section

open Nat ZeroAtInftyContinuousMap
open scoped AbstractMeasure PowerSeries ZeroAtInfty

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Comultiplication of diagonal Amice vectors -/

namespace AnalyticStage

private theorem compLeft_amiceTerm {E F R : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E]
    [NormedAddCommGroup F] [Module ℤ_[p] F] [Semiring R] [Module R E] [ContinuousConstSMul R E]
    [Module R F] [ContinuousConstSMul R F] [LinearMap.CompatibleSMul E F ℤ_[p] R]
    (u : E →L[R] F) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖) (h n : ℕ) (e : E) :
    compLeft u hu (amiceTerm p h n e) = amiceTerm p h n (u e) := by
  ext i
  rw [compLeft_apply, amiceTerm_apply, amiceTerm_apply, u.map_smul_of_tower]

private theorem comul_amiceTerm_self_one (n : ℕ) :
    comul ℤ_[p] (amiceTerm p n n (1 : ℤ_[p])) =
      ∑ ij ∈ Finset.antidiagonal n,
        amiceTerm p n ij.1 (amiceTerm p n ij.2 (1 : ℤ_[p])) := by
  have hp0 : IsSMulRegular ℤ_[p] (p : ℤ_[p]) :=
    mul_right_injective₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hpStage : IsSMulRegular (AnalyticStage p n ℤ_[p]) (p : ℤ_[p]) :=
    fun f g hfg ↦ by ext i : 1; exact hp0 (DFunLike.congr_fun hfg i)
  apply eval_injective ℤ_[p] hpStage
  ext x : 1
  apply eval_injective ℤ_[p] hp0
  ext y : 1
  rw [eval_eval_comul, eval_amiceTerm, Nat.div_eq_of_lt (Nat.lt_pow_self hp.out.one_lt),
    factorial_zero, one_smul, PadicInt.mahlerTerm_apply, mahler_apply, smul_eq_mul, mul_one,
    Ring.add_choose_eq n (Commute.all x y), map_sum, ContinuousMap.coe_sum, Finset.sum_apply,
    map_sum, ContinuousMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  have hij' : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  have h1 : ij.1 / p ^ n = 0 :=
    Nat.div_eq_of_lt ((by omega : ij.1 ≤ n).trans_lt (Nat.lt_pow_self hp.out.one_lt))
  have h2 : ij.2 / p ^ n = 0 :=
    Nat.div_eq_of_lt ((by omega : ij.2 ≤ n).trans_lt (Nat.lt_pow_self hp.out.one_lt))
  rw [eval_amiceTerm, h1, factorial_zero, one_smul, PadicInt.mahlerTerm_apply, mahler_apply,
    ContinuousLinearMap.map_smul, ContinuousMap.smul_apply, eval_amiceTerm, h2, factorial_zero,
    one_smul, PadicInt.mahlerTerm_apply, mahler_apply, smul_eq_mul, smul_eq_mul, mul_one]

section Module

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E]

/-- **Vandermonde comultiplication of diagonal Amice vectors.** At level `n`, where
`⌊n / pⁿ⌋! = 1`, `amiceTerm p n n e` represents `(x choose n) • e`, and its stage comultiplication
splits along the antidiagonal without any torsion-freeness assumption on `E`. -/
theorem comul_amiceTerm_self (n : ℕ) (e : E) :
    comul S (amiceTerm p n n e) =
      ∑ ij ∈ Finset.antidiagonal n, amiceTerm p n ij.1 (amiceTerm p n ij.2 e) := by
  let u : ℤ_[p] →L[ℤ_[p]] E := ContinuousLinearMap.toSpanSingleton ℤ_[p] e
  have hu : ∃ C, ∀ r : ℤ_[p], ‖u r‖ ≤ C * ‖r‖ :=
    ⟨‖e‖, fun r ↦ by simpa [u, mul_comm] using norm_smul_le r e⟩
  have he : amiceTerm p n n e = compLeft u hu (amiceTerm p n n (1 : ℤ_[p])) := by
    rw [compLeft_amiceTerm]
    simp [u]
  rw [comul_eq_comul S ℤ_[p], he, comul_compLeft ℤ_[p] u hu, comul_amiceTerm_self_one, map_sum]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [compLeft_amiceTerm, compLeft_amiceTerm]
  simp [u]

end Module

end AnalyticStage

/-! ### Multiplicativity of the Amice transform -/

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

/-- Right convolution of the `n`-th locally analytic Mahler term `(x choose n)` by `ν` expands along
the Vandermonde antidiagonal weighted by the moments of `ν`. -/
theorem convolveRight_mahlerTerm (ν : LocallyAnalyticDistribution p K) (n : ℕ) :
    convolveRight ν (mahlerTerm p K 1 n) =
      ∑ ij ∈ Finset.antidiagonal n,
        (amiceTransform ν).coeff ij.2 • mahlerTerm p K 1 ij.1 := by
  have hstage : stageConvolveRight n ν (amiceTerm p n n (1 : K)) =
      ∑ ij ∈ Finset.antidiagonal n,
        amiceTerm p n ij.1 (stage n ν (amiceTerm p n ij.2 (1 : K))) := by
    calc stageConvolveRight n ν (amiceTerm p n n (1 : K))
        = compLeft (stage n ν) ⟨‖stage n ν‖, (stage n ν).le_opNorm⟩
            (comul K (amiceTerm p n n (1 : K))) := by
              ext x
              simp
      _ = ∑ ij ∈ Finset.antidiagonal n,
            amiceTerm p n ij.1 (stage n ν (amiceTerm p n ij.2 (1 : K))) := by
              rw [comul_amiceTerm_self K, map_sum]
              exact Finset.sum_congr rfl fun ij _ ↦ compLeft_amiceTerm _ _ _ _ _
  rw [mahlerTerm_def, convolveRight_ofStage, hstage, map_sum]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  have hij' : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  have h1 : ij.1 / p ^ n = 0 :=
    Nat.div_eq_of_lt ((by omega : ij.1 ≤ n).trans_lt (Nat.lt_pow_self hp.out.one_lt))
  have h2 : ij.2 / p ^ n = 0 :=
    Nat.div_eq_of_lt ((by omega : ij.2 ≤ n).trans_lt (Nat.lt_pow_self hp.out.one_lt))
  rw [stage_amiceTerm, h2, factorial_zero, Nat.cast_one, one_mul, one_mul, ofStage_amiceTerm,
    h1, factorial_zero, one_smul]
  simpa only [smul_eq_mul, mul_one] using
    mahlerTerm_smul K ((amiceTransform ν).coeff ij.2) (1 : K) ij.1

/-- The Amice transform of the Dirac distribution at `x ∈ ℤ_p` is the binomial series
`(1 + X) ^ x`. -/
@[simp]
theorem amiceTransform_dirac (x : ℤ_[p]) :
    amiceTransform (dirac (p := p) (K := K) x) = PowerSeries.binomialSeries K x := by
  ext n
  rw [coeff_amiceTransform, coe_dirac_apply, eval_mahlerTerm, PowerSeries.binomialSeries_coeff,
    PadicInt.mahlerTerm_apply, mahler_apply]

/-- The Amice transform of `1 = dirac 0` is `1`. -/
@[simp]
theorem amiceTransform_one :
    amiceTransform (1 : LocallyAnalyticDistribution p K) = 1 := by
  rw [← dirac_zero, amiceTransform_dirac, PowerSeries.binomialSeries_zero]

/-- **The Amice transform carries additive convolution to formal power-series multiplication.** -/
@[simp]
theorem amiceTransform_mul (μ ν : LocallyAnalyticDistribution p K) :
    amiceTransform (μ * ν) = amiceTransform μ * amiceTransform ν := by
  ext n
  rw [coeff_amiceTransform, coe_mul_apply, convolveRight_mahlerTerm, map_sum,
    PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [LinearMap.map_smul, coeff_amiceTransform, coeff_amiceTransform, smul_eq_mul, mul_comm]

/-- The Amice transform preserves natural powers. -/
@[simp]
theorem amiceTransform_pow (μ : LocallyAnalyticDistribution p K) (n : ℕ) :
    amiceTransform (μ ^ n) = amiceTransform μ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, amiceTransform_mul, ih]

/-- **The Amice transform as an injective `K`-algebra homomorphism.** -/
noncomputable def amiceTransformAlgHom : LocallyAnalyticDistribution p K →ₐ[K] PowerSeries K :=
  AlgHom.ofLinearMap amiceTransform amiceTransform_one amiceTransform_mul

/-- `amiceTransformAlgHom` has underlying map `amiceTransform`. -/
@[simp]
theorem amiceTransformAlgHom_apply (μ : LocallyAnalyticDistribution p K) :
    amiceTransformAlgHom μ = amiceTransform μ :=
  (rfl)

/-- `amiceTransformAlgHom` is injective. -/
theorem amiceTransformAlgHom_injective :
    Function.Injective (amiceTransformAlgHom (p := p) (K := K)) :=
  amiceTransform_injective

/-- Precomposing `amiceTransformAlgHom` with `ofMultiplicativeMeasure` recovers Mathlib's
measure-algebra Amice transform `AbstractMeasure.amiceTransformₐ`. -/
@[simp]
theorem amiceTransformAlgHom_comp_ofMultiplicativeMeasure :
    (amiceTransformAlgHom (p := p) (K := K)).comp ofMultiplicativeMeasure =
      AbstractMeasure.amiceTransformₐ := by
  apply AlgHom.ext fun μ ↦ PowerSeries.ext fun n ↦ ?_
  rw [AlgHom.comp_apply, amiceTransformAlgHom_apply, ofMultiplicativeMeasure_eq_ofMeasure,
    amiceTransform_ofMeasure, AbstractMeasure.coeff_amiceTransform,
    AbstractMeasure.coeff_amiceTransformₐ, AbstractMeasure.arrowCongrLeft_apply]
  congr 1

/-! ### The Amice `K`-algebra isomorphism on the open unit disc -/

section NormedAlgebra

variable [NormedAlgebra ℚ_[p] K]

/-- The inverse Amice transform sends `1` to `1`. -/
@[simp]
theorem ofOnOpenDisc_one (h1 : (1 : PowerSeries K).OnOpenDisc 1) :
    ofOnOpenDisc p h1 = 1 :=
  amiceTransform_injective <| by rw [amiceTransform_ofOnOpenDisc, amiceTransform_one]

/-- The inverse Amice transform converts multiplication of open-disc power series into additive
convolution of distributions. -/
theorem ofOnOpenDisc_mul {F G : PowerSeries K}
    (hFG : (F * G).OnOpenDisc 1) (hF : F.OnOpenDisc 1) (hG : G.OnOpenDisc 1) :
    ofOnOpenDisc p hFG = ofOnOpenDisc p hF * ofOnOpenDisc p hG :=
  amiceTransform_injective <| by
    rw [amiceTransform_ofOnOpenDisc, amiceTransform_mul, amiceTransform_ofOnOpenDisc,
      amiceTransform_ofOnOpenDisc]

/-- The inverse Amice transform commutes with `K`-scalar multiplication. -/
theorem ofOnOpenDisc_smul (a : K) {F : PowerSeries K}
    (haF : (a • F).OnOpenDisc 1) (hF : F.OnOpenDisc 1) :
    ofOnOpenDisc p haF = a • ofOnOpenDisc p hF :=
  amiceTransform_injective <| by
    rw [amiceTransform_ofOnOpenDisc, map_smul, amiceTransform_ofOnOpenDisc]

/-- **Amice's theorem as a `K`-algebra isomorphism.** Over a complete normed `ℚ_p`-algebra `K`,
the Amice transform identifies the convolution algebra `LocallyAnalyticDistribution p K` of locally
analytic distributions on `ℤ_p` with the `K`-algebra `PowerSeries.OnOpenDisc.subring K 1` of power
series converging on the open unit disc. -/
noncomputable def amiceTransformAlgEquiv :
    LocallyAnalyticDistribution p K ≃ₐ[K] PowerSeries.OnOpenDisc.subring K 1 :=
  AlgEquiv.ofLinearEquiv
    { toFun := amiceTransformEquiv
      invFun := amiceTransformEquiv.symm
      left_inv := amiceTransformEquiv.left_inv
      right_inv := amiceTransformEquiv.right_inv
      map_add' := map_add amiceTransformEquiv
      map_smul' := fun a μ ↦ Subtype.ext <| by
        simpa only [RingHom.id_apply, TauCeti.PowerSeries.coe_smul_onOpenDiscSubring,
          coe_amiceTransformEquiv] using map_smul amiceTransform a μ }
    (Subtype.ext <| by
      change (amiceTransformEquiv (1 : LocallyAnalyticDistribution p K) : PowerSeries K) = 1
      rw [coe_amiceTransformEquiv, amiceTransform_one])
    (fun μ ν ↦ Subtype.ext <| by
      change (amiceTransformEquiv (μ * ν) : PowerSeries K) =
        (amiceTransformEquiv μ : PowerSeries K) * (amiceTransformEquiv ν : PowerSeries K)
      rw [coe_amiceTransformEquiv, coe_amiceTransformEquiv, coe_amiceTransformEquiv,
        amiceTransform_mul])

/-- `amiceTransformAlgEquiv` has `amiceTransform` as its underlying formal power series. -/
@[simp]
theorem coe_amiceTransformAlgEquiv (μ : LocallyAnalyticDistribution p K) :
    (amiceTransformAlgEquiv μ : PowerSeries K) = amiceTransform μ :=
  coe_amiceTransformEquiv μ

/-- The inverse of `amiceTransformAlgEquiv` constructs the distribution via `ofOnOpenDisc`. -/
@[simp]
theorem amiceTransformAlgEquiv_symm_apply (F : PowerSeries.OnOpenDisc.subring K 1) :
    amiceTransformAlgEquiv.symm F =
      ofOnOpenDisc p (PowerSeries.OnOpenDisc.mem_subring.mp F.2) :=
  amiceTransformEquiv_symm_apply F

/-- `amiceTransformAlgEquiv` upgrades `amiceTransformEquiv` without changing the underlying
additive equivalence. -/
theorem toAddEquiv_amiceTransformAlgEquiv :
    (amiceTransformAlgEquiv (p := p) (K := K)).toAddEquiv = amiceTransformEquiv := by
  ext μ
  rfl

end NormedAlgebra

end LocallyAnalyticDistribution

end TauCeti
