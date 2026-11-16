/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
public import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm
public import Mathlib.RingTheory.Finiteness.Bilinear
public import Mathlib.RingTheory.Localization.BaseChange
public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.ReducedAlgebra
public import TauCeti.FieldTheory.Minpoly.TorsionFree
public import TauCeti.RingTheory.Localization.Reduced

import Mathlib.RingTheory.Localization.Integer
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Maps.Strict.Basic
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.StrictMorphism

/-!
# Banach function algebras over weakly stable fraction fields

Let `B` be a Noetherian ultrametric Banach algebra over a nontrivially normed ultrametric field `K`
(neither `K` nor `F` is assumed complete), and let `F` be a normed fraction field of `B` extending
the norm of `B` isometrically (`∀ b : B, ‖algebraMap B F b‖ = ‖b‖`) and satisfying weak stability
(`TauCeti.IsWeaklyStable F`). Let `A` be a reduced ultrametric Banach `K`-algebra equipped with a
continuous `K`-algebra map `B → A` making `A` a finite torsion-free `B`-module.

Then `F ⊗[B] A` is a module-finite reduced `F`-algebra, the canonical map `A → F ⊗[B] A` is
injective, and the norm `‖·‖` on `A` is equivalent to the generic spectral norm
`a ↦ spectralValue (minpoly F (1 ⊗ₜ[B] a))` on `F ⊗[B] A`. Consequently:

* the smoothing seminorm `smoothingFun (normRingSeminorm A) a = inf_{n ≥ 1} ‖a ^ n‖ ^ (1 / n)`
  coincides with `spectralValue (minpoly F (1 ⊗ₜ[B] a))` (and, when `B` is integrally closed, with
  `spectralValue (minpoly B a)`);
* there is a constant `C > 0` such that `smoothingFun (normRingSeminorm A) a ≤ ‖a‖` and
  `‖a‖ ≤ C * smoothingFun (normRingSeminorm A) a` for every `a : A`; in the terminology of
  [bosch-guntzer-remmert], §3.8.3, `A` is a **Banach function algebra**.

No normalisation `‖(1 : A)‖ ≤ 1` is required on `A`, and `K` need not be complete. Continuity of
`algebraMap B A` and compatibility with a shared nontrivially normed base field `K` are both
necessary: without continuity of `algebraMap B A` a discontinuous field automorphism of `ℂ_p`
produces inequivalent complete norms with distinct smoothings, and without a shared normed scalar
action `(ℚ_p, |·|_p ^ (1 / 2))` over `(ℚ_p, |·|_p)` violates linear boundedness near `0`.

## Main results

* `LinearMap.exists_norm_le_mul_apply_of_injective`: an injective `B`-linear map from a finite
  complete normed `B`-module to a Noetherian complete normed `B`-module admits a positive inverse
  norm bound.
* `TauCeti.isReduced_tensorProduct_of_isLocalization`: `F ⊗[B] A` is reduced whenever `F` is a
  localization of `B` and `A` is reduced.
* `TauCeti.exists_norm_comparison_spectralValue_minpoly_tensorProduct`: `‖a‖` and
  `spectralValue (minpoly F (1 ⊗ₜ[B] a))` bound one another up to positive constants.
* `TauCeti.smoothingFun_eq_spectralValue_minpoly_tensorProduct`: the smoothing of `‖·‖` on `A`
  equals `spectralValue (minpoly F (1 ⊗ₜ[B] a))`.
* `TauCeti.smoothingFun_eq_spectralValue_minpoly_base`: when `B` is integrally closed, the
  smoothing of `‖·‖` on `A` equals `spectralValue (minpoly B a)`.
* `TauCeti.exists_norm_le_mul_smoothingFun`: **Banach function algebra theorem**
  ([bosch-guntzer-remmert], §3.8.3, Theorem 7) — `smoothingFun (normRingSeminorm A) a ≤ ‖a‖` and
  `‖a‖ ≤ C * smoothingFun (normRingSeminorm A) a`.
* `TauCeti.tendsto_pow_norm_pow_one_div_smoothingFun`: `‖a ^ n‖ ^ (1 / n)` converges to
  `smoothingFun (normRingSeminorm A) a` even without `‖(1 : A)‖ ≤ 1`.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §3.8.1, Theorem 7 and §3.8.3, Theorem 7.
-/

public section

open Filter Polynomial Topology
open scoped TensorProduct nonZeroDivisors

namespace TauCeti

section Algebraic

/-- Base change of a reduced commutative `B`-algebra `A` along any localization `F` of `B` is
reduced. -/
theorem isReduced_tensorProduct_of_isLocalization {B F A : Type*} [CommRing B] [CommRing F]
    [Algebra B F] (M : Submonoid B) [IsLocalization M F] [CommRing A] [Algebra B A]
    [IsReduced A] : IsReduced (F ⊗[B] A) := by
  let : Algebra A (F ⊗[B] A) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid A M) (F ⊗[B] A) :=
    IsLocalization.tensorRight F M
  exact IsLocalization.isReduced (Algebra.algebraMapSubmonoid A M) (F ⊗[B] A)

/-- Right base change `A ⊗[B] F` of a reduced commutative `B`-algebra `A` along any localization
`F` of `B` is reduced. -/
theorem isReduced_tensorProduct_right_of_isLocalization {B F A : Type*} [CommRing B] [CommRing F]
    [Algebra B F] (M : Submonoid B) [IsLocalization M F] [CommRing A] [Algebra B A]
    [IsReduced A] : IsReduced (A ⊗[B] F) :=
  IsLocalization.isReduced (Algebra.algebraMapSubmonoid A M) (A ⊗[B] F)

/-- If `A` is a torsion-free commutative `B`-algebra and `F` is a localization of `B` at `B⁰`,
then `a ↦ 1 ⊗ₜ[B] a : A →ₐ[B] F ⊗[B] A` is injective. -/
theorem injective_includeRight_of_isTorsionFree {B F A : Type*} [CommRing B] [CommRing F]
    [Algebra B F] [IsLocalization B⁰ F] [CommRing A] [Algebra B A] [Module.IsTorsionFree B A] :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[B] F ⊗[B] A) :=
  (IsLocalizedModule.injective_iff_isRegular B⁰ (TensorProduct.mk B F A 1)).mpr fun c ↦
    (isRegular_iff_mem_nonZeroDivisors.mpr c.2).isSMulRegular

private theorem basis_repr_sum_smul {F L : Type*} [Field F] [AddCommGroup L] [Module F L]
    {m : ℕ} (b : Module.Basis (Fin m) F L) (v : Fin m → F) (i : Fin m) :
    b.repr (∑ j, v j • b j) i = v i := by
  rw [← b.equivFun_apply, map_sum, Finset.sum_apply]
  simp [b.equivFun_apply, b.repr_self, Finsupp.single_apply]

/-- In `F ⊗[B] A` for a fraction field `F` of `B` and a finite `B`-algebra `A`, any `F`-basis can
be rescaled by a nonzero element of `B` so that all basis vectors come from `A`. -/
private theorem exists_basis_in_range_includeRight {B F A : Type*} [CommRing B] [Field F]
    [Algebra B F] [IsFractionRing B F] [CommRing A] [Algebra B A] [Module.Finite B A]
    [Nontrivial (F ⊗[B] A)] :
    ∃ (m : ℕ) (_ : NeZero m) (b : Module.Basis (Fin m) F (F ⊗[B] A)) (e : Fin m → A),
      ∀ i, b i = (1 : F) ⊗ₜ[B] e i := by
  have : Nontrivial B := (algebraMap B F).domain_nontrivial
  let L := F ⊗[B] A
  let m := Module.finrank F L
  have hm : NeZero m := ⟨Module.finrank_pos.ne'⟩
  let b₀ : Module.Basis (Fin m) F L := Module.finBasis F L
  let : Algebra A L := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid A B⁰) L := IsLocalization.tensorRight F B⁰
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Algebra.algebraMapSubmonoid A B⁰) b₀
  obtain ⟨d, hd, hsd⟩ := s.2
  choose e he using hs
  have hd_ne : algebraMap B F d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  let u : Fˣ := Units.mk0 (algebraMap B F d) hd_ne
  refine ⟨m, hm, b₀.unitsSMul (fun _ ↦ u), e, fun i ↦ ?_⟩
  rw [Module.Basis.unitsSMul_apply, Units.smul_def]
  have hsmul : (u : F) • b₀ i = (s : A) • b₀ i := by
    rw [Algebra.smul_def, Algebra.smul_def, ← hsd]
    congr 1
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul d
  rw [hsmul, ← he i]
  rfl

private def basisSumLinearMap {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    {m : ℕ} (e : Fin m → A) : (Fin m → B) →ₗ[B] A where
  toFun v := ∑ i, v i • e i
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r v := by simp [Finset.smul_sum, mul_smul]

private theorem includeRight_basisSumLinearMap {B F A : Type*} [CommRing B] [Field F]
    [Algebra B F] [CommRing A] [Algebra B A] {m : ℕ}
    (b : Module.Basis (Fin m) F (F ⊗[B] A)) (e : Fin m → A)
    (he : ∀ i, b i = (1 : F) ⊗ₜ[B] e i) (v : Fin m → B) :
    (Algebra.TensorProduct.includeRight : A →ₐ[B] F ⊗[B] A) (basisSumLinearMap e v) =
      ∑ i, algebraMap B F (v i) • b i := by
  change (Algebra.TensorProduct.includeRight : A →ₐ[B] F ⊗[B] A) (∑ i, v i • e i) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, IsScalarTower.algebraMap_smul F, Algebra.TensorProduct.includeRight_apply, he i]

private theorem injective_basisSumLinearMap {B F A : Type*} [CommRing B] [Field F]
    [Algebra B F] [IsFractionRing B F] [CommRing A] [Algebra B A] {m : ℕ}
    (b : Module.Basis (Fin m) F (F ⊗[B] A)) (e : Fin m → A)
    (he : ∀ i, b i = (1 : F) ⊗ₜ[B] e i) :
    Function.Injective (basisSumLinearMap (B := B) e) := by
  intro u v huv
  have hL : ∑ i, algebraMap B F (u i) • b i = ∑ i, algebraMap B F (v i) • b i := by
    rw [← includeRight_basisSumLinearMap b e he u, ← includeRight_basisSumLinearMap b e he v, huv]
  ext i
  apply IsFractionRing.injective B F
  have hi := congrArg (fun x ↦ b.repr x i) hL
  rwa [basis_repr_sum_smul, basis_repr_sum_smul] at hi

/-- Given an `F`-basis `b i = 1 ⊗ₜ[B] e i` of `F ⊗[B] A` with `e i : A` and `[Module.Finite B A]`,
some `s ∈ B⁰` multiplies all of `A` into the `B`-span of `e`. -/
private theorem exists_mem_nonZeroDivisors_smul_eq_sum {B F A : Type*} [CommRing B] [Field F]
    [Algebra B F] [IsFractionRing B F] [CommRing A] [Algebra B A] [Module.Finite B A]
    [Module.IsTorsionFree B A] {m : ℕ} (b : Module.Basis (Fin m) F (F ⊗[B] A)) (e : Fin m → A)
    (he : ∀ i, b i = (1 : F) ⊗ₜ[B] e i) :
    ∃ s ∈ B⁰, ∃ c : A → Fin m → B,
      (∀ a : A, s • a = ∑ i, c a i • e i) ∧
        ∀ (a : A) (i : Fin m),
          algebraMap B F (c a i) = algebraMap B F s * b.repr (1 ⊗ₜ[B] a) i := by
  let ι : A →ₐ[B] F ⊗[B] A := Algebra.TensorProduct.includeRight
  have hι : Function.Injective ι := injective_includeRight_of_isTorsionFree
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := B) (M := A)
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite B⁰
    (fun p : G × Fin m ↦ b.repr (ι p.1.1) p.2)
  let Φ : (Fin m → B) →ₗ[B] A := basisSumLinearMap e
  have hι_Φ : ∀ v : Fin m → B, ι (Φ v) = ∑ i, algebraMap B F (v i) • b i :=
    includeRight_basisSumLinearMap b e he
  have hG_mem : (G : Set A) ⊆ (LinearMap.range Φ).comap (LinearMap.lsmul B A s.1) := by
    intro g hg
    choose d hd using fun i ↦ hs (⟨g, hg⟩, i)
    refine ⟨d, hι ?_⟩
    rw [hι_Φ d]
    calc
      ∑ i, algebraMap B F (d i) • b i = ∑ i, ((s.1 : B) • b.repr (ι g) i) • b i := by
        simp_rw [hd]
      _ = algebraMap B F s.1 • ∑ i, b.repr (ι g) i • b i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [IsScalarTower.algebraMap_smul F, smul_assoc]
      _ = ι (s.1 • g) := by
        rw [b.sum_repr, map_smul, IsScalarTower.algebraMap_smul F]
  have htop : (⊤ : Submodule B A) ≤ (LinearMap.range Φ).comap (LinearMap.lsmul B A s.1) :=
    hG ▸ Submodule.span_le.mpr hG_mem
  have hall (a : A) : ∃ v : Fin m → B, s.1 • a = Φ v :=
    let ⟨v, hv⟩ := htop (Submodule.mem_top (x := a))
    ⟨v, hv.symm⟩
  choose c hc using hall
  refine ⟨s.1, s.2, c, hc, fun a i ↦ ?_⟩
  have hrepr : ∑ j, algebraMap B F (c a j) • b j = algebraMap B F s.1 • ι a := by
    rw [← hι_Φ (c a), ← hc a, map_smul, IsScalarTower.algebraMap_smul F]
  have h := congrArg (fun x ↦ b.repr x i) hrepr
  rw [basis_repr_sum_smul, LinearEquiv.map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at h
  exact h

end Algebraic

section SmoothingComparison

/-- General Gelfand-smoothing principle: if a ring homomorphism `φ : A →+* L` out of a seminormed
commutative ring `A` into a ring `L` carrying a power-multiplicative seminorm `ν` satisfies a
two-sided linear norm comparison with `‖·‖`, then `smoothingFun (normRingSeminorm A) = ν ∘ φ`,
`smoothingFun (normRingSeminorm A) a ≤ ‖a‖ ≤ C₂ * smoothingFun (normRingSeminorm A) a`, and
`‖a ^ n‖ ^ (1 / n)` converges to `smoothingFun (normRingSeminorm A) a`. -/
private theorem smoothingFun_eq_of_isPowMul_of_norm_comparison {A L : Type*} [SeminormedCommRing A]
    [Ring L] {ν : L → ℝ} (hν_nonneg : ∀ x, 0 ≤ ν x) (hν_pm : IsPowMul ν) (φ : A →+* L)
    {C₁ C₂ : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hle : ∀ a : A, ν (φ a) ≤ C₁ * ‖a‖) (hge : ∀ a : A, ‖a‖ ≤ C₂ * ν (φ a)) :
    (∀ a : A, smoothingFun (normRingSeminorm A) a = ν (φ a)) ∧
      (∀ a : A, smoothingFun (normRingSeminorm A) a ≤ ‖a‖ ∧
        ‖a‖ ≤ C₂ * smoothingFun (normRingSeminorm A) a) ∧
      ∀ a : A, Tendsto (fun n : ℕ ↦ ‖a ^ n‖ ^ (1 / (n : ℝ))) atTop
        (𝓝 (smoothingFun (normRingSeminorm A) a)) := by
  have hcontr (a : A) : ν (φ a) ≤ ‖a‖ :=
    contraction_of_isPowMul_of_boundedWrt (normRingSeminorm A) hν_pm ⟨C₁, hC₁, hle⟩ a
  have hlow (a : A) {n : ℕ} (hn : n ≠ 0) : ν (φ a) ≤ ‖a ^ n‖ ^ (1 / (n : ℝ)) := by
    rw [← Real.pow_rpow_inv_natCast (hν_nonneg (φ a)) hn,
      ← hν_pm (φ a) (Nat.one_le_iff_ne_zero.mpr hn), ← map_pow, one_div]
    exact Real.rpow_le_rpow (hν_nonneg _) (hcontr (a ^ n)) (by positivity)
  have hupp (a : A) {n : ℕ} (hn : n ≠ 0) :
      ‖a ^ n‖ ^ (1 / (n : ℝ)) ≤ C₂ ^ (1 / (n : ℝ)) * ν (φ a) := by
    calc
      ‖a ^ n‖ ^ (1 / (n : ℝ))
          ≤ (C₂ * ν (φ (a ^ n))) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (norm_nonneg _) (hge (a ^ n)) (by positivity)
      _ = C₂ ^ (1 / (n : ℝ)) * ν (φ a) := by
        rw [map_pow, hν_pm (φ a) (Nat.one_le_iff_ne_zero.mpr hn),
          Real.mul_rpow hC₂.le (pow_nonneg (hν_nonneg _) _), one_div,
          Real.pow_rpow_inv_natCast (hν_nonneg _) hn]
  have hlim_up (a : A) :
      Tendsto (fun n : ℕ ↦ C₂ ^ (1 / (n : ℝ)) * ν (φ a)) atTop (𝓝 (ν (φ a))) := by
    simpa using ((Real.continuousAt_const_rpow hC₂.ne' (b := 0)).tendsto.comp
      tendsto_one_div_atTop_nhds_zero_nat).mul_const (ν (φ a))
  have heq (a : A) : smoothingFun (normRingSeminorm A) a = ν (φ a) := by
    refine le_antisymm ?_ (le_ciInf fun n ↦ hlow a n.ne_zero)
    refine ge_of_tendsto (hlim_up a) ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (smoothingFun_le (normRingSeminorm A) a ⟨n, Nat.pos_of_ne_zero hn⟩).trans (hupp a hn)
  refine ⟨heq, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [heq a]
    exact ⟨hcontr a, hge a⟩
  · rw [heq a]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hlim_up a) ?_ ?_
    · filter_upwards [eventually_ne_atTop 0] with n hn using hlow a hn
    · filter_upwards [eventually_ne_atTop 0] with n hn using hupp a hn

end SmoothingComparison

section BanachFunctionAlgebra

/-- An injective `B`-linear map from a finite complete normed `B`-module to a Noetherian complete
normed `B`-module over a complete ultrametric normed `K`-algebra `B` admits a positive inverse norm
bound, by Henkel's open mapping / strict morphism theorem. -/
theorem _root_.LinearMap.exists_norm_le_mul_apply_of_injective {K B M N : Type*}
    [NontriviallyNormedField K]
    [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
    [NormedAddCommGroup M] [NormedSpace K M] [CompleteSpace M]
    [Module B M] [ContinuousSMul B M] [IsScalarTower K B M] [Module.Finite B M]
    [NormedAddCommGroup N] [NormedSpace K N] [CompleteSpace N]
    [Module B N] [ContinuousSMul B N] [IsScalarTower K B N] [IsNoetherian B N]
    (T : M →ₗ[B] N) (hT : Function.Injective T) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : M, ‖x‖ ≤ C * ‖T x‖ := by
  let : Huber.IsTateRing B := Huber.IsTateRing.of_normedAlgebra K B
  have hemb : IsEmbedding T :=
    isEmbedding_iff_isStrictMap_injective.mpr ⟨T.isStrictMap_of_module_finite, hT⟩
  let TK : M →ₗ[K] N := T.restrictScalars K
  let e : M ≃ₗ[K] LinearMap.range TK := LinearEquiv.ofInjective TK hT
  have hcont_symm : Continuous e.symm := by
    rw [hemb.continuous_iff]
    have hcomp : T ∘ e.symm = Subtype.val := by
      ext y
      exact congrArg Subtype.val (e.apply_symm_apply y)
    exact hcomp ▸ continuous_subtype_val
  let S : LinearMap.range TK →L[K] M := { toLinearMap := e.symm.toLinearMap, cont := hcont_symm }
  refine ⟨1 + ‖S‖, by positivity, fun x ↦ ?_⟩
  have hx : e.symm ⟨T x, ⟨x, rfl⟩⟩ = x := e.symm_apply_apply x
  have hle : ‖x‖ ≤ ‖S‖ * ‖T x‖ := by
    simpa [S, hx] using S.le_opNorm ⟨T x, ⟨x, rfl⟩⟩
  exact hle.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

private theorem pi_norm_eq_mul_basis_norm {B F L : Type*} [SeminormedCommRing B] [NormedField F]
    [Algebra B F] [Ring L] [Algebra F L] {m : ℕ} [NeZero m]
    (b : Module.Basis (Fin m) F L) {s : B} (hs_pos : 0 < ‖s‖)
    (hBF : ∀ x : B, ‖algebraMap B F x‖ = ‖x‖) (v : Fin m → B) (y : L)
    (hv : ∀ i, algebraMap B F (v i) = algebraMap B F s * b.repr y i) :
    ‖v‖ = ‖s‖ * b.norm y := by
  have hvi (i : Fin m) : ‖v i‖ = ‖s‖ * ‖b.repr y i‖ := by
    rw [← hBF (v i), hv i, norm_mul, hBF s]
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (mul_nonneg hs_pos.le (b.norm_nonneg y))).mpr fun i ↦ ?_
    rw [hvi i]
    exact mul_le_mul_of_nonneg_left (b.norm_repr_le_norm i) hs_pos.le
  · rw [← le_div_iff₀' hs_pos]
    refine Finset.sup'_le _ _ fun i _ ↦ ?_
    rw [le_div_iff₀' hs_pos, ← hvi i]
    exact norm_le_pi_norm v i

private theorem exists_basis_lattice_bounds {K B F A : Type*}
    [NontriviallyNormedField K]
    [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
    [IsNoetherianRing B]
    [NormedField F] [Algebra B F] [IsFractionRing B F]
    [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [Algebra B A] [IsScalarTower K B A] [Module.Finite B A] [Module.IsTorsionFree B A]
    {m : ℕ} [NeZero m] (b : Module.Basis (Fin m) F (F ⊗[B] A)) (e : Fin m → A)
    (he : ∀ i, b i = (1 : F) ⊗ₜ[B] e i)
    (hBF : ∀ x : B, ‖algebraMap B F x‖ = ‖x‖) (hBA : Continuous (algebraMap B A)) :
    ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ ∀ a : A,
      b.norm ((1 : F) ⊗ₜ[B] a) ≤ K₁ * ‖a‖ ∧ ‖a‖ ≤ K₂ * b.norm ((1 : F) ⊗ₜ[B] a) := by
  have : Nontrivial B := (algebraMap B F).domain_nontrivial
  have : ContinuousSMul B A := continuousSMul_of_algebraMap B A hBA
  obtain ⟨s, hs, c, hc_sum, hc_repr⟩ := exists_mem_nonZeroDivisors_smul_eq_sum b e he
  let Φ : (Fin m → B) →ₗ[B] A := basisSumLinearMap e
  obtain ⟨C_Φ, hC_Φ, hΦ_bound⟩ := Φ.exists_norm_le_mul_apply_of_injective (K := K)
    (injective_basisSumLinearMap b e he)
  obtain ⟨C_s, hC_s, hs_bound⟩ := (LinearMap.lsmul B A s).exists_norm_le_mul_apply_of_injective
    (K := K) ((isRegular_iff_mem_nonZeroDivisors.mpr hs).isSMulRegular)
  let fBA : B →L[K] A := { toLinearMap := (Algebra.linearMap B A).restrictScalars K, cont := hBA }
  have hs_pos : 0 < ‖s‖ := by
    rw [← hBF s, norm_pos_iff]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have hc_norm (a : A) : ‖c a‖ = ‖s‖ * b.norm ((1 : F) ⊗ₜ[B] a) :=
    pi_norm_eq_mul_basis_norm b hs_pos hBF (c a) ((1 : F) ⊗ₜ[B] a) (hc_repr a)
  have hΦ_ca (a : A) : Φ (c a) = s • a := (hc_sum a).symm
  refine ⟨C_Φ * (1 + ‖algebraMap B A s‖) / ‖s‖,
    C_s * (1 + ‖fBA‖) * (1 + ∑ i, ‖e i‖) * ‖s‖, by positivity, by positivity, fun a ↦ ⟨?_, ?_⟩⟩
  · rw [div_mul_eq_mul_div, le_div_iff₀' hs_pos, ← hc_norm a]
    calc
      ‖c a‖ ≤ C_Φ * ‖Φ (c a)‖ := hΦ_bound (c a)
      _ = C_Φ * ‖algebraMap B A s * a‖ := by rw [hΦ_ca a, Algebra.smul_def]
      _ ≤ C_Φ * (‖algebraMap B A s‖ * ‖a‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) hC_Φ.le
      _ ≤ C_Φ * (1 + ‖algebraMap B A s‖) * ‖a‖ := by
        nlinarith [norm_nonneg a, norm_nonneg (algebraMap B A s)]
  · have hΦ_upper : ‖Φ (c a)‖ ≤ (1 + ‖fBA‖) * (1 + ∑ i, ‖e i‖) * ‖c a‖ := by
      calc
        ‖Φ (c a)‖ = ‖∑ i, algebraMap B A (c a i) * e i‖ := by
          simp [Φ, basisSumLinearMap, Algebra.smul_def]
        _ ≤ ∑ i, ‖algebraMap B A (c a i) * e i‖ := norm_sum_le _ _
        _ ≤ ∑ i, ((1 + ‖fBA‖) * ‖c a‖) * ‖e i‖ := by
          refine Finset.sum_le_sum fun i _ ↦
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          calc
            ‖algebraMap B A (c a i)‖ ≤ ‖fBA‖ * ‖c a i‖ := fBA.le_opNorm (c a i)
            _ ≤ (1 + ‖fBA‖) * ‖c a‖ :=
              mul_le_mul (by linarith) (norm_le_pi_norm (c a) i) (norm_nonneg _) (by positivity)
        _ = (1 + ‖fBA‖) * (∑ i, ‖e i‖) * ‖c a‖ := by rw [← Finset.mul_sum]; ring
        _ ≤ (1 + ‖fBA‖) * (1 + ∑ i, ‖e i‖) * ‖c a‖ := by
          nlinarith [norm_nonneg (c a), norm_nonneg fBA]
    calc
      ‖a‖ ≤ C_s * ‖s • a‖ := hs_bound a
      _ = C_s * ‖Φ (c a)‖ := by rw [hΦ_ca a]
      _ ≤ C_s * ((1 + ‖fBA‖) * (1 + ∑ i, ‖e i‖) * ‖c a‖) :=
        mul_le_mul_of_nonneg_left hΦ_upper hC_s.le
      _ = C_s * (1 + ‖fBA‖) * (1 + ∑ i, ‖e i‖) * ‖s‖ * b.norm ((1 : F) ⊗ₜ[B] a) := by
        rw [hc_norm a]; ring

section MainTheorems

variable (K : Type*) [NontriviallyNormedField K]
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
  [IsNoetherianRing B]
  (F : Type*) [NormedField F] [IsUltrametricDist F] [Algebra B F] [IsFractionRing B F]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsReduced A] [Algebra B A] [IsScalarTower K B A] [Module.Finite B A] [Module.IsTorsionFree B A]

include K

/-- Two-sided linear norm comparison between any complete ultrametric `K`-algebra norm on `A` and
the generic spectral norm `a ↦ spectralValue (minpoly F (1 ⊗ₜ[B] a))` on `F ⊗[B] A`, under weak
stability of `F` and continuity of `algebraMap B A`. -/
theorem exists_norm_comparison_spectralValue_minpoly_tensorProduct
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hF : IsWeaklyStable F)
    (hBA : Continuous (algebraMap B A)) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ a : A,
      spectralValue (minpoly F ((1 : F) ⊗ₜ[B] a)) ≤ C₁ * ‖a‖ ∧
        ‖a‖ ≤ C₂ * spectralValue (minpoly F ((1 : F) ⊗ₜ[B] a)) := by
  let L := F ⊗[B] A
  have : IsReduced L := isReduced_tensorProduct_of_isLocalization B⁰
  have hι : Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[B] L) :=
    injective_includeRight_of_isTorsionFree
  rcases subsingleton_or_nontrivial A with hSub | hNontriv
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, fun a ↦ ?_⟩
    rw [Subsingleton.elim a 0, norm_zero, mul_zero, ← reducedSpectralAlgNorm_apply,
      show ((1 : F) ⊗ₜ[B] (0 : A)) = 0 by simp, map_zero, mul_zero]
    exact ⟨le_rfl, le_rfl⟩
  have : Nontrivial L := hι.nontrivial
  obtain ⟨m, hm, b, e, he⟩ := exists_basis_in_range_includeRight (B := B) (F := F) (A := A)
  obtain ⟨K₁, K₂, hK₁, hK₂, hK⟩ := exists_basis_lattice_bounds (K := K) b e he hBF hBA
  obtain ⟨C_sp, D_sp, hC_sp, hD_sp, hsp⟩ := hF.exists_basis_norm_comparison_of_isReduced b
  refine ⟨D_sp * K₁, K₂ * C_sp, by positivity, by positivity, fun a ↦ ⟨?_, ?_⟩⟩
  · calc
      spectralValue (minpoly F ((1 : F) ⊗ₜ[B] a))
          = reducedSpectralAlgNorm F L ((1 : F) ⊗ₜ[B] a) := (reducedSpectralAlgNorm_apply _).symm
      _ ≤ D_sp * b.norm ((1 : F) ⊗ₜ[B] a) := (hsp _).2
      _ ≤ D_sp * (K₁ * ‖a‖) := mul_le_mul_of_nonneg_left (hK a).1 hD_sp.le
      _ = (D_sp * K₁) * ‖a‖ := by ring
  · calc
      ‖a‖ ≤ K₂ * b.norm ((1 : F) ⊗ₜ[B] a) := (hK a).2
      _ ≤ K₂ * (C_sp * reducedSpectralAlgNorm F L ((1 : F) ⊗ₜ[B] a)) :=
        mul_le_mul_of_nonneg_left (hsp _).1 hK₂.le
      _ = (K₂ * C_sp) * spectralValue (minpoly F ((1 : F) ⊗ₜ[B] a)) := by
        rw [reducedSpectralAlgNorm_apply]; ring

/-- Under the hypotheses of [bosch-guntzer-remmert], §3.8.3, Theorem 7, the smoothing
`smoothingFun (normRingSeminorm A) a = inf_{n ≥ 1} ‖a ^ n‖ ^ (1 / n)` of any complete ultrametric
`K`-algebra norm on `A` coincides with the generic spectral norm
`spectralValue (minpoly F (1 ⊗ₜ[B] a))` on `F ⊗[B] A`. -/
theorem smoothingFun_eq_spectralValue_minpoly_tensorProduct
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hF : IsWeaklyStable F)
    (hBA : Continuous (algebraMap B A)) (a : A) :
    smoothingFun (normRingSeminorm A) a =
      spectralValue (minpoly F ((1 : F) ⊗ₜ[B] a)) := by
  let L := F ⊗[B] A
  have : IsReduced L := isReduced_tensorProduct_of_isLocalization B⁰
  obtain ⟨C₁, C₂, hC₁, hC₂, hcomp⟩ :=
    exists_norm_comparison_spectralValue_minpoly_tensorProduct K F hBF hF hBA
  have h := (smoothingFun_eq_of_isPowMul_of_norm_comparison
    (apply_nonneg (reducedSpectralAlgNorm F L)) isPowMul_reducedSpectralAlgNorm
    (Algebra.TensorProduct.includeRight : A →ₐ[B] L).toRingHom hC₁ hC₂
    (fun x ↦ by simpa only [reducedSpectralAlgNorm_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply] using (hcomp x).1)
    (fun x ↦ by simpa only [reducedSpectralAlgNorm_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply] using (hcomp x).2)).1 a
  simpa only [reducedSpectralAlgNorm_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply] using h

/-- When `B` is additionally integrally closed, the smoothing of `‖·‖` on `A` equals
`spectralValue (minpoly B a)` ([bosch-guntzer-remmert], §3.8.1, Theorem 7 and §3.8.3, Theorem 7). -/
theorem smoothingFun_eq_spectralValue_minpoly_base [IsIntegrallyClosed B]
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hF : IsWeaklyStable F)
    (hBA : Continuous (algebraMap B A)) (a : A) :
    smoothingFun (normRingSeminorm A) a = spectralValue (minpoly B a) := by
  rw [smoothingFun_eq_spectralValue_minpoly_tensorProduct K F hBF hF hBA a]
  let ι : A →ₐ[B] F ⊗[B] A := Algebra.TensorProduct.includeRight
  have hι : Function.Injective ι := injective_includeRight_of_isTorsionFree
  have hmin : minpoly F ((1 : F) ⊗ₜ[B] a) = (minpoly B a).map (algebraMap B F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions_of_injective F ι hι
      (Algebra.IsIntegral.isIntegral a)
  rw [hmin, (algebraMap B F).spectralValue_map_of_norm_eq hBF]

/-- **Banach function algebra theorem** ([bosch-guntzer-remmert], §3.8.3, Theorem 7). Let `B` be a
Noetherian ultrametric Banach `K`-algebra with a weakly stable normed fraction field `F` extending
its norm, and let `A` be a reduced ultrametric Banach `K`-algebra that is a finite torsion-free
`B`-algebra with continuous structure map `algebraMap B A`. Then `A` is a Banach function algebra:
its norm is equivalent to its smoothing `smoothingFun (normRingSeminorm A)`. -/
theorem exists_norm_le_mul_smoothingFun
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hF : IsWeaklyStable F)
    (hBA : Continuous (algebraMap B A)) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A,
      smoothingFun (normRingSeminorm A) a ≤ ‖a‖ ∧
        ‖a‖ ≤ C * smoothingFun (normRingSeminorm A) a := by
  let L := F ⊗[B] A
  have : IsReduced L := isReduced_tensorProduct_of_isLocalization B⁰
  obtain ⟨C₁, C₂, hC₁, hC₂, hcomp⟩ :=
    exists_norm_comparison_spectralValue_minpoly_tensorProduct K F hBF hF hBA
  exact ⟨C₂, hC₂, (smoothingFun_eq_of_isPowMul_of_norm_comparison
    (apply_nonneg (reducedSpectralAlgNorm F L)) isPowMul_reducedSpectralAlgNorm
    (Algebra.TensorProduct.includeRight : A →ₐ[B] L).toRingHom hC₁ hC₂
    (fun x ↦ by simpa only [reducedSpectralAlgNorm_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply] using (hcomp x).1)
    (fun x ↦ by simpa only [reducedSpectralAlgNorm_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply] using (hcomp x).2)).2.1⟩

/-- Under the hypotheses of [bosch-guntzer-remmert], §3.8.3, Theorem 7, the spectral-radius
sequence `‖a ^ n‖ ^ (1 / n)` converges to `smoothingFun (normRingSeminorm A) a`, even without
assuming `‖(1 : A)‖ ≤ 1`. -/
theorem tendsto_pow_norm_pow_one_div_smoothingFun
    (hBF : ∀ b : B, ‖algebraMap B F b‖ = ‖b‖) (hF : IsWeaklyStable F)
    (hBA : Continuous (algebraMap B A)) (a : A) :
    Tendsto (fun n : ℕ ↦ ‖a ^ n‖ ^ (1 / (n : ℝ))) atTop
      (𝓝 (smoothingFun (normRingSeminorm A) a)) := by
  let L := F ⊗[B] A
  have : IsReduced L := isReduced_tensorProduct_of_isLocalization B⁰
  obtain ⟨C₁, C₂, hC₁, hC₂, hcomp⟩ :=
    exists_norm_comparison_spectralValue_minpoly_tensorProduct K F hBF hF hBA
  exact (smoothingFun_eq_of_isPowMul_of_norm_comparison
    (apply_nonneg (reducedSpectralAlgNorm F L)) isPowMul_reducedSpectralAlgNorm
    (Algebra.TensorProduct.includeRight : A →ₐ[B] L).toRingHom hC₁ hC₂
    (fun x ↦ by simpa only [reducedSpectralAlgNorm_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply] using (hcomp x).1)
    (fun x ↦ by simpa only [reducedSpectralAlgNorm_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply] using (hcomp x).2)).2.2 a

end MainTheorems

end BanachFunctionAlgebra

end TauCeti
