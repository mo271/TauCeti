/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing.PoleFiltration
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Chart
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.Away
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Prime
-- Proof-only: the body of `projModelVariableChangeIso` is not exposed.
import all TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel

/-!
# The homogeneous coordinate ring as the Rees ring of the pole filtration

Let `W` be a Weierstrass curve over a commutative ring `R`, and let
`F n = poleFiltration W.toAffine n` be the pole-order filtration on the affine coordinate ring
`R[W]` (assigning weight `2` to `x` and weight `3` to `y`). Dehomogenizing along `Z` sends
`X ↦ x T`, `Y ↦ y T`, `Z ↦ T` and gives a canonical graded `R`-algebra isomorphism

  `W.toProjective.CoordinateRing ≃ₐ[R] TauCeti.coeffSubalgebra (fun k ↦ F (3 * k))`

(`WeierstrassCurve.Projective.dehomogEquiv`). Consequently, the projective Weierstrass model
`W.projModel` is canonically isomorphic over `Spec R` to
`Proj (TauCeti.coeffSubalgebra.grade (fun k ↦ F (3 * k)))`
(`WeierstrassCurve.projModelIsoProjRees`), identifying the standard affine chart `D₊(Z)`
(`WeierstrassCurve.affineChartι`) with the chart `D₊(X)` of the section ring
(`WeierstrassCurve.affineChartι_projModelIsoProjRees_hom`).

No ellipticity or Noetherian hypothesis on `W` or `R` is needed.

## Main definitions

* `WeierstrassCurve.Projective.dehomogEquiv`: the graded `R`-algebra isomorphism from
  `W.toProjective.CoordinateRing` to
  `coeffSubalgebra (fun k ↦ poleFiltration W.toAffine (3 * k))`.
* `WeierstrassCurve.chartRingTwoEquivAffine`: the `R`-algebra isomorphism between the chart ring
  `W.toProjective.ChartRing 2` of `D₊(Z)` and the affine coordinate ring
  `W.toAffine.CoordinateRing`.
* `WeierstrassCurve.affineChartι`: the open immersion `Spec R[W] ⟶ W.projModel` identifying the
  affine curve with the chart `D₊(Z)`.
* `WeierstrassCurve.projModelIsoProjRees`: the isomorphism
  `W.projModel ≅ Proj (coeffSubalgebra.grade (fun k ↦ poleFiltration W.toAffine (3 * k)))`
  over `Spec R`.

## Main results

* `WeierstrassCurve.Projective.dehomogEquiv_mem_grade_iff`: `dehomogEquiv` preserves and reflects
  the grading.
* `WeierstrassCurve.Projective.coeff_dehomogEquiv_variableChangeEquiv`: `dehomogEquiv` intertwines
  projective and affine changes of variables.
* `WeierstrassCurve.affineChartι_projModelOver` and
  `WeierstrassCurve.affineChartι_projModelIsoProjRees_hom`: compatibility of `affineChartι` with
  the structure morphism and with `projModelIsoProjRees`.
* `WeierstrassCurve.affineChartι_projModelVariableChangeIso_hom`: on `D₊(Z)`, the projective
  isomorphism `projModelVariableChangeIso W C` is `Spec` of the affine change of variables.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2.
-/

public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open TauCeti

namespace WeierstrassCurve

section Algebra

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

open Affine.CoordinateRing in
/-- The `R`-algebra isomorphism between the chart ring `R[X, Y, Z] ⧸ (W, Z - 1)` of `D₊(Z)` and
the affine coordinate ring `R[W]`, sending `X ↦ x`, `Y ↦ y`, `Z ↦ 1`. -/
noncomputable def chartRingTwoEquivAffine :
    W.toProjective.ChartRing 2 ≃ₐ[R] W.toAffine.CoordinateRing := by
  have heq : aeval ![AdjoinRoot.of W.toAffine.polynomial Polynomial.X,
      AdjoinRoot.root W.toAffine.polynomial, 1] W.toProjective.polynomial = 0 := by
    rw [aeval_def, ← eval_map, ← Projective.map_polynomial]
    exact (Projective.equation_some _ _).mpr (by
      simpa only [AlgHom.id_apply, Affine.baseChange, WeierstrassCurve.baseChange] using
        Affine.CoordinateRing.equation_of_algHom (AlgHom.id R W.toAffine.CoordinateRing))
  let toFun : W.toProjective.ChartRing 2 →ₐ[R] W.toAffine.CoordinateRing :=
    Ideal.Quotient.liftₐ _
      (aeval ![AdjoinRoot.of W.toAffine.polynomial Polynomial.X,
        AdjoinRoot.root W.toAffine.polynomial, 1]) fun _ hp ↦
      RingHom.mem_ker.mp <| Ideal.span_le.mpr (Set.range_subset_iff.mpr <| Fin.forall_fin_two.mpr
        ⟨by rw [Projective.chartRelation_zero]; exact heq, by simp⟩) hp
  let invFun : W.toAffine.CoordinateRing →ₐ[R] W.toProjective.ChartRing 2 :=
    Affine.CoordinateRing.evalAlgHom <|
      (Projective.equation_some (Ideal.Quotient.mk _ (X 0)) (Ideal.Quotient.mk _ (X 1))).mp <| by
        rw [Projective.Equation, Affine.baseChange, WeierstrassCurve.baseChange,
          Projective.map_polynomial, eval_map, ← aeval_def,
          ← W.toProjective.chartRing_mk_X_self 2, ← Projective.chartRelation_zero _ 2,
          ← Ideal.Quotient.mk_span_range _ 0]
        exact DFunLike.congr_fun (algHom_ext fun i ↦ by fin_cases i <;> simp :
          aeval _ = Ideal.Quotient.mkₐ R _) _
  have hto : ∀ p, toFun (Ideal.Quotient.mk _ p) =
      aeval ![AdjoinRoot.of W.toAffine.polynomial Polynomial.X,
        AdjoinRoot.root W.toAffine.polynomial, 1] p := fun _ ↦ rfl
  exact AlgEquiv.ofAlgHom toFun invFun
    (by
      ext <;> simp [invFun, hto])
    (Ideal.Quotient.algHom_ext R <| algHom_ext fun j ↦ by
      fin_cases j <;> simp [invFun, hto])

@[simp]
theorem chartRingTwoEquivAffine_mk (p : MvPolynomial (Fin 3) R) :
    W.chartRingTwoEquivAffine (Ideal.Quotient.mk _ p) =
      aeval ![AdjoinRoot.of W.toAffine.polynomial Polynomial.X,
        AdjoinRoot.root W.toAffine.polynomial, 1] p := by
  rfl

@[simp]
theorem chartRingTwoEquivAffine_symm_of_X :
    W.chartRingTwoEquivAffine.symm (AdjoinRoot.of W.toAffine.polynomial Polynomial.X) =
      Ideal.Quotient.mk _ (X 0) := by
  simp [chartRingTwoEquivAffine]

@[simp]
theorem chartRingTwoEquivAffine_symm_root :
    W.chartRingTwoEquivAffine.symm (AdjoinRoot.root W.toAffine.polynomial) =
      Ideal.Quotient.mk _ (X 1) := by
  simp [chartRingTwoEquivAffine]

namespace Projective

open Affine.CoordinateRing

/-- The scaled pole filtration `k ↦ poleFiltration W.toAffine (3 * k)` on `R[W]`. -/
private noncomputable abbrev poleFiltrationThree (W : WeierstrassCurve R) (k : ℕ) :
    Submodule R W.toAffine.CoordinateRing :=
  Affine.CoordinateRing.poleFiltration W.toAffine (3 * k)

/-- The element `x T` in degree `1` of `coeffSubalgebra (fun k ↦ poleFiltration W (3 * k))`. -/
private noncomputable def dehomogX : coeffSubalgebra (poleFiltrationThree W) :=
  coeffSubalgebra.monomial (poleFiltrationThree W) 1
    (AdjoinRoot.of W.toAffine.polynomial Polynomial.X) (of_X_mem_poleFiltration _ (by decide))

/-- The element `y T` in degree `1` of `coeffSubalgebra (fun k ↦ poleFiltration W (3 * k))`. -/
private noncomputable def dehomogY : coeffSubalgebra (poleFiltrationThree W) :=
  coeffSubalgebra.monomial (poleFiltrationThree W) 1
    (AdjoinRoot.root W.toAffine.polynomial) (root_mem_poleFiltration _ (by decide))

/-- The element `T` in degree `1` of `coeffSubalgebra (fun k ↦ poleFiltration W (3 * k))`. -/
private noncomputable def dehomogZ : coeffSubalgebra (poleFiltrationThree W) :=
  coeffSubalgebra.X (poleFiltrationThree W) (one_mem_poleFiltration _ 3)

private theorem equation_dehomog :
    (W.toProjective.map (algebraMap R (coeffSubalgebra (poleFiltrationThree W)))).Equation
      ![dehomogX W, dehomogY W, dehomogZ W] := by
  rw [Projective.equation_iff]
  apply Subtype.ext
  let x := AdjoinRoot.of W.toAffine.polynomial Polynomial.X
  let y := AdjoinRoot.root W.toAffine.polynomial
  let a := algebraMap R W.toAffine.CoordinateRing
  have hEq : y ^ 2 + a W.a₁ * x * y + a W.a₃ * y -
      (x ^ 3 + a W.a₂ * x ^ 2 + a W.a₄ * x + a W.a₆) = 0 := by
    have h := equation_X_root W
    rw [Affine.equation_iff'] at h
    simpa only [x, y, a, Affine.baseChange_a₁, Affine.baseChange_a₂, Affine.baseChange_a₃,
      Affine.baseChange_a₄, Affine.baseChange_a₆] using h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, Subalgebra.coe_sub,
    Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap,
    ZeroMemClass.coe_zero, dehomogX, dehomogY, dehomogZ, coeffSubalgebra.coe_monomial,
    coeffSubalgebra.coe_X, Polynomial.algebraMap_apply, ← Polynomial.C_mul_X_pow_eq_monomial,
    pow_one]
  change (Polynomial.C y * Polynomial.X) ^ 2 * Polynomial.X +
      Polynomial.C (a W.a₁) * (Polynomial.C x * Polynomial.X) *
        (Polynomial.C y * Polynomial.X) * Polynomial.X +
      Polynomial.C (a W.a₃) * (Polynomial.C y * Polynomial.X) * Polynomial.X ^ 2 -
    ((Polynomial.C x * Polynomial.X) ^ 3 +
      Polynomial.C (a W.a₂) * (Polynomial.C x * Polynomial.X) ^ 2 * Polynomial.X +
      Polynomial.C (a W.a₄) * (Polynomial.C x * Polynomial.X) * Polynomial.X ^ 2 +
      Polynomial.C (a W.a₆) * Polynomial.X ^ 3) = 0
  trans Polynomial.C (y ^ 2 + a W.a₁ * x * y + a W.a₃ * y -
      (x ^ 3 + a W.a₂ * x ^ 2 + a W.a₄ * x + a W.a₆)) * Polynomial.X ^ 3
  · simp only [map_sub, map_add, map_mul, map_pow]
    ring
  · rw [hEq, map_zero, zero_mul]

/-- The dehomogenization homomorphism
`W.toProjective.CoordinateRing →ₐ[R] coeffSubalgebra (F ∘ (3 * ·))` sending
`X ↦ x T`, `Y ↦ y T`, `Z ↦ T`. -/
private noncomputable def dehomogHom :
    W.toProjective.CoordinateRing →ₐ[R] coeffSubalgebra (poleFiltrationThree W) :=
  AlgHom.mk' (W.toProjective.evalHom (algebraMap R _) (equation_dehomog W)) fun r x ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    exact RingHom.congr_fun
      (W.toProjective.evalHom_comp_algebraMap (algebraMap R _) (equation_dehomog W)) r

@[simp]
private theorem dehomogHom_coord_zero :
    dehomogHom W (W.toProjective.coord 0) = dehomogX W :=
  congrFun (W.toProjective.evalHom_comp_coord _ _) 0

@[simp]
private theorem dehomogHom_coord_one :
    dehomogHom W (W.toProjective.coord 1) = dehomogY W :=
  congrFun (W.toProjective.evalHom_comp_coord _ _) 1

@[simp]
private theorem dehomogHom_coord_two :
    dehomogHom W (W.toProjective.coord 2) = dehomogZ W :=
  congrFun (W.toProjective.evalHom_comp_coord _ _) 2

private theorem dehomogHom_mem_grade {n : ℕ} {a : W.toProjective.CoordinateRing}
    (ha : a ∈ W.toProjective.grading n) :
    dehomogHom W a ∈ coeffSubalgebra.grade (poleFiltrationThree W) n := by
  obtain ⟨p, hp, rfl⟩ := W.toProjective.mem_grading_iff.mp ha
  have hval : dehomogHom W (Ideal.Quotient.mk _ p) =
      aeval ![dehomogX W, dehomogY W, dehomogZ W] p :=
    W.toProjective.evalHom_mk _ _ p
  rw [hval]
  have h1 (i : Fin 3) : ![dehomogX W, dehomogY W, dehomogZ W] i ∈
      coeffSubalgebra.grade (poleFiltrationThree W) 1 := by
    fin_cases i
    · exact coeffSubalgebra.monomial_mem_grade 1 _ _
    · exact coeffSubalgebra.monomial_mem_grade 1 _ _
    · exact coeffSubalgebra.X_mem_grade_one _ _
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd ↦ ?_
  rw [aeval_monomial]
  have hd_deg : d.sum (fun _ e ↦ e) = n := by
    simpa [Finsupp.weight_apply, Finsupp.linearCombination_apply] using hp (mem_support_iff.mp hd)
  have hprod : ∏ i ∈ d.support, ![dehomogX W, dehomogY W, dehomogZ W] i ^ d i ∈
      coeffSubalgebra.grade (poleFiltrationThree W) (∑ i ∈ d.support, d i) := by
    induction d.support using Finset.cons_induction with
    | empty =>
      simpa using SetLike.GradedOne.one_mem (A := coeffSubalgebra.grade (poleFiltrationThree W))
    | cons i s hi ih =>
      rw [Finset.prod_cons, Finset.sum_cons]
      have hpow : ![dehomogX W, dehomogY W, dehomogZ W] i ^ d i ∈
          coeffSubalgebra.grade (poleFiltrationThree W) (d i) := by
        simpa [smul_eq_mul, mul_one] using SetLike.pow_mem_graded (d i) (h1 i)
      exact SetLike.mul_mem_graded hpow ih
  rw [show ∑ i ∈ d.support, d i = n from hd_deg] at hprod
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hprod

/-- `dehomogHom` as a graded ring homomorphism. -/
private noncomputable def dehomogGradedHomAux :
    W.toProjective.grading →+*ᵍ coeffSubalgebra.grade (poleFiltrationThree W) where
  __ := (dehomogHom W).toRingHom
  map_mem := dehomogHom_mem_grade W

private theorem evalOne_dehomogHom_mk (p : MvPolynomial (Fin 3) R) :
    coeffSubalgebra.evalOne (poleFiltrationThree W)
      (dehomogHom W (Ideal.Quotient.mk _ p)) =
      W.chartRingTwoEquivAffine (Ideal.Quotient.mk _ p) := by
  have heval : (coeffSubalgebra.evalOne (poleFiltrationThree W)).comp (dehomogHom W) =
      W.chartRingTwoEquivAffine.toAlgHom.comp
        (Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ R _) fun q hq ↦
          RingHom.mem_ker.mp <| Ideal.Quotient.eq_zero_iff_mem.mpr <|
            Ideal.span_mono
              (Set.singleton_subset_iff.mpr ⟨0, W.toProjective.chartRelation_zero 2⟩ :
                {W.toProjective.polynomial} ⊆ Set.range (W.toProjective.chartRelation 2))
              hq) := by
    apply AlgHom.toRingHom_injective
    apply W.toProjective.ringHom_ext
    · ext r; simp
    · ext i
      fin_cases i <;>
      · change coeffSubalgebra.evalOne _ (dehomogHom W (W.toProjective.coord _)) =
          W.chartRingTwoEquivAffine (Ideal.Quotient.mk _ (X _))
        simp [dehomogX, dehomogY, dehomogZ, coeffSubalgebra.evalOne_monomial,
          coeffSubalgebra.evalOne_X]
  exact AlgHom.congr_fun heval (Ideal.Quotient.mk _ p)

private theorem dehomogHom_injective : Function.Injective (dehomogHom W) := by
  classical
  -- Compare `(evalOne ∘ dehomogHom)` with `chartRingTwoEquivAffine ∘ awayEquivChartRing 2` on
  -- homogeneous elements, then cancel powers of the non-zero-divisor `Z`.
  intro a b hab
  rw [← sub_eq_zero] at hab ⊢
  rw [← map_sub] at hab
  set c := a - b
  suffices ∀ n,
      (DirectSum.decompose W.toProjective.grading c n : W.toProjective.CoordinateRing) = 0 by
    rw [← DirectSum.sum_support_decompose W.toProjective.grading c]
    exact Finset.sum_eq_zero fun n _ ↦ this n
  intro n
  set cn : W.toProjective.grading n := DirectSum.decompose W.toProjective.grading c n
  have hcn0 : dehomogHom W cn.1 = 0 := by
    have hdec := (dehomogGradedHomAux W).map_directSumDecompose (x := c) (i := n)
    change dehomogHom W cn.1 =
      (DirectSum.decompose (coeffSubalgebra.grade (poleFiltrationThree W)) (dehomogHom W c) n :
        coeffSubalgebra (poleFiltrationThree W)) at hdec
    rw [hab, DirectSum.decompose_zero] at hdec
    simpa using hdec
  let z : Away W.toProjective.grading (W.toProjective.coord 2) :=
    Away.mk W.toProjective.grading (W.toProjective.coord_mem_grading 2) n cn
      (by simp [smul_eq_mul])
  have hz_image : W.chartRingTwoEquivAffine (W.toProjective.awayEquivChartRing 2 z) = 0 := by
    obtain ⟨p, -, hp⟩ := W.toProjective.mem_grading_iff.mp cn.2
    have haway : W.toProjective.awayEquivChartRing 2 z = Ideal.Quotient.mk _ p := by
      have hpm : Ideal.Quotient.mk (Ideal.span {W.toProjective.polynomial}) p ∈
          W.toProjective.grading (n • 1) := by simpa [smul_eq_mul] using hp ▸ cn.2
      have := W.toProjective.awayEquivChartRing_mk 2 hpm
      convert this using 2
      ext
      simp [z, Away.val_mk, hp]
    rw [haway, ← evalOne_dehomogHom_mk W p, hp, hcn0, map_zero]
  have hz0 : z = 0 :=
    (W.toProjective.awayEquivChartRing 2).injective
      (W.chartRingTwoEquivAffine.injective (by simpa using hz_image))
  have hval0 : z.val = 0 := by rw [hz0]; exact HomogeneousLocalization.val_zero
  rw [Away.val_mk, Localization.mk_eq_mk'_apply] at hval0
  obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
    (IsLocalization.mk'_eq_zero_iff (S := Localization _) _ _).mp hval0
  exact (mem_nonZeroDivisors_iff.mp
    (Submonoid.pow_mem (nonZeroDivisors _) W.toProjective.coord_two_mem_nonZeroDivisors m)).1
    cn.1 (by simpa [mul_comm] using hm)

private theorem dehomogHom_surjective : Function.Surjective (dehomogHom W) := by
  -- First prove every pure `x`-power `x^i T^k` with `2 * i ≤ 3 * k` lies in the range, by strong
  -- induction on `i`.
  have hx_mem : ∀ i k : ℕ, ∀ h : 2 * i ≤ 3 * k,
      coeffSubalgebra.monomial (poleFiltrationThree W) k
        (AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ i)
        (by
          have := basisMonomials_mem_poleFiltration W.toAffine (n := 3 * k) (p := (i, 0))
            (by simpa using h)
          simpa using this) ∈ (dehomogHom W).range := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro k h
      by_cases hi : i < 3
      · -- For `i < 3`, `2 * i ≤ 3 * k` implies `i ≤ k`, so `X^i * Z^(k - i)` hits `x^i T^k`.
        have hik : i ≤ k := by omega
        refine ⟨W.toProjective.coord 0 ^ i * W.toProjective.coord 2 ^ (k - i), ?_⟩
        change dehomogHom W (W.toProjective.coord 0 ^ i * W.toProjective.coord 2 ^ (k - i)) = _
        rw [map_mul, map_pow, map_pow, dehomogHom_coord_zero, dehomogHom_coord_two]
        apply Subtype.ext
        simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, dehomogX, dehomogZ,
          coeffSubalgebra.coe_monomial, coeffSubalgebra.coe_X,
          ← Polynomial.C_mul_X_pow_eq_monomial, pow_one, mul_pow, ← map_pow, mul_assoc,
          ← pow_add, Nat.add_sub_of_le hik]
      · -- For `i ≥ 3`, write `i = i' + 3` and eliminate `x^3` via the Weierstrass equation.
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 3 := ⟨i - 3, by omega⟩
        have hk2 : 2 ≤ k := by omega
        have hk1 : 1 ≤ k := by omega
        have h0 := ih i' (by omega) (k - 2) (by omega)
        have h1 := ih (i' + 1) (by omega) (k - 1) (by omega)
        have h2 := ih i' (by omega) (k - 1) (by omega)
        have h3 := ih (i' + 2) (by omega) k (by omega)
        have h4 := ih (i' + 1) (by omega) k (by omega)
        have h5 := ih i' (by omega) k (by omega)
        have hy_mem : dehomogY W ∈ (dehomogHom W).range :=
          ⟨W.toProjective.coord 1, dehomogHom_coord_one W⟩
        have hcomb :
            coeffSubalgebra.monomial (poleFiltrationThree W) (k - 2)
                (AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ i') _ * dehomogY W ^ 2 +
              W.a₁ • (coeffSubalgebra.monomial (poleFiltrationThree W) (k - 1)
                (AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ (i' + 1)) _ * dehomogY W) +
              W.a₃ • (coeffSubalgebra.monomial (poleFiltrationThree W) (k - 1)
                (AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ i') _ * dehomogY W) -
              W.a₂ • coeffSubalgebra.monomial (poleFiltrationThree W) k
                (AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ (i' + 2)) _ -
              W.a₄ • coeffSubalgebra.monomial (poleFiltrationThree W) k
                (AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ (i' + 1)) _ -
              W.a₆ • coeffSubalgebra.monomial (poleFiltrationThree W) k
                (AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ i') _ ∈
              (dehomogHom W).range :=
          sub_mem (sub_mem (sub_mem (add_mem (add_mem
            (mul_mem h0 (pow_mem hy_mem 2))
            (Subalgebra.smul_mem _ (mul_mem h1 hy_mem) _))
            (Subalgebra.smul_mem _ (mul_mem h2 hy_mem) _))
            (Subalgebra.smul_mem _ h3 _))
            (Subalgebra.smul_mem _ h4 _))
            (Subalgebra.smul_mem _ h5 _)
        convert hcomb using 1
        apply Subtype.ext
        have hEq := equation_X_root W
        rw [Affine.equation_iff'] at hEq
        simp only [Affine.baseChange_a₁, Affine.baseChange_a₂, Affine.baseChange_a₃,
          Affine.baseChange_a₄, Affine.baseChange_a₆] at hEq
        have hx3 : AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ 3 =
            AdjoinRoot.root W.toAffine.polynomial ^ 2 +
              algebraMap R _ W.a₁ * AdjoinRoot.of W.toAffine.polynomial Polynomial.X *
                AdjoinRoot.root W.toAffine.polynomial +
              algebraMap R _ W.a₃ * AdjoinRoot.root W.toAffine.polynomial -
              algebraMap R _ W.a₂ * AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ 2 -
              algebraMap R _ W.a₄ * AdjoinRoot.of W.toAffine.polynomial Polynomial.X -
              algebraMap R _ W.a₆ := by
          linear_combination -hEq
        have hX2 : (Polynomial.X : Polynomial W.toAffine.CoordinateRing) ^ (k - 2) *
            Polynomial.X ^ 2 = Polynomial.X ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hk2]
        have hX1 : (Polynomial.X : Polynomial W.toAffine.CoordinateRing) ^ (k - 1) *
            Polynomial.X = Polynomial.X ^ k := by
          rw [← pow_succ, Nat.sub_add_cancel hk1]
        simp only [Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow,
          Subalgebra.coe_algebraMap, dehomogY, coeffSubalgebra.coe_monomial,
          ← Polynomial.C_mul_X_pow_eq_monomial, pow_one, Algebra.smul_def,
          Polynomial.algebraMap_apply]
        rw [pow_add, hx3]
        simp only [mul_sub, mul_add, map_sub, map_add, map_mul, map_pow, sub_mul, add_mul]
        calc
          _ = Polynomial.C (AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ i' *
                AdjoinRoot.root W.toAffine.polynomial ^ 2) *
                  (Polynomial.X ^ (k - 2) * Polynomial.X ^ 2) +
              Polynomial.C (algebraMap R _ W.a₁ *
                (AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ (i' + 1) *
                  AdjoinRoot.root W.toAffine.polynomial)) *
                  (Polynomial.X ^ (k - 1) * Polynomial.X) +
              Polynomial.C (algebraMap R _ W.a₃ *
                (AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ i' *
                  AdjoinRoot.root W.toAffine.polynomial)) *
                  (Polynomial.X ^ (k - 1) * Polynomial.X) -
              Polynomial.C (algebraMap R _ W.a₂ *
                AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ (i' + 2)) * Polynomial.X ^ k -
              Polynomial.C (algebraMap R _ W.a₄ *
                AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ (i' + 1)) * Polynomial.X ^ k -
              Polynomial.C (algebraMap R _ W.a₆ *
                AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ i') * Polynomial.X ^ k := by
            rw [hX2, hX1]
            simp only [pow_succ, map_mul, map_pow]
            ring
          _ = _ := by
            simp only [map_mul, map_pow]
            ring
  -- Every basis monomial `x^i y^j T^k` with `2 * i + 3 * j ≤ 3 * k` lies in the range.
  have hbasis : ∀ (k : ℕ) (p : ℕ × Fin 2) (hp : 2 * p.1 + 3 * p.2.1 ≤ 3 * k),
      coeffSubalgebra.monomial (poleFiltrationThree W) k
        (Affine.CoordinateRing.basisMonomials W.toAffine p)
        (basisMonomials_mem_poleFiltration W.toAffine hp) ∈ (dehomogHom W).range := by
    rintro k ⟨i, j⟩ hij
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · simpa only [basisMonomials_apply, Fin.val_zero, pow_zero, mul_one] using
        hx_mem i k (by simpa using hij)
    · have hk1 : 1 ≤ k := by dsimp at hij; omega
      have hprev := hx_mem i (k - 1) (by dsimp at hij; omega)
      have hy_mem : dehomogY W ∈ (dehomogHom W).range :=
        ⟨W.toProjective.coord 1, dehomogHom_coord_one W⟩
      have hprod := mul_mem hprev hy_mem
      convert hprod using 1
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, dehomogY, coeffSubalgebra.coe_monomial,
        ← Polynomial.C_mul_X_pow_eq_monomial, pow_one]
      rw [basisMonomials_apply]
      simp only [Fin.val_one, pow_one, map_mul]
      calc
        Polynomial.C (AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ i) *
            Polynomial.C (AdjoinRoot.root W.toAffine.polynomial) * Polynomial.X ^ k
            = Polynomial.C (AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ i) *
                Polynomial.C (AdjoinRoot.root W.toAffine.polynomial) *
                (Polynomial.X ^ (k - 1) * Polynomial.X) := by
              rw [← pow_succ, Nat.sub_add_cancel hk1]
        _ = _ := by ring
  have hmon : ∀ (k : ℕ) (b : W.toAffine.CoordinateRing) (hb : b ∈ poleFiltrationThree W k),
      coeffSubalgebra.monomial (poleFiltrationThree W) k b hb ∈ (dehomogHom W).range := by
    intro k b hb
    set B := poleFiltrationBasis W.toAffine (3 * k)
    have hrep : b = ∑ p ∈ (B.repr ⟨b, hb⟩).support,
        (B.repr ⟨b, hb⟩ p) • Affine.CoordinateRing.basisMonomials W.toAffine p.1 := by
      have h := congrArg Subtype.val (B.linearCombination_repr ⟨b, hb⟩)
      rw [Finsupp.linearCombination_apply, Finsupp.sum, AddSubmonoidClass.coe_finsetSum] at h
      simpa only [SetLike.val_smul, B, poleFiltrationBasis_apply] using h.symm
    have hmeq : coeffSubalgebra.monomial (poleFiltrationThree W) k b hb =
        ∑ p ∈ (B.repr ⟨b, hb⟩).support,
          (B.repr ⟨b, hb⟩ p) •
            coeffSubalgebra.monomial (poleFiltrationThree W) k
              (Affine.CoordinateRing.basisMonomials W.toAffine p.1)
              (basisMonomials_mem_poleFiltration W.toAffine p.2) := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum, coeffSubalgebra.coe_monomial]
      conv_lhs => rw [hrep]
      rw [map_sum (Polynomial.monomial k)]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [SetLike.val_smul, coeffSubalgebra.coe_monomial, Polynomial.smul_monomial]
    rw [hmeq]
    exact sum_mem fun p _ ↦ Subalgebra.smul_mem _ (hbasis k p.1 p.2) _
  intro g
  suffices g ∈ (dehomogHom W).range from this
  have hsum : g = ∑ k ∈ (g : Polynomial W.toAffine.CoordinateRing).support,
      coeffSubalgebra.monomial (poleFiltrationThree W) k
        ((g : Polynomial W.toAffine.CoordinateRing).coeff k)
        (mem_coeffSubalgebra_iff.mp g.2 k) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simpa [coeffSubalgebra.coe_monomial] using
      ((g : Polynomial W.toAffine.CoordinateRing).as_sum_support)
  rw [hsum]
  exact sum_mem fun k _ ↦ hmon k _ (mem_coeffSubalgebra_iff.mp g.2 k)

/-- **Dehomogenization isomorphism.** The homogeneous coordinate ring of `W` is canonically
isomorphic as a graded `R`-algebra to `coeffSubalgebra (fun k ↦ poleFiltration W (3 * k))`,
sending `X ↦ x T`, `Y ↦ y T`, `Z ↦ T`. -/
noncomputable def dehomogEquiv :
    W.toProjective.CoordinateRing ≃ₐ[R]
      coeffSubalgebra (fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k)) :=
  AlgEquiv.ofBijective (dehomogHom W) ⟨dehomogHom_injective W, dehomogHom_surjective W⟩

@[simp]
theorem dehomogEquiv_coord_zero :
    dehomogEquiv W (W.toProjective.coord 0) =
      coeffSubalgebra.monomial (fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k)) 1
        (AdjoinRoot.of W.toAffine.polynomial Polynomial.X)
        (Affine.CoordinateRing.of_X_mem_poleFiltration _ (by decide)) :=
  dehomogHom_coord_zero W

@[simp]
theorem dehomogEquiv_coord_one :
    dehomogEquiv W (W.toProjective.coord 1) =
      coeffSubalgebra.monomial (fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k)) 1
        (AdjoinRoot.root W.toAffine.polynomial)
        (Affine.CoordinateRing.root_mem_poleFiltration _ (by decide)) :=
  dehomogHom_coord_one W

@[simp]
theorem dehomogEquiv_coord_two :
    dehomogEquiv W (W.toProjective.coord 2) =
      coeffSubalgebra.X (fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k))
        (Affine.CoordinateRing.one_mem_poleFiltration _ 3) :=
  dehomogHom_coord_two W

/-- `dehomogEquiv` preserves and reflects the grading. -/
theorem dehomogEquiv_mem_grade_iff {n : ℕ} {a : W.toProjective.CoordinateRing} :
    dehomogEquiv W a ∈
        coeffSubalgebra.grade
          (fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k)) n ↔
      a ∈ W.toProjective.grading n :=
  Graded.map_mem_iff_of_injective (dehomogGradedHomAux W) (dehomogEquiv W).injective

/-- `dehomogEquiv` intertwines projective and affine changes of variables. -/
theorem coeff_dehomogEquiv_variableChangeEquiv (C : VariableChange R)
    (a : W.toProjective.CoordinateRing) (k : ℕ) :
    ((dehomogEquiv (C • W) (Projective.variableChangeEquiv W C a) :
        Polynomial (C • W).toAffine.CoordinateRing).coeff k) =
      Affine.CoordinateRing.variableChangeEquiv C rfl
        ((dehomogEquiv W a : Polynomial W.toAffine.CoordinateRing).coeff k) := by
  let lhs : W.toProjective.CoordinateRing →ₐ[R] Polynomial (C • W).toAffine.CoordinateRing :=
    (coeffSubalgebra _).val.comp ((dehomogEquiv (C • W)).toAlgHom.comp
      (Projective.variableChangeEquiv W C).toAlgHom)
  let rhs : W.toProjective.CoordinateRing →ₐ[R] Polynomial (C • W).toAffine.CoordinateRing :=
    (Polynomial.mapAlgHom (Affine.CoordinateRing.variableChangeEquiv C rfl).toAlgHom).comp
      ((coeffSubalgebra _).val.comp (dehomogEquiv W).toAlgHom)
  have heq : lhs = rhs := by
    apply AlgHom.toRingHom_injective
    apply W.toProjective.ringHom_ext
    · ext r; simp [lhs, rhs]
    · funext i
      have hmk : ∀ r : R, dehomogEquiv (C • W) (Ideal.Quotient.mk _ (MvPolynomial.C r)) =
          algebraMap R _ r := fun r ↦ (dehomogEquiv (C • W)).commutes r
      fin_cases i
      · change ((dehomogEquiv (C • W)
            (Projective.variableChangeEquiv W C (Ideal.Quotient.mk _ (X 0))) :
            Polynomial (C • W).toAffine.CoordinateRing)) =
          Polynomial.map (Affine.CoordinateRing.variableChangeEquiv C rfl).toRingHom
            (dehomogEquiv W (W.toProjective.coord 0) : Polynomial W.toAffine.CoordinateRing)
        rw [Projective.variableChangeEquiv_mk, linearSubst_X]
        have hvc : (Affine.CoordinateRing.variableChangeEquiv C (W' := W) rfl).toRingHom
            (AdjoinRoot.of W.toAffine.polynomial Polynomial.X) =
            algebraMap R _ (C.u : R) ^ 2 *
              AdjoinRoot.of (C • W).toAffine.polynomial Polynomial.X +
              algebraMap R _ C.r :=
          Affine.CoordinateRing.variableChangeEquiv_of_X C rfl
        simp only [VariableChange.toMatrix_def, Fin.sum_univ_three, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons, map_add, map_mul, hmk, map_zero, zero_mul, add_zero,
          dehomogEquiv_coord_zero, dehomogEquiv_coord_two, Subalgebra.coe_add, Subalgebra.coe_mul,
          Subalgebra.coe_pow, Subalgebra.coe_algebraMap, coeffSubalgebra.coe_monomial,
          coeffSubalgebra.coe_X, Polynomial.algebraMap_apply,
          ← Polynomial.C_mul_X_pow_eq_monomial, pow_one, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_X, hvc, map_pow]
        ring
      · change ((dehomogEquiv (C • W)
            (Projective.variableChangeEquiv W C (Ideal.Quotient.mk _ (X 1))) :
            Polynomial (C • W).toAffine.CoordinateRing)) =
          Polynomial.map (Affine.CoordinateRing.variableChangeEquiv C rfl).toRingHom
            (dehomogEquiv W (W.toProjective.coord 1) : Polynomial W.toAffine.CoordinateRing)
        rw [Projective.variableChangeEquiv_mk, linearSubst_X]
        have hvc : (Affine.CoordinateRing.variableChangeEquiv C (W' := W) rfl).toRingHom
            (AdjoinRoot.root W.toAffine.polynomial) =
            algebraMap R _ (C.u : R) ^ 3 * AdjoinRoot.root (C • W).toAffine.polynomial +
              algebraMap R _ (C.u : R) ^ 2 * algebraMap R _ C.s *
                AdjoinRoot.of (C • W).toAffine.polynomial Polynomial.X +
              algebraMap R _ C.t :=
          Affine.CoordinateRing.variableChangeEquiv_root C rfl
        simp only [VariableChange.toMatrix_def, Fin.sum_univ_three, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons, map_add, map_mul, hmk, dehomogEquiv_coord_zero,
          dehomogEquiv_coord_one, dehomogEquiv_coord_two, Subalgebra.coe_add, Subalgebra.coe_mul,
          Subalgebra.coe_pow, Subalgebra.coe_algebraMap, coeffSubalgebra.coe_monomial,
          coeffSubalgebra.coe_X, Polynomial.algebraMap_apply,
          ← Polynomial.C_mul_X_pow_eq_monomial, pow_one, Polynomial.map_mul, Polynomial.map_C,
          Polynomial.map_X, hvc, map_pow]
        ring
      · change ((dehomogEquiv (C • W)
            (Projective.variableChangeEquiv W C (Ideal.Quotient.mk _ (X 2))) :
            Polynomial (C • W).toAffine.CoordinateRing)) =
          Polynomial.map (Affine.CoordinateRing.variableChangeEquiv C rfl).toRingHom
            (dehomogEquiv W (W.toProjective.coord 2) : Polynomial W.toAffine.CoordinateRing)
        rw [Projective.variableChangeEquiv_mk, linearSubst_X]
        simp only [VariableChange.toMatrix_def, Fin.sum_univ_three, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons, map_zero, map_one, zero_mul, one_mul, zero_add,
          dehomogEquiv_coord_two, coeffSubalgebra.coe_X, Polynomial.map_X]
  simpa [lhs, rhs, Polynomial.coe_mapAlgHom, Polynomial.coeff_map] using
    congrArg (fun p : Polynomial (C • W).toAffine.CoordinateRing ↦ p.coeff k)
      (AlgHom.congr_fun heq a)

end Projective

end Algebra

section Scheme

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The standard affine chart `D₊(Z)` of `W.projModel`, presented as an open immersion from
`Spec R[W]`. -/
noncomputable def affineChartι : Spec (.of W.toAffine.CoordinateRing) ⟶ W.projModel :=
  Spec.map W.chartRingTwoEquivAffine.toRingEquiv.toCommRingCatIso.hom ≫ W.chartι 2

instance isOpenImmersion_affineChartι : IsOpenImmersion W.affineChartι := by
  unfold affineChartι
  infer_instance

instance isSchemeTheoreticallyDominant_affineChartι :
    IsSchemeTheoreticallyDominant W.affineChartι := by
  unfold affineChartι
  infer_instance

@[simp]
theorem opensRange_affineChartι :
    W.affineChartι.opensRange =
      Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2) := by
  unfold affineChartι
  rw [Scheme.Hom.opensRange_comp_of_isIso, opensRange_chartι]

@[reassoc (attr := simp)]
theorem affineChartι_projModelOver :
    W.affineChartι ≫ W.projModelOver = Spec.algebraMap R W.toAffine.CoordinateRing := by
  unfold affineChartι
  rw [Category.assoc, chartι_projModelOver, ← Spec.map_comp]
  congr 1
  ext r
  simp

/-- `dehomogEquiv W` as a graded ring homomorphism. -/
noncomputable def Projective.dehomogGradedHom :
    W.toProjective.grading →+*ᵍ
      coeffSubalgebra.grade
        (fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k)) where
  __ := (Projective.dehomogEquiv W).toRingEquiv.toRingHom
  map_mem ha := (Projective.dehomogEquiv_mem_grade_iff W).mpr ha

/-- The inverse of `dehomogEquiv W` as a graded ring homomorphism. -/
noncomputable def Projective.dehomogGradedHomSymm :
    coeffSubalgebra.grade
        (fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k)) →+*ᵍ
      W.toProjective.grading where
  __ := (Projective.dehomogEquiv W).symm.toRingEquiv.toRingHom
  map_mem {n y} hy := (Projective.dehomogEquiv_mem_grade_iff W).mp (by
    change Projective.dehomogEquiv W ((Projective.dehomogEquiv W).symm y) ∈ _
    rw [AlgEquiv.apply_symm_apply]
    exact hy)

private theorem Projective.rightInverse_dehomogGradedHomSymm :
    Function.RightInverse (Projective.dehomogGradedHomSymm W) (Projective.dehomogGradedHom W) :=
  (Projective.dehomogEquiv W).apply_symm_apply

private theorem Projective.leftInverse_dehomogGradedHomSymm :
    Function.LeftInverse (Projective.dehomogGradedHomSymm W) (Projective.dehomogGradedHom W) :=
  (Projective.dehomogEquiv W).symm_apply_apply

/-- **Isomorphism between the projective Weierstrass model and `Proj` of the Rees ring of the pole
filtration.** -/
noncomputable def projModelIsoProjRees :
    W.projModel ≅
      Proj (coeffSubalgebra.grade
        (fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k))) :=
  (Proj.mapIso (Projective.dehomogGradedHom W) (Projective.dehomogGradedHomSymm W)
    (Projective.rightInverse_dehomogGradedHomSymm W)
    (Projective.leftInverse_dehomogGradedHomSymm W)).symm

/-- `projModelIsoProjRees` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem projModelIsoProjRees_hom_toSpecCoeff :
    W.projModelIsoProjRees.hom ≫
        Proj.toSpecCoeff (coeffSubalgebra.grade
          (fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k))) =
      W.projModelOver := by
  rw [projModelIsoProjRees, Iso.symm_hom, Proj.mapIso_inv, Proj.toSpecCoeff_def,
    Proj.map_toSpecZero_assoc, ← Spec.map_comp, projModelOver]
  congr 2
  ext r
  simp [Projective.dehomogGradedHomSymm]

/-- Transport `Away.map φ x` along an equality `φ x = y`. -/
private noncomputable def awayMapEq {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (φ : 𝒜 →+*ᵍ ℬ) (x : A) (y : B) (hxy : φ x = y) : Away 𝒜 x →+* Away ℬ y :=
  hxy ▸ Away.map φ x

private theorem awayMapEq_mk {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (φ : 𝒜 →+*ᵍ ℬ) {x : A} {y : B}
    (hxy : φ x = y) {d : ℕ} (hx : x ∈ 𝒜 d) (hy : y ∈ ℬ d)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayMapEq φ x y hxy (Away.mk 𝒜 hx n a ha) = Away.mk ℬ hy n (φ a) (φ.map_mem ha) := by
  subst hxy
  ext
  simp [awayMapEq, Away.map_mk, Away.val_mk]

private theorem awayι_comp_map_eq {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R B}
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (φ : 𝒜 →+*ᵍ ℬ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    {x : A} {y : B} (hxy : φ x = y) {d : ℕ} (hd : 0 < d) (hx : x ∈ 𝒜 d) (hy : y ∈ ℬ d) :
    Proj.awayι ℬ y hy hd ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom (awayMapEq φ x y hxy)) ≫ Proj.awayι 𝒜 x hx hd := by
  subst hxy
  exact Proj.awayι_comp_map φ hφ hd x hx

/-- Under `projModelIsoProjRees`, the affine chart `D₊(Z)` (`affineChartι W`) corresponds to the
chart `D₊(X)` of the Rees ring, identified with `Spec R[W]` via `coeffSubalgebra.awayXEquiv`. -/
@[reassoc]
theorem affineChartι_projModelIsoProjRees_hom :
    W.affineChartι ≫ W.projModelIsoProjRees.hom =
      Spec.map (CommRingCat.ofHom
        (coeffSubalgebra.awayXEquiv
          (fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k))
          (Affine.CoordinateRing.one_mem_poleFiltration _ 3)
          ((Affine.CoordinateRing.poleFiltration_mono _).comp
            fun _ _ h ↦ Nat.mul_le_mul_left 3 h)
          (Affine.CoordinateRing.iSup_poleFiltration_three_mul _)).toRingHom) ≫
      Proj.awayι
        (coeffSubalgebra.grade (fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k)))
        (coeffSubalgebra.X _ (Affine.CoordinateRing.one_mem_poleFiltration _ 3))
        (coeffSubalgebra.X_mem_grade_one _ _) one_pos := by
  let M := fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k)
  let h1 : (1 : W.toAffine.CoordinateRing) ∈ M 1 :=
    Affine.CoordinateRing.one_mem_poleFiltration W.toAffine 3
  let X_M := coeffSubalgebra.X M h1
  have hZ : Projective.dehomogGradedHomSymm W X_M = W.toProjective.coord 2 := by
    change (Projective.dehomogEquiv W).symm X_M = _
    rw [AlgEquiv.symm_apply_eq, Projective.dehomogEquiv_coord_two]
  have haway : Proj.awayι W.toProjective.grading (W.toProjective.coord 2)
      (W.toProjective.coord_mem_grading 2) one_pos ≫ W.projModelIsoProjRees.hom =
      Spec.map (CommRingCat.ofHom
        (awayMapEq (Projective.dehomogGradedHomSymm W) X_M (W.toProjective.coord 2) hZ)) ≫
      Proj.awayι (coeffSubalgebra.grade M) X_M (coeffSubalgebra.X_mem_grade_one M h1) one_pos := by
    rw [projModelIsoProjRees, Iso.symm_hom, Proj.mapIso_inv]
    exact awayι_comp_map_eq (Projective.dehomogGradedHomSymm W) _ hZ one_pos
      (coeffSubalgebra.X_mem_grade_one M h1) (W.toProjective.coord_mem_grading 2)
  unfold affineChartι
  rw [chartι_def, Category.assoc, Category.assoc, haway, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc]
  congr 2
  -- Compare the composite ring hom `Away (grade M) X_M →+* R[W]` with `awayXEquiv` on every
  -- fraction `a / X_M^n`.
  apply CommRingCat.hom_ext
  ext z
  obtain ⟨n, a, ha, rfl⟩ :=
    Away.mk_surjective (coeffSubalgebra.grade M) (coeffSubalgebra.X_mem_grade_one M h1) z
  obtain ⟨b, hb, hba⟩ := coeffSubalgebra.mem_grade_iff.mp (by simpa [smul_eq_mul] using ha)
  have ha_eq : a = coeffSubalgebra.monomial M n b hb :=
    Subtype.ext (by rw [coeffSubalgebra.coe_monomial]; exact hba.symm)
  have hmap : awayMapEq (Projective.dehomogGradedHomSymm W) X_M (W.toProjective.coord 2) hZ
      (Away.mk (coeffSubalgebra.grade M) (coeffSubalgebra.X_mem_grade_one M h1) n a ha) =
      Away.mk W.toProjective.grading (W.toProjective.coord_mem_grading 2) n
        ((Projective.dehomogEquiv W).symm a)
        (by
          have hmem : (Projective.dehomogEquiv W).symm a ∈ W.toProjective.grading n :=
            (Projective.dehomogEquiv_mem_grade_iff W).mp (by simpa [smul_eq_mul] using ha)
          simpa [smul_eq_mul] using hmem) :=
    awayMapEq_mk (Projective.dehomogGradedHomSymm W) hZ (coeffSubalgebra.X_mem_grade_one M h1)
      (W.toProjective.coord_mem_grading 2) n a ha
  have hmem_deg : (Projective.dehomogEquiv W).symm a ∈ W.toProjective.grading n :=
    (Projective.dehomogEquiv_mem_grade_iff W).mp (by simpa [smul_eq_mul] using ha)
  obtain ⟨p, -, hp⟩ := W.toProjective.mem_grading_iff.mp hmem_deg
  have hchart : W.toProjective.awayEquivChartRing 2
      (awayMapEq (Projective.dehomogGradedHomSymm W) X_M (W.toProjective.coord 2) hZ
        (Away.mk (coeffSubalgebra.grade M) (coeffSubalgebra.X_mem_grade_one M h1) n a ha)) =
      Ideal.Quotient.mk _ p := by
    rw [hmap]
    have hpm : Ideal.Quotient.mk (Ideal.span {W.toProjective.polynomial}) p ∈
        W.toProjective.grading (n • 1) := by simpa [smul_eq_mul] using hp ▸ hmem_deg
    have := W.toProjective.awayEquivChartRing_mk 2 hpm
    convert this using 2
    ext
    simp [Away.val_mk, hp]
  have h1' : coeffSubalgebra.evalOne M a = W.chartRingTwoEquivAffine (Ideal.Quotient.mk _ p) := by
    have h := Projective.evalOne_dehomogHom_mk W p
    rw [hp] at h
    exact (congrArg (coeffSubalgebra.evalOne M)
      ((Projective.dehomogEquiv W).apply_symm_apply a)).symm.trans h
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    RingEquiv.toCommRingCatIso_hom, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv]
  rw [hchart, ← h1']
  have hz_eq : Away.mk (coeffSubalgebra.grade M) (coeffSubalgebra.X_mem_grade_one M h1) n a ha =
      Away.mk (coeffSubalgebra.grade M) (coeffSubalgebra.X_mem_grade_one M h1) n
        (coeffSubalgebra.monomial M n b hb)
        (by simpa [smul_eq_mul] using coeffSubalgebra.monomial_mem_grade n b hb) := by
    ext; simp [Away.val_mk, ha_eq]
  rw [hz_eq]
  change coeffSubalgebra.evalOne M a =
    coeffSubalgebra.awayXEquiv M h1
      ((Affine.CoordinateRing.poleFiltration_mono W.toAffine).comp
        fun _ _ h ↦ Nat.mul_le_mul_left 3 h)
      (Affine.CoordinateRing.iSup_poleFiltration_three_mul _)
      (Away.mk (coeffSubalgebra.grade M) (coeffSubalgebra.X_mem_grade_one M h1) n
        (coeffSubalgebra.monomial M n b hb) _)
  rw [coeffSubalgebra.awayXEquiv_mk, ha_eq, coeffSubalgebra.evalOne_monomial]

/-- The graded ring isomorphism on Rees rings induced by an admissible change of variables. -/
private noncomputable def variableChangeReesHom (C : VariableChange R) :
    coeffSubalgebra.grade
        (fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k)) →+*ᵍ
      coeffSubalgebra.grade
        (fun k ↦ Affine.CoordinateRing.poleFiltration (C • W).toAffine (3 * k)) where
  toFun f := ⟨Polynomial.map (Affine.CoordinateRing.variableChangeEquiv C (W' := W) rfl).toRingHom
      f.1,
    mem_coeffSubalgebra_iff.mpr fun k ↦ by
      simpa [Polynomial.coeff_map] using
        Affine.CoordinateRing.variableChangeEquiv_mem_poleFiltration C rfl
          (mem_coeffSubalgebra_iff.mp f.2 k)⟩
  map_one' := by ext1; simp
  map_mul' _ _ := by ext1; simp
  map_zero' := by ext1; simp
  map_add' _ _ := by ext1; simp
  map_mem {k f} hf := by
    obtain ⟨b, hb, hbf⟩ := coeffSubalgebra.mem_grade_iff.mp hf
    refine coeffSubalgebra.mem_grade_iff.mpr
      ⟨Affine.CoordinateRing.variableChangeEquiv C (W' := W) rfl b,
        Affine.CoordinateRing.variableChangeEquiv_mem_poleFiltration C rfl hb, ?_⟩
    simp [← hbf, Polynomial.map_monomial]

private theorem variableChangeReesHom_surjective (C : VariableChange R) :
    Function.Surjective (W.variableChangeReesHom C) := by
  intro g
  let e := Affine.CoordinateRing.variableChangeEquiv C (W' := W) rfl
  refine ⟨⟨Polynomial.map e.symm.toRingHom g.1, mem_coeffSubalgebra_iff.mpr fun k ↦ by
    simpa [e, Polynomial.coeff_map, Affine.CoordinateRing.variableChangeEquiv_symm] using
      Affine.CoordinateRing.variableChangeEquiv_mem_poleFiltration C⁻¹
        (inv_smul_smul C W) (mem_coeffSubalgebra_iff.mp g.2 k)⟩, ?_⟩
  ext1
  change Polynomial.map e.toRingHom (Polynomial.map e.symm.toRingHom g.1) = g.1
  rw [Polynomial.map_map,
    show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from
      RingHom.ext fun x ↦ e.apply_symm_apply x,
    Polynomial.map_id]

private theorem projModelVariableChangeIso_hom_projModelIsoProjRees_hom (C : VariableChange R) :
    (W.projModelVariableChangeIso C).hom ≫ W.projModelIsoProjRees.hom =
      (C • W).projModelIsoProjRees.hom ≫
        Proj.map (W.variableChangeReesHom C)
          (HomogeneousIdeal.irrelevant_le_map_of_surjective _
            (W.variableChangeReesHom_surjective C)) := by
  rw [projModelVariableChangeIso, projModelIsoProjRees, projModelIsoProjRees, Iso.symm_hom,
    Iso.symm_hom, Proj.mapIso_hom, Proj.mapIso_inv, Proj.mapIso_inv, ← Proj.map_comp,
    ← Proj.map_comp]
  refine Proj.map_congr ?_ _ _
  apply GradedRingHom.ext
  intro f
  apply (Projective.dehomogEquiv (C • W)).injective
  apply Subtype.ext
  ext k
  change ((Projective.dehomogEquiv (C • W)
      (Projective.variableChangeEquiv W C ((Projective.dehomogEquiv W).symm f)) :
      Polynomial (C • W).toAffine.CoordinateRing).coeff k) =
    ((Projective.dehomogEquiv (C • W)
      ((Projective.dehomogEquiv (C • W)).symm (W.variableChangeReesHom C f)) :
      Polynomial (C • W).toAffine.CoordinateRing).coeff k)
  rw [Projective.coeff_dehomogEquiv_variableChangeEquiv, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]
  simp [variableChangeReesHom, Polynomial.coeff_map]

private theorem awayXEquiv_awayMapEq_variableChangeReesHom (C : VariableChange R) :
    (coeffSubalgebra.awayXEquiv
      (fun k ↦ Affine.CoordinateRing.poleFiltration (C • W).toAffine (3 * k))
      (Affine.CoordinateRing.one_mem_poleFiltration _ 3)
      ((Affine.CoordinateRing.poleFiltration_mono _).comp fun _ _ h ↦ Nat.mul_le_mul_left 3 h)
      (Affine.CoordinateRing.iSup_poleFiltration_three_mul _)).toRingHom.comp
      (awayMapEq (W.variableChangeReesHom C)
        (coeffSubalgebra.X _ (Affine.CoordinateRing.one_mem_poleFiltration W.toAffine 3))
        (coeffSubalgebra.X _ (Affine.CoordinateRing.one_mem_poleFiltration (C • W).toAffine 3))
        (by ext1; simp [variableChangeReesHom])) =
    (Affine.CoordinateRing.variableChangeEquiv C (W' := W) rfl).toRingHom.comp
      (coeffSubalgebra.awayXEquiv
        (fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k))
        (Affine.CoordinateRing.one_mem_poleFiltration _ 3)
        ((Affine.CoordinateRing.poleFiltration_mono _).comp fun _ _ h ↦ Nat.mul_le_mul_left 3 h)
        (Affine.CoordinateRing.iSup_poleFiltration_three_mul _)).toRingHom := by
  let M := fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k)
  let M' := fun k ↦ Affine.CoordinateRing.poleFiltration (C • W).toAffine (3 * k)
  let h1W : (1 : W.toAffine.CoordinateRing) ∈ M 1 :=
    Affine.CoordinateRing.one_mem_poleFiltration W.toAffine 3
  let h1CW : (1 : (C • W).toAffine.CoordinateRing) ∈ M' 1 :=
    Affine.CoordinateRing.one_mem_poleFiltration (C • W).toAffine 3
  let φ := W.variableChangeReesHom C
  have hXeq : φ (coeffSubalgebra.X M h1W) = coeffSubalgebra.X M' h1CW := by
    ext1; simp [φ, variableChangeReesHom]
  ext z
  obtain ⟨n, a, ha, rfl⟩ :=
    Away.mk_surjective (coeffSubalgebra.grade M) (coeffSubalgebra.X_mem_grade_one M h1W) z
  obtain ⟨b, hb, hba⟩ := coeffSubalgebra.mem_grade_iff.mp (by simpa [smul_eq_mul] using ha)
  have ha_eq : a = coeffSubalgebra.monomial M n b hb :=
    Subtype.ext (by rw [coeffSubalgebra.coe_monomial]; exact hba.symm)
  have hz_eq : Away.mk (coeffSubalgebra.grade M) (coeffSubalgebra.X_mem_grade_one M h1W) n a ha =
      Away.mk (coeffSubalgebra.grade M) (coeffSubalgebra.X_mem_grade_one M h1W) n
        (coeffSubalgebra.monomial M n b hb)
        (by simpa [smul_eq_mul] using coeffSubalgebra.monomial_mem_grade n b hb) := by
    ext; simp [Away.val_mk, ha_eq]
  have hφa : φ (coeffSubalgebra.monomial M n b hb) =
      coeffSubalgebra.monomial M' n
        (Affine.CoordinateRing.variableChangeEquiv C (W' := W) rfl b)
        (Affine.CoordinateRing.variableChangeEquiv_mem_poleFiltration C rfl hb) := by
    ext1; simp [φ, variableChangeReesHom, Polynomial.map_monomial]
  have hmap_mk : awayMapEq φ (coeffSubalgebra.X M h1W) (coeffSubalgebra.X M' h1CW) hXeq
      (Away.mk (coeffSubalgebra.grade M) (coeffSubalgebra.X_mem_grade_one M h1W) n
        (coeffSubalgebra.monomial M n b hb)
        (by simpa [smul_eq_mul] using coeffSubalgebra.monomial_mem_grade n b hb)) =
      Away.mk (coeffSubalgebra.grade M') (coeffSubalgebra.X_mem_grade_one M' h1CW) n
        (coeffSubalgebra.monomial M' n
          (Affine.CoordinateRing.variableChangeEquiv C (W' := W) rfl b)
          (Affine.CoordinateRing.variableChangeEquiv_mem_poleFiltration C rfl hb))
        (by simpa [smul_eq_mul] using coeffSubalgebra.monomial_mem_grade n _ _) := by
    rw [awayMapEq_mk (hy := coeffSubalgebra.X_mem_grade_one M' h1CW)]
    ext
    simp [Away.val_mk, hφa]
  rw [RingHom.comp_apply, RingHom.comp_apply, hz_eq, hmap_mk]
  exact (coeffSubalgebra.awayXEquiv_mk ..).trans
    (congrArg (Affine.CoordinateRing.variableChangeEquiv C (W' := W) rfl)
      (coeffSubalgebra.awayXEquiv_mk ..)).symm

/-- On the affine chart `D₊(Z)`, the projective isomorphism `projModelVariableChangeIso W C` is
`Spec` of the affine variable-change isomorphism `variableChangeEquiv C rfl`. -/
@[reassoc]
theorem affineChartι_projModelVariableChangeIso_hom (C : VariableChange R) :
    (C • W).affineChartι ≫ (W.projModelVariableChangeIso C).hom =
      Spec.map (CommRingCat.ofHom (Affine.CoordinateRing.variableChangeEquiv C rfl).toRingHom) ≫
        W.affineChartι := by
  let M := fun k ↦ Affine.CoordinateRing.poleFiltration W.toAffine (3 * k)
  let M' := fun k ↦ Affine.CoordinateRing.poleFiltration (C • W).toAffine (3 * k)
  let h1W : (1 : W.toAffine.CoordinateRing) ∈ M 1 :=
    Affine.CoordinateRing.one_mem_poleFiltration W.toAffine 3
  let h1CW : (1 : (C • W).toAffine.CoordinateRing) ∈ M' 1 :=
    Affine.CoordinateRing.one_mem_poleFiltration (C • W).toAffine 3
  let φ := W.variableChangeReesHom C
  have hφ : HomogeneousIdeal.irrelevant (coeffSubalgebra.grade M') ≤
      (HomogeneousIdeal.irrelevant (coeffSubalgebra.grade M)).map φ :=
    HomogeneousIdeal.irrelevant_le_map_of_surjective _ (W.variableChangeReesHom_surjective C)
  rw [← cancel_mono W.projModelIsoProjRees.hom, Category.assoc, Category.assoc,
    affineChartι_projModelIsoProjRees_hom, projModelVariableChangeIso_hom_projModelIsoProjRees_hom,
    affineChartι_projModelIsoProjRees_hom_assoc]
  have hXeq : φ (coeffSubalgebra.X M h1W) = coeffSubalgebra.X M' h1CW := by
    ext1
    simp [φ, variableChangeReesHom]
  have hXmap : Proj.awayι (coeffSubalgebra.grade M') (coeffSubalgebra.X M' h1CW)
      (coeffSubalgebra.X_mem_grade_one M' h1CW) one_pos ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom
        (awayMapEq φ (coeffSubalgebra.X M h1W) (coeffSubalgebra.X M' h1CW) hXeq)) ≫
        Proj.awayι (coeffSubalgebra.grade M) (coeffSubalgebra.X M h1W)
          (coeffSubalgebra.X_mem_grade_one M h1W) one_pos :=
    awayι_comp_map_eq φ hφ hXeq one_pos
      (coeffSubalgebra.X_mem_grade_one M h1W) (coeffSubalgebra.X_mem_grade_one M' h1CW)
  rw [hXmap, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, W.awayXEquiv_awayMapEq_variableChangeReesHom C]

end Scheme

end WeierstrassCurve
