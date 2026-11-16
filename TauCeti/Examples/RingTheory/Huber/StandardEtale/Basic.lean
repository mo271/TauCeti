/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Huber.Padic.Field
import TauCeti.RingTheory.Huber.StandardEtale.ExplicitInverse

/-!
# Examples and non-examples of standard étale presentations

Concrete examples and obstructions for `TauCeti.Huber.tateSeries`, `TauCeti.Huber.tateSeriesPlus`,
`TauCeti.Huber.StandardEtalePresentation`, and `TauCeti.Huber.explicitInverse`:

* coordinate coefficients, non-invertibility of `tateSeries.X`, and comparison with
  `Pair.polydiscVar` and `Pair.polydiscPlus`;
* membership and non-membership of `p` and `p⁻¹` in `tateSeriesPlus` over `(ℚ_[p], ℤ_[p])`;
* the zero-variable identity presentation of `(ℚ_[p], ℤ_[p])` at `p`, its explicit-inverse
  refinement `withInverse`, and impossibility at the non-pseudouniformiser scale `1`;
* the quadratic extension `T² - 5` over `(ℚ_[2], ℤ_[2])` at `ϖ = 2` with exponent `k = 1`, where
  `2` divides the Jacobian `2 T` in `ℤ_[2]⟨T⟩` yet `2 · (2 T)⁻¹ = (1 / 5) T` lies in `Q⁺`, together
  with its explicit-inverse equation `S · (2 T) - 2` and squared Jacobian `4 T²`;
* inseparability obstruction for Frobenius `T ^ p - a` in characteristic `p`, contrasted with the
  Artin–Schreier presentation `T ^ p - T - u` (`J = -1`, `k = 0`) and the idempotent quadratic
  presentation `T² - T` (`J = 2 T - 1`, `J² = 1 + 4 (T² - T)`, `k = 0`).

## References

* [R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*][huber1996], §1.6.
* [P. Scholze, *Étale cohomology of diamonds*][scholze2017], §24.
-/

open TauCeti.Huber

/-! ### Coordinate variables, `tateSeriesPlus`, and polydisc comparisons -/

section TateSeriesExamples

variable {p : ℕ} [Fact p.Prime]

-- Each restricted variable has degree-one self-coefficient 1, off-diagonal coefficient 0, and
-- zero constant term.
example :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)
        (tateSeries.X 2 ℚ_[p] 0 : MvPowerSeries (Fin 2) ℚ_[p]) = 1 ∧
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)
        (tateSeries.X 2 ℚ_[p] 0 : MvPowerSeries (Fin 2) ℚ_[p]) = 0 ∧
      MvPowerSeries.constantCoeff
        ((tateSeries.X 2 ℚ_[p] 0 + tateSeries.X 2 ℚ_[p] 1 : tateSeries 2 ℚ_[p]) :
          MvPowerSeries (Fin 2) ℚ_[p]) = 0 := by
  refine ⟨by simp, ?_, by simp⟩
  rw [tateSeries.coe_X, MvPowerSeries.coeff_X]
  split_ifs with h
  · exact absurd (Finsupp.single_left_injective one_ne_zero h) (by decide)
  · rfl

-- A restricted coordinate variable is never a unit over a nontrivial base, and coerces to the
-- completed polydisc variable.
example :
    ¬ IsUnit (tateSeries.X 1 ℚ_[p] 0) ∧
      ((tateSeries.X 1 ℚ_[p] 0 : tateSeries 1 ℚ_[p]) :
          restrictedMvPowerSeriesCompletion 1 ℚ_[p]) =
        Pair.polydiscVar 1 ℚ_[p] 0 :=
  ⟨tateSeries.not_isUnit_X 0, tateSeries.coe_completion_X 0⟩

-- Over `(ℚ_[p], ℤ_[p])`, the constant series `p` lies in `tateSeriesPlus`, whereas `p⁻¹` does not.
example :
    let P := Pair.powerBounded ℚ_[p]
    algebraMap ℚ_[p] (tateSeries 1 ℚ_[p]) p ∈ tateSeriesPlus 1 ℚ_[p] P.plus ∧
      algebraMap ℚ_[p] (tateSeries 1 ℚ_[p]) (p : ℚ_[p])⁻¹ ∉ tateSeriesPlus 1 ℚ_[p] P.plus := by
  intro P
  refine ⟨algebraMap_mem_tateSeriesPlus_iff.mpr ?_, fun hinv ↦ ?_⟩
  · simpa only [pow_one] using (Padic.isPseudoUniformizer_p (p := p)).pow_mem_plus P 1
  · have hmem : (p : ℚ_[p])⁻¹ ∈ P.plus := algebraMap_mem_tateSeriesPlus_iff.mp hinv
    rw [Pair.powerBounded_plus] at hmem
    have hnorm : ‖(p : ℚ_[p])⁻¹‖ ≤ 1 :=
      isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp hmem)
    rw [norm_inv, _root_.Padic.norm_p] at hnorm
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hge := (inv_inv (p : ℝ)) ▸ hnorm
    linarith

-- `tateSeriesPlus` for `⊤` is `⊤`, and matches `polydiscPlus` across the completion equivalence.
example (N : ℕ) :
    tateSeriesPlus N ℚ_[p] ⊤ = ⊤ ∧
      (tateSeriesPlus N ℚ_[p] (Pair.powerBounded ℚ_[p]).plus).map
          (restrictedMvPowerSeriesCompletionEquiv N ℚ_[p]).symm.toRingHom =
        (Pair.powerBounded ℚ_[p]).polydiscPlus N :=
  ⟨tateSeriesPlus_top, (Pair.powerBounded ℚ_[p]).map_tateSeriesPlus_completionEquiv_symm N⟩

end TateSeriesExamples

/-! ### Identity presentation, scale impossibility, and explicit-inverse refinement -/

section IdentityAndImpossibility

variable {p : ℕ} [Fact p.Prime]

-- `(ℚ_[p], ℤ_[p])` admits the zero-variable identity presentation over itself at `ϖ = p`, and its
-- explicit-inverse refinement `withInverse` presents the same pair in one variable `S - 1` with
-- `k = 0` and `π S = 1`.
example :
    let P₀ := StandardEtalePresentation.id (Pair.powerBounded ℚ_[p])
      (Padic.isPseudoUniformizer_p (p := p))
    P₀.N = 0 ∧ P₀.k = 0 ∧ P₀.withInverse.N = 1 ∧ P₀.withInverse.k = 0 ∧
      P₀.withInverse.F (Fin.last P₀.N) = (tateSeries.X 1 ℚ_[p] 0 - 1 : tateSeries 1 ℚ_[p]) ∧
      P₀.withInverse.π (tateSeries.X 1 ℚ_[p] 0) = 1 := by
  intro P₀
  have hunit : (P₀.jacobianUnit : ℚ_[p]) = 1 := by
    rw [StandardEtalePresentation.coe_jacobianUnit]
    change (tateSeries.finZeroAlgEquiv ℚ_[p])
      (tateSeriesJacobian (Fin.elim0 : Fin 0 → tateSeries 0 ℚ_[p])) = 1
    rw [tateSeriesJacobian_fin_zero, map_one]
  have hunit_eq : P₀.jacobianUnit = 1 := Units.ext hunit
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · change explicitInverse (p : ℚ_[p]) (Fin.elim0 : Fin 0 → tateSeries 0 ℚ_[p]) 0 (Fin.last 0) =
      tateSeries.X 1 ℚ_[p] 0 - 1
    simp [Fin.last]
  · have hlast : P₀.withInverse.π (tateSeries.X 1 ℚ_[p] 0) =
        algebraMap ℚ_[p] ℚ_[p] ((p : ℚ_[p]) ^ 0) * ↑P₀.jacobianUnit⁻¹ :=
      P₀.withInverse_π_last
    simpa [hunit_eq] using hlast

-- No standard étale presentation over `ℚ_[2]` exists at scale `ϖ = 1`, because `1` is not
-- topologically nilpotent in the Hausdorff nontrivial ring `ℚ_[2]`.
example :
    IsEmpty (StandardEtalePresentation (Pair.powerBounded ℚ_[2]) 1 (Pair.powerBounded ℚ_[2])) := by
  refine ⟨fun P ↦ ?_⟩
  have hnil : Filter.Tendsto (fun n : ℕ ↦ (1 : ℚ_[2]) ^ n) Filter.atTop (nhds 0) :=
    P.isPseudoUniformizer.isTopologicallyNilpotent
  simp only [one_pow] at hnil
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hnil)

end IdentityAndImpossibility

/-! ### Quadratic presentation `T² - 5` over `(ℚ_[2], ℤ_[2])` at `ϖ = 2`, `k = 1` -/

section DyadicQuadratic

-- Over `(ℚ_[2], ℤ_[2])` at scale `ϖ = 2`, the quadratic polynomial `F = ![T² - 5]` has Jacobian
-- `2 T`, explicit-inverse equation `S * (2 T) - 2`, and squared explicit-inverse Jacobian `4 T²`.
example :
    let T : tateSeries 1 ℚ_[2] := tateSeries.X 1 ℚ_[2] 0
    let F : Fin 1 → tateSeries 1 ℚ_[2] := ![T ^ 2 - algebraMap ℚ_[2] (tateSeries 1 ℚ_[2]) 5]
    let T₀ : tateSeries 2 ℚ_[2] := tateSeries.X 2 ℚ_[2] 0
    let S : tateSeries 2 ℚ_[2] := tateSeries.X 2 ℚ_[2] 1
    tateSeriesJacobian F = 2 * T ∧
      explicitInverse (2 : ℚ_[2]) F 1 1 =
        S * (2 * T₀) - algebraMap ℚ_[2] (tateSeries 2 ℚ_[2]) 2 ∧
      tateSeriesJacobian (explicitInverse (2 : ℚ_[2]) F 1) = (2 * T₀) ^ 2 := by
  intro T F T₀ S
  have hJF : tateSeriesJacobian F = 2 * T := by
    rw [tateSeriesJacobian_fin_one]
    simp [F, T, two_mul]
  have hexp :
      explicitInverse (2 : ℚ_[2]) F 1 1 =
        S * (2 * T₀) - algebraMap ℚ_[2] (tateSeries 2 ℚ_[2]) 2 := by
    have hlast := explicitInverse_last (2 : ℚ_[2]) F 1
    rw [hJF, map_mul, map_ofNat] at hlast
    simpa [Fin.last, T, T₀, S, pow_one] using hlast
  have hJG : tateSeriesJacobian (explicitInverse (2 : ℚ_[2]) F 1) = (2 * T₀) ^ 2 := by
    rw [tateSeriesJacobian_explicitInverse, hJF, map_mul, map_ofNat]
    simp [T, T₀]
  exact ⟨hJF, hexp, hJG⟩

-- The same quadratic polynomial `F = ![T² - 5]` over `(ℚ_[2], ℤ_[2])` defines a genuine
-- `StandardEtalePresentation` of its quotient Huber pair at scale `ϖ = 2` and exponent `k = 1`,
-- since `2 · (2 T)⁻¹ = (1 / 5) T ∈ Q⁺` even though `2` divides `2 T` in `ℤ_[2]⟨T⟩`.
example :
    let P₂ := Pair.powerBounded ℚ_[2]
    let T : tateSeries 1 ℚ_[2] := tateSeries.X 1 ℚ_[2] 0
    let F : Fin 1 → tateSeries 1 ℚ_[2] := ![T ^ 2 - algebraMap ℚ_[2] (tateSeries 1 ℚ_[2]) 5]
    ∃ Q : StandardEtalePresentation P₂ 2
        ((P₂.weighted (k := 1) isWeightFamily_one_weight).quotient
          (Ideal.span (Set.range F)).closure),
      Q.N = 1 ∧ Q.k = 1 := by
  intro P₂ T F
  have hJF : tateSeriesJacobian F = 2 * T := by
    rw [tateSeriesJacobian_fin_one]; simp [F, T, two_mul]
  have h5_mem : (5 : ℚ_[2]) ∈ P₂.plus := by
    rw [Pair.powerBounded_plus, mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one]
    exact_mod_cast _root_.Padic.norm_int_le_one (p := 2) 5
  have h5inv_mem : (5⁻¹ : ℚ_[2]) ∈ P₂.plus := by
    rw [Pair.powerBounded_plus, mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one, norm_inv]
    have hnorm5 : ‖(5 : ℚ_[2])‖ = 1 := by
      simpa using (_root_.Padic.norm_natCast_eq_one_iff (p := 2) (n := 5)).mpr (by decide)
    simp [hnorm5]
  have hF_plus : ∀ i, F i ∈ tateSeriesPlus 1 ℚ_[2] P₂.plus := fun i ↦ by
    fin_cases i
    exact sub_mem (pow_mem (tateSeries.X_mem_tateSeriesPlus P₂.plus 0) 2)
      (algebraMap_mem_tateSeriesPlus_iff.mpr h5_mem)
  let K : Ideal (tateSeries 1 ℚ_[2]) := (Ideal.span (Set.range F)).closure
  let q : tateSeries 1 ℚ_[2] →+* tateSeries 1 ℚ_[2] ⧸ K := Ideal.Quotient.mk K
  have hTsq : q T ^ 2 = algebraMap ℚ_[2] (tateSeries 1 ℚ_[2] ⧸ K) 5 := by
    have hF0 : q (F 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr <| by
      rw [← SetLike.mem_coe, Ideal.coe_closure]; exact subset_closure (Ideal.subset_span ⟨0, rfl⟩)
    dsimp only [F, Matrix.cons_val_zero] at hF0; rwa [map_sub, map_pow, sub_eq_zero] at hF0
  let invJ : tateSeries 1 ℚ_[2] ⧸ K :=
    algebraMap ℚ_[2] (tateSeries 1 ℚ_[2] ⧸ K) (10⁻¹ : ℚ_[2]) * q T
  have hunit_mul : q (2 * T) * invJ = 1 := by
    have hstep : q (2 * T) * invJ =
        algebraMap ℚ_[2] (tateSeries 1 ℚ_[2] ⧸ K) (2 * 10⁻¹ : ℚ_[2]) * q T ^ 2 := by
      simp only [invJ, map_mul, map_ofNat]; ring
    rw [hstep, hTsq, ← map_mul]; norm_num
  let u : (tateSeries 1 ℚ_[2] ⧸ K)ˣ :=
    ⟨q (2 * T), invJ, hunit_mul, by rw [mul_comm]; exact hunit_mul⟩
  have hbound :
      algebraMap ℚ_[2] (tateSeries 1 ℚ_[2] ⧸ K) ((2 : ℚ_[2]) ^ 1) * ↑u⁻¹ ∈
        ((P₂.weighted (k := 1) isWeightFamily_one_weight).quotient K).plus := by
    have heq : algebraMap ℚ_[2] (tateSeries 1 ℚ_[2] ⧸ K) ((2 : ℚ_[2]) ^ 1) * ↑u⁻¹ =
        q (algebraMap ℚ_[2] (tateSeries 1 ℚ_[2]) (5⁻¹ : ℚ_[2]) * T) := by
      change algebraMap ℚ_[2] _ ((2 : ℚ_[2]) ^ 1) * (algebraMap ℚ_[2] _ (10⁻¹ : ℚ_[2]) * q T) = _
      rw [pow_one, ← mul_assoc, ← map_mul, map_mul q, show (2 * 10⁻¹ : ℚ_[2]) = 5⁻¹ by norm_num]
      rfl
    rw [heq]
    have hmem : algebraMap ℚ_[2] (tateSeries 1 ℚ_[2]) (5⁻¹ : ℚ_[2]) * T ∈
        tateSeriesPlus 1 ℚ_[2] P₂.plus :=
      mul_mem (algebraMap_mem_tateSeriesPlus_iff.mpr h5inv_mem)
        (tateSeries.X_mem_tateSeriesPlus P₂.plus 0)
    simpa only [Pair.Hom.toRingHom_quotientHom] using
      (Pair.quotientHom (P₂.weighted (k := 1) isWeightFamily_one_weight) K).map_mem_plus _
        ((P₂.weighted_plus_eq_tateSeriesPlus 1).symm ▸ hmem)
  exact ⟨StandardEtalePresentation.ofQuotient P₂ (Padic.isPseudoUniformizer_p (p := 2))
    F hF_plus 1 ⟨u, hJF ▸ rfl, hbound⟩, rfl, rfl⟩

end DyadicQuadratic

/-! ### Characteristic-`p` inseparability vs. Artin–Schreier and idempotent presentations -/

section CharacteristicPAndIdempotent

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsTateRing A] [CompleteSpace A] [T2Space A]

-- In characteristic `p`, Frobenius `F = ![T ^ p - a]` has identically zero Jacobian determinant,
-- obstructing any standard étale presentation with equation `F` onto a nontrivial target `C`.
example {p : ℕ} [Fact p.Prime] [CharP A p] (Aplus : Pair A) (ϖ a : A)
    {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    [Algebra A C] [Nontrivial C] (Cplus : Pair C) :
    let T : tateSeries 1 A := tateSeries.X 1 A 0
    let F : Fin 1 → tateSeries 1 A := ![T ^ p - algebraMap A (tateSeries 1 A) a]
    tateSeriesJacobian F = 0 ∧
      ¬ ∃ P : StandardEtalePresentation Aplus ϖ Cplus, P.N = 1 ∧ HEq P.F F := by
  intro T F
  have hp0 : (p : tateSeries 1 A) = 0 := by
    rw [← map_natCast (algebraMap A (tateSeries 1 A)), CharP.cast_eq_zero, map_zero]
  have hJ : tateSeriesJacobian F = 0 := by
    rw [tateSeriesJacobian_fin_one]
    simp [F, T, hp0]
  refine ⟨hJ, ?_⟩
  rintro ⟨P, hN, hF⟩
  rcases P with ⟨hϖ, NP, FP, hFP, kP, πP, hquot, hker, hplus, hunit⟩
  dsimp only at hN hF
  subst hN
  cases eq_of_heq hF
  let P' : StandardEtalePresentation Aplus ϖ Cplus :=
    ⟨hϖ, 1, F, hFP, kP, πP, hquot, hker, hplus, hunit⟩
  have hunit0 : IsUnit (πP (tateSeriesJacobian F)) := P'.isUnit_π_jacobian
  rw [hJ, map_zero] at hunit0
  exact not_isUnit_zero hunit0

-- In contrast, the Artin–Schreier polynomial `F = ![T ^ p - T - u]` (`u ∈ A⁺`) in characteristic
-- `p` has Jacobian `-1` and defines a standard étale presentation with `N = 1` and `k = 0`.
example {p : ℕ} [Fact p.Prime] [CharP A p] (Aplus : Pair A) {ϖ u : A}
    (hϖ : IsPseudoUniformizer ϖ) (hu : u ∈ Aplus.plus) :
    let T : tateSeries 1 A := tateSeries.X 1 A 0
    let F : Fin 1 → tateSeries 1 A := ![T ^ p - T - algebraMap A (tateSeries 1 A) u]
    tateSeriesJacobian F = -1 ∧
      ∃ P : StandardEtalePresentation Aplus ϖ
          ((Aplus.weighted (k := 1) isWeightFamily_one_weight).quotient
            (Ideal.span (Set.range F)).closure),
        P.N = 1 ∧ P.k = 0 := by
  intro T F
  have hp0 : (p : tateSeries 1 A) = 0 := by
    rw [← map_natCast (algebraMap A (tateSeries 1 A)), CharP.cast_eq_zero, map_zero]
  have hJ : tateSeriesJacobian F = -1 := by
    rw [tateSeriesJacobian_fin_one]
    simp [F, T, hp0]
  refine ⟨hJ, ?_⟩
  have hF_plus : ∀ i, F i ∈ tateSeriesPlus 1 A Aplus.plus := fun i ↦ by
    fin_cases i
    exact sub_mem (sub_mem (pow_mem (tateSeries.X_mem_tateSeriesPlus Aplus.plus 0) p)
      (tateSeries.X_mem_tateSeriesPlus Aplus.plus 0))
      (algebraMap_mem_tateSeriesPlus_iff.mpr hu)
  let v : (tateSeries 1 A ⧸ (Ideal.span (Set.range F)).closure)ˣ := ⟨-1, -1, by ring, by ring⟩
  refine ⟨StandardEtalePresentation.ofQuotient Aplus hϖ F hF_plus 0
    ⟨v, by rw [hJ, map_neg, map_one], ?_⟩, rfl, rfl⟩
  rw [pow_zero, map_one, one_mul]
  exact neg_mem (one_mem _)

-- Over any complete Hausdorff Tate pair `(A, A⁺)`, the idempotent equation `F = ![T² - T]` has
-- Jacobian `2 T - 1` satisfying `(2 T - 1)² = 1 + 4 (T² - T)`, giving a standard étale
-- presentation of its quotient Huber pair with `N = 1` and `k = 0`.
example (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) :
    let T : tateSeries 1 A := tateSeries.X 1 A 0
    let F : Fin 1 → tateSeries 1 A := ![T ^ 2 - T]
    tateSeriesJacobian F = 2 * T - 1 ∧
      ∃ P : StandardEtalePresentation Aplus ϖ
          ((Aplus.weighted (k := 1) isWeightFamily_one_weight).quotient
            (Ideal.span (Set.range F)).closure),
        P.N = 1 ∧ P.k = 0 := by
  intro T F
  have hJ : tateSeriesJacobian F = 2 * T - 1 := by
    rw [tateSeriesJacobian_fin_one]
    simp [F, T, two_mul]
  refine ⟨hJ, ?_⟩
  have hF_plus : ∀ i, F i ∈ tateSeriesPlus 1 A Aplus.plus := fun i ↦ by
    fin_cases i
    exact sub_mem (pow_mem (tateSeries.X_mem_tateSeriesPlus Aplus.plus 0) 2)
      (tateSeries.X_mem_tateSeriesPlus Aplus.plus 0)
  let K : Ideal (tateSeries 1 A) := (Ideal.span (Set.range F)).closure
  let q : tateSeries 1 A →+* tateSeries 1 A ⧸ K := Ideal.Quotient.mk K
  have hF0 : q (T ^ 2 - T) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, ← SetLike.mem_coe, Ideal.coe_closure]
    exact subset_closure (Ideal.subset_span ⟨0, rfl⟩)
  have hsq : q (2 * T - 1) * q (2 * T - 1) = 1 := by
    have hid : (2 * T - 1) * (2 * T - 1) = 1 + 4 * (T ^ 2 - T) := by ring
    rw [← map_mul, hid, map_add, map_one, map_mul, hF0, mul_zero, add_zero]
  let u : (tateSeries 1 A ⧸ K)ˣ := ⟨q (2 * T - 1), q (2 * T - 1), hsq, hsq⟩
  have h2T_mem : 2 * T - 1 ∈ tateSeriesPlus 1 A Aplus.plus :=
    sub_mem (mul_mem (ofNat_mem _ 2) (tateSeries.X_mem_tateSeriesPlus Aplus.plus 0)) (one_mem _)
  have hbound :
      algebraMap A (tateSeries 1 A ⧸ K) (ϖ ^ 0) * ↑u⁻¹ ∈
        ((Aplus.weighted (k := 1) isWeightFamily_one_weight).quotient K).plus := by
    rw [pow_zero, map_one, one_mul]
    change q (2 * T - 1) ∈ _
    simpa only [Pair.Hom.toRingHom_quotientHom] using
      (Pair.quotientHom (Aplus.weighted (k := 1) isWeightFamily_one_weight) K).map_mem_plus _
        ((Aplus.weighted_plus_eq_tateSeriesPlus 1).symm ▸ h2T_mem)
  exact ⟨StandardEtalePresentation.ofQuotient Aplus hϖ F hF_plus 0 ⟨u, hJ ▸ rfl, hbound⟩, rfl, rfl⟩

end CharacteristicPAndIdempotent
