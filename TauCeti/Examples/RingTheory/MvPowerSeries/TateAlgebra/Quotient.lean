/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.ClosedIdeal
public import TauCeti.RingTheory.Huber.Restricted.BoundedLift

/-!
# Topological versus isometric quotients of restricted power series

Concrete checks for `TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Quotient`:

* Rescaling the `p`-adic norm on `ℚ_[p]` by `2` yields an ultrametric normed ring `DoubleNorm ℚ_[p]`
  for which the identity homomorphism `DoubleNorm ℚ_[p] →+* ℚ_[p]` is contractive and has uniformly
  bounded lifts with factor `2`. Thus `restrictedMapQuotientEquiv` is a topological ring isomorphism
  `(DoubleNorm ℚ_[p]){X} ⧸ ker ≃+* ℚ_[p]{X}`, yet it is *not* an isometry: the residue class of `1`
  has quotient Gauss norm at least `2`, while its image `1` in `ℚ_[p]{X}` has Gauss norm `1`.
  Sharp coefficient lifts (`exists_restrictedMap_eq_and_norm_lt`) are therefore genuinely needed for
  the isometric conclusion of `isometry_restrictedMapSharpQuotientEquiv`.
* Over `ℤ_[p]`, every `(p : ℤ_[p]) ^ m` scales norms multiplicatively, so `(p ^ m)` is closed and
  `Ideal.spanSingletonIsRestrictedQuotientEquiv` gives an isometric ring isomorphism
  `ℤ_[p]{X} ⧸ (p ^ m) ≃+* (ℤ_[p] ⧸ (p ^ m)){X}`.
-/

public section

namespace TauCeti.Examples.RestrictedQuotient

open _root_.MvPowerSeries TauCeti.MvPowerSeries

/-- Type synonym carrying twice the norm of `R`, used to separate topological quotient maps of
restricted series from isometric ones. -/
-- The body is exposed because the ring structure below is transferred from `R` along it.
@[expose]
def DoubleNorm (R : Type*) : Type _ := R

/-- Twice the norm of `R` is submultiplicative (`2 * ‖x * y‖ ≤ (2 * ‖x‖) * (2 * ‖y‖)`) and defines
a ring norm on `R`. -/
noncomputable def doubleRingNorm (R : Type*) [NormedRing R] : RingNorm R where
  toFun x := 2 * ‖x‖
  map_zero' := by simp
  neg' x := by simp
  add_le' x y := by
    calc 2 * ‖x + y‖ ≤ 2 * (‖x‖ + ‖y‖) := by gcongr; exact norm_add_le x y
      _ = 2 * ‖x‖ + 2 * ‖y‖ := by ring
  mul_le' x y := by
    calc 2 * ‖x * y‖ ≤ 2 * (‖x‖ * ‖y‖) := by gcongr; exact norm_mul_le x y
      _ ≤ (2 * ‖x‖) * (2 * ‖y‖) := by nlinarith [norm_nonneg x, norm_nonneg y]
  eq_zero_of_map_eq_zero' x hx := norm_eq_zero.mp (by linarith)

noncomputable instance {R : Type*} [NormedRing R] : NormedRing (DoubleNorm R) :=
  (doubleRingNorm R).toNormedRing

/-- The identity ring equivalence `R ≃+* DoubleNorm R`. -/
noncomputable def toDoubleNorm (R : Type*) [NormedRing R] : R ≃+* DoubleNorm R :=
  RingEquiv.refl R

/-- The identity ring homomorphism `DoubleNorm R →+* R`. -/
noncomputable def ofDoubleNorm (R : Type*) [NormedRing R] : DoubleNorm R →+* R :=
  (toDoubleNorm R).symm.toRingHom

/-- Elements of `DoubleNorm R` have twice their norm in `R`. -/
@[simp]
theorem norm_toDoubleNorm {R : Type*} [NormedRing R] (x : R) :
    ‖toDoubleNorm R x‖ = 2 * ‖x‖ := (rfl)

/-- Norms on `DoubleNorm R` equal twice the norms of their images under `ofDoubleNorm`. -/
theorem norm_eq_two_mul_norm_ofDoubleNorm {R : Type*} [NormedRing R] (x : DoubleNorm R) :
    ‖x‖ = 2 * ‖ofDoubleNorm R x‖ := (rfl)

instance {R : Type*} [NormedRing R] [IsUltrametricDist R] : IsUltrametricDist (DoubleNorm R) where
  dist_triangle_max x y z := by
    -- Each distance in `DoubleNorm R` is twice the corresponding distance in `R`.
    have hd (a b : DoubleNorm R) :
        dist a b = 2 * dist (ofDoubleNorm R a) (ofDoubleNorm R b) := by
      rw [dist_eq_norm_neg_add, dist_eq_norm_neg_add, ← map_neg, ← map_add,
        ← norm_eq_two_mul_norm_ofDoubleNorm]
    rw [hd x z, hd x y, hd y z, ← mul_max_of_nonneg _ _ zero_le_two]
    exact mul_le_mul_of_nonneg_left (dist_triangle_max _ _ _) zero_le_two

section Counterexample

/-- `ofDoubleNorm R` is contractive (`‖ofDoubleNorm R a‖ ≤ 1 * ‖a‖`). -/
theorem norm_ofDoubleNorm_le {R : Type*} [NormedRing R] (a : DoubleNorm R) :
    ‖ofDoubleNorm R a‖ ≤ 1 * ‖a‖ := by
  rw [norm_eq_two_mul_norm_ofDoubleNorm]
  linarith [norm_nonneg (ofDoubleNorm R a)]

/-- Every element of `R` lifts to `DoubleNorm R` along `ofDoubleNorm R` with norm at most twice its
norm. -/
theorem exists_ofDoubleNorm_lift {R : Type*} [NormedRing R] (b : R) :
    ∃ a : DoubleNorm R, ofDoubleNorm R a = b ∧ ‖a‖ ≤ 2 * ‖b‖ := by
  refine ⟨toDoubleNorm R b, rfl, ?_⟩
  rw [norm_toDoubleNorm]

variable (p : ℕ) [Fact p.Prime]

-- `ofDoubleNorm ℚ_[p]` is contractive and has uniformly bounded lifts with factor `2`, so
-- `restrictedMapQuotientEquiv` is continuous in both directions, yet it is NOT an isometry.
example :
    Continuous (restrictedMapQuotientEquiv (c := fun _ : Unit ↦ (1 : ℝ))
      (ofDoubleNorm ℚ_[p]) norm_ofDoubleNorm_le exists_ofDoubleNorm_lift) ∧
    Continuous (restrictedMapQuotientEquiv (c := fun _ : Unit ↦ (1 : ℝ))
      (ofDoubleNorm ℚ_[p]) norm_ofDoubleNorm_le exists_ofDoubleNorm_lift).symm ∧
    ¬ Isometry (restrictedMapQuotientEquiv (c := fun _ : Unit ↦ (1 : ℝ))
      (ofDoubleNorm ℚ_[p]) norm_ofDoubleNorm_le exists_ofDoubleNorm_lift) := by
  let K := RingHom.ker (restrictedMap (c := fun _ : Unit ↦ (1 : ℝ))
    (ofDoubleNorm ℚ_[p]) norm_ofDoubleNorm_le)
  set e := restrictedMapQuotientEquiv (c := fun _ : Unit ↦ (1 : ℝ))
    (ofDoubleNorm ℚ_[p]) norm_ofDoubleNorm_le exists_ofDoubleNorm_lift
  refine ⟨continuous_restrictedMapQuotientEquiv _ _ _,
    continuous_restrictedMapQuotientEquiv_symm _ _ _, fun hiso ↦ ?_⟩
  let oneQ : IsRestricted.subring (R := DoubleNorm ℚ_[p]) (fun _ : Unit ↦ (1 : ℝ)) ⧸ K := 1
  have hnorm1 : ‖e oneQ‖ = ‖oneQ‖ := hiso.norm_map_of_map_zero (map_zero e) oneQ
  have he1 : ‖e oneQ‖ = 1 := by
    dsimp only [oneQ]
    rw [map_one, norm_one]
  have hq2 : (2 : ℝ) ≤ ‖oneQ‖ := by
    refine QuotientAddGroup.le_norm_iff.mpr fun g hg ↦ ?_
    have hker : g - 1 ∈ K := Ideal.Quotient.eq.mp hg
    have hinj : Function.Injective (restrictedMap (c := fun _ : Unit ↦ (1 : ℝ))
        (ofDoubleNorm ℚ_[p]) norm_ofDoubleNorm_le) :=
      restrictedMap_injective _ _ (toDoubleNorm ℚ_[p]).symm.injective
    have hg1 : g = 1 := sub_eq_zero.mp (hinj (by rwa [map_zero, ← RingHom.mem_ker]))
    subst hg1
    have h0 := MvPowerSeries.norm_coeff_mul_prod_le
      (1 : IsRestricted.subring (R := DoubleNorm ℚ_[p]) (fun _ : Unit ↦ (1 : ℝ))) 0
    simpa [norm_eq_two_mul_norm_ofDoubleNorm] using h0
  linarith

end Counterexample

section PadicIntQuotient

variable (p : ℕ) [Fact p.Prime] (m : ℕ)

-- Over `ℤ_[p]`, `(p : ℤ_[p]) ^ m` scales norms multiplicatively and generates a closed ideal, so
-- `ℤ_[p]{X} ⧸ (p ^ m) ≃+* (ℤ_[p] ⧸ (p ^ m)){X}` is an isometric ring isomorphism.
example :
    letI : IsClosed (Ideal.span ({(p : ℤ_[p]) ^ m} : Set ℤ_[p]) : Set ℤ_[p]) :=
      Ideal.isClosed_span_singleton_of_norm_mul ((p : ℤ_[p]) ^ m) fun a ↦ norm_mul a _
    ∃ e : (IsRestricted.subring (R := ℤ_[p]) (fun _ : Unit ↦ (1 : ℝ)) ⧸
        Ideal.span (Set.singleton
          (algebraMap ℤ_[p] (IsRestricted.subring (R := ℤ_[p]) (fun _ : Unit ↦ (1 : ℝ)))
            ((p : ℤ_[p]) ^ m)))) ≃+*
      IsRestricted.subring (R := ℤ_[p] ⧸ Ideal.span ({(p : ℤ_[p]) ^ m} : Set ℤ_[p]))
        (fun _ : Unit ↦ (1 : ℝ)),
      Isometry e ∧ Isometry e.symm := by
  let : IsClosed (Ideal.span ({(p : ℤ_[p]) ^ m} : Set ℤ_[p]) : Set ℤ_[p]) :=
    Ideal.isClosed_span_singleton_of_norm_mul ((p : ℤ_[p]) ^ m) fun a ↦ norm_mul a _
  exact ⟨Ideal.spanSingletonIsRestrictedQuotientEquiv ((p : ℤ_[p]) ^ m) (fun a ↦ norm_mul a _),
    Ideal.isometry_spanSingletonIsRestrictedQuotientEquiv _ _,
    Ideal.isometry_spanSingletonIsRestrictedQuotientEquiv_symm _ _⟩

end PadicIntQuotient

end TauCeti.Examples.RestrictedQuotient
