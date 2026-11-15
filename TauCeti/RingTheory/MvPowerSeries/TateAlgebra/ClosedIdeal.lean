/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Quotient
public import TauCeti.Analysis.Normed.Group.Quotient

import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner

/-!
# Closed ideals and residue Gauss norms of Tate algebras

Every left ideal `I` of a restricted power-series algebra `K⟨X₁/c₁, …, Xₙ/cₙ⟩` in finitely many
variables over a complete ultrametric division ring `K` is closed for the Gauss norm, and in fact
*strictly closed*: every residue class in `K⟨X₁/c₁, …, Xₙ/cₙ⟩ ⧸ I` has a representative attaining
its quotient Gauss norm (`Ideal.exists_mk_eq_and_norm_eq_isRestricted_subring`), even when `K` is
trivially normed or not spherically complete. At unit polyradius, every quotient norm is the norm
of a scalar in `K` (`Ideal.exists_norm_eq_norm_quotient_isRestricted_subring`).

When `K` is commutative, `isClosed_ideal_isRestrictedSubring` makes Mathlib's
`Ideal.Quotient.normedCommRing` apply to every quotient of a Tate algebra. Together with
`Ideal.Quotient.normedAlgebra`, `Submodule.Quotient.completeSpace` and
`Submodule.Quotient.instIsUltrametricDist`, the residue Gauss norm on such a quotient is a complete
ultrametric algebra norm whose values at unit polyradius lie in `‖K‖`. Moreover, strict finite
generators and exact quotient-norm representatives combine with the restricted-series quotient
results of `TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Quotient` to identify the extended ideal
`I · T{Y/d}` in any further family of restricted variables with the series having coefficients in
`I`, give exact norm-attaining lifts along `T{Y/d} →+* (T ⧸ I){Y/d}`, and make
`T{Y/d} ⧸ (I · T{Y/d}) ≃+* (T ⧸ I){Y/d}` an isometry (`Ideal.tateQuotientIsRestrictedEquiv`).

## Main results

* `TauCeti.MvPowerSeries.isClosed_ideal_isRestrictedSubring`: every left ideal of a finite-variable
  Tate algebra over a complete ultrametric division ring is closed.
* `Ideal.exists_norm_sub_eq_norm_mk_isRestricted_subring` and
  `Ideal.exists_mk_eq_and_norm_eq_isRestricted_subring`: every coset has a least-norm element, so
  every residue class has a representative attaining its quotient norm.
* `Ideal.exists_norm_eq_norm_quotient_isRestricted_subring`: at unit polyradius, every quotient
  Gauss norm is the norm of an element of `K`.
* `Ideal.mem_map_algebraMap_isRestricted_subring_iff` and
  `Ideal.ker_restrictedQuotientMk_isRestricted_subring`: for an ideal `I` of a commutative Tate
  algebra `T = K⟨X/c⟩`, `I · T{Y/d}` is the ideal of restricted series with coefficients in `I`.
* `Ideal.exists_restrictedQuotientMk_eq_and_norm_eq_isRestricted_subring` and
  `Ideal.tateQuotientIsRestrictedEquiv`: exact Gauss-norm lifts and the isometric isomorphism
  `T{Y/d} ⧸ (I · T{Y/d}) ≃+* (T ⧸ I){Y/d}`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§5.2.6–5.2.7 and §6.1.1, Proposition 2.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

section DivisionRing

variable {K : Type*} [NormedDivisionRing K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [Finite σ] {c : σ → ℝ} [∀ i, Fact (0 < c i)]

/-- Every left ideal of a finite-variable restricted power-series algebra over a complete
ultrametric division ring is closed for the Gauss norm. -/
instance isClosed_ideal_isRestrictedSubring (I : Ideal (IsRestricted.subring (R := K) c)) :
    IsClosed (I : Set (IsRestricted.subring (R := K) c)) :=
  isClosed_ideal_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    (fun x y hx ↦ ⟨y * x⁻¹, 0, by rw [add_zero, inv_mul_cancel_right₀ hx], by simp, Or.inl rfl⟩) I

/-- **Least-norm coset adjustment for ideals of Tate algebras.** For every series `f` and left ideal
`I`, some `g ∈ I` makes `‖f - g‖` equal to the quotient Gauss norm of `f` modulo `I`. -/
theorem _root_.Ideal.exists_norm_sub_eq_norm_mk_isRestricted_subring
    (I : Ideal (IsRestricted.subring (R := K) c)) (f : IsRestricted.subring (R := K) c) :
    ∃ g ∈ I, ‖f - g‖ = ‖(Submodule.Quotient.mk f : IsRestricted.subring (R := K) c ⧸ I)‖ := by
  obtain ⟨g, hg, hle⟩ := I.exists_norm_sub_le_isRestricted_subring f
  exact ⟨g, hg, (Submodule.Quotient.norm_sub_eq_norm_mk_iff hg).mpr hle⟩

/-- **Exact quotient-norm representatives for ideals of Tate algebras** ([Bosch, Güntzer, Remmert,
*Non-Archimedean Analysis*][bosch-guntzer-remmert], §5.2.7, Proposition 2). Every class in
`K⟨X/c⟩ ⧸ I` is represented by a restricted series of the same norm. -/
theorem _root_.Ideal.exists_mk_eq_and_norm_eq_isRestricted_subring
    (I : Ideal (IsRestricted.subring (R := K) c)) (q : IsRestricted.subring (R := K) c ⧸ I) :
    ∃ f : IsRestricted.subring (R := K) c, Submodule.Quotient.mk f = q ∧ ‖f‖ = ‖q‖ :=
  Submodule.Quotient.exists_mk_eq_and_norm_eq_iff.mpr I.exists_norm_sub_le_isRestricted_subring q

/-- **Values of the residue Gauss norm at unit polyradius** ([Bosch, Güntzer, Remmert,
*Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.1, Proposition 2). Every residue class in
`K⟨X⟩ ⧸ I` has quotient Gauss norm equal to the norm of a scalar in `K`. -/
theorem _root_.Ideal.exists_norm_eq_norm_quotient_isRestricted_subring
    (I : Ideal (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)))
    (q : IsRestricted.subring (R := K) (fun _ : σ ↦ 1) ⧸ I) :
    ∃ a : K, ‖a‖ = ‖q‖ := by
  obtain ⟨f, -, hfq⟩ := I.exists_mk_eq_and_norm_eq_isRestricted_subring q
  obtain ⟨t, ht⟩ := exists_norm_coeff_eq_norm f
  exact ⟨coeff t (f : MvPowerSeries σ K), ht.trans hfq⟩

end DivisionRing

section ExtendedIdeal

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [Finite σ] {c : σ → ℝ} [∀ i, Fact (0 < c i)]
  {τ : Type*} {d : τ → ℝ}

/-- Every ideal `I` of a commutative Tate algebra `T = K⟨X/c⟩` admits a finite subset `F ⊆ I` and a
constant `L` such that every `y ∈ I` has a representation `y = ∑ x ∈ F, a x * x` with
`‖a x‖ ≤ L * ‖y‖`, deduced from the strict division bound `‖a x‖ * ‖x‖ ≤ ‖y‖` over nonzero
generators. -/
theorem _root_.Ideal.exists_finset_sum_mul_norm_le_isRestricted_subring
    (I : Ideal (IsRestricted.subring (R := K) c)) :
    ∃ F : Finset (IsRestricted.subring (R := K) c), (∀ x ∈ F, x ∈ I) ∧
      ∃ L : ℝ, ∀ y ∈ I,
        ∃ a : IsRestricted.subring (R := K) c → IsRestricted.subring (R := K) c,
          y = ∑ x ∈ F, a x * x ∧ ∀ x ∈ F, ‖a x‖ ≤ L * ‖y‖ := by
  obtain ⟨F, hFI, hF⟩ := I.exists_finset_eq_sum_mul_isRestricted_subring
  refine ⟨F, fun x hx ↦ (hFI x hx).1, ∑ z ∈ F, ‖z‖⁻¹, fun y hy ↦ ?_⟩
  obtain ⟨a, hsum, hnorm⟩ := hF y hy
  refine ⟨a, hsum, fun x hx ↦ ?_⟩
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr (hFI x hx).2
  calc ‖a x‖ = ‖a x‖ * ‖x‖ * ‖x‖⁻¹ := (mul_inv_cancel_right₀ hpos.ne' _).symm
    _ ≤ ‖y‖ * ‖x‖⁻¹ := mul_le_mul_of_nonneg_right (hnorm x hx) (inv_nonneg.mpr hpos.le)
    _ = ‖x‖⁻¹ * ‖y‖ := mul_comm _ _
    _ ≤ (∑ z ∈ F, ‖z‖⁻¹) * ‖y‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun z _ ↦ inv_nonneg.mpr (norm_nonneg z)) hx) (norm_nonneg y)

/-- **Extended ideals of Tate algebras in further restricted variables.** For an ideal `I` of a
commutative Tate algebra `T = K⟨X/c⟩`, a restricted series in `T{Y/d}` lies in `I · T{Y/d}` if and
only if every coefficient lies in `I`. Neither finiteness of `τ` nor positivity of `d` is needed. -/
theorem _root_.Ideal.mem_map_algebraMap_isRestricted_subring_iff
    (I : Ideal (IsRestricted.subring (R := K) c))
    {f : IsRestricted.subring (R := IsRestricted.subring (R := K) c) d} :
    f ∈ I.map (algebraMap _ (IsRestricted.subring (R := IsRestricted.subring (R := K) c) d)) ↔
      ∀ t, coeff t (f : MvPowerSeries τ (IsRestricted.subring (R := K) c)) ∈ I := by
  obtain ⟨F, hFI, L, hgen⟩ := I.exists_finset_sum_mul_norm_le_isRestricted_subring
  exact Ideal.mem_map_algebraMap_isRestricted_subring_iff_of_exists_finset_sum_mul I hFI hgen

/-- For an ideal `I` of `T = K⟨X/c⟩`, the kernel of coefficient reduction
`T{Y/d} →+* (T ⧸ I){Y/d}` is the extended ideal `I · T{Y/d}`. -/
theorem _root_.Ideal.ker_restrictedQuotientMk_isRestricted_subring
    (I : Ideal (IsRestricted.subring (R := K) c)) :
    RingHom.ker (I.restrictedQuotientMk (c := d)) =
      I.map (algebraMap _ (IsRestricted.subring (R := IsRestricted.subring (R := K) c) d)) := by
  ext f
  rw [I.mem_ker_restrictedQuotientMk, I.mem_map_algebraMap_isRestricted_subring_iff]

/-- **Ring isomorphism `T{Y/d} ⧸ (I · T{Y/d}) ≃+* (T ⧸ I){Y/d}`** for an ideal `I` of a commutative
Tate algebra `T = K⟨X/c⟩` and any family of radii `d`; at positive radii `d` it is an isometry in
both directions (`Ideal.isometry_tateQuotientIsRestrictedEquiv` and `_symm`). -/
noncomputable def _root_.Ideal.tateQuotientIsRestrictedEquiv
    (I : Ideal (IsRestricted.subring (R := K) c)) :
    (IsRestricted.subring (R := IsRestricted.subring (R := K) c) d ⧸
        I.map (algebraMap _ (IsRestricted.subring (R := IsRestricted.subring (R := K) c) d))) ≃+*
      IsRestricted.subring (R := IsRestricted.subring (R := K) c ⧸ I) d :=
  (Ideal.quotEquivOfEq I.ker_restrictedQuotientMk_isRestricted_subring.symm).trans
    I.restrictedQuotientMkEquiv

/-- `Ideal.tateQuotientIsRestrictedEquiv` acts as `Ideal.restrictedQuotientMk` on residue
classes. -/
@[simp]
theorem _root_.Ideal.tateQuotientIsRestrictedEquiv_mk
    (I : Ideal (IsRestricted.subring (R := K) c))
    (f : IsRestricted.subring (R := IsRestricted.subring (R := K) c) d) :
    I.tateQuotientIsRestrictedEquiv (Ideal.Quotient.mk _ f) = I.restrictedQuotientMk f := by
  simp only [Ideal.tateQuotientIsRestrictedEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, I.restrictedQuotientMkEquiv_mk]

/-- The inverse of `Ideal.tateQuotientIsRestrictedEquiv` sends `I.restrictedQuotientMk f` to the
class of `f` modulo `I · T{Y/d}`. -/
@[simp]
theorem _root_.Ideal.tateQuotientIsRestrictedEquiv_symm_restrictedQuotientMk
    (I : Ideal (IsRestricted.subring (R := K) c))
    (f : IsRestricted.subring (R := IsRestricted.subring (R := K) c) d) :
    I.tateQuotientIsRestrictedEquiv.symm (I.restrictedQuotientMk f) = Ideal.Quotient.mk _ f := by
  simp [Ideal.tateQuotientIsRestrictedEquiv]

variable [∀ j, Fact (0 < d j)]

/-- For any ideal `I` of `T = K⟨X/c⟩`, the extended ideal `I · T{Y/d}` is closed in `T{Y/d}` at
positive radii `d`. -/
instance isClosed_map_algebraMap_isRestrictedSubring
    (I : Ideal (IsRestricted.subring (R := K) c)) :
    IsClosed (I.map (algebraMap _
      (IsRestricted.subring (R := IsRestricted.subring (R := K) c) d)) :
      Set (IsRestricted.subring (R := IsRestricted.subring (R := K) c) d)) := by
  obtain ⟨F, hFI, L, hgen⟩ := I.exists_finset_sum_mul_norm_le_isRestricted_subring
  exact Ideal.isClosed_map_algebraMap_isRestricted_subring_of_exists_finset_sum_mul I hFI hgen

/-- **Exact Gauss-norm lifts over quotients of Tate algebras.** Because every residue class in
`T ⧸ I` has a representative attaining its quotient norm, every restricted series in `(T ⧸ I){Y/d}`
lifts to `T{Y/d}` with exact equality of Gauss norms. -/
theorem _root_.Ideal.exists_restrictedQuotientMk_eq_and_norm_eq_isRestricted_subring
    (I : Ideal (IsRestricted.subring (R := K) c))
    (g : IsRestricted.subring (R := IsRestricted.subring (R := K) c ⧸ I) d) :
    ∃ f, I.restrictedQuotientMk f = g ∧ ‖f‖ = ‖g‖ :=
  I.exists_restrictedQuotientMk_eq_and_norm_eq (fun q ↦ by
    obtain ⟨a, ha, hnorm⟩ := I.exists_mk_eq_and_norm_eq_isRestricted_subring q
    exact ⟨a, ha, hnorm.le⟩) g

/-- `Ideal.tateQuotientIsRestrictedEquiv` preserves norms at positive radii `d`. -/
theorem _root_.Ideal.norm_tateQuotientIsRestrictedEquiv
    (I : Ideal (IsRestricted.subring (R := K) c))
    (x : IsRestricted.subring (R := IsRestricted.subring (R := K) c) d ⧸
      I.map (algebraMap _ (IsRestricted.subring (R := IsRestricted.subring (R := K) c) d))) :
    ‖I.tateQuotientIsRestrictedEquiv x‖ = ‖x‖ := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨F, hFI, L, hgen⟩ := I.exists_finset_sum_mul_norm_le_isRestricted_subring
  rw [I.tateQuotientIsRestrictedEquiv_mk,
    ← I.isRestrictedQuotientEquivQuotientIsRestricted_mk hFI hgen,
    I.norm_isRestrictedQuotientEquivQuotientIsRestricted hFI hgen]

/-- `Ideal.tateQuotientIsRestrictedEquiv` is an isometry at positive radii `d`. -/
theorem _root_.Ideal.isometry_tateQuotientIsRestrictedEquiv
    (I : Ideal (IsRestricted.subring (R := K) c)) :
    Isometry (I.tateQuotientIsRestrictedEquiv (d := d)) :=
  AddMonoidHomClass.isometry_of_norm _ I.norm_tateQuotientIsRestrictedEquiv

/-- The inverse of `Ideal.tateQuotientIsRestrictedEquiv` is an isometry at positive radii `d`. -/
theorem _root_.Ideal.isometry_tateQuotientIsRestrictedEquiv_symm
    (I : Ideal (IsRestricted.subring (R := K) c)) :
    Isometry (I.tateQuotientIsRestrictedEquiv (d := d)).symm :=
  AddMonoidHomClass.isometry_of_norm _ fun g ↦ by
    obtain ⟨x, rfl⟩ := (I.tateQuotientIsRestrictedEquiv (d := d)).surjective g
    rw [RingEquiv.symm_apply_apply, I.norm_tateQuotientIsRestrictedEquiv]

end ExtendedIdeal

end TauCeti.MvPowerSeries
