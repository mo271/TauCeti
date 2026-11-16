/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Maximal.Topology
public import TauCeti.RingTheory.Affinoid.SupSeminorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

import TauCeti.RingTheory.Affinoid.MaximumModulus
import TauCeti.RingTheory.Affinoid.QuotientNorm
import TauCeti.RingTheory.Affinoid.Restricted
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Radius
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Units

/-!
# Closed annuli and sharpness examples for the affinoid supremum seminorm

This file establishes three concrete examples witnessing the sharpness of the hypotheses in the
theory of the affinoid supremum seminorm (`TauCeti.RingTheory.Affinoid.BanachFunctionAlgebra` and
`TauCeti.RingTheory.Affinoid.Multiplicative`):

1. **Nonreduced nilpotent kernel**
   (`TauCeti.mk_X_ne_zero_and_supSeminorm_eq_zero_quotient_span_X_sq`):
   in `K⟨T⟩ ⧸ (T ^ 2)` the residue class of `T` is nonzero with `supSeminorm K = 0`, showing that
   reducedness is necessary for `supSeminorm K` to be a norm.
2. **Closed annulus** (`TauCeti.isDomain_quotient_annulusIdeal`,
   `TauCeti.supSeminorm_mk_X_zero_quotient_annulusIdeal`,
   `TauCeti.supSeminorm_mk_X_one_quotient_annulusIdeal`,
   `TauCeti.supSeminorm_mk_X_mul_X_quotient_annulusIdeal`): for `0 < ‖c‖ < 1`, the quotient
   `K⟨X_0, X_1⟩ ⧸ (X_0 X_1 - c)` representing the closed annulus `‖c‖ ≤ |T| ≤ 1` is an integral
   domain, yet `|X_0|sup = |X_1|sup = 1` while `|X_0 X_1|sup = ‖c‖ < 1`. Thus being a reduced
   integral domain does not suffice for `supSeminorm K` to be multiplicative.
3. **Disconnected maximum locus** (`TauCeti.not_dense_setOf_pointNorm_eq_supSeminorm_prod`): on the
   product algebra `K × K`, the maximum locus of `(1, 0)` in `MaximalSpectrum (K × K)` is a
   singleton in a two-point `T₁` space and therefore not Zariski dense, showing that the Tate
   maximum-locus density theorem does not extend to arbitrary affinoid algebras.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§6.1.4 and 6.2.1–6.2.4.
-/

public section

open _root_.MvPowerSeries TauCeti.MvPowerSeries

namespace TauCeti

section DualNumbers

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- In the nonreduced affinoid algebra `K⟨T⟩ ⧸ (T ^ 2)` of dual numbers over `K⟨T⟩`, the residue
class of `T` is nonzero and nilpotent, so its supremum seminorm vanishes despite the element being
nonzero. -/
theorem mk_X_ne_zero_and_supSeminorm_eq_zero_quotient_span_X_sq :
    let t : IsRestricted.subring (R := K) (fun _ : Fin 1 ↦ 1) := ⟨X 0, isRestricted_X _ 0⟩
    let ε := Ideal.Quotient.mk (Ideal.span {t ^ 2}) t
    ε ≠ 0 ∧ ε ^ 2 = 0 ∧ supSeminorm K ε = 0 := by
  intro t ε
  have hsq : ε ^ 2 = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  refine ⟨?_, hsq, (isAffinoidAlgebra_tate.quotient _).supSeminorm_eq_zero_iff.mpr ⟨2, hsq⟩⟩
  intro h0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
  obtain ⟨g, hg⟩ := h0
  have hcoeff := congrArg (fun f : IsRestricted.subring (R := K) (fun _ : Fin 1 ↦ 1) ↦
    coeff (Finsupp.single 0 1) (f : MvPowerSeries (Fin 1) K)) hg
  have hleft : coeff (Finsupp.single 0 1) (t : MvPowerSeries (Fin 1) K) = 1 := by
    simp [t, coeff_X]
  have hright :
      coeff (Finsupp.single 0 1) ((t ^ 2 * g : _) : MvPowerSeries (Fin 1) K) = 0 := by
    change coeff (Finsupp.single 0 1) (X 0 ^ 2 * (g : MvPowerSeries (Fin 1) K)) = 0
    have hX2 : (X (0 : Fin 1) ^ 2 : MvPowerSeries (Fin 1) K) = monomial (Finsupp.single 0 2) 1 := by
      rw [sq, X, monomial_mul_monomial, mul_one, ← Finsupp.single_add]
    rw [hX2, coeff_mul]
    refine Finset.sum_eq_zero fun p hp ↦ ?_
    have hp_le : p.1 0 ≤ 1 := by
      have hsum : p.1 0 + p.2 0 = 1 := by
        simpa using congrArg (fun ν : Fin 1 →₀ ℕ ↦ ν 0) (Finset.mem_antidiagonal.mp hp)
      omega
    have hne : p.1 ≠ Finsupp.single 0 2 := fun h ↦ by
      have : p.1 0 = 2 := by simp [h]
      omega
    rw [coeff_monomial, ite_eq_right_iff.mpr fun h ↦ absurd h hne, zero_mul]
  exact one_ne_zero (hleft.symm.trans (hcoeff.trans hright))

end DualNumbers

section Annulus

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The element `X_0 * X_1 - c` in the two-variable Tate algebra `K⟨X_0, X_1⟩`. -/
noncomputable abbrev annulusGenerator (c : K) :
    IsRestricted.subring (R := K) (fun _ : Fin 2 ↦ 1) :=
  ⟨X 0, isRestricted_X _ 0⟩ * ⟨X 1, isRestricted_X _ 1⟩ - algebraMap K _ c

/-- The principal ideal `(X_0 * X_1 - c)` defining the closed annulus `‖c‖ ≤ |T| ≤ 1` inside
`K⟨X_0, X_1⟩`. -/
noncomputable abbrev annulusIdeal (c : K) :
    Ideal (IsRestricted.subring (R := K) (fun _ : Fin 2 ↦ 1)) :=
  Ideal.span {annulusGenerator c}

omit [CompleteSpace K] in
private theorem coeff_annulusGenerator (c : K) (μ : Fin 2 →₀ ℕ) :
    coeff μ (annulusGenerator c : MvPowerSeries (Fin 2) K) =
      (if μ = Finsupp.single 0 1 + Finsupp.single 1 1 then 1 else 0) -
        if μ = 0 then c else 0 := by
  change coeff μ (X (0 : Fin 2) * X 1 - MvPowerSeries.C c) = _
  have hXY : (X (0 : Fin 2) * X 1 : MvPowerSeries (Fin 2) K) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [X, X, monomial_mul_monomial, mul_one]
  rw [map_sub, hXY, coeff_monomial, coeff_C]

omit [CompleteSpace K] in
private theorem norm_annulusGenerator {c : K} (hc : ‖c‖ ≤ 1) :
    ‖annulusGenerator c‖ = 1 := by
  have hne : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1) ≠ 0 := fun h ↦ by
    simpa using congrArg (fun μ : Fin 2 →₀ ℕ ↦ μ 0) h
  have h11 : ‖coeff (Finsupp.single 0 1 + Finsupp.single 1 1)
      (annulusGenerator c : MvPowerSeries (Fin 2) K)‖ = 1 := by
    rw [coeff_annulusGenerator]; simp [hne]
  refine le_antisymm ?_ ((norm_coeff_le_norm (annulusGenerator c) _).trans_eq' h11)
  rw [norm_le_iff]
  intro μ
  have hprod : μ.prod (fun _ e ↦ (1 : ℝ) ^ e) = 1 := by simp [Finsupp.prod]
  rw [hprod, mul_one, coeff_annulusGenerator]
  by_cases hμ1 : μ = Finsupp.single 0 1 + Finsupp.single 1 1
  · subst hμ1; simp [hne]
  · by_cases hμ0 : μ = 0
    · subst hμ0; simpa [hne.symm] using hc
    · simp [hμ1, hμ0]

omit [CompleteSpace K] in
private theorem norm_constantCoeff_mul_le_of_single {c : K} (hc₀ : 0 < ‖c‖) (hc₁ : ‖c‖ ≤ 1)
    {g h : IsRestricted.subring (R := K) (fun _ : Fin 2 ↦ 1)} (hgh : g * h = annulusGenerator c)
    (k : Fin 2) (hhk : ‖coeff (Finsupp.single k 1) (h : MvPowerSeries (Fin 2) K)‖ = ‖h‖) :
    ‖constantCoeff (g : MvPowerSeries (Fin 2) K)‖ * ‖h‖ ≤ ‖c‖ := by
  let w : Fin 2 → ℝ := fun i ↦ if i = k then 1 else ‖c‖
  have (i : Fin 2) : Fact (0 < w i) := ⟨by dsimp [w]; split_ifs <;> positivity⟩
  have hw0 (i : Fin 2) : 0 ≤ w i := (Fact.out : 0 < w i).le
  have hw1 : w ≤ fun _ : Fin 2 ↦ 1 := fun i ↦ by dsimp [w]; split_ifs <;> linarith
  let ρ := restrictedRadiusHom (R := K) hw0 hw1
  have hρh : ‖ρ h‖ = ‖h‖ := by
    refine le_antisymm (norm_restrictedRadiusHom_le hw0 hw1 h) ?_
    have hwt : (Finsupp.single k 1).prod (w · ^ ·) = 1 := by
      simp [Finsupp.prod_single_index, w]
    calc
      ‖h‖ = ‖coeff (Finsupp.single k 1) (ρ h : MvPowerSeries (Fin 2) K)‖ *
          (Finsupp.single k 1).prod (w · ^ ·) := by rw [coe_restrictedRadiusHom, hwt, mul_one, hhk]
      _ ≤ ‖ρ h‖ := norm_coeff_mul_prod_le (ρ h) _
  have hρf : ‖ρ (annulusGenerator c)‖ ≤ ‖c‖ := by
    rw [norm_le_iff]
    intro μ
    rw [coe_restrictedRadiusHom, coeff_annulusGenerator]
    have hne : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1) ≠ 0 := fun h0 ↦ by
      simpa using congrArg (fun ν : Fin 2 →₀ ℕ ↦ ν 0) h0
    by_cases hμ1 : μ = Finsupp.single 0 1 + Finsupp.single 1 1
    · subst hμ1
      have hwprod : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1).prod (w · ^ ·) = ‖c‖ := by
        rw [prod_pow_add]
        fin_cases k <;> simp [Finsupp.prod_single_index, w]
      simp [hne, hwprod]
    · by_cases hμ0 : μ = 0
      · subst hμ0; simp [hne.symm]
      · simp [hμ1, hμ0, hc₀.le]
  calc
    ‖constantCoeff (g : MvPowerSeries (Fin 2) K)‖ * ‖h‖
        ≤ ‖ρ g‖ * ‖ρ h‖ := by
          rw [hρh]
          exact mul_le_mul_of_nonneg_right
            (coe_restrictedRadiusHom hw0 hw1 g ▸ norm_constantCoeff_le (ρ g)) (norm_nonneg h)
    _ = ‖ρ (annulusGenerator c)‖ := by rw [← norm_mul, ← map_mul, hgh]
    _ ≤ ‖c‖ := hρf

omit [CompleteSpace K] in
private theorem false_of_achieves_single_zero_one {c : K} (hc₀ : 0 < ‖c‖) (hc₁ : ‖c‖ < 1)
    {g h : IsRestricted.subring (R := K) (fun _ : Fin 2 ↦ 1)} (hgh : g * h = annulusGenerator c)
    (hg0 : ‖coeff (Finsupp.single 0 1) (g : MvPowerSeries (Fin 2) K)‖ = ‖g‖)
    (hh1 : ‖coeff (Finsupp.single 1 1) (h : MvPowerSeries (Fin 2) K)‖ = ‖h‖) : False := by
  have hb1 := norm_constantCoeff_mul_le_of_single hc₀ hc₁.le hgh 1 hh1
  have hb2 := norm_constantCoeff_mul_le_of_single hc₀ hc₁.le (mul_comm h g ▸ hgh) 0 hg0
  have hprod_norm : ‖g‖ * ‖h‖ = 1 := by rw [← norm_mul, hgh, norm_annulusGenerator hc₁.le]
  have hc0_prod : ‖constantCoeff (g : MvPowerSeries (Fin 2) K)‖ *
      ‖constantCoeff (h : MvPowerSeries (Fin 2) K)‖ = ‖c‖ := by
    have h0 : constantCoeff (annulusGenerator c : MvPowerSeries (Fin 2) K) = -c := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_annulusGenerator]
      have hne : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 + Finsupp.single 1 1 := fun h0 ↦ by
        simpa using congrArg (fun ν : Fin 2 →₀ ℕ ↦ ν 0) h0
      simp [hne]
    have hm : constantCoeff (g : MvPowerSeries (Fin 2) K) *
        constantCoeff (h : MvPowerSeries (Fin 2) K) = -c := by
      rw [← map_mul, ← Subring.coe_mul, hgh, h0]
    rw [← norm_mul, hm, norm_neg]
  have hle : ‖c‖ ≤ ‖c‖ * ‖c‖ := by
    calc
      ‖c‖ = (‖constantCoeff (g : MvPowerSeries (Fin 2) K)‖ * ‖h‖) *
          (‖constantCoeff (h : MvPowerSeries (Fin 2) K)‖ * ‖g‖) := by
            linear_combination -hc0_prod - (‖constantCoeff (g : MvPowerSeries (Fin 2) K)‖ *
              ‖constantCoeff (h : MvPowerSeries (Fin 2) K)‖) * hprod_norm
      _ ≤ ‖c‖ * ‖c‖ := mul_le_mul hb1 hb2 (by positivity) hc₀.le
  exact (mul_lt_of_lt_one_right hc₀ hc₁).not_ge hle

private theorem eq_single_pair_of_add_eq {i j : Fin 2 →₀ ℕ} (hi0 : i ≠ 0) (hj0 : j ≠ 0)
    (hij_eq : i + j = Finsupp.single 0 1 + Finsupp.single 1 1) :
    (i = Finsupp.single 0 1 ∧ j = Finsupp.single 1 1) ∨
      (i = Finsupp.single 1 1 ∧ j = Finsupp.single 0 1) := by
  have h0_sum : i 0 + j 0 = 1 := by simpa using congrArg (fun ν : Fin 2 →₀ ℕ ↦ ν 0) hij_eq
  have h1_sum : i 1 + j 1 = 1 := by simpa using congrArg (fun ν : Fin 2 →₀ ℕ ↦ ν 1) hij_eq
  rcases Nat.eq_zero_or_pos (i 0) with hi00 | hi0_pos
  · right
    have hj00 : j 0 = 1 := by omega
    have hi11 : i 1 = 1 := by
      rcases Nat.eq_zero_or_pos (i 1) with hi10 | hi1_pos
      · exact absurd (Finsupp.ext fun k ↦ by fin_cases k <;> simp [hi00, hi10]) hi0
      · omega
    have hj11 : j 1 = 0 := by omega
    exact ⟨Finsupp.ext fun k ↦ by fin_cases k <;> simp [hi00, hi11],
      Finsupp.ext fun k ↦ by fin_cases k <;> simp [hj00, hj11]⟩
  · left
    have hi01 : i 0 = 1 := by omega
    have hj00 : j 0 = 0 := by omega
    have hj11 : j 1 = 1 := by
      rcases Nat.eq_zero_or_pos (j 1) with hj10 | hj1_pos
      · exact absurd (Finsupp.ext fun k ↦ by fin_cases k <;> simp [hj00, hj10]) hj0
      · omega
    have hi10 : i 1 = 0 := by omega
    exact ⟨Finsupp.ext fun k ↦ by fin_cases k <;> simp [hi01, hi10],
      Finsupp.ext fun k ↦ by fin_cases k <;> simp [hj00, hj11]⟩

/-- For `c ≠ 0` with `‖c‖ < 1`, the quadratic polynomial `X_0 * X_1 - c` is irreducible in the
two-variable Tate algebra `K⟨X_0, X_1⟩`. -/
theorem irreducible_annulusGenerator {c : K} (hc₀ : c ≠ 0) (hc₁ : ‖c‖ < 1) :
    Irreducible (annulusGenerator c) := by
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc₀
  have hne11 : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1) ≠ 0 := fun h0 ↦ by
    simpa using congrArg (fun ν : Fin 2 →₀ ℕ ↦ ν 0) h0
  refine ⟨fun hu ↦ ?_, fun g h hgh ↦ ?_⟩
  · have hlt := norm_coeff_mul_prod_lt_of_isUnit hu hne11
    have hc0 : constantCoeff (annulusGenerator c : MvPowerSeries (Fin 2) K) = -c := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_annulusGenerator]
      simp [hne11.symm]
    have h11 : ‖coeff (Finsupp.single 0 1 + Finsupp.single 1 1)
        (annulusGenerator c : MvPowerSeries (Fin 2) K)‖ *
        (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1).prod (fun _ e ↦ (1 : ℝ) ^ e) = 1 := by
      rw [coeff_annulusGenerator]; simp [hne11, Finsupp.prod]
    rw [h11, hc0, norm_neg] at hlt
    exact hc₁.not_gt hlt
  · have hf0 : annulusGenerator c ≠ 0 := fun h0 ↦ by
      simpa [h0] using norm_annulusGenerator hc₁.le
    have hg0 : g ≠ 0 := left_ne_zero_of_mul (hgh ▸ hf0)
    have hh0 : h ≠ 0 := right_ne_zero_of_mul (hgh ▸ hf0)
    obtain ⟨i, j, hi, hj, himax, hjmax, hdom⟩ :=
      g.2.exists_norm_coeff_mul_norm_coeff_lt h.2
        (Subtype.coe_ne_coe.mpr hg0) (Subtype.coe_ne_coe.mpr hh0)
    have hcoeff_ij : ‖coeff (i + j) (annulusGenerator c : MvPowerSeries (Fin 2) K)‖ = 1 := by
      rw [hgh, Subring.coe_mul, antidiagonal_dominant norm _ _ i j
        IsUltrametricDist.isNonarchimedean_norm norm_mul (fun a ↦ (norm_neg a).symm)
        (fun p hp hne ↦ by simpa only [norm_mul] using hdom p hp hne), norm_mul]
      have hi' : ‖coeff i (g : MvPowerSeries (Fin 2) K)‖ = ‖g‖ := by
        simpa [AchievesGaussNorm, Finsupp.prod, ← norm_eq_gaussNorm] using hi
      have hj' : ‖coeff j (h : MvPowerSeries (Fin 2) K)‖ = ‖h‖ := by
        simpa [AchievesGaussNorm, Finsupp.prod, ← norm_eq_gaussNorm] using hj
      rw [hi', hj', ← norm_mul, ← hgh, norm_annulusGenerator hc₁.le]
    have hij_eq : i + j = Finsupp.single 0 1 + Finsupp.single 1 1 := by
      by_contra hne
      rw [coeff_annulusGenerator] at hcoeff_ij
      by_cases h0 : i + j = 0
      · simp [h0, hne11.symm, hc₁.ne] at hcoeff_ij
      · simp [hne, h0] at hcoeff_ij
    by_cases hi0 : i = 0
    · left
      subst hi0
      rw [isUnit_iff_constantCoeff_ne_zero_and_norm_coeff_mul_prod_lt]
      refine ⟨by simpa [coeff_zero_eq_constantCoeff_apply] using
        g.2.coeff_ne_zero_of_achievesGaussNorm (Subtype.coe_ne_coe.mpr hg0) hi, fun t ht ↦ ?_⟩
      simpa [AchievesGaussNorm, Finsupp.prod, coeff_zero_eq_constantCoeff_apply] using
        (himax t ht).trans_eq hi.symm
    · by_cases hj0 : j = 0
      · right
        subst hj0
        rw [isUnit_iff_constantCoeff_ne_zero_and_norm_coeff_mul_prod_lt]
        refine ⟨by simpa [coeff_zero_eq_constantCoeff_apply] using
          h.2.coeff_ne_zero_of_achievesGaussNorm (Subtype.coe_ne_coe.mpr hh0) hj, fun t ht ↦ ?_⟩
        simpa [AchievesGaussNorm, Finsupp.prod, coeff_zero_eq_constantCoeff_apply] using
          (hjmax t ht).trans_eq hj.symm
      · exfalso
        have hi_norm : ‖coeff i (g : MvPowerSeries (Fin 2) K)‖ = ‖g‖ := by
          simpa [AchievesGaussNorm, Finsupp.prod, ← norm_eq_gaussNorm] using hi
        have hj_norm : ‖coeff j (h : MvPowerSeries (Fin 2) K)‖ = ‖h‖ := by
          simpa [AchievesGaussNorm, Finsupp.prod, ← norm_eq_gaussNorm] using hj
        rcases eq_single_pair_of_add_eq hi0 hj0 hij_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact false_of_achieves_single_zero_one hc_pos hc₁ hgh.symm hi_norm hj_norm
        · exact false_of_achieves_single_zero_one hc_pos hc₁ (mul_comm g h ▸ hgh.symm)
            hj_norm hi_norm

/-- **The closed annulus algebra is an integral domain.** For `c ≠ 0` with `‖c‖ < 1`, the quotient
`K⟨X_0, X_1⟩ ⧸ (X_0 * X_1 - c)` representing the closed annulus `‖c‖ ≤ |T| ≤ 1` is a domain. -/
theorem isDomain_quotient_annulusIdeal {c : K} (hc₀ : c ≠ 0) (hc₁ : ‖c‖ < 1) :
    IsDomain (IsRestricted.subring (R := K) (fun _ : Fin 2 ↦ 1) ⧸ annulusIdeal c) := by
  rw [Ideal.Quotient.isDomain_iff_prime, annulusIdeal, Ideal.span_singleton_prime]
  · exact UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (irreducible_annulusGenerator hc₀ hc₁)
  · exact (irreducible_annulusGenerator hc₀ hc₁).ne_zero

private noncomputable def annulusEvalAlgHom {c : K} (a : Fin 2 → K) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hprod : a 0 * a 1 = c) :
    (IsRestricted.subring (R := K) (fun _ : Fin 2 ↦ 1) ⧸ annulusIdeal c) →ₐ[K] K := by
  let ev0 : IsRestricted.subring (R := K) (fun _ : Fin 2 ↦ 1) →ₐ[K] K :=
    { toRingHom := restrictedEval₂ (RingHom.id K) a (fun _ ↦ le_rfl) ha
      commutes' r := restrictedEval₂_algebraMap (RingHom.id K) a (fun _ ↦ le_rfl) ha r }
  refine Ideal.Quotient.liftₐ _ ev0 fun f hf ↦ ?_
  rw [annulusIdeal, Ideal.mem_span_singleton] at hf
  obtain ⟨g, rfl⟩ := hf
  have hgen : ev0 (annulusGenerator c) = 0 := by
    change ev0 (⟨X 0, isRestricted_X _ 0⟩ * ⟨X 1, isRestricted_X _ 1⟩ - algebraMap K _ c) = 0
    rw [map_sub, map_mul]
    change restrictedEval₂ _ a _ ha ⟨X 0, _⟩ * restrictedEval₂ _ a _ ha ⟨X 1, _⟩ -
      restrictedEval₂ _ a _ ha (algebraMap K _ c) = 0
    rw [restrictedEval₂_X, restrictedEval₂_X, restrictedEval₂_algebraMap, RingHom.id_apply, hprod,
      sub_self]
  rw [map_mul, hgen, zero_mul]

/-- In `K⟨X_0, X_1⟩ ⧸ (X_0 * X_1 - c)` with `‖c‖ ≤ 1`, the residue class of `X_0` has supremum
seminorm `1`. -/
theorem supSeminorm_mk_X_zero_quotient_annulusIdeal {c : K} (hc : ‖c‖ ≤ 1) :
    supSeminorm K (Ideal.Quotient.mk (annulusIdeal c) ⟨X 0, isRestricted_X _ 0⟩) = 1 := by
  let hA : IsAffinoidAlgebra K (_ ⧸ annulusIdeal c) :=
    isAffinoidAlgebra_tate.quotient (annulusIdeal c)
  have hle : supSeminorm K (Ideal.Quotient.mk (annulusIdeal c) ⟨X 0, isRestricted_X _ 0⟩) ≤ 1 := by
    calc
      supSeminorm K (Ideal.Quotient.mk (annulusIdeal c) ⟨X 0, isRestricted_X _ 0⟩)
          ≤ supSeminorm K (⟨X 0, isRestricted_X _ 0⟩ :
              IsRestricted.subring (R := K) (fun _ : Fin 2 ↦ 1)) :=
            isAffinoidAlgebra_tate.supSeminorm_map_le hA (Ideal.Quotient.mkₐ K (annulusIdeal c)) _
      _ ≤ ‖(⟨X 0, isRestricted_X _ 0⟩ : IsRestricted.subring (R := K) (fun _ : Fin 2 ↦ 1))‖ :=
            isAffinoidAlgebra_tate.supSeminorm_le_norm _
      _ = 1 := norm_X 0
  have ha : ∀ i : Fin 2, ‖(![1, c] i : K)‖ ≤ 1 := fun i ↦ by fin_cases i <;> simp [hc]
  let ev := annulusEvalAlgHom ![1, c] ha (one_mul c)
  let m₀ : MaximalSpectrum K := ⟨⊥, Ideal.bot_isMaximal⟩
  let x : MaximalSpectrum (_ ⧸ annulusIdeal c) := isAffinoidAlgebra_self.maximalSpectrumComap ev m₀
  have hge : 1 ≤ pointNorm K x (Ideal.Quotient.mk (annulusIdeal c) ⟨X 0, isRestricted_X _ 0⟩) := by
    have hev : ev (Ideal.Quotient.mk (annulusIdeal c) ⟨X 0, isRestricted_X _ 0⟩) = 1 :=
      restrictedEval₂_X (RingHom.id K) ![1, c] (fun _ ↦ le_rfl) ha 0
    rw [isAffinoidAlgebra_self.pointNorm_maximalSpectrumComap ev m₀, hev, pointNorm_one]
  exact le_antisymm hle (hge.trans (hA.pointNorm_le_supSeminorm x _))

/-- In `K⟨X_0, X_1⟩ ⧸ (X_0 * X_1 - c)` with `‖c‖ ≤ 1`, the residue class of `X_1` has supremum
seminorm `1`. -/
theorem supSeminorm_mk_X_one_quotient_annulusIdeal {c : K} (hc : ‖c‖ ≤ 1) :
    supSeminorm K (Ideal.Quotient.mk (annulusIdeal c) ⟨X 1, isRestricted_X _ 1⟩) = 1 := by
  let hA : IsAffinoidAlgebra K (_ ⧸ annulusIdeal c) :=
    isAffinoidAlgebra_tate.quotient (annulusIdeal c)
  have hle : supSeminorm K (Ideal.Quotient.mk (annulusIdeal c) ⟨X 1, isRestricted_X _ 1⟩) ≤ 1 := by
    calc
      supSeminorm K (Ideal.Quotient.mk (annulusIdeal c) ⟨X 1, isRestricted_X _ 1⟩)
          ≤ supSeminorm K (⟨X 1, isRestricted_X _ 1⟩ :
              IsRestricted.subring (R := K) (fun _ : Fin 2 ↦ 1)) :=
            isAffinoidAlgebra_tate.supSeminorm_map_le hA (Ideal.Quotient.mkₐ K (annulusIdeal c)) _
      _ ≤ ‖(⟨X 1, isRestricted_X _ 1⟩ : IsRestricted.subring (R := K) (fun _ : Fin 2 ↦ 1))‖ :=
            isAffinoidAlgebra_tate.supSeminorm_le_norm _
      _ = 1 := norm_X 1
  have ha : ∀ i : Fin 2, ‖(![c, 1] i : K)‖ ≤ 1 := fun i ↦ by fin_cases i <;> simp [hc]
  let ev := annulusEvalAlgHom ![c, 1] ha (mul_one c)
  let m₀ : MaximalSpectrum K := ⟨⊥, Ideal.bot_isMaximal⟩
  let x : MaximalSpectrum (_ ⧸ annulusIdeal c) := isAffinoidAlgebra_self.maximalSpectrumComap ev m₀
  have hge : 1 ≤ pointNorm K x (Ideal.Quotient.mk (annulusIdeal c) ⟨X 1, isRestricted_X _ 1⟩) := by
    have hev : ev (Ideal.Quotient.mk (annulusIdeal c) ⟨X 1, isRestricted_X _ 1⟩) = 1 :=
      restrictedEval₂_X (RingHom.id K) ![c, 1] (fun _ ↦ le_rfl) ha 1
    rw [isAffinoidAlgebra_self.pointNorm_maximalSpectrumComap ev m₀, hev, pointNorm_one]
  exact le_antisymm hle (hge.trans (hA.pointNorm_le_supSeminorm x _))

/-- In `K⟨X_0, X_1⟩ ⧸ (X_0 * X_1 - c)` with `‖c‖ ≤ 1`, the product of the residue classes of `X_0`
and `X_1` has supremum seminorm `‖c‖`. In particular, for `‖c‖ < 1`, `|X_0 * X_1|sup < |X_0|sup *
|X_1|sup`, so `supSeminorm K` is not multiplicative on the closed annulus domain. -/
theorem supSeminorm_mk_X_mul_X_quotient_annulusIdeal {c : K} (hc : ‖c‖ ≤ 1) :
    supSeminorm K (Ideal.Quotient.mk (annulusIdeal c) ⟨X 0, isRestricted_X _ 0⟩ *
      Ideal.Quotient.mk (annulusIdeal c) ⟨X 1, isRestricted_X _ 1⟩) = ‖c‖ := by
  have ha : ∀ i : Fin 2, ‖(![1, c] i : K)‖ ≤ 1 := fun i ↦ by fin_cases i <;> simp [hc]
  have : Nontrivial (_ ⧸ annulusIdeal c) :=
    (annulusEvalAlgHom ![1, c] ha (one_mul c)).domain_nontrivial
  have heq : Ideal.Quotient.mk (annulusIdeal c)
      (⟨X 0, isRestricted_X _ 0⟩ * ⟨X 1, isRestricted_X _ 1⟩) =
      algebraMap K (_ ⧸ annulusIdeal c) c := by
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  rw [← map_mul, heq, supSeminorm_algebraMap]

end Annulus

section MaximumLocusProd

private theorem maximalSpectrum_prod_eq_fst_or_snd {K : Type*} [Field K]
    (x : MaximalSpectrum (K × K)) :
    x = ⟨RingHom.ker (AlgHom.fst K K K).toRingHom,
        RingHom.ker_isMaximal_of_surjective _ fun a ↦ ⟨(a, 0), rfl⟩⟩ ∨
      x = ⟨RingHom.ker (AlgHom.snd K K K).toRingHom,
        RingHom.ker_isMaximal_of_surjective _ fun b ↦ ⟨(0, b), rfl⟩⟩ := by
  have hmul : (((1 : K), (0 : K)) * ((0 : K), (1 : K)) : K × K) ∈ x.asIdeal := by
    have h00 : (((1 : K), (0 : K)) * ((0 : K), (1 : K)) : K × K) = 0 := by ext <;> simp
    exact h00 ▸ x.asIdeal.zero_mem
  rcases x.isMaximal.isPrime.mem_or_mem hmul with h10 | h01
  · right
    have hsnd_max : (RingHom.ker (AlgHom.snd K K K).toRingHom).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ fun b ↦ ⟨(0, b), rfl⟩
    refine MaximalSpectrum.ext (hsnd_max.eq_of_le x.isMaximal.ne_top fun p hp ↦ ?_).symm
    have hp2 : p.2 = 0 := hp
    have heq : p = p * ((1 : K), (0 : K)) := by ext <;> simp [hp2]
    exact heq ▸ x.asIdeal.mul_mem_left p h10
  · left
    have hfst_max : (RingHom.ker (AlgHom.fst K K K).toRingHom).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ fun a ↦ ⟨(a, 0), rfl⟩
    refine MaximalSpectrum.ext (hfst_max.eq_of_le x.isMaximal.ne_top fun p hp ↦ ?_).symm
    have hp1 : p.1 = 0 := hp
    have heq : p = p * ((0 : K), (1 : K)) := by ext <;> simp [hp1]
    exact heq ▸ x.asIdeal.mul_mem_left p h01

/-- On `K × K`, the maximum locus `{x : MaximalSpectrum (K × K) | pointNorm K x (1, 0) =
supSeminorm K (1, 0)}` is a singleton in a two-point `T₁` space, hence is not Zariski dense. -/
theorem not_dense_setOf_pointNorm_eq_supSeminorm_prod (K : Type*) [NontriviallyNormedField K] :
    ¬ Dense {x : MaximalSpectrum (K × K) |
      pointNorm K x ((1 : K), (0 : K)) = supSeminorm K ((1 : K), (0 : K))} := by
  let x₁ : MaximalSpectrum (K × K) := ⟨RingHom.ker (AlgHom.fst K K K).toRingHom,
    RingHom.ker_isMaximal_of_surjective _ fun a ↦ ⟨(a, 0), rfl⟩⟩
  let x₂ : MaximalSpectrum (K × K) := ⟨RingHom.ker (AlgHom.snd K K K).toRingHom,
    RingHom.ker_isMaximal_of_surjective _ fun b ↦ ⟨(0, b), rfl⟩⟩
  have hpt1 : pointNorm K x₁ ((1 : K), (0 : K)) = 1 := by
    rw [pointNorm_eq_spectralNorm (ψ := AlgHom.fst K K K) le_rfl]
    change spectralNorm K K (1 : K) = 1
    rw [← map_one (algebraMap K K), spectralNorm_extends, norm_one]
  have hpt2 : pointNorm K x₂ ((1 : K), (0 : K)) = 0 := by
    rw [pointNorm_eq_spectralNorm (ψ := AlgHom.snd K K K) le_rfl]
    change spectralNorm K K (0 : K) = 0
    exact spectralNorm_zero
  have hle1 (x : MaximalSpectrum (K × K)) : pointNorm K x ((1 : K), (0 : K)) ≤ 1 := by
    rcases maximalSpectrum_prod_eq_fst_or_snd x with rfl | rfl <;> linarith
  have hsup : supSeminorm K ((1 : K), (0 : K)) = 1 :=
    le_antisymm (supSeminorm_le zero_le_one hle1)
      (hpt1 ▸ pointNorm_le_supSeminorm_of_bddAbove ⟨1, by rintro _ ⟨x, rfl⟩; exact hle1 x⟩ x₁)
  let S : Set (MaximalSpectrum (K × K)) :=
    {x | pointNorm K x ((1 : K), (0 : K)) = supSeminorm K ((1 : K), (0 : K))}
  have hS_sub : S ⊆ {x₁} := fun x hx ↦ by
    rcases maximalSpectrum_prod_eq_fst_or_snd x with rfl | rfl
    · rfl
    · linarith [hx.trans hsup]
  intro hDense
  have hx₂_eq : x₂ = x₁ :=
    Set.mem_singleton_iff.mp (closure_minimal hS_sub isClosed_singleton (hDense x₂))
  have h10_mem : ((1 : K), (0 : K)) ∈ x₂.asIdeal := rfl
  rw [hx₂_eq] at h10_mem
  exact one_ne_zero (α := K) h10_mem

end MaximumLocusProd

end TauCeti
