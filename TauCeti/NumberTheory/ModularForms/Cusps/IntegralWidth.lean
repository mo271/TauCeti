/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Conj
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective
public import TauCeti.NumberTheory.ModularForms.Cusps.Basic
public import TauCeti.NumberTheory.ModularForms.WithCenter
import TauCeti.Algebra.GroupAction.CosetRepresentation
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.NumberTheory.Modular.ConjugateTranslation

/-!
# Integral cusp widths and normalized cusp data for subgroups of `SL(2, ℤ)`

For any subgroup `H ≤ SL(2, ℤ)` (without finiteness hypotheses), every upper-triangular matrix in
`(H : Subgroup (GL (Fin 2) ℝ))` comes from an integer power of `ModularGroup.T`. Consequently, the
analytic period groups and widths of `Mathlib.NumberTheory.ModularForms.Cusps` agree on the nose
with the group-theoretic `TauCeti.Subgroup.integerCuspWidth`:

* **Strict and projective widths at `∞` (`Subgroup.strictPeriods_coe_eq_zmultiples`,
  `Subgroup.strictWidthInfty_coe_SL2Z`, `Subgroup.adjoinNegOne_coe_eq_withCenter`,
  `Subgroup.widthInfty_coe_SL2Z`).** `(H : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty` equals
  `TauCeti.Subgroup.integerCuspWidth (H : Subgroup (GL (Fin 2) ℝ))`, adjoining `-1` in `GL(2, ℝ)`
  corresponds to `H.withCenter`, and `(H : Subgroup (GL (Fin 2) ℝ)).widthInfty` equals
  `TauCeti.Subgroup.integerCuspWidth (H.withCenter : Subgroup (GL (Fin 2) ℝ))` (which agrees with
  `integerCuspWidth (H : Subgroup (GL (Fin 2) ℝ))` whenever `-1 ∈ H`).
* **Normalized Fuchsian cusp data (`Subgroup.cuspDatumInftyOfSL2Z`, `Subgroup.cuspDatumOfSL2Z`).**
  When `H` has finite index in `SL(2, ℤ)`, `H.cuspDatumInftyOfSL2Z` is the normalized
  `Subgroup.CuspDatum` for `H.map sl2zToPSL2R` at `∞` with identity scaling and width
  `integerCuspWidth (H.withCenter : Subgroup (GL (Fin 2) ℝ))`, and `H.cuspDatumOfSL2Z σ` transports
  it to the cusp `σ • ∞` with integral scaling `(sl2zToPSL2R σ)⁻¹` and cusp orbit
  `H.cuspOrbitOfSL2Z σ`.

## References

* F. Diamond, J. Shurman, *A First Course in Modular Forms*, Springer, 2005, §2.4.
-/

open Matrix Matrix.SpecialLinearGroup Matrix.ProjectiveSpecialLinearGroup OnePoint
open scoped MatrixGroups ModularForm Pointwise

public noncomputable section

namespace Subgroup

/-! ### Effective images and `withCenter` under conjugation and `liftSL` -/

/-- Adjoining `{±I}` to `H ≤ SL(2, ℤ)` does not change its effective image in `PSL(2, ℝ)`. -/
@[simp]
theorem map_sl2zToPSL2R_withCenter (H : Subgroup SL(2, ℤ)) :
    H.withCenter.map sl2zToPSL2R = H.map sl2zToPSL2R := by
  refine le_antisymm ?_ (Subgroup.map_mono H.le_withCenter)
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨a, ha, rfl | rfl⟩ := Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mp hb
  · exact Subgroup.mem_map_of_mem _ ha
  · rw [sl2zToPSL2R_neg]
    exact Subgroup.mem_map_of_mem _ ha

/-- For `Γ' ≤ PSL(2, ℤ)`, the effective image of `Γ'.liftSL` in `PSL(2, ℝ)` agrees with
`Γ'.map psl2zToPSL2R`. -/
@[simp]
theorem map_sl2zToPSL2R_liftSL (Γ' : Subgroup PSL(2, ℤ)) :
    Γ'.liftSL.map sl2zToPSL2R = Γ'.map psl2zToPSL2R := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_liftSL]
  refine ⟨fun ⟨g, hg, hgx⟩ ↦ ⟨(g : PSL(2, ℤ)), hg, by simpa using hgx⟩, ?_⟩
  rintro ⟨p, hp, rfl⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
  exact ⟨g, hp, by simp⟩

/-- `Subgroup.withCenter` commutes with conjugation on `SL(2, ℤ)`. -/
theorem withCenter_conjAct_smul (H : Subgroup SL(2, ℤ)) (g : ConjAct SL(2, ℤ)) :
    (g • H).withCenter = g • H.withCenter := by
  obtain ⟨c, rfl⟩ := ConjAct.toConjAct.surjective g
  ext x
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.toConjAct_smul, inv_inv, Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg]
  refine ⟨?_, ?_⟩
  · rintro ⟨b, hb, hxb | rfl⟩
    · exact ⟨c⁻¹ * b * c, hb, Or.inl (by rw [hxb])⟩
    · exact ⟨c⁻¹ * b * c, hb, Or.inr (by simp)⟩
  · rintro ⟨a, ha, hax | hax⟩
    · exact ⟨c * a * c⁻¹, by simpa [mul_assoc] using ha,
        Or.inl (by simpa [mul_assoc] using congrArg (fun y ↦ c * y * c⁻¹) hax)⟩
    · exact ⟨c * a * c⁻¹, by simpa [mul_assoc] using ha,
        Or.inr (by simpa [mul_assoc] using congrArg (fun y ↦ c * y * c⁻¹) hax)⟩

/-! ### Strict periods, periods, and integer cusp widths of subgroups of `SL(2, ℤ)` -/

/-- A matrix `g : SL(2, ℤ)` maps into `(H : Subgroup (GL (Fin 2) ℝ))` if and only if `g ∈ H`. -/
theorem mem_coe_GL_iff {H : Subgroup SL(2, ℤ)} {g : SL(2, ℤ)} :
    (g : GL (Fin 2) ℝ) ∈ (H : Subgroup (GL (Fin 2) ℝ)) ↔ g ∈ H := by
  rw [TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, Subgroup.mem_map_iff_mem mapGL_injective]

/-- A natural power `T ^ n` lies in `H ≤ SL(2, ℤ)` if and only if the integer cusp width of `H`
divides `n`. -/
theorem T_pow_mem_iff_integerCuspWidth_dvd {H : Subgroup SL(2, ℤ)} {n : ℕ} :
    ModularGroup.T ^ n ∈ H ↔
      TauCeti.Subgroup.integerCuspWidth (H : Subgroup (GL (Fin 2) ℝ)) ∣ n := by
  rw [← mem_coe_GL_iff, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, map_pow,
    ← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, TauCeti.Subgroup.T_pow_mem_iff]

/-- An integer power `T ^ k` lies in `H ≤ SL(2, ℤ)` if and only if the integer cusp width of `H`
divides `k`. -/
theorem T_zpow_mem_iff_integerCuspWidth_dvd {H : Subgroup SL(2, ℤ)} {k : ℤ} :
    ModularGroup.T ^ k ∈ H ↔
      (TauCeti.Subgroup.integerCuspWidth (H : Subgroup (GL (Fin 2) ℝ)) : ℤ) ∣ k := by
  have habs : ModularGroup.T ^ k ∈ H ↔ ModularGroup.T ^ k.natAbs ∈ H := by
    rcases Int.natAbs_eq k with hk | hk
    · conv_lhs => rw [hk, zpow_natCast]
    · conv_lhs => rw [hk, _root_.zpow_neg, zpow_natCast]
      exact H.inv_mem_iff
  rw [habs, T_pow_mem_iff_integerCuspWidth_dvd, Int.natCast_dvd]

/-- For every subgroup `H ≤ SL(2, ℤ)`, the strict period group of `(H : Subgroup (GL (Fin 2) ℝ))`
is generated by `(integerCuspWidth (H : Subgroup (GL (Fin 2) ℝ)) : ℝ)`. -/
theorem strictPeriods_coe_eq_zmultiples (H : Subgroup SL(2, ℤ)) :
    (H : Subgroup (GL (Fin 2) ℝ)).strictPeriods =
      AddSubgroup.zmultiples
        (TauCeti.Subgroup.integerCuspWidth (H : Subgroup (GL (Fin 2) ℝ)) : ℝ) := by
  refine le_antisymm (fun x hx ↦ ?_)
    (AddSubgroup.zmultiples_le.mpr TauCeti.Subgroup.integerCuspWidth_mem_strictPeriods)
  rw [Subgroup.mem_strictPeriods_iff] at hx
  obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.mp hx
  have h00 : g 0 0 = 1 := by
    exact_mod_cast (by simpa [mapGL_coe_matrix] using congr($hgx 0 0) : (g 0 0 : ℝ) = 1)
  have h10 : g 1 0 = 0 := by
    exact_mod_cast (by simpa [mapGL_coe_matrix] using congr($hgx 1 0) : (g 1 0 : ℝ) = 0)
  have h01 : (g 0 1 : ℝ) = x := by
    simpa [mapGL_coe_matrix] using congr($hgx 0 1)
  have h11 : g 1 1 = 1 := by
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      simpa only [det_fin_two] using g.det_coe
    lia
  have hgT : g = ModularGroup.T ^ g 0 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11, ModularGroup.coe_T_zpow]
  have hT : ModularGroup.T ^ g 0 1 ∈ H := hgT ▸ hg
  obtain ⟨m, hm⟩ := T_zpow_mem_iff_integerCuspWidth_dvd.mp hT
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨m, ?_⟩
  rw [zsmul_eq_mul, ← h01, hm, Int.cast_mul, Int.cast_natCast, mul_comm]

/-- For every subgroup `H ≤ SL(2, ℤ)`, the analytic strict width at `∞` equals the group-theoretic
`TauCeti.Subgroup.integerCuspWidth`. -/
theorem strictWidthInfty_coe_SL2Z (H : Subgroup SL(2, ℤ)) :
    (H : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty =
      TauCeti.Subgroup.integerCuspWidth (H : Subgroup (GL (Fin 2) ℝ)) :=
  strictWidthInfty_eq_of_strictPeriods_eq_zmultiples
    (strictPeriods_coe_eq_zmultiples H) (Nat.cast_nonneg _)

/-- Adjoining `-1` in `GL(2, ℝ)` to the image of `H ≤ SL(2, ℤ)` produces the image of
`H.withCenter`. -/
theorem adjoinNegOne_coe_eq_withCenter (H : Subgroup SL(2, ℤ)) :
    (H : Subgroup (GL (Fin 2) ℝ)).adjoinNegOne = (H.withCenter : Subgroup (GL (Fin 2) ℝ)) := by
  ext x
  rw [Subgroup.mem_adjoinNegOne_iff]
  refine ⟨?_, ?_⟩
  · rintro (⟨a, ha, rfl⟩ | hx)
    · exact ⟨a, H.le_withCenter ha, rfl⟩
    · obtain ⟨a, ha, hax⟩ := hx
      refine ⟨-a, Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mpr ⟨a, ha, Or.inr rfl⟩, ?_⟩
      have hneg : mapGL ℝ (-a) = -mapGL ℝ a := by
        rw [← neg_one_mul a, map_mul, mapGL_neg_one, neg_one_mul]
      rw [hneg, hax, neg_neg]
  · rintro ⟨b, hb, rfl⟩
    rcases Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mp hb with ⟨a, ha, hba | rfl⟩
    · exact Or.inl ⟨a, ha, by rw [hba]⟩
    · refine Or.inr ⟨a, ha, ?_⟩
      rw [← neg_one_mul a, map_mul, mapGL_neg_one, neg_one_mul, neg_neg]

/-- For every subgroup `H ≤ SL(2, ℤ)`, the projective period group of
`(H : Subgroup (GL (Fin 2) ℝ))` is generated by
`(integerCuspWidth (H.withCenter : Subgroup (GL (Fin 2) ℝ)) : ℝ)`. -/
theorem periods_coe_eq_zmultiples (H : Subgroup SL(2, ℤ)) :
    (H : Subgroup (GL (Fin 2) ℝ)).periods =
      AddSubgroup.zmultiples
        (TauCeti.Subgroup.integerCuspWidth (H.withCenter : Subgroup (GL (Fin 2) ℝ)) : ℝ) := by
  rw [Subgroup.periods, adjoinNegOne_coe_eq_withCenter, strictPeriods_coe_eq_zmultiples]

/-- For every subgroup `H ≤ SL(2, ℤ)`, the projective width at `∞` equals
`integerCuspWidth (H.withCenter : Subgroup (GL (Fin 2) ℝ))`. -/
theorem widthInfty_coe_SL2Z (H : Subgroup SL(2, ℤ)) :
    (H : Subgroup (GL (Fin 2) ℝ)).widthInfty =
      TauCeti.Subgroup.integerCuspWidth (H.withCenter : Subgroup (GL (Fin 2) ℝ)) := by
  rw [Subgroup.widthInfty, adjoinNegOne_coe_eq_withCenter, strictWidthInfty_coe_SL2Z]

/-- When `-1 ∈ H`, the projective width at `∞` of `(H : Subgroup (GL (Fin 2) ℝ))` equals
`integerCuspWidth (H : Subgroup (GL (Fin 2) ℝ))`. -/
theorem widthInfty_coe_eq_integerCuspWidth_of_neg_one_mem {H : Subgroup SL(2, ℤ)}
    (h : (-1 : SL(2, ℤ)) ∈ H) :
    (H : Subgroup (GL (Fin 2) ℝ)).widthInfty =
      TauCeti.Subgroup.integerCuspWidth (H : Subgroup (GL (Fin 2) ℝ)) := by
  rw [widthInfty_coe_SL2Z,
    Subgroup.withCenter_eq_self_iff.mpr (center_le_iff_neg_one_mem.mpr h)]

/-! ### Normalized Fuchsian cusp data for finite-index subgroups of `SL(2, ℤ)` -/

/-- Conjugating `(ConjAct.toConjAct σ⁻¹ • H).map sl2zToPSL2R` by `sl2zToPSL2R σ` recovers
`H.map sl2zToPSL2R`. -/
theorem conjAct_sl2zToPSL2R_smul_map_conjAct (H : Subgroup SL(2, ℤ)) (σ : SL(2, ℤ)) :
    ConjAct.toConjAct (sl2zToPSL2R σ) • (ConjAct.toConjAct σ⁻¹ • H).map sl2zToPSL2R =
      H.map sl2zToPSL2R := by
  ext x
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.toConjAct_smul, inv_inv, Subgroup.mem_map]
  refine ⟨?_, fun ⟨a, ha, hax⟩ ↦ ⟨σ⁻¹ * a * σ, by simpa [mul_assoc] using ha, ?_⟩⟩
  · rintro ⟨b, hb, hbx⟩
    refine ⟨σ * b * σ⁻¹, hb, ?_⟩
    simpa [mul_assoc] using congrArg (fun y ↦ sl2zToPSL2R σ * y * (sl2zToPSL2R σ)⁻¹) hbx
  · simp [← hax, mul_assoc]

/-- **Normalized cusp datum at `∞` for a finite-index subgroup of `SL(2, ℤ)`.** In the identity
scaling, `∞` has width `integerCuspWidth (H.withCenter : Subgroup (GL (Fin 2) ℝ))` and generator
`sl2zToPSL2R (T ^ w)` in `(H.map sl2zToPSL2R)`. -/
def cuspDatumInftyOfSL2Z (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] :
    (H.map sl2zToPSL2R).CuspDatum := by
  let w : ℕ := TauCeti.Subgroup.integerCuspWidth (H.withCenter : Subgroup (GL (Fin 2) ℝ))
  have hw_pos : 0 < w := TauCeti.Subgroup.integerCuspWidth_pos
  have hw_mem : ModularGroup.T ^ w ∈ H.withCenter :=
    (T_pow_mem_iff_integerCuspWidth_dvd (H := H.withCenter)).mpr dvd_rfl
  let γ : H.map sl2zToPSL2R :=
    ⟨sl2zToPSL2R (ModularGroup.T ^ (w : ℤ)), by
      rw [← H.map_sl2zToPSL2R_withCenter, zpow_natCast]
      exact Subgroup.mem_map_of_mem _ hw_mem⟩
  have hpow (m : ℤ) :
      ((γ ^ m : H.map sl2zToPSL2R) : PSL(2, ℝ)) =
        sl2zToPSL2R (ModularGroup.T ^ ((w : ℤ) * m)) := by
    rw [Subgroup.coe_zpow, _root_.zpow_mul, map_zpow]
  have hγ : (γ : PSL(2, ℝ)) = upperRightHom (w : ℝ) := by
    simpa using (hpow 1).trans (TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow _)
  refine ⟨∞, 1, γ, w, Nat.cast_pos.mpr hw_pos, le_antisymm ?_ ?_, by simpa using hγ⟩
  · rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, Subgroup.smul_def, hγ]
    exact upperRightHom_smul_infty _
  · rintro ⟨_, a, ha, rfl⟩ hg
    have hc : a 1 0 = 0 :=
      (TauCeti.sl2zToPSL2R_smul_infty_eq_infty_iff a).mp (MulAction.mem_stabilizer_iff.mp hg)
    have haWC : a ∈ H.withCenter := H.le_withCenter ha
    refine Subgroup.mem_zpowers_iff.mpr ?_
    rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with ha' | ha'
    · have hT : ModularGroup.T ^ a 0 1 ∈ H.withCenter := by
        rw [← ha']
        exact haWC
      obtain ⟨k, hk⟩ := (T_zpow_mem_iff_integerCuspWidth_dvd (H := H.withCenter)).mp hT
      have h : sl2zToPSL2R a = sl2zToPSL2R (ModularGroup.T ^ a 0 1) := by
        conv_lhs => rw [ha']
      exact ⟨k, Subtype.ext ((hpow k).trans (by rw [← hk, ← h]))⟩
    · have hneg : ModularGroup.T ^ (-a 0 1) = -a := by
        conv_rhs => rw [ha']
        rw [neg_neg]
      have hT : ModularGroup.T ^ (-a 0 1) ∈ H.withCenter := by
        rw [hneg]
        exact Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mpr ⟨a, ha, Or.inr rfl⟩
      obtain ⟨k, hk⟩ := (T_zpow_mem_iff_integerCuspWidth_dvd (H := H.withCenter)).mp hT
      have h : sl2zToPSL2R a = sl2zToPSL2R (ModularGroup.T ^ (-a 0 1)) := by
        conv_lhs => rw [ha', sl2zToPSL2R_neg]
      exact ⟨k, Subtype.ext ((hpow k).trans (by rw [← hk, ← h]))⟩

@[simp]
theorem cuspDatumInftyOfSL2Z_cusp (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] :
    H.cuspDatumInftyOfSL2Z.cusp = (∞ : OnePoint ℝ) := (rfl)

@[simp]
theorem cuspDatumInftyOfSL2Z_scaling (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] :
    H.cuspDatumInftyOfSL2Z.scaling = 1 := (rfl)

@[simp]
theorem cuspDatumInftyOfSL2Z_width (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] :
    H.cuspDatumInftyOfSL2Z.width =
      TauCeti.Subgroup.integerCuspWidth (H.withCenter : Subgroup (GL (Fin 2) ℝ)) := (rfl)

/-- **Normalized cusp datum at `σ • ∞` for a finite-index subgroup of `SL(2, ℤ)`.** Built by
conjugating `(ConjAct.toConjAct σ⁻¹ • H).cuspDatumInftyOfSL2Z` by `sl2zToPSL2R σ`, with integral
scaling `(sl2zToPSL2R σ)⁻¹`. -/
def cuspDatumOfSL2Z (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (σ : SL(2, ℤ)) :
    (H.map sl2zToPSL2R).CuspDatum :=
  have : Finite (SL(2, ℤ) ⧸ (ConjAct.toConjAct σ⁻¹ • H)) :=
    Finite.of_equiv (SL(2, ℤ) ⧸ H) (Subgroup.quotientEquivOfConjAct rfl)
  have : (ConjAct.toConjAct σ⁻¹ • H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  (ConjAct.toConjAct σ⁻¹ • H).cuspDatumInftyOfSL2Z.conj
    (H.conjAct_sl2zToPSL2R_smul_map_conjAct σ)

@[simp]
theorem cuspDatumOfSL2Z_cusp (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (σ : SL(2, ℤ)) :
    (H.cuspDatumOfSL2Z σ).cusp = sl2zToPSL2R σ • (∞ : OnePoint ℝ) := by
  rw [cuspDatumOfSL2Z, CuspDatum.conj_cusp, cuspDatumInftyOfSL2Z_cusp]

@[simp]
theorem cuspDatumOfSL2Z_scaling (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (σ : SL(2, ℤ)) :
    (H.cuspDatumOfSL2Z σ).scaling = (sl2zToPSL2R σ)⁻¹ := by
  rw [cuspDatumOfSL2Z, CuspDatum.conj_scaling, cuspDatumInftyOfSL2Z_scaling, one_mul]

@[simp]
theorem cuspDatumOfSL2Z_width (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (σ : SL(2, ℤ)) :
    (H.cuspDatumOfSL2Z σ).width =
      TauCeti.Subgroup.integerCuspWidth
        (((ConjAct.toConjAct σ⁻¹ • H.withCenter : Subgroup SL(2, ℤ)) :
          Subgroup (GL (Fin 2) ℝ))) := by
  rw [cuspDatumOfSL2Z, CuspDatum.conj_width, cuspDatumInftyOfSL2Z_width, withCenter_conjAct_smul]

/-- The cusp orbit of `H.cuspDatumOfSL2Z σ` is `H.cuspOrbitOfSL2Z σ`. -/
@[simp]
theorem cuspDatumOfSL2Z_cuspOrbit (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (σ : SL(2, ℤ)) :
    (H.cuspDatumOfSL2Z σ).cuspOrbit = H.cuspOrbitOfSL2Z σ :=
  Subtype.ext (by rw [CuspDatum.cuspOrbit_val, cuspOrbitOfSL2Z_val, cuspDatumOfSL2Z_cusp])

end Subgroup

end
