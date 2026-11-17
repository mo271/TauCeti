/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Degree
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Fricke
import Mathlib.FieldTheory.PrimeField
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.NumberTheory.Cyclotomic.Adjoin
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.QExpansion
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
import TauCeti.NumberTheory.ModularForms.QExpansion.Order

/-!
# Arithmeticity and cyclotomic Fourier action on Fricke functions

The field `F_N = TauCeti.modularFunctionField N` consists of the meromorphic functions on the
compactified modular curve `X(N)` whose Laurent expansion at `∞` in `q_N = exp (2πiτ / N)` has
all its coefficients in the cyclotomic field `ℚ(ζ_N) = Subfield.closure {z : ℂ | z ^ N = 1}`.
This file establishes three arithmetic facts about `F_N` and the Fricke functions `f_a`:

1. **Cyclotomic automorphisms.** The Galois group of `ℚ(ζ_N) / ℚ` is identified with `(ℤ/Nℤ)ˣ`
   (`TauCeti.cyclotomicAut`), sending every `N`-th root of unity `ζ` to `ζ ^ d.val`, and in
   particular sending `ZMod.stdAddChar r` to `ZMod.stdAddChar (r * d)`. The elements fixed by all
   `d ∈ (ℤ/Nℤ)ˣ` are precisely the rationals `⊥ : Subfield ℂ`.
2. **Cyclotomic `q`-expansions of Fricke functions.** At the cusp `∞`, the Laurent expansion of the
   Fricke function `f_a` is the quotient of the `q_N`-expansions of `E₄`, `E₆`, `Δ` and
   `(2πi)⁻² weightedG2MF (Pi.single a 1)` (`TauCeti.laurentQExpansion_frickeMeromorphicFunction`).
   Since `E₄`, `E₆` and `Δ` have integer coefficients while
   `(2πi)⁻² weightedG2MF (Pi.single a 1)` has coefficients given rationally in terms of
   `ZMod.stdAddChar` (`TauCeti.EisensteinSeries.qExpansion_weightedG2MF_single_div_coeff`), every
   Fricke function lies in `F_N` (`TauCeti.frickeMeromorphicFunction_mem_modularFunctionField`),
   and applying `cyclotomicAut N d` to the Fourier coefficients of `f_a` yields the Fourier
   expansion of `f_{a · diag(1, d)}`
   (`TauCeti.mapRingHom_cyclotomicAut_modularFunctionFieldLaurent_fricke`).
3. **Arithmetic generation and exact degree.** Comparing the finite-dimensional subextension
   `ℚ(ζ_N)(j, f_a : a ≠ 0) ≤ F_N` with the complex generation
   `ℂ(X(N)) = ℂ(j, f_a : a ≠ 0)` (`TauCeti.adjoin_insert_image_frickeMeromorphicFunction_eq_top`)
   and the upper bound `[F_N : ℚ(ζ_N)(j)] ≤ [ℂ(X(N)) : ℂ(j)]`
   (`TauCeti.finrank_adjoin_modularFunctionJ_le`) shows that the Fricke functions generate `F_N`
   over `ℚ(ζ_N)(j)` (`TauCeti.modularFunctionField_eq_closure`) and that
   `[F_N : ℚ(ζ_N)(j)] = #(SL(2, ℤ/Nℤ) / {±1})` (`TauCeti.finrank_adjoin_modularFunctionJ_eq`).

## Main declarations

* `TauCeti.cyclotomicAut`: the canonical isomorphism `(ℤ/Nℤ)ˣ ≃* RingAut ℚ(ζ_N)`.
* `TauCeti.cyclotomicAut_apply_of_pow_eq_one`, `TauCeti.cyclotomicAut_stdAddChar`, and
  `TauCeti.forall_cyclotomicAut_apply_eq_iff`: action of `cyclotomicAut` on roots of unity and
  characterization of its fixed field `ℚ`.
* `TauCeti.modularFunctionFieldLaurent`: the injective `q_N`-expansion homomorphism
  `F_N →+* ℚ(ζ_N)⸨q⸩`.
* `TauCeti.laurentQExpansion_frickeMeromorphicFunction`: the Laurent `q_N`-expansion of `f_a`.
* `TauCeti.frickeMeromorphicFunction_mem_modularFunctionField`: every Fricke function lies in `F_N`.
* `TauCeti.mapRingHom_cyclotomicAut_modularFunctionFieldLaurent_fricke`: `cyclotomicAut N d` acts
  on the Fourier coefficients of `f_a` by sending `f_a` to `f_{a · diag(1, d)}`.
* `TauCeti.modularFunctionField_eq_closure`: `F_N = ℚ(ζ_N)(j, f_a : a ≠ 0)`.
* `TauCeti.finrank_adjoin_modularFunctionJ_eq`: `[F_N : ℚ(ζ_N)(j)] = |im(SL(2, ℤ/Nℤ))|`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §6.1, §6.2.
* Serge Lang, *Elliptic Functions*, 2nd ed., Graduate Texts in Mathematics 112, Springer, 1987,
  Chapter 6, §§2–3.
-/

public noncomputable section

open CongruenceSubgroup Subgroup.CompactifiedQuotient TauCeti.RiemannSurface UpperHalfPlane
open scoped IntermediateField Matrix MatrixGroups Real

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-! ### Cyclotomic automorphisms of `ℚ(ζ_N)` -/

section Cyclotomic

/-- The `N`-th cyclotomic intermediate field of `ℂ / ℚ`. -/
private def cyclotomicIntermediateField (N : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {z : ℂ | z ^ N = 1}

private theorem toSubfield_cyclotomicIntermediateField (N : ℕ) :
    (cyclotomicIntermediateField N).toSubfield = Subfield.closure {z : ℂ | z ^ N = 1} := by
  refine le_antisymm ?_ (Subfield.closure_le.mpr (IntermediateField.subset_adjoin ℚ _))
  have hle : IntermediateField.adjoin ℚ {z : ℂ | z ^ N = 1} ≤
      (Subfield.closure {z : ℂ | z ^ N = 1}).toIntermediateField fun q ↦ by simp :=
    IntermediateField.adjoin_le_iff.mpr Subfield.subset_closure
  exact fun x hx ↦ hle hx

private def cyclotomicRingEquiv (N : ℕ) :
    cyclotomicIntermediateField N ≃+* Subfield.closure {z : ℂ | z ^ N = 1} where
  toFun x := ⟨x.1, by rw [← toSubfield_cyclotomicIntermediateField N]; exact x.2⟩
  invFun x := ⟨x.1, by
    rw [← IntermediateField.mem_toSubfield, toSubfield_cyclotomicIntermediateField N]
    exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private instance instIsCyclotomicExtension_cyclotomicIntermediateField (N : ℕ) [NeZero N] :
    IsCyclotomicExtension {N} ℚ (cyclotomicIntermediateField N) :=
  (Complex.isPrimitiveRoot_exp N (NeZero.ne N)).isCyclotomicExtension_adjoin_nth_roots

private def cyclotomicAutTransport (N : ℕ) :
    (cyclotomicIntermediateField N ≃ₐ[ℚ] cyclotomicIntermediateField N) ≃*
      (Subfield.closure {z : ℂ | z ^ N = 1} ≃+* Subfield.closure {z : ℂ | z ^ N = 1}) where
  toFun σ := (cyclotomicRingEquiv N).symm.trans (σ.toRingEquiv.trans (cyclotomicRingEquiv N))
  invFun τ := AlgEquiv.ofRingEquiv
    (f := (cyclotomicRingEquiv N).trans (τ.trans (cyclotomicRingEquiv N).symm))
    fun q ↦ Subtype.ext <| by
      change ((τ (q : Subfield.closure {z : ℂ | z ^ N = 1}) :
        Subfield.closure {z : ℂ | z ^ N = 1}) : ℂ) = (q : ℂ)
      rw [map_ratCast]
      rfl
  left_inv _ := AlgEquiv.ext fun _ ↦ Subtype.ext rfl
  right_inv _ := RingEquiv.ext fun _ ↦ Subtype.ext rfl
  map_mul' _ _ := RingEquiv.ext fun _ ↦ Subtype.ext rfl

variable (N) in
/-- **The cyclotomic Galois automorphisms of `ℚ(ζ_N)`**: the canonical group isomorphism
`(ℤ/Nℤ)ˣ ≃* RingAut ℚ(ζ_N)` sending `d` to the automorphism `ζ ↦ ζ ^ d.val` on `N`-th roots of
unity (`TauCeti.cyclotomicAut_apply_of_pow_eq_one`). -/
def cyclotomicAut :
    (ZMod N)ˣ ≃*
      (Subfield.closure {z : ℂ | z ^ N = 1} ≃+* Subfield.closure {z : ℂ | z ^ N = 1}) :=
  (IsCyclotomicExtension.autEquivPow (cyclotomicIntermediateField N)
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos N))).symm.trans (cyclotomicAutTransport N)

/-- On an `N`-th root of unity `x ∈ ℚ(ζ_N)`, `cyclotomicAut N d` raises `x` to the power `d.val`. -/
theorem cyclotomicAut_apply_of_pow_eq_one (d : (ZMod N)ˣ)
    {x : Subfield.closure {z : ℂ | z ^ N = 1}} (hx : (x : ℂ) ^ N = 1) :
    (cyclotomicAut N d x : ℂ) = (x : ℂ) ^ (d : ZMod N).val := by
  let hirr := Polynomial.cyclotomic.irreducible_rat (NeZero.pos N)
  let σ := (IsCyclotomicExtension.autEquivPow (cyclotomicIntermediateField N) hirr).symm d
  let y : cyclotomicIntermediateField N := (cyclotomicRingEquiv N).symm x
  have hy : y ^ N = 1 := Subtype.ext (by simpa [y, cyclotomicRingEquiv] using hx)
  have hσ := IsCyclotomicExtension.autEquivPow_apply_of_pow_eq_one
    (cyclotomicIntermediateField N) hirr σ hy
  rw [MulEquiv.apply_symm_apply] at hσ
  simpa [cyclotomicAut, cyclotomicAutTransport, cyclotomicRingEquiv, σ, y] using
    congrArg Subtype.val hσ

/-- Every value of the standard additive character `ZMod.stdAddChar` on `ZMod N` is an `N`-th root
of unity, hence lies in `ℚ(ζ_N)`. -/
theorem stdAddChar_mem_closure_nth_roots (r : ZMod N) :
    (ZMod.stdAddChar r : ℂ) ∈ Subfield.closure {z : ℂ | z ^ N = 1} := by
  refine Subfield.subset_closure ?_
  change (ZMod.stdAddChar r : ℂ) ^ N = 1
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
    AddChar.map_zero_eq_one]

/-- `cyclotomicAut N d` sends the `N`-th root of unity `e^(2πi r / N)` to `e^(2πi r d / N)`. -/
theorem cyclotomicAut_stdAddChar (d : (ZMod N)ˣ) (r : ZMod N) :
    (cyclotomicAut N d ⟨ZMod.stdAddChar r, stdAddChar_mem_closure_nth_roots r⟩ : ℂ) =
      ZMod.stdAddChar (r * (d : ZMod N)) := by
  have hpow : (ZMod.stdAddChar r : ℂ) ^ N = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      AddChar.map_zero_eq_one]
  rw [cyclotomicAut_apply_of_pow_eq_one d hpow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
    ZMod.natCast_zmod_val, mul_comm]

/-- **The fixed field of `cyclotomicAut N` is `ℚ`.** An element of `ℚ(ζ_N)` is fixed by every
`cyclotomicAut N d` exactly when it lies in the prime subfield `⊥ : Subfield ℂ`. -/
theorem forall_cyclotomicAut_apply_eq_iff {x : Subfield.closure {z : ℂ | z ^ N = 1}} :
    (∀ d : (ZMod N)ˣ, cyclotomicAut N d x = x) ↔ (x : ℂ) ∈ (⊥ : Subfield ℂ) := by
  constructor
  · intro hx
    have hgal : IsGalois ℚ (cyclotomicIntermediateField N) :=
      IsCyclotomicExtension.isGalois {N} ℚ (cyclotomicIntermediateField N)
    have hfin : FiniteDimensional ℚ (cyclotomicIntermediateField N) :=
      IsCyclotomicExtension.finiteDimensional {N} ℚ (cyclotomicIntermediateField N)
    let y : cyclotomicIntermediateField N := (cyclotomicRingEquiv N).symm x
    have hfix : ∀ σ : cyclotomicIntermediateField N ≃ₐ[ℚ] cyclotomicIntermediateField N,
        σ y = y := by
      intro σ
      obtain ⟨d, hd⟩ := (cyclotomicAut N).surjective (cyclotomicAutTransport N σ)
      have hσ : σ = (cyclotomicAutTransport N).symm (cyclotomicAut N d) := by
        rw [hd, MulEquiv.symm_apply_apply]
      rw [hσ]
      exact Subtype.ext (by
        simpa [cyclotomicAutTransport, cyclotomicRingEquiv, y] using congrArg Subtype.val (hx d))
    have hy : y ∈ IntermediateField.fixedField
        (⊤ : Subgroup (cyclotomicIntermediateField N ≃ₐ[ℚ] cyclotomicIntermediateField N)) :=
      (IntermediateField.mem_fixedField_iff _ _).mpr fun σ _ ↦ hfix σ
    rw [IsGalois.fixedField_top] at hy
    obtain ⟨q, hq⟩ := hy
    have hxq : (x : ℂ) = (q : ℂ) := by
      simpa [y, cyclotomicRingEquiv] using (congrArg Subtype.val hq).symm
    rw [hxq, Subfield.bot_eq_of_charZero]
    exact ⟨q, rfl⟩
  · intro hx d
    rw [Subfield.bot_eq_of_charZero, RingHom.mem_fieldRange] at hx
    obtain ⟨q, hq⟩ := hx
    have hxq : x = (q : Subfield.closure {z : ℂ | z ^ N = 1}) :=
      Subtype.ext (by simpa using hq.symm)
    rw [hxq, map_ratCast]

end Cyclotomic

/-! ### The cyclotomic Laurent `q`-expansion on `F_N` -/

section ModularLaurent

variable (N) in
/-- **The cyclotomic Laurent `q`-expansion on `F_N`**, bundled as an injective ring homomorphism
`F_N →+* ℚ(ζ_N)⸨q⸩`: the Laurent expansion at `∞` in `q_N = exp (2πiτ / N)`, read with
coefficients in `ℚ(ζ_N)`. -/
def modularFunctionFieldLaurent :
    modularFunctionField N →+* LaurentSeries (Subfield.closure {z : ℂ | z ^ N = 1}) :=
  (laurentQExpansionRestrict (cuspDatumInftyGamma N) (Subfield.closure {z : ℂ | z ^ N = 1})).comp
    (RingEquiv.subfieldCongr (modularFunctionField_def (N := N))).toRingHom

/-- Viewing `modularFunctionFieldLaurent N F` over `ℂ` recovers `laurentQExpansion` at `∞`. -/
@[simp]
theorem mapRingHom_subtype_modularFunctionFieldLaurent (F : modularFunctionField N) :
    HahnSeries.mapRingHom (Subfield.closure {z : ℂ | z ^ N = 1}).subtype
        (modularFunctionFieldLaurent N F) =
      laurentQExpansion (cuspDatumInftyGamma N) F := by
  rw [modularFunctionFieldLaurent, RingHom.comp_apply,
    mapRingHom_subtype_laurentQExpansionRestrict]
  rfl

/-- The coefficients of `modularFunctionFieldLaurent N F`, coerced to `ℂ`, are the coefficients
of `laurentQExpansion (cuspDatumInftyGamma N) F`. -/
@[simp]
theorem coe_coeff_modularFunctionFieldLaurent (F : modularFunctionField N) (n : ℤ) :
    ((modularFunctionFieldLaurent N F).coeff n : ℂ) =
      (laurentQExpansion (cuspDatumInftyGamma N) F).coeff n := by
  simpa only [HahnSeries.coeff_mapRingHom, Subfield.coe_subtype] using
    congrArg (fun ℓ ↦ ℓ.coeff n) (mapRingHom_subtype_modularFunctionFieldLaurent F)

/-- **The `q`-expansion principle on `F_N`**: `modularFunctionFieldLaurent N` is injective. -/
theorem modularFunctionFieldLaurent_injective :
    Function.Injective (modularFunctionFieldLaurent N) :=
  (modularFunctionFieldLaurent N).injective

/-- The cyclotomic Laurent `q`-expansion of a constant `c ∈ ℚ(ζ_N)` is the constant series. -/
@[simp]
theorem modularFunctionFieldLaurent_algebraMap (c : Subfield.closure {z : ℂ | z ^ N = 1}) :
    modularFunctionFieldLaurent N
        ⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr c.2⟩ =
      HahnSeries.C c :=
  laurentQExpansionRestrict_algebraMap (cuspDatumInftyGamma N) _ c

end ModularLaurent

/-! ### Laurent `q`-expansions and cyclotomic arithmetic of Fricke functions -/

section FrickeQExpansion

open scoped ArithmeticFunction.sigma

/-- The Fricke function of the zero residue vanishes identically. -/
@[simp]
theorem frickeFunction_zero : frickeFunction (0 : Fin 2 → ZMod N) = 0 := by
  ext τ
  simp [frickeFunction_def]

/-- The Fricke meromorphic function of the zero residue is zero. -/
@[simp]
theorem frickeMeromorphicFunction_zero :
    frickeMeromorphicFunction (0 : Fin 2 → ZMod N) = 0 :=
  meromorphicFunction_ext fun τ ↦ by simp

/-- **The Laurent `q`-expansion of a Fricke function at `∞`.** In the level-`N` parameter
`q_N = exp (2πiτ / N)`, the expansion of `f_a` is the quotient of the `q_N`-expansions of `E₄`,
`E₆`, `Δ` and `(2πi)⁻² weightedG2MF (Pi.single a 1)`. -/
theorem laurentQExpansion_frickeMeromorphicFunction (a : Fin 2 → ZMod N) :
    laurentQExpansion (cuspDatumInftyGamma N) (frickeMeromorphicFunction a) =
      (qExpansion N _root_.ModularForm.E₄ : LaurentSeries ℂ) *
        (qExpansion N _root_.ModularForm.E₆ : LaurentSeries ℂ) /
        (qExpansion N _root_.ModularForm.discriminant : LaurentSeries ℂ) *
        (((2 * π * Complex.I) ^ 2)⁻¹ •
          (qExpansion N
            (EisensteinSeries.weightedG2MF (Pi.single a 1)) : LaurentSeries ℂ)) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hNSL : (N : ℝ) ∈ Subgroup.strictPeriods 𝒮ℒ := by
    rw [Subgroup.strictPeriods_SL2Z]
    exact ⟨N, by simp⟩
  have hNG : (N : ℝ) ∈ Subgroup.strictPeriods (Gamma N : Subgroup (GL (Fin 2) ℝ)) := by simp
  have hanE₄ : AnalyticAt ℂ (cuspFunction (N : ℝ) _root_.ModularForm.E₄) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero _root_.ModularForm.E₄ hNpos hNSL
  have hanE₆ : AnalyticAt ℂ (cuspFunction (N : ℝ) _root_.ModularForm.E₆) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero _root_.ModularForm.E₆ hNpos hNSL
  have hanΔ : AnalyticAt ℂ (cuspFunction (N : ℝ) _root_.ModularForm.discriminant) 0 := by
    simpa [CuspForm.coe_discriminant] using
      ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant hNpos hNSL
  have hanG : AnalyticAt ℂ (cuspFunction (N : ℝ)
      (EisensteinSeries.weightedG2MF (Pi.single a 1))) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero
      (EisensteinSeries.weightedG2MF (Pi.single a 1)) hNpos hNG
  have hmerE₄₆ :=
    TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_mul hanE₄.meromorphicAt hanE₆.meromorphicAt
  have hmerFrac :=
    TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_div hmerE₄₆ hanΔ.meromorphicAt
  have hmerSc := TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_mul
    (TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_const ((2 * π * Complex.I) ^ 2)⁻¹)
    hanG.meromorphicAt
  have hfun : (fun z : ℍ ↦ (frickeMeromorphicFunction a).finitePart
      (ofQuotient (Quotient.mk _ ((cuspDatumInftyGamma N).scaling⁻¹ • z)))) =
      (⇑_root_.ModularForm.E₄ * ⇑_root_.ModularForm.E₆ / _root_.ModularForm.discriminant) *
      ((fun _ ↦ ((2 * π * Complex.I) ^ 2)⁻¹) *
        ⇑(EisensteinSeries.weightedG2MF (Pi.single a 1))) := by
    ext τ
    simp only [cuspDatumInftyGamma_scaling, inv_one, one_smul,
      finitePart_frickeMeromorphicFunction_ofQuotient_mk, frickeFunction_def, Pi.mul_apply,
      Pi.div_apply, EisensteinSeries.coe_weightedG2MF]
    ring
  rw [laurentQExpansion_apply, cuspDatumInftyGamma_width, hfun,
    TauCeti.UpperHalfPlane.laurentQExpansion_mul hmerFrac hmerSc,
    TauCeti.UpperHalfPlane.laurentQExpansion_div hmerE₄₆ hanΔ.meromorphicAt,
    TauCeti.UpperHalfPlane.laurentQExpansion_mul hanE₄.meromorphicAt hanE₆.meromorphicAt,
    TauCeti.UpperHalfPlane.laurentQExpansion_mul
      (TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_const _) hanG.meromorphicAt,
    TauCeti.UpperHalfPlane.laurentQExpansion_const,
    TauCeti.UpperHalfPlane.laurentQExpansion_of_analyticAt hanE₄,
    TauCeti.UpperHalfPlane.laurentQExpansion_of_analyticAt hanE₆,
    TauCeti.UpperHalfPlane.laurentQExpansion_of_analyticAt hanΔ,
    TauCeti.UpperHalfPlane.laurentQExpansion_of_analyticAt hanG,
    HahnSeries.C_mul_eq_smul]

/-- A power series over `ℂ` with integer coefficients lifts to a power series over `ℚ(ζ_N)` fixed
by every cyclotomic automorphism. -/
private def liftIntPowerSeries (p : PowerSeries ℂ) (hp : ∀ n, ∃ m : ℤ, p.coeff n = m) :
    PowerSeries (Subfield.closure {z : ℂ | z ^ N = 1}) :=
  PowerSeries.mk fun n ↦
    ((Classical.choose (hp n) : ℤ) : Subfield.closure {z : ℂ | z ^ N = 1})

omit [NeZero N] in
private theorem map_subtype_liftIntPowerSeries (p : PowerSeries ℂ)
    (hp : ∀ n, ∃ m : ℤ, p.coeff n = m) :
    PowerSeries.map (Subfield.closure {z : ℂ | z ^ N = 1}).subtype
        (liftIntPowerSeries (N := N) p hp) = p := by
  ext n
  simpa [liftIntPowerSeries] using (Classical.choose_spec (hp n)).symm

private theorem map_cyclotomicAut_liftIntPowerSeries (p : PowerSeries ℂ)
    (hp : ∀ n, ∃ m : ℤ, p.coeff n = m) (d : (ZMod N)ˣ) :
    PowerSeries.map (cyclotomicAut N d).toRingHom (liftIntPowerSeries (N := N) p hp) =
      liftIntPowerSeries (N := N) p hp := by
  ext n
  simp [liftIntPowerSeries]

private theorem exists_qExpansion_E₄_natCast_coeff_int (n : ℕ) :
    ∃ m : ℤ, (qExpansion N _root_.ModularForm.E₄).coeff n = m := by
  have hexp : qExpansion N _root_.ModularForm.E₄ =
      PowerSeries.expand N (NeZero.ne N) (qExpansion 1 _root_.ModularForm.E₄) := by
    simpa using TauCeti.qExpansion_nat_mul one_ne_zero (NeZero.pos N)
      (SlashInvariantFormClass.periodic_comp_ofComplex _root_.ModularForm.E₄
        one_mem_strictPeriods_SL)
      (ModularFormClass.analyticAt_cuspFunction_zero _root_.ModularForm.E₄ one_pos
        one_mem_strictPeriods_SL)
  rw [hexp, PowerSeries.coeff_expand]
  split_ifs
  · exact ModularForm.exists_E₄_qExpansion_coeff_eq_intCast (n / N)
  · exact ⟨0, by simp⟩

private theorem exists_qExpansion_E₆_natCast_coeff_int (n : ℕ) :
    ∃ m : ℤ, (qExpansion N _root_.ModularForm.E₆).coeff n = m := by
  have hexp : qExpansion N _root_.ModularForm.E₆ =
      PowerSeries.expand N (NeZero.ne N) (qExpansion 1 _root_.ModularForm.E₆) := by
    simpa using TauCeti.qExpansion_nat_mul one_ne_zero (NeZero.pos N)
      (SlashInvariantFormClass.periodic_comp_ofComplex _root_.ModularForm.E₆
        one_mem_strictPeriods_SL)
      (ModularFormClass.analyticAt_cuspFunction_zero _root_.ModularForm.E₆ one_pos
        one_mem_strictPeriods_SL)
  rw [hexp, PowerSeries.coeff_expand]
  split_ifs
  · rw [ModularForm.qExpansion_E₆_eq, PowerSeries.coeff_map]
    exact ⟨_, rfl⟩
  · exact ⟨0, by simp⟩

private theorem exists_qExpansion_discriminant_natCast_coeff_int (n : ℕ) :
    ∃ m : ℤ, (qExpansion N _root_.ModularForm.discriminant).coeff n = m := by
  rw [ModularForm.qExpansion_natCast_discriminant, PowerSeries.coeff_expand]
  split_ifs
  · exact ModularForm.exists_discriminant_qExpansion_coeff_eq_intCast (n / N)
  · exact ⟨0, by simp⟩

/-- `ZMod.stdAddChar r` viewed as an element of `ℚ(ζ_N)`. -/
private def stdAddCharSubfield (r : ZMod N) : Subfield.closure {z : ℂ | z ^ N = 1} :=
  ⟨ZMod.stdAddChar r, stdAddChar_mem_closure_nth_roots r⟩

private theorem cyclotomicAut_stdAddCharSubfield (d : (ZMod N)ˣ) (r : ZMod N) :
    cyclotomicAut N d (stdAddCharSubfield r) = stdAddCharSubfield (r * (d : ZMod N)) :=
  Subtype.ext (cyclotomicAut_stdAddChar d r)

/-- Explicit power series over `ℚ(ζ_N)` for `(2πi)⁻² weightedG2MF (Pi.single a 1)` when `a ≠ 0`. -/
private def g2SingleSeries (a : Fin 2 → ZMod N) :
    PowerSeries (Subfield.closure {z : ℂ | z ^ N = 1}) :=
  PowerSeries.mk fun n ↦
    ((N : Subfield.closure {z : ℂ | z ^ N = 1}) ^ 2)⁻¹ *
      if n = 0 then
        1 / 12 +
          if a 0 = 0 then
            stdAddCharSubfield (a 1) / (1 - stdAddCharSubfield (a 1)) ^ 2
          else 0
      else
        (∑ x ∈ n.divisorsAntidiagonal,
          ((if (x.1 : ZMod N) = a 0 then stdAddCharSubfield (a 1 * (x.2 : ZMod N)) else 0) +
            if -(x.1 : ZMod N) = a 0 then
              stdAddCharSubfield (-(a 1 * (x.2 : ZMod N)))
            else 0) * (x.2 : Subfield.closure {z : ℂ | z ^ N = 1})) -
          if N ∣ n then 2 * (σ 1 (n / N) : Subfield.closure {z : ℂ | z ^ N = 1}) else 0

private theorem map_subtype_g2SingleSeries {a : Fin 2 → ZMod N} (ha : a ≠ 0) :
    PowerSeries.map (Subfield.closure {z : ℂ | z ^ N = 1}).subtype (g2SingleSeries a) =
      ((2 * π * Complex.I) ^ 2)⁻¹ •
        qExpansion N (EisensteinSeries.weightedG2MF (Pi.single a 1)) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_smul, smul_eq_mul, ← div_eq_inv_mul,
    EisensteinSeries.qExpansion_weightedG2MF_single_div_coeff ha n]
  simp only [g2SingleSeries, PowerSeries.coeff_mk, map_mul, map_inv₀, map_pow, map_natCast,
    Subfield.coe_subtype]
  congr 1
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [↓reduceIte]
    push_cast
    congr 1
    split_ifs <;> simp [stdAddCharSubfield]
  · simp only [hn, ↓reduceIte]
    push_cast
    apply congrArg₂ (· - ·)
    · refine Finset.sum_congr rfl fun x _ ↦ ?_
      apply congrArg₂ (· * ·) _ rfl
      apply congrArg₂ (· + ·) <;> split_ifs <;> simp [stdAddCharSubfield]
    · split_ifs <;> rfl

omit [NeZero N] in
private theorem vecMul_diagGL_one_apply (a : Fin 2 → ZMod N) (d : (ZMod N)ˣ) :
    (a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N))) 0 = a 0 ∧
      (a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N))) 1 = a 1 * (d : ZMod N) := by
  constructor <;> simp [Matrix.vecMul, dotProduct]

private theorem map_cyclotomicAut_g2SingleSeries (d : (ZMod N)ˣ) (a : Fin 2 → ZMod N) :
    PowerSeries.map (cyclotomicAut N d).toRingHom (g2SingleSeries a) =
      g2SingleSeries (a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N))) := by
  obtain ⟨h0, h1⟩ := vecMul_diagGL_one_apply a d
  refine PowerSeries.ext fun n ↦ ?_
  simp only [PowerSeries.coeff_map, g2SingleSeries, PowerSeries.coeff_mk,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h0, h1]
  rw [map_mul, map_inv₀, map_pow, map_natCast]
  apply congrArg (((N : Subfield.closure {z : ℂ | z ^ N = 1}) ^ 2)⁻¹ * ·)
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [↓reduceIte, map_add, map_div₀, map_one, map_ofNat]
    apply congrArg (1 / 12 + ·)
    split_ifs <;> simp [cyclotomicAut_stdAddCharSubfield]
  · simp only [hn, ↓reduceIte, map_sub, map_sum, map_mul, map_add, map_natCast]
    apply congrArg₂ (· - ·)
    · refine Finset.sum_congr rfl fun x _ ↦ ?_
      apply congrArg₂ (· * ·) _ rfl
      apply congrArg₂ (· + ·)
      · split_ifs
        · rw [cyclotomicAut_stdAddCharSubfield]
          congr 1
          ring
        · simp
      · split_ifs
        · rw [cyclotomicAut_stdAddCharSubfield]
          congr 1
          ring
        · simp
    · split_ifs <;> simp [map_ofNat]

/-- Explicit Laurent series over `ℚ(ζ_N)` representing `f_a` for `a ≠ 0`. -/
private def frickeLaurentSeries (a : Fin 2 → ZMod N) :
    LaurentSeries (Subfield.closure {z : ℂ | z ^ N = 1}) :=
  (liftIntPowerSeries (N := N) _ (exists_qExpansion_E₄_natCast_coeff_int (N := N)) :
      LaurentSeries (Subfield.closure {z : ℂ | z ^ N = 1})) *
    (liftIntPowerSeries (N := N) _ (exists_qExpansion_E₆_natCast_coeff_int (N := N)) :
      LaurentSeries (Subfield.closure {z : ℂ | z ^ N = 1})) /
    (liftIntPowerSeries (N := N) _ (exists_qExpansion_discriminant_natCast_coeff_int (N := N)) :
      LaurentSeries (Subfield.closure {z : ℂ | z ^ N = 1})) *
    (g2SingleSeries a : LaurentSeries (Subfield.closure {z : ℂ | z ^ N = 1}))

private theorem mapRingHom_subtype_frickeLaurentSeries {a : Fin 2 → ZMod N} (ha : a ≠ 0) :
    HahnSeries.mapRingHom (Subfield.closure {z : ℂ | z ^ N = 1}).subtype (frickeLaurentSeries a) =
      laurentQExpansion (cuspDatumInftyGamma N) (frickeMeromorphicFunction a) := by
  rw [laurentQExpansion_frickeMeromorphicFunction, frickeLaurentSeries]
  simp only [map_mul, map_div₀, HahnSeries.mapRingHom_apply, HahnSeries.map_ofPowerSeries,
    map_subtype_liftIntPowerSeries, map_subtype_g2SingleSeries ha]
  congr 1
  ext n
  rcases n with n | n <;> simp

/-- **Every Fricke function belongs to `F_N`.** Its Laurent `q_N`-expansion at `∞` has all its
coefficients in the `N`-th cyclotomic field `ℚ(ζ_N)`. -/
theorem frickeMeromorphicFunction_mem_modularFunctionField (a : Fin 2 → ZMod N) :
    frickeMeromorphicFunction a ∈ modularFunctionField N := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [frickeMeromorphicFunction_zero]
    exact zero_mem _
  · rw [modularFunctionField_def]
    exact (mem_coeffSubfield_iff_exists_mapRingHom_eq _).mpr
      ⟨frickeLaurentSeries a, mapRingHom_subtype_frickeLaurentSeries ha⟩

/-- **Action of `cyclotomicAut N d` on the `q`-expansion of a Fricke function.** Applying the
cyclotomic automorphism `ζ ↦ ζ ^ d.val` coefficientwise to the `q_N`-expansion of `f_a` yields the
`q_N`-expansion of `f_{a · diag(1, d)}`. -/
theorem mapRingHom_cyclotomicAut_modularFunctionFieldLaurent_fricke (d : (ZMod N)ˣ)
    (a : Fin 2 → ZMod N) :
    HahnSeries.mapRingHom (cyclotomicAut N d).toRingHom
        (modularFunctionFieldLaurent N
          ⟨frickeMeromorphicFunction a, frickeMeromorphicFunction_mem_modularFunctionField a⟩) =
      modularFunctionFieldLaurent N
        ⟨frickeMeromorphicFunction (a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N))),
          frickeMeromorphicFunction_mem_modularFunctionField _⟩ := by
  rcases eq_or_ne a 0 with rfl | ha
  · have h0 : (⟨frickeMeromorphicFunction (0 : Fin 2 → ZMod N),
        frickeMeromorphicFunction_mem_modularFunctionField 0⟩ : modularFunctionField N) = 0 :=
      Subtype.ext frickeMeromorphicFunction_zero
    have h0' : (⟨frickeMeromorphicFunction
        ((0 : Fin 2 → ZMod N) ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N))),
        frickeMeromorphicFunction_mem_modularFunctionField _⟩ : modularFunctionField N) = 0 :=
      Subtype.ext (by simp)
    rw [h0, h0', map_zero, map_zero]
  · have had : a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N)) ≠ 0 := by
      intro h
      apply ha
      have hinv := congrArg (· ᵥ* (((diagGL ![1, d])⁻¹ : GL (Fin 2) (ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N))) h
      simpa [Matrix.vecMul_vecMul] using hinv
    have h1 : modularFunctionFieldLaurent N
        ⟨frickeMeromorphicFunction a, frickeMeromorphicFunction_mem_modularFunctionField a⟩ =
        frickeLaurentSeries a := by
      apply HahnSeries.mapRingHom_injective (Subfield.closure {z : ℂ | z ^ N = 1}).subtype_injective
      rw [mapRingHom_subtype_modularFunctionFieldLaurent, mapRingHom_subtype_frickeLaurentSeries ha]
    have h2 : modularFunctionFieldLaurent N
        ⟨frickeMeromorphicFunction (a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N))),
          frickeMeromorphicFunction_mem_modularFunctionField _⟩ =
        frickeLaurentSeries (a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N))) := by
      apply HahnSeries.mapRingHom_injective (Subfield.closure {z : ℂ | z ^ N = 1}).subtype_injective
      rw [mapRingHom_subtype_modularFunctionFieldLaurent,
        mapRingHom_subtype_frickeLaurentSeries had]
    rw [h1, h2, frickeLaurentSeries, frickeLaurentSeries]
    simp only [map_mul, map_div₀, HahnSeries.mapRingHom_apply, HahnSeries.map_ofPowerSeries,
      map_cyclotomicAut_liftIntPowerSeries, map_cyclotomicAut_g2SingleSeries]

end FrickeQExpansion

/-! ### Arithmetic generation `F_N = ℚ(ζ_N)(j, f_a : a ≠ 0)` and exact degree -/

section Generation

/-- An abstract degree comparison: if `A / C` is finite, `f : A →+* M` maps `C` into the image of
`B` in `M` where `M / B` is finite, and `f(A)` generates `M` over `B`, then
`[M : B] ≤ [A : C]`. -/
private theorem finrank_le_of_adjoin_range_eq_top
    {C A B M : Type*} [Field C] [Field A] [Field B] [Field M]
    [Algebra C A] [FiniteDimensional C A] [Algebra B M] [FiniteDimensional B M]
    (f : A →+* M) (hC : ∀ c : C, ∃ b : B, algebraMap B M b = f (algebraMap C A c))
    (hA : IntermediateField.adjoin B (Set.range f) = ⊤) :
    Module.finrank B M ≤ Module.finrank C A := by
  classical
  let b := Module.Basis.ofVectorSpace C A
  have : Fintype (Module.Basis.ofVectorSpaceIndex C A) :=
    Fintype.ofFinite (Module.Basis.ofVectorSpaceIndex C A)
  let v : Module.Basis.ofVectorSpaceIndex C A → M := fun i ↦ f (b i)
  let W : Submodule B M := Submodule.span B (Set.range v)
  have hf_mem_W : ∀ x : A, f x ∈ W := by
    intro x
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem W fun i _ ↦ ?_
    obtain ⟨c, hc⟩ := hC (b.repr x i)
    rw [Algebra.smul_def, map_mul, ← hc, ← Algebra.smul_def]
    exact Submodule.smul_mem W c (Submodule.subset_span ⟨i, rfl⟩)
  have hS_le_W : Submodule.span B (Set.range f) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hf_mem_W x)
  let Ssub : Subalgebra B M :=
    { carrier := Submodule.span B (Set.range f)
      mul_mem' := fun {x y} hx hy ↦ by
        refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ h₁ h₂ ↦ by
          rw [add_mul]; exact Submodule.add_mem _ h₁ h₂) (fun c _ _ h₁ ↦ by
          rw [Algebra.smul_mul_assoc]; exact Submodule.smul_mem _ c h₁) hx
        rintro _ ⟨a, rfl⟩
        refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ h₁ h₂ ↦ by
          rw [mul_add]; exact Submodule.add_mem _ h₁ h₂) (fun c _ _ h₁ ↦ by
          rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem _ c h₁) hy
        rintro _ ⟨a', rfl⟩
        exact Submodule.subset_span ⟨a * a', map_mul f a a'⟩
      one_mem' := Submodule.subset_span ⟨1, map_one f⟩
      add_mem' := Submodule.add_mem _
      zero_mem' := Submodule.zero_mem _
      algebraMap_mem' := fun c ↦ by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem (Submodule.span B (Set.range f)) c
          (Submodule.subset_span ⟨1, map_one f⟩) }
  have hW_top : W = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ hS_le_W <|
      (Algebra.adjoin_le (S := Ssub) fun _ hx ↦ Submodule.subset_span hx) ?_
    have : Algebra.IsAlgebraic B M := Algebra.IsAlgebraic.of_finite B M
    rw [← IntermediateField.adjoin_toSubalgebra (F := B), hA]
    trivial
  have h1 : Module.finrank B M = Module.finrank B W := by
    rw [hW_top, finrank_top]
  have h2 : Module.finrank B W ≤ Fintype.card (Module.Basis.ofVectorSpaceIndex C A) :=
    (finrank_span_le_card (Set.range v)).trans <| by
      rw [Set.toFinset_range]
      exact Finset.card_image_le.trans_eq Finset.card_univ
  rw [h1, Module.finrank_eq_card_basis b]
  exact h2

/-- An intermediate field of a finite extension with the same degree as the ambient field equals
`⊤`. -/
private theorem intermediateField_eq_top_of_finrank_eq {F E : Type*} [Field F] [Field E]
    [Algebra F E] [FiniteDimensional F E] (A : IntermediateField F E)
    (h : Module.finrank F A = Module.finrank F E) : A = ⊤ := by
  have hsub : A.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq h
  exact eq_top_iff.mpr fun x _ ↦ by
    have : x ∈ A.toSubmodule := hsub ▸ Submodule.mem_top
    exact this

/-- Abstract generation criterion: if `[L : C] ≤ [M : B]`, `val : L →+* M` maps `C` into the
image of `B`, and `val '' S` generates `M` over `B`, then `S` generates `L` over `C` and
`[L : C] = [M : B]`. -/
private theorem adjoin_eq_top_and_finrank_eq
    {K L B M : Type*} [Field K] [Field L] [Field B] [Field M]
    [Algebra K L] [Algebra B M] [FiniteDimensional B M]
    (val : L →+* M) (C : IntermediateField K L) [FiniteDimensional C L] (S : Set L)
    (hC : ∀ c : C, ∃ b : B, algebraMap B M b = val c)
    (hgen : IntermediateField.adjoin B (val '' S) = ⊤)
    (hle : Module.finrank C L ≤ Module.finrank B M) :
    IntermediateField.adjoin C S = ⊤ ∧ Module.finrank C L = Module.finrank B M := by
  let A : IntermediateField C L := IntermediateField.adjoin C S
  let f : A →+* M := val.comp A.val.toRingHom
  have hA : IntermediateField.adjoin B (Set.range f) = ⊤ := by
    refine eq_top_iff.mpr (hgen.symm.le.trans (IntermediateField.adjoin.mono B _ _ ?_))
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, IntermediateField.subset_adjoin C S hx⟩, rfl⟩
  have : FiniteDimensional C A := Submodule.finiteDimensional_of_le (le_top : A.toSubmodule ≤ ⊤)
  have hfin_le : Module.finrank B M ≤ Module.finrank C A :=
    finrank_le_of_adjoin_range_eq_top f hC hA
  have hfin_A_le_L : Module.finrank C A ≤ Module.finrank C L :=
    Submodule.finrank_le A.toSubmodule
  exact ⟨intermediateField_eq_top_of_finrank_eq A (le_antisymm hfin_A_le_L (hle.trans hfin_le)),
    le_antisymm hle (hfin_le.trans hfin_A_le_L)⟩

private def frickeCoeffIntermediateField (a : Fin 2 → ZMod N) :
    coeffIntermediateField (cuspDatumInftyGamma N) (Subfield.closure {z : ℂ | z ^ N = 1}) :=
  ⟨frickeMeromorphicFunction a,
    mem_coeffIntermediateField.mpr (modularFunctionField_def (N := N) ▸
      frickeMeromorphicFunction_mem_modularFunctionField a)⟩

private theorem adjoin_fricke_eq_top_and_finrank :
    IntermediateField.adjoin
        ((Subfield.closure {z : ℂ | z ^ N = 1})⟮modularFunctionJ N
          (Subfield.closure {z : ℂ | z ^ N = 1})⟯)
        ((frickeCoeffIntermediateField (N := N)) '' {a : Fin 2 → ZMod N | a ≠ 0}) = ⊤ ∧
      Module.finrank
          ((Subfield.closure {z : ℂ | z ^ N = 1})⟮modularFunctionJ N
            (Subfield.closure {z : ℂ | z ^ N = 1})⟯)
          (coeffIntermediateField (cuspDatumInftyGamma N)
            (Subfield.closure {z : ℂ | z ^ N = 1})) =
        Nat.card (modularFunctionActionZMod N).range.unop := by
  let K := Subfield.closure {z : ℂ | z ^ N = 1}
  let M := MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient
  let L := coeffIntermediateField (cuspDatumInftyGamma N) K
  let C : IntermediateField K L := K⟮modularFunctionJ N K⟯
  let S : Set L := (frickeCoeffIntermediateField (N := N)) '' {a : Fin 2 → ZMod N | a ≠ 0}
  let Cj : IntermediateField ℂ M := IntermediateField.adjoin ℂ {(modularFunctionJ N K : M)}
  have hC : ∀ c : C, ∃ b : Cj, algebraMap Cj M b = L.val.toRingHom c := by
    intro c
    have hle : C.map L.val ≤ Cj.restrictScalars K := by
      rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact IntermediateField.subset_adjoin ℂ _ (Set.mem_singleton _)
    exact ⟨⟨L.val c, hle ⟨c, c.2, rfl⟩⟩, rfl⟩
  have hgen : IntermediateField.adjoin Cj (L.val.toRingHom '' S) = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    have hle : IntermediateField.adjoin ℂ (insert
        (Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
          ModularGroup.jMeromorphicFunction)
        (frickeMeromorphicFunction '' {a : Fin 2 → ZMod N | a ≠ 0})) ≤
        (IntermediateField.adjoin Cj (L.val.toRingHom '' S)).restrictScalars ℂ := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ (rfl | ⟨a, ha, rfl⟩)
      · rw [← coe_modularFunctionJ N K]
        exact IntermediateField.algebraMap_mem (IntermediateField.adjoin Cj (L.val.toRingHom '' S))
          ⟨(modularFunctionJ N K : M), IntermediateField.subset_adjoin ℂ _ (Set.mem_singleton _)⟩
      · exact IntermediateField.subset_adjoin Cj (L.val.toRingHom '' S)
          ⟨frickeCoeffIntermediateField a, ⟨a, ha, rfl⟩, rfl⟩
    exact hle (adjoin_insert_image_frickeMeromorphicFunction_eq_top (N := N) ▸
      IntermediateField.mem_top)
  have hle : Module.finrank C L ≤ Module.finrank Cj M := by
    rw [finrank_adjoin_coe_modularFunctionJ]
    exact finrank_adjoin_modularFunctionJ_le N K
  have hres := adjoin_eq_top_and_finrank_eq L.val.toRingHom C S hC hgen hle
  exact ⟨hres.1, hres.2.trans (finrank_adjoin_coe_modularFunctionJ N K)⟩

/-- **The exact degree `[F_N : ℚ(ζ_N)(j)]`** equals the order of the image of `SL(2, ℤ/Nℤ)` on
`X(N)`. -/
theorem finrank_adjoin_modularFunctionJ_eq :
    Module.finrank
        ((Subfield.closure {z : ℂ | z ^ N = 1})⟮modularFunctionJ N
          (Subfield.closure {z : ℂ | z ^ N = 1})⟯)
        (coeffIntermediateField (cuspDatumInftyGamma N)
          (Subfield.closure {z : ℂ | z ^ N = 1})) =
      Nat.card (modularFunctionActionZMod N).range.unop :=
  (adjoin_fricke_eq_top_and_finrank (N := N)).2

/-- **The Fricke functions generate `F_N`**: `F_N = ℚ(ζ_N)(j, f_a : a ≠ 0)`, the subfield of
meromorphic functions on `X(N)` generated by `j`, the constants in `ℚ(ζ_N)`, and the Fricke
functions of the nonzero residues modulo `N`. -/
theorem modularFunctionField_eq_closure :
    modularFunctionField N =
      Subfield.closure (insert
        (Subgroup.compactifiedQuotientComap
          (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R ModularGroup.jMeromorphicFunction)
        (algebraMap ℂ _ '' Subfield.closure {z : ℂ | z ^ N = 1} ∪
          frickeMeromorphicFunction '' {a : Fin 2 → ZMod N | a ≠ 0})) := by
  let K := Subfield.closure {z : ℂ | z ^ N = 1}
  let M := MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient
  let L := coeffIntermediateField (cuspDatumInftyGamma N) K
  let G : Set M := insert
    (Subgroup.compactifiedQuotientComap
      (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R ModularGroup.jMeromorphicFunction)
    (algebraMap ℂ M '' K ∪ frickeMeromorphicFunction '' {a : Fin 2 → ZMod N | a ≠ 0})
  refine le_antisymm ?_ (Subfield.closure_le.mpr ?_)
  · intro F hF
    have hFL : F ∈ L := mem_coeffIntermediateField.mpr (modularFunctionField_def (N := N) ▸ hF)
    have hmem : (⟨F, hFL⟩ : L) ∈ IntermediateField.adjoin (K⟮modularFunctionJ N K⟯)
        ((frickeCoeffIntermediateField (N := N)) '' {a : Fin 2 → ZMod N | a ≠ 0}) := by
      rw [(adjoin_fricke_eq_top_and_finrank (N := N)).1]
      trivial
    let B : Subfield L := (Subfield.closure G).comap L.val.toRingHom
    have hK_le_B : ∀ c : K, algebraMap K L c ∈ B := fun c ↦
      Subfield.subset_closure (Set.mem_insert_of_mem _ (Or.inl ⟨c, c.2, rfl⟩))
    have hC_le_B : ∀ c : K⟮modularFunctionJ N K⟯, (c : L) ∈ B := by
      intro c
      have hle : (K⟮modularFunctionJ N K⟯) ≤ B.toIntermediateField hK_le_B :=
        IntermediateField.adjoin_le_iff.mpr <| Set.singleton_subset_iff.mpr <| by
          change (modularFunctionJ N K : M) ∈ Subfield.closure G
          rw [coe_modularFunctionJ]
          exact Subfield.subset_closure (Set.mem_insert _ _)
      exact hle c.2
    have hA_le_B : IntermediateField.adjoin (K⟮modularFunctionJ N K⟯)
        ((frickeCoeffIntermediateField (N := N)) '' {a : Fin 2 → ZMod N | a ≠ 0}) ≤
        B.toIntermediateField hC_le_B := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨a, ha, rfl⟩
      exact Subfield.subset_closure (Set.mem_insert_of_mem _ (Or.inr ⟨a, ha, rfl⟩))
    exact hA_le_B hmem
  · rintro _ (rfl | ⟨c, hc, rfl⟩ | ⟨a, -, rfl⟩)
    · exact compactifiedQuotientComap_jMeromorphicFunction_mem_modularFunctionField
    · exact algebraMap_mem_modularFunctionField.mpr hc
    · exact frickeMeromorphicFunction_mem_modularFunctionField a

/-- **Internal generation of `F_N`.** Inside the field `F_N`, the subfield generated by `j`, the
constants in `ℚ(ζ_N)`, and the Fricke functions `f_a` (`a ≠ 0`) is all of `F_N`. -/
theorem closure_modularFunctionField_eq_top :
    Subfield.closure (insert
      (⟨Subgroup.compactifiedQuotientComap
          (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R ModularGroup.jMeromorphicFunction,
        compactifiedQuotientComap_jMeromorphicFunction_mem_modularFunctionField⟩ :
        modularFunctionField N)
      ((fun c : Subfield.closure {z : ℂ | z ^ N = 1} ↦
          (⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr c.2⟩ :
            modularFunctionField N)) '' Set.univ ∪
        (fun a : Fin 2 → ZMod N ↦
          (⟨frickeMeromorphicFunction a, frickeMeromorphicFunction_mem_modularFunctionField a⟩ :
            modularFunctionField N)) '' {a : Fin 2 → ZMod N | a ≠ 0})) = ⊤ := by
  set S := Subfield.closure (insert
    (⟨Subgroup.compactifiedQuotientComap
        (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R ModularGroup.jMeromorphicFunction,
      compactifiedQuotientComap_jMeromorphicFunction_mem_modularFunctionField⟩ :
      modularFunctionField N)
    ((fun c : Subfield.closure {z : ℂ | z ^ N = 1} ↦
        (⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr c.2⟩ :
          modularFunctionField N)) '' Set.univ ∪
      (fun a : Fin 2 → ZMod N ↦
        (⟨frickeMeromorphicFunction a, frickeMeromorphicFunction_mem_modularFunctionField a⟩ :
          modularFunctionField N)) '' {a : Fin 2 → ZMod N | a ≠ 0}))
  have hmap : S.map (modularFunctionField N).subtype = modularFunctionField N := by
    rw [RingHom.map_field_closure, Set.image_insert_eq, Set.image_union, Set.image_image,
      Set.image_image]
    have hset : (fun c : Subfield.closure {z : ℂ | z ^ N = 1} ↦
        algebraMap ℂ (MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) c) ''
        Set.univ = algebraMap ℂ _ '' Subfield.closure {z : ℂ | z ^ N = 1} := by
      ext x
      simp
    simp only [Subfield.coe_subtype]
    rw [hset]
    exact (modularFunctionField_eq_closure (N := N)).symm
  refine eq_top_iff.mpr fun F _ ↦ ?_
  have hF : (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) ∈
      S.map (modularFunctionField N).subtype := by
    rw [hmap]
    exact F.2
  obtain ⟨G, hGS, hGF⟩ := hF
  exact (Subtype.ext hGF) ▸ hGS

end Generation

end TauCeti
