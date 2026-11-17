/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Arithmetic
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Separation

/-!
# The action of `GL(2, ℤ/Nℤ) / {±I}` on the modular function field `F_N`

Let `F_N = TauCeti.modularFunctionField N` be the field of meromorphic functions on `X(N)` whose
Laurent expansion at `∞` in `q_N = exp (2πiτ / N)` has coefficients in `ℚ(ζ_N)`. The pullback along
`X(N) → X(1)` embeds `ℚ(j)` into `F_N` (`TauCeti.modularFunctionFieldBase`).

This file constructs the right action of `GL(2, ℤ/Nℤ)` on `F_N` by `ℚ(j)`-automorphisms
(`TauCeti.modularFunctionFieldAction`), descending to an isomorphism
`GL(2, ℤ/Nℤ) / {±I} ≃* Gal(F_N / ℚ(j))ᵐᵒᵖ`:

1. **`SL(2, ℤ/Nℤ)` acts by fractional linear maps.** Using `F_N = ℚ(ζ_N)(j, f_a : a ≠ 0)`
   (`TauCeti.modularFunctionField_eq_closure`), `TauCeti.modularFunctionActionZMod` preserves `F_N`
   and restricts to `TauCeti.modularFunctionFieldSLAction`, fixing `ℚ(j)` and `ℚ(ζ_N)` and sending
   `f_a ↦ f_{a · s}`.
2. **`diag(1, d)` acts on Fourier coefficients.** Applying `TauCeti.cyclotomicAut N d`
   (`ζ ↦ ζ ^ d.val`) coefficientwise to `q_N`-expansions fixes `ℚ(j)`, acts on `ℚ(ζ_N)` by
   `cyclotomicAut N d`, and sends `f_a ↦ f_{a · diag(1, d)}`, yielding
   `TauCeti.modularFunctionFieldDiagAction`.
3. **Full `GL(2, ℤ/Nℤ)` action.** Writing `g = diag(1, det g) * s` with `s ∈ SL(2, ℤ/Nℤ)` and
   composing the two actions defines a group homomorphism
   `TauCeti.modularFunctionFieldAction : GL (Fin 2) (ZMod N) →* (F_N ≃ₐ[ℚ(j)] F_N)ᵐᵒᵖ` with right
   multiplication order `(F | g₁) | g₂ = F | (g₁ * g₂)`.
4. **Kernel, fixed fields, and Galois group.** The kernel is `{±I} = Subgroup.zpowers (-1)`, which
   is trivial at `N = 2` where `-I = I`. The fixed fields of `SL(2, ℤ/Nℤ)`, `{diag(1, d)}`, and
   `GL(2, ℤ/Nℤ)` are `ℚ(ζ_N)(j)`, the subfield of functions with rational `q_N`-expansion, and
   `ℚ(j)`. By Artin's theorem `F_N / ℚ(j)` is finite Galois with group opposite-isomorphic to
   `GL(2, ℤ/Nℤ) / {±I}` (and `GL(2, ℤ/2ℤ)` at level two).

## Main declarations

* `TauCeti.modularFunctionFieldBase`: the embedded base field `ℚ(j) ≤ F_N`.
* `TauCeti.modularFunctionFieldSLAction`, `TauCeti.modularFunctionFieldDiagAction`, and
  `TauCeti.modularFunctionFieldAction`: the right actions of `SL(2, ℤ/Nℤ)`, `(ℤ/Nℤ)ˣ`, and
  `GL(2, ℤ/Nℤ)` on `F_N` over `ℚ(j)`.
* `TauCeti.unop_modularFunctionFieldAction_mul_apply`: right multiplication order.
* `TauCeti.coe_unop_modularFunctionFieldAction_toGL`,
  `TauCeti.coe_unop_modularFunctionFieldAction_toGL_map_ofQuotient`, and
  `TauCeti.modularFunctionFieldLaurent_unop_modularFunctionFieldAction_diagGL`: explicit formulas
  on `SL(2, ℤ/Nℤ)` and `diag(1, d)`.
* `TauCeti.coe_unop_modularFunctionFieldAction_fricke` and
  `TauCeti.unop_modularFunctionFieldAction_algebraMap`: action on `f_a` and `ℚ(ζ_N)`.
* `TauCeti.ker_modularFunctionFieldAction`, `TauCeti.ker_modularFunctionFieldAction_level_two`, and
  `TauCeti.modularFunctionFieldAction_level_two_injective`: exact kernel, including `N = 2`.
* `TauCeti.fixedField_unop_range_modularFunctionFieldSLAction`,
  `TauCeti.forall_unop_modularFunctionFieldAction_diagGL_eq_iff`, and
  `TauCeti.fixedField_unop_range_modularFunctionFieldAction`: fixed-field theorems.
* `TauCeti.isGalois_modularFunctionField`, `TauCeti.modularFunctionFieldActionQuotientEquiv`, and
  `TauCeti.modularFunctionFieldActionLevelTwoEquiv`: Galois group isomorphisms.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §6.2, Theorem 6.6.
* Serge Lang, *Elliptic Functions*, 2nd ed., Graduate Texts in Mathematics 112, Springer, 1987,
  Chapter 6, §3.
-/

public noncomputable section

open CongruenceSubgroup MulOpposite Subgroup.CompactifiedQuotient TauCeti.RiemannSurface
open UpperHalfPlane
open scoped Matrix MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-! ### The level-one base field `ℚ(j)` inside `F_N` -/

section BaseField

variable (N) in
/-- **The level-one rational base field `ℚ(j)` inside `F_N`**: the image of the level-one modular
function field `coeffSubfield ModularGroup.cuspDatumInfty ⊥` under the pullback map
`TauCeti.modularFunctionFieldMapOfLevelOne`. -/
def modularFunctionFieldBase : Subfield (modularFunctionField N) :=
  (modularFunctionFieldMapOfLevelOne N).fieldRange

/-- An element of `F_N` lies in `modularFunctionFieldBase N` exactly when it is the pullback of a
level-one modular function with rational `q`-expansion. -/
theorem mem_modularFunctionFieldBase_iff {F : modularFunctionField N} :
    F ∈ modularFunctionFieldBase N ↔
      ∃ G : coeffSubfield ModularGroup.cuspDatumInfty ⊥,
        modularFunctionFieldMapOfLevelOne N G = F :=
  RingHom.mem_fieldRange

/-- The pullback of the modular invariant `j` lies in `modularFunctionFieldBase N`. -/
theorem j_mem_modularFunctionFieldBase :
    (⟨Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
        ModularGroup.jMeromorphicFunction,
      compactifiedQuotientComap_jMeromorphicFunction_mem_modularFunctionField⟩ :
        modularFunctionField N) ∈ modularFunctionFieldBase N :=
  ⟨⟨ModularGroup.jMeromorphicFunction, ModularGroup.jMeromorphicFunction_mem_coeffSubfield ⊥⟩,
    Subtype.ext (coe_modularFunctionFieldMapOfLevelOne_apply _)⟩

/-- **`modularFunctionFieldBase N` is the subfield generated by `j`** inside `F_N`. -/
theorem modularFunctionFieldBase_eq_closure :
    modularFunctionFieldBase N =
      Subfield.closure
        {(⟨Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
            ModularGroup.jMeromorphicFunction,
          compactifiedQuotientComap_jMeromorphicFunction_mem_modularFunctionField⟩ :
            modularFunctionField N)} := by
  let j₁ : coeffSubfield ModularGroup.cuspDatumInfty ⊥ :=
    ⟨ModularGroup.jMeromorphicFunction, ModularGroup.jMeromorphicFunction_mem_coeffSubfield ⊥⟩
  have htop : Subfield.closure ({j₁} : Set (coeffSubfield ModularGroup.cuspDatumInfty ⊥)) = ⊤ := by
    have hmap : (Subfield.closure ({j₁} : Set (coeffSubfield ModularGroup.cuspDatumInfty ⊥))).map
        (coeffSubfield ModularGroup.cuspDatumInfty ⊥).subtype =
        coeffSubfield ModularGroup.cuspDatumInfty ⊥ := by
      rw [RingHom.map_field_closure, Set.image_singleton, Subfield.coe_subtype]
      exact ModularGroup.coeffSubfield_cuspDatumInfty_bot.symm
    refine eq_top_iff.mpr fun G _ ↦ ?_
    have hG : (G : MeromorphicFunction psl2zToPSL2R.range.CompactifiedQuotient) ∈
        (Subfield.closure ({j₁} : Set (coeffSubfield ModularGroup.cuspDatumInfty ⊥))).map
          (coeffSubfield ModularGroup.cuspDatumInfty ⊥).subtype := by
      rw [hmap]
      exact G.2
    obtain ⟨H, hH, hHG⟩ := hG
    exact (Subtype.ext hHG) ▸ hH
  rw [modularFunctionFieldBase, RingHom.fieldRange_eq_map, ← htop, RingHom.map_field_closure,
    Set.image_singleton]
  congr 1
  exact Set.singleton_eq_singleton_iff.mpr
    (Subtype.ext (coe_modularFunctionFieldMapOfLevelOne_apply j₁))

end BaseField

/-! ### Restriction of the `SL(2, ℤ/Nℤ)` action to `F_N` -/

section SLAction

/-- **Stability of `F_N` under `SL(2, ℤ/Nℤ)`.** Pulling back along any element of `SL(2, ℤ/Nℤ)`
preserves the arithmetic modular function field `F_N`. -/
theorem unop_modularFunctionActionZMod_mem_modularFunctionField (s : SL(2, ZMod N))
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient}
    (hF : F ∈ modularFunctionField N) :
    unop (modularFunctionActionZMod N s) F ∈ modularFunctionField N := by
  have hle : modularFunctionField N ≤
      (modularFunctionField N).comap (unop (modularFunctionActionZMod N s)).toRingHom := by
    nth_rw 1 [modularFunctionField_eq_closure]
    rw [Subfield.closure_le]
    rintro _ (rfl | ⟨c, hc, rfl⟩ | ⟨a, -, rfl⟩)
    · change unop (modularFunctionActionZMod N s) _ ∈ modularFunctionField N
      rw [unop_modularFunctionActionZMod_compactifiedQuotientComap]
      exact compactifiedQuotientComap_jMeromorphicFunction_mem_modularFunctionField
    · change unop (modularFunctionActionZMod N s) _ ∈ modularFunctionField N
      rw [AlgEquiv.commutes]
      exact algebraMap_mem_modularFunctionField.mpr hc
    · change unop (modularFunctionActionZMod N s) _ ∈ modularFunctionField N
      rw [unop_modularFunctionActionZMod_frickeMeromorphicFunction]
      exact frickeMeromorphicFunction_mem_modularFunctionField _
  exact hle hF

/-- The `ℚ(j)`-automorphism of `F_N` induced by an element of `SL(2, ℤ/Nℤ)`. -/
private def slAut (s : SL(2, ZMod N)) :
    modularFunctionField N ≃ₐ[modularFunctionFieldBase N] modularFunctionField N where
  toFun F := ⟨unop (modularFunctionActionZMod N s) F,
    unop_modularFunctionActionZMod_mem_modularFunctionField s F.2⟩
  invFun F := ⟨unop (modularFunctionActionZMod N s⁻¹) F,
    unop_modularFunctionActionZMod_mem_modularFunctionField s⁻¹ F.2⟩
  left_inv F := Subtype.ext <| by
    change unop (modularFunctionActionZMod N s⁻¹) (unop (modularFunctionActionZMod N s) F) = F
    rw [← AlgEquiv.mul_apply, ← unop_mul, ← map_mul, mul_inv_cancel, map_one, unop_one]
    rfl
  right_inv F := Subtype.ext <| by
    change unop (modularFunctionActionZMod N s) (unop (modularFunctionActionZMod N s⁻¹) F) = F
    rw [← AlgEquiv.mul_apply, ← unop_mul, ← map_mul, inv_mul_cancel, map_one, unop_one]
    rfl
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  commutes' r := Subtype.ext <| by
    obtain ⟨G, hG⟩ := mem_modularFunctionFieldBase_iff.mp r.2
    change unop (modularFunctionActionZMod N s) (r : modularFunctionField N) =
      (r : modularFunctionField N)
    rw [← hG, coe_modularFunctionFieldMapOfLevelOne_apply,
      unop_modularFunctionActionZMod_compactifiedQuotientComap]

variable (N) in
/-- **The right action of `SL(2, ℤ/Nℤ)` on `F_N` over `ℚ(j)`**: the restriction of the fractional
linear action `TauCeti.modularFunctionActionZMod` to the arithmetic modular function field `F_N`. -/
def modularFunctionFieldSLAction :
    SL(2, ZMod N) →*
      (modularFunctionField N ≃ₐ[modularFunctionFieldBase N] modularFunctionField N)ᵐᵒᵖ where
  toFun s := op (slAut s)
  map_one' := congrArg op <| AlgEquiv.ext fun F ↦ Subtype.ext <| by
    change unop (modularFunctionActionZMod N 1) F = F
    rw [map_one, unop_one]
    rfl
  map_mul' s₁ s₂ := by
    rw [← op_mul]
    refine congrArg op (AlgEquiv.ext fun F ↦ Subtype.ext ?_)
    change unop (modularFunctionActionZMod N (s₁ * s₂)) F =
      unop (modularFunctionActionZMod N s₂) (unop (modularFunctionActionZMod N s₁) F)
    rw [map_mul, unop_mul, AlgEquiv.mul_apply]

/-- As a map on meromorphic functions on `X(N)`, `modularFunctionFieldSLAction` agrees with
`TauCeti.modularFunctionActionZMod`. -/
@[simp]
theorem coe_unop_modularFunctionFieldSLAction (s : SL(2, ZMod N)) (F : modularFunctionField N) :
    (unop (modularFunctionFieldSLAction N s) F :
        MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) =
      unop (modularFunctionActionZMod N s) F := by
  rfl

/-- `SL(2, ℤ/Nℤ)` fixes every constant in `ℚ(ζ_N)`. -/
@[simp]
theorem unop_modularFunctionFieldSLAction_algebraMap (s : SL(2, ZMod N))
    (c : Subfield.closure {z : ℂ | z ^ N = 1}) :
    unop (modularFunctionFieldSLAction N s)
        ⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr c.2⟩ =
      ⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr c.2⟩ :=
  Subtype.ext (by rw [coe_unop_modularFunctionFieldSLAction, AlgEquiv.commutes])

/-- `SL(2, ℤ/Nℤ)` permutes the Fricke functions by `f_a ↦ f_{a · s}`. -/
@[simp]
theorem unop_modularFunctionFieldSLAction_fricke (s : SL(2, ZMod N)) (a : Fin 2 → ZMod N) :
    unop (modularFunctionFieldSLAction N s)
        ⟨frickeMeromorphicFunction a, frickeMeromorphicFunction_mem_modularFunctionField a⟩ =
      ⟨frickeMeromorphicFunction (a ᵥ* (s : Matrix (Fin 2) (Fin 2) (ZMod N))),
        frickeMeromorphicFunction_mem_modularFunctionField _⟩ :=
  Subtype.ext (unop_modularFunctionActionZMod_frickeMeromorphicFunction s a)

end SLAction

/-! ### The diagonal Fourier action `diag(1, d)` on `F_N` -/

section DiagAction

/-- Every function in `modularFunctionFieldBase N = ℚ(j)` has rational `q_N`-expansion, so its
Laurent series over `ℚ(ζ_N)` is fixed by every cyclotomic automorphism. -/
private theorem mapRingHom_cyclotomicAut_modularFunctionFieldLaurent_of_mem_base (d : (ZMod N)ˣ)
    {F : modularFunctionField N} (hF : F ∈ modularFunctionFieldBase N) :
    HahnSeries.mapRingHom (cyclotomicAut N d).toRingHom (modularFunctionFieldLaurent N F) =
      modularFunctionFieldLaurent N F := by
  obtain ⟨G, rfl⟩ := mem_modularFunctionFieldBase_iff.mp hF
  have hbot : (modularFunctionFieldMapOfLevelOne N G :
      MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) ∈
      coeffSubfield (cuspDatumInftyGamma N) ⊥ := by
    rw [coe_modularFunctionFieldMapOfLevelOne_apply]
    exact (compactifiedQuotientComap_mem_coeffSubfield_iff _ (by simp)).mpr G.2
  refine HahnSeries.ext (funext fun n ↦ ?_)
  rw [HahnSeries.coeff_mapRingHom]
  exact forall_cyclotomicAut_apply_eq_iff.mpr
    (by rw [coe_coeff_modularFunctionFieldLaurent]; exact (mem_coeffSubfield _).mp hbot n) d

private theorem mapRingHom_cyclotomicAut_one
    (ℓ : LaurentSeries (Subfield.closure {z : ℂ | z ^ N = 1})) :
    HahnSeries.mapRingHom (cyclotomicAut N 1).toRingHom ℓ = ℓ := by
  refine HahnSeries.ext (funext fun n ↦ ?_)
  simp

private theorem mapRingHom_cyclotomicAut_comp (d₁ d₂ : (ZMod N)ˣ)
    (ℓ : LaurentSeries (Subfield.closure {z : ℂ | z ^ N = 1})) :
    HahnSeries.mapRingHom (cyclotomicAut N d₁).toRingHom
        (HahnSeries.mapRingHom (cyclotomicAut N d₂).toRingHom ℓ) =
      HahnSeries.mapRingHom (cyclotomicAut N (d₁ * d₂)).toRingHom ℓ := by
  refine HahnSeries.ext (funext fun n ↦ ?_)
  simp only [HahnSeries.coeff_mapRingHom, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
  rfl

/-- Applying `cyclotomicAut N d` to the Fourier coefficients of any `F ∈ F_N` produces the
`q_N`-expansion of another element of `F_N`. -/
private theorem mapRingHom_cyclotomicAut_mem_fieldRange (d : (ZMod N)ˣ)
    (F : modularFunctionField N) :
    HahnSeries.mapRingHom (cyclotomicAut N d).toRingHom (modularFunctionFieldLaurent N F) ∈
      (modularFunctionFieldLaurent N).fieldRange := by
  let S : Subfield (modularFunctionField N) :=
    (modularFunctionFieldLaurent N).fieldRange.comap
      ((HahnSeries.mapRingHom (cyclotomicAut N d).toRingHom).comp (modularFunctionFieldLaurent N))
  have hS : S = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← closure_modularFunctionField_eq_top (N := N), Subfield.closure_le]
    rintro _ (rfl | ⟨c, -, rfl⟩ | ⟨a, -, rfl⟩) <;>
      simp only [SetLike.mem_coe, S, Subfield.mem_comap, RingHom.comp_apply]
    · rw [mapRingHom_cyclotomicAut_modularFunctionFieldLaurent_of_mem_base d
        j_mem_modularFunctionFieldBase]
      exact ⟨_, rfl⟩
    · refine ⟨⟨algebraMap ℂ _ (cyclotomicAut N d c),
        algebraMap_mem_modularFunctionField.mpr (cyclotomicAut N d c).2⟩, ?_⟩
      rw [modularFunctionFieldLaurent_algebraMap, modularFunctionFieldLaurent_algebraMap,
        HahnSeries.mapRingHom_apply, HahnSeries.map_C]
      rfl
    · rw [mapRingHom_cyclotomicAut_modularFunctionFieldLaurent_fricke]
      exact ⟨_, rfl⟩
  have hF : F ∈ S := hS ▸ Subfield.mem_top F
  exact hF

/-- The underlying map of the diagonal Fourier action on `F_N`. -/
private def diagFun (d : (ZMod N)ˣ) (F : modularFunctionField N) : modularFunctionField N :=
  (modularFunctionFieldLaurent N).rangeRestrictFieldEquiv.symm
    ⟨HahnSeries.mapRingHom (cyclotomicAut N d).toRingHom (modularFunctionFieldLaurent N F),
      mapRingHom_cyclotomicAut_mem_fieldRange d F⟩

private theorem modularFunctionFieldLaurent_diagFun (d : (ZMod N)ˣ) (F : modularFunctionField N) :
    modularFunctionFieldLaurent N (diagFun d F) =
      HahnSeries.mapRingHom (cyclotomicAut N d).toRingHom (modularFunctionFieldLaurent N F) := by
  exact congrArg Subtype.val
    ((modularFunctionFieldLaurent N).rangeRestrictFieldEquiv.apply_symm_apply
      ⟨HahnSeries.mapRingHom (cyclotomicAut N d).toRingHom (modularFunctionFieldLaurent N F),
        mapRingHom_cyclotomicAut_mem_fieldRange d F⟩)

/-- The `ℚ(j)`-automorphism of `F_N` acting on Fourier coefficients by `cyclotomicAut N d`. -/
private def diagAut (d : (ZMod N)ˣ) :
    modularFunctionField N ≃ₐ[modularFunctionFieldBase N] modularFunctionField N where
  toFun := diagFun d
  invFun := diagFun d⁻¹
  left_inv F := modularFunctionFieldLaurent_injective <| by
    rw [modularFunctionFieldLaurent_diagFun, modularFunctionFieldLaurent_diagFun,
      mapRingHom_cyclotomicAut_comp, inv_mul_cancel, mapRingHom_cyclotomicAut_one]
  right_inv F := modularFunctionFieldLaurent_injective <| by
    rw [modularFunctionFieldLaurent_diagFun, modularFunctionFieldLaurent_diagFun,
      mapRingHom_cyclotomicAut_comp, mul_inv_cancel, mapRingHom_cyclotomicAut_one]
  map_mul' _ _ := modularFunctionFieldLaurent_injective <| by
    simp only [map_mul, modularFunctionFieldLaurent_diagFun]
  map_add' _ _ := modularFunctionFieldLaurent_injective <| by
    simp only [map_add, modularFunctionFieldLaurent_diagFun]
  commutes' r := modularFunctionFieldLaurent_injective <| by
    change modularFunctionFieldLaurent N (diagFun d r) = modularFunctionFieldLaurent N r
    rw [modularFunctionFieldLaurent_diagFun]
    exact mapRingHom_cyclotomicAut_modularFunctionFieldLaurent_of_mem_base d r.2

variable (N) in
/-- **The diagonal Fourier action of `(ℤ/Nℤ)ˣ` on `F_N` over `ℚ(j)`**: `d ∈ (ℤ/Nℤ)ˣ` acts by
applying `TauCeti.cyclotomicAut N d` (`ζ ↦ ζ ^ d.val`) to each coefficient of the `q_N`-expansion
at `∞`. -/
def modularFunctionFieldDiagAction :
    (ZMod N)ˣ →*
      (modularFunctionField N ≃ₐ[modularFunctionFieldBase N] modularFunctionField N)ᵐᵒᵖ where
  toFun d := op (diagAut d)
  map_one' := congrArg op <| AlgEquiv.ext fun F ↦ modularFunctionFieldLaurent_injective <| by
    change modularFunctionFieldLaurent N (diagFun 1 F) = modularFunctionFieldLaurent N F
    rw [modularFunctionFieldLaurent_diagFun, mapRingHom_cyclotomicAut_one]
  map_mul' d₁ d₂ := by
    rw [← op_mul]
    refine congrArg op (AlgEquiv.ext fun F ↦ modularFunctionFieldLaurent_injective ?_)
    change modularFunctionFieldLaurent N (diagFun (d₁ * d₂) F) =
      modularFunctionFieldLaurent N (diagFun d₂ (diagFun d₁ F))
    rw [modularFunctionFieldLaurent_diagFun, modularFunctionFieldLaurent_diagFun,
      modularFunctionFieldLaurent_diagFun, mapRingHom_cyclotomicAut_comp, mul_comm]

/-- **`modularFunctionFieldDiagAction` acts on Laurent `q_N`-expansions by applying
`cyclotomicAut N d` coefficientwise.** -/
theorem modularFunctionFieldLaurent_unop_modularFunctionFieldDiagAction (d : (ZMod N)ˣ)
    (F : modularFunctionField N) :
    modularFunctionFieldLaurent N (unop (modularFunctionFieldDiagAction N d) F) =
      HahnSeries.mapRingHom (cyclotomicAut N d).toRingHom (modularFunctionFieldLaurent N F) :=
  modularFunctionFieldLaurent_diagFun d F

/-- On a constant `c ∈ ℚ(ζ_N)`, `modularFunctionFieldDiagAction N d` applies `cyclotomicAut N d`. -/
@[simp]
theorem unop_modularFunctionFieldDiagAction_algebraMap (d : (ZMod N)ˣ)
    (c : Subfield.closure {z : ℂ | z ^ N = 1}) :
    unop (modularFunctionFieldDiagAction N d)
        ⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr c.2⟩ =
      ⟨algebraMap ℂ _ (cyclotomicAut N d c),
        algebraMap_mem_modularFunctionField.mpr (cyclotomicAut N d c).2⟩ := by
  apply modularFunctionFieldLaurent_injective
  rw [modularFunctionFieldLaurent_unop_modularFunctionFieldDiagAction,
    modularFunctionFieldLaurent_algebraMap, modularFunctionFieldLaurent_algebraMap,
    HahnSeries.mapRingHom_apply, HahnSeries.map_C]
  rfl

/-- On a Fricke function `f_a`, `modularFunctionFieldDiagAction N d` sends `f_a` to
`f_{a · diag(1, d)}`. -/
@[simp]
theorem unop_modularFunctionFieldDiagAction_fricke (d : (ZMod N)ˣ) (a : Fin 2 → ZMod N) :
    unop (modularFunctionFieldDiagAction N d)
        ⟨frickeMeromorphicFunction a, frickeMeromorphicFunction_mem_modularFunctionField a⟩ =
      ⟨frickeMeromorphicFunction (a ᵥ* (diagGL ![1, d] : Matrix (Fin 2) (Fin 2) (ZMod N))),
        frickeMeromorphicFunction_mem_modularFunctionField _⟩ := by
  apply modularFunctionFieldLaurent_injective
  rw [modularFunctionFieldLaurent_unop_modularFunctionFieldDiagAction]
  exact mapRingHom_cyclotomicAut_modularFunctionFieldLaurent_fricke d a

end DiagAction

/-! ### The `GL(2, ℤ/Nℤ)` action on `F_N` -/

section GLAction

/-- The `SL(2, ℤ/Nℤ)` factor `diag(1, det g)⁻¹ * g` in the decomposition
`g = diag(1, det g) * slPart g`. -/
private def slPart (g : GL (Fin 2) (ZMod N)) : SL(2, ZMod N) :=
  ⟨((diagGL ![1, Matrix.GeneralLinearGroup.det g])⁻¹ * g : GL (Fin 2) (ZMod N)), by
    have hdet : Matrix.GeneralLinearGroup.det
        ((diagGL ![1, Matrix.GeneralLinearGroup.det g])⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, det_diagGL, Fin.prod_univ_two]
      simp
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]⟩

omit [NeZero N] in
private theorem diagGL_mul_slPart (g : GL (Fin 2) (ZMod N)) :
    diagGL ![1, Matrix.GeneralLinearGroup.det g] * (slPart g).toGL = g := by
  apply Units.ext
  change ((diagGL ![1, Matrix.GeneralLinearGroup.det g] *
    ((diagGL ![1, Matrix.GeneralLinearGroup.det g])⁻¹ * g) : GL (Fin 2) (ZMod N)) :
    Matrix (Fin 2) (Fin 2) (ZMod N)) = g
  rw [mul_inv_cancel_left]

omit [NeZero N] in
private theorem slPart_toGL (s : SL(2, ZMod N)) : slPart s.toGL = s := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have h1 : diagGL ![(1 : (ZMod N)ˣ), 1] = 1 := Units.ext <| by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h := diagGL_mul_slPart s.toGL
  rw [Matrix.SpecialLinearGroup.coeToGL_det, h1, one_mul] at h
  exact h

omit [NeZero N] in
private theorem slPart_diagGL (d : (ZMod N)ˣ) : slPart (diagGL ![1, d]) = 1 := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hdet : Matrix.GeneralLinearGroup.det (diagGL ![1, d]) = d := by
    rw [det_diagGL, Fin.prod_univ_two]
    simp
  have h := diagGL_mul_slPart (diagGL ![1, d])
  rw [hdet] at h
  simpa using mul_left_cancel (h.trans (mul_one _).symm)

/-- The `ℚ(j)`-automorphism of `F_N` associated to `g ∈ GL(2, ℤ/Nℤ)`: first apply the diagonal
Fourier action of `diag(1, det g)`, then the fractional linear action of `slPart g`. -/
private def glAut (g : GL (Fin 2) (ZMod N)) :
    modularFunctionField N ≃ₐ[modularFunctionFieldBase N] modularFunctionField N :=
  unop (modularFunctionFieldSLAction N (slPart g)) *
    unop (modularFunctionFieldDiagAction N (Matrix.GeneralLinearGroup.det g))

private theorem glAut_algebraMap (g : GL (Fin 2) (ZMod N))
    (c : Subfield.closure {z : ℂ | z ^ N = 1}) :
    glAut g ⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr c.2⟩ =
      ⟨algebraMap ℂ _ (cyclotomicAut N (Matrix.GeneralLinearGroup.det g) c),
        algebraMap_mem_modularFunctionField.mpr
          (cyclotomicAut N (Matrix.GeneralLinearGroup.det g) c).2⟩ := by
  rw [glAut, AlgEquiv.mul_apply, unop_modularFunctionFieldDiagAction_algebraMap,
    unop_modularFunctionFieldSLAction_algebraMap]

private theorem glAut_fricke (g : GL (Fin 2) (ZMod N)) (a : Fin 2 → ZMod N) :
    glAut g ⟨frickeMeromorphicFunction a, frickeMeromorphicFunction_mem_modularFunctionField a⟩ =
      ⟨frickeMeromorphicFunction (a ᵥ* (g : Matrix (Fin 2) (Fin 2) (ZMod N))),
        frickeMeromorphicFunction_mem_modularFunctionField _⟩ := by
  rw [glAut, AlgEquiv.mul_apply, unop_modularFunctionFieldDiagAction_fricke,
    unop_modularFunctionFieldSLAction_fricke]
  refine Subtype.ext (congrArg frickeMeromorphicFunction ?_)
  rw [Matrix.vecMul_vecMul]
  have hmul : (diagGL ![1, Matrix.GeneralLinearGroup.det g] : Matrix (Fin 2) (Fin 2) (ZMod N)) *
      ((slPart g : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      (g : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
    simpa only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using
      congrArg Units.val (diagGL_mul_slPart g)
  rw [hmul]

omit [NeZero N] in
private theorem unop_mul_unop_one {G : Type*} [Monoid G] (a : Gᵐᵒᵖ) :
    unop a * unop (1 : Gᵐᵒᵖ) = unop a := by
  rw [unop_one, mul_one]

omit [NeZero N] in
private theorem unop_one_mul_unop {G : Type*} [Monoid G] (b : Gᵐᵒᵖ) :
    unop (1 : Gᵐᵒᵖ) * unop b = unop b := by
  rw [unop_one, one_mul]

private theorem glAut_one : glAut (1 : GL (Fin 2) (ZMod N)) = 1 := by
  have hsl : slPart (1 : GL (Fin 2) (ZMod N)) = 1 := by
    simpa using slPart_toGL (1 : SL(2, ZMod N))
  have hdet : Matrix.GeneralLinearGroup.det (1 : GL (Fin 2) (ZMod N)) = 1 := map_one _
  have h1 : modularFunctionFieldSLAction N (slPart (1 : GL (Fin 2) (ZMod N))) = 1 :=
    (congrArg (modularFunctionFieldSLAction N) hsl).trans (modularFunctionFieldSLAction N).map_one
  have h2 : modularFunctionFieldDiagAction N
      (Matrix.GeneralLinearGroup.det (1 : GL (Fin 2) (ZMod N))) = 1 :=
    (congrArg (modularFunctionFieldDiagAction N) hdet).trans
      (modularFunctionFieldDiagAction N).map_one
  exact (congrArg₂ (fun a b ↦ unop a * unop b) h1 h2).trans ((unop_one_mul_unop 1).trans unop_one)

private theorem glAut_mul (g₁ g₂ : GL (Fin 2) (ZMod N)) :
    glAut (g₁ * g₂) = glAut g₂ * glAut g₁ := by
  refine AlgEquiv.ext fun F ↦ ?_
  have heq : (glAut (g₁ * g₂)).toRingHom.eqLocusField (glAut g₂ * glAut g₁).toRingHom = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← closure_modularFunctionField_eq_top (N := N), Subfield.closure_le]
    rintro _ (rfl | ⟨c, -, rfl⟩ | ⟨a, -, rfl⟩)
    · change glAut (g₁ * g₂) _ = (glAut g₂ * glAut g₁) _
      let jF : modularFunctionFieldBase N :=
        ⟨⟨Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
            ModularGroup.jMeromorphicFunction,
          compactifiedQuotientComap_jMeromorphicFunction_mem_modularFunctionField⟩,
          j_mem_modularFunctionFieldBase⟩
      change glAut (g₁ * g₂) (algebraMap (modularFunctionFieldBase N) (modularFunctionField N) jF) =
        (glAut g₂ * glAut g₁)
          (algebraMap (modularFunctionFieldBase N) (modularFunctionField N) jF)
      rw [AlgEquiv.commutes, AlgEquiv.commutes]
    · change glAut (g₁ * g₂) _ = (glAut g₂ * glAut g₁) _
      rw [AlgEquiv.mul_apply, glAut_algebraMap, glAut_algebraMap, glAut_algebraMap, map_mul,
        mul_comm (Matrix.GeneralLinearGroup.det g₁), map_mul]
      rfl
    · change glAut (g₁ * g₂) _ = (glAut g₂ * glAut g₁) _
      rw [AlgEquiv.mul_apply, glAut_fricke, glAut_fricke, glAut_fricke, Matrix.vecMul_vecMul,
        Units.val_mul]
  have hF : F ∈ (glAut (g₁ * g₂)).toRingHom.eqLocusField (glAut g₂ * glAut g₁).toRingHom :=
    heq ▸ Subfield.mem_top F
  exact hF

variable (N) in
/-- **The right action of `GL(2, ℤ/Nℤ)` on the modular function field `F_N` over `ℚ(j)`.**

On `SL(2, ℤ/Nℤ)`, the action is pullback by fractional linear maps
(`TauCeti.coe_unop_modularFunctionFieldAction_toGL`); on `diag(1, d)`, it applies the cyclotomic
automorphism `ζ ↦ ζ ^ d.val` to the Fourier coefficients at `∞`
(`TauCeti.modularFunctionFieldLaurent_unop_modularFunctionFieldAction_diagGL`). This is a right
action (`TauCeti.unop_modularFunctionFieldAction_mul_apply`), so it is bundled as a homomorphism to
the opposite of the automorphism group. -/
def modularFunctionFieldAction :
    GL (Fin 2) (ZMod N) →*
      (modularFunctionField N ≃ₐ[modularFunctionFieldBase N] modularFunctionField N)ᵐᵒᵖ where
  toFun g := op (glAut g)
  map_one' := congrArg op glAut_one
  map_mul' g₁ g₂ := by
    rw [← op_mul, glAut_mul]

/-- **Multiplication order.** The action of `GL(2, ℤ/Nℤ)` on `F_N` is a right action: acting by
`g₁ * g₂` applies `g₁` first and then `g₂`. -/
theorem unop_modularFunctionFieldAction_mul_apply (g₁ g₂ : GL (Fin 2) (ZMod N))
    (F : modularFunctionField N) :
    unop (modularFunctionFieldAction N (g₁ * g₂)) F =
      unop (modularFunctionFieldAction N g₂) (unop (modularFunctionFieldAction N g₁) F) := by
  exact congrArg (fun σ ↦ σ F) (glAut_mul g₁ g₂)

/-- On `SL(2, ℤ/Nℤ)`, `modularFunctionFieldAction` restricts to `modularFunctionFieldSLAction`. -/
@[simp]
theorem modularFunctionFieldAction_toGL (s : SL(2, ZMod N)) :
    modularFunctionFieldAction N s.toGL = modularFunctionFieldSLAction N s := by
  refine unop_injective ?_
  have h1 : modularFunctionFieldSLAction N (slPart s.toGL) = modularFunctionFieldSLAction N s :=
    congrArg (modularFunctionFieldSLAction N) (slPart_toGL s)
  have h2 : modularFunctionFieldDiagAction N (Matrix.GeneralLinearGroup.det s.toGL) = 1 :=
    (congrArg (modularFunctionFieldDiagAction N) (Matrix.SpecialLinearGroup.coeToGL_det s)).trans
      (modularFunctionFieldDiagAction N).map_one
  exact (congrArg₂ (fun a b ↦ unop a * unop b) h1 h2).trans (unop_mul_unop_one _)

/-- **`SL(2, ℤ/Nℤ)` acts by fractional linear maps**: on underlying meromorphic functions on
`X(N)`, `s.toGL` agrees with `TauCeti.modularFunctionActionZMod N s`. -/
theorem coe_unop_modularFunctionFieldAction_toGL (s : SL(2, ZMod N)) (F : modularFunctionField N) :
    (unop (modularFunctionFieldAction N s.toGL) F :
        MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) =
      unop (modularFunctionActionZMod N s) F := by
  rw [modularFunctionFieldAction_toGL, coe_unop_modularFunctionFieldSLAction]

/-- **Explicit fractional linear formula on `SL(2, ℤ)`**: the reduction modulo `N` of `γ ∈ SL(2, ℤ)`
sends `F ∈ F_N` to the function whose value at the orbit of `τ` is `F` at the orbit of `γ • τ`. -/
theorem coe_unop_modularFunctionFieldAction_toGL_map_ofQuotient (γ : SL(2, ℤ))
    (F : modularFunctionField N) (τ : ℍ) :
    (unop (modularFunctionFieldAction N
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).toGL) F :
        MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient)
        (ofQuotient (Quotient.mk _ τ)) =
      (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient)
        (ofQuotient (Quotient.mk _ (γ • τ))) := by
  rw [coe_unop_modularFunctionFieldAction_toGL, modularFunctionActionZMod_map,
    modularFunctionAction_apply_ofQuotient]

/-- On `diag(1, d)`, `modularFunctionFieldAction` restricts to `modularFunctionFieldDiagAction`. -/
@[simp]
theorem modularFunctionFieldAction_diagGL (d : (ZMod N)ˣ) :
    modularFunctionFieldAction N (diagGL ![1, d]) = modularFunctionFieldDiagAction N d := by
  refine unop_injective ?_
  have hdet : Matrix.GeneralLinearGroup.det (diagGL ![1, d]) = d := by
    rw [det_diagGL, Fin.prod_univ_two]
    simp
  have h1 : modularFunctionFieldSLAction N (slPart (diagGL ![1, d])) = 1 :=
    (congrArg (modularFunctionFieldSLAction N) (slPart_diagGL d)).trans
      (modularFunctionFieldSLAction N).map_one
  have h2 : modularFunctionFieldDiagAction N (Matrix.GeneralLinearGroup.det (diagGL ![1, d])) =
      modularFunctionFieldDiagAction N d :=
    congrArg (modularFunctionFieldDiagAction N) hdet
  exact (congrArg₂ (fun a b ↦ unop a * unop b) h1 h2).trans (unop_one_mul_unop _)

/-- **`diag(1, d)` acts on Fourier coefficients**: on the `q_N`-expansion at `∞`, `diag(1, d)`
applies `TauCeti.cyclotomicAut N d` (`ζ ↦ ζ ^ d.val`) coefficientwise. -/
theorem modularFunctionFieldLaurent_unop_modularFunctionFieldAction_diagGL (d : (ZMod N)ˣ)
    (F : modularFunctionField N) :
    modularFunctionFieldLaurent N (unop (modularFunctionFieldAction N (diagGL ![1, d])) F) =
      HahnSeries.mapRingHom (cyclotomicAut N d).toRingHom (modularFunctionFieldLaurent N F) := by
  rw [modularFunctionFieldAction_diagGL,
    modularFunctionFieldLaurent_unop_modularFunctionFieldDiagAction]

/-- Coefficientwise action of `diag(1, d)` on the Laurent `q_N`-expansion of `F ∈ F_N`. -/
theorem coeff_modularFunctionFieldLaurent_unop_modularFunctionFieldAction_diagGL (d : (ZMod N)ˣ)
    (F : modularFunctionField N) (n : ℤ) :
    (modularFunctionFieldLaurent N
        (unop (modularFunctionFieldAction N (diagGL ![1, d])) F)).coeff n =
      cyclotomicAut N d ((modularFunctionFieldLaurent N F).coeff n) := by
  rw [modularFunctionFieldLaurent_unop_modularFunctionFieldAction_diagGL,
    HahnSeries.coeff_mapRingHom]
  rfl

/-- **`GL(2, ℤ/Nℤ)` permutes the Fricke functions**: `g` sends `f_a` to `f_{a · g}`. -/
theorem unop_modularFunctionFieldAction_fricke (g : GL (Fin 2) (ZMod N)) (a : Fin 2 → ZMod N) :
    unop (modularFunctionFieldAction N g)
        ⟨frickeMeromorphicFunction a, frickeMeromorphicFunction_mem_modularFunctionField a⟩ =
      ⟨frickeMeromorphicFunction (a ᵥ* (g : Matrix (Fin 2) (Fin 2) (ZMod N))),
        frickeMeromorphicFunction_mem_modularFunctionField _⟩ :=
  glAut_fricke g a

/-- Underlying meromorphic-function form of the `GL(2, ℤ/Nℤ)` action on Fricke functions:
`g` sends `f_a` to `f_{a · g}`. -/
theorem coe_unop_modularFunctionFieldAction_fricke (g : GL (Fin 2) (ZMod N)) (a : Fin 2 → ZMod N) :
    (unop (modularFunctionFieldAction N g)
        ⟨frickeMeromorphicFunction a, frickeMeromorphicFunction_mem_modularFunctionField a⟩ :
        MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) =
      frickeMeromorphicFunction (a ᵥ* (g : Matrix (Fin 2) (Fin 2) (ZMod N))) :=
  congrArg Subtype.val (unop_modularFunctionFieldAction_fricke g a)

/-- **`GL(2, ℤ/Nℤ)` acts on constants in `ℚ(ζ_N)` through the determinant**: `g` acts on
`c ∈ ℚ(ζ_N)` by `cyclotomicAut N (det g)`. -/
theorem unop_modularFunctionFieldAction_algebraMap (g : GL (Fin 2) (ZMod N))
    (c : Subfield.closure {z : ℂ | z ^ N = 1}) :
    unop (modularFunctionFieldAction N g)
        ⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr c.2⟩ =
      ⟨algebraMap ℂ _ (cyclotomicAut N (Matrix.GeneralLinearGroup.det g) c),
        algebraMap_mem_modularFunctionField.mpr
          (cyclotomicAut N (Matrix.GeneralLinearGroup.det g) c).2⟩ :=
  glAut_algebraMap g c

/-- On an `N`-th root of unity `z ∈ ℂ`, `g ∈ GL(2, ℤ/Nℤ)` raises `z` to the power `(det g).val`. -/
theorem coe_unop_modularFunctionFieldAction_algebraMap_of_pow_eq_one (g : GL (Fin 2) (ZMod N))
    {z : ℂ} (hz : z ^ N = 1) :
    (unop (modularFunctionFieldAction N g)
        ⟨algebraMap ℂ _ z, algebraMap_mem_modularFunctionField.mpr (Subfield.subset_closure hz)⟩ :
        MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) =
      algebraMap ℂ _ (z ^ (Matrix.GeneralLinearGroup.det g : ZMod N).val) := by
  let c : Subfield.closure {w : ℂ | w ^ N = 1} := ⟨z, Subfield.subset_closure hz⟩
  have h := congrArg Subtype.val (unop_modularFunctionFieldAction_algebraMap g c)
  dsimp only at h
  rw [cyclotomicAut_apply_of_pow_eq_one (Matrix.GeneralLinearGroup.det g) (x := c) hz] at h
  exact h

end GLAction

/-! ### Negation invariance and exact kernel (including `N = 2`) -/

section Kernel

/-- `-g` acts on `F_N` in the same way as `g`, since `-I ∈ SL(2, ℤ/Nℤ)` acts trivially. -/
@[simp]
theorem modularFunctionFieldAction_neg (g : GL (Fin 2) (ZMod N)) :
    modularFunctionFieldAction N (-g) = modularFunctionFieldAction N g := by
  have hneg : (-1 : GL (Fin 2) (ZMod N)) = (-1 : SL(2, ZMod N)).toGL := Units.ext (by simp)
  have h1 : modularFunctionFieldAction N (-1 : GL (Fin 2) (ZMod N)) = 1 := by
    rw [hneg, modularFunctionFieldAction_toGL]
    refine unop_injective (AlgEquiv.ext fun F ↦ Subtype.ext ?_)
    change unop (modularFunctionActionZMod N (-1)) F = F
    rw [modularFunctionActionZMod_neg, (modularFunctionActionZMod N).map_one]
    rfl
  exact (congrArg (modularFunctionFieldAction N) (neg_one_mul g).symm).trans <|
    ((modularFunctionFieldAction N).map_mul (-1) g).trans <|
    (congrArg (· * modularFunctionFieldAction N g) h1).trans (one_mul _)

/-- **Kernel membership**: `g ∈ GL(2, ℤ/Nℤ)` acts trivially on `F_N` if and only if `g = ±I`. -/
theorem mem_ker_modularFunctionFieldAction_iff (g : GL (Fin 2) (ZMod N)) :
    g ∈ (modularFunctionFieldAction N).ker ↔ g = 1 ∨ g = -1 := by
  rw [MonoidHom.mem_ker]
  refine ⟨fun hg ↦ ?_, ?_⟩
  · rw [← Matrix.GeneralLinearGroup.forall_weightedG2_single_vecMul_apply_eq_iff g UpperHalfPlane.I]
    intro a ha
    have hga : a ᵥ* (g : Matrix (Fin 2) (Fin 2) (ZMod N)) ≠ 0 := fun h0 ↦ ha <| by
      apply Matrix.vecMul_injective_of_isUnit g.isUnit
      simpa using h0
    have hfa : frickeMeromorphicFunction (a ᵥ* (g : Matrix (Fin 2) (Fin 2) (ZMod N))) =
        frickeMeromorphicFunction a := by
      rw [← coe_unop_modularFunctionFieldAction_fricke, hg, unop_one]
      rfl
    rcases (frickeMeromorphicFunction_eq_iff hga ha).mp hfa with heq | heq
    · rw [heq]
    · rw [heq, EisensteinSeries.weightedG2_single_neg]
  · rintro (rfl | rfl)
    · exact map_one _
    · rw [modularFunctionFieldAction_neg, map_one]

/-- **The kernel of the `GL(2, ℤ/Nℤ)` action is `{±I}`**, i.e. `Subgroup.zpowers (-1)`. -/
theorem ker_modularFunctionFieldAction :
    (modularFunctionFieldAction N).ker = Subgroup.zpowers (-1 : GL (Fin 2) (ZMod N)) := by
  ext g
  rw [mem_ker_modularFunctionFieldAction_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩
  · rintro ⟨k, rfl⟩
    have hsq : (-1 : GL (Fin 2) (ZMod N)) ^ (2 : ℤ) = 1 := by
      rw [zpow_two, neg_mul_neg, one_mul]
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, hsq, one_zpow]
    · right
      rw [zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]

/-- At level `N = 2`, where `±I` coincide, the `GL(2, ℤ/2ℤ)` action has trivial kernel. -/
theorem ker_modularFunctionFieldAction_level_two :
    (modularFunctionFieldAction 2).ker = ⊥ := by
  have hneg : (-1 : GL (Fin 2) (ZMod 2)) = 1 :=
    Units.ext (by ext i j; simp [ZMod.neg_eq_self_mod_two])
  rw [ker_modularFunctionFieldAction, hneg, Subgroup.zpowers_one_eq_bot]

/-- At level `N = 2`, the `GL(2, ℤ/2ℤ)` action on `F₂` is faithful. -/
theorem modularFunctionFieldAction_level_two_injective :
    Function.Injective (modularFunctionFieldAction 2) :=
  (MonoidHom.ker_eq_bot_iff _).mp ker_modularFunctionFieldAction_level_two

end Kernel

/-! ### Fixed-field statements -/

section FixedField

/-- **Elements of `F_N` fixed by `SL(2, ℤ/Nℤ)`**: a function in `F_N` is fixed by every
`s ∈ SL(2, ℤ/Nℤ)` exactly when it lies in `ℚ(ζ_N)(j)`. -/
theorem forall_unop_modularFunctionFieldAction_toGL_eq_iff (F : modularFunctionField N) :
    (∀ s : SL(2, ZMod N), unop (modularFunctionFieldAction N s.toGL) F = F) ↔
      (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) ∈
        Subfield.closure (insert
          (Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
            ModularGroup.jMeromorphicFunction)
          (algebraMap ℂ _ '' Subfield.closure {z : ℂ | z ^ N = 1})) := by
  rw [← modularFunctionField_inf_fixedField_eq_closure]
  constructor
  · intro h
    refine ⟨F.2, (IntermediateField.mem_fixedField_iff _ _).mpr fun σ hσ ↦ ?_⟩
    obtain ⟨s, hs⟩ := Subgroup.mem_unop.mp hσ
    rw [← unop_op σ, ← hs, ← coe_unop_modularFunctionFieldAction_toGL]
    exact congrArg Subtype.val (h s)
  · rintro ⟨_, h⟩ s
    refine Subtype.ext ?_
    rw [coe_unop_modularFunctionFieldAction_toGL]
    exact (IntermediateField.mem_fixedField_iff _ _).mp h _ (Subgroup.mem_unop.mpr ⟨s, op_unop _⟩)

/-- Pushing `ℚ(j)(ℚ(ζ_N))` out of `F_N` into the ambient meromorphic function field recovers
`Subfield.closure (insert j (algebraMap ℂ _ '' ℚ(ζ_N)))`. -/
private theorem map_adjoin_cyclotomic_eq :
    (IntermediateField.adjoin (modularFunctionFieldBase N)
        ((fun c : Subfield.closure {z : ℂ | z ^ N = 1} ↦
          (⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr c.2⟩ :
            modularFunctionField N)) '' Set.univ)).toSubfield.map
        (modularFunctionField N).subtype =
      Subfield.closure (insert
        (Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
          ModularGroup.jMeromorphicFunction)
        (algebraMap ℂ _ '' Subfield.closure {z : ℂ | z ^ N = 1})) := by
  set Kset : Set (modularFunctionField N) :=
    (fun c : Subfield.closure {z : ℂ | z ^ N = 1} ↦
      (⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr c.2⟩ :
        modularFunctionField N)) '' Set.univ
  set jF : modularFunctionField N :=
    ⟨Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
        ModularGroup.jMeromorphicFunction,
      compactifiedQuotientComap_jMeromorphicFunction_mem_modularFunctionField⟩
  have hsub : (IntermediateField.adjoin (modularFunctionFieldBase N) Kset).toSubfield =
      Subfield.closure (insert jF Kset) := by
    refine le_antisymm ?_ (Subfield.closure_le.mpr ?_)
    · have hbase : ∀ r : modularFunctionFieldBase N, (r : modularFunctionField N) ∈
          Subfield.closure (insert jF Kset) := fun r ↦
        (modularFunctionFieldBase_eq_closure (N := N) ▸ Subfield.closure_mono
          (Set.singleton_subset_iff.mpr (Set.mem_insert jF Kset))) r.2
      change IntermediateField.adjoin (modularFunctionFieldBase N) Kset ≤
        (Subfield.closure (insert jF Kset)).toIntermediateField hbase
      exact IntermediateField.adjoin_le_iff.mpr fun x hx ↦
        Subfield.subset_closure (Set.mem_insert_of_mem jF hx)
    · rw [Set.insert_subset_iff]
      exact ⟨IntermediateField.algebraMap_mem _ (⟨jF, j_mem_modularFunctionFieldBase⟩ :
          modularFunctionFieldBase N), IntermediateField.subset_adjoin _ _⟩
  rw [hsub, RingHom.map_field_closure, Set.image_insert_eq]
  refine congrArg Subfield.closure (congrArg (insert _) ?_)
  ext x
  exact ⟨by rintro ⟨_, ⟨c, -, rfl⟩, rfl⟩; exact ⟨c, c.2, rfl⟩,
    by rintro ⟨c, hc, rfl⟩; exact ⟨⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr hc⟩,
      ⟨⟨c, hc⟩, trivial, rfl⟩, rfl⟩⟩

/-- **The fixed field of `SL(2, ℤ/Nℤ)` inside `F_N` is `ℚ(ζ_N)(j)`**, obtained by adjoining the
cyclotomic constants `ℚ(ζ_N)` to `ℚ(j) = modularFunctionFieldBase N`. -/
theorem fixedField_unop_range_modularFunctionFieldSLAction :
    IntermediateField.fixedField (modularFunctionFieldSLAction N).range.unop =
      IntermediateField.adjoin (modularFunctionFieldBase N)
        ((fun c : Subfield.closure {z : ℂ | z ^ N = 1} ↦
            (⟨algebraMap ℂ _ c, algebraMap_mem_modularFunctionField.mpr c.2⟩ :
              modularFunctionField N)) '' Set.univ) := by
  ext F
  constructor
  · intro hF
    have hSL : ∀ s : SL(2, ZMod N), unop (modularFunctionFieldAction N s.toGL) F = F := fun s ↦ by
      rw [modularFunctionFieldAction_toGL]
      exact (IntermediateField.mem_fixedField_iff _ _).mp hF _
        (Subgroup.mem_unop.mpr ⟨s, op_unop _⟩)
    have hmem := (forall_unop_modularFunctionFieldAction_toGL_eq_iff F).mp hSL
    rw [← map_adjoin_cyclotomic_eq] at hmem
    obtain ⟨G, hG, hGF⟩ := hmem
    exact (IntermediateField.mem_toSubfield _ _).mp ((Subtype.ext hGF) ▸ hG)
  · intro hF
    have hmem : (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) ∈
        Subfield.closure (insert
          (Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
            ModularGroup.jMeromorphicFunction)
          (algebraMap ℂ _ '' Subfield.closure {z : ℂ | z ^ N = 1})) := by
      rw [← map_adjoin_cyclotomic_eq]
      exact ⟨F, (IntermediateField.mem_toSubfield _ _).mpr hF, rfl⟩
    have hSL := (forall_unop_modularFunctionFieldAction_toGL_eq_iff F).mpr hmem
    refine (IntermediateField.mem_fixedField_iff _ _).mpr fun σ hσ ↦ ?_
    obtain ⟨s, hs⟩ := Subgroup.mem_unop.mp hσ
    rw [← unop_op σ, ← hs, ← modularFunctionFieldAction_toGL]
    exact hSL s

/-- **Elements of `F_N` fixed by `diag(1, d)`**: a function in `F_N` is fixed by every diagonal
matrix `diag(1, d)` (`d ∈ (ℤ/Nℤ)ˣ`) exactly when its Laurent `q_N`-expansion at `∞` has rational
coefficients. -/
theorem forall_unop_modularFunctionFieldAction_diagGL_eq_iff (F : modularFunctionField N) :
    (∀ d : (ZMod N)ˣ, unop (modularFunctionFieldAction N (diagGL ![1, d])) F = F) ↔
      (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) ∈
        coeffSubfield (cuspDatumInftyGamma N) ⊥ := by
  rw [mem_coeffSubfield]
  constructor
  · intro h n
    rw [← coe_coeff_modularFunctionFieldLaurent, ← forall_cyclotomicAut_apply_eq_iff]
    intro d
    rw [← coeff_modularFunctionFieldLaurent_unop_modularFunctionFieldAction_diagGL, h d]
  · intro h d
    apply modularFunctionFieldLaurent_injective
    refine HahnSeries.ext (funext fun n ↦ ?_)
    rw [coeff_modularFunctionFieldLaurent_unop_modularFunctionFieldAction_diagGL]
    exact forall_cyclotomicAut_apply_eq_iff.mpr
      (by rw [coe_coeff_modularFunctionFieldLaurent]; exact h n) d

/-- **Elements of `F_N` fixed by `GL(2, ℤ/Nℤ)`**: a function in `F_N` is fixed by every
`g ∈ GL(2, ℤ/Nℤ)` exactly when it lies in `ℚ(j) = modularFunctionFieldBase N`. -/
theorem forall_unop_modularFunctionFieldAction_eq_iff (F : modularFunctionField N) :
    (∀ g : GL (Fin 2) (ZMod N), unop (modularFunctionFieldAction N g) F = F) ↔
      F ∈ modularFunctionFieldBase N := by
  constructor
  · intro h
    have hSL : ∀ s : SL(2, ZMod N), unop (modularFunctionActionZMod N s) F = F := fun s ↦ by
      rw [← coe_unop_modularFunctionFieldAction_toGL, h s.toGL]
    obtain ⟨G, hGF⟩ := forall_unop_modularFunctionActionZMod_apply_eq_iff.mp hSL
    have hbot : (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) ∈
        coeffSubfield (cuspDatumInftyGamma N) ⊥ :=
      (forall_unop_modularFunctionFieldAction_diagGL_eq_iff F).mp fun d ↦ h (diagGL ![1, d])
    have hG : G ∈ coeffSubfield ModularGroup.cuspDatumInfty ⊥ :=
      (compactifiedQuotientComap_mem_coeffSubfield_iff _ (by simp)).mp (hGF.symm ▸ hbot)
    exact mem_modularFunctionFieldBase_iff.mpr
      ⟨⟨G, hG⟩, Subtype.ext ((coe_modularFunctionFieldMapOfLevelOne_apply ⟨G, hG⟩).trans hGF)⟩
  · intro hF g
    exact (unop (modularFunctionFieldAction N g)).commutes ⟨F, hF⟩

/-- **The fixed field of `GL(2, ℤ/Nℤ)` in `F_N` is `ℚ(j)`.** Inside `F_N` viewed over
`modularFunctionFieldBase N`, the fixed field of the `GL(2, ℤ/Nℤ)` action is `⊥`. -/
theorem fixedField_unop_range_modularFunctionFieldAction :
    IntermediateField.fixedField (modularFunctionFieldAction N).range.unop = ⊥ := by
  ext F
  rw [IntermediateField.mem_fixedField_iff, IntermediateField.mem_bot]
  have hiff : (∀ σ ∈ (modularFunctionFieldAction N).range.unop, σ F = F) ↔
      ∀ g : GL (Fin 2) (ZMod N), unop (modularFunctionFieldAction N g) F = F := by
    refine ⟨fun h g ↦ h _ (Subgroup.mem_unop.mpr ⟨g, op_unop _⟩), fun h σ hσ ↦ ?_⟩
    obtain ⟨g, hg⟩ := Subgroup.mem_unop.mp hσ
    rw [← unop_op σ, ← hg]
    exact h g
  rw [hiff, forall_unop_modularFunctionFieldAction_eq_iff]
  exact ⟨fun hF ↦ ⟨⟨F, hF⟩, rfl⟩, fun ⟨x, hx⟩ ↦ hx ▸ x.2⟩

end FixedField

/-! ### Galois group of `F_N / ℚ(j)` and quotient isomorphism -/

section Galois

/-- If a finite subgroup of `K`-automorphisms of `M` has fixed field `⊥`, then `M / K` is finite
dimensional (Artin's theorem). -/
private theorem finiteDimensional_of_fixedField_eq_bot {K M : Type*} [Field K] [Field M]
    [Algebra K M] (H : Subgroup (M ≃ₐ[K] M)) [Finite H]
    (h : IntermediateField.fixedField H = ⊥) : FiniteDimensional K M := by
  have hbot : FiniteDimensional (⊥ : IntermediateField K M) M := by
    rw [← h]
    exact IntermediateField.finiteDimensional_fixedField H
  have hbase : FiniteDimensional K (⊥ : IntermediateField K M) :=
    (IntermediateField.botEquiv K M).symm.toLinearEquiv.finiteDimensional
  exact Module.Finite.trans (⊥ : IntermediateField K M) M

/-- The image of `GL(2, ℤ/Nℤ)` in `Aut(F_N / ℚ(j))` is finite. -/
instance finite_unop_range_modularFunctionFieldAction :
    Finite (modularFunctionFieldAction N).range.unop := by
  classical
  exact Finite.of_injective
    (fun g ↦ (⟨op g.1, g.2⟩ : (modularFunctionFieldAction N).range))
    (fun _ _ h ↦ Subtype.ext (MulOpposite.op_injective (congrArg Subtype.val h)))

/-- `F_N` is a finite extension of `ℚ(j) = modularFunctionFieldBase N`. -/
instance finiteDimensional_modularFunctionField :
    FiniteDimensional (modularFunctionFieldBase N) (modularFunctionField N) :=
  finiteDimensional_of_fixedField_eq_bot (modularFunctionFieldAction N).range.unop
    fixedField_unop_range_modularFunctionFieldAction

/-- `F_N` is a Galois extension of `ℚ(j) = modularFunctionFieldBase N`. -/
instance isGalois_modularFunctionField :
    IsGalois (modularFunctionFieldBase N) (modularFunctionField N) := by
  rw [← isGalois_iff_isGalois_bot, ← fixedField_unop_range_modularFunctionFieldAction]
  exact IntermediateField.isGalois_fixedField _

/-- Every `ℚ(j)`-automorphism of `F_N` arises from the action of some `g ∈ GL(2, ℤ/Nℤ)`. -/
theorem modularFunctionFieldAction_surjective :
    Function.Surjective (modularFunctionFieldAction N) := by
  have htop : (modularFunctionFieldAction N).range.unop = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField_of_finite
        (modularFunctionFieldAction N).range.unop,
      fixedField_unop_range_modularFunctionFieldAction, IntermediateField.fixingSubgroup_bot]
  intro σ
  have hmem : unop σ ∈ (modularFunctionFieldAction N).range.unop := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨g, hg⟩ := Subgroup.mem_unop.mp hmem
  exact ⟨g, hg.trans (op_unop σ)⟩

omit [NeZero N] in
/-- `{±I} = Subgroup.zpowers (-1)` is a normal subgroup of `GL(2, ℤ/Nℤ)`, being central. -/
instance normal_zpowers_neg_one_gl (N : ℕ) :
    (Subgroup.zpowers (-1 : GL (Fin 2) (ZMod N))).Normal :=
  Subgroup.normal_of_le_center <| Subgroup.zpowers_le.mpr <|
    Subgroup.mem_center_iff.mpr fun _ ↦ by simp

variable (N) in
/-- **The Galois group isomorphism `GL(2, ℤ/Nℤ) / {±I} ≃* Gal(F_N / ℚ(j))ᵐᵒᵖ`.**
This holds for every positive level `N`, including `N = 1` and `N = 2`. -/
def modularFunctionFieldActionQuotientEquiv :
    (GL (Fin 2) (ZMod N) ⧸ Subgroup.zpowers (-1 : GL (Fin 2) (ZMod N))) ≃*
      (modularFunctionField N ≃ₐ[modularFunctionFieldBase N] modularFunctionField N)ᵐᵒᵖ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_modularFunctionFieldAction (N := N)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (modularFunctionFieldAction N)
      modularFunctionFieldAction_surjective)

/-- `modularFunctionFieldActionQuotientEquiv N` evaluates on cosets via
`modularFunctionFieldAction N`. -/
@[simp]
theorem modularFunctionFieldActionQuotientEquiv_mk (g : GL (Fin 2) (ZMod N)) :
    modularFunctionFieldActionQuotientEquiv N (QuotientGroup.mk g) =
      modularFunctionFieldAction N g := by
  rfl

/-- **Level-two Galois group isomorphism `GL(2, ℤ/2ℤ) ≃* Gal(F₂ / ℚ(j))ᵐᵒᵖ`**: at `N = 2`,
`-I = I`, so `GL(2, ℤ/2ℤ)` itself is opposite-isomorphic to the Galois group of `F₂ / ℚ(j)`. -/
def modularFunctionFieldActionLevelTwoEquiv :
    GL (Fin 2) (ZMod 2) ≃*
      (modularFunctionField 2 ≃ₐ[modularFunctionFieldBase 2] modularFunctionField 2)ᵐᵒᵖ :=
  MulEquiv.ofBijective (modularFunctionFieldAction 2)
    ⟨modularFunctionFieldAction_level_two_injective, modularFunctionFieldAction_surjective⟩

/-- `modularFunctionFieldActionLevelTwoEquiv` is `modularFunctionFieldAction 2`. -/
@[simp]
theorem modularFunctionFieldActionLevelTwoEquiv_apply (g : GL (Fin 2) (ZMod 2)) :
    modularFunctionFieldActionLevelTwoEquiv g = modularFunctionFieldAction 2 g := by
  rfl

/-- **The degree `[F_N : ℚ(j)]`** equals the order of `GL(2, ℤ/Nℤ) / {±I}`. -/
theorem finrank_modularFunctionField :
    Module.finrank (modularFunctionFieldBase N) (modularFunctionField N) =
      Nat.card (GL (Fin 2) (ZMod N) ⧸ Subgroup.zpowers (-1 : GL (Fin 2) (ZMod N))) := by
  rw [← IsGalois.card_aut_eq_finrank]
  exact (Nat.card_congr ((modularFunctionFieldActionQuotientEquiv N).toEquiv.trans
    MulOpposite.opEquiv.symm)).symm

/-- At level `N = 2`, the degree `[F₂ : ℚ(j)]` equals `|GL(2, ℤ/2ℤ)|`. -/
theorem finrank_modularFunctionField_level_two :
    Module.finrank (modularFunctionFieldBase 2) (modularFunctionField 2) =
      Nat.card (GL (Fin 2) (ZMod 2)) := by
  rw [← IsGalois.card_aut_eq_finrank]
  exact (Nat.card_congr (modularFunctionFieldActionLevelTwoEquiv.toEquiv.trans
    MulOpposite.opEquiv.symm)).symm

end Galois

end TauCeti
