/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Comparison
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Scheme
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.Data.ZMod.Pow

/-!
# The diamond action of `(ℤ/Nℤ)ˣ` on points and schemes of exact order `N`

Let `E` be an elliptic curve over a scheme `S` and let `N : ℕ`. If an `S`-point `P` of `E` is
killed by `N`, then for every unit `u : (ZMod N)ˣ` multiplication by `u` permutes `ZMod N` and
therefore leaves the divisor `[P] + [2P] + ⋯ + [NP]` unchanged:

  `[uP] + [2(uP)] + ⋯ + [N(uP)] = [P] + [2P] + ⋯ + [NP]`

(`EllipticCurveGeom.multiplesDivisor_zpow_unit_of_pow_eq_one`). Using `ZMod.cast : ZMod N → ℤ` to
lift `u : ZMod N` to an integer exponent makes this statement uniform across all `N : ℕ`, including
`N = 0` (where `(ZMod 0)ˣ = ℤˣ = {±1}`) and `N = 1`.

Two consequences follow over an arbitrary base scheme `S`, with no invertibility assumption on `N`:

1. **Invariance of exact order.** Both Drinfeld exact order (`EllipticCurveGeom.IsOfExactOrder`)
   and naive exact order (`EllipticCurveGeom.IsOfNaiveExactOrder`) are preserved by `P ↦ uP`
   (`EllipticCurveGeom.IsOfExactOrder.zpow_unit`,
   `EllipticCurveGeom.IsOfNaiveExactOrder.zpow_unit`), and when `P ^ N = 1` the condition on `uP`
   is equivalent to that on `P`. Note that `P ^ N = 1` cannot be omitted in the backward
   implication for Drinfeld exact order: over `𝔽₃`, a non-trivial `2`-torsion point `P` satisfies
   `P ^ ((-1 : ZMod 3).cast : ℤ) = P ^ 2 = 1`, which has Drinfeld exact order `3`, whereas `P`
   itself is not killed by `3`. By contrast, negation `P ↦ P⁻¹` preserves and reflects both notions
   unconditionally (`EllipticCurveGeom.isOfExactOrder_inv_iff`,
   `EllipticCurveGeom.isOfNaiveExactOrder_inv_iff`).
2. **The diamond action on the exact-order scheme.** Transporting `P ↦ uP` across the universal
   property `EllipticCurveGeom.exactOrderPointsEquivOfIsPullback` of `E.exactOrderScheme N` gives a
   group action `(ZMod N)ˣ →* Aut (E.exactOrderScheme N)` over `S`
   (`EllipticCurveGeom.exactOrderSchemeAction`), uniquely characterised by carrying the closed
   immersion `E.exactOrderSchemeι N` to `(E.exactOrderSchemeι N) ^ ((u : ZMod N).cast : ℤ)`.
   Over any nonempty `S`-scheme `T` on whose residue fields `N` is nonzero, this action is free on
   `T`-valued points (`EllipticCurveGeom.eq_one_of_comp_exactOrderSchemeAction_hom_eq`), without
   requiring `N` to be invertible on `S` itself.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exactOrderSchemeAction E N`: the diamond action
  `(ZMod N)ˣ →* Aut (E.exactOrderScheme N)` on the scheme of points of exact order `N`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.multiplesDivisor_zpow_unit_of_pow_eq_one`: if
  `P ^ N = 1`, then `uP` and `P` generate the same divisor `[P] + ⋯ + [NP]` for `u : (ZMod N)ˣ`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsOfExactOrder.zpow_unit` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOfExactOrder_zpow_unit_iff`: Drinfeld exact order
  under `P ↦ uP`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsOfNaiveExactOrder.zpow_unit` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOfNaiveExactOrder_zpow_unit_iff`: naive exact order
  under `x ↦ ux`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exactOrderSchemeAction_hom_comp_exactOrderSchemeι`:
  the automorphism of `E.exactOrderScheme N` attached to `u` acts on the universal inclusion as
  raising to `((u : ZMod N).cast : ℤ)`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.eq_one_of_isOfExactOrder_zpow_unit_eq_self` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.eq_one_of_comp_exactOrderSchemeAction_hom_eq`:
  freeness of the `(ℤ/Nℤ)ˣ`-action over nonempty schemes on which `N` is invertible.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, §1.4, §1.6, §3.2, and §7.4.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}

/-! ### Precomposition with integer powers in `Over S` -/

/-- Precomposing a point `x : Z ⟶ E` over `S` with `k : Z' ⟶ Z` commutes with integer powers in
the group of points. -/
theorem comp_zpow {Z Z' : Over S} (k : Z' ⟶ Z)
    (x : Z ⟶ Over.mk E.structureMap) (m : ℤ) :
    k ≫ (x ^ m) = (k ≫ x) ^ m :=
  let φ : (Z ⟶ Over.mk E.structureMap) →* (Z' ⟶ Over.mk E.structureMap) :=
    { toFun := (k ≫ ·)
      map_one' := comp_one k
      map_mul' := comp_mul k }
  map_zpow φ x m

/-! ### Invariance of `[P] + [2P] + ⋯ + [NP]` under `(ℤ/Nℤ)ˣ` -/

/-- When `N ≠ 0` and `P ^ N = 1`, the divisor `[P] + [2P] + ⋯ + [NP]` equals the divisor of all
residue multiples `P ^ x.val` indexed by `x : ZMod N`. -/
theorem multiplesDivisor_eq_pointsDivisor_zmod {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    {N : ℕ} [NeZero N] (hP : P ^ N = 1) :
    E.multiplesDivisor P N = E.pointsDivisor (fun x : ZMod N ↦ P ^ x.val) := by
  rw [multiplesDivisor_eq_pointsDivisor]
  let e : Fin N ≃ ZMod N := (ZMod.finEquiv N).toEquiv.trans (Equiv.addRight 1)
  have he : (fun a : Fin N ↦ P ^ (a.val + 1)) = (fun x : ZMod N ↦ P ^ x.val) ∘ e := by
    ext1 a
    dsimp only [Function.comp_apply, e, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe,
      RingEquiv.coe_toEquiv, Equiv.coe_addRight]
    rw [ZMod.finEquiv_apply, ← Nat.cast_one (R := ZMod N), ← Nat.cast_add, pow_val_natCast hP]
  rw [he]
  exact E.pointsDivisor_comp_equiv _ e

/-- **Unit multiples of an `N`-torsion point generate the same divisor.** If `P ^ N = 1`, then for
every unit `u : (ZMod N)ˣ` the point `P ^ ((u : ZMod N).cast : ℤ)` has the same divisor
`[P] + [2P] + ⋯ + [NP]` as `P`, for all `N : ℕ`. -/
theorem multiplesDivisor_zpow_unit_of_pow_eq_one {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    {N : ℕ} (hP : P ^ N = 1) (u : (ZMod N)ˣ) :
    E.multiplesDivisor (P ^ ((u : ZMod N).cast : ℤ)) N = E.multiplesDivisor P N := by
  rcases eq_or_ne N 0 with rfl | hN0
  · simp
  have : NeZero N := ⟨hN0⟩
  have hPu : (P ^ ((u : ZMod N).cast : ℤ)) ^ N = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hP, one_zpow]
  rw [multiplesDivisor_eq_pointsDivisor_zmod hPu, multiplesDivisor_eq_pointsDivisor_zmod hP]
  have hu : (fun x : ZMod N ↦ (P ^ ((u : ZMod N).cast : ℤ)) ^ x.val) =
      (fun x : ZMod N ↦ P ^ x.val) ∘ Units.mulLeft u := by
    ext1 x
    simp [zpow_zmod_cast_eq_pow_val, ← pow_val_mul hP]
  rw [hu]
  exact E.pointsDivisor_comp_equiv _ (Units.mulLeft u)

/-- For `N ≠ 0` and `P ^ N = 1`, `P ^ (u : ZMod N).val` and `P` generate the same divisor
`[P] + ⋯ + [NP]`. -/
theorem multiplesDivisor_pow_unit_of_pow_eq_one {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    {N : ℕ} [NeZero N] (hP : P ^ N = 1) (u : (ZMod N)ˣ) :
    E.multiplesDivisor (P ^ (u : ZMod N).val) N = E.multiplesDivisor P N := by
  rw [← zpow_zmod_cast_eq_pow_val, multiplesDivisor_zpow_unit_of_pow_eq_one hP u]

/-- If `P ^ N = 1`, then `-P` and `P` generate the same divisor `[P] + ⋯ + [NP]`. -/
theorem multiplesDivisor_inv_of_pow_eq_one {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    {N : ℕ} (hP : P ^ N = 1) :
    E.multiplesDivisor P⁻¹ N = E.multiplesDivisor P N := by
  rw [← zpow_zmod_cast_neg_one hP]
  exact multiplesDivisor_zpow_unit_of_pow_eq_one hP (-1)

/-- If `P` has exact order `N`, then `uP` and `P` generate the same cyclic subgroup divisor
`[P] + ⋯ + [NP]` for every `u : (ZMod N)ˣ`. -/
theorem IsOfExactOrder.multiplesDivisor_zpow_unit {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    {N : ℕ} (h : E.IsOfExactOrder P N) (u : (ZMod N)ˣ) :
    E.multiplesDivisor (P ^ ((u : ZMod N).cast : ℤ)) N = E.multiplesDivisor P N :=
  multiplesDivisor_zpow_unit_of_pow_eq_one h.pow_eq_one u

/-- If `P` has exact order `N ≠ 0`, then `P ^ (u : ZMod N).val` and `P` generate the same cyclic
subgroup divisor `[P] + ⋯ + [NP]`. -/
theorem IsOfExactOrder.multiplesDivisor_pow_unit {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    {N : ℕ} [NeZero N] (h : E.IsOfExactOrder P N) (u : (ZMod N)ˣ) :
    E.multiplesDivisor (P ^ (u : ZMod N).val) N = E.multiplesDivisor P N :=
  multiplesDivisor_pow_unit_of_pow_eq_one h.pow_eq_one u

/-- If `P` has exact order `N`, then `-P` and `P` generate the same cyclic subgroup divisor
`[P] + ⋯ + [NP]`. -/
theorem IsOfExactOrder.multiplesDivisor_inv {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    {N : ℕ} (h : E.IsOfExactOrder P N) :
    E.multiplesDivisor P⁻¹ N = E.multiplesDivisor P N :=
  multiplesDivisor_inv_of_pow_eq_one h.pow_eq_one

/-! ### Drinfeld exact order under `(ℤ/Nℤ)ˣ` -/

/-- Two points with the same `multiplesDivisor` simultaneously satisfy `IsOfExactOrder`. -/
private theorem isOfExactOrder_of_multiplesDivisor_eq
    {P Q : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ}
    (hdiv : E.multiplesDivisor Q N = E.multiplesDivisor P N) (hP : E.IsOfExactOrder P N) :
    E.IsOfExactOrder Q N := by
  let H (I : E.carrier.IdealSheafData) : Prop :=
    ∃ _ : GrpObj (Over.mk (I.subschemeι ≫ E.structureMap)),
      IsMonHom (Over.homMk I.subschemeι :
        Over.mk (I.subschemeι ≫ E.structureMap) ⟶ Over.mk E.structureMap)
  exact isOfExactOrder_def.mpr ((congrArg H hdiv.symm).mp (isOfExactOrder_def.mp hP))

/-- **Points of Drinfeld exact order `N` are closed under `(ℤ/Nℤ)ˣ`.** If `P` has exact order `N`,
then so does `P ^ ((u : ZMod N).cast : ℤ)` for every `u : (ZMod N)ˣ` and every `N : ℕ`. -/
theorem IsOfExactOrder.zpow_unit {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ}
    (h : E.IsOfExactOrder P N) (u : (ZMod N)ˣ) :
    E.IsOfExactOrder (P ^ ((u : ZMod N).cast : ℤ)) N :=
  isOfExactOrder_of_multiplesDivisor_eq (h.multiplesDivisor_zpow_unit u) h

/-- For an `N`-torsion point `P` (`P ^ N = 1`), `P ^ ((u : ZMod N).cast : ℤ)` has exact order `N`
if and only if `P` does. -/
theorem isOfExactOrder_zpow_unit_iff {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ}
    (hP : P ^ N = 1) (u : (ZMod N)ˣ) :
    E.IsOfExactOrder (P ^ ((u : ZMod N).cast : ℤ)) N ↔ E.IsOfExactOrder P N :=
  ⟨fun hu ↦ by simpa [zpow_zmod_cast_mul_inv hP u] using hu.zpow_unit u⁻¹, fun h ↦ h.zpow_unit u⟩

/-- For `N ≠ 0`, if `P` has exact order `N`, then so does `P ^ (u : ZMod N).val`. -/
theorem IsOfExactOrder.pow_unit {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ} [NeZero N]
    (h : E.IsOfExactOrder P N) (u : (ZMod N)ˣ) :
    E.IsOfExactOrder (P ^ (u : ZMod N).val) N := by
  rw [← zpow_zmod_cast_eq_pow_val]
  exact h.zpow_unit u

/-- For `N ≠ 0` and `P ^ N = 1`, `P ^ (u : ZMod N).val` has exact order `N` if and only if `P`
does. -/
theorem isOfExactOrder_pow_unit_iff {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ} [NeZero N]
    (hP : P ^ N = 1) (u : (ZMod N)ˣ) :
    E.IsOfExactOrder (P ^ (u : ZMod N).val) N ↔ E.IsOfExactOrder P N := by
  rw [← zpow_zmod_cast_eq_pow_val]
  exact isOfExactOrder_zpow_unit_iff hP u

/-- If `P` has exact order `N`, then so does its negative `P⁻¹`. -/
theorem IsOfExactOrder.inv {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ}
    (h : E.IsOfExactOrder P N) : E.IsOfExactOrder P⁻¹ N := by
  rw [← zpow_zmod_cast_neg_one h.pow_eq_one]
  exact h.zpow_unit (-1)

/-- Negating a point preserves and reflects Drinfeld exact order `N`, with no torsion hypothesis on
`P`. -/
@[simp]
theorem isOfExactOrder_inv_iff {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {N : ℕ} :
    E.IsOfExactOrder P⁻¹ N ↔ E.IsOfExactOrder P N :=
  ⟨fun h ↦ by simpa using h.inv, fun h ↦ h.inv⟩

/-! ### Naive exact order under `(ℤ/Nℤ)ˣ` -/

/-- **Points of naive exact order `N` are closed under `(ℤ/Nℤ)ˣ`.** For any scheme `Z` over `S`,
any `N : ℕ`, and any unit `u : (ZMod N)ˣ`, if `x : Z ⟶ E` has naive exact order `N` then so does
`x ^ ((u : ZMod N).cast : ℤ)`. -/
theorem IsOfNaiveExactOrder.zpow_unit {Z : Over S} {x : Z ⟶ Over.mk E.structureMap} {N : ℕ}
    (h : E.IsOfNaiveExactOrder x N) (u : (ZMod N)ˣ) :
    E.IsOfNaiveExactOrder (x ^ ((u : ZMod N).cast : ℤ)) N := by
  rw [isOfNaiveExactOrder_iff]
  refine ⟨by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.pow_eq_one,
    one_zpow], fun d hd hdN ↦ ?_⟩
  set y := x ^ ((u : ZMod N).cast : ℤ)
  have hxy : (y ^ d) ^ ((↑u⁻¹ : ZMod N).cast : ℤ) = x ^ d := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm (d : ℤ), zpow_mul, zpow_natCast,
      zpow_zmod_cast_mul_inv h.pow_eq_one u]
  have heq : equalizer.ι (y ^ d) 1 ≫ x ^ d = equalizer.ι (y ^ d) 1 ≫ 1 := by
    rw [← hxy, comp_zpow, equalizer.condition, comp_one, one_zpow]
  have := h.isEmpty_equalizer hd hdN
  exact Function.isEmpty (equalizer.lift (equalizer.ι (y ^ d) 1) heq).left

/-- For a point `x : Z ⟶ E` killed by `N`, `x ^ ((u : ZMod N).cast : ℤ)` has naive exact order `N`
if and only if `x` does. -/
theorem isOfNaiveExactOrder_zpow_unit_iff {Z : Over S} {x : Z ⟶ Over.mk E.structureMap} {N : ℕ}
    (hx : x ^ N = 1) (u : (ZMod N)ˣ) :
    E.IsOfNaiveExactOrder (x ^ ((u : ZMod N).cast : ℤ)) N ↔ E.IsOfNaiveExactOrder x N :=
  ⟨fun hu ↦ by simpa [zpow_zmod_cast_mul_inv hx u] using hu.zpow_unit u⁻¹, fun h ↦ h.zpow_unit u⟩

/-- For `N ≠ 0`, if `x` has naive exact order `N`, then so does `x ^ (u : ZMod N).val`. -/
theorem IsOfNaiveExactOrder.pow_unit {Z : Over S} {x : Z ⟶ Over.mk E.structureMap} {N : ℕ}
    [NeZero N] (h : E.IsOfNaiveExactOrder x N) (u : (ZMod N)ˣ) :
    E.IsOfNaiveExactOrder (x ^ (u : ZMod N).val) N := by
  rw [← zpow_zmod_cast_eq_pow_val]
  exact h.zpow_unit u

/-- For `N ≠ 0` and `x ^ N = 1`, `x ^ (u : ZMod N).val` has naive exact order `N` if and only if
`x` does. -/
theorem isOfNaiveExactOrder_pow_unit_iff {Z : Over S} {x : Z ⟶ Over.mk E.structureMap} {N : ℕ}
    [NeZero N] (hx : x ^ N = 1) (u : (ZMod N)ˣ) :
    E.IsOfNaiveExactOrder (x ^ (u : ZMod N).val) N ↔ E.IsOfNaiveExactOrder x N := by
  rw [← zpow_zmod_cast_eq_pow_val]
  exact isOfNaiveExactOrder_zpow_unit_iff hx u

/-- If `x` has naive exact order `N`, then so does its negative `x⁻¹`. -/
theorem IsOfNaiveExactOrder.inv {Z : Over S} {x : Z ⟶ Over.mk E.structureMap} {N : ℕ}
    (h : E.IsOfNaiveExactOrder x N) : E.IsOfNaiveExactOrder x⁻¹ N := by
  rw [← zpow_zmod_cast_neg_one h.pow_eq_one]
  exact h.zpow_unit (-1)

/-- Negating a point preserves and reflects naive exact order `N`, with no torsion hypothesis on
`x`. -/
@[simp]
theorem isOfNaiveExactOrder_inv_iff {Z : Over S} {x : Z ⟶ Over.mk E.structureMap} {N : ℕ} :
    E.IsOfNaiveExactOrder x⁻¹ N ↔ E.IsOfNaiveExactOrder x N :=
  ⟨fun h ↦ by simpa using h.inv, fun h ↦ h.inv⟩

/-! ### Freeness where `N` is invertible -/

/-- **Freeness on points of exact order `N` where `N` is invertible.** Over a nonempty scheme `S`
on whose residue fields `N` is nonzero, a unit `u : (ZMod N)ˣ` fixing an `S`-point `P` of exact
order `N` is `1`. -/
theorem eq_one_of_isOfExactOrder_zpow_unit_eq_self [Nonempty S] {N : ℕ}
    (hN : ∀ s : S, (N : S.residueField s) ≠ 0)
    {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} (hP : E.IsOfExactOrder P N)
    {u : (ZMod N)ˣ} (hu : P ^ ((u : ZMod N).cast : ℤ) = P) : u = 1 := by
  have : NeZero N := ⟨by
    rintro rfl
    obtain ⟨s⟩ := ‹Nonempty S›
    exact hN s Nat.cast_zero⟩
  have hPn : E.IsOfNaiveExactOrder P N := (isOfExactOrder_iff_isOfNaiveExactOrder hN).mp hP
  let φ := (zmodMonoidHomEquiv N _).symm ⟨P, hP.pow_eq_one⟩
  have hφ1 : φ (.ofAdd 1) = P := zmodMonoidHomEquiv_symm_apply_ofAdd_one _
  have hφ : E.IsFiberwiseInjective φ :=
    isFiberwiseInjective_iff_isOfNaiveExactOrder.mpr (by rwa [hφ1])
  have h_eq : φ (.ofAdd (u : ZMod N)) = φ (.ofAdd 1) := by
    rw [hφ1, zmodMonoidHomEquiv_symm_apply, ← zpow_zmod_cast_eq_pow_val]
    exact hu
  exact Units.ext (Multiplicative.ofAdd.injective (hφ.injective h_eq))

/-! ### The diamond action on the exact-order scheme -/

section Scheme

variable (E) (N : ℕ)

/-- The universal inclusion `E.exactOrderSchemeι N` is killed by `N` in the group of points of `E`
over `E.exactOrderScheme N`. -/
theorem exactOrderSchemeι_pow_eq_one : (E.exactOrderSchemeι N) ^ N = 1 := by
  have h := E.exactOrderSchemeι_comp_mulBy N
  rwa [comp_mulBy, zpow_natCast] at h

/-- The endomorphism of `E.exactOrderScheme N` over `S` sending the universal point `P_univ` of
exact order `N` to `P_univ ^ ((u : ZMod N).cast : ℤ)`. -/
private noncomputable def exactOrderSchemeEnd (u : (ZMod N)ˣ) :
    E.exactOrderScheme N ⟶ E.exactOrderScheme N :=
  let hg := E.isPullback_baseChange (E.exactOrderScheme N).hom
  let h0 : (E.baseChange (E.exactOrderScheme N).hom).zero ≫
      (E.baseChangeIso (E.exactOrderScheme N).hom).hom ≫ pullback.fst _ _ =
        (E.exactOrderScheme N).hom ≫ E.zero := by simp
  let P := (exactOrderPointsEquivOfIsPullback N hg h0).symm (𝟙 (E.exactOrderScheme N))
  exactOrderPointsEquivOfIsPullback N hg h0 ⟨P.1 ^ ((u : ZMod N).cast : ℤ), P.2.zpow_unit u⟩

private theorem exactOrderSchemeEnd_comp_ι (u : (ZMod N)ˣ) :
    exactOrderSchemeEnd E N u ≫ E.exactOrderSchemeι N =
      E.exactOrderSchemeι N ^ ((u : ZMod N).cast : ℤ) := by
  let hg := E.isPullback_baseChange (E.exactOrderScheme N).hom
  have h0 : (E.baseChange (E.exactOrderScheme N).hom).zero ≫
      (E.baseChangeIso (E.exactOrderScheme N).hom).hom ≫ pullback.fst _ _ =
        (E.exactOrderScheme N).hom ≫ E.zero := by simp
  let P := (exactOrderPointsEquivOfIsPullback N hg h0).symm (𝟙 (E.exactOrderScheme N))
  have hP : pointsBaseChangeEquiv hg h0 P.1 = E.exactOrderSchemeι N :=
    Over.OverMorphism.ext <| by
      rw [pointsBaseChangeEquiv_left]
      simpa [P] using exactOrderPointsEquivOfIsPullback_symm_apply_left_comp hg h0 (𝟙 _)
  refine Over.OverMorphism.ext ?_
  dsimp only [exactOrderSchemeEnd]
  rw [Over.comp_left, exactOrderSchemeι_left,
    exactOrderPointsEquivOfIsPullback_apply_left_comp hg h0,
    ← pointsBaseChangeEquiv_left hg h0, map_zpow, hP]

private theorem exactOrderSchemeEnd_one : exactOrderSchemeEnd E N 1 = 𝟙 (E.exactOrderScheme N) := by
  refine (cancel_mono (E.exactOrderSchemeι N)).mp ?_
  rw [exactOrderSchemeEnd_comp_ι, Category.id_comp, Units.val_one,
    zpow_zmod_cast_one (E.exactOrderSchemeι_pow_eq_one N)]

private theorem exactOrderSchemeEnd_comp (u v : (ZMod N)ˣ) :
    exactOrderSchemeEnd E N u ≫ exactOrderSchemeEnd E N v = exactOrderSchemeEnd E N (u * v) := by
  refine (cancel_mono (E.exactOrderSchemeι N)).mp ?_
  rw [Category.assoc, exactOrderSchemeEnd_comp_ι, comp_zpow, exactOrderSchemeEnd_comp_ι,
    ← zpow_zmod_cast_mul (E.exactOrderSchemeι_pow_eq_one N), ← Units.val_mul,
    exactOrderSchemeEnd_comp_ι]

/-- **The diamond action on the exact-order scheme** (Katz–Mazur, §1.6 and §7.4). A unit
`u : (ZMod N)ˣ` acts on `E.exactOrderScheme N` over `S` by sending the universal point `P` of exact
order `N` to `uP` (`exactOrderSchemeAction_hom_comp_exactOrderSchemeι`). No hypothesis is placed on
`S` or `N`. -/
noncomputable def exactOrderSchemeAction : (ZMod N)ˣ →* Aut (E.exactOrderScheme N) where
  toFun u := Aut.of
    { hom := exactOrderSchemeEnd E N u
      inv := exactOrderSchemeEnd E N u⁻¹
      hom_inv_id := (exactOrderSchemeEnd_comp E N u u⁻¹).trans <| by
        rw [mul_inv_cancel, exactOrderSchemeEnd_one]
      inv_hom_id := (exactOrderSchemeEnd_comp E N u⁻¹ u).trans <| by
        rw [inv_mul_cancel, exactOrderSchemeEnd_one] }
  map_one' := by
    apply Aut.ext
    rw [Aut.one_asIso]
    exact Iso.ext (exactOrderSchemeEnd_one E N)
  map_mul' u v := by
    apply Aut.ext
    rw [Aut.mul_asIso]
    exact Iso.ext <| (congrArg (exactOrderSchemeEnd E N) (mul_comm u v)).trans
      (exactOrderSchemeEnd_comp E N v u).symm

variable {E N}

/-- The diamond automorphism of `E.exactOrderScheme N` attached to `u : (ZMod N)ˣ` carries the
inclusion `E.exactOrderSchemeι N` to `(E.exactOrderSchemeι N) ^ ((u : ZMod N).cast : ℤ)`. -/
@[reassoc (attr := simp)]
theorem exactOrderSchemeAction_hom_comp_exactOrderSchemeι (u : (ZMod N)ˣ) :
    (E.exactOrderSchemeAction N u).asIso.hom ≫ E.exactOrderSchemeι N =
      E.exactOrderSchemeι N ^ ((u : ZMod N).cast : ℤ) :=
  exactOrderSchemeEnd_comp_ι E N u

/-- The inverse diamond automorphism of `E.exactOrderScheme N` attached to `u : (ZMod N)ˣ` carries
`E.exactOrderSchemeι N` to `(E.exactOrderSchemeι N) ^ ((↑u⁻¹ : ZMod N).cast : ℤ)`. -/
@[reassoc (attr := simp)]
theorem exactOrderSchemeAction_inv_comp_exactOrderSchemeι (u : (ZMod N)ˣ) :
    (E.exactOrderSchemeAction N u).asIso.inv ≫ E.exactOrderSchemeι N =
      E.exactOrderSchemeι N ^ ((↑u⁻¹ : ZMod N).cast : ℤ) :=
  exactOrderSchemeEnd_comp_ι E N u⁻¹

/-- The diamond automorphism for `-1 : (ZMod N)ˣ` negates the inclusion of the exact-order scheme
in `E`. -/
theorem exactOrderSchemeAction_neg_one_hom_comp_exactOrderSchemeι :
    (E.exactOrderSchemeAction N (-1)).asIso.hom ≫ E.exactOrderSchemeι N =
      (E.exactOrderSchemeι N)⁻¹ := by
  rw [exactOrderSchemeAction_hom_comp_exactOrderSchemeι, Units.val_neg, Units.val_one,
    zpow_zmod_cast_neg_one (E.exactOrderSchemeι_pow_eq_one N)]

/-- **Compatibility of `exactOrderPointsEquivOfIsPullback` with the diamond action.** Under the
equivalence between points of exact order `N` on a base change `E'` of `E` along `T ⟶ S` and
morphisms `T ⟶ E.exactOrderScheme N`, replacing `P` by `P ^ ((u : ZMod N).cast : ℤ)` postcomposes
the classifying morphism with `(E.exactOrderSchemeAction N u).asIso.hom`. -/
theorem exactOrderPointsEquivOfIsPullback_zpow_unit {T : Over S} {E' : EllipticCurveGeom T.left}
    {g : E'.carrier ⟶ E.carrier} (hg : IsPullback g E'.structureMap E.structureMap T.hom)
    (h0 : E'.zero ≫ g = T.hom ≫ E.zero)
    (P : {P : 𝟙_ (Over T.left) ⟶ Over.mk E'.structureMap // E'.IsOfExactOrder P N})
    (u : (ZMod N)ˣ) :
    exactOrderPointsEquivOfIsPullback N hg h0 ⟨P.1 ^ ((u : ZMod N).cast : ℤ), P.2.zpow_unit u⟩ =
      exactOrderPointsEquivOfIsPullback N hg h0 P ≫ (E.exactOrderSchemeAction N u).asIso.hom := by
  refine (cancel_mono (E.exactOrderSchemeι N)).mp ?_
  have hy : exactOrderPointsEquivOfIsPullback N hg h0 P ≫ E.exactOrderSchemeι N =
      pointsBaseChangeEquiv hg h0 P.1 :=
    Over.OverMorphism.ext <| by
      rw [Over.comp_left, exactOrderSchemeι_left,
        exactOrderPointsEquivOfIsPullback_apply_left_comp hg h0, pointsBaseChangeEquiv_left]
  rw [Category.assoc, exactOrderSchemeAction_hom_comp_exactOrderSchemeι, comp_zpow, hy, ← map_zpow]
  exact Over.OverMorphism.ext <| by
    rw [Over.comp_left, exactOrderSchemeι_left,
      exactOrderPointsEquivOfIsPullback_apply_left_comp hg h0, pointsBaseChangeEquiv_left]

/-- Postcomposing `y : T ⟶ E.exactOrderScheme N` with `(E.exactOrderSchemeAction N u).asIso.hom`
raises the corresponding point of exact order `N` on `E'` to `((u : ZMod N).cast : ℤ)`. -/
@[simp]
theorem exactOrderPointsEquivOfIsPullback_symm_comp_exactOrderSchemeAction_hom
    {T : Over S} {E' : EllipticCurveGeom T.left} {g : E'.carrier ⟶ E.carrier}
    (hg : IsPullback g E'.structureMap E.structureMap T.hom) (h0 : E'.zero ≫ g = T.hom ≫ E.zero)
    (y : T ⟶ E.exactOrderScheme N) (u : (ZMod N)ˣ) :
    ((exactOrderPointsEquivOfIsPullback N hg h0).symm
      (y ≫ (E.exactOrderSchemeAction N u).asIso.hom)).1 =
      ((exactOrderPointsEquivOfIsPullback N hg h0).symm y).1 ^ ((u : ZMod N).cast : ℤ) := by
  let P := (exactOrderPointsEquivOfIsPullback N hg h0).symm y
  have hy : y = exactOrderPointsEquivOfIsPullback N hg h0 P := (Equiv.apply_symm_apply _ y).symm
  rw [hy, ← exactOrderPointsEquivOfIsPullback_zpow_unit hg h0 P u, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

/-- **The diamond action on `E.exactOrderScheme N` is free where `N` is invertible.** Let `T` be a
nonempty scheme over `S` on whose residue fields `N` is nonzero. If `u : (ZMod N)ˣ` fixes a point
`y : T ⟶ E.exactOrderScheme N`, then `u = 1`. No invertibility assumption on `S` is needed. -/
theorem eq_one_of_comp_exactOrderSchemeAction_hom_eq {T : Over S} [Nonempty T.left]
    (hN : ∀ t : T.left, (N : T.left.residueField t) ≠ 0)
    {y : T ⟶ E.exactOrderScheme N} {u : (ZMod N)ˣ}
    (hy : y ≫ (E.exactOrderSchemeAction N u).asIso.hom = y) : u = 1 := by
  let hg := E.isPullback_baseChange T.hom
  have h0 : (E.baseChange T.hom).zero ≫ (E.baseChangeIso T.hom).hom ≫ pullback.fst _ _ =
      T.hom ≫ E.zero := by simp
  let P := (exactOrderPointsEquivOfIsPullback N hg h0).symm y
  refine eq_one_of_isOfExactOrder_zpow_unit_eq_self hN P.2 ?_
  have := congrArg (fun z ↦ ((exactOrderPointsEquivOfIsPullback N hg h0).symm z).1) hy
  simpa [P] using this

end Scheme

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
