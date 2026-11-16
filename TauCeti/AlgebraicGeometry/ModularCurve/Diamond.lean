/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import TauCeti.AlgebraicGeometry.ModularCurve.Comparison
public import TauCeti.AlgebraicGeometry.ModularCurve.Rigidifier.FreeAction
public import TauCeti.Data.ZMod.Aut
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
import TauCeti.Data.ZMod.Pow

/-!
# The diamond action on naive `[Γ₁(N)]`, simultaneous moduli schemes, and `Y₁(N)`

This file complements the integral diamond action `ModuliProblem.gammaOneAction` on `[Γ₁(N)]`
with its counterpart on naive `[Γ₁(N)]`-structures, its compatibility with the Borel projection
from `[Γ(N)]` and with the Drinfeld–naive comparison, its freeness on rigidified simultaneous
moduli schemes, and the induced action on the fine modular curve `Y₁(N)` for `N ≥ 4`:

1. **Naive `[Γ₁(N)]` (`ModuliProblem.gammaOneNaiveAction`).** Precomposing homomorphisms
   `Multiplicative (ZMod N) →* E(S)` with `TauCeti.zmodUnitsMulAutEquiv` defines an action
   `(ZMod N)ˣ →* Aut (gammaOneNaive B N)` sending the generator `P = φ 1` to
   `P ^ ((u : ZMod N).cast : ℤ)`, acting freely over every nonempty base scheme, and sending `-1`
   to pullback along `EllObj.neg`.
2. **Borel compatibility and the `SL₂` `d⁻¹` law.** Under the projection
   `ModuliProblem.gammaNaiveToGammaOneNaive : [Γ(N)]_naive ⟶ [Γ₁(N)]_naive` keeping the first basis
   point, an upper-triangular matrix `g : GL2Borel (ZMod N)` acts on `[Γ₁(N)]_naive` through its
   upper-left entry `(GL2Borel.diag g).1`
   (`ModuliProblem.gammaNaiveAction_hom_comp_gammaNaiveToGammaOneNaive_of_borel`). When
   `det g = 1`, `GL2Borel.det_diag` gives `(GL2Borel.diag g).1 = (GL2Borel.diag g).2⁻¹`, recovering
   the classical `SL₂(ℤ/Nℤ)` formula `P ↦ d⁻¹P`
   (`ModuliProblem.gammaNaiveAction_hom_comp_gammaNaiveToGammaOneNaive_of_borel_of_det_eq_one`).
3. **Drinfeld–naive comparison.** Over a base `B` where `N` is invertible, the isomorphism
   `ModuliProblem.gammaOneToGammaOneNaive : [Γ₁(N)] ⟶ [Γ₁(N)]_naive` is `(ZMod N)ˣ`-equivariant
   (`ModuliProblem.gammaOneAction_hom_comp_gammaOneToGammaOneNaive`).
4. **Freeness on simultaneous moduli schemes.** When `𝒫` is a rigid moduli problem and `V`
   represents `(𝒫, [Γ₁(N)]_naive)`, `(ZMod N)ˣ` acts freely on `V.base`; when `V` represents the
   integral simultaneous problem `(𝒫, [Γ₁(N)])`, `(ZMod N)ˣ` acts freely on `T`-points of `V.base`
   over any nonempty scheme `T` on whose residue fields `N` is nonzero, without requiring `N` to be
   invertible on `B`
   (`ModuliProblem.IsRigid.eq_one_of_comp_simultaneousAction_gammaOneAction_base_eq`).
5. **The diamond action on `Y₁(N)` (`N ≥ 4`).** For `N ≥ 4` over an arbitrary base `B`, Yoneda
   transport (`CategoryTheory.Functor.RepresentableBy.autMulEquiv`) along
   `ModuliProblem.gammaOneNaiveRepresentableBy` induces `(ZMod N)ˣ →* Aut (EllObj.yOne B N)`
   (`EllObj.yOneAction`). Here `-1 : (ZMod N)ˣ` acts on the universal elliptic curve as the
   negation automorphism `EllObj.negAut` (`[-1]` over the identity of `Y₁(N)`), so the induced
   action `EllObj.yOneBaseAction` on the base curve `Y₁(N)` over `B` kills `-1` and descends to the
   reduced diamond group `(ZMod N)ˣ ⧸ Subgroup.zpowers (-1)` (`EllObj.yOneReducedBaseAction`). Note
   that this quotient action on `Y₁(N)` is not globally free: elliptic curves with extra
   automorphisms (`j = 0` or `j = 1728`) give points with non-trivial stabiliser in
   `(ZMod N)ˣ / {±1}`.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveAction B N`: the diamond action
  `(ZMod N)ˣ →* Aut (gammaOneNaive B N)`.
* `TauCeti.AlgebraicGeometry.EllObj.yOneAction B N h4`: for `N ≥ 4`, the diamond action
  `(ZMod N)ˣ →* Aut (EllObj.yOne B N)` on the universal elliptic curve over `Y₁(N)`.
* `TauCeti.AlgebraicGeometry.EllObj.yOneBaseAction B N h4` and
  `TauCeti.AlgebraicGeometry.EllObj.yOneReducedBaseAction B N h4`: the induced actions of
  `(ZMod N)ˣ` and `(ZMod N)ˣ ⧸ Subgroup.zpowers (-1)` on the modular curve `Y₁(N)` over `B`.

## Main results

* `ModuliProblem.gammaNaiveAction_hom_comp_gammaNaiveToGammaOneNaive_of_borel` and
  `ModuliProblem.gammaNaiveAction_hom_comp_gammaNaiveToGammaOneNaive_of_borel_of_det_eq_one`: Borel
  compatibility of `[Γ(N)]_naive ⟶ [Γ₁(N)]_naive` and the `P ↦ d⁻¹P` law for `det = 1`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneAction_hom_comp_gammaOneToGammaOneNaive`:
  `(ZMod N)ˣ`-equivariance of `[Γ₁(N)] ⟶ [Γ₁(N)]_naive`.
* `ModuliProblem.IsRigid.eq_one_of_comp_simultaneousAction_gammaOneAction_base_eq` and
  `ModuliProblem.IsRigid.span_range_gammaOneAction_smul_sub_eq_top`: freeness of `(ZMod N)ˣ` on
  rigidified simultaneous moduli schemes where `N` is invertible.
* `TauCeti.AlgebraicGeometry.EllObj.yOneAction_neg_one` and
  `TauCeti.AlgebraicGeometry.EllObj.yOneBaseAction_neg_one`: `-1` acts as `[-1]` on the universal
  curve over `Y₁(N)` and trivially on `Y₁(N)` itself.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §3.7, §7.1, §7.4, and §7.6.
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, §1.5 and §7.7.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace ModuliProblem

/-! ### The diamond action on naive `[Γ₁(N)]` -/

section NaiveDiamond

/-- Since `(ZMod N)ˣ` is commutative, `zmodUnitsMulAutEquiv` lifts to a homomorphism into the
opposite group `(MulAut (Multiplicative (ZMod N)))ᵐᵒᵖ`. -/
private def zmodUnitsToMulAutOp (N : ℕ) :
    (ZMod N)ˣ →* (MulAut (Multiplicative (ZMod N)))ᵐᵒᵖ where
  toFun u := .op (zmodUnitsMulAutEquiv N u)
  map_one' := by simp
  map_mul' u v := by
    rw [← MulOpposite.op_mul, ← map_mul, mul_comm]

variable (B : Scheme.{u}) (N : ℕ)

/-- **The diamond action of `(ℤ/Nℤ)ˣ` on the naive moduli problem `[Γ₁(N)]`.** A unit
`u : (ZMod N)ˣ` acts on `Multiplicative (ZMod N)` by multiplication
(`TauCeti.zmodUnitsMulAutEquiv`), sending a naive `[Γ₁(N)]`-structure `φ : ℤ/Nℤ →* E(S)` to `φ ∘ u`
(`naiveLevelEquiv_gammaOneNaiveAction_hom_app`), whose value at `1` is
`(φ 1) ^ ((u : ZMod N).cast : ℤ)`. -/
noncomputable def gammaOneNaiveAction : (ZMod N)ˣ →* Aut (gammaOneNaive B N) :=
  (naiveLevelAction B _).comp (zmodUnitsToMulAutOp N)

variable {B N}

/-- A unit `u : (ZMod N)ˣ` precomposes a naive `[Γ₁(N)]`-structure `φ` with
`zmodUnitsMulAutEquiv N u`. -/
@[simp]
theorem naiveLevelEquiv_gammaOneNaiveAction_hom_app (u : (ZMod N)ˣ) (X : EllObj B)
    (α : (gammaOneNaive B N).obj (op X)) :
    (naiveLevelEquiv X ((gammaOneNaiveAction B N u).asIso.hom.app (op X) α)).1 =
      (naiveLevelEquiv X α).1.comp (zmodUnitsMulAutEquiv N u).toMonoidHom :=
  naiveLevelEquiv_naiveLevelAction_hom_app _ X α

/-- The inverse of the diamond automorphism for `u : (ZMod N)ˣ` precomposes a naive
`[Γ₁(N)]`-structure `φ` with `(zmodUnitsMulAutEquiv N u).symm`. -/
@[simp]
theorem naiveLevelEquiv_gammaOneNaiveAction_inv_app (u : (ZMod N)ˣ) (X : EllObj B)
    (α : (gammaOneNaive B N).obj (op X)) :
    (naiveLevelEquiv X ((gammaOneNaiveAction B N u).asIso.inv.app (op X) α)).1 =
      (naiveLevelEquiv X α).1.comp (zmodUnitsMulAutEquiv N u).symm.toMonoidHom :=
  naiveLevelEquiv_naiveLevelAction_inv_app _ X α

/-- Under the diamond action on naive `[Γ₁(N)]`, `u : (ZMod N)ˣ` sends the generator point `φ 1` to
`(φ 1) ^ ((u : ZMod N).cast : ℤ)`, for all `N : ℕ`. -/
theorem naiveLevelEquiv_gammaOneNaiveAction_hom_app_ofAdd_one (u : (ZMod N)ˣ) (X : EllObj B)
    (α : (gammaOneNaive B N).obj (op X)) :
    (naiveLevelEquiv X ((gammaOneNaiveAction B N u).asIso.hom.app (op X) α)).1 (.ofAdd 1) =
      ((naiveLevelEquiv X α).1 (.ofAdd 1)) ^ ((u : ZMod N).cast : ℤ) := by
  rw [naiveLevelEquiv_gammaOneNaiveAction_hom_app, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, zmodUnitsMulAutEquiv_apply, _root_.mul_one, zmodMonoidHom_apply_ofAdd]

/-- On any object `X` of `Ell/B`, `-1 : (ZMod N)ˣ` acts on naive `[Γ₁(N)]`-structures as pullback
along the negation arrow `X.neg`. -/
theorem gammaOneNaiveAction_neg_one_hom_app (X : EllObj B)
    (α : (gammaOneNaive B N).obj (op X)) :
    (gammaOneNaiveAction B N (-1)).asIso.hom.app (op X) α =
      (gammaOneNaive B N).map X.neg.op α := by
  apply (naiveLevelEquiv X).injective
  apply Subtype.ext
  refine MonoidHom.ext fun z ↦ ?_
  obtain ⟨a, rfl⟩ : ∃ a : ZMod N, Multiplicative.ofAdd a = z := ⟨z.toAdd, rfl⟩
  rw [naiveLevelEquiv_gammaOneNaiveAction_hom_app, naiveLevelEquiv_map, MonoidHom.comp_apply,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, zmodUnitsMulAutEquiv_apply, Units.val_neg,
    Units.val_one, neg_mul, _root_.one_mul, ofAdd_neg, map_inv, X.pointsPullback_neg]

/-- For `N ≠ 0`, `u : (ZMod N)ˣ` sends the `E[N]`-point `P` of a naive `[Γ₁(N)]`-structure to
`P ^ (u : ZMod N).val`. -/
theorem gammaOneNaiveEquiv_gammaOneNaiveAction_hom_app_torsionι [NeZero N] (u : (ZMod N)ˣ)
    (X : EllObj B) (α : (gammaOneNaive B N).obj (op X)) :
    (gammaOneNaiveEquiv X ((gammaOneNaiveAction B N u).asIso.hom.app (op X) α)).1 ≫
        X.curve.torsionι N =
      ((gammaOneNaiveEquiv X α).1 ≫ X.curve.torsionι N) ^ (u : ZMod N).val := by
  rw [gammaOneNaiveEquiv_apply_torsionι, gammaOneNaiveEquiv_apply_torsionι,
    naiveLevelEquiv_gammaOneNaiveAction_hom_app_ofAdd_one, zpow_zmod_cast_eq_pow_val]

/-- **The diamond action on naive `[Γ₁(N)]` is free over a nonempty base.** -/
theorem eq_one_of_gammaOneNaiveAction_hom_app_eq_self {X : EllObj B} [Nonempty X.base]
    {u : (ZMod N)ˣ} {α : (gammaOneNaive B N).obj (op X)}
    (h : (gammaOneNaiveAction B N u).asIso.hom.app (op X) α = α) : u = 1 := by
  have hσ := eq_one_of_naiveLevelAction_hom_app_eq_self h
  exact (zmodUnitsMulAutEquiv N).injective (by simpa [zmodUnitsToMulAutOp] using hσ)

/-! ### Compatibility with `[Γ(N)] ⟶ [Γ₁(N)]` on the Borel subgroup -/

variable (B N) in
/-- **Borel equivariance of `[Γ(N)]_naive ⟶ [Γ₁(N)]_naive`.** An upper-triangular matrix
`g : GL2Borel (ZMod N)` sends `(P, Q)` to `(aP, bP + dQ)` where `(a, d) = GL2Borel.diag g`, so its
action on `[Γ(N)]_naive` intertwines with the diamond action of `a = (GL2Borel.diag g).1` on
`[Γ₁(N)]_naive`. -/
theorem gammaNaiveAction_hom_comp_gammaNaiveToGammaOneNaive_of_borel (g : GL2Borel (ZMod N)) :
    (gammaNaiveAction B N (.op (g : GL (Fin 2) (ZMod N)))).asIso.hom ≫
        gammaNaiveToGammaOneNaive B N =
      gammaNaiveToGammaOneNaive B N ≫
        (gammaOneNaiveAction B N (GL2Borel.diag g).1).asIso.hom := by
  refine naiveLevel_hom_ext fun X α ↦ MonoidHom.ext fun z ↦ ?_
  obtain ⟨a, rfl⟩ : ∃ a : ZMod N, Multiplicative.ofAdd a = z := ⟨z.toAdd, rfl⟩
  simp

variable (B N) in
/-- **The `SL₂(ℤ/Nℤ)` diamond formula `P ↦ d⁻¹P`.** For an upper-triangular matrix
`g : GL2Borel (ZMod N)` of determinant `1` (`a * d = 1`), the action of `g` on `[Γ(N)]_naive`
descends along `[Γ(N)]_naive ⟶ [Γ₁(N)]_naive` to the diamond action of
`d⁻¹ = (GL2Borel.diag g).2⁻¹`. -/
theorem gammaNaiveAction_hom_comp_gammaNaiveToGammaOneNaive_of_borel_of_det_eq_one
    {g : GL2Borel (ZMod N)} (hdet : (g : GL (Fin 2) (ZMod N)).det = 1) :
    (gammaNaiveAction B N (.op (g : GL (Fin 2) (ZMod N)))).asIso.hom ≫
        gammaNaiveToGammaOneNaive B N =
      gammaNaiveToGammaOneNaive B N ≫
        (gammaOneNaiveAction B N (GL2Borel.diag g).2⁻¹).asIso.hom := by
  have had : (GL2Borel.diag g).1 = (GL2Borel.diag g).2⁻¹ :=
    mul_eq_one_iff_eq_inv.mp ((GL2Borel.det_diag g).symm.trans hdet)
  rw [← had]
  exact gammaNaiveAction_hom_comp_gammaNaiveToGammaOneNaive_of_borel B N g

end NaiveDiamond

/-! ### Equivariance of the Drinfeld–naive comparison -/

section Comparison

variable {B : Scheme.{u}} {N : ℕ} [NeZero N] {hN : ∀ b : B, (N : B.residueField b) ≠ 0}

/-- **The comparison `[Γ₁(N)] ⟶ [Γ₁(N)]_naive` is `(ℤ/Nℤ)ˣ`-equivariant.** Over a base `B` where
`N` is invertible, `gammaOneToGammaOneNaive` intertwines `gammaOneAction` with
`gammaOneNaiveAction`. -/
@[reassoc (attr := simp)]
theorem gammaOneAction_hom_comp_gammaOneToGammaOneNaive (u : (ZMod N)ˣ) :
    (gammaOneAction B N u).asIso.hom ≫ gammaOneToGammaOneNaive B N hN =
      gammaOneToGammaOneNaive B N hN ≫ (gammaOneNaiveAction B N u).asIso.hom := by
  refine naiveLevel_hom_ext fun X α ↦ MonoidHom.ext fun z ↦ ?_
  obtain ⟨a, rfl⟩ : ∃ a : ZMod N, Multiplicative.ofAdd a = z := ⟨z.toAdd, rfl⟩
  simp [zpow_zmod_cast_eq_pow_val, ← pow_val_mul (gammaOneEquiv X α).2.pow_eq_one]

/-- The inverse diamond automorphisms also commute with `gammaOneToGammaOneNaive`. -/
@[reassoc (attr := simp)]
theorem gammaOneAction_inv_comp_gammaOneToGammaOneNaive (u : (ZMod N)ˣ) :
    (gammaOneAction B N u).asIso.inv ≫ gammaOneToGammaOneNaive B N hN =
      gammaOneToGammaOneNaive B N hN ≫ (gammaOneNaiveAction B N u).asIso.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, gammaOneAction_hom_comp_gammaOneToGammaOneNaive,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Comparison

/-! ### Freeness on simultaneous rigidified moduli schemes -/

section Simultaneous

variable {B : Scheme.{u}} {P : ModuliProblem B} {V : EllObj B} {N : ℕ}

/-- **`(ℤ/Nℤ)ˣ` acts freely on `𝕄(𝒫, [Γ₁(N)]_naive)`** for every rigid moduli problem `𝒫`. -/
theorem IsRigid.eq_one_of_comp_simultaneousAction_gammaOneNaiveAction_base_eq
    (hP : P.IsRigid) (R : (P ⊗ gammaOneNaive B N).RepresentableBy V) {T : Scheme.{u}} [Nonempty T]
    {x : T ⟶ V.base} {u : (ZMod N)ˣ}
    (hx : x ≫ (simultaneousAction R (gammaOneNaiveAction B N) u).asIso.hom.base = x) :
    u = 1 :=
  hP.eq_one_of_comp_simultaneousAction_base_eq R _
    (fun _ _ _ _ h ↦ eq_one_of_gammaOneNaiveAction_hom_app_eq_self h) hx

/-- **`(ℤ/Nℤ)ˣ` acts freely on the global functions of an affine `𝕄(𝒫, [Γ₁(N)]_naive)`** for every
rigid `𝒫`. -/
theorem IsRigid.span_range_gammaOneNaiveAction_smul_sub_eq_top
    (hP : P.IsRigid) (R : (P ⊗ gammaOneNaive B N).RepresentableBy V) [IsAffine V.base]
    {u : (ZMod N)ˣ} (hu : u ≠ 1) :
    letI := simultaneousSectionsAction R (gammaOneNaiveAction B N)
    Ideal.span (Set.range fun a : Γ(V.base, ⊤) ↦ u • a - a) = ⊤ :=
  hP.span_range_smul_sub_eq_top R _
    (fun _ _ _ _ h ↦ eq_one_of_gammaOneNaiveAction_hom_app_eq_self h) hu

/-- **`(ℤ/Nℤ)ˣ` acts freely on `T`-points of `𝕄(𝒫, [Γ₁(N)])` wherever `N` is invertible on `T`.**
Let `𝒫` be rigid and let `V` represent the integral simultaneous problem `(𝒫, [Γ₁(N)])` over `B`.
If `T` is a nonempty scheme on whose residue fields `N` is nonzero and `x : T ⟶ V.base` is fixed
by `u : (ZMod N)ˣ`, then `u = 1`. Crucially, `N` need not be invertible on `B` or on all of
`V.base` (as in Katz–Mazur 7.6.1, where `B = Spec ℤ` and freeness is used over `D(p)`). -/
theorem IsRigid.eq_one_of_comp_simultaneousAction_gammaOneAction_base_eq
    (hP : P.IsRigid) (R : (P ⊗ gammaOne B N).RepresentableBy V) {T : Scheme.{u}} [Nonempty T]
    (hN : ∀ t : T, (N : T.residueField t) ≠ 0) {x : T ⟶ V.base} {u : (ZMod N)ˣ}
    (hx : x ≫ (simultaneousAction R (gammaOneAction B N) u).asIso.hom.base = x) : u = 1 := by
  let e := V.baseChangeFunctorHom (Over.mk x)
  let s := (simultaneousAction R (gammaOneAction B N) u).asIso.hom
  let τ := EllObj.Hom.lift e (e ≫ s) (𝟙 _) (by
    simp only [e, s, EllObj.comp_base, EllObj.baseChangeFunctorHom_base, Over.mk_hom]
    exact (Category.id_comp x).trans hx.symm)
  have h := R.homEquiv_comp τ e
  rw [show τ ≫ e = e ≫ s from EllObj.Hom.lift_comp _ _ _ _,
    homEquiv_comp_simultaneousAction_hom] at h
  obtain ⟨hα, hβ⟩ := Prod.ext_iff.1 h
  simp only [Functor.Monoidal.tensorObj_map_apply_fst,
    Functor.Monoidal.tensorObj_map_apply_snd] at hα hβ
  have hτ : τ = 𝟙 _ := P.isRigid_iff.1 hP τ (EllObj.Hom.lift_base _ _ _ _) _ hα.symm
  rw [hτ, op_id, Functor.map_id_apply] at hβ
  have : Nonempty (V.baseChangeFunctor.obj (Over.mk x)).base := ‹Nonempty T›
  exact eq_one_of_gammaOneAction_hom_app_eq_self hN hβ

/-- **Freeness on global functions of an affine `𝕄(𝒫, [Γ₁(N)])` where `N` is invertible on
`V.base`.** No invertibility hypothesis on `B` is needed. -/
theorem IsRigid.span_range_gammaOneAction_smul_sub_eq_top
    (hP : P.IsRigid) (R : (P ⊗ gammaOne B N).RepresentableBy V) [IsAffine V.base]
    (hN : ∀ v : V.base, (N : V.base.residueField v) ≠ 0) {u : (ZMod N)ˣ} (hu : u ≠ 1) :
    letI := simultaneousSectionsAction R (gammaOneAction B N)
    Ideal.span (Set.range fun a : Γ(V.base, ⊤) ↦ u • a - a) = ⊤ := by
  let _ := simultaneousSectionsAction R (gammaOneAction B N)
  have hspan : Ideal.span (Set.range fun a : Γ(V.base, ⊤) ↦
      (simultaneousAction R (gammaOneAction B N) u⁻¹).asIso.hom.base.appTop a - a) = ⊤ :=
    (Scheme.Hom.span_range_appTop_sub_eq_top_iff _).2 fun T x hx ↦
      not_nonempty_iff.1 fun _ ↦ inv_ne_one.2 hu <|
        hP.eq_one_of_comp_simultaneousAction_gammaOneAction_base_eq R
          (fun _ ↦ x.natCast_residueField_ne_zero (hN _)) hx
  simpa only [simultaneousSectionsAction_smul_def] using hspan

end Simultaneous

end ModuliProblem

namespace EllObj

/-! ### The diamond action on the fine modular curve `Y₁(N)` (`N ≥ 4`) -/

section YOne

variable (B : Scheme.{u}) (N : ℕ) [NeZero N] (h4 : 4 ≤ N)

/-- **The diamond action of `(ℤ/Nℤ)ˣ` on the universal elliptic curve over `Y₁(N)`** for `N ≥ 4`.
By Yoneda transport (`CategoryTheory.Functor.RepresentableBy.autMulEquiv`) along
`ModuliProblem.gammaOneNaiveRepresentableBy`, `u : (ZMod N)ˣ` acts as the unique automorphism of
`EllObj.yOne B N` in `Ell/B` pulling the universal point `yOnePoint` back to
`yOnePoint ^ ((u : ZMod N).cast : ℤ)` (`pointsPullback_yOneAction_hom_yOnePoint`). No
invertibility hypothesis on `N` over `B` is needed. -/
noncomputable def yOneAction : (ZMod N)ˣ →* Aut (yOne B N) :=
  (ModuliProblem.gammaOneNaiveRepresentableBy h4).autMulEquiv.toMonoidHom.comp
    (ModuliProblem.gammaOneNaiveAction B N)

variable {B N}

/-- Postcomposing an arrow `k : X ⟶ yOne B N` with `(yOneAction B N h4 u).asIso.hom` applies the
diamond action of `u` to the naive `[Γ₁(N)]`-structure classified by `k`. -/
@[simp]
theorem gammaOneNaiveRepresentableBy_homEquiv_comp_yOneAction_hom (u : (ZMod N)ˣ) {X : EllObj B}
    (k : X ⟶ yOne B N) :
    (ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv
        (k ≫ (yOneAction B N h4 u).asIso.hom) =
      (ModuliProblem.gammaOneNaiveAction B N u).asIso.hom.app (op X)
        ((ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv k) :=
  (ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv_comp_autMulEquiv_hom _ k

/-- Postcomposing `k : X ⟶ yOne B N` with `(yOneAction B N h4 u).asIso.inv` applies the inverse
diamond action of `u` to the classified naive `[Γ₁(N)]`-structure. -/
@[simp]
theorem gammaOneNaiveRepresentableBy_homEquiv_comp_yOneAction_inv (u : (ZMod N)ˣ) {X : EllObj B}
    (k : X ⟶ yOne B N) :
    (ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv
        (k ≫ (yOneAction B N h4 u).asIso.inv) =
      (ModuliProblem.gammaOneNaiveAction B N u).asIso.inv.app (op X)
        ((ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv k) :=
  (ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv_comp_autMulEquiv_inv _ k

/-- Where `N` is invertible on `B`, postcomposing `k : X ⟶ yOne B N` with
`(yOneAction B N h4 u).asIso.hom` also applies the integral Drinfeld diamond action
`ModuliProblem.gammaOneAction` to the classified `[Γ₁(N)]`-structure. -/
@[simp]
theorem gammaOneRepresentableBy_homEquiv_comp_yOneAction_hom
    {hN : ∀ b : B, (N : B.residueField b) ≠ 0} (u : (ZMod N)ˣ) {X : EllObj B}
    (k : X ⟶ yOne B N) :
    (ModuliProblem.gammaOneRepresentableBy (hN := hN) h4).homEquiv
        (k ≫ (yOneAction B N h4 u).asIso.hom) =
      (ModuliProblem.gammaOneAction B N u).asIso.hom.app (op X)
        ((ModuliProblem.gammaOneRepresentableBy (hN := hN) h4).homEquiv k) := by
  apply (ModuliProblem.gammaOneEquiv X).injective
  apply Subtype.ext
  rw [ModuliProblem.gammaOneEquiv_gammaOneRepresentableBy_homEquiv h4,
    ModuliProblem.gammaOneEquiv_gammaOneAction_hom_app,
    ModuliProblem.gammaOneEquiv_gammaOneRepresentableBy_homEquiv h4,
    ← ModuliProblem.naiveLevelEquiv_gammaOneNaiveRepresentableBy_homEquiv h4,
    ← ModuliProblem.naiveLevelEquiv_gammaOneNaiveRepresentableBy_homEquiv h4,
    gammaOneNaiveRepresentableBy_homEquiv_comp_yOneAction_hom,
    ModuliProblem.naiveLevelEquiv_gammaOneNaiveAction_hom_app_ofAdd_one]

/-- **Action on the universal point of `Y₁(N)`.** Pulling `yOnePoint` back along the diamond
automorphism `(yOneAction B N h4 u).asIso.hom` raises `yOnePoint` to `((u : ZMod N).cast : ℤ)`. -/
theorem pointsPullback_yOneAction_hom_yOnePoint (u : (ZMod N)ˣ) :
    EllipticCurveGeom.pointsPullback (yOneAction B N h4 u).asIso.hom.isPullback
        (yOneAction B N h4 u).asIso.hom.zero_total yOnePoint =
      yOnePoint ^ ((u : ZMod N).cast : ℤ) := by
  have hid := ModuliProblem.naiveLevelEquiv_gammaOneNaiveRepresentableBy_homEquiv_id (B := B) h4
  calc EllipticCurveGeom.pointsPullback (yOneAction B N h4 u).asIso.hom.isPullback
          (yOneAction B N h4 u).asIso.hom.zero_total yOnePoint
      = (ModuliProblem.naiveLevelEquiv _
          ((ModuliProblem.gammaOneNaive B N).map (yOneAction B N h4 u).asIso.hom.op
            ((ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv (𝟙 _)))).1 (.ofAdd 1) := by
        rw [ModuliProblem.naiveLevelEquiv_map, MonoidHom.comp_apply, hid]
    _ = (ModuliProblem.naiveLevelEquiv _
          ((ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv
            (𝟙 _ ≫ (yOneAction B N h4 u).asIso.hom))).1 (.ofAdd 1) := by
        rw [← (ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv_comp,
          Category.id_comp, Category.comp_id]
    _ = yOnePoint ^ ((u : ZMod N).cast : ℤ) := by
        rw [gammaOneNaiveRepresentableBy_homEquiv_comp_yOneAction_hom,
          ModuliProblem.naiveLevelEquiv_gammaOneNaiveAction_hom_app_ofAdd_one, hid]

/-- **The diamond automorphism of `-1` on `EllObj.yOne B N` is `[-1]` over `𝟙`.** On the universal
elliptic curve over `Y₁(N)`, `-1 : (ZMod N)ˣ` acts as `EllObj.negAut` (`[-1]` on the curve over
the identity of the base `Y₁(N)`). -/
@[simp]
theorem yOneAction_neg_one : yOneAction B N h4 (-1) = (yOne B N).negAut := by
  apply Aut.ext
  apply Iso.ext
  refine (ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv.injective ?_
  calc (ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv
          (yOneAction B N h4 (-1)).asIso.hom
      = (ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv
          (𝟙 _ ≫ (yOneAction B N h4 (-1)).asIso.hom) := by rw [Category.id_comp]
    _ = (ModuliProblem.gammaOneNaive B N).map (yOne B N).neg.op
          ((ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv (𝟙 _)) := by
        rw [gammaOneNaiveRepresentableBy_homEquiv_comp_yOneAction_hom,
          ModuliProblem.gammaOneNaiveAction_neg_one_hom_app]
    _ = (ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv
          (yOne B N).negAut.asIso.hom := by
        rw [negAut_hom, ← (ModuliProblem.gammaOneNaiveRepresentableBy h4).homEquiv_comp,
          Category.comp_id]

/-- The diamond automorphism for `-1` acts as the identity morphism on the base scheme `Y₁(N)`. -/
theorem yOneAction_neg_one_hom_base :
    (yOneAction B N h4 (-1)).asIso.hom.base = 𝟙 (yOne B N).base := by
  rw [yOneAction_neg_one, negAut_hom, neg_base]

variable (B N) in
/-- **The diamond action of `(ℤ/Nℤ)ˣ` on the modular curve `Y₁(N)` over `B`** for `N ≥ 4`, obtained
by applying the base-forgetful functor `EllObj.forget B` to `EllObj.yOneAction`. -/
noncomputable def yOneBaseAction : (ZMod N)ˣ →* Aut (Over.mk (yOne B N).structureMap) :=
  ((forget B).mapAut (yOne B N)).comp (yOneAction B N h4)

@[simp]
theorem yOneBaseAction_hom_left (u : (ZMod N)ˣ) :
    (yOneBaseAction B N h4 u).asIso.hom.left = (yOneAction B N h4 u).asIso.hom.base :=
  (rfl)

@[simp]
theorem yOneBaseAction_inv_left (u : (ZMod N)ˣ) :
    (yOneBaseAction B N h4 u).asIso.inv.left = (yOneAction B N h4 u).asIso.inv.base :=
  (rfl)

variable (B N) in
/-- **The unit `-1` acts trivially on the modular curve `Y₁(N)`.** Because `-1` negates the
universal point via the curve automorphism `[-1]` lying over `𝟙`, the induced `B`-automorphism of
the base `Y₁(N)` is the identity. -/
@[simp]
theorem yOneBaseAction_neg_one : yOneBaseAction B N h4 (-1) = 1 := by
  apply Aut.ext
  rw [Aut.one_asIso]
  apply Iso.ext
  apply Over.OverMorphism.ext
  rw [yOneBaseAction_hom_left, yOneAction_neg_one_hom_base, Iso.refl_hom, Over.id_left]
  rfl

variable (B N) in
/-- The subgroup `{±1} = Subgroup.zpowers (-1)` lies in the kernel of `yOneBaseAction`. -/
theorem zpowers_neg_one_le_ker_yOneBaseAction :
    Subgroup.zpowers (-1 : (ZMod N)ˣ) ≤ (yOneBaseAction B N h4).ker :=
  Subgroup.zpowers_le.mpr (by simp)

variable (B N) in
/-- **The reduced diamond action of `(ℤ/Nℤ)ˣ / {±1}` on `Y₁(N)` over `B`** for `N ≥ 4`: the
descent of `yOneBaseAction` modulo `Subgroup.zpowers (-1)`. -/
noncomputable def yOneReducedBaseAction :
    (ZMod N)ˣ ⧸ Subgroup.zpowers (-1 : (ZMod N)ˣ) →* Aut (Over.mk (yOne B N).structureMap) :=
  QuotientGroup.lift (Subgroup.zpowers (-1 : (ZMod N)ˣ)) (yOneBaseAction B N h4)
    (zpowers_neg_one_le_ker_yOneBaseAction B N h4)

@[simp]
theorem yOneReducedBaseAction_mk (u : (ZMod N)ˣ) :
    yOneReducedBaseAction B N h4 (QuotientGroup.mk u) = yOneBaseAction B N h4 u :=
  (rfl)

end YOne

end EllObj

end TauCeti.AlgebraicGeometry
