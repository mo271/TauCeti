/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Diamond
public import TauCeti.AlgebraicGeometry.ModularCurve.ModuliProblem
import TauCeti.AlgebraicGeometry.ResidueField
import TauCeti.Data.ZMod.Pow

/-!
# The moduli problem `[Γ₁(N)]`

Following Katz and Mazur, a `[Γ₁(N)]`-structure on an elliptic curve `E` over a scheme `S` is an
`S`-point `P` of `E` of exact order `N`: the divisor `[P] + [2P] + ⋯ + [NP]` on `E` is a subgroup
scheme (`EllipticCurveGeom.IsOfExactOrder`). This is Drinfeld's notion, which makes sense over
every base, including bases on which `N` is not invertible.

An arrow `(E'/S') ⟶ (E/S)` of `Ell/B` exhibits `E'` as the base change of `E`, so every `S`-point
of `E` has a base change, an `S'`-point of `E'` (`EllipticCurveGeom.pointsPullback`), and points
of exact order `N` pull back to points of exact order `N`
(`EllipticCurveGeom.IsOfExactOrder.pointsPullback`). Base change of points is functorial, so the
`[Γ₁(N)]`-structures form a moduli problem over `Ell/B` (`ModuliProblem.gammaOne`). For `N = 1`
the only point of exact order one is the zero section, so `[Γ₁(1)]` is the trivial moduli problem
`[Γ(1)]` (`ModuliProblem.gammaOneOneIso`).

The problem `[Γ₁(N)]` is relatively representable (`ModuliProblem.gammaOneRelRepData`): for an
object `(E/S)` and a scheme `T` over `S`, the `[Γ₁(N)]`-structures on the base change `E_T` are the
morphisms from `T` to the exact-order scheme `E.exactOrderScheme N` over `S`
(`ModuliProblem.gammaOneBaseChangeEquiv`), the closed subscheme of `E` on which the universal point
has exact order `N`. It lies in `E[N]`, so for `N ≠ 0` the problem `[Γ₁(N)]` is finite over `Ell/B`
(`ModuliProblem.hasProperty_isFinite_gammaOneRelRepData`). No hypothesis is placed on `B`.

The unit group `(ZMod N)ˣ` acts on `[Γ₁(N)]` by the **diamond action** `P ↦ uP`
(`ModuliProblem.gammaOneAction`), compatible with the diamond action on `E.exactOrderScheme N`
(`ModuliProblem.gammaOneBaseChangeEquiv_gammaOneAction_hom_app`), sending `-1` to pullback along
the negation arrow `[-1]` of `Ell/B` (`ModuliProblem.gammaOneAction_neg_one_hom_app`), and acting
freely over any nonempty test base on whose residue fields `N` is nonzero
(`ModuliProblem.eq_one_of_gammaOneAction_hom_app_eq_self`).

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOne B N`: the moduli problem `[Γ₁(N)]` over
  `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneEquiv`: the `[Γ₁(N)]`-structures on an object
  `(E/S)` of `Ell/B` are the `S`-points of `E` of exact order `N`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneBaseChangeEquiv`: the `[Γ₁(N)]`-structures on
  the base change `E_T` are the morphisms from `T` to the exact-order scheme of `E`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneRelRepData`: `[Γ₁(N)]` is relatively
  representable, by the exact-order scheme.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneAction B N`: the diamond action
  `(ZMod N)ˣ →* Aut (gammaOne B N)`.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneEquiv_map`: the pull-back of a
  `[Γ₁(N)]`-structure along an arrow of `Ell/B` is the base change of its point.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneOneIso`: `[Γ₁(1)]` is the trivial moduli
  problem.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneBaseChangeEquiv_map`: the correspondence with
  morphisms to the exact-order scheme is natural in `T`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.hasProperty_isFinite_gammaOneRelRepData`: for `N ≠ 0`,
  `[Γ₁(N)]` is finite over `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneEquiv_gammaOneAction_hom_app` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.eq_one_of_gammaOneAction_hom_app_eq_self`: the diamond
  action sends `P` to `uP`, and is free over nonempty test bases where `N` is invertible.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.4 (points of exact order
  `N`), §3.2 (the moduli problem `[Γ₁(N)]`), 3.6.0 (its relative representability by a finite
  scheme), Chapter 4, and §7.4 (the `(ℤ/Nℤ)ˣ`-action on `[Γ₁(N)]`).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj

universe u

namespace TauCeti.AlgebraicGeometry

variable {B : Scheme.{u}}

namespace ModuliProblem

variable (B) (N : ℕ)

/-- **The moduli problem `[Γ₁(N)]`** over `Ell/B` (Katz–Mazur, §3.2). A `[Γ₁(N)]`-structure on an
object `(E/S)` of `Ell/B` is an `S`-point of `E` of exact order `N` (`gammaOneEquiv`), and it pulls
back along an arrow of `Ell/B` by base change of points (`gammaOneEquiv_map`). -/
noncomputable def gammaOne : ModuliProblem B where
  obj X := ULift.{u + 1}
    {P : 𝟙_ (Over X.unop.base) ⟶ Over.mk X.unop.curve.structureMap //
      X.unop.curve.IsOfExactOrder P N}
  map φ := TypeCat.ofHom fun P ↦
    ⟨⟨EllipticCurveGeom.pointsPullback φ.unop.isPullback φ.unop.zero_total P.down.1,
      P.down.2.pointsPullback φ.unop.isPullback φ.unop.zero_total⟩⟩
  map_id X := by
    ext P
    exact congrArg Over.Hom.left ((EllipticCurveGeom.eq_pointsPullback_iff _ _).mpr
      (by simp)).symm
  map_comp φ ψ := by
    ext P
    exact congrArg Over.Hom.left ((EllipticCurveGeom.eq_pointsPullback_iff _ _).mpr
      (by simp)).symm

variable {B N}

/-- The `[Γ₁(N)]`-structures on an object `(E/S)` of `Ell/B` are the `S`-points of `E` of exact
order `N`. -/
noncomputable def gammaOneEquiv (X : EllObj B) :
    (gammaOne B N).obj (op X) ≃
      {P : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap // X.curve.IsOfExactOrder P N} :=
  Equiv.ulift

/-- The pull-back of a `[Γ₁(N)]`-structure along an arrow `φ` of `Ell/B` is the base change of its
point along `φ`. -/
@[simp]
theorem gammaOneEquiv_map {X Y : EllObj B} (φ : X ⟶ Y) (α : (gammaOne B N).obj (op Y)) :
    (gammaOneEquiv X ((gammaOne B N).map φ.op α)).1 =
      EllipticCurveGeom.pointsPullback φ.isPullback φ.zero_total (gammaOneEquiv Y α).1 :=
  (rfl)

/-- An `S`-point of exact order one is the zero section, so an object of `Ell/B` has exactly one
`[Γ₁(1)]`-structure. -/
noncomputable instance (X : (EllObj B)ᵒᵖ) : Unique ((gammaOne B 1).obj X) where
  default := (gammaOneEquiv X.unop).symm ⟨1, EllipticCurveGeom.isOfExactOrder_one_iff.mpr rfl⟩
  uniq α := (gammaOneEquiv X.unop).injective <| Subtype.ext <| by
    simpa using EllipticCurveGeom.isOfExactOrder_one_iff.mp (gammaOneEquiv X.unop α).2

variable (B) in
/-- **`[Γ₁(1)]` is the trivial moduli problem** `[Γ(1)]`: the only point of exact order one of an
elliptic curve is its zero section. -/
noncomputable def gammaOneOneIso : gammaOne B 1 ≅ 𝟙_ (ModuliProblem B) :=
  isoTensorUnitOfUnique _

/-! ### Relative representability of `[Γ₁(N)]` -/

section RelRep

/-- **`[Γ₁(N)]`-structures on base changes are points of the exact-order scheme.** For an object
`X = (E/S)` of `Ell/B` and a scheme `T` over `S`, the `[Γ₁(N)]`-structures on the base change `E_T`
of `E` correspond to the morphisms `T ⟶ E.exactOrderScheme N` over `S`: a structure, a `T`-point
`P` of `E_T` of exact order `N`, corresponds to the morphism whose image in `E` is `P` followed by
the projection `E_T ⟶ E` (`gammaOneBaseChangeEquiv_apply_left_comp`). -/
noncomputable def gammaOneBaseChangeEquiv (X : EllObj B) (T : Over X.base) :
    (gammaOne B N).obj (op (X.baseChangeFunctor.obj T)) ≃ (T ⟶ X.curve.exactOrderScheme N) :=
  (gammaOneEquiv _).trans <|
    EllipticCurveGeom.exactOrderPointsEquivOfIsPullback (E' := X.curve.baseChange T.hom) N
      (X.curve.isPullback_baseChange T.hom) (by simp)

/-- The morphism `T ⟶ E.exactOrderScheme N` of a `[Γ₁(N)]`-structure on `E_T`, followed by the
inclusion of the exact-order scheme in `E`, is the point of the structure followed by the
projection `E_T ⟶ E`. -/
@[reassoc (attr := simp)]
theorem gammaOneBaseChangeEquiv_apply_left_comp (X : EllObj B) (T : Over X.base)
    (α : (gammaOne B N).obj (op (X.baseChangeFunctor.obj T))) :
    (gammaOneBaseChangeEquiv X T α).left ≫ (X.curve.exactOrderLocus N).subschemeι =
      (gammaOneEquiv _ α).1.left ≫ (X.curve.baseChangeIso T.hom).hom ≫ pullback.fst _ _ :=
  EllipticCurveGeom.exactOrderPointsEquivOfIsPullback_apply_left_comp _ _ _

/-- **Naturality of `gammaOneBaseChangeEquiv`.** Along a morphism `k : T' ⟶ T` of schemes over the
base of `X`, the morphism `T' ⟶ E.exactOrderScheme N` of the pull-back to `E_{T'}` of a
`[Γ₁(N)]`-structure on `E_T` is the composite of `k` with the morphism of the structure. -/
theorem gammaOneBaseChangeEquiv_map (X : EllObj B) {T' T : Over X.base} (k : T' ⟶ T)
    (α : (gammaOne B N).obj (op (X.baseChangeFunctor.obj T))) :
    gammaOneBaseChangeEquiv X T' ((gammaOne B N).map (X.baseChangeFunctor.map k).op α) =
      k ≫ gammaOneBaseChangeEquiv X T α := by
  -- both sides are compared as points of `E` with values in `T'`
  refine (cancel_mono (X.curve.exactOrderSchemeι N)).mp ?_
  ext1
  simp only [Over.comp_left, Category.assoc, EllipticCurveGeom.exactOrderSchemeι_left,
    gammaOneBaseChangeEquiv_apply_left_comp, gammaOneEquiv_map]
  -- the morphism `E_{T'} ⟶ E_T` lies over `k` and composes with `E_T ⟶ E` to `E_{T'} ⟶ E`
  have hk := congrArg EllObj.Hom.total (X.baseChangeFunctor_map_baseChangeFunctorHom k)
  simp only [EllObj.comp_total, EllObj.baseChangeFunctorHom_total] at hk
  -- the composites are formed by terms, since the base change `E_{T'}` appears both as
  -- `(X.baseChangeFunctor.obj T').curve` and as `X.curve.baseChange T'.hom`
  exact (congrArg (fun m ↦ (EllipticCurveGeom.pointsPullback (X.baseChangeFunctor.map k).isPullback
    (X.baseChangeFunctor.map k).zero_total (gammaOneEquiv _ α).1).left ≫ m) hk.symm).trans
      (EllipticCurveGeom.pointsPullback_left_comp_assoc _ _ _ _)

/-- Naturality of `gammaOneBaseChangeEquiv`, read backwards: the `[Γ₁(N)]`-structure on `E_{T'}` of
the composite of `k : T' ⟶ T` with a morphism `T ⟶ E.exactOrderScheme N` is the pull-back of the
structure on `E_T` of that morphism. -/
theorem gammaOneBaseChangeEquiv_symm_comp (X : EllObj B) {T' T : Over X.base} (k : T' ⟶ T)
    (a : T ⟶ X.curve.exactOrderScheme N) :
    (gammaOneBaseChangeEquiv X T').symm (k ≫ a) =
      (gammaOne B N).map (X.baseChangeFunctor.map k).op ((gammaOneBaseChangeEquiv X T).symm a) := by
  rw [Equiv.symm_apply_eq, gammaOneBaseChangeEquiv_map, Equiv.apply_symm_apply]

variable (B N) in
/-- **The moduli problem `[Γ₁(N)]` is relatively representable** (Katz–Mazur, 3.6.0). For an
object `X = (E/S)` of `Ell/B`, the functor `T ↦ [Γ₁(N)](E_T/T)` on schemes over `S` is represented
by the exact-order scheme `E.exactOrderScheme N`, the closed subscheme of `E` of points of exact
order `N`, through `gammaOneBaseChangeEquiv`. No hypothesis is placed on `B`, and `N` need not be
invertible on it. -/
noncomputable def gammaOneRelRepData : (gammaOne B N).RelRepData where
  rep X := X.curve.exactOrderScheme N
  representableBy X :=
    { homEquiv := (gammaOneBaseChangeEquiv X _).symm
      homEquiv_comp k a := (gammaOneBaseChangeEquiv_symm_comp X k a).trans
        -- the fibre of `[Γ₁(N)]` over `X` at `T` is `[Γ₁(N)](E_T/T)` after unfolding `fibre`
        rfl }

/-- The scheme representing `[Γ₁(N)]`-structures on base changes of `X = (E/S)` is the exact-order
scheme of `E`. -/
@[simp]
theorem gammaOneRelRepData_rep (X : EllObj B) :
    (gammaOneRelRepData B N).rep X = X.curve.exactOrderScheme N :=
  (rfl)

/-- The `[Γ₁(N)]`-structure on `E_T` of a morphism from `T` to the representing scheme is the one
given by `gammaOneBaseChangeEquiv`, after identifying the representing scheme with the exact-order
scheme through `gammaOneRelRepData_rep`. -/
@[simp]
theorem gammaOneRelRepData_homEquiv (X : EllObj B) {T : Over X.base}
    (a : T ⟶ (gammaOneRelRepData B N).rep X) :
    ((gammaOneRelRepData B N).representableBy X).homEquiv a =
      (gammaOneBaseChangeEquiv X T).symm (a ≫ eqToHom (gammaOneRelRepData_rep X)) :=
  congrArg (gammaOneBaseChangeEquiv X T).symm (Category.comp_id a).symm

variable (B N) in
/-- **The moduli problem `[Γ₁(N)]` is finite over `Ell/B`** (Katz–Mazur, 3.6.0) for `N ≠ 0`: each
representing scheme, the exact-order scheme of an elliptic curve `E/S`, is a closed subscheme of
`E[N]` and hence finite over `S`. -/
theorem hasProperty_isFinite_gammaOneRelRepData [NeZero N] :
    (gammaOneRelRepData B N).HasProperty @IsFinite :=
  (RelRepData.hasProperty_iff _).mpr fun X ↦
    EllipticCurveGeom.isFinite_exactOrderScheme_hom X.curve N

end RelRep

/-! ### The diamond action on `[Γ₁(N)]` -/

section Diamond

/-- Two morphisms of moduli problems into `[Γ₁(N)]` agree once they assign the same point to every
structure. -/
@[ext]
theorem gammaOne_hom_ext {P : ModuliProblem B} {f g : P ⟶ gammaOne B N}
    (h : ∀ (X : EllObj B) (α : P.obj (op X)),
      (gammaOneEquiv X (f.app (op X) α)).1 = (gammaOneEquiv X (g.app (op X) α)).1) :
    f = g := by
  ext X α
  exact (gammaOneEquiv X.unop).injective (Subtype.ext (h X.unop α))

/-- The endomorphism of `[Γ₁(N)]` sending a point `P` of exact order `N` to
`P ^ ((u : ZMod N).cast : ℤ)`. -/
private noncomputable def gammaOneEnd (B : Scheme.{u}) (N : ℕ) (u : (ZMod N)ˣ) :
    gammaOne B N ⟶ gammaOne B N where
  app X := TypeCat.ofHom fun α ↦ (gammaOneEquiv X.unop).symm
    ⟨(gammaOneEquiv X.unop α).1 ^ ((u : ZMod N).cast : ℤ), (gammaOneEquiv X.unop α).2.zpow_unit u⟩
  naturality X Y φ := by
    ext α
    apply (gammaOneEquiv _).injective
    apply Subtype.ext
    simp only [op_unop, TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
      Equiv.apply_symm_apply]
    rw [← Quiver.Hom.op_unop φ, gammaOneEquiv_map, gammaOneEquiv_map, Equiv.apply_symm_apply,
      map_zpow]

@[simp]
private theorem gammaOneEquiv_gammaOneEnd_app (u : (ZMod N)ˣ) (X : EllObj B)
    (α : (gammaOne B N).obj (op X)) :
    (gammaOneEquiv X ((gammaOneEnd B N u).app (op X) α)).1 =
      (gammaOneEquiv X α).1 ^ ((u : ZMod N).cast : ℤ) := by
  simp [gammaOneEnd]

variable (B N) in
/-- **The diamond action of `(ℤ/Nℤ)ˣ` on `[Γ₁(N)]`** (Katz–Mazur, §7.4). A unit `u : (ZMod N)ˣ`
sends a `[Γ₁(N)]`-structure `P` on `(E/S)` to `uP = P ^ ((u : ZMod N).cast : ℤ)`
(`gammaOneEquiv_gammaOneAction_hom_app`), over an arbitrary base scheme `B` and for all `N : ℕ`. -/
noncomputable def gammaOneAction : (ZMod N)ˣ →* Aut (gammaOne B N) where
  toFun u := Aut.of
    { hom := gammaOneEnd B N u
      inv := gammaOneEnd B N u⁻¹
      hom_inv_id := gammaOne_hom_ext fun X α ↦ by
        simp [zpow_zmod_cast_mul_inv (gammaOneEquiv X α).2.pow_eq_one u]
      inv_hom_id := gammaOne_hom_ext fun X α ↦ by
        simpa using zpow_zmod_cast_mul_inv (gammaOneEquiv X α).2.pow_eq_one u⁻¹ }
  map_one' := by
    apply Aut.ext
    rw [Aut.one_asIso]
    apply Iso.ext
    exact gammaOne_hom_ext fun X α ↦ by
      simp [zpow_zmod_cast_one (gammaOneEquiv X α).2.pow_eq_one]
  map_mul' u v := by
    apply Aut.ext
    rw [Aut.mul_asIso]
    apply Iso.ext
    exact gammaOne_hom_ext fun X α ↦ by
      simp [← zpow_zmod_cast_mul (gammaOneEquiv X α).2.pow_eq_one, mul_comm (v : ZMod N)]

/-- A unit `u : (ZMod N)ˣ` sends a `[Γ₁(N)]`-structure `P` to `P ^ ((u : ZMod N).cast : ℤ)`. -/
@[simp]
theorem gammaOneEquiv_gammaOneAction_hom_app (u : (ZMod N)ˣ) (X : EllObj B)
    (α : (gammaOne B N).obj (op X)) :
    (gammaOneEquiv X ((gammaOneAction B N u).asIso.hom.app (op X) α)).1 =
      (gammaOneEquiv X α).1 ^ ((u : ZMod N).cast : ℤ) :=
  gammaOneEquiv_gammaOneEnd_app u X α

/-- The inverse of the diamond automorphism for `u : (ZMod N)ˣ` sends `P` to
`P ^ ((↑u⁻¹ : ZMod N).cast : ℤ)`. -/
@[simp]
theorem gammaOneEquiv_gammaOneAction_inv_app (u : (ZMod N)ˣ) (X : EllObj B)
    (α : (gammaOne B N).obj (op X)) :
    (gammaOneEquiv X ((gammaOneAction B N u).asIso.inv.app (op X) α)).1 =
      (gammaOneEquiv X α).1 ^ ((↑u⁻¹ : ZMod N).cast : ℤ) :=
  gammaOneEquiv_gammaOneEnd_app u⁻¹ X α

/-- For `N ≠ 0`, `u : (ZMod N)ˣ` sends a `[Γ₁(N)]`-structure `P` to `P ^ (u : ZMod N).val`. -/
theorem gammaOneEquiv_gammaOneAction_hom_app_eq_pow_val [NeZero N] (u : (ZMod N)ˣ)
    (X : EllObj B) (α : (gammaOne B N).obj (op X)) :
    (gammaOneEquiv X ((gammaOneAction B N u).asIso.hom.app (op X) α)).1 =
      (gammaOneEquiv X α).1 ^ (u : ZMod N).val := by
  rw [gammaOneEquiv_gammaOneAction_hom_app, zpow_zmod_cast_eq_pow_val]

/-- The unit `-1 : (ZMod N)ˣ` negates the point of a `[Γ₁(N)]`-structure. -/
theorem gammaOneEquiv_gammaOneAction_neg_one_hom_app (X : EllObj B)
    (α : (gammaOne B N).obj (op X)) :
    (gammaOneEquiv X ((gammaOneAction B N (-1)).asIso.hom.app (op X) α)).1 =
      (gammaOneEquiv X α).1⁻¹ := by
  rw [gammaOneEquiv_gammaOneAction_hom_app, Units.val_neg, Units.val_one,
    zpow_zmod_cast_neg_one (gammaOneEquiv X α).2.pow_eq_one]

/-- **The diamond action of `-1` is pullback along `[-1]`**: on any object `X` of `Ell/B`, the unit
`-1 : (ZMod N)ˣ` acts on `[Γ₁(N)](X)` as pullback along the negation arrow `X.neg`. -/
theorem gammaOneAction_neg_one_hom_app (X : EllObj B) (α : (gammaOne B N).obj (op X)) :
    (gammaOneAction B N (-1)).asIso.hom.app (op X) α = (gammaOne B N).map X.neg.op α := by
  apply (gammaOneEquiv X).injective
  apply Subtype.ext
  rw [gammaOneEquiv_gammaOneAction_neg_one_hom_app, gammaOneEquiv_map, X.pointsPullback_neg]

/-- **Compatibility of `gammaOneBaseChangeEquiv` with the diamond action.** Under the
identification of `[Γ₁(N)]`-structures on `E_T` with morphisms `T ⟶ E.exactOrderScheme N`, the
diamond action of `u : (ZMod N)ˣ` postcomposes with `(E.exactOrderSchemeAction N u).asIso.hom`. -/
@[simp]
theorem gammaOneBaseChangeEquiv_gammaOneAction_hom_app (X : EllObj B) (T : Over X.base)
    (u : (ZMod N)ˣ) (α : (gammaOne B N).obj (op (X.baseChangeFunctor.obj T))) :
    gammaOneBaseChangeEquiv X T ((gammaOneAction B N u).asIso.hom.app _ α) =
      gammaOneBaseChangeEquiv X T α ≫ (X.curve.exactOrderSchemeAction N u).asIso.hom := by
  refine (cancel_mono (X.curve.exactOrderSchemeι N)).mp ?_
  have hy : gammaOneBaseChangeEquiv X T α ≫ X.curve.exactOrderSchemeι N =
      X.baseChangePointsEquiv T (gammaOneEquiv _ α).1 :=
    Over.OverMorphism.ext <| by simp [EllipticCurveGeom.exactOrderSchemeι_left]; rfl
  rw [Category.assoc, EllipticCurveGeom.exactOrderSchemeAction_hom_comp_exactOrderSchemeι,
    EllipticCurveGeom.comp_zpow, hy]
  exact Over.OverMorphism.ext <| by
    simp [EllipticCurveGeom.exactOrderSchemeι_left, gammaOneEquiv_gammaOneAction_hom_app,
      ← map_zpow]
    rfl

/-- Postcomposing `a : T ⟶ E.exactOrderScheme N` with `(E.exactOrderSchemeAction N u).asIso.hom`
applies the diamond action of `u` to the classified `[Γ₁(N)]`-structure on `E_T`. -/
@[simp]
theorem gammaOneBaseChangeEquiv_symm_comp_exactOrderSchemeAction_hom (X : EllObj B)
    (T : Over X.base) (u : (ZMod N)ˣ) (a : T ⟶ X.curve.exactOrderScheme N) :
    (gammaOneBaseChangeEquiv X T).symm (a ≫ (X.curve.exactOrderSchemeAction N u).asIso.hom) =
      (gammaOneAction B N u).asIso.hom.app _ ((gammaOneBaseChangeEquiv X T).symm a) := by
  rw [Equiv.symm_apply_eq, gammaOneBaseChangeEquiv_gammaOneAction_hom_app, Equiv.apply_symm_apply]

/-- **The diamond action on `[Γ₁(N)]` is free over nonempty bases where `N` is invertible.** If
`X` has nonempty base `X.base` on whose residue fields `N` is nonzero, and `u : (ZMod N)ˣ` fixes a
`[Γ₁(N)]`-structure `α` on `X`, then `u = 1`. Note that `N` need not be invertible on `B` itself
(for instance `B = Spec ℤ` and `X.base` lies over `D(N)`). -/
theorem eq_one_of_gammaOneAction_hom_app_eq_self {X : EllObj B} [Nonempty X.base]
    (hN : ∀ s : X.base, (N : X.base.residueField s) ≠ 0) {u : (ZMod N)ˣ}
    {α : (gammaOne B N).obj (op X)}
    (h : (gammaOneAction B N u).asIso.hom.app (op X) α = α) : u = 1 :=
  EllipticCurveGeom.eq_one_of_isOfExactOrder_zpow_unit_eq_self hN (gammaOneEquiv X α).2 <| by
    simpa using congrArg (fun β ↦ (gammaOneEquiv X β).1) h

/-- Over a base scheme `B` on whose residue fields `N` is nonzero, `(ZMod N)ˣ` acts freely on
`[Γ₁(N)](X)` for every object `X` of `Ell/B` with nonempty base. -/
theorem eq_one_of_gammaOneAction_hom_app_eq_self_of_base {X : EllObj B} [Nonempty X.base]
    (hN : ∀ b : B, (N : B.residueField b) ≠ 0) {u : (ZMod N)ˣ}
    {α : (gammaOne B N).obj (op X)}
    (h : (gammaOneAction B N u).asIso.hom.app (op X) α = α) : u = 1 :=
  eq_one_of_gammaOneAction_hom_app_eq_self
    (fun _ ↦ X.structureMap.natCast_residueField_ne_zero (hN _)) h

end Diamond

end ModuliProblem

end TauCeti.AlgebraicGeometry
