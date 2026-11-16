/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.RigidSignature.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.MixedDualFunctor

/-!
# Categorical object normalization in the free rigid category

In `TauCeti.RigidObject`, raw formal rigid objects normalize to finite integer-labelled winding
words `WindingWord α`, and `RigidObject.ofWord` realizes any winding word back as a right-associated
tensor product of levelled atoms ending in the unit. Neither associativity, unitality, distribution
of duals over tensor products, nor mixed-dual cancellation `ᘁ(Xᘁ) ≅ X` and `(ᘁX)ᘁ ≅ X` holds as an
equality of raw object expressions, and no pivotal identification `X ≅ Xᘁᘁ` is imposed.

In the free rigid monoidal category `S.FreeRigid`, all of those non-pivotal identifications become
canonical structural isomorphisms built from associators, unitors, the mixed-dual trivializations
`TauCeti.leftDualRightDualIso` and `TauCeti.rightDualLeftDualIso`, and the uniqueness of duals in
`ExactPairing` (`CategoryTheory.rightDualIso`, `CategoryTheory.leftDualIso`,
`CategoryTheory.rightDualTensorIso`, `CategoryTheory.leftDualTensorIso`). Assembling them yields:

* `FreeRigid.ofWordAppendIso`, `FreeRigid.atLevelRightDualIso`, `FreeRigid.atLevelLeftDualIso`,
  `FreeRigid.ofWordRightDualIso`, and `FreeRigid.ofWordLeftDualIso`: compatibility of
  `RigidObject.ofWord` and `RigidObject.atLevel` with concatenation and with both chosen duals,
  reversing port order and shifting integer levels under duality.
* `FreeRigid.normalizeIso X`: the canonical isomorphism `(⟨X⟩ : S.FreeRigid) ≅ ⟨ofWord X.normalize⟩`
  for every formal rigid object `X`, together with `FreeRigid.isoOfNormalizeEq` constructing an
  isomorphism `(⟨X⟩ : S.FreeRigid) ≅ ⟨Y⟩` whenever `X.normalize = Y.normalize`.

## References

* A. Joyal and R. Street, *Planar diagrams and tensor algebra*, unpublished manuscript (1988), §2.
-/

public section

universe u v

open CategoryTheory MonoidalCategory

namespace TauCeti.RigidObject

variable {α : Type u}

/-- Realizing a generator at level `0` yields the generator itself. -/
@[simp]
theorem atLevel_zero (a : α) : atLevel a 0 = of a := by
  simpa using atLevel_natCast a 0

/-- Realizing a generator at level `-1` yields its formal left dual. -/
@[simp]
theorem atLevel_neg_one (a : α) : atLevel a (-1) = (of a).leftDual := by
  simpa using atLevel_negSucc a 0

/-- Realizing a generator at nonnegative level `k + 1` applies one additional formal right dual. -/
theorem atLevel_natCast_add_one (a : α) (k : ℕ) :
    atLevel a ((k : ℤ) + 1) = (atLevel a k).rightDual := by
  rw [← Int.natCast_succ, atLevel_natCast, Function.iterate_succ_apply', atLevel_natCast]

end TauCeti.RigidObject

namespace TauCeti.RigidSignature.FreeRigid

variable {S : RigidSignature.{u, v}}

/-- The chosen formal right dual of the formal unit is canonically isomorphic to
`𝟙_ S.FreeRigid`. -/
noncomputable def unitRightDualIso :
    (⟨RigidObject.unit.rightDual⟩ : S.FreeRigid) ≅ 𝟙_ S.FreeRigid :=
  rightDualIso
    (RightRigidCategory.rightDual (𝟙_ S.FreeRigid)).exact
    exactPairingUnit

/-- The chosen formal left dual of the formal unit is canonically isomorphic to
`𝟙_ S.FreeRigid`. -/
noncomputable def unitLeftDualIso :
    (⟨RigidObject.unit.leftDual⟩ : S.FreeRigid) ≅ 𝟙_ S.FreeRigid :=
  leftDualIso
    (LeftRigidCategory.leftDual (𝟙_ S.FreeRigid)).exact
    exactPairingUnit

/-- The chosen formal right dual of a formal tensor product is canonically isomorphic to the
reversed tensor product of the formal right duals. -/
noncomputable def tensorRightDualIso (X Y : RigidObject S.Obj) :
    (⟨(X.tensor Y).rightDual⟩ : S.FreeRigid) ≅ ⟨Y.rightDual⟩ ⊗ ⟨X.rightDual⟩ :=
  rightDualTensorIso (⟨X⟩ : S.FreeRigid) ⟨Y⟩

/-- The chosen formal left dual of a formal tensor product is canonically isomorphic to the
reversed tensor product of the formal left duals. -/
noncomputable def tensorLeftDualIso (X Y : RigidObject S.Obj) :
    (⟨(X.tensor Y).leftDual⟩ : S.FreeRigid) ≅ ⟨Y.leftDual⟩ ⊗ ⟨X.leftDual⟩ :=
  leftDualTensorIso (⟨X⟩ : S.FreeRigid) ⟨Y⟩

/-- Transport an isomorphism `(⟨X⟩ : S.FreeRigid) ≅ ⟨Y⟩` to the formal right duals via the
contravariant right-adjoint mate isomorphism. -/
noncomputable def rightDualCongr {X Y : RigidObject S.Obj}
    (e : (⟨X⟩ : S.FreeRigid) ≅ ⟨Y⟩) :
    (⟨X.rightDual⟩ : S.FreeRigid) ≅ ⟨Y.rightDual⟩ :=
  e.symm.rightAdjointMate

/-- Transport an isomorphism `(⟨X⟩ : S.FreeRigid) ≅ ⟨Y⟩` to the formal left duals via the
contravariant left-adjoint mate isomorphism. -/
noncomputable def leftDualCongr {X Y : RigidObject S.Obj}
    (e : (⟨X⟩ : S.FreeRigid) ≅ ⟨Y⟩) :
    (⟨X.leftDual⟩ : S.FreeRigid) ≅ ⟨Y.leftDual⟩ :=
  e.symm.leftAdjointMate

/-- Realizing a concatenated winding word is canonically isomorphic to tensoring the realizations of
its two factors, using left unitality and associativity in `S.FreeRigid`. -/
noncomputable def ofWordAppendIso :
    ∀ (L M : WindingWord S.Obj),
      (⟨RigidObject.ofWord (L ++ M)⟩ : S.FreeRigid) ≅
        ⟨RigidObject.ofWord L⟩ ⊗ ⟨RigidObject.ofWord M⟩
  | [], M =>
    eqToIso (by simp) ≪≫
      (λ_ (⟨RigidObject.ofWord M⟩ : S.FreeRigid)).symm ≪≫
      eqToIso (by ext; simp; rfl)
  | (a, n) :: L, M =>
    eqToIso (by ext; simp; rfl) ≪≫
      (Iso.refl (⟨RigidObject.atLevel a n⟩ : S.FreeRigid) ⊗ᵢ ofWordAppendIso L M) ≪≫
      (α_ (⟨RigidObject.atLevel a n⟩ : S.FreeRigid)
        ⟨RigidObject.ofWord L⟩ ⟨RigidObject.ofWord M⟩).symm ≪≫
      eqToIso (by ext; simp; rfl)

/-- Taking the formal right dual of a realized atom at integer level `n` is canonically isomorphic
to the realized atom at level `n + 1`: for `n ≥ 0` the two raw expressions coincide, while for
`n < 0` one outer left dual cancels against the right dual via
`TauCeti.rightDualLeftDualIso`. -/
noncomputable def atLevelRightDualIso (a : S.Obj) :
    ∀ n : ℤ, (⟨(RigidObject.atLevel a n).rightDual⟩ : S.FreeRigid) ≅
      ⟨RigidObject.atLevel a (n + 1)⟩
  | .ofNat k =>
    eqToIso <| congrArg FreeRigid.mk <| by
      change (RigidObject.atLevel a (k : ℤ)).rightDual = RigidObject.atLevel a ((k : ℤ) + 1)
      exact (RigidObject.atLevel_natCast_add_one a k).symm
  | .negSucc 0 =>
    have h0 : Int.negSucc 0 = -1 := rfl
    eqToIso (by rw [TauCeti.rightDualLeftDualFunctor_obj]; ext; simp [h0]; rfl) ≪≫
      (TauCeti.rightDualLeftDualIso S.FreeRigid).app (of a) ≪≫
      eqToIso (congrArg FreeRigid.mk (by simp [h0]))
  | .negSucc (k + 1) =>
    have hk : Int.negSucc (k + 1) + 1 = Int.negSucc k := by omega
    eqToIso (by
      rw [TauCeti.rightDualLeftDualFunctor_obj]
      ext
      rw [RigidObject.atLevel_negSucc, Function.iterate_succ_apply', ← RigidObject.atLevel_negSucc]
      rfl) ≪≫
      (TauCeti.rightDualLeftDualIso S.FreeRigid).app ⟨RigidObject.atLevel a (.negSucc k)⟩ ≪≫
      eqToIso (congrArg FreeRigid.mk (by rw [hk]))

/-- Taking the formal left dual of a realized atom at integer level `n` is canonically isomorphic
to the realized atom at level `n - 1`: for `n ≤ 0` the two raw expressions coincide, while for
`n > 0` one outer right dual cancels against the left dual via
`TauCeti.leftDualRightDualIso`. -/
noncomputable def atLevelLeftDualIso (a : S.Obj) :
    ∀ n : ℤ, (⟨(RigidObject.atLevel a n).leftDual⟩ : S.FreeRigid) ≅
      ⟨RigidObject.atLevel a (n - 1)⟩
  | .ofNat 0 =>
    eqToIso <| congrArg FreeRigid.mk <| by
      change (RigidObject.atLevel a 0).leftDual = RigidObject.atLevel a (0 - 1)
      simp
  | .ofNat (k + 1) =>
    have h1 : (Int.ofNat (k + 1) : ℤ) = (k : ℤ) + 1 := rfl
    have hk : (Int.ofNat (k + 1) : ℤ) - 1 = (k : ℤ) := by omega
    eqToIso (by
      rw [TauCeti.leftDualRightDualFunctor_obj]
      ext
      rw [h1, RigidObject.atLevel_natCast_add_one]
      rfl) ≪≫
      (TauCeti.leftDualRightDualIso S.FreeRigid).app ⟨RigidObject.atLevel a (k : ℤ)⟩ ≪≫
      eqToIso (congrArg FreeRigid.mk (by rw [hk]))
  | .negSucc k =>
    have hk : Int.negSucc k - 1 = Int.negSucc (k + 1) := by omega
    eqToIso <| congrArg FreeRigid.mk <| by
      simp only [hk, RigidObject.atLevel_negSucc, Function.iterate_succ_apply']

/-- Taking the formal right dual of the realization of a winding word is canonically isomorphic to
realizing `WindingWord.rightDual L` (which reverses port order and shifts every level by `+1`). -/
noncomputable def ofWordRightDualIso :
    ∀ L : WindingWord S.Obj,
      (⟨(RigidObject.ofWord L).rightDual⟩ : S.FreeRigid) ≅
        ⟨RigidObject.ofWord (WindingWord.rightDual L)⟩
  | [] =>
    eqToIso (by simp) ≪≫
      unitRightDualIso ≪≫
      eqToIso (by ext; simp; rfl)
  | (a, n) :: L =>
    eqToIso (by simp) ≪≫
      tensorRightDualIso (RigidObject.atLevel a n) (RigidObject.ofWord L) ≪≫
      (ofWordRightDualIso L ⊗ᵢ
        (atLevelRightDualIso a n ≪≫
          (ρ_ (⟨RigidObject.atLevel a (n + 1)⟩ : S.FreeRigid)).symm ≪≫
          eqToIso (by ext; simp; rfl))) ≪≫
      (ofWordAppendIso (WindingWord.rightDual L) [(a, n + 1)]).symm ≪≫
      eqToIso (by simp)

/-- Taking the formal left dual of the realization of a winding word is canonically isomorphic to
realizing `WindingWord.leftDual L` (which reverses port order and shifts every level by `-1`). -/
noncomputable def ofWordLeftDualIso :
    ∀ L : WindingWord S.Obj,
      (⟨(RigidObject.ofWord L).leftDual⟩ : S.FreeRigid) ≅
        ⟨RigidObject.ofWord (WindingWord.leftDual L)⟩
  | [] =>
    eqToIso (by simp) ≪≫
      unitLeftDualIso ≪≫
      eqToIso (by ext; simp; rfl)
  | (a, n) :: L =>
    eqToIso (by simp) ≪≫
      tensorLeftDualIso (RigidObject.atLevel a n) (RigidObject.ofWord L) ≪≫
      (ofWordLeftDualIso L ⊗ᵢ
        (atLevelLeftDualIso a n ≪≫
          (ρ_ (⟨RigidObject.atLevel a (n - 1)⟩ : S.FreeRigid)).symm ≪≫
          eqToIso (by ext; simp; rfl))) ≪≫
      (ofWordAppendIso (WindingWord.leftDual L) [(a, n - 1)]).symm ≪≫
      eqToIso (by simp)

/-- Every formal rigid object `X` is canonically isomorphic in `S.FreeRigid` to the realization of
its normalized winding word `X.normalize`. -/
noncomputable def normalizeIso :
    ∀ X : RigidObject S.Obj,
      (⟨X⟩ : S.FreeRigid) ≅ ⟨RigidObject.ofWord X.normalize⟩
  | .of a =>
    (ρ_ (of a)).symm ≪≫
      eqToIso (by ext; simp; rfl)
  | .unit =>
    eqToIso (by simp)
  | .tensor X Y =>
    (normalizeIso X ⊗ᵢ normalizeIso Y) ≪≫
      (ofWordAppendIso X.normalize Y.normalize).symm ≪≫
      eqToIso (by simp)
  | .rightDual X =>
    rightDualCongr (normalizeIso X) ≪≫
      ofWordRightDualIso X.normalize ≪≫
      eqToIso (by simp)
  | .leftDual X =>
    leftDualCongr (normalizeIso X) ≪≫
      ofWordLeftDualIso X.normalize ≪≫
      eqToIso (by simp)

@[simp]
theorem normalizeIso_unit :
    normalizeIso (.unit : RigidObject S.Obj) =
      eqToIso (by simp) := by rfl

@[simp]
theorem normalizeIso_tensor (X Y : RigidObject S.Obj) :
    normalizeIso (X.tensor Y) =
      (normalizeIso X ⊗ᵢ normalizeIso Y) ≪≫
        (ofWordAppendIso X.normalize Y.normalize).symm ≪≫
        eqToIso (by simp) := by rfl

@[simp]
theorem normalizeIso_rightDual (X : RigidObject S.Obj) :
    normalizeIso (X : RigidObject S.Obj).rightDual =
      rightDualCongr (normalizeIso X) ≪≫
        ofWordRightDualIso X.normalize ≪≫
        eqToIso (by simp) := by rfl

@[simp]
theorem normalizeIso_leftDual (X : RigidObject S.Obj) :
    normalizeIso (X : RigidObject S.Obj).leftDual =
      leftDualCongr (normalizeIso X) ≪≫
        ofWordLeftDualIso X.normalize ≪≫
        eqToIso (by simp) := by rfl

/-- Any two formal rigid objects with the same normalized winding word are canonically isomorphic in
`S.FreeRigid`. -/
noncomputable def isoOfNormalizeEq {X Y : RigidObject S.Obj} (h : X.normalize = Y.normalize) :
    (⟨X⟩ : S.FreeRigid) ≅ ⟨Y⟩ :=
  normalizeIso X ≪≫
    eqToIso (congrArg (fun L ↦ (⟨RigidObject.ofWord L⟩ : S.FreeRigid)) h) ≪≫
    (normalizeIso Y).symm

@[simp]
theorem isoOfNormalizeEq_refl (X : RigidObject S.Obj) :
    isoOfNormalizeEq (rfl : X.normalize = X.normalize) = Iso.refl _ := by
  simp [isoOfNormalizeEq]

@[simp]
theorem isoOfNormalizeEq_symm {X Y : RigidObject S.Obj} (h : X.normalize = Y.normalize) :
    (isoOfNormalizeEq h).symm = isoOfNormalizeEq h.symm := by
  ext
  simp [isoOfNormalizeEq]

theorem isoOfNormalizeEq_trans {X Y Z : RigidObject S.Obj}
    (hXY : X.normalize = Y.normalize) (hYZ : Y.normalize = Z.normalize) :
    isoOfNormalizeEq (hXY.trans hYZ) =
      isoOfNormalizeEq hXY ≪≫ isoOfNormalizeEq hYZ := by
  ext
  simp [isoOfNormalizeEq, eqToHom_trans_assoc]

end TauCeti.RigidSignature.FreeRigid
