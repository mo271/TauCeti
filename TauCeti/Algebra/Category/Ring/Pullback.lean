/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import TauCeti.RingTheory.Pullback

/-!
# Explicit pullback cones in `RingCat`

For morphisms `f : A ⟶ C` and `g : B ⟶ C` in `RingCat.{u}` (with no commutativity assumption),
the explicit subring fibre product `RingHom.pullback f.hom g.hom` together with the projections
`RingHom.pullbackFst` and `RingHom.pullbackSnd` forms a limiting `PullbackCone` in `RingCat.{u}`
(paralleling `CommRingCat.pullbackCone` and `CommRingCat.pullbackConeIsLimit` in
`Mathlib.Algebra.Category.Ring.Constructions`).

Consequently, for possibly noncommutative rings `R, S, T : Type u` and ring homomorphisms
`f : R →+* T` and `g : S →+* T`, the commuting square on `RingCat.of (f.pullback g)` is a
categorical pullback (`RingCat.isPullback_pullback`), yielding a canonical isomorphism
`RingCat.isoPullback : RingCat.of (f.pullback g) ≅ Limits.pullback (ofHom f) (ofHom g)`.

## Main definitions

* `RingCat.pullbackCone`: the explicit `PullbackCone` with apex `RingCat.of (f.hom.pullback g.hom)`.
* `RingCat.pullbackConeIsLimit`: witness that `RingCat.pullbackCone f g` is a limit cone.
* `RingCat.isoPullback`: canonical isomorphism between `RingCat.of (f.pullback g)` and the
  categorical pullback in `RingCat.{u}`.

## Main results

* `RingCat.isPullback_pullback`: the square formed by `RingHom.pullbackFst`, `RingHom.pullbackSnd`,
  `f`, and `g` is a categorical pullback in `RingCat.{u}`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §2.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter I, §2.6.
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingCat

section Cone

variable {A B C : RingCat.{u}}

/-- In `RingCat.{u}`, the fibre product `f.hom.pullback g.hom` with projections `pullbackFst` and
`pullbackSnd` forms an explicit `PullbackCone` for `f : A ⟶ C` and `g : B ⟶ C`. -/
@[expose]
def pullbackCone (f : A ⟶ C) (g : B ⟶ C) : PullbackCone f g :=
  PullbackCone.mk
    (ofHom (f.hom.pullbackFst g.hom))
    (ofHom (f.hom.pullbackSnd g.hom))
    (hom_ext (f.hom.pullback_comm_sq g.hom))

/-- Apex of `RingCat.pullbackCone f g`. -/
@[simp]
theorem pullbackCone_pt (f : A ⟶ C) (g : B ⟶ C) :
    (pullbackCone f g).pt = of (f.hom.pullback g.hom) :=
  rfl

/-- First projection of `RingCat.pullbackCone f g`. -/
@[simp]
theorem pullbackCone_fst (f : A ⟶ C) (g : B ⟶ C) :
    (pullbackCone f g).fst = ofHom (f.hom.pullbackFst g.hom) :=
  rfl

/-- Second projection of `RingCat.pullbackCone f g`. -/
@[simp]
theorem pullbackCone_snd (f : A ⟶ C) (g : B ⟶ C) :
    (pullbackCone f g).snd = ofHom (f.hom.pullbackSnd g.hom) :=
  rfl

/-- `RingCat.pullbackCone f g` is a limit cone in `RingCat.{u}`. -/
def pullbackConeIsLimit (f : A ⟶ C) (g : B ⟶ C) : IsLimit (pullbackCone f g) :=
  PullbackCone.IsLimit.mk
    (hom_ext (f.hom.pullback_comm_sq g.hom))
    (fun s ↦ ofHom (f.hom.pullbackLift g.hom s.fst.hom s.snd.hom (congrArg Hom.hom s.condition)))
    (fun _ ↦ hom_ext (f.hom.pullbackFst_comp_pullbackLift g.hom _ _ _))
    (fun _ ↦ hom_ext (f.hom.pullbackSnd_comp_pullbackLift g.hom _ _ _))
    (fun _ _ h₁ h₂ ↦ hom_ext <| RingHom.pullback_hom_ext
      ((congrArg Hom.hom h₁).trans (f.hom.pullbackFst_comp_pullbackLift g.hom _ _ _).symm)
      ((congrArg Hom.hom h₂).trans (f.hom.pullbackSnd_comp_pullbackLift g.hom _ _ _).symm))

end Cone

section IsPullback

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- For possibly noncommutative rings `R, S, T : Type u` and ring homomorphisms `f : R →+* T` and
`g : S →+* T`, the square formed by `f.pullbackFst g`, `f.pullbackSnd g`, `f`, and `g` is a
categorical pullback square in `RingCat.{u}`. -/
theorem isPullback_pullback (f : R →+* T) (g : S →+* T) :
    IsPullback (ofHom (f.pullbackFst g)) (ofHom (f.pullbackSnd g)) (ofHom f) (ofHom g) where
  w := hom_ext (f.pullback_comm_sq g)
  isLimit' := ⟨pullbackConeIsLimit (ofHom f) (ofHom g)⟩

/-- Canonical isomorphism in `RingCat.{u}` between `RingCat.of (f.pullback g)` and the categorical
pullback `Limits.pullback (ofHom f) (ofHom g)`. -/
noncomputable def isoPullback (f : R →+* T) (g : S →+* T) :
    of (f.pullback g) ≅ Limits.pullback (ofHom f) (ofHom g) :=
  (isPullback_pullback f g).isoPullback

/-- Composing `(isoPullback f g).hom` with `pullback.fst` recovers `f.pullbackFst g`. -/
@[simp]
theorem isoPullback_hom_fst (f : R →+* T) (g : S →+* T) :
    (isoPullback f g).hom ≫ Limits.pullback.fst (ofHom f) (ofHom g) =
      ofHom (f.pullbackFst g) :=
  (isPullback_pullback f g).isoPullback_hom_fst

/-- Composing `(isoPullback f g).hom` with `pullback.snd` recovers `f.pullbackSnd g`. -/
@[simp]
theorem isoPullback_hom_snd (f : R →+* T) (g : S →+* T) :
    (isoPullback f g).hom ≫ Limits.pullback.snd (ofHom f) (ofHom g) =
      ofHom (f.pullbackSnd g) :=
  (isPullback_pullback f g).isoPullback_hom_snd

/-- Composing `(isoPullback f g).inv` with `f.pullbackFst g` recovers `pullback.fst`. -/
theorem isoPullback_inv_fst (f : R →+* T) (g : S →+* T) :
    (isoPullback f g).inv ≫ ofHom (f.pullbackFst g) =
      Limits.pullback.fst (ofHom f) (ofHom g) :=
  (isPullback_pullback f g).isoPullback_inv_fst

/-- Composing `(isoPullback f g).inv` with `f.pullbackSnd g` recovers `pullback.snd`. -/
theorem isoPullback_inv_snd (f : R →+* T) (g : S →+* T) :
    (isoPullback f g).inv ≫ ofHom (f.pullbackSnd g) =
      Limits.pullback.snd (ofHom f) (ofHom g) :=
  (isPullback_pullback f g).isoPullback_inv_snd

end IsPullback

end RingCat
