/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Product
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.FiberDimension

/-!
# Relative dimension of abelian schemes

For an abelian scheme `A` over an arbitrary base scheme `S`, the **relative dimension**
`A.relativeDimension : S → ℕ` assigns to each point `s : S` the fibre dimension of the smooth
structure morphism `A.toOver.hom : A.toScheme ⟶ S` at `s`.

Building on `TauCeti.AlgebraicGeometry.Morphisms.Smooth.FiberDimension`, this file establishes:
* exact equality between `A.relativeDimension s` and `topologicalKrullDim (A.toOver.hom.fiber s)`;
* local constancy of `A.relativeDimension` on `S`;
* equivalence between constant relative dimension `g` and
  `SmoothOfRelativeDimension g A.toOver.hom`;
* invariance under isomorphism, base change (`(A.baseChange f).relativeDimension t =
  A.relativeDimension (f t)`), vanishing on `identity S`, and additivity on binary products
  (`(A.prod B).relativeDimension s = A.relativeDimension s + B.relativeDimension s`);
* characterization of relative dimension zero: `A` has relative dimension zero everywhere if and
  only if `A.toOver.hom` is an isomorphism, iff `A.zeroSection` is an isomorphism, iff `A` is a
  zero object of `AbelianScheme S` (isomorphic to `identity S`), in which case `A.mulBy n = 𝟙 _`
  for every `n : ℤ`.

## Main declarations

* `TauCeti.AlgebraicGeometry.AbelianScheme.relativeDimension`: the fibre-dimension function
  `S → ℕ` of an abelian scheme `A` over `S`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.isLocallyConstant_relativeDimension`: local constancy.
* `TauCeti.AlgebraicGeometry.AbelianScheme.relativeDimension_baseChange`: compatibility with
  base change.
* `TauCeti.AlgebraicGeometry.AbelianScheme.relativeDimension_prod`: additivity on products.
* `TauCeti.AlgebraicGeometry.AbelianScheme.isoIdentityOfRelativeDimensionZero`: every abelian
  scheme of relative dimension zero is canonically isomorphic to `identity S`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.isZero_iff_forall_relativeDimension_eq_zero`: zero
  objects of `AbelianScheme S` are precisely those of relative dimension zero everywhere.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianScheme

variable {S T : Scheme.{u}}

noncomputable section

/-- The relative dimension of an abelian scheme `A` over `S` at a point `s : S`, defined as the
fibre dimension of its structure morphism `A.toOver.hom` at `s`. -/
def relativeDimension (A : AbelianScheme S) (s : S) : ℕ :=
  A.toOver.hom.fiberDimension s

lemma relativeDimension_def (A : AbelianScheme S) (s : S) :
    A.relativeDimension s = A.toOver.hom.fiberDimension s :=
  (rfl)

/-- The topological Krull dimension of the scheme-theoretic fibre of `A` over `s : S` equals
`A.relativeDimension s`. -/
lemma topologicalKrullDim_fiber_eq_relativeDimension (A : AbelianScheme S) (s : S) :
    topologicalKrullDim (A.toOver.hom.fiber s) = (A.relativeDimension s : WithBot ℕ∞) :=
  A.toOver.hom.topologicalKrullDim_fiber_eq_fiberDimension s

/-- The fibre of `A` over `s : S` is smooth over `Spec κ(s)` of relative dimension
`A.relativeDimension s`. -/
lemma smoothOfRelativeDimension_fiber (A : AbelianScheme S) (s : S) :
    SmoothOfRelativeDimension (A.relativeDimension s)
      (A.toOver.hom.fiberToSpecResidueField s) :=
  A.toOver.hom.smoothOfRelativeDimension_fiberToSpecResidueField s

/-- If `A.toOver.hom` is smooth of constant relative dimension `g`, then `A.relativeDimension s = g`
at every point `s : S`. -/
lemma relativeDimension_eq_of_smoothOfRelativeDimension (A : AbelianScheme S) {g : ℕ}
    [SmoothOfRelativeDimension g A.toOver.hom] (s : S) :
    A.relativeDimension s = g :=
  A.toOver.hom.fiberDimension_eq_of_smoothOfRelativeDimension s

/-- The relative dimension of an abelian scheme is a locally constant function on the base `S`. -/
lemma isLocallyConstant_relativeDimension (A : AbelianScheme S) :
    IsLocallyConstant A.relativeDimension :=
  A.toOver.hom.isLocallyConstant_fiberDimension

/-- An abelian scheme is smooth of constant relative dimension `g` if and only if its relative
dimension is `g` at every point of `S`. -/
lemma smoothOfRelativeDimension_iff_forall_relativeDimension_eq (A : AbelianScheme S) (g : ℕ) :
    SmoothOfRelativeDimension g A.toOver.hom ↔ ∀ s : S, A.relativeDimension s = g :=
  TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_forall_fiberDimension_eq A.toOver.hom g

/-- Isomorphic abelian schemes have the same relative dimension at every point of `S`. -/
lemma relativeDimension_eq_of_iso {A B : AbelianScheme S} (e : A ≅ B) (s : S) :
    A.relativeDimension s = B.relativeDimension s := by
  have h : (isoToScheme e).hom ≫ B.toOver.hom = A.toOver.hom := by
    simpa only [isoToScheme_hom] using Hom.toSchemeHom_comp_hom e.hom
  rw [relativeDimension_def, relativeDimension_def, ← h]
  exact Scheme.Hom.fiberDimension_comp_of_isIso_left (isoToScheme e).hom B.toOver.hom s

/-- The identity abelian scheme over `S` has relative dimension zero at every point. -/
@[simp]
lemma relativeDimension_identity (s : S) : (identity S).relativeDimension s = 0 := by
  have hiso : IsIso (identity S).toOver.hom := by
    have h := (toSchemeHom_toIdentity (identity S)).symm
    have hid : toIdentity (identity S) = 𝟙 (identity S) := Subsingleton.elim _ _
    rw [hid, Hom.toSchemeHom_id, Category.id_comp] at h
    rw [h]
    infer_instance
  exact (identity S).toOver.hom.fiberDimension_of_isIso s

/-- Base change pulls back the relative dimension along the base morphism. -/
@[simp]
lemma relativeDimension_baseChange (A : AbelianScheme S) (f : T ⟶ S) (t : T) :
    (A.baseChange f).relativeDimension t = A.relativeDimension (f t) := by
  rw [relativeDimension_def, relativeDimension_def, baseChange_toOver]
  exact Scheme.Hom.fiberDimension_pullback_snd A.toOver.hom f t

/-- Relative dimension is additive on binary products of abelian schemes. -/
@[simp]
lemma relativeDimension_prod (A B : AbelianScheme S) (s : S) :
    (A.prod B).relativeDimension s = A.relativeDimension s + B.relativeDimension s := by
  rw [relativeDimension_def, relativeDimension_def, relativeDimension_def, prod_toOver,
    Over.tensorObj_hom]
  exact Scheme.Hom.fiberDimension_pullback_fst_comp A.toOver.hom B.toOver.hom s

/-! ### Relative dimension zero -/

/-- The structure morphism of an abelian scheme is an isomorphism if and only if its relative
dimension is zero at every point of `S`. -/
lemma isIso_toOver_hom_iff_forall_relativeDimension_eq_zero (A : AbelianScheme S) :
    IsIso A.toOver.hom ↔ ∀ s : S, A.relativeDimension s = 0 :=
  TauCeti.AlgebraicGeometry.isIso_iff_forall_fiberDimension_eq_zero A.toOver.hom

/-- The zero section of an abelian scheme is an isomorphism if and only if its relative dimension
is zero at every point of `S`. -/
lemma isIso_zeroSection_iff_forall_relativeDimension_eq_zero (A : AbelianScheme S) :
    IsIso A.zeroSection ↔ ∀ s : S, A.relativeDimension s = 0 := by
  rw [← isIso_toOver_hom_iff_forall_relativeDimension_eq_zero]
  have : IsIso (A.zeroSection ≫ A.toOver.hom) := by
    rw [A.zeroSection_comp_toOver_hom]
    infer_instance
  exact ⟨fun _ ↦ IsIso.of_isIso_comp_left A.zeroSection A.toOver.hom,
    fun _ ↦ IsIso.of_isIso_comp_right A.zeroSection A.toOver.hom⟩

/-- An abelian scheme whose relative dimension vanishes everywhere is canonically isomorphic to
`identity S`. -/
def isoIdentityOfRelativeDimensionZero (A : AbelianScheme S)
    (h : ∀ s : S, A.relativeDimension s = 0) : A ≅ identity S where
  hom := toIdentity A
  inv := fromIdentity A
  hom_inv_id := by
    have : IsIso A.toOver.hom :=
      (isIso_toOver_hom_iff_forall_relativeDimension_eq_zero A).mpr h
    apply Hom.ext
    rw [← cancel_mono A.toOver.hom, Hom.toSchemeHom_comp_hom, Hom.toSchemeHom_id,
      Category.id_comp]
  inv_hom_id := Subsingleton.elim _ _

/-- An abelian scheme is a zero object of `AbelianScheme S` if and only if its relative dimension
is zero at every point of `S`. -/
lemma isZero_iff_forall_relativeDimension_eq_zero (A : AbelianScheme S) :
    IsZero A ↔ ∀ s : S, A.relativeDimension s = 0 := by
  constructor
  · intro hA s
    let e : A ≅ identity S := hA.iso (isZeroIdentity S)
    rw [relativeDimension_eq_of_iso e s, relativeDimension_identity]
  · intro h
    exact (isZeroIdentity S).of_iso (isoIdentityOfRelativeDimensionZero A h)

/-- On an abelian scheme of relative dimension zero, multiplication by every integer `n` is the
identity morphism. -/
lemma mulBy_eq_id_of_relativeDimension_eq_zero (A : AbelianScheme S)
    (h : ∀ s : S, A.relativeDimension s = 0) (n : ℤ) :
    A.mulBy n = 𝟙 A.toOver := by
  let e : A ≅ identity S := isoIdentityOfRelativeDimensionZero A h
  have hcomp := Hom.mulBy_comp e.hom n
  rw [mulBy_identity, Category.comp_id] at hcomp
  have : IsIso (Hom.toOverHom e.hom) := by
    rw [← isoToOver_hom e]
    infer_instance
  rw [← cancel_mono (Hom.toOverHom e.hom), hcomp, Category.id_comp]

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti
