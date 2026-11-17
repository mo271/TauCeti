/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
public import TauCeti.RingTheory.Depth.Basic
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Sections

/-!
# Basic-open localizations for finite étale covers over punctured spectra

Let `(R, 𝔪)` be a Noetherian local ring of depth at least two, `U` its punctured spectrum, and `X`
a finite étale cover of `U`. For every `g ∈ 𝔪`, the basic open `D(g) ⊆ U` (`openU R g`) is affine
and its ring of sections `LocU R g` is the localization of `R` away from `g`
(`isLocalization_locU`). Similarly, the preimage `openX R X g` in `X` is affine, its ring of
sections `LocX R X g` is the base change of the global sections `Sec R X = Γ(X, 𝒪_X)` along
`R → LocU R g` (`isBaseChange_locX`), and `LocX R X g` is finite projective over `LocU R g`
(`finite_projective_locX`).

Given a morphism of punctured spectra induced by a homomorphism `A → R` of local rings and a
pullback cover `X'` of `X`, the local sections `LocX R X' (algebraMap A R g)` form a base change
of `LocX A X g` along `LocU A g → LocU R (algebraMap A R g)` (`isBaseChange_locX_step`), hence
also of `Sec A X` along `A → LocU R (algebraMap A R g)` (`isBaseChange_localMapAX`).

## Main definitions

* `TauCeti.IsLocalRing.sectionsAlgebra`: the canonical `R`-algebra structure on `Γ(X, 𝒪_X)` for a
  finite étale cover `X` of `puncturedSpectrum R`.
* `TauCeti.IsLocalRing.PuncturedBasicOpen.openU`, `openX`: basic opens `D(g) ⊆ U` and their
  preimages in `X`.
* `TauCeti.IsLocalRing.PuncturedBasicOpen.Sec`, `LocU`, `LocX`: wrapper types carrying the
  canonical `R`- and `LocU`-algebra structures on `Γ(X, ⊤)`, `Γ(U, D(g))`, and `Γ(X, p⁻¹ D(g))`.

## Main results

* `TauCeti.IsLocalRing.PuncturedBasicOpen.isLocalization_locU`: `LocU R g` is the localization of
  `R` away from `g` when `2 ≤ depth R`.
* `TauCeti.IsLocalRing.PuncturedBasicOpen.finite_projective_locX`: `LocX R X g` is finite
  projective over `LocU R g` for `g ∈ 𝔪`.
* `TauCeti.IsLocalRing.PuncturedBasicOpen.isBaseChange_locX`: `LocX R X g` is the base change of
  `Sec R X` to `LocU R g`.
* `TauCeti.IsLocalRing.PuncturedBasicOpen.isBaseChange_locX_step` and `isBaseChange_localMapAX`:
  base change of local sections along a pullback of covers.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open scoped Pointwise

universe u

namespace TauCeti.IsLocalRing

/-- The canonical `R`-algebra structure on the global sections `Γ(X, 𝒪_X)` of a finite étale cover
`X` of the punctured spectrum of `R`. -/
@[expose, instance_reducible]
def sectionsAlgebra (R : Type u) [CommRing R] [IsLocalRing R]
    (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) : Algebra R Γ(X.obj.left, ⊤) :=
  (((Scheme.ΓSpecIso (.of R)).inv ≫ (X.obj.hom ≫ (puncturedSpectrum R).ι).appTop).hom).toAlgebra

namespace PuncturedBasicOpen

section BasicOpen

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The basic open `D(g)` of `puncturedSpectrum R` defined by `g : R`. -/
@[expose]
def openU (g : R) : (puncturedSpectrum R).toScheme.Opens :=
  (puncturedSpectrum R).toScheme.basicOpen
    ((puncturedSpectrum R).ι.appTop ((Scheme.ΓSpecIso (.of R)).inv g))

/-- The basic open of a finite étale cover `X` over `puncturedSpectrum R` defined by `g : R`. -/
@[expose]
def openX (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : R) :
    X.obj.left.Opens :=
  X.obj.left.basicOpen
    ((X.obj.hom ≫ (puncturedSpectrum R).ι).appTop ((Scheme.ΓSpecIso (.of R)).inv g))

private lemma openU_eq_preimage (g : R) :
    openU R g = (puncturedSpectrum R).ι ⁻¹ᵁ
      (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv g) :=
  (Scheme.preimage_basicOpen_top (puncturedSpectrum R).ι _).symm

/-- The basic open `openX R X g` is the preimage of `openU R g` along `X → puncturedSpectrum R`. -/
lemma openX_eq_preimage (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : R) :
    openX R X g = X.obj.hom ⁻¹ᵁ openU R g := by
  rw [openX, openU, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.preimage_basicOpen_top]

/-- Inclusion of basic opens on `puncturedSpectrum R` induces inclusion of their preimages in `X`.
-/
lemma openX_mono {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) {g₁ g₂ : R}
    (hle : openU R g₂ ≤ openU R g₁) :
    openX R X g₂ ≤ openX R X g₁ := by
  rw [openX_eq_preimage, openX_eq_preimage]
  exact fun _ hx ↦ hle hx

/-- The basic open `D(g₁ * g₂)` on `puncturedSpectrum R` is `D(g₁) ⊓ D(g₂)`. -/
lemma openU_mul (g₁ g₂ : R) : openU R (g₁ * g₂) = openU R g₁ ⊓ openU R g₂ := by
  simp [openU, map_mul, Scheme.basicOpen_mul]

/-- The basic open of `g₁ * g₂` on `X` is the intersection of those of `g₁` and `g₂`. -/
lemma openX_mul (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g₁ g₂ : R) :
    openX R X (g₁ * g₂) = openX R X g₁ ⊓ openX R X g₂ := by
  simp [openX, map_mul, Scheme.basicOpen_mul]

private lemma isAffineOpen_openU {g : R} (hg : g ∈ maximalIdeal R) :
    IsAffineOpen (openU R g) := by
  let D : (Spec (.of R)).Opens := (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv g)
  have hDaff : IsAffineOpen D := (isAffineOpen_top (Spec (.of R))).basicOpen _
  have hDle : D ≤ puncturedSpectrum R := fun p hp ↦ by
    refine (mem_puncturedSpectrum_iff R p).mpr fun h ↦ ?_
    have hp' : g ∉ p.asIdeal := by
      have h1 : p ∈ (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv g) := hp
      rw [basicOpen_eq_of_affine] at h1
      exact h1
    exact hp' (h ▸ hg)
  rw [← (puncturedSpectrum R).ι.isAffineOpen_iff_of_isOpenImmersion, openU_eq_preimage,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hDle]
  exact hDaff

private lemma isAffineOpen_openX (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme)
    {g : R} (hg : g ∈ maximalIdeal R) :
    IsAffineOpen (openX R X g) := by
  rw [openX_eq_preimage]
  exact (isAffineOpen_openU R hg).preimage X.obj.hom

private lemma compactSpace_puncturedSpectrum [IsNoetherianRing R] :
    CompactSpace (puncturedSpectrum R).toScheme :=
  isCompact_iff_compactSpace.mp
    (isCompact_puncturedSpectrum_of_fg_maximalIdeal R (maximalIdeal R).fg_of_isNoetherianRing)

private lemma quasiSeparatedSpace_puncturedSpectrum :
    QuasiSeparatedSpace (puncturedSpectrum R).toScheme :=
  quasiSeparatedSpace_of_quasiSeparated (puncturedSpectrum R).ι

private lemma compactSpace_finiteEtale [IsNoetherianRing R]
    (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) :
    CompactSpace X.obj.left := by
  have := compactSpace_puncturedSpectrum R
  exact QuasiCompact.compactSpace_of_compactSpace X.obj.hom

private lemma quasiSeparatedSpace_finiteEtale
    (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) :
    QuasiSeparatedSpace X.obj.left :=
  quasiSeparatedSpace_of_quasiSeparated (X.obj.hom ≫ (puncturedSpectrum R).ι)

/-- Wrapper around `Γ(X, ⊤)` carrying its canonical `R`-algebra structure `sectionsAlgebra R X`. -/
@[expose]
def Sec (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) : Type u :=
  Γ(X.obj.left, ⊤)

/-- Wrapper around `Γ(puncturedSpectrum R, openU R g)` carrying its canonical `R`-algebra
structure. -/
@[expose]
def LocU (g : R) : Type u :=
  Γ((puncturedSpectrum R).toScheme, openU R g)

/-- Wrapper around `Γ(X, openX R X g)` carrying its canonical algebra structures over `R`,
`Sec R X`, and `LocU R g`. -/
@[expose]
def LocX (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : R) : Type u :=
  Γ(X.obj.left, openX R X g)

instance (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) : CommRing (Sec R X) :=
  inferInstanceAs (CommRing Γ(X.obj.left, ⊤))

instance (g : R) : CommRing (LocU R g) :=
  inferInstanceAs (CommRing Γ((puncturedSpectrum R).toScheme, openU R g))

instance (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : R) :
    CommRing (LocX R X g) :=
  inferInstanceAs (CommRing Γ(X.obj.left, openX R X g))

instance (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) : Algebra R (Sec R X) :=
  sectionsAlgebra R X

instance (g : R) : Algebra R (LocU R g) :=
  (((Scheme.ΓSpecIso (.of R)).inv ≫ (puncturedSpectrum R).ι.appTop ≫
    (puncturedSpectrum R).toScheme.presheaf.map
      (homOfLE (le_top : openU R g ≤ ⊤)).op).hom).toAlgebra

instance (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : R) :
    Algebra R (LocX R X g) :=
  (((Scheme.ΓSpecIso (.of R)).inv ≫ (X.obj.hom ≫ (puncturedSpectrum R).ι).appTop ≫
    X.obj.left.presheaf.map (homOfLE (le_top : openX R X g ≤ ⊤)).op).hom).toAlgebra

instance (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : R) :
    Algebra (Sec R X) (LocX R X g) :=
  (X.obj.left.presheaf.map (homOfLE (le_top : openX R X g ≤ ⊤)).op).hom.toAlgebra

instance (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : R) :
    Algebra (LocU R g) (LocX R X g) :=
  (X.obj.hom.appLE (openU R g) (openX R X g) (openX_eq_preimage R X g).le).hom.toAlgebra

instance (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : R) :
    IsScalarTower R (Sec R X) (LocX R X g) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

private lemma openU_to_openX_comm (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : R) :
    ((Scheme.ΓSpecIso (.of R)).inv ≫ (puncturedSpectrum R).ι.appTop ≫
      (puncturedSpectrum R).toScheme.presheaf.map (homOfLE (le_top : openU R g ≤ ⊤)).op) ≫
      X.obj.hom.appLE (openU R g) (openX R X g) (openX_eq_preimage R X g).le =
    ((Scheme.ΓSpecIso (.of R)).inv ≫ (X.obj.hom ≫ (puncturedSpectrum R).ι).appTop) ≫
      X.obj.left.presheaf.map (homOfLE (le_top : openX R X g ≤ ⊤)).op := by
  simp only [Category.assoc, Scheme.Hom.comp_appTop, Scheme.Hom.map_appLE]
  rfl

instance (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : R) :
    IsScalarTower R (LocU R g) (LocX R X g) :=
  IsScalarTower.of_algebraMap_eq fun a ↦
    congrArg (fun f ↦ f a) (openU_to_openX_comm R X g).symm

/-- Global-section pullback map `Sec A X →+* Sec R X'` induced by a scheme morphism
`f : X' ⟶ X`. -/
@[expose]
def secAppTop {A R : Type u} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    {X : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    {X' : FiniteEtaleScheme (puncturedSpectrum R).toScheme}
    (f : X'.obj.left ⟶ X.obj.left) : Sec A X →+* Sec R X' :=
  f.appTop.hom

/-- Restriction map `LocU R g₁ →+* LocU R g₂` for `openU R g₂ ≤ openU R g₁`. -/
@[expose]
def locURes {R : Type u} [CommRing R] [IsLocalRing R] {g₁ g₂ : R}
    (hle : openU R g₂ ≤ openU R g₁) : LocU R g₁ →+* LocU R g₂ :=
  ((puncturedSpectrum R).toScheme.presheaf.map (homOfLE hle).op).hom

/-- Restriction map `LocX R X g₁ →+* LocX R X g₂` for `openX R X g₂ ≤ openX R X g₁`. -/
@[expose]
def locXRes {R : Type u} [CommRing R] [IsLocalRing R]
    {X : FiniteEtaleScheme (puncturedSpectrum R).toScheme} {g₁ g₂ : R}
    (hle : openX R X g₂ ≤ openX R X g₁) : LocX R X g₁ →+* LocX R X g₂ :=
  (X.obj.left.presheaf.map (homOfLE hle).op).hom

/-- Pullback map `LocU R₁ g₁ →+* LocU R₂ g₂` along a morphism of punctured spectra. -/
@[expose]
def locUAppLE {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂]
    [IsLocalRing R₂] (f : (puncturedSpectrum R₂).toScheme ⟶ (puncturedSpectrum R₁).toScheme)
    {g₁ : R₁} {g₂ : R₂} (h : openU R₂ g₂ ≤ f ⁻¹ᵁ openU R₁ g₁) :
    LocU R₁ g₁ →+* LocU R₂ g₂ :=
  (f.appLE (openU R₁ g₁) (openU R₂ g₂) h).hom

/-- Pullback map `LocX R₁ X₁ g₁ →+* LocX R₂ X₂ g₂` along a morphism of finite étale covers. -/
@[expose]
def locXAppLE {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂]
    [IsLocalRing R₂] {X₁ : FiniteEtaleScheme (puncturedSpectrum R₁).toScheme}
    {X₂ : FiniteEtaleScheme (puncturedSpectrum R₂).toScheme}
    (f : X₂.obj.left ⟶ X₁.obj.left)
    {g₁ : R₁} {g₂ : R₂} (h : openX R₂ X₂ g₂ ≤ f ⁻¹ᵁ openX R₁ X₁ g₁) :
    LocX R₁ X₁ g₁ →+* LocX R₂ X₂ g₂ :=
  (f.appLE (openX R₁ X₁ g₁) (openX R₂ X₂ g₂) h).hom

/-- The restriction map `Sec R X → LocX R X g` is `R`-linear. -/
lemma algebraMap_smul_locX {R : Type u} [CommRing R] [IsLocalRing R]
    {X : FiniteEtaleScheme (puncturedSpectrum R).toScheme} {g : R} (c : R) (w : Sec R X) :
    algebraMap (Sec R X) (LocX R X g) (c • w) = c • algebraMap (Sec R X) (LocX R X g) w := by
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R (Sec R X) (LocX R X g),
    ← Algebra.smul_def]

/-- Restriction `locURes` commutes with `algebraMap R (LocU R _)`. -/
lemma locURes_algebraMap {R : Type u} [CommRing R] [IsLocalRing R] {g₁ g₂ : R}
    (hle : openU R g₂ ≤ openU R g₁) (x : R) :
    locURes hle (algebraMap R (LocU R g₁) x) = algebraMap R (LocU R g₂) x := by
  have hcomp : ((Scheme.ΓSpecIso (.of R)).inv ≫ (puncturedSpectrum R).ι.appTop ≫
      (puncturedSpectrum R).toScheme.presheaf.map (homOfLE (le_top : openU R g₁ ≤ ⊤)).op) ≫
      (puncturedSpectrum R).toScheme.presheaf.map (homOfLE hle).op =
      (Scheme.ΓSpecIso (.of R)).inv ≫ (puncturedSpectrum R).ι.appTop ≫
        (puncturedSpectrum R).toScheme.presheaf.map (homOfLE (le_top : openU R g₂ ≤ ⊤)).op := by
    rw [Category.assoc, Category.assoc, ← Functor.map_comp]
    rfl
  exact congrArg (fun f ↦ f x) hcomp

/-- Restriction `locXRes` commutes with `algebraMap (Sec R X) (LocX R X _)`. -/
lemma locXRes_algebraMap {R : Type u} [CommRing R] [IsLocalRing R]
    {X : FiniteEtaleScheme (puncturedSpectrum R).toScheme} {g₁ g₂ : R}
    (hle : openX R X g₂ ≤ openX R X g₁) (x : Sec R X) :
    locXRes hle (algebraMap (Sec R X) (LocX R X g₁) x) = algebraMap (Sec R X) (LocX R X g₂) x := by
  have hcomp : X.obj.left.presheaf.map (homOfLE (le_top : openX R X g₁ ≤ ⊤)).op ≫
      X.obj.left.presheaf.map (homOfLE hle).op =
      X.obj.left.presheaf.map (homOfLE (le_top : openX R X g₂ ≤ ⊤)).op := by
    rw [← Functor.map_comp]
    rfl
  exact congrArg (fun f ↦ f x) hcomp

/-- Restriction `locXRes` is semilinear with respect to `locURes`. -/
lemma locXRes_smul {R : Type u} [CommRing R] [IsLocalRing R]
    (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) {g₁ g₂ : R}
    (hle : openU R g₂ ≤ openU R g₁) (t : LocU R g₁) (x : LocX R X g₁) :
    locXRes (X := X) (openX_mono X hle) (t • x) =
      locURes hle t • locXRes (X := X) (openX_mono X hle) x := by
  have hcomm : X.obj.hom.appLE (openU R g₁) (openX R X g₁) (openX_eq_preimage R X g₁).le ≫
      X.obj.left.presheaf.map (homOfLE (openX_mono X hle)).op =
      (puncturedSpectrum R).toScheme.presheaf.map (homOfLE hle).op ≫
        X.obj.hom.appLE (openU R g₂) (openX R X g₂) (openX_eq_preimage R X g₂).le := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  exact congrArg (· * _) (congrArg (fun f ↦ f t) hcomm)

/-- Pullback `locUAppLE` intertwines `algebraMap R₁ (LocU R₁ g₁)` with `φ : R₁ →+* R₂`. -/
lemma locUAppLE_algebraMap {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂]
    [IsLocalRing R₂] {φ : R₁ →+* R₂}
    {f : (puncturedSpectrum R₂).toScheme ⟶ (puncturedSpectrum R₁).toScheme}
    (hf : f ≫ (puncturedSpectrum R₁).ι = (puncturedSpectrum R₂).ι ≫ Spec.map (CommRingCat.ofHom φ))
    {g₁ : R₁} {g₂ : R₂} (h : openU R₂ g₂ ≤ f ⁻¹ᵁ openU R₁ g₁) (x : R₁) :
    locUAppLE f h (algebraMap R₁ (LocU R₁ g₁) x) = algebraMap R₂ (LocU R₂ g₂) (φ x) := by
  have h1 : (puncturedSpectrum R₁).toScheme.presheaf.map (homOfLE (le_top : openU R₁ g₁ ≤ ⊤)).op ≫
      f.appLE (openU R₁ g₁) (openU R₂ g₂) h =
      f.appTop ≫ (puncturedSpectrum R₂).toScheme.presheaf.map
        (homOfLE (le_top : openU R₂ g₂ ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE]
    rfl
  have hcomp : ((Scheme.ΓSpecIso (.of R₁)).inv ≫ (puncturedSpectrum R₁).ι.appTop ≫
      (puncturedSpectrum R₁).toScheme.presheaf.map (homOfLE (le_top : openU R₁ g₁ ≤ ⊤)).op) ≫
      f.appLE (openU R₁ g₁) (openU R₂ g₂) h =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of R₂)).inv ≫ (puncturedSpectrum R₂).ι.appTop ≫
        (puncturedSpectrum R₂).toScheme.presheaf.map (homOfLE (le_top : openU R₂ g₂ ≤ ⊤)).op := by
    rw [Category.assoc, Category.assoc, h1, ← Scheme.Hom.comp_appTop_assoc, hf,
      Scheme.Hom.comp_appTop_assoc, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc]
  exact congrArg (fun k ↦ k x) hcomp

/-- Pullback `locXAppLE` intertwines restriction from global sections with `secAppTop`. -/
lemma locXAppLE_algebraMap {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂]
    [IsLocalRing R₂] {X₁ : FiniteEtaleScheme (puncturedSpectrum R₁).toScheme}
    {X₂ : FiniteEtaleScheme (puncturedSpectrum R₂).toScheme} (f : X₂.obj.left ⟶ X₁.obj.left)
    {g₁ : R₁} {g₂ : R₂} (h : openX R₂ X₂ g₂ ≤ f ⁻¹ᵁ openX R₁ X₁ g₁) (x : Sec R₁ X₁) :
    locXAppLE f h (algebraMap (Sec R₁ X₁) (LocX R₁ X₁ g₁) x) =
      algebraMap (Sec R₂ X₂) (LocX R₂ X₂ g₂) (secAppTop f x) := by
  have hcomp : X₁.obj.left.presheaf.map (homOfLE (le_top : openX R₁ X₁ g₁ ≤ ⊤)).op ≫
      f.appLE (openX R₁ X₁ g₁) (openX R₂ X₂ g₂) h =
      f.appTop ≫ X₂.obj.left.presheaf.map (homOfLE (le_top : openX R₂ X₂ g₂ ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE]
    rfl
  exact congrArg (fun k ↦ k x) hcomp

/-- Pullback `locXAppLE` is semilinear with respect to `locUAppLE`. -/
lemma locXAppLE_smul {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂]
    [IsLocalRing R₂] {X₁ : FiniteEtaleScheme (puncturedSpectrum R₁).toScheme}
    {X₂ : FiniteEtaleScheme (puncturedSpectrum R₂).toScheme}
    (fU : (puncturedSpectrum R₂).toScheme ⟶ (puncturedSpectrum R₁).toScheme)
    (fX : X₂.obj.left ⟶ X₁.obj.left) (hcomm : fX ≫ X₁.obj.hom = X₂.obj.hom ≫ fU)
    {g₁ : R₁} {g₂ : R₂} (hU : openU R₂ g₂ ≤ fU ⁻¹ᵁ openU R₁ g₁)
    (hX : openX R₂ X₂ g₂ ≤ fX ⁻¹ᵁ openX R₁ X₁ g₁) (t : LocU R₁ g₁) (x : LocX R₁ X₁ g₁) :
    locXAppLE fX hX (t • x) = locUAppLE fU hU t • locXAppLE fX hX x := by
  have hsq : X₁.obj.hom.appLE (openU R₁ g₁) (openX R₁ X₁ g₁) (openX_eq_preimage R₁ X₁ g₁).le ≫
      fX.appLE (openX R₁ X₁ g₁) (openX R₂ X₂ g₂) hX =
      fU.appLE (openU R₁ g₁) (openU R₂ g₂) hU ≫
        X₂.obj.hom.appLE (openU R₂ g₂) (openX R₂ X₂ g₂) (openX_eq_preimage R₂ X₂ g₂).le := by
    have haux : ∀ {k₁ k₂ : X₂.obj.left ⟶ (puncturedSpectrum R₁).toScheme} (_ : k₁ = k₂)
        (h₁ : openX R₂ X₂ g₂ ≤ k₁ ⁻¹ᵁ openU R₁ g₁) (h₂ : openX R₂ X₂ g₂ ≤ k₂ ⁻¹ᵁ openU R₁ g₁),
        k₁.appLE (openU R₁ g₁) (openX R₂ X₂ g₂) h₁ =
          k₂.appLE (openU R₁ g₁) (openX R₂ X₂ g₂) h₂ := by
      rintro k _ rfl _ _; rfl
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact haux hcomm _ _
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  exact congrArg (· * _) (congrArg (fun k ↦ k t) hsq)

/-- When `2 ≤ depth R`, `LocU R g` is the localization of `R` away from `g`. -/
lemma isLocalization_locU [IsNoetherianRing R]
    (hdepthR : 2 ≤ depth (ModuleCat.of R R)) (g : R) :
    IsLocalization.Away g (LocU R g) := by
  let U := puncturedSpectrum R
  have := compactSpace_puncturedSpectrum R
  have := quasiSeparatedSpace_puncturedSpectrum R
  have : IsIso U.ι.appTop := isIso_ι_appTop_puncturedSpectrum R hdepthR
  let e : CommRingCat.of R ≅ Γ(U.toScheme, ⊤) := (Scheme.ΓSpecIso (.of R)).symm ≪≫ asIso U.ι.appTop
  let s : Γ(U.toScheme, ⊤) := U.ι.appTop ((Scheme.ΓSpecIso (.of R)).inv g)
  let res : Γ(U.toScheme, ⊤) ⟶ Γ(U.toScheme, U.toScheme.basicOpen s) :=
    U.toScheme.presheaf.map (homOfLE (le_top : U.toScheme.basicOpen s ≤ ⊤)).op
  have hloc : IsLocalization.Away s Γ(U.toScheme, U.toScheme.basicOpen s) :=
    isLocalization_basicOpen_of_qcqs (X := U.toScheme) (U := ⊤) isCompact_univ
      isQuasiSeparated_univ s
  constructor; constructor
  · rintro ⟨_, k, rfl⟩
    have hu : IsUnit (res (s ^ k)) := hloc.1.map_units ⟨_, k, rfl⟩
    have hpow : algebraMap R (LocU R g) (g ^ k) = res (s ^ k) :=
      congrArg res (map_pow e.hom.hom g k)
    rwa [hpow]
  · intro z
    let z' : Γ(U.toScheme, U.toScheme.basicOpen s) := z
    obtain ⟨⟨x, ⟨_, k, rfl⟩⟩, hx⟩ := hloc.1.surj z'
    refine ⟨⟨e.inv x, ⟨_, k, rfl⟩⟩, ?_⟩
    change z' * res (e.hom.hom (g ^ k)) = res (e.hom (e.inv x))
    rw [map_pow, ← CommRingCat.comp_apply e.inv e.hom, Iso.inv_hom_id, CommRingCat.id_apply]
    exact hx
  · intro x y hxy
    have hxy' : res (e.hom x) = res (e.hom y) := hxy
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := hloc.1.exists_of_eq hxy'
    refine ⟨⟨_, k, rfl⟩, ?_⟩
    have hke : e.hom (g ^ k * x) = e.hom (g ^ k * y) := by
      rw [map_mul, map_pow, map_mul, map_pow]
      exact hk
    exact (ConcreteCategory.bijective_of_isIso e.hom).1 hke

private lemma isLocalization_locX [IsNoetherianRing R]
    (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : R) :
    IsLocalization.Away (algebraMap R (Sec R X) g) (LocX R X g) := by
  have := compactSpace_finiteEtale R X
  have := quasiSeparatedSpace_finiteEtale R X
  exact isLocalization_basicOpen_of_qcqs (X := X.obj.left) (U := ⊤) isCompact_univ
    isQuasiSeparated_univ _

/-- For `g ∈ maximalIdeal R`, the local section ring `LocX R X g` of a finite étale cover `X` is
finite and projective over `LocU R g`. -/
lemma finite_projective_locX [IsNoetherianRing R]
    (hdepthR : 2 ≤ depth (ModuleCat.of R R))
    (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) {g : R} (hg : g ∈ maximalIdeal R) :
    Module.Finite (LocU R g) (LocX R X g) ∧ Module.Projective (LocU R g) (LocX R X g) := by
  have : IsLocalization.Away g (LocU R g) := isLocalization_locU R hdepthR g
  have : IsNoetherianRing (LocU R g) :=
    IsLocalization.isNoetherianRing (Submonoid.powers g) (LocU R g) inferInstance
  have hUaff : IsAffineOpen (openU R g) := isAffineOpen_openU R hg
  have hXaff : IsAffineOpen (openX R X g) := isAffineOpen_openX R X hg
  have hfin : (algebraMap (LocU R g) (LocX R X g)).Finite := by
    have h1 : (X.obj.hom.app (openU R g)).hom.Finite := X.obj.hom.finite_app (openU R g) hUaff
    have heq : X.obj.hom.appLE (openU R g) (openX R X g) (openX_eq_preimage R X g).le =
        X.obj.hom.app (openU R g) ≫
          X.obj.left.presheaf.map (eqToHom (openX_eq_preimage R X g)).op := by
      rw [Scheme.Hom.app_eq_appLE, Subsingleton.elim (eqToHom (openX_eq_preimage R X g))
        (homOfLE (openX_eq_preimage R X g).le), Scheme.Hom.appLE_map]
    change (X.obj.hom.appLE (openU R g) (openX R X g) (openX_eq_preimage R X g).le).hom.Finite
    rw [heq, CommRingCat.hom_comp]
    exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso _).2) h1
  have het : (algebraMap (LocU R g) (LocX R X g)).Etale :=
    X.obj.hom.etale_appLE hUaff hXaff (openX_eq_preimage R X g).le
  have : Module.Finite (LocU R g) (LocX R X g) := RingHom.finite_algebraMap.mp hfin
  have : Module.Flat (LocU R g) (LocX R X g) :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Etale.iff_flat_and_formallyUnramified.mp het).1
  have : Module.FinitePresentation (LocU R g) (LocX R X g) :=
    Module.finitePresentation_of_finite _ _
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

/-- When `2 ≤ depth R`, `LocX R X g` is the base change of `Sec R X` along `R → LocU R g`. -/
lemma isBaseChange_locX [IsNoetherianRing R]
    (hdepthR : 2 ≤ depth (ModuleCat.of R R))
    (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : R) :
    IsBaseChange (LocU R g)
      (IsScalarTower.toAlgHom R (Sec R X) (LocX R X g)).toLinearMap := by
  have : IsLocalization.Away g (LocU R g) := isLocalization_locU R hdepthR g
  have : IsLocalization.Away (algebraMap R (Sec R X) g) (LocX R X g) :=
    isLocalization_locX R X g
  have hsub : Algebra.algebraMapSubmonoid (Sec R X) (Submonoid.powers g) =
      Submonoid.powers (algebraMap R (Sec R X) g) := Submonoid.map_powers _ _
  have : IsLocalization (Algebra.algebraMapSubmonoid (Sec R X) (Submonoid.powers g))
      (LocX R X g) := by
    rwa [hsub]
  exact (Algebra.isPushout_of_isLocalization (Submonoid.powers g) (LocU R g)
    (Sec R X) (LocX R X g)).symm.out

private lemma iSup_openU_eq_top {s : Finset R} (hs : Ideal.span (s : Set R) = maximalIdeal R) :
    ⨆ g : s, openU R g.1 = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  let p : PrimeSpectrum R := (puncturedSpectrum R).ι x
  obtain ⟨g, hgs, hgp⟩ : ∃ g ∈ s, g ∉ p.asIdeal := by
    by_contra! hall
    refine (mem_puncturedSpectrum_iff R p).mp x.2 (PrimeSpectrum.ext ?_)
    refine le_antisymm (le_maximalIdeal p.isPrime.ne_top) ?_
    change maximalIdeal R ≤ p.asIdeal
    rw [← hs, Ideal.span_le]
    exact hall
  refine ⟨⟨g, hgs⟩, ?_⟩
  rw [openU_eq_preimage, Scheme.Hom.mem_preimage, basicOpen_eq_of_affine]
  exact hgp

/-- Preimage of `openU A g` under a morphism of punctured spectra induced by `A → R`. -/
lemma preimage_openU_eq {A R : Type u} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] [Algebra A R]
    {r : (puncturedSpectrum R).toScheme ⟶ (puncturedSpectrum A).toScheme}
    (hr : r ≫ (puncturedSpectrum A).ι =
      (puncturedSpectrum R).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A R))) (g : A) :
    r ⁻¹ᵁ openU A g = openU R (algebraMap A R g) := by
  rw [openU, openU, Scheme.preimage_basicOpen_top, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, hr, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply (Scheme.ΓSpecIso (.of A)).inv, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- Preimage of `openX A X g` under the projection `X' ⟶ X` of a pullback cover. -/
lemma preimage_openX_eq {A R : Type u} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] [Algebra A R]
    {r : (puncturedSpectrum R).toScheme ⟶ (puncturedSpectrum A).toScheme}
    (hr : r ≫ (puncturedSpectrum A).ι =
      (puncturedSpectrum R).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)))
    {X : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    {X' : FiniteEtaleScheme (puncturedSpectrum R).toScheme}
    {pX : X'.obj.left ⟶ X.obj.left}
    (hpb : IsPullback pX X'.obj.hom X.obj.hom r) (g : A) :
    pX ⁻¹ᵁ openX A X g = openX R X' (algebraMap A R g) := by
  rw [openX_eq_preimage, openX_eq_preimage, ← Scheme.Hom.comp_preimage, hpb.w,
    Scheme.Hom.comp_preimage, preimage_openU_eq hr]

private lemma isPushout_openX {A R : Type u} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] [Algebra A R]
    {r : (puncturedSpectrum R).toScheme ⟶ (puncturedSpectrum A).toScheme}
    (hr : r ≫ (puncturedSpectrum A).ι =
      (puncturedSpectrum R).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)))
    {X : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    {X' : FiniteEtaleScheme (puncturedSpectrum R).toScheme}
    {pX : X'.obj.left ⟶ X.obj.left}
    (hpb : IsPullback pX X'.obj.hom X.obj.hom r) {g : A} (hg : g ∈ maximalIdeal A)
    (hg' : algebraMap A R g ∈ maximalIdeal R) :
    IsPushout
      (r.appLE (openU A g) (openU R (algebraMap A R g)) (preimage_openU_eq hr g).ge)
      (X.obj.hom.appLE (openU A g) (openX A X g) (openX_eq_preimage A X g).le)
      (X'.obj.hom.appLE (openU R (algebraMap A R g)) (openX R X' (algebraMap A R g))
        (openX_eq_preimage R X' (algebraMap A R g)).le)
      (pX.appLE (openX A X g) (openX R X' (algebraMap A R g)) (preimage_openX_eq hr hpb g).ge) := by
  let US := openU A g
  let UT := openU R (algebraMap A R g)
  let UX := openX A X g
  let UY := openX R X' (algebraMap A R g)
  have hUST : UT ≤ r ⁻¹ᵁ US := (preimage_openU_eq hr g).ge
  have hUSX : UX ≤ X.obj.hom ⁻¹ᵁ US := (openX_eq_preimage A X g).le
  have hUY : UY = pX ⁻¹ᵁ UX ⊓ X'.obj.hom ⁻¹ᵁ UT := by
    rw [preimage_openX_eq hr hpb g, ← openX_eq_preimage R X' (algebraMap A R g), inf_idem]
  have hpbRes := Scheme.Hom.isPullback_resLE hpb hUST hUSX hUY
  have : IsAffine US.toScheme := isAffineOpen_openU A hg
  have : IsAffine UT.toScheme := isAffineOpen_openU R hg'
  have : IsAffine UX.toScheme := isAffineOpen_openX A X hg
  have hpoTop := isPushout_appTop_of_isPullback hpbRes
  have hpo := hpoTop.of_iso US.topIso UX.topIso UT.topIso UY.topIso
    (arrowResLEAppIso X.obj.hom US UX hUSX).hom.w.symm
    (arrowResLEAppIso r US UT hUST).hom.w.symm
    (arrowResLEAppIso pX UX UY (by simp [hUY])).hom.w.symm
    (arrowResLEAppIso X'.obj.hom UT UY (by simp [hUY])).hom.w.symm
  exact hpo.flip

/-- The image of an element of `maximalIdeal A` under a surjective local ring map `A → R` lies in
`maximalIdeal R`. -/
lemma mem_maximalIdeal_of_surjective {A R : Type*} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] [Algebra A R] (hsurj : Function.Surjective (algebraMap A R))
    {g : A} (hg : g ∈ maximalIdeal A) : algebraMap A R g ∈ maximalIdeal R :=
  IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A R) hsurj ▸ Ideal.mem_map_of_mem _ hg

/-- The basic opens `openU R (algebraMap A R g)` for generators `g` of `maximalIdeal A` cover
`puncturedSpectrum R` when `A → R` is surjective. -/
lemma iSup_openU_image_eq_top {A R : Type u} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] [Algebra A R] (hsurj : Function.Surjective (algebraMap A R))
    {s : Finset A} (hs : Ideal.span (s : Set A) = maximalIdeal A) :
    ⨆ g : s, openU R (algebraMap A R g.1) = ⊤ := by
  classical
  have hsR : Ideal.span ((s.image (algebraMap A R) : Finset R) : Set R) = maximalIdeal R := by
    rw [Finset.coe_image, ← Ideal.map_span, hs,
      IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A R) hsurj]
  refine eq_top_iff.mpr fun x _ ↦ ?_
  have hx : x ∈ ⨆ g : s.image (algebraMap A R), openU R g.1 := by
    rw [iSup_openU_eq_top R hsR]
    trivial
  obtain ⟨⟨y, hy⟩, hxy⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨g, hgs, rfl⟩ := Finset.mem_image.mp hy
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hgs⟩, hxy⟩

/-- The basic opens `openX R X (algebraMap A R g)` for generators `g` of `maximalIdeal A` cover `X`
when `A → R` is surjective. -/
lemma iSup_openX_image_eq_top {A R : Type u} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] [Algebra A R] (hsurj : Function.Surjective (algebraMap A R))
    {s : Finset A} (hs : Ideal.span (s : Set A) = maximalIdeal A)
    (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) :
    ⨆ g : s, openX R X (algebraMap A R g.1) = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  have hx : X.obj.hom x ∈ ⨆ g : s, openU R (algebraMap A R g.1) := by
    rw [iSup_openU_image_eq_top hsurj hs]
    trivial
  obtain ⟨g, hg⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨g, by rwa [openX_eq_preimage]⟩

end BasicOpen

/-! ### Base change of local section rings along a pullback of covers -/

section LocalAlgebra

variable {A R : Type u} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [Algebra A R]

/-- The `A`-algebra structure on `LocU R (algebraMap A R g)` obtained by restriction along `A → R`.
-/
@[expose, instance_reducible]
def localAlgAT (A R : Type u) [CommRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] (g : A) : Algebra A (LocU R (algebraMap A R g)) :=
  ((algebraMap R (LocU R (algebraMap A R g))).comp (algebraMap A R)).toAlgebra

/-- The `A`-algebra structure on `LocX R X' (algebraMap A R g)` obtained by restriction along
`A → R`. -/
@[expose, instance_reducible]
def localAlgAX (A R : Type u) [CommRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] (X' : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : A) :
    Algebra A (LocX R X' (algebraMap A R g)) :=
  ((algebraMap R (LocX R X' (algebraMap A R g))).comp (algebraMap A R)).toAlgebra

/-- Scalar tower compatibility for `A → LocU R (algebraMap A R g) → LocX R X' (algebraMap A R g)`.
-/
lemma localIsScalarTower_AX (A R : Type u) [CommRing A] [CommRing R]
    [IsLocalRing R] [Algebra A R] (X' : FiniteEtaleScheme (puncturedSpectrum R).toScheme) (g : A) :
    letI := localAlgAT A R g
    letI := localAlgAX A R X' g
    IsScalarTower A (LocU R (algebraMap A R g)) (LocX R X' (algebraMap A R g)) := by
  let := localAlgAT A R g
  let := localAlgAX A R X' g
  exact IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap R (LocX R X' (algebraMap A R g)) (algebraMap A R a) =
      algebraMap (LocU R (algebraMap A R g)) (LocX R X' (algebraMap A R g))
        (algebraMap R (LocU R (algebraMap A R g)) (algebraMap A R a))
    rw [← IsScalarTower.algebraMap_apply R (LocU R (algebraMap A R g))
      (LocX R X' (algebraMap A R g))]

/-- The `A`-linear pullback map `Sec A X →ₗ[A] LocX R X' (algebraMap A R g)` for a pullback cover
`X'` of `X`. -/
@[expose]
def localMapAX {r : (puncturedSpectrum R).toScheme ⟶ (puncturedSpectrum A).toScheme}
    (hr : r ≫ (puncturedSpectrum A).ι =
      (puncturedSpectrum R).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)))
    {X : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    {X' : FiniteEtaleScheme (puncturedSpectrum R).toScheme}
    {pX : X'.obj.left ⟶ X.obj.left} (hpb : IsPullback pX X'.obj.hom X.obj.hom r) (g : A) :
    letI := localAlgAX A R X' g
    Sec A X →ₗ[A] LocX R X' (algebraMap A R g) :=
  letI := localAlgAX A R X' g
  { toFun := fun x ↦ algebraMap (Sec R X') (LocX R X' (algebraMap A R g)) (secAppTop pX x)
    map_add' := fun x y ↦ by rw [map_add, map_add]
    map_smul' := fun a x ↦ by
      have hp : secAppTop pX (algebraMap A (Sec A X) a) =
          algebraMap R (Sec R X') (algebraMap A R a) := by
        have hcomp : ((Scheme.ΓSpecIso (.of A)).inv ≫
            (X.obj.hom ≫ (puncturedSpectrum A).ι).appTop) ≫ pX.appTop =
            CommRingCat.ofHom (algebraMap A R) ≫ (Scheme.ΓSpecIso (.of R)).inv ≫
              (X'.obj.hom ≫ (puncturedSpectrum R).ι).appTop := by
          rw [Category.assoc, ← Scheme.Hom.comp_appTop, ← Category.assoc, hpb.w, Category.assoc, hr,
            ← Category.assoc, Scheme.Hom.comp_appTop, ← Category.assoc,
            ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
        exact congrArg (fun f ↦ f a) hcomp
      change algebraMap (Sec R X') (LocX R X' (algebraMap A R g))
        (secAppTop pX (algebraMap A (Sec A X) a * x)) =
        algebraMap R (LocX R X' (algebraMap A R g)) (algebraMap A R a) *
          algebraMap (Sec R X') (LocX R X' (algebraMap A R g)) (secAppTop pX x)
      rw [map_mul, map_mul, hp, ← IsScalarTower.algebraMap_apply R (Sec R X')
        (LocX R X' (algebraMap A R g))] }

/-- Base-change property of `LocX A X g → LocX R X' (algebraMap A R g)` along
`LocU A g → LocU R (algebraMap A R g)`, together with compatibility with `localMapAX`. -/
lemma isBaseChange_locX_step
    {r : (puncturedSpectrum R).toScheme ⟶ (puncturedSpectrum A).toScheme}
    (hr : r ≫ (puncturedSpectrum A).ι =
      (puncturedSpectrum R).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)))
    {X : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    {X' : FiniteEtaleScheme (puncturedSpectrum R).toScheme}
    {pX : X'.obj.left ⟶ X.obj.left} (hpb : IsPullback pX X'.obj.hom X.obj.hom r)
    {g : A} (hg : g ∈ maximalIdeal A) (hg' : algebraMap A R g ∈ maximalIdeal R) :
    letI := localAlgAT A R g
    letI := localAlgAX A R X' g
    letI : Algebra (LocU A g) (LocU R (algebraMap A R g)) :=
      (locUAppLE r (preimage_openU_eq hr g).ge).toAlgebra
    letI : Algebra (LocX A X g) (LocX R X' (algebraMap A R g)) :=
      (locXAppLE pX (preimage_openX_eq hr hpb g).ge).toAlgebra
    letI : Algebra (LocU A g) (LocX R X' (algebraMap A R g)) :=
      ((algebraMap (LocU R (algebraMap A R g)) (LocX R X' (algebraMap A R g))).comp
        (algebraMap (LocU A g) (LocU R (algebraMap A R g)))).toAlgebra
    ∃ (_ : IsScalarTower A (LocU A g) (LocU R (algebraMap A R g)))
      (_ : IsScalarTower (LocU A g) (LocU R (algebraMap A R g)) (LocX R X' (algebraMap A R g)))
      (_ : IsScalarTower A (LocU A g) (LocX R X' (algebraMap A R g)))
      (_ : IsScalarTower (LocU A g) (LocX A X g) (LocX R X' (algebraMap A R g))),
      IsBaseChange (LocU R (algebraMap A R g))
        (IsScalarTower.toAlgHom (LocU A g) (LocX A X g)
          (LocX R X' (algebraMap A R g))).toLinearMap ∧
      (IsScalarTower.toAlgHom (LocU A g) (LocX A X g)
          (LocX R X' (algebraMap A R g))).toLinearMap.restrictScalars A ∘ₗ
        (IsScalarTower.toAlgHom A (Sec A X) (LocX A X g)).toLinearMap =
        localMapAX hr hpb g := by
  let Q := LocU A g
  let T := LocU R (algebraMap A R g)
  let XQ := LocX A X g
  let XT := LocX R X' (algebraMap A R g)
  let := localAlgAT A R g
  let := localAlgAX A R X' g
  have := localIsScalarTower_AX A R X' g
  let : Algebra Q T := (locUAppLE r (preimage_openU_eq hr g).ge).toAlgebra
  let : Algebra XQ XT := (locXAppLE pX (preimage_openX_eq hr hpb g).ge).toAlgebra
  let : Algebra Q XT := ((algebraMap T XT).comp (algebraMap Q T)).toAlgebra
  have hAQT : IsScalarTower A Q T := IsScalarTower.of_algebraMap_eq fun a ↦
    (locUAppLE_algebraMap hr (preimage_openU_eq hr g).ge a).symm
  have hQTXT : IsScalarTower Q T XT := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hAQXT : IsScalarTower A Q XT := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap A XT a = algebraMap T XT (algebraMap Q T (algebraMap A Q a))
    rw [← IsScalarTower.algebraMap_apply A Q T, ← IsScalarTower.algebraMap_apply A T XT]
  have hpoCat := isPushout_openX hr hpb hg hg'
  have hQXXT : IsScalarTower Q XQ XT := IsScalarTower.of_algebraMap_eq fun q ↦
    congrArg (fun f ↦ f q) hpoCat.w
  have hpoAlg : Algebra.IsPushout Q T XQ XT :=
    (CommRingCat.isPushout_iff_isPushout (R := Q) (S := XQ) (R' := T) (S' := XT)).mp hpoCat
  refine ⟨hAQT, hQTXT, hAQXT, hQXXT, hpoAlg.out, LinearMap.ext fun x ↦ ?_⟩
  exact locXAppLE_algebraMap pX (preimage_openX_eq hr hpb g).ge x

/-- `LocX R X' (algebraMap A R g)` is the base change of `Sec A X` along
`A → LocU R (algebraMap A R g)`. -/
lemma isBaseChange_localMapAX [IsNoetherianRing A]
    (hdepthA : 2 ≤ depth (ModuleCat.of A A))
    {r : (puncturedSpectrum R).toScheme ⟶ (puncturedSpectrum A).toScheme}
    (hr : r ≫ (puncturedSpectrum A).ι =
      (puncturedSpectrum R).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)))
    {X : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    {X' : FiniteEtaleScheme (puncturedSpectrum R).toScheme}
    {pX : X'.obj.left ⟶ X.obj.left} (hpb : IsPullback pX X'.obj.hom X.obj.hom r)
    {g : A} (hg : g ∈ maximalIdeal A) (hg' : algebraMap A R g ∈ maximalIdeal R) :
    letI := localAlgAT A R g
    letI := localAlgAX A R X' g
    haveI := localIsScalarTower_AX A R X' g
    IsBaseChange (LocU R (algebraMap A R g)) (localMapAX hr hpb g) := by
  let := localAlgAT A R g
  let := localAlgAX A R X' g
  have := localIsScalarTower_AX A R X' g
  let : Algebra (LocU A g) (LocU R (algebraMap A R g)) :=
    (locUAppLE r (preimage_openU_eq hr g).ge).toAlgebra
  let : Algebra (LocX A X g) (LocX R X' (algebraMap A R g)) :=
    (locXAppLE pX (preimage_openX_eq hr hpb g).ge).toAlgebra
  let : Algebra (LocU A g) (LocX R X' (algebraMap A R g)) :=
    ((algebraMap (LocU R (algebraMap A R g)) (LocX R X' (algebraMap A R g))).comp
      (algebraMap (LocU A g) (LocU R (algebraMap A R g)))).toAlgebra
  obtain ⟨_, _, _, _, hQT, heq⟩ := isBaseChange_locX_step hr hpb hg hg'
  have hcomp := (isBaseChange_locX A hdepthA X g).comp hQT
  rwa [heq] at hcomp

end LocalAlgebra

end PuncturedBasicOpen

end TauCeti.IsLocalRing
