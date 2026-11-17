/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import TauCeti.AlgebraicGeometry.FiniteEtale.Hypersurface.BasicOpen
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Sections
import TauCeti.LinearAlgebra.TensorProduct.Hom

/-!
# Linear-map coordinates for pullbacks of finite étale covers over a punctured spectrum

Let `(A, 𝔪)` be a Noetherian local ring of depth at least two, `U` its punctured spectrum, and
`V, W` finite étale covers of `U` whose global-section rings `B = Γ(V, 𝒪)` and `C = Γ(W, 𝒪)` are
finite `A`-modules. Given a finite presentation
`(Fin s → A) —φ→ (Fin r → A) —π→ Dual A (C →ₗ[A] B) → 0`, this file constructs, for every
surjective homomorphism `A → R` of Noetherian local rings with `2 ≤ depth R` and pullback covers
`V', W'` over the punctured spectrum `U_R` (`TauCeti.IsLocalRing.CoverPullback`), a canonical
`R`-linear coordinate map
`CoverPullback.coords : (Γ(W', 𝒪) →ₗ[R] Γ(V', 𝒪)) →ₗ[R] (Fin r → R)`.

Over every basic open `D(g) ⊆ U` (`g ∈ 𝔪`), `A_g` is flat over `A` and `B_g, C_g` are finite étale,
hence finite projective, over `A_g` (`TauCeti.IsLocalRing.PuncturedBasicOpen`). Applying
`IsBaseChange.bijective_homDualEval_of_flat_projective` and `IsBaseChange.homCoords_exact` over each
`D(g)` and gluing over a finite generating set of `𝔪` identifies `Γ(W', 𝒪) →ₗ[R] Γ(V', 𝒪)` with the
kernel of the transposed linear system of `φ` with coefficients in `R`
(`CoverPullback.coords_exact`), naturally in morphisms of base rings `τ : R₁ →ₐ[A] R₂`
(`CoverPullbackHom.coords_map` and `CoverPullbackHom.compat_of_coords_eq`).

This is the linear-algebraic and Zariski-gluing core of Stacks, Lemma 58.19.7 (0BLJ).

## Main definitions

* `TauCeti.IsLocalRing.CoverPullback`: pullback data for a pair of finite étale covers `V, W` along
  a surjective local ring map `A → R` with `2 ≤ depth R`.
* `TauCeti.IsLocalRing.CoverPullbackHom`: a morphism of `CoverPullback`s over `τ : R₁ →ₐ[A] R₂`.
* `TauCeti.IsLocalRing.CoverPullback.coords`: the global coordinate map
  `(Γ(W', 𝒪) →ₗ[R] Γ(V', 𝒪)) →ₗ[R] (Fin r → R)`.

## Main results

* `TauCeti.IsLocalRing.CoverPullback.coords_exact`: `CoverPullback.coords` is injective and its
  image is cut out by the transposed relations of `φ` over `R`.
* `TauCeti.IsLocalRing.CoverPullbackHom.coords_map`: compatible linear maps have `τ`-compatible
  coordinates.
* `TauCeti.IsLocalRing.CoverPullbackHom.compat_of_coords_eq`: conversely, `τ`-compatible
  coordinates force compatibility on sections pulled back from `W`.
* `TauCeti.IsLocalRing.CoverPullback.linearMap_eq_of_eq_on_base`: an `R`-linear map
  `Γ(W', 𝒪) →ₗ[R] Γ(V', 𝒪)` is determined by its values on sections pulled back from `W`.

## References

* [The Stacks Project, Lemma 58.19.7](https://stacks.math.columbia.edu/tag/0BLJ).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open scoped Pointwise

universe u

namespace TauCeti.IsLocalRing

open PuncturedBasicOpen

/-- Pullback data for a pair of finite étale covers `V, W` over `puncturedSpectrum A` along a
surjective homomorphism `A → R` of Noetherian local rings with `2 ≤ depth R`. -/
structure CoverPullback {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme) (R : Type u)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R] where
  /-- The base ring map `A → R` is surjective. -/
  surj : Function.Surjective (algebraMap A R)
  /-- The target local ring `R` has depth at least two. -/
  depth_ge : 2 ≤ depth (ModuleCat.of R R)
  /-- The induced morphism on punctured spectra `U_R ⟶ U_A`. -/
  base : (puncturedSpectrum R).toScheme ⟶ (puncturedSpectrum A).toScheme
  /-- Compatibility of `base` with `Spec R ⟶ Spec A`. -/
  base_comp_ι : base ≫ (puncturedSpectrum A).ι =
    (puncturedSpectrum R).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A R))
  /-- The pullback of `V` to `U_R`. -/
  V' : FiniteEtaleScheme (puncturedSpectrum R).toScheme
  /-- The pullback of `W` to `U_R`. -/
  W' : FiniteEtaleScheme (puncturedSpectrum R).toScheme
  /-- The projection `V' ⟶ V`. -/
  pV : V'.obj.left ⟶ V.obj.left
  /-- The projection `W' ⟶ W`. -/
  pW : W'.obj.left ⟶ W.obj.left
  /-- `V'` is the pullback of `V` along `base`. -/
  isPullback_V : IsPullback pV V'.obj.hom V.obj.hom base
  /-- `W'` is the pullback of `W` along `base`. -/
  isPullback_W : IsPullback pW W'.obj.hom W.obj.hom base

/-- The identity `CoverPullback` at `R = A`. -/
@[expose]
def CoverPullback.id {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepthA : 2 ≤ depth (ModuleCat.of A A))
    (V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme) : CoverPullback V W A where
  surj := Function.surjective_id
  depth_ge := hdepthA
  base := 𝟙 _
  base_comp_ι := by simp
  V' := V
  W' := W
  pV := 𝟙 _
  pW := 𝟙 _
  isPullback_V := IsPullback.of_horiz_isIso ⟨by simp⟩
  isPullback_W := IsPullback.of_horiz_isIso ⟨by simp⟩

/-- A morphism between two `CoverPullback`s compatible with an `A`-algebra map `τ : R₁ →ₐ[A] R₂`. -/
structure CoverPullbackHom {A R₁ R₂ : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [Algebra A R₁]
    [CommRing R₂] [IsLocalRing R₂] [IsNoetherianRing R₂] [Algebra A R₂]
    {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    (P₁ : CoverPullback V W R₁) (P₂ : CoverPullback V W R₂) (τ : R₁ →ₐ[A] R₂) where
  /-- The morphism on punctured spectra `U_{R₂} ⟶ U_{R₁}`. -/
  tU : (puncturedSpectrum R₂).toScheme ⟶ (puncturedSpectrum R₁).toScheme
  /-- Compatibility of `tU` with the base maps to `U_A`. -/
  tU_comp_base : tU ≫ P₁.base = P₂.base
  /-- Compatibility of `tU` with `Spec τ`. -/
  tU_comp_ι : tU ≫ (puncturedSpectrum R₁).ι =
    (puncturedSpectrum R₂).ι ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)
  /-- The transition morphism `P₂.V' ⟶ P₁.V'`. -/
  tV : P₂.V'.obj.left ⟶ P₁.V'.obj.left
  /-- Compatibility of `tV` with the structure maps to punctured spectra. -/
  tV_comp_hom : tV ≫ P₁.V'.obj.hom = P₂.V'.obj.hom ≫ tU
  /-- Compatibility of `tV` with the projections to `V`. -/
  tV_comp_pV : tV ≫ P₁.pV = P₂.pV
  /-- The transition morphism `P₂.W' ⟶ P₁.W'`. -/
  tW : P₂.W'.obj.left ⟶ P₁.W'.obj.left
  /-- Compatibility of `tW` with the structure maps to punctured spectra. -/
  tW_comp_hom : tW ≫ P₁.W'.obj.hom = P₂.W'.obj.hom ≫ tU
  /-- Compatibility of `tW` with the projections to `W`. -/
  tW_comp_pW : tW ≫ P₁.pW = P₂.pW

/-- The canonical morphism from `CoverPullback.id` to any `CoverPullback V W R`. -/
@[expose]
def CoverPullbackHom.fromId {A R : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R]
    (hdepthA : 2 ≤ depth (ModuleCat.of A A))
    {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    (P : CoverPullback V W R) :
    CoverPullbackHom (CoverPullback.id hdepthA V W) P (Algebra.ofId A R) where
  tU := P.base
  tU_comp_base := Category.comp_id _
  tU_comp_ι := P.base_comp_ι
  tV := P.pV
  tV_comp_hom := P.isPullback_V.w
  tV_comp_pV := Category.comp_id _
  tW := P.pW
  tW_comp_hom := P.isPullback_W.w
  tW_comp_pW := Category.comp_id _

/-! ### Local coordinates on basic opens over a cover pullback -/

section LocalCoords

private lemma CoverPullbackHom.preU {A R₁ R₂ : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [Algebra A R₁]
    [CommRing R₂] [IsLocalRing R₂] [IsNoetherianRing R₂] [Algebra A R₂]
    {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    {P₁ : CoverPullback V W R₁} {P₂ : CoverPullback V W R₂} {τ : R₁ →ₐ[A] R₂}
    (F : CoverPullbackHom P₁ P₂ τ) (g : A) :
    openU R₂ (algebraMap A R₂ g) ≤ F.tU ⁻¹ᵁ openU R₁ (algebraMap A R₁ g) := by
  rw [← preimage_openU_eq P₁.base_comp_ι g, ← Scheme.Hom.comp_preimage, F.tU_comp_base,
    preimage_openU_eq P₂.base_comp_ι g]

private lemma CoverPullbackHom.preV {A R₁ R₂ : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [Algebra A R₁]
    [CommRing R₂] [IsLocalRing R₂] [IsNoetherianRing R₂] [Algebra A R₂]
    {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    {P₁ : CoverPullback V W R₁} {P₂ : CoverPullback V W R₂} {τ : R₁ →ₐ[A] R₂}
    (F : CoverPullbackHom P₁ P₂ τ) (g : A) :
    openX R₂ P₂.V' (algebraMap A R₂ g) ≤ F.tV ⁻¹ᵁ openX R₁ P₁.V' (algebraMap A R₁ g) := by
  rw [← preimage_openX_eq P₁.base_comp_ι P₁.isPullback_V g, ← Scheme.Hom.comp_preimage,
    F.tV_comp_pV, preimage_openX_eq P₂.base_comp_ι P₂.isPullback_V g]

section WithCoverPullback

variable {A R : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R]
  (hdepthA : 2 ≤ depth (ModuleCat.of A A))
  {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme}

private lemma local_isBaseChange_and_bijective_homDualEval
    [Module.Finite A (Sec A V)] [Module.Finite A (Sec A W)]
    (P : CoverPullback V W R) {g : A} (hg : g ∈ maximalIdeal A) :
    letI := localAlgAT A R g
    letI := localAlgAX A R P.V' g
    letI := localAlgAX A R P.W' g
    haveI := localIsScalarTower_AX A R P.V' g
    haveI := localIsScalarTower_AX A R P.W' g
    have hcT : IsBaseChange (LocU R (algebraMap A R g))
        (localMapAX P.base_comp_ι P.isPullback_W g) :=
      isBaseChange_localMapAX hdepthA P.base_comp_ι P.isPullback_W hg
        (mem_maximalIdeal_of_surjective P.surj hg)
    ∃ heT : IsBaseChange (LocU R (algebraMap A R g))
        (IsBaseChange.linearMapLeftRightHom hcT (localMapAX P.base_comp_ι P.isPullback_V g)),
      Function.Bijective
        (IsBaseChange.homDualEval hcT (localMapAX P.base_comp_ι P.isPullback_V g) heT) := by
  let Q := LocU A g
  let T := LocU R (algebraMap A R g)
  let CQ := LocX A W g
  let BQ := LocX A V g
  let CT := LocX R P.W' (algebraMap A R g)
  let BT := LocX R P.V' (algebraMap A R g)
  let := localAlgAT A R g
  let := localAlgAX A R P.V' g
  let := localAlgAX A R P.W' g
  have := localIsScalarTower_AX A R P.V' g
  have := localIsScalarTower_AX A R P.W' g
  have hg' : algebraMap A R g ∈ maximalIdeal R := mem_maximalIdeal_of_surjective P.surj hg
  let : Algebra Q T := (locUAppLE P.base (preimage_openU_eq P.base_comp_ι g).ge).toAlgebra
  let : Algebra CQ CT :=
    (locXAppLE P.pW (preimage_openX_eq P.base_comp_ι P.isPullback_W g).ge).toAlgebra
  let : Algebra BQ BT :=
    (locXAppLE P.pV (preimage_openX_eq P.base_comp_ι P.isPullback_V g).ge).toAlgebra
  let : Algebra Q CT := ((algebraMap T CT).comp (algebraMap Q T)).toAlgebra
  let : Algebra Q BT := ((algebraMap T BT).comp (algebraMap Q T)).toAlgebra
  obtain ⟨_, _, _, _, hcQT, hcEq⟩ := isBaseChange_locX_step P.base_comp_ι P.isPullback_W hg hg'
  obtain ⟨_, _, _, _, hbQT, hbEq⟩ := isBaseChange_locX_step P.base_comp_ι P.isPullback_V hg hg'
  have : IsLocalization.Away g Q := isLocalization_locU A hdepthA g
  have : Module.Flat A Q := IsLocalization.flat Q (Submonoid.powers g)
  have ⟨_, _⟩ := finite_projective_locX A hdepthA W hg
  have ⟨_, _⟩ := finite_projective_locX A hdepthA V hg
  have : Module.FinitePresentation A (Sec A W) := Module.finitePresentation_of_finite A _
  have : Module.FinitePresentation A (Sec A W →ₗ[A] Sec A V) :=
    Module.finitePresentation_of_finite A _
  have hcQ := isBaseChange_locX A hdepthA W g
  have hbQ := isBaseChange_locX A hdepthA V g
  have heT0 := IsBaseChange.linearMapLeftRight_of_flat_projective hcQ hbQ hcQT hbQT
  have hbij0 := IsBaseChange.bijective_homDualEval_of_flat_projective hcQ hbQ hcQT hbQT heT0
  have htrans : ∀ {c₁ c₂ : Sec A W →ₗ[A] CT} (_ : c₁ = c₂)
      {b₁ b₂ : Sec A V →ₗ[A] BT} (_ : b₁ = b₂)
      (hc₁ : IsBaseChange T c₁) (hc₂ : IsBaseChange T c₂)
      (he₁ : IsBaseChange T (IsBaseChange.linearMapLeftRightHom hc₁ b₁)),
      Function.Bijective (IsBaseChange.homDualEval hc₁ b₁ he₁) →
      ∃ he₂ : IsBaseChange T (IsBaseChange.linearMapLeftRightHom hc₂ b₂),
        Function.Bijective (IsBaseChange.homDualEval hc₂ b₂ he₂) := by
    rintro c _ rfl b _ rfl hc _ he h
    exact ⟨he, h⟩
  exact htrans hcEq hbEq (hcQ.comp hcQT) _ heT0 hbij0

private def localCoords [Module.Finite A (Sec A V)] [Module.Finite A (Sec A W)]
    (P : CoverPullback V W R) {r : ℕ}
    (π : (Fin r → A) →ₗ[A] Module.Dual A (Sec A W →ₗ[A] Sec A V))
    {g : A} (hg : g ∈ maximalIdeal A) :
    (LocX R P.W' (algebraMap A R g) →ₗ[LocU R (algebraMap A R g)]
      LocX R P.V' (algebraMap A R g)) →ₗ[LocU R (algebraMap A R g)]
      (Fin r → LocU R (algebraMap A R g)) :=
  letI := localAlgAT A R g
  letI := localAlgAX A R P.V' g
  letI := localAlgAX A R P.W' g
  haveI := localIsScalarTower_AX A R P.V' g
  haveI := localIsScalarTower_AX A R P.W' g
  let hcT := isBaseChange_localMapAX hdepthA P.base_comp_ι P.isPullback_W hg
    (mem_maximalIdeal_of_surjective P.surj hg)
  let heT := (local_isBaseChange_and_bijective_homDualEval hdepthA P hg).choose
  IsBaseChange.homCoords π hcT (localMapAX P.base_comp_ι P.isPullback_V g) heT

include hdepthA in
private lemma localCoords_eq_of_eq_on_secA (P : CoverPullback V W R) {g : A}
    (hg : g ∈ maximalIdeal A)
    {u₁ u₂ : LocX R P.W' (algebraMap A R g) →ₗ[LocU R (algebraMap A R g)]
      LocX R P.V' (algebraMap A R g)}
    (h : ∀ c : Sec A W,
      u₁ (algebraMap (Sec R P.W') (LocX R P.W' (algebraMap A R g)) (secAppTop P.pW c)) =
      u₂ (algebraMap (Sec R P.W') (LocX R P.W' (algebraMap A R g)) (secAppTop P.pW c))) :
    u₁ = u₂ := by
  let := localAlgAT A R g
  let := localAlgAX A R P.W' g
  have := localIsScalarTower_AX A R P.W' g
  exact (isBaseChange_localMapAX hdepthA P.base_comp_ι P.isPullback_W hg
    (mem_maximalIdeal_of_surjective P.surj hg)).algHom_ext u₁ u₂ h

private lemma localCoords_exact [Module.Finite A (Sec A V)] [Module.Finite A (Sec A W)]
    (P : CoverPullback V W R) {r s : ℕ}
    {π : (Fin r → A) →ₗ[A] Module.Dual A (Sec A W →ₗ[A] Sec A V)}
    {φ : (Fin s → A) →ₗ[A] (Fin r → A)}
    (hπ : Function.Surjective π) (hφπ : Function.Exact φ π)
    {g : A} (hg : g ∈ maximalIdeal A) :
    Function.Injective (localCoords hdepthA P π hg) ∧
      ∀ v : Fin r → LocU R (algebraMap A R g),
        (∃ u, localCoords hdepthA P π hg u = v) ↔
          ∀ j : Fin s,
            ∑ i : Fin r,
              algebraMap R (LocU R (algebraMap A R g)) (algebraMap A R (φ (Pi.single j 1) i)) *
                v i = 0 := by
  let := localAlgAT A R g
  let := localAlgAX A R P.V' g
  let := localAlgAX A R P.W' g
  have := localIsScalarTower_AX A R P.V' g
  have := localIsScalarTower_AX A R P.W' g
  have hcT := isBaseChange_localMapAX hdepthA P.base_comp_ι P.isPullback_W hg
    (mem_maximalIdeal_of_surjective P.surj hg)
  have hspec := local_isBaseChange_and_bijective_homDualEval hdepthA P hg
  exact IsBaseChange.homCoords_exact hπ hφπ hcT (localMapAX P.base_comp_ι P.isPullback_V g)
    hspec.choose hspec.choose_spec

private lemma localCoords_res_le [Module.Finite A (Sec A V)] [Module.Finite A (Sec A W)]
    (P : CoverPullback V W R) {r : ℕ}
    (π : (Fin r → A) →ₗ[A] Module.Dual A (Sec A W →ₗ[A] Sec A V))
    {g h : A} (hg : g ∈ maximalIdeal A) (hh : h ∈ maximalIdeal A)
    (hle : openU R (algebraMap A R h) ≤ openU R (algebraMap A R g))
    (u : LocX R P.W' (algebraMap A R g) →ₗ[LocU R (algebraMap A R g)]
      LocX R P.V' (algebraMap A R g)) :
    ∃ u' : LocX R P.W' (algebraMap A R h) →ₗ[LocU R (algebraMap A R h)]
        LocX R P.V' (algebraMap A R h),
      (∀ y : LocX R P.W' (algebraMap A R g),
        u' (locXRes (openX_mono P.W' hle) y) = locXRes (openX_mono P.V' hle) (u y)) ∧
      ∀ i : Fin r,
        localCoords hdepthA P π hh u' i = locURes hle (localCoords hdepthA P π hg u i) := by
  let := localAlgAT A R g
  let := localAlgAT A R h
  let := localAlgAX A R P.V' g
  let := localAlgAX A R P.W' g
  let := localAlgAX A R P.V' h
  let := localAlgAX A R P.W' h
  have := localIsScalarTower_AX A R P.V' g
  have := localIsScalarTower_AX A R P.W' g
  have := localIsScalarTower_AX A R P.V' h
  have := localIsScalarTower_AX A R P.W' h
  have hcT := isBaseChange_localMapAX hdepthA P.base_comp_ι P.isPullback_W hg
    (mem_maximalIdeal_of_surjective P.surj hg)
  have hcT' := isBaseChange_localMapAX hdepthA P.base_comp_ι P.isPullback_W hh
    (mem_maximalIdeal_of_surjective P.surj hh)
  have hspec := local_isBaseChange_and_bijective_homDualEval hdepthA P hg
  have hspec' := local_isBaseChange_and_bijective_homDualEval hdepthA P hh
  let τ : LocU R (algebraMap A R g) →ₐ[A] LocU R (algebraMap A R h) :=
    { toRingHom := locURes hle
      commutes' := fun a ↦ locURes_algebraMap hle (algebraMap A R a) }
  obtain ⟨u', hu'm, hdual⟩ := IsBaseChange.homDualEval_natural
    hcT (localMapAX P.base_comp_ι P.isPullback_V g) hspec.choose
    hcT' (localMapAX P.base_comp_ι P.isPullback_V h) hspec'.choose
    τ (locXRes (openX_mono P.V' hle)) (fun _ _ ↦ map_add _ _ _)
    (fun t x ↦ locXRes_smul P.V' hle t x)
    (fun y ↦ locXRes_algebraMap (openX_mono P.V' hle) (secAppTop P.pV y)) u
  refine ⟨u', fun y ↦ ?_, fun i ↦ ?_⟩
  · induction y using hcT.inductionOn with
    | tmul m =>
      change u' (locXRes (openX_mono P.W' hle) (algebraMap _ _ (secAppTop P.pW m))) = _
      rw [locXRes_algebraMap (openX_mono P.W' hle)]
      exact hu'm m
    | smul t y hy =>
      rw [locXRes_smul P.W' hle, map_smul, map_smul, locXRes_smul P.V' hle, hy]
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, map_add, h₁, h₂]
  · rw [localCoords, localCoords, IsBaseChange.homCoords_apply, IsBaseChange.homCoords_apply]
    exact hdual (π (Pi.single i 1))

end WithCoverPullback

private lemma localCoords_hom {A R₁ R₂ : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [Algebra A R₁]
    [CommRing R₂] [IsLocalRing R₂] [IsNoetherianRing R₂] [Algebra A R₂]
    (hdepthA : 2 ≤ depth (ModuleCat.of A A))
    {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    [Module.Finite A (Sec A V)] [Module.Finite A (Sec A W)]
    {P₁ : CoverPullback V W R₁} {P₂ : CoverPullback V W R₂} {τ : R₁ →ₐ[A] R₂}
    (F : CoverPullbackHom P₁ P₂ τ) {r : ℕ}
    (π : (Fin r → A) →ₗ[A] Module.Dual A (Sec A W →ₗ[A] Sec A V))
    {g : A} (hg : g ∈ maximalIdeal A)
    (u₁ : LocX R₁ P₁.W' (algebraMap A R₁ g) →ₗ[LocU R₁ (algebraMap A R₁ g)]
      LocX R₁ P₁.V' (algebraMap A R₁ g)) :
    ∃ u₂ : LocX R₂ P₂.W' (algebraMap A R₂ g) →ₗ[LocU R₂ (algebraMap A R₂ g)]
        LocX R₂ P₂.V' (algebraMap A R₂ g),
      (∀ c : Sec A W,
        u₂ (algebraMap (Sec R₂ P₂.W') (LocX R₂ P₂.W' (algebraMap A R₂ g)) (secAppTop P₂.pW c)) =
        locXAppLE F.tV (F.preV g) (u₁ (algebraMap (Sec R₁ P₁.W')
          (LocX R₁ P₁.W' (algebraMap A R₁ g)) (secAppTop P₁.pW c)))) ∧
      ∀ i : Fin r,
        localCoords hdepthA P₂ π hg u₂ i =
          locUAppLE F.tU (F.preU g) (localCoords hdepthA P₁ π hg u₁ i) := by
  let := localAlgAT A R₁ g
  let := localAlgAT A R₂ g
  let := localAlgAX A R₁ P₁.V' g
  let := localAlgAX A R₁ P₁.W' g
  let := localAlgAX A R₂ P₂.V' g
  let := localAlgAX A R₂ P₂.W' g
  have := localIsScalarTower_AX A R₁ P₁.V' g
  have := localIsScalarTower_AX A R₁ P₁.W' g
  have := localIsScalarTower_AX A R₂ P₂.V' g
  have := localIsScalarTower_AX A R₂ P₂.W' g
  have hcT₁ := isBaseChange_localMapAX hdepthA P₁.base_comp_ι P₁.isPullback_W hg
    (mem_maximalIdeal_of_surjective P₁.surj hg)
  have hcT₂ := isBaseChange_localMapAX hdepthA P₂.base_comp_ι P₂.isPullback_W hg
    (mem_maximalIdeal_of_surjective P₂.surj hg)
  have hspec₁ := local_isBaseChange_and_bijective_homDualEval hdepthA P₁ hg
  have hspec₂ := local_isBaseChange_and_bijective_homDualEval hdepthA P₂ hg
  let τT : LocU R₁ (algebraMap A R₁ g) →ₐ[A] LocU R₂ (algebraMap A R₂ g) :=
    { toRingHom := locUAppLE F.tU (F.preU g)
      commutes' := fun a ↦ by
        change locUAppLE F.tU (F.preU g) (algebraMap R₁ _ (algebraMap A R₁ a)) =
          algebraMap R₂ _ (algebraMap A R₂ a)
        rw [locUAppLE_algebraMap F.tU_comp_ι (F.preU g)]
        exact congrArg _ (τ.commutes a) }
  have htVg_b (y : Sec A V) :
      locXAppLE F.tV (F.preV g) (localMapAX P₁.base_comp_ι P₁.isPullback_V g y) =
        localMapAX P₂.base_comp_ι P₂.isPullback_V g y := by
    change locXAppLE F.tV (F.preV g) (algebraMap _ _ (secAppTop P₁.pV y)) =
      algebraMap _ _ (secAppTop P₂.pV y)
    rw [locXAppLE_algebraMap]
    congr 1
    let y' : Γ(V.obj.left, ⊤) := y
    change F.tV.appTop (P₁.pV.appTop y') = P₂.pV.appTop y'
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, F.tV_comp_pV]
  obtain ⟨u₂, hu₂c, hdual⟩ := IsBaseChange.homDualEval_natural
    hcT₁ (localMapAX P₁.base_comp_ι P₁.isPullback_V g) hspec₁.choose
    hcT₂ (localMapAX P₂.base_comp_ι P₂.isPullback_V g) hspec₂.choose
    τT (locXAppLE F.tV (F.preV g)) (fun _ _ ↦ map_add _ _ _)
    (fun t x ↦ locXAppLE_smul F.tU F.tV F.tV_comp_hom (F.preU g) (F.preV g) t x)
    htVg_b u₁
  refine ⟨u₂, hu₂c, fun i ↦ ?_⟩
  rw [localCoords, localCoords, IsBaseChange.homCoords_apply, IsBaseChange.homCoords_apply]
  exact hdual (π (Pi.single i 1))

end LocalCoords

/-! ### Global coordinates on `Hom_R(Γ(W', 𝒪), Γ(V', 𝒪))` via gluing over `U_R` -/

section GlobalCoords

private lemma isCompatible_openU {A R : Type u} [CommRing A]
    [CommRing R] [IsLocalRing R] [Algebra A R] {s : Finset A}
    (f : ∀ g : s, LocU R (algebraMap A R g.1))
    (h : ∀ (g₁ g₂ : s)
      (hle₁ : openU R (algebraMap A R (g₁.1 * g₂.1)) ≤ openU R (algebraMap A R g₁.1))
      (hle₂ : openU R (algebraMap A R (g₁.1 * g₂.1)) ≤ openU R (algebraMap A R g₂.1)),
      locURes hle₁ (f g₁) = locURes hle₂ (f g₂)) :
    TopCat.Presheaf.IsCompatible (puncturedSpectrum R).toScheme.presheaf
      (fun g : s ↦ openU R (algebraMap A R g.1)) f := by
  intro g₁ g₂
  have hmul : openU R (algebraMap A R g₁.1) ⊓ openU R (algebraMap A R g₂.1) =
      openU R (algebraMap A R (g₁.1 * g₂.1)) := by rw [map_mul, openU_mul]
  have hle₁ : openU R (algebraMap A R (g₁.1 * g₂.1)) ≤ openU R (algebraMap A R g₁.1) :=
    hmul ▸ inf_le_left
  have hle₂ : openU R (algebraMap A R (g₁.1 * g₂.1)) ≤ openU R (algebraMap A R g₂.1) :=
    hmul ▸ inf_le_right
  have hf₁ : TopologicalSpace.Opens.infLELeft _ _ = eqToHom hmul ≫ homOfLE hle₁ := rfl
  have hf₂ : TopologicalSpace.Opens.infLERight _ _ = eqToHom hmul ≫ homOfLE hle₂ := rfl
  rw [hf₁, hf₂, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
  exact congrArg ((puncturedSpectrum R).toScheme.presheaf.map (eqToHom hmul).op) (h g₁ g₂ hle₁ hle₂)

private lemma isCompatible_openX {A R : Type u} [CommRing A]
    [CommRing R] [IsLocalRing R] [Algebra A R]
    (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) {s : Finset A}
    (f : ∀ g : s, LocX R X (algebraMap A R g.1))
    (h : ∀ (g₁ g₂ : s)
      (hle₁ : openU R (algebraMap A R (g₁.1 * g₂.1)) ≤ openU R (algebraMap A R g₁.1))
      (hle₂ : openU R (algebraMap A R (g₁.1 * g₂.1)) ≤ openU R (algebraMap A R g₂.1)),
      locXRes (openX_mono X hle₁) (f g₁) = locXRes (openX_mono X hle₂) (f g₂)) :
    TopCat.Presheaf.IsCompatible X.obj.left.presheaf
      (fun g : s ↦ openX R X (algebraMap A R g.1)) f := by
  intro g₁ g₂
  have hmulU : openU R (algebraMap A R g₁.1) ⊓ openU R (algebraMap A R g₂.1) =
      openU R (algebraMap A R (g₁.1 * g₂.1)) := by rw [map_mul, openU_mul]
  have hmulX : openX R X (algebraMap A R g₁.1) ⊓ openX R X (algebraMap A R g₂.1) =
      openX R X (algebraMap A R (g₁.1 * g₂.1)) := by rw [map_mul, openX_mul]
  have hleU₁ : openU R (algebraMap A R (g₁.1 * g₂.1)) ≤ openU R (algebraMap A R g₁.1) :=
    hmulU ▸ inf_le_left
  have hleU₂ : openU R (algebraMap A R (g₁.1 * g₂.1)) ≤ openU R (algebraMap A R g₂.1) :=
    hmulU ▸ inf_le_right
  have hf₁ : TopologicalSpace.Opens.infLELeft _ _ = eqToHom hmulX ≫ homOfLE (openX_mono X hleU₁) :=
    rfl
  have hf₂ : TopologicalSpace.Opens.infLERight _ _ = eqToHom hmulX ≫ homOfLE (openX_mono X hleU₂) :=
    rfl
  rw [hf₁, hf₂, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
  exact congrArg (X.obj.left.presheaf.map (eqToHom hmulX).op) (h g₁ g₂ hleU₁ hleU₂)

private lemma secR_eq_of_locally_eq {A R : Type u} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R]
    (hdepthR : 2 ≤ depth (ModuleCat.of R R)) (hsurj : Function.Surjective (algebraMap A R))
    {s : Finset A} (hs : Ideal.span (s : Set A) = maximalIdeal A) {x y : R}
    (h : ∀ g ∈ s, algebraMap R (LocU R (algebraMap A R g)) x =
      algebraMap R (LocU R (algebraMap A R g)) y) :
    x = y := by
  have : IsIso (puncturedSpectrum R).ι.appTop := isIso_ι_appTop_puncturedSpectrum R hdepthR
  let eR : CommRingCat.of R ≅ Γ((puncturedSpectrum R).toScheme, ⊤) :=
    (Scheme.ΓSpecIso (.of R)).symm ≪≫ asIso (puncturedSpectrum R).ι.appTop
  have hgl : eR.hom x = eR.hom y :=
    (puncturedSpectrum R).toScheme.sheaf.eq_of_locally_eq'
      (fun g : s ↦ openU R (algebraMap A R g.1)) ⊤ (fun _ ↦ homOfLE le_top)
      (by rw [iSup_openU_image_eq_top hsurj hs]) _ _ fun g ↦ h g.1 g.2
  exact congrArg (fun z ↦ eR.inv z) hgl |>.trans (by simp) |>.symm.trans (by simp) |>.symm

private lemma secX_eq_of_locally_eq {A R : Type u} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] [Algebra A R]
    (hsurj : Function.Surjective (algebraMap A R))
    {s : Finset A} (hs : Ideal.span (s : Set A) = maximalIdeal A)
    (X : FiniteEtaleScheme (puncturedSpectrum R).toScheme) {x y : Sec R X}
    (h : ∀ g ∈ s, algebraMap (Sec R X) (LocX R X (algebraMap A R g)) x =
      algebraMap (Sec R X) (LocX R X (algebraMap A R g)) y) :
    x = y :=
  X.obj.left.sheaf.eq_of_locally_eq'
    (fun g : s ↦ openX R X (algebraMap A R g.1)) ⊤
    (fun _ ↦ homOfLE le_top) (by rw [iSup_openX_image_eq_top hsurj hs])
    x y fun g ↦ h g.1 g.2

section WithPullback

variable {A R : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R]
  {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme}

private def localizeSecMap (P : CoverPullback V W R) (g : A)
    (ψ : Sec R P.W' →ₗ[R] Sec R P.V') :
    LocX R P.W' (algebraMap A R g) →ₗ[LocU R (algebraMap A R g)]
      LocX R P.V' (algebraMap A R g) :=
  (isBaseChange_locX R P.depth_ge P.W' (algebraMap A R g)).lift
    ((IsScalarTower.toAlgHom R (Sec R P.V') (LocX R P.V' (algebraMap A R g))).toLinearMap ∘ₗ ψ)

private lemma localizeSecMap_apply (P : CoverPullback V W R) (g : A)
    (ψ : Sec R P.W' →ₗ[R] Sec R P.V') (w : Sec R P.W') :
    localizeSecMap P g ψ (algebraMap (Sec R P.W') (LocX R P.W' (algebraMap A R g)) w) =
      algebraMap (Sec R P.V') (LocX R P.V' (algebraMap A R g)) (ψ w) :=
  (isBaseChange_locX R P.depth_ge P.W' (algebraMap A R g)).lift_eq _ w

private lemma localizeSecMap_add (P : CoverPullback V W R) (g : A)
    (ψ₁ ψ₂ : Sec R P.W' →ₗ[R] Sec R P.V') :
    localizeSecMap P g (ψ₁ + ψ₂) = localizeSecMap P g ψ₁ + localizeSecMap P g ψ₂ := by
  apply (isBaseChange_locX R P.depth_ge P.W' (algebraMap A R g)).algHom_ext
  intro w; simp [localizeSecMap_apply]

private lemma localizeSecMap_smul (P : CoverPullback V W R) (g : A) (c : R)
    (ψ : Sec R P.W' →ₗ[R] Sec R P.V') :
    localizeSecMap P g (c • ψ) =
      algebraMap R (LocU R (algebraMap A R g)) c • localizeSecMap P g ψ := by
  apply (isBaseChange_locX R P.depth_ge P.W' (algebraMap A R g)).algHom_ext
  intro w
  change localizeSecMap P g (c • ψ) (algebraMap _ _ w) =
    (algebraMap R _ c • localizeSecMap P g ψ) (algebraMap _ _ w)
  rw [localizeSecMap_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    algebraMap_smul_locX, localizeSecMap_apply, ← algebraMap_smul (LocU R (algebraMap A R g))]

private lemma localCoords_localizeSecMap_res (hdepthA : 2 ≤ depth (ModuleCat.of A A))
    [Module.Finite A (Sec A V)] [Module.Finite A (Sec A W)]
    (P : CoverPullback V W R) {r : ℕ}
    (π : (Fin r → A) →ₗ[A] Module.Dual A (Sec A W →ₗ[A] Sec A V))
    {g h : A} (hg : g ∈ maximalIdeal A) (hh : h ∈ maximalIdeal A)
    (hle : openU R (algebraMap A R h) ≤ openU R (algebraMap A R g))
    (ψ : Sec R P.W' →ₗ[R] Sec R P.V') (i : Fin r) :
    locURes hle (localCoords hdepthA P π hg (localizeSecMap P g ψ) i) =
      localCoords hdepthA P π hh (localizeSecMap P h ψ) i := by
  obtain ⟨u', hu', hcoords⟩ := localCoords_res_le hdepthA P π hg hh hle (localizeSecMap P g ψ)
  have hu'eq : u' = localizeSecMap P h ψ := by
    apply localCoords_eq_of_eq_on_secA hdepthA P hh
    intro c
    calc u' (algebraMap _ _ (secAppTop P.pW c))
        = u' (locXRes (openX_mono P.W' hle) (algebraMap _ _ (secAppTop P.pW c))) := by
          rw [locXRes_algebraMap]
      _ = locXRes (openX_mono P.V' hle)
            (localizeSecMap P g ψ (algebraMap _ _ (secAppTop P.pW c))) := hu' _
      _ = algebraMap _ _ (ψ (secAppTop P.pW c)) := by
          rw [localizeSecMap_apply, locXRes_algebraMap]
      _ = _ := (localizeSecMap_apply P h ψ _).symm
  rw [← hu'eq, hcoords]

private lemma existsUnique_globalCoord (hdepthA : 2 ≤ depth (ModuleCat.of A A))
    [Module.Finite A (Sec A V)] [Module.Finite A (Sec A W)]
    (P : CoverPullback V W R) {r : ℕ}
    (π : (Fin r → A) →ₗ[A] Module.Dual A (Sec A W →ₗ[A] Sec A V))
    (ψ : Sec R P.W' →ₗ[R] Sec R P.V') (i : Fin r) :
    ∃! a : R, ∀ (g : A) (hg : g ∈ maximalIdeal A),
      algebraMap R (LocU R (algebraMap A R g)) a =
        localCoords hdepthA P π hg (localizeSecMap P g ψ) i := by
  obtain ⟨s, hs⟩ := (maximalIdeal A).fg_of_isNoetherianRing
  have hmem (g : s) : g.1 ∈ maximalIdeal A := hs ▸ Ideal.subset_span g.2
  have hcompat := isCompatible_openU
    (fun g : s ↦ localCoords hdepthA P π (hmem g) (localizeSecMap P g.1 ψ) i)
    fun g₁ g₂ hle₁ hle₂ ↦ by
      have hmem₁₂ : g₁.1 * g₂.1 ∈ maximalIdeal A := Ideal.mul_mem_right g₂.1 _ (hmem g₁)
      rw [localCoords_localizeSecMap_res hdepthA P π (hmem g₁) hmem₁₂ hle₁ ψ i,
        localCoords_localizeSecMap_res hdepthA P π (hmem g₂) hmem₁₂ hle₂ ψ i]
  obtain ⟨gl, hgl, _⟩ := (puncturedSpectrum R).toScheme.sheaf.existsUnique_gluing'
    (fun g : s ↦ openU R (algebraMap A R g.1)) ⊤
    (fun _ ↦ homOfLE le_top) (by rw [iSup_openU_image_eq_top P.surj hs]) _ hcompat
  have : IsIso (puncturedSpectrum R).ι.appTop := isIso_ι_appTop_puncturedSpectrum R P.depth_ge
  let eR : CommRingCat.of R ≅ Γ((puncturedSpectrum R).toScheme, ⊤) :=
    (Scheme.ΓSpecIso (.of R)).symm ≪≫ asIso (puncturedSpectrum R).ι.appTop
  let a : R := eR.inv gl
  have ha_s (g : s) : algebraMap R (LocU R (algebraMap A R g.1)) a =
      localCoords hdepthA P π (hmem g) (localizeSecMap P g.1 ψ) i := by
    have he : eR.hom a = gl := by change (eR.inv ≫ eR.hom) gl = gl; simp
    have hres : algebraMap R (LocU R (algebraMap A R g.1)) a =
        (puncturedSpectrum R).toScheme.presheaf.map
          (homOfLE (le_top : openU R (algebraMap A R g.1) ≤ ⊤)).op (eR.hom a) := rfl
    rw [hres, he]
    exact hgl g
  refine ⟨a, fun h hh ↦ ?_, fun b hb ↦ secR_eq_of_locally_eq P.depth_ge P.surj hs fun g hg ↦ ?_⟩
  · have hcov : openU R (algebraMap A R h) ≤
        ⨆ g : s, openU R (algebraMap A R (h * g.1)) := by
      intro x hx
      have hx' : x ∈ ⨆ g : s, openU R (algebraMap A R g.1) := by
        rw [iSup_openU_image_eq_top P.surj hs]; trivial
      obtain ⟨g, hgx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨g, by rw [map_mul, openU_mul]; exact ⟨hx, hgx⟩⟩
    have hle_h (g : s) : openU R (algebraMap A R (h * g.1)) ≤ openU R (algebraMap A R h) := by
      rw [map_mul, openU_mul]; exact inf_le_left
    have hle_g (g : s) : openU R (algebraMap A R (h * g.1)) ≤ openU R (algebraMap A R g.1) := by
      rw [map_mul, openU_mul]; exact inf_le_right
    apply (puncturedSpectrum R).toScheme.sheaf.eq_of_locally_eq'
      (fun g : s ↦ openU R (algebraMap A R (h * g.1))) (openU R (algebraMap A R h))
      (fun g ↦ homOfLE (hle_h g)) hcov
    intro g
    have hhg : h * g.1 ∈ maximalIdeal A := Ideal.mul_mem_right g.1 _ hh
    change locURes (hle_h g) (algebraMap R (LocU R (algebraMap A R h)) a) =
      locURes (hle_h g) (localCoords hdepthA P π hh (localizeSecMap P h ψ) i)
    rw [locURes_algebraMap (hle_h g) a, ← locURes_algebraMap (hle_g g) a, ha_s g,
      localCoords_localizeSecMap_res hdepthA P π (hmem g) hhg (hle_g g) ψ i,
      localCoords_localizeSecMap_res hdepthA P π hh hhg (hle_h g) ψ i]
  · rw [hb g (hs ▸ Ideal.subset_span hg), ha_s ⟨g, hg⟩]

private def globalCoords (hdepthA : 2 ≤ depth (ModuleCat.of A A))
    [Module.Finite A (Sec A V)] [Module.Finite A (Sec A W)]
    (P : CoverPullback V W R) {r : ℕ}
    (π : (Fin r → A) →ₗ[A] Module.Dual A (Sec A W →ₗ[A] Sec A V)) :
    (Sec R P.W' →ₗ[R] Sec R P.V') →ₗ[R] (Fin r → R) where
  toFun ψ i := (existsUnique_globalCoord hdepthA P π ψ i).choose
  map_add' ψ₁ ψ₂ := by
    obtain ⟨s, hs⟩ := (maximalIdeal A).fg_of_isNoetherianRing
    ext i
    refine secR_eq_of_locally_eq P.depth_ge P.surj hs fun g hg ↦ ?_
    have hgm : g ∈ maximalIdeal A := hs ▸ Ideal.subset_span hg
    rw [(existsUnique_globalCoord hdepthA P π (ψ₁ + ψ₂) i).choose_spec.1 g hgm, Pi.add_apply,
      map_add, (existsUnique_globalCoord hdepthA P π ψ₁ i).choose_spec.1 g hgm,
      (existsUnique_globalCoord hdepthA P π ψ₂ i).choose_spec.1 g hgm,
      localizeSecMap_add, map_add, Pi.add_apply]
  map_smul' c ψ := by
    obtain ⟨s, hs⟩ := (maximalIdeal A).fg_of_isNoetherianRing
    ext i
    refine secR_eq_of_locally_eq P.depth_ge P.surj hs fun g hg ↦ ?_
    have hgm : g ∈ maximalIdeal A := hs ▸ Ideal.subset_span hg
    rw [(existsUnique_globalCoord hdepthA P π (c • ψ) i).choose_spec.1 g hgm, RingHom.id_apply,
      Pi.smul_apply, smul_eq_mul, map_mul,
      (existsUnique_globalCoord hdepthA P π ψ i).choose_spec.1 g hgm,
      localizeSecMap_smul, map_smul, Pi.smul_apply, smul_eq_mul]

/-- The global coordinate `R`-linear map `(Γ(W', 𝒪) →ₗ[R] Γ(V', 𝒪)) →ₗ[R] (Fin r → R)`
associated to a presentation map `π : (Fin r → A) →ₗ[A] Dual A (Γ(W, 𝒪) →ₗ[A] Γ(V, 𝒪))`. -/
def CoverPullback.coords (hdepthA : 2 ≤ depth (ModuleCat.of A A))
    (P : CoverPullback V W R)
    (hfinV : letI := sectionsAlgebra A V; Module.Finite A Γ(V.obj.left, ⊤))
    (hfinW : letI := sectionsAlgebra A W; Module.Finite A Γ(W.obj.left, ⊤))
    {r : ℕ}
    (π : letI := sectionsAlgebra A V; letI := sectionsAlgebra A W;
      (Fin r → A) →ₗ[A] Module.Dual A (Γ(W.obj.left, ⊤) →ₗ[A] Γ(V.obj.left, ⊤))) :
    letI := sectionsAlgebra R P.V'
    letI := sectionsAlgebra R P.W'
    (Γ(P.W'.obj.left, ⊤) →ₗ[R] Γ(P.V'.obj.left, ⊤)) →ₗ[R] (Fin r → R) :=
  letI : Module.Finite A (Sec A V) := hfinV
  letI : Module.Finite A (Sec A W) := hfinW
  globalCoords hdepthA P π

private lemma globalCoords_spec (hdepthA : 2 ≤ depth (ModuleCat.of A A))
    (P : CoverPullback V W R)
    [Module.Finite A (Sec A V)] [Module.Finite A (Sec A W)]
    {r : ℕ}
    (π : (Fin r → A) →ₗ[A] Module.Dual A (Sec A W →ₗ[A] Sec A V))
    (ψ : Sec R P.W' →ₗ[R] Sec R P.V') {g : A} (hg : g ∈ maximalIdeal A) (i : Fin r) :
    algebraMap R (LocU R (algebraMap A R g)) (P.coords hdepthA ‹_› ‹_› π ψ i) =
      localCoords hdepthA P π hg (localizeSecMap P g ψ) i :=
  (existsUnique_globalCoord hdepthA P π ψ i).choose_spec.1 g hg

/-- **Exactness of global Hom coordinates.** When `(Fin s → A) —φ→ (Fin r → A) —π→ Dual A (C →ₗ B)
→ 0` is exact, `P.coords` is injective and its image consists of the vectors in `Fin r → R`
satisfying the transposed linear equations of `φ` with coefficients in `R`. -/
theorem CoverPullback.coords_exact (hdepthA : 2 ≤ depth (ModuleCat.of A A))
    (P : CoverPullback V W R)
    (hfinV : letI := sectionsAlgebra A V; Module.Finite A Γ(V.obj.left, ⊤))
    (hfinW : letI := sectionsAlgebra A W; Module.Finite A Γ(W.obj.left, ⊤))
    {r s : ℕ}
    {π : letI := sectionsAlgebra A V; letI := sectionsAlgebra A W;
      (Fin r → A) →ₗ[A] Module.Dual A (Γ(W.obj.left, ⊤) →ₗ[A] Γ(V.obj.left, ⊤))}
    {φ : (Fin s → A) →ₗ[A] (Fin r → A)}
    (hπ : Function.Surjective π) (hφπ : Function.Exact φ π) :
    Function.Injective (P.coords hdepthA hfinV hfinW π) ∧
      ∀ v : Fin r → R,
        (∃ ψ, P.coords hdepthA hfinV hfinW π ψ = v) ↔
          ∀ j : Fin s, ∑ i : Fin r, algebraMap A R (φ (Pi.single j 1) i) * v i = 0 := by
  let := sectionsAlgebra R P.V'
  let := sectionsAlgebra R P.W'
  let : Module.Finite A (Sec A V) := hfinV
  let : Module.Finite A (Sec A W) := hfinW
  let π' : (Fin r → A) →ₗ[A] Module.Dual A (Sec A W →ₗ[A] Sec A V) := π
  obtain ⟨gen, hgen⟩ := (maximalIdeal A).fg_of_isNoetherianRing
  have hmem (g : gen) : g.1 ∈ maximalIdeal A := hgen ▸ Ideal.subset_span g.2
  refine ⟨fun ψ₁ ψ₂ h ↦ ?_, fun v ↦ ⟨?_, ?_⟩⟩
  · let ψ₁' : Sec R P.W' →ₗ[R] Sec R P.V' := ψ₁
    let ψ₂' : Sec R P.W' →ₗ[R] Sec R P.V' := ψ₂
    refine LinearMap.ext fun w ↦ secX_eq_of_locally_eq P.surj hgen P.V' fun g hg ↦ ?_
    have hgm : g ∈ maximalIdeal A := hgen ▸ Ideal.subset_span hg
    have hu : localizeSecMap P g ψ₁' = localizeSecMap P g ψ₂' := by
      apply (localCoords_exact hdepthA P hπ hφπ hgm).1
      ext i
      rw [← globalCoords_spec hdepthA P π' ψ₁' hgm i,
        ← globalCoords_spec hdepthA P π' ψ₂' hgm i, h]
    let w' : Sec R P.W' := w
    change algebraMap _ _ (ψ₁' w') = algebraMap _ _ (ψ₂' w')
    rw [← localizeSecMap_apply P g ψ₁' w', ← localizeSecMap_apply P g ψ₂' w', hu]
  · rintro ⟨ψ, rfl⟩ j
    let ψ' : Sec R P.W' →ₗ[R] Sec R P.V' := ψ
    refine secR_eq_of_locally_eq P.depth_ge P.surj hgen fun g hg ↦ ?_
    have hgm : g ∈ maximalIdeal A := hgen ▸ Ideal.subset_span hg
    rw [map_zero, map_sum]
    have hloc := ((localCoords_exact hdepthA P hπ hφπ hgm).2
      (localCoords hdepthA P π' hgm (localizeSecMap P g ψ'))).mp
        ⟨localizeSecMap P g ψ', rfl⟩ j
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans hloc
    rw [map_mul]
    exact congrArg (_ * ·) (globalCoords_spec hdepthA P π' ψ' hgm i)
  · intro hv
    have hex (g : A) (hg : g ∈ maximalIdeal A) :
        ∃ u : LocX R P.W' (algebraMap A R g) →ₗ[LocU R (algebraMap A R g)]
            LocX R P.V' (algebraMap A R g),
          localCoords hdepthA P π' hg u =
            fun i ↦ algebraMap R (LocU R (algebraMap A R g)) (v i) := by
      refine ((localCoords_exact hdepthA P hπ hφπ hg).2 _).mpr fun j ↦ ?_
      have := congrArg (algebraMap R (LocU R (algebraMap A R g))) (hv j)
      simpa only [map_sum, map_mul, map_zero] using this
    choose u hu using hex
    have hu_res {g₁ g₂ : A} (hg₁ : g₁ ∈ maximalIdeal A) (hg₂ : g₂ ∈ maximalIdeal A)
        (hle : openU R (algebraMap A R g₂) ≤ openU R (algebraMap A R g₁)) (w : Sec R P.W') :
        locXRes (openX_mono P.V' hle)
          (u g₁ hg₁ (algebraMap (Sec R P.W') (LocX R P.W' (algebraMap A R g₁)) w)) =
          u g₂ hg₂ (algebraMap (Sec R P.W') (LocX R P.W' (algebraMap A R g₂)) w) := by
      obtain ⟨u', hu', hcoords⟩ := localCoords_res_le hdepthA P π' hg₁ hg₂ hle (u g₁ hg₁)
      have hu'eq : u' = u g₂ hg₂ := by
        apply (localCoords_exact hdepthA P hπ hφπ hg₂).1
        ext i
        rw [hcoords i, hu g₁ hg₁, hu g₂ hg₂, locURes_algebraMap hle (v i)]
      rw [← hu', hu'eq, locXRes_algebraMap (openX_mono P.W' hle) w]
    have hglue (w : Sec R P.W') :
        ∃! y : Sec R P.V', ∀ g : gen,
          algebraMap (Sec R P.V') (LocX R P.V' (algebraMap A R g.1)) y =
            u g.1 (hmem g) (algebraMap (Sec R P.W') (LocX R P.W' (algebraMap A R g.1)) w) := by
      have hcompat := isCompatible_openX P.V'
        (fun g : gen ↦ u g.1 (hmem g)
          (algebraMap (Sec R P.W') (LocX R P.W' (algebraMap A R g.1)) w)) fun g₁ g₂ hle₁ hle₂ ↦ by
        have hmem₁₂ : g₁.1 * g₂.1 ∈ maximalIdeal A := Ideal.mul_mem_right g₂.1 _ (hmem g₁)
        rw [hu_res (hmem g₁) hmem₁₂ hle₁ w, hu_res (hmem g₂) hmem₁₂ hle₂ w]
      exact P.V'.obj.left.sheaf.existsUnique_gluing'
        (fun g : gen ↦ openX R P.V' (algebraMap A R g.1)) ⊤
        (fun _ ↦ homOfLE le_top) (by rw [iSup_openX_image_eq_top P.surj hgen]) _ hcompat
    let ψ : Sec R P.W' →ₗ[R] Sec R P.V' :=
      { toFun := fun w ↦ (hglue w).choose
        map_add' := fun w₁ w₂ ↦ secX_eq_of_locally_eq P.surj hgen P.V' fun g hg ↦ by
          rw [(hglue (w₁ + w₂)).choose_spec.1 ⟨g, hg⟩, map_add, map_add, map_add,
            (hglue w₁).choose_spec.1 ⟨g, hg⟩, (hglue w₂).choose_spec.1 ⟨g, hg⟩]
        map_smul' := fun c w ↦ secX_eq_of_locally_eq P.surj hgen P.V' fun g hg ↦ by
          rw [RingHom.id_apply, (hglue (c • w)).choose_spec.1 ⟨g, hg⟩, algebraMap_smul_locX,
            algebraMap_smul_locX, (hglue w).choose_spec.1 ⟨g, hg⟩,
            ← algebraMap_smul (LocU R (algebraMap A R g)) c,
            ← algebraMap_smul (LocU R (algebraMap A R g)) c, map_smul] }
    refine ⟨ψ, funext fun i ↦ secR_eq_of_locally_eq P.depth_ge P.surj hgen fun g hg ↦ ?_⟩
    have hgm : g ∈ maximalIdeal A := hgen ▸ Ideal.subset_span hg
    have hloc : localizeSecMap P g ψ = u g hgm := by
      apply (isBaseChange_locX R P.depth_ge P.W' (algebraMap A R g)).algHom_ext
      intro w
      change localizeSecMap P g ψ (algebraMap _ _ w) = u g hgm (algebraMap _ _ w)
      rw [localizeSecMap_apply]
      exact (hglue w).choose_spec.1 ⟨g, hg⟩
    rw [globalCoords_spec hdepthA P π' ψ hgm i, hloc, hu g hgm]

/-- Two `R`-linear maps `Γ(W', 𝒪) →ₗ[R] Γ(V', 𝒪)` that agree on all sections pulled back from `W`
are equal. -/
theorem CoverPullback.linearMap_eq_of_eq_on_base (hdepthA : 2 ≤ depth (ModuleCat.of A A))
    (P : CoverPullback V W R)
    {ψ₁ ψ₂ : letI := sectionsAlgebra R P.V'; letI := sectionsAlgebra R P.W';
      Γ(P.W'.obj.left, ⊤) →ₗ[R] Γ(P.V'.obj.left, ⊤)}
    (h : ∀ c : Γ(W.obj.left, ⊤), ψ₁ (P.pW.appTop c) = ψ₂ (P.pW.appTop c)) :
    ψ₁ = ψ₂ := by
  let := sectionsAlgebra R P.V'
  let := sectionsAlgebra R P.W'
  let ψ₁' : Sec R P.W' →ₗ[R] Sec R P.V' := ψ₁
  let ψ₂' : Sec R P.W' →ₗ[R] Sec R P.V' := ψ₂
  obtain ⟨gen, hgen⟩ := (maximalIdeal A).fg_of_isNoetherianRing
  refine LinearMap.ext fun w ↦ secX_eq_of_locally_eq P.surj hgen P.V' fun g hg ↦ ?_
  have hgm : g ∈ maximalIdeal A := hgen ▸ Ideal.subset_span hg
  have hu : localizeSecMap P g ψ₁' = localizeSecMap P g ψ₂' := by
    apply localCoords_eq_of_eq_on_secA hdepthA P hgm
    intro c
    rw [localizeSecMap_apply, localizeSecMap_apply]
    exact congrArg _ (h c)
  let w' : Sec R P.W' := w
  change algebraMap _ _ (ψ₁' w') = algebraMap _ _ (ψ₂' w')
  rw [← localizeSecMap_apply P g ψ₁' w', ← localizeSecMap_apply P g ψ₂' w', hu]

end WithPullback

section WithPullbackHom

variable {A R₁ R₂ : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [Algebra A R₁]
  [CommRing R₂] [IsLocalRing R₂] [IsNoetherianRing R₂] [Algebra A R₂]
  {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme}

/-- Forward naturality of `CoverPullback.coords` along a morphism `F : CoverPullbackHom P₁ P₂ τ`. -/
theorem CoverPullbackHom.coords_map (hdepthA : 2 ≤ depth (ModuleCat.of A A))
    (hfinV : letI := sectionsAlgebra A V; Module.Finite A Γ(V.obj.left, ⊤))
    (hfinW : letI := sectionsAlgebra A W; Module.Finite A Γ(W.obj.left, ⊤))
    {P₁ : CoverPullback V W R₁} {P₂ : CoverPullback V W R₂} {τ : R₁ →ₐ[A] R₂}
    (F : CoverPullbackHom P₁ P₂ τ) {r : ℕ}
    (π : letI := sectionsAlgebra A V; letI := sectionsAlgebra A W;
      (Fin r → A) →ₗ[A] Module.Dual A (Γ(W.obj.left, ⊤) →ₗ[A] Γ(V.obj.left, ⊤)))
    (ψ₁ : letI := sectionsAlgebra R₁ P₁.V'; letI := sectionsAlgebra R₁ P₁.W';
      Γ(P₁.W'.obj.left, ⊤) →ₗ[R₁] Γ(P₁.V'.obj.left, ⊤))
    (ψ₂ : letI := sectionsAlgebra R₂ P₂.V'; letI := sectionsAlgebra R₂ P₂.W';
      Γ(P₂.W'.obj.left, ⊤) →ₗ[R₂] Γ(P₂.V'.obj.left, ⊤))
    (hcompat : ∀ c : Γ(W.obj.left, ⊤), ψ₂ (P₂.pW.appTop c) = F.tV.appTop (ψ₁ (P₁.pW.appTop c)))
    (i : Fin r) :
    P₂.coords hdepthA hfinV hfinW π ψ₂ i = τ (P₁.coords hdepthA hfinV hfinW π ψ₁ i) := by
  let : Module.Finite A (Sec A V) := hfinV
  let : Module.Finite A (Sec A W) := hfinW
  let π' : (Fin r → A) →ₗ[A] Module.Dual A (Sec A W →ₗ[A] Sec A V) := π
  let ψ₁' : Sec R₁ P₁.W' →ₗ[R₁] Sec R₁ P₁.V' := ψ₁
  let ψ₂' : Sec R₂ P₂.W' →ₗ[R₂] Sec R₂ P₂.V' := ψ₂
  obtain ⟨gen, hgen⟩ := (maximalIdeal A).fg_of_isNoetherianRing
  refine secR_eq_of_locally_eq P₂.depth_ge P₂.surj hgen fun g hg ↦ ?_
  have hgm : g ∈ maximalIdeal A := hgen ▸ Ideal.subset_span hg
  obtain ⟨u₂, hu₂c, hcoords⟩ := localCoords_hom hdepthA F π' hgm (localizeSecMap P₁ g ψ₁')
  have hu₂eq : u₂ = localizeSecMap P₂ g ψ₂' := by
    apply localCoords_eq_of_eq_on_secA hdepthA P₂ hgm
    intro c
    rw [hu₂c c, localizeSecMap_apply, localizeSecMap_apply, locXAppLE_algebraMap]
    exact congrArg _ (hcompat c).symm
  rw [globalCoords_spec hdepthA P₂ π' ψ₂' hgm i, ← hu₂eq, hcoords i,
    ← globalCoords_spec hdepthA P₁ π' ψ₁' hgm i, locUAppLE_algebraMap F.tU_comp_ι (F.preU g)]
  rfl

/-- Reverse compatibility: `τ`-compatible global coordinates imply compatibility of `ψ₁, ψ₂` on
all sections pulled back from `W`. -/
theorem CoverPullbackHom.compat_of_coords_eq (hdepthA : 2 ≤ depth (ModuleCat.of A A))
    (hfinV : letI := sectionsAlgebra A V; Module.Finite A Γ(V.obj.left, ⊤))
    (hfinW : letI := sectionsAlgebra A W; Module.Finite A Γ(W.obj.left, ⊤))
    {P₁ : CoverPullback V W R₁} {P₂ : CoverPullback V W R₂} {τ : R₁ →ₐ[A] R₂}
    (F : CoverPullbackHom P₁ P₂ τ) {r s : ℕ}
    {π : letI := sectionsAlgebra A V; letI := sectionsAlgebra A W;
      (Fin r → A) →ₗ[A] Module.Dual A (Γ(W.obj.left, ⊤) →ₗ[A] Γ(V.obj.left, ⊤))}
    {φ : (Fin s → A) →ₗ[A] (Fin r → A)}
    (hπ : Function.Surjective π) (hφπ : Function.Exact φ π)
    (ψ₁ : letI := sectionsAlgebra R₁ P₁.V'; letI := sectionsAlgebra R₁ P₁.W';
      Γ(P₁.W'.obj.left, ⊤) →ₗ[R₁] Γ(P₁.V'.obj.left, ⊤))
    (ψ₂ : letI := sectionsAlgebra R₂ P₂.V'; letI := sectionsAlgebra R₂ P₂.W';
      Γ(P₂.W'.obj.left, ⊤) →ₗ[R₂] Γ(P₂.V'.obj.left, ⊤))
    (heq : ∀ i : Fin r,
      P₂.coords hdepthA hfinV hfinW π ψ₂ i = τ (P₁.coords hdepthA hfinV hfinW π ψ₁ i))
    (c : Γ(W.obj.left, ⊤)) :
    ψ₂ (P₂.pW.appTop c) = F.tV.appTop (ψ₁ (P₁.pW.appTop c)) := by
  let : Module.Finite A (Sec A V) := hfinV
  let : Module.Finite A (Sec A W) := hfinW
  let π' : (Fin r → A) →ₗ[A] Module.Dual A (Sec A W →ₗ[A] Sec A V) := π
  let ψ₁' : Sec R₁ P₁.W' →ₗ[R₁] Sec R₁ P₁.V' := ψ₁
  let ψ₂' : Sec R₂ P₂.W' →ₗ[R₂] Sec R₂ P₂.V' := ψ₂
  let c' : Sec A W := c
  obtain ⟨gen, hgen⟩ := (maximalIdeal A).fg_of_isNoetherianRing
  change ψ₂' (secAppTop P₂.pW c') = secAppTop F.tV (ψ₁' (secAppTop P₁.pW c'))
  refine secX_eq_of_locally_eq P₂.surj hgen P₂.V' fun g hg ↦ ?_
  have hgm : g ∈ maximalIdeal A := hgen ▸ Ideal.subset_span hg
  obtain ⟨u₂, hu₂c, hcoords⟩ := localCoords_hom hdepthA F π' hgm (localizeSecMap P₁ g ψ₁')
  have hu₂eq : u₂ = localizeSecMap P₂ g ψ₂' := by
    apply (localCoords_exact hdepthA P₂ hπ hφπ hgm).1
    ext i
    rw [hcoords i, ← globalCoords_spec hdepthA P₁ π' ψ₁' hgm i,
      locUAppLE_algebraMap F.tU_comp_ι (F.preU g), AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      ← heq i, globalCoords_spec hdepthA P₂ π' ψ₂' hgm i]
  rw [← localizeSecMap_apply P₂ g ψ₂' (secAppTop P₂.pW c'), ← hu₂eq, hu₂c c',
    localizeSecMap_apply, locXAppLE_algebraMap]

end WithPullbackHom

end GlobalCoords

end TauCeti.IsLocalRing
