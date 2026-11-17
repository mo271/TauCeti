/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
public import TauCeti.RingTheory.Depth.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Henselian
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Etale
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Pullback
import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Spf
import TauCeti.AlgebraicGeometry.FiniteEtale.Hypersurface.Coordinates
import TauCeti.AlgebraicGeometry.FiniteEtale.Lefschetz
import TauCeti.AlgebraicGeometry.FiniteEtale.Sections
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Sections

/-!
# Full faithfulness of restriction to a hypersurface section

Let `(A, 𝔪)` be a Noetherian integrally closed local domain of depth at least three, and let
`f ∈ A` be an element such that `A ⧸ (f)` is local and `A` is `(f)`-adically complete. This file
proves that restriction of finite étale covers from the punctured spectrum `U` of `A` to the
punctured spectrum `U₀` of `A ⧸ (f)` is fully faithful (Stacks, Lemma 58.19.7 (0BLJ)).

Combined with the henselian lifting of finite étale schemes over `(A, (f))`
(`TauCeti.IsLocalRing.extends_iff_extends_quotient`), this yields the local Lefschetz extension
theorem and descent of purity from `A ⧸ (f)` to `A` (Stacks, Lemma 58.20.7 (0BLM)).

When `f = 0`, `A ⧸ (0) ≅ A` and restriction is an equivalence. When `f ≠ 0`, each quotient
`Rₙ = A ⧸ (f)ⁿ⁺¹` is a Noetherian local ring of depth at least two. The punctured spectra of `Rₙ`
assemble into the adic thickening system `𝔘 = Spf(A, (f)) ×_{Spec A} U`, and pulling back finite
étale covers `V, W` of `U` yields levelwise finite étale systems `𝔙, 𝔚` over `𝔘`. By topological
invariance of étale morphisms on adic thickening systems
(`TauCeti.AlgebraicGeometry.AdicThickeningSystem.liftOfEtale` and
`TauCeti.AlgebraicGeometry.AdicThickeningSystem.hom_ext_of_formallyUnramified`), morphisms
`V₀ ⟶ W₀` over `U₀` lift uniquely to compatible systems of morphisms `Vₙ ⟶ Wₙ` over `Uₙ`. Applying
the global coordinate linear maps `CoverPullback.coords` from
`TauCeti.AlgebraicGeometry.FiniteEtale.Hypersurface.Coordinates` at every level `n` produces
compatible coordinate vectors in `Rₙʳ`, which lift uniquely to `Aʳ` by `(f)`-adic completeness and
yield an `A`-linear map `Γ(W, 𝒪) →ₗ[A] Γ(V, 𝒪)`. Separatedness of `A` shows this map is a ring
homomorphism and hence comes from a unique `U`-morphism `V ⟶ W`
(`TauCeti.IsLocalRing.existsUnique_hom_puncturedSpectrum_of_appTop`).

## Main results

* `TauCeti.IsLocalRing.restrictPuncturedQuotient_faithful_of_three_le_depth`: restriction of finite
  étale covers from `U` to `U₀` is faithful.
* `TauCeti.IsLocalRing.restrictPuncturedQuotient_full_of_three_le_depth`: restriction of finite
  étale covers from `U` to `U₀` is full.
* `TauCeti.IsLocalRing.extends_iff_extends_quotient_span_singleton`: a finite étale cover of `U`
  extends to `Spec A` if and only if its restriction to `U₀` extends to `Spec (A ⧸ (f))`.
* `TauCeti.IsLocalRing.purityHolds_of_purityHolds_quotient_span_singleton`: purity for `A ⧸ (f)`
  implies purity for `A`.

## References

* [The Stacks Project, Lemma 58.19.7](https://stacks.math.columbia.edu/tag/0BLJ).
* [The Stacks Project, Lemma 58.20.7](https://stacks.math.columbia.edu/tag/0BLM).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open TauCeti.AlgebraicGeometry

universe u

namespace TauCeti.IsLocalRing

section Helpers

private lemma isLocalRing_quotient_pow_succ {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} (hf : f ∈ maximalIdeal A) (n : ℕ) :
    IsLocalRing (A ⧸ Ideal.span {f} ^ (n + 1)) := by
  have hne : Ideal.span {f} ^ (n + 1) ≠ ⊤ := fun htop ↦
    (maximalIdeal.isMaximal A).ne_top <| top_le_iff.mp <| htop ▸ by
      rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
      exact (maximalIdeal A).pow_mem_of_mem hf (n + 1) (Nat.succ_pos n)
  have : Nontrivial (A ⧸ Ideal.span {f} ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private lemma two_le_depth_quotient_pow_succ {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsDomain A] (hdepth : 3 ≤ depth (ModuleCat.of A A))
    {f : A} (hf : f ∈ maximalIdeal A) (hf0 : f ≠ 0) (n : ℕ) :
    letI := isLocalRing_quotient_pow_succ hf n
    2 ≤ depth (ModuleCat.of (A ⧸ Ideal.span {f} ^ (n + 1)) (A ⧸ Ideal.span {f} ^ (n + 1))) := by
  let := isLocalRing_quotient_pow_succ hf n
  rw [← depth_eq_depth_of_surjective (R := A) (T := A ⧸ Ideal.span {f} ^ (n + 1))
    (M := A ⧸ Ideal.span {f} ^ (n + 1))
    (Ideal.Quotient.algebraMap_eq (Ideal.span {f} ^ (n + 1)) ▸ Ideal.Quotient.mk_surjective)]
  let e : QuotSMulTop (f ^ (n + 1)) A ≃ₗ[A] A ⧸ Ideal.span {f} ^ (n + 1) :=
    (Ideal.quotientEquivAlgOfEq A (by
      simp [Ideal.span_singleton_pow, ← Submodule.ideal_span_singleton_smul])).toLinearEquiv
  rw [← depth_eq_of_linearEquiv e]
  have h1 := depth_quotSMulTop_succ_eq_depth (R := A) (M := A)
    (IsSMulRegular.of_ne_zero (pow_ne_zero (n + 1) hf0))
    ((maximalIdeal A).pow_mem_of_mem hf (n + 1) (Nat.succ_pos n))
  cases hd : depth (ModuleCat.of A (QuotSMulTop (f ^ (n + 1)) A)) with
  | top => exact le_top
  | coe k =>
    rw [hd] at h1
    have hk : 3 ≤ k + 1 := by exact_mod_cast (h1 ▸ hdepth : (3 : ℕ∞) ≤ (k : ℕ∞) + 1)
    exact_mod_cast (by omega : 2 ≤ k)

private lemma exists_finPresentation {A M : Type u} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (r s : ℕ) (π : (Fin r → A) →ₗ[A] M) (φ : (Fin s → A) →ₗ[A] (Fin r → A)),
      Function.Surjective π ∧ Function.Exact φ π := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' A M
  have : Module.Finite A (LinearMap.ker π) := Module.Finite.of_fg (IsNoetherian.noetherian _)
  obtain ⟨s, φ₀, hφ₀⟩ := Module.Finite.exists_fin' A (LinearMap.ker π)
  refine ⟨r, s, π, (LinearMap.ker π).subtype.comp φ₀, hπ, ?_⟩
  rw [LinearMap.exact_iff, LinearMap.range_comp, LinearMap.range_eq_top.mpr hφ₀,
    Submodule.map_top, Submodule.range_subtype]

private lemma eq_zero_of_forall_mk_pow_succ_eq_zero {A : Type u} [CommRing A] {I : Ideal A}
    [IsAdicComplete I A] {a : A} (h : ∀ n : ℕ, Ideal.Quotient.mk (I ^ (n + 1)) a = 0) :
    a = 0 := by
  refine IsHausdorff.haus' (I := I) a fun n ↦ ?_
  cases n with
  | zero =>
    rw [SModEq.sub_mem, pow_zero]
    simp
  | succ k =>
    simpa [SModEq.sub_mem, Ideal.smul_top_eq_map] using Ideal.Quotient.eq_zero_iff_mem.mp (h k)

private lemma exists_of_compatible_quotientPowSucc {A : Type u} [CommRing A] {I : Ideal A}
    [IsAdicComplete I A] (v : ∀ n : ℕ, A ⧸ I ^ (n + 1))
    (hcompat : ∀ n : ℕ, Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))) (v (n + 1)) = v n) :
    ∃ a : A, ∀ n : ℕ, Ideal.Quotient.mk (I ^ (n + 1)) a = v n := by
  choose g hg using fun n ↦ Ideal.Quotient.mk_surjective (v n)
  have hmk {m n : ℕ} (hmn : m ≤ n) : Ideal.Quotient.mk (I ^ (m + 1)) (g n) = v m := by
    induction hmn with
    | refl => exact hg m
    | @step k _ ih =>
      have hk := congrArg
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (k + 1))))
        (hg (k + 1))
      have hfac : Ideal.Quotient.mk (I ^ (k + 1)) (g (k + 1)) = v k := by
        simpa only [Ideal.Quotient.factor_mk, hcompat k] using hk
      have hsub : Ideal.Quotient.mk (I ^ (m + 1)) (g (k + 1)) =
          Ideal.Quotient.factor
            (Ideal.pow_le_pow_right (I := I) (Nat.succ_le_succ ‹m ≤ k›))
            (Ideal.Quotient.mk (I ^ (k + 1)) (g (k + 1))) := rfl
      rw [hsub, hfac, ← hg k]
      exact ih
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' (I := I) g fun {m n} hmn ↦ by
    have hmem : g m - g n ∈ I ^ (m + 1) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hg m, hmk hmn, sub_self]
    simpa [SModEq.sub_mem, Ideal.smul_top_eq_map] using Ideal.pow_le_pow_right (Nat.le_succ m) hmem
  refine ⟨a, fun n ↦ ?_⟩
  have hmem : g (n + 1) - a ∈ I ^ (n + 1) := by
    simpa [SModEq.sub_mem, Ideal.smul_top_eq_map] using ha (n + 1)
  have heq : Ideal.Quotient.mk (I ^ (n + 1)) (g (n + 1)) = Ideal.Quotient.mk (I ^ (n + 1)) a := by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  rw [← heq, hmk (Nat.le_succ n)]

private def secLinearMapOfHom {R : Type u} [CommRing R] [IsLocalRing R]
    (V W : FiniteEtaleScheme (puncturedSpectrum R).toScheme)
    (h : V.obj.left ⟶ W.obj.left) (hh : h ≫ W.obj.hom = V.obj.hom) :
    letI := sectionsAlgebra R V
    letI := sectionsAlgebra R W
    Γ(W.obj.left, ⊤) →ₗ[R] Γ(V.obj.left, ⊤) :=
  letI := sectionsAlgebra R V
  letI := sectionsAlgebra R W
  { toFun := h.appTop.hom
    map_add' := map_add h.appTop.hom
    map_smul' := fun r x ↦ by
      rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      change h.appTop ((W.obj.hom ≫ (puncturedSpectrum R).ι).appTop
          ((Scheme.ΓSpecIso (.of R)).inv r)) =
        (V.obj.hom ≫ (puncturedSpectrum R).ι).appTop ((Scheme.ΓSpecIso (.of R)).inv r)
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Category.assoc, hh] }

private lemma restrictPuncturedQuotient_zero_isEquivalence {A : Type u} [CommRing A]
    [IsLocalRing A] [IsLocalRing (A ⧸ Ideal.span {(0 : A)})] :
    (restrictPuncturedQuotient (Ideal.span {(0 : A)})).IsEquivalence := by
  let I : Ideal A := Ideal.span {0}
  have hI : I = ⊥ := Ideal.span_singleton_eq_bot.mpr rfl
  let e : A ≃+* A ⧸ I := (RingEquiv.quotientBot A).symm.trans (Ideal.quotEquivOfEq hI.symm)
  have halg : CommRingCat.ofHom (algebraMap A (A ⧸ I)) = e.toCommRingCatIso.hom := by
    ext x; rfl
  have hSpecIso : IsIso (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I)))) := by
    rw [halg]; infer_instance
  let hrad := radical_map_maximalIdeal_of_surjective (A := A) (A' := A ⧸ I)
    (Ideal.Quotient.algebraMap_eq I ▸ Ideal.Quotient.mk_surjective)
  let r := (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I)))).resLE
    (puncturedSpectrum A) (puncturedSpectrum (A ⧸ I)) (preimage_puncturedSpectrum hrad).ge
  have hpb : IsPullback r (puncturedSpectrum (A ⧸ I)).ι (puncturedSpectrum A).ι
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I)))) :=
    IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι _ _).symm
      (by simpa using preimage_puncturedSpectrum hrad)
  have hrIso : IsIso r :=
    (MorphismProperty.isomorphisms Scheme).of_isPullback hpb.flip hSpecIso
  let E : FiniteEtaleScheme (puncturedSpectrum A).toScheme ≌
      FiniteEtaleScheme (puncturedSpectrum (A ⧸ I)).toScheme :=
    CategoryTheory.Equivalence.mk
      (FiniteEtaleScheme.pullback r) (FiniteEtaleScheme.pullback (inv r))
      (FiniteEtaleScheme.pullbackId.symm ≪≫
        eqToIso (congrArg FiniteEtaleScheme.pullback (IsIso.inv_hom_id r).symm) ≪≫
        FiniteEtaleScheme.pullbackComp (inv r) r)
      ((FiniteEtaleScheme.pullbackComp r (inv r)).symm ≪≫
        eqToIso (congrArg FiniteEtaleScheme.pullback (IsIso.hom_inv_id r)) ≪≫
        FiniteEtaleScheme.pullbackId)
  exact E.isEquivalence_functor

end Helpers

/-! ### The adic thickening tower over a punctured spectrum -/

section AdicTower

variable {A : Type u} [CommRing A] [IsLocalRing A]

private abbrev towerBase (f : A) : AdicThickeningSystem.{u} :=
  AdicThickeningSystem.pullback (AdicThickeningSystem.spfToSpec (Ideal.span {f}))
    (AdicThickeningSystem.ofScheme.map (puncturedSpectrum A).ι)

private abbrev towerBaseToU (f : A) :
    towerBase f ⟶ AdicThickeningSystem.ofScheme.obj (puncturedSpectrum A).toScheme :=
  AdicThickeningSystem.pullback.snd (AdicThickeningSystem.spfToSpec (Ideal.span {f}))
    (AdicThickeningSystem.ofScheme.map (puncturedSpectrum A).ι)

private abbrev towerBaseToSpf (f : A) :
    towerBase f ⟶ AdicThickeningSystem.spf (Ideal.span {f}) :=
  AdicThickeningSystem.pullback.fst (AdicThickeningSystem.spfToSpec (Ideal.span {f}))
    (AdicThickeningSystem.ofScheme.map (puncturedSpectrum A).ι)

private abbrev towerSys (f : A) (X : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    AdicThickeningSystem.{u} :=
  AdicThickeningSystem.pullback (towerBaseToU f) (AdicThickeningSystem.ofScheme.map X.obj.hom)

private abbrev towerFst (f : A) (X : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    towerSys f X ⟶ towerBase f :=
  AdicThickeningSystem.pullback.fst (towerBaseToU f) (AdicThickeningSystem.ofScheme.map X.obj.hom)

private abbrev towerSnd (f : A) (X : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    towerSys f X ⟶ AdicThickeningSystem.ofScheme.obj X.obj.left :=
  AdicThickeningSystem.pullback.snd (towerBaseToU f) (AdicThickeningSystem.ofScheme.map X.obj.hom)

private def towerSndApp (f : A) (X : FiniteEtaleScheme (puncturedSpectrum A).toScheme) (n : ℕ) :
    (towerSys f X).X n ⟶ X.obj.left :=
  (towerSnd f X).app n

private lemma towerSndApp_naturality (f : A) (X : FiniteEtaleScheme (puncturedSpectrum A).toScheme)
    (n : ℕ) : (towerSys f X).ι n ≫ towerSndApp f X (n + 1) = towerSndApp f X n :=
  ((towerSnd f X).naturality n).trans (Category.comp_id _)

private lemma isPullback_towerSys (f : A) (X : FiniteEtaleScheme (puncturedSpectrum A).toScheme)
    (n : ℕ) :
    IsPullback ((towerFst f X).app n) (towerSndApp f X n)
      ((towerBaseToU f).app n) X.obj.hom := by
  dsimp only [towerSndApp]
  rw [AdicThickeningSystem.pullback.fst_app (towerBaseToU f),
    AdicThickeningSystem.pullback.snd_app (towerBaseToU f)]
  exact IsPullback.of_hasPullback ((towerBaseToU f).app n)
    ((AdicThickeningSystem.ofScheme.map X.obj.hom).app n)

private lemma etale_towerFst_app (f : A) (X : FiniteEtaleScheme (puncturedSpectrum A).toScheme)
    (n : ℕ) : Etale ((towerFst f X).app n) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale.{u})
    (isPullback_towerSys f X n).flip ((finiteEtaleSchemeProperty_iff X.obj).mp X.property).2

private lemma isFinite_towerFst_app (f : A) (X : FiniteEtaleScheme (puncturedSpectrum A).toScheme)
    (n : ℕ) : IsFinite ((towerFst f X).app n) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite.{u})
    (isPullback_towerSys f X n).flip ((finiteEtaleSchemeProperty_iff X.obj).mp X.property).1

private def towerMap (f : A) {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    (g : V ⟶ W) : towerSys f V ⟶ towerSys f W :=
  AdicThickeningSystem.pullback.lift (towerFst f V)
    (towerSnd f V ≫ AdicThickeningSystem.ofScheme.map g.hom.left) (by
      rw [Category.assoc, ← Functor.map_comp, Over.w g.hom]
      exact AdicThickeningSystem.pullback.condition _ _)

private lemma towerMap_comp_fst (f : A) {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    (g : V ⟶ W) : towerMap f g ≫ towerFst f W = towerFst f V :=
  AdicThickeningSystem.pullback.lift_fst _ _ _

private lemma towerMap_app_comp_snd (f : A) {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme}
    (g : V ⟶ W) (n : ℕ) :
    (towerMap f g).app n ≫ towerSndApp f W n = towerSndApp f V n ≫ g.hom.left :=
  congrArg (fun k ↦ k.app n) (AdicThickeningSystem.pullback.lift_snd (towerFst f V)
    (towerSnd f V ≫ AdicThickeningSystem.ofScheme.map g.hom.left) _)

private def levelBaseHom {f : A} (hf : f ∈ maximalIdeal A) (n : ℕ) :
    letI := isLocalRing_quotient_pow_succ hf n
    (puncturedSpectrum (A ⧸ Ideal.span {f} ^ (n + 1))).toScheme ⟶
      (puncturedSpectrum A).toScheme :=
  letI := isLocalRing_quotient_pow_succ hf n
  let hrad := radical_map_maximalIdeal_of_surjective (A := A)
    (A' := A ⧸ Ideal.span {f} ^ (n + 1))
    (Ideal.Quotient.algebraMap_eq (Ideal.span {f} ^ (n + 1)) ▸ Ideal.Quotient.mk_surjective)
  (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ Ideal.span {f} ^ (n + 1))))).resLE
    (puncturedSpectrum A) (puncturedSpectrum (A ⧸ Ideal.span {f} ^ (n + 1)))
    (preimage_puncturedSpectrum hrad).ge

private lemma isPullback_levelBase {f : A} (hf : f ∈ maximalIdeal A) (n : ℕ) :
    letI := isLocalRing_quotient_pow_succ hf n
    IsPullback (puncturedSpectrum (A ⧸ Ideal.span {f} ^ (n + 1))).ι
      (levelBaseHom hf n)
      ((AdicThickeningSystem.spfToSpec (Ideal.span {f})).app n)
      (puncturedSpectrum A).ι := by
  let := isLocalRing_quotient_pow_succ hf n
  have hrad := radical_map_maximalIdeal_of_surjective (A := A)
    (A' := A ⧸ Ideal.span {f} ^ (n + 1))
    (Ideal.Quotient.algebraMap_eq (Ideal.span {f} ^ (n + 1)) ▸ Ideal.Quotient.mk_surjective)
  rw [AdicThickeningSystem.spfToSpec_app]
  exact (IsOpenImmersion.isPullback (levelBaseHom hf n)
    (puncturedSpectrum (A ⧸ Ideal.span {f} ^ (n + 1))).ι (puncturedSpectrum A).ι
    (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ Ideal.span {f} ^ (n + 1)))))
    (Scheme.Hom.resLE_comp_ι _ _).symm
    (by simpa using preimage_puncturedSpectrum hrad)).flip

private def levelBaseIso {f : A} (hf : f ∈ maximalIdeal A) (n : ℕ) :
    letI := isLocalRing_quotient_pow_succ hf n
    (puncturedSpectrum (A ⧸ Ideal.span {f} ^ (n + 1))).toScheme ≅ (towerBase f).X n :=
  letI := isLocalRing_quotient_pow_succ hf n
  (isPullback_levelBase hf n).isoPullback

private lemma levelBaseIso_hom_fst {f : A} (hf : f ∈ maximalIdeal A) (n : ℕ) :
    letI := isLocalRing_quotient_pow_succ hf n
    (levelBaseIso hf n).hom ≫ (towerBaseToSpf f).app n =
      (puncturedSpectrum (A ⧸ Ideal.span {f} ^ (n + 1))).ι := by
  let := isLocalRing_quotient_pow_succ hf n
  rw [AdicThickeningSystem.pullback.fst_app]
  exact (isPullback_levelBase hf n).isoPullback_hom_fst

private lemma levelBaseIso_hom_snd {f : A} (hf : f ∈ maximalIdeal A) (n : ℕ) :
    letI := isLocalRing_quotient_pow_succ hf n
    (levelBaseIso hf n).hom ≫ (towerBaseToU f).app n = levelBaseHom hf n := by
  let := isLocalRing_quotient_pow_succ hf n
  rw [AdicThickeningSystem.pullback.snd_app]
  exact (isPullback_levelBase hf n).isoPullback_hom_snd

private def levelCover {f : A} (hf : f ∈ maximalIdeal A) (n : ℕ)
    (X : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    letI := isLocalRing_quotient_pow_succ hf n
    FiniteEtaleScheme (puncturedSpectrum (A ⧸ Ideal.span {f} ^ (n + 1))).toScheme :=
  letI := isLocalRing_quotient_pow_succ hf n
  haveI := etale_towerFst_app f X n
  haveI := isFinite_towerFst_app f X n
  ⟨Over.mk ((towerFst f X).app n ≫ (levelBaseIso hf n).inv),
    (finiteEtaleSchemeProperty_iff _).mpr ⟨by dsimp; infer_instance, by dsimp; infer_instance⟩⟩

private def towerPullback [IsNoetherianRing A] [IsDomain A] {f : A}
    (hf : f ∈ maximalIdeal A) (hf0 : f ≠ 0) (hdepth : 3 ≤ depth (ModuleCat.of A A))
    (V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme) (n : ℕ) :
    letI := isLocalRing_quotient_pow_succ hf n
    CoverPullback V W (A ⧸ Ideal.span {f} ^ (n + 1)) :=
  letI := isLocalRing_quotient_pow_succ hf n
  { surj := Ideal.Quotient.algebraMap_eq (Ideal.span {f} ^ (n + 1)) ▸ Ideal.Quotient.mk_surjective
    depth_ge := two_le_depth_quotient_pow_succ hdepth hf hf0 n
    base := levelBaseHom hf n
    base_comp_ι := Scheme.Hom.resLE_comp_ι _ _
    V' := levelCover hf n V
    W' := levelCover hf n W
    pV := towerSndApp f V n
    pW := towerSndApp f W n
    isPullback_V := (isPullback_towerSys f V n).flip.of_iso
      (Iso.refl _) (Iso.refl _) (levelBaseIso hf n).symm (Iso.refl _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      (Category.id_comp _).symm
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans
        ((Iso.inv_comp_eq (levelBaseIso hf n)).mpr (levelBaseIso_hom_snd hf n).symm).symm)
    isPullback_W := (isPullback_towerSys f W n).flip.of_iso
      (Iso.refl _) (Iso.refl _) (levelBaseIso hf n).symm (Iso.refl _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      (Category.id_comp _).symm
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans
        ((Iso.inv_comp_eq (levelBaseIso hf n)).mpr (levelBaseIso_hom_snd hf n).symm).symm) }

private def towerFactorAlgHom (f : A) (n : ℕ) :
    (A ⧸ Ideal.span {f} ^ (n + 2)) →ₐ[A] (A ⧸ Ideal.span {f} ^ (n + 1)) where
  toRingHom := Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  commutes' _ := rfl

private def towerStep [IsNoetherianRing A] [IsDomain A] {f : A}
    (hf : f ∈ maximalIdeal A) (hf0 : f ≠ 0) (hdepth : 3 ≤ depth (ModuleCat.of A A))
    (V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme) (n : ℕ) :
    letI := isLocalRing_quotient_pow_succ hf (n + 1)
    letI := isLocalRing_quotient_pow_succ hf n
    CoverPullbackHom (towerPullback hf hf0 hdepth V W (n + 1))
      (towerPullback hf hf0 hdepth V W n) (towerFactorAlgHom f n) :=
  letI := isLocalRing_quotient_pow_succ hf (n + 1)
  letI := isLocalRing_quotient_pow_succ hf n
  { tU := (levelBaseIso hf n).hom ≫ (towerBase f).ι n ≫ (levelBaseIso hf (n + 1)).inv
    tU_comp_base := by
      have h1 : (levelBaseIso hf (n + 1)).inv ≫ levelBaseHom hf (n + 1) =
          (towerBaseToU f).app (n + 1) :=
        (Iso.inv_comp_eq _).mpr (levelBaseIso_hom_snd hf (n + 1)).symm
      have hnat : (towerBase f).ι n ≫ (towerBaseToU f).app (n + 1) = (towerBaseToU f).app n :=
        ((towerBaseToU f).naturality n).trans (Category.comp_id _)
      exact (Category.assoc _ _ _).trans <|
        (congrArg ((levelBaseIso hf n).hom ≫ ·)
          ((Category.assoc _ _ _).trans <|
            (congrArg ((towerBase f).ι n ≫ ·) h1).trans hnat)).trans
          (levelBaseIso_hom_snd hf n)
    tU_comp_ι := by
      have h1 : (levelBaseIso hf (n + 1)).inv ≫
          (puncturedSpectrum (A ⧸ Ideal.span {f} ^ (n + 1 + 1))).ι =
          (towerBaseToSpf f).app (n + 1) :=
        (Iso.inv_comp_eq _).mpr (levelBaseIso_hom_fst hf (n + 1)).symm
      have hnat : (towerBase f).ι n ≫ (towerBaseToSpf f).app (n + 1) =
          (towerBaseToSpf f).app n ≫ (AdicThickeningSystem.spf (Ideal.span {f})).ι n :=
        (towerBaseToSpf f).naturality n
      exact (Category.assoc _ _ _).trans <|
        (congrArg ((levelBaseIso hf n).hom ≫ ·)
          ((Category.assoc _ _ _).trans <|
            (congrArg ((towerBase f).ι n ≫ ·) h1).trans hnat)).trans <|
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (levelBaseIso_hom_fst hf n))
    tV := (towerSys f V).ι n
    tV_comp_hom := by
      change (towerSys f V).ι n ≫ ((towerFst f V).app (n + 1) ≫ (levelBaseIso hf (n + 1)).inv) =
        ((towerFst f V).app n ≫ (levelBaseIso hf n).inv) ≫
          ((levelBaseIso hf n).hom ≫ (towerBase f).ι n ≫ (levelBaseIso hf (n + 1)).inv)
      rw [← Category.assoc, (towerFst f V).naturality n, Category.assoc, Category.assoc,
        Iso.inv_hom_id_assoc]
    tV_comp_pV := towerSndApp_naturality f V n
    tW := (towerSys f W).ι n
    tW_comp_hom := by
      change (towerSys f W).ι n ≫ ((towerFst f W).app (n + 1) ≫ (levelBaseIso hf (n + 1)).inv) =
        ((towerFst f W).app n ≫ (levelBaseIso hf n).inv) ≫
          ((levelBaseIso hf n).hom ≫ (towerBase f).ι n ≫ (levelBaseIso hf (n + 1)).inv)
      rw [← Category.assoc, (towerFst f W).naturality n, Category.assoc, Category.assoc,
        Iso.inv_hom_id_assoc]
    tW_comp_pW := towerSndApp_naturality f W n }

/-! ### Comparison between level zero of the tower and `restrictPuncturedQuotient` -/

private lemma isPullback_levelZero_quotient {f : A} [IsLocalRing (A ⧸ Ideal.span {f})] :
    letI hrad := radical_map_maximalIdeal_of_surjective (A := A) (A' := A ⧸ Ideal.span {f})
      (Ideal.Quotient.algebraMap_eq (Ideal.span {f}) ▸ Ideal.Quotient.mk_surjective)
    letI r₀ := (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ Ideal.span {f})))).resLE
      (puncturedSpectrum A) (puncturedSpectrum (A ⧸ Ideal.span {f}))
      (preimage_puncturedSpectrum hrad).ge
    letI e₀ : A ⧸ Ideal.span {f} ^ 1 ≃+* A ⧸ Ideal.span {f} :=
      Ideal.quotEquivOfEq (pow_one (Ideal.span {f}))
    IsPullback ((puncturedSpectrum (A ⧸ Ideal.span {f})).ι ≫ Spec.map e₀.toCommRingCatIso.hom) r₀
      ((AdicThickeningSystem.spfToSpec (Ideal.span {f})).app 0) (puncturedSpectrum A).ι := by
  let hrad := radical_map_maximalIdeal_of_surjective (A := A) (A' := A ⧸ Ideal.span {f})
    (Ideal.Quotient.algebraMap_eq (Ideal.span {f}) ▸ Ideal.Quotient.mk_surjective)
  let r₀ := (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ Ideal.span {f})))).resLE
    (puncturedSpectrum A) (puncturedSpectrum (A ⧸ Ideal.span {f}))
    (preimage_puncturedSpectrum hrad).ge
  let e₀ : A ⧸ Ideal.span {f} ^ 1 ≃+* A ⧸ Ideal.span {f} :=
    Ideal.quotEquivOfEq (pow_one (Ideal.span {f}))
  have hpb0 : IsPullback (puncturedSpectrum (A ⧸ Ideal.span {f})).ι r₀
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ Ideal.span {f}))))
      (puncturedSpectrum A).ι :=
    (IsOpenImmersion.isPullback r₀ (puncturedSpectrum (A ⧸ Ideal.span {f})).ι
      (puncturedSpectrum A).ι
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ Ideal.span {f}))))
      (Scheme.Hom.resLE_comp_ι _ _).symm
      (by simpa using preimage_puncturedSpectrum hrad)).flip
  have hfac : Spec.map e₀.toCommRingCatIso.hom ≫
      (AdicThickeningSystem.spfToSpec (Ideal.span {f})).app 0 =
      Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ Ideal.span {f}))) := by
    refine (congrArg (Spec.map e₀.toCommRingCatIso.hom ≫ ·)
      (AdicThickeningSystem.spfToSpec_app (Ideal.span {f}) 0)).trans ?_
    change Spec.map e₀.toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f} ^ 1))) = _
    rw [← Spec.map_comp]
    congr 1
  exact hpb0.of_iso (Iso.refl _) (Scheme.Spec.mapIso e₀.toCommRingCatIso.op)
    (Iso.refl _) (Iso.refl _)
    (Category.id_comp _).symm
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans hfac.symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

private def levelZeroBaseIso {f : A} [IsLocalRing (A ⧸ Ideal.span {f})] :
    (puncturedSpectrum (A ⧸ Ideal.span {f})).toScheme ≅ (towerBase f).X 0 :=
  (isPullback_levelZero_quotient (f := f)).isoPullback

private lemma levelZeroBaseIso_hom_snd {f : A} [IsLocalRing (A ⧸ Ideal.span {f})] :
    (levelZeroBaseIso (f := f)).hom ≫ (towerBaseToU f).app 0 =
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ Ideal.span {f})))).resLE
        (puncturedSpectrum A) (puncturedSpectrum (A ⧸ Ideal.span {f}))
        (preimage_puncturedSpectrum (radical_map_maximalIdeal_of_surjective (A := A)
          (A' := A ⧸ Ideal.span {f})
          (Ideal.Quotient.algebraMap_eq (Ideal.span {f}) ▸ Ideal.Quotient.mk_surjective))).ge := by
  rw [AdicThickeningSystem.pullback.snd_app]
  exact (isPullback_levelZero_quotient (f := f)).isoPullback_hom_snd

private def levelZeroCoverIso {f : A} [IsLocalRing (A ⧸ Ideal.span {f})]
    (X : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    ((restrictPuncturedQuotient (Ideal.span {f})).obj X).obj.left ≅ (towerSys f X).X 0 := by
  let hrad := radical_map_maximalIdeal_of_surjective (A := A) (A' := A ⧸ Ideal.span {f})
    (Ideal.Quotient.algebraMap_eq (Ideal.span {f}) ▸ Ideal.Quotient.mk_surjective)
  let r₀ := (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ Ideal.span {f})))).resLE
    (puncturedSpectrum A) (puncturedSpectrum (A ⧸ Ideal.span {f}))
    (preimage_puncturedSpectrum hrad).ge
  have hpb : IsPullback
      (((restrictPuncturedQuotient (Ideal.span {f})).obj X).obj.hom ≫
        (levelZeroBaseIso (f := f)).hom)
      (Limits.pullback.fst X.obj.hom r₀)
      ((towerBaseToU f).app 0) X.obj.hom :=
    (IsPullback.of_hasPullback X.obj.hom r₀).flip.of_iso
      (Iso.refl _) (levelZeroBaseIso (f := f)) (Iso.refl _) (Iso.refl _)
      (Category.id_comp _).symm
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (levelZeroBaseIso_hom_snd (f := f)).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact hpb.isoPullback

private lemma levelZeroCoverIso_hom_fst {f : A} [IsLocalRing (A ⧸ Ideal.span {f})]
    (X : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (levelZeroCoverIso (f := f) X).hom ≫ (towerFst f X).app 0 =
      ((restrictPuncturedQuotient (Ideal.span {f})).obj X).obj.hom ≫
        (levelZeroBaseIso (f := f)).hom := by
  rw [AdicThickeningSystem.pullback.fst_app (towerBaseToU f)]
  exact IsPullback.isoPullback_hom_fst _

private lemma levelZeroCoverIso_hom_snd {f : A} [IsLocalRing (A ⧸ Ideal.span {f})]
    (X : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (levelZeroCoverIso (f := f) X).hom ≫ towerSndApp f X 0 =
      Limits.pullback.fst X.obj.hom _ := by
  dsimp only [towerSndApp]
  rw [AdicThickeningSystem.pullback.snd_app (towerBaseToU f)]
  exact IsPullback.isoPullback_hom_snd _

private lemma levelZeroCoverIso_naturality {f : A} [IsLocalRing (A ⧸ Ideal.span {f})]
    {V W : FiniteEtaleScheme (puncturedSpectrum A).toScheme} (g : V ⟶ W) :
    (levelZeroCoverIso (f := f) V).hom ≫ (towerMap f g).app 0 =
      ((restrictPuncturedQuotient (Ideal.span {f})).map g).hom.left ≫
        (levelZeroCoverIso (f := f) W).hom := by
  refine (isPullback_towerSys f W 0).hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, levelZeroCoverIso_hom_fst,
      ← AdicThickeningSystem.comp_app, towerMap_comp_fst, levelZeroCoverIso_hom_fst,
      ← Category.assoc, Over.w ((restrictPuncturedQuotient (Ideal.span {f})).map g).hom]
  · rw [Category.assoc, Category.assoc, levelZeroCoverIso_hom_snd, towerMap_app_comp_snd,
      ← Category.assoc, levelZeroCoverIso_hom_snd]
    exact (Limits.pullback.lift_fst _ _ _).symm

private lemma sec_eq_zero_of_forall_tower_eq_zero [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A] {f : A} [IsAdicComplete (Ideal.span {f}) A]
    (hf : f ∈ maximalIdeal A) (hf0 : f ≠ 0) (hdepth : 3 ≤ depth (ModuleCat.of A A))
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme)
    {b : Γ(V.obj.left, ⊤)}
    (hb : ∀ n : ℕ, (towerSndApp f V n).appTop b = 0) : b = 0 := by
  have hdepthA : 2 ≤ depth (ModuleCat.of A A) := le_trans (by decide) hdepth
  let W : FiniteEtaleScheme (puncturedSpectrum A).toScheme :=
    ⟨Over.mk (𝟙 (puncturedSpectrum A).toScheme),
      (finiteEtaleSchemeProperty_iff _).mpr ⟨by dsimp; infer_instance, by dsimp; infer_instance⟩⟩
  have hfinV : letI := sectionsAlgebra A V; Module.Finite A Γ(V.obj.left, ⊤) :=
    finite_sections_puncturedSpectrum hdepthA V
  have hfinW : letI := sectionsAlgebra A W; Module.Finite A Γ(W.obj.left, ⊤) :=
    finite_sections_puncturedSpectrum hdepthA W
  let := sectionsAlgebra A V
  let := sectionsAlgebra A W
  have : IsIso (puncturedSpectrum A).ι.appTop := isIso_ι_appTop_puncturedSpectrum A hdepthA
  let eA : CommRingCat.of A ≅ Γ(W.obj.left, ⊤) :=
    (Scheme.ΓSpecIso (.of A)).symm ≪≫ asIso (puncturedSpectrum A).ι.appTop
  let μ : Γ(W.obj.left, ⊤) →ₗ[A] Γ(V.obj.left, ⊤) :=
    { toFun := fun x ↦ eA.inv x • b
      map_add' := fun x y ↦ by rw [map_add, add_smul]
      map_smul' := fun a x ↦ by
        rw [RingHom.id_apply, Algebra.smul_def (r := a) (x := x), map_mul, mul_smul]
        congr 1
        have hcomp : algebraMap A Γ(W.obj.left, ⊤) a = eA.hom a := by
          change ((W.obj.hom ≫ (puncturedSpectrum A).ι).appTop ((Scheme.ΓSpecIso (.of A)).inv a)) =
            (puncturedSpectrum A).ι.appTop ((Scheme.ΓSpecIso (.of A)).inv a)
          dsimp only [W, Over.mk_hom]
          simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.comp_apply,
            CommRingCat.id_apply]
        rw [hcomp]
        change (eA.hom ≫ eA.inv) a = a
        simp }
  obtain ⟨r, s, π, φ, hπ, hφπ⟩ :=
    exists_finPresentation (A := A) (M := Module.Dual A (Γ(W.obj.left, ⊤) →ₗ[A] Γ(V.obj.left, ⊤)))
  let Pid := CoverPullback.id hdepthA V W
  have hcoords : Pid.coords hdepthA hfinV hfinW π μ = 0 := by
    ext i
    refine eq_zero_of_forall_mk_pow_succ_eq_zero (I := Ideal.span {f}) fun n ↦ ?_
    let := isLocalRing_quotient_pow_succ hf n
    let Pn := towerPullback hf hf0 hdepth V W n
    let := sectionsAlgebra (A ⧸ Ideal.span {f} ^ (n + 1)) Pn.V'
    let := sectionsAlgebra (A ⧸ Ideal.span {f} ^ (n + 1)) Pn.W'
    have hmap := CoverPullbackHom.coords_map hdepthA hfinV hfinW
      (CoverPullbackHom.fromId hdepthA Pn) π μ 0 (fun c ↦ ?_) i
    · rw [map_zero, Pi.zero_apply] at hmap
      exact hmap.symm
    · simp only [LinearMap.zero_apply, CoverPullbackHom.fromId, CoverPullback.id,
        Scheme.Hom.id_appTop]
      change 0 = (towerSndApp f V n).appTop (eA.inv c • b)
      rw [Algebra.smul_def, map_mul, hb n, mul_zero]
  have hμ0 : μ = 0 :=
    (Pid.coords_exact hdepthA hfinV hfinW hπ hφπ).1 (hcoords.trans (map_zero _).symm)
  have h1 := congrArg (fun f : Γ(W.obj.left, ⊤) →ₗ[A] Γ(V.obj.left, ⊤) ↦ f 1) hμ0
  simpa [μ] using h1

end AdicTower

/-! ### Full faithfulness of restriction and descent of purity -/

section Main

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsDomain A] [IsIntegrallyClosed A] {f : A} [IsAdicComplete (Ideal.span {f}) A]
  [IsLocalRing (A ⧸ Ideal.span {f})]

/-- **Faithfulness of restriction to a hypersurface section.** Let `A` be a Noetherian integrally
closed local domain of depth at least three, and let `f ∈ A` be an element such that `A ⧸ (f)` is
local and `A` is `(f)`-adically complete. Then restriction of finite étale covers from the
punctured spectrum of `A` to that of `A ⧸ (f)` is faithful. -/
@[stacks 0BLJ "faithful, integrally closed complete local domain case"]
theorem restrictPuncturedQuotient_faithful_of_three_le_depth
    (hdepth : 3 ≤ depth (ModuleCat.of A A)) :
    (restrictPuncturedQuotient (Ideal.span {f})).Faithful := by
  rcases eq_or_ne f 0 with rfl | hf0
  · have := restrictPuncturedQuotient_zero_isEquivalence (A := A)
    infer_instance
  have hf : f ∈ maximalIdeal A :=
    le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp inferInstance)
      (Ideal.mem_span_singleton_self f)
  have hdepthA : 2 ≤ depth (ModuleCat.of A A) := le_trans (by decide) hdepth
  refine ⟨fun {V W} g₁ g₂ heq ↦ ?_⟩
  have h0 : (towerMap f g₁).app 0 = (towerMap f g₂).app 0 := by
    rw [← cancel_epi (levelZeroCoverIso (f := f) V).hom, levelZeroCoverIso_naturality,
      levelZeroCoverIso_naturality, heq]
  have : ∀ n, FormallyUnramified ((towerFst f W).app n) := fun n ↦
    have := etale_towerFst_app f W n; inferInstance
  have hsys : towerMap f g₁ = towerMap f g₂ :=
    AdicThickeningSystem.hom_ext_of_formallyUnramified (towerFst f W)
      ((towerMap_comp_fst f g₁).trans (towerMap_comp_fst f g₂).symm) h0
  have hfinV : letI := sectionsAlgebra A V; Module.Finite A Γ(V.obj.left, ⊤) :=
    finite_sections_puncturedSpectrum hdepthA V
  have hfinW : letI := sectionsAlgebra A W; Module.Finite A Γ(W.obj.left, ⊤) :=
    finite_sections_puncturedSpectrum hdepthA W
  let := sectionsAlgebra A V
  let := sectionsAlgebra A W
  obtain ⟨r, s, π, φ, hπ, hφπ⟩ :=
    exists_finPresentation (A := A) (M := Module.Dual A (Γ(W.obj.left, ⊤) →ₗ[A] Γ(V.obj.left, ⊤)))
  let ψ₁ := secLinearMapOfHom V W g₁.hom.left (Over.w g₁.hom)
  let ψ₂ := secLinearMapOfHom V W g₂.hom.left (Over.w g₂.hom)
  let Pid := CoverPullback.id hdepthA V W
  have hcoords : Pid.coords hdepthA hfinV hfinW π ψ₁ = Pid.coords hdepthA hfinV hfinW π ψ₂ := by
    ext i
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_mk_pow_succ_eq_zero (I := Ideal.span {f}) fun n ↦ ?_
    rw [map_sub, sub_eq_zero]
    let := isLocalRing_quotient_pow_succ hf n
    let Pn := towerPullback hf hf0 hdepth V W n
    have hwn (g : V ⟶ W) : (towerMap f g).app n ≫ Pn.W'.obj.hom = Pn.V'.obj.hom := by
      change (towerMap f g).app n ≫ ((towerFst f W).app n ≫ (levelBaseIso hf n).inv) =
        (towerFst f V).app n ≫ (levelBaseIso hf n).inv
      rw [← Category.assoc, ← AdicThickeningSystem.comp_app, towerMap_comp_fst]
    have hcomp (g : V ⟶ W) (c : Γ(W.obj.left, ⊤)) :
        secLinearMapOfHom Pn.V' Pn.W' ((towerMap f g).app n) (hwn g) (Pn.pW.appTop c) =
          Pn.pV.appTop (secLinearMapOfHom V W g.hom.left (Over.w g.hom) c) := by
      change ((towerMap f g).app n).appTop ((towerSndApp f W n).appTop c) =
        (towerSndApp f V n).appTop (g.hom.left.appTop c)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, towerMap_app_comp_snd]
    have hm1 := CoverPullbackHom.coords_map hdepthA hfinV hfinW
      (CoverPullbackHom.fromId hdepthA Pn) π ψ₁
      (secLinearMapOfHom Pn.V' Pn.W' ((towerMap f g₁).app n) (hwn g₁)) (hcomp g₁) i
    have hm2 := CoverPullbackHom.coords_map hdepthA hfinV hfinW
      (CoverPullbackHom.fromId hdepthA Pn) π ψ₂
      (secLinearMapOfHom Pn.V' Pn.W' ((towerMap f g₂).app n) (hwn g₂)) (hcomp g₂) i
    have hψn : secLinearMapOfHom Pn.V' Pn.W' ((towerMap f g₁).app n) (hwn g₁) =
        secLinearMapOfHom Pn.V' Pn.W' ((towerMap f g₂).app n) (hwn g₂) := by
      let := sectionsAlgebra (A ⧸ Ideal.span {f} ^ (n + 1)) Pn.V'
      let := sectionsAlgebra (A ⧸ Ideal.span {f} ^ (n + 1)) Pn.W'
      ext x
      change ((towerMap f g₁).app n).appTop x = ((towerMap f g₂).app n).appTop x
      rw [hsys]
    exact hm1.symm.trans (by rw [hψn]; exact hm2)
  have hψeq : ψ₁ = ψ₂ := (Pid.coords_exact hdepthA hfinV hfinW hπ hφπ).1 hcoords
  have happ : g₁.hom.left.appTop = g₂.hom.left.appTop := by
    ext x; exact congrArg (fun l : Γ(W.obj.left, ⊤) →ₗ[A] Γ(V.obj.left, ⊤) ↦ l x) hψeq
  have huniq := existsUnique_hom_puncturedSpectrum_of_appTop A hdepthA V.obj.hom W.obj.hom
    g₁.hom.left.appTop (by rw [← Scheme.Hom.comp_appTop, ← Category.assoc, Over.w g₁.hom])
  have hleft : g₁.hom.left = g₂.hom.left :=
    huniq.unique ⟨Over.w g₁.hom, rfl⟩ ⟨Over.w g₂.hom, happ.symm⟩
  exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext hleft)

/-- **Fullness of restriction to a hypersurface section.** Let `A` be a Noetherian integrally
closed local domain of depth at least three, and let `f ∈ A` be an element such that `A ⧸ (f)` is
local and `A` is `(f)`-adically complete. Then restriction of finite étale covers from the
punctured spectrum of `A` to that of `A ⧸ (f)` is full. -/
@[stacks 0BLJ "full, integrally closed complete local domain case"]
theorem restrictPuncturedQuotient_full_of_three_le_depth
    (hdepth : 3 ≤ depth (ModuleCat.of A A)) :
    (restrictPuncturedQuotient (Ideal.span {f})).Full := by
  rcases eq_or_ne f 0 with rfl | hf0
  · have := restrictPuncturedQuotient_zero_isEquivalence (A := A)
    infer_instance
  have hf : f ∈ maximalIdeal A :=
    le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp inferInstance)
      (Ideal.mem_span_singleton_self f)
  have hdepthA : 2 ≤ depth (ModuleCat.of A A) := le_trans (by decide) hdepth
  refine ⟨fun {V W} g₀ ↦ ?_⟩
  -- Lift `g₀` across the adic thickening system `towerSys f V ⟶ towerSys f W`.
  let a₀ : (towerSys f V).X 0 ⟶ (towerSys f W).X 0 :=
    (levelZeroCoverIso (f := f) V).inv ≫ g₀.hom.left ≫ (levelZeroCoverIso (f := f) W).hom
  have ha₀ : a₀ ≫ (towerFst f W).app 0 = (towerFst f V).app 0 := by
    rw [Category.assoc, Category.assoc, levelZeroCoverIso_hom_fst,
      ← Category.assoc g₀.hom.left, Over.w g₀.hom, ← levelZeroCoverIso_hom_fst,
      Iso.inv_hom_id_assoc]
  have : ∀ n, Etale ((towerFst f W).app n) := etale_towerFst_app f W
  let g : towerSys f V ⟶ towerSys f W :=
    AdicThickeningSystem.liftOfEtale (towerFst f V) (towerFst f W) a₀ ha₀
  have hgn (n : ℕ) : letI := isLocalRing_quotient_pow_succ hf n
      g.app n ≫ (levelCover hf n W).obj.hom = (levelCover hf n V).obj.hom := by
    change g.app n ≫ ((towerFst f W).app n ≫ (levelBaseIso hf n).inv) =
      (towerFst f V).app n ≫ (levelBaseIso hf n).inv
    rw [← Category.assoc, AdicThickeningSystem.liftOfEtale_app_comp]
  -- Extract compatible global coordinates at every level `n` and lift to `A`.
  have hfinV : letI := sectionsAlgebra A V; Module.Finite A Γ(V.obj.left, ⊤) :=
    finite_sections_puncturedSpectrum hdepthA V
  have hfinW : letI := sectionsAlgebra A W; Module.Finite A Γ(W.obj.left, ⊤) :=
    finite_sections_puncturedSpectrum hdepthA W
  let := sectionsAlgebra A V
  let := sectionsAlgebra A W
  obtain ⟨r, s, π, φ, hπ, hφπ⟩ :=
    exists_finPresentation (A := A) (M := Module.Dual A (Γ(W.obj.left, ⊤) →ₗ[A] Γ(V.obj.left, ⊤)))
  let v (n : ℕ) : Fin r → A ⧸ Ideal.span {f} ^ (n + 1) :=
    letI := isLocalRing_quotient_pow_succ hf n
    (towerPullback hf hf0 hdepth V W n).coords hdepthA hfinV hfinW π
      (secLinearMapOfHom (levelCover hf n V) (levelCover hf n W) (g.app n) (hgn n))
  have hv_compat (i : Fin r) (n : ℕ) :
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := Ideal.span {f}) (Nat.le_succ (n + 1)))
        (v (n + 1) i) = v n i := by
    let := isLocalRing_quotient_pow_succ hf (n + 1)
    let := isLocalRing_quotient_pow_succ hf n
    have hmap := CoverPullbackHom.coords_map hdepthA hfinV hfinW
      (towerStep hf hf0 hdepth V W n) π
      (secLinearMapOfHom (levelCover hf (n + 1) V) (levelCover hf (n + 1) W)
        (g.app (n + 1)) (hgn (n + 1)))
      (secLinearMapOfHom (levelCover hf n V) (levelCover hf n W) (g.app n) (hgn n))
      (fun c ↦ ?_) i
    · exact hmap.symm
    · change (g.app n).appTop ((towerSndApp f W n).appTop c) =
        ((towerSys f V).ι n).appTop ((g.app (n + 1)).appTop ((towerSndApp f W (n + 1)).appTop c))
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
        g.naturality n, Category.assoc, towerSndApp_naturality]
  choose a ha using fun i ↦ exists_of_compatible_quotientPowSucc (fun n ↦ v n i) (hv_compat i)
  -- The lifted coordinate vector `a` satisfies the presentation equations of `φ`, giving `ψ`.
  let Pid := CoverPullback.id hdepthA V W
  have hrel (j : Fin s) : ∑ i : Fin r, φ (Pi.single j 1) i * a i = 0 := by
    refine eq_zero_of_forall_mk_pow_succ_eq_zero (I := Ideal.span {f}) fun n ↦ ?_
    let := isLocalRing_quotient_pow_succ hf n
    rw [map_sum]
    have hn := ((towerPullback hf hf0 hdepth V W n).coords_exact hdepthA hfinV hfinW hπ hφπ).2
      (v n) |>.mp
      ⟨secLinearMapOfHom (levelCover hf n V) (levelCover hf n W) (g.app n) (hgn n), rfl⟩ j
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans hn
    rw [map_mul, ha i n]
    rfl
  obtain ⟨ψ₀, hψcoords⟩ := ((Pid.coords_exact hdepthA hfinV hfinW hπ hφπ).2 a).mpr hrel
  let ψ : Γ(W.obj.left, ⊤) →ₗ[A] Γ(V.obj.left, ⊤) := ψ₀
  -- Compatibility of `ψ` with `g.app n` on pulled-back sections at every level `n`.
  have hψcompat (n : ℕ) (c : Γ(W.obj.left, ⊤)) :
      (g.app n).appTop ((towerSndApp f W n).appTop c) =
        (towerSndApp f V n).appTop (ψ c) := by
    let := isLocalRing_quotient_pow_succ hf n
    let Pn := towerPullback hf hf0 hdepth V W n
    exact CoverPullbackHom.compat_of_coords_eq hdepthA hfinV hfinW
      (CoverPullbackHom.fromId hdepthA Pn) hπ hφπ ψ
      (secLinearMapOfHom Pn.V' Pn.W' (g.app n) (hgn n))
      (fun i ↦ by
        change v n i = Ideal.Quotient.mk (Ideal.span {f} ^ (n + 1)) (Pid.coords _ _ _ π ψ₀ i)
        rw [hψcoords, ha i n]) c
  -- `ψ` preserves `1` and multiplication by separatedness of `Γ(V, 𝒪)`.
  have hψ1 : ψ 1 = 1 := by
    rw [← sub_eq_zero]
    refine sec_eq_zero_of_forall_tower_eq_zero hf hf0 hdepth V fun n ↦ ?_
    rw [map_sub, ← hψcompat n 1, map_one, map_one, map_one, sub_self]
  have hψmul (c₁ c₂ : Γ(W.obj.left, ⊤)) : ψ (c₁ * c₂) = ψ c₁ * ψ c₂ := by
    rw [← sub_eq_zero]
    refine sec_eq_zero_of_forall_tower_eq_zero hf hf0 hdepth V fun n ↦ ?_
    rw [map_sub, ← hψcompat n (c₁ * c₂), map_mul, map_mul, map_mul, hψcompat n c₁,
      hψcompat n c₂, sub_self]
  let ψRing : Γ(W.obj.left, ⊤) ⟶ Γ(V.obj.left, ⊤) :=
    CommRingCat.ofHom
      { toFun := ψ
        map_one' := hψ1
        map_mul' := hψmul
        map_zero' := map_zero ψ
        map_add' := map_add ψ }
  have hψbase : (W.obj.hom ≫ (puncturedSpectrum A).ι).appTop ≫ ψRing =
      (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop := by
    ext x
    let rA : A := (Scheme.ΓSpecIso (.of A)).hom x
    have hx : (Scheme.ΓSpecIso (.of A)).inv rA = x := by
      change ((Scheme.ΓSpecIso (.of A)).hom ≫ (Scheme.ΓSpecIso (.of A)).inv) x = x; simp
    rw [← hx]
    change ψ (algebraMap A Γ(W.obj.left, ⊤) rA) = algebraMap A Γ(V.obj.left, ⊤) rA
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hψ1, ← Algebra.algebraMap_eq_smul_one]
  -- Construct `G : V ⟶ W` from `ψRing` and check `(restrictPuncturedQuotient I).map G = g₀`.
  obtain ⟨G_left, ⟨hGhom, hGapp⟩, _⟩ := existsUnique_hom_puncturedSpectrum_of_appTop A hdepthA
    V.obj.hom W.obj.hom ψRing hψbase
  let G : V ⟶ W := ObjectProperty.homMk (Over.homMk G_left hGhom)
  refine ⟨G, ?_⟩
  let := isLocalRing_quotient_pow_succ hf 0
  let P0 := towerPullback hf hf0 hdepth V W 0
  have hGw0 : (towerMap f G).app 0 ≫ P0.W'.obj.hom = P0.V'.obj.hom := by
    change (towerMap f G).app 0 ≫ ((towerFst f W).app 0 ≫ (levelBaseIso hf 0).inv) =
      (towerFst f V).app 0 ≫ (levelBaseIso hf 0).inv
    rw [← Category.assoc, ← AdicThickeningSystem.comp_app, towerMap_comp_fst]
  have hlin0 : secLinearMapOfHom P0.V' P0.W' ((towerMap f G).app 0) hGw0 =
      secLinearMapOfHom P0.V' P0.W' (g.app 0) (hgn 0) := by
    refine P0.linearMap_eq_of_eq_on_base hdepthA fun c ↦ ?_
    change ((towerMap f G).app 0).appTop ((towerSndApp f W 0).appTop c) =
      (g.app 0).appTop ((towerSndApp f W 0).appTop c)
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, towerMap_app_comp_snd,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hψcompat 0 c]
    exact congrArg ((towerSndApp f V 0).appTop) (congrArg (fun h ↦ h c) hGapp)
  have happ0 : ((towerMap f G).app 0).appTop = (g.app 0).appTop := by
    let := sectionsAlgebra (A ⧸ Ideal.span {f} ^ 1) P0.V'
    let := sectionsAlgebra (A ⧸ Ideal.span {f} ^ 1) P0.W'
    ext x
    exact congrArg (fun l : Γ(P0.W'.obj.left, ⊤) →ₗ[A ⧸ Ideal.span {f} ^ 1] Γ(P0.V'.obj.left, ⊤)
      ↦ l x) hlin0
  have h0eq : (towerMap f G).app 0 = g.app 0 := by
    let hG0 : P0.V'.obj.left ⟶ P0.W'.obj.left := (towerMap f G).app 0
    have hGw0' : hG0 ≫ P0.W'.obj.hom = P0.V'.obj.hom := hGw0
    have huniq0 := existsUnique_hom_puncturedSpectrum_of_appTop (A ⧸ Ideal.span {f} ^ 1)
      (two_le_depth_quotient_pow_succ hdepth hf hf0 0) P0.V'.obj.hom P0.W'.obj.hom hG0.appTop
      (by rw [← Scheme.Hom.comp_appTop, ← Category.assoc, hGw0'])
    exact huniq0.unique ⟨hGw0', rfl⟩ ⟨hgn 0, happ0.symm⟩
  have hleft0 : ((restrictPuncturedQuotient (Ideal.span {f})).map G).hom.left = g₀.hom.left := by
    rw [← cancel_mono (levelZeroCoverIso (f := f) W).hom, ← levelZeroCoverIso_naturality, h0eq,
      AdicThickeningSystem.liftOfEtale_app_zero]
    simp [a₀]
  exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext hleft0)

/-- **Local Lefschetz extension theorem.** Let `A` be a Noetherian integrally closed local domain
of depth at least three, and let `f ∈ A` be an element such that `A ⧸ (f)` is local and `A` is
`(f)`-adically complete. A finite étale cover of the punctured spectrum of `A` extends to `Spec A`
if and only if its restriction to the punctured spectrum of `A ⧸ (f)` extends to `Spec (A ⧸ (f))`.
-/
@[stacks 0BLM "integrally closed complete local domain case"]
theorem extends_iff_extends_quotient_span_singleton
    (hdepth : 3 ≤ depth (ModuleCat.of A A))
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (∃ Y : FiniteEtaleScheme (Spec (.of A)), Nonempty ((restrictPunctured A).obj Y ≅ V)) ↔
      ∃ Y₀ : FiniteEtaleScheme (Spec (.of (A ⧸ Ideal.span {f}))),
        Nonempty ((restrictPunctured (A ⧸ Ideal.span {f})).obj Y₀ ≅
          (restrictPuncturedQuotient (Ideal.span {f})).obj V) := by
  have := restrictPuncturedQuotient_faithful_of_three_le_depth (f := f) hdepth
  have := restrictPuncturedQuotient_full_of_three_le_depth (f := f) hdepth
  exact extends_iff_extends_quotient (Ideal.span {f}) V

/-- **Descent of purity from a hypersurface section.** Let `A` be a Noetherian integrally closed
local domain of depth at least three, and let `f ∈ A` be an element such that `A ⧸ (f)` is local
and `A` is `(f)`-adically complete. If purity holds for `A ⧸ (f)`, then purity holds for `A`. -/
theorem purityHolds_of_purityHolds_quotient_span_singleton
    (hdepth : 3 ≤ depth (ModuleCat.of A A))
    (h : PurityHolds (A ⧸ Ideal.span {f})) : PurityHolds A := by
  have := restrictPuncturedQuotient_faithful_of_three_le_depth (f := f) hdepth
  have := restrictPuncturedQuotient_full_of_three_le_depth (f := f) hdepth
  exact purityHolds_of_purityHolds_quotient (Ideal.span {f}) h

end Main

end TauCeti.IsLocalRing
