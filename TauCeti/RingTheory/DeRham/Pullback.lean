/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.MapSemilinear
public import TauCeti.RingTheory.DeRham.Basic
public import TauCeti.RingTheory.Kaehler.MapSemilinear

/-!
# Functorial pullback of algebraic differential forms and the de Rham complex

An `A`-algebra homomorphism `f : B →ₐ[A] C` induces a semilinear map
`KaehlerDifferential.mapSemilinear f : Ω[B⁄A] →ₛₗ[f.toRingHom] Ω[C⁄A]` sending `D b` to `D (f b)`.
Applying `exteriorPower.mapSemilinear` in every degree `n` produces the pullback of algebraic
differential forms `DeRham.pullback f n : Forms A B n →ₛₗ[f.toRingHom] Forms A C n` along with its
underlying `A`-linear map `DeRham.pullbackLinear f n : Forms A B n →ₗ[A] Forms A C n`.

Because no global `B`-algebra structure on `C` is installed, `pullback` applies uniformly to
arbitrary `A`-algebra homomorphisms — including endomorphisms `B →ₐ[A] B` such as Frobenius —
without conflicting with `Algebra.id`. Restricting scalars to `A` commutes with the exterior
derivative `DeRham.d`, respects the wedge product `DeRham.wedge`, and packages into a functorial
cochain map `DeRham.complexMap f : complex A B ⟶ complex A C`.

## Main definitions

* `TauCeti.DeRham.pullback f n`: the `f.toRingHom`-semilinear pullback
  `Forms A B n →ₛₗ[f.toRingHom] Forms A C n` along `f : B →ₐ[A] C`.
* `TauCeti.DeRham.pullbackLinear f n`: `pullback f n` viewed as an `A`-linear map
  `Forms A B n →ₗ[A] Forms A C n`.
* `TauCeti.DeRham.formsLinearEquiv e n`: the `A`-linear equivalence `Forms A B n ≃ₗ[A] Forms A C n`
  induced by `e : B ≃ₐ[A] C`.
* `TauCeti.DeRham.complexMap f`: the induced morphism `complex A B ⟶ complex A C` in
  `CochainComplex (ModuleCat A) ℕ`.
* `TauCeti.DeRham.complexIso e`: the induced isomorphism `complex A B ≅ complex A C` for
  `e : B ≃ₐ[A] C`.

## Main results

* `TauCeti.DeRham.pullback_elementary`: `pullback f n` sends `c • (D v₀ ∧ ⋯ ∧ D vₙ₋₁)` to
  `f c • (D (f v₀) ∧ ⋯ ∧ D (f vₙ₋₁))`.
* `TauCeti.DeRham.pullback_unique`: `pullback f n` is the unique `f.toRingHom`-semilinear map
  sending `D v₀ ∧ ⋯ ∧ D vₙ₋₁` to `D (f v₀) ∧ ⋯ ∧ D (f vₙ₋₁)`.
* `TauCeti.DeRham.pullback_d`: `pullback` commutes with `DeRham.d`.
* `TauCeti.DeRham.pullback_wedge`: `pullback` preserves `DeRham.wedge`.
* `TauCeti.DeRham.pullback_id`, `TauCeti.DeRham.pullback_comp`: functoriality on forms.
* `TauCeti.DeRham.complexMap_id`, `TauCeti.DeRham.complexMap_comp`: functoriality on the de Rham
  cochain complex.

## References

* [The Stacks Project, *The de Rham complex*, Section 10.132 (Tag 0FKF)](https://stacks.math.columbia.edu/tag/0FKF).
-/

public section

noncomputable section

universe u v w z

namespace TauCeti.DeRham

open KaehlerDifferential CategoryTheory

section Forms

variable {A : Type u} {B : Type v} {C : Type w} {E : Type z}
  [CommRing A] [CommRing B] [CommRing C] [CommRing E]
  [Algebra A B] [Algebra A C] [Algebra A E]

/-- Restrict an `f.toRingHom`-semilinear map out of `Forms A B n` to an `A`-linear map. -/
private def restrictSemilinear (f : B →ₐ[A] C) {n : ℕ}
    (φ : Forms A B n →ₛₗ[f.toRingHom] Forms A C n) :
    Forms A B n →ₗ[A] Forms A C n where
  toFun := φ
  map_add' := map_add φ
  map_smul' a ω := by
    rw [← IsScalarTower.algebraMap_smul B a ω, φ.map_smulₛₗ]
    change f (algebraMap A B a) • φ ω = a • φ ω
    rw [f.commutes, IsScalarTower.algebraMap_smul]

/-- **Functorial pullback of algebraic `n`-forms** along an `A`-algebra homomorphism
`f : B →ₐ[A] C`, defined as `exteriorPower.mapSemilinear n (KaehlerDifferential.mapSemilinear f)`.
-/
def pullback (f : B →ₐ[A] C) (n : ℕ) : Forms A B n →ₛₗ[f.toRingHom] Forms A C n :=
  exteriorPower.mapSemilinear n (KaehlerDifferential.mapSemilinear f)

/-- `pullback f n` viewed as an `A`-linear map `Forms A B n →ₗ[A] Forms A C n`. -/
def pullbackLinear (f : B →ₐ[A] C) (n : ℕ) : Forms A B n →ₗ[A] Forms A C n :=
  restrictSemilinear f (pullback f n)

@[simp]
theorem pullbackLinear_apply (f : B →ₐ[A] C) (n : ℕ) (ω : Forms A B n) :
    pullbackLinear f n ω = pullback f n ω :=
  (rfl)

@[simp]
theorem coe_pullback (f : B →ₐ[A] C) (n : ℕ) (ω : Forms A B n) :
    (pullback f n ω : _root_.ExteriorAlgebra C Ω[C⁄A]) =
      _root_.ExteriorAlgebra.mapSemilinear (KaehlerDifferential.mapSemilinear f) ω.1 :=
  exteriorPower.coe_mapSemilinear n (KaehlerDifferential.mapSemilinear f) ω

/-- Semilinearity of `pullback f n` over `B`-scalars, stated directly in terms of `f b`. -/
@[simp]
theorem pullback_smul (f : B →ₐ[A] C) (n : ℕ) (b : B) (ω : Forms A B n) :
    pullback f n (b • ω) = f b • pullback f n ω :=
  (pullback f n).map_smulₛₗ b ω

theorem pullback_base_smul (f : B →ₐ[A] C) (n : ℕ) (a : A) (ω : Forms A B n) :
    pullback f n (a • ω) = a • pullback f n ω :=
  (pullbackLinear f n).map_smul a ω

theorem pullback_add (f : B →ₐ[A] C) (n : ℕ) (ω₁ ω₂ : Forms A B n) :
    pullback f n (ω₁ + ω₂) = pullback f n ω₁ + pullback f n ω₂ :=
  map_add (pullback f n) ω₁ ω₂

@[simp]
theorem pullback_ιMulti (f : B →ₐ[A] C) (n : ℕ) (w : Fin n → Ω[B⁄A]) :
    pullback f n (exteriorPower.ιMulti B n w) =
      exteriorPower.ιMulti C n (KaehlerDifferential.mapSemilinear f ∘ w) :=
  exteriorPower.mapSemilinear_apply_ιMulti n (KaehlerDifferential.mapSemilinear f) w

@[simp]
theorem pullback_ιMulti_D (f : B →ₐ[A] C) (n : ℕ) (v : Fin n → B) :
    pullback f n (exteriorPower.ιMulti B n (D A B ∘ v)) =
      exteriorPower.ιMulti C n (D A C ∘ f ∘ v) := by
  rw [pullback_ιMulti]
  congr 1
  ext i
  exact KaehlerDifferential.mapSemilinear_D f (v i)

/-- `pullback f n` sends an elementary `n`-form `c • (D v₀ ∧ ⋯ ∧ D vₙ₋₁)` to
`f c • (D (f v₀) ∧ ⋯ ∧ D (f vₙ₋₁))`. -/
@[simp]
theorem pullback_elementary (f : B →ₐ[A] C) (n : ℕ) (c : B) (v : Fin n → B) :
    pullback f n (elementary A B n c v) = elementary A C n (f c) (f ∘ v) := by
  rw [elementary_def, pullback_smul, pullback_ιMulti_D, elementary_def]

@[simp]
theorem pullback_zeroForm (f : B →ₐ[A] C) (b : B) :
    pullback f 0 (zeroForm A B b) = zeroForm A C (f b) := by
  apply (exteriorPower.zeroEquiv C Ω[C⁄A]).injective
  rw [pullback, exteriorPower.zeroEquiv_mapSemilinear, zeroEquiv_zeroForm, zeroEquiv_zeroForm]
  rfl

@[simp]
theorem zeroEquiv_pullback (f : B →ₐ[A] C) (ω : Forms A B 0) :
    exteriorPower.zeroEquiv C Ω[C⁄A] (pullback f 0 ω) =
      f (exteriorPower.zeroEquiv B Ω[B⁄A] ω) :=
  exteriorPower.zeroEquiv_mapSemilinear (KaehlerDifferential.mapSemilinear f) ω

@[simp]
theorem oneEquiv_pullback (f : B →ₐ[A] C) (ω : Forms A B 1) :
    exteriorPower.oneEquiv C Ω[C⁄A] (pullback f 1 ω) =
      KaehlerDifferential.mapSemilinear f (exteriorPower.oneEquiv B Ω[B⁄A] ω) :=
  exteriorPower.oneEquiv_mapSemilinear (KaehlerDifferential.mapSemilinear f) ω

@[simp]
theorem pullback_oneForm (f : B →ₐ[A] C) (ω : Ω[B⁄A]) :
    pullback f 1 (oneForm A B ω) = oneForm A C (KaehlerDifferential.mapSemilinear f ω) := by
  apply (exteriorPower.oneEquiv C Ω[C⁄A]).injective
  rw [oneEquiv_pullback, oneEquiv_oneForm, oneEquiv_oneForm]

/-- **Uniqueness of `DeRham.pullback`.** Any `f.toRingHom`-semilinear map out of `Forms A B n` that
sends `D v₀ ∧ ⋯ ∧ D vₙ₋₁` to `D (f v₀) ∧ ⋯ ∧ D (f vₙ₋₁)` for every `v : Fin n → B` equals
`pullback f n`. -/
theorem pullback_unique (f : B →ₐ[A] C) {n : ℕ}
    (φ : Forms A B n →ₛₗ[f.toRingHom] Forms A C n)
    (hφ : ∀ v : Fin n → B,
      φ (exteriorPower.ιMulti B n (D A B ∘ v)) = exteriorPower.ιMulti C n (D A C ∘ f ∘ v)) :
    φ = pullback f n := by
  have hlin : restrictSemilinear f φ = pullbackLinear f n :=
    ext_of_elementary fun c v ↦ by
      change φ (elementary A B n c v) = pullback f n (elementary A B n c v)
      rw [elementary_def, φ.map_smulₛₗ, hφ v, pullback_smul, pullback_ιMulti_D]
      rfl
  exact LinearMap.ext fun ω ↦ LinearMap.congr_fun hlin ω

/-- `pullbackLinear f` commutes with the algebraic exterior derivative `DeRham.d`. -/
theorem pullbackLinear_comp_d (f : B →ₐ[A] C) (n : ℕ) :
    (pullbackLinear f (n + 1)).comp (d A B n) = (d A C n).comp (pullbackLinear f n) := by
  refine ext_of_elementary fun c v ↦ ?_
  have hcons : f ∘ Fin.cons c v = Fin.cons (f c) (f ∘ v) := by
    ext i
    cases i using Fin.cases <;> rfl
  rw [LinearMap.comp_apply, LinearMap.comp_apply, pullbackLinear_apply, pullbackLinear_apply,
    d_elementary, pullback_elementary, map_one, hcons, pullback_elementary, d_elementary]

/-- `pullback f` commutes with the algebraic exterior derivative `DeRham.d`. -/
@[simp]
theorem pullback_d (f : B →ₐ[A] C) (n : ℕ) (ω : Forms A B n) :
    pullback f (n + 1) (d A B n ω) = d A C n (pullback f n ω) :=
  LinearMap.congr_fun (pullbackLinear_comp_d f n) ω

/-- `pullback f` preserves wedge products of algebraic differential forms. -/
@[simp]
theorem pullback_wedge (f : B →ₐ[A] C) {m n : ℕ} (α : Forms A B m) (β : Forms A B n) :
    pullback f (m + n) (wedge A B α β) =
      wedge A C (pullback f m α) (pullback f n β) := by
  rw [wedge_def, wedge_def, pullback, pullback, pullback, exteriorPower.mapSemilinear_wedge]

/-- Pulling back along the identity `A`-algebra homomorphism is the identity `B`-linear map. -/
theorem pullback_id (n : ℕ) :
    (pullback (AlgHom.id A B) n : Forms A B n →ₗ[B] Forms A B n) = LinearMap.id := by
  refine exteriorPower.semilinearMap_ext fun w ↦ ?_
  change pullback (AlgHom.id A B) n (exteriorPower.ιMulti B n w) = exteriorPower.ιMulti B n w
  rw [pullback_ιMulti]
  congr 1
  ext i
  exact KaehlerDifferential.mapSemilinear_id_apply (w i)

@[simp]
theorem pullback_id_apply (n : ℕ) (ω : Forms A B n) :
    pullback (AlgHom.id A B) n ω = ω :=
  DFunLike.congr_fun (pullback_id (A := A) (B := B) n) ω

@[simp]
theorem pullbackLinear_id (n : ℕ) :
    pullbackLinear (AlgHom.id A B) n = LinearMap.id :=
  LinearMap.ext fun ω ↦ pullback_id_apply n ω

/-- `pullback` is functorial with respect to composition of `A`-algebra homomorphisms. -/
theorem pullback_comp (g : C →ₐ[A] E) (f : B →ₐ[A] C) (n : ℕ) :
    pullback (g.comp f) n = (pullback g n).comp (pullback f n) := by
  rw [pullback, KaehlerDifferential.mapSemilinear_comp, exteriorPower.mapSemilinear_comp]
  rfl

@[simp]
theorem pullback_comp_apply (g : C →ₐ[A] E) (f : B →ₐ[A] C) (n : ℕ) (ω : Forms A B n) :
    pullback (g.comp f) n ω = pullback g n (pullback f n ω) :=
  DFunLike.congr_fun (pullback_comp g f n) ω

@[simp]
theorem pullbackLinear_comp (g : C →ₐ[A] E) (f : B →ₐ[A] C) (n : ℕ) :
    pullbackLinear (g.comp f) n = (pullbackLinear g n).comp (pullbackLinear f n) :=
  LinearMap.ext fun ω ↦ pullback_comp_apply g f n ω

@[simp]
theorem pullback_apply_symm_apply (e : B ≃ₐ[A] C) (n : ℕ) (ω : Forms A C n) :
    pullback e.toAlgHom n (pullback e.symm.toAlgHom n ω) = ω := by
  rw [← pullback_comp_apply, AlgEquiv.comp_symm, pullback_id_apply]

@[simp]
theorem pullback_symm_apply_apply (e : B ≃ₐ[A] C) (n : ℕ) (ω : Forms A B n) :
    pullback e.symm.toAlgHom n (pullback e.toAlgHom n ω) = ω :=
  pullback_apply_symm_apply e.symm n ω

/-- An `A`-algebra isomorphism `e : B ≃ₐ[A] C` induces an `A`-linear equivalence on `n`-forms. -/
def formsLinearEquiv (e : B ≃ₐ[A] C) (n : ℕ) : Forms A B n ≃ₗ[A] Forms A C n :=
  LinearEquiv.ofLinearMap (pullbackLinear e.toAlgHom n) (pullbackLinear e.symm.toAlgHom n)
    (by rw [← pullbackLinear_comp, AlgEquiv.comp_symm, pullbackLinear_id])
    (by rw [← pullbackLinear_comp, AlgEquiv.symm_comp, pullbackLinear_id])

@[simp]
theorem formsLinearEquiv_apply (e : B ≃ₐ[A] C) (n : ℕ) (ω : Forms A B n) :
    formsLinearEquiv e n ω = pullback e.toAlgHom n ω :=
  (rfl)

@[simp]
theorem formsLinearEquiv_symm (e : B ≃ₐ[A] C) (n : ℕ) :
    (formsLinearEquiv e n).symm = formsLinearEquiv e.symm n :=
  LinearEquiv.ext fun _ ↦ rfl

end Forms

/-! ### Functoriality of the algebraic de Rham cochain complex -/

section Complex

variable {A : Type u} {B C E : Type v}
  [CommRing A] [CommRing B] [CommRing C] [CommRing E]
  [Algebra A B] [Algebra A C] [Algebra A E]

/-- **Functoriality of the algebraic de Rham complex.** An `A`-algebra homomorphism `f : B →ₐ[A] C`
induces a cochain map `complex A B ⟶ complex A C` in `CochainComplex (ModuleCat A) ℕ` whose degree
`n` component is `pullbackLinear f n`. -/
@[expose]
def complexMap (f : B →ₐ[A] C) : complex A B ⟶ complex A C where
  f n := ModuleCat.ofHom (pullbackLinear f n)
  comm' := by
    rintro i _ rfl
    rw [complex_d, complex_d]
    apply ModuleCat.hom_ext
    ext ω
    exact (pullback_d f i ω).symm

@[simp]
theorem complexMap_f (f : B →ₐ[A] C) (n : ℕ) :
    (complexMap f).f n = ModuleCat.ofHom (pullbackLinear f n) :=
  (rfl)

theorem complexMap_f_apply (f : B →ₐ[A] C) (n : ℕ) (ω : Forms A B n) :
    ((complexMap f).f n).hom ω = pullback f n ω :=
  (rfl)

@[simp]
theorem complexMap_id (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    complexMap (AlgHom.id A B) = 𝟙 (complex A B) :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    ModuleCat.hom_ext (LinearMap.ext fun ω ↦ pullback_id_apply n ω)

@[simp]
theorem complexMap_comp (g : C →ₐ[A] E) (f : B →ₐ[A] C) :
    complexMap (g.comp f) = complexMap f ≫ complexMap g :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    ModuleCat.hom_ext (LinearMap.ext fun ω ↦ pullback_comp_apply g f n ω)

/-- An `A`-algebra isomorphism `e : B ≃ₐ[A] C` induces an isomorphism of algebraic de Rham cochain
complexes `complex A B ≅ complex A C`. -/
@[expose]
def complexIso (e : B ≃ₐ[A] C) : complex A B ≅ complex A C where
  hom := complexMap e.toAlgHom
  inv := complexMap e.symm.toAlgHom
  hom_inv_id := by rw [← complexMap_comp, AlgEquiv.symm_comp, complexMap_id]
  inv_hom_id := by rw [← complexMap_comp, AlgEquiv.comp_symm, complexMap_id]

@[simp]
theorem complexIso_hom (e : B ≃ₐ[A] C) :
    (complexIso e).hom = complexMap e.toAlgHom :=
  (rfl)

@[simp]
theorem complexIso_inv (e : B ≃ₐ[A] C) :
    (complexIso e).inv = complexMap e.symm.toAlgHom :=
  (rfl)

end Complex

end TauCeti.DeRham
