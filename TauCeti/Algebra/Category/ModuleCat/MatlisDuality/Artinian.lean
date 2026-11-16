/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Artinian
public import TauCeti.RingTheory.MatlisDuality.Completion
import TauCeti.Algebra.Module.Injective.Hom

/-!
# Categorical Matlis duality for Artinian modules over Noetherian local rings

Let `R` and `S` be rings and `E` an `(R, S)`-compatible abelian group (`[Module R E]`,
`[Module S E]`, `[SMulCommClass R S E]`). Precomposition into `E` defines a contravariant additive
functor `ModuleCat.linearMapFunctor R S E : (ModuleCat R)ᵒᵖ ⥤ ModuleCat S` sending `M` to
`ModuleCat.linearMapObj R S E M`, whose underlying `S`-module is `M →ₗ[R] E`. When `E` is
injective over `R`, it sends opposite short exact sequences to short exact sequences
(`CategoryTheory.ShortComplex.ShortExact.map_op_linearMapFunctor`). When the two scalar actions
commute symmetrically (`[SMulCommClass S R E]`), evaluation restricts `linearMapFunctor` to an
anti-equivalence `ModuleCat.linearMapDualityOn` between any full subcategories of `ModuleCat R` and
`ModuleCat S` exchanged by `Hom(-, E)` on which evaluation is bijective.

Specializing to an injective hull `ι : κ → E` of the residue field of a Noetherian local ring
`R` gives the two categorical Matlis dualities for Artinian modules:

* `TauCeti.IsInjectiveEnvelope.artinianMatlisDuality`: when `R` is complete, the anti-equivalence
  `(ModuleCat.isArtinian R).FullSubcategoryᵒᵖ ≌ FGModuleCat R` (Stacks Tag 08Z9).
* `TauCeti.IsInjectiveEnvelope.artinianMatlisDualityAdicCompletion`: without completeness, the
  anti-equivalence `(ModuleCat.isArtinian R).FullSubcategoryᵒᵖ ≌ FGModuleCat R̂` where
  `R̂ = AdicCompletion (maximalIdeal R) R` (Stacks Tag 0EGL).

## References

* The Stacks Project, Section 47.7, Matlis duality (Tag 08Z1): Proposition 47.7.8 (08Z9) and
  Remark 47.7.9 (0EGL).
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

open CategoryTheory Opposite

universe u t v w

namespace ModuleCat

section Functor

variable (R : Type u) [Ring R] (S : Type t) [Ring S] (E : Type v) [AddCommGroup E]
  [Module R E] [Module S E] [SMulCommClass R S E]

/-- The bundled `S`-module of `R`-linear maps `M →ₗ[R] E`. -/
def linearMapObj (M : ModuleCat.{w} R) : ModuleCat.{max w v} S :=
  ModuleCat.of S (M →ₗ[R] E)

/-- Identification of the bundled dual `linearMapObj R S E M` with `M →ₗ[R] E`. -/
def linearMapObjEquiv (M : ModuleCat.{w} R) : linearMapObj R S E M ≃ₗ[S] (M →ₗ[R] E) :=
  LinearEquiv.refl _ _

/-- Precomposition into `E` as a morphism of bundled `S`-modules. -/
def linearMapMap {M M' : ModuleCat.{w} R} (g : M ⟶ M') :
    linearMapObj R S E M' ⟶ linearMapObj R S E M :=
  ModuleCat.ofHom ((linearMapObjEquiv R S E M).symm.toLinearMap ∘ₗ g.hom.lcomp S E ∘ₗ
    (linearMapObjEquiv R S E M').toLinearMap)

@[simp]
theorem linearMapObjEquiv_map_apply {M M' : ModuleCat.{w} R} (g : M ⟶ M')
    (φ : linearMapObj R S E M') (x : M) :
    linearMapObjEquiv R S E M (linearMapMap R S E g φ) x =
      linearMapObjEquiv R S E M' φ (g x) := (rfl)

/-- The contravariant `Hom` functor `(ModuleCat R)ᵒᵖ ⥤ ModuleCat S` sending `M` to `M →ₗ[R] E`
with its post-multiplication `S`-module structure. -/
@[expose]
def linearMapFunctor : (ModuleCat.{w} R)ᵒᵖ ⥤ ModuleCat.{max w v} S where
  obj M := linearMapObj R S E M.unop
  map g := linearMapMap R S E g.unop
  map_id M := by
    ext φ
    apply (linearMapObjEquiv R S E M.unop).injective
    ext x
    simp
  map_comp _ _ := by
    ext φ
    apply (linearMapObjEquiv R S E _).injective
    ext x
    simp

@[simp]
theorem linearMapFunctor_obj (M : (ModuleCat.{w} R)ᵒᵖ) :
    (linearMapFunctor R S E).obj M = linearMapObj R S E M.unop :=
  rfl

@[simp]
theorem linearMapFunctor_map {M M' : (ModuleCat.{w} R)ᵒᵖ} (g : M ⟶ M') :
    (linearMapFunctor R S E).map g = linearMapMap R S E g.unop :=
  rfl

theorem linearMapMap_add {M M' : ModuleCat.{w} R} (g h : M ⟶ M') :
    linearMapMap R S E (g + h) = linearMapMap R S E g + linearMapMap R S E h := by
  ext φ
  apply (linearMapObjEquiv R S E _).injective
  ext x
  refine (linearMapObjEquiv_map_apply R S E (g + h) φ x).trans ?_
  simp [ModuleCat.hom_add, map_add]

instance : (linearMapFunctor.{u, t, v, w} R S E).Additive where
  map_add := linearMapMap_add R S E _ _

end Functor

section Exact

/-- When `E` is injective over `R`, `ModuleCat.linearMapFunctor R S E` turns a short exact sequence
in `ModuleCat R` into a short exact sequence in `ModuleCat S`. -/
theorem _root_.CategoryTheory.ShortComplex.ShortExact.map_op_linearMapFunctor
    {R : Type u} [Ring R] (S : Type t) [Ring S] (E : Type v) [AddCommGroup E]
    [Module R E] [Module S E] [SMulCommClass R S E] [Small.{v} R] [Module.Injective R E]
    {C : ShortComplex (ModuleCat.{w} R)} (hC : C.ShortExact) :
    (C.op.map (linearMapFunctor R S E)).ShortExact := by
  suffices (ShortComplex.mk (linearMapMap R S E C.g) (linearMapMap R S E C.f)
      (C.op.map (linearMapFunctor R S E)).zero).ShortExact from this
  refine
    { exact := (ShortComplex.moduleCat_exact_iff _).mpr fun φ hφ ↦ by
        let φ' : C.X₂ →ₗ[R] E := linearMapObjEquiv R S E C.X₂ φ
        have hker : LinearMap.ker C.g.hom ≤ LinearMap.ker φ' := by
          rw [← hC.exact.moduleCat_range_eq_ker, LinearMap.range_le_ker_iff]
          ext x
          have hx := congrArg (fun ψ ↦ linearMapObjEquiv R S E C.X₁ ψ x) hφ
          simpa [φ'] using hx
        obtain ⟨ψ', hψ'⟩ := (LinearMap.exists_comp_eq_iff_ker_le C.g.hom φ').mpr hker
        refine ⟨(linearMapObjEquiv R S E C.X₃).symm ψ', ?_⟩
        apply (linearMapObjEquiv R S E C.X₂).injective
        ext x
        simpa [φ'] using LinearMap.congr_fun hψ' x
      mono_f := (ModuleCat.mono_iff_injective _).mpr fun ψ₁ ψ₂ h ↦ by
        apply (linearMapObjEquiv R S E C.X₃).injective
        ext x
        obtain ⟨y, rfl⟩ := hC.moduleCat_surjective_g x
        simpa using congrArg (fun φ ↦ linearMapObjEquiv R S E C.X₂ φ y) h
      epi_g := (ModuleCat.epi_iff_surjective _).mpr fun χ ↦ by
        obtain ⟨φ', hφ'⟩ := Module.Injective.extension_property R E _ _ C.f.hom
          hC.moduleCat_injective_f (linearMapObjEquiv R S E C.X₁ χ)
        refine ⟨(linearMapObjEquiv R S E C.X₂).symm φ', ?_⟩
        apply (linearMapObjEquiv R S E C.X₁).injective
        ext x
        simpa using LinearMap.congr_fun hφ' x }

end Exact

section Eval

variable (R : Type u) [Ring R] (S : Type t) [Ring S] (E : Type v) [AddCommGroup E]
  [Module R E] [Module S E] [SMulCommClass R S E] [SMulCommClass S R E]

/-- Canonical evaluation `M ⟶ Hom_S(Hom_R(M, E), E)` as a morphism in `ModuleCat R`. -/
def linearMapEval (M : ModuleCat.{max v w} R) :
    M ⟶ linearMapObj S R E (linearMapObj R S E M) :=
  ModuleCat.ofHom
    { toFun := fun m ↦ (linearMapObjEquiv S R E _).symm
        { toFun := fun φ ↦ linearMapObjEquiv R S E M φ m
          map_add' := fun _ _ ↦ by simp
          map_smul' := fun _ _ ↦ by simp }
      map_add' := fun x₁ x₂ ↦ by
        apply (linearMapObjEquiv S R E _).injective
        ext φ
        exact (linearMapObjEquiv R S E M φ).map_add x₁ x₂
      map_smul' := fun r m ↦ by
        apply (linearMapObjEquiv S R E _).injective
        ext φ
        exact (linearMapObjEquiv R S E M φ).map_smul r m }

@[simp]
theorem linearMapObjEquiv_eval_apply (M : ModuleCat.{max v w} R) (m : M)
    (φ : linearMapObj R S E M) :
    linearMapObjEquiv S R E _ (linearMapEval R S E M m) φ =
      linearMapObjEquiv R S E M φ m :=
  (rfl)

/-- Evaluation `M ⟶ Hom_S(Hom_R(M, E), E)` is natural in `M`. -/
theorem linearMapEval_naturality {M M' : ModuleCat.{max v w} R} (g : M ⟶ M') :
    g ≫ linearMapEval R S E M' =
      linearMapEval R S E M ≫ linearMapMap S R E (linearMapMap R S E g) := by
  ext m
  apply (linearMapObjEquiv S R E _).injective
  ext φ
  simp

variable {R S E}

/-- Transfer bijectivity of unbundled evaluation `M → ((M →ₗ[R] E) →ₗ[S] E)` to bundled
`linearMapEval`. -/
theorem bijective_linearMapEval_of_bijective {M : ModuleCat.{max v w} R}
    (ev : M → (M →ₗ[R] E) →ₗ[S] E) (hev : ∀ m (g : M →ₗ[R] E), ev m g = g m)
    (hb : Function.Bijective ev) :
    Function.Bijective (linearMapEval R S E M) := by
  let c : ((M →ₗ[R] E) →ₗ[S] E) ≃ linearMapObj S R E (linearMapObj R S E M) :=
    { toFun := fun ψ ↦ (linearMapObjEquiv S R E _).symm
        (ψ.comp (linearMapObjEquiv R S E M).toLinearMap)
      invFun := fun χ ↦ (linearMapObjEquiv S R E _ χ).comp
        (linearMapObjEquiv R S E M).symm.toLinearMap
      left_inv := fun ψ ↦ by ext f; simp
      right_inv := fun χ ↦ by apply (linearMapObjEquiv S R E _).injective; ext φ; simp }
  have heq : (linearMapEval R S E M : M → _) = c ∘ ev := by
    ext m
    apply (linearMapObjEquiv S R E _).injective
    ext φ
    simp [c, hev]
  rw [heq]
  exact c.bijective.comp hb

/-- When evaluation on `M` is bijective, it upgrades to an isomorphism in `ModuleCat R`. -/
def linearMapEvalIso {M : ModuleCat.{max v w} R}
    (hM : Function.Bijective (linearMapEval R S E M)) :
    M ≅ linearMapObj S R E (linearMapObj R S E M) :=
  (LinearEquiv.ofBijective (linearMapEval R S E M).hom hM).toModuleIso

@[simp]
theorem linearMapEvalIso_hom {M : ModuleCat.{max v w} R}
    (hM : Function.Bijective (linearMapEval R S E M)) :
    (linearMapEvalIso hM).hom = linearMapEval R S E M :=
  (rfl)

/-- Naturality of `linearMapEvalIso` with respect to morphisms in `ModuleCat R`. -/
theorem linearMapEvalIso_hom_naturality {M M' : ModuleCat.{max v w} R} (g : M ⟶ M')
    (hM : Function.Bijective (linearMapEval R S E M))
    (hM' : Function.Bijective (linearMapEval R S E M')) :
    g ≫ (linearMapEvalIso hM').hom =
      (linearMapEvalIso hM).hom ≫ linearMapMap S R E (linearMapMap R S E g) :=
  linearMapEval_naturality R S E g

/-- Triangle identity for `linearMapEval`: evaluation on `Hom_R(M, E)` is precomposition with the
inverse of evaluation on `M`. -/
theorem linearMapEval_linearMapObj {M : ModuleCat.{max v w} R}
    (hM : Function.Bijective (linearMapEval R S E M)) :
    linearMapEval S R E (linearMapObj R S E M) =
      linearMapMap R S E (linearMapEvalIso hM).inv := by
  ext φ
  apply (linearMapObjEquiv R S E _).injective
  ext ψ
  obtain ⟨m, rfl⟩ : ∃ m, (linearMapEvalIso hM).hom m = ψ :=
    ⟨(linearMapEvalIso hM).inv ψ, (linearMapEvalIso hM).inv_hom_id_apply ψ⟩
  simp only [linearMapEvalIso_hom, linearMapObjEquiv_eval_apply, linearMapObjEquiv_map_apply]
  rw [← linearMapEvalIso_hom hM, (linearMapEvalIso hM).hom_inv_id_apply]

/-- Triangle identity for `linearMapEvalIso`. -/
theorem linearMapEvalIso_linearMapObj_hom {M : ModuleCat.{max v w} R}
    (hM : Function.Bijective (linearMapEval R S E M))
    (hM' : Function.Bijective (linearMapEval S R E (linearMapObj R S E M))) :
    (linearMapEvalIso hM').hom = linearMapMap R S E (linearMapEvalIso hM).inv :=
  linearMapEval_linearMapObj hM

/-- **Contravariant `Hom` duality on full subcategories.** If `Hom_R(-, E)` and `Hom_S(-, E)`
exchange object properties `P` and `Q` and evaluation is bijective on both classes, they restrict
to an anti-equivalence `P.FullSubcategoryᵒᵖ ≌ Q.FullSubcategory` with evaluation as unit and
counit. -/
@[expose]
def linearMapDualityOn (P : ObjectProperty (ModuleCat.{max v w} R))
    (Q : ObjectProperty (ModuleCat.{max v w} S))
    (hPQ : ∀ M, P M → Q (linearMapObj R S E M))
    (hQP : ∀ N, Q N → P (linearMapObj S R E N))
    (hEvalP : ∀ M, P M → Function.Bijective (linearMapEval R S E M))
    (hEvalQ : ∀ N, Q N → Function.Bijective (linearMapEval S R E N)) :
    P.FullSubcategoryᵒᵖ ≌ Q.FullSubcategory where
  functor := ObjectProperty.lift _ (P.ι.op ⋙ linearMapFunctor R S E)
    fun M ↦ hPQ _ M.unop.property
  inverse := (ObjectProperty.lift _ (Q.ι.op ⋙ linearMapFunctor S R E)
    fun N ↦ hQP _ N.unop.property).rightOp
  unitIso := NatIso.ofComponents
    (fun M ↦ (ObjectProperty.isoMk _ (linearMapEvalIso (hEvalP _ M.unop.property))).symm.op)
    (fun {X Y} g ↦ Quiver.Hom.unop_inj <| (Iso.inv_comp_eq _).mpr <|
      ((Iso.eq_comp_inv _).mpr <| ObjectProperty.hom_ext _ <|
        linearMapEvalIso_hom_naturality g.unop.hom (hEvalP _ Y.unop.property)
          (hEvalP _ X.unop.property)).trans (Category.assoc _ _ _))
  counitIso := NatIso.ofComponents
    (fun N ↦ (ObjectProperty.isoMk _ (linearMapEvalIso (hEvalQ _ N.property))).symm)
    (fun {X Y} g ↦ (Iso.comp_inv_eq _).mpr <| ((Iso.eq_inv_comp _).mpr <|
      ObjectProperty.hom_ext _ <|
        (linearMapEvalIso_hom_naturality g.hom (hEvalQ _ X.property)
          (hEvalQ _ Y.property)).symm).trans (Category.assoc _ _ _).symm)
  functor_unitIso_comp M := by
    refine ObjectProperty.hom_ext Q ?_
    exact (Iso.comp_inv_eq_id (linearMapEvalIso (hEvalQ _ (hPQ _ M.unop.property)))).mpr
      (linearMapEvalIso_linearMapObj_hom (hEvalP _ M.unop.property)
        (hEvalQ _ (hPQ _ M.unop.property))).symm

section OnLemmas

variable (P : ObjectProperty (ModuleCat.{max v w} R))
  (Q : ObjectProperty (ModuleCat.{max v w} S))
  (hPQ : ∀ M, P M → Q (linearMapObj R S E M))
  (hQP : ∀ N, Q N → P (linearMapObj S R E N))
  (hEvalP : ∀ M, P M → Function.Bijective (linearMapEval R S E M))
  (hEvalQ : ∀ N, Q N → Function.Bijective (linearMapEval S R E N))

@[simp]
theorem linearMapDualityOn_functor_obj_obj (M : P.FullSubcategoryᵒᵖ) :
    ((linearMapDualityOn P Q hPQ hQP hEvalP hEvalQ).functor.obj M).obj =
      linearMapObj R S E M.unop.obj :=
  rfl

@[simp]
theorem linearMapDualityOn_functor_map_hom {M M' : P.FullSubcategoryᵒᵖ} (g : M ⟶ M') :
    ((linearMapDualityOn P Q hPQ hQP hEvalP hEvalQ).functor.map g).hom =
      linearMapMap R S E g.unop.hom :=
  rfl

@[simp]
theorem linearMapDualityOn_inverse_obj_unop_obj (N : Q.FullSubcategory) :
    ((linearMapDualityOn P Q hPQ hQP hEvalP hEvalQ).inverse.obj N).unop.obj =
      linearMapObj S R E N.obj :=
  rfl

@[simp]
theorem linearMapDualityOn_inverse_map_unop_hom {N N' : Q.FullSubcategory} (g : N ⟶ N') :
    ((linearMapDualityOn P Q hPQ hQP hEvalP hEvalQ).inverse.map g).unop.hom =
      linearMapMap S R E g.hom :=
  rfl

@[simp]
theorem linearMapDualityOn_unitIso_inv_app (M : P.FullSubcategoryᵒᵖ) :
    ((linearMapDualityOn P Q hPQ hQP hEvalP hEvalQ).unitIso.inv.app M).unop.hom =
      (linearMapEvalIso (hEvalP _ M.unop.property)).hom :=
  rfl

@[simp]
theorem linearMapDualityOn_counitIso_inv_app (N : Q.FullSubcategory) :
    ((linearMapDualityOn P Q hPQ hQP hEvalP hEvalQ).counitIso.inv.app N).hom =
      (linearMapEvalIso (hEvalQ _ N.property)).hom :=
  rfl

end OnLemmas

end Eval

end ModuleCat

namespace TauCeti.IsInjectiveEnvelope

open IsLocalRing ModuleCat

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)

include hι

section Complete

variable [IsAdicComplete (maximalIdeal R) R]

/-- **Categorical Matlis duality over a complete Noetherian local ring.** For an injective hull `E`
of the residue field, `Hom_R(-, E)` is an anti-equivalence between Artinian `R`-modules and
finitely generated `R`-modules, with evaluation as unit and counit. -/
@[expose, stacks 08Z9]
def artinianMatlisDuality :
    (ModuleCat.isArtinian.{max v w} R).FullSubcategoryᵒᵖ ≌ FGModuleCat.{max v w} R :=
  linearMapDualityOn (ModuleCat.isArtinian R) (ModuleCat.isFG R)
    (fun M hM ↦
      have := (ModuleCat.isArtinian_iff M).mp hM
      have := hι.finite_linearMap_of_isArtinian M
      (ModuleCat.isFG_iff _).mpr (Module.Finite.equiv (linearMapObjEquiv R R E M).symm))
    (fun N hN ↦
      have := (ModuleCat.isFG_iff N).mp hN
      have := hι.isArtinian_linearMap_of_finite N
      (ModuleCat.isArtinian_iff _).mpr (isArtinian_of_linearEquiv (linearMapObjEquiv R R E N).symm))
    (fun M hM ↦
      have := (ModuleCat.isArtinian_iff M).mp hM
      bijective_linearMapEval_of_bijective LinearMap.applyₗ (fun _ _ ↦ rfl)
        (hι.bijective_applyₗ_of_isArtinian M))
    (fun N hN ↦
      have := (ModuleCat.isFG_iff N).mp hN
      bijective_linearMapEval_of_bijective LinearMap.applyₗ (fun _ _ ↦ rfl)
        (hι.bijective_applyₗ_of_finite N))

@[simp]
theorem artinianMatlisDuality_functor_obj_obj
    (M : (ModuleCat.isArtinian.{max v w} R).FullSubcategoryᵒᵖ) :
    (hι.artinianMatlisDuality.functor.obj M).obj = linearMapObj R R E M.unop.obj :=
  rfl

@[simp]
theorem artinianMatlisDuality_functor_map_hom
    {M M' : (ModuleCat.isArtinian.{max v w} R).FullSubcategoryᵒᵖ} (g : M ⟶ M') :
    (hι.artinianMatlisDuality.functor.map g).hom = linearMapMap R R E g.unop.hom :=
  rfl

@[simp]
theorem artinianMatlisDuality_inverse_obj_unop_obj (N : FGModuleCat.{max v w} R) :
    (hι.artinianMatlisDuality.inverse.obj N).unop.obj = linearMapObj R R E N.obj :=
  rfl

@[simp]
theorem artinianMatlisDuality_inverse_map_unop_hom {N N' : FGModuleCat.{max v w} R} (g : N ⟶ N') :
    (hι.artinianMatlisDuality.inverse.map g).unop.hom = linearMapMap R R E g.hom :=
  rfl

/-- The inverse of the unit of `artinianMatlisDuality` is evaluation on `M`. -/
@[simp]
theorem artinianMatlisDuality_unitIso_inv_app
    (M : (ModuleCat.isArtinian.{max v w} R).FullSubcategoryᵒᵖ) :
    (hι.artinianMatlisDuality.unitIso.inv.app M).unop.hom =
      linearMapEval R R E M.unop.obj :=
  (rfl)

/-- The inverse of the counit of `artinianMatlisDuality` is evaluation on `N`. -/
@[simp]
theorem artinianMatlisDuality_counitIso_inv_app (N : FGModuleCat.{max v w} R) :
    (hι.artinianMatlisDuality.counitIso.inv.app N).hom = linearMapEval R R E N.obj :=
  (rfl)

end Complete

section General

/-- **Categorical Matlis duality over a general Noetherian local ring.** For an injective hull `E`
of the residue field of `R`, `Hom_R(-, E)` and `Hom_{R̂}(-, E)` form an anti-equivalence between
Artinian `R`-modules and finitely generated modules over the completion
`R̂ = AdicCompletion (maximalIdeal R) R`, with evaluation as unit and counit. -/
@[expose, stacks 0EGL]
def artinianMatlisDualityAdicCompletion :
    (ModuleCat.isArtinian.{max v w} R).FullSubcategoryᵒᵖ ≌
      FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R) :=
  let S := _root_.AdicCompletion (maximalIdeal R) R
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  letI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  linearMapDualityOn (ModuleCat.isArtinian R) (ModuleCat.isFG S)
    (fun M hM ↦
      have := (ModuleCat.isArtinian_iff M).mp hM
      have := hι.finite_adicCompletion_linearMap_of_isArtinian M
      (ModuleCat.isFG_iff _).mpr (Module.Finite.equiv (linearMapObjEquiv R S E M).symm))
    (fun N hN ↦
      have := (ModuleCat.isFG_iff N).mp hN
      have := hι.isArtinian_adicCompletionLinearMap_of_finite N
      (ModuleCat.isArtinian_iff _).mpr (isArtinian_of_linearEquiv (linearMapObjEquiv S R E N).symm))
    (fun M hM ↦
      have := (ModuleCat.isArtinian_iff M).mp hM
      bijective_linearMapEval_of_bijective (hι.evalAdicCompletionₗ M)
        (hι.evalAdicCompletionₗ_apply_apply M)
        (hι.bijective_evalAdicCompletionₗ_of_isArtinian M))
    (fun N hN ↦
      have := (ModuleCat.isFG_iff N).mp hN
      bijective_linearMapEval_of_bijective (hι.evalLinearMapAdicCompletionₗ N)
        (hι.evalLinearMapAdicCompletionₗ_apply_apply N)
        (hι.bijective_evalLinearMapAdicCompletionₗ_of_finite N))

@[simp]
theorem artinianMatlisDualityAdicCompletion_functor_obj_obj
    (M : (ModuleCat.isArtinian.{max v w} R).FullSubcategoryᵒᵖ) :
    (hι.artinianMatlisDualityAdicCompletion.functor.obj M).obj =
      letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      letI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
      linearMapObj R (_root_.AdicCompletion (maximalIdeal R) R) E M.unop.obj :=
  rfl

@[simp]
theorem artinianMatlisDualityAdicCompletion_functor_map_hom
    {M M' : (ModuleCat.isArtinian.{max v w} R).FullSubcategoryᵒᵖ} (g : M ⟶ M') :
    (hι.artinianMatlisDualityAdicCompletion.functor.map g).hom =
      letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      letI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
      linearMapMap R (_root_.AdicCompletion (maximalIdeal R) R) E g.unop.hom :=
  rfl

@[simp]
theorem artinianMatlisDualityAdicCompletion_inverse_obj_unop_obj
    (N : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    (hι.artinianMatlisDualityAdicCompletion.inverse.obj N).unop.obj =
      letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      letI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
      linearMapObj (_root_.AdicCompletion (maximalIdeal R) R) R E N.obj :=
  rfl

@[simp]
theorem artinianMatlisDualityAdicCompletion_inverse_map_unop_hom
    {N N' : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)} (g : N ⟶ N') :
    (hι.artinianMatlisDualityAdicCompletion.inverse.map g).unop.hom =
      letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      letI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
      linearMapMap (_root_.AdicCompletion (maximalIdeal R) R) R E g.hom :=
  rfl

/-- The inverse of the unit of `artinianMatlisDualityAdicCompletion` is evaluation on `M`. -/
@[simp]
theorem artinianMatlisDualityAdicCompletion_unitIso_inv_app
    (M : (ModuleCat.isArtinian.{max v w} R).FullSubcategoryᵒᵖ) :
    (hι.artinianMatlisDualityAdicCompletion.unitIso.inv.app M).unop.hom =
      letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      letI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
      linearMapEval R (_root_.AdicCompletion (maximalIdeal R) R) E M.unop.obj :=
  (rfl)

/-- The inverse of the counit of `artinianMatlisDualityAdicCompletion` is evaluation on `N`. -/
@[simp]
theorem artinianMatlisDualityAdicCompletion_counitIso_inv_app
    (N : FGModuleCat.{max v w} (_root_.AdicCompletion (maximalIdeal R) R)) :
    (hι.artinianMatlisDualityAdicCompletion.counitIso.inv.app N).hom =
      letI := AdicCompletion.torsionModule hι.mem_primaryComponent
      letI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
      linearMapEval (_root_.AdicCompletion (maximalIdeal R) R) R E N.obj :=
  (rfl)

end General

end TauCeti.IsInjectiveEnvelope
