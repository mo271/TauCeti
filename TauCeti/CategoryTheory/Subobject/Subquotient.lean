/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Subobject.Cokernel
public import TauCeti.CategoryTheory.Subobject.FactorThru
public import TauCeti.CategoryTheory.Subobject.Limits

/-!
# Subquotient presentations of objects in an abelian category

Given objects `A` and `X` in an abelian category `C`, a *subquotient presentation* of `X` inside
`A` (`TauCeti.SubquotientPresentation A X`) consists of subobjects `B ≤ Z` of `A` together with a
marking isomorphism `cokernel (Subobject.ofLE B Z le) ≅ X`. Writing `P.π : (P.Z : C) ⟶ X` for the
composite of the cokernel projection with `P.iso.hom`, this file establishes the lattice,
composition, and functoriality properties of subquotient presentations:

* `TauCeti.SubquotientPresentation.ext`: two presentations of `X` inside `A` are equal as soon as
  they have the same upper subobject `Z` and the same projection `π`.
* `TauCeti.SubquotientPresentation.orderIso`: preimage along `P.π` is an order isomorphism
  `Subobject X ≃o Set.Icc P.B P.Z`, whose inverse sends `S ∈ [P.B, P.Z]` to the direct image of
  `S` along `P.π` (equivalently, the image in `cokernel (Subobject.ofLE P.B P.Z P.le)` transported
  along `P.iso`). It preserves all greatest lower bounds and least upper bounds.
* `TauCeti.SubquotientPresentation.refl`: the identity presentation `(⊥, ⊤, e)` of `X` inside `X`,
  for which `orderIso` acts as the identity on underlying subobjects.
* `TauCeti.SubquotientPresentation.trans` and `TauCeti.SubquotientPresentation.ofSubobjects`:
  transport of a presentation `Q` of `Y` inside `X` along a presentation `P` of `X` inside `A`
  (specializing to the presentation of `cokernel (Subobject.ofLE I K hIK)` inside `A` for
  `I ≤ K` in `Subobject X`), satisfying `refl_trans`, `trans_refl`, and `trans_assoc` (so refining
  along `I ≤ I' ≤ K' ≤ K` agrees with refining in two steps).
* `TauCeti.SubquotientPresentation.descMap`: functoriality of presentations along a morphism
  `f : A₁ ⟶ A₂` carrying `Z₁` into the pullback of `Z₂` and the image of `B₁` into `B₂`, compatible
  with `refl` and `trans`.

## References

* [The Stacks Project Authors, *Stacks Project*][stacks-project], Tag 011N (construction of cycle
  and boundary subobjects via subquotient transport).
* H. Helle and J. Rognes, *Boardman's whole-plane obstruction group*, Lemma 2.2.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe v u

section Basic

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCokernels C]

/-- A *subquotient presentation* of an object `X` inside an ambient object `A` consists of a pair of
subobjects `B ≤ Z` of `A` together with an isomorphism from `cokernel (Subobject.ofLE B Z le)` to
`X`. -/
structure SubquotientPresentation (A X : C) where
  /-- The lower ("boundary") subobject of `A`. -/
  B : Subobject A
  /-- The upper ("cycle") subobject of `A`. -/
  Z : Subobject A
  /-- The inclusion `B ≤ Z` in `Subobject A`. -/
  le : B ≤ Z
  /-- The marking isomorphism identifying the quotient `Z / B` with `X`. -/
  iso : cokernel (Subobject.ofLE B Z le) ≅ X

namespace SubquotientPresentation

variable {A X Y W : C}

/-- The canonical projection `(P.Z : C) ⟶ X` of a subquotient presentation, defined as the cokernel
projection followed by `P.iso.hom`. -/
noncomputable def π (P : SubquotientPresentation A X) : (P.Z : C) ⟶ X :=
  cokernel.π (Subobject.ofLE P.B P.Z P.le) ≫ P.iso.hom

instance epi_π (P : SubquotientPresentation A X) : Epi P.π := by
  rw [π]
  infer_instance

@[reassoc (attr := simp)]
lemma ofLE_comp_π (P : SubquotientPresentation A X) :
    Subobject.ofLE P.B P.Z P.le ≫ P.π = 0 := by
  rw [π, cokernel.condition_assoc, zero_comp]

@[reassoc (attr := simp)]
lemma π_comp_iso_inv (P : SubquotientPresentation A X) :
    P.π ≫ P.iso.inv = cokernel.π (Subobject.ofLE P.B P.Z P.le) := by
  simp [π]

/-- The tautological subquotient presentation of `cokernel (Subobject.ofLE I K hIK)` inside `X` by
the pair `(I, K)`. -/
noncomputable def ofLE {I K : Subobject X} (hIK : I ≤ K) :
    SubquotientPresentation X (cokernel (Subobject.ofLE I K hIK)) where
  B := I
  Z := K
  le := hIK
  iso := Iso.refl _

@[simp]
lemma ofLE_B {I K : Subobject X} (hIK : I ≤ K) : (ofLE hIK).B = I := by
  simp [ofLE]

@[simp]
lemma ofLE_Z {I K : Subobject X} (hIK : I ≤ K) : (ofLE hIK).Z = K := by
  simp [ofLE]

lemma ofLE_π {I K : Subobject X} (hIK : I ≤ K) :
    (ofLE hIK).π = Subobject.ofLE (ofLE hIK).Z K (ofLE_Z hIK).le ≫
      cokernel.π (Subobject.ofLE I K hIK) := by
  simp [ofLE, π]

/-- Transport a subquotient presentation of `X` inside `A` along an isomorphism `X ≅ Y`. -/
noncomputable def transIso (P : SubquotientPresentation A X) (e : X ≅ Y) :
    SubquotientPresentation A Y where
  B := P.B
  Z := P.Z
  le := P.le
  iso := P.iso ≪≫ e

@[simp]
lemma transIso_B (P : SubquotientPresentation A X) (e : X ≅ Y) : (P.transIso e).B = P.B := by
  simp [transIso]

@[simp]
lemma transIso_Z (P : SubquotientPresentation A X) (e : X ≅ Y) : (P.transIso e).Z = P.Z := by
  simp [transIso]

@[reassoc]
lemma transIso_π (P : SubquotientPresentation A X) (e : X ≅ Y) :
    (P.transIso e).π = Subobject.ofLE (P.transIso e).Z P.Z (P.transIso_Z e).le ≫
      P.π ≫ e.hom := by
  rcases P with ⟨B, Z, le, iso⟩
  simp [transIso, π]

@[simp]
lemma transIso_refl (P : SubquotientPresentation A X) :
    P.transIso (Iso.refl X) = P := by
  cases P
  simp [transIso]

@[simp]
lemma transIso_trans (P : SubquotientPresentation A X) (e₁ : X ≅ Y) (e₂ : Y ≅ W) :
    (P.transIso e₁).transIso e₂ = P.transIso (e₁ ≪≫ e₂) := by
  cases P
  simp [transIso, Iso.trans_assoc]

end SubquotientPresentation

end Basic

namespace SubquotientPresentation

variable {C : Type u} [Category.{v} C] [Abelian C] {A A₁ A₂ A₃ X X₁ X₂ X₃ Y Y₁ Y₂ W : C}

/-! ### Kernel of the projection, extensionality, and vanishing -/

/-- The kernel subobject of `P.π` inside `P.Z` is the subobject represented by
`Subobject.ofLE P.B P.Z P.le`. -/
lemma kernelSubobject_π (P : SubquotientPresentation A X) :
    kernelSubobject P.π = Subobject.mk (Subobject.ofLE P.B P.Z P.le) := by
  rw [π, kernelSubobject_comp_mono, Subobject.kernelSubobject_cokernel_π]

/-- Under `P.Z.subobjectOrderIso`, the kernel subobject of `P.π` corresponds to `P.B`. -/
@[simp]
lemma subobjectOrderIso_kernelSubobject_π (P : SubquotientPresentation A X) :
    (P.Z.subobjectOrderIso (kernelSubobject P.π)).1 = P.B := by
  have hsymm : P.Z.subobjectOrderIso.symm ⟨P.B, P.le⟩ = kernelSubobject P.π := by
    rw [kernelSubobject_π]
    rfl
  rw [← hsymm, OrderIso.apply_symm_apply]

/-- A morphism `g : T ⟶ (P.Z : C)` vanishes after `P.π` if and only if `g ≫ P.Z.arrow` factors
through `P.B`. -/
lemma factors_B_iff_comp_π_eq_zero {T : C} (P : SubquotientPresentation A X)
    (g : T ⟶ (P.Z : C)) :
    P.B.Factors (g ≫ P.Z.arrow) ↔ g ≫ P.π = 0 := by
  constructor
  · intro h
    have hfac : g = P.B.factorThru (g ≫ P.Z.arrow) h ≫ Subobject.ofLE P.B P.Z P.le := by
      rw [← cancel_mono P.Z.arrow, Category.assoc, Subobject.ofLE_arrow,
        Subobject.factorThru_arrow]
    rw [hfac, Category.assoc, ofLE_comp_π, comp_zero]
  · intro hg
    have hmk : (Subobject.mk (Subobject.ofLE P.B P.Z P.le)).Factors g := by
      rw [← kernelSubobject_π, kernelSubobject_factors_iff]
      exact hg
    let u := (Subobject.mk (Subobject.ofLE P.B P.Z P.le)).factorThru g hmk
    have heq : g ≫ P.Z.arrow =
        (u ≫ (Subobject.underlyingIso (Subobject.ofLE P.B P.Z P.le)).hom) ≫ P.B.arrow := by
      calc g ≫ P.Z.arrow
          = (u ≫ (Subobject.mk (Subobject.ofLE P.B P.Z P.le)).arrow) ≫ P.Z.arrow := by
              rw [Subobject.factorThru_arrow]
        _ = (u ≫ (Subobject.underlyingIso (Subobject.ofLE P.B P.Z P.le)).hom ≫
              Subobject.ofLE P.B P.Z P.le) ≫ P.Z.arrow := by
              rw [Subobject.underlyingIso_hom_comp_eq_mk]
        _ = (u ≫ (Subobject.underlyingIso (Subobject.ofLE P.B P.Z P.le)).hom) ≫ P.B.arrow := by
              rw [Category.assoc, Category.assoc, Subobject.ofLE_arrow, ← Category.assoc]
    rw [heq]
    exact Subobject.factors_comp_arrow _

/-- Two subquotient presentations of `X` inside `A` are equal if they have the same upper subobject
`Z` and compatible projections `π`. In particular, `B` and `iso` are uniquely recovered from `Z`
and `π`. -/
@[ext (iff := false)]
lemma ext {P₁ P₂ : SubquotientPresentation A X} (hZ : P₁.Z = P₂.Z)
    (hπ : Subobject.ofLE P₁.Z P₂.Z hZ.le ≫ P₂.π = P₁.π) : P₁ = P₂ := by
  rcases P₁ with ⟨B₁, Z₁, le₁, iso₁⟩
  rcases P₂ with ⟨B₂, Z₂, le₂, iso₂⟩
  dsimp at hZ
  subst hZ
  have hπ' : ({ B := B₁, Z := Z₁, le := le₁, iso := iso₁ } : SubquotientPresentation A X).π =
      ({ B := B₂, Z := Z₁, le := le₂, iso := iso₂ } : SubquotientPresentation A X).π := by
    dsimp at hπ
    rw [Subobject.ofLE_refl, Category.id_comp] at hπ
    exact hπ.symm
  have hB : B₁ = B₂ := by
    have h₁ := subobjectOrderIso_kernelSubobject_π
      ({ B := B₁, Z := Z₁, le := le₁, iso := iso₁ } : SubquotientPresentation A X)
    have h₂ := subobjectOrderIso_kernelSubobject_π
      ({ B := B₂, Z := Z₁, le := le₂, iso := iso₂ } : SubquotientPresentation A X)
    dsimp at h₁ h₂
    rw [hπ'] at h₁
    exact h₁.symm.trans h₂
  subst hB
  congr 1
  ext1
  rw [← cancel_epi (cokernel.π (Subobject.ofLE B₁ Z₁ le₁))]
  exact hπ'

/-- For any subquotient presentation `P` of `X`, `X` is a zero object if and only if `P.B = P.Z`. -/
lemma isZero_iff (P : SubquotientPresentation A X) : IsZero X ↔ P.B = P.Z := by
  rcases P with ⟨B, Z, le, iso⟩
  dsimp
  rw [← iso.isZero_iff]
  constructor
  · intro h
    have hπ : cokernel.π (Subobject.ofLE B Z le) = 0 := h.eq_of_tgt _ _
    have : Epi (Subobject.ofLE B Z le) := Abelian.epi_of_cokernel_π_eq_zero _ hπ
    have : IsIso (Subobject.ofLE B Z le) := isIso_of_mono_of_epi _
    exact le_antisymm le (Subobject.le_of_comm (inv (Subobject.ofLE B Z le)) (by simp))
  · rintro rfl
    rw [Subobject.ofLE_refl]
    exact isZero_cokernel_of_epi _

/-! ### The lattice isomorphism `Subobject X ≃o Set.Icc P.B P.Z` -/

/-- The preimage of a subobject `K : Subobject X` in `Subobject A` along `P.π`, viewed inside `A`
via `P.Z.subobjectOrderIso`. -/
noncomputable def preimage (P : SubquotientPresentation A X) (K : Subobject X) : Subobject A :=
  (P.Z.subobjectOrderIso ((Subobject.pullback P.π).obj K)).1

lemma preimage_le_Z (P : SubquotientPresentation A X) (K : Subobject X) :
    P.preimage K ≤ P.Z :=
  (P.Z.subobjectOrderIso ((Subobject.pullback P.π).obj K)).2

lemma B_le_preimage (P : SubquotientPresentation A X) (K : Subobject X) :
    P.B ≤ P.preimage K := by
  have hle : kernelSubobject P.π ≤ (Subobject.pullback P.π).obj K := by
    rw [← (Subobject.existsPullbackAdj P.π).gc _ _, Subobject.exists_eq_imageSubobject,
      kernelSubobject_arrow_comp, imageSubobject_zero]
    exact bot_le
  have hmon := Subtype.coe_le_coe.mpr (P.Z.subobjectOrderIso.monotone hle)
  rwa [P.subobjectOrderIso_kernelSubobject_π] at hmon

lemma preimage_mem_Icc (P : SubquotientPresentation A X) (K : Subobject X) :
    P.preimage K ∈ Set.Icc P.B P.Z :=
  ⟨P.B_le_preimage K, P.preimage_le_Z K⟩

/-- The direct image in `Subobject X` of a subobject `S : Subobject A` lying below `P.Z`. -/
noncomputable def imageOfLE (P : SubquotientPresentation A X) (S : Subobject A) (hSZ : S ≤ P.Z) :
    Subobject X :=
  (Subobject.exists P.π).obj (P.Z.subobjectOrderIso.symm ⟨S, hSZ⟩)

lemma imageOfLE_eq_imageSubobject (P : SubquotientPresentation A X) (S : Subobject A)
    (hSZ : S ≤ P.Z) :
    P.imageOfLE S hSZ = imageSubobject (Subobject.ofLE S P.Z hSZ ≫ P.π) :=
  Subobject.exists_mk_eq_imageSubobject (Subobject.ofLE S P.Z hSZ) P.π

/-- The direct image of `S ≤ P.Z` along `P.π` equals the direct image along the cokernel projection
`P.Z ⟶ cokernel (Subobject.ofLE P.B P.Z P.le)` transported along `P.iso`. -/
lemma imageOfLE_eq_mapIsoToOrderIso (P : SubquotientPresentation A X) (S : Subobject A)
    (hSZ : S ≤ P.Z) :
    P.imageOfLE S hSZ = Subobject.mapIsoToOrderIso P.iso
      ((Subobject.exists (cokernel.π (Subobject.ofLE P.B P.Z P.le))).obj
        (P.Z.subobjectOrderIso.symm ⟨S, hSZ⟩)) := by
  rw [imageOfLE, Subobject.exists_eq_imageSubobject, Subobject.exists_eq_imageSubobject, π,
    ← Category.assoc]
  set f := (P.Z.subobjectOrderIso.symm ⟨S, hSZ⟩).arrow ≫ cokernel.π (Subobject.ofLE P.B P.Z P.le)
  calc imageSubobject (f ≫ P.iso.hom)
      = imageSubobject (factorThruImageSubobject f ≫ (imageSubobject f).arrow ≫ P.iso.hom) := by
          rw [imageSubobject_arrow_comp_assoc]
    _ = imageSubobject ((imageSubobject f).arrow ≫ P.iso.hom) :=
          imageSubobject_comp_eq_of_epi (factorThruImageSubobject f) _
    _ = Subobject.mk ((imageSubobject f).arrow ≫ P.iso.hom) := imageSubobject_mono _
    _ = Subobject.mk (image.ι f ≫ P.iso.hom) :=
          Subobject.mk_eq_mk_of_comm _ _ (imageSubobjectIso f) (by simp)
    _ = Subobject.mapIsoToOrderIso P.iso (imageSubobject f) := by
          rw [Subobject.mapIsoToOrderIso_apply, Subobject.map_mk]

lemma imageOfLE_mono (P : SubquotientPresentation A X) {S₁ S₂ : Subobject A}
    (hS₁ : S₁ ≤ P.Z) (hS₂ : S₂ ≤ P.Z) (h : S₁ ≤ S₂) :
    P.imageOfLE S₁ hS₁ ≤ P.imageOfLE S₂ hS₂ :=
  leOfHom ((Subobject.exists P.π).map (homOfLE (P.Z.subobjectOrderIso.symm.monotone
    (Subtype.coe_le_coe.mp h))))

private lemma imageOfLE_preimage_aux (P : SubquotientPresentation A X) (K : Subobject X) :
    P.imageOfLE (P.preimage K) (P.preimage_le_Z K) = K := by
  rw [imageOfLE]
  have hsymm : P.Z.subobjectOrderIso.symm ⟨P.preimage K, P.preimage_le_Z K⟩ =
      (Subobject.pullback P.π).obj K :=
    P.Z.subobjectOrderIso.symm_apply_apply _
  rw [hsymm, Subobject.exists_obj_pullback_obj_of_epi]

/-- Preimage along `P.π` is an order isomorphism from `Subobject X` onto `Set.Icc P.B P.Z`, whose
inverse sends `S ∈ [P.B, P.Z]` to its direct image along `P.π`. -/
noncomputable def orderIso (P : SubquotientPresentation A X) :
    Subobject X ≃o Set.Icc P.B P.Z where
  toFun K := ⟨P.preimage K, P.preimage_mem_Icc K⟩
  invFun S := P.imageOfLE S.1 S.2.2
  left_inv K := imageOfLE_preimage_aux P K
  right_inv S := Subtype.ext <| by
    dsimp only
    have hker : kernelSubobject P.π ≤ P.Z.subobjectOrderIso.symm ⟨S.1, S.2.2⟩ := by
      rw [← P.Z.subobjectOrderIso.le_iff_le, OrderIso.apply_symm_apply]
      exact Subtype.coe_le_coe.mp (P.subobjectOrderIso_kernelSubobject_π.trans_le S.2.1)
    rw [preimage, imageOfLE, Subobject.pullback_obj_exists_obj_of_kernelSubobject_le P.π hker]
    exact congrArg Subtype.val (P.Z.subobjectOrderIso.apply_symm_apply ⟨S.1, S.2.2⟩)
  map_rel_iff' {I K} := by
    constructor
    · intro h
      have him :=
        P.imageOfLE_mono (P.preimage_le_Z I) (P.preimage_le_Z K) (Subtype.coe_le_coe.mpr h)
      rwa [imageOfLE_preimage_aux, imageOfLE_preimage_aux] at him
    · intro h
      exact Subtype.coe_le_coe.mp (Subtype.coe_le_coe.mpr
        (P.Z.subobjectOrderIso.monotone (leOfHom ((Subobject.pullback P.π).map (homOfLE h)))))

@[simp]
lemma coe_orderIso_apply (P : SubquotientPresentation A X) (K : Subobject X) :
    ((P.orderIso K : Set.Icc P.B P.Z) : Subobject A) = P.preimage K := by
  simp [orderIso]

@[simp]
lemma orderIso_symm_apply (P : SubquotientPresentation A X) (S : Set.Icc P.B P.Z) :
    P.orderIso.symm S = P.imageOfLE S.1 S.2.2 := by
  simp [orderIso]

@[simp]
lemma imageOfLE_preimage (P : SubquotientPresentation A X) (K : Subobject X) :
    P.imageOfLE (P.preimage K) (P.preimage_le_Z K) = K :=
  imageOfLE_preimage_aux P K

@[simp]
lemma preimage_imageOfLE (P : SubquotientPresentation A X) {S : Subobject A} (hBS : P.B ≤ S)
    (hSZ : S ≤ P.Z) :
    P.preimage (P.imageOfLE S hSZ) = S := by
  have h := congrArg Subtype.val (P.orderIso.apply_symm_apply ⟨S, hBS, hSZ⟩)
  rwa [orderIso_symm_apply, coe_orderIso_apply] at h

@[simp]
lemma imageOfLE_B (P : SubquotientPresentation A X) : P.imageOfLE P.B P.le = ⊥ := by
  rw [imageOfLE_eq_imageSubobject, ofLE_comp_π, imageSubobject_zero]

@[simp]
lemma preimage_bot (P : SubquotientPresentation A X) : P.preimage ⊥ = P.B := by
  rw [← P.imageOfLE_B, P.preimage_imageOfLE le_rfl P.le]

@[simp]
lemma imageOfLE_Z (P : SubquotientPresentation A X) : P.imageOfLE P.Z le_rfl = ⊤ := by
  rw [imageOfLE_eq_imageSubobject, Subobject.ofLE_refl, Category.id_comp,
    ← Category.comp_id P.π, imageSubobject_comp_eq_of_epi P.π (𝟙 X), imageSubobject_mono,
    ← Subobject.top_eq_id]

@[simp]
lemma preimage_top (P : SubquotientPresentation A X) : P.preimage ⊤ = P.Z := by
  rw [← P.imageOfLE_Z, P.preimage_imageOfLE P.le le_rfl]

lemma preimage_mono (P : SubquotientPresentation A X) : Monotone P.preimage := by
  intro I K h
  simpa only [← coe_orderIso_apply] using Subtype.coe_le_coe.mpr (P.orderIso.monotone h)

@[simp]
lemma preimage_le_preimage_iff (P : SubquotientPresentation A X) {I K : Subobject X} :
    P.preimage I ≤ P.preimage K ↔ I ≤ K := by
  rw [← coe_orderIso_apply, ← coe_orderIso_apply, Subtype.coe_le_coe, P.orderIso.le_iff_le]

lemma preimage_injective (P : SubquotientPresentation A X) : Function.Injective P.preimage := by
  intro I K h
  refine P.orderIso.injective (Subtype.ext ?_)
  simpa only [coe_orderIso_apply] using h

@[simp]
lemma preimage_eq_preimage_iff (P : SubquotientPresentation A X) {I K : Subobject X} :
    P.preimage I = P.preimage K ↔ I = K :=
  P.preimage_injective.eq_iff

/-- A subobject `S ≤ P.Z` lies below `P.preimage K` if and only if `S ⟶ P.Z ⟶ X` factors through
`K`. -/
lemma le_preimage_iff_factors (P : SubquotientPresentation A X) {S : Subobject A} (hSZ : S ≤ P.Z)
    (K : Subobject X) :
    S ≤ P.preimage K ↔ K.Factors (Subobject.ofLE S P.Z hSZ ≫ P.π) := by
  have hS : (⟨S, hSZ⟩ : Set.Iic P.Z) ≤ P.Z.subobjectOrderIso ((Subobject.pullback P.π).obj K) ↔
      S ≤ P.preimage K := Iff.rfl
  rw [← hS, ← P.Z.subobjectOrderIso.symm_apply_le, ← (Subobject.existsPullbackAdj P.π).gc _ _]
  have him : (Subobject.exists P.π).obj (P.Z.subobjectOrderIso.symm ⟨S, hSZ⟩) =
      imageSubobject (Subobject.ofLE S P.Z hSZ ≫ P.π) :=
    P.imageOfLE_eq_imageSubobject S hSZ
  rw [him, Subobject.le_iff_factors]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa using Subobject.factors_of_factors_right (factorThruImageSubobject _) h
  · let u := K.factorThru (Subobject.ofLE S P.Z hSZ ≫ P.π) h
    have hu : u ≫ K.arrow = Subobject.ofLE S P.Z hSZ ≫ P.π := K.factorThru_arrow _ h
    have hw : ((imageSubobjectIso _).hom ≫ image.lift ⟨_, K.arrow, u, hu⟩) ≫ K.arrow =
        (imageSubobject (Subobject.ofLE S P.Z hSZ ≫ P.π)).arrow := by
      rw [Category.assoc, image.lift_fac, imageSubobject_arrow]
    rw [← hw]
    exact Subobject.factors_comp_arrow _

/-- A morphism `g : T ⟶ (P.Z : C)` has `g ≫ P.Z.arrow` factoring through `P.preimage K` if and
only if `g ≫ P.π` factors through `K`. -/
lemma factors_preimage_iff {T : C} (P : SubquotientPresentation A X) (K : Subobject X)
    (g : T ⟶ (P.Z : C)) :
    (P.preimage K).Factors (g ≫ P.Z.arrow) ↔ K.Factors (g ≫ P.π) := by
  set f := Subobject.ofLE (P.preimage K) P.Z (P.preimage_le_Z K)
  have heq : (Subobject.pullback P.π).obj K = Subobject.mk f :=
    (P.Z.subobjectOrderIso.symm_apply_apply ((Subobject.pullback P.π).obj K)).symm
  constructor
  · intro h
    let u := (P.preimage K).factorThru (g ≫ P.Z.arrow) h
    have hw : (u ≫ (Subobject.underlyingIso f).inv ≫ (Subobject.isoOfEq _ _ heq).inv ≫
        Subobject.pullbackπ P.π K) ≫ K.arrow = g ≫ P.π := by
      calc (u ≫ (Subobject.underlyingIso f).inv ≫ (Subobject.isoOfEq _ _ heq).inv ≫
              Subobject.pullbackπ P.π K) ≫ K.arrow
          = u ≫ (Subobject.underlyingIso f).inv ≫ (Subobject.isoOfEq _ _ heq).inv ≫
              ((Subobject.pullback P.π).obj K).arrow ≫ P.π := by
              simp only [Category.assoc, (Subobject.isPullback P.π K).w]
        _ = u ≫ (Subobject.underlyingIso f).inv ≫ (Subobject.mk f).arrow ≫ P.π := by
              rw [Subobject.isoOfEq_inv, Subobject.ofLE_arrow_assoc]
        _ = (u ≫ f) ≫ P.π := by
              rw [← Category.assoc (Subobject.underlyingIso f).inv, Subobject.underlyingIso_arrow,
                ← Category.assoc]
        _ = g ≫ P.π := by
              congr 1
              rw [← cancel_mono P.Z.arrow, Category.assoc, Subobject.ofLE_arrow]
              exact Subobject.factorThru_arrow _ _ h
    rw [← hw]
    exact Subobject.factors_comp_arrow _
  · intro h
    let v := K.factorThru (g ≫ P.π) h
    have hv : v ≫ K.arrow = g ≫ P.π := Subobject.factorThru_arrow _ _ h
    let w := (Subobject.isPullback P.π K).lift v g hv
    have hw_snd : w ≫ ((Subobject.pullback P.π).obj K).arrow = g :=
      (Subobject.isPullback P.π K).lift_snd v g hv
    have hw' : (w ≫ (Subobject.isoOfEq _ _ heq).hom ≫ (Subobject.underlyingIso f).hom) ≫
        (P.preimage K).arrow = g ≫ P.Z.arrow := by
      calc (w ≫ (Subobject.isoOfEq _ _ heq).hom ≫ (Subobject.underlyingIso f).hom) ≫
              (P.preimage K).arrow
          = w ≫ (Subobject.isoOfEq _ _ heq).hom ≫ ((Subobject.underlyingIso f).hom ≫ f) ≫
              P.Z.arrow := by
              simp only [Category.assoc, f, Subobject.ofLE_arrow]
        _ = w ≫ ((Subobject.isoOfEq _ _ heq).hom ≫ (Subobject.mk f).arrow) ≫ P.Z.arrow := by
              rw [Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
        _ = g ≫ P.Z.arrow := by
              rw [Subobject.isoOfEq_hom, Subobject.ofLE_arrow, ← Category.assoc, hw_snd]
    rw [← hw']
    exact Subobject.factors_comp_arrow _

lemma factors_ofLE_preimage_comp_π (P : SubquotientPresentation A X) (K : Subobject X) :
    K.Factors (Subobject.ofLE (P.preimage K) P.Z (P.preimage_le_Z K) ≫ P.π) :=
  (P.le_preimage_iff_factors (P.preimage_le_Z K) K).mp le_rfl

/-- `P.orderIso` preserves greatest lower bounds in `Set.Icc P.B P.Z`. -/
lemma isGLB_orderIso_image (P : SubquotientPresentation A X) {s : Set (Subobject X)}
    {K : Subobject X} :
    IsGLB (P.orderIso '' s) (P.orderIso K) ↔ IsGLB s K :=
  P.orderIso.isGLB_image'

/-- `P.orderIso` preserves least upper bounds in `Set.Icc P.B P.Z`. -/
lemma isLUB_orderIso_image (P : SubquotientPresentation A X) {s : Set (Subobject X)}
    {K : Subobject X} :
    IsLUB (P.orderIso '' s) (P.orderIso K) ↔ IsLUB s K :=
  P.orderIso.isLUB_image'

/-- For a nonempty set `s` of subobjects of `X`, `P.preimage K` is a greatest lower bound of
`P.preimage '' s` in the ambient lattice `Subobject A` if and only if `K` is a greatest lower bound
of `s` in `Subobject X`. -/
lemma isGLB_preimage_image_iff (P : SubquotientPresentation A X) {s : Set (Subobject X)}
    (hs : s.Nonempty) {K : Subobject X} :
    IsGLB (P.preimage '' s) (P.preimage K) ↔ IsGLB s K := by
  have himg : (P.preimage '' s) = ((↑) '' (P.orderIso '' s)) := by
    ext x
    simp
  rw [himg, ← P.coe_orderIso_apply K,
    ← TauCeti.isGLB_Icc_iff_ambient (hs.image P.orderIso), P.orderIso.isGLB_image']

/-- For a nonempty set `s` of subobjects of `X`, `P.preimage K` is a least upper bound of
`P.preimage '' s` in the ambient lattice `Subobject A` if and only if `K` is a least upper bound of
`s` in `Subobject X`. -/
lemma isLUB_preimage_image_iff (P : SubquotientPresentation A X) {s : Set (Subobject X)}
    (hs : s.Nonempty) {K : Subobject X} :
    IsLUB (P.preimage '' s) (P.preimage K) ↔ IsLUB s K := by
  have himg : (P.preimage '' s) = ((↑) '' (P.orderIso '' s)) := by
    ext x
    simp
  rw [himg, ← P.coe_orderIso_apply K,
    ← TauCeti.isLUB_Icc_iff_ambient (hs.image P.orderIso), P.orderIso.isLUB_image']

/-- If a nonempty family `P.preimage '' s` has a greatest lower bound `M` in `Subobject A`, then
`M ∈ Set.Icc P.B P.Z` and `P.imageOfLE M _` is a greatest lower bound of `s` in `Subobject X`. -/
lemma isGLB_of_isGLB_preimage_image (P : SubquotientPresentation A X) {s : Set (Subobject X)}
    (hs : s.Nonempty) {M : Subobject A} (hM : IsGLB (P.preimage '' s) M) :
    ∃ hMZ : M ≤ P.Z, P.B ≤ M ∧ IsGLB s (P.imageOfLE M hMZ) := by
  obtain ⟨K₀, hK₀⟩ := hs
  have hMZ : M ≤ P.Z := (hM.1 ⟨K₀, hK₀, rfl⟩).trans (P.preimage_le_Z K₀)
  have hBM : P.B ≤ M := hM.2 (by rintro _ ⟨K, _, rfl⟩; exact P.B_le_preimage K)
  refine ⟨hMZ, hBM, ?_⟩
  rw [← P.isGLB_preimage_image_iff ⟨K₀, hK₀⟩, P.preimage_imageOfLE hBM hMZ]
  exact hM

/-- If a nonempty family `P.preimage '' s` has a least upper bound `M` in `Subobject A`, then
`M ∈ Set.Icc P.B P.Z` and `P.imageOfLE M _` is a least upper bound of `s` in `Subobject X`. -/
lemma isLUB_of_isLUB_preimage_image (P : SubquotientPresentation A X) {s : Set (Subobject X)}
    (hs : s.Nonempty) {M : Subobject A} (hM : IsLUB (P.preimage '' s) M) :
    ∃ hMZ : M ≤ P.Z, P.B ≤ M ∧ IsLUB s (P.imageOfLE M hMZ) := by
  obtain ⟨K₀, hK₀⟩ := hs
  have hBM : P.B ≤ M := (P.B_le_preimage K₀).trans (hM.1 ⟨K₀, hK₀, rfl⟩)
  have hMZ : M ≤ P.Z := hM.2 (by rintro _ ⟨K, _, rfl⟩; exact P.preimage_le_Z K)
  refine ⟨hMZ, hBM, ?_⟩
  rw [← P.isLUB_preimage_image_iff ⟨K₀, hK₀⟩, P.preimage_imageOfLE hBM hMZ]
  exact hM

/-! ### The identity presentation `(⊥, ⊤, e)` -/

/-- The canonical identity presentation of `X` inside `X`, with `B = ⊥`, `Z = ⊤`, and `iso` the
canonical identification `cokernel (Subobject.ofLE ⊥ ⊤ bot_le) ≅ X`. -/
noncomputable def refl (X : C) : SubquotientPresentation X X where
  B := ⊥
  Z := ⊤
  le := bot_le
  iso :=
    cokernelIsoOfEq (IsZero.eq_of_src (IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero) _ _)
      ≪≫ cokernelZeroIsoTarget ≪≫ asIso (⊤ : Subobject X).arrow

@[simp]
lemma refl_B (X : C) : (refl X).B = ⊥ := by
  simp [refl]

@[simp]
lemma refl_Z (X : C) : (refl X).Z = ⊤ := by
  simp [refl]

lemma refl_π (X : C) : (refl X).π = (refl X).Z.arrow := by
  dsimp only [refl, π, Iso.trans_hom, asIso_hom]
  rw [π_comp_cokernelIsoOfEq_hom_assoc, cokernelZeroIsoTarget_hom, ← Category.assoc,
    cokernel.π_desc, Category.id_comp]

/-- Transport along the identity presentation `(⊥, ⊤, e)` acts as the identity on `Subobject X`. -/
@[simp]
lemma preimage_refl (K : Subobject X) : (refl X).preimage K = K := by
  apply le_antisymm
  · rw [Subobject.le_iff_factors]
    have h := (refl X).factors_ofLE_preimage_comp_π K
    rwa [refl_π, Subobject.ofLE_arrow] at h
  · rw [(refl X).le_preimage_iff_factors (by rw [refl_Z]; exact le_top), refl_π,
      Subobject.ofLE_arrow]
    exact Subobject.factors_self K

@[simp]
lemma imageOfLE_refl (S : Subobject X) (hS : S ≤ (refl X).Z) :
    (refl X).imageOfLE S hS = S := by
  apply (refl X).preimage_injective
  rw [(refl X).preimage_imageOfLE (by rw [refl_B]; exact bot_le) hS, preimage_refl]

/-! ### Composition / refinement of subquotient presentations -/

/-- The canonical epimorphism `(P.preimage K : C) ⟶ (K : C)` lifting
`Subobject.ofLE (P.preimage K) P.Z _ ≫ P.π` across `K.arrow`. -/
noncomputable def liftZ (P : SubquotientPresentation A X) (K : Subobject X) :
    (P.preimage K : C) ⟶ (K : C) :=
  K.factorThru (Subobject.ofLE (P.preimage K) P.Z (P.preimage_le_Z K) ≫ P.π)
    (P.factors_ofLE_preimage_comp_π K)

@[reassoc (attr := simp)]
lemma liftZ_arrow (P : SubquotientPresentation A X) (K : Subobject X) :
    P.liftZ K ≫ K.arrow = Subobject.ofLE (P.preimage K) P.Z (P.preimage_le_Z K) ≫ P.π :=
  K.factorThru_arrow _ _

instance epi_liftZ (P : SubquotientPresentation A X) (K : Subobject X) : Epi (P.liftZ K) := by
  set f := Subobject.ofLE (P.preimage K) P.Z (P.preimage_le_Z K)
  have heq : (Subobject.pullback P.π).obj K = Subobject.mk f :=
    (P.Z.subobjectOrderIso.symm_apply_apply ((Subobject.pullback P.π).obj K)).symm
  have hfac : P.liftZ K =
      (Subobject.underlyingIso f).inv ≫ (Subobject.isoOfEq _ _ heq).inv ≫
        Subobject.pullbackπ P.π K := by
    rw [← cancel_mono K.arrow, liftZ_arrow]
    calc f ≫ P.π
        = (Subobject.underlyingIso f).inv ≫ (Subobject.mk f).arrow ≫ P.π := by
            rw [Subobject.underlyingIso_arrow_assoc]
      _ = (Subobject.underlyingIso f).inv ≫ (Subobject.isoOfEq _ _ heq).inv ≫
            ((Subobject.pullback P.π).obj K).arrow ≫ P.π := by
            rw [Subobject.isoOfEq_inv, Subobject.ofLE_arrow_assoc]
      _ = ((Subobject.underlyingIso f).inv ≫ (Subobject.isoOfEq _ _ heq).inv ≫
            Subobject.pullbackπ P.π K) ≫ K.arrow := by
            simp only [Category.assoc, (Subobject.isPullback P.π K).w]
  rw [hfac]
  infer_instance

/-- Compose a presentation `P` of `X` inside `A` with a presentation `Q` of `Y` inside `X`, yielding
a presentation `(P.preimage Q.B, P.preimage Q.Z, _)` of `Y` inside `A`. -/
noncomputable def trans (P : SubquotientPresentation A X) (Q : SubquotientPresentation X Y) :
    SubquotientPresentation A Y where
  B := P.preimage Q.B
  Z := P.preimage Q.Z
  le := P.preimage_mono Q.le
  iso := by
    let p : (P.preimage Q.Z : C) ⟶ Y := P.liftZ Q.Z ≫ Q.π
    let m := Subobject.ofLE (P.preimage Q.B) (P.preimage Q.Z) (P.preimage_mono Q.le)
    have hm_zero : m ≫ p = 0 := by
      have hfac : Q.B.Factors ((m ≫ P.liftZ Q.Z) ≫ Q.Z.arrow) := by
        rw [Category.assoc, liftZ_arrow, Subobject.ofLE_comp_ofLE_assoc]
        exact P.factors_ofLE_preimage_comp_π Q.B
      rw [← Category.assoc]
      exact (Q.factors_B_iff_comp_π_eq_zero (m ≫ P.liftZ Q.Z)).mp hfac
    have hPB : ∀ {T : C} (k : T ⟶ (P.preimage Q.Z : C)), k ≫ p = 0 →
        (P.preimage Q.B).Factors (k ≫ (P.preimage Q.Z).arrow) := by
      intro T k hk
      have hQB : Q.B.Factors ((k ≫ P.liftZ Q.Z) ≫ Q.Z.arrow) :=
        (Q.factors_B_iff_comp_π_eq_zero (k ≫ P.liftZ Q.Z)).mpr (by simpa [p] using hk)
      rw [← Subobject.ofLE_arrow (P.preimage_le_Z Q.Z), ← Category.assoc]
      refine (P.factors_preimage_iff Q.B _).mpr ?_
      rw [Category.assoc, ← liftZ_arrow, ← Category.assoc]
      exact hQB
    have hfac_m : ∀ {T : C} (k : T ⟶ (P.preimage Q.Z : C)) (hk : k ≫ p = 0),
        (P.preimage Q.B).factorThru (k ≫ (P.preimage Q.Z).arrow) (hPB k hk) ≫ m = k := by
      intro T k hk
      rw [← cancel_mono (P.preimage Q.Z).arrow, Category.assoc]
      dsimp only [m]
      rw [Subobject.ofLE_arrow, Subobject.factorThru_arrow]
    have hker : IsLimit (KernelFork.ofι m hm_zero) :=
      KernelFork.IsLimit.ofι _ _
        (fun {T} k hk ↦ (P.preimage Q.B).factorThru (k ≫ (P.preimage Q.Z).arrow) (hPB k hk))
        (fun {T} k hk ↦ hfac_m k hk)
        (fun {T} k hk b hb ↦ (cancel_mono m).mp (hb.trans (hfac_m k hk).symm))
    exact (cokernelIsCokernel m).coconePointUniqueUpToIso (Abelian.epiIsCokernelOfKernel _ hker)

@[simp]
lemma trans_B (P : SubquotientPresentation A X) (Q : SubquotientPresentation X Y) :
    (P.trans Q).B = P.preimage Q.B := by
  simp [trans]

@[simp]
lemma trans_Z (P : SubquotientPresentation A X) (Q : SubquotientPresentation X Y) :
    (P.trans Q).Z = P.preimage Q.Z := by
  simp [trans]

@[reassoc]
lemma trans_π (P : SubquotientPresentation A X) (Q : SubquotientPresentation X Y) :
    (P.trans Q).π = Subobject.ofLE (P.trans Q).Z (P.preimage Q.Z) (P.trans_Z Q).le ≫
      P.liftZ Q.Z ≫ Q.π := by
  dsimp only [trans, π]
  rw [Subobject.ofLE_refl, Category.id_comp]
  exact (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

/-- Preimages along a composed presentation `P.trans Q` are iterated preimages. -/
@[simp]
lemma preimage_trans (P : SubquotientPresentation A X) (Q : SubquotientPresentation X Y)
    (K : Subobject Y) :
    (P.trans Q).preimage K = P.preimage (Q.preimage K) := by
  apply le_antisymm
  · have hZ₁ := (P.trans Q).preimage_le_Z K
    have hZ₂ := (P.trans_Z Q).le
    have hZ₃ := P.preimage_le_Z Q.Z
    rw [P.le_preimage_iff_factors (hZ₁.trans (hZ₂.trans hZ₃)),
      ← Subobject.ofLE_comp_ofLE _ _ _ (hZ₁.trans hZ₂) hZ₃, Category.assoc, ← liftZ_arrow,
      ← Category.assoc]
    refine (Q.factors_preimage_iff K _).mpr ?_
    have h := (P.trans Q).factors_ofLE_preimage_comp_π K
    rwa [trans_π, ← Category.assoc, Subobject.ofLE_comp_ofLE, ← Category.assoc] at h
  · have hle₁ : P.preimage (Q.preimage K) ≤ P.preimage Q.Z := P.preimage_mono (Q.preimage_le_Z K)
    have hle : P.preimage (Q.preimage K) ≤ (P.trans Q).Z := hle₁.trans (P.trans_Z Q).ge
    rw [(P.trans Q).le_preimage_iff_factors hle, trans_π, ← Category.assoc,
      Subobject.ofLE_comp_ofLE, ← Category.assoc]
    have hcomm : Subobject.ofLE (P.preimage (Q.preimage K)) (P.preimage Q.Z) hle₁ ≫ P.liftZ Q.Z =
        P.liftZ (Q.preimage K) ≫ Subobject.ofLE (Q.preimage K) Q.Z (Q.preimage_le_Z K) := by
      rw [← cancel_mono Q.Z.arrow, Category.assoc, Category.assoc, liftZ_arrow,
        Subobject.ofLE_arrow, liftZ_arrow, Subobject.ofLE_comp_ofLE_assoc]
    rw [hcomm, Category.assoc]
    exact Subobject.factors_of_factors_right _ (Q.factors_ofLE_preimage_comp_π K)

@[simp]
lemma refl_trans (Q : SubquotientPresentation X Y) : (refl X).trans Q = Q := by
  refine ext (by rw [trans_Z, preimage_refl]) ?_
  rw [trans_π, ← Category.assoc]
  congr 1
  rw [← cancel_mono Q.Z.arrow, Category.assoc, liftZ_arrow, refl_π, Subobject.ofLE_arrow,
    Subobject.ofLE_arrow, Subobject.ofLE_arrow]

@[simp]
lemma trans_refl (P : SubquotientPresentation A X) : P.trans (refl X) = P := by
  refine ext (by rw [trans_Z, refl_Z, preimage_top]) ?_
  rw [trans_π]
  have h : P.liftZ (refl X).Z ≫ (refl X).π =
      Subobject.ofLE (P.preimage (refl X).Z) P.Z (P.preimage_le_Z _) ≫ P.π := by
    rw [refl_π, liftZ_arrow]
  rw [h, Subobject.ofLE_comp_ofLE_assoc]

/-- Composition of subquotient presentations is associative. -/
lemma trans_assoc (P : SubquotientPresentation A X) (Q : SubquotientPresentation X Y)
    (R : SubquotientPresentation Y W) :
    (P.trans Q).trans R = P.trans (Q.trans R) := by
  refine ext (by rw [trans_Z, trans_Z, trans_Z, preimage_trans]) ?_
  rw [trans_π, trans_π, trans_π]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono R.Z.arrow]
  simp only [Category.assoc, liftZ_arrow, trans_π]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono Q.Z.arrow]
  simp only [Category.assoc, liftZ_arrow, Subobject.ofLE_arrow]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono P.Z.arrow]
  simp only [Category.assoc, Subobject.ofLE_arrow]

@[simp]
lemma preimage_transIso (P : SubquotientPresentation A X) (e : X ≅ Y) (K : Subobject Y) :
    (P.transIso e).preimage K = P.preimage (Subobject.mapIsoToOrderIso e.symm K) := by
  apply le_antisymm
  · rw [P.le_preimage_iff_factors (((P.transIso e).preimage_le_Z K).trans (P.transIso_Z e).le),
      Subobject.factors_mapIsoToOrderIso_iff, Iso.symm_inv]
    have h := (P.transIso e).factors_ofLE_preimage_comp_π K
    rwa [transIso_π, ← Category.assoc, Subobject.ofLE_comp_ofLE, ← Category.assoc] at h
  · rw [(P.transIso e).le_preimage_iff_factors ((P.preimage_le_Z _).trans (P.transIso_Z e).ge),
      transIso_π, ← Category.assoc, Subobject.ofLE_comp_ofLE, ← Category.assoc]
    have h := P.factors_ofLE_preimage_comp_π (Subobject.mapIsoToOrderIso e.symm K)
    rwa [Subobject.factors_mapIsoToOrderIso_iff, Iso.symm_inv] at h

lemma trans_transIso (P : SubquotientPresentation A X) (Q : SubquotientPresentation X Y)
    (e : Y ≅ W) :
    (P.trans Q).transIso e = P.trans (Q.transIso e) := by
  refine ext (by rw [transIso_Z, trans_Z, trans_Z, transIso_Z]) ?_
  rw [transIso_π, trans_π, trans_π, transIso_π]
  simp only [← Category.assoc]
  congr 1
  congr 1
  rw [← cancel_mono Q.Z.arrow]
  simp only [Category.assoc, liftZ_arrow, Subobject.ofLE_arrow]
  simp only [← Category.assoc]
  congr 1

/-- Given a presentation `P` of `X` inside `A` and subobjects `I ≤ K` of `X`, this is the induced
presentation `(P.preimage I, P.preimage K, _)` of `cokernel (Subobject.ofLE I K hIK)` inside `A`. -/
noncomputable abbrev ofSubobjects (P : SubquotientPresentation A X) {I K : Subobject X}
    (hIK : I ≤ K) : SubquotientPresentation A (cokernel (Subobject.ofLE I K hIK)) :=
  P.trans (ofLE hIK)

/-- Any presentation `P` with `P.B = I'` and `P.Z = K'` agrees with `ofLE hI'K'` up to transporting
along an isomorphism. -/
lemma exists_transIso_eq_ofLE (P : SubquotientPresentation A X) {I' K' : Subobject A}
    (hB : P.B = I') (hZ : P.Z = K') (hI'K' : I' ≤ K') :
    ∃ e : X ≅ cokernel (Subobject.ofLE I' K' hI'K'), P.transIso e = ofLE hI'K' := by
  rcases P with ⟨B, Z, le, iso⟩
  dsimp at hB hZ
  subst hB hZ
  exact ⟨iso.symm, by simp [transIso, ofLE]⟩

/-- **Two-step naturality of subquotient refinement.** For `I ≤ I' ≤ K' ≤ K` in `Subobject X`,
refining a presentation `P` of `X` directly by `I' ≤ K'` agrees (up to the canonical Noether
isomorphism) with first refining `P` by `I ≤ K` and then refining by the images `I'' ≤ K''` of
`I' ≤ K'` inside `cokernel (Subobject.ofLE I K hIK)`. -/
lemma ofSubobjects_two_step (P : SubquotientPresentation A X) {I I' K' K : Subobject X}
    (hII' : I ≤ I') (hI'K' : I' ≤ K') (hK'K : K' ≤ K) :
    let hIK : I ≤ K := hII'.trans (hI'K'.trans hK'K)
    let I'' := (ofLE hIK).imageOfLE I' (by rw [ofLE_Z]; exact hI'K'.trans hK'K)
    let K'' := (ofLE hIK).imageOfLE K' (by rw [ofLE_Z]; exact hK'K)
    have hI''K'' : I'' ≤ K'' := (ofLE hIK).imageOfLE_mono _ _ hI'K'
    ∃ e : cokernel (Subobject.ofLE I'' K'' hI''K'') ≅ cokernel (Subobject.ofLE I' K' hI'K'),
      ((P.ofSubobjects hIK).ofSubobjects hI''K'').transIso e = P.ofSubobjects hI'K' := by
  intro hIK I'' K'' hI''K''
  have hB : ((ofLE hIK).ofSubobjects hI''K'').B = I' := by
    rw [ofSubobjects, trans_B, ofLE_B, (ofLE hIK).preimage_imageOfLE (by rw [ofLE_B]; exact hII')]
  have hZ : ((ofLE hIK).ofSubobjects hI''K'').Z = K' := by
    rw [ofSubobjects, trans_Z, ofLE_Z,
      (ofLE hIK).preimage_imageOfLE (by rw [ofLE_B]; exact hII'.trans hI'K')]
  obtain ⟨e, he⟩ := ((ofLE hIK).ofSubobjects hI''K'').exists_transIso_eq_ofLE hB hZ hI'K'
  exact ⟨e, by rw [ofSubobjects, ofSubobjects, trans_assoc, trans_transIso, he]⟩

/-! ### Functoriality along morphisms of ambient objects -/

/-- When `P₁.Z ≤ (Subobject.pullback f).obj P₂.Z`, `f : A₁ ⟶ A₂` restricts to a morphism
`(P₁.Z : C) ⟶ (P₂.Z : C)`. -/
noncomputable def mapZ (P₁ : SubquotientPresentation A₁ X₁) (P₂ : SubquotientPresentation A₂ X₂)
    (f : A₁ ⟶ A₂) (hZ : P₁.Z ≤ (Subobject.pullback f).obj P₂.Z) :
    (P₁.Z : C) ⟶ (P₂.Z : C) :=
  Subobject.ofLE P₁.Z ((Subobject.pullback f).obj P₂.Z) hZ ≫ Subobject.pullbackπ f P₂.Z

@[reassoc (attr := simp)]
lemma mapZ_arrow (P₁ : SubquotientPresentation A₁ X₁) (P₂ : SubquotientPresentation A₂ X₂)
    (f : A₁ ⟶ A₂) (hZ : P₁.Z ≤ (Subobject.pullback f).obj P₂.Z) :
    P₁.mapZ P₂ f hZ ≫ P₂.Z.arrow = P₁.Z.arrow ≫ f := by
  rw [mapZ, Category.assoc, (Subobject.isPullback f P₂.Z).w, Subobject.ofLE_arrow_assoc]

/-- A morphism `f : A₁ ⟶ A₂` satisfying `P₁.Z ≤ pullback f P₂.Z` and `exists f P₁.B ≤ P₂.B` induces
a canonical morphism `X₁ ⟶ X₂` between the presented subquotients. -/
noncomputable def descMap (P₁ : SubquotientPresentation A₁ X₁) (P₂ : SubquotientPresentation A₂ X₂)
    (f : A₁ ⟶ A₂) (hB : (Subobject.exists f).obj P₁.B ≤ P₂.B)
    (hZ : P₁.Z ≤ (Subobject.pullback f).obj P₂.Z) : X₁ ⟶ X₂ :=
  P₁.iso.inv ≫ cokernel.desc (Subobject.ofLE P₁.B P₁.Z P₁.le) (P₁.mapZ P₂ f hZ ≫ P₂.π) (by
    rw [← Category.assoc]
    refine (P₂.factors_B_iff_comp_π_eq_zero _).mp ?_
    rw [Category.assoc, mapZ_arrow, Subobject.ofLE_arrow_assoc]
    have hB' : ((Subobject.pullback f).obj P₂.B).Factors P₁.B.arrow :=
      (Subobject.le_iff_factors _ _).mp (((Subobject.existsPullbackAdj f).gc _ _).mp hB)
    let u := ((Subobject.pullback f).obj P₂.B).factorThru P₁.B.arrow hB'
    have hu := ((Subobject.pullback f).obj P₂.B).factorThru_arrow P₁.B.arrow hB'
    have hw : (u ≫ Subobject.pullbackπ f P₂.B) ≫ P₂.B.arrow = P₁.B.arrow ≫ f := by
      rw [Category.assoc, (Subobject.isPullback f P₂.B).w, ← Category.assoc, hu]
    rw [← hw]
    exact Subobject.factors_comp_arrow _)

@[reassoc (attr := simp)]
lemma π_comp_descMap (P₁ : SubquotientPresentation A₁ X₁) (P₂ : SubquotientPresentation A₂ X₂)
    (f : A₁ ⟶ A₂) (hB : (Subobject.exists f).obj P₁.B ≤ P₂.B)
    (hZ : P₁.Z ≤ (Subobject.pullback f).obj P₂.Z) :
    P₁.π ≫ P₁.descMap P₂ f hB hZ = P₁.mapZ P₂ f hZ ≫ P₂.π := by
  simp [π, descMap]

/-- Uniqueness characterization of `descMap`: any `g : X₁ ⟶ X₂` intertwined with `mapZ` by the
projections `π` equals `descMap`. -/
lemma descMap_eq_of_π_comp (P₁ : SubquotientPresentation A₁ X₁) (P₂ : SubquotientPresentation A₂ X₂)
    (f : A₁ ⟶ A₂) (hB : (Subobject.exists f).obj P₁.B ≤ P₂.B)
    (hZ : P₁.Z ≤ (Subobject.pullback f).obj P₂.Z) {g : X₁ ⟶ X₂}
    (hg : P₁.π ≫ g = P₁.mapZ P₂ f hZ ≫ P₂.π) :
    P₁.descMap P₂ f hB hZ = g := by
  rw [← cancel_epi P₁.π, π_comp_descMap, hg]

lemma exists_id_le (S : Subobject A) : (Subobject.exists (𝟙 A)).obj S ≤ S := by
  rw [Subobject.exists_eq_imageSubobject, Category.comp_id, imageSubobject_mono, Subobject.mk_arrow]

lemma le_pullback_id (S : Subobject A) : S ≤ (Subobject.pullback (𝟙 A)).obj S :=
  ((Subobject.existsPullbackAdj (𝟙 A)).gc _ _).mp (exists_id_le S)

@[simp]
lemma descMap_id (P : SubquotientPresentation A X)
    (hB : (Subobject.exists (𝟙 A)).obj P.B ≤ P.B := exists_id_le P.B)
    (hZ : P.Z ≤ (Subobject.pullback (𝟙 A)).obj P.Z := le_pullback_id P.Z) :
    P.descMap P (𝟙 A) hB hZ = 𝟙 X := by
  refine P.descMap_eq_of_π_comp P (𝟙 A) hB hZ ?_
  rw [Category.comp_id]
  have h1 : P.mapZ P (𝟙 A) hZ = 𝟙 (P.Z : C) := by
    rw [← cancel_mono P.Z.arrow, mapZ_arrow, Category.comp_id, Category.id_comp]
  rw [h1, Category.id_comp]

lemma exists_comp_le {f₁ : A₁ ⟶ A₂} {f₂ : A₂ ⟶ A₃} {S₁ : Subobject A₁} {S₂ : Subobject A₂}
    {S₃ : Subobject A₃} (h₁ : (Subobject.exists f₁).obj S₁ ≤ S₂)
    (h₂ : (Subobject.exists f₂).obj S₂ ≤ S₃) :
    (Subobject.exists (f₁ ≫ f₂)).obj S₁ ≤ S₃ := by
  rw [Subobject.exists_eq_imageSubobject, ← Category.assoc, ← Subobject.exists_obj_imageSubobject,
    ← Subobject.exists_eq_imageSubobject]
  exact (leOfHom ((Subobject.exists f₂).map (homOfLE h₁))).trans h₂

lemma le_pullback_comp {f₁ : A₁ ⟶ A₂} {f₂ : A₂ ⟶ A₃} {S₁ : Subobject A₁} {S₂ : Subobject A₂}
    {S₃ : Subobject A₃} (h₁ : S₁ ≤ (Subobject.pullback f₁).obj S₂)
    (h₂ : S₂ ≤ (Subobject.pullback f₂).obj S₃) :
    S₁ ≤ (Subobject.pullback (f₁ ≫ f₂)).obj S₃ := by
  rw [← (Subobject.existsPullbackAdj (f₁ ≫ f₂)).gc _ _]
  exact exists_comp_le (((Subobject.existsPullbackAdj f₁).gc _ _).mpr h₁)
    (((Subobject.existsPullbackAdj f₂).gc _ _).mpr h₂)

lemma descMap_comp (P₁ : SubquotientPresentation A₁ X₁) (P₂ : SubquotientPresentation A₂ X₂)
    (P₃ : SubquotientPresentation A₃ X₃) (f₁ : A₁ ⟶ A₂) (f₂ : A₂ ⟶ A₃)
    (hB₁ : (Subobject.exists f₁).obj P₁.B ≤ P₂.B)
    (hZ₁ : P₁.Z ≤ (Subobject.pullback f₁).obj P₂.Z)
    (hB₂ : (Subobject.exists f₂).obj P₂.B ≤ P₃.B)
    (hZ₂ : P₂.Z ≤ (Subobject.pullback f₂).obj P₃.Z)
    (hB₁₂ : (Subobject.exists (f₁ ≫ f₂)).obj P₁.B ≤ P₃.B := exists_comp_le hB₁ hB₂)
    (hZ₁₂ : P₁.Z ≤ (Subobject.pullback (f₁ ≫ f₂)).obj P₃.Z := le_pullback_comp hZ₁ hZ₂) :
    P₁.descMap P₂ f₁ hB₁ hZ₁ ≫ P₂.descMap P₃ f₂ hB₂ hZ₂ =
      P₁.descMap P₃ (f₁ ≫ f₂) hB₁₂ hZ₁₂ := by
  symm
  refine P₁.descMap_eq_of_π_comp P₃ (f₁ ≫ f₂) hB₁₂ hZ₁₂ ?_
  rw [← Category.assoc, π_comp_descMap, Category.assoc, π_comp_descMap, ← Category.assoc]
  congr 1
  rw [← cancel_mono P₃.Z.arrow, Category.assoc, mapZ_arrow, mapZ_arrow, mapZ_arrow_assoc]

lemma exists_refl_le (f : X₁ ⟶ X₂) : (Subobject.exists f).obj (refl X₁).B ≤ (refl X₂).B := by
  rw [refl_B, refl_B, Subobject.exists_eq_imageSubobject,
    IsZero.eq_of_src (IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero)
      ((⊥ : Subobject X₁).arrow ≫ f) 0,
    imageSubobject_zero]

lemma refl_le_pullback (f : X₁ ⟶ X₂) : (refl X₁).Z ≤ (Subobject.pullback f).obj (refl X₂).Z := by
  rw [refl_Z, refl_Z, Subobject.pullback_top]

@[simp]
lemma descMap_refl (f : X₁ ⟶ X₂)
    (hB : (Subobject.exists f).obj (refl X₁).B ≤ (refl X₂).B := exists_refl_le f)
    (hZ : (refl X₁).Z ≤ (Subobject.pullback f).obj (refl X₂).Z := refl_le_pullback f) :
    (refl X₁).descMap (refl X₂) f hB hZ = f := by
  refine (refl X₁).descMap_eq_of_π_comp (refl X₂) f hB hZ ?_
  rw [refl_π, refl_π, mapZ_arrow]

/-- If `f : A₁ ⟶ A₂` induces `g : X₁ ⟶ X₂` on presentations `P₁, P₂`, then for any subobjects
`K₁ : Subobject X₁` and `K₂ : Subobject X₂` with `(Subobject.exists g).obj K₁ ≤ K₂`, `f` maps
`P₁.preimage K₁` into `P₂.preimage K₂`. -/
lemma exists_preimage_le (P₁ : SubquotientPresentation A₁ X₁) (P₂ : SubquotientPresentation A₂ X₂)
    (f : A₁ ⟶ A₂) (hPB : (Subobject.exists f).obj P₁.B ≤ P₂.B)
    (hPZ : P₁.Z ≤ (Subobject.pullback f).obj P₂.Z) {K₁ : Subobject X₁} {K₂ : Subobject X₂}
    (hK : (Subobject.exists (P₁.descMap P₂ f hPB hPZ)).obj K₁ ≤ K₂) :
    (Subobject.exists f).obj (P₁.preimage K₁) ≤ P₂.preimage K₂ := by
  set g := P₁.descMap P₂ f hPB hPZ
  rw [(Subobject.existsPullbackAdj f).gc _ _, Subobject.le_iff_factors]
  have hK' : K₂.Factors (K₁.arrow ≫ g) := by
    have hKpull : ((Subobject.pullback g).obj K₂).Factors K₁.arrow :=
      (Subobject.le_iff_factors _ _).mp (((Subobject.existsPullbackAdj g).gc _ _).mp hK)
    let u := ((Subobject.pullback g).obj K₂).factorThru K₁.arrow hKpull
    have hu := ((Subobject.pullback g).obj K₂).factorThru_arrow K₁.arrow hKpull
    have hw : (u ≫ Subobject.pullbackπ g K₂) ≫ K₂.arrow = K₁.arrow ≫ g := by
      rw [Category.assoc, (Subobject.isPullback g K₂).w, ← Category.assoc, hu]
    rw [← hw]
    exact Subobject.factors_comp_arrow _
  have hfac : (P₂.preimage K₂).Factors ((P₁.preimage K₁).arrow ≫ f) := by
    have heq : (P₁.preimage K₁).arrow ≫ f =
        (Subobject.ofLE (P₁.preimage K₁) P₁.Z (P₁.preimage_le_Z K₁) ≫ P₁.mapZ P₂ f hPZ) ≫
          P₂.Z.arrow := by
      rw [Category.assoc, mapZ_arrow, Subobject.ofLE_arrow_assoc]
    rw [heq, P₂.factors_preimage_iff, Category.assoc, ← P₁.π_comp_descMap P₂ f hPB hPZ,
      ← Category.assoc, ← liftZ_arrow, Category.assoc]
    exact Subobject.factors_of_factors_right (P₁.liftZ K₁) hK'
  let v := (Subobject.isPullback f (P₂.preimage K₂)).lift
    ((P₂.preimage K₂).factorThru _ hfac) (P₁.preimage K₁).arrow (Subobject.factorThru_arrow _ _ _)
  have hv : v ≫ ((Subobject.pullback f).obj (P₂.preimage K₂)).arrow = (P₁.preimage K₁).arrow :=
    (Subobject.isPullback f (P₂.preimage K₂)).lift_snd _ _ _
  rw [← hv]
  exact Subobject.factors_comp_arrow v

/-- Dual form of `exists_preimage_le` phrased with `Subobject.pullback`. -/
lemma preimage_le_pullback (P₁ : SubquotientPresentation A₁ X₁) (P₂ : SubquotientPresentation A₂ X₂)
    (f : A₁ ⟶ A₂) (hPB : (Subobject.exists f).obj P₁.B ≤ P₂.B)
    (hPZ : P₁.Z ≤ (Subobject.pullback f).obj P₂.Z) {K₁ : Subobject X₁} {K₂ : Subobject X₂}
    (hK : K₁ ≤ (Subobject.pullback (P₁.descMap P₂ f hPB hPZ)).obj K₂) :
    P₁.preimage K₁ ≤ (Subobject.pullback f).obj (P₂.preimage K₂) := by
  rw [← (Subobject.existsPullbackAdj f).gc _ _]
  exact P₁.exists_preimage_le P₂ f hPB hPZ
    (((Subobject.existsPullbackAdj (P₁.descMap P₂ f hPB hPZ)).gc _ _).mpr hK)

/-- `descMap` commutes with composing presentations via `trans`. -/
lemma descMap_trans (P₁ : SubquotientPresentation A₁ X₁) (P₂ : SubquotientPresentation A₂ X₂)
    (Q₁ : SubquotientPresentation X₁ Y₁) (Q₂ : SubquotientPresentation X₂ Y₂)
    (f : A₁ ⟶ A₂) (hPB : (Subobject.exists f).obj P₁.B ≤ P₂.B)
    (hPZ : P₁.Z ≤ (Subobject.pullback f).obj P₂.Z)
    (hQB : (Subobject.exists (P₁.descMap P₂ f hPB hPZ)).obj Q₁.B ≤ Q₂.B)
    (hQZ : Q₁.Z ≤ (Subobject.pullback (P₁.descMap P₂ f hPB hPZ)).obj Q₂.Z)
    (hB' : (Subobject.exists f).obj (P₁.trans Q₁).B ≤ (P₂.trans Q₂).B := by
      simpa using P₁.exists_preimage_le P₂ f hPB hPZ hQB)
    (hZ' : (P₁.trans Q₁).Z ≤ (Subobject.pullback f).obj (P₂.trans Q₂).Z := by
      simpa using P₁.preimage_le_pullback P₂ f hPB hPZ hQZ) :
    (P₁.trans Q₁).descMap (P₂.trans Q₂) f hB' hZ' =
      Q₁.descMap Q₂ (P₁.descMap P₂ f hPB hPZ) hQB hQZ := by
  refine (P₁.trans Q₁).descMap_eq_of_π_comp (P₂.trans Q₂) f hB' hZ' ?_
  rw [trans_π, trans_π, Category.assoc, Category.assoc, π_comp_descMap]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono Q₂.Z.arrow]
  simp only [Category.assoc, mapZ_arrow, liftZ_arrow, liftZ_arrow_assoc,
    P₁.π_comp_descMap P₂ f hPB hPZ]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono P₂.Z.arrow]
  simp only [Category.assoc, mapZ_arrow, Subobject.ofLE_arrow, Subobject.ofLE_arrow_assoc]

/-- `descMap` commutes with transporting presentations along isomorphisms via `transIso`. -/
lemma descMap_transIso (P₁ : SubquotientPresentation A₁ X₁) (P₂ : SubquotientPresentation A₂ X₂)
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (f : A₁ ⟶ A₂)
    (hB : (Subobject.exists f).obj P₁.B ≤ P₂.B)
    (hZ : P₁.Z ≤ (Subobject.pullback f).obj P₂.Z)
    (hB' : (Subobject.exists f).obj (P₁.transIso e₁).B ≤ (P₂.transIso e₂).B := by simpa using hB)
    (hZ' : (P₁.transIso e₁).Z ≤ (Subobject.pullback f).obj (P₂.transIso e₂).Z := by
      simpa using hZ) :
    (P₁.transIso e₁).descMap (P₂.transIso e₂) f hB' hZ' =
      e₁.inv ≫ P₁.descMap P₂ f hB hZ ≫ e₂.hom := by
  refine (P₁.transIso e₁).descMap_eq_of_π_comp (P₂.transIso e₂) f hB' hZ' ?_
  rw [transIso_π, transIso_π, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    P₁.π_comp_descMap_assoc P₂ f hB hZ]
  simp only [← Category.assoc]
  congr 2
  rw [← cancel_mono P₂.Z.arrow]
  simp only [Category.assoc, mapZ_arrow, Subobject.ofLE_arrow, Subobject.ofLE_arrow_assoc]

end SubquotientPresentation

end TauCeti
