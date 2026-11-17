/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subobject
import TauCeti.CategoryTheory.Subobject.Image
import TauCeti.CategoryTheory.Subobject.Pullback

/-!
# Subquotient presentations in an abelian category

A *subquotient presentation* `TauCeti.SubquotientPresentation A X` presents an object `X` inside
an ambient object `A` by a pair of subobjects `lower ≤ upper` of `A` together with an isomorphism
`cokernel (Subobject.ofLE lower upper le) ≅ X`.

In an abelian category, pulling back along the canonical epimorphism `π : (upper : C) ⟶ X` and
mapping into `A` yields an order isomorphism `Subobject X ≃o Set.Icc lower upper`, carrying meets
and joins of nonempty sets between `Subobject X` and `Subobject A`. Composition, functoriality,
and the canonical homology presentation of a `ShortComplex` are developed in
`TauCeti.CategoryTheory.Subobject.Subquotient.Comp`.

## Main definitions

* `TauCeti.SubquotientPresentation`: a presentation of `X` as a subquotient `upper / lower` of `A`.
* `TauCeti.SubquotientPresentation.π`: the canonical epimorphism `(p.upper : C) ⟶ X`.
* `TauCeti.SubquotientPresentation.refl`: the identity presentation of `A` inside `A`.
* `TauCeti.SubquotientPresentation.lift`, `TauCeti.SubquotientPresentation.desc`: lifting and
  descending subobjects between `X` and `A`.
* `TauCeti.SubquotientPresentation.orderIso`: the correspondence
  `Subobject X ≃o Set.Icc lower upper`.
* `TauCeti.SubquotientPresentation.liftTo`: the canonical epimorphism `(p.lift K : C) ⟶ (K : C)`.

## References

* [The Stacks Project, Tag 011N](https://stacks.math.columbia.edu/tag/011N)
* E. Helle and J. Rognes, *Boardman's whole-plane obstruction group for Cartan–Eilenberg systems*,
  arXiv:2408.05989 (2024), Lemma 2.2.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C]

/-- A presentation of `X` as a subquotient `upper / lower` inside an ambient object `A`. -/
structure SubquotientPresentation [HasZeroMorphisms C] [HasCokernels C] (A X : C) where
  /-- The lower subobject of `A`. -/
  lower : Subobject A
  /-- The upper subobject of `A`. -/
  upper : Subobject A
  /-- The inclusion `lower ≤ upper`. -/
  le : lower ≤ upper
  /-- The identification of the cokernel of `lower ↪ upper` with `X`. -/
  iso : cokernel (Subobject.ofLE lower upper le) ≅ X

namespace SubquotientPresentation

section Basic

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The canonical projection from `p.upper` onto `X`. -/
@[expose]
noncomputable def π {A X : C} (p : SubquotientPresentation A X) : (p.upper : C) ⟶ X :=
  cokernel.π (Subobject.ofLE p.lower p.upper p.le) ≫ p.iso.hom

instance epi_π {A X : C} (p : SubquotientPresentation A X) : Epi p.π :=
  epi_comp _ _

@[reassoc (attr := simp)]
lemma ofLE_comp_π {A X : C} (p : SubquotientPresentation A X) :
    Subobject.ofLE p.lower p.upper p.le ≫ p.π = 0 := by
  simp [π]

/-- The tautological presentation of `cokernel (Subobject.ofLE B Z h)` inside `A`. -/
noncomputable abbrev cokernelOfLE {A : C} (B Z : Subobject A) (h : B ≤ Z) :
    SubquotientPresentation A (cokernel (Subobject.ofLE B Z h)) where
  lower := B
  upper := Z
  le := h
  iso := Iso.refl _

@[simp]
lemma cokernelOfLE_π {A : C} (B Z : Subobject A) (h : B ≤ Z) :
    (cokernelOfLE B Z h).π = cokernel.π (Subobject.ofLE B Z h) := by
  dsimp [π, cokernelOfLE]
  exact Category.comp_id _

/-- Transport a subquotient presentation along an isomorphism `X ≅ Y`. -/
noncomputable abbrev transIso {A X Y : C} (p : SubquotientPresentation A X) (e : X ≅ Y) :
    SubquotientPresentation A Y where
  lower := p.lower
  upper := p.upper
  le := p.le
  iso := p.iso ≪≫ e

@[simp, reassoc]
lemma transIso_π {A X Y : C} (p : SubquotientPresentation A X) (e : X ≅ Y) :
    (p.transIso e).π = p.π ≫ e.hom := by
  simp [π, transIso]

@[simp]
lemma transIso_refl {A X : C} (p : SubquotientPresentation A X) :
    p.transIso (Iso.refl X) = p := by
  cases p
  simp [transIso]

@[simp]
lemma transIso_transIso {A X Y Z : C} (p : SubquotientPresentation A X) (e₁ : X ≅ Y)
    (e₂ : Y ≅ Z) : (p.transIso e₁).transIso e₂ = p.transIso (e₁ ≪≫ e₂) := by
  cases p
  simp [transIso, Iso.trans_assoc]

/-- The canonical isomorphism `cokernel (Subobject.ofLE ⊥ ⊤ bot_le) ≅ A`. -/
noncomputable def reflIso [HasZeroObject C] (A : C) :
    cokernel (Subobject.ofLE (⊥ : Subobject A) ⊤ bot_le) ≅ A where
  hom := cokernel.desc (Subobject.ofLE (⊥ : Subobject A) ⊤ bot_le) (⊤ : Subobject A).arrow
    (by simp)
  inv := inv (⊤ : Subobject A).arrow ≫ cokernel.π (Subobject.ofLE (⊥ : Subobject A) ⊤ bot_le)
  hom_inv_id := by
    apply coequalizer.hom_ext
    simp
  inv_hom_id := by simp

/-- The canonical identity presentation `(⊥, ⊤)` of `A` inside itself. -/
noncomputable abbrev refl [HasZeroObject C] (A : C) : SubquotientPresentation A A where
  lower := ⊥
  upper := ⊤
  le := bot_le
  iso := reflIso A

@[simp]
lemma refl_π [HasZeroObject C] (A : C) : (refl A).π = (⊤ : Subobject A).arrow := by
  dsimp [π, refl, reflIso]
  exact cokernel.π_desc _ _ _

end Basic

section NormalMono

variable [HasZeroMorphisms C] [HasKernels C] [HasCokernels C] [IsNormalMonoCategory C]

/-- The kernel subobject of `p.π` is `Subobject.mk (Subobject.ofLE p.lower p.upper p.le)`. -/
@[simp]
lemma kernelSubobject_π {A X : C} (p : SubquotientPresentation A X) :
    kernelSubobject p.π = Subobject.mk (Subobject.ofLE p.lower p.upper p.le) := by
  rw [π, kernelSubobject_comp_mono, kernelSubobject_cokernel_π]

/-- Mapping the kernel subobject of `p.π` into `A` recovers `p.lower`. -/
lemma map_kernelSubobject_π {A X : C} (p : SubquotientPresentation A X) :
    (Subobject.map p.upper.arrow).obj (kernelSubobject p.π) = p.lower := by
  rw [kernelSubobject_π, Subobject.map_mk]
  refine Subobject.eq_of_comm
    (Subobject.underlyingIso (Subobject.ofLE p.lower p.upper p.le ≫ p.upper.arrow)) ?_
  rw [← Subobject.ofLE_arrow p.le]
  exact Subobject.underlyingIso_hom_comp_eq_mk _

/-- The presented object `X` is zero if and only if `p.lower = p.upper`. -/
lemma isZero_iff {A X : C} (p : SubquotientPresentation A X) :
    IsZero X ↔ p.lower = p.upper := by
  refine ⟨fun hX ↦ ?_, fun h ↦ ?_⟩
  · have hπ : p.π = 0 := hX.eq_of_tgt _ _
    have htop : Subobject.mk (Subobject.ofLE p.lower p.upper p.le) = ⊤ := by
      rw [← p.kernelSubobject_π, hπ, kernelSubobject_zero]
    have hiso : IsIso (Subobject.ofLE p.lower p.upper p.le) := by
      have h' : IsIso (Subobject.mk (Subobject.ofLE p.lower p.upper p.le)).arrow :=
        (Subobject.isIso_arrow_iff_eq_top _).2 htop
      rw [← Subobject.underlyingIso_hom_comp_eq_mk (Subobject.ofLE p.lower p.upper p.le)] at h'
      exact IsIso.of_isIso_comp_left
        (Subobject.underlyingIso (Subobject.ofLE p.lower p.upper p.le)).hom
        (Subobject.ofLE p.lower p.upper p.le)
    exact le_antisymm p.le (Subobject.le_of_comm (inv (Subobject.ofLE p.lower p.upper p.le))
      (by simp))
  · have hiso : IsIso (Subobject.ofLE p.lower p.upper p.le) := by
      have : Subobject.ofLE p.lower p.upper p.le = (Subobject.isoOfEq p.lower p.upper h).hom := rfl
      rw [this]
      infer_instance
    have hπ0 : cokernel.π (Subobject.ofLE p.lower p.upper p.le) = 0 := by
      rw [← cancel_epi (Subobject.ofLE p.lower p.upper p.le), cokernel.condition, comp_zero]
    have hzero : IsZero (cokernel (Subobject.ofLE p.lower p.upper p.le)) := by
      rw [IsZero.iff_id_eq_zero]
      exact (cancel_epi (cokernel.π (Subobject.ofLE p.lower p.upper p.le))).1
        (by rw [hπ0, zero_comp, comp_zero])
    exact hzero.of_iso p.iso.symm

end NormalMono

section Abelian

variable [Abelian C]

/-- Two presentations of `X` inside `A` agree if they have the same upper subobject and compatible
projections `π`. -/
lemma ext {A X : C} {p q : SubquotientPresentation A X} (hupper : p.upper = q.upper)
    (hπ : (Subobject.isoOfEq p.upper q.upper hupper).hom ≫ q.π = p.π) : p = q := by
  have hlower : p.lower = q.lower := by
    rw [← p.map_kernelSubobject_π, ← q.map_kernelSubobject_π, ← hπ,
      ← Subobject.pullback_kernelSubobject, ← Subobject.exists_iso_map, ← Subobject.exists_iso_map]
    have harrow : p.upper.arrow =
        (Subobject.isoOfEq p.upper q.upper hupper).hom ≫ q.upper.arrow := by
      simp
    rw [harrow, Subobject.exists_comp, Subobject.exists_pullback_eq_of_epi]
  rcases p with ⟨l₁, u₁, h₁, e₁⟩
  rcases q with ⟨l₂, u₂, h₂, e₂⟩
  dsimp at hlower hupper hπ
  subst hlower
  subst hupper
  have he : e₁ = e₂ := by
    apply Iso.ext
    apply (cancel_epi (cokernel.π (Subobject.ofLE l₁ u₁ h₁))).1
    simpa [π] using hπ.symm
  subst he
  rfl

/-- Lift a subobject `K` of `X` along `p` to a subobject of `A` lying in `[p.lower, p.upper]`. -/
noncomputable def lift {A X : C} (p : SubquotientPresentation A X) (K : Subobject X) :
    Subobject A :=
  (Subobject.map p.upper.arrow).obj ((Subobject.pullback p.π).obj K)

/-- Descend a subobject `S` of `A` along `p` to a subobject of `X`. -/
noncomputable def desc {A X : C} (p : SubquotientPresentation A X) (S : Subobject A) :
    Subobject X :=
  (Subobject.exists p.π).obj ((Subobject.pullback p.upper.arrow).obj S)

lemma lift_monotone {A X : C} (p : SubquotientPresentation A X) : Monotone p.lift :=
  fun _ _ h ↦ (Subobject.map p.upper.arrow).monotone ((Subobject.pullback p.π).monotone h)

lemma desc_monotone {A X : C} (p : SubquotientPresentation A X) : Monotone p.desc :=
  fun _ _ h ↦ (Subobject.exists p.π).monotone ((Subobject.pullback p.upper.arrow).monotone h)

@[simp]
lemma lift_bot {A X : C} (p : SubquotientPresentation A X) : p.lift ⊥ = p.lower := by
  rw [lift, Subobject.pullback_bot, p.map_kernelSubobject_π]

@[simp]
lemma lift_top {A X : C} (p : SubquotientPresentation A X) : p.lift ⊤ = p.upper := by
  dsimp [lift]
  rw [Subobject.pullback_top, ← Subobject.exists_iso_map, Subobject.exists_eq_mk_of_mono]
  exact Subobject.eq_of_comm
    (Subobject.underlyingIso _ ≪≫ asIso (⊤ : Subobject (p.upper : C)).arrow) (by simp)

lemma lower_le_lift {A X : C} (p : SubquotientPresentation A X) (K : Subobject X) :
    p.lower ≤ p.lift K :=
  p.lift_bot ▸ p.lift_monotone bot_le

lemma lift_le_upper {A X : C} (p : SubquotientPresentation A X) (K : Subobject X) :
    p.lift K ≤ p.upper :=
  p.lift_top ▸ p.lift_monotone le_top

@[simp]
lemma desc_lift {A X : C} (p : SubquotientPresentation A X) (K : Subobject X) :
    p.desc (p.lift K) = K := by
  simp [desc, lift]

lemma lift_desc {A X : C} (p : SubquotientPresentation A X) {S : Subobject A}
    (hB : p.lower ≤ S) (hZ : S ≤ p.upper) : p.lift (p.desc S) = S := by
  have hker : kernelSubobject p.π ≤ (Subobject.pullback p.upper.arrow).obj S := by
    rw [← (Subobject.mapPullbackAdj p.upper.arrow).gc, p.map_kernelSubobject_π]
    exact hB
  dsimp [lift, desc]
  rw [Subobject.pullback_exists_eq_of_kernelSubobject_le p.π hker,
    ← Subobject.inf_eq_map_pullback, inf_eq_right.mpr hZ]

@[simp]
lemma lift_le_lift_iff {A X : C} (p : SubquotientPresentation A X) {K₁ K₂ : Subobject X} :
    p.lift K₁ ≤ p.lift K₂ ↔ K₁ ≤ K₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ p.lift_monotone h⟩
  simpa only [p.desc_lift] using p.desc_monotone h

lemma lift_injective {A X : C} (p : SubquotientPresentation A X) : Function.Injective p.lift :=
  fun _ _ h ↦ le_antisymm (p.lift_le_lift_iff.1 h.le) (p.lift_le_lift_iff.1 h.ge)

/-- The lattice correspondence between `Subobject X` and the interval `[p.lower, p.upper]` in
`Subobject A`. -/
@[expose]
noncomputable def orderIso {A X : C} (p : SubquotientPresentation A X) :
    Subobject X ≃o Set.Icc p.lower p.upper where
  toFun K := ⟨p.lift K, p.lower_le_lift K, p.lift_le_upper K⟩
  invFun S := p.desc S.1
  left_inv := p.desc_lift
  right_inv S := Subtype.ext (p.lift_desc S.2.1 S.2.2)
  map_rel_iff' := p.lift_le_lift_iff

@[simp]
lemma orderIso_apply_coe {A X : C} (p : SubquotientPresentation A X) (K : Subobject X) :
    (p.orderIso K : Subobject A) = p.lift K := rfl

@[simp]
lemma orderIso_symm_apply {A X : C} (p : SubquotientPresentation A X)
    (S : Set.Icc p.lower p.upper) : p.orderIso.symm S = p.desc S.1 := rfl

lemma le_lift_desc_of_le_upper {A X : C} (p : SubquotientPresentation A X) {T : Subobject A}
    (hT : T ≤ p.upper) : T ≤ p.lift (p.desc T) := by
  calc T = p.upper ⊓ T := (inf_eq_right.mpr hT).symm
    _ = (Subobject.map p.upper.arrow).obj ((Subobject.pullback p.upper.arrow).obj T) :=
      Subobject.inf_eq_map_pullback p.upper T
    _ ≤ p.lift (p.desc T) :=
      (Subobject.map p.upper.arrow).monotone (Subobject.le_pullback_exists p.π _)

lemma lift_desc_le_of_lower_le {A X : C} (p : SubquotientPresentation A X) {T : Subobject A}
    (hT : p.lower ≤ T) : p.lift (p.desc T) ≤ T := by
  have hker : kernelSubobject p.π ≤ (Subobject.pullback p.upper.arrow).obj T := by
    rw [← (Subobject.mapPullbackAdj p.upper.arrow).gc, p.map_kernelSubobject_π]
    exact hT
  dsimp [lift, desc]
  rw [Subobject.pullback_exists_eq_of_kernelSubobject_le p.π hker, ← Subobject.inf_eq_map_pullback]
  exact inf_le_right

/-- For a nonempty set `s` of subobjects of `X`, `W` is a greatest lower bound of `p.lift '' s`
in `Subobject A` if and only if `W ∈ [p.lower, p.upper]` and `p.desc W` is a greatest lower bound
of `s`. -/
lemma isGLB_lift_image_iff {A X : C} (p : SubquotientPresentation A X) {s : Set (Subobject X)}
    (hs : s.Nonempty) {W : Subobject A} :
    IsGLB (p.lift '' s) W ↔ p.lower ≤ W ∧ W ≤ p.upper ∧ IsGLB s (p.desc W) := by
  obtain ⟨K₀, hK₀⟩ := hs
  constructor
  · intro hW
    have hB : p.lower ≤ W := hW.2 (by rintro _ ⟨K, _, rfl⟩; exact p.lower_le_lift K)
    have hZ : W ≤ p.upper := (hW.1 ⟨K₀, hK₀, rfl⟩).trans (p.lift_le_upper K₀)
    refine ⟨hB, hZ, ?_, ?_⟩
    · intro K hK
      simpa only [p.desc_lift] using p.desc_monotone (hW.1 ⟨K, hK, rfl⟩)
    · intro L hL
      have hlift : p.lift L ≤ W := hW.2 (by rintro _ ⟨K, hK, rfl⟩; exact p.lift_monotone (hL hK))
      simpa only [p.desc_lift] using p.desc_monotone hlift
  · rintro ⟨hB, hZ, hdesc⟩
    have hW : p.lift (p.desc W) = W := p.lift_desc hB hZ
    constructor
    · rintro _ ⟨K, hK, rfl⟩
      rw [← hW]
      exact p.lift_monotone (hdesc.1 hK)
    · intro T hT
      have hTu : T ≤ p.upper := (hT ⟨K₀, hK₀, rfl⟩).trans (p.lift_le_upper K₀)
      have hTd : p.desc T ≤ p.desc W :=
        hdesc.2 fun K hK ↦ by simpa only [p.desc_lift] using p.desc_monotone (hT ⟨K, hK, rfl⟩)
      exact (p.le_lift_desc_of_le_upper hTu).trans (hW ▸ p.lift_monotone hTd)

/-- For a nonempty set `s` of subobjects of `X`, `p.lift` preserves and reflects greatest lower
bounds. -/
lemma isGLB_lift_image_lift_iff {A X : C} (p : SubquotientPresentation A X) {s : Set (Subobject X)}
    (hs : s.Nonempty) {Z : Subobject X} :
    IsGLB (p.lift '' s) (p.lift Z) ↔ IsGLB s Z := by
  rw [p.isGLB_lift_image_iff hs, p.desc_lift]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨p.lower_le_lift Z, p.lift_le_upper Z, h⟩⟩

/-- Existence of a greatest lower bound for a nonempty set `s` of subobjects of `X` is equivalent
to existence for `p.lift '' s` in `Subobject A`. -/
lemma exists_isGLB_lift_image_iff {A X : C} (p : SubquotientPresentation A X)
    {s : Set (Subobject X)} (hs : s.Nonempty) :
    (∃ W, IsGLB (p.lift '' s) W) ↔ ∃ Z, IsGLB s Z :=
  ⟨fun ⟨W, hW⟩ ↦ ⟨p.desc W, ((p.isGLB_lift_image_iff hs).1 hW).2.2⟩,
    fun ⟨Z, hZ⟩ ↦ ⟨p.lift Z, (p.isGLB_lift_image_lift_iff hs).2 hZ⟩⟩

/-- For a nonempty set `s` of subobjects of `X`, `W` is a least upper bound of `p.lift '' s` in
`Subobject A` if and only if `W ∈ [p.lower, p.upper]` and `p.desc W` is a least upper bound of
`s`. -/
lemma isLUB_lift_image_iff {A X : C} (p : SubquotientPresentation A X) {s : Set (Subobject X)}
    (hs : s.Nonempty) {W : Subobject A} :
    IsLUB (p.lift '' s) W ↔ p.lower ≤ W ∧ W ≤ p.upper ∧ IsLUB s (p.desc W) := by
  obtain ⟨K₀, hK₀⟩ := hs
  constructor
  · intro hW
    have hB : p.lower ≤ W := (p.lower_le_lift K₀).trans (hW.1 ⟨K₀, hK₀, rfl⟩)
    have hZ : W ≤ p.upper := hW.2 (by rintro _ ⟨K, _, rfl⟩; exact p.lift_le_upper K)
    refine ⟨hB, hZ, ?_, ?_⟩
    · intro K hK
      simpa only [p.desc_lift] using p.desc_monotone (hW.1 ⟨K, hK, rfl⟩)
    · intro L hL
      have hlift : W ≤ p.lift L := hW.2 (by rintro _ ⟨K, hK, rfl⟩; exact p.lift_monotone (hL hK))
      simpa only [p.desc_lift] using p.desc_monotone hlift
  · rintro ⟨hB, hZ, hdesc⟩
    have hW : p.lift (p.desc W) = W := p.lift_desc hB hZ
    constructor
    · rintro _ ⟨K, hK, rfl⟩
      rw [← hW]
      exact p.lift_monotone (hdesc.1 hK)
    · intro T hT
      have hTl : p.lower ≤ T := (p.lower_le_lift K₀).trans (hT ⟨K₀, hK₀, rfl⟩)
      have hTd : p.desc W ≤ p.desc T :=
        hdesc.2 fun K hK ↦ by simpa only [p.desc_lift] using p.desc_monotone (hT ⟨K, hK, rfl⟩)
      exact (hW ▸ p.lift_monotone hTd).trans (p.lift_desc_le_of_lower_le hTl)

/-- For a nonempty set `s` of subobjects of `X`, `p.lift` preserves and reflects least upper
bounds. -/
lemma isLUB_lift_image_lift_iff {A X : C} (p : SubquotientPresentation A X) {s : Set (Subobject X)}
    (hs : s.Nonempty) {B : Subobject X} :
    IsLUB (p.lift '' s) (p.lift B) ↔ IsLUB s B := by
  rw [p.isLUB_lift_image_iff hs, p.desc_lift]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨p.lower_le_lift B, p.lift_le_upper B, h⟩⟩

/-- Existence of a least upper bound for a nonempty set `s` of subobjects of `X` is equivalent to
existence for `p.lift '' s` in `Subobject A`. -/
lemma exists_isLUB_lift_image_iff {A X : C} (p : SubquotientPresentation A X)
    {s : Set (Subobject X)} (hs : s.Nonempty) :
    (∃ W, IsLUB (p.lift '' s) W) ↔ ∃ B, IsLUB s B :=
  ⟨fun ⟨W, hW⟩ ↦ ⟨p.desc W, ((p.isLUB_lift_image_iff hs).1 hW).2.2⟩,
    fun ⟨B, hB⟩ ↦ ⟨p.lift B, (p.isLUB_lift_image_lift_iff hs).2 hB⟩⟩

@[simp]
lemma refl_lift {A : C} (K : Subobject A) : (refl A).lift K = K := by
  dsimp only [lift]
  rw [refl_π]
  exact (Subobject.inf_eq_map_pullback (⊤ : Subobject A) K).symm.trans (top_inf_eq K)

@[simp]
lemma transIso_lift {A X Y : C} (p : SubquotientPresentation A X) (e : X ≅ Y) (K : Subobject Y) :
    (p.transIso e).lift K = p.lift ((Subobject.pullback e.hom).obj K) := by
  dsimp only [lift]
  rw [transIso_π, Subobject.pullback_comp]

lemma factors_ofLE_comp_π {A X : C} (p : SubquotientPresentation A X) (K : Subobject X) :
    K.Factors (Subobject.ofLE (p.lift K) p.upper (p.lift_le_upper K) ≫ p.π) := by
  rw [← pullback_factors_iff]
  have hle : Subobject.mk (Subobject.ofLE (p.lift K) p.upper (p.lift_le_upper K)) ≤
      (Subobject.pullback p.π).obj K := by
    rw [← Subobject.exists_le_exists_iff_of_mono p.upper.arrow, Subobject.exists_iso_map,
      Subobject.map_mk]
    have heq : Subobject.mk (Subobject.ofLE (p.lift K) p.upper (p.lift_le_upper K) ≫
        p.upper.arrow) = p.lift K :=
      Subobject.eq_of_comm (Subobject.underlyingIso _) (by
        rw [← Subobject.ofLE_arrow (p.lift_le_upper K)]
        exact Subobject.underlyingIso_hom_comp_eq_mk _)
    rw [heq]
    exact le_rfl
  have hfac : ((Subobject.underlyingIso _).inv ≫ Subobject.ofLE _ _ hle) ≫
      ((Subobject.pullback p.π).obj K).arrow =
      Subobject.ofLE (p.lift K) p.upper (p.lift_le_upper K) := by
    simp
  exact hfac ▸ Subobject.factors_comp_arrow _

/-- The canonical epimorphism `(p.lift K : C) ⟶ (K : C)` restricting `p.π` to `p.lift K`. -/
noncomputable def liftTo {A X : C} (p : SubquotientPresentation A X) (K : Subobject X) :
    (p.lift K : C) ⟶ (K : C) :=
  K.factorThru (Subobject.ofLE (p.lift K) p.upper (p.lift_le_upper K) ≫ p.π)
    (p.factors_ofLE_comp_π K)

@[reassoc (attr := simp)]
lemma liftTo_arrow {A X : C} (p : SubquotientPresentation A X) (K : Subobject X) :
    p.liftTo K ≫ K.arrow = Subobject.ofLE (p.lift K) p.upper (p.lift_le_upper K) ≫ p.π :=
  K.factorThru_arrow _ _

@[reassoc (attr := simp)]
lemma ofLE_comp_liftTo {A X : C} (p : SubquotientPresentation A X) {K₁ K₂ : Subobject X}
    (h : K₁ ≤ K₂) :
    Subobject.ofLE (p.lift K₁) (p.lift K₂) (p.lift_monotone h) ≫ p.liftTo K₂ =
      p.liftTo K₁ ≫ Subobject.ofLE K₁ K₂ h := by
  rw [← cancel_mono K₂.arrow]
  simp [Subobject.ofLE_comp_ofLE_assoc]

instance epi_liftTo {A X : C} (p : SubquotientPresentation A X) (K : Subobject X) :
    Epi (p.liftTo K) := by
  set Q := (Subobject.pullback p.π).obj K
  have heq : p.lift K = Subobject.mk (Q.arrow ≫ p.upper.arrow) := by
    dsimp [lift, Q]
    rw [← Subobject.exists_iso_map, Subobject.exists_eq_mk_of_mono]
  let e : (p.lift K : C) ≅ (Q : C) :=
    Subobject.isoOfEq _ _ heq ≪≫ Subobject.underlyingIso (Q.arrow ≫ p.upper.arrow)
  have hfac : p.liftTo K = e.hom ≫ Subobject.pullbackπ p.π K := by
    rw [← cancel_mono K.arrow, liftTo_arrow, Category.assoc, (Subobject.isPullback p.π K).w,
      ← Category.assoc]
    congr 1
    rw [← cancel_mono p.upper.arrow]
    dsimp [e]
    rw [Subobject.ofLE_arrow, Category.assoc, Category.assoc,
      Subobject.underlyingIso_hom_comp_eq_mk, Subobject.isoOfEq_hom, Subobject.ofLE_arrow]
  rw [hfac]
  exact epi_comp _ _

/-- A morphism `f : W ⟶ A` factors through `p.lift K` if and only if it factors through `p.upper`
and its composite with `p.π` factors through `K`. -/
lemma factors_lift_iff {A X W : C} (p : SubquotientPresentation A X) (K : Subobject X)
    (f : W ⟶ A) :
    (p.lift K).Factors f ↔
      ∃ hf : p.upper.Factors f, K.Factors (p.upper.factorThru f hf ≫ p.π) := by
  constructor
  · intro hfK
    have hf : p.upper.Factors f := Subobject.factors_of_le _ (p.lift_le_upper K) hfK
    refine ⟨hf, ?_⟩
    have hfac : ((p.lift K).factorThru f hfK ≫ p.liftTo K) ≫ K.arrow =
        p.upper.factorThru f hf ≫ p.π := by
      rw [Category.assoc, liftTo_arrow, ← Category.assoc]
      congr 1
      rw [← cancel_mono p.upper.arrow]
      simp
    exact hfac ▸ Subobject.factors_comp_arrow _
  · rintro ⟨hf, hK⟩
    have hQ : ((Subobject.pullback p.π).obj K).Factors (p.upper.factorThru f hf) :=
      (pullback_factors_iff p.π K _).2 hK
    have heq : p.lift K =
        Subobject.mk (((Subobject.pullback p.π).obj K).arrow ≫ p.upper.arrow) := by
      dsimp [lift]
      rw [← Subobject.exists_iso_map, Subobject.exists_eq_mk_of_mono]
    have hfac : (((Subobject.pullback p.π).obj K).factorThru _ hQ ≫
        (Subobject.underlyingIso _).inv ≫ (Subobject.isoOfEq _ _ heq).inv) ≫ (p.lift K).arrow =
        f := by
      simp [Category.assoc]
    exact hfac ▸ Subobject.factors_comp_arrow _

end Abelian

end SubquotientPresentation

end TauCeti
