/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Order.Bounds.Image
public import Mathlib.Order.Bounds.OrderIso
public import TauCeti.CategoryTheory.Subobject.Image

/-!
# Indexed meets, joins, and preimage-image identities for subobjects

This file provides lattice and categorical properties of `Subobject` needed for subquotient
presentations and spectral sequence towers, without requiring `[WellPowered C]`:

* `CategoryTheory.Subobject.kernelSubobject_cokernel_π` and
  `CategoryTheory.Subobject.factors_iff_comp_cokernel_π_eq_zero`: in an abelian category, a
  monomorphism is its own kernel of cokernel, so factoring through a subobject `S` is equivalent to
  vanishing after `cokernel.π S.arrow`.
* `CategoryTheory.Subobject.exists_obj_pullback_obj_of_epi` and
  `CategoryTheory.Subobject.pullback_obj_exists_obj_of_kernelSubobject_le`: for an epimorphism
  `π : X ⟶ Y` in an abelian category, pullback along `π` and direct image along `π` are inverse
  between `Subobject Y` and `{S : Subobject X | kernelSubobject π ≤ S}`.
* `CategoryTheory.Subobject.isLUB_exists_image` and
  `CategoryTheory.Subobject.isGLB_pullback_image`: direct image preserves least upper bounds and
  pullback preserves greatest lower bounds.
* `CategoryTheory.Subobject.isLUB_range_imageSubobject_sigmaDesc` and
  `CategoryTheory.Subobject.isGLB_range_kernelSubobject_piLift`: indexed joins and meets of a
  family `f : ι → Subobject A` as the image of the coproduct map and the kernel of the map into the
  product of cokernels.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

section Interval

variable {α : Type*} [Lattice α] {B Z : α}

/-- For a nonempty subset `t` of an interval `Set.Icc B Z` in a lattice, an element of the interval
is a greatest lower bound in `Set.Icc B Z` if and only if its underlying element is a greatest lower
bound in the ambient lattice. -/
lemma isGLB_Icc_iff_ambient {t : Set (Set.Icc B Z)} (ht : t.Nonempty) {x : Set.Icc B Z} :
    IsGLB t x ↔ IsGLB ((↑) '' t : Set α) x.1 := by
  refine ⟨fun hx ↦ ⟨?_, ?_⟩, IsGLB.of_image Subtype.coe_le_coe⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact Subtype.coe_le_coe.mpr (hx.1 hy)
  · intro a ha
    obtain ⟨y₀, hy₀⟩ := ht
    have hBa : B ≤ a ⊔ B := le_sup_right
    have haZ : a ⊔ B ≤ Z := (sup_le (ha ⟨y₀, hy₀, rfl⟩) y₀.2.1).trans y₀.2.2
    have hlb : (⟨a ⊔ B, hBa, haZ⟩ : Set.Icc B Z) ∈ lowerBounds t := fun y hy ↦
      Subtype.coe_le_coe.mp (sup_le (ha ⟨y, hy, rfl⟩) y.2.1)
    exact le_sup_left.trans (Subtype.coe_le_coe.mpr (hx.2 hlb))

/-- For a nonempty subset `t` of an interval `Set.Icc B Z` in a lattice, an element of the interval
is a least upper bound in `Set.Icc B Z` if and only if its underlying element is a least upper
bound in the ambient lattice. -/
lemma isLUB_Icc_iff_ambient {t : Set (Set.Icc B Z)} (ht : t.Nonempty) {x : Set.Icc B Z} :
    IsLUB t x ↔ IsLUB ((↑) '' t : Set α) x.1 := by
  refine ⟨fun hx ↦ ⟨?_, ?_⟩, IsLUB.of_image Subtype.coe_le_coe⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact Subtype.coe_le_coe.mpr (hx.1 hy)
  · intro a ha
    obtain ⟨y₀, hy₀⟩ := ht
    have hBa : B ≤ a ⊓ Z := le_inf (y₀.2.1.trans (ha ⟨y₀, hy₀, rfl⟩)) (y₀.2.1.trans y₀.2.2)
    have haZ : a ⊓ Z ≤ Z := inf_le_right
    have hub : (⟨a ⊓ Z, hBa, haZ⟩ : Set.Icc B Z) ∈ upperBounds t := fun y hy ↦
      Subtype.coe_le_coe.mp (le_inf (ha ⟨y, hy, rfl⟩) y.2.2)
    exact (Subtype.coe_le_coe.mpr (hx.2 hub)).trans inf_le_left

end Interval

end TauCeti

namespace CategoryTheory.Subobject

universe w v u

section Basic

variable {C : Type u} [Category.{v} C] {X Y : C}

/-- Inclusion between subobjects is equivalent to the smaller arrow factoring through the larger
subobject. -/
lemma le_iff_factors (P Q : Subobject Y) : P ≤ Q ↔ Q.Factors P.arrow :=
  ⟨fun h ↦ factors_of_le P.arrow h (factors_self P), le_of_factors⟩

/-- Direct image along `f` preserves least upper bounds of sets of subobjects. -/
lemma isLUB_exists_image [HasImages C] [HasPullbacks C] (f : X ⟶ Y) {s : Set (Subobject X)}
    {S : Subobject X} (hs : IsLUB s S) :
    IsLUB ((«exists» f).obj '' s) ((«exists» f).obj S) :=
  (existsPullbackAdj f).gc.isLUB_l_image hs

/-- Pullback along `f` preserves greatest lower bounds of sets of subobjects. -/
lemma isGLB_pullback_image [HasImages C] [HasPullbacks C] (f : X ⟶ Y) {s : Set (Subobject Y)}
    {S : Subobject Y} (hs : IsGLB s S) :
    IsGLB ((pullback f).obj '' s) ((pullback f).obj S) :=
  (existsPullbackAdj f).gc.isGLB_u_image hs

/-- The least upper bound of an indexed family `f : ι → Subobject Y` is the image subobject of the
induced morphism from the coproduct `∐ i, (f i : C)`. -/
lemma isLUB_range_imageSubobject_sigmaDesc {ι : Type w} [HasCoproductsOfShape ι C] [HasImages C]
    (f : ι → Subobject Y) :
    IsLUB (Set.range f) (imageSubobject (Sigma.desc fun i ↦ (f i).arrow)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact le_of_comm (Sigma.ι (fun i ↦ (f i : C)) i ≫
      factorThruImageSubobject (Sigma.desc fun i ↦ (f i).arrow)) (by simp)
  · intro T hT
    have hle : ∀ i, f i ≤ T := fun i ↦ hT ⟨i, rfl⟩
    exact le_of_comm
      ((imageSubobjectIso (Sigma.desc fun i ↦ (f i).arrow)).hom ≫
        image.lift ⟨(T : C), T.arrow, Sigma.desc fun i ↦ ofLE (f i) T (hle i), by ext; simp⟩)
      (by rw [Category.assoc, image.lift_fac, imageSubobject_arrow])

/-- Along a monomorphism `f`, direct image `Subobject.exists f` agrees with `Subobject.map f`. -/
lemma exists_obj_eq_map_obj_of_mono [HasImages C] (f : X ⟶ Y) [Mono f] (S : Subobject X) :
    («exists» f).obj S = (map f).obj S := by
  conv_rhs => rw [← mk_arrow S]
  rw [exists_eq_imageSubobject, imageSubobject_mono, map_mk]

end Basic

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {W X Y : C}

/-- In an abelian category, `kernelSubobject g = ⊤` if and only if `g = 0`. -/
@[simp]
lemma kernelSubobject_eq_top_iff (g : X ⟶ Y) :
    kernelSubobject g = ⊤ ↔ g = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; exact kernelSubobject_zero⟩
  have htop : (⊤ : Subobject X).arrow ≫ g = 0 := by
    rw [← h]
    exact kernelSubobject_arrow_comp g
  exact (cancel_epi (⊤ : Subobject X).arrow).mp (by rw [htop, comp_zero])

/-- In an abelian category, `imageSubobject f = ⊥` if and only if `f = 0`. -/
@[simp]
lemma imageSubobject_eq_bot_iff (f : X ⟶ Y) :
    imageSubobject f = ⊥ ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; exact imageSubobject_zero⟩
  have hz : IsZero (imageSubobject f : C) := by
    rw [h]
    exact IsZero.of_iso (isZero_zero C) botCoeIsoZero
  rw [← imageSubobject_arrow_comp f, hz.eq_of_tgt (factorThruImageSubobject f) 0, zero_comp]

/-- In an abelian category, the kernel subobject of `cokernel.π m` for a monomorphism `m` is
`Subobject.mk m`. -/
@[simp]
lemma kernelSubobject_cokernel_π (m : X ⟶ Y) [Mono m] :
    kernelSubobject (cokernel.π m) = mk m :=
  le_antisymm
    (le_mk_of_comm (Abelian.monoLift m _ (kernelSubobject_arrow_comp _))
      (Abelian.monoLift_comp _ _ _))
    (mk_le_mk_of_comm (kernel.lift (cokernel.π m) m (cokernel.condition m)) (by simp))

/-- In an abelian category, the kernel subobject of `cokernel.π S.arrow` is `S`. -/
lemma kernelSubobject_cokernel_π_arrow (S : Subobject Y) :
    kernelSubobject (cokernel.π S.arrow) = S := by
  rw [kernelSubobject_cokernel_π, mk_arrow]

/-- In an abelian category, a morphism `g : W ⟶ Y` factors through a subobject `S : Subobject Y`
if and only if its composite with `cokernel.π S.arrow` is zero. -/
lemma factors_iff_comp_cokernel_π_eq_zero (S : Subobject Y) (g : W ⟶ Y) :
    S.Factors g ↔ g ≫ cokernel.π S.arrow = 0 := by
  conv_lhs => rw [← kernelSubobject_cokernel_π_arrow S]
  exact kernelSubobject_factors_iff _ _

/-- In an abelian category, `P ≤ Q` in `Subobject Y` if and only if `P.arrow ≫ cokernel.π Q.arrow`
vanishes. -/
lemma le_iff_arrow_comp_cokernel_π_eq_zero (P Q : Subobject Y) :
    P ≤ Q ↔ P.arrow ≫ cokernel.π Q.arrow = 0 := by
  rw [le_iff_factors, factors_iff_comp_cokernel_π_eq_zero]

/-- In an abelian category, the direct image along an epimorphism `π : X ⟶ Y` of the pullback of a
subobject `K : Subobject Y` is `K`. -/
@[simp]
lemma exists_obj_pullback_obj_of_epi (π : X ⟶ Y) [Epi π] (K : Subobject Y) :
    («exists» π).obj ((pullback π).obj K) = K := by
  rw [exists_eq_imageSubobject, ← (isPullback π K).w, imageSubobject_comp_eq_of_epi,
    imageSubobject_mono, mk_arrow]

/-- In an abelian category, the pullback along an epimorphism `π : X ⟶ Y` of the direct image of a
subobject `S : Subobject X` containing `kernelSubobject π` is `S`. -/
lemma pullback_obj_exists_obj_of_kernelSubobject_le (π : X ⟶ Y) [Epi π] {S : Subobject X}
    (hS : kernelSubobject π ≤ S) :
    (pullback π).obj ((«exists» π).obj S) = S := by
  refine le_antisymm ?_ ((existsPullbackAdj π).gc.le_u_l S)
  rw [le_iff_arrow_comp_cokernel_π_eq_zero]
  have hker : kernel.ι π ≫ cokernel.π S.arrow = 0 := by
    rw [← kernelSubobject_arrow', Category.assoc,
      (le_iff_arrow_comp_cokernel_π_eq_zero _ _).mp hS, comp_zero]
  let q : Y ⟶ cokernel S.arrow := Abelian.epiDesc π (cokernel.π S.arrow) hker
  have hq : π ≫ q = cokernel.π S.arrow := Abelian.comp_epiDesc π (cokernel.π S.arrow) hker
  have him : ((«exists» π).obj S).arrow ≫ q = 0 := by
    rw [exists_eq_imageSubobject]
    exact imageSubobject_arrow_comp_eq_zero (by rw [Category.assoc, hq, cokernel.condition])
  rw [← hq, ← Category.assoc, ← (isPullback π _).w, Category.assoc, him, comp_zero]

/-- In an abelian category, the greatest lower bound of an indexed family `f : ι → Subobject Y` is
the kernel subobject of the canonical morphism from `Y` into `∏ᶜ i, cokernel (f i).arrow`. -/
lemma isGLB_range_kernelSubobject_piLift {ι : Type w} [HasProductsOfShape ι C]
    (f : ι → Subobject Y) :
    IsGLB (Set.range f) (kernelSubobject (Pi.lift fun i ↦ cokernel.π (f i).arrow)) := by
  rw [isGLB_iff_le_iff]
  intro T
  rw [le_iff_factors, kernelSubobject_factors_iff, mem_lowerBounds]
  constructor
  · rintro h _ ⟨i, rfl⟩
    rw [le_iff_arrow_comp_cokernel_π_eq_zero]
    simpa using h =≫ Pi.π (fun i ↦ cokernel (f i).arrow) i
  · intro h
    refine limit.hom_ext fun ⟨i⟩ ↦ ?_
    simpa using (le_iff_arrow_comp_cokernel_π_eq_zero _ _).mp (h (f i) ⟨i, rfl⟩)

end Abelian

end CategoryTheory.Subobject
