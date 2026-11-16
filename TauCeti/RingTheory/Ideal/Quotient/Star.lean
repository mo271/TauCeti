/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Star on ideal quotients

A two-sided ideal stable under star gives a star ring quotient. The quotient inherits
conjugate scalar multiplication when the original ring is a star algebra, and star-preserving
algebra homomorphisms descend to star algebra homomorphisms between quotients whenever the
source ideal maps into the target ideal. This allows star-stable trace radicals to be divided
out and compared before introducing any norm.
-/

public section

namespace Ideal

variable {A : Type*}

/-- An ideal is star-stable if it contains the adjoint of each of its elements. -/
class IsStar [Semiring A] [Star A] (I : Ideal A) : Prop where
  /-- Closure under the involution. -/
  star_mem : ∀ {a : A}, a ∈ I → star a ∈ I

section Membership

variable [Semiring A] [InvolutiveStar A] (I : Ideal A) [I.IsStar]

/-- Membership in a star-stable ideal is unchanged by the involution. -/
@[simp]
theorem star_mem_iff {a : A} : star a ∈ I ↔ a ∈ I :=
  ⟨fun h ↦ by simpa using IsStar.star_mem h, IsStar.star_mem⟩

end Membership

/-- Preimages of star-stable ideals along star-preserving ring homomorphisms are star-stable. -/
theorem IsStar.comap {B : Type*} [Semiring A] [Star A] [Semiring B] [Star B]
    {J : Ideal B} [J.IsStar] {F : Type*} [FunLike F A B] [RingHomClass F A B] [StarHomClass F A B]
    (f : F) : (J.comap f).IsStar where
  star_mem ha := by
    rw [mem_comap, map_star]
    exact IsStar.star_mem ha

namespace Quotient

variable [Ring A] [StarRing A] (I : Ideal A) [I.IsTwoSided] [I.IsStar]

instance instStar : Star (A ⧸ I) where
  star := QuotientAddGroup.lift I.toAddSubgroup
    ((Ideal.Quotient.mk I).toAddMonoidHom.comp (starAddEquiv : A ≃+ A).toAddMonoidHom)
    (fun _ ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (IsStar.star_mem ha))

/-- Taking adjoints commutes with passing to the quotient. -/
@[simp]
theorem star_mk (a : A) : star (mk I a) = mk I (star a) := (rfl)

instance instStarRing : StarRing (A ⧸ I) where
  star_involutive x := by
    obtain ⟨a, rfl⟩ := mk_surjective x
    simp
  star_mul x y := by
    obtain ⟨a, rfl⟩ := mk_surjective x
    obtain ⟨b, rfl⟩ := mk_surjective y
    simp only [← map_mul, star_mk, star_mul]
  star_add x y := by
    obtain ⟨a, rfl⟩ := mk_surjective x
    obtain ⟨b, rfl⟩ := mk_surjective y
    simp only [← map_add, star_mk, star_add]

instance {R : Type*} [CommSemiring R] [StarRing R] [Algebra R A] [StarModule R A] :
    StarModule R (A ⧸ I) where
  star_smul r x := by
    obtain ⟨a, rfl⟩ := mk_surjective x
    calc
      star (r • mk I a) = star (mk I (r • a)) := by
        rw [← mkₐ_eq_mk R, map_smul]
      _ = mk I (star r • star a) := by rw [star_mk, star_smul]
      _ = star r • star (mk I a) := by
        rw [star_mk, ← mkₐ_eq_mk R, map_smul]

end Quotient

section Hom

variable {R B : Type*} [CommSemiring R] [Ring A] [StarRing A] [Algebra R A]
  [Ring B] [StarRing B] [Algebra R B] {I : Ideal A} (J : Ideal B)
  [I.IsTwoSided] [I.IsStar] [J.IsTwoSided] [J.IsStar]

/-- The star algebra homomorphism `A ⧸ I →⋆ₐ[R] B ⧸ J` induced by `f : A →⋆ₐ[R] B`
when `I ≤ J.comap f.toAlgHom`. -/
def quotientStarAlgHom (f : A →⋆ₐ[R] B) (hIJ : I ≤ J.comap f.toAlgHom) :
    A ⧸ I →⋆ₐ[R] B ⧸ J :=
  { quotientMapₐ J f.toAlgHom hIJ with
    map_star' x := by
      obtain ⟨a, rfl⟩ := Quotient.mk_surjective x
      -- Fold `AlgHom.toFun` back to `⇑(quotientMapₐ ...)` so `quotient_map_mkₐ` applies.
      change quotientMapₐ J f.toAlgHom hIJ (star (Quotient.mk I a)) =
        star (quotientMapₐ J f.toAlgHom hIJ (Quotient.mk I a))
      rw [Quotient.star_mk, quotient_map_mkₐ, quotient_map_mkₐ, Quotient.mkₐ_eq_mk,
        Quotient.star_mk]
      exact congrArg (Quotient.mk J) (map_star f a) }

/-- Forgetting star compatibility recovers `Ideal.quotientMapₐ`. -/
@[simp]
theorem toAlgHom_quotientStarAlgHom (f : A →⋆ₐ[R] B) (hIJ : I ≤ J.comap f.toAlgHom) :
    (quotientStarAlgHom J f hIJ).toAlgHom = quotientMapₐ J f.toAlgHom hIJ := (rfl)

/-- Evaluating `Ideal.quotientStarAlgHom` on a quotient representative applies `f`. -/
@[simp]
theorem quotientStarAlgHom_mk (f : A →⋆ₐ[R] B) (hIJ : I ≤ J.comap f.toAlgHom) (a : A) :
    quotientStarAlgHom J f hIJ (Quotient.mk I a) = Quotient.mk J (f a) :=
  quotient_map_mkₐ J f.toAlgHom hIJ

/-- `Ideal.quotientStarAlgHom` is injective when `J.comap f.toAlgHom ≤ I`. -/
theorem quotientStarAlgHom_injective (f : A →⋆ₐ[R] B) {hIJ : I ≤ J.comap f.toAlgHom}
    (hJI : J.comap f.toAlgHom ≤ I) :
    Function.Injective (quotientStarAlgHom J f hIJ) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective y
  rw [quotientStarAlgHom_mk, quotientStarAlgHom_mk, Quotient.eq] at hxy
  exact Quotient.eq.mpr (hJI (mem_comap.mpr (by simpa only [StarAlgHom.coe_toAlgHom, map_sub]
    using hxy)))

/-- `Ideal.quotientStarAlgHom` is surjective when `f` is surjective. -/
theorem quotientStarAlgHom_surjective (f : A →⋆ₐ[R] B) (hIJ : I ≤ J.comap f.toAlgHom)
    (hf : Function.Surjective f) :
    Function.Surjective (quotientStarAlgHom J f hIJ) := fun y ↦ by
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective y
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨Quotient.mk I a, quotientStarAlgHom_mk J f hIJ a⟩

/-- A surjective star algebra homomorphism `f : A →⋆ₐ[R] B` with `I = J.comap f.toAlgHom` induces
a star algebra isomorphism `(A ⧸ I) ≃⋆ₐ[R] B ⧸ J`. -/
noncomputable def quotientStarAlgEquivOfSurjective (f : A →⋆ₐ[R] B)
    (hIJ : I = J.comap f.toAlgHom) (hf : Function.Surjective f) :
    (A ⧸ I) ≃⋆ₐ[R] B ⧸ J :=
  StarAlgEquiv.ofBijective (quotientStarAlgHom J f hIJ.le)
    ⟨quotientStarAlgHom_injective J f hIJ.ge, quotientStarAlgHom_surjective J f hIJ.le hf⟩

/-- Evaluating `Ideal.quotientStarAlgEquivOfSurjective` on a quotient representative applies `f`.
-/
@[simp]
theorem quotientStarAlgEquivOfSurjective_mk (f : A →⋆ₐ[R] B)
    (hIJ : I = J.comap f.toAlgHom) (hf : Function.Surjective f) (a : A) :
    quotientStarAlgEquivOfSurjective J f hIJ hf (Quotient.mk I a) = Quotient.mk J (f a) :=
  quotientStarAlgHom_mk J f hIJ.le a

end Hom

end Ideal
