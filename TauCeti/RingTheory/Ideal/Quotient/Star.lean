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
conjugate scalar multiplication when the original ring is a star algebra. This allows
star-stable trace radicals to be divided out before introducing any norm.

Star-algebra homomorphisms and equivalences that respect star-stable two-sided ideals
descend to the quotients as `Ideal.quotientMapStarAlg` and `Ideal.quotientEquivStarAlg`.
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

section Maps

variable {R B : Type*} [CommSemiring R] [Ring A] [StarRing A] [Algebra R A]
  [Ring B] [StarRing B] [Algebra R B] {I : Ideal A} (J : Ideal B)
  [I.IsTwoSided] [I.IsStar] [J.IsTwoSided] [J.IsStar]

/-- The `⋆`-algebra homomorphism `A ⧸ I →⋆ₐ[R] B ⧸ J` induced by `f : A →⋆ₐ[R] B`
when `I ≤ J.comap f`. -/
def quotientMapStarAlg (f : A →⋆ₐ[R] B) (hIJ : I ≤ J.comap f) :
    A ⧸ I →⋆ₐ[R] B ⧸ J :=
  { Ideal.quotientMapₐ J f.toAlgHom hIJ with
    map_star' := fun x ↦ by
      obtain ⟨a, rfl⟩ := Quotient.mk_surjective x
      exact congrArg (Quotient.mk J) (map_star f a) }

/-- Forgetting star preservation recovers `Ideal.quotientMapₐ`. -/
@[simp]
theorem quotientMapStarAlg_toAlgHom (f : A →⋆ₐ[R] B) (hIJ : I ≤ J.comap f) :
    (quotientMapStarAlg J f hIJ).toAlgHom = Ideal.quotientMapₐ J f.toAlgHom hIJ := (rfl)

/-- Action of `quotientMapStarAlg` on a quotient representative. -/
@[simp]
theorem quotientMapStarAlg_mk (f : A →⋆ₐ[R] B) (hIJ : I ≤ J.comap f) (a : A) :
    quotientMapStarAlg J f hIJ (Quotient.mk I a) = Quotient.mk J (f a) := (rfl)

variable (I) in
/-- The `⋆`-algebra equivalence `(A ⧸ I) ≃⋆ₐ[R] B ⧸ J` induced by `f : A ≃⋆ₐ[R] B`
when `J = I.map f`. -/
def quotientEquivStarAlg (f : A ≃⋆ₐ[R] B) (hIJ : J = I.map (f : A →+* B)) :
    (A ⧸ I) ≃⋆ₐ[R] B ⧸ J :=
  { (Ideal.quotientEquivAlg I J f.toAlgEquiv hIJ).toRingEquiv with
    map_smul' := fun r x ↦ map_smul (Ideal.quotientEquivAlg I J f.toAlgEquiv hIJ) r x
    map_star' := fun x ↦ by
      obtain ⟨a, rfl⟩ := Quotient.mk_surjective x
      exact congrArg (Quotient.mk J) (map_star f a) }

/-- Forgetting star preservation recovers `Ideal.quotientEquivAlg`. -/
@[simp]
theorem quotientEquivStarAlg_toAlgEquiv (f : A ≃⋆ₐ[R] B) (hIJ : J = I.map (f : A →+* B)) :
    (quotientEquivStarAlg I J f hIJ).toAlgEquiv = Ideal.quotientEquivAlg I J f.toAlgEquiv hIJ := by
  ext x
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective x
  rfl

/-- Action of `quotientEquivStarAlg` on a quotient representative. -/
@[simp]
theorem quotientEquivStarAlg_mk (f : A ≃⋆ₐ[R] B) (hIJ : J = I.map (f : A →+* B)) (a : A) :
    quotientEquivStarAlg I J f hIJ (Quotient.mk I a) = Quotient.mk J (f a) := (rfl)

/-- Action of `(quotientEquivStarAlg I J f hIJ).symm` on a quotient representative. -/
@[simp]
theorem quotientEquivStarAlg_symm_mk (f : A ≃⋆ₐ[R] B) (hIJ : J = I.map (f : A →+* B)) (b : B) :
    (quotientEquivStarAlg I J f hIJ).symm (Quotient.mk J b) = Quotient.mk I (f.symm b) := (rfl)

end Maps

end Ideal
