/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.Quotient.Star
public import TauCeti.RingTheory.TraceFunctional.Radical
public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Sesquilinear trace forms

A linear functional on a star algebra defines the sesquilinear form
`(x, y) ↦ τ (star x * y)`, conjugate-linear in the first variable. If the functional preserves
star, this form is Hermitian. If it is also tracial, its multiplication-pairing radical is
star-stable and equals the kernel of the sesquilinear form, so the quotient trace preserves star
and surjective trace-preserving star algebra maps induce star algebra isomorphisms on the
trace-radical quotients. No positivity is assumed: these facts apply before deciding whether a
trace gives a Hilbert space after quotient and completion.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, for sesquilinear trace forms and
  trace radicals of Temperley–Lieb algebras.
-/

public section

namespace LinearMap

section Semiring

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A]
  [Algebra R A] [StarModule R A]

/-- The sesquilinear form of a linear functional on a star algebra, conjugate-linear in the
first argument. Hermitian symmetry requires that the functional preserve star. -/
def traceSesqForm (τ : A →ₗ[R] R) : A →ₗ⋆[R] A →ₗ[R] R :=
  ((LinearMap.mul R A).compr₂ τ).comp (starLinearEquiv R).toLinearMap

/-- Evaluation of the sesquilinear trace form. -/
@[simp]
theorem traceSesqForm_apply (τ : A →ₗ[R] R) (x y : A) :
    τ.traceSesqForm x y = τ (star x * y) := (rfl)

/-- A star-preserving functional has a Hermitian sesquilinear trace form. Traciality is not
needed for this symmetry. -/
theorem traceSesqForm_isSymm (τ : A →ₗ[R] R) (hstar : ∀ x, τ (star x) = star (τ x)) :
    τ.traceSesqForm.IsSymm := by
  constructor
  intro x y
  simp only [traceSesqForm_apply, starRingEnd_apply, ← hstar, star_mul, star_star]

end Semiring

section StarRingR

variable {R A : Type*} [CommRing R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]

/-- The multiplication-pairing radical of a star-preserving trace is stable under star. -/
theorem star_mem_traceRadical_iff (τ : A →ₗ[R] R)
    (hτ : ∀ x y, τ (x * y) = τ (y * x)) (hstar : ∀ x, τ (star x) = star (τ x)) {x : A} :
    star x ∈ τ.traceRadical hτ ↔ x ∈ τ.traceRadical hτ := by
  have hmem {a : A} (ha : a ∈ τ.traceRadical hτ) : star a ∈ τ.traceRadical hτ := by
    rw [mem_traceRadical] at ha ⊢
    intro y
    rw [hτ, ← star_star y, ← star_mul, hstar, ha, star_zero]
  exact ⟨fun hx ↦ by simpa only [star_star] using hmem hx, hmem⟩

/-- Bundled `Ideal.IsStar` witness for the trace radical of a star-preserving tracial functional.
Kept as a theorem rather than a global instance since `hstar` is not recoverable from `τ` alone. -/
theorem isStar_traceRadical (τ : A →ₗ[R] R)
    (hτ : ∀ x y, τ (x * y) = τ (y * x)) (hstar : ∀ x, τ (star x) = star (τ x)) :
    (τ.traceRadical hτ).IsStar where
  star_mem ha := (τ.star_mem_traceRadical_iff hτ hstar).mpr ha

/-- For a star-preserving trace, the left kernel of its sesquilinear form is the underlying
coefficient submodule of its multiplication-pairing radical. -/
theorem ker_traceSesqForm [StarModule R A] (τ : A →ₗ[R] R)
    (hτ : ∀ x y, τ (x * y) = τ (y * x)) (hstar : ∀ x, τ (star x) = star (τ x)) :
    ker τ.traceSesqForm = (τ.traceRadical hτ).restrictScalars R := by
  ext x
  rw [mem_ker, LinearMap.ext_iff, Submodule.restrictScalars_mem,
    ← τ.star_mem_traceRadical_iff hτ hstar, mem_traceRadical]
  simp [traceSesqForm_apply]

/-- When a tracial functional preserves star, its induced quotient trace also preserves star. -/
@[simp]
theorem quotientTrace_star (τ : A →ₗ[R] R) (hτ : ∀ x y, τ (x * y) = τ (y * x))
    [(τ.traceRadical hτ).IsStar] (hstar : ∀ x, τ (star x) = star (τ x))
    (x : A ⧸ τ.traceRadical hτ) :
    τ.quotientTrace hτ (star x) = star (τ.quotientTrace hτ x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.star_mk, quotientTrace_mk, hstar]

end StarRingR

section QuotientEquiv

variable {R A B : Type*} [CommRing R] [Ring A] [StarRing A] [Algebra R A]
  [Ring B] [StarRing B] [Algebra R B]
  {τ : A →ₗ[R] R} (hτ : ∀ x y, τ (x * y) = τ (y * x))
  {σ : B →ₗ[R] R} (hσ : ∀ x y, σ (x * y) = σ (y * x))
  [(τ.traceRadical hτ).IsStar] [(σ.traceRadical hσ).IsStar]

/-- A surjective trace-preserving star algebra map induces a star algebra isomorphism between
the trace-radical quotients. -/
noncomputable def quotientTraceStarEquivOfSurjective (f : A →⋆ₐ[R] B)
    (hf : σ ∘ₗ f.toAlgHom.toLinearMap = τ) (hsurj : Function.Surjective f) :
    (A ⧸ τ.traceRadical hτ) ≃⋆ₐ[R] B ⧸ σ.traceRadical hσ :=
  Ideal.quotientStarAlgEquivOfSurjective (σ.traceRadical hσ) f
    (comap_traceRadical_of_surjective hτ hσ f.toAlgHom hf hsurj).symm hsurj

/-- The induced star algebra isomorphism acts on quotient representatives by `f`. -/
@[simp]
theorem quotientTraceStarEquivOfSurjective_mk (f : A →⋆ₐ[R] B)
    (hf : σ ∘ₗ f.toAlgHom.toLinearMap = τ) (hsurj : Function.Surjective f) (a : A) :
    quotientTraceStarEquivOfSurjective hτ hσ f hf hsurj
        (Ideal.Quotient.mk (τ.traceRadical hτ) a) =
      Ideal.Quotient.mk (σ.traceRadical hσ) (f a) :=
  Ideal.quotientStarAlgEquivOfSurjective_mk (σ.traceRadical hσ) f
    (comap_traceRadical_of_surjective hτ hσ f.toAlgHom hf hsurj).symm hsurj a

/-- Forgetting star compatibility recovers `LinearMap.quotientTraceEquivOfSurjective`. -/
@[simp]
theorem toAlgEquiv_quotientTraceStarEquivOfSurjective (f : A →⋆ₐ[R] B)
    (hf : σ ∘ₗ f.toAlgHom.toLinearMap = τ) (hsurj : Function.Surjective f) :
    (quotientTraceStarEquivOfSurjective hτ hσ f hf hsurj).toAlgEquiv =
      quotientTraceEquivOfSurjective hτ hσ f.toAlgHom hf hsurj := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- Fold `StarAlgEquiv.toAlgEquiv` application back to `⇑(quotientTraceStarEquivOfSurjective ...)`.
  change quotientTraceStarEquivOfSurjective hτ hσ f hf hsurj (Ideal.Quotient.mk _ a) = _
  rw [quotientTraceStarEquivOfSurjective_mk, quotientTraceEquivOfSurjective_mk]
  rfl

/-- The induced star algebra isomorphism intertwines the quotient traces. -/
@[simp]
theorem quotientTrace_quotientTraceStarEquivOfSurjective (f : A →⋆ₐ[R] B)
    (hf : σ ∘ₗ f.toAlgHom.toLinearMap = τ) (hsurj : Function.Surjective f)
    (x : A ⧸ τ.traceRadical hτ) :
    σ.quotientTrace hσ (quotientTraceStarEquivOfSurjective hτ hσ f hf hsurj x) =
      τ.quotientTrace hτ x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotientTraceStarEquivOfSurjective_mk, σ.quotientTrace_mk hσ, τ.quotientTrace_mk hτ]
  exact LinearMap.congr_fun hf a

/-- The inverse of the induced star algebra isomorphism also intertwines the quotient traces. -/
@[simp]
theorem quotientTrace_quotientTraceStarEquivOfSurjective_symm (f : A →⋆ₐ[R] B)
    (hf : σ ∘ₗ f.toAlgHom.toLinearMap = τ) (hsurj : Function.Surjective f)
    (y : B ⧸ σ.traceRadical hσ) :
    τ.quotientTrace hτ ((quotientTraceStarEquivOfSurjective hτ hσ f hf hsurj).symm y) =
      σ.quotientTrace hσ y := by
  let e := quotientTraceStarEquivOfSurjective hτ hσ f hf hsurj
  have h := quotientTrace_quotientTraceStarEquivOfSurjective hτ hσ f hf hsurj (e.symm y)
  rw [e.apply_symm_apply] at h
  exact h.symm

end QuotientEquiv

end LinearMap
