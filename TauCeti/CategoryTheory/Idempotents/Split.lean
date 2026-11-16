/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.Algebra.Ring.Idempotent.Basic

/-!
# Sums and perturbations of split idempotents

An idempotent `e` of `X` splits when `e = r ≫ i` for morphisms `i : Y ⟶ X` and `r : X ⟶ Y` with
`i ≫ r = 𝟙 Y`, as in Mathlib's `CategoryTheory.IsIdempotentComplete`. Splitting is invariant under
conjugation by an isomorphism; in a preadditive category, an idempotent perturbation `e + u` of a
split idempotent `e` by a square-zero endomorphism `u` is conjugate to `e` and therefore splits,
and when binary biproducts exist, the sum of two orthogonal split idempotents splits through the
biproduct of their images.

## Main results

* `TauCeti.exists_split_of_iso_conj`: an idempotent splits whenever a conjugate by an isomorphism
  splits.
* `TauCeti.exists_split_add_of_sq_eq_zero`: an idempotent perturbation `e + u` of a split
  idempotent `e` by `u` with `u ≫ u = 0` splits.
* `TauCeti.exists_split_add_of_comp_eq_zero`: the sum of two orthogonal split idempotents splits.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

/-- **Splitting of idempotents is invariant under conjugation by an isomorphism**: if
`φ.inv ≫ e ≫ φ.hom` splits, then `e` splits through the same object. -/
theorem exists_split_of_iso_conj {C : Type*} [Category* C] {X X' : C} (φ : X ≅ X') {e : X ⟶ X}
    (h : ∃ (Y : C) (i : Y ⟶ X') (r : X' ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = φ.inv ≫ e ≫ φ.hom) :
    ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e := by
  obtain ⟨Y, i, r, hir, hri⟩ := h
  exact ⟨Y, i ≫ φ.inv, φ.hom ≫ r, by simp [hir], by simp [reassoc_of% hri]⟩

/-- **Square-zero perturbations of split idempotents split**: in a preadditive category, if `e` and
`e + u` are idempotent endomorphisms of `X`, `u ≫ u = 0`, and `e` splits, then `e + u` splits
through the same object. -/
theorem exists_split_add_of_sq_eq_zero {C : Type*} [Category* C] [Preadditive C] {X : C}
    {e u : X ⟶ X} (he : e ≫ e = e) (hu : u ≫ u = 0) (heu : (e + u) ≫ (e + u) = e + u)
    (hsplit : ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e) :
    ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e + u := by
  let e' : End X := End.of e
  let u' : End X := End.of u
  have he' : IsIdempotentElem e' := End.ext he
  have hu' : u' * u' = 0 := End.ext hu
  have heu' : IsIdempotentElem (e' + u') := End.ext heu
  let a : End X := 1 + (e' * u' - u' * e')
  let b : End X := 1 - (e' * u' - u' * e')
  let φ : X ≅ X :=
    { hom := a.asHom
      inv := b.asHom
      hom_inv_id := congrArg End.asHom (he'.one_sub_mul_sub_mul_mul_one_add hu' heu')
      inv_hom_id := congrArg End.asHom (he'.one_add_mul_sub_mul_mul_one_sub hu' heu') }
  have hconj : φ.inv ≫ (e + u) ≫ φ.hom = e :=
    congrArg End.asHom (he'.conj_one_add_mul_sub_mul hu' heu')
  exact exists_split_of_iso_conj φ (hconj.symm ▸ hsplit)

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- **Orthogonal split idempotents have a split sum**: if `e₁` and `e₂` split and `e₁ ≫ e₂ = 0 =
e₂ ≫ e₁`, then `e₁ + e₂` splits, through the biproduct of the two images. -/
theorem exists_split_add_of_comp_eq_zero {X : C} {e₁ e₂ : X ⟶ X}
    (h₁ : ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e₁)
    (h₂ : ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e₂)
    (h₁₂ : e₁ ≫ e₂ = 0) (h₂₁ : e₂ ≫ e₁ = 0) :
    ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e₁ + e₂ := by
  obtain ⟨Y₁, i₁, r₁, hi₁, rfl⟩ := h₁
  obtain ⟨Y₂, i₂, r₂, hi₂, rfl⟩ := h₂
  have h₁₂' : i₁ ≫ r₂ = 0 := by
    simpa [reassoc_of% hi₁, hi₂] using i₁ ≫= h₁₂ =≫ r₂
  have h₂₁' : i₂ ≫ r₁ = 0 := by
    simpa [reassoc_of% hi₂, hi₁] using i₂ ≫= h₂₁ =≫ r₁
  refine ⟨Y₁ ⊞ Y₂, biprod.desc i₁ i₂, biprod.lift r₁ r₂, ?_, by simp⟩
  ext <;> simp [hi₁, hi₂, h₁₂', h₂₁']

end TauCeti
