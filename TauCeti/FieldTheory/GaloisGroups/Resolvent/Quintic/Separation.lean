/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Solvable

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar
import TauCeti.FieldTheory.GaloisGroups.FactorDegrees
import TauCeti.FieldTheory.GaloisGroups.Label
import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Orbit
import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Trinomial

/-!
# Separation of Dummit's quintic `F₂₀` resolvent away from characteristic five

Dummit's criterion (`TauCeti.isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec`)
characterizes solvability of a monic irreducible separable quintic `f : F[X]` by the existence of a
root of the specialized `F₂₀` resolvent sextic `quinticF20Spec.specialize F f` in `F`, under the
hypothesis that this specialized sextic is separable. For a reducible quintic such as `X⁵ - X` over
`ℚ`, the sextic can indeed collide and acquire a spurious root in `F`
(`TauCeti.resolventSextic_X_pow_five_sub_X`).

Following Robin Chapman's note on Dummit's paper, this file proves that when `5 ≠ 0` in `F` and `f`
is monic, separable, and irreducible of degree five, **no collision can occur**: the specialized
resolvent sextic is automatically separable (`TauCeti.separable_specialize_quinticF20Spec`).

The proof uses the transitive Galois action on the five roots of `f` in `f.SplittingField`:
1. Every transitive subgroup of `Equiv.Perm (Fin 5)` is conjugate to one of `5T1`–`5T5`, and all
   five reference subgroups contain `finRotate 5`. Re-indexing the roots `x₀, …, x₄` conjugates a
   Galois automorphism `ϕ` onto `finRotate 5`.
2. Under `ϕ`, the root `θ₀` of the sextic attached to the identity coset is fixed while the five
   remaining roots `θ₁, …, θ₅` are permuted in a single `5`-cycle. Any repeated root among
   `θ₀, …, θ₅` therefore propagates under powers of `ϕ` to `θ₁ = θ₂ = θ₃ = θ₄ = θ₅`.
3. Chapman's factored difference identities (`TauCeti.eval₂_rename_formPerm_quinticF20Invariant_sub`
   and `TauCeti.eval₂_rename_swap_quinticF20Invariant_sub`) and distinctness of `x₀, …, x₄` force
   `2 x₁ = x₀ + x₂ = x₃ + x₄`, hence `5 x₁ = x₀ + x₁ + x₂ + x₃ + x₄`. Applying `ϕ` gives
   `5 x₂ = 5 x₁`, contradicting `x₁ ≠ x₂` when `5 ≠ 0`.

Consequently, away from characteristic five:
* `Group.IsSolvable f.Gal` holds if and only if `quinticF20Spec.specialize F f` has a root in `F`,
  with no separability hypothesis (`TauCeti.isSolvable_gal_iff_exists_isRoot_quinticF20`);
* whenever `a : F` is a root of the sextic, `quinticF20Spec.specialize F f` factors as
  `(X - C a) * q` where `q` is monic and irreducible of degree five
  (`TauCeti.exists_eq_X_sub_C_mul_irreducible_of_isRoot_specialize_quinticF20Spec`).

The hypothesis `5 ≠ 0` is sharp: over `𝔽₅`, the Artin–Schreier quintic `X⁵ - X - 1` is monic,
separable, and irreducible of degree five, while its `F₂₀` resolvent sextic is `(X - 3)(X - 2)⁵`,
inseparable (`TauCeti.exists_monic_separable_irreducible_not_separable_specialize_quinticF20Spec`).

## Main results

* `TauCeti.rename_formPerm_quinticF20Invariant_sub`,
  `TauCeti.rename_swap_quinticF20Invariant_sub`,
  `TauCeti.eval₂_rename_formPerm_quinticF20Invariant_sub`,
  `TauCeti.eval₂_rename_swap_quinticF20Invariant_sub`: Chapman's factored polynomial identities in
  `MvPolynomial (Fin 5) ℤ` and under `eval₂` for differences of coset values of Dummit's
  `F₂₀`-invariant.
* `TauCeti.separable_specialize_quinticF20Spec`,
  `TauCeti.resolventSeparationEvidence_quinticF20Spec`: **Chapman's separation theorem** for monic
  separable irreducible quintics over fields with `5 ≠ 0`.
* `TauCeti.isSolvable_gal_iff_exists_isRoot_quinticF20`: **Dummit's criterion (group form)** with no
  resolvent-separability premise away from characteristic five.
* `TauCeti.exists_eq_X_sub_C_mul_irreducible_of_isRoot_specialize_quinticF20Spec`: a base-field root
  splits the sextic into `(X - C a)` times a monic irreducible quintic.
* `TauCeti.specialize_quinticF20Spec_X_pow_five_sub_X_sub_one_zmod_five`,
  `TauCeti.not_separable_specialize_quinticF20Spec_X_pow_five_sub_X_sub_one_zmod_five`,
  `TauCeti.exists_monic_separable_irreducible_not_separable_specialize_quinticF20Spec`:
  characteristic-five sharpness counterexample.

## References

* R. Chapman, *A note on Dummit's "Solving solvable quintics"* (1995).
* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), 387–401,
  Theorem 1.
-/

public section

open Equiv Equiv.Perm Polynomial

namespace TauCeti

section Identities

/-- **Chapman's first difference identity** in `ℤ[X₀, …, X₄]`: the difference of Dummit's
`F₂₀`-invariant at the `3`-cycles `(0 1 2)` and `(0 2 1)` factors into root-difference linear forms
times a quadratic bracket. -/
theorem rename_formPerm_quinticF20Invariant_sub :
    MvPolynomial.rename ⇑(([0, 1, 2] : List (Fin 5)).formPerm) quinticF20Invariant -
      MvPolynomial.rename ⇑(([0, 2, 1] : List (Fin 5)).formPerm) quinticF20Invariant =
      (MvPolynomial.X 0 - MvPolynomial.X 3) * (MvPolynomial.X 2 - MvPolynomial.X 4) *
        ((MvPolynomial.X 1 - MvPolynomial.X 0) * (MvPolynomial.X 1 - MvPolynomial.X 3) -
          (MvPolynomial.X 1 - MvPolynomial.X 2) * (MvPolynomial.X 1 - MvPolynomial.X 4)) := by
  have h1 : ∀ a : Fin 5, ([0, 1, 2] : List (Fin 5)).formPerm a =
      if a = 0 then 1 else if a = 1 then 2 else if a = 2 then 0 else a := by decide
  have h2 : ∀ a : Fin 5, ([0, 2, 1] : List (Fin 5)).formPerm a =
      if a = 0 then 2 else if a = 2 then 1 else if a = 1 then 0 else a := by decide
  simp only [rename_quinticF20Invariant, Fin.sum_univ_five, Fin.isValue, h1, h2, Fin.reduceAdd,
    Fin.reduceSub, Fin.reduceEq, ↓reduceIte]
  ring

/-- **Chapman's second difference identity** in `ℤ[X₀, …, X₄]`: the difference of Dummit's
`F₂₀`-invariant at the transpositions `(0 1)` and `(1 2)` factors into root-difference linear forms
times the companion quadratic bracket. -/
theorem rename_swap_quinticF20Invariant_sub :
    MvPolynomial.rename ⇑(swap (0 : Fin 5) 1) quinticF20Invariant -
      MvPolynomial.rename ⇑(swap (1 : Fin 5) 2) quinticF20Invariant =
      (MvPolynomial.X 2 - MvPolynomial.X 3) * (MvPolynomial.X 0 - MvPolynomial.X 4) *
        ((MvPolynomial.X 1 - MvPolynomial.X 2) * (MvPolynomial.X 1 - MvPolynomial.X 3) -
          (MvPolynomial.X 1 - MvPolynomial.X 0) * (MvPolynomial.X 1 - MvPolynomial.X 4)) := by
  simp only [rename_quinticF20Invariant, Fin.sum_univ_five, Fin.isValue, swap_apply_def,
    Fin.reduceAdd, Fin.reduceSub, Fin.reduceEq, ↓reduceIte]
  ring

/-- Evaluation form of `TauCeti.rename_formPerm_quinticF20Invariant_sub` in any commutative ring. -/
theorem eval₂_rename_formPerm_quinticF20Invariant_sub {R : Type*} [CommRing R] (x : Fin 5 → R) :
    MvPolynomial.eval₂ (Int.castRingHom R) x
        (MvPolynomial.rename ⇑(([0, 1, 2] : List (Fin 5)).formPerm) quinticF20Invariant) -
      MvPolynomial.eval₂ (Int.castRingHom R) x
        (MvPolynomial.rename ⇑(([0, 2, 1] : List (Fin 5)).formPerm) quinticF20Invariant) =
      (x 0 - x 3) * (x 2 - x 4) *
        ((x 1 - x 0) * (x 1 - x 3) - (x 1 - x 2) * (x 1 - x 4)) := by
  simpa [map_sub, map_mul] using
    congrArg (MvPolynomial.eval₂ (Int.castRingHom R) x) rename_formPerm_quinticF20Invariant_sub

/-- Evaluation form of `TauCeti.rename_swap_quinticF20Invariant_sub` in any commutative ring. -/
theorem eval₂_rename_swap_quinticF20Invariant_sub {R : Type*} [CommRing R] (x : Fin 5 → R) :
    MvPolynomial.eval₂ (Int.castRingHom R) x
        (MvPolynomial.rename ⇑(swap (0 : Fin 5) 1) quinticF20Invariant) -
      MvPolynomial.eval₂ (Int.castRingHom R) x
        (MvPolynomial.rename ⇑(swap (1 : Fin 5) 2) quinticF20Invariant) =
      (x 2 - x 3) * (x 0 - x 4) *
        ((x 1 - x 2) * (x 1 - x 3) - (x 1 - x 0) * (x 1 - x 4)) := by
  simpa [map_sub, map_mul] using
    congrArg (MvPolynomial.eval₂ (Int.castRingHom R) x) rename_swap_quinticF20Invariant_sub

end Identities

section Separation

/-- The six orbit representatives of `quinticF20OrbitRepresentatives` ordered so that `0` is fixed
by `finRotate 5` and `1 ↦ 2 ↦ 3 ↦ 4 ↦ 5 ↦ 1` is a single `5`-cycle under `finRotate 5`. -/
private def quinticF20CycleRep : Fin 6 → Perm (Fin 5) :=
  ![1, swap 2 3, swap 3 4, swap 2 3 * swap 3 4, swap 2 4, swap 3 4 * swap 2 3]

/-- The six values of Dummit's `F₂₀`-invariant along `quinticF20CycleRep` at a root tuple `x`. -/
private noncomputable def quinticF20CycleRoots {R : Type*} [CommRing R] (x : Fin 5 → R)
    (i : Fin 6) : R :=
  MvPolynomial.eval₂ (Int.castRingHom R) x
    (MvPolynomial.rename ⇑(quinticF20CycleRep i) quinticF20Invariant)

/-- `swap 2 3` and `[0, 1, 2].formPerm` represent the same `F₂₀`-coset, and `swap 2 3 * swap 3 4`
and `[0, 2, 1].formPerm` represent the same `F₂₀`-coset. -/
private theorem quinticF20CycleRoots_one_sub_three {R : Type*} [CommRing R] (x : Fin 5 → R) :
    quinticF20CycleRoots x 1 - quinticF20CycleRoots x 3 =
      (x 0 - x 3) * (x 2 - x 4) *
        ((x 1 - x 0) * (x 1 - x 3) - (x 1 - x 2) * (x 1 - x 4)) := by
  rw [← eval₂_rename_formPerm_quinticF20Invariant_sub x]
  have h1 : ∀ a : Fin 5, ([0, 1, 2] : List (Fin 5)).formPerm a =
      if a = 0 then 1 else if a = 1 then 2 else if a = 2 then 0 else a := by decide
  have h2 : ∀ a : Fin 5, ([0, 2, 1] : List (Fin 5)).formPerm a =
      if a = 0 then 2 else if a = 2 then 1 else if a = 1 then 0 else a := by decide
  simp only [quinticF20CycleRoots, quinticF20CycleRep, Matrix.cons_val_one, Matrix.cons_val,
    eval₂_rename_quinticF20Invariant, h1, h2, Fin.isValue, coe_mul, Function.comp_apply,
    swap_apply_def, Fin.reduceEq, ↓reduceIte]
  ring

/-- `swap 2 4` and `swap 0 1` represent the same `F₂₀`-coset, and `swap 3 4 * swap 2 3` and
`swap 1 2` represent the same `F₂₀`-coset. -/
private theorem quinticF20CycleRoots_four_sub_five {R : Type*} [CommRing R] (x : Fin 5 → R) :
    quinticF20CycleRoots x 4 - quinticF20CycleRoots x 5 =
      (x 2 - x 3) * (x 0 - x 4) *
        ((x 1 - x 2) * (x 1 - x 3) - (x 1 - x 0) * (x 1 - x 4)) := by
  rw [← eval₂_rename_swap_quinticF20Invariant_sub x]
  simp only [quinticF20CycleRoots, quinticF20CycleRep, Matrix.cons_val,
    eval₂_rename_quinticF20Invariant, Fin.isValue, coe_mul, Function.comp_apply, swap_apply_def,
    Fin.reduceEq, ↓reduceIte]
  ring

private theorem map_specialize_quinticF20Spec_eq_prod {F E : Type*} [Field F] [Field E]
    [Algebra F E] {f : F[X]} (hf : f.Monic) (hdeg : f.natDegree = 5)
    (e : f.rootSet E ≃ Fin 5) :
    (quinticF20Spec.specialize F f).map (algebraMap F E) =
      ∏ i : Fin 6, (X - C (quinticF20CycleRoots (fun k ↦ (e.symm k : E)) i)) := by
  rw [quinticF20Spec.map_specialize_eq_galResolvent_numbering hf hdeg e, quinticF20Spec_Φ,
    ← MvPolynomial.map_universalResolvent_eq_galResolvent, universalResolvent_quinticF20Invariant,
    Polynomial.map_prod, prod_quinticF20OrbitRepresentatives, Fin.prod_univ_six]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, MvPolynomial.coe_eval₂Hom,
    quinticF20CycleRoots, quinticF20CycleRep, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

/-- The next index under the action of `finRotate 5` on `quinticF20CycleRoots`: `0` is fixed and
`1 ↦ 2 ↦ 3 ↦ 4 ↦ 5 ↦ 1`. -/
private def quinticF20CycleNext : Fin 6 → Fin 6 :=
  ![0, 2, 3, 4, 5, 1]

private theorem apply_quinticF20CycleRoots {R : Type*} [CommRing R] (x : Fin 5 → R)
    (ϕ : R →+* R) (hϕ : ∀ k : Fin 5, ϕ (x k) = x (finRotate 5 k)) (i : Fin 6) :
    ϕ (quinticF20CycleRoots x i) = quinticF20CycleRoots x (quinticF20CycleNext i) := by
  fin_cases i <;>
    · simp only [quinticF20CycleRoots, quinticF20CycleRep, quinticF20CycleNext, Fin.zero_eta,
        Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        eval₂_rename_quinticF20Invariant, map_add, map_mul, map_pow, hϕ, Fin.isValue, coe_one,
        id_eq, coe_mul, Function.comp_apply, swap_apply_def, finRotate_apply, Fin.reduceAdd,
        Fin.reduceEq, ↓reduceIte]
      ring

private theorem quinticF20CycleRoots_injective {E : Type*} [Field E] (h5 : (5 : E) ≠ 0)
    {x : Fin 5 → E} (hx : Function.Injective x) (ϕ : E →+* E)
    (hϕ : ∀ k : Fin 5, ϕ (x k) = x (finRotate 5 k)) :
    Function.Injective (quinticF20CycleRoots x) := by
  set θ := quinticF20CycleRoots x
  have hstep (i : Fin 6) : ϕ (θ i) = θ (quinticF20CycleNext i) :=
    apply_quinticF20CycleRoots x ϕ hϕ i
  have h12_false : θ 1 ≠ θ 2 := by
    intro h12
    have h23 : θ 2 = θ 3 := by simpa [hstep, quinticF20CycleNext] using congrArg ϕ h12
    have h34 : θ 3 = θ 4 := by simpa [hstep, quinticF20CycleNext] using congrArg ϕ h23
    have h45 : θ 4 = θ 5 := by simpa [hstep, quinticF20CycleNext] using congrArg ϕ h34
    have h13 : θ 1 = θ 3 := h12.trans h23
    have hd1 : (x 0 - x 3) * (x 2 - x 4) *
        ((x 1 - x 0) * (x 1 - x 3) - (x 1 - x 2) * (x 1 - x 4)) = 0 := by
      rw [← quinticF20CycleRoots_one_sub_three x]
      exact sub_eq_zero.mpr h13
    have hd2 : (x 2 - x 3) * (x 0 - x 4) *
        ((x 1 - x 2) * (x 1 - x 3) - (x 1 - x 0) * (x 1 - x 4)) = 0 := by
      rw [← quinticF20CycleRoots_four_sub_five x]
      exact sub_eq_zero.mpr h45
    have hne (a b : Fin 5) (hab : a ≠ b) : x a - x b ≠ 0 := sub_ne_zero.mpr (hx.ne hab)
    have hB1 : (x 1 - x 0) * (x 1 - x 3) - (x 1 - x 2) * (x 1 - x 4) = 0 :=
      (mul_eq_zero.mp hd1).resolve_left
        (mul_ne_zero (hne 0 3 (by decide)) (hne 2 4 (by decide)))
    have hB2 : (x 1 - x 2) * (x 1 - x 3) - (x 1 - x 0) * (x 1 - x 4) = 0 :=
      (mul_eq_zero.mp hd2).resolve_left
        (mul_ne_zero (hne 2 3 (by decide)) (hne 0 4 (by decide)))
    have hprod1 : (x 2 - x 0) * (2 * x 1 - x 3 - x 4) = 0 := by linear_combination hB1 - hB2
    have hprod2 : (x 4 - x 3) * (2 * x 1 - x 0 - x 2) = 0 := by linear_combination hB1 + hB2
    have hsum1 : 2 * x 1 - x 3 - x 4 = 0 :=
      (mul_eq_zero.mp hprod1).resolve_left (hne 2 0 (by decide))
    have hsum2 : 2 * x 1 - x 0 - x 2 = 0 :=
      (mul_eq_zero.mp hprod2).resolve_left (hne 4 3 (by decide))
    have hfive1 : 5 * x 1 = x 0 + x 1 + x 2 + x 3 + x 4 := by linear_combination hsum1 + hsum2
    have hfive2 := congrArg ϕ hfive1
    simp only [map_mul, map_add, map_ofNat, hϕ, finRotate_apply, Fin.isValue, Fin.reduceAdd]
      at hfive2
    have hdiff : 5 * (x 2 - x 1) = 0 := by linear_combination hfive2 - hfive1
    exact hne 2 1 (by decide) ((mul_eq_zero.mp hdiff).resolve_left h5)
  have h13_false : θ 1 ≠ θ 3 := by
    intro h13
    have h24 : θ 2 = θ 4 := by simpa [hstep, quinticF20CycleNext] using congrArg ϕ h13
    have h35 : θ 3 = θ 5 := by simpa [hstep, quinticF20CycleNext] using congrArg ϕ h24
    have h41 : θ 4 = θ 1 := by simpa [hstep, quinticF20CycleNext] using congrArg ϕ h35
    exact h12_false (h41.symm.trans h24.symm)
  -- Reduce any `i ≠ j` to `θ 1 = θ 2` or `θ 1 = θ 3` by applying `ϕ` along the cycle.
  have hlt_false : ∀ {i j : Fin 6}, i < j → θ i ≠ θ j := by
    intro i j hlt hij
    have h1 := by simpa only [hstep] using congrArg ϕ hij
    have h2 := by simpa only [hstep] using congrArg ϕ h1
    have h3 := by simpa only [hstep] using congrArg ϕ h2
    have h4 := by simpa only [hstep] using congrArg ϕ h3
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.reduceLT] at hlt
    · exact h12_false (hij.symm.trans (by simpa [quinticF20CycleNext] using h1))
    · have h23 : θ 2 = θ 3 := hij.symm.trans (by simpa [quinticF20CycleNext] using h1)
      have h51 : θ 1 = θ 2 := by
        simpa [hstep, quinticF20CycleNext] using
          congrArg ϕ (congrArg ϕ (congrArg ϕ (congrArg ϕ h23)))
      exact h12_false h51
    · have h34 : θ 3 = θ 4 := hij.symm.trans (by simpa [quinticF20CycleNext] using h1)
      have h51 : θ 1 = θ 2 := by
        simpa [hstep, quinticF20CycleNext] using congrArg ϕ (congrArg ϕ (congrArg ϕ h34))
      exact h12_false h51
    · have h45 : θ 4 = θ 5 := hij.symm.trans (by simpa [quinticF20CycleNext] using h1)
      have h51 : θ 1 = θ 2 := by
        simpa [hstep, quinticF20CycleNext] using congrArg ϕ (congrArg ϕ h45)
      exact h12_false h51
    · have h10 : θ 1 = θ 0 := by simpa [quinticF20CycleNext] using h1.symm
      have h15 : θ 1 = θ 5 := h10.trans hij
      have h21 : θ 2 = θ 1 := by simpa [hstep, quinticF20CycleNext] using congrArg ϕ h15
      exact h12_false h21.symm
    · exact h12_false hij
    · exact h13_false hij
    · exact h13_false (by simpa [quinticF20CycleNext] using h2.symm)
    · exact h12_false (by simpa [quinticF20CycleNext] using h1.symm)
    · exact h12_false (by simpa [quinticF20CycleNext] using h4)
    · exact h13_false (by simpa [quinticF20CycleNext] using h4)
    · exact h13_false (by simpa [quinticF20CycleNext] using h1.symm)
    · exact h12_false (by simpa [quinticF20CycleNext] using h3)
    · exact h13_false (by simpa [quinticF20CycleNext] using h3)
    · exact h12_false (by simpa [quinticF20CycleNext] using h2)
  intro i j hij
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact (hlt_false hlt hij).elim
  · rfl
  · exact (hlt_false hgt hij.symm).elim

/-- Every monic separable irreducible quintic admits a root numbering in its splitting field under
which some `F`-automorphism acts as `finRotate 5`. -/
private theorem exists_numbering_and_aut_finRotate {F : Type*} [Field F] {f : F[X]}
    (hsep : f.Separable) (hirr : Irreducible f) (hdeg : f.natDegree = 5) :
    ∃ (e : f.rootSet f.SplittingField ≃ Fin 5)
      (ϕ : f.SplittingField ≃ₐ[F] f.SplittingField),
      ∀ k : Fin 5, ϕ (e.symm k : f.SplittingField) =
        (e.symm (finRotate 5 k) : f.SplittingField) := by
  have : Fact ((f.map (algebraMap F f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  obtain ⟨e₀⟩ := nonempty_rootSet_equiv_fin hsep (SplittingField.splits f)
  let e₁ : f.rootSet f.SplittingField ≃ Fin 5 := e₀.trans (finCongr hdeg)
  let G₁ : Subgroup (Perm (Fin 5)) :=
    (Gal.galActionHom f f.SplittingField).range.map e₁.permCongrHom.toMonoidHom
  have : MulAction.IsPretransitive G₁ (Fin 5) :=
    (isPretransitive_map_range_galActionHom_iff hsep (by omega) e₁).mpr hirr
  obtain ⟨j, hj⟩ := exists_transitiveGroupLabel_five G₁
  obtain ⟨τ, hτ⟩ := hj.exists_map_permCongrHom_eq
  have hrot_ref : finRotate 5 ∈ referenceSubgroup 5 j := by
    have h0 : finRotate 5 ∈ referenceSubgroup 5 ⟨0, by simp⟩ := by
      rw [referenceSubgroup_five_zero]
      exact Subgroup.subset_closure (Set.mem_singleton _)
    obtain ⟨a, ha⟩ := j
    rw [numTransitiveGroups_five] at ha
    interval_cases a
    · exact h0
    · exact referenceSubgroup_five_zero_le_referenceSubgroup_five_one h0
    · exact (referenceSubgroup_five_zero_le_referenceSubgroup_five_one.trans
        referenceSubgroup_five_one_le_referenceSubgroup_five_two) h0
    · rw [referenceSubgroup_five_three]
      exact referenceSubgroup_five_zero_le_alternatingGroup h0
    · rw [referenceSubgroup_five_four]
      trivial
  rw [← hτ] at hrot_ref
  obtain ⟨π, ⟨σ, ⟨g, rfl⟩, rfl⟩, hπ⟩ := hrot_ref
  obtain ⟨ϕ, rfl⟩ := Gal.restrict_surjective f f.SplittingField g
  let e : f.rootSet f.SplittingField ≃ Fin 5 := e₁.trans τ
  refine ⟨e, ϕ, fun k ↦ ?_⟩
  have happly : e.permCongr (Gal.galActionHom f f.SplittingField
      (Gal.restrict f f.SplittingField ϕ)) = finRotate 5 := by
    apply Equiv.Perm.ext
    intro m
    have hm := Equiv.Perm.ext_iff.mp hπ m
    simpa [e, Equiv.permCongrHom_coe, Equiv.permCongr_apply] using hm
  have hk : e.symm (finRotate 5 k) =
      Gal.galActionHom f f.SplittingField (Gal.restrict f f.SplittingField ϕ) (e.symm k) := by
    rw [← happly, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [hk, Gal.galActionHom_restrict]

/-- **Separation of the quintic `F₂₀` resolvent** (Chapman's note on Dummit's *Solving solvable
quintics*). Over a field in which `5 ≠ 0`, the specialized `F₂₀` resolvent sextic of a monic
separable irreducible quintic is separable. -/
theorem separable_specialize_quinticF20Spec {F : Type*} [Field F] [NeZero (5 : F)] {f : F[X]}
    (hf : f.Monic) (hsep : f.Separable) (hirr : Irreducible f) (hdeg : f.natDegree = 5) :
    (quinticF20Spec.specialize F f).Separable := by
  obtain ⟨e, ϕ, hϕ⟩ := exists_numbering_and_aut_finRotate hsep hirr hdeg
  have h5 : (5 : f.SplittingField) ≠ 0 := by
    rw [← map_ofNat (algebraMap F f.SplittingField) 5]
    exact (_root_.map_ne_zero (algebraMap F f.SplittingField)).mpr (NeZero.ne (5 : F))
  have hx_inj : Function.Injective (fun k : Fin 5 ↦ (e.symm k : f.SplittingField)) :=
    Subtype.val_injective.comp e.symm.injective
  rw [← separable_map (algebraMap F f.SplittingField),
    map_specialize_quinticF20Spec_eq_prod hf hdeg e]
  exact separable_prod_X_sub_C_iff.mpr (quinticF20CycleRoots_injective h5 hx_inj ϕ.toRingHom hϕ)

/-- Over a field in which `5 ≠ 0`, any monic separable irreducible quintic carries
`ResolventSeparationEvidence` for Dummit's `F₂₀` resolvent specification. -/
theorem resolventSeparationEvidence_quinticF20Spec {F : Type*} [Field F] [NeZero (5 : F)]
    {f : F[X]} (hf : f.Monic) (hsep : f.Separable) (hirr : Irreducible f)
    (hdeg : f.natDegree = 5) :
    ResolventSeparationEvidence quinticF20Spec f :=
  ⟨separable_specialize_quinticF20Spec hf hsep hirr hdeg⟩

/-- **Dummit's criterion, group form.** Over a field in which `5 ≠ 0`, the Galois group of a monic
separable irreducible quintic `f` is solvable if and only if Dummit's `F₂₀` resolvent sextic
`quinticF20Spec.specialize F f` has a root in `F`. Unlike
`TauCeti.isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec`, no separability hypothesis on
the specialized sextic is required. -/
theorem isSolvable_gal_iff_exists_isRoot_quinticF20 {F : Type*} [Field F] [NeZero (5 : F)]
    {f : F[X]} (hf : f.Monic) (hsep : f.Separable) (hirr : Irreducible f)
    (hdeg : f.natDegree = 5) :
    Group.IsSolvable f.Gal ↔ ∃ a : F, (quinticF20Spec.specialize F f).IsRoot a :=
  isSolvable_gal_iff_exists_isRoot_specialize_quinticF20Spec hf hsep hirr hdeg
    (resolventSeparationEvidence_quinticF20Spec hf hsep hirr hdeg)

/-- **Linear-times-irreducible-quintic factorization of the `F₂₀` resolvent** (Dummit, Theorem 1).
Over a field `F` with `5 ≠ 0`, if `f : F[X]` is monic, separable, and irreducible of degree five
and `a : F` is a root of `quinticF20Spec.specialize F f`, then the sextic factors as `(X - C a) * q`
for a monic irreducible quintic `q : F[X]`: the `5`-cycle in `f.Gal` permutes the remaining five
distinct roots of the sextic transitively. -/
theorem exists_eq_X_sub_C_mul_irreducible_of_isRoot_specialize_quinticF20Spec {F : Type*}
    [Field F] [NeZero (5 : F)] {f : F[X]} (hf : f.Monic) (hsep : f.Separable) (hirr : Irreducible f)
    (hdeg : f.natDegree = 5) {a : F} (ha : (quinticF20Spec.specialize F f).IsRoot a) :
    ∃ q : F[X], q.Monic ∧ Irreducible q ∧ q.natDegree = 5 ∧
      quinticF20Spec.specialize F f = (X - C a) * q := by
  classical
  obtain ⟨e, ϕ, hϕ⟩ := exists_numbering_and_aut_finRotate hsep hirr hdeg
  let x : Fin 5 → f.SplittingField := fun k ↦ (e.symm k : f.SplittingField)
  let θ : Fin 6 → f.SplittingField := quinticF20CycleRoots x
  have h5 : (5 : f.SplittingField) ≠ 0 := by
    rw [← map_ofNat (algebraMap F f.SplittingField) 5]
    exact (_root_.map_ne_zero (algebraMap F f.SplittingField)).mpr (NeZero.ne (5 : F))
  have hx_inj : Function.Injective x := Subtype.val_injective.comp e.symm.injective
  have hθ_inj : Function.Injective θ := quinticF20CycleRoots_injective h5 hx_inj ϕ.toRingHom hϕ
  have hstep (i : Fin 6) : ϕ (θ i) = θ (quinticF20CycleNext i) :=
    apply_quinticF20CycleRoots x ϕ.toRingHom hϕ i
  have hmap := map_specialize_quinticF20Spec_eq_prod hf hdeg e
  -- `algebraMap F _ a` is fixed by `ϕ`, so among `θ 0, …, θ 5` it must equal the fixed root `θ 0`.
  have ha_eval : eval (algebraMap F f.SplittingField a)
      (∏ i : Fin 6, (X - C (θ i))) = 0 := by
    rw [← hmap, eval_map, eval₂_at_apply, ha, map_zero]
  rw [eval_prod] at ha_eval
  obtain ⟨i₀, -, hi₀⟩ := Finset.prod_eq_zero_iff.mp ha_eval
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hi₀
  have hi₀_eq : i₀ = 0 := by
    by_contra hne0
    have hfix : θ (quinticF20CycleNext i₀) = θ i₀ := by
      rw [← hstep, ← hi₀, ϕ.commutes]
    have hidx := hθ_inj hfix
    fin_cases i₀ <;> simp [quinticF20CycleNext] at hne0 hidx
  subst hi₀_eq
  -- Set `q = minpoly F (θ 1)`; its roots in `f.SplittingField` include the 5-cycle `θ 1, …, θ 5`.
  let g : F[X] := quinticF20Spec.specialize F f
  have hg_monic : g.Monic := quinticF20Spec.monic_specialize F f
  have hg_deg : g.natDegree = 6 := by
    rw [ResolventSpec.natDegree_specialize, quinticF20Spec_H, index_referenceSubgroup_five_two]
  have hθ1_aeval : aeval (θ 1) g = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hmap, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp [θ, x])
  have hθ1_int : IsIntegral F (θ 1) :=
    ⟨g, hg_monic, hθ1_aeval⟩
  let q : F[X] := minpoly F (θ 1)
  have hq_monic : q.Monic := minpoly.monic hθ1_int
  have hq_irr : Irreducible q := minpoly.irreducible hθ1_int
  have hq_dvd : q ∣ g := minpoly.dvd F (θ 1) hθ1_aeval
  have haeval_step {z : f.SplittingField} (hz : aeval z q = 0) : aeval (ϕ z) q = 0 := by
    simpa [hz] using aeval_algHom_apply ϕ.toAlgHom z q
  have hr1 : aeval (θ 1) q = 0 := minpoly.aeval F (θ 1)
  have hr2 : aeval (θ 2) q = 0 := by simpa [hstep, quinticF20CycleNext] using haeval_step hr1
  have hr3 : aeval (θ 3) q = 0 := by simpa [hstep, quinticF20CycleNext] using haeval_step hr2
  have hr4 : aeval (θ 4) q = 0 := by simpa [hstep, quinticF20CycleNext] using haeval_step hr3
  have hr5 : aeval (θ 5) q = 0 := by simpa [hstep, quinticF20CycleNext] using haeval_step hr4
  -- Those five distinct roots in `f.SplittingField` force `5 ≤ q.natDegree`.
  let S : Finset f.SplittingField := ({1, 2, 3, 4, 5} : Finset (Fin 6)).image θ
  have hS_card : S.card = 5 := by
    rw [Finset.card_image_of_injective _ hθ_inj]
    decide
  have hq_map_ne : q.map (algebraMap F f.SplittingField) ≠ 0 :=
    (hq_monic.map _).ne_zero
  have hS_le : S.val ≤ (q.map (algebraMap F f.SplittingField)).roots := by
    refine (Multiset.le_iff_subset S.nodup).mpr fun r hr ↦ (mem_roots hq_map_ne).mpr ?_
    have hr' : r ∈ ({1, 2, 3, 4, 5} : Finset (Fin 6)).image θ := Finset.mem_val.mp hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr'
    rw [IsRoot.def, eval_map, ← aeval_def]
    fin_cases k <;> simp at hk <;> assumption
  have hq_deg_ge : 5 ≤ q.natDegree := by
    have hle := (Multiset.card_le_card hS_le).trans
      (card_roots' (q.map (algebraMap F f.SplittingField)))
    rwa [← Finset.card_def, hS_card, hq_monic.natDegree_map] at hle
  -- `q.eval a ≠ 0` by degree, giving a Bézout identity between `X - C a` and `q`.
  have hq_eval : q.eval a ≠ 0 := fun hroot ↦ by
    have hdvd : X - C a ∣ q := dvd_iff_isRoot.mpr hroot
    obtain ⟨r, hr⟩ := hdvd
    have hr_monic : r.Monic := (monic_X_sub_C a).of_mul_monic_left (hr ▸ hq_monic)
    have hr_unit : IsUnit r :=
      (hq_irr.isUnit_or_isUnit hr).resolve_left (not_isUnit_X_sub_C a)
    have hr_deg : r.natDegree = 0 := natDegree_eq_zero_of_isUnit hr_unit
    have hdeg_eq : q.natDegree = 1 := by
      rw [hr, (monic_X_sub_C a).natDegree_mul hr_monic, natDegree_X_sub_C, hr_deg]
    omega
  obtain ⟨r, hr⟩ := X_sub_C_dvd_sub_C_eval (p := q) (a := a)
  have hcop : IsCoprime (X - C a) q := by
    refine ⟨-C (q.eval a)⁻¹ * r, C (q.eval a)⁻¹, ?_⟩
    calc (-C (q.eval a)⁻¹ * r) * (X - C a) + C (q.eval a)⁻¹ * q
        = -C (q.eval a)⁻¹ * ((X - C a) * r) + C (q.eval a)⁻¹ * q := by ring
      _ = -C (q.eval a)⁻¹ * (q - C (q.eval a)) + C (q.eval a)⁻¹ * q := by rw [← hr]
      _ = C (q.eval a)⁻¹ * C (q.eval a) := by ring
      _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hq_eval, C_1]
  have hmul_dvd : (X - C a) * q ∣ g := hcop.mul_dvd (dvd_iff_isRoot.mpr ha) hq_dvd
  have hmul_monic : ((X - C a) * q).Monic := (monic_X_sub_C a).mul hq_monic
  have hmul_deg_le : ((X - C a) * q).natDegree ≤ 6 :=
    hg_deg ▸ natDegree_le_of_dvd hmul_dvd hg_monic.ne_zero
  rw [(monic_X_sub_C a).natDegree_mul hq_monic, natDegree_X_sub_C] at hmul_deg_le
  have hq_deg : q.natDegree = 5 := by omega
  refine ⟨q, hq_monic, hq_irr, hq_deg, eq_of_monic_of_dvd_of_natDegree_le
    hmul_monic hg_monic hmul_dvd ?_⟩
  rw [hg_deg, (monic_X_sub_C a).natDegree_mul hq_monic, natDegree_X_sub_C, hq_deg]

end Separation

section CharacteristicFive

/-- Over `𝔽₅`, Dummit's `F₂₀` resolvent of the Artin–Schreier quintic `X⁵ - X - 1` factors as
`(X - 3)(X - 2)⁵`: the five non-trivial coset values collide at `2`. -/
theorem specialize_quinticF20Spec_X_pow_five_sub_X_sub_one_zmod_five :
    quinticF20Spec.specialize (ZMod 5) (X ^ 5 - X - 1) = (X - 3) * (X - 2) ^ 5 := by
  have hf : (X ^ 5 - X - 1 : (ZMod 5)[X]) = X ^ 5 + C (-1) * X + C (-1) := by
    simp only [map_neg, C_1]
    ring
  rw [hf, quinticF20Spec_specialize_X_pow_five_add_C_mul_X_add_C]
  simp only [map_neg, map_mul, map_pow, map_sub, map_ofNat, C_1]
  ring_nf
  reduce_mod_char

/-- Over `𝔽₅`, the specialized `F₂₀` resolvent `(X - 3)(X - 2)⁵` of `X⁵ - X - 1` is not
separable. -/
theorem not_separable_specialize_quinticF20Spec_X_pow_five_sub_X_sub_one_zmod_five :
    ¬ (quinticF20Spec.specialize (ZMod 5) (X ^ 5 - X - 1)).Separable := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [specialize_quinticF20Spec_X_pow_five_sub_X_sub_one_zmod_five, ← C_ofNat]
  intro hsep
  exact absurd (hsep.of_mul_right.of_pow (not_isUnit_X_sub_C (2 : ZMod 5)) (by decide)).2
    (by decide)

/-- **Sharpness of `5 ≠ 0` in `TauCeti.separable_specialize_quinticF20Spec`.** Over `𝔽₅`, there
exists a monic, separable, irreducible quintic (`X⁵ - X - 1`) whose specialized `F₂₀` resolvent
sextic is not separable. -/
theorem exists_monic_separable_irreducible_not_separable_specialize_quinticF20Spec :
    ∃ f : (ZMod 5)[X], f.Monic ∧ f.Separable ∧ Irreducible f ∧ f.natDegree = 5 ∧
      ¬ (quinticF20Spec.specialize (ZMod 5) f).Separable := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hdeg : (X ^ 5 - X - 1 : (ZMod 5)[X]).natDegree = 5 := by
    rw [sub_sub]
    compute_degree!
  have hmonic : (X ^ 5 - X - 1 : (ZMod 5)[X]).Monic := by
    rw [Monic.def, leadingCoeff, hdeg]
    simp [coeff_X, coeff_one]
  have hsep : (X ^ 5 - X - 1 : (ZMod 5)[X]).Separable := by
    refine ⟨0, -1, ?_⟩
    simp only [derivative_sub, derivative_X_pow, derivative_X, derivative_one]
    ring_nf
    reduce_mod_char
    simp only [C_0, mul_zero, add_zero]
  exact ⟨X ^ 5 - X - 1, hmonic, hsep, Polynomial.irreducible_X_pow_five_sub_X_sub_one_zmod_five,
    hdeg, not_separable_specialize_quinticF20Spec_X_pow_five_sub_X_sub_one_zmod_five⟩

end CharacteristicFive

end TauCeti
