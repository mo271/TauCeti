/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WeakCompletion.Completion
public import TauCeti.RingTheory.Dagger.WeakCompletion.Map
import Mathlib.Data.Fintype.Order
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Algebra.MvPolynomial.Degrees

/-!
# Overconvergent polynomial evaluation in weak completions

Let `O` be a commutative ring, `π : O`, `σ` a finite index type, and `S` a finitely generated
`O`-algebra. While `weakCompletion.map π (MvPolynomial.aeval x)` evaluates elements of the weak
completion `(O[X_σ])†` at tuples `x : σ → S` coming from `S`, the universal property of weak
completions requires evaluating `(O[X_σ])†` at arbitrary tuples `y : σ → S†` in the weak completion
itself (the Kleisli extension of weak completion on finitely generated polynomial algebras).

On the ambient `π`-adic completions, `MvPolynomial.aeval y : O[X_σ] →ₐ[O] S†` induces a map
`(O[X_σ])^∧ →ₐ[O] (S†)^∧ ≃ₐ[O] S^∧`. We prove that this composite sends `(O[X_σ])†` into `S†`: if
each `yᵢ` has a degree-growth expansion in a finite generating family `x` of `S` with slope `C`, and
`z = ∑_{j ≥ 0} πʲ Pⱼ(X)` in `(O[X_σ])†` satisfies `deg Pⱼ ≤ d (j + 1)`, then each `Pⱼ(y)` has an
expansion `∑_{r ≥ 0} πʳ R_{j, r}(x)` with `deg R_{j, r} ≤ C (r + deg Pⱼ)`, and collecting along the
antidiagonals `j + r = m` yields an expansion of the image of `z` with slope `C (d + 1)`.

No noetherianity, valuation, completeness, or regularity of `π` is needed.

## Main definitions and results

* `TauCeti.Dagger.weakCompletion.aeval`: evaluation `(O[X_σ])† →ₐ[O] S†` of weakly completed
  polynomials at any tuple `y : σ → S†`.
* `TauCeti.Dagger.weakCompletion.aeval_of` and `TauCeti.Dagger.weakCompletion.aeval_of_X`:
  `aeval π y` extends `MvPolynomial.aeval y` along `O[X_σ] → (O[X_σ])†`, sending `X i` to `y i`.
* `TauCeti.Dagger.weakCompletion.algHom_ext_mvPolynomial`: homomorphisms from `(O[X_σ])†` into any
  `π`-adically separated `O`-algebra are determined by the images of the variables `X i`.
* `TauCeti.Dagger.weakCompletion.existsUnique_aeval`: `aeval π y` is the unique `O`-algebra
  homomorphism `(O[X_σ])† →ₐ[O] S†` sending `of π _ (X i)` to `y i`.
* `TauCeti.Dagger.weakCompletion.aeval_of_comp`, `TauCeti.Dagger.weakCompletion.map_comp_aeval`,
  and `TauCeti.Dagger.weakCompletion.aeval_comp`: compatibility of `aeval` with `weakCompletion.map`
  and with composition of weakly completed substitutions.

## References

* P. Monsky and G. Washnitzer, *Formal cohomology. I*, Ann. of Math. 88 (1968), §1–§2.
* M. van der Put, *The cohomology of Monsky and Washnitzer*, Mém. Soc. Math. France 23 (1986),
  §2, (2.1)–(2.2).
-/

public section

namespace TauCeti.Dagger.weakCompletion

open Finset MvPolynomial

section BoundedExpansion

variable {O S : Type*} [CommRing O] [CommRing S] [Algebra O S] [Algebra.FiniteType O S]

/-- Auxiliary predicate recording that `z : S†` has a `π`-adic polynomial expansion in `x` whose
`r`-th polynomial has total degree at most `C * (r + D)`. Tracking the additive offset `D`
separately from the slope `C` makes Cauchy products additive in `D` at fixed slope `C`. -/
private def hasBoundedExpansion {ι : Type*} (π : O) (x : ι → S) (C D : ℕ)
    (z : weakCompletion π S) : Prop :=
  ∃ R : ℕ → MvPolynomial ι O, (∀ r, (R r).totalDegree ≤ C * (r + D)) ∧
    ∀ k, eval π k z =
      Ideal.Quotient.mk _ (∑ r ∈ range k, algebraMap O S π ^ r * MvPolynomial.aeval x (R r))

private theorem hasBoundedExpansion.mono {ι : Type*} {π : O} {x : ι → S} {C D D' : ℕ}
    {z : weakCompletion π S} (h : hasBoundedExpansion π x C D z) (hD : D ≤ D') :
    hasBoundedExpansion π x C D' z := by
  obtain ⟨R, hdeg, hev⟩ := h
  exact ⟨R, fun r ↦ (hdeg r).trans (by gcongr), hev⟩

private theorem hasBoundedExpansion_algebraMap {ι : Type*} (π : O) (x : ι → S) (C D : ℕ) (a : O) :
    hasBoundedExpansion π x C D (algebraMap O (weakCompletion π S) a) := by
  refine ⟨fun r ↦ if r = 0 then MvPolynomial.C a else 0, fun r ↦ ?_, fun k ↦ ?_⟩
  · rcases r with _ | r <;> simp
  · rw [eval_algebraMap]
    rcases k with _ | k
    · rw [Ideal.Quotient.eq]
      simp
    · simp [Finset.sum_range_succ']

private theorem hasBoundedExpansion_one {ι : Type*} (π : O) (x : ι → S) (C D : ℕ) :
    hasBoundedExpansion π x C D 1 := by
  simpa using hasBoundedExpansion_algebraMap π x C D 1

private theorem hasBoundedExpansion_zero {ι : Type*} (π : O) (x : ι → S) (C D : ℕ) :
    hasBoundedExpansion π x C D 0 := by
  simpa using hasBoundedExpansion_algebraMap π x C D 0

private theorem hasBoundedExpansion_add {ι : Type*} {π : O} {x : ι → S} {C D : ℕ}
    {z w : weakCompletion π S} (hz : hasBoundedExpansion π x C D z)
    (hw : hasBoundedExpansion π x C D w) :
    hasBoundedExpansion π x C D (z + w) := by
  obtain ⟨R₁, hdeg₁, hev₁⟩ := hz
  obtain ⟨R₂, hdeg₂, hev₂⟩ := hw
  refine ⟨R₁ + R₂, fun r ↦ (totalDegree_add _ _).trans (max_le (hdeg₁ r) (hdeg₂ r)), fun k ↦ ?_⟩
  simp [hev₁ k, hev₂ k, mul_add, sum_add_distrib]

private theorem hasBoundedExpansion_sum {ι α : Type*} {π : O} {x : ι → S} {C D : ℕ}
    (s : Finset α) (f : α → weakCompletion π S)
    (hf : ∀ a ∈ s, hasBoundedExpansion π x C D (f a)) :
    hasBoundedExpansion π x C D (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hasBoundedExpansion_zero π x C D
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hasBoundedExpansion_add (hf a (mem_insert_self a s))
      (ih fun b hb ↦ hf b (mem_insert_of_mem hb))

private theorem hasBoundedExpansion_mul {ι : Type*} {π : O} {x : ι → S} {C D₁ D₂ : ℕ}
    {z₁ z₂ : weakCompletion π S} (h₁ : hasBoundedExpansion π x C D₁ z₁)
    (h₂ : hasBoundedExpansion π x C D₂ z₂) :
    hasBoundedExpansion π x C (D₁ + D₂) (z₁ * z₂) := by
  obtain ⟨R₁, hdeg₁, hev₁⟩ := h₁
  obtain ⟨R₂, hdeg₂, hev₂⟩ := h₂
  refine ⟨fun r ↦ ∑ ab ∈ antidiagonal r, R₁ ab.1 * R₂ ab.2, fun r ↦ ?_, fun k ↦ ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun ab hab ↦ ?_)
    rw [mem_antidiagonal] at hab
    refine (totalDegree_mul _ _).trans ((add_le_add (hdeg₁ ab.1) (hdeg₂ ab.2)).trans ?_)
    nlinarith
  · have hπ :
        Ideal.Quotient.mk (Ideal.span {algebraMap O S π} ^ k) (algebraMap O S π) ^ k = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (Ideal.subset_span rfl) k
    rw [map_mul, hev₁ k, hev₂ k]
    simp only [map_sum, map_mul, map_pow]
    exact TauCeti.sum_range_pow_mul_mul_sum_range_pow_mul_of_pow_eq_zero hπ _ _

private theorem hasBoundedExpansion_pow {ι : Type*} {π : O} {x : ι → S} {C D : ℕ}
    {z : weakCompletion π S} (hz : hasBoundedExpansion π x C D z) :
    ∀ e : ℕ, hasBoundedExpansion π x C (e * D) (z ^ e)
  | 0 => by simpa using hasBoundedExpansion_one π x C 0
  | e + 1 => by
    rw [pow_succ, Nat.succ_mul]
    exact hasBoundedExpansion_mul (hasBoundedExpansion_pow hz e) hz

private theorem hasBoundedExpansion_prod_pow {ι σ : Type*} {π : O} {x : ι → S} {C : ℕ}
    {y : σ → weakCompletion π S} (hy : ∀ i, hasBoundedExpansion π x C 1 (y i))
    (s : Finset σ) (g : σ → ℕ) :
    hasBoundedExpansion π x C (∑ i ∈ s, g i) (∏ i ∈ s, y i ^ g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasBoundedExpansion_one π x C 0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact hasBoundedExpansion_mul (by simpa using hasBoundedExpansion_pow (hy i) (g i)) ih

private theorem hasBoundedExpansion_aeval_mvPolynomial {ι σ : Type*} {π : O} {x : ι → S} {C : ℕ}
    {y : σ → weakCompletion π S} (hy : ∀ i, hasBoundedExpansion π x C 1 (y i))
    (P : MvPolynomial σ O) :
    hasBoundedExpansion π x C P.totalDegree (MvPolynomial.aeval y P) := by
  classical
  have hsum : MvPolynomial.aeval y P =
      ∑ ν ∈ P.support, MvPolynomial.aeval y (MvPolynomial.monomial ν (P.coeff ν)) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
  rw [hsum]
  refine hasBoundedExpansion_sum P.support _ fun ν hν ↦ ?_
  rw [MvPolynomial.aeval_monomial]
  have hmon : hasBoundedExpansion π x C (ν.sum fun _ e ↦ e)
      (algebraMap O (weakCompletion π S) (P.coeff ν) * ν.prod fun i e ↦ y i ^ e) := by
    simpa [Finsupp.prod, Finsupp.sum] using
      hasBoundedExpansion_mul (hasBoundedExpansion_algebraMap π x C 0 (P.coeff ν))
        (hasBoundedExpansion_prod_pow hy ν.support ν)
  exact hmon.mono (MvPolynomial.le_totalDegree hν)

private theorem aeval_mem {σ : Type*} [Finite σ] (π : O) (y : σ → weakCompletion π S)
    (z : weakCompletion π (MvPolynomial σ O)) :
    adicCompletionEquiv π S
      (AdicCompletion.mapₐ (MvPolynomial.aeval y)
        (by
            rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, AlgHom.commutes]
            exact Ideal.subset_span rfl)
        (z : piAdicCompletion π (MvPolynomial σ O))) ∈ weakCompletion π S := by
  classical
  obtain ⟨g, hg⟩ := Algebra.FiniteType.out (R := O) (A := S)
  let x : g → S := (↑)
  have hx : Algebra.adjoin O (Set.range x) = ⊤ := by
    simpa only [x, Subtype.range_coe_subtype, Finset.setOfPred_mem] using hg
  have hy_mem (i : σ) := (mem_weakCompletion_iff π hx).mp (y i).property
  choose c Q hQdeg hQev using hy_mem
  obtain ⟨C, hC⟩ := Finite.exists_le c
  have hy_exp (i : σ) : hasBoundedExpansion π x C 1 (y i) :=
    ⟨Q i, fun r ↦ (hQdeg i r).trans (Nat.mul_le_mul_right _ (hC i)),
      fun k ↦ (eval_eq π k (y i)).trans (hQev i k)⟩
  obtain ⟨d, P, hPdeg, hz⟩ :=
    (mem_weakCompletion_iff π (MvPolynomial.adjoin_range_X (R := O) (σ := σ))).mp z.property
  have hPy (j : ℕ) : hasBoundedExpansion π x C (d * (j + 1)) (MvPolynomial.aeval y (P j)) :=
    (hasBoundedExpansion_aeval_mvPolynomial hy_exp (P j)).mono (hPdeg j)
  choose R hRdeg hRev using hPy
  refine (mem_weakCompletion_iff π hx).mpr
    ⟨C * (d + 1), fun m ↦ ∑ jr ∈ antidiagonal m, R jr.1 jr.2, fun m ↦ ?_, fun k ↦ ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun jr hjr ↦ ?_)
    rw [mem_antidiagonal] at hjr
    refine (hRdeg jr.1 jr.2).trans ?_
    calc C * (jr.2 + d * (jr.1 + 1))
        ≤ C * ((d + 1) * (m + 1)) := Nat.mul_le_mul_left C (by nlinarith)
      _ = C * (d + 1) * (m + 1) := (mul_assoc _ _ _).symm
  · rw [evalₐ_adicCompletionEquiv, AdicCompletion.evalₐ_mapₐ, hz k, Ideal.quotientMap_mk,
      quotientPowEquiv_mk]
    simp only [MvPolynomial.aeval_X_left_apply, map_sum, map_mul, map_pow, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, AlgHom.commutes, hRev]
    let e := Ideal.Quotient.mk (Ideal.span {algebraMap O S π} ^ k) (algebraMap O S π)
    let u (j r : ℕ) :=
      Ideal.Quotient.mk (Ideal.span {algebraMap O S π} ^ k) (MvPolynomial.aeval x (R j r))
    have hek : e ^ k = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (Ideal.subset_span rfl) k
    have htri := (TauCeti.sum_range_triangle k (fun j r ↦ e ^ (j + r) * u j r) fun j r hjr ↦ by
      have hexp : j + r = k + (j + r - k) := by omega
      rw [hexp, pow_add, hek, zero_mul, zero_mul]).symm
    calc (∑ j ∈ range k, e ^ j * ∑ r ∈ range k, e ^ r * u j r)
        = ∑ j ∈ range k, ∑ r ∈ range k, e ^ (j + r) * u j r := by
          simp_rw [mul_sum, ← mul_assoc, ← pow_add]
      _ = ∑ m ∈ range k, ∑ j ∈ range (m + 1), e ^ (j + (m - j)) * u j (m - j) := htri
      _ = ∑ m ∈ range k, e ^ m * ∑ jr ∈ antidiagonal m, u jr.1 jr.2 := by
          refine sum_congr rfl fun m _ ↦ ?_
          rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ u m, mul_sum]
          exact sum_congr rfl fun j hj ↦ by
            rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (mem_range.mp hj))]

end BoundedExpansion

section Aeval

variable {O S T σ τ : Type*} [CommRing O] [CommRing S] [CommRing T] [Algebra O S] [Algebra O T]
  (π : O) [Algebra.FiniteType O S] [Algebra.FiniteType O T] [Finite σ] [Finite τ]

/-- Overconvergent evaluation `(O[X_σ])† →ₐ[O] S†` of weakly completed polynomials in finitely many
variables at any tuple `y : σ → S†` in the weak completion of `S`. -/
noncomputable def aeval (y : σ → weakCompletion π S) :
    weakCompletion π (MvPolynomial σ O) →ₐ[O] weakCompletion π S :=
  (((adicCompletionEquiv π S).toAlgHom.restrictScalars O).comp
    ((AdicCompletion.mapₐ (MvPolynomial.aeval y)
      (by
            rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, AlgHom.commutes]
            exact Ideal.subset_span rfl)).comp
      (weakCompletion π (MvPolynomial σ O)).val)).codRestrict _ (aeval_mem π y)

/-- On the ambient `π`-adic completions, `aeval π y` is induced by `MvPolynomial.aeval y` via the
completion comparison `adicCompletionEquiv π S : (S†)^∧ ≃ₐ S^∧`. -/
@[simp]
theorem coe_aeval (y : σ → weakCompletion π S) (z : weakCompletion π (MvPolynomial σ O)) :
    (aeval π y z : piAdicCompletion π S) =
      adicCompletionEquiv π S
        (AdicCompletion.mapₐ (MvPolynomial.aeval y)
          (by
            rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, AlgHom.commutes]
            exact Ideal.subset_span rfl)
          (z : piAdicCompletion π (MvPolynomial σ O))) :=
  (rfl)

/-- Modulo `π ^ n`, `aeval π y` applies the quotient map induced by `MvPolynomial.aeval y` and
identifies `(S†) ⧸ πⁿ (S†)` with `S ⧸ πⁿ S`. -/
@[simp]
theorem eval_aeval (y : σ → weakCompletion π S) (n : ℕ) (z : weakCompletion π (MvPolynomial σ O)) :
    eval π n (aeval π y z) =
      quotientPowEquiv π n
        (Ideal.quotientMap (Ideal.span {algebraMap O (weakCompletion π S) π} ^ n)
          (MvPolynomial.aeval y).toRingHom
          ((Ideal.pow_right_mono
            (by
              rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, AlgHom.toRingHom_eq_coe,
                AlgHom.coe_toRingHom, AlgHom.commutes]
              exact Ideal.subset_span rfl) n).trans
            (Ideal.le_comap_pow _ n))
          (eval π n z)) := by
  rw [eval_eq, coe_aeval, evalₐ_adicCompletionEquiv, AdicCompletion.evalₐ_mapₐ, eval_eq]

/-- Overconvergent evaluation extends polynomial evaluation along `O[X_σ] → (O[X_σ])†`. -/
@[simp]
theorem aeval_of (y : σ → weakCompletion π S) (P : MvPolynomial σ O) :
    aeval π y (of π (MvPolynomial σ O) P) = MvPolynomial.aeval y P := by
  apply Subtype.ext
  rw [coe_aeval, coe_of, AdicCompletion.mapₐ_of, adicCompletionEquiv_of]

/-- Homomorphism-level form of `aeval_of`. -/
theorem aeval_comp_of (y : σ → weakCompletion π S) :
    (aeval π y).comp (of π (MvPolynomial σ O)) = MvPolynomial.aeval y :=
  AlgHom.ext (aeval_of π y)

/-- Overconvergent evaluation sends the image of `X i` in `(O[X_σ])†` to `y i`. -/
theorem aeval_of_X (y : σ → weakCompletion π S) (i : σ) :
    aeval π y (of π (MvPolynomial σ O) (MvPolynomial.X i)) = y i := by
  rw [aeval_of, MvPolynomial.aeval_X]

/-- Two `O`-algebra homomorphisms from `(O[X_σ])†` into a `π`-adically separated `O`-algebra agree
as soon as they agree on the images of the variables `X i`. -/
theorem algHom_ext_mvPolynomial {B : Type*} [CommRing B] [Algebra O B]
    [IsHausdorff (Ideal.span {algebraMap O B π}) B]
    {φ ψ : weakCompletion π (MvPolynomial σ O) →ₐ[O] B}
    (h : ∀ i, φ (of π (MvPolynomial σ O) (MvPolynomial.X i)) =
      ψ (of π (MvPolynomial σ O) (MvPolynomial.X i))) :
    φ = ψ := by
  have hpoly : φ.comp (of π (MvPolynomial σ O)) = ψ.comp (of π (MvPolynomial σ O)) :=
    MvPolynomial.algHom_ext h
  exact algHom_ext π fun P ↦ DFunLike.congr_fun hpoly P

/-- An `O`-algebra homomorphism `(O[X_σ])† →ₐ[O] S†` equals `aeval π y` if and only if it sends the
image of each variable `X i` to `y i`. -/
theorem eq_aeval_iff (y : σ → weakCompletion π S)
    (φ : weakCompletion π (MvPolynomial σ O) →ₐ[O] weakCompletion π S) :
    φ = aeval π y ↔ ∀ i, φ (of π (MvPolynomial σ O) (MvPolynomial.X i)) = y i :=
  ⟨fun h i ↦ h ▸ aeval_of_X π y i, fun h ↦
    algHom_ext_mvPolynomial π fun i ↦ (h i).trans (aeval_of_X π y i).symm⟩

/-- Universal property of `(O[X_σ])†` with respect to weak completions: for every tuple
`y : σ → S†`, `aeval π y` is the unique `O`-algebra homomorphism `(O[X_σ])† →ₐ[O] S†` sending the
image of each variable `X i` to `y i`. -/
theorem existsUnique_aeval (y : σ → weakCompletion π S) :
    ∃! φ : weakCompletion π (MvPolynomial σ O) →ₐ[O] weakCompletion π S,
      ∀ i, φ (of π (MvPolynomial σ O) (MvPolynomial.X i)) = y i :=
  ⟨aeval π y, aeval_of_X π y, fun _ h ↦ (eq_aeval_iff π y _).mpr h⟩

/-- Evaluating at elements coming from `S` agrees with the functorial map `map π (aeval x)`. -/
@[simp]
theorem aeval_of_comp (x : σ → S) :
    aeval π (of π S ∘ x) = map π (MvPolynomial.aeval x) :=
  algHom_ext_mvPolynomial π fun i ↦ by simp

/-- Evaluating `(O[X_σ])†` at its own variables is the identity. -/
theorem aeval_X_comp_of :
    aeval π (of π (MvPolynomial σ O) ∘ MvPolynomial.X) =
      AlgHom.id O (weakCompletion π (MvPolynomial σ O)) := by
  rw [aeval_of_comp, MvPolynomial.aeval_X_left, map_id]

/-- Post-composing `aeval π y` with `map π f` evaluates at `map π f ∘ y`. -/
theorem map_comp_aeval (f : S →ₐ[O] T) (y : σ → weakCompletion π S) :
    (map π f).comp (aeval π y) = aeval π (map π f ∘ y) :=
  algHom_ext_mvPolynomial π fun i ↦ by simp

/-- Pointwise form of `map_comp_aeval`. -/
@[simp]
theorem map_aeval (f : S →ₐ[O] T) (y : σ → weakCompletion π S)
    (z : weakCompletion π (MvPolynomial σ O)) :
    map π f (aeval π y z) = aeval π (map π f ∘ y) z :=
  DFunLike.congr_fun (map_comp_aeval π f y) z

/-- Associativity of overconvergent evaluation (Kleisli composition on polynomial weak
completions). -/
theorem aeval_comp (y : τ → weakCompletion π S) (w : σ → weakCompletion π (MvPolynomial τ O)) :
    (aeval π y).comp (aeval π w) = aeval π (aeval π y ∘ w) :=
  algHom_ext_mvPolynomial π fun i ↦ by simp

/-- Pointwise form of `aeval_comp`. -/
@[simp]
theorem aeval_aeval (y : τ → weakCompletion π S) (w : σ → weakCompletion π (MvPolynomial τ O))
    (z : weakCompletion π (MvPolynomial σ O)) :
    aeval π y (aeval π w z) = aeval π (aeval π y ∘ w) z :=
  DFunLike.congr_fun (aeval_comp π y w) z

end Aeval

end TauCeti.Dagger.weakCompletion
