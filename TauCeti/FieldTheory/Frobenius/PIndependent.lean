/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Finsupp.Single
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import TauCeti.Algebra.Polynomial.PowChar

/-!
# `p`-independent families and pairs

Let `k` be a field of characteristic `p > 0`. A family `b : ι → k` is `p`-independent when its
`p`-monomials `∏ i, b i ^ (e i)` (`e : ι →₀ Fin p`, so finitely many nonzero exponents, each `< p`)
are linearly independent over the subfield `k ^ p` of `p`-th powers. This file develops both the
two-element specialization `IsPIndependentPair` and the general indexed predicate `IsPIndependent`,
together with the `k ^ p`-subalgebra/span identification, the Kummer minimal polynomial
`X ^ p - x ^ p` over any subfield containing `k ^ p`, the one-element extension criterion, and
closure under unions of chains.

## Main definitions

* `TauCeti.IsPIndependentPair`: two elements `a, b ∈ k` are `p`-independent.
* `TauCeti.pMonomial`: the `p`-monomial `e.prod (fun i m ↦ b i ^ (m : ℕ))` attached to
  `e : ι →₀ Fin p`.
* `TauCeti.IsPIndependent`: a family `b : ι → k` has `k ^ p`-linearly independent `p`-monomials.

## Main results

* `TauCeti.isPIndependentPair_iff_linearIndependent`,
  `TauCeti.isPIndependentPair_iff_isPIndependent`: `p`-independence of a pair agrees with linear
  independence of `a ^ i * b ^ j` (`i, j < p`) and with `IsPIndependent p ![a, b]`.
* `TauCeti.adjoin_fieldRange_frobenius_toSubmodule`,
  `TauCeti.coe_intermediateField_adjoin_fieldRange_frobenius`: `k ^ p[b]` and `k ^ p(b)` coincide
  with the `k ^ p`-linear span of the `p`-monomials in `b`.
* `TauCeti.minpoly_eq_X_pow_sub_C_of_fieldRange_frobenius_le`: for a subfield `L ≥ k ^ p` and
  `x ∉ L`, the minimal polynomial of `x` over `L` is `X ^ p - C (x ^ p)`.
* `TauCeti.isPIndependent_sumElim_unique_iff`, `TauCeti.isPIndependent_insert_iff`: adjoining `x`
  preserves `p`-independence if and only if `x` is outside the `k ^ p`-span of the `p`-monomials.
* `TauCeti.isPIndependent_sUnion_of_isChain`: `p`-independence is preserved under unions of chains.

## References

* H. Matsumura, *Commutative Ring Theory*, 2nd ed., Cambridge Univ. Press, 1989, §26.
* The Stacks Project, Definition 15.47.1 (Tag 07P1).
* S. Lang, *Algebra*, 3rd ed., GTM 211, Springer, 2002, Chapter VIII, Section 4.
-/

public section

open Finset

namespace TauCeti

section Pair

variable {k : Type*} [Field k] {p : ℕ} {a b : k}

variable (p) in
/-- `a` and `b` are `p`-independent: the monomials `a ^ i * b ^ j` with `i, j < p` are linearly
independent over the subfield of `p`-th powers of `k`. -/
def IsPIndependentPair (a b : k) : Prop :=
  ∀ c : ℕ → ℕ → k,
    ∑ i ∈ range p, ∑ j ∈ range p, c i j ^ p * a ^ i * b ^ j = 0 → ∀ i < p, ∀ j < p, c i j = 0

/-- Unfolding `IsPIndependentPair`: every vanishing combination `∑ cᵢⱼ ^ p a ^ i b ^ j` with
`i, j < p` has zero coefficients. -/
theorem isPIndependentPair_iff : IsPIndependentPair p a b ↔ ∀ c : ℕ → ℕ → k,
    ∑ i ∈ range p, ∑ j ∈ range p, c i j ^ p * a ^ i * b ^ j = 0 → ∀ i < p, ∀ j < p, c i j = 0 :=
  Iff.rfl

/-- `a` and `b` are `p`-independent exactly when the monomials `a ^ i * b ^ j` with `i, j < p`
are linearly independent over the field range `k ^ p` of Frobenius. -/
theorem isPIndependentPair_iff_linearIndependent [ExpChar k p] :
    IsPIndependentPair p a b ↔ LinearIndependent (frobenius k p).fieldRange
      (fun ij : Fin p × Fin p ↦ a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ)) := by
  have hp : p ≠ 0 := (expChar_pos k p).ne'
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h g hg ij
    choose c hc using fun ij ↦ RingHom.mem_fieldRange.mp (g ij).2
    have := h (fun i j ↦ if h : i < p ∧ j < p then c (⟨i, h.1⟩, ⟨j, h.2⟩) else 0) ?_
      ij.1 ij.1.2 ij.2 ij.2.2
    · rw [Subtype.ext_iff, ← hc]
      simpa using this
    · rw [Fintype.sum_prod_type] at hg
      simpa [sum_range, Subfield.smul_def, ← hc, frobenius_def, mul_assoc] using hg
  · intro h c hc i hi j hj
    have := h (fun ij ↦ ⟨c ij.1 ij.2 ^ p, c ij.1 ij.2, frobenius_def ..⟩) ?_ (⟨i, hi⟩, ⟨j, hj⟩)
    · simpa [Subtype.ext_iff, hp] using this
    · rw [Fintype.sum_prod_type]
      simpa [sum_range, Subfield.smul_def, mul_assoc] using hc

/-- A vanishing combination `∑ cᵢⱼ ^ p a ^ i b ^ j` of a `p`-independent pair has all its
coefficients `cᵢⱼ` with `i, j < p` equal to zero. -/
theorem IsPIndependentPair.eq_zero (hab : IsPIndependentPair p a b) {c : ℕ → ℕ → k}
    (h : ∑ i ∈ range p, ∑ j ∈ range p, c i j ^ p * a ^ i * b ^ j = 0) {i j : ℕ} (hi : i < p)
    (hj : j < p) : c i j = 0 :=
  hab c h i hi j hj

open Polynomial in
/-- `p`-independence of `a` and `b` over `k ^ p` gives `p`-independence over `k[X] ^ p`: a
vanishing combination `∑ Pᵢⱼ ^ p a ^ i b ^ j` with polynomial `Pᵢⱼ` has `Pᵢⱼ = 0` for `i, j < p`. -/
theorem IsPIndependentPair.eq_zero_of_sum_pow_mul_C_eq_zero [ExpChar k p]
    (hab : IsPIndependentPair p a b) {P : ℕ → ℕ → k[X]}
    (h : ∑ i ∈ range p, ∑ j ∈ range p, P i j ^ p * C (a ^ i * b ^ j) = 0) {i j : ℕ} (hi : i < p)
    (hj : j < p) : P i j = 0 := by
  ext n
  have hn := congrArg (fun q : k[X] ↦ q.coeff (p * n)) h
  simp only [finsetSum_coeff, coeff_mul_C, coeff_pow_char_mul, coeff_zero] at hn
  exact hab.eq_zero (c := fun i j ↦ (P i j).coeff n) (by simpa only [mul_assoc] using hn) hi hj

/-- `α ∉ k + k β` when `α` and `β` are `p`-th roots of a `p`-independent pair `a, b`. -/
theorem notMem_span_pair_of_pow_eq [hp : Fact p.Prime] [CharP k p]
    (hab : IsPIndependentPair p a b) {K : Type*} [Field K] [Algebra k K] {α β : K}
    (hα : α ^ p = algebraMap k K a) (hβ : β ^ p = algebraMap k K b) :
    α ∉ Submodule.span k {1, β} := by
  have := charP_of_injective_algebraMap (algebraMap k K).injective p
  rw [Submodule.mem_span_pair]
  rintro ⟨c₀, c₂, h⟩
  have hpow := congrArg (· ^ p) h
  simp only [add_pow_char, Algebra.smul_def, mul_pow, mul_one, hα, hβ, ← map_pow,
    ← map_mul, ← map_add] at hpow
  have := hab.eq_zero (c := fun i j ↦ if i = 0 ∧ j = 0 then c₀ else if i = 1 ∧ j = 0 then -1 else
      if i = 0 ∧ j = 1 then c₂ else 0) ?_ hp.out.one_lt hp.out.pos
  · simp at this
  · have hpa := (algebraMap k K).injective hpow
    have hp0 : p ≠ 0 := hp.out.ne_zero
    have h0 : 0 ∈ range p := mem_range.mpr hp.out.pos
    have h1 : 1 ∈ range p := mem_range.mpr hp.out.one_lt
    rw [sum_eq_add 0 1 zero_ne_one (fun i _ hi ↦ sum_eq_zero fun j _ ↦ by
        simp [hi.1, hi.2, zero_pow hp0]) (absurd h0) (absurd h1),
      sum_eq_add 0 1 zero_ne_one (fun j _ hj ↦ by simp [hj.1, hj.2, zero_pow hp0])
        (absurd h0) (absurd h1),
      sum_eq_single 0 (fun j _ hj ↦ by simp [hj, zero_pow hp0]) (absurd h0)]
    simp only [and_true, one_ne_zero, zero_ne_one, and_false, ite_true, ite_false, pow_zero,
      pow_one, mul_one, neg_one_pow_char]
    linear_combination hpa

end Pair

section PMonomial

variable (p : ℕ) [NeZero p] {R : Type*} [CommMonoid R] {ι ι' : Type*}

/-- The `p`-monomial `∏ i, b i ^ (e i)` attached to a finitely supported exponent `e : ι →₀ Fin p`.
Each exponent lies strictly below `p`, and only finitely many indices appear in the product. -/
def pMonomial (b : ι → R) (e : ι →₀ Fin p) : R :=
  e.prod fun i m ↦ b i ^ (m : ℕ)

@[simp]
theorem pMonomial_zero (b : ι → R) : pMonomial p b 0 = 1 :=
  Finsupp.prod_zero_index

@[simp]
theorem pMonomial_single (b : ι → R) (i : ι) (m : Fin p) :
    pMonomial p b (Finsupp.single i m) = b i ^ (m : ℕ) :=
  Finsupp.prod_single_index (by simp)

@[simp]
theorem pMonomial_embDomain (b : ι → R) (f : ι' ↪ ι) (e : ι' →₀ Fin p) :
    pMonomial p b (e.embDomain f) = pMonomial p (b ∘ f) e :=
  Finsupp.prod_embDomain

@[simp]
theorem pMonomial_equivMapDomain (b : ι → R) (f : ι' ≃ ι) (e : ι' →₀ Fin p) :
    pMonomial p b (e.equivMapDomain f) = pMonomial p (b ∘ f) e :=
  Finsupp.prod_equivMapDomain f e fun i m ↦ b i ^ (m : ℕ)

/-- The `p`-monomial `pMonomial p b e` is the product over `e.support` of `b i ^ (e i : ℕ)`. -/
theorem pMonomial_eq_prod_support (b : ι → R) (e : ι →₀ Fin p) :
    pMonomial p b e = ∏ i ∈ e.support, b i ^ (e i : ℕ) :=
  (rfl)

/-- On any finite superset `s ⊇ e.support`, `pMonomial p b e` equals `∏ i ∈ s, b i ^ (e i : ℕ)`. -/
theorem pMonomial_of_support_subset (b : ι → R) {e : ι →₀ Fin p} {s : Finset ι}
    (hs : e.support ⊆ s) :
    pMonomial p b e = ∏ i ∈ s, b i ^ (e i : ℕ) :=
  e.prod_of_support_subset hs _ (by simp)

theorem pMonomial_eq_prod [Fintype ι] (b : ι → R) (e : ι →₀ Fin p) :
    pMonomial p b e = ∏ i, b i ^ (e i : ℕ) :=
  Finsupp.prod_fintype e _ (by simp)

@[simp]
theorem pMonomial_equivFunOnFinite_symm [Fintype ι] (b : ι → R) (e : ι → Fin p) :
    pMonomial p b (Finsupp.equivFunOnFinite.symm e) = ∏ i, b i ^ (e i : ℕ) := by
  rw [pMonomial_eq_prod]
  rfl

end PMonomial

section Family

variable (p : ℕ) [NeZero p] {k : Type*} [Field k] [ExpChar k p] {ι ι' : Type*}

/-- A family `b : ι → k` in a field of exponential characteristic `p` is `p`-independent if its
`p`-monomials `pMonomial p b` (`e : ι →₀ Fin p`) are linearly independent over the subfield
`k ^ p = (frobenius k p).fieldRange` of `p`-th powers. -/
def IsPIndependent (b : ι → k) : Prop :=
  LinearIndependent (frobenius k p).fieldRange (pMonomial p b)

theorem isPIndependent_def {b : ι → k} :
    IsPIndependent p b ↔ LinearIndependent (frobenius k p).fieldRange (pMonomial p b) :=
  (Iff.rfl)

/-- On a finite index type, `p`-independence is linear independence of `∏ i, b i ^ (e i)` indexed by
functions `e : ι → Fin p`. -/
theorem isPIndependent_iff_of_fintype [Fintype ι] {b : ι → k} :
    IsPIndependent p b ↔
      LinearIndependent (frobenius k p).fieldRange (fun e : ι → Fin p ↦ ∏ i, b i ^ (e i : ℕ)) := by
  rw [isPIndependent_def,
    ← linearIndependent_equiv (Finsupp.equivFunOnFinite.symm : (ι → Fin p) ≃ _)]
  simp [Function.comp_def]

/-- Two elements `x, y : k` form a `p`-independent pair if and only if `![x, y]` is
`p`-independent. -/
theorem isPIndependentPair_iff_isPIndependent {x y : k} :
    IsPIndependentPair p x y ↔ IsPIndependent p ![x, y] := by
  rw [isPIndependentPair_iff_linearIndependent, isPIndependent_iff_of_fintype]
  let e : (Fin 2 → Fin p) ≃ Fin p × Fin p :=
    { toFun := fun f ↦ (f 0, f 1)
      invFun := fun ij ↦ ![ij.1, ij.2]
      left_inv := fun f ↦ by ext i; fin_cases i <;> rfl
      right_inv := fun _ ↦ rfl }
  rw [← linearIndependent_equiv e.symm]
  convert Iff.rfl using 2
  ext ij
  simp [Fin.prod_univ_two]
  rfl

/-- Every empty family is `p`-independent: its unique `p`-monomial is `1 ≠ 0`. -/
theorem isPIndependent_of_isEmpty [IsEmpty ι] (b : ι → k) : IsPIndependent p b := by
  rw [isPIndependent_def, linearIndependent_unique_iff]
  simp [Subsingleton.elim (default : ι →₀ Fin p) 0]

variable {p}

/-- `p`-independence passes to subfamilies along any injection. -/
theorem IsPIndependent.comp {b : ι → k} (hb : IsPIndependent p b) (f : ι' → ι)
    (hf : Function.Injective f) : IsPIndependent p (b ∘ f) := by
  rw [isPIndependent_def] at hb ⊢
  simpa [Function.comp_def] using
    hb.comp (Finsupp.embDomain ⟨f, hf⟩) (Finsupp.embDomain_injective ⟨f, hf⟩)

/-- Reindexing along an equivalence preserves `p`-independence. -/
theorem isPIndependent_equiv (e : ι' ≃ ι) {b : ι → k} :
    IsPIndependent p (b ∘ e) ↔ IsPIndependent p b :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.comp e.symm e.symm.injective,
    fun h ↦ h.comp e e.injective⟩

/-- No member of a `p`-independent family (for `1 < p`) can lie in `k ^ p`. -/
theorem not_isPIndependent_of_mem_fieldRange_frobenius (hp : 1 < p) {b : ι → k} {i : ι}
    (hi : b i ∈ (frobenius k p).fieldRange) : ¬ IsPIndependent p b := by
  classical
  intro hb
  let e₁ : ι →₀ Fin p := Finsupp.single i ⟨1, hp⟩
  have hne : e₁ ≠ 0 := Finsupp.single_ne_zero.mpr (Fin.ne_of_gt Nat.zero_lt_one)
  let f : (ι →₀ Fin p) →₀ (frobenius k p).fieldRange :=
    Finsupp.single e₁ 1 - Finsupp.single 0 ⟨b i, hi⟩
  have hcomb : Finsupp.linearCombination (frobenius k p).fieldRange (pMonomial p b) f = 0 := by
    simp [f, e₁, Subfield.smul_def]
  have hf0 : f e₁ = 0 := by
    rw [linearIndependent_iff.mp hb f hcomb]
    rfl
  have hf1 : f e₁ = 1 := by simp [f, hne]
  exact one_ne_zero (hf1.symm.trans hf0)

/-- For `1 < p`, every `p`-independent family is injective. -/
theorem IsPIndependent.injective (hp : 1 < p) {b : ι → k} (hb : IsPIndependent p b) :
    Function.Injective b := by
  classical
  intro i j hij
  by_contra hne
  have heq : (Finsupp.single i ⟨1, hp⟩ : ι →₀ Fin p) = Finsupp.single j ⟨1, hp⟩ :=
    LinearIndependent.injective hb (by simp only [pMonomial_single, hij])
  have hi := DFunLike.congr_fun heq i
  simp [hne] at hi

end Family

section PrimeChar

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*} [Field k] [CharP k p] {ι : Type*}

private theorem mul_pMonomial_mem_span (b : ι → k) (i : ι) (e : ι →₀ Fin p) :
    b i * pMonomial p b e ∈
      Submodule.span (frobenius k p).fieldRange (Set.range (pMonomial p b)) := by
  classical
  let s : Finset ι := insert i e.support
  have he : pMonomial p b e = b i ^ (e i : ℕ) * ∏ j ∈ s.erase i, b j ^ (e j : ℕ) := by
    rw [pMonomial_of_support_subset p b (subset_insert i _),
      ← mul_prod_erase s _ (mem_insert_self i _)]
  have hup (m : Fin p) : pMonomial p b (e.update i m) =
      b i ^ (m : ℕ) * ∏ j ∈ s.erase i, b j ^ (e j : ℕ) := by
    rw [pMonomial_of_support_subset p b (Finsupp.support_update_subset e i),
      ← mul_prod_erase s _ (mem_insert_self i _), Finsupp.coe_update, Function.update_self]
    congr 1
    exact prod_congr rfl fun j hj ↦ by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [he, ← mul_assoc, ← pow_succ']
  by_cases hlt : (e i : ℕ) + 1 < p
  · rw [← hup ⟨(e i : ℕ) + 1, hlt⟩]
    exact Submodule.subset_span ⟨_, rfl⟩
  · have heq : (e i : ℕ) + 1 = p := by omega
    have h0 : ∏ j ∈ s.erase i, b j ^ (e j : ℕ) = pMonomial p b (e.update i 0) := by
      simpa using (hup 0).symm
    have hsmul : b i ^ p * pMonomial p b (e.update i 0) =
        (⟨b i ^ p, b i, rfl⟩ : (frobenius k p).fieldRange) • pMonomial p b (e.update i 0) := by
      rw [Subfield.smul_def, smul_eq_mul]
    rw [heq, h0, hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The `k ^ p`-subalgebra generated by `b` coincides as a `k ^ p`-submodule with the linear span
of the `p`-monomials in `b`. -/
theorem adjoin_fieldRange_frobenius_toSubmodule (b : ι → k) :
    (Algebra.adjoin (frobenius k p).fieldRange (Set.range b)).toSubmodule =
      Submodule.span (frobenius k p).fieldRange (Set.range (pMonomial p b)) := by
  set K₀ := (frobenius k p).fieldRange
  set M := Submodule.span K₀ (Set.range (pMonomial p b))
  apply le_antisymm
  · have hclosed : ∀ z ∈ Algebra.adjoin K₀ (Set.range b), ∀ y ∈ M, z * y ∈ M := by
      intro z hz
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨i, rfl⟩ y hy
        refine Submodule.span_induction ?_ (by simp)
          (fun u v _ _ hu hv ↦ by rw [mul_add]; exact M.add_mem hu hv)
          (fun c u _ hu ↦ by rw [mul_smul_comm]; exact M.smul_mem c hu) hy
        rintro _ ⟨e, rfl⟩
        exact mul_pMonomial_mem_span b i e
      · intro c y hy
        simpa [Algebra.smul_def] using M.smul_mem c hy
      · intro u v _ _ hu hv y hy
        rw [add_mul]
        exact M.add_mem (hu y hy) (hv y hy)
      · intro u v _ _ hu hv y hy
        rw [mul_assoc]
        exact hu _ (hv y hy)
    intro z hz
    simpa using hclosed z hz 1 (Submodule.subset_span ⟨0, pMonomial_zero p b⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, pMonomial_eq_prod_support]
    exact prod_mem fun i _ ↦ pow_mem (Algebra.subset_adjoin (Set.mem_range_self i)) _

/-- Every element of `k` is integral over `k ^ p`, so the intermediate field `k ^ p(b)` has the
same underlying set as the `k ^ p`-linear span of `pMonomial p b`. -/
theorem coe_intermediateField_adjoin_fieldRange_frobenius (b : ι → k) :
    (IntermediateField.adjoin (frobenius k p).fieldRange (Set.range b) : Set k) =
      (Submodule.span (frobenius k p).fieldRange (Set.range (pMonomial p b)) : Set k) := by
  have halg : ∀ x ∈ Set.range b, IsAlgebraic (frobenius k p).fieldRange x := fun x _ ↦
    ⟨Polynomial.X ^ p - Polynomial.C ⟨x ^ p, x, rfl⟩,
      (Polynomial.monic_X_pow_sub_C _ hp.out.ne_zero).ne_zero, by
        rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
        exact sub_self _⟩
  rw [← IntermediateField.coe_toSubalgebra,
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg,
    ← Subalgebra.coe_toSubmodule, adjoin_fieldRange_frobenius_toSubmodule]

/-- Over any subfield `L` containing `k ^ p`, an element `x ∉ L` has minimal polynomial
`X ^ p - C (x ^ p)`. -/
theorem minpoly_eq_X_pow_sub_C_of_fieldRange_frobenius_le {L : Subfield k}
    (hL : (frobenius k p).fieldRange ≤ L) {x : k} (hx : x ∉ L) :
    minpoly L x = Polynomial.X ^ p - Polynomial.C ⟨x ^ p, hL ⟨x, rfl⟩⟩ := by
  have hmonic : (Polynomial.X ^ p - Polynomial.C (⟨x ^ p, hL ⟨x, rfl⟩⟩ : L)).Monic :=
    Polynomial.monic_X_pow_sub_C _ hp.out.ne_zero
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C (⟨x ^ p, hL ⟨x, rfl⟩⟩ : L)) :=
    irreducible_X_pow_sub_C_of_prime hp.out fun y hy ↦ hx <| by
      have hy' : (y : k) ^ p = x ^ p := congrArg Subtype.val hy
      exact frobenius_inj k p hy' ▸ y.2
  have haeval : Polynomial.aeval x
      (Polynomial.X ^ p - Polynomial.C (⟨x ^ p, hL ⟨x, rfl⟩⟩ : L)) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact sub_self _
  exact (minpoly.eq_of_irreducible_of_monic hirr haeval hmonic).symm

open scoped IntermediateField in
/-- Over any subfield `L` containing `k ^ p`, an element `x ∉ L` has `1, x, …, x ^ (p - 1)`
linearly independent over `L`. -/
theorem linearIndependent_pow_of_fieldRange_frobenius_le {L : Subfield k}
    (hL : (frobenius k p).fieldRange ≤ L) {x : k} (hx : x ∉ L) :
    LinearIndependent L (fun m : Fin p ↦ x ^ (m : ℕ)) := by
  have hx_int : IsIntegral L x :=
    ⟨Polynomial.X ^ p - Polynomial.C ⟨x ^ p, hL ⟨x, rfl⟩⟩,
      Polynomial.monic_X_pow_sub_C _ hp.out.ne_zero, by
        rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
        exact sub_self _⟩
  let pb := IntermediateField.adjoin.powerBasis hx_int
  have hdim : pb.dim = p := by
    rw [IntermediateField.adjoin.powerBasis_dim,
      minpoly_eq_X_pow_sub_C_of_fieldRange_frobenius_le hL hx,
      Polynomial.natDegree_X_pow_sub_C]
  have hli := pb.basis.linearIndependent.map' L⟮x⟯.val.toLinearMap
    (LinearMap.ker_eq_bot.mpr L⟮x⟯.val.injective)
  have hcast := hli.comp (Fin.cast hdim.symm) (Fin.cast_injective _)
  convert hcast using 1
  ext m
  simp [pb]

/-- Equivalence `(ι ⊕ κ →₀ Fin p) ≃ (ι →₀ Fin p) × Fin p` splitting off a `[Unique κ]` exponent. -/
private noncomputable def sumUniqueFinsuppEquiv (p : ℕ) [NeZero p] (ι κ : Type*) [Unique κ] :
    (ι ⊕ κ →₀ Fin p) ≃ (ι →₀ Fin p) × Fin p :=
  Finsupp.sumFinsuppEquivProdFinsupp.trans
    (Equiv.prodCongr (Equiv.refl _)
      (Finsupp.equivFunOnFinite.trans (Equiv.funUnique κ (Fin p))))

private theorem pMonomial_sumUniqueFinsuppEquiv_symm (p : ℕ) [NeZero p] {R : Type*} [CommMonoid R]
    {κ : Type*} [Unique κ] (b : ι → R) (x : R) (em : (ι →₀ Fin p) × Fin p) :
    pMonomial p (Sum.elim b (fun _ : κ ↦ x)) ((sumUniqueFinsuppEquiv p ι κ).symm em) =
      pMonomial p b em.1 * x ^ (em.2 : ℕ) := by
  classical
  let f := (sumUniqueFinsuppEquiv p ι κ).symm em
  have hf_inl (i : ι) : f (Sum.inl i) = em.1 i := by
    simp [f, sumUniqueFinsuppEquiv, Finsupp.sumFinsuppEquivProdFinsupp]
  have hf_inr (u : κ) : f (Sum.inr u) = em.2 := by
    rw [Subsingleton.elim u default]
    simp [f, sumUniqueFinsuppEquiv, Finsupp.sumFinsuppEquivProdFinsupp]
  let S : Finset (ι ⊕ κ) := em.1.support.map Function.Embedding.inl ∪ {Sum.inr default}
  have hsub : f.support ⊆ S := by
    rintro (i | u) hz
    · rw [Finsupp.mem_support_iff, hf_inl] at hz
      exact mem_union_left _ (mem_map.mpr ⟨i, Finsupp.mem_support_iff.mpr hz, rfl⟩)
    · rw [Subsingleton.elim u default]
      exact mem_union_right _ (mem_singleton_self _)
  have hdisj : Disjoint (em.1.support.map Function.Embedding.inl) {Sum.inr (default : κ)} := by
    simp
  rw [pMonomial_of_support_subset p _ hsub, prod_union hdisj,
    prod_map, prod_singleton, hf_inr (default : κ)]
  have h1 : (∏ x ∈ em.1.support, b x ^ (f (Sum.inl x) : ℕ)) = pMonomial p b em.1 :=
    prod_congr rfl fun i _ ↦ by rw [hf_inl]
  simp [h1]

private theorem isPIndependent_sumElim_unique_of_notMem_span {κ : Type*} [Unique κ] {b : ι → k}
    {x : k} (hb : IsPIndependent p b)
    (hxM : x ∉ Submodule.span (frobenius k p).fieldRange (Set.range (pMonomial p b))) :
    IsPIndependent p (Sum.elim b (fun _ : κ ↦ x)) := by
  set K₀ := (frobenius k p).fieldRange
  have hfun : (pMonomial p (Sum.elim b fun _ : κ ↦ x) ∘ ⇑(sumUniqueFinsuppEquiv p ι κ).symm) =
      fun em : (ι →₀ Fin p) × Fin p ↦ pMonomial p b em.1 * x ^ (em.2 : ℕ) :=
    funext (pMonomial_sumUniqueFinsuppEquiv_symm p b x)
  rw [isPIndependent_def, ← linearIndependent_equiv (sumUniqueFinsuppEquiv p ι κ).symm, hfun]
  let L : Subfield k := (IntermediateField.adjoin K₀ (Set.range b)).toSubfield
  have hK₀L : K₀ ≤ L := fun z hz ↦
    IntermediateField.algebraMap_mem (IntermediateField.adjoin K₀ (Set.range b)) ⟨z, hz⟩
  have hxL : x ∉ L := by
    rw [← SetLike.mem_coe, IntermediateField.coe_toSubfield,
      coe_intermediateField_adjoin_fieldRange_frobenius]
    exact hxM
  have hpow := linearIndependent_pow_of_fieldRange_frobenius_le hK₀L hxL
  rw [linearIndependent_iff']
  intro s g hg em₀ hem₀
  classical
  let S₁ : Finset (ι →₀ Fin p) := s.image Prod.fst
  have hsum : ∑ m : Fin p,
      (∑ e ∈ S₁, (if (e, m) ∈ s then g (e, m) else 0) • pMonomial p b e) * x ^ (m : ℕ) = 0 := by
    calc ∑ m : Fin p,
          (∑ e ∈ S₁, (if (e, m) ∈ s then g (e, m) else 0) • pMonomial p b e) * x ^ (m : ℕ)
        = ∑ em ∈ S₁ ×ˢ (univ : Finset (Fin p)),
            (if em ∈ s then g em else 0) • (pMonomial p b em.1 * x ^ (em.2 : ℕ)) := by
          rw [sum_product_right]
          refine sum_congr rfl fun m _ ↦ ?_
          rw [sum_mul]
          exact sum_congr rfl fun e _ ↦ smul_mul_assoc ..
      _ = ∑ em ∈ s, g em • (pMonomial p b em.1 * x ^ (em.2 : ℕ)) := by
          simp only [ite_smul, zero_smul, ← sum_filter]
          refine sum_congr ?_ fun _ _ ↦ rfl
          ext ⟨e, m⟩
          simp only [mem_filter, mem_product, mem_univ, and_true, S₁, mem_image,
            and_iff_right_iff_imp]
          exact fun h ↦ ⟨(e, m), h, rfl⟩
      _ = 0 := hg
  let coeffL : Fin p → L := fun m ↦
    ⟨∑ e ∈ S₁, (if (e, m) ∈ s then g (e, m) else 0) • pMonomial p b e, by
      rw [← SetLike.mem_coe, IntermediateField.coe_toSubfield,
        coe_intermediateField_adjoin_fieldRange_frobenius]
      exact Submodule.sum_mem _ fun e _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)⟩
  have hcoeff0 : coeffL em₀.2 = 0 :=
    Fintype.linearIndependent_iff.mp hpow coeffL
      (by simpa [coeffL, Subfield.smul_def] using hsum) em₀.2
  have hinner : ∑ e ∈ S₁,
      (if (e, em₀.2) ∈ s then g (e, em₀.2) else 0) • pMonomial p b e = 0 :=
    congrArg Subtype.val hcoeff0
  have := linearIndependent_iff'.mp hb S₁
    (fun e ↦ if (e, em₀.2) ∈ s then g (e, em₀.2) else 0) hinner em₀.1
    (mem_image_of_mem Prod.fst hem₀)
  simpa [hem₀] using this

/-- Adjoining a single element `x` (indexed by `[Unique κ]`) to `b` preserves `p`-independence if
and only if `b` is `p`-independent and `x` does not lie in the `k ^ p`-span of `pMonomial p b`. -/
theorem isPIndependent_sumElim_unique_iff {κ : Type*} [Unique κ] {b : ι → k} {x : k} :
    IsPIndependent p (Sum.elim b (fun _ : κ ↦ x)) ↔
      IsPIndependent p b ∧
        x ∉ Submodule.span (frobenius k p).fieldRange (Set.range (pMonomial p b)) := by
  set K₀ := (frobenius k p).fieldRange
  have hfun : (pMonomial p (Sum.elim b fun _ : κ ↦ x) ∘ ⇑(sumUniqueFinsuppEquiv p ι κ).symm) =
      fun em : (ι →₀ Fin p) × Fin p ↦ pMonomial p b em.1 * x ^ (em.2 : ℕ) :=
    funext (pMonomial_sumUniqueFinsuppEquiv_symm p b x)
  refine ⟨fun hbx ↦ ?_, fun ⟨hb, hxM⟩ ↦ isPIndependent_sumElim_unique_of_notMem_span hb hxM⟩
  have hb : IsPIndependent p b := by
    simpa [Function.comp_def] using hbx.comp Sum.inl Sum.inl_injective
  refine ⟨hb, fun hxM ↦ ?_⟩
  rw [isPIndependent_def, ← linearIndependent_equiv (sumUniqueFinsuppEquiv p ι κ).symm,
    hfun] at hbx
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hxM
  rcases hxM with ⟨c, hc⟩
  let m1 : Fin p := ⟨1, hp.out.one_lt⟩
  have hm1 : m1 ≠ 0 := Fin.ne_of_gt Nat.zero_lt_one
  let emb : (ι →₀ Fin p) ↪ (ι →₀ Fin p) × Fin p :=
    ⟨fun e ↦ (e, (0 : Fin p)), fun _ _ h ↦ (Prod.mk.inj h).1⟩
  let f : (ι →₀ Fin p) × Fin p →₀ K₀ := Finsupp.single (0, m1) 1 - c.embDomain emb
  have hcomb : Finsupp.linearCombination K₀
      (fun em : (ι →₀ Fin p) × Fin p ↦ pMonomial p b em.1 * x ^ (em.2 : ℕ)) f = 0 := by
    have hemb (e : ι →₀ Fin p) : emb e = (e, 0) := rfl
    have hcomp_emb :
        ((fun em : (ι →₀ Fin p) × Fin p ↦ pMonomial p b em.1 * x ^ (em.2 : ℕ)) ∘ emb) =
          pMonomial p b :=
      funext fun e ↦ by simp [hemb]
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_embDomain,
      hcomp_emb, Finsupp.linearCombination_apply, hc]
    simp [m1]
  have hf0 : f (0, m1) = 0 := by
    rw [linearIndependent_iff.mp hbx f hcomb]
    rfl
  have hf1 : f (0, m1) = 1 := by
    simp only [f, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same]
    rw [Finsupp.embDomain_of_notMem_range, sub_zero]
    rintro ⟨e, he⟩
    exact hm1 (Prod.mk.inj he).2.symm
  exact one_ne_zero (hf1.symm.trans hf0)

/-- Inserting `x ∉ s` into a subset `s : Set k` preserves `p`-independence if and only if `s` is
`p`-independent and `x` lies outside the `k ^ p`-span of `pMonomial p ((↑) : s → k)`. -/
theorem isPIndependent_insert_iff {s : Set k} {x : k} (hx : x ∉ s) :
    IsPIndependent p ((↑) : ↥(insert x s) → k) ↔
      IsPIndependent p ((↑) : s → k) ∧
        x ∉ Submodule.span (frobenius k p).fieldRange (Set.range (pMonomial p ((↑) : s → k))) := by
  classical
  rw [← isPIndependent_equiv (Equiv.Set.insert hx).symm]
  have hcomp : (((↑) : ↥(insert x s) → k) ∘ (Equiv.Set.insert hx).symm) =
      Sum.elim ((↑) : s → k) (fun _ : PUnit ↦ x) := by
    ext (y | ⟨⟩) <;> rfl
  rw [hcomp, isPIndependent_sumElim_unique_iff]

private theorem isPIndependent_subtype_iff_linearIndepOn (s : Set k) :
    IsPIndependent p ((↑) : s → k) ↔
      LinearIndepOn (frobenius k p).fieldRange (pMonomial p (id : k → k))
        {e : k →₀ Fin p | (e.support : Set k) ⊆ s} := by
  rw [isPIndependent_def, LinearIndepOn,
    ← linearIndependent_equiv (Finsupp.restrictSupportEquiv s (Fin p))]
  convert Iff.rfl using 2
  ext e
  simp only [Function.comp_apply, Finsupp.restrictSupportEquiv_apply, pMonomial]
  exact (Finsupp.prod_subtypeDomain_index fun x hx ↦ e.2 hx).symm

/-- The union of a chain of `p`-independent subsets of `k` is `p`-independent. -/
theorem isPIndependent_sUnion_of_isChain {c : Set (Set k)} (hc : IsChain (· ⊆ ·) c)
    (h : ∀ s ∈ c, IsPIndependent p ((↑) : s → k)) :
    IsPIndependent p ((↑) : ↥(⋃₀ c) → k) := by
  rcases c.eq_empty_or_nonempty with rfl | hne
  · rw [Set.sUnion_empty]
    exact isPIndependent_of_isEmpty p _
  · rw [isPIndependent_subtype_iff_linearIndepOn]
    have hdir : DirectedOn ((fun s : Set k ↦ {e : k →₀ Fin p | (e.support : Set k) ⊆ s}) ⁻¹'o
        (· ⊆ ·)) c := by
      intro s hs t ht
      rcases hc.directedOn s hs t ht with ⟨u, hu, hsu, htu⟩
      exact ⟨u, hu, fun _ he ↦ he.trans hsu, fun _ he ↦ he.trans htu⟩
    have hbi := linearIndepOn_biUnion_of_directed hdir fun s hs ↦
      (isPIndependent_subtype_iff_linearIndepOn s).mp (h s hs)
    refine hbi.mono fun e (he : (e.support : Set k) ⊆ ⋃₀ c) ↦ ?_
    have he' : (e.support : Set k) ⊆ ⋃ s ∈ c, s := by rwa [← Set.sUnion_eq_biUnion]
    rcases hc.directedOn.exists_mem_subset_of_finset_subset_biUnion hne he' with ⟨s, hs, hes⟩
    exact Set.mem_biUnion hs hes

end PrimeChar

end TauCeti
