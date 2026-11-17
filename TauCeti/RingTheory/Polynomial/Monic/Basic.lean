/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Factorization and associated monic divisors of monic polynomials

Over a commutative semiring without zero divisors, every divisor of a monic polynomial has unit
leading coefficient and is therefore associated to a unique monic polynomial. By strong induction
on degree via `Polynomial.Monic.irreducible_iff_natDegree`, every monic polynomial factors as a
multiset product of monic irreducible polynomials. When the polynomial ring is additionally a
unique factorization monoid, that multiset is unique.

Unlike `TauCeti.RingTheory.Polynomial.Monic.Factorization`, these results require neither
`NormalizationMonoid`, nor squarefreeness, nor the discriminant.

## Main results

* `Polynomial.Monic.existsUnique_associated_of_dvd`: every divisor of a monic polynomial is
  associated to a unique monic polynomial.
* `Polynomial.Monic.exists_multiset_irreducible_prod_eq`: every monic polynomial factors as a
  multiset product of monic irreducible polynomials.
* `Polynomial.Monic.existsUnique_multiset_irreducible_prod_eq`: when `R[X]` is a unique
  factorization monoid, that multiset factorization is unique.
-/

public section

namespace Polynomial.Monic

variable {R : Type*} [CommSemiring R] [NoZeroDivisors R] {f : R[X]}

/-- Over a commutative semiring without zero divisors, every divisor of a monic polynomial is
associated to a unique monic polynomial. -/
theorem existsUnique_associated_of_dvd {d : R[X]} (hf : f.Monic) (hd : d ∣ f) :
    ∃! g : R[X], g.Monic ∧ Associated d g := by
  have hu : IsUnit d.leadingCoeff :=
    isUnit_of_dvd_one (by simpa only [hf.leadingCoeff] using leadingCoeff_dvd_leadingCoeff hd)
  let g : R[X] := hu.unit⁻¹ • d
  have hg : g.Monic := monic_of_isUnit_leadingCoeff_inv_smul hu
  have hassoc : Associated d g := by
    refine ⟨(isUnit_C.mpr hu.unit⁻¹.isUnit).unit, ?_⟩
    simp [g, Units.smul_def, smul_eq_C_mul, mul_comm]
  refine ⟨g, ⟨hg, hassoc⟩, ?_⟩
  rintro g' ⟨hg', hg'assoc⟩
  exact eq_of_monic_of_associated hg' hg (hg'assoc.symm.trans hassoc)

/-- Over a commutative semiring without zero divisors, every monic polynomial factors as a multiset
product of monic irreducible polynomials. -/
theorem exists_multiset_irreducible_prod_eq (hf : f.Monic) :
    ∃ s : Multiset R[X], (∀ g ∈ s, g.Monic ∧ Irreducible g) ∧ s.prod = f := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  by_cases hirr : Irreducible f
  · exact ⟨{f}, by simpa using ⟨hf, hirr⟩, by simp⟩
  rcases eq_or_ne f 1 with rfl | hf1
  · exact ⟨0, by simp, by simp⟩
  obtain ⟨a, b, ha, hb, rfl, ha0, hb0⟩ : ∃ a b : R[X], a.Monic ∧ b.Monic ∧ a * b = f ∧
      a.natDegree ≠ 0 ∧ b.natDegree ≠ 0 := by
    simpa [hf.irreducible_iff_natDegree, hf1, not_or] using hirr
  have hdeg := ha.natDegree_mul hb
  obtain ⟨sa, hsa, hsap⟩ := ih a.natDegree (by omega) ha rfl
  obtain ⟨sb, hsb, hsbp⟩ := ih b.natDegree (by omega) hb rfl
  exact ⟨sa + sb, fun q hq ↦ (Multiset.mem_add.mp hq).elim (hsa q) (hsb q),
    by rw [Multiset.prod_add, hsap, hsbp]⟩

/-- Over a commutative semiring without zero divisors whose polynomial ring is a unique
factorization monoid, every monic polynomial factors uniquely as a multiset product of monic
irreducible polynomials. -/
theorem existsUnique_multiset_irreducible_prod_eq [UniqueFactorizationMonoid R[X]] (hf : f.Monic) :
    ∃! s : Multiset R[X], (∀ g ∈ s, g.Monic ∧ Irreducible g) ∧ s.prod = f := by
  obtain ⟨s, hs, hsprod⟩ := hf.exists_multiset_irreducible_prod_eq
  refine ⟨s, ⟨hs, hsprod⟩, ?_⟩
  rintro t ⟨ht, htprod⟩
  have hrel : Multiset.Rel Associated t s :=
    UniqueFactorizationMonoid.factors_unique (fun q hq ↦ (ht q hq).2) (fun q hq ↦ (hs q hq).2)
      (by rw [htprod, hsprod]; exact Associated.refl f)
  clear hsprod htprod hf
  induction hrel with
  | zero => rfl
  | @cons a b l₁ l₂ hab _ ih =>
    have ha := (ht a (Multiset.mem_cons_self a l₁)).1
    have hb := (hs b (Multiset.mem_cons_self b l₂)).1
    rw [eq_of_monic_of_associated ha hb hab,
      ih (fun q hq ↦ hs q (Multiset.mem_cons_of_mem hq))
        (fun q hq ↦ ht q (Multiset.mem_cons_of_mem hq))]

end Polynomial.Monic
