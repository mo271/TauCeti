/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.Algebra.GroupWithZero.Irreducible
import TauCeti.RingTheory.Polynomial.Monic.Basic

/-!
# Rückert's descent along polynomial-like ring maps

This file develops the abstract descent principle of Bosch, Güntzer and Remmert, §5.2.5, which
transfers the noetherian, factorial and Jacobson properties from a ring `A` to a ring `B`
receiving an injective map `φ : A[X] →+* B` that behaves like the inclusion of polynomials into
restricted power series.

The hypotheses (`RingHom.IsRueckert`) concern a set `W` of monic polynomials, closed under
taking monic factors, such that

* for every `w ∈ W`, the map `φ` induces an isomorphism `A[X] ⧸ (w) ≃+* B ⧸ (φ w)`
  (`RingHom.IsRueckert.quotientEquiv`), and
* every nonzero `b : B` becomes a unit multiple of some `φ w` after a ring automorphism of `B`.

For a Tate algebra `A = K⟨X₁, …, Xₙ⟩` and `B = A⟨Y⟩`, the polynomials `W` are the
Weierstrass polynomials: the quotient comparison is Weierstrass division, and the automorphisms
are the changes of variables making a series distinguished, followed by Weierstrass preparation.

The quotient comparison descends every quotient of `B` by a nonzero ideal, after an automorphism,
to a quotient of some `A[X] ⧸ (w)`, which is finite over `A` because `w` is monic
(`RingHom.IsRueckert.exists_finite_quotient`). It also reflects units, associates, prime ideals,
primality, irreducibility, coprimality, and squarefreeness for members of `W`. Consequently:

* `RingHom.IsRueckert.isNoetherianRing`: if `A` is noetherian, so is `B`;
* `RingHom.IsRueckert.uniqueFactorizationMonoid`: if `A` is a unique factorisation domain and `B`
  is a domain, then `B` is a unique factorisation domain. Each `φ w` is a product of primes,
  because a monic factorisation of `w` in the factorial ring `A[X]` stays in `W`, and an
  irreducible `w ∈ W` generates a prime ideal whose quotient is identified with `B ⧸ (φ w)`;
* `RingHom.IsRueckert.isJacobsonRing`: if `A` is a Jacobson ring and the Jacobson radical of `B`
  is zero, then `B` is a Jacobson ring. Indeed every nonzero radical ideal of `B` is the
  intersection of the maximal ideals containing it (`RingHom.IsRueckert.jacobson_eq_self`): it
  contains some nonzero `b`, and `B ⧸ (b)` is isomorphic to the Jacobson ring `A[X] ⧸ (w)`. The
  condition on the Jacobson radical cannot be dropped: for a reduced ring `B` it is necessary
  (`RingHom.IsRueckert.isJacobsonRing_iff_jacobson_eq_bot`).

## Main definitions

* `RingHom.IsRueckert φ W`: the Rückert hypotheses for `φ : A[X] →+* B` and `W ⊆ A[X]`.
* `RingHom.IsRueckert.quotientEquiv`: the ring isomorphism `A[X] ⧸ (w) ≃+* B ⧸ (φ w)` induced by
  `φ`, for `w ∈ W`.

## Main results

* `RingHom.IsRueckert.isUnit_apply_iff`, `RingHom.IsRueckert.associated_apply_iff`,
  `RingHom.IsRueckert.isPrime_span_apply_iff`, `RingHom.IsRueckert.prime_apply_iff`,
  `RingHom.IsRueckert.irreducible_of_irreducible_apply`,
  `RingHom.IsRueckert.irreducible_apply_iff`, `RingHom.IsRueckert.isRelPrime_apply_iff`,
  `RingHom.IsRueckert.squarefree_apply_iff`: preservation and reflection of units, associates,
  prime principal ideals, primality, irreducibility, relative primality, and squarefreeness for
  members of `W`.
* `RingHom.IsRueckert.existsUnique_associated_of_dvd`,
  `RingHom.IsRueckert.existsUnique_associated_of_dvd_apply`,
  `RingHom.IsRueckert.exists_multiset_irreducible_prod_eq`,
  `RingHom.IsRueckert.existsUnique_multiset_irreducible_prod_eq`: associated divisors (in `A[X]`
  and in `B`) and factorisation of `w ∈ W` into irreducible members of `W`.
* `RingHom.IsRueckert.isNoetherianRing`: Rückert's noetherian descent.
* `RingHom.IsRueckert.uniqueFactorizationMonoid`: Rückert's factorial descent.
* `RingHom.IsRueckert.isJacobsonRing`: Rückert's Jacobson descent.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.2.5.
-/

public section

open Polynomial

namespace RingHom

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **The Rückert hypotheses** for an injective ring map `φ : A[X] →+* B` and a set `W` of monic
polynomials closed under taking monic factors: for each `w ∈ W`, the map `φ` induces an
isomorphism `A[X] ⧸ (w) ≃+* B ⧸ (φ w)` (the divisibility and remainder conditions below), and
every nonzero element of `B` is mapped by some ring automorphism of `B` to a unit multiple of
`φ w` for some `w ∈ W`. -/
structure IsRueckert (φ : A[X] →+* B) (W : Set A[X]) : Prop where
  /-- The map `φ` is injective. -/
  injective : Function.Injective φ
  /-- Every member of `W` is monic. -/
  monic {w : A[X]} (hw : w ∈ W) : w.Monic
  /-- Monic factors of members of `W` belong to `W`. -/
  mem_of_dvd {w p : A[X]} (hw : w ∈ W) (hp : p.Monic) (hpw : p ∣ w) : p ∈ W
  /-- Divisibility by `w ∈ W` is detected after applying `φ`: the induced map
  `A[X] ⧸ (w) → B ⧸ (φ w)` is injective. -/
  dvd_iff {w : A[X]} (hw : w ∈ W) (p : A[X]) : φ w ∣ φ p ↔ w ∣ p
  /-- Every element of `B` is congruent to an element of the image of `φ` modulo `φ w` for
  `w ∈ W`: the induced map `A[X] ⧸ (w) → B ⧸ (φ w)` is surjective. -/
  exists_dvd_sub {w : A[X]} (hw : w ∈ W) (b : B) : ∃ p : A[X], φ w ∣ b - φ p
  /-- Every nonzero element of `B` is, after a ring automorphism, a unit multiple of `φ w` for
  some `w ∈ W`. -/
  exists_mul_eq {b : B} (hb : b ≠ 0) : ∃ (α : B ≃+* B) (u : Bˣ), ∃ w ∈ W, u * α b = φ w

namespace IsRueckert

variable {φ : A[X] →+* B} {W : Set A[X]} (h : φ.IsRueckert W)
include h

private theorem ker_comp_mk {w : A[X]} (hw : w ∈ W) :
    ker ((Ideal.Quotient.mk (Ideal.span {φ w})).comp φ) = Ideal.span {w} := by
  ext p
  simp [mem_ker, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, h.dvd_iff hw]

private theorem surjective_comp_mk {w : A[X]} (hw : w ∈ W) :
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {φ w})).comp φ) := by
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨p, hp⟩ := h.exists_dvd_sub hw b
  exact ⟨p, (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr hp)).symm⟩

/-- For `w ∈ W`, the map `φ` induces a ring isomorphism `A[X] ⧸ (w) ≃+* B ⧸ (φ w)`. -/
noncomputable def quotientEquiv {w : A[X]} (hw : w ∈ W) :
    A[X] ⧸ Ideal.span {w} ≃+* B ⧸ Ideal.span {φ w} :=
  (Ideal.quotEquivOfEq (h.ker_comp_mk hw).symm).trans
    (quotientKerEquivOfSurjective (h.surjective_comp_mk hw))

/-- The quotient comparison sends the class of a polynomial to the class of its image. -/
@[simp]
theorem quotientEquiv_mk {w : A[X]} (hw : w ∈ W) (p : A[X]) :
    h.quotientEquiv hw (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (φ p) :=
  (rfl)

/-- The quotient of `B` by a nonzero principal ideal is isomorphic to `A[X] ⧸ (w)` for some
`w ∈ W`. -/
theorem exists_nonempty_ringEquiv_quotient_span_singleton {b : B} (hb : b ≠ 0) :
    ∃ w ∈ W, Nonempty (A[X] ⧸ Ideal.span {w} ≃+* B ⧸ Ideal.span {b}) := by
  obtain ⟨α, u, w, hw, hu⟩ := h.exists_mul_eq hb
  have hspan : Ideal.span {φ w} = (Ideal.span {b}).map (α : B →+* B) := by
    rw [Ideal.map_span, Set.image_singleton, ← hu, Ideal.span_singleton_mul_left_unit u.isUnit,
      RingEquiv.coe_toRingHom]
  exact ⟨w, hw, ⟨(h.quotientEquiv hw).trans (Ideal.quotientEquiv _ _ α hspan).symm⟩⟩

/-- **Finite-quotient descent.** For every nonzero ideal `I` of `B` there is a ring automorphism
`α` of `B` such that `B ⧸ α(I)` is finite over `A`, through `A → A[X] → B`. -/
theorem exists_finite_quotient {I : Ideal B} (hI : I ≠ ⊥) :
    ∃ α : B ≃+* B, ((Ideal.Quotient.mk (I.map α)).comp (φ.comp C)).Finite := by
  obtain ⟨b, hbI, hb⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨α, u, w, hw, hu⟩ := h.exists_mul_eq hb
  have hle : Ideal.span {φ w} ≤ I.map α := by
    rw [Ideal.span_singleton_le_iff_mem, ← hu]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem α hbI)
  have hfin : (algebraMap A (A[X] ⧸ Ideal.span {w})).Finite :=
    finite_algebraMap.mpr (h.monic hw).finite_quotient
  refine ⟨α, ?_⟩
  have he := Finite.of_surjective (h.quotientEquiv hw).toRingHom (h.quotientEquiv hw).surjective
  convert ((Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)).comp he).comp hfin
    using 1
  ext a
  simp [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_eq]

/-- **Rückert's noetherian descent.** If `A` is noetherian, so is `B`. -/
theorem isNoetherianRing [IsNoetherianRing A] : IsNoetherianRing B := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  rcases eq_or_ne I ⊥ with rfl | hI
  · exact Submodule.fg_bot
  obtain ⟨b, hbI, hb⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨w, -, ⟨e⟩⟩ := h.exists_nonempty_ringEquiv_quotient_span_singleton hb
  have : IsNoetherianRing (B ⧸ Ideal.span {b}) := isNoetherianRing_of_ringEquiv _ e
  refine Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective
    ((isNoetherianRing_iff_ideal_fg _).mp this _) ?_ Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hbI)]
  exact Submodule.fg_span_singleton b

/-- A member `w ∈ W` maps to a unit in `B` if and only if `w` is a unit in `A[X]` (i.e. `w = 1`). -/
theorem isUnit_apply_iff {w : A[X]} (hw : w ∈ W) : IsUnit (φ w) ↔ IsUnit w :=
  ⟨fun hu ↦ isUnit_of_dvd_one ((h.dvd_iff hw 1).mp (by simpa only [map_one] using hu.dvd)),
    fun hu ↦ hu.map φ⟩

/-- Two members of `W` have associated images in `B` if and only if they are equal. -/
theorem associated_apply_iff {w₁ w₂ : A[X]} (hw₁ : w₁ ∈ W) (hw₂ : w₂ ∈ W) :
    Associated (φ w₁) (φ w₂) ↔ w₁ = w₂ := by
  refine ⟨fun h12 ↦ ?_, by rintro rfl; exact Associated.refl _⟩
  rcases subsingleton_or_nontrivial A with _ | _
  · exact Subsingleton.elim w₁ w₂
  have h1 : w₁ ∣ w₂ := (h.dvd_iff hw₁ w₂).mp h12.dvd
  obtain ⟨r, hr⟩ := (h.dvd_iff hw₂ w₁).mp h12.symm.dvd
  have hr0 : r ≠ 0 := by rintro rfl; exact (h.monic hw₁).ne_zero (by simp [hr])
  have hdeg₂ : w₂.natDegree ≤ w₁.natDegree := by
    rw [hr, (h.monic hw₂).natDegree_mul' hr0]; exact Nat.le_add_right _ _
  exact (eq_of_monic_of_dvd_of_natDegree_le (h.monic hw₁) (h.monic hw₂) h1 hdeg₂).symm

/-- For `w ∈ W`, the principal ideal `(φ w)` in `B` is prime if and only if `(w)` in `A[X]` is
prime. -/
theorem isPrime_span_apply_iff {w : A[X]} (hw : w ∈ W) :
    (Ideal.span {φ w}).IsPrime ↔ (Ideal.span {w}).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime, ← Ideal.Quotient.isDomain_iff_prime]
  exact ⟨fun _ ↦ (h.quotientEquiv hw).toMulEquiv.isDomain _,
    fun _ ↦ (h.quotientEquiv hw).symm.toMulEquiv.isDomain _⟩

/-- For `w ∈ W`, the image `φ w` is prime in `B` if and only if `w` is prime in `A[X]`. -/
theorem prime_apply_iff {w : A[X]} (hw : w ∈ W) : Prime (φ w) ↔ Prime w := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp [not_prime_zero]
  have hφw0 : φ w ≠ 0 := (map_ne_zero_iff φ h.injective).mpr hw0
  rw [← Ideal.span_singleton_prime hφw0, ← Ideal.span_singleton_prime hw0]
  exact h.isPrime_span_apply_iff hw

/-- The image of a prime member of `W` is prime. -/
theorem prime_apply {w : A[X]} (hw : w ∈ W) (hp : Prime w) : Prime (φ w) :=
  (h.prime_apply_iff hw).mpr hp

/-- Over a ring without zero divisors, if the image `φ w` of `w ∈ W` is irreducible in `B`, then
`w` is irreducible in `A[X]`. -/
theorem irreducible_of_irreducible_apply [NoZeroDivisors A] {w : A[X]} (hw : w ∈ W)
    (hirr : Irreducible (φ w)) : Irreducible w :=
  hirr.of_map_of_dvd fun p ↦ (h.dvd_iff hw p).mp

/-- Over rings without zero divisors where `A[X]` is factorial, `φ w` is irreducible in `B` if and
only if `w` is irreducible in `A[X]`, for every `w ∈ W`. -/
theorem irreducible_apply_iff [NoZeroDivisors A] [UniqueFactorizationMonoid A[X]]
    [NoZeroDivisors B] {w : A[X]} (hw : w ∈ W) : Irreducible (φ w) ↔ Irreducible w :=
  ⟨h.irreducible_of_irreducible_apply hw, fun hirr ↦
    (h.prime_apply hw (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)).irreducible⟩

/-- Over a ring without zero divisors, every divisor of `w ∈ W` is associated to a unique member
of `W`. -/
theorem existsUnique_associated_of_dvd [NoZeroDivisors A] {w d : A[X]} (hw : w ∈ W) (hd : d ∣ w) :
    ∃! p : A[X], p ∈ W ∧ Associated d p := by
  obtain ⟨p, ⟨hpmon, hassoc⟩, huniq⟩ := (h.monic hw).existsUnique_associated_of_dvd hd
  refine ⟨p, ⟨h.mem_of_dvd hw hpmon (hassoc.symm.dvd.trans hd), hassoc⟩, ?_⟩
  rintro p' ⟨hp', hp'assoc⟩
  exact huniq p' ⟨h.monic hp', hp'assoc⟩

/-- Over a ring without zero divisors, every member of `W` factors as a multiset product of
irreducible members of `W`. -/
theorem exists_multiset_irreducible_prod_eq [NoZeroDivisors A] {w : A[X]} (hw : w ∈ W) :
    ∃ s : Multiset A[X], (∀ p ∈ s, p ∈ W ∧ Irreducible p) ∧ s.prod = w := by
  obtain ⟨s, hs, rfl⟩ := (h.monic hw).exists_multiset_irreducible_prod_eq
  exact ⟨s, fun p hp ↦ ⟨h.mem_of_dvd hw (hs p hp).1 (Multiset.dvd_prod hp), (hs p hp).2⟩, rfl⟩

/-- Over a ring without zero divisors whose polynomial ring is a unique factorisation monoid,
every member of `W` factors uniquely as a multiset product of irreducible members of `W`. -/
theorem existsUnique_multiset_irreducible_prod_eq [NoZeroDivisors A]
    [UniqueFactorizationMonoid A[X]] {w : A[X]} (hw : w ∈ W) :
    ∃! s : Multiset A[X], (∀ p ∈ s, p ∈ W ∧ Irreducible p) ∧ s.prod = w := by
  obtain ⟨s, ⟨hs, hsprod⟩, huniq⟩ := (h.monic hw).existsUnique_multiset_irreducible_prod_eq
  refine ⟨s, ⟨fun p hp ↦ ⟨h.mem_of_dvd hw (hs p hp).1 (hsprod ▸ Multiset.dvd_prod hp),
    (hs p hp).2⟩, hsprod⟩, ?_⟩
  rintro t ⟨ht, htprod⟩
  exact huniq t ⟨fun p hp ↦ ⟨h.monic (ht p hp).1, (ht p hp).2⟩, htprod⟩

/-- Over a unique factorisation domain `A`, the image of every member of `W` is associated to a
product of primes. -/
theorem exists_prime_factors_apply [IsDomain A] [UniqueFactorizationMonoid A] {w : A[X]}
    (hw : w ∈ W) : ∃ f : Multiset B, (∀ b ∈ f, Prime b) ∧ Associated f.prod (φ w) := by
  obtain ⟨s, hs, rfl⟩ := h.exists_multiset_irreducible_prod_eq hw
  refine ⟨s.map φ, fun b hb ↦ ?_, by rw [← map_multiset_prod]⟩
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hb
  exact h.prime_apply (hs p hp).1 (UniqueFactorizationMonoid.irreducible_iff_prime.mp (hs p hp).2)

/-- **Rückert's factorial descent.** If `A` is a unique factorisation domain and `B` is a domain,
then `B` is a unique factorisation domain. -/
theorem uniqueFactorizationMonoid [IsDomain A] [UniqueFactorizationMonoid A] [IsDomain B] :
    UniqueFactorizationMonoid B := by
  refine UniqueFactorizationMonoid.of_exists_prime_factors fun b hb ↦ ?_
  obtain ⟨α, u, w, hw, hu⟩ := h.exists_mul_eq hb
  obtain ⟨f, hf, hfw⟩ := h.exists_prime_factors_apply hw
  refine ⟨f.map α.symm, fun c hc ↦ ?_, ?_⟩
  · obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hc
    exact (MulEquiv.prime_iff α.symm.toMulEquiv).mpr (hf d hd)
  · rw [← map_multiset_prod]
    refine (hfw.map α.symm).trans ?_
    rw [← hu, map_mul, RingEquiv.symm_apply_apply]
    exact associated_unit_mul_left b _ (u.isUnit.map α.symm)

omit h in
/-- Any divisor of a multiset product of prime elements is associated to the product of a
submultiset. -/
private theorem exists_le_associated_map_prod_of_dvd {ι : Type*} [NoZeroDivisors B]
    (f : ι → B) (s : Multiset ι) (hs : ∀ i ∈ s, Prime (f i)) {g : B}
    (hg : g ∣ (s.map f).prod) : ∃ t ≤ s, Associated (t.map f).prod g := by
  induction s using Multiset.induction_on generalizing g with
  | empty =>
    refine ⟨0, le_rfl, ?_⟩
    simpa only [Multiset.map_zero, Multiset.prod_zero] using
      (associated_one_iff_isUnit.mpr (isUnit_of_dvd_one (by simpa using hg))).symm
  | @cons a s ih =>
    have ha : Prime (f a) := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ i ∈ s, Prime (f i) := fun i hi ↦ hs i (Multiset.mem_cons_of_mem hi)
    rw [Multiset.map_cons, Multiset.prod_cons] at hg
    by_cases hag : f a ∣ g
    · obtain ⟨g', rfl⟩ := hag
      have hg' : g' ∣ (s.map f).prod := (mul_dvd_mul_iff_left ha.ne_zero).mp hg
      obtain ⟨t, hts, ht⟩ := ih hs' hg'
      refine ⟨a ::ₘ t, Multiset.cons_le_cons a hts, ?_⟩
      simpa only [Multiset.map_cons, Multiset.prod_cons] using (Associated.refl (f a)).mul_mul ht
    · obtain ⟨k, hk⟩ := hg
      have hak : f a ∣ k := (ha.dvd_or_dvd ⟨(s.map f).prod, hk.symm⟩).resolve_left hag
      obtain ⟨k', rfl⟩ := hak
      have hgk' : (s.map f).prod = g * k' := mul_left_cancel₀ ha.ne_zero (by rw [hk, mul_left_comm])
      obtain ⟨t, hts, ht⟩ := ih hs' ⟨k', hgk'⟩
      exact ⟨t, hts.trans (Multiset.le_cons_self s a), ht⟩

/-- Over rings without zero divisors where `A[X]` is factorial, every divisor `g ∣ φ w` in `B` of
the image of `w ∈ W` is associated to `φ q` for a unique `q ∈ W`, which divides `w` in `A[X]`. -/
theorem existsUnique_associated_of_dvd_apply [NoZeroDivisors A] [UniqueFactorizationMonoid A[X]]
    [NoZeroDivisors B] {w : A[X]} (hw : w ∈ W) {g : B} (hg : g ∣ φ w) :
    ∃! q : A[X], q ∈ W ∧ q ∣ w ∧ Associated (φ q) g := by
  obtain ⟨s, hs, rfl⟩ := h.exists_multiset_irreducible_prod_eq hw
  have hprime : ∀ p ∈ s, Prime (φ p) := fun p hp ↦
    h.prime_apply (hs p hp).1 (UniqueFactorizationMonoid.irreducible_iff_prime.mp (hs p hp).2)
  obtain ⟨t, hts, ht⟩ :=
    exists_le_associated_map_prod_of_dvd φ s hprime (map_multiset_prod φ s ▸ hg)
  have ht_mon : t.prod.Monic :=
    Multiset.prod_induction (·.Monic) t (fun _ _ ↦ Monic.mul) monic_one fun p hp ↦
      h.monic (hs p (Multiset.subset_of_le hts hp)).1
  have ht_dvd : t.prod ∣ s.prod := Multiset.prod_dvd_prod_of_le hts
  have htW : t.prod ∈ W := h.mem_of_dvd hw ht_mon ht_dvd
  have htassoc : Associated (φ t.prod) g := by rwa [map_multiset_prod]
  refine ⟨t.prod, ⟨htW, ht_dvd, htassoc⟩, ?_⟩
  rintro q' ⟨hq'W, -, hq'⟩
  exact (h.associated_apply_iff hq'W htW).mp (hq'.trans htassoc.symm)

/-- Over rings without zero divisors where `A[X]` is factorial, a member `w ∈ W` and an arbitrary
polynomial `p : A[X]` are relatively prime in `A[X]` if and only if their images `φ w, φ p` are
relatively prime in `B`. -/
theorem isRelPrime_apply_iff [NoZeroDivisors A] [UniqueFactorizationMonoid A[X]]
    [NoZeroDivisors B] {w : A[X]} (hw : w ∈ W) (p : A[X]) :
    IsRelPrime (φ w) (φ p) ↔ IsRelPrime w p := by
  refine ⟨fun hrel d hdw hdp ↦ ?_, fun hrel g hgw hgp ↦ ?_⟩
  · obtain ⟨q, ⟨hqW, hassoc⟩, -⟩ := h.existsUnique_associated_of_dvd hw hdw
    have hu : IsUnit (φ q) := hrel (map_dvd φ (hassoc.symm.dvd.trans hdw))
      (map_dvd φ (hassoc.symm.dvd.trans hdp))
    exact hassoc.isUnit_iff.mpr ((h.isUnit_apply_iff hqW).mp hu)
  · obtain ⟨q, ⟨hqW, hqw, hassoc⟩, -⟩ := h.existsUnique_associated_of_dvd_apply hw hgw
    have hqp : q ∣ p := (h.dvd_iff hqW p).mp (hassoc.dvd.trans hgp)
    exact hassoc.isUnit_iff.mp ((hrel hqw hqp).map φ)

/-- Over rings without zero divisors where `A[X]` is factorial, a member `w ∈ W` is squarefree in
`A[X]` if and only if its image `φ w` is squarefree in `B`. -/
theorem squarefree_apply_iff [NoZeroDivisors A] [UniqueFactorizationMonoid A[X]]
    [NoZeroDivisors B] {w : A[X]} (hw : w ∈ W) : Squarefree (φ w) ↔ Squarefree w := by
  refine ⟨fun hsq d hd ↦ ?_, fun hsq g hg ↦ ?_⟩
  · obtain ⟨p, ⟨hpW, hassoc⟩, -⟩ :=
      h.existsUnique_associated_of_dvd hw ((dvd_mul_right d d).trans hd)
    have hp2 : p * p ∣ w := (hassoc.symm.mul_mul hassoc.symm).dvd.trans hd
    exact hassoc.isUnit_iff.mpr ((h.isUnit_apply_iff hpW).mp
      (hsq (φ p) (by simpa only [map_mul] using map_dvd φ hp2)))
  · rcases subsingleton_or_nontrivial A with _ | _
    · have : Subsingleton B := subsingleton_of_zero_eq_one
        (by rw [← map_zero φ, ← map_one φ, Subsingleton.elim (0 : A[X]) 1])
      exact isUnit_of_subsingleton g
    obtain ⟨q, ⟨hqW, ⟨w', hw'⟩, hassoc⟩, -⟩ :=
      h.existsUnique_associated_of_dvd_apply hw ((dvd_mul_right g g).trans hg)
    have hqq : φ q * φ q ∣ φ q * φ w' := by
      rw [← map_mul φ q w', ← hw']
      exact (hassoc.mul_mul hassoc).dvd.trans hg
    have hφq0 : φ q ≠ 0 := (map_ne_zero_iff φ h.injective).mpr (h.monic hqW).ne_zero
    have hqw' : q ∣ w' := (h.dvd_iff hqW w').mp ((mul_dvd_mul_iff_left hφq0).mp hqq)
    exact hassoc.isUnit_iff.mp ((hsq q (by rw [hw']; exact mul_dvd_mul_left q hqw')).map φ)

/-- Over a Jacobson ring `A`, every nonzero radical ideal of `B` is the intersection of the
maximal ideals containing it. -/
theorem jacobson_eq_self [IsJacobsonRing A] {P : Ideal B} (hP : P.IsRadical) (hP0 : P ≠ ⊥) :
    P.jacobson = P := by
  obtain ⟨b, hbP, hb⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨w, -, ⟨e⟩⟩ := h.exists_nonempty_ringEquiv_quotient_span_singleton hb
  have : IsJacobsonRing (B ⧸ Ideal.span {b}) :=
    isJacobsonRing_of_surjective ⟨e.toRingHom, e.surjective⟩
  have hle : Ideal.span {b} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr hbP
  have : IsJacobsonRing (B ⧸ P) :=
    isJacobsonRing_of_surjective ⟨_, Ideal.Quotient.factor_surjective hle⟩
  have : IsReduced (B ⧸ P) := (Ideal.isRadical_iff_quotient_reduced P).mp hP
  rw [Ideal.jacobson_eq_iff_jacobson_quotient_eq_bot, ← Ideal.jacobson_bot]
  exact IsJacobsonRing.out' ⊥ Ideal.isRadical_bot

/-- **Rückert's Jacobson descent.** If `A` is a Jacobson ring and the Jacobson radical of `B` is
zero, then `B` is a Jacobson ring. -/
theorem isJacobsonRing [IsJacobsonRing A] (hB : Ring.jacobson B = ⊥) : IsJacobsonRing B := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  rcases eq_or_ne P ⊥ with rfl | hP0
  · rw [Ideal.jacobson_bot, hB]
  · exact h.jacobson_eq_self hP.isRadical hP0

/-- For a reduced ring `B` over a Jacobson ring `A`, the ring `B` is Jacobson exactly when its
Jacobson radical is zero. -/
theorem isJacobsonRing_iff_jacobson_eq_bot [IsJacobsonRing A] [IsReduced B] :
    IsJacobsonRing B ↔ Ring.jacobson B = ⊥ :=
  ⟨fun _ ↦ by rw [← Ideal.jacobson_bot]; exact IsJacobsonRing.out' ⊥ Ideal.isRadical_bot,
    h.isJacobsonRing⟩

end IsRueckert

end RingHom
