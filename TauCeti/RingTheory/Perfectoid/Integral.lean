/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Principal
public import TauCeti.RingTheory.Ideal.Quotient.Frobenius
public import TauCeti.RingTheory.Perfect.Basic
public import TauCeti.RingTheory.Perfectoid.FontaineTheta

/-!
# Integral perfectoid rings

Fix a prime `p`. A commutative ring `A` is *integral perfectoid* (Bhatt–Morrow–Scholze,
*Integral p-adic Hodge theory*, Definition 3.5) if

* some `π ∈ A` with `π ^ p ∣ p` makes `A` `π`-adically complete and separated;
* Frobenius `A ⧸ p → A ⧸ p`, `x ↦ x ^ p`, is surjective; and
* the kernel of Fontaine's map `θ : W(A♭) → A` is principal, where `A♭ = lim_{x ↦ x ^ p} A ⧸ p`
  is the tilt (Mathlib's `PreTilt` and `WittVector.fontaineTheta`).

This is the integral counterpart of a perfectoid Tate ring: no topology is given, and the
definition does not depend on a choice of `π`. Integral perfectoid rings may have `p`-torsion and
need not be domains. Perfect rings of characteristic `p` are examples, with `π = 0`
(`of_perfectRing`).

Mathlib's `PreTilt` and `fontaineTheta` need `p` to be a nonunit, as an instance argument. The
completeness clause makes `A` `p`-adically complete, since `π ∣ p`, and then `p` lies in the
Jacobson radical; so `p` is a nonunit unless `A` is the zero ring. The kernel clause is therefore
stated for every proof that `p` is a nonunit, which makes it vacuous for the zero ring, where the
unique map to `A` has principal kernel anyway.

## Main definitions

* `TauCeti.Perfectoid.IsIntegralPerfectoid p A`: `A` is an integral perfectoid ring.

## Main results

* `TauCeti.Perfectoid.IsIntegralPerfectoid.isAdicComplete_span_natCast`: an integral perfectoid
  ring is `p`-adically complete and separated.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.not_isUnit_natCast`: in a nonzero integral perfectoid
  ring, `p` is not a unit.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.isPrincipal_ker_fontaineTheta`: the kernel of
  Mathlib's Fontaine map is principal.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.surjective_fontaineTheta`: Fontaine's map
  `θ : W(A♭) → A` is surjective.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.exists_natCast_dvd_sub_pow`: every element is a
  `p`-th power modulo `p`.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.frobeniusModPow_surjective`,
  `TauCeti.Perfectoid.IsIntegralPerfectoid.frobeniusModPow_injective`,
  `TauCeti.Perfectoid.IsIntegralPerfectoid.frobeniusModPow_bijective`: relative Frobenius
  `A ⧸ π → A ⧸ π ^ p` is surjective for every `π` with `π ^ p ∣ p`, and bijective when `A` is
  `π`-adically complete (Bhatt–Morrow–Scholze, Lemma 3.10(i)).
* `TauCeti.Perfectoid.IsIntegralPerfectoid.exists_associated_untilt`: for every `π` with
  `π ^ p ∣ p` and `[IsAdicComplete (span {π}) A]`, `π` is associated to `ϖ.untilt` for some
  `ϖ : PreTilt A p` with `π * p ∣ π - ϖ.untilt` (Bhatt–Morrow–Scholze, Lemma 3.9).
* `TauCeti.Perfectoid.IsIntegralPerfectoid.of_bijective_frobeniusModPow`: if `A` is `π`-adically
  complete for a nonzerodivisor `π` with `π ^ p ∣ p` and bijective relative Frobenius
  `A ⧸ (π) → A ⧸ (π ^ p)`, then `A` is integral perfectoid (Bhatt–Morrow–Scholze, Lemma 3.10(ii)).
* `TauCeti.Perfectoid.IsIntegralPerfectoid.of_perfectRing`: a perfect ring of characteristic `p`
  is integral perfectoid; the kernel of `θ` is `(p)` (`WittVector.ker_fontaineTheta_eq_span_p`).
* `TauCeti.Perfectoid.IsIntegralPerfectoid.of_subsingleton`: so is the zero ring.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, §3.2, Definition 3.5 and
  Lemmas 3.9–3.10.
-/

public section

open Ideal
open scoped nonZeroDivisors

namespace TauCeti.Perfectoid

variable (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]

/-- A commutative ring `A` is *integral perfectoid* if some `π` with `π ^ p ∣ p` makes `A`
`π`-adically complete and separated, Frobenius on `A ⧸ p` is surjective, and the kernel of
Fontaine's map `θ : W(A♭) → A` is principal (Bhatt–Morrow–Scholze, *Integral p-adic Hodge theory*,
Definition 3.5). Mathlib's `θ` is only defined when `p` is a nonunit and `A` is `p`-adically
complete, so the kernel condition is stated for every proof of these two facts; the second
always follows from the first clause (`isAdicComplete_span_natCast`), and the first fails only for
the zero ring (`not_isUnit_natCast`). -/
class IsIntegralPerfectoid : Prop where
  /-- Some `π` with `π ^ p ∣ p` makes `A` `π`-adically complete and separated. -/
  exists_adic_element : ∃ π : A, π ^ p ∣ (p : A) ∧ IsAdicComplete (span {π}) A
  /-- Frobenius on `A ⧸ p` is surjective. -/
  frobenius_surjective : Function.Surjective fun x : ModP A p ↦ x ^ p
  /-- The kernel of Fontaine's map `θ : W(A♭) → A` is principal. -/
  theta_kernel_principal : ∀ (hp : ¬IsUnit (p : A)) (hc : IsAdicComplete (span {(p : A)}) A),
    letI : Fact (¬IsUnit (p : A)) := ⟨hp⟩
    letI := hc
    (RingHom.ker (WittVector.fontaineTheta A p)).IsPrincipal

namespace IsIntegralPerfectoid

section Basic

variable {p A} [IsIntegralPerfectoid p A]

/-- An integral perfectoid ring is `p`-adically complete and separated: it is complete for some
`π` with `π ^ p ∣ p`, and `π ∣ p`. -/
instance isAdicComplete_span_natCast : IsAdicComplete (span {(p : A)}) A := by
  obtain ⟨π, hπ, hc⟩ := exists_adic_element (p := p) (A := A)
  exact .span_singleton_of_dvd ((dvd_pow_self π (Fact.out : p.Prime).ne_zero).trans hπ)

/-- In a nonzero integral perfectoid ring, `p` is not a unit: by completeness, `p` lies in the
Jacobson radical. This supplies the standing hypothesis of Mathlib's `PreTilt` and
`WittVector.fontaineTheta`. -/
theorem not_isUnit_natCast [Nontrivial A] : ¬IsUnit (p : A) :=
  IsAdicComplete.not_isUnit_of_mem (mem_span_singleton_self (p : A))

/-- The kernel of Fontaine's map `θ : W(A♭) → A` of an integral perfectoid ring is principal. -/
theorem isPrincipal_ker_fontaineTheta [Fact ¬IsUnit (p : A)] :
    (RingHom.ker (WittVector.fontaineTheta A p)).IsPrincipal :=
  theta_kernel_principal Fact.out inferInstance

/-- In an integral perfectoid ring, every element is a `p`-th power modulo `p`. -/
theorem exists_natCast_dvd_sub_pow (x : A) : ∃ y, (p : A) ∣ x - y ^ p := by
  obtain ⟨y, hy⟩ := frobenius_surjective (p := p) (Ideal.Quotient.mk (span {(p : A)}) x)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨y, mem_span_singleton.mp (Ideal.Quotient.eq.mp ?_)⟩
  rw [map_pow]
  exact hy.symm

/-- Fontaine's map `θ : W(A♭) → A` of an integral perfectoid ring is surjective. -/
theorem surjective_fontaineTheta [Fact ¬IsUnit (p : A)] :
    Function.Surjective (WittVector.fontaineTheta A p) :=
  _root_.surjective_fontaineTheta ((surjective_frobenius_modP_iff A).mpr exists_natCast_dvd_sub_pow)

/-- In an integral perfectoid ring, Frobenius `A ⧸ π → A ⧸ π ^ p` is surjective for every `π`
with `π ^ p ∣ p`, with no completeness assumption on `π`. This is the surjectivity half of
Bhatt–Morrow–Scholze, *Integral p-adic Hodge theory*, Lemma 3.10(i). -/
theorem frobeniusModPow_surjective {π : A} (h : π ^ p ∣ (p : A)) :
    Function.Surjective (frobeniusModPow p h) :=
  (frobeniusModPow_surjective_iff h).mpr fun x ↦
    (exists_natCast_dvd_sub_pow x).imp fun _ ↦ h.trans

/-- **Existence of compatible `p`-power roots up to a unit** (Bhatt–Morrow–Scholze, *Integral
`p`-adic Hodge theory*, Lemma 3.9). If an integral perfectoid ring `A` is `π`-adically complete for
an element `π` with `π ^ p ∣ p`, then some `ϖ : PreTilt A p` satisfies `π * p ∣ π - ϖ.untilt` and
`Associated π ϖ.untilt`. -/
theorem exists_associated_untilt [Fact ¬IsUnit (p : A)] {π : A} (hdvd : π ^ p ∣ (p : A))
    [IsAdicComplete (span {π}) A] :
    ∃ ϖ : PreTilt A p, π * (p : A) ∣ π - ϖ.untilt ∧ Associated π ϖ.untilt :=
  PreTilt.exists_associated_untilt hdvd
    ((frobeniusModPow_surjective_iff hdvd).mp (frobeniusModPow_surjective hdvd))

/-- **Injectivity of relative Frobenius on an integral perfectoid ring** (Bhatt–Morrow–Scholze,
*Integral `p`-adic Hodge theory*, Lemma 3.10(i)). If `A` is `π`-adically complete for an element `π`
with `π ^ p ∣ p`, then Frobenius `A ⧸ (π) → A ⧸ (π ^ p)` is injective. No nonzerodivisor
assumption on `π` is needed. -/
theorem frobeniusModPow_injective {π : A} (h : π ^ p ∣ (p : A)) [IsAdicComplete (span {π}) A] :
    Function.Injective (frobeniusModPow p h) := by
  have hp : p.Prime := Fact.out
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Function.injective_of_subsingleton _
  have : Fact (¬IsUnit (p : A)) := ⟨not_isUnit_natCast⟩
  obtain ⟨ϖ, -, hassoc⟩ := exists_associated_untilt h
  have hspan : span {ϖ.untilt} = span {π} := by
    obtain ⟨u, hu⟩ := hassoc
    rw [← hu, span_singleton_mul_right_unit u.isUnit]
  have : IsAdicComplete (span {ϖ.untilt}) A := hspan ▸ inferInstance
  have hdvd' : ϖ.untilt ^ p ∣ (p : A) := (pow_dvd_pow_of_dvd hassoc.symm.dvd p).trans h
  have hdvd1 : ϖ.untilt ∣ (p : A) := (dvd_pow_self _ hp.ne_zero).trans hdvd'
  have : IsAdicComplete (span {ϖ}) (PreTilt A p) :=
    PreTilt.isAdicComplete_span_singleton hdvd1
  -- Build a distinguished element `ξ' = p - [ϖ ^ p] w ∈ ker θ` and show `ker θ = (ξ')`.
  obtain ⟨c, hc⟩ := hdvd'
  obtain ⟨w, hw⟩ := surjective_fontaineTheta (p := p) (A := A) c
  let ξ' : WittVector p (PreTilt A p) :=
    (p : WittVector p (PreTilt A p)) - WittVector.teichmuller p (ϖ ^ p) * w
  have hξ'_ker : ξ' ∈ RingHom.ker (WittVector.fontaineTheta A p) := by
    rw [RingHom.mem_ker]
    simp only [ξ', map_sub, map_natCast, map_mul, WittVector.fontaineTheta_teichmuller, map_pow, hw]
    rw [hc, sub_self]
  have hξ'_dist : ξ'.IsDistinguished := by
    have hpow : WittVector.teichmuller p (ϖ ^ p) =
        WittVector.teichmuller p ϖ * WittVector.teichmuller p ϖ ^ (p - 1) := by
      rw [map_pow, ← pow_succ', Nat.sub_add_cancel hp.pos]
    have heq : ξ' = (p : WittVector p (PreTilt A p)) +
        WittVector.teichmuller p ϖ * (-(WittVector.teichmuller p ϖ ^ (p - 1) * w)) := by
      simp only [ξ', hpow]
      ring
    rw [heq]
    exact WittVector.isDistinguished_p_add_teichmuller_mul_of_isAdicComplete
      (mem_span_singleton_self ϖ) _
  obtain ⟨ξ, hker⟩ := (isPrincipal_ker_fontaineTheta (p := p) (A := A)).principal
  have hker' : RingHom.ker (WittVector.fontaineTheta A p) = span {ξ} := by
    simpa [Submodule.span_singleton_eq_range] using hker
  obtain ⟨η, hη⟩ := mem_span_singleton.mp (hker' ▸ hξ'_ker)
  -- `ξ.coeff 0` has vanishing zeroth coordinate in `ModP A p`, so it lies in the Jacobson radical.
  have hξ_ker : WittVector.fontaineTheta A p ξ = 0 := by
    rw [← RingHom.mem_ker, hker']
    exact mem_span_singleton_self ξ
  have hξ0_zero : Perfection.coeff (ModP A p) p 0 (ξ.coeff 0) = 0 := by
    rw [← PreTilt.coeff_def, ← WittVector.mk_fontaineTheta, hξ_ker, map_zero]
  have : IsAdicComplete (span {ξ.coeff 0}) (PreTilt A p) :=
    Perfection.isAdicComplete_span_singleton_of_coeff_zero_eq_zero hξ0_zero
  have hξ0_jac : ξ.coeff 0 ∈ Ring.jacobson (PreTilt A p) :=
    IsAdicComplete.le_jacobson (span {ξ.coeff 0}) (mem_span_singleton_self _)
  -- Compare first Witt coordinates of `ξ' = ξ * η` to deduce that `η` is a unit.
  have hcoeff1 : ξ'.coeff 1 = (η.coeff 0) ^ p * ξ.coeff 1 + (ξ.coeff 0) ^ p * η.coeff 1 := by
    rw [hη, mul_comm, WittVector.mul_coeff_one_charP]
  have hjac_term : -((ξ.coeff 0) ^ p * η.coeff 1) ∈ Ring.jacobson (PreTilt A p) :=
    neg_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hξ0_jac p hp.pos))
  obtain ⟨u, hu⟩ := WittVector.isDistinguished_iff.mp hξ'_dist
  have hprod_unit : IsUnit ((η.coeff 0) ^ p * ξ.coeff 1) := by
    have hsum : (η.coeff 0) ^ p * ξ.coeff 1 = (u : PreTilt A p) *
        (-((ξ.coeff 0) ^ p * η.coeff 1) * (↑u⁻¹ : PreTilt A p) + 1) := by
      rw [mul_add, mul_one, mul_left_comm, Units.mul_inv, mul_one, hu, hcoeff1]
      ring
    rw [hsum]
    exact u.isUnit.mul (Ring.mem_jacobson_iff.mp hjac_term ↑u⁻¹)
  have hη_unit : IsUnit η :=
    WittVector.isUnit_iff_isUnit_coeff_zero.mpr <|
      (isUnit_pow_iff hp.ne_zero).mp (isUnit_of_mul_isUnit_left hprod_unit)
  have hker_ξ' : RingHom.ker (WittVector.fontaineTheta A p) = span {ξ'} := by
    rw [hker', hη, span_singleton_mul_right_unit hη_unit]
  -- Deduce `ϖ.untilt ^ p ∣ x ^ p → ϖ.untilt ∣ x` by lifting to `W(A♭)` and reading `coeff 0`.
  refine (frobeniusModPow_injective_iff h).mpr fun x hx ↦ hassoc.dvd.trans ?_
  obtain ⟨z, hz⟩ : ϖ.untilt ^ p ∣ x ^ p := (pow_dvd_pow_of_dvd hassoc.symm.dvd p).trans hx
  obtain ⟨y, rfl⟩ := surjective_fontaineTheta (p := p) (A := A) x
  obtain ⟨u', rfl⟩ := surjective_fontaineTheta (p := p) (A := A) z
  have hmem : y ^ p - WittVector.teichmuller p (ϖ ^ p) * u' ∈
      RingHom.ker (WittVector.fontaineTheta A p) := by
    rw [RingHom.mem_ker]
    simp only [map_sub, map_pow, map_mul, WittVector.fontaineTheta_teichmuller, hz, sub_self]
  obtain ⟨v, hv⟩ := mem_span_singleton.mp (hker_ξ' ▸ hmem)
  have hv0 := congrArg (WittVector.constantCoeff (p := p) (R := PreTilt A p)) hv
  simp only [map_sub, map_pow, map_mul, map_natCast, WittVector.constantCoeff_apply,
    WittVector.teichmuller_coeff_zero, CharP.cast_eq_zero, zero_sub, neg_mul, ξ'] at hv0
  have hy0_pow : (y.coeff 0) ^ p =
      (ϖ * (frobeniusEquiv (PreTilt A p) p).symm (u'.coeff 0 - w.coeff 0 * v.coeff 0)) ^ p := by
    rw [mul_pow, frobeniusEquiv_symm_pow_p]
    linear_combination hv0
  have hy0 : y.coeff 0 =
      ϖ * (frobeniusEquiv (PreTilt A p) p).symm (u'.coeff 0 - w.coeff 0 * v.coeff 0) :=
    injective_frobenius (PreTilt A p) p hy0_pow
  obtain ⟨y', hy'⟩ := WittVector.exists_eq_sum_teichmullerCoeff_add_pow_mul y 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, pow_one,
    WittVector.teichmullerCoeff_zero] at hy'
  rw [hy', hy0, map_add, map_mul, map_mul, map_mul, map_natCast,
    WittVector.fontaineTheta_teichmuller]
  exact dvd_add (dvd_mul_right _ _) (hdvd1.mul_right _)

/-- **Bijectivity of relative Frobenius on an integral perfectoid ring** (Bhatt–Morrow–Scholze,
*Integral `p`-adic Hodge theory*, Lemma 3.10(i)). If `A` is `π`-adically complete for an element `π`
with `π ^ p ∣ p`, then Frobenius `A ⧸ (π) → A ⧸ (π ^ p)` is bijective. -/
theorem frobeniusModPow_bijective {π : A} (h : π ^ p ∣ (p : A)) [IsAdicComplete (span {π}) A] :
    Function.Bijective (frobeniusModPow p h) :=
  ⟨frobeniusModPow_injective h, frobeniusModPow_surjective h⟩

end Basic

/-- **Perfect rings of characteristic `p` are integral perfectoid**, with `π = 0`: the ring is
`0`-adically complete, Frobenius is bijective, and the kernel of `θ` is `(p)`
(`WittVector.ker_fontaineTheta_eq_span_p`). -/
instance of_perfectRing [CharP A p] [PerfectRing A p] : IsIntegralPerfectoid p A where
  exists_adic_element := ⟨0, by simp, inferInstance⟩
  frobenius_surjective x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨Ideal.Quotient.mk _ ((frobeniusEquiv A p).symm x), ?_⟩
    dsimp only
    rw [← map_pow, frobeniusEquiv_symm_pow_p]
  theta_kernel_principal hp hc := by
    let : Fact (¬IsUnit (p : A)) := ⟨hp⟩
    have := isReduced_of_perfectRing A p
    exact ⟨⟨p, WittVector.ker_fontaineTheta_eq_span_p⟩⟩

/-- The zero ring is integral perfectoid. -/
theorem of_subsingleton [Subsingleton A] : IsIntegralPerfectoid p A where
  exists_adic_element := ⟨0, ⟨0, Subsingleton.elim _ _⟩, inferInstance⟩
  frobenius_surjective x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    dsimp only
    rw [← map_pow, Subsingleton.elim (x ^ p) x]
  theta_kernel_principal hp := (hp (isUnit_of_subsingleton _)).elim

variable {p A} in
/-- **Relative Frobenius criterion for integral perfectoid rings** (Bhatt–Morrow–Scholze,
*Integral `p`-adic Hodge theory*, Lemma 3.10(ii)). Let `A` be `π`-adically complete for a
nonzerodivisor `π` with `π ^ p ∣ p`. If relative Frobenius `A ⧸ (π) → A ⧸ (π ^ p)` is bijective,
then `A` is an integral perfectoid ring. -/
theorem of_bijective_frobeniusModPow {π : A} {hdvd : π ^ p ∣ (p : A)}
    [IsAdicComplete (span {π}) A] (hreg : π ∈ A⁰)
    (hbij : Function.Bijective (frobeniusModPow p hdvd)) : IsIntegralPerfectoid p A where
  exists_adic_element := ⟨π, hdvd, inferInstance⟩
  frobenius_surjective := surjective_pow_modP_of_frobeniusModPow_surjective hbij.2
  theta_kernel_principal hp hc := by
    let : Fact (¬IsUnit (p : A)) := ⟨hp⟩
    obtain ⟨ξ, -, -, hker⟩ :=
      WittVector.exists_isDistinguished_mem_nonZeroDivisors_ker_fontaineTheta hreg hbij
    exact ⟨⟨ξ, hker⟩⟩

end IsIntegralPerfectoid

end TauCeti.Perfectoid
