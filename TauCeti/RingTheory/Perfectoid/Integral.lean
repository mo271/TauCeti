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
public import TauCeti.RingTheory.WittVector.Primitive.Torsion

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

For every nonzero integral perfectoid ring `A`, an element `ξ ∈ ker θ` generates `ker θ` if and
only if `ξ` is distinguished (`ker_fontaineTheta_eq_span_iff_isDistinguished`); every generator is
a nonzerodivisor in `W(A♭)` (`mem_nonZeroDivisors_of_ker_fontaineTheta_eq_span`), some generator
has the normal form `p + [ϖ] ^ p * x` with `x` a unit and `ϖ.untilt ^ p` associated to `p`
(`exists_ker_fontaineTheta_eq_span_p_add_teichmuller_pow_mul`, yielding the normalized
characterisation `iff_normalized`), and any ring homomorphism between nonzero integral perfectoid
rings carries generators of `ker θ` to generators of `ker θ` (`ker_fontaineTheta_eq_span_map`).
Transporting the Witt-vector torsion bound along `W(A♭) ⧸ (ξ) ≃+* A` shows that all `p`-power
torsion in any integral perfectoid ring is killed by `p` (`p_mul_eq_zero_of_pow_mul_eq_zero`).

## Main definitions

* `TauCeti.Perfectoid.IsIntegralPerfectoid p A`: `A` is an integral perfectoid ring.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.fontaineThetaQuotientEquiv`: the ring isomorphism
  `W(A♭) ⧸ (ξ) ≃+* A` induced by `WittVector.fontaineTheta A p`.

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
* `TauCeti.Perfectoid.IsIntegralPerfectoid.frobeniusModPow_surjective`: for every `π` with
  `π ^ p ∣ p`, Frobenius `A ⧸ π → A ⧸ π ^ p` is surjective.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.exists_associated_untilt`: for every `π` with
  `π ^ p ∣ p` and `[IsAdicComplete (span {π}) A]`, `π` is associated to `ϖ.untilt` for some
  `ϖ : PreTilt A p` with `π * p ∣ π - ϖ.untilt` (Bhatt–Morrow–Scholze, Lemma 3.9).
* `TauCeti.Perfectoid.IsIntegralPerfectoid.ker_fontaineTheta_eq_span_iff_isDistinguished`:
  `ξ ∈ ker θ` generates `ker θ` iff `ξ` is distinguished.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.mem_nonZeroDivisors_of_ker_fontaineTheta_eq_span`:
  every generator of `ker θ` is a nonzerodivisor in `W(A♭)`.
* `IsIntegralPerfectoid.exists_ker_fontaineTheta_eq_span_p_add_teichmuller_pow_mul`:
  existence of a normal-form generator `p + [ϖ] ^ p * x` with `x` a unit and `ϖ.untilt ^ p`
  associated to `p`.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.exists_normalized_adic_element`,
  `TauCeti.Perfectoid.IsIntegralPerfectoid.iff_normalized`: normalized characterisation with
  `π ^ p = p * u`.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.ker_fontaineTheta_eq_span_map`: ring homomorphisms
  between nonzero integral perfectoid rings preserve generators of `ker θ`.
* `TauCeti.Perfectoid.IsIntegralPerfectoid.p_mul_eq_zero_of_pow_mul_eq_zero`,
  `TauCeti.Perfectoid.IsIntegralPerfectoid.p_pow_mul_eq_zero_iff`: all `p`-power torsion in an
  integral perfectoid ring is killed by `p` (Bhatt–Morrow–Scholze, Proposition 4.19(3)).
* `TauCeti.Perfectoid.IsIntegralPerfectoid.of_bijective_frobeniusModPow`: if `A` is `π`-adically
  complete for a nonzerodivisor `π` with `π ^ p ∣ p` and bijective relative Frobenius
  `A ⧸ (π) → A ⧸ (π ^ p)`, then `A` is integral perfectoid (Bhatt–Morrow–Scholze, Lemma 3.10(ii)).
* `TauCeti.Perfectoid.IsIntegralPerfectoid.of_perfectRing`: a perfect ring of characteristic `p`
  is integral perfectoid; the kernel of `θ` is `(p)` (`WittVector.ker_fontaineTheta_eq_span_p`).
* `TauCeti.Perfectoid.IsIntegralPerfectoid.of_subsingleton`: so is the zero ring.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, §3.2, Definition 3.5,
  Lemmas 3.9–3.10, and Remark 3.11.
* B. Bhatt, M. Morrow, P. Scholze, *Topological Hochschild homology and integral `p`-adic Hodge
  theory*, Definition 4.18 and Proposition 4.19(3).
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

/-- Every nonzero integral perfectoid ring has a distinguished element in the kernel of Fontaine's
map `θ : W(A♭) → A`. -/
private theorem exists_isDistinguished_mem_ker_fontaineTheta [Fact ¬IsUnit (p : A)] :
    ∃ ξ : WittVector p (PreTilt A p),
      ξ.IsDistinguished ∧ ξ ∈ RingHom.ker (WittVector.fontaineTheta A p) := by
  obtain ⟨π, hπ, hc⟩ := exists_adic_element (p := p) (A := A)
  obtain ⟨ϖ, -, hassoc⟩ := exists_associated_untilt (p := p) (A := A) hπ
  have hdvd : ϖ.untilt ^ p ∣ (p : A) := (pow_dvd_pow_of_dvd hassoc.symm.dvd p).trans hπ
  have hspan : span {ϖ.untilt} = span {π} := by
    obtain ⟨u, hu⟩ := hassoc
    rw [← hu, span_singleton_mul_right_unit u.isUnit]
  have : IsAdicComplete (span {ϖ.untilt}) A := hspan ▸ hc
  have : IsAdicComplete (span {ϖ}) (PreTilt A p) :=
    PreTilt.isAdicComplete_span_singleton_of_pow_dvd hdvd
  obtain ⟨c, hc'⟩ := dvd_neg.mpr hdvd
  obtain ⟨α, hα⟩ := surjective_fontaineTheta (p := p) (A := A) c
  refine ⟨(p : WittVector p (PreTilt A p)) + WittVector.teichmuller p (ϖ ^ p) * α, ?_, ?_⟩
  · exact WittVector.isDistinguished_p_add_teichmuller_mul_of_isAdicComplete
      (Ideal.pow_mem_of_mem _ (mem_span_singleton_self ϖ) p (Fact.out : p.Prime).pos) α
  · rw [RingHom.mem_ker, map_add, map_natCast, map_mul, WittVector.fontaineTheta_teichmuller,
      map_pow, hα, ← hc', add_neg_cancel]

/-- **Characterisation of generators of `ker θ` by distinguishedness** (Bhatt–Morrow–Scholze,
*Integral `p`-adic Hodge theory*, Remark 3.11; Bhatt–Morrow–Scholze, *Topological Hochschild
homology and integral `p`-adic Hodge theory*, Proposition 4.19). For any nonzero integral
perfectoid ring `A`, an element `ξ ∈ ker (fontaineTheta A p)` generates `ker (fontaineTheta A p)`
if and only if `ξ` is distinguished. -/
theorem ker_fontaineTheta_eq_span_iff_isDistinguished [Fact ¬IsUnit (p : A)]
    {ξ : WittVector p (PreTilt A p)} (hξ : ξ ∈ RingHom.ker (WittVector.fontaineTheta A p)) :
    RingHom.ker (WittVector.fontaineTheta A p) = span {ξ} ↔ ξ.IsDistinguished := by
  obtain ⟨ξ₀, hξ₀_gen⟩ := (isPrincipal_ker_fontaineTheta (p := p) (A := A)).principal
  have hξ₀_ker : ξ₀ ∈ RingHom.ker (WittVector.fontaineTheta A p) :=
    hξ₀_gen ▸ mem_span_singleton_self ξ₀
  have hξ₀_jac : ξ₀.coeff 0 ∈ Ring.jacobson (PreTilt A p) :=
    WittVector.coeff_zero_mem_jacobson_of_mem_ker_fontaineTheta hξ₀_ker
  -- Any distinguished element of `ker θ` is a multiple of `ξ₀`, forcing `ξ₀` to be distinguished.
  obtain ⟨d, hd_dist, hd_ker⟩ := exists_isDistinguished_mem_ker_fontaineTheta (p := p) (A := A)
  obtain ⟨c, hc⟩ := mem_span_singleton.mp (hξ₀_gen ▸ hd_ker)
  have hξ₀_dist : ξ₀.IsDistinguished :=
    ((WittVector.isDistinguished_mul_iff_of_coeff_zero_mem_jacobson hξ₀_jac).mp
      (by rwa [mul_comm, ← hc])).2
  refine ⟨fun hspan ↦ ?_, fun hdist ↦ ?_⟩
  · obtain ⟨y, hy⟩ := mem_span_singleton.mp (by rw [← hspan]; exact hξ₀_ker)
    have hξ_jac : ξ.coeff 0 ∈ Ring.jacobson (PreTilt A p) :=
      WittVector.coeff_zero_mem_jacobson_of_mem_ker_fontaineTheta hξ
    exact ((WittVector.isDistinguished_mul_iff_of_coeff_zero_mem_jacobson hξ_jac).mp
      (by rwa [mul_comm, ← hy])).2
  · obtain ⟨y, hy⟩ := mem_span_singleton.mp (hξ₀_gen ▸ hξ)
    have hy_unit : IsUnit y :=
      ((WittVector.isDistinguished_mul_iff_of_coeff_zero_mem_jacobson hξ₀_jac).mp
        (by rwa [mul_comm, ← hy])).1
    rw [hξ₀_gen, hy, span_singleton_mul_right_unit hy_unit]

/-- For any nonzero integral perfectoid ring `A`, `ker (fontaineTheta A p)` is generated by a
distinguished Witt vector. -/
theorem exists_isDistinguished_ker_fontaineTheta [Fact ¬IsUnit (p : A)] :
    ∃ ξ : WittVector p (PreTilt A p),
      ξ.IsDistinguished ∧ RingHom.ker (WittVector.fontaineTheta A p) = span {ξ} := by
  obtain ⟨ξ, hker⟩ := (isPrincipal_ker_fontaineTheta (p := p) (A := A)).principal
  exact ⟨ξ, (ker_fontaineTheta_eq_span_iff_isDistinguished
    (hker ▸ mem_span_singleton_self ξ)).mp hker, hker⟩

/-- Every generator of `ker (fontaineTheta A p)` of a nonzero integral perfectoid ring is a
nonzerodivisor in `W(A♭)` (Bhatt–Morrow–Scholze, *Topological Hochschild homology and integral
`p`-adic Hodge theory*, Proposition 4.19). -/
theorem mem_nonZeroDivisors_of_ker_fontaineTheta_eq_span [Fact ¬IsUnit (p : A)]
    {ξ : WittVector p (PreTilt A p)}
    (hker : RingHom.ker (WittVector.fontaineTheta A p) = span {ξ}) :
    ξ ∈ (WittVector p (PreTilt A p))⁰ :=
  ((ker_fontaineTheta_eq_span_iff_isDistinguished
    (hker ▸ mem_span_singleton_self ξ)).mp hker).mem_nonZeroDivisors

/-- **Normal-form generator of `ker θ`** (Bhatt–Morrow–Scholze, *Integral `p`-adic Hodge theory*,
Lemma 3.10; *Topological Hochschild homology and integral `p`-adic Hodge theory*, Definition 4.18).
For any nonzero integral perfectoid ring `A`, there exist `ϖ : PreTilt A p` and a unit
`x : (WittVector p (PreTilt A p))ˣ` such that `ker θ = (p + [ϖ] ^ p * x)`, `ϖ.untilt ^ p` is
associated to `p` in `A`, and `A` is `(ϖ.untilt)`-adically complete. -/
theorem exists_ker_fontaineTheta_eq_span_p_add_teichmuller_pow_mul [Fact ¬IsUnit (p : A)] :
    ∃ (ϖ : PreTilt A p) (x : (WittVector p (PreTilt A p))ˣ),
      RingHom.ker (WittVector.fontaineTheta A p) =
        span {(p : WittVector p (PreTilt A p)) + WittVector.teichmuller p ϖ ^ p * x} ∧
      Associated (ϖ.untilt ^ p) (p : A) ∧
      IsAdicComplete (span {ϖ.untilt}) A := by
  obtain ⟨ξ, hξ_dist, hker⟩ := exists_isDistinguished_ker_fontaineTheta (p := p) (A := A)
  obtain ⟨u, hu⟩ := WittVector.isDistinguished_iff_exists_unit.mp hξ_dist
  set ϖ : PreTilt A p := (frobeniusEquiv (PreTilt A p) p).symm (ξ.coeff 0)
  have hϖ : ϖ ^ p = ξ.coeff 0 := frobeniusEquiv_symm_pow_p (PreTilt A p) p (ξ.coeff 0)
  set x : (WittVector p (PreTilt A p))ˣ := u⁻¹
  have hgen : ξ * ↑x = (p : WittVector p (PreTilt A p)) + WittVector.teichmuller p ϖ ^ p * ↑x := by
    calc ξ * ↑x = (WittVector.teichmuller p (ξ.coeff 0) + ↑p * ↑u) * ↑x := congrArg (· * ↑x) hu
      _ = (p : WittVector p (PreTilt A p)) + WittVector.teichmuller p ϖ ^ p * ↑x := by
          rw [← map_pow, hϖ, add_mul, mul_assoc, Units.mul_inv, mul_one, add_comm]
  have hspan : RingHom.ker (WittVector.fontaineTheta A p) =
      span {(p : WittVector p (PreTilt A p)) + WittVector.teichmuller p ϖ ^ p * ↑x} := by
    rw [← hgen, span_singleton_mul_right_unit x.isUnit, hker]
  have hθξ : ϖ.untilt ^ p + (p : A) * WittVector.fontaineTheta A p ↑u = 0 := by
    have h0 : WittVector.fontaineTheta A p ξ = 0 :=
      RingHom.mem_ker.mp (hker ▸ mem_span_singleton_self ξ)
    rwa [hu, ← hϖ, map_add, WittVector.fontaineTheta_teichmuller, map_pow, map_mul,
      map_natCast] at h0
  have hassoc : Associated (ϖ.untilt ^ p) (p : A) := by
    refine Associated.symm ⟨Units.map (WittVector.fontaineTheta A p).toMonoidHom (-u), ?_⟩
    change (p : A) * WittVector.fontaineTheta A p (-(u : WittVector p (PreTilt A p))) = ϖ.untilt ^ p
    rw [map_neg, mul_neg, eq_comm, eq_neg_iff_add_eq_zero]
    exact hθξ
  have hle1 : span {ϖ.untilt} ^ p ≤ span {(p : A)} := by
    rw [span_singleton_pow, span_singleton_le_span_singleton]
    exact hassoc.symm.dvd
  have hle2 : span {(p : A)} ^ 1 ≤ span {ϖ.untilt} := by
    rw [pow_one, span_singleton_le_span_singleton]
    exact (dvd_pow_self ϖ.untilt (Fact.out : p.Prime).ne_zero).trans hassoc.dvd
  exact ⟨ϖ, x, hspan, hassoc, IsAdicComplete.of_pow_le_of_pow_le hle1 hle2⟩

/-- Every integral perfectoid ring admits an element `π` and a unit `u` such that `π ^ p = p * u`
and `A` is `π`-adically complete (Bhatt–Morrow–Scholze, *Topological Hochschild homology and
integral `p`-adic Hodge theory*, Definition 4.18). -/
theorem exists_normalized_adic_element :
    ∃ (π : A) (u : Aˣ), π ^ p = (p : A) * u ∧ IsAdicComplete (span {π}) A := by
  by_cases hA : Subsingleton A
  · exact ⟨0, 1, Subsingleton.elim _ _, inferInstance⟩
  · have : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    have : Fact ¬IsUnit (p : A) := ⟨not_isUnit_natCast⟩
    obtain ⟨ϖ, -, -, hassoc, hc⟩ :=
      exists_ker_fontaineTheta_eq_span_p_add_teichmuller_pow_mul (p := p) (A := A)
    obtain ⟨u, hu⟩ := hassoc.symm
    exact ⟨ϖ.untilt, u, hu.symm, hc⟩

/-- **Preservation of generators of `ker θ`.** Any ring homomorphism `f : A →+* B` between nonzero
integral perfectoid rings maps every generator of `ker (fontaineTheta A p)` to a generator of
`ker (fontaineTheta B p)`. -/
theorem ker_fontaineTheta_eq_span_map [Fact ¬IsUnit (p : A)] {B : Type*} [CommRing B]
    [IsIntegralPerfectoid p B] [Fact ¬IsUnit (p : B)] (f : A →+* B)
    {ξ : WittVector p (PreTilt A p)}
    (hker : RingHom.ker (WittVector.fontaineTheta A p) = span {ξ}) :
    RingHom.ker (WittVector.fontaineTheta B p) = span {WittVector.map (PreTilt.map p f) ξ} := by
  have hξ_ker : ξ ∈ RingHom.ker (WittVector.fontaineTheta A p) :=
    hker ▸ mem_span_singleton_self ξ
  have hξ_dist : ξ.IsDistinguished :=
    (ker_fontaineTheta_eq_span_iff_isDistinguished hξ_ker).mp hker
  have hmap_ker : WittVector.map (PreTilt.map p f) ξ ∈
      RingHom.ker (WittVector.fontaineTheta B p) := by
    rw [RingHom.mem_ker, WittVector.fontaineTheta_map, RingHom.mem_ker.mp hξ_ker, map_zero]
  exact (ker_fontaineTheta_eq_span_iff_isDistinguished hmap_ker).mpr (hξ_dist.map _)

/-- For any nonzero integral perfectoid ring `A` and any generator `ξ` of `ker (fontaineTheta A p)`,
Fontaine's map induces a ring isomorphism `W(A♭) ⧸ (ξ) ≃+* A`. -/
noncomputable def fontaineThetaQuotientEquiv [Fact ¬IsUnit (p : A)]
    {ξ : WittVector p (PreTilt A p)}
    (hker : RingHom.ker (WittVector.fontaineTheta A p) = span {ξ}) :
    (WittVector p (PreTilt A p) ⧸ span {ξ}) ≃+* A :=
  (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_fontaineTheta (p := p) (A := A)))

@[simp]
theorem fontaineThetaQuotientEquiv_mk [Fact ¬IsUnit (p : A)]
    {ξ : WittVector p (PreTilt A p)}
    (hker : RingHom.ker (WittVector.fontaineTheta A p) = span {ξ})
    (w : WittVector p (PreTilt A p)) :
    fontaineThetaQuotientEquiv hker (Ideal.Quotient.mk (span {ξ}) w) =
      WittVector.fontaineTheta A p w := by
  simp [fontaineThetaQuotientEquiv]

@[simp]
theorem fontaineThetaQuotientEquiv_symm_fontaineTheta [Fact ¬IsUnit (p : A)]
    {ξ : WittVector p (PreTilt A p)}
    (hker : RingHom.ker (WittVector.fontaineTheta A p) = span {ξ})
    (w : WittVector p (PreTilt A p)) :
    (fontaineThetaQuotientEquiv hker).symm (WittVector.fontaineTheta A p w) =
      Ideal.Quotient.mk (span {ξ}) w :=
  (fontaineThetaQuotientEquiv hker).symm_apply_eq.mpr (fontaineThetaQuotientEquiv_mk hker w).symm

/-- **All `p`-power torsion in an integral perfectoid ring is killed by `p`**
(Bhatt–Morrow–Scholze, *Topological Hochschild homology and integral `p`-adic Hodge theory*,
Proposition 4.19(3)). For any integral perfectoid ring `A`, any `n : ℕ`, and any `a : A`, if
`p ^ n * a = 0`, then `p * a = 0`. -/
theorem p_mul_eq_zero_of_pow_mul_eq_zero (n : ℕ) {a : A} (ha : (p : A) ^ n * a = 0) :
    (p : A) * a = 0 := by
  by_cases hA : Subsingleton A
  · exact Subsingleton.elim _ _
  · have : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    have : Fact ¬IsUnit (p : A) := ⟨not_isUnit_natCast⟩
    obtain ⟨ξ, hξ_dist, hker⟩ := exists_isDistinguished_ker_fontaineTheta (p := p) (A := A)
    let e := fontaineThetaQuotientEquiv hker
    obtain ⟨x, rfl⟩ := e.surjective a
    have hx : (p : WittVector p (PreTilt A p) ⧸ span {ξ}) ^ n * x = 0 :=
      e.injective (by simpa [map_mul, map_pow, map_natCast] using ha)
    have hpx := hξ_dist.p_mul_eq_zero_of_pow_mul_eq_zero n hx
    simpa [map_mul, map_natCast] using congrArg e hpx

/-- In an integral perfectoid ring `A`, for any `n ≠ 0` and any `a : A`, `p ^ n * a = 0` if and
only if `p * a = 0`. -/
theorem p_pow_mul_eq_zero_iff {n : ℕ} (hn : n ≠ 0) (a : A) :
    (p : A) ^ n * a = 0 ↔ (p : A) * a = 0 := by
  refine ⟨p_mul_eq_zero_of_pow_mul_eq_zero n, fun h ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ, mul_assoc, h, mul_zero]

end Basic

/-- **Normalized characterisation of integral perfectoid rings** (Bhatt–Morrow–Scholze,
*Topological Hochschild homology and integral `p`-adic Hodge theory*, Definition 4.18).
A commutative ring `A` is integral perfectoid if and only if there exist `π : A` and a unit
`u : Aˣ` with `π ^ p = p * u` such that `A` is `π`-adically complete, Frobenius on `A ⧸ p` is
surjective, and `ker (fontaineTheta A p)` is principal whenever `p` is not a unit. -/
theorem iff_normalized :
    IsIntegralPerfectoid p A ↔
      (∃ (π : A) (u : Aˣ), π ^ p = (p : A) * u ∧ IsAdicComplete (span {π}) A) ∧
      Function.Surjective (fun x : ModP A p ↦ x ^ p) ∧
      ∀ (hp : ¬IsUnit (p : A)) (hc : IsAdicComplete (span {(p : A)}) A),
        letI : Fact (¬IsUnit (p : A)) := ⟨hp⟩
        letI := hc
        (RingHom.ker (WittVector.fontaineTheta A p)).IsPrincipal := by
  refine ⟨fun h ↦ ⟨exists_normalized_adic_element, h.frobenius_surjective,
    h.theta_kernel_principal⟩, fun ⟨⟨π, u, hπ, hc⟩, hfrob, hker⟩ ↦ ?_⟩
  refine ⟨⟨π, ⟨↑u⁻¹, ?_⟩, hc⟩, hfrob, hker⟩
  rw [hπ, mul_assoc, Units.mul_inv, mul_one]

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
