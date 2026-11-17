/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Subring
public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import TauCeti.RingTheory.Perfectoid.AlmostSetup
public import TauCeti.RingTheory.Perfectoid.Basic
public import TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Map
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Pair
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Theta
public import TauCeti.RingTheory.WittVector.Primitive.Quotient

import TauCeti.RingTheory.Huber.OpenIdeal
import TauCeti.RingTheory.Huber.Pair.Complete
import TauCeti.RingTheory.Huber.Perfect
import TauCeti.RingTheory.Huber.Reduction
import TauCeti.RingTheory.Perfectoid.Away
import TauCeti.RingTheory.Perfectoid.Untilt
import TauCeti.RingTheory.WittVector.Quotient
import TauCeti.RingTheory.WittVector.TeichmullerCoeff

/-!
# The untilt along a primitive element is a perfectoid Tate pair

Let `p` be a prime, `(R, R⁺)` a perfect complete Hausdorff Tate pair of characteristic `p`, and
`ξ ∈ 𝕎 R⁺` a primitive Witt vector of degree one. This file proves that the untilt
`(A, A⁺) = (untilt p P (span {ξ}), untiltPlus p P (span {ξ}))` is a perfectoid Tate pair whose
tilt is canonically isomorphic to `(R, R⁺)` with Fontaine kernel `(ξ)`:

* **Algebraic tilt of `𝕎 S ⧸ I`**: for any perfect ring `S` of characteristic `p` and ideal
  `I ≤ 𝕎 S` such that `S` is `I.map constantCoeff`-adically complete and `p` is not a unit in
  `𝕎 S ⧸ I`, `PreTilt (𝕎 S ⧸ I) p ≃+* S` (`Ideal.wittVectorQuotientPreTiltEquiv`). When `𝕎 S ⧸ I`
  is `p`-adically complete, `PreTilt.untilt` is the class of the Teichmüller map and Mathlib's
  `WittVector.fontaineTheta` is the quotient map `𝕎 S → 𝕎 S ⧸ I` with kernel `I`.
* **Perfectoid Tate structure**: choosing a pseudouniformiser `ϖ ∈ R⁺` with `ϖ ^ p ∣ ξ₀` shows
  that relative Frobenius on `A⁺ = 𝕎 R⁺ ⧸ (ξ)` from `A⁺ ⧸ ([ϖ])` to `A⁺ ⧸ ([ϖ] ^ p)` is bijective,
  so `TauCeti.Perfectoid.isPerfectoidTateRing_of_hasBasis` (Bhatt–Morrow–Scholze, Lemma 3.21)
  makes `A` a uniform perfectoid Tate ring in which `p` is topologically nilpotent.
* **Ring of integral elements and almost comparison**: `A⁺` equals `A°` when `R⁺ = R°`; for an
  arbitrary Huber pair `(R, R⁺)`, the map induced by `(R, R⁺) → (R, R°)` embeds the untilt of
  `(R, R⁺)` into that of `(R, R°)`, and descending integrality modulo `[ϖ]` proves that `A⁺` is
  integrally closed in `A`, hence a ring of integral elements
  (`untilt.isRingOfIntegralElements_untiltPlus`, `untilt.pair`), with `A° / A⁺` almost zero.
* **Tilting identification and Fontaine kernel**: `uniformTilt p A` is a Tate ring, canonically
  isomorphic as a topological ring to `R` (`TauCeti.Perfectoid.untilt.tiltEquiv`,
  `TauCeti.Perfectoid.untilt.isHomeomorph_tiltEquiv`), identifying `A♭⁺` with `R⁺`, the sharp map
  of the tilt with `TauCeti.Perfectoid.untilt.sharp` (which is therefore continuous), and the
  kernel of Fontaine's map `θ_A` with `(ξ)` (`TauCeti.Perfectoid.untilt.map_ker_theta`).

## Main definitions

* `Ideal.wittVectorQuotientPreTiltEquiv`: `PreTilt (𝕎 S ⧸ I) p ≃+* S`.
* `TauCeti.Perfectoid.untilt.pair`: the Huber pair `(untilt p P (span {ξ}), untiltPlus ...)`.
* `TauCeti.Perfectoid.untilt.tiltEquivPlus`: `A♭⁺ ≃+* R⁺`.
* `TauCeti.Perfectoid.untilt.tiltEquiv`: `uniformTilt p (untilt p P (span {ξ})) ≃+* R`.
* `TauCeti.Perfectoid.untilt.tiltHom`, `TauCeti.Perfectoid.untilt.tiltInv`: mutually inverse
  morphisms of Huber pairs between `(untilt.pair hξ).tilt` and `P`.

## Main results

* `Ideal.fontaineTheta_comp_map_wittVectorQuotientPreTiltEquiv_symm`,
  `Ideal.map_ker_fontaineTheta_wittVectorQuotientPreTiltEquiv`: Fontaine's map on `𝕎 S ⧸ I`
  is the quotient map and has kernel `I`.
* `TauCeti.Perfectoid.untilt.isTopologicallyNilpotent_natCast`,
  `TauCeti.Perfectoid.untilt.isUniform`, `TauCeti.Perfectoid.untilt.isPerfectoidTateRing`:
  the untilt along a primitive element is a uniform perfectoid Tate ring.
* `TauCeti.Perfectoid.untilt.untiltPlus_eq_powerBoundedSubring`,
  `TauCeti.Perfectoid.untilt.isIntegrallyClosedIn_untiltPlus`,
  `TauCeti.Perfectoid.untilt.isRingOfIntegralElements_untiltPlus`: `A⁺` is a ring of integral
  elements, equal to `A°` when `R⁺ = R°`.
* `TauCeti.Perfectoid.untilt.isAlmostZero_powerBounded_quotient`,
  `TauCeti.Perfectoid.untilt.isAlmostIso_algebraLinearMap`: `A° / A⁺` is almost zero.
* `TauCeti.Perfectoid.untilt.sharp_tiltEquiv`, `TauCeti.Perfectoid.untilt.continuous_sharp`,
  `TauCeti.Perfectoid.untilt.isHomeomorph_tiltEquiv`, `TauCeti.Perfectoid.untilt.theta_eq`,
  `TauCeti.Perfectoid.untilt.map_ker_theta`: topological tilting identification and Fontaine kernel.

## References

* P. Scholze, *Étale cohomology of diamonds*, §3, Theorem 3.17.
* P. Scholze and J. Weinstein, *Berkeley lectures on `p`-adic geometry*, Theorem 6.2.11.
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Theorem 2.3.9, Definition 2.3.14, Remark 2.3.16.
* K. S. Kedlaya, R. Liu, *Relative `p`-adic Hodge theory II*, Lemma 3.3.7, Theorem 3.3.8.
* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.21.
-/

public section

open Filter Topology TauCeti.Huber
open WittVector (teichmuller constantCoeff constantCoeff_apply)
open scoped nonZeroDivisors Pointwise

/-! ### Auxiliary lemmas on perfection and `PreTilt` -/

section Helpers

private theorem iterate_frobeniusEquiv_symm_pow {p : ℕ} [Fact p.Prime] {S : Type*} [CommRing S]
    [CharP S p] [PerfectRing S p] (a : S) (n : ℕ) :
    ((frobeniusEquiv S p).symm^[n] a) ^ p ^ n = a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p, ih]

private theorem isAdicComplete_span_singleton_of_mem_radical {S : Type*} [CommRing S]
    {ϖ a : S} [IsAdicComplete (Ideal.span {ϖ}) S] (ha : a ∈ (Ideal.span {ϖ}).radical) :
    IsAdicComplete (Ideal.span {a}) S := by
  obtain ⟨m, hm⟩ := ha
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [pow_zero, Ideal.mem_span_singleton, isUnit_iff_dvd_one.symm] at hm
    have htop : Ideal.span {ϖ} = ⊤ := Ideal.span_singleton_eq_top.mpr hm
    have hsub : Subsingleton S := ⟨fun x y ↦ by
      apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {ϖ})).mpr
      intro n
      refine SModEq.sub_mem.mpr ?_
      rw [← one_smul S (x - y)]
      exact Submodule.smul_mem_smul (by rw [htop, Ideal.top_pow]; trivial) trivial⟩
    exact
      { toIsHausdorff := ⟨fun x _ ↦ Subsingleton.elim x 0⟩
        toIsPrecomplete := ⟨fun f _ ↦ ⟨0, fun n ↦ by rw [Subsingleton.elim (f n) 0]⟩⟩ }
  · have := IsAdicComplete.span_singleton_of_dvd (M := S) (Ideal.mem_span_singleton.mp hm)
    refine IsAdicComplete.of_pow_le_of_pow_le (I := Ideal.span {a ^ m}) (k := m) (l := 1) ?_ ?_
    · rw [Ideal.span_singleton_pow]
    · rw [pow_one, Ideal.span_singleton_le_span_singleton]
      exact dvd_pow_self a hm0

private noncomputable def perfectionRingEquiv {p : ℕ} [Fact p.Prime] {R₁ R₂ : Type*}
    [CommRing R₁] [CommRing R₂] [CharP R₁ p] [CharP R₂ p] (e : R₁ ≃+* R₂) :
    Perfection R₁ p ≃+* Perfection R₂ p :=
  RingEquiv.ofRingHom (Perfection.map p e.toRingHom) (Perfection.map p e.symm.toRingHom)
    (RingHom.ext fun x ↦ Perfection.ext fun n ↦ by simp)
    (RingHom.ext fun x ↦ Perfection.ext fun n ↦ by simp)

private theorem coeff_perfectionRingEquiv {p : ℕ} [Fact p.Prime] {R₁ R₂ : Type*}
    [CommRing R₁] [CommRing R₂] [CharP R₁ p] [CharP R₂ p] (e : R₁ ≃+* R₂)
    (x : Perfection R₁ p) (n : ℕ) :
    Perfection.coeff R₂ p n (perfectionRingEquiv e x) = e (Perfection.coeff R₁ p n x) := by
  simp [perfectionRingEquiv]

private theorem coeff_perfectionRingEquiv_symm {p : ℕ} [Fact p.Prime] {R₁ R₂ : Type*}
    [CommRing R₁] [CommRing R₂] [CharP R₁ p] [CharP R₂ p] (e : R₁ ≃+* R₂)
    (x : Perfection R₂ p) (n : ℕ) :
    Perfection.coeff R₁ p n ((perfectionRingEquiv e).symm x) =
      e.symm (Perfection.coeff R₂ p n x) := by
  simp [perfectionRingEquiv]

/-- Transport `PreTilt` along a ring equivalence. -/
private noncomputable def preTiltRingEquiv {p : ℕ} [Fact p.Prime] {A₁ A₂ : Type*}
    [CommRing A₁] [CommRing A₂] [Fact ¬IsUnit (p : A₁)] [Fact ¬IsUnit (p : A₂)]
    (e : A₁ ≃+* A₂) : PreTilt A₁ p ≃+* PreTilt A₂ p :=
  let eMod : ModP A₁ p ≃+* ModP A₂ p :=
    Ideal.quotientEquiv (Ideal.span {(p : A₁)}) (Ideal.span {(p : A₂)}) e (by
      rw [Ideal.map_span, Set.image_singleton, RingEquiv.coe_toRingHom, map_natCast])
  PreTilt.equivPerfection.trans ((perfectionRingEquiv eMod).trans PreTilt.equivPerfection.symm)

private theorem coeff_preTiltRingEquiv {p : ℕ} [Fact p.Prime] {A₁ A₂ : Type*}
    [CommRing A₁] [CommRing A₂] [Fact ¬IsUnit (p : A₁)] [Fact ¬IsUnit (p : A₂)]
    (e : A₁ ≃+* A₂) (x : PreTilt A₁ p) (n : ℕ) :
    PreTilt.coeff n (preTiltRingEquiv e x) =
      Ideal.quotientEquiv (Ideal.span {(p : A₁)}) (Ideal.span {(p : A₂)}) e (by
        rw [Ideal.map_span, Set.image_singleton, RingEquiv.coe_toRingHom, map_natCast])
        (PreTilt.coeff n x) := by
  simp [preTiltRingEquiv, coeff_perfectionRingEquiv]

private theorem untilt_preTiltRingEquiv {p : ℕ} [Fact p.Prime] {A₁ A₂ : Type*}
    [CommRing A₁] [CommRing A₂] [Fact ¬IsUnit (p : A₁)] [Fact ¬IsUnit (p : A₂)]
    [IsAdicComplete (Ideal.span {(p : A₁)}) A₁] [IsAdicComplete (Ideal.span {(p : A₂)}) A₂]
    (e : A₁ ≃+* A₂) (x : PreTilt A₁ p) :
    (preTiltRingEquiv e x).untilt = e x.untilt := by
  rw [← PreTilt.teichmuller₀_equivPerfection]
  refine Perfection.teichmuller₀_spec fun n ↦
    ⟨e (PreTilt.untilt (((frobeniusEquiv (PreTilt A₁ p) p).symm^[n]) x)), ?_, ?_⟩
  · rw [PreTilt.coeff_equivPerfection, coeff_preTiltRingEquiv, PreTilt.coeff_eq_mk_untilt_iterate,
      Ideal.quotientEquiv_mk]
  · rw [← map_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]

/-- Functoriality of `WittVector` on ring equivalences. -/
private noncomputable def wittVectorMapEquiv {p : ℕ} [Fact p.Prime] {A₁ A₂ : Type*}
    [CommRing A₁] [CommRing A₂] (e : A₁ ≃+* A₂) :
    WittVector p A₁ ≃+* WittVector p A₂ :=
  RingEquiv.ofRingHom (WittVector.map e.toRingHom) (WittVector.map e.symm.toRingHom)
    (RingHom.ext fun x ↦ WittVector.ext fun n ↦ by simp [WittVector.map_coeff])
    (RingHom.ext fun x ↦ WittVector.ext fun n ↦ by simp [WittVector.map_coeff])

end Helpers

/-! ### Algebraic tilt and Fontaine kernel of `𝕎 S ⧸ (ξ)` -/

namespace WittVector.IsDistinguished

variable {p : ℕ} [hp : Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]
  {ϖ : S} {ξ : WittVector p S}

local notation "𝕎" => WittVector p

/-- If `ξ` is distinguished and `ϖ ^ p ∣ ξ.coeff 0`, then `[ϖ] ^ p ∣ p` in `𝕎 S ⧸ (ξ)`. -/
theorem pow_prime_dvd_natCast_quotient (hξ : ξ.IsDistinguished) (hξ₀ : ϖ ^ p ∣ ξ.coeff 0) :
    Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ) ^ p ∣
      (p : 𝕎 S ⧸ Ideal.span {ξ}) := by
  obtain ⟨u, hu⟩ := WittVector.isDistinguished_iff_exists_unit.mp hξ
  obtain ⟨c, hc⟩ := hξ₀
  refine ⟨-Ideal.Quotient.mk (Ideal.span {ξ}) ↑u⁻¹ *
      Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p c), ?_⟩
  have hξ_zero : Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p (ξ.coeff 0)) +
      (p : 𝕎 S ⧸ Ideal.span {ξ}) * Ideal.Quotient.mk (Ideal.span {ξ}) ↑u = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {ξ})), ← map_mul, ← map_add, ← hu,
      Ideal.Quotient.mk_singleton_self]
  have hu' : Ideal.Quotient.mk (Ideal.span {ξ}) ↑u⁻¹ *
      Ideal.Quotient.mk (Ideal.span {ξ}) ↑u = 1 := by
    rw [← map_mul, u.inv_mul, map_one]
  have hfac : Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ) ^ p *
      Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p c) =
      Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p (ξ.coeff 0)) := by
    rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, ← hc]
  calc (p : 𝕎 S ⧸ Ideal.span {ξ})
    _ = (p : 𝕎 S ⧸ Ideal.span {ξ}) * (Ideal.Quotient.mk (Ideal.span {ξ}) ↑u⁻¹ *
          Ideal.Quotient.mk (Ideal.span {ξ}) ↑u) := by rw [hu', mul_one]
    _ = -Ideal.Quotient.mk (Ideal.span {ξ}) ↑u⁻¹ *
          Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p (ξ.coeff 0)) := by
        linear_combination Ideal.Quotient.mk (Ideal.span {ξ}) ↑u⁻¹ * hξ_zero
    _ = Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ) ^ p *
          (-Ideal.Quotient.mk (Ideal.span {ξ}) ↑u⁻¹ *
            Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p c)) := by
        rw [← hfac]
        ring

/-- **Bijectivity of relative Frobenius on `𝕎 S ⧸ (ξ)`**: when `ξ` is distinguished and
`ϖ ^ p ∣ ξ.coeff 0`, the relative Frobenius
`(𝕎 S ⧸ (ξ)) ⧸ ([ϖ]) → (𝕎 S ⧸ (ξ)) ⧸ ([ϖ] ^ p)` is bijective. -/
theorem frobeniusModPow_bijective_quotient (hξ : ξ.IsDistinguished) (hξ₀ : ϖ ^ p ∣ ξ.coeff 0) :
    Function.Bijective
      (TauCeti.frobeniusModPow p (hξ.pow_prime_dvd_natCast_quotient hξ₀)) := by
  let e₁ := hξ.quotientTeichmullerEquiv ((dvd_pow_self _ hp.out.ne_zero).trans hξ₀)
  let e₂ := (Ideal.quotEquivOfEq (I := Ideal.span
      {Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ) ^ p})
      (J := Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p (ϖ ^ p))})
      (by rw [← map_pow, ← map_pow])).trans (hξ.quotientTeichmullerEquiv hξ₀)
  let fS : S ⧸ Ideal.span {ϖ} ≃+* S ⧸ Ideal.span {ϖ ^ p} :=
    Ideal.quotientEquiv (Ideal.span {ϖ}) (Ideal.span {ϖ ^ p}) (_root_.frobeniusEquiv S p) (by
      rw [Ideal.map_span, Set.image_singleton, RingEquiv.coe_toRingHom, coe_frobeniusEquiv,
        frobenius_def])
  have heq : ⇑(TauCeti.frobeniusModPow p (hξ.pow_prime_dvd_natCast_quotient hξ₀)) =
      ⇑((e₁.trans fS).trans e₂.symm) := by
    funext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hmk : TauCeti.frobeniusModPow p (hξ.pow_prime_dvd_natCast_quotient hξ₀)
        (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {ξ}) w)) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {ξ}) w ^ p) :=
      TauCeti.frobeniusModPow_mk _ _
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.eq_symm_apply, hmk,
      ← map_pow (Ideal.Quotient.mk (Ideal.span {ξ})) w p]
    simp only [e₁, e₂, fS, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      quotientTeichmullerEquiv_mk_mk, Ideal.quotientEquiv_mk, coe_frobeniusEquiv, frobenius_def,
      ← constantCoeff_apply, map_pow]
  rw [heq]
  exact ((e₁.trans fS).trans e₂.symm).bijective

end WittVector.IsDistinguished

/-! ### Algebraic tilt and Fontaine kernel of `𝕎 S ⧸ I` -/

namespace Ideal

variable {p : ℕ} [hp : Fact p.Prime] {S : Type*} [CommRing S] [CharP S p] [PerfectRing S p]

local notation "𝕎" => WittVector p

/-- **Algebraic tilt of `𝕎 S ⧸ I`**: over a perfect ring `S` of characteristic `p`, if `I ≤ 𝕎 S`
is an ideal such that `S` is `I.map constantCoeff`-adically complete and `p` is not a unit in
`𝕎 S ⧸ I`, then `PreTilt (𝕎 S ⧸ I) p ≃+* S`. -/
noncomputable def wittVectorQuotientPreTiltEquiv (I : Ideal (𝕎 S))
    [IsAdicComplete (I.map constantCoeff) S] [hpu : Fact ¬IsUnit (p : 𝕎 S ⧸ I)] :
    PreTilt (𝕎 S ⧸ I) p ≃+* S := by
  let J : Ideal S := I.map constantCoeff
  let eMod : ModP (𝕎 S ⧸ I) p ≃+* S ⧸ J := I.wittVectorQuotientPEquiv
  have : Nontrivial (ModP (𝕎 S ⧸ I) p) :=
    Ideal.Quotient.nontrivial_iff.mpr (mt Ideal.span_singleton_eq_top.mp hpu.out)
  have : Nontrivial (S ⧸ J) := eMod.injective.nontrivial
  have : CharP (S ⧸ J) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr <| by
    rw [← map_natCast (Ideal.Quotient.mk J), CharP.cast_eq_zero S p, map_zero]
  let eRed : Perfection S p ≃+* Perfection (S ⧸ J) p :=
    RingEquiv.ofBijective (Perfection.map p (Ideal.Quotient.mk J)) <| by
      have heq : ⇑(Perfection.map p (Ideal.Quotient.mk J)) = ⇑(Perfection.quotientMulEquiv p J) :=
        funext fun x ↦ Perfection.ext fun n ↦ by simp
      rw [heq]
      exact (Perfection.quotientMulEquiv p J).bijective
  exact PreTilt.equivPerfection.trans
    ((perfectionRingEquiv eMod).trans (eRed.symm.trans (PerfectionMap.id p S).equiv.symm))

/-- The inverse of `wittVectorQuotientPreTiltEquiv` sends `a : S` to the sequence of classes of
`[a ^ (1 / p ^ n)]`. -/
@[simp]
theorem coeff_wittVectorQuotientPreTiltEquiv_symm (I : Ideal (𝕎 S))
    [IsAdicComplete (I.map constantCoeff) S] [hpu : Fact ¬IsUnit (p : 𝕎 S ⧸ I)] (a : S) (n : ℕ) :
    PreTilt.coeff n (I.wittVectorQuotientPreTiltEquiv.symm a) =
      Ideal.Quotient.mk (Ideal.span {(p : 𝕎 S ⧸ I)})
        (Ideal.Quotient.mk I (teichmuller p ((frobeniusEquiv S p).symm^[n] a))) := by
  let J : Ideal S := I.map constantCoeff
  let eMod : ModP (𝕎 S ⧸ I) p ≃+* S ⧸ J := I.wittVectorQuotientPEquiv
  have : Nontrivial (ModP (𝕎 S ⧸ I) p) :=
    Ideal.Quotient.nontrivial_iff.mpr (mt Ideal.span_singleton_eq_top.mp hpu.out)
  have : Nontrivial (S ⧸ J) := eMod.injective.nontrivial
  have : CharP (S ⧸ J) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr <| by
    rw [← map_natCast (Ideal.Quotient.mk J), CharP.cast_eq_zero S p, map_zero]
  unfold wittVectorQuotientPreTiltEquiv
  simp only [RingEquiv.symm_trans_apply, RingEquiv.symm_symm, PreTilt.coeff_equivPerfection_symm,
    coeff_perfectionRingEquiv_symm]
  have heval : Perfection.coeff (S ⧸ J) p n
      (Perfection.map p (Ideal.Quotient.mk J) ((PerfectionMap.id p S).equiv a)) =
      Ideal.Quotient.mk J ((frobeniusEquiv S p).symm^[n] a) := by
    rw [Perfection.coeff_map, PerfectionMap.equiv_apply]
    rfl
  rw [RingEquiv.ofBijective_apply, heval]
  exact I.wittVectorQuotientPEquiv_symm_mk _

/-- Under `wittVectorQuotientPreTiltEquiv`, `PreTilt.untilt` sends `a : S` to the class of `[a]` in
`𝕎 S ⧸ I`. -/
@[simp]
theorem untilt_wittVectorQuotientPreTiltEquiv_symm (I : Ideal (𝕎 S))
    [IsAdicComplete (I.map constantCoeff) S] [Fact ¬IsUnit (p : 𝕎 S ⧸ I)]
    [IsAdicComplete (Ideal.span {(p : 𝕎 S ⧸ I)}) (𝕎 S ⧸ I)] (a : S) :
    (I.wittVectorQuotientPreTiltEquiv.symm a).untilt =
      Ideal.Quotient.mk I (teichmuller p a) := by
  rw [← PreTilt.teichmuller₀_equivPerfection]
  refine Perfection.teichmuller₀_spec fun n ↦
    ⟨Ideal.Quotient.mk I (teichmuller p ((frobeniusEquiv S p).symm^[n] a)), ?_, ?_⟩
  · rw [PreTilt.coeff_equivPerfection, coeff_wittVectorQuotientPreTiltEquiv_symm]
  · rw [← map_pow, ← map_pow, iterate_frobeniusEquiv_symm_pow]
    rfl

/-- **Fontaine's map on `𝕎 S ⧸ I` is the quotient map**: composing `WittVector.fontaineTheta`
with `𝕎 (wittVectorQuotientPreTiltEquiv.symm)` recovers `Ideal.Quotient.mk I`. -/
theorem fontaineTheta_comp_map_wittVectorQuotientPreTiltEquiv_symm (I : Ideal (𝕎 S))
    [IsAdicComplete (I.map constantCoeff) S] [Fact ¬IsUnit (p : 𝕎 S ⧸ I)]
    [IsAdicComplete (Ideal.span {(p : 𝕎 S ⧸ I)}) (𝕎 S ⧸ I)] :
    (WittVector.fontaineTheta (𝕎 S ⧸ I) p).comp
      (WittVector.map I.wittVectorQuotientPreTiltEquiv.symm.toRingHom) =
      Ideal.Quotient.mk I := by
  refine WittVector.ringHom_ext_teichmuller fun a ↦ ?_
  simp only [RingHom.comp_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, untilt_wittVectorQuotientPreTiltEquiv_symm]

/-- **Kernel of Fontaine's map on `𝕎 S ⧸ I`**: under `wittVectorQuotientPreTiltEquiv`, the kernel
of `WittVector.fontaineTheta (𝕎 S ⧸ I) p` maps onto `I`. -/
theorem map_ker_fontaineTheta_wittVectorQuotientPreTiltEquiv (I : Ideal (𝕎 S))
    [IsAdicComplete (I.map constantCoeff) S] [Fact ¬IsUnit (p : 𝕎 S ⧸ I)]
    [IsAdicComplete (Ideal.span {(p : 𝕎 S ⧸ I)}) (𝕎 S ⧸ I)] :
    (RingHom.ker (WittVector.fontaineTheta (𝕎 S ⧸ I) p)).map
      (WittVector.map I.wittVectorQuotientPreTiltEquiv.toRingHom) = I := by
  let eW := wittVectorMapEquiv (p := p) I.wittVectorQuotientPreTiltEquiv
  rw [show WittVector.map I.wittVectorQuotientPreTiltEquiv.toRingHom = (eW : _ →+* _) from rfl,
    Ideal.map_comap_of_equiv eW]
  ext w
  have hev := RingHom.congr_fun I.fontaineTheta_comp_map_wittVectorQuotientPreTiltEquiv_symm w
  rw [RingHom.comp_apply] at hev
  rw [Ideal.mem_comap, RingHom.mem_ker,
    show eW.symm w = WittVector.map I.wittVectorQuotientPreTiltEquiv.symm.toRingHom w from rfl,
    hev, Ideal.Quotient.eq_zero_iff_mem]

end Ideal

/-! ### Perfectoid Tate pair structure and tilting identification of the untilt -/

namespace TauCeti.Perfectoid.untilt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

local notation "𝕎" => WittVector p

section PrimitiveTate

variable [TopologicalSpace R] [IsTopologicalRing R] [IsTateRing R] [CharP R p] [PerfectRing R p]
  {P : Pair R} {ξ : WittVector p P.plus}

/-- For a primitive Witt vector `ξ ∈ 𝕎 R⁺`, there exists a pseudouniformiser `ϖ ∈ R⁺` whose `p`-th
power divides `ξ.coeff 0` in `R⁺`. -/
theorem exists_isPseudoUniformizer_pow_dvd_coeff_zero (hξ : ξ.IsPrimitive) :
    ∃ ϖ : P.plus, IsPseudoUniformizer (ϖ : R) ∧ ϖ ^ p ∣ ξ.coeff 0 := by
  obtain ⟨ϖ₀, hϖ₀⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  have hϖ₀p : IsUnit ((ϖ₀ ^ p : P.plus) : R) := by simpa using hϖ₀.isUnit.pow p
  have hξ0_nil : IsTopologicallyNilpotent ((ξ.coeff 0 : P.plus) : R) :=
    hξ.isTopologicallyNilpotent_coeff_zero.map (φ := P.plus.subtype) continuous_subtype_val
  obtain ⟨m, c, hc⟩ := P.plus.exists_dvd_pow_of_isTopologicallyNilpotent
    P.isRingOfIntegralElements.isOpen hϖ₀p hξ0_nil
  -- Take `ϖ = ϖ₀ ^ (1 / p ^ m)` in the perfect ring `R⁺`.
  let ϖ : P.plus := (frobeniusEquiv P.plus p).symm^[m] ϖ₀
  have hϖ_pow : ϖ ^ p ^ m = ϖ₀ := iterate_frobeniusEquiv_symm_pow ϖ₀ m
  have hϖ_powR : (ϖ : R) ^ p ^ m = (ϖ₀ : R) := by
    rw [← Subring.coe_pow, hϖ_pow]
  have hϖ : IsPseudoUniformizer (ϖ : R) := isPseudoUniformizer_iff.mpr
    ⟨(isUnit_pow_iff (pow_ne_zero m hp.out.ne_zero)).mp (hϖ_powR ▸ hϖ₀.isUnit),
      (hϖ_powR ▸ hϖ₀.isTopologicallyNilpotent).of_pow (pow_ne_zero m hp.out.ne_zero)⟩
  refine ⟨ϖ, hϖ, ?_⟩
  -- Since `m ≤ p ^ m`, `(ξ₀ / ϖ ^ p) ^ (p ^ m) = c * ξ₀ ^ (p ^ m - m) ∈ R⁺`, and `R⁺` is
  -- integrally closed in `R`.
  obtain ⟨u, hu⟩ := hϖ.isUnit.pow p
  have hle : m ≤ p ^ m := (Nat.lt_pow_self hp.out.one_lt).le
  let y : R := (↑u⁻¹ : R) * (ξ.coeff 0 : R)
  have hy_pow : y ^ p ^ m = ((c * ξ.coeff 0 ^ (p ^ m - m) : P.plus) : R) := by
    have hsplit : (ξ.coeff 0 : R) ^ p ^ m =
        ((ϖ : R) ^ p) ^ p ^ m * ((c * ξ.coeff 0 ^ (p ^ m - m) : P.plus) : R) := by
      have h1 : (ξ.coeff 0 : P.plus) ^ p ^ m =
          (ϖ ^ p) ^ p ^ m * (c * ξ.coeff 0 ^ (p ^ m - m)) := by
        rw [← pow_mul, mul_comm p, pow_mul, hϖ_pow, ← mul_assoc, ← hc, ← pow_add,
          Nat.add_sub_of_le hle]
      simpa only [Subring.coe_pow, Subring.coe_mul] using congrArg Subtype.val h1
    rw [mul_pow, hsplit, ← mul_assoc, ← mul_pow, ← hu, Units.inv_mul, one_pow, one_mul]
  have hy_mem : y ∈ P.plus :=
    P.isRingOfIntegralElements.mem_of_pow_mem (pow_pos hp.out.pos m)
      (hy_pow ▸ (c * ξ.coeff 0 ^ (p ^ m - m)).2)
  refine ⟨⟨y, hy_mem⟩, Subtype.ext ?_⟩
  simp only [Subring.coe_mul, Subring.coe_pow, y, ← hu, ← mul_assoc, Units.mul_inv, one_mul]

/-- For a primitive Witt vector `ξ ∈ 𝕎 R⁺`, the untilt admits a pseudouniformiser with
compatible `p`-power roots whose `p`-th power divides `p` in `A°`. -/
theorem nonempty_pseudoUniformizerRoots (hξ : ξ.IsPrimitive) :
    Nonempty (PseudoUniformizerRoots p (untilt p P (Ideal.span {ξ}))) := by
  obtain ⟨ϖ, hϖ, hξ₀⟩ := exists_isPseudoUniformizer_pow_dvd_coeff_zero hξ
  obtain ⟨c, hc⟩ := hξ.isDistinguished.pow_prime_dvd_natCast_quotient hξ₀
  refine ⟨{
    roots := ⟨fun n ↦ sharp p P (Ideal.span {ξ}) ((frobeniusEquiv R p).symm^[n] (ϖ : R)),
      fun n ↦ by rw [← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]⟩
    isPseudoUniformizer := by
      simpa only [Perfection.coeffMonoidHom_mk, Function.iterate_zero_apply] using
        isPseudoUniformizer_sharp (J := Ideal.span {ξ}) hϖ
    pow_dvd := by
      refine ⟨⟨algebraMap _ _ c, untiltPlus_le_powerBoundedSubring (mem_untiltPlus.mpr ⟨c, rfl⟩)⟩,
        Subtype.ext ?_⟩
      simp only [Perfection.coeffMonoidHom_mk, Function.iterate_zero_apply, Subring.coe_natCast,
        Subring.coe_mul, Subring.coe_pow, sharp_coe]
      rw [← map_pow, ← map_mul, ← hc, map_natCast] }⟩

/-- The prime `p` is topologically nilpotent in the untilt along a primitive element. -/
theorem isTopologicallyNilpotent_natCast (hξ : ξ.IsPrimitive) :
    IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ})) := by
  obtain ⟨ϖ, hϖ, hξ₀⟩ := exists_isPseudoUniformizer_pow_dvd_coeff_zero hξ
  exact isTopologicallyNilpotent_natCast_of_hasBasis (hasBasis_nhds_zero hϖ)
    ((dvd_pow_self _ hp.out.ne_zero).trans (hξ.isDistinguished.pow_prime_dvd_natCast_quotient hξ₀))

/-- The image of `[ϖ]` is a nonzerodivisor in `𝕎 R⁺ ⧸ (ξ)` when `ϖ ∣ ξ.coeff 0`. -/
private theorem mk_teichmuller_mem_nonZeroDivisors_of_dvd (hξ : ξ.IsPrimitive) {ϖ : P.plus}
    (hϖ : IsPseudoUniformizer (ϖ : R)) (hξ₀ : ϖ ∣ ξ.coeff 0) :
    Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ) ∈ (𝕎 P.plus ⧸ Ideal.span {ξ})⁰ :=
  hξ.isDistinguished.mk_teichmuller_mem_nonZeroDivisors
    ⟨1, by rw [pow_one]; exact Ideal.mem_span_singleton.mpr hξ₀⟩
    (comap_nonZeroDivisors_le_of_injective (f := P.plus.subtype) Subtype.val_injective
      hϖ.isUnit.mem_nonZeroDivisors)

/-- **The untilt along a primitive element is uniform.** -/
theorem isUniform (hξ : ξ.IsPrimitive) : IsUniform (untilt p P (Ideal.span {ξ})) := by
  obtain ⟨ϖ, hϖ, hξ₀⟩ := exists_isPseudoUniformizer_pow_dvd_coeff_zero hξ
  have := isLocalizationAway (J := Ideal.span {ξ}) hϖ
  have hπ := mk_teichmuller_mem_nonZeroDivisors_of_dvd hξ hϖ
    ((dvd_pow_self _ hp.out.ne_zero).trans hξ₀)
  have hdvd := hξ.isDistinguished.pow_prime_dvd_natCast_quotient hξ₀
  have hinj := (TauCeti.frobeniusModPow_injective_iff hdvd).mp
    (hξ.isDistinguished.frobeniusModPow_bijective_quotient hξ₀).1
  refine isUniform_of_hasBasis_of_compatible_roots (hasBasis_nhds_zero hϖ) hp.out.one_lt hπ hinj
    (w := fun n ↦ Ideal.Quotient.mk (Ideal.span {ξ})
      (teichmuller p ((frobeniusEquiv P.plus p).symm^[n] ϖ)))
    (fun n ↦ by rw [← map_pow, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p])
    (by simp)

/-- Over a nonzero Hausdorff uniform perfect Tate ring of characteristic `p`, the untilt along a
primitive element is nonzero. -/
theorem nontrivial [T2Space R] [IsUniform R] [Nontrivial R] (hξ : ξ.IsPrimitive) :
    Nontrivial (untilt p P (Ideal.span {ξ})) := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  obtain ⟨ϖ, hϖ, hξ₀⟩ := exists_isPseudoUniformizer_pow_dvd_coeff_zero hξ
  have hsubA₀ : Subsingleton (𝕎 P.plus ⧸ Ideal.span {ξ}) :=
    (algebraMap_injective hξ).subsingleton
  have hsubQ : Subsingleton (P.plus ⧸ Ideal.span {ϖ}) :=
    (hξ.isDistinguished.quotientTeichmullerEquiv
      ((dvd_pow_self _ hp.out.ne_zero).trans hξ₀)).symm.injective.subsingleton
  have htop : Ideal.span {ϖ} = ⊤ :=
    (Ideal.Quotient.subsingleton_iff (I := Ideal.span {ϖ})).mp hsubQ
  exact P.isRingOfIntegralElements.not_isUnit_of_isTopologicallyNilpotent
    hϖ.isTopologicallyNilpotent (Ideal.span_singleton_eq_top.mp htop)

/-- **When `R⁺ = R°`, `untiltPlus` equals the full power-bounded subring `A°`.** -/
theorem untiltPlus_eq_powerBoundedSubring [IsUniform R]
    {ξ : WittVector p (Pair.powerBounded R).plus} (hξ : ξ.IsPrimitive) :
    untiltPlus p (Pair.powerBounded R) (Ideal.span {ξ}) =
      powerBoundedSubring (untilt p (Pair.powerBounded R) (Ideal.span {ξ})) := by
  refine le_antisymm untiltPlus_le_powerBoundedSubring fun x hx ↦ ?_
  obtain ⟨ϖ, hϖ, hξ₀⟩ :=
    exists_isPseudoUniformizer_pow_dvd_coeff_zero (P := Pair.powerBounded R) hξ
  have := isLocalizationAway (J := Ideal.span {ξ}) hϖ
  have hπ := mk_teichmuller_mem_nonZeroDivisors_of_dvd hξ hϖ
    ((dvd_pow_self _ hp.out.ne_zero).trans hξ₀)
  have hdvd := hξ.isDistinguished.pow_prime_dvd_natCast_quotient hξ₀
  have hinj := (TauCeti.frobeniusModPow_injective_iff hdvd).mp
    (hξ.isDistinguished.frobeniusModPow_bijective_quotient hξ₀).1
  let r : ℕ → (Pair.powerBounded R).plus :=
    fun n ↦ (frobeniusEquiv (Pair.powerBounded R).plus p).symm^[n] ϖ
  let w : ℕ → 𝕎 (Pair.powerBounded R).plus ⧸ Ideal.span {ξ} := fun n ↦
    Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p (r n))
  have hw : ∀ n, w (n + 1) ^ p = w n := fun n ↦ by
    dsimp only [w, r]
    rw [← map_pow, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  have halmost := (mem_powerBoundedSubring_iff_forall_mul_mem_range_of_hasBasis
    (hasBasis_nhds_zero hϖ) hp.out.one_lt hπ hinj hw (by simp [w, r])).mp hx
  -- Let `y ∈ A₀` represent `[ϖ] * x`; then `w n ^ (p ^ n - 1) ∣ y` in `A₀` for every `n`.
  obtain ⟨y, hy⟩ := halmost 0
  have hy_dvd (n : ℕ) : w n ^ (p ^ n - 1) ∣ y := by
    obtain ⟨z, hz⟩ := halmost n
    refine ⟨z, algebraMap_injective hξ ?_⟩
    have hpow : w n ^ p ^ n = w 0 := by
      dsimp only [w, r]
      rw [← map_pow, ← map_pow, iterate_frobeniusEquiv_symm_pow]
      rfl
    have h1 : 1 ≤ p ^ n := Nat.one_le_pow n p hp.out.pos
    rw [hy, map_mul, map_pow, hz, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel h1, ← map_pow, hpow]
  -- Reduce `y` modulo `([ϖ])` to an element `b ∈ R° ⧸ (ϖ)`: then `r n ^ (p ^ n - 1) ∣ b` in `R°`.
  let e := hξ.isDistinguished.quotientTeichmullerEquiv ((dvd_pow_self _ hp.out.ne_zero).trans hξ₀)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e (Ideal.Quotient.mk _ y))
  have hb_dvd (n : ℕ) : r n ^ (p ^ n - 1) ∣ b := by
    obtain ⟨z, hz⟩ := hy_dvd n
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (e (Ideal.Quotient.mk _ z))
    have hmod : Ideal.Quotient.mk (Ideal.span {ϖ}) b =
        Ideal.Quotient.mk (Ideal.span {ϖ}) (r n ^ (p ^ n - 1) * c) := by
      rw [hb, hz, map_mul, map_pow, map_mul, map_pow, ← hc]
      have hwn : e (Ideal.Quotient.mk _ (w n)) = Ideal.Quotient.mk (Ideal.span {ϖ}) (r n) := by
        simp [e, w]
      rw [hwn, ← map_pow, ← map_mul]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hmod
    have hr_dvd_ϖ : r n ^ (p ^ n - 1) ∣ ϖ := by
      refine ⟨r n, ?_⟩
      have h1 : 1 ≤ p ^ n := Nat.one_le_pow n p hp.out.pos
      rw [← pow_succ, Nat.sub_add_cancel h1]
      exact (iterate_frobeniusEquiv_symm_pow ϖ n).symm
    have hsub := hr_dvd_ϖ.trans hmod
    have hadd := dvd_add hsub (dvd_mul_right (r n ^ (p ^ n - 1)) c)
    rwa [sub_add_cancel] at hadd
  -- Hence `t := ϖ⁻¹ * b` satisfies `r n * t ∈ R°` for all `n`, so `t` is power-bounded, i.e.
  -- `ϖ ∣ b` in `R°`.
  obtain ⟨u, hu⟩ := hϖ.isUnit
  let t : R := (↑u⁻¹ : R) * (b : R)
  have hrt (n : ℕ) : (r n : R) * t ∈ powerBoundedSubring R := by
    obtain ⟨d, hd⟩ := hb_dvd n
    have h1 : 1 ≤ p ^ n := Nat.one_le_pow n p hp.out.pos
    have hmul : (r n : R) * (b : R) = (ϖ : R) * (d : R) := by
      have h' : r n * b = ϖ * d := by
        rw [hd, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel h1, iterate_frobeniusEquiv_symm_pow]
      simpa only [Subring.coe_mul] using congrArg Subtype.val h'
    have heq : (r n : R) * t = (d : R) := by
      rw [show (r n : R) * t = (↑u⁻¹ : R) * ((r n : R) * (b : R)) by simp only [t]; ring,
        hmul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [heq]
    exact Pair.powerBounded_plus (A := R) ▸ d.2
  have ht_pb : t ∈ powerBoundedSubring R := by
    refine mem_powerBoundedSubring.mpr (isPowerBounded_iff.mpr ?_)
    refine ((isBounded_singleton (↑u⁻¹ : R)).mul IsUniform.isBounded_powerBoundedSubring).subset ?_
    rintro _ ⟨k, rfl⟩
    have hle : k ≤ p ^ k := (Nat.lt_pow_self hp.out.one_lt).le
    have hϖt : (ϖ : R) * t ^ k ∈ powerBoundedSubring R := by
      have hsplit : (ϖ : R) = (r k : R) ^ (p ^ k - k) * (r k : R) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hle, ← Subring.coe_pow, iterate_frobeniusEquiv_symm_pow]
      rw [hsplit, mul_assoc, ← mul_pow]
      exact mul_mem (pow_mem (Pair.powerBounded_plus (A := R) ▸ (r k).2) _) (pow_mem (hrt k) k)
    exact Set.mem_mul.mpr ⟨↑u⁻¹, Set.mem_singleton _, (ϖ : R) * t ^ k, hϖt, by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]⟩
  have hb_zero : Ideal.Quotient.mk (Ideal.span {ϖ}) b = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    refine ⟨⟨t, (Pair.powerBounded_plus (A := R)).symm ▸ ht_pb⟩, Subtype.ext ?_⟩
    simp only [Subring.coe_mul, t, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  have hy_zero :
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ)}) y =
        0 :=
    e.injective (by rw [map_zero, ← hb, hb_zero])
  obtain ⟨y', hy'⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hy_zero)
  refine mem_untiltPlus.mpr ⟨y', ?_⟩
  apply (isPseudoUniformizer_algebraMap (J := Ideal.span {ξ}) hϖ).isUnit.mul_left_cancel
  calc algebraMap _ _ (w 0) * algebraMap _ _ y'
    _ = algebraMap _ _ y := by rw [← map_mul]; exact congrArg _ hy'.symm
    _ = algebraMap _ _ (w 0) * x := hy

private theorem le_powerBounded_plus (P : Pair R) :
    P.plus ≤ (Pair.powerBounded R).plus := by
  rw [Pair.powerBounded_plus]
  exact P.isRingOfIntegralElements.le_powerBoundedSubring

/-- Multiplication by `[ϖ]` sends `𝕎 R°` into `𝕎 R⁺` for any pseudouniformiser `ϖ ∈ R⁺`. -/
private theorem exists_map_eq_teichmuller_mul_of_isPseudoUniformizer {ϖ : P.plus}
    (hϖ : IsPseudoUniformizer (ϖ : R)) (x : 𝕎 (Pair.powerBounded R).plus) :
    ∃ y : 𝕎 P.plus,
      WittVector.map (Subring.inclusion (le_powerBounded_plus P)) y =
        teichmuller p (Subring.inclusion (le_powerBounded_plus P) ϖ) * x := by
  let inc : P.plus →+* (Pair.powerBounded R).plus := Subring.inclusion (le_powerBounded_plus P)
  have hmem (n : ℕ) : ((teichmuller p (inc ϖ) * x).coeff n : R) ∈ P.plus := by
    have hcoeff : ((teichmuller p (inc ϖ) * x).coeff n : R) =
        (ϖ : R) ^ p ^ n * (x.coeff n : R) := by
      have h1 := WittVector.teichmullerCoeff_pow (teichmuller p (inc ϖ) * x) n
      rw [WittVector.teichmullerCoeff_teichmuller_mul, mul_pow,
        WittVector.teichmullerCoeff_pow] at h1
      simpa only [Subring.coe_mul, Subring.coe_pow, inc, Subring.coe_inclusion] using
        congrArg Subtype.val h1.symm
    rw [hcoeff, mul_comm]
    have hxpb : IsPowerBounded (x.coeff n : R) :=
      mem_powerBoundedSubring.mp (Pair.powerBounded_plus (A := R) ▸ (x.coeff n).2)
    exact P.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
      (hxpb.isTopologicallyNilpotent_mul
        (hϖ.isTopologicallyNilpotent.pow (pow_ne_zero n hp.out.ne_zero)))
  refine ⟨WittVector.mk p fun n ↦ ⟨((teichmuller p (inc ϖ) * x).coeff n : R), hmem n⟩, ?_⟩
  ext n
  simp [WittVector.map_coeff, inc]

/-- The untilt map induced by `(R, R⁺) → (R, R°)` is injective, since `[ϖ] · 𝕎 R° ⊆ 𝕎 R⁺`. -/
private theorem map_inclusion_powerBounded_injective (hξ : ξ.IsPrimitive)
    (ι : Pair.Hom P (Pair.powerBounded R)) (hι : ι.toRingHom = RingHom.id R)
    (hJ : (Ideal.span {ξ}).map
      (WittVector.map (ι.toRingHom.restrict P.plus (Pair.powerBounded R).plus ι.map_mem_plus)) ≤
        Ideal.span {WittVector.map (Subring.inclusion (le_powerBounded_plus P)) ξ}) :
    Function.Injective (map ι hJ) := by
  let Q := Pair.powerBounded R
  let inc : P.plus →+* Q.plus := Subring.inclusion (le_powerBounded_plus P)
  have hinc_eq : ι.toRingHom.restrict P.plus Q.plus ι.map_mem_plus = inc := by
    ext x
    exact congrArg (fun φ : R →+* R ↦ φ (x : R)) hι
  have hW_inj : Function.Injective (WittVector.map inc) := fun _ _ h ↦
    WittVector.ext fun n ↦ Subring.inclusion_injective (le_powerBounded_plus P) (by
      simpa only [WittVector.map_coeff] using congrArg (fun v : 𝕎 Q.plus ↦ v.coeff n) h)
  have hξ' : (WittVector.map inc ξ).IsPrimitive := hξ.map (continuous_subtype_val.subtype_mk _)
  obtain ⟨ϖ, hϖ, -⟩ := exists_isPseudoUniformizer_pow_dvd_coeff_zero hξ
  rw [injective_iff_map_eq_zero]
  intro a ha
  have := isLocalizationAway (J := Ideal.span {ξ}) hϖ
  obtain ⟨k, y, hy⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ)) a
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hfw : map ι hJ (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {ξ}) w)) = 0 := by
    rw [← hy, map_mul, ha, zero_mul]
  rw [map_algebraMap, hinc_eq] at hfw
  have hmk0 : Ideal.Quotient.mk (Ideal.span {WittVector.map inc ξ}) (WittVector.map inc w) = 0 :=
    algebraMap_injective hξ' (hfw.trans (map_zero _).symm)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hmk0)
  obtain ⟨v', hv'⟩ := exists_map_eq_teichmuller_mul_of_isPseudoUniformizer hϖ v
  have hrel : teichmuller p ϖ * w = ξ * v' := hW_inj <| by
    rw [map_mul, map_mul, WittVector.map_teichmuller, hv, hv']
    ring
  have hzero : algebraMap (𝕎 P.plus ⧸ Ideal.span {ξ}) (untilt p P (Ideal.span {ξ}))
      (Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ)) *
      (a * algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ)) ^ k) = 0 := by
    rw [hy, ← map_mul, ← map_mul, hrel,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right ξ v')),
      map_zero]
  have hu1 := (isPseudoUniformizer_algebraMap (J := Ideal.span {ξ}) hϖ).isUnit
  have hu2 := hu1.pow k
  have hzero' : a * algebraMap (𝕎 P.plus ⧸ Ideal.span {ξ}) (untilt p P (Ideal.span {ξ}))
      (Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ)) ^ k = 0 :=
    hu1.mul_left_cancel (hzero.trans (mul_zero _).symm)
  exact hu2.mul_right_cancel (hzero'.trans (zero_mul _).symm)

/-- **Integral closedness of `untiltPlus`**: for any Huber pair `P = (R, R⁺)` on a uniform perfect
Tate ring `R` of characteristic `p` and primitive `ξ ∈ 𝕎 R⁺`, `untiltPlus p P (span {ξ})` is
integrally closed in `untilt p P (span {ξ})`. -/
theorem isIntegrallyClosedIn_untiltPlus [IsUniform R] (hξ : ξ.IsPrimitive) :
    IsIntegrallyClosedIn (untiltPlus p P (Ideal.span {ξ}))
      (untilt p P (Ideal.span {ξ})) := by
  classical
  let Q := Pair.powerBounded R
  let ι : Pair.Hom P Q :=
    { toRingHom := RingHom.id R
      continuous_toRingHom := continuous_id
      map_mem_plus := fun _ hx ↦ le_powerBounded_plus P hx }
  let inc : P.plus →+* Q.plus := Subring.inclusion (le_powerBounded_plus P)
  have hinc_eq : ι.toRingHom.restrict P.plus Q.plus ι.map_mem_plus = inc := by
    ext x
    rfl
  let ξ' : 𝕎 Q.plus := WittVector.map inc ξ
  have hξ' : ξ'.IsPrimitive := hξ.map (continuous_subtype_val.subtype_mk _)
  have hJ : (Ideal.span {ξ}).map
      (WittVector.map (ι.toRingHom.restrict P.plus Q.plus ι.map_mem_plus)) ≤ Ideal.span {ξ'} := by
    rw [Ideal.map_span, Set.image_singleton, hinc_eq]
  let f : untilt p P (Ideal.span {ξ}) →+* untilt p Q (Ideal.span {ξ'}) := map ι hJ
  obtain ⟨ϖ, hϖ, hξ₀⟩ := exists_isPseudoUniformizer_pow_dvd_coeff_zero hξ
  have hf_inj : Function.Injective f := map_inclusion_powerBounded_injective hξ ι rfl hJ
  -- Test integral closedness using `Subring.isIntegrallyClosedIn_map_of_ker_le` modulo `ϖ`.
  refine Subring.isIntegrallyClosedIn_iff.mpr fun x hx ↦ ?_
  have hx_pb : x ∈ powerBoundedSubring (untilt p P (Ideal.span {ξ})) :=
    mem_powerBoundedSubring.mpr <| isPowerBounded_of_isIntegral <|
      RingHom.IsIntegralElem.of_comp (f := (untiltPlus p P (Ideal.span {ξ})).inclusion
        untiltPlus_le_powerBoundedSubring) hx
  have hfx_pb : f x ∈ powerBoundedSubring (untilt p Q (Ideal.span {ξ'})) :=
    mem_powerBoundedSubring.mpr
      ((mem_powerBoundedSubring.mp hx_pb).map_of_isTateRing (continuous_map ι hJ).continuousAt)
  have hfx_plus : f x ∈ untiltPlus p Q (Ideal.span {ξ'}) :=
    (untiltPlus_eq_powerBoundedSubring hξ').symm ▸ hfx_pb
  obtain ⟨yQ, hyQ⟩ := mem_untiltPlus.mp hfx_plus
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective yQ
  -- Descend integrality of `w.coeff 0` to `R° ⧸ (ϖ)` to deduce `(w.coeff 0 : R) ∈ R⁺`.
  let D : Subring Q.plus := P.plus.comap Q.plus.subtype
  have hD_ic : IsIntegrallyClosedIn D Q.plus := Subring.isIntegrallyClosedIn_iff.mpr fun z hz ↦ by
    let j : D →+* P.plus := Q.plus.subtype.restrict D P.plus fun _ h ↦ h
    have hzR : IsIntegral P.plus (z : R) := hz.map_of_comp_eq j Q.plus.subtype (by ext y; rfl)
    exact Subring.isIntegrallyClosedIn_iff.mp P.isRingOfIntegralElements.isIntegrallyClosedIn hzR
  let qMod : Q.plus →+* Q.plus ⧸ Ideal.span {inc ϖ} := Ideal.Quotient.mk _
  have hker : (RingHom.ker qMod : Set Q.plus) ⊆ D := by
    intro b hb
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hb)
    have hbc : (b : R) = (ϖ : R) * (c : R) := by
      simpa only [Subring.coe_mul, inc, Subring.coe_inclusion] using congrArg Subtype.val hc
    simp only [SetLike.mem_coe, D, Subring.mem_comap, Subring.coe_subtype, hbc]
    rw [mul_comm]
    have hc_pb : IsPowerBounded (c : R) :=
      mem_powerBoundedSubring.mp (Pair.powerBounded_plus (A := R) ▸ c.2)
    exact P.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
      (hc_pb.isTopologicallyNilpotent_mul hϖ.isTopologicallyNilpotent)
  have hD_map : IsIntegrallyClosedIn (D.map qMod) (Q.plus ⧸ Ideal.span {inc ϖ}) :=
    D.isIntegrallyClosedIn_map_of_ker_le qMod Ideal.Quotient.mk_surjective hker
  have hξ'₀ : inc ϖ ∣ ξ'.coeff 0 := by
    rw [show ξ'.coeff 0 = inc (ξ.coeff 0) from WittVector.map_coeff inc ξ 0]
    exact map_dvd inc ((dvd_pow_self _ hp.out.ne_zero).trans hξ₀)
  let f_plus : untiltPlus p P (Ideal.span {ξ}) →+* untiltPlus p Q (Ideal.span {ξ'}) :=
    f.restrict _ _ fun _ ha ↦ map_mem_untiltPlus ι hJ ha
  let ψ : untiltPlus p Q (Ideal.span {ξ'}) →+* Q.plus ⧸ Ideal.span {inc ϖ} :=
    (quotEquiv hξ' hξ'₀).toRingHom.comp (Ideal.Quotient.mk _)
  let g : untiltPlus p P (Ideal.span {ξ}) →+* D.map qMod :=
    (ψ.comp f_plus).codRestrict (D.map qMod) fun a ↦ by
      obtain ⟨ya, hya⟩ := mem_untiltPlus.mp a.2
      obtain ⟨va, rfl⟩ := Ideal.Quotient.mk_surjective ya
      refine ⟨inc (va.coeff 0), (va.coeff 0).2, ?_⟩
      have ha_eq : f_plus a = ⟨algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {ξ'})
          (WittVector.map inc va)), mem_untiltPlus.mpr ⟨_, rfl⟩⟩ :=
        Subtype.ext (by
          rw [show (f_plus a : untilt p Q (Ideal.span {ξ'})) = f a from rfl, ← hya,
            show f = map ι hJ from rfl, map_algebraMap, hinc_eq])
      simp only [RingHom.comp_apply, ha_eq, ψ, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        quotEquiv_mk_algebraMap, WittVector.map_coeff, qMod]
  have hfx_int : f_plus.IsIntegralElem ⟨f x, hfx_plus⟩ := by
    obtain ⟨q, hqm, hq0⟩ := hx
    refine ⟨q, hqm, (untiltPlus p Q (Ideal.span {ξ'})).subtype_injective ?_⟩
    have hcomp : (untiltPlus p Q (Ideal.span {ξ'})).subtype.comp f_plus =
        f.comp (algebraMap (untiltPlus p P (Ideal.span {ξ})) (untilt p P (Ideal.span {ξ}))) := rfl
    rw [map_zero, Polynomial.hom_eval₂, hcomp, Subring.coe_subtype, ← Polynomial.hom_eval₂, hq0,
      map_zero]
  have hw0_int : IsIntegral (D.map qMod) (ψ ⟨f x, hfx_plus⟩) :=
    RingHom.IsIntegralElem.of_comp (f := g) (hfx_int.map ψ)
  have hw0_map : qMod (w.coeff 0) ∈ D.map qMod := by
    have hψ : ψ ⟨f x, hfx_plus⟩ = qMod (w.coeff 0) := by
      have hfx_eq : (⟨f x, hfx_plus⟩ : untiltPlus p Q (Ideal.span {ξ'})) =
          ⟨algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {ξ'}) w), mem_untiltPlus.mpr ⟨_, rfl⟩⟩ :=
        Subtype.ext hyQ.symm
      rw [hfx_eq]
      exact quotEquiv_mk_algebraMap hξ' hξ'₀ w
    rw [← hψ]
    exact Subring.isIntegrallyClosedIn_iff.mp hD_map hw0_int
  have hw0_mem : (w.coeff 0 : R) ∈ P.plus := by
    have hmemD : w.coeff 0 ∈ D := by
      rw [← Subring.comap_map_eq_self hker]
      exact hw0_map
    exact hmemD
  -- Step 3: write `w = [w₀] + p * b`; modulo `ξ'`, `p * b` is a multiple of `[ϖ]` and pulls back
  -- into `𝕎 R⁺`.
  obtain ⟨b, hb⟩ := WittVector.exists_eq_sum_teichmullerCoeff_add_pow_mul w 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, pow_one,
    WittVector.teichmullerCoeff_zero] at hb
  obtain ⟨u, hu⟩ := WittVector.isDistinguished_iff_exists_unit.mp hξ.isDistinguished
  obtain ⟨d, hd⟩ := (dvd_pow_self ϖ hp.out.ne_zero).trans hξ₀
  obtain ⟨y, hy⟩ := exists_map_eq_teichmuller_mul_of_isPseudoUniformizer hϖ
    (teichmuller p (inc d) * b)
  let a₀ : P.plus := ⟨(w.coeff 0 : R), hw0_mem⟩
  let v : 𝕎 P.plus := teichmuller p a₀ - u.inv * y
  have hv_mod : Ideal.Quotient.mk (Ideal.span {ξ'}) (WittVector.map inc v) =
      Ideal.Quotient.mk (Ideal.span {ξ'}) w := by
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨-WittVector.map inc u.inv * b, ?_⟩
    have hξ'_eq : ξ' = teichmuller p (inc ϖ) * teichmuller p (inc d) +
        (p : 𝕎 Q.plus) * WittVector.map inc u.val := by
      have h := congrArg (WittVector.map inc) hu
      rw [map_add, map_mul, map_natCast, WittVector.map_teichmuller, hd, map_mul, map_mul] at h
      exact h
    have hu_inv : WittVector.map inc u.inv * WittVector.map inc u.val = 1 := by
      rw [← map_mul, u.inv_val, map_one]
    have ha₀ : inc a₀ = w.coeff 0 := Subtype.ext rfl
    have hv_map : WittVector.map inc v = teichmuller p (w.coeff 0) -
        WittVector.map inc u.inv * (teichmuller p (inc ϖ) * (teichmuller p (inc d) * b)) := by
      simp only [v, map_sub, map_mul, WittVector.map_teichmuller, ha₀]
      rw [show inc = Subring.inclusion (le_powerBounded_plus P) from rfl, hy]
    calc WittVector.map inc v - w
      _ = (teichmuller p (w.coeff 0) -
            WittVector.map inc u.inv * (teichmuller p (inc ϖ) * (teichmuller p (inc d) * b))) -
          (teichmuller p (w.coeff 0) + (p : 𝕎 Q.plus) * b) := by
          rw [hv_map]
          exact congrArg (_ - ·) hb
      _ = ξ' * (-WittVector.map inc u.inv * b) := by
          rw [hξ'_eq]
          linear_combination p * b * hu_inv
  refine mem_untiltPlus.mpr ⟨Ideal.Quotient.mk (Ideal.span {ξ}) v, hf_inj ?_⟩
  rw [show f = map ι hJ from rfl, map_algebraMap, hinc_eq, hv_mod, hyQ]

/-- **The subring `untiltPlus` is a ring of integral elements** for a primitive element `ξ` over a
uniform perfect Tate ring of characteristic `p`. -/
theorem isRingOfIntegralElements_untiltPlus [IsUniform R] (hξ : ξ.IsPrimitive) :
    IsRingOfIntegralElements (untiltPlus p P (Ideal.span {ξ})) where
  isOpen := isOpen_untiltPlus
  isIntegrallyClosedIn := isIntegrallyClosedIn_untiltPlus hξ
  le_powerBoundedSubring := untiltPlus_le_powerBoundedSubring

/-- **The untilt Huber pair `(A, A⁺)`** along a primitive element `ξ`. -/
noncomputable def pair [IsUniform R] (hξ : ξ.IsPrimitive) :
    Pair (untilt p P (Ideal.span {ξ})) where
  plus := untiltPlus p P (Ideal.span {ξ})
  isRingOfIntegralElements := isRingOfIntegralElements_untiltPlus hξ

@[simp]
theorem pair_plus [IsUniform R] (hξ : ξ.IsPrimitive) :
    (pair hξ).plus = untiltPlus p P (Ideal.span {ξ}) := by
  rfl

/-- **`A° / A⁺` is almost zero** for the almost setup `(A⁺, A°°)` of the untilt along a primitive
element. -/
theorem isAlmostZero_powerBounded_quotient [IsUniform R] (hξ : ξ.IsPrimitive)
    [Algebra (untiltPlus p P (Ideal.span {ξ}))
      (powerBoundedSubring (untilt p P (Ideal.span {ξ})))]
    [IsScalarTower (untiltPlus p P (Ideal.span {ξ}))
      (powerBoundedSubring (untilt p P (Ideal.span {ξ})))
      (untilt p P (Ideal.span {ξ}))] :
    letI : Fact (1 < p) := ⟨hp.out.one_lt⟩
    letI : Nonempty (PseudoUniformizerRoots p (untilt p P (Ideal.span {ξ}))) :=
      nonempty_pseudoUniformizerRoots hξ
    (almostSetupPlus p (untilt p P (Ideal.span {ξ}))
      (isRingOfIntegralElements_untiltPlus hξ)).IsAlmostZero
      (powerBoundedSubring (untilt p P (Ideal.span {ξ})) ⧸
        LinearMap.range (Algebra.linearMap (untiltPlus p P (Ideal.span {ξ}))
          (powerBoundedSubring (untilt p P (Ideal.span {ξ}))))) := by
  have : Fact (1 < p) := ⟨hp.out.one_lt⟩
  have : Nonempty (PseudoUniformizerRoots p (untilt p P (Ideal.span {ξ}))) :=
    nonempty_pseudoUniformizerRoots hξ
  exact almostSetupPlus_isAlmostZero_powerBounded_quotient (isRingOfIntegralElements_untiltPlus hξ)

/-- **The inclusion `A⁺ → A°` is an almost isomorphism** for the almost setup `(A⁺, A°°)`. -/
theorem isAlmostIso_algebraLinearMap [IsUniform R] (hξ : ξ.IsPrimitive)
    [Algebra (untiltPlus p P (Ideal.span {ξ}))
      (powerBoundedSubring (untilt p P (Ideal.span {ξ})))]
    [IsScalarTower (untiltPlus p P (Ideal.span {ξ}))
      (powerBoundedSubring (untilt p P (Ideal.span {ξ})))
      (untilt p P (Ideal.span {ξ}))] :
    letI : Fact (1 < p) := ⟨hp.out.one_lt⟩
    letI : Nonempty (PseudoUniformizerRoots p (untilt p P (Ideal.span {ξ}))) :=
      nonempty_pseudoUniformizerRoots hξ
    (almostSetupPlus p (untilt p P (Ideal.span {ξ}))
      (isRingOfIntegralElements_untiltPlus hξ)).IsAlmostIso
      (Algebra.linearMap (untiltPlus p P (Ideal.span {ξ}))
        (powerBoundedSubring (untilt p P (Ideal.span {ξ})))) := by
  have : Fact (1 < p) := ⟨hp.out.one_lt⟩
  have : Nonempty (PseudoUniformizerRoots p (untilt p P (Ideal.span {ξ}))) :=
    nonempty_pseudoUniformizerRoots hξ
  exact almostSetupPlus_isAlmostIso_algebraLinearMap (isRingOfIntegralElements_untiltPlus hξ)

/-- The uniform tilt of any untilt is a Tate ring. -/
theorem isTateRing_uniformTilt (J : Ideal (WittVector p P.plus))
    [CompleteSpace (untilt p P J)] [T2Space (untilt p P J)]
    [IsUniform (untilt p P J)] [Fact (IsTopologicallyNilpotent (p : untilt p P J))] :
    IsTateRing (uniformTilt p (untilt p P J)) := by
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  let ϖ_tilt : uniformTilt p (untilt p P J) :=
    uniformTilt.mk (fun n ↦ sharp p P J ((frobeniusEquiv R p).symm^[n] (ϖ : R)))
      fun n ↦ by rw [← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  exact uniformTilt.isTateRing_of_sharp (ϖ := ϖ_tilt) (by
    simpa [ϖ_tilt] using isPseudoUniformizer_sharp (J := J) hϖ)

end PrimitiveTate

private theorem isAdicComplete_map_constantCoeff [UniformSpace R] [IsUniformAddGroup R]
    [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R] [IsUniform R]
    {P : Pair R} {ξ : WittVector p P.plus} (hξ : ξ.IsPrimitive) :
    IsAdicComplete ((Ideal.span {ξ}).map constantCoeff) P.plus := by
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  have := P.isRingOfIntegralElements.isAdicComplete_span_singleton ϖ hϖ
  have hrad : ξ.coeff 0 ∈ (Ideal.span {ϖ}).radical := by
    obtain ⟨n, hn⟩ := P.plus.exists_dvd_pow_of_isTopologicallyNilpotent
      P.isRingOfIntegralElements.isOpen hϖ.isUnit
      (hξ.isTopologicallyNilpotent_coeff_zero.map (φ := P.plus.subtype) continuous_subtype_val)
    exact ⟨n, Ideal.mem_span_singleton.mpr hn⟩
  have hI_eq : (Ideal.span {ξ}).map constantCoeff = Ideal.span {ξ.coeff 0} := by
    simp [Ideal.map_span]
  exact hI_eq ▸ isAdicComplete_span_singleton_of_mem_radical hrad

section PerfectoidAndTilt

variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R]
  [CompleteSpace R] [T2Space R] [CharP R p] [PerfectRing R p]
  {P : Pair R} {ξ : WittVector p P.plus}

/-- **The untilt along a primitive element is a perfectoid Tate ring** (Scholze, *Étale cohomology
of diamonds*, Theorem 3.17; Bhatt–Morrow–Scholze, Lemma 3.21). -/
theorem isPerfectoidTateRing (hξ : ξ.IsPrimitive) :
    letI := completeSpace hξ
    letI := t2Space hξ
    IsPerfectoidTateRing p (untilt p P (Ideal.span {ξ})) := by
  have := IsUniform.of_perfectRing (R := R) p
  have := completeSpace hξ
  have := t2Space hξ
  obtain ⟨ϖ, hϖ, hξ₀⟩ := exists_isPseudoUniformizer_pow_dvd_coeff_zero hξ
  have := isLocalizationAway (J := Ideal.span {ξ}) hϖ
  have := P.isRingOfIntegralElements.isAdicComplete_span_singleton ϖ hϖ
  have hϖ_dvd : ϖ ∣ ξ.coeff 0 := (dvd_pow_self _ hp.out.ne_zero).trans hξ₀
  have hrad : ξ.coeff 0 ∈ (Ideal.span {ϖ}).radical :=
    ⟨1, by rw [pow_one]; exact Ideal.mem_span_singleton.mpr hϖ_dvd⟩
  have := hξ.isDistinguished.isAdicComplete_quotient hrad
  have hπ := mk_teichmuller_mem_nonZeroDivisors_of_dvd hξ hϖ hϖ_dvd
  exact isPerfectoidTateRing_of_hasBasis (hasBasis_nhds_zero hϖ) hπ
    (hξ.isDistinguished.pow_prime_dvd_natCast_quotient hξ₀)
    (hξ.isDistinguished.frobeniusModPow_bijective_quotient hξ₀)

section Tilt

variable [IsUniform R]
  [CompleteSpace (untilt p P (Ideal.span {ξ}))]
  [T2Space (untilt p P (Ideal.span {ξ}))]
  [IsUniform (untilt p P (Ideal.span {ξ}))]
  [Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ})))]

open Classical in
/-- **Identification of the integral tilt**: `A♭⁺ ≃+* R⁺` for the untilt along a primitive
element `ξ`. -/
noncomputable def tiltEquivPlus (hξ : ξ.IsPrimitive) :
    uniformTilt.plusSubring p (isRingOfIntegralElements_untiltPlus hξ) ≃+* P.plus :=
  if hR : Subsingleton R then
    have : Subsingleton (untilt p P (Ideal.span {ξ})) := subsingleton_of_subsingleton
    { toFun := fun _ ↦ 0
      invFun := fun _ ↦ 0
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _
      map_mul' := fun _ _ ↦ Subsingleton.elim _ _
      map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
  else
    have : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
    have : Nontrivial (untilt p P (Ideal.span {ξ})) := nontrivial hξ
    let hA := isRingOfIntegralElements_untiltPlus hξ
    have hpuA : Fact (¬IsUnit (p : untiltPlus p P (Ideal.span {ξ}))) :=
      ⟨hA.not_isUnit_natCast_of_isTopologicallyNilpotent p Fact.out⟩
    have : Fact (¬IsUnit (p : 𝕎 P.plus ⧸ Ideal.span {ξ})) :=
      ⟨fun hu ↦ hpuA.out (by simpa using hu.map (quotientEquivUntiltPlus hξ))⟩
    have := isAdicComplete_map_constantCoeff hξ
    (uniformTilt.plusEquivPreTilt p hA).trans
      ((preTiltRingEquiv (quotientEquivUntiltPlus hξ).symm).trans
        (Ideal.span {ξ}).wittVectorQuotientPreTiltEquiv)

/-- The inverse of `tiltEquivPlus` has zeroth coordinate `sharp a`. -/
private theorem coeff_zero_tiltEquivPlus_symm (hξ : ξ.IsPrimitive) (a : P.plus) :
    uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) 0
      ((tiltEquivPlus hξ).symm a : uniformTilt p (untilt p P (Ideal.span {ξ}))) =
      sharp p P (Ideal.span {ξ}) (a : R) := by
  classical
  by_cases hR : Subsingleton R
  · have : Subsingleton (untilt p P (Ideal.span {ξ})) := subsingleton_of_subsingleton
    exact Subsingleton.elim _ _
  · have : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
    have : Nontrivial (untilt p P (Ideal.span {ξ})) := nontrivial hξ
    let hA := isRingOfIntegralElements_untiltPlus hξ
    have hpuA : Fact (¬IsUnit (p : untiltPlus p P (Ideal.span {ξ}))) :=
      ⟨hA.not_isUnit_natCast_of_isTopologicallyNilpotent p Fact.out⟩
    have : Fact (¬IsUnit (p : 𝕎 P.plus ⧸ Ideal.span {ξ})) :=
      ⟨fun hu ↦ hpuA.out (by simpa using hu.map (quotientEquivUntiltPlus hξ))⟩
    have := hA.isAdicComplete_span_natCast p Fact.out
    have := isAdicComplete_map_constantCoeff hξ
    obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
    have := P.isRingOfIntegralElements.isAdicComplete_span_singleton ϖ hϖ
    have hrad : ξ.coeff 0 ∈ (Ideal.span {ϖ}).radical := by
      obtain ⟨n, hn⟩ := P.plus.exists_dvd_pow_of_isTopologicallyNilpotent
        P.isRingOfIntegralElements.isOpen hϖ.isUnit
        (hξ.isTopologicallyNilpotent_coeff_zero.map (φ := P.plus.subtype) continuous_subtype_val)
      exact ⟨n, Ideal.mem_span_singleton.mpr hn⟩
    have := hξ.isDistinguished.isAdicComplete_quotient_natCast hrad
    have hsymm : (tiltEquivPlus hξ).symm a =
        (uniformTilt.plusEquivPreTilt p hA).symm
          ((preTiltRingEquiv (quotientEquivUntiltPlus hξ).symm).symm
            ((Ideal.span {ξ}).wittVectorQuotientPreTiltEquiv.symm a)) := by
      unfold tiltEquivPlus
      rw [dite_eq_right fun h ↦ (hR h).elim]
      simp only [RingEquiv.symm_trans_apply]
    rw [hsymm, ← uniformTilt.coe_plusSharp, uniformTilt.plusSharp_plusEquivPreTilt_symm]
    have hpre : ((preTiltRingEquiv (quotientEquivUntiltPlus hξ).symm).symm
        ((Ideal.span {ξ}).wittVectorQuotientPreTiltEquiv.symm a)).untilt =
        quotientEquivUntiltPlus hξ
          (((Ideal.span {ξ}).wittVectorQuotientPreTiltEquiv.symm a).untilt) := by
      have h := untilt_preTiltRingEquiv (quotientEquivUntiltPlus hξ).symm
        ((preTiltRingEquiv (quotientEquivUntiltPlus hξ).symm).symm
          ((Ideal.span {ξ}).wittVectorQuotientPreTiltEquiv.symm a))
      rw [RingEquiv.apply_symm_apply] at h
      exact (quotientEquivUntiltPlus hξ).symm.injective (by
        rw [RingEquiv.symm_apply_apply, h])
    rw [hpre, Ideal.untilt_wittVectorQuotientPreTiltEquiv_symm, coe_quotientEquivUntiltPlus,
      sharp_coe]

/-- The `n`-th coordinate of `(tiltEquivPlus hξ).symm a` is `sharp (a ^ (1 / p ^ n))`. -/
@[simp]
theorem coeff_tiltEquivPlus_symm (hξ : ξ.IsPrimitive) (a : P.plus) (n : ℕ) :
    uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n
      ((tiltEquivPlus hξ).symm a : uniformTilt p (untilt p P (Ideal.span {ξ}))) =
      sharp p P (Ideal.span {ξ}) (((frobeniusEquiv P.plus p).symm^[n] a : P.plus) : R) := by
  let y := (tiltEquivPlus hξ).symm ((frobeniusEquiv P.plus p).symm^[n] a)
  have hy_pow : y ^ p ^ n = (tiltEquivPlus hξ).symm a := by
    rw [← map_pow, iterate_frobeniusEquiv_symm_pow]
  have hy_pow' : (y : uniformTilt p (untilt p P (Ideal.span {ξ}))) ^ p ^ n =
      ((tiltEquivPlus hξ).symm a : uniformTilt p (untilt p P (Ideal.span {ξ}))) := by
    rw [← Subring.coe_pow, hy_pow]
  rw [← hy_pow', map_pow]
  simpa only [zero_add] using
    (uniformTilt.coeff_pow_p_pow (n := 0) (m := n)
      (y : uniformTilt p (untilt p P (Ideal.span {ξ})))).trans
      (coeff_zero_tiltEquivPlus_symm hξ _)

/-- The inverse of `tiltEquivPlus` carries pseudouniformisers of `R` in `R⁺` to pseudouniformisers
of the tilt of the untilt. -/
theorem isPseudoUniformizer_tiltEquivPlus_symm (hξ : ξ.IsPrimitive) {ϖ : P.plus}
    (hϖ : IsPseudoUniformizer (ϖ : R)) :
    IsPseudoUniformizer
      ((tiltEquivPlus hξ).symm ϖ : uniformTilt p (untilt p P (Ideal.span {ξ}))) := by
  have h0 : IsPseudoUniformizer
      (uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) 0 ((tiltEquivPlus hξ).symm ϖ : _)) := by
    rw [coeff_zero_tiltEquivPlus_symm]
    exact isPseudoUniformizer_sharp (J := Ideal.span {ξ}) hϖ
  exact isPseudoUniformizer_iff.mpr
    ⟨uniformTilt.isUnit_iff_coeff_zero.mpr h0.isUnit,
      uniformTilt.isTopologicallyNilpotent_iff_coeff_zero.mpr h0.isTopologicallyNilpotent⟩

/-- **Tilting identification of the untilt**: `uniformTilt p (untilt p P (span {ξ})) ≃+* R`. -/
noncomputable def tiltEquiv (hξ : ξ.IsPrimitive) :
    uniformTilt p (untilt p P (Ideal.span {ξ})) ≃+* R :=
  let hA := isRingOfIntegralElements_untiltPlus hξ
  let ϖ := P.isRingOfIntegralElements.exists_isPseudoUniformizer.choose
  let hϖ := P.isRingOfIntegralElements.exists_isPseudoUniformizer.choose_spec
  let ϖ_tilt := (tiltEquivPlus hξ).symm ϖ
  have hϖ_tilt := isPseudoUniformizer_tiltEquivPlus_symm hξ hϖ
  letI := Subring.isLocalizationAway_of_isOpen (uniformTilt.plusSubring p hA)
    (uniformTilt.isOpen_plusSubring hA) ϖ_tilt hϖ_tilt.isTopologicallyNilpotent hϖ_tilt.isUnit
  letI := Subring.isLocalizationAway_of_isOpen P.plus P.isRingOfIntegralElements.isOpen ϖ
    hϖ.isTopologicallyNilpotent hϖ.isUnit
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers ϖ_tilt) (T := Submonoid.powers ϖ)
    (uniformTilt p (untilt p P (Ideal.span {ξ}))) R (tiltEquivPlus hξ) (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers ((tiltEquivPlus hξ).apply_symm_apply ϖ))

/-- `tiltEquiv` restricts to `tiltEquivPlus` on `A♭⁺`. -/
@[simp]
theorem tiltEquiv_coe (hξ : ξ.IsPrimitive)
    (x : uniformTilt.plusSubring p (isRingOfIntegralElements_untiltPlus hξ)) :
    tiltEquiv hξ (x : uniformTilt p (untilt p P (Ideal.span {ξ}))) =
      (tiltEquivPlus hξ x : R) := by
  let hA := isRingOfIntegralElements_untiltPlus hξ
  let ϖ := P.isRingOfIntegralElements.exists_isPseudoUniformizer.choose
  let hϖ := P.isRingOfIntegralElements.exists_isPseudoUniformizer.choose_spec
  let ϖ_tilt := (tiltEquivPlus hξ).symm ϖ
  have hϖ_tilt := isPseudoUniformizer_tiltEquivPlus_symm hξ hϖ
  have := Subring.isLocalizationAway_of_isOpen (uniformTilt.plusSubring p hA)
    (uniformTilt.isOpen_plusSubring hA) ϖ_tilt hϖ_tilt.isTopologicallyNilpotent hϖ_tilt.isUnit
  have := Subring.isLocalizationAway_of_isOpen P.plus P.isRingOfIntegralElements.isOpen ϖ
    hϖ.isTopologicallyNilpotent hϖ.isUnit
  unfold tiltEquiv
  dsimp only
  exact IsLocalization.ringEquivOfRingEquiv_eq _ x

/-- The inverse of `tiltEquiv` restricts to `(tiltEquivPlus hξ).symm` on `R⁺`. -/
@[simp]
theorem tiltEquiv_symm_coe (hξ : ξ.IsPrimitive) (a : P.plus) :
    (tiltEquiv hξ).symm (a : R) = ((tiltEquivPlus hξ).symm a : _) := by
  apply (tiltEquiv hξ).injective
  rw [RingEquiv.apply_symm_apply, tiltEquiv_coe, RingEquiv.apply_symm_apply]

/-- The `n`-th coordinate of `(tiltEquiv hξ).symm x` is `sharp (x ^ (1 / p ^ n))`. -/
@[simp]
theorem coeff_tiltEquiv_symm (hξ : ξ.IsPrimitive) (x : R) (n : ℕ) :
    uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n ((tiltEquiv hξ).symm x) =
      sharp p P (Ideal.span {ξ}) ((frobeniusEquiv R p).symm^[n] x) := by
  have hcoe_one (b : P.plus) :
      (frobeniusEquiv R p).symm (b : R) = ((frobeniusEquiv P.plus p).symm b : R) := by
    apply (frobeniusEquiv R p).injective
    rw [RingEquiv.apply_symm_apply, coe_frobeniusEquiv, frobenius_def, ← Subring.coe_pow,
      frobeniusEquiv_symm_pow_p]
  have hcoe_iter (m : ℕ) (b : P.plus) :
      (frobeniusEquiv R p).symm^[m] (b : R) =
        (((frobeniusEquiv P.plus p).symm^[m] b : P.plus) : R) := by
    induction m with
    | zero => rfl
    | succ k ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, hcoe_one]
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  have := Subring.isLocalizationAway_of_isOpen P.plus P.isRingOfIntegralElements.isOpen ϖ
    hϖ.isTopologicallyNilpotent hϖ.isUnit
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj ϖ x
  have hϖ_root_u : IsUnit ((frobeniusEquiv R p).symm^[n] (ϖ : R)) :=
    (isUnit_pow_iff (pow_ne_zero n hp.out.ne_zero)).mp
      ((iterate_frobeniusEquiv_symm_pow (ϖ : R) n).symm ▸ hϖ.isUnit)
  have hu : IsUnit (sharp p P (Ideal.span {ξ}) ((frobeniusEquiv R p).symm^[n] (ϖ : R)) ^ k) :=
    (hϖ_root_u.map (sharp p P (Ideal.span {ξ}))).pow k
  apply hu.mul_right_cancel
  calc uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n ((tiltEquiv hξ).symm x) *
        sharp p P (Ideal.span {ξ}) ((frobeniusEquiv R p).symm^[n] (ϖ : R)) ^ k
    _ = uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n ((tiltEquiv hξ).symm x) *
        uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n
          ((tiltEquiv hξ).symm ((ϖ : R) ^ k)) := by
        rw [map_pow, map_pow, tiltEquiv_symm_coe, coeff_tiltEquivPlus_symm, hcoe_iter]
    _ = uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n
          ((tiltEquiv hξ).symm (x * (ϖ : R) ^ k)) := by
        rw [← map_mul, ← map_mul]
    _ = uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n ((tiltEquiv hξ).symm (a : R)) := by
        rw [show x * (ϖ : R) ^ k = (a : R) from ha]
    _ = sharp p P (Ideal.span {ξ}) ((frobeniusEquiv R p).symm^[n] (a : R)) := by
        rw [tiltEquiv_symm_coe, coeff_tiltEquivPlus_symm, hcoe_iter]
    _ = sharp p P (Ideal.span {ξ}) ((frobeniusEquiv R p).symm^[n] (x * (ϖ : R) ^ k)) := by
        rw [show (a : R) = x * (ϖ : R) ^ k from ha.symm]
    _ = sharp p P (Ideal.span {ξ}) ((frobeniusEquiv R p).symm^[n] x) *
        sharp p P (Ideal.span {ξ}) ((frobeniusEquiv R p).symm^[n] (ϖ : R)) ^ k := by
        rw [iterate_map_mul (frobeniusEquiv R p).symm, iterate_map_pow (frobeniusEquiv R p).symm,
          map_mul, map_pow]

/-- **Compatibility of `sharp` and `tiltEquiv`**: `sharp (tiltEquiv x) = x♯` for every `x` in the
tilt of the untilt. -/
@[simp]
theorem sharp_tiltEquiv (hξ : ξ.IsPrimitive)
    (x : uniformTilt p (untilt p P (Ideal.span {ξ}))) :
    sharp p P (Ideal.span {ξ}) (tiltEquiv hξ x) =
      uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) 0 x := by
  have h := coeff_tiltEquiv_symm hξ (tiltEquiv hξ x) 0
  simpa only [RingEquiv.symm_apply_apply, Function.iterate_zero_apply] using h.symm

/-- `tiltEquiv` identifies the integral tilt `A♭⁺` with `R⁺`. -/
theorem mem_plus_tiltEquiv_iff (hξ : ξ.IsPrimitive)
    (x : uniformTilt p (untilt p P (Ideal.span {ξ}))) :
    tiltEquiv hξ x ∈ P.plus ↔
      x ∈ uniformTilt.plusSubring p (isRingOfIntegralElements_untiltPlus hξ) := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have h := tiltEquiv_symm_coe hξ ⟨tiltEquiv hξ x, hx⟩
    rw [RingEquiv.symm_apply_apply] at h
    exact h ▸ ((tiltEquivPlus hξ).symm ⟨tiltEquiv hξ x, hx⟩).2
  · rw [show x = ((⟨x, hx⟩ : uniformTilt.plusSubring p _) : _) from rfl, tiltEquiv_coe]
    exact (tiltEquivPlus hξ ⟨x, hx⟩).2

/-- The image of `A♭⁺` under `tiltEquiv` is `R⁺`. -/
theorem map_plusSubring_tiltEquiv (hξ : ξ.IsPrimitive) :
    (uniformTilt.plusSubring p (isRingOfIntegralElements_untiltPlus hξ)).map
      (tiltEquiv hξ).toRingHom = P.plus := by
  ext y
  simp only [Subring.mem_map, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  refine ⟨?_, fun hy ↦ ⟨(tiltEquiv hξ).symm y,
    (mem_plus_tiltEquiv_iff hξ _).mp (by simpa using hy), (tiltEquiv hξ).apply_symm_apply y⟩⟩
  rintro ⟨x, hx, rfl⟩
  exact (mem_plus_tiltEquiv_iff hξ x).mpr hx

/-- The inverse `(tiltEquiv hξ).symm : R → uniformTilt p (untilt p P (span {ξ}))` is continuous. -/
@[fun_prop, continuity]
theorem continuous_tiltEquiv_symm (hξ : ξ.IsPrimitive) : Continuous (tiltEquiv hξ).symm := by
  refine continuous_of_continuousAt_zero (tiltEquiv hξ).symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, uniformTilt.tendsto_nhds_iff]
  intro n
  have hroot : Continuous (frobeniusEquiv R p).symm :=
    (frobeniusEquiv R p).toEquiv.continuous_symm_iff.mpr (Huber.isOpenMap_frobenius p)
  have hroot_zero : Tendsto ((frobeniusEquiv R p).symm^[n]) (𝓝 0) (𝓝 0) := by
    have h := (hroot.iterate n).continuousAt (x := (0 : R))
    simpa only [ContinuousAt, iterate_map_zero] using h
  have hcomp := (tendsto_sharp_zero (J := Ideal.span {ξ})).comp hroot_zero
  have hfun : (fun i ↦ uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n
        ((tiltEquiv hξ).symm.toAddMonoidHom i)) =
      fun x ↦ sharp p P (Ideal.span {ξ}) ((frobeniusEquiv R p).symm^[n] x) :=
    funext fun x ↦ coeff_tiltEquiv_symm hξ x n
  simpa only [Function.comp_def, uniformTilt.coeff_zero, hfun] using hcomp

/-- `tiltEquiv hξ : uniformTilt p (untilt p P (span {ξ})) → R` is continuous. -/
@[fun_prop, continuity]
theorem continuous_tiltEquiv (hξ : ξ.IsPrimitive) : Continuous (tiltEquiv hξ) := by
  let hA := isRingOfIntegralElements_untiltPlus hξ
  refine continuous_of_continuousAt_zero (tiltEquiv hξ).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro U hU
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  obtain ⟨k, hk⟩ := P.isRingOfIntegralElements.isBounded.exists_pow_mul_subset
    hϖ.isTopologicallyNilpotent hU
  obtain ⟨u, hu⟩ := (hϖ.isUnit.pow k).map (tiltEquiv hξ).symm
  let V : Set (uniformTilt p (untilt p P (Ideal.span {ξ}))) :=
    ((↑u⁻¹ : uniformTilt p (untilt p P (Ideal.span {ξ}))) * ·) ⁻¹'
      (uniformTilt.plusSubring p hA : Set _)
  have hV_open : IsOpen V :=
    (uniformTilt.isOpen_plusSubring hA).preimage (continuous_const_mul _)
  have hV_zero : (0 : uniformTilt p (untilt p P (Ideal.span {ξ}))) ∈ V := by
    simp [V]
  refine Filter.mem_of_superset (hV_open.mem_nhds hV_zero) fun x hx ↦ hk ?_
  have hx' : tiltEquiv hξ ((↑u⁻¹ : _) * x) ∈ P.plus :=
    (mem_plus_tiltEquiv_iff hξ _).mpr hx
  have hx_eq : (tiltEquiv hξ).toAddMonoidHom x = (ϖ : R) ^ k * tiltEquiv hξ ((↑u⁻¹ : _) * x) := by
    have hval : (tiltEquiv hξ).toAddMonoidHom x = tiltEquiv hξ x := rfl
    rw [hval, show (ϖ : R) ^ k = tiltEquiv hξ (u : _) by rw [hu, RingEquiv.apply_symm_apply],
      ← map_mul, ← mul_assoc, Units.mul_inv, one_mul]
  rw [hx_eq]
  exact Set.mul_mem_mul (Set.mem_singleton _) hx'

/-- **Topological tilting identification**: `tiltEquiv hξ` is a homeomorphism. -/
theorem isHomeomorph_tiltEquiv (hξ : ξ.IsPrimitive) : IsHomeomorph (tiltEquiv hξ) :=
  (Homeomorph.mk (tiltEquiv hξ).toEquiv (continuous_tiltEquiv hξ)
    (continuous_tiltEquiv_symm hξ)).isHomeomorph

/-- **Fontaine's map on the untilt is the quotient map**: composing `uniformTilt.theta` with
`𝕎 (tiltEquivPlus.symm)` recovers `𝕎 R⁺ → 𝕎 R⁺ ⧸ (ξ) ≃+* untiltPlus`. -/
theorem theta_eq [Nontrivial (untilt p P (Ideal.span {ξ}))] (hξ : ξ.IsPrimitive) :
    (uniformTilt.theta p (isRingOfIntegralElements_untiltPlus hξ)).comp
      (WittVector.map (tiltEquivPlus hξ).symm.toRingHom) =
      (quotientEquivUntiltPlus hξ).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {ξ})) := by
  have := (isRingOfIntegralElements_untiltPlus hξ).isAdicComplete_span_natCast p Fact.out
  refine WittVector.ringHom_ext_teichmuller fun a ↦ Subtype.ext ?_
  simp only [RingHom.comp_apply, WittVector.map_teichmuller, uniformTilt.theta_teichmuller,
    uniformTilt.coe_plusSharp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    coeff_zero_tiltEquivPlus_symm, coe_quotientEquivUntiltPlus, sharp_coe]

/-- **Kernel of Fontaine's map on the untilt**: under `tiltEquivPlus`, the kernel of
`uniformTilt.theta` maps onto `Ideal.span {ξ}`. -/
theorem map_ker_theta [Nontrivial (untilt p P (Ideal.span {ξ}))] (hξ : ξ.IsPrimitive) :
    (RingHom.ker (uniformTilt.theta p (isRingOfIntegralElements_untiltPlus hξ))).map
      (WittVector.map (tiltEquivPlus hξ).toRingHom) = Ideal.span {ξ} := by
  let eW := wittVectorMapEquiv (p := p) (tiltEquivPlus hξ)
  rw [show WittVector.map (tiltEquivPlus hξ).toRingHom = (eW : _ →+* _) from rfl,
    Ideal.map_comap_of_equiv eW]
  ext w
  have hev := RingHom.congr_fun (theta_eq hξ) w
  rw [RingHom.comp_apply, RingHom.comp_apply] at hev
  rw [Ideal.mem_comap, RingHom.mem_ker,
    show eW.symm w = WittVector.map (tiltEquivPlus hξ).symm.toRingHom w from rfl, hev,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    map_eq_zero_iff _ (quotientEquivUntiltPlus hξ).injective, Ideal.Quotient.eq_zero_iff_mem]

section PairTilt

variable [IsTateRing (uniformTilt p (untilt p P (Ideal.span {ξ})))]

/-- The morphism of Huber pairs `(untilt.pair hξ).tilt → P` given by `tiltEquiv`. -/
noncomputable def tiltHom (hξ : ξ.IsPrimitive) :
    Pair.Hom ((pair hξ).tilt (p := p)) P where
  toRingHom := (tiltEquiv hξ).toRingHom
  continuous_toRingHom := continuous_tiltEquiv hξ
  map_mem_plus x hx := (mem_plus_tiltEquiv_iff hξ x).mpr (by rwa [Pair.tilt_plus] at hx)

/-- The inverse morphism of Huber pairs `P → (untilt.pair hξ).tilt` given by
`(tiltEquiv hξ).symm`. -/
noncomputable def tiltInv (hξ : ξ.IsPrimitive) :
    Pair.Hom P ((pair hξ).tilt (p := p)) where
  toRingHom := (tiltEquiv hξ).symm.toRingHom
  continuous_toRingHom := continuous_tiltEquiv_symm hξ
  map_mem_plus x hx := by
    rw [Pair.tilt_plus]
    exact (mem_plus_tiltEquiv_iff hξ _).mp (by simpa using hx)

@[simp]
theorem tiltHom_comp_tiltInv (hξ : ξ.IsPrimitive) :
    (tiltHom hξ).comp (tiltInv hξ) = Pair.Hom.id P := by
  apply Pair.Hom.ext
  refine RingHom.ext fun x ↦ ?_
  simp [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_id, tiltHom, tiltInv]

@[simp]
theorem tiltInv_comp_tiltHom (hξ : ξ.IsPrimitive) :
    (tiltInv hξ).comp (tiltHom hξ) = Pair.Hom.id ((pair hξ).tilt (p := p)) := by
  apply Pair.Hom.ext
  refine RingHom.ext fun x ↦ ?_
  simp [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_id, tiltHom, tiltInv]

end PairTilt

end Tilt

/-- **Continuity of `sharp`**: for a primitive element `ξ` over a perfect complete Hausdorff Tate
ring of characteristic `p`, `sharp p P (span {ξ}) : R → untilt p P (span {ξ})` is continuous. -/
@[fun_prop, continuity]
theorem continuous_sharp (hξ : ξ.IsPrimitive) : Continuous (sharp p P (Ideal.span {ξ})) := by
  have := IsUniform.of_perfectRing (R := R) p
  have := completeSpace hξ
  have := t2Space hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  refine ((uniformTilt.continuous_coeff 0).comp (continuous_tiltEquiv_symm hξ)).congr fun x ↦ ?_
  simpa only [Function.comp_apply, Function.iterate_zero_apply] using coeff_tiltEquiv_symm hξ x 0

end PerfectoidAndTilt

end TauCeti.Perfectoid.untilt
