/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Subring
public import TauCeti.NumberTheory.Padics.Complex.Basic
public import TauCeti.RingTheory.Perfectoid.Away
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Perfectoid
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Gauge

import TauCeti.RingTheory.Huber.Pair.Complete
import TauCeti.RingTheory.Huber.Perfect

/-!
# Checks for the untilt along an ideal of `𝕎 R⁺`

These checks take for `(R, R⁺)` the tilt `ℂ_p♭` of `ℂ_p` with its power-bounded subring, a
perfect complete Hausdorff Tate ring of characteristic `p`, and test both `J = (p)` and the
mixed-characteristic primitive ideal `J = (p - [t])`:

* Compatibility: `p` and `p - [t]` are primitive, so the untilt is a complete Hausdorff uniform
  perfectoid Tate ring into which `𝕎 R⁺ ⧸ J` embeds as a ring of integral elements, with `A°/A⁺`
  almost zero, tilt homeomorphic to `ℂ_p♭`, sharp map continuous, and Fontaine kernel `(ξ)`.
* Degenerate cases: the untilt along `⊤` is zero; over a zero base every primitive untilt is zero
  with zero `sharp` and `tiltEquiv`; along `(p)`, `equivOfSpanP` is a homeomorphism to `ℂ_p♭`
  preserving `R⁺`.
* Computations and non-examples: `sharp (t ^ 2) = p ^ 2` for `J = (p - [t])`; at `p = 2`,
  `sharp (t + t) = 0 ≠ sharp t + sharp t`; enlarging `(p)` to `⊤` kills `sharp 1 = 1`; the map
  from the non-primitive quotient along `(p ^ 2)` to `(p)` kills the nonzero class of `p`; and
  `tiltEquiv` sends the sum of two shifted root sequences to `ϖ₀ + ϖ₁` while `ϖ₀ ≠ ϖ₀ ^ p`.
* Integral-to-Tate criterion: relative Frobenius on `𝕎 ℂ_p♭° ⧸ (p - [t])` is bijective and
  `isPerfectoidTateRing_of_isIntegralPerfectoid_of_hasBasis` recovers the perfectoid Tate structure.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.PrimitiveUntilt

variable (p : ℕ) [Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

private noncomputable def parameter : PseudoUniformizerRoots p ℂ_[p] :=
  Classical.choice (nonempty_pseudoUniformizerRoots_of_isAlgClosed (PadicComplex.norm_p_lt_one p))

local instance : IsTateRing (uniformTilt p ℂ_[p]) :=
  uniformTilt.isTateRing_of_sharp (ϖ := (parameter p).toTilt)
    (by simpa using (parameter p).isPseudoUniformizer_root_zero)

local instance : IsUniform (uniformTilt p ℂ_[p]) := IsUniform.of_perfectRing p

/-- The Huber pair `(ℂ_p♭, ℂ_p♭°)`. -/
private noncomputable abbrev pair : Pair (uniformTilt p ℂ_[p]) := Pair.powerBounded _

/-- The tilted pseudouniformiser `t = p♭` as an element of `ℂ_p♭°`. -/
private noncomputable def tPlus : (pair p).plus :=
  ⟨(parameter p).toTilt,
    (pair p).isRingOfIntegralElements.mem_of_isTopologicallyNilpotent
      (parameter p).isPseudoUniformizer_toTilt.isTopologicallyNilpotent⟩

private theorem isPseudoUniformizer_tPlus :
    IsPseudoUniformizer ((tPlus p : (pair p).plus) : uniformTilt p ℂ_[p]) :=
  (parameter p).isPseudoUniformizer_toTilt

/-- The mixed-characteristic primitive element `ξ = p - [t] ∈ 𝕎 ℂ_p♭°`. -/
private noncomputable def xi : WittVector p (pair p).plus :=
  (p : WittVector p (pair p).plus) - WittVector.teichmuller p (tPlus p)

private theorem isPrimitive_xi : (xi p).IsPrimitive := by
  have ht := isPseudoUniformizer_tPlus p
  have hI : IsAdic (Ideal.span {tPlus p}) :=
    (pair p).plus.isAdic_span_singleton_of_isOpen_of_isBounded
      (pair p).isRingOfIntegralElements.isOpen (pair p).isRingOfIntegralElements.isBounded
      ht (tPlus p).2
  have := (pair p).isRingOfIntegralElements.isAdicComplete_span_singleton (tPlus p) ht
  have h := WittVector.isPrimitive_p_add_teichmuller_mul_of_isAdic
    (S := (pair p).plus) hI (Ideal.subset_span rfl) (-1)
  rwa [mul_neg_one, ← sub_eq_add_neg] at h

-- Compatibility: the untilt along the primitive ideal `(p)` is complete and Hausdorff.
example : CompleteSpace (untilt p (pair p) (Ideal.span {(p : WittVector p (pair p).plus)})) :=
  untilt.completeSpace WittVector.isPrimitive_p

example : T2Space (untilt p (pair p) (Ideal.span {(p : WittVector p (pair p).plus)})) :=
  untilt.t2Space WittVector.isPrimitive_p

-- Compatibility: `𝕎 R⁺ ⧸ (p)` embeds into the untilt along `(p)`.
example : Function.Injective
    (algebraMap (WittVector p (pair p).plus ⧸ Ideal.span {(p : WittVector p (pair p).plus)})
      (untilt p (pair p) (Ideal.span {(p : WittVector p (pair p).plus)}))) :=
  untilt.algebraMap_injective WittVector.isPrimitive_p

-- Degenerate case: the untilt along the unit ideal is the zero ring.
example : Subsingleton (untilt p (pair p) ⊤) := by
  refine IsLocalization.subsingleton
    (M := (untiltDenominators p (pair p)).map (Ideal.Quotient.mk ⊤)) ?_
  exact ⟨1, one_mem _, Ideal.Quotient.eq_zero_iff_mem.mpr Submodule.mem_top⟩

-- Computation: the class of `[ϖ]` is a pseudouniformiser, and the untilt is `(𝕎 R⁺ ⧸ J)[1/[ϖ]]`.
example (J : Ideal (WittVector p (pair p).plus)) (ϖ : (pair p).plus)
    (hϖ : IsPseudoUniformizer (ϖ : uniformTilt p ℂ_[p])) :
    IsPseudoUniformizer (algebraMap _ (untilt p (pair p) J)
      (Ideal.Quotient.mk J (WittVector.teichmuller p ϖ))) ∧
    IsLocalization.Away (Ideal.Quotient.mk J (WittVector.teichmuller p ϖ)) (untilt p (pair p) J) :=
  ⟨untilt.isPseudoUniformizer_algebraMap hϖ, untilt.isLocalizationAway hϖ⟩

-- Degenerate recovery: `untilt p (pair p) (span {p})` is homeomorphic to `ℂ_p♭` preserving `R⁺`.
example : IsHomeomorph (untilt.equivOfSpanP p (pair p)) ∧
    (untiltPlus p (pair p) (Ideal.span {(p : WittVector p (pair p).plus)})).map
      (untilt.equivOfSpanP p (pair p)).toRingHom = (pair p).plus :=
  ⟨untilt.isHomeomorph_equivOfSpanP, untilt.map_untiltPlus_equivOfSpanP⟩

-- Zero base: over a zero ring, every primitive untilt is zero with zero `sharp` and `tiltEquiv`.
example {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
    [IsTateRing R] [CompleteSpace R] [T2Space R] [IsUniform R] [CharP R p] [PerfectRing R p]
    [Subsingleton R] (P : Pair R) (ξ : WittVector p P.plus) (hξ : ξ.IsPrimitive)
    [CompleteSpace (untilt p P (Ideal.span {ξ}))] [T2Space (untilt p P (Ideal.span {ξ}))]
    [IsUniform (untilt p P (Ideal.span {ξ}))]
    [Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ})))] (x : R)
    (y : uniformTilt p (untilt p P (Ideal.span {ξ}))) :
    Subsingleton (untilt p P (Ideal.span {ξ})) ∧
      untilt.sharp p P (Ideal.span {ξ}) x = 0 ∧ untilt.tiltEquiv hξ y = 0 := by
  have : Subsingleton (untilt p P (Ideal.span {ξ})) := untilt.subsingleton_of_subsingleton
  exact ⟨inferInstance, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

-- Computation: for `ξ = p - [t]`, `sharp t = p` and `sharp (t ^ 2) = p ^ 2`.
private theorem sharp_tPlus_eq_p :
    untilt.sharp p (pair p) (Ideal.span {xi p}) ((tPlus p : (pair p).plus) : uniformTilt p ℂ_[p]) =
      (p : untilt p (pair p) (Ideal.span {xi p})) := by
  rw [untilt.sharp_coe]
  have hmod : Ideal.Quotient.mk (Ideal.span {xi p}) (WittVector.teichmuller p (tPlus p)) =
      Ideal.Quotient.mk (Ideal.span {xi p}) (p : WittVector p (pair p).plus) := by
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-1, by simp [xi]⟩
  rw [hmod, map_natCast, map_natCast]

example : untilt.sharp p (pair p) (Ideal.span {xi p})
    (((tPlus p : (pair p).plus) : uniformTilt p ℂ_[p]) ^ 2) =
    (p : untilt p (pair p) (Ideal.span {xi p})) ^ 2 := by
  rw [map_pow, sharp_tPlus_eq_p]

-- Non-additivity at `p = 2`: `sharp (t + t) = 0`, whereas `sharp t + sharp t = 4 ≠ 0`.
example :
    untilt.sharp 2 (pair 2) (Ideal.span {xi 2})
        (((tPlus 2 : (pair 2).plus) : uniformTilt 2 ℂ_[2]) +
          ((tPlus 2 : (pair 2).plus) : uniformTilt 2 ℂ_[2])) ≠
      untilt.sharp 2 (pair 2) (Ideal.span {xi 2})
          ((tPlus 2 : (pair 2).plus) : uniformTilt 2 ℂ_[2]) +
        untilt.sharp 2 (pair 2) (Ideal.span {xi 2})
          ((tPlus 2 : (pair 2).plus) : uniformTilt 2 ℂ_[2]) := by
  have : Nontrivial (untilt 2 (pair 2) (Ideal.span {xi 2})) :=
    untilt.nontrivial (isPrimitive_xi 2)
  have hsum_zero : ((tPlus 2 : (pair 2).plus) : uniformTilt 2 ℂ_[2]) +
      ((tPlus 2 : (pair 2).plus) : uniformTilt 2 ℂ_[2]) = 0 := by
    have h2 : (2 : uniformTilt 2 ℂ_[2]) = 0 := by
      exact_mod_cast CharP.cast_eq_zero (uniformTilt 2 ℂ_[2]) 2
    rw [← two_mul, h2, zero_mul]
  rw [hsum_zero, map_zero, sharp_tPlus_eq_p 2]
  have hunit : IsUnit (((2 : ℕ) : untilt 2 (pair 2) (Ideal.span {xi 2})) ^ 2) := by
    rw [← sharp_tPlus_eq_p 2]
    exact (untilt.isPseudoUniformizer_sharp (J := Ideal.span {xi 2})
      (isPseudoUniformizer_tPlus 2)).isUnit.pow 2
  have h4 : ((2 : ℕ) : untilt 2 (pair 2) (Ideal.span {xi 2})) + ((2 : ℕ) : _) =
      ((2 : ℕ) : _) ^ 2 := by
    push_cast
    ring
  rw [h4]
  exact hunit.ne_zero.symm

-- Functoriality: enlarging `(p)` to `⊤` kills the nonzero element `sharp 1 = 1`.
example :
    let hJ : (Ideal.span {(p : WittVector p (pair p).plus)}).map
        (WittVector.map ((Pair.Hom.id (pair p)).toRingHom.restrict _ _
          (Pair.Hom.id (pair p)).map_mem_plus)) ≤ ⊤ := le_top
    untilt.sharp p (pair p) (Ideal.span {(p : WittVector p (pair p).plus)}) 1 ≠ 0 ∧
      untilt.map (Pair.Hom.id (pair p)) hJ
        (untilt.sharp p (pair p) (Ideal.span {(p : WittVector p (pair p).plus)}) 1) = 0 := by
  intro hJ
  have : Nontrivial (untilt p (pair p) (Ideal.span {(p : WittVector p (pair p).plus)})) :=
    untilt.nontrivial WittVector.isPrimitive_p
  have : Subsingleton (untilt p (pair p) ⊤) := by
    refine IsLocalization.subsingleton
      (M := (untiltDenominators p (pair p)).map (Ideal.Quotient.mk ⊤)) ?_
    exact ⟨1, one_mem _, Ideal.Quotient.eq_zero_iff_mem.mpr Submodule.mem_top⟩
  refine ⟨by rw [map_one]; exact one_ne_zero, Subsingleton.elim _ _⟩

-- Non-example: `(p ^ 2)` is not primitive; in its untilt `p ^ 2 = 0` while `p ≠ 0`, and the map
-- into the untilt along `(p)` kills `p`.
example :
    let J₂ : Ideal (WittVector p (pair p).plus) := Ideal.span {(p : WittVector p (pair p).plus) ^ 2}
    let J₁ : Ideal (WittVector p (pair p).plus) := Ideal.span {(p : WittVector p (pair p).plus)}
    let hJ : J₂.map (WittVector.map ((Pair.Hom.id (pair p)).toRingHom.restrict _ _
        (Pair.Hom.id (pair p)).map_mem_plus)) ≤ J₁ := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      have hmap : WittVector.map ((Pair.Hom.id (pair p)).toRingHom.restrict _ _
          (Pair.Hom.id (pair p)).map_mem_plus) ((p : WittVector p (pair p).plus) ^ 2) =
          (p : WittVector p (pair p).plus) ^ 2 := by
        rw [map_pow, map_natCast]
      rw [hmap]
      exact Ideal.mem_span_singleton.mpr (dvd_pow_self _ (by decide))
    (p : untilt p (pair p) J₂) ^ 2 = 0 ∧
      (p : untilt p (pair p) J₂) ≠ 0 ∧
      untilt.map (Pair.Hom.id (pair p)) hJ (p : untilt p (pair p) J₂) = 0 := by
  intro J₂ J₁ hJ
  have hp2 : (p : untilt p (pair p) J₂) ^ 2 = 0 := by
    have hq : (Ideal.Quotient.mk J₂ ((p : WittVector p (pair p).plus) ^ 2)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    calc (p : untilt p (pair p) J₂) ^ 2
      _ = algebraMap (WittVector p (pair p).plus ⧸ J₂) (untilt p (pair p) J₂)
            (Ideal.Quotient.mk J₂ ((p : WittVector p (pair p).plus) ^ 2)) := by
          rw [map_pow, map_natCast, map_pow, map_natCast]
      _ = 0 := by rw [hq, map_zero]
  have hp_ne : (p : untilt p (pair p) J₂) ≠ 0 := by
    intro h0
    have := untilt.isLocalizationAway (J := J₂) (isPseudoUniformizer_tPlus p)
    have h0' : algebraMap (WittVector p (pair p).plus ⧸ J₂) (untilt p (pair p) J₂)
        (Ideal.Quotient.mk J₂ (p : WittVector p (pair p).plus)) = 0 := by
      simpa only [map_natCast] using h0
    obtain ⟨⟨y, k, hk_eq⟩, hk⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Ideal.Quotient.mk J₂ (WittVector.teichmuller p (tPlus p))))
      (untilt p (pair p) J₂) _).mp h0'
    dsimp only at hk_eq hk
    rw [← hk_eq, ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at hk
    obtain ⟨w, hw⟩ := hk
    have hcoeff := congrArg (fun v : WittVector p (pair p).plus ↦ v.coeff 1) hw
    have hteich : (WittVector.teichmuller p (tPlus p) ^ k * (p : WittVector p (pair p).plus)).coeff
        1 = (tPlus p ^ k) ^ p := by
      rw [← map_pow, ← WittVector.verschiebung_frobenius, WittVector.verschiebung_coeff_succ,
        WittVector.coeff_frobenius_charP, WittVector.teichmuller_coeff_zero]
    have hp2w : ((p : WittVector p (pair p).plus) ^ 2 * w).coeff 1 = 0 := by
      have hrew : (p : WittVector p (pair p).plus) ^ 2 * w =
          (w * (p : WittVector p (pair p).plus)) * (p : WittVector p (pair p).plus) := by ring
      rw [hrew, ← WittVector.verschiebung_frobenius, WittVector.verschiebung_coeff_succ,
        ← WittVector.verschiebung_frobenius, WittVector.frobenius_verschiebung,
        WittVector.mul_coeff_zero, WittVector.coeff_p_zero, mul_zero]
    rw [hteich, hp2w] at hcoeff
    have hval : (((tPlus p : (pair p).plus) : uniformTilt p ℂ_[p]) ^ k) ^ p = 0 := by
      simpa only [Subring.coe_pow, ZeroMemClass.coe_zero] using congrArg Subtype.val hcoeff
    exact ((isPseudoUniformizer_tPlus p).isUnit.pow k |>.pow p).ne_zero hval
  have hkill : untilt.map (Pair.Hom.id (pair p)) hJ (p : untilt p (pair p) J₂) = 0 := by
    rw [map_natCast]
    have hq : Ideal.Quotient.mk J₁ (p : WittVector p (pair p).plus) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    calc (p : untilt p (pair p) J₁)
      _ = algebraMap (WittVector p (pair p).plus ⧸ J₁) (untilt p (pair p) J₁)
            (Ideal.Quotient.mk J₁ (p : WittVector p (pair p).plus)) := by
          rw [map_natCast, map_natCast]
      _ = 0 := by rw [hq, map_zero]
  exact ⟨hp2, hp_ne, hkill⟩

section XiUntilt

private local instance : CompleteSpace (untilt p (pair p) (Ideal.span {xi p})) :=
  untilt.completeSpace (isPrimitive_xi p)

private local instance : T2Space (untilt p (pair p) (Ideal.span {xi p})) :=
  untilt.t2Space (isPrimitive_xi p)

private local instance : IsUniform (untilt p (pair p) (Ideal.span {xi p})) :=
  untilt.isUniform (isPrimitive_xi p)

private local instance :
    Fact (IsTopologicallyNilpotent (p : untilt p (pair p) (Ideal.span {xi p}))) :=
  ⟨untilt.isTopologicallyNilpotent_natCast (isPrimitive_xi p)⟩

private local instance : Nontrivial (untilt p (pair p) (Ideal.span {xi p})) :=
  untilt.nontrivial (isPrimitive_xi p)

private local instance : IsTateRing (uniformTilt p (untilt p (pair p) (Ideal.span {xi p}))) :=
  untilt.isTateRing_uniformTilt (Ideal.span {xi p})

-- Perfectoid Tate pair structure, tilting identification, and Fontaine kernel for `J = (p - [t])`.
example :
    IsPerfectoidTateRing p (untilt p (pair p) (Ideal.span {xi p})) ∧
      IsRingOfIntegralElements (untiltPlus p (pair p) (Ideal.span {xi p})) ∧
      untiltPlus p (pair p) (Ideal.span {xi p}) =
        powerBoundedSubring (untilt p (pair p) (Ideal.span {xi p})) ∧
      Continuous (untilt.sharp p (pair p) (Ideal.span {xi p})) ∧
      IsHomeomorph (untilt.tiltEquiv (isPrimitive_xi p)) ∧
      (RingHom.ker (uniformTilt.theta p
          (untilt.isRingOfIntegralElements_untiltPlus (isPrimitive_xi p)))).map
          (WittVector.map (untilt.tiltEquivPlus (isPrimitive_xi p)).toRingHom) =
        Ideal.span {xi p} ∧
      (untilt.tiltHom (isPrimitive_xi p)).comp (untilt.tiltInv (isPrimitive_xi p)) =
        Pair.Hom.id (pair p) :=
  ⟨untilt.isPerfectoidTateRing (isPrimitive_xi p),
    untilt.isRingOfIntegralElements_untiltPlus (isPrimitive_xi p),
    untilt.untiltPlus_eq_powerBoundedSubring (isPrimitive_xi p),
    untilt.continuous_sharp (isPrimitive_xi p),
    untilt.isHomeomorph_tiltEquiv (isPrimitive_xi p),
    untilt.map_ker_theta (isPrimitive_xi p),
    untilt.tiltHom_comp_tiltInv (isPrimitive_xi p)⟩

-- Tilting identification values: `tiltEquiv` sends the sum of two shifted root sequences to
-- `ϖ₀ + ϖ₁`, and `ϖ₀ ≠ ϖ₀ ^ p` (distinguishing `tiltEquiv` from a Frobenius twist).
example :
    let hξ := isPrimitive_xi p
    let ϖ₀ : (pair p).plus := tPlus p
    let ϖ₁ : (pair p).plus := (frobeniusEquiv (pair p).plus p).symm (tPlus p)
    untilt.tiltEquiv hξ
        (((untilt.tiltEquivPlus hξ).symm ϖ₀ :
            uniformTilt p (untilt p (pair p) (Ideal.span {xi p}))) +
          ((untilt.tiltEquivPlus hξ).symm ϖ₁ :
            uniformTilt p (untilt p (pair p) (Ideal.span {xi p})))) =
      (ϖ₀ : uniformTilt p ℂ_[p]) + (ϖ₁ : uniformTilt p ℂ_[p]) ∧
    untilt.tiltEquiv hξ
        ((untilt.tiltEquivPlus hξ).symm ϖ₀ :
          uniformTilt p (untilt p (pair p) (Ideal.span {xi p}))) ≠
      (ϖ₀ : uniformTilt p ℂ_[p]) ^ p := by
  intro hξ ϖ₀ ϖ₁
  have heval (a : (pair p).plus) :
      untilt.tiltEquiv hξ ((untilt.tiltEquivPlus hξ).symm a :
          uniformTilt p (untilt p (pair p) (Ideal.span {xi p}))) = (a : uniformTilt p ℂ_[p]) :=
    (untilt.tiltEquiv_coe hξ ((untilt.tiltEquivPlus hξ).symm a)).trans
      (congrArg Subtype.val ((untilt.tiltEquivPlus hξ).apply_symm_apply a))
  refine ⟨(map_add (untilt.tiltEquiv hξ) _ _).trans
      (congrArg₂ (· + ·) (heval ϖ₀) (heval ϖ₁)), fun h ↦ ?_⟩
  have heq := (heval ϖ₀).symm.trans h
  have ht := isPseudoUniformizer_tPlus p
  have h1 : ((tPlus p : (pair p).plus) : uniformTilt p ℂ_[p]) ^ (p - 1) = 1 := by
    have hmul : (tPlus p : uniformTilt p ℂ_[p]) * (tPlus p : uniformTilt p ℂ_[p]) ^ (p - 1) =
        (tPlus p : uniformTilt p ℂ_[p]) * 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_le, mul_one, ← heq]
    exact ht.isUnit.mul_left_cancel hmul
  have hconst : Filter.Tendsto (fun n : ℕ ↦ ((tPlus p : (pair p).plus) : uniformTilt p ℂ_[p]) ^
      ((p - 1) * n)) Filter.atTop (nhds 1) := by
    simp only [pow_mul, h1, one_pow]
    exact tendsto_const_nhds
  have hzero : Filter.Tendsto (fun n : ℕ ↦ ((tPlus p : (pair p).plus) : uniformTilt p ℂ_[p]) ^
      ((p - 1) * n)) Filter.atTop (nhds 0) :=
    ht.isTopologicallyNilpotent.comp
      (Filter.tendsto_atTop_atTop_of_monotone (fun _ _ h ↦ Nat.mul_le_mul_left _ h)
        fun b ↦ ⟨b, Nat.le_mul_of_pos_left b (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)⟩)
  exact one_ne_zero (tendsto_nhds_unique hconst hzero)

-- Integral-to-Tate criterion (BMS Lemma 3.10(i) and Lemma 3.21) on `𝕎 ℂ_p♭° ⧸ (p - [t])`.
example : IsPerfectoidTateRing p (untilt p (pair p) (Ideal.span {xi p})) := by
  have hξ := isPrimitive_xi p
  obtain ⟨ϖ, hϖ, hϖp⟩ := untilt.exists_isPseudoUniformizer_pow_dvd_coeff_zero hξ
  have hdvd := hξ.isDistinguished.pow_prime_dvd_natCast_quotient hϖp
  have hbij := hξ.isDistinguished.frobeniusModPow_bijective_quotient hϖp
  have := (pair p).isRingOfIntegralElements.isAdicComplete_span_singleton ϖ hϖ
  have hrad : (xi p).coeff 0 ∈ (Ideal.span {ϖ}).radical :=
    Ideal.le_radical (Ideal.mem_span_singleton.mpr
      ((dvd_pow_self _ (Fact.out : p.Prime).ne_zero).trans hϖp))
  have := hξ.isDistinguished.isAdicComplete_quotient hrad
  have := untilt.isLocalizationAway (J := Ideal.span {xi p}) hϖ
  have hπ_nzd : Ideal.Quotient.mk (Ideal.span {xi p}) (WittVector.teichmuller p ϖ) ∈
      nonZeroDivisors (WittVector p (pair p).plus ⧸ Ideal.span {xi p}) := by
    refine mem_nonZeroDivisors_iff_right.mpr fun x hx ↦ untilt.algebraMap_injective hξ ?_
    have hu := (untilt.isPseudoUniformizer_algebraMap (J := Ideal.span {xi p}) hϖ).isUnit
    have hmul : algebraMap _ (untilt p (pair p) (Ideal.span {xi p}))
        (Ideal.Quotient.mk (Ideal.span {xi p}) (WittVector.teichmuller p ϖ)) *
        algebraMap _ _ x = 0 := by
      rw [← map_mul, mul_comm, hx, map_zero]
    rw [map_zero]
    exact hu.mul_left_cancel (hmul.trans (mul_zero _).symm)
  have := IsIntegralPerfectoid.of_bijective_frobeniusModPow hπ_nzd hbij
  exact isPerfectoidTateRing_of_isIntegralPerfectoid_of_hasBasis
    (π := Ideal.Quotient.mk (Ideal.span {xi p}) (WittVector.teichmuller p ϖ))
    (untilt.hasBasis_nhds_zero (J := Ideal.span {xi p}) hϖ) hπ_nzd hdvd

end XiUntilt

end TauCeti.Examples.PrimitiveUntilt
