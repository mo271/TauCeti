/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.FiniteEtale.FiniteNormal
import TauCeti.AlgebraicGeometry.FiniteEtale.Completion
import TauCeti.AlgebraicGeometry.FiniteEtale.Hypersurface.Basic
import TauCeti.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.AdicCompletion.Principal
import TauCeti.RingTheory.LocalRing.MaximalIdeal.Square
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import TauCeti.RingTheory.RegularLocalRing.Normal
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension
import TauCeti.RingTheory.RegularLocalRing.Purity

/-!
# Purity for regular local rings

A regular local ring `A` of dimension at least two is pure: every finite étale cover of its
punctured spectrum extends to a finite étale scheme over `Spec A` (Stacks, Lemma 58.21.3 (0BMA)).
Equivalently, every finite torsion-free `A`-algebra whose localizations at maximal ideals are
normal domains, and which is étale over `A` away from the closed point, is étale over `A`.

In dimension two, a regular local ring is a Noetherian integrally closed domain, so purity is
equivalent to the algebraic statement (`TauCeti.IsLocalRing.purityHolds_iff_forall_etale`), where a
finite normal torsion-free algebra is free by miracle flatness and étale by the discriminant
criterion (`TauCeti.Algebra.etale_of_finiteNormal_of_ringKrullDim_eq_two`).

For dimension `d ≥ 3`, purity is proved by induction on `d`. Since a regular local ring is
Cohen–Macaulay, its depth equals its dimension, so extension across the closed point is detected
on the `𝔪`-adic completion `Â`
(`TauCeti.IsLocalRing.extends_iff_completion_extends_of_two_le_depth`). The completion `Â` is again
a regular local ring of dimension `d ≥ 3`, hence has depth at least three, is `(f)`-adically
complete for any regular parameter `f ∈ 𝔪̂ \ 𝔪̂²`, and its quotient `Â ⧸ (f)` is a regular local
ring of dimension `d - 1`. Purity for `Â ⧸ (f)` holds by the induction hypothesis and descends to
`Â` by `TauCeti.IsLocalRing.purityHolds_of_purityHolds_quotient_span_singleton`.

## Main results

* `TauCeti.IsLocalRing.purityHolds_of_ringKrullDim_eq_two`: purity holds for a regular local ring
  of dimension two.
* `TauCeti.IsLocalRing.purityHolds_of_isRegularLocalRing`: purity holds for any regular local ring
  of dimension at least two.
* `TauCeti.Algebra.etale_of_finiteNormal_of_isRegularLocalRing`: a finite torsion-free algebra
  with normal localizations over a regular local ring of dimension at least two, étale away from
  the closed point, is étale.

## References

* [The Stacks Project, Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA), purity for
  regular local rings.
* A. Grothendieck, *Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz locaux et
  globaux* (SGA 2), Exposé X, Théorème 3.4.
-/

public section

open IsLocalRing

universe u

namespace TauCeti.IsLocalRing

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- **Purity for a two-dimensional regular local ring.** If `A` is a regular local ring of
dimension two, every finite étale cover of the punctured spectrum of `A` extends to a finite étale
scheme over `Spec A`. -/
@[stacks 0BMA "(1) in dimension two"]
theorem purityHolds_of_ringKrullDim_eq_two (hdim : ringKrullDim A = 2) : PurityHolds A := by
  refine (purityHolds_iff_forall_etale hdim.ge).mpr fun B ↦ ?_
  obtain ⟨_, _, hnormal, het⟩ := (finiteNormalPuncturedEtale_iff A _).mp B.property
  exact TauCeti.Algebra.etale_of_finiteNormal_of_ringKrullDim_eq_two hdim (fun 𝔮 _ ↦ hnormal 𝔮)
    fun q _ hq ↦ have := het q hq; inferInstance

private theorem purityHolds_of_isRegularLocalRing_aux (n : ℕ) :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A],
      (maximalIdeal A).spanFinrank = n + 2 → PurityHolds A := by
  induction n with
  | zero =>
    intro A _ _ h
    have hdim : ringKrullDim A = 2 := by
      rw [← _root_.IsRegularLocalRing.spanFinrank_maximalIdeal, h]
      rfl
    exact purityHolds_of_ringKrullDim_eq_two hdim
  | succ n ih =>
    intro A _ _ h
    have hdimA : ringKrullDim A = (n + 3 : ℕ) := by
      rw [← _root_.IsRegularLocalRing.spanFinrank_maximalIdeal, h]
    have hdepthA : 2 ≤ depth (ModuleCat.of A A) := by
      have hd : (depth (ModuleCat.of A A) : WithBot ℕ∞) = ((n + 3 : ℕ) : WithBot ℕ∞) :=
        (TauCeti.IsRegularLocalRing.depth_eq_ringKrullDim (R := A)).trans hdimA
      refine WithBot.coe_le_coe.mp ?_
      rw [hd]
      change ((2 : ℕ) : WithBot ℕ∞) ≤ ((n + 3 : ℕ) : WithBot ℕ∞)
      exact_mod_cast (by omega : 2 ≤ n + 3)
    let Ahat := AdicCompletion (maximalIdeal A) A
    have hdimHat : ringKrullDim Ahat = (n + 3 : ℕ) :=
      (TauCeti.AdicCompletion.ringKrullDim_eq (R := A)).trans hdimA
    have hdepthHat : 3 ≤ depth (ModuleCat.of Ahat Ahat) := by
      have hd : (depth (ModuleCat.of Ahat Ahat) : WithBot ℕ∞) = ((n + 3 : ℕ) : WithBot ℕ∞) :=
        (TauCeti.IsRegularLocalRing.depth_eq_ringKrullDim (R := Ahat)).trans hdimHat
      refine WithBot.coe_le_coe.mp ?_
      rw [hd]
      change ((3 : ℕ) : WithBot ℕ∞) ≤ ((n + 3 : ℕ) : WithBot ℕ∞)
      exact_mod_cast (by omega : 3 ≤ n + 3)
    have hspanHat : (maximalIdeal Ahat).spanFinrank = n + 3 := by
      exact_mod_cast (_root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := Ahat)).trans hdimHat
    have hposHat : 0 < ringKrullDim Ahat := by
      rw [hdimHat]
      exact_mod_cast Nat.succ_pos (n + 2)
    obtain ⟨f, hfm, hf2, -⟩ :=
      TauCeti.IsLocalRing.exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes
        (R := Ahat) hposHat
    have hf0 : f ≠ 0 := fun h0 ↦ hf2 (h0 ▸ zero_mem _)
    have : IsRegularLocalRing (Ahat ⧸ Ideal.span {f}) :=
      TauCeti.IsRegularLocalRing.quotient_span_singleton hfm hf2
    have hdrop :=
      TauCeti.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_span_singleton_add_one hf0
    have hquot : PurityHolds (Ahat ⧸ Ideal.span {f}) := ih (Ahat ⧸ Ideal.span {f}) (by omega)
    have : IsAdicComplete (Ideal.span {f}) Ahat := IsAdicComplete.span_singleton_of_mem hfm
    have hhat : PurityHolds Ahat :=
      purityHolds_of_purityHolds_quotient_span_singleton (A := Ahat) (f := f) hdepthHat hquot
    refine (purityHolds_iff A).mpr fun V ↦ ?_
    exact (extends_iff_completion_extends_of_two_le_depth hdepthA V).mpr
      ((purityHolds_iff Ahat).mp hhat _)

/-- **Purity for a regular local ring.** If `A` is a regular local ring of dimension at least two,
every finite étale cover of the punctured spectrum of `A` extends to a finite étale scheme over
`Spec A`. -/
@[stacks 0BMA "(1)"]
theorem purityHolds_of_isRegularLocalRing (hdim : 2 ≤ ringKrullDim A) : PurityHolds A := by
  have hle : 2 ≤ (maximalIdeal A).spanFinrank := by
    rw [← _root_.IsRegularLocalRing.spanFinrank_maximalIdeal] at hdim
    exact_mod_cast hdim
  exact purityHolds_of_isRegularLocalRing_aux ((maximalIdeal A).spanFinrank - 2) A (by omega)

end TauCeti.IsLocalRing

namespace TauCeti.Algebra

/-- **Purity for finite normal algebras over a regular local ring.** Let `A` be a regular local
ring of dimension at least two and `B` a finite torsion-free `A`-algebra whose localizations at
maximal ideals are normal domains. If `B` is étale over `A` at every prime not lying over the
maximal ideal, then `B` is étale over `A`. -/
@[stacks 0BMA "(2), with B torsion free over A"]
theorem etale_of_finiteNormal_of_isRegularLocalRing {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [IsRegularLocalRing A] [Module.Finite A B] [Module.IsTorsionFree A B]
    (hdim : 2 ≤ ringKrullDim A)
    (hnormal : ∀ (𝔮 : Ideal B) [𝔮.IsMaximal],
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮))
    (hetale : ∀ (q : Ideal B) [q.IsPrime], q.under A ≠ maximalIdeal A →
      Algebra.IsEtaleAt A q) :
    Algebra.Etale A B :=
  etale_of_finiteNormal_of_purityHolds (IsLocalRing.purityHolds_of_isRegularLocalRing hdim)
    hdim hnormal hetale

end TauCeti.Algebra
