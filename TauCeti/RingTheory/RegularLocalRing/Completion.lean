/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Flat.Basic
public import TauCeti.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.RegularLocalRing.GRing
public import TauCeti.RingTheory.SerreCondition.RegularAlgebraMap
import TauCeti.Algebra.DualNumber.Basic
import TauCeti.RingTheory.Flat.IntegrallyClosed
import TauCeti.RingTheory.TrivSqZeroExt

/-!
# Completions of local G-rings

Let `A` be a local G-ring with maximal ideal `𝔪` and `Â = AdicCompletion 𝔪 A` its `𝔪`-adic
completion. Identifying `A` with `A_𝔪` transports the defining G-ring condition at `𝔪` to show that
the completion map `A → Â` is a regular ring map (Stacks, Lemma 15.43.4 (`0H7T`)). Because `A → Â`
is also faithfully flat (`AdicCompletion.faithfullyFlat_of_isLocalRing`) and `Â` is a Noetherian
local ring, combining regular-map ascent (`TauCeti.RingTheory.SerreCondition.RegularAlgebraMap`)
with faithful-flatness descent gives local-to-completion equivalences for `A` and `Â`:

* `Â` satisfies Serre's condition `(R_n)` (respectively `(S_n)`) if and only if `A` does;
* `Â` is reduced if and only if `A` is reduced;
* `Â` is an integrally closed domain if and only if `A` is an integrally closed domain (analytic
  irreducibility and analytic normality of normal local G-rings).

For an arbitrary Noetherian local ring, `depth Â = depth A` and `dim Â = dim A` already make
Cohen–Macaulayness invariant under completion without the G-ring hypothesis. By contrast, `(R_n)`,
`(S_n)` for finite `n` (such as `(S_1)`, absence of embedded primes), reducedness, and analytic
normality genuinely require `IsGRing A`: Nagata constructed Noetherian local domains whose
completions acquire nilpotents or embedded primes at non-maximal primes. Likewise, `IsDomain A`
alone does not make `Â` a domain even for a local G-ring (the local ring of the node
`k[x, y] ⧸ (y² - x² - x³)` at `(x, y)` has completion with two branches `y = ±x √(1 + x)`), whereas
when `A` is also integrally closed, `Â` is both reduced and integrally closed in its total ring of
fractions and hence a domain because `Â` is local (`IsLocalRing.isDomain_of_isIntegrallyClosed`).

## Main results

* `TauCeti.Excellence.IsGRing.regularAlgebraMap_adicCompletion_maximalIdeal`: for a local G-ring
  `A`, the completion map `A → Â` at the maximal ideal is a regular ring map (Stacks,
  Lemma 15.43.4 (`0H7T`)).
* `TauCeti.Excellence.IsGRing.satisfiesSerreR_adicCompletion_iff` and
  `TauCeti.Excellence.IsGRing.satisfiesSerreS_adicCompletion_iff`: `Â` satisfies `(R_n)` or `(S_n)`
  if and only if `A` does.
* `TauCeti.Excellence.IsGRing.isReduced_adicCompletion_iff` and the low-priority instance
  `TauCeti.Excellence.IsGRing.isReduced_adicCompletion`: `Â` is reduced if and only if `A` is.
* `TauCeti.Excellence.IsGRing.isIntegrallyClosed_adicCompletion`,
  `TauCeti.Excellence.IsGRing.isDomain_adicCompletion`, and
  `TauCeti.Excellence.IsGRing.isDomain_and_isIntegrallyClosed_adicCompletion_iff`: `Â` is an
  integrally closed domain if and only if `A` is.

## References

* [Stacks Project, Lemma 15.43.4](https://stacks.math.columbia.edu/tag/0H7T) and
  [Section 15.51](https://stacks.math.columbia.edu/tag/07P6).
* H. Matsumura, *Commutative Ring Theory*, §32.
-/

public section

universe u

open IsLocalRing

namespace TauCeti.Excellence.IsGRing

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsGRing A]

/-- **The completion map of a local G-ring is regular.** For a local G-ring `A` with maximal ideal
`𝔪`, the completion map `A → Â` is a regular ring map. Stacks, Lemma 15.43.4 (0H7T). -/
@[stacks 0H7T]
instance regularAlgebraMap_adicCompletion_maximalIdeal :
    RegularAlgebraMap A (AdicCompletion (maximalIdeal A) A) :=
  (IsLocalization.atUnits A (maximalIdeal A).primeCompl
      (S := Localization.AtPrime (maximalIdeal A))
      fun _ hx ↦ notMem_maximalIdeal.mp hx).symm.toRingEquiv
    |>.regularAlgebraMap_adicCompletion (map_ringEquiv_maximalIdeal _)

/-- For a local G-ring `A`, the completion `Â` at its maximal ideal satisfies Serre's condition
`(R_n)` if and only if `A` does. -/
theorem satisfiesSerreR_adicCompletion_iff {n : ℕ} :
    Ring.SatisfiesSerreR n (AdicCompletion (maximalIdeal A) A) ↔ Ring.SatisfiesSerreR n A :=
  ⟨fun h ↦ h.of_faithfullyFlat, RegularAlgebraMap.satisfiesSerreR⟩

/-- For a local G-ring `A`, the completion `Â` at its maximal ideal satisfies Serre's condition
`(S_n)` if and only if `A` does. -/
theorem satisfiesSerreS_adicCompletion_iff {n : ℕ} :
    Module.SatisfiesSerreS n (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal A) A) ↔ Module.SatisfiesSerreS n A A :=
  ⟨fun h ↦ h.of_faithfullyFlat, RegularAlgebraMap.satisfiesSerreS⟩

/-- For a local G-ring `A`, the completion `Â` at its maximal ideal is reduced if and only if `A`
is reduced. -/
theorem isReduced_adicCompletion_iff :
    IsReduced (AdicCompletion (maximalIdeal A) A) ↔ IsReduced A :=
  ⟨fun _ ↦ isReduced_of_injective (algebraMap A (AdicCompletion (maximalIdeal A) A))
      (FaithfulSMul.algebraMap_injective A (AdicCompletion (maximalIdeal A) A)),
    fun _ ↦ RegularAlgebraMap.isReduced (R := A)⟩

/-- The completion of a reduced local G-ring at its maximal ideal is reduced. -/
instance (priority := low) isReduced_adicCompletion [IsReduced A] :
    IsReduced (AdicCompletion (maximalIdeal A) A) :=
  isReduced_adicCompletion_iff.mpr ‹_›

/-- The completion of a reduced integrally closed local G-ring at its maximal ideal is integrally
closed in its total ring of fractions. -/
instance (priority := low) isIntegrallyClosed_adicCompletion [IsReduced A] [IsIntegrallyClosed A] :
    IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) :=
  RegularAlgebraMap.isIntegrallyClosed (R := A)

/-- **Analytic irreducibility of normal local G-rings.** The completion of an integrally closed
local G-ring domain at its maximal ideal is an integral domain: it is a reduced integrally closed
Noetherian local ring. -/
instance (priority := low) isDomain_adicCompletion [IsDomain A] [IsIntegrallyClosed A] :
    IsDomain (AdicCompletion (maximalIdeal A) A) :=
  IsLocalRing.isDomain_of_isIntegrallyClosed

/-- **Analytic normality of local G-rings.** For a local G-ring `A`, the completion `Â` at its
maximal ideal is an integrally closed domain if and only if `A` is an integrally closed domain. -/
theorem isDomain_and_isIntegrallyClosed_adicCompletion_iff :
    (IsDomain (AdicCompletion (maximalIdeal A) A) ∧
      IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A)) ↔
      IsDomain A ∧ IsIntegrallyClosed A :=
  ⟨fun ⟨_, _⟩ ↦
    ⟨Function.Injective.isDomain (algebraMap A (AdicCompletion (maximalIdeal A) A))
      (FaithfulSMul.algebraMap_injective A (AdicCompletion (maximalIdeal A) A)),
      TauCeti.IsIntegrallyClosed.of_faithfullyFlat A (AdicCompletion (maximalIdeal A) A)⟩,
    fun ⟨_, _⟩ ↦ ⟨inferInstance, inferInstance⟩⟩

/-! ### Checks -/

/-- For an integrally closed G-ring domain `R` and any prime `p`, the completed local ring `R̂_p`
is an integrally closed domain. -/
example (R : Type u) [CommRing R] [IsGRing R] [IsDomain R] [IsIntegrallyClosed R]
    (p : Ideal R) [p.IsPrime] :
    IsDomain (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) ∧
      IsIntegrallyClosed
        (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) :=
  have : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
  ⟨inferInstance, inferInstance⟩

/-- The dual numbers `k[ε]` over a field form a local G-ring whose completion map is regular and
whose completion satisfies `(S_n)` for all `n`, yet is not reduced because `k[ε]` is not reduced. -/
example (k : Type u) [Field k] (n : ℕ) :
    RegularAlgebraMap (DualNumber k)
        (AdicCompletion (maximalIdeal (DualNumber k)) (DualNumber k)) ∧
      Module.SatisfiesSerreS n (AdicCompletion (maximalIdeal (DualNumber k)) (DualNumber k))
        (AdicCompletion (maximalIdeal (DualNumber k)) (DualNumber k)) ∧
      ¬ IsReduced (AdicCompletion (maximalIdeal (DualNumber k)) (DualNumber k)) :=
  ⟨inferInstance,
    satisfiesSerreS_adicCompletion_iff.mpr .of_krullDimLE_zero,
    isReduced_adicCompletion_iff.not.mpr (DualNumber.not_isReduced (R := k))⟩

end TauCeti.Excellence.IsGRing
