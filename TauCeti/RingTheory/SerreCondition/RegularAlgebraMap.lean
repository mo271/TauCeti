/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.Ring
public import TauCeti.RingTheory.RegularLocalRing.RegularAlgebraMap
public import TauCeti.RingTheory.SerreCondition.Flat
import TauCeti.Algebra.DualNumber.Basic
import TauCeti.RingTheory.IntegralClosure.ReducedArtinian
import TauCeti.RingTheory.Localization.Reduced
import TauCeti.RingTheory.RegularLocalRing.Normal

/-!
# Serre's conditions, reducedness, and normality along regular ring maps

Let `R → B` be a regular ring map (`TauCeti.Excellence.RegularAlgebraMap R B`) with `B` Noetherian:
`B` is flat over `R` and every fibre `κ(p) ⊗[R] B` is geometrically regular over `κ(p)`, hence a
regular ring (`TauCeti.Excellence.GeometricallyRegular.isRegularRing`). Regular rings satisfy
Serre's conditions `(R_n)` and `(S_n)` for all `n`, are reduced, and have integrally closed domain
localizations at all primes (`TauCeti.IsRegularRing.isIntegrallyClosed`). Applying the flat ascent
theorems of `TauCeti.RingTheory.SerreCondition.Flat` therefore shows that a regular ring map with
Noetherian target preserves:

* Serre's conditions `(R_n)` and `(S_n)` and Cohen–Macaulayness (Stacks, Lemma 15.43.1 (`07QK`));
* reducedness (Stacks, Lemma 15.43.2 (`0BFK`));
* normality, both stalkwise (every localization `B_q` at a prime is an integrally closed domain) and
  globally (`IsIntegrallyClosed B`), from either stalkwise normality of `R` or
  `[IsNoetherianRing R] [IsReduced R] [IsIntegrallyClosed R]` (Stacks, Lemma 15.43.3 (`0H7S`)).

The stalkwise ascent theorems and `RegularAlgebraMap.isReduced` do not require `R` to be globally
Noetherian: at each prime `q` of `B` lying over `p`, `R_p` is Noetherian by faithful flatness of
`R_p → B_q`.

## Main results

* `TauCeti.Excellence.RegularAlgebraMap.satisfiesSerreR`,
  `TauCeti.Excellence.RegularAlgebraMap.satisfiesSerreS`, and
  `TauCeti.Excellence.RegularAlgebraMap.isCohenMacaulay`: `(R_n)`, `(S_n)`, and Cohen–Macaulayness
  ascend along regular ring maps with Noetherian target (Stacks, Lemma 15.43.1 (`07QK`)).
* `TauCeti.Excellence.RegularAlgebraMap.isReduced`: reducedness ascends along regular ring maps
  with Noetherian target (Stacks, Lemma 15.43.2 (`0BFK`)).
* `TauCeti.Excellence.RegularAlgebraMap.isDomain_localization_atPrime`,
  `TauCeti.Excellence.RegularAlgebraMap.isIntegrallyClosed_localization_atPrime`, and
  `TauCeti.Excellence.RegularAlgebraMap.isIntegrallyClosed_of_forall_localization`: stalkwise and
  global normality ascend along regular ring maps from stalkwise normal bases (Stacks,
  Lemma 15.43.3 (`0H7S`)).
* `RegularAlgebraMap.isDomain_localization_atPrime_of_isIntegrallyClosed`,
  `RegularAlgebraMap.isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed`, and
  `RegularAlgebraMap.isIntegrallyClosed`: convenience forms when `R` is a reduced integrally closed
  Noetherian ring (such as any Noetherian integrally closed domain).

## References

* [Stacks Project, Section 15.43](https://stacks.math.columbia.edu/tag/07QJ): Lemmas 15.43.1
  (`07QK`), 15.43.2 (`0BFK`), and 15.43.3 (`0H7S`).
-/

public section

universe u v

namespace TauCeti.Excellence.RegularAlgebraMap

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- **Serre's condition `(R_n)` ascends along regular ring maps.** If `R → B` is a regular ring map
with `B` Noetherian and `R` satisfies `(R_n)`, then `B` satisfies `(R_n)`.
Stacks, Lemma 15.43.1 (07QK). -/
@[stacks 07QK "(R_n) part"]
theorem satisfiesSerreR {n : ℕ} [IsNoetherianRing B] [RegularAlgebraMap R B]
    (hR : Ring.SatisfiesSerreR n R) : Ring.SatisfiesSerreR n B :=
  hR.of_flat fun p _ ↦
    have := GeometricallyRegular.isRegularRing p.ResidueField (B := p.Fiber B)
    _root_.IsRegularRing.satisfiesSerreR n

/-- **Serre's condition `(S_n)` ascends along regular ring maps.** If `R → B` is a regular ring map
with `B` Noetherian and `R` satisfies `(S_n)`, then `B` satisfies `(S_n)`.
Stacks, Lemma 15.43.1 (07QK). -/
@[stacks 07QK "(S_n) part"]
theorem satisfiesSerreS {n : ℕ} [IsNoetherianRing B] [RegularAlgebraMap R B]
    (hR : Module.SatisfiesSerreS n R R) : Module.SatisfiesSerreS n B B :=
  hR.of_flat fun p _ ↦
    have := GeometricallyRegular.isRegularRing p.ResidueField (B := p.Fiber B)
    _root_.IsRegularRing.satisfiesSerreS n

/-- **Cohen–Macaulayness ascends along regular ring maps.** A Noetherian regular algebra over a
Cohen–Macaulay ring is Cohen–Macaulay. Stacks, Lemma 15.43.1 (07QK). -/
@[stacks 07QK "Cohen–Macaulay part"]
theorem isCohenMacaulay [TauCeti.Ring.IsCohenMacaulay R] [IsNoetherianRing B]
    [RegularAlgebraMap R B] : TauCeti.Ring.IsCohenMacaulay B :=
  TauCeti.Ring.isCohenMacaulay_iff_forall_satisfiesSerreS.2 fun n ↦
    satisfiesSerreS (TauCeti.Ring.isCohenMacaulay_iff_forall_satisfiesSerreS.1 ‹_› n)

/-- **Reducedness ascends along regular ring maps.** A Noetherian regular algebra over a reduced
ring is reduced. Stacks, Lemma 15.43.2 (0BFK). -/
@[stacks 0BFK]
theorem isReduced [IsReduced R] [IsNoetherianRing B] [RegularAlgebraMap R B] : IsReduced B :=
  TauCeti.isReduced_of_flat_of_isReduced_fiber (R := R) fun p _ ↦
    have := GeometricallyRegular.isRegularRing p.ResidueField (B := p.Fiber B)
    inferInstance

/-- Every localization at a prime of a reduced integrally closed Noetherian ring is an integrally
closed domain, since its total ring of fractions is reduced and Artinian. -/
private theorem isDomain_and_isIntegrallyClosed_localization_of_isReduced
    [IsNoetherianRing R] [IsReduced R] [IsIntegrallyClosed R] (p : Ideal R) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  have : IsArtinianRing (FractionRing R) := IsFractionRing.isArtinianRing_of_isReduced R _
  have : IsReduced (FractionRing R) := IsLocalization.isReduced (nonZeroDivisors R) _
  exact ⟨IsIntegrallyClosedIn.isDomain_localization_atPrime (FractionRing R) p,
    IsIntegrallyClosedIn.isIntegrallyClosed_localization_atPrime (FractionRing R) p⟩

/-- **Normality ascends along regular ring maps (domain part).** If `R → B` is a regular ring map
with `B` Noetherian and every localization `R_p` at a prime is an integrally closed domain, then
every localization `B_q` at a prime is a domain. Stacks, Lemma 15.43.3 (0H7S). -/
@[stacks 0H7S "domain part"]
theorem isDomain_localization_atPrime [IsNoetherianRing B] [RegularAlgebraMap R B]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (q : Ideal B) [q.IsPrime] : IsDomain (Localization.AtPrime q) :=
  TauCeti.isDomain_localization_atPrime_of_flat hR
    (fun p _ Q _ ↦
      have := GeometricallyRegular.isRegularRing p.ResidueField (B := p.Fiber B)
      isDomain_and_isIntegrallyClosed_localization_of_isReduced (R := p.Fiber B) Q)
    q

/-- **Normality ascends along regular ring maps (integral closedness of localizations).** If
`R → B` is a regular ring map with `B` Noetherian and every localization `R_p` at a prime is an
integrally closed domain, then every localization `B_q` at a prime is integrally closed.
Stacks, Lemma 15.43.3 (0H7S). -/
@[stacks 0H7S "integrally closed localization part"]
theorem isIntegrallyClosed_localization_atPrime [IsNoetherianRing B] [RegularAlgebraMap R B]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (q : Ideal B) [q.IsPrime] : IsIntegrallyClosed (Localization.AtPrime q) :=
  TauCeti.isIntegrallyClosed_localization_atPrime_of_flat hR
    (fun p _ Q _ ↦
      have := GeometricallyRegular.isRegularRing p.ResidueField (B := p.Fiber B)
      isDomain_and_isIntegrallyClosed_localization_of_isReduced (R := p.Fiber B) Q)
    q

/-- **Global integral closedness ascends along regular ring maps from stalkwise normal bases.** If
`R → B` is a regular ring map with `B` Noetherian and every localization `R_p` at a prime is an
integrally closed domain, then `B` is integrally closed in its total ring of fractions.
Stacks, Lemma 15.43.3 (0H7S). -/
@[stacks 0H7S "global integral closedness from stalks"]
theorem isIntegrallyClosed_of_forall_localization [IsNoetherianRing B] [RegularAlgebraMap R B]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed B :=
  TauCeti.isIntegrallyClosed_of_flat hR fun p _ Q _ ↦
    have := GeometricallyRegular.isRegularRing p.ResidueField (B := p.Fiber B)
    isDomain_and_isIntegrallyClosed_localization_of_isReduced (R := p.Fiber B) Q

/-- **Normality ascends along regular ring maps over reduced integrally closed Noetherian rings
(domain part).** Stacks, Lemma 15.43.3 (0H7S). -/
@[stacks 0H7S "domain part for reduced integrally closed base"]
theorem isDomain_localization_atPrime_of_isIntegrallyClosed [IsNoetherianRing R] [IsReduced R]
    [IsIntegrallyClosed R] [IsNoetherianRing B] [RegularAlgebraMap R B]
    (q : Ideal B) [q.IsPrime] : IsDomain (Localization.AtPrime q) :=
  isDomain_localization_atPrime (fun p _ ↦
    isDomain_and_isIntegrallyClosed_localization_of_isReduced (R := R) p) q

/-- **Normality ascends along regular ring maps over reduced integrally closed Noetherian rings
(integral closedness of localizations).** Stacks, Lemma 15.43.3 (0H7S). -/
@[stacks 0H7S "integrally closed localization part for reduced integrally closed base"]
theorem isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed [IsNoetherianRing R]
    [IsReduced R] [IsIntegrallyClosed R] [IsNoetherianRing B] [RegularAlgebraMap R B]
    (q : Ideal B) [q.IsPrime] : IsIntegrallyClosed (Localization.AtPrime q) :=
  isIntegrallyClosed_localization_atPrime (fun p _ ↦
    isDomain_and_isIntegrallyClosed_localization_of_isReduced (R := R) p) q

/-- **Integral closedness ascends along regular ring maps over reduced integrally closed Noetherian
rings.** If `R` is a reduced integrally closed Noetherian ring (for example any Noetherian
integrally closed domain) and `B` is a Noetherian regular `R`-algebra, then `B` is integrally
closed in its total ring of fractions. Stacks, Lemma 15.43.3 (0H7S). -/
@[stacks 0H7S "global integral closedness"]
theorem isIntegrallyClosed [IsNoetherianRing R] [IsReduced R] [IsIntegrallyClosed R]
    [IsNoetherianRing B] [RegularAlgebraMap R B] : IsIntegrallyClosed B :=
  isIntegrallyClosed_of_forall_localization (R := R) fun p _ ↦
    isDomain_and_isIntegrallyClosed_localization_of_isReduced (R := R) p

/-! ### Checks -/

/-- A polynomial ring in finitely many variables over a reduced integrally closed Noetherian ring is
smooth, hence a regular algebra, so it is reduced and integrally closed with normal local rings. -/
example (R : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R] [IsIntegrallyClosed R]
    (m : ℕ) (q : Ideal (MvPolynomial (Fin m) R)) [q.IsPrime] :
    IsReduced (MvPolynomial (Fin m) R) ∧ IsIntegrallyClosed (MvPolynomial (Fin m) R) ∧
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) :=
  ⟨isReduced (R := R), isIntegrallyClosed (R := R),
    isDomain_localization_atPrime_of_isIntegrallyClosed (R := R) q,
    isIntegrallyClosed_localization_atPrime_of_isIntegrallyClosed (R := R) q⟩

/-- Regularity of `R → B` (rather than flatness alone) is needed in `RegularAlgebraMap.isReduced`:
the dual numbers `k[ε]` are flat and Noetherian over the field `k`, yet neither regular over `k`
nor reduced. -/
example (k : Type u) [Field k] :
    Module.Flat k (DualNumber k) ∧ ¬ RegularAlgebraMap k (DualNumber k) ∧
      ¬ IsReduced (DualNumber k) :=
  ⟨Module.Flat.of_free,
    fun _ ↦ DualNumber.not_isReduced (R := k) (isReduced (R := k)),
    DualNumber.not_isReduced (R := k)⟩

end TauCeti.Excellence.RegularAlgebraMap
