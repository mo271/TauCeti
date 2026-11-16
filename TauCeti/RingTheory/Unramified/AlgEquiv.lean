/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Localization.Basic

/-!
# Unramifiedness at a prime transports along an isomorphism of algebras

`Algebra.IsUnramifiedAt R q` says that the localization of the ambient algebra at `q` is formally
unramified over `R`. An isomorphism `ψ : A ≃ₐ[R] B` of `R`-algebras matches the prime complement
of `q` with that of `q.comap ψ`, so it induces an isomorphism of the two localizations over `R`
and unramifiedness at `q` is equivalent to unramifiedness at `q.comap ψ`.

## Main results

* `AlgEquiv.isUnramifiedAt_iff_of_eq_comap`: `A` is unramified over `R` at a prime equal to
  `q.comap ψ` if and only if `B` is unramified over `R` at `q`.
* `AlgEquiv.isUnramifiedIn_iff`: an ideal of `R` is unramified in `A` if and only if it is
  unramified in `B`.
-/

public section

namespace AlgEquiv

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- **Unramifiedness transports along an isomorphism of `R`-algebras.** For a prime `q` of `B`,
`A` is unramified over `R` at the corresponding prime `q.comap ψ` if and only if `B` is unramified
over `R` at `q`, stated for any prime `p` of `A` equal to `q.comap ψ`. -/
theorem isUnramifiedAt_iff_of_eq_comap (ψ : A ≃ₐ[R] B) {q : Ideal B} [q.IsPrime]
    {p : Ideal A} [p.IsPrime] (hp : p = q.comap ψ) :
    Algebra.IsUnramifiedAt R p ↔ Algebra.IsUnramifiedAt R q := by
  -- The transported prime is the parameter `p` with the equation `hp`, not the term `q.comap ψ`
  -- itself: `Algebra.IsUnramifiedAt` takes the primality of its ideal as an instance argument, so
  -- `rw` cannot turn a statement about `q.comap ψ` into one about `p`, while `subst` can.
  subst hp
  exact Algebra.FormallyUnramified.iff_of_equiv (IsLocalization.algEquivOfAlgEquiv
    (Localization.AtPrime (q.comap ψ)) (Localization.AtPrime q) ψ
      (Ideal.map_primeCompl_comap_of_surjective ψ ψ.surjective q))

private theorem isUnramifiedIn_of_algEquiv (ψ : A ≃ₐ[R] B) {p : Ideal R}
    (h : Algebra.IsUnramifiedIn A p) : Algebra.IsUnramifiedIn B p := fun q _ hqp ↦
  have hlo : (q.comap ψ).LiesOver p := ⟨hqp.over.trans (by ext; simp)⟩
  (ψ.isUnramifiedAt_iff_of_eq_comap rfl).mp (h (q.comap ψ) inferInstance hlo)

/-- **Unramifiedness of a base ideal transports along an isomorphism of `R`-algebras.** -/
theorem isUnramifiedIn_iff (ψ : A ≃ₐ[R] B) (p : Ideal R) :
    Algebra.IsUnramifiedIn A p ↔ Algebra.IsUnramifiedIn B p :=
  ⟨isUnramifiedIn_of_algEquiv ψ, isUnramifiedIn_of_algEquiv ψ.symm⟩

end AlgEquiv
