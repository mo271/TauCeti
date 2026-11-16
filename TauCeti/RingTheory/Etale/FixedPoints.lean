/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import TauCeti.RingTheory.Invariant.FixedPointIdeal

/-!
# Étaleness of fixed-point schemes under monoid actions

Let a monoid `M` act on a commutative `R`-algebra `A` by `R`-algebra endomorphisms. Unlike formal
smoothness (`TauCeti.RingTheory.Smooth.FixedPoints`), formal étaleness of the fixed-point quotient
`A ⧸ fixedPointIdeal M A` requires neither a group structure on `M` nor invertibility of its
cardinality: given a square-zero ideal `J` of a commutative `R`-algebra `B` and a morphism
`f : (A ⧸ fixedPointIdeal M A) →ₐ[R] B ⧸ J`, formal smoothness of `A` supplies an infinitesimal lift
`l : A →ₐ[R] B` of `f ∘ mk`, and formal unramifiedness of `A` makes `l` unique, hence automatically
`M`-invariant (`formallyEtale_quotient_fixedPointIdeal`). Combining this with finite presentation
of the quotient when `M` is finite
(`TauCeti.MulSemiringAction.finitePresentation_quotient_fixedPointIdeal`) shows that fixed-point
quotients of étale `R`-algebras under finite monoids are étale over `R`
(`etale_quotient_fixedPointIdeal`).

## Main results

* `TauCeti.MulSemiringAction.formallyEtale_quotient_fixedPointIdeal`: for any monoid `M` acting by
  `R`-algebra endomorphisms on a formally étale `R`-algebra `A`, `A ⧸ fixedPointIdeal M A` is
  formally étale over `R`.
* `TauCeti.MulSemiringAction.etale_quotient_fixedPointIdeal`: if `M` is finite and `A` is étale
  over `R`, then `A ⧸ fixedPointIdeal M A` is étale over `R`.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Propositions 3.1
  and 3.4, pp. 293–295.
-/

public section

namespace TauCeti.MulSemiringAction

variable {R M A : Type*} [CommRing R] [Monoid M] [CommRing A] [Algebra R A]
  [MulSemiringAction M A] [SMulCommClass M R A]

/-- For any monoid `M` acting by `R`-algebra endomorphisms on a formally étale `R`-algebra `A`,
the fixed-point quotient `A ⧸ fixedPointIdeal M A` is formally étale over `R`, with no finiteness
or invertibility assumption on `M`. -/
instance formallyEtale_quotient_fixedPointIdeal [Algebra.FormallyEtale R A] :
    Algebra.FormallyEtale R (A ⧸ fixedPointIdeal M A) := by
  set I := fixedPointIdeal M A
  have : Algebra.FormallySmooth R (A ⧸ I) := by
    refine Algebra.FormallySmooth.iff_comp_surjective.mpr fun B _ _ J hJ fbar ↦ ?_
    obtain ⟨l, hl⟩ :=
      Algebra.FormallySmooth.comp_surjective R A J hJ (fbar.comp (Ideal.Quotient.mkₐ R I))
    have hinv (m : M) : l.comp (MulSemiringAction.toAlgHom R A m) = l := by
      apply Algebra.FormallyUnramified.comp_injective J hJ
      ext a
      have hm := congr($hl (m • a))
      have ha := congr($hl a)
      simp only [AlgHom.comp_apply, MulSemiringAction.toAlgHom_apply,
        Ideal.Quotient.mkₐ_eq_mk] at hm ha ⊢
      rw [hm, ha, mk_fixedPointIdeal_smul]
    refine ⟨(quotientFixedPointIdealAlgHomEquiv R M A B).symm
      ⟨l, fun m a ↦ congr($(hinv m) a)⟩, ?_⟩
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [I, AlgHom.comp_apply, quotientFixedPointIdealAlgHomEquiv_symm_apply_mk]
    exact congr($hl a)
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

/-- For any finite monoid `M` acting by `R`-algebra endomorphisms on an étale `R`-algebra `A`,
the fixed-point quotient `A ⧸ fixedPointIdeal M A` is étale over `R`. -/
instance etale_quotient_fixedPointIdeal [Finite M] [Algebra.Etale R A] :
    Algebra.Etale R (A ⧸ fixedPointIdeal M A) where
  formallyEtale := inferInstance
  finitePresentation := inferInstance

end TauCeti.MulSemiringAction
