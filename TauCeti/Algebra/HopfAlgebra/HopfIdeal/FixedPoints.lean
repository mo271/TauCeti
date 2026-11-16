/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Equalizer
public import TauCeti.RingTheory.Invariant.FixedPointIdeal

/-!
# The fixed-point Hopf ideal of a family of bialgebra endomorphisms

Let `f : ι → (H →ₐc[R] H)` be a family of bialgebra endomorphisms of a commutative Hopf algebra `H`
over a commutative ring `R`. The **fixed-point Hopf ideal** `HopfIdeal.fixedPoints f` is the
supremum `⨆ i, equalizer (f i) (BialgHom.id R H)` of the equalizer Hopf ideals of the individual
endomorphisms with the identity.

Its underlying ideal is spanned by all displacements `f i a - a` (`fixedPoints_toIdeal`), hence
coincides with `TauCeti.MulSemiringAction.fixedPointIdeal G H` whenever a type `G` acts on `H`
through `f` (`fixedPoints_toIdeal_eq_fixedPointIdeal`). Contravariantly, when `H` is commutative,
the quotient `H ⧸ (fixedPoints f).toIdeal` is the coordinate Hopf algebra of the closed subgroup
scheme of `Spec H` fixed by every `f i`; see
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.FixedPoints` for the categorical and functor-of-points
formulation.

## Main declarations

* `TauCeti.HopfIdeal.fixedPoints`: the Hopf ideal `⨆ i, equalizer (f i) (BialgHom.id R H)`.
* `TauCeti.HopfIdeal.fixedPoints_toIdeal` and
  `TauCeti.HopfIdeal.fixedPoints_toIdeal_eq_fixedPointIdeal`: identification of the underlying
  ideal with the displacement span and with `TauCeti.MulSemiringAction.fixedPointIdeal`.
* `TauCeti.HopfIdeal.fixedPoints_le_iff`, `TauCeti.HopfIdeal.fixedPoints_le_ker_iff`, and
  `TauCeti.HopfIdeal.fixedPoints_eq_bot_iff`: universal property, kernel criterion, and vanishing
  characterization.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), Proposition 3.1,
  p. 293.
* J. S. Milne, *Algebraic Groups* (2017), §1.h.
-/

public section

namespace TauCeti

universe u v w

namespace HopfIdeal

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [_root_.HopfAlgebra R H]
  {ι : Type w}

/-- The **fixed-point Hopf ideal** of a family `f : ι → (H →ₐc[R] H)` of bialgebra endomorphisms of
a commutative Hopf algebra: the supremum of the equalizer Hopf ideals
`equalizer (f i) (BialgHom.id R H)`. Contravariantly, `H ⧸ (fixedPoints f).toIdeal` is the
coordinate Hopf algebra of the closed subgroup scheme of points fixed by every `f i`. -/
noncomputable def fixedPoints (f : ι → (H →ₐc[R] H)) : HopfIdeal R H :=
  ⨆ i, equalizer (f i) (BialgHom.id R H)

/-- `fixedPoints f` is the supremum of the individual equalizer Hopf ideals with the identity. -/
theorem fixedPoints_eq_iSup (f : ι → (H →ₐc[R] H)) :
    fixedPoints f = ⨆ i, equalizer (f i) (BialgHom.id R H) :=
  (rfl)

/-- The ideal underlying `fixedPoints f` is spanned by all displacements `f i a - a`. -/
@[simp]
theorem fixedPoints_toIdeal (f : ι → (H →ₐc[R] H)) :
    (fixedPoints f).toIdeal = Ideal.span {y : H | ∃ (i : ι) (a : H), f i a - a = y} := by
  rw [fixedPoints_eq_iSup, iSup_toIdeal]
  apply le_antisymm
  · refine iSup_le fun i ↦ ?_
    rw [equalizer_toIdeal, equalizerIdeal_le_iff]
    exact fun a ↦ Ideal.subset_span ⟨i, a, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨i, a, rfl⟩
    have hsub := sub_mem_equalizerIdeal (f i) (BialgHom.id R H) a
    rw [BialgHom.id_apply, ← equalizer_toIdeal] at hsub
    exact Submodule.mem_iSup_of_mem i hsub

/-- When a type `G` acts on `H` through a family of bialgebra endomorphisms `f`, the ideal
underlying `HopfIdeal.fixedPoints f` coincides with `MulSemiringAction.fixedPointIdeal G H`. -/
theorem fixedPoints_toIdeal_eq_fixedPointIdeal {G : Type w} [SMul G H] (f : G → (H →ₐc[R] H))
    (hf : ∀ (g : G) (a : H), g • a = f g a) :
    (fixedPoints f).toIdeal = MulSemiringAction.fixedPointIdeal G H := by
  rw [fixedPoints_toIdeal, MulSemiringAction.fixedPointIdeal_def]
  simp_rw [hf]

/-- Every displacement `f i a - a` belongs to `fixedPoints f`. -/
theorem sub_mem_fixedPoints (f : ι → (H →ₐc[R] H)) (i : ι) (a : H) :
    f i a - a ∈ fixedPoints f := by
  rw [← mem_toIdeal, fixedPoints_toIdeal]
  exact Ideal.subset_span ⟨i, a, rfl⟩

/-- Universal property of `fixedPoints f` among Hopf ideals of `H`. -/
theorem fixedPoints_le_iff {f : ι → (H →ₐc[R] H)} {J : HopfIdeal R H} :
    fixedPoints f ≤ J ↔ ∀ (i : ι) (a : H), f i a - a ∈ J := by
  rw [← toIdeal_le_toIdeal, fixedPoints_eq_iSup, iSup_toIdeal, iSup_le_iff]
  exact forall_congr' fun i ↦ by
    rw [toIdeal_le_toIdeal, equalizer_le_iff]
    simp only [BialgHom.id_apply]

/-- A ring homomorphism out of `H` kills `fixedPoints f` if and only if it equalizes every `f i`
with the identity. -/
theorem fixedPoints_le_ker_iff {A : Type*} [Ring A] (f : ι → (H →ₐc[R] H)) (φ : H →+* A) :
    (fixedPoints f).toIdeal ≤ RingHom.ker φ ↔ ∀ (i : ι) (a : H), φ (f i a) = φ a := by
  rw [fixedPoints_eq_iSup, iSup_toIdeal, iSup_le_iff]
  exact forall_congr' fun _ ↦ equalizer_le_ker_iff φ

/-- `fixedPoints f` vanishes if and only if every `f i` is the identity bialgebra morphism. -/
@[simp]
theorem fixedPoints_eq_bot_iff (f : ι → (H →ₐc[R] H)) :
    fixedPoints f = ⊥ ↔ ∀ i, f i = BialgHom.id R H := by
  rw [eq_bot_iff, fixedPoints_le_iff]
  simp only [mem_bot, sub_eq_zero, BialgHom.ext_iff, BialgHom.id_apply]

end HopfIdeal

end TauCeti
