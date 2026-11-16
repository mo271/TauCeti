/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.ExtendedHom

/-!
# Extension of ideal classes

Mathlib's computation of `ClassGroup.extendedHom` on fractional ideals uses the canonical
fraction fields. Here the same comparison is established for any fraction fields, so it can
be used with the fractional ideals attached to finite ideles.

For an extension from a Dedekind domain `R` into an arbitrary integral domain `B`, we also
characterize when `ClassGroup.extendedHom R B` vanishes: the class of a nonzero ideal `I` maps
to `1` iff `I.map (algebraMap R B)` is principal (`ClassGroup.extendedHom_mk0_eq_one_iff`), so
`ClassGroup.extendedHom R B = 1` if and only if every ideal of `R` becomes principal in `B`
(`ClassGroup.extendedHom_eq_one_iff_forall_isPrincipal`).

## Main results

* `ClassGroup.extendedHom_mk_of_isFractionRing`: extension of fractional-ideal classes over
  arbitrary fraction fields.
* `ClassGroup.extendedHom_mk0_eq_one_iff`: a nonzero ideal class of a Dedekind domain maps to `1`
  in an integral domain extension iff the extended ideal is principal.
* `ClassGroup.extendedHom_eq_one_iff_forall_isPrincipal`: `ClassGroup.extendedHom R B = 1` iff
  every ideal of `R` becomes principal in `B`.
-/

public section

open scoped nonZeroDivisors

namespace ClassGroup

section FractionRing

variable {R B K L : Type*} [CommRing R] [IsDomain R]
  [CommRing B] [IsDomain B] [Algebra R B] [Module.IsTorsionFree R B]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra B L] [IsFractionRing B L]

/-- Extension of an ideal class can be computed using any choices of fraction fields. -/
theorem extendedHom_mk_of_isFractionRing (I : (FractionalIdeal R⁰ K)ˣ) :
    extendedHom R B (mk K I) = mk L
      (Units.map (FractionalIdeal.extendedHom L B :
        FractionalIdeal R⁰ K →+* FractionalIdeal B⁰ L).toMonoidHom I) := by
  have h (J : FractionalIdeal R⁰ K) :
      FractionalIdeal.extendedHom (FractionRing B) B
          (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R) J) =
        FractionalIdeal.canonicalEquiv B⁰ L (FractionRing B)
          (FractionalIdeal.extendedHom L B J) := by
    obtain ⟨a, A, _, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J
    simp only [map_mul, FractionalIdeal.canonicalEquiv_spanSingleton,
      FractionalIdeal.canonicalEquiv_coeIdeal, FractionalIdeal.extendedHom_spanSingleton,
      FractionalIdeal.extendedHom_coeIdeal_eq_map]
    simp only [IsFractionRing.map, map_inv₀]
    -- The proof argument introduced by canonicalEquiv_spanSingleton requires unfolding
    -- Submonoid membership beyond the transparency used by rw.
    erw [IsLocalization.map_eq, IsLocalization.map_eq, IsLocalization.map_eq,
      IsLocalization.map_eq]
    rfl
  rw [← mk_canonicalEquiv K (FractionRing R) I, extendedHom_mk,
    ← mk_canonicalEquiv L (FractionRing B)]
  apply congrArg (mk (FractionRing B))
  apply Units.ext
  exact h I

end FractionRing

section DedekindDomain

variable {R B : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing B] [IsDomain B] [Algebra R B] [Module.IsTorsionFree R B]

/-- The class of a nonzero ideal of a Dedekind domain `R` maps to `1` in `ClassGroup B` if and
only if the extended ideal in `B` is principal. Unlike `ClassGroup.extendedHom_mk0`, the target
domain `B` need not be a Dedekind domain. -/
theorem extendedHom_mk0_eq_one_iff (I : (Ideal R)⁰) :
    extendedHom R B (mk0 I) = 1 ↔ (I.1.map (algebraMap R B)).IsPrincipal := by
  rw [extendedHom_mk0', mk_eq_one_iff]
  have hcoe :
      ((Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom
          (FractionalIdeal.mk0 (FractionRing R) I) :
            (FractionalIdeal B⁰ (FractionRing B))ˣ) : Submodule B (FractionRing B)) =
        IsLocalization.coeSubmodule (FractionRing B) (I.1.map (algebraMap R B)) := by
    simp [Units.coe_map]
  rw [hcoe]
  exact IsLocalization.coeSubmodule_isPrincipal (FractionRing B) le_rfl

variable (R B) in
/-- Extension of ideal classes from a Dedekind domain `R` to an integral domain `B` is trivial
if and only if every ideal of `R` becomes principal in `B`. This is the two-sided form of
Mathlib's `ClassGroup.extendedHom_eq_one_of_forall_isPrincipal`, without requiring `B` to be a
Dedekind domain. -/
theorem extendedHom_eq_one_iff_forall_isPrincipal :
    extendedHom R B = 1 ↔ ∀ I : Ideal R, (I.map (algebraMap R B)).IsPrincipal := by
  refine ⟨fun h I ↦ ?_, fun h ↦ ?_⟩
  · rcases eq_or_ne I ⊥ with rfl | hI
    · rw [Ideal.map_bot]
      exact bot_isPrincipal
    · exact (extendedHom_mk0_eq_one_iff ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩).mp
        (by simp [h])
  · ext x
    obtain ⟨I, rfl⟩ := mk0_surjective x
    exact (extendedHom_mk0_eq_one_iff I).mpr (h I.1)

end DedekindDomain

end ClassGroup
