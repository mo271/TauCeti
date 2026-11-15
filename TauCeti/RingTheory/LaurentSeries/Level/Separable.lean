/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field
public import TauCeti.RingTheory.LaurentSeries.Level.Adjoin

/-!
# Coefficient-field algebra and separability of ramified Laurent levels

For a field `K` and a positive integer `d`, the ramified Laurent level `Level K d = K⸨u⸩` with
`u ^ d = X` is a `K`-algebra via its underlying Laurent-series coordinate `u`, forming a scalar
tower `K → K⸨X⸩ → Level K d`. Reading elements in the level parameter upgrades
`Level.ringEquivLaurentSeries` to a `K`-algebra equivalence `Level.algEquivLaurentSeries`.

Over `K⸨X⸩`, the level parameter `u` has minimal polynomial `T ^ d - X`, which is separable if and
only if `d` is nonzero in `K`. Consequently both the wrapped level `Level K d` and the actual
level-`d` subfield `puiseuxField.level K d` are separable — hence formally étale — extensions of
`K⸨X⸩` whenever `[NeZero ((d : ℕ) : K)]`, with exact biconditional characterizations in arbitrary
characteristic.
-/

public section

open Polynomial
open scoped LaurentSeries

namespace TauCeti.LaurentSeries

namespace Level

variable (K : Type*) [Field K] (d : ℕ+)

/-- Level `d` is a `K`-algebra through its underlying Laurent series in the level parameter `u`. -/
noncomputable instance : Algebra K (Level K d) where
  __ := (ringEquivLaurentSeries K d).toAddEquiv.module K
  algebraMap := (ringEquivLaurentSeries K d).symm.toRingHom.comp (Algebra.algebraMap K K⸨X⸩)
  commutes' _ _ := mul_comm _ _
  smul_def' c x := by
    apply (ringEquivLaurentSeries K d).injective
    have hc : c • ringEquivLaurentSeries K d x =
        Algebra.algebraMap K K⸨X⸩ c * ringEquivLaurentSeries K d x := by
      rw [← HahnSeries.C_mul_eq_smul, ← _root_.LaurentSeries.algebraMap_apply]
    simpa [Equiv.smul_def] using hc

@[simp]
theorem ringEquivLaurentSeries_algebraMap_coeff (c : K) :
    ringEquivLaurentSeries K d (Algebra.algebraMap K (Level K d) c) =
      Algebra.algebraMap K K⸨X⸩ c :=
  (ringEquivLaurentSeries K d).apply_symm_apply _

@[simp]
theorem ringEquivLaurentSeries_coeff_smul (c : K) (x : Level K d) :
    ringEquivLaurentSeries K d (c • x) = c • ringEquivLaurentSeries K d x :=
  (ringEquivLaurentSeries K d).apply_symm_apply _

/-- The `K`-algebra structure on `Level K d` factors through the base Laurent field `K⸨X⸩`. -/
instance : IsScalarTower K K⸨X⸩ (Level K d) where
  smul_assoc c f x := by
    apply (ringEquivLaurentSeries K d).injective
    rw [Algebra.smul_def (c • f), Algebra.smul_def f, ringEquivLaurentSeries_coeff_smul,
      map_mul, map_mul, algebraMap_apply, algebraMap_apply,
      ← HahnSeries.C_mul_eq_smul, ← _root_.LaurentSeries.algebraMap_apply,
      map_mul, AlgHom.commutes, mul_assoc,
      ← HahnSeries.C_mul_eq_smul, ← _root_.LaurentSeries.algebraMap_apply]

/-- Reading a ramified level in its level parameter `u` is a `K`-algebra equivalence with `K⸨X⸩`. -/
noncomputable def algEquivLaurentSeries : Level K d ≃ₐ[K] K⸨X⸩ :=
  AlgEquiv.ofRingEquiv (f := ringEquivLaurentSeries K d)
    (ringEquivLaurentSeries_algebraMap_coeff K d)

@[simp]
theorem toRingEquiv_algEquivLaurentSeries :
    (algEquivLaurentSeries K d).toRingEquiv = ringEquivLaurentSeries K d :=
  (rfl)

@[simp]
theorem algEquivLaurentSeries_apply (x : Level K d) :
    algEquivLaurentSeries K d x = ringEquivLaurentSeries K d x :=
  (rfl)

@[simp]
theorem algEquivLaurentSeries_symm_apply (f : K⸨X⸩) :
    (algEquivLaurentSeries K d).symm f = (ringEquivLaurentSeries K d).symm f :=
  (rfl)

end Level

/-- The radical polynomial `T ^ d - X` over `K⸨X⸩` is separable if and only if `d ≠ 0` in `K`. -/
theorem separable_X_pow_sub_C_single_iff (K : Type*) [Field K] (d : ℕ+) :
    (X ^ (d : ℕ) - C (HahnSeries.single 1 1) : K⸨X⸩[X]).Separable ↔ ((d : ℕ) : K) ≠ 0 := by
  rw [X_pow_sub_C_separable_iff d.pos (HahnSeries.single_ne_zero one_ne_zero),
    ← map_natCast (algebraMap K K⸨X⸩), map_ne_zero_iff _ (algebraMap K K⸨X⸩).injective]

/-- When `d` is nonzero in `K`, the radical polynomial `T ^ d - X` is separable over `K⸨X⸩`. -/
theorem separable_X_pow_sub_C_single (K : Type*) [Field K] (d : ℕ+) [NeZero ((d : ℕ) : K)] :
    (X ^ (d : ℕ) - C (HahnSeries.single 1 1) : K⸨X⸩[X]).Separable :=
  (separable_X_pow_sub_C_single_iff K d).mpr (NeZero.ne _)

namespace Level

variable (K : Type*) [Field K] (d : ℕ+)

/-- The level parameter `u` is separable over `K⸨X⸩` if and only if `d` is nonzero in `K`. -/
theorem isSeparable_parameter_iff :
    IsSeparable K⸨X⸩ (parameter K d) ↔ ((d : ℕ) : K) ≠ 0 := by
  rw [IsSeparable, minpoly_parameter, separable_X_pow_sub_C_single_iff]

/-- The ramified level `Level K d` is separable over `K⸨X⸩` if and only if `d` is nonzero in `K`. -/
theorem isSeparable_iff :
    Algebra.IsSeparable K⸨X⸩ (Level K d) ↔ ((d : ℕ) : K) ≠ 0 := by
  rw [← isSeparable_parameter_iff K d]
  refine ⟨fun _ ↦ Algebra.IsSeparable.isSeparable K⸨X⸩ (parameter K d), fun h ↦ ?_⟩
  have hadj : Algebra.IsSeparable K⸨X⸩
      (IntermediateField.adjoin K⸨X⸩ ({parameter K d} : Set (Level K d))) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K⸨X⸩ (Level K d)).mpr h
  rw [adjoin_parameter_eq_top] at hadj
  exact AlgEquiv.Algebra.isSeparable IntermediateField.topEquiv

/-- The ramified level `Level K d` is formally étale over `K⸨X⸩` if and only if `d` is nonzero in
`K`. -/
theorem formallyEtale_iff :
    Algebra.FormallyEtale K⸨X⸩ (Level K d) ↔ ((d : ℕ) : K) ≠ 0 := by
  rw [Algebra.FormallyEtale.iff_isSeparable, isSeparable_iff]

section NeZero

variable [NeZero ((d : ℕ) : K)]

/-- When `d` is nonzero in `K`, the level parameter `u` is separable over `K⸨X⸩`. -/
theorem isSeparable_parameter : IsSeparable K⸨X⸩ (parameter K d) :=
  (isSeparable_parameter_iff K d).mpr (NeZero.ne _)

instance : Algebra.IsSeparable K⸨X⸩ (Level K d) :=
  (isSeparable_iff K d).mpr (NeZero.ne _)

instance : Algebra.FormallyEtale K⸨X⸩ (Level K d) :=
  .of_isSeparable K⸨X⸩ (Level K d)

end NeZero

end Level

end TauCeti.LaurentSeries

namespace TauCeti.puiseuxField

variable (K : Type*) [Field K] (d : ℕ+)

/-- The level-`d` subfield of the Puiseux field is separable over `K⸨X⸩` if and only if `d` is
nonzero in `K`. -/
theorem isSeparable_level_iff :
    Algebra.IsSeparable K⸨X⸩ (level K d) ↔ ((d : ℕ) : K) ≠ 0 := by
  rw [← AlgEquiv.Algebra.isSeparable_iff (levelEquiv K d), LaurentSeries.Level.isSeparable_iff]

/-- The level-`d` subfield of the Puiseux field is formally étale over `K⸨X⸩` if and only if `d` is
nonzero in `K`. -/
theorem formallyEtale_level_iff :
    Algebra.FormallyEtale K⸨X⸩ (level K d) ↔ ((d : ℕ) : K) ≠ 0 := by
  rw [← Algebra.FormallyEtale.iff_of_equiv (levelEquiv K d),
    LaurentSeries.Level.formallyEtale_iff]

section NeZero

variable [NeZero ((d : ℕ) : K)]

instance : Algebra.IsSeparable K⸨X⸩ (level K d) :=
  AlgEquiv.Algebra.isSeparable (levelEquiv K d)

instance : Algebra.FormallyEtale K⸨X⸩ (level K d) :=
  .of_isSeparable K⸨X⸩ (level K d)

end NeZero

end TauCeti.puiseuxField
