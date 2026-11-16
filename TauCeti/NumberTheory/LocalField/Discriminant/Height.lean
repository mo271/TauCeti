/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different.Wild
public import TauCeti.NumberTheory.LocalField.Discriminant.Basic

/-!
# Ramification height and mean of an extension of local fields

Let `L/K` be a finite separable extension of nonarchimedean local fields with ramification index
`e = e(L/K)`, inertia degree `f = f(L/K)`, different exponent `d = d(L/K)` and discriminant
exponent `δ = δ(L/K) = f · d`. By Dedekind's different theorem, `e - 1 ≤ d`, with equality if and
only if `L/K` is tamely ramified. Subtracting the tame baseline isolates the wild contribution:

* the **ramification height** `TauCeti.ramificationHeight K L : ℕ` is
  `δ / f + 1 - e = d + 1 - e` (often called the Swan-like wild excess `H(L/K)` or, for totally
  ramified extensions, Serre's wild exponent `c(L/K)`);
* the **ramification mean** `TauCeti.ramificationMean K L : ℚ` is
  `ramificationHeight K L / e`, the average wild slope per ramification degree.

Both invariants vanish if and only if `L/K` is tamely ramified, are preserved by `K`-algebra
equivalences, and are unchanged when passing to the top step `L/L₀` over an unramified intermediate
extension `L₀/K` — in particular over the canonical maximal unramified subextension
`unramifiedExtension K L (inertiaDegree K L)`.

## Main definitions

* `TauCeti.ramificationHeight K L`: the wild excess `δ(L/K) / f(L/K) + 1 - e(L/K)` of a separable
  local-field extension `L/K`.
* `TauCeti.ramificationMean K L`: the rational quotient `ramificationHeight K L / e(L/K)`.

## Main results

* `TauCeti.ramificationHeight_eq_differentExponent_add_one_sub_ramificationIndex` and
  `TauCeti.IsTotallyRamified.ramificationHeight_eq`: expressions in terms of `differentExponent`
  and, in the totally ramified case, `discriminantExponent` and `Module.finrank`.
* `TauCeti.differentExponent_eq_ramificationIndex_sub_one_add_ramificationHeight` and
  `TauCeti.discriminantExponent_eq_inertiaDegree_mul_add_ramificationHeight`: recovery of `d(L/K)`
  and `δ(L/K)` without truncation loss.
* `TauCeti.ramificationIndex_mul_ramificationMean`: `e(L/K) * ramificationMean K L =
  ramificationHeight K L`.
* `TauCeti.ramificationHeight_eq_zero_iff` and `TauCeti.ramificationMean_eq_zero_iff`: both
  invariants vanish if and only if `L/K` is tamely ramified.
* `TauCeti.ramificationHeight_le_natCastValuation`: when `(e(L/K) : L) ≠ 0`,
  `ramificationHeight K L ≤ v_L(e(L/K))`.
* `TauCeti.ramificationHeight_eq_of_algEquiv` and `TauCeti.ramificationMean_eq_of_algEquiv`:
  invariance under `K`-algebra equivalence.
* `TauCeti.IsUnramified.ramificationHeight_tower_eq`,
  `TauCeti.IsUnramified.ramificationMean_tower_eq`,
  `TauCeti.ramificationHeight_unramifiedExtension_inertiaDegree` and
  `TauCeti.ramificationMean_unramifiedExtension_inertiaDegree`: invariance under unramified base
  steps and under the canonical unramified–totally ramified factorization.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §§6–7.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

variable (K L : Type*)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [Algebra.IsSeparable K L]

/-- The ramification height `H(L/K) = δ(L/K) / f(L/K) + 1 - e(L/K)` of a separable extension `L/K`
of nonarchimedean local fields, measuring the excess of the different exponent over its tame value
`e(L/K) - 1`. -/
def ramificationHeight : ℕ :=
  discriminantExponent K L / inertiaDegree K L + 1 - ramificationIndex K L

/-- The ramification mean `M(L/K) = H(L/K) / e(L/K)` of a separable extension `L/K` of
nonarchimedean local fields. -/
def ramificationMean : ℚ :=
  (ramificationHeight K L : ℚ) / ramificationIndex K L

/-- Defining formula for `ramificationHeight`. -/
theorem ramificationHeight_def :
    ramificationHeight K L =
      discriminantExponent K L / inertiaDegree K L + 1 - ramificationIndex K L := by
  rw [ramificationHeight]

/-- Defining formula for `ramificationMean`. -/
theorem ramificationMean_def :
    ramificationMean K L = (ramificationHeight K L : ℚ) / ramificationIndex K L := by
  rw [ramificationMean]

/-- `ramificationHeight K L` equals `differentExponent K L + 1 - ramificationIndex K L`. -/
theorem ramificationHeight_eq_differentExponent_add_one_sub_ramificationIndex :
    ramificationHeight K L = differentExponent K L + 1 - ramificationIndex K L := by
  rw [ramificationHeight_def, discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    Nat.mul_div_right _ (inertiaDegree_pos (K := K) (L := L))]

variable {K L} in
/-- For a totally ramified extension, `ramificationHeight K L` is
`discriminantExponent K L + 1 - [L : K]`. -/
theorem IsTotallyRamified.ramificationHeight_eq (h : IsTotallyRamified K L) :
    ramificationHeight K L = discriminantExponent K L + 1 - Module.finrank K L := by
  rw [ramificationHeight_def, h.inertiaDegree_eq_one, Nat.div_one,
    (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).mp h]

/-- Faithfulness of the truncated subtraction in `ramificationHeight`:
`d(L/K) = e(L/K) - 1 + H(L/K)`. -/
theorem differentExponent_eq_ramificationIndex_sub_one_add_ramificationHeight :
    differentExponent K L = ramificationIndex K L - 1 + ramificationHeight K L := by
  have hle := ramificationIndex_sub_one_le_differentExponent K L
  have he := ramificationIndex_pos (K := K) (L := L)
  rw [ramificationHeight_eq_differentExponent_add_one_sub_ramificationIndex]
  omega

/-- Faithfulness of `ramificationHeight` for the discriminant exponent:
`δ(L/K) = f(L/K) * (e(L/K) - 1 + H(L/K))`. -/
theorem discriminantExponent_eq_inertiaDegree_mul_add_ramificationHeight :
    discriminantExponent K L =
      inertiaDegree K L * (ramificationIndex K L - 1 + ramificationHeight K L) := by
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    differentExponent_eq_ramificationIndex_sub_one_add_ramificationHeight]

/-- Clearing the denominator of `ramificationMean`:
`e(L/K) * M(L/K) = H(L/K)`. -/
theorem ramificationIndex_mul_ramificationMean :
    (ramificationIndex K L : ℚ) * ramificationMean K L = ramificationHeight K L :=
  mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (ramificationIndex_pos (K := K) (L := L)).ne')

/-- The ramification height vanishes if and only if the extension is tamely ramified. -/
@[simp]
theorem ramificationHeight_eq_zero_iff :
    ramificationHeight K L = 0 ↔ IsTamelyRamified K L := by
  rw [← differentExponent_eq_ramificationIndex_sub_one_iff (K := K) (L := L)]
  have hle := ramificationIndex_sub_one_le_differentExponent K L
  have he := ramificationIndex_pos (K := K) (L := L)
  rw [ramificationHeight_eq_differentExponent_add_one_sub_ramificationIndex]
  omega

/-- The ramification height is positive if and only if the extension is wildly ramified. -/
@[simp]
theorem ramificationHeight_pos_iff :
    0 < ramificationHeight K L ↔ IsWildlyRamified K L := by
  rw [Nat.pos_iff_ne_zero, ne_eq, ramificationHeight_eq_zero_iff, not_isTamelyRamified_iff]

/-- The ramification mean is nonnegative. -/
theorem ramificationMean_nonneg : 0 ≤ ramificationMean K L := by
  rw [ramificationMean_def]
  positivity

/-- The ramification mean vanishes if and only if the extension is tamely ramified. -/
@[simp]
theorem ramificationMean_eq_zero_iff :
    ramificationMean K L = 0 ↔ IsTamelyRamified K L := by
  rw [ramificationMean_def, div_eq_zero_iff,
    or_iff_left (Nat.cast_ne_zero.mpr (ramificationIndex_pos (K := K) (L := L)).ne'),
    Nat.cast_eq_zero, ramificationHeight_eq_zero_iff]

/-- The ramification mean is positive if and only if the extension is wildly ramified. -/
@[simp]
theorem ramificationMean_pos_iff :
    0 < ramificationMean K L ↔ IsWildlyRamified K L := by
  rw [lt_iff_le_and_ne, and_iff_right (ramificationMean_nonneg K L), ne_comm,
    ne_eq, ramificationMean_eq_zero_iff, not_isTamelyRamified_iff]

variable {K L} in
/-- **Upper bound on the ramification height.** When `(e(L/K) : L) ≠ 0` (in particular throughout
mixed characteristic), `H(L/K) ≤ v_L(e(L/K))`. -/
theorem ramificationHeight_le_natCastValuation (he : (ramificationIndex K L : L) ≠ 0) :
    ramificationHeight K L ≤ natCastValuation L (ramificationIndex K L) he := by
  have hd := differentExponent_le_ramificationIndex_sub_one_add_natCastValuation (K := K) he
  have hpos := ramificationIndex_pos (K := K) (L := L)
  rw [differentExponent_eq_ramificationIndex_sub_one_add_ramificationHeight K L] at hd
  omega

section AlgEquiv

variable (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M]

/-- `ramificationHeight` is preserved by `K`-algebra equivalences. -/
theorem ramificationHeight_eq_of_algEquiv (e : L ≃ₐ[K] M) :
    ramificationHeight K L =
      (let _ : Algebra.IsSeparable K M := AlgEquiv.Algebra.isSeparable e
       ramificationHeight K M) := by
  have : Algebra.IsSeparable K M := AlgEquiv.Algebra.isSeparable e
  have : Module.Finite K L := finite_of_valuativeExtension K L
  rw [ramificationHeight_def, ramificationHeight_def, discriminantExponent_eq_of_algEquiv K L M e,
    inertiaDegree_eq_of_algEquiv K L M e, ramificationIndex_eq_of_algEquiv K L M e]

/-- `ramificationMean` is preserved by `K`-algebra equivalences. -/
theorem ramificationMean_eq_of_algEquiv (e : L ≃ₐ[K] M) :
    ramificationMean K L =
      (let _ : Algebra.IsSeparable K M := AlgEquiv.Algebra.isSeparable e
       ramificationMean K M) := by
  have : Algebra.IsSeparable K M := AlgEquiv.Algebra.isSeparable e
  rw [ramificationMean_def, ramificationMean_def, ramificationHeight_eq_of_algEquiv K L M e,
    ramificationIndex_eq_of_algEquiv K L M e]

end AlgEquiv

section UnramifiedTower

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra K E] [Algebra E L] [IsScalarTower K E L]
  [ValuativeExtension K E] [ValuativeExtension E L] [IsUnramified K E]

/-- In a tower `K → E → L` with `E/K` unramified, the top step `L/E` has the same ramification
height as `L/K`. -/
theorem IsUnramified.ramificationHeight_tower_eq :
    letI : Algebra.IsSeparable E L := Algebra.isSeparable_tower_top_of_isSeparable K E L
    ramificationHeight E L = ramificationHeight K L := by
  let _ : Algebra.IsSeparable E L := Algebra.isSeparable_tower_top_of_isSeparable K E L
  rw [ramificationHeight_eq_differentExponent_add_one_sub_ramificationIndex,
    ramificationHeight_eq_differentExponent_add_one_sub_ramificationIndex,
    IsUnramified.differentExponent_tower_eq K E L,
    IsUnramified.ramificationIndex_tower_eq K E L]

/-- In a tower `K → E → L` with `E/K` unramified, the top step `L/E` has the same ramification
mean as `L/K`. -/
theorem IsUnramified.ramificationMean_tower_eq :
    letI : Algebra.IsSeparable E L := Algebra.isSeparable_tower_top_of_isSeparable K E L
    ramificationMean E L = ramificationMean K L := by
  let _ : Algebra.IsSeparable E L := Algebra.isSeparable_tower_top_of_isSeparable K E L
  rw [ramificationMean_def, ramificationMean_def,
    IsUnramified.ramificationHeight_tower_eq K L E,
    IsUnramified.ramificationIndex_tower_eq K E L]

end UnramifiedTower

section Factorization

variable [ValuativeRel (unramifiedExtension K L (inertiaDegree K L))]
  [TopologicalSpace (unramifiedExtension K L (inertiaDegree K L))]
  [IsNonarchimedeanLocalField (unramifiedExtension K L (inertiaDegree K L))]
  [ValuativeExtension K (unramifiedExtension K L (inertiaDegree K L))]

/-- The top step of the canonical unramified–totally ramified factorization of `L/K` has the same
ramification height as `L/K`. -/
@[simp]
theorem ramificationHeight_unramifiedExtension_inertiaDegree :
    letI : Algebra.IsSeparable (unramifiedExtension K L (inertiaDegree K L)) L :=
      Algebra.isSeparable_tower_top_of_isSeparable K _ L
    ramificationHeight (unramifiedExtension K L (inertiaDegree K L)) L =
      ramificationHeight K L := by
  have := isUnramified_unramifiedExtension_inertiaDegree K L
  exact IsUnramified.ramificationHeight_tower_eq K L _

/-- The top step of the canonical unramified–totally ramified factorization of `L/K` has the same
ramification mean as `L/K`. -/
@[simp]
theorem ramificationMean_unramifiedExtension_inertiaDegree :
    letI : Algebra.IsSeparable (unramifiedExtension K L (inertiaDegree K L)) L :=
      Algebra.isSeparable_tower_top_of_isSeparable K _ L
    ramificationMean (unramifiedExtension K L (inertiaDegree K L)) L =
      ramificationMean K L := by
  have := isUnramified_unramifiedExtension_inertiaDegree K L
  exact IsUnramified.ramificationMean_tower_eq K L _

end Factorization

end TauCeti

end
