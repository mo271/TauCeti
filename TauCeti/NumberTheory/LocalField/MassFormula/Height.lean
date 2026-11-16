/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Discriminant.Height
public import TauCeti.NumberTheory.LocalField.MassFormula.Basic

/-!
# Agreement of `IntermediateField.wildExponent` with `ramificationHeight`

On totally ramified subextensions `L` of `SeparableClosure K`, `L.wildExponent` (defined in
`TauCeti.NumberTheory.LocalField.MassFormula.Basic` without fixing local-field instances in the
type) agrees with `TauCeti.ramificationHeight K L` for the canonical finite-intermediate-field
local-field structure; for `L ∈ totallyRamifiedOfDegree K n`, `(L.wildExponent : ℚ) / n` agrees
with `TauCeti.ramificationMean K L`.

## Main results

* `IntermediateField.IsTotallyRamified.wildExponent_eq_ramificationHeight`: for a totally ramified
  subextension `L` of `SeparableClosure K`, `L.wildExponent = ramificationHeight K L`.
* `IntermediateField.wildExponent_div_eq_ramificationMean`: for `L ∈ totallyRamifiedOfDegree K n`,
  `(L.wildExponent : ℚ) / n = ramificationMean K L`.
-/

public section
noncomputable section

open ValuativeRel TauCeti

namespace IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- On a totally ramified subextension `L` of `SeparableClosure K`, Serre's wild exponent
`L.wildExponent` agrees with `TauCeti.ramificationHeight K L`. -/
theorem IsTotallyRamified.wildExponent_eq_ramificationHeight
    {L : IntermediateField K (SeparableClosure K)} (hL : L.IsTotallyRamified) :
    L.wildExponent =
      (haveI : Module.Finite K L := hL.finite
       letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
       letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
       haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
       haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
       haveI : Algebra.IsSeparable K L :=
         Algebra.isSeparable_tower_bot_of_isSeparable K L (SeparableClosure K)
       ramificationHeight K L) := by
  have : Module.Finite K L := hL.finite
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  have : Algebra.IsSeparable K L :=
    Algebra.isSeparable_tower_bot_of_isSeparable K L (SeparableClosure K)
  have htr : TauCeti.IsTotallyRamified K L := L.isTotallyRamified_iff.mp hL
  rw [L.wildExponent_def, L.discriminantExponent_eq, htr.ramificationHeight_eq]

/-- On `L ∈ totallyRamifiedOfDegree K n`, `(L.wildExponent : ℚ) / n` agrees with
`TauCeti.ramificationMean K L`. -/
theorem wildExponent_div_eq_ramificationMean {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    (L.wildExponent : ℚ) / n =
      (haveI : Module.Finite K L := (mem_totallyRamifiedOfDegree_iff.mp hL).2.finite
       letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
       letI := finiteIntermediateFieldTopology K (SeparableClosure K) L
       haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
       haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
       haveI : Algebra.IsSeparable K L :=
         Algebra.isSeparable_tower_bot_of_isSeparable K L (SeparableClosure K)
       ramificationMean K L) := by
  obtain ⟨hn, htr'⟩ := mem_totallyRamifiedOfDegree_iff.mp hL
  have : Module.Finite K L := htr'.finite
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  have : Algebra.IsSeparable K L :=
    Algebra.isSeparable_tower_bot_of_isSeparable K L (SeparableClosure K)
  have htr : TauCeti.IsTotallyRamified K L := L.isTotallyRamified_iff.mp htr'
  rw [htr'.wildExponent_eq_ramificationHeight, ramificationMean_def,
    (isTotallyRamified_iff_ramificationIndex_eq_finrank K L).mp htr]
  congr 1
  exact_mod_cast hn.symm

end IntermediateField

end
