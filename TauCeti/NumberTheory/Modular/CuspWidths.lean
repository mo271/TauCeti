/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Cusp.LocalMultiplicity
public import TauCeti.Combinatorics.PermutationTriple.CycleData
public import TauCeti.Combinatorics.PermutationTriple.Mirror
public import TauCeti.GroupTheory.DoubleCoset.RightCosets
public import TauCeti.NumberTheory.Modular.CosetTriple
public import TauCeti.NumberTheory.ModularForms.Cusps.IntegralWidth
public import TauCeti.NumberTheory.ModularForms.Norm.Cusps
import TauCeti.Analysis.Complex.Fuchsian.Cusp.ChangeScaling
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Cusp
import TauCeti.NumberTheory.Modular.ConjugateTranslation

/-!
# Cusp widths and the number of cusps of modular coset triples

For a subgroup `Γ' ≤ PSL(2, ℤ)` equipped with a coset numbering `e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n`, the
`∞`-component `permT Γ' e = (modularTriple Γ' e).σinf` is the permutation induced by left
multiplication by `T = [1, 1; 0, 1]`. Its full cycle partition and orbit count encode the cusp
geometry of `Γ'` and of its preimage `Γ'.liftSL ≤ SL(2, ℤ)`:

* **Definitions and invariance (`TauCeti.ModularGroup.cuspWidths`,
  `TauCeti.ModularGroup.cuspCount`).** `cuspWidths Γ' e := (permT Γ' e).fullCycleType` (including
  fixed points as cusps of width `1`) and `cuspCount Γ' e := orbitCount (permT Γ' e)` sum to `n`,
  have cardinality `cuspCount Γ' e`, and have least common multiple `orderOf (permT Γ' e)`. Both
  depend only on the isomorphism class of `modularTriple Γ' e`, hence are independent of `e` and
  invariant under conjugation in `PSL(2, ℤ)`, under the mirror involution `conjJAut`, and under
  passing to the LMFDB right-coset permutation `r.permCongr (Γ'.rightCosetPerm T)`.
* **Width at `∞` and at an arbitrary cusp (`TauCeti.ModularGroup.period_permT_one`,
  `TauCeti.ModularGroup.period_permT_coset`, `TauCeti.ModularGroup.cuspDatumPSL`).** For
  `σ : SL(2, ℤ)`, the cycle length of `permT Γ' e` through `e ⟦σ⁻¹⟧` equals the least `m > 0` with
  `σ T ^ m σ⁻¹ ∈ Γ'.liftSL`, agrees with `integerCuspWidth` of `(σ⁻¹ Γ'.liftSL σ : Subgroup GL₂(ℝ))`
  (and at `σ = 1` with `strictWidthInfty` and `widthInfty`), and equals `(cuspDatumPSL Γ' σ).width`
  for the normalized Fuchsian cusp datum at `σ • ∞` with integral scaling `(sl2zToPSL2R σ)⁻¹`.
* **Double cosets and cusp orbits (`TauCeti.ModularGroup.permTCycleEquivDoubleCoset`,
  `TauCeti.ModularGroup.permTCycleEquivCuspOrbit`, `TauCeti.ModularGroup.permTCycleEquivCuspOrbits`,
  `TauCeti.ModularGroup.cuspCount_eq_card_cuspOrbits`).** Cycles of `permT Γ' e` correspond
  bijectively to double cosets `Γ' \ PSL(2, ℤ) / ⟨T⟩` (carrying cycle lengths to right-coset fiber
  sizes), to Fuchsian `(Γ'.map psl2zToPSL2R).CuspOrbit`, and to Mathlib's
  `CuspOrbits (Γ'.liftSL.map (mapGL ℝ))` via `cosetToCuspOrbit`.
* **Width ratios and tower sum (`TauCeti.ModularGroup.period_permT_coset_eq_widthIndex_mul`,
  `TauCeti.ModularGroup.period_permT_coset_eq_localMultiplicity_mul`,
  `TauCeti.ModularGroup.sum_cycleLength_fiber_permTCycleMapOfLE`).** For `Γ₁' ≤ Γ₂'`, the width at
  `σ • ∞` grows by the Fuchsian `widthIndex` (equal to the compactified quotient map's
  `localMultiplicity`), and the cycle lengths of `permT Γ₁' e₁` lying over a cycle of `permT Γ₂' e₂`
  are multiples of its length summing to its length times `[Γ₂' : Γ₁']`.

## References

* F. Diamond, J. Shurman, *A First Course in Modular Forms*, Springer, 2005, §3.8.
* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton University
  Press, 1971, §1.6.
-/

open Equiv Equiv.Perm Matrix Matrix.SpecialLinearGroup Matrix.ProjectiveSpecialLinearGroup
open MulAction OnePoint
open scoped MatrixGroups ModularForm Pointwise

public noncomputable section

namespace TauCeti.ModularGroup

open _root_.ModularGroup PermutationTriple

variable {n : ℕ}

/-! ### Definitions, basic properties, and invariance -/

/-- **The cusp widths of a modular coset triple**: the full cycle partition of `permT Γ' e`, with
fixed points included as cusps of width `1`. -/
def cuspWidths (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : Multiset ℕ :=
  (permT Γ' e).fullCycleType

/-- Unfolds `cuspWidths` as the full cycle type of `permT Γ' e`. -/
theorem cuspWidths_def (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspWidths Γ' e = (permT Γ' e).fullCycleType := (rfl)

/-- **The number of cusps of a modular coset triple**: the number of cycles of `permT Γ' e`,
fixed points included. -/
def cuspCount (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) : ℕ :=
  orbitCount (permT Γ' e)

/-- Unfolds `cuspCount` as `orbitCount (permT Γ' e)`. -/
theorem cuspCount_def (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e = orbitCount (permT Γ' e) := (rfl)

/-- The `∞`-entry of `(modularTriple Γ' e).cycleData` is `cuspWidths Γ' e`. -/
theorem cycleData_σinf_modularTriple (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).cycleData.2.2 = cuspWidths Γ' e := by
  rw [cycleData_σinf, cuspWidths, permT, fullCycleType_def]

/-- The `∞`-entry of `(modularTriple Γ' e).cycleCounts` is `cuspCount Γ' e`. -/
theorem cycleCounts_σinf_modularTriple (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (modularTriple Γ' e).cycleCounts.2.2 = cuspCount Γ' e := by
  rw [cycleCounts_σinf, cuspCount, permT]

/-- The number of parts of `cuspWidths Γ' e` (counted with multiplicity) is `cuspCount Γ' e`. -/
@[simp]
theorem card_cuspWidths (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (cuspWidths Γ' e).card = cuspCount Γ' e := by
  rw [cuspWidths, fullCycleType_def, cuspCount, orbitCount_eq_card_parts_partition]

/-- The cusp widths of an index-`n` modular subgroup sum to `n`. -/
@[simp]
theorem sum_cuspWidths (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (cuspWidths Γ' e).sum = n := by
  rw [cuspWidths, sum_fullCycleType, Fintype.card_fin]

/-- The least common multiple of the cusp widths equals `orderOf (permT Γ' e)`. -/
@[simp]
theorem lcm_cuspWidths (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (cuspWidths Γ' e).lcm = orderOf (permT Γ' e) := by
  rw [cuspWidths, fullCycleType_def, lcm_parts_partition]

/-- Every cusp width is positive. -/
theorem pos_of_mem_cuspWidths {Γ' : Subgroup PSL(2, ℤ)} {e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n} {w : ℕ}
    (hw : w ∈ cuspWidths Γ' e) : 0 < w :=
  pos_of_mem_fullCycleType hw

/-- Every cusp width is at most the index `n`. -/
theorem le_of_mem_cuspWidths {Γ' : Subgroup PSL(2, ℤ)} {e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n} {w : ℕ}
    (hw : w ∈ cuspWidths Γ' e) : w ≤ n := by
  rw [← sum_cuspWidths Γ' e]
  exact Multiset.le_sum_of_mem hw

/-- Every cusp width divides `orderOf (permT Γ' e)`. -/
theorem dvd_orderOf_permT_of_mem_cuspWidths {Γ' : Subgroup PSL(2, ℤ)} {e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n}
    {w : ℕ} (hw : w ∈ cuspWidths Γ' e) : w ∣ orderOf (permT Γ' e) := by
  rw [← lcm_cuspWidths Γ' e]
  exact Multiset.dvd_lcm hw

/-- Every finite-index subgroup of `PSL(2, ℤ)` has at least one cusp. -/
theorem cuspCount_pos (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    0 < cuspCount Γ' e := by
  obtain ⟨i⟩ : Nonempty (Fin n) :=
    Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (Γ'.ne_zero_of_equiv e))
  have : Nonempty (Quotient (SameCycle.setoid (permT Γ' e))) := ⟨Quotient.mk _ i⟩
  rw [cuspCount, orbitCount_def]
  exact Nat.card_pos

/-- The number of cusps is at most the index `n`. -/
theorem cuspCount_le (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e ≤ n :=
  calc
    cuspCount Γ' e = (cuspWidths Γ' e).card := (card_cuspWidths Γ' e).symm
    _ ≤ (cuspWidths Γ' e).sum := by
      simpa using Multiset.card_nsmul_le_sum fun w hw ↦ pos_of_mem_cuspWidths hw
    _ = n := sum_cuspWidths Γ' e

/-- Isomorphic modular coset triples have the same multiset of cusp widths. -/
theorem cuspWidths_eq_of_equivalent {Γ₁' Γ₂' : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁' ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂' ≃ Fin n}
    (h : (modularTriple Γ₁' e₁).Equivalent (modularTriple Γ₂' e₂)) :
    cuspWidths Γ₁' e₁ = cuspWidths Γ₂' e₂ := by
  rw [← cycleData_σinf_modularTriple, ← cycleData_σinf_modularTriple, cycleData_eq_of_equivalent h]

/-- Isomorphic modular coset triples have the same cusp count. -/
theorem cuspCount_eq_of_equivalent {Γ₁' Γ₂' : Subgroup PSL(2, ℤ)}
    {e₁ : PSL(2, ℤ) ⧸ Γ₁' ≃ Fin n} {e₂ : PSL(2, ℤ) ⧸ Γ₂' ≃ Fin n}
    (h : (modularTriple Γ₁' e₁).Equivalent (modularTriple Γ₂' e₂)) :
    cuspCount Γ₁' e₁ = cuspCount Γ₂' e₂ := by
  rw [← card_cuspWidths, ← card_cuspWidths, cuspWidths_eq_of_equivalent h]

/-- `cuspWidths Γ' e` is independent of the coset numbering `e`. -/
theorem cuspWidths_eq (Γ' : Subgroup PSL(2, ℤ)) (e₁ e₂ : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspWidths Γ' e₁ = cuspWidths Γ' e₂ :=
  cuspWidths_eq_of_equivalent (equivalent_modularTriple Γ' e₁ e₂)

/-- `cuspCount Γ' e` is independent of the coset numbering `e`. -/
theorem cuspCount_eq (Γ' : Subgroup PSL(2, ℤ)) (e₁ e₂ : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e₁ = cuspCount Γ' e₂ :=
  cuspCount_eq_of_equivalent (equivalent_modularTriple Γ' e₁ e₂)

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same multiset of cusp widths. -/
theorem cuspWidths_conjAct_smul (g : ConjAct PSL(2, ℤ)) (Γ' : Subgroup PSL(2, ℤ))
    (e₁ : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (e₂ : PSL(2, ℤ) ⧸ (g • Γ') ≃ Fin n) :
    cuspWidths (g • Γ') e₂ = cuspWidths Γ' e₁ :=
  (cuspWidths_eq_of_equivalent ((millington e₁ e₂).mpr ⟨g, rfl⟩)).symm

/-- Conjugate subgroups of `PSL(2, ℤ)` have the same cusp count. -/
theorem cuspCount_conjAct_smul (g : ConjAct PSL(2, ℤ)) (Γ' : Subgroup PSL(2, ℤ))
    (e₁ : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (e₂ : PSL(2, ℤ) ⧸ (g • Γ') ≃ Fin n) :
    cuspCount (g • Γ') e₂ = cuspCount Γ' e₁ :=
  (cuspCount_eq_of_equivalent ((millington e₁ e₂).mpr ⟨g, rfl⟩)).symm

/-- Passing to the mirror subgroup `Γ'.map conjJAut` preserves `cuspWidths`. -/
theorem cuspWidths_map_conjJAut (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    cuspWidths (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = cuspWidths Γ' e := by
  rw [← cycleData_σinf_modularTriple, ← cycleData_σinf_modularTriple,
    cycleData_eq_of_equivalent (equivalent_mirror_modularTriple Γ' e e'), cycleData_mirror]

/-- Passing to the mirror subgroup `Γ'.map conjJAut` preserves `cuspCount`. -/
theorem cuspCount_map_conjJAut (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (e' : PSL(2, ℤ) ⧸ Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ)) ≃ Fin n) :
    cuspCount (Γ'.map (conjJAut : PSL(2, ℤ) →* PSL(2, ℤ))) e' = cuspCount Γ' e := by
  rw [← card_cuspWidths, ← card_cuspWidths, cuspWidths_map_conjJAut Γ' e e']

/-- In the LMFDB right-coset convention, `r.permCongr (Γ'.rightCosetPerm T)` has full cycle type
`cuspWidths Γ' e`. -/
theorem fullCycleType_rightCosetPerm_T (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ)))).fullCycleType = cuspWidths Γ' e := by
  let e₀ := (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ').symm.trans r
  have hT : permT Γ' e₀ = (r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ))))⁻¹ :=
    (modularTriple_quotientRightRel Γ' r).2.2.2.1
  rw [← cuspWidths_eq Γ' e₀ e, cuspWidths, hT, fullCycleType_inv]

/-- In the LMFDB right-coset convention, `r.permCongr (Γ'.rightCosetPerm T)` has `cuspCount Γ' e`
orbits. -/
theorem orbitCount_rightCosetPerm_T (Γ' : Subgroup PSL(2, ℤ))
    (r : Quotient (QuotientGroup.rightRel Γ') ≃ Fin n) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    orbitCount (r.permCongr (Γ'.rightCosetPerm (T : PSL(2, ℤ)))) = cuspCount Γ' e := by
  rw [orbitCount_eq_card_parts_partition, ← fullCycleType_def,
    fullCycleType_rightCosetPerm_T Γ' r e, card_cuspWidths]

/-! ### Width at `∞`, width at a cusp `σ ∞`, and normalized Fuchsian cusp data -/

/-- The cycle length of `permT Γ' e` through `e ⟦σ⁻¹⟧` divides `m` if and only if
`σ * T ^ m * σ⁻¹ ∈ Γ'.liftSL`. -/
theorem period_permT_coset_dvd_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (σ : SL(2, ℤ)) (m : ℕ) :
    MulAction.period (permT Γ' e) (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) ∣ m ↔
      σ * T ^ m * σ⁻¹ ∈ Γ'.liftSL := by
  rw [permT, modularTriple_σinf, e.period_permutationRepresentation, Γ'.period_mk_dvd_iff]
  simp [← QuotientGroup.mk_pow, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]

/-- **Width at a cusp `σ ∞`.** The cycle of `permT Γ' e` through `e ⟦σ⁻¹⟧` has length equal to the
least `m > 0` with `σ * T ^ m * σ⁻¹ ∈ Γ'.liftSL`. -/
theorem period_permT_coset (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (σ : SL(2, ℤ)) :
    MulAction.period (permT Γ' e) (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      sInf {m : ℕ | 0 < m ∧ σ * T ^ m * σ⁻¹ ∈ Γ'.liftSL} := by
  rw [MulAction.period_eq_sInf]
  congr 1
  ext m
  exact and_congr_right'
    (MulAction.pow_smul_eq_iff_period_dvd.trans (period_permT_coset_dvd_iff Γ' e σ m))

/-- The cycle length of `permT Γ' e` through `e ⟦σ⁻¹⟧` equals the integer cusp width at `∞` of the
conjugate subgroup `(σ⁻¹ • Γ'.liftSL : Subgroup (GL (Fin 2) ℝ))`. -/
theorem period_permT_coset_eq_integerCuspWidth (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ)) :
    MulAction.period (permT Γ' e) (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      TauCeti.Subgroup.integerCuspWidth
        (((ConjAct.toConjAct σ⁻¹ • Γ'.liftSL : Subgroup SL(2, ℤ)) :
          Subgroup (GL (Fin 2) ℝ))) := by
  refine Nat.dvd_right_iff_eq.mp fun m ↦ ?_
  rw [period_permT_coset_dvd_iff, ← Subgroup.T_pow_mem_iff_integerCuspWidth_dvd,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul]

/-- At the base coset `e 1`, the cycle length of `permT Γ' e` divides `m` iff `T ^ m ∈ Γ'.liftSL`.
-/
theorem period_permT_one_dvd_iff (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (m : ℕ) :
    MulAction.period (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) ∣ m ↔
      T ^ m ∈ Γ'.liftSL := by
  simpa only [inv_one, QuotientGroup.mk_one, one_mul, mul_one] using
    period_permT_coset_dvd_iff Γ' e 1 m

/-- **Width at `∞`.** The cycle of `permT Γ' e` through the base coset `e 1` has length equal to
the least `m > 0` with `T ^ m ∈ Γ'.liftSL`. -/
theorem period_permT_one (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    MulAction.period (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      sInf {m : ℕ | 0 < m ∧ T ^ m ∈ Γ'.liftSL} := by
  simpa using period_permT_coset Γ' e 1

/-- The cycle length of `permT Γ' e` through `e 1` equals
`TauCeti.Subgroup.integerCuspWidth (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ))`. -/
theorem period_permT_one_eq_integerCuspWidth (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    MulAction.period (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      TauCeti.Subgroup.integerCuspWidth (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) := by
  simpa using period_permT_coset_eq_integerCuspWidth Γ' e 1

/-- Cast to `ℝ`, the cycle length of `permT Γ' e` through `e 1` equals the analytic strict width
`(Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty`. -/
theorem cast_period_permT_one_eq_strictWidthInfty (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (MulAction.period (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) : ℝ) =
      (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty := by
  rw [period_permT_one_eq_integerCuspWidth, Subgroup.strictWidthInfty_coe_SL2Z]

/-- Cast to `ℝ`, the cycle length of `permT Γ' e` through `e 1` equals the projective width
`(Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)).widthInfty` (since `-1 ∈ Γ'.liftSL`). -/
theorem cast_period_permT_one_eq_widthInfty (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    (MulAction.period (permT Γ' e) (e ((1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) : ℝ) =
      (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)).widthInfty := by
  rw [period_permT_one_eq_integerCuspWidth,
    Subgroup.widthInfty_coe_eq_integerCuspWidth_of_neg_one_mem Γ'.neg_one_mem_liftSL]

/-- Compatibility with `TauCeti.ModularForm.cuspTranslationOrbitWidth` on `(Γ'.liftSL : _)`. -/
theorem period_permT_coset_eq_cuspTranslationOrbitWidth (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ)) :
    MulAction.period (permT Γ' e) (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      TauCeti.ModularForm.cuspTranslationOrbitWidth
        (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict σ⁻¹) :
          𝒮ℒ ⧸ (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
            TauCeti.ModularForm.CuspTranslationOrbit (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ))) :=
  Nat.dvd_right_iff_eq.mp fun m ↦ by
    rw [period_permT_coset_dvd_iff, TauCeti.ModularForm.cuspTranslationOrbitWidth_mk_dvd_iff,
      inv_inv]

/-- **Normalized Fuchsian cusp datum of `Γ'.map psl2zToPSL2R` at `σ • ∞`** with integral scaling
`(sl2zToPSL2R σ)⁻¹`. -/
def cuspDatumPSL (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] (σ : SL(2, ℤ)) :
    (Γ'.map psl2zToPSL2R).CuspDatum :=
  (Γ'.liftSL.cuspDatumOfSL2Z σ).conj
    (by rw [map_one, one_smul]; exact Γ'.map_sl2zToPSL2R_liftSL)

@[simp]
theorem cuspDatumPSL_cusp (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] (σ : SL(2, ℤ)) :
    (cuspDatumPSL Γ' σ).cusp = sl2zToPSL2R σ • (∞ : OnePoint ℝ) := by
  rw [cuspDatumPSL, Subgroup.CuspDatum.conj_cusp, one_smul, Subgroup.cuspDatumOfSL2Z_cusp]

@[simp]
theorem cuspDatumPSL_scaling (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] (σ : SL(2, ℤ)) :
    (cuspDatumPSL Γ' σ).scaling = (sl2zToPSL2R σ)⁻¹ := by
  rw [cuspDatumPSL, Subgroup.CuspDatum.conj_scaling, inv_one, mul_one,
    Subgroup.cuspDatumOfSL2Z_scaling]

/-- The width of `cuspDatumPSL Γ' σ` equals the cycle length of `permT Γ' e` through `e ⟦σ⁻¹⟧`. -/
theorem cuspDatumPSL_width_eq_period_permT (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (σ : SL(2, ℤ)) :
    let : Γ'.FiniteIndex := Γ'.finiteIndex_of_equiv e
    (cuspDatumPSL Γ' σ).width =
      MulAction.period (permT Γ' e) (e (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) := by
  intro _
  rw [cuspDatumPSL, Subgroup.CuspDatum.conj_width, Subgroup.cuspDatumOfSL2Z_width,
    Subgroup.withCenter_eq_self_iff.mpr Γ'.center_le_liftSL,
    period_permT_coset_eq_integerCuspWidth Γ' e σ]

/-! ### Double cosets and cusp-orbit bijections -/

/-- Equivalence between the cycle quotient of `permT Γ' e` and the `⟨T⟩`-orbit quotient on
`PSL(2, ℤ) ⧸ Γ'`. -/
def permTCycleEquivOrbitRelQuotient (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ' e)) ≃
      orbitRel.Quotient (Subgroup.zpowers (T : PSL(2, ℤ))) (PSL(2, ℤ) ⧸ Γ') :=
  (Quotient.congrRight fun i j ↦ by
    -- `Setoid.r` on `SameCycle.setoid π` is `π.SameCycle`.
    change (permT Γ' e).SameCycle i j ↔
      (e.permutationRepresentation (T : PSL(2, ℤ))).SameCycle i j
    rw [permT, modularTriple_σinf]).trans
    (e.sameCycleQuotientPermutationRepresentationEquiv (T : PSL(2, ℤ)))

@[simp]
theorem permTCycleEquivOrbitRelQuotient_mk (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (i : Fin n) :
    permTCycleEquivOrbitRelQuotient Γ' e (Quotient.mk (SameCycle.setoid (permT Γ' e)) i) =
      Quotient.mk'' (e.symm i) :=
  e.sameCycleQuotientPermutationRepresentationEquiv_mk (T : PSL(2, ℤ)) i

@[simp]
theorem permTCycleEquivOrbitRelQuotient_symm_mk (Γ' : Subgroup PSL(2, ℤ))
    (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (q : PSL(2, ℤ) ⧸ Γ') :
    (permTCycleEquivOrbitRelQuotient Γ' e).symm (Quotient.mk'' q) =
      Quotient.mk (SameCycle.setoid (permT Γ' e)) (e q) := by
  apply (permTCycleEquivOrbitRelQuotient Γ' e).injective
  rw [apply_symm_apply, permTCycleEquivOrbitRelQuotient_mk, symm_apply_apply]

/-- **Cycles of `permT Γ' e` are double cosets `Γ' \ PSL(2, ℤ) / ⟨T⟩`**, sending the cycle of
`e (g Γ')` to `Γ' g⁻¹ ⟨T⟩`. -/
def permTCycleEquivDoubleCoset (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ' e)) ≃
      DoubleCoset.Quotient (Γ' : Set PSL(2, ℤ)) (Subgroup.zpowers (T : PSL(2, ℤ))) :=
  (permTCycleEquivOrbitRelQuotient Γ' e).trans
    (TauCeti.orbitRelQuotientQuotientEquivDoubleCoset Γ' (Subgroup.zpowers (T : PSL(2, ℤ))))

/-- `permTCycleEquivDoubleCoset` sends the cycle of `e (g Γ')` to `Γ' g⁻¹ ⟨T⟩`. -/
@[simp]
theorem permTCycleEquivDoubleCoset_mk (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) :
    permTCycleEquivDoubleCoset Γ' e
        (Quotient.mk (SameCycle.setoid (permT Γ' e)) (e (g : PSL(2, ℤ) ⧸ Γ'))) =
      DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g⁻¹ := by
  simp [permTCycleEquivDoubleCoset]

/-- The number of right cosets of `Γ'` inside `Γ' g ⟨T⟩` equals the cycle length of `permT Γ' e`
through `e (g⁻¹ Γ')`. -/
theorem natCard_rightCosetFiber_permTCycle (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n)
    (g : PSL(2, ℤ)) :
    Nat.card {r : Quotient (QuotientGroup.rightRel Γ') //
        DoubleCoset.rightCosetToDoubleCoset Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) r =
          DoubleCoset.mk Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) g} =
      MulAction.period (permT Γ' e) (e ((g⁻¹ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) := by
  rw [TauCeti.natCard_rightCosetFiber_zpowers_mk, permT, modularTriple_σinf,
    e.period_permutationRepresentation]

open scoped Classical in
/-- `cuspWidths Γ' e` is the multiset of right-coset fiber sizes over `Γ' \ PSL(2, ℤ) / ⟨T⟩`. -/
theorem cuspWidths_eq_map_doubleCoset (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    let : Fintype (DoubleCoset.Quotient (Γ' : Set PSL(2, ℤ)) (Subgroup.zpowers (T : PSL(2, ℤ)))) :=
      have : Γ'.FiniteIndex := Γ'.finiteIndex_of_equiv e
      Fintype.ofFinite _
    cuspWidths Γ' e =
      (Finset.univ :
          Finset (DoubleCoset.Quotient (Γ' : Set PSL(2, ℤ))
            (Subgroup.zpowers (T : PSL(2, ℤ))))).val.map
        fun d ↦ Nat.card {r : Quotient (QuotientGroup.rightRel Γ') //
          DoubleCoset.rightCosetToDoubleCoset Γ' (Subgroup.zpowers (T : PSL(2, ℤ))) r = d} := by
  intro _
  rw [cuspWidths, permT, modularTriple_σinf]
  exact TauCeti.fullCycleType_permutationRepresentation_eq_map_doubleCoset e (T : PSL(2, ℤ))

/-- The number of cusps equals the number of double cosets `Γ' \ PSL(2, ℤ) / ⟨T⟩`. -/
theorem cuspCount_eq_card_doubleCoset (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e =
      Nat.card (DoubleCoset.Quotient (Γ' : Set PSL(2, ℤ)) (Subgroup.zpowers (T : PSL(2, ℤ)))) := by
  rw [cuspCount, orbitCount_def]
  exact Nat.card_congr (permTCycleEquivDoubleCoset Γ' e)

/-- Two matrices `g₁, g₂ : SL(2, ℤ)` satisfy `(g₁ * h * g₂⁻¹) 1 0 = 0` for some `h ∈ Γ'.liftSL` if
and only if their left cosets in `PSL(2, ℤ) ⧸ Γ'` lie in the same `⟨T⟩`-orbit. -/
theorem exists_mem_liftSL_c_eq_zero_iff (Γ' : Subgroup PSL(2, ℤ)) (g₁ g₂ : SL(2, ℤ)) :
    (∃ h ∈ Γ'.liftSL, (g₁ * h * g₂⁻¹) 1 0 = 0) ↔
      orbitRel (Subgroup.zpowers (T : PSL(2, ℤ))) (PSL(2, ℤ) ⧸ Γ')
        ((g₁ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') ((g₂ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') := by
  rw [orbitRel_apply, mem_orbit_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨h, hh, hc⟩
    have key {u : SL(2, ℤ)} (hu : u ∈ Γ'.liftSL) {k : ℤ} (huk : g₁ * u * g₂⁻¹ = T ^ k) :
        ∃ x : Subgroup.zpowers (T : PSL(2, ℤ)),
          x • ((g₂ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') = ((g₁ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') := by
      refine ⟨⟨(T : PSL(2, ℤ)) ^ k, Subgroup.zpow_mem_zpowers _ k⟩, ?_⟩
      rw [Subgroup.smul_def, Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      dsimp only
      rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul, ← Subgroup.mem_liftSL]
      have hid : (T ^ k * g₂)⁻¹ * g₁ = g₂⁻¹ * (g₁ * u * g₂⁻¹)⁻¹ * g₁ := by rw [huk]; group
      have hid2 : g₂⁻¹ * (g₁ * u * g₂⁻¹)⁻¹ * g₁ = u⁻¹ := by group
      rw [hid, hid2]
      exact Γ'.liftSL.inv_mem hu
    rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hk | hk
    · exact key hh hk
    · have hneg : -h ∈ Γ'.liftSL := by
        simpa using Γ'.liftSL.mul_mem Γ'.neg_one_mem_liftSL hh
      exact key hneg (by rw [mul_neg, neg_mul, hk, neg_neg])
  · rintro ⟨x, hx⟩
    obtain ⟨k, hxk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    rw [Subgroup.smul_def, ← hxk, Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
      ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← Subgroup.mem_liftSL] at hx
    refine ⟨((T ^ k * g₂)⁻¹ * g₁)⁻¹, Γ'.liftSL.inv_mem hx, ?_⟩
    have hid : g₁ * ((T ^ k * g₂)⁻¹ * g₁)⁻¹ * g₂⁻¹ = T ^ k := by group
    rw [hid]
    simp [coe_T_zpow]

/-- Descends a surjective map `f : SL(2, ℤ) → β` whose fibers are the `⟨T⟩`-orbit equivalence
classes on `PSL(2, ℤ) ⧸ Γ'` to an equivalence
`orbitRel.Quotient (Subgroup.zpowers (T : PSL(2, ℤ))) (PSL(2, ℤ) ⧸ Γ') ≃ β`. -/
private def orbitRelQuotientEquivOfSL2Z (Γ' : Subgroup PSL(2, ℤ)) {β : Type*} (f : SL(2, ℤ) → β)
    (hf_iff : ∀ γ₁ γ₂ : SL(2, ℤ),
      f γ₁ = f γ₂ ↔
        orbitRel (Subgroup.zpowers (T : PSL(2, ℤ))) (PSL(2, ℤ) ⧸ Γ')
          ((γ₁ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') ((γ₂ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'))
    (hsurj : Function.Surjective f) :
    orbitRel.Quotient (Subgroup.zpowers (T : PSL(2, ℤ))) (PSL(2, ℤ) ⧸ Γ') ≃ β := by
  let fPSL : PSL(2, ℤ) → β :=
    Quotient.lift f fun a b hab ↦ (hf_iff a b).mpr <| by
      have hab' : (a : PSL(2, ℤ)) = (b : PSL(2, ℤ)) := Quotient.sound hab
      rw [hab']
  let fQ : PSL(2, ℤ) ⧸ Γ' → β := fun q ↦
    Quotient.liftOn' q fPSL fun a b hab ↦ by
      obtain ⟨γ₁, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨γ₂, rfl⟩ := QuotientGroup.mk_surjective b
      exact (hf_iff γ₁ γ₂).mpr <| by
        rw [QuotientGroup.eq.mpr (QuotientGroup.leftRel_apply.mp hab)]
  refine Equiv.ofBijective
    (fun ω ↦ Quotient.liftOn' ω fQ fun a b ↦
      QuotientGroup.induction_on a fun g₁ ↦ QuotientGroup.induction_on b fun g₂ hab ↦ by
        obtain ⟨γ₁, rfl⟩ := QuotientGroup.mk_surjective g₁
        obtain ⟨γ₂, rfl⟩ := QuotientGroup.mk_surjective g₂
        exact (hf_iff γ₁ γ₂).mpr hab)
    ⟨?_, ?_⟩
  · intro ω₁ ω₂
    refine Quotient.inductionOn₂' ω₁ ω₂ fun q₁ q₂ ↦
      QuotientGroup.induction_on q₁ fun g₁ ↦ QuotientGroup.induction_on q₂ fun g₂ h ↦ ?_
    obtain ⟨γ₁, rfl⟩ := QuotientGroup.mk_surjective g₁
    obtain ⟨γ₂, rfl⟩ := QuotientGroup.mk_surjective g₂
    exact Quotient.sound' ((hf_iff γ₁ γ₂).mp h)
  · intro b
    obtain ⟨γ, rfl⟩ := hsurj b
    exact ⟨Quotient.mk'' ((γ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'), rfl⟩

/-- Equivalence between `⟨T⟩`-orbits on `PSL(2, ℤ) ⧸ Γ'` and Fuchsian cusp orbits of
`Γ'.map psl2zToPSL2R`, sending the orbit of `γ Γ'` to `(cuspDatumPSL Γ' γ⁻¹).cuspOrbit`. -/
def orbitRelQuotientEquivCuspOrbit (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    orbitRel.Quotient (Subgroup.zpowers (T : PSL(2, ℤ))) (PSL(2, ℤ) ⧸ Γ') ≃
      (Γ'.map psl2zToPSL2R).CuspOrbit := by
  have hmk (σ : SL(2, ℤ)) :
      (cuspDatumPSL Γ' σ).cuspOrbit =
        (Γ'.map psl2zToPSL2R).cuspOrbitMk ⟨sl2zToPSL2R σ • ∞, by
          rw [← Γ'.map_sl2zToPSL2R_liftSL]
          exact Subgroup.mem_cuspPoints.mpr
            (Γ'.liftSL.isCuspPoint_map_sl2zToPSL2R_smul_infty σ)⟩ :=
    Subtype.ext (by rw [Subgroup.CuspDatum.cuspOrbit_val, cuspDatumPSL_cusp,
      Subgroup.cuspOrbitMk_val])
  refine orbitRelQuotientEquivOfSL2Z Γ' (fun γ ↦ (cuspDatumPSL Γ' γ⁻¹).cuspOrbit)
    (fun γ₁ γ₂ ↦ ?_) fun C ↦ ?_
  · rw [← exists_mem_liftSL_c_eq_zero_iff Γ' γ₁ γ₂, hmk γ₁⁻¹, hmk γ₂⁻¹,
      Subgroup.cuspOrbitMk_eq_iff, mem_orbit_iff]
    simp only [Subtype.exists, Subgroup.mk_smul, ← Γ'.map_sl2zToPSL2R_liftSL, Subgroup.mem_map,
      exists_prop]
    have key (h : SL(2, ℤ)) :
        sl2zToPSL2R h • (sl2zToPSL2R γ₂⁻¹ • (∞ : OnePoint ℝ)) = sl2zToPSL2R γ₁⁻¹ • ∞ ↔
          (γ₁ * h * γ₂⁻¹) 1 0 = 0 := by
      rw [← inv_smul_eq_iff, ← map_inv, inv_inv, ← mul_smul, ← mul_smul, ← map_mul, ← map_mul,
        TauCeti.sl2zToPSL2R_smul_infty_eq_infty_iff]
    exact ⟨fun ⟨_, ⟨h, hh, rfl⟩, hγ⟩ ↦ ⟨h, hh, (key h).mp hγ⟩,
      fun ⟨h, hh, hγ⟩ ↦ ⟨_, ⟨h, hh, rfl⟩, (key h).mpr hγ⟩⟩
  · obtain ⟨⟨c, hc⟩, rfl⟩ := Subgroup.cuspOrbitMk_surjective C
    rw [← Γ'.map_sl2zToPSL2R_liftSL, Subgroup.mem_cuspPoints,
      Γ'.liftSL.isCuspPoint_map_sl2zToPSL2R_iff_orbit_infty] at hc
    obtain ⟨⟨_, g, rfl⟩, rfl⟩ := mem_orbit_iff.mp hc
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
    exact ⟨γ⁻¹, Subtype.ext (by simp [Subgroup.CuspDatum.cuspOrbit_val, Subgroup.cuspOrbitMk_val,
      Subgroup.smul_def])⟩

/-- `orbitRelQuotientEquivCuspOrbit` sends the `⟨T⟩`-orbit of `γ Γ'` to
`(cuspDatumPSL Γ' γ⁻¹).cuspOrbit`. -/
@[simp]
theorem orbitRelQuotientEquivCuspOrbit_mk (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex]
    (γ : SL(2, ℤ)) :
    orbitRelQuotientEquivCuspOrbit Γ'
        (Quotient.mk'' ((γ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      (cuspDatumPSL Γ' γ⁻¹).cuspOrbit := (rfl)

/-- **Cycles of `permT Γ' e` are Fuchsian cusp orbits** of `Γ'.map psl2zToPSL2R`. -/
def permTCycleEquivCuspOrbit (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ' e)) ≃ (Γ'.map psl2zToPSL2R).CuspOrbit :=
  have : Γ'.FiniteIndex := Γ'.finiteIndex_of_equiv e
  (permTCycleEquivOrbitRelQuotient Γ' e).trans (orbitRelQuotientEquivCuspOrbit Γ')

/-- The number of cusps equals `Nat.card (Γ'.map psl2zToPSL2R).CuspOrbit`. -/
theorem cuspCount_eq_card_cuspOrbit (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e = Nat.card (Γ'.map psl2zToPSL2R).CuspOrbit := by
  rw [cuspCount, orbitCount_def]
  exact Nat.card_congr (permTCycleEquivCuspOrbit Γ' e)

/-- Equivalence between `⟨T⟩`-orbits on `PSL(2, ℤ) ⧸ Γ'` and Mathlib's
`CuspOrbits (Γ'.liftSL.map (mapGL ℝ))`, compatible with `cosetToCuspOrbit`. -/
def orbitRelQuotientEquivCuspOrbits (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    orbitRel.Quotient (Subgroup.zpowers (T : PSL(2, ℤ))) (PSL(2, ℤ) ⧸ Γ') ≃
      CuspOrbits (Γ'.liftSL.map (mapGL ℝ)) := by
  let 𝒢 : Subgroup (GL (Fin 2) ℝ) := Γ'.liftSL.map (mapGL ℝ)
  have : 𝒢.IsArithmetic := inferInstanceAs (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)).IsArithmetic
  have keyM (M : SL(2, ℤ)) : mapGL ℝ M • (∞ : OnePoint ℝ) = ∞ ↔ M 1 0 = 0 := by
    simp [OnePoint.smul_infty_eq_self_iff, mapGL_coe_matrix]
  refine orbitRelQuotientEquivOfSL2Z Γ' (fun γ ↦ cosetToCuspOrbit 𝒢 ⟦γ⟧)
    (fun γ₁ γ₂ ↦ ?_) fun C ↦ ?_
  · rw [← exists_mem_liftSL_c_eq_zero_iff Γ' γ₁ γ₂, cosetToCuspOrbit_apply_mk,
      cosetToCuspOrbit_apply_mk, Quotient.eq]
    have key (h : SL(2, ℤ)) :
        mapGL ℝ h • (mapGL ℝ γ₂⁻¹ • (∞ : OnePoint ℝ)) = mapGL ℝ γ₁⁻¹ • ∞ ↔
          (γ₁ * h * γ₂⁻¹) 1 0 = 0 := by
      rw [← inv_smul_eq_iff, ← map_inv, inv_inv, ← mul_smul, ← mul_smul, ← map_mul, ← map_mul,
        keyM]
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨_, h, hh, rfl⟩, heq⟩
      exact ⟨h, hh, (key h).mp (congrArg Subtype.val heq)⟩
    · rintro ⟨h, hh, hc⟩
      exact ⟨⟨mapGL ℝ h, Subgroup.mem_map_of_mem _ hh⟩, Subtype.ext ((key h).mpr hc)⟩
  · obtain ⟨q, rfl⟩ := surjective_cosetToCuspOrbit 𝒢 C
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨γ, rfl⟩

/-- `orbitRelQuotientEquivCuspOrbits` sends the `⟨T⟩`-orbit of `γ Γ'` to `cosetToCuspOrbit _ ⟦γ⟧`.
-/
@[simp]
theorem orbitRelQuotientEquivCuspOrbits_mk (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex]
    (γ : SL(2, ℤ)) :
    have : (Γ'.liftSL.map (mapGL ℝ)).IsArithmetic :=
      inferInstanceAs (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)).IsArithmetic
    orbitRelQuotientEquivCuspOrbits Γ'
        (Quotient.mk'' ((γ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ')) =
      cosetToCuspOrbit (Γ'.liftSL.map (mapGL ℝ)) ⟦γ⟧ := (rfl)

/-- **Cycles of `permT Γ' e` are Mathlib cusp orbits** of `Γ'.liftSL.map (mapGL ℝ)`. -/
def permTCycleEquivCuspOrbits (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    Quotient (SameCycle.setoid (permT Γ' e)) ≃ CuspOrbits (Γ'.liftSL.map (mapGL ℝ)) :=
  have : Γ'.FiniteIndex := Γ'.finiteIndex_of_equiv e
  (permTCycleEquivOrbitRelQuotient Γ' e).trans (orbitRelQuotientEquivCuspOrbits Γ')

/-- **Cusps are cusp orbits**: `cuspCount Γ' e` equals the number of cusp orbits of
`Γ'.liftSL.map (mapGL ℝ)` in Mathlib's sense. -/
theorem cuspCount_eq_card_cuspOrbits (Γ' : Subgroup PSL(2, ℤ)) (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e = Nat.card (CuspOrbits (Γ'.liftSL.map (mapGL ℝ))) := by
  rw [cuspCount, orbitCount_def]
  exact Nat.card_congr (permTCycleEquivCuspOrbits Γ' e)

/-! ### Width ratios, ramification indices, and tower cycle-length sums -/

section Tower

/-- Along an inclusion `h : Γ₁' ≤ Γ₂'`, the cycle length of `permT Γ₂' e₂` divides that of
`permT Γ₁' e₁` on every coset. -/
theorem period_permT_dvd_of_le {Γ₁' Γ₂' : Subgroup PSL(2, ℤ)} (h : Γ₁' ≤ Γ₂') {n₁ n₂ : ℕ}
    (e₁ : PSL(2, ℤ) ⧸ Γ₁' ≃ Fin n₁) (e₂ : PSL(2, ℤ) ⧸ Γ₂' ≃ Fin n₂) (q : PSL(2, ℤ) ⧸ Γ₁') :
    MulAction.period (permT Γ₂' e₂) (e₂ (Subgroup.quotientMapOfLE h q)) ∣
      MulAction.period (permT Γ₁' e₁) (e₁ q) := by
  rw [permT, modularTriple_σinf, permT, modularTriple_σinf,
    e₁.period_permutationRepresentation, e₂.period_permutationRepresentation]
  exact Subgroup.period_quotientMapOfLE_dvd h (T : PSL(2, ℤ)) q

/-- **Width ratio via `CuspDatum.widthIndex`.** For `h : Γ₁' ≤ Γ₂'` and `σ : SL(2, ℤ)`, using the
same integral scaling `(sl2zToPSL2R σ)⁻¹` for both normalized cusp data, the cycle length of
`permT Γ₁' e₁` at `σ ∞` is `widthIndex` times the cycle length of `permT Γ₂' e₂`. -/
theorem period_permT_coset_eq_widthIndex_mul {Γ₁' Γ₂' : Subgroup PSL(2, ℤ)} (h : Γ₁' ≤ Γ₂')
    {n₁ n₂ : ℕ} (e₁ : PSL(2, ℤ) ⧸ Γ₁' ≃ Fin n₁) (e₂ : PSL(2, ℤ) ⧸ Γ₂' ≃ Fin n₂) (σ : SL(2, ℤ)) :
    let : Γ₁'.FiniteIndex := Γ₁'.finiteIndex_of_equiv e₁
    let : Γ₂'.FiniteIndex := Γ₂'.finiteIndex_of_equiv e₂
    MulAction.period (permT Γ₁' e₁) (e₁ (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ₁')) =
      TauCeti.Subgroup.CuspDatum.widthIndex (Subgroup.map_mono h) (cuspDatumPSL Γ₁' σ)
          (cuspDatumPSL Γ₂' σ) (by simp) *
        MulAction.period (permT Γ₂' e₂)
          (e₂ (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ₂')) := by
  intro _ _
  have hw := TauCeti.Subgroup.CuspDatum.width_eq_widthIndex_mul (Subgroup.map_mono h)
    (cuspDatumPSL Γ₁' σ) (cuspDatumPSL Γ₂' σ) (by simp)
  rw [cuspDatumPSL_width_eq_period_permT Γ₁' e₁ σ,
    cuspDatumPSL_width_eq_period_permT Γ₂' e₂ σ] at hw
  exact_mod_cast hw

/-- **Width ratio via `localMultiplicity`.** At the adjoined cusp `σ • ∞`, the local multiplicity
of the compactified quotient map `X(Γ₁') → X(Γ₂')` times the downstairs cusp width equals the
upstairs cusp width. -/
theorem period_permT_coset_eq_localMultiplicity_mul {Γ₁' Γ₂' : Subgroup PSL(2, ℤ)} (h : Γ₁' ≤ Γ₂')
    {n₁ n₂ : ℕ} (e₁ : PSL(2, ℤ) ⧸ Γ₁' ≃ Fin n₁) (e₂ : PSL(2, ℤ) ⧸ Γ₂' ≃ Fin n₂) (σ : SL(2, ℤ)) :
    let : Γ₁'.FiniteIndex := Γ₁'.finiteIndex_of_equiv e₁
    let : Γ₂'.FiniteIndex := Γ₂'.finiteIndex_of_equiv e₂
    let : DiscreteTopology (Γ₂'.map psl2zToPSL2R) := by
      rw [← Γ₂'.map_sl2zToPSL2R_liftSL]
      exact Γ₂'.liftSL.isCofinite_map_sl2zToPSL2R.discreteTopology
    let : DiscreteTopology (Γ₁'.map psl2zToPSL2R) :=
      DiscreteTopology.of_subset ‹_› (Subgroup.map_mono h)
    TauCeti.RiemannSurface.localMultiplicity
        (Subgroup.compactifiedQuotientMap (Subgroup.map_mono h))
        (Subgroup.CompactifiedQuotient.ofCusp (cuspDatumPSL Γ₁' σ).cuspOrbit) *
      MulAction.period (permT Γ₂' e₂)
        (e₂ (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ₂')) =
      MulAction.period (permT Γ₁' e₁)
        (e₁ (((σ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ₁')) := by
  intro _ _ _ _
  rw [Subgroup.CompactifiedQuotient.localMultiplicity_compactifiedQuotientMap_ofCusp_eq_widthIndex
      (Subgroup.map_mono h) (cuspDatumPSL Γ₁' σ) (cuspDatumPSL Γ₂' σ) (by simp),
    ← period_permT_coset_eq_widthIndex_mul h e₁ e₂ σ]

/-- Projection from cycles of `permT Γ₁' e₁` to cycles of `permT Γ₂' e₂` induced by `h : Γ₁' ≤ Γ₂'`.
-/
def permTCycleMapOfLE {Γ₁' Γ₂' : Subgroup PSL(2, ℤ)} (h : Γ₁' ≤ Γ₂') {n₁ n₂ : ℕ}
    (e₁ : PSL(2, ℤ) ⧸ Γ₁' ≃ Fin n₁) (e₂ : PSL(2, ℤ) ⧸ Γ₂' ≃ Fin n₂) :
    Quotient (SameCycle.setoid (permT Γ₁' e₁)) →
      Quotient (SameCycle.setoid (permT Γ₂' e₂)) :=
  (permTCycleEquivOrbitRelQuotient Γ₂' e₂).symm ∘
    Subgroup.quotientOrbitRelQuotientMapOfLE h (Subgroup.zpowers (T : PSL(2, ℤ))) ∘
      permTCycleEquivOrbitRelQuotient Γ₁' e₁

/-- `permTCycleMapOfLE` sends the cycle of `e₁ q` to the cycle of `e₂ (quotientMapOfLE h q)`. -/
@[simp]
theorem permTCycleMapOfLE_mk {Γ₁' Γ₂' : Subgroup PSL(2, ℤ)} (h : Γ₁' ≤ Γ₂') {n₁ n₂ : ℕ}
    (e₁ : PSL(2, ℤ) ⧸ Γ₁' ≃ Fin n₁) (e₂ : PSL(2, ℤ) ⧸ Γ₂' ≃ Fin n₂) (q : PSL(2, ℤ) ⧸ Γ₁') :
    permTCycleMapOfLE h e₁ e₂ (Quotient.mk (SameCycle.setoid (permT Γ₁' e₁)) (e₁ q)) =
      Quotient.mk (SameCycle.setoid (permT Γ₂' e₂)) (e₂ (Subgroup.quotientMapOfLE h q)) := by
  simp [permTCycleMapOfLE]

open scoped Classical in
/-- **Tower sum of cycle lengths.** Over any cycle of `permT Γ₂' e₂` through `i : Fin n₂`, the
lengths of the cycles of `permT Γ₁' e₁` in its preimage sum to
`MulAction.period (permT Γ₂' e₂) i * [Γ₂' : Γ₁']`. -/
theorem sum_cycleLength_fiber_permTCycleMapOfLE {Γ₁' Γ₂' : Subgroup PSL(2, ℤ)} (h : Γ₁' ≤ Γ₂')
    {n₁ n₂ : ℕ} (e₁ : PSL(2, ℤ) ⧸ Γ₁' ≃ Fin n₁) (e₂ : PSL(2, ℤ) ⧸ Γ₂' ≃ Fin n₂) (i : Fin n₂) :
    (∑ c : {c : Quotient (SameCycle.setoid (permT Γ₁' e₁)) //
        permTCycleMapOfLE h e₁ e₂ c = Quotient.mk (SameCycle.setoid (permT Γ₂' e₂)) i},
      Nat.card {j : Fin n₁ // Quotient.mk (SameCycle.setoid (permT Γ₁' e₁)) j = c.1}) =
      MulAction.period (permT Γ₂' e₂) i * Γ₁'.relIndex Γ₂' := by
  have : Γ₁'.FiniteIndex := Γ₁'.finiteIndex_of_equiv e₁
  have : Γ₁'.IsFiniteRelIndex Γ₂' := ⟨Subgroup.index_ne_zero_of_finite⟩
  have : Finite (PSL(2, ℤ) ⧸ Γ₂') := Finite.of_equiv (Fin n₂) e₂.symm
  let eq₁ := permTCycleEquivOrbitRelQuotient Γ₁' e₁
  let eq₂ := permTCycleEquivOrbitRelQuotient Γ₂' e₂
  let ω : orbitRel.Quotient (Subgroup.zpowers (T : PSL(2, ℤ))) (PSL(2, ℤ) ⧸ Γ₂') :=
    Quotient.mk'' (e₂.symm i)
  have hfib : ∀ c : Quotient (SameCycle.setoid (permT Γ₁' e₁)),
      permTCycleMapOfLE h e₁ e₂ c = Quotient.mk (SameCycle.setoid (permT Γ₂' e₂)) i ↔
        Subgroup.quotientOrbitRelQuotientMapOfLE h (Subgroup.zpowers (T : PSL(2, ℤ))) (eq₁ c) =
          ω := by
    intro c
    rw [permTCycleMapOfLE, Function.comp_apply, Function.comp_apply, eq₂.symm_apply_eq,
      permTCycleEquivOrbitRelQuotient_mk]
  let efib := eq₁.subtypeEquiv
    (p := fun c ↦ permTCycleMapOfLE h e₁ e₂ c = Quotient.mk (SameCycle.setoid (permT Γ₂' e₂)) i)
    (q := fun x ↦
      Subgroup.quotientOrbitRelQuotientMapOfLE h (Subgroup.zpowers (T : PSL(2, ℤ))) x = ω)
    hfib
  let : Fintype {b : orbitRel.Quotient (Subgroup.zpowers (T : PSL(2, ℤ))) (PSL(2, ℤ) ⧸ Γ₁') //
      Subgroup.quotientOrbitRelQuotientMapOfLE h (Subgroup.zpowers (T : PSL(2, ℤ))) b = ω} :=
    Fintype.ofEquiv _ efib
  have hcard (c : Quotient (SameCycle.setoid (permT Γ₁' e₁))) :
      Nat.card {j : Fin n₁ // Quotient.mk (SameCycle.setoid (permT Γ₁' e₁)) j = c} =
        Nat.card (eq₁ c).orbit :=
    Nat.card_congr <| e₁.symm.subtypeEquiv fun j ↦ by
      rw [orbitRel.Quotient.mem_orbit, ← permTCycleEquivOrbitRelQuotient_mk Γ₁' e₁ j]
      exact eq₁.injective.eq_iff.symm
  have hsum :
      (∑ c : {c : Quotient (SameCycle.setoid (permT Γ₁' e₁)) //
          permTCycleMapOfLE h e₁ e₂ c = Quotient.mk (SameCycle.setoid (permT Γ₂' e₂)) i},
        Nat.card {j : Fin n₁ // Quotient.mk (SameCycle.setoid (permT Γ₁' e₁)) j = c.1}) =
        ∑ c : {c : Quotient (SameCycle.setoid (permT Γ₁' e₁)) //
          permTCycleMapOfLE h e₁ e₂ c = Quotient.mk (SameCycle.setoid (permT Γ₂' e₂)) i},
          Nat.card (efib c).1.orbit :=
    Finset.sum_congr rfl fun c _ ↦ hcard c.1
  rw [hsum, efib.sum_comp (fun b ↦ Nat.card b.1.orbit),
    Subgroup.sum_natCard_orbit_fiber_quotientOrbitRelQuotientMapOfLE h
      (Subgroup.zpowers (T : PSL(2, ℤ))) ω,
    orbitRel.Quotient.orbit_mk, MulAction.natCard_orbit_zpowers, permT, modularTriple_σinf,
    ← e₂.period_permutationRepresentation, apply_symm_apply]

end Tower

/-! ### Level-one values and explicit checks -/

/-- For the full modular group `⊤`, the cusp-width multiset is `{1}`. -/
@[simp]
theorem cuspWidths_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) :
    cuspWidths ⊤ e = {1} := by
  have h1 : permT ⊤ e = 1 := Subsingleton.elim _ _
  rw [cuspWidths, h1, fullCycleType_one, Fintype.card_fin]
  rfl

/-- For the full modular group `⊤`, the cusp count is `1`. -/
@[simp]
theorem cuspCount_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) :
    cuspCount ⊤ e = 1 := by
  rw [← card_cuspWidths, cuspWidths_top, Multiset.card_singleton]

/-- For the full modular group `⊤`, the cycle length of `permT ⊤ e` is `1`. -/
theorem period_permT_top (e : PSL(2, ℤ) ⧸ (⊤ : Subgroup PSL(2, ℤ)) ≃ Fin 1) (i : Fin 1) :
    MulAction.period (permT ⊤ e) i = 1 := by
  have h1 : permT ⊤ e = 1 := Subsingleton.elim _ _
  rw [h1, MulAction.period_one]

/-- Rescaling the level-one cusp `∞` by `diag(2, 2⁻¹)` multiplies the normalized cusp width by `4`,
giving a valid `CuspDatum` of width `4 = 4 · 1` that does not have integral scaling in `PSL(2, ℤ)`.
-/
theorem exists_cuspDatum_infty_diag_two :
    let g : SL(2, ℝ) := ⟨!![(2 : ℝ), 0; 0, (2 : ℝ)⁻¹], by rw [Matrix.det_fin_two_of]; norm_num⟩
    ∃ D : psl2zToPSL2R.range.CuspDatum,
      D.cusp = ∞ ∧ D.scaling = (g : PSL(2, ℝ)) ∧ D.width = 4 := by
  intro g
  have : DiscreteTopology psl2zToPSL2R.range := isCofinite_psl2zToPSL2RRange.discreteTopology
  have hg : (g : PSL(2, ℝ)) • (∞ : OnePoint ℝ) = ∞ := by
    rw [OnePoint.pslMk_smul, OnePoint.smul_infty_eq_self_iff,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    rfl
  obtain ⟨D, hDc, hDσ⟩ := isCuspPoint_infty.exists_cuspDatum hg
  refine ⟨D, hDc, hDσ, ?_⟩
  have hw := TauCeti.cuspDatum_width_eq_mul (D := cuspDatumInfty) (D' := D) (a := 4) (b := 0)
    (by rw [cuspDatumInfty_cusp, hDc]) fun z ↦ by
      rw [hDσ, cuspDatumInfty_scaling, one_smul, UpperHalfPlane.pslMk_smul,
        UpperHalfPlane.coe_specialLinearGroup_apply]
      simp [g]
      ring
  simpa using hw

section Checks

-- A transposition on three points has full cycle partition `{2, 1}`, sum `3`, and orbit count `2`.
example :
    (swap (0 : Fin 3) 1).fullCycleType = {2, 1} ∧
      (swap (0 : Fin 3) 1).fullCycleType.sum = 3 ∧
      orbitCount (swap (0 : Fin 3) 1) = 2 := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hft : (swap (0 : Fin 3) 1).fullCycleType = {2, 1} := by
    rw [fullCycleType_def, parts_partition]
    simp only [support_swap h01, Finset.card_pair h01, Fintype.card_fin,
      isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr h01)]
    rfl
  exact ⟨hft, by simp, by rw [orbitCount_eq_card_parts_partition, ← fullCycleType_def, hft]; rfl⟩

-- The identity on three points has full cycle partition `{1, 1, 1}`, sum `3`, and orbit count `3`.
example :
    (1 : Perm (Fin 3)).fullCycleType = {1, 1, 1} ∧
      (1 : Perm (Fin 3)).fullCycleType.sum = 3 ∧
      orbitCount (1 : Perm (Fin 3)) = 3 :=
  ⟨by rw [fullCycleType_one]; rfl, by simp, by simp [orbitCount_one]⟩

end Checks

end TauCeti.ModularGroup

end
