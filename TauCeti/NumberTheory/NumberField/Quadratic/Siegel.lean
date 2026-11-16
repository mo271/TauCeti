/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.NumberTheory.NumberField.QuadraticAlgebra
import TauCeti.NumberTheory.LSeries.Quadratic.Siegel
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta
import TauCeti.NumberTheory.NumberField.Quadratic.Model
import TauCeti.NumberTheory.NumberField.Quadratic.Radicand
import TauCeti.NumberTheory.QuadraticOrder.Field

/-!
# Siegel's class-number lower bound and finiteness for imaginary quadratic fields

Combining Siegel's theorem (`TauCeti.quadratic_LFunction_siegel`) with the analytic class-number
inequality `√|D| Re L(1, χ_D) / π ≤ h(K)`
(`TauCeti.NumberField.sqrt_mul_LFunction_one_re_div_le_classNumber`) gives the uniform ineffective
lower bound

`c_ε |disc K| ^ (1 / 2 - ε) ≤ h(K)`

for every `ε > 0` and every imaginary quadratic number field `K`. Specializing `ε = 1 / 4` bounds
`|disc K|` in terms of `h(K)` (`(|disc K|) ^ (1 / 4) ≤ h(K) / c_{1/4}`), including the degenerate
bound `B = 0` and the class-number-one threshold `B = 1`.

From this discriminant bound follow all qualitative finiteness and divergence consequences of the
Gauss–Heilbronn–Siegel class-number problem:
* Only finitely many discriminants — and only finitely many negative fundamental discriminants `D` —
  occur among imaginary quadratic fields with `h(K) ≤ B` (or in a single fiber `h(K) = B`).
* Only finitely many negative squarefree radicands `d` satisfy `h(ℚ(√d)) ≤ B` (or `= B`), and via
  the radicand classification (`NumberField.existsUnique_neg_squarefree_algEquiv`) only finitely
  many imaginary quadratic fields up to `ℚ`-algebra isomorphism have class number at most `B`.
* The class number tends to infinity along any family of imaginary quadratic fields whose
  discriminants tend to infinity in absolute value, and in particular along negative fundamental
  discriminants `D → -∞` and negative squarefree radicands `d → -∞`.

Because the constant in Siegel's theorem is ineffective, none of these finiteness theorems yields
an explicit discriminant cutoff or numerical enumeration.

## Main results

* `QuadraticAlgebra.discr_eq_of_isFundamentalDiscr`: for a fundamental discriminant `D`,
  `NumberField.discr ℚ(√D) = D`.
* `TauCeti.NumberField.imaginary_classNumber_lower_bound`: for every `ε > 0` there is `c > 0` with
  `c |disc L| ^ (1 / 2 - ε) ≤ h(L)` for every imaginary quadratic field `L`.
* `TauCeti.NumberField.imaginary_discr_bounded_of_classNumber_le`: for every `B : ℕ`, `|disc L|` is
  uniformly bounded over imaginary quadratic fields `L` with `h(L) ≤ B`.
* `TauCeti.NumberField.exists_finset_imaginary_discr_of_classNumber_le`,
  `TauCeti.NumberField.exists_finset_neg_isFundamentalDiscr_of_classNumber_le`, and their `_eq`
  companions: finiteness of discriminants and fibers of bounded or fixed class number.
* `TauCeti.NumberField.imaginary_radicand_bounded_of_classNumber_le`,
  `TauCeti.NumberField.exists_finset_neg_squarefree_of_classNumber_le`,
  `TauCeti.NumberField.exists_finset_neg_squarefree_of_classNumber_eq`, and
  `TauCeti.NumberField.exists_finset_algEquiv_of_classNumber_le`: radicand bounds, radicand
  finiteness, and finiteness up to `ℚ`-algebra isomorphism.
* `TauCeti.NumberField.tendsto_classNumber_atTop`,
  `TauCeti.NumberField.tendsto_classNumber_quadraticAlgebra_of_isFundamentalDiscr`, and
  `TauCeti.NumberField.tendsto_classNumber_quadraticAlgebra_of_squarefree`: divergence `h → ∞` as
  `|D| → ∞`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapters 6 and 21.
* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
-/

public section

open Filter NumberField Polynomial
open scoped NumberField

universe u

namespace QuadraticAlgebra

/-- **The discriminant of `ℚ(√D)` at a fundamental discriminant `D` is `D`.** For a nonsquare
fundamental discriminant `D`, the quadratic order `ℤ[(D + √D) / 2]` of discriminant `D` is the
maximal order of `ℚ(√D)`. -/
theorem discr_eq_of_isFundamentalDiscr {D : ℤ} [Fact (¬ IsSquare D)]
    (hD : Int.IsFundamentalDiscr D) :
    NumberField.discr (QuadraticAlgebra ℚ (D : ℚ) 0) = D := by
  have hmod := hD.emod_four_eq_zero_or_one
  rw [← TauCeti.GlobalNumberFields.NumberFieldOrder.discr_maximal,
    ← (TauCeti.QuadraticOrder.numberFieldOrder_eq_maximal_iff D hmod).mpr hD,
    TauCeti.QuadraticOrder.numberFieldOrder_discr]

end QuadraticAlgebra

namespace TauCeti.NumberField

/-! ### Uniform lower bound and discriminant bound -/

/-- **Uniform class-number lower bound for imaginary quadratic fields.** For every `ε > 0`, there
exists `c > 0` such that `c |disc L| ^ (1 / 2 - ε) ≤ h(L)` for every imaginary quadratic field `L`.
The constant `c` comes from Siegel's theorem (`TauCeti.quadratic_LFunction_siegel`) via the class
number inequality `√|disc L| Re L(1, χ_D) / π ≤ h(L)` with `w_L ≥ 2`, and is ineffective. -/
theorem imaginary_classNumber_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (L : Type u) [Field L] [NumberField L]
      [NumberField.IsTotallyComplex L], Module.finrank ℚ L = 2 →
      c * Real.rpow (|NumberField.discr L| : ℝ) (1 / 2 - ε) ≤
        (NumberField.classNumber L : ℝ) := by
  obtain ⟨c₀, hc₀, hsiegel⟩ := TauCeti.quadratic_LFunction_siegel ε hε
  refine ⟨c₀ / Real.pi, by positivity, fun L _ _ _ hL ↦ ?_⟩
  have hfund := Multiquadratic.isFundamentalDiscr_discr hL
  set χ : DirichletCharacter ℂ (discr L).natAbs :=
    (Multiquadratic.fundamentalDiscriminantChar (discr L) hfund).ringHomComp (Int.castRingHom ℂ)
  have hχp : χ.IsPrimitive :=
    (DirichletCharacter.isPrimitive_ringHomComp_iff _ _ Int.cast_injective).mpr
      (Multiquadratic.isPrimitive_fundamentalDiscriminantChar hfund)
  have hχq : χ.IsQuadratic := (Multiquadratic.fundamentalDiscriminantChar_isQuadratic hfund).comp _
  have hχ1 : χ ≠ 1 := Multiquadratic.ringHomComp_fundamentalDiscriminantChar_discr_ne_one hL
  have hL_lb : c₀ * (|discr L| : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re := by
    simpa only [Real.rpow_eq_pow, Nat.cast_natAbs, Int.cast_abs] using
      hsiegel (discr L).natAbs χ hχp hχq hχ1
  have hD_pos : 0 < (|discr L| : ℝ) := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero L))
  have hcnf := sqrt_mul_LFunction_one_re_div_le_classNumber hL
  rw [Real.rpow_eq_pow]
  calc
    c₀ / Real.pi * (|discr L| : ℝ) ^ (1 / 2 - ε)
      = (|discr L| : ℝ) ^ (1 / 2 : ℝ) * (c₀ * (|discr L| : ℝ) ^ (-ε)) / Real.pi := by
          rw [sub_eq_add_neg, Real.rpow_add hD_pos]
          ring
    _ = √(|discr L| : ℝ) * (c₀ * (|discr L| : ℝ) ^ (-ε)) / Real.pi := by
          rw [Real.sqrt_eq_rpow]
    _ ≤ √(|discr L| : ℝ) * (χ.LFunction 1).re / Real.pi := by gcongr
    _ ≤ (classNumber L : ℝ) := hcnf

/-- **Discriminant bound for imaginary quadratic fields of bounded class number.** For every bound
`B : ℕ` (including `B = 0` and `B = 1`), there is an ineffective real constant `C` such that every
imaginary quadratic field `L` with `classNumber L ≤ B` satisfies `|disc L| ≤ C`. -/
theorem imaginary_discr_bounded_of_classNumber_le (B : ℕ) :
    ∃ C : ℝ, ∀ (L : Type u) [Field L] [NumberField L]
      [NumberField.IsTotallyComplex L], Module.finrank ℚ L = 2 →
      NumberField.classNumber L ≤ B → (|NumberField.discr L| : ℝ) ≤ C := by
  obtain ⟨c, hc, hlb⟩ := imaginary_classNumber_lower_bound.{u} (1 / 4) (by norm_num)
  refine ⟨((B : ℝ) / c) ^ (4 : ℝ), fun L _ _ _ hL hB ↦ ?_⟩
  have hD_nonneg : 0 ≤ (|discr L| : ℝ) := by positivity
  have hquarter : (|discr L| : ℝ) ^ (1 / 4 : ℝ) ≤ (B : ℝ) / c := by
    rw [le_div_iff₀ hc, mul_comm]
    refine (le_of_eq ?_).trans ((hlb L hL).trans (Nat.cast_le.mpr hB))
    rw [Real.rpow_eq_pow]
    congr 2
    norm_num
  calc
    (|discr L| : ℝ) = ((|discr L| : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) := by
        rw [← Real.rpow_mul hD_nonneg]
        norm_num
    _ ≤ ((B : ℝ) / c) ^ (4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hquarter (by norm_num)

/-! ### Finiteness of discriminants, radicands, fibers, and isomorphism classes -/

/-- Bounded real absolute value restricts an integer to `[-⌈max C 0⌉₊, ⌈max C 0⌉₊]`. -/
private theorem mem_Icc_of_abs_cast_le {x : ℤ} {C : ℝ} (h : |(x : ℝ)| ≤ C) :
    x ∈ Finset.Icc (-(⌈max C 0⌉₊ : ℤ)) (⌈max C 0⌉₊ : ℤ) := by
  have habsR : ((|x| : ℤ) : ℝ) ≤ ((⌈max C 0⌉₊ : ℤ) : ℝ) := by
    rw [Int.cast_abs, Int.cast_natCast]
    exact (h.trans (le_max_left _ _)).trans (Nat.le_ceil _)
  exact Finset.mem_Icc.mpr (abs_le.mp (Int.cast_le.mp habsR))

/-- **Finiteness of discriminants of imaginary quadratic fields with bounded class number.** For
every `B : ℕ`, there is a finite set `s : Finset ℤ` containing `disc L` for every imaginary
quadratic field `L` with `classNumber L ≤ B`. -/
theorem exists_finset_imaginary_discr_of_classNumber_le (B : ℕ) :
    ∃ s : Finset ℤ, ∀ (L : Type u) [Field L] [NumberField L]
      [NumberField.IsTotallyComplex L], Module.finrank ℚ L = 2 →
      NumberField.classNumber L ≤ B → NumberField.discr L ∈ s := by
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{u} B
  exact ⟨Finset.Icc (-(⌈max C 0⌉₊ : ℤ)) (⌈max C 0⌉₊ : ℤ),
    fun L _ _ _ hL hB ↦ mem_Icc_of_abs_cast_le (hC L hL hB)⟩

/-- **Finite discriminant fibers of the class number.** For every `B : ℕ`, only finitely many
discriminants occur among imaginary quadratic fields of class number `B`. -/
theorem exists_finset_imaginary_discr_of_classNumber_eq (B : ℕ) :
    ∃ s : Finset ℤ, ∀ (L : Type u) [Field L] [NumberField L]
      [NumberField.IsTotallyComplex L], Module.finrank ℚ L = 2 →
      NumberField.classNumber L = B → NumberField.discr L ∈ s := by
  obtain ⟨s, hs⟩ := exists_finset_imaginary_discr_of_classNumber_le.{u} B
  exact ⟨s, fun L _ _ _ hL hB ↦ hs L hL hB.le⟩

/-- **Finiteness of negative fundamental discriminants with bounded class number.** For every
`B : ℕ`, only finitely many negative fundamental discriminants `D` satisfy
`classNumber ℚ(√D) ≤ B`. -/
theorem exists_finset_neg_isFundamentalDiscr_of_classNumber_le (B : ℕ) :
    ∃ s : Finset ℤ, ∀ (D : ℤ) [Fact (¬ IsSquare D)],
      D < 0 → Int.IsFundamentalDiscr D →
        NumberField.classNumber (QuadraticAlgebra ℚ (D : ℚ) 0) ≤ B → D ∈ s := by
  obtain ⟨s, hs⟩ := exists_finset_imaginary_discr_of_classNumber_le.{0} B
  refine ⟨s, fun D _ hneg hfund hB ↦ ?_⟩
  have : IsTotallyComplex (QuadraticAlgebra ℚ (D : ℚ) 0) :=
    QuadraticAlgebra.isTotallyComplex_iff.mpr (by exact_mod_cast hneg)
  simpa [QuadraticAlgebra.discr_eq_of_isFundamentalDiscr hfund] using
    hs (QuadraticAlgebra ℚ (D : ℚ) 0) (QuadraticAlgebra.finrank_eq_two _ _) hB

/-- **Finite fibers of the class number over negative fundamental discriminants.** For every
`B : ℕ`, only finitely many negative fundamental discriminants `D` satisfy
`classNumber ℚ(√D) = B`. -/
theorem exists_finset_neg_isFundamentalDiscr_of_classNumber_eq (B : ℕ) :
    ∃ s : Finset ℤ, ∀ (D : ℤ) [Fact (¬ IsSquare D)],
      D < 0 → Int.IsFundamentalDiscr D →
        NumberField.classNumber (QuadraticAlgebra ℚ (D : ℚ) 0) = B → D ∈ s := by
  obtain ⟨s, hs⟩ := exists_finset_neg_isFundamentalDiscr_of_classNumber_le B
  exact ⟨s, fun D _ hneg hfund hB ↦ hs D hneg hfund hB.le⟩

/-- For a nonsquare squarefree integer `d`, `|d| ≤ |disc ℚ(√d)|` since `disc ℚ(√d)` is `d` or
`4d`. -/
private theorem abs_le_abs_discr_quadraticAlgebra {d : ℤ} [Fact (¬ IsSquare d)]
    (hsf : Squarefree d) :
    |d| ≤ |NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0)| := by
  by_cases hd4 : d % 4 = 1
  · rw [QuadraticAlgebra.discr_eq_of_mod_four_eq_one hsf hd4]
  · rw [QuadraticAlgebra.discr_eq_four_mul_of_mod_four_ne_one hsf hd4, abs_mul]
    have : (1 : ℤ) ≤ |(4 : ℤ)| := by norm_num
    exact le_mul_of_one_le_left (abs_nonneg d) this

/-- **Radicand bound for imaginary quadratic fields of bounded class number.** For every `B : ℕ`,
there is a real bound `M` such that if `L` is an imaginary quadratic field with `classNumber L ≤ B`
and `θ : 𝓞 L` has minimal polynomial `X² - d` with `d` squarefree, then `|d| ≤ M`. -/
theorem imaginary_radicand_bounded_of_classNumber_le (B : ℕ) :
    ∃ M : ℝ, ∀ (L : Type u) [Field L] [NumberField L]
      [NumberField.IsTotallyComplex L], Module.finrank ℚ L = 2 →
      ∀ (θ : 𝓞 L) (d : ℤ), Squarefree d → minpoly ℤ θ = X ^ 2 - C d →
        NumberField.classNumber L ≤ B → (|d| : ℝ) ≤ M := by
  obtain ⟨M, hM⟩ := imaginary_discr_bounded_of_classNumber_le.{u} B
  refine ⟨M, fun L _ _ _ hL θ d hsf hmin hB ↦ ?_⟩
  have : Fact (¬ IsSquare d) := ⟨Rat.isSquare_intCast_iff.not.mp (not_isSquare_radicand hmin)⟩
  obtain ⟨φ⟩ := nonempty_algEquiv_quadraticAlgebra hL hmin
  have hle : (|d| : ℝ) ≤ (|discr L| : ℝ) := by
    rw [← Int.cast_abs, ← Int.cast_abs, Int.cast_le, discr_eq_discr_of_algEquiv L φ]
    exact abs_le_abs_discr_quadraticAlgebra hsf
  exact hle.trans (hM L hL hB)

/-- **Finiteness of negative squarefree radicands with bounded class number.** For every `B : ℕ`,
only finitely many negative squarefree integers `d` satisfy `classNumber ℚ(√d) ≤ B`. -/
theorem exists_finset_neg_squarefree_of_classNumber_le (B : ℕ) :
    ∃ s : Finset ℤ, ∀ (d : ℤ) [Fact (¬ IsSquare d)],
      d < 0 → Squarefree d →
        NumberField.classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) ≤ B → d ∈ s := by
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{0} B
  refine ⟨Finset.Icc (-(⌈max C 0⌉₊ : ℤ)) (⌈max C 0⌉₊ : ℤ), fun d _ hneg hsf hB ↦ ?_⟩
  have : IsTotallyComplex (QuadraticAlgebra ℚ (d : ℚ) 0) :=
    QuadraticAlgebra.isTotallyComplex_iff.mpr (by exact_mod_cast hneg)
  have hd_le : |(d : ℝ)| ≤ C := by
    have h1 : |(d : ℝ)| ≤ |(discr (QuadraticAlgebra ℚ (d : ℚ) 0) : ℝ)| := by
      simpa only [Int.cast_abs] using
        (Int.cast_le (R := ℝ)).mpr (abs_le_abs_discr_quadraticAlgebra hsf)
    exact h1.trans (hC (QuadraticAlgebra ℚ (d : ℚ) 0) (QuadraticAlgebra.finrank_eq_two _ _) hB)
  exact mem_Icc_of_abs_cast_le hd_le

/-- **Finite fibers of the class number over negative squarefree radicands.** For every `B : ℕ`,
only finitely many negative squarefree integers `d` satisfy `classNumber ℚ(√d) = B`. -/
theorem exists_finset_neg_squarefree_of_classNumber_eq (B : ℕ) :
    ∃ s : Finset ℤ, ∀ (d : ℤ) [Fact (¬ IsSquare d)],
      d < 0 → Squarefree d →
        NumberField.classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) = B → d ∈ s := by
  obtain ⟨s, hs⟩ := exists_finset_neg_squarefree_of_classNumber_le B
  exact ⟨s, fun d _ hneg hsf hB ↦ hs d hneg hsf hB.le⟩

/-- **Finiteness of imaginary quadratic fields of bounded class number up to isomorphism.** For
every `B : ℕ`, there is a finite set `s` of negative squarefree integers such that every imaginary
quadratic field `L` with `classNumber L ≤ B` is `ℚ`-isomorphic to `QuadraticAlgebra ℚ d 0` for a
unique `d ∈ s`. -/
theorem exists_finset_algEquiv_of_classNumber_le (B : ℕ) :
    ∃ s : Finset ℤ,
      (∀ d ∈ s, d < 0 ∧ Squarefree d) ∧
      ∀ (L : Type u) [Field L] [NumberField L] [NumberField.IsTotallyComplex L],
        Module.finrank ℚ L = 2 → NumberField.classNumber L ≤ B →
        ∃! d : ℤ, d ∈ s ∧ Nonempty (L ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0) := by
  classical
  obtain ⟨s₀, hs₀⟩ := exists_finset_neg_squarefree_of_classNumber_le B
  let s := s₀.filter fun d ↦ d < 0 ∧ Squarefree d
  refine ⟨s, fun d hd ↦ (Finset.mem_filter.mp hd).2, fun L _ _ _ hL hB ↦ ?_⟩
  obtain ⟨d, ⟨hneg, hsf, ⟨φ⟩⟩, huniq⟩ := existsUnique_neg_squarefree_algEquiv hL
  have : Fact (¬ IsSquare d) := ⟨not_isSquare_of_neg hneg⟩
  have hclass : classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) ≤ B := by
    rwa [← φ.toRingEquiv.classNumber_eq]
  have hmem : d ∈ s := Finset.mem_filter.mpr ⟨hs₀ d hneg hsf hclass, hneg, hsf⟩
  refine ⟨d, ⟨hmem, ⟨φ⟩⟩, fun e ⟨he_mem, hψ⟩ ↦ ?_⟩
  obtain ⟨he_neg, he_sf⟩ := (Finset.mem_filter.mp he_mem).2
  exact huniq e ⟨he_neg, he_sf, hψ⟩

/-! ### Divergence of the class number as `|D| → ∞` -/

/-- **Class numbers of imaginary quadratic fields diverge with the discriminant.** Along any filter
on a family of imaginary quadratic number fields whose discriminants tend to `∞` in absolute value,
`classNumber` tends to `∞`. -/
theorem tendsto_classNumber_atTop {ι : Type*} {l : Filter ι}
    (L : ι → Type u) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (hcomplex : ∀ᶠ i in l, NumberField.IsTotallyComplex (L i))
    (hdeg : ∀ᶠ i in l, Module.finrank ℚ (L i) = 2)
    (hdiscr : Filter.Tendsto (fun i ↦ |NumberField.discr (L i)|) l Filter.atTop) :
    Filter.Tendsto (fun i ↦ NumberField.classNumber (L i)) l Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  rcases eq_or_ne B 0 with rfl | _
  · exact Eventually.of_forall fun _ ↦ Nat.zero_le _
  obtain ⟨C, hC⟩ := imaginary_discr_bounded_of_classNumber_le.{u} (B - 1)
  have hlarge : ∀ᶠ i in l, (⌊max C 0⌋₊ + 1 : ℤ) ≤ |discr (L i)| :=
    hdiscr.eventually (eventually_ge_atTop _)
  filter_upwards [hcomplex, hdeg, hlarge] with i hci hdegi hDi
  by_contra! hlt
  have hle : |(discr (L i) : ℝ)| ≤ C := @hC (L i) _ _ hci hdegi (by omega)
  have hgt : max C 0 < |(discr (L i) : ℝ)| := by
    rw [← Int.cast_abs]
    exact (Nat.lt_floor_add_one (max C 0)).trans_le (by exact_mod_cast hDi)
  linarith [le_max_left C 0]

/-- **Divergence of `h(D)` along negative fundamental discriminants `D → -∞`.** -/
theorem tendsto_classNumber_quadraticAlgebra_of_isFundamentalDiscr
    {ι : Type*} {l : Filter ι} (D : ι → ℤ) [∀ i, Fact (¬ IsSquare (D i))]
    (hfund : ∀ᶠ i in l, Int.IsFundamentalDiscr (D i))
    (hD : Filter.Tendsto D l Filter.atBot) :
    Filter.Tendsto
      (fun i ↦ NumberField.classNumber (QuadraticAlgebra ℚ (D i : ℚ) 0)) l Filter.atTop := by
  have hneg : ∀ᶠ i in l, D i < 0 := hD.eventually (eventually_lt_atBot 0)
  refine tendsto_classNumber_atTop (fun i ↦ QuadraticAlgebra ℚ (D i : ℚ) 0)
    (hneg.mono fun i hi ↦ QuadraticAlgebra.isTotallyComplex_iff.mpr (by exact_mod_cast hi))
    (Eventually.of_forall fun _ ↦ QuadraticAlgebra.finrank_eq_two _ _) ?_
  refine (tendsto_neg_atBot_atTop.comp hD).congr' ?_
  filter_upwards [hfund, hneg] with i hfi hni
  simp [QuadraticAlgebra.discr_eq_of_isFundamentalDiscr hfi, abs_of_neg hni]

/-- **Divergence of `h(ℚ(√d))` along negative squarefree radicands `d → -∞`.** -/
theorem tendsto_classNumber_quadraticAlgebra_of_squarefree
    {ι : Type*} {l : Filter ι} (d : ι → ℤ) [∀ i, Fact (¬ IsSquare (d i))]
    (hsf : ∀ᶠ i in l, Squarefree (d i))
    (hd : Filter.Tendsto d l Filter.atBot) :
    Filter.Tendsto
      (fun i ↦ NumberField.classNumber (QuadraticAlgebra ℚ (d i : ℚ) 0)) l Filter.atTop := by
  have hneg : ∀ᶠ i in l, d i < 0 := hd.eventually (eventually_lt_atBot 0)
  refine tendsto_classNumber_atTop (fun i ↦ QuadraticAlgebra ℚ (d i : ℚ) 0)
    (hneg.mono fun i hi ↦ QuadraticAlgebra.isTotallyComplex_iff.mpr (by exact_mod_cast hi))
    (Eventually.of_forall fun _ ↦ QuadraticAlgebra.finrank_eq_two _ _) ?_
  refine tendsto_atTop_mono' l ?_ (tendsto_neg_atBot_atTop.comp hd)
  filter_upwards [hsf, hneg] with i hsfi hni
  simpa [abs_of_neg hni] using abs_le_abs_discr_quadraticAlgebra hsfi

end TauCeti.NumberField
