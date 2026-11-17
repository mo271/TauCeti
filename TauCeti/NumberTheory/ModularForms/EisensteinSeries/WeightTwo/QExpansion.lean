/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Character
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The `q`-expansion of weight-two Eisenstein series

For Dirichlet characters `ψ` modulo `u` and `φ` modulo `v`, not both trivial, with
`ψ(-1) φ(-1) = 1` and `u v ∣ N`, we compute the `q`-expansion of the weight-two Eisenstein series
with character `G₂^{ψ,φ}` (`TauCeti.EisensteinSeries.charG2MF`). As in weight `k ≥ 3`
(`TauCeti.EisensteinSeries.qExpansion_charEisensteinSeriesMF_coeff`), its constant coefficient is
`ψ(0) ∑_{d ∈ ℤ} φ⁻¹(d) d⁻²`, and for `n ≥ 1` its `n`-th coefficient is
`-8 π² / v² ∑_{c m = n} ψ(c) φ̂(m) m`, where `φ̂(m) = ∑_{r mod v} φ⁻¹(r) e^(2πi r m / v)`.
For primitive `φ` this is `-8 π² g(φ⁻¹) / v²` times the twisted divisor sum
`σ₁^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n/d) φ(d) d`.

The double series `∑_{(c, d)} ψ(c) φ⁻¹(d) (c v z + d)⁻²` does not converge absolutely, and the
order of summation matters. The series `G₂^{ψ,φ}` is the sum over the translates of a box of
residues modulo `N` (`TauCeti.EisensteinSeries.hasSum_charG2MF`); we show that it is also the sum
over `c` of the absolutely convergent rows `ψ(c) ∑_d φ⁻¹(d) (c v z + d)⁻²`
(`TauCeti.EisensteinSeries.hasSum_charRow_charG2MF`). These are the rows of the weighted series
of `charWeight`, which has total mass zero, so this is the row expansion of weighted weight-two
series (`TauCeti.EisensteinSeries.hasSum_weightedG2Row`). The coefficients
then follow from the row-by-row computation shared with weight `k ≥ 3`
(`TauCeti.EisensteinSeries.qExpansion_coeff_of_apply_eq_tsum_charRow`).

For an arbitrary weight `W : (Fin 2 → ZMod N) → ℂ`, the weighted weight-two modular form
`weightedG2MF W` of level `Γ(N)` satisfies
`∑_c weightedG2Row W z c = weightedG2 W z + N⁻² (∑_a W(a)) G₂(z)`
(`TauCeti.EisensteinSeries.tsum_weightedG2Row`). Subtracting the `q`-expansion of `G₂`
(`EisensteinSeries.hasSum_qExpansion_E2`) from the row-sum `q`-expansion
(`TauCeti.EisensteinSeries.hasSum_weightedEisenstein_qParam`) yields the `q`-expansion of
`weightedG2MF W` in `q_N = e^(2πi z / N)`
(`TauCeti.EisensteinSeries.qExpansion_weightedG2MF_coeff`). Specializing to a single nonzero
residue `W = Pi.single a 1` and dividing by `(2πi)²` expresses every coefficient explicitly as a
rational combination of `N`-th roots of unity `ZMod.stdAddChar`
(`TauCeti.EisensteinSeries.qExpansion_weightedG2MF_single_div_coeff`).

## Main results

* `TauCeti.EisensteinSeries.hasSum_charRow_charG2MF`: `G₂^{ψ,φ}` summed along rows.
* `TauCeti.EisensteinSeries.qExpansion_charG2MF_coeff`: the coefficients of `G₂^{ψ,φ}`.
* `TauCeti.EisensteinSeries.qExpansion_charG2MF_coeff_of_isPrimitive`: for primitive `φ`, the
  nonconstant coefficients are `-8 π² g(φ⁻¹) / v²` times the twisted divisor sums.
* `TauCeti.EisensteinSeries.qExpansion_weightedG2MF_coeff`: the coefficients of `weightedG2MF W`
  in `e^(2πi z / N)`.
* `TauCeti.EisensteinSeries.qExpansion_weightedG2MF_single_div_coeff`: the coefficients of
  `(2πi)⁻² weightedG2MF (Pi.single a 1)` for `a ≠ 0`, explicitly in terms of `ZMod.stdAddChar`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.6.
* [T. Miyake, *Modular forms*][miyake1989], §7.1, §7.2.
* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §6.1.
-/

public section

noncomputable section

open Complex ZMod EisensteinSeries ModularForm
open UpperHalfPlane hiding I
open scoped Real ArithmeticFunction.sigma

namespace TauCeti.EisensteinSeries

section Character

variable {u v N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- **The weight-two Eisenstein series with character summed along rows**: unless `ψ` and `φ` are
both trivial, `G₂^{ψ,φ}(z)` is the sum over `c ∈ ℤ` of the absolutely convergent rows
`ψ(c) ∑_{d ∈ ℤ} φ⁻¹(d) (c v z + d)⁻²`. The double series itself does not converge absolutely. -/
theorem hasSum_charRow_charG2MF (huv : u * v ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1) (z : ℍ) :
    HasSum (charRow ψ φ 2 z) (charG2MF ψ φ huv z) := by
  have : NeZero v := NeZero.of_dvd (dvd_of_mul_left_dvd huv)
  rw [hasSum_charRow_iff, coe_charG2MF]
  refine (hasSum_weightedG2Row (sum_charWeight_eq_zero ψ φ huv h) z).congr_fun fun c ↦ ?_
  simp [weightedG2Row_def, charWeight_intCast ψ φ huv]

/-- **The `q`-expansion of the weight-two Eisenstein series with character.** For characters `ψ`
modulo `u` and `φ` modulo `v`, not both trivial, with `ψ(-1) φ(-1) = 1`, the constant coefficient
of `G₂^{ψ,φ}` is `ψ(0) ∑_{d ∈ ℤ} φ⁻¹(d) d⁻²`, and for `n ≥ 1` its `n`-th coefficient is
`-8 π² / v² ∑_{c m = n} ψ(c) φ̂(m) m`, where `φ̂(m) = ∑_{r mod v} φ⁻¹(r) e^(2πi r m / v)` is the
discrete Fourier transform of `φ⁻¹` at `-m`. (If `ψ(-1) φ(-1) ≠ 1`, the series is zero:
`charG2MF_eq_zero`.) -/
theorem qExpansion_charG2MF_coeff [NeZero v] (huv : u * v ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1)
    (hpar : ψ (-1) * φ (-1) = 1) (n : ℕ) :
    (qExpansion 1 (charG2MF ψ φ huv)).coeff n =
      if n = 0 then ψ 0 * ∑' d : ℤ, φ⁻¹ d * (d : ℂ) ^ (-2 : ℤ)
      else -8 * π ^ 2 / v ^ 2 *
        ∑ x ∈ n.divisorsAntidiagonal, ψ x.1 * 𝓕 ⇑(φ⁻¹) (-(x.2 : ZMod v)) * x.2 := by
  rw [qExpansion_coeff_of_apply_eq_tsum_charRow ψ φ (k := 2) le_rfl (by simpa using hpar)
    fun z ↦ (hasSum_charRow_charG2MF ψ φ huv h z).tsum_eq.symm]
  split_ifs
  · simp only [Nat.cast_ofNat]
  · simp only [Nat.add_one_sub_one, pow_one, Nat.factorial_one, Nat.cast_one, one_mul]
    congr 1
    rw [mul_pow, mul_pow, neg_sq, I_sq]
    ring

/-- **The `q`-expansion of the weight-two Eisenstein series with character, for primitive `φ`.**
Then the Fourier transform of `φ⁻¹` is a multiple of `φ` by the Gauss sum `g(φ⁻¹)`, and for
`n ≥ 1` the `n`-th coefficient of `G₂^{ψ,φ}` is `-8 π² g(φ⁻¹) / v² · σ₁^{ψ,φ}(n)`, where
`σ₁^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n/d) φ(d) d` is the twisted divisor sum. -/
theorem qExpansion_charG2MF_coeff_of_isPrimitive [NeZero v] (huv : u * v ∣ N)
    (h : ψ ≠ 1 ∨ φ ≠ 1) (hpar : ψ (-1) * φ (-1) = 1) (hφ : φ.IsPrimitive) {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 (charG2MF ψ φ huv)).coeff n =
      -8 * π ^ 2 / v ^ 2 * gaussSum φ⁻¹ stdAddChar *
        DirichletCharacter.twistedDivisorSum 1 ψ φ n := by
  rw [qExpansion_coeff_of_apply_eq_tsum_charRow_of_isPrimitive ψ φ (k := 2) le_rfl
    (by simpa using hpar) hφ (fun z ↦ (hasSum_charRow_charG2MF ψ φ huv h z).tsum_eq.symm) hn]
  simp only [Nat.add_one_sub_one, Nat.factorial_one, Nat.cast_one, one_mul]
  congr 2
  rw [mul_pow, mul_pow, neg_sq, I_sq]
  ring

end Character

section Weighted

variable {N : ℕ} [NeZero N]

/-- The `q`-expansion of Mathlib's `EisensteinSeries.G2` rewritten in the level-`N` parameter
`q_N = e^(2πi z / N)`. -/
private lemma hasSum_G2_qParam (z : ℍ) :
    HasSum
      (fun n : ℕ ↦
        (if N ∣ n then
          if n = 0 then 2 * riemannZeta 2 else -8 * π ^ 2 * σ 1 (n / N)
        else 0) • Function.Periodic.qParam N z ^ n)
      (G2 z) := by
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hG2 : 2 * riemannZeta 2 * E2 z = G2 z := by
    simp only [E2, riemannZeta_two, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hE := (hasSum_qExpansion_E2 (z := z)).mul_left (2 * riemannZeta 2)
  rw [hG2] at hE
  refine ((mul_right_injective₀ (NeZero.ne N)).hasSum_iff fun n hn ↦ ?_).mp ?_
  · have hnd : ¬ N ∣ n := fun ⟨m, hm⟩ ↦ hn ⟨m, hm.symm⟩
    simp [hnd]
  · refine hE.congr_fun fun m ↦ ?_
    have hq : Function.Periodic.qParam N z ^ (N * m) = cexp (2 * π * I * z) ^ m := by
      simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul, Complex.ofReal_natCast]
      congr 1
      push_cast
      field_simp
    rw [Function.comp_apply, hq, Nat.mul_div_cancel_left m (NeZero.pos N)]
    simp only [dvd_mul_right, ↓reduceIte]
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · have hNm : N * m ≠ 0 := mul_ne_zero (NeZero.ne N) hm
      simp only [hm, hNm, ↓reduceIte, smul_eq_mul, riemannZeta_two]
      ring

/-- **The `q`-expansion of a weighted weight-two Eisenstein series at period `N`.** For any weight
`W : (Fin 2 → ZMod N) → ℂ`, the constant coefficient of `weightedG2MF W` in `e^(2πi z / N)` is
`∑_{d ∈ ℤ} W(0, d) d⁻² - N⁻² (∑_a W(a)) · 2 ζ(2)`, and for `n ≥ 1` its `n`-th coefficient is
`-4π² / N²` times the folded divisor sum minus `(∑_a W(a)) · 2 σ₁(n / N)` when `N ∣ n`. -/
theorem qExpansion_weightedG2MF_coeff (W : (Fin 2 → ZMod N) → ℂ) (n : ℕ) :
    (qExpansion N (weightedG2MF W)).coeff n =
      if n = 0 then
        ∑' d : ℤ, W ![0, (d : ZMod N)] * (d : ℂ) ^ (-2 : ℤ) -
          ((N : ℂ) ^ 2)⁻¹ * (∑ a, W a) * (2 * riemannZeta 2)
      else
        -4 * π ^ 2 / N ^ 2 *
          (∑ x ∈ n.divisorsAntidiagonal,
            𝓕 (fun d ↦ W ![(x.1 : ZMod N), d] + W ![-(x.1 : ZMod N), -d])
              (-(x.2 : ZMod N)) * (x.2 : ℂ) -
            (∑ a, W a) * if N ∣ n then 2 * σ 1 (n / N) else 0) := by
  set b : ℕ → ℂ := fun n ↦
    if n = 0 then
      ∑' d : ℤ, W ![0, (d : ZMod N)] * (d : ℂ) ^ (-2 : ℤ) -
        ((N : ℂ) ^ 2)⁻¹ * (∑ a, W a) * (2 * riemannZeta 2)
    else
      -4 * π ^ 2 / N ^ 2 *
        (∑ x ∈ n.divisorsAntidiagonal,
          𝓕 (fun d ↦ W ![(x.1 : ZMod N), d] + W ![-(x.1 : ZMod N), -d])
            (-(x.2 : ZMod N)) * (x.2 : ℂ) -
          (∑ a, W a) * if N ∣ n then 2 * σ 1 (n / N) else 0)
  have hN : (N : ℝ) ∈ (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  suffices h : ∀ τ : ℍ,
      HasSum (fun m ↦ b m • Function.Periodic.qParam N τ ^ m) (weightedG2MF W τ) from
    (ModularFormClass.qExpansion_coeff_unique (Nat.cast_pos.mpr (NeZero.pos N)) hN h n).symm
  intro τ
  have hcomp (c d : ℤ) : ((↑) : ℤ → ZMod N) ∘ ![c, d] = ![(c : ZMod N), (d : ZMod N)] := by
    ext i; fin_cases i <;> rfl
  have hrow (c : ℤ) : Summable fun d : ℤ ↦
      W ![(c : ZMod N), (d : ZMod N)] * eisSummand (2 : ℕ) ![c, d] τ :=
    (summable_weightedG2Row_terms W τ c).congr fun d ↦ by simp [hcomp]
  have hrows : Summable fun c : ℤ ↦
      ∑' d : ℤ, W ![(c : ZMod N), (d : ZMod N)] * eisSummand (2 : ℕ) ![c, d] τ :=
    (summable_weightedG2Row W τ).congr fun c ↦ by
      rw [weightedG2Row_def]
      exact tsum_congr fun d ↦ by simp [hcomp]
  have h1 := hasSum_weightedEisenstein_qParam W (k := 2) le_rfl τ hrows hrow
  have h2 := (hasSum_G2_qParam (N := N) τ).mul_left (((N : ℂ) ^ 2)⁻¹ * ∑ a, W a)
  have hsum : (∑' c : ℤ, ∑' d : ℤ,
      W ![(c : ZMod N), (d : ZMod N)] * eisSummand (2 : ℕ) ![c, d] τ) -
      ((N : ℂ) ^ 2)⁻¹ * (∑ a, W a) * G2 τ = weightedG2MF W τ := by
    have hts : (∑' c : ℤ, ∑' d : ℤ,
        W ![(c : ZMod N), (d : ZMod N)] * eisSummand (2 : ℕ) ![c, d] τ) =
        ∑' c, weightedG2Row W τ c :=
      tsum_congr fun c ↦ by
        rw [weightedG2Row_def]
        exact tsum_congr fun d ↦ by simp [hcomp]
    rw [hts, tsum_weightedG2Row, coe_weightedG2MF]
    ring
  rw [← hsum]
  refine (h1.sub h2).congr_fun fun m ↦ ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp [b, mul_assoc]
  · simp only [b, hm, ↓reduceIte, Nat.add_one_sub_one, pow_one, Nat.factorial_one, Nat.cast_one,
      one_mul, even_two, Even.neg_pow, one_pow, smul_eq_mul]
    have hpi2 : (-2 * (π : ℂ) * I) ^ 2 = -4 * π ^ 2 := by
      rw [mul_pow, mul_pow, neg_sq, I_sq]; ring
    rw [hpi2]
    split_ifs <;> push_cast <;> ring

/-- For `a ≠ 0` and `a 0 = 0`, the point `(a 1).val / N` is not an integer. -/
private lemma val_div_mem_integerComplement {a : Fin 2 → ZMod N} (ha : a ≠ 0) (ha0 : a 0 = 0) :
    ((a 1).val : ℂ) / N ∈ Complex.integerComplement := by
  have ha1 : a 1 ≠ 0 := by
    intro h
    apply ha
    ext i
    fin_cases i
    · exact ha0
    · exact h
  have hpos : 0 < (a 1).val := Nat.pos_of_ne_zero (by simpa [ZMod.val_eq_zero] using ha1)
  have hlt : (a 1).val < N := ZMod.val_lt (a 1)
  rintro ⟨k, hk⟩
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hk' : ((a 1).val : ℤ) = k * N := by
    have : ((a 1).val : ℂ) = k * N := by
      rw [hk]
      field_simp
    exact_mod_cast this
  have hle : k ≤ 0 ∨ 1 ≤ k := by omega
  rcases hle with hk0 | hk1
  · have : k * (N : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk0 (Nat.cast_nonneg N)
    omega
  · have : (N : ℤ) ≤ k * N := le_mul_of_one_le_left (Nat.cast_nonneg N) hk1
    omega

/-- The discrete Fourier transform of the folded single-residue weight `Pi.single a 1`. -/
private lemma dft_folded_single (a : Fin 2 → ZMod N) (c m : ZMod N) :
    𝓕 (fun d ↦ Pi.single (M := fun _ ↦ ℂ) a 1 ![c, d] +
        Pi.single (M := fun _ ↦ ℂ) a 1 ![-c, -d]) (-m) =
      (if c = a 0 then (stdAddChar (a 1 * m) : ℂ) else 0) +
        if -c = a 0 then (stdAddChar (-(a 1 * m)) : ℂ) else 0 := by
  classical
  have ha_eq : ![a 0, a 1] = a := by ext i; fin_cases i <;> rfl
  rw [ZMod.dft_apply]
  simp only [mul_neg, neg_neg, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Fintype.sum_eq_single (a 1) (fun j hj ↦ by
      have hne : ![c, j] ≠ a := fun h ↦ hj (by simpa using congrFun h 1)
      simp [Pi.single_eq_of_ne hne])]
    by_cases hc : c = a 0
    · simp [hc, ha_eq]
    · have hne : ![c, a 1] ≠ a := fun h ↦ hc (by simpa using congrFun h 0)
      simp [hc, hne]
  · rw [Fintype.sum_eq_single (-a 1) (fun j hj ↦ by
      have hne : ![-c, -j] ≠ a := fun h ↦ hj (by
        have h1 : -j = a 1 := by simpa using congrFun h 1
        exact neg_eq_iff_eq_neg.mp h1)
      simp [Pi.single_eq_of_ne hne])]
    by_cases hc : -c = a 0
    · simp [hc, ha_eq, neg_mul]
    · have hne : ![-c, a 1] ≠ a := fun h ↦ hc (by simpa using congrFun h 0)
      simp [hc, hne]

/-- **The normalized `q`-expansion of a single-residue weight-two Eisenstein series.** For
`a ≠ 0` modulo `N`, dividing the `q_N`-expansion of `weightedG2MF (Pi.single a 1)` by `(2πi)²`
produces coefficients expressed rationally in terms of the `N`-th roots of unity
`ZMod.stdAddChar`. In particular every coefficient lies in the `N`-th cyclotomic field `ℚ(ζ_N)`,
and applying the cyclotomic automorphism `ζ ↦ ζ^d` replaces `a` by `![a 0, a 1 * d]`. -/
theorem qExpansion_weightedG2MF_single_div_coeff {a : Fin 2 → ZMod N} (ha : a ≠ 0) (n : ℕ) :
    (qExpansion N (weightedG2MF (Pi.single a 1))).coeff n / (2 * π * I) ^ 2 =
      ((N : ℂ) ^ 2)⁻¹ *
        if n = 0 then
          1 / 12 + if a 0 = 0 then stdAddChar (a 1) / (1 - stdAddChar (a 1)) ^ 2 else 0
        else
          (∑ x ∈ n.divisorsAntidiagonal,
            ((if (x.1 : ZMod N) = a 0 then (stdAddChar (a 1 * (x.2 : ZMod N)) : ℂ) else 0) +
              if -(x.1 : ZMod N) = a 0 then
                (stdAddChar (-(a 1 * (x.2 : ZMod N))) : ℂ)
              else 0) * x.2) -
            if N ∣ n then 2 * σ 1 (n / N) else 0 := by
  classical
  have hpi_eq : (2 * (π : ℂ) * I) ^ 2 = -4 * π ^ 2 := by
    rw [mul_pow, mul_pow, I_sq]; ring
  rw [qExpansion_weightedG2MF_coeff]
  have hsum1 : ∑ b : Fin 2 → ZMod N, Pi.single (M := fun _ ↦ ℂ) a 1 b = 1 := by simp
  rw [hsum1, one_mul]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [↓reduceIte]
    have hcomp (d : ℤ) : ((↑) : ℤ → ZMod N) ∘ ![0, d] = ![0, (d : ZMod N)] := by
      ext i; fin_cases i <;> simp
    have h0 : ∑' d : ℤ, Pi.single (M := fun _ ↦ ℂ) a 1 ![0, (d : ZMod N)] * (d : ℂ) ^ (-2 : ℤ) =
        ((N : ℂ) ^ 2)⁻¹ * if a 0 = 0 then UpperHalfPlane.rowSum ((a 1).val / N) else 0 := by
      have hts := tsum_weight_mul_zpow_neg_two_eq_sum_rowSum (Pi.single (M := fun _ ↦ ℂ) a 1)
      rw [show (∑' d : ℤ, Pi.single (M := fun _ ↦ ℂ) a 1 ![0, (d : ZMod N)] * (d : ℂ) ^ (-2 : ℤ)) =
          ∑' d : ℤ, Pi.single (M := fun _ ↦ ℂ) a 1 (((↑) : ℤ → ZMod N) ∘ ![0, d]) *
            (d : ℂ) ^ (-2 : ℤ) from
        tsum_congr fun d ↦ by rw [hcomp], hts]
      congr 1
      rw [Fintype.sum_eq_single (a 1) (fun r hr ↦ by
        have hne : ![0, r] ≠ a := fun h ↦ hr (by simpa using congrFun h 1)
        simp [Pi.single_eq_of_ne hne])]
      by_cases ha0 : a 0 = 0
      · have heq : ![0, a 1] = a := by ext i; fin_cases i <;> simp [ha0]
        simp [ha0, heq]
      · have hne : ![0, a 1] ≠ a := fun h ↦ ha0 (by simpa using (congrFun h 0).symm)
        simp [ha0, Pi.single_eq_of_ne hne]
    rw [h0]
    have hzeta : 2 * riemannZeta 2 = -(1 / 12) * (2 * π * I) ^ 2 := by
      rw [riemannZeta_two, hpi_eq]; ring
    by_cases ha0 : a 0 = 0
    · have hexp : cexp (2 * π * I * (((a 1).val : ℂ) / N)) = stdAddChar (a 1) := by
        have := ZMod.stdAddChar_coe (N := N) ((a 1).val : ℤ)
        simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at this
        rw [this, mul_div_assoc]
      simp only [ha0, ↓reduceIte]
      rw [UpperHalfPlane.rowSum_eq_cexp (val_div_mem_integerComplement ha ha0), hexp, hzeta]
      field_simp
      ring
    · simp only [ha0, ↓reduceIte]
      rw [hzeta]
      field_simp
      ring
  · simp only [hn, ↓reduceIte]
    have hdft : ∀ x ∈ n.divisorsAntidiagonal,
        𝓕 (fun d ↦ Pi.single (M := fun _ ↦ ℂ) a 1 ![(x.1 : ZMod N), d] +
            Pi.single (M := fun _ ↦ ℂ) a 1 ![-(x.1 : ZMod N), -d]) (-(x.2 : ZMod N)) * (x.2 : ℂ) =
          ((if (x.1 : ZMod N) = a 0 then (stdAddChar (a 1 * (x.2 : ZMod N)) : ℂ) else 0) +
            if -(x.1 : ZMod N) = a 0 then
              (stdAddChar (-(a 1 * (x.2 : ZMod N))) : ℂ)
            else 0) * x.2 :=
      fun x _ ↦ by rw [dft_folded_single]
    rw [Finset.sum_congr rfl hdft, ← hpi_eq]
    field_simp

end Weighted

end TauCeti.EisensteinSeries
