/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.SelbergSieve

import Mathlib.Tactic.FieldSimp

/-!
# Euler-product sieve dimension and truncated remainder mass

Combinatorial and upper-bound sieves parameterize the prime-density product over prime intervals
`[w, z)` with `2 ≤ w ≤ z` by a sieve dimension `κ` and constant `K` via Euler-product ratios
(`TauCeti.HasProductSieveDimension` and `BoundingSieve.HasProductDimension`), and collect
approximation errors below a strict real cutoff `D` into `BoundingSieve.remainderMass`.

## Main definitions and results

* `TauCeti.HasProductSieveDimension` and `BoundingSieve.HasProductDimension`: Euler-product ratio
  dimension bound `∏ (1 - g(p))⁻¹ ≤ K (log z / log w) ^ κ` on `[w, z)` for `2 ≤ w ≤ z`, together
  with their equivalence on `BoundingSieve`, automatic bounds `1 ≤ K` and `0 ≤ κ`, monotonicity in
  parameters and density, and finite-prime witnesses.
* `BoundingSieve.remainderMass`: strict-cutoff absolute remainder sum `∑_{d ∣ P, d < D} |s.rem d|`,
  with monotonicity, vanishing for `D ≤ 1`, congruence, and
  `BoundingSieve.errSum_le_mul_remainderMass`.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, Chapter 12: "Brun's combinatorial sieve",
  Sections 12.2–12.3.
-/

public noncomputable section

open Finset Nat Real

namespace TauCeti

/-- Euler-product sieve dimension: for every `2 ≤ w ≤ z`, the product of `(1 - g p)⁻¹` over primes
`p ∈ P` with `w ≤ p < z` is at most `K * (log z / log w) ^ κ`. -/
def HasProductSieveDimension (P : Set ℕ) (g : ℕ → ℝ) (κ K : ℝ) : Prop :=
  open Classical in
  ∀ w z : ℝ, 2 ≤ w → w ≤ z →
    (∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p ↦ p ∈ P ∧ p.Prime ∧ w ≤ (p : ℝ)),
      (1 - g p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ

/-- Explicit unfolding of `HasProductSieveDimension`. -/
theorem hasProductSieveDimension_iff {P : Set ℕ} {g : ℕ → ℝ} {κ K : ℝ} :
    HasProductSieveDimension P g κ K ↔
      ∀ w z : ℝ, 2 ≤ w → w ≤ z →
        (open Classical in
          ∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p ↦ p ∈ P ∧ p.Prime ∧ w ≤ (p : ℝ)),
            (1 - g p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ :=
  Iff.rfl

/-- Apply an Euler-product sieve dimension bound on `[w, z)` with `2 ≤ w ≤ z`. -/
theorem HasProductSieveDimension.bound {P : Set ℕ} {g : ℕ → ℝ} {κ K : ℝ}
    (h : HasProductSieveDimension P g κ K) {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z) :
    (open Classical in
      ∏ p ∈ (Finset.range ⌈z⌉₊).filter (fun p ↦ p ∈ P ∧ p.Prime ∧ w ≤ (p : ℝ)),
        (1 - g p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ :=
  h w z hw hwz

/-- Any `HasProductSieveDimension` witness satisfies `1 ≤ K`. -/
theorem HasProductSieveDimension.one_le {P : Set ℕ} {g : ℕ → ℝ} {κ K : ℝ}
    (h : HasProductSieveDimension P g κ K) : 1 ≤ K := by
  classical
  have h2 := h.bound (le_rfl : (2 : ℝ) ≤ 2) le_rfl
  have hemp : (Finset.range ⌈(2 : ℝ)⌉₊).filter (fun p ↦ p ∈ P ∧ p.Prime ∧ (2 : ℝ) ≤ p) = ∅ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_ceil, Finset.notMem_empty, iff_false]
    rintro ⟨hp2, -, -, h2p⟩
    linarith
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [hemp, Finset.prod_empty, div_self hlog, Real.one_rpow, mul_one] at h2
  exact h2

/-- When `0 ≤ g p < 1` on primes in `P`, `HasProductSieveDimension P g κ K` forces `0 ≤ κ`. -/
theorem HasProductSieveDimension.nonneg_dim {P : Set ℕ} {g : ℕ → ℝ} {κ K : ℝ}
    (h : HasProductSieveDimension P g κ K)
    (hg : ∀ p ∈ P, p.Prime → 0 ≤ g p ∧ g p < 1) : 0 ≤ κ := by
  classical
  by_contra hκ_not
  have hκ : κ < 0 := lt_of_not_ge hκ_not
  have hK : 1 ≤ K := h.one_le
  set t : ℝ := (2 * K) ^ (-κ⁻¹)
  have ht1 : 1 < t := Real.one_lt_rpow (by linarith) (neg_pos.mpr (inv_lt_zero.mpr hκ))
  set z : ℝ := (2 : ℝ) ^ t
  have h2z : (2 : ℝ) ≤ z := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2 : ℝ) ^ t := (Real.rpow_lt_rpow_of_exponent_lt one_lt_two ht1).le
  set S := (Finset.range ⌈z⌉₊).filter (fun p ↦ p ∈ P ∧ p.Prime ∧ (2 : ℝ) ≤ p)
  have hprod_ge : 1 ≤ ∏ p ∈ S, (1 - g p)⁻¹ := by
    calc (1 : ℝ) = ∏ _p ∈ S, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ ∏ p ∈ S, (1 - g p)⁻¹ := Finset.prod_le_prod₀ (fun _ _ ↦ zero_le_one) fun p hp ↦ by
        obtain ⟨_, hpP, hpp, _⟩ := Finset.mem_filter.mp hp
        obtain ⟨hgp0, hgp1⟩ := hg p hpP hpp
        exact (one_le_inv₀ (by linarith)).mpr (by linarith)
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hratio : Real.log z / Real.log 2 = t := by
    rw [Real.log_rpow zero_lt_two, mul_div_cancel_right₀ _ hlog2]
  have hbound := h.bound le_rfl h2z
  have hrhs : K * (Real.log z / Real.log 2) ^ κ = (1 : ℝ) / 2 := by
    rw [hratio, ← Real.rpow_mul (by positivity : 0 ≤ 2 * K), neg_mul, inv_mul_cancel₀ hκ.ne,
      Real.rpow_neg_one]
    field_simp [(by positivity : (2 * K) ≠ 0)]
  linarith [hprod_ge.trans hbound]

/-- Increasing `K` preserves `HasProductSieveDimension`. -/
theorem HasProductSieveDimension.mono_const {P : Set ℕ} {g : ℕ → ℝ} {κ K K' : ℝ}
    (h : HasProductSieveDimension P g κ K) (hK : K ≤ K') :
    HasProductSieveDimension P g κ K' := fun w z hw hwz ↦ by
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hpow : 0 ≤ (Real.log z / Real.log w) ^ κ :=
    Real.rpow_nonneg (div_pos hlogz hlogw).le κ
  exact (h w z hw hwz).trans (mul_le_mul_of_nonneg_right hK hpow)

/-- Increasing `κ` preserves `HasProductSieveDimension`. -/
theorem HasProductSieveDimension.mono_dim {P : Set ℕ} {g : ℕ → ℝ} {κ κ' K : ℝ}
    (h : HasProductSieveDimension P g κ K) (hκ : κ ≤ κ') :
    HasProductSieveDimension P g κ' K := fun w z hw hwz ↦ by
  have hK : 0 ≤ K := zero_le_one.trans h.one_le
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hratio : 1 ≤ Real.log z / Real.log w :=
    (one_le_div hlogw).mpr (Real.log_le_log (by linarith) hwz)
  exact (h w z hw hwz).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hratio hκ) hK)

/-- Pointwise smaller densities `h p ≤ g p` on primes in `P` satisfy the same
`HasProductSieveDimension` bound whenever `g p < 1` on primes in `P`. -/
theorem HasProductSieveDimension.mono_density {P : Set ℕ} {g h : ℕ → ℝ} {κ K : ℝ}
    (hg : HasProductSieveDimension P g κ K)
    (hle : ∀ p ∈ P, p.Prime → h p ≤ g p ∧ g p < 1) :
    HasProductSieveDimension P h κ K := by
  classical
  intro w z hw hwz
  set S := (Finset.range ⌈z⌉₊).filter (fun p ↦ p ∈ P ∧ p.Prime ∧ w ≤ (p : ℝ))
  refine (Finset.prod_le_prod₀ (s := S) (fun p hp ↦ ?_) fun p hp ↦ ?_).trans (hg.bound hw hwz)
  · obtain ⟨_, hpP, hpp, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨hhg, hg1⟩ := hle p hpP hpp
    exact inv_nonneg.mpr (by linarith)
  · obtain ⟨_, hpP, hpp, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨hhg, hg1⟩ := hle p hpP hpp
    exact inv_anti₀ (by linarith) (by linarith)

/-- Zero density satisfies `HasProductSieveDimension P 0 κ K` whenever `0 ≤ κ` and `1 ≤ K`. -/
theorem HasProductSieveDimension.zero (P : Set ℕ) {κ K : ℝ} (hκ : 0 ≤ κ) (hK : 1 ≤ K) :
    HasProductSieveDimension P (fun _ ↦ 0) κ K := by
  classical
  intro w z hw hwz
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hratio : 1 ≤ Real.log z / Real.log w :=
    (one_le_div hlogw).mpr (Real.log_le_log (by linarith) hwz)
  have hpow : 1 ≤ (Real.log z / Real.log w) ^ κ := Real.one_le_rpow hratio hκ
  simp only [sub_zero, inv_one, Finset.prod_const_one]
  exact one_mul (1 : ℝ) ▸ mul_le_mul hK hpow zero_le_one (zero_le_one.trans hK)

/-- Any finite set `S : Finset ℕ` with `0 ≤ g p < 1` on primes in `S` satisfies
`HasProductSieveDimension (S : Set ℕ) g κ (∏ p ∈ S.filter Nat.Prime, (1 - g p)⁻¹)` for `0 ≤ κ`. -/
theorem HasProductSieveDimension.of_finset (S : Finset ℕ) {g : ℕ → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hg : ∀ p ∈ S, p.Prime → 0 ≤ g p ∧ g p < 1) :
    HasProductSieveDimension (S : Set ℕ) g κ (∏ p ∈ S.filter Nat.Prime, (1 - g p)⁻¹) := by
  rw [hasProductSieveDimension_iff]
  intro w z hw hwz
  have h1 : ∀ p ∈ S.filter Nat.Prime, 1 ≤ (1 - g p)⁻¹ := fun p hp ↦ by
    obtain ⟨hpS, hpp⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hlt⟩ := hg p hpS hpp
    exact (one_le_inv₀ (by linarith)).mpr (by linarith)
  have hK_nn : 0 ≤ ∏ p ∈ S.filter Nat.Prime, (1 - g p)⁻¹ :=
    Finset.prod_nonneg fun p hp ↦ zero_le_one.trans (h1 p hp)
  have hratio : 1 ≤ Real.log z / Real.log w :=
    (one_le_div (Real.log_pos (by linarith))).mpr (Real.log_le_log (by linarith) hwz)
  refine (Finset.prod_le_prod_of_subset_of_one_le₀ (t := S.filter Nat.Prime) ?_ ?_
      fun p hp _ ↦ h1 p hp).trans
    (le_mul_of_one_le_right hK_nn (Real.one_le_rpow hratio hκ))
  · intro p hp
    simp only [Finset.mem_filter] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hp.2.1, hp.2.2.1⟩
  · intro p hp
    simp only [Finset.mem_filter] at hp
    exact zero_le_one.trans (h1 p (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hp.2.1, hp.2.2.1⟩))

end TauCeti

namespace BoundingSieve

/-- The Euler-product dimension bound on the prime factors of `s.prodPrimes` with density `s.nu`. -/
def HasProductDimension (s : BoundingSieve) (κ K : ℝ) : Prop :=
  ∀ w z : ℝ, 2 ≤ w → w ≤ z →
    (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
      (1 - s.nu p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ

/-- Explicit unfolding of `BoundingSieve.HasProductDimension`. -/
theorem hasProductDimension_iff (s : BoundingSieve) (κ K : ℝ) :
    s.HasProductDimension κ K ↔
      ∀ w z : ℝ, 2 ≤ w → w ≤ z →
        (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
          (1 - s.nu p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ :=
  Iff.rfl

/-- Apply `BoundingSieve.HasProductDimension` on `[w, z)` with `2 ≤ w ≤ z`. -/
theorem HasProductDimension.bound {s : BoundingSieve} {κ K : ℝ}
    (h : s.HasProductDimension κ K) {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z) :
    (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
      (1 - s.nu p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ :=
  h w z hw hwz

/-- `s.HasProductDimension κ K` agrees with `TauCeti.HasProductSieveDimension` on
`(s.prodPrimes.primeFactors : Set ℕ)` and `s.nu`. -/
theorem hasProductDimension_iff_hasProductSieveDimension (s : BoundingSieve) (κ K : ℝ) :
    s.HasProductDimension κ K ↔
      TauCeti.HasProductSieveDimension (s.prodPrimes.primeFactors : Set ℕ) s.nu κ K := by
  rw [hasProductDimension_iff, TauCeti.hasProductSieveDimension_iff]
  refine forall₄_congr fun w z _ _ ↦ ?_
  refine (congrArg (· ≤ K * (Real.log z / Real.log w) ^ κ)
    (Finset.prod_congr ?_ fun _ _ ↦ rfl)).to_iff
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_ceil, Finset.mem_coe]
  exact ⟨fun ⟨hpP, hwp, hpz⟩ ↦ ⟨hpz, hpP, Nat.prime_of_mem_primeFactors hpP, hwp⟩,
    fun ⟨hpz, hpP, _, hwp⟩ ↦ ⟨hpP, hwp, hpz⟩⟩

/-- Every `BoundingSieve` satisfies `s.HasProductDimension κ (∏ p ∈ P.primeFactors, (1 - s.nu p)⁻¹)`
for every `0 ≤ κ`. -/
theorem hasProductDimension_prod_inv (s : BoundingSieve) {κ : ℝ} (hκ : 0 ≤ κ) :
    s.HasProductDimension κ (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)⁻¹) := by
  have hflt : s.prodPrimes.primeFactors.filter Nat.Prime = s.prodPrimes.primeFactors :=
    Finset.filter_eq_self.mpr fun _ hp ↦ Nat.prime_of_mem_primeFactors hp
  rw [s.hasProductDimension_iff_hasProductSieveDimension]
  simpa only [hflt] using
    TauCeti.HasProductSieveDimension.of_finset (g := s.nu) s.prodPrimes.primeFactors hκ
      fun p hp hpp ↦
        have hdvd : p ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors hp
        ⟨(s.nu_pos_of_prime p hpp hdvd).le, s.nu_lt_one_of_prime p hpp hdvd⟩

/-- Any `BoundingSieve.HasProductDimension` witness satisfies `1 ≤ K`. -/
theorem HasProductDimension.one_le {s : BoundingSieve} {κ K : ℝ}
    (h : s.HasProductDimension κ K) : 1 ≤ K :=
  ((s.hasProductDimension_iff_hasProductSieveDimension κ K).mp h).one_le

/-- Any `BoundingSieve.HasProductDimension` witness satisfies `0 ≤ κ`. -/
theorem HasProductDimension.nonneg_dim {s : BoundingSieve} {κ K : ℝ}
    (h : s.HasProductDimension κ K) : 0 ≤ κ := by
  refine ((s.hasProductDimension_iff_hasProductSieveDimension κ K).mp h).nonneg_dim ?_
  intro p hpP hpp
  have hdvd : p ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors (Finset.mem_coe.mp hpP)
  exact ⟨(s.nu_pos_of_prime p hpp hdvd).le, s.nu_lt_one_of_prime p hpp hdvd⟩

/-- Increasing `K` preserves `BoundingSieve.HasProductDimension`. -/
theorem HasProductDimension.mono_const {s : BoundingSieve} {κ K K' : ℝ}
    (h : s.HasProductDimension κ K) (hK : K ≤ K') : s.HasProductDimension κ K' :=
  (s.hasProductDimension_iff_hasProductSieveDimension κ K').mpr
    (((s.hasProductDimension_iff_hasProductSieveDimension κ K).mp h).mono_const hK)

/-- Increasing `κ` preserves `BoundingSieve.HasProductDimension`. -/
theorem HasProductDimension.mono_dim {s : BoundingSieve} {κ κ' K : ℝ}
    (h : s.HasProductDimension κ K) (hκ : κ ≤ κ') : s.HasProductDimension κ' K :=
  (s.hasProductDimension_iff_hasProductSieveDimension κ' K).mpr
    (((s.hasProductDimension_iff_hasProductSieveDimension κ K).mp h).mono_dim hκ)

/-- Absolute native remainders on positive divisors of `s.prodPrimes` strictly below `D`,
including `d = 1` when `1 < D`. -/
def remainderMass (s : BoundingSieve) (D : ℝ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) < D), |s.rem d|

/-- Explicit unfolding of `BoundingSieve.remainderMass`. -/
theorem remainderMass_def (s : BoundingSieve) (D : ℝ) :
    s.remainderMass D =
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) < D), |s.rem d| := (rfl)

/-- Every truncated remainder mass is nonnegative. -/
theorem remainderMass_nonneg (s : BoundingSieve) (D : ℝ) : 0 ≤ s.remainderMass D :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Truncated remainder mass is monotone in the cutoff `D`. -/
@[gcongr]
theorem remainderMass_mono (s : BoundingSieve) {D E : ℝ} (hDE : D ≤ E) :
    s.remainderMass D ≤ s.remainderMass E := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ abs_nonneg _
  intro d hd
  obtain ⟨hdP, hdD⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨hdP, hdD.trans_le hDE⟩

/-- For `D ≤ 1`, no positive divisor satisfies `d < D`, so `s.remainderMass D = 0`. -/
theorem remainderMass_eq_zero_of_le_one (s : BoundingSieve) {D : ℝ} (hD : D ≤ 1) :
    s.remainderMass D = 0 := by
  rw [remainderMass_def]
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  obtain ⟨hdP, hdD⟩ := Finset.mem_filter.mp hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hdP
  linarith

/-- Two sieves with the same `prodPrimes` and equal absolute remainders on its divisors have equal
truncated remainder masses at every cutoff. -/
theorem remainderMass_congr {s₁ s₂ : BoundingSieve} {D : ℝ}
    (hP : s₁.prodPrimes = s₂.prodPrimes)
    (hrem : ∀ d ∈ s₁.prodPrimes.divisors, |s₁.rem d| = |s₂.rem d|) :
    s₁.remainderMass D = s₂.remainderMass D := by
  simp only [remainderMass_def]
  rw [← hP]
  exact Finset.sum_congr rfl fun d hd ↦ hrem d (Finset.mem_filter.mp hd).1

/-- Coefficients vanishing on divisors `d ≥ D` and bounded in modulus by `L` on divisors `d < D`
satisfy `s.errSum c ≤ L * s.remainderMass D`. Nonnegativity of `L` is not assumed: it follows from
`|c 1| ≤ L` when `1 < D` and is vacuous when `D ≤ 1`. -/
theorem errSum_le_mul_remainderMass (s : BoundingSieve) (c : ℕ → ℝ) (D : ℝ) {L : ℝ}
    (hsupp : ∀ d ∈ s.prodPrimes.divisors, D ≤ (d : ℝ) → c d = 0)
    (hbound : ∀ d ∈ s.prodPrimes.divisors, (d : ℝ) < D → |c d| ≤ L) :
    s.errSum c ≤ L * s.remainderMass D := by
  classical
  rw [errSum, remainderMass_def, Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not s.prodPrimes.divisors (fun d : ℕ ↦ (d : ℝ) < D)]
  have hzero : ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ ↦ ¬(d : ℝ) < D),
      |c d| * |s.rem d| = 0 := by
    refine Finset.sum_eq_zero fun d hd ↦ ?_
    obtain ⟨hdP, hdD⟩ := Finset.mem_filter.mp hd
    rw [hsupp d hdP (le_of_not_gt hdD), abs_zero, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_le_sum fun d hd ↦ ?_
  obtain ⟨hdP, hdD⟩ := Finset.mem_filter.mp hd
  exact mul_le_mul_of_nonneg_right (hbound d hdP hdD) (abs_nonneg _)

end BoundingSieve
