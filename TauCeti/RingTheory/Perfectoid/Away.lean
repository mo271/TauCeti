/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Away
public import TauCeti.RingTheory.Perfectoid.Basic
public import TauCeti.RingTheory.Perfectoid.Integral

import TauCeti.RingTheory.Perfectoid.Untilt

/-!
# Perfectoid Tate rings from integral perfectoid rings

Let `p` be a prime, `A₀` a commutative ring, and `π ∈ A₀` a nonzerodivisor with `π ^ p ∣ p` such
that `A₀` is `π`-adically complete and relative Frobenius `A₀ ⧸ (π) → A₀ ⧸ (π ^ p)` is bijective
(equivalently, `A₀` is integral perfectoid and `π`-adically complete; Bhatt–Morrow–Scholze,
*Integral `p`-adic Hodge theory*, Lemma 3.10). Let `A = A₀[1/π]` carry a topology whose
neighbourhoods of zero have basis `πⁿ A₀`, such as `TauCeti.Huber.awayTopology π A`.

This file proves Bhatt–Morrow–Scholze, Lemma 3.21:
* After replacing `π` by a unit multiple admitting compatible `p`-power roots `w n ∈ A₀` with
  `w (n + 1) ^ p = w n`, the power-bounded elements of `A` are exactly the almost elements of `A₀`:
  `IsPowerBounded x ↔ ∀ n, algebraMap A₀ A (w n) * x ∈ range (algebraMap A₀ A)`.
* In particular `A₀ ⊆ A°` and `π · A° ⊆ A₀`, so `A°` is bounded (`IsUniform A`).
* `A` is a perfectoid Tate ring (`IsPerfectoidTateRing p A`), with pseudouniformiser `w 1`
  satisfying `w 1 ^ p ∣ p` in `A°`.

As in `TauCeti.RingTheory.Huber.LocalizationTopology.Away`, the topological results are stated for
any topology on `A` whose neighbourhoods of zero have basis `πⁿ A₀`, so they apply equally to
`TauCeti.Huber.awayTopology` and to carriers with their own topology instance such as the untilt
`TauCeti.Perfectoid.untilt`.

## Main results

* `TauCeti.Perfectoid.mem_range_algebraMap_of_pow_mem`: if `π` is a nonzerodivisor and
  `π ^ p ∣ a ^ p → π ∣ a` in `A₀`, then `x ^ (p ^ r) ∈ A₀` implies `x ∈ A₀` in `A₀[1/π]`.
* `TauCeti.Perfectoid.exists_compatible_roots_associated`: in a `π`-adically complete ring with
  `π ^ p ∣ p` and surjective relative Frobenius, a unit multiple of `π` admits compatible
  `p`-power roots.
* `TauCeti.Perfectoid.isPowerBounded_iff_forall_mul_mem_range_of_hasBasis`: characterisation of
  power-bounded elements of `A₀[1/π]` as almost elements of `A₀`.
* `TauCeti.Perfectoid.algebraMap_mul_mem_range_of_isPowerBounded_of_hasBasis`: `π · A° ⊆ A₀`.
* `TauCeti.Perfectoid.isUniform_of_hasBasis_of_compatible_roots`,
  `TauCeti.Perfectoid.isUniform_of_hasBasis`: `A₀[1/π]` is uniform.
* `TauCeti.Perfectoid.isPerfectoidTateRing_of_hasBasis`,
  `TauCeti.Perfectoid.isPerfectoidTateRing_of_isIntegralPerfectoid_of_hasBasis`: `A₀[1/π]` is a
  perfectoid Tate ring (Bhatt–Morrow–Scholze, Lemma 3.21).

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, §3.2, Lemmas 3.9, 3.10 and
  3.21.
* P. Scholze, *Perfectoid spaces*, Lemmas 5.6–5.7.
-/

public section

open Filter Topology TauCeti.Huber
open scoped nonZeroDivisors

namespace TauCeti.Perfectoid

section Algebra

variable {A₀ : Type*} [CommRing A₀] {π : A₀} {A : Type*} [CommRing A] [Algebra A₀ A]

/-- If `π` is a nonzerodivisor of `A₀` and `π ^ p ∣ a ^ p → π ∣ a`, then in `A = A₀[1/π]` every
element whose `p`-th power lies in the image of `A₀` already lies in the image of `A₀`. -/
theorem mem_range_algebraMap_of_pow_prime_mem [IsLocalization.Away π A] {p : ℕ}
    (hπ : π ∈ A₀⁰) (hinj : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a) {x : A}
    (hx : x ^ p ∈ (algebraMap A₀ A).range) : x ∈ (algebraMap A₀ A).range := by
  -- Induct on the denominator exponent `k` in `x * π ^ k = a`.
  have key : ∀ (k : ℕ) (a : A₀), x * algebraMap A₀ A π ^ k = algebraMap A₀ A a →
      x ∈ (algebraMap A₀ A).range := by
    intro k
    induction k with
    | zero =>
      intro a ha
      exact ⟨a, by simpa using ha.symm⟩
    | succ k ih =>
      intro a ha
      obtain ⟨b, hb⟩ := hx
      have hpow : algebraMap A₀ A (a ^ p) = algebraMap A₀ A (b * (π ^ (k + 1)) ^ p) := by
        rw [map_pow, ← ha, mul_pow, ← hb, map_mul, map_pow, map_pow]
      have ha_pow : a ^ p = b * (π ^ (k + 1)) ^ p :=
        IsLocalization.injective A (Submonoid.powers_le.mpr hπ) hpow
      have hdvd_pow : π ^ p ∣ a ^ p := by
        refine ⟨b * (π ^ k) ^ p, ?_⟩
        rw [ha_pow, pow_succ', mul_pow]
        ring
      obtain ⟨a', rfl⟩ := hinj a hdvd_pow
      refine ih a' ?_
      have hu : IsUnit (algebraMap A₀ A π) := IsLocalization.Away.algebraMap_isUnit π
      apply hu.mul_right_cancel
      rw [mul_assoc, ← pow_succ, ha, map_mul, mul_comm (algebraMap A₀ A π)]
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj π x
  exact key k a ha

/-- If `π` is a nonzerodivisor of `A₀` and `π ^ p ∣ a ^ p → π ∣ a`, then in `A = A₀[1/π]` every
element whose `p ^ r`-th power lies in the image of `A₀` already lies in the image of `A₀`. -/
theorem mem_range_algebraMap_of_pow_mem [IsLocalization.Away π A] {p : ℕ}
    (hπ : π ∈ A₀⁰) (hinj : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a) {x : A} {r : ℕ}
    (hx : x ^ p ^ r ∈ (algebraMap A₀ A).range) : x ∈ (algebraMap A₀ A).range := by
  induction r with
  | zero => simpa using hx
  | succ r ih =>
    apply ih
    refine mem_range_algebraMap_of_pow_prime_mem hπ hinj ?_
    rwa [← pow_mul, ← pow_succ]

/-- **Existence of compatible `p`-power roots up to a unit** in a `π`-adically complete ring with
`π ^ p ∣ p` and surjective relative Frobenius `A₀ ⧸ (π) → A₀ ⧸ (π ^ p)` (Bhatt–Morrow–Scholze,
*Integral `p`-adic Hodge theory*, Lemma 3.9). Unlike `PreTilt.exists_associated_untilt`, this
allows the zero ring as well. -/
theorem exists_compatible_roots_associated {p : ℕ} [hp : Fact p.Prime] {π : A₀}
    (hdvd : π ^ p ∣ (p : A₀)) [IsAdicComplete (Ideal.span {π}) A₀]
    (hs : ∀ a : A₀, ∃ b, π ^ p ∣ a - b ^ p) :
    ∃ w : ℕ → A₀, Associated π (w 0) ∧ ∀ n, w (n + 1) ^ p = w n := by
  rcases subsingleton_or_nontrivial A₀ with _ | _
  · exact ⟨fun _ ↦ 0, by rw [Subsingleton.elim π 0], fun _ ↦ zero_pow hp.out.ne_zero⟩
  have : IsAdicComplete (Ideal.span {(p : A₀)}) A₀ :=
    .span_singleton_of_dvd ((dvd_pow_self π hp.out.ne_zero).trans hdvd)
  have : Fact (¬IsUnit (p : A₀)) :=
    ⟨IsAdicComplete.not_isUnit_of_mem (Ideal.mem_span_singleton_self (p : A₀))⟩
  obtain ⟨ϖ, -, hassoc⟩ := PreTilt.exists_associated_untilt hdvd hs
  refine ⟨fun n ↦ PreTilt.untilt (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) ϖ),
    by simpa using hassoc, fun n ↦ PreTilt.untilt_iterate_frobeniusEquiv_symm_succ_pow ϖ n⟩

/-- In a compatible system of `p`-power roots, `w n ^ (p ^ n) = w 0`. -/
private theorem compatible_roots_pow {p : ℕ} {w : ℕ → A₀}
    (hw : ∀ n, w (n + 1) ^ p = w n) (n : ℕ) : w n ^ p ^ n = w 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, hw n, ih]

end Algebra

section HasBasis

variable {A₀ : Type*} [CommRing A₀] {π : A₀} {A : Type*} [CommRing A] [Algebra A₀ A]
  [TopologicalSpace A]
  (h : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd π A n : Set A))
include h

/-- **A set mapped into `A₀` by multiplication by `π` is bounded** in `A₀[1/π]`. -/
theorem isBounded_of_mul_subset_range_of_hasBasis {S : Set A}
    (hS : ∀ x ∈ S, algebraMap A₀ A π * x ∈ (algebraMap A₀ A).range) : IsBounded S :=
  isBounded_iff.mpr fun U hU ↦ by
    obtain ⟨m, -, hm⟩ := h.mem_iff.mp hU
    refine ⟨(awayNhd π A (m + 1) : Set A), h.mem_of_mem trivial, ?_⟩
    rintro _ ⟨v, hv, y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := mem_awayNhd.mp hv
    obtain ⟨b, hb⟩ := hS y hy
    refine hm (mem_awayNhd.mpr ⟨a * b, ?_⟩)
    calc algebraMap A₀ A (π ^ m * (a * b))
      _ = algebraMap A₀ A (π ^ m * a) * algebraMap A₀ A b := by rw [← mul_assoc, map_mul]
      _ = algebraMap A₀ A (π ^ m * a) * (algebraMap A₀ A π * y) := by rw [hb]
      _ = algebraMap A₀ A (π ^ (m + 1) * a) * y := by
        rw [← mul_assoc, ← map_mul, pow_succ, mul_right_comm]

/-- The image of `π` is topologically nilpotent in `A` for any topology with basis `πⁿ A₀`. -/
theorem isTopologicallyNilpotent_algebraMap_of_hasBasis :
    IsTopologicallyNilpotent (algebraMap A₀ A π) := by
  refine h.tendsto_right_iff.mpr fun n _ ↦ ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [← map_pow, ← Nat.add_sub_cancel' hm, pow_add]
  exact algebraMap_pow_mul_mem_awayNhd _ _

/-- Any multiple of `π` in `A₀` maps to a topologically nilpotent element of `A`. -/
theorem isTopologicallyNilpotent_algebraMap_of_dvd_of_hasBasis {b : A₀} (hb : π ∣ b) :
    IsTopologicallyNilpotent (algebraMap A₀ A b) := by
  obtain ⟨c, rfl⟩ := hb
  rw [map_mul, mul_comm]
  have hpb : IsPowerBounded (algebraMap A₀ A c) :=
    (isBounded_range_algebraMap_of_hasBasis h).isPowerBounded_of_mem ⟨c, rfl⟩
  exact hpb.isTopologicallyNilpotent_mul (isTopologicallyNilpotent_algebraMap_of_hasBasis h)

/-- If `π ∣ p` in `A₀`, then `p` is topologically nilpotent in `A`. -/
theorem isTopologicallyNilpotent_natCast_of_hasBasis {p : ℕ} (hπp : π ∣ (p : A₀)) :
    IsTopologicallyNilpotent (p : A) := by
  simpa only [map_natCast] using isTopologicallyNilpotent_algebraMap_of_dvd_of_hasBasis h hπp

/-- The image of `A₀` lies inside the power-bounded subring of `A₀[1/π]`. -/
theorem range_algebraMap_le_powerBoundedSubring_of_hasBasis [NonarchimedeanAddGroup A] :
    (algebraMap A₀ A).range ≤ powerBoundedSubring A := fun _ hx ↦
  mem_powerBoundedSubring.mpr ((isBounded_range_algebraMap_of_hasBasis h).isPowerBounded_of_mem hx)

variable [IsLocalization.Away π A]

/-- **Power-bounded elements of `A₀[1/π]` are the almost elements of `A₀`** (Bhatt–Morrow–Scholze,
*Integral `p`-adic Hodge theory*, proof of Lemma 3.21). Given a nonzerodivisor `π ∈ A₀` with
`π ^ p ∣ a ^ p → π ∣ a` and compatible `p`-power roots `w n` of a unit multiple of `π`, an element
`x ∈ A₀[1/π]` is power-bounded if and only if `w n * x ∈ A₀` for every `n`. -/
theorem isPowerBounded_iff_forall_mul_mem_range_of_hasBasis {p : ℕ} (hp : 1 < p)
    (hπ : π ∈ A₀⁰) (hinj : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a)
    {w : ℕ → A₀} (hw : ∀ n, w (n + 1) ^ p = w n) (hassoc : Associated π (w 0)) {x : A} :
    IsPowerBounded x ↔ ∀ n, algebraMap A₀ A (w n) * x ∈ (algebraMap A₀ A).range := by
  obtain ⟨u, hu⟩ := hassoc
  refine ⟨fun hx n ↦ ?_, fun hx ↦ ?_⟩
  · -- Some `π ^ m` carries every power of `x` into `A₀`; raise `w n * x` to the `p ^ (m + n)`-th
    -- power so the `w n` factor supplies `π ^ m`.
    have h0 : (Set.range (algebraMap A₀ A)) ∈ 𝓝 (0 : A) :=
      coe_awayNhd_zero (π := π) (A := A) ▸ h.mem_of_mem (i := 0) trivial
    obtain ⟨m, hm⟩ := (isPowerBounded_iff.mp hx).exists_pow_mul_subset
      (isPseudoUniformizer_algebraMap_of_hasBasis h).isTopologicallyNilpotent h0
    have hmp : m ≤ p ^ m := (Nat.lt_pow_self hp).le
    have hpow : (algebraMap A₀ A (w n) * x) ^ p ^ (m + n) ∈ (algebraMap A₀ A).range := by
      have hπpow : (algebraMap A₀ A π) ^ p ^ m =
          (algebraMap A₀ A π) ^ m * (algebraMap A₀ A π) ^ (p ^ m - m) := by
        rw [← pow_add, Nat.add_sub_cancel' hmp]
      have hfactor : (algebraMap A₀ A (w n) * x) ^ p ^ (m + n) =
          algebraMap A₀ A (π ^ (p ^ m - m) * (u : A₀) ^ p ^ m) *
            ((algebraMap A₀ A π) ^ m * x ^ p ^ (m + n)) := by
        rw [mul_pow, ← map_pow, pow_add, mul_comm (p ^ m), pow_mul, compatible_roots_pow hw n,
          ← hu, mul_pow, map_mul, map_pow, map_pow, hπpow, map_mul, map_pow, map_pow]
        ring
      rw [hfactor]
      exact Subring.mul_mem _ ⟨_, rfl⟩
        (hm (Set.mul_mem_mul (Set.mem_singleton _) ⟨p ^ (m + n), rfl⟩))
    exact mem_range_algebraMap_of_pow_mem hπ hinj hpow
  · -- For every `k`, choose `n = k` so `k ≤ p ^ n`; then `π * x ^ k ∈ A₀`.
    refine isPowerBounded_iff.mpr (isBounded_of_mul_subset_range_of_hasBasis h ?_)
    rintro _ ⟨k, rfl⟩
    have hkp : k ≤ p ^ k := (Nat.lt_pow_self hp).le
    have hfactor : algebraMap A₀ A π * x ^ k =
        algebraMap A₀ A ((↑u⁻¹ : A₀) * w k ^ (p ^ k - k)) * (algebraMap A₀ A (w k) * x) ^ k := by
      have hπ_eq : π = (↑u⁻¹ : A₀) * w k ^ p ^ k := by
        rw [compatible_roots_pow hw k, ← hu, ← mul_assoc, mul_comm (↑u⁻¹ : A₀), mul_assoc,
          Units.inv_mul, mul_one]
      rw [mul_pow, ← mul_assoc, ← map_pow, ← map_mul, mul_assoc, ← pow_add,
        Nat.sub_add_cancel hkp, ← hπ_eq]
    rw [hfactor]
    exact Subring.mul_mem _ ⟨_, rfl⟩ (Subring.pow_mem _ (hx k) k)

/-- Subring form of `isPowerBounded_iff_forall_mul_mem_range_of_hasBasis`. -/
theorem mem_powerBoundedSubring_iff_forall_mul_mem_range_of_hasBasis [NonarchimedeanAddGroup A]
    {p : ℕ} (hp : 1 < p) (hπ : π ∈ A₀⁰) (hinj : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a)
    {w : ℕ → A₀} (hw : ∀ n, w (n + 1) ^ p = w n) (hassoc : Associated π (w 0)) {x : A} :
    x ∈ powerBoundedSubring A ↔ ∀ n, algebraMap A₀ A (w n) * x ∈ (algebraMap A₀ A).range :=
  mem_powerBoundedSubring.trans
    (isPowerBounded_iff_forall_mul_mem_range_of_hasBasis h hp hπ hinj hw hassoc)

/-- Under the hypotheses of `isPowerBounded_iff_forall_mul_mem_range_of_hasBasis`, `π · A° ⊆ A₀`. -/
theorem algebraMap_mul_mem_range_of_isPowerBounded_of_hasBasis {p : ℕ} (hp : 1 < p)
    (hπ : π ∈ A₀⁰) (hinj : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a)
    {w : ℕ → A₀} (hw : ∀ n, w (n + 1) ^ p = w n) (hassoc : Associated π (w 0))
    {x : A} (hx : IsPowerBounded x) :
    algebraMap A₀ A π * x ∈ (algebraMap A₀ A).range := by
  have h0 := (isPowerBounded_iff_forall_mul_mem_range_of_hasBasis h hp hπ hinj hw hassoc).mp hx 0
  obtain ⟨u, hu⟩ := hassoc
  have heq : algebraMap A₀ A π * x = algebraMap A₀ A (↑u⁻¹ : A₀) * (algebraMap A₀ A (w 0) * x) := by
    rw [← mul_assoc, ← map_mul, ← hu, mul_comm π, ← mul_assoc, Units.inv_mul, one_mul]
  rw [heq]
  exact Subring.mul_mem _ ⟨_, rfl⟩ h0

/-- **`A₀[1/π]` is uniform** when `π` is a nonzerodivisor with `π ^ p ∣ a ^ p → π ∣ a` and a unit
multiple of `π` has compatible `p`-power roots. -/
theorem isUniform_of_hasBasis_of_compatible_roots {p : ℕ} (hp : 1 < p)
    (hπ : π ∈ A₀⁰) (hinj : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a)
    {w : ℕ → A₀} (hw : ∀ n, w (n + 1) ^ p = w n) (hassoc : Associated π (w 0)) :
    IsUniform A :=
  isUniform_iff.mpr <| isBounded_of_mul_subset_range_of_hasBasis h fun _ hx ↦
    algebraMap_mul_mem_range_of_isPowerBounded_of_hasBasis h hp hπ hinj hw hassoc hx

/-- **`A₀[1/π]` is uniform** when `A₀` is `π`-adically complete for a nonzerodivisor `π` with
`π ^ p ∣ p` and bijective relative Frobenius `A₀ ⧸ (π) → A₀ ⧸ (π ^ p)`. -/
theorem isUniform_of_hasBasis {p : ℕ} [hp : Fact p.Prime] (hπ : π ∈ A₀⁰)
    (hdvd : π ^ p ∣ (p : A₀)) [IsAdicComplete (Ideal.span {π}) A₀]
    (hbij : Function.Bijective (frobeniusModPow p hdvd)) :
    IsUniform A := by
  obtain ⟨w, hassoc, hw⟩ :=
    exists_compatible_roots_associated hdvd ((frobeniusModPow_surjective_iff hdvd).mp hbij.2)
  exact isUniform_of_hasBasis_of_compatible_roots h hp.out.one_lt hπ
    ((frobeniusModPow_injective_iff hdvd).mp hbij.1) hw hassoc

end HasBasis

section Perfectoid

variable {p : ℕ} [hp : Fact p.Prime] {A₀ : Type*} [CommRing A₀] {π : A₀}
  {A : Type*} [CommRing A] [Algebra A₀ A] [IsLocalization.Away π A]
  [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [IsTateRing A]
  [CompleteSpace A] [T2Space A]

/-- **`A₀[1/π]` is a perfectoid Tate ring** (Bhatt–Morrow–Scholze, *Integral `p`-adic Hodge
theory*, Lemma 3.21): if `A₀` is `π`-adically complete for a nonzerodivisor `π` with `π ^ p ∣ p`
and bijective relative Frobenius `A₀ ⧸ (π) → A₀ ⧸ (π ^ p)`, then `A₀[1/π]` with its `π`-adic
topology is a perfectoid Tate ring. -/
theorem isPerfectoidTateRing_of_hasBasis
    (h : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd π A n : Set A))
    (hπ : π ∈ A₀⁰) (hdvd : π ^ p ∣ (p : A₀)) [IsAdicComplete (Ideal.span {π}) A₀]
    (hbij : Function.Bijective (frobeniusModPow p hdvd)) :
    IsPerfectoidTateRing p A := by
  have hp1 : 1 < p := hp.out.one_lt
  have hinj : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a := (frobeniusModPow_injective_iff hdvd).mp hbij.1
  have hsurj : ∀ a : A₀, ∃ b, π ^ p ∣ a - b ^ p := (frobeniusModPow_surjective_iff hdvd).mp hbij.2
  obtain ⟨w, hassoc, hw⟩ := exists_compatible_roots_associated hdvd hsurj
  have : IsUniform A := isUniform_of_hasBasis_of_compatible_roots h hp1 hπ hinj hw hassoc
  obtain ⟨u, hu⟩ := hassoc
  have hmem_pb (a : A₀) : algebraMap A₀ A a ∈ powerBoundedSubring A :=
    range_algebraMap_le_powerBoundedSubring_of_hasBasis h ⟨a, rfl⟩
  -- Every `w n` becomes a pseudouniformiser in `A`, since `w n ^ (p ^ n) = w 0 = π * u`.
  have hw_pu (n : ℕ) : IsPseudoUniformizer (algebraMap A₀ A (w n)) := by
    have h0 : IsPseudoUniformizer (algebraMap A₀ A (w 0)) := by
      rw [← hu, map_mul]
      exact isPseudoUniformizer_iff.mpr
        ⟨(IsLocalization.Away.algebraMap_isUnit π).mul (u.isUnit.map (algebraMap A₀ A)),
          by
            rw [mul_comm]
            exact (mem_powerBoundedSubring.mp (hmem_pb u)).isTopologicallyNilpotent_mul
              (isPseudoUniformizer_algebraMap_of_hasBasis h).isTopologicallyNilpotent⟩
    have hpow : (algebraMap A₀ A (w n)) ^ p ^ n = algebraMap A₀ A (w 0) := by
      rw [← map_pow, compatible_roots_pow hw n]
    rw [← hpow] at h0
    exact isPseudoUniformizer_iff.mpr
      ⟨(isUnit_pow_iff (pow_ne_zero n hp.out.ne_zero)).mp h0.isUnit,
        h0.isTopologicallyNilpotent.of_pow (pow_ne_zero n hp.out.ne_zero)⟩
  -- Take `ϖ = w 1 ∈ A°`: `ϖ ^ p = w 0` divides `p`, and every `x ∈ A°` has `w 1 * x ∈ A₀`,
  -- whose `p`-th root modulo `π ^ p` divides by `w 2` to give a `p`-th root of `x` modulo `w 0`.
  let ϖ : powerBoundedSubring A := ⟨algebraMap A₀ A (w 1), hmem_pb (w 1)⟩
  have hϖ_dvd : ϖ ^ p ∣ (p : powerBoundedSubring A) := by
    have hw0_dvd_π : w 0 ∣ π := ⟨(↑u⁻¹ : A₀), by rw [← hu, mul_assoc, Units.mul_inv, mul_one]⟩
    obtain ⟨d, hd⟩ : w 0 ∣ (p : A₀) :=
      hw0_dvd_π.trans ((dvd_pow_self π hp.out.ne_zero).trans hdvd)
    refine ⟨⟨algebraMap A₀ A d, hmem_pb d⟩, Subtype.ext ?_⟩
    simp only [ϖ, Subring.coe_pow, Subring.coe_mul, Subring.coe_natCast, ← map_pow, hw 0,
      ← map_mul, ← hd, map_natCast]
  refine IsPerfectoidTateRing.of_surjective ϖ (hw_pu 1) hϖ_dvd fun x ↦ ?_
  obtain ⟨a, ha⟩ :=
    (mem_powerBoundedSubring_iff_forall_mul_mem_range_of_hasBasis h hp1 hπ hinj hw ⟨u, hu⟩).mp x.2 1
  obtain ⟨b, c, hbc⟩ := hsurj a
  obtain ⟨v, hv⟩ := (hw_pu 2).isUnit
  have hv_pow : (v : A) ^ p = algebraMap A₀ A (w 1) := by
    rw [hv, ← map_pow, hw 1]
  let y : A := (↑v⁻¹ : A) * algebraMap A₀ A b
  let k : ℕ := p * p - (1 + p)
  have hk : 1 + p + k = p * p := Nat.add_sub_of_le (by nlinarith)
  let z₀ : A₀ := w 1 ^ k * (↑u⁻¹ : A₀) ^ p * c
  -- Compute `x - y ^ p = ϖ ^ p * z₀` by multiplying by the unit `w 1 = v ^ p`.
  have hdiff : (x : A) - y ^ p = (ϖ : A) ^ p * algebraMap A₀ A z₀ := by
    apply (hw_pu 1).isUnit.mul_left_cancel
    have hy_mul : algebraMap A₀ A (w 1) * y ^ p = algebraMap A₀ A (b ^ p) := by
      rw [← hv_pow, mul_pow, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul, map_pow]
    have hπ_pow : π ^ p = w 1 * (w 1 ^ p * (w 1 ^ k * (↑u⁻¹ : A₀) ^ p)) := by
      have hπ_eq : π = w 1 ^ p * (↑u⁻¹ : A₀) := by
        rw [hw 0, ← hu, mul_assoc, Units.mul_inv, mul_one]
      calc π ^ p
        _ = (w 1 ^ p) ^ p * (↑u⁻¹ : A₀) ^ p := by rw [hπ_eq, mul_pow]
        _ = w 1 ^ (1 + p + k) * (↑u⁻¹ : A₀) ^ p := by rw [← pow_mul, hk]
        _ = w 1 * (w 1 ^ p * (w 1 ^ k * (↑u⁻¹ : A₀) ^ p)) := by
          rw [pow_add, pow_add, pow_one]
          ring
    calc algebraMap A₀ A (w 1) * ((x : A) - y ^ p)
      _ = algebraMap A₀ A a - algebraMap A₀ A (b ^ p) := by
        rw [mul_sub, ← ha, hy_mul]
      _ = algebraMap A₀ A (π ^ p * c) := by rw [← map_sub, hbc]
      _ = algebraMap A₀ A (w 1) * ((ϖ : A) ^ p * algebraMap A₀ A z₀) := by
        rw [hπ_pow]
        simp only [ϖ, z₀, map_mul, map_pow]
        ring
  have hy_pow_pb : IsPowerBounded (y ^ p) := by
    have heq : y ^ p = (x : A) - (ϖ : A) ^ p * algebraMap A₀ A z₀ := by linear_combination -hdiff
    rw [heq]
    exact mem_powerBoundedSubring.mp
      (sub_mem x.2 (mul_mem (pow_mem ϖ.2 p) (hmem_pb z₀)))
  have hy_pb : y ∈ powerBoundedSubring A :=
    mem_powerBoundedSubring.mpr (hy_pow_pb.of_pow hp.out.ne_zero)
  refine ⟨⟨y, hy_pb⟩, ⟨⟨algebraMap A₀ A z₀, hmem_pb z₀⟩, Subtype.ext ?_⟩⟩
  push_cast
  exact hdiff

/-- **Inverting a nonzerodivisor `π` in an integral perfectoid ring gives a perfectoid Tate ring**
(Bhatt–Morrow–Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.21): if `A₀` is integral
perfectoid and `π`-adically complete for a nonzerodivisor `π` with `π ^ p ∣ p`, then `A₀[1/π]`
with its `π`-adic topology is a perfectoid Tate ring. -/
theorem isPerfectoidTateRing_of_isIntegralPerfectoid_of_hasBasis [IsIntegralPerfectoid p A₀]
    (h : (𝓝 (0 : A)).HasBasis (fun _ : ℕ ↦ True) fun n ↦ (awayNhd π A n : Set A))
    (hπ : π ∈ A₀⁰) (hdvd : π ^ p ∣ (p : A₀)) [IsAdicComplete (Ideal.span {π}) A₀] :
    IsPerfectoidTateRing p A :=
  isPerfectoidTateRing_of_hasBasis h hπ hdvd (IsIntegralPerfectoid.frobeniusModPow_bijective hdvd)

end Perfectoid

end TauCeti.Perfectoid
