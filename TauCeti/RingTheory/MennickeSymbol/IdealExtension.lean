/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MennickeSymbol.Dedekind
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Tactic.LinearCombination

/-!
# Extension of Mennicke symbols to nonzero ideals

Let `A` be a Dedekind domain, `I : Ideal A`, and `s : MennickeSymbol A I C` a Mennicke symbol with
values in an arbitrary monoid `C` (not assumed commutative). Following Bass–Milnor–Serre
Proposition 2.13, `s` extends canonically from principal elements `b ∈ I` to nonzero ideals
`𝔟 ≤ I` coprime to `Ideal.span {a}` (with `a - 1 ∈ I`):

Given `(a, 𝔟)`, choose any auxiliary ideal `𝔠` coprime to `𝔟` such that `𝔟 * 𝔠 = Ideal.span {b}`
is principal (`b ≠ 0`), and any lift `a' : A` satisfying `a' ≡ a (mod 𝔟)` and `a' ≡ 1 (mod 𝔠)`.
Then `(a', b)` is an admissible pair in `MennickePair A I`, and `s(a', b)` is **independent of
the choice of `(𝔠, b, a')`**. We denote this value by `s.evalIdeal a 𝔟 h𝔟0 h𝔟I ha hab`.

The extension satisfies:
* Principal specialization: `s.evalIdeal a (Ideal.span {b}) ... = s(a, b)` for `b ≠ 0`.
* Congruence invariance: `s.evalIdeal a₁ 𝔟 = s.evalIdeal a₂ 𝔟` whenever `a₁ - a₂ ∈ 𝔟`.
* Ideal multiplicativity: `s.evalIdeal a (𝔟₁ * 𝔟₂) = s.evalIdeal a 𝔟₁ * s.evalIdeal a 𝔟₂`
  (with no coprimality required between `𝔟₁` and `𝔟₂`).
* Scalar multiplicativity: `s.evalIdeal (a₁ * a₂) 𝔟 = s.evalIdeal a₁ 𝔟 * s.evalIdeal a₂ 𝔟`
  (via Lam's denominator multiplication lemma).
* Trivial values: `s.evalIdeal 1 𝔟 = 1` (and `s.evalIdeal a 𝔟 = 1` when `a - 1 ∈ 𝔟`), and
  `s.evalIdeal a ⊤ = 1`. Note that `s.evalIdeal u 𝔟` need **not** equal `1` for an arbitrary unit
  `u : Aˣ` when `𝔟` is not principal.
* Naturality (`evalIdeal_comp`, `evalIdeal_comapIdeal`), commutativity (`evalIdeal_commute`), and
  invertibility (`evalIdeal_isUnit`).

## Main definitions

* `TauCeti.MennickeSymbol.evalIdeal`: the extension `[𝔟 / a]` of `s : MennickeSymbol A I C` to
  nonzero ideals `𝔟 ≤ I` coprime to `Ideal.span {a}`.

## Main results

* `TauCeti.MennickeSymbol.evalIdeal_eq_of_aux`: evaluates `evalIdeal` using any auxiliary choice
  `(𝔠, b, a')`, witnessing independence of the auxiliary ideal `𝔠`, generator `b`, and lift `a'`.
* `TauCeti.MennickeSymbol.evalIdeal_span_singleton`: specialization to principal ideals.
* `TauCeti.MennickeSymbol.evalIdeal_congr` and `evalIdeal_add_mem`: invariance modulo `𝔟`.
* `TauCeti.MennickeSymbol.evalIdeal_mul_ideal`: multiplicativity in the ideal argument.
* `TauCeti.MennickeSymbol.evalIdeal_mul_fst`: multiplicativity in the scalar argument.
* `TauCeti.MennickeSymbol.evalIdeal_one`, `evalIdeal_eq_one_of_sub_one_mem`, and `evalIdeal_top`.
* `TauCeti.MennickeSymbol.evalIdeal_comp`, `evalIdeal_comapIdeal`, `evalIdeal_commute`, and
  `evalIdeal_isUnit`.

## References

* H. Bass, J. Milnor, and J.-P. Serre, *Solution of the congruence subgroup problem for `SL_n`
  (`n ≥ 3`) and `Sp_{2n}` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), §2, Proposition 2.13,
  pp. 69–71.
-/

public section

namespace TauCeti

namespace MennickeSymbol

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {I J : Ideal A}
  {C D : Type*} [Monoid C] [Monoid D]

/-! ### Auxiliary ideal construction and independence -/

/-- Any nonzero ideal `𝔟` admits an auxiliary nonzero ideal `𝔠` coprime to a given nonzero ideal
`K` such that `𝔟 * 𝔠` is principal. -/
private theorem exists_aux_ideal_mul_eq_span {𝔟 K : Ideal A} (h𝔟 : 𝔟 ≠ ⊥) (hK : K ≠ ⊥) :
    ∃ (𝔠 : Ideal A) (b : A), 𝔠 ≠ ⊥ ∧ b ≠ 0 ∧ 𝔟 * 𝔠 = Ideal.span {b} ∧ IsCoprime 𝔠 K := by
  let 𝔟0 : nonZeroDivisors (Ideal A) :=
    ⟨𝔟, mem_nonZeroDivisors_of_ne_zero (by rwa [Ideal.zero_eq_bot])⟩
  obtain ⟨𝔠0, hcls, hcop⟩ := ClassGroup.exists_mk0_eq_and_isCoprime (ClassGroup.mk0 𝔟0)⁻¹ hK
  obtain ⟨b, hb0, hmul⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp hcls
  refine ⟨(𝔠0 : Ideal A), b, ?_, hb0, ?_, hcop⟩
  · have hne := nonZeroDivisors.coe_ne_zero 𝔠0
    rwa [Ideal.zero_eq_bot] at hne
  · rw [mul_comm]
    exact hmul

omit [IsDedekindDomain A] in
/-- Two-ideal Chinese remainder lift: given coprime `𝔟, 𝔠` and `a : A`, find `a'` with
`a' - a ∈ 𝔟` and `a' - 1 ∈ 𝔠`. -/
private theorem exists_crt_one {𝔟 𝔠 : Ideal A} (hcop : IsCoprime 𝔟 𝔠) (a : A) :
    ∃ a' : A, a' - a ∈ 𝔟 ∧ a' - 1 ∈ 𝔠 := by
  obtain ⟨u, hu, v, hv, huv⟩ := Ideal.isCoprime_iff_exists.mp hcop
  refine ⟨u + v * a, ?_, ?_⟩
  · have heq : u + v * a - a = u * (1 - a) := by linear_combination a * huv
    rw [heq]
    exact 𝔟.mul_mem_right (1 - a) hu
  · have heq : u + v * a - 1 = v * (a - 1) := by linear_combination huv
    rw [heq]
    exact 𝔠.mul_mem_right (a - 1) hv

omit [IsDedekindDomain A] in
/-- If `𝔟 ≤ I` and `IsCoprime 𝔟 𝔠`, then `IsCoprime I 𝔠`. -/
private theorem isCoprime_of_le_left {𝔟 𝔠 : Ideal A} (h𝔟I : 𝔟 ≤ I) (hcop : IsCoprime 𝔟 𝔠) :
    IsCoprime I 𝔠 := by
  rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff]
  calc
    (⊤ : Ideal A) = 𝔟 ⊔ 𝔠 := hcop.sup_eq.symm
    _ ≤ I ⊔ 𝔠 := sup_le_sup_right h𝔟I 𝔠

omit [IsDedekindDomain A] in
/-- Build the admissible pair `(a', b)` from auxiliary data `(𝔠, b, a')`. -/
private def mkAuxPair {a : A} {𝔟 𝔠 : Ideal A} {b a' : A}
    (h𝔟I : 𝔟 ≤ I) (ha : a - 1 ∈ I) (hab : IsCoprime (Ideal.span {a}) 𝔟)
    (hb : 𝔟 * 𝔠 = Ideal.span {b}) (ha'b : a' - a ∈ 𝔟) (ha'c : a' - 1 ∈ 𝔠) :
    MennickePair A I where
  fst := a'
  snd := b
  sub_one_mem := by
    have heq : a' - 1 = (a' - a) + (a - 1) := by ring
    rw [heq]
    exact add_mem (h𝔟I ha'b) ha
  snd_mem := h𝔟I (Ideal.mul_le_left (hb ▸ Ideal.mem_span_singleton_self b))
  isCoprime := by
    have hcop_b : IsCoprime (Ideal.span {a'}) 𝔟 := by
      rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hab.sup_eq]
      refine sup_le ?_ le_sup_right
      rw [Ideal.span_singleton_le_iff_mem]
      have heq : a = a' - (a' - a) := by ring
      rw [heq]
      exact sub_mem (Submodule.mem_sup_left (Ideal.mem_span_singleton_self a'))
        (Submodule.mem_sup_right ha'b)
    have hcop_c : IsCoprime (Ideal.span {a'}) 𝔠 := by
      rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
      have heq : (1 : A) = a' - (a' - 1) := by ring
      rw [heq]
      exact sub_mem (Submodule.mem_sup_left (Ideal.mem_span_singleton_self a'))
        (Submodule.mem_sup_right ha'c)
    have hcop_bc : IsCoprime (Ideal.span {a'}) (Ideal.span {b}) := by
      rw [← hb]
      exact hcop_b.mul_right hcop_c
    exact (Ideal.isCoprime_span_singleton_iff a' b).mp hcop_bc

omit [IsDedekindDomain A] in
/-- Independence of the lift `a'` for fixed `(𝔠, b)`. -/
private theorem mkAuxPair_congr_lift (s : MennickeSymbol A I C) {a : A} {𝔟 𝔠 : Ideal A}
    {b a'₁ a'₂ : A} (h𝔟I : 𝔟 ≤ I) (ha : a - 1 ∈ I) (hab : IsCoprime (Ideal.span {a}) 𝔟)
    (hcop : IsCoprime 𝔟 𝔠) (hb : 𝔟 * 𝔠 = Ideal.span {b})
    (h1b : a'₁ - a ∈ 𝔟) (h1c : a'₁ - 1 ∈ 𝔠) (h2b : a'₂ - a ∈ 𝔟) (h2c : a'₂ - 1 ∈ 𝔠) :
    s (mkAuxPair h𝔟I ha hab hb h1b h1c) = s (mkAuxPair h𝔟I ha hab hb h2b h2c) := by
  have hdiff_b : a'₁ - a'₂ ∈ 𝔟 := by
    have heq : a'₁ - a'₂ = (a'₁ - a) - (a'₂ - a) := by ring
    rw [heq]
    exact sub_mem h1b h2b
  have hdiff_c : a'₁ - a'₂ ∈ 𝔠 := by
    have heq : a'₁ - a'₂ = (a'₁ - 1) - (a'₂ - 1) := by ring
    rw [heq]
    exact sub_mem h1c h2c
  have hdiff_span : a'₁ - a'₂ ∈ Ideal.span {b} := by
    rw [← hb, Ideal.mul_eq_inf_of_isCoprime hcop]
    exact ⟨hdiff_b, hdiff_c⟩
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hdiff_span
  exact s.map_eq_of_fst_eq_add_mul rfl (t := t) (by simp only [mkAuxPair]; linear_combination ht)

/-- Helper: given nonzero `𝔟 ≤ I` and nonzero `𝔠₁, 𝔠₂` with `𝔟 * 𝔠ᵢ = (bᵢ)`, construct an ideal
`𝔢` coprime to `𝔟`, `𝔠₁`, `𝔠₂` and elements `c₁, c₂` such that `𝔠ᵢ * (I * 𝔢) = (cᵢ)`. -/
private theorem exists_common_cofactor {𝔟 𝔠₁ 𝔠₂ : Ideal A} {b₁ b₂ : A}
    (h𝔟0 : 𝔟 ≠ ⊥) (h𝔟I : 𝔟 ≤ I) (h𝔠₁0 : 𝔠₁ ≠ ⊥) (h𝔠₂0 : 𝔠₂ ≠ ⊥)
    (hb₁ : 𝔟 * 𝔠₁ = Ideal.span {b₁}) (hb₂ : 𝔟 * 𝔠₂ = Ideal.span {b₂}) :
    ∃ (𝔢 : Ideal A) (c₁ c₂ : A),
      IsCoprime 𝔟 𝔢 ∧ IsCoprime 𝔠₁ 𝔢 ∧ IsCoprime 𝔠₂ 𝔢 ∧
      𝔠₁ * (I * 𝔢) = Ideal.span {c₁} ∧ 𝔠₂ * (I * 𝔢) = Ideal.span {c₂} := by
  have hI0 : I ≠ ⊥ := fun hbot ↦ h𝔟0 (le_bot_iff.mp (hbot ▸ h𝔟I))
  have hb₁0 : b₁ ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_zero, ← Ideal.zero_eq_bot] at hb₁
    exact mul_ne_zero (by rwa [Ideal.zero_eq_bot]) (by rwa [Ideal.zero_eq_bot]) hb₁
  have hb₂0 : b₂ ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_zero, ← Ideal.zero_eq_bot] at hb₂
    exact mul_ne_zero (by rwa [Ideal.zero_eq_bot]) (by rwa [Ideal.zero_eq_bot]) hb₂
  have hJ0 : 𝔟 * 𝔠₁ * 𝔠₂ ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact mul_ne_zero (mul_ne_zero (by rwa [Ideal.zero_eq_bot]) (by rwa [Ideal.zero_eq_bot]))
      (by rwa [Ideal.zero_eq_bot])
  let 𝔟0 : nonZeroDivisors (Ideal A) :=
    ⟨𝔟, mem_nonZeroDivisors_of_ne_zero (by rwa [Ideal.zero_eq_bot])⟩
  let I0 : nonZeroDivisors (Ideal A) :=
    ⟨I, mem_nonZeroDivisors_of_ne_zero (by rwa [Ideal.zero_eq_bot])⟩
  let 𝔠₁0 : nonZeroDivisors (Ideal A) :=
    ⟨𝔠₁, mem_nonZeroDivisors_of_ne_zero (by rwa [Ideal.zero_eq_bot])⟩
  let 𝔠₂0 : nonZeroDivisors (Ideal A) :=
    ⟨𝔠₂, mem_nonZeroDivisors_of_ne_zero (by rwa [Ideal.zero_eq_bot])⟩
  obtain ⟨𝔢0, h𝔢_cls, h𝔢_cop⟩ :=
    ClassGroup.exists_mk0_eq_and_isCoprime (ClassGroup.mk0 𝔟0 * (ClassGroup.mk0 I0)⁻¹) hJ0
  let 𝔡0 : nonZeroDivisors (Ideal A) := I0 * 𝔢0
  have h𝔡_cls : ClassGroup.mk0 𝔡0 = ClassGroup.mk0 𝔟0 := by
    rw [map_mul, h𝔢_cls, mul_comm (ClassGroup.mk0 𝔟0), mul_inv_cancel_left]
  have h𝔠₁_cls : ClassGroup.mk0 𝔠₁0 = (ClassGroup.mk0 𝔡0)⁻¹ := by
    rw [h𝔡_cls]
    exact ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨b₁, hb₁0, by rw [mul_comm]; exact hb₁⟩
  have h𝔠₂_cls : ClassGroup.mk0 𝔠₂0 = (ClassGroup.mk0 𝔡0)⁻¹ := by
    rw [h𝔡_cls]
    exact ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨b₂, hb₂0, by rw [mul_comm]; exact hb₂⟩
  obtain ⟨c₁, _, hc₁⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp h𝔠₁_cls
  obtain ⟨c₂, _, hc₂⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp h𝔠₂_cls
  exact ⟨(𝔢0 : Ideal A), c₁, c₂,
    (h𝔢_cop.of_mul_right_left.of_mul_right_left).symm,
    (h𝔢_cop.of_mul_right_left.of_mul_right_right).symm,
    (h𝔢_cop.of_mul_right_right).symm, hc₁, hc₂⟩

/-- Common-lift comparison: given a shared lift `a'` with `a' ≡ a (mod 𝔟)` and `a' ≡ 1 (mod cᵢ)`
where `𝔠ᵢ * (I * 𝔢) = Ideal.span {cᵢ}`, the two auxiliary pairs `(a', b₁)` and `(a', b₂)` have
equal symbol values. -/
private theorem mkAuxPair_eq_of_common_lift (s : MennickeSymbol A I C) {a a' : A}
    {𝔟 𝔠₁ 𝔠₂ 𝔢 : Ideal A} {b₁ b₂ c₁ c₂ : A} (h𝔟I : 𝔟 ≤ I) (ha : a - 1 ∈ I)
    (hab : IsCoprime (Ideal.span {a}) 𝔟)
    (hb₁ : 𝔟 * 𝔠₁ = Ideal.span {b₁}) (hb₂ : 𝔟 * 𝔠₂ = Ideal.span {b₂})
    (hc₁ : 𝔠₁ * (I * 𝔢) = Ideal.span {c₁}) (hc₂ : 𝔠₂ * (I * 𝔢) = Ideal.span {c₂})
    (ha'b : a' - a ∈ 𝔟) (ha'c₁ : a' - 1 ∈ 𝔠₁) (ha'c₂ : a' - 1 ∈ 𝔠₂)
    (ha'c₁_span : a' - 1 ∈ Ideal.span {c₁}) (ha'c₂_span : a' - 1 ∈ Ideal.span {c₂}) :
    s (mkAuxPair h𝔟I ha hab hb₁ ha'b ha'c₁) = s (mkAuxPair h𝔟I ha hab hb₂ ha'b ha'c₂) := by
  let q₁ := mkAuxPair h𝔟I ha hab hb₁ ha'b ha'c₁
  let q₂ := mkAuxPair h𝔟I ha hab hb₂ ha'b ha'c₂
  have ha'I : a' - 1 ∈ I := q₁.sub_one_mem
  let r₁ : MennickePair A I :=
    { fst := a'
      snd := c₁
      sub_one_mem := ha'I
      snd_mem := Ideal.mul_le_left (Ideal.mul_le_right (hc₁ ▸ Ideal.mem_span_singleton_self c₁))
      isCoprime := by
        simpa using IsCoprime.add_one_left_of_dvd (Ideal.mem_span_singleton.mp ha'c₁_span) }
  let r₂ : MennickePair A I :=
    { fst := a'
      snd := c₂
      sub_one_mem := ha'I
      snd_mem := Ideal.mul_le_left (Ideal.mul_le_right (hc₂ ▸ Ideal.mem_span_singleton_self c₂))
      isCoprime := by
        simpa using IsCoprime.add_one_left_of_dvd (Ideal.mem_span_singleton.mp ha'c₂_span) }
  have hr₁ : s r₁ = 1 := s.map_eq_one_of_sub_one_mem_span ha'c₁_span
  have hr₂ : s r₂ = 1 := s.map_eq_one_of_sub_one_mem_span ha'c₂_span
  have hspan_eq : Ideal.span {b₁ * c₂} = Ideal.span {b₂ * c₁} := by
    calc
      Ideal.span {b₁ * c₂} = Ideal.span {b₁} * Ideal.span {c₂} :=
        (Ideal.span_singleton_mul_span_singleton b₁ c₂).symm
      _ = (𝔟 * 𝔠₁) * (𝔠₂ * (I * 𝔢)) := by rw [hb₁, hc₂]
      _ = (𝔟 * 𝔠₂) * (𝔠₁ * (I * 𝔢)) := by ring
      _ = Ideal.span {b₂} * Ideal.span {c₁} := by rw [hb₂, hc₁]
      _ = Ideal.span {b₂ * c₁} := Ideal.span_singleton_mul_span_singleton b₂ c₁
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan_eq
  have hprod_eq : s (q₁.mulSnd r₂ rfl) = s (q₂.mulSnd r₁ rfl) :=
    s.map_unit_mul_snd u⁻¹ (by simp [q₁, q₂, mkAuxPair]) (by
      simp only [MennickePair.mulSnd_snd, q₁, q₂, r₁, r₂, mkAuxPair]
      calc
        b₁ * c₂ = (↑u⁻¹ : A) * ((u : A) * (b₁ * c₂)) := by rw [← mul_assoc]; simp
        _ = (↑u⁻¹ : A) * (b₂ * c₁) := by rw [mul_comm (u : A), hu])
  calc
    s q₁ = s q₁ * s r₂ := by rw [hr₂, mul_one]
    _ = s (q₁.mulSnd r₂ rfl) := (s.map_mulSnd q₁ r₂ rfl).symm
    _ = s (q₂.mulSnd r₁ rfl) := hprod_eq
    _ = s q₂ * s r₁ := s.map_mulSnd q₂ r₁ rfl
    _ = s q₂ := by rw [hr₁, mul_one]

/-- Independence of the auxiliary ideal `𝔠` and generator `b` (and lift `a'`). Works directly
for arbitrary nonzero `𝔠₁, 𝔠₂` coprime to `𝔟`, without assuming `IsCoprime 𝔠₁ 𝔠₂`. -/
private theorem mkAuxPair_indep (s : MennickeSymbol A I C) {a : A} {𝔟 : Ideal A}
    (h𝔟0 : 𝔟 ≠ ⊥) (h𝔟I : 𝔟 ≤ I) (ha : a - 1 ∈ I) (hab : IsCoprime (Ideal.span {a}) 𝔟)
    {𝔠₁ 𝔠₂ : Ideal A} {b₁ b₂ a'₁ a'₂ : A}
    (h𝔠₁0 : 𝔠₁ ≠ ⊥) (h𝔠₂0 : 𝔠₂ ≠ ⊥)
    (hcop₁ : IsCoprime 𝔟 𝔠₁) (hcop₂ : IsCoprime 𝔟 𝔠₂)
    (hb₁ : 𝔟 * 𝔠₁ = Ideal.span {b₁}) (hb₂ : 𝔟 * 𝔠₂ = Ideal.span {b₂})
    (h1b : a'₁ - a ∈ 𝔟) (h1c : a'₁ - 1 ∈ 𝔠₁) (h2b : a'₂ - a ∈ 𝔟) (h2c : a'₂ - 1 ∈ 𝔠₂) :
    s (mkAuxPair h𝔟I ha hab hb₁ h1b h1c) = s (mkAuxPair h𝔟I ha hab hb₂ h2b h2c) := by
  obtain ⟨𝔢, c₁, c₂, h𝔢𝔟, h𝔢𝔠₁, h𝔢𝔠₂, hc₁, hc₂⟩ :=
    exists_common_cofactor h𝔟0 h𝔟I h𝔠₁0 h𝔠₂0 hb₁ hb₂
  have hcop_all : IsCoprime 𝔟 (𝔠₁ * 𝔠₂ * 𝔢) := (hcop₁.mul_right hcop₂).mul_right h𝔢𝔟
  obtain ⟨a', ha'b, ha'all⟩ := exists_crt_one hcop_all a
  have ha'c₁ : a' - 1 ∈ 𝔠₁ := Ideal.mul_le_left (Ideal.mul_le_left ha'all)
  have ha'c₂ : a' - 1 ∈ 𝔠₂ := Ideal.mul_le_right (Ideal.mul_le_left ha'all)
  have ha'e : a' - 1 ∈ 𝔢 := Ideal.mul_le_right ha'all
  have ha'I : a' - 1 ∈ I := by
    have heq : a' - 1 = (a' - a) + (a - 1) := by ring
    rw [heq]
    exact add_mem (h𝔟I ha'b) ha
  have hIe : IsCoprime I 𝔢 := isCoprime_of_le_left h𝔟I h𝔢𝔟
  have ha'd : a' - 1 ∈ I * 𝔢 := by
    rw [Ideal.mul_eq_inf_of_isCoprime hIe]
    exact ⟨ha'I, ha'e⟩
  have h𝔠₁d : IsCoprime 𝔠₁ (I * 𝔢) := (isCoprime_of_le_left h𝔟I hcop₁).symm.mul_right h𝔢𝔠₁
  have h𝔠₂d : IsCoprime 𝔠₂ (I * 𝔢) := (isCoprime_of_le_left h𝔟I hcop₂).symm.mul_right h𝔢𝔠₂
  have ha'c₁_span : a' - 1 ∈ Ideal.span {c₁} := by
    rw [← hc₁, Ideal.mul_eq_inf_of_isCoprime h𝔠₁d]
    exact ⟨ha'c₁, ha'd⟩
  have ha'c₂_span : a' - 1 ∈ Ideal.span {c₂} := by
    rw [← hc₂, Ideal.mul_eq_inf_of_isCoprime h𝔠₂d]
    exact ⟨ha'c₂, ha'd⟩
  calc
    s (mkAuxPair h𝔟I ha hab hb₁ h1b h1c) = s (mkAuxPair h𝔟I ha hab hb₁ ha'b ha'c₁) :=
      mkAuxPair_congr_lift s h𝔟I ha hab hcop₁ hb₁ h1b h1c ha'b ha'c₁
    _ = s (mkAuxPair h𝔟I ha hab hb₂ ha'b ha'c₂) :=
      mkAuxPair_eq_of_common_lift s h𝔟I ha hab hb₁ hb₂ hc₁ hc₂ ha'b ha'c₁ ha'c₂
        ha'c₁_span ha'c₂_span
    _ = s (mkAuxPair h𝔟I ha hab hb₂ h2b h2c) :=
      mkAuxPair_congr_lift s h𝔟I ha hab hcop₂ hb₂ ha'b ha'c₂ h2b h2c

/-! ### Definition and fundamental properties of `evalIdeal` -/

/-- Extension of a Mennicke symbol `s : MennickeSymbol A I C` (into an arbitrary monoid `C`) to
nonzero ideals `𝔟 ≤ I` coprime to `Ideal.span {a}` with `a - 1 ∈ I`
(Bass–Milnor–Serre Proposition 2.13). -/
noncomputable def evalIdeal (s : MennickeSymbol A I C) (a : A) (𝔟 : Ideal A)
    (h𝔟0 : 𝔟 ≠ ⊥) (h𝔟I : 𝔟 ≤ I) (ha : a - 1 ∈ I) (hab : IsCoprime (Ideal.span {a}) 𝔟) : C :=
  let haux := exists_aux_ideal_mul_eq_span h𝔟0 h𝔟0
  let hspec := haux.choose_spec.choose_spec
  let hlift := exists_crt_one hspec.2.2.2.symm a
  s (mkAuxPair h𝔟I ha hab hspec.2.2.1 hlift.choose_spec.1 hlift.choose_spec.2)

/-- **Independence of auxiliary data**: `s.evalIdeal a 𝔟` equals `s p` for any admissible pair
`p = (a', b)` arising from any auxiliary ideal `𝔠` coprime to `𝔟` with `𝔟 * 𝔠 = Ideal.span {b}`,
`a' - a ∈ 𝔟`, and `a' - 1 ∈ 𝔠`. -/
theorem evalIdeal_eq_of_aux (s : MennickeSymbol A I C) {a : A} {𝔟 : Ideal A}
    (h𝔟0 : 𝔟 ≠ ⊥) (h𝔟I : 𝔟 ≤ I) (ha : a - 1 ∈ I) (hab : IsCoprime (Ideal.span {a}) 𝔟)
    {𝔠 : Ideal A} {b a' : A} (hcop : IsCoprime 𝔟 𝔠) (hb : 𝔟 * 𝔠 = Ideal.span {b})
    (ha'b : a' - a ∈ 𝔟) (ha'c : a' - 1 ∈ 𝔠) {p : MennickePair A I}
    (hp_fst : p.fst = a') (hp_snd : p.snd = b) :
    s.evalIdeal a 𝔟 h𝔟0 h𝔟I ha hab = s p := by
  have hp_eq : mkAuxPair h𝔟I ha hab hb ha'b ha'c = p := by
    ext
    · simp [mkAuxPair, hp_fst]
    · simp [mkAuxPair, hp_snd]
  rw [← hp_eq]
  by_cases h𝔠0 : 𝔠 = ⊥
  · subst h𝔠0
    have h𝔟_top : 𝔟 = ⊤ := by simpa using hcop.sup_eq
    have hb0 : b = 0 := by simpa [Ideal.span_singleton_eq_bot] using hb.symm
    have h1 : s (mkAuxPair h𝔟I ha hab hb ha'b ha'c) = 1 :=
      s.map_eq_one_of_snd_eq_zero (by simp [mkAuxPair, hb0])
    have htop : s.evalIdeal a 𝔟 h𝔟0 h𝔟I ha hab = 1 := by
      unfold evalIdeal
      have hspec := (exists_aux_ideal_mul_eq_span h𝔟0 h𝔟0).choose_spec.choose_spec
      have hcop_top : IsCoprime 𝔟 (⊤ : Ideal A) :=
        Ideal.isCoprime_iff_sup_eq.mpr (sup_top_eq 𝔟)
      rw [mkAuxPair_indep s h𝔟0 h𝔟I ha hab hspec.1 top_ne_bot hspec.2.2.2.symm hcop_top
        hspec.2.2.1 (by rw [h𝔟_top, Ideal.mul_top, Ideal.span_singleton_one])
        _ _ (by rw [h𝔟_top]; exact Submodule.mem_top) Submodule.mem_top]
      exact s.map_eq_one_of_fst_eq_one rfl
    exact htop.trans h1.symm
  · unfold evalIdeal
    have hspec := (exists_aux_ideal_mul_eq_span h𝔟0 h𝔟0).choose_spec.choose_spec
    exact mkAuxPair_indep s h𝔟0 h𝔟I ha hab hspec.1 h𝔠0 hspec.2.2.2.symm hcop
      hspec.2.2.1 hb _ _ ha'b ha'c

/-- **Principal specialization**: when `𝔟 = Ideal.span {p.snd}` is nonzero, `evalIdeal`
recovers the original Mennicke symbol value `s p`. -/
@[simp]
theorem evalIdeal_span_singleton (s : MennickeSymbol A I C) (p : MennickePair A I)
    (h𝔟0 : Ideal.span {p.snd} ≠ ⊥)
    (h𝔟I : Ideal.span {p.snd} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr p.snd_mem)
    (hab : IsCoprime (Ideal.span {p.fst}) (Ideal.span {p.snd}) :=
      (Ideal.isCoprime_span_singleton_iff p.fst p.snd).mpr p.isCoprime) :
    s.evalIdeal p.fst (Ideal.span {p.snd}) h𝔟0 h𝔟I p.sub_one_mem hab = s p :=
  s.evalIdeal_eq_of_aux h𝔟0 h𝔟I p.sub_one_mem hab (𝔠 := ⊤) (b := p.snd) (a' := p.fst)
    (Ideal.isCoprime_iff_sup_eq.mpr (sup_top_eq _)) (Ideal.mul_top _) (by simp) Submodule.mem_top
    rfl rfl

/-- **Congruence invariance**: `evalIdeal s a₁ 𝔟 = evalIdeal s a₂ 𝔟` whenever `a₁ - a₂ ∈ 𝔟`. -/
theorem evalIdeal_congr (s : MennickeSymbol A I C) {a₁ a₂ : A} {𝔟 : Ideal A}
    (h𝔟0 : 𝔟 ≠ ⊥) (h𝔟I : 𝔟 ≤ I) (ha₁ : a₁ - 1 ∈ I) (ha₂ : a₂ - 1 ∈ I)
    (hab₁ : IsCoprime (Ideal.span {a₁}) 𝔟) (hab₂ : IsCoprime (Ideal.span {a₂}) 𝔟)
    (hcong : a₁ - a₂ ∈ 𝔟) :
    s.evalIdeal a₁ 𝔟 h𝔟0 h𝔟I ha₁ hab₁ = s.evalIdeal a₂ 𝔟 h𝔟0 h𝔟I ha₂ hab₂ := by
  obtain ⟨𝔠, b, _, _, hb, hcop⟩ := exists_aux_ideal_mul_eq_span h𝔟0 h𝔟0
  obtain ⟨a', ha'b₁, ha'c⟩ := exists_crt_one hcop.symm a₁
  have ha'b₂ : a' - a₂ ∈ 𝔟 := by
    have heq : a' - a₂ = (a' - a₁) + (a₁ - a₂) := by ring
    rw [heq]
    exact add_mem ha'b₁ hcong
  let p := mkAuxPair h𝔟I ha₁ hab₁ hb ha'b₁ ha'c
  rw [s.evalIdeal_eq_of_aux h𝔟0 h𝔟I ha₁ hab₁ hcop.symm hb ha'b₁ ha'c (p := p) rfl rfl,
    s.evalIdeal_eq_of_aux h𝔟0 h𝔟I ha₂ hab₂ hcop.symm hb ha'b₂ ha'c (p := p) rfl rfl]

/-- Shift invariance `a ↦ a + x` for `x ∈ 𝔟`. -/
theorem evalIdeal_add_mem (s : MennickeSymbol A I C) {a x : A} {𝔟 : Ideal A}
    (h𝔟0 : 𝔟 ≠ ⊥) (h𝔟I : 𝔟 ≤ I) (ha : a - 1 ∈ I) (hx : x ∈ 𝔟)
    (hab : IsCoprime (Ideal.span {a}) 𝔟)
    (hax : a + x - 1 ∈ I := by
      have heq : a + x - 1 = (a - 1) + x := by ring
      rw [heq]; exact add_mem ha (h𝔟I hx))
    (habx : IsCoprime (Ideal.span {a + x}) 𝔟 := by
      rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hab.sup_eq]
      refine sup_le ?_ le_sup_right
      rw [Ideal.span_singleton_le_iff_mem]
      have heq : a = (a + x) - x := by ring
      rw [heq]
      exact sub_mem (Submodule.mem_sup_left (Ideal.mem_span_singleton_self (a + x)))
        (Submodule.mem_sup_right hx)) :
    s.evalIdeal (a + x) 𝔟 h𝔟0 h𝔟I hax habx = s.evalIdeal a 𝔟 h𝔟0 h𝔟I ha hab :=
  s.evalIdeal_congr h𝔟0 h𝔟I hax ha habx hab (by simpa using hx)

/-- `evalIdeal` sends `a = 1` to `1` for every nonzero ideal `𝔟 ≤ I`. -/
@[simp]
theorem evalIdeal_one (s : MennickeSymbol A I C) {𝔟 : Ideal A}
    (h𝔟0 : 𝔟 ≠ ⊥) (h𝔟I : 𝔟 ≤ I)
    (h1 : (1 : A) - 1 ∈ I := by simp)
    (hab : IsCoprime (Ideal.span {(1 : A)}) 𝔟 := by
      rw [Ideal.span_singleton_one, Ideal.isCoprime_iff_sup_eq]; exact top_sup_eq 𝔟) :
    s.evalIdeal 1 𝔟 h𝔟0 h𝔟I h1 hab = 1 := by
  obtain ⟨𝔠, b, _, _, hb, hcop⟩ := exists_aux_ideal_mul_eq_span h𝔟0 h𝔟0
  let p := mkAuxPair h𝔟I h1 hab hb (by simp : (1 : A) - 1 ∈ 𝔟) (by simp : (1 : A) - 1 ∈ 𝔠)
  rw [s.evalIdeal_eq_of_aux h𝔟0 h𝔟I h1 hab hcop.symm hb (a' := 1) (by simp) (by simp)
    (p := p) rfl rfl]
  exact s.map_eq_one_of_fst_eq_one rfl

/-- If `a ≡ 1 (mod 𝔟)`, then `s.evalIdeal a 𝔟 = 1`. -/
theorem evalIdeal_eq_one_of_sub_one_mem (s : MennickeSymbol A I C) {a : A} {𝔟 : Ideal A}
    (h𝔟0 : 𝔟 ≠ ⊥) (h𝔟I : 𝔟 ≤ I) (ha : a - 1 ∈ 𝔟)
    (haI : a - 1 ∈ I := h𝔟I ha)
    (hab : IsCoprime (Ideal.span {a}) 𝔟 := by
      rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
      have heq : (1 : A) = a - (a - 1) := by ring
      rw [heq]
      exact sub_mem (Submodule.mem_sup_left (Ideal.mem_span_singleton_self a))
        (Submodule.mem_sup_right ha)) :
    s.evalIdeal a 𝔟 h𝔟0 h𝔟I haI hab = 1 := by
  have h1 : IsCoprime (Ideal.span {(1 : A)}) 𝔟 := by
    rw [Ideal.span_singleton_one, Ideal.isCoprime_iff_sup_eq]
    exact top_sup_eq 𝔟
  rw [s.evalIdeal_congr h𝔟0 h𝔟I haI (by simp) hab h1 ha]
  exact s.evalIdeal_one h𝔟0 h𝔟I (by simp) h1

/-- At the unit ideal `𝔟 = ⊤`, `evalIdeal` is identically `1`. -/
@[simp]
theorem evalIdeal_top (s : MennickeSymbol A I C) {a : A}
    (h𝔟0 : (⊤ : Ideal A) ≠ ⊥ := top_ne_bot) (h𝔟I : (⊤ : Ideal A) ≤ I)
    (ha : a - 1 ∈ I := h𝔟I Submodule.mem_top)
    (hab : IsCoprime (Ideal.span {a}) (⊤ : Ideal A) :=
      Ideal.isCoprime_iff_sup_eq.mpr (sup_top_eq _)) :
    s.evalIdeal a ⊤ h𝔟0 h𝔟I ha hab = 1 :=
  s.evalIdeal_eq_one_of_sub_one_mem h𝔟0 h𝔟I Submodule.mem_top ha hab

/-- **Multiplicativity in the ideal argument**: for any nonzero ideals `𝔟₁, 𝔟₂ ≤ I` coprime to
`Ideal.span {a}` (with no coprimality assumed between `𝔟₁` and `𝔟₂`),
`[𝔟₁ * 𝔟₂ / a] = [𝔟₁ / a] * [𝔟₂ / a]`. -/
theorem evalIdeal_mul_ideal (s : MennickeSymbol A I C) {a : A} {𝔟₁ 𝔟₂ : Ideal A}
    (h₁0 : 𝔟₁ ≠ ⊥) (h₂0 : 𝔟₂ ≠ ⊥) (h₁I : 𝔟₁ ≤ I) (h₂I : 𝔟₂ ≤ I) (ha : a - 1 ∈ I)
    (hab₁ : IsCoprime (Ideal.span {a}) 𝔟₁) (hab₂ : IsCoprime (Ideal.span {a}) 𝔟₂)
    (h12_0 : 𝔟₁ * 𝔟₂ ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact mul_ne_zero (by rwa [Ideal.zero_eq_bot]) (by rwa [Ideal.zero_eq_bot]))
    (h12_I : 𝔟₁ * 𝔟₂ ≤ I := Ideal.mul_le_left.trans h₁I)
    (hab12 : IsCoprime (Ideal.span {a}) (𝔟₁ * 𝔟₂) := hab₁.mul_right hab₂) :
    s.evalIdeal a (𝔟₁ * 𝔟₂) h12_0 h12_I ha hab12 =
      s.evalIdeal a 𝔟₁ h₁0 h₁I ha hab₁ * s.evalIdeal a 𝔟₂ h₂0 h₂I ha hab₂ := by
  obtain ⟨𝔠₁, b₁, h𝔠₁0, _, hb₁, hcop₁⟩ := exists_aux_ideal_mul_eq_span h₁0 h12_0
  have hK0 : 𝔟₁ * 𝔟₂ * 𝔠₁ ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact mul_ne_zero (by rwa [Ideal.zero_eq_bot]) (by rwa [Ideal.zero_eq_bot])
  obtain ⟨𝔠₂, b₂, _, _, hb₂, hcop₂⟩ := exists_aux_ideal_mul_eq_span h₂0 hK0
  have hcop₁_b₁ : IsCoprime 𝔟₁ 𝔠₁ := (hcop₁.of_mul_right_left).symm
  have hcop₂_b₂ : IsCoprime 𝔟₂ 𝔠₂ := (hcop₂.of_mul_right_left.of_mul_right_right).symm
  have hcop₁₂ : IsCoprime (𝔟₁ * 𝔟₂) (𝔠₁ * 𝔠₂) :=
    hcop₁.symm.mul_right (hcop₂.of_mul_right_left).symm
  have hmul : (𝔟₁ * 𝔟₂) * (𝔠₁ * 𝔠₂) = Ideal.span {b₁ * b₂} := by
    calc
      (𝔟₁ * 𝔟₂) * (𝔠₁ * 𝔠₂) = (𝔟₁ * 𝔠₁) * (𝔟₂ * 𝔠₂) := by ring
      _ = Ideal.span {b₁} * Ideal.span {b₂} := by rw [hb₁, hb₂]
      _ = Ideal.span {b₁ * b₂} := Ideal.span_singleton_mul_span_singleton b₁ b₂
  obtain ⟨a', ha'b, ha'c⟩ := exists_crt_one hcop₁₂ a
  have ha'b₁ : a' - a ∈ 𝔟₁ := Ideal.mul_le_left ha'b
  have ha'b₂ : a' - a ∈ 𝔟₂ := Ideal.mul_le_right ha'b
  have ha'c₁ : a' - 1 ∈ 𝔠₁ := Ideal.mul_le_left ha'c
  have ha'c₂ : a' - 1 ∈ 𝔠₂ := Ideal.mul_le_right ha'c
  let p₁ := mkAuxPair h₁I ha hab₁ hb₁ ha'b₁ ha'c₁
  let p₂ := mkAuxPair h₂I ha hab₂ hb₂ ha'b₂ ha'c₂
  let p₁₂ := mkAuxPair h12_I ha hab12 hmul ha'b ha'c
  rw [s.evalIdeal_eq_of_aux h12_0 h12_I ha hab12 hcop₁₂ hmul ha'b ha'c (p := p₁₂) rfl rfl,
    s.evalIdeal_eq_of_aux h₁0 h₁I ha hab₁ hcop₁_b₁ hb₁ ha'b₁ ha'c₁ (p := p₁) rfl rfl,
    s.evalIdeal_eq_of_aux h₂0 h₂I ha hab₂ hcop₂_b₂ hb₂ ha'b₂ ha'c₂ (p := p₂) rfl rfl]
  exact s.map_mul_snd_eq rfl rfl rfl

/-- **Multiplicativity in the scalar argument** (via Lam's denominator multiplication lemma):
`[𝔟 / a₁ * a₂] = [𝔟 / a₁] * [𝔟 / a₂]` for any Mennicke symbol into an arbitrary monoid `C`. -/
theorem evalIdeal_mul_fst (s : MennickeSymbol A I C) {a₁ a₂ : A} {𝔟 : Ideal A}
    (h𝔟0 : 𝔟 ≠ ⊥) (h𝔟I : 𝔟 ≤ I) (ha₁ : a₁ - 1 ∈ I) (ha₂ : a₂ - 1 ∈ I)
    (hab₁ : IsCoprime (Ideal.span {a₁}) 𝔟) (hab₂ : IsCoprime (Ideal.span {a₂}) 𝔟)
    (ha₁₂ : a₁ * a₂ - 1 ∈ I := by
      have heq : a₁ * a₂ - 1 = a₁ * (a₂ - 1) + (a₁ - 1) := by ring
      rw [heq]; exact add_mem (I.mul_mem_left a₁ ha₂) ha₁)
    (hab₁₂ : IsCoprime (Ideal.span {a₁ * a₂}) 𝔟 := by
      rw [← Ideal.span_singleton_mul_span_singleton]
      exact hab₁.mul_left hab₂) :
    s.evalIdeal (a₁ * a₂) 𝔟 h𝔟0 h𝔟I ha₁₂ hab₁₂ =
      s.evalIdeal a₁ 𝔟 h𝔟0 h𝔟I ha₁ hab₁ * s.evalIdeal a₂ 𝔟 h𝔟0 h𝔟I ha₂ hab₂ := by
  obtain ⟨𝔠, b, _, _, hb, hcop⟩ := exists_aux_ideal_mul_eq_span h𝔟0 h𝔟0
  obtain ⟨a'₁, ha'₁b, ha'₁c⟩ := exists_crt_one hcop.symm a₁
  obtain ⟨a'₂, ha'₂b, ha'₂c⟩ := exists_crt_one hcop.symm a₂
  have ha'₁₂b : a'₁ * a'₂ - a₁ * a₂ ∈ 𝔟 := by
    have heq : a'₁ * a'₂ - a₁ * a₂ = a'₁ * (a'₂ - a₂) + (a'₁ - a₁) * a₂ := by ring
    rw [heq]
    exact add_mem (𝔟.mul_mem_left a'₁ ha'₂b) (𝔟.mul_mem_right a₂ ha'₁b)
  have ha'₁₂c : a'₁ * a'₂ - 1 ∈ 𝔠 := by
    have heq : a'₁ * a'₂ - 1 = a'₁ * (a'₂ - 1) + (a'₁ - 1) := by ring
    rw [heq]
    exact add_mem (𝔠.mul_mem_left a'₁ ha'₂c) ha'₁c
  let p₁ := mkAuxPair h𝔟I ha₁ hab₁ hb ha'₁b ha'₁c
  let p₂ := mkAuxPair h𝔟I ha₂ hab₂ hb ha'₂b ha'₂c
  let p₁₂ := mkAuxPair h𝔟I ha₁₂ hab₁₂ hb ha'₁₂b ha'₁₂c
  rw [s.evalIdeal_eq_of_aux h𝔟0 h𝔟I ha₁₂ hab₁₂ hcop.symm hb ha'₁₂b ha'₁₂c (p := p₁₂) rfl rfl,
    s.evalIdeal_eq_of_aux h𝔟0 h𝔟I ha₁ hab₁ hcop.symm hb ha'₁b ha'₁c (p := p₁) rfl rfl,
    s.evalIdeal_eq_of_aux h𝔟0 h𝔟I ha₂ hab₂ hcop.symm hb ha'₂b ha'₂c (p := p₂) rfl rfl]
  exact s.map_mul_fst rfl rfl rfl

/-- Naturality of `evalIdeal` under post-composition with a monoid homomorphism. -/
theorem evalIdeal_comp (s : MennickeSymbol A I C) (φ : C →* D) {a : A} {𝔟 : Ideal A}
    (h𝔟0 : 𝔟 ≠ ⊥) (h𝔟I : 𝔟 ≤ I) (ha : a - 1 ∈ I) (hab : IsCoprime (Ideal.span {a}) 𝔟) :
    (s.comp φ).evalIdeal a 𝔟 h𝔟0 h𝔟I ha hab = φ (s.evalIdeal a 𝔟 h𝔟0 h𝔟I ha hab) := by
  obtain ⟨𝔠, b, _, _, hb, hcop⟩ := exists_aux_ideal_mul_eq_span h𝔟0 h𝔟0
  obtain ⟨a', ha'b, ha'c⟩ := exists_crt_one hcop.symm a
  let p := mkAuxPair h𝔟I ha hab hb ha'b ha'c
  rw [(s.comp φ).evalIdeal_eq_of_aux h𝔟0 h𝔟I ha hab hcop.symm hb ha'b ha'c (p := p) rfl rfl,
    s.evalIdeal_eq_of_aux h𝔟0 h𝔟I ha hab hcop.symm hb ha'b ha'c (p := p) rfl rfl,
    comp_apply]

/-- Naturality of `evalIdeal` under restriction along an ideal inclusion `J ≤ I`. -/
theorem evalIdeal_comapIdeal (hJI : J ≤ I) (s : MennickeSymbol A I C) {a : A} {𝔟 : Ideal A}
    (h𝔟0 : 𝔟 ≠ ⊥) (h𝔟J : 𝔟 ≤ J) (ha : a - 1 ∈ J) (hab : IsCoprime (Ideal.span {a}) 𝔟) :
    (s.comapIdeal hJI).evalIdeal a 𝔟 h𝔟0 h𝔟J ha hab =
      s.evalIdeal a 𝔟 h𝔟0 (h𝔟J.trans hJI) (hJI ha) hab := by
  obtain ⟨𝔠, b, _, _, hb, hcop⟩ := exists_aux_ideal_mul_eq_span h𝔟0 h𝔟0
  obtain ⟨a', ha'b, ha'c⟩ := exists_crt_one hcop.symm a
  let p := mkAuxPair h𝔟J ha hab hb ha'b ha'c
  rw [(s.comapIdeal hJI).evalIdeal_eq_of_aux h𝔟0 h𝔟J ha hab hcop.symm hb ha'b ha'c (p := p) rfl rfl,
    s.evalIdeal_eq_of_aux h𝔟0 (h𝔟J.trans hJI) (hJI ha) hab hcop.symm hb ha'b ha'c
      (p := p.mapIdeal hJI) (by simp [p, mkAuxPair]) (by simp [p, mkAuxPair]),
    comapIdeal_apply]

/-- Any two values of `evalIdeal` commute in an arbitrary (possibly nonabelian) monoid `C`. -/
theorem evalIdeal_commute (s : MennickeSymbol A I C) {a₁ a₂ : A} {𝔟₁ 𝔟₂ : Ideal A}
    (h₁0 : 𝔟₁ ≠ ⊥) (h₂0 : 𝔟₂ ≠ ⊥) (h₁I : 𝔟₁ ≤ I) (h₂I : 𝔟₂ ≤ I)
    (ha₁ : a₁ - 1 ∈ I) (ha₂ : a₂ - 1 ∈ I)
    (hab₁ : IsCoprime (Ideal.span {a₁}) 𝔟₁) (hab₂ : IsCoprime (Ideal.span {a₂}) 𝔟₂) :
    Commute (s.evalIdeal a₁ 𝔟₁ h₁0 h₁I ha₁ hab₁) (s.evalIdeal a₂ 𝔟₂ h₂0 h₂I ha₂ hab₂) := by
  obtain ⟨𝔠₁, b₁, _, _, hb₁, hcop₁⟩ := exists_aux_ideal_mul_eq_span h₁0 h₁0
  obtain ⟨a'₁, ha'₁b, ha'₁c⟩ := exists_crt_one hcop₁.symm a₁
  obtain ⟨𝔠₂, b₂, _, _, hb₂, hcop₂⟩ := exists_aux_ideal_mul_eq_span h₂0 h₂0
  obtain ⟨a'₂, ha'₂b, ha'₂c⟩ := exists_crt_one hcop₂.symm a₂
  let p₁ := mkAuxPair h₁I ha₁ hab₁ hb₁ ha'₁b ha'₁c
  let p₂ := mkAuxPair h₂I ha₂ hab₂ hb₂ ha'₂b ha'₂c
  rw [s.evalIdeal_eq_of_aux h₁0 h₁I ha₁ hab₁ hcop₁.symm hb₁ ha'₁b ha'₁c (p := p₁) rfl rfl,
    s.evalIdeal_eq_of_aux h₂0 h₂I ha₂ hab₂ hcop₂.symm hb₂ ha'₂b ha'₂c (p := p₂) rfl rfl]
  exact s.commute p₁ p₂

/-- Every value of `evalIdeal` in an arbitrary monoid `C` is a unit. -/
theorem evalIdeal_isUnit (s : MennickeSymbol A I C) {a : A} {𝔟 : Ideal A}
    (h𝔟0 : 𝔟 ≠ ⊥) (h𝔟I : 𝔟 ≤ I) (ha : a - 1 ∈ I) (hab : IsCoprime (Ideal.span {a}) 𝔟) :
    IsUnit (s.evalIdeal a 𝔟 h𝔟0 h𝔟I ha hab) := by
  obtain ⟨𝔠, b, _, _, hb, hcop⟩ := exists_aux_ideal_mul_eq_span h𝔟0 h𝔟0
  obtain ⟨a', ha'b, ha'c⟩ := exists_crt_one hcop.symm a
  let p := mkAuxPair h𝔟I ha hab hb ha'b ha'c
  rw [s.evalIdeal_eq_of_aux h𝔟0 h𝔟I ha hab hcop.symm hb ha'b ha'c (p := p) rfl rfl]
  exact s.isUnit p

end MennickeSymbol

end TauCeti
