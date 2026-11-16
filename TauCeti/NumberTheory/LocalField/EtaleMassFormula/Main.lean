/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.EtaleAlgebra
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SplittingSymbol
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.TransitiveMass
import Mathlib.Data.Finset.Powerset

/-!
# Bhargava's mass formulas for étale algebras over a local field

Let `K` be a nonarchimedean local field with residue field of cardinality `q`. This file proves
Bhargava's three mass formulas for finite étale algebras over `K`, formulated in terms of the
labelled Galois sets `TauCeti.GaloisSet K n` and transferred to isomorphism classes of étale
`K`-algebras via `TauCeti.tsum_etaleDiscriminantExponent`:

1. **Fixed splitting symbol** (`TauCeti.etaleMass_splittingSymbol`, [Bhargava 2007, Prop. 2.1]):
   for a multiset `σ` of pairs `(f, e)` of positive integers with `∑ f * e = n`, the Galois sets of
   size `n` with splitting symbol `σ` have mass `1 / (#Aut(σ) * q ^ (∑ f * (e - 1)))`.
2. **Fixed ramification partition** (`TauCeti.etaleMass_ramificationPartition`,
   [Bhargava 2007, Prop. 2.2]): for a partition `π` of `k` into at most `n - k` parts, the Galois
   sets of size `n` whose splitting symbol has ramification partition `π` have mass `1 / q ^ k`.
   In particular, the unramified Galois sets of size `n` (`k = 0`) have total mass `1`
   (`TauCeti.etaleMass_ramificationPartition_eq_zero`).
3. **Total étale mass** (`TauCeti.etaleMass_eq` and `TauCeti.tsum_etaleDiscriminantExponent_eq`,
   [Bhargava 2007, Thm. 1.1 and Prop. 2.3]): `M_n(K) = ∑_{k ≤ n} q(k, n - k) / q ^ k`, where
   `q(k, m)` is the number of partitions of `k` into at most `m` parts. As an illustration,
   `TauCeti.etaleMass_two` evaluates `M_2(K) = 1 + 1 / q`.

To prove `TauCeti.etaleMass_splittingSymbol`, we induct on the number of factors of `σ`. When
`n > 0`, grouping the Galois sets of splitting symbol `σ` by the orbit `B ⊆ Fin n` of label `0` and
its `(f, e)` pair splits each `(x, B)`-fibre along `TauCeti.GaloisSet.sumCongrTransitiveEquiv` into
a product of transitive Galois sets of symbol `{x}` on `B` (evaluated by
`TauCeti.tsum_splittingSymbol_eq_singleton`) and Galois sets of symbol `σ.erase x` on `Bᶜ`. Summing
over the `(n - 1).choose (f * e - 1)` subsets `B` containing `0` and then over the distinct factors
`x ∈ σ.toFinset` yields `n! / (#Aut(σ) * q ^ splittingSymbolExponent σ)`. Summing over the
symbols with a given ramification partition via
`TauCeti.tsum_one_div_splittingSymbolAut_ramificationPartition` gives Proposition 2.2, and summing
over all partitions gives Theorem 1.1.

## Main results

* `TauCeti.tsum_splittingSymbol_eq` and `TauCeti.etaleMass_splittingSymbol`: mass of the Galois sets
  with a prescribed splitting symbol.
* `TauCeti.etaleMass_ramificationPartition` and `TauCeti.etaleMass_ramificationPartition_eq_zero`:
  mass of the Galois sets with a prescribed ramification partition.
* `TauCeti.etaleMass_eq`, `TauCeti.tsum_etaleDiscriminantExponent_eq`, and `TauCeti.etaleMass_two`:
  Bhargava's mass formula for `etaleMass K n` and for isomorphism classes of étale `K`-algebras.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, Theorem 1.1, Propositions 2.1–2.3, and §8.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

open ValuativeRel
open scoped Nat ENNReal

namespace TauCeti

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Mass formula for a fixed splitting symbol -/

section SplittingSymbol

/-- The `(f, e)` pair of the fixed field of the stabilizer of label `i` in `ρ`. -/
private def orbitPair {n : ℕ} (ρ : GaloisSet K n) (i : Fin n) : ℕ × ℕ :=
  letI := ρ.mulAction
  let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i)
  (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)

private theorem orbitPair_mem_splittingSymbol {n : ℕ} (ρ : GaloisSet K n) (i : Fin n) :
    orbitPair ρ i ∈ ρ.splittingSymbol :=
  ρ.mk_inertiaDegree_mem_splittingSymbol i

private theorem orbitPair_mul_eq_card_orbit {n : ℕ} (ρ : GaloisSet K n) (i : Fin n) :
    (orbitPair ρ i).1 * (orbitPair ρ i).2 =
      (letI := ρ.mulAction; Nat.card (MulAction.orbit Gal(SeparableClosure K/K) i)) := by
  let := ρ.mulAction
  dsimp only [orbitPair]
  rw [Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _),
    ρ.finrank_fixedField_stabilizer i]

private theorem orbitPair_sumCongr_inl {m n k : ℕ} (e : Fin m ⊕ Fin n ≃ Fin k)
    (ρ : GaloisSet K m) (τ : GaloisSet K n) (i : Fin m) :
    orbitPair (GaloisSet.sumCongr e ρ τ) (e (Sum.inl i)) = orbitPair ρ i := by
  dsimp only [orbitPair]
  rw [GaloisSet.stabilizer_sumCongr_inl]

private theorem splittingSymbol_of_isTransitive_eq_singleton_orbitPair {n : ℕ}
    (ρ : GaloisSet K n) (hρ : ρ.IsTransitive) (i : Fin n) :
    ρ.splittingSymbol = {orbitPair ρ i} := by
  rw [ρ.splittingSymbol_of_isTransitive hρ i]
  dsimp only [orbitPair]
  rw [ρ.finrank_fixedField_stabilizer_of_isTransitive hρ i]

private theorem splittingSymbol_sumCongr_and_orbitPair_iff {d m n : ℕ}
    (e : Fin d ⊕ Fin m ≃ Fin n) (j₀ : Fin d) (ρ₁ : GaloisSet K d) (hρ₁ : ρ₁.IsTransitive)
    (ρ₂ : GaloisSet K m) {σ : Multiset (ℕ × ℕ)} {x : ℕ × ℕ} (hx : x ∈ σ) :
    (GaloisSet.sumCongr e ρ₁ ρ₂).splittingSymbol = σ ∧
        orbitPair (GaloisSet.sumCongr e ρ₁ ρ₂) (e (Sum.inl j₀)) = x ↔
      ρ₁.splittingSymbol = {x} ∧ ρ₂.splittingSymbol = σ.erase x := by
  have h1 := splittingSymbol_of_isTransitive_eq_singleton_orbitPair ρ₁ hρ₁ j₀
  rw [GaloisSet.splittingSymbol_sumCongr, orbitPair_sumCongr_inl]
  constructor
  · rintro ⟨hsym, rfl⟩
    refine ⟨h1, ?_⟩
    rw [← hsym, h1, Multiset.singleton_add, Multiset.erase_cons_head]
  · rintro ⟨hρ₁x, hρ₂⟩
    have horb : orbitPair ρ₁ j₀ = x := Multiset.singleton_inj.1 (h1.symm.trans hρ₁x)
    rw [hρ₁x, hρ₂, Multiset.singleton_add, Multiset.cons_erase hx]
    exact ⟨rfl, horb⟩

private theorem exists_sumEquiv_of_mem_filter_powersetCard {n d : ℕ} (i₀ : Fin n)
    {B : Finset (Fin n)}
    (hB : B ∈ ((Finset.univ : Finset (Fin n)).powersetCard d).filter ({i₀} ⊆ ·)) :
    d ≤ n ∧ ∃ (e : Fin d ⊕ Fin (n - d) ≃ Fin n) (j₀ : Fin d),
      Set.range (e ∘ Sum.inl) = (B : Set (Fin n)) ∧ e (Sum.inl j₀) = i₀ := by
  classical
  obtain ⟨hBcard, hi₀B⟩ := Finset.mem_filter.1 hB
  have hcard : B.card = d := (Finset.mem_powersetCard.1 hBcard).2
  have hdn : d ≤ n := by simpa [hcard] using B.card_le_univ
  have hi₀ : i₀ ∈ B := Finset.singleton_subset_iff.1 hi₀B
  let e₁ : Fin d ≃ B := (Fintype.equivFinOfCardEq (by simp [hcard])).symm
  let e₂ : Fin (n - d) ≃ (Bᶜ : Finset (Fin n)) :=
    (Fintype.equivFinOfCardEq (by simp [hcard])).symm
  let e : Fin d ⊕ Fin (n - d) ≃ Fin n :=
    { toFun := Sum.elim (fun j ↦ (e₁ j).1) (fun j ↦ (e₂ j).1)
      invFun := fun l ↦ if hl : l ∈ B then Sum.inl (e₁.symm ⟨l, hl⟩)
        else Sum.inr (e₂.symm ⟨l, Finset.mem_compl.2 hl⟩)
      left_inv := by
        rintro (j | j)
        · simp [(e₁ j).2]
        · simp [Finset.mem_compl.1 (e₂ j).2]
      right_inv := fun l ↦ by by_cases hl : l ∈ B <;> simp [hl] }
  refine ⟨hdn, e, e₁.symm ⟨i₀, hi₀⟩, ?_, by simp [e]⟩
  ext l
  simp only [Set.mem_range, Function.comp_apply, SetLike.mem_coe]
  exact ⟨fun ⟨j, hj⟩ ↦ hj ▸ (e₁ j).2, fun hl ↦ ⟨e₁.symm ⟨l, hl⟩, by simp [e]⟩⟩

private def fiberSplittingEquiv {n : ℕ} {σ : Multiset (ℕ × ℕ)} {x : ℕ × ℕ} (hx : x ∈ σ)
    (hxpos : 0 < x.1 ∧ 0 < x.2) (e : Fin (x.1 * x.2) ⊕ Fin (n - x.1 * x.2) ≃ Fin n)
    (j₀ : Fin (x.1 * x.2)) :
    {ρ₁ : GaloisSet K (x.1 * x.2) // ρ₁.splittingSymbol = {x}} ×
      {ρ₂ : GaloisSet K (n - x.1 * x.2) // ρ₂.splittingSymbol = σ.erase x} ≃
      {μ : GaloisSet K n //
        (letI := μ.mulAction
        MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inl j₀)) = Set.range (e ∘ Sum.inl)) ∧
          μ.splittingSymbol = σ ∧ orbitPair μ (e (Sum.inl j₀)) = x} :=
  ({ toFun := fun p ↦
       ⟨(⟨p.1.1, ((GaloisSet.splittingSymbol_eq_singleton_iff hxpos.1 hxpos.2 p.1.1).1 p.1.2).1⟩,
          p.2.1),
        ⟨p.1.2, p.2.2⟩⟩
     invFun := fun p ↦ (⟨p.1.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
     left_inv := fun _ ↦ rfl
     right_inv := fun _ ↦ rfl } :
    {ρ₁ : GaloisSet K (x.1 * x.2) // ρ₁.splittingSymbol = {x}} ×
      {ρ₂ : GaloisSet K (n - x.1 * x.2) // ρ₂.splittingSymbol = σ.erase x} ≃
      {p : {ρ₁ : GaloisSet K (x.1 * x.2) // ρ₁.IsTransitive} × GaloisSet K (n - x.1 * x.2) //
        p.1.1.splittingSymbol = {x} ∧ p.2.splittingSymbol = σ.erase x}).trans <|
    (Equiv.subtypeEquiv (GaloisSet.sumCongrTransitiveEquiv e j₀) fun p ↦ by
      rw [GaloisSet.coe_sumCongrTransitiveEquiv_apply]
      exact (splittingSymbol_sumCongr_and_orbitPair_iff e j₀ p.1.1 p.1.2 p.2 hx).symm).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _)

private theorem coe_fiberSplittingEquiv_apply {n : ℕ} {σ : Multiset (ℕ × ℕ)} {x : ℕ × ℕ}
    (hx : x ∈ σ) (hxpos : 0 < x.1 ∧ 0 < x.2)
    (e : Fin (x.1 * x.2) ⊕ Fin (n - x.1 * x.2) ≃ Fin n) (j₀ : Fin (x.1 * x.2))
    (p : {ρ₁ : GaloisSet K (x.1 * x.2) // ρ₁.splittingSymbol = {x}} ×
      {ρ₂ : GaloisSet K (n - x.1 * x.2) // ρ₂.splittingSymbol = σ.erase x}) :
    (fiberSplittingEquiv hx hxpos e j₀ p).1 = GaloisSet.sumCongr e p.1.1 p.2.1 :=
  GaloisSet.coe_sumCongrTransitiveEquiv_apply e j₀ _

private theorem tsum_fiber_eq {n : ℕ} {σ : Multiset (ℕ × ℕ)} {x : ℕ × ℕ} (hx : x ∈ σ)
    (hxpos : 0 < x.1 ∧ 0 < x.2) (i₀ : Fin n) {B : Finset (Fin n)}
    (hB : B ∈ ((Finset.univ : Finset (Fin n)).powersetCard (x.1 * x.2)).filter ({i₀} ⊆ ·)) :
    (∑' μ : {μ : GaloisSet K n // μ.splittingSymbol = σ ∧ orbitPair μ i₀ = x ∧
        (letI := μ.mulAction
        MulAction.orbit Gal(SeparableClosure K/K) i₀ = (B : Set (Fin n)))},
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ μ.1.discriminantExponent) =
      (∑' ρ₁ : {ρ₁ : GaloisSet K (x.1 * x.2) // ρ₁.splittingSymbol = {x}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
        ∑' ρ₂ : {ρ₂ : GaloisSet K (n - x.1 * x.2) // ρ₂.splittingSymbol = σ.erase x},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent := by
  obtain ⟨-, e, j₀, hrange, hj₀⟩ := exists_sumEquiv_of_mem_filter_powersetCard i₀ hB
  let E := (fiberSplittingEquiv (K := K) hx hxpos e j₀).trans <|
    Equiv.subtypeEquivRight
      (q := fun μ ↦ μ.splittingSymbol = σ ∧ orbitPair μ i₀ = x ∧
        (letI := μ.mulAction
        MulAction.orbit Gal(SeparableClosure K/K) i₀ = (B : Set (Fin n))))
      fun μ ↦ by
        rw [hj₀, hrange]
        exact and_comm.trans and_assoc
  rw [← E.tsum_eq]
  have hmul : ∀ p : {ρ₁ : GaloisSet K (x.1 * x.2) // ρ₁.splittingSymbol = {x}} ×
      {ρ₂ : GaloisSet K (n - x.1 * x.2) // ρ₂.splittingSymbol = σ.erase x},
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (E p).1.discriminantExponent =
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ p.1.1.discriminantExponent) *
          (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ p.2.1.discriminantExponent) := fun p ↦ by
    have hE : (E p).1 = GaloisSet.sumCongr e p.1.1 p.2.1 :=
      coe_fiberSplittingEquiv_apply hx hxpos e j₀ p
    have htop₁ : ((Nat.card 𝓀[K] : ℝ≥0∞) ^ p.1.1.discriminantExponent) ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    have htop₂ : ((Nat.card 𝓀[K] : ℝ≥0∞) ^ p.2.1.discriminantExponent) ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    rw [hE, GaloisSet.discriminantExponent_sumCongr, pow_add, one_div, one_div, one_div,
      ENNReal.mul_inv (Or.inr htop₂) (Or.inl htop₁)]
  rw [tsum_congr hmul, tsum_prod']
  simp_rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]

private theorem choose_factorial_num {n : ℕ} {σ : Multiset (ℕ × ℕ)} {x : ℕ × ℕ}
    (hxpos : 0 < x.1 ∧ 0 < x.2) (hdn : x.1 * x.2 ≤ n) :
    (n - 1).choose (x.1 * x.2 - 1) * ((x.1 * x.2 - 1)! * x.2) * (n - x.1 * x.2)! *
        (x.1 * σ.count x) =
      (n - 1)! * (σ.count x * (x.1 * x.2)) := by
  set d := x.1 * x.2
  have hd_pos : 0 < d := Nat.mul_pos hxpos.1 hxpos.2
  have hsub : n - 1 - (d - 1) = n - d := by omega
  have hchoose : (n - 1).choose (d - 1) * (d - 1)! * (n - d)! = (n - 1)! :=
    hsub ▸ Nat.choose_mul_factorial_mul_factorial (by omega)
  calc (n - 1).choose (d - 1) * ((d - 1)! * x.2) * (n - d)! * (x.1 * σ.count x)
      = ((n - 1).choose (d - 1) * (d - 1)! * (n - d)!) * (σ.count x * (x.1 * x.2)) := by ring
    _ = (n - 1)! * (σ.count x * d) := by rw [hchoose]

private theorem nat_mul_erase_formula {n : ℕ} {σ : Multiset (ℕ × ℕ)} {x : ℕ × ℕ} (hx : x ∈ σ)
    (hxpos : 0 < x.1 ∧ 0 < x.2) (hdn : x.1 * x.2 ≤ n) (q : ℝ≥0∞) (hq : q ≠ ⊤) :
    ((n - 1).choose (x.1 * x.2 - 1) : ℝ≥0∞) *
        ((((x.1 * x.2 - 1)! : ℝ≥0∞) * (x.2 : ℝ≥0∞) / q ^ (x.1 * (x.2 - 1))) *
          (((n - x.1 * x.2)! : ℝ≥0∞) /
            ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
              q ^ splittingSymbolExponent (σ.erase x)))) =
      (((n - 1)! * (σ.count x * (x.1 * x.2)) : ℕ) : ℝ≥0∞) /
        ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ) := by
  set d := x.1 * x.2
  have hc : ((x.1 * σ.count x : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.mul_pos hxpos.1 (Multiset.count_pos.2 hx)).ne'
  have hctop : ((x.1 * σ.count x : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hden_top₁ : q ^ (x.1 * (x.2 - 1)) ≠ ⊤ := ENNReal.pow_ne_top hq
  have hden_top₂ : (splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
      q ^ splittingSymbolExponent (σ.erase x) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.pow_ne_top hq)
  have hden_eq : ((x.1 * σ.count x : ℕ) : ℝ≥0∞) *
      (q ^ (x.1 * (x.2 - 1)) * ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
        q ^ splittingSymbolExponent (σ.erase x))) =
      (splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ := by
    have hexp : x.1 * (x.2 - 1) + splittingSymbolExponent (σ.erase x) =
        splittingSymbolExponent σ := by
      rw [← splittingSymbolExponent_cons, Multiset.cons_erase hx]
    rw [← splittingSymbolAut_erase_mul hx, ← hexp, pow_add]
    push_cast; ring
  simp only [div_eq_mul_inv]
  calc ((n - 1).choose (d - 1) : ℝ≥0∞) *
        (((d - 1)! * x.2 * (q ^ (x.1 * (x.2 - 1)))⁻¹) *
          ((n - d)! * ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
            q ^ splittingSymbolExponent (σ.erase x))⁻¹))
      = (((n - 1).choose (d - 1) : ℝ≥0∞) * ((d - 1)! * x.2) * (n - d)!) *
          (((x.1 * σ.count x : ℕ) : ℝ≥0∞) * ((x.1 * σ.count x : ℕ) : ℝ≥0∞)⁻¹) *
          ((q ^ (x.1 * (x.2 - 1)))⁻¹ * ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
            q ^ splittingSymbolExponent (σ.erase x))⁻¹) := by
          rw [ENNReal.mul_inv_cancel hc hctop, mul_one]; ring
    _ = (((n - 1).choose (d - 1) : ℝ≥0∞) * ((d - 1)! * x.2) * (n - d)! *
          ((x.1 * σ.count x : ℕ) : ℝ≥0∞)) *
          (((x.1 * σ.count x : ℕ) : ℝ≥0∞)⁻¹ *
            ((q ^ (x.1 * (x.2 - 1)))⁻¹ * ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
              q ^ splittingSymbolExponent (σ.erase x))⁻¹)) := by ring
    _ = ((((n - 1).choose (d - 1) * ((d - 1)! * x.2) * (n - d)! * (x.1 * σ.count x) : ℕ) :
          ℝ≥0∞)) * (((x.1 * σ.count x : ℕ) : ℝ≥0∞) * (q ^ (x.1 * (x.2 - 1)) *
            ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
              q ^ splittingSymbolExponent (σ.erase x))))⁻¹ := by
          rw [← ENNReal.mul_inv (Or.inr hden_top₂) (Or.inl hden_top₁),
            ← ENNReal.mul_inv (Or.inl hc) (Or.inl hctop)]
          push_cast; rfl
    _ = (((n - 1)! * (σ.count x * d) : ℕ) : ℝ≥0∞) *
          ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ)⁻¹ := by
          rw [choose_factorial_num hxpos hdn, hden_eq]

private def orbitFinset {n : ℕ} (ρ : GaloisSet K n) (i : Fin n) : Finset (Fin n) :=
  letI := ρ.mulAction
  haveI := Fintype.ofFinite (MulAction.orbit Gal(SeparableClosure K/K) i)
  (MulAction.orbit Gal(SeparableClosure K/K) i).toFinset

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem coe_orbitFinset {n : ℕ} (ρ : GaloisSet K n) (i : Fin n) :
    (orbitFinset ρ i : Set (Fin n)) =
      (letI := ρ.mulAction; MulAction.orbit Gal(SeparableClosure K/K) i) := by
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbit Gal(SeparableClosure K/K) i)
  exact Set.coe_toFinset _

private theorem card_orbitFinset {n : ℕ} (ρ : GaloisSet K n) (i : Fin n) :
    (orbitFinset ρ i).card = (orbitPair ρ i).1 * (orbitPair ρ i).2 := by
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbit Gal(SeparableClosure K/K) i)
  rw [orbitFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card, orbitPair_mul_eq_card_orbit]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem mem_orbitFinset_self {n : ℕ} (ρ : GaloisSet K n) (i : Fin n) :
    i ∈ orbitFinset ρ i := by
  let := ρ.mulAction
  rw [← Finset.mem_coe, coe_orbitFinset]
  exact MulAction.mem_orbit_self i

private theorem tsum_fiber_x_eq {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hn : (σ.map fun x ↦ x.1 * x.2).sum = n)
    (i₀ : Fin n) {x : ℕ × ℕ} (hx : x ∈ σ)
    (ih : ∑' ρ₂ : {ρ₂ : GaloisSet K (n - x.1 * x.2) // ρ₂.splittingSymbol = σ.erase x},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent =
      ((n - x.1 * x.2)! : ℝ≥0∞) /
        ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent (σ.erase x))) :
    (∑' μ : {μ : GaloisSet K n // μ.splittingSymbol = σ ∧ orbitPair μ i₀ = x},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ μ.1.discriminantExponent) =
      (((n - 1)! * (σ.count x * (x.1 * x.2)) : ℕ) : ℝ≥0∞) /
        ((splittingSymbolAut σ : ℝ≥0∞) *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ) := by
  classical
  have hxpos := hσ x hx
  set d := x.1 * x.2
  have hd_pos : 0 < d := Nat.mul_pos hxpos.1 hxpos.2
  have hdn : d ≤ n := by
    rw [← hn, ← Multiset.cons_erase hx, Multiset.map_cons, Multiset.sum_cons]
    exact Nat.le_add_right _ _
  set Fset : Finset (Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powersetCard d).filter ({i₀} ⊆ ·)
  let Φ : {μ : GaloisSet K n // μ.splittingSymbol = σ ∧ orbitPair μ i₀ = x} → Fset := fun μ ↦
    ⟨orbitFinset μ.1 i₀, Finset.mem_filter.2
      ⟨Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, by rw [card_orbitFinset, μ.2.2]⟩,
      Finset.singleton_subset_iff.2 (mem_orbitFinset_self μ.1 i₀)⟩⟩
  rw [← tsum_fiberwise _ Φ, tsum_fintype]
  have hfib : ∀ B : Fset,
      (∑' μ : Φ ⁻¹' {B}, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ μ.1.1.discriminantExponent) =
        (((x.1 * x.2 - 1)! : ℝ≥0∞) * (x.2 : ℝ≥0∞) /
            (Nat.card 𝓀[K] : ℝ≥0∞) ^ (x.1 * (x.2 - 1))) *
          (((n - x.1 * x.2)! : ℝ≥0∞) /
            ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
              (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent (σ.erase x))) := fun B ↦ by
    let EB : Φ ⁻¹' {B} ≃ {μ : GaloisSet K n // μ.splittingSymbol = σ ∧ orbitPair μ i₀ = x ∧
        (letI := μ.mulAction
        MulAction.orbit Gal(SeparableClosure K/K) i₀ = (B.1 : Set (Fin n)))} :=
      { toFun := fun ⟨μ, hμ⟩ ↦ ⟨μ.1, μ.2.1, μ.2.2, by
          rw [← coe_orbitFinset]
          exact congrArg (fun C : Fset ↦ (C.1 : Set (Fin n))) (Set.mem_singleton_iff.1 hμ)⟩
        invFun := fun μ ↦ ⟨⟨μ.1, μ.2.1, μ.2.2.1⟩, Set.mem_singleton_iff.2 <| Subtype.ext <|
          Finset.coe_inj.1 <| by simpa [Φ, coe_orbitFinset] using μ.2.2.2⟩
        left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }
    have hval : ∀ μ, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (EB.symm μ).1.1.discriminantExponent =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ μ.1.discriminantExponent := fun _ ↦ rfl
    rw [← EB.symm.tsum_eq, tsum_congr hval, tsum_fiber_eq hx hxpos i₀ B.2,
      tsum_splittingSymbol_eq_singleton hxpos.1 hxpos.2, ih]
  simp_rw [hfib]
  have hcard : Fintype.card Fset = (n - 1).choose (d - 1) := by
    rw [Fintype.card_coe, Finset.card_filter_powersetCard_subset ({i₀}) Finset.univ d
      (Finset.subset_univ _) (by simpa using Nat.succ_le_of_lt hd_pos)]
    simp
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  exact nat_mul_erase_formula hx hxpos hdn (Nat.card 𝓀[K] : ℝ≥0∞) (ENNReal.natCast_ne_top _)

private theorem sum_factorial_pred_mul_count {n : ℕ} (hn_pos : 0 < n) {σ : Multiset (ℕ × ℕ)}
    (hn : (σ.map fun x ↦ x.1 * x.2).sum = n) :
    (∑ x ∈ σ.toFinset, (n - 1)! * (σ.count x * (x.1 * x.2))) = n ! := by
  rw [← Finset.mul_sum]
  have hcnt := Finset.sum_multiset_map_count σ (fun x ↦ x.1 * x.2)
  simp only [smul_eq_mul] at hcnt
  rw [← hcnt, hn, mul_comm, Nat.mul_factorial_pred hn_pos.ne']

private theorem tsum_splittingSymbol_aux :
    ∀ (m n : ℕ) (σ : Multiset (ℕ × ℕ)), Multiset.card σ = m →
      (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) → (σ.map fun x ↦ x.1 * x.2).sum = n →
      ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
        (n ! : ℝ≥0∞) / ((splittingSymbolAut σ : ℝ≥0∞) *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ)
  | 0, n, σ, hcard, _, hn => by
      have hσ0 := Multiset.card_eq_zero.1 hcard; subst hσ0
      simp only [Multiset.map_zero, Multiset.sum_zero] at hn; subst hn
      rw [tsum_eq_single ⟨GaloisSet.trivial K 0, by simp⟩
        fun ρ hρ ↦ (hρ (Subtype.ext (Subsingleton.elim _ _))).elim]
      simp
  | m + 1, n, σ, hcard, hσ, hn => by
      classical
      obtain ⟨x₀, hx₀⟩ :=
        Multiset.exists_mem_of_ne_zero ((Multiset.card_pos (s := σ)).1 (by omega))
      have hn_pos : 0 < n := by
        have := Nat.mul_pos (hσ x₀ hx₀).1 (hσ x₀ hx₀).2
        rw [← hn, ← Multiset.cons_erase hx₀, Multiset.map_cons, Multiset.sum_cons]; omega
      let i₀ : Fin n := ⟨0, hn_pos⟩
      let Ψ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ} → σ.toFinset := fun ⟨ρ, hρ⟩ ↦
        ⟨orbitPair ρ i₀, Multiset.mem_toFinset.2 (hρ ▸ orbitPair_mem_splittingSymbol ρ i₀)⟩
      rw [← tsum_fiberwise _ Ψ, tsum_fintype]
      have hterm : ∀ b : σ.toFinset,
          (∑' ρ : Ψ ⁻¹' {b}, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.1.discriminantExponent) =
            (((n - 1)! * (σ.count b.1 * (b.1.1 * b.1.2)) : ℕ) : ℝ≥0∞) /
              ((splittingSymbolAut σ : ℝ≥0∞) *
                (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ) := fun ⟨x, hxfin⟩ ↦ by
        have hx : x ∈ σ := Multiset.mem_toFinset.1 hxfin
        let EX : Ψ ⁻¹' {⟨x, hxfin⟩} ≃
            {μ : GaloisSet K n // μ.splittingSymbol = σ ∧ orbitPair μ i₀ = x} :=
          { toFun := fun ⟨ρ, hρ⟩ ↦ ⟨ρ.1, ρ.2, Subtype.mk.inj (Set.mem_singleton_iff.1 hρ)⟩
            invFun := fun μ ↦ ⟨⟨μ.1, μ.2.1⟩, Set.mem_singleton_iff.2 (Subtype.ext μ.2.2)⟩
            left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }
        have hcard_erase : Multiset.card (σ.erase x) = m :=
          Nat.add_right_cancel (by rw [← Multiset.card_cons x, Multiset.cons_erase hx, hcard])
        have hsum : x.1 * x.2 + ((σ.erase x).map fun y ↦ y.1 * y.2).sum = n := by
          simpa using (congrArg (fun s ↦ (s.map fun y : ℕ × ℕ ↦ y.1 * y.2).sum)
            (Multiset.cons_erase hx)).trans hn
        have ih := tsum_splittingSymbol_aux m (n - x.1 * x.2) (σ.erase x) hcard_erase
          (fun y hy ↦ hσ y (Multiset.mem_of_mem_erase hy)) (by omega)
        have hval : ∀ μ, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (EX.symm μ).1.1.discriminantExponent =
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ μ.1.discriminantExponent := fun _ ↦ rfl
        rw [← EX.symm.tsum_eq, tsum_congr hval]
        exact tsum_fiber_x_eq hσ hn i₀ hx ih
      rw [Finset.sum_congr rfl fun b _ ↦ hterm b,
        Finset.sum_coe_sort σ.toFinset fun x ↦
          (((n - 1)! * (σ.count x * (x.1 * x.2)) : ℕ) : ℝ≥0∞) /
            ((splittingSymbolAut σ : ℝ≥0∞) *
              (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ)]
      simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum,
        sum_factorial_pred_mul_count hn_pos hn]

/-- Summed over the labelled Galois sets of size `n` with splitting symbol `σ`, the weights
`q ^ (-d(ρ))` total `n! / (#Aut(σ) * q ^ splittingSymbolExponent σ)`. -/
theorem tsum_splittingSymbol_eq (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hn : (σ.map fun x ↦ x.1 * x.2).sum = n) :
    ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      (n ! : ℝ≥0∞) / ((splittingSymbolAut σ : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ) :=
  tsum_splittingSymbol_aux (Multiset.card σ) n σ rfl hσ hn

/-- **Mass formula for a fixed splitting symbol** ([Bhargava 2007, Prop. 2.1]): for a splitting
symbol `σ` of degree `n` (a multiset of pairs `(f, e)` of positive integers with `∑ f * e = n`),
the labelled Galois sets of size `n` with splitting symbol `σ` have mass
`1 / (#Aut(σ) * q ^ splittingSymbolExponent σ)`. -/
theorem etaleMass_splittingSymbol (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hn : (σ.map fun x ↦ x.1 * x.2).sum = n) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((splittingSymbolAut σ : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ) := by
  rw [tsum_splittingSymbol_eq n σ hσ hn, div_eq_mul_inv, ← mul_assoc,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n))
      (ENNReal.natCast_ne_top _),
    one_mul, one_div]

end SplittingSymbol

/-! ### Mass formula for a fixed ramification partition -/

/-- **Mass formula for a fixed ramification partition** ([Bhargava 2007, Prop. 2.2]): for a
partition `π` of `k` into at most `n - k` parts, the labelled Galois sets of size `n` whose
splitting symbol has ramification partition `π` have mass `1 / q ^ k`. -/
theorem etaleMass_ramificationPartition (n k : ℕ) (π : k.Partition)
    (hπ : Multiset.card π.parts ≤ n - k) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  let S := {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) ∧
    (σ.map fun x ↦ x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts}
  let Ψ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} → S :=
    fun ρ ↦ ⟨ρ.1.splittingSymbol,
      ⟨fun _ hx ↦ GaloisSet.pos_of_mem_splittingSymbol hx,
        ρ.1.sum_map_mul_splittingSymbol, ρ.2⟩⟩
  rw [← tsum_fiberwise _ Ψ, ← ENNReal.tsum_mul_left]
  have hfib : ∀ σ : S,
      (n ! : ℝ≥0∞)⁻¹ *
          (∑' ρ : Ψ ⁻¹' {σ}, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.1.discriminantExponent) =
        (1 / (splittingSymbolAut σ.1 : ℝ≥0∞)) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k) := fun σ ↦ by
    let Eσ : Ψ ⁻¹' {σ} ≃ {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1} :=
      { toFun := fun ⟨ρ, hρ⟩ ↦ ⟨ρ.1, Subtype.mk.inj (Set.mem_singleton_iff.1 hρ)⟩
        invFun := fun ρ ↦ ⟨⟨ρ.1, ρ.2.symm ▸ σ.2.2.2⟩, Set.mem_singleton_iff.2 (Subtype.ext ρ.2)⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hexp : splittingSymbolExponent σ.1 = k := by
      rw [← sum_ramificationPartition_eq_splittingSymbolExponent, σ.2.2.2, π.parts_sum]
    have htop₁ : (splittingSymbolAut σ.1 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have htop₂ : ((Nat.card 𝓀[K] : ℝ≥0∞) ^ k) ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    rw [← Eσ.symm.tsum_eq]
    have hval : ∀ ρ, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (Eσ.symm ρ).1.1.discriminantExponent =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent := fun _ ↦ rfl
    rw [tsum_congr hval, etaleMass_splittingSymbol n σ.1 σ.2.1 σ.2.2.1, hexp,
      one_div, one_div, one_div, ENNReal.mul_inv (Or.inr htop₂) (Or.inl htop₁)]
  rw [tsum_congr hfib, ENNReal.tsum_mul_right,
    tsum_one_div_splittingSymbolAut_ramificationPartition n k π hπ, one_mul]

/-- The unramified labelled Galois sets of size `n` (those whose splitting symbol has empty
ramification partition) have total mass `1` ([Bhargava 2007, (2.4)]). -/
theorem etaleMass_ramificationPartition_eq_zero (n : ℕ) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = 0},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent = 1 := by
  have hparts : (default : Nat.Partition 0).parts = 0 := by simp
  rw [← hparts]
  simpa using etaleMass_ramificationPartition (K := K) n 0 default (by simp)

/-! ### Bhargava's mass formula -/

private theorem tsum_admissibleMultiset_eq (n : ℕ) (q : ℝ≥0∞) :
    (∑' P : {P : Multiset ℕ // (∀ t ∈ P, 0 < t) ∧ P.sum ≤ n ∧ Multiset.card P ≤ n - P.sum},
        1 / q ^ P.1.sum) =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π ↦ Multiset.card π.parts ≤ n - k).card :
            ℝ≥0∞) / q ^ k := by
  let Adm := {P : Multiset ℕ // (∀ t ∈ P, 0 < t) ∧ P.sum ≤ n ∧ Multiset.card P ≤ n - P.sum}
  rw [← tsum_fiberwise _ (fun P : Adm ↦ P.1.sum),
    tsum_eq_sum (s := Finset.range (n + 1)) fun k hk ↦ by
      have hkn : ¬ k ≤ n := fun hle ↦ hk (Finset.mem_range.2 (Nat.lt_succ_of_le hle))
      have : IsEmpty ((fun P : Adm ↦ P.1.sum) ⁻¹' {k}) :=
        ⟨fun ⟨P, hP⟩ ↦ hkn ((Set.mem_singleton_iff.1 hP) ▸ P.2.2.1)⟩
      exact tsum_empty]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hk)
  let Ek : (fun P : Adm ↦ P.1.sum) ⁻¹' {k} ≃
      {π : k.Partition // Multiset.card π.parts ≤ n - k} :=
    { toFun := fun ⟨P, hP⟩ ↦
        let hPk : P.1.sum = k := Set.mem_singleton_iff.1 hP
        ⟨{ parts := P.1, parts_pos := fun ht ↦ P.2.1 _ ht, parts_sum := hPk },
          by dsimp only; rw [← hPk]; exact P.2.2.2⟩
      invFun := fun π ↦
        ⟨⟨π.1.parts, ⟨fun _ ht ↦ π.1.parts_pos ht,
          by rw [π.1.parts_sum]; exact hkle,
          by rw [π.1.parts_sum]; exact π.2⟩⟩, Set.mem_singleton_iff.2 π.1.parts_sum⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ Subtype.ext (Nat.Partition.ext rfl) }
  rw [← Ek.symm.tsum_eq]
  have hconst : ∀ π : {π : k.Partition // Multiset.card π.parts ≤ n - k},
      1 / q ^ (Ek.symm π).1.1.sum = 1 / q ^ k := fun π ↦ by
    have hEq : (Ek.symm π).1.1 = π.1.parts := rfl
    rw [hEq, π.1.parts_sum]
  rw [tsum_congr hconst, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_subtype,
    nsmul_eq_mul, mul_one_div]

variable (K) in
/-- **Bhargava's mass formula** ([Bhargava 2007, Thm. 1.1, Prop. 2.3, and §8]): for any
nonarchimedean local field `K` with residue field of cardinality `q`, the étale mass of degree `n`
is `∑_{k ≤ n} q(k, n - k) / q ^ k`, where `q(k, m)` is the number of partitions of `k` into at most
`m` parts. For `n > 0` the `k = n` summand vanishes (`q(n, 0) = 0`), matching Bhargava's
`∑_{k < n}`; at `n = 0` both sides equal `1`. -/
theorem etaleMass_eq (n : ℕ) :
    etaleMass K n =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π ↦ Multiset.card π.parts ≤ n - k).card :
            ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  let Adm := {P : Multiset ℕ // (∀ t ∈ P, 0 < t) ∧ P.sum ≤ n ∧ Multiset.card P ≤ n - P.sum}
  let Ξ : GaloisSet K n → Adm := fun ρ ↦
    ⟨ramificationPartition ρ.splittingSymbol, by
      have hdeg := sum_map_mul_eq_sum_ramificationPartition_add ρ.splittingSymbol
        fun _ hx ↦ (GaloisSet.pos_of_mem_splittingSymbol hx).2
      rw [ρ.sum_map_mul_splittingSymbol] at hdeg
      refine ⟨fun t ht ↦ Nat.pos_of_ne_zero (mem_ramificationPartition.1 ht).1,
        by omega, by omega⟩⟩
  rw [etaleMass_def, ← tsum_fiberwise _ Ξ, ← ENNReal.tsum_mul_left]
  have hfib : ∀ P : Adm,
      (n ! : ℝ≥0∞)⁻¹ *
          (∑' ρ : Ξ ⁻¹' {P}, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent) =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ P.1.sum := fun P ↦ by
    let π : P.1.sum.Partition :=
      { parts := P.1, parts_pos := fun ht ↦ P.2.1 _ ht, parts_sum := rfl }
    let EP : Ξ ⁻¹' {P} ≃ {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} :=
      Equiv.subtypeEquivRight fun ρ ↦ Subtype.ext_iff
    rw [← EP.symm.tsum_eq]
    exact etaleMass_ramificationPartition n P.1.sum π P.2.2.2
  rw [tsum_congr hfib]
  exact tsum_admissibleMultiset_eq n (Nat.card 𝓀[K] : ℝ≥0∞)

variable (K) in
/-- **Bhargava's mass formula for étale algebras** ([Bhargava 2007, Thm. 1.1 and §8]): for a
family `A` of étale `K`-algebras of degree `n` containing one representative of each
`K`-isomorphism class,
`∑ 1 / (#Aut_K(A i) * q ^ d(A i)) = ∑_{k ≤ n} q(k, n - k) / q ^ k`. -/
theorem tsum_etaleDiscriminantExponent_eq (n : ℕ) {ι : Type*} (A : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, Algebra.Etale K (A i)]
    (hdeg : ∀ i, Module.finrank K (A i) = n)
    (hinj : ∀ i j, Nonempty (A i ≃ₐ[K] A j) → i = j)
    (hsurj : ∀ (B : Type u) [CommRing B] [Algebra K B] [Algebra.Etale K B],
      Module.finrank K B = n → ∃ i, Nonempty (B ≃ₐ[K] A i)) :
    ∑' i, 1 / ((Nat.card (A i ≃ₐ[K] A i) : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ etaleDiscriminantExponent K (A i)) =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π ↦ Multiset.card π.parts ≤ n - k).card :
            ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k :=
  (tsum_etaleDiscriminantExponent K n A hdeg hinj hsurj).trans (etaleMass_eq K n)

variable (K) in
/-- In degree `2`, the étale mass of `K` is `1 + 1 / q`, accounting for the two unramified étale
algebras (`K × K` and the quadratic unramified field, of total mass `1 / 2 + 1 / 2 = 1`) and the
ramified quadratic extensions (of total mass `1 / q`). -/
theorem etaleMass_two :
    etaleMass K 2 = 1 + 1 / (Nat.card 𝓀[K] : ℝ≥0∞) := by
  rw [etaleMass_eq K 2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 :
      (((Finset.univ : Finset (Nat.Partition 0)).filter
          fun π ↦ Multiset.card π.parts ≤ 2 - 0).card : ℝ≥0∞) = 1 := by
    simp
  have h1 :
      (((Finset.univ : Finset (Nat.Partition 1)).filter
          fun π ↦ Multiset.card π.parts ≤ 2 - 1).card : ℝ≥0∞) = 1 := by
    simp
  have h2 :
      ((Finset.univ : Finset (Nat.Partition 2)).filter
        fun π ↦ Multiset.card π.parts ≤ 2 - 2) = ∅ := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      Nat.sub_self, le_zero_iff, Multiset.card_eq_zero]
    intro hparts
    have hsum := π.parts_sum
    rw [hparts, Multiset.sum_zero] at hsum
    omega
  rw [h0, h1, h2]
  simp

end TauCeti
