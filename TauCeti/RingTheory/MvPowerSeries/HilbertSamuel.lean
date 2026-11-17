/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import TauCeti.RingTheory.LocalRing.HilbertSamuel
public import TauCeti.RingTheory.MvPowerSeries.InitialDiagram

import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.NatCard
import Mathlib.RingTheory.LocalRing.Length
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient
import TauCeti.RingTheory.MvPowerSeries.FormalDivision
import TauCeti.RingTheory.MvPowerSeries.Ideal

/-!
# Hilbert–Samuel functions and lexicographic stabilization for formal power series

For an ideal `I` of a finite-variable formal power series ring `K⟦X_i : i ∈ σ⟧` over a field `K`,
the graded-lexicographic initial diagram `D(I) = MonomialOrder.degLex.initialDiagram I` determines
the Hilbert–Samuel function of `K⟦X⟧ ⧸ I` completely:
`H_I(ℓ) = #{α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D(I)}`.
In particular, for `I = ⊥` we obtain the binomial count
`H(ℓ) = Nat.choose (Nat.card σ + ℓ) (Nat.card σ)`, and for a monomial ideal `I = (X^α : α ∈ S)`
the count avoids all exponent cones above `S`.

Using Dickson's lemma for the componentwise order on `σ →₀ ℕ`, we prove the combinatorial
stabilization theorem for upper sets (Bierstone–Milman 1989, Theorem 5.2.1): there is no strictly
lexicographically decreasing sequence of complement-count functions `ℓ ↦ #{|α| ≤ ℓ, α ∉ D_j}` of
upper sets `D_j ⊆ σ →₀ ℕ`. Consequently, every lexicographically nonincreasing sequence of
Hilbert–Samuel functions realized by ideals in a fixed finite-variable power series ring
`K⟦X_i : i ∈ σ⟧` is eventually constant (`TauCeti.hsLexStabilization_of_finite`,
`TauCeti.hsLexStabilization`), and in particular every pointwise nonincreasing such sequence
stabilizes (`TauCeti.hsPointwiseStabilization`).

## Main results

* `Finsupp.ncard_degree_le`:
  `#{α : σ →₀ ℕ | α.degree ≤ ℓ} = Nat.choose (Nat.card σ + ℓ) (Nat.card σ)`.
* `MonomialOrder.degLex_initialDiagram_sup_maximalIdeal_pow`:
  `D(I ⊔ 𝔪 ^ n) = D(I) ∪ {α | n ≤ α.degree}`.
* `MvPowerSeries.length_eq_length_base`: for any `MvPowerSeries σ K`-module `M`, its length over
  `MvPowerSeries σ K` equals its `K`-length.
* `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_eq_ncard`:
  `H_I(ℓ) = #{α | α.degree ≤ ℓ ∧ α ∉ D(I)}`.
* `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_bot`,
  `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_span_monomial`, and
  `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_span_X_pow`: explicit formulas for the zero
  ideal, monomial ideals, and `K⟦x⟧ ⧸ (x ^ k)`.
* `TauCeti.not_strictAnti_toLex_ncard_degree_le_compl` and
  `TauCeti.eventually_const_ncard_degree_le_compl_of_lex_antitone`: combinatorial lexicographic
  stabilization for sequences of upper sets in `σ →₀ ℕ`.
* `TauCeti.hsLexStabilization_of_finite`, `TauCeti.hsLexStabilization`, and
  `TauCeti.hsPointwiseStabilization`: lexicographic and pointwise stabilization of realized
  Hilbert–Samuel functions in `MvPowerSeries σ K`.

## References

* E. Bierstone and P. D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc. **2**
  (1989), 801–836, Theorem 5.2.1.
* E. Bierstone and P. D. Milman, *Canonical desingularization in characteristic zero by blowing
  up the maximum strata of a local invariant*, Invent. Math. **128** (1997), 207–302,
  Corollary 3.20.
* E. Bierstone, P. D. Milman, and M. Temkin, *Q-universal desingularization* (2009), §6.1.
-/

public section

open IsLocalRing

section DegreeLeCount

/-- Splitting an exponent on `Option σ` into its `some`-part and its `none`-coordinate. -/
private theorem finsupp_option_eq_mapDomain_add_single {σ : Type*} (P : Option σ →₀ ℕ) :
    P = Finsupp.mapDomain some (P.comapDomain some (Option.some_injective σ).injOn) +
      Finsupp.single none (P none) := by
  ext x
  cases x with
  | none => simp [Finsupp.mapDomain_of_notMem_range]
  | some i => simp [Finsupp.mapDomain_apply_of_injective (Option.some_injective σ)]

/-- Auxiliary bijection between exponents `α : σ →₀ ℕ` of total degree at most `ℓ` and exponents
`P : Option σ →₀ ℕ` of exact total degree `ℓ`, placing the slack `ℓ - α.degree` at `none`. -/
private noncomputable def finsEquivOptionDegreeEq (σ : Type*) (ℓ : ℕ) :
    ↥{α : σ →₀ ℕ | α.degree ≤ ℓ} ≃ {P : Option σ →₀ ℕ // P.sum (fun _ ↦ id) = ℓ} where
  toFun α :=
    ⟨Finsupp.mapDomain some α.1 + Finsupp.single none (ℓ - α.1.degree), by
      have hdeg :
          (Finsupp.mapDomain some α.1 + Finsupp.single none (ℓ - α.1.degree)).degree = ℓ := by
        rw [map_add, Finsupp.degree_mapDomain, Finsupp.degree_single, Nat.add_sub_of_le α.2]
      exact hdeg⟩
  invFun P :=
    ⟨P.1.comapDomain some (Option.some_injective σ).injOn, by
      have hdeg : P.1.degree =
          (P.1.comapDomain some (Option.some_injective σ).injOn).degree + P.1 none := by
        conv_lhs => rw [finsupp_option_eq_mapDomain_add_single P.1]
        rw [map_add, Finsupp.degree_mapDomain, Finsupp.degree_single]
      have hP : P.1.degree = ℓ := P.2
      change (P.1.comapDomain some (Option.some_injective σ).injOn).degree ≤ ℓ
      omega⟩
  left_inv α := by
    ext i
    simp [Finsupp.mapDomain_apply_of_injective (Option.some_injective σ)]
  right_inv P := by
    ext x
    have hdeg :
        (P.1.comapDomain some (Option.some_injective σ).injOn).degree + P.1 none = ℓ := by
      calc (P.1.comapDomain some (Option.some_injective σ).injOn).degree + P.1 none
          = (Finsupp.mapDomain some (P.1.comapDomain some (Option.some_injective σ).injOn) +
              Finsupp.single none (P.1 none)).degree := by
            rw [map_add, Finsupp.degree_mapDomain, Finsupp.degree_single]
        _ = P.1.degree := by rw [← finsupp_option_eq_mapDomain_add_single P.1]
        _ = ℓ := P.2
    cases x with
    | none =>
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
        Finsupp.mapDomain_of_notMem_range (f := some) _ none (by simp), zero_add]
      omega
    | some i =>
      simp [Finsupp.mapDomain_apply_of_injective (Option.some_injective σ)]

namespace Finsupp

/-- **Stars and bars for `Finsupp.degree`**: over a finite variable type `σ`, the number of
exponents `α : σ →₀ ℕ` of total degree at most `ℓ` is `Nat.choose (Nat.card σ + ℓ) (Nat.card σ)`. -/
theorem ncard_degree_le {σ : Type*} [Finite σ] (ℓ : ℕ) :
    {α : σ →₀ ℕ | α.degree ≤ ℓ}.ncard = Nat.choose (Nat.card σ + ℓ) (Nat.card σ) := by
  classical
  rw [← Nat.card_coe_set_eq]
  have e : ↥{α : σ →₀ ℕ | α.degree ≤ ℓ} ≃ Sym (Option σ) ℓ :=
    (finsEquivOptionDegreeEq σ ℓ).trans (Sym.equivNatSum (Option σ) ℓ).symm
  let _ := Fintype.ofFinite σ
  rw [Nat.card_congr e, Sym.natCard_sym_eq_choose, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_option]
  have h : Fintype.card σ + 1 + ℓ - 1 = Fintype.card σ + ℓ := by omega
  rw [h, Nat.choose_symm_add]

end Finsupp

end DegreeLeCount

section PowerSeriesDiagram

namespace MonomialOrder

/-- Adding the `n`-th power of the maximal ideal of `MvPowerSeries σ K` adjoins precisely the
exponents of total degree at least `n` to the graded-lexicographic initial diagram. -/
theorem degLex_initialDiagram_sup_maximalIdeal_pow {σ K : Type*} [Finite σ] [LinearOrder σ]
    [Field K] (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    degLex.initialDiagram (I ⊔ maximalIdeal (MvPowerSeries σ K) ^ n) =
      degLex.initialDiagram I ∪ {α : σ →₀ ℕ | n ≤ α.degree} := by
  ext α
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · intro hα
    by_cases hdeg : n ≤ α.degree
    · exact Or.inr hdeg
    push Not at hdeg
    left
    obtain ⟨h, hh_mem, hh0, hinit⟩ := degLex.mem_initialDiagram_iff.mp hα
    obtain ⟨f, hfI, g, hg_mem, hfg⟩ := Submodule.mem_sup.mp hh_mem
    have hg_ord : (n : ℕ∞) ≤ g.order := MvPowerSeries.mem_maximalIdeal_pow_iff_le_order.mp hg_mem
    -- Subtracting `g ∈ 𝔪 ^ n` leaves all coefficients at `degLex`-exponents `≤ α` unchanged.
    have hcoeff : ∀ β : σ →₀ ℕ, β ≼[degLex] α →
        MvPowerSeries.coeff β f = MvPowerSeries.coeff β h := by
      intro β hβα
      have hβdeg : β.degree ≤ α.degree := by
        by_contra! hlt
        exact hβα.not_gt (degLex_lt_iff.mpr (Finsupp.DegLex.lt_iff.mpr (Or.inl hlt)))
      have hg0 : MvPowerSeries.coeff β g = 0 :=
        MvPowerSeries.coeff_of_lt_order ((Nat.cast_lt.mpr (hβdeg.trans_lt hdeg)).trans_le hg_ord)
      rw [← hfg, map_add, hg0, add_zero]
    have hfα : MvPowerSeries.coeff α f ≠ 0 := by
      rw [hcoeff α le_rfl, ← hinit]
      exact degLex.coeff_initialExp_ne_zero hh0
    refine degLex.mem_initialDiagram_iff_exists_isLeast.mpr ⟨f, hfI, ?_, ?_⟩
    · exact ⟨α, MvPowerSeries.mem_support.mpr hfα, rfl⟩
    · rintro _ ⟨β, hβsupp, rfl⟩
      by_contra! hlt
      have hfβ : MvPowerSeries.coeff β f = 0 := by
        rw [hcoeff β hlt.le]
        exact degLex.coeff_eq_zero_of_lt_initialExp (hinit.symm ▸ hlt)
      exact (MvPowerSeries.mem_support.mp hβsupp) hfβ
  · rintro (hα | hdeg)
    · exact degLex.initialDiagram_mono le_sup_left hα
    · refine degLex.mem_initialDiagram_iff.mpr ⟨MvPowerSeries.monomial α (1 : K), ?_, ?_, ?_⟩
      · refine Ideal.mem_sup_right (MvPowerSeries.mem_maximalIdeal_pow_iff_le_order.mpr ?_)
        rw [MvPowerSeries.order_monomial_of_ne_zero (one_ne_zero : (1 : K) ≠ 0)]
        exact Nat.cast_le.mpr hdeg
      · intro h0
        exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrArg (MvPowerSeries.coeff α) h0)
      · exact degLex.initialExp_monomial_of_ne_zero α (one_ne_zero : (1 : K) ≠ 0)

end MonomialOrder

namespace MvPowerSeries

/-- Over a field `K`, the length of any `MvPowerSeries σ K`-module equals its `K`-length, since
the residue field of `MvPowerSeries σ K` is `K`. -/
theorem length_eq_length_base {σ K M : Type*} [Field K] [AddCommGroup M]
    [Module (MvPowerSeries σ K) M] [Module K M] [IsScalarTower K (MvPowerSeries σ K) M] :
    Module.length (MvPowerSeries σ K) M = Module.length K M := by
  let φ : MvPowerSeries σ K →ₐ[K] K :=
    { toRingHom := constantCoeff, commutes' := constantCoeff_C }
  have hsurj : Function.Surjective φ := fun c ↦ ⟨C c, constantCoeff_C c⟩
  let e : ResidueField (MvPowerSeries σ K) ≃ₐ[K] K :=
    TauCeti.residueFieldAlgEquivOfSurjective hsurj
  have : IsLocalHom (algebraMap K (MvPowerSeries σ K)) :=
    ⟨fun a ha ↦ isUnit_iff_ne_zero.mpr fun h0 ↦ ha.ne_zero (by simp [h0])⟩
  have hres : Module.length (ResidueField K) (ResidueField (MvPowerSeries σ K)) = 1 := by
    rw [← Module.length_eq_of_surjective (R := ResidueField K) (S := K)
        (M := ResidueField (MvPowerSeries σ K)) residue_surjective,
      e.toLinearEquiv.length_eq]
    exact Module.length_eq_one K K
  have h := IsLocalRing.length_restrictScalars K (MvPowerSeries σ K) M
  rw [hres, mul_one] at h
  exact h.symm

end MvPowerSeries

end PowerSeriesDiagram

namespace TauCeti

section HilbertSamuelCount

/-- **Hilbert–Samuel count via the initial diagram** (Bierstone–Milman 1997, Corollary 3.20):
for an ideal `I` of `MvPowerSeries σ K` over a field `K` in finitely many ordered variables,
`H_I(ℓ)` is the number of exponents `α` of total degree at most `ℓ` outside the
graded-lexicographic initial diagram `D(I)`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries_eq_ncard {σ K : Type*} [Finite σ]
    [LinearOrder σ] [Field K] (I : Ideal (MvPowerSeries σ K)) (ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ =
      ({α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ MonomialOrder.degLex.initialDiagram I}.ncard : ℕ∞) := by
  classical
  set J : Ideal (MvPowerSeries σ K) := I ⊔ maximalIdeal (MvPowerSeries σ K) ^ (ℓ + 1)
  set S : Set (σ →₀ ℕ) := {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ MonomialOrder.degLex.initialDiagram I}
  have hS_iff (α : σ →₀ ℕ) : α ∉ MonomialOrder.degLex.initialDiagram J ↔ α ∈ S := by
    rw [MonomialOrder.degLex_initialDiagram_sup_maximalIdeal_pow]
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, Nat.lt_succ_iff, S]
    exact and_comm
  -- Identify `complementSubmodule J` with the finite-dimensional `K`-space `S → K`.
  let mkSeries (c : S → K) : MvPowerSeries σ K :=
    fun α ↦ if h : α ∈ S then c ⟨α, h⟩ else 0
  let e : MonomialOrder.degLex.complementSubmodule J ≃ₗ[K] (S → K) :=
    { toFun := fun f α ↦ MvPowerSeries.coeff α.1 f.1
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      invFun := fun c ↦
        ⟨mkSeries c, by
          rw [MonomialOrder.degLex.mem_complementSubmodule_iff]
          intro α hα
          rw [hS_iff]
          by_contra hnot
          exact (MvPowerSeries.mem_support.mp hα) (by
            rw [MvPowerSeries.coeff_apply]
            simp [mkSeries, hnot])⟩
      left_inv := fun f ↦ by
        ext α
        rw [MvPowerSeries.coeff_apply]
        dsimp only [mkSeries]
        split_ifs with hα
        · rfl
        · by_contra hne
          have hmem : α ∉ MonomialOrder.degLex.initialDiagram J :=
            (MonomialOrder.degLex.mem_complementSubmodule_iff.mp f.2) α
              (MvPowerSeries.mem_support.mpr (Ne.symm hne))
          exact hα ((hS_iff α).mp hmem)
      right_inv := fun c ↦ by
        ext α
        dsimp only
        rw [MvPowerSeries.coeff_apply]
        simp [mkSeries, α.2] }
  have hS_fin : S.Finite := (Finsupp.finite_of_degree_le ℓ).subset fun _ h ↦ h.1
  let _ : Fintype S := hS_fin.fintype
  rw [localQuotientHilbertSamuel_def, MvPowerSeries.length_eq_length_base,
    (MonomialOrder.degLex.quotientEquivComplementSubmodule J).length_eq, e.length_eq,
    Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Module.length_eq_one K K, mul_one, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- For a finite variable type `σ` and a field `K`, the Hilbert–Samuel function of
`MvPowerSeries σ K` is `H(ℓ) = Nat.choose (Nat.card σ + ℓ) (Nat.card σ)`. -/
@[simp]
theorem localQuotientHilbertSamuel_mvPowerSeries_bot {σ K : Type*} [Finite σ] [Field K] (ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) ⊥ ℓ =
      (Nat.choose (Nat.card σ + ℓ) (Nat.card σ) : ℕ∞) := by
  let e : σ ≃ Fin (Nat.card σ) := Finite.equivFin σ
  let _ : LinearOrder σ := LinearOrder.lift' e e.injective
  rw [localQuotientHilbertSamuel_mvPowerSeries_eq_ncard, MonomialOrder.initialDiagram_bot]
  simpa using congrArg ((↑) : ℕ → ℕ∞) (Finsupp.ncard_degree_le (σ := σ) ℓ)

/-- For a monomial ideal `I = (X ^ α : α ∈ S)` in `MvPowerSeries σ K`, `H_I(ℓ)` counts the
exponents of degree at most `ℓ` dominating no generator in `S`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries_span_monomial {σ K : Type*} [Finite σ] [Field K]
    (S : Set (σ →₀ ℕ)) (ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K)
        (Ideal.span ((fun α ↦ MvPowerSeries.monomial α (1 : K)) '' S)) ℓ =
      ({α : σ →₀ ℕ | α.degree ≤ ℓ ∧ ∀ β ∈ S, ¬ β ≤ α}.ncard : ℕ∞) := by
  let e : σ ≃ Fin (Nat.card σ) := Finite.equivFin σ
  let _ : LinearOrder σ := LinearOrder.lift' e e.injective
  rw [localQuotientHilbertSamuel_mvPowerSeries_eq_ncard, MonomialOrder.initialDiagram_span_monomial]
  congr 2
  ext α
  simp

/-- In one variable, the Hilbert–Samuel function of `K⟦x⟧ ⧸ (x ^ k)` is `min (ℓ + 1) k`. In
particular, `K⟦x⟧ ⧸ (x ^ 2)` has `H(0) = 1` and `H(ℓ) = 2` for `ℓ ≥ 1`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries_span_X_pow {K : Type*} [Field K] (k ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries (Fin 1) K)
        (Ideal.span {MvPowerSeries.X (0 : Fin 1) ^ k}) ℓ = ((min (ℓ + 1) k : ℕ) : ℕ∞) := by
  have hXpow : MvPowerSeries.X (0 : Fin 1) ^ k =
      MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) k) (1 : K) := by
    rw [MvPowerSeries.X, MvPowerSeries.monomial_pow, one_pow, Finsupp.smul_single, smul_eq_mul,
      mul_one]
  have hspan : Ideal.span {MvPowerSeries.X (0 : Fin 1) ^ k} =
      Ideal.span
        ((fun α ↦ MvPowerSeries.monomial α (1 : K)) '' {Finsupp.single (0 : Fin 1) k}) := by
    simp [hXpow]
  rw [hspan, localQuotientHilbertSamuel_mvPowerSeries_span_monomial]
  congr 1
  set T : Set (Fin 1 →₀ ℕ) :=
    {α : Fin 1 →₀ ℕ | α.degree ≤ ℓ ∧ ∀ β ∈ ({Finsupp.single (0 : Fin 1) k} : Set _), ¬ β ≤ α}
  have eT : T ≃ Fin (min (ℓ + 1) k) :=
    { toFun := fun α ↦ ⟨α.1 0, by
        have hdeg : α.1.degree = α.1 0 := by simp [Finsupp.degree_eq_sum]
        have h1 : α.1 0 ≤ ℓ := hdeg ▸ α.2.1
        have h2 : ¬ k ≤ α.1 0 := fun hle ↦ α.2.2 _ rfl (fun i ↦ by
          fin_cases i
          simpa using hle)
        omega⟩
      invFun := fun i ↦ ⟨Finsupp.single 0 i.1, by
        refine ⟨by simp [Finsupp.degree_single]; omega, ?_⟩
        rintro _ rfl hle
        have := hle 0
        simp only [Finsupp.single_eq_same] at this
        omega⟩
      left_inv := fun α ↦ Subtype.ext <| Finsupp.ext fun i ↦ by
        fin_cases i
        simp
      right_inv := fun i ↦ by
        ext
        simp }
  rw [← Nat.card_coe_set_eq, Nat.card_congr eT, Nat.card_eq_fintype_card, Fintype.card_fin]

end HilbertSamuelCount

section LexStabilization

/-- Diagonal pigeonhole stabilization: given finite sets `B : ℕ → Finset α` and a sequence of
subsets `D : ℕ → Set α`, there exist nested infinite index sets `S 0 ⊇ S 1 ⊇ ⋯` and limit slices
`E ℓ` such that `(B ℓ : Set α) ∩ D j = E ℓ` for every `j ∈ S ℓ`. -/
private theorem exists_antitone_infinite_inter_eq {α : Type*} (B : ℕ → Finset α)
    (D : ℕ → Set α) :
    ∃ (S : ℕ → Set ℕ) (E : ℕ → Set α),
      Antitone S ∧ (∀ ℓ, (S ℓ).Infinite) ∧
        ∀ ℓ, ∀ j ∈ S ℓ, (B ℓ : Set α) ∩ D j = E ℓ := by
  classical
  have hstep : ∀ (ℓ : ℕ) (s : {s : Set ℕ // s.Infinite}),
      ∃ p : {t : Set ℕ // t.Infinite} × Finset α,
        p.1.1 ⊆ s.1 ∧ ∀ j ∈ p.1.1, (B ℓ).filter (· ∈ D j) = p.2 := by
    intro ℓ s
    have : Infinite s.1 := s.2.to_subtype
    let φ : s.1 → (B ℓ).powerset := fun j ↦
      ⟨(B ℓ).filter (· ∈ D j.1), Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
    obtain ⟨E, hE⟩ := Finite.exists_infinite_fiber φ
    refine ⟨⟨⟨Subtype.val '' (φ ⁻¹' {E}),
      (Set.infinite_coe_iff.mp hE).image Subtype.val_injective.injOn⟩, E.1⟩, ?_, ?_⟩
    · rintro _ ⟨j, -, rfl⟩
      exact j.2
    · rintro _ ⟨j, hj, rfl⟩
      exact congrArg Subtype.val (Set.mem_singleton_iff.mp hj)
  let chain : ℕ → {t : Set ℕ // t.Infinite} × Finset α :=
    Nat.rec
      (Classical.choose (hstep 0 ⟨Set.univ, Set.infinite_univ⟩))
      (fun ℓ prev ↦ Classical.choose (hstep (ℓ + 1) prev.1))
  refine ⟨fun ℓ ↦ (chain ℓ).1.1, fun ℓ ↦ ((chain ℓ).2 : Set α),
    antitone_nat_of_succ_le fun ℓ ↦ (Classical.choose_spec (hstep (ℓ + 1) (chain ℓ).1)).1,
    fun ℓ ↦ (chain ℓ).1.2, fun ℓ j hj ↦ ?_⟩
  have hfilter : (B ℓ).filter (· ∈ D j) = (chain ℓ).2 := by
    cases ℓ with
    | zero => exact (Classical.choose_spec (hstep 0 ⟨Set.univ, Set.infinite_univ⟩)).2 j hj
    | succ ℓ => exact (Classical.choose_spec (hstep (ℓ + 1) (chain ℓ).1)).2 j hj
  dsimp only
  rw [← hfilter]
  ext a
  simp

/-- **Combinatorial lexicographic stabilization for upper sets** (Bierstone–Milman 1989,
Theorem 5.2.1): for a finite variable type `σ`, there is no sequence `D : ℕ → Set (σ →₀ ℕ)` of
upper sets whose complement-count functions `ℓ ↦ #{|α| ≤ ℓ, α ∉ D j}` strictly decrease in the
lexicographic order. -/
theorem not_strictAnti_toLex_ncard_degree_le_compl {σ : Type*} [Finite σ]
    (D : ℕ → Set (σ →₀ ℕ)) (hD : ∀ j, IsUpperSet (D j)) :
    ¬ StrictAnti fun j ↦
      toLex fun ℓ ↦ {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D j}.ncard := by
  classical
  intro hanti
  let B : ℕ → Finset (σ →₀ ℕ) := fun ℓ ↦ (Finsupp.finite_of_degree_le (σ := σ) ℓ).toFinset
  let h : ℕ → ℕ → ℕ := fun j ℓ ↦ {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D j}.ncard
  obtain ⟨S, E, hS_anti, hS_inf, hSE⟩ := exists_antitone_infinite_inter_eq B D
  -- Form the diagonal limit diagram `D_inf` and establish degree-by-degree coherence.
  let D_inf : Set (σ →₀ ℕ) := {α | α ∈ E α.degree}
  let h_inf : ℕ → ℕ := fun r ↦ {α : σ →₀ ℕ | α.degree ≤ r ∧ α ∉ D_inf}.ncard
  have hcoh : ∀ ℓ, ∀ j ∈ S ℓ, ∀ α : σ →₀ ℕ, α.degree ≤ ℓ → (α ∈ D j ↔ α ∈ D_inf) := by
    intro ℓ j hj α hα
    have hαB : α ∈ (B α.degree : Set (σ →₀ ℕ)) :=
      (Finsupp.finite_of_degree_le α.degree).mem_toFinset.mpr (le_rfl : α.degree ≤ α.degree)
    have heq := congrArg (α ∈ ·) (hSE α.degree j (hS_anti hα hj))
    simpa [D_inf, hαB] using heq
  have hcount_eq : ∀ ℓ, ∀ j ∈ S ℓ, ∀ r ≤ ℓ, h j r = h_inf r := by
    intro ℓ j hj r hr
    dsimp only [h, h_inf]
    congr 1
    ext α
    simp only [Set.mem_ofPred_eq, and_congr_right_iff]
    intro hαr
    exact not_congr (hcoh ℓ j hj α (hαr.trans hr))
  -- By Dickson's lemma, the minimal elements of `D_inf` are finite of max degree `d`.
  have hV_fin : {v : σ →₀ ℕ | Minimal (· ∈ D_inf) v}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  let d : ℕ := hV_fin.toFinset.sup Finsupp.degree
  -- For any `j ∈ S d`, every minimal element of `D_inf` lies in `D j`, hence `D_inf ⊆ D j`.
  have hsub_of_mem_Sd : ∀ j ∈ S d, D_inf ⊆ D j := by
    intro j hj γ hγ
    obtain ⟨v, hvγ, hvmin⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ D_inf) γ hγ
    have hvd : v.degree ≤ d := Finset.le_sup (f := Finsupp.degree) (hV_fin.mem_toFinset.mpr hvmin)
    exact hD j hvγ ((hcoh d j hj v hvd).mpr hvmin.prop)
  -- Contradict strict lex decrease between `j ∈ S d` and `k ∈ S ℓ₀` with `j + 1 < k`.
  obtain ⟨j, hj⟩ := (hS_inf d).nonempty
  have hle_inf (r : ℕ) : h j r ≤ h_inf r :=
    Set.ncard_le_ncard (fun α ⟨hαr, hαnot⟩ ↦ ⟨hαr, fun hαinf ↦ hαnot (hsub_of_mem_Sd j hj hαinf)⟩)
      ((Finsupp.finite_of_degree_le r).subset fun _ hα ↦ hα.1)
  obtain ⟨ℓ₀, hlt_eq, hlt_at⟩ := hanti (Nat.lt_succ_self j)
  obtain ⟨k, hkS, hkgt⟩ := (hS_inf ℓ₀).exists_gt (j + 1)
  have hle_k : ∀ r ≤ ℓ₀, h j r ≤ h k r := fun r hr ↦
    (hle_inf r).trans_eq (hcount_eq ℓ₀ k hkS r hr).symm
  have hlt_k : h (j + 1) ℓ₀ < h k ℓ₀ := hlt_at.trans_le (hle_k ℓ₀ le_rfl)
  have hex : ∃ r, h (j + 1) r < h k r := ⟨ℓ₀, hlt_k⟩
  let r₀ : ℕ := Nat.find hex
  have hr₀_le : r₀ ≤ ℓ₀ := Nat.find_min' hex hlt_k
  have hlt_lex : toLex (h (j + 1)) < toLex (h k) := by
    refine ⟨r₀, fun r hr ↦ ?_, Nat.find_spec hex⟩
    have hr_lt : r < ℓ₀ := hr.trans_le hr₀_le
    have hle_r : h (j + 1) r ≤ h k r := (hlt_eq r hr_lt).le.trans (hle_k r hr_lt.le)
    exact le_antisymm hle_r (not_lt.mp (Nat.find_min hex hr))
  exact hlt_lex.not_gt (hanti hkgt)

/-- Every lexicographically nonincreasing sequence of complement-count functions of upper sets in
`σ →₀ ℕ` (for finite `σ`) is eventually constant. -/
theorem eventually_const_ncard_degree_le_compl_of_lex_antitone {σ : Type*} [Finite σ]
    (D : ℕ → Set (σ →₀ ℕ)) (hD : ∀ j, IsUpperSet (D j))
    (h : ∀ j, toLex (fun ℓ ↦ {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D (j + 1)}.ncard) ≤
      toLex (fun ℓ ↦ {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D j}.ncard)) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      (fun ℓ ↦ {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D j}.ncard) =
        fun ℓ ↦ {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D j₀}.ncard := by
  let f : ℕ → Lex (ℕ → ℕ) := fun j ↦
    toLex fun ℓ ↦ {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D j}.ncard
  have hf_anti : Antitone f := antitone_nat_of_succ_le h
  by_contra hnot
  push Not at hnot
  -- Extract a strictly increasing subsequence along which `f` strictly decreases.
  have hnext : ∀ j₀, ∃ j, j₀ < j ∧ f j < f j₀ := by
    intro j₀
    obtain ⟨j, hge, hne⟩ := hnot j₀
    have hlt : f j < f j₀ := (hf_anti hge).lt_of_ne (fun heq ↦ hne (toLex.injective heq))
    have hgt : j₀ < j := hge.lt_of_ne (fun heq ↦ hlt.ne (congrArg f heq.symm))
    exact ⟨j, hgt, hlt⟩
  let φ : ℕ → ℕ := Nat.rec 0 fun _ prev ↦ Classical.choose (hnext prev)
  have hφ_lt (k : ℕ) : f (φ (k + 1)) < f (φ k) := (Classical.choose_spec (hnext (φ k))).2
  exact not_strictAnti_toLex_ncard_degree_le_compl (D ∘ φ) (fun k ↦ hD (φ k))
    (strictAnti_nat_of_succ_lt hφ_lt)

/-- **Lexicographic stabilization of realized Hilbert–Samuel functions** over any finite variable
type `σ` and any field `K` (Bierstone–Milman 1989, Theorem 5.2.1; Bierstone–Milman–Temkin §6.1):
every lexicographically nonincreasing sequence of Hilbert–Samuel functions of ideals in
`MvPowerSeries σ K` is eventually constant. -/
theorem hsLexStabilization_of_finite {σ K : Type*} [Finite σ] [Field K]
    (I : ℕ → Ideal (MvPowerSeries σ K))
    (h : ∀ j, localQuotientHilbertSamuel _ (I (j + 1)) = localQuotientHilbertSamuel _ (I j) ∨
      Pi.Lex (· < ·) (· < ·) (localQuotientHilbertSamuel _ (I (j + 1)))
        (localQuotientHilbertSamuel _ (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel _ (I j) = localQuotientHilbertSamuel _ (I j₀) := by
  let e : σ ≃ Fin (Nat.card σ) := Finite.equivFin σ
  let _ : LinearOrder σ := LinearOrder.lift' e e.injective
  let D : ℕ → Set (σ →₀ ℕ) := fun j ↦ MonomialOrder.degLex.initialDiagram (I j)
  have hval (j ℓ : ℕ) : localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) ℓ =
      ({α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D j}.ncard : ℕ∞) :=
    localQuotientHilbertSamuel_mvPowerSeries_eq_ncard (I j) ℓ
  have hlex : ∀ j, toLex (fun ℓ ↦ {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D (j + 1)}.ncard) ≤
      toLex (fun ℓ ↦ {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D j}.ncard) := by
    intro j
    rcases h j with heq | hlt
    · refine le_of_eq (congrArg toLex (funext fun ℓ ↦ Nat.cast_injective (R := ℕ∞) ?_))
      rw [← hval, ← hval, heq]
    · obtain ⟨ℓ₀, hlt_eq, hlt_at⟩ := hlt
      refine le_of_lt (show Pi.Lex (· < ·) (· < ·)
          (fun ℓ ↦ {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D (j + 1)}.ncard)
          (fun ℓ ↦ {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D j}.ncard) from
        ⟨ℓ₀, fun r hr ↦ Nat.cast_injective (R := ℕ∞) (by rw [← hval, ← hval]; exact hlt_eq r hr),
          Nat.cast_lt (α := ℕ∞).mp (by rw [← hval, ← hval]; exact hlt_at)⟩)
  obtain ⟨j₀, hj₀⟩ := eventually_const_ncard_degree_le_compl_of_lex_antitone D
    (fun j ↦ MonomialOrder.degLex.isUpperSet_initialDiagram (I j)) hlex
  refine ⟨j₀, fun j hj ↦ funext fun ℓ ↦ ?_⟩
  rw [hval, hval, congrFun (hj₀ j hj) ℓ]

/-- **Lexicographic stabilization of realized Hilbert–Samuel functions** in
`MvPowerSeries (Fin n) K` over an arbitrary field `K`: every lexicographically nonincreasing
sequence of Hilbert–Samuel functions realized by ideals in `K⟦X₁, …, Xₙ⟧` is eventually
constant. -/
theorem hsLexStabilization (K : Type*) [Field K] (n : ℕ)
    (I : ℕ → Ideal (MvPowerSeries (Fin n) K))
    (h : ∀ j, localQuotientHilbertSamuel _ (I (j + 1)) = localQuotientHilbertSamuel _ (I j) ∨
      Pi.Lex (· < ·) (· < ·) (localQuotientHilbertSamuel _ (I (j + 1)))
        (localQuotientHilbertSamuel _ (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel _ (I j) = localQuotientHilbertSamuel _ (I j₀) :=
  hsLexStabilization_of_finite I h

/-- **Pointwise Hilbert–Samuel stabilization**: every pointwise nonincreasing sequence of
Hilbert–Samuel functions realized by ideals in `MvPowerSeries σ K` (for finite `σ` and any field
`K`) is eventually constant. -/
theorem hsPointwiseStabilization {σ K : Type*} [Finite σ] [Field K]
    (I : ℕ → Ideal (MvPowerSeries σ K))
    (h : ∀ j ℓ, localQuotientHilbertSamuel _ (I (j + 1)) ℓ ≤
      localQuotientHilbertSamuel _ (I j) ℓ) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel _ (I j) = localQuotientHilbertSamuel _ (I j₀) :=
  hsLexStabilization_of_finite I fun j ↦ by
    have hle : toLex (localQuotientHilbertSamuel _ (I (j + 1))) ≤
        toLex (localQuotientHilbertSamuel _ (I j)) :=
      Pi.toLex_monotone (h j)
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact Or.inl (toLex.injective heq)
    · exact Or.inr hlt

end LexStabilization

section Examples

/-- For `K⟦X₁, …, Xₙ⟧`, `H(ℓ) = Nat.choose (n + ℓ) n`. -/
example {K : Type*} [Field K] (n ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries (Fin n) K) ⊥ ℓ = (Nat.choose (n + ℓ) n : ℕ∞) := by
  simp

/-- For `K⟦x⟧ ⧸ (x ^ 2)`, `H(0) = 1` and `H(ℓ) = 2` for every `ℓ ≥ 1`. -/
example {K : Type*} [Field K] :
    localQuotientHilbertSamuel (MvPowerSeries (Fin 1) K)
        (Ideal.span {MvPowerSeries.X (0 : Fin 1) ^ 2}) 0 = 1 ∧
      ∀ ℓ ≥ 1, localQuotientHilbertSamuel (MvPowerSeries (Fin 1) K)
        (Ideal.span {MvPowerSeries.X (0 : Fin 1) ^ 2}) ℓ = 2 := by
  refine ⟨by rw [localQuotientHilbertSamuel_mvPowerSeries_span_X_pow]; norm_num, fun ℓ hℓ ↦ ?_⟩
  rw [localQuotientHilbertSamuel_mvPowerSeries_span_X_pow, min_eq_right (by omega : 2 ≤ ℓ + 1)]
  rfl

/-- Realizability is essential for `hsLexStabilization`: the non-realized indicator functions
`ℓ ↦ if j ≤ ℓ then 1 else 0` strictly decrease in lexicographic order. -/
example : StrictAnti fun j : ℕ ↦ toLex fun ℓ : ℕ ↦ (if j ≤ ℓ then (1 : ℕ) else 0) :=
  strictAnti_nat_of_succ_lt fun j ↦
    ⟨j, fun r hr ↦ by
      change (if j + 1 ≤ r then (1 : ℕ) else 0) = (if j ≤ r then 1 else 0)
      have : r < j := hr
      split_ifs <;> omega,
      by simp⟩

end Examples

end TauCeti
