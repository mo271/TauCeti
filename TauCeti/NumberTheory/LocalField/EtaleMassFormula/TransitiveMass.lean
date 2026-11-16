/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet.Sum
public import TauCeti.FieldTheory.Galois.GaloisSet.Relabelling
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Mass
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount
import TauCeti.FieldTheory.Galois.FixedField
import Mathlib.Data.Fintype.Sum

/-!
# Splitting symbols of Galois sets and the transitive mass by residue degree

For a nonarchimedean local field `K` with residue field of cardinality `q`, the *splitting symbol*
`TauCeti.GaloisSet.splittingSymbol ρ` of a labelled Galois set `ρ : GaloisSet K n` is the multiset,
over the Galois orbits on `Fin n`, of the pairs `(f, e)` of residue degree and ramification index of
the fixed field of a point stabilizer in each orbit [Bhargava 2007, (2.1)]. Conjugate stabilizers
have isomorphic fixed fields, so `(f, e)` is independent of the representative chosen in each orbit.

Each factor `(f, e)` of `ρ.splittingSymbol` has positive components, and `∑ f * e = n`. The symbol
is invariant under equivariant bijections (in particular under relabelling) and additive on disjoint
unions `TauCeti.GaloisSet.sumCongr`, as is `TauCeti.GaloisSet.discriminantExponent`.

A labelled Galois set of size `f * e` (with `0 < f` and `0 < e`) has splitting symbol `{(f, e)}`
precisely when it is transitive and its point stabilizers fix subextensions of residue degree `f`
(`TauCeti.GaloisSet.splittingSymbol_eq_singleton_iff`). Combining
`TauCeti.GaloisSet.tsum_isTransitive` with the subfield count `TauCeti.tsum_inertiaDegree_eq`
evaluates the mass of the Galois sets with splitting symbol `{(f, e)}` to
`1 / (f * q ^ (f * (e - 1)))` (`TauCeti.etaleMass_isTransitive_splittingSymbol`).

## Main definitions and results

* `TauCeti.GaloisSet.splittingSymbol`: the multiset of `(f, e)` pairs over the orbits of a Galois
  set.
* `TauCeti.GaloisSet.discriminantExponent_sumCongr` and
  `TauCeti.GaloisSet.splittingSymbol_sumCongr`: additivity of discriminant weight and splitting
  symbol on disjoint unions.
* `TauCeti.GaloisSet.splittingSymbol_eq_singleton_iff`: characterization of transitive Galois sets
  of prescribed residue degree and ramification index.
* `TauCeti.tsum_splittingSymbol_eq_singleton` and
  `TauCeti.etaleMass_isTransitive_splittingSymbol`: mass of the Galois sets with splitting symbol
  `{(f, e)}`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

open ValuativeRel
open scoped Nat ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

namespace GaloisSet

variable {m n k : ℕ}

/-- Discriminant exponent is additive on disjoint unions of labelled Galois sets. -/
@[simp]
theorem discriminantExponent_sumCongr (e : Fin m ⊕ Fin n ≃ Fin k) (ρ : GaloisSet K m)
    (τ : GaloisSet K n) :
    (sumCongr e ρ τ).discriminantExponent = ρ.discriminantExponent + τ.discriminantExponent := by
  let := ρ.mulAction
  let := τ.mulAction
  let := (sumCongr e ρ τ).mulAction
  rw [discriminantExponent_def, discriminantExponent_def, discriminantExponent_def,
    ← orbitDiscriminantExponent_eq_of_equiv K e fun σ x ↦ (sumCongr_smul_apply e ρ τ σ x).symm,
    orbitDiscriminantExponent_sum]

open Classical in
/-- The **splitting symbol** of a labelled Galois set ([Bhargava 2007, (2.1)]): the multiset, over
its orbits, of the pair `(f, e)` of residue degree and ramification index of the fixed field of the
stabilizer of a point of the orbit. -/
def splittingSymbol (ρ : GaloisSet K n) : Multiset (ℕ × ℕ) :=
  letI := ρ.mulAction
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  (Finset.univ : Finset (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
    fun ω ↦
      let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) (ω.out : Fin n))
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)

open Classical in
/-- The defining formula of `splittingSymbol`. -/
theorem splittingSymbol_def (ρ : GaloisSet K n) :
    ρ.splittingSymbol =
      letI := ρ.mulAction
      haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
      (Finset.univ : Finset (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
        fun ω ↦
          let F := IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) (ω.out : Fin n))
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree) :=
  (rfl)

section OrbitPair

variable {X : Type*} [MulAction Gal(SeparableClosure K/K) X]

private theorem pair_fixedField_stabilizer_smul (σ : Gal(SeparableClosure K/K)) (x : X) :
    (let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) (σ • x));
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) =
      (let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) x);
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) := by
  dsimp only
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    Subgroup.fixedField_map_conj]
  let e := (IntermediateField.fixedField
    (MulAction.stabilizer Gal(SeparableClosure K/K) x)).equivMap σ.toAlgHom
  rw [← IntermediateField.inertiaDegree_eq_of_algEquiv e, ← e.toLinearEquiv.finrank_eq]

private theorem pair_fixedField_stabilizer_out
    {ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X} {x : X}
    (hx : (Quotient.mk'' x : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    (let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out);
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) =
      (let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) x);
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) := by
  obtain ⟨σ, rfl⟩ := TauCeti.MulAction.exists_smul_out_eq hx
  exact (pair_fixedField_stabilizer_smul σ ω.out).symm

end OrbitPair

open Classical in
/-- Any choice of one representative per orbit computes the splitting symbol. -/
theorem splittingSymbol_eq_map_univ (ρ : GaloisSet K n)
    (s : (letI := ρ.mulAction
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) → Fin n)
    (hs : ∀ ω, (letI := ρ.mulAction
      (Quotient.mk'' (s ω) : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) = ω) :
    ρ.splittingSymbol =
      letI := ρ.mulAction
      haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
      (Finset.univ : Finset (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
        fun ω ↦
          let F := IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) (s ω))
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree) := by
  let := ρ.mulAction
  rw [splittingSymbol_def]
  exact Multiset.map_congr rfl fun ω _ ↦ pair_fixedField_stabilizer_out (hs ω)

/-- The `(f, e)` pair of the fixed field of any label's stabilizer belongs to the splitting
symbol. -/
theorem mk_inertiaDegree_mem_splittingSymbol (ρ : GaloisSet K n) (i : Fin n) :
    (letI := ρ.mulAction
    let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i)
    (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) ∈ ρ.splittingSymbol := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_def, Multiset.mem_map]
  exact ⟨Quotient.mk'' i, Finset.mem_univ _, pair_fixedField_stabilizer_out rfl⟩

/-- Equivariant bijections preserve the splitting symbol of labelled Galois sets. -/
theorem splittingSymbol_eq_of_equiv (ρ : GaloisSet K m) (τ : GaloisSet K n) (e : Fin m ≃ Fin n)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin m), e (ρ.val σ i) = τ.val σ (e i)) :
    ρ.splittingSymbol = τ.splittingSymbol := by
  classical
  let := ρ.mulAction
  let := τ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  let E := TauCeti.MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e he
  rw [splittingSymbol_def, splittingSymbol_def, ← Multiset.map_univ_val_equiv E, Multiset.map_map]
  refine Multiset.map_congr rfl fun ω _ ↦ ?_
  have hE : (Quotient.mk'' (e ω.out) :
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E ω := by
    rw [← TauCeti.MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e he, Quotient.out_eq']
  simp only [Function.comp_apply]
  rw [pair_fixedField_stabilizer_out hE]
  dsimp only
  rw [TauCeti.MulAction.stabilizer_eq_of_injective e e.injective he]

/-- Relabelling a Galois set preserves its splitting symbol. -/
@[simp]
theorem splittingSymbol_smul (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    (e • ρ).splittingSymbol = ρ.splittingSymbol :=
  (ρ.splittingSymbol_eq_of_equiv (e • ρ) e (by simp)).symm

/-- Splitting symbols are additive on disjoint unions of labelled Galois sets. -/
@[simp]
theorem splittingSymbol_sumCongr (e : Fin m ⊕ Fin n ≃ Fin k) (ρ : GaloisSet K m)
    (τ : GaloisSet K n) :
    (sumCongr e ρ τ).splittingSymbol = ρ.splittingSymbol + τ.splittingSymbol := by
  classical
  let hsmul : ∀ (σ : Gal(SeparableClosure K/K)) (x : Fin m ⊕ Fin n),
      letI := ρ.mulAction; letI := τ.mulAction; letI := (sumCongr e ρ τ).mulAction
      e (σ • x) = σ • e x := fun σ x ↦ (sumCongr_smul_apply e ρ τ σ x).symm
  let := ρ.mulAction
  let := τ.mulAction
  let := (sumCongr e ρ τ).mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k))
  let E₁ := TauCeti.MulAction.orbitRelQuotientCongr
    (MulEquiv.refl Gal(SeparableClosure K/K)) e hsmul
  let E₂ := TauCeti.MulAction.orbitRelQuotientSumEquiv
    (G := Gal(SeparableClosure K/K)) (X := Fin m) (Y := Fin n)
  rw [splittingSymbol_def, ← Multiset.map_univ_val_equiv (E₂.symm.trans E₁),
    ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.map_map, Multiset.map_disjSum]
  congr 1
  · rw [splittingSymbol_def]
    refine Multiset.map_congr rfl fun ω _ ↦ ?_
    have hω : (Quotient.mk'' (e (Sum.inl ω.out)) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k)) =
          (E₂.symm.trans E₁) (.inl ω) := by
      rw [Equiv.trans_apply,
        ← TauCeti.MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e hsmul,
        ← TauCeti.MulAction.orbitRelQuotientSumEquiv_symm_inl_mk, Quotient.out_eq']
    dsimp only [Function.comp_apply]
    rw [pair_fixedField_stabilizer_out hω]
    dsimp only
    rw [stabilizer_sumCongr_inl]
  · rw [splittingSymbol_def]
    refine Multiset.map_congr rfl fun ω _ ↦ ?_
    have hω : (Quotient.mk'' (e (Sum.inr ω.out)) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k)) =
          (E₂.symm.trans E₁) (.inr ω) := by
      rw [Equiv.trans_apply,
        ← TauCeti.MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e hsmul,
        ← TauCeti.MulAction.orbitRelQuotientSumEquiv_symm_inr_mk, Quotient.out_eq']
    dsimp only [Function.comp_apply]
    rw [pair_fixedField_stabilizer_out hω]
    dsimp only
    rw [stabilizer_sumCongr_inr]

/-- The number of factors in `ρ.splittingSymbol` is the number of Galois orbits on `Fin n`. -/
@[simp]
theorem card_splittingSymbol (ρ : GaloisSet K n) :
    Multiset.card ρ.splittingSymbol =
      Nat.card (letI := ρ.mulAction
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  simp [splittingSymbol_def, Nat.card_eq_fintype_card]

/-- Every factor `(f, e)` in `ρ.splittingSymbol` has `0 < f` and `0 < e`. -/
theorem pos_of_mem_splittingSymbol {ρ : GaloisSet K n} {x : ℕ × ℕ} (hx : x ∈ ρ.splittingSymbol) :
    0 < x.1 ∧ 0 < x.2 := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_def, Multiset.mem_map] at hx
  obtain ⟨ω, -, rfl⟩ := hx
  dsimp only
  set F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
  have : FiniteDimensional K F := ρ.finiteDimensional_fixedField_stabilizer ω.out
  have hf : 0 < F.inertiaDegree := F.inertiaDegree_pos
  have hmul : F.inertiaDegree * (Module.finrank K F / F.inertiaDegree) = Module.finrank K F :=
    Nat.mul_div_cancel' F.inertiaDegree_dvd_finrank
  have hpos : 0 < Module.finrank K F := Module.finrank_pos
  exact ⟨hf, Nat.pos_of_ne_zero fun h0 ↦ by rw [h0, mul_zero] at hmul; omega⟩

/-- The degrees `f * e` of the factors of `ρ.splittingSymbol` add up to `n`. -/
@[simp]
theorem sum_map_mul_splittingSymbol (ρ : GaloisSet K n) :
    (ρ.splittingSymbol.map fun x ↦ x.1 * x.2).sum = n := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  let (ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    Fintype.ofFinite (MulAction.orbit Gal(SeparableClosure K/K) ω.out)
  rw [splittingSymbol_def, Multiset.map_map]
  have hmap : Finset.univ.val.map ((fun x : ℕ × ℕ ↦ x.1 * x.2) ∘
      fun ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) ↦
        let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) =
      Finset.univ.val.map fun ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) ↦
        Fintype.card (MulAction.orbit Gal(SeparableClosure K/K) ω.out) :=
    Multiset.map_congr rfl fun ω _ ↦ by
      dsimp only [Function.comp_apply]
      rw [Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _),
        ρ.finrank_fixedField_stabilizer ω.out, Nat.card_eq_fintype_card]
  rw [hmap]
  exact Fintype.card_sigma.symm.trans <|
    (Fintype.card_congr
      (MulAction.selfEquivSigmaOrbits Gal(SeparableClosure K/K) (Fin n)).symm).trans
      (Fintype.card_fin n)

/-- An action on an empty label set has empty splitting symbol. -/
@[simp]
theorem splittingSymbol_of_isEmpty [IsEmpty (Fin n)] (ρ : GaloisSet K n) :
    ρ.splittingSymbol = 0 := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  simp [splittingSymbol_def]

/-- The unique Galois set of size zero has empty splitting symbol. -/
theorem splittingSymbol_zero (ρ : GaloisSet K 0) : ρ.splittingSymbol = 0 :=
  splittingSymbol_of_isEmpty ρ

/-- The trivial Galois set of size `n` has splitting symbol `n` copies of `(1, 1)`. -/
@[simp]
theorem splittingSymbol_trivial :
    (trivial K n).splittingSymbol = Multiset.replicate n (1, 1) := by
  classical
  let := (trivial K n).mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have hmem : ∀ x ∈ (trivial K n).splittingSymbol, x = (1, 1) := by
    intro x hx
    rw [splittingSymbol_def, Multiset.mem_map] at hx
    obtain ⟨ω, -, rfl⟩ := hx
    simp [fixedField_stabilizer_trivial]
  have hcard : Multiset.card (trivial K n).splittingSymbol = n := by
    have hsum := sum_map_mul_splittingSymbol (trivial K n)
    rw [Multiset.eq_replicate.2 ⟨rfl, hmem⟩] at hsum ⊢
    simpa using hsum
  exact Multiset.eq_replicate.2 ⟨hcard, hmem⟩

/-- A transitive labelled Galois set has a singleton splitting symbol, computed from the fixed
field of any label's stabilizer. -/
theorem splittingSymbol_of_isTransitive (ρ : GaloisSet K n) (hρ : ρ.IsTransitive) (i : Fin n) :
    ρ.splittingSymbol =
      letI := ρ.mulAction
      let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i)
      {(F.inertiaDegree, n / F.inertiaDegree)} := by
  classical
  let := ρ.mulAction
  have : Nonempty (Fin n) := ⟨i⟩
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin n) := ρ.isTransitive_def.1 hρ
  let := ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
    Gal(SeparableClosure K/K) (Fin n)).1 inferInstance).some
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have huniv : (Finset.univ :
      Finset (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) =
        {Quotient.mk'' i} := by
    ext ω
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  rw [splittingSymbol_def, huniv, Finset.singleton_val, Multiset.map_singleton,
    pair_fixedField_stabilizer_out rfl]
  dsimp only
  rw [ρ.finrank_fixedField_stabilizer_of_isTransitive hρ i]

/-- For `0 < f` and `0 < e`, a labelled Galois set of size `f * e` has splitting symbol `{(f, e)}`
precisely when it is transitive and the stabilizer of label `0` fixes a subextension of residue
degree `f`. -/
theorem splittingSymbol_eq_singleton_iff {f e : ℕ} (hf : 0 < f) (he : 0 < e)
    (ρ : GaloisSet K (f * e)) :
    ρ.splittingSymbol = {(f, e)} ↔
      ρ.IsTransitive ∧
        (letI := ρ.mulAction
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K)
            (⟨0, Nat.mul_pos hf he⟩ : Fin (f * e)))).inertiaDegree = f) := by
  let i₀ : Fin (f * e) := ⟨0, Nat.mul_pos hf he⟩
  constructor
  · intro h
    have htrans : ρ.IsTransitive := by
      let := ρ.mulAction
      have : Nonempty (Fin (f * e)) := ⟨i₀⟩
      have hcard : Nat.card (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (f * e))) =
          1 := by
        rw [← ρ.card_splittingSymbol, h, Multiset.card_singleton]
      obtain ⟨_, _⟩ := Nat.card_eq_one_iff_unique.1 hcard
      exact ρ.isTransitive_def.2 <| (MulAction.pretransitive_iff_unique_quotient_of_nonempty
        Gal(SeparableClosure K/K) (Fin (f * e))).2 ⟨{ default := Quotient.mk'' i₀
                                                      uniq := fun _ ↦ Subsingleton.elim _ _ }⟩
    have hsym := ρ.splittingSymbol_of_isTransitive htrans i₀
    rw [h] at hsym
    exact ⟨htrans, (Prod.mk.inj (Multiset.singleton_inj.1 hsym.symm)).1⟩
  · rintro ⟨htrans, hdeg⟩
    rw [ρ.splittingSymbol_of_isTransitive htrans i₀]
    dsimp only at hdeg ⊢
    rw [hdeg, Nat.mul_div_right e hf]

end GaloisSet

private theorem tsum_ite_eq_tsum_subtype {α : Type*} (p : α → Prop) [DecidablePred p]
    (f : α → ℝ≥0∞) :
    (∑' x : α, if p x then f x else 0) = ∑' x : {x : α // p x}, f x.1 := by
  have h : (∑' x : ({x : α | p x} : Set α), f x.1) = ∑' x : α, if p x then f x else 0 := by
    rw [tsum_subtype]
    refine tsum_congr fun x ↦ ?_
    by_cases hx : p x <;> simp [Set.indicator, hx]
  exact h.symm

/-- Summed over the labelled Galois sets of size `f * e` with splitting symbol `{(f, e)}`, the
weights `q ^ (-d(ρ))` total `(f * e - 1)! * e / q ^ (f * (e - 1))`. -/
theorem tsum_splittingSymbol_eq_singleton {f e : ℕ} (hf : 0 < f) (he : 0 < e) :
    ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      ((f * e - 1)! : ℝ≥0∞) * (e : ℝ≥0∞) /
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)) := by
  classical
  let i₀ : Fin (f * e) := ⟨0, Nat.mul_pos hf he⟩
  let g : IntermediateField K (SeparableClosure K) → ℝ≥0∞ := fun L ↦
    if L.inertiaDegree = f then 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.discriminantExponent else 0
  let E₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}} ≃
      {ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} //
        letI := ρ.1.mulAction
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree = f} :=
    (Equiv.subtypeEquivRight (GaloisSet.splittingSymbol_eq_singleton_iff hf he)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  have lhs_eq :
      (∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent) =
      ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive},
        (letI := ρ.1.mulAction
        g (IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i₀))) := by
    rw [← E₁.symm.tsum_eq]
    refine (tsum_congr fun ρ ↦ ?_).trans (tsum_ite_eq_tsum_subtype _ _).symm
    exact congrArg (fun d ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ d)
      (ρ.1.1.discriminantExponent_of_isTransitive ρ.1.2 i₀)
  have rhs_eq :
      (∑' L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e}, g L.1) =
      ∑' L : {L : IntermediateField K (SeparableClosure K) //
          Module.finrank K L = f * e ∧ L.inertiaDegree = f},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent :=
    (tsum_ite_eq_tsum_subtype (fun L : {L : IntermediateField K (SeparableClosure K) //
        Module.finrank K L = f * e} ↦ L.1.inertiaDegree = f)
      (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent)).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun L : IntermediateField K (SeparableClosure K) ↦ Module.finrank K L = f * e)
        (fun L ↦ L.inertiaDegree = f)).tsum_eq
        (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent))
  rw [lhs_eq, GaloisSet.tsum_isTransitive i₀ g, rhs_eq, tsum_inertiaDegree_eq hf.ne' e,
    mul_div_assoc']

/-- **The transitive mass by residue degree** ([Bhargava 2007, §2]): for `0 < f` and `0 < e`, the
labelled Galois sets of size `f * e` with splitting symbol `{(f, e)}` have mass
`1 / (f * q ^ (f * (e - 1)))`, where `q` is the residue cardinality of `K`. -/
theorem etaleMass_isTransitive_splittingSymbol (f e : ℕ) (hf : 0 < f) (he : 0 < e) :
    ((f * e)! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  rw [tsum_splittingSymbol_eq_singleton hf he]
  set c : ℝ≥0∞ := ((f * e - 1)! : ℝ≥0∞) * (e : ℝ≥0∞)
  set qpow : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))
  have hfac : (f * e)! = f * ((f * e - 1)! * e) := by
    calc (f * e)! = f * e * (f * e - 1)! := (Nat.mul_factorial_pred (Nat.mul_pos hf he).ne').symm
      _ = f * ((f * e - 1)! * e) := by ring
  have hc0 : c ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)) (Nat.cast_ne_zero.2 he.ne')
  have hctop : c ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)
  have hf0 : (f : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hf.ne'
  have hftop : (f : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc ((f * e)! : ℝ≥0∞)⁻¹ * (c / qpow)
      = ((f : ℝ≥0∞) * c)⁻¹ * (c * qpow⁻¹) := by
          rw [hfac, Nat.cast_mul, Nat.cast_mul, div_eq_mul_inv]
    _ = (f : ℝ≥0∞)⁻¹ * (c⁻¹ * c) * qpow⁻¹ := by
          rw [ENNReal.mul_inv (Or.inl hf0) (Or.inl hftop)]; ring
    _ = (f : ℝ≥0∞)⁻¹ * qpow⁻¹ := by rw [ENNReal.inv_mul_cancel hc0 hctop, mul_one]
    _ = 1 / ((f : ℝ≥0∞) * qpow) := by
          rw [← ENNReal.mul_inv (Or.inl hf0) (Or.inl hftop), one_div]

end TauCeti
