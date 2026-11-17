/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.List
public import TauCeti.ModelTheory.Infinitary.CodedConnectives
public import TauCeti.ModelTheory.Infinitary.LanguageMap
public import TauCeti.ModelTheory.Infinitary.Operations
public import TauCeti.ModelTheory.Interpolation.PCClass
public import TauCeti.ModelTheory.RelationalConfiguration.QueryCode
public import TauCeti.ModelTheory.RelationalConfiguration.Structure

/-!
# Projective-class sentences for descriptive trees

Given a descriptive tree `T` on `Bool × ℕ` and an enumeration `e : Encodable (Atom L ℕ)` of the
relational atoms of a language `L` over `ℕ`, this file builds an `L_{ω₁ω}` sentence
`pcSentenceWith e T` (and its canonical specialization `pcSentence T` for `Countable (Atom L ℕ)`)
in the expanded language `L.sum pcWitnessLanguage`.

The relational witness vocabulary `pcWitnessLanguage` has three relation symbols (`PCWitnessRel`):
a unary `zero`, a binary `succ`, and a binary `branch`. The witness axioms (`witnessAxioms`) state
that:

1. `zero` holds of a unique element, `succ` is the graph of an injective total function whose range
   misses `zero`, and every element satisfies some numeral formula `numeralFormula k`; together
   these force the numeral map `ℕ → M` to be a bijection `e : M ≃ ℕ` onto any model `M`, of any
   cardinality and in any universe.
2. `branch` is the graph of a total function, inducing a branch `g : ℕ → ℕ` along `e`.

For each level `n`, `levelSentence e T n` states (via `BoundedFormulaInf.iSupAlong` over
`List (Bool × ℕ)`) that some node `s ∈ T` of length `n` matches both the first `n` coordinates of
the query code (evaluated at the numerals, using `⊥` for undecodable coordinates) and the first `n`
values of `g`. The resulting `pcSentenceWith e T` satisfies:

* **Completeness** (`realize_pcSentenceWith_ofStructure`, `realize_pcSentenceWith_standardWitness`):
  if `(queryCodeWith e c, g) ∈ body T`, then `ℕ` with `c.toStructure` and `standardWitness g`
  models `pcSentenceWith e T`. For an arbitrary language (even with function symbols), the same
  holds for `ofStructure L ℕ`.
* **Soundness** (`exists_equiv_and_branch_of_realize_pcSentenceWith`,
  `exists_equiv_and_branch_of_pcMem_pcSentenceWith`): every model `M` (in any universe, without
  requiring `L.IsRelational` or invariance) admits `f : M ≃ ℕ` and `g : ℕ → ℕ` with
  `(fun n => (queryCodeWith e (f.encodeVia (L := L)) n, g n)) ∈ body T`.

## Main definitions

* `TauCeti.RelationalConfiguration.PCWitnessRel`: the three witness relation symbols (`zero`,
  `succ`, `branch`).
* `TauCeti.RelationalConfiguration.pcWitnessLanguage`: the relational witness language.
* `TauCeti.RelationalConfiguration.standardWitnessRel` and
  `TauCeti.RelationalConfiguration.standardWitness`: the standard witness structure on `ℕ` for a
  branch `g : ℕ → ℕ`.
* `TauCeti.RelationalConfiguration.numeralFormula`, `branchAtFormula`, `witnessAxioms`: the
  witness-language numeral formulas and axioms.
* `TauCeti.RelationalConfiguration.pcSentenceWith` and `pcSentence`: the `L_{ω₁ω}` sentence in
  `L.sum pcWitnessLanguage` characterizing a descriptive tree `T` on `Bool × ℕ`.

## Main results

* `TauCeti.RelationalConfiguration.realize_pcSentenceWith_ofStructure`,
  `realize_pcSentenceWith_standardWitness`, and `pcMem_pcSentenceWith_of_mem_body` (with canonical
  counterparts for `pcSentence`): completeness of `pcSentenceWith` and `pcSentence`.
* `TauCeti.RelationalConfiguration.exists_equiv_and_branch_of_realize_pcSentenceWith` and
  `exists_equiv_and_branch_of_pcMem_pcSentenceWith`: soundness of `pcSentenceWith` in arbitrary
  universes, without assuming `L.IsRelational`.
* `TauCeti.RelationalConfiguration.exists_pcSentence`: packaged completeness and soundness for the
  canonical `pcSentence`.
* `TauCeti.RelationalConfiguration.not_realize_pcSentenceWith_bot` and
  `realize_pcSentenceWith_top_ofStructure`: boundary checks at `⊥` and `⊤`.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Lemma 4.24 (representing invariant analytic sets as `PC_{ω₁ω}` classes; here the
  witness symbols are relational graphs, so `pcWitnessLanguage` is relational and works uniformly
  with `RelationalConfiguration`).
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995.
-/

public section

universe u v w

open Descriptive Descriptive.Tree FirstOrder FirstOrder.Language

namespace TauCeti.RelationalConfiguration

/-! ### The witness vocabulary and standard witness structure -/

/-- The relation symbols of the witness vocabulary: a unary `zero`, a binary `succ`, and a binary
`branch`. -/
inductive PCWitnessRel : ℕ → Type
  | zero : PCWitnessRel 1
  | succ : PCWitnessRel 2
  | branch : PCWitnessRel 2

instance (n : ℕ) : Finite (PCWitnessRel n) := by
  refine Finite.of_injective (f := fun r : PCWitnessRel n => match r with
    | .zero => (0 : Fin 3)
    | .succ => 1
    | .branch => 2) ?_
  intro a b h
  cases a <;> cases b <;> simp_all

/-- The relational witness language with relation symbols `PCWitnessRel`. -/
@[expose]
def pcWitnessLanguage : Language.{0, 0} :=
  ⟨fun _ => Empty, PCWitnessRel⟩

instance : pcWitnessLanguage.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance (n : ℕ) : Finite (pcWitnessLanguage.Relations n) :=
  inferInstanceAs (Finite (PCWitnessRel n))

/-- The relations of the standard witness structure on `ℕ` for a branch `g`: `zero` is `{0}`,
`succ` is the graph of `n ↦ n + 1`, and `branch` is the graph of `g`. -/
def standardWitnessRel (g : ℕ → ℕ) : {n : ℕ} → PCWitnessRel n → (Fin n → ℕ) → Prop
  | _, .zero, v => v 0 = 0
  | _, .succ, v => v 1 = v 0 + 1
  | _, .branch, v => v 1 = g (v 0)

/-- The standard witness structure on `ℕ` for a branch `g`. -/
@[instance_reducible]
def standardWitness (g : ℕ → ℕ) : pcWitnessLanguage.Structure ℕ where
  funMap f := isEmptyElim f
  RelMap := standardWitnessRel g

/-! ### Atomic witness formulas and realization helpers -/

private def zeroAt {n : ℕ} (i : Fin n) : pcWitnessLanguage.BoundedFormulaω Empty n :=
  .rel PCWitnessRel.zero ![.var (.inr i)]

private def succAt {n : ℕ} (i j : Fin n) : pcWitnessLanguage.BoundedFormulaω Empty n :=
  .rel PCWitnessRel.succ ![.var (.inr i), .var (.inr j)]

private def branchAt {n : ℕ} (i j : Fin n) : pcWitnessLanguage.BoundedFormulaω Empty n :=
  .rel PCWitnessRel.branch ![.var (.inr i), .var (.inr j)]

private theorem realize_zeroAt {M : Type w} [pcWitnessLanguage.Structure M] {n : ℕ}
    (i : Fin n) (xs : Fin n → M) :
    (zeroAt i).Realize Empty.elim xs ↔
      Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![xs i] := by
  simp only [zeroAt]
  refine iff_of_eq (congrArg (Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.zero) ?_)
  funext k; fin_cases k; rfl

private theorem realize_succAt {M : Type w} [pcWitnessLanguage.Structure M] {n : ℕ}
    (i j : Fin n) (xs : Fin n → M) :
    (succAt i j).Realize Empty.elim xs ↔
      Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![xs i, xs j] := by
  simp only [succAt]
  refine iff_of_eq (congrArg (Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.succ) ?_)
  funext k; fin_cases k <;> rfl

private theorem realize_branchAt {M : Type w} [pcWitnessLanguage.Structure M] {n : ℕ}
    (i j : Fin n) (xs : Fin n → M) :
    (branchAt i j).Realize Empty.elim xs ↔
      Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.branch ![xs i, xs j] := by
  simp only [branchAt]
  refine iff_of_eq (congrArg (Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.branch) ?_)
  funext k; fin_cases k <;> rfl

/-! ### Numeral formulas and witness axioms -/

/-- The `k`-th numeral formula `νₖ(x)` in `pcWitnessLanguage`: `ν₀(x) := zero(x)` and
`νₖ₊₁(x) := ∃ y, νₖ(y) ∧ succ(y, x)`. -/
def numeralFormula : ℕ → pcWitnessLanguage.BoundedFormulaω Empty 1
  | 0 => zeroAt 0
  | k + 1 => (BoundedFormulaInf.mapBound (![1] : Fin 1 → Fin 2) (numeralFormula k) ⊓
      succAt (1 : Fin 2) 0).ex

/-- Reindexing `numeralFormula k` along a singleton projection `![j]` evaluates it at `![xs j]`. -/
private theorem realize_mapBound_numeralFormula {M : Type w} [pcWitnessLanguage.Structure M]
    {n : ℕ} (k : ℕ) (j : Fin n) (xs : Fin n → M) :
    (BoundedFormulaInf.mapBound (![j] : Fin 1 → Fin n) (numeralFormula k)).Realize Empty.elim xs ↔
      (numeralFormula k).Realize Empty.elim ![xs j] := by
  rw [BoundedFormulaInf.realize_mapBound]
  exact iff_of_eq (congrArg _ (by funext i; fin_cases i; rfl))

/-- Realization of `numeralFormula 0`. -/
@[simp]
theorem realize_numeralFormula_zero {M : Type w} [pcWitnessLanguage.Structure M] (x : M) :
    (numeralFormula 0).Realize Empty.elim ![x] ↔
      Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![x] :=
  realize_zeroAt 0 ![x]

/-- Realization of `numeralFormula (k + 1)`. -/
@[simp]
theorem realize_numeralFormula_succ {M : Type w} [pcWitnessLanguage.Structure M] (k : ℕ) (x : M) :
    (numeralFormula (k + 1)).Realize Empty.elim ![x] ↔
      ∃ y : M, (numeralFormula k).Realize Empty.elim ![y] ∧
        Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![y, x] := by
  simp only [numeralFormula, BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_inf,
    realize_mapBound_numeralFormula, realize_succAt]
  rfl

/-- In `standardWitness g`, `numeralFormula k` holds precisely of `k`. -/
theorem realize_numeralFormula_standardWitness (g : ℕ → ℕ) (k x : ℕ) :
    @BoundedFormulaInf.Realize pcWitnessLanguage ℕ Empty ℕ (standardWitness g) 1
      (numeralFormula k) Empty.elim ![x] ↔ x = k := by
  let := standardWitness g
  induction k generalizing x with
  | zero => rw [realize_numeralFormula_zero]; rfl
  | succ k ih =>
    rw [realize_numeralFormula_succ]
    refine ⟨fun ⟨y, hy, hsucc⟩ => ?_, fun hx => ⟨k, (ih k).2 rfl, hx⟩⟩
    have hyk : y = k := (ih y).1 hy
    have hxy : x = y + 1 := hsucc
    omega

/-- The sentence asserting `∃ x y, νᵢ(x) ∧ νₘ(y) ∧ branch(x, y)`. -/
def branchAtFormula (i m : ℕ) : pcWitnessLanguage.Sentenceω :=
  (BoundedFormulaInf.mapBound (![0] : Fin 1 → Fin 2) (numeralFormula i) ⊓
    BoundedFormulaInf.mapBound (![1] : Fin 1 → Fin 2) (numeralFormula m) ⊓
    branchAt (0 : Fin 2) 1).exs

/-- Unfolding realization of `branchAtFormula i m`. -/
theorem realize_branchAtFormula {M : Type w} [pcWitnessLanguage.Structure M] (i m : ℕ) :
    SentenceInf.Realize (branchAtFormula i m) M ↔
      ∃ x y : M, (numeralFormula i).Realize Empty.elim ![x] ∧
        (numeralFormula m).Realize Empty.elim ![y] ∧
        Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.branch ![x, y] := by
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, branchAtFormula,
    BoundedFormulaInf.realize_exs, BoundedFormulaInf.realize_inf,
    realize_mapBound_numeralFormula, realize_branchAt]
  exact ⟨fun ⟨xs, ⟨hi, hm⟩, hbr⟩ => ⟨xs 0, xs 1, hi, hm, hbr⟩,
    fun ⟨x, y, hi, hm, hbr⟩ => ⟨![x, y], ⟨hi, hm⟩, hbr⟩⟩

/-- Axioms characterizing `zero`, `succ`, `allNumerals`, and `branch`:
`zero` has a unique element, `succ` is the graph of an injective total function missing `zero`,
every element satisfies some `numeralFormula k`, and `branch` is the graph of a total function. -/
def witnessAxioms : pcWitnessLanguage.Sentenceω :=
  let zeroExists : pcWitnessLanguage.Sentenceω := (zeroAt (0 : Fin 1)).exs
  let zeroUnique : pcWitnessLanguage.Sentenceω :=
    ((zeroAt (0 : Fin 2) ⊓ zeroAt 1).imp (.equal (.var (.inr 0)) (.var (.inr 1)))).alls
  let succTotal : pcWitnessLanguage.Sentenceω := (succAt (0 : Fin 2) 1).ex.all
  let succFunc : pcWitnessLanguage.Sentenceω :=
    ((succAt (0 : Fin 3) 1 ⊓ succAt 0 2).imp (.equal (.var (.inr 1)) (.var (.inr 2)))).alls
  let succInj : pcWitnessLanguage.Sentenceω :=
    ((succAt (0 : Fin 3) 2 ⊓ succAt 1 2).imp (.equal (.var (.inr 0)) (.var (.inr 1)))).alls
  let succNeZero : pcWitnessLanguage.Sentenceω :=
    ((succAt (0 : Fin 2) 1).imp (zeroAt 1).not).alls
  let allNumerals : pcWitnessLanguage.Sentenceω := (BoundedFormulaInf.iSup numeralFormula).all
  let branchTotal : pcWitnessLanguage.Sentenceω := (branchAt (0 : Fin 2) 1).ex.all
  let branchFunc : pcWitnessLanguage.Sentenceω :=
    ((branchAt (0 : Fin 3) 1 ⊓ branchAt 0 2).imp (.equal (.var (.inr 1)) (.var (.inr 2)))).alls
  [zeroExists, zeroUnique, succTotal, succFunc, succInj, succNeZero, allNumerals,
    branchTotal, branchFunc].foldr (· ⊓ ·) ⊤

/-- Unpacked semantic content of `witnessAxioms`. -/
private theorem witnessAxioms_iff {M : Type w} [pcWitnessLanguage.Structure M] :
    SentenceInf.Realize witnessAxioms M ↔
      (∃ x : M, Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![x]) ∧
      (∀ x y : M, Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![x] →
        Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![y] → x = y) ∧
      (∀ x : M, ∃ y : M, Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, y]) ∧
      (∀ x y z : M, Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, y] →
        Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, z] → y = z) ∧
      (∀ x y z : M, Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, z] →
        Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![y, z] → x = y) ∧
      (∀ x y : M, Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, y] →
        ¬ Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![y]) ∧
      (∀ x : M, ∃ k : ℕ, (numeralFormula k).Realize Empty.elim ![x]) ∧
      (∀ x : M, ∃ y : M, Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.branch ![x, y]) ∧
      (∀ x y z : M, Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.branch ![x, y] →
        Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.branch ![x, z] → y = z) := by
  have h1 {a : M} : Fin.snoc (default : Fin 0 → M) a = ![a] := by funext i; fin_cases i; rfl
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, witnessAxioms, List.foldr_cons,
    List.foldr_nil, BoundedFormulaInf.realize_inf, BoundedFormulaInf.realize_top, and_true,
    BoundedFormulaInf.realize_exs, BoundedFormulaInf.realize_alls, BoundedFormulaInf.realize_all,
    BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_imp, BoundedFormulaInf.realize_not,
    BoundedFormulaInf.realize_equal, BoundedFormulaInf.realize_iSup, Term.realize_var,
    Sum.elim_inr, realize_zeroAt, realize_succAt, realize_branchAt, and_imp, h1]
  refine and_congr ⟨fun ⟨xs, h⟩ => ⟨xs 0, h⟩, fun ⟨x, h⟩ => ⟨![x], h⟩⟩
    (and_congr ⟨fun h x y => h ![x, y], fun h xs => h (xs 0) (xs 1)⟩
    (and_congr Iff.rfl
    (and_congr ⟨fun h x y z => h ![x, y, z], fun h xs => h (xs 0) (xs 1) (xs 2)⟩
    (and_congr ⟨fun h x y z => h ![x, y, z], fun h xs => h (xs 0) (xs 1) (xs 2)⟩
    (and_congr ⟨fun h x y => h ![x, y], fun h xs => h (xs 0) (xs 1)⟩
    (and_congr Iff.rfl (and_congr Iff.rfl
    ⟨fun h x y z => h ![x, y, z], fun h xs => h (xs 0) (xs 1) (xs 2)⟩)))))))

/-- Every `standardWitness g` satisfies `witnessAxioms`. -/
theorem realize_witnessAxioms_standardWitness (g : ℕ → ℕ) :
    @SentenceInf.Realize pcWitnessLanguage ℕ witnessAxioms ℕ (standardWitness g) := by
  let := standardWitness g
  rw [witnessAxioms_iff]
  refine ⟨⟨0, rfl⟩, fun _ _ hx hy => hx.trans hy.symm, fun x => ⟨x + 1, rfl⟩,
    fun _ _ _ hxy hxz => hxy.trans hxz.symm, fun x y z hxz hyz => ?_,
    fun x y hxy hy0 => ?_, fun x => ⟨x, (realize_numeralFormula_standardWitness g x x).2 rfl⟩,
    fun x => ⟨g x, rfl⟩, fun _ _ _ hxy hxz => hxy.trans hxz.symm⟩
  · have h1 : z = x + 1 := hxz; have h2 : z = y + 1 := hyz; omega
  · have h1 : y = x + 1 := hxy; have h2 : y = 0 := hy0; omega

/-- In any model of `pcWitnessLanguage` with unique zero `x₀` and functional successor `s`, the
`k`-th numeral formula holds precisely at `s^[k] x₀`. -/
private theorem realize_numeralFormula_iterate {M : Type w} [pcWitnessLanguage.Structure M]
    {x₀ : M} (hx₀ : Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![x₀])
    (hzeroU : ∀ x y : M, Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![x] →
      Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.zero ![y] → x = y)
    {s : M → M}
    (hs_iff : ∀ x y : M, Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, y] ↔
      y = s x)
    (k : ℕ) (x : M) :
    (numeralFormula k).Realize Empty.elim ![x] ↔ x = s^[k] x₀ := by
  induction k generalizing x with
  | zero =>
    rw [realize_numeralFormula_zero]
    exact ⟨fun hx => hzeroU x x₀ hx hx₀, fun hx => hx ▸ hx₀⟩
  | succ k ih =>
    simp only [realize_numeralFormula_succ, ih, hs_iff]
    exact ⟨fun ⟨_, hy, hx⟩ => hx.trans ((congrArg s hy).trans
        (Function.iterate_succ_apply' s k x₀).symm),
      fun hx => ⟨s^[k] x₀, rfl, hx.trans (Function.iterate_succ_apply' s k x₀)⟩⟩

/-- Every model `M` of `witnessAxioms` (in any universe) admits a bijection `e : M ≃ ℕ` matching
the numeral formulas and a function `g : ℕ → ℕ` matching `branchAtFormula`. -/
theorem exists_equiv_of_realize_witnessAxioms {M : Type w} [pcWitnessLanguage.Structure M]
    (h : SentenceInf.Realize witnessAxioms M) :
    ∃ (e : M ≃ ℕ) (g : ℕ → ℕ),
      (∀ k x, (numeralFormula k).Realize Empty.elim ![x] ↔ x = e.symm k) ∧
      ∀ i m, SentenceInf.Realize (branchAtFormula i m) M ↔ m = g i := by
  obtain ⟨⟨x₀, hx₀⟩, hzeroU, hsuccT, hsuccF, hsuccI, hsuccNe, hallN, hbrT, hbrF⟩ :=
    witnessAxioms_iff.1 h
  choose s hs using hsuccT
  choose bf hbf using hbrT
  have hs_iff : ∀ x y, Structure.RelMap (L := pcWitnessLanguage) PCWitnessRel.succ ![x, y] ↔
      y = s x := fun x y => ⟨fun hxy => hsuccF x y (s x) hxy (hs x), fun hxy => hxy ▸ hs x⟩
  have hs_inj : Function.Injective s := fun x y hxy => hsuccI x y (s x) (hs x) (hxy ▸ hs y)
  have hs_ne : ∀ x, s x ≠ x₀ := fun x hxx => hsuccNe x x₀ (hxx ▸ hs x) hx₀
  have hnum := fun k x => realize_numeralFormula_iterate hx₀ hzeroU hs_iff k x
  have hinj : Function.Injective (fun k => s^[k] x₀) := fun m n hmn => by
    have hlt : ∀ a b, a < b → s^[b] x₀ ≠ s^[a] x₀ := fun a b hab heq => by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hab)
      have h0 := Function.iterate_cancel hs_inj heq
      rw [hk, Function.iterate_succ_apply'] at h0
      exact hs_ne _ h0
    rcases lt_trichotomy m n with h' | rfl | h'
    · exact (hlt m n h' hmn.symm).elim
    · rfl
    · exact (hlt n m h' hmn).elim
  have hbij : Function.Bijective (fun k => s^[k] x₀) :=
    ⟨hinj, fun x => by obtain ⟨k, hk⟩ := hallN x; exact ⟨k, ((hnum k x).1 hk).symm⟩⟩
  let e : M ≃ ℕ := (Equiv.ofBijective _ hbij).symm
  have he_symm : ∀ k, e.symm k = s^[k] x₀ := fun _ => rfl
  let g : ℕ → ℕ := fun k => e (bf (e.symm k))
  refine ⟨e, g, fun k x => by rw [he_symm, hnum], fun i m => ?_⟩
  rw [realize_branchAtFormula]
  constructor
  · rintro ⟨x, y, hx, hy, hbr⟩
    have hxi : x = e.symm i := (he_symm i) ▸ (hnum i x).1 hx
    have hym : y = e.symm m := (he_symm m) ▸ (hnum m y).1 hy
    have : e.symm m = bf (e.symm i) :=
      hym.symm.trans ((hbrF x y (bf x) hbr (hbf x)).trans (congrArg bf hxi))
    simpa [g] using congrArg e this
  · rintro rfl
    exact ⟨e.symm i, bf (e.symm i), (hnum i _).2 rfl,
      (hnum _ _).2 ((he_symm _).symm.trans (e.symm_apply_apply _)).symm, hbf _⟩

/-! ### PC sentence of a descriptive tree -/

section PCSentence

variable {L : Language.{u, v}}

/-- The sentence in `L.sum pcWitnessLanguage` asserting that the `L`-relation `R` holds at the
numerals `v 0, …, v (l - 1)`. Works for all arities `l` including nullary `l = 0`. -/
def atomSentence {l : ℕ} (R : L.Relations l) (v : Fin l → ℕ) :
    (L.sum pcWitnessLanguage).Sentenceω :=
  ((List.ofFn fun j : Fin l =>
      LHom.sumInr.onBoundedFormulaInf
        (BoundedFormulaInf.mapBound (![j] : Fin 1 → Fin l) (numeralFormula (v j)))).foldr
      (· ⊓ ·) ⊤ ⊓
    .rel (LHom.sumInl.onRelation R) fun j => .var (.inr j)).exs

/-- Realization of `atomSentence R v` when `numeralFormula k` names `f.symm k`. -/
private theorem realize_atomSentence {M : Type w} [L.Structure M]
    [(L.sum pcWitnessLanguage).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).IsExpansionOn M]
    (f : M ≃ ℕ)
    (hnum : ∀ k x, @BoundedFormulaInf.Realize pcWitnessLanguage ℕ Empty M
      ((LHom.sumInr : pcWitnessLanguage →ᴸ L.sum pcWitnessLanguage).reduct M) 1
      (numeralFormula k) Empty.elim ![x] ↔ x = f.symm k)
    {l : ℕ} (R : L.Relations l) (v : Fin l → ℕ) :
    SentenceInf.Realize (atomSentence R v) M ↔ Structure.RelMap R (f.symm ∘ v) := by
  let : pcWitnessLanguage.Structure M :=
    (LHom.sumInr : pcWitnessLanguage →ᴸ L.sum pcWitnessLanguage).reduct M
  have hfold (xs : Fin l → M) :
      ((List.ofFn fun j : Fin l =>
          (LHom.sumInr : pcWitnessLanguage →ᴸ L.sum pcWitnessLanguage).onBoundedFormulaInf
            (BoundedFormulaInf.mapBound (![j] : Fin 1 → Fin l) (numeralFormula (v j)))).foldr
          (· ⊓ ·) ⊤).Realize Empty.elim xs ↔ xs = f.symm ∘ v := by
    rw [BoundedFormulaInf.realize_foldr_inf]
    simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
      LHom.realize_onBoundedFormulaInf, realize_mapBound_numeralFormula, hnum]
    exact ⟨fun h => funext h, fun h j => congrFun h j⟩
  simp only [SentenceInf.realize_def, FormulaInf.realize_def, atomSentence,
    BoundedFormulaInf.realize_exs, BoundedFormulaInf.realize_inf, hfold,
    BoundedFormulaInf.realize_rel, Term.realize_var, Sum.elim_inr]
  constructor
  · rintro ⟨xs, rfl, hrel⟩
    rwa [← (LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).map_onRelation R (f.symm ∘ v)]
  · intro hrel
    refine ⟨f.symm ∘ v, rfl, ?_⟩
    rwa [(LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).map_onRelation R (f.symm ∘ v)]

/-- The sentence reading the `i`-th coordinate of `queryCodeWith e`: `atomSentence R v` when `i`
decodes to `atom R v`, and `⊥` when `i` decodes to `none`. -/
def querySentence (e : Encodable (Atom L ℕ)) (i : ℕ) : (L.sum pcWitnessLanguage).Sentenceω :=
  match @Encodable.decode _ e i with
  | some a => atomSentence a.2.1 a.2.2
  | none => ⊥

/-- The sentence asserting that the `i`-th coordinate of `queryCodeWith e` equals `b`. -/
def bitSentence (e : Encodable (Atom L ℕ)) (i : ℕ) (b : Bool) :
    (L.sum pcWitnessLanguage).Sentenceω :=
  if b then querySentence e i else (querySentence e i).not

private theorem realize_bitSentence {M : Type w} [L.Structure M]
    [(L.sum pcWitnessLanguage).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).IsExpansionOn M]
    (e : Encodable (Atom L ℕ)) (f : M ≃ ℕ)
    (hnum : ∀ k x, @BoundedFormulaInf.Realize pcWitnessLanguage ℕ Empty M
      ((LHom.sumInr : pcWitnessLanguage →ᴸ L.sum pcWitnessLanguage).reduct M) 1
      (numeralFormula k) Empty.elim ![x] ↔ x = f.symm k)
    (i : ℕ) (b : Bool) :
    SentenceInf.Realize (bitSentence e i b) M ↔
      queryCodeWith e (f.encodeVia (L := L)) i = b := by
  have hq : SentenceInf.Realize (querySentence e i) M ↔
      queryCodeWith e (f.encodeVia (L := L)) i = true := by
    unfold querySentence
    cases h : @Encodable.decode _ e i with
    | none => simp [queryCodeWith_eq_false_of_decode_eq_none e _ h]
    | some a =>
      rw [queryCodeWith_eq_eval_of_decode_eq_some e _ h]
      obtain ⟨l, R, v⟩ := a
      rw [realize_atomSentence f hnum R v, ← atom_def R v]
      classical
      simp [Equiv.eval_encodeVia]
  cases b <;> simp [bitSentence, hq]

/-- The sentence asserting that the initial segment of length `s.length` of `(queryCode, g)` equals
the finite sequence `s : List (Bool × ℕ)`. -/
def nodeSentence (e : Encodable (Atom L ℕ)) (s : List (Bool × ℕ)) :
    (L.sum pcWitnessLanguage).Sentenceω :=
  (List.ofFn fun i : Fin s.length =>
    bitSentence e i.1 (s[i.1]).1 ⊓
      LHom.sumInr.onBoundedFormulaInf (branchAtFormula i.1 (s[i.1]).2)).foldr (· ⊓ ·) ⊤

private theorem realize_nodeSentence {M : Type w} [L.Structure M]
    [(L.sum pcWitnessLanguage).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).IsExpansionOn M]
    (e : Encodable (Atom L ℕ)) (f : M ≃ ℕ) (g : ℕ → ℕ)
    (hnum : ∀ k x, @BoundedFormulaInf.Realize pcWitnessLanguage ℕ Empty M
      ((LHom.sumInr : pcWitnessLanguage →ᴸ L.sum pcWitnessLanguage).reduct M) 1
      (numeralFormula k) Empty.elim ![x] ↔ x = f.symm k)
    (hbr : ∀ i m, @SentenceInf.Realize pcWitnessLanguage ℕ (branchAtFormula i m) M
      ((LHom.sumInr : pcWitnessLanguage →ᴸ L.sum pcWitnessLanguage).reduct M) ↔ m = g i)
    (s : List (Bool × ℕ)) :
    SentenceInf.Realize (nodeSentence e s) M ↔
      initialSegment (fun k => (queryCodeWith e (f.encodeVia (L := L)) k, g k)) s.length = s := by
  let : pcWitnessLanguage.Structure M :=
    (LHom.sumInr : pcWitnessLanguage →ᴸ L.sum pcWitnessLanguage).reduct M
  rw [SentenceInf.realize_def, FormulaInf.realize_def, nodeSentence,
    BoundedFormulaInf.realize_foldr_inf]
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
    BoundedFormulaInf.realize_inf]
  constructor
  · intro h
    refine List.ext_getElem (by simp) fun i _ hi₂ => ?_
    have ⟨hbit, hbranch⟩ := h ⟨i, hi₂⟩
    rw [← FormulaInf.realize_def, ← SentenceInf.realize_def] at hbit hbranch
    have hb : queryCodeWith e (f.encodeVia (L := L)) i = (s[i]).1 :=
      (realize_bitSentence e f hnum i _).1 hbit
    have hbr' : (s[i]).2 = g i :=
      (hbr i _).1 ((LHom.realize_sentenceInf_onBoundedFormulaInf LHom.sumInr _).1 hbranch)
    simp only [getElem_initialSegment]
    exact Prod.ext hb hbr'.symm
  · intro h i
    have hi : (initialSegment (fun k => (queryCodeWith e (f.encodeVia (L := L)) k, g k))
        s.length)[i.1]'(by simp [i.2]) = s[i.1] := by
      simpa using congrArg (fun l : List (Bool × ℕ) => l[i.1]?) h
    rw [getElem_initialSegment] at hi
    rw [← FormulaInf.realize_def, ← SentenceInf.realize_def,
      ← FormulaInf.realize_def, ← SentenceInf.realize_def]
    exact ⟨(realize_bitSentence e f hnum i.1 _).2 (congrArg Prod.fst hi),
      (LHom.realize_sentenceInf_onBoundedFormulaInf LHom.sumInr _).2
        ((hbr i.1 _).2 (congrArg Prod.snd hi).symm)⟩

/-- The sentence asserting that the length-`n` initial segment of `(queryCode, g)` lies in `T`. -/
noncomputable def levelSentence (e : Encodable (Atom L ℕ)) (T : tree (Bool × ℕ)) (n : ℕ) :
    (L.sum pcWitnessLanguage).Sentenceω := by
  classical
  exact BoundedFormulaInf.iSupAlong (TauCeti.IndexCoding.ofEncodable (List (Bool × ℕ))) fun s =>
    if s ∈ T ∧ s.length = n then nodeSentence e s else ⊥

private theorem realize_levelSentence {M : Type w} [L.Structure M]
    [(L.sum pcWitnessLanguage).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).IsExpansionOn M]
    (e : Encodable (Atom L ℕ)) (f : M ≃ ℕ) (g : ℕ → ℕ)
    (hnum : ∀ k x, @BoundedFormulaInf.Realize pcWitnessLanguage ℕ Empty M
      ((LHom.sumInr : pcWitnessLanguage →ᴸ L.sum pcWitnessLanguage).reduct M) 1
      (numeralFormula k) Empty.elim ![x] ↔ x = f.symm k)
    (hbr : ∀ i m, @SentenceInf.Realize pcWitnessLanguage ℕ (branchAtFormula i m) M
      ((LHom.sumInr : pcWitnessLanguage →ᴸ L.sum pcWitnessLanguage).reduct M) ↔ m = g i)
    (T : tree (Bool × ℕ)) (n : ℕ) :
    SentenceInf.Realize (levelSentence e T n) M ↔
      initialSegment (fun k => (queryCodeWith e (f.encodeVia (L := L)) k, g k)) n ∈ T := by
  classical
  rw [SentenceInf.realize_def, FormulaInf.realize_def, levelSentence,
    BoundedFormulaInf.realize_iSupAlong]
  constructor
  · rintro ⟨s, hs⟩
    by_cases hsn : s ∈ T ∧ s.length = n
    · simp only [hsn, ← FormulaInf.realize_def, ← SentenceInf.realize_def] at hs
      have heq := (realize_nodeSentence e f g hnum hbr s).1 hs
      rw [hsn.2] at heq
      exact heq.symm ▸ hsn.1
    · simp only [hsn, ↓reduceIte, BoundedFormulaInf.realize_bot] at hs
  · intro hn
    refine ⟨initialSegment (fun k => (queryCodeWith e (f.encodeVia (L := L)) k, g k)) n, ?_⟩
    have hcond : initialSegment (fun k => (queryCodeWith e (f.encodeVia (L := L)) k, g k)) n ∈ T ∧
        (initialSegment (fun k => (queryCodeWith e (f.encodeVia (L := L)) k, g k)) n).length = n :=
      ⟨hn, by simp⟩
    simp only [hcond, ← FormulaInf.realize_def, ← SentenceInf.realize_def]
    exact (realize_nodeSentence e f g hnum hbr _).2 (by rw [length_initialSegment])

/-- **The PC sentence of a descriptive tree** (explicit-encoding form): the `L_{ω₁ω}` sentence in
`L.sum pcWitnessLanguage` asserting `witnessAxioms` and that every finite initial segment of
`(queryCodeWith e, branch)` lies in `T`. -/
noncomputable def pcSentenceWith (e : Encodable (Atom L ℕ)) (T : tree (Bool × ℕ)) :
    (L.sum pcWitnessLanguage).Sentenceω :=
  LHom.sumInr.onBoundedFormulaInf witnessAxioms ⊓ .iInf (levelSentence e T)

/-- **Completeness of `pcSentenceWith`** for an arbitrary `L`-structure on `ℕ` (no `L.IsRelational`
required): if `(queryCodeWith e (ofStructure L ℕ), g)` is a branch of `T`, then `ℕ` with
`standardWitness g` models `pcSentenceWith e T`. -/
theorem realize_pcSentenceWith_ofStructure (e : Encodable (Atom L ℕ)) (T : tree (Bool × ℕ))
    [L.Structure ℕ] (g : ℕ → ℕ)
    (h : (fun n => (queryCodeWith e (ofStructure L ℕ) n, g n)) ∈ body T) :
    @SentenceInf.Realize (L.sum pcWitnessLanguage) ℕ (pcSentenceWith e T) ℕ
      (@Language.sumStructure L pcWitnessLanguage ℕ _ (standardWitness g)) := by
  let : pcWitnessLanguage.Structure ℕ := standardWitness g
  have hnum : ∀ k x, @BoundedFormulaInf.Realize pcWitnessLanguage ℕ Empty ℕ
      ((LHom.sumInr : pcWitnessLanguage →ᴸ L.sum pcWitnessLanguage).reduct ℕ) 1
      (numeralFormula k) Empty.elim ![x] ↔ x = (Equiv.refl ℕ).symm k := fun k x =>
    realize_numeralFormula_standardWitness g k x
  have hbr : ∀ i m, @SentenceInf.Realize pcWitnessLanguage ℕ (branchAtFormula i m) ℕ
      ((LHom.sumInr : pcWitnessLanguage →ᴸ L.sum pcWitnessLanguage).reduct ℕ) ↔ m = g i := by
    intro i m
    rw [realize_branchAtFormula]
    constructor
    · rintro ⟨x, y, hx, hy, hrel⟩
      have hx' : x = i := (realize_numeralFormula_standardWitness g i x).1 hx
      have hy' : y = m := (realize_numeralFormula_standardWitness g m y).1 hy
      have hr : y = g x := hrel
      subst hx' hy'
      exact hr
    · rintro rfl
      exact ⟨i, g i, (realize_numeralFormula_standardWitness g i i).2 rfl,
        (realize_numeralFormula_standardWitness g (g i) (g i)).2 rfl, rfl⟩
  rw [pcSentenceWith, SentenceInf.realize_inf, SentenceInf.realize_iInf]
  refine ⟨(LHom.realize_sentenceInf_onBoundedFormulaInf LHom.sumInr witnessAxioms).2
      (realize_witnessAxioms_standardWitness g), fun n => ?_⟩
  rw [realize_levelSentence e (Equiv.refl ℕ) g hnum hbr T n, Equiv.encodeVia_refl]
  exact mem_body.1 h n

/-- **Completeness of `pcSentenceWith`** for a relational configuration `c` on `ℕ`. -/
theorem realize_pcSentenceWith_standardWitness [L.IsRelational] (e : Encodable (Atom L ℕ))
    (T : tree (Bool × ℕ)) (c : RelationalConfiguration L ℕ) (g : ℕ → ℕ)
    (h : (fun n => (queryCodeWith e c n, g n)) ∈ body T) :
    @SentenceInf.Realize (L.sum pcWitnessLanguage) ℕ (pcSentenceWith e T) ℕ
      (@Language.sumStructure L pcWitnessLanguage ℕ c.toStructure (standardWitness g)) := by
  let := c.toStructure
  exact realize_pcSentenceWith_ofStructure e T g (by simpa [ofStructure_toStructure] using h)

/-- If `(queryCodeWith e (ofStructure L ℕ), g) ∈ body T`, then `ℕ` lies in the projective class of
`pcSentenceWith e T`. -/
theorem pcMem_pcSentenceWith_of_mem_body (e : Encodable (Atom L ℕ)) (T : tree (Bool × ℕ))
    [L.Structure ℕ] (g : ℕ → ℕ)
    (h : (fun n => (queryCodeWith e (ofStructure L ℕ) n, g n)) ∈ body T) :
    (LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).PCMem (pcSentenceWith e T) ℕ := by
  let : pcWitnessLanguage.Structure ℕ := standardWitness g
  exact LHom.pcMem_of_isExpansionOn (realize_pcSentenceWith_ofStructure e T g h)

/-- **Soundness of `pcSentenceWith`**: every expansion of any `L`-structure `M` (in any universe,
without requiring `L.IsRelational`) that models `pcSentenceWith e T` admits `f : M ≃ ℕ` and
`g : ℕ → ℕ` such that `(queryCodeWith e (f.encodeVia), g) ∈ body T`. -/
theorem exists_equiv_and_branch_of_realize_pcSentenceWith (e : Encodable (Atom L ℕ))
    (T : tree (Bool × ℕ)) {M : Type w} [L.Structure M] [(L.sum pcWitnessLanguage).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).IsExpansionOn M]
    (h : SentenceInf.Realize (pcSentenceWith e T) M) :
    ∃ (f : M ≃ ℕ) (g : ℕ → ℕ),
      (fun n => (queryCodeWith e (f.encodeVia (L := L)) n, g n)) ∈ body T := by
  rw [pcSentenceWith, SentenceInf.realize_inf, SentenceInf.realize_iInf] at h
  let : pcWitnessLanguage.Structure M :=
    (LHom.sumInr : pcWitnessLanguage →ᴸ L.sum pcWitnessLanguage).reduct M
  have hwit : SentenceInf.Realize witnessAxioms M :=
    (LHom.realize_sentenceInf_onBoundedFormulaInf LHom.sumInr witnessAxioms).1 h.1
  obtain ⟨f, g, hnum, hbr⟩ := exists_equiv_of_realize_witnessAxioms hwit
  exact ⟨f, g, mem_body.2 fun n => (realize_levelSentence e f g hnum hbr T n).1 (h.2 n)⟩

/-- Soundness of `pcSentenceWith` stated directly for projective-class membership `LHom.PCMem`. -/
theorem exists_equiv_and_branch_of_pcMem_pcSentenceWith (e : Encodable (Atom L ℕ))
    (T : tree (Bool × ℕ)) {M : Type w} [L.Structure M]
    (h : (LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).PCMem (pcSentenceWith e T) M) :
    ∃ (f : M ≃ ℕ) (g : ℕ → ℕ),
      (fun n => (queryCodeWith e (f.encodeVia (L := L)) n, g n)) ∈ body T := by
  obtain ⟨S, hS, hreal⟩ := LHom.pcMem_iff.1 h
  exact @exists_equiv_and_branch_of_realize_pcSentenceWith L e T M _ S hS hreal

/-- Boundary check: the empty tree `⊥` yields an unsatisfiable PC sentence. -/
theorem not_realize_pcSentenceWith_bot (e : Encodable (Atom L ℕ)) {M : Type w}
    [(L.sum pcWitnessLanguage).Structure M] :
    ¬ SentenceInf.Realize (pcSentenceWith e ⊥) M := by
  intro h
  rw [pcSentenceWith, SentenceInf.realize_inf, SentenceInf.realize_iInf] at h
  have h0 := h.2 0
  classical
  rw [SentenceInf.realize_def, FormulaInf.realize_def, levelSentence,
    BoundedFormulaInf.realize_iSupAlong] at h0
  obtain ⟨s, hs⟩ := h0
  have hnot : ¬ (s ∈ (⊥ : tree (Bool × ℕ)) ∧ s.length = 0) := fun hc => hc.1
  simp only [hnot, ↓reduceIte, BoundedFormulaInf.realize_bot] at hs

/-- Boundary check: for the full tree `⊤`, every `L`-structure on `ℕ` with any branch `g` satisfies
`pcSentenceWith e ⊤`. -/
theorem realize_pcSentenceWith_top_ofStructure (e : Encodable (Atom L ℕ)) [L.Structure ℕ]
    (g : ℕ → ℕ) :
    @SentenceInf.Realize (L.sum pcWitnessLanguage) ℕ (pcSentenceWith e ⊤) ℕ
      (@Language.sumStructure L pcWitnessLanguage ℕ _ (standardWitness g)) :=
  realize_pcSentenceWith_ofStructure e ⊤ g (by rw [body_top]; trivial)

/-! ### Canonical PC sentence -/

/-- The canonical **PC sentence** of a descriptive tree `T` on `Bool × ℕ`, built from
`Encodable.ofCountable (Atom L ℕ)`. -/
noncomputable def pcSentence [Countable (Atom L ℕ)] (T : tree (Bool × ℕ)) :
    (L.sum pcWitnessLanguage).Sentenceω :=
  pcSentenceWith (Encodable.ofCountable (Atom L ℕ)) T

/-- `pcSentence` is `pcSentenceWith` for `Encodable.ofCountable (Atom L ℕ)`. -/
theorem pcSentence_eq_pcSentenceWith [Countable (Atom L ℕ)] (T : tree (Bool × ℕ)) :
    pcSentence (L := L) T = pcSentenceWith (Encodable.ofCountable (Atom L ℕ)) T := (rfl)

/-- Completeness of `pcSentence` for any `L`-structure on `ℕ`. -/
theorem realize_pcSentence_ofStructure [Countable (Atom L ℕ)] (T : tree (Bool × ℕ))
    [L.Structure ℕ] (g : ℕ → ℕ)
    (h : (fun n => (queryCode (ofStructure L ℕ) n, g n)) ∈ body T) :
    @SentenceInf.Realize (L.sum pcWitnessLanguage) ℕ (pcSentence T) ℕ
      (@Language.sumStructure L pcWitnessLanguage ℕ _ (standardWitness g)) := by
  rw [queryCode_eq_queryCodeWith] at h
  exact realize_pcSentenceWith_ofStructure (Encodable.ofCountable (Atom L ℕ)) T g h

/-- Completeness of `pcSentence` for a relational configuration on `ℕ`. -/
theorem realize_pcSentence_standardWitness [L.IsRelational] [Countable (Atom L ℕ)]
    (T : tree (Bool × ℕ)) (c : RelationalConfiguration L ℕ) (g : ℕ → ℕ)
    (h : (fun n => (queryCode c n, g n)) ∈ body T) :
    @SentenceInf.Realize (L.sum pcWitnessLanguage) ℕ (pcSentence T) ℕ
      (@Language.sumStructure L pcWitnessLanguage ℕ c.toStructure (standardWitness g)) := by
  rw [queryCode_eq_queryCodeWith] at h
  exact realize_pcSentenceWith_standardWitness (Encodable.ofCountable (Atom L ℕ)) T c g h

/-- If `(queryCode (ofStructure L ℕ), g) ∈ body T`, then `ℕ` lies in the projective class of
`pcSentence T`. -/
theorem pcMem_pcSentence_of_mem_body [Countable (Atom L ℕ)] (T : tree (Bool × ℕ))
    [L.Structure ℕ] (g : ℕ → ℕ)
    (h : (fun n => (queryCode (ofStructure L ℕ) n, g n)) ∈ body T) :
    (LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).PCMem (pcSentence T) ℕ := by
  rw [queryCode_eq_queryCodeWith] at h
  exact pcMem_pcSentenceWith_of_mem_body (Encodable.ofCountable (Atom L ℕ)) T g h

/-- Soundness of `pcSentence` for any `L`-structure `M` with an expansion modeling
`pcSentence T`. -/
theorem exists_equiv_and_branch_of_realize_pcSentence [Countable (Atom L ℕ)]
    (T : tree (Bool × ℕ)) {M : Type w} [L.Structure M] [(L.sum pcWitnessLanguage).Structure M]
    [(LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).IsExpansionOn M]
    (h : SentenceInf.Realize (pcSentence (L := L) T) M) :
    ∃ (f : M ≃ ℕ) (g : ℕ → ℕ),
      (fun n => (queryCode (f.encodeVia (L := L)) n, g n)) ∈ body T := by
  simp_rw [queryCode_eq_queryCodeWith]
  exact exists_equiv_and_branch_of_realize_pcSentenceWith (Encodable.ofCountable (Atom L ℕ)) T h

/-- Soundness of `pcSentence` stated directly for projective-class membership `LHom.PCMem`. -/
theorem exists_equiv_and_branch_of_pcMem_pcSentence [Countable (Atom L ℕ)]
    (T : tree (Bool × ℕ)) {M : Type w} [L.Structure M]
    (h : (LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).PCMem (pcSentence T) M) :
    ∃ (f : M ≃ ℕ) (g : ℕ → ℕ),
      (fun n => (queryCode (f.encodeVia (L := L)) n, g n)) ∈ body T := by
  simp_rw [queryCode_eq_queryCodeWith]
  exact exists_equiv_and_branch_of_pcMem_pcSentenceWith (Encodable.ofCountable (Atom L ℕ)) T h

/-- Boundary check: `pcSentence ⊥` has no model. -/
theorem not_realize_pcSentence_bot [Countable (Atom L ℕ)] {M : Type w}
    [(L.sum pcWitnessLanguage).Structure M] :
    ¬ SentenceInf.Realize (pcSentence (L := L) ⊥) M :=
  not_realize_pcSentenceWith_bot (Encodable.ofCountable (Atom L ℕ))

/-- **Specification of the PC sentence of a descriptive tree.** Completeness holds on `ℕ` with
`standardWitness g`, and soundness holds in arbitrary universes `Type w` without invariance. -/
theorem exists_pcSentence [L.IsRelational] [Countable (Atom L ℕ)] (T : tree (Bool × ℕ)) :
    ∃ ψ : (L.sum pcWitnessLanguage).Sentenceω,
      (∀ (c : RelationalConfiguration L ℕ) (g : ℕ → ℕ),
        (fun n => (queryCode c n, g n)) ∈ body T →
        @SentenceInf.Realize (L.sum pcWitnessLanguage) ℕ ψ ℕ
          (@Language.sumStructure L pcWitnessLanguage ℕ c.toStructure (standardWitness g))) ∧
      (∀ (M : Type w) [L.Structure M] [pcWitnessLanguage.Structure M],
        SentenceInf.Realize ψ M →
        ∃ (f : M ≃ ℕ) (g : ℕ → ℕ),
          (fun n => (queryCode (f.encodeVia (L := L)) n, g n)) ∈ body T) :=
  ⟨pcSentence T, fun c g h => realize_pcSentence_standardWitness T c g h,
    fun _ _ _ h => exists_equiv_and_branch_of_realize_pcSentence T h⟩

end PCSentence

end TauCeti.RelationalConfiguration
