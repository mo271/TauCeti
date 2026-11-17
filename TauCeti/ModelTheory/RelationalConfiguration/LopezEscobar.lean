/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
public import TauCeti.ModelTheory.RelationalConfiguration.PCSentence
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.MeasureTheory.Constructions.Cylinders
import TauCeti.ModelTheory.Interpolation.Craig
import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap
import TauCeti.ModelTheory.Sublanguage

/-!
# The López–Escobar theorem

For a relational language `L` and a carrier `V`, the **López–Escobar theorem** identifies the
isomorphism-invariant sets of configurations measurable for the product σ-algebra with the model
classes of `L_{ω₁ω}` sentences.

We establish the hard direction (`lopez_escobar`) with **no countability hypothesis on `L` and no
cardinality hypothesis on `V`** (empty, finite, countably infinite, and uncountable carriers are
all covered):

* **Countably infinite `V` (`V ≃ ℕ`):** a set `B` measurable for the product σ-algebra depends on
  countably many atoms (`MeasurableSet.eq_preimage_restrict_countable`), hence pulls back from a
  countable relational sublanguage `L₀ := symbSublang ∅ R` via `LHom.reductConfiguration` (using
  extension by `false` along `symbSublangIncl ∅ R`, which is measurable and `Equiv.Perm V`-
  equivariant). In `L₀`, both `B₀` and `B₀ᶜ` are Borel in a Polish space, hence analytic and
  represented by descriptive trees `T₀, T₁` on `Bool × ℕ` (`exists_tree_of_analyticSet`). By
  soundness of `pcSentence` (`PCSentence.lean`) and isomorphism invariance of `B₀`, the two
  projective classes `LHom.sumInl.PCMem (pcSentence T₀)` and
  `LHom.sumInl.PCMem (pcSentence T₁)` are disjoint; `FirstOrder.Language.pcSeparation` supplies a
  single separating sentence `θ₀ : L₀.Sentenceω`, whose completeness puts `B₀ = modelsOf θ₀`.
  Translating `θ₀` back along `symbSublangIncl ∅ R` yields `B = modelsOf θ`.
* **Finite `V` (`V ≃ Fin m`, including `m = 0`):** by σ-algebra induction on `Pi.measurableSpace`,
  every product-measurable set `B ⊆ RelationalConfiguration L (Fin m)` is realized at the identity
  tuple `id : Fin m → Fin m` by a single `φ : L.BoundedFormulaω Empty m`. Existentially closing
  `distinct m ⊓ φ` (requiring the `m` witnesses to be pairwise distinct, hence a permutation of
  `Fin m`) recovers `B = modelsOf (distinct m ⊓ φ).exs` by isomorphism invariance. This handles
  arbitrary (possibly uncountable) `L` and `m = 0` uniformly.
* **Uncountable `V` (`¬ Countable V`):** a product-measurable set `B` depends on a countable set of
  atoms `I`, whose vertices lie in a countable subset `S ⊆ V`. Because `V \ S` is infinite, there
  is an involution `σ : Equiv.Perm V` mapping `S` into `V \ S` (built from `Equiv.sumComm` via
  `Equiv.Perm.viaEmbeddingHom`). For any two configurations `c, d` agreeing on all nullary atoms,
  combining `c` on `S`-tuples with `d` along `σ` on `σ(S)`-tuples gives a hybrid configuration `h`
  agreeing with `c` on `I` while `σ • h` agrees with `d` on `I`. Action invariance therefore forces
  `c ∈ B ↔ d ∈ B` (`mem_iff_of_restrict_finZero_eq_of_uncountable`), so `B` depends only on nullary
  atoms and pulls back from `RelationalConfiguration L (Fin 0)`, where σ-algebra induction yields a
  quantifier-free nullary sentence `φ : L.Sentenceω`.

On any countable carrier `V`, the easy direction (`measurableSet_modelsOf`,
`isomorphismInvariant_modelsOf`) matches the hard direction, yielding:

* `lopezEscobar_iff`: `MeasurableSet B ∧ IsomorphismInvariant B ↔ ∃ φ, B = modelsOf φ`;
* `lopezEscobar_action_iff`: the same using `MulAction.IsFixedBlock (Equiv.Perm V) B`;
* `measurableSet_iInf_invariants_iff_exists_modelsOf`: the invariant σ-algebra
  `⨅ σ : Equiv.Perm V, MeasurableSpace.invariants (σ • ·)` is exactly `Set.range modelsOf`.

Here `[Countable V]` cannot be dropped from the equivalence: on an uncountable carrier `V` with a
unary predicate `P`, `modelsOf (∀ x, P x)` is the singleton of the all-true configuration, which is
not measurable for the product σ-algebra since `mem_iff_of_restrict_finZero_eq_of_uncountable`
forces every invariant measurable set containing it to also contain the all-false configuration.

We also characterize invariant analytic classes on countably infinite carriers in countable
relational vocabularies as projective (`PC_{ω₁ω}`) classes (`analyticSet_iff_exists_pc`). All three
hypotheses (`[∀ n, Countable (L.Relations n)]`, `[Countable V]`, `[Infinite V]`) are sharp:
uncountably many unary predicates admit an invariant analytic singleton whose dependencies are
uncountable; on a finite carrier (e.g. `V = Fin 1` with countably many nullary relations, so
`RelationalConfiguration L V ≃ ℕ → Bool` and every set is invariant), `pcWitnessLanguage.Structure
V` is finite, so every `PC_{ω₁ω}` class is a finite union of Borel sets, hence Borel, missing
non-Borel analytic sets; and on any uncountable carrier `V` with a unary predicate `P`, the
projective class of `∃ x, P x` contains configurations not fixed by `Equiv.Perm V`, which cannot be
analytic (`perm_smul_eq_of_mem_analyticSet_of_uncountable` in `InvariantSeparation.lean`).

## Main results

* `TauCeti.RelationalConfiguration.mem_iff_of_restrict_finZero_eq_of_uncountable`: on an uncountable
  carrier, every `Equiv.Perm V`-invariant product-measurable set depends only on nullary atoms.
* `TauCeti.RelationalConfiguration.lopez_escobar`: every isomorphism-invariant product-measurable
  set of configurations is `modelsOf φ` for some `φ : L.Sentenceω`, for every relational `L` and
  every carrier `V`.
* `TauCeti.RelationalConfiguration.lopezEscobar_iff`, `lopezEscobar_action_iff`, and
  `measurableSet_iInf_invariants_iff_exists_modelsOf`: the two-sided characterizations on any
  countable carrier `V`.
* `TauCeti.RelationalConfiguration.analyticSet_iff_exists_pc`: on a countably infinite carrier in a
  countable relational language, an isomorphism-invariant set is analytic iff it is the projective
  class of some `ψ : (L.sum pcWitnessLanguage).Sentenceω`.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fund. Math. 57
  (1965), 253–272.
* R. L. Vaught, *Invariant sets in topology and logic*, Fund. Math. 82 (1974), 269–294,
  Corollary 3.3.
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 16.8.
* S. Gao, *Invariant Descriptive Set Theory*, CRC Press, 2009, Chapter 11.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Corollary 4.23, Lemma 4.24, and Theorem 4.26.
-/

public section

universe u v w w'

open Descriptive Descriptive.Tree FirstOrder FirstOrder.Language MeasureTheory Set
open scoped Pointwise

namespace TauCeti.RelationalConfiguration

/-! ### Extension by `false` along an injective language map -/

section ExtendFalse

variable {L₀ : Language.{u, v}} {L : Language.{u, v}} {V : Type w}

/-- Extend a configuration of `L₀` along `g : L₀ →ᴸ L` by setting atoms outside the range of
`g.onAtom` to `false`. -/
private noncomputable def extendFalse (g : L₀ →ᴸ L) (c : RelationalConfiguration L₀ V) :
    RelationalConfiguration L V :=
  mk (Function.extend g.onAtom c.eval fun _ => false)

private theorem eval_extendFalse_onAtom {g : L₀ →ᴸ L} (hg : g.Injective)
    (c : RelationalConfiguration L₀ V) (a : Atom L₀ V) :
    (extendFalse g c).eval (g.onAtom a) = c.eval a := by
  rw [extendFalse, eval_mk, hg.onAtom_injective.extend_apply]

private theorem reductConfiguration_extendFalse {g : L₀ →ᴸ L} (hg : g.Injective)
    (c : RelationalConfiguration L₀ V) :
    g.reductConfiguration (extendFalse g c) = c :=
  ext fun a => by rw [LHom.eval_reductConfiguration, eval_extendFalse_onAtom hg]

private theorem measurable_extendFalse (g : L₀ →ᴸ L) :
    Measurable (extendFalse (V := V) g) := by
  refine measurable_iff.2 fun a => ?_
  classical
  by_cases ha : ∃ b : Atom L₀ V, g.onAtom b = a
  · simp only [extendFalse, eval_mk, Function.extend_def, ha, ↓reduceDIte]
    exact measurable_eval _
  · simp only [extendFalse, eval_mk, Function.extend_def, ha, ↓reduceDIte]
    exact measurable_const

private theorem extendFalse_perm_smul {g : L₀ →ᴸ L} (hg : g.Injective) (σ : Equiv.Perm V)
    (c : RelationalConfiguration L₀ V) :
    extendFalse g (σ • c) = σ • extendFalse g c := by
  ext a
  classical
  rw [eval_perm_smul]
  by_cases ha : ∃ b : Atom L₀ V, g.onAtom b = a
  · obtain ⟨b, rfl⟩ := ha
    rw [eval_extendFalse_onAtom hg, eval_perm_smul, ← LHom.onAtom_map,
      eval_extendFalse_onAtom hg]
  · have ha' : ¬ ∃ b : Atom L₀ V, g.onAtom b = a.map σ.symm := fun ⟨b, hb⟩ =>
      ha ⟨b.map σ, by rw [LHom.onAtom_map, hb, ← Atom.map_comp]; simp⟩
    rw [extendFalse, eval_mk, Function.extend_apply' _ _ a ha,
      extendFalse, eval_mk, Function.extend_apply' _ _ (a.map σ.symm) ha']

end ExtendFalse

/-! ### Carrier transport of configurations and model classes -/

section CarrierTransport

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w} {W : Type w'}

/-- A bijection `e : V ≃ W` induces an `L`-isomorphism
`(c.restrict e).toStructure ≃[L] c.toStructure`. -/
private def equivOfRestrict (e : V ≃ W) (c : RelationalConfiguration L W) :
    @Language.Equiv L V W (c.restrict e).toStructure c.toStructure :=
  let : L.Structure V := (c.restrict e).toStructure
  let : L.Structure W := c.toStructure
  { toEquiv := e
    map_fun' := fun f _ => isEmptyElim f
    map_rel' := fun R x => by
      simp only [toStructure_relMap, eval_restrict, Atom.map_atom]
      rfl }

/-- Restricting along a bijection `e : V ≃ W` preserves model classes. -/
private theorem mem_modelsOf_restrict_iff (e : V ≃ W) (φ : L.SentenceInf ℕ)
    (c : RelationalConfiguration L W) :
    c.restrict e ∈ modelsOf φ ↔ c ∈ modelsOf φ :=
  (equivOfRestrict e c).mem_modelsOf_iff φ

/-- Preimage of an isomorphism-invariant set along `restrict e` is isomorphism invariant. -/
private theorem isomorphismInvariant_preimage_restrict (e : V ≃ W)
    {B : Set (RelationalConfiguration L V)} (hinv : IsomorphismInvariant B) :
    IsomorphismInvariant (restrict e ⁻¹' B) := by
  rw [isomorphismInvariant_iff_isInvariantBlock] at hinv ⊢
  intro σ
  rintro _ ⟨c, hc, rfl⟩
  rw [mem_preimage] at hc ⊢
  have hconj : (σ • c).restrict e = (e.symm.permCongr σ) • (c.restrict e) := by
    ext a
    simp only [eval_restrict, eval_perm_smul, ← Atom.map_comp]
    congr 1
    exact congrArg (fun f => a.map f)
      (funext fun v => (e.apply_symm_apply (σ.symm (e v))).symm)
  rw [hconj]
  exact hinv (e.symm.permCongr σ) (smul_mem_smul_set hc)

/-- Transport a `modelsOf` witness along a carrier bijection `e : V ≃ W`. -/
private theorem exists_modelsOf_of_equiv (e : V ≃ W)
    {B : Set (RelationalConfiguration L V)}
    (h : ∃ φ : L.Sentenceω, restrict e ⁻¹' B = modelsOf φ) :
    ∃ φ : L.Sentenceω, B = modelsOf φ := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ, ?_⟩
  ext c
  have hce : (c.restrict e.symm).restrict e = c := by ext a; simp [← Atom.map_comp]
  have hc : c ∈ B ↔ c.restrict e.symm ∈ restrict e ⁻¹' B := by rw [mem_preimage, hce]
  rw [hc, hφ, mem_modelsOf_restrict_iff]

end CarrierTransport

/-! ### Countably infinite case (`V = ℕ`) -/

section NatCase

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Countable-vocabulary López–Escobar theorem on `ℕ`.** -/
private theorem lopez_escobar_nat_of_countable [∀ n, Countable (L.Relations n)]
    {B : Set (RelationalConfiguration L ℕ)} (hB : MeasurableSet B)
    (hinv : IsomorphismInvariant B) :
    ∃ φ : L.Sentenceω, B = modelsOf φ := by
  obtain ⟨T₀, hT₀⟩ := exists_tree_of_analyticSet hB.analyticSet
  obtain ⟨T₁, hT₁⟩ := exists_tree_of_analyticSet hB.compl.analyticSet
  have hdisj : ∀ (M : Type) [L.Structure M] [Nonempty M] [Countable M],
      (LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).PCMem (pcSentence T₀) M →
      ¬ (LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).PCMem (pcSentence T₁) M := by
    intro M _ _ _ h₀ h₁
    obtain ⟨f₀, g₀, hg₀⟩ := exists_equiv_and_branch_of_pcMem_pcSentence T₀ h₀
    obtain ⟨f₁, g₁, hg₁⟩ := exists_equiv_and_branch_of_pcMem_pcSentence T₁ h₁
    have hm₀ : f₀.encodeVia (L := L) ∈ B := by rw [hT₀]; exact ⟨g₀, hg₀⟩
    have hm₁ : f₁.encodeVia (L := L) ∈ Bᶜ := by rw [hT₁]; exact ⟨g₁, hg₁⟩
    have hiso : isoSetoid L ℕ (f₀.encodeVia (L := L)) (f₁.encodeVia (L := L)) :=
      (f₀.isoSetoid_encodeVia_iff f₁).2 ⟨Language.Equiv.refl L M⟩
    exact hm₁ (hinv.mem_iff hiso |>.1 hm₀)
  obtain ⟨θ, hθ₀, hθ₁⟩ := pcSeparation.{u, v, 0, 0, 0, 0, 0, 0}
    (pcSentence T₀) (pcSentence T₁) hdisj
  refine ⟨θ, ?_⟩
  ext c
  let := c.toStructure
  rw [mem_modelsOf]
  constructor
  · intro hc
    rw [hT₀] at hc
    obtain ⟨g, hg⟩ := hc
    exact hθ₀ ℕ (pcMem_pcSentence_of_mem_body T₀ g (by simpa [ofStructure_toStructure] using hg))
  · intro hθc
    by_contra hc
    have hc' : c ∈ Bᶜ := hc
    rw [hT₁] at hc'
    obtain ⟨g, hg⟩ := hc'
    exact hθ₁ ℕ (pcMem_pcSentence_of_mem_body T₁ g (by simpa [ofStructure_toStructure] using hg))
      hθc

/-- **López–Escobar theorem on `ℕ` for arbitrary relational languages**, reducing to a countable
symbol sublanguage via `MeasurableSet.eq_preimage_restrict_countable`. -/
private theorem lopez_escobar_nat {B : Set (RelationalConfiguration L ℕ)}
    (hB : MeasurableSet B) (hinv : IsomorphismInvariant B) :
    ∃ φ : L.Sentenceω, B = modelsOf φ := by
  obtain ⟨I, t, hI, hBI⟩ := hB.eq_preimage_restrict_countable
  let symOf : Atom L ℕ → Σ n, L.Relations n := fun a => ⟨a.1, a.2.1⟩
  let R : Set (Σ n, L.Relations n) := symOf '' I
  have hR : R.Countable := hI.image symOf
  let g : symbSublang ∅ R →ᴸ L := symbSublangIncl ∅ R
  have hg : g.Injective := symbSublangIncl_injective ∅ R
  have hagree : ∀ c₁ c₂ : RelationalConfiguration L ℕ,
      g.reductConfiguration c₁ = g.reductConfiguration c₂ → (c₁ ∈ B ↔ c₂ ∈ B) := by
    intro c₁ c₂ heq
    have hdom : I.domRestrict c₁ = I.domRestrict c₂ := by
      funext ⟨a, ha⟩
      let b : Atom (symbSublang ∅ R) ℕ := atom ⟨a.2.1, ⟨a, ha, rfl⟩⟩ a.2.2
      have hgb : g.onAtom b = a := by
        rw [LHom.onAtom_atom, symbSublangIncl_onRelation, atom_def]; rfl
      have hval := congrArg (fun c : RelationalConfiguration (symbSublang ∅ R) ℕ => c.eval b) heq
      rw [LHom.eval_reductConfiguration, LHom.eval_reductConfiguration, hgb,
        eval_def, eval_def] at hval
      exact hval
    rw [hBI]; exact iff_of_eq (congrArg (· ∈ t) hdom)
  let B₀ : Set (RelationalConfiguration (symbSublang ∅ R) ℕ) := extendFalse g ⁻¹' B
  have hB₀ : MeasurableSet B₀ := hB.preimage (measurable_extendFalse g)
  have hinv₀ : IsomorphismInvariant B₀ := by
    rw [isomorphismInvariant_iff_isInvariantBlock] at hinv ⊢
    intro σ
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_preimage, extendFalse_perm_smul hg]
    exact hinv σ (smul_mem_smul_set hc)
  have : Countable R := hR.to_subtype
  have : ∀ n, Countable ((symbSublang (∅ : Set (Σ k, L.Functions k)) R).Relations n) := fun n =>
    Function.Injective.countable (f := fun r => (⟨n, r⟩ : Σ k, _)) fun _ _ h =>
      eq_of_heq (Sigma.mk.inj_iff.1 h).2
  obtain ⟨φ₀, hφ₀⟩ := lopez_escobar_nat_of_countable hB₀ hinv₀
  refine ⟨g.onBoundedFormulaInf φ₀, ?_⟩
  ext c
  rw [mem_modelsOf, LHom.realize_sentenceInf_reductConfiguration, ← mem_modelsOf, ← hφ₀]
  exact hagree c (extendFalse g (g.reductConfiguration c))
    (reductConfiguration_extendFalse hg _).symm

end NatCase

/-! ### Finite and nullary cases -/

section FiniteCase

variable {L : Language.{u, v}}

/-- Given a formula `φ` tracking a Boolean predicate `f : α → Bool` across a family, every subset
`t : Set Bool` is tracked uniformly by one of `⊤`, `φ`, `φ.not`, or `⊥`. -/
private theorem exists_formula_of_bool_set_family {m : ℕ} {α : Type*}
    (t : Set Bool) (f : α → Bool) (r : L.BoundedFormulaω Empty m → α → Prop)
    (h_top : ∀ x, r ⊤ x) (h_bot : ∀ x, ¬ r ⊥ x)
    (φ : L.BoundedFormulaω Empty m)
    (h_pos : ∀ x, f x = true ↔ r φ x) (h_neg : ∀ x, f x = false ↔ r φ.not x) :
    ∃ ψ : L.BoundedFormulaω Empty m, ∀ x, f x ∈ t ↔ r ψ x := by
  by_cases ht : true ∈ t <;> by_cases hf : false ∈ t
  · exact ⟨⊤, fun x => ⟨fun _ => h_top x, fun _ => by cases f x <;> assumption⟩⟩
  · exact ⟨φ, fun x => (by cases f x <;> simp [ht, hf] : f x ∈ t ↔ f x = true).trans (h_pos x)⟩
  · exact ⟨φ.not,
      fun x => (by cases f x <;> simp [ht, hf] : f x ∈ t ↔ f x = false).trans (h_neg x)⟩
  · exact ⟨⊥, fun x => ⟨fun h => by cases hb : f x <;> (rw [hb] at h; contradiction),
      fun h => (h_bot x h).elim⟩⟩

variable [L.IsRelational]

/-- Every product-measurable set of configurations on `Fin 0` is realized by a single `L_{ω₁ω}`
sentence uniformly across all carriers `W` (pulling back along `restrict Fin.elim0`). -/
private theorem exists_nullary_sentence_of_measurableSet
    {B₀ : Set (RelationalConfiguration L (Fin 0))} (hB₀ : MeasurableSet B₀) :
    ∃ φ : L.Sentenceω, ∀ {W : Type w} (c : RelationalConfiguration L W),
      c.restrict Fin.elim0 ∈ B₀ ↔ c ∈ modelsOf φ := by
  let P (s : Set (Atom L (Fin 0) → Bool)) : Prop :=
    ∃ φ : L.Sentenceω, ∀ {W : Type w} (c : RelationalConfiguration L W),
      (c.restrict Fin.elim0).eval ∈ s ↔ c ∈ modelsOf φ
  let m₀ : MeasurableSpace (Atom L (Fin 0) → Bool) :=
    { MeasurableSet' := P
      measurableSet_empty := ⟨⊥, fun c => by simp⟩
      measurableSet_compl := fun s ⟨φ, hφ⟩ => ⟨φ.not, fun c => by simp [hφ]⟩
      measurableSet_iUnion := fun f hf => by
        choose φs hφs using hf
        exact ⟨BoundedFormulaInf.iSup φs, fun c => by simp [hφs]⟩ }
  have hle : MeasurableSpace.pi ≤ m₀ := by
    refine iSup_le fun a => ?_
    rintro _ ⟨t, -, rfl⟩
    induction a using Atom.induction_atom with
    | @h n R x =>
      cases n with
      | zero =>
        by_cases ht : true ∈ t <;> by_cases hf : false ∈ t
        · exact ⟨⊤, fun c => by
            simp only [modelsOf_top, mem_univ, iff_true, mem_preimage]
            cases (c.restrict Fin.elim0).eval (atom R x) <;> assumption⟩
        · refine ⟨BoundedFormulaInf.rel R Fin.elim0, fun {W} c => ?_⟩
          have hmem : ∀ b : Bool, b ∈ t ↔ b = true := fun b => by cases b <;> simp [ht, hf]
          simp only [mem_preimage, hmem, mem_modelsOf, SentenceInf.realize_def,
            FormulaInf.realize_def, BoundedFormulaInf.realize_rel, toStructure_relMap,
            eval_restrict, Atom.map_atom]
          exact iff_of_eq (congrArg (fun y : Fin 0 → W => c.eval (atom R y) = true)
            (Subsingleton.elim _ _))
        · refine ⟨(BoundedFormulaInf.rel R Fin.elim0).not, fun {W} c => ?_⟩
          have hmem : ∀ b : Bool, b ∈ t ↔ b = false := fun b => by cases b <;> simp [ht, hf]
          simp only [mem_preimage, hmem, mem_modelsOf, SentenceInf.realize_def,
            FormulaInf.realize_def, BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_rel,
            toStructure_relMap, eval_restrict, Atom.map_atom, Bool.not_eq_true]
          exact iff_of_eq (congrArg (fun y : Fin 0 → W => c.eval (atom R y) = false)
            (Subsingleton.elim _ _))
        · exact ⟨⊥, fun c => by
            rw [modelsOf_bot, mem_empty_iff_false, iff_false, mem_preimage]
            cases (c.restrict Fin.elim0).eval (atom R x) <;> assumption⟩
      | succ k => exact Fin.elim0 (x 0)
  obtain ⟨φ, hφ⟩ := hle (mk ⁻¹' B₀) (hB₀.preimage measurable_mk)
  refine ⟨φ, fun c => ?_⟩
  have hmk : mk (c.restrict Fin.elim0).eval = c.restrict Fin.elim0 := ext fun a => eval_mk _ a
  simpa [hmk] using hφ c

/-- Every product-measurable set of configurations on `Fin m` is defined at the identity tuple
`id : Fin m → Fin m` by a single `L.BoundedFormulaω Empty m`. -/
private theorem exists_formula_on_fin {m : ℕ} {B : Set (RelationalConfiguration L (Fin m))}
    (hB : MeasurableSet B) :
    ∃ φ : L.BoundedFormulaω Empty m, ∀ c : RelationalConfiguration L (Fin m),
      c ∈ B ↔ @BoundedFormulaInf.Realize L ℕ Empty (Fin m) c.toStructure m φ Empty.elim id := by
  let P (s : Set (Atom L (Fin m) → Bool)) : Prop :=
    ∃ φ : L.BoundedFormulaω Empty m, ∀ c : RelationalConfiguration L (Fin m),
      c.eval ∈ s ↔ @BoundedFormulaInf.Realize L ℕ Empty (Fin m) c.toStructure m φ Empty.elim id
  let m₀ : MeasurableSpace (Atom L (Fin m) → Bool) :=
    { MeasurableSet' := P
      measurableSet_empty := ⟨⊥, fun c => by simp⟩
      measurableSet_compl := fun s ⟨φ, hφ⟩ => ⟨φ.not, fun c => by simp [hφ]⟩
      measurableSet_iUnion := fun f hf => by
        choose φs hφs using hf
        exact ⟨BoundedFormulaInf.iSup φs, fun c => by simp [hφs]⟩ }
  have hle : MeasurableSpace.pi ≤ m₀ := by
    refine iSup_le fun a => ?_
    rintro _ ⟨t, -, rfl⟩
    induction a using Atom.induction_atom with
    | @h n R x =>
      exact exists_formula_of_bool_set_family t
        (fun c : RelationalConfiguration L (Fin m) => c.eval (atom R x))
        (fun ψ c => @BoundedFormulaInf.Realize L ℕ Empty (Fin m) c.toStructure m ψ Empty.elim id)
        (fun _ => by simp) (fun _ => by simp)
        (BoundedFormulaInf.rel R fun i => .var (.inr (x i)))
        (fun c => by simp) (fun c => by simp)
  obtain ⟨φ, hφ⟩ := hle (mk ⁻¹' B) (hB.preimage measurable_mk)
  refine ⟨φ, fun c => ?_⟩
  have hmk : mk c.eval = c := ext fun a => eval_mk _ a
  simpa [hmk] using hφ c

/-- **López–Escobar theorem on `Fin m`** (including `m = 0`), for arbitrary relational `L`. -/
private theorem lopez_escobar_fin {m : ℕ} {B : Set (RelationalConfiguration L (Fin m))}
    (hB : MeasurableSet B) (hinv : IsomorphismInvariant B) :
    ∃ φ : L.Sentenceω, B = modelsOf φ := by
  obtain ⟨φ, hφ⟩ := exists_formula_on_fin hB
  let distinct : L.BoundedFormulaω Empty m :=
    BoundedFormulaInf.iInfAlong (TauCeti.IndexCoding.ofEncodable {p : Fin m × Fin m // p.1 ≠ p.2})
      fun p => (BoundedFormulaInf.equal (.var (.inr p.1.1)) (.var (.inr p.1.2))).not
  have hdist : ∀ (c : RelationalConfiguration L (Fin m)) (xs : Fin m → Fin m),
      @BoundedFormulaInf.Realize L ℕ Empty (Fin m) c.toStructure m distinct Empty.elim xs ↔
        Function.Injective xs := by
    intro c xs
    let := c.toStructure
    simp only [distinct, BoundedFormulaInf.realize_iInfAlong, BoundedFormulaInf.realize_not,
      BoundedFormulaInf.realize_equal, Term.realize_var, Sum.elim_inr, Function.Injective]
    exact ⟨fun h i j hij => by_contra fun hne => h ⟨(i, j), hne⟩ hij,
      fun h ⟨⟨_, _⟩, hne⟩ hij => hne (h hij)⟩
  refine ⟨(distinct ⊓ φ).exs, ?_⟩
  ext c
  let := c.toStructure
  rw [mem_modelsOf, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_exs]
  simp only [BoundedFormulaInf.realize_inf, hdist]
  constructor
  · intro hc
    exact ⟨id, Function.injective_id, (hφ c).1 hc⟩
  · rintro ⟨xs, hinj, hreal⟩
    let σ : Equiv.Perm (Fin m) := Equiv.ofBijective xs (Finite.injective_iff_bijective.1 hinj)
    have hreal' : @BoundedFormulaInf.Realize L ℕ Empty (Fin m) (c.restrict σ).toStructure m
        φ Empty.elim id := by
      let hiso := equivOfRestrict σ c
      have htr := @StrongHomClass.realize_boundedFormulaInf L ℕ Empty m (Fin m) (Fin m)
        (c.restrict σ).toStructure c.toStructure _ _ _ hiso φ Empty.elim id
      have hcomp : hiso ∘ Empty.elim = Empty.elim := Subsingleton.elim _ _
      have hxs : (⇑hiso ∘ id : Fin m → Fin m) = xs := rfl
      rw [hcomp, hxs] at htr
      exact htr.1 hreal
    have hσ : c.restrict σ = σ⁻¹ • c := by
      ext a; simp [eval_perm_smul, eval_restrict, Equiv.Perm.inv_def]
    have hmem : σ⁻¹ • c ∈ B := (hφ (σ⁻¹ • c)).2 (hσ ▸ hreal')
    have hperm : isoSetoid L (Fin m) (σ⁻¹ • c) c :=
      isoSetoid_iff_exists_perm_smul_eq.2 ⟨σ, by simp⟩
    exact hinv.mem_iff hperm |>.1 hmem

end FiniteCase

/-! ### Uncountable carriers -/

section UncountableCase

variable {L : Language.{u, v}} {V : Type w}

/-- Hybrid configuration combining `c` on nullary atoms and `S`-tuples with `d` pulled back along
an involution `σ` on `σ(S)`-tuples. -/
private noncomputable def patchConfig (S : Set V) (σ : Equiv.Perm V)
    (c d : RelationalConfiguration L V) : RelationalConfiguration L V := by
  classical
  exact mk fun a =>
    if a.1 = 0 then c.eval a
    else if ∀ i, a.2.2 i ∈ S then c.eval a
    else if ∀ i, σ (a.2.2 i) ∈ S then d.eval (a.map σ)
    else false

private theorem eval_patchConfig_of_mem {S : Set V} {σ : Equiv.Perm V}
    {c d : RelationalConfiguration L V} {a : Atom L V} (haS : ∀ i, a.2.2 i ∈ S) :
    (patchConfig S σ c d).eval a = c.eval a := by
  classical
  dsimp only [patchConfig]
  rw [eval_mk]
  split_ifs <;> rfl

private theorem eval_smul_patchConfig_of_mem {S : Set V} {σ : Equiv.Perm V}
    (hσ_symm : σ.symm = σ) (hσ_out : ∀ {v}, v ∈ S → σ v ∉ S)
    {c d : RelationalConfiguration L V}
    (hcd : c.restrict Fin.elim0 = d.restrict Fin.elim0)
    {a : Atom L V} (haS : ∀ i, a.2.2 i ∈ S) :
    (σ • patchConfig S σ c d).eval a = d.eval a := by
  classical
  have hσ_inv : ∀ v, σ (σ v) = v := fun v => by simpa [hσ_symm] using σ.apply_symm_apply v
  rw [eval_perm_smul, hσ_symm]
  induction a using Atom.induction_atom with
  | @h n R x =>
    cases n with
    | zero =>
      have hnull := congrArg (fun k : RelationalConfiguration L (Fin 0) =>
        k.eval (atom R Fin.elim0)) hcd
      simp only [eval_restrict, Atom.map_atom] at hnull
      have hmap : (atom R x).map σ = atom R x := by
        rw [Atom.map_atom]; congr 1; exact Subsingleton.elim _ _
      have hheval : (patchConfig S σ c d).eval (atom R x) = c.eval (atom R x) := by
        dsimp only [patchConfig]; rw [eval_mk]; simp [atom_def]
      have hx0 : x = Fin.elim0 ∘ (Fin.elim0 : Fin 0 → Fin 0) := Subsingleton.elim _ _
      rw [hmap, hheval, hx0]
      exact hnull
    | succ k =>
      rw [Atom.map_atom]
      have haS' : ∀ i : Fin (k + 1), x i ∈ S := fun i => by rw [atom_def] at haS; exact haS i
      have hnot0 : (atom R (⇑σ ∘ x)).1 ≠ 0 := by rw [atom_def]; exact Nat.succ_ne_zero k
      have hnotS : ¬ ∀ i, (atom R (⇑σ ∘ x)).2.2 i ∈ S := by
        rw [atom_def]; exact fun hAll => hσ_out (haS' 0) (hAll 0)
      have hbackS : ∀ i, σ ((atom R (⇑σ ∘ x)).2.2 i) ∈ S := by
        rw [atom_def]; exact fun i => by simpa [hσ_inv] using haS' i
      have hmap : (atom R (⇑σ ∘ x)).map σ = atom R x := by
        rw [Atom.map_atom]; congr 1; funext i; exact hσ_inv (x i)
      dsimp only [patchConfig]
      rw [eval_mk]
      simp only [hnot0, hnotS, hbackS, implies_true, ↓reduceIte, hmap]

/-- Every permutation-invariant product-measurable set on an uncountable carrier depends only on
the nullary atoms: configurations with the same nullary restriction belong to `B` together. No
`L.IsRelational` hypothesis is needed. -/
theorem mem_iff_of_restrict_finZero_eq_of_uncountable (hunc : ¬ Countable V)
    {B : Set (RelationalConfiguration L V)} (hB : MeasurableSet B)
    (hinv : MulAction.IsFixedBlock (Equiv.Perm V) B)
    {c d : RelationalConfiguration L V}
    (hcd : c.restrict Fin.elim0 = d.restrict Fin.elim0) :
    c ∈ B ↔ d ∈ B := by
  classical
  obtain ⟨I, t, hI, hBI⟩ := hB.eq_preimage_restrict_countable
  let S : Set V := ⋃ a ∈ I, Set.range a.2.2
  have hS : S.Countable := hI.biUnion fun a _ => Set.countable_range a.2.2
  have hVSc : ¬ Countable (↥(Sᶜ : Set V)) := fun hSc =>
    hunc (Set.countable_univ_iff.1 (by rw [← union_compl_self S]; exact hS.union hSc))
  have : Infinite (↥(Sᶜ : Set V)) := not_finite_iff_infinite.1 fun hf =>
    hVSc (@Finite.to_countable _ hf)
  have : Countable S := hS.to_subtype
  let j : S ↪ (↥(Sᶜ : Set V)) :=
    (Equiv.ofInjective _ (Countable.exists_injective_nat S).choose_spec |>.toEmbedding).trans
      ((Function.Embedding.subtype _).trans (Infinite.natEmbedding (↥(Sᶜ : Set V))))
  have he_inj : Function.Injective (Sum.elim (Subtype.val : S → V) (fun x => (j x).1)) := by
    rintro (x | x) (y | y) hxy <;> dsimp only [Sum.elim] at hxy
    · exact congrArg Sum.inl (Subtype.ext hxy)
    · exact ((j y).2 (hxy ▸ x.2)).elim
    · exact ((j x).2 (hxy.symm ▸ y.2)).elim
    · exact congrArg Sum.inr (j.injective (Subtype.ext hxy))
  let e : S ⊕ S ↪ V := ⟨Sum.elim Subtype.val (fun x => (j x).1), he_inj⟩
  let σ : Equiv.Perm V := Equiv.Perm.viaEmbeddingHom e (Equiv.sumComm S S)
  have hσ_symm : σ.symm = σ := by
    rw [← Equiv.Perm.inv_def, ← map_inv]; rfl
  have hσ_out : ∀ {v}, v ∈ S → σ v ∉ S := fun {v} hv => by
    have hval := Equiv.Perm.viaEmbedding_apply (Equiv.sumComm S S) (ι := e) (Sum.inl ⟨v, hv⟩)
    simpa [σ, Equiv.Perm.viaEmbeddingHom_apply, e] using hval ▸ (j ⟨v, hv⟩).2
  let h := patchConfig S σ c d
  have h_c : I.domRestrict h = I.domRestrict c := funext fun ⟨a, ha⟩ => by
    have hval := eval_patchConfig_of_mem (S := S) (σ := σ) (c := c) (d := d)
      fun i => mem_biUnion ha (mem_range_self i)
    rwa [eval_def, eval_def] at hval
  have h_d : I.domRestrict (σ • h) = I.domRestrict d := funext fun ⟨a, ha⟩ => by
    have hval := eval_smul_patchConfig_of_mem hσ_symm hσ_out hcd
      fun i => mem_biUnion ha (mem_range_self i)
    rwa [eval_def, eval_def] at hval
  have hhc : h ∈ B ↔ c ∈ B := by rw [hBI]; exact iff_of_eq (congrArg (· ∈ t) h_c)
  have hhd : σ • h ∈ B ↔ d ∈ B := by rw [hBI]; exact iff_of_eq (congrArg (· ∈ t) h_d)
  have hσh : h ∈ B ↔ σ • h ∈ B :=
    ⟨fun hh => (hinv σ) ▸ smul_mem_smul_set (a := σ) hh,
      fun hh => inv_smul_smul σ h ▸ (hinv σ⁻¹) ▸ smul_mem_smul_set (a := σ⁻¹) hh⟩
  exact hhc.symm.trans (hσh.trans hhd)

/-- **López–Escobar theorem on an uncountable carrier**: every isomorphism-invariant
product-measurable set depends only on nullary atoms and is defined by a quantifier-free nullary
sentence. -/
private theorem lopez_escobar_of_uncountable [L.IsRelational] (hunc : ¬ Countable V)
    {B : Set (RelationalConfiguration L V)} (hB : MeasurableSet B)
    (hinv : IsomorphismInvariant B) :
    ∃ φ : L.Sentenceω, B = modelsOf φ := by
  let B₀ : Set (RelationalConfiguration L (Fin 0)) := extend (Fin.elim0 : Fin 0 → V) ⁻¹' B
  have hB₀ : MeasurableSet B₀ := hB.preimage (measurable_extend Fin.elim0)
  obtain ⟨φ, hφ⟩ := exists_nullary_sentence_of_measurableSet (L := L) hB₀
  refine ⟨φ, ?_⟩
  ext c
  rw [← hφ c, mem_preimage]
  have hfix : MulAction.IsFixedBlock (Equiv.Perm V) B :=
    isomorphismInvariant_iff_isFixedBlock.1 hinv
  have hrest : ((c.restrict Fin.elim0).extend (Fin.elim0 : Fin 0 → V)).restrict Fin.elim0 =
      c.restrict Fin.elim0 :=
    restrict_extend (Function.injective_of_subsingleton (Fin.elim0 : Fin 0 → V)) _
  exact (mem_iff_of_restrict_finZero_eq_of_uncountable hunc hB hfix hrest).symm

end UncountableCase

/-! ### The López–Escobar theorem (all relational languages, all carriers) -/

section Main

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-- **The López–Escobar theorem (hard direction).** For every relational language `L` (possibly
uncountable) and every carrier `V` (empty, finite, countably infinite, or uncountable), every
isomorphism-invariant set of configurations measurable for the product σ-algebra is the model class
of a single `L_{ω₁ω}` sentence. -/
theorem lopez_escobar {B : Set (RelationalConfiguration L V)} (hB : MeasurableSet B)
    (hinv : IsomorphismInvariant B) :
    ∃ φ : L.Sentenceω, B = modelsOf φ := by
  by_cases hC : Countable V
  · by_cases hF : Finite V
    · obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin V
      exact exists_modelsOf_of_equiv e
        (lopez_escobar_fin (hB.preimage (measurable_restrict e))
          (isomorphismInvariant_preimage_restrict e hinv))
    · have : Infinite V := not_finite_iff_infinite.1 hF
      obtain ⟨e⟩ : Nonempty (V ≃ ℕ) := nonempty_equiv_of_countable
      exact exists_modelsOf_of_equiv e
        (lopez_escobar_nat (hB.preimage (measurable_restrict e))
          (isomorphismInvariant_preimage_restrict e hinv))
  · exact lopez_escobar_of_uncountable hC hB hinv

/-- **The López–Escobar theorem** on any countable carrier `V`, for every relational language `L`:
a set of configurations is product-measurable and isomorphism-invariant iff it is the model class
of a single `L_{ω₁ω}` sentence. -/
theorem lopezEscobar_iff [Countable V] {B : Set (RelationalConfiguration L V)} :
    (MeasurableSet B ∧ IsomorphismInvariant B) ↔ ∃ φ : L.Sentenceω, B = modelsOf φ :=
  ⟨fun ⟨hB, hinv⟩ => lopez_escobar hB hinv,
    fun ⟨φ, hφ⟩ => hφ ▸ ⟨measurableSet_modelsOf φ, isomorphismInvariant_modelsOf φ⟩⟩

/-- **The López–Escobar theorem (logic-action form)** on any countable carrier `V`, for every
relational language `L`. -/
theorem lopezEscobar_action_iff [Countable V] {B : Set (RelationalConfiguration L V)} :
    (MeasurableSet B ∧ MulAction.IsFixedBlock (Equiv.Perm V) B) ↔
      ∃ φ : L.Sentenceω, B = modelsOf φ := by
  rw [← isomorphismInvariant_iff_isFixedBlock]
  exact lopezEscobar_iff

/-- **The invariant σ-algebra is the definable one.** On any countable carrier `V` and for every
relational language `L`, the sets measurable for the invariant σ-algebra
`⨅ σ : Equiv.Perm V, MeasurableSpace.invariants (σ • ·)` are precisely the model classes of
`L_{ω₁ω}` sentences. -/
theorem measurableSet_iInf_invariants_iff_exists_modelsOf [Countable V]
    (B : Set (RelationalConfiguration L V)) :
    MeasurableSet[⨅ σ : Equiv.Perm V,
        MeasurableSpace.invariants (fun c : RelationalConfiguration L V => σ • c)] B ↔
      ∃ φ : L.Sentenceω, B = modelsOf φ := by
  rw [MeasurableSpace.measurableSet_iInf]
  simp only [MeasurableSpace.measurableSet_invariants]
  rw [← lopezEscobar_action_iff]
  constructor
  · intro h
    refine ⟨(h 1).1, fun σ => ?_⟩
    have hpre := (h σ⁻¹).2
    simpa [Set.preimage_smul] using hpre
  · rintro ⟨hB, hinv⟩ σ
    refine ⟨hB, ?_⟩
    simpa [Set.preimage_smul] using hinv σ⁻¹

/-- A configuration lies in the projective class of `ψ` along `LHom.sumInl` iff it is the reduct
of some model of `ψ` in `RelationalConfiguration (L.sum pcWitnessLanguage) V`. -/
private theorem mem_image_reductConfiguration_modelsOf_iff
    (ψ : (L.sum pcWitnessLanguage).Sentenceω) (c : RelationalConfiguration L V) :
    c ∈ (LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).reductConfiguration ''
        modelsOf (V := V) ψ ↔
      @LHom.PCMem L (L.sum pcWitnessLanguage) LHom.sumInl ψ V c.toStructure := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    let := (LHom.sumInl.reductConfiguration d).toStructure
    let := d.toStructure
    have hred : (LHom.sumInl.reductConfiguration d).toStructure = LHom.sumInl.reduct V :=
      LHom.toStructure_reductConfiguration LHom.sumInl d
    have hExp : @LHom.IsExpansionOn L (L.sum pcWitnessLanguage) LHom.sumInl V
        (LHom.sumInl.reductConfiguration d).toStructure d.toStructure :=
      hred ▸ LHom.isExpansionOn_reduct LHom.sumInl V
    exact LHom.pcMem_iff.2 ⟨d.toStructure, hExp, mem_modelsOf.1 hd⟩
  · intro h
    let := c.toStructure
    obtain ⟨S, hS, hreal⟩ := LHom.pcMem_iff.1 h
    let d : RelationalConfiguration (L.sum pcWitnessLanguage) V :=
      @ofStructure (L.sum pcWitnessLanguage) V S
    refine ⟨d, ?_, ?_⟩
    · rw [mem_modelsOf, toStructure_ofStructure]
      exact hreal
    · ext a
      induction a using Atom.induction_atom with
      | h R x =>
        classical
        have hrel : @Structure.RelMap (L.sum pcWitnessLanguage) V S _
            (Sum.inl R) x ↔ c.eval (atom R x) = true :=
          (iff_of_eq (@LHom.IsExpansionOn.map_onRelation L (L.sum pcWitnessLanguage)
            LHom.sumInl V c.toStructure S hS _ R x)).trans (toStructure_relMap c R x)
        rw [LHom.eval_reductConfiguration, LHom.onAtom_atom]
        dsimp only [d]
        rw [eval_ofStructure]
        cases hb : c.eval (atom R x)
        · simp only [LHom.sumInl_onRelation, decide_eq_false_iff_not]
          exact fun hr => Bool.false_ne_true (hb ▸ hrel.1 hr)
        · simp only [LHom.sumInl_onRelation, decide_eq_true_eq]
          exact hrel.2 hb

/-- Encoding `c.toStructure` along a bijection `f : V ≃ W` coincides with `c.restrict f.symm`. -/
private theorem encodeVia_toStructure_eq_restrict {W : Type w'} (f : V ≃ W)
    (c : RelationalConfiguration L V) :
    @Equiv.encodeVia L V W c.toStructure f = c.restrict f.symm := by
  let := c.toStructure
  ext a
  induction a using Atom.induction_atom with
  | h R x =>
    classical
    simp [Equiv.eval_encodeVia, toStructure_relMap, eval_restrict, Atom.map_atom]

/-- **Invariant analytic classes are projective (`PC_{ω₁ω}`) classes.** On a countably infinite
carrier in a countable relational vocabulary, an isomorphism-invariant class of configurations is
analytic iff it is the class of configurations whose decoded structures lie in
`LHom.sumInl.PCMem ψ` for some `ψ : (L.sum pcWitnessLanguage).Sentenceω`. -/
theorem analyticSet_iff_exists_pc [∀ n, Countable (L.Relations n)] [Countable V] [Infinite V]
    {B : Set (RelationalConfiguration L V)} (hinv : IsomorphismInvariant B) :
    AnalyticSet B ↔ ∃ ψ : (L.sum pcWitnessLanguage).Sentenceω,
      B = {c | @LHom.PCMem L (L.sum pcWitnessLanguage) LHom.sumInl ψ V c.toStructure} := by
  constructor
  · intro hB
    obtain ⟨e⟩ : Nonempty (V ≃ ℕ) := nonempty_equiv_of_countable
    obtain ⟨T, hT⟩ := exists_tree_of_analyticSet
      (hB.image_of_continuous (continuous_restrict e.symm))
    refine ⟨pcSentence T, ?_⟩
    ext c
    simp only [mem_ofPred_eq]
    constructor
    · intro hc
      have hc' : c.restrict e.symm ∈ restrict e.symm '' B := ⟨c, hc, rfl⟩
      rw [hT] at hc'
      obtain ⟨g, hg⟩ := hc'
      let : L.Structure ℕ := (c.restrict e.symm).toStructure
      have hbody : (fun n => ((ofStructure L ℕ).queryCode n, g n)) ∈ body T := by
        simpa [ofStructure_toStructure] using hg
      have hpc := pcMem_pcSentence_of_mem_body T g hbody
      let : L.Structure V := c.toStructure
      exact (StrongHomClass.pcMem_iff (equivOfRestrict e.symm c)).1 hpc
    · intro hpc
      let : L.Structure V := c.toStructure
      obtain ⟨f, g, hg⟩ := exists_equiv_and_branch_of_pcMem_pcSentence T hpc
      obtain ⟨d, hdB, hdeq⟩ : f.encodeVia (L := L) ∈ restrict e.symm '' B := by
        rw [hT]; exact ⟨g, hg⟩
      have hperm : (e.trans f.symm) • d = c := by
        have h1 := congrArg (restrict f) (hdeq.trans (encodeVia_toStructure_eq_restrict f c))
        ext a
        have h2 := congrArg (fun k : RelationalConfiguration L V => k.eval a) h1
        simpa [eval_perm_smul, eval_restrict, ← Atom.map_comp, Function.comp_assoc] using h2
      exact (hinv.mem_iff (isoSetoid_iff_exists_perm_smul_eq.2 ⟨e.trans f.symm, hperm⟩)).1 hdB
  · rintro ⟨ψ, rfl⟩
    have heq : {c : RelationalConfiguration L V |
        @LHom.PCMem L (L.sum pcWitnessLanguage) LHom.sumInl ψ V c.toStructure} =
        (LHom.sumInl : L →ᴸ L.sum pcWitnessLanguage).reductConfiguration ''
          modelsOf (V := V) ψ := by
      ext c; exact (mem_image_reductConfiguration_modelsOf_iff ψ c).symm
    rw [heq]
    have : ∀ n, Countable ((L.sum pcWitnessLanguage).Relations n) := fun n =>
      inferInstanceAs (Countable (L.Relations n ⊕ PCWitnessRel n))
    exact (measurableSet_modelsOf ψ).analyticSet.image_of_continuous
      (LHom.continuous_reductConfiguration LHom.sumInl)

end Main

end TauCeti.RelationalConfiguration
