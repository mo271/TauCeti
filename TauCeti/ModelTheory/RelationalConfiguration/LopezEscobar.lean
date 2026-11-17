/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Interpolation.PCClass
public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Topology.MetricSpace.PiNat
import TauCeti.ModelTheory.Infinitary.CodedConnectives
import TauCeti.ModelTheory.Interpolation.Craig

/-!
# The López–Escobar theorem

On a countable carrier `V` in a relational language `L` with countably many relation symbols of
each arity, the model classes `modelsOf θ` of `L_{ω₁ω}` sentences are Borel and invariant under
isomorphism (`measurableSet_modelsOf`, `isomorphismInvariant_modelsOf`). This file proves the
converse and its analytic separation form (**López–Escobar separation**): any two analytic sets
`A` and `B` of configurations on `V` containing no isomorphic pair are separated by a single
`L_{ω₁ω}` sentence `θ`, with `A ⊆ modelsOf θ` and `Disjoint B (modelsOf θ)`
(`exists_sentence_separating`).

The proof on a nonempty countable carrier reduces analytic separation to projective-class
separation (`FirstOrder.Language.pcSeparation`): for any analytic set `A` of configurations on `V`,
the class of `L`-structures isomorphic to some member of `A` is a `PC_{ω₁ω}` class
(`exists_pcMem_iff_exists_equiv_of_analyticSet`). When `A` is the continuous image of Baire space
`ℕ → ℕ` under `f`, an expansion adds unary predicates naming each vertex `v : V` and nullary
predicates recording each coordinate value `x n = k` of a point `x : ℕ → ℕ`; because `f` is
continuous, each atom truth condition `(f x).eval a = true` is open in `ℕ → ℕ` and therefore a
countable disjunction of finite prefix cylinders. Two analytic sets without an isomorphic pair
produce disjoint `PC_{ω₁ω}` classes of countable nonempty structures, which `pcSeparation`
separates by a single `L_{ω₁ω}` sentence.

On an empty carrier, every atom has arity `0` and isomorphism is equality, so Lusin separation
reduces directly to the fact that every measurable set in the product σ-algebra is the model class
of an `L_{ω₁ω}` sentence (`exists_modelsOf_eq_of_isEmpty`), with no countability hypothesis on
`L`.

From separation we obtain the López–Escobar theorem for isomorphism-invariant Borel sets
(`exists_modelsOf_eq_of_isomorphismInvariant`, `exists_modelsOf_eq_iff`), separation of analytic
splits inside a class (`exists_sentence_mem_modelsOf_iff_of_analyticSet`), and **relative
López–Escobar** (`exists_sentence_mem_modelsOf_iff`): along a measurable map from a standard
Borel space `X` into configurations on `V`, every Borel subset of `X` invariant under isomorphism
of images is the preimage of `modelsOf θ` for a single `L_{ω₁ω}` sentence `θ`.

## Main results

* `TauCeti.RelationalConfiguration.isomorphismInvariant_modelsOf`: every model class is
  isomorphism invariant.
* `TauCeti.RelationalConfiguration.exists_pcMem_iff_exists_equiv_of_analyticSet`: the isomorphism
  saturation of an analytic set of configurations is a `PC_{ω₁ω}` class.
* `TauCeti.RelationalConfiguration.exists_modelsOf_eq_of_isEmpty`: on an empty carrier, every
  measurable set of configurations is a model class of an `L_{ω₁ω}` sentence.
* `TauCeti.RelationalConfiguration.exists_sentence_separating`: **López–Escobar separation** for
  two analytic sets containing no isomorphic pair.
* `TauCeti.RelationalConfiguration.exists_modelsOf_eq_of_isomorphismInvariant` and
  `TauCeti.RelationalConfiguration.exists_modelsOf_eq_iff`: **the López–Escobar theorem**,
  identifying isomorphism-invariant Borel sets with model classes of `L_{ω₁ω}` sentences.
* `TauCeti.RelationalConfiguration.exists_sentence_mem_modelsOf_iff_of_analyticSet` and
  `TauCeti.RelationalConfiguration.exists_sentence_mem_modelsOf_iff`: **relative López–Escobar**
  for analytic cuts and along measurable maps from standard Borel spaces.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae 57 (1965), 253–272.
* David Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge
  University Press, 2016, Chapter 4 (the López–Escobar theorem via `PC_{ω₁ω}` separation).
* Alexander S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 16.8.
* Su Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Chapter 11.
-/

public section

universe u v w w' uι

open FirstOrder FirstOrder.Language MeasureTheory Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {V : Type w}

/-- The model class of any infinitary sentence is isomorphism invariant. -/
theorem isomorphismInvariant_modelsOf [L.IsRelational] {ι : Type uι} (φ : L.SentenceInf ι) :
    IsomorphismInvariant (modelsOf (V := V) φ) :=
  isomorphismInvariant_iff.2 fun _ _ h hc =>
    let ⟨e⟩ := isoSetoid_apply.1 h
    (e.mem_modelsOf_iff φ).1 hc

/-! ### Projective-class presentation of analytic classes -/

section AnalyticPC

/-- Auxiliary relation symbols adjoining a unary vertex predicate for each `v : V` and a nullary
coordinate predicate for each `(n, k) : ℕ × ℕ`. -/
private inductive AuxRel (V : Type w) : ℕ → Type w
  | vertex (v : V) : AuxRel V 1
  | baire (n k : ℕ) : AuxRel V 0

/-- Auxiliary relational language built from `AuxRel V`. -/
private def auxLang (V : Type w) : Language.{0, w} where
  Functions _ := PEmpty
  Relations := AuxRel V

/-- The unary vertex relation symbol `P_v` in `L.sum (auxLang V)`. -/
private def relVertex (v : V) : (L.sum (auxLang V)).Relations 1 :=
  Sum.inr (AuxRel.vertex v)

/-- The nullary Baire-coordinate relation symbol `Q_{n, k}` in `L.sum (auxLang V)`. -/
private def relBaire (n k : ℕ) : (L.sum (auxLang V)).Relations 0 :=
  Sum.inr (AuxRel.baire n k)

/-- The unary vertex predicate `P_v(t)` in `L.sum (auxLang V)`. -/
private def relP {m : ℕ} (v : V) (t : (L.sum (auxLang V)).Term (Empty ⊕ Fin m)) :
    (L.sum (auxLang V)).BoundedFormulaInf ℕ Empty m :=
  BoundedFormulaInf.rel (relVertex (L := L) v) ![t]

/-- The nullary Baire-coordinate predicate `Q_{n, k}` in `L.sum (auxLang V)`, weakened to `m`
bound variables. -/
private def relQ (m n k : ℕ) : (L.sum (auxLang V)).BoundedFormulaInf ℕ Empty m :=
  BoundedFormulaInf.rel (relBaire (L := L) (V := V) n k) Fin.elim0

private theorem realize_relP {M : Type w'} [(L.sum (auxLang V)).Structure M] {m : ℕ} (v : V)
    (t : (L.sum (auxLang V)).Term (Empty ⊕ Fin m)) (val : Empty → M) (xs : Fin m → M) :
    (relP (L := L) v t).Realize val xs ↔
      Structure.RelMap (relVertex (L := L) v) ![t.realize (Sum.elim val xs)] := by
  unfold relP
  rw [BoundedFormulaInf.realize_rel]
  exact Iff.of_eq (congrArg _ (funext fun i => by fin_cases i; rfl))

private theorem realize_relQ {M : Type w'} [(L.sum (auxLang V)).Structure M] {m : ℕ} (n k : ℕ)
    (val : Empty → M) (xs : Fin m → M) :
    (relQ (L := L) (V := V) m n k).Realize val xs ↔
      Structure.RelMap (M := M) (relBaire (L := L) (V := V) n k) Fin.elim0 := by
  unfold relQ
  rw [BoundedFormulaInf.realize_rel]
  exact Iff.of_eq (congrArg _ (funext fun i => i.elim0))

/-- Conjunction asserting that the Baire-coordinate predicates match the finite prefix `w`. -/
private def prefixFormula (m : ℕ) (w : List ℕ) :
    (L.sum (auxLang V)).BoundedFormulaInf ℕ Empty m :=
  BoundedFormulaInf.iInfAlong (IndexCoding.ofEncodable (Fin w.length))
    fun i => relQ (L := L) (V := V) m i.1 w[i]

/-- Disjunction over all finite prefixes whose cylinder in `ℕ → ℕ` lies in
`{x | (f x).eval a = true}`. -/
private noncomputable def atomOpenFormula (f : (ℕ → ℕ) → RelationalConfiguration L V)
    (m : ℕ) (a : Atom L V) : (L.sum (auxLang V)).BoundedFormulaInf ℕ Empty m :=
  BoundedFormulaInf.iSupAlong
    (IndexCoding.ofEncodableWith (Encodable.ofCountable
      {w : List ℕ //
        ∀ z : ℕ → ℕ, (∀ i : Fin w.length, z i.1 = w[i]) → (f z).eval a = true}))
    fun w => prefixFormula (L := L) (V := V) m w.1

/-- Sentence asserting that the unary predicates `P_v` partition the carrier into singletons
indexed bijectively by `V`. -/
private noncomputable def vertexBijAxioms [Countable V] : (L.sum (auxLang V)).Sentenceω :=
  open Classical in
  (BoundedFormulaInf.iInfAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable V)) fun v =>
      (relP (L := L) v (Term.var (Sum.inr (0 : Fin 1)))).ex) ⊓
    (BoundedFormulaInf.iInfAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable V)) fun v =>
      ((relP (L := L) v (Term.var (Sum.inr (0 : Fin 2)))).imp
        ((relP (L := L) v (Term.var (Sum.inr (1 : Fin 2)))).imp
          (BoundedFormulaInf.equal (Term.var (Sum.inr (0 : Fin 2)))
            (Term.var (Sum.inr (1 : Fin 2)))))).alls) ⊓
    (BoundedFormulaInf.iInfAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable (V × V)))
      fun p =>
        if p.1 = p.2 then ⊤
        else (relP (L := L) p.1 (Term.var (Sum.inr (0 : Fin 1))) ⊓
          relP (L := L) p.2 (Term.var (Sum.inr (0 : Fin 1)))).not.all) ⊓
    (BoundedFormulaInf.iSupAlong (IndexCoding.ofEncodableWith (Encodable.ofCountable V)) fun v =>
      relP (L := L) v (Term.var (Sum.inr (0 : Fin 1)))).all

/-- Sentence asserting that the nullary predicates `Q_{n, k}` encode a function `ℕ → ℕ`. -/
private def baireAxioms : (L.sum (auxLang V)).Sentenceω :=
  (BoundedFormulaInf.iInf fun n =>
      BoundedFormulaInf.iSup fun k => relQ (L := L) (V := V) 0 n k) ⊓
    (BoundedFormulaInf.iInfAlong (IndexCoding.ofEncodable (ℕ × ℕ × ℕ)) fun p =>
      if p.2.1 = p.2.2 then ⊤
      else (relQ (L := L) (V := V) 0 p.1 p.2.1 ⊓ relQ (L := L) (V := V) 0 p.1 p.2.2).not)

/-- Sentence asserting that each `L`-relation agrees on the named vertices with `f x`. -/
private noncomputable def atomAxioms [∀ n, Countable (L.Relations n)] [Countable V]
    (f : (ℕ → ℕ) → RelationalConfiguration L V) : (L.sum (auxLang V)).Sentenceω :=
  BoundedFormulaInf.iInfAlong
    (IndexCoding.ofEncodableWith
      (Encodable.ofCountable (Σ n : ℕ, L.Relations n × (Fin n → V))))
    fun p =>
      ((BoundedFormulaInf.iInfAlong (IndexCoding.ofEncodable (Fin p.1)) fun j =>
          relP (L := L) (p.2.2 j) (Term.var (Sum.inr j))).imp
        ((BoundedFormulaInf.rel ((LHom.sumInl : L →ᴸ L.sum (auxLang V)).onRelation p.2.1)
            fun j => Term.var (Sum.inr j)).iff
          (atomOpenFormula f p.1 (atom p.2.1 p.2.2)))).alls

/-- The `L.sum (auxLang V)`-sentence whose projective class is the isomorphism saturation of
`range f`. -/
private noncomputable def analyticSentence [∀ n, Countable (L.Relations n)] [Countable V]
    (f : (ℕ → ℕ) → RelationalConfiguration L V) : (L.sum (auxLang V)).Sentenceω :=
  vertexBijAxioms (L := L) (V := V) ⊓ baireAxioms (L := L) (V := V) ⊓ atomAxioms f

/-- Realization of `vertexBijAxioms` yields a bijection `e : V ≃ M` naming each vertex by
`P_v`. -/
private theorem exists_equiv_of_realize_vertexBijAxioms [Countable V] {M : Type w'}
    [(L.sum (auxLang V)).Structure M]
    (h : SentenceInf.Realize (vertexBijAxioms (L := L) (V := V)) M) :
    ∃ e : V ≃ M, ∀ (v : V) (z : M),
      Structure.RelMap (relVertex (L := L) v) ![z] ↔ z = e v := by
  classical
  simp only [vertexBijAxioms, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_inf, BoundedFormulaInf.realize_iInfAlong,
    BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_alls, BoundedFormulaInf.realize_all,
    BoundedFormulaInf.realize_imp, BoundedFormulaInf.realize_equal,
    BoundedFormulaInf.realize_iSupAlong, realize_relP, Term.realize_var, Sum.elim_inr] at h
  obtain ⟨⟨⟨hex, huniq⟩, hdisj⟩, hcov⟩ := h
  have huniq' : ∀ (v : V) (z₁ z₂ : M),
      Structure.RelMap (relVertex (L := L) v) ![z₁] →
      Structure.RelMap (relVertex (L := L) v) ![z₂] → z₁ = z₂ :=
    fun v z₁ z₂ h₁ h₂ => huniq v ![z₁, z₂] h₁ h₂
  have hdisj' : ∀ {v₁ v₂ : V} {z : M},
      Structure.RelMap (relVertex (L := L) v₁) ![z] →
      Structure.RelMap (relVertex (L := L) v₂) ![z] → v₁ = v₂ := by
    intro v₁ v₂ z h₁ h₂
    by_contra hne
    have hd := hdisj (v₁, v₂)
    simp only [hne, ↓reduceIte, BoundedFormulaInf.realize_all, BoundedFormulaInf.realize_not,
      BoundedFormulaInf.realize_inf, realize_relP, Term.realize_var, Sum.elim_inr] at hd
    exact hd z ⟨h₁, h₂⟩
  choose g hg using hex
  have hbij : Function.Bijective g := by
    refine ⟨fun v₁ v₂ h => hdisj' (hg v₁) (h ▸ hg v₂), fun z => ?_⟩
    obtain ⟨v, hv⟩ := hcov z
    exact ⟨v, huniq' v (g v) z (hg v) hv⟩
  refine ⟨Equiv.ofBijective g hbij, fun v z => ⟨fun hz => huniq' v z (g v) hz (hg v), ?_⟩⟩
  rintro rfl
  exact hg v

/-- Conversely, interpreting each `P_v` as the singleton `{e v}` for a bijection `e : V ≃ M`
satisfies `vertexBijAxioms`. -/
private theorem realize_vertexBijAxioms_of_equiv [Countable V] {M : Type w'}
    [(L.sum (auxLang V)).Structure M] (e : V ≃ M)
    (he : ∀ (v : V) (z : M), Structure.RelMap (relVertex (L := L) v) ![z] ↔ z = e v) :
    SentenceInf.Realize (vertexBijAxioms (L := L) (V := V)) M := by
  classical
  simp only [vertexBijAxioms, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_inf, BoundedFormulaInf.realize_iInfAlong,
    BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_alls, BoundedFormulaInf.realize_all,
    BoundedFormulaInf.realize_imp, BoundedFormulaInf.realize_equal,
    BoundedFormulaInf.realize_iSupAlong, realize_relP, Term.realize_var, Sum.elim_inr, he]
  refine ⟨⟨⟨fun v => ⟨e v, rfl⟩, fun v xs h₁ h₂ => h₁.trans h₂.symm⟩,
    fun p => ?_⟩, fun z => ⟨e.symm z, (e.apply_symm_apply z).symm⟩⟩
  by_cases hp : p.1 = p.2
  · simp [hp]
  · simp only [hp, ↓reduceIte, BoundedFormulaInf.realize_all, BoundedFormulaInf.realize_not,
      BoundedFormulaInf.realize_inf, realize_relP, Term.realize_var, Sum.elim_inr, he]
    rintro z ⟨h₁, h₂⟩
    exact hp (e.injective (h₁.symm.trans h₂))

/-- Realization of `baireAxioms` yields a sequence `x : ℕ → ℕ` encoded by `Q_{n, k}`. -/
private theorem exists_baire_of_realize_baireAxioms {M : Type w'}
    [(L.sum (auxLang V)).Structure M]
    (h : SentenceInf.Realize (baireAxioms (L := L) (V := V)) M) :
    ∃ x : ℕ → ℕ, ∀ n k : ℕ,
      Structure.RelMap (M := M) (relBaire (L := L) (V := V) n k) Fin.elim0 ↔ x n = k := by
  simp only [baireAxioms, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_inf, BoundedFormulaInf.realize_iInf, BoundedFormulaInf.realize_iSup,
    BoundedFormulaInf.realize_iInfAlong, realize_relQ] at h
  obtain ⟨hex, huniq⟩ := h
  choose x hx using hex
  refine ⟨x, fun n k => ⟨fun hk => ?_, fun hnk => hnk ▸ hx n⟩⟩
  by_contra hne
  have hu := huniq (n, x n, k)
  simp only [hne, ↓reduceIte, BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_inf,
    realize_relQ] at hu
  exact hu ⟨hx n, hk⟩

/-- Conversely, interpreting each `Q_{n, k}` by `x n = k` satisfies `baireAxioms`. -/
private theorem realize_baireAxioms_of_eq {M : Type w'} [(L.sum (auxLang V)).Structure M]
    (x : ℕ → ℕ)
    (hx : ∀ n k : ℕ,
      Structure.RelMap (M := M) (relBaire (L := L) (V := V) n k) Fin.elim0 ↔ x n = k) :
    SentenceInf.Realize (baireAxioms (L := L) (V := V)) M := by
  simp only [baireAxioms, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_inf, BoundedFormulaInf.realize_iInf, BoundedFormulaInf.realize_iSup,
    BoundedFormulaInf.realize_iInfAlong, realize_relQ, hx]
  refine ⟨fun n => ⟨x n, rfl⟩, fun p => ?_⟩
  by_cases hp : p.2.1 = p.2.2
  · simp [hp]
  · simp only [hp, ↓reduceIte, BoundedFormulaInf.realize_not, BoundedFormulaInf.realize_inf,
      realize_relQ, hx]
    rintro ⟨h₁, h₂⟩
    exact hp (h₁.symm.trans h₂)

/-- When the nullary predicates `Q_{n, k}` encode `x : ℕ → ℕ`, the open formula for an atom
`a` holds exactly when `(f x).eval a = true`. -/
private theorem realize_atomOpenFormula_iff {M : Type w'} [(L.sum (auxLang V)).Structure M]
    {f : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f) {x : ℕ → ℕ}
    (hx : ∀ n k : ℕ,
      Structure.RelMap (M := M) (relBaire (L := L) (V := V) n k) Fin.elim0 ↔ x n = k)
    {m : ℕ} (a : Atom L V) (xs : Fin m → M) :
    (atomOpenFormula f m a).Realize Empty.elim xs ↔ (f x).eval a = true := by
  simp only [atomOpenFormula, prefixFormula, BoundedFormulaInf.realize_iSupAlong,
    BoundedFormulaInf.realize_iInfAlong, realize_relQ, hx, Subtype.exists]
  constructor
  · rintro ⟨w, hw, hxw⟩
    exact hw x hxw
  · intro hfx
    have hopen : IsOpen {y : ℕ → ℕ | (f y).eval a = true} :=
      (isClopen_setOf_eval a true).isOpen.preimage hf
    obtain ⟨_, ⟨y, n, rfl⟩, hxy, hyU⟩ :=
      (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => ℕ)).exists_subset_of_mem_open hfx hopen
    refine ⟨List.ofFn (fun i : Fin n => x i), fun z hz => ?_, fun i => by simp⟩
    apply hyU
    rw [← PiNat.mem_cylinder_iff_eq.1 hxy, PiNat.mem_cylinder_iff]
    intro i hi
    simpa using hz ⟨i, by simpa using hi⟩

/-- Any expansion of `M` satisfying `analyticSentence f` is isomorphic to `f x` for some
`x : ℕ → ℕ`. -/
private theorem exists_equiv_of_pcMem_analyticSentence [L.IsRelational]
    [∀ n, Countable (L.Relations n)] [Countable V]
    {f : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f)
    {M : Type w'} [iM : L.Structure M]
    (h : LHom.sumInl.PCMem (analyticSentence f) M) :
    ∃ x : ℕ → ℕ, Nonempty (@Language.Equiv L V M (f x).toStructure iM) := by
  obtain ⟨S, hS, hΘ⟩ := LHom.pcMem_iff.1 h
  simp only [analyticSentence, SentenceInf.realize_inf] at hΘ
  obtain ⟨⟨hV, hQ⟩, hAtom⟩ := hΘ
  obtain ⟨e, he⟩ := @exists_equiv_of_realize_vertexBijAxioms L V _ M S hV
  obtain ⟨x, hx⟩ := @exists_baire_of_realize_baireAxioms L V M S hQ
  refine ⟨x, ⟨@Language.Equiv.mk L V M (f x).toStructure iM e
    (fun {n} fn => isEmptyElim fn) (fun {l} R t => ?_)⟩⟩
  simp only [atomAxioms, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iInfAlong, BoundedFormulaInf.realize_alls,
    BoundedFormulaInf.realize_imp, BoundedFormulaInf.realize_iff, realize_relP,
    BoundedFormulaInf.realize_rel, Term.realize_var, Sum.elim_inr] at hAtom
  have ha := hAtom ⟨l, R, t⟩ (e ∘ t) (fun j => (he (t j) (e (t j))).2 rfl)
  rw [@realize_atomOpenFormula_iff L V M S f hf x hx l (atom R t) (e ∘ t)] at ha
  have hrel : @Structure.RelMap _ _ S l (LHom.sumInl.onRelation R) (e ∘ t) ↔
      @Structure.RelMap _ _ iM l R (e ∘ t) :=
    Iff.of_eq (@LHom.map_onRelation L (L.sum (auxLang V)) LHom.sumInl M iM S hS l R (e ∘ t))
  have hfun : (fun j : Fin l => e (t j)) = e ∘ t := rfl
  rw [toStructure_relMap]
  exact hrel.symm.trans (by simpa [hfun] using ha)

/-- Any structure isomorphic to `f x` expands to a model of `analyticSentence f`. -/
private theorem pcMem_analyticSentence_of_equiv [L.IsRelational]
    [∀ n, Countable (L.Relations n)] [Countable V]
    {f : (ℕ → ℕ) → RelationalConfiguration L V} (hf : Continuous f)
    {M : Type w'} [iM : L.Structure M] {x : ℕ → ℕ}
    (e : @Language.Equiv L V M (f x).toStructure iM) :
    LHom.sumInl.PCMem (analyticSentence f) M := by
  let : L.Structure V := (f x).toStructure
  let Saux : (auxLang V).Structure M :=
    { funMap := fun fn => PEmpty.elim fn
      RelMap := fun R xs =>
        match R with
        | .vertex v => xs 0 = e v
        | .baire k m => x k = m }
  let : (L.sum (auxLang V)).Structure M := @Language.sumStructure L (auxLang V) M iM Saux
  refine LHom.pcMem_iff.2 ⟨_, inferInstance, ?_⟩
  have he : ∀ (v : V) (z : M), Structure.RelMap (relVertex (L := L) v) ![z] ↔ z = e v :=
    fun _ _ => Iff.rfl
  have hx : ∀ n k : ℕ,
      Structure.RelMap (M := M) (relBaire (L := L) (V := V) n k) Fin.elim0 ↔ x n = k :=
    fun _ _ => Iff.rfl
  simp only [analyticSentence, SentenceInf.realize_inf]
  refine ⟨⟨realize_vertexBijAxioms_of_equiv e.toEquiv he,
    realize_baireAxioms_of_eq x hx⟩, ?_⟩
  simp only [atomAxioms, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iInfAlong, BoundedFormulaInf.realize_alls,
    BoundedFormulaInf.realize_imp, BoundedFormulaInf.realize_iff, realize_relP,
    BoundedFormulaInf.realize_rel, Term.realize_var, Sum.elim_inr]
  rintro ⟨l, R, t⟩ xs hxs
  rw [realize_atomOpenFormula_iff hf hx (atom R t) xs]
  have hxs_eq : xs = e ∘ t := funext fun j => hxs j
  rw [hxs_eq]
  exact (@Language.Equiv.map_rel L V M (f x).toStructure iM e l R t).trans
    (toStructure_relMap (f x) R t)

/-- **Analytic classes are `PC_{ω₁ω}`.** For any analytic set `A` of relational configurations
on a countable carrier `V` in a relational language with countably many relation symbols of each
arity, the class of `L`-structures (in any universe `w'`) isomorphic to a member of `A` is the
projective class of an `L_{ω₁ω}` sentence in an expansion of `L`. -/
theorem exists_pcMem_iff_exists_equiv_of_analyticSet [L.IsRelational]
    [∀ n, Countable (L.Relations n)] [Countable V]
    {A : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) :
    ∃ (L₁ : Language.{0, w}) (Θ : (L.sum L₁).Sentenceω),
      ∀ (M : Type w') [L.Structure M],
        LHom.sumInl.PCMem Θ M ↔
          ∃ c ∈ A, Nonempty (@Language.Equiv L V M c.toStructure _) := by
  rcases analyticSet_iff_exists_polishSpace_range.1 hA with ⟨β, _, _, f₀, hf₀, rfl⟩
  rcases isEmpty_or_nonempty β with hβ | hβ
  · refine ⟨auxLang V, ⊥, fun M _ => ?_⟩
    simp [LHom.pcMem_iff]
  · obtain ⟨g, hg, hgsurj⟩ := PolishSpace.exists_nat_nat_continuous_surjective β
    rw [← hgsurj.range_comp f₀]
    refine ⟨auxLang V, analyticSentence (f₀ ∘ g), fun M iM => ⟨fun h => ?_, ?_⟩⟩
    · obtain ⟨x, hx⟩ := exists_equiv_of_pcMem_analyticSentence (hf₀.comp hg) h
      exact ⟨(f₀ ∘ g) x, mem_range_self x, hx⟩
    · rintro ⟨_, ⟨x, rfl⟩, ⟨e⟩⟩
      exact pcMem_analyticSentence_of_equiv (hf₀.comp hg) e

end AnalyticPC

/-! ### Empty-carrier Borel model classes -/

variable [L.IsRelational]

/-- On an empty carrier, every measurable set of relational configurations is the model class of
an `L_{ω₁ω}` sentence. No countability hypothesis on the language is needed, because the product
σ-algebra is generated by countable Boolean operations on nullary atoms. -/
theorem exists_modelsOf_eq_of_isEmpty [IsEmpty V] {A : Set (RelationalConfiguration L V)}
    (hA : MeasurableSet A) : ∃ θ : L.Sentenceω, modelsOf (V := V) θ = A := by
  have hm : (inferInstance : MeasurableSpace (RelationalConfiguration L V)) =
      MeasurableSpace.generateFrom
        {B : Set (RelationalConfiguration L V) | ∃ (a : Atom L V) (t : Set Bool),
          MeasurableSet t ∧ (fun c : RelationalConfiguration L V => c.eval a) ⁻¹' t = B} := by
    have hpi : (inferInstance : MeasurableSpace (RelationalConfiguration L V)) =
        MeasurableSpace.generateFrom
          {B : Set (RelationalConfiguration L V) | ∃ (a : Atom L V) (t : Set Bool),
            MeasurableSet t ∧ (fun c : RelationalConfiguration L V => c a) ⁻¹' t = B} :=
      MeasurableSpace.pi_eq_generateFrom_projections (α := fun _ : Atom L V => Bool)
    refine hpi.trans (congrArg MeasurableSpace.generateFrom ?_)
    ext B
    exact exists_congr fun a => exists_congr fun t => and_congr_right fun _ => by
      have hfn : (fun c : RelationalConfiguration L V => c a) = fun c => c.eval a :=
        funext fun c => (eval_def c a).symm
      rw [hfn]
  have hA' : @MeasurableSet _ (MeasurableSpace.generateFrom
      {B : Set (RelationalConfiguration L V) | ∃ (a : Atom L V) (t : Set Bool),
        MeasurableSet t ∧ (fun c : RelationalConfiguration L V => c.eval a) ⁻¹' t = B}) A :=
    hm ▸ hA
  clear hA hm
  induction A, hA' using MeasurableSpace.generateFrom_induction with
  | hC s hs _ =>
    obtain ⟨a, t, -, rfl⟩ := hs
    induction a using Atom.induction_atom with
    | @h n R u =>
      cases n with
      | zero =>
        have hrel (c : RelationalConfiguration L V) :
            c ∈ modelsOf (V := V) (BoundedFormulaInf.rel R Fin.elim0 : L.Sentenceω) ↔
              c.eval (atom R u) = true := by
          simp only [mem_modelsOf, SentenceInf.realize_def, FormulaInf.realize_def,
            BoundedFormulaInf.realize_rel, toStructure_relMap]
          exact Iff.of_eq (congrArg (fun v => c.eval (atom R v) = true) (funext fun i => i.elim0))
        by_cases ht : true ∈ t <;> by_cases hf : false ∈ t
        · exact ⟨⊤, by ext c; simp only [modelsOf_top, mem_univ, mem_preimage, true_iff]
                       cases hc : c.eval (atom R u) <;> simp [ht, hf]⟩
        · exact ⟨BoundedFormulaInf.rel R Fin.elim0, by
            ext c; rw [hrel, mem_preimage]; cases hc : c.eval (atom R u) <;> simp [ht, hf]⟩
        · exact ⟨(BoundedFormulaInf.rel R Fin.elim0).not, by
            ext c; rw [modelsOf_not, mem_compl_iff, hrel, mem_preimage]
            cases hc : c.eval (atom R u) <;> simp [ht, hf]⟩
        · exact ⟨⊥, by
            ext c
            simp only [modelsOf_bot, mem_empty_iff_false, mem_preimage, false_iff]
            cases hc : c.eval (atom R u) <;> simp [ht, hf]⟩
      | succ n =>
        exact isEmptyElim (u 0)
  | empty => exact ⟨⊥, modelsOf_bot⟩
  | compl s _ ih =>
    obtain ⟨θ, rfl⟩ := ih
    exact ⟨θ.not, modelsOf_not θ⟩
  | iUnion u _ ih =>
    choose θ hθ using ih
    exact ⟨BoundedFormulaInf.iSup θ, by simp [modelsOf_iSup, hθ]⟩

/-! ### López–Escobar separation and theorem -/

/-- **López–Escobar separation.** On a countable carrier `V` in a relational language with
countably many relation symbols of each arity, any two analytic sets `A` and `B` of configurations
containing no isomorphic pair are separated by a single `L_{ω₁ω}` sentence `θ`:
`A ⊆ modelsOf θ` and `Disjoint B (modelsOf θ)`. -/
theorem exists_sentence_separating [∀ n, Countable (L.Relations n)] [Countable V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hdisj : ∀ a ∈ A, ∀ b ∈ B, ¬ isoSetoid L V a b) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) := by
  rcases isEmpty_or_nonempty V with hV | hV
  · -- On an empty carrier isomorphism is equality, so Lusin separation suffices.
    have hAB : Disjoint A B := Set.disjoint_left.2 fun a ha hb =>
      hdisj a ha a hb ((isoSetoid L V).refl a)
    obtain ⟨U, hAU, hBU, hUm⟩ := hA.measurablySeparable hB hAB
    obtain ⟨θ, rfl⟩ := exists_modelsOf_eq_of_isEmpty hUm
    exact ⟨θ, hAU, hBU⟩
  · obtain ⟨L₁, Θ₁, hΘ₁⟩ :=
      exists_pcMem_iff_exists_equiv_of_analyticSet.{u, v, w, w} hA
    obtain ⟨L₂, Θ₂, hΘ₂⟩ :=
      exists_pcMem_iff_exists_equiv_of_analyticSet.{u, v, w, w} hB
    obtain ⟨θ, h₁, h₂⟩ :=
      FirstOrder.Language.pcSeparation.{u, v, 0, w, 0, w, w, w} Θ₁ Θ₂
        fun M iM _ _ hM₁ hM₂ => by
          obtain ⟨a, ha, ⟨e₁⟩⟩ := (hΘ₁ M).1 hM₁
          obtain ⟨b, hb, ⟨e₂⟩⟩ := (hΘ₂ M).1 hM₂
          exact hdisj a ha b hb (isoSetoid_apply.2 ⟨@Language.Equiv.comp L V M a.toStructure iM V
            b.toStructure (@Language.Equiv.symm L V M b.toStructure iM e₂) e₁⟩)
    refine ⟨θ, fun a ha => ?_, Set.disjoint_left.2 fun b hb hθb => ?_⟩
    · let : L.Structure V := a.toStructure
      exact mem_modelsOf.2
        (h₁ V ((hΘ₁ V).2 ⟨a, ha, ⟨@Language.Equiv.refl L V a.toStructure⟩⟩))
    · let : L.Structure V := b.toStructure
      exact h₂ V ((hΘ₂ V).2 ⟨b, hb, ⟨@Language.Equiv.refl L V b.toStructure⟩⟩)
        (mem_modelsOf.1 hθb)

/-- **The López–Escobar theorem.** On a countable carrier in a relational language with countably
many relation symbols of each arity, every isomorphism-invariant Borel set of configurations is the
model class of an `L_{ω₁ω}` sentence. -/
theorem exists_modelsOf_eq_of_isomorphismInvariant [∀ n, Countable (L.Relations n)] [Countable V]
    {A : Set (RelationalConfiguration L V)} (hA : MeasurableSet A)
    (hinv : IsomorphismInvariant A) :
    ∃ θ : L.Sentenceω, modelsOf θ = A := by
  obtain ⟨θ, hsub, hdisj⟩ := exists_sentence_separating hA.analyticSet hA.compl.analyticSet
    fun _ ha _ hb hab => hb (isomorphismInvariant_iff.1 hinv hab ha)
  exact ⟨θ, subset_antisymm (Set.disjoint_compl_left_iff_subset.1 hdisj) hsub⟩

/-- **The López–Escobar characterization.** On a countable carrier in a relational language with
countably many relation symbols of each arity, a set of configurations is the model class of an
`L_{ω₁ω}` sentence if and only if it is Borel and isomorphism invariant. -/
theorem exists_modelsOf_eq_iff [∀ n, Countable (L.Relations n)] [Countable V]
    {A : Set (RelationalConfiguration L V)} :
    (∃ θ : L.Sentenceω, modelsOf θ = A) ↔ MeasurableSet A ∧ IsomorphismInvariant A :=
  ⟨fun ⟨θ, hθ⟩ => hθ ▸ ⟨measurableSet_modelsOf θ, isomorphismInvariant_modelsOf θ⟩,
    fun ⟨hA, hinv⟩ => exists_modelsOf_eq_of_isomorphismInvariant hA hinv⟩

/-! ### Relative López–Escobar -/

/-- **Relative López–Escobar for analytic cuts.** If `C ∩ B` and `C \ B` are analytic sets of
configurations on a countable carrier and `B` is closed under isomorphism within `C`, then a single
`L_{ω₁ω}` sentence agrees with `B` on `C`. -/
theorem exists_sentence_mem_modelsOf_iff_of_analyticSet [∀ n, Countable (L.Relations n)]
    [Countable V] {B C : Set (RelationalConfiguration L V)}
    (hCB : AnalyticSet (C ∩ B)) (hCdiff : AnalyticSet (C \ B))
    (hinv : ∀ c ∈ C, ∀ d ∈ C, isoSetoid L V c d → c ∈ B → d ∈ B) :
    ∃ θ : L.Sentenceω, ∀ c ∈ C, c ∈ modelsOf θ ↔ c ∈ B := by
  obtain ⟨θ, hsub, hdisj⟩ := exists_sentence_separating hCB hCdiff
    fun a ⟨haC, haB⟩ b ⟨hbC, hbB⟩ hab => hbB (hinv a haC b hbC hab haB)
  refine ⟨θ, fun c hc => ⟨fun hθ => by_contra fun hcB => ?_,
    fun hcB => hsub ⟨hc, hcB⟩⟩⟩
  exact Set.disjoint_left.1 hdisj ⟨hc, hcB⟩ hθ

/-- **Relative López–Escobar.** For a measurable map `f` from a standard Borel space `X` into
configurations on a countable carrier, every Borel set `U ⊆ X` invariant under isomorphism of
images is pulled back from the model class of a single `L_{ω₁ω}` sentence. -/
theorem exists_sentence_mem_modelsOf_iff [∀ n, Countable (L.Relations n)] [Countable V]
    {X : Type w'} [MeasurableSpace X] [StandardBorelSpace X]
    {f : X → RelationalConfiguration L V} (hf : Measurable f)
    {U : Set X} (hU : MeasurableSet U)
    (hinv : ∀ ⦃x y : X⦄, isoSetoid L V (f x) (f y) → x ∈ U → y ∈ U) :
    ∃ θ : L.Sentenceω, ∀ x, f x ∈ modelsOf θ ↔ x ∈ U := by
  obtain ⟨θ, hsub, hdisj⟩ := exists_sentence_separating
    (hU.analyticSet_image hf) (hU.compl.analyticSet_image hf)
    (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy; exact hy (hinv hxy hx))
  refine ⟨θ, fun x => ⟨fun hθ => by_contra fun hx => ?_, fun hx => hsub ⟨x, hx, rfl⟩⟩⟩
  exact Set.disjoint_left.1 hdisj ⟨x, hx, rfl⟩ hθ

end TauCeti.RelationalConfiguration
