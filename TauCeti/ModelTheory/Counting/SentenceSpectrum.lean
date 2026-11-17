/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Morley
public import TauCeti.ModelTheory.RelationalConfiguration.SentenceTheory
public import TauCeti.SetTheory.Descriptive.BorelReducibility
import TauCeti.Data.Set.Countable
import TauCeti.ModelTheory.RelationalConfiguration.LopezEscobar
import TauCeti.ModelTheory.Scott.Isomorphism
import TauCeti.SetTheory.Descriptive.Silver

/-!
# Sentence spectra and Borel observables of countable structures

This file develops the descriptive set theory of truth sequences
`sentenceTheory θ c : ℕ → Bool` of countable lists of `L_{ω₁ω}` sentences on relational
configurations over a countable carrier `V` in a relational language `L` with countably many
relation symbols of each arity.

From relative López–Escobar (`TauCeti.RelationalConfiguration.exists_sentence_mem_modelsOf_iff`),
every isomorphism-invariant Borel observable `g : X → ℕ → Bool` along a measurable family
`f : X → RelationalConfiguration L V` from a standard Borel space is realized pointwise as the
truth sequence `sentenceTheory θ ∘ f` of a countable list of `L_{ω₁ω}` sentences
(`exists_sentenceTheory_comp_eq`). More generally, an isomorphism-invariant measurable observable
into any countably separated measurable space has the same fibres as `sentenceTheory θ ∘ f`
(`exists_sentenceTheory_comp_eq_iff`). Specializing to `X = ℕ → Bool` and `g = id` yields
**Cantor recovery** (`exists_sentenceTheory_comp_eq_id`): any Borel map from Cantor space with
pairwise non-isomorphic values is inverted by the truth sequence of a countable list of sentences.

Combining Cantor recovery with Silver's theorem relative to a Borel subset
(`Setoid.countable_or_hasCantorAntichainOn_of_measurableSet`) gives the **sentence-spectrum
characterization of thinness**: a Borel set `C` of configurations on `V` is thin for isomorphism
if and only if every countable list of `L_{ω₁ω}` sentences realizes only countably many truth
sequences on `C` (`isThinOn_iff_countable_sentenceTheory_image`), with the sentence specialization
`isThinOnNatModels_iff_countable_sentenceTheory_image` for `modelsOf φ` on `ℕ`. The reverse
implication needs no Borel or invariance hypothesis on `C`
(`isThinOn_of_countable_sentenceTheory_image`).

Purely by counting (`TauCeti.countable_range_of_splits`), if a presentation `classOf : C → Q` of
the isomorphism classes (or any invariant determining sentence truth, with no surjectivity or
measurable structure on `Q`) has a countable truth side for every single sentence, then every
countable list of sentences realizes only countably many truth sequences on `C`
(`countable_sentenceTheory_image_of_splits`). Hence single-sentence splits force thinness
(`isThinOn_of_splits_via`, and the quotient form `isThinOn_of_sentence_splits`), without assuming
`C` is Borel or isomorphism invariant.

Finally, along a measurable family `f : X → RelationalConfiguration L V` from a standard Borel
space `X` (in particular, on a Borel class `C`), smoothness of the pulled-back isomorphism
relation is equivalent to existence of a single countable list of `L_{ω₁ω}` sentences separating
its classes (`isSmooth_comap_isoSetoid_iff`, `isSmooth_comap_val_isoSetoid_iff`). When `f` meets
only countably many isomorphism classes, Scott sentences make every class Borel and the
pulled-back relation is unconditionally smooth (`isSmooth_comap_isoSetoid_of_countable`). On a
thin Borel class `C`, smoothness is therefore equivalent to meeting only countably many
isomorphism classes (`isSmooth_comap_val_isoSetoid_iff_countable_quotient_of_isThinOn`): in
particular, a thin Borel class with uncountably many isomorphism classes admits no Borel complete
invariant.

## Main results

* `TauCeti.exists_sentenceTheory_comp_eq`, `TauCeti.exists_sentenceTheory_eq_on`, and
  `TauCeti.exists_sentenceTheory_comp_eq_iff`: Borel isomorphism-invariant observables into Cantor
  space or any countably separated measurable space are captured by `sentenceTheory θ`.
* `TauCeti.exists_sentenceTheory_comp_eq_id`: **Cantor recovery** for Borel maps from Cantor space
  with pairwise non-isomorphic values.
* `TauCeti.isThinOn_of_countable_sentenceTheory_image`,
  `TauCeti.countable_sentenceTheory_image_of_isThinOn`,
  `TauCeti.isThinOn_iff_countable_sentenceTheory_image`, and
  `TauCeti.isThinOnNatModels_iff_countable_sentenceTheory_image`: the sentence-spectrum
  characterization of thin classes and thin sentences.
* `TauCeti.countable_sentenceTheory_image_of_splits`, `TauCeti.isThinOn_of_splits_via`, and
  `TauCeti.isThinOn_of_sentence_splits`: single-sentence splits give countable sentence spectra and
  thinness.
* `TauCeti.isSmooth_comap_isoSetoid_iff`, `TauCeti.isSmooth_comap_val_isoSetoid_iff`,
  `TauCeti.isSmooth_comap_isoSetoid_of_countable`, and
  `TauCeti.isSmooth_comap_val_isoSetoid_iff_countable_quotient_of_isThinOn`: Borel complete
  invariants and smoothness along measurable families and on Borel and thin Borel classes.

## References

* E. G. K. López-Escobar, *An interpolation theorem for denumerably long formulas*, Fundamenta
  Mathematicae 57 (1965), 253–272.
* David Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge
  University Press, 2016, Chapter 4 (López–Escobar theorem) and Chapter 6 (scattered sentences).
* Su Gao, *Invariant Descriptive Set Theory*, Chapman & Hall/CRC, 2009, Chapters 5 and 11.
* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.
-/

public section

universe u v w w' uι

open Cardinal FirstOrder FirstOrder.Language MeasurableSpace MeasureTheory Set

namespace TauCeti

open RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-! ### Borel observables and Cantor recovery -/

/-- **Borel observables into Cantor space.** Along a measurable map `f` from a standard Borel
space `X` into configurations on a countable carrier, every isomorphism-invariant measurable map
`g : X → ℕ → Bool` is realized pointwise as the truth sequence of a countable list of
`L_{ω₁ω}` sentences. -/
theorem exists_sentenceTheory_comp_eq [∀ n, Countable (L.Relations n)] [Countable V]
    {X : Type w'} [MeasurableSpace X] [StandardBorelSpace X]
    {f : X → RelationalConfiguration L V} (hf : Measurable f)
    {g : X → ℕ → Bool} (hg : Measurable g)
    (hinv : ∀ ⦃x y : X⦄, isoSetoid L V (f x) (f y) → g x = g y) :
    ∃ θ : ℕ → L.Sentenceω, ∀ x, sentenceTheory θ (f x) = g x := by
  have hcoord : ∀ n : ℕ, ∃ ψ : L.Sentenceω, ∀ x, f x ∈ modelsOf ψ ↔ g x n = true :=
    fun n =>
      exists_sentence_mem_modelsOf_iff hf
        ((measurable_pi_apply n).comp hg (measurableSet_singleton true))
        fun x y hxy hx => by simpa [hinv hxy] using hx
  choose θ hθ using hcoord
  refine ⟨θ, fun x => funext fun n => ?_⟩
  rw [Bool.eq_iff_iff, sentenceTheory_eq_true_iff]
  exact hθ n x

/-- **Borel observables on a Borel class.** On a Borel set `C` of configurations on a countable
carrier, every isomorphism-invariant measurable map `g : C → ℕ → Bool` is realized as the
truth sequence of a countable list of `L_{ω₁ω}` sentences. -/
theorem exists_sentenceTheory_eq_on [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C)
    {g : C → ℕ → Bool} (hg : Measurable g)
    (hinv : ∀ ⦃c d : C⦄, isoSetoid L V c.1 d.1 → g c = g d) :
    ∃ θ : ℕ → L.Sentenceω, ∀ c : C, sentenceTheory θ c.1 = g c :=
  have := hC.standardBorel
  exists_sentenceTheory_comp_eq measurable_subtype_coe hg hinv

/-- **Borel observables into a countably separated space.** Along a measurable map `f` from a
standard Borel space `X` into configurations on a countable carrier, every isomorphism-invariant
measurable map `g : X → Y` into a countably separated measurable space has the same fibres as the
truth sequence of a countable list of `L_{ω₁ω}` sentences. -/
theorem exists_sentenceTheory_comp_eq_iff [∀ n, Countable (L.Relations n)] [Countable V]
    {X : Type w'} [MeasurableSpace X] [StandardBorelSpace X]
    {Y : Type*} [MeasurableSpace Y] [CountablySeparated Y]
    {f : X → RelationalConfiguration L V} (hf : Measurable f)
    {g : X → Y} (hg : Measurable g)
    (hinv : ∀ ⦃x y : X⦄, isoSetoid L V (f x) (f y) → g x = g y) :
    ∃ θ : ℕ → L.Sentenceω,
      ∀ x y, sentenceTheory θ (f x) = sentenceTheory θ (f y) ↔ g x = g y := by
  obtain ⟨ι, hι, hinj⟩ := measurable_injection_nat_bool_of_countablySeparated Y
  obtain ⟨θ, hθ⟩ := exists_sentenceTheory_comp_eq hf (hι.comp hg) fun x y hxy =>
    congrArg ι (hinv hxy)
  refine ⟨θ, fun x y => ?_⟩
  rw [hθ x, hθ y, Function.comp_apply, Function.comp_apply, hinj.eq_iff]

/-- **Cantor recovery.** A measurable map from Cantor space into configurations on a countable
carrier whose distinct points map to non-isomorphic configurations is inverted by the truth
sequence of a countable list of `L_{ω₁ω}` sentences. -/
theorem exists_sentenceTheory_comp_eq_id [∀ n, Countable (L.Relations n)] [Countable V]
    {f : (ℕ → Bool) → RelationalConfiguration L V} (hf : Measurable f)
    (hnoniso : ∀ ⦃x y : ℕ → Bool⦄, x ≠ y → ¬ isoSetoid L V (f x) (f y)) :
    ∃ θ : ℕ → L.Sentenceω, ∀ x, sentenceTheory θ (f x) = x :=
  exists_sentenceTheory_comp_eq hf measurable_id fun _ _ hxy =>
    by_contra fun hne => hnoniso hne hxy

/-! ### Sentence-spectrum characterization of thinness -/

/-- **Countable sentence spectra force thinness.** If every countable list of `L_{ω₁ω}`
sentences realizes only countably many truth sequences on a set `C` of configurations on a
countable carrier, then `C` is thin for isomorphism. No Borel or isomorphism-invariance hypothesis
on `C` is needed. -/
theorem isThinOn_of_countable_sentenceTheory_image [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)}
    (h : ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable) :
    (isoSetoid L V).IsThinOn C := by
  rw [Setoid.isThinOn_iff_not_hasCantorAntichainOn]
  intro hcantor
  obtain ⟨f, hf, hC, hnoniso⟩ := Setoid.hasCantorAntichainOn_iff.1 hcantor
  obtain ⟨θ, hθ⟩ :=
    exists_sentenceTheory_comp_eq_id hf.measurable fun _ _ hne => hnoniso _ _ hne
  have huniv : (univ : Set (ℕ → Bool)) ⊆ sentenceTheory θ '' C :=
    fun x _ => ⟨f x, hC x, hθ x⟩
  have hmk : #(ℕ → Bool) = 𝔠 := by simp
  have hcount : Countable (ℕ → Bool) := countable_univ_iff.1 ((h θ).mono huniv)
  exact aleph0_lt_continuum.not_ge (hmk ▸ mk_le_aleph0)

/-- **Thin Borel classes have countable sentence spectra.** On a thin Borel set `C` of
configurations on a countable carrier, every countable list of infinitary sentences with countable
branching realizes only countably many truth sequences. -/
theorem countable_sentenceTheory_image_of_isThinOn [∀ n, Countable (L.Relations n)] [Countable V]
    {ι : Type uι} [Countable ι] {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C)
    (hthin : (isoSetoid L V).IsThinOn C) (θ : ℕ → L.SentenceInf ι) :
    (sentenceTheory θ '' C).Countable := by
  let F : Setoid C := (⊥ : Setoid (ℕ → Bool)).comap fun c => sentenceTheory θ c.1
  have hRF : ∀ x y : C, isoSetoid L V x.1 y.1 → F x y := fun x y hxy =>
    sentenceTheory_eq_of_isoSetoid hxy θ
  have hF : MeasurableSet {p : C × C | F p.1 p.2} := by
    have hmeas : Measurable fun c : C => sentenceTheory θ c.1 :=
      (measurable_sentenceTheory θ).comp measurable_subtype_coe
    exact measurableSet_eq_fun (hmeas.comp measurable_fst) (hmeas.comp measurable_snd)
  have hquot : Countable (Quotient F) :=
    (Setoid.countable_or_hasCantorAntichainOn_of_measurableSet hC (isoSetoid L V) F hRF
      hF).resolve_right (Setoid.isThinOn_iff_not_hasCantorAntichainOn.1 hthin)
  have hrange : range (Quotient.lift (fun c : C => sentenceTheory θ c.1) fun _ _ h => h) =
      sentenceTheory θ '' C := by
    ext s
    simp only [mem_range, Quotient.exists, Quotient.lift_mk, mem_image, Subtype.exists]
    exact exists_congr fun _ => exists_prop
  rw [← hrange]
  exact countable_range _

/-- **Sentence-spectrum characterization of thin Borel classes.** A Borel set `C` of configurations
on a countable carrier in a countable relational vocabulary is thin for isomorphism if and only if
every countable list of `L_{ω₁ω}` sentences realizes only countably many truth sequences on `C`.
No isomorphism invariance of `C` is assumed. -/
theorem isThinOn_iff_countable_sentenceTheory_image [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    (isoSetoid L V).IsThinOn C ↔
      ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' C).Countable :=
  ⟨fun h => countable_sentenceTheory_image_of_isThinOn hC h,
    isThinOn_of_countable_sentenceTheory_image⟩

/-- **Sentence-spectrum characterization of thin sentences.** In a countable relational vocabulary,
an infinitary sentence with countable branching is thin on `ℕ` if and only if every countable list
of `L_{ω₁ω}` sentences realizes only countably many truth sequences on its models on `ℕ`. -/
theorem isThinOnNatModels_iff_countable_sentenceTheory_image [∀ n, Countable (L.Relations n)]
    {ι : Type uι} [Countable ι] {φ : L.SentenceInf ι} :
    IsThinOnNatModels φ ↔
      ∀ θ : ℕ → L.Sentenceω, (sentenceTheory θ '' modelsOf (V := ℕ) φ).Countable :=
  isThinOnNatModels_iff_isThinOn.trans
    (isThinOn_iff_countable_sentenceTheory_image (measurableSet_modelsOf φ))

/-! ### Single-sentence splits -/

/-- **Countable sentence spectra from single-sentence splits.** Let `classOf : C → Q` be any map
whose fibres agree on all sentences in `L.SentenceInf ι` (no surjectivity, topology, or σ-algebra
on `Q`, and no countability on `L`, `V`, or `ι`, is assumed). If every single sentence has a truth
side covering only countably many points of `Q`, then every countable list of sentences realizes
only countably many truth sequences on `C`. -/
theorem countable_sentenceTheory_image_of_splits {ι : Type uι} {Q : Type*}
    {C : Set (RelationalConfiguration L V)} (classOf : C → Q)
    (hclass : ∀ ⦃c d : C⦄, classOf c = classOf d →
      ∀ ψ : L.SentenceInf ι, c.1 ∈ modelsOf ψ ↔ d.1 ∈ modelsOf ψ)
    (hsplit : ∀ ψ : L.SentenceInf ι,
      (classOf '' {c : C | c.1 ∈ modelsOf ψ}).Countable ∨
        (classOf '' {c : C | c.1 ∉ modelsOf ψ}).Countable)
    (θ : ℕ → L.SentenceInf ι) :
    (sentenceTheory θ '' C).Countable := by
  let P : ℕ → range classOf → Prop := fun n q =>
    ∃ c : C, classOf c = q.1 ∧ c.1 ∈ modelsOf (θ n)
  have hP_iff : ∀ (n : ℕ) (q : range classOf) (c : C), classOf c = q.1 →
      (P n q ↔ c.1 ∈ modelsOf (θ n)) := fun n q c hc =>
    ⟨fun ⟨d, hd, hdm⟩ => (hclass (hd.trans hc.symm) (θ n)).1 hdm,
      fun hcm => ⟨c, hc, hcm⟩⟩
  let g : range classOf → ℕ → Bool := fun q => sentenceTheory θ q.2.choose.1
  have hg : ∀ q₁ q₂ : range classOf, (∀ n, P n q₁ ↔ P n q₂) → g q₁ = g q₂ := by
    intro q₁ q₂ hq
    refine sentenceTheory_eq_iff.2 fun n => ?_
    rw [← hP_iff n q₁ q₁.2.choose q₁.2.choose_spec,
      ← hP_iff n q₂ q₂.2.choose q₂.2.choose_spec]
    exact hq n
  have hsplitP : ∀ n, {q : range classOf | P n q}.Countable ∨
      {q : range classOf | ¬ P n q}.Countable := fun n => by
    refine (hsplit (θ n)).imp (fun h => ?_) (fun h => ?_)
    · refine (h.preimage Subtype.val_injective).mono fun q hq => ?_
      obtain ⟨c, hc, hcm⟩ := hq
      exact ⟨c, hcm, hc⟩
    · refine (h.preimage Subtype.val_injective).mono fun q hq => ?_
      refine ⟨q.2.choose, ?_, q.2.choose_spec⟩
      exact fun hmem => hq ((hP_iff n q q.2.choose q.2.choose_spec).2 hmem)
  refine (countable_range_of_splits g hg hsplitP).mono ?_
  rintro _ ⟨c, hc, rfl⟩
  let q : range classOf := ⟨classOf ⟨c, hc⟩, ⟨c, hc⟩, rfl⟩
  refine ⟨q, sentenceTheory_eq_iff.2 fun n => ?_⟩
  exact hclass q.2.choose_spec (θ n)

/-- **Single-sentence splits imply thinness (presentation form).** If a presentation
`classOf : C → Q` of a class `C` of configurations determines truth of `L_{ω₁ω}` sentences and
every sentence has a truth side with countably many points of `Q`, then `C` is thin for
isomorphism. No Borel or invariance hypothesis on `C`, and no surjectivity or measurable structure
on `Q`, is assumed. -/
theorem isThinOn_of_splits_via [∀ n, Countable (L.Relations n)] [Countable V] {Q : Type*}
    {C : Set (RelationalConfiguration L V)} (classOf : C → Q)
    (hclass : ∀ ⦃c d : C⦄, classOf c = classOf d →
      ∀ ψ : L.Sentenceω, c.1 ∈ modelsOf ψ ↔ d.1 ∈ modelsOf ψ)
    (hsplit : ∀ ψ : L.Sentenceω,
      (classOf '' {c : C | c.1 ∈ modelsOf ψ}).Countable ∨
        (classOf '' {c : C | c.1 ∉ modelsOf ψ}).Countable) :
    (isoSetoid L V).IsThinOn C :=
  isThinOn_of_countable_sentenceTheory_image
    (countable_sentenceTheory_image_of_splits classOf hclass hsplit)

/-- **Single-sentence splits imply thinness (quotient form).** If every `L_{ω₁ω}` sentence cuts
a set `C` of configurations on a countable carrier so that one side meets only countably many
isomorphism classes, then `C` is thin for isomorphism. No Borel or invariance hypothesis on `C` is
assumed. -/
theorem isThinOn_of_sentence_splits [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)}
    (hsplit : ∀ θ : L.Sentenceω,
      (Quotient.mk (isoSetoid L V) '' (C ∩ modelsOf θ)).Countable ∨
        (Quotient.mk (isoSetoid L V) '' (C \ modelsOf θ)).Countable) :
    (isoSetoid L V).IsThinOn C := by
  refine isThinOn_of_splits_via (fun c : C => Quotient.mk (isoSetoid L V) c.1)
    (fun c d hcd ψ => (isomorphismInvariant_modelsOf ψ).mem_iff (Quotient.exact hcd)) fun ψ => ?_
  have h1 : (fun c : C => Quotient.mk (isoSetoid L V) c.1) '' {c : C | c.1 ∈ modelsOf ψ} =
      Quotient.mk (isoSetoid L V) '' (C ∩ modelsOf ψ) :=
    Set.ext fun _ => ⟨fun ⟨⟨c, hc⟩, hm, hq⟩ => ⟨c, ⟨hc, hm⟩, hq⟩,
      fun ⟨c, ⟨hc, hm⟩, hq⟩ => ⟨⟨c, hc⟩, hm, hq⟩⟩
  have h2 : (fun c : C => Quotient.mk (isoSetoid L V) c.1) '' {c : C | c.1 ∉ modelsOf ψ} =
      Quotient.mk (isoSetoid L V) '' (C \ modelsOf ψ) :=
    Set.ext fun _ => ⟨fun ⟨⟨c, hc⟩, hm, hq⟩ => ⟨c, ⟨hc, hm⟩, hq⟩,
      fun ⟨c, ⟨hc, hm⟩, hq⟩ => ⟨⟨c, hc⟩, hm, hq⟩⟩
  rw [h1, h2]
  exact hsplit ψ

/-! ### Smoothness and Borel complete invariants -/

/-- **Smooth isomorphism is classification by countably many sentences.** Along a measurable map
`f` from a standard Borel space `X` into configurations on a countable carrier in a countable
relational vocabulary, the pulled-back isomorphism relation is smooth (admits a Borel complete
invariant in Cantor space, or equivalently in any uncountable standard Borel space) if and only if
some countable list of `L_{ω₁ω}` sentences separates isomorphism of images. -/
theorem isSmooth_comap_isoSetoid_iff [∀ n, Countable (L.Relations n)] [Countable V]
    {X : Type w'} [MeasurableSpace X] [StandardBorelSpace X]
    {f : X → RelationalConfiguration L V} (hf : Measurable f) :
    ((isoSetoid L V).comap f).IsSmooth ↔
      ∃ θ : ℕ → L.Sentenceω, ∀ x y,
        isoSetoid L V (f x) (f y) ↔ sentenceTheory θ (f x) = sentenceTheory θ (f y) := by
  constructor
  · intro h
    obtain ⟨g, hg, hiff⟩ := Setoid.isSmooth_iff.1 h
    obtain ⟨θ, hθ⟩ := exists_sentenceTheory_comp_eq hf hg fun x y hxy => (hiff x y).1 hxy
    exact ⟨θ, fun x y => by simpa only [Setoid.comap_rel, hθ x, hθ y] using hiff x y⟩
  · rintro ⟨θ, hθ⟩
    exact Setoid.isSmooth_iff.2 ⟨fun x => sentenceTheory θ (f x),
      (measurable_sentenceTheory θ).comp hf, hθ⟩

/-- **Smooth isomorphism on a Borel class is classification by countably many sentences.** On a
Borel set `C` of configurations on a countable carrier in a countable relational vocabulary,
isomorphism restricted to `C` is smooth if and only if some countable list of `L_{ω₁ω}`
sentences separates the isomorphism classes of `C`. -/
theorem isSmooth_comap_val_isoSetoid_iff [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C) :
    ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth ↔
      ∃ θ : ℕ → L.Sentenceω, ∀ c ∈ C, ∀ d ∈ C,
        isoSetoid L V c d ↔ sentenceTheory θ c = sentenceTheory θ d := by
  have := hC.standardBorel
  rw [isSmooth_comap_isoSetoid_iff measurable_subtype_coe]
  exact exists_congr fun _ =>
    ⟨fun h c hc d hd => h ⟨c, hc⟩ ⟨d, hd⟩, fun h c d => h c.1 c.2 d.1 d.2⟩

/-- **Countably many isomorphism classes are smooth.** Along any measurable map `f` into
configurations on a countable carrier in a countable relational vocabulary, if the pulled-back
isomorphism relation has countably many classes, then it is smooth: Scott sentences make every
isomorphism class Borel. No standard Borel hypothesis on `X` is required. -/
theorem isSmooth_comap_isoSetoid_of_countable [∀ n, Countable (L.Relations n)] [Countable V]
    {X : Type w'} [MeasurableSpace X] {f : X → RelationalConfiguration L V} (hf : Measurable f)
    [Countable (Quotient ((isoSetoid L V).comap f))] :
    ((isoSetoid L V).comap f).IsSmooth := by
  refine Setoid.isSmooth_of_countable_quotient fun x => ?_
  let := (f x).toStructure
  have hclass : {y : X | ((isoSetoid L V).comap f) x y} =
      f ⁻¹' modelsOf (V := V) (scottSentence (L := L) V) := by
    ext y
    simp only [Setoid.comap_rel, isoSetoid_apply, mem_ofPred_eq, mem_preimage, mem_modelsOf]
    exact (@realize_scottSentence_iff L _ _ V (f x).toStructure _ V (f y).toStructure _).symm
  rw [hclass]
  exact (measurableSet_modelsOf (V := V) (scottSentence (L := L) V)).preimage hf

/-- **Smoothness on a thin Borel class is countability of isomorphism classes.** On a thin Borel
set `C` of configurations on a countable carrier in a countable relational vocabulary, isomorphism
is smooth (equivalently, admits a complete countable list of `L_{ω₁ω}` sentences) if and only if
`C` meets only countably many isomorphism classes. In particular, a thin Borel class meeting
uncountably many isomorphism classes admits no Borel complete invariant. -/
theorem isSmooth_comap_val_isoSetoid_iff_countable_quotient_of_isThinOn
    [∀ n, Countable (L.Relations n)] [Countable V]
    {C : Set (RelationalConfiguration L V)} (hC : MeasurableSet C)
    (hthin : (isoSetoid L V).IsThinOn C) :
    ((isoSetoid L V).comap (Subtype.val : C → _)).IsSmooth ↔
      Countable (Quotient ((isoSetoid L V).comap (Subtype.val : C → _))) :=
  ⟨fun hsmooth =>
      (Setoid.countable_or_hasCantorAntichainOn_of_measurableSet hC (isoSetoid L V)
        ((isoSetoid L V).comap Subtype.val) (fun _ _ h => h)
        hsmooth.measurableSet_setOf).resolve_right
        (Setoid.isThinOn_iff_not_hasCantorAntichainOn.1 hthin),
    fun _ => isSmooth_comap_isoSetoid_of_countable measurable_subtype_coe⟩

end TauCeti
