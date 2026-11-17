/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap
public import TauCeti.ModelTheory.RelationalConfiguration.LopezEscobar
public import TauCeti.ModelTheory.Sublanguage
import Mathlib.GroupTheory.Perm.Sign
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.SetTheory.Descriptive.InvariantSeparation

/-!
# Invariant analytic separation and sentence separation

This file establishes three separation results for analytic classes of relational configurations,
building on the López–Escobar theorem (`TauCeti.ModelTheory.RelationalConfiguration.LopezEscobar`)
and abstract invariant Lusin separation (`TauCeti.SetTheory.Descriptive.InvariantSeparation`):

1. **`exists_countable_sublanguage_separating`** (arbitrary `L`, arbitrary `V`): any two disjoint
   analytic sets `A, B ⊆ RelationalConfiguration L V` remain disjoint after projection to a
   countable relational sublanguage `symbSublang ∅ R`. The proof writes `A` and `B` as continuous
   images of Polish spaces `β₁, β₂`; their product `β₁ × β₂` is second countable, so the open cover
   by single-atom disagreements has a countable subcover
   (`TopologicalSpace.isOpen_iUnion_countable`). Only the separation is countable: neither `A` nor
   `B` need depend on countably many symbols.
2. **`invariant_analytic_separation`** (arbitrary `L`, any countable carrier `V`): if `A` and `B`
   are disjoint analytic sets and `B` is invariant under the logic action (`MulAction.IsFixedBlock
   (Equiv.Perm V) B`), some product-measurable action-invariant set `C` contains `A` and is disjoint
   from `B`. Note that `L` need not be relational: projecting along `symbSublangIncl ∅ R` passes to
   a countable relational sublanguage where `Setoid.exists_invariant_measurableSet_separating`
   applies to `isoSetoid`, and the preimage along the reduct map returns to `L`.
   Countability of `V` is sharp: on an uncountable carrier `V` with a unary predicate `P`, the
   singleton `A` of the all-false configuration and the singleton `B` of the all-true configuration
   are disjoint action-invariant analytic sets, yet `mem_iff_of_restrict_finZero_eq_of_uncountable`
   forces every product-measurable invariant set containing `A` to also contain `B`.
3. **`exists_sentence_separating`** (arbitrary relational `L`, **arbitrary carrier `V`** — empty,
   finite, countably infinite, or uncountable): if `A` and `B` are disjoint analytic sets and `B`
   is invariant under `Equiv.Perm V`, then some `θ : L.Sentenceω` satisfies `A ⊆ modelsOf θ` and
   `Disjoint B (modelsOf θ)`.
   * For countable `V`, this follows immediately from `invariant_analytic_separation` and
     `lopezEscobar_action_iff`.
   * For uncountable `V`, `invariant_analytic_separation` fails for product-measurable sets, yet
     **sentence separation still holds!** The key rigidity theorem
     (`perm_smul_eq_of_mem_analyticSet_of_uncountable`, holding for arbitrary `L`, not necessarily
     relational) shows that on an uncountable carrier, every action-invariant analytic set `B`
     consists exclusively of fixed points of `Equiv.Perm V`: if some `c ∈ B` were moved by a
     permutation, finite-tuple swap decomposition and a single fresh vertex would yield an
     uncountable discrete family `(c_w, a_w)` in `B`, contradicting second countability of the
     Polish domain parameterizing `B`. Passing to a countable separating sublanguage `L₀`, the
     fixed-point locus `Fix` is closed and definable by a single `L₀.Sentenceω` (`isFixedSentence`).
     Restricting along `ι : ℕ ↪ V` injects `Fix` into `RelationalConfiguration L₀ ℕ`, preserves
     satisfaction of every `L₀.Sentenceω` on `Fix`, and sends `A₀ ∩ Fix` and `B₀` to disjoint
     analytic sets with `B₁` fixed by `Equiv.Perm ℕ`. The countable case yields `θ₁ : L₀.Sentenceω`,
     and translating `isFixedSentence.not ⊔ θ₁` back to `L` separates `A` from `B`.

Note that in `invariant_analytic_separation` and `exists_sentence_separating`, only `B` is assumed
invariant: `A` need not be invariant (equivalently, the saturation of `A` is disjoint from `B`).

## Main results

* `TauCeti.RelationalConfiguration.exists_countable_sublanguage_separating`: disjoint analytic
  classes are separated by a countable relational sublanguage, for every `L` and every `V`.
* `TauCeti.RelationalConfiguration.invariant_analytic_separation`: invariant Lusin separation in
  `RelationalConfiguration L V`, for every `L` and every countable `V`.
* `TauCeti.RelationalConfiguration.perm_smul_eq_of_mem_analyticSet_of_uncountable`: on an
  uncountable carrier, every element of a permutation-invariant analytic set is fixed by every
  permutation, for every `L`.
* `TauCeti.RelationalConfiguration.exists_sentence_separating`: separating an analytic class from a
  disjoint permutation-invariant analytic class by a single `L_{ω₁ω}` sentence, for every
  relational `L` and every carrier `V`.

## References

* R. L. Vaught, *Invariant sets in topology and logic*, Fund. Math. 82 (1974), 269–294, (10),
  p. 281.
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 14.7 and Theorem 16.8.
* S. Gao, *Invariant Descriptive Set Theory*, CRC Press, 2009, Chapter 11.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46, Cambridge University
  Press, 2016, Corollary 4.25.
-/

public section

universe u v w

open FirstOrder FirstOrder.Language MeasureTheory Set TopologicalSpace
open scoped Pointwise

namespace TauCeti.RelationalConfiguration

section SublanguageSeparation

variable {L : Language.{u, v}} {V : Type w}

/-- Every pair of disjoint analytic sets of configurations has disjoint images in some countable
relational sublanguage `symbSublang ∅ R`. Holds for arbitrary `L` (not necessarily relational or
countable) and arbitrary carrier `V` (possibly uncountable). -/
theorem exists_countable_sublanguage_separating
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hd : Disjoint A B) :
    ∃ R : Set (Σ n, L.Relations n), R.Countable ∧
      Disjoint ((symbSublangIncl ∅ R).reductConfiguration '' A)
        ((symbSublangIncl ∅ R).reductConfiguration '' B) := by
  rcases analyticSet_iff_exists_polishSpace_range.1 hA with ⟨β₁, _, _, f₁, hf₁, rfl⟩
  rcases analyticSet_iff_exists_polishSpace_range.1 hB with ⟨β₂, _, _, f₂, hf₂, rfl⟩
  let U : Atom L V → Set (β₁ × β₂) := fun a => {p | (f₁ p.1).eval a ≠ (f₂ p.2).eval a}
  have hU_open : ∀ a, IsOpen (U a) := fun a =>
    (isClosed_eq ((continuous_eval a).comp (hf₁.comp continuous_fst))
      ((continuous_eval a).comp (hf₂.comp continuous_snd))).isOpen_compl
  obtain ⟨I, hIc, hIcov⟩ := isOpen_iUnion_countable U hU_open
  let symOf : Atom L V → Σ n, L.Relations n := fun a => ⟨a.1, a.2.1⟩
  refine ⟨symOf '' I, hIc.image symOf, disjoint_left.2 ?_⟩
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ ⟨_, ⟨y, rfl⟩, hxy⟩
  have hne : f₁ x ≠ f₂ y := fun heq =>
    disjoint_left.1 hd (mem_range_self x) (heq ▸ mem_range_self y)
  have hmem : (x, y) ∈ ⋃ a, U a := by
    by_contra hnot
    exact hne (ext fun a => by_contra fun hda => hnot (mem_iUnion.2 ⟨a, hda⟩))
  rw [← hIcov] at hmem
  rcases mem_iUnion₂.1 hmem with ⟨a, haI, hda⟩
  let b : Atom (symbSublang ∅ (symOf '' I)) V := atom ⟨a.2.1, ⟨a, haI, rfl⟩⟩ a.2.2
  have hgb : (symbSublangIncl ∅ (symOf '' I)).onAtom b = a := by
    rw [LHom.onAtom_atom, symbSublangIncl_onRelation, atom_def]; rfl
  have heq := congrArg (fun k => k.eval b) hxy
  rw [LHom.eval_reductConfiguration, LHom.eval_reductConfiguration, hgb] at heq
  exact hda heq.symm

end SublanguageSeparation

section CountableSeparation

variable {L : Language.{u, v}} {V : Type w}

/-- A fixed block stays a fixed block under the reduct map of any language homomorphism. -/
private theorem isFixedBlock_image_reductConfiguration {L₀ : Language.{u, v}} (g : L₀ →ᴸ L)
    {B : Set (RelationalConfiguration L V)} (hinv : MulAction.IsFixedBlock (Equiv.Perm V) B) :
    MulAction.IsFixedBlock (Equiv.Perm V) (g.reductConfiguration '' B) := by
  intro σ
  ext c
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨σ • b, ?_, LHom.reductConfiguration_perm_smul g σ b⟩
    rw [← hinv σ]
    exact smul_mem_smul_set hb
  · rintro ⟨b, hb, rfl⟩
    refine ⟨g.reductConfiguration (σ⁻¹ • b), ⟨σ⁻¹ • b, ?_, rfl⟩, ?_⟩
    · rw [← hinv σ⁻¹]; exact smul_mem_smul_set hb
    · dsimp only
      rw [← LHom.reductConfiguration_perm_smul, smul_inv_smul]

/-- A fixed block pulls back to a fixed block under the reduct map of any language homomorphism. -/
private theorem isFixedBlock_preimage_reductConfiguration {L₀ : Language.{u, v}} (g : L₀ →ᴸ L)
    {C : Set (RelationalConfiguration L₀ V)} (hinv : MulAction.IsFixedBlock (Equiv.Perm V) C) :
    MulAction.IsFixedBlock (Equiv.Perm V) (g.reductConfiguration ⁻¹' C) := by
  intro σ
  ext c
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_preimage, mem_preimage,
    LHom.reductConfiguration_perm_smul]
  rw [← Set.mem_smul_set_iff_inv_smul_mem, hinv σ]

/-- **Invariant analytic separation** on any countable carrier `V`, for every language `L` (not
necessarily relational or countable): if `A` and `B` are disjoint analytic sets and `B` is
invariant under the logic action, then some product-measurable action-invariant set `C` contains
`A` and is disjoint from `B`. -/
theorem invariant_analytic_separation [Countable V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hinv : MulAction.IsFixedBlock (Equiv.Perm V) B) (hd : Disjoint A B) :
    ∃ C, A ⊆ C ∧ Disjoint B C ∧ MeasurableSet C ∧ MulAction.IsFixedBlock (Equiv.Perm V) C := by
  obtain ⟨R, hR, hdisj⟩ := exists_countable_sublanguage_separating hA hB hd
  let g : symbSublang (∅ : Set (Σ n, L.Functions n)) R →ᴸ L := symbSublangIncl ∅ R
  have : Countable R := hR.to_subtype
  have : ∀ n, Countable ((symbSublang (∅ : Set (Σ k, L.Functions k)) R).Relations n) := fun n =>
    Function.Injective.countable (f := fun r => (⟨n, r⟩ : Σ k, _)) fun _ _ h =>
      eq_of_heq (Sigma.mk.inj_iff.1 h).2
  let A₀ := g.reductConfiguration '' A
  let B₀ := g.reductConfiguration '' B
  have hA₀ : AnalyticSet A₀ := hA.image_of_continuous (LHom.continuous_reductConfiguration g)
  have hB₀ : AnalyticSet B₀ := hB.image_of_continuous (LHom.continuous_reductConfiguration g)
  have hB₀_inv : IsomorphismInvariant B₀ :=
    isomorphismInvariant_iff_isFixedBlock.2 (isFixedBlock_image_reductConfiguration g hinv)
  have hq : Disjoint (Quotient.mk (isoSetoid _ V) '' A₀) (Quotient.mk (isoSetoid _ V) '' B₀) := by
    refine disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    exact disjoint_left.1 hdisj ha ((hB₀_inv.mem_iff (Quotient.exact hba)).1 hb)
  obtain ⟨C₀, hC₀m, hC₀sat, hAC₀, hC₀B⟩ :=
    (isoSetoid _ V).exists_invariant_measurableSet_separating analyticSet_setOf_isoSetoid
      hA₀ hB₀ hq
  have hC₀_fix : MulAction.IsFixedBlock (Equiv.Perm V) C₀ :=
    isomorphismInvariant_iff_isFixedBlock.1
      (isomorphismInvariant_iff_preimage_image_quotientMk.2 hC₀sat)
  refine ⟨g.reductConfiguration ⁻¹' C₀, image_subset_iff.1 hAC₀, ?_,
    hC₀m.preimage (LHom.measurable_reductConfiguration g),
    isFixedBlock_preimage_reductConfiguration g hC₀_fix⟩
  exact disjoint_left.2 fun b hb hbc => disjoint_left.1 hC₀B hbc ⟨b, hb, rfl⟩

end CountableSeparation

/-! ### Finite-tuple swap decomposition and uncountable rigidity -/

section UncountableRigidity

variable {L : Language.{u, v}} {V : Type w}

/-- If `c` differs on two tuples `xs, ys : Fin n → V` with the same equality pattern, then some
single transposition `Equiv.swap u v` already changes `c` at some intermediate tuple `z`. -/
private theorem exists_swap_ne_of_eq_iff [DecidableEq V] (c : RelationalConfiguration L V) {n : ℕ}
    (R : L.Relations n) (xs ys : Fin n → V) (hpat : ∀ i j, xs i = xs j ↔ ys i = ys j)
    (hne : c.eval (atom R xs) ≠ c.eval (atom R ys)) :
    ∃ (z : Fin n → V) (u v : V),
      c.eval (atom R (⇑(Equiv.swap u v) ∘ z)) ≠ c.eval (atom R z) := by
  let S : Finset V := Finset.univ.image xs ∪ Finset.univ.image ys
  let xs' : Fin n → S := fun i =>
    ⟨xs i, Finset.mem_union_left _ (Finset.mem_image_of_mem xs (Finset.mem_univ i))⟩
  let ys' : Fin n → S := fun i =>
    ⟨ys i, Finset.mem_union_right _ (Finset.mem_image_of_mem ys (Finset.mem_univ i))⟩
  have hpat' : ∀ i j, xs' i = xs' j ↔ ys' i = ys' j := fun i j => by
    simp only [Subtype.ext_iff, xs', ys', hpat]
  obtain ⟨π, -, hπ⟩ := exists_perm_apply_eq_of_eq_iff (fun _ : S => ()) hpat' (fun _ => rfl)
  have hys : Subtype.val ∘ ⇑π ∘ xs' = ys := funext fun i => congrArg Subtype.val (hπ i)
  have hxs : Subtype.val ∘ xs' = xs := rfl
  suffices ∀ σ : Equiv.Perm S,
      c.eval (atom R (Subtype.val ∘ ⇑σ ∘ xs')) ≠ c.eval (atom R xs) →
      ∃ (z : Fin n → V) (u v : V),
        c.eval (atom R (⇑(Equiv.swap u v) ∘ z)) ≠ c.eval (atom R z) from
    this π (by rw [hys]; exact hne.symm)
  intro σ
  induction σ using Equiv.Perm.swap_induction_on with
  | one => intro h; exact (h (congrArg (fun t => c.eval (atom R t)) hxs)).elim
  | swap_mul f x y _ ih =>
    intro hne'
    let z : Fin n → V := Subtype.val ∘ ⇑f ∘ xs'
    have hcomp : Subtype.val ∘ ⇑(Equiv.swap x y * f) ∘ xs' = ⇑(Equiv.swap x.1 y.1) ∘ z := by
      funext i
      simp only [Function.comp_apply, Equiv.Perm.mul_apply, z, Equiv.swap_apply_def,
        apply_ite Subtype.val, Subtype.ext_iff]
    rw [hcomp] at hne'
    by_cases hstep : c.eval (atom R (⇑(Equiv.swap x.1 y.1) ∘ z)) ≠ c.eval (atom R z)
    · exact ⟨z, x.1, y.1, hstep⟩
    · push Not at hstep
      exact ih (hstep ▸ hne')

/-- On an infinite carrier `V`, factoring `Equiv.swap u v` through a single fresh vertex `w`
produces a transposition `Equiv.swap p q` changing `c` with `q` outside the range of the tuple. -/
private theorem exists_fresh_swap_ne [DecidableEq V] [Infinite V] (c : RelationalConfiguration L V)
    {n : ℕ} (R : L.Relations n) (z : Fin n → V) (u v : V)
    (hne : c.eval (atom R (⇑(Equiv.swap u v) ∘ z)) ≠ c.eval (atom R z)) :
    ∃ (z' : Fin n → V) (p q : V), q ∉ Set.range z' ∧
      c.eval (atom R (⇑(Equiv.swap p q) ∘ z')) ≠ c.eval (atom R z') := by
  obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset ((Finset.univ.image z) ∪ {u, v})
  have hwz : w ∉ Set.range z := fun ⟨i, hi⟩ =>
    hw (Finset.mem_union_left _ (hi ▸ Finset.mem_image_of_mem z (Finset.mem_univ i)))
  have hwu : w ≠ u := fun h => hw (Finset.mem_union_right _ (by simp [h]))
  have hwv : w ≠ v := fun h => hw (Finset.mem_union_right _ (by simp [h]))
  have htriple : Equiv.swap w v * Equiv.swap v u * Equiv.swap u w = Equiv.swap u v := by
    calc Equiv.swap w v * Equiv.swap v u * Equiv.swap u w
        = Equiv.swap w v * Equiv.swap v u *
            (Equiv.swap v u * Equiv.swap w v * Equiv.swap v u) := by
          rw [Equiv.swap_mul_swap_mul_swap hwv hwu]
      _ = Equiv.swap w v * (Equiv.swap v u * Equiv.swap v u) *
            Equiv.swap w v * Equiv.swap v u := by
          simp only [mul_assoc]
      _ = Equiv.swap u v := by
          simp only [Equiv.swap_mul_self, mul_one, one_mul, Equiv.swap_comm]
  let z₁ : Fin n → V := ⇑(Equiv.swap u w) ∘ z
  let z₂ : Fin n → V := ⇑(Equiv.swap v u) ∘ z₁
  have hz₃ : ⇑(Equiv.swap w v) ∘ z₂ = ⇑(Equiv.swap u v) ∘ z := by
    funext i
    simpa [z₁, z₂, Function.comp_apply, Equiv.Perm.mul_apply] using
      congrArg (fun σ : Equiv.Perm V => σ (z i)) htriple
  have hu₁ : u ∉ Set.range z₁ := fun ⟨i, hi⟩ =>
    hwz ⟨i, (Equiv.swap u w).injective (by simpa [z₁] using hi)⟩
  have hv₂ : v ∉ Set.range z₂ := fun ⟨i, hi⟩ =>
    hu₁ ⟨i, (Equiv.swap v u).injective (by simpa [z₂] using hi)⟩
  by_cases h1 : c.eval (atom R z₁) ≠ c.eval (atom R z)
  · exact ⟨z, u, w, hwz, h1⟩
  · push Not at h1
    by_cases h2 : c.eval (atom R z₂) ≠ c.eval (atom R z₁)
    · exact ⟨z₁, v, u, hu₁, h2⟩
    · push Not at h2
      refine ⟨z₂, w, v, hv₂, ?_⟩
      rw [hz₃, h2, h1]
      exact hne

/-- An analytic set of configurations cannot contain an uncountable family separated pairwise by
single-atom cylinders. -/
private theorem not_exists_uncountable_discrete_of_analyticSet
    {B : Set (RelationalConfiguration L V)} (hB : AnalyticSet B)
    {ι : Type w} (hι : ¬ Countable ι) (cs : ι → RelationalConfiguration L V)
    (hcs : ∀ i, cs i ∈ B) (as : ι → Atom L V)
    (hsep : ∀ i j, i ≠ j → (cs j).eval (as i) ≠ (cs i).eval (as i)) : False := by
  classical
  rcases analyticSet_iff_exists_polishSpace_range.1 hB with ⟨β, _, _, f, hf, rfl⟩
  choose p hp using fun i => hcs i
  obtain ⟨ℬ, hℬc, -, hℬ⟩ := TopologicalSpace.exists_countable_basis β
  have hopen : ∀ i : ι, IsOpen {x : β | (f x).eval (as i) = (cs i).eval (as i)} := fun i =>
    (isOpen_discrete {(cs i).eval (as i)}).preimage ((continuous_eval (as i)).comp hf)
  have hex : ∀ i : ι,
      ∃ O ∈ ℬ, p i ∈ O ∧ O ⊆ {x : β | (f x).eval (as i) = (cs i).eval (as i)} :=
    fun i => hℬ.isOpen_iff.1 (hopen i) (p i) (by simp [hp i])
  choose O hOℬ hpO hOU using hex
  have hinj : Function.Injective (fun i : ι => (⟨O i, hOℬ i⟩ : ℬ)) := by
    intro i j hij
    by_contra hne
    have hOeq : O i = O j := congrArg Subtype.val hij
    have hpj : p j ∈ O i := hOeq ▸ hpO j
    exact hsep i j hne (by simpa [hp j] using hOU i hpj)
  have : Countable ℬ := hℬc.to_subtype
  exact hι (Function.Injective.countable hinj)

/-- Case 1 of uncountable rigidity: uncountably many fresh vertices `w` preserving `atom R z`
under `Equiv.swap p w` yield a discrete family `{Equiv.swap q w • c}` inside `B`. -/
private theorem false_of_fresh_swap_eq_uncountable [DecidableEq V]
    {B : Set (RelationalConfiguration L V)} (hB : AnalyticSet B)
    {c : RelationalConfiguration L V} (hmem : ∀ τ : Equiv.Perm V, τ • c ∈ B)
    {n : ℕ} {R : L.Relations n} {z : Fin n → V} {p q : V}
    (hqz : q ∉ Set.range z) (hpq : c.eval (atom R (⇑(Equiv.swap p q) ∘ z)) ≠ c.eval (atom R z))
    {W₀ : Set V} (hW₀ : ¬ Countable W₀)
    (hsub : ∀ w ∈ W₀, w ∉ Set.range z ∪ {p, q} ∧
      c.eval (atom R (⇑(Equiv.swap p w) ∘ z)) = c.eval (atom R z)) : False := by
  refine not_exists_uncountable_discrete_of_analyticSet hB hW₀
    (fun w : W₀ => Equiv.swap q w.1 • c) (fun _ => hmem _)
    (fun w : W₀ => atom R (⇑(Equiv.swap p w.1) ∘ z)) fun w w' hne' => ?_
  have hneV : w.1 ≠ w'.1 := fun h => hne' (Subtype.ext h)
  have hw := (hsub w.1 w.2).1
  have hw' := (hsub w'.1 w'.2).1
  have hw1 : ⇑(Equiv.swap q w.1) ∘ ⇑(Equiv.swap p w.1) ∘ z = ⇑(Equiv.swap p q) ∘ z := by
    funext i
    simp only [Function.comp_apply]
    have hzw : z i ≠ w.1 := fun h => hw (Or.inl ⟨i, h⟩)
    have hzq : z i ≠ q := fun h => hqz ⟨i, h⟩
    by_cases hzp : z i = p
    · rw [hzp, Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_left]
    · rw [Equiv.swap_apply_of_ne_of_ne hzp hzw, Equiv.swap_apply_of_ne_of_ne hzq hzw,
        Equiv.swap_apply_of_ne_of_ne hzp hzq]
  have hw2 : ⇑(Equiv.swap q w'.1) ∘ ⇑(Equiv.swap p w.1) ∘ z = ⇑(Equiv.swap p w.1) ∘ z := by
    funext i
    simp only [Function.comp_apply]
    have hzw : z i ≠ w.1 := fun h => hw (Or.inl ⟨i, h⟩)
    have hzw' : z i ≠ w'.1 := fun h => hw' (Or.inl ⟨i, h⟩)
    have hzq : z i ≠ q := fun h => hqz ⟨i, h⟩
    by_cases hzp : z i = p
    · rw [hzp, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (fun h => hw (Or.inr (by simp [h]))) hneV]
    · rw [Equiv.swap_apply_of_ne_of_ne hzp hzw, Equiv.swap_apply_of_ne_of_ne hzq hzw']
  simp only [eval_perm_smul, Equiv.symm_swap, Atom.map_atom, hw1, hw2]
  rw [(hsub w.1 w.2).2]
  exact hpq.symm

/-- Case 2 of uncountable rigidity: uncountably many fresh vertices `w` changing `atom R z`
under `Equiv.swap p w` yield a discrete family `{Equiv.swap p w • c}` inside `B`. -/
private theorem false_of_fresh_swap_ne_uncountable [DecidableEq V]
    {B : Set (RelationalConfiguration L V)} (hB : AnalyticSet B)
    {c : RelationalConfiguration L V} (hmem : ∀ τ : Equiv.Perm V, τ • c ∈ B)
    {n : ℕ} {R : L.Relations n} {z : Fin n → V} {p q : V}
    {W₁ : Set V} (hW₁ : ¬ Countable W₁)
    (hsub : ∀ w ∈ W₁, w ∉ Set.range z ∪ {p, q} ∧
      c.eval (atom R (⇑(Equiv.swap p w) ∘ z)) ≠ c.eval (atom R z)) : False := by
  refine not_exists_uncountable_discrete_of_analyticSet hB hW₁
    (fun w : W₁ => Equiv.swap p w.1 • c) (fun _ => hmem _)
    (fun w : W₁ => atom R (⇑(Equiv.swap p w.1) ∘ z)) fun w w' hne' => ?_
  have hneV : w.1 ≠ w'.1 := fun h => hne' (Subtype.ext h)
  have hw := (hsub w.1 w.2).1
  have hw' := (hsub w'.1 w'.2).1
  have hw1 : ⇑(Equiv.swap p w.1) ∘ ⇑(Equiv.swap p w.1) ∘ z = z := funext fun i => by simp
  have hw2 : ⇑(Equiv.swap p w'.1) ∘ ⇑(Equiv.swap p w.1) ∘ z = ⇑(Equiv.swap p w.1) ∘ z := by
    funext i
    simp only [Function.comp_apply]
    have hzw : z i ≠ w.1 := fun h => hw (Or.inl ⟨i, h⟩)
    have hzw' : z i ≠ w'.1 := fun h => hw' (Or.inl ⟨i, h⟩)
    by_cases hzp : z i = p
    · rw [hzp, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (fun h => hw (Or.inr (by simp [h]))) hneV]
    · rw [Equiv.swap_apply_of_ne_of_ne hzp hzw, Equiv.swap_apply_of_ne_of_ne hzp hzw']
  simp only [eval_perm_smul, Equiv.symm_swap, Atom.map_atom, hw1, hw2]
  exact (hsub w.1 w.2).2

/-- **Uncountable rigidity theorem.** On an uncountable carrier `V`, every element of an analytic
set invariant under the logic action is fixed by every permutation of `V`. Holds for arbitrary `L`
(not necessarily relational or countable). -/
theorem perm_smul_eq_of_mem_analyticSet_of_uncountable (hunc : ¬ Countable V)
    {B : Set (RelationalConfiguration L V)} (hB : AnalyticSet B)
    (hinv : MulAction.IsFixedBlock (Equiv.Perm V) B)
    {c : RelationalConfiguration L V} (hc : c ∈ B) (σ : Equiv.Perm V) :
    σ • c = c := by
  classical
  by_contra hne
  have : Infinite V := not_finite_iff_infinite.1 fun hf => hunc (@Finite.to_countable _ hf)
  have hmem : ∀ (τ : Equiv.Perm V), τ • c ∈ B := fun τ => (hinv τ) ▸ smul_mem_smul_set hc
  obtain ⟨a, ha⟩ : ∃ a : Atom L V, (σ • c).eval a ≠ c.eval a := by
    by_contra hall; push Not at hall; exact hne (ext hall)
  induction a using Atom.induction_atom with
  | @h n R x =>
    rw [eval_perm_smul, Atom.map_atom] at ha
    obtain ⟨z₀, u, v, hswap₀⟩ := exists_swap_ne_of_eq_iff c R (⇑σ.symm ∘ x) x
      (fun i j => σ.symm.injective.eq_iff) ha
    obtain ⟨z, p, q, hqz, hpq⟩ := exists_fresh_swap_ne c R z₀ u v hswap₀
    let W : Set V := (Set.range z ∪ {p, q})ᶜ
    let W₀ : Set V := {w ∈ W | c.eval (atom R (⇑(Equiv.swap p w) ∘ z)) = c.eval (atom R z)}
    let W₁ : Set V := {w ∈ W | c.eval (atom R (⇑(Equiv.swap p w) ∘ z)) ≠ c.eval (atom R z)}
    have hWc : ¬ W.Countable := fun hWc =>
      hunc (Set.countable_univ_iff.1 (by
        rw [← union_compl_self (Set.range z ∪ {p, q})]
        exact ((Set.countable_range z).union (Set.to_countable {p, q})).union hWc))
    by_cases hW₁ : W₁.Countable
    · have hW₀ : ¬ Countable W₀ := fun h => hWc (by
        have hsub : W ⊆ W₀ ∪ W₁ := fun w hw => by
          by_cases he : c.eval (atom R (⇑(Equiv.swap p w) ∘ z)) = c.eval (atom R z)
          · exact Or.inl ⟨hw, he⟩
          · exact Or.inr ⟨hw, he⟩
        exact ((Set.countable_coe_iff.1 h).union hW₁).mono hsub)
      exact false_of_fresh_swap_eq_uncountable hB hmem hqz hpq hW₀ fun _ hw => hw
    · exact false_of_fresh_swap_ne_uncountable hB hmem
        (fun h => hW₁ (Set.countable_coe_iff.1 h)) fun _ hw => hw

/-- On the fixed-point locus `Fix`, restriction along any embedding `ι : ℕ ↪ V` is injective. -/
private theorem injOn_restrict_fixed (ι : ℕ ↪ V) :
    Set.InjOn (restrict (L := L) ι) {c | ∀ σ : Equiv.Perm V, σ • c = c} := by
  classical
  intro c hc d hd hcd
  ext a
  induction a using Atom.induction_atom with
  | @h n R x =>
    let S : Fin n → Finset (Fin n) := fun i => Finset.univ.filter fun j => x j = x i
    have hSne : ∀ i, (S i).Nonempty := fun i => ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, rfl⟩⟩
    let y : Fin n → ℕ := fun i => ((S i).min' (hSne i)).val
    have hpat : ∀ i j : Fin n, x i = x j ↔ ι (y i) = ι (y j) := by
      intro i j
      rw [ι.injective.eq_iff]
      refine ⟨fun hij => by simp only [y, S, hij], fun hij => ?_⟩
      have hmin : (S i).min' (hSne i) = (S j).min' (hSne j) := Fin.ext hij
      have hmi := (Finset.mem_filter.1 (Finset.min'_mem (S i) (hSne i))).2
      have hmj := (Finset.mem_filter.1 (Finset.min'_mem (S j) (hSne j))).2
      rw [← hmi, hmin, hmj]
    obtain ⟨τ, -, hτ⟩ := exists_perm_apply_eq_of_eq_iff (fun _ : V => ()) hpat (fun _ => rfl)
    have hτ' : ⇑τ ∘ x = ι ∘ y := funext hτ
    have hcx : c.eval (atom R x) = c.eval (atom R (ι ∘ y)) := by
      have h := congrArg (fun k => k.eval (atom R x)) (hc τ⁻¹)
      simpa [eval_perm_smul, Atom.map_atom, Equiv.Perm.inv_def, hτ'] using h.symm
    have hdx : d.eval (atom R x) = d.eval (atom R (ι ∘ y)) := by
      have h := congrArg (fun k => k.eval (atom R x)) (hd τ⁻¹)
      simpa [eval_perm_smul, Atom.map_atom, Equiv.Perm.inv_def, hτ'] using h.symm
    have hval := congrArg (fun k => k.eval (atom R y)) hcd
    simp only [eval_restrict, Atom.map_atom] at hval
    rw [hcx, hdx, hval]

/-- Every fixed point of `Equiv.Perm V` restricts along `ι : ℕ ↪ V` to a fixed point of
`Equiv.Perm ℕ`. -/
private theorem perm_smul_restrict_eq_of_fixed (ι : ℕ ↪ V)
    {c : RelationalConfiguration L V} (hc : ∀ σ : Equiv.Perm V, σ • c = c)
    (π : Equiv.Perm ℕ) : π • c.restrict ι = c.restrict ι := by
  ext a
  induction a using Atom.induction_atom with
  | @h n R y =>
    have hpat : ∀ i j : Fin n, ι (y i) = ι (y j) ↔ ι (π.symm (y i)) = ι (π.symm (y j)) :=
      fun i j => by rw [ι.injective.eq_iff, ι.injective.eq_iff, π.symm.injective.eq_iff]
    obtain ⟨τ, -, hτ⟩ := exists_perm_apply_eq_of_eq_iff (fun _ : V => ())
      (a := ι ∘ y) (b := ι ∘ ⇑π.symm ∘ y) hpat (fun _ => rfl)
    have hτ' : ⇑τ ∘ (ι ∘ y) = ι ∘ ⇑π.symm ∘ y := funext hτ
    have h := congrArg (fun k => k.eval (atom R (ι ∘ y))) (hc τ⁻¹)
    simpa [eval_perm_smul, eval_restrict, Atom.map_atom, Equiv.Perm.inv_def,
      Function.comp_assoc, hτ'] using h

/-- The fixed-point locus `{c | ∀ σ : Equiv.Perm V, σ • c = c}` is closed. -/
private theorem isClosed_fixedPoints :
    IsClosed {c : RelationalConfiguration L V | ∀ σ : Equiv.Perm V, σ • c = c} := by
  have heq : {c : RelationalConfiguration L V | ∀ σ : Equiv.Perm V, σ • c = c} =
      ⋂ σ : Equiv.Perm V, {c | σ • c = c} := by ext c; simp
  rw [heq]
  exact isClosed_iInter fun σ => isClosed_eq (continuous_const_smul σ) continuous_id

end UncountableRigidity

/-! ### Sentence defining permutation fixed points and elementary transfer -/

section FixedPointSentence

variable {L : Language.{u, v}} [L.IsRelational]

/-- The bounded formula in `n + n` variables asserting that the first `n` variables have the same
equality pattern as the last `n` variables. -/
private def samePatternFormula (n : ℕ) : L.BoundedFormulaω Empty (n + n) :=
  BoundedFormulaInf.iInfAlong (TauCeti.IndexCoding.ofEncodable (Fin n × Fin n)) fun p =>
    (BoundedFormulaInf.equal (.var (.inr (Fin.castAdd n p.1)))
      (.var (.inr (Fin.castAdd n p.2)))).iff
      (BoundedFormulaInf.equal (.var (.inr (Fin.natAdd n p.1)))
        (.var (.inr (Fin.natAdd n p.2))))

/-- In a countable relational vocabulary, the `L_{ω₁ω}` sentence characterizing fixed points of the
logic action: for every relation symbol `R`, tuples with the same equality pattern receive the same
truth value. -/
private noncomputable def isFixedSentence [Countable (Σ n, L.Relations n)] : L.Sentenceω :=
  BoundedFormulaInf.iInfAlong
    (TauCeti.IndexCoding.ofEncodableWith (Encodable.ofCountable (Σ n, L.Relations n))) fun s =>
      ((samePatternFormula s.1).imp
        ((BoundedFormulaInf.rel s.2 fun i => .var (.inr (Fin.castAdd s.1 i))).iff
          (BoundedFormulaInf.rel s.2 fun i => .var (.inr (Fin.natAdd s.1 i))))).alls

/-- On EVERY carrier `V`, `modelsOf isFixedSentence` is precisely the set of configurations fixed
by every permutation of `V`. -/
private theorem mem_modelsOf_isFixedSentence_iff [Countable (Σ n, L.Relations n)] {V : Type w}
    (c : RelationalConfiguration L V) :
    c ∈ modelsOf (isFixedSentence (L := L)) ↔ ∀ σ : Equiv.Perm V, σ • c = c := by
  let := c.toStructure
  rw [mem_modelsOf, isFixedSentence, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_iInfAlong]
  constructor
  · intro h σ
    ext a
    induction a using Atom.induction_atom with
    | @h n R x =>
      rw [eval_perm_smul, Atom.map_atom]
      have hR := h ⟨n, R⟩
      rw [BoundedFormulaInf.realize_alls] at hR
      let xy : Fin (n + n) → V := Fin.addCases (⇑σ.symm ∘ x) x
      have hpat : (samePatternFormula (L := L) n).Realize Empty.elim xy := by
        simp only [samePatternFormula, BoundedFormulaInf.realize_iInfAlong,
          BoundedFormulaInf.realize_iff, BoundedFormulaInf.realize_equal,
          Term.realize_var, Sum.elim_inr]
        intro ⟨i, j⟩
        simp only [xy, Fin.addCases_left, Fin.addCases_right]
        exact σ.symm.injective.eq_iff
      have hstep := (BoundedFormulaInf.realize_imp.1 (hR xy)) hpat
      simp only [BoundedFormulaInf.realize_iff, BoundedFormulaInf.realize_rel, Term.realize_var,
        Sum.elim_inr, toStructure_relMap, xy, Fin.addCases_left, Fin.addCases_right] at hstep
      exact Bool.eq_iff_iff.2 (by simpa [Function.comp_def] using hstep)
  · intro hfix ⟨n, R⟩
    rw [BoundedFormulaInf.realize_alls]
    intro xy
    rw [BoundedFormulaInf.realize_imp]
    intro hpat
    simp only [samePatternFormula, BoundedFormulaInf.realize_iInfAlong,
      BoundedFormulaInf.realize_iff, BoundedFormulaInf.realize_equal,
      Term.realize_var, Sum.elim_inr] at hpat
    let xs : Fin n → V := fun i => xy (Fin.castAdd n i)
    let ys : Fin n → V := fun i => xy (Fin.natAdd n i)
    obtain ⟨τ, -, hτ⟩ := exists_perm_apply_eq_of_eq_iff (a := xs) (b := ys) (fun _ : V => ())
      (fun i j => hpat (i, j)) (fun _ => rfl)
    have hτ' : ⇑τ ∘ xs = ys := funext hτ
    have hval := congrArg (fun k => k.eval (atom R xs)) (hfix τ⁻¹)
    rw [eval_perm_smul, Atom.map_atom, Equiv.Perm.inv_def, Equiv.symm_symm, hτ'] at hval
    simp only [BoundedFormulaInf.realize_iff, BoundedFormulaInf.realize_rel, Term.realize_var,
      Sum.elim_inr, toStructure_relMap]
    exact iff_of_eq (congrArg (· = true) hval.symm)

/-- In a relational language, any term commutes with any function on variables. -/
private theorem term_realize_comp {n : ℕ} {V : Type w} (t : L.Term (Empty ⊕ Fin n))
    (c : RelationalConfiguration L V) (ι : ℕ → V) (xs : Fin n → ℕ) :
    @Term.realize L V c.toStructure _ (Sum.elim Empty.elim (ι ∘ xs)) t =
      ι (@Term.realize L ℕ (c.restrict ι).toStructure _ (Sum.elim Empty.elim xs) t) := by
  induction t with
  | var v =>
    rcases v with e | i
    · exact Empty.elim e
    · rfl
  | func f _ => exact isEmptyElim f

/-- Transporting satisfaction along the transposition `Equiv.swap (ι a) b` when `c` is fixed by
every permutation and `a ∉ range xs`, `b ∉ range ι`. -/
private theorem realize_swap_snoc {V : Type w} {ιIdx : Type*}
    {c : RelationalConfiguration L V} (hfix : ∀ σ : Equiv.Perm V, σ • c = c)
    (ι : ℕ ↪ V) {m : ℕ} (φ : L.BoundedFormulaInf ιIdx Empty (m + 1)) (xs : Fin m → ℕ)
    {a : ℕ} (ha : a ∉ Finset.univ.image xs) {b : V} (hb : ¬ ∃ k : ℕ, ι k = b)
    (h1 : @BoundedFormulaInf.Realize L ιIdx Empty V c.toStructure (m + 1) φ Empty.elim
      (Fin.snoc (ι ∘ xs) (ι a))) :
    @BoundedFormulaInf.Realize L ιIdx Empty V c.toStructure (m + 1) φ Empty.elim
      (Fin.snoc (ι ∘ xs) b) := by
  classical
  let σ : Equiv.Perm V := Equiv.swap (ι a) b
  have hσc : c.restrict σ = c := by
    ext e
    have h := congrArg (fun k => k.eval e) (hfix σ⁻¹)
    simpa [eval_perm_smul, eval_restrict, Equiv.Perm.inv_def] using h
  let e : @Language.Equiv L V V c.toStructure c.toStructure :=
    let : L.Structure V := c.toStructure
    { toEquiv := σ
      map_fun' := fun f _ => isEmptyElim f
      map_rel' := fun R y => by
        have hxy := congrArg (fun k => k.eval (atom R y)) hσc
        simpa [toStructure_relMap, eval_restrict, Atom.map_atom] using
          iff_of_eq (congrArg (· = true) hxy) }
  have htr := @StrongHomClass.realize_boundedFormulaInf L ιIdx Empty (m + 1) V V
    c.toStructure c.toStructure _ _ _ e φ Empty.elim (Fin.snoc (ι ∘ xs) (ι a))
  have hcomp : e ∘ Empty.elim = Empty.elim := Subsingleton.elim _ _
  have he : ∀ x, e x = σ x := fun _ => rfl
  have hval : ⇑e ∘ Fin.snoc (ι ∘ xs) (ι a) = Fin.snoc (ι ∘ xs) b := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.comp_apply, Fin.snoc_last, he, σ, Equiv.swap_apply_left]
    · have hne1 : ι (xs j) ≠ ι a := fun heq =>
        ha (by rw [← ι.injective heq]; exact Finset.mem_image_of_mem xs (Finset.mem_univ j))
      have hne2 : ι (xs j) ≠ b := fun heq => hb ⟨xs j, heq⟩
      simp only [Function.comp_apply, Fin.snoc_castSucc, he, σ]
      exact Equiv.swap_apply_of_ne_of_ne hne1 hne2
  rw [hcomp, hval] at htr
  exact htr.2 h1

/-- If `c` is fixed by every permutation of `V`, then restricting `c` along an embedding
`ι : ℕ ↪ V` is an elementary embedding for ALL of `L_{ω₁ω}`. -/
private theorem realize_boundedFormulaInf_restrict_iff {V : Type w} {ιIdx : Type*}
    {c : RelationalConfiguration L V} (hfix : ∀ σ : Equiv.Perm V, σ • c = c)
    (ι : ℕ ↪ V) {n : ℕ} (φ : L.BoundedFormulaInf ιIdx Empty n) (xs : Fin n → ℕ) :
    @BoundedFormulaInf.Realize L ιIdx Empty ℕ (c.restrict ι).toStructure n φ Empty.elim xs ↔
      @BoundedFormulaInf.Realize L ιIdx Empty V c.toStructure n φ Empty.elim (ι ∘ xs) := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ =>
    simp only [BoundedFormulaInf.realize_equal, term_realize_comp _ c ι xs]
    exact ι.injective.eq_iff.symm
  | rel R ts =>
    simp only [BoundedFormulaInf.realize_rel, toStructure_relMap, eval_restrict, Atom.map_atom]
    refine iff_of_eq (congrArg (fun y => c.eval (atom R y) = true) (funext fun i => ?_))
    exact (term_realize_comp (ts i) c ι xs).symm
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [BoundedFormulaInf.realize_imp, ih₁ xs, ih₂ xs]
  | iSup φs ih =>
    simp only [BoundedFormulaInf.realize_iSup]
    exact exists_congr fun k => ih k xs
  | iInf φs ih =>
    simp only [BoundedFormulaInf.realize_iInf]
    exact forall_congr' fun k => ih k xs
  | all φ ih =>
    simp only [BoundedFormulaInf.realize_all]
    constructor
    · intro h b
      have hsnoc : ∀ a : ℕ, ι ∘ Fin.snoc xs a = Fin.snoc (ι ∘ xs) (ι a) := fun a => by
        ext i; refine Fin.lastCases ?_ ?_ i <;> simp
      by_cases hb : ∃ a : ℕ, ι a = b
      · obtain ⟨a, rfl⟩ := hb
        exact hsnoc a ▸ (ih (Fin.snoc xs a)).1 (h a)
      · obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset (Finset.univ.image xs)
        exact realize_swap_snoc hfix ι φ xs ha hb (hsnoc a ▸ (ih (Fin.snoc xs a)).1 (h a))
    · intro h a
      have hsnoc : ι ∘ Fin.snoc xs a = Fin.snoc (ι ∘ xs) (ι a) := by
        ext i; refine Fin.lastCases ?_ ?_ i <;> simp
      exact (ih (Fin.snoc xs a)).2 (hsnoc ▸ h (ι a))

/-- Special case of `realize_boundedFormulaInf_restrict_iff` for sentences. -/
private theorem mem_modelsOf_restrict_iff_of_perm_smul_eq {V : Type w}
    {c : RelationalConfiguration L V} (hfix : ∀ σ : Equiv.Perm V, σ • c = c)
    (ι : ℕ ↪ V) (φ : L.Sentenceω) :
    c.restrict ι ∈ modelsOf φ ↔ c ∈ modelsOf φ := by
  let : L.Structure ℕ := (c.restrict ι).toStructure
  let : L.Structure V := c.toStructure
  rw [mem_modelsOf, mem_modelsOf, SentenceInf.realize_def, SentenceInf.realize_def,
    FormulaInf.realize_def, FormulaInf.realize_def]
  have h1 := @realize_boundedFormulaInf_restrict_iff L _ V ℕ c hfix ι 0 φ
    (@default (Fin 0 → ℕ) Unique.instInhabited)
  have hV : (ι ∘ (@default (Fin 0 → ℕ) Unique.instInhabited)) =
      (@default (Fin 0 → V) Unique.instInhabited) := Subsingleton.elim _ _
  rwa [hV] at h1

end FixedPointSentence

/-! ### Invariant sentence separation (all relational languages, all carriers) -/

section SentenceSeparation

variable {L : Language.{u, v}} [L.IsRelational] {V : Type w}

/-- Countable-carrier sentence separation: immediate from `invariant_analytic_separation` and
`lopezEscobar_action_iff`. -/
private theorem exists_sentence_separating_of_countable [Countable V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hinv : MulAction.IsFixedBlock (Equiv.Perm V) B) (hd : Disjoint A B) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) := by
  obtain ⟨C, hAC, hBC, hCm, hCinv⟩ := invariant_analytic_separation hA hB hinv hd
  obtain ⟨θ, rfl⟩ := lopezEscobar_action_iff.1 ⟨hCm, hCinv⟩
  exact ⟨θ, hAC, hBC⟩

/-- Restricting fixed points along `ι : ℕ ↪ V` yields a fixed block for `Equiv.Perm ℕ`. -/
private theorem isFixedBlock_restrict_image_of_fixed {L₀ : Language.{u, v}} (ι : ℕ ↪ V)
    {B₀ : Set (RelationalConfiguration L₀ V)}
    (hfix : ∀ c ∈ B₀, ∀ σ : Equiv.Perm V, σ • c = c) :
    MulAction.IsFixedBlock (Equiv.Perm ℕ) (restrict ι '' B₀) := by
  intro π; ext x; constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, (perm_smul_restrict_eq_of_fixed ι (hfix b hb) π).symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.restrict ι, ⟨b, hb, rfl⟩, perm_smul_restrict_eq_of_fixed ι (hfix b hb) π⟩

/-- Uncountable-carrier sentence separation: projects to a countable separating sublanguage,
defines the fixed-point locus by `isFixedSentence`, and reduces to `ℕ` via elementary transfer. -/
private theorem exists_sentence_separating_of_uncountable (hC : ¬ Countable V)
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hinv : MulAction.IsFixedBlock (Equiv.Perm V) B) (hd : Disjoint A B) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) := by
  obtain ⟨R, hR, hdisj⟩ := exists_countable_sublanguage_separating hA hB hd
  let g : symbSublang (∅ : Set (Σ n, L.Functions n)) R →ᴸ L := symbSublangIncl ∅ R
  have : Countable R := hR.to_subtype
  let A₀ := g.reductConfiguration '' A
  let B₀ := g.reductConfiguration '' B
  have hA₀ : AnalyticSet A₀ := hA.image_of_continuous (LHom.continuous_reductConfiguration g)
  have hB₀ : AnalyticSet B₀ := hB.image_of_continuous (LHom.continuous_reductConfiguration g)
  have hB₀_fix := isFixedBlock_image_reductConfiguration g hinv
  let Fix : Set (RelationalConfiguration (symbSublang ∅ R) V) :=
    {c | ∀ σ : Equiv.Perm V, σ • c = c}
  have hB₀_sub : B₀ ⊆ Fix := fun c hc σ =>
    perm_smul_eq_of_mem_analyticSet_of_uncountable hC hB₀ hB₀_fix hc σ
  have : Infinite V := not_finite_iff_infinite.1 fun hf => hC (@Finite.to_countable _ hf)
  let ι : ℕ ↪ V := Infinite.natEmbedding V
  have hA₀F : AnalyticSet (A₀ ∩ Fix) :=
    let m : MeasurableSpace (RelationalConfiguration (symbSublang ∅ R) V) := borel _
    @AnalyticSet.inter_measurableSet _ _ m (@BorelSpace.mk _ _ m rfl) _ _ hA₀
      (MeasurableSpace.measurableSet_generateFrom (s := {s | IsOpen s})
        isClosed_fixedPoints.isOpen_compl).of_compl
  have hdisj₁ : Disjoint (restrict ι '' (A₀ ∩ Fix)) (restrict ι '' B₀) := by
    refine disjoint_left.2 ?_
    rintro _ ⟨a, ⟨ha₀, haF⟩, rfl⟩ ⟨b, hb₀, hba⟩
    exact disjoint_left.1 hdisj ha₀ (injOn_restrict_fixed ι haF (hB₀_sub hb₀) hba.symm ▸ hb₀)
  obtain ⟨θ₁, hA₁θ, hB₁θ⟩ := exists_sentence_separating_of_countable
    (hA₀F.image_of_continuous (continuous_restrict ι))
    (hB₀.image_of_continuous (continuous_restrict ι))
    (isFixedBlock_restrict_image_of_fixed ι fun _ hc => hB₀_sub hc) hdisj₁
  refine ⟨g.onBoundedFormulaInf (isFixedSentence.not ⊔ θ₁), ?_, ?_⟩
  · intro c hc
    rw [mem_modelsOf, LHom.realize_sentenceInf_reductConfiguration, ← mem_modelsOf,
      modelsOf_sup, modelsOf_not]
    by_cases hfix : g.reductConfiguration c ∈ Fix
    · exact Or.inr ((mem_modelsOf_restrict_iff_of_perm_smul_eq hfix ι θ₁).1
        (hA₁θ ⟨g.reductConfiguration c, ⟨⟨c, hc, rfl⟩, hfix⟩, rfl⟩))
    · exact Or.inl (by rwa [mem_compl_iff, mem_modelsOf_isFixedSentence_iff])
  · refine disjoint_left.2 fun c hc hθ => ?_
    rw [mem_modelsOf, LHom.realize_sentenceInf_reductConfiguration, ← mem_modelsOf,
      modelsOf_sup, modelsOf_not] at hθ
    have hfix : g.reductConfiguration c ∈ Fix := hB₀_sub ⟨c, hc, rfl⟩
    rcases hθ with hnot | hreal
    · exact hnot (mem_modelsOf_isFixedSentence_iff _ |>.2 hfix)
    · exact disjoint_left.1 hB₁θ ⟨g.reductConfiguration c, ⟨c, hc, rfl⟩, rfl⟩
        ((mem_modelsOf_restrict_iff_of_perm_smul_eq hfix ι θ₁).2 hreal)

/-- **Sentence separation for disjoint analytic classes.** For every relational language `L`
(possibly uncountable) and every carrier `V` (empty, finite, countably infinite, or uncountable),
if `A` and `B` are disjoint analytic classes of configurations and `B` is invariant under the logic
action `Equiv.Perm V`, then there exists a single sentence `θ : L.Sentenceω` with `A ⊆ modelsOf θ`
and `Disjoint B (modelsOf θ)`. -/
theorem exists_sentence_separating
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hinv : MulAction.IsFixedBlock (Equiv.Perm V) B) (hd : Disjoint A B) :
    ∃ θ : L.Sentenceω, A ⊆ modelsOf θ ∧ Disjoint B (modelsOf θ) := by
  by_cases hC : Countable V
  · exact exists_sentence_separating_of_countable hA hB hinv hd
  · exact exists_sentence_separating_of_uncountable hC hA hB hinv hd

end SentenceSeparation

end TauCeti.RelationalConfiguration
