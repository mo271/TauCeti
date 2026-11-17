/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import TauCeti.CategoryTheory.Subobject.Subquotient.Comp
import TauCeti.CategoryTheory.Subobject.Pullback

/-!
# Cycle and boundary towers of a spectral sequence

Given a spectral sequence `E : SpectralSequence C c r₀` in an abelian category `C` and a position
`pq : κ`, each page object `(E.page r).X pq` is inductively presented as a subquotient
`Z_r(pq) / B_r(pq)` of the initial object `(E.page r₀).X pq`:

* at the starting page `r₀`, the presentation is the identity presentation with `B_{r₀} = ⊥` and
  `Z_{r₀} = ⊤`;
* passing from page `r` to page `r + 1`, the presentation is composed with the homology
  presentation of the short complex `(E.page r).sc pq` and transported along `E.iso r (r + 1) pq`,
  lifting the kernel of `(E.page r).dFrom pq` to `Z_{r+1}(pq)` and the image of
  `(E.page r).dTo pq` to `B_{r+1}(pq)`.

The resulting towers satisfy `B_r ≤ B_{r+1} ≤ Z_{r+1} ≤ Z_r` for every `r ≥ r₀`, detect the
vanishing of outgoing and incoming differentials on page `r` via `Z_{r+1} = Z_r` and
`B_{r+1} = B_r`, are natural with respect to morphisms of spectral sequences (inducing the page-`r`
components on the subquotient presentations), and rebase compatibly when truncating `E` to start at
a later page `s ≥ r₀`.

## Main definitions

* `CategoryTheory.SpectralSequence.fromPage`: truncate a spectral sequence to start at a later page
  `s ≥ r₀`.
* `CategoryTheory.SpectralSequence.pagePresentation`: the subquotient presentation of
  `(E.page r).X pq` inside `(E.page r₀).X pq`.
* `CategoryTheory.SpectralSequence.cyclesSubobject`: the `r`-th cycle subobject `Z_r(pq)`.
* `CategoryTheory.SpectralSequence.boundariesSubobject`: the `r`-th boundary subobject `B_r(pq)`.

## Main results

* `CategoryTheory.SpectralSequence.boundariesSubobject_mono`,
  `CategoryTheory.SpectralSequence.cyclesSubobject_anti`,
  `CategoryTheory.SpectralSequence.boundariesSubobject_le_cyclesSubobject_of_pages`: monotonicity
  and interleaving of the cycle and boundary towers.
* `CategoryTheory.SpectralSequence.cyclesSubobject_add_one_eq_iff`,
  `CategoryTheory.SpectralSequence.boundariesSubobject_add_one_eq_iff`: stability of a single step
  in terms of vanishing outgoing and incoming differentials.
* `CategoryTheory.SpectralSequence.isZero_page_X_iff`: vanishing of a page object in terms of
  `B_r = Z_r`.
* `CategoryTheory.SpectralSequence.pagePresentation_map`: naturality of the presentations for a
  morphism of spectral sequences.
* `CategoryTheory.SpectralSequence.pagePresentation_comp_fromPage`: rebasing compatibility from a
  later page `s ≥ r₀`.

## References

* [The Stacks Project, Tag 011N](https://stacks.math.columbia.edu/tag/011N)
* E. Helle and J. Rognes, *Boardman's whole-plane obstruction group for Cartan–Eilenberg systems*,
  arXiv:2408.05989 (2024), Lemma 2.2.
-/

public section

namespace CategoryTheory.SpectralSequence

open Category Limits TauCeti

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section FromPage

/-- Truncate a spectral sequence `E` starting at `r₀` to a spectral sequence starting at a later
page `s ≥ r₀`, keeping the same pages and homology isomorphisms for all `r ≥ s`. -/
abbrev fromPage (E : SpectralSequence C c r₀) (s : ℤ) (hs : r₀ ≤ s) :
    SpectralSequence C c s where
  page r hr := E.page r (hs.trans hr)
  iso r r' pq hrr' hr := E.iso r r' pq hrr' (hs.trans hr)

/-- The morphism between truncated spectral sequences induced by `f : E ⟶ E'`. -/
@[expose]
def fromPageMap {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (s : ℤ) (hs : r₀ ≤ s) :
    E.fromPage s hs ⟶ E'.fromPage s hs where
  hom r hr := f.hom r (hs.trans hr)
  comm r r' pq hrr' hr := f.comm r r' pq hrr' (hs.trans hr)

@[simp]
lemma fromPageMap_hom {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (s : ℤ) (hs : r₀ ≤ s)
    (r : ℤ) (hr : s ≤ r) :
    (fromPageMap f s hs).hom r hr = f.hom r (hs.trans hr) :=
  rfl

/-- Truncation of spectral sequences to a later starting page `s ≥ r₀`, as a functor. -/
@[expose]
def fromPageFunctor (C : Type*) [Category* C] [Abelian C] {κ : Type*} (c : ℤ → ComplexShape κ)
    (r₀ s : ℤ) (hs : r₀ ≤ s) : SpectralSequence C c r₀ ⥤ SpectralSequence C c s where
  obj E := E.fromPage s hs
  map f := fromPageMap f s hs

@[simp]
lemma fromPageFunctor_obj (C : Type*) [Category* C] [Abelian C] {κ : Type*}
    (c : ℤ → ComplexShape κ) (r₀ s : ℤ) (hs : r₀ ≤ s) (E : SpectralSequence C c r₀) :
    (fromPageFunctor C c r₀ s hs).obj E = E.fromPage s hs :=
  rfl

@[simp]
lemma fromPageFunctor_map (C : Type*) [Category* C] [Abelian C] {κ : Type*}
    (c : ℤ → ComplexShape κ) (r₀ s : ℤ) (hs : r₀ ≤ s) {E E' : SpectralSequence C c r₀}
    (f : E ⟶ E') :
    (fromPageFunctor C c r₀ s hs).map f = fromPageMap f s hs :=
  rfl

end FromPage

section Towers

variable (E : SpectralSequence C c r₀)

/-- The canonical subquotient presentation of `(E.page r).X pq` inside `(E.page r₀).X pq`,
constructed by induction on `r ≥ r₀`. -/
noncomputable def pagePresentation (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    SubquotientPresentation ((E.page r₀ le_rfl).X pq) ((E.page r hr).X pq) :=
  Int.leInduction
    (motive := fun r hr ↦
      SubquotientPresentation ((E.page r₀ le_rfl).X pq) ((E.page r hr).X pq))
    (SubquotientPresentation.refl _)
    (fun s hs p ↦
      (p.comp (SubquotientPresentation.ofShortComplex ((E.page s hs).sc pq))).transIso
        (E.iso s (s + 1) pq rfl hs))
    r hr

@[simp]
lemma pagePresentation_self (pq : κ) :
    E.pagePresentation pq r₀ le_rfl = SubquotientPresentation.refl _ :=
  Int.leInduction_base _ _

lemma pagePresentation_add_one (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.pagePresentation pq (r + 1) (Int.le_add_one hr) =
      ((E.pagePresentation pq r hr).comp
        (SubquotientPresentation.ofShortComplex ((E.page r hr).sc pq))).transIso
        (E.iso r (r + 1) pq rfl hr) :=
  Int.leInduction_add_one _ _ r hr

/-- The `r`-th cycle subobject `Z_r(pq)` of `(E.page r₀).X pq`. -/
@[expose]
noncomputable def cyclesSubobject (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    Subobject ((E.page r₀ le_rfl).X pq) :=
  (E.pagePresentation pq r hr).upper

/-- The `r`-th boundary subobject `B_r(pq)` of `(E.page r₀).X pq`. -/
@[expose]
noncomputable def boundariesSubobject (pq : κ) (r : ℤ) (hr : r₀ ≤ r := by lia) :
    Subobject ((E.page r₀ le_rfl).X pq) :=
  (E.pagePresentation pq r hr).lower

@[simp]
lemma pagePresentation_upper (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (E.pagePresentation pq r hr).upper = E.cyclesSubobject pq r hr :=
  rfl

@[simp]
lemma pagePresentation_lower (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (E.pagePresentation pq r hr).lower = E.boundariesSubobject pq r hr :=
  rfl

@[simp]
lemma cyclesSubobject_self (pq : κ) : E.cyclesSubobject pq r₀ le_rfl = ⊤ := by
  simp [cyclesSubobject]

@[simp]
lemma boundariesSubobject_self (pq : κ) : E.boundariesSubobject pq r₀ le_rfl = ⊥ := by
  simp [boundariesSubobject]

lemma cyclesSubobject_add_one (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).lift (kernelSubobject ((E.page r hr).dFrom pq)) := by
  rw [cyclesSubobject, pagePresentation_add_one]
  rfl

lemma boundariesSubobject_add_one (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).lift (imageSubobject ((E.page r hr).dTo pq)) := by
  rw [boundariesSubobject, pagePresentation_add_one]
  rfl

lemma boundariesSubobject_le_cyclesSubobject (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r hr ≤ E.cyclesSubobject pq r hr :=
  (E.pagePresentation pq r hr).le

lemma boundariesSubobject_le_add_one (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r hr ≤ E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) := by
  rw [boundariesSubobject_add_one]
  exact (E.pagePresentation pq r hr).lower_le_lift _

lemma cyclesSubobject_add_one_le (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) ≤ E.cyclesSubobject pq r hr := by
  rw [cyclesSubobject_add_one]
  exact (E.pagePresentation pq r hr).lift_le_upper _

/-- The boundary tower `r ↦ B_r(pq)` is increasing. -/
lemma boundariesSubobject_mono (pq : κ) {r r' : ℤ} (hr : r₀ ≤ r) (hrr' : r ≤ r') :
    E.boundariesSubobject pq r hr ≤ E.boundariesSubobject pq r' (hr.trans hrr') := by
  induction r', hrr' using Int.leInduction with
  | base => exact le_rfl
  | succ s hrs ih => exact ih.trans (E.boundariesSubobject_le_add_one pq s (hr.trans hrs))

/-- The cycle tower `r ↦ Z_r(pq)` is decreasing. -/
lemma cyclesSubobject_anti (pq : κ) {r r' : ℤ} (hr : r₀ ≤ r) (hrr' : r ≤ r') :
    E.cyclesSubobject pq r' (hr.trans hrr') ≤ E.cyclesSubobject pq r hr := by
  induction r', hrr' using Int.leInduction with
  | base => exact le_rfl
  | succ s hrs ih => exact (E.cyclesSubobject_add_one_le pq s (hr.trans hrs)).trans ih

/-- Every boundary subobject lies below every cycle subobject, regardless of page indices. -/
lemma boundariesSubobject_le_cyclesSubobject_of_pages (pq : κ) (r r' : ℤ)
    (hr : r₀ ≤ r) (hr' : r₀ ≤ r') :
    E.boundariesSubobject pq r hr ≤ E.cyclesSubobject pq r' hr' :=
  (E.boundariesSubobject_mono pq hr (le_max_left r r')).trans <|
    (E.boundariesSubobject_le_cyclesSubobject pq (max r r') (hr.trans (le_max_left r r'))).trans
      (E.cyclesSubobject_anti pq hr' (le_max_right r r'))

/-- The cycle tower stays constant from page `r` to page `r + 1` if and only if the differential
leaving `pq` on page `r` vanishes. -/
lemma cyclesSubobject_add_one_eq_iff (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) = E.cyclesSubobject pq r hr ↔
      (E.page r hr).dFrom pq = 0 := by
  rw [E.cyclesSubobject_add_one pq r hr, ← E.pagePresentation_upper pq r hr,
    ← (E.pagePresentation pq r hr).lift_top,
    (E.pagePresentation pq r hr).lift_injective.eq_iff, kernelSubobject_eq_top_iff]

/-- The boundary tower stays constant from page `r` to page `r + 1` if and only if the differential
entering `pq` on page `r` vanishes. -/
lemma boundariesSubobject_add_one_eq_iff (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) = E.boundariesSubobject pq r hr ↔
      (E.page r hr).dTo pq = 0 := by
  rw [E.boundariesSubobject_add_one pq r hr, ← E.pagePresentation_lower pq r hr,
    ← (E.pagePresentation pq r hr).lift_bot,
    (E.pagePresentation pq r hr).lift_injective.eq_iff, imageSubobject_eq_bot_iff]

/-- The outgoing differential `dFrom pq` vanishes if and only if every differential `d pq pq'`
leaving `pq` vanishes. -/
lemma dFrom_eq_zero_iff (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (E.page r hr).dFrom pq = 0 ↔ ∀ pq', (E.page r hr).d pq pq' = 0 := by
  constructor
  · intro h pq'
    by_cases hrel : (c r).Rel pq pq'
    · rw [← (c r).next_eq' hrel]
      exact h
    · exact (E.page r hr).shape pq pq' hrel
  · intro h
    exact h ((c r).next pq)

/-- The incoming differential `dTo pq` vanishes if and only if every differential `d pq' pq`
entering `pq` vanishes. -/
lemma dTo_eq_zero_iff (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (E.page r hr).dTo pq = 0 ↔ ∀ pq', (E.page r hr).d pq' pq = 0 := by
  constructor
  · intro h pq'
    by_cases hrel : (c r).Rel pq' pq
    · rw [← (c r).prev_eq' hrel]
      exact h
    · exact (E.page r hr).shape pq' pq hrel
  · intro h
    exact h ((c r).prev pq)

/-- The object at `pq` on page `r` is zero if and only if `B_r(pq) = Z_r(pq)`. -/
lemma isZero_page_X_iff (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    IsZero ((E.page r hr).X pq) ↔ E.boundariesSubobject pq r hr = E.cyclesSubobject pq r hr :=
  (E.pagePresentation pq r hr).isZero_iff

/-- If every differential leaving `pq` on pages `r₀ ≤ s < r` vanishes, then `Z_r(pq) = ⊤`. -/
lemma cyclesSubobject_eq_top_of_dFrom_eq_zero (pq : κ) (r : ℤ) (hr : r₀ ≤ r)
    (h : ∀ s (hs : r₀ ≤ s), s < r → (E.page s hs).dFrom pq = 0) :
    E.cyclesSubobject pq r hr = ⊤ := by
  induction r, hr using Int.leInduction with
  | base => exact E.cyclesSubobject_self pq
  | succ s hs ih =>
    rw [(E.cyclesSubobject_add_one_eq_iff pq s hs).2 (h s hs (Int.lt_add_one_iff.2 le_rfl))]
    exact ih (fun t ht hts ↦ h t ht (hts.trans (Int.lt_add_one_iff.2 le_rfl)))

/-- If every differential entering `pq` on pages `r₀ ≤ s < r` vanishes, then `B_r(pq) = ⊥`. -/
lemma boundariesSubobject_eq_bot_of_dTo_eq_zero (pq : κ) (r : ℤ) (hr : r₀ ≤ r)
    (h : ∀ s (hs : r₀ ≤ s), s < r → (E.page s hs).dTo pq = 0) :
    E.boundariesSubobject pq r hr = ⊥ := by
  induction r, hr using Int.leInduction with
  | base => exact E.boundariesSubobject_self pq
  | succ s hs ih =>
    rw [(E.boundariesSubobject_add_one_eq_iff pq s hs).2 (h s hs (Int.lt_add_one_iff.2 le_rfl))]
    exact ih (fun t ht hts ↦ h t ht (hts.trans (Int.lt_add_one_iff.2 le_rfl)))

end Towers

section Naturality

variable {E E' : SpectralSequence C c r₀}

private lemma pagePresentation_naturality_aux (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    ∃ (hZ : (E.pagePresentation pq r hr).upper ≤
        (Subobject.pullback ((f.hom r₀ le_rfl).f pq)).obj (E'.pagePresentation pq r hr).upper)
      (hB : (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj (E.pagePresentation pq r hr).lower ≤
        (E'.pagePresentation pq r hr).lower),
      (E.pagePresentation pq r hr).map (E'.pagePresentation pq r hr)
        ((f.hom r₀ le_rfl).f pq) hZ hB = (f.hom r hr).f pq := by
  induction r, hr using Int.leInduction with
  | base =>
    rw [pagePresentation_self, pagePresentation_self]
    refine ⟨?_, ((Subobject.existsPullbackAdj _).gc _ _).2 bot_le,
      SubquotientPresentation.map_refl _ _ _⟩
    dsimp
    rw [Subobject.pullback_top]
  | succ s hs ih =>
    rcases ih with ⟨hZ, hB, hmap⟩
    let φ : (E.page s hs).sc pq ⟶ (E'.page s hs).sc pq :=
      (HomologicalComplex.shortComplexFunctor C (c s) pq).map (f.hom s hs)
    have hτ₂ : (E.pagePresentation pq s hs).map (E'.pagePresentation pq s hs)
        ((f.hom r₀ le_rfl).f pq) hZ hB = φ.τ₂ := hmap
    have hqZ : (SubquotientPresentation.ofShortComplex ((E.page s hs).sc pq)).upper ≤
        (Subobject.pullback ((E.pagePresentation pq s hs).map (E'.pagePresentation pq s hs)
          ((f.hom r₀ le_rfl).f pq) hZ hB)).obj
          (SubquotientPresentation.ofShortComplex ((E'.page s hs).sc pq)).upper := by
      rw [hτ₂]
      exact SubquotientPresentation.ofShortComplex_upper_le_pullback φ
    have hqB : (Subobject.exists ((E.pagePresentation pq s hs).map (E'.pagePresentation pq s hs)
        ((f.hom r₀ le_rfl).f pq) hZ hB)).obj
        (SubquotientPresentation.ofShortComplex ((E.page s hs).sc pq)).lower ≤
        (SubquotientPresentation.ofShortComplex ((E'.page s hs).sc pq)).lower := by
      rw [hτ₂]
      exact SubquotientPresentation.exists_ofShortComplex_lower_le φ
    have hZ' : (E.pagePresentation pq (s + 1) (Int.le_add_one hs)).upper ≤
        (Subobject.pullback ((f.hom r₀ le_rfl).f pq)).obj
          (E'.pagePresentation pq (s + 1) (Int.le_add_one hs)).upper := by
      rw [pagePresentation_add_one, pagePresentation_add_one]
      exact (E.pagePresentation pq s hs).lift_le_pullback_lift (E'.pagePresentation pq s hs)
        ((f.hom r₀ le_rfl).f pq) hZ hB hqZ
    have hB' : (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj
        (E.pagePresentation pq (s + 1) (Int.le_add_one hs)).lower ≤
        (E'.pagePresentation pq (s + 1) (Int.le_add_one hs)).lower := by
      rw [pagePresentation_add_one, pagePresentation_add_one]
      exact (E.pagePresentation pq s hs).exists_lift_le_lift (E'.pagePresentation pq s hs)
        ((f.hom r₀ le_rfl).f pq) hZ hB hqB
    refine ⟨hZ', hB', ?_⟩
    have hqmap : (SubquotientPresentation.ofShortComplex ((E.page s hs).sc pq)).map
        (SubquotientPresentation.ofShortComplex ((E'.page s hs).sc pq))
        ((E.pagePresentation pq s hs).map (E'.pagePresentation pq s hs)
          ((f.hom r₀ le_rfl).f pq) hZ hB) hqZ hqB =
        HomologicalComplex.homologyMap (f.hom s hs) pq := by
      generalize hg : (E.pagePresentation pq s hs).map (E'.pagePresentation pq s hs)
        ((f.hom r₀ le_rfl).f pq) hZ hB = g at hτ₂ hqZ hqB
      subst hτ₂
      exact SubquotientPresentation.map_ofShortComplex φ
    have hstep : ((E.pagePresentation pq s hs).comp
          (SubquotientPresentation.ofShortComplex ((E.page s hs).sc pq))).transIso
            (E.iso s (s + 1) pq rfl hs) =
          E.pagePresentation pq (s + 1) (Int.le_add_one hs) :=
      (E.pagePresentation_add_one pq s hs).symm
    have hstep' : ((E'.pagePresentation pq s hs).comp
          (SubquotientPresentation.ofShortComplex ((E'.page s hs).sc pq))).transIso
            (E'.iso s (s + 1) pq rfl hs) =
          E'.pagePresentation pq (s + 1) (Int.le_add_one hs) :=
      (E'.pagePresentation_add_one pq s hs).symm
    revert hZ' hB'
    rw [← hstep, ← hstep']
    intro hZ' hB'
    rw [SubquotientPresentation.map_transIso,
      SubquotientPresentation.map_comp_presentation _ _ _ _ _ _ _ hqZ hqB, hqmap,
      f.comm s (s + 1) pq rfl hs, Iso.inv_hom_id_assoc]

/-- Naturality of the cycle tower: a morphism `f : E ⟶ E'` sends `Z_r(E, pq)` into
`Z_r(E', pq)` along its first-page component. -/
lemma cyclesSubobject_le_pullback (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq r hr ≤
      (Subobject.pullback ((f.hom r₀ le_rfl).f pq)).obj (E'.cyclesSubobject pq r hr) :=
  (pagePresentation_naturality_aux f pq r hr).choose

/-- Naturality of the boundary tower: a morphism `f : E ⟶ E'` maps `B_r(E, pq)` into
`B_r(E', pq)` along its first-page component. -/
lemma exists_boundariesSubobject_le (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj (E.boundariesSubobject pq r hr) ≤
      E'.boundariesSubobject pq r hr :=
  (pagePresentation_naturality_aux f pq r hr).choose_spec.choose

/-- The morphism induced on page-`r` subquotient presentations by the first-page component of
`f : E ⟶ E'` is the page-`r` component `(f.hom r hr).f pq`. -/
lemma pagePresentation_map (f : E ⟶ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (E.pagePresentation pq r hr).map (E'.pagePresentation pq r hr)
      ((f.hom r₀ le_rfl).f pq)
      (cyclesSubobject_le_pullback f pq r hr)
      (exists_boundariesSubobject_le f pq r hr) = (f.hom r hr).f pq :=
  (pagePresentation_naturality_aux f pq r hr).choose_spec.choose_spec

/-- The isomorphism between page-`r` objects induced by an isomorphism of spectral sequences. -/
@[expose, simps!]
def pageXIsoOfIso (e : E ≅ E') (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (E.page r hr).X pq ≅ (E'.page r hr).X pq :=
  (pageFunctor C c r₀ r hr ⋙ HomologicalComplex.eval C (c r) pq).mapIso e

/-- An isomorphism of spectral sequences identifies their cycle towers via the first-page
isomorphism. -/
lemma map_cyclesSubobject_of_iso (e : E ≅ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.map (pageXIsoOfIso e r₀ le_rfl pq).hom).obj (E.cyclesSubobject pq r hr) =
      E'.cyclesSubobject pq r hr := by
  let e₀ := pageXIsoOfIso e r₀ le_rfl pq
  refine le_antisymm ?_ ?_
  · exact (Subobject.mapPullbackAdj e₀.hom).gc _ _ |>.2 (cyclesSubobject_le_pullback e.hom pq r hr)
  · have hinv : (Subobject.map e₀.inv).obj (E'.cyclesSubobject pq r hr) ≤
        E.cyclesSubobject pq r hr :=
      (Subobject.mapPullbackAdj e₀.inv).gc _ _ |>.2 (cyclesSubobject_le_pullback e.inv pq r hr)
    simpa only [← Subobject.map_comp, e₀.inv_hom_id, Subobject.map_id] using
      (Subobject.map e₀.hom).monotone hinv

/-- An isomorphism of spectral sequences identifies their boundary towers via the first-page
isomorphism. -/
lemma map_boundariesSubobject_of_iso (e : E ≅ E') (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.map (pageXIsoOfIso e r₀ le_rfl pq).hom).obj (E.boundariesSubobject pq r hr) =
      E'.boundariesSubobject pq r hr := by
  let e₀ := pageXIsoOfIso e r₀ le_rfl pq
  refine le_antisymm ?_ ?_
  · rw [← Subobject.exists_iso_map]
    exact exists_boundariesSubobject_le e.hom pq r hr
  · have hinv : (Subobject.map e₀.inv).obj (E'.boundariesSubobject pq r hr) ≤
        E.boundariesSubobject pq r hr := by
      rw [← Subobject.exists_iso_map]
      exact exists_boundariesSubobject_le e.inv pq r hr
    simpa only [← Subobject.map_comp, e₀.inv_hom_id, Subobject.map_id] using
      (Subobject.map e₀.hom).monotone hinv

end Naturality

section Rebasing

variable (E : SpectralSequence C c r₀)

/-- Rebasing compatibility: composing the presentation of page `s` inside page `r₀` with the
presentation of page `r` inside page `s` yields the presentation of page `r` inside page `r₀`. -/
lemma pagePresentation_comp_fromPage (pq : κ) (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hr : s ≤ r) :
    (E.pagePresentation pq s hs).comp ((E.fromPage s hs).pagePresentation pq r hr) =
      E.pagePresentation pq r (hs.trans hr) := by
  induction r, hr using Int.leInduction with
  | base =>
    rw [pagePresentation_self, SubquotientPresentation.comp_refl]
  | succ t ht ih =>
    rw [(E.fromPage s hs).pagePresentation_add_one pq t ht,
      E.pagePresentation_add_one pq t (hs.trans ht),
      SubquotientPresentation.comp_transIso, ← SubquotientPresentation.comp_assoc, ih]

/-- Under the presentation of page `s`, the cycle tower built from page `s` lifts to the cycle
tower of `E`. -/
lemma lift_fromPage_cyclesSubobject (pq : κ) (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hr : s ≤ r) :
    (E.pagePresentation pq s hs).lift ((E.fromPage s hs).cyclesSubobject pq r hr) =
      E.cyclesSubobject pq r (hs.trans hr) :=
  congrArg SubquotientPresentation.upper (E.pagePresentation_comp_fromPage pq s hs r hr)

/-- Under the presentation of page `s`, the boundary tower built from page `s` lifts to the
boundary tower of `E`. -/
lemma lift_fromPage_boundariesSubobject (pq : κ) (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hr : s ≤ r) :
    (E.pagePresentation pq s hs).lift ((E.fromPage s hs).boundariesSubobject pq r hr) =
      E.boundariesSubobject pq r (hs.trans hr) :=
  congrArg SubquotientPresentation.lower (E.pagePresentation_comp_fromPage pq s hs r hr)

/-- Under the presentation of page `s`, descending `Z_r(pq)` recovers the rebased cycle subobject
of `E.fromPage s hs`. -/
lemma desc_cyclesSubobject_eq_fromPage (pq : κ) (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hr : s ≤ r) :
    (E.pagePresentation pq s hs).desc (E.cyclesSubobject pq r (hs.trans hr)) =
      (E.fromPage s hs).cyclesSubobject pq r hr := by
  rw [← E.lift_fromPage_cyclesSubobject pq s hs r hr, SubquotientPresentation.desc_lift]

/-- Under the presentation of page `s`, descending `B_r(pq)` recovers the rebased boundary
subobject of `E.fromPage s hs`. -/
lemma desc_boundariesSubobject_eq_fromPage (pq : κ) (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hr : s ≤ r) :
    (E.pagePresentation pq s hs).desc (E.boundariesSubobject pq r (hs.trans hr)) =
      (E.fromPage s hs).boundariesSubobject pq r hr := by
  rw [← E.lift_fromPage_boundariesSubobject pq s hs r hr, SubquotientPresentation.desc_lift]

end Rebasing

end CategoryTheory.SpectralSequence
