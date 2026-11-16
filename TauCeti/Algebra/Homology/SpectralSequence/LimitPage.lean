/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import TauCeti.Algebra.Homology.SpectralSequence.Stabilization

/-!
# Infinite cycles, infinite boundaries, and the limit page of a spectral sequence

At each position `pq : κ` of a spectral sequence `E : SpectralSequence C c r₀` in an abelian
category `C`, the cycle and boundary towers inside `(E.page r₀ le_rfl).X pq` form a decreasing
family `E.cyclesSet pq` and an increasing family `E.boundariesSet pq`. Without requiring
`[WellPowered C]`, this file introduces entrywise existence hypotheses:

* `CategoryTheory.SpectralSequence.HasInfiniteCyclesAt E pq`: `E.cyclesSet pq` admits a greatest
  lower bound `E.infiniteCycles pq` (`Z_∞^{pq}`).
* `CategoryTheory.SpectralSequence.HasInfiniteBoundariesAt E pq`: `E.boundariesSet pq` admits a
  least upper bound `E.infiniteBoundaries pq` (`B_∞^{pq}`).
* `CategoryTheory.SpectralSequence.HasLimitPageAt E pq`: both bounds exist, in which case
  `E.infiniteBoundaries pq ≤ E.infiniteCycles pq` and
  `E.limitPage pq := cokernel (Subobject.ofLE (E.infiniteBoundaries pq) (E.infiniteCycles pq) _)`
  defines the limit page object `E_∞^{pq}`.

We establish:
* existence and canonical isomorphism `StabilizesAt.limitPageIso : E.limitPage pq ≅ (E.page s).X pq`
  whenever `E.StabilizesAt pq s`, independent of `s` (`StabilizesAt.limitPageIso_trans_pageXIso`);
* automatic instances under `[HasCountableProducts C]` and `[HasCountableCoproducts C]`;
* functoriality `limitPageMap`, compatibility with identities, composition, isomorphisms, and
  `StabilizesAt.limitPageIso`;
* rebasing at any page `s ≥ r₀` (`exists_isGLB_cyclesSetFrom_iff`,
  `exists_isLUB_boundariesSetFrom_iff`, `exists_limitPageRebaseIso`);
* vanishing propagation `isZero_limitPage_of_isZero_page_X`.

## References

* G. Helle and J. Rognes, *Boardman's theorem on strong convergence of spectral sequences*,
  Lemma 2.2 and Definition 2.3.
* The Stacks Project Authors, *The Stacks Project*, Tags 011N and 0BDV.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SpectralSequence

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-! ### Sets of cycle and boundary subobjects -/

/-- The set of cycle subobjects `{Z_{s, r}^{pq} | r ≥ s}` inside `(E.page s hs).X pq`. -/
noncomputable def cyclesSetFrom (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ) (hs : r₀ ≤ s) :
    Set (Subobject ((E.page s hs).X pq)) :=
  Set.range fun r : Set.Ici s ↦ E.cyclesSubobjectFrom pq s hs r.1 r.2

/-- The set of boundary subobjects `{B_{s, r}^{pq} | r ≥ s}` inside `(E.page s hs).X pq`. -/
noncomputable def boundariesSetFrom (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ) (hs : r₀ ≤ s) :
    Set (Subobject ((E.page s hs).X pq)) :=
  Set.range fun r : Set.Ici s ↦ E.boundariesSubobjectFrom pq s hs r.1 r.2

/-- The set of cycle subobjects `{Z_r^{pq} | r ≥ r₀}` inside `(E.page r₀ le_rfl).X pq`. -/
noncomputable abbrev cyclesSet (E : SpectralSequence C c r₀) (pq : κ) :
    Set (Subobject ((E.page r₀ le_rfl).X pq)) :=
  E.cyclesSetFrom pq r₀ le_rfl

/-- The set of boundary subobjects `{B_r^{pq} | r ≥ r₀}` inside `(E.page r₀ le_rfl).X pq`. -/
noncomputable abbrev boundariesSet (E : SpectralSequence C c r₀) (pq : κ) :
    Set (Subobject ((E.page r₀ le_rfl).X pq)) :=
  E.boundariesSetFrom pq r₀ le_rfl

lemma cyclesSetFrom_nonempty (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ) (hs : r₀ ≤ s) :
    (E.cyclesSetFrom pq s hs).Nonempty :=
  ⟨E.cyclesSubobjectFrom pq s hs s le_rfl, ⟨⟨s, Set.mem_Ici.mpr le_rfl⟩, rfl⟩⟩

lemma boundariesSetFrom_nonempty (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ) (hs : r₀ ≤ s) :
    (E.boundariesSetFrom pq s hs).Nonempty :=
  ⟨E.boundariesSubobjectFrom pq s hs s le_rfl, ⟨⟨s, Set.mem_Ici.mpr le_rfl⟩, rfl⟩⟩

/-! ### Entrywise existence hypotheses and definitions of `Z_∞`, `B_∞`, and `E_∞` -/

/-- Entrywise hypothesis that the cycle tower at `pq` admits a greatest lower bound `Z_∞^{pq}` in
`Subobject ((E.page r₀ le_rfl).X pq)`. -/
class HasInfiniteCyclesAt (E : SpectralSequence C c r₀) (pq : κ) : Prop where
  exists_isGLB : ∃ Z, IsGLB (E.cyclesSet pq) Z

/-- Entrywise hypothesis that the boundary tower at `pq` admits a least upper bound `B_∞^{pq}` in
`Subobject ((E.page r₀ le_rfl).X pq)`. -/
class HasInfiniteBoundariesAt (E : SpectralSequence C c r₀) (pq : κ) : Prop where
  exists_isLUB : ∃ B, IsLUB (E.boundariesSet pq) B

/-- Entrywise hypothesis that both `Z_∞^{pq}` and `B_∞^{pq}` exist at `pq`, so the limit page object
`E_∞^{pq}` is defined. -/
class HasLimitPageAt (E : SpectralSequence C c r₀) (pq : κ) : Prop extends
  E.HasInfiniteCyclesAt pq, E.HasInfiniteBoundariesAt pq

/-- The subobject `Z_∞^{pq} = ⨅_{r ≥ r₀} Z_r^{pq}` of infinite cycles at `pq`. -/
noncomputable def infiniteCycles (E : SpectralSequence C c r₀) (pq : κ)
    [E.HasInfiniteCyclesAt pq] : Subobject ((E.page r₀ le_rfl).X pq) :=
  (HasInfiniteCyclesAt.exists_isGLB (E := E) (pq := pq)).choose

/-- The subobject `B_∞^{pq} = ⨆_{r ≥ r₀} B_r^{pq}` of infinite boundaries at `pq`. -/
noncomputable def infiniteBoundaries (E : SpectralSequence C c r₀) (pq : κ)
    [E.HasInfiniteBoundariesAt pq] : Subobject ((E.page r₀ le_rfl).X pq) :=
  (HasInfiniteBoundariesAt.exists_isLUB (E := E) (pq := pq)).choose

lemma isGLB_infiniteCycles (E : SpectralSequence C c r₀) (pq : κ) [E.HasInfiniteCyclesAt pq] :
    IsGLB (E.cyclesSet pq) (E.infiniteCycles pq) :=
  (HasInfiniteCyclesAt.exists_isGLB (E := E) (pq := pq)).choose_spec

lemma isLUB_infiniteBoundaries (E : SpectralSequence C c r₀) (pq : κ)
    [E.HasInfiniteBoundariesAt pq] :
    IsLUB (E.boundariesSet pq) (E.infiniteBoundaries pq) :=
  (HasInfiniteBoundariesAt.exists_isLUB (E := E) (pq := pq)).choose_spec

lemma infiniteCycles_le (E : SpectralSequence C c r₀) (pq : κ) [E.HasInfiniteCyclesAt pq]
    (r : ℤ) (hr : r₀ ≤ r) :
    E.infiniteCycles pq ≤ E.cyclesSubobject pq r hr :=
  (E.isGLB_infiniteCycles pq).1 ⟨⟨r, hr⟩, rfl⟩

lemma le_infiniteCycles_iff (E : SpectralSequence C c r₀) (pq : κ) [E.HasInfiniteCyclesAt pq]
    {S : Subobject ((E.page r₀ le_rfl).X pq)} :
    S ≤ E.infiniteCycles pq ↔ ∀ r (hr : r₀ ≤ r), S ≤ E.cyclesSubobject pq r hr := by
  rw [isGLB_iff_le_iff.mp (E.isGLB_infiniteCycles pq) S, mem_lowerBounds]
  refine ⟨fun h r hr ↦ h _ ⟨⟨r, hr⟩, rfl⟩, ?_⟩
  rintro h _ ⟨⟨r, hr⟩, rfl⟩
  exact h r hr

lemma le_infiniteBoundaries (E : SpectralSequence C c r₀) (pq : κ) [E.HasInfiniteBoundariesAt pq]
    (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r hr ≤ E.infiniteBoundaries pq :=
  (E.isLUB_infiniteBoundaries pq).1 ⟨⟨r, hr⟩, rfl⟩

lemma infiniteBoundaries_le_iff (E : SpectralSequence C c r₀) (pq : κ)
    [E.HasInfiniteBoundariesAt pq] {S : Subobject ((E.page r₀ le_rfl).X pq)} :
    E.infiniteBoundaries pq ≤ S ↔ ∀ r (hr : r₀ ≤ r), E.boundariesSubobject pq r hr ≤ S := by
  rw [isLUB_iff_le_iff.mp (E.isLUB_infiniteBoundaries pq) S, mem_upperBounds]
  refine ⟨fun h r hr ↦ h _ ⟨⟨r, hr⟩, rfl⟩, ?_⟩
  rintro h _ ⟨⟨r, hr⟩, rfl⟩
  exact h r hr

lemma boundariesSubobject_le_infiniteCycles (E : SpectralSequence C c r₀) (pq : κ)
    [E.HasInfiniteCyclesAt pq] (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r hr ≤ E.infiniteCycles pq :=
  (E.le_infiniteCycles_iff pq).mpr fun _ hr' ↦
    E.boundariesSubobject_le_cyclesSubobject_of_all pq hr hr'

lemma infiniteBoundaries_le_cyclesSubobject (E : SpectralSequence C c r₀) (pq : κ)
    [E.HasInfiniteBoundariesAt pq] (r : ℤ) (hr : r₀ ≤ r) :
    E.infiniteBoundaries pq ≤ E.cyclesSubobject pq r hr :=
  (E.infiniteBoundaries_le_iff pq).mpr fun _ hr' ↦
    E.boundariesSubobject_le_cyclesSubobject_of_all pq hr' hr

lemma infiniteBoundaries_le_infiniteCycles (E : SpectralSequence C c r₀) (pq : κ)
    [E.HasLimitPageAt pq] :
    E.infiniteBoundaries pq ≤ E.infiniteCycles pq :=
  (E.infiniteBoundaries_le_iff pq).mpr (E.boundariesSubobject_le_infiniteCycles pq)

/-- The limit page object `E_∞^{pq} = Z_∞^{pq} / B_∞^{pq}` of a spectral sequence at `pq`. -/
noncomputable def limitPage (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] : C :=
  cokernel (Subobject.ofLE (E.infiniteBoundaries pq) (E.infiniteCycles pq)
    (E.infiniteBoundaries_le_infiniteCycles pq))

/-- The canonical subquotient presentation `(B_∞^{pq}, Z_∞^{pq}, _)` of `E.limitPage pq` inside
`(E.page r₀ le_rfl).X pq`. -/
noncomputable def limitPagePresentation (E : SpectralSequence C c r₀) (pq : κ)
    [E.HasLimitPageAt pq] :
    TauCeti.SubquotientPresentation ((E.page r₀ le_rfl).X pq) (E.limitPage pq) :=
  TauCeti.SubquotientPresentation.ofLE (E.infiniteBoundaries_le_infiniteCycles pq)

@[simp]
lemma limitPagePresentation_B (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] :
    (E.limitPagePresentation pq).B = E.infiniteBoundaries pq := by
  dsimp only [limitPagePresentation, limitPage]
  exact TauCeti.SubquotientPresentation.ofLE_B _

@[simp]
lemma limitPagePresentation_Z (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] :
    (E.limitPagePresentation pq).Z = E.infiniteCycles pq := by
  dsimp only [limitPagePresentation, limitPage]
  exact TauCeti.SubquotientPresentation.ofLE_Z _

/-! ### General existence from countable products and coproducts -/

private lemma countable_Ici (a : ℤ) : Countable (Set.Ici a) :=
  Function.Injective.countable (f := fun r : Set.Ici a ↦ (r.1 - a).toNat) fun x y h ↦
    Subtype.ext (by have hx : a ≤ x.1 := x.2; have hy : a ≤ y.1 := y.2; lia)

/-- In an abelian category with countable products, infinite cycles exist at every position of every
spectral sequence. -/
instance instHasInfiniteCyclesAt [HasCountableProducts C] (E : SpectralSequence C c r₀) (pq : κ) :
    E.HasInfiniteCyclesAt pq := by
  have := countable_Ici r₀
  exact ⟨_, Subobject.isGLB_range_kernelSubobject_piLift
    (fun r : Set.Ici r₀ ↦ E.cyclesSubobject pq r.1 r.2)⟩

/-- In an abelian category with countable coproducts, infinite boundaries exist at every position of
every spectral sequence. -/
instance instHasInfiniteBoundariesAt [HasCountableCoproducts C] (E : SpectralSequence C c r₀)
    (pq : κ) : E.HasInfiniteBoundariesAt pq := by
  have := countable_Ici r₀
  exact ⟨_, Subobject.isLUB_range_imageSubobject_sigmaDesc
    (fun r : Set.Ici r₀ ↦ E.boundariesSubobject pq r.1 r.2)⟩

/-- In an abelian category with countable products and countable coproducts, the limit page exists
at every position of every spectral sequence. -/
instance instHasLimitPageAt [HasCountableProducts C] [HasCountableCoproducts C]
    (E : SpectralSequence C c r₀) (pq : κ) : E.HasLimitPageAt pq where

/-! ### Existence and canonical isomorphism in the stabilised case -/

/-- When `E` stabilises at `pq` from page `s`, `E.cyclesSubobject pq s h.le` is the greatest lower
bound of `E.cyclesSet pq`. -/
lemma StabilizesAt.isGLB_cyclesSubobject {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) :
    IsGLB (E.cyclesSet pq) (E.cyclesSubobject pq s h.le) := by
  refine ⟨?_, fun T hT ↦ hT ⟨⟨s, h.le⟩, rfl⟩⟩
  rintro _ ⟨⟨r, hr⟩, rfl⟩
  rcases le_total s r with hsr | hrs
  · exact (h.cyclesSubobject_eq r hsr).symm.le
  · exact E.cyclesSubobject_anti pq hr hrs

/-- When `E` stabilises at `pq` from page `s`, `E.boundariesSubobject pq s h.le` is the least upper
bound of `E.boundariesSet pq`. -/
lemma StabilizesAt.isLUB_boundariesSubobject {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) :
    IsLUB (E.boundariesSet pq) (E.boundariesSubobject pq s h.le) := by
  refine ⟨?_, fun T hT ↦ hT ⟨⟨s, h.le⟩, rfl⟩⟩
  rintro _ ⟨⟨r, hr⟩, rfl⟩
  rcases le_total s r with hsr | hrs
  · exact (h.boundariesSubobject_eq r hsr).le
  · exact E.boundariesSubobject_mono pq hr hrs

lemma StabilizesAt.hasInfiniteCyclesAt {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) : E.HasInfiniteCyclesAt pq :=
  ⟨_, h.isGLB_cyclesSubobject⟩

lemma StabilizesAt.hasInfiniteBoundariesAt {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) : E.HasInfiniteBoundariesAt pq :=
  ⟨_, h.isLUB_boundariesSubobject⟩

/-- Stabilisation at `pq` implies existence of the limit page at `pq` with no ambient completeness
or well-poweredness assumption. -/
lemma StabilizesAt.hasLimitPageAt {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) : E.HasLimitPageAt pq := by
  have := h.hasInfiniteCyclesAt
  have := h.hasInfiniteBoundariesAt
  exact ⟨⟩

lemma StabilizesAt.infiniteCycles_eq {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) [E.HasInfiniteCyclesAt pq] :
    E.infiniteCycles pq = E.cyclesSubobject pq s h.le :=
  (E.isGLB_infiniteCycles pq).unique h.isGLB_cyclesSubobject

lemma StabilizesAt.infiniteBoundaries_eq {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) [E.HasInfiniteBoundariesAt pq] :
    E.infiniteBoundaries pq = E.boundariesSubobject pq s h.le :=
  (E.isLUB_infiniteBoundaries pq).unique h.isLUB_boundariesSubobject

private lemma StabilizesAt.exists_id_infiniteBoundaries_le {E : SpectralSequence C c r₀}
    {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s) [E.HasLimitPageAt pq] :
    (Subobject.exists (𝟙 ((E.page r₀ le_rfl).X pq))).obj (E.limitPagePresentation pq).B ≤
      (E.pagePresentation pq s h.le).B := by
  rw [limitPagePresentation_B, h.infiniteBoundaries_eq]
  exact TauCeti.SubquotientPresentation.exists_id_le _

private lemma StabilizesAt.infiniteCycles_le_pullback_id {E : SpectralSequence C c r₀}
    {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s) [E.HasLimitPageAt pq] :
    (E.limitPagePresentation pq).Z ≤
      (Subobject.pullback (𝟙 ((E.page r₀ le_rfl).X pq))).obj (E.pagePresentation pq s h.le).Z := by
  rw [limitPagePresentation_Z, h.infiniteCycles_eq]
  exact TauCeti.SubquotientPresentation.le_pullback_id _

private lemma StabilizesAt.exists_id_boundariesSubobject_le {E : SpectralSequence C c r₀}
    {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s) [E.HasLimitPageAt pq] :
    (Subobject.exists (𝟙 ((E.page r₀ le_rfl).X pq))).obj (E.pagePresentation pq s h.le).B ≤
      (E.limitPagePresentation pq).B := by
  rw [limitPagePresentation_B, h.infiniteBoundaries_eq]
  exact TauCeti.SubquotientPresentation.exists_id_le _

private lemma StabilizesAt.cyclesSubobject_le_pullback_id {E : SpectralSequence C c r₀}
    {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s) [E.HasLimitPageAt pq] :
    (E.pagePresentation pq s h.le).Z ≤
      (Subobject.pullback (𝟙 ((E.page r₀ le_rfl).X pq))).obj (E.limitPagePresentation pq).Z := by
  rw [limitPagePresentation_Z, h.infiniteCycles_eq]
  exact TauCeti.SubquotientPresentation.le_pullback_id _

/-- When `E` stabilises at `pq` from page `s`, this is the canonical isomorphism
`E.limitPage pq ≅ (E.page s h.le).X pq` induced by `Z_∞^{pq} = Z_s^{pq}` and
`B_∞^{pq} = B_s^{pq}`. -/
noncomputable def StabilizesAt.limitPageIso {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) [E.HasLimitPageAt pq] :
    E.limitPage pq ≅ (E.page s h.le).X pq where
  hom := (E.limitPagePresentation pq).descMap (E.pagePresentation pq s h.le) (𝟙 _)
    h.exists_id_infiniteBoundaries_le h.infiniteCycles_le_pullback_id
  inv := (E.pagePresentation pq s h.le).descMap (E.limitPagePresentation pq) (𝟙 _)
    h.exists_id_boundariesSubobject_le h.cyclesSubobject_le_pullback_id
  hom_inv_id := by
    rw [TauCeti.SubquotientPresentation.descMap_comp]
    refine (E.limitPagePresentation pq).descMap_eq_of_π_comp _ _ _ _ ?_
    rw [Category.comp_id]
    have hmap : (E.limitPagePresentation pq).mapZ (E.limitPagePresentation pq) (𝟙 _ ≫ 𝟙 _)
        (TauCeti.SubquotientPresentation.le_pullback_comp h.infiniteCycles_le_pullback_id
          h.cyclesSubobject_le_pullback_id) = 𝟙 _ := by
      rw [← cancel_mono (E.limitPagePresentation pq).Z.arrow,
        TauCeti.SubquotientPresentation.mapZ_arrow, Category.comp_id, Category.comp_id,
        Category.id_comp]
    rw [hmap, Category.id_comp]
  inv_hom_id := by
    rw [TauCeti.SubquotientPresentation.descMap_comp]
    refine (E.pagePresentation pq s h.le).descMap_eq_of_π_comp _ _ _ _ ?_
    rw [Category.comp_id]
    have hmap : (E.pagePresentation pq s h.le).mapZ (E.pagePresentation pq s h.le) (𝟙 _ ≫ 𝟙 _)
        (TauCeti.SubquotientPresentation.le_pullback_comp h.cyclesSubobject_le_pullback_id
          h.infiniteCycles_le_pullback_id) = 𝟙 _ := by
      rw [← cancel_mono (E.pagePresentation pq s h.le).Z.arrow,
        TauCeti.SubquotientPresentation.mapZ_arrow, Category.comp_id, Category.comp_id,
        Category.id_comp]
    rw [hmap, Category.id_comp]

/-- Independence of the stabilisation page `s`: composing `h.limitPageIso` with `h.pageXIso s' hss'`
yields `(h.mono hss').limitPageIso`. -/
@[simp]
lemma StabilizesAt.limitPageIso_trans_pageXIso {E : SpectralSequence C c r₀} {pq : κ}
    {s s' : ℤ} (h : E.StabilizesAt pq s) (hss' : s ≤ s') [E.HasLimitPageAt pq] :
    h.limitPageIso ≪≫ h.pageXIso s' hss' = (h.mono hss').limitPageIso := by
  ext
  simp only [Iso.trans_hom, limitPageIso]
  have heq := h.pagePresentation_eq s' hss'
  have hB_tr : (Subobject.exists (𝟙 _)).obj
      ((E.limitPagePresentation pq).transIso (Iso.refl _)).B ≤
      ((E.pagePresentation pq s h.le).transIso (h.pageXIso s' hss')).B := by
    simpa using h.exists_id_infiniteBoundaries_le
  have hZ_tr : ((E.limitPagePresentation pq).transIso (Iso.refl _)).Z ≤
      (Subobject.pullback (𝟙 _)).obj
        ((E.pagePresentation pq s h.le).transIso (h.pageXIso s' hss')).Z := by
    simpa using h.infiniteCycles_le_pullback_id
  have htr := (E.limitPagePresentation pq).descMap_transIso (E.pagePresentation pq s h.le)
    (Iso.refl (E.limitPage pq)) (h.pageXIso s' hss') (𝟙 _)
    h.exists_id_infiniteBoundaries_le h.infiniteCycles_le_pullback_id hB_tr hZ_tr
  rw [Iso.refl_inv, Category.id_comp] at htr
  have hcongr : ∀ (P P' : TauCeti.SubquotientPresentation
      ((E.page r₀ le_rfl).X pq) (E.limitPage pq))
      (Q Q' : TauCeti.SubquotientPresentation
      ((E.page r₀ le_rfl).X pq) ((E.page s' (h.mono hss').le).X pq))
      (_ : P = P') (_ : Q = Q')
      (hB₁ : (Subobject.exists (𝟙 _)).obj P.B ≤ Q.B)
      (hZ₁ : P.Z ≤ (Subobject.pullback (𝟙 _)).obj Q.Z)
      (hB₂ : (Subobject.exists (𝟙 _)).obj P'.B ≤ Q'.B)
      (hZ₂ : P'.Z ≤ (Subobject.pullback (𝟙 _)).obj Q'.Z),
      P.descMap Q (𝟙 _) hB₁ hZ₁ = P'.descMap Q' (𝟙 _) hB₂ hZ₂ := by
    rintro P _ Q _ rfl rfl _ _ _ _
    rfl
  exact htr.symm.trans
    (hcongr _ _ _ _ (TauCeti.SubquotientPresentation.transIso_refl _) heq.symm _ _ _ _)

/-! ### Functoriality and isomorphism transport -/

/-- A morphism `f : E ⟶ E'` maps `E.infiniteBoundaries pq` into `E'.infiniteBoundaries pq` along
`(f.hom r₀ le_rfl).f pq`. -/
lemma exists_infiniteBoundaries_le {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    [E.HasInfiniteBoundariesAt pq] [E'.HasInfiniteBoundariesAt pq] :
    (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj (E.infiniteBoundaries pq) ≤
      E'.infiniteBoundaries pq := by
  refine (Subobject.isLUB_exists_image ((f.hom r₀ le_rfl).f pq)
    (E.isLUB_infiniteBoundaries pq)).2 ?_
  rintro _ ⟨_, ⟨⟨r, hr⟩, rfl⟩, rfl⟩
  exact (exists_boundariesSubobject_le f pq r hr).trans (E'.le_infiniteBoundaries pq r hr)

/-- A morphism `f : E ⟶ E'` maps `E.infiniteCycles pq` into `E'.infiniteCycles pq` along
`(f.hom r₀ le_rfl).f pq`. -/
lemma infiniteCycles_le_pullback {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    [E.HasInfiniteCyclesAt pq] [E'.HasInfiniteCyclesAt pq] :
    E.infiniteCycles pq ≤
      (Subobject.pullback ((f.hom r₀ le_rfl).f pq)).obj (E'.infiniteCycles pq) := by
  refine (Subobject.isGLB_pullback_image ((f.hom r₀ le_rfl).f pq)
    (E'.isGLB_infiniteCycles pq)).2 ?_
  rintro _ ⟨_, ⟨⟨r, hr⟩, rfl⟩, rfl⟩
  exact (E.infiniteCycles_le pq r hr).trans (cyclesSubobject_le_pullback f pq r hr)

private lemma exists_limitPagePresentation_B_le {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    (pq : κ) [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj (E.limitPagePresentation pq).B ≤
      (E'.limitPagePresentation pq).B := by
  rw [limitPagePresentation_B, limitPagePresentation_B]
  exact exists_infiniteBoundaries_le f pq

private lemma limitPagePresentation_Z_le_pullback {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    (pq : κ) [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    (E.limitPagePresentation pq).Z ≤
      (Subobject.pullback ((f.hom r₀ le_rfl).f pq)).obj (E'.limitPagePresentation pq).Z := by
  rw [limitPagePresentation_Z, limitPagePresentation_Z]
  exact infiniteCycles_le_pullback f pq

/-- The morphism `E.limitPage pq ⟶ E'.limitPage pq` induced by a morphism `f : E ⟶ E'` of spectral
sequences. -/
noncomputable def limitPageMap {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    E.limitPage pq ⟶ E'.limitPage pq :=
  (E.limitPagePresentation pq).descMap (E'.limitPagePresentation pq) ((f.hom r₀ le_rfl).f pq)
    (exists_limitPagePresentation_B_le f pq) (limitPagePresentation_Z_le_pullback f pq)

@[simp]
lemma limitPageMap_id (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq] :
    limitPageMap (𝟙 E) pq = 𝟙 (E.limitPage pq) := by
  refine (E.limitPagePresentation pq).descMap_eq_of_π_comp _ _ _ _ ?_
  rw [Category.comp_id]
  have hmap : (E.limitPagePresentation pq).mapZ (E.limitPagePresentation pq)
      (((𝟙 E : E ⟶ E).hom r₀ le_rfl).f pq)
      (limitPagePresentation_Z_le_pullback (𝟙 E) pq) = 𝟙 _ := by
    rw [← cancel_mono (E.limitPagePresentation pq).Z.arrow,
      TauCeti.SubquotientPresentation.mapZ_arrow, id_hom, HomologicalComplex.id_f,
      Category.comp_id, Category.id_comp]
  rw [hmap, Category.id_comp]

@[simp, reassoc]
lemma limitPageMap_comp {E E' E'' : SpectralSequence C c r₀} (f : E ⟶ E') (g : E' ⟶ E'')
    (pq : κ) [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] [E''.HasLimitPageAt pq] :
    limitPageMap (f ≫ g) pq = limitPageMap f pq ≫ limitPageMap g pq := by
  dsimp only [limitPageMap]
  rw [TauCeti.SubquotientPresentation.descMap_comp]
  refine (E.limitPagePresentation pq).descMap_eq_of_π_comp _ _ _ _ ?_
  rw [TauCeti.SubquotientPresentation.π_comp_descMap]
  congr 1

/-- An isomorphism `e : E ≅ E'` induces an isomorphism `E.limitPage pq ≅ E'.limitPage pq`. -/
noncomputable def limitPageIsoOfIso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    E.limitPage pq ≅ E'.limitPage pq where
  hom := limitPageMap e.hom pq
  inv := limitPageMap e.inv pq
  hom_inv_id := by rw [← limitPageMap_comp, e.hom_inv_id, limitPageMap_id]
  inv_hom_id := by rw [← limitPageMap_comp, e.inv_hom_id, limitPageMap_id]

@[simp]
lemma limitPageIsoOfIso_hom {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    (limitPageIsoOfIso e pq).hom = limitPageMap e.hom pq := by
  simp [limitPageIsoOfIso]

@[simp]
lemma limitPageIsoOfIso_inv {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    (limitPageIsoOfIso e pq).inv = limitPageMap e.inv pq := by
  simp [limitPageIsoOfIso]

private lemma mapIsoToOrderIso_eq_of_exists_le' {X Y : C} (e : X ≅ Y) {S : Subobject X}
    {T : Subobject Y} (h₁ : (Subobject.exists e.hom).obj S ≤ T)
    (h₂ : (Subobject.exists e.inv).obj T ≤ S) :
    Subobject.mapIsoToOrderIso e S = T := by
  refine le_antisymm ?_ ?_
  · rw [Subobject.mapIsoToOrderIso_apply, ← Subobject.exists_obj_eq_map_obj_of_mono]
    exact h₁
  · rw [← (Subobject.mapIsoToOrderIso e).symm_apply_le]
    have hsymm : (Subobject.mapIsoToOrderIso e).symm T = (Subobject.map e.inv).obj T := rfl
    rw [hsymm, ← Subobject.exists_obj_eq_map_obj_of_mono]
    exact h₂

/-- An isomorphism `e : E ≅ E'` transports `E.infiniteBoundaries pq` to
`E'.infiniteBoundaries pq`. -/
lemma mapIsoToOrderIso_infiniteBoundaries {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ)
    [E.HasInfiniteBoundariesAt pq] [E'.HasInfiniteBoundariesAt pq] :
    Subobject.mapIsoToOrderIso
      ((pageFunctor C c r₀ r₀ le_rfl ⋙ HomologicalComplex.eval C (c r₀) pq).mapIso e)
      (E.infiniteBoundaries pq) =
      E'.infiniteBoundaries pq :=
  mapIsoToOrderIso_eq_of_exists_le' _
    (exists_infiniteBoundaries_le e.hom pq)
    (exists_infiniteBoundaries_le e.inv pq)

/-- An isomorphism `e : E ≅ E'` transports `E.infiniteCycles pq` to `E'.infiniteCycles pq`. -/
lemma mapIsoToOrderIso_infiniteCycles {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ)
    [E.HasInfiniteCyclesAt pq] [E'.HasInfiniteCyclesAt pq] :
    Subobject.mapIsoToOrderIso
      ((pageFunctor C c r₀ r₀ le_rfl ⋙ HomologicalComplex.eval C (c r₀) pq).mapIso e)
      (E.infiniteCycles pq) =
      E'.infiniteCycles pq :=
  mapIsoToOrderIso_eq_of_exists_le' _
    (((Subobject.existsPullbackAdj ((e.hom.hom r₀ le_rfl).f pq)).gc _ _).mpr
      (infiniteCycles_le_pullback e.hom pq))
    (((Subobject.existsPullbackAdj ((e.inv.hom r₀ le_rfl).f pq)).gc _ _).mpr
      (infiniteCycles_le_pullback e.inv pq))

/-- Under the stabilisation isomorphisms `h.limitPageIso` and `h'.limitPageIso`, `limitPageMap f pq`
agrees with the page morphism `(f.hom s h.le).f pq`. -/
@[reassoc]
lemma StabilizesAt.limitPageMap_comp_limitPageIso_hom {E E' : SpectralSequence C c r₀}
    (f : E ⟶ E') {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s) (h' : E'.StabilizesAt pq s)
    [E.HasLimitPageAt pq] [E'.HasLimitPageAt pq] :
    limitPageMap f pq ≫ h'.limitPageIso.hom =
      h.limitPageIso.hom ≫ (f.hom s h.le).f pq := by
  dsimp only [limitPageMap, limitPageIso]
  rw [← descMap_pagePresentation f pq s h.le,
    TauCeti.SubquotientPresentation.descMap_comp,
    TauCeti.SubquotientPresentation.descMap_comp]
  refine (E.limitPagePresentation pq).descMap_eq_of_π_comp _ _ _ _ ?_
  rw [TauCeti.SubquotientPresentation.π_comp_descMap]
  congr 1
  rw [← cancel_mono (E'.pagePresentation pq s h'.le).Z.arrow,
    TauCeti.SubquotientPresentation.mapZ_arrow,
    TauCeti.SubquotientPresentation.mapZ_arrow, Category.comp_id, Category.id_comp]

/-! ### Rebasing at a later page `s ≥ r₀` -/

private lemma lowerBounds_preimage_cyclesSetFrom (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) :
    lowerBounds ((E.pagePresentation pq s hs).preimage '' E.cyclesSetFrom pq s hs) =
      lowerBounds (E.cyclesSet pq) := by
  ext T
  simp only [mem_lowerBounds, Set.mem_image, cyclesSet, cyclesSetFrom, Set.mem_range,
    Subtype.exists]
  constructor
  · rintro h _ ⟨r, hr, rfl⟩
    rcases le_total s r with hsr | hrs
    · have hsr' := h ((E.pagePresentation pq s hs).preimage
        (E.cyclesSubobjectFrom pq s hs r hsr)) ⟨_, ⟨r, hsr, rfl⟩, rfl⟩
      rwa [E.preimage_cyclesSubobjectFrom pq hs hsr] at hsr'
    · have hs₀ := h ((E.pagePresentation pq s hs).preimage
        (E.cyclesSubobjectFrom pq s hs s le_rfl)) ⟨_, ⟨s, Set.mem_Ici.mpr le_rfl, rfl⟩, rfl⟩
      rw [E.preimage_cyclesSubobjectFrom pq hs le_rfl] at hs₀
      exact hs₀.trans (E.cyclesSubobject_anti pq hr hrs)
  · rintro h _ ⟨_, ⟨r, hsr, rfl⟩, rfl⟩
    rw [E.preimage_cyclesSubobjectFrom pq hs hsr]
    exact h (E.cyclesSubobject pq r (hs.trans hsr)) ⟨r, hs.trans hsr, rfl⟩

private lemma upperBounds_preimage_boundariesSetFrom (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) :
    upperBounds ((E.pagePresentation pq s hs).preimage '' E.boundariesSetFrom pq s hs) =
      upperBounds (E.boundariesSet pq) := by
  ext T
  simp only [mem_upperBounds, Set.mem_image, boundariesSet, boundariesSetFrom, Set.mem_range,
    Subtype.exists]
  constructor
  · rintro h _ ⟨r, hr, rfl⟩
    rcases le_total s r with hsr | hrs
    · have hsr' := h ((E.pagePresentation pq s hs).preimage
        (E.boundariesSubobjectFrom pq s hs r hsr)) ⟨_, ⟨r, hsr, rfl⟩, rfl⟩
      rwa [E.preimage_boundariesSubobjectFrom pq hs hsr] at hsr'
    · have hs₀ := h ((E.pagePresentation pq s hs).preimage
        (E.boundariesSubobjectFrom pq s hs s le_rfl)) ⟨_, ⟨s, Set.mem_Ici.mpr le_rfl, rfl⟩, rfl⟩
      rw [E.preimage_boundariesSubobjectFrom pq hs le_rfl] at hs₀
      exact (E.boundariesSubobject_mono pq hr hrs).trans hs₀
  · rintro h _ ⟨_, ⟨r, hsr, rfl⟩, rfl⟩
    rw [E.preimage_boundariesSubobjectFrom pq hs hsr]
    exact h (E.boundariesSubobject pq r (hs.trans hsr)) ⟨r, hs.trans hsr, rfl⟩

/-- For any `s ≥ r₀` and `K : Subobject ((E.page s hs).X pq)`, `K` is the GLB of
`E.cyclesSetFrom pq s hs` if and only if its preimage in `E_{r₀}` is the GLB of `E.cyclesSet pq`. -/
lemma isGLB_cyclesSetFrom_iff (E : SpectralSequence C c r₀) (pq : κ)
    {s : ℤ} (hs : r₀ ≤ s) {K : Subobject ((E.page s hs).X pq)} :
    IsGLB (E.cyclesSetFrom pq s hs) K ↔
      IsGLB (E.cyclesSet pq) ((E.pagePresentation pq s hs).preimage K) := by
  rw [← (E.pagePresentation pq s hs).isGLB_preimage_image_iff (E.cyclesSetFrom_nonempty pq s hs),
    isGLB_iff_le_iff, isGLB_iff_le_iff, E.lowerBounds_preimage_cyclesSetFrom pq s hs]

/-- For any `s ≥ r₀` and `I : Subobject ((E.page s hs).X pq)`, `I` is the LUB of
`E.boundariesSetFrom pq s hs` if and only if its preimage in `E_{r₀}` is the LUB of
`E.boundariesSet pq`. -/
lemma isLUB_boundariesSetFrom_iff (E : SpectralSequence C c r₀) (pq : κ)
    {s : ℤ} (hs : r₀ ≤ s) {I : Subobject ((E.page s hs).X pq)} :
    IsLUB (E.boundariesSetFrom pq s hs) I ↔
      IsLUB (E.boundariesSet pq) ((E.pagePresentation pq s hs).preimage I) := by
  rw [← (E.pagePresentation pq s hs).isLUB_preimage_image_iff
      (E.boundariesSetFrom_nonempty pq s hs),
    isLUB_iff_le_iff, isLUB_iff_le_iff, E.upperBounds_preimage_boundariesSetFrom pq s hs]

/-- Existence of infinite cycles is unchanged by rebasing the tower at any later page `s ≥ r₀`. -/
lemma exists_isGLB_cyclesSetFrom_iff (E : SpectralSequence C c r₀) (pq : κ)
    {s : ℤ} (hs : r₀ ≤ s) :
    (∃ K, IsGLB (E.cyclesSetFrom pq s hs) K) ↔ E.HasInfiniteCyclesAt pq := by
  refine ⟨fun ⟨K, hK⟩ ↦ ⟨_, (E.isGLB_cyclesSetFrom_iff pq hs).mp hK⟩, fun h ↦ ?_⟩
  refine ⟨(E.pagePresentation pq s hs).imageOfLE (E.infiniteCycles pq)
    (E.infiniteCycles_le pq s hs), ?_⟩
  rw [E.isGLB_cyclesSetFrom_iff pq hs,
    (E.pagePresentation pq s hs).preimage_imageOfLE
      (E.boundariesSubobject_le_infiniteCycles pq s hs)]
  exact E.isGLB_infiniteCycles pq

/-- Existence of infinite boundaries is unchanged by rebasing the tower at any later page
`s ≥ r₀`. -/
lemma exists_isLUB_boundariesSetFrom_iff (E : SpectralSequence C c r₀) (pq : κ)
    {s : ℤ} (hs : r₀ ≤ s) :
    (∃ I, IsLUB (E.boundariesSetFrom pq s hs) I) ↔ E.HasInfiniteBoundariesAt pq := by
  refine ⟨fun ⟨I, hI⟩ ↦ ⟨_, (E.isLUB_boundariesSetFrom_iff pq hs).mp hI⟩, fun h ↦ ?_⟩
  refine ⟨(E.pagePresentation pq s hs).imageOfLE (E.infiniteBoundaries pq)
    (E.infiniteBoundaries_le_cyclesSubobject pq s hs), ?_⟩
  rw [E.isLUB_boundariesSetFrom_iff pq hs,
    (E.pagePresentation pq s hs).preimage_imageOfLE (E.le_infiniteBoundaries pq s hs)]
  exact E.isLUB_infiniteBoundaries pq

/-- **Rebasing the limit page at `s ≥ r₀`.** If `I` and `K` are the LUB and GLB of the boundary and
cycle towers inside `(E.page s hs).X pq`, then `I ≤ K` and `cokernel (Subobject.ofLE I K _)` is
canonically isomorphic to `E.limitPage pq`, compatibly with the subquotient presentations inside
`E_{r₀}`. -/
lemma exists_limitPageRebaseIso (E : SpectralSequence C c r₀) (pq : κ) [E.HasLimitPageAt pq]
    {s : ℤ} (hs : r₀ ≤ s) {I K : Subobject ((E.page s hs).X pq)}
    (hI : IsLUB (E.boundariesSetFrom pq s hs) I)
    (hK : IsGLB (E.cyclesSetFrom pq s hs) K) :
    ∃ (hIK : I ≤ K) (e : cokernel (Subobject.ofLE I K hIK) ≅ E.limitPage pq),
      ((E.pagePresentation pq s hs).ofSubobjects hIK).transIso e =
        E.limitPagePresentation pq := by
  have hpreI : (E.pagePresentation pq s hs).preimage I = E.infiniteBoundaries pq :=
    ((E.isLUB_boundariesSetFrom_iff pq hs).mp hI).unique (E.isLUB_infiniteBoundaries pq)
  have hpreK : (E.pagePresentation pq s hs).preimage K = E.infiniteCycles pq :=
    ((E.isGLB_cyclesSetFrom_iff pq hs).mp hK).unique (E.isGLB_infiniteCycles pq)
  have hIK : I ≤ K := by
    rw [← (E.pagePresentation pq s hs).preimage_le_preimage_iff, hpreI, hpreK]
    exact E.infiniteBoundaries_le_infiniteCycles pq
  refine ⟨hIK, ?_⟩
  dsimp only [limitPagePresentation, limitPage]
  refine ((E.pagePresentation pq s hs).ofSubobjects hIK).exists_transIso_eq_ofLE ?_ ?_ _
  · rw [TauCeti.SubquotientPresentation.ofSubobjects, TauCeti.SubquotientPresentation.trans_B,
      TauCeti.SubquotientPresentation.ofLE_B, hpreI]
  · rw [TauCeti.SubquotientPresentation.ofSubobjects, TauCeti.SubquotientPresentation.trans_Z,
      TauCeti.SubquotientPresentation.ofLE_Z, hpreK]

/-! ### Vanishing propagation -/

/-- If `(E.page r hr).X pq` vanishes for some `r ≥ r₀`, then `E.limitPage pq` vanishes whenever it
exists. -/
lemma isZero_limitPage_of_isZero_page_X (E : SpectralSequence C c r₀) (pq : κ)
    {r : ℤ} (hr : r₀ ≤ r) (hz : IsZero ((E.page r hr).X pq)) [E.HasLimitPageAt pq] :
    IsZero (E.limitPage pq) := by
  have hBZ : E.boundariesSubobject pq r hr = E.cyclesSubobject pq r hr :=
    (E.isZero_page_X_iff pq r hr).mp hz
  rw [(E.limitPagePresentation pq).isZero_iff, limitPagePresentation_B, limitPagePresentation_Z]
  exact le_antisymm (E.infiniteBoundaries_le_infiniteCycles pq) <|
    (E.infiniteCycles_le pq r hr).trans (hBZ.symm.le.trans (E.le_infiniteBoundaries pq r hr))

end CategoryTheory.SpectralSequence
