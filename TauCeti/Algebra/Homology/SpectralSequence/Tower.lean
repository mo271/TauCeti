/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.Subquotient

/-!
# Cycle and boundary towers of a spectral sequence

In an abelian category `C`, every page object `(E.page r hr).X pq` (`r ≥ r₀`) of a spectral sequence
`E : SpectralSequence C c r₀` is canonically a subquotient of `(E.page r₀ le_rfl).X pq` (and more
generally of `(E.page s hs).X pq` for any intermediate page `r₀ ≤ s ≤ r`), constructed inductively
by composing `TauCeti.SubquotientPresentation` with `HomologicalComplex.homologyPresentation` and
`E.iso r (r + 1) pq`.

This yields the nested towers of boundary and cycle subobjects inside `(E.page r₀ le_rfl).X pq`:
`⊥ = B_{r₀} ≤ B_{r₀+1} ≤ ⋯ ≤ B_r ≤ ⋯ ≤ Z_r ≤ ⋯ ≤ Z_{r₀+1} ≤ Z_{r₀} = ⊤`,
together with:
* step-equality characterizations `cyclesSubobject_add_one_eq_iff` and
  `boundariesSubobject_add_one_eq_iff` (`Z_{r+1} = Z_r ↔ d_r = 0` out of `pq` and
  `B_{r+1} = B_r ↔ d_r = 0` into `pq`);
* vanishing characterization `isZero_page_X_iff` (`IsZero ((E.page r).X pq) ↔ B_r = Z_r`);
* functoriality `descMap_pagePresentation` and isomorphism transport along `e : E ≅ E'`;
* rebasing `pagePresentation_eq_trans` comparing the towers inside `E_{r₀}` with those inside any
  later page `E_s` (`s ≥ r₀`).

## References

* The Stacks Project Authors, *The Stacks Project*, Tags 011N and 011O.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SpectralSequence

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-! ### Subquotient presentations from an intermediate page and from `r₀` -/

/-- The canonical presentation of `(E.page r).X pq` as a subquotient of an earlier page object
`(E.page s).X pq` (`r₀ ≤ s ≤ r`), built inductively along the page homology isomorphisms. -/
noncomputable def pagePresentationFrom (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    TauCeti.SubquotientPresentation ((E.page s hs).X pq) ((E.page r (hs.trans hsr)).X pq) :=
  Int.leInduction
    (motive := fun r hsr ↦
      TauCeti.SubquotientPresentation ((E.page s hs).X pq) ((E.page r (hs.trans hsr)).X pq))
    (TauCeti.SubquotientPresentation.refl _)
    (fun r hsr P ↦
      (P.trans ((E.page r (hs.trans hsr)).homologyPresentation pq)).transIso
        (E.iso r (r + 1) pq rfl (hs.trans hsr)))
    r hsr

@[simp]
lemma pagePresentationFrom_self (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ) (hs : r₀ ≤ s) :
    E.pagePresentationFrom pq s hs s le_rfl = TauCeti.SubquotientPresentation.refl _ :=
  Int.leInduction_base _ _

lemma pagePresentationFrom_add_one (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.pagePresentationFrom pq s hs (r + 1) (Int.le_add_one hsr) =
      ((E.pagePresentationFrom pq s hs r hsr).trans
        ((E.page r (hs.trans hsr)).homologyPresentation pq)).transIso
        (E.iso r (r + 1) pq rfl (hs.trans hsr)) :=
  Int.leInduction_add_one _ _ r hsr

/-- The `r`-th boundary subobject at `pq` viewed inside `(E.page s hs).X pq` (`r₀ ≤ s ≤ r`). -/
noncomputable abbrev boundariesSubobjectFrom (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) : Subobject ((E.page s hs).X pq) :=
  (E.pagePresentationFrom pq s hs r hsr).B

/-- The `r`-th cycle subobject at `pq` viewed inside `(E.page s hs).X pq` (`r₀ ≤ s ≤ r`). -/
noncomputable abbrev cyclesSubobjectFrom (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) : Subobject ((E.page s hs).X pq) :=
  (E.pagePresentationFrom pq s hs r hsr).Z

/-- The canonical presentation of `(E.page r hr).X pq` as a subquotient of the initial page object
`(E.page r₀ le_rfl).X pq`. -/
noncomputable abbrev pagePresentation (E : SpectralSequence C c r₀) (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r := by lia) :
    TauCeti.SubquotientPresentation ((E.page r₀ le_rfl).X pq) ((E.page r hr).X pq) :=
  E.pagePresentationFrom pq r₀ le_rfl r hr

/-- The `r`-th boundary subobject `B_r^{pq} ≤ (E.page r₀ le_rfl).X pq` of a spectral sequence. -/
noncomputable abbrev boundariesSubobject (E : SpectralSequence C c r₀) (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r := by lia) : Subobject ((E.page r₀ le_rfl).X pq) :=
  (E.pagePresentation pq r hr).B

/-- The `r`-th cycle subobject `Z_r^{pq} ≤ (E.page r₀ le_rfl).X pq` of a spectral sequence. -/
noncomputable abbrev cyclesSubobject (E : SpectralSequence C c r₀) (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r := by lia) : Subobject ((E.page r₀ le_rfl).X pq) :=
  (E.pagePresentation pq r hr).Z

lemma pagePresentation_r₀ (E : SpectralSequence C c r₀) (pq : κ) :
    E.pagePresentation pq r₀ le_rfl = TauCeti.SubquotientPresentation.refl _ :=
  E.pagePresentationFrom_self pq r₀ le_rfl

lemma pagePresentation_add_one (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    E.pagePresentation pq (r + 1) (Int.le_add_one hr) =
      ((E.pagePresentation pq r hr).trans
        ((E.page r hr).homologyPresentation pq)).transIso
        (E.iso r (r + 1) pq rfl hr) :=
  E.pagePresentationFrom_add_one pq r₀ le_rfl r hr

/-! ### Rebasing across intermediate pages -/

/-- For `r₀ ≤ s ≤ t ≤ r`, the subquotient presentation from `s` to `r` factors as the presentation
from `s` to `t` composed with the presentation from `t` to `r`. -/
lemma pagePresentationFrom_eq_trans (E : SpectralSequence C c r₀) (pq : κ)
    {s t r : ℤ} (hs : r₀ ≤ s) (hst : s ≤ t) (htr : t ≤ r) :
    E.pagePresentationFrom pq s hs r (hst.trans htr) =
      (E.pagePresentationFrom pq s hs t hst).trans
        (E.pagePresentationFrom pq t (hs.trans hst) r htr) := by
  induction r, htr using Int.leInduction with
  | base => simp
  | succ r htr ih =>
    rw [E.pagePresentationFrom_add_one pq s hs r (hst.trans htr),
      E.pagePresentationFrom_add_one pq t (hs.trans hst) r htr, ih,
      TauCeti.SubquotientPresentation.trans_assoc,
      TauCeti.SubquotientPresentation.trans_transIso]

/-- Rebasing from `r₀` through an intermediate page `s ≥ r₀`: `E.pagePresentation pq r` factors as
`E.pagePresentation pq s` composed with `E.pagePresentationFrom pq s hs r hsr`. -/
lemma pagePresentation_eq_trans (E : SpectralSequence C c r₀) (pq : κ)
    {s r : ℤ} (hs : r₀ ≤ s) (hsr : s ≤ r) :
    E.pagePresentation pq r (hs.trans hsr) =
      (E.pagePresentation pq s hs).trans (E.pagePresentationFrom pq s hs r hsr) :=
  E.pagePresentationFrom_eq_trans pq le_rfl hs hsr

@[simp]
lemma preimage_boundariesSubobjectFrom (E : SpectralSequence C c r₀) (pq : κ)
    {s r : ℤ} (hs : r₀ ≤ s) (hsr : s ≤ r) :
    (E.pagePresentation pq s hs).preimage (E.boundariesSubobjectFrom pq s hs r hsr) =
      E.boundariesSubobject pq r (hs.trans hsr) := by
  dsimp only [boundariesSubobject, boundariesSubobjectFrom]
  rw [E.pagePresentation_eq_trans pq hs hsr, TauCeti.SubquotientPresentation.trans_B]

@[simp]
lemma preimage_cyclesSubobjectFrom (E : SpectralSequence C c r₀) (pq : κ)
    {s r : ℤ} (hs : r₀ ≤ s) (hsr : s ≤ r) :
    (E.pagePresentation pq s hs).preimage (E.cyclesSubobjectFrom pq s hs r hsr) =
      E.cyclesSubobject pq r (hs.trans hsr) := by
  dsimp only [cyclesSubobject, cyclesSubobjectFrom]
  rw [E.pagePresentation_eq_trans pq hs hsr, TauCeti.SubquotientPresentation.trans_Z]

/-! ### Inclusions, monotonicity, step-equality, and vanishing -/

@[simp]
lemma boundariesSubobjectFrom_self (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ) (hs : r₀ ≤ s) :
    E.boundariesSubobjectFrom pq s hs s le_rfl = ⊥ := by
  simp [boundariesSubobjectFrom]

@[simp]
lemma cyclesSubobjectFrom_self (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ) (hs : r₀ ≤ s) :
    E.cyclesSubobjectFrom pq s hs s le_rfl = ⊤ := by
  simp [cyclesSubobjectFrom]

lemma boundariesSubobject_r₀ (E : SpectralSequence C c r₀) (pq : κ) :
    E.boundariesSubobject pq r₀ le_rfl = ⊥ :=
  E.boundariesSubobjectFrom_self pq r₀ le_rfl

lemma cyclesSubobject_r₀ (E : SpectralSequence C c r₀) (pq : κ) :
    E.cyclesSubobject pq r₀ le_rfl = ⊤ :=
  E.cyclesSubobjectFrom_self pq r₀ le_rfl

lemma boundariesSubobjectFrom_add_one_eq_preimage (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.boundariesSubobjectFrom pq s hs (r + 1) (Int.le_add_one hsr) =
      (E.pagePresentationFrom pq s hs r hsr).preimage
        (imageSubobject ((E.page r (hs.trans hsr)).dTo pq)) := by
  dsimp only [boundariesSubobjectFrom]
  rw [pagePresentationFrom_add_one, TauCeti.SubquotientPresentation.transIso_B,
    TauCeti.SubquotientPresentation.trans_B, HomologicalComplex.homologyPresentation_B]

lemma cyclesSubobjectFrom_add_one_eq_preimage (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.cyclesSubobjectFrom pq s hs (r + 1) (Int.le_add_one hsr) =
      (E.pagePresentationFrom pq s hs r hsr).preimage
        (kernelSubobject ((E.page r (hs.trans hsr)).dFrom pq)) := by
  dsimp only [cyclesSubobjectFrom]
  rw [pagePresentationFrom_add_one, TauCeti.SubquotientPresentation.transIso_Z,
    TauCeti.SubquotientPresentation.trans_Z, HomologicalComplex.homologyPresentation_Z]

lemma boundariesSubobject_add_one_eq_preimage (E : SpectralSequence C c r₀) (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).preimage (imageSubobject ((E.page r hr).dTo pq)) :=
  E.boundariesSubobjectFrom_add_one_eq_preimage pq r₀ le_rfl r hr

lemma cyclesSubobject_add_one_eq_preimage (E : SpectralSequence C c r₀) (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) =
      (E.pagePresentation pq r hr).preimage (kernelSubobject ((E.page r hr).dFrom pq)) :=
  E.cyclesSubobjectFrom_add_one_eq_preimage pq r₀ le_rfl r hr

lemma boundariesSubobjectFrom_le_cyclesSubobjectFrom (E : SpectralSequence C c r₀) (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.boundariesSubobjectFrom pq s hs r hsr ≤ E.cyclesSubobjectFrom pq s hs r hsr :=
  (E.pagePresentationFrom pq s hs r hsr).le

lemma boundariesSubobject_le_cyclesSubobject (E : SpectralSequence C c r₀) (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r hr ≤ E.cyclesSubobject pq r hr :=
  (E.pagePresentation pq r hr).le

lemma boundariesSubobjectFrom_mono (E : SpectralSequence C c r₀) (pq : κ)
    {s r r' : ℤ} (hs : r₀ ≤ s) (hsr : s ≤ r) (hrr' : r ≤ r') :
    E.boundariesSubobjectFrom pq s hs r hsr ≤
      E.boundariesSubobjectFrom pq s hs r' (hsr.trans hrr') := by
  dsimp only [boundariesSubobjectFrom]
  rw [E.pagePresentationFrom_eq_trans pq hs hsr hrr', TauCeti.SubquotientPresentation.trans_B]
  exact (E.pagePresentationFrom pq s hs r hsr).B_le_preimage _

lemma cyclesSubobjectFrom_anti (E : SpectralSequence C c r₀) (pq : κ)
    {s r r' : ℤ} (hs : r₀ ≤ s) (hsr : s ≤ r) (hrr' : r ≤ r') :
    E.cyclesSubobjectFrom pq s hs r' (hsr.trans hrr') ≤
      E.cyclesSubobjectFrom pq s hs r hsr := by
  dsimp only [cyclesSubobjectFrom]
  rw [E.pagePresentationFrom_eq_trans pq hs hsr hrr', TauCeti.SubquotientPresentation.trans_Z]
  exact (E.pagePresentationFrom pq s hs r hsr).preimage_le_Z _

lemma boundariesSubobject_mono (E : SpectralSequence C c r₀) (pq : κ)
    {r r' : ℤ} (hr : r₀ ≤ r) (hrr' : r ≤ r') :
    E.boundariesSubobject pq r hr ≤ E.boundariesSubobject pq r' (hr.trans hrr') :=
  E.boundariesSubobjectFrom_mono pq le_rfl hr hrr'

lemma cyclesSubobject_anti (E : SpectralSequence C c r₀) (pq : κ)
    {r r' : ℤ} (hr : r₀ ≤ r) (hrr' : r ≤ r') :
    E.cyclesSubobject pq r' (hr.trans hrr') ≤ E.cyclesSubobject pq r hr :=
  E.cyclesSubobjectFrom_anti pq le_rfl hr hrr'

lemma boundariesSubobject_le_add_one (E : SpectralSequence C c r₀) (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq r hr ≤ E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) :=
  E.boundariesSubobject_mono pq hr (Int.le_add_one le_rfl)

lemma cyclesSubobject_add_one_le (E : SpectralSequence C c r₀) (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) ≤ E.cyclesSubobject pq r hr :=
  E.cyclesSubobject_anti pq hr (Int.le_add_one le_rfl)

/-- Every boundary subobject is contained in every cycle subobject, regardless of the page indices
`r, r' ≥ r₀`. -/
lemma boundariesSubobjectFrom_le_cyclesSubobjectFrom_of_all (E : SpectralSequence C c r₀) (pq : κ)
    {s r r' : ℤ} (hs : r₀ ≤ s) (hsr : s ≤ r) (hsr' : s ≤ r') :
    E.boundariesSubobjectFrom pq s hs r hsr ≤ E.cyclesSubobjectFrom pq s hs r' hsr' :=
  (E.boundariesSubobjectFrom_mono pq hs hsr (le_max_left r r')).trans <|
    (E.boundariesSubobjectFrom_le_cyclesSubobjectFrom pq s hs (max r r')
      (hsr.trans (le_max_left r r'))).trans <|
      E.cyclesSubobjectFrom_anti pq hs hsr' (le_max_right r r')

/-- Every boundary subobject `B_r^{pq}` is contained in every cycle subobject `Z_{r'}^{pq}`. -/
lemma boundariesSubobject_le_cyclesSubobject_of_all (E : SpectralSequence C c r₀) (pq : κ)
    {r r' : ℤ} (hr : r₀ ≤ r) (hr' : r₀ ≤ r') :
    E.boundariesSubobject pq r hr ≤ E.cyclesSubobject pq r' hr' :=
  E.boundariesSubobjectFrom_le_cyclesSubobjectFrom_of_all pq le_rfl hr hr'

@[simp]
lemma boundariesSubobjectFrom_eq_imageOfLE (E : SpectralSequence C c r₀) (pq : κ)
    {s r : ℤ} (hs : r₀ ≤ s) (hsr : s ≤ r)
    (hle : E.boundariesSubobject pq r (hs.trans hsr) ≤ (E.pagePresentation pq s hs).Z :=
      E.boundariesSubobject_le_cyclesSubobject_of_all pq (hs.trans hsr) hs) :
    (E.pagePresentation pq s hs).imageOfLE (E.boundariesSubobject pq r (hs.trans hsr)) hle =
      E.boundariesSubobjectFrom pq s hs r hsr := by
  apply (E.pagePresentation pq s hs).preimage_injective
  rw [(E.pagePresentation pq s hs).preimage_imageOfLE (E.boundariesSubobject_mono pq hs hsr) hle,
    E.preimage_boundariesSubobjectFrom pq hs hsr]

@[simp]
lemma cyclesSubobjectFrom_eq_imageOfLE (E : SpectralSequence C c r₀) (pq : κ)
    {s r : ℤ} (hs : r₀ ≤ s) (hsr : s ≤ r)
    (hle : E.cyclesSubobject pq r (hs.trans hsr) ≤ (E.pagePresentation pq s hs).Z :=
      E.cyclesSubobject_anti pq hs hsr) :
    (E.pagePresentation pq s hs).imageOfLE (E.cyclesSubobject pq r (hs.trans hsr)) hle =
      E.cyclesSubobjectFrom pq s hs r hsr := by
  apply (E.pagePresentation pq s hs).preimage_injective
  rw [(E.pagePresentation pq s hs).preimage_imageOfLE
      (E.boundariesSubobject_le_cyclesSubobject_of_all pq hs (hs.trans hsr)) hle,
    E.preimage_cyclesSubobjectFrom pq hs hsr]

/-- Step-equality in the cycle tower: `Z_{r+1}^{pq} = Z_r^{pq}` if and only if the differential out
of `pq` on page `r` vanishes. -/
lemma cyclesSubobject_add_one_eq_iff (E : SpectralSequence C c r₀) (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) = E.cyclesSubobject pq r hr ↔
      (E.page r hr).dFrom pq = 0 := by
  rw [E.cyclesSubobject_add_one_eq_preimage pq r hr]
  dsimp only [cyclesSubobject]
  rw [← (E.pagePresentation pq r hr).preimage_top,
    (E.pagePresentation pq r hr).preimage_eq_preimage_iff,
    Subobject.kernelSubobject_eq_top_iff]

/-- Step-equality in the cycle tower phrased via all outgoing differentials `d pq pq'`. -/
lemma cyclesSubobject_add_one_eq_iff_forall_d (E : SpectralSequence C c r₀) (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq (r + 1) (Int.le_add_one hr) = E.cyclesSubobject pq r hr ↔
      ∀ pq', (E.page r hr).d pq pq' = 0 := by
  rw [cyclesSubobject_add_one_eq_iff, HomologicalComplex.dFrom_eq_zero_iff]

/-- Step-equality in the boundary tower: `B_{r+1}^{pq} = B_r^{pq}` if and only if the differential
into `pq` on page `r` vanishes. -/
lemma boundariesSubobject_add_one_eq_iff (E : SpectralSequence C c r₀) (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) = E.boundariesSubobject pq r hr ↔
      (E.page r hr).dTo pq = 0 := by
  rw [E.boundariesSubobject_add_one_eq_preimage pq r hr]
  dsimp only [boundariesSubobject]
  rw [← (E.pagePresentation pq r hr).preimage_bot,
    (E.pagePresentation pq r hr).preimage_eq_preimage_iff,
    Subobject.imageSubobject_eq_bot_iff]

/-- Step-equality in the boundary tower phrased via all incoming differentials `d pq' pq`. -/
lemma boundariesSubobject_add_one_eq_iff_forall_d (E : SpectralSequence C c r₀) (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r) :
    E.boundariesSubobject pq (r + 1) (Int.le_add_one hr) = E.boundariesSubobject pq r hr ↔
      ∀ pq', (E.page r hr).d pq' pq = 0 := by
  rw [boundariesSubobject_add_one_eq_iff, HomologicalComplex.dTo_eq_zero_iff]

/-- A page object `(E.page r hr).X pq` vanishes if and only if `B_r^{pq} = Z_r^{pq}`. -/
lemma isZero_page_X_iff (E : SpectralSequence C c r₀) (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    IsZero ((E.page r hr).X pq) ↔ E.boundariesSubobject pq r hr = E.cyclesSubobject pq r hr :=
  (E.pagePresentation pq r hr).isZero_iff

/-! ### Functoriality and isomorphism transport -/

private lemma descMap_congr {A₁ A₂ X₁ X₂ : C}
    {P₁ P₁' : TauCeti.SubquotientPresentation A₁ X₁}
    {P₂ P₂' : TauCeti.SubquotientPresentation A₂ X₂} (h₁ : P₁ = P₁') (h₂ : P₂ = P₂')
    (f : A₁ ⟶ A₂) (hB : (Subobject.exists f).obj P₁.B ≤ P₂.B)
    (hZ : P₁.Z ≤ (Subobject.pullback f).obj P₂.Z)
    (hB' : (Subobject.exists f).obj P₁'.B ≤ P₂'.B)
    (hZ' : P₁'.Z ≤ (Subobject.pullback f).obj P₂'.Z) :
    P₁.descMap P₂ f hB hZ = P₁'.descMap P₂' f hB' hZ' := by
  subst h₁ h₂
  rfl

private lemma pagePresentationFrom_naturality_aux {E E' : SpectralSequence C c r₀}
    (f : E ⟶ E') (pq : κ) (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    ∃ (hB : (Subobject.exists ((f.hom s hs).f pq)).obj
          (E.pagePresentationFrom pq s hs r hsr).B ≤
        (E'.pagePresentationFrom pq s hs r hsr).B)
      (hZ : (E.pagePresentationFrom pq s hs r hsr).Z ≤
        (Subobject.pullback ((f.hom s hs).f pq)).obj
          (E'.pagePresentationFrom pq s hs r hsr).Z),
      (E.pagePresentationFrom pq s hs r hsr).descMap
        (E'.pagePresentationFrom pq s hs r hsr) ((f.hom s hs).f pq) hB hZ =
        (f.hom r (hs.trans hsr)).f pq := by
  induction r, hsr using Int.leInduction with
  | base =>
    have hB : (Subobject.exists ((f.hom s hs).f pq)).obj
        (E.pagePresentationFrom pq s hs s le_rfl).B ≤
      (E'.pagePresentationFrom pq s hs s le_rfl).B := by
      rw [pagePresentationFrom_self, pagePresentationFrom_self]
      exact TauCeti.SubquotientPresentation.exists_refl_le _
    have hZ : (E.pagePresentationFrom pq s hs s le_rfl).Z ≤
        (Subobject.pullback ((f.hom s hs).f pq)).obj
          (E'.pagePresentationFrom pq s hs s le_rfl).Z := by
      rw [pagePresentationFrom_self, pagePresentationFrom_self]
      exact TauCeti.SubquotientPresentation.refl_le_pullback _
    refine ⟨hB, hZ, ?_⟩
    rw [descMap_congr (E.pagePresentationFrom_self pq s hs)
      (E'.pagePresentationFrom_self pq s hs) ((f.hom s hs).f pq) hB hZ
      (TauCeti.SubquotientPresentation.exists_refl_le _)
      (TauCeti.SubquotientPresentation.refl_le_pullback _),
      TauCeti.SubquotientPresentation.descMap_refl]
  | succ r hsr ih =>
    obtain ⟨hB, hZ, hdesc⟩ := ih
    have hQB : (Subobject.exists ((E.pagePresentationFrom pq s hs r hsr).descMap
          (E'.pagePresentationFrom pq s hs r hsr) ((f.hom s hs).f pq) hB hZ)).obj
        ((E.page r (hs.trans hsr)).homologyPresentation pq).B ≤
      ((E'.page r (hs.trans hsr)).homologyPresentation pq).B := by
      rw [hdesc]
      exact HomologicalComplex.exists_homologyPresentation_B_le (f.hom r (hs.trans hsr)) pq
    have hQZ : ((E.page r (hs.trans hsr)).homologyPresentation pq).Z ≤
        (Subobject.pullback ((E.pagePresentationFrom pq s hs r hsr).descMap
          (E'.pagePresentationFrom pq s hs r hsr) ((f.hom s hs).f pq) hB hZ)).obj
        ((E'.page r (hs.trans hsr)).homologyPresentation pq).Z := by
      rw [hdesc]
      exact HomologicalComplex.homologyPresentation_Z_le_pullback (f.hom r (hs.trans hsr)) pq
    have hB_tr : (Subobject.exists ((f.hom s hs).f pq)).obj
        ((E.pagePresentationFrom pq s hs r hsr).trans
          ((E.page r (hs.trans hsr)).homologyPresentation pq)).B ≤
      ((E'.pagePresentationFrom pq s hs r hsr).trans
        ((E'.page r (hs.trans hsr)).homologyPresentation pq)).B := by
      rw [TauCeti.SubquotientPresentation.trans_B, TauCeti.SubquotientPresentation.trans_B]
      exact (E.pagePresentationFrom pq s hs r hsr).exists_preimage_le
        (E'.pagePresentationFrom pq s hs r hsr) ((f.hom s hs).f pq) hB hZ hQB
    have hZ_tr : ((E.pagePresentationFrom pq s hs r hsr).trans
          ((E.page r (hs.trans hsr)).homologyPresentation pq)).Z ≤
        (Subobject.pullback ((f.hom s hs).f pq)).obj
          (((E'.pagePresentationFrom pq s hs r hsr).trans
            ((E'.page r (hs.trans hsr)).homologyPresentation pq)).Z) := by
      rw [TauCeti.SubquotientPresentation.trans_Z, TauCeti.SubquotientPresentation.trans_Z]
      exact (E.pagePresentationFrom pq s hs r hsr).preimage_le_pullback
        (E'.pagePresentationFrom pq s hs r hsr) ((f.hom s hs).f pq) hB hZ hQZ
    have hB_iso : (Subobject.exists ((f.hom s hs).f pq)).obj
        (((E.pagePresentationFrom pq s hs r hsr).trans
          ((E.page r (hs.trans hsr)).homologyPresentation pq)).transIso
          (E.iso r (r + 1) pq rfl (hs.trans hsr))).B ≤
      (((E'.pagePresentationFrom pq s hs r hsr).trans
        ((E'.page r (hs.trans hsr)).homologyPresentation pq)).transIso
        (E'.iso r (r + 1) pq rfl (hs.trans hsr))).B := by
      simpa using hB_tr
    have hZ_iso : (((E.pagePresentationFrom pq s hs r hsr).trans
          ((E.page r (hs.trans hsr)).homologyPresentation pq)).transIso
          (E.iso r (r + 1) pq rfl (hs.trans hsr))).Z ≤
        (Subobject.pullback ((f.hom s hs).f pq)).obj
          ((((E'.pagePresentationFrom pq s hs r hsr).trans
            ((E'.page r (hs.trans hsr)).homologyPresentation pq)).transIso
            (E'.iso r (r + 1) pq rfl (hs.trans hsr))).Z) := by
      simpa using hZ_tr
    have hB' : (Subobject.exists ((f.hom s hs).f pq)).obj
        (E.pagePresentationFrom pq s hs (r + 1) (Int.le_add_one hsr)).B ≤
      (E'.pagePresentationFrom pq s hs (r + 1) (Int.le_add_one hsr)).B := by
      rw [pagePresentationFrom_add_one, pagePresentationFrom_add_one]
      exact hB_iso
    have hZ' : (E.pagePresentationFrom pq s hs (r + 1) (Int.le_add_one hsr)).Z ≤
        (Subobject.pullback ((f.hom s hs).f pq)).obj
          (E'.pagePresentationFrom pq s hs (r + 1) (Int.le_add_one hsr)).Z := by
      rw [pagePresentationFrom_add_one, pagePresentationFrom_add_one]
      exact hZ_iso
    refine ⟨hB', hZ', ?_⟩
    rw [descMap_congr (E.pagePresentationFrom_add_one pq s hs r hsr)
      (E'.pagePresentationFrom_add_one pq s hs r hsr) ((f.hom s hs).f pq) hB' hZ' hB_iso hZ_iso,
      TauCeti.SubquotientPresentation.descMap_transIso _ _ _ _ _ hB_tr hZ_tr hB_iso hZ_iso,
      TauCeti.SubquotientPresentation.descMap_trans _ _ _ _ _ hB hZ hQB hQZ hB_tr hZ_tr]
    have hhom : ((E.page r (hs.trans hsr)).homologyPresentation pq).descMap
        ((E'.page r (hs.trans hsr)).homologyPresentation pq)
        ((E.pagePresentationFrom pq s hs r hsr).descMap
          (E'.pagePresentationFrom pq s hs r hsr) ((f.hom s hs).f pq) hB hZ) hQB hQZ =
        HomologicalComplex.homologyMap (f.hom r (hs.trans hsr)) pq := by
      refine ((E.page r (hs.trans hsr)).homologyPresentation pq).descMap_eq_of_π_comp _ _ _ _ ?_
      rw [← HomologicalComplex.descMap_homologyPresentation (f.hom r (hs.trans hsr)) pq,
        TauCeti.SubquotientPresentation.π_comp_descMap]
      congr 1
      rw [← cancel_mono ((E'.page r (hs.trans hsr)).homologyPresentation pq).Z.arrow,
        TauCeti.SubquotientPresentation.mapZ_arrow,
        TauCeti.SubquotientPresentation.mapZ_arrow, hdesc]
    rw [hhom, f.comm r (r + 1) pq rfl (hs.trans hsr), Iso.inv_hom_id_assoc]

/-- A morphism `f : E ⟶ E'` maps `boundariesSubobjectFrom` of `E` into that of `E'` along
`(f.hom s hs).f pq`. -/
lemma exists_boundariesSubobjectFrom_le {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    (Subobject.exists ((f.hom s hs).f pq)).obj (E.boundariesSubobjectFrom pq s hs r hsr) ≤
      E'.boundariesSubobjectFrom pq s hs r hsr :=
  (pagePresentationFrom_naturality_aux f pq s hs r hsr).1

/-- A morphism `f : E ⟶ E'` maps `cyclesSubobjectFrom` of `E` into that of `E'` along
`(f.hom s hs).f pq`. -/
lemma cyclesSubobjectFrom_le_pullback {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    E.cyclesSubobjectFrom pq s hs r hsr ≤
      (Subobject.pullback ((f.hom s hs).f pq)).obj (E'.cyclesSubobjectFrom pq s hs r hsr) :=
  (pagePresentationFrom_naturality_aux f pq s hs r hsr).2.1

/-- The morphism induced by `(f.hom s hs).f pq` on `pagePresentationFrom` agrees with the `r`-th
page morphism `(f.hom r).f pq`. -/
lemma descMap_pagePresentationFrom {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r)
    (hB : (Subobject.exists ((f.hom s hs).f pq)).obj
        (E.pagePresentationFrom pq s hs r hsr).B ≤
      (E'.pagePresentationFrom pq s hs r hsr).B :=
      exists_boundariesSubobjectFrom_le f pq s hs r hsr)
    (hZ : (E.pagePresentationFrom pq s hs r hsr).Z ≤
        (Subobject.pullback ((f.hom s hs).f pq)).obj
          (E'.pagePresentationFrom pq s hs r hsr).Z :=
      cyclesSubobjectFrom_le_pullback f pq s hs r hsr) :
    (E.pagePresentationFrom pq s hs r hsr).descMap
      (E'.pagePresentationFrom pq s hs r hsr) ((f.hom s hs).f pq) hB hZ =
      (f.hom r (hs.trans hsr)).f pq :=
  (pagePresentationFrom_naturality_aux f pq s hs r hsr).2.2

/-- A morphism `f : E ⟶ E'` maps `E.boundariesSubobject pq r` into `E'.boundariesSubobject pq r`
along `(f.hom r₀ le_rfl).f pq`. -/
lemma exists_boundariesSubobject_le {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r) :
    (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj (E.boundariesSubobject pq r hr) ≤
      E'.boundariesSubobject pq r hr :=
  exists_boundariesSubobjectFrom_le f pq r₀ le_rfl r hr

/-- A morphism `f : E ⟶ E'` maps `E.cyclesSubobject pq r` into `E'.cyclesSubobject pq r` along
`(f.hom r₀ le_rfl).f pq`. -/
lemma cyclesSubobject_le_pullback {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r) :
    E.cyclesSubobject pq r hr ≤
      (Subobject.pullback ((f.hom r₀ le_rfl).f pq)).obj (E'.cyclesSubobject pq r hr) :=
  cyclesSubobjectFrom_le_pullback f pq r₀ le_rfl r hr

/-- The morphism induced by `(f.hom r₀ le_rfl).f pq` on `pagePresentation` agrees with the `r`-th
page morphism `(f.hom r hr).f pq`. -/
lemma descMap_pagePresentation {E E' : SpectralSequence C c r₀} (f : E ⟶ E') (pq : κ)
    (r : ℤ) (hr : r₀ ≤ r)
    (hB : (Subobject.exists ((f.hom r₀ le_rfl).f pq)).obj (E.pagePresentation pq r hr).B ≤
      (E'.pagePresentation pq r hr).B := exists_boundariesSubobject_le f pq r hr)
    (hZ : (E.pagePresentation pq r hr).Z ≤
        (Subobject.pullback ((f.hom r₀ le_rfl).f pq)).obj (E'.pagePresentation pq r hr).Z :=
      cyclesSubobject_le_pullback f pq r hr) :
    (E.pagePresentation pq r hr).descMap (E'.pagePresentation pq r hr)
      ((f.hom r₀ le_rfl).f pq) hB hZ = (f.hom r hr).f pq :=
  descMap_pagePresentationFrom f pq r₀ le_rfl r hr hB hZ

private lemma mapIsoToOrderIso_eq_of_exists_le {X Y : C} (e : X ≅ Y) {S : Subobject X}
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

/-- An isomorphism `e : E ≅ E'` of spectral sequences transports `E.boundariesSubobjectFrom` to
`E'.boundariesSubobjectFrom` along the induced isomorphism on `(page s).X pq`. -/
lemma mapIsoToOrderIso_boundariesSubobjectFrom {E E' : SpectralSequence C c r₀} (e : E ≅ E')
    (pq : κ) (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    Subobject.mapIsoToOrderIso
      ((pageFunctor C c r₀ s hs ⋙ HomologicalComplex.eval C (c s) pq).mapIso e)
      (E.boundariesSubobjectFrom pq s hs r hsr) =
      E'.boundariesSubobjectFrom pq s hs r hsr :=
  mapIsoToOrderIso_eq_of_exists_le _
    (exists_boundariesSubobjectFrom_le e.hom pq s hs r hsr)
    (exists_boundariesSubobjectFrom_le e.inv pq s hs r hsr)

/-- An isomorphism `e : E ≅ E'` of spectral sequences transports `E.cyclesSubobjectFrom` to
`E'.cyclesSubobjectFrom` along the induced isomorphism on `(page s).X pq`. -/
lemma mapIsoToOrderIso_cyclesSubobjectFrom {E E' : SpectralSequence C c r₀} (e : E ≅ E')
    (pq : κ) (s : ℤ) (hs : r₀ ≤ s) (r : ℤ) (hsr : s ≤ r) :
    Subobject.mapIsoToOrderIso
      ((pageFunctor C c r₀ s hs ⋙ HomologicalComplex.eval C (c s) pq).mapIso e)
      (E.cyclesSubobjectFrom pq s hs r hsr) =
      E'.cyclesSubobjectFrom pq s hs r hsr :=
  mapIsoToOrderIso_eq_of_exists_le _
    (((Subobject.existsPullbackAdj ((e.hom.hom s hs).f pq)).gc _ _).mpr
      (cyclesSubobjectFrom_le_pullback e.hom pq s hs r hsr))
    (((Subobject.existsPullbackAdj ((e.inv.hom s hs).f pq)).gc _ _).mpr
      (cyclesSubobjectFrom_le_pullback e.inv pq s hs r hsr))

/-- An isomorphism `e : E ≅ E'` of spectral sequences transports `E.boundariesSubobject pq r` to
`E'.boundariesSubobject pq r`. -/
lemma mapIsoToOrderIso_boundariesSubobject {E E' : SpectralSequence C c r₀} (e : E ≅ E')
    (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    Subobject.mapIsoToOrderIso
      ((pageFunctor C c r₀ r₀ le_rfl ⋙ HomologicalComplex.eval C (c r₀) pq).mapIso e)
      (E.boundariesSubobject pq r hr) =
      E'.boundariesSubobject pq r hr :=
  mapIsoToOrderIso_boundariesSubobjectFrom e pq r₀ le_rfl r hr

/-- An isomorphism `e : E ≅ E'` of spectral sequences transports `E.cyclesSubobject pq r` to
`E'.cyclesSubobject pq r`. -/
lemma mapIsoToOrderIso_cyclesSubobject {E E' : SpectralSequence C c r₀} (e : E ≅ E')
    (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    Subobject.mapIsoToOrderIso
      ((pageFunctor C c r₀ r₀ le_rfl ⋙ HomologicalComplex.eval C (c r₀) pq).mapIso e)
      (E.cyclesSubobject pq r hr) =
      E'.cyclesSubobject pq r hr :=
  mapIsoToOrderIso_cyclesSubobjectFrom e pq r₀ le_rfl r hr

end CategoryTheory.SpectralSequence
