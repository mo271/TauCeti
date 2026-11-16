/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Tower

/-!
# Stabilisation, regularity, coregularity, and degeneration of spectral sequences

This file defines entrywise stabilisation, regularity, coregularity, and global degeneration for a
spectral sequence `E : SpectralSequence C c r₀` in an abelian category `C`, and connects them to the
cycle and boundary towers from `TauCeti.Algebra.Homology.SpectralSequence.Tower`:

* `CategoryTheory.SpectralSequence.StabilizesAt E pq s`: all differentials into and out of `pq`
  vanish on every page `r ≥ s`.
* `CategoryTheory.SpectralSequence.IsRegularAt E pq` and
  `CategoryTheory.SpectralSequence.IsCoregularAt E pq`: outgoing (resp. incoming) differentials at
  `pq` vanish on all sufficiently high pages; equivalent to eventual stationarity of the cycle
  (resp. boundary) tower (`isRegularAt_iff_eventually_cyclesSubobject_eq`,
  `isCoregularAt_iff_eventually_boundariesSubobject_eq`).
* `CategoryTheory.SpectralSequence.DegeneratesAt E s`: all differentials at all positions vanish on
  every page `r ≥ s`.
* `CategoryTheory.SpectralSequence.StabilizesAt.pageXIso`: the canonical stabilisation isomorphism
  `(E.page s).X pq ≅ (E.page r).X pq` (`r ≥ s`), compatible with `pagePresentationFrom`,
  `pagePresentation`, composition across `s ≤ r ≤ r'`, and morphisms of spectral sequences.

## References

* The Stacks Project Authors, *The Stacks Project*, Tag 0BDV (Lemma 24.8).
* G. Helle and J. Rognes, *Boardman's theorem on strong convergence of spectral sequences*.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SpectralSequence

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-! ### Predicates: stabilisation, regularity, coregularity, degeneration -/

/-- A spectral sequence `E` *stabilises* at `pq : κ` from page `s` if `r₀ ≤ s` and on every page
`r ≥ s` all differentials out of and into `pq` vanish. -/
structure StabilizesAt (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ) : Prop where
  le : r₀ ≤ s
  d_out : ∀ r (hsr : s ≤ r) pq', (E.page r (le.trans hsr)).d pq pq' = 0
  d_in : ∀ r (hsr : s ≤ r) pq', (E.page r (le.trans hsr)).d pq' pq = 0

/-- A spectral sequence `E` is *regular* at `pq : κ` if there exists `s ≥ r₀` such that on every
page `r ≥ s` all differentials out of `pq` vanish. -/
def IsRegularAt (E : SpectralSequence C c r₀) (pq : κ) : Prop :=
  ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ r (hsr : s ≤ r) pq', (E.page r (hs.trans hsr)).d pq pq' = 0

/-- A spectral sequence `E` is *coregular* at `pq : κ` if there exists `s ≥ r₀` such that on every
page `r ≥ s` all differentials into `pq` vanish. -/
def IsCoregularAt (E : SpectralSequence C c r₀) (pq : κ) : Prop :=
  ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ r (hsr : s ≤ r) pq', (E.page r (hs.trans hsr)).d pq' pq = 0

/-- A spectral sequence `E` *degenerates* at page `s` if `r₀ ≤ s` and on every page `r ≥ s` all
differentials vanish at every position. -/
structure DegeneratesAt (E : SpectralSequence C c r₀) (s : ℤ) : Prop where
  le : r₀ ≤ s
  d_eq_zero : ∀ r (hsr : s ≤ r) pq pq', (E.page r (le.trans hsr)).d pq pq' = 0

/-! ### Equivalence with eventual stationarity of the cycle and boundary towers -/

/-- Outgoing differentials at `pq` vanish on all pages `r ≥ s` if and only if the cycle tower is
constant from `s` onwards. -/
lemma forall_d_out_eq_zero_iff_cyclesSubobject_eq (E : SpectralSequence C c r₀) (pq : κ)
    {s : ℤ} (hs : r₀ ≤ s) :
    (∀ r (hsr : s ≤ r) pq', (E.page r (hs.trans hsr)).d pq pq' = 0) ↔
      ∀ r (hsr : s ≤ r), E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs := by
  constructor
  · intro hd r hsr
    induction r, hsr using Int.leInduction with
    | base => rfl
    | succ r hsr ih =>
      rw [(E.cyclesSubobject_add_one_eq_iff_forall_d pq r (hs.trans hsr)).mpr (hd r hsr), ih]
  · intro hZ r hsr
    rw [← E.cyclesSubobject_add_one_eq_iff_forall_d pq r (hs.trans hsr),
      hZ (r + 1) (Int.le_add_one hsr), hZ r hsr]

/-- Incoming differentials at `pq` vanish on all pages `r ≥ s` if and only if the boundary tower is
constant from `s` onwards. -/
lemma forall_d_in_eq_zero_iff_boundariesSubobject_eq (E : SpectralSequence C c r₀) (pq : κ)
    {s : ℤ} (hs : r₀ ≤ s) :
    (∀ r (hsr : s ≤ r) pq', (E.page r (hs.trans hsr)).d pq' pq = 0) ↔
      ∀ r (hsr : s ≤ r),
        E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs := by
  constructor
  · intro hd r hsr
    induction r, hsr using Int.leInduction with
    | base => rfl
    | succ r hsr ih =>
      rw [(E.boundariesSubobject_add_one_eq_iff_forall_d pq r (hs.trans hsr)).mpr (hd r hsr), ih]
  · intro hB r hsr
    rw [← E.boundariesSubobject_add_one_eq_iff_forall_d pq r (hs.trans hsr),
      hB (r + 1) (Int.le_add_one hsr), hB r hsr]

/-- **Stacks Tag 0BDV, Lemma 24.8(1):** `E` is regular at `pq` if and only if the cycle tower at
`pq` is eventually constant. -/
lemma isRegularAt_iff_eventually_cyclesSubobject_eq (E : SpectralSequence C c r₀) (pq : κ) :
    E.IsRegularAt pq ↔
      ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ r (hsr : s ≤ r),
        E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs :=
  exists_congr fun _ ↦ exists_congr fun hs ↦
    E.forall_d_out_eq_zero_iff_cyclesSubobject_eq pq hs

/-- **Stacks Tag 0BDV, Lemma 24.8(2):** `E` is coregular at `pq` if and only if the boundary tower
at `pq` is eventually constant. -/
lemma isCoregularAt_iff_eventually_boundariesSubobject_eq (E : SpectralSequence C c r₀) (pq : κ) :
    E.IsCoregularAt pq ↔
      ∃ (s : ℤ) (hs : r₀ ≤ s), ∀ r (hsr : s ≤ r),
        E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs :=
  exists_congr fun _ ↦ exists_congr fun hs ↦
    E.forall_d_in_eq_zero_iff_boundariesSubobject_eq pq hs

/-- `E` stabilises at `pq` from page `s` if and only if `r₀ ≤ s` and both the cycle and boundary
towers at `pq` are constant from `s` onwards. -/
lemma stabilizesAt_iff_towers_eq (E : SpectralSequence C c r₀) (pq : κ) (s : ℤ) :
    E.StabilizesAt pq s ↔
      ∃ hs : r₀ ≤ s,
        (∀ r (hsr : s ≤ r),
          E.cyclesSubobject pq r (hs.trans hsr) = E.cyclesSubobject pq s hs) ∧
        (∀ r (hsr : s ≤ r),
          E.boundariesSubobject pq r (hs.trans hsr) = E.boundariesSubobject pq s hs) := by
  refine ⟨fun h ↦ ⟨h.le,
    (E.forall_d_out_eq_zero_iff_cyclesSubobject_eq pq h.le).mp h.d_out,
    (E.forall_d_in_eq_zero_iff_boundariesSubobject_eq pq h.le).mp h.d_in⟩, ?_⟩
  rintro ⟨hs, hZ, hB⟩
  exact ⟨hs,
    (E.forall_d_out_eq_zero_iff_cyclesSubobject_eq pq hs).mpr hZ,
    (E.forall_d_in_eq_zero_iff_boundariesSubobject_eq pq hs).mpr hB⟩

/-! ### Monotonicity, combination of regularity and coregularity, and degeneration -/

lemma StabilizesAt.mono {E : SpectralSequence C c r₀} {pq : κ} {s s' : ℤ}
    (h : E.StabilizesAt pq s) (hss' : s ≤ s') : E.StabilizesAt pq s' where
  le := h.le.trans hss'
  d_out r hs'r pq' := h.d_out r (hss'.trans hs'r) pq'
  d_in r hs'r pq' := h.d_in r (hss'.trans hs'r) pq'

lemma StabilizesAt.dFrom_eq_zero {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) (r : ℤ) (hsr : s ≤ r) :
    (E.page r (h.le.trans hsr)).dFrom pq = 0 :=
  ((E.page r (h.le.trans hsr)).dFrom_eq_zero_iff pq).mpr (h.d_out r hsr)

lemma StabilizesAt.dTo_eq_zero {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) (r : ℤ) (hsr : s ≤ r) :
    (E.page r (h.le.trans hsr)).dTo pq = 0 :=
  ((E.page r (h.le.trans hsr)).dTo_eq_zero_iff pq).mpr (h.d_in r hsr)

lemma StabilizesAt.cyclesSubobject_eq {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) (r : ℤ) (hsr : s ≤ r) :
    E.cyclesSubobject pq r (h.le.trans hsr) = E.cyclesSubobject pq s h.le :=
  (E.forall_d_out_eq_zero_iff_cyclesSubobject_eq pq h.le).mp h.d_out r hsr

lemma StabilizesAt.boundariesSubobject_eq {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) (r : ℤ) (hsr : s ≤ r) :
    E.boundariesSubobject pq r (h.le.trans hsr) = E.boundariesSubobject pq s h.le :=
  (E.forall_d_in_eq_zero_iff_boundariesSubobject_eq pq h.le).mp h.d_in r hsr

lemma StabilizesAt.isRegularAt {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) : E.IsRegularAt pq :=
  ⟨s, h.le, h.d_out⟩

lemma StabilizesAt.isCoregularAt {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) : E.IsCoregularAt pq :=
  ⟨s, h.le, h.d_in⟩

/-- Regularity and coregularity together at `pq` are equivalent to stabilisation at `pq` from some
page `s`. -/
lemma isRegularAt_and_isCoregularAt_iff (E : SpectralSequence C c r₀) (pq : κ) :
    E.IsRegularAt pq ∧ E.IsCoregularAt pq ↔ ∃ s, E.StabilizesAt pq s := by
  refine ⟨?_, fun ⟨s, h⟩ ↦ ⟨h.isRegularAt, h.isCoregularAt⟩⟩
  rintro ⟨⟨s₁, hs₁, hd₁⟩, ⟨s₂, _, hd₂⟩⟩
  exact ⟨max s₁ s₂, hs₁.trans (le_max_left s₁ s₂),
    fun r hr pq' ↦ hd₁ r ((le_max_left s₁ s₂).trans hr) pq',
    fun r hr pq' ↦ hd₂ r ((le_max_right s₁ s₂).trans hr) pq'⟩

lemma DegeneratesAt.mono {E : SpectralSequence C c r₀} {s s' : ℤ}
    (h : E.DegeneratesAt s) (hss' : s ≤ s') : E.DegeneratesAt s' where
  le := h.le.trans hss'
  d_eq_zero r hs'r pq pq' := h.d_eq_zero r (hss'.trans hs'r) pq pq'

lemma DegeneratesAt.stabilizesAt {E : SpectralSequence C c r₀} {s : ℤ}
    (h : E.DegeneratesAt s) (pq : κ) : E.StabilizesAt pq s where
  le := h.le
  d_out r hsr pq' := h.d_eq_zero r hsr pq pq'
  d_in r hsr pq' := h.d_eq_zero r hsr pq' pq

/-- Global degeneration at page `s` is equivalent to `r₀ ≤ s` together with entrywise stabilisation
at every `pq : κ` from page `s`. -/
lemma degeneratesAt_iff_forall_stabilizesAt (E : SpectralSequence C c r₀) (s : ℤ) :
    E.DegeneratesAt s ↔ r₀ ≤ s ∧ ∀ pq, E.StabilizesAt pq s :=
  ⟨fun h ↦ ⟨h.le, h.stabilizesAt⟩,
    fun ⟨hs, h⟩ ↦ ⟨hs, fun r hsr pq pq' ↦ (h pq).d_out r hsr pq'⟩⟩

/-! ### Canonical stabilisation isomorphism across pages -/

/-- When `E` stabilises at `pq` from page `s`, this is the canonical isomorphism
`(E.page s h.le).X pq ≅ (E.page r (h.le.trans hsr)).X pq` for `r ≥ s`, built inductively by
composing `HomologicalComplex.XIsoHomologyOfDEqZero` with `E.iso`. -/
noncomputable def StabilizesAt.pageXIso {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) (r : ℤ) (hsr : s ≤ r) :
    (E.page s h.le).X pq ≅ (E.page r (h.le.trans hsr)).X pq :=
  Int.leInduction
    (motive := fun r hsr ↦ (E.page s h.le).X pq ≅ (E.page r (h.le.trans hsr)).X pq)
    (Iso.refl _)
    (fun r hsr e ↦
      e ≪≫ (E.page r (h.le.trans hsr)).XIsoHomologyOfDEqZero pq
        (h.dTo_eq_zero r hsr) (h.dFrom_eq_zero r hsr) ≪≫
        E.iso r (r + 1) pq rfl (h.le.trans hsr))
    r hsr

@[simp]
lemma StabilizesAt.pageXIso_self {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) :
    h.pageXIso s le_rfl = Iso.refl _ :=
  Int.leInduction_base _ _

lemma StabilizesAt.pageXIso_add_one {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) (r : ℤ) (hsr : s ≤ r) :
    h.pageXIso (r + 1) (Int.le_add_one hsr) =
      h.pageXIso r hsr ≪≫
        (E.page r (h.le.trans hsr)).XIsoHomologyOfDEqZero pq
          (h.dTo_eq_zero r hsr) (h.dFrom_eq_zero r hsr) ≪≫
        E.iso r (r + 1) pq rfl (h.le.trans hsr) :=
  Int.leInduction_add_one _ _ r hsr

/-- When `E` stabilises at `pq` from page `s`, the presentation of `(E.page r).X pq` inside
`(E.page s).X pq` is the identity presentation transported along `h.pageXIso r hsr`. -/
lemma StabilizesAt.pagePresentationFrom_eq {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) (r : ℤ) (hsr : s ≤ r) :
    E.pagePresentationFrom pq s h.le r hsr =
      (TauCeti.SubquotientPresentation.refl _).transIso (h.pageXIso r hsr) := by
  induction r, hsr using Int.leInduction with
  | base => simp
  | succ r hsr ih =>
    rw [E.pagePresentationFrom_add_one pq s h.le r hsr, ih, h.pageXIso_add_one r hsr,
      ← (E.page r (h.le.trans hsr)).refl_transIso_eq_homologyPresentation pq
        (h.dTo_eq_zero r hsr) (h.dFrom_eq_zero r hsr),
      ← TauCeti.SubquotientPresentation.trans_transIso,
      TauCeti.SubquotientPresentation.trans_refl,
      TauCeti.SubquotientPresentation.transIso_trans,
      TauCeti.SubquotientPresentation.transIso_trans]

/-- When `E` stabilises at `pq` from page `s`, the presentation of `(E.page r).X pq` inside
`(E.page r₀).X pq` is `(E.pagePresentation pq s h.le)` transported along `h.pageXIso r hsr`. -/
lemma StabilizesAt.pagePresentation_eq {E : SpectralSequence C c r₀} {pq : κ} {s : ℤ}
    (h : E.StabilizesAt pq s) (r : ℤ) (hsr : s ≤ r) :
    E.pagePresentation pq r (h.le.trans hsr) =
      (E.pagePresentation pq s h.le).transIso (h.pageXIso r hsr) := by
  rw [E.pagePresentation_eq_trans pq h.le hsr, h.pagePresentationFrom_eq r hsr,
    ← TauCeti.SubquotientPresentation.trans_transIso,
    TauCeti.SubquotientPresentation.trans_refl]

/-- Compatibility of `StabilizesAt.pageXIso` with composition across `s ≤ r ≤ r'`. -/
@[simp]
lemma StabilizesAt.pageXIso_trans {E : SpectralSequence C c r₀} {pq : κ} {s r r' : ℤ}
    (h : E.StabilizesAt pq s) (hsr : s ≤ r) (hrr' : r ≤ r') :
    h.pageXIso r hsr ≪≫ (h.mono hsr).pageXIso r' hrr' =
      h.pageXIso r' (hsr.trans hrr') := by
  induction r', hrr' using Int.leInduction with
  | base => simp
  | succ r' hrr' ih =>
    rw [(h.mono hsr).pageXIso_add_one r' hrr', h.pageXIso_add_one r' (hsr.trans hrr'),
      ← Iso.trans_assoc, ← Iso.trans_assoc, ih, Iso.trans_assoc]

/-- Naturality of `StabilizesAt.pageXIso` with respect to a morphism `f : E ⟶ E'` of spectral
sequences. -/
@[reassoc]
lemma StabilizesAt.pageXIso_hom_naturality {E E' : SpectralSequence C c r₀} (f : E ⟶ E')
    {pq : κ} {s : ℤ} (h : E.StabilizesAt pq s) (h' : E'.StabilizesAt pq s)
    (r : ℤ) (hsr : s ≤ r) :
    (h.pageXIso r hsr).hom ≫ (f.hom r (h.le.trans hsr)).f pq =
      (f.hom s h.le).f pq ≫ (h'.pageXIso r hsr).hom := by
  induction r, hsr using Int.leInduction with
  | base => simp
  | succ r hsr ih =>
    rw [h.pageXIso_add_one r hsr, h'.pageXIso_add_one r hsr]
    simp only [Iso.trans_hom, Category.assoc]
    rw [← f.comm r (r + 1) pq rfl (h.le.trans hsr),
      ← HomologicalComplex.XIsoHomologyOfDEqZero_hom_naturality_assoc
        (f.hom r (h.le.trans hsr)) pq,
      reassoc_of% ih]

/-! ### Invariance under isomorphisms of spectral sequences -/

/-- Along an isomorphism `e : E ≅ E'` of spectral sequences, a page differential vanishes in `E` if
and only if the corresponding differential vanishes in `E'`. -/
lemma page_d_eq_zero_iff_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E')
    (r : ℤ) (hr : r₀ ≤ r) (i j : κ) :
    (E.page r hr).d i j = 0 ↔ (E'.page r hr).d i j = 0 := by
  let eP : E.page r hr ≅ E'.page r hr := (pageFunctor C c r₀ r hr).mapIso e
  let eXi : (E.page r hr).X i ≅ (E'.page r hr).X i :=
    (HomologicalComplex.eval C (c r) i).mapIso eP
  let eXj : (E.page r hr).X j ≅ (E'.page r hr).X j :=
    (HomologicalComplex.eval C (c r) j).mapIso eP
  constructor
  · intro h
    have hcomm : eXi.hom ≫ (E'.page r hr).d i j = (E.page r hr).d i j ≫ eXj.hom :=
      eP.hom.comm i j
    rw [h, zero_comp] at hcomm
    exact (cancel_epi eXi.hom).mp (by rw [hcomm, comp_zero])
  · intro h
    have hcomm : (E.page r hr).d i j ≫ eXj.hom = eXi.hom ≫ (E'.page r hr).d i j :=
      (eP.hom.comm i j).symm
    rw [h, comp_zero] at hcomm
    exact (cancel_mono eXj.hom).mp (by rw [hcomm, zero_comp])

lemma stabilizesAt_iff_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ) (s : ℤ) :
    E.StabilizesAt pq s ↔ E'.StabilizesAt pq s := by
  refine ⟨fun h ↦ ⟨h.le,
    fun r hsr pq' ↦ (page_d_eq_zero_iff_of_iso e r (h.le.trans hsr) pq pq').mp (h.d_out r hsr pq'),
    fun r hsr pq' ↦ (page_d_eq_zero_iff_of_iso e r (h.le.trans hsr) pq' pq).mp
      (h.d_in r hsr pq')⟩, ?_⟩
  intro h
  exact ⟨h.le,
    fun r hsr pq' ↦
      (page_d_eq_zero_iff_of_iso e r (h.le.trans hsr) pq pq').mpr (h.d_out r hsr pq'),
    fun r hsr pq' ↦
      (page_d_eq_zero_iff_of_iso e r (h.le.trans hsr) pq' pq).mpr (h.d_in r hsr pq')⟩

lemma isRegularAt_iff_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ) :
    E.IsRegularAt pq ↔ E'.IsRegularAt pq := by
  dsimp only [IsRegularAt]
  exact exists_congr fun _ ↦ exists_congr fun hs ↦ forall_congr' fun r ↦ forall_congr' fun hsr ↦
    forall_congr' fun pq' ↦ page_d_eq_zero_iff_of_iso e r (hs.trans hsr) pq pq'

lemma isCoregularAt_iff_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : κ) :
    E.IsCoregularAt pq ↔ E'.IsCoregularAt pq := by
  dsimp only [IsCoregularAt]
  exact exists_congr fun _ ↦ exists_congr fun hs ↦ forall_congr' fun r ↦ forall_congr' fun hsr ↦
    forall_congr' fun pq' ↦ page_d_eq_zero_iff_of_iso e r (hs.trans hsr) pq' pq

lemma degeneratesAt_iff_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (s : ℤ) :
    E.DegeneratesAt s ↔ E'.DegeneratesAt s := by
  simp_rw [degeneratesAt_iff_forall_stabilizesAt, stabilizesAt_iff_of_iso e]

end CategoryTheory.SpectralSequence
