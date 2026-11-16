/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Topology.Maps.Proper.Basic
public import TauCeti.Topology.Maps.Proper.Cover

/-!
# Proper homotopies and proper homotopy equivalences

A homotopy `F : I × X → Y` is *proper* when `IsProperMap F` holds on the entire cylinder `I × X`,
not merely on individual time slices. Because `I` is compact and Hausdorff, properness on the
cylinder implies properness of every time slice (`ContinuousMap.Homotopy.isProperMap_curry`), in
particular of both endpoints, and is preserved under constant homotopies (`refl`), time reversal
(`symm`), concatenation (`trans`), and horizontal composition (`comp`), hence under whiskering on
either side.

A continuous map `f : X → Y` is a *proper homotopy equivalence*
(`ContinuousMap.HasProperHomotopyInverse`) if it is proper and has a proper homotopy inverse
`g : Y → X` for which both homotopies `g ∘ f ≃ id` and `f ∘ g ≃ id` are proper on `I × X` and
`I × Y`. Proper homotopy equivalences contain homeomorphisms
(`Homeomorph.hasProperHomotopyInverse`), are closed under composition
(`ContinuousMap.HasProperHomotopyInverse.comp`), and are invariant under proper homotopy
(`ContinuousMap.HasProperHomotopyInverse.of_homotopy`,
`ContinuousMap.Homotopy.hasProperHomotopyInverse_iff`). No separation or compactness hypothesis on
the spaces is required: horizontal composition uses only that `I` is Hausdorff, and concatenation
uses the finite source-cover criterion on `{t ≤ 1 / 2} ∪ {1 / 2 ≤ t} = I × X`.

## Main declarations

* `ContinuousMap.Homotopy.isProperMap_curry`, `ContinuousMap.Homotopy.isProperMap_left`,
  `ContinuousMap.Homotopy.isProperMap_right`: time slices and endpoints of a proper homotopy are
  proper.
* `ContinuousMap.Homotopy.isProperMap_refl_iff`, `ContinuousMap.Homotopy.isProperMap_symm_iff`,
  `ContinuousMap.Homotopy.isProperMap_trans`, `ContinuousMap.Homotopy.isProperMap_comp`,
  `ContinuousMap.Homotopy.isProperMap_compContinuousMap`: closure of proper homotopies under the
  homotopy operations, together with the corresponding `ContinuousMap.HomotopyRel` lemmas.
* `ContinuousMap.HasProperHomotopyInverse`: proper homotopy equivalences, with `id`, `comp`,
  `of_homotopy`, and `ContinuousMap.Homotopy.hasProperHomotopyInverse_iff`.

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23.
-/

public section

open Filter Set Topology
open scoped unitInterval

namespace ContinuousMap

section Homotopy

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace Homotopy

variable {f f₀ f₁ f₂ : C(X, Y)}

/-- Every time slice `x ↦ F (t, x)` of a proper homotopy `F : I × X → Y` is proper. -/
theorem isProperMap_curry (F : f₀.Homotopy f₁) (hF : IsProperMap F) (t : I) :
    IsProperMap (F.curry t) :=
  hF.comp (IsClosedEmbedding.of_continuous_injective_isClosedMap (.prodMk_right t)
    (Prod.mk_right_injective t) (isClosedMap_prodMk_left t)).isProperMap

/-- The initial map `f₀` of a proper homotopy `F : f₀.Homotopy f₁` is proper. -/
theorem isProperMap_left (F : f₀.Homotopy f₁) (hF : IsProperMap F) : IsProperMap f₀ :=
  F.curry_zero ▸ F.isProperMap_curry hF 0

/-- The terminal map `f₁` of a proper homotopy `F : f₀.Homotopy f₁` is proper. -/
theorem isProperMap_right (F : f₀.Homotopy f₁) (hF : IsProperMap F) : IsProperMap f₁ :=
  F.curry_one ▸ F.isProperMap_curry hF 1

/-- The constant homotopy on `f` is proper if and only if `f` is proper. -/
@[simp]
theorem isProperMap_refl_iff : IsProperMap (Homotopy.refl f) ↔ IsProperMap f :=
  ⟨(Homotopy.refl f).isProperMap_left, fun hf ↦ hf.comp isProperMap_snd_of_compactSpace⟩

/-- The constant homotopy on a proper map is proper. -/
theorem isProperMap_refl (hf : IsProperMap f) : IsProperMap (Homotopy.refl f) :=
  isProperMap_refl_iff.2 hf

/-- Casting the endpoints of a homotopy preserves and reflects properness. -/
@[simp]
theorem isProperMap_cast_iff {g₀ g₁ : C(X, Y)} (F : f₀.Homotopy f₁) (h₀ : f₀ = g₀)
    (h₁ : f₁ = g₁) : IsProperMap (F.cast h₀ h₁) ↔ IsProperMap F :=
  Iff.rfl

/-- Reversing a homotopy preserves and reflects properness. -/
@[simp]
theorem isProperMap_symm_iff (F : f₀.Homotopy f₁) : IsProperMap F.symm ↔ IsProperMap F :=
  (unitInterval.symmHomeomorph.prodCongr (.refl X)).comp_isProperMap_iff' (f := F)

/-- The reverse of a proper homotopy is proper. -/
theorem isProperMap_symm (F : f₀.Homotopy f₁) (hF : IsProperMap F) : IsProperMap F.symm :=
  F.isProperMap_symm_iff.2 hF

private noncomputable def lowerHalfHomeomorph (X : Type*) [TopologicalSpace X] :
    {p : I × X | (p.1 : ℝ) ≤ 1 / 2} ≃ₜ I × X where
  toFun p := (⟨2 * (p.1.1 : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨p.1.1.2.1, p.2⟩⟩,
    p.1.2)
  invFun q := ⟨(⟨(q.1 : ℝ) / 2, ⟨by linarith [q.1.2.1], by linarith [q.1.2.2]⟩⟩, q.2), by
    simp only [mem_ofPred_eq]
    linarith [q.1.2.2]⟩
  left_inv p := by
    ext
    · simp
    · rfl
  right_inv q := by
    ext
    · simp
      ring
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem isProperMap_domRestrict_le_half (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂)
    (hF : IsProperMap F) :
    IsProperMap ({p : I × X | (p.1 : ℝ) ≤ 1 / 2}.domRestrict (F.trans G)) := by
  have hEq : {p : I × X | (p.1 : ℝ) ≤ 1 / 2}.domRestrict (F.trans G) =
      F ∘ lowerHalfHomeomorph X := by
    ext p
    simp only [Function.comp_apply, domRestrict_apply, trans_apply]
    split_ifs with h
    · rfl
    · exact (h p.2).elim
  rw [hEq]
  exact hF.comp (lowerHalfHomeomorph X).isProperMap

/-- **Concatenating two proper homotopies gives a proper homotopy.** -/
theorem isProperMap_trans (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (hF : IsProperMap F)
    (hG : IsProperMap G) : IsProperMap (F.trans G) := by
  let s₁ : Set (I × X) := {p | (p.1 : ℝ) ≤ 1 / 2}
  let s₂ : Set (I × X) := {p | 1 / 2 ≤ (p.1 : ℝ)}
  have hcover : s₁ ∪ s₂ = univ := by
    ext p
    simpa [s₁, s₂] using le_total (p.1 : ℝ) (1 / 2)
  refine (F.trans G).continuous.isProperMap_of_union_eq_univ hcover
    (isProperMap_domRestrict_le_half F G hF) ?_
  -- Time reversal exchanges `s₂` with `s₁` and `F.trans G` with `G.symm.trans F.symm`.
  let swapHalf : s₂ ≃ₜ s₁ :=
    { toFun := fun p ↦ ⟨(σ p.1.1, p.1.2), by
        have hp : (1 / 2 : ℝ) ≤ p.1.1 := p.2
        simp only [s₁, mem_ofPred_eq, unitInterval.coe_symm_eq]
        linarith⟩
      invFun := fun p ↦ ⟨(σ p.1.1, p.1.2), by
        have hp : (p.1.1 : ℝ) ≤ 1 / 2 := p.2
        simp only [s₂, mem_ofPred_eq, unitInterval.coe_symm_eq]
        linarith⟩
      left_inv := fun p ↦ by ext <;> simp
      right_inv := fun p ↦ by ext <;> simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hEq : s₂.domRestrict (F.trans G) =
      s₁.domRestrict (G.symm.trans F.symm) ∘ swapHalf := by
    ext p
    simp [swapHalf, ← symm_trans]
  rw [hEq]
  exact (isProperMap_domRestrict_le_half G.symm F.symm (G.isProperMap_symm hG)).comp
    swapHalf.isProperMap

/-- **Horizontal composition of proper homotopies is proper.** -/
theorem isProperMap_comp {g₀ g₁ : C(Y, Z)} (G : g₀.Homotopy g₁) (F : f₀.Homotopy f₁)
    (hG : IsProperMap G) (hF : IsProperMap F) : IsProperMap (G.comp F) := by
  refine isProperMap_iff_ultrafilter.2 ⟨(G.comp F).continuous, fun 𝒰 z hz ↦ ?_⟩
  have hmap : Tendsto G (𝒰.map fun p : I × X ↦ (p.1, F p)) (𝓝 z) := by
    rwa [Ultrafilter.coe_map, tendsto_map'_iff]
  obtain ⟨⟨t₀, y₀⟩, hGz, hty⟩ := hG.ultrafilter_le_nhds_of_tendsto hmap
  rw [Ultrafilter.coe_map, nhds_prod_eq, le_prod, tendsto_map'_iff, tendsto_map'_iff] at hty
  obtain ⟨⟨t₁, x₀⟩, hFy, htx⟩ := hF.ultrafilter_le_nhds_of_tendsto hty.2
  have ht : t₁ = t₀ := tendsto_nhds_unique ((continuous_fst.tendsto (t₁, x₀)).mono_left htx) hty.1
  subst ht
  exact ⟨(t₁, x₀), by simpa [hFy] using hGz, htx⟩

/-- Right whiskering a proper homotopy by a proper map gives a proper homotopy. -/
theorem isProperMap_compContinuousMap {g₀ g₁ : C(Y, Z)} (G : g₀.Homotopy g₁) {f : C(X, Y)}
    (hG : IsProperMap G) (hf : IsProperMap f) : IsProperMap (G.compContinuousMap f) :=
  G.isProperMap_comp (.refl f) hG (isProperMap_refl hf)

end Homotopy

namespace HomotopyRel

variable {f f₀ f₁ f₂ : C(X, Y)} {S : Set X}

/-- The constant relative homotopy on `f` is proper if and only if `f` is proper. -/
@[simp]
theorem isProperMap_refl_iff (f : C(X, Y)) (S : Set X) :
    IsProperMap (HomotopyRel.refl f S) ↔ IsProperMap f :=
  Homotopy.isProperMap_refl_iff

/-- The constant relative homotopy on a proper map is proper. -/
theorem isProperMap_refl (hf : IsProperMap f) (S : Set X) :
    IsProperMap (HomotopyRel.refl f S) :=
  Homotopy.isProperMap_refl hf

/-- Casting the endpoints of a relative homotopy preserves and reflects properness. -/
@[simp]
theorem isProperMap_cast_iff {g₀ g₁ : C(X, Y)} (F : f₀.HomotopyRel f₁ S) (h₀ : f₀ = g₀)
    (h₁ : f₁ = g₁) : IsProperMap (F.cast h₀ h₁) ↔ IsProperMap F :=
  Iff.rfl

/-- Reversing a relative homotopy preserves and reflects properness. -/
@[simp]
theorem isProperMap_symm_iff (F : f₀.HomotopyRel f₁ S) :
    IsProperMap F.symm ↔ IsProperMap F :=
  F.toHomotopy.isProperMap_symm_iff

/-- The reverse of a proper relative homotopy is proper. -/
theorem isProperMap_symm (F : f₀.HomotopyRel f₁ S) (hF : IsProperMap F) :
    IsProperMap F.symm :=
  F.toHomotopy.isProperMap_symm hF

/-- Concatenating two proper relative homotopies gives a proper relative homotopy. -/
theorem isProperMap_trans (F : f₀.HomotopyRel f₁ S) (G : f₁.HomotopyRel f₂ S)
    (hF : IsProperMap F) (hG : IsProperMap G) : IsProperMap (F.trans G) :=
  F.toHomotopy.isProperMap_trans G.toHomotopy hF hG

/-- Postcomposing a proper relative homotopy with a proper map gives a proper relative homotopy. -/
theorem isProperMap_compContinuousMap (F : f₀.HomotopyRel f₁ S) {g : C(Y, Z)}
    (hF : IsProperMap F) (hg : IsProperMap g) : IsProperMap (F.compContinuousMap g) :=
  (Homotopy.refl g).isProperMap_comp F.toHomotopy (Homotopy.isProperMap_refl hg) hF

end HomotopyRel

end Homotopy

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A continuous map `f : X → Y` is a **proper homotopy equivalence** if it is proper and has a
proper homotopy inverse `g`, with both homotopies `g ∘ f ≃ id` and `f ∘ g ≃ id` proper as maps
`I × X → X` and `I × Y → Y`. -/
def HasProperHomotopyInverse (f : C(X, Y)) : Prop :=
  IsProperMap f ∧ ∃ g : C(Y, X), IsProperMap g ∧
    ∃ H : Homotopy (g.comp f) (ContinuousMap.id X), ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y),
      IsProperMap H ∧ IsProperMap H'

namespace HasProperHomotopyInverse

/-- A proper map with a proper inverse `g` up to proper homotopies `g ∘ f ≃ id` and
`f ∘ g ≃ id` is a proper homotopy equivalence. -/
theorem intro {f : C(X, Y)} (hf : IsProperMap f) (g : C(Y, X)) (hg : IsProperMap g)
    (H : Homotopy (g.comp f) (ContinuousMap.id X)) (H' : Homotopy (f.comp g) (ContinuousMap.id Y))
    (hH : IsProperMap H) (hH' : IsProperMap H') : f.HasProperHomotopyInverse :=
  ⟨hf, g, hg, H, H', hH, hH'⟩

/-- A proper homotopy equivalence is a proper map. -/
theorem isProperMap {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) : IsProperMap f :=
  hf.1

/-- A proper homotopy equivalence has a proper homotopy inverse `g`, with proper homotopies
`g ∘ f ≃ id` and `f ∘ g ≃ id`. -/
theorem exists_inverse {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    ∃ g : C(Y, X), IsProperMap g ∧
      ∃ H : Homotopy (g.comp f) (ContinuousMap.id X),
        ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y), IsProperMap H ∧ IsProperMap H' :=
  hf.2

/-- Every proper homotopy equivalence admits a proper homotopy inverse which is itself a proper
homotopy equivalence. -/
theorem exists_inverse_hasProperHomotopyInverse {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    ∃ g : C(Y, X), g.HasProperHomotopyInverse ∧
      ∃ H : Homotopy (g.comp f) (ContinuousMap.id X),
        ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y), IsProperMap H ∧ IsProperMap H' := by
  obtain ⟨g, hg, H, H', hH, hH'⟩ := hf.exists_inverse
  exact ⟨g, .intro hg f hf.isProperMap H' H hH' hH, H, H', hH, hH'⟩

/-- A proper homotopy equivalence `f` is a homotopy equivalence: forgetting properness gives a
homotopy equivalence whose forward map is `f`. -/
theorem exists_homotopyEquiv {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    ∃ e : X ≃ₕ Y, (e : X → Y) = f := by
  obtain ⟨g, -, H, H', -, -⟩ := hf.exists_inverse
  exact ⟨⟨f, g, ⟨H⟩, ⟨H'⟩⟩, rfl⟩

/-- The identity map is a proper homotopy equivalence. -/
protected theorem id : (ContinuousMap.id X).HasProperHomotopyInverse :=
  .intro isProperMap_id (.id X) isProperMap_id (.refl _) (.refl _)
    (Homotopy.isProperMap_refl isProperMap_id) (Homotopy.isProperMap_refl isProperMap_id)

private noncomputable def compCancelHomotopy {f : C(X, Y)} {g : C(Y, Z)} {f' : C(Y, X)}
    {g' : C(Z, Y)} (Hg : (g'.comp g).Homotopy (.id Y)) (Hf : (f'.comp f).Homotopy (.id X)) :
    ((f'.comp g').comp (g.comp f)).Homotopy (.id X) :=
  ((((Homotopy.refl f').comp Hg).compContinuousMap f).cast (by ext; rfl) (by ext; rfl)).trans Hf

private theorem isProperMap_compCancelHomotopy {f : C(X, Y)} {g : C(Y, Z)} {f' : C(Y, X)}
    {g' : C(Z, Y)} (hf : IsProperMap f) (hf' : IsProperMap f')
    (Hg : (g'.comp g).Homotopy (.id Y)) (Hf : (f'.comp f).Homotopy (.id X))
    (hHg : IsProperMap Hg) (hHf : IsProperMap Hf) :
    IsProperMap (compCancelHomotopy Hg Hf) :=
  Homotopy.isProperMap_trans _ Hf
    (((Homotopy.refl f').comp Hg).isProperMap_compContinuousMap
      ((Homotopy.refl f').isProperMap_comp Hg (Homotopy.isProperMap_refl hf') hHg) hf)
    hHf

/-- **Proper homotopy equivalences are closed under composition.** -/
theorem comp {f : C(X, Y)} {g : C(Y, Z)} (hg : g.HasProperHomotopyInverse)
    (hf : f.HasProperHomotopyInverse) : (g.comp f).HasProperHomotopyInverse := by
  obtain ⟨f', hf', Hf, Hf', hHf, hHf'⟩ := hf.exists_inverse
  obtain ⟨g', hg', Hg, Hg', hHg, hHg'⟩ := hg.exists_inverse
  exact .intro (hg.isProperMap.comp hf.isProperMap) (f'.comp g') (hf'.comp hg')
    (compCancelHomotopy Hg Hf) (compCancelHomotopy Hf' Hg')
    (isProperMap_compCancelHomotopy hf.isProperMap hf' Hg Hf hHg hHf)
    (isProperMap_compCancelHomotopy hg' hg.isProperMap Hf' Hg' hHf' hHg')

/-- **Proper homotopy transport.** Any map properly homotopic to a proper homotopy equivalence is
itself a proper homotopy equivalence, with the same proper homotopy inverse. -/
theorem of_homotopy {f₀ f₁ : C(X, Y)} (hf₀ : f₀.HasProperHomotopyInverse) {F : f₀.Homotopy f₁}
    (hF : IsProperMap F) : f₁.HasProperHomotopyInverse := by
  obtain ⟨g, hg, H, H', hH, hH'⟩ := hf₀.exists_inverse
  have hFsymm : IsProperMap F.symm := F.isProperMap_symm hF
  exact .intro (F.isProperMap_right hF) g hg
    (((Homotopy.refl g).comp F.symm).trans H)
    ((F.symm.compContinuousMap g).trans H')
    (Homotopy.isProperMap_trans _ H
      ((Homotopy.refl g).isProperMap_comp F.symm (Homotopy.isProperMap_refl hg) hFsymm) hH)
    (Homotopy.isProperMap_trans _ H'
      (F.symm.isProperMap_compContinuousMap hFsymm hg) hH')

end HasProperHomotopyInverse

/-- Being a proper homotopy equivalence is invariant under proper homotopy. -/
theorem Homotopy.hasProperHomotopyInverse_iff {f₀ f₁ : C(X, Y)} (F : f₀.Homotopy f₁)
    (hF : IsProperMap F) :
    f₀.HasProperHomotopyInverse ↔ f₁.HasProperHomotopyInverse :=
  ⟨fun h ↦ h.of_homotopy hF, fun h ↦ h.of_homotopy (F.isProperMap_symm hF)⟩

end ContinuousMap

/-- A homeomorphism is a proper homotopy equivalence, with constant homotopies: these are the
projections `I × X → X` and `I × Y → Y`, which are proper as `I` is compact. -/
theorem Homeomorph.hasProperHomotopyInverse {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : (e : C(X, Y)).HasProperHomotopyInverse := by
  refine .intro e.isProperMap e.symm e.symm.isProperMap
    ((ContinuousMap.Homotopy.refl _).cast rfl e.symm_comp_toContinuousMap)
    ((ContinuousMap.Homotopy.refl _).cast rfl e.toContinuousMap_comp_symm) ?_ ?_ <;>
  · convert isProperMap_snd_of_compactSpace (X := I) using 1
    ext x
    simp
