/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic
public import TauCeti.Topology.Homotopy.Proper

/-!
# The proper homotopy extension property

A subset `A` of a topological space `X` has the *proper homotopy extension property*
(`TauCeti.HasProperHomotopyExtensionProperty`) when every jointly proper homotopy `H : I × A → Y`
whose initial slice agrees on `A` with a proper map `f : X → Y` extends to a jointly proper
homotopy `G : I × X → Y` starting at `f`.

Although `HasProperHomotopyExtensionProperty` quantifies over target spaces `Y` in the universe of
`X`, properness makes `range f ∪ range H` closed in `Y`, so factoring through its quotient topology
on `X ⊕ (I × A)` lifts proper homotopy extension to targets in *any* universe without assuming `A`
closed (`TauCeti.HasProperHomotopyExtensionProperty.exists_extension`). Consequently, homeomorphism
invariance (`TauCeti.HasProperHomotopyExtensionProperty.image`) and composition along closed
embeddings (`TauCeti.HasProperHomotopyExtensionProperty.image_of_isClosedEmbedding`) also hold
across arbitrary universes without closedness hypotheses on `A`.

On the geometric side, a subset `A ⊆ X` is closed and has the proper homotopy extension property
if and only if `I × X` admits a *proper* retraction onto `{0} × X ∪ I × A`
(`TauCeti.isClosed_and_hasProperHomotopyExtensionProperty_iff_exists_retraction`,
`TauCeti.hasProperHomotopyExtensionProperty_iff_exists_retraction`): properness of the retraction
forces its range `{0} × X ∪ I × A` (and hence `A`) to be closed (`TauCeti.isClosed_of_retraction`).
For closed `A`:

* `HasProperHomotopyExtensionProperty A` implies the ordinary `HasHomotopyExtensionProperty A`
  (`TauCeti.HasProperHomotopyExtensionProperty.hasHomotopyExtensionProperty`), so closed subsets
  such as `{0} ∪ {1 / (n + 1) | n : ℕ} ⊆ I` that lack a cylinder retraction also fail the proper
  property;
* when `X` is compact and Hausdorff, `HasProperHomotopyExtensionProperty A` and
  `HasHomotopyExtensionProperty A` coincide on closed subsets
  (`TauCeti.hasProperHomotopyExtensionProperty_iff_hasHomotopyExtensionProperty`).

Unlike `HasHomotopyExtensionProperty`, which forces `A` to be closed in a Hausdorff space,
`HasProperHomotopyExtensionProperty A` holds *vacuously* for every non-closed subset `A` of a
Hausdorff space (`TauCeti.hasProperHomotopyExtensionProperty_of_not_isClosed`): at a boundary point
`x₀ ∈ closure A \ A`, no proper map `H : I × A → Y` can agree on `{0} × A` with a continuous map
on `X`. Closedness of `A` is therefore genuinely required whenever a cylinder retraction or
ordinary homotopy extension is extracted.

## Main declarations

* `TauCeti.HasProperHomotopyExtensionProperty`, `TauCeti.hasProperHomotopyExtensionProperty_iff`,
  `TauCeti.HasProperHomotopyExtensionProperty.exists_extension`,
  `TauCeti.HasProperHomotopyExtensionProperty.exists_homotopy_of_restrict`: the proper homotopy
  extension property and its universe-polymorphic elimination forms.
* `TauCeti.hasProperHomotopyExtensionProperty_empty`,
  `TauCeti.hasProperHomotopyExtensionProperty_univ`, `IsClopen.hasProperHomotopyExtensionProperty`:
  basic subsets with the proper homotopy extension property.
* `TauCeti.isClosed_of_retraction`,
  `TauCeti.isClosed_and_hasProperHomotopyExtensionProperty_iff_exists_retraction`,
  `TauCeti.hasProperHomotopyExtensionProperty_iff_exists_retraction`: **proper cylinder-retraction
  characterizations.**
* `TauCeti.HasProperHomotopyExtensionProperty.hasHomotopyExtensionProperty`,
  `TauCeti.hasProperHomotopyExtensionProperty_iff_hasHomotopyExtensionProperty`: comparison with
  `TauCeti.HasHomotopyExtensionProperty`.
* `TauCeti.hasProperHomotopyExtensionProperty_of_not_isClosed`: vacuous satisfaction on non-closed
  subsets of Hausdorff spaces.
* `TauCeti.HasProperHomotopyExtensionProperty.image`,
  `TauCeti.HasProperHomotopyExtensionProperty.image_of_isClosedEmbedding`: invariance under
  homeomorphisms and composition along closed embeddings across arbitrary universes.

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23, Theorem 1.6.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0,
  "The Homotopy Extension Property".
-/

public section

namespace TauCeti

open Filter Set Topology unitInterval

universe u u' v

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- A subset `A` of `X` has the **proper homotopy extension property** when every jointly proper
homotopy `H : I × A → Y` whose initial map agrees on `A` with a proper map `f : X → Y` extends to a
jointly proper homotopy `G : I × X → Y` starting at `f`.

Targets `Y` are quantified over the universe of `X`;
`TauCeti.HasProperHomotopyExtensionProperty.exists_extension` lifts this to targets in an arbitrary
universe with no extra hypothesis on `A`. -/
def HasProperHomotopyExtensionProperty (A : Set X) : Prop :=
  ∀ {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)), IsProperMap f →
    ∀ (H : C(I × A, Y)), IsProperMap H → (∀ a : A, H (0, a) = f a) →
      ∃ G : C(I × X, Y), IsProperMap G ∧
        (∀ x : X, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a)

/-- Unfolding of `TauCeti.HasProperHomotopyExtensionProperty`. -/
theorem hasProperHomotopyExtensionProperty_iff :
    HasProperHomotopyExtensionProperty A ↔
      ∀ {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)), IsProperMap f →
        ∀ (H : C(I × A, Y)), IsProperMap H → (∀ a : A, H (0, a) = f a) →
          ∃ G : C(I × X, Y), IsProperMap G ∧
            (∀ x : X, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) :=
  Iff.rfl

/-- `TauCeti.HasProperHomotopyExtensionProperty` extends proper homotopies into target spaces `Y`
in any universe, with no closedness hypothesis on `A`. -/
theorem HasProperHomotopyExtensionProperty.exists_extension
    (h : HasProperHomotopyExtensionProperty A) {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (hf : IsProperMap f) (H : C(I × A, Y)) (hH : IsProperMap H)
    (h0 : ∀ a : A, H (0, a) = f a) :
    ∃ G : C(I × X, Y), IsProperMap G ∧
      (∀ x : X, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) := by
  -- Factor `f` and `H` through a space in `Type u` closedly embedded onto `range f ∪ range H`.
  let q : X ⊕ (I × A) → Y := Sum.elim f H
  let S : Setoid (X ⊕ (I × A)) :=
    ⟨fun s₁ s₂ ↦ q s₁ = q s₂, fun _ ↦ rfl, fun hq ↦ hq.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩
  let j : Quotient S → Y := Quotient.lift q fun _ _ hq ↦ hq
  let : TopologicalSpace (Quotient S) := TopologicalSpace.induced j ‹TopologicalSpace Y›
  have hj_inj : Function.Injective j := by
    intro z₁ z₂ hz
    obtain ⟨s₁, rfl⟩ := Quotient.exists_rep z₁
    obtain ⟨s₂, rfl⟩ := Quotient.exists_rep z₂
    exact Quotient.sound hz
  have hj_emb : IsEmbedding j := ⟨⟨rfl⟩, hj_inj⟩
  have hrange : range j = range f ∪ range H := by
    ext y
    refine ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨x | p, rfl⟩ := Quotient.exists_rep z
      · exact Or.inl ⟨x, rfl⟩
      · exact Or.inr ⟨p, rfl⟩
    · rintro (⟨x, rfl⟩ | ⟨p, rfl⟩)
      · exact ⟨Quotient.mk S (Sum.inl x), rfl⟩
      · exact ⟨Quotient.mk S (Sum.inr p), rfl⟩
  have hj : IsClosedEmbedding j := ⟨hj_emb, hrange ▸ hf.isClosed_range.union hH.isClosed_range⟩
  let f₀ : C(X, Quotient S) :=
    ⟨fun x ↦ Quotient.mk S (Sum.inl x), hj_emb.continuous_iff.2 f.continuous⟩
  let H₀ : C(I × A, Quotient S) :=
    ⟨fun p ↦ Quotient.mk S (Sum.inr p), hj_emb.continuous_iff.2 H.continuous⟩
  have hf₀ : IsProperMap f₀ := isProperMap_of_comp_of_inj f₀.continuous hj.continuous hf hj_inj
  have hH₀ : IsProperMap H₀ := isProperMap_of_comp_of_inj H₀.continuous hj.continuous hH hj_inj
  obtain ⟨G₀, hG₀, hG₀_zero, hG₀_mem⟩ := h f₀ hf₀ H₀ hH₀ fun a ↦ hj_inj (h0 a)
  exact ⟨⟨fun p ↦ j (G₀ p), hj.continuous.comp G₀.continuous⟩, hj.isProperMap.comp hG₀,
    fun x ↦ congrArg j (hG₀_zero x), fun t a ↦ congrArg j (hG₀_mem t a)⟩

/-- Bundled-homotopy form of `exists_extension`: a proper homotopy starting at `f.restrict A`, for
a proper map `f : C(X, Y)` into a space in any universe, extends to a proper homotopy
`G : f.Homotopy f'` whose terminal map `f'` is also proper. -/
theorem HasProperHomotopyExtensionProperty.exists_homotopy_of_restrict
    (h : HasProperHomotopyExtensionProperty A) {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (hf : IsProperMap f) {g : C(A, Y)} (H : (f.restrict A).Homotopy g)
    (hH : IsProperMap H) :
    ∃ (f' : C(X, Y)) (G : f.Homotopy f'), IsProperMap f' ∧ IsProperMap G ∧
      ∀ (t : I) (a : A), G (t, (a : X)) = H (t, a) := by
  obtain ⟨G, hG, hG₀, hG₁⟩ :=
    h.exists_extension f hf H.toContinuousMap hH fun a ↦ H.apply_zero a
  let G' : f.Homotopy ⟨fun x ↦ G (1, x), by fun_prop⟩ :=
    { toContinuousMap := G, map_zero_left := hG₀, map_one_left := fun _ ↦ rfl }
  exact ⟨_, G', G'.isProperMap_right hG, hG, hG₁⟩

/-- The empty subset has the proper homotopy extension property. -/
@[simp]
theorem hasProperHomotopyExtensionProperty_empty :
    HasProperHomotopyExtensionProperty (∅ : Set X) :=
  fun f hf _ _ _ ↦ ⟨f.comp ContinuousMap.snd, hf.comp isProperMap_snd_of_compactSpace,
    fun _ ↦ rfl, fun _ a ↦ a.2.elim⟩

/-- The whole space `univ` has the proper homotopy extension property. -/
@[simp]
theorem hasProperHomotopyExtensionProperty_univ :
    HasProperHomotopyExtensionProperty (univ : Set X) := by
  intro Y _ f _ H hH h0
  let e : I × X ≃ₜ I × (univ : Set X) :=
    (Homeomorph.refl I).prodCongr (Homeomorph.Set.univ X).symm
  refine ⟨⟨fun p ↦ H (e p), by fun_prop⟩, hH.comp e.isProperMap, fun x ↦ ?_, fun _ _ ↦ rfl⟩
  exact h0 ⟨x, mem_univ x⟩

section Retraction

open scoped Classical in
/-- The map `{0} × X ∪ I × A → Y` glued from `f` on `{0} × X` and `H` on `I × A`. -/
private noncomputable def cylinderGlue {Y : Type v} (f : X → Y) (H : I × A → Y)
    (z : cylinderExtensionDomain A) : Y :=
  if h : z.1.2 ∈ A then H (z.1.1, ⟨z.1.2, h⟩) else f z.1.2

private theorem isProperMap_cylinderGlue {Y : Type v} [TopologicalSpace Y] (hA : IsClosed A)
    {f : C(X, Y)} (hf : IsProperMap f) {H : C(I × A, Y)} (hH : IsProperMap H)
    (h0 : ∀ a : A, H (0, a) = f a) :
    IsProperMap (cylinderGlue f H) := by
  let C₁ : Set (cylinderExtensionDomain A) := {z | z.1.1 = 0}
  let C₂ : Set (cylinderExtensionDomain A) := {z | z.1.2 ∈ A}
  have hC₁ : IsClosed C₁ := isClosed_eq (by fun_prop) continuous_const
  have hC₂ : IsClosed C₂ := hA.preimage (by fun_prop)
  have hcover : C₁ ∪ C₂ = univ := eq_univ_of_forall fun z ↦ mem_cylinderExtensionDomain_iff.1 z.2
  rw [isProperMap_iff_domRestrict_of_isClosed_union hC₁ hC₂ hcover]
  -- `C₁` is homeomorphic to `X` and `C₂` is homeomorphic to `I × A`.
  let e₁ : C₁ ≃ₜ X :=
    { toFun := fun z ↦ z.1.1.2
      invFun := fun x ↦ ⟨⟨(0, x), zero_mem_cylinderExtensionDomain x⟩, rfl⟩
      left_inv := fun z ↦ Subtype.ext <| Subtype.ext <| Prod.ext z.2.symm rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let e₂ : C₂ ≃ₜ I × A :=
    { toFun := fun z ↦ (z.1.1.1, ⟨z.1.1.2, z.2⟩)
      invFun := fun q ↦ ⟨⟨(q.1, q.2.1), mem_cylinderExtensionDomain_of_mem q.2.2⟩, q.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨?_, ?_⟩
  · have hEq₁ : C₁.domRestrict (cylinderGlue f H) = f ∘ e₁ := by
      funext z
      have hz0 : z.1.1.1 = 0 := z.2
      by_cases hzA : z.1.1.2 ∈ A <;> simp [cylinderGlue, e₁, hz0, hzA, h0]
    exact hEq₁ ▸ hf.comp e₁.isProperMap
  · have hEq₂ : C₂.domRestrict (cylinderGlue f H) = H ∘ e₂ := by
      funext z
      have hzA : z.1.1.2 ∈ A := z.2
      simp [cylinderGlue, e₂, hzA]
    exact hEq₂ ▸ hH.comp e₂.isProperMap

/-- If `I × X` admits a proper retraction onto `{0} × X ∪ I × A`, then `A` is closed in `X`. -/
theorem isClosed_of_retraction {r : C(I × X, I × X)} (hr_prop : IsProperMap r)
    (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
    (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p) : IsClosed A := by
  have hrange : range r = cylinderExtensionDomain A :=
    Subset.antisymm (range_subset_iff.2 hr) fun p hp ↦ ⟨p, hr' p hp⟩
  have hcyl : IsClosed (cylinderExtensionDomain A) := hrange ▸ hr_prop.isClosed_range
  have hpre : (fun x : X ↦ ((1 : I), x)) ⁻¹' cylinderExtensionDomain A = A :=
    ext fun x ↦ by simp [mem_cylinderExtensionDomain_iff]
  exact hpre ▸ hcyl.preimage (by fun_prop)

/-- A proper retraction of `I × X` onto `{0} × X ∪ I × A` solves every proper homotopy extension
problem for `A`, with values in a space in any universe. Closedness of `A` follows automatically
from properness of `r`. -/
theorem exists_proper_homotopy_extension_of_retraction {Y : Type v} [TopologicalSpace Y]
    {r : C(I × X, I × X)} (hr_prop : IsProperMap r)
    (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
    (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p)
    (f : C(X, Y)) (hf : IsProperMap f) (H : C(I × A, Y)) (hH : IsProperMap H)
    (h0 : ∀ a : A, H (0, a) = f a) :
    ∃ G : C(I × X, Y), IsProperMap G ∧
      (∀ x : X, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) := by
  have hA : IsClosed A := isClosed_of_retraction hr_prop hr hr'
  let r₀ : C(I × X, cylinderExtensionDomain A) := ⟨fun p ↦ ⟨r p, hr p⟩, r.continuous.subtype_mk hr⟩
  have hr₀ : IsProperMap r₀ :=
    isProperMap_of_comp_of_inj r₀.continuous continuous_subtype_val hr_prop Subtype.val_injective
  have hg : IsProperMap (cylinderGlue f H) := isProperMap_cylinderGlue hA hf hH h0
  let gMap : C(cylinderExtensionDomain A, Y) := ⟨cylinderGlue f H, hg.continuous⟩
  refine ⟨gMap.comp r₀, hg.comp hr₀, fun x ↦ ?_, fun t a ↦ ?_⟩
  · by_cases hx : x ∈ A <;>
      simp [gMap, r₀, cylinderGlue, hr' _ (zero_mem_cylinderExtensionDomain x), hx, h0]
  · simp [gMap, r₀, cylinderGlue, hr' _ (mem_cylinderExtensionDomain_of_mem a.2)]

/-- A subset onto whose cylinder extension domain `I × X` properly retracts has the proper homotopy
extension property. -/
theorem hasProperHomotopyExtensionProperty_of_retraction {r : C(I × X, I × X)}
    (hr_prop : IsProperMap r) (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
    (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p) :
    HasProperHomotopyExtensionProperty A := by
  intro Y _ f hf H hH h0
  exact exists_proper_homotopy_extension_of_retraction hr_prop hr hr' f hf H hH h0

/-- Every clopen subset has the proper homotopy extension property. -/
theorem _root_.IsClopen.hasProperHomotopyExtensionProperty (hA : IsClopen A) :
    HasProperHomotopyExtensionProperty A := by
  classical
  let s₁ : Set (I × X) := {p | p.2 ∈ A}
  let s₂ : Set (I × X) := {p | p.2 ∈ Aᶜ}
  have hs₁ : IsClopen s₁ := hA.preimage continuous_snd
  have hs₂ : IsClosed s₂ := hA.compl.isClosed.preimage continuous_snd
  have hr_cont : Continuous fun p : I × X ↦ if p.2 ∈ A then p else ((0 : I), p.2) :=
    Continuous.if (by simp [s₁, hs₁.frontier_eq]) continuous_id (by fun_prop)
  let r : C(I × X, I × X) := ⟨fun p : I × X ↦ if p.2 ∈ A then p else ((0 : I), p.2), hr_cont⟩
  have hr_prop : IsProperMap r := by
    have hcover : s₁ ∪ s₂ = univ := eq_univ_of_forall fun p ↦ em (p.2 ∈ A)
    rw [isProperMap_iff_domRestrict_of_isClosed_union hs₁.isClosed hs₂ hcover]
    refine ⟨?_, ?_⟩
    · have hEq₁ : s₁.domRestrict r = Subtype.val :=
        funext fun p ↦ ite_eq_left_iff.2 fun h ↦ (h p.2).elim
      exact hEq₁ ▸ hs₁.isClosed.isProperMap_subtypeVal
    · let e₂ : s₂ ≃ₜ I × (Aᶜ : Set X) :=
        { toFun := fun p ↦ (p.1.1, ⟨p.1.2, p.2⟩)
          invFun := fun q ↦ ⟨(q.1, q.2.1), q.2.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop }
      have hzero : IsProperMap (fun x : X ↦ ((0 : I), x)) :=
        (IsClosedEmbedding.of_continuous_injective_isClosedMap (.prodMk_right (0 : I))
          (Prod.mk_right_injective _) (isClosedMap_prodMk_left _)).isProperMap
      have hEq₂ : s₂.domRestrict r =
          (fun x : X ↦ ((0 : I), x)) ∘ Subtype.val ∘ (Prod.snd : I × (Aᶜ : Set X) → (Aᶜ : Set X)) ∘
            e₂ :=
        funext fun p ↦ ite_eq_right_iff.2 fun h ↦ (p.2 h).elim
      rw [hEq₂]
      exact hzero.comp (hA.compl.isClosed.isProperMap_subtypeVal.comp
        (isProperMap_snd_of_compactSpace.comp e₂.isProperMap))
  apply hasProperHomotopyExtensionProperty_of_retraction (r := r) hr_prop
  · intro p
    by_cases h : p.2 ∈ A <;> simp [r, h, mem_cylinderExtensionDomain_iff]
  · rintro ⟨t, x⟩ hp
    obtain rfl | hx : t = 0 ∨ x ∈ A := mem_cylinderExtensionDomain_iff.1 hp
    · by_cases h : x ∈ A <;> simp [r, h]
    · simp [r, hx]

/-- A closed subset `A` with the proper homotopy extension property admits a proper retraction of
`I × X` onto `{0} × X ∪ I × A`. -/
theorem HasProperHomotopyExtensionProperty.exists_retraction
    (h : HasProperHomotopyExtensionProperty A) (hA : IsClosed A) :
    ∃ r : C(I × X, I × X), IsProperMap r ∧ (∀ p, r p ∈ cylinderExtensionDomain A) ∧
      ∀ p ∈ cylinderExtensionDomain A, r p = p := by
  let f : C(X, cylinderExtensionDomain A) :=
    ⟨fun x ↦ ⟨((0 : I), x), zero_mem_cylinderExtensionDomain x⟩, by fun_prop⟩
  let H : C(I × A, cylinderExtensionDomain A) :=
    ⟨fun q ↦ ⟨(q.1, q.2.1), mem_cylinderExtensionDomain_of_mem q.2.2⟩, by fun_prop⟩
  have hzero : IsProperMap (fun x : X ↦ ((0 : I), x)) :=
    (IsClosedEmbedding.of_continuous_injective_isClosedMap (.prodMk_right (0 : I))
      (Prod.mk_right_injective _) (isClosedMap_prodMk_left _)).isProperMap
  have hf : IsProperMap f :=
    isProperMap_of_comp_of_inj f.continuous continuous_subtype_val hzero Subtype.val_injective
  have hH : IsProperMap H :=
    isProperMap_of_comp_of_inj H.continuous continuous_subtype_val
      (isProperMap_id.prodMap hA.isProperMap_subtypeVal) Subtype.val_injective
  obtain ⟨G, hG, hG₀, hG₁⟩ := h.exists_extension f hf H hH fun _ ↦ rfl
  refine ⟨(ContinuousMap.subtypeVal _).comp G,
    (isClosed_cylinderExtensionDomain hA).isProperMap_subtypeVal.comp hG, fun p ↦ (G p).2, ?_⟩
  intro ⟨t, x⟩ hp
  rcases mem_cylinderExtensionDomain_iff.1 hp with rfl | hx
  · exact congrArg Subtype.val (hG₀ x)
  · exact congrArg Subtype.val (hG₁ t ⟨x, hx⟩)

/-- **A subset is closed and has the proper homotopy extension property if and only if
`{0} × X ∪ I × A` is a proper retract of `I × X`.** -/
theorem isClosed_and_hasProperHomotopyExtensionProperty_iff_exists_retraction :
    (IsClosed A ∧ HasProperHomotopyExtensionProperty A) ↔
      ∃ r : C(I × X, I × X), IsProperMap r ∧ (∀ p, r p ∈ cylinderExtensionDomain A) ∧
        ∀ p ∈ cylinderExtensionDomain A, r p = p :=
  ⟨fun ⟨hA, h⟩ ↦ h.exists_retraction hA,
    fun ⟨_, hr_prop, hr, hr'⟩ ↦
      ⟨isClosed_of_retraction hr_prop hr hr',
        hasProperHomotopyExtensionProperty_of_retraction hr_prop hr hr'⟩⟩

/-- **A closed subset has the proper homotopy extension property if and only if `{0} × X ∪ I × A`
is a proper retract of `I × X`.** -/
theorem hasProperHomotopyExtensionProperty_iff_exists_retraction (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty A ↔
      ∃ r : C(I × X, I × X), IsProperMap r ∧ (∀ p, r p ∈ cylinderExtensionDomain A) ∧
        ∀ p ∈ cylinderExtensionDomain A, r p = p :=
  ⟨fun h ↦ h.exists_retraction hA,
    fun ⟨_, hr_prop, hr, hr'⟩ ↦ hasProperHomotopyExtensionProperty_of_retraction hr_prop hr hr'⟩

/-- A closed subset with the proper homotopy extension property also has the ordinary homotopy
extension property. -/
theorem HasProperHomotopyExtensionProperty.hasHomotopyExtensionProperty
    (h : HasProperHomotopyExtensionProperty A) (hA : IsClosed A) :
    HasHomotopyExtensionProperty A := by
  obtain ⟨r, -, hr, hr'⟩ := h.exists_retraction hA
  exact hasHomotopyExtensionProperty_of_retraction hA hr hr'

/-- On a compact Hausdorff space, a closed subset has the proper homotopy extension property if
and only if it has the ordinary homotopy extension property. -/
theorem hasProperHomotopyExtensionProperty_iff_hasHomotopyExtensionProperty
    [CompactSpace X] [T2Space X] (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty A ↔ HasHomotopyExtensionProperty A := by
  refine ⟨fun h ↦ h.hasHomotopyExtensionProperty hA, fun h ↦ ?_⟩
  obtain ⟨r, hr, hr'⟩ := h.exists_retraction
  exact hasProperHomotopyExtensionProperty_of_retraction r.continuous.isProperMap hr hr'

end Retraction

/-- In a Hausdorff space, every *non-closed* subset `A` satisfies
`HasProperHomotopyExtensionProperty A` vacuously. -/
theorem hasProperHomotopyExtensionProperty_of_not_isClosed [T2Space X] (hA : ¬ IsClosed A) :
    HasProperHomotopyExtensionProperty A := by
  intro Y _ f _ H hH h0
  exfalso
  have hnot : ¬ closure A ⊆ A := fun hsub ↦
    hA (Subset.antisymm hsub subset_closure ▸ isClosed_closure)
  obtain ⟨x₀, hx₀cl, hx₀A⟩ := not_subset.1 hnot
  -- Choose an ultrafilter on `A` converging in `X` to `x₀ ∈ closure A \ A`.
  have hne : (Filter.comap (Subtype.val : A → X) (𝓝 x₀)).NeBot :=
    mem_closure_iff_comap_neBot.1 hx₀cl
  let 𝒰 : Ultrafilter A := Ultrafilter.of (Filter.comap (Subtype.val : A → X) (𝓝 x₀))
  have h𝒰 : Tendsto (Subtype.val : A → X) 𝒰 (𝓝 x₀) :=
    tendsto_iff_comap.2 (Ultrafilter.of_le _)
  -- Along `(0, 𝒰)`, `H` agrees with `f` and converges to `f x₀`, forcing a limit in `I × A`.
  have hH_tendsto : Tendsto H (𝒰.map fun a : A ↦ ((0 : I), a)) (𝓝 (f x₀)) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff]
    exact ((f.continuous.tendsto x₀).comp h𝒰).congr fun a ↦ (h0 a).symm
  obtain ⟨⟨_, b⟩, -, hb⟩ := hH.ultrafilter_le_nhds_of_tendsto hH_tendsto
  have hb_tendsto : Tendsto (Subtype.val : A → X) 𝒰 (𝓝 (b : X)) := by
    have hsnd := ((continuous_subtype_val.comp continuous_snd).tendsto (_, b)).mono_left hb
    rwa [Ultrafilter.coe_map, tendsto_map'_iff] at hsnd
  exact hx₀A (tendsto_nhds_unique h𝒰 hb_tendsto ▸ b.2)

section Transport

/-- `HasProperHomotopyExtensionProperty` is invariant under homeomorphisms across arbitrary
universes, with no closedness hypothesis on `A`. -/
theorem HasProperHomotopyExtensionProperty.image {X' : Type u'} [TopologicalSpace X']
    (h : HasProperHomotopyExtensionProperty A) (e : X ≃ₜ X') :
    HasProperHomotopyExtensionProperty (e '' A) := by
  intro Y _ f hf H hH h0
  let eA : I × A ≃ₜ I × (e '' A) := (Homeomorph.refl I).prodCongr (e.image A)
  obtain ⟨G, hG, hG₀, hG₁⟩ :=
    h.exists_extension ⟨fun x ↦ f (e x), by fun_prop⟩ (hf.comp e.isProperMap)
      ⟨fun q ↦ H (eA q), by fun_prop⟩ (hH.comp eA.isProperMap)
      fun a ↦ h0 ⟨e a, mem_image_of_mem e a.2⟩
  let eX : I × X' ≃ₜ I × X := (Homeomorph.refl I).prodCongr e.symm
  refine ⟨⟨fun q ↦ G (eX q), by fun_prop⟩, hG.comp eX.isProperMap, fun x' ↦ ?_, fun t b ↦ ?_⟩
  · simpa [eX] using hG₀ (e.symm x')
  · obtain ⟨a, ha, hae⟩ := b.2
    have hEq : eX (t, b) = (t, a) := by simp [eX, ← hae]
    simp only [ContinuousMap.coe_mk, hEq]
    rw [hG₁ t ⟨a, ha⟩]
    exact congrArg (fun c ↦ H (t, c)) (Subtype.ext hae)

/-- **Proper cofibrations compose along closed embeddings.** If `j : X → X'` is a closed embedding
whose range has the proper homotopy extension property in `X'`, and `A` has the proper homotopy
extension property in `X`, then `j '' A` has the proper homotopy extension property in `X'`. -/
theorem HasProperHomotopyExtensionProperty.image_of_isClosedEmbedding {X' : Type u'}
    [TopologicalSpace X'] (h : HasProperHomotopyExtensionProperty A) {j : X → X'}
    (hj : IsClosedEmbedding j) (hj' : HasProperHomotopyExtensionProperty (range j)) :
    HasProperHomotopyExtensionProperty (j '' A) := by
  intro Y _ f hf H hH h0
  let jA : I × A ≃ₜ I × (j '' A) :=
    (Homeomorph.refl I).prodCongr (hj.isEmbedding.homeomorphImage A)
  obtain ⟨G, hG, hG₀, hG₁⟩ := h.exists_extension
    ⟨fun x ↦ f (j x), by fun_prop⟩ (hf.comp hj.isProperMap)
    ⟨fun q ↦ H (jA q), by fun_prop⟩ (hH.comp jA.isProperMap)
    fun a ↦ h0 ⟨j a, mem_image_of_mem j a.2⟩
  let jR : I × range j ≃ₜ I × X := (Homeomorph.refl I).prodCongr hj.isEmbedding.toHomeomorph.symm
  obtain ⟨G', hG', hG'₀, hG'₁⟩ := hj'.exists_extension f hf
    ⟨fun q ↦ G (jR q), by fun_prop⟩ (hG.comp jR.isProperMap) fun y ↦ by
      obtain ⟨_, x, rfl⟩ := y
      simp [jR, hG₀]
  refine ⟨G', hG', hG'₀, fun t b ↦ ?_⟩
  obtain ⟨_, a, ha, rfl⟩ := b
  rw [hG'₁ t ⟨j a, mem_range_self a⟩]
  have hR : jR (t, ⟨j a, mem_range_self a⟩) = (t, a) := by simp [jR]
  simp only [ContinuousMap.coe_mk, hR, hG₁ t ⟨a, ha⟩]
  rfl

end Transport

end TauCeti
