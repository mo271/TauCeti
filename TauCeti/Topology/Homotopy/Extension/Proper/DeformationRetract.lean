/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Proper.Prod

/-!
# A proper cofibration which is a proper homotopy equivalence is a proper strong deformation retract

Let `A ⊆ X` have the proper homotopy extension property. If the inclusion `A → X` is a proper
homotopy equivalence (`ContinuousMap.HasProperHomotopyInverse`), then `A` is a *proper strong
deformation retract* of `X`: there exist a proper retraction `r : C(X, A)` and a jointly proper
homotopy `H : (ContinuousMap.id X).HomotopyRel ((subtypeVal A).comp r) A` stationary on `A` at
every time (`TauCeti.properStrongDeformationRetract_of_inverse`). Conversely, any proper strong
deformation retraction exhibits the inclusion `A → X` as a proper homotopy equivalence, yielding an
exact equivalence
(`TauCeti.HasProperHomotopyExtensionProperty.exists_proper_strong_deformation_retraction_iff`).

No compactness or Hausdorffness assumption on `X` is needed: properness of `Subtype.val : A → X`
implies that `A` is closed (`IsProperMap.isClosed_range`), while properness of a homotopy inverse
`g : C(X, A)` follows automatically from properness of `(subtypeVal A).comp g` along the injective
map `Subtype.val` (`isProperMap_of_comp_of_inj`). To make the inverse homotopy stationary on `A`
without passing to path spaces (which would demand local compactness), the retracing step extends a
compact-square reparametrization from `{0, 1} × X ∪ I × A` to `I × X` via
`TauCeti.HasProperHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod`.

## Main declarations

* `TauCeti.HasProperHomotopyExtensionProperty.exists_proper_retraction_homotopic`: a proper left
  homotopy inverse of the inclusion of `A` is properly homotopic to a proper retraction.
* `TauCeti.HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retracing`: a proper
  homotopy followed by a proper homotopy that retraces it on a closed subset `A` with the proper
  homotopy extension property yields a proper homotopy relative to `A`.
* `TauCeti.HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retraction`: a retraction
  onto `A` whose composite with the inclusion is properly homotopic to `id_X` is properly homotopic
  to `id_X` relative to `A`.
* `TauCeti.properStrongDeformationRetract_of_inverse`: **rectification of a proper homotopy inverse
  of a proper cofibration inclusion to a proper strong deformation retraction.**
* `TauCeti.HasProperHomotopyExtensionProperty.exists_proper_strong_deformation_retraction_iff`:
  characterization of proper strong deformation retracts via
  `ContinuousMap.HasProperHomotopyInverse`.

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. **27** (1973), 1–23, §1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0,
  Proposition 0.19.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousMap Set Topology unitInterval

universe u v

section Retracing

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X}

private abbrev cylinderBoundary (A : Set X) : Set (I × X) :=
  ({0, 1} : Set I) ×ˢ (univ : Set X) ∪ univ ×ˢ A

private noncomputable def retracingTime₁ (u t : I) : I :=
  projIcc 0 1 zero_le_one (2 * (t : ℝ) * (1 - u))

private noncomputable def retracingTime₂ (u t : I) : I :=
  projIcc 0 1 zero_le_one (1 - 2 * (1 - (t : ℝ)) * (1 - u))

private lemma isProperMap_reparam (hB : IsClosed (cylinderBoundary A))
    {s : Set (I × cylinderBoundary A)} (hs : IsClosed s) {φ : I × I → I} (hφ : Continuous φ)
    {F : I × X → Y} (hF : IsProperMap F) :
    IsProperMap (fun q : s ↦ F (φ (q.1.1, q.1.2.1.1), q.1.2.1.2)) :=
  -- The map factors through the closed embedding `s ↪ I × cylinderBoundary A ↪ I × (I × X)`,
  -- reassociates to `(I × I) × X`, applies proper `φ × id`, and composes with proper `F`.
  hF.comp <| ((hφ.isProperMap.prodMap isProperMap_id).comp
    (Homeomorph.prodAssoc I I X).symm.isProperMap).comp <|
    (isProperMap_id.prodMap hB.isClosedEmbedding_subtypeVal.isProperMap).comp
      hs.isClosedEmbedding_subtypeVal.isProperMap

private noncomputable def retracingBoundaryMap {f₀ f₁ f₂ : C(X, Y)} (F : f₀.Homotopy f₁)
    (G : f₁.Homotopy f₂) (q : I × cylinderBoundary A) : Y :=
  if (q.2.1.1 : ℝ) ≤ 1 / 2 then
    F (retracingTime₁ q.1 q.2.1.1, q.2.1.2)
  else
    G (retracingTime₂ q.1 q.2.1.1, q.2.1.2)

private lemma isProperMap_retracingBoundaryMap (hA : IsClosed A) {f₀ f₁ f₂ : C(X, Y)}
    (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (hF : IsProperMap F) (hG : IsProperMap G)
    (hG_retrace : ∀ t, ∀ x ∈ A, G (t, x) = F (σ t, x)) :
    IsProperMap (retracingBoundaryMap (A := A) F G) := by
  have hB : IsClosed (cylinderBoundary A) :=
    ((Set.toFinite _).isClosed.prod isClosed_univ).union (isClosed_univ.prod hA)
  let s₁ : Set (I × cylinderBoundary A) := {q | (q.2.1.1 : ℝ) ≤ 1 / 2}
  let s₂ : Set (I × cylinderBoundary A) := {q | 1 / 2 ≤ (q.2.1.1 : ℝ)}
  have hs₁ : IsClosed s₁ := isClosed_le (by fun_prop) continuous_const
  have hs₂ : IsClosed s₂ := isClosed_le continuous_const (by fun_prop)
  have hcov : s₁ ∪ s₂ = univ := ext fun q ↦ by simp [s₁, s₂, le_total]
  rw [isProperMap_iff_domRestrict_of_isClosed_union hs₁ hs₂ hcov]
  refine ⟨?_, ?_⟩
  · have h₁ : s₁.domRestrict (retracingBoundaryMap F G) =
        fun q : s₁ ↦ F (retracingTime₁ q.1.1 q.1.2.1.1, q.1.2.1.2) :=
      funext fun q ↦ ite_eq_left_iff.2 fun h ↦ absurd q.2 h
    exact h₁ ▸ isProperMap_reparam hB hs₁
      (φ := fun p ↦ retracingTime₁ p.1 p.2) (by unfold retracingTime₁; fun_prop) hF
  · have h₂ : s₂.domRestrict (retracingBoundaryMap F G) =
        fun q : s₂ ↦ G (retracingTime₂ q.1.1 q.1.2.1.1, q.1.2.1.2) := by
      ext q
      simp only [domRestrict_apply, retracingBoundaryMap]
      split_ifs with hle
      · have hhalf : (q.1.2.1.1 : ℝ) = 1 / 2 := le_antisymm hle q.2
        have hxA : q.1.2.1.2 ∈ A := by
          rcases q.1.2.2 with ⟨h01, -⟩ | ⟨-, hx⟩
          · rcases h01 with h0 | h1
            · rw [h0] at hhalf; norm_num at hhalf
            · rw [Set.mem_singleton_iff.1 h1] at hhalf; norm_num at hhalf
          · exact hx
        rw [hG_retrace _ _ hxA]
        congr 2
        have hu0 := q.1.1.2.1
        have hu1 := q.1.1.2.2
        ext
        simp only [retracingTime₁, retracingTime₂, hhalf, coe_symm_eq, coe_projIcc, min_def,
          max_def]
        split_ifs <;> linarith
      · rfl
    exact h₂ ▸ isProperMap_reparam hB hs₂
      (φ := fun p ↦ retracingTime₂ p.1 p.2) (by unfold retracingTime₂; fun_prop) hG

private lemma retracingBoundaryMap_zero {f₀ f₁ f₂ : C(X, Y)} (F : f₀.Homotopy f₁)
    (G : f₁.Homotopy f₂) (z : cylinderBoundary A) :
    retracingBoundaryMap F G (0, z) = F.trans G z.1 := by
  have hz0 := z.1.1.2.1
  have hz1 := z.1.1.2.2
  unfold retracingBoundaryMap
  rw [Homotopy.trans_apply]
  split_ifs with ht <;>
  · congr 2
    ext
    simp only [retracingTime₁, retracingTime₂, Icc.coe_zero, coe_projIcc, min_def, max_def]
    split_ifs <;> linarith

/-- **A proper homotopy retracing itself on a closed proper cofibration can be made stationary.**
If `F : f₀.Homotopy f₁` and `G : f₁.Homotopy f₂` are proper homotopies such that `G` runs backwards
along `F` at every point of a closed subset `A ⊆ X` with the proper homotopy extension property,
then there is a proper homotopy from `f₀` to `f₂` relative to `A`. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retracing
    (hA : HasProperHomotopyExtensionProperty A) (hA_closed : IsClosed A) {f₀ f₁ f₂ : C(X, Y)}
    (F : f₀.Homotopy f₁) (G : f₁.Homotopy f₂) (hF : IsProperMap F) (hG : IsProperMap G)
    (hG_retrace : ∀ t, ∀ x ∈ A, G (t, x) = F (σ t, x)) :
    ∃ H : f₀.HomotopyRel f₂ A, IsProperMap H := by
  have hΨ := isProperMap_retracingBoundaryMap hA_closed F G hF hG hG_retrace
  obtain ⟨K, hK, hK₀, hK₁⟩ := (hA.zero_one_prod_univ_union_univ_prod hA_closed).exists_extension
    (F.trans G).toContinuousMap (F.isProperMap_trans G hF hG)
    ⟨retracingBoundaryMap F G, hΨ.continuous⟩ hΨ (retracingBoundaryMap_zero F G)
  let H : f₀.HomotopyRel f₂ A :=
    { toFun := fun p ↦ K (1, p)
      continuous_toFun := by fun_prop
      map_zero_left := fun x ↦ by
        rw [hK₁ 1 ⟨(0, x), Or.inl ⟨Or.inl rfl, trivial⟩⟩]
        simp [retracingBoundaryMap, retracingTime₁]
      map_one_left := fun x ↦ by
        rw [hK₁ 1 ⟨(1, x), Or.inl ⟨Or.inr rfl, trivial⟩⟩]
        norm_num [retracingBoundaryMap, retracingTime₂]
      prop' := fun t x hx ↦ by
        simp only [ContinuousMap.coe_mk]
        rw [hK₁ 1 ⟨(t, x), Or.inr ⟨trivial, hx⟩⟩]
        simp only [ContinuousMap.coe_mk, retracingBoundaryMap]
        split_ifs
        · simp [retracingTime₁]
        · simp [retracingTime₂, hG_retrace 1 x hx] }
  let K' : (F.trans G).toContinuousMap.Homotopy H.toContinuousMap :=
    { toContinuousMap := K, map_zero_left := hK₀, map_one_left := fun _ ↦ rfl }
  exact ⟨H, K'.isProperMap_right hK⟩

end Retracing

section DeformationRetract

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- A proper homotopy left inverse `g : C(X, A)` of the inclusion of a subset with the proper
homotopy extension property is properly homotopic to a proper retraction `r : C(X, A)`. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_retraction_homotopic
    (hA : HasProperHomotopyExtensionProperty A) {g : C(X, A)} (hg : IsProperMap g)
    (H : (g.comp (subtypeVal A)).Homotopy (.id A)) (hH : IsProperMap H) :
    ∃ (r : C(X, A)) (E : r.Homotopy g), IsProperMap r ∧ (∀ a : A, r a = a) ∧ IsProperMap E := by
  obtain ⟨G, hG, hG₀, hG₁⟩ := hA.exists_extension g hg H.toContinuousMap hH H.apply_zero
  let G' : g.Homotopy ⟨fun x ↦ G (1, x), by fun_prop⟩ :=
    { toContinuousMap := G, map_zero_left := hG₀, map_one_left := fun _ ↦ rfl }
  exact ⟨⟨fun x ↦ G (1, x), by fun_prop⟩, G'.symm, G'.isProperMap_right hG,
    fun a ↦ by simpa using hG₁ 1 a, G'.isProperMap_symm hG⟩

/-- A retraction `r : C(X, A)` onto a subset `A` with the proper homotopy extension property whose
composite with the inclusion is properly homotopic to `id_X` is properly homotopic to `id_X`
relative to `A`. Neither `IsProperMap (Subtype.val : A → X)` nor `IsProperMap r` needs to be
assumed separately, as both follow from properness of `F`. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_homotopyRel_of_retraction
    (hA : HasProperHomotopyExtensionProperty A) {r : C(X, A)} (hr : ∀ a : A, r a = a)
    (F : ((subtypeVal A).comp r).Homotopy (.id X)) (hF : IsProperMap F) :
    ∃ H : (ContinuousMap.id X).HomotopyRel ((subtypeVal A).comp r) A, IsProperMap H := by
  have hcomp : IsProperMap ((subtypeVal A).comp r) := F.isProperMap_left hF
  have hincl : IsProperMap (Subtype.val : A → X) :=
    isProperMap_of_comp_of_surj r.continuous continuous_subtype_val hcomp fun a ↦ ⟨a, hr a⟩
  have hA_closed : IsClosed A := Subtype.range_coe (s := A) ▸ hincl.isClosed_range
  let G : ((subtypeVal A).comp r).Homotopy ((subtypeVal A).comp r) :=
    (F.compContinuousMap ((subtypeVal A).comp r)).cast
      (ContinuousMap.ext fun x ↦ by simp [hr]) (ContinuousMap.id_comp _)
  refine hA.exists_proper_homotopyRel_of_retracing hA_closed F.symm G (F.isProperMap_symm hF)
    (F.isProperMap_compContinuousMap hF hcomp) fun t x hx ↦ ?_
  have hrx : (r x : X) = x := congrArg Subtype.val (hr ⟨x, hx⟩)
  simp [G, hrx]

/-- **A proper cofibration whose inclusion has a proper homotopy inverse is a proper strong
deformation retract.** Given `HasProperHomotopyExtensionProperty A`, properness of the inclusion
`A → X`, a continuous map `g : C(X, A)`, and proper homotopies `H : g ∘ incl ≃ id_A` and
`K : incl ∘ g ≃ id_X`, there exist a proper retraction `r : C(X, A)` and a jointly proper homotopy
`id_X ≃ incl ∘ r` relative to `A`. Properness of `g` need not be assumed separately, as it follows
from properness of `K`. -/
theorem properStrongDeformationRetract_of_inverse (A : Set X)
    (hA : HasProperHomotopyExtensionProperty A) (hincl : IsProperMap (Subtype.val : A → X))
    (g : C(X, A)) (H : (g.comp (subtypeVal A)).Homotopy (.id A))
    (K : ((subtypeVal A).comp g).Homotopy (.id X)) (hH : IsProperMap H) (hK : IsProperMap K) :
    ∃ r : C(X, A), IsProperMap r ∧ (∀ a : A, r a = a) ∧
      ∃ Hrel : (ContinuousMap.id X).HomotopyRel ((subtypeVal A).comp r) A, IsProperMap Hrel := by
  have hg : IsProperMap g :=
    isProperMap_of_comp_of_inj g.continuous continuous_subtype_val (K.isProperMap_left hK)
      Subtype.val_injective
  obtain ⟨r, E, hr_prop, hr, hE⟩ := hA.exists_proper_retraction_homotopic hg H hH
  have hF : IsProperMap (((Homotopy.refl (subtypeVal A)).comp E).trans K) :=
    Homotopy.isProperMap_trans _ K
      ((Homotopy.refl (subtypeVal A)).isProperMap_comp E (Homotopy.isProperMap_refl hincl) hE) hK
  exact ⟨r, hr_prop, hr, hA.exists_proper_homotopyRel_of_retraction hr _ hF⟩

/-- For a subset `A ⊆ X` with the proper homotopy extension property, `A` is a proper strong
deformation retract of `X` if and only if its inclusion `subtypeVal A : C(A, X)` has a proper
homotopy inverse. -/
theorem HasProperHomotopyExtensionProperty.exists_proper_strong_deformation_retraction_iff
    (hA : HasProperHomotopyExtensionProperty A) :
    (∃ r : C(X, A), IsProperMap r ∧ (∀ a : A, r a = a) ∧
      ∃ H : (ContinuousMap.id X).HomotopyRel ((subtypeVal A).comp r) A, IsProperMap H) ↔
      (subtypeVal A).HasProperHomotopyInverse := by
  refine ⟨fun ⟨r, hr_prop, hr, H, hH⟩ ↦ ?_, fun h ↦ ?_⟩
  · have hincl : IsProperMap (subtypeVal A) :=
      isProperMap_of_comp_of_surj r.continuous continuous_subtype_val
        (H.toHomotopy.isProperMap_right hH) fun a ↦ ⟨a, hr a⟩
    have hri : r.comp (subtypeVal A) = ContinuousMap.id A := ContinuousMap.ext hr
    exact .intro hincl r hr_prop ((Homotopy.refl (.id A)).cast hri.symm rfl) H.toHomotopy.symm
      ((Homotopy.isProperMap_cast_iff _ _ _).2 (Homotopy.isProperMap_refl isProperMap_id))
      (H.isProperMap_symm hH)
  · obtain ⟨g, -, H, K, hH, hK⟩ := h.exists_inverse
    exact properStrongDeformationRetract_of_inverse A hA h.isProperMap g H K hH hK

end DeformationRetract

end TauCeti
