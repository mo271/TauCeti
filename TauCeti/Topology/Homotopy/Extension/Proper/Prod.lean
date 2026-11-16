/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Cube
public import TauCeti.Topology.Homotopy.Extension.NDRPair
public import TauCeti.Topology.Homotopy.Extension.Proper.Basic

/-!
# Proper NDR pairs and products of closed proper cofibrations

A closed subset `A ⊆ X` has the proper homotopy extension property if and only if it admits NDR
data `N : NDRPair A` whose deformation `N.deformation : I × X → X` is proper
(`TauCeti.exists_isProperMap_ndrPair_iff`). Neither `X` nor `Y` needs any compactness or
separation assumption:

* From a proper cylinder retraction `r : I × X → I × X`, Strøm's NDR construction
  `TauCeti.NDRPair.ofRetraction` takes `Prod.snd ∘ r` as deformation, which is proper because `I`
  is compact (`TauCeti.NDRPair.isProperMap_ofRetraction_deformation`).
* Conversely, when `N.deformation` is proper, the cylinder deformation
  `N.cylinderDeformation : I × (I × X) → I × X` is proper
  (`TauCeti.NDRPair.isProperMap_cylinderDeformation`): along any ultrafilter on `I × (I × X)`,
  compactness of `I` supplies limits for the two time coordinates while
  `ContinuousMap.exists_tendsto_of_tendsto_apply_prodMk` supplies a limit in `X` and identifies the
  value of `N.cylinderDeformation` there.

The same ultrafilter argument shows that the product `N.prod M` of two NDR pairs with proper
deformations again has a proper deformation (`TauCeti.NDRPair.isProperMap_prod_deformation`). This
gives Strøm's product theorem in the proper category
(`TauCeti.HasProperHomotopyExtensionProperty.prod_univ_union_univ_prod`), together with its two
main specializations:

* `TauCeti.HasProperHomotopyExtensionProperty.univ_prod`: `(univ : Set Y) ×ˢ A ⊆ Y × X` for any
  space `Y`;
* `TauCeti.HasProperHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod`: the cylinder-end
  pair `{0, 1} × X ∪ I × A ⊆ I × X`, used to extend proper homotopies between homotopies with both
  endpoints and the trace over `A` prescribed.

## Main declarations

* `TauCeti.NDRPair.isProperMap_cylinderDeformation`,
  `TauCeti.NDRPair.isProperMap_cylinderRetraction`,
  `TauCeti.NDRPair.hasProperHomotopyExtensionProperty`: properness of the cylinder deformation and
  retraction of a proper NDR pair.
* `TauCeti.NDRPair.isProperMap_ofRetraction_deformation`,
  `TauCeti.exists_isProperMap_ndrPair_iff`: **Strøm's characterization of closed subsets with the
  proper homotopy extension property.**
* `TauCeti.NDRPair.isProperMap_prod_deformation`,
  `TauCeti.HasProperHomotopyExtensionProperty.prod_univ_union_univ_prod`: **Strøm's product
  theorem** for closed subsets with the proper homotopy extension property.
* `TauCeti.hasProperHomotopyExtensionProperty_cubeBoundary`,
  `TauCeti.hasProperHomotopyExtensionProperty_zero_one`: cube boundaries and `{0, 1} ⊆ I`.
* `TauCeti.HasProperHomotopyExtensionProperty.univ_prod`,
  `TauCeti.HasProperHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod`: product with an
  arbitrary space and the cylinder-boundary pair `{0, 1} × X ∪ I × A ⊆ I × X`.

## References

* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142.
* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23.
-/

public section

open Filter Set Topology unitInterval

universe u v

namespace TauCeti

namespace NDRPair

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- If the deformation of an NDR pair `N : NDRPair A` is proper, then its cylinder deformation
`I × (I × X) → I × X` is proper. -/
theorem isProperMap_cylinderDeformation (N : NDRPair A) (hN : IsProperMap N.deformation) :
    IsProperMap N.cylinderDeformation := by
  refine isProperMap_iff_ultrafilter.2
    ⟨N.cylinderDeformation.continuous, fun 𝒰 ⟨t_lim, x_lim⟩ hlim ↦ ?_⟩
  rw [nhds_prod_eq, tendsto_prod_iff'] at hlim
  -- Compactness of `I` gives limits `s₀` and `t₀` for the two interval coordinates.
  obtain ⟨s₀, -, hs₀⟩ :=
    isCompact_univ.ultrafilter_le_nhds (𝒰.map Prod.fst) (le_principal_iff.2 univ_mem)
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.ultrafilter_le_nhds
    (𝒰.map (Prod.fst ∘ Prod.snd)) (le_principal_iff.2 univ_mem)
  rw [Ultrafilter.coe_map] at hs₀ ht₀
  -- Properness of `N.deformation` gives a limit `x₀` for the `X`-coordinate.
  have hφ : ∀ w : I × (I × X), w.2.2 ∉ A →
      ContinuousAt (fun w : I × (I × X) ↦
        w.1 * projIcc 0 1 zero_le_one ((w.2.1 : ℝ) / N.control w.2.2)) w :=
    fun w hw ↦ continuous_fst.continuousAt.mul
      (N.control.continuousAt_projIcc_div_of_notMem N.control_eq_zero_iff
        (by fun_prop) (by fun_prop) hw)
  have hsnd : Tendsto (fun w : I × (I × X) ↦
      N.deformation (w.1 * projIcc 0 1 zero_le_one ((w.2.1 : ℝ) / N.control w.2.2), w.2.2))
      𝒰 (𝓝 x_lim) :=
    hlim.2.congr fun w ↦ N.cylinderDeformation_snd w.1 w.2.1 w.2.2
  obtain ⟨x₀, hx₀, hval⟩ := N.deformation.exists_tendsto_of_tendsto_apply_prodMk hN
    (fun t _ hx ↦ N.deformation_of_mem t hx) hφ hsnd
  have hle : (𝒰 : Filter (I × (I × X))) ≤ 𝓝 (s₀, (t₀, x₀)) :=
    Tendsto.prodMk_nhds hs₀ (Tendsto.prodMk_nhds ht₀ hx₀)
  have hfst : (N.cylinderDeformation (s₀, (t₀, x₀))).1 = t_lim :=
    tendsto_nhds_unique
      (((continuous_fst.comp N.cylinderDeformation.continuous).tendsto _).mono_left hle) hlim.1
  refine ⟨(s₀, (t₀, x₀)), Prod.ext hfst ?_, hle⟩
  rw [N.cylinderDeformation_snd]
  exact hval (s₀, (t₀, x₀)) hle rfl

/-- If `N.deformation` is proper, then the cylinder retraction `I × X → {0} × X ∪ I × A` is
proper. -/
theorem isProperMap_cylinderRetraction (N : NDRPair A) (hN : IsProperMap N.deformation) :
    IsProperMap N.cylinderRetraction := by
  have hslice : IsProperMap (fun z : I × X ↦ ((1 : I), z)) :=
    (IsClosedEmbedding.of_continuous_injective_isClosedMap (.prodMk_right (1 : I))
      (Prod.mk_right_injective _) (isClosedMap_prodMk_left _)).isProperMap
  have hEq : (Subtype.val : cylinderExtensionDomain A → I × X) ∘ N.cylinderRetraction =
      N.cylinderDeformation ∘ fun z : I × X ↦ ((1 : I), z) :=
    funext N.coe_cylinderRetraction_apply
  exact isProperMap_of_comp_of_inj N.cylinderRetraction.continuous continuous_subtype_val
    (hEq ▸ (N.isProperMap_cylinderDeformation hN).comp hslice) Subtype.val_injective

/-- An NDR pair with proper deformation has the proper homotopy extension property. -/
theorem hasProperHomotopyExtensionProperty (N : NDRPair A) (hN : IsProperMap N.deformation) :
    HasProperHomotopyExtensionProperty A :=
  hasProperHomotopyExtensionProperty_of_retraction
    (r := (ContinuousMap.subtypeVal _).comp N.cylinderRetraction)
    ((isClosed_cylinderExtensionDomain N.isClosed).isProperMap_subtypeVal.comp
      (N.isProperMap_cylinderRetraction hN))
    (fun z ↦ (N.cylinderRetraction z).2)
    fun z hz ↦ congrArg Subtype.val (N.cylinderRetraction_apply_coe ⟨z, hz⟩)

/-- For a proper retraction `r : I × X → I × X` onto `{0} × X ∪ I × A`, Strøm's NDR pair
`NDRPair.ofRetraction` has proper deformation `Prod.snd ∘ r`. -/
theorem isProperMap_ofRetraction_deformation {r : C(I × X, I × X)}
    (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
    (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p) (hA : IsClosed A)
    (hr_prop : IsProperMap r) :
    IsProperMap (NDRPair.ofRetraction hr hr' hA).deformation := by
  have hEq : ⇑(NDRPair.ofRetraction hr hr' hA).deformation = Prod.snd ∘ r :=
    funext (NDRPair.ofRetraction_deformation hr hr' hA)
  exact hEq ▸ isProperMap_snd_of_compactSpace.comp hr_prop

/-- **Product of proper NDR pairs.** If `N : NDRPair A` and `M : NDRPair B` have proper
deformations, then so does `N.prod M`. -/
theorem isProperMap_prod_deformation {Y : Type v} [TopologicalSpace Y] {B : Set Y}
    (N : NDRPair A) (M : NDRPair B) (hN : IsProperMap N.deformation)
    (hM : IsProperMap M.deformation) :
    IsProperMap (N.prod M).deformation := by
  refine isProperMap_iff_ultrafilter.2
    ⟨(N.prod M).deformation.continuous, fun 𝒰 ⟨x_lim, y_lim⟩ hlim ↦ ?_⟩
  rw [nhds_prod_eq, tendsto_prod_iff'] at hlim
  obtain ⟨t₀, -, ht₀⟩ :=
    isCompact_univ.ultrafilter_le_nhds (𝒰.map Prod.fst) (le_principal_iff.2 univ_mem)
  rw [Ultrafilter.coe_map] at ht₀
  have hφ₁ : ∀ w : I × (X × Y), w.2.1 ∉ A →
      ContinuousAt (fun w : I × (X × Y) ↦
        w.1 * projIcc 0 1 zero_le_one ((M.control w.2.2 : ℝ) / N.control w.2.1)) w :=
    fun w hw ↦ continuous_fst.continuousAt.mul
      (N.control.continuousAt_projIcc_div_of_notMem N.control_eq_zero_iff
        (by fun_prop) (by fun_prop) hw)
  have hφ₂ : ∀ w : I × (X × Y), w.2.2 ∉ B →
      ContinuousAt (fun w : I × (X × Y) ↦
        w.1 * projIcc 0 1 zero_le_one ((N.control w.2.1 : ℝ) / M.control w.2.2)) w :=
    fun w hw ↦ continuous_fst.continuousAt.mul
      (M.control.continuousAt_projIcc_div_of_notMem M.control_eq_zero_iff
        (by fun_prop) (by fun_prop) hw)
  have h₁ : Tendsto (fun w : I × (X × Y) ↦
      N.deformation (w.1 * projIcc 0 1 zero_le_one ((M.control w.2.2 : ℝ) / N.control w.2.1),
        w.2.1)) 𝒰 (𝓝 x_lim) :=
    hlim.1.congr fun w ↦ congrArg Prod.fst (N.prod_deformation_apply M w.1 w.2.1 w.2.2)
  have h₂ : Tendsto (fun w : I × (X × Y) ↦
      M.deformation (w.1 * projIcc 0 1 zero_le_one ((N.control w.2.1 : ℝ) / M.control w.2.2),
        w.2.2)) 𝒰 (𝓝 y_lim) :=
    hlim.2.congr fun w ↦ congrArg Prod.snd (N.prod_deformation_apply M w.1 w.2.1 w.2.2)
  obtain ⟨x₀, hx₀, hval₁⟩ := N.deformation.exists_tendsto_of_tendsto_apply_prodMk hN
    (fun t _ hx ↦ N.deformation_of_mem t hx) hφ₁ h₁
  obtain ⟨y₀, hy₀, hval₂⟩ := M.deformation.exists_tendsto_of_tendsto_apply_prodMk hM
    (fun t _ hy ↦ M.deformation_of_mem t hy) hφ₂ h₂
  have hle : (𝒰 : Filter (I × (X × Y))) ≤ 𝓝 (t₀, (x₀, y₀)) :=
    Tendsto.prodMk_nhds ht₀ (Tendsto.prodMk_nhds hx₀ hy₀)
  refine ⟨(t₀, (x₀, y₀)), ?_, hle⟩
  rw [N.prod_deformation_apply M]
  exact Prod.ext (hval₁ _ hle rfl) (hval₂ _ hle rfl)

end NDRPair

section Products

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : Set X} {B : Set Y}

/-- **Strøm's characterization in the proper category**: a subset is closed and has the proper
homotopy extension property if and only if it admits NDR data with a proper deformation. -/
theorem exists_isProperMap_ndrPair_iff :
    (IsClosed A ∧ HasProperHomotopyExtensionProperty A) ↔
      ∃ N : NDRPair A, IsProperMap N.deformation :=
  ⟨fun ⟨hA, h⟩ ↦
    let ⟨_, hr_prop, hr, hr'⟩ := h.exists_retraction hA
    ⟨NDRPair.ofRetraction hr hr' hA,
      NDRPair.isProperMap_ofRetraction_deformation hr hr' hA hr_prop⟩,
   fun ⟨N, hN⟩ ↦ ⟨N.isClosed, N.hasProperHomotopyExtensionProperty hN⟩⟩

/-- **Strøm's product theorem for proper cofibrations**: if closed subsets `A ⊆ X` and `B ⊆ Y`
have the proper homotopy extension property, then so does `A × Y ∪ X × B ⊆ X × Y`. -/
theorem HasProperHomotopyExtensionProperty.prod_univ_union_univ_prod
    (hA : HasProperHomotopyExtensionProperty A) (hA' : IsClosed A)
    (hB : HasProperHomotopyExtensionProperty B) (hB' : IsClosed B) :
    HasProperHomotopyExtensionProperty (A ×ˢ (univ : Set Y) ∪ (univ : Set X) ×ˢ B) := by
  obtain ⟨N, hN⟩ := exists_isProperMap_ndrPair_iff.1 ⟨hA', hA⟩
  obtain ⟨M, hM⟩ := exists_isProperMap_ndrPair_iff.1 ⟨hB', hB⟩
  exact (N.prod M).hasProperHomotopyExtensionProperty (N.isProperMap_prod_deformation M hN hM)

/-- The product `Y × A ⊆ Y × X` of any topological space `Y` with a closed subset `A ⊆ X` having
the proper homotopy extension property again has the proper homotopy extension property. -/
theorem HasProperHomotopyExtensionProperty.univ_prod
    (h : HasProperHomotopyExtensionProperty A) (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty ((univ : Set Y) ×ˢ A) := by
  simpa using hasProperHomotopyExtensionProperty_empty.prod_univ_union_univ_prod
    isClosed_empty h hA

/-- For a finite index type `N`, the boundary `Cube.boundary N` of `I^N` has the proper homotopy
extension property in `I^N`. -/
@[simp]
theorem hasProperHomotopyExtensionProperty_cubeBoundary {N : Type*} [Finite N] :
    HasProperHomotopyExtensionProperty (Cube.boundary N) :=
  (hasProperHomotopyExtensionProperty_iff_hasHomotopyExtensionProperty Cube.isClosed_boundary).2
    hasHomotopyExtensionProperty_cubeBoundary

/-- The boundary `{0, 1}` of the unit interval has the proper homotopy extension property in `I`. -/
@[simp]
theorem hasProperHomotopyExtensionProperty_zero_one :
    HasProperHomotopyExtensionProperty ({0, 1} : Set I) :=
  (hasProperHomotopyExtensionProperty_iff_hasHomotopyExtensionProperty (Set.toFinite _).isClosed).2
    hasHomotopyExtensionProperty_zero_one

/-- **The cylinder-boundary pair on a closed proper cofibration**: if a closed subset `A ⊆ X` has
the proper homotopy extension property, then so does `{0, 1} × X ∪ I × A ⊆ I × X`. -/
theorem HasProperHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod
    (h : HasProperHomotopyExtensionProperty A) (hA : IsClosed A) :
    HasProperHomotopyExtensionProperty (({0, 1} : Set I) ×ˢ (univ : Set X) ∪ univ ×ˢ A) :=
  hasProperHomotopyExtensionProperty_zero_one.prod_univ_union_univ_prod
    (Set.toFinite _).isClosed h hA

end Products

end TauCeti
