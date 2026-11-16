/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.WeightTwist
public import TauCeti.RepresentationTheory.LSPath.Central.Transport
public import TauCeti.RepresentationTheory.LSPath.Crystal.Component

import Mathlib.LinearAlgebra.TensorProduct.Basic
import TauCeti.LinearAlgebra.RootSystem.Chamber
import TauCeti.LinearAlgebra.RootSystem.Positive
import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Ray
import TauCeti.RepresentationTheory.LSPath.OrbitStable

/-!
# Crystal-level central transport on Lakshmibai–Seshadri paths

Let `P : RootDatum ι X Y` be a finite reduced root datum with base `b : P.Base`. A weight `χ ∈ X`
annihilates all simple coroots if and only if it is fixed by the Weyl group
(`TauCeti.LSPath.forall_toLinearMap_coroot_eq_zero_iff_forall_smul_eq_self`). Adding such a central
character preserves the closed dominant chamber (`add_mem_dominantChamber_of_forall_coroot_eq_zero`)
and shifts the crystal weights of `LSPath.normalCrystal` by `χ` while commuting with the crystal
root operators (`normalCrystal_wt_centralTransport`, `normalCrystal_e_centralTransport`,
`normalCrystal_f_centralTransport`).

Crucially, `LSPath.centralTransport` acts on the canonical LS encoding `(τ; a)` by directions and
breaks—whose distinguished piecewise-linear presentation in `ℚ ⊗[ℤ] X` intertwines Littelmann's root
operators via `PLPath.raise_shiftDistinguished`—rather than by applying `t ↦ t χ` to an arbitrary
representative of the ambient path reparametrization quotient (where pointwise shifting is not well
defined; see `TauCeti.PLPath.not_exists_shiftTimed_on_paths`).

For central weights `χ, σ ∈ X` and dominant `λ ∈ X`, this yields the two-offset family of strict
crystal isomorphisms
`centralTransportIso : B(λ)^(σ + χ) ≃ B(λ + χ)^σ`
(and its propositional-endpoint form `centralTransportIsoOfEq`), whose underlying path bijection is
`LSPath.centralTransport χ` independently of `σ`. At `σ = 0` this gives `centralTransportIsoZero`
from the weight-twisted `B(λ)^χ` onto `B(λ + χ)`. Keeping track of both offsets makes every source,
intermediate crystal, and target identical as weighted crystals in the strict-isomorphism laws:
* **Identity**: `T_{λ, 0}^σ = id` (`centralTransportIsoOfEq_zero`);
* **Additive composition**: `T_{λ + χ, ψ}^σ ∘ T_{λ, χ}^{σ + ψ} = T_{λ, χ + ψ}^σ`
  (`centralTransportIso_trans`, `centralTransportIsoOfEq_trans`);
* **Inverse**: `(T_{λ, χ}^σ)⁻¹ = T_{λ + χ, -χ}^{σ + χ}`
  (`centralTransportIso_symm`, `centralTransportIsoOfEq_symm`).

All results apply without restriction to `λ + χ = 0`, pure central shapes (`LSPath P b χ` consists
solely of `straight χ` and its `normalCrystal` is strictly isomorphic to `NormalCrystal.central`,
`pureCentralCrystalIso`), and empty root systems (`IsEmpty b.support`).

## Main definitions

* `TauCeti.LSPath.centralTransportIsoZero`: strict crystal isomorphism
  `(normalCrystal hlam).weightTwist χ hχ ≃ normalCrystal hlam'` for central `χ`.
* `TauCeti.LSPath.centralTransportIso`: two-offset strict crystal isomorphism
  `B(λ)^(σ + χ) ≃ B(λ + χ)^σ` for central `χ, σ`.
* `TauCeti.LSPath.centralTransportIsoOfEq`: two-offset strict crystal isomorphism with general
  propositionally equal weight and twist endpoints `λ + χ = μ` and `σ + χ = τ`.
* `TauCeti.LSPath.pureCentralCrystalIso`: strict crystal isomorphism
  `NormalCrystal.central χ hχ ≃ normalCrystal hχ_dom` for a pure central weight `χ`.

## Main results

* `TauCeti.LSPath.forall_toLinearMap_coroot_eq_zero_iff_forall_smul_eq_self`: a weight annihilates
  the simple coroots if and only if it is fixed by `P.weylGroup`.
* `TauCeti.LSPath.normalCrystal_wt_centralTransport`,
  `TauCeti.LSPath.normalCrystal_e_centralTransport`,
  `TauCeti.LSPath.normalCrystal_f_centralTransport`: effect of `centralTransport` on crystal weights
  and root operators.
* `TauCeti.LSPath.centralTransportIsoOfEq_zero`,
  `TauCeti.LSPath.centralTransportIsoOfEq_trans`,
  `TauCeti.LSPath.centralTransportIsoOfEq_symm`: identity, additive composition, and inverse laws
  as equalities of strict crystal isomorphisms.
* `TauCeti.LSPath.eq_straight_of_forall_coroot_eq_zero`: for a pure central shape `χ`, every LS path
  equals `straight χ`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§2, 4–5.
* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
-/

public section

namespace TauCeti.LSPath

open Module RootPairing Set
open scoped TensorProduct

section CentralWeights

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base}

/-- A weight in a root datum annihilates all simple coroots if and only if it is fixed by the Weyl
group. -/
theorem forall_toLinearMap_coroot_eq_zero_iff_forall_smul_eq_self {χ : X} :
    (∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) ↔ ∀ w : P.weylGroup, w • χ = χ := by
  refine ⟨fun h ↦ smul_eq_self_of_forall_coroot'_eq_zero b (fun i hi ↦ h ⟨i, hi⟩), fun h i ↦ ?_⟩
  have hrefl : P.toLinearMap (RootPairing.weylGroup.ofIdx P i.1 • χ) (P.coroot i.1) =
      P.toLinearMap χ (P.coroot i.1) := by
    rw [h]
  rw [RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul,
    P.reflection_apply, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
    P.root_coroot_eq_pairing, P.pairing_same, smul_eq_mul] at hrefl
  -- `P.coroot' i.1 χ` unfolds to `P.toLinearMap χ (P.coroot i.1)`, giving `c - c * 2 = c`.
  change P.toLinearMap χ (P.coroot i) - P.toLinearMap χ (P.coroot i) * 2 =
    P.toLinearMap χ (P.coroot i) at hrefl
  omega

/-- Convert simple-coroot annihilation from `P.toLinearMap χ (P.coroot i) = 0` to
`P.coroot' i χ = 0`. -/
theorem coroot'_eq_zero_of_forall_coroot_eq_zero {χ : X}
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    ∀ i ∈ b.support, P.coroot' i χ = 0 :=
  fun i hi ↦ hχ ⟨i, hi⟩

/-- Every weight annihilating the simple coroots lies in the closed dominant chamber. -/
theorem mem_dominantChamber_of_forall_coroot_eq_zero {χ : X}
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    χ ∈ dominantChamber P b :=
  (mem_dominantChamber P b χ).mpr fun i hi ↦ by
    simpa [RootPairing.coroot'] using (hχ ⟨i, hi⟩).ge

/-- Translating a dominant weight by a weight annihilating the simple coroots preserves
dominance. -/
theorem add_mem_dominantChamber_of_forall_coroot_eq_zero {lam χ : X}
    (hlam : lam ∈ dominantChamber P b)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    lam + χ ∈ dominantChamber P b :=
  add_mem_dominantChamber P b hlam (mem_dominantChamber_of_forall_coroot_eq_zero hχ)

end CentralWeights

section CrystalTransport

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced]

/-! ### Extensionality via underlying direction values and break times -/

private def dirVals {lam : X} (π : LSPath P b lam) : List P.weylGroup :=
  (List.ofFn π.dir).map Subtype.val

private def times {lam : X} (π : LSPath P b lam) : List ℚ :=
  List.ofFn π.time

private theorem ext_of_dirVals_of_times {lam : X} {π π' : LSPath P b lam}
    (hdir : dirVals π = dirVals π') (htime : times π = times π') :
    π = π' :=
  LSPath.ext (List.map_injective_iff.mpr Subtype.val_injective hdir) htime

@[simp]
private theorem dirVals_centralTransport {lam χ : X}
    {hχ : ∀ i ∈ b.support, P.coroot' i χ = 0} (π : LSPath P b lam) :
    dirVals (centralTransport χ hχ π) = dirVals π := by
  simp only [dirVals]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_ofFn, length_centralTransport]
  · intro n h₁ h₂
    simp only [List.getElem_map, List.getElem_ofFn, dir_centralTransport, Fin.cast_mk]

@[simp]
private theorem times_centralTransport {lam χ : X}
    {hχ : ∀ i ∈ b.support, P.coroot' i χ = 0} (π : LSPath P b lam) :
    times (centralTransport χ hχ π) = times π := by
  simp only [times]
  apply List.ext_getElem
  · simp only [List.length_ofFn, length_centralTransport]
  · intro n h₁ h₂
    simp only [List.getElem_ofFn, time_centralTransport, Fin.cast_mk]

/-! ### Intertwining `normalCrystal` with `centralTransport` -/

/-- `centralTransport χ` shifts the crystal weight of an LS path by `χ`. -/
@[simp]
theorem normalCrystal_wt_centralTransport {lam χ : X}
    (hlam : lam ∈ dominantChamber P b) {hlam' : lam + χ ∈ dominantChamber P b}
    {hχ : ∀ i ∈ b.support, P.coroot' i χ = 0} (π : LSPath P b lam) :
    (normalCrystal hlam').wt (centralTransport χ hχ π) = (normalCrystal hlam).wt π + χ := by
  let f₀ : X →+ (ℚ ⊗[ℤ] X) := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
  apply P.tensorProduct_mk_injective ℚ
  change f₀ ((normalCrystal hlam').wt (centralTransport χ hχ π)) =
    f₀ ((normalCrystal hlam).wt π + χ)
  rw [map_add, ← endpoint_toPLPath_eq_apply_normalCrystal_wt (𝕜 := ℚ) hlam',
    ← endpoint_toPLPath_eq_apply_normalCrystal_wt (𝕜 := ℚ) hlam,
    endpoint_toPLPath_centralTransport]

/-- `centralTransport χ` commutes with the crystal raising operators `e_i`. -/
@[simp]
theorem normalCrystal_e_centralTransport {lam χ : X}
    (hlam : lam ∈ dominantChamber P b) {hlam' : lam + χ ∈ dominantChamber P b}
    {hχ : ∀ i ∈ b.support, P.coroot' i χ = 0} (i : b.support) (π : LSPath P b lam) :
    (normalCrystal hlam').e i (centralTransport χ hχ π) =
      ((normalCrystal hlam).e i π).map (centralTransport χ hχ) := by
  let f₀ : X →+ (ℚ ⊗[ℤ] X) := (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom
  let F₀ : b.support → Dual ℚ (ℚ ⊗[ℤ] X) := fun j ↦
    LinearMap.liftBaseChange ℚ ((Algebra.linearMap ℤ ℚ).comp (P.coroot' j.1))
  have hf₀ : Function.Injective f₀ := P.tensorProduct_mk_injective ℚ
  have hF₀ : ∀ (j : b.support) (x : X), F₀ j (f₀ x) = (P.coroot' j x : ℚ) := by
    intro j x
    simp [f₀, F₀]
  have hS : MapsTo (preReflection (f₀ (P.root i)) (F₀ i))
      (range fun w : P.weylGroup ↦ f₀ (w • lam))
      (range fun w : P.weylGroup ↦ f₀ (w • lam)) := by
    have h := P.mapsTo_preReflection_image_orbit_weylGroup i.1 (hF₀ i) lam
    rwa [MulAction.orbit, ← range_comp] at h
  have hS' : (range fun w : P.weylGroup ↦ f₀ (w • lam)).Pairwise fun u v ↦ ¬ SameRay ℚ u v := by
    have h := P.pairwise_not_sameRay_image_orbit_weylGroup b hF₀ lam
    rwa [MulAction.orbit, ← range_comp] at h
  have hFχ : F₀ i (f₀ χ) = 0 := by simp [hF₀, hχ i.1 i.2]
  apply Option.map_injective (toPLPath_injective_of_coroot' hlam' hf₀.injOn hF₀)
  rw [map_toPLPath_normalCrystal_e hlam' hF₀,
    toPLPath_centralTransport χ hχ π ℚ f₀ hlam hf₀.injOn hS',
    PLPath.raise_shiftDistinguished (π.hasDistinguished_toPLPath ℚ f₀) hS hS' hFχ,
    ← map_toPLPath_normalCrystal_e hlam hF₀, Option.map_map, Option.map_map]
  congr 1
  funext ρ
  exact (toPLPath_centralTransport χ hχ ρ ℚ f₀ hlam hf₀.injOn hS').symm

omit [Finite ι] [P.IsReduced] in
private theorem toLinearMap_coroot_eq_zero_of_forall_coroot'_eq_zero {χ : X}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) :
    ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0 :=
  fun j ↦ hχ j.1 j.2

/-- **Central transport from the weight-twisted crystal `B(λ)^χ` onto `B(λ + χ)`** (the `σ = 0`
specialization of `centralTransportIso`). -/
noncomputable def centralTransportIsoZero {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    NormalCrystal.StrictIso
      ((normalCrystal hlam).weightTwist χ hχ)
      (normalCrystal (add_mem_dominantChamber_of_forall_coroot_eq_zero hlam hχ)) where
  toEquiv := centralTransport χ (coroot'_eq_zero_of_forall_coroot_eq_zero hχ)
  wt_toFun π := by
    simp only [Equiv.toFun_as_coe, NormalCrystal.weightTwist_wt,
      normalCrystal_wt_centralTransport hlam]
  e_toFun i π := by
    simp only [Equiv.toFun_as_coe, NormalCrystal.weightTwist_e,
      normalCrystal_e_centralTransport hlam]

@[simp]
theorem coe_centralTransportIsoZero {lam : X} {hlam : lam ∈ dominantChamber P b}
    {χ : X} {hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0} :
    ⇑(centralTransportIsoZero hlam χ hχ) =
      centralTransport χ (coroot'_eq_zero_of_forall_coroot_eq_zero hχ) :=
  (rfl)

/-- `centralTransport χ` commutes with the crystal lowering operators `f_i`. -/
@[simp]
theorem normalCrystal_f_centralTransport {lam χ : X}
    (hlam : lam ∈ dominantChamber P b) {hlam' : lam + χ ∈ dominantChamber P b}
    {hχ : ∀ i ∈ b.support, P.coroot' i χ = 0} (i : b.support) (π : LSPath P b lam) :
    (normalCrystal hlam').f i (centralTransport χ hχ π) =
      ((normalCrystal hlam).f i π).map (centralTransport χ hχ) := by
  simpa only [NormalCrystal.weightTwist_f, coe_centralTransportIsoZero] using
    (centralTransportIsoZero hlam χ
      (toLinearMap_coroot_eq_zero_of_forall_coroot'_eq_zero hχ)).f_apply i π

/-- `centralTransport χ` preserves the crystal string lengths `ε_i`. -/
@[simp]
theorem normalCrystal_ε_centralTransport {lam χ : X}
    (hlam : lam ∈ dominantChamber P b) {hlam' : lam + χ ∈ dominantChamber P b}
    {hχ : ∀ i ∈ b.support, P.coroot' i χ = 0} (i : b.support) (π : LSPath P b lam) :
    (normalCrystal hlam').ε i (centralTransport χ hχ π) = (normalCrystal hlam).ε i π := by
  simpa only [NormalCrystal.weightTwist_ε, coe_centralTransportIsoZero] using
    (centralTransportIsoZero hlam χ
      (toLinearMap_coroot_eq_zero_of_forall_coroot'_eq_zero hχ)).ε_apply i π

/-- `centralTransport χ` preserves the crystal string lengths `φ_i`. -/
@[simp]
theorem normalCrystal_φ_centralTransport {lam χ : X}
    (hlam : lam ∈ dominantChamber P b) {hlam' : lam + χ ∈ dominantChamber P b}
    {hχ : ∀ i ∈ b.support, P.coroot' i χ = 0} (i : b.support) (π : LSPath P b lam) :
    (normalCrystal hlam').φ i (centralTransport χ hχ π) = (normalCrystal hlam).φ i π := by
  simpa only [NormalCrystal.weightTwist_φ, coe_centralTransportIsoZero] using
    (centralTransportIsoZero hlam χ
      (toLinearMap_coroot_eq_zero_of_forall_coroot'_eq_zero hχ)).φ_apply i π

/-- In any compatible realization `(f, F)` (without injectivity or ray-separation assumptions on
`f`), raising a centrally transported LS path raises the original LS path and centrally transports
the result. -/
theorem raise_toPLPath_centralTransport {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] {f : X →+ V} {F : b.support → Dual 𝕜 V}
    {lam χ : X} (hlam : lam ∈ dominantChamber P b)
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    PLPath.raise (F i) (f (P.root i)) ((centralTransport χ hχ π).toPLPath 𝕜 f) =
      ((normalCrystal hlam).e i π).map fun ρ ↦ (centralTransport χ hχ ρ).toPLPath 𝕜 f := by
  have hlam' := add_mem_dominantChamber_of_forall_coroot_eq_zero hlam
    (toLinearMap_coroot_eq_zero_of_forall_coroot'_eq_zero hχ)
  rw [← map_toPLPath_normalCrystal_e hlam' hF, normalCrystal_e_centralTransport hlam,
    Option.map_map]
  rfl

/-- In any compatible realization `(f, F)` (without injectivity or ray-separation assumptions on
`f`), lowering a centrally transported LS path lowers the original LS path and centrally transports
the result. -/
theorem lower_toPLPath_centralTransport {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] {f : X →+ V} {F : b.support → Dual 𝕜 V}
    {lam χ : X} (hlam : lam ∈ dominantChamber P b)
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (π : LSPath P b lam) :
    PLPath.lower (F i) (f (P.root i)) ((centralTransport χ hχ π).toPLPath 𝕜 f) =
      ((normalCrystal hlam).f i π).map fun ρ ↦ (centralTransport χ hχ ρ).toPLPath 𝕜 f := by
  have hlam' := add_mem_dominantChamber_of_forall_coroot_eq_zero hlam
    (toLinearMap_coroot_eq_zero_of_forall_coroot'_eq_zero hχ)
  rw [← map_toPLPath_normalCrystal_f hlam' hF, normalCrystal_f_centralTransport hlam,
    Option.map_map]
  rfl

/-! ### The two-offset strict crystal isomorphism `T_{λ, χ}^σ : B(λ)^(σ + χ) ≃ B(λ + χ)^σ` -/

/-- **Two-offset crystal central transport `T_{λ, χ}^σ : B(λ)^(σ + χ) ≃ B(λ + χ)^σ`.**
For central weights `χ, σ ∈ X` and dominant `λ ∈ X`, `LSPath.centralTransport χ` is a strict
isomorphism from `(normalCrystal hlam).weightTwist (σ + χ)` onto
`(normalCrystal hlam').weightTwist σ`. Its underlying path bijection is independent of `σ`. -/
noncomputable def centralTransportIso {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    NormalCrystal.StrictIso
      ((normalCrystal hlam).weightTwist (σ + χ) (by simp [map_add, hσ, hχ]))
      ((normalCrystal (add_mem_dominantChamber_of_forall_coroot_eq_zero hlam hχ)).weightTwist
        σ hσ) where
  toEquiv := centralTransport χ (coroot'_eq_zero_of_forall_coroot_eq_zero hχ)
  wt_toFun π := by
    simp only [Equiv.toFun_as_coe, NormalCrystal.weightTwist_wt,
      normalCrystal_wt_centralTransport hlam]
    rw [add_assoc, add_comm χ σ, ← add_assoc]
  e_toFun i π := by
    simp only [Equiv.toFun_as_coe, NormalCrystal.weightTwist_e,
      normalCrystal_e_centralTransport hlam]

@[simp]
theorem coe_centralTransportIso {lam : X} {hlam : lam ∈ dominantChamber P b}
    {χ σ : X}
    {hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0}
    {hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0} :
    ⇑(centralTransportIso hlam χ σ hχ hσ) =
      centralTransport χ (coroot'_eq_zero_of_forall_coroot_eq_zero hχ) :=
  (rfl)

/-- The underlying path map of `centralTransportIso` is independent of the auxiliary twist `σ`. -/
theorem centralTransportIso_apply_eq {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ σ₁ σ₂ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ₁ : ∀ i : b.support, P.toLinearMap σ₁ (P.coroot i) = 0)
    (hσ₂ : ∀ i : b.support, P.toLinearMap σ₂ (P.coroot i) = 0)
    (π : LSPath P b lam) :
    centralTransportIso hlam χ σ₁ hχ hσ₁ π = centralTransportIso hlam χ σ₂ hχ hσ₂ π :=
  (rfl)

private noncomputable def castCrystalIso {lam₁ lam₂ : X}
    (hlam₁ : lam₁ ∈ dominantChamber P b) (hlam₂ : lam₂ ∈ dominantChamber P b)
    {σ₁ σ₂ : X}
    (hσ₁ : ∀ i : b.support, P.toLinearMap σ₁ (P.coroot i) = 0)
    (hσ₂ : ∀ i : b.support, P.toLinearMap σ₂ (P.coroot i) = 0)
    (hlam_eq : lam₁ = lam₂) (hσ_eq : σ₁ = σ₂) :
    NormalCrystal.StrictIso
      ((normalCrystal hlam₁).weightTwist σ₁ hσ₁)
      ((normalCrystal hlam₂).weightTwist σ₂ hσ₂) := by
  subst hlam_eq
  subst hσ_eq
  exact NormalCrystal.StrictIso.refl _

@[simp]
private theorem dirVals_castCrystalIso {lam₁ lam₂ : X}
    {hlam₁ : lam₁ ∈ dominantChamber P b} {hlam₂ : lam₂ ∈ dominantChamber P b}
    {σ₁ σ₂ : X}
    {hσ₁ : ∀ i : b.support, P.toLinearMap σ₁ (P.coroot i) = 0}
    {hσ₂ : ∀ i : b.support, P.toLinearMap σ₂ (P.coroot i) = 0}
    {hlam_eq : lam₁ = lam₂} {hσ_eq : σ₁ = σ₂} (π : LSPath P b lam₁) :
    dirVals (castCrystalIso hlam₁ hlam₂ hσ₁ hσ₂ hlam_eq hσ_eq π) = dirVals π := by
  subst hlam_eq
  subst hσ_eq
  simp [castCrystalIso]

@[simp]
private theorem times_castCrystalIso {lam₁ lam₂ : X}
    {hlam₁ : lam₁ ∈ dominantChamber P b} {hlam₂ : lam₂ ∈ dominantChamber P b}
    {σ₁ σ₂ : X}
    {hσ₁ : ∀ i : b.support, P.toLinearMap σ₁ (P.coroot i) = 0}
    {hσ₂ : ∀ i : b.support, P.toLinearMap σ₂ (P.coroot i) = 0}
    {hlam_eq : lam₁ = lam₂} {hσ_eq : σ₁ = σ₂} (π : LSPath P b lam₁) :
    times (castCrystalIso hlam₁ hlam₂ hσ₁ hσ₂ hlam_eq hσ_eq π) = times π := by
  subst hlam_eq
  subst hσ_eq
  simp [castCrystalIso]

/-- **Two-offset crystal central transport `T_{λ, χ}^σ` with propositionally equal endpoints.**
Given `λ + χ = μ` and `σ + χ = τ`, this is `centralTransportIso` typed directly as a strict crystal
isomorphism `B(λ)^τ ≃ B(μ)^σ`, allowing the identity, composition, and inverse laws (as well as
`λ + χ = 0` specializations) to be stated with identical weighted-crystal endpoints and without
dependent casts. -/
noncomputable def centralTransportIsoOfEq {lam μ : X}
    (hlam : lam ∈ dominantChamber P b) (hμ : μ ∈ dominantChamber P b)
    (χ σ τ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hτ : ∀ i : b.support, P.toLinearMap τ (P.coroot i) = 0)
    (hμ_eq : lam + χ = μ) (hτ_eq : σ + χ = τ) :
    NormalCrystal.StrictIso
      ((normalCrystal hlam).weightTwist τ hτ)
      ((normalCrystal hμ).weightTwist σ hσ) :=
  ((castCrystalIso hlam hlam hτ (by simp [map_add, hσ, hχ]) rfl hτ_eq.symm).trans
    (centralTransportIso hlam χ σ hχ hσ)).trans
    (castCrystalIso (add_mem_dominantChamber_of_forall_coroot_eq_zero hlam hχ) hμ
      hσ hσ hμ_eq rfl)

@[simp]
private theorem dirVals_centralTransportIsoOfEq {lam μ : X}
    {hlam : lam ∈ dominantChamber P b} {hμ : μ ∈ dominantChamber P b}
    {χ σ τ : X}
    {hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0}
    {hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0}
    {hτ : ∀ i : b.support, P.toLinearMap τ (P.coroot i) = 0}
    {hμ_eq : lam + χ = μ} {hτ_eq : σ + χ = τ} (π : LSPath P b lam) :
    dirVals (centralTransportIsoOfEq hlam hμ χ σ τ hχ hσ hτ hμ_eq hτ_eq π) = dirVals π := by
  simp [centralTransportIsoOfEq]

@[simp]
private theorem times_centralTransportIsoOfEq {lam μ : X}
    {hlam : lam ∈ dominantChamber P b} {hμ : μ ∈ dominantChamber P b}
    {χ σ τ : X}
    {hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0}
    {hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0}
    {hτ : ∀ i : b.support, P.toLinearMap τ (P.coroot i) = 0}
    {hμ_eq : lam + χ = μ} {hτ_eq : σ + χ = τ} (π : LSPath P b lam) :
    times (centralTransportIsoOfEq hlam hμ χ σ τ hχ hσ hτ hμ_eq hτ_eq π) = times π := by
  simp [centralTransportIsoOfEq]

@[simp]
theorem length_centralTransportIsoOfEq {lam μ : X}
    {hlam : lam ∈ dominantChamber P b} {hμ : μ ∈ dominantChamber P b}
    {χ σ τ : X}
    {hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0}
    {hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0}
    {hτ : ∀ i : b.support, P.toLinearMap τ (P.coroot i) = 0}
    {hμ_eq : lam + χ = μ} {hτ_eq : σ + χ = τ} (π : LSPath P b lam) :
    (centralTransportIsoOfEq hlam hμ χ σ τ hχ hσ hτ hμ_eq hτ_eq π).length = π.length := by
  have h := congrArg List.length
    (dirVals_centralTransportIsoOfEq (hlam := hlam) (hμ := hμ) (hχ := hχ) (hσ := hσ) (hτ := hτ)
      (hμ_eq := hμ_eq) (hτ_eq := hτ_eq) π)
  simpa [dirVals] using h

/-- For reflexivity proofs, `centralTransportIsoOfEq` coincides with `centralTransportIso`. -/
@[simp]
theorem centralTransportIsoOfEq_rfl {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    centralTransportIsoOfEq hlam
      (add_mem_dominantChamber_of_forall_coroot_eq_zero hlam hχ)
      χ σ (σ + χ) hχ hσ (by simp [map_add, hσ, hχ]) rfl rfl =
      centralTransportIso hlam χ σ hχ hσ :=
  NormalCrystal.StrictIso.ext fun π ↦ ext_of_dirVals_of_times (by simp) (by simp)

/-- Realizing `centralTransportIsoOfEq` gives the realized path of `centralTransport χ`. -/
@[simp]
theorem toPLPath_centralTransportIsoOfEq {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (f : X →+ V)
    {lam μ : X} {hlam : lam ∈ dominantChamber P b} {hμ : μ ∈ dominantChamber P b}
    {χ σ τ : X}
    {hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0}
    {hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0}
    {hτ : ∀ i : b.support, P.toLinearMap τ (P.coroot i) = 0}
    {hμ_eq : lam + χ = μ} {hτ_eq : σ + χ = τ} (π : LSPath P b lam) :
    (centralTransportIsoOfEq hlam hμ χ σ τ hχ hσ hτ hμ_eq hτ_eq π).toPLPath 𝕜 f =
      (centralTransport χ (coroot'_eq_zero_of_forall_coroot_eq_zero hχ) π).toPLPath 𝕜 f := by
  subst hμ_eq
  subst hτ_eq
  rw [centralTransportIsoOfEq_rfl, coe_centralTransportIso]

/-- The underlying path map of `centralTransportIsoOfEq` is independent of the twist offsets `σ`
and `τ`. -/
theorem centralTransportIsoOfEq_apply_indep {lam μ : X}
    (hlam : lam ∈ dominantChamber P b) (hμ : μ ∈ dominantChamber P b)
    (χ σ₁ τ₁ σ₂ τ₂ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ₁ : ∀ i : b.support, P.toLinearMap σ₁ (P.coroot i) = 0)
    (hτ₁ : ∀ i : b.support, P.toLinearMap τ₁ (P.coroot i) = 0)
    (hσ₂ : ∀ i : b.support, P.toLinearMap σ₂ (P.coroot i) = 0)
    (hτ₂ : ∀ i : b.support, P.toLinearMap τ₂ (P.coroot i) = 0)
    (hμ_eq : lam + χ = μ) (hτ₁_eq : σ₁ + χ = τ₁) (hτ₂_eq : σ₂ + χ = τ₂)
    (π : LSPath P b lam) :
    centralTransportIsoOfEq hlam hμ χ σ₁ τ₁ hχ hσ₁ hτ₁ hμ_eq hτ₁_eq π =
      centralTransportIsoOfEq hlam hμ χ σ₂ τ₂ hχ hσ₂ hτ₂ hμ_eq hτ₂_eq π :=
  ext_of_dirVals_of_times (by simp) (by simp)

/-- At `σ = 0`, `centralTransportIso` agrees on elements with `centralTransportIsoZero`. -/
theorem centralTransportIso_zero_right_apply {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) (π : LSPath P b lam) :
    centralTransportIso hlam χ 0 hχ (by simp) π = centralTransportIsoZero hlam χ hχ π :=
  (rfl)

/-- **Strict-isomorphism identity law `T_{λ, 0}^σ = id`.** -/
@[simp]
theorem centralTransportIsoOfEq_zero {lam : X} (hlam : lam ∈ dominantChamber P b)
    (σ : X) (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    centralTransportIsoOfEq hlam hlam 0 σ σ (by simp) hσ hσ (add_zero lam) (add_zero σ) =
      NormalCrystal.StrictIso.refl ((normalCrystal hlam).weightTwist σ hσ) :=
  NormalCrystal.StrictIso.ext fun π ↦ ext_of_dirVals_of_times (by simp) (by simp)

/-- **Additive composition law `T_{λ + χ, ψ}^σ ∘ T_{λ, χ}^{σ + ψ} = T_{λ, χ + ψ}^σ`** in general
propositional-endpoint form: source, intermediate crystal, and target are identical weighted
crystals. -/
@[simp]
theorem centralTransportIsoOfEq_trans {lam μ ν : X}
    (hlam : lam ∈ dominantChamber P b)
    (hμ : μ ∈ dominantChamber P b)
    (hν : ν ∈ dominantChamber P b)
    (χ ψ σ ρ τ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hψ : ∀ i : b.support, P.toLinearMap ψ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hρ : ∀ i : b.support, P.toLinearMap ρ (P.coroot i) = 0)
    (hτ : ∀ i : b.support, P.toLinearMap τ (P.coroot i) = 0)
    (hμ_eq : lam + χ = μ) (hν_eq : μ + ψ = ν)
    (hρ_eq : σ + ψ = ρ) (hτ_eq : ρ + χ = τ) :
    (centralTransportIsoOfEq hlam hμ χ ρ τ hχ hρ hτ hμ_eq hτ_eq).trans
      (centralTransportIsoOfEq hμ hν ψ σ ρ hψ hσ hρ hν_eq hρ_eq) =
      centralTransportIsoOfEq hlam hν (χ + ψ) σ τ
        (by simp [map_add, hχ, hψ]) hσ hτ
        (by rw [← add_assoc, hμ_eq, hν_eq])
        (by rw [← hτ_eq, ← hρ_eq]; abel) :=
  NormalCrystal.StrictIso.ext fun π ↦ ext_of_dirVals_of_times (by simp) (by simp)

/-- **Additive composition law `T_{λ + χ, ψ}^σ ∘ T_{λ, χ}^{σ + ψ} = T_{λ, χ + ψ}^σ`** directly on
`centralTransportIso`. -/
theorem centralTransportIso_trans {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ ψ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hψ : ∀ i : b.support, P.toLinearMap ψ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    (centralTransportIso hlam χ (σ + ψ) hχ (by simp [map_add, hσ, hψ])).trans
      (centralTransportIso (add_mem_dominantChamber_of_forall_coroot_eq_zero hlam hχ)
        ψ σ hψ hσ) =
      centralTransportIsoOfEq hlam
        (add_mem_dominantChamber_of_forall_coroot_eq_zero
          (add_mem_dominantChamber_of_forall_coroot_eq_zero hlam hχ) hψ)
        (χ + ψ) σ ((σ + ψ) + χ)
        (by simp [map_add, hχ, hψ]) hσ (by simp [map_add, hσ, hψ, hχ])
        (add_assoc lam χ ψ).symm (by abel) :=
  NormalCrystal.StrictIso.ext fun π ↦ ext_of_dirVals_of_times (by simp) (by simp)

/-- **Inverse formula `(T_{λ, χ}^σ)⁻¹ = T_{λ + χ, -χ}^{σ + χ}`** in general propositional-endpoint
form. -/
@[simp]
theorem centralTransportIsoOfEq_symm {lam μ : X}
    (hlam : lam ∈ dominantChamber P b) (hμ : μ ∈ dominantChamber P b)
    (χ σ τ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hτ : ∀ i : b.support, P.toLinearMap τ (P.coroot i) = 0)
    (hμ_eq : lam + χ = μ) (hτ_eq : σ + χ = τ) :
    (centralTransportIsoOfEq hlam hμ χ σ τ hχ hσ hτ hμ_eq hτ_eq).symm =
      centralTransportIsoOfEq hμ hlam (-χ) τ σ
        (by simp [hχ]) hτ hσ
        (by rw [← hμ_eq, add_neg_cancel_right])
        (by rw [← hτ_eq, add_neg_cancel_right]) := by
  refine NormalCrystal.StrictIso.ext fun π ↦ ext_of_dirVals_of_times ?_ ?_
  · rw [← dirVals_centralTransportIsoOfEq (hlam := hlam) (hμ := hμ) (hχ := hχ) (hσ := hσ)
      (hτ := hτ) (hμ_eq := hμ_eq) (hτ_eq := hτ_eq)
      ((centralTransportIsoOfEq hlam hμ χ σ τ hχ hσ hτ hμ_eq hτ_eq).symm π)]
    simp
  · rw [← times_centralTransportIsoOfEq (hlam := hlam) (hμ := hμ) (hχ := hχ) (hσ := hσ)
      (hτ := hτ) (hμ_eq := hμ_eq) (hτ_eq := hτ_eq)
      ((centralTransportIsoOfEq hlam hμ χ σ τ hχ hσ hτ hμ_eq hτ_eq).symm π)]
    simp

/-- **Inverse formula `(T_{λ, χ}^σ)⁻¹ = T_{λ + χ, -χ}^{σ + χ}`** directly on
`centralTransportIso`. -/
theorem centralTransportIso_symm {lam : X} (hlam : lam ∈ dominantChamber P b)
    (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0) :
    (centralTransportIso hlam χ σ hχ hσ).symm =
      centralTransportIsoOfEq
        (add_mem_dominantChamber_of_forall_coroot_eq_zero hlam hχ) hlam
        (-χ) (σ + χ) σ
        (by simp [hχ]) (by simp [map_add, hσ, hχ]) hσ
        (add_neg_cancel_right lam χ) (add_neg_cancel_right σ χ) := by
  rw [← centralTransportIsoOfEq_rfl, centralTransportIsoOfEq_symm]

/-! ### Pure central shapes, `λ + χ = 0`, and empty root systems -/

/-- For a weight `χ` annihilating all simple coroots (including `χ = 0` and any weight of an empty
root system), `straight χ` is the unique Lakshmibai–Seshadri path of shape `χ`. -/
theorem eq_straight_of_forall_coroot_eq_zero {χ : X}
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) (π : LSPath P b χ) :
    π = straight χ := by
  have hdom := mem_dominantChamber_of_forall_coroot_eq_zero hχ
  have hf_none (i : b.support) : (normalCrystal hdom).f i (straight χ) = none := by
    rw [← (normalCrystal hdom).φ_eq_zero_iff]
    have hdiff := (normalCrystal hdom).φ_sub_ε i (straight χ)
    rw [normalCrystal_ε_straight, normalCrystal_wt_straight, hχ i] at hdiff
    omega
  obtain ⟨w, hw⟩ := exists_fWord_straight_eq_some hdom π
  cases w with
  | nil =>
    rw [NormalCrystal.fWord_nil, Option.some.injEq] at hw
    exact hw.symm
  | cons i w =>
    simp [NormalCrystal.fWord_cons, hf_none i] at hw

/-- **The LS path crystal of a pure central weight `χ` is strictly isomorphic to
`NormalCrystal.central χ`.** This covers `χ = 0` as well as arbitrary weights when `b.support` is
empty. -/
noncomputable def pureCentralCrystalIso (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    NormalCrystal.StrictIso
      (NormalCrystal.central χ hχ)
      (normalCrystal (mem_dominantChamber_of_forall_coroot_eq_zero hχ)) where
  toEquiv :=
    { toFun := fun _ ↦ straight χ
      invFun := fun _ ↦ PUnit.unit
      left_inv := fun _ ↦ rfl
      right_inv := fun π ↦ (eq_straight_of_forall_coroot_eq_zero hχ π).symm }
  wt_toFun _ := by simp
  e_toFun _ _ := by simp

@[simp]
theorem pureCentralCrystalIso_apply (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) (u : PUnit) :
    pureCentralCrystalIso χ hχ u = straight χ :=
  (rfl)

@[simp]
theorem pureCentralCrystalIso_symm_apply (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) (π : LSPath P b χ) :
    (pureCentralCrystalIso χ hχ).symm π = PUnit.unit :=
  (rfl)

/-- **Central transport to shape `0` (`λ + χ = 0`).** For a pure central weight `λ` and `χ = -λ`
(or any `λ + χ = 0`), `centralTransportIsoOfEq` gives a strict crystal isomorphism onto the
`σ`-twisted zero-shape LS crystal `(normalCrystal (zero_mem_dominantChamber P b)).weightTwist σ`. -/
noncomputable def centralTransportIsoToZero {lam χ σ : X}
    (hlam : lam ∈ dominantChamber P b)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hzero : lam + χ = 0) :
    NormalCrystal.StrictIso
      ((normalCrystal hlam).weightTwist (σ + χ) (by simp [map_add, hσ, hχ]))
      ((normalCrystal (zero_mem_dominantChamber P b)).weightTwist σ hσ) :=
  centralTransportIsoOfEq hlam (zero_mem_dominantChamber P b) χ σ (σ + χ)
    hχ hσ (by simp [map_add, hσ, hχ]) hzero rfl

theorem centralTransportIsoToZero_eq {lam χ σ : X}
    (hlam : lam ∈ dominantChamber P b)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hzero : lam + χ = 0) :
    centralTransportIsoToZero hlam hχ hσ hzero =
      centralTransportIsoOfEq hlam (zero_mem_dominantChamber P b) χ σ (σ + χ)
        hχ hσ (by simp [map_add, hσ, hχ]) hzero rfl :=
  (rfl)

end CrystalTransport

end TauCeti.LSPath
