/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
import Mathlib.RingTheory.Ideal.Maps

/-!
# Isomorphisms of topological rings induce homeomorphisms of adic spectra

An isomorphism of topological commutative rings `e : A ≃+* B` carrying `A⁺ ⊆ A` onto `B⁺ ⊆ B`
induces a contravariant homeomorphism `Spa (B, B⁺) ≃ₜ Spa (A, A⁺)` (`spaHomeomorphOfRingEquiv`) by
valuation pullback along `e`, matching `spaRationalFamily` without Huber or separation hypotheses.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.23 and Remark 7.30.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {A B C : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
  [CommRing C] [TopologicalSpace C]

/-- A topological ring isomorphism `e : A ≃+* B` carrying `A⁺` onto `B⁺` induces a homeomorphism
`Spa (B, B⁺) ≃ₜ Spa (A, A⁺)` by pullback of valuations along `e`. -/
def spaHomeomorphOfRingEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {Aplus : Subring A} {Bplus : Subring B}
    (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus) :
    spa Bplus ≃ₜ spa Aplus where
  toFun := spaComap (e : A →+* B) he Aplus Bplus hplus
  invFun := spaComap (e.symm : B →+* A) he' Bplus Aplus hplus'
  left_inv := spaComap_spaComap (e.symm : B →+* A) he' hplus' (e : A →+* B) he
    e.apply_symm_apply hplus
  right_inv := spaComap_spaComap (e : A →+* B) he hplus (e.symm : B →+* A) he'
    e.symm_apply_apply hplus'
  continuous_toFun := continuous_spaComap (e : A →+* B) he Aplus Bplus hplus
  continuous_invFun := continuous_spaComap (e.symm : B →+* A) he' Bplus Aplus hplus'

section Equiv

variable (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) {Aplus : Subring A}
  {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, e a ∈ Bplus) (hplus' : ∀ b ∈ Bplus, e.symm b ∈ Aplus)

/-- Abbreviate `spaHomeomorphOfRingEquiv` applied to the section variables. -/
local macro "reHomeo" : term =>
  let i := Lean.mkIdent
  `(spaHomeomorphOfRingEquiv $(i `e) $(i `he) $(i `he') $(i `hplus) $(i `hplus'))

/-- `spaHomeomorphOfRingEquiv` acts on points as `spaComap` along `e`. -/
@[simp] theorem spaHomeomorphOfRingEquiv_apply (v : spa Bplus) :
    reHomeo v = spaComap (e : A →+* B) he Aplus Bplus hplus v := (rfl)

/-- As a function, `spaHomeomorphOfRingEquiv` is `spaComap` along `e`. -/
@[simp] theorem coe_spaHomeomorphOfRingEquiv :
    ⇑reHomeo = spaComap (e : A →+* B) he Aplus Bplus hplus :=
  funext (spaHomeomorphOfRingEquiv_apply e he he' hplus hplus')

/-- The inverse of `spaHomeomorphOfRingEquiv` acts on points as `spaComap` along `e.symm`. -/
@[simp] theorem spaHomeomorphOfRingEquiv_symm_apply (v : spa Aplus) :
    (reHomeo).symm v = spaComap (e.symm : B →+* A) he' Bplus Aplus hplus' v := (rfl)

/-- As a function, `(spaHomeomorphOfRingEquiv e ...).symm` is `spaComap` along `e.symm`. -/
@[simp] theorem coe_spaHomeomorphOfRingEquiv_symm :
    ⇑(reHomeo).symm = spaComap (e.symm : B →+* A) he' Bplus Aplus hplus' :=
  funext (spaHomeomorphOfRingEquiv_symm_apply e he he' hplus hplus')

/-- On `Spv`, `spaHomeomorphOfRingEquiv` acts as `ValuationSpectrum.comap` along `e`. -/
theorem spaHomeomorphOfRingEquiv_val (v : spa Bplus) : (reHomeo v).1 = comap (e : A →+* B) v.1 :=
  spaComap_val (e : A →+* B) he Aplus Bplus hplus v

/-- On `Spv`, `(spaHomeomorphOfRingEquiv e ...).symm` acts as `comap` along `e.symm`. -/
theorem spaHomeomorphOfRingEquiv_symm_val (v : spa Aplus) :
    ((reHomeo).symm v).1 = comap (e.symm : B →+* A) v.1 :=
  spaComap_val (e.symm : B →+* A) he' Bplus Aplus hplus' v

/-- The inverse of `spaHomeomorphOfRingEquiv` is `spaHomeomorphOfRingEquiv` for `e.symm`. -/
theorem spaHomeomorphOfRingEquiv_symm :
    (reHomeo).symm = spaHomeomorphOfRingEquiv e.symm he' he hplus' hplus :=
  Homeomorph.ext fun _ ↦ rfl

/-- Preimage under `spaHomeomorphOfRingEquiv` preserves `spaRationalFamily`. -/
theorem spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily
    {U : Set (spa Aplus)} (hU : U ∈ spaRationalFamily Aplus) :
    reHomeo ⁻¹' U ∈ spaRationalFamily Bplus := by
  rw [coe_spaHomeomorphOfRingEquiv]
  refine spaComap_preimage_mem_spaRationalFamily (e : A →+* B) he Aplus Bplus hplus (fun J hJ ↦ ?_)
    hU
  have hmap : Ideal.map (e : A →+* B) J = J.comap e.symm := (Ideal.comap_symm e).symm
  rw [hmap, Ideal.coe_comap]; exact hJ.preimage he'

/-- Image under `spaHomeomorphOfRingEquiv` preserves `spaRationalFamily`. -/
theorem spaHomeomorphOfRingEquiv_image_mem_spaRationalFamily
    {V : Set (spa Bplus)} (hV : V ∈ spaRationalFamily Bplus) :
    reHomeo '' V ∈ spaRationalFamily Aplus := by
  rw [Homeomorph.image_eq_preimage_symm, spaHomeomorphOfRingEquiv_symm]
  exact spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e.symm he' he hplus' hplus hV

/-- Membership in `spaRationalFamily` is preserved and reflected by preimage. -/
theorem spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily_iff {U : Set (spa Aplus)} :
    reHomeo ⁻¹' U ∈ spaRationalFamily Bplus ↔ U ∈ spaRationalFamily Aplus := by
  refine ⟨fun h ↦ ?_, spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e he he' hplus hplus'⟩
  have himage := spaHomeomorphOfRingEquiv_image_mem_spaRationalFamily e he he' hplus hplus' h
  rwa [Set.image_preimage_eq _ (reHomeo).surjective] at himage

/-- Preimage under `spaHomeomorphOfRingEquiv` bijects `spaRationalFamily Aplus` onto
`spaRationalFamily Bplus`. -/
theorem bijOn_preimage_spaHomeomorphOfRingEquiv_spaRationalFamily :
    Set.BijOn (fun U : Set (spa Aplus) ↦ reHomeo ⁻¹' U)
      (spaRationalFamily Aplus) (spaRationalFamily Bplus) :=
  ⟨fun _ hU ↦ spaHomeomorphOfRingEquiv_preimage_mem_spaRationalFamily e he he' hplus hplus' hU,
    (reHomeo).surjective.preimage_injective.injOn,
    fun V hV ↦ ⟨reHomeo '' V,
      spaHomeomorphOfRingEquiv_image_mem_spaRationalFamily e he he' hplus hplus' hV,
      (reHomeo).preimage_image V⟩⟩

end Equiv

/-- `spaHomeomorphOfRingEquiv` of `RingEquiv.refl` is `Homeomorph.refl`. -/
@[simp] theorem spaHomeomorphOfRingEquiv_refl (Aplus : Subring A) :
    spaHomeomorphOfRingEquiv (RingEquiv.refl A) continuous_id continuous_id
      (Aplus := Aplus) (Bplus := Aplus) (fun _ ha ↦ ha) (fun _ ha ↦ ha) =
      Homeomorph.refl (spa Aplus) :=
  Homeomorph.ext fun v ↦ congr_fun (spaComap_id Aplus) v

/-- `spaHomeomorphOfRingEquiv` is contravariantly functorial for `RingEquiv.trans`. -/
@[simp] theorem spaHomeomorphOfRingEquiv_trans (e₁ : A ≃+* B) (he₁ : Continuous e₁)
    (he₁' : Continuous e₁.symm) (e₂ : B ≃+* C) (he₂ : Continuous e₂) (he₂' : Continuous e₂.symm)
    {Aplus : Subring A} {Bplus : Subring B} {Cplus : Subring C}
    (hplus₁ : ∀ a ∈ Aplus, e₁ a ∈ Bplus) (hplus₁' : ∀ b ∈ Bplus, e₁.symm b ∈ Aplus)
    (hplus₂ : ∀ b ∈ Bplus, e₂ b ∈ Cplus) (hplus₂' : ∀ c ∈ Cplus, e₂.symm c ∈ Bplus) :
    spaHomeomorphOfRingEquiv (e₁.trans e₂) (he₂.comp he₁) (he₁'.comp he₂')
        (fun a ha ↦ hplus₂ (e₁ a) (hplus₁ a ha)) (fun c hc ↦ hplus₁' (e₂.symm c) (hplus₂' c hc)) =
      (spaHomeomorphOfRingEquiv e₂ he₂ he₂' hplus₂ hplus₂').trans
        (spaHomeomorphOfRingEquiv e₁ he₁ he₁' hplus₁ hplus₁') :=
  Homeomorph.ext fun v ↦ congr_fun
    (spaComap_comp (φ := (e₁ : A →+* B)) he₁ (ψ := (e₂ : B →+* C)) he₂
      Aplus Bplus Cplus hplus₁ hplus₂) v

end TauCeti.ValuationSpectrum

end
