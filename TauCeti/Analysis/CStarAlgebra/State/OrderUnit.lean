/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.Algebra.Order.Star
public import TauCeti.Analysis.CStarAlgebra.State.Space
public import TauCeti.Analysis.Normed.Order.OrderUnit.State
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.Algebra.Module.Star
import TauCeti.Analysis.CStarAlgebra.SelfAdjointSpectrumInterval

/-!
# Self-adjoint order-unit structure and state-space homeomorphism for C⋆-algebras

For a nontrivial unital normed star-ordered algebra `A` with an isometric real continuous functional
calculus (in particular any nontrivial unital real or complex C⋆-algebra), the self-adjoint part
`selfAdjoint A` with unit `(1 : selfAdjoint A)` is an order-unit normed space
(`TauCeti.OrderUnit.isOrderUnitNorm_one_selfAdjoint`): `‖(1 : selfAdjoint A)‖ = 1`, and for `r ≥ 0`
one has `‖x‖ ≤ r ↔ -r • 1 ≤ x ∧ x ≤ r • 1` via `IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc`.

On a unital complex C⋆-algebra `A`, taking the real part on `selfAdjoint A` defines a weak-star
continuous `ℝ`-linear map
`TauCeti.restrictSelfAdjoint : WeakDual ℂ A →L[ℝ] WeakDual ℝ (selfAdjoint A)`, and Cartesian
decomposition `a = ℜ a + I • ℑ a` defines a weak-star continuous `ℝ`-linear right inverse
`TauCeti.extendSelfAdjoint : WeakDual ℝ (selfAdjoint A) →L[ℝ] WeakDual ℂ A`. Because states of `A`
are real-valued on `selfAdjoint A` and determined by their values on nonnegative elements
(`WeakDual.ext_nonneg`), these maps restrict to mutually inverse affine maps and induce a weak-star
homeomorphism `TauCeti.stateSpaceHomeomorphOrderUnit` between `TauCeti.stateSpace A` and
`TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`.

## References

* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras*, Vol. I,
  §4.3.
* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. **4** (1999), 559–600, §1.
-/

public section

open Set WeakDual
open scoped ComplexOrder ComplexStarModule

namespace TauCeti.OrderUnit

/-- **Self-adjoint part as an order-unit normed space.** In a normed star-ordered real algebra `A`
with `[NormOneClass A]` and an isometric continuous functional calculus for self-adjoint elements
(in particular any nontrivial unital C⋆-algebra), `(1 : selfAdjoint A)` satisfies
`IsOrderUnitNorm`. -/
theorem isOrderUnitNorm_one_selfAdjoint {A : Type*} [NormedRing A] [StarRing A]
    [PartialOrder A] [StarOrderedRing A] [NormedAlgebra ℝ A] [StarModule ℝ A]
    [NonnegSpectrumClass ℝ A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [NormOneClass A] :
    IsOrderUnitNorm (1 : selfAdjoint A) where
  norm_eq_one := norm_one (α := A)
  norm_le_iff x r hr := by
    change ‖(x : A)‖ ≤ r ↔ (-r) • (1 : A) ≤ (x : A) ∧ (x : A) ≤ r • (1 : A)
    rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
      x.2.norm_le_iff_spectrum_subset_Icc hr,
      algebraMap_le_iff_le_spectrum (ha := x.2),
      le_algebraMap_iff_spectrum_le (ha := x.2)]
    exact ⟨fun h => ⟨fun _ hs => (h hs).1, fun _ hs => (h hs).2⟩,
      fun ⟨h1, h2⟩ _ hs => ⟨h1 _ hs, h2 _ hs⟩⟩

end TauCeti.OrderUnit

namespace TauCeti

section RestrictExtend

variable (A : Type*) [CStarAlgebra A]

/-- Weak-star continuous `ℝ`-linear restriction sending `ω : WeakDual ℂ A` to the real functional
`x ↦ (ω x).re` on `selfAdjoint A`. -/
noncomputable def restrictSelfAdjoint : WeakDual ℂ A →L[ℝ] WeakDual ℝ (selfAdjoint A) where
  toFun ω := StrongDual.toWeakDual
    { toFun x := (ω (x : A)).re
      map_add' x y := by simp
      map_smul' r x := by
        change (ω (r • (x : A))).re = r • (ω (x : A)).re
        rw [← Complex.coe_smul, map_smul]
        simp
      cont := Complex.continuous_re.comp
        ((toStrongDual ω).continuous.comp continuous_subtype_val) }
  map_add' _ _ := DFunLike.ext _ _ fun _ => rfl
  map_smul' r ω := DFunLike.ext _ _ fun x => by
    change (r • ω (x : A)).re = r * (ω (x : A)).re
    rw [Complex.real_smul]
    simp
  cont := WeakDual.continuous_of_continuous_eval fun x =>
    Complex.continuous_re.comp (eval_continuous (x : A))

/-- `restrictSelfAdjoint A ω` evaluates at `x : selfAdjoint A` as `(ω x).re`. -/
@[simp]
theorem restrictSelfAdjoint_apply (ω : WeakDual ℂ A) (x : selfAdjoint A) :
    restrictSelfAdjoint A ω x = (ω (x : A)).re :=
  (rfl)

private theorem continuous_realPart : Continuous (fun a : A => ℜ a) :=
  continuous_selfAdjointPart ℝ A

private theorem continuous_imaginaryPart : Continuous (fun a : A => ℑ a) := by
  have h : (fun a : A => ℑ a) = fun a => -ℜ (Complex.I • a) := by
    ext1 a
    simp [realPart_I_smul]
  rw [h]
  exact ((continuous_selfAdjointPart ℝ A).comp (continuous_const_smul Complex.I)).neg

/-- Weak-star continuous `ℝ`-linear complexification sending a real functional
`φ : WeakDual ℝ (selfAdjoint A)` to `a ↦ φ (ℜ a) + I * φ (ℑ a)` on `A`. -/
noncomputable def extendSelfAdjoint : WeakDual ℝ (selfAdjoint A) →L[ℝ] WeakDual ℂ A where
  toFun φ := StrongDual.toWeakDual
    { toFun a := (φ (ℜ a) : ℂ) + Complex.I * (φ (ℑ a) : ℂ)
      map_add' a b := by
        simp only [map_add, Complex.ofReal_add]
        ring
      map_smul' z a := by
        rw [realPart_smul, imaginaryPart_smul, map_sub, map_add, map_smul, map_smul,
          map_smul, map_smul]
        simp only [smul_eq_mul, RingHom.id_apply]
        apply Complex.ext <;> simp
      cont :=
        (Complex.continuous_ofReal.comp
          ((toStrongDual φ).continuous.comp (continuous_realPart A))).add
          (continuous_const.mul (Complex.continuous_ofReal.comp
            ((toStrongDual φ).continuous.comp (continuous_imaginaryPart A)))) }
  map_add' φ ψ := DFunLike.ext _ _ fun a => by
    change ((φ (ℜ a) + ψ (ℜ a) : ℝ) : ℂ) + Complex.I * ((φ (ℑ a) + ψ (ℑ a) : ℝ) : ℂ) =
      ((φ (ℜ a) : ℂ) + Complex.I * (φ (ℑ a) : ℂ)) +
        ((ψ (ℜ a) : ℂ) + Complex.I * (ψ (ℑ a) : ℂ))
    push_cast
    ring
  map_smul' r φ := DFunLike.ext _ _ fun a => by
    change ((r * φ (ℜ a) : ℝ) : ℂ) + Complex.I * ((r * φ (ℑ a) : ℝ) : ℂ) =
      r • ((φ (ℜ a) : ℂ) + Complex.I * (φ (ℑ a) : ℂ))
    rw [Complex.real_smul]
    push_cast
    ring
  cont := WeakDual.continuous_of_continuous_eval fun a =>
    (Complex.continuous_ofReal.comp (eval_continuous (ℜ a))).add
      (continuous_const.mul (Complex.continuous_ofReal.comp (eval_continuous (ℑ a))))

/-- `extendSelfAdjoint A φ` evaluates via the Cartesian decomposition `a = ℜ a + I • ℑ a`. -/
@[simp]
theorem extendSelfAdjoint_apply (φ : WeakDual ℝ (selfAdjoint A)) (a : A) :
    extendSelfAdjoint A φ a = (φ (ℜ a) : ℂ) + Complex.I * (φ (ℑ a) : ℂ) :=
  (rfl)

variable {A}

/-- On a self-adjoint element `x : selfAdjoint A`, `extendSelfAdjoint A φ` agrees with `φ`. -/
theorem extendSelfAdjoint_apply_coe (φ : WeakDual ℝ (selfAdjoint A)) (x : selfAdjoint A) :
    extendSelfAdjoint A φ (x : A) = (φ x : ℂ) := by
  simp

/-- Restricting `extendSelfAdjoint A φ` to `selfAdjoint A` recovers `φ`. -/
@[simp]
theorem restrictSelfAdjoint_extendSelfAdjoint (φ : WeakDual ℝ (selfAdjoint A)) :
    restrictSelfAdjoint A (extendSelfAdjoint A φ) = φ :=
  DFunLike.ext _ _ fun x => by simp

end RestrictExtend

section StateSpaceEquiv

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Restricting a state of `A` to `selfAdjoint A` yields an order-unit state of
`(selfAdjoint A, 1)`. -/
theorem mapsTo_restrictSelfAdjoint_stateSpace :
    MapsTo (restrictSelfAdjoint A) (stateSpace A) (OrderUnit.stateSpace (1 : selfAdjoint A)) := by
  intro ω hω
  refine OrderUnit.mem_stateSpace_iff_map_nonneg.2 ⟨fun x hx => ?_, ?_⟩
  · simpa using (Complex.le_def.1 (map_nonneg_of_mem_stateSpace hω hx)).1
  · simp [map_one_of_mem_stateSpace hω]

/-- Extending an order-unit state of `(selfAdjoint A, 1)` by complex linearity yields a state of
`A`. -/
theorem mapsTo_extendSelfAdjoint_stateSpace :
    MapsTo (extendSelfAdjoint A) (OrderUnit.stateSpace (1 : selfAdjoint A)) (stateSpace A) := by
  intro φ hφ
  refine mem_stateSpace_iff_map_one.2 ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨hre, him⟩ := nonneg_iff_realPart_imaginaryPart.1 ha
    have hφre : 0 ≤ φ (ℜ a) := OrderUnit.map_nonneg_of_mem_stateSpace hφ hre
    simpa [him] using hφre
  · change extendSelfAdjoint A φ ((1 : selfAdjoint A) : A) = 1
    rw [extendSelfAdjoint_apply_coe, OrderUnit.map_unit_of_mem_stateSpace hφ, Complex.ofReal_one]

/-- A state of `A` is recovered from its real restriction to `selfAdjoint A`. -/
theorem extendSelfAdjoint_restrictSelfAdjoint_of_mem_stateSpace {ω : WeakDual ℂ A}
    (hω : ω ∈ stateSpace A) :
    extendSelfAdjoint A (restrictSelfAdjoint A ω) = ω := by
  refine WeakDual.ext_nonneg fun a ha => ?_
  have hnonneg : 0 ≤ ω a := map_nonneg_of_mem_stateSpace hω ha
  have him : (ω a).im = 0 := (Complex.le_def.1 hnonneg).2.symm
  let x : selfAdjoint A := ⟨a, ha.isSelfAdjoint⟩
  change extendSelfAdjoint A (restrictSelfAdjoint A ω) (x : A) = ω a
  rw [extendSelfAdjoint_apply_coe, restrictSelfAdjoint_apply]
  exact Complex.ext rfl him.symm

/-- Every state `ω ∈ stateSpace A` takes real values on `selfAdjoint A`:
`((restrictSelfAdjoint A ω x : ℝ) : ℂ) = ω x`. -/
theorem coe_restrictSelfAdjoint_apply_of_mem_stateSpace {ω : WeakDual ℂ A}
    (hω : ω ∈ stateSpace A) (x : selfAdjoint A) :
    ((restrictSelfAdjoint A ω x : ℝ) : ℂ) = ω (x : A) := by
  have := DFunLike.congr_fun (extendSelfAdjoint_restrictSelfAdjoint_of_mem_stateSpace hω) (x : A)
  simpa using this

/-- Every state `ω ∈ stateSpace A` has zero imaginary part on self-adjoint elements. -/
theorem im_apply_selfAdjoint_eq_zero_of_mem_stateSpace {ω : WeakDual ℂ A}
    (hω : ω ∈ stateSpace A) (x : selfAdjoint A) :
    (ω (x : A)).im = 0 := by
  have := congrArg Complex.im (coe_restrictSelfAdjoint_apply_of_mem_stateSpace hω x)
  simpa using this.symm

/-- On self-adjoint elements, the complex distance between two states of `A` equals the real
distance between their restrictions to `selfAdjoint A`. -/
theorem norm_sub_apply_selfAdjoint_of_mem_stateSpace {ω₁ ω₂ : WeakDual ℂ A}
    (hω₁ : ω₁ ∈ stateSpace A) (hω₂ : ω₂ ∈ stateSpace A) (x : selfAdjoint A) :
    ‖ω₁ (x : A) - ω₂ (x : A)‖ = |restrictSelfAdjoint A ω₁ x - restrictSelfAdjoint A ω₂ x| := by
  rw [← coe_restrictSelfAdjoint_apply_of_mem_stateSpace hω₁ x,
    ← coe_restrictSelfAdjoint_apply_of_mem_stateSpace hω₂ x, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]

/-- `restrictSelfAdjoint A` restricts to a bijection between `stateSpace A` and
`OrderUnit.stateSpace (1 : selfAdjoint A)`. -/
theorem bijOn_restrictSelfAdjoint_stateSpace :
    BijOn (restrictSelfAdjoint A) (stateSpace A) (OrderUnit.stateSpace (1 : selfAdjoint A)) :=
  ⟨mapsTo_restrictSelfAdjoint_stateSpace,
    fun _ h₁ _ h₂ h => by
      rw [← extendSelfAdjoint_restrictSelfAdjoint_of_mem_stateSpace h₁,
        ← extendSelfAdjoint_restrictSelfAdjoint_of_mem_stateSpace h₂, h],
    fun φ hφ => ⟨extendSelfAdjoint A φ, mapsTo_extendSelfAdjoint_stateSpace hφ,
      restrictSelfAdjoint_extendSelfAdjoint φ⟩⟩

variable (A) in
/-- **Weak-star homeomorphism between C⋆-algebra states and self-adjoint order-unit states.**
Restriction to `selfAdjoint A` and Cartesian extension identify `TauCeti.stateSpace A` with
`TauCeti.OrderUnit.stateSpace (1 : selfAdjoint A)`. -/
noncomputable def stateSpaceHomeomorphOrderUnit :
    stateSpace A ≃ₜ OrderUnit.stateSpace (1 : selfAdjoint A) where
  toFun ω := ⟨restrictSelfAdjoint A ω.1, mapsTo_restrictSelfAdjoint_stateSpace ω.2⟩
  invFun φ := ⟨extendSelfAdjoint A φ.1, mapsTo_extendSelfAdjoint_stateSpace φ.2⟩
  left_inv ω := Subtype.ext (extendSelfAdjoint_restrictSelfAdjoint_of_mem_stateSpace ω.2)
  right_inv φ := Subtype.ext (restrictSelfAdjoint_extendSelfAdjoint φ.1)
  continuous_toFun :=
    ((restrictSelfAdjoint A).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((extendSelfAdjoint A).continuous.comp continuous_subtype_val).subtype_mk _

/-- Coercing `stateSpaceHomeomorphOrderUnit A ω` to `WeakDual` gives `restrictSelfAdjoint A ω.1`. -/
@[simp]
theorem coe_stateSpaceHomeomorphOrderUnit (ω : stateSpace A) :
    (stateSpaceHomeomorphOrderUnit A ω : WeakDual ℝ (selfAdjoint A)) =
      restrictSelfAdjoint A ω.1 :=
  (rfl)

/-- `stateSpaceHomeomorphOrderUnit A ω` evaluates at `x : selfAdjoint A` as `(ω.1 x).re`. -/
theorem stateSpaceHomeomorphOrderUnit_apply (ω : stateSpace A) (x : selfAdjoint A) :
    (stateSpaceHomeomorphOrderUnit A ω).1 x = (ω.1 (x : A)).re :=
  (rfl)

/-- Coercing `(stateSpaceHomeomorphOrderUnit A).symm φ` to `WeakDual` gives
`extendSelfAdjoint A φ.1`. -/
@[simp]
theorem coe_stateSpaceHomeomorphOrderUnit_symm
    (φ : OrderUnit.stateSpace (1 : selfAdjoint A)) :
    ((stateSpaceHomeomorphOrderUnit A).symm φ : WeakDual ℂ A) = extendSelfAdjoint A φ.1 :=
  (rfl)

/-- `(stateSpaceHomeomorphOrderUnit A).symm φ` evaluates on `A` via `ℜ` and `ℑ`. -/
theorem stateSpaceHomeomorphOrderUnit_symm_apply
    (φ : OrderUnit.stateSpace (1 : selfAdjoint A)) (a : A) :
    ((stateSpaceHomeomorphOrderUnit A).symm φ).1 a =
      (φ.1 (ℜ a) : ℂ) + Complex.I * (φ.1 (ℑ a) : ℂ) :=
  (rfl)

/-- On `selfAdjoint A`, `(stateSpaceHomeomorphOrderUnit A).symm φ` agrees with `φ`. -/
theorem stateSpaceHomeomorphOrderUnit_symm_apply_coe
    (φ : OrderUnit.stateSpace (1 : selfAdjoint A)) (x : selfAdjoint A) :
    ((stateSpaceHomeomorphOrderUnit A).symm φ).1 (x : A) = (φ.1 x : ℂ) :=
  extendSelfAdjoint_apply_coe φ.1 x

/-- `stateSpaceHomeomorphOrderUnit A` preserves real convex combinations of states. -/
theorem stateSpaceHomeomorphOrderUnit_convex_comb (ω₁ ω₂ : stateSpace A) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    stateSpaceHomeomorphOrderUnit A ⟨s • ω₁.1 + t • ω₂.1, convex_stateSpace ω₁.2 ω₂.2 hs ht hst⟩ =
      ⟨s • (stateSpaceHomeomorphOrderUnit A ω₁).1 + t • (stateSpaceHomeomorphOrderUnit A ω₂).1,
        OrderUnit.convex_stateSpace 1 (stateSpaceHomeomorphOrderUnit A ω₁).2
          (stateSpaceHomeomorphOrderUnit A ω₂).2 hs ht hst⟩ :=
  Subtype.ext <| by simp [map_add, map_smul]

/-- **Norm detection on `selfAdjoint A` by C⋆-algebra states.** On a nontrivial unital C⋆-algebra,
the norm of a self-adjoint element is the supremum of its state magnitudes over `stateSpace A`. -/
theorem norm_selfAdjoint_eq_iSup_stateSpace [Nontrivial A] (x : selfAdjoint A) :
    ‖(x : A)‖ = ⨆ ω : stateSpace A, ‖ω.1 (x : A)‖ := by
  have he := OrderUnit.isOrderUnitNorm_one_selfAdjoint (A := A)
  rw [show ‖(x : A)‖ = ‖x‖ from rfl, he.norm_eq_iSup_stateSpace x,
    ← (stateSpaceHomeomorphOrderUnit A).toEquiv.iSup_comp]
  refine iSup_congr fun ω => ?_
  change |restrictSelfAdjoint A ω.1 x| = ‖ω.1 (x : A)‖
  rw [← coe_restrictSelfAdjoint_apply_of_mem_stateSpace ω.2 x, Complex.norm_real, Real.norm_eq_abs]

/-- **Scalar-line quotient norm on `selfAdjoint A` via C⋆-algebra state spread.** Twice the
quotient norm of `x : selfAdjoint A` modulo `ℝ ∙ 1` equals the supremum of `‖ω₁ x - ω₂ x‖` over
pairs of states of `A`. -/
theorem two_mul_norm_quotient_scalarLine_selfAdjoint_eq_iSup [Nontrivial A] (x : selfAdjoint A) :
    2 * ‖(Submodule.Quotient.mk x : selfAdjoint A ⧸ OrderUnit.scalarLine (1 : selfAdjoint A))‖ =
      ⨆ p : stateSpace A × stateSpace A, ‖p.1.1 (x : A) - p.2.1 (x : A)‖ := by
  have he := OrderUnit.isOrderUnitNorm_one_selfAdjoint (A := A)
  let e2 :=
    (stateSpaceHomeomorphOrderUnit A).toEquiv.prodCongr (stateSpaceHomeomorphOrderUnit A).toEquiv
  rw [he.two_mul_norm_quotient_scalarLine_eq_iSup x, ← e2.iSup_comp]
  exact iSup_congr fun p => (norm_sub_apply_selfAdjoint_of_mem_stateSpace p.1.2 p.2.2 x).symm

end StateSpaceEquiv

end TauCeti
