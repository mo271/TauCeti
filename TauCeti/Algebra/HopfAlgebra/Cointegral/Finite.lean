/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Finite
public import TauCeti.Algebra.HopfAlgebra.Cointegral.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfModule.Basic
public import TauCeti.Algebra.HopfAlgebra.Integral.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import TauCeti.Algebra.Coalgebra.Basic
import TauCeti.Algebra.HopfAlgebra.Antipode
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Cointegrals of finite projective Hopf algebras

For a finite projective bialgebra `H` over a commutative semiring `k`, the convolution dual
`ConvolutionDual k H` is itself a bialgebra whose counit is evaluation at `1 : H`. Under the
wrapper equivalence `WithConv.linearEquiv`, the right and left cointegrals of `H` correspond
bijectively to the right and left integrals of `ConvolutionDual k H`.

When `H` is a finite projective Hopf algebra over `k`, its linear dual `Module.Dual k H` carries a
canonical right `H`-Hopf module structure (`TauCeti.dualRightHopfModule`):

* the right `H`-coaction is reconstructed via `TauCeti.Comodule.ofConvolutionAction` from the left
  regular convolution action `(ψ, φ) ↦ ψ * φ` of `ConvolutionDual k H` on `Module.Dual k H`;
* the right `H`-action twists right translation by the antipode, `(φ ◁ h) x = φ (x * S h)`.

Its coinvariants are the functionals invariant under left convolution multiplication, namely
`leftCointegrals k H`. Applying the Fundamental Theorem of Hopf Modules
(`TauCeti.RightHopfModule.coinvariantTensorEquiv`) yields the canonical Larson–Sweedler linear
isomorphism

```text
leftCointegrals k H ⊗[k] H ≃ₗ[k] Module.Dual k H,      φ ⊗ h ↦ (x ↦ φ (x * S h)),
```

over any commutative semiring `k` without subtraction or commutativity hypotheses. Specializing to a
finite-dimensional Hopf algebra over a field `k` cancels `finrank k H > 0` across `finrank` to prove
that `leftCointegrals k H` is one-dimensional, hence contains a nonzero left cointegral.

## Main definitions

* `TauCeti.rightCointegralsEquivRightIntegral`, `TauCeti.leftCointegralsEquivLeftIntegral`: linear
  equivalences identifying `rightCointegrals k H` and `leftCointegrals k H` with the integral spaces
  of `ConvolutionDual k H`.
* `TauCeti.dualRightHopfModule`: the Larson–Sweedler right `H`-Hopf module structure on
  `Module.Dual k H`.
* `TauCeti.leftCointegralsTensorEquiv`: the canonical `k`-linear equivalence
  `leftCointegrals k H ⊗[k] H ≃ₗ[k] Module.Dual k H`.

## Main results

* `TauCeti.dualRightHopfModule_coinvariants`: the coinvariants of `dualRightHopfModule k H` equal
  `leftCointegrals k H`.
* `TauCeti.finrank_leftCointegrals`: `Module.finrank k (leftCointegrals k H) = 1` for a
  finite-dimensional Hopf algebra over a field.
* `TauCeti.exists_isLeftCointegral_ne_zero`: every finite-dimensional Hopf algebra over a field
  admits a nonzero left cointegral.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. **91** (1969), 75–94, Proposition 1 and Theorem, p. 83.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, AMS, 1993, Theorem 2.1.3.
-/

public noncomputable section

open scoped TensorProduct Coalgebra
open TensorProduct WithConv

namespace TauCeti

universe u v

section Bialgebra

variable {k : Type u} {H : Type v} [CommSemiring k] [Semiring H] [Bialgebra k H]
  [Module.Finite k H] [Module.Projective k H]

/-- Under `WithConv.toConv`, right cointegrals on `H` are precisely the right integrals of the
finite dual `ConvolutionDual k H`. -/
theorem toConv_mem_rightIntegral_iff (φ : Module.Dual k H) :
    toConv φ ∈ rightIntegral k (ConvolutionDual k H) ↔ IsRightCointegral φ := by
  simp only [mem_rightIntegral_iff, isRightCointegral_iff_convMul, ConvolutionDual.counit_apply]

/-- Under `WithConv.toConv`, left cointegrals on `H` are precisely the left integrals of the
finite dual `ConvolutionDual k H`. -/
theorem toConv_mem_leftIntegral_iff (φ : Module.Dual k H) :
    toConv φ ∈ leftIntegral k (ConvolutionDual k H) ↔ IsLeftCointegral φ := by
  simp only [mem_leftIntegral_iff, isLeftCointegral_iff_convMul, ConvolutionDual.counit_apply]

/-- An element of `ConvolutionDual k H` is a right integral if and only if its underlying linear
functional is a right cointegral on `H`. -/
@[simp]
theorem mem_rightIntegral_convolutionDual_iff (ψ : ConvolutionDual k H) :
    ψ ∈ rightIntegral k (ConvolutionDual k H) ↔ IsRightCointegral ψ.ofConv := by
  simpa only [toConv_ofConv] using toConv_mem_rightIntegral_iff ψ.ofConv

/-- An element of `ConvolutionDual k H` is a left integral if and only if its underlying linear
functional is a left cointegral on `H`. -/
@[simp]
theorem mem_leftIntegral_convolutionDual_iff (ψ : ConvolutionDual k H) :
    ψ ∈ leftIntegral k (ConvolutionDual k H) ↔ IsLeftCointegral ψ.ofConv := by
  simpa only [toConv_ofConv] using toConv_mem_leftIntegral_iff ψ.ofConv

variable (k H) in
/-- The `k`-linear equivalence between right cointegrals of a finite projective bialgebra `H` and
right integrals of its finite dual `ConvolutionDual k H`. -/
def rightCointegralsEquivRightIntegral :
    rightCointegrals k H ≃ₗ[k] rightIntegral k (ConvolutionDual k H) :=
  (WithConv.linearEquiv k (Module.Dual k H)).symm.ofSubmodules
    (rightCointegrals k H) (rightIntegral k (ConvolutionDual k H)) <| by
      ext ψ
      simp only [Submodule.mem_map_equiv, mem_rightCointegrals,
        mem_rightIntegral_convolutionDual_iff]
      rfl

@[simp]
theorem rightCointegralsEquivRightIntegral_apply (φ : rightCointegrals k H) :
    (rightCointegralsEquivRightIntegral k H φ : ConvolutionDual k H) =
      toConv (φ : Module.Dual k H) :=
  (rfl)

@[simp]
theorem rightCointegralsEquivRightIntegral_symm_apply
    (ψ : rightIntegral k (ConvolutionDual k H)) :
    ((rightCointegralsEquivRightIntegral k H).symm ψ : Module.Dual k H) =
      (ψ : ConvolutionDual k H).ofConv :=
  (rfl)

variable (k H) in
/-- The `k`-linear equivalence between left cointegrals of a finite projective bialgebra `H` and
left integrals of its finite dual `ConvolutionDual k H`. -/
def leftCointegralsEquivLeftIntegral :
    leftCointegrals k H ≃ₗ[k] leftIntegral k (ConvolutionDual k H) :=
  (WithConv.linearEquiv k (Module.Dual k H)).symm.ofSubmodules
    (leftCointegrals k H) (leftIntegral k (ConvolutionDual k H)) <| by
      ext ψ
      simp only [Submodule.mem_map_equiv, mem_leftCointegrals,
        mem_leftIntegral_convolutionDual_iff]
      rfl

@[simp]
theorem leftCointegralsEquivLeftIntegral_apply (φ : leftCointegrals k H) :
    (leftCointegralsEquivLeftIntegral k H φ : ConvolutionDual k H) =
      toConv (φ : Module.Dual k H) :=
  (rfl)

@[simp]
theorem leftCointegralsEquivLeftIntegral_symm_apply
    (ψ : leftIntegral k (ConvolutionDual k H)) :
    ((leftCointegralsEquivLeftIntegral k H).symm ψ : Module.Dual k H) =
      (ψ : ConvolutionDual k H).ofConv :=
  (rfl)

end Bialgebra

section HopfAlgebra

variable (k : Type u) (H : Type v) [CommSemiring k] [Semiring H] [HopfAlgebra k H]

/-- Left regular convolution multiplication of `ConvolutionDual k H` on `Module.Dual k H`, bundled
as an algebra homomorphism into `Module.End k (Module.Dual k H)`. -/
private def dualConvAction : WithConv (Module.Dual k H) →ₐ[k] Module.End k (Module.Dual k H) where
  toFun ψ := (WithConv.linearEquiv k (Module.Dual k H)).toLinearMap ∘ₗ
    LinearMap.mulLeft k ψ ∘ₗ (WithConv.linearEquiv k (Module.Dual k H)).symm.toLinearMap
  map_one' := by ext φ x; simp
  map_mul' ψ₁ ψ₂ := by ext φ x; simp
  map_zero' := by ext φ x; simp
  map_add' ψ₁ ψ₂ := by ext φ x; simp [add_mul]
  commutes' r := by ext φ x; simp [Algebra.algebraMap_eq_smul_one]

/-- The antipode-twisted right translation `(φ ◁ h) x = φ (x * S h)` on `Module.Dual k H`. -/
private def dualRightAct : Module.Dual k H →ₗ[k] H →ₗ[k] Module.Dual k H where
  toFun φ :=
    { toFun h := φ.comp (LinearMap.mulRight k (HopfAlgebraStruct.antipode k h))
      map_add' h₁ h₂ := by ext x; simp [mul_add]
      map_smul' r h := by ext x; simp }
  map_add' φ₁ φ₂ := by ext h x; simp
  map_smul' r φ := by ext h x; simp

variable [Module.Finite k H] [Module.Projective k H]

/-- **The Larson–Sweedler right Hopf module on the linear dual.** On `Module.Dual k H`, the right
coaction reconstructed from left convolution multiplication and the antipode-twisted right action
`(φ ◁ h) x = φ (x * S h)` satisfy the right Hopf module compatibility law. -/
def dualRightHopfModule : RightHopfModule k H (Module.Dual k H) where
  toComodule := Comodule.ofConvolutionAction (dualConvAction k H)
  act := dualRightAct k H
  act_one φ := by
    ext x
    change φ (x * HopfAlgebraStruct.antipode k 1) = φ x
    rw [_root_.HopfAlgebra.antipode_one, mul_one]
  act_mul φ a b := by
    ext x
    change φ (x * HopfAlgebraStruct.antipode k b * HopfAlgebraStruct.antipode k a) =
      φ (x * HopfAlgebraStruct.antipode k (a * b))
    rw [mul_assoc, _root_.HopfAlgebra.antipode_mul_antidistrib]
  coact_act φ h := by
    classical
    apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro ψ
    ext x
    let rx := ℛ k x
    -- Auxiliary functional contracting `a ⊗ (b ⊗ c) ↦ ∑ᵢ φ (x₂ᵢ * S a) * ψ (x₁ᵢ * (S b * c))`.
    let Λ₀ : H ⊗[k] (H ⊗[k] H) →ₗ[k] k :=
      ∑ i ∈ rx.index,
        LinearMap.mul' k k ∘ₗ
          TensorProduct.map
            (φ ∘ₗ LinearMap.mulLeft k (rx.right i) ∘ₗ HopfAlgebraStruct.antipode k)
            (ψ ∘ₗ LinearMap.mulLeft k (rx.left i) ∘ₗ LinearMap.mul' k H ∘ₗ
              (HopfAlgebraStruct.antipode k).rTensor H)
    -- RHS equals `Λ₀ (assoc ((Δ ⊗ id) (Δ h)))`.
    have hrhs :
        LinearMap.tensorComponent ψ
            (TensorProduct.map₂ (dualRightAct k H) (LinearMap.mul k H)
              ((Comodule.ofConvolutionAction (dualConvAction k H)).coact φ)
              (Coalgebra.comul h)) x =
          Λ₀ (TensorProduct.assoc k H H H (Coalgebra.comul.rTensor H (Coalgebra.comul h))) := by
      have hterm (z : H ⊗[k] H) :
          LinearMap.tensorComponent ψ
              (TensorProduct.map₂ (dualRightAct k H) (LinearMap.mul k H)
                ((Comodule.ofConvolutionAction (dualConvAction k H)).coact φ) z) x =
            Λ₀ (TensorProduct.assoc k H H H (Coalgebra.comul.rTensor H z)) := by
        induction z using TensorProduct.inductionOn with
        | add z₁ z₂ hz₁ hz₂ => simp only [map_add, LinearMap.add_apply, hz₁, hz₂]
        | tmul a c =>
          have hmap₂ :
              TensorProduct.map₂ (dualRightAct k H) (LinearMap.mul k H)
                  ((Comodule.ofConvolutionAction (dualConvAction k H)).coact φ) (a ⊗ₜ[k] c) =
                TensorProduct.map ((dualRightAct k H).flip a) (LinearMap.mulRight k c)
                  ((Comodule.ofConvolutionAction (dualConvAction k H)).coact φ) := by
            generalize (Comodule.ofConvolutionAction (dualConvAction k H)).coact φ = w
            induction w using TensorProduct.inductionOn with
            | tmul f d => rfl
            | add w₁ w₂ hw₁ hw₂ => simp only [map_add, LinearMap.add_apply, hw₁, hw₂]
          rw [hmap₂, LinearMap.tensorComponent_map, Comodule.tensorComponent_ofConvolutionAction]
          let ra := ℛ k a
          have hcomul_sa : Coalgebra.comul (HopfAlgebraStruct.antipode k a) =
              ∑ j ∈ ra.index,
                HopfAlgebraStruct.antipode k (ra.right j) ⊗ₜ[k]
                  HopfAlgebraStruct.antipode k (ra.left j) := by
            rw [HopfAlgebra.antipode_comul_antidistrib_apply, ← ra.eq, map_sum, map_sum]
            rfl
          have hcomul_prod :
              Coalgebra.comul (x * HopfAlgebraStruct.antipode k a) =
                ∑ i ∈ rx.index, ∑ j ∈ ra.index,
                  (rx.left i * HopfAlgebraStruct.antipode k (ra.right j)) ⊗ₜ[k]
                    (rx.right i * HopfAlgebraStruct.antipode k (ra.left j)) := by
            rw [Bialgebra.comul_mul, ← rx.eq, hcomul_sa, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [Finset.mul_sum]
            simp only [Algebra.TensorProduct.tmul_mul_tmul]
          change ((toConv (ψ.comp (LinearMap.mulRight k c)) * toConv φ).ofConv)
              (x * HopfAlgebraStruct.antipode k a) =
            Λ₀ (TensorProduct.assoc k H H H (Coalgebra.comul a ⊗ₜ[k] c))
          rw [ConvolutionDual.mul_apply_eq_lTensor]
          simp only [hcomul_prod, map_sum, LinearMap.lTensor_tmul, rid_tmul,
            LinearMap.comp_apply, LinearMap.mulRight_apply, map_smul, smul_eq_mul]
          rw [← ra.eq, sum_tmul]
          simp only [Λ₀, map_sum, assoc_tmul, LinearMap.sum_apply, LinearMap.comp_apply,
            map_tmul, LinearMap.mulLeft_apply, LinearMap.rTensor_tmul, LinearMap.mul'_apply]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
          rw [mul_assoc]
      exact hterm (Coalgebra.comul h)
    -- Coassociativity rewrites to `(id ⊗ Δ) (Δ h)`, where `S` cancels `id` on the right leg.
    have hlhs :
        Λ₀ (Coalgebra.comul.lTensor H (Coalgebra.comul h)) =
          LinearMap.tensorComponent ψ
            ((Comodule.ofConvolutionAction (dualConvAction k H)).coact
              (dualRightAct k H φ h)) x := by
      have hstep (z : H ⊗[k] H) :
          Λ₀ (Coalgebra.comul.lTensor H z) =
            ∑ i ∈ rx.index,
              ψ (rx.left i) *
                φ (rx.right i *
                  HopfAlgebraStruct.antipode k
                    (TensorProduct.rid k H (Coalgebra.counit.lTensor H z))) := by
        induction z using TensorProduct.inductionOn with
        | add z₁ z₂ hz₁ hz₂ =>
          simp only [map_add, hz₁, hz₂, mul_add, Finset.sum_add_distrib]
        | tmul a d =>
          simp only [Λ₀, LinearMap.lTensor_tmul, rid_tmul, LinearMap.sum_apply,
            LinearMap.comp_apply, map_tmul, LinearMap.mulLeft_apply, LinearMap.mul'_apply,
            _root_.HopfAlgebra.mul_antipode_rTensor_comul_apply, Algebra.algebraMap_eq_smul_one,
            mul_smul_comm, mul_one, map_smul, smul_eq_mul]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          ring
      rw [hstep (Coalgebra.comul h), Coalgebra.lTensor_counit_comul, rid_tmul, one_smul,
        Comodule.tensorComponent_ofConvolutionAction]
      change _ = ((toConv ψ * toConv (dualRightAct k H φ h)).ofConv) x
      rw [rx.convMul_apply]
      rfl
    rw [hrhs, Coalgebra.coassoc_apply, hlhs]

variable {k H}

@[simp]
theorem dualRightHopfModule_act_apply (φ : Module.Dual k H) (h x : H) :
    (dualRightHopfModule k H).act φ h x = φ (x * HopfAlgebraStruct.antipode k h) :=
  (rfl)

@[simp]
theorem tensorComponent_dualRightHopfModule_coact (ψ φ : Module.Dual k H) :
    LinearMap.tensorComponent ψ ((dualRightHopfModule k H).coact φ) =
      (toConv ψ * toConv φ).ofConv :=
  Comodule.tensorComponent_ofConvolutionAction (dualConvAction k H) ψ φ

/-- The coinvariants of `dualRightHopfModule k H` are precisely the left cointegrals of `H`. -/
@[simp]
theorem dualRightHopfModule_coinvariants :
    (dualRightHopfModule k H).coinvariants = leftCointegrals k H := by
  ext φ
  rw [RightHopfModule.mem_coinvariants, mem_leftCointegrals, isLeftCointegral_iff_convMul]
  refine ⟨fun h ψ ↦ ?_, fun h ↦ ?_⟩
  · apply WithConv.ofConv_injective
    have hψ := congrArg (LinearMap.tensorComponent ψ.ofConv) h
    simpa only [tensorComponent_dualRightHopfModule_coact, toConv_ofConv,
      LinearMap.tensorComponent_tmul, ofConv_smul] using hψ
  · apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro ψ
    rw [tensorComponent_dualRightHopfModule_coact, LinearMap.tensorComponent_tmul]
    exact congrArg WithConv.ofConv (h (toConv ψ))

variable (k H) in
/-- **The Larson–Sweedler dual isomorphism**: for any finite projective Hopf algebra `H` over a
commutative semiring `k`, `leftCointegrals k H ⊗[k] H` is canonically `k`-linearly isomorphic to
`Module.Dual k H` via `φ ⊗ h ↦ (x ↦ φ (x * S h))`. -/
def leftCointegralsTensorEquiv :
    leftCointegrals k H ⊗[k] H ≃ₗ[k] Module.Dual k H :=
  TensorProduct.congr (LinearEquiv.ofEq _ _ dualRightHopfModule_coinvariants.symm)
    (LinearEquiv.refl k H) ≪≫ₗ (dualRightHopfModule k H).coinvariantTensorEquiv

@[simp]
theorem leftCointegralsTensorEquiv_tmul_apply (φ : leftCointegrals k H) (h x : H) :
    leftCointegralsTensorEquiv k H (φ ⊗ₜ[k] h) x =
      (φ : Module.Dual k H) (x * HopfAlgebraStruct.antipode k h) := by
  simp [leftCointegralsTensorEquiv]

end HopfAlgebra

section Field

variable (k : Type u) (H : Type v) [Field k] [Ring H] [HopfAlgebra k H] [FiniteDimensional k H]

/-- **Larson–Sweedler theorem (left cointegrals)**: the space of left cointegrals of a
finite-dimensional Hopf algebra over a field has dimension `1`. -/
@[simp]
theorem finrank_leftCointegrals : Module.finrank k (leftCointegrals k H) = 1 := by
  have : Nontrivial H := Bialgebra.nontrivial k
  have hpos : 0 < Module.finrank k H := Module.finrank_pos
  -- `leftCointegrals` is defined over `CommSemiring k`, so supply vector-space freeness explicitly.
  have := Module.Free.of_divisionRing k (leftCointegrals k H)
  have heq := (leftCointegralsTensorEquiv k H).finrank_eq
  rw [Module.finrank_tensorProduct, Subspace.dual_finrank_eq] at heq
  exact Nat.mul_right_cancel hpos (heq.trans (one_mul _).symm)

/-- Every finite-dimensional Hopf algebra over a field admits a nonzero left cointegral. -/
theorem exists_isLeftCointegral_ne_zero :
    ∃ φ : Module.Dual k H, IsLeftCointegral φ ∧ φ ≠ 0 := by
  have : Nontrivial (leftCointegrals k H) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_leftCointegrals]; exact Nat.zero_lt_one)
  obtain ⟨⟨φ, hφ⟩, hne⟩ := exists_ne (0 : leftCointegrals k H)
  exact ⟨φ, (mem_leftCointegrals φ).mp hφ, fun h0 ↦ hne (Subtype.ext h0)⟩

end Field

end TauCeti
