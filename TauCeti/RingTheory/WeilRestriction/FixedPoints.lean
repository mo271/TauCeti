/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PolynomialAlgebra
public import TauCeti.Algebra.TensorProduct.BaseChange
public import TauCeti.RingTheory.Etale.FixedPoints
public import TauCeti.RingTheory.Invariant.AlgebraDescent
public import TauCeti.RingTheory.Smooth.FixedPoints
public import TauCeti.RingTheory.WeilRestriction.Etale
public import TauCeti.RingTheory.WeilRestriction.Semilinear

/-!
# Fixed-point schemes of Weil restrictions and Edixhoven's tame descent theorem

Let `B` be a finite projective `A`-algebra, `C` a finitely presented `B`-algebra, and `Γ` a monoid
acting on `B` by `A`-algebra automorphisms `ρB : Γ →* (B ≃ₐ[A] B)` and on `C` by ring automorphisms
`ρC : Γ →* RingAut C` semilinear over `ρB`. By `WeilRestriction.inducedAction`, `Γ` acts on
`WeilRestriction A B C` by `A`-algebra automorphisms.

This file studies the **fixed-point ideal** `WeilRestriction.fixedPointIdeal ρB ρC h` and its
quotient `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h`, which represents the closed subscheme
`(Res_{B/A} Spec C)^Γ`:
* For any `A`-algebra `T`, `A`-algebra homomorphisms out of the quotient correspond naturally and
  bijectively to `Γ`-equivariant `B`-algebra points `C →ₐ[B] B ⊗[A] T` (`fixedPointsHomEquiv`).
* When `Γ` is a finite group whose order `(Nat.card Γ : A)` is invertible in `A` and `C` is
  formally smooth (respectively smooth) over `B`, the fixed-point quotient
  `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` is formally smooth (respectively smooth) over
  `A` (`formallySmooth_quotient_fixedPointIdeal`, `smooth_quotient_fixedPointIdeal`). This is
  Edixhoven's tame fixed-point smoothness theorem applied to Weil restrictions — the algebraic core
  of tame Galois descent of integral models, requiring neither Noetherian nor Henselian hypotheses
  on `A`.
* When `C` is formally étale (respectively étale, for finite `Γ`) over `B`, the fixed-point
  quotient is formally étale (respectively étale) over `A` with no invertibility assumption on
  `Nat.card Γ` (`formallyEtale_quotient_fixedPointIdeal`, `etale_quotient_fixedPointIdeal`).
* When a finite group `Γ` acts on `B` with invariant ring `A`
  (`[Algebra.IsInvariant A B Γ] [FaithfulSMul A B]`) and `B` admits an element of trace `1` — in
  particular whenever `(Nat.card Γ : A)` is invertible (including ramified tame extensions) or
  whenever `Γ` acts freely (`TauCeti.MulSemiringAction.exists_sum_smul_eq_one`) — for every
  finitely presented `A`-algebra `D` the `Γ`-fixed quotient of `WeilRestriction A B (B ⊗[A] D)` is
  canonically isomorphic as an `A`-algebra to `D`
  (`quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne`,
  `quotientFixedPointIdealBaseChangeAlgEquiv`). Specializing to `D = A[X]` identifies the `Γ`-fixed
  quotient of `WeilRestriction A B B[X]` with `A[X]`
  (`quotientFixedPointIdealPolynomialAlgEquivOfExistsTraceOne`,
  `quotientFixedPointIdealPolynomialAlgEquiv`).

## Main definitions

* `TauCeti.Algebra.WeilRestriction.fixedPointIdeal`: the ideal of `WeilRestriction A B C` generated
  by all displacements `inducedAction ρB ρC h γ x - x`.
* `TauCeti.Algebra.WeilRestriction.fixedPointsHomEquiv`: functor of points of
  `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h`, classifying `Γ`-equivariant points
  `C →ₐ[B] B ⊗[A] T`.
* `TauCeti.Algebra.WeilRestriction.quotientFixedPointIdealAlgEquivOfEquiv`: functoriality of the
  fixed-point quotient under `Γ`-equivariant `B`-algebra isomorphisms.
* `TauCeti.MulSemiringAction.baseChangeRingAutHom`: the left-factor action `Γ →* RingAut (B ⊗[A] D)`
  induced by an `A`-linear `MulSemiringAction Γ B`.
* `TauCeti.Algebra.WeilRestriction.quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne`,
  `TauCeti.Algebra.WeilRestriction.quotientFixedPointIdealBaseChangeAlgEquiv`,
  `TauCeti.Algebra.WeilRestriction.quotientFixedPointIdealPolynomialAlgEquivOfExistsTraceOne`, and
  `TauCeti.Algebra.WeilRestriction.quotientFixedPointIdealPolynomialAlgEquiv`: descent of
  `(Res_{B/A}(B ⊗[A] D))^Γ ≃ₐ[A] D` and `(Res_{B/A} B[X])^Γ ≃ₐ[A] A[X]`.

## Main results

* `TauCeti.Algebra.WeilRestriction.formallySmooth_quotient_fixedPointIdeal` and
  `TauCeti.Algebra.WeilRestriction.smooth_quotient_fixedPointIdeal`: Edixhoven's tame fixed-point
  smoothness theorem for Weil restrictions.
* `TauCeti.Algebra.WeilRestriction.formallyEtale_quotient_fixedPointIdeal` and
  `TauCeti.Algebra.WeilRestriction.etale_quotient_fixedPointIdeal`: preservation of formal
  étaleness and étaleness on fixed points of Weil restrictions.

## References

* B. Edixhoven, *Néron models and tame ramification*, Compositio Math. 81 (1992), §2.4 and
  Propositions 3.1, 3.4, pp. 292–295.
* M. Kisin, G. Pappas, *Integral models of Shimura varieties with parahoric level structure*,
  Publ. Math. IHÉS 128 (2018), Proposition 1.3.9, p. 143.
-/

public noncomputable section

open Algebra TensorProduct Polynomial

namespace TauCeti.MulSemiringAction

variable (A B : Type*) [CommSemiring A] [CommSemiring B] [Algebra A B]
  (Γ : Type*) [Group Γ] [MulSemiringAction Γ B] [SMulCommClass Γ A B]

/-- The induced action `Γ →* RingAut (B ⊗[A] D)` acting on the left factor `B` via `Γ` and
trivially on `D`. -/
def baseChangeRingAutHom (D : Type*) [Semiring D] [Algebra A D] :
    Γ →* RingAut (B ⊗[A] D) :=
  letI : MulSemiringAction Γ (B ⊗[A] D) :=
    MulSemiringAction.compHom (B ⊗[A] D)
      ((TauCeti.ScalarAut.toAlgAut (A := D)).comp (MulSemiringAction.toAlgAut Γ A B))
  MulSemiringAction.toRingAut Γ (B ⊗[A] D)

@[simp]
theorem baseChangeRingAutHom_tmul (D : Type*) [Semiring D] [Algebra A D] (γ : Γ) (b : B) (d : D) :
    baseChangeRingAutHom A B Γ D γ (b ⊗ₜ[A] d) = (γ • b) ⊗ₜ[A] d := by
  rw [baseChangeRingAutHom, MulSemiringAction.toRingAut_apply,
    MulSemiringAction.toRingEquiv_apply_apply, MulAction.compHom_smul_def, MonoidHom.comp_apply,
    AlgEquiv.smul_def, TauCeti.ScalarAut.toAlgAut_tmul, MulSemiringAction.toAlgAut_apply,
    MulSemiringAction.toAlgEquiv_apply]

/-- On `B ⊗[A] D`, `baseChangeRingAutHom A B Γ D γ` agrees with `Algebra.TensorProduct.rTensor` of
`MulSemiringAction.toAlgHom A B γ`. -/
theorem baseChangeRingAutHom_apply (D : Type*) [Semiring D] [Algebra A D] (γ : Γ) (z : B ⊗[A] D) :
    baseChangeRingAutHom A B Γ D γ z =
      Algebra.TensorProduct.rTensor D (MulSemiringAction.toAlgHom A B γ) z := by
  induction z using TensorProduct.inductionOn with
  | tmul b d => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Semilinearity of `baseChangeRingAutHom` over `MulSemiringAction.toAlgAut Γ A B` along
`algebraMap B (B ⊗[A] D)`. -/
theorem baseChangeRingAutHom_algebraMap (D : Type*) [Semiring D] [Algebra A D] (γ : Γ) (b : B) :
    baseChangeRingAutHom A B Γ D γ (algebraMap B (B ⊗[A] D) b) =
      algebraMap B (B ⊗[A] D) (MulSemiringAction.toAlgAut Γ A B γ b) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

/-- Compatibility of the coefficientwise `Γ`-action on `B[X]` with `algebraMap B B[X]`. -/
theorem toRingAut_polynomial_algebraMap (γ : Γ) (b : B) :
    MulSemiringAction.toRingAut Γ B[X] γ (algebraMap B B[X] b) =
      algebraMap B B[X] (MulSemiringAction.toAlgAut Γ A B γ b) :=
  Polynomial.smul_C γ b

end TauCeti.MulSemiringAction

namespace TauCeti.Algebra.WeilRestriction

section General

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation B C]
  {Γ : Type*} [Monoid Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

private abbrev inducedMulSemiringAction : MulSemiringAction Γ (WeilRestriction A B C) :=
  MulSemiringAction.compHom (WeilRestriction A B C) (inducedAction ρB ρC h)

private theorem inducedMulSemiringAction_smul (γ : Γ) (x : WeilRestriction A B C) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ (inducedMulSemiringAction ρB ρC h).toSMul) γ x =
      inducedAction ρB ρC h γ x := by
  let _ := inducedMulSemiringAction ρB ρC h
  exact (MulAction.compHom_smul_def (inducedAction ρB ρC h) γ x).trans
    (AlgEquiv.smul_def (inducedAction ρB ρC h γ) x)

private theorem inducedSMulCommClass :
    @SMulCommClass Γ A (WeilRestriction A B C)
      (inducedMulSemiringAction ρB ρC h).toSMul Algebra.toSMul := by
  let _ := inducedMulSemiringAction ρB ρC h
  exact ⟨fun γ a x ↦ by
    rw [inducedMulSemiringAction_smul ρB ρC h, inducedMulSemiringAction_smul ρB ρC h, map_smul]⟩

/-- The **fixed-point ideal** of `WeilRestriction.inducedAction ρB ρC h` inside
`WeilRestriction A B C`: the ideal generated by all displacements
`inducedAction ρB ρC h γ x - x`. Its quotient represents the closed subscheme of `Γ`-fixed points
of `Res_{B/A}(Spec C)`. -/
def fixedPointIdeal : Ideal (WeilRestriction A B C) :=
  @MulSemiringAction.fixedPointIdeal Γ (WeilRestriction A B C)
    (inducedMulSemiringAction ρB ρC h).toSMul _

theorem fixedPointIdeal_def :
    fixedPointIdeal ρB ρC h = Ideal.span {y : WeilRestriction A B C |
      ∃ (γ : Γ) (x : WeilRestriction A B C), inducedAction ρB ρC h γ x - x = y} := by
  let _ := inducedMulSemiringAction ρB ρC h
  rw [fixedPointIdeal, MulSemiringAction.fixedPointIdeal_def]
  simp_rw [inducedMulSemiringAction_smul ρB ρC h]

/-- Every displacement `inducedAction ρB ρC h γ x - x` belongs to `fixedPointIdeal ρB ρC h`. -/
theorem inducedAction_sub_mem_fixedPointIdeal (γ : Γ) (x : WeilRestriction A B C) :
    inducedAction ρB ρC h γ x - x ∈ fixedPointIdeal ρB ρC h := by
  let _ := inducedMulSemiringAction ρB ρC h
  rw [fixedPointIdeal, ← inducedMulSemiringAction_smul ρB ρC h]
  exact MulSemiringAction.smul_sub_mem_fixedPointIdeal γ x

/-- Universal property of `fixedPointIdeal ρB ρC h` among ideals of `WeilRestriction A B C`. -/
theorem fixedPointIdeal_le_iff {J : Ideal (WeilRestriction A B C)} :
    fixedPointIdeal ρB ρC h ≤ J ↔
      ∀ (γ : Γ) (x : WeilRestriction A B C), inducedAction ρB ρC h γ x - x ∈ J := by
  let _ := inducedMulSemiringAction ρB ρC h
  simp_rw [fixedPointIdeal, MulSemiringAction.fixedPointIdeal_le_iff,
    inducedMulSemiringAction_smul ρB ρC h]

/-- A ring homomorphism out of `WeilRestriction A B C` vanishes on `fixedPointIdeal ρB ρC h` if and
only if it is invariant under `inducedAction ρB ρC h`. -/
theorem fixedPointIdeal_le_ker_iff {F R' : Type*} [Ring R']
    [FunLike F (WeilRestriction A B C) R'] [RingHomClass F (WeilRestriction A B C) R'] (φ : F) :
    fixedPointIdeal ρB ρC h ≤ RingHom.ker φ ↔
      ∀ (γ : Γ) (x : WeilRestriction A B C), φ (inducedAction ρB ρC h γ x) = φ x := by
  let _ := inducedMulSemiringAction ρB ρC h
  simp_rw [fixedPointIdeal, MulSemiringAction.fixedPointIdeal_le_ker_iff,
    inducedMulSemiringAction_smul ρB ρC h]

/-- `fixedPointIdeal ρB ρC h` vanishes if and only if the induced action on `WeilRestriction A B C`
is trivial. -/
@[simp]
theorem fixedPointIdeal_eq_bot_iff :
    fixedPointIdeal ρB ρC h = ⊥ ↔ inducedAction ρB ρC h = 1 := by
  let _ := inducedMulSemiringAction ρB ρC h
  rw [fixedPointIdeal, MulSemiringAction.fixedPointIdeal_eq_bot_iff]
  simp_rw [inducedMulSemiringAction_smul ρB ρC h, DFunLike.ext_iff, MonoidHom.one_apply,
    AlgEquiv.one_apply]

/-- Modulo `fixedPointIdeal ρB ρC h`, `inducedAction ρB ρC h γ x` equals `x`. -/
theorem mk_fixedPointIdeal_inducedAction (γ : Γ) (x : WeilRestriction A B C) :
    Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) (inducedAction ρB ρC h γ x) =
      Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) x := by
  let _ := inducedMulSemiringAction ρB ρC h
  rw [fixedPointIdeal, ← inducedMulSemiringAction_smul ρB ρC h,
    MulSemiringAction.mk_fixedPointIdeal_smul]

/-- **Functor of points of the fixed-point scheme of a Weil restriction.** For every commutative
`A`-algebra `T`, `A`-algebra homomorphisms
`(WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) →ₐ[A] T` correspond bijectively to
`Γ`-equivariant `B`-algebra homomorphisms `C →ₐ[B] B ⊗[A] T`. -/
def fixedPointsHomEquiv (T : Type*) [CommRing T] [Algebra A T] :
    ((WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) →ₐ[A] T) ≃
      {y : C →ₐ[B] B ⊗[A] T // ∀ (γ : Γ) (c : C),
        y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)} :=
  let _ := inducedMulSemiringAction ρB ρC h
  (MulSemiringAction.quotientFixedPointIdealAlgHomEquiv A Γ (WeilRestriction A B C) T).trans <|
    (homEquiv A B C T).subtypeEquiv fun g ↦ by
      refine forall_congr' fun γ ↦ ?_
      rw [← comp_inducedAction_eq_iff ρB ρC h γ g, AlgHom.ext_iff]
      simp_rw [inducedMulSemiringAction_smul ρB ρC h, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]

@[simp]
theorem fixedPointsHomEquiv_apply {T : Type*} [CommRing T] [Algebra A T]
    (φ : (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) →ₐ[A] T) :
    (fixedPointsHomEquiv ρB ρC h T φ).1 =
      homEquiv A B C T (φ.comp (Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h))) := by
  let _ := inducedMulSemiringAction ρB ρC h
  revert φ
  unfold fixedPointsHomEquiv fixedPointIdeal
  intro φ
  simp only [Equiv.trans_apply, Equiv.subtypeEquiv_apply]
  exact congrArg (homEquiv A B C T) <| AlgHom.ext fun x ↦ by
    rw [MulSemiringAction.quotientFixedPointIdealAlgHomEquiv_apply, AlgHom.comp_apply,
      Ideal.Quotient.mkₐ_eq_mk]

@[simp]
theorem fixedPointsHomEquiv_symm_apply_mk {T : Type*} [CommRing T] [Algebra A T]
    (y : {y : C →ₐ[B] B ⊗[A] T // ∀ (γ : Γ) (c : C),
      y (ρC γ c) = Algebra.TensorProduct.rTensor T (ρB γ : B →ₐ[A] B) (y c)})
    (x : WeilRestriction A B C) :
    (fixedPointsHomEquiv ρB ρC h T).symm y (Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) x) =
      (homEquiv A B C T).symm y.1 x := by
  let _ := inducedMulSemiringAction ρB ρC h
  unfold fixedPointsHomEquiv fixedPointIdeal
  simp only [Equiv.symm_trans_apply,
    MulSemiringAction.quotientFixedPointIdealAlgHomEquiv_symm_apply_mk,
    Equiv.subtypeEquiv_symm, Equiv.subtypeEquiv_apply]

/-- Naturality of `fixedPointsHomEquiv` in the target `A`-algebra `T`. -/
theorem fixedPointsHomEquiv_comp {T T' : Type*} [CommRing T] [Algebra A T] [CommRing T']
    [Algebra A T'] (φ : (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) →ₐ[A] T)
    (k : T →ₐ[A] T') :
    (fixedPointsHomEquiv ρB ρC h T' (k.comp φ)).1 =
      (Algebra.TensorProduct.lTensor B k).comp (fixedPointsHomEquiv ρB ρC h T φ).1 := by
  rw [fixedPointsHomEquiv_apply, AlgHom.comp_assoc, homEquiv_comp, fixedPointsHomEquiv_apply]

/-- Two `A`-algebra homomorphisms out of `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` are
equal if they classify the same `B`-algebra point. -/
theorem fixedPoints_hom_ext {T : Type*} [CommRing T] [Algebra A T]
    {φ ψ : (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) →ₐ[A] T}
    (heq : (fixedPointsHomEquiv ρB ρC h T φ).1 = (fixedPointsHomEquiv ρB ρC h T ψ).1) :
    φ = ψ :=
  (fixedPointsHomEquiv ρB ρC h T).injective (Subtype.ext heq)

/-- A `Γ`-equivariant `B`-algebra isomorphism `e : C ≃ₐ[B] D` induces an `A`-algebra isomorphism
between the fixed-point quotients of `WeilRestriction A B C` and `WeilRestriction A B D`. -/
def quotientFixedPointIdealAlgEquivOfEquiv {D : Type*} [CommRing D] [Algebra B D]
    [FinitePresentation B D] (ρD : Γ →* RingAut D)
    (hD : ∀ γ b, ρD γ (algebraMap B D b) = algebraMap B D (ρB γ b))
    (e : C ≃ₐ[B] D) (he : ∀ (γ : Γ) (c : C), ρD γ (e c) = e (ρC γ c)) :
    (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) ≃ₐ[A]
      (WeilRestriction A B D ⧸ fixedPointIdeal ρB ρD hD) :=
  let _ := inducedMulSemiringAction ρB ρC h
  let _ := inducedMulSemiringAction ρB ρD hD
  MulSemiringAction.quotientFixedPointIdealAlgEquivOfEquiv A
    (AlgEquiv.ofAlgHom (map A B e.toAlgHom) (map A B e.symm.toAlgHom)
      (by rw [← map_comp]; simp) (by rw [← map_comp]; simp))
    fun γ x ↦ by
      rw [inducedMulSemiringAction_smul ρB ρC h, inducedMulSemiringAction_smul ρB ρD hD,
        AlgEquiv.ofAlgHom_apply, AlgEquiv.ofAlgHom_apply]
      have hcomm :
          (map A B e.toAlgHom).comp (inducedAction ρB ρC h γ : _ →ₐ[A] _) =
            (inducedAction ρB ρD hD γ : _ →ₐ[A] _).comp (map A B e.toAlgHom) := by
        apply (homEquiv A B C (WeilRestriction A B D)).injective
        ext c
        rw [homEquiv_comp_inducedAction_apply, homEquiv_map, AlgHom.comp_apply,
          AlgEquiv.coe_toAlgHom, homEquiv_comp_map, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
          ← AlgHom.id_comp
            (inducedAction ρB ρD hD γ : WeilRestriction A B D →ₐ[A] WeilRestriction A B D),
          homEquiv_comp_inducedAction_apply]
        simp [he]
      exact congr($hcomm x)

@[simp]
theorem quotientFixedPointIdealAlgEquivOfEquiv_mk {D : Type*} [CommRing D] [Algebra B D]
    [FinitePresentation B D] (ρD : Γ →* RingAut D)
    (hD : ∀ γ b, ρD γ (algebraMap B D b) = algebraMap B D (ρB γ b))
    (e : C ≃ₐ[B] D) (he : ∀ (γ : Γ) (c : C), ρD γ (e c) = e (ρC γ c))
    (x : WeilRestriction A B C) :
    quotientFixedPointIdealAlgEquivOfEquiv ρB ρC h ρD hD e he
        (Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) x) =
      Ideal.Quotient.mk (fixedPointIdeal ρB ρD hD) (map A B e.toAlgHom x) := by
  let _ := inducedMulSemiringAction ρB ρC h
  let _ := inducedMulSemiringAction ρB ρD hD
  unfold quotientFixedPointIdealAlgEquivOfEquiv fixedPointIdeal
  simp only [MulSemiringAction.quotientFixedPointIdealAlgEquivOfEquiv_mk, AlgEquiv.ofAlgHom_apply]

@[simp]
theorem quotientFixedPointIdealAlgEquivOfEquiv_symm_mk {D : Type*} [CommRing D] [Algebra B D]
    [FinitePresentation B D] (ρD : Γ →* RingAut D)
    (hD : ∀ γ b, ρD γ (algebraMap B D b) = algebraMap B D (ρB γ b))
    (e : C ≃ₐ[B] D) (he : ∀ (γ : Γ) (c : C), ρD γ (e c) = e (ρC γ c))
    (y : WeilRestriction A B D) :
    (quotientFixedPointIdealAlgEquivOfEquiv ρB ρC h ρD hD e he).symm
        (Ideal.Quotient.mk (fixedPointIdeal ρB ρD hD) y) =
      Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) (map A B e.symm.toAlgHom y) := by
  let _ := inducedMulSemiringAction ρB ρC h
  let _ := inducedMulSemiringAction ρB ρD hD
  unfold quotientFixedPointIdealAlgEquivOfEquiv fixedPointIdeal
  simp only [MulSemiringAction.quotientFixedPointIdealAlgEquivOfEquiv_symm_mk,
    AlgEquiv.ofAlgHom_symm_apply]

/-- Naturality of `fixedPointsHomEquiv` along `quotientFixedPointIdealAlgEquivOfEquiv`. -/
theorem fixedPointsHomEquiv_comp_quotientFixedPointIdealAlgEquivOfEquiv
    {D : Type*} [CommRing D] [Algebra B D] [FinitePresentation B D]
    (ρD : Γ →* RingAut D) (hD : ∀ γ b, ρD γ (algebraMap B D b) = algebraMap B D (ρB γ b))
    (e : C ≃ₐ[B] D) (he : ∀ (γ : Γ) (c : C), ρD γ (e c) = e (ρC γ c))
    {T : Type*} [CommRing T] [Algebra A T]
    (φ : (WeilRestriction A B D ⧸ fixedPointIdeal ρB ρD hD) →ₐ[A] T) :
    (fixedPointsHomEquiv ρB ρC h T
        (φ.comp (quotientFixedPointIdealAlgEquivOfEquiv ρB ρC h ρD hD e he).toAlgHom)).1 =
      (fixedPointsHomEquiv ρB ρD hD T φ).1.comp e.toAlgHom := by
  have hcomp :
      (quotientFixedPointIdealAlgEquivOfEquiv ρB ρC h ρD hD e he).toAlgHom.comp
          (Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρC h)) =
        (Ideal.Quotient.mkₐ A (fixedPointIdeal ρB ρD hD)).comp (map A B e.toAlgHom) := by
    apply AlgHom.ext
    intro x
    simp
  rw [fixedPointsHomEquiv_apply, fixedPointsHomEquiv_apply, AlgHom.comp_assoc, hcomp,
    ← AlgHom.comp_assoc, homEquiv_comp_map]

/-- When `Γ` acts trivially on both `B` and `C`, `fixedPointIdeal ρB ρC h` vanishes. -/
theorem fixedPointIdeal_eq_bot_of_eq_one (hB : ρB = 1) (hC : ρC = 1) :
    fixedPointIdeal ρB ρC h = ⊥ :=
  (fixedPointIdeal_eq_bot_iff ρB ρC h).mpr (inducedAction_eq_one ρB ρC h hB hC)

/-- When `Γ` acts trivially on `B` and `C`, the fixed-point quotient of `WeilRestriction A B C` is
isomorphic as an `A`-algebra to `WeilRestriction A B C`. -/
def quotientFixedPointIdealAlgEquivOfEqOne (hB : ρB = 1) (hC : ρC = 1) :
    (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) ≃ₐ[A] WeilRestriction A B C :=
  let _ := inducedMulSemiringAction ρB ρC h
  MulSemiringAction.quotientFixedPointIdealAlgEquivOfTrivial A
    ((MulSemiringAction.fixedPointIdeal_eq_bot_iff).mp
      (fixedPointIdeal_eq_bot_of_eq_one ρB ρC h hB hC))

@[simp]
theorem quotientFixedPointIdealAlgEquivOfEqOne_mk (hB : ρB = 1) (hC : ρC = 1)
    (x : WeilRestriction A B C) :
    quotientFixedPointIdealAlgEquivOfEqOne ρB ρC h hB hC
        (Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) x) = x := by
  let _ := inducedMulSemiringAction ρB ρC h
  exact MulSemiringAction.quotientFixedPointIdealAlgEquivOfTrivial_mk A _ x

@[simp]
theorem quotientFixedPointIdealAlgEquivOfEqOne_symm_apply (hB : ρB = 1) (hC : ρC = 1)
    (x : WeilRestriction A B C) :
    (quotientFixedPointIdealAlgEquivOfEqOne ρB ρC h hB hC).symm x =
      Ideal.Quotient.mk (fixedPointIdeal ρB ρC h) x := by
  let _ := inducedMulSemiringAction ρB ρC h
  exact MulSemiringAction.quotientFixedPointIdealAlgEquivOfTrivial_symm_apply A _ x

/-- When `Γ` is finite, `fixedPointIdeal ρB ρC h` is finitely generated. -/
theorem fg_fixedPointIdeal [Finite Γ] : (fixedPointIdeal ρB ρC h).FG := by
  let _ := inducedMulSemiringAction ρB ρC h
  have := inducedSMulCommClass ρB ρC h
  exact MulSemiringAction.fg_fixedPointIdeal (R := A)

/-- When `Γ` is finite, `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` is finitely presented
over `A`. -/
instance finitePresentation_quotient_fixedPointIdeal [Finite Γ] :
    FinitePresentation A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) := by
  let _ := inducedMulSemiringAction ρB ρC h
  have := inducedSMulCommClass ρB ρC h
  exact MulSemiringAction.finitePresentation_quotient_fixedPointIdeal

/-- **Formal étaleness of fixed points of a Weil restriction.** If `C` is formally étale over `B`,
then for any monoid `Γ` acting compatibly on `B` and `C`, the fixed-point quotient
`WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` is formally étale over `A`. -/
instance formallyEtale_quotient_fixedPointIdeal [FormallyEtale B C] :
    FormallyEtale A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) := by
  let _ := inducedMulSemiringAction ρB ρC h
  have := inducedSMulCommClass ρB ρC h
  exact MulSemiringAction.formallyEtale_quotient_fixedPointIdeal

/-- **Étaleness of fixed points of a Weil restriction.** If `Γ` is finite and `C` is étale over
`B`, then `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` is étale over `A`. -/
instance etale_quotient_fixedPointIdeal [Finite Γ] [Etale B C] :
    Etale A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) := by
  let _ := inducedMulSemiringAction ρB ρC h
  have := inducedSMulCommClass ρB ρC h
  exact MulSemiringAction.etale_quotient_fixedPointIdeal

end General

section TameSmooth

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Module.Finite A B] [Module.Projective A B]
  [FinitePresentation B C]
  {Γ : Type*} [Group Γ] [Finite Γ] (ρB : Γ →* (B ≃ₐ[A] B)) (ρC : Γ →* RingAut C)
  (h : ∀ γ b, ρC γ (algebraMap B C b) = algebraMap B C (ρB γ b))

/-- **Edixhoven's formal smoothness theorem for Weil restrictions.** Let `B` be finite projective
over `A`, `C` finitely presented and formally smooth over `B`, and `Γ` a finite group with
`(Nat.card Γ : A)` invertible in `A` acting compatibly on `B` and `C`. Then the fixed-point
quotient `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` is formally smooth over `A`. -/
theorem formallySmooth_quotient_fixedPointIdeal [FormallySmooth B C]
    (hΓ : IsUnit (Nat.card Γ : A)) :
    FormallySmooth A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) := by
  let _ := inducedMulSemiringAction ρB ρC h
  have := inducedSMulCommClass ρB ρC h
  exact MulSemiringAction.formallySmooth_quotient_fixedPointIdeal hΓ

/-- **Edixhoven's smoothness theorem for Weil restrictions.** Let `B` be finite projective over `A`,
`C` smooth over `B`, and `Γ` a finite group with `(Nat.card Γ : A)` invertible in `A` acting on `B`
by `A`-algebra automorphisms and on `C` by compatible semilinear ring automorphisms. Then the
fixed-point quotient `WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h` — the coordinate ring of
`(Res_{B/A} Spec C)^Γ` — is smooth over `A`. -/
theorem smooth_quotient_fixedPointIdeal [Smooth B C] (hΓ : IsUnit (Nat.card Γ : A)) :
    Smooth A (WeilRestriction A B C ⧸ fixedPointIdeal ρB ρC h) := by
  let _ := inducedMulSemiringAction ρB ρC h
  have := inducedSMulCommClass ρB ρC h
  exact MulSemiringAction.smooth_quotient_fixedPointIdeal hΓ

end TameSmooth

section GaloisDescent

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  (Γ : Type*) [Group Γ] [MulSemiringAction Γ B] [SMulCommClass Γ A B]

private def baseChangeUniversalSection
    [Module.Finite A B] [Module.Projective A B]
    (D : Type*) [CommRing D] [Algebra A D] [FinitePresentation A D] :
    D →ₐ[A]
      B ⊗[A]
        (WeilRestriction A B (B ⊗[A] D) ⧸
          fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
            (MulSemiringAction.baseChangeRingAutHom A B Γ D)
            (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ D)) :=
  ((fixedPointsHomEquiv (MulSemiringAction.toAlgAut Γ A B)
      (MulSemiringAction.baseChangeRingAutHom A B Γ D)
      (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ D)
      (WeilRestriction A B (B ⊗[A] D) ⧸
        fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
          (MulSemiringAction.baseChangeRingAutHom A B Γ D)
          (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ D))
      (AlgHom.id A _)).1.restrictScalars A).comp
    (Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D)

private theorem baseChangeUniversalSection_inv
    [Module.Finite A B] [Module.Projective A B]
    (D : Type*) [CommRing D] [Algebra A D] [FinitePresentation A D]
    (g : Γ) (d : D) :
    Algebra.TensorProduct.rTensor _ (MulSemiringAction.toAlgHom A B g)
        (baseChangeUniversalSection A B Γ D d) =
      baseChangeUniversalSection A B Γ D d := by
  have h1 := (fixedPointsHomEquiv (MulSemiringAction.toAlgAut Γ A B)
    (MulSemiringAction.baseChangeRingAutHom A B Γ D)
    (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ D) _
    (AlgHom.id A _)).2 g ((1 : B) ⊗ₜ[A] d)
  have hfix1 :
      MulSemiringAction.baseChangeRingAutHom A B Γ D g ((1 : B) ⊗ₜ[A] d) =
        (1 : B) ⊗ₜ[A] d := by simp
  rw [hfix1] at h1
  exact h1.symm

/-- **Galois descent for constant Weil restrictions.** Let `B` be finite projective over `A`, and
let a finite group `Γ` act on `B` with invariant ring `A`
(`[Algebra.IsInvariant A B Γ] [FaithfulSMul A B]`) such that `B` admits an element of trace `1`
(`∃ c : B, ∑ γ : Γ, γ • c = 1`). For every finitely presented `A`-algebra `D`, the `Γ`-fixed
quotient of `WeilRestriction A B (B ⊗[A] D)` is canonically isomorphic as an `A`-algebra to `D`. -/
def quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne
    [Module.Finite A B] [Module.Projective A B] [Fintype Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (D : Type*) [CommRing D] [Algebra A D] [FinitePresentation A D]
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    (WeilRestriction A B (B ⊗[A] D) ⧸
      fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
        (MulSemiringAction.baseChangeRingAutHom A B Γ D)
        (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ D)) ≃ₐ[A] D :=
  let ρB : Γ →* (B ≃ₐ[A] B) := MulSemiringAction.toAlgAut Γ A B
  let ρBD := MulSemiringAction.baseChangeRingAutHom A B Γ D
  let hBD := MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ D
  let Q := WeilRestriction A B (B ⊗[A] D) ⧸ fixedPointIdeal ρB ρBD hBD
  let fwd : Q →ₐ[A] D := (fixedPointsHomEquiv ρB ρBD hBD D).symm
    ⟨AlgHom.id B (B ⊗[A] D), fun γ x ↦ MulSemiringAction.baseChangeRingAutHom_apply A B Γ D γ x⟩
  let bwd : D →ₐ[A] Q := MulSemiringAction.retractToBaseAlgHom A B Γ hc
    (baseChangeUniversalSection A B Γ D) (baseChangeUniversalSection_inv A B Γ D)
  AlgEquiv.ofAlgHom fwd bwd
    (by
      ext d
      apply MulSemiringAction.includeRight_injective_of_exists_trace_one A B Γ hc
      have hd :=
        congr($(fixedPointsHomEquiv_comp ρB ρBD hBD (AlgHom.id A Q) fwd) ((1 : B) ⊗ₜ[A] d))
      rw [AlgHom.comp_id, (fixedPointsHomEquiv ρB ρBD hBD D).apply_symm_apply] at hd
      calc
        (Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D) (fwd (bwd d))
            = Algebra.TensorProduct.lTensor (S := B) B fwd
                ((Algebra.TensorProduct.includeRight : Q →ₐ[A] B ⊗[A] Q) (bwd d)) := by simp
        _ = Algebra.TensorProduct.lTensor (S := B) B fwd
              (baseChangeUniversalSection A B Γ D d) := by
              rw [MulSemiringAction.includeRight_retractToBaseAlgHom_apply]
        _ = (1 : B) ⊗ₜ[A] d := hd.symm)
    (by
      apply fixedPoints_hom_ext ρB ρBD hBD
      rw [fixedPointsHomEquiv_comp, (fixedPointsHomEquiv ρB ρBD hBD D).apply_symm_apply]
      apply Algebra.TensorProduct.ext
      · ext
      · ext d
        simp [bwd, baseChangeUniversalSection, Q, ρB, ρBD])

@[simp]
theorem quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne_mk
    [Module.Finite A B] [Module.Projective A B] [Fintype Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (D : Type*) [CommRing D] [Algebra A D] [FinitePresentation A D]
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1)
    (x : WeilRestriction A B (B ⊗[A] D)) :
    quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne A B Γ D hc
        (Ideal.Quotient.mk
          (fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
            (MulSemiringAction.baseChangeRingAutHom A B Γ D)
            (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ D)) x) =
      (homEquiv A B (B ⊗[A] D) D).symm (AlgHom.id B (B ⊗[A] D)) x := by
  rw [quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne, AlgEquiv.ofAlgHom_apply,
    fixedPointsHomEquiv_symm_apply_mk]

@[simp]
theorem one_tmul_quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne_symm_apply
    [Module.Finite A B] [Module.Projective A B] [Fintype Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (D : Type*) [CommRing D] [Algebra A D] [FinitePresentation A D]
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) (d : D) :
    (1 : B) ⊗ₜ[A]
        (quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne A B Γ D hc).symm d =
      Algebra.TensorProduct.lTensor (S := B) B
        (Ideal.Quotient.mkₐ A
          (fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
            (MulSemiringAction.baseChangeRingAutHom A B Γ D)
            (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ D)))
        (universalPoint A B (B ⊗[A] D) ((1 : B) ⊗ₜ[A] d)) := by
  rw [quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne, AlgEquiv.ofAlgHom_symm_apply,
    MulSemiringAction.one_tmul_retractToBaseAlgHom_apply]
  simp [baseChangeUniversalSection]

theorem includeRight_quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne_symm_apply
    [Module.Finite A B] [Module.Projective A B] [Fintype Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (D : Type*) [CommRing D] [Algebra A D] [FinitePresentation A D]
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) (d : D) :
    (Algebra.TensorProduct.includeRight : _ →ₐ[A] B ⊗[A] _)
        ((quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne A B Γ D hc).symm d) =
      Algebra.TensorProduct.lTensor (S := B) B
        (Ideal.Quotient.mkₐ A
          (fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
            (MulSemiringAction.baseChangeRingAutHom A B Γ D)
            (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ D)))
        (universalPoint A B (B ⊗[A] D) ((1 : B) ⊗ₜ[A] d)) := by
  simp

private theorem exists_sum_smul_eq_one_of_isUnit_card [Fintype Γ]
    (hΓ : IsUnit (Nat.card Γ : A)) :
    ∃ c : B, ∑ γ : Γ, γ • c = 1 := by
  refine ⟨algebraMap A B ↑hΓ.unit⁻¹, ?_⟩
  have hmul : (Fintype.card Γ : A) * ↑hΓ.unit⁻¹ = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Units.mul_inv_eq_one.mpr rfl
  simp only [smul_algebraMap, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul A,
    Algebra.smul_def, ← map_mul, hmul, map_one]

/-- **Tame Galois descent for constant Weil restrictions.** Let `B` be finite projective over `A`,
and let a finite group `Γ` with `(Nat.card Γ : A)` invertible act on `B` with invariant ring `A`
(`[Algebra.IsInvariant A B Γ] [FaithfulSMul A B]`). For every finitely presented `A`-algebra `D`,
the `Γ`-fixed quotient of `WeilRestriction A B (B ⊗[A] D)` is canonically isomorphic as an
`A`-algebra to `D`. -/
def quotientFixedPointIdealBaseChangeAlgEquiv
    [Module.Finite A B] [Module.Projective A B] [Finite Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (D : Type*) [CommRing D] [Algebra A D] [FinitePresentation A D]
    (hΓ : IsUnit (Nat.card Γ : A)) :
    (WeilRestriction A B (B ⊗[A] D) ⧸
      fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
        (MulSemiringAction.baseChangeRingAutHom A B Γ D)
        (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ D)) ≃ₐ[A] D := by
  have := Fintype.ofFinite Γ
  exact quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne A B Γ D
    (exists_sum_smul_eq_one_of_isUnit_card A B Γ hΓ)

@[simp]
theorem quotientFixedPointIdealBaseChangeAlgEquiv_mk
    [Module.Finite A B] [Module.Projective A B] [Finite Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (D : Type*) [CommRing D] [Algebra A D] [FinitePresentation A D]
    (hΓ : IsUnit (Nat.card Γ : A))
    (x : WeilRestriction A B (B ⊗[A] D)) :
    quotientFixedPointIdealBaseChangeAlgEquiv A B Γ D hΓ
        (Ideal.Quotient.mk
          (fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
            (MulSemiringAction.baseChangeRingAutHom A B Γ D)
            (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ D)) x) =
      (homEquiv A B (B ⊗[A] D) D).symm (AlgHom.id B (B ⊗[A] D)) x := by
  rw [quotientFixedPointIdealBaseChangeAlgEquiv,
    quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne_mk]

@[simp]
theorem one_tmul_quotientFixedPointIdealBaseChangeAlgEquiv_symm_apply
    [Module.Finite A B] [Module.Projective A B] [Finite Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (D : Type*) [CommRing D] [Algebra A D] [FinitePresentation A D]
    (hΓ : IsUnit (Nat.card Γ : A)) (d : D) :
    (1 : B) ⊗ₜ[A]
        (quotientFixedPointIdealBaseChangeAlgEquiv A B Γ D hΓ).symm d =
      Algebra.TensorProduct.lTensor (S := B) B
        (Ideal.Quotient.mkₐ A
          (fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
            (MulSemiringAction.baseChangeRingAutHom A B Γ D)
            (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ D)))
        (universalPoint A B (B ⊗[A] D) ((1 : B) ⊗ₜ[A] d)) := by
  rw [quotientFixedPointIdealBaseChangeAlgEquiv,
    one_tmul_quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne_symm_apply]

theorem includeRight_quotientFixedPointIdealBaseChangeAlgEquiv_symm_apply
    [Module.Finite A B] [Module.Projective A B] [Finite Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (D : Type*) [CommRing D] [Algebra A D] [FinitePresentation A D]
    (hΓ : IsUnit (Nat.card Γ : A)) (d : D) :
    (Algebra.TensorProduct.includeRight : _ →ₐ[A] B ⊗[A] _)
        ((quotientFixedPointIdealBaseChangeAlgEquiv A B Γ D hΓ).symm d) =
      Algebra.TensorProduct.lTensor (S := B) B
        (Ideal.Quotient.mkₐ A
          (fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
            (MulSemiringAction.baseChangeRingAutHom A B Γ D)
            (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ D)))
        (universalPoint A B (B ⊗[A] D) ((1 : B) ⊗ₜ[A] d)) := by
  simp

private theorem baseChangeRingAutHom_polyEquivTensor_symm (γ : Γ) (z : B ⊗[A] A[X]) :
    MulSemiringAction.toRingAut Γ B[X] γ ((polyEquivTensor' A B).symm z) =
      (polyEquivTensor' A B).symm
        (MulSemiringAction.baseChangeRingAutHom A B Γ A[X] γ z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b q =>
    ext k
    simp [smul_mul', smul_algebraMap]

/-- **Galois descent of the affine line.** Under the trace-one hypothesis of
`quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne`, the `Γ`-fixed quotient of
`WeilRestriction A B B[X]` for the coefficientwise `Γ`-action on `B[X]` is isomorphic as an
`A`-algebra to `A[X]`. -/
def quotientFixedPointIdealPolynomialAlgEquivOfExistsTraceOne
    [Module.Finite A B] [Module.Projective A B] [Fintype Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) :
    (WeilRestriction A B B[X] ⧸
      fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B) (MulSemiringAction.toRingAut Γ B[X])
        (MulSemiringAction.toRingAut_polynomial_algebraMap A B Γ)) ≃ₐ[A] A[X] :=
  (quotientFixedPointIdealAlgEquivOfEquiv
    (MulSemiringAction.toAlgAut Γ A B)
    (MulSemiringAction.baseChangeRingAutHom A B Γ A[X])
    (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ A[X])
    (MulSemiringAction.toRingAut Γ B[X])
    (MulSemiringAction.toRingAut_polynomial_algebraMap A B Γ)
    (polyEquivTensor' A B).symm (baseChangeRingAutHom_polyEquivTensor_symm A B Γ)).symm.trans
      (quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne A B Γ A[X] hc)

@[simp]
theorem quotientFixedPointIdealPolynomialAlgEquivOfExistsTraceOne_mk
    [Module.Finite A B] [Module.Projective A B] [Fintype Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1)
    (x : WeilRestriction A B B[X]) :
    quotientFixedPointIdealPolynomialAlgEquivOfExistsTraceOne A B Γ hc
        (Ideal.Quotient.mk
          (fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
            (MulSemiringAction.toRingAut Γ B[X])
            (MulSemiringAction.toRingAut_polynomial_algebraMap A B Γ)) x) =
      (homEquiv A B B[X] A[X]).symm (polyEquivTensor' A B).toAlgHom x := by
  rw [quotientFixedPointIdealPolynomialAlgEquivOfExistsTraceOne, AlgEquiv.trans_apply,
    quotientFixedPointIdealAlgEquivOfEquiv_symm_mk, AlgEquiv.symm_symm,
    quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne_mk]
  have hmap :
      ((homEquiv A B (B ⊗[A] A[X]) A[X]).symm (AlgHom.id B (B ⊗[A] A[X]))).comp
          (map A B (polyEquivTensor' A B).toAlgHom) =
        (homEquiv A B B[X] A[X]).symm (polyEquivTensor' A B).toAlgHom := by
    apply (homEquiv A B B[X] A[X]).injective
    rw [homEquiv_comp_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply, AlgHom.id_comp]
  exact congr($hmap x)

@[simp]
theorem one_tmul_quotientFixedPointIdealPolynomialAlgEquivOfExistsTraceOne_symm_apply
    [Module.Finite A B] [Module.Projective A B] [Fintype Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (hc : ∃ c : B, ∑ γ : Γ, γ • c = 1) (p : A[X]) :
    (1 : B) ⊗ₜ[A]
        (quotientFixedPointIdealPolynomialAlgEquivOfExistsTraceOne A B Γ hc).symm p =
      Algebra.TensorProduct.lTensor (S := B) B
        (Ideal.Quotient.mkₐ A
          (fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
            (MulSemiringAction.toRingAut Γ B[X])
            (MulSemiringAction.toRingAut_polynomial_algebraMap A B Γ)))
        (universalPoint A B B[X] (p.map (algebraMap A B))) := by
  rw [quotientFixedPointIdealPolynomialAlgEquivOfExistsTraceOne, AlgEquiv.symm_trans_apply,
    AlgEquiv.symm_symm]
  let e := quotientFixedPointIdealAlgEquivOfEquiv
    (MulSemiringAction.toAlgAut Γ A B)
    (MulSemiringAction.baseChangeRingAutHom A B Γ A[X])
    (MulSemiringAction.baseChangeRingAutHom_algebraMap A B Γ A[X])
    (MulSemiringAction.toRingAut Γ B[X])
    (MulSemiringAction.toRingAut_polynomial_algebraMap A B Γ)
    (polyEquivTensor' A B).symm (baseChangeRingAutHom_polyEquivTensor_symm A B Γ)
  have hlTensor :
      Algebra.TensorProduct.lTensor (S := B) B e.toAlgHom
          ((1 : B) ⊗ₜ[A]
            (quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne A B Γ A[X] hc).symm p) =
        (1 : B) ⊗ₜ[A]
          e ((quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne A B Γ A[X] hc).symm p) := by
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom]
  rw [← hlTensor, one_tmul_quotientFixedPointIdealBaseChangeAlgEquivOfExistsTraceOne_symm_apply,
    ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_id_comp]
  have hmk :
      e.toAlgHom.comp (Ideal.Quotient.mkₐ A _) =
        (Ideal.Quotient.mkₐ A _).comp (map A B (polyEquivTensor' A B).symm.toAlgHom) := by
    apply AlgHom.ext
    intro x
    simp [e]
  rw [hmk, Algebra.TensorProduct.map_id_comp, AlgHom.comp_apply, lTensor_map_universalPoint]
  simp

/-- **Tame Galois descent of the affine line.** Under the same hypotheses as
`quotientFixedPointIdealBaseChangeAlgEquiv`, the `Γ`-fixed quotient of `WeilRestriction A B B[X]`
for the coefficientwise `Γ`-action on `B[X]` is isomorphic as an `A`-algebra to `A[X]`. -/
def quotientFixedPointIdealPolynomialAlgEquiv
    [Module.Finite A B] [Module.Projective A B] [Finite Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (hΓ : IsUnit (Nat.card Γ : A)) :
    (WeilRestriction A B B[X] ⧸
      fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B) (MulSemiringAction.toRingAut Γ B[X])
        (MulSemiringAction.toRingAut_polynomial_algebraMap A B Γ)) ≃ₐ[A] A[X] := by
  have := Fintype.ofFinite Γ
  exact quotientFixedPointIdealPolynomialAlgEquivOfExistsTraceOne A B Γ
    (exists_sum_smul_eq_one_of_isUnit_card A B Γ hΓ)

@[simp]
theorem quotientFixedPointIdealPolynomialAlgEquiv_mk
    [Module.Finite A B] [Module.Projective A B] [Finite Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (hΓ : IsUnit (Nat.card Γ : A))
    (x : WeilRestriction A B B[X]) :
    quotientFixedPointIdealPolynomialAlgEquiv A B Γ hΓ
        (Ideal.Quotient.mk
          (fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
            (MulSemiringAction.toRingAut Γ B[X])
            (MulSemiringAction.toRingAut_polynomial_algebraMap A B Γ)) x) =
      (homEquiv A B B[X] A[X]).symm (polyEquivTensor' A B).toAlgHom x := by
  rw [quotientFixedPointIdealPolynomialAlgEquiv,
    quotientFixedPointIdealPolynomialAlgEquivOfExistsTraceOne_mk]

@[simp]
theorem one_tmul_quotientFixedPointIdealPolynomialAlgEquiv_symm_apply
    [Module.Finite A B] [Module.Projective A B] [Finite Γ]
    [Algebra.IsInvariant A B Γ] [FaithfulSMul A B]
    (hΓ : IsUnit (Nat.card Γ : A)) (p : A[X]) :
    (1 : B) ⊗ₜ[A]
        (quotientFixedPointIdealPolynomialAlgEquiv A B Γ hΓ).symm p =
      Algebra.TensorProduct.lTensor (S := B) B
        (Ideal.Quotient.mkₐ A
          (fixedPointIdeal (MulSemiringAction.toAlgAut Γ A B)
            (MulSemiringAction.toRingAut Γ B[X])
            (MulSemiringAction.toRingAut_polynomial_algebraMap A B Γ)))
        (universalPoint A B B[X] (p.map (algebraMap A B))) := by
  rw [quotientFixedPointIdealPolynomialAlgEquiv,
    one_tmul_quotientFixedPointIdealPolynomialAlgEquivOfExistsTraceOne_symm_apply]

end GaloisDescent

end TauCeti.Algebra.WeilRestriction
