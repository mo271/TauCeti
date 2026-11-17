/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Algebra.Star.Subalgebra
public import TauCeti.Analysis.CStarAlgebra.InductiveLimit.Basic
import TauCeti.Analysis.CStarAlgebra.Quotient

/-!
# Universal property, recognition criteria, and functoriality of C⋆-inductive limits

This file establishes the categorical universal property of `TauCeti.CStarInductiveLimit`, together
with its range, surjectivity, injectivity, and recognition isomorphism criteria, functoriality on
morphisms of directed systems, cofinal subsystem invariance, and the constant-system equivalence.

## Main definitions

* `TauCeti.CStarInductiveLimit.lift`: universal property for compatible families of nonunital
  `⋆`-homomorphisms into a C⋆-algebra `B`.
* `TauCeti.CStarInductiveLimit.liftUnital`: unital universal property for compatible families of
  unital `⋆`-homomorphisms into a unital C⋆-algebra `B`.
* `TauCeti.CStarInductiveLimit.starAlgEquivOfDense` and
  `TauCeti.CStarInductiveLimit.starAlgEquivOfDenseOfInjective`: recognition isomorphisms identifying
  a C⋆-algebra `B` with `CStarInductiveLimit A f` from a compatible family with dense union of
  ranges and matching kernels.
* `TauCeti.CStarInductiveLimit.starAlgEquivOfNonUnitalSubalgebra` and
  `TauCeti.CStarInductiveLimit.starAlgEquivOfStarSubalgebra`: recognition isomorphisms identifying a
  C⋆-algebra with the inductive limit of a monotone family of closed `⋆`-subalgebras whose union is
  dense.
* `TauCeti.CStarInductiveLimit.map`, `TauCeti.CStarInductiveLimit.mapUnital`, and
  `TauCeti.CStarInductiveLimit.mapEquiv`: functoriality of `CStarInductiveLimit` on compatible
  families of `⋆`-homomorphisms and `⋆`-equivalences.
* `TauCeti.CStarInductiveLimit.cofinalEquiv`: passing to a cofinal subsystem produces an isomorphic
  C⋆-inductive limit.
* `TauCeti.CStarInductiveLimit.constEquiv`: the inductive limit of a constant directed system is
  canonically `⋆`-isomorphic to the constant algebra.

## Main results

* `TauCeti.CStarInductiveLimit.range_lift_eq_closure_iUnion`: the range of `lift` is the closure of
  the union of the stage ranges.
* `TauCeti.CStarInductiveLimit.surjective_lift_iff`: `lift` is surjective if and only if the union
  of the stage ranges is dense.
* `TauCeti.CStarInductiveLimit.injective_lift_iff` and
  `TauCeti.CStarInductiveLimit.isometry_lift_iff`: `lift` is injective (equivalently, isometric) if
  and only if every stage element annihilated by `g i` already vanishes in the inductive limit.

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Section II.8.2 (Propositions II.8.2.1 and II.8.2.2).
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra

namespace TauCeti.CStarInductiveLimit

section StageHomHelper

variable {ι : Type*} {A : ι → Type*} [∀ i, NonUnitalCStarAlgebra (A i)]
variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- Helper converting a stage `⋆`-homomorphism into a contractive continuous linear map. -/
private def stageHomCLM (g : ∀ i, A i →⋆ₙₐ[ℂ] B) (i : ι) : A i →L[ℂ] B :=
  let L : A i →ₗ[ℂ] B :=
    { toFun := g i
      map_add' := map_add (g i)
      map_smul' := map_smul (g i) }
  L.mkContinuous 1 fun a => by
    change ‖g i a‖ ≤ 1 * ‖a‖
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le (g i) a

private theorem stageHomCLM_apply (g : ∀ i, A i →⋆ₙₐ[ℂ] B) (i : ι) (a : A i) :
    stageHomCLM g i a = g i a :=
  rfl

private theorem stageHomCLM_norm_le (g : ∀ i, A i →⋆ₙₐ[ℂ] B) (i : ι) :
    ‖stageHomCLM g i‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one fun a => by
    change ‖g i a‖ ≤ 1 * ‖a‖
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le (g i) a

end StageHomHelper

section NonUnital

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, NonUnitalCStarAlgebra (A i)]
variable [∀ i j h, NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

section Lift

variable {B : Type*} [NonUnitalCStarAlgebra B]

variable (A f) in
/-- **Universal property of `CStarInductiveLimit` (nonunital).** Every compatible family of
`⋆`-algebra homomorphisms `g i : A i →⋆ₙₐ[ℂ] B` into a C⋆-algebra `B` factors uniquely through a
`⋆`-algebra homomorphism `CStarInductiveLimit A f →⋆ₙₐ[ℂ] B`. -/
def lift (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) :
    CStarInductiveLimit A f →⋆ₙₐ[ℂ] B :=
  let L : CStarInductiveLimit A f →L[ℂ] B :=
    liftCLM A f (stageHomCLM g)
      (by intro i j hij a; rw [stageHomCLM_apply, stageHomCLM_apply]; exact hg hij a)
      (C := 1) (stageHomCLM_norm_le g)
  { toFun := L
    map_smul' := L.map_smul
    map_zero' := L.map_zero
    map_add' := L.map_add
    map_mul' x y := by
      induction x, y using induction_on₂ with
      | hp =>
        exact isClosed_eq (L.continuous.comp continuous_mul)
          ((L.continuous.comp continuous_fst).mul (L.continuous.comp continuous_snd))
      | ih i a b =>
        dsimp only [L]
        rw [← map_mul, liftCLM_of, liftCLM_of, liftCLM_of]
        exact map_mul (g i) a b
    map_star' x := by
      induction x using induction_on with
      | hp =>
        exact isClosed_eq (L.continuous.comp continuous_star) (continuous_star.comp L.continuous)
      | ih i a =>
        dsimp only [L]
        rw [← map_star, liftCLM_of, liftCLM_of]
        exact map_star (g i) a }

/-- Evaluating `lift` on the canonical image of stage `i` recovers `g i`. -/
@[simp]
theorem lift_of (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) (i : ι) (a : A i) :
    lift A f g hg (of A f i a) = g i a :=
  liftCLM_of (f := f) (stageHomCLM g)
    (by intro i j hij a; rw [stageHomCLM_apply, stageHomCLM_apply]; exact hg hij a)
    (stageHomCLM_norm_le g) i a

/-- Composing `lift` with `of A f i` recovers `g i`. -/
@[simp]
theorem lift_comp_of (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) (i : ι) :
    (lift A f g hg).comp (of A f i) = g i :=
  NonUnitalStarAlgHom.ext fun a => lift_of g hg i a

/-- Uniqueness part of the universal property of `CStarInductiveLimit`. -/
theorem lift_unique (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a)
    {φ : CStarInductiveLimit A f →⋆ₙₐ[ℂ] B} (hφ : ∀ i, φ.comp (of A f i) = g i) :
    φ = lift A f g hg :=
  hom_ext fun i => (hφ i).trans (lift_comp_of g hg i).symm

/-- Lifting the canonical stage maps `of A f` yields the identity homomorphism. -/
@[simp]
theorem lift_of_self :
    lift A f (of A f) (fun _ _ hij a => of_f hij a) =
      NonUnitalStarAlgHom.id ℂ (CStarInductiveLimit A f) :=
  (lift_unique (of A f) (fun _ _ hij a => of_f hij a) fun _ => rfl).symm

/-- Post-composing `lift` with a `⋆`-homomorphism `ψ` commutes with lifting. -/
theorem comp_lift {C : Type*} [NonUnitalCStarAlgebra C] (ψ : B →⋆ₙₐ[ℂ] C)
    (g : ∀ i, A i →⋆ₙₐ[ℂ] B) (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) :
    ψ.comp (lift A f g hg) =
      lift A f (fun i => ψ.comp (g i)) (fun _ _ hij a => congrArg ψ (hg hij a)) :=
  lift_unique _ _ fun i => by
    ext a
    simp

/-- **Range formula for `lift`.** The range of the lifted `⋆`-homomorphism is the closure of the
union of the ranges of the stage maps. -/
theorem range_lift_eq_closure_iUnion (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) :
    Set.range (lift A f g hg) = closure (⋃ i, Set.range (g i)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using induction_on with
    | hp => exact isClosed_closure.preimage (map_continuous (lift A f g hg))
    | ih i a =>
      rw [lift_of]
      exact subset_closure (Set.mem_iUnion.2 ⟨i, a, rfl⟩)
  · refine closure_minimal ?_ (lift A f g hg).isClosed_setRange
    refine Set.iUnion_subset fun i => ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨of A f i a, lift_of g hg i a⟩

/-- **Surjectivity criterion for `lift`.** The lifted `⋆`-homomorphism is surjective if and only if
the union of the stage ranges is dense in `B`. -/
theorem surjective_lift_iff (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) :
    Function.Surjective (lift A f g hg) ↔ Dense (⋃ i, Set.range (g i)) := by
  rw [← Set.range_eq_univ, range_lift_eq_closure_iUnion, dense_iff_closure_eq]

/-- **Isometry criterion for `lift`.** The lifted `⋆`-homomorphism is isometric if and only if
every stage element in `ker (g i)` already vanishes in `CStarInductiveLimit A f`. -/
theorem isometry_lift_iff (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) :
    Isometry (lift A f g hg) ↔ ∀ i (a : A i), g i a = 0 → of A f i a = 0 := by
  refine ⟨fun hiso i a hga => hiso.injective ?_, fun hker => ?_⟩
  · rw [lift_of, hga, map_zero]
  · refine AddMonoidHomClass.isometry_of_norm (lift A f g hg) fun x => ?_
    induction x using induction_on with
    | hp =>
      exact isClosed_eq (continuous_norm.comp (map_continuous (lift A f g hg))) continuous_norm
    | ih i a =>
      rw [lift_of]
      let K : TwoSidedIdeal (A i) := TwoSidedIdeal.ker (of A f i)
      let ψ : A i ⧸ K →⋆ₙₐ[ℂ] B :=
        TwoSidedIdeal.Quotient.liftStarAlgHom K (g i) fun b hb => by
          rw [← lift_of g hg i b, (TwoSidedIdeal.mem_ker (of A f i)).mp hb, map_zero]
      have hψ_inj : Function.Injective ψ :=
        TwoSidedIdeal.Quotient.liftStarAlgHom_injective_of_ker_le _ fun b hb =>
          (TwoSidedIdeal.mem_ker (of A f i)).mpr (hker i b ((TwoSidedIdeal.mem_ker (g i)).mp hb))
      have h1 : ‖g i a‖ = ‖TwoSidedIdeal.Quotient.mk K a‖ := by
        rw [← TwoSidedIdeal.Quotient.liftStarAlgHom_mk K (g i) _ a]
        exact NonUnitalStarAlgHom.norm_map ψ hψ_inj _
      have h2 : ‖of A f i a‖ = ‖TwoSidedIdeal.Quotient.mk K a‖ := by
        rw [← (of A f i).quotientKerHom_mk a]
        exact NonUnitalStarAlgHom.norm_map _ (of A f i).quotientKerHom_injective _
      exact h1.trans h2.symm

/-- **Injectivity criterion for `lift`.** The lifted `⋆`-homomorphism is injective if and only if
every stage element in `ker (g i)` already vanishes in `CStarInductiveLimit A f`. -/
theorem injective_lift_iff (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) :
    Function.Injective (lift A f g hg) ↔ ∀ i (a : A i), g i a = 0 → of A f i a = 0 :=
  ⟨fun hinj => (isometry_lift_iff g hg).mp (NonUnitalStarAlgHom.isometry _ hinj),
    fun hker => ((isometry_lift_iff g hg).mpr hker).injective⟩

/-- If every stage map `g i` is injective, then `lift A f g hg` is isometric. -/
theorem isometry_lift_of_injective (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a)
    (hinj : ∀ i, Function.Injective (g i)) : Isometry (lift A f g hg) :=
  (isometry_lift_iff g hg).mpr fun i a ha => by
    have : a = 0 := hinj i (ha.trans (map_zero (g i)).symm)
    rw [this, map_zero]

/-- If every stage map `g i` is injective, then `lift A f g hg` is injective. -/
theorem injective_lift_of_injective (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a)
    (hinj : ∀ i, Function.Injective (g i)) : Function.Injective (lift A f g hg) :=
  (isometry_lift_of_injective g hg hinj).injective

variable (A f) in
/-- **Recognition isomorphism for C⋆-inductive limits.** A compatible family `g i : A i →⋆ₙₐ[ℂ] B`
whose union of ranges is dense in `B` and whose stage kernels lie inside `ker (of A f i)` induces
an isometric `⋆`-algebra isomorphism `CStarInductiveLimit A f ≃⋆ₐ[ℂ] B`. -/
def starAlgEquivOfDense (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a)
    (hdense : Dense (⋃ i, Set.range (g i)))
    (hker : ∀ i (a : A i), g i a = 0 → of A f i a = 0) :
    CStarInductiveLimit A f ≃⋆ₐ[ℂ] B :=
  StarAlgEquiv.ofBijective (lift A f g hg)
    ⟨(injective_lift_iff g hg).mpr hker, (surjective_lift_iff g hg).mpr hdense⟩

/-- Evaluating `starAlgEquivOfDense` on stage `i` recovers `g i`. -/
@[simp]
theorem starAlgEquivOfDense_of (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a)
    (hdense : Dense (⋃ i, Set.range (g i)))
    (hker : ∀ i (a : A i), g i a = 0 → of A f i a = 0) (i : ι) (a : A i) :
    starAlgEquivOfDense A f g hg hdense hker (of A f i a) = g i a :=
  lift_of g hg i a

variable (A f) in
/-- **Recognition isomorphism (injective stage maps).** A compatible family of injective
`⋆`-homomorphisms `g i : A i →⋆ₙₐ[ℂ] B` with dense union of ranges identifies `B` with
`CStarInductiveLimit A f`. -/
def starAlgEquivOfDenseOfInjective (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a)
    (hdense : Dense (⋃ i, Set.range (g i)))
    (hinj : ∀ i, Function.Injective (g i)) :
    CStarInductiveLimit A f ≃⋆ₐ[ℂ] B :=
  starAlgEquivOfDense A f g hg hdense fun i a ha => by
    have : a = 0 := hinj i (ha.trans (map_zero (g i)).symm)
    rw [this, map_zero]

/-- Evaluating `starAlgEquivOfDenseOfInjective` on stage `i` recovers `g i`. -/
@[simp]
theorem starAlgEquivOfDenseOfInjective_of (g : ∀ i, A i →⋆ₙₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a)
    (hdense : Dense (⋃ i, Set.range (g i)))
    (hinj : ∀ i, Function.Injective (g i)) (i : ι) (a : A i) :
    starAlgEquivOfDenseOfInjective A f g hg hdense hinj (of A f i a) = g i a :=
  lift_of g hg i a

end Lift

end NonUnital

section Unital

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, CStarAlgebra (A i)]
variable [∀ i j h, AlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

-- Verify cross-module definitional compatibility of the unital and nonunital instances.
example :
    (instCStarAlgebra (A := A) (f := f)).toNonUnitalCStarAlgebra =
      instNonUnitalCStarAlgebra (A := A) (f := f) := by
  with_reducible_and_instances rfl

variable {B : Type*} [CStarAlgebra B]

variable (A f) in
/-- **Universal property of `CStarInductiveLimit` (unital).** Every compatible family of unital
`⋆`-algebra homomorphisms `g i : A i →⋆ₐ[ℂ] B` into a unital C⋆-algebra `B` factors uniquely
through a unital `⋆`-algebra homomorphism `CStarInductiveLimit A f →⋆ₐ[ℂ] B`. -/
def liftUnital (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) :
    CStarInductiveLimit A f →⋆ₐ[ℂ] B where
  __ := lift A f (fun i => (g i).toNonUnitalStarAlgHom)
    (by intro i j hij a; simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom] using hg hij a)
  map_one' := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    change lift A f (fun i => (g i).toNonUnitalStarAlgHom)
      (by intro i j hij a; simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom] using hg hij a) 1 = 1
    rw [← of_one (A := A) (f := f) i, lift_of]
    exact map_one (g i)
  commutes' c := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    change lift A f (fun i => (g i).toNonUnitalStarAlgHom)
      (by intro i j hij a; simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom] using hg hij a)
      (c • 1) = algebraMap ℂ B c
    rw [map_smul, ← of_one (A := A) (f := f) i, lift_of, StarAlgHom.coe_toNonUnitalStarAlgHom,
      map_one, ← Algebra.algebraMap_eq_smul_one]

/-- As a nonunital `⋆`-homomorphism, `liftUnital` is `lift`. -/
@[simp]
theorem toNonUnitalStarAlgHom_liftUnital (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) :
    (liftUnital A f g hg).toNonUnitalStarAlgHom =
      lift A f (fun i => (g i).toNonUnitalStarAlgHom)
        (by intro i j hij a; simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom] using hg hij a) :=
  (rfl)

/-- `liftUnital` has the same underlying function as `lift`. -/
@[simp]
theorem liftUnital_apply (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a)
    (x : CStarInductiveLimit A f) :
    liftUnital A f g hg x =
      lift A f (fun i => (g i).toNonUnitalStarAlgHom)
        (by intro i j hij a; simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom] using hg hij a)
        x :=
  (rfl)

/-- Evaluating `liftUnital` on the canonical unital image of stage `i` recovers `g i`. -/
theorem liftUnital_ofUnital (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) (i : ι) (a : A i) :
    liftUnital A f g hg (ofUnital A f i a) = g i a := by
  rw [liftUnital_apply, ofUnital_apply, lift_of]
  rfl

/-- Composing `liftUnital` with `ofUnital A f i` recovers `g i`. -/
@[simp]
theorem liftUnital_comp_ofUnital (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) (i : ι) :
    (liftUnital A f g hg).comp (ofUnital A f i) = g i :=
  StarAlgHom.ext fun a => liftUnital_ofUnital g hg i a

/-- Uniqueness part of the unital universal property of `CStarInductiveLimit`. -/
theorem liftUnital_unique (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a)
    {φ : CStarInductiveLimit A f →⋆ₐ[ℂ] B} (hφ : ∀ i, φ.comp (ofUnital A f i) = g i) :
    φ = liftUnital A f g hg :=
  unitalHom_ext fun i => (hφ i).trans (liftUnital_comp_ofUnital g hg i).symm

/-- Lifting the canonical unital stage maps `ofUnital A f` yields the identity homomorphism. -/
@[simp]
theorem liftUnital_ofUnital_self :
    liftUnital A f (ofUnital A f) (fun _ _ hij a => ofUnital_f hij a) =
      StarAlgHom.id ℂ (CStarInductiveLimit A f) :=
  (liftUnital_unique (ofUnital A f) (fun _ _ hij a => ofUnital_f hij a) fun _ => rfl).symm

/-- The range of `liftUnital` is the closure of the union of the stage ranges. -/
theorem range_liftUnital_eq_closure_iUnion (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) :
    Set.range (liftUnital A f g hg) = closure (⋃ i, Set.range (g i)) := by
  have hfun : ⇑(liftUnital A f g hg) = ⇑(lift A f (fun i => (g i).toNonUnitalStarAlgHom)
      (by intro i j hij a; simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom] using hg hij a)) :=
    rfl
  rw [hfun]
  exact range_lift_eq_closure_iUnion (fun i => (g i).toNonUnitalStarAlgHom) _

/-- `liftUnital` is surjective if and only if the union of the stage ranges is dense in `B`. -/
theorem surjective_liftUnital_iff (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) :
    Function.Surjective (liftUnital A f g hg) ↔ Dense (⋃ i, Set.range (g i)) := by
  have hfun : ⇑(liftUnital A f g hg) = ⇑(lift A f (fun i => (g i).toNonUnitalStarAlgHom)
      (by intro i j hij a; simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom] using hg hij a)) :=
    rfl
  rw [hfun]
  exact surjective_lift_iff (fun i => (g i).toNonUnitalStarAlgHom) _

/-- `liftUnital` is isometric if and only if every stage element in `ker (g i)` vanishes in
`CStarInductiveLimit A f`. -/
theorem isometry_liftUnital_iff (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) :
    Isometry (liftUnital A f g hg) ↔ ∀ i (a : A i), g i a = 0 → ofUnital A f i a = 0 := by
  have hfun : ⇑(liftUnital A f g hg) = ⇑(lift A f (fun i => (g i).toNonUnitalStarAlgHom)
      (by intro i j hij a; simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom] using hg hij a)) :=
    rfl
  rw [hfun]
  simpa only [ofUnital_apply, StarAlgHom.coe_toNonUnitalStarAlgHom] using
    isometry_lift_iff (fun i => (g i).toNonUnitalStarAlgHom) _

/-- `liftUnital` is injective if and only if every stage element in `ker (g i)` vanishes in
`CStarInductiveLimit A f`. -/
theorem injective_liftUnital_iff (g : ∀ i, A i →⋆ₐ[ℂ] B)
    (hg : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), g j (f i j hij a) = g i a) :
    Function.Injective (liftUnital A f g hg) ↔ ∀ i (a : A i), g i a = 0 → ofUnital A f i a = 0 := by
  have hfun : ⇑(liftUnital A f g hg) = ⇑(lift A f (fun i => (g i).toNonUnitalStarAlgHom)
      (by intro i j hij a; simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom] using hg hij a)) :=
    rfl
  rw [hfun]
  simpa only [ofUnital_apply, StarAlgHom.coe_toNonUnitalStarAlgHom] using
    injective_lift_iff (fun i => (g i).toNonUnitalStarAlgHom) _

end Unital

section SubalgebraRecognition

/-- Directed-system instance for a monotone family of nonunital `⋆`-subalgebras with inclusions. -/
instance instDirectedSystemNonUnitalStarSubalgebra {ι R B : Type*} [Preorder ι]
    [CommSemiring R] [NonUnitalSemiring B] [StarRing B] [Module R B]
    (S : ι →o NonUnitalStarSubalgebra R B) :
    DirectedSystem (fun i => S i)
      (fun _ _ h => ⇑(NonUnitalStarSubalgebra.inclusion (S.monotone h))) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

/-- Directed-system instance for a monotone family of unital `⋆`-subalgebras with inclusions. -/
instance instDirectedSystemStarSubalgebra {ι R B : Type*} [Preorder ι]
    [CommSemiring R] [StarRing R] [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]
    (S : ι →o StarSubalgebra R B) :
    DirectedSystem (fun i => S i)
      (fun _ _ h => ⇑(StarSubalgebra.inclusion (S.monotone h))) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]

/-- **Increasing-union recognition isomorphism (nonunital).** If `S : ι →o NonUnitalStarSubalgebra
ℂ B` is a monotone family of closed `⋆`-subalgebras of a C⋆-algebra `B` whose union is dense in
`B`, then `B` is canonically `⋆`-isomorphic to the C⋆-inductive limit of `(S, inclusion)`. -/
def starAlgEquivOfNonUnitalSubalgebra {B : Type*} [NonUnitalCStarAlgebra B]
    (S : ι →o NonUnitalStarSubalgebra ℂ B) [∀ i, IsClosed (S i : Set B)]
    (hdense : Dense (⋃ i, (S i : Set B))) :
    CStarInductiveLimit (fun i => S i)
      (fun _ _ h => NonUnitalStarSubalgebra.inclusion (S.monotone h)) ≃⋆ₐ[ℂ] B :=
  starAlgEquivOfDenseOfInjective (fun i => S i)
    (fun _ _ h => NonUnitalStarSubalgebra.inclusion (S.monotone h))
    (fun i => NonUnitalStarSubalgebraClass.subtype (S i)) (fun _ _ _ _ => rfl)
    (by
      have hrange : ∀ i, Set.range (NonUnitalStarSubalgebraClass.subtype (R := ℂ) (S i)) =
          (S i : Set B) := fun _ => Subtype.range_coe
      simpa only [hrange] using hdense)
    (fun _ => Subtype.val_injective)

/-- Evaluating `starAlgEquivOfNonUnitalSubalgebra` on stage `i` recovers the subtype coercion. -/
@[simp]
theorem starAlgEquivOfNonUnitalSubalgebra_of {B : Type*} [NonUnitalCStarAlgebra B]
    (S : ι →o NonUnitalStarSubalgebra ℂ B) [∀ i, IsClosed (S i : Set B)]
    (hdense : Dense (⋃ i, (S i : Set B))) (i : ι) (a : S i) :
    starAlgEquivOfNonUnitalSubalgebra S hdense
      (of (fun i => S i) (fun _ _ h => NonUnitalStarSubalgebra.inclusion (S.monotone h)) i a) =
        (a : B) := by
  unfold starAlgEquivOfNonUnitalSubalgebra
  exact starAlgEquivOfDenseOfInjective_of (A := fun i => S i) _ _ _ _ i a

/-- **Increasing-union recognition isomorphism (unital).** If `S : ι →o StarSubalgebra ℂ B` is a
monotone family of closed unital `⋆`-subalgebras of a unital C⋆-algebra `B` whose union is dense
in `B`, then `B` is canonically `⋆`-isomorphic to the C⋆-inductive limit of `(S, inclusion)`. -/
def starAlgEquivOfStarSubalgebra {B : Type*} [CStarAlgebra B]
    (S : ι →o StarSubalgebra ℂ B) [∀ i, IsClosed (S i : Set B)]
    (hdense : Dense (⋃ i, (S i : Set B))) :
    CStarInductiveLimit (fun i => S i)
      (fun _ _ h => StarSubalgebra.inclusion (S.monotone h)) ≃⋆ₐ[ℂ] B :=
  starAlgEquivOfDenseOfInjective (fun i => S i)
    (fun _ _ h => StarSubalgebra.inclusion (S.monotone h))
    (fun i => (S i).subtype.toNonUnitalStarAlgHom) (fun _ _ _ _ => rfl)
    (by
      have hrange : ∀ i, Set.range ((S i).subtype.toNonUnitalStarAlgHom) = (S i : Set B) :=
        fun _ => Subtype.range_coe
      simpa only [hrange] using hdense)
    (fun _ => Subtype.val_injective)

/-- Evaluating `starAlgEquivOfStarSubalgebra` on stage `i` recovers the subtype coercion. -/
@[simp]
theorem starAlgEquivOfStarSubalgebra_of {B : Type*} [CStarAlgebra B]
    (S : ι →o StarSubalgebra ℂ B) [∀ i, IsClosed (S i : Set B)]
    (hdense : Dense (⋃ i, (S i : Set B))) (i : ι) (a : S i) :
    starAlgEquivOfStarSubalgebra S hdense
      (of (fun i => S i) (fun _ _ h => StarSubalgebra.inclusion (S.monotone h)) i a) =
        (a : B) := by
  unfold starAlgEquivOfStarSubalgebra
  exact starAlgEquivOfDenseOfInjective_of (A := fun i => S i) _ _ _ _ i a

end SubalgebraRecognition

section Functoriality

section NonUnitalMap

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type*} {T₁ : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ i j (h : i ≤ j), T₁ h}
variable [∀ i j (h : i ≤ j), FunLike (T₁ h) (A i) (A j)] [DirectedSystem A (f · · ·)]
variable [∀ i, NonUnitalCStarAlgebra (A i)]
variable [∀ i j h, NonUnitalAlgHomClass (T₁ h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T₁ h) (A i) (A j)]
variable {B : ι → Type*} {T₂ : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {g : ∀ i j (h : i ≤ j), T₂ h}
variable [∀ i j (h : i ≤ j), FunLike (T₂ h) (B i) (B j)] [DirectedSystem B (g · · ·)]
variable [∀ i, NonUnitalCStarAlgebra (B i)]
variable [∀ i j h, NonUnitalAlgHomClass (T₂ h) ℂ (B i) (B j)]
variable [∀ i j h, StarHomClass (T₂ h) (B i) (B j)]

variable (A f B g) in
/-- **Functoriality of `CStarInductiveLimit`.** A compatible family of `⋆`-homomorphisms
`φ i : A i →⋆ₙₐ[ℂ] B i` between directed systems induces a `⋆`-homomorphism between their
C⋆-inductive limits. -/
def map (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i)
    (hφ : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), φ j (f i j hij a) = g i j hij (φ i a)) :
    CStarInductiveLimit A f →⋆ₙₐ[ℂ] CStarInductiveLimit B g :=
  lift A f (fun i => (of B g i).comp (φ i)) fun i j hij a => by
    change of B g j (φ j (f i j hij a)) = of B g i (φ i a)
    rw [hφ hij a, of_f hij]

/-- Evaluating `map` on stage `i` shifts through `φ i`. -/
@[simp]
theorem map_of (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i)
    (hφ : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), φ j (f i j hij a) = g i j hij (φ i a))
    (i : ι) (a : A i) :
    map A f B g φ hφ (of A f i a) = of B g i (φ i a) :=
  lift_of _ _ i a

/-- `map` sends the identity morphism of directed systems to the identity `⋆`-homomorphism. -/
@[simp]
theorem map_id :
    map A f A f (fun i => NonUnitalStarAlgHom.id ℂ (A i)) (fun _ _ _ _ => rfl) =
      NonUnitalStarAlgHom.id ℂ (CStarInductiveLimit A f) :=
  hom_ext fun i => NonUnitalStarAlgHom.ext fun a =>
    map_of (fun i => NonUnitalStarAlgHom.id ℂ (A i)) (fun _ _ _ _ => rfl) i a

/-- `map` preserves composition of morphisms of directed systems. -/
theorem map_comp {C : ι → Type*} {T₃ : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
    {h : ∀ i j (hij : i ≤ j), T₃ hij}
    [∀ i j (hij : i ≤ j), FunLike (T₃ hij) (C i) (C j)] [DirectedSystem C (h · · ·)]
    [∀ i, NonUnitalCStarAlgebra (C i)]
    [∀ i j hij, NonUnitalAlgHomClass (T₃ hij) ℂ (C i) (C j)]
    [∀ i j hij, StarHomClass (T₃ hij) (C i) (C j)]
    (ψ : ∀ i, B i →⋆ₙₐ[ℂ] C i)
    (hψ : ∀ ⦃i j⦄ (hij : i ≤ j) (b : B i), ψ j (g i j hij b) = h i j hij (ψ i b))
    (φ : ∀ i, A i →⋆ₙₐ[ℂ] B i)
    (hφ : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), φ j (f i j hij a) = g i j hij (φ i a)) :
    (map B g C h ψ hψ).comp (map A f B g φ hφ) =
      map A f C h (fun i => (ψ i).comp (φ i)) (fun _ _ hij a => by
        change ψ _ (φ _ (f _ _ hij a)) = h _ _ hij (ψ _ (φ _ a))
        rw [hφ hij a, hψ hij]) :=
  hom_ext fun i => by ext a; simp

variable (A f B g) in
/-- A compatible family of `⋆`-algebra isomorphisms between directed systems induces a
`⋆`-algebra isomorphism between their C⋆-inductive limits. -/
def mapEquiv (e : ∀ i, A i ≃⋆ₐ[ℂ] B i)
    (he : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), e j (f i j hij a) = g i j hij (e i a)) :
    CStarInductiveLimit A f ≃⋆ₐ[ℂ] CStarInductiveLimit B g :=
  let toHom := map A f B g (fun i => (e i).toNonUnitalStarAlgHom)
    (by intro i j hij a; simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_apply] using he hij a)
  let invHom := map B g A f (fun i => (e i).symm.toNonUnitalStarAlgHom) (by
    intro i j hij b
    simp only [StarAlgEquiv.toNonUnitalStarAlgHom_apply]
    rw [← (e j).symm_apply_apply (f i j hij ((e i).symm b)), he hij,
      StarAlgEquiv.apply_symm_apply])
  { toFun := toHom
    invFun := invHom
    left_inv x := by
      have h : invHom.comp toHom = NonUnitalStarAlgHom.id ℂ (CStarInductiveLimit A f) :=
        hom_ext fun i => NonUnitalStarAlgHom.ext fun a => by
          change invHom (toHom (of A f i a)) = of A f i a
          dsimp only [toHom, invHom]
          rw [map_of, map_of]
          exact congrArg (of A f i) ((e i).symm_apply_apply a)
      exact DFunLike.congr_fun h x
    right_inv y := by
      have h : toHom.comp invHom = NonUnitalStarAlgHom.id ℂ (CStarInductiveLimit B g) :=
        hom_ext fun i => NonUnitalStarAlgHom.ext fun b => by
          change toHom (invHom (of B g i b)) = of B g i b
          dsimp only [toHom, invHom]
          rw [map_of, map_of]
          exact congrArg (of B g i) ((e i).apply_symm_apply b)
      exact DFunLike.congr_fun h y
    map_mul' := map_mul toHom
    map_add' := map_add toHom
    map_smul' := map_smul toHom
    map_star' := map_star toHom }

/-- Evaluating `mapEquiv` on stage `i` shifts through `e i`. -/
@[simp]
theorem mapEquiv_of (e : ∀ i, A i ≃⋆ₐ[ℂ] B i)
    (he : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), e j (f i j hij a) = g i j hij (e i a))
    (i : ι) (a : A i) :
    mapEquiv A f B g e he (of A f i a) = of B g i (e i a) :=
  map_of (fun i => (e i).toNonUnitalStarAlgHom)
    (by intro i j hij a; simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_apply] using he hij a) i a

/-- Evaluating `(mapEquiv ...).symm` on stage `i` shifts through `(e i).symm`. -/
@[simp]
theorem mapEquiv_symm_of (e : ∀ i, A i ≃⋆ₐ[ℂ] B i)
    (he : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), e j (f i j hij a) = g i j hij (e i a))
    (i : ι) (b : B i) :
    (mapEquiv A f B g e he).symm (of B g i b) = of A f i ((e i).symm b) :=
  (mapEquiv A f B g e he).injective <| by
    change mapEquiv A f B g e he ((mapEquiv A f B g e he).symm (of B g i b)) =
      mapEquiv A f B g e he (of A f i ((e i).symm b))
    rw [StarAlgEquiv.apply_symm_apply, mapEquiv_of, StarAlgEquiv.apply_symm_apply]

end NonUnitalMap

section UnitalMap

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {A : ι → Type*} {T₁ : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ i j (h : i ≤ j), T₁ h}
variable [∀ i j (h : i ≤ j), FunLike (T₁ h) (A i) (A j)] [DirectedSystem A (f · · ·)]
variable [∀ i, CStarAlgebra (A i)]
variable [∀ i j h, AlgHomClass (T₁ h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T₁ h) (A i) (A j)]
variable {B : ι → Type*} {T₂ : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {g : ∀ i j (h : i ≤ j), T₂ h}
variable [∀ i j (h : i ≤ j), FunLike (T₂ h) (B i) (B j)] [DirectedSystem B (g · · ·)]
variable [∀ i, CStarAlgebra (B i)]
variable [∀ i j h, AlgHomClass (T₂ h) ℂ (B i) (B j)]
variable [∀ i j h, StarHomClass (T₂ h) (B i) (B j)]

variable (A f B g) in
/-- **Unital functoriality of `CStarInductiveLimit`.** A compatible family of unital
`⋆`-homomorphisms between unital directed systems induces a unital `⋆`-homomorphism between their
C⋆-inductive limits. -/
def mapUnital (φ : ∀ i, A i →⋆ₐ[ℂ] B i)
    (hφ : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), φ j (f i j hij a) = g i j hij (φ i a)) :
    CStarInductiveLimit A f →⋆ₐ[ℂ] CStarInductiveLimit B g :=
  liftUnital A f (fun i => (ofUnital B g i).comp (φ i)) fun i j hij a => by
    change ofUnital B g j (φ j (f i j hij a)) = ofUnital B g i (φ i a)
    rw [hφ hij a, ofUnital_f hij]

/-- Evaluating `mapUnital` on stage `i` shifts through `φ i`. -/
theorem mapUnital_ofUnital (φ : ∀ i, A i →⋆ₐ[ℂ] B i)
    (hφ : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), φ j (f i j hij a) = g i j hij (φ i a))
    (i : ι) (a : A i) :
    mapUnital A f B g φ hφ (ofUnital A f i a) = ofUnital B g i (φ i a) :=
  liftUnital_ofUnital _ _ i a

/-- As a nonunital `⋆`-homomorphism, `mapUnital` is `map`. -/
@[simp]
theorem toNonUnitalStarAlgHom_mapUnital (φ : ∀ i, A i →⋆ₐ[ℂ] B i)
    (hφ : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), φ j (f i j hij a) = g i j hij (φ i a)) :
    (mapUnital A f B g φ hφ).toNonUnitalStarAlgHom =
      map A f B g (fun i => (φ i).toNonUnitalStarAlgHom)
        (by intro i j hij a; simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom] using hφ hij a) :=
  hom_ext fun i => NonUnitalStarAlgHom.ext fun a =>
    calc (mapUnital A f B g φ hφ).toNonUnitalStarAlgHom (of A f i a)
        = mapUnital A f B g φ hφ (of A f i a) := rfl
      _ = mapUnital A f B g φ hφ (ofUnital A f i a) :=
          congrArg (mapUnital A f B g φ hφ) (ofUnital_apply i a).symm
      _ = ofUnital B g i (φ i a) := mapUnital_ofUnital φ hφ i a
      _ = of B g i (φ i a) := ofUnital_apply i (φ i a)
      _ = map A f B g (fun i => (φ i).toNonUnitalStarAlgHom)
            (by intro i j hij a; simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom] using hφ hij a)
            (of A f i a) :=
          (map_of (fun i => (φ i).toNonUnitalStarAlgHom) _ i a).symm

end UnitalMap

end Functoriality

section CofinalAndConst

section Cofinal

/-- Pullback directed-system instance along a monotone map `u : κ →o ι`. -/
instance instDirectedSystemComp {ι κ : Type*} [Preorder ι] [Preorder κ] {A : ι → Type*}
    {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ i j (h : i ≤ j), T h}
    [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)] [DirectedSystem A (f · · ·)] (u : κ →o ι) :
    DirectedSystem (fun k => A (u k)) (fun k₁ k₂ h => ⇑(f (u k₁) (u k₂) (u.monotone h))) where
  map_self _ a := DirectedSystem.map_self (f := fun i j h => ⇑(f i j h)) a
  map_map _ _ _ h₁₂ h₂₃ a :=
    DirectedSystem.map_map (f := fun i j h => ⇑(f i j h)) (u.monotone h₁₂) (u.monotone h₂₃) a

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [hFun : ∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, NonUnitalCStarAlgebra (A i)]
variable [hAlg : ∀ i j h, NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
variable [hStar : ∀ i j h, StarHomClass (T h) (A i) (A j)]
variable {κ : Type*} [Preorder κ] [IsDirectedOrder κ] [Nonempty κ]

variable (A f) in
/-- **Cofinal subsystem invariance.** Passing to a monotone cofinal subsystem `u : κ →o ι` produces
a `⋆`-isomorphic C⋆-inductive limit. -/
def cofinalEquiv (u : κ →o ι) (hcof : ∀ i : ι, ∃ k : κ, i ≤ u k) :
    @CStarInductiveLimit κ _ (fun k => A (u k)) (fun _ _ h => T (u.monotone h))
        (fun k₁ k₂ h => f (u k₁) (u k₂) (u.monotone h)) (fun _ _ h => hFun _ _ (u.monotone h))
        (instDirectedSystemComp u) _ _ _ (fun _ _ h => hAlg _ _ (u.monotone h))
        (fun _ _ h => hStar _ _ (u.monotone h)) ≃⋆ₐ[ℂ]
      CStarInductiveLimit A f := by
  refine @starAlgEquivOfDense κ _ (fun k => A (u k)) (fun _ _ h => T (u.monotone h))
    (fun k₁ k₂ h => f (u k₁) (u k₂) (u.monotone h)) (fun _ _ h => hFun _ _ (u.monotone h))
    (instDirectedSystemComp u) _ _ _ (fun _ _ h => hAlg _ _ (u.monotone h))
    (fun _ _ h => hStar _ _ (u.monotone h)) (CStarInductiveLimit A f) _
    (fun k => of A f (u k)) (fun _ _ h a => of_f (u.monotone h) a) ?_ ?_
  · refine dense_iUnion_range_of.mono ?_
    refine Set.iUnion_subset fun i => ?_
    obtain ⟨k, hik⟩ := hcof i
    rintro _ ⟨a, rfl⟩
    exact Set.mem_iUnion.2 ⟨k, f i (u k) hik a, of_f hik a⟩
  · intro k a ha
    rw [of_eq_zero_iff_tendsto] at ha
    rw [@of_eq_zero_iff_tendsto κ _ (fun k => A (u k)) (fun _ _ h => T (u.monotone h))
      (fun k₁ k₂ h => f (u k₁) (u k₂) (u.monotone h)) (fun _ _ h => hFun _ _ (u.monotone h))
      (instDirectedSystemComp u) _ _ _ (fun _ _ h => hAlg _ _ (u.monotone h))
      (fun _ _ h => hStar _ _ (u.monotone h))]
    have : IsDirectedOrder {m : κ // k ≤ m} := ⟨fun m₁ m₂ => by
      obtain ⟨m, hm₁, hm₂⟩ := directed_of (· ≤ ·) m₁.1 m₂.1
      exact ⟨⟨m, m₁.2.trans hm₁⟩, hm₁, hm₂⟩⟩
    let v : {m : κ // k ≤ m} → {j : ι // u k ≤ j} := fun m => ⟨u m.1, u.monotone m.2⟩
    have hv : Tendsto v atTop atTop := tendsto_atTop_atTop.2 fun j => by
      obtain ⟨m₀, hjm₀⟩ := hcof j.1
      obtain ⟨m, hkm, hm₀m⟩ := directed_of (· ≤ ·) k m₀
      exact ⟨⟨m, hkm⟩, fun m' hm' => hjm₀.trans (u.monotone (hm₀m.trans hm'))⟩
    exact ha.comp hv

/-- Evaluating `cofinalEquiv` on stage `k` of the subsystem yields `of A f (u k)`. -/
@[simp]
theorem cofinalEquiv_of (u : κ →o ι) (hcof : ∀ i : ι, ∃ k : κ, i ≤ u k) (k : κ) (a : A (u k)) :
    cofinalEquiv A f u hcof
      (@of κ _ (fun k => A (u k)) (fun _ _ h => T (u.monotone h))
        (fun k₁ k₂ h => f (u k₁) (u k₂) (u.monotone h)) (fun _ _ h => hFun _ _ (u.monotone h))
        (instDirectedSystemComp u) _ _ _ (fun _ _ h => hAlg _ _ (u.monotone h))
        (fun _ _ h => hStar _ _ (u.monotone h)) k a) =
        of A f (u k) a := by
  unfold cofinalEquiv
  exact @starAlgEquivOfDense_of κ _ (fun k => A (u k)) (fun _ _ h => T (u.monotone h))
    (fun k₁ k₂ h => f (u k₁) (u k₂) (u.monotone h)) (fun _ _ h => hFun _ _ (u.monotone h))
    (instDirectedSystemComp u) _ _ _ (fun _ _ h => hAlg _ _ (u.monotone h))
    (fun _ _ h => hStar _ _ (u.monotone h)) (CStarInductiveLimit A f) _ _ _ _ _ k a

end Cofinal

section Const

/-- Directed-system instance for a constant directed system with identity transition maps. -/
instance instDirectedSystemConst {ι R B : Type*} [Preorder ι] [Monoid R]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B] :
    DirectedSystem (fun _ : ι => B) (fun _ _ _ => ⇑(NonUnitalStarAlgHom.id R B)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

variable (ι : Type*) [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (B : Type*) [NonUnitalCStarAlgebra B]

/-- **Constant directed system equivalence.** The C⋆-inductive limit of a constant directed system
with identity transition maps is canonically `⋆`-isomorphic to the constant algebra `B`. -/
def constEquiv :
    CStarInductiveLimit (fun _ : ι => B) (fun _ _ _ => NonUnitalStarAlgHom.id ℂ B) ≃⋆ₐ[ℂ] B :=
  starAlgEquivOfDenseOfInjective (fun _ : ι => B) (fun _ _ _ => NonUnitalStarAlgHom.id ℂ B)
    (fun _ => NonUnitalStarAlgHom.id ℂ B) (fun _ _ _ _ => rfl)
    (by
      obtain ⟨i₀⟩ := ‹Nonempty ι›
      intro b
      exact subset_closure (Set.mem_iUnion.2 ⟨i₀, b, rfl⟩))
    (fun _ => Function.injective_id)

/-- Evaluating `constEquiv` on any stage `i` recovers the identity on `B`. -/
@[simp]
theorem constEquiv_of (i : ι) (b : B) :
    constEquiv ι B (of (fun _ : ι => B) (fun _ _ _ => NonUnitalStarAlgHom.id ℂ B) i b) = b := by
  unfold constEquiv
  exact starAlgEquivOfDenseOfInjective_of (A := fun _ : ι => B) _ _ _ _ i b

/-- Evaluating `(constEquiv ι B).symm` on `b : B` yields `of _ _ i b` for any `i : ι`. -/
theorem constEquiv_symm_apply (i : ι) (b : B) :
    (constEquiv ι B).symm b =
      of (fun _ : ι => B) (fun _ _ _ => NonUnitalStarAlgHom.id ℂ B) i b :=
  (constEquiv ι B).injective <| by
    change constEquiv ι B ((constEquiv ι B).symm b) =
      constEquiv ι B (of (fun _ : ι => B) (fun _ _ _ => NonUnitalStarAlgHom.id ℂ B) i b)
    rw [StarAlgEquiv.apply_symm_apply, constEquiv_of]

end Const

end CofinalAndConst

end TauCeti.CStarInductiveLimit
