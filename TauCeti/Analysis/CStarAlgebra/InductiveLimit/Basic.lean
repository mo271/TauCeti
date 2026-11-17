/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Analysis.CStarAlgebra.Completion
import Mathlib.Topology.Order.MonotoneConvergence
import TauCeti.Analysis.Normed.Operator.Completion

/-!
# C⋆-inductive limits of directed systems of C⋆-algebras

Given a directed system `(A, f)` of (possibly nonunital) complex C⋆-algebras indexed by a nonempty
directed preorder `ι` with `⋆`-homomorphism transition maps `f i j h : A i → A j` (not assumed
injective), the algebraic direct limit `DirectLimit A f` carries the C⋆-seminorm

`‖⟦⟨i, a⟩⟧‖ = ⨅ (j : {j : ι // i ≤ j}), ‖f i j.1 j.2 a‖ = lim_{j ≥ i} ‖f i j _ a‖`.

Because every `⋆`-homomorphism between C⋆-algebras is contractive, the net `j ↦ ‖f i j _ a‖` is
antitone and bounded below by `0`, so its infimum equals its limit along `Filter.atTop`. Passing
to the limit establishes the seminorm axioms, submultiplicativity, isometric involution, and the
C⋆-identity `‖x⋆ * x‖ = ‖x‖ * ‖x‖`. Taking the Hausdorff completion yields a complex C⋆-algebra
`TauCeti.CStarInductiveLimit A f`, unital when every `A i` is unital and the transition maps are
unital, and commutative when every `A i` is commutative.

## Main definitions

* `TauCeti.PreCStarInductiveLimit`: the algebraic direct limit `DirectLimit A f` equipped with its
  C⋆-seminorm.
* `TauCeti.CStarInductiveLimit`: the C⋆-inductive limit of a directed system `(A, f)` of complex
  C⋆-algebras and `⋆`-homomorphisms, defined as the Hausdorff completion of
  `PreCStarInductiveLimit A f`.
* `TauCeti.CStarInductiveLimit.of`: the canonical `⋆`-homomorphism from stage `i` into
  `CStarInductiveLimit A f`.
* `TauCeti.CStarInductiveLimit.ofUnital`: the canonical unital `⋆`-homomorphism from stage `i` into
  `CStarInductiveLimit A f` for a directed system of unital C⋆-algebras and unital
  `⋆`-homomorphisms.
* `TauCeti.CStarInductiveLimit.liftCLM`: extends a uniformly bounded compatible family of
  continuous linear maps `φ i : A i →L[ℂ] E` into a complex Banach space `E` to a continuous linear
  map on `CStarInductiveLimit A f`.

## Main results

* `TauCeti.CStarInductiveLimit.instNonUnitalCStarAlgebra`,
  `TauCeti.CStarInductiveLimit.instCStarAlgebra`,
  `TauCeti.CStarInductiveLimit.instNonUnitalCommCStarAlgebra`, and
  `TauCeti.CStarInductiveLimit.instCommCStarAlgebra`: C⋆-algebra instances on the inductive limit,
  together with the spectral order `instPartialOrder` and `instStarOrderedRing`.
* `TauCeti.CStarInductiveLimit.norm_of` and `TauCeti.CStarInductiveLimit.tendsto_norm_f`: the norm
  formula `‖of A f i a‖ = ⨅ j ≥ i, ‖f i j _ a‖` and its limit formulation.
* `TauCeti.CStarInductiveLimit.isometry_of` and `TauCeti.CStarInductiveLimit.of_injective`: if the
  transition maps out of stage `i` are injective, then `of A f i` is isometric and injective.
* `TauCeti.CStarInductiveLimit.dense_iUnion_range_of` and
  `TauCeti.CStarInductiveLimit.induction_on`: the union of the images `Set.range (of A f i)` is
  dense in the inductive limit.
* `TauCeti.CStarInductiveLimit.nontrivial_iff`: for a unital directed system, the inductive limit
  is nontrivial if and only if every stage is nontrivial.

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Section II.8.2.
-/

public section

noncomputable section

open Filter Topology UniformSpace
open scoped CStarAlgebra

namespace TauCeti

section PreLimit

private instance instNonemptyIci {ι : Type*} [Preorder ι] (i : ι) :
    Nonempty {j : ι // i ≤ j} :=
  ⟨⟨i, le_rfl⟩⟩

private instance instIsDirectedOrderIci {ι : Type*} [Preorder ι] [IsDirectedOrder ι] (i : ι) :
    IsDirectedOrder {j : ι // i ≤ j} where
  directed a b := by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩

section StageNorm

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable (f : ∀ i j (h : i ≤ j), T h)
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [∀ i, NonUnitalCStarAlgebra (A i)]

/-- The C⋆-seminorm of an element `a : A i` at stage `i`: the infimum (and `atTop` limit) of
`‖f i j _ a‖` over `j ≥ i`. -/
private def stageNorm (i : ι) (a : A i) : ℝ :=
  ⨅ j : {j : ι // i ≤ j}, ‖f i j.1 j.2 a‖

private theorem bddBelow_range_norm_f (i : ι) (a : A i) :
    BddBelow (Set.range fun j : {j : ι // i ≤ j} => ‖f i j.1 j.2 a‖) :=
  ⟨0, by rintro _ ⟨j, rfl⟩; exact norm_nonneg _⟩

variable [DirectedSystem A (f · · ·)]
variable [∀ i j h, NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

private theorem antitone_norm_f (i : ι) (a : A i) :
    Antitone (fun j : {j : ι // i ≤ j} => ‖f i j.1 j.2 a‖) := by
  intro j₁ j₂ h
  dsimp only
  have hmap : f j₁.1 j₂.1 h (f i j₁.1 j₁.2 a) = f i j₂.1 j₂.2 a :=
    DirectedSystem.map_map (f := fun i j hij => (f i j hij : A i → A j)) j₁.2 h a
  rw [← hmap]
  exact NonUnitalStarAlgHom.norm_apply_le (f j₁.1 j₂.1 h) _

private theorem tendsto_norm_f_stageNorm (i : ι) (a : A i) :
    Tendsto (fun j : {j : ι // i ≤ j} => ‖f i j.1 j.2 a‖) atTop (𝓝 (stageNorm f i a)) :=
  tendsto_atTop_ciInf (antitone_norm_f f i a) (bddBelow_range_norm_f f i a)

variable [IsDirectedOrder ι]

private theorem stageNorm_map {i k : ι} (hik : i ≤ k) (a : A i) :
    stageNorm f k (f i k hik a) = stageNorm f i a := by
  let u : {m : ι // k ≤ m} → {m : ι // i ≤ m} := fun m => ⟨m.1, hik.trans m.2⟩
  have hu : Tendsto u atTop atTop := tendsto_atTop_atTop.2 fun j => by
    obtain ⟨m, hjm, hkm⟩ := directed_of (· ≤ ·) j.1 k
    exact ⟨⟨m, hkm⟩, fun m' hm' => hjm.trans hm'⟩
  have hcomp :
      (fun m : {m : ι // i ≤ m} => ‖f i m.1 m.2 a‖) ∘ u =
        fun m : {m : ι // k ≤ m} => ‖f k m.1 m.2 (f i k hik a)‖ := by
    funext m
    exact congrArg norm
      (DirectedSystem.map_map (f := fun a b h => (f a b h : A a → A b)) hik m.2 a).symm
  have h₁ : Tendsto (fun m : {m : ι // k ≤ m} => ‖f k m.1 m.2 (f i k hik a)‖)
      atTop (𝓝 (stageNorm f i a)) :=
    hcomp ▸ (tendsto_norm_f_stageNorm f i a).comp hu
  exact tendsto_nhds_unique (tendsto_norm_f_stageNorm f k (f i k hik a)) h₁

end StageNorm

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable (f : ∀ i j (h : i ≤ j), T h)
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι]
variable [∀ i, NonUnitalCStarAlgebra (A i)]
variable [∀ i j h, NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

/-- The C⋆-seminorm descended to the algebraic direct limit `DirectLimit A f`. -/
private def preNorm : DirectLimit A f → ℝ :=
  Quotient.lift (fun p : Σ i, A i => stageNorm f p.1 p.2) fun p q hpq => by
    obtain ⟨k, hpk, hqk, heq⟩ := hpq
    rw [← stageNorm_map f hpk p.2, ← stageNorm_map f hqk q.2, heq]

private theorem preNorm_mk (i : ι) (a : A i) : preNorm f ⟦⟨i, a⟩⟧ = stageNorm f i a :=
  rfl

private theorem preNorm_add_le (x y : DirectLimit A f) :
    preNorm f (x + y) ≤ preNorm f x + preNorm f y := by
  induction x, y using DirectLimit.induction₂ with | _ i a b =>
    rw [DirectLimit.add_def, preNorm_mk, preNorm_mk, preNorm_mk]
    exact le_of_tendsto_of_tendsto (tendsto_norm_f_stageNorm f i (a + b))
      ((tendsto_norm_f_stageNorm f i a).add (tendsto_norm_f_stageNorm f i b))
      (Eventually.of_forall fun j => by dsimp only; rw [map_add]; exact norm_add_le _ _)

private theorem preNorm_mul_le (x y : DirectLimit A f) :
    preNorm f (x * y) ≤ preNorm f x * preNorm f y := by
  induction x, y using DirectLimit.induction₂ with | _ i a b =>
    rw [DirectLimit.mul_def, preNorm_mk, preNorm_mk, preNorm_mk]
    exact le_of_tendsto_of_tendsto (tendsto_norm_f_stageNorm f i (a * b))
      ((tendsto_norm_f_stageNorm f i a).mul (tendsto_norm_f_stageNorm f i b))
      (Eventually.of_forall fun j => by dsimp only; rw [map_mul]; exact norm_mul_le _ _)

private theorem preNorm_star (x : DirectLimit A f) : preNorm f (star x) = preNorm f x := by
  induction x using DirectLimit.induction with | _ i a =>
    rw [DirectLimit.star_def, preNorm_mk, preNorm_mk]
    simp only [stageNorm, map_star, norm_star]

private theorem preNorm_star_mul_self (x : DirectLimit A f) :
    preNorm f (star x * x) = preNorm f x * preNorm f x := by
  induction x using DirectLimit.induction with | _ i a =>
    rw [DirectLimit.star_def, DirectLimit.mul_def, preNorm_mk, preNorm_mk]
    exact tendsto_nhds_unique (tendsto_norm_f_stageNorm f i (star a * a)) <| by
      simpa only [map_mul, map_star, CStarRing.norm_star_mul_self] using
        (tendsto_norm_f_stageNorm f i a).mul (tendsto_norm_f_stageNorm f i a)

variable [Nonempty ι]

private theorem preNorm_zero : preNorm f 0 = 0 := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  rw [DirectLimit.zero_def i, preNorm_mk]
  exact tendsto_nhds_unique (tendsto_norm_f_stageNorm f i 0)
    (by simp only [map_zero, norm_zero]; exact tendsto_const_nhds)

private theorem preNorm_neg (x : DirectLimit A f) : preNorm f (-x) = preNorm f x := by
  induction x using DirectLimit.induction with | _ i a =>
    rw [DirectLimit.neg_def, preNorm_mk, preNorm_mk]
    simp only [stageNorm, map_neg, norm_neg]

private theorem preNorm_smul (c : ℂ) (x : DirectLimit A f) :
    preNorm f (c • x) = ‖c‖ * preNorm f x := by
  induction x using DirectLimit.induction with | _ i a =>
    rw [DirectLimit.smul_def, preNorm_mk, preNorm_mk]
    exact tendsto_nhds_unique (tendsto_norm_f_stageNorm f i (c • a)) <| by
      simpa only [map_smul, norm_smul] using
        (tendsto_norm_f_stageNorm f i a).const_mul ‖c‖

variable (A) in
/-- The algebraic direct limit `DirectLimit A f` equipped with its C⋆-seminorm
`‖⟦⟨i, a⟩⟧‖ = ⨅ j ≥ i, ‖f i j _ a‖`. It is a separate type synonym so that the seminormed
instances do not leak onto Mathlib's algebraic `DirectLimit`. -/
@[expose] def PreCStarInductiveLimit : Type _ :=
  DirectLimit A f

namespace PreCStarInductiveLimit

private def toPre : DirectLimit A f → PreCStarInductiveLimit A f := id

instance instNonUnitalRing : NonUnitalRing (PreCStarInductiveLimit A f) :=
  inferInstanceAs (NonUnitalRing (DirectLimit A f))

instance instStarRing : StarRing (PreCStarInductiveLimit A f) :=
  inferInstanceAs (StarRing (DirectLimit A f))

instance instModule : Module ℂ (PreCStarInductiveLimit A f) :=
  inferInstanceAs (Module ℂ (DirectLimit A f))

instance instStarModule : StarModule ℂ (PreCStarInductiveLimit A f) :=
  inferInstanceAs (StarModule ℂ (DirectLimit A f))

instance instIsScalarTower :
    IsScalarTower ℂ (PreCStarInductiveLimit A f) (PreCStarInductiveLimit A f) :=
  inferInstanceAs (IsScalarTower ℂ (DirectLimit A f) (DirectLimit A f))

instance instSMulCommClass :
    SMulCommClass ℂ (PreCStarInductiveLimit A f) (PreCStarInductiveLimit A f) :=
  inferInstanceAs (SMulCommClass ℂ (DirectLimit A f) (DirectLimit A f))

/-- The C⋆-seminorm on `PreCStarInductiveLimit A f` as an `AddGroupSeminorm`. -/
def seminorm : AddGroupSeminorm (PreCStarInductiveLimit A f) where
  toFun := preNorm f
  map_zero' := preNorm_zero f
  add_le' := preNorm_add_le f
  neg' := preNorm_neg f

instance instSeminormedAddCommGroup : SeminormedAddCommGroup (PreCStarInductiveLimit A f) :=
  @AddGroupSeminorm.toSeminormedAddCommGroup (PreCStarInductiveLimit A f) _ (seminorm f)

instance instNormedSpace : NormedSpace ℂ (PreCStarInductiveLimit A f) where
  __ : Module ℂ (PreCStarInductiveLimit A f) := inferInstance
  norm_smul_le c x := by exact (preNorm_smul f c x).le

instance instNonUnitalSeminormedRing : NonUnitalSeminormedRing (PreCStarInductiveLimit A f) where
  __ : SeminormedAddCommGroup (PreCStarInductiveLimit A f) := inferInstance
  __ : NonUnitalRing (PreCStarInductiveLimit A f) := inferInstance
  norm_mul_le x y := by exact preNorm_mul_le f x y

instance instNormedStarGroup : NormedStarGroup (PreCStarInductiveLimit A f) where
  norm_star_le x := (preNorm_star f x).le

/-- The seminorm on `PreCStarInductiveLimit A f` satisfies the C⋆-identity. -/
theorem norm_star_mul_self (x : PreCStarInductiveLimit A f) : ‖star x * x‖ = ‖x‖ * ‖x‖ :=
  preNorm_star_mul_self f x

end PreCStarInductiveLimit

end PreLimit

section Def

variable {ι : Type*} [Preorder ι] (A : ι → Type*) {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable (f : ∀ i j (h : i ≤ j), T h)
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, NonUnitalCStarAlgebra (A i)]
variable [∀ i j h, NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

/-- The **C⋆-inductive limit** of a directed system `(A, f)` of (possibly nonunital) complex
C⋆-algebras and `⋆`-homomorphisms: the Hausdorff completion of the algebraic direct limit with
respect to the C⋆-seminorm `‖⟦⟨i, a⟩⟧‖ = ⨅ j ≥ i, ‖f i j _ a‖`. -/
@[expose] def CStarInductiveLimit : Type _ :=
  Completion (PreCStarInductiveLimit A f)

end Def

namespace CStarInductiveLimit

section NonUnital

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, NonUnitalCStarAlgebra (A i)]
variable [∀ i j h, NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

/-- The completion of `PreCStarInductiveLimit A f` is a nonunital C⋆-algebra. -/
instance instNonUnitalCStarAlgebraCompletion :
    NonUnitalCStarAlgebra (Completion (PreCStarInductiveLimit A f)) where
  toCStarRing := Completion.cstarRing fun x => (PreCStarInductiveLimit.norm_star_mul_self f x).ge

/-- The C⋆-inductive limit of a directed system of nonunital C⋆-algebras is a nonunital
C⋆-algebra. -/
instance instNonUnitalCStarAlgebra : NonUnitalCStarAlgebra (CStarInductiveLimit A f) :=
  inferInstanceAs (NonUnitalCStarAlgebra (Completion (PreCStarInductiveLimit A f)))

/-- The positive cone of `CStarInductiveLimit A f` is the C⋆-algebra spectral order. -/
instance instPartialOrder : PartialOrder (CStarInductiveLimit A f) :=
  CStarAlgebra.spectralOrder (CStarInductiveLimit A f)

/-- The spectral order on `CStarInductiveLimit A f` makes it a `StarOrderedRing`. -/
instance instStarOrderedRing : StarOrderedRing (CStarInductiveLimit A f) :=
  CStarAlgebra.spectralOrderedRing (CStarInductiveLimit A f)

variable (A f) in
/-- The canonical `⋆`-algebra homomorphism from stage `i` into the C⋆-inductive limit. -/
def of (i : ι) : A i →⋆ₙₐ[ℂ] CStarInductiveLimit A f where
  toFun a := (PreCStarInductiveLimit.toPre f ⟦⟨i, a⟩⟧ : Completion (PreCStarInductiveLimit A f))
  map_smul' c a := by
    change (PreCStarInductiveLimit.toPre f ⟦⟨i, c • a⟩⟧ :
      Completion (PreCStarInductiveLimit A f)) =
        c • (PreCStarInductiveLimit.toPre f ⟦⟨i, a⟩⟧ : Completion (PreCStarInductiveLimit A f))
    rw [← Completion.coe_smul]
    exact congrArg ((↑) : PreCStarInductiveLimit A f → Completion (PreCStarInductiveLimit A f))
      (DirectLimit.smul_def (f := f) i a c).symm
  map_zero' := by
    change (PreCStarInductiveLimit.toPre f ⟦⟨i, (0 : A i)⟩⟧ :
      Completion (PreCStarInductiveLimit A f)) = 0
    rw [← DirectLimit.zero_def (f := f) i]
    exact Completion.coe_zero
  map_add' a b := by
    change (PreCStarInductiveLimit.toPre f ⟦⟨i, a + b⟩⟧ :
      Completion (PreCStarInductiveLimit A f)) =
        (PreCStarInductiveLimit.toPre f ⟦⟨i, a⟩⟧ : Completion (PreCStarInductiveLimit A f)) +
        (PreCStarInductiveLimit.toPre f ⟦⟨i, b⟩⟧ : Completion (PreCStarInductiveLimit A f))
    rw [← Completion.coe_add]
    exact congrArg ((↑) : PreCStarInductiveLimit A f → Completion (PreCStarInductiveLimit A f))
      (DirectLimit.add_def (f := f) i a b).symm
  map_mul' a b := by
    change (PreCStarInductiveLimit.toPre f ⟦⟨i, a * b⟩⟧ :
      Completion (PreCStarInductiveLimit A f)) =
        (PreCStarInductiveLimit.toPre f ⟦⟨i, a⟩⟧ : Completion (PreCStarInductiveLimit A f)) *
        (PreCStarInductiveLimit.toPre f ⟦⟨i, b⟩⟧ : Completion (PreCStarInductiveLimit A f))
    rw [← Completion.coe_mul']
    exact congrArg ((↑) : PreCStarInductiveLimit A f → Completion (PreCStarInductiveLimit A f))
      (DirectLimit.mul_def (f := f) i a b).symm
  map_star' a := by
    change (PreCStarInductiveLimit.toPre f ⟦⟨i, star a⟩⟧ :
      Completion (PreCStarInductiveLimit A f)) =
        star (PreCStarInductiveLimit.toPre f ⟦⟨i, a⟩⟧ : Completion (PreCStarInductiveLimit A f))
    rw [← Completion.coe_star]
    exact congrArg ((↑) : PreCStarInductiveLimit A f → Completion (PreCStarInductiveLimit A f))
      (DirectLimit.star_def (f := f) i a).symm

/-- The canonical maps into the C⋆-inductive limit are compatible with the transition maps. -/
@[simp]
theorem of_f {i j : ι} (hij : i ≤ j) (a : A i) : of A f j (f i j hij a) = of A f i a :=
  congrArg ((↑) : PreCStarInductiveLimit A f → Completion (PreCStarInductiveLimit A f))
    (DirectLimit.eq_of_le (f := f) ⟨i, a⟩ j hij).symm

/-- Composition form of `of_f` for bundled `NonUnitalStarAlgHom` transitions. -/
@[simp]
theorem of_comp_f {i j : ι} (hij : i ≤ j) :
    (of A f j).comp (NonUnitalStarAlgHom.ofClass (f i j hij)) = of A f i :=
  NonUnitalStarAlgHom.ext fun a => of_f hij a

/-- **Norm formula for the C⋆-inductive limit.** The norm of `of A f i a` is the infimum of
`‖f i j _ a‖` over all `j ≥ i`. -/
theorem norm_of (i : ι) (a : A i) :
    ‖of A f i a‖ = ⨅ j : {j : ι // i ≤ j}, ‖f i j.1 j.2 a‖ :=
  Completion.norm_coe (PreCStarInductiveLimit.toPre f ⟦⟨i, a⟩⟧)

/-- Along the directed tail `{j // i ≤ j}`, the norms `‖f i j _ a‖` decrease to `‖of A f i a‖`. -/
theorem tendsto_norm_f (i : ι) (a : A i) :
    Tendsto (fun j : {j : ι // i ≤ j} => ‖f i j.1 j.2 a‖) atTop (𝓝 ‖of A f i a‖) := by
  rw [norm_of]
  exact tendsto_norm_f_stageNorm f i a

/-- The norm of `of A f i a` is at most the norm of any forward transition `f i j hij a`. -/
theorem norm_of_le_norm_f {i j : ι} (hij : i ≤ j) (a : A i) :
    ‖of A f i a‖ ≤ ‖f i j hij a‖ := by
  rw [norm_of]
  exact ciInf_le (bddBelow_range_norm_f f i a) ⟨j, hij⟩

/-- An element `a : A i` vanishes in the C⋆-inductive limit if and only if the infimum of its
forward transition norms is `0`. -/
theorem of_eq_zero_iff (i : ι) (a : A i) :
    of A f i a = 0 ↔ ⨅ j : {j : ι // i ≤ j}, ‖f i j.1 j.2 a‖ = 0 := by
  rw [← norm_eq_zero, norm_of]

/-- An element `a : A i` vanishes in the C⋆-inductive limit if and only if `‖f i j _ a‖ → 0`
as `j → ∞` in `{j // i ≤ j}`. -/
theorem of_eq_zero_iff_tendsto (i : ι) (a : A i) :
    of A f i a = 0 ↔ Tendsto (fun j : {j : ι // i ≤ j} => ‖f i j.1 j.2 a‖) atTop (𝓝 0) := by
  constructor
  · intro h
    simpa only [h, norm_zero] using tendsto_norm_f (f := f) i a
  · intro h
    rw [← norm_eq_zero]
    exact tendsto_nhds_unique (tendsto_norm_f (f := f) i a) h

/-- If every transition map out of stage `i` is injective, then `of A f i` preserves norms. -/
theorem norm_of_eq_of_injective (i : ι) (hinj : ∀ j (hij : i ≤ j), Function.Injective (f i j hij))
    (a : A i) : ‖of A f i a‖ = ‖a‖ := by
  rw [norm_of]
  have hconst : (fun j : {j : ι // i ≤ j} => ‖f i j.1 j.2 a‖) = fun _ => ‖a‖ := by
    funext j
    exact NonUnitalStarAlgHom.norm_map (f i j.1 j.2) (hinj j.1 j.2) a
  rw [hconst, ciInf_const]

/-- If every transition map out of stage `i` is injective, then `of A f i` is an isometry. -/
theorem isometry_of (i : ι) (hinj : ∀ j (hij : i ≤ j), Function.Injective (f i j hij)) :
    Isometry (of A f i) :=
  AddMonoidHomClass.isometry_of_norm (of A f i) (norm_of_eq_of_injective i hinj)

/-- If every transition map out of stage `i` is injective, then `of A f i` is injective. -/
theorem of_injective (i : ι) (hinj : ∀ j (hij : i ≤ j), Function.Injective (f i j hij)) :
    Function.Injective (of A f i) :=
  (isometry_of i hinj).injective

/-- **Closed induction on the C⋆-inductive limit.** A closed property that holds on the image of
every stage `A i` holds everywhere on `CStarInductiveLimit A f`. -/
@[elab_as_elim]
theorem induction_on {p : CStarInductiveLimit A f → Prop} (x : CStarInductiveLimit A f)
    (hp : IsClosed {x | p x}) (ih : ∀ i (a : A i), p (of A f i a)) : p x := by
  refine Completion.induction_on (p := p) x hp fun y => ?_
  induction y using DirectLimit.induction with | _ i a =>
    exact ih i a

/-- **Binary closed induction on the C⋆-inductive limit.** A closed binary property that holds on
all pairs coming from a common stage `A i` holds for all pairs in `CStarInductiveLimit A f`. -/
@[elab_as_elim]
theorem induction_on₂ {p : CStarInductiveLimit A f → CStarInductiveLimit A f → Prop}
    (x y : CStarInductiveLimit A f) (hp : IsClosed {q : _ × _ | p q.1 q.2})
    (ih : ∀ i (a b : A i), p (of A f i a) (of A f i b)) : p x y := by
  refine Completion.induction_on₂ (p := p) x y hp fun u v => ?_
  induction u, v using DirectLimit.induction₂ with | _ i a b =>
    exact ih i a b

/-- The union of the canonical images of the stages is dense in `CStarInductiveLimit A f`. -/
theorem dense_iUnion_range_of : Dense (⋃ i, Set.range (of A f i)) := by
  intro x
  induction x using induction_on with
  | hp => exact isClosed_closure
  | ih i a => exact subset_closure (Set.mem_iUnion.2 ⟨i, a, rfl⟩)

/-- The closure of the union of the canonical images of the stages is the whole inductive limit. -/
@[simp]
theorem closure_iUnion_range_of : closure (⋃ i, Set.range (of A f i)) = Set.univ :=
  dense_iUnion_range_of.closure_eq

/-- Two `⋆`-homomorphisms out of `CStarInductiveLimit A f` that agree on every stage are equal. -/
@[ext]
theorem hom_ext {B : Type*} [NonUnitalCStarAlgebra B]
    {φ ψ : CStarInductiveLimit A f →⋆ₙₐ[ℂ] B}
    (h : ∀ i, φ.comp (of A f i) = ψ.comp (of A f i)) : φ = ψ :=
  NonUnitalStarAlgHom.ext fun x => induction_on x
    (isClosed_eq (map_continuous φ) (map_continuous ψ)) fun i a =>
      DFunLike.congr_fun (h i) a

/-- Two continuous linear maps out of `CStarInductiveLimit A f` into a Hausdorff space that agree on
every stage are equal. -/
@[ext]
theorem continuousLinearMap_ext {E : Type*} [TopologicalSpace E] [T2Space E]
    [AddCommMonoid E] [Module ℂ E] {S₁ S₂ : CStarInductiveLimit A f →L[ℂ] E}
    (h : ∀ i (a : A i), S₁ (of A f i a) = S₂ (of A f i a)) : S₁ = S₂ :=
  ContinuousLinearMap.ext fun x => induction_on x (isClosed_eq S₁.continuous S₂.continuous) h

section LiftCLM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private def preLiftLinear (φ : ∀ i, A i →L[ℂ] E)
    (hφ : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), φ j (f i j hij a) = φ i a) :
    PreCStarInductiveLimit A f →ₗ[ℂ] E :=
  DirectLimit.Module.lift ℂ ι A f (fun i => (φ i : A i →ₗ[ℂ] E)) (fun _ _ hij a => hφ hij a)

private theorem preLiftLinear_bound (φ : ∀ i, A i →L[ℂ] E)
    (hφ : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), φ j (f i j hij a) = φ i a)
    {C : ℝ} (hC : ∀ i, ‖φ i‖ ≤ C) (x : PreCStarInductiveLimit A f) :
    ‖preLiftLinear (f := f) φ hφ x‖ ≤ C * ‖x‖ := by
  induction x using DirectLimit.induction with | _ i a =>
    have hbound : ∀ j : {j : ι // i ≤ j},
        ‖preLiftLinear (f := f) φ hφ ⟦⟨i, a⟩⟧‖ ≤ C * ‖f i j.1 j.2 a‖ := fun j => by
      change ‖φ i a‖ ≤ C * ‖f i j.1 j.2 a‖
      rw [← hφ j.2 a]
      exact ((φ j.1).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC j.1) (norm_nonneg _))
    exact ge_of_tendsto ((tendsto_norm_f_stageNorm f i a).const_mul C)
      (Eventually.of_forall hbound)

/-- Helper constructing the continuous linear map on the pre-completion direct limit. -/
private def preLiftCLM (φ : ∀ i, A i →L[ℂ] E)
    (hφ : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), φ j (f i j hij a) = φ i a)
    {C : ℝ} (hC : ∀ i, ‖φ i‖ ≤ C) : PreCStarInductiveLimit A f →L[ℂ] E :=
  (preLiftLinear (f := f) φ hφ).mkContinuous C (preLiftLinear_bound (f := f) φ hφ hC)

variable [CompleteSpace E]

variable (A f) in
/-- **Bounded linear universal property of `CStarInductiveLimit`.** A compatible family of
continuous complex-linear maps `φ i : A i →L[ℂ] E` into a Banach space `E` with uniformly bounded
operator norms extends uniquely to a continuous linear map on `CStarInductiveLimit A f`. -/
def liftCLM (φ : ∀ i, A i →L[ℂ] E)
    (hφ : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), φ j (f i j hij a) = φ i a)
    {C : ℝ} (hC : ∀ i, ‖φ i‖ ≤ C) : CStarInductiveLimit A f →L[ℂ] E :=
  (preLiftCLM (f := f) φ hφ hC).fromCompletion

/-- Evaluating `liftCLM` on the canonical image of stage `i` recovers `φ i`. -/
@[simp]
theorem liftCLM_of (φ : ∀ i, A i →L[ℂ] E)
    (hφ : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), φ j (f i j hij a) = φ i a)
    {C : ℝ} (hC : ∀ i, ‖φ i‖ ≤ C) (i : ι) (a : A i) :
    liftCLM A f φ hφ hC (of A f i a) = φ i a :=
  ContinuousLinearMap.fromCompletion_apply_coe (preLiftCLM (f := f) φ hφ hC)
    (PreCStarInductiveLimit.toPre f ⟦⟨i, a⟩⟧)

/-- The operator norm of `liftCLM` is at most the uniform bound `C`. -/
theorem opNorm_liftCLM_le (φ : ∀ i, A i →L[ℂ] E)
    (hφ : ∀ ⦃i j⦄ (hij : i ≤ j) (a : A i), φ j (f i j hij a) = φ i a)
    {C : ℝ} (hC : ∀ i, ‖φ i‖ ≤ C) :
    ‖liftCLM A f φ hφ hC‖ ≤ C := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hC0 : 0 ≤ C := (norm_nonneg (φ i₀)).trans (hC i₀)
  change ‖(preLiftCLM (f := f) φ hφ hC).fromCompletion‖ ≤ C
  rw [ContinuousLinearMap.norm_fromCompletion]
  exact LinearMap.mkContinuous_norm_le _ hC0 (preLiftLinear_bound (f := f) φ hφ hC)

end LiftCLM

end NonUnital

section NonUnitalComm

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, NonUnitalCommCStarAlgebra (A i)]
variable [∀ i j h, NonUnitalAlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

/-- The C⋆-inductive limit of a directed system of commutative nonunital C⋆-algebras is
commutative. -/
instance instNonUnitalCommCStarAlgebra : NonUnitalCommCStarAlgebra (CStarInductiveLimit A f) where
  __ := (inferInstance : NonUnitalCStarAlgebra (CStarInductiveLimit A f))
  mul_comm x y := by
    induction x, y using induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih i a b => rw [← map_mul, ← map_mul, mul_comm]

end NonUnitalComm

section Unital

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, CStarAlgebra (A i)]
variable [∀ i j h, AlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

private theorem of_one_eq_of_one (i j : ι) : of A f i 1 = of A f j 1 := by
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  rw [← of_f hik, ← of_f hjk, map_one (f i k hik), map_one (f j k hjk)]

/-- The unit element of a unital C⋆-inductive limit, built directly on top of the nonunital
structure so that the unital and nonunital `CStarAlgebra` instances are definitionally compatible.
-/
instance instOne : One (CStarInductiveLimit A f) where
  one := of A f (Classical.arbitrary ι) 1

/-- Every canonical stage map sends `1` to `1`. -/
@[simp]
theorem of_one (i : ι) : of A f i 1 = (1 : CStarInductiveLimit A f) :=
  of_one_eq_of_one i (Classical.arbitrary ι)

/-- The unital ring structure on `CStarInductiveLimit A f`, extending its nonunital ring
structure without creating a typeclass diamond. -/
instance instRing : Ring (CStarInductiveLimit A f) where
  __ := (instNonUnitalCStarAlgebra (A := A) (f := f)).toNonUnitalRing
  __ := instOne (A := A) (f := f)
  one_mul x := by
    induction x using induction_on with
    | hp => exact isClosed_eq (continuous_const_mul _) continuous_id
    | ih i a => rw [← of_one i, ← map_mul, one_mul]
  mul_one x := by
    induction x using induction_on with
    | hp => exact isClosed_eq (continuous_mul_const _) continuous_id
    | ih i a => rw [← of_one i, ← map_mul, mul_one]

/-- The unital normed ring structure on `CStarInductiveLimit A f`. -/
instance instNormedRing : NormedRing (CStarInductiveLimit A f) where
  __ := (instNonUnitalCStarAlgebra (A := A) (f := f)).toNonUnitalNormedRing
  __ := instRing (A := A) (f := f)

/-- The unital `ℂ`-algebra structure on `CStarInductiveLimit A f`, with `algebraMap c = c • 1`. -/
instance instAlgebra : Algebra ℂ (CStarInductiveLimit A f) where
  algebraMap :=
    { toFun := fun c => c • (1 : CStarInductiveLimit A f)
      map_one' := one_smul ℂ 1
      map_mul' := fun c d => by rw [smul_mul_smul_comm, mul_one]
      map_zero' := zero_smul ℂ 1
      map_add' := fun c d => add_smul c d 1 }
  commutes' c x := by
    change (c • (1 : CStarInductiveLimit A f)) * x = x * (c • 1)
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  smul_def' c x := by
    change c • x = (c • (1 : CStarInductiveLimit A f)) * x
    rw [smul_mul_assoc, one_mul]

/-- The unital normed `ℂ`-algebra structure on `CStarInductiveLimit A f`. -/
instance instNormedAlgebra : NormedAlgebra ℂ (CStarInductiveLimit A f) where
  norm_smul_le := (instNonUnitalCStarAlgebra (A := A) (f := f)).norm_smul_le

/-- The C⋆-inductive limit of a directed system of unital C⋆-algebras and unital `⋆`-homomorphisms
is a unital C⋆-algebra. -/
instance instCStarAlgebra : CStarAlgebra (CStarInductiveLimit A f) where
  __ := instNormedRing (A := A) (f := f)
  __ := instNormedAlgebra (A := A) (f := f)
  __ := (instNonUnitalCStarAlgebra (A := A) (f := f)).toStarRing
  __ := (instNonUnitalCStarAlgebra (A := A) (f := f)).toCompleteSpace
  __ := (instNonUnitalCStarAlgebra (A := A) (f := f)).toCStarRing
  __ := (instNonUnitalCStarAlgebra (A := A) (f := f)).toStarModule

-- Verify that `instCStarAlgebra.toNonUnitalCStarAlgebra` agrees definitionally with
-- `instNonUnitalCStarAlgebra` so no diamonds arise between unital and nonunital APIs.
example :
    (instCStarAlgebra (A := A) (f := f)).toNonUnitalCStarAlgebra =
      instNonUnitalCStarAlgebra (A := A) (f := f) := by
  with_reducible_and_instances rfl

variable (A f) in
/-- The canonical unital `⋆`-algebra homomorphism from stage `i` into a unital C⋆-inductive limit.
-/
def ofUnital (i : ι) : A i →⋆ₐ[ℂ] CStarInductiveLimit A f where
  __ := of A f i
  map_one' := of_one i
  commutes' c := by
    change of A f i (algebraMap ℂ (A i) c) = c • (1 : CStarInductiveLimit A f)
    rw [Algebra.algebraMap_eq_smul_one, map_smul, of_one]

/-- As a nonunital `⋆`-homomorphism, `ofUnital A f i` is `of A f i`. -/
@[simp]
theorem toNonUnitalStarAlgHom_ofUnital (i : ι) :
    (ofUnital A f i).toNonUnitalStarAlgHom = of A f i :=
  (rfl)

/-- `ofUnital A f i` has the same underlying function as `of A f i`. -/
@[simp]
theorem ofUnital_apply (i : ι) (a : A i) : ofUnital A f i a = of A f i a :=
  (rfl)

/-- The canonical unital maps are compatible with the transition maps. -/
theorem ofUnital_f {i j : ι} (hij : i ≤ j) (a : A i) :
    ofUnital A f j (f i j hij a) = ofUnital A f i a :=
  of_f hij a

/-- Composition form of `ofUnital_f` for bundled `StarAlgHom` transitions. -/
@[simp]
theorem ofUnital_comp_f {i j : ι} (hij : i ≤ j) :
    (ofUnital A f j).comp (StarAlgHom.ofClass (f i j hij)) = ofUnital A f i :=
  StarAlgHom.ext fun a => ofUnital_f hij a

/-- Two unital `⋆`-homomorphisms out of `CStarInductiveLimit A f` that agree on every stage are
equal. -/
@[ext]
theorem unitalHom_ext {B : Type*} [CStarAlgebra B]
    {φ ψ : CStarInductiveLimit A f →⋆ₐ[ℂ] B}
    (h : ∀ i, φ.comp (ofUnital A f i) = ψ.comp (ofUnital A f i)) : φ = ψ :=
  StarAlgHom.ext fun x => induction_on x
    (isClosed_eq (map_continuous φ) (map_continuous ψ)) fun i a =>
      DFunLike.congr_fun (h i) a

/-- If some stage of a unital directed system is trivial, then the C⋆-inductive limit is trivial. -/
theorem subsingleton_of_subsingleton (i : ι) [Subsingleton (A i)] :
    Subsingleton (CStarInductiveLimit A f) := by
  refine subsingleton_of_zero_eq_one ?_
  rw [← of_one i, Subsingleton.elim (1 : A i) 0, map_zero]

/-- If every stage of a unital directed system is nontrivial, then the C⋆-inductive limit is
nontrivial. -/
instance instNontrivial [∀ i, Nontrivial (A i)] : Nontrivial (CStarInductiveLimit A f) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine nontrivial_iff_exists_ne (0 : CStarInductiveLimit A f) |>.2 ⟨1, ?_⟩
  intro h
  have h1 : ‖(1 : CStarInductiveLimit A f)‖ = 1 := by
    rw [← of_one i, norm_of]
    have hconst : (fun j : {j : ι // i ≤ j} => ‖f i j.1 j.2 1‖) = fun _ => 1 := by
      funext j
      rw [map_one, norm_one]
    rw [hconst, ciInf_const]
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- **Nontriviality criterion for unital C⋆-inductive limits.** A unital C⋆-inductive limit is
nontrivial if and only if every stage is nontrivial. -/
theorem nontrivial_iff : Nontrivial (CStarInductiveLimit A f) ↔ ∀ i, Nontrivial (A i) := by
  refine ⟨fun h i => ?_, fun _ => inferInstance⟩
  by_contra hnot
  rw [not_nontrivial_iff_subsingleton] at hnot
  have := subsingleton_of_subsingleton (A := A) (f := f) i
  exact false_of_nontrivial_of_subsingleton (CStarInductiveLimit A f)

end Unital

section Comm

variable {ι : Type*} [Preorder ι] {A : ι → Type*} {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*}
variable {f : ∀ i j (h : i ≤ j), T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (A i) (A j)]
variable [DirectedSystem A (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
variable [∀ i, CommCStarAlgebra (A i)]
variable [∀ i j h, AlgHomClass (T h) ℂ (A i) (A j)]
variable [∀ i j h, StarHomClass (T h) (A i) (A j)]

/-- The C⋆-inductive limit of a directed system of commutative unital C⋆-algebras and unital
`⋆`-homomorphisms is a commutative unital C⋆-algebra. -/
instance instCommCStarAlgebra : CommCStarAlgebra (CStarInductiveLimit A f) where
  __ := instCStarAlgebra (A := A) (f := f)
  mul_comm := (instNonUnitalCommCStarAlgebra (A := A) (f := f)).mul_comm

example :
    (instCommCStarAlgebra (A := A) (f := f)).toCStarAlgebra =
      instCStarAlgebra (A := A) (f := f) := by
  with_reducible_and_instances rfl

example :
    (instCommCStarAlgebra (A := A) (f := f)).toNonUnitalCommCStarAlgebra =
      instNonUnitalCommCStarAlgebra (A := A) (f := f) := by
  with_reducible_and_instances rfl

end Comm

end CStarInductiveLimit

end TauCeti
