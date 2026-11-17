/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Analysis.Complex.Order
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
import TauCeti.Basic.Complex.BigOperators

/-!
# Star structure and Parseval positivity on twisted group algebras

For a group `G` and unitary normalized factor set `α : G → G → kˣ`, `twistedMonoidAlgebra k G α`
carries a conjugate-linear star structure with `star (of g) = (α g g⁻¹)⁻¹ • of g⁻¹`
(`instStarRing`, `instStarModule`), functorial via `mapStarAlgHom`, and `scalarTrace` satisfies
Parseval positivity (`scalarTrace_star_mul`, `scalarTrace_star_mul_self`,
`scalarTracePositiveFunctional`, `nullSubmodule_scalarTracePositiveFunctional`).
-/

public section

open scoped ComplexOrder
open MulOpposite Module

namespace TauCeti.TwistedMonoidAlgebra

private noncomputable def unitOf {k G : Type*} [CommSemiring k] [Group G] {α : G → G → kˣ}
    [IsFactorSet α] (g : G) : (twistedMonoidAlgebra k G α)ˣ where
  val := of g
  inv := (((α g g⁻¹)⁻¹ : kˣ) : k) • of g⁻¹
  val_inv := by simp [smul_smul, ← Units.val_mul]
  inv_val := by simp [smul_smul, ← Units.val_mul, IsFactorSet.apply_inv_eq_inv_apply α g]

section Construction
variable {k G : Type*} [CommSemiring k] [StarRing k] [Group G]
  {α : G → G → kˣ} [IsFactorSet α]
  [hα : Fact (∀ g h : G, star (α g h : k) = ((α g h)⁻¹ : kˣ))]

private noncomputable def conjugateReverse :
    twistedMonoidAlgebra k G α →+* (twistedMonoidAlgebra k G α)ᵐᵒᵖ := by
  letI : Algebra k (twistedMonoidAlgebra k G α)ᵐᵒᵖ := Algebra.compHom _ (starRingEnd k)
  refine (lift (k := k) (G := G) (α := α) (fun g ↦ op ((unitOf (k := k) (α := α) g)⁻¹).val) (by
      change op ((((α 1 1⁻¹)⁻¹ : kˣ) : k) • of (1 : G)⁻¹) = 1
      simp only [inv_one, IsFactorSet.one_left, of_one, Units.val_one, one_smul]; rfl)
    fun g h ↦ unop_injective ?_).toRingHom
  have hmul : unitOf (k := k) (α := α) g * unitOf h =
      Units.map (algebraMap k (twistedMonoidAlgebra k G α)).toMonoidHom (α g h) * unitOf (g * h) :=
    Units.ext <| by change of g * of h = _ * of (g * h); simp [Algebra.smul_def]
  have hinv : ((unitOf (k := k) (α := α) h)⁻¹).val * (unitOf g)⁻¹.val =
      (unitOf (g * h))⁻¹.val * algebraMap k (twistedMonoidAlgebra k G α) ((α g h)⁻¹ : kˣ) := by
    simpa [mul_inv_rev, ← map_inv] using
      congrArg (fun u : (twistedMonoidAlgebra k G α)ˣ ↦ u⁻¹.val) hmul
  simpa only [unop_mul, unop_op, Algebra.smul_def, Algebra.compHom_algebraMap_apply,
    starRingEnd_apply, MulOpposite.algebraMap_apply, hα.out g h, Algebra.commutes] using hinv
private theorem conjugateReverse_of (g : G) :
    conjugateReverse (k := k) (G := G) (α := α) (of g) =
      op ((((α g g⁻¹)⁻¹ : kˣ) : k) • of g⁻¹) := by simp [conjugateReverse]; rfl
private theorem conjugateReverse_smul (r : k) (x : twistedMonoidAlgebra k G α) :
    conjugateReverse (r • x) = op (star r • unop (conjugateReverse x)) := by
  rw [Algebra.smul_def, map_mul, show conjugateReverse (k := k) (G := G) (α := α)
      (algebraMap k _ r) = op (algebraMap k _ (star r)) by
    simp [conjugateReverse, Algebra.compHom_algebraMap_apply, starRingEnd_apply]]
  exact unop_injective (by simp [Algebra.smul_def, Algebra.commutes])
private theorem conjugateReverse_involutive (x : twistedMonoidAlgebra k G α) :
    unop (conjugateReverse (unop (conjugateReverse x))) = x := by
  let f : twistedMonoidAlgebra k G α →ₗ[k] twistedMonoidAlgebra k G α :=
    { toFun := fun y ↦ unop (conjugateReverse (unop (conjugateReverse y)))
      map_add' := fun _ _ ↦ by simp [map_add]
      map_smul' := fun _ _ ↦ by simp [conjugateReverse_smul] }
  exact LinearMap.congr_fun ((basis k G α).ext fun g ↦ by
    have hstar : star (((α g g⁻¹)⁻¹ : kˣ) : k) = (α g g⁻¹ : k) := by
      simpa using congrArg star (hα.out g g⁻¹).symm
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply, basis_apply,
      conjugateReverse_of, unop_op, conjugateReverse_smul, smul_smul, inv_inv,
      ← IsFactorSet.apply_inv_eq_inv_apply α g, hstar, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_smul] : f = LinearMap.id) x

/-- Canonical conjugate-linear star ring structure on `twistedMonoidAlgebra k G α`. -/
@[no_expose]
noncomputable instance instStarRing : StarRing (twistedMonoidAlgebra k G α) where
  star x := unop (conjugateReverse x)
  star_involutive := conjugateReverse_involutive
  star_mul _ _ := by simp [map_mul]
  star_add _ _ := by simp [map_add]
noncomputable instance instStarModule : StarModule k (twistedMonoidAlgebra k G α) where
  star_smul r x := (congrArg unop (conjugateReverse_smul r x)).trans (unop_op _)
@[simp] theorem star_of (g : G) :
    star (of g : twistedMonoidAlgebra k G α) = (((α g g⁻¹)⁻¹ : kˣ) : k) • of g⁻¹ :=
  congrArg unop (conjugateReverse_of g)
theorem star_of_of_apply_inv_eq_one {g : G} (h : α g g⁻¹ = 1) :
    star (of g : twistedMonoidAlgebra k G α) = of g⁻¹ := by simp [h]
theorem star_of_mul_of (g : G) : star (of g : twistedMonoidAlgebra k G α) * of g = 1 := by
  simp [smul_smul, ← Units.val_mul, IsFactorSet.apply_inv_eq_inv_apply α g]
theorem of_mul_star_of (g : G) : (of g : twistedMonoidAlgebra k G α) * star (of g) = 1 := by
  simp [smul_smul, ← Units.val_mul]

section Map
variable {H : Type*} [Group H] {β : H → H → kˣ} [IsFactorSet β]
  [Fact (∀ h₁ h₂ : H, star (β h₁ h₂ : k) = ((β h₁ h₂)⁻¹ : kˣ))]
theorem map_star (f : G →* H) (hf : ∀ g₁ g₂ : G, β (f g₁) (f g₂) = α g₁ g₂)
    (x : twistedMonoidAlgebra k G α) : map f hf (star x) = star (map f hf x) := by
  conv_lhs => rw [← (basis k G α).linearCombination_repr x]
  conv_rhs => rw [← (basis k G α).linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, star_sum, map_sum, star_smul, map_smul,
    basis_apply, star_of, map_of, ← map_inv, hf]
/-- A compatible monoid homomorphism induces a `⋆`-algebra homomorphism. -/
noncomputable def mapStarAlgHom (f : G →* H) (hf : ∀ g₁ g₂ : G, β (f g₁) (f g₂) = α g₁ g₂) :
    twistedMonoidAlgebra k G α →⋆ₐ[k] twistedMonoidAlgebra k H β :=
  { map f hf with map_star' := map_star f hf }
@[simp] theorem toAlgHom_mapStarAlgHom (f : G →* H)
    (hf : ∀ g₁ g₂ : G, β (f g₁) (f g₂) = α g₁ g₂) :
    (mapStarAlgHom f hf).toAlgHom = map f hf := (rfl)
@[simp] theorem mapStarAlgHom_of (f : G →* H)
    (hf : ∀ g₁ g₂ : G, β (f g₁) (f g₂) = α g₁ g₂) (g : G) :
    mapStarAlgHom f hf (of g) = of (f g) := map_of f hf g
theorem mapStarAlgHom_injective {f : G →* H} (hf : ∀ g₁ g₂ : G, β (f g₁) (f g₂) = α g₁ g₂)
    (hinj : Function.Injective f) : Function.Injective (mapStarAlgHom f hf) :=
  map_injective hf hinj
theorem scalarTrace_mapStarAlgHom {f : G →* H} (hf : ∀ g₁ g₂ : G, β (f g₁) (f g₂) = α g₁ g₂)
    (hinj : Function.Injective f) (x : twistedMonoidAlgebra k G α) :
    scalarTrace β (mapStarAlgHom f hf x) = scalarTrace α x := scalarTrace_map α hf hinj x
end Map

@[simp] theorem scalarTrace_star (x : twistedMonoidAlgebra k G α) :
    scalarTrace α (star x) = star (scalarTrace α x) := by
  conv_lhs => rw [← (basis k G α).linearCombination_repr x]
  conv_rhs => rw [← (basis k G α).linearCombination_repr x]
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, star_sum, map_sum, star_smul, map_smul,
    basis_apply, star_of, scalarTrace_of, smul_eq_mul, inv_eq_one, star_mul']
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  split_ifs with hg <;> [ (subst hg; simp [IsFactorSet.one_left]) ; simp ]
theorem scalarTrace_star_of_mul_of [DecidableEq G] (g h : G) :
    scalarTrace α (star (of g) * of h) = if g = h then 1 else 0 := by
  rw [star_of, smul_mul_assoc, map_smul, scalarTrace_of_mul_of, smul_eq_mul]
  simp only [inv_mul_eq_one]
  split_ifs with hgh
  · subst hgh
    rw [IsFactorSet.apply_inv_eq_inv_apply α g, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · simp
/-- Sesquilinear Parseval identity: `scalarTrace α (star x * y) = ∑ g, star (x_g) * y_g`. -/
theorem scalarTrace_star_mul (x y : twistedMonoidAlgebra k G α) :
    scalarTrace α (star x * y) =
      ((basis k G α).repr x).sum fun g c ↦ star c * (basis k G α).repr y g := by
  classical
  have hterm (g : G) : scalarTrace α (star (of g) * y) = (basis k G α).repr y g :=
    LinearMap.congr_fun ((basis k G α).ext fun h ↦ by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Basis.coord_apply, Basis.repr_self]
      rw [basis_apply, scalarTrace_star_of_mul_of]; simp [Finsupp.single_apply, eq_comm] :
      (scalarTrace α).comp (LinearMap.mulLeft k (star (of g))) = (basis k G α).coord g) y
  conv_lhs => rw [← (basis k G α).linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, star_sum, Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl fun g _ ↦ by
    rw [basis_apply, star_smul, smul_mul_assoc, map_smul, hterm, smul_eq_mul]
end Construction

section ComplexPositivity
variable {G : Type*} [Group G] (α : G → G → ℂˣ) [IsFactorSet α]
  [Fact (∀ g h : G, star (α g h : ℂ) = ((α g h)⁻¹ : ℂˣ))]
/-- **Parseval identity for `scalarTrace` on a complex twisted group algebra.** -/
theorem scalarTrace_star_mul_self (x : twistedMonoidAlgebra ℂ G α) :
    scalarTrace α (star x * x) =
      ((((basis ℂ G α).repr x).sum fun _ z ↦ Complex.normSq z : ℝ) : ℂ) := by
  rw [scalarTrace_star_mul]
  simpa using (Finsupp.ofReal_sum_normSq_mul ((basis ℂ G α).repr x) (fun _ ↦ (1 : ℝ))).symm
/-- **Positivity of `scalarTrace` on a complex twisted group algebra.** -/
theorem scalarTrace_star_mul_self_nonneg (x : twistedMonoidAlgebra ℂ G α) :
    0 ≤ scalarTrace α (star x * x) := by
  rw [scalarTrace_star_mul_self]
  exact Complex.zero_le_real.mpr <| by
    simpa using Finsupp.sum_normSq_mul_nonneg ((basis ℂ G α).repr x) (w := fun _ ↦ (1 : ℝ))
      (fun _ ↦ zero_le_one)
@[simp] theorem scalarTrace_star_mul_self_eq_zero_iff {x : twistedMonoidAlgebra ℂ G α} :
    scalarTrace α (star x * x) = 0 ↔ x = 0 := by
  rw [scalarTrace_star_mul_self, Complex.ofReal_eq_zero]
  have h := Finsupp.sum_normSq_mul_eq_zero_iff ((basis ℂ G α).repr x) (w := fun _ ↦ (1 : ℝ))
    (fun _ ↦ zero_le_one)
  simp only [mul_one, ne_eq, one_ne_zero, not_false_eq_true, forall_const] at h; rw [h]
  exact ⟨fun hx ↦ (basis ℂ G α).repr.map_eq_zero_iff.mp (Finsupp.ext fun s ↦ by simpa using hx s),
    fun hx s ↦ by rw [hx, LinearEquiv.map_zero, Finsupp.zero_apply]⟩
/-- The canonical scalar trace bundled as a `StarPositiveFunctional`. -/
noncomputable def scalarTracePositiveFunctional :
    StarPositiveFunctional (twistedMonoidAlgebra ℂ G α) where
  toLinearMap := scalarTrace α
  square_nonneg := scalarTrace_star_mul_self_nonneg α
@[simp] theorem toLinearMap_scalarTracePositiveFunctional :
    (scalarTracePositiveFunctional α).toLinearMap = scalarTrace α := (rfl)
@[simp] theorem scalarTracePositiveFunctional_apply (x : twistedMonoidAlgebra ℂ G α) :
    scalarTracePositiveFunctional α x = scalarTrace α x := (rfl)
@[simp] theorem nullSubmodule_scalarTracePositiveFunctional :
    (scalarTracePositiveFunctional α).nullSubmodule = ⊥ := by
  ext x; simp [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero]
end ComplexPositivity

end TauCeti.TwistedMonoidAlgebra
