/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import TauCeti.Geometry.Variational.PolynomialJet.VerticalForm
import Mathlib.LinearAlgebra.TensorProduct.Prod
import TauCeti.LinearAlgebra.ExteriorAlgebra.BaseChange
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The polynomial jet variational bicomplex and Kähler comparison

This file constructs the ambient bigraded variational algebra `PolynomialJet.JetForm R ι α` over
an arbitrary commutative ring `R`, together with its horizontal and vertical differentials
`PolynomialJet.horizDeriv` (`d_H`), `PolynomialJet.vertDeriv` (`d_V`), and total exterior
differential `PolynomialJet.totalExteriorDeriv` (`d = d_H + d_V`).

The two wedge-order equivalences `PolynomialJet.horizontalFirstEquiv` (`u ⊗ β ↦ β ∧ u`) and
`PolynomialJet.verticalFirstEquiv` (`u ⊗ β ↦ u ∧ β`) differ by the Koszul sign `(-1) ^ (p * q)`
on horizontal degree `p` and vertical degree `q`. Under vertical-first order, `d_V` agrees with
`PolynomialJet.verticalAlgDeriv` (`d_alg`) and `d_H` acquires the sign `(-1) ^ q`; under
horizontal-first order, `d_H` agrees with `PolynomialJet.unsignedHorizDeriv` (`D_H⁰`) and `d_V`
acquires the sign `(-1) ^ p`. Consequently `d_V` and `d_H` are graded derivations satisfying
`d_V² = 0`, `d_H² = 0`, `d_H d_V + d_V d_H = 0`, and `(d_H + d_V)² = 0`.

Finally, `PolynomialJet.kaehlerContactEquiv` and `PolynomialJet.kaehlerExteriorEquiv` split
Mathlib's polynomial Kähler differential module `Ω[PolynomialJet R ι α ⁄ R]` into horizontal and
contact summands (`duᵃ_I = θᵃ_I + ∑ᵢ uᵃ_(I+eᵢ) dxⁱ`) and identify `ExteriorAlgebra A Ω[A⁄R]` with
`JetForm R ι α`, matching the universal Kähler differential `D f` with `(d_H + d_V) f`.

## References

* I. M. Anderson, *The Variational Bicomplex* (1989), Chapters 1–2, for the contact splitting and
  variational bicomplex differentials.
* R. E. Borcherds, *Quantum Field Theory* lecture notes, p. 49, for the comparison between the
  commuting differentials `d_alg`, `D_H⁰` and the anticommuting signed differentials `d_V`, `d_H`
  under both wedge orders.
-/

public section

open scoped TensorProduct BigOperators

namespace TauCeti
namespace PolynomialJet

open MvPolynomial

noncomputable section

/-! ### Ambient bigraded variational algebra and wedge-order equivalences -/

section Bicomplex

variable {R ι α : Type*} [CommRing R]

/-- The ambient bigraded variational exterior algebra
`PolynomialJet R ι α ⊗[R] ExteriorAlgebra R ((ι →₀ R) × ((α × (ι →₀ ℕ)) →₀ R))`. -/
abbrev JetForm (R ι α : Type*) [CommRing R] :=
  PolynomialJet R ι α ⊗[R] ExteriorAlgebra R ((ι →₀ R) × ((α × (ι →₀ ℕ)) →₀ R))

/-- The canonical embedding of jet polynomials as `(0, 0)`-forms in `JetForm R ι α`. -/
def ofPoly : PolynomialJet R ι α →ₐ[R] JetForm R ι α :=
  Algebra.TensorProduct.includeLeft

/-- The canonical embedding of constant horizontal forms into `JetForm R ι α`. -/
def ofHoriz : HorizAlgebra R ι →ₐ[R] JetForm R ι α :=
  Algebra.TensorProduct.includeRight.comp
    (ExteriorAlgebra.map (LinearMap.inl R (ι →₀ R) ((α × (ι →₀ ℕ)) →₀ R)))

/-- The canonical embedding of constant contact forms into `JetForm R ι α`. -/
def ofContact : ContactAlgebra R ι α →ₐ[R] JetForm R ι α :=
  Algebra.TensorProduct.includeRight.comp
    (ExteriorAlgebra.map (LinearMap.inr R (ι →₀ R) ((α × (ι →₀ ℕ)) →₀ R)))

/-- The canonical embedding of relative vertical forms into `JetForm R ι α`. -/
def ofVertical : VerticalForm R ι α →ₐ[R] JetForm R ι α :=
  Algebra.TensorProduct.map (AlgHom.id R (PolynomialJet R ι α))
    (ExteriorAlgebra.map (LinearMap.inr R (ι →₀ R) ((α × (ι →₀ ℕ)) →₀ R)))

/-- The horizontal coordinate `1`-form `dxⁱ` in `JetForm R ι α`. -/
def dx (i : ι) : JetForm R ι α :=
  ofHoriz (horizGen i)

/-- The contact `1`-form `θᵃ_I` in `JetForm R ι α`. -/
def theta (a : α) (I : ι →₀ ℕ) : JetForm R ι α :=
  ofContact (contactGen a I)

theorem ofPoly_apply (f : PolynomialJet R ι α) :
    ofPoly f = f ⊗ₜ[R] (1 : ExteriorAlgebra R ((ι →₀ R) × ((α × (ι →₀ ℕ)) →₀ R))) :=
  (rfl)

theorem ofHoriz_apply (β : HorizAlgebra R ι) :
    ofHoriz (α := α) β =
      (1 : PolynomialJet R ι α) ⊗ₜ[R]
        ExteriorAlgebra.map (LinearMap.inl R (ι →₀ R) ((α × (ι →₀ ℕ)) →₀ R)) β :=
  (rfl)

theorem ofContact_apply (η : ContactAlgebra R ι α) :
    ofContact η =
      (1 : PolynomialJet R ι α) ⊗ₜ[R]
        ExteriorAlgebra.map (LinearMap.inr R (ι →₀ R) ((α × (ι →₀ ℕ)) →₀ R)) η :=
  (rfl)

@[simp]
theorem ofVertical_tmul (f : PolynomialJet R ι α) (η : ContactAlgebra R ι α) :
    ofVertical (f ⊗ₜ[R] η) = ofPoly f * ofContact η := by
  simp [ofVertical, ofPoly, ofContact, Algebra.TensorProduct.tmul_mul_tmul]

theorem ofPoly_mul_comm (f : PolynomialJet R ι α) (ω : JetForm R ι α) :
    ofPoly f * ω = ω * ofPoly f := by
  induction ω using TensorProduct.inductionOn with
  | tmul g ξ => simp [ofPoly_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add ω₁ ω₂ h₁ h₂ => simp [mul_add, add_mul, h₁, h₂]

theorem smul_eq_ofPoly_mul (f : PolynomialJet R ι α) (ω : JetForm R ι α) :
    f • ω = ofPoly f * ω := by
  induction ω using TensorProduct.inductionOn with
  | tmul g ξ => simp [ofPoly_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add ω₁ ω₂ h₁ h₂ => simp [smul_add, mul_add, h₁, h₂]

@[simp]
theorem dx_mul_self (i : ι) : dx (R := R) (α := α) i * dx i = 0 := by
  rw [dx, ← map_mul, horizGen_mul_self, map_zero]

theorem dx_mul_add_swap (i j : ι) :
    dx (R := R) (α := α) i * dx j + dx j * dx i = 0 := by
  rw [dx, dx, ← map_mul, ← map_mul, ← map_add, horizGen_mul_add_swap, map_zero]

@[simp]
theorem theta_mul_self (a : α) (I : ι →₀ ℕ) :
    theta (R := R) a I * theta a I = 0 := by
  rw [theta, ← map_mul, contactGen_mul_self, map_zero]

theorem theta_mul_add_swap (a b : α) (I J : ι →₀ ℕ) :
    theta (R := R) a I * theta b J + theta b J * theta a I = 0 := by
  rw [theta, theta, ← map_mul, ← map_mul, ← map_add, contactGen_mul_add_swap, map_zero]

theorem dx_mul_theta_add_swap (i : ι) (a : α) (I : ι →₀ ℕ) :
    dx (R := R) i * theta a I + theta a I * dx i = 0 := by
  simp only [dx, theta, ofHoriz_apply, ofContact_apply, horizGen_eq_ι, contactGen_eq_ι,
    ExteriorAlgebra.map_apply_ι, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    ← TensorProduct.tmul_add, ExteriorAlgebra.ι_add_mul_swap, TensorProduct.tmul_zero]

/-- Graded commutativity between horizontal and contact factors in `JetForm R ι α`. -/
theorem ofHoriz_mul_ofContact_eq {p q : ℕ} {β : HorizAlgebra R ι} {η : ContactAlgebra R ι α}
    (hβ : β ∈ ⋀[R]^p (ι →₀ R)) (hη : η ∈ ⋀[R]^q ((α × (ι →₀ ℕ)) →₀ R)) :
    ofHoriz (α := α) β * ofContact η = (-1 : R) ^ (p * q) • (ofContact η * ofHoriz β) := by
  have h := ExteriorAlgebra.map_inl_inr_anticomm R p q ⟨β, hβ⟩ ⟨η, hη⟩
  rw [mul_comm q p, ← Int.cast_smul_eq_zsmul R] at h
  push_cast at h
  simp only [ofHoriz_apply, ofContact_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    ← TensorProduct.tmul_smul]
  exact congrArg ((1 : PolynomialJet R ι α) ⊗ₜ[R] ·) h

theorem ofContact_mul_ofHoriz_eq {p q : ℕ} {β : HorizAlgebra R ι} {η : ContactAlgebra R ι α}
    (hβ : β ∈ ⋀[R]^p (ι →₀ R)) (hη : η ∈ ⋀[R]^q ((α × (ι →₀ ℕ)) →₀ R)) :
    ofContact η * ofHoriz (α := α) β = (-1 : R) ^ (p * q) • (ofHoriz β * ofContact η) := by
  simp [ofHoriz_mul_ofContact_eq hβ hη, smul_smul, ← mul_pow]

theorem ofVertical_mul_ofHoriz_eq {p q : ℕ} {u : VerticalForm R ι α} (hu : u ∈ verticalDegree q)
    {β : HorizAlgebra R ι} (hβ : β ∈ ⋀[R]^p (ι →₀ R)) :
    ofVertical u * ofHoriz β = (-1 : R) ^ (p * q) • (ofHoriz β * ofVertical u) := by
  refine verticalDegree_induction
    (P := fun v ↦ ofVertical v * ofHoriz β = (-1 : R) ^ (p * q) • (ofHoriz β * ofVertical v))
    (fun a b ha hb ↦ by simp [add_mul, mul_add, smul_add, ha, hb]) (fun f η hη ↦ ?_) hu
  rw [ofVertical_tmul, mul_assoc, ofContact_mul_ofHoriz_eq hβ hη, mul_smul_comm, ← mul_assoc,
    ofPoly_mul_comm f (ofHoriz β), mul_assoc]

/-- The horizontal-first wedge-order equivalence `VerticalForm ⊗ HorizAlgebra ≃ₗ[R] JetForm`,
sending `u ⊗ β` to `ofHoriz β * ofVertical u`. -/
def horizontalFirstEquiv :
    VerticalForm R ι α ⊗[R] HorizAlgebra R ι ≃ₗ[R] JetForm R ι α :=
  (TensorProduct.assoc R (PolynomialJet R ι α) (ContactAlgebra R ι α) (HorizAlgebra R ι)).trans
    (((TensorProduct.comm R (ContactAlgebra R ι α) (HorizAlgebra R ι)).trans
      ((GradedTensorProduct.of R
        (fun p : ℕ ↦ ⋀[R]^p (ι →₀ R))
        (fun q : ℕ ↦ ⋀[R]^q ((α × (ι →₀ ℕ)) →₀ R))).trans
        (ExteriorAlgebra.prodEquivTensor R (ι →₀ R)
          ((α × (ι →₀ ℕ)) →₀ R)).symm.toLinearEquiv)).lTensor (PolynomialJet R ι α))

theorem horizontalFirstEquiv_tmul (u : VerticalForm R ι α) (β : HorizAlgebra R ι) :
    horizontalFirstEquiv (u ⊗ₜ[R] β) = ofHoriz β * ofVertical u := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp [TensorProduct.add_tmul, mul_add, h₁, h₂]
  | tmul f η =>
    have hg : GradedTensorProduct.of R
        (fun p : ℕ ↦ ⋀[R]^p (ι →₀ R)) (fun q : ℕ ↦ ⋀[R]^q ((α × (ι →₀ ℕ)) →₀ R))
        (β ⊗ₜ[R] η) = β ᵍ⊗ₜ[R] η := rfl
    simp only [horizontalFirstEquiv, LinearEquiv.trans_apply, TensorProduct.assoc_tmul,
      LinearEquiv.lTensor_tmul, TensorProduct.comm_tmul, hg, AlgEquiv.toLinearEquiv_apply,
      ExteriorAlgebra.prodEquivTensor_symm_tmul, ofHoriz_apply, ofVertical_tmul, ofPoly_apply,
      ofContact_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem horizontalFirstEquiv_tmul_tmul (f : PolynomialJet R ι α) (β : HorizAlgebra R ι)
    (η : ContactAlgebra R ι α) :
    horizontalFirstEquiv ((f ⊗ₜ[R] η) ⊗ₜ[R] β) = ofPoly f * (ofHoriz β * ofContact η) := by
  rw [horizontalFirstEquiv_tmul, ofVertical_tmul, ← mul_assoc, ← ofPoly_mul_comm f (ofHoriz β),
    mul_assoc]

/-- The vertical-first wedge-order equivalence `VerticalForm ⊗ HorizAlgebra ≃ₗ[R] JetForm`,
sending `u ⊗ β` to `ofVertical u * ofHoriz β`. -/
def verticalFirstEquiv :
    VerticalForm R ι α ⊗[R] HorizAlgebra R ι ≃ₗ[R] JetForm R ι α :=
  let eSwap : ExteriorAlgebra R (((α × (ι →₀ ℕ)) →₀ R) × (ι →₀ R)) ≃ₐ[R]
      ExteriorAlgebra R ((ι →₀ R) × ((α × (ι →₀ ℕ)) →₀ R)) :=
    AlgEquiv.ofAlgHom
      (ExteriorAlgebra.map (LinearEquiv.prodComm R _ _).toLinearMap)
      (ExteriorAlgebra.map (LinearEquiv.prodComm R _ _).symm.toLinearMap)
      (by rw [ExteriorAlgebra.map_comp_map, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
        LinearEquiv.refl_toLinearMap, ExteriorAlgebra.map_id])
      (by rw [ExteriorAlgebra.map_comp_map, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
        LinearEquiv.refl_toLinearMap, ExteriorAlgebra.map_id])
  (TensorProduct.assoc R (PolynomialJet R ι α) (ContactAlgebra R ι α) (HorizAlgebra R ι)).trans
    (((GradedTensorProduct.of R
      (fun q : ℕ ↦ ⋀[R]^q ((α × (ι →₀ ℕ)) →₀ R))
      (fun p : ℕ ↦ ⋀[R]^p (ι →₀ R))).trans
      ((ExteriorAlgebra.prodEquivTensor R
        ((α × (ι →₀ ℕ)) →₀ R) (ι →₀ R)).symm.trans eSwap).toLinearEquiv).lTensor
        (PolynomialJet R ι α))

theorem verticalFirstEquiv_tmul (u : VerticalForm R ι α) (β : HorizAlgebra R ι) :
    verticalFirstEquiv (u ⊗ₜ[R] β) = ofVertical u * ofHoriz β := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp [TensorProduct.add_tmul, add_mul, h₁, h₂]
  | tmul f η =>
    have hg : GradedTensorProduct.of R
        (fun q : ℕ ↦ ⋀[R]^q ((α × (ι →₀ ℕ)) →₀ R)) (fun p : ℕ ↦ ⋀[R]^p (ι →₀ R))
        (η ⊗ₜ[R] β) = η ᵍ⊗ₜ[R] β := rfl
    have hswap₁ : ExteriorAlgebra.map
        (LinearEquiv.prodComm R ((α × (ι →₀ ℕ)) →₀ R) (ι →₀ R)).toLinearMap
        (ExteriorAlgebra.map (LinearMap.inl R ((α × (ι →₀ ℕ)) →₀ R) (ι →₀ R)) η) =
        ExteriorAlgebra.map (LinearMap.inr R (ι →₀ R) ((α × (ι →₀ ℕ)) →₀ R)) η := by
      rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]; congr 1
    have hswap₂ : ExteriorAlgebra.map
        (LinearEquiv.prodComm R ((α × (ι →₀ ℕ)) →₀ R) (ι →₀ R)).toLinearMap
        (ExteriorAlgebra.map (LinearMap.inr R ((α × (ι →₀ ℕ)) →₀ R) (ι →₀ R)) β) =
        ExteriorAlgebra.map (LinearMap.inl R (ι →₀ R) ((α × (ι →₀ ℕ)) →₀ R)) β := by
      rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]; congr 1
    simp only [verticalFirstEquiv, LinearEquiv.trans_apply, TensorProduct.assoc_tmul,
      LinearEquiv.lTensor_tmul, hg, AlgEquiv.toLinearEquiv_apply, AlgEquiv.trans_apply,
      ExteriorAlgebra.prodEquivTensor_symm_tmul, AlgEquiv.ofAlgHom_apply, map_mul,
      hswap₁, hswap₂, ofVertical_tmul, ofPoly_apply, ofContact_apply, ofHoriz_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The horizontal-first and vertical-first wedge orders differ by the Koszul sign `(-1) ^ (p * q)`
on horizontal degree `p` and vertical degree `q`. -/
theorem horizontalFirstEquiv_eq_neg_one_pow_smul_verticalFirstEquiv {p q : ℕ}
    {u : VerticalForm R ι α} (hu : u ∈ verticalDegree q)
    {β : HorizAlgebra R ι} (hβ : β ∈ ⋀[R]^p (ι →₀ R)) :
    horizontalFirstEquiv (u ⊗ₜ[R] β) =
      (-1 : R) ^ (p * q) • verticalFirstEquiv (u ⊗ₜ[R] β) := by
  simp [horizontalFirstEquiv_tmul, verticalFirstEquiv_tmul, ofVertical_mul_ofHoriz_eq hu hβ,
    smul_smul, ← mul_pow]

theorem verticalFirstEquiv_eq_neg_one_pow_smul_horizontalFirstEquiv {p q : ℕ}
    {u : VerticalForm R ι α} (hu : u ∈ verticalDegree q)
    {β : HorizAlgebra R ι} (hβ : β ∈ ⋀[R]^p (ι →₀ R)) :
    verticalFirstEquiv (u ⊗ₜ[R] β) =
      (-1 : R) ^ (p * q) • horizontalFirstEquiv (u ⊗ₜ[R] β) := by
  rw [verticalFirstEquiv_tmul, horizontalFirstEquiv_tmul, ofVertical_mul_ofHoriz_eq hu hβ]

private theorem verticalFirstEquiv_mul_verticalFirstEquiv {p q' : ℕ}
    (u : VerticalForm R ι α) {β : HorizAlgebra R ι} (hβ : β ∈ ⋀[R]^p (ι →₀ R))
    {v : VerticalForm R ι α} (hv : v ∈ verticalDegree q') (γ : HorizAlgebra R ι) :
    verticalFirstEquiv (u ⊗ₜ[R] β) * verticalFirstEquiv (v ⊗ₜ[R] γ) =
      (-1 : R) ^ (p * q') • verticalFirstEquiv ((u * v) ⊗ₜ[R] (β * γ)) := by
  have hswap : ofHoriz β * ofVertical v = (-1 : R) ^ (p * q') • (ofVertical v * ofHoriz β) := by
    simp [ofVertical_mul_ofHoriz_eq hv hβ, smul_smul, ← mul_pow]
  rw [verticalFirstEquiv_tmul, verticalFirstEquiv_tmul, verticalFirstEquiv_tmul, map_mul, map_mul,
    mul_assoc (ofVertical u), ← mul_assoc (ofHoriz β), hswap, smul_mul_assoc, mul_smul_comm]
  simp only [mul_assoc]

private theorem horizontalFirstEquiv_mul_horizontalFirstEquiv {q p' : ℕ}
    {u : VerticalForm R ι α} (hu : u ∈ verticalDegree q) (β : HorizAlgebra R ι)
    (v : VerticalForm R ι α) {γ : HorizAlgebra R ι} (hγ : γ ∈ ⋀[R]^p' (ι →₀ R)) :
    horizontalFirstEquiv (u ⊗ₜ[R] β) * horizontalFirstEquiv (v ⊗ₜ[R] γ) =
      (-1 : R) ^ (p' * q) • horizontalFirstEquiv ((u * v) ⊗ₜ[R] (β * γ)) := by
  rw [horizontalFirstEquiv_tmul, horizontalFirstEquiv_tmul, horizontalFirstEquiv_tmul,
    map_mul, map_mul]
  calc (ofHoriz β * ofVertical u) * (ofHoriz γ * ofVertical v)
      = ofHoriz β * (ofVertical u * ofHoriz γ) * ofVertical v := by simp only [mul_assoc]
    _ = (-1 : R) ^ (p' * q) • (ofHoriz β * ofHoriz γ * (ofVertical u * ofVertical v)) := by
        rw [ofVertical_mul_ofHoriz_eq hu hγ, mul_smul_comm, smul_mul_assoc]
        simp only [mul_assoc]

/-- Forms of horizontal degree `p` and vertical (contact) degree `q` in `JetForm R ι α`. -/
def bidegreeForm (p q : ℕ) : Submodule (PolynomialJet R ι α) (JetForm R ι α) :=
  Submodule.span (PolynomialJet R ι α)
    {ω | ∃ β ∈ ⋀[R]^p (ι →₀ R), ∃ η ∈ ⋀[R]^q ((α × (ι →₀ ℕ)) →₀ R),
      ω = ofHoriz β * ofContact η}

theorem ofHoriz_mul_ofContact_mem_bidegreeForm {p q : ℕ}
    {β : HorizAlgebra R ι} (hβ : β ∈ ⋀[R]^p (ι →₀ R))
    {η : ContactAlgebra R ι α} (hη : η ∈ ⋀[R]^q ((α × (ι →₀ ℕ)) →₀ R)) :
    ofHoriz (α := α) β * ofContact η ∈ bidegreeForm p q :=
  Submodule.subset_span ⟨β, hβ, η, hη, rfl⟩

theorem ofPoly_mem_bidegreeForm_zero (f : PolynomialJet R ι α) :
    ofPoly f ∈ bidegreeForm 0 0 := by
  have h1 : (1 : JetForm R ι α) ∈ bidegreeForm 0 0 := by
    simpa using ofHoriz_mul_ofContact_mem_bidegreeForm (R := R) (ι := ι) (α := α)
      (SetLike.one_mem_graded _) (SetLike.one_mem_graded _)
  simpa [smul_eq_ofPoly_mul] using Submodule.smul_mem (bidegreeForm 0 0) f h1

theorem dx_mem_bidegreeForm (i : ι) : dx (R := R) (α := α) i ∈ bidegreeForm 1 0 := by
  simpa [dx] using ofHoriz_mul_ofContact_mem_bidegreeForm (R := R) (α := α)
    (horizGen_mem_exteriorPower_one i) (SetLike.one_mem_graded _)

theorem theta_mem_bidegreeForm (a : α) (I : ι →₀ ℕ) :
    theta (R := R) a I ∈ bidegreeForm 0 1 := by
  simpa [theta] using ofHoriz_mul_ofContact_mem_bidegreeForm (R := R) (ι := ι)
    (SetLike.one_mem_graded _) (contactGen_mem_exteriorPower_one a I)

theorem horizontalFirstEquiv_mem_bidegreeForm {p q : ℕ}
    {u : VerticalForm R ι α} (hu : u ∈ verticalDegree q)
    {β : HorizAlgebra R ι} (hβ : β ∈ ⋀[R]^p (ι →₀ R)) :
    horizontalFirstEquiv (u ⊗ₜ[R] β) ∈ bidegreeForm p q := by
  refine verticalDegree_induction
    (P := fun v ↦ horizontalFirstEquiv (v ⊗ₜ[R] β) ∈ bidegreeForm p q)
    (fun u₁ u₂ h₁ h₂ ↦ by simpa [TensorProduct.add_tmul] using add_mem h₁ h₂)
    (fun f η hη ↦ ?_) hu
  rw [horizontalFirstEquiv_tmul_tmul, ← smul_eq_ofPoly_mul]
  exact Submodule.smul_mem _ f (ofHoriz_mul_ofContact_mem_bidegreeForm hβ hη)

theorem verticalFirstEquiv_mem_bidegreeForm {p q : ℕ}
    {u : VerticalForm R ι α} (hu : u ∈ verticalDegree q)
    {β : HorizAlgebra R ι} (hβ : β ∈ ⋀[R]^p (ι →₀ R)) :
    verticalFirstEquiv (u ⊗ₜ[R] β) ∈ bidegreeForm p q := by
  rw [verticalFirstEquiv_eq_neg_one_pow_smul_horizontalFirstEquiv hu hβ]
  exact Submodule.smul_of_tower_mem _ _ (horizontalFirstEquiv_mem_bidegreeForm hu hβ)

/-- Induction principle for homogeneous `(p, q)`-forms in `bidegreeForm p q`. -/
theorem bidegreeForm_induction {p q : ℕ} {P : JetForm R ι α → Prop}
    (hzero : P 0) (hadd : ∀ ω₁ ω₂, P ω₁ → P ω₂ → P (ω₁ + ω₂))
    (hgen : ∀ (f : PolynomialJet R ι α) (β : HorizAlgebra R ι) (η : ContactAlgebra R ι α),
      β ∈ ⋀[R]^p (ι →₀ R) → η ∈ ⋀[R]^q ((α × (ι →₀ ℕ)) →₀ R) →
        P (ofPoly f * (ofHoriz β * ofContact η)))
    {ω : JetForm R ι α} (hω : ω ∈ bidegreeForm p q) : P ω := by
  have hmain : ∀ x ∈ bidegreeForm p q, ∀ f : PolynomialJet R ι α, P (ofPoly f * x) := by
    intro x hx
    refine Submodule.span_induction ?_ (fun _ ↦ by simpa using hzero)
      (fun a b _ _ ha hb f ↦ by rw [mul_add]; exact hadd _ _ (ha f) (hb f))
      (fun g a _ ha f ↦ by simpa [smul_eq_ofPoly_mul, ← mul_assoc, ← map_mul] using ha (f * g)) hx
    rintro _ ⟨β, hβ, η, hη, rfl⟩ f
    exact hgen f β η hβ hη
  simpa using hmain ω hω 1

/-- Wedge multiplication adds bidegrees in `JetForm R ι α`. -/
theorem bidegreeForm_mul {p₁ q₁ p₂ q₂ : ℕ} {ω₁ ω₂ : JetForm R ι α}
    (h₁ : ω₁ ∈ bidegreeForm p₁ q₁) (h₂ : ω₂ ∈ bidegreeForm p₂ q₂) :
    ω₁ * ω₂ ∈ bidegreeForm (p₁ + p₂) (q₁ + q₂) := by
  refine Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ bidegreeForm (p₁ + p₂) (q₁ + q₂))
    ?_ (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)
    (fun _ _ _ _ _ _ ha hb ↦ by rw [add_mul]; exact add_mem ha hb)
    (fun _ _ _ _ _ _ ha hb ↦ by rw [mul_add]; exact add_mem ha hb)
    (fun f _ _ _ _ h ↦ by rw [smul_mul_assoc]; exact Submodule.smul_mem _ f h)
    (fun f _ _ _ _ h ↦ by rw [mul_smul_comm]; exact Submodule.smul_mem _ f h) h₁ h₂
  rintro _ _ ⟨β₁, hβ₁, η₁, hη₁, rfl⟩ ⟨β₂, hβ₂, η₂, hη₂, rfl⟩
  have hprod : (ofHoriz β₁ * ofContact η₁) * (ofHoriz β₂ * ofContact η₂) =
      (-1 : R) ^ (p₂ * q₁) • (ofHoriz (β₁ * β₂) * ofContact (η₁ * η₂)) := by
    calc (ofHoriz β₁ * ofContact η₁) * (ofHoriz β₂ * ofContact η₂)
        = ofHoriz β₁ * (ofContact η₁ * ofHoriz β₂) * ofContact η₂ := by simp only [mul_assoc]
      _ = (-1 : R) ^ (p₂ * q₁) • (ofHoriz (β₁ * β₂) * ofContact (η₁ * η₂)) := by
          rw [ofContact_mul_ofHoriz_eq hβ₂ hη₁, mul_smul_comm, smul_mul_assoc, map_mul, map_mul]
          simp only [mul_assoc]
  rw [hprod]
  exact Submodule.smul_of_tower_mem _ _ (ofHoriz_mul_ofContact_mem_bidegreeForm
    (SetLike.mul_mem_graded hβ₁ hβ₂) (SetLike.mul_mem_graded hη₁ hη₂))

/-! ### Signed vertical differential `d_V` -/

/-- The signed vertical differential `d_V` on `JetForm R ι α`, acting on vertical-first
decompositions without sign. -/
def vertDeriv : JetForm R ι α →ₗ[R] JetForm R ι α :=
  (verticalFirstEquiv (R := R) (ι := ι) (α := α)).toLinearMap ∘ₗ
    TensorProduct.map verticalAlgDeriv LinearMap.id ∘ₗ
    (verticalFirstEquiv (R := R) (ι := ι) (α := α)).symm.toLinearMap

/-- In vertical-first order `u ⊗ β ↦ u ∧ β`, `d_V` acts directly as `d_alg ⊗ id`. -/
@[simp]
theorem vertDeriv_verticalFirstEquiv (u : VerticalForm R ι α) (β : HorizAlgebra R ι) :
    vertDeriv (verticalFirstEquiv (u ⊗ₜ[R] β)) =
      verticalFirstEquiv (verticalAlgDeriv u ⊗ₜ[R] β) := by
  simp only [vertDeriv, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]

/-- In horizontal-first order `u ⊗ β ↦ β ∧ u`, `d_V` acquires the sign `(-1) ^ p` on horizontal
degree `p`. -/
theorem vertDeriv_horizontalFirstEquiv {p : ℕ} (u : VerticalForm R ι α)
    {β : HorizAlgebra R ι} (hβ : β ∈ ⋀[R]^p (ι →₀ R)) :
    vertDeriv (horizontalFirstEquiv (u ⊗ₜ[R] β)) =
      (-1 : R) ^ p • horizontalFirstEquiv (verticalAlgDeriv u ⊗ₜ[R] β) := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp [TensorProduct.add_tmul, smul_add, h₁, h₂]
  | tmul f η =>
    induction η using DirectSum.Decomposition.inductionOn
        (fun d : ℕ ↦ ⋀[R]^d ((α × (ι →₀ ℕ)) →₀ R)) with
    | zero => simp
    | add η₁ η₂ h₁ h₂ =>
      simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, smul_add, h₁, h₂]
    | @homogeneous q η =>
      have hu : f ⊗ₜ[R] (η : ContactAlgebra R ι α) ∈ verticalDegree q :=
        tmul_mem_verticalDegree f η.2
      rw [horizontalFirstEquiv_eq_neg_one_pow_smul_verticalFirstEquiv hu hβ, map_smul,
        vertDeriv_verticalFirstEquiv,
        verticalFirstEquiv_eq_neg_one_pow_smul_horizontalFirstEquiv
          (verticalAlgDeriv_mem_verticalDegree hu) hβ,
        smul_smul, ← pow_add]
      congr 1
      exact neg_one_pow_congr (by simp [Nat.even_add, Nat.even_mul, Nat.even_add_one]; grind)

theorem vertDeriv_ofPoly (f : PolynomialJet R ι α) :
    vertDeriv (ofPoly f) = ofVertical (verticalAlgDeriv (f ⊗ₜ[R] (1 : ContactAlgebra R ι α))) := by
  have h := vertDeriv_verticalFirstEquiv (f ⊗ₜ[R] (1 : ContactAlgebra R ι α)) 1
  simpa [verticalFirstEquiv_tmul] using h

@[simp]
theorem vertDeriv_ofPoly_X_base (j : ι) :
    vertDeriv (ofPoly (X (Sum.inl j) : PolynomialJet R ι α)) = 0 := by
  rw [vertDeriv_ofPoly, verticalAlgDeriv_tmul_one_X_base, map_zero]

@[simp]
theorem vertDeriv_ofPoly_X_field (a : α) (I : ι →₀ ℕ) :
    vertDeriv (ofPoly (X (Sum.inr (a, I)) : PolynomialJet R ι α)) = theta a I := by
  rw [vertDeriv_ofPoly, verticalAlgDeriv_tmul_one_X_field, ofVertical_tmul, map_one, one_mul, theta]

@[simp]
theorem vertDeriv_ofHoriz (β : HorizAlgebra R ι) :
    vertDeriv (ofHoriz (α := α) β) = 0 := by
  have h := vertDeriv_verticalFirstEquiv (1 : VerticalForm R ι α) β
  rw [verticalFirstEquiv_tmul, map_one, one_mul, Algebra.TensorProduct.one_def,
    verticalAlgDeriv_one_tmul, TensorProduct.zero_tmul, map_zero] at h
  exact h

@[simp]
theorem vertDeriv_ofContact (η : ContactAlgebra R ι α) :
    vertDeriv (ofContact η) = 0 := by
  have h := vertDeriv_verticalFirstEquiv ((1 : PolynomialJet R ι α) ⊗ₜ[R] η) 1
  simpa [verticalFirstEquiv_tmul] using h

@[simp]
theorem vertDeriv_dx (i : ι) : vertDeriv (dx (R := R) (α := α) i) = 0 :=
  vertDeriv_ofHoriz _

@[simp]
theorem vertDeriv_theta (a : α) (I : ι →₀ ℕ) : vertDeriv (theta (R := R) a I) = 0 :=
  vertDeriv_ofContact _

/-- `vertDeriv` raises vertical degree by one and preserves horizontal degree. -/
theorem vertDeriv_mem_bidegreeForm {p q : ℕ} {ω : JetForm R ι α}
    (hω : ω ∈ bidegreeForm p q) : vertDeriv ω ∈ bidegreeForm p (q + 1) := by
  refine bidegreeForm_induction (P := fun x ↦ vertDeriv x ∈ bidegreeForm p (q + 1))
    (by simp) (fun _ _ ha hb ↦ by simpa using add_mem ha hb) (fun f β η hβ hη ↦ ?_) hω
  rw [← horizontalFirstEquiv_tmul_tmul, vertDeriv_horizontalFirstEquiv _ hβ]
  exact Submodule.smul_of_tower_mem _ _
    (horizontalFirstEquiv_mem_bidegreeForm
      (verticalAlgDeriv_mem_verticalDegree (tmul_mem_verticalDegree f hη)) hβ)

/-- **Graded Leibniz rule for `d_V`**: on a `(p, q)`-form `ω₁`,
`d_V (ω₁ * ω₂) = d_V ω₁ * ω₂ + (-1) ^ (p + q) • (ω₁ * d_V ω₂)`. -/
theorem vertDeriv_mul {p q : ℕ} {ω₁ : JetForm R ι α} (h₁ : ω₁ ∈ bidegreeForm p q)
    (ω₂ : JetForm R ι α) :
    vertDeriv (ω₁ * ω₂) =
      vertDeriv ω₁ * ω₂ + (-1 : R) ^ (p + q) • (ω₁ * vertDeriv ω₂) := by
  obtain ⟨z, rfl⟩ := verticalFirstEquiv.surjective ω₂
  refine bidegreeForm_induction
    (P := fun x ↦ vertDeriv (x * verticalFirstEquiv z) =
      vertDeriv x * verticalFirstEquiv z +
        (-1 : R) ^ (p + q) • (x * vertDeriv (verticalFirstEquiv z)))
    (by simp) (fun _ _ ha hb ↦ by simp only [add_mul, map_add, smul_add, ha, hb]; abel)
    (fun f β η hβ hη ↦ ?_) h₁
  have h1 : ofPoly f * (ofHoriz β * ofContact η) =
      (-1 : R) ^ (p * q) • verticalFirstEquiv ((f ⊗ₜ[R] η) ⊗ₜ[R] β) := by
    rw [← horizontalFirstEquiv_tmul_tmul,
      horizontalFirstEquiv_eq_neg_one_pow_smul_verticalFirstEquiv
        (tmul_mem_verticalDegree f hη) hβ]
  rw [h1, smul_mul_assoc, map_smul, map_smul, smul_mul_assoc, smul_mul_assoc,
    smul_comm ((-1 : R) ^ (p + q)), ← smul_add]
  congr 1
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ ha hb => simp only [map_add, mul_add, smul_add, ha, hb]; abel
  | tmul u γ =>
    induction u using TensorProduct.inductionOn with
    | add u₁ u₂ ha hb =>
      simp only [TensorProduct.add_tmul, map_add, mul_add, smul_add, ha, hb]; abel
    | tmul g ξ =>
      induction ξ using DirectSum.Decomposition.inductionOn
          (fun d : ℕ ↦ ⋀[R]^d ((α × (ι →₀ ℕ)) →₀ R)) with
      | zero => simp
      | add ξ₁ ξ₂ ha hb =>
        simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, mul_add, smul_add,
          ha, hb]; abel
      | @homogeneous q' ξ =>
        have hv : g ⊗ₜ[R] (ξ : ContactAlgebra R ι α) ∈ verticalDegree q' :=
          tmul_mem_verticalDegree g ξ.2
        rw [verticalFirstEquiv_mul_verticalFirstEquiv _ hβ hv, map_smul,
          vertDeriv_verticalFirstEquiv, verticalAlgDeriv_mul (tmul_mem_verticalDegree f hη),
          TensorProduct.add_tmul, ← TensorProduct.smul_tmul', map_add, map_smul, smul_add,
          vertDeriv_verticalFirstEquiv, vertDeriv_verticalFirstEquiv,
          verticalFirstEquiv_mul_verticalFirstEquiv _ hβ hv,
          verticalFirstEquiv_mul_verticalFirstEquiv _ hβ (verticalAlgDeriv_mem_verticalDegree hv),
          smul_smul, smul_smul]
        congr 2
        rw [← pow_add, ← pow_add]
        exact neg_one_pow_congr (by simp [Nat.even_add, Nat.even_mul, Nat.even_add_one]; grind)

/-- The vertical differential `d_V` squares to zero on all of `JetForm R ι α`. -/
@[simp]
theorem vertDeriv_vertDeriv (ω : JetForm R ι α) :
    vertDeriv (vertDeriv ω) = 0 := by
  obtain ⟨z, rfl⟩ := verticalFirstEquiv.surjective ω
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ => simp [h₁, h₂]
  | tmul u β => simp

/-! ### Signed horizontal differential `d_H` and total differential `d = d_H + d_V` -/

section HorizBicomplex

variable [Fintype ι]

/-- The signed horizontal differential `d_H` on `JetForm R ι α`, acting on horizontal-first
decompositions directly as `unsignedHorizDeriv` (`D_H⁰`). -/
def horizDeriv : JetForm R ι α →ₗ[R] JetForm R ι α :=
  (horizontalFirstEquiv (R := R) (ι := ι) (α := α)).toLinearMap ∘ₗ
    unsignedHorizDeriv ∘ₗ
    (horizontalFirstEquiv (R := R) (ι := ι) (α := α)).symm.toLinearMap

/-- In horizontal-first order `u ⊗ β ↦ β ∧ u`, `d_H` acts directly as `D_H⁰`. -/
@[simp]
theorem horizDeriv_horizontalFirstEquiv (z : VerticalForm R ι α ⊗[R] HorizAlgebra R ι) :
    horizDeriv (horizontalFirstEquiv z) = horizontalFirstEquiv (unsignedHorizDeriv z) := by
  simp only [horizDeriv, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- In vertical-first order `u ⊗ β ↦ u ∧ β`, `d_H` acquires the sign `(-1) ^ q` on vertical
degree `q`. -/
theorem horizDeriv_verticalFirstEquiv {q : ℕ} {u : VerticalForm R ι α}
    (hu : u ∈ verticalDegree q) (β : HorizAlgebra R ι) :
    horizDeriv (verticalFirstEquiv (u ⊗ₜ[R] β)) =
      (-1 : R) ^ q • verticalFirstEquiv (unsignedHorizDeriv (u ⊗ₜ[R] β)) := by
  induction β using DirectSum.Decomposition.inductionOn (fun d : ℕ ↦ ⋀[R]^d (ι →₀ R)) with
  | zero => simp
  | add β₁ β₂ h₁ h₂ => simp [TensorProduct.tmul_add, smul_add, h₁, h₂]
  | @homogeneous p β =>
    rw [verticalFirstEquiv_eq_neg_one_pow_smul_horizontalFirstEquiv hu β.2, map_smul,
      horizDeriv_horizontalFirstEquiv, unsignedHorizDeriv_tmul, map_sum, map_sum,
      Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hdegβ : horizGen (R := R) i * (β : HorizAlgebra R ι) ∈ ⋀[R]^(p + 1) (ι →₀ R) := by
      rw [add_comm]
      exact SetLike.mul_mem_graded (horizGen_mem_exteriorPower_one i) β.2
    rw [horizontalFirstEquiv_eq_neg_one_pow_smul_verticalFirstEquiv
      (liftedTotalDeriv_mem_verticalDegree i hu) hdegβ, smul_smul, ← pow_add]
    congr 1
    exact neg_one_pow_congr (by simp [Nat.even_add, Nat.even_mul, Nat.even_add_one]; grind)

theorem horizDeriv_ofPoly (f : PolynomialJet R ι α) :
    horizDeriv (ofPoly f) = ∑ i : ι, totalDeriv i f • dx i := by
  have h := horizDeriv_horizontalFirstEquiv ((f ⊗ₜ[R] (1 : ContactAlgebra R ι α)) ⊗ₜ[R] 1)
  simp only [horizontalFirstEquiv_tmul, ofVertical_tmul, map_one, one_mul, mul_one,
    unsignedHorizDeriv_tmul, liftedTotalDeriv_tmul, contactDeriv_one, TensorProduct.tmul_zero,
    add_zero, map_sum, smul_eq_ofPoly_mul, dx, ofPoly_mul_comm] at h ⊢
  exact h

open Classical in
@[simp]
theorem horizDeriv_ofPoly_X_base (j : ι) :
    horizDeriv (ofPoly (X (Sum.inl j) : PolynomialJet R ι α)) = dx j := by
  rw [horizDeriv_ofPoly, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

@[simp]
theorem horizDeriv_ofPoly_X_field (a : α) (I : ι →₀ ℕ) :
    horizDeriv (ofPoly (X (Sum.inr (a, I)) : PolynomialJet R ι α)) =
      ∑ i : ι, (X (Sum.inr (a, I + Finsupp.single i 1)) : PolynomialJet R ι α) • dx i := by
  simp [horizDeriv_ofPoly]

@[simp]
theorem horizDeriv_ofHoriz (β : HorizAlgebra R ι) :
    horizDeriv (ofHoriz (α := α) β) = 0 := by
  have h := horizDeriv_horizontalFirstEquiv ((1 : VerticalForm R ι α) ⊗ₜ[R] β)
  rw [horizontalFirstEquiv_tmul, map_one, mul_one, unsignedHorizDeriv_tmul] at h
  simpa using h

@[simp]
theorem horizDeriv_dx (i : ι) : horizDeriv (dx (R := R) (α := α) i) = 0 :=
  horizDeriv_ofHoriz _

@[simp]
theorem horizDeriv_theta (a : α) (I : ι →₀ ℕ) :
    horizDeriv (theta (R := R) a I) =
      ∑ i : ι, dx i * theta a (I + Finsupp.single i 1) := by
  have h := horizDeriv_horizontalFirstEquiv
    (((1 : PolynomialJet R ι α) ⊗ₜ[R] contactGen a I) ⊗ₜ[R] 1)
  simpa [horizontalFirstEquiv_tmul, theta, dx] using h

/-- `horizDeriv` raises horizontal degree by one and preserves vertical degree. -/
theorem horizDeriv_mem_bidegreeForm {p q : ℕ} {ω : JetForm R ι α}
    (hω : ω ∈ bidegreeForm p q) : horizDeriv ω ∈ bidegreeForm (p + 1) q := by
  refine bidegreeForm_induction (P := fun x ↦ horizDeriv x ∈ bidegreeForm (p + 1) q)
    (by simp) (fun _ _ ha hb ↦ by simpa using add_mem ha hb) (fun f β η hβ hη ↦ ?_) hω
  rw [← horizontalFirstEquiv_tmul_tmul, horizDeriv_horizontalFirstEquiv, unsignedHorizDeriv_tmul,
    map_sum]
  refine sum_mem fun i _ ↦ ?_
  have hdegβ : horizGen (R := R) i * β ∈ ⋀[R]^(p + 1) (ι →₀ R) := by
    rw [add_comm]
    exact SetLike.mul_mem_graded (horizGen_mem_exteriorPower_one i) hβ
  exact horizontalFirstEquiv_mem_bidegreeForm
    (liftedTotalDeriv_mem_verticalDegree i (tmul_mem_verticalDegree f hη)) hdegβ

/-- **Graded Leibniz rule for `d_H`**: on a `(p, q)`-form `ω₁`,
`d_H (ω₁ * ω₂) = d_H ω₁ * ω₂ + (-1) ^ (p + q) • (ω₁ * d_H ω₂)`. -/
theorem horizDeriv_mul {p q : ℕ} {ω₁ : JetForm R ι α} (h₁ : ω₁ ∈ bidegreeForm p q)
    (ω₂ : JetForm R ι α) :
    horizDeriv (ω₁ * ω₂) =
      horizDeriv ω₁ * ω₂ + (-1 : R) ^ (p + q) • (ω₁ * horizDeriv ω₂) := by
  obtain ⟨z, rfl⟩ := horizontalFirstEquiv.surjective ω₂
  refine bidegreeForm_induction
    (P := fun x ↦ horizDeriv (x * horizontalFirstEquiv z) =
      horizDeriv x * horizontalFirstEquiv z +
        (-1 : R) ^ (p + q) • (x * horizDeriv (horizontalFirstEquiv z)))
    (by simp) (fun _ _ ha hb ↦ by simp only [add_mul, map_add, smul_add, ha, hb]; abel)
    (fun f β η hβ hη ↦ ?_) h₁
  rw [← horizontalFirstEquiv_tmul_tmul]
  have hu : f ⊗ₜ[R] η ∈ verticalDegree q := tmul_mem_verticalDegree f hη
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ ha hb => simp only [map_add, mul_add, smul_add, ha, hb]; abel
  | tmul u γ =>
    induction γ using DirectSum.Decomposition.inductionOn (fun d : ℕ ↦ ⋀[R]^d (ι →₀ R)) with
    | zero => simp
    | add γ₁ γ₂ ha hb =>
      simp only [TensorProduct.tmul_add, map_add, mul_add, smul_add, ha, hb]; abel
    | @homogeneous p' γ =>
      have hdxβ (i : ι) : β * (horizGen i * (γ : HorizAlgebra R ι)) =
          (-1 : R) ^ p • (horizGen i * (β * (γ : HorizAlgebra R ι))) := by
        have hβdx := TauCeti.ExteriorAlgebra.mul_eq_neg_one_pow_smul_mul_of_mem
          hβ (horizGen_mem_exteriorPower_one i)
        simp only [one_mul] at hβdx
        rw [← mul_assoc, hβdx, smul_mul_assoc, mul_assoc]
      rw [horizontalFirstEquiv_mul_horizontalFirstEquiv hu β u γ.2, map_smul,
        horizDeriv_horizontalFirstEquiv, horizDeriv_horizontalFirstEquiv,
        horizDeriv_horizontalFirstEquiv, unsignedHorizDeriv_tmul, unsignedHorizDeriv_tmul,
        unsignedHorizDeriv_tmul, map_sum, map_sum, map_sum, Finset.smul_sum, Finset.sum_mul,
        Finset.mul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hdegγ : horizGen (R := R) i * (γ : HorizAlgebra R ι) ∈ ⋀[R]^(p' + 1) (ι →₀ R) := by
        rw [add_comm]
        exact SetLike.mul_mem_graded (horizGen_mem_exteriorPower_one i) γ.2
      rw [liftedTotalDeriv_mul, TensorProduct.add_tmul, map_add, smul_add,
        horizontalFirstEquiv_mul_horizontalFirstEquiv
          (liftedTotalDeriv_mem_verticalDegree i hu) _ u γ.2,
        horizontalFirstEquiv_mul_horizontalFirstEquiv hu β _ hdegγ,
        mul_assoc (horizGen i) β (γ : HorizAlgebra R ι), hdxβ i, TensorProduct.tmul_smul,
        map_smul, smul_smul, smul_smul]
      congr 2
      rw [← pow_add, ← pow_add]
      exact neg_one_pow_congr (by simp [Nat.even_add, Nat.even_mul, Nat.even_add_one]; grind)

/-- The horizontal differential `d_H` squares to zero on all of `JetForm R ι α`. -/
@[simp]
theorem horizDeriv_horizDeriv (ω : JetForm R ι α) :
    horizDeriv (horizDeriv ω) = 0 := by
  obtain ⟨z, rfl⟩ := horizontalFirstEquiv.surjective ω
  simp

/-- **Bicomplex anticommutativity**: `d_H ∘ d_V + d_V ∘ d_H = 0` on all of `JetForm R ι α`. -/
theorem horizDeriv_vertDeriv_add_vertDeriv_horizDeriv (ω : JetForm R ι α) :
    horizDeriv (vertDeriv ω) + vertDeriv (horizDeriv ω) = 0 := by
  obtain ⟨z, rfl⟩ := horizontalFirstEquiv.surjective ω
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ =>
    simp only [map_add]
    rw [add_add_add_comm, h₁, h₂, add_zero]
  | tmul u β =>
    induction β using DirectSum.Decomposition.inductionOn (fun d : ℕ ↦ ⋀[R]^d (ι →₀ R)) with
    | zero => simp
    | add β₁ β₂ h₁ h₂ =>
      simp only [TensorProduct.tmul_add, map_add]
      rw [add_add_add_comm, h₁, h₂, add_zero]
    | @homogeneous p β =>
      rw [vertDeriv_horizontalFirstEquiv u β.2, map_smul, horizDeriv_horizontalFirstEquiv,
        horizDeriv_horizontalFirstEquiv]
      simp_rw [unsignedHorizDeriv_tmul, map_sum]
      have hterm (i : ι) :
          vertDeriv (horizontalFirstEquiv (liftedTotalDeriv i u ⊗ₜ[R]
            (horizGen i * (β : HorizAlgebra R ι)))) =
          (-1 : R) ^ (p + 1) • horizontalFirstEquiv
            (liftedTotalDeriv i (verticalAlgDeriv u) ⊗ₜ[R]
              (horizGen i * (β : HorizAlgebra R ι))) := by
        have hdegβ : horizGen (R := R) i * (β : HorizAlgebra R ι) ∈ ⋀[R]^(p + 1) (ι →₀ R) := by
          rw [add_comm]
          exact SetLike.mul_mem_graded (horizGen_mem_exteriorPower_one i) β.2
        rw [vertDeriv_horizontalFirstEquiv _ hdegβ, verticalAlgDeriv_liftedTotalDeriv]
      simp_rw [hterm]
      rw [← Finset.smul_sum, ← add_smul, pow_succ, mul_neg_one, add_neg_cancel, zero_smul]

/-- The total exterior differential `d = d_H + d_V` on `JetForm R ι α`. -/
def totalExteriorDeriv : JetForm R ι α →ₗ[R] JetForm R ι α :=
  horizDeriv + vertDeriv

theorem totalExteriorDeriv_apply (ω : JetForm R ι α) :
    totalExteriorDeriv ω = horizDeriv ω + vertDeriv ω :=
  (rfl)

/-- Vertical-first formula for `d = d_H + d_V`: on vertical degree `q`,
`d (u ∧ β) = d_alg u ∧ β + (-1) ^ q • D_H⁰ (u ⊗ β)`. -/
theorem totalExteriorDeriv_verticalFirstEquiv {q : ℕ} {u : VerticalForm R ι α}
    (hu : u ∈ verticalDegree q) (β : HorizAlgebra R ι) :
    totalExteriorDeriv (verticalFirstEquiv (u ⊗ₜ[R] β)) =
      verticalFirstEquiv (verticalAlgDeriv u ⊗ₜ[R] β) +
        (-1 : R) ^ q • verticalFirstEquiv (unsignedHorizDeriv (u ⊗ₜ[R] β)) := by
  rw [totalExteriorDeriv_apply, horizDeriv_verticalFirstEquiv hu β, vertDeriv_verticalFirstEquiv,
    add_comm]

/-- Horizontal-first formula for `d = d_H + d_V`: on horizontal degree `p`,
`d (β ∧ u) = D_H⁰ (u ⊗ β) + (-1) ^ p • (β ∧ d_alg u)`. -/
theorem totalExteriorDeriv_horizontalFirstEquiv {p : ℕ} (u : VerticalForm R ι α)
    {β : HorizAlgebra R ι} (hβ : β ∈ ⋀[R]^p (ι →₀ R)) :
    totalExteriorDeriv (horizontalFirstEquiv (u ⊗ₜ[R] β)) =
      horizontalFirstEquiv (unsignedHorizDeriv (u ⊗ₜ[R] β)) +
        (-1 : R) ^ p • horizontalFirstEquiv (verticalAlgDeriv u ⊗ₜ[R] β) := by
  rw [totalExteriorDeriv_apply, horizDeriv_horizontalFirstEquiv,
    vertDeriv_horizontalFirstEquiv u hβ]

@[simp]
theorem totalExteriorDeriv_ofPoly_X_base (j : ι) :
    totalExteriorDeriv (ofPoly (X (Sum.inl j) : PolynomialJet R ι α)) = dx j := by
  simp [totalExteriorDeriv_apply]

@[simp]
theorem totalExteriorDeriv_ofPoly_X_field (a : α) (I : ι →₀ ℕ) :
    totalExteriorDeriv (ofPoly (X (Sum.inr (a, I)) : PolynomialJet R ι α)) =
      theta a I +
        ∑ i : ι, (X (Sum.inr (a, I + Finsupp.single i 1)) : PolynomialJet R ι α) • dx i := by
  simp [totalExteriorDeriv_apply, add_comm]

/-- Contact `1`-form identity: `θᵃ_I = d uᵃ_I - ∑ᵢ uᵃ_(I+eᵢ) dxⁱ`. -/
theorem theta_eq_totalExteriorDeriv_sub (a : α) (I : ι →₀ ℕ) :
    theta (R := R) a I =
      totalExteriorDeriv (ofPoly (X (Sum.inr (a, I)) : PolynomialJet R ι α)) -
        ∑ i : ι, (X (Sum.inr (a, I + Finsupp.single i 1)) : PolynomialJet R ι α) • dx i := by
  simp

@[simp]
theorem totalExteriorDeriv_dx (i : ι) :
    totalExteriorDeriv (dx (R := R) (α := α) i) = 0 := by
  simp [totalExteriorDeriv_apply]

@[simp]
theorem totalExteriorDeriv_theta (a : α) (I : ι →₀ ℕ) :
    totalExteriorDeriv (theta (R := R) a I) =
      ∑ i : ι, dx i * theta a (I + Finsupp.single i 1) := by
  simp [totalExteriorDeriv_apply]

/-- **Graded Leibniz rule for `d = d_H + d_V`**. -/
theorem totalExteriorDeriv_mul {p q : ℕ} {ω₁ : JetForm R ι α} (h₁ : ω₁ ∈ bidegreeForm p q)
    (ω₂ : JetForm R ι α) :
    totalExteriorDeriv (ω₁ * ω₂) =
      totalExteriorDeriv ω₁ * ω₂ + (-1 : R) ^ (p + q) • (ω₁ * totalExteriorDeriv ω₂) := by
  simp only [totalExteriorDeriv_apply, horizDeriv_mul h₁, vertDeriv_mul h₁, add_mul, mul_add,
    smul_add]
  abel

/-- The total exterior differential `d = d_H + d_V` squares to zero. -/
@[simp]
theorem totalExteriorDeriv_totalExteriorDeriv (ω : JetForm R ι α) :
    totalExteriorDeriv (totalExteriorDeriv ω) = 0 := by
  simp only [totalExteriorDeriv_apply, map_add, horizDeriv_horizDeriv, vertDeriv_vertDeriv,
    zero_add, add_zero]
  rw [add_comm]
  exact horizDeriv_vertDeriv_add_vertDeriv_horizDeriv ω

end HorizBicomplex

end Bicomplex

/-! ### Contact splitting and Kähler / de Rham comparison -/

section KaehlerComparison

variable {R ι α : Type*} [CommRing R] [Fintype ι]

private def contactSplitDerivation :
    Derivation R (PolynomialJet R ι α)
      ((ι →₀ PolynomialJet R ι α) × ((α × (ι →₀ ℕ)) →₀ PolynomialJet R ι α)) :=
  MvPolynomial.mkDerivation R
    (Sum.elim
      (fun j ↦ (Finsupp.single j 1, 0))
      (fun aI ↦
        (∑ i : ι, Finsupp.single i (X (Sum.inr (aI.1, aI.2 + Finsupp.single i 1))),
          Finsupp.single aI 1)))

/-- The contact splitting of the polynomial Kähler differentials `Ω[PolynomialJet R ι α ⁄ R]`
into horizontal and contact free summands: `dxʲ ↦ (eⱼ, 0)` and
`duᵃ_I ↦ (∑ᵢ uᵃ_(I+eᵢ) eᵢ, e_(a,I))`. -/
def kaehlerContactEquiv :
    Ω[PolynomialJet R ι α ⁄ R] ≃ₗ[PolynomialJet R ι α]
      ((ι →₀ PolynomialJet R ι α) × ((α × (ι →₀ ℕ)) →₀ PolynomialJet R ι α)) :=
  let toFun := contactSplitDerivation.liftKaehlerDifferential
  let invHoriz : (ι →₀ PolynomialJet R ι α) →ₗ[PolynomialJet R ι α]
      Ω[PolynomialJet R ι α ⁄ R] :=
    Finsupp.linearCombination (PolynomialJet R ι α)
      fun j ↦ KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inl j))
  let invContact : ((α × (ι →₀ ℕ)) →₀ PolynomialJet R ι α) →ₗ[PolynomialJet R ι α]
      Ω[PolynomialJet R ι α ⁄ R] :=
    Finsupp.linearCombination (PolynomialJet R ι α) fun aI ↦
      KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inr aI)) -
        ∑ i : ι, (X (Sum.inr (aI.1, aI.2 + Finsupp.single i 1)) : PolynomialJet R ι α) •
          KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inl i))
  LinearEquiv.ofLinearMap toFun (invHoriz.coprod invContact)
    (by
      apply LinearMap.prod_ext
      · apply Finsupp.lhom_ext'; intro j; apply LinearMap.ext_ring
        simp [toFun, invHoriz, contactSplitDerivation]
      · apply Finsupp.lhom_ext'; rintro ⟨a, I⟩; apply LinearMap.ext_ring
        apply Prod.ext <;> simp [toFun, invContact, contactSplitDerivation, map_sum,
          Prod.fst_sum, Prod.snd_sum])
    (by
      apply Derivation.liftKaehlerDifferential_unique
      apply MvPolynomial.derivation_ext
      rintro (j | ⟨a, I⟩)
      · simp [toFun, invHoriz, contactSplitDerivation]
      · simp [toFun, invHoriz, invContact, contactSplitDerivation, map_sum])

@[simp]
theorem kaehlerContactEquiv_D_X_base (j : ι) :
    kaehlerContactEquiv (R := R) (α := α)
      (KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inl j))) =
      (Finsupp.single j 1, 0) := by
  simp [kaehlerContactEquiv, contactSplitDerivation]

@[simp]
theorem kaehlerContactEquiv_D_X_field (a : α) (I : ι →₀ ℕ) :
    kaehlerContactEquiv (R := R)
      (KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inr (a, I)))) =
      (∑ i : ι, Finsupp.single i (X (Sum.inr (a, I + Finsupp.single i 1))),
        Finsupp.single (a, I) 1) := by
  simp [kaehlerContactEquiv, contactSplitDerivation]

@[simp]
theorem kaehlerContactEquiv_symm_inl (j : ι) :
    (kaehlerContactEquiv (R := R) (α := α)).symm (Finsupp.single j 1, 0) =
      KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inl j)) := by
  simp [kaehlerContactEquiv]

@[simp]
theorem kaehlerContactEquiv_symm_inr (a : α) (I : ι →₀ ℕ) :
    (kaehlerContactEquiv (R := R)).symm (0, Finsupp.single (a, I) 1) =
      KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inr (a, I))) -
        ∑ i : ι, (X (Sum.inr (a, I + Finsupp.single i 1)) : PolynomialJet R ι α) •
          KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inl i)) := by
  simp [kaehlerContactEquiv]

/-- Algebra equivalence identifying `ExteriorAlgebra A Ω[A⁄R]` with the variational bicomplex
`JetForm R ι α` via the contact splitting. -/
def kaehlerExteriorEquiv :
    ExteriorAlgebra (PolynomialJet R ι α) Ω[PolynomialJet R ι α ⁄ R] ≃ₐ[PolynomialJet R ι α]
      JetForm R ι α := by
  classical
  let e : Ω[PolynomialJet R ι α ⁄ R] ≃ₗ[PolynomialJet R ι α]
      PolynomialJet R ι α ⊗[R] ((ι →₀ R) × ((α × (ι →₀ ℕ)) →₀ R)) :=
    kaehlerContactEquiv.trans
      ((LinearEquiv.prodCongr
        (TensorProduct.finsuppScalarRight R (PolynomialJet R ι α) (PolynomialJet R ι α) ι).symm
        (TensorProduct.finsuppScalarRight R (PolynomialJet R ι α) (PolynomialJet R ι α)
          (α × (ι →₀ ℕ))).symm).trans
        (TensorProduct.prodRight R (PolynomialJet R ι α) (PolynomialJet R ι α)
          (ι →₀ R) ((α × (ι →₀ ℕ)) →₀ R)).symm)
  exact (AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap)
      (ExteriorAlgebra.map e.symm.toLinearMap)
      (by rw [ExteriorAlgebra.map_comp_map, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
        LinearEquiv.refl_toLinearMap, ExteriorAlgebra.map_id])
      (by rw [ExteriorAlgebra.map_comp_map, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
        LinearEquiv.refl_toLinearMap, ExteriorAlgebra.map_id])).trans
    (ExteriorAlgebra.baseChangeEquiv R ((ι →₀ R) × ((α × (ι →₀ ℕ)) →₀ R))
      (PolynomialJet R ι α)).symm

omit [Fintype ι] in
private theorem prodRight_symm_fst (g : PolynomialJet R ι α) (i : ι) :
    (TensorProduct.prodRight R (PolynomialJet R ι α) (PolynomialJet R ι α)
      (ι →₀ R) ((α × (ι →₀ ℕ)) →₀ R)).symm (g ⊗ₜ[R] Finsupp.single i (1 : R), 0) =
      g ⊗ₜ[R] (Finsupp.single i (1 : R), 0) := by
  have hz : (0 : PolynomialJet R ι α ⊗[R] ((α × (ι →₀ ℕ)) →₀ R)) = g ⊗ₜ[R] 0 :=
    (TensorProduct.tmul_zero _ _).symm
  rw [hz, TensorProduct.prodRight_symm_tmul]

@[simp]
theorem kaehlerExteriorEquiv_ι_D_X_base (j : ι) :
    kaehlerExteriorEquiv (R := R) (α := α)
        (ExteriorAlgebra.ι (PolynomialJet R ι α)
          (KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inl j)))) =
      dx j := by
  simp only [kaehlerExteriorEquiv, AlgEquiv.trans_apply, AlgEquiv.ofAlgHom_apply,
    ExteriorAlgebra.map_apply_ι, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    kaehlerContactEquiv_D_X_base, LinearEquiv.prodCongr_apply,
    TensorProduct.finsuppScalarRight_symm_apply_single, map_zero, prodRight_symm_fst,
    ExteriorAlgebra.baseChangeEquiv_symm_ι, LinearMap.baseChange_tmul, dx, ofHoriz_apply,
    horizGen_eq_ι, LinearMap.inl_apply]

@[simp]
theorem kaehlerExteriorEquiv_ι_D_X_field (a : α) (I : ι →₀ ℕ) :
    kaehlerExteriorEquiv (R := R)
        (ExteriorAlgebra.ι (PolynomialJet R ι α)
          (KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inr (a, I))))) =
      theta a I +
        ∑ i : ι, (X (Sum.inr (a, I + Finsupp.single i 1)) : PolynomialJet R ι α) • dx i := by
  have hsplit :
      (∑ i : ι, (X (Sum.inr (a, I + Finsupp.single i 1)) : PolynomialJet R ι α) ⊗ₜ[R]
          Finsupp.single i (1 : R),
        (1 : PolynomialJet R ι α) ⊗ₜ[R] Finsupp.single (a, I) (1 : R)) =
      ((1 : PolynomialJet R ι α) ⊗ₜ[R] (0 : ι →₀ R),
        (1 : PolynomialJet R ι α) ⊗ₜ[R] Finsupp.single (a, I) (1 : R)) +
      ∑ i : ι, ((X (Sum.inr (a, I + Finsupp.single i 1)) : PolynomialJet R ι α) ⊗ₜ[R]
        Finsupp.single i (1 : R), 0) := by
    apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  simp only [kaehlerExteriorEquiv, AlgEquiv.trans_apply, AlgEquiv.ofAlgHom_apply,
    ExteriorAlgebra.map_apply_ι, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    kaehlerContactEquiv_D_X_field, LinearEquiv.prodCongr_apply, map_sum,
    TensorProduct.finsuppScalarRight_symm_apply_single, hsplit, map_add, prodRight_symm_fst,
    TensorProduct.prodRight_symm_tmul, ExteriorAlgebra.baseChangeEquiv_symm_ι,
    LinearMap.baseChange_tmul]
  congr 1
  · simp [theta, ofContact_apply, contactGen_eq_ι, ExteriorAlgebra.map_apply_ι]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [dx, ofHoriz_apply, horizGen_eq_ι, ExteriorAlgebra.map_apply_ι,
      smul_eq_ofPoly_mul, ofPoly_apply, Algebra.TensorProduct.tmul_mul_tmul]

/-- Under `kaehlerExteriorEquiv`, the universal Kähler differential `D f` agrees with the total
bicomplex differential `(d_H + d_V) f` for every jet polynomial `f`. -/
theorem kaehlerExteriorEquiv_ι_D (f : PolynomialJet R ι α) :
    kaehlerExteriorEquiv
        (ExteriorAlgebra.ι (PolynomialJet R ι α)
          (KaehlerDifferential.D R (PolynomialJet R ι α) f)) =
      totalExteriorDeriv (ofPoly f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    have hc : (C c : PolynomialJet R ι α) = algebraMap R (PolynomialJet R ι α) c := rfl
    have hof : ofPoly (algebraMap R (PolynomialJet R ι α) c) =
        ofHoriz (α := α) (algebraMap R (HorizAlgebra R ι) c) := by
      rw [ofPoly_apply, ofHoriz_apply, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, map_smul, map_one]
    rw [hc, Derivation.map_algebraMap, map_zero, map_zero, hof, totalExteriorDeriv_apply,
      horizDeriv_ofHoriz, vertDeriv_ofHoriz, add_zero]
  | add f g hf hg => simp [map_add, hf, hg]
  | mul_X f v hf =>
    rw [Derivation.leibniz, map_add, map_smul, map_smul, map_add, map_smul, map_smul, hf,
      map_mul, totalExteriorDeriv_mul (ofPoly_mem_bidegreeForm_zero f), add_zero, pow_zero,
      one_smul, smul_eq_ofPoly_mul, smul_eq_ofPoly_mul, ofPoly_mul_comm (X v), add_comm]
    congr 2
    rcases v with j | ⟨a, I⟩ <;> simp

@[simp]
theorem kaehlerExteriorEquiv_symm_dx (j : ι) :
    (kaehlerExteriorEquiv (R := R) (α := α)).symm (dx j) =
      ExteriorAlgebra.ι (PolynomialJet R ι α)
        (KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inl j))) := by
  apply (kaehlerExteriorEquiv (R := R) (ι := ι) (α := α)).injective
  rw [AlgEquiv.apply_symm_apply, kaehlerExteriorEquiv_ι_D_X_base]

/-- Under `kaehlerExteriorEquiv.symm`, the contact generator `θᵃ_I` is the Kähler contact
`1`-form `D uᵃ_I - ∑ᵢ uᵃ_(I+eᵢ) D xⁱ`. -/
@[simp]
theorem kaehlerExteriorEquiv_symm_theta (a : α) (I : ι →₀ ℕ) :
    (kaehlerExteriorEquiv (R := R)).symm (theta a I) =
      ExteriorAlgebra.ι (PolynomialJet R ι α)
        (KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inr (a, I))) -
          ∑ i : ι, (X (Sum.inr (a, I + Finsupp.single i 1)) : PolynomialJet R ι α) •
            KaehlerDifferential.D R (PolynomialJet R ι α) (X (Sum.inl i))) := by
  apply (kaehlerExteriorEquiv (R := R) (ι := ι) (α := α)).injective
  simp [AlgEquiv.apply_symm_apply]

end KaehlerComparison

end
end PolynomialJet
end TauCeti
