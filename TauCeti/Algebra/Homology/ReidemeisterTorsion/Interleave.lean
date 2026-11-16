/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Interleave
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Algebra.Homology.ModuleCat.Finrank

/-!
# Reidemeister torsion of interleaved chain complexes

Given three `ℤ`-indexed families of vector spaces `X₁`, `X₂`, `X₃` over a field `F` and morphisms
`f q : X₁ q ⟶ X₂ q`, `g q : X₂ q ⟶ X₃ q` and `δ q : X₃ (q + 1) ⟶ X₁ q` whose consecutive
composites vanish, `ChainComplex.interleave` places `X₁ q`, `X₂ q` and `X₃ q` in degrees `3q + 2`,
`3q + 1` and `3q`, and `ChainComplex.interleave.basis` assembles degreewise bases `b₁`, `b₂`, `b₃`
into bases of the interleaved complex.

This file proves two results about the Reidemeister torsion of an interleaved complex:
* `ChainComplex.interleave.reidemeisterTorsion_basis_eq_mul`: replacing `(b₁, b₂, b₃)` by
  `(b₁', b₂', b₃')` multiplies the Reidemeister torsion by the product of the three alternating
  transition determinants, with exponents `(-1) ^ q` on `X₁` and `X₃` and `(-1) ^ (q + 1)` on `X₂`.
* `ChainComplex.interleave.reidemeisterTorsion_basis_eq_one`: when a bounded interleaved complex is
  given bases `b₁ q = (u q, v' q)`, `b₂ q = (v q, w' q)` and `b₃ (q + 1) = (w (q + 1), u' q)`
  adapted to bases `u q`, `v q`, `w q` of the images of `δ q`, `f q`, `g q` and lifts `v' q`,
  `w' q`, `u' q`, the complex is acyclic and its Reidemeister torsion is `1`.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1–2.
-/

public section

noncomputable section

open CategoryTheory Module

namespace ChainComplex.interleave

section BasisChange

/-- Regroup a finitely supported product over `ℤ` according to residues modulo `3`. -/
private theorem finprod_int_three_mul {M : Type*} [CommMonoid M] {g : ℤ → M}
    (hg : Function.HasFiniteMulSupport g) :
    ∏ᶠ n : ℤ, g n =
      (∏ᶠ q : ℤ, g (3 * q + 2)) * (∏ᶠ q : ℤ, g (3 * q + 1)) * ∏ᶠ q : ℤ, g (3 * q) := by
  have h₂ : Function.HasFiniteMulSupport fun q ↦ g (3 * q + 2) :=
    hg.preimage fun _ _ _ _ h ↦ by omega
  have h₁ : Function.HasFiniteMulSupport fun q ↦ g (3 * q + 1) :=
    hg.preimage fun _ _ _ _ h ↦ by omega
  have h₀ : Function.HasFiniteMulSupport fun q ↦ g (3 * q) :=
    hg.preimage fun _ _ _ _ h ↦ by omega
  let e (q : ℤ) : Fin 3 ≃ {n : ℤ // n / 3 = q} :=
    { toFun i := ⟨3 * q + i, by omega⟩
      invFun n := ⟨(n.1 % 3).toNat, by have := n.2; omega⟩
      left_inv i := by ext; simp; omega
      right_inv n := by ext; have := n.2; simp; omega }
  have he (q : ℤ) (i : Fin 3) : ((e q i : {n : ℤ // n / 3 = q}) : ℤ) = 3 * q + i.1 := rfl
  rw [← TauCeti.finprod_fiberwise (fun n : ℤ ↦ n / 3) g hg]
  trans (∏ᶠ q : ℤ, (g (3 * q + 2) * g (3 * q + 1)) * g (3 * q))
  · refine finprod_congr fun q ↦ ?_
    rw [← finprod_comp_equiv (e q), finprod_eq_prod_of_fintype, Fin.prod_univ_three,
      he q 0, he q 1, he q 2]
    simp only [Fin.val_zero, Nat.cast_zero, add_zero, Fin.val_one, Nat.cast_one, Fin.val_two,
      Nat.cast_ofNat]
    rw [mul_comm (_ * _), mul_comm (g (3 * q)), ← mul_assoc]
  · rw [finprod_mul_distrib (h₂.fun_mul h₁) h₀, finprod_mul_distrib h₂ h₁]

variable {F : Type*} [Field F] {X₁ X₂ X₃ : ℤ → ModuleCat F} {f : ∀ q, X₁ q ⟶ X₂ q}
  {g : ∀ q, X₂ q ⟶ X₃ q} {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q} (hfg : ∀ q, f q ≫ g q = 0)
  (hgδ : ∀ q, g (q + 1) ≫ δ q = 0) (hδf : ∀ q, δ q ≫ f q = 0)
  {m₁ m₂ m₃ : ℤ → ℕ}
  (b₁ b₁' : ∀ q, Basis (Fin (m₁ q)) F (X₁ q))
  (b₂ b₂' : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
  (b₃ b₃' : ∀ q, Basis (Fin (m₃ q)) F (X₃ q))

private theorem basis_det_basis₁ {n q : ℤ} (h : n = 3 * q + 2) :
    (basis hfg hgδ hδf b₁ b₂ b₃ n).det (basis hfg hgδ hδf b₁' b₂' b₃' n) =
      (b₁ q).det (b₁' q) := by
  have hb : basis hfg hgδ hδf b₁ b₂ b₃ n =
      ((b₁ q).reindex (finCongr (rank_of_eq_three_mul_add_two h).symm)).map
        (XIso₁ hfg hgδ hδf n q h).symm.toLinearEquiv :=
    DFunLike.ext _ _ fun i ↦ (XIso₁ hfg hgδ hδf n q h).toLinearEquiv.injective (by simp)
  rw [hb, Basis.det_map, Basis.det_reindex]
  congr 1
  ext i
  exact XIso₁_hom_basis hfg hgδ hδf b₁' b₂' b₃' h _

private theorem basis_det_basis₂ {n q : ℤ} (h : n = 3 * q + 1) :
    (basis hfg hgδ hδf b₁ b₂ b₃ n).det (basis hfg hgδ hδf b₁' b₂' b₃' n) =
      (b₂ q).det (b₂' q) := by
  have hb : basis hfg hgδ hδf b₁ b₂ b₃ n =
      ((b₂ q).reindex (finCongr (rank_of_eq_three_mul_add_one h).symm)).map
        (XIso₂ hfg hgδ hδf n q h).symm.toLinearEquiv :=
    DFunLike.ext _ _ fun i ↦ (XIso₂ hfg hgδ hδf n q h).toLinearEquiv.injective (by simp)
  rw [hb, Basis.det_map, Basis.det_reindex]
  congr 1
  ext i
  exact XIso₂_hom_basis hfg hgδ hδf b₁' b₂' b₃' h _

private theorem basis_det_basis₃ {n q : ℤ} (h : n = 3 * q) :
    (basis hfg hgδ hδf b₁ b₂ b₃ n).det (basis hfg hgδ hδf b₁' b₂' b₃' n) =
      (b₃ q).det (b₃' q) := by
  have hb : basis hfg hgδ hδf b₁ b₂ b₃ n =
      ((b₃ q).reindex (finCongr (rank_of_eq_three_mul h).symm)).map
        (XIso₃ hfg hgδ hδf n q h).symm.toLinearEquiv :=
    DFunLike.ext _ _ fun i ↦ (XIso₃ hfg hgδ hδf n q h).toLinearEquiv.injective (by simp)
  rw [hb, Basis.det_map, Basis.det_reindex]
  congr 1
  ext i
  exact XIso₃_hom_basis hfg hgδ hδf b₁' b₂' b₃' h _

/-- Replacing the families of bases `b₁`, `b₂`, `b₃` of an interleaved complex by `b₁'`, `b₂'`,
`b₃'` multiplies its Reidemeister torsion by the product of the three alternating transition
determinants, with exponents `(-1) ^ q` on `X₁` and `X₃` (degrees `3q + 2` and `3q`) and
`(-1) ^ (q + 1)` on `X₂` (degree `3q + 1`). -/
theorem reidemeisterTorsion_basis_eq_mul :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion (basis hfg hgδ hδf b₁' b₂' b₃') =
      (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion (basis hfg hgδ hδf b₁ b₂ b₃) *
        ((∏ᶠ q : ℤ, (b₁ q).det (b₁' q) ^ (q.negOnePow : ℤ)) *
          (∏ᶠ q : ℤ, (b₂ q).det (b₂' q) ^ ((q + 1).negOnePow : ℤ)) *
          ∏ᶠ q : ℤ, (b₃ q).det (b₃' q) ^ (q.negOnePow : ℤ)) := by
  by_cases hr : {n | rank m₁ m₂ m₃ n ≠ 0}.Finite
  swap
  · simp [HomologicalComplex.reidemeisterTorsion_of_not_finite _ _ hr]
  have hsupp : Function.HasFiniteMulSupport fun n : ℤ ↦
      (basis hfg hgδ hδf b₁ b₂ b₃ n).det (basis hfg hgδ hδf b₁' b₂' b₃' n) ^
        (n.negOnePow : ℤ) :=
    hr.subset <| Function.mulSupport_subset_iff'.2 fun n hn ↦ by
      have : IsEmpty (Fin (rank m₁ m₂ m₃ n)) := by
        rw [show rank m₁ m₂ m₃ n = 0 by simpa using hn]; infer_instance
      simp
  rw [HomologicalComplex.reidemeisterTorsion_eq_mul_finprod_det _ (basis hfg hgδ hδf b₁ b₂ b₃),
    finprod_int_three_mul hsupp]
  congr 2
  · congr 1
    · refine finprod_congr fun q ↦ ?_
      rw [basis_det_basis₁ hfg hgδ hδf b₁ b₁' b₂ b₂' b₃ b₃' rfl,
        (Int.negOnePow_eq_iff (3 * q + 2) q).2 ⟨q + 1, by omega⟩]
    · refine finprod_congr fun q ↦ ?_
      rw [basis_det_basis₂ hfg hgδ hδf b₁ b₁' b₂ b₂' b₃ b₃' rfl,
        (Int.negOnePow_eq_iff (3 * q + 1) (q + 1)).2 ⟨q, by omega⟩]
  · refine finprod_congr fun q ↦ ?_
    rw [basis_det_basis₃ hfg hgδ hδf b₁ b₁' b₂ b₂' b₃ b₃' rfl,
      (Int.negOnePow_eq_iff (3 * q) q).2 ⟨q, by omega⟩]

end BasisChange

section AdaptedBasis

variable {F : Type*} [Field F]

/-- Transport the range of a linear map along isomorphisms of its source and target. -/
private def rangeLinearEquivOfIso {M₁ M₂ N₁ N₂ : ModuleCat F} {φ : M₁ ⟶ N₁} {ψ : M₂ ⟶ N₂}
    (eM : M₁ ≅ M₂) (eN : N₁ ≅ N₂) (h : φ = eM.hom ≫ ψ ≫ eN.inv) :
    LinearMap.range ψ.hom ≃ₗ[F] LinearMap.range φ.hom where
  toFun y := ⟨eN.inv.hom y.1, by obtain ⟨x, hx⟩ := y.2; exact ⟨eM.inv.hom x, by simp [h, hx]⟩⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)
  invFun z := ⟨eN.hom.hom z.1, by obtain ⟨x, hx⟩ := z.2; exact ⟨eM.hom.hom x, by simp [h, ← hx]⟩⟩
  left_inv _ := Subtype.ext (by simp)
  right_inv _ := Subtype.ext (by simp)

@[simp]
private theorem coe_rangeLinearEquivOfIso {M₁ M₂ N₁ N₂ : ModuleCat F} {φ : M₁ ⟶ N₁} {ψ : M₂ ⟶ N₂}
    (eM : M₁ ≅ M₂) (eN : N₁ ≅ N₂) (h : φ = eM.hom ≫ ψ ≫ eN.inv) (y : LinearMap.range ψ.hom) :
    (rangeLinearEquivOfIso eM eN h y : N₁) = eN.inv.hom y.1 :=
  (rfl)

private theorem map_append_eq_append_cast {X Y : Type*} {p' r' p r : ℕ} (φ : X → Y)
    (x : Fin p' → X) (y : Fin r' → X) (a : Fin p → Y) (b : Fin r → Y)
    (hp : p' = p) (hr : r' = r) (hx : ∀ l, φ (x l) = a (Fin.cast hp l))
    (hy : ∀ l, φ (y l) = b (Fin.cast hr l)) (hc : p' + r' = p + r) (m : Fin (p' + r')) :
    φ (Fin.append x y m) = Fin.append a b (Fin.cast hc m) := by
  subst hp hr
  induction m using Fin.addCases <;> simp [hx, hy]

variable {X₁ X₂ X₃ : ℤ → ModuleCat F} {f : ∀ q, X₁ q ⟶ X₂ q}
  {g : ∀ q, X₂ q ⟶ X₃ q} {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q}
  {hfg : ∀ q, f q ≫ g q = 0} {hgδ : ∀ q, g (q + 1) ≫ δ q = 0} {hδf : ∀ q, δ q ≫ f q = 0}
  {m₁ m₂ m₃ α β γ : ℤ → ℕ}
  (b₁ : ∀ q, Basis (Fin (m₁ q)) F (X₁ q))
  (b₂ : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
  (b₃ : ∀ q, Basis (Fin (m₃ q)) F (X₃ q))
  (u : ∀ q, Basis (Fin (α q)) F (LinearMap.range (δ q).hom))
  (v : ∀ q, Basis (Fin (β q)) F (LinearMap.range (f q).hom))
  (w : ∀ q, Basis (Fin (γ q)) F (LinearMap.range (g q).hom))
  (v' : ∀ q, Fin (β q) → X₁ q) (hv' : ∀ q k, (f q).hom (v' q k) = v q k)
  (w' : ∀ q, Fin (γ q) → X₂ q) (hw' : ∀ q k, (g q).hom (w' q k) = w q k)
  (u' : ∀ q, Fin (α q) → X₃ (q + 1)) (hu' : ∀ q k, (δ q).hom (u' q k) = u q k)

/-- The boundary basis of `interleave` in degree `n`, transported from `w`, `v` or `u`. -/
private def adaptedBoundaryBasis (n : ℤ) :
    Basis (Fin (rank α β γ n)) F
      (LinearMap.range ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom) :=
  if h₀ : n % 3 = 0 then
    ((w (n / 3)).reindex (finCongr (rank_of_eq_three_mul (by omega)).symm)).map
      (rangeLinearEquivOfIso (XIso₂ hfg hgδ hδf (n + 1) (n / 3) (by omega))
        (XIso₃ hfg hgδ hδf n (n / 3) (by omega))
        (interleave_d_eq_of_eq_three_mul hfg hgδ hδf (by omega)))
  else if h₁ : n % 3 = 1 then
    ((v (n / 3)).reindex (finCongr (rank_of_eq_three_mul_add_one (by omega)).symm)).map
      (rangeLinearEquivOfIso (XIso₁ hfg hgδ hδf (n + 1) (n / 3) (by omega))
        (XIso₂ hfg hgδ hδf n (n / 3) (by omega))
        (interleave_d_eq_of_eq_three_mul_add_one hfg hgδ hδf (by omega)))
  else
    ((u (n / 3)).reindex (finCongr (rank_of_eq_three_mul_add_two (by omega)).symm)).map
      (rangeLinearEquivOfIso (XIso₃ hfg hgδ hδf (n + 1) (n / 3 + 1) (by omega))
        (XIso₁ hfg hgδ hδf n (n / 3) (by omega))
        (interleave_d_eq_of_eq_three_mul_add_two hfg hgδ hδf (by omega)))

/-- Lifts of `adaptedBoundaryBasis` to degree `n + 1`, transported from `w'`, `v'` or `u'`. -/
private def adaptedBoundaryLift (n : ℤ) (k : Fin (rank α β γ n)) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X (n + 1) :=
  if h₀ : n % 3 = 0 then
    (XIso₂ hfg hgδ hδf (n + 1) (n / 3) (by omega)).inv
      (w' (n / 3) (Fin.cast (rank_of_eq_three_mul (by omega)) k))
  else if h₁ : n % 3 = 1 then
    (XIso₁ hfg hgδ hδf (n + 1) (n / 3) (by omega)).inv
      (v' (n / 3) (Fin.cast (rank_of_eq_three_mul_add_one (by omega)) k))
  else
    (XIso₃ hfg hgδ hδf (n + 1) (n / 3 + 1) (by omega)).inv
      (u' (n / 3) (Fin.cast (rank_of_eq_three_mul_add_two (by omega)) k))

private theorem coe_adaptedBoundaryBasis₁ {n q : ℤ} (h : n = 3 * q + 2) (k : Fin (rank α β γ n)) :
    (XIso₁ hfg hgδ hδf n q h).hom (adaptedBoundaryBasis u v w n k : _) =
      u q (Fin.cast (rank_of_eq_three_mul_add_two h) k) := by
  obtain rfl : n / 3 = q := by omega
  rw [adaptedBoundaryBasis, dite_eq_right (by omega), dite_eq_right (by omega)]
  simp

private theorem coe_adaptedBoundaryBasis₂ {n q : ℤ} (h : n = 3 * q + 1) (k : Fin (rank α β γ n)) :
    (XIso₂ hfg hgδ hδf n q h).hom (adaptedBoundaryBasis u v w n k : _) =
      v q (Fin.cast (rank_of_eq_three_mul_add_one h) k) := by
  obtain rfl : n / 3 = q := by omega
  rw [adaptedBoundaryBasis, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

private theorem coe_adaptedBoundaryBasis₃ {n q : ℤ} (h : n = 3 * q) (k : Fin (rank α β γ n)) :
    (XIso₃ hfg hgδ hδf n q h).hom (adaptedBoundaryBasis u v w n k : _) =
      w q (Fin.cast (rank_of_eq_three_mul h) k) := by
  obtain rfl : n / 3 = q := by omega
  rw [adaptedBoundaryBasis, dite_eq_left (by omega)]
  simp

private theorem XIso₁_adaptedBoundaryLift {n q : ℤ} (h : n = 3 * q + 1) (k : Fin (rank α β γ n)) :
    (XIso₁ hfg hgδ hδf (n + 1) q (by omega)).hom (adaptedBoundaryLift v' w' u' n k) =
      v' q (Fin.cast (rank_of_eq_three_mul_add_one h) k) := by
  obtain rfl : n / 3 = q := by omega
  rw [adaptedBoundaryLift, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

private theorem XIso₂_adaptedBoundaryLift {n q : ℤ} (h : n = 3 * q) (k : Fin (rank α β γ n)) :
    (XIso₂ hfg hgδ hδf (n + 1) q (by omega)).hom (adaptedBoundaryLift v' w' u' n k) =
      w' q (Fin.cast (rank_of_eq_three_mul h) k) := by
  obtain rfl : n / 3 = q := by omega
  rw [adaptedBoundaryLift, dite_eq_left (by omega)]
  simp

private theorem XIso₃_adaptedBoundaryLift {n q : ℤ} (h : n = 3 * q + 2) (k : Fin (rank α β γ n)) :
    (XIso₃ hfg hgδ hδf (n + 1) (q + 1) (by omega)).hom (adaptedBoundaryLift v' w' u' n k) =
      u' q (Fin.cast (rank_of_eq_three_mul_add_two h) k) := by
  obtain rfl : n / 3 = q := by omega
  rw [adaptedBoundaryLift, dite_eq_right (by omega), dite_eq_right (by omega)]
  simp

include hv' hw' hu' in
private theorem adaptedBoundaryLift_spec (n : ℤ) (k : Fin (rank α β γ n)) :
    ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).d (n + 1) n).hom
      (adaptedBoundaryLift v' w' u' n k) = adaptedBoundaryBasis u v w n k := by
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, n = 3 * q ∨ n = 3 * q + 1 ∨ n = 3 * q + 2 := ⟨n / 3, by omega⟩
  · apply (XIso₃ hfg hgδ hδf n q hq).toLinearEquiv.injective
    rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, coe_adaptedBoundaryBasis₃ u v w hq,
      interleave_d_eq_of_eq_three_mul hfg hgδ hδf hq]
    simp [XIso₂_adaptedBoundaryLift v' w' u' hq, hw']
  · apply (XIso₂ hfg hgδ hδf n q hq).toLinearEquiv.injective
    rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, coe_adaptedBoundaryBasis₂ u v w hq,
      interleave_d_eq_of_eq_three_mul_add_one hfg hgδ hδf hq]
    simp [XIso₁_adaptedBoundaryLift v' w' u' hq, hv']
  · apply (XIso₁ hfg hgδ hδf n q hq).toLinearEquiv.injective
    rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, coe_adaptedBoundaryBasis₁ u v w hq,
      interleave_d_eq_of_eq_three_mul_add_two hfg hgδ hδf hq]
    simp [XIso₃_adaptedBoundaryLift v' w' u' hq, hu']

include b₁ b₂ b₃ u v w in
private theorem acyclic_of_rank_eq_add
    (hm₁ : ∀ q, m₁ q = α q + β q)
    (hm₂ : ∀ q, m₂ q = β q + γ q)
    (hm₃ : ∀ q, m₃ (q + 1) = γ (q + 1) + α q) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic := by
  intro n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : Module.Finite F ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X (m + 1)) :=
    .of_basis (basis hfg hgδ hδf b₁ b₂ b₃ (m + 1))
  rw [HomologicalComplex.exactAt_iff_finrank_add_finrank _ (i := m + 1 + 1) (k := m)
      (by simp) (by simp),
    finrank_eq_card_basis (adaptedBoundaryBasis u v w (m + 1)),
    finrank_eq_card_basis (adaptedBoundaryBasis u v w m),
    finrank_eq_card_basis (basis hfg hgδ hδf b₁ b₂ b₃ (m + 1))]
  simp only [Fintype.card_fin]
  obtain ⟨q, rfl | rfl | rfl⟩ : ∃ q, m = 3 * q ∨ m = 3 * q + 1 ∨ m = 3 * q + 2 :=
    ⟨m / 3, by omega⟩
  · rw [rank_of_eq_three_mul_add_one rfl, rank_of_eq_three_mul rfl,
      rank_of_eq_three_mul_add_one rfl, hm₂ q]
  · have h : 3 * q + 1 + 1 = 3 * q + 2 := by omega
    rw [rank_of_eq_three_mul_add_two h, rank_of_eq_three_mul_add_one rfl,
      rank_of_eq_three_mul_add_two h, hm₁ q]
  · have h : 3 * q + 2 + 1 = 3 * (q + 1) := by omega
    rw [rank_of_eq_three_mul h, rank_of_eq_three_mul_add_two rfl, rank_of_eq_three_mul h, hm₃ q]

private theorem torsionBracket_basis_eq_one
    (hK : (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).Acyclic)
    (hm₁ : ∀ q, m₁ q = α q + β q)
    (hm₂ : ∀ q, m₂ q = β q + γ q)
    (hm₃ : ∀ q, m₃ (q + 1) = γ (q + 1) + α q)
    (hb₁ : ∀ q, ⇑(b₁ q) = Fin.append (fun k ↦ (u q k : X₁ q)) (v' q) ∘ Fin.cast (hm₁ q))
    (hb₂ : ∀ q, ⇑(b₂ q) = Fin.append (fun k ↦ (v q k : X₂ q)) (w' q) ∘ Fin.cast (hm₂ q))
    (hb₃ : ∀ q, ⇑(b₃ (q + 1)) =
      Fin.append (fun k ↦ (w (q + 1) k : X₃ (q + 1))) (u' q) ∘ Fin.cast (hm₃ q))
    (n : ℤ) :
    HomologicalComplex.torsionBracket (basis hfg hgδ hδf b₁ b₂ b₃) (by simp) (by simp)
      (hK (n + 1)) (adaptedBoundaryBasis u v w (n + 1)) (adaptedBoundaryBasis u v w n)
      (adaptedBoundaryLift v' w' u' n) (adaptedBoundaryLift_spec u v w v' hv' w' hw' u' hu' n) =
      1 := by
  have hn := HomologicalComplex.eq_add_of_exactAt (basis hfg hgδ hδf b₁ b₂ b₃) (by simp) (by simp)
    (hK (n + 1)) (adaptedBoundaryBasis u v w (n + 1)) (adaptedBoundaryBasis u v w n)
  rw [HomologicalComplex.torsionBracket_eq_det_append _ _ _ (hK (n + 1)) _ _ _ _ hn,
    ← Basis.det_self (basis hfg hgδ hδf b₁ b₂ b₃ (n + 1))]
  congr 1; ext i
  obtain ⟨m, rfl⟩ := (finCongr hn.symm).surjective i
  rw [Function.comp_apply, show Fin.cast hn (finCongr hn.symm m) = m from Fin.ext (by simp)]
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, n = 3 * q ∨ n = 3 * q + 1 ∨ n = 3 * q + 2 := ⟨n / 3, by omega⟩
  · have hq' : n + 1 = 3 * q + 1 := by omega
    apply (XIso₂ hfg hgδ hδf (n + 1) q hq').toLinearEquiv.injective
    rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, XIso₂_hom_basis hfg hgδ hδf b₁ b₂ b₃ hq',
      hb₂ q, Function.comp_apply, map_append_eq_append_cast _ _ _ (fun k ↦ (v q k : X₂ q)) (w' q)
        (rank_of_eq_three_mul_add_one hq') (rank_of_eq_three_mul hq)
        (coe_adaptedBoundaryBasis₂ (hfg := hfg) (hgδ := hgδ) (hδf := hδf) u v w hq')
        (XIso₂_adaptedBoundaryLift v' w' u' hq)
        (by rw [rank_of_eq_three_mul_add_one hq', rank_of_eq_three_mul hq])]
    congr 1
  · have hq' : n + 1 = 3 * q + 2 := by omega
    apply (XIso₁ hfg hgδ hδf (n + 1) q hq').toLinearEquiv.injective
    rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, XIso₁_hom_basis hfg hgδ hδf b₁ b₂ b₃ hq',
      hb₁ q, Function.comp_apply, map_append_eq_append_cast _ _ _ (fun k ↦ (u q k : X₁ q)) (v' q)
        (rank_of_eq_three_mul_add_two hq') (rank_of_eq_three_mul_add_one hq)
        (coe_adaptedBoundaryBasis₁ (hfg := hfg) (hgδ := hgδ) (hδf := hδf) u v w hq')
        (XIso₁_adaptedBoundaryLift v' w' u' hq)
        (by rw [rank_of_eq_three_mul_add_two hq', rank_of_eq_three_mul_add_one hq])]
    congr 1
  · have hq' : n + 1 = 3 * (q + 1) := by omega
    apply (XIso₃ hfg hgδ hδf (n + 1) (q + 1) hq').toLinearEquiv.injective
    rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, XIso₃_hom_basis hfg hgδ hδf b₁ b₂ b₃ hq',
      hb₃ q, Function.comp_apply,
      map_append_eq_append_cast _ _ _ (fun k ↦ (w (q + 1) k : X₃ (q + 1))) (u' q)
        (rank_of_eq_three_mul hq') (rank_of_eq_three_mul_add_two hq)
        (coe_adaptedBoundaryBasis₃ (hfg := hfg) (hgδ := hgδ) (hδf := hδf) u v w hq')
        (XIso₃_adaptedBoundaryLift v' w' u' hq)
        (by rw [rank_of_eq_three_mul hq', rank_of_eq_three_mul_add_two hq])]
    congr 1

include hv' hw' hu' in
/-- When a bounded interleaved complex is given bases `b₁ q = (u q, v' q)`, `b₂ q = (v q, w' q)`
and `b₃ (q + 1) = (w (q + 1), u' q)` built from bases `u q`, `v q`, `w q` of the images of `δ q`,
`f q`, `g q` and lifts `v' q`, `w' q`, `u' q`, the complex is acyclic and its Reidemeister torsion
is `1`. -/
theorem reidemeisterTorsion_basis_eq_one
    (hr : {n | rank m₁ m₂ m₃ n ≠ 0}.Finite)
    (hm₁ : ∀ q, m₁ q = α q + β q)
    (hm₂ : ∀ q, m₂ q = β q + γ q)
    (hm₃ : ∀ q, m₃ (q + 1) = γ (q + 1) + α q)
    (hb₁ : ∀ q, ⇑(b₁ q) = Fin.append (fun k ↦ (u q k : X₁ q)) (v' q) ∘ Fin.cast (hm₁ q))
    (hb₂ : ∀ q, ⇑(b₂ q) = Fin.append (fun k ↦ (v q k : X₂ q)) (w' q) ∘ Fin.cast (hm₂ q))
    (hb₃ : ∀ q, ⇑(b₃ (q + 1)) =
      Fin.append (fun k ↦ (w (q + 1) k : X₃ (q + 1))) (u' q) ∘ Fin.cast (hm₃ q)) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion (basis hfg hgδ hδf b₁ b₂ b₃) =
      1 := by
  have hK := acyclic_of_rank_eq_add (hfg := hfg) (hgδ := hgδ) (hδf := hδf) b₁ b₂ b₃ u v w
    hm₁ hm₂ hm₃
  rw [HomologicalComplex.reidemeisterTorsion_eq_finprod hr hK (adaptedBoundaryBasis u v w)
    (adaptedBoundaryLift v' w' u') (adaptedBoundaryLift_spec u v w v' hv' w' hw' u' hu')]
  refine finprod_eq_one_of_forall_eq_one fun n ↦ ?_
  rw [torsionBracket_basis_eq_one b₁ b₂ b₃ u v w v' hv' w' hw' u' hu' hK hm₁ hm₂ hm₃ hb₁ hb₂ hb₃,
    one_zpow]

end AdaptedBasis

end ChainComplex.interleave
