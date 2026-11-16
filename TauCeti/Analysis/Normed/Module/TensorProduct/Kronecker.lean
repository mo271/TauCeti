/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import TauCeti.Analysis.Normed.Module.TensorProduct.Associator
public import TauCeti.Analysis.Normed.Module.TensorProduct.Map
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Kronecker

/-!
# Equivalence between Kronecker coordinates and tensor products of finite coordinate spaces

For natural numbers `m` and `n` and a commutative semiring `R`, the finite coordinate space
`Fin (m * n) → R` with pair `(i, j)` indexed by `finProdFinEquiv (i, j)` is canonically `R`-linearly
equivalent to `(Fin m → R) ⊗[R] (Fin n → R)` (`TauCeti.kroneckerTensorEquiv`). Its inverse sends a
pure tensor `u ⊗ₜ[R] w` to the array `k ↦ u i * w j` at `k = finProdFinEquiv (i, j)`, while the
forward map sends the standard basis vector `Pi.single (finProdFinEquiv (i, j)) c` to
`c • (Pi.single i 1 ⊗ₜ[R] Pi.single j 1)`.

This equivalence intertwines `ContinuousLinearMap.kronecker` with `TensorProduct.map` and matches
the Kronecker coherence isomorphisms (`ContinuousLinearEquiv.kroneckerComm`,
`ContinuousLinearEquiv.kroneckerAssoc`, `ContinuousLinearEquiv.kroneckerLid`, and
`ContinuousLinearEquiv.kroneckerRid`) with `TensorProduct.comm`, `TensorProduct.assoc`,
`TensorProduct.lid`, and `TensorProduct.rid`.

Over any nontrivially normed field `𝕜` (without assuming completeness of `𝕜`), equipping the tensor
product with the projective norm upgrades `kroneckerTensorEquiv` to a continuous linear equivalence
`TauCeti.ProjectiveTensor.kroneckerEquiv 𝕜 m n :
(Fin (m * n) → 𝕜) ≃L[𝕜] ProjectiveTensor 𝕜 (Fin m → 𝕜) (Fin n → 𝕜)` that intertwines
`ContinuousLinearMap.kronecker` with `ProjectiveTensor.mapL` and the Kronecker coherences with
`ProjectiveTensor.comm`, `ProjectiveTensor.assoc`, `ProjectiveTensor.lid`, and
`ProjectiveTensor.rid`.

The algebraic equivalence is assembled from Mathlib's `LinearEquiv.piCongrLeft`,
`LinearEquiv.piCurry`, `TensorProduct.piScalarRight`, and `TensorProduct.comm`.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, §2.1.
-/

public section

open scoped TensorProduct

namespace TauCeti

section Algebraic

variable (R : Type*) [CommSemiring R]

/-- Canonical `R`-linear equivalence between Kronecker coordinates `Fin (m * n) → R` (with pair
`(i, j)` stored at `finProdFinEquiv (i, j)`) and `(Fin m → R) ⊗[R] (Fin n → R)`. -/
noncomputable def kroneckerTensorEquiv (m n : ℕ) :
    (Fin (m * n) → R) ≃ₗ[R] (Fin m → R) ⊗[R] (Fin n → R) :=
  (LinearEquiv.piCongrLeft R (fun _ ↦ R)
      ((Equiv.sigmaEquivProd (Fin m) (Fin n)).trans finProdFinEquiv)).symm.trans <|
    (LinearEquiv.piCurry R (fun _ : Fin m ↦ fun _ : Fin n ↦ R)).trans <|
      (TensorProduct.piScalarRight R R (Fin n → R) (Fin m)).symm.trans
        (TensorProduct.comm R (Fin n → R) (Fin m → R))

variable {R} {m n p m' n' : ℕ}

/-- The inverse of `kroneckerTensorEquiv` evaluates a pure tensor `u ⊗ₜ w` at
`finProdFinEquiv (i, j)` to `u i * w j`. -/
@[simp]
theorem kroneckerTensorEquiv_symm_tmul_apply (u : Fin m → R) (w : Fin n → R)
    (i : Fin m) (j : Fin n) :
    (kroneckerTensorEquiv R m n).symm (u ⊗ₜ[R] w) (finProdFinEquiv (i, j)) = u i * w j := by
  simp [kroneckerTensorEquiv, LinearEquiv.piCongrLeft, Sigma.uncurry]

/-- On a pure tensor `u ⊗ₜ w`, `(kroneckerTensorEquiv R m n).symm` is the coordinate array
`k ↦ u (finProdFinEquiv.symm k).1 * w (finProdFinEquiv.symm k).2`. -/
theorem kroneckerTensorEquiv_symm_tmul (u : Fin m → R) (w : Fin n → R) :
    (kroneckerTensorEquiv R m n).symm (u ⊗ₜ[R] w) =
      fun k ↦ u (finProdFinEquiv.symm k).1 * w (finProdFinEquiv.symm k).2 := by
  ext k
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp

/-- `kroneckerTensorEquiv` sends the standard basis vector at `finProdFinEquiv (i, j)` with
coefficient `c` to `c • (Pi.single i 1 ⊗ₜ Pi.single j 1)`. -/
@[simp]
theorem kroneckerTensorEquiv_single (i : Fin m) (j : Fin n) (c : R) :
    kroneckerTensorEquiv R m n (Pi.single (finProdFinEquiv (i, j)) c) =
      c • (Pi.single i 1 ⊗ₜ[R] Pi.single j 1) := by
  apply (kroneckerTensorEquiv R m n).symm.injective
  ext k
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [LinearEquiv.symm_apply_apply, map_smul, Pi.smul_apply,
    kroneckerTensorEquiv_symm_tmul_apply, smul_eq_mul]
  by_cases hi : i' = i <;> by_cases hj : j' = j <;> simp [hi, hj]

/-- Explicit basis expansion of `kroneckerTensorEquiv` on an arbitrary coordinate vector. -/
theorem kroneckerTensorEquiv_apply (v : Fin (m * n) → R) :
    kroneckerTensorEquiv R m n v =
      ∑ i : Fin m, ∑ j : Fin n,
        v (finProdFinEquiv (i, j)) • (Pi.single i 1 ⊗ₜ[R] Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v, map_sum]
  rw [← finProdFinEquiv.sum_comp]
  simp [Fintype.sum_prod_type]

section Operators

open ContinuousLinearEquiv ContinuousLinearMap

variable [TopologicalSpace R]

/-- The inverse of `kroneckerTensorEquiv` intertwines `TensorProduct.map` with
`ContinuousLinearMap.kronecker`. -/
@[simp]
theorem kroneckerTensorEquiv_symm_map
    (f : (Fin m → R) →L[R] (Fin m' → R)) (g : (Fin n → R) →L[R] (Fin n' → R))
    (t : (Fin m → R) ⊗[R] (Fin n → R)) :
    (kroneckerTensorEquiv R m' n').symm (TensorProduct.map f.toLinearMap g.toLinearMap t) =
      f.kronecker g ((kroneckerTensorEquiv R m n).symm t) := by
  induction t using TensorProduct.inductionOn with
  | tmul u w =>
      ext k
      obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
      simp only [TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
        kroneckerTensorEquiv_symm_tmul_apply, kronecker_apply]
      have hcol : (fun i' ↦ g (fun j' ↦ u i' * w j') j) = g w j • u := by
        ext i'
        have hrow : (fun j' ↦ u i' * w j') = u i' • w := rfl
        rw [hrow, _root_.map_smul, Pi.smul_apply, smul_eq_mul, mul_comm, Pi.smul_apply, smul_eq_mul]
      rw [hcol, _root_.map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- `kroneckerTensorEquiv` intertwines `ContinuousLinearMap.kronecker` with `TensorProduct.map`. -/
@[simp]
theorem kroneckerTensorEquiv_kronecker
    (f : (Fin m → R) →L[R] (Fin m' → R)) (g : (Fin n → R) →L[R] (Fin n' → R))
    (v : Fin (m * n) → R) :
    kroneckerTensorEquiv R m' n' (f.kronecker g v) =
      TensorProduct.map f.toLinearMap g.toLinearMap (kroneckerTensorEquiv R m n v) := by
  apply (kroneckerTensorEquiv R m' n').symm.injective
  rw [LinearEquiv.symm_apply_apply, kroneckerTensorEquiv_symm_map, LinearEquiv.symm_apply_apply]

/-- `kroneckerTensorEquiv` intertwines `kroneckerComm` with `TensorProduct.comm`. -/
@[simp]
theorem kroneckerTensorEquiv_kroneckerComm (v : Fin (m * n) → R) :
    kroneckerTensorEquiv R n m (kroneckerComm R m n v) =
      TensorProduct.comm R (Fin m → R) (Fin n → R) (kroneckerTensorEquiv R m n v) := by
  obtain ⟨t, rfl⟩ := (kroneckerTensorEquiv R m n).symm.surjective v
  rw [LinearEquiv.apply_symm_apply]
  apply (kroneckerTensorEquiv R n m).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.inductionOn with
  | tmul u w =>
      ext k
      obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective k
      simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- Iterated `kroneckerTensorEquiv` intertwines `kroneckerAssoc` with `TensorProduct.assoc`. -/
theorem kroneckerTensorEquiv_kroneckerAssoc (v : Fin (m * n * p) → R) :
    TensorProduct.map LinearMap.id (kroneckerTensorEquiv R n p).toLinearMap
        (kroneckerTensorEquiv R m (n * p) (kroneckerAssoc R m n p v)) =
      TensorProduct.assoc R (Fin m → R) (Fin n → R) (Fin p → R)
        (TensorProduct.map (kroneckerTensorEquiv R m n).toLinearMap LinearMap.id
          (kroneckerTensorEquiv R (m * n) p v)) := by
  rw [← Finset.univ_sum_single v]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  obtain ⟨⟨ij, l⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective ij
  simp [kroneckerAssoc_single]

/-- `kroneckerTensorEquiv` intertwines `kroneckerLid` with `TensorProduct.lid` along evaluation on
`Fin 1`. -/
@[simp]
theorem lid_map_funUnique_kroneckerTensorEquiv (v : Fin (1 * n) → R) :
    TensorProduct.lid R (Fin n → R)
        (TensorProduct.map (LinearEquiv.funUnique (Fin 1) R R).toLinearMap LinearMap.id
          (kroneckerTensorEquiv R 1 n v)) =
      kroneckerLid R n v := by
  obtain ⟨t, rfl⟩ := (kroneckerTensorEquiv R 1 n).symm.surjective v
  rw [LinearEquiv.apply_symm_apply]
  induction t using TensorProduct.inductionOn with
  | tmul u w =>
      ext j
      simp [smul_eq_mul]
  | add x y hx hy => simp [hx, hy]

/-- `kroneckerTensorEquiv` intertwines `kroneckerRid` with `TensorProduct.rid` along evaluation on
`Fin 1`. -/
@[simp]
theorem rid_map_funUnique_kroneckerTensorEquiv (v : Fin (m * 1) → R) :
    TensorProduct.rid R (Fin m → R)
        (TensorProduct.map LinearMap.id (LinearEquiv.funUnique (Fin 1) R R).toLinearMap
          (kroneckerTensorEquiv R m 1 v)) =
      kroneckerRid R m v := by
  obtain ⟨t, rfl⟩ := (kroneckerTensorEquiv R m 1).symm.surjective v
  rw [LinearEquiv.apply_symm_apply]
  induction t using TensorProduct.inductionOn with
  | tmul u w =>
      ext i
      simp [smul_eq_mul, mul_comm]
  | add x y hx hy => simp [hx, hy]

end Operators

end Algebraic

namespace ProjectiveTensor

section Normed

open ContinuousLinearEquiv ContinuousLinearMap

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

/-- Continuous bilinear map `(u, w) ↦ (kroneckerTensorEquiv 𝕜 m n).symm (u ⊗ₜ w)` into Kronecker
coordinates, used to bound the inverse of `ProjectiveTensor.kroneckerEquiv` without completeness of
`𝕜`. -/
private noncomputable def kroneckerMulBilinear (m n : ℕ) :
    (Fin m → 𝕜) →L[𝕜] (Fin n → 𝕜) →L[𝕜] (Fin (m * n) → 𝕜) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜
      (fun u w ↦ (kroneckerTensorEquiv 𝕜 m n).symm (u ⊗ₜ[𝕜] w))
      (fun _ _ _ ↦ by rw [TensorProduct.add_tmul, LinearEquiv.map_add])
      (fun _ _ _ ↦ by rw [← TensorProduct.smul_tmul', LinearEquiv.map_smul])
      (fun _ _ _ ↦ by rw [TensorProduct.tmul_add, LinearEquiv.map_add])
      (fun _ _ _ ↦ by rw [TensorProduct.tmul_smul, LinearEquiv.map_smul]))
    1 fun u w ↦ by
      rw [one_mul]
      refine (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg u) (norm_nonneg w))).2 fun k ↦ ?_
      obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
      simp only [LinearMap.mk₂_apply, kroneckerTensorEquiv_symm_tmul_apply, norm_mul]
      exact mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm w j) (norm_nonneg _) (norm_nonneg u)

/-- Continuous linear equivalence between Kronecker coordinates `Fin (m * n) → 𝕜` and the
projective tensor product `ProjectiveTensor 𝕜 (Fin m → 𝕜) (Fin n → 𝕜)`, requiring no completeness
hypothesis on `𝕜`. -/
noncomputable def kroneckerEquiv (m n : ℕ) :
    (Fin (m * n) → 𝕜) ≃L[𝕜] ProjectiveTensor 𝕜 (Fin m → 𝕜) (Fin n → 𝕜) where
  toLinearEquiv :=
    (kroneckerTensorEquiv 𝕜 m n).trans (linearEquiv 𝕜 (Fin m → 𝕜) (Fin n → 𝕜)).symm
  continuous_toFun := by
    let forwardL : (Fin (m * n) → 𝕜) →L[𝕜] ProjectiveTensor 𝕜 (Fin m → 𝕜) (Fin n → 𝕜) :=
      ∑ i : Fin m, ∑ j : Fin n,
        (tmulL 𝕜 (Fin m → 𝕜) (Fin n → 𝕜) (Pi.single i 1)).comp
          ((ContinuousLinearMap.proj (R := 𝕜) (finProdFinEquiv (i, j))).smulRight (Pi.single j 1))
    refine forwardL.continuous.congr fun v ↦ ProjectiveTensor.ext ?_
    simp [forwardL, kroneckerTensorEquiv_apply]
  continuous_invFun := by
    let invL : ProjectiveTensor 𝕜 (Fin m → 𝕜) (Fin n → 𝕜) →L[𝕜] (Fin (m * n) → 𝕜) :=
      liftIsometry 𝕜 (Fin m → 𝕜) (Fin n → 𝕜) (Fin (m * n) → 𝕜) (kroneckerMulBilinear 𝕜 m n)
    refine invL.continuous.congr fun u ↦ ?_
    simp only [LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, linearEquiv_apply]
    rcases u with ⟨t⟩
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [invL, kroneckerMulBilinear]
    | add x y hx hy => simpa [mk_add, _root_.map_add] using congrArg₂ (· + ·) hx hy

variable {𝕜} {m n p m' n' : ℕ}

/-- The underlying algebraic tensor of `ProjectiveTensor.kroneckerEquiv 𝕜 m n v` is
`kroneckerTensorEquiv 𝕜 m n v`. -/
@[simp]
theorem toTensorProduct_kroneckerEquiv (v : Fin (m * n) → 𝕜) :
    (kroneckerEquiv 𝕜 m n v).toTensorProduct = kroneckerTensorEquiv 𝕜 m n v := by
  simp [kroneckerEquiv]

/-- `ProjectiveTensor.kroneckerEquiv` wraps `kroneckerTensorEquiv` in `ProjectiveTensor.mk`. -/
theorem kroneckerEquiv_apply (v : Fin (m * n) → 𝕜) :
    kroneckerEquiv 𝕜 m n v = ⟨kroneckerTensorEquiv 𝕜 m n v⟩ := by
  simp [kroneckerEquiv]

/-- The inverse of `ProjectiveTensor.kroneckerEquiv` applies `(kroneckerTensorEquiv 𝕜 m n).symm` to
the underlying algebraic tensor. -/
@[simp]
theorem kroneckerEquiv_symm_apply (u : ProjectiveTensor 𝕜 (Fin m → 𝕜) (Fin n → 𝕜)) :
    (kroneckerEquiv 𝕜 m n).symm u = (kroneckerTensorEquiv 𝕜 m n).symm u.toTensorProduct := by
  apply (kroneckerEquiv 𝕜 m n).injective
  exact ProjectiveTensor.ext (by simp)

/-- The inverse of `ProjectiveTensor.kroneckerEquiv` evaluates a pure tensor `⟨u ⊗ₜ w⟩` at
`finProdFinEquiv (i, j)` to `u i * w j`. -/
@[simp]
theorem kroneckerEquiv_symm_tmul_apply (u : Fin m → 𝕜) (w : Fin n → 𝕜) (i : Fin m) (j : Fin n) :
    (kroneckerEquiv 𝕜 m n).symm ⟨u ⊗ₜ[𝕜] w⟩ (finProdFinEquiv (i, j)) = u i * w j := by
  simp

/-- `ProjectiveTensor.kroneckerEquiv` sends the standard basis vector at `finProdFinEquiv (i, j)`
with coefficient `c` to `c • ⟨Pi.single i 1 ⊗ₜ Pi.single j 1⟩`. -/
@[simp]
theorem kroneckerEquiv_single (i : Fin m) (j : Fin n) (c : 𝕜) :
    kroneckerEquiv 𝕜 m n (Pi.single (finProdFinEquiv (i, j)) c) =
      c • ⟨Pi.single i 1 ⊗ₜ[𝕜] Pi.single j 1⟩ :=
  ProjectiveTensor.ext (by simp)

/-- `ProjectiveTensor.kroneckerEquiv` intertwines `ContinuousLinearMap.kronecker` with
`ProjectiveTensor.mapL`. -/
@[simp]
theorem kroneckerEquiv_kronecker
    (f : (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)) (g : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜))
    (v : Fin (m * n) → 𝕜) :
    kroneckerEquiv 𝕜 m' n' (f.kronecker g v) = mapL f g (kroneckerEquiv 𝕜 m n v) :=
  ProjectiveTensor.ext (by simp)

/-- Operator identity intertwining `ContinuousLinearMap.kronecker` with `ProjectiveTensor.mapL`
along `ProjectiveTensor.kroneckerEquiv`. -/
theorem kroneckerEquiv_comp_kronecker
    (f : (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)) (g : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜)) :
    (kroneckerEquiv 𝕜 m' n').toContinuousLinearMap.comp (f.kronecker g) =
      (mapL f g).comp (kroneckerEquiv 𝕜 m n).toContinuousLinearMap :=
  ContinuousLinearMap.ext (kroneckerEquiv_kronecker f g)

/-- The inverse of `ProjectiveTensor.kroneckerEquiv` intertwines `ProjectiveTensor.mapL` with
`ContinuousLinearMap.kronecker`. -/
theorem kroneckerEquiv_symm_mapL
    (f : (Fin m → 𝕜) →L[𝕜] (Fin m' → 𝕜)) (g : (Fin n → 𝕜) →L[𝕜] (Fin n' → 𝕜))
    (u : ProjectiveTensor 𝕜 (Fin m → 𝕜) (Fin n → 𝕜)) :
    (kroneckerEquiv 𝕜 m' n').symm (mapL f g u) =
      f.kronecker g ((kroneckerEquiv 𝕜 m n).symm u) := by
  simp

/-- `ProjectiveTensor.kroneckerEquiv` intertwines `kroneckerComm` with `ProjectiveTensor.comm`. -/
@[simp]
theorem kroneckerEquiv_kroneckerComm (v : Fin (m * n) → 𝕜) :
    kroneckerEquiv 𝕜 n m (kroneckerComm 𝕜 m n v) =
      comm 𝕜 (Fin m → 𝕜) (Fin n → 𝕜) (kroneckerEquiv 𝕜 m n v) :=
  ProjectiveTensor.ext (by simp)

/-- Iterated `ProjectiveTensor.kroneckerEquiv` intertwines `kroneckerAssoc` with
`ProjectiveTensor.assoc`. -/
theorem kroneckerEquiv_kroneckerAssoc (v : Fin (m * n * p) → 𝕜) :
    mapL (ContinuousLinearMap.id 𝕜 (Fin m → 𝕜))
        (kroneckerEquiv 𝕜 n p).toContinuousLinearMap
        (kroneckerEquiv 𝕜 m (n * p) (kroneckerAssoc 𝕜 m n p v)) =
      assoc 𝕜 (Fin m → 𝕜) (Fin n → 𝕜) (Fin p → 𝕜)
        (mapL (kroneckerEquiv 𝕜 m n).toContinuousLinearMap
          (ContinuousLinearMap.id 𝕜 (Fin p → 𝕜))
          (kroneckerEquiv 𝕜 (m * n) p v)) := by
  rw [← Finset.univ_sum_single v]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  obtain ⟨⟨ij, l⟩, rfl⟩ := finProdFinEquiv.surjective k
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective ij
  simp [kroneckerAssoc_single]

/-- `ProjectiveTensor.kroneckerEquiv` intertwines `kroneckerLid` with `ProjectiveTensor.lid` along
evaluation on `Fin 1`. -/
theorem lid_mapL_funUnique_kroneckerEquiv (v : Fin (1 * n) → 𝕜) :
    lid 𝕜 (Fin n → 𝕜)
        (mapL (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).toContinuousLinearMap
          (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜))
          (kroneckerEquiv 𝕜 1 n v)) =
      kroneckerLid 𝕜 n v := by
  simp only [lid_apply, mapL_apply, toTensorProduct_kroneckerEquiv]
  exact lid_map_funUnique_kroneckerTensorEquiv v

/-- `ProjectiveTensor.kroneckerEquiv` intertwines `kroneckerRid` with `ProjectiveTensor.rid` along
evaluation on `Fin 1`. -/
theorem rid_mapL_funUnique_kroneckerEquiv (v : Fin (m * 1) → 𝕜) :
    rid 𝕜 (Fin m → 𝕜)
        (mapL (ContinuousLinearMap.id 𝕜 (Fin m → 𝕜))
          (ContinuousLinearEquiv.funUnique (Fin 1) 𝕜 𝕜).toContinuousLinearMap
          (kroneckerEquiv 𝕜 m 1 v)) =
      kroneckerRid 𝕜 m v := by
  simp only [rid_apply, mapL_apply, toTensorProduct_kroneckerEquiv]
  exact rid_map_funUnique_kroneckerTensorEquiv v

end Normed

end ProjectiveTensor

end TauCeti
