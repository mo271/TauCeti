/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Group.Hom.Instances
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
public import TauCeti.RingTheory.Pullback

/-!
# Mayer–Vietoris exactness on algebraic `K₁` for Milnor squares

Given a fibre product `D = π₁.pullback π₂` of possibly noncommutative rings along unital ring
homomorphisms `π₁ : A₁ →+* Q` and `π₂ : A₂ →+* Q` with canonical projections
`p₁ = π₁.pullbackFst π₂` and `p₂ = π₁.pullbackSnd π₂`, functoriality of algebraic `K₁` produces
the sequence of abelian groups

`K₁(D) ⟶ K₁(A₁) × K₁(A₂) ⟶ K₁(Q)`

with maps `f₁ = (K₁(p₁), K₁(p₂))` (`TauCeti.AlgebraicK1.pullbackProdMap`) and
`g₁(x₁, x₂) = K₁(π₁)(x₁) / K₁(π₂)(x₂)` (`TauCeti.AlgebraicK1.pullbackDivMap`).

Unconditionally, `g₁.comp f₁ = 1`. In a **Milnor square** — where `π₁` or `π₂` is surjective —
this sequence is exact at `K₁(A₁) × K₁(A₂)`: `g₁.ker = f₁.range`
(`TauCeti.AlgebraicK1.ker_pullbackDivMap_eq_range_pullbackProdMap`).

The proof operates directly on finite-size invertible matrices without categorical machinery:

1. Square matrices over `π₁.pullback π₂` identify with the fibre product of matrix rings
   (`RingHom.mapMatrixPullbackEquiv`), so compatible pairs `(u₁, u₂) ∈ GL n A₁ × GL n A₂` with
   equal images in `GL n Q` lift to `GL n (π₁.pullback π₂)`
   (`RingHom.generalLinearGroupPullbackLift`) compatibly with stabilization.
2. If `(x₁, x₂) ∈ ker g₁`, choosing finite matrix representatives of `x₁` and `x₂` and stabilizing
   to a common size `n` gives matrices whose images in `GL (Fin n) Q` have equal classes in
   `K₁(Q)`. By `TauCeti.AlgebraicK1.mk_eq_mk_iff`, after stabilizing further to some `N ≥ n`, the
   discrepancy `(π₁(v₁))⁻¹ * π₂(v₂)` lies in `elementarySubgroup (Fin N) Q`.
3. When `π₁` is surjective, `RingHom.exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq` lifts
   this elementary matrix to `e₁ ∈ elementarySubgroup (Fin N) A₁`. Replacing `v₁` by `v₁ * e₁`
   aligns its image in `GL (Fin N) Q` with `π₂(v₂)` without changing its class in `K₁(A₁)`,
   allowing `(v₁ * e₁, v₂)` to lift to `GL (Fin N) (π₁.pullback π₂)`. The case where `π₂` is
   surjective follows by symmetry along `RingHom.pullbackComm`.

## Main definitions

* `RingHom.mapMatrixPullbackEquiv`: ring isomorphism
  `Matrix m m (f.pullback g) ≃+* (f.mapMatrix (m := m)).pullback (g.mapMatrix (m := m))`.
* `RingHom.generalLinearGroupPullbackEquiv`, `RingHom.generalLinearGroupPullbackLift`:
  description of `GL m (f.pullback g)` as compatible pairs in `GL m R × GL m S`.
* `TauCeti.AlgebraicK1.pullbackProdMap`: the map `K₁(π₁.pullback π₂) →* K₁(A₁) × K₁(A₂)`.
* `TauCeti.AlgebraicK1.pullbackDivMap`: the ratio map `(x₁, x₂) ↦ K₁(π₁)(x₁) / K₁(π₂)(x₂)` from
  `K₁(A₁) × K₁(A₂)` to `K₁(Q)`.
* `TauCeti.AlgebraicK1.pullbackKerEquivOfBijectiveRight`,
  `TauCeti.AlgebraicK1.pullbackKerEquivOfBijectiveLeft`: group isomorphism
  `K₁(π₁.pullback π₂) ≃* (pullbackDivMap π₁ π₂).ker` when one leg of the square is bijective.

## Main results

* `TauCeti.AlgebraicK1.pullbackDivMap_comp_pullbackProdMap`: unconditional composite triviality.
* `TauCeti.AlgebraicK1.exists_mk_pullback_of_map_eq`: finite-size matrix alignment in a Milnor
  square.
* `TauCeti.AlgebraicK1.ker_pullbackDivMap_eq_range_pullbackProdMap`,
  `TauCeti.AlgebraicK1.mulExact_pullbackProdMap_pullbackDivMap`: exactness of
  `K₁(π₁.pullback π₂) → K₁(A₁) × K₁(A₂) → K₁(Q)` when `π₁` or `π₂` is surjective.
* `TauCeti.AlgebraicK1.surjective_pullbackProdMap_of_subsingleton`: over a subsingleton corner
  `Q`, `pullbackProdMap π₁ π₂` is surjective.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971),
  §3, Theorem 3.3 (Mayer–Vietoris for `K₁` and `K₀`).
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Theorem 2.6.
-/

public section

open Matrix

/-! ## Matrices and general linear groups over a fibre product -/

namespace RingHom

section Matrices

variable {m R S T : Type*} [Fintype m] [DecidableEq m] [Ring R] [Ring S] [Semiring T]

/-- Square matrices over `f.pullback g` are canonically isomorphic to the fibre product of the
matrix ring homomorphisms `f.mapMatrix` and `g.mapMatrix`. -/
def mapMatrixPullbackEquiv (f : R →+* T) (g : S →+* T) :
    Matrix m m (f.pullback g) ≃+*
      (f.mapMatrix (m := m)).pullback (g.mapMatrix (m := m)) :=
  let φ : Matrix m m (f.pullback g) →+*
      (f.mapMatrix (m := m)).pullback (g.mapMatrix (m := m)) :=
    (f.mapMatrix (m := m)).pullbackLift (g.mapMatrix (m := m))
      ((f.pullbackFst g).mapMatrix (m := m))
      ((f.pullbackSnd g).mapMatrix (m := m))
      (ext fun M ↦ Matrix.ext fun i j ↦ f.pullback_eq g (M i j))
  { φ with
    invFun := fun P ↦ Matrix.of fun i j ↦
      ⟨((f.mapMatrix (m := m)).pullbackFst (g.mapMatrix (m := m)) P i j,
        (f.mapMatrix (m := m)).pullbackSnd (g.mapMatrix (m := m)) P i j),
        by simpa using congrFun (congrFun
          ((f.mapMatrix (m := m)).pullback_eq (g.mapMatrix (m := m)) P) i) j⟩
    left_inv := fun M ↦ Matrix.ext fun i j ↦ pullback_ext
      (by simp [φ, pullbackFst_apply])
      (by simp [φ, pullbackSnd_apply])
    right_inv := fun P ↦ pullback_ext
      (by
        simp only [φ]
        ext i j
        simp [pullbackFst_apply])
      (by
        simp only [φ]
        ext i j
        simp [pullbackSnd_apply]) }

/-- First matrix projection of `mapMatrixPullbackEquiv`. -/
@[simp]
theorem pullbackFst_mapMatrixPullbackEquiv_apply (f : R →+* T) (g : S →+* T)
    (M : Matrix m m (f.pullback g)) :
    (f.mapMatrix (m := m)).pullbackFst (g.mapMatrix (m := m)) (f.mapMatrixPullbackEquiv g M) =
      (f.pullbackFst g).mapMatrix M := by
  simp [mapMatrixPullbackEquiv]

/-- Second matrix projection of `mapMatrixPullbackEquiv`. -/
@[simp]
theorem pullbackSnd_mapMatrixPullbackEquiv_apply (f : R →+* T) (g : S →+* T)
    (M : Matrix m m (f.pullback g)) :
    (f.mapMatrix (m := m)).pullbackSnd (g.mapMatrix (m := m)) (f.mapMatrixPullbackEquiv g M) =
      (f.pullbackSnd g).mapMatrix M := by
  simp [mapMatrixPullbackEquiv]

/-- Entrywise first projection of `(mapMatrixPullbackEquiv).symm`. -/
theorem mapMatrix_pullbackFst_mapMatrixPullbackEquiv_symm_apply (f : R →+* T) (g : S →+* T)
    (P : (f.mapMatrix (m := m)).pullback (g.mapMatrix (m := m))) :
    (f.pullbackFst g).mapMatrix ((f.mapMatrixPullbackEquiv g).symm P) =
      (f.mapMatrix (m := m)).pullbackFst (g.mapMatrix (m := m)) P := by
  ext i j
  simp [mapMatrixPullbackEquiv, pullbackFst_apply]

/-- Entrywise second projection of `(mapMatrixPullbackEquiv).symm`. -/
theorem mapMatrix_pullbackSnd_mapMatrixPullbackEquiv_symm_apply (f : R →+* T) (g : S →+* T)
    (P : (f.mapMatrix (m := m)).pullback (g.mapMatrix (m := m))) :
    (f.pullbackSnd g).mapMatrix ((f.mapMatrixPullbackEquiv g).symm P) =
      (f.mapMatrix (m := m)).pullbackSnd (g.mapMatrix (m := m)) P := by
  ext i j
  simp [mapMatrixPullbackEquiv, pullbackSnd_apply]

/-- `GL m (f.pullback g)` is canonically isomorphic to the subgroup of pairs
`(u, v) ∈ GL m R × GL m S` whose images in `GL m T` agree. -/
def generalLinearGroupPullbackEquiv (f : R →+* T) (g : S →+* T) :
    GL m (f.pullback g) ≃*
      ((Units.map (f.mapMatrix (m := m) : Matrix m m R →* Matrix m m T)).comp
          (MonoidHom.fst (GL m R) (GL m S))).eqLocus
        ((Units.map (g.mapMatrix (m := m) : Matrix m m S →* Matrix m m T)).comp
          (MonoidHom.snd (GL m R) (GL m S))) :=
  (Units.mapEquiv (f.mapMatrixPullbackEquiv g).toMulEquiv).trans
    ((f.mapMatrix (m := m)).pullbackUnitsEquiv (g.mapMatrix (m := m)))

/-- Underlying pair of invertible matrices associated to `w : GL m (f.pullback g)`. -/
@[simp]
theorem coe_generalLinearGroupPullbackEquiv_apply (f : R →+* T) (g : S →+* T)
    (w : GL m (f.pullback g)) :
    ((f.generalLinearGroupPullbackEquiv g w :
      ((Units.map (f.mapMatrix (m := m) : Matrix m m R →* Matrix m m T)).comp
          (MonoidHom.fst (GL m R) (GL m S))).eqLocus
        ((Units.map (g.mapMatrix (m := m) : Matrix m m S →* Matrix m m T)).comp
          (MonoidHom.snd (GL m R) (GL m S)))) : GL m R × GL m S) =
      (Units.map ((f.pullbackFst g).mapMatrix (m := m) :
          Matrix m m (f.pullback g) →* Matrix m m R) w,
        Units.map ((f.pullbackSnd g).mapMatrix (m := m) :
          Matrix m m (f.pullback g) →* Matrix m m S) w) := by
  simp only [generalLinearGroupPullbackEquiv, MulEquiv.trans_apply, coe_pullbackUnitsEquiv_apply]
  exact Prod.ext (Units.ext (by simp)) (Units.ext (by simp))

/-- A compatible pair of invertible matrices `(u, v) ∈ GL m R × GL m S` with equal images in
`GL m T` lifts to an invertible matrix over `f.pullback g`. -/
def generalLinearGroupPullbackLift (f : R →+* T) (g : S →+* T) (u : GL m R) (v : GL m S)
    (h : Units.map (f.mapMatrix (m := m) : Matrix m m R →* Matrix m m T) u =
      Units.map (g.mapMatrix (m := m) : Matrix m m S →* Matrix m m T) v) :
    GL m (f.pullback g) :=
  (f.generalLinearGroupPullbackEquiv g).symm ⟨(u, v), h⟩

/-- Mapping `generalLinearGroupPullbackLift` along `pullbackFst` recovers `u`. -/
@[simp]
theorem unitsMap_pullbackFst_generalLinearGroupPullbackLift (f : R →+* T) (g : S →+* T)
    (u : GL m R) (v : GL m S)
    (h : Units.map (f.mapMatrix (m := m) : Matrix m m R →* Matrix m m T) u =
      Units.map (g.mapMatrix (m := m) : Matrix m m S →* Matrix m m T) v) :
    Units.map ((f.pullbackFst g).mapMatrix (m := m) :
        Matrix m m (f.pullback g) →* Matrix m m R)
      (f.generalLinearGroupPullbackLift g u v h) = u := by
  have := congrArg Prod.fst (f.coe_generalLinearGroupPullbackEquiv_apply g
    (f.generalLinearGroupPullbackLift g u v h))
  simpa [generalLinearGroupPullbackLift] using this.symm

/-- Mapping `generalLinearGroupPullbackLift` along `pullbackSnd` recovers `v`. -/
@[simp]
theorem unitsMap_pullbackSnd_generalLinearGroupPullbackLift (f : R →+* T) (g : S →+* T)
    (u : GL m R) (v : GL m S)
    (h : Units.map (f.mapMatrix (m := m) : Matrix m m R →* Matrix m m T) u =
      Units.map (g.mapMatrix (m := m) : Matrix m m S →* Matrix m m T) v) :
    Units.map ((f.pullbackSnd g).mapMatrix (m := m) :
        Matrix m m (f.pullback g) →* Matrix m m S)
      (f.generalLinearGroupPullbackLift g u v h) = v := by
  have := congrArg Prod.snd (f.coe_generalLinearGroupPullbackEquiv_apply g
    (f.generalLinearGroupPullbackLift g u v h))
  simpa [generalLinearGroupPullbackLift] using this.symm

end Matrices

section Stabilization

variable {R S T : Type*} [Ring R] [Ring S] [Ring T]

/-- Stabilization `u ↦ u ⊕ 1` commutes with `generalLinearGroupPullbackLift`. -/
theorem stabilizeGL_generalLinearGroupPullbackLift {k n : ℕ} (hkn : k ≤ n)
    (f : R →+* T) (g : S →+* T) (u : GL (Fin k) R) (v : GL (Fin k) S)
    (h : Units.map (f.mapMatrix (m := Fin k) : Matrix (Fin k) (Fin k) R →*
        Matrix (Fin k) (Fin k) T) u =
      Units.map (g.mapMatrix (m := Fin k) : Matrix (Fin k) (Fin k) S →*
        Matrix (Fin k) (Fin k) T) v) :
    TauCeti.stabilizeGL (f.pullback g) hkn (f.generalLinearGroupPullbackLift g u v h) =
      f.generalLinearGroupPullbackLift g (TauCeti.stabilizeGL R hkn u)
        (TauCeti.stabilizeGL S hkn v) (by
          have hu := (TauCeti.stabilizeGL_map hkn f u).symm
          have hv := (TauCeti.stabilizeGL_map hkn g v).symm
          simp only [RingHom.toMonoidHom_eq_coe] at hu hv
          rw [hu, hv, h]) := by
  apply (f.generalLinearGroupPullbackEquiv (m := Fin n) g).injective
  apply Subtype.ext
  have h₁ := (TauCeti.stabilizeGL_map hkn (f.pullbackFst g)
    (f.generalLinearGroupPullbackLift g u v h)).symm
  have h₂ := (TauCeti.stabilizeGL_map hkn (f.pullbackSnd g)
    (f.generalLinearGroupPullbackLift g u v h)).symm
  simp only [RingHom.toMonoidHom_eq_coe,
    f.unitsMap_pullbackFst_generalLinearGroupPullbackLift g u v h,
    f.unitsMap_pullbackSnd_generalLinearGroupPullbackLift g u v h] at h₁ h₂
  simp [h₁, h₂]

end Stabilization

end RingHom

/-! ## Mayer–Vietoris exactness for algebraic `K₁` -/

namespace TauCeti.AlgebraicK1

section Maps

variable {A₁ A₂ Q : Type*} [Ring A₁] [Ring A₂] [Ring Q]

/-- The pair homomorphism `K₁(π₁.pullback π₂) →* K₁(A₁) × K₁(A₂)` induced by the two projections
`π₁.pullbackFst π₂` and `π₁.pullbackSnd π₂`. -/
@[expose]
noncomputable def pullbackProdMap (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q) :
    AlgebraicK1 (π₁.pullback π₂) →* AlgebraicK1 A₁ × AlgebraicK1 A₂ :=
  (map (π₁.pullbackFst π₂)).prod (map (π₁.pullbackSnd π₂))

/-- Evaluation of `pullbackProdMap` on an element `x`. -/
theorem pullbackProdMap_apply (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    (x : AlgebraicK1 (π₁.pullback π₂)) :
    pullbackProdMap π₁ π₂ x = (map (π₁.pullbackFst π₂) x, map (π₁.pullbackSnd π₂) x) :=
  rfl

/-- First coordinate of `pullbackProdMap`. -/
@[simp]
theorem fst_pullbackProdMap (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q) (x : AlgebraicK1 (π₁.pullback π₂)) :
    (pullbackProdMap π₁ π₂ x).1 = map (π₁.pullbackFst π₂) x :=
  rfl

/-- Second coordinate of `pullbackProdMap`. -/
@[simp]
theorem snd_pullbackProdMap (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q) (x : AlgebraicK1 (π₁.pullback π₂)) :
    (pullbackProdMap π₁ π₂ x).2 = map (π₁.pullbackSnd π₂) x :=
  rfl

/-- The ratio homomorphism `K₁(A₁) × K₁(A₂) →* K₁(Q)` sending `(x₁, x₂)` to
`K₁(π₁)(x₁) / K₁(π₂)(x₂)`. -/
@[expose]
noncomputable def pullbackDivMap (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q) :
    AlgebraicK1 A₁ × AlgebraicK1 A₂ →* AlgebraicK1 Q :=
  (map π₁).comp (MonoidHom.fst (AlgebraicK1 A₁) (AlgebraicK1 A₂)) /
    (map π₂).comp (MonoidHom.snd (AlgebraicK1 A₁) (AlgebraicK1 A₂))

/-- Evaluation of `pullbackDivMap` on a pair `(x₁, x₂)`. -/
@[simp]
theorem pullbackDivMap_apply (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    (p : AlgebraicK1 A₁ × AlgebraicK1 A₂) :
    pullbackDivMap π₁ π₂ p = map π₁ p.1 / map π₂ p.2 :=
  rfl

/-- Membership in `ker (pullbackDivMap π₁ π₂)` means that `x₁` and `x₂` have the same image in
`K₁(Q)`. -/
theorem mem_ker_pullbackDivMap_iff (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    {p : AlgebraicK1 A₁ × AlgebraicK1 A₂} :
    p ∈ (pullbackDivMap π₁ π₂).ker ↔ map π₁ p.1 = map π₂ p.2 := by
  rw [MonoidHom.mem_ker, pullbackDivMap_apply, div_eq_one]

/-- Unconditionally (without surjectivity of either leg), the composite
`K₁(π₁.pullback π₂) → K₁(A₁) × K₁(A₂) → K₁(Q)` is trivial. -/
@[simp]
theorem pullbackDivMap_comp_pullbackProdMap (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q) :
    (pullbackDivMap π₁ π₂).comp (pullbackProdMap π₁ π₂) = 1 :=
  MonoidHom.ext fun x ↦ by simp [map_map, π₁.pullback_comm_sq π₂]

/-- Unconditionally, the image of `pullbackProdMap` is contained in the kernel of
`pullbackDivMap`. -/
theorem range_pullbackProdMap_le_ker_pullbackDivMap (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q) :
    (pullbackProdMap π₁ π₂).range ≤ (pullbackDivMap π₁ π₂).ker := by
  rintro _ ⟨x, rfl⟩
  exact MonoidHom.mem_ker.2 congr($(pullbackDivMap_comp_pullbackProdMap π₁ π₂) x)

/-- `pullbackProdMap` intertwines `RingHom.pullbackComm` with `Prod.swap`. -/
theorem pullbackProdMap_map_pullbackComm (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    (x : AlgebraicK1 (π₁.pullback π₂)) :
    pullbackProdMap π₂ π₁ (map (π₁.pullbackComm π₂).toRingHom x) =
      (pullbackProdMap π₁ π₂ x).swap := by
  ext <;> simp [map_map]

/-- Swapping the two factors inverts `pullbackDivMap`. -/
theorem pullbackDivMap_swap (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    (p : AlgebraicK1 A₁ × AlgebraicK1 A₂) :
    pullbackDivMap π₂ π₁ p.swap = (pullbackDivMap π₁ π₂ p)⁻¹ := by
  simp [inv_div]

/-- Naturality of `pullbackProdMap` with respect to morphisms of cospans (`RingHom.pullbackMap`). -/
theorem pullbackProdMap_map_pullbackMap {B₁ B₂ Q' : Type*} [Ring B₁] [Ring B₂] [Ring Q']
    (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q) (ρ₁ : B₁ →+* Q') (ρ₂ : B₂ →+* Q')
    (α : A₁ →+* B₁) (β : A₂ →+* B₂) (γ : Q →+* Q')
    (h₁ : ρ₁.comp α = γ.comp π₁) (h₂ : ρ₂.comp β = γ.comp π₂)
    (x : AlgebraicK1 (π₁.pullback π₂)) :
    pullbackProdMap ρ₁ ρ₂ (map (π₁.pullbackMap π₂ ρ₁ ρ₂ α β γ h₁ h₂) x) =
      (map α (pullbackProdMap π₁ π₂ x).1, map β (pullbackProdMap π₁ π₂ x).2) := by
  ext <;> simp [map_map]

/-- Naturality of `pullbackDivMap` with respect to morphisms of cospans. -/
theorem map_pullbackDivMap {B₁ B₂ Q' : Type*} [Ring B₁] [Ring B₂] [Ring Q']
    (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q) (ρ₁ : B₁ →+* Q') (ρ₂ : B₂ →+* Q')
    (α : A₁ →+* B₁) (β : A₂ →+* B₂) (γ : Q →+* Q')
    (h₁ : ρ₁.comp α = γ.comp π₁) (h₂ : ρ₂.comp β = γ.comp π₂)
    (p : AlgebraicK1 A₁ × AlgebraicK1 A₂) :
    map γ (pullbackDivMap π₁ π₂ p) = pullbackDivMap ρ₁ ρ₂ (map α p.1, map β p.2) := by
  simp [map_div, map_map, h₁, h₂]

end Maps

section Exactness

variable {A₁ A₂ Q : Type*} [Ring A₁] [Ring A₂] [Ring Q]

/-- Auxiliary alignment lemma when the left leg `π₁` is surjective: finite matrix representatives
with equal `K₁(Q)` classes lift after stabilization and an elementary modification on `A₁` to a
single invertible matrix over `π₁.pullback π₂`. -/
private theorem exists_mk_pullback_of_surjective_left {π₁ : A₁ →+* Q} {π₂ : A₂ →+* Q}
    (hπ₁ : Function.Surjective π₁) {m k : ℕ} (u₁ : GL (Fin m) A₁) (u₂ : GL (Fin k) A₂)
    (h : map π₁ (mk A₁ m u₁) = map π₂ (mk A₂ k u₂)) :
    ∃ N : ℕ, ∃ w : GL (Fin N) (π₁.pullback π₂),
      map (π₁.pullbackFst π₂) (mk (π₁.pullback π₂) N w) = mk A₁ m u₁ ∧
        map (π₁.pullbackSnd π₂) (mk (π₁.pullback π₂) N w) = mk A₂ k u₂ := by
  set n := max m k
  have hm : m ≤ n := le_max_left m k
  have hk : k ≤ n := le_max_right m k
  set u₁' := stabilizeGL A₁ hm u₁
  set u₂' := stabilizeGL A₂ hk u₂
  have hQ : mk Q n (Units.map (π₁.mapMatrix (m := Fin n)).toMonoidHom u₁') =
      mk Q n (Units.map (π₂.mapMatrix (m := Fin n)).toMonoidHom u₂') := by
    rw [← map_mk, ← map_mk, mk_stabilizeGL, mk_stabilizeGL, h]
  obtain ⟨N, hn, heQ⟩ := mk_eq_mk_iff.1 hQ
  set v₁ := stabilizeGL A₁ hn u₁'
  set v₂ := stabilizeGL A₂ hn u₂'
  have hdiscr : (Units.map (π₁.mapMatrix (m := Fin N)).toMonoidHom v₁)⁻¹ *
      Units.map (π₂.mapMatrix (m := Fin N)).toMonoidHom v₂ ∈
        elementarySubgroup (Fin N) Q := by
    simpa only [v₁, v₂, ← stabilizeGL_map, map_mul, map_inv] using heQ
  obtain ⟨e₁, he₁, he₁_eq⟩ :=
    π₁.exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq hπ₁ hdiscr
  have hcompat : Units.map (π₁.mapMatrix (m := Fin N) :
        Matrix (Fin N) (Fin N) A₁ →* Matrix (Fin N) (Fin N) Q) (v₁ * e₁) =
      Units.map (π₂.mapMatrix (m := Fin N) :
        Matrix (Fin N) (Fin N) A₂ →* Matrix (Fin N) (Fin N) Q) v₂ := by
    simp only [RingHom.toMonoidHom_eq_coe] at he₁_eq
    rw [map_mul, he₁_eq, mul_inv_cancel_left]
  refine ⟨N, π₁.generalLinearGroupPullbackLift π₂ (v₁ * e₁) v₂ hcompat, ?_, ?_⟩
  · have he₁_one : mk A₁ N e₁ = 1 := mk_eq_one_iff.2 ⟨N, le_rfl, by simpa using he₁⟩
    rw [map_mk, RingHom.toMonoidHom_eq_coe,
      π₁.unitsMap_pullbackFst_generalLinearGroupPullbackLift, map_mul, he₁_one, mul_one]
    simp [v₁, u₁']
  · rw [map_mk, RingHom.toMonoidHom_eq_coe,
      π₁.unitsMap_pullbackSnd_generalLinearGroupPullbackLift]
    simp [v₂, u₂']

/-- **Finite-size representative alignment in a Milnor square**: if `u₁ ∈ GL (Fin m) A₁` and
`u₂ ∈ GL (Fin k) A₂` define equal classes in `K₁(Q)` and at least one of `π₁` or `π₂` is
surjective, then some `w ∈ GL (Fin N) (π₁.pullback π₂)` maps to the classes of `u₁` and `u₂` in
`K₁(A₁)` and `K₁(A₂)`. -/
theorem exists_mk_pullback_of_map_eq {π₁ : A₁ →+* Q} {π₂ : A₂ →+* Q}
    (h : Function.Surjective π₁ ∨ Function.Surjective π₂)
    {m k : ℕ} (u₁ : GL (Fin m) A₁) (u₂ : GL (Fin k) A₂)
    (heq : map π₁ (mk A₁ m u₁) = map π₂ (mk A₂ k u₂)) :
    ∃ N : ℕ, ∃ w : GL (Fin N) (π₁.pullback π₂),
      map (π₁.pullbackFst π₂) (mk (π₁.pullback π₂) N w) = mk A₁ m u₁ ∧
        map (π₁.pullbackSnd π₂) (mk (π₁.pullback π₂) N w) = mk A₂ k u₂ := by
  rcases h with hπ₁ | hπ₂
  · exact exists_mk_pullback_of_surjective_left hπ₁ u₁ u₂ heq
  · obtain ⟨N, w, hw₂, hw₁⟩ := exists_mk_pullback_of_surjective_left hπ₂ u₂ u₁ heq.symm
    refine ⟨N, Units.map (((π₂.pullbackComm π₁).toRingHom).mapMatrix (m := Fin N)).toMonoidHom w,
      ?_, ?_⟩
    · rwa [← map_mk, map_map, RingEquiv.toRingHom_eq_coe, π₂.pullbackFst_comp_pullbackComm π₁]
    · rwa [← map_mk, map_map, RingEquiv.toRingHom_eq_coe, π₂.pullbackSnd_comp_pullbackComm π₁]

/-- **Mayer–Vietoris exactness for algebraic `K₁`** in a Milnor square: if `π₁ : A₁ →+* Q` or
`π₂ : A₂ →+* Q` is surjective, then the kernel of `(x₁, x₂) ↦ K₁(π₁)(x₁) / K₁(π₂)(x₂)` on
`K₁(A₁) × K₁(A₂)` equals the image of `K₁(π₁.pullback π₂)`. -/
theorem ker_pullbackDivMap_eq_range_pullbackProdMap (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    (h : Function.Surjective π₁ ∨ Function.Surjective π₂) :
    (pullbackDivMap π₁ π₂).ker = (pullbackProdMap π₁ π₂).range := by
  refine le_antisymm ?_ (range_pullbackProdMap_le_ker_pullbackDivMap π₁ π₂)
  rintro ⟨x₁, x₂⟩ hx
  obtain ⟨m, u₁, rfl⟩ := exists_mk x₁
  obtain ⟨k, u₂, rfl⟩ := exists_mk x₂
  obtain ⟨N, w, hw₁, hw₂⟩ :=
    exists_mk_pullback_of_map_eq h u₁ u₂ ((mem_ker_pullbackDivMap_iff π₁ π₂).1 hx)
  exact ⟨mk (π₁.pullback π₂) N w, Prod.ext hw₁ hw₂⟩

/-- `Function.MulExact` formulation of Mayer–Vietoris exactness at `K₁(A₁) × K₁(A₂)` for a Milnor
square. -/
theorem mulExact_pullbackProdMap_pullbackDivMap (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    (h : Function.Surjective π₁ ∨ Function.Surjective π₂) :
    Function.MulExact (pullbackProdMap π₁ π₂) (pullbackDivMap π₁ π₂) :=
  MonoidHom.mulExact_iff.2 (ker_pullbackDivMap_eq_range_pullbackProdMap π₁ π₂ h)

end Exactness

/-! ## Degenerate corners and bijective legs -/

section Degenerate

variable {A₁ A₂ Q : Type*} [Ring A₁] [Ring A₂] [Ring Q]

/-- Over a subsingleton corner `Q`, `pullbackProdMap π₁ π₂` is surjective onto
`K₁(A₁) × K₁(A₂)`. -/
theorem surjective_pullbackProdMap_of_subsingleton (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    [Subsingleton Q] :
    Function.Surjective (pullbackProdMap π₁ π₂) := by
  have hQ : ∀ y : AlgebraicK1 Q, y = 1 := fun y ↦ by
    obtain ⟨n, u, rfl⟩ := exists_mk y
    have hu : u = 1 := Units.ext (Matrix.ext fun _ _ ↦ Subsingleton.elim _ _)
    rw [hu, map_one]
  rw [← MonoidHom.range_eq_top,
    ← ker_pullbackDivMap_eq_range_pullbackProdMap π₁ π₂ (.inl fun _ ↦ ⟨0, Subsingleton.elim _ _⟩),
    eq_top_iff]
  intro p _
  exact MonoidHom.mem_ker.2 (hQ _)

/-- When `π₂ : A₂ →+* Q` is bijective (for example `π₂ = RingHom.id Q`), `pullbackProdMap π₁ π₂`
is injective. -/
theorem injective_pullbackProdMap_of_bijective_right (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    (hπ₂ : Function.Bijective π₂) :
    Function.Injective (pullbackProdMap π₁ π₂) := by
  let e := π₁.pullbackEquivLeftOfBijective π₂ hπ₂
  intro x y hxy
  have h₁ : map (π₁.pullbackFst π₂) x = map (π₁.pullbackFst π₂) y := congrArg Prod.fst hxy
  have hret : ∀ z, map e.symm.toRingHom (map (π₁.pullbackFst π₂) z) = z := fun z ↦ by
    have hcomp := e.symm_toRingHom_comp_toRingHom
    simp only [RingEquiv.toRingHom_eq_coe, e, π₁.coe_pullbackEquivLeftOfBijective π₂ hπ₂] at hcomp
    rw [map_map]
    simp only [RingEquiv.toRingHom_eq_coe, e, hcomp, map_id, MonoidHom.id_apply]
  rw [← hret x, ← hret y, h₁]

/-- When `π₁ : A₁ →+* Q` is bijective (for example `π₁ = RingHom.id Q`), `pullbackProdMap π₁ π₂`
is injective. -/
theorem injective_pullbackProdMap_of_bijective_left (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    (hπ₁ : Function.Bijective π₁) :
    Function.Injective (pullbackProdMap π₁ π₂) := by
  let e := π₁.pullbackEquivRightOfBijective π₂ hπ₁
  intro x y hxy
  have h₂ : map (π₁.pullbackSnd π₂) x = map (π₁.pullbackSnd π₂) y := congrArg Prod.snd hxy
  have hret : ∀ z, map e.symm.toRingHom (map (π₁.pullbackSnd π₂) z) = z := fun z ↦ by
    have hcomp := e.symm_toRingHom_comp_toRingHom
    simp only [RingEquiv.toRingHom_eq_coe, e, π₁.coe_pullbackEquivRightOfBijective π₂ hπ₁] at hcomp
    rw [map_map]
    simp only [RingEquiv.toRingHom_eq_coe, e, hcomp, map_id, MonoidHom.id_apply]
  rw [← hret x, ← hret y, h₂]

/-- When `π₂ : A₂ →+* Q` is bijective, `pullbackProdMap π₁ π₂` restricts to a group isomorphism
`K₁(π₁.pullback π₂) ≃* (pullbackDivMap π₁ π₂).ker`. -/
noncomputable def pullbackKerEquivOfBijectiveRight (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    (hπ₂ : Function.Bijective π₂) :
    AlgebraicK1 (π₁.pullback π₂) ≃* (pullbackDivMap π₁ π₂).ker :=
  let g := (pullbackProdMap π₁ π₂).codRestrict (pullbackDivMap π₁ π₂).ker fun x ↦
    range_pullbackProdMap_le_ker_pullbackDivMap π₁ π₂ ⟨x, rfl⟩
  have hg : Function.Bijective g :=
    ⟨fun x y hxy ↦ injective_pullbackProdMap_of_bijective_right π₁ π₂ hπ₂
        (congrArg Subtype.val hxy),
      fun ⟨p, hp⟩ ↦ by
        rw [ker_pullbackDivMap_eq_range_pullbackProdMap π₁ π₂ (.inr hπ₂.2)] at hp
        obtain ⟨x, rfl⟩ := hp
        exact ⟨x, rfl⟩⟩
  { toFun := g
    invFun := (Equiv.ofBijective g hg).symm
    left_inv := Equiv.ofBijective_symm_apply_apply g hg
    right_inv := Equiv.ofBijective_apply_symm_apply g hg
    map_mul' := map_mul g }

/-- Underlying pair of `pullbackKerEquivOfBijectiveRight x` is `pullbackProdMap π₁ π₂ x`. -/
@[simp]
theorem coe_pullbackKerEquivOfBijectiveRight_apply (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    (hπ₂ : Function.Bijective π₂) (x : AlgebraicK1 (π₁.pullback π₂)) :
    (pullbackKerEquivOfBijectiveRight π₁ π₂ hπ₂ x : AlgebraicK1 A₁ × AlgebraicK1 A₂) =
      pullbackProdMap π₁ π₂ x := by
  simp [pullbackKerEquivOfBijectiveRight]

/-- When `π₁ : A₁ →+* Q` is bijective, `pullbackProdMap π₁ π₂` restricts to a group isomorphism
`K₁(π₁.pullback π₂) ≃* (pullbackDivMap π₁ π₂).ker`. -/
noncomputable def pullbackKerEquivOfBijectiveLeft (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    (hπ₁ : Function.Bijective π₁) :
    AlgebraicK1 (π₁.pullback π₂) ≃* (pullbackDivMap π₁ π₂).ker :=
  let g := (pullbackProdMap π₁ π₂).codRestrict (pullbackDivMap π₁ π₂).ker fun x ↦
    range_pullbackProdMap_le_ker_pullbackDivMap π₁ π₂ ⟨x, rfl⟩
  have hg : Function.Bijective g :=
    ⟨fun x y hxy ↦ injective_pullbackProdMap_of_bijective_left π₁ π₂ hπ₁
        (congrArg Subtype.val hxy),
      fun ⟨p, hp⟩ ↦ by
        rw [ker_pullbackDivMap_eq_range_pullbackProdMap π₁ π₂ (.inl hπ₁.2)] at hp
        obtain ⟨x, rfl⟩ := hp
        exact ⟨x, rfl⟩⟩
  { toFun := g
    invFun := (Equiv.ofBijective g hg).symm
    left_inv := Equiv.ofBijective_symm_apply_apply g hg
    right_inv := Equiv.ofBijective_apply_symm_apply g hg
    map_mul' := map_mul g }

/-- Underlying pair of `pullbackKerEquivOfBijectiveLeft x` is `pullbackProdMap π₁ π₂ x`. -/
@[simp]
theorem coe_pullbackKerEquivOfBijectiveLeft_apply (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
    (hπ₁ : Function.Bijective π₁) (x : AlgebraicK1 (π₁.pullback π₂)) :
    (pullbackKerEquivOfBijectiveLeft π₁ π₂ hπ₁ x : AlgebraicK1 A₁ × AlgebraicK1 A₂) =
      pullbackProdMap π₁ π₂ x := by
  simp [pullbackKerEquivOfBijectiveLeft]

end Degenerate

end TauCeti.AlgebraicK1
