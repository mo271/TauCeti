/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# Right Hopf modules and the fundamental theorem

Let `H` be a bialgebra over a commutative semiring `R`. A **right `H`-Hopf module** is an
`R`-module `M` carrying both a right `H`-coaction `coact : M →ₗ[R] M ⊗[R] H` and a right
`H`-action `act : M →ₗ[R] H →ₗ[R] M` such that the coaction is equivariant for the diagonal
right action of the coproduct:

```text
coact (m ◁ h) = ∑ (m₀ ◁ h₁) ⊗ (m₁ * h₂).
```

This compatibility is stated without choosing a representation of the coproduct, through
`TensorProduct.map₂` applied to the action and multiplication. Every `R`-module `N` generates a
free right `H`-Hopf module `N ⊗[R] H`, whose coaction is the cofree coaction `Comodule.cofree`
and whose right `H`-action multiplies on the right factor; its coinvariants recover `N`.

When `H` is a Hopf algebra, contracting a coaction with the antipode defines an idempotent
`R`-linear projection `coinvariantProj : M →ₗ[R] M`, `m ↦ ∑ m₀ ◁ S(m₁)`, onto the submodule of
coinvariants `{v ∈ M | coact v = v ⊗ 1}`. The **Fundamental Theorem of Hopf Modules** identifies
every right `H`-Hopf module with the free right `H`-Hopf module on its coinvariants:

```text
μ.coinvariants ⊗[R] H ≃ₗ[R] M,    v ⊗ h ↦ v ◁ h,    m ↦ ∑ P(m₀) ⊗ m₁,
```

intertwining both the right `H`-action and the right `H`-coaction. Over a finite projective Hopf
algebra, applying this decomposition to the linear dual produces the tensor factorization of the
dual in terms of left cointegrals (`TauCeti.Algebra.HopfAlgebra.Cointegral.Finite`).

## Main definitions

* `TauCeti.RightHopfModule`: a right Hopf module over a bialgebra.
* `TauCeti.RightHopfModule.coinvariants`: the submodule of coinvariant vectors `coact v = v ⊗ 1`.
* `TauCeti.RightHopfModule.free`: the free right Hopf module `N ⊗[R] H` on an `R`-module `N`.
* `TauCeti.RightHopfModule.freeCoinvariantsEquiv`: the linear equivalence
  `N ≃ₗ[R] (free R H N).coinvariants`.
* `TauCeti.RightHopfModule.Hom`: morphisms of right Hopf modules, preserving action and coaction.
* `TauCeti.RightHopfModule.coinvariantProj`: the projection `m ↦ ∑ m₀ ◁ S(m₁)` onto coinvariants.
* `TauCeti.RightHopfModule.coinvariantTensorEquiv`: the Fundamental Theorem of Hopf Modules, as an
  `R`-linear equivalence `μ.coinvariants ⊗[R] H ≃ₗ[R] M`.
* `TauCeti.RightHopfModule.coinvariantTensorHom` and
  `TauCeti.RightHopfModule.coinvariantTensorInvHom`: the forward and inverse maps bundled as
  morphisms of right Hopf modules.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. **91** (1969), 75–94, Proposition 1.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, Theorem 4.1.1.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, AMS, 1993, Theorem 1.9.4.
-/

public noncomputable section

open scoped TensorProduct Coalgebra
open TensorProduct

namespace TauCeti

universe u v w x

/-- A right Hopf module over an `R`-bialgebra `H`: a right `H`-comodule equipped with a right
`H`-action whose coaction is equivariant for the diagonal right action of the coproduct. -/
structure RightHopfModule (R : Type u) (H : Type v) (M : Type w) [CommSemiring R]
    [Semiring H] [Bialgebra R H] [AddCommMonoid M] [Module R M] extends Comodule R H M where
  /-- The `R`-bilinear right action of `H` on `M`. -/
  act : M →ₗ[R] H →ₗ[R] M
  /-- The multiplicative identity of `H` acts as the identity on `M`. -/
  act_one : ∀ m, act m 1 = m
  /-- Multiplication in `H` acts as sequential right action on `M`. -/
  act_mul : ∀ m h k, act (act m h) k = act m (h * k)
  /-- Coaction is equivariant for the diagonal right action of the coproduct. -/
  coact_act : ∀ m h,
    coact (act m h) = TensorProduct.map₂ act (LinearMap.mul R H) (coact m) (Coalgebra.comul h)

namespace RightHopfModule

section Bialgebra

variable {R : Type u} {H : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R] [Semiring H] [Bialgebra R H]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

attribute [simp] act_one

/-- Two right Hopf module structures agree when their coactions and right actions agree. -/
@[ext]
theorem ext {μ ν : RightHopfModule R H M} (hcoact : ∀ m, μ.coact m = ν.coact m)
    (hact : ∀ m h, μ.act m h = ν.act m h) : μ = ν := by
  have hc : μ.toComodule = ν.toComodule := Comodule.ext (LinearMap.ext hcoact)
  have ha : μ.act = ν.act := LinearMap.ext₂ hact
  cases μ
  cases ν
  cases hc
  cases ha
  rfl

/-- Scalar multiples of `1 : H` act as the module scalar action of `R`. -/
theorem act_smul_one (μ : RightHopfModule R H M) (m : M) (r : R) :
    μ.act m (r • (1 : H)) = r • m := by
  rw [map_smul, μ.act_one]

/-- Elements in the image of `algebraMap R H` act as scalars from `R`. -/
@[simp]
theorem act_algebraMap (μ : RightHopfModule R H M) (m : M) (r : R) :
    μ.act m (algebraMap R H r) = r • m := by
  rw [Algebra.algebraMap_eq_smul_one, μ.act_smul_one]

/-- The right `H`-action packaged as an algebra homomorphism `Hᵐᵒᵖ →ₐ[R] Module.End R M`. -/
def actionAlgHom (μ : RightHopfModule R H M) : Hᵐᵒᵖ →ₐ[R] Module.End R M :=
  AlgHom.ofLinearMap
    (μ.act.flip.comp (MulOpposite.opLinearEquiv R (M := H)).symm.toLinearMap)
    (LinearMap.ext μ.act_one)
    fun x y ↦ LinearMap.ext fun m ↦ (μ.act_mul m y.unop x.unop).symm

@[simp]
theorem actionAlgHom_apply (μ : RightHopfModule R H M) (h : H) (m : M) :
    μ.actionAlgHom (MulOpposite.op h) m = μ.act m h :=
  (rfl)

/-- The Hopf-module compatibility equation expanded in any finite representation of the
coproduct of `h`. -/
theorem coact_act_eq_sum (μ : RightHopfModule R H M) (m : M) {h : H} {ι : Type*}
    (r : Coalgebra.Repr R h ι) :
    μ.coact (μ.act m h) =
      ∑ i ∈ r.index,
        TensorProduct.map (μ.act.flip (r.left i)) (LinearMap.mulRight R (r.right i))
          (μ.coact m) := by
  rw [μ.coact_act, ← r.eq, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  induction μ.coact m using TensorProduct.inductionOn with
  | tmul m₀ c => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The submodule of coinvariant vectors: those `v : M` satisfying `μ.coact v = v ⊗ₜ 1`. -/
def coinvariants (μ : RightHopfModule R H M) : Submodule R M :=
  letI := μ.toComodule
  (Comodule.fixedSubcomodule R H M).toSubmodule

/-- A vector belongs to `μ.coinvariants` if and only if `μ.coact v = v ⊗ₜ 1`. -/
@[simp]
theorem mem_coinvariants (μ : RightHopfModule R H M) {v : M} :
    v ∈ μ.coinvariants ↔ μ.coact v = v ⊗ₜ[R] (1 : H) := by
  let : Comodule R H M := μ.toComodule
  exact Comodule.mem_fixedSubcomodule

/-- `μ.coinvariants` is the underlying submodule of `Comodule.fixedSubcomodule` for `μ`. -/
theorem coinvariants_eq_fixedSubcomodule (μ : RightHopfModule R H M) :
    (letI := μ.toComodule; (Comodule.fixedSubcomodule R H M).toSubmodule) = μ.coinvariants :=
  (rfl)

/-- Acting on a coinvariant vector `v` by `h` coacts via the coproduct of `h`:
`coact (v ◁ h) = ∑ (v ◁ h₁) ⊗ h₂`. -/
theorem coact_act_of_mem_coinvariants (μ : RightHopfModule R H M) {v : M}
    (hv : v ∈ μ.coinvariants) (h : H) :
    μ.coact (μ.act v h) = (μ.act v).rTensor H (Coalgebra.comul h) := by
  have hmul : LinearMap.mul R H (1 : H) = LinearMap.id := LinearMap.ext one_mul
  rw [μ.coact_act, μ.mem_coinvariants.mp hv, TensorProduct.map₂_apply_tmul, hmul,
    LinearMap.rTensor_def]

/-! ### The free right Hopf module -/

variable (R H N) in
/-- The free right `H`-Hopf module `N ⊗[R] H` on an `R`-module `N`, with the cofree right
coaction `n ⊗ h ↦ ∑ (n ⊗ h₁) ⊗ h₂` and right `H`-action `(n ⊗ h) ◁ k = n ⊗ (h * k)`. -/
def free : RightHopfModule R H (N ⊗[R] H) where
  toComodule := Comodule.cofree R H N
  act := ((LinearMap.lTensorHom N).comp (LinearMap.mul R H).flip).flip
  act_one z := by
    induction z using TensorProduct.inductionOn with
    | tmul n h => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  act_mul z h k := by
    induction z using TensorProduct.inductionOn with
    | tmul n a => simp [mul_assoc]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  coact_act z h := by
    let : Comodule R H (N ⊗[R] H) := Comodule.cofree R H N
    let actN : (N ⊗[R] H) →ₗ[R] H →ₗ[R] (N ⊗[R] H) :=
      ((LinearMap.lTensorHom N).comp (LinearMap.mul R H).flip).flip
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hx hy
    | tmul n a =>
      have ha : actN (n ⊗ₜ[R] a) h = n ⊗ₜ[R] (a * h) := rfl
      rw [ha, Comodule.cofree_coact_tmul, Comodule.cofree_coact_tmul, Bialgebra.comul_mul]
      generalize Coalgebra.comul (R := R) a = u, Coalgebra.comul (R := R) h = v
      induction u using TensorProduct.inductionOn with
      | add x y hx hy =>
        simpa only [add_mul, tmul_add, map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hx hy
      | tmul a₁ a₂ =>
        induction v using TensorProduct.inductionOn with
        | add x y hx hy =>
          simpa only [mul_add, tmul_add, map_add] using congrArg₂ (· + ·) hx hy
        | tmul h₁ h₂ =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, assoc_symm_tmul, map₂_apply_tmul]
          rfl

/-- The comodule underlying `free R H N` is `Comodule.cofree R H N`. -/
@[simp]
theorem free_toComodule : (free R H N).toComodule = Comodule.cofree R H N :=
  (rfl)

/-- Coaction of the free right Hopf module on a pure tensor. -/
@[simp]
theorem free_coact_tmul (n : N) (h : H) :
    (free R H N).coact (n ⊗ₜ[R] h) =
      (TensorProduct.assoc R N H H).symm (n ⊗ₜ[R] Coalgebra.comul h) :=
  Comodule.cofreeCoact_tmul n h

/-- Right `H`-action of the free right Hopf module on a pure tensor. -/
@[simp]
theorem free_act_tmul (n : N) (h k : H) :
    (free R H N).act (n ⊗ₜ[R] h) k = n ⊗ₜ[R] (h * k) :=
  (rfl)

/-- Vectors of the form `n ⊗ₜ 1` are coinvariant in the free right Hopf module `N ⊗[R] H`. -/
theorem tmul_one_mem_free_coinvariants (n : N) :
    n ⊗ₜ[R] (1 : H) ∈ (free R H N).coinvariants := by
  rw [mem_coinvariants, free_coact_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.assoc_symm_tmul]

variable (R H N) in
/-- The coinvariants of the free right `H`-Hopf module `N ⊗[R] H` are canonically isomorphic
to `N`, via `n ↦ n ⊗ₜ 1` and `z ↦ (id ⊗ ε) z`. No antipode is needed. -/
def freeCoinvariantsEquiv : N ≃ₗ[R] (free R H N).coinvariants :=
  LinearEquiv.ofLinearMap
    (((TensorProduct.mk R N H).flip (1 : H)).codRestrict (free R H N).coinvariants
      tmul_one_mem_free_coinvariants)
    (((TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := H)).lTensor N) ∘ₗ
      (free R H N).coinvariants.subtype)
    (by
      ext z
      have hz : Comodule.cofreeCoact R H N (z : N ⊗[R] H) = (z : N ⊗[R] H) ⊗ₜ[R] 1 :=
        (free R H N).mem_coinvariants.mp z.property
      have h := LinearMap.congr_fun
        (Comodule.rTensor_rid_comp_lTensor_counit_comp_cofreeCoact (R := R) (C := H) (M := N))
        (z : N ⊗[R] H)
      rw [LinearMap.comp_apply, hz, LinearMap.rTensor_tmul] at h
      exact h)
    (by
      ext n
      have hsub : (free R H N).coinvariants.subtype
          (((TensorProduct.mk R N H).flip (1 : H)).codRestrict (free R H N).coinvariants
            tmul_one_mem_free_coinvariants n) = n ⊗ₜ[R] (1 : H) := rfl
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hsub, LinearMap.lTensor_tmul,
        Bialgebra.counit_one, rid_tmul, one_smul, LinearMap.id_apply])

@[simp]
theorem coe_freeCoinvariantsEquiv (n : N) :
    (freeCoinvariantsEquiv R H N n : N ⊗[R] H) = n ⊗ₜ[R] (1 : H) :=
  (rfl)

@[simp]
theorem freeCoinvariantsEquiv_symm_apply (z : (free R H N).coinvariants) :
    (freeCoinvariantsEquiv R H N).symm z =
      TensorProduct.rid R N (Coalgebra.counit.lTensor N (z : N ⊗[R] H)) :=
  (rfl)

/-! ### Morphisms of right Hopf modules -/

/-- A morphism of right `H`-Hopf modules: an `R`-linear map commuting with both the right
`H`-coaction and the right `H`-action. -/
structure Hom (μ : RightHopfModule R H M) (ν : RightHopfModule R H N) extends M →ₗ[R] N where
  /-- The map intertwines the coactions. -/
  map_coact' : ∀ m, ν.coact (toLinearMap m) = toLinearMap.rTensor H (μ.coact m)
  /-- The map intertwines the right actions. -/
  map_act' : ∀ m h, toLinearMap (μ.act m h) = ν.act (toLinearMap m) h

namespace Hom

variable {P Q : Type*} [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
variable {μ : RightHopfModule R H M} {ν : RightHopfModule R H N}
variable {ξ : RightHopfModule R H P} {ζ : RightHopfModule R H Q}

instance : FunLike (Hom μ ν) M N where
  coe f := f.toLinearMap
  coe_injective f g h := by
    have hlin : f.toLinearMap = g.toLinearMap := DFunLike.coe_injective h
    cases f
    cases g
    cases hlin
    rfl

instance : LinearMapClass (Hom μ ν) R M N where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

/-- Morphisms of right Hopf modules are determined by their underlying functions. -/
@[ext]
theorem ext {f g : Hom μ ν} (h : ∀ m, f m = g m) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem coe_toLinearMap (f : Hom μ ν) : ⇑f.toLinearMap = f :=
  (rfl)

@[simp]
theorem coe_mk (φ : M →ₗ[R] N) (hc ha) : ⇑(⟨φ, hc, ha⟩ : Hom μ ν) = φ :=
  (rfl)

/-- View a right Hopf module morphism as a morphism of the underlying comodules. -/
def toComoduleHom (f : Hom μ ν) :
    letI := μ.toComodule
    letI := ν.toComodule
    Comodule.Hom R H M N :=
  letI := μ.toComodule
  letI := ν.toComodule
  { toLinearMap := f.toLinearMap
    map_coact := LinearMap.ext fun m ↦ (f.map_coact' m).symm }

@[simp]
theorem map_coact (f : Hom μ ν) (m : M) :
    ν.coact (f m) = f.toLinearMap.rTensor H (μ.coact m) :=
  f.map_coact' m

@[simp]
theorem map_act (f : Hom μ ν) (m : M) (h : H) :
    f (μ.act m h) = ν.act (f m) h :=
  f.map_act' m h

/-- The identity morphism of a right Hopf module. -/
def id (μ : RightHopfModule R H M) : Hom μ μ where
  toLinearMap := LinearMap.id
  map_coact' m := (LinearMap.rTensor_id_apply H M (μ.coact m)).symm
  map_act' _ _ := rfl

/-- Composition of morphisms of right Hopf modules. -/
def comp (g : Hom ν ξ) (f : Hom μ ν) : Hom μ ξ where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  map_coact' m := by
    rw [LinearMap.comp_apply, g.map_coact', f.map_coact', LinearMap.rTensor_comp_apply]
  map_act' m h := by simp

@[simp]
theorem id_apply (μ : RightHopfModule R H M) (m : M) : id μ m = m :=
  (rfl)

@[simp]
theorem comp_apply (g : Hom ν ξ) (f : Hom μ ν) (m : M) : g.comp f m = g (f m) :=
  (rfl)

@[simp]
theorem id_comp (f : Hom μ ν) : (id ν).comp f = f := by
  ext
  rfl

@[simp]
theorem comp_id (f : Hom μ ν) : f.comp (id μ) = f := by
  ext
  rfl

/-- Composition of right Hopf module morphisms is associative. -/
theorem comp_assoc (h : Hom ξ ζ) (g : Hom ν ξ) (f : Hom μ ν) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  rfl

/-- A morphism of right Hopf modules maps coinvariants into coinvariants. -/
theorem map_mem_coinvariants (f : Hom μ ν) {v : M} (hv : v ∈ μ.coinvariants) :
    f v ∈ ν.coinvariants := by
  rw [mem_coinvariants] at hv ⊢
  rw [f.map_coact, hv, LinearMap.rTensor_tmul, coe_toLinearMap]

/-- The linear map induced on coinvariant submodules by a morphism of right Hopf modules. -/
def mapCoinvariants (f : Hom μ ν) : μ.coinvariants →ₗ[R] ν.coinvariants :=
  f.toLinearMap.restrict fun _ hv ↦ f.map_mem_coinvariants hv

@[simp]
theorem coe_mapCoinvariants (f : Hom μ ν) (v : μ.coinvariants) :
    (f.mapCoinvariants v : N) = f v :=
  (rfl)

@[simp]
theorem mapCoinvariants_id (μ : RightHopfModule R H M) :
    (id μ).mapCoinvariants = LinearMap.id := by
  ext
  rfl

@[simp]
theorem mapCoinvariants_comp (g : Hom ν ξ) (f : Hom μ ν) :
    (g.comp f).mapCoinvariants = g.mapCoinvariants ∘ₗ f.mapCoinvariants := by
  ext
  rfl

/-- Functoriality of `free` in the coefficient module: an `R`-linear map `f : M →ₗ[R] N` induces
the right Hopf module morphism `f ⊗ id : M ⊗[R] H → N ⊗[R] H`. -/
def freeMap (f : M →ₗ[R] N) : Hom (free R H M) (free R H N) where
  toLinearMap := f.rTensor H
  map_coact' z := by
    let := Comodule.cofree R H M
    let := Comodule.cofree R H N
    exact (Comodule.Hom.cofreeMap (C := H) f).map_coact_apply z |>.symm
  map_act' z h := by
    induction z using TensorProduct.inductionOn with
    | tmul m a => rfl
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

@[simp]
theorem freeMap_apply (f : M →ₗ[R] N) (z : M ⊗[R] H) :
    freeMap f z = f.rTensor H z :=
  (rfl)

end Hom

end Bialgebra

/-! ### Coinvariant projection and the Fundamental Theorem of Hopf Modules -/

section HopfAlgebra

variable {R : Type u} {H : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The linear contraction `(m₀ ⊗ h) ↦ m₀ ◁ S(h)` underlying the coinvariant projection. -/
private def antipodeActLift (μ : RightHopfModule R H M) : M ⊗[R] H →ₗ[R] M :=
  TensorProduct.lift (μ.act.compl₂ (HopfAlgebraStruct.antipode R))

@[simp]
private theorem antipodeActLift_tmul (μ : RightHopfModule R H M) (m : M) (h : H) :
    μ.antipodeActLift (m ⊗ₜ[R] h) = μ.act m (HopfAlgebraStruct.antipode R h) :=
  (rfl)

/-- The coinvariant projection `M →ₗ[R] M` of a right `H`-Hopf module, sending `m` with coaction
`∑ m₀ ⊗ m₁` to `∑ m₀ ◁ S(m₁)`. -/
def coinvariantProj (μ : RightHopfModule R H M) : M →ₗ[R] M :=
  μ.antipodeActLift ∘ₗ μ.coact

/-- `coinvariantProj` contracts `μ.coact m` with the antipode through the right action. -/
theorem coinvariantProj_def (μ : RightHopfModule R H M) (m : M) :
    μ.coinvariantProj m =
      TensorProduct.lift (μ.act.compl₂ (HopfAlgebraStruct.antipode R)) (μ.coact m) :=
  (rfl)

/-- On `v ◁ h` for a coinvariant vector `v`, the coinvariant projection evaluates to `ε(h) • v`. -/
@[simp]
theorem coinvariantProj_act_of_mem_coinvariants (μ : RightHopfModule R H M) {v : M}
    (hv : v ∈ μ.coinvariants) (h : H) :
    μ.coinvariantProj (μ.act v h) = Coalgebra.counit (R := R) h • v := by
  have hlift : μ.antipodeActLift ∘ₗ (μ.act v).rTensor H =
      μ.act v ∘ₗ LinearMap.mul' R H ∘ₗ (HopfAlgebraStruct.antipode R).lTensor H := by
    refine TensorProduct.ext' fun a b ↦ ?_
    simp [μ.act_mul]
  rw [coinvariantProj, LinearMap.comp_apply, μ.coact_act_of_mem_coinvariants hv,
    ← LinearMap.comp_apply, hlift, LinearMap.comp_apply, LinearMap.comp_apply,
    _root_.HopfAlgebra.mul_antipode_lTensor_comul_apply, μ.act_algebraMap]

/-- Coinvariant vectors are fixed by `coinvariantProj`. -/
@[simp]
theorem coinvariantProj_of_mem_coinvariants (μ : RightHopfModule R H M) {v : M}
    (hv : v ∈ μ.coinvariants) :
    μ.coinvariantProj v = v := by
  simpa only [μ.act_one, Bialgebra.counit_one, one_smul] using
    μ.coinvariantProj_act_of_mem_coinvariants hv 1

/-- Auxiliary four-factor contraction `(m₀ ⊗ c₁) ⊗ (c₂ ⊗ c₃) ↦ (m₀ ◁ S c₃) ⊗ (c₁ * S c₂)`
through which `coact ∘ coinvariantProj` factors. -/
private def coactAntipodeLift (μ : RightHopfModule R H M) :
    (M ⊗[R] H) ⊗[R] (H ⊗[R] H) →ₗ[R] M ⊗[R] H :=
  TensorProduct.lift <|
    (TensorProduct.map₂ μ.act (LinearMap.mul R H)).compl₂
      (TensorProduct.map (HopfAlgebraStruct.antipode R) (HopfAlgebraStruct.antipode R) ∘ₗ
        (TensorProduct.comm R H H).toLinearMap)

private theorem coact_antipodeActLift_eq (μ : RightHopfModule R H M) (z : M ⊗[R] H) :
    μ.coact (μ.antipodeActLift z) =
      μ.coactAntipodeLift (TensorProduct.map μ.coact Coalgebra.comul z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m c =>
    rw [antipodeActLift_tmul, μ.coact_act, HopfAlgebra.antipode_comul_antidistrib_apply,
      TensorProduct.map_tmul]
    rfl

private theorem coactAntipodeLift_double_comul (μ : RightHopfModule R H M) (z : M ⊗[R] H) :
    μ.coactAntipodeLift
        (Coalgebra.comul.lTensor (M ⊗[R] H)
          ((TensorProduct.assoc R M H H).symm (Coalgebra.comul.lTensor M z))) =
      μ.antipodeActLift z ⊗ₜ[R] (1 : H) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
  | tmul m b =>
    classical
    let rb := ℛ R b
    let r₁ := fun i ↦ ℛ R (rb.left i)
    let r₂ := fun i ↦ ℛ R (rb.right i)
    -- Contract coassociativity of `b` with `c₁ ⊗ (c₂ ⊗ c₃) ↦ (m ◁ S c₃) ⊗ (c₁ * S c₂)`.
    let θ : H ⊗[R] (H ⊗[R] H) →ₗ[R] M ⊗[R] H :=
      μ.coactAntipodeLift ∘ₗ (TensorProduct.mk R M H m).rTensor (H ⊗[R] H)
    have hθ (c₁ c₂ c₃ : H) :
        θ (c₁ ⊗ₜ[R] (c₂ ⊗ₜ[R] c₃)) =
          μ.act m (HopfAlgebraStruct.antipode R c₃) ⊗ₜ[R]
            (c₁ * HopfAlgebraStruct.antipode R c₂) := rfl
    have hrhs :
        μ.coactAntipodeLift
            (Coalgebra.comul.lTensor (M ⊗[R] H)
              ((TensorProduct.assoc R M H H).symm (Coalgebra.comul.lTensor M (m ⊗ₜ[R] b)))) =
          ∑ i ∈ rb.index, ∑ j ∈ (r₂ i).index,
            θ (rb.left i ⊗ₜ[R] ((r₂ i).left j ⊗ₜ[R] (r₂ i).right j)) := by
      simp only [LinearMap.lTensor_tmul, ← rb.eq, tmul_sum, map_sum, assoc_symm_tmul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← (r₂ i).eq, tmul_sum, map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ rfl
    have hlhs :
        (∑ i ∈ rb.index, ∑ j ∈ (r₁ i).index,
            θ ((r₁ i).left j ⊗ₜ[R] ((r₁ i).right j ⊗ₜ[R] rb.right i))) =
          μ.act m (HopfAlgebraStruct.antipode R b) ⊗ₜ[R] (1 : H) := by
      simp_rw [hθ, ← tmul_sum, _root_.HopfAlgebra.sum_mul_antipode_eq_smul (r₁ _),
        ← smul_tmul, ← map_smul, ← sum_tmul]
      rw [← map_sum, ← map_sum, Coalgebra.sum_counit_smul rb]
    have hcoassoc :
        (∑ i ∈ rb.index, ∑ j ∈ (r₁ i).index,
            θ ((r₁ i).left j ⊗ₜ[R] ((r₁ i).right j ⊗ₜ[R] rb.right i))) =
          ∑ i ∈ rb.index, ∑ j ∈ (r₂ i).index,
            θ (rb.left i ⊗ₜ[R] ((r₂ i).left j ⊗ₜ[R] (r₂ i).right j)) := by
      simpa only [map_sum] using congrArg θ (Coalgebra.sum_tmul_tmul_eq rb r₁ r₂)
    rw [hrhs, ← hcoassoc, hlhs, antipodeActLift_tmul]

/-- The image of `coinvariantProj` lies in `μ.coinvariants`: every projected vector satisfies
`coact (P m) = P m ⊗ₜ 1`. -/
theorem coinvariantProj_mem_coinvariants (μ : RightHopfModule R H M) (m : M) :
    μ.coinvariantProj m ∈ μ.coinvariants := by
  let : Comodule R H M := μ.toComodule
  rw [mem_coinvariants, coinvariantProj, LinearMap.comp_apply, μ.coact_antipodeActLift_eq]
  have hmap : TensorProduct.map μ.coact Coalgebra.comul (μ.coact m) =
      Coalgebra.comul.lTensor (M ⊗[R] H) (μ.coact.rTensor H (μ.coact m)) :=
    (LinearMap.congr_fun (LinearMap.lTensor_comp_rTensor _ _ _) (μ.coact m)).symm
  rw [hmap, ← Comodule.coassoc_symm_apply (R := R) (C := H), μ.coactAntipodeLift_double_comul]

/-- `coinvariantProj` is idempotent. -/
@[simp]
theorem coinvariantProj_coinvariantProj (μ : RightHopfModule R H M) (m : M) :
    μ.coinvariantProj (μ.coinvariantProj m) = μ.coinvariantProj m :=
  μ.coinvariantProj_of_mem_coinvariants (μ.coinvariantProj_mem_coinvariants m)

/-- The coinvariant projection corestricted to the coinvariant submodule `μ.coinvariants`. -/
def toCoinvariants (μ : RightHopfModule R H M) : M →ₗ[R] μ.coinvariants :=
  μ.coinvariantProj.codRestrict μ.coinvariants μ.coinvariantProj_mem_coinvariants

@[simp]
theorem coe_toCoinvariants (μ : RightHopfModule R H M) (m : M) :
    (μ.toCoinvariants m : M) = μ.coinvariantProj m :=
  (rfl)

@[simp]
theorem toCoinvariants_coe (μ : RightHopfModule R H M) (v : μ.coinvariants) :
    μ.toCoinvariants v = v :=
  Subtype.ext (μ.coinvariantProj_of_mem_coinvariants v.property)

@[simp]
theorem toCoinvariants_act_coe (μ : RightHopfModule R H M) (v : μ.coinvariants) (h : H) :
    μ.toCoinvariants (μ.act v h) = Coalgebra.counit (R := R) h • v :=
  Subtype.ext (μ.coinvariantProj_act_of_mem_coinvariants v.property h)

/-- Morphisms of right Hopf modules commute with `coinvariantProj`. -/
@[simp]
theorem Hom.map_coinvariantProj {μ : RightHopfModule R H M} {ν : RightHopfModule R H N}
    (f : Hom μ ν) (m : M) :
    f (μ.coinvariantProj m) = ν.coinvariantProj (f m) := by
  rw [coinvariantProj_def, coinvariantProj_def, f.map_coact]
  induction μ.coact m using TensorProduct.inductionOn with
  | tmul m₀ h => exact f.map_act m₀ (HopfAlgebraStruct.antipode R h)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The Fundamental Theorem of Hopf Modules**: every right `H`-Hopf module `M` over a Hopf
algebra `H` is canonically `R`-linearly isomorphic to `μ.coinvariants ⊗[R] H`, via `v ⊗ h ↦ v ◁ h`
with inverse `m ↦ ∑ P(m₀) ⊗ m₁`. No finiteness, projectivity, or subtraction is assumed. -/
def coinvariantTensorEquiv (μ : RightHopfModule R H M) :
    μ.coinvariants ⊗[R] H ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap
    (TensorProduct.lift (μ.act.comp μ.coinvariants.subtype))
    (μ.toCoinvariants.rTensor H ∘ₗ μ.coact)
    (by
      let : Comodule R H M := μ.toComodule
      ext m
      -- Contracting `(m₀ ⊗ c₁) ⊗ c₂ ↦ (m₀ ◁ S c₁) ◁ c₂` along coassociativity cancels `S c₁ * c₂`.
      let Ξ : (M ⊗[R] H) ⊗[R] H →ₗ[R] M :=
        TensorProduct.lift (μ.act.comp μ.antipodeActLift)
      have hΞ_lhs :
          TensorProduct.lift (μ.act.comp μ.coinvariants.subtype)
              (μ.toCoinvariants.rTensor H (μ.coact m)) =
            Ξ (μ.coact.rTensor H (μ.coact m)) := by
        have hcomp : TensorProduct.lift (μ.act.comp μ.coinvariants.subtype) ∘ₗ
            μ.toCoinvariants.rTensor H = Ξ ∘ₗ μ.coact.rTensor H := by
          refine TensorProduct.ext' fun m₀ c ↦ ?_
          rfl
        exact LinearMap.congr_fun hcomp (μ.coact m)
      have hΞ_counit (z : M ⊗[R] H) :
          Ξ ((TensorProduct.assoc R M H H).symm (Coalgebra.comul.lTensor M z)) =
            TensorProduct.rid R M (Coalgebra.counit.lTensor M z) := by
        induction z using TensorProduct.inductionOn with
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul m₀ b =>
          classical
          let rb := ℛ R b
          simp only [LinearMap.lTensor_tmul, ← rb.eq, tmul_sum, map_sum, assoc_symm_tmul]
          have hterm (i : _) :
              Ξ ((m₀ ⊗ₜ[R] rb.left i) ⊗ₜ[R] rb.right i) =
                μ.act m₀ (HopfAlgebraStruct.antipode R (rb.left i) * rb.right i) :=
            μ.act_mul m₀ (HopfAlgebraStruct.antipode R (rb.left i)) (rb.right i)
          simp_rw [hterm]
          rw [← map_sum, _root_.HopfAlgebra.sum_antipode_mul_eq_smul rb, μ.act_smul_one, rid_tmul]
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hΞ_lhs,
        ← Comodule.coassoc_symm_apply (R := R) (C := H), hΞ_counit,
        Comodule.rid_lTensor_counit_coact (R := R) (C := H), LinearMap.id_apply])
    (by
      refine TensorProduct.ext' fun v h ↦ ?_
      simp only [LinearMap.comp_apply, lift.tmul, Submodule.subtype_apply, LinearMap.id_apply]
      rw [μ.coact_act_of_mem_coinvariants v.property, ← LinearMap.rTensor_comp_apply]
      classical
      let rh := ℛ R h
      rw [← rh.eq, map_sum]
      simp_rw [LinearMap.rTensor_tmul, LinearMap.comp_apply, μ.toCoinvariants_act_coe,
        smul_tmul, ← tmul_sum, Coalgebra.sum_counit_smul rh])

@[simp]
theorem coinvariantTensorEquiv_tmul (μ : RightHopfModule R H M) (v : μ.coinvariants) (h : H) :
    μ.coinvariantTensorEquiv (v ⊗ₜ[R] h) = μ.act v h :=
  (rfl)

theorem coinvariantTensorEquiv_symm_apply (μ : RightHopfModule R H M) (m : M) :
    μ.coinvariantTensorEquiv.symm m = μ.toCoinvariants.rTensor H (μ.coact m) :=
  (rfl)

@[simp]
theorem coinvariantTensorEquiv_symm_of_mem_coinvariants (μ : RightHopfModule R H M) {v : M}
    (hv : v ∈ μ.coinvariants) :
    μ.coinvariantTensorEquiv.symm v = (⟨v, hv⟩ : μ.coinvariants) ⊗ₜ[R] (1 : H) := by
  rw [coinvariantTensorEquiv_symm_apply, μ.mem_coinvariants.mp hv, LinearMap.rTensor_tmul]
  exact congrArg (· ⊗ₜ[R] (1 : H)) (μ.toCoinvariants_coe ⟨v, hv⟩)

/-- `coinvariantTensorEquiv` intertwines the free right `H`-action on `μ.coinvariants ⊗[R] H`
with the right `H`-action on `M`. -/
@[simp]
theorem coinvariantTensorEquiv_act (μ : RightHopfModule R H M)
    (z : μ.coinvariants ⊗[R] H) (h : H) :
    μ.coinvariantTensorEquiv ((free R H μ.coinvariants).act z h) =
      μ.act (μ.coinvariantTensorEquiv z) h := by
  induction z using TensorProduct.inductionOn with
  | tmul v a => exact (μ.act_mul v a h).symm
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- `coinvariantTensorEquiv.symm` intertwines the coaction of `M` with the cofree coaction on
`μ.coinvariants ⊗[R] H`. -/
@[simp]
theorem coact_coinvariantTensorEquiv_symm (μ : RightHopfModule R H M) (m : M) :
    (free R H μ.coinvariants).coact (μ.coinvariantTensorEquiv.symm m) =
      μ.coinvariantTensorEquiv.symm.toLinearMap.rTensor H (μ.coact m) := by
  let : Comodule R H M := μ.toComodule
  let : Comodule R H (μ.coinvariants ⊗[R] H) := Comodule.cofree R H μ.coinvariants
  exact ((Comodule.Hom.cofreeLift (C := H) μ.toCoinvariants).map_coact_apply m).symm

/-- `coinvariantTensorEquiv` intertwines the cofree coaction on `μ.coinvariants ⊗[R] H` with
the coaction of `M`. -/
@[simp]
theorem coact_coinvariantTensorEquiv (μ : RightHopfModule R H M)
    (z : μ.coinvariants ⊗[R] H) :
    μ.coact (μ.coinvariantTensorEquiv z) =
      μ.coinvariantTensorEquiv.toLinearMap.rTensor H ((free R H μ.coinvariants).coact z) := by
  have h1 := μ.coact_coinvariantTensorEquiv_symm (μ.coinvariantTensorEquiv z)
  rw [μ.coinvariantTensorEquiv.symm_apply_apply] at h1
  calc μ.coact (μ.coinvariantTensorEquiv z)
      = (LinearMap.id : M →ₗ[R] M).rTensor H (μ.coact (μ.coinvariantTensorEquiv z)) :=
        (LinearMap.rTensor_id_apply H M _).symm
    _ = (μ.coinvariantTensorEquiv.toLinearMap ∘ₗ
          μ.coinvariantTensorEquiv.symm.toLinearMap).rTensor H
          (μ.coact (μ.coinvariantTensorEquiv z)) := by
        rw [LinearEquiv.comp_symm]
    _ = μ.coinvariantTensorEquiv.toLinearMap.rTensor H
          ((free R H μ.coinvariants).coact z) := by
        rw [LinearMap.rTensor_comp_apply, h1]

/-- The Fundamental Theorem equivalence `μ.coinvariants ⊗[R] H → M` bundled as a morphism of
right `H`-Hopf modules. -/
def coinvariantTensorHom (μ : RightHopfModule R H M) :
    Hom (free R H μ.coinvariants) μ where
  toLinearMap := μ.coinvariantTensorEquiv.toLinearMap
  map_coact' := μ.coact_coinvariantTensorEquiv
  map_act' := μ.coinvariantTensorEquiv_act

/-- The inverse Fundamental Theorem equivalence `M → μ.coinvariants ⊗[R] H` bundled as a morphism
of right `H`-Hopf modules. -/
def coinvariantTensorInvHom (μ : RightHopfModule R H M) :
    Hom μ (free R H μ.coinvariants) where
  toLinearMap := μ.coinvariantTensorEquiv.symm.toLinearMap
  map_coact' := μ.coact_coinvariantTensorEquiv_symm
  map_act' m h := by
    apply μ.coinvariantTensorEquiv.injective
    rw [LinearEquiv.coe_toLinearMap, μ.coinvariantTensorEquiv.apply_symm_apply,
      μ.coinvariantTensorEquiv_act, μ.coinvariantTensorEquiv.apply_symm_apply]

@[simp]
theorem coinvariantTensorHom_apply (μ : RightHopfModule R H M) (z : μ.coinvariants ⊗[R] H) :
    μ.coinvariantTensorHom z = μ.coinvariantTensorEquiv z :=
  (rfl)

@[simp]
theorem coinvariantTensorInvHom_apply (μ : RightHopfModule R H M) (m : M) :
    μ.coinvariantTensorInvHom m = μ.coinvariantTensorEquiv.symm m :=
  (rfl)

@[simp]
theorem coinvariantTensorHom_comp_invHom (μ : RightHopfModule R H M) :
    μ.coinvariantTensorHom.comp μ.coinvariantTensorInvHom = Hom.id μ := by
  ext m
  exact μ.coinvariantTensorEquiv.apply_symm_apply m

@[simp]
theorem coinvariantTensorInvHom_comp_hom (μ : RightHopfModule R H M) :
    μ.coinvariantTensorInvHom.comp μ.coinvariantTensorHom = Hom.id (free R H μ.coinvariants) := by
  ext z
  exact μ.coinvariantTensorEquiv.symm_apply_apply z

/-- Naturality of `coinvariantTensorEquiv`: every morphism of right `H`-Hopf modules is determined
by its action on coinvariants. -/
theorem Hom.coinvariantTensorEquiv_freeMap_mapCoinvariants
    {μ : RightHopfModule R H M} {ν : RightHopfModule R H N}
    (f : Hom μ ν) (z : μ.coinvariants ⊗[R] H) :
    ν.coinvariantTensorEquiv (Hom.freeMap f.mapCoinvariants z) =
      f (μ.coinvariantTensorEquiv z) := by
  induction z using TensorProduct.inductionOn with
  | tmul v h => exact (f.map_act v h).symm
  | add x y hx hy => simp only [map_add, hx, hy]

end HopfAlgebra

end RightHopfModule

end TauCeti
