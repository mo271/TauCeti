/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Commensurable
import Mathlib.Data.Finsupp.SMul

/-!
# Hecke algebras of permutation modules via invariant kernels

Let `G` be a group acting on a set `S` and let `A` be a commutative ring (or semiring where
commutativity and negation are not needed). Following Treumann–Venkatesh [treumann2016], §2.10, we
define `TauCeti.InvariantKernel A G S`, written math-informally as
$\operatorname{Fun}_G(S \times S, A)$: functions $h : S \times S \to A$ invariant under the
diagonal `G`-action whose support meets only finitely many `G`-orbits in `S × S`.

Without any finiteness assumption on `G` or `S`, `InvariantKernel A G S` is a free `A`-module with
basis `TauCeti.InvariantKernel.orbitBasis` given by the indicator functions of the diagonal
`G`-orbits on `S × S`, and matrix transposition `hᵀ(x, y) = h(y, x)` is an `A`-linear involution.

When every `(stabilizer G x)`-orbit on `S` is finite — in particular, whenever `G` is a topological
group with separately continuous multiplication and every point of `S` has compact open stabilizer
(`MulAction.finite_orbit_stabilizer_of_isCompact_of_isOpen`) — each row `y ↦ h(x, y)` and each
column `t ↦ h(t, s)` is finitely supported. Matrix convolution
$$(h_1 * h_2)(x, z) = \sum_{y \in S} h_1(x, y) \, h_2(y, z)$$
then makes `InvariantKernel A G S` an associative non-unital ring, with transposition an
anti-involution onto its opposite, and gives a covariant left action on the permutation
representation `A[S]` (`Representation.ofMulAction A G S`) by
$$h \cdot [s] = \sum_{t \in S} h(t, s) \, [t].$$
Note the order of indices: `h(t, s)` makes this a *left* action for the matrix product above
(whereas `h(s, t)` as printed in [treumann2016], §2.10 would give a right action).

When `S` has finitely many `G`-orbits (`[Finite (MulAction.orbitRel.Quotient G S)]`), the Kronecker
delta `δ(x, z)` lies in `InvariantKernel A G S`, making `InvariantKernel A G S` a unital `A`-algebra
isomorphic to the `G`-equivariant endomorphism algebra of `A[S]`
(`TauCeti.InvariantKernel.toIntertwiningAlgEquiv` and
`TauCeti.InvariantKernel.toModuleEndAlgEquiv`).

## Main definitions

* `TauCeti.InvariantKernel`: diagonally `G`-invariant kernels `S × S → A` supported on finitely many
  `G`-orbits.
* `TauCeti.InvariantKernel.orbitFinsupp` and `TauCeti.InvariantKernel.orbitBasis`: coordinates and
  basis of orbit indicator functions.
* `TauCeti.InvariantKernel.transpose`: matrix transpose `hᵀ(x, y) = h(y, x)`, promoted to
  `transposeMulEquiv` and `transposeAlgEquiv` onto the opposite algebra.
* `TauCeti.InvariantKernel.toIntertwiningMap`: the `G`-equivariant endomorphism of `A[S]` sending
  `single s 1` to `∑_t single t (h(t, s))`.
* `TauCeti.InvariantKernel.toIntertwiningAlgEquiv` and
  `TauCeti.InvariantKernel.toModuleEndAlgEquiv`: when `S / G` is finite, the `A`-algebra
  isomorphisms with `IntertwiningMap` and
  `Module.End (MonoidAlgebra A G) (Representation.ofMulAction A G S).asModule`.
* `TauCeti.InvariantKernel.mapRingHom`: pushforward of invariant kernels along a ring homomorphism
  `A →+* B`.

## References

* [D. Treumann and A. Venkatesh, *Linkage and functoriality*][treumann2016], §2.10,
  (2.10.1)–(2.10.3), pp. 187–188.
-/

public noncomputable section

open MulAction MonoidAlgebra Representation

namespace TauCeti

/-- The `A`-module $\operatorname{Fun}_G(S \times S, A)$ of functions `h : S × S → A` invariant
under the diagonal action of `G` whose support meets only finitely many `G`-orbits in `S × S`. -/
structure InvariantKernel (A G S : Type*) [Zero A] [Group G] [MulAction G S] where
  /-- The underlying two-variable kernel `S × S → A`. -/
  toFun : S × S → A
  /-- Invariance under the diagonal `G`-action. -/
  map_smul' : ∀ (g : G) (x y : S), toFun (g • x, g • y) = toFun (x, y)
  /-- Finiteness of the set of `G`-orbits meeting the support. -/
  finite_orbitSupport' :
    Set.Finite ((Quotient.mk (orbitRel G (S × S))) '' Function.support toFun)

namespace InvariantKernel

section Basic

variable {A G S : Type*} [Zero A] [Group G] [MulAction G S]

instance : FunLike (InvariantKernel A G S) (S × S) A where
  coe h := h.toFun
  coe_injective h₁ h₂ heq := by cases h₁; cases h₂; congr

@[simp]
theorem toFun_eq_coe (h : InvariantKernel A G S) : h.toFun = ⇑h := (rfl)

@[simp]
theorem coe_mk (f : S × S → A) (hsmul hfin) :
    ⇑(⟨f, hsmul, hfin⟩ : InvariantKernel A G S) = f := (rfl)

/-- Two invariant kernels are equal as soon as they take the same value at every pair `(x, y)`. -/
@[ext]
theorem ext {h₁ h₂ : InvariantKernel A G S} (H : ∀ x y : S, h₁ (x, y) = h₂ (x, y)) : h₁ = h₂ :=
  DFunLike.ext h₁ h₂ fun ⟨x, y⟩ ↦ H x y

/-- Diagonal `G`-invariance of an `InvariantKernel`. -/
@[simp]
theorem map_smul (h : InvariantKernel A G S) (g : G) (x y : S) :
    h (g • x, g • y) = h (x, y) :=
  h.map_smul' g x y

/-- Diagonal `G`-invariance written with the product action on `S × S`. -/
theorem map_smul_prod (h : InvariantKernel A G S) (g : G) (p : S × S) :
    h (g • p) = h p :=
  h.map_smul g p.1 p.2

/-- The set of `G`-orbits meeting the support of `h` is finite. -/
theorem finite_orbitSupport (h : InvariantKernel A G S) :
    Set.Finite ((Quotient.mk (orbitRel G (S × S))) '' Function.support h) :=
  h.finite_orbitSupport'

instance : Zero (InvariantKernel A G S) where
  zero := ⟨0, fun _ _ _ ↦ rfl, by simp⟩

@[simp]
theorem zero_apply (p : S × S) : (0 : InvariantKernel A G S) p = 0 := (rfl)

instance : Inhabited (InvariantKernel A G S) := ⟨0⟩

/-- On an empty `G`-set, `InvariantKernel A G S` has only the zero kernel. -/
instance [IsEmpty S] : Unique (InvariantKernel A G S) where
  default := 0
  uniq _ := ext fun x ↦ isEmptyElim x

/-- Matrix transpose `hᵀ(x, y) = h(y, x)` preserves diagonal `G`-invariance and finite orbit
support. -/
def transpose (h : InvariantKernel A G S) : InvariantKernel A G S where
  toFun p := h p.swap
  map_smul' g x y := h.map_smul g y x
  finite_orbitSupport' := by
    let swapOrb : orbitRel.Quotient G (S × S) → orbitRel.Quotient G (S × S) :=
      Quotient.map' Prod.swap fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨g, hg⟩ ↦ by
        obtain ⟨hx, hy⟩ := Prod.mk.inj hg
        exact ⟨g, Prod.ext hy hx⟩
    have hsub : (Quotient.mk (orbitRel G (S × S))) '' Function.support (fun p : S × S ↦ h p.swap) ⊆
        swapOrb '' ((Quotient.mk (orbitRel G (S × S))) '' Function.support h) := by
      rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
      exact ⟨⟦(y, x)⟧, ⟨(y, x), hxy, rfl⟩, rfl⟩
    exact (h.finite_orbitSupport.image swapOrb).subset hsub

@[simp]
theorem transpose_apply (h : InvariantKernel A G S) (x y : S) :
    h.transpose (x, y) = h (y, x) := (rfl)

@[simp]
theorem transpose_transpose (h : InvariantKernel A G S) :
    h.transpose.transpose = h :=
  ext fun _ _ ↦ rfl

@[simp]
theorem transpose_zero : (0 : InvariantKernel A G S).transpose = 0 :=
  ext fun _ _ ↦ rfl

end Basic

section AddCommMonoid

variable {R A G S : Type*} [Group G] [MulAction G S]

section Add

variable [AddCommMonoid A]

instance : Add (InvariantKernel A G S) where
  add h₁ h₂ :=
    { toFun := h₁ + h₂
      map_smul' := fun g x y ↦ by simp [Pi.add_apply]
      finite_orbitSupport' :=
        ((h₁.finite_orbitSupport.union h₂.finite_orbitSupport)).subset <| by
          rw [← Set.image_union]
          exact Set.image_mono (Function.support_add ⇑h₁ ⇑h₂) }

@[simp]
theorem add_apply (h₁ h₂ : InvariantKernel A G S) (p : S × S) :
    (h₁ + h₂) p = h₁ p + h₂ p := (rfl)

instance [Semiring R] [Module R A] : SMul R (InvariantKernel A G S) where
  smul r h :=
    { toFun := r • ⇑h
      map_smul' := fun g x y ↦ by simp [Pi.smul_apply]
      finite_orbitSupport' :=
        h.finite_orbitSupport.subset <| Set.image_mono fun p hp hzero ↦
          hp (by simp [Pi.smul_apply, hzero]) }

@[simp]
theorem smul_apply [Semiring R] [Module R A] (r : R) (h : InvariantKernel A G S) (p : S × S) :
    (r • h) p = r • h p := (rfl)

instance : AddCommMonoid (InvariantKernel A G S) :=
  DFunLike.coe_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance [Semiring R] [Module R A] : Module R (InvariantKernel A G S) :=
  DFunLike.coe_injective.module R ⟨⟨_, rfl⟩, fun _ _ ↦ rfl⟩ fun _ _ ↦ rfl

instance {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂] [Module R₁ A] [Module R₂ A]
    [SMul R₁ R₂] [IsScalarTower R₁ R₂ A] :
    IsScalarTower R₁ R₂ (InvariantKernel A G S) where
  smul_assoc r₁ r₂ h := ext fun x y ↦ smul_assoc r₁ r₂ (h (x, y))

instance {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂] [Module R₁ A] [Module R₂ A]
    [SMulCommClass R₁ R₂ A] :
    SMulCommClass R₁ R₂ (InvariantKernel A G S) where
  smul_comm r₁ r₂ h := ext fun x y ↦ smul_comm r₁ r₂ (h (x, y))

@[simp]
theorem transpose_add (h₁ h₂ : InvariantKernel A G S) :
    (h₁ + h₂).transpose = h₁.transpose + h₂.transpose :=
  ext fun _ _ ↦ rfl

@[simp]
theorem transpose_smul [Semiring R] [Module R A] (r : R) (h : InvariantKernel A G S) :
    (r • h).transpose = r • h.transpose :=
  ext fun _ _ ↦ rfl

end Add

section Group

variable [AddCommGroup A]

instance : Neg (InvariantKernel A G S) where
  neg h :=
    { toFun := -⇑h
      map_smul' := fun g x y ↦ by simp [Pi.neg_apply]
      finite_orbitSupport' := by simpa [Function.support_neg] using h.finite_orbitSupport }

instance : Sub (InvariantKernel A G S) where
  sub h₁ h₂ :=
    { toFun := ⇑h₁ - ⇑h₂
      map_smul' := fun g x y ↦ by simp [Pi.sub_apply]
      finite_orbitSupport' :=
        (h₁.finite_orbitSupport.union h₂.finite_orbitSupport).subset <| by
          rw [← Set.image_union]
          exact Set.image_mono (Function.support_sub ⇑h₁ ⇑h₂) }

@[simp]
theorem neg_apply (h : InvariantKernel A G S) (p : S × S) : (-h) p = -h p := (rfl)

@[simp]
theorem sub_apply (h₁ h₂ : InvariantKernel A G S) (p : S × S) :
    (h₁ - h₂) p = h₁ p - h₂ p := (rfl)

instance : AddCommGroup (InvariantKernel A G S) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end Group

end AddCommMonoid

section OrbitBasis

variable (A G S : Type*) [Semiring A] [Group G] [MulAction G S]

/-- Reading an `InvariantKernel` as a finitely supported function on the diagonal orbit space
`(S × S) / G`. -/
def orbitFinsupp : InvariantKernel A G S ≃ₗ[A] (orbitRel.Quotient G (S × S) →₀ A) where
  toFun h :=
    Finsupp.ofSupportFinite
      (fun O ↦ Quotient.liftOn' O h fun p q ⟨g, hg⟩ ↦ by
        rw [← hg]
        exact h.map_smul_prod g q)
      (h.finite_orbitSupport.subset fun O hO ↦ by
        induction O using Quotient.inductionOn' with | h p =>
        exact ⟨p, hO, rfl⟩)
  map_add' h₁ h₂ := by
    ext O
    induction O using Quotient.inductionOn' with | h p =>
    rfl
  map_smul' r h := by
    ext O
    induction O using Quotient.inductionOn' with | h p =>
    rfl
  invFun f :=
    { toFun := fun p ↦ f ⟦p⟧
      map_smul' := fun g x y ↦ congrArg f (Quotient.sound ⟨g, rfl⟩)
      finite_orbitSupport' :=
        f.support.finite_toSet.subset <| by
          rintro _ ⟨p, hp, rfl⟩
          exact Finsupp.mem_support_iff.mpr hp }
  left_inv h := by ext x y; rfl
  right_inv f := by
    ext O
    induction O using Quotient.inductionOn' with | h p =>
    rfl

variable {A G S} in
@[simp]
theorem orbitFinsupp_apply_mk (h : InvariantKernel A G S) (p : S × S) :
    orbitFinsupp A G S h ⟦p⟧ = h p := (rfl)

variable {A G S} in
@[simp]
theorem orbitFinsupp_symm_apply (f : orbitRel.Quotient G (S × S) →₀ A) (p : S × S) :
    (orbitFinsupp A G S).symm f p = f ⟦p⟧ := (rfl)

/-- **The orbit-indicator basis of `InvariantKernel A G S`.** Each diagonal `G`-orbit `O` on
`S × S` contributes its indicator function. -/
def orbitBasis : Module.Basis (orbitRel.Quotient G (S × S)) A (InvariantKernel A G S) :=
  Module.Basis.ofRepr (orbitFinsupp A G S)

variable {A G S} in
@[simp]
theorem orbitBasis_repr_mk (h : InvariantKernel A G S) (p : S × S) :
    (orbitBasis A G S).repr h ⟦p⟧ = h p := (rfl)

open Classical in
variable {A G S} in
/-- Evaluating `orbitBasis A G S O` at `(x, y)` gives `1` on the orbit `O` and `0` off it. -/
@[simp]
theorem orbitBasis_apply (O : orbitRel.Quotient G (S × S)) (x y : S) :
    orbitBasis A G S O (x, y) =
      if (Quotient.mk (orbitRel G (S × S)) (x, y)) = O then 1 else 0 := by
  rw [← orbitBasis_repr_mk, Module.Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

end OrbitBasis

section Convolution

variable {A G S : Type*} [Group G] [MulAction G S]

/-- A single diagonal `G`-orbit on `S × S` meets any horizontal slice `{x} × S` in at most one
`(stabilizer G x)`-orbit, hence in a finite set when stabilizer orbits are finite. -/
private theorem finite_orbit_slice_right
    [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]
    (O : orbitRel.Quotient G (S × S)) (x : S) :
    Set.Finite {y : S | Quotient.mk (orbitRel G (S × S)) (x, y) = O} := by
  by_cases hne : ∃ y₀ : S, Quotient.mk (orbitRel G (S × S)) (x, y₀) = O
  · obtain ⟨y₀, rfl⟩ := hne
    refine (Set.toFinite (orbit (stabilizer G x) y₀)).subset fun y hy ↦ ?_
    obtain ⟨g, hg⟩ := Quotient.exact hy
    obtain ⟨hgx, hgy⟩ := Prod.mk.inj hg
    exact ⟨⟨g, hgx⟩, hgy⟩
  · exact Set.finite_empty.subset fun y hy ↦ (hne ⟨y, hy⟩).elim

/-- Every row `y ↦ h (x, y)` of an `InvariantKernel` has finite support when stabilizer orbits are
finite. -/
theorem finite_support_right [Zero A]
    [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]
    (h : InvariantKernel A G S) (x : S) :
    (Function.support fun y ↦ h (x, y)).Finite := by
  refine (h.finite_orbitSupport.biUnion fun O _ ↦ finite_orbit_slice_right O x).subset ?_
  intro y hy
  exact Set.mem_biUnion ⟨(x, y), hy, rfl⟩ rfl

/-- Every column `x ↦ h (x, z)` of an `InvariantKernel` has finite support when stabilizer orbits
are finite. -/
theorem finite_support_left [Zero A]
    [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]
    (h : InvariantKernel A G S) (z : S) :
    (Function.support fun x ↦ h (x, z)).Finite :=
  h.transpose.finite_support_right z

section Semiring

variable [Semiring A] [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]

/-- Matrix convolution `(h₁ * h₂)(x, z) = ∑ᶠ y, h₁(x, y) * h₂(y, z)` of invariant kernels. -/
instance : Mul (InvariantKernel A G S) where
  mul h₁ h₂ :=
    { toFun := fun p ↦ ∑ᶠ y : S, h₁ (p.1, y) * h₂ (y, p.2)
      map_smul' := fun g x z ↦ by
        rw [← finsum_comp_equiv (MulAction.toPerm g)]
        refine finsum_congr fun y ↦ ?_
        simp only [MulAction.toPerm_apply, map_smul]
      finite_orbitSupport' := by
        refine (h₁.finite_orbitSupport.biUnion fun O₁ _ ↦
          ((h₂.finite_support_right O₁.out.2).image fun w ↦
            Quotient.mk (orbitRel G (S × S)) (O₁.out.1, w))).subset ?_
        rintro _ ⟨⟨x, z⟩, hxz, rfl⟩
        have hex : ∃ y : S, h₁ (x, y) * h₂ (y, z) ≠ 0 := by
          by_contra! hall
          exact hxz (finsum_eq_zero_of_forall_eq_zero hall)
        obtain ⟨y, hy⟩ := hex
        have hy₁ : h₁ (x, y) ≠ 0 := left_ne_zero_of_mul hy
        have hy₂ : h₂ (y, z) ≠ 0 := right_ne_zero_of_mul hy
        let O₁ : orbitRel.Quotient G (S × S) := ⟦(x, y)⟧
        have hO₁ : O₁ ∈ (Quotient.mk (orbitRel G (S × S))) '' Function.support h₁ :=
          ⟨(x, y), hy₁, rfl⟩
        obtain ⟨g, hg⟩ : ∃ g : G, g • O₁.out = (x, y) := by
          obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G (S × S)) (x, y)
          exact ⟨g⁻¹, by simpa [O₁] using congrArg (g⁻¹ • ·) hg.symm⟩
        obtain ⟨hx, hy_eq⟩ := Prod.mk.inj hg
        have hw : g⁻¹ • z ∈ Function.support (fun w ↦ h₂ (O₁.out.2, w)) := by
          rw [Function.mem_support, ← h₂.map_smul g, hy_eq, smul_inv_smul]
          exact hy₂
        refine Set.mem_biUnion hO₁ ⟨g⁻¹ • z, hw, ?_⟩
        exact Quotient.sound ⟨g⁻¹, by simp [← hx]⟩ }

/-- **Matrix convolution formula** for `InvariantKernel`. -/
theorem mul_apply (h₁ h₂ : InvariantKernel A G S) (x z : S) :
    (h₁ * h₂) (x, z) = ∑ᶠ y : S, h₁ (x, y) * h₂ (y, z) := (rfl)

/-- Matrix convolution written over any `Finset` containing the support of the row
`y ↦ h₁(x, y)`. -/
theorem mul_apply_eq_sum (h₁ h₂ : InvariantKernel A G S) (x z : S) (s : Finset S)
    (hs : ∀ y, h₁ (x, y) ≠ 0 → y ∈ s) :
    (h₁ * h₂) (x, z) = ∑ y ∈ s, h₁ (x, y) * h₂ (y, z) := by
  rw [mul_apply, finsum_eq_sum_of_support_subset]
  intro y hy
  exact hs y (left_ne_zero_of_mul hy)

instance : NonUnitalSemiring (InvariantKernel A G S) where
  left_distrib h₁ h₂ h₃ := by
    ext x z
    simp only [mul_apply, add_apply, mul_add]
    exact finsum_add_distrib
      ((h₁.finite_support_right x).subset fun y hy ↦ left_ne_zero_of_mul hy)
      ((h₁.finite_support_right x).subset fun y hy ↦ left_ne_zero_of_mul hy)
  right_distrib h₁ h₂ h₃ := by
    ext x z
    simp only [mul_apply, add_apply, add_mul]
    exact finsum_add_distrib
      ((h₁.finite_support_right x).subset fun y hy ↦ left_ne_zero_of_mul hy)
      ((h₂.finite_support_right x).subset fun y hy ↦ left_ne_zero_of_mul hy)
  zero_mul h := ext fun x z ↦ by simp [mul_apply]
  mul_zero h := ext fun x z ↦ by simp [mul_apply]
  mul_assoc h₁ h₂ h₃ := by
    classical
    ext x w
    let Y := (h₁.finite_support_right x).toFinset
    let Z := (h₃.finite_support_left w).toFinset
    have lhs_eq : ((h₁ * h₂) * h₃) (x, w) =
        ∑ z ∈ Z, ∑ y ∈ Y, h₁ (x, y) * h₂ (y, z) * h₃ (z, w) := by
      rw [mul_apply, finsum_eq_sum_of_support_subset _ (s := Z) (fun z hz ↦ by
        simp [Z, right_ne_zero_of_mul hz])]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [mul_apply_eq_sum h₁ h₂ x z Y (fun y hy ↦ by simp [Y, hy]), Finset.sum_mul]
    have rhs_eq : (h₁ * (h₂ * h₃)) (x, w) =
        ∑ y ∈ Y, ∑ z ∈ Z, h₁ (x, y) * (h₂ (y, z) * h₃ (z, w)) := by
      rw [mul_apply_eq_sum h₁ (h₂ * h₃) x w Y (fun y hy ↦ by simp [Y, hy])]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [mul_apply, finsum_eq_sum_of_support_subset _ (s := Z) (fun z hz ↦ by
        simp [Z, right_ne_zero_of_mul hz]), Finset.mul_sum]
    rw [lhs_eq, rhs_eq, Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun z _ ↦ mul_assoc _ _ _

instance {R : Type*} [CommSemiring R] [Algebra R A] :
    IsScalarTower R (InvariantKernel A G S) (InvariantKernel A G S) where
  smul_assoc r h₁ h₂ := by
    ext x z
    simp only [smul_eq_mul, mul_apply, smul_apply, smul_mul_assoc]
    exact (smul_finsum' r
      ((h₁.finite_support_right x).subset fun y hy ↦ left_ne_zero_of_mul hy)).symm

instance {R : Type*} [CommSemiring R] [Algebra R A] :
    SMulCommClass R (InvariantKernel A G S) (InvariantKernel A G S) where
  smul_comm r h₁ h₂ := by
    ext x z
    simp only [smul_eq_mul, mul_apply, smul_apply, mul_smul_comm]
    exact smul_finsum' r
      ((h₁.finite_support_right x).subset fun y hy ↦ left_ne_zero_of_mul hy)

end Semiring

section Ring

variable [Ring A] [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]

instance : NonUnitalRing (InvariantKernel A G S) :=
  { (inferInstance : AddCommGroup (InvariantKernel A G S)),
    (inferInstance : NonUnitalSemiring (InvariantKernel A G S)) with }

end Ring

section TransposeMul

variable [CommSemiring A] [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]

/-- Matrix transpose reverses the convolution product over a commutative coefficient semiring. -/
@[simp]
theorem transpose_mul (h₁ h₂ : InvariantKernel A G S) :
    (h₁ * h₂).transpose = h₂.transpose * h₁.transpose := by
  ext x z
  simp only [transpose_apply, mul_apply, mul_comm]

/-- Matrix transpose as a multiplicative equivalence onto the opposite algebra. -/
def transposeMulEquiv : InvariantKernel A G S ≃* (InvariantKernel A G S)ᵐᵒᵖ where
  toFun h := MulOpposite.op h.transpose
  invFun h := h.unop.transpose
  left_inv h := h.transpose_transpose
  right_inv h := MulOpposite.unop_injective h.unop.transpose_transpose
  map_mul' h₁ h₂ := by simp [transpose_mul]

@[simp]
theorem transposeMulEquiv_apply (h : InvariantKernel A G S) :
    transposeMulEquiv h = MulOpposite.op h.transpose := (rfl)

@[simp]
theorem transposeMulEquiv_symm_apply (h : (InvariantKernel A G S)ᵐᵒᵖ) :
    transposeMulEquiv.symm h = h.unop.transpose := (rfl)

end TransposeMul

end Convolution

section Unital

variable {A G S : Type*} [Group G] [MulAction G S]

section Scalar

variable [Semiring A] [Finite (orbitRel.Quotient G S)]

open Classical in
/-- The scalar diagonal kernel `(x, z) ↦ if x = z then a else 0`, supported on the diagonal orbits
when `S / G` is finite. -/
def scalarKernel (a : A) : InvariantKernel A G S where
  toFun p := if p.1 = p.2 then a else 0
  map_smul' g x y := by simp [MulAction.injective g |>.eq_iff]
  finite_orbitSupport' := by
    let diagOrb : orbitRel.Quotient G S → orbitRel.Quotient G (S × S) :=
      Quotient.map' (fun s ↦ (s, s)) fun s₁ s₂ ⟨g, hg⟩ ↦ ⟨g, Prod.ext hg hg⟩
    refine (Set.finite_range diagOrb).subset ?_
    rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
    have heq : x = y := by
      by_contra hne
      exact hxy (by simp [hne])
    subst heq
    exact ⟨⟦x⟧, rfl⟩

open Classical in
@[simp]
theorem scalarKernel_apply (a : A) (x z : S) :
    scalarKernel (G := G) a (x, z) = if x = z then a else 0 := (rfl)

@[simp]
theorem transpose_scalarKernel (a : A) :
    (scalarKernel (G := G) (S := S) a).transpose = scalarKernel a := by
  classical
  ext x z
  simp [eq_comm]

instance : One (InvariantKernel A G S) where
  one := scalarKernel 1

open Classical in
/-- **Identity kernel formula** when `S` has finitely many `G`-orbits. -/
theorem one_apply (x z : S) :
    (1 : InvariantKernel A G S) (x, z) = if x = z then 1 else 0 := (rfl)

@[simp]
theorem transpose_one : (1 : InvariantKernel A G S).transpose = 1 :=
  transpose_scalarKernel 1

end Scalar

section Semiring

variable [Semiring A] [Finite (orbitRel.Quotient G S)]
  [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]

instance : Semiring (InvariantKernel A G S) where
  __ := (inferInstance : NonUnitalSemiring (InvariantKernel A G S))
  __ := (inferInstance : One (InvariantKernel A G S))
  one_mul h := by
    classical
    ext x z
    rw [mul_apply, finsum_eq_single _ x fun y hy ↦ by simp [one_apply, hy.symm]]
    simp [one_apply]
  mul_one h := by
    classical
    ext x z
    rw [mul_apply, finsum_eq_single _ z fun y hy ↦ by simp [one_apply, hy]]
    simp [one_apply]

end Semiring

section Ring

variable [Ring A] [Finite (orbitRel.Quotient G S)]
  [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]

instance : Ring (InvariantKernel A G S) :=
  { (inferInstance : AddCommGroup (InvariantKernel A G S)),
    (inferInstance : Semiring (InvariantKernel A G S)) with }

end Ring

section Algebra

variable [CommSemiring A] [Finite (orbitRel.Quotient G S)]
  [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]

instance : Algebra A (InvariantKernel A G S) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

open Classical in
/-- **Scalar matrix formula**: `algebraMap A (InvariantKernel A G S) a` is `a` on the diagonal and
`0` off the diagonal. -/
theorem algebraMap_apply (a : A) (x z : S) :
    algebraMap A (InvariantKernel A G S) a (x, z) = if x = z then a else 0 := by
  classical
  rw [Algebra.algebraMap_eq_smul_one, smul_apply, one_apply]
  by_cases hxz : x = z <;> simp [hxz]

/-- Matrix transpose as an `A`-algebra isomorphism onto the opposite algebra. -/
def transposeAlgEquiv : InvariantKernel A G S ≃ₐ[A] (InvariantKernel A G S)ᵐᵒᵖ where
  toFun h := MulOpposite.op h.transpose
  invFun h := h.unop.transpose
  left_inv h := h.transpose_transpose
  right_inv h := MulOpposite.unop_injective h.unop.transpose_transpose
  map_mul' h₁ h₂ := by simp [transpose_mul]
  map_add' h₁ h₂ := by simp
  commutes' a := by
    classical
    apply MulOpposite.unop_injective
    ext x z
    simp [algebraMap_apply, eq_comm]

@[simp]
theorem transposeAlgEquiv_apply (h : InvariantKernel A G S) :
    transposeAlgEquiv h = MulOpposite.op h.transpose := (rfl)

@[simp]
theorem transposeAlgEquiv_symm_apply (h : (InvariantKernel A G S)ᵐᵒᵖ) :
    transposeAlgEquiv.symm h = h.unop.transpose := (rfl)

/-- On a one-point `G`-set, `InvariantKernel A G S` is `A` itself by evaluation at the unique
pair. -/
def uniqueAlgEquiv [Unique S] : InvariantKernel A G S ≃ₐ[A] A where
  toFun h := h (default, default)
  invFun a := algebraMap A (InvariantKernel A G S) a
  left_inv h := by
    classical
    ext x z
    rw [Subsingleton.elim x default, Subsingleton.elim z default, algebraMap_apply]
    simp
  right_inv a := by classical simp [algebraMap_apply]
  map_mul' h₁ h₂ := by
    rw [mul_apply, finsum_eq_single _ default fun y hy ↦ (hy (Subsingleton.elim y default)).elim]
  map_add' _ _ := rfl
  commutes' a := by classical simp [algebraMap_apply]

@[simp]
theorem uniqueAlgEquiv_apply [Unique S] (h : InvariantKernel A G S) :
    uniqueAlgEquiv h = h (default, default) := (rfl)

end Algebra

end Unital

section BaseChange

variable {A B G S : Type*} [Group G] [MulAction G S]

/-- Push an `InvariantKernel` forward along a ring homomorphism `φ : A →+* B`. -/
def mapNonUnitalRingHom [Semiring A] [Semiring B]
    [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]
    (φ : A →+* B) : InvariantKernel A G S →ₙ+* InvariantKernel B G S where
  toFun h :=
    { toFun := fun p ↦ φ (h p)
      map_smul' := fun g x y ↦ congrArg φ (h.map_smul g x y)
      finite_orbitSupport' :=
        h.finite_orbitSupport.subset <| Set.image_mono fun p hp hzero ↦
          hp (by simp [hzero]) }
  map_mul' h₁ h₂ := by
    classical
    ext x z
    let Y := (h₁.finite_support_right x).toFinset
    rw [coe_mk, mul_apply_eq_sum h₁ h₂ x z Y (fun y hy ↦ by simp [Y, hy]), map_sum,
      mul_apply_eq_sum _ _ x z Y (fun y hy ↦ by
        simp only [coe_mk] at hy
        have hne : h₁ (x, y) ≠ 0 := fun h0 ↦ hy (by rw [h0, map_zero])
        simp [Y, hne])]
    simp [map_mul]
  map_zero' := ext fun _ _ ↦ map_zero φ
  map_add' h₁ h₂ := ext fun x z ↦ map_add φ (h₁ (x, z)) (h₂ (x, z))

@[simp]
theorem mapNonUnitalRingHom_apply [Semiring A] [Semiring B]
    [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]
    (φ : A →+* B) (h : InvariantKernel A G S) (p : S × S) :
    mapNonUnitalRingHom φ h p = φ (h p) := (rfl)

/-- Unital ring homomorphism induced on `InvariantKernel` by `φ : A →+* B` when `S / G` is
finite. -/
def mapRingHom [Semiring A] [Semiring B] [Finite (orbitRel.Quotient G S)]
    [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]
    (φ : A →+* B) : InvariantKernel A G S →+* InvariantKernel B G S where
  __ := mapNonUnitalRingHom φ
  map_one' := by
    classical
    ext x z
    by_cases hxz : x = z <;> simp [hxz, one_apply]

@[simp]
theorem mapRingHom_apply [Semiring A] [Semiring B] [Finite (orbitRel.Quotient G S)]
    [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]
    (φ : A →+* B) (h : InvariantKernel A G S) (p : S × S) :
    mapRingHom φ h p = φ (h p) := (rfl)

end BaseChange

section PermutationAction

variable {A G S : Type*} [CommSemiring A] [Group G] [MulAction G S]

section Action

variable [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]

/-- Column `s` of an `InvariantKernel`, as a finitely supported function `t ↦ h(t, s)`. -/
def colFinsupp (h : InvariantKernel A G S) (s : S) : S →₀ A :=
  Finsupp.ofSupportFinite (fun t ↦ h (t, s)) (h.finite_support_left s)

@[simp]
theorem colFinsupp_apply (h : InvariantKernel A G S) (s t : S) :
    h.colFinsupp s t = h (t, s) := (rfl)

/-- The `G`-equivariant linear endomorphism of `A[S]` attached to `h : InvariantKernel A G S`,
sending `single s 1` to `∑_t single t (h(t, s))`. -/
def toIntertwiningMap (h : InvariantKernel A G S) :
    (ofMulAction A G S).IntertwiningMap (ofMulAction A G S) where
  toLinearMap :=
    Finsupp.linearCombination A (fun s ↦ MonoidAlgebra.ofCoeff (h.colFinsupp s)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv A).toLinearMap
  isIntertwining' g := by
    refine MonoidAlgebra.lhom_ext' fun s ↦ LinearMap.ext_ring ?_
    ext t
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply, ofMulAction_single,
      LinearEquiv.coe_coe, coeffLinearEquiv_apply, coeff_single, Finsupp.linearCombination_single,
      one_smul, coeff_ofMulAction, coeff_ofCoeff, colFinsupp_apply]
    rw [← h.map_smul g (g⁻¹ • t) s, smul_inv_smul]

/-- **Column action formula**: `h` sends `single s c` to the vector whose `t`-coefficient is
`c * h(t, s) = h(t, s) * c`. Note the order `(t, s)` of the matrix indices. -/
@[simp]
theorem coeff_toIntertwiningMap_single (h : InvariantKernel A G S) (s : S) (c : A) (t : S) :
    (h.toIntertwiningMap (MonoidAlgebra.single s c)).coeff t = h (t, s) * c := by
  simp [toIntertwiningMap, mul_comm]

/-- Explicit finite sum expansion of `h.toIntertwiningMap (single s 1)`. -/
theorem toIntertwiningMap_single_one_eq_sum (h : InvariantKernel A G S) (s : S) :
    h.toIntertwiningMap (MonoidAlgebra.single s 1) =
      ∑ t ∈ (h.colFinsupp s).support, MonoidAlgebra.single t (h (t, s)) := by
  ext t
  classical
  simp only [coeff_toIntertwiningMap_single, mul_one, coeff_sum, Finsupp.finsetSum_apply,
    coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finsupp.mem_support_iff,
    colFinsupp_apply]
  split_ifs with ht
  · rfl
  · exact not_not.mp ht

/-- Action of `h` on an arbitrary finitely supported column `v : A[S]`. -/
theorem coeff_toIntertwiningMap_apply (h : InvariantKernel A G S) (v : MonoidAlgebra A S) (t : S) :
    (h.toIntertwiningMap v).coeff t = ∑ᶠ s : S, h (t, s) * v.coeff s := by
  induction v using MonoidAlgebra.induction_linear with
  | zero => simp
  | add v w hv hw =>
    rw [map_add, coeff_add, Finsupp.add_apply, hv, hw, ← finsum_add_distrib]
    · exact finsum_congr fun s ↦ (mul_add _ _ _).symm
    · exact (h.finite_support_right t).subset fun s hs ↦ left_ne_zero_of_mul hs
    · exact (h.finite_support_right t).subset fun s hs ↦ left_ne_zero_of_mul hs
  | single s c =>
    classical
    rw [coeff_toIntertwiningMap_single,
      finsum_eq_single _ s fun s' hs' ↦ by simp [coeff_single, Finsupp.single_eq_of_ne hs']]
    simp

@[simp]
theorem toIntertwiningMap_zero :
    (0 : InvariantKernel A G S).toIntertwiningMap = 0 := by
  apply IntertwiningMap.ext
  refine MonoidAlgebra.lhom_ext' fun s ↦ LinearMap.ext_ring ?_
  ext t
  simp

@[simp]
theorem toIntertwiningMap_add (h₁ h₂ : InvariantKernel A G S) :
    (h₁ + h₂).toIntertwiningMap = h₁.toIntertwiningMap + h₂.toIntertwiningMap := by
  apply IntertwiningMap.ext
  refine MonoidAlgebra.lhom_ext' fun s ↦ LinearMap.ext_ring ?_
  ext t
  simp

@[simp]
theorem toIntertwiningMap_smul (a : A) (h : InvariantKernel A G S) :
    (a • h).toIntertwiningMap = a • h.toIntertwiningMap := by
  apply IntertwiningMap.ext
  refine MonoidAlgebra.lhom_ext' fun s ↦ LinearMap.ext_ring ?_
  ext t
  simp

/-- Covariant multiplicativity: matrix convolution matches composition of intertwining maps on the
left permutation module `A[S]`. -/
@[simp]
theorem toIntertwiningMap_mul (h₁ h₂ : InvariantKernel A G S) :
    (h₁ * h₂).toIntertwiningMap = h₁.toIntertwiningMap.comp h₂.toIntertwiningMap := by
  apply IntertwiningMap.ext
  refine MonoidAlgebra.lhom_ext' fun z ↦ LinearMap.ext_ring ?_
  ext x
  simp only [LinearMap.comp_apply, lsingle_apply, IntertwiningMap.coe_toLinearMap]
  rw [coeff_toIntertwiningMap_single, mul_one, IntertwiningMap.comp_apply,
    coeff_toIntertwiningMap_apply, mul_apply]
  refine finsum_congr fun y ↦ ?_
  rw [coeff_toIntertwiningMap_single, mul_one]

/-- Left `InvariantKernel A G S`-module structure on `A[S]` when `S / G` is finite. -/
@[simp]
theorem toIntertwiningMap_one [Finite (orbitRel.Quotient G S)] :
    (1 : InvariantKernel A G S).toIntertwiningMap = .id (ofMulAction A G S) := by
  classical
  apply IntertwiningMap.ext
  refine MonoidAlgebra.lhom_ext' fun s ↦ LinearMap.ext_ring ?_
  ext t
  simp [one_apply, coeff_single, Finsupp.single_apply, eq_comm]

/-- Scalar matrices act on `A[S]` by scalar multiplication. -/
@[simp]
theorem toIntertwiningMap_algebraMap [Finite (orbitRel.Quotient G S)]
    (a : A) (v : MonoidAlgebra A S) :
    (algebraMap A (InvariantKernel A G S) a).toIntertwiningMap v = a • v := by
  rw [Algebra.algebraMap_eq_smul_one, toIntertwiningMap_smul, toIntertwiningMap_one]
  rfl

end Action

section Equiv

variable [Finite (orbitRel.Quotient G S)]

/-- Extract the matrix kernel `(t, s) ↦ (f (single s 1)).coeff t` of a `G`-intertwining
endomorphism of `A[S]` when `S` has finitely many `G`-orbits. -/
def ofIntertwiningMap
    (f : (ofMulAction A G S).IntertwiningMap (ofMulAction A G S)) :
    InvariantKernel A G S where
  toFun p := (f (MonoidAlgebra.single p.2 1)).coeff p.1
  map_smul' g t s := by
    have hf : f (MonoidAlgebra.single (g • s) 1) =
        ofMulAction A G S g (f (MonoidAlgebra.single s 1)) := by
      rw [← f.isIntertwining, ofMulAction_single]
    rw [hf, coeff_ofMulAction, inv_smul_smul]
  finite_orbitSupport' := by
    have hsmul (g : G) (t s : S) :
        (f (MonoidAlgebra.single (g • s) 1)).coeff (g • t) =
          (f (MonoidAlgebra.single s 1)).coeff t := by
      have hf : f (MonoidAlgebra.single (g • s) 1) =
          ofMulAction A G S g (f (MonoidAlgebra.single s 1)) := by
        rw [← f.isIntertwining, ofMulAction_single]
      rw [hf, coeff_ofMulAction, inv_smul_smul]
    refine (Set.finite_iUnion fun ω : orbitRel.Quotient G S ↦
      ((f (MonoidAlgebra.single ω.out 1)).coeff.support.finite_toSet.image fun x ↦
        Quotient.mk (orbitRel G (S × S)) (x, ω.out))).subset ?_
    rintro _ ⟨⟨t, s⟩, hts, rfl⟩
    let ω : orbitRel.Quotient G S := ⟦s⟧
    obtain ⟨g, hg⟩ : ∃ g : G, g • ω.out = s := by
      obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G S) s
      exact ⟨g⁻¹, by simpa [ω] using congrArg (g⁻¹ • ·) hg.symm⟩
    refine Set.mem_iUnion.mpr ⟨ω, g⁻¹ • t, ?_, Quotient.sound ⟨g⁻¹, by simp [← hg]⟩⟩
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    rw [← hsmul g (g⁻¹ • t) ω.out, smul_inv_smul, hg]
    exact hts

@[simp]
theorem ofIntertwiningMap_apply
    (f : (ofMulAction A G S).IntertwiningMap (ofMulAction A G S)) (t s : S) :
    ofIntertwiningMap f (t, s) = (f (MonoidAlgebra.single s 1)).coeff t := (rfl)

variable [∀ x y : S, Finite ↥(orbit (stabilizer G x) y)]

/-- **When `S` has finitely many `G`-orbits, `InvariantKernel A G S` is isomorphic as an
`A`-algebra to the intertwining endomorphisms of `A[S]`.** -/
def toIntertwiningAlgEquiv :
    InvariantKernel A G S ≃ₐ[A]
      (ofMulAction A G S).IntertwiningMap (ofMulAction A G S) where
  toFun := toIntertwiningMap
  invFun := ofIntertwiningMap
  left_inv h := ext fun t s ↦ by simp
  right_inv f := by
    apply IntertwiningMap.ext
    refine MonoidAlgebra.lhom_ext' fun s ↦ LinearMap.ext_ring ?_
    ext t
    simp
  map_mul' := toIntertwiningMap_mul
  map_add' := toIntertwiningMap_add
  commutes' a := IntertwiningMap.ext (LinearMap.ext fun v ↦ toIntertwiningMap_algebraMap a v)

@[simp]
theorem toIntertwiningAlgEquiv_apply (h : InvariantKernel A G S) :
    toIntertwiningAlgEquiv h = h.toIntertwiningMap := (rfl)

@[simp]
theorem toIntertwiningAlgEquiv_symm_apply
    (f : (ofMulAction A G S).IntertwiningMap (ofMulAction A G S)) :
    toIntertwiningAlgEquiv.symm f = ofIntertwiningMap f := (rfl)

/-- **When `S` has finitely many `G`-orbits, `InvariantKernel A G S` is isomorphic as an
`A`-algebra to `End_{A[G]}(A[S])`.** -/
def toModuleEndAlgEquiv :
    InvariantKernel A G S ≃ₐ[A]
      Module.End (MonoidAlgebra A G) (ofMulAction A G S).asModule :=
  toIntertwiningAlgEquiv.trans (IntertwiningMap.equivAlgEnd (ofMulAction A G S))

theorem toModuleEndAlgEquiv_def :
    toModuleEndAlgEquiv (A := A) (G := G) (S := S) =
      toIntertwiningAlgEquiv.trans (IntertwiningMap.equivAlgEnd (ofMulAction A G S)) := (rfl)

@[simp]
theorem toModuleEndAlgEquiv_apply (h : InvariantKernel A G S)
    (v : (ofMulAction A G S).asModule) :
    toModuleEndAlgEquiv h v =
      (ofMulAction A G S).asModuleEquiv.symm (h.toIntertwiningMap v) := (rfl)

@[simp]
theorem toModuleEndAlgEquiv_symm_apply
    (f : Module.End (MonoidAlgebra A G) (ofMulAction A G S).asModule) (t s : S) :
    (toModuleEndAlgEquiv.symm f) (t, s) =
      ((ofMulAction A G S).asModuleEquiv
        (f ((ofMulAction A G S).asModuleEquiv.symm (MonoidAlgebra.single s 1)))).coeff t := (rfl)

end Equiv

section MatrixOrderCheck

/-- Elementary off-diagonal `(0, 1)` kernel on `Fin 2` (with trivial `PUnit`-action), used to
witness the index order `h(t, s)` in the column action on `A[Fin 2]`. -/
def finTwoOffDiag (A : Type*) [Semiring A] : InvariantKernel A PUnit (Fin 2) where
  toFun p := if p = (0, 1) then 1 else 0
  map_smul' _ _ _ := rfl
  finite_orbitSupport' := Set.toFinite _

/-- The `(0, 1)` elementary kernel sends `single 1 1` to `single 0 1` (and not `0`), confirming
that `h` acts on basis columns via `h(t, s)` rather than `h(s, t)`. -/
@[simp]
theorem finTwoOffDiag_toIntertwiningMap_single_one (A : Type*) [CommSemiring A] :
    (finTwoOffDiag A).toIntertwiningMap (MonoidAlgebra.single (1 : Fin 2) 1) =
      MonoidAlgebra.single (0 : Fin 2) 1 := by
  ext t
  fin_cases t <;> simp [finTwoOffDiag, coeff_single]

/-- Conversely, the `(0, 1)` elementary kernel annihilates `single 0 1`. -/
@[simp]
theorem finTwoOffDiag_toIntertwiningMap_single_zero (A : Type*) [CommSemiring A] :
    (finTwoOffDiag A).toIntertwiningMap (MonoidAlgebra.single (0 : Fin 2) 1) = 0 := by
  ext t
  fin_cases t <;> simp [finTwoOffDiag]

end MatrixOrderCheck

end PermutationAction

end InvariantKernel

end TauCeti

end
