/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Rat
public import TauCeti.GroupTheory.Coset.Basic
public import TauCeti.NumberTheory.HeckeRing.Representation
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.Coset
public import TauCeti.RepresentationTheory.HeckeAlgebra.Level
public import TauCeti.RepresentationTheory.RelativeNorm

/-!
# Right Hecke actions on subgroup invariants, Hecke sums, and coset transfers

For a group `G`, a subgroup `U ≤ G`, and a `G`-representation `ρ : Representation A G V` over a
commutative ring `A`, Frobenius reciprocity for the permutation module `A[G ⧸ U]` identifies
`G`-intertwining maps `A[G ⧸ U] → V` with the `U`-invariants
`V^U = Representation.invariants (ρ.comp U.subtype)` by evaluation at the identity coset
(`TauCeti.quotientIntertwiningEquivInvariants`; compare `TauCeti.quotientHomEquivInvariants` for
bundled `Rep` in a single universe).

Precomposition of intertwining maps with endomorphisms of `A[G ⧸ U]` transports through this
identification to a right action of `TauCeti.HeckeAlgebraLevel A G U` — and, whenever every
stabilizer orbit on `G ⧸ U` is finite (in particular whenever `(⊤, U, U)` is a Hecke triple), of
the double-coset kernel algebra `TauCeti.LevelHeckeKernel A G U` — on `V^U`. Explicitly, in
right-coset coordinates (`TauCeti.coe_op_kernel_smul_eq_finsum_rightCoset`),
$$v * h = \sum_{Ug \in U \backslash G} h(1U, gU) \, \rho(g)^{-1} v.$$

To compare this action with `HeckeCoset.heckeSum` (`TauCeti.NumberTheory.HeckeRing.Representation`),
we attach to `v ∈ V` the `A`-linear map `TauCeti.invRegularEval ρ v : A[G] →ₗ[A] V` sending `[x]`
to `ρ(x⁻¹) v`. When `v ∈ V^U`, `invRegularEval ρ v` is `U`-invariant for the left regular
representation on `A[G]`, and evaluating `HeckeCoset.heckeSum` of a double coset `D = [UgU]` at
`[1]` recovers `v * [UgU]` (`TauCeti.heckeSum_leftRegular_invRegularEval_eq_smul`), naturally along
equivariant maps in `V` and under every commutative coefficient homomorphism `A →+* B`
(`TauCeti.invariantsSemilinearMap_op_kernel_smul`,
`TauCeti.invariantsBaseChange_op_heckeCosetKernel_smul`).

On `Multiplicative ℤ` at trivial level `⊥` with the unramified character `ofAdd n ↦ 2^n` on `ℚ`,
both `[ofAdd 1]` on invariants and `invRegularEval` at `ofAdd 1` produce `1 / 2`, whereas applying
`HeckeCoset.heckeSum` directly to the character with `id` gives `2`, pinning the inverse-evaluation
direction (`TauCeti.unramifiedDoublingRep_op_heckeCosetKernel_smul`,
`TauCeti.heckeSum_unramifiedDoublingRep_id`).

Finally, for `U' ≤ U`, the canonical `G`-maps `A[G ⧸ U'] → A[G ⧸ U]` (`gU' ↦ gU`) and
`A[G ⧸ U] → A[G ⧸ U']` (`gU ↦ ∑_{k ∈ U / U'} g k U'`) induce the inclusion `V^U → V^{U'}` and the
integral transfer `tr_{U/U'} : V^{U'} → V^U`, satisfying `tr ∘ incl = [U : U'] • id` and, when
`U'` is normal in `U`, `incl ∘ tr = ∑_{u ∈ U / U'} ρ(u)` as an endomorphism of `V^{U'}`.

## Main definitions

* `TauCeti.leftCosetVector`: `aU ↦ ρ(a) v` for a `U`-fixed vector `v`.
* `TauCeti.quotientIntertwiningEquivInvariants`: `(ofMulAction A G (G ⧸ U)).IntertwiningMap ρ ≃ₗ[A]
  Representation.invariants (ρ.comp U.subtype)`.
* Right module instances of `(HeckeAlgebraLevel A G U)ᵐᵒᵖ` and `(LevelHeckeKernel A G U)ᵐᵒᵖ` on
  `Representation.invariants (ρ.comp U.subtype)`.
* `TauCeti.rightCosetSummand`: the right-coset summand `Ug ↦ h(1U, gU) • ρ(g⁻¹) v`.
* `TauCeti.invRegularEval`: the `A`-linear map `q_v : A[G] →ₗ[A] V` sending `[x]` to `ρ(x⁻¹) v`.
* `TauCeti.quotientProjIntertwining` and `TauCeti.quotientTraceIntertwining`: the coset projection
  and transfer intertwining maps between `A[G ⧸ U']` and `A[G ⧸ U]`, together with the induced maps
  `TauCeti.invariantsInclusion` and `TauCeti.invariantsTrace`.

## References

* [D. Treumann and A. Venkatesh, *Linkage and functoriality*][treumann2016], §2.10,
  (2.10.1)–(2.10.3), pp. 187–188.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971], §3.4.
-/

public noncomputable section

open MulAction MonoidAlgebra Representation DoubleCoset
open scoped Pointwise TensorProduct

namespace TauCeti

section Semiring

variable {A G V : Type*} [Semiring A] [Group G] [AddCommMonoid V] [Module A V]

/-- For a `U`-fixed vector `v : V`, `aU ↦ ρ a v` is well-defined on the left coset space `G ⧸ U`. -/
def leftCosetVector (ρ : Representation A G V) {U : Subgroup G} {v : V}
    (hv : ∀ u : U, ρ u v = v) : G ⧸ U → V :=
  Quotient.lift (fun a : G ↦ ρ a v) fun _ _ hab ↦
    ρ.apply_eq_apply_of_quotientGroup_mk_eq hv (Quotient.sound hab)

@[simp]
theorem leftCosetVector_mk (ρ : Representation A G V) {U : Subgroup G} {v : V}
    (hv : ∀ u : U, ρ u v = v) (a : G) :
    leftCosetVector ρ hv (a : G ⧸ U) = ρ a v := (rfl)

/-- A `U`-fixed vector `v` defines a `G`-intertwining map `A[G ⧸ U] → V` sending `[aU]` to
`ρ(a) v`. -/
def quotientIntertwiningOfInvariant (ρ : Representation A G V) {U : Subgroup G} {v : V}
    (hv : ∀ u : U, ρ u v = v) :
    (ofMulAction A G (G ⧸ U)).IntertwiningMap ρ where
  toLinearMap :=
    Finsupp.linearCombination A (leftCosetVector ρ hv) ∘ₗ (coeffLinearEquiv A).toLinearMap
  isIntertwining' g := by
    refine MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext fun c ↦ ?_
    induction q using QuotientGroup.induction_on with | H a =>
    simp [smul_eq_mul]

@[simp]
theorem quotientIntertwiningOfInvariant_single (ρ : Representation A G V) {U : Subgroup G} {v : V}
    (hv : ∀ u : U, ρ u v = v) (q : G ⧸ U) (c : A) :
    quotientIntertwiningOfInvariant ρ hv (MonoidAlgebra.single q c) =
      c • leftCosetVector ρ hv q := by
  simp [quotientIntertwiningOfInvariant]

/-- **The inverse regular evaluation map `q_v : A[G] →ₗ[A] V`**, sending `[x]` to `ρ(x⁻¹) v`. -/
def invRegularEval (ρ : Representation A G V) (v : V) : MonoidAlgebra A G →ₗ[A] V :=
  Finsupp.linearCombination A (fun x : G ↦ ρ x⁻¹ v) ∘ₗ (coeffLinearEquiv A).toLinearMap

@[simp]
theorem invRegularEval_single (ρ : Representation A G V) (v : V) (x : G) (c : A) :
    invRegularEval ρ v (MonoidAlgebra.single x c) = c • ρ x⁻¹ v := by
  simp [invRegularEval]

/-- When `v` is fixed by `U`, `invRegularEval ρ v` is `U`-invariant for the left regular
representation of `G` on `A[G]` restricted to `⊤ : Submonoid G`. -/
theorem invRegularEval_comp_leftRegular_of_mem (ρ : Representation A G V) {U : Subgroup G} {v : V}
    (hv : ∀ u : U, ρ u v = v) {u : G} (hu : u ∈ U) :
    invRegularEval ρ v ∘ₗ
        ((Representation.leftRegular A G).comp (⊤ : Submonoid G).subtype) ⟨u, trivial⟩ =
      invRegularEval ρ v := by
  refine MonoidAlgebra.lhom_ext' fun x ↦ LinearMap.ext fun c ↦ ?_
  simp only [LinearMap.comp_apply, lsingle_apply, MonoidHom.comp_apply, Submonoid.coe_subtype,
    ofMulAction_single, smul_eq_mul, invRegularEval_single, mul_inv_rev, map_mul,
    Module.End.mul_eq_comp]
  rw [hv ⟨u⁻¹, U.inv_mem hu⟩]

end Semiring

section FrobeniusAndRightAction

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]

/-- Evaluating a `U`-invariant vector `v : Representation.invariants (ρ.comp U.subtype)` at any
`u : U` leaves `v.1` fixed. -/
theorem invariants_comp_subtype_apply {ρ : Representation A G V} {U : Subgroup G}
    (v : Representation.invariants (ρ.comp U.subtype)) (u : U) :
    ρ u v.1 = v.1 :=
  (Representation.mem_invariants (ρ.comp U.subtype) v.1).mp v.2 u

/-- Every vector is invariant under restriction to the trivial subgroup `⊥`. -/
theorem mem_invariants_comp_bot_subtype (ρ : Representation A G V) (x : V) :
    x ∈ Representation.invariants (ρ.comp (⊥ : Subgroup G).subtype) := fun u ↦ by
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.mem_bot.mp u.2]
  simp

/-- **Frobenius reciprocity for the coset permutation module `A[G ⧸ U]`.** `G`-intertwining maps
`A[G ⧸ U] → V` correspond `A`-linearly to the `U`-invariants
`Representation.invariants (ρ.comp U.subtype)` via evaluation at the identity coset `1U`.

Unlike `TauCeti.quotientHomEquivInvariants`, which works with bundled `Rep` in a single universe,
this equivalence allows `A`, `G`, and `V` to live in independent universes. -/
def quotientIntertwiningEquivInvariants (ρ : Representation A G V) (U : Subgroup G) :
    (ofMulAction A G (G ⧸ U)).IntertwiningMap ρ ≃ₗ[A]
      Representation.invariants (ρ.comp U.subtype) where
  toFun f :=
    ⟨f (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1), fun u ↦ by
      have hu : (u : G) • ((1 : G) : G ⧸ U) = ((1 : G) : G ⧸ U) := by
        rw [Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq]
        simp
      have hcomm :=
        IntertwiningMap.isIntertwining (ofMulAction A G (G ⧸ U)) ρ f u
          (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1)
      simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, ofMulAction_single, hu]
        using hcomm.symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := quotientIntertwiningOfInvariant ρ (invariants_comp_subtype_apply v)
  left_inv f := by
    apply IntertwiningMap.ext
    refine MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
    induction q using QuotientGroup.induction_on with | H a =>
    have ha : MonoidAlgebra.single (a : G ⧸ U) (1 : A) =
        ofMulAction A G (G ⧸ U) a (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1) := by
      rw [ofMulAction_single, Quotient.smul_coe, smul_eq_mul, mul_one]
    have hcomm :=
      IntertwiningMap.isIntertwining (ofMulAction A G (G ⧸ U)) ρ f a
        (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1)
    simp only [LinearMap.comp_apply, lsingle_apply, IntertwiningMap.coe_toLinearMap,
      quotientIntertwiningOfInvariant_single, leftCosetVector_mk, one_smul]
    rw [ha, hcomm]
  right_inv v := Subtype.ext (by simp)

@[simp]
theorem coe_quotientIntertwiningEquivInvariants_apply (ρ : Representation A G V) (U : Subgroup G)
    (f : (ofMulAction A G (G ⧸ U)).IntertwiningMap ρ) :
    (quotientIntertwiningEquivInvariants ρ U f : V) =
      f (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1) := (rfl)

@[simp]
theorem quotientIntertwiningEquivInvariants_symm_apply_single (ρ : Representation A G V)
    (U : Subgroup G) (v : Representation.invariants (ρ.comp U.subtype)) (a : G) (c : A) :
    (quotientIntertwiningEquivInvariants ρ U).symm v (MonoidAlgebra.single (a : G ⧸ U) c) =
      c • ρ a v.1 :=
  (quotientIntertwiningOfInvariant_single ρ
    (invariants_comp_subtype_apply v) (a : G ⧸ U) c).trans (by simp)

/-- Right precomposition on `σ.IntertwiningMap ρ` as an `A`-algebra homomorphism from
`(σ.IntertwiningMap σ)ᵐᵒᵖ` to `Module.End A (σ.IntertwiningMap ρ)`. -/
def precompIntertwiningAlgHom {W : Type*} [AddCommMonoid W] [Module A W]
    (σ : Representation A G W) (ρ : Representation A G V) :
    (σ.IntertwiningMap σ)ᵐᵒᵖ →ₐ[A] Module.End A (σ.IntertwiningMap ρ) :=
  AlgHom.ofLinearMap
    (((IntertwiningMap.llcomp σ σ ρ).flip).comp (MulOpposite.opLinearEquiv A).symm.toLinearMap)
    (LinearMap.ext fun _ ↦ IntertwiningMap.ext (LinearMap.ext fun _ ↦ rfl))
    (fun _ _ ↦ LinearMap.ext fun _ ↦ IntertwiningMap.ext (LinearMap.ext fun _ ↦ rfl))

@[simp]
theorem precompIntertwiningAlgHom_apply {W : Type*} [AddCommMonoid W] [Module A W]
    (σ : Representation A G W) (ρ : Representation A G V)
    (φ : (σ.IntertwiningMap σ)ᵐᵒᵖ) (f : σ.IntertwiningMap ρ) :
    precompIntertwiningAlgHom σ ρ φ f = f.comp φ.unop := (rfl)

/-- Precomposing `f : A[G ⧸ U] →_G V` on the right with an intertwining endomorphism of `A[G ⧸ U]`,
transported to `Representation.invariants (ρ.comp U.subtype)` as an `A`-algebra homomorphism from
the opposite endomorphism algebra. -/
def invariantsPrecompAlgHom (ρ : Representation A G V) (U : Subgroup G) :
    ((ofMulAction A G (G ⧸ U)).IntertwiningMap (ofMulAction A G (G ⧸ U)))ᵐᵒᵖ →ₐ[A]
      Module.End A (Representation.invariants (ρ.comp U.subtype)) :=
  ((quotientIntertwiningEquivInvariants ρ U).conjAlgEquiv A).toAlgHom.comp
    (precompIntertwiningAlgHom (ofMulAction A G (G ⧸ U)) ρ)

@[simp]
theorem invariantsPrecompAlgHom_apply (ρ : Representation A G V) (U : Subgroup G)
    (φ : ((ofMulAction A G (G ⧸ U)).IntertwiningMap (ofMulAction A G (G ⧸ U)))ᵐᵒᵖ)
    (v : Representation.invariants (ρ.comp U.subtype)) :
    invariantsPrecompAlgHom ρ U φ v =
      quotientIntertwiningEquivInvariants ρ U
        (((quotientIntertwiningEquivInvariants ρ U).symm v).comp φ.unop) := (rfl)

/-- Right action of `HeckeAlgebraLevel A G U = End_{A[G]}(A[G ⧸ U])` on
`Representation.invariants (ρ.comp U.subtype)` via precomposition on `Hom_G(A[G ⧸ U], V)`. -/
def invariantsHeckeLevelAlgHom (ρ : Representation A G V) (U : Subgroup G) :
    (HeckeAlgebraLevel A G U)ᵐᵒᵖ →ₐ[A]
      Module.End A (Representation.invariants (ρ.comp U.subtype)) :=
  (invariantsPrecompAlgHom ρ U).comp
    (IntertwiningMap.equivAlgEnd (ofMulAction A G (G ⧸ U))).symm.op.toAlgHom

theorem invariantsHeckeLevelAlgHom_def (ρ : Representation A G V) (U : Subgroup G) :
    invariantsHeckeLevelAlgHom ρ U =
      (invariantsPrecompAlgHom ρ U).comp
        (IntertwiningMap.equivAlgEnd (ofMulAction A G (G ⧸ U))).symm.op.toAlgHom := (rfl)

/-- Every space of `U`-invariants `Representation.invariants (ρ.comp U.subtype)` is canonically a
right `HeckeAlgebraLevel A G U`-module. -/
instance instModuleOpHeckeAlgebraLevelInvariants (ρ : Representation A G V) (U : Subgroup G) :
    Module (HeckeAlgebraLevel A G U)ᵐᵒᵖ (Representation.invariants (ρ.comp U.subtype)) :=
  Module.compHom _ (invariantsHeckeLevelAlgHom ρ U).toRingHom

instance instSMulCommClassHeckeAlgebraLevelInvariants (ρ : Representation A G V) (U : Subgroup G) :
    SMulCommClass A (HeckeAlgebraLevel A G U)ᵐᵒᵖ
      (Representation.invariants (ρ.comp U.subtype)) where
  smul_comm a φ v := ((invariantsHeckeLevelAlgHom ρ U φ).map_smul a v).symm

theorem coe_op_heckeAlgebraLevel_smul (ρ : Representation A G V) (U : Subgroup G)
    (f : HeckeAlgebraLevel A G U) (v : Representation.invariants (ρ.comp U.subtype)) :
    ((MulOpposite.op f • v : Representation.invariants (ρ.comp U.subtype)) : V) =
      (quotientIntertwiningEquivInvariants ρ U).symm v
        (((IntertwiningMap.equivAlgEnd (ofMulAction A G (G ⧸ U))).symm f)
          (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1)) := by
  -- Unfold the `Module.compHom` scalar action to `invariantsHeckeLevelAlgHom`.
  change ((invariantsHeckeLevelAlgHom ρ U (MulOpposite.op f) v :
    Representation.invariants (ρ.comp U.subtype)) : V) = _
  simp [invariantsHeckeLevelAlgHom_def]

section KernelAction

/-- Right action of `LevelHeckeKernel A G U` on `Representation.invariants (ρ.comp U.subtype)` as
an `A`-algebra homomorphism from `(LevelHeckeKernel A G U)ᵐᵒᵖ`. -/
def invariantsKernelAlgHom (ρ : Representation A G V) (U : Subgroup G)
    [∀ x y : G ⧸ U, Finite ↥(orbit (stabilizer G x) y)] :
    (LevelHeckeKernel A G U)ᵐᵒᵖ →ₐ[A]
      Module.End A (Representation.invariants (ρ.comp U.subtype)) :=
  (invariantsPrecompAlgHom ρ U).comp InvariantKernel.toIntertwiningAlgEquiv.op.toAlgHom

theorem invariantsKernelAlgHom_def (ρ : Representation A G V) (U : Subgroup G)
    [∀ x y : G ⧸ U, Finite ↥(orbit (stabilizer G x) y)] :
    invariantsKernelAlgHom ρ U =
      (invariantsPrecompAlgHom ρ U).comp InvariantKernel.toIntertwiningAlgEquiv.op.toAlgHom :=
  (rfl)

/-- Whenever every stabilizer orbit on `G ⧸ U` is finite — in particular whenever `(⊤, U, U)` is a
Hecke triple — `Representation.invariants (ρ.comp U.subtype)` is a right
`LevelHeckeKernel A G U`-module. -/
instance instModuleOpLevelHeckeKernelInvariants (ρ : Representation A G V) (U : Subgroup G)
    [∀ x y : G ⧸ U, Finite ↥(orbit (stabilizer G x) y)] :
    Module (LevelHeckeKernel A G U)ᵐᵒᵖ (Representation.invariants (ρ.comp U.subtype)) :=
  Module.compHom _ (invariantsKernelAlgHom ρ U).toRingHom

instance instSMulCommClassLevelHeckeKernelInvariants (ρ : Representation A G V) (U : Subgroup G)
    [∀ x y : G ⧸ U, Finite ↥(orbit (stabilizer G x) y)] :
    SMulCommClass A (LevelHeckeKernel A G U)ᵐᵒᵖ
      (Representation.invariants (ρ.comp U.subtype)) where
  smul_comm a h v := ((invariantsKernelAlgHom ρ U h).map_smul a v).symm

theorem coe_op_kernel_smul (ρ : Representation A G V) {U : Subgroup G}
    [∀ x y : G ⧸ U, Finite ↥(orbit (stabilizer G x) y)]
    (h : LevelHeckeKernel A G U) (v : Representation.invariants (ρ.comp U.subtype)) :
    ((MulOpposite.op h • v : Representation.invariants (ρ.comp U.subtype)) : V) =
      (quotientIntertwiningEquivInvariants ρ U).symm v
        (h.toIntertwiningMap (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1)) := by
  -- Unfold the `Module.compHom` scalar action to `invariantsKernelAlgHom`.
  change ((invariantsKernelAlgHom ρ U (MulOpposite.op h) v :
    Representation.invariants (ρ.comp U.subtype)) : V) = _
  simp [invariantsKernelAlgHom_def]

/-- Compatibility of the right `LevelHeckeKernel` and `HeckeAlgebraLevel` actions under
`levelHeckeAlgEquiv`. -/
@[simp]
theorem op_levelHeckeAlgEquiv_smul (ρ : Representation A G V) (U : Subgroup G)
    [IsHeckeTriple (⊤ : Submonoid G) U U]
    (h : LevelHeckeKernel A G U) (v : Representation.invariants (ρ.comp U.subtype)) :
    MulOpposite.op (levelHeckeAlgEquiv A G U h) • v = MulOpposite.op h • v := by
  apply Subtype.ext
  rw [coe_op_heckeAlgebraLevel_smul, coe_op_kernel_smul, levelHeckeAlgEquiv_def,
    InvariantKernel.toModuleEndAlgEquiv_def]
  simp

end KernelAction

section RightCosetFormula

/-- The summand `Ug ↦ h(1U, gU) • ρ(g⁻¹) v` on the right coset space
`U \ G = Quotient (QuotientGroup.rightRel U)` attached to a `U`-fixed vector `v` and an invariant
kernel `h : LevelHeckeKernel A G U`. -/
def rightCosetSummand (ρ : Representation A G V) {U : Subgroup G} {v : V}
    (hv : ∀ u : U, ρ u v = v) (h : LevelHeckeKernel A G U)
    (q : Quotient (QuotientGroup.rightRel U)) : V :=
  h (QuotientGroup.quotientRightRelEquivQuotientLeftRel U q, ((1 : G) : G ⧸ U)) •
    leftCosetVector ρ hv (QuotientGroup.quotientRightRelEquivQuotientLeftRel U q)

/-- On the right coset `Ug` of `g : G`, `rightCosetSummand` evaluates to
`h(1U, gU) • ρ(g⁻¹) v`. -/
@[simp]
theorem rightCosetSummand_mk (ρ : Representation A G V) {U : Subgroup G} {v : V}
    (hv : ∀ u : U, ρ u v = v) (h : LevelHeckeKernel A G U) (g : G) :
    rightCosetSummand ρ hv h (Quotient.mk'' g) =
      h (((1 : G) : G ⧸ U), (g : G ⧸ U)) • ρ g⁻¹ v := by
  have hinv := h.map_smul g ((g⁻¹ : G) : G ⧸ U) ((1 : G) : G ⧸ U)
  have h1 : g • ((g⁻¹ : G) : G ⧸ U) = ((1 : G) : G ⧸ U) := by
    rw [Quotient.smul_coe, smul_eq_mul, mul_inv_cancel]
  have h2 : g • ((1 : G) : G ⧸ U) = (g : G ⧸ U) := by
    rw [Quotient.smul_coe, smul_eq_mul, mul_one]
  rw [h1, h2] at hinv
  simp [rightCosetSummand, hinv]

/-- Only finitely many right cosets `Ug ∈ U \ G` contribute a nonzero summand to `v * h`. -/
theorem finite_support_rightCosetSummand (ρ : Representation A G V) {U : Subgroup G}
    [∀ x y : G ⧸ U, Finite ↥(orbit (stabilizer G x) y)]
    {v : V} (hv : ∀ u : U, ρ u v = v) (h : LevelHeckeKernel A G U) :
    (Function.support (rightCosetSummand ρ hv h)).Finite := by
  refine ((h.finite_support_left ((1 : G) : G ⧸ U)).image
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm).subset ?_
  intro q hq
  refine ⟨QuotientGroup.quotientRightRelEquivQuotientLeftRel U q, ?_, by simp⟩
  intro hzero
  exact hq (by simp [rightCosetSummand, hzero])

/-- Expanding `(MulOpposite.op h • v : V)` as a finite `Finset` sum over the column support of `h`
at `1U`. -/
theorem coe_op_kernel_smul_eq_sum_colFinsupp (ρ : Representation A G V) {U : Subgroup G}
    [∀ x y : G ⧸ U, Finite ↥(orbit (stabilizer G x) y)]
    (h : LevelHeckeKernel A G U) (v : Representation.invariants (ρ.comp U.subtype)) :
    ((MulOpposite.op h • v : Representation.invariants (ρ.comp U.subtype)) : V) =
      ∑ t ∈ (h.colFinsupp ((1 : G) : G ⧸ U)).support,
        h (t, ((1 : G) : G ⧸ U)) • leftCosetVector ρ (invariants_comp_subtype_apply v) t := by
  rw [coe_op_kernel_smul, InvariantKernel.toIntertwiningMap_single_one_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  induction t using QuotientGroup.induction_on with | H a =>
  simp

/-- **Explicit right-coset formula for the right Hecke action on `V^U`**:
$$v * h = \sum_{Ug \in U \backslash G} h(1U, gU) \, \rho(g)^{-1} v.$$ -/
theorem coe_op_kernel_smul_eq_finsum_rightCoset (ρ : Representation A G V) {U : Subgroup G}
    [∀ x y : G ⧸ U, Finite ↥(orbit (stabilizer G x) y)]
    (h : LevelHeckeKernel A G U) (v : Representation.invariants (ρ.comp U.subtype)) :
    ((MulOpposite.op h • v : Representation.invariants (ρ.comp U.subtype)) : V) =
      ∑ᶠ q : Quotient (QuotientGroup.rightRel U),
        rightCosetSummand ρ (invariants_comp_subtype_apply v) h q := by
  rw [coe_op_kernel_smul_eq_sum_colFinsupp]
  symm
  have hcomp : rightCosetSummand ρ (invariants_comp_subtype_apply v) h =
      fun q ↦ (fun t ↦ h (t, ((1 : G) : G ⧸ U)) •
        leftCosetVector ρ (invariants_comp_subtype_apply v) t)
        (QuotientGroup.quotientRightRelEquivQuotientLeftRel U q) := rfl
  rw [hcomp, finsum_comp_equiv (QuotientGroup.quotientRightRelEquivQuotientLeftRel U)]
  refine finsum_eq_sum_of_support_subset _ fun t ht ↦ ?_
  rw [Finset.mem_coe, Finsupp.mem_support_iff, InvariantKernel.colFinsupp_apply]
  intro hzero
  exact ht (by simp [hzero])

end RightCosetFormula

section HeckeSumComparison

/-- **Comparison with `HeckeCoset.heckeSum`.** For a Hecke triple `(⊤, U, U)`, a double coset
`D : HeckeCoset ⊤ U U`, and a `U`-invariant vector `v ∈ V^U`, evaluating `HeckeCoset.heckeSum` on
the algebraic left regular representation `A[G]` along `invRegularEval ρ v.1` at `[1]` equals
`v * [D]`. -/
theorem heckeSum_leftRegular_invRegularEval_eq_smul (ρ : Representation A G V) {U : Subgroup G}
    [IsHeckeTriple (⊤ : Submonoid G) U U]
    (D : HeckeCoset (⊤ : Submonoid G) U U) (v : Representation.invariants (ρ.comp U.subtype)) :
    HeckeCoset.heckeSum D ((Representation.leftRegular A G).comp (⊤ : Submonoid G).subtype)
        (Submonoid.mem_top _) le_top (invRegularEval ρ v.1) (MonoidAlgebra.single 1 1) =
      ((MulOpposite.op (heckeCosetKernel A D) • v :
        Representation.invariants (ρ.comp U.subtype)) : V) := by
  have : Fintype (DecompQuotient U U (D.out : G)⁻¹) := Fintype.ofFinite _
  have hfin : Finite ↥(orbit U (((D.out : G)⁻¹ : G) : G ⧸ U)) :=
    Finite.of_equiv (DecompQuotient U U (D.out : G)⁻¹)
      (orbitEquivDecompQuotient U (D.out : G)⁻¹).symm
  have : Fintype ↥(orbit U (((D.out : G)⁻¹ : G) : G ⧸ U)) := Fintype.ofFinite _
  rw [HeckeCoset.heckeSum_eq_sum_of_rightCosets D
      ((Representation.leftRegular A G).comp (⊤ : Submonoid G).subtype) (Submonoid.mem_top _)
      le_top le_top
      (fun u hu ↦
        invRegularEval_comp_leftRegular_of_mem ρ (invariants_comp_subtype_apply v) hu)
      (rightCosetRep D) (fun _ ↦ Submonoid.mem_top _)
      (doubleCoset_eq_iUnion_rightCosetRep D) (op_rightCosetRep_smul_injective D),
    LinearMap.sum_apply, coe_op_kernel_smul, heckeCosetKernel_eq_doubleCosetBasis_out,
    toIntertwiningMap_doubleCosetBasis_single_one, map_sum]
  refine Fintype.sum_equiv (orbitEquivDecompQuotient U (D.out : G)⁻¹).symm _ _ fun w ↦ ?_
  have hw : (((orbitEquivDecompQuotient U (D.out : G)⁻¹).symm w :
        ↥(orbit U (((D.out : G)⁻¹ : G) : G ⧸ U))) : G ⧸ U) =
      (((rightCosetRep D w)⁻¹ : G) : G ⧸ U) := by
    conv_lhs => rw [← QuotientGroup.out_eq' w]
    rw [coe_orbitEquivDecompQuotient_symm_mk, rightCosetRep_def, mul_inv_rev, inv_inv]
  rw [hw, quotientIntertwiningEquivInvariants_symm_apply_single, one_smul]
  simp

/-- Pushing a double-coset basis kernel forward along any ring homomorphism `φ : A →+* B` gives the
corresponding double-coset basis kernel over `B`. -/
@[simp]
theorem mapRingHom_doubleCosetBasis {B : Type*} [CommRing B] (φ : A →+* B) (U : Subgroup G)
    [∀ x y : G ⧸ U, Finite ↥(orbit (stabilizer G x) y)]
    (q : DoubleCoset.Quotient (U : Set G) U) :
    InvariantKernel.mapRingHom φ (doubleCosetBasis A G U q) = doubleCosetBasis B G U q := by
  classical
  induction q using Quotient.inductionOn' with | h g =>
  ext x y
  induction x using QuotientGroup.induction_on with | H a =>
  induction y using QuotientGroup.induction_on with | H b =>
  rw [InvariantKernel.mapRingHom_apply, doubleCosetBasis_apply_mk, doubleCosetBasis_apply_mk]
  split_ifs <;> simp

@[simp]
theorem mapRingHom_heckeCosetKernel {B : Type*} [CommRing B] (φ : A →+* B) {U : Subgroup G}
    [∀ x y : G ⧸ U, Finite ↥(orbit (stabilizer G x) y)]
    (D : HeckeCoset (⊤ : Submonoid G) U U) :
    InvariantKernel.mapRingHom φ (heckeCosetKernel A D) = heckeCosetKernel B D := by
  rw [heckeCosetKernel_def, heckeCosetKernel_def, mapRingHom_doubleCosetBasis]

/-- A `φ`-semilinear `G`-equivariant map `F : V →ₛₗ[φ] W` restricts to a `φ`-semilinear map on
`U`-invariants `V^U →ₛₗ[φ] W^U`. -/
def invariantsSemilinearMap {B W : Type*} [CommRing B] [AddCommGroup W] [Module B W]
    {φ : A →+* B} (ρ : Representation A G V) (σ : Representation B G W) (U : Subgroup G)
    (F : V →ₛₗ[φ] W) (hF : ∀ g x, F (ρ g x) = σ g (F x)) :
    Representation.invariants (ρ.comp U.subtype) →ₛₗ[φ]
      Representation.invariants (σ.comp U.subtype) where
  toFun v := ⟨F v.1, fun u ↦ (hF u v.1).symm.trans (congrArg F (invariants_comp_subtype_apply v u))⟩
  map_add' v₁ v₂ := Subtype.ext (map_add F v₁.1 v₂.1)
  map_smul' a v := Subtype.ext (map_smulₛₗ F a v.1)

@[simp]
theorem coe_invariantsSemilinearMap_apply {B W : Type*} [CommRing B] [AddCommGroup W] [Module B W]
    {φ : A →+* B} (ρ : Representation A G V) (σ : Representation B G W) (U : Subgroup G)
    (F : V →ₛₗ[φ] W) (hF : ∀ g x, F (ρ g x) = σ g (F x))
    (v : Representation.invariants (ρ.comp U.subtype)) :
    (invariantsSemilinearMap ρ σ U F hF v : W) = F v.1 := (rfl)

/-- **Simultaneous naturality in `V` and under commutative ring homomorphisms `φ : A →+* B`.**
Any `φ`-semilinear `G`-equivariant map `F : V →ₛₗ[φ] W` intertwines the right action of `h` on
`V^U` with the right action of `InvariantKernel.mapRingHom φ h` on `W^U`. -/
theorem invariantsSemilinearMap_op_kernel_smul {B W : Type*} [CommRing B] [AddCommGroup W]
    [Module B W] {φ : A →+* B} (ρ : Representation A G V) (σ : Representation B G W)
    {U : Subgroup G} [∀ x y : G ⧸ U, Finite ↥(orbit (stabilizer G x) y)]
    (F : V →ₛₗ[φ] W) (hF : ∀ g x, F (ρ g x) = σ g (F x))
    (h : LevelHeckeKernel A G U) (v : Representation.invariants (ρ.comp U.subtype)) :
    invariantsSemilinearMap ρ σ U F hF (MulOpposite.op h • v) =
      MulOpposite.op (InvariantKernel.mapRingHom φ h) •
        invariantsSemilinearMap ρ σ U F hF v := by
  classical
  apply Subtype.ext
  rw [coe_invariantsSemilinearMap_apply, coe_op_kernel_smul_eq_sum_colFinsupp,
    coe_op_kernel_smul_eq_sum_colFinsupp, map_sum]
  have hsub : ((InvariantKernel.mapRingHom φ h).colFinsupp ((1 : G) : G ⧸ U)).support ⊆
      (h.colFinsupp ((1 : G) : G ⧸ U)).support := by
    intro t ht
    rw [Finsupp.mem_support_iff, InvariantKernel.colFinsupp_apply,
      InvariantKernel.mapRingHom_apply] at ht
    rw [Finsupp.mem_support_iff, InvariantKernel.colFinsupp_apply]
    intro hzero
    exact ht (by rw [hzero, map_zero])
  symm
  refine (Finset.sum_subset hsub fun t _ ht ↦ ?_).trans (Finset.sum_congr rfl fun t _ ↦ ?_)
  · rw [Finsupp.mem_support_iff, not_not, InvariantKernel.colFinsupp_apply,
      InvariantKernel.mapRingHom_apply] at ht
    simp [ht]
  · induction t using QuotientGroup.induction_on with | H a =>
    rw [InvariantKernel.mapRingHom_apply, leftCosetVector_mk, leftCosetVector_mk,
      coe_invariantsSemilinearMap_apply, map_smulₛₗ, hF]

/-- Restriction of a `G`-intertwining map `F : ρ.IntertwiningMap σ` to an `A`-linear map on
`U`-invariants `V^U →ₗ[A] W^U`. -/
def invariantsMap {W : Type*} [AddCommGroup W] [Module A W]
    {ρ : Representation A G V} {σ : Representation A G W}
    (U : Subgroup G) (F : ρ.IntertwiningMap σ) :
    Representation.invariants (ρ.comp U.subtype) →ₗ[A]
      Representation.invariants (σ.comp U.subtype) :=
  invariantsSemilinearMap ρ σ U F.toLinearMap (IntertwiningMap.isIntertwining ρ σ F)

@[simp]
theorem coe_invariantsMap_apply {W : Type*} [AddCommGroup W] [Module A W]
    {ρ : Representation A G V} {σ : Representation A G W}
    (U : Subgroup G) (F : ρ.IntertwiningMap σ)
    (v : Representation.invariants (ρ.comp U.subtype)) :
    (invariantsMap U F v : W) = F v.1 := (rfl)

/-- **Naturality in `V`**: every `G`-intertwining map `F : ρ.IntertwiningMap σ` commutes with the
right `LevelHeckeKernel` action on `U`-invariants. -/
@[simp]
theorem invariantsMap_op_kernel_smul {W : Type*} [AddCommGroup W] [Module A W]
    {ρ : Representation A G V} {σ : Representation A G W}
    {U : Subgroup G} [∀ x y : G ⧸ U, Finite ↥(orbit (stabilizer G x) y)]
    (F : ρ.IntertwiningMap σ) (h : LevelHeckeKernel A G U)
    (v : Representation.invariants (ρ.comp U.subtype)) :
    invariantsMap U F (MulOpposite.op h • v) = MulOpposite.op h • invariantsMap U F v := by
  have key := invariantsSemilinearMap_op_kernel_smul (φ := RingHom.id A) ρ σ F.toLinearMap
    (IntertwiningMap.isIntertwining ρ σ F) h v
  have hid : InvariantKernel.mapRingHom (RingHom.id A) h = h := by
    ext x y
    rw [InvariantKernel.mapRingHom_apply, RingHom.id_apply]
  simpa [invariantsMap, hid] using key

/-- Canonical `A`-linear map `v ↦ 1 ⊗ₜ v` from `V^U` to `(ρ.baseChange B)^U` for any commutative
`A`-algebra `B`. -/
def invariantsBaseChange (B : Type*) [CommRing B] [Algebra A B]
    (ρ : Representation A G V) (U : Subgroup G) :
    Representation.invariants (ρ.comp U.subtype) →ₗ[A]
      Representation.invariants ((ρ.baseChange B).comp U.subtype) where
  toFun v :=
    ⟨(1 : B) ⊗ₜ[A] v.1, fun u ↦ by
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, Representation.baseChange_apply,
        LinearMap.baseChange_tmul]
      exact congrArg ((1 : B) ⊗ₜ[A] ·) (invariants_comp_subtype_apply v u)⟩
  map_add' v₁ v₂ := Subtype.ext (TensorProduct.tmul_add 1 v₁.1 v₂.1)
  map_smul' a v := Subtype.ext (TensorProduct.tmul_smul a (1 : B) v.1)

@[simp]
theorem coe_invariantsBaseChange_apply (B : Type*) [CommRing B] [Algebra A B]
    (ρ : Representation A G V) (U : Subgroup G)
    (v : Representation.invariants (ρ.comp U.subtype)) :
    (invariantsBaseChange B ρ U v : B ⊗[A] V) = (1 : B) ⊗ₜ[A] v.1 := (rfl)

/-- **Compatibility with commutative scalar extension for arbitrary kernels.** -/
theorem invariantsBaseChange_op_kernel_smul (B : Type*) [CommRing B] [Algebra A B]
    (ρ : Representation A G V) {U : Subgroup G}
    [∀ x y : G ⧸ U, Finite ↥(orbit (stabilizer G x) y)]
    (h : LevelHeckeKernel A G U) (v : Representation.invariants (ρ.comp U.subtype)) :
    invariantsBaseChange B ρ U (MulOpposite.op h • v) =
      MulOpposite.op (InvariantKernel.mapRingHom (algebraMap A B) h) •
        invariantsBaseChange B ρ U v := by
  let F : V →ₛₗ[algebraMap A B] B ⊗[A] V :=
    { toFun := fun x ↦ (1 : B) ⊗ₜ[A] x
      map_add' := fun x y ↦ TensorProduct.tmul_add 1 x y
      map_smul' := fun a x ↦
        calc
          (1 : B) ⊗ₜ[A] (a • x) = (a • (1 : B)) ⊗ₜ[A] x :=
            (TensorProduct.smul_tmul a 1 x).symm
          _ = (algebraMap A B a * 1) ⊗ₜ[A] x := by rw [Algebra.smul_def]
          _ = (algebraMap A B a • (1 : B)) ⊗ₜ[A] x := by rw [smul_eq_mul]
          _ = algebraMap A B a • ((1 : B) ⊗ₜ[A] x) := (TensorProduct.smul_tmul' _ _ _).symm }
  have hF (g : G) (x : V) : F (ρ g x) = ρ.baseChange B g (F x) := by
    simp [F, Representation.baseChange_apply]
  have hv : invariantsSemilinearMap ρ (ρ.baseChange B) U F hF v =
      invariantsBaseChange B ρ U v := Subtype.ext rfl
  have key :=
    congrArg Subtype.val (invariantsSemilinearMap_op_kernel_smul ρ (ρ.baseChange B) F hF h v)
  rw [hv, coe_invariantsSemilinearMap_apply] at key
  exact Subtype.ext key

/-- **Compatibility with commutative scalar extension**: for any commutative `A`-algebra `B` and
double coset `D : HeckeCoset ⊤ U U`, `invariantsBaseChange B ρ U` intertwines the right `[D]`-action
on `V^U` with the right `[D]`-action on `(ρ.baseChange B)^U`. -/
@[simp]
theorem invariantsBaseChange_op_heckeCosetKernel_smul (B : Type*) [CommRing B] [Algebra A B]
    (ρ : Representation A G V) {U : Subgroup G} [IsHeckeTriple (⊤ : Submonoid G) U U]
    (D : HeckeCoset (⊤ : Submonoid G) U U)
    (v : Representation.invariants (ρ.comp U.subtype)) :
    invariantsBaseChange B ρ U (MulOpposite.op (heckeCosetKernel A D) • v) =
      MulOpposite.op (heckeCosetKernel B D) • invariantsBaseChange B ρ U v := by
  rw [invariantsBaseChange_op_kernel_smul, mapRingHom_heckeCosetKernel]

end HeckeSumComparison

end FrobeniusAndRightAction

section HeckeSumDirectionCheck

/-- The unramified rational representation of `Multiplicative ℤ` on `ℚ` sending `ofAdd n` to
multiplication by `2 ^ n` (modeling an unramified character with `χ(ϖ) = 2` on the valuation
quotient `Fˣ / O_Fˣ ≃ ℤ`). -/
def unramifiedDoublingRep : Representation ℚ (Multiplicative ℤ) ℚ where
  toFun g := ((2 : ℚ) ^ Multiplicative.toAdd g) • (1 : Module.End ℚ ℚ)
  map_one' := by simp
  map_mul' g₁ g₂ := by
    rw [toAdd_mul, zpow_add₀ (two_ne_zero : (2 : ℚ) ≠ 0), mul_smul, smul_mul_assoc, one_mul]

@[simp]
theorem unramifiedDoublingRep_apply (n : ℤ) (x : ℚ) :
    unramifiedDoublingRep (Multiplicative.ofAdd n) x = (2 : ℚ) ^ n * x := by
  simp [unramifiedDoublingRep]

/-- Direction check 1: `invRegularEval` at the generator `ofAdd 1` produces `1 / 2`. -/
theorem invRegularEval_unramifiedDoublingRep_single_ofAdd_one :
    invRegularEval unramifiedDoublingRep (1 : ℚ)
      (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1) = 1 / 2 := by
  have hinv : (Multiplicative.ofAdd (1 : ℤ))⁻¹ = Multiplicative.ofAdd (-1 : ℤ) := rfl
  rw [invRegularEval_single, hinv, unramifiedDoublingRep_apply]
  simp [zpow_neg, one_div]

/-- Direction check 2: the right operator of `[ofAdd 1]` at trivial level `⊥` acts by `1 / 2` on the
invariant line `1 ∈ ℚ`. -/
theorem unramifiedDoublingRep_op_heckeCosetKernel_smul :
    let D : HeckeCoset (⊤ : Submonoid (Multiplicative ℤ))
        (⊥ : Subgroup (Multiplicative ℤ)) (⊥ : Subgroup (Multiplicative ℤ)) :=
      HeckeCoset.mk _ _ ⟨Multiplicative.ofAdd (1 : ℤ), trivial⟩
    let v : Representation.invariants
        (unramifiedDoublingRep.comp (⊥ : Subgroup (Multiplicative ℤ)).subtype) :=
      ⟨1, mem_invariants_comp_bot_subtype unramifiedDoublingRep 1⟩
    ((MulOpposite.op (heckeCosetKernel ℚ D) • v :
        Representation.invariants
          (unramifiedDoublingRep.comp (⊥ : Subgroup (Multiplicative ℤ)).subtype)) : ℚ) =
      1 / 2 := by
  intro D v
  rw [coe_op_kernel_smul, heckeCosetKernel_mk,
    toIntertwiningMap_doubleCosetBasis_multiplicativeInt_single_one,
    quotientIntertwiningEquivInvariants_symm_apply_single, one_smul,
    unramifiedDoublingRep_apply (-1) v.1]
  simp [v, zpow_neg, one_div]

/-- Direction check 3: by contrast, applying `HeckeCoset.heckeSum` directly to
`unramifiedDoublingRep` itself with `q = id` gives `2` rather than `1 / 2`. -/
theorem heckeSum_unramifiedDoublingRep_id :
    let D : HeckeCoset (⊤ : Submonoid (Multiplicative ℤ))
        (⊥ : Subgroup (Multiplicative ℤ)) (⊥ : Subgroup (Multiplicative ℤ)) :=
      HeckeCoset.mk _ _ ⟨Multiplicative.ofAdd (1 : ℤ), trivial⟩
    HeckeCoset.heckeSum D (unramifiedDoublingRep.comp (⊤ : Submonoid (Multiplicative ℤ)).subtype)
      (Submonoid.mem_top _) le_top LinearMap.id (1 : ℚ) = 2 := by
  intro D
  have : Fintype
      (DecompQuotient (⊥ : Subgroup (Multiplicative ℤ)) (⊥ : Subgroup (Multiplicative ℤ))
        (D.out : Multiplicative ℤ)⁻¹) := Fintype.ofFinite _
  have hsub : Subsingleton
      (DecompQuotient (⊥ : Subgroup (Multiplicative ℤ)) (⊥ : Subgroup (Multiplicative ℤ))
        (D.out : Multiplicative ℤ)⁻¹) :=
    Quotient.instSubsingletonQuotient _
  let q₀ : DecompQuotient (⊥ : Subgroup (Multiplicative ℤ)) (⊥ : Subgroup (Multiplicative ℤ))
      (D.out : Multiplicative ℤ)⁻¹ := QuotientGroup.mk 1
  have hinv (γ : Multiplicative ℤ) (hγ : γ ∈ (⊥ : Subgroup (Multiplicative ℤ))) :
      LinearMap.id ∘ₗ
        (unramifiedDoublingRep.comp (⊤ : Submonoid (Multiplicative ℤ)).subtype) ⟨γ, trivial⟩ =
        LinearMap.id := by
    rw [Subgroup.mem_bot.mp hγ]
    apply LinearMap.ext
    intro x
    simp
  rw [HeckeCoset.heckeSum_eq_sum_of_rightCosets D _ (Submonoid.mem_top _) le_top le_top hinv
      (rightCosetRep D) (fun _ ↦ Submonoid.mem_top _)
      (doubleCoset_eq_iUnion_rightCosetRep D) (op_rightCosetRep_smul_injective D),
    LinearMap.sum_apply,
    Finset.sum_eq_single q₀ (fun b _ hb ↦ (hb (Subsingleton.elim b q₀)).elim)
      (fun h ↦ (h (Finset.mem_univ q₀)).elim)]
  have hd : (D.out : Multiplicative ℤ) = Multiplicative.ofAdd (1 : ℤ) := by
    have hmem : (D.out : Multiplicative ℤ) ∈ DoubleCoset.doubleCoset
        (Multiplicative.ofAdd (1 : ℤ)) (⊥ : Subgroup (Multiplicative ℤ))
        (⊥ : Subgroup (Multiplicative ℤ)) := by
      have heq := HeckeCoset.eq_iff.mp (Quotient.out_eq' D)
      exact heq ▸ DoubleCoset.mem_doubleCoset_self _ _ _
    obtain ⟨u₁, hu₁, u₂, hu₂, hprod⟩ := DoubleCoset.mem_doubleCoset.mp hmem
    rw [Subgroup.mem_bot.mp hu₁, Subgroup.mem_bot.mp hu₂, one_mul, mul_one] at hprod
    exact hprod
  have hw : (q₀.out : Multiplicative ℤ) = 1 := Subgroup.mem_bot.mp q₀.out.2
  have hrep : rightCosetRep D q₀ = Multiplicative.ofAdd (1 : ℤ) := by
    rw [rightCosetRep_def, hw, inv_one, mul_one, hd]
  simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq, MonoidHom.comp_apply,
    Submonoid.coe_subtype, hrep, unramifiedDoublingRep_apply, zpow_one, mul_one]

end HeckeSumDirectionCheck

section CosetTransfers

variable {G : Type*} [Group G] {U' U : Subgroup G}

/-- The canonical `G`-equivariant projection `G ⧸ U' → G ⧸ U` for `U' ≤ U`. -/
def quotientMapOfLe (hle : U' ≤ U) : G ⧸ U' → G ⧸ U :=
  Quotient.map' id fun _ _ hab ↦
    QuotientGroup.leftRel_apply.mpr (hle (QuotientGroup.leftRel_apply.mp hab))

@[simp]
theorem quotientMapOfLe_mk (hle : U' ≤ U) (g : G) :
    quotientMapOfLe hle (g : G ⧸ U') = (g : G ⧸ U) := (rfl)

theorem quotientMapOfLe_smul (hle : U' ≤ U) (g : G) (q : G ⧸ U') :
    quotientMapOfLe hle (g • q) = g • quotientMapOfLe hle q := by
  induction q using QuotientGroup.induction_on with | H a =>
  rfl

/-- **The coset projection intertwining map `A[G ⧸ U'] →_G A[G ⧸ U]`** sending `[gU']` to `[gU]`
for `U' ≤ U`. -/
def quotientProjIntertwining (A : Type*) [Semiring A] (hle : U' ≤ U) :
    (ofMulAction A G (G ⧸ U')).IntertwiningMap (ofMulAction A G (G ⧸ U)) where
  toLinearMap :=
    (coeffLinearEquiv A).symm.toLinearMap ∘ₗ
      Finsupp.lmapDomain A A (quotientMapOfLe hle) ∘ₗ
      (coeffLinearEquiv A).toLinearMap
  isIntertwining' g := by
    refine MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext fun c ↦ ?_
    simp [quotientMapOfLe_smul]

@[simp]
theorem quotientProjIntertwining_single {A : Type*} [Semiring A] (hle : U' ≤ U) (g : G) (c : A) :
    quotientProjIntertwining A hle (MonoidAlgebra.single (g : G ⧸ U') c) =
      MonoidAlgebra.single (g : G ⧸ U) c := by
  simp [quotientProjIntertwining]

/-- Well-definedness of `gU ↦ ∑ᶠ k : U ⧸ U'.subgroupOf U, single ((g * k.out : G) : G ⧸ U') 1` on
the left coset space `G ⧸ U`. -/
private def quotientTraceOnCosets (A : Type*) [Semiring A] (U' U : Subgroup G) :
    G ⧸ U → MonoidAlgebra A (G ⧸ U') :=
  Quotient.lift
    (fun g : G ↦ ∑ᶠ k : U ⧸ U'.subgroupOf U,
      MonoidAlgebra.single ((g * (k.out : G) : G) : G ⧸ U') (1 : A))
    fun g₁ g₂ hab ↦ by
      let u : U := ⟨g₁⁻¹ * g₂, QuotientGroup.leftRel_apply.mp hab⟩
      have hg₂ : g₂ = g₁ * (u : G) := by simp [u]
      rw [← finsum_comp_equiv (MulAction.toPerm u)]
      refine finsum_congr fun k ↦ ?_
      rw [MulAction.toPerm_apply, QuotientGroup.mk_mul_out_smul g₁ u k, hg₂]

@[simp]
private theorem quotientTraceOnCosets_mk {A : Type*} [Semiring A] (U' U : Subgroup G) (g : G) :
    quotientTraceOnCosets A U' U (g : G ⧸ U) =
      ∑ᶠ k : U ⧸ U'.subgroupOf U,
        MonoidAlgebra.single ((g * (k.out : G) : G) : G ⧸ U') (1 : A) := (rfl)

/-- **The integral coset transfer intertwining map `A[G ⧸ U] →_G A[G ⧸ U']`** sending `[gU]` to
`∑_{k ∈ U / U'} [g k U']` for `U' ≤ U` of finite relative index in `U`. -/
def quotientTraceIntertwining (A : Type*) [CommSemiring A] (_hle : U' ≤ U)
    [Finite (U ⧸ U'.subgroupOf U)] :
    (ofMulAction A G (G ⧸ U)).IntertwiningMap (ofMulAction A G (G ⧸ U')) where
  toLinearMap :=
    Finsupp.linearCombination A (quotientTraceOnCosets A U' U) ∘ₗ
      (coeffLinearEquiv A).toLinearMap
  isIntertwining' g := by
    refine MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
    induction q using QuotientGroup.induction_on with | H a =>
    simp only [LinearMap.comp_apply, lsingle_apply, ofMulAction_single, Quotient.smul_coe,
      smul_eq_mul, LinearEquiv.coe_coe, coeffLinearEquiv_apply, coeff_single,
      Finsupp.linearCombination_single, one_smul, quotientTraceOnCosets_mk]
    rw [_root_.map_finsum (ofMulAction A G (G ⧸ U') g) (Set.toFinite _)]
    refine finsum_congr fun k ↦ ?_
    simp [smul_eq_mul, mul_assoc]

/-- Coset-basis specification of `quotientTraceIntertwining`: `[gU]` maps to
`c • ∑ᶠ k : U ⧸ U'.subgroupOf U, [(g * k.out) U']`. -/
@[simp]
theorem quotientTraceIntertwining_single {A : Type*} [CommSemiring A] (hle : U' ≤ U)
    [Finite (U ⧸ U'.subgroupOf U)] (g : G) (c : A) :
    quotientTraceIntertwining A hle (MonoidAlgebra.single (g : G ⧸ U) c) =
      c • ∑ᶠ k : U ⧸ U'.subgroupOf U,
        MonoidAlgebra.single ((g * (k.out : G) : G) : G ⧸ U') (1 : A) := by
  simp [quotientTraceIntertwining]

/-- First composite of the coset transfers: `proj ∘ trace = [U : U'] • id` on `A[G ⧸ U]`. -/
@[simp]
theorem quotientProjIntertwining_comp_quotientTraceIntertwining {A : Type*} [CommSemiring A]
    (hle : U' ≤ U) [Finite (U ⧸ U'.subgroupOf U)] :
    (quotientProjIntertwining A hle).comp (quotientTraceIntertwining A hle) =
      U'.relIndex U • .id (ofMulAction A G (G ⧸ U)) := by
  have : Fintype (U ⧸ U'.subgroupOf U) := Fintype.ofFinite _
  apply IntertwiningMap.ext
  refine MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
  induction q using QuotientGroup.induction_on with | H g =>
  simp only [LinearMap.comp_apply, lsingle_apply, IntertwiningMap.coe_toLinearMap,
    IntertwiningMap.comp_apply, quotientTraceIntertwining_single, one_smul,
    finsum_eq_sum_of_fintype, map_sum, quotientProjIntertwining_single, IntertwiningMap.coe_nsmul,
    Pi.smul_apply, IntertwiningMap.id_apply]
  have hcoset (k : U ⧸ U'.subgroupOf U) : ((g * (k.out : G) : G) : G ⧸ U) = (g : G ⧸ U) :=
    QuotientGroup.mk_mul_of_mem g k.out.2
  simp [hcoset, Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

/-- Second composite of the coset transfers on basis vectors: `(trace ∘ proj) ([gU'])` sums
`[(g * k.out) U']` over `k ∈ U ⧸ U'.subgroupOf U`. -/
theorem quotientTraceIntertwining_comp_quotientProjIntertwining_single {A : Type*} [CommSemiring A]
    (hle : U' ≤ U) [Finite (U ⧸ U'.subgroupOf U)] (g : G) (c : A) :
    (quotientTraceIntertwining A hle).comp (quotientProjIntertwining A hle)
        (MonoidAlgebra.single (g : G ⧸ U') c) =
      c • ∑ᶠ k : U ⧸ U'.subgroupOf U,
        MonoidAlgebra.single ((g * (k.out : G) : G) : G ⧸ U') (1 : A) := by
  simp

section InvariantTransfers

variable {A V : Type*} [CommRing A] [AddCommGroup V] [Module A V]

/-- **The inclusion `V^U →ₗ[A] V^{U'}` for `U' ≤ U`**, induced by precomposition with
`quotientProjIntertwining A hle` under `quotientIntertwiningEquivInvariants`. -/
def invariantsInclusion (ρ : Representation A G V) (hle : U' ≤ U) :
    Representation.invariants (ρ.comp U.subtype) →ₗ[A]
      Representation.invariants (ρ.comp U'.subtype) :=
  (quotientIntertwiningEquivInvariants ρ U').toLinearMap ∘ₗ
    (IntertwiningMap.llcomp (ofMulAction A G (G ⧸ U')) (ofMulAction A G (G ⧸ U)) ρ).flip
      (quotientProjIntertwining A hle) ∘ₗ
    (quotientIntertwiningEquivInvariants ρ U).symm.toLinearMap

theorem invariantsInclusion_apply (ρ : Representation A G V) (hle : U' ≤ U)
    (v : Representation.invariants (ρ.comp U.subtype)) :
    invariantsInclusion ρ hle v =
      quotientIntertwiningEquivInvariants ρ U'
        (((quotientIntertwiningEquivInvariants ρ U).symm v).comp
          (quotientProjIntertwining A hle)) := (rfl)

@[simp]
theorem coe_invariantsInclusion_apply (ρ : Representation A G V) (hle : U' ≤ U)
    (v : Representation.invariants (ρ.comp U.subtype)) :
    (invariantsInclusion ρ hle v : V) = v.1 := by
  rw [invariantsInclusion_apply]
  simp

/-- **The integral trace `tr_{U/U'} : V^{U'} →ₗ[A] V^U` for `U' ≤ U`**, induced by precomposition
with `quotientTraceIntertwining A hle` under `quotientIntertwiningEquivInvariants`. -/
def invariantsTrace (ρ : Representation A G V) (hle : U' ≤ U) [Finite (U ⧸ U'.subgroupOf U)] :
    Representation.invariants (ρ.comp U'.subtype) →ₗ[A]
      Representation.invariants (ρ.comp U.subtype) :=
  (quotientIntertwiningEquivInvariants ρ U).toLinearMap ∘ₗ
    (IntertwiningMap.llcomp (ofMulAction A G (G ⧸ U)) (ofMulAction A G (G ⧸ U')) ρ).flip
      (quotientTraceIntertwining A hle) ∘ₗ
    (quotientIntertwiningEquivInvariants ρ U').symm.toLinearMap

theorem invariantsTrace_apply (ρ : Representation A G V) (hle : U' ≤ U)
    [Finite (U ⧸ U'.subgroupOf U)]
    (v : Representation.invariants (ρ.comp U'.subtype)) :
    invariantsTrace ρ hle v =
      quotientIntertwiningEquivInvariants ρ U
        (((quotientIntertwiningEquivInvariants ρ U').symm v).comp
          (quotientTraceIntertwining A hle)) := (rfl)

/-- Explicit coset-representative formula for `invariantsTrace`:
`tr_{U/U'}(v) = ∑ᶠ k : U ⧸ U'.subgroupOf U, ρ(k.out) v`. -/
theorem coe_invariantsTrace_apply (ρ : Representation A G V) (hle : U' ≤ U)
    [Finite (U ⧸ U'.subgroupOf U)]
    (v : Representation.invariants (ρ.comp U'.subtype)) :
    (invariantsTrace ρ hle v : V) =
      ∑ᶠ k : U ⧸ U'.subgroupOf U, ρ (k.out : G) v.1 := by
  have : Fintype (U ⧸ U'.subgroupOf U) := Fintype.ofFinite _
  rw [invariantsTrace_apply]
  simp only [coe_quotientIntertwiningEquivInvariants_apply, IntertwiningMap.comp_apply,
    quotientTraceIntertwining_single, one_smul, one_mul, finsum_eq_sum_of_fintype, map_sum,
    quotientIntertwiningEquivInvariants_symm_apply_single]

/-- Comparison with `Representation.relNorm` on `ρ.comp U.subtype`. -/
theorem coe_invariantsTrace_eq_relNorm (ρ : Representation A G V) (hle : U' ≤ U)
    [Fintype (U ⧸ U'.subgroupOf U)]
    (v : Representation.invariants (ρ.comp U'.subtype)) :
    (invariantsTrace ρ hle v : V) =
      Representation.relNorm (ρ.comp U.subtype) (U'.subgroupOf U) v.1 := by
  rw [coe_invariantsTrace_apply, finsum_eq_sum_of_fintype, Representation.relNorm_apply]
  rfl

/-- **First transfer composite on invariants**: `tr_{U/U'} ∘ incl = [U : U'] • id` on `V^U`, over
every commutative ring `A` (without any invertibility assumption on `[U : U']`). -/
@[simp]
theorem invariantsTrace_comp_invariantsInclusion (ρ : Representation A G V) (hle : U' ≤ U)
    [Finite (U ⧸ U'.subgroupOf U)] :
    (invariantsTrace ρ hle).comp (invariantsInclusion ρ hle) =
      U'.relIndex U •
        (LinearMap.id : Module.End A (Representation.invariants (ρ.comp U.subtype))) := by
  ext v
  let f := (quotientIntertwiningEquivInvariants ρ U).symm v
  have hcomp :
      (quotientIntertwiningEquivInvariants ρ U').symm (invariantsInclusion ρ hle v) =
        f.comp (quotientProjIntertwining A hle) :=
    (quotientIntertwiningEquivInvariants ρ U').symm_apply_apply _
  have hassoc :
      (f.comp (quotientProjIntertwining A hle)).comp (quotientTraceIntertwining A hle) =
        f.comp ((quotientProjIntertwining A hle).comp (quotientTraceIntertwining A hle)) := rfl
  have hf : quotientIntertwiningEquivInvariants ρ U (U'.relIndex U • f) = U'.relIndex U • v := by
    rw [map_nsmul, LinearEquiv.apply_symm_apply]
  have hsmul : f.comp (U'.relIndex U • .id (ofMulAction A G (G ⧸ U))) = U'.relIndex U • f := by
    apply IntertwiningMap.ext
    refine LinearMap.ext fun x ↦ ?_
    exact map_nsmul f.toLinearMap (U'.relIndex U) x
  have key : invariantsTrace ρ hle (invariantsInclusion ρ hle v) = U'.relIndex U • v := by
    rw [invariantsTrace_apply, hcomp, hassoc,
      quotientProjIntertwining_comp_quotientTraceIntertwining, hsmul, hf]
  exact congrArg Subtype.val key

/-- Iterated invariants along `U'.subgroupOf U ≤ U ≤ G` agree as submodules of `V` with
`U'`-invariants when `U' ≤ U`. -/
theorem invariants_comp_subgroupOf_eq (ρ : Representation A G V) (hle : U' ≤ U) :
    Representation.invariants ((ρ.comp U.subtype).comp (U'.subgroupOf U).subtype) =
      Representation.invariants (ρ.comp U'.subtype) := by
  ext x
  simp only [mem_invariants, MonoidHom.comp_apply, Subgroup.coe_subtype]
  exact ⟨fun h u' ↦ h ⟨⟨u', hle u'.2⟩, u'.2⟩, fun h u ↦ h ⟨u.1, u.2⟩⟩

/-- **Second transfer composite on invariants when `U'` is normal in `U`**: `incl ∘ tr_{U/U'}`
equals the group norm `∑ u : U ⧸ U'.subgroupOf U, ρ(u)` of the residual `U ⧸ U'`-action on
`V^{U'}`. -/
theorem invariantsInclusion_comp_invariantsTrace_eq_norm (ρ : Representation A G V) (hle : U' ≤ U)
    [(U'.subgroupOf U).Normal] [Fintype (U ⧸ U'.subgroupOf U)] :
    (invariantsInclusion ρ hle).comp (invariantsTrace ρ hle) =
      (LinearEquiv.ofEq _ _ (invariants_comp_subgroupOf_eq ρ hle)).conj
        (Representation.quotientToInvariants (ρ.comp U.subtype) (U'.subgroupOf U)).norm := by
  ext v
  simp only [LinearMap.comp_apply, coe_invariantsInclusion_apply, coe_invariantsTrace_apply,
    finsum_eq_sum_of_fintype, LinearEquiv.conj_apply_apply, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply, Representation.norm, LinearMap.sum_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rfl

end InvariantTransfers

end CosetTransfers

end TauCeti

end
