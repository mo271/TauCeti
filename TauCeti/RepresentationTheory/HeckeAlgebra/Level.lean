/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Inv
public import TauCeti.GroupTheory.DoubleCoset.Orbits
public import TauCeti.NumberTheory.HeckeRing.Basic
public import TauCeti.RepresentationTheory.HeckeAlgebra.Kernel
public import TauCeti.RepresentationTheory.OfMulAction

/-!
# Level Hecke algebras on coset spaces `G ⧸ U`

Specializing `TauCeti.InvariantKernel` to the transitive coset space `S = G ⧸ U` of a subgroup
`U ≤ G` over a coefficient ring `A`, we obtain the **level Hecke algebra** in both its endomorphism
and double-coset kernel incarnations:

* `TauCeti.HeckeAlgebraLevel A G U`: the `A[G]`-module endomorphism algebra
  `End_{A[G]}(A[G ⧸ U])` of the left permutation module `A[G ⧸ U]`.
* `TauCeti.LevelHeckeKernel A G U`: the invariant-kernel model
  $H(G, U; A) := \operatorname{Fun}_G(G/U \times G/U, A)$, defined over *every* commutative ring `A`
  (including $\mathbb{F}_p$ for $p$-adic groups `G`) with no Haar measure or averaging.

Without any commensurability assumption on `U`, `LevelHeckeKernel A G U` has an `A`-basis
`TauCeti.doubleCosetBasis` indexed by `DoubleCoset.Quotient (U : Set G) U`, sending the double coset
`UgU` to the indicator of the diagonal `G`-orbit of `(1U, gU)`.

When `(⊤, U, U)` is a Hecke triple — in particular for every compact open subgroup `U` of a
topological group with separately continuous multiplication
(`OpenSubgroup.instIsHeckeTripleTopOfCompactSpace`,
`Subgroup.isHeckeTriple_top_of_isCompact_of_isOpen`) and for every normal subgroup `U`
(`Subgroup.instIsHeckeTripleTopOfNormal`) — every stabilizer orbit on `G ⧸ U` is finite, and
`TauCeti.levelHeckeAlgEquiv` identifies `LevelHeckeKernel A G U` with `HeckeAlgebraLevel A G U` as
`A`-algebras. Matrix transposition becomes the double-coset anti-involution sending `[UgU]` to
`MulOpposite.op [Ug⁻¹U]`, and when `U` is normal in `G` we recover
`HeckeAlgebraLevel A G U ≃ₐ[A] MonoidAlgebra A (G ⧸ U)` (`TauCeti.normalHeckeAlgebraLevelAlgEquiv`).

## Main definitions

* `TauCeti.HeckeAlgebraLevel`: `End_{A[G]}(A[G ⧸ U])`.
* `TauCeti.LevelHeckeKernel`: `InvariantKernel A G (G ⧸ U)`.
* `TauCeti.doubleCosetBasis` and `TauCeti.heckeCosetKernel`: the double-coset indicator basis of
  `LevelHeckeKernel A G U`.
* `TauCeti.levelHeckeAlgEquiv`: `LevelHeckeKernel A G U ≃ₐ[A] HeckeAlgebraLevel A G U`.
* `TauCeti.levelHeckeTransposeAlgEquiv`: the anti-involution `[UgU] ↦ [Ug⁻¹U]` on
  `HeckeAlgebraLevel A G U`.
* `TauCeti.normalHeckeAlgebraLevelAlgEquiv`: for `[U.Normal]`,
  `HeckeAlgebraLevel A G U ≃ₐ[A] MonoidAlgebra A (G ⧸ U)`.

## References

* [D. Treumann and A. Venkatesh, *Linkage and functoriality*][treumann2016], §2.10, pp. 187–188.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971], §3.1.
-/

public noncomputable section

open MulAction MonoidAlgebra Representation DoubleCoset
open scoped Pointwise

namespace Subgroup

/-- Every normal subgroup `U` of `G` has commensurator `⊤`, so `(⊤, U, U)` is automatically a Hecke
triple. -/
instance instIsHeckeTripleTopOfNormal {G : Type*} [Group G] (U : Subgroup G) [U.Normal] :
    IsHeckeTriple (⊤ : Submonoid G) U U where
  left_le := le_top
  right_le := le_top
  commensurable := Commensurable.refl U
  le_commensurator_right g _ := by
    -- `U.commensurator` unfolds to `{g | Commensurable (ConjAct.toConjAct g • U) U}`
    change Commensurable (ConjAct.toConjAct g • U) U
    have hnorm : ConjAct.toConjAct g • U = U := by
      ext x
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, ConjAct.smul_def,
        ConjAct.ofConjAct_toConjAct]
      exact ⟨fun h ↦ by simpa [mul_assoc] using ‹U.Normal›.conj_mem _ h g,
        fun h ↦ ‹U.Normal›.conj_mem _ h g⁻¹⟩
    rw [hnorm]

end Subgroup

namespace TauCeti

/-- The level Hecke algebra as endomorphisms of the left permutation module `A[G ⧸ U]`. -/
abbrev HeckeAlgebraLevel (A G : Type*) [CommSemiring A] [Group G] (U : Subgroup G) :=
  Module.End (MonoidAlgebra A G) (_root_.Representation.ofMulAction A G (G ⧸ U)).asModule

/-- The kernel presentation $H(G, U; A) = \operatorname{Fun}_G(G/U \times G/U, A)$ of the level
Hecke algebra. -/
abbrev LevelHeckeKernel (A G : Type*) [Zero A] [Group G] (U : Subgroup G) :=
  InvariantKernel A G (G ⧸ U)

section CosetOrbits

variable {G : Type*} [Group G] (U : Subgroup G)

/-- Since `G` acts transitively on `G ⧸ U`, the orbit quotient `(G ⧸ U) / G` has a unique point. -/
instance instUniqueOrbitRelQuotientQuotientGroup :
    Unique (orbitRel.Quotient G (G ⧸ U)) where
  default := ⟦((1 : G) : G ⧸ U)⟧
  uniq q := ((pretransitive_iff_subsingleton_quotient G (G ⧸ U)).mp inferInstance).elim q _

/-- The stabilizer in `U` of the left coset `(g : G ⧸ U)` is `(g U g⁻¹) ∩ U`, viewed inside `U`. -/
theorem stabilizer_subgroup_quotientGroup_mk (g : G) :
    stabilizer U ((g : G) : G ⧸ U) = (ConjAct.toConjAct g • U).subgroupOf U := by
  ext u
  rw [mem_stabilizer_iff, Subgroup.smul_def, Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, inv_inv]
  exact ⟨fun h ↦ by simpa [mul_assoc] using U.inv_mem h,
    fun h ↦ by simpa [mul_assoc] using U.inv_mem h⟩

/-- The `U`-orbit of `(g : G ⧸ U)` is in canonical bijection with Shimura's left-coset
decomposition quotient `DecompQuotient U U g = U ⧸ (g U g⁻¹ ∩ U)`. -/
def orbitEquivDecompQuotient (g : G) :
    ↥(orbit U ((g : G) : G ⧸ U)) ≃ DecompQuotient U U g :=
  (orbitEquivQuotientStabilizer U ((g : G) : G ⧸ U)).trans
    (Subgroup.quotientEquivOfEq (stabilizer_subgroup_quotientGroup_mk U g).symm).symm

@[simp]
theorem coe_orbitEquivDecompQuotient_symm_mk {U : Subgroup G} (g : G) (u : U) :
    (((orbitEquivDecompQuotient U g).symm (QuotientGroup.mk u) :
        ↥(orbit U ((g : G) : G ⧸ U))) : G ⧸ U) = (((u : G) * g : G) : G ⧸ U) := by
  simp [orbitEquivDecompQuotient, Subgroup.quotientEquivOfEq_mk, Subgroup.smul_def, smul_eq_mul]

/-- The number of left cosets in `UgU` — equivalently, the cardinality of the `U`-orbit of
`(g : G ⧸ U)` — equals `HeckeCoset.degree`. -/
theorem natCard_orbit_quotientGroup_mk (g : G) :
    Nat.card ↥(orbit U ((g : G) : G ⧸ U)) =
      (HeckeCoset.mk U U (⟨g, trivial⟩ : (⊤ : Submonoid G))).degree := by
  rw [Nat.card_congr (orbitEquivDecompQuotient U g), HeckeCoset.degree_mk]
  rfl

/-- Whenever `(⊤, U, U)` is a Hecke triple, every `(stabilizer G x)`-orbit on `G ⧸ U` is finite. -/
instance instFiniteOrbitStabilizerQuotientGroup [IsHeckeTriple (⊤ : Submonoid G) U U]
    (x y : G ⧸ U) : Finite ↥(orbit (stabilizer G x) y) := by
  induction x using QuotientGroup.induction_on with | H a =>
  suffices hfin : Set.Finite (orbit (stabilizer G ((a : G) : G ⧸ U)) y) from hfin.to_subtype
  obtain ⟨c, hc⟩ : ∃ c : G, ((c : G) : G ⧸ U) = a⁻¹ • y := ⟨(a⁻¹ • y).out, Quotient.out_eq' _⟩
  have hU_fin : Set.Finite (orbit U ((c : G) : G ⧸ U)) := by
    have : Finite (DecompQuotient U U c) :=
      @Finite.of_fintype _
        (Subgroup.fintypeOfIndexNeZero
          (IsHeckeTriple.commensurable_conjAct_right (Δ := ⊤) (H₁ := U) (H₂ := U)
            ⟨c, trivial⟩).1.relIndex_ne_zero)
    have : Finite ↥(orbit U ((c : G) : G ⧸ U)) :=
      Finite.of_equiv (DecompQuotient U U c) (orbitEquivDecompQuotient U c).symm
    exact Set.toFinite _
  refine (hU_fin.image fun z ↦ a • z).subset fun w hw ↦ ?_
  obtain ⟨⟨k, hk⟩, rfl⟩ := hw
  have hka : a⁻¹ * k * a ∈ U := by
    have hfix : k • ((a : G) : G ⧸ U) = ((a : G) : G ⧸ U) := hk
    rw [Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq] at hfix
    simpa [mul_assoc] using U.inv_mem hfix
  refine ⟨(⟨a⁻¹ * k * a, hka⟩ : U) • ((c : G) : G ⧸ U), ⟨⟨a⁻¹ * k * a, hka⟩, rfl⟩, ?_⟩
  dsimp only
  rw [Subgroup.smul_def, Subgroup.smul_def, hc, smul_smul, smul_smul]
  simp [mul_assoc]

end CosetOrbits

section DoubleCosetBasis

variable (A G : Type*) [Semiring A] [Group G] (U : Subgroup G)

/-- **The double-coset basis of `LevelHeckeKernel A G U`.** Each double coset `UgU` in
`DoubleCoset.Quotient (U : Set G) U` contributes the indicator function of the diagonal `G`-orbit
of `(1U, gU)`. -/
def doubleCosetBasis :
    Module.Basis (DoubleCoset.Quotient (U : Set G) U) A (LevelHeckeKernel A G U) :=
  (InvariantKernel.orbitBasis A G (G ⧸ U)).reindex (doubleCosetEquivOrbitQuotient U U).symm

variable {A G U}

/-- Coordinates of `h : LevelHeckeKernel A G U` in `doubleCosetBasis` read the slice `(1U, gU)`. -/
@[simp]
theorem doubleCosetBasis_repr_mk (h : LevelHeckeKernel A G U) (g : G) :
    (doubleCosetBasis A G U).repr h (DoubleCoset.mk U U g) =
      h (((1 : G) : G ⧸ U), (g : G ⧸ U)) := by
  rw [doubleCosetBasis, Module.Basis.repr_reindex_apply, Equiv.symm_symm,
    doubleCosetEquivOrbitQuotient_apply_mk, doubleCosetOrbit_def,
    InvariantKernel.orbitBasis_repr_mk]

open Classical in
/-- Evaluating `[UgU]` at `(xU, yU)` tests whether `x⁻¹ * y ∈ UgU`. -/
@[simp]
theorem doubleCosetBasis_apply_mk (g x y : G) :
    doubleCosetBasis A G U (DoubleCoset.mk U U g) ((x : G ⧸ U), (y : G ⧸ U)) =
      if x⁻¹ * y ∈ DoubleCoset.doubleCoset g (U : Set G) U then 1 else 0 := by
  rw [doubleCosetBasis, Module.Basis.reindex_apply, Equiv.symm_symm,
    doubleCosetEquivOrbitQuotient_apply_mk, InvariantKernel.orbitBasis_apply]
  have horb : (Quotient.mk (orbitRel G ((G ⧸ U) × (G ⧸ U))) ((x : G ⧸ U), (y : G ⧸ U))) =
      doubleCosetOrbit U U (x⁻¹ * y) := by
    rw [doubleCosetOrbit_def]
    exact Quotient.sound (MulAction.orbitRel_apply.mpr ⟨x, Prod.ext (by simp) (by simp)⟩)
  have hiff : (doubleCosetOrbit U U (x⁻¹ * y) = doubleCosetOrbit U U g) ↔
      x⁻¹ * y ∈ DoubleCoset.doubleCoset g (U : Set G) U := by
    rw [doubleCosetOrbit_eq_iff, DoubleCoset.eq, mem_doubleCoset]
    exact ⟨fun ⟨u₁, hu₁, u₂, hu₂, hxy⟩ ↦
        ⟨u₁⁻¹, U.inv_mem hu₁, u₂⁻¹, U.inv_mem hu₂, by simp [hxy, mul_assoc]⟩,
      fun ⟨u₁, hu₁, u₂, hu₂, hxy⟩ ↦
        ⟨u₁⁻¹, U.inv_mem hu₁, u₂⁻¹, U.inv_mem hu₂, by simp [hxy, mul_assoc]⟩⟩
  simp [horb, hiff]

open Classical in
/-- Along the identity first coordinate, `[UgU] (1U, yU)` is the indicator of `y ∈ UgU`. -/
theorem doubleCosetBasis_apply_one_mk (g y : G) :
    doubleCosetBasis A G U (DoubleCoset.mk U U g) (((1 : G) : G ⧸ U), (y : G ⧸ U)) =
      if y ∈ DoubleCoset.doubleCoset g (U : Set G) U then 1 else 0 := by
  simp

open Classical in
/-- Along the identity second coordinate, `[UgU] (xU, 1U)` is the indicator of `x ∈ Ug⁻¹U`. -/
theorem doubleCosetBasis_apply_mk_one (g x : G) :
    doubleCosetBasis A G U (DoubleCoset.mk U U g) ((x : G ⧸ U), ((1 : G) : G ⧸ U)) =
      if x ∈ DoubleCoset.doubleCoset g⁻¹ (U : Set G) U then 1 else 0 := by
  have h := doubleCosetBasis_apply_mk (A := A) (U := U) g x 1
  rw [mul_one] at h
  rw [h, ← DoubleCoset.doubleCoset_inv, Set.mem_inv]

/-- Equivalence between `HeckeCoset (⊤ : Submonoid G) U U` and `DoubleCoset.Quotient (U : Set G) U`,
forgetting the trivial submonoid membership. -/
def heckeCosetEquivDoubleCoset (G : Type*) [Group G] (U : Subgroup G) :
    HeckeCoset (⊤ : Submonoid G) U U ≃ DoubleCoset.Quotient (U : Set G) U where
  toFun := Quotient.lift (fun g : (⊤ : Submonoid G) ↦ DoubleCoset.mk U U (g : G))
    fun g₁ g₂ hab ↦ by
      have hd : DoubleCoset.doubleCoset (g₁ : G) U U = DoubleCoset.doubleCoset (g₂ : G) U U :=
        HeckeCoset.eq_iff.mp (Quotient.sound hab)
      exact DoubleCoset.eq.mpr
        (DoubleCoset.mem_doubleCoset.mp (hd ▸ DoubleCoset.mem_doubleCoset_self U U (g₂ : G)))
  invFun := Quotient.lift (fun g : G ↦ HeckeCoset.mk U U ⟨g, trivial⟩)
    fun g₁ g₂ hab ↦ HeckeCoset.eq_iff.mpr <| by
      obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.eq.mp (Quotient.sound hab)
      ext w
      simp only [DoubleCoset.mem_doubleCoset]
      exact ⟨fun ⟨u₁, hu₁, u₂, hu₂, hw⟩ ↦
          ⟨u₁ * h⁻¹, U.mul_mem hu₁ (U.inv_mem hh), k⁻¹ * u₂, U.mul_mem (U.inv_mem hk) hu₂,
            by simp [hw, mul_assoc]⟩,
        fun ⟨u₁, hu₁, u₂, hu₂, hw⟩ ↦
          ⟨u₁ * h, U.mul_mem hu₁ hh, k * u₂, U.mul_mem hk hu₂, by simp [hw, mul_assoc]⟩⟩
  left_inv D := by
    induction D using HeckeCoset.induction with | h g =>
    cases g; rfl
  right_inv q := by
    induction q using Quotient.inductionOn' with | h g =>
    rfl

@[simp]
theorem heckeCosetEquivDoubleCoset_mk (g : (⊤ : Submonoid G)) :
    heckeCosetEquivDoubleCoset G U (HeckeCoset.mk U U g) = DoubleCoset.mk U U (g : G) := (rfl)

@[simp]
theorem heckeCosetEquivDoubleCoset_symm_mk (g : G) :
    (heckeCosetEquivDoubleCoset G U).symm (DoubleCoset.mk U U g) =
      HeckeCoset.mk U U (⟨g, Submonoid.mem_top g⟩ : (⊤ : Submonoid G)) := (rfl)

/-- The basis kernel `[D]` in `LevelHeckeKernel A G U` attached to `D : HeckeCoset ⊤ U U`. -/
def heckeCosetKernel (A : Type*) [Semiring A] {G : Type*} [Group G] {U : Subgroup G}
    (D : HeckeCoset (⊤ : Submonoid G) U U) : LevelHeckeKernel A G U :=
  doubleCosetBasis A G U (heckeCosetEquivDoubleCoset G U D)

theorem heckeCosetKernel_def (A : Type*) [Semiring A] {G : Type*} [Group G] {U : Subgroup G}
    (D : HeckeCoset (⊤ : Submonoid G) U U) :
    heckeCosetKernel A D = doubleCosetBasis A G U (heckeCosetEquivDoubleCoset G U D) := (rfl)

@[simp]
theorem heckeCosetKernel_mk (g : (⊤ : Submonoid G)) :
    heckeCosetKernel A (HeckeCoset.mk U U g) =
      doubleCosetBasis A G U (DoubleCoset.mk U U (g : G)) := (rfl)

theorem heckeCosetKernel_eq_doubleCosetBasis_out (D : HeckeCoset (⊤ : Submonoid G) U U) :
    heckeCosetKernel A D = doubleCosetBasis A G U (DoubleCoset.mk U U (D.out : G)) := by
  conv_lhs => rw [← Quotient.out_eq' D]
  rfl

open Classical in
theorem heckeCosetKernel_apply_one_mk (D : HeckeCoset (⊤ : Submonoid G) U U) (y : G) :
    heckeCosetKernel A D (((1 : G) : G ⧸ U), (y : G ⧸ U)) =
      if y ∈ DoubleCoset.doubleCoset (D.out : G) (U : Set G) U then 1 else 0 := by
  rw [heckeCosetKernel_eq_doubleCosetBasis_out, doubleCosetBasis_apply_one_mk]

/-- Matrix transposition sends `[UgU]` to `[Ug⁻¹U]`. -/
@[simp]
theorem transpose_doubleCosetBasis_mk (g : G) :
    (doubleCosetBasis A G U (DoubleCoset.mk U U g)).transpose =
      doubleCosetBasis A G U (DoubleCoset.mk U U g⁻¹) := by
  classical
  ext x y
  induction x using QuotientGroup.induction_on with | H a =>
  induction y using QuotientGroup.induction_on with | H b =>
  simp only [InvariantKernel.transpose_apply, doubleCosetBasis_apply_mk,
    ← DoubleCoset.doubleCoset_inv, Set.mem_inv, mul_inv_rev, inv_inv]

end DoubleCosetBasis

section AlgebraEquiv

variable (A G : Type*) [CommSemiring A] [Group G] (U : Subgroup G)
  [IsHeckeTriple (⊤ : Submonoid G) U U]

/-- **Isomorphism between the double-coset kernel algebra `LevelHeckeKernel A G U` and
`HeckeAlgebraLevel A G U = End_{A[G]}(A[G ⧸ U])`.** -/
def levelHeckeAlgEquiv : LevelHeckeKernel A G U ≃ₐ[A] HeckeAlgebraLevel A G U :=
  InvariantKernel.toModuleEndAlgEquiv

theorem levelHeckeAlgEquiv_def :
    levelHeckeAlgEquiv A G U = InvariantKernel.toModuleEndAlgEquiv := (rfl)

variable {A G U}

open Classical in
/-- Acting on the identity coset `[1U]`, `[UgU]` produces the indicator sum of the `U`-orbit of
`g⁻¹U` in `G ⧸ U`. -/
theorem coeff_toIntertwiningMap_doubleCosetBasis_single_one (g : G) (y : G ⧸ U) :
    ((doubleCosetBasis A G U (DoubleCoset.mk U U g)).toIntertwiningMap
      (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1)).coeff y =
      if y ∈ orbit U ((g⁻¹ : G) : G ⧸ U) then 1 else 0 := by
  induction y using QuotientGroup.induction_on with | H x =>
  rw [InvariantKernel.coeff_toIntertwiningMap_single, mul_one, doubleCosetBasis_apply_mk_one,
    mem_doubleCoset_iff_mk_mem_orbit]

/-- Explicit finite sum of `[UgU]` acting on `single ((1 : G) : G ⧸ U) 1` over the `U`-orbit of
`(g⁻¹ : G ⧸ U)`. -/
theorem toIntertwiningMap_doubleCosetBasis_single_one (g : G)
    [Fintype ↥(orbit U ((g⁻¹ : G) : G ⧸ U))] :
    (doubleCosetBasis A G U (DoubleCoset.mk U U g)).toIntertwiningMap
      (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1) =
      ∑ y : ↥(orbit U ((g⁻¹ : G) : G ⧸ U)), MonoidAlgebra.single (y : G ⧸ U) 1 := by
  classical
  ext z
  rw [coeff_toIntertwiningMap_doubleCosetBasis_single_one, coeff_sum, Finsupp.finsetSum_apply]
  by_cases hz : z ∈ orbit U ((g⁻¹ : G) : G ⧸ U)
  · simp only [hz, ↓reduceIte]
    symm
    rw [Finset.sum_eq_single (⟨z, hz⟩ : ↥(orbit U ((g⁻¹ : G) : G ⧸ U)))]
    · simp
    · rintro ⟨y, hy⟩ _ hne
      have hyz : z ≠ y := fun h ↦ hne (Subtype.ext h.symm)
      rw [coeff_single, Finsupp.single_eq_of_ne hyz]
    · intro habs
      exact (habs (Finset.mem_univ _)).elim
  · simp only [hz, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero fun ⟨y, hy⟩ _ ↦ ?_
    have hyz : z ≠ y := fun h ↦ hz (h ▸ hy)
    rw [coeff_single, Finsupp.single_eq_of_ne hyz]

/-- Reading back the `(1U, gU)` kernel entry of `f : HeckeAlgebraLevel A G U` extracts the
`(g⁻¹ : G ⧸ U)`-coefficient of `f ([1U])`. -/
theorem levelHeckeAlgEquiv_symm_apply_one_mk (f : HeckeAlgebraLevel A G U) (g : G) :
    (levelHeckeAlgEquiv A G U).symm f (((1 : G) : G ⧸ U), (g : G ⧸ U)) =
      ((ofMulAction A G (G ⧸ U)).asModuleEquiv
        (f ((ofMulAction A G (G ⧸ U)).asModuleEquiv.symm
          (MonoidAlgebra.single ((1 : G) : G ⧸ U) 1)))).coeff ((g⁻¹ : G) : G ⧸ U) := by
  have hinv :=
    ((levelHeckeAlgEquiv A G U).symm f).map_smul g ((g⁻¹ : G) : G ⧸ U) ((1 : G) : G ⧸ U)
  have h1 : g • ((g⁻¹ : G) : G ⧸ U) = ((1 : G) : G ⧸ U) := by
    rw [Quotient.smul_coe, smul_eq_mul, mul_inv_cancel]
  have h2 : g • ((1 : G) : G ⧸ U) = (g : G ⧸ U) := by
    rw [Quotient.smul_coe, smul_eq_mul, mul_one]
  rw [h1, h2] at hinv
  rw [hinv, levelHeckeAlgEquiv, InvariantKernel.toModuleEndAlgEquiv_symm_apply]

/-- The anti-involution on `LevelHeckeKernel A G U` sends `[UgU]` to `MulOpposite.op [Ug⁻¹U]`. -/
theorem transposeAlgEquiv_doubleCosetBasis_mk (g : G) :
    InvariantKernel.transposeAlgEquiv (doubleCosetBasis A G U (DoubleCoset.mk U U g)) =
      MulOpposite.op (doubleCosetBasis A G U (DoubleCoset.mk U U g⁻¹)) := by
  simp [InvariantKernel.transposeAlgEquiv_apply]

variable (A G U) in
/-- **The double-coset anti-involution on `HeckeAlgebraLevel A G U`**, transported from matrix
transposition on `LevelHeckeKernel A G U`. -/
def levelHeckeTransposeAlgEquiv :
    HeckeAlgebraLevel A G U ≃ₐ[A] (HeckeAlgebraLevel A G U)ᵐᵒᵖ :=
  (levelHeckeAlgEquiv A G U).symm.trans
    (InvariantKernel.transposeAlgEquiv.trans (levelHeckeAlgEquiv A G U).op)

@[simp]
theorem levelHeckeTransposeAlgEquiv_levelHeckeAlgEquiv (h : LevelHeckeKernel A G U) :
    levelHeckeTransposeAlgEquiv A G U (levelHeckeAlgEquiv A G U h) =
      MulOpposite.op (levelHeckeAlgEquiv A G U h.transpose) := by
  simp [levelHeckeTransposeAlgEquiv]

theorem levelHeckeTransposeAlgEquiv_doubleCosetBasis (g : G) :
    levelHeckeTransposeAlgEquiv A G U
        (levelHeckeAlgEquiv A G U (doubleCosetBasis A G U (DoubleCoset.mk U U g))) =
      MulOpposite.op
        (levelHeckeAlgEquiv A G U (doubleCosetBasis A G U (DoubleCoset.mk U U g⁻¹))) := by
  simp

/-- Sign/inversion check on `Multiplicative ℤ` at trivial level: `[ofAdd 1]` sends `single 1 1` to
`single (ofAdd (-1)) 1`. -/
theorem toIntertwiningMap_doubleCosetBasis_multiplicativeInt_single_one :
    (doubleCosetBasis A (Multiplicative ℤ) (⊥ : Subgroup (Multiplicative ℤ))
      (DoubleCoset.mk (⊥ : Subgroup (Multiplicative ℤ)) (⊥ : Subgroup (Multiplicative ℤ))
        (Multiplicative.ofAdd (1 : ℤ)))).toIntertwiningMap
      (MonoidAlgebra.single
        ((1 : Multiplicative ℤ) : Multiplicative ℤ ⧸ (⊥ : Subgroup (Multiplicative ℤ))) 1) =
      MonoidAlgebra.single
        (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
          Multiplicative ℤ ⧸ (⊥ : Subgroup (Multiplicative ℤ)))) 1 := by
  ext y
  classical
  let q : Multiplicative ℤ ⧸ (⊥ : Subgroup (Multiplicative ℤ)) :=
    ((Multiplicative.ofAdd (1 : ℤ))⁻¹ : Multiplicative ℤ)
  -- `Multiplicative.ofAdd (-1)` is definitionally `(Multiplicative.ofAdd 1)⁻¹`.
  change _ = (MonoidAlgebra.single q 1).coeff y
  rw [coeff_toIntertwiningMap_doubleCosetBasis_single_one, coeff_single, Finsupp.single_apply]
  have horb : orbit (⊥ : Subgroup (Multiplicative ℤ)) q = {q} := by
    ext z
    simp only [mem_orbit_iff, Set.mem_singleton_iff]
    refine ⟨?_, fun h ↦ h ▸ ⟨1, one_smul _ _⟩⟩
    rintro ⟨u, rfl⟩
    have hu : u = 1 := Subtype.ext (Subgroup.mem_bot.mp u.2)
    rw [hu, one_smul]
  rw [horb, Set.mem_singleton_iff]
  by_cases hy : y = q <;> simp [hy, eq_comm]

end AlgebraEquiv

section NormalSubgroup

variable (A G : Type*) [CommSemiring A] [Group G] (U : Subgroup G) [U.Normal]

/-- Underlying `A`-linear equivalence `MonoidAlgebra A (G ⧸ U) ≃ₗ[A] LevelHeckeKernel A G U`
sending `p` to `(x, y) ↦ p.coeff (x⁻¹ * y)` when `U` is normal in `G`. -/
def normalLevelLinearEquiv :
    MonoidAlgebra A (G ⧸ U) ≃ₗ[A] LevelHeckeKernel A G U where
  toFun p :=
    { toFun := fun q ↦ p.coeff (q.1⁻¹ * q.2)
      map_smul' := fun g x y ↦ by
        have hsmul : (g • x)⁻¹ * (g • y) = x⁻¹ * y := by
          induction x using QuotientGroup.induction_on with | H a =>
          induction y using QuotientGroup.induction_on with | H b =>
          simp only [Quotient.smul_coe, smul_eq_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
          congr 1
          group
        rw [hsmul]
      finite_orbitSupport' := by
        refine (p.coeff.support.finite_toSet.image fun z ↦
          Quotient.mk (orbitRel G ((G ⧸ U) × (G ⧸ U))) (1, z)).subset ?_
        rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
        refine ⟨x⁻¹ * y, Finsupp.mem_support_iff.mpr hxy, ?_⟩
        induction x using QuotientGroup.induction_on with | H a =>
        induction y using QuotientGroup.induction_on with | H b =>
        exact Quotient.sound (MulAction.orbitRel_apply.mpr ⟨a⁻¹, Prod.ext
          (by simp [smul_eq_mul])
          (by simp [smul_eq_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul])⟩) }
  map_add' _ _ := by ext x z; simp
  map_smul' _ _ := by ext x z; simp
  invFun h :=
    MonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (fun z ↦ h (1, z)) (h.finite_support_right 1))
  left_inv p := by ext z; simp
  right_inv h := by
    ext x y
    simp only [InvariantKernel.coe_mk, Finsupp.ofSupportFinite_coe]
    induction x using QuotientGroup.induction_on with | H a =>
    have hsmul := h.map_smul a 1 (((a : G) : G ⧸ U)⁻¹ * y)
    have ha1 : a • (1 : G ⧸ U) = ((a : G) : G ⧸ U) := by
      rw [← QuotientGroup.mk_one, Quotient.smul_coe, smul_eq_mul, mul_one]
    have ha2 : a • (((a : G) : G ⧸ U)⁻¹ * y) = y := by
      induction y using QuotientGroup.induction_on with | H b =>
      simp [smul_eq_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rw [ha1, ha2] at hsmul
    exact hsmul.symm

@[simp]
theorem normalLevelLinearEquiv_apply (p : MonoidAlgebra A (G ⧸ U)) (x y : G ⧸ U) :
    normalLevelLinearEquiv A G U p (x, y) = p.coeff (x⁻¹ * y) := (rfl)

/-- When `U` is normal in `G`, `MonoidAlgebra A (G ⧸ U)` is isomorphic as an `A`-algebra to
`LevelHeckeKernel A G U` via `p ↦ ((x, y) ↦ p.coeff (x⁻¹ * y))`, sending `single (g : G ⧸ U) 1` to
`[UgU]`. -/
def normalLevelHeckeKernelAlgEquiv :
    MonoidAlgebra A (G ⧸ U) ≃ₐ[A] LevelHeckeKernel A G U :=
  AlgEquiv.ofLinearEquiv (normalLevelLinearEquiv A G U)
    (by
      classical
      ext x z
      simp only [MonoidAlgebra.one_def, normalLevelLinearEquiv_apply, coeff_single,
        Finsupp.single_apply, InvariantKernel.one_apply]
      by_cases hxz : x = z
      · subst hxz; simp
      · have hne : (1 : G ⧸ U) ≠ x⁻¹ * z := fun h ↦ hxz (inv_mul_eq_one.mp h.symm)
        simp [hxz, hne])
    (fun p₁ p₂ ↦ by
      induction p₁ using MonoidAlgebra.induction_linear with
      | zero => simp
      | add u v hu hv => simp [add_mul, hu, hv]
      | single q₁ c₁ =>
        induction p₂ using MonoidAlgebra.induction_linear with
        | zero => simp
        | add u v hu hv => simp [mul_add, hu, hv]
        | single q₂ c₂ =>
          classical
          ext x z
          simp only [single_mul_single, normalLevelLinearEquiv_apply, InvariantKernel.mul_apply,
            coeff_single, Finsupp.single_apply]
          rw [finsum_eq_single _ (x * q₁)]
          · have heq : (q₁ = x⁻¹ * (x * q₁)) := (inv_mul_cancel_left x q₁).symm
            have heq₂ : (q₁ * q₂ = x⁻¹ * z ↔ q₂ = (x * q₁)⁻¹ * z) := by
              constructor <;> intro h
              · rw [mul_inv_rev, mul_assoc, ← h, inv_mul_cancel_left]
              · rw [h]; group
            simp [← heq, heq₂]
          · intro y hy
            have hne : q₁ ≠ x⁻¹ * y := fun h ↦ hy (by rw [h, mul_inv_cancel_left])
            simp [hne])

@[simp]
theorem normalLevelHeckeKernelAlgEquiv_apply (p : MonoidAlgebra A (G ⧸ U)) (x y : G ⧸ U) :
    normalLevelHeckeKernelAlgEquiv A G U p (x, y) = p.coeff (x⁻¹ * y) := (rfl)

@[simp]
theorem normalLevelHeckeKernelAlgEquiv_single_one (g : G) :
    normalLevelHeckeKernelAlgEquiv A G U (MonoidAlgebra.single (g : G ⧸ U) 1) =
      doubleCosetBasis A G U (DoubleCoset.mk U U g) := by
  classical
  ext x y
  induction x using QuotientGroup.induction_on with | H a =>
  induction y using QuotientGroup.induction_on with | H b =>
  simp only [normalLevelHeckeKernelAlgEquiv_apply, coeff_single, Finsupp.single_apply,
    doubleCosetBasis_apply_mk]
  have hmem : a⁻¹ * b ∈ DoubleCoset.doubleCoset g (U : Set G) U ↔
      ((g : G ⧸ U) = ((a : G ⧸ U)⁻¹ * (b : G ⧸ U))) := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_doubleCoset]
    constructor
    · rintro ⟨u₁, hu₁, u₂, hu₂, hab⟩
      rw [hab]
      have hconj : g⁻¹ * u₁ * g ∈ U := by
        simpa [mul_assoc] using ‹U.Normal›.conj_mem u₁ hu₁ g⁻¹
      simpa [mul_assoc] using U.mul_mem hconj hu₂
    · intro h
      exact ⟨1, U.one_mem, g⁻¹ * (a⁻¹ * b), h, by group⟩
  by_cases h : (g : G ⧸ U) = (a : G ⧸ U)⁻¹ * (b : G ⧸ U)
  · simp [h, hmem.mpr h]
  · simp [h, mt hmem.mp h]

/-- **When `U` is normal in `G`, the level Hecke algebra `HeckeAlgebraLevel A G U` is isomorphic as
an `A`-algebra to `MonoidAlgebra A (G ⧸ U)`.** -/
def normalHeckeAlgebraLevelAlgEquiv :
    HeckeAlgebraLevel A G U ≃ₐ[A] MonoidAlgebra A (G ⧸ U) :=
  (levelHeckeAlgEquiv A G U).symm.trans (normalLevelHeckeKernelAlgEquiv A G U).symm

theorem normalHeckeAlgebraLevelAlgEquiv_def :
    normalHeckeAlgebraLevelAlgEquiv A G U =
      (levelHeckeAlgEquiv A G U).symm.trans (normalLevelHeckeKernelAlgEquiv A G U).symm := (rfl)

@[simp]
theorem normalHeckeAlgebraLevelAlgEquiv_symm_single_one (g : G) :
    (normalHeckeAlgebraLevelAlgEquiv A G U).symm (MonoidAlgebra.single (g : G ⧸ U) 1) =
      levelHeckeAlgEquiv A G U (doubleCosetBasis A G U (DoubleCoset.mk U U g)) := by
  simp [normalHeckeAlgebraLevelAlgEquiv_def]

end NormalSubgroup

end TauCeti

end
