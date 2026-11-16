/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyFour.Order
public import TauCeti.GroupTheory.SpecificGroups.Sporadic.Mathieu.TwentyThree
import TauCeti.GroupTheory.GroupAction.Simple.Stabilizer

/-!
# Point stabilizer identification and simplicity of the permutation model of `M₂₄`

This file identifies the stabilizer of `0 : Fin 24` in the canonical `24`-point permutation model
`TauCeti.Sporadic.M24` with the canonical `23`-point permutation model `TauCeti.Sporadic.M23`,
compatibly with their permutation actions, and deduces that `M24` is doubly transitive, primitive,
and simple.

First, `b⁻¹ * a ∈ M24` fixes `0` and cycles the remaining `23` points, while `a` moves `0` to `3`.
Hence `M24` acts transitively on `Fin 24`, so by orbit-stabilizer and `TauCeti.Sporadic.card_M24`
the point stabilizer `MulAction.stabilizer M24 (0 : Fin 24)` has order
`244823040 / 24 = 10200960 = Nat.card M23`.

Next, the explicit coordinate permutation
```text
m23CoordPerm = (0, 5, 6, 21, 16, 14, 15, 20, 18, 10, 23)(1, 3, 13, 9, 22, 19, 8, 17, 2, 4, 11)
```
sends `23 : Fin 24` to `0` and restricts on `0, …, 22` to a bijection `m23CoordEquiv` between
`Fin 23` and `{x : Fin 24 // x ≠ 0}` (the carrier of `SubMulAction.ofStabilizer M24 0`). Extending
permutations of `Fin 23` along `m23CoordEquiv` maps `M23.a` and `M23.b` to explicit words in
`M24.a` and `M24.b` fixing `0`. Since domain extension is injective and both groups have order
`10200960`, this restricts to a multiplicative equivalence
`M24.stabilizerZeroEquivM23 : MulAction.stabilizer M24 (0 : Fin 24) ≃* M23` intertwined with
`m23CoordEquiv.symm` on `{x : Fin 24 // x ≠ 0}`.

Transporting `M23.isPretransitive` and `TauCeti.Sporadic.isSimpleGroup_M23` across this
equivariant identification shows that `M24` is doubly transitive (hence primitive) and that
`MulAction.stabilizer M24 (0 : Fin 24)` is simple. Because the degree `24 = 23 + 1` is divisible
by the distinct primes `2` and `3` and the stabilizer contains `b⁻¹ * a` of prime order `23`,
`TauCeti.isSimpleGroup_of_isSimpleGroup_stabilizer_of_card_eq_succ` rules out regular normal
subgroups and proves `IsSimpleGroup M24`.

## Main declarations

* `TauCeti.Sporadic.M24.isPretransitive`: `M24` acts transitively on `Fin 24`.
* `TauCeti.Sporadic.M24.natCard_stabilizer_zero`: `MulAction.stabilizer M24 (0 : Fin 24)` has
  order `10200960`.
* `TauCeti.Sporadic.M24.m23CoordPerm`, `TauCeti.Sporadic.M24.m23CoordEquiv`: explicit coordinate
  comparison between `Fin 23` and `{x : Fin 24 // x ≠ 0}`.
* `TauCeti.Sporadic.M24.stabilizerZeroEquivM23`: explicit multiplicative equivalence
  `MulAction.stabilizer M24 (0 : Fin 24) ≃* M23`.
* `TauCeti.Sporadic.M24.ofStabilizerZeroMulActionHom`: equivariant bijection from
  `SubMulAction.ofStabilizer M24 (0 : Fin 24)` to `Fin 23` along `stabilizerZeroEquivM23`.
* `TauCeti.Sporadic.M24.isMultiplyPretransitive_two`, `TauCeti.Sporadic.M24.isPreprimitive`:
  double transitivity and primitivity of `M24` on `Fin 24`.
* `TauCeti.Sporadic.M24.isSimpleGroup_stabilizer_zero`: simplicity of the point stabilizer of `0`.
* `TauCeti.Sporadic.isSimpleGroup_M24`: simplicity of the canonical permutation model `M24`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Springer,
  1999, Chapter 10, §2.
* J. D. Dixon and B. Mortimer, *Permutation Groups*, Graduate Texts in Mathematics 163, Springer,
  1996, §1.6 and §7.4.
* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, representations `M23G1-p23B0` and `M24G1-p24B0`.
-/

public section

namespace TauCeti.Sporadic

namespace M24

/-! ### Transitivity and point-stabilizer order -/

/-- The word `b⁻¹ * a` belongs to `M24`. -/
theorem b_inv_mul_a_mem : b⁻¹ * a ∈ M24 :=
  mul_mem (inv_mem b_mem) a_mem

/-- The element `b⁻¹ * a` of `M24` fixes `0 : Fin 24`. -/
theorem b_inv_mul_a_mem_stabilizer_zero :
    (⟨b⁻¹ * a, b_inv_mul_a_mem⟩ : M24) ∈ MulAction.stabilizer M24 (0 : Fin 24) := by
  rw [MulAction.mem_stabilizer_iff, Subgroup.mk_smul, Equiv.Perm.smul_def]
  decide +kernel

/-- The stabilizer element `b⁻¹ * a` has prime order `23`. -/
theorem orderOf_b_inv_mul_a : orderOf (b⁻¹ * a) = 23 :=
  have : Fact (Nat.Prime 23) := ⟨by decide⟩
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

/-- The canonical permutation model `M24` acts transitively on `Fin 24`. -/
instance isPretransitive : MulAction.IsPretransitive M24 (Fin 24) := by
  have h : ∀ x : Fin 24, x = 0 ∨ ∃ k : Fin 23, ((b⁻¹ * a) ^ (k : ℕ) * a) 0 = x := by
    decide +kernel
  refine MulAction.IsPretransitive.of_orbit (x₀ := 0) fun x ↦ ?_
  rcases h x with rfl | ⟨k, hk⟩
  · exact ⟨1, one_smul M24 0⟩
  · refine ⟨⟨(b⁻¹ * a) ^ (k : ℕ) * a, mul_mem (pow_mem b_inv_mul_a_mem _) a_mem⟩, ?_⟩
    simpa only [Subgroup.mk_smul, Equiv.Perm.smul_def] using hk

/-- The stabilizer of `0 : Fin 24` in `M24` has index `24`. -/
theorem index_stabilizer_zero : (MulAction.stabilizer M24 (0 : Fin 24)).index = 24 := by
  rw [MulAction.index_stabilizer_of_transitive M24 (0 : Fin 24), Nat.card_fin]

/-- The stabilizer of `0 : Fin 24` in `M24` has order `10200960 = Nat.card M23`. -/
theorem natCard_stabilizer_zero :
    Nat.card (MulAction.stabilizer M24 (0 : Fin 24)) = 10200960 := by
  have h := (MulAction.stabilizer M24 (0 : Fin 24)).card_mul_index
  rw [index_stabilizer_zero, card_M24] at h
  omega

/-! ### Coordinate comparison and isomorphism with `M23` -/

/-- Coordinate permutation sending `Fin.castSucc` of the `23` ATLAS coordinates of `M23`
(`M23G1-p23B0`) into `{x : Fin 24 // x ≠ 0}` and sending `23 : Fin 24` to `0`. Its body is exposed
so kernel checks can evaluate coordinate images directly. -/
@[expose] def m23CoordPerm : Equiv.Perm (Fin 24) :=
  c[0, 5, 6, 21, 16, 14, 15, 20, 18, 10, 23] * c[1, 3, 13, 9, 22, 19, 8, 17, 2, 4, 11]

/-- Cycle decomposition of `m23CoordPerm`. -/
theorem m23CoordPerm_def :
    m23CoordPerm =
      c[0, 5, 6, 21, 16, 14, 15, 20, 18, 10, 23] * c[1, 3, 13, 9, 22, 19, 8, 17, 2, 4, 11] :=
  (rfl)

@[simp]
theorem m23CoordPerm_twentyThree : m23CoordPerm 23 = 0 := by
  decide +kernel

theorem m23CoordPerm_last : m23CoordPerm (Fin.last 23) = 0 :=
  m23CoordPerm_twentyThree

@[simp]
theorem m23CoordPerm_symm_zero : m23CoordPerm.symm 0 = 23 :=
  m23CoordPerm.symm_apply_eq.mpr m23CoordPerm_twentyThree.symm

theorem m23CoordPerm_castSucc_ne_zero (i : Fin 23) : m23CoordPerm i.castSucc ≠ 0 := by
  intro h
  exact Fin.castSucc_ne_last i (m23CoordPerm.injective (h.trans m23CoordPerm_last.symm))

/-- Explicit coordinate equivalence `Fin 23 ≃ {x : Fin 24 // x ≠ 0}` sending `i` to
`m23CoordPerm i.castSucc`. -/
def m23CoordEquiv : Fin 23 ≃ {x : Fin 24 // x ≠ 0} :=
  (finSuccAboveEquiv (Fin.last 23)).trans
    (m23CoordPerm.subtypeEquiv fun x ↦ by
      rw [ne_eq, ne_eq, ← m23CoordPerm_last, m23CoordPerm.apply_eq_iff_eq])

@[simp]
theorem coe_m23CoordEquiv_apply (i : Fin 23) :
    (m23CoordEquiv i : Fin 24) = m23CoordPerm i.castSucc := by
  change m23CoordPerm ((Fin.last 23).succAbove i) = m23CoordPerm i.castSucc
  rw [Fin.succAbove_last]

@[simp]
theorem m23CoordEquiv_symm_mk_castSucc (i : Fin 23) :
    m23CoordEquiv.symm ⟨m23CoordPerm i.castSucc, m23CoordPerm_castSucc_ne_zero i⟩ = i := by
  apply m23CoordEquiv.injective
  ext
  simp

@[simp]
theorem m23CoordPerm_m23CoordEquiv_symm_castSucc (x : {x : Fin 24 // x ≠ 0}) :
    m23CoordPerm (m23CoordEquiv.symm x).castSucc = x.1 := by
  rw [← coe_m23CoordEquiv_apply, Equiv.apply_symm_apply]

/-- Auxiliary element of `M24` of order `3` fixing `0 : Fin 24`. -/
private def stabAuxH : Equiv.Perm (Fin 24) :=
  (b * a) ^ 5 * (b⁻¹ * a) ^ 5 * b⁻¹

private theorem stabAuxH_mem : stabAuxH ∈ M24 :=
  mul_mem (mul_mem (pow_mem (mul_mem b_mem a_mem) 5) (pow_mem b_inv_mul_a_mem 5)) (inv_mem b_mem)

/-- Extending `M23.a` along `m23CoordEquiv` produces an explicit word in `M24.a` and `M24.b`. -/
private theorem extendDomain_m23CoordEquiv_a_eq :
    M23.a.extendDomain m23CoordEquiv =
      ((b⁻¹ * a) ^ 3 * stabAuxH⁻¹ * (b⁻¹ * a)⁻¹ * stabAuxH⁻¹) ^ 2 := by
  rw [M23.a_def]
  decide +kernel

/-- Extending `M23.b` along `m23CoordEquiv` produces an explicit word in `M24.a` and `M24.b`. -/
private theorem extendDomain_m23CoordEquiv_b_eq :
    M23.b.extendDomain m23CoordEquiv =
      stabAuxH * (b⁻¹ * a) ^ 2 * stabAuxH * (b⁻¹ * a)⁻¹ ^ 2 := by
  rw [M23.b_def]
  decide +kernel

private theorem extendDomain_m23CoordEquiv_a_mem : M23.a.extendDomain m23CoordEquiv ∈ M24 := by
  rw [extendDomain_m23CoordEquiv_a_eq]
  exact pow_mem (mul_mem (mul_mem (mul_mem (pow_mem b_inv_mul_a_mem 3) (inv_mem stabAuxH_mem))
    (inv_mem b_inv_mul_a_mem)) (inv_mem stabAuxH_mem)) 2

private theorem extendDomain_m23CoordEquiv_b_mem : M23.b.extendDomain m23CoordEquiv ∈ M24 := by
  rw [extendDomain_m23CoordEquiv_b_eq]
  exact mul_mem (mul_mem (mul_mem stabAuxH_mem (pow_mem b_inv_mul_a_mem 2)) stabAuxH_mem)
    (pow_mem (inv_mem b_inv_mul_a_mem) 2)

/-- Extending any permutation in `M23` along `m23CoordEquiv` lands in `M24`. -/
theorem extendDomain_m23CoordEquiv_mem {σ : Equiv.Perm (Fin 23)} (hσ : σ ∈ M23) :
    σ.extendDomain m23CoordEquiv ∈ M24 := by
  have hle : M23 ≤ M24.comap (Equiv.Perm.extendDomainHom m23CoordEquiv) := by
    rw [M23_def, Subgroup.closure_le]
    rintro τ (rfl | rfl)
    · exact extendDomain_m23CoordEquiv_a_mem
    · exact extendDomain_m23CoordEquiv_b_mem
  exact hle hσ

/-- Extending a permutation along `m23CoordEquiv` fixes `0 : Fin 24`. -/
@[simp]
theorem extendDomain_m23CoordEquiv_apply_zero (σ : Equiv.Perm (Fin 23)) :
    σ.extendDomain m23CoordEquiv 0 = 0 :=
  Equiv.Perm.extendDomain_apply_not_subtype σ m23CoordEquiv (not_not.mpr rfl)

/-- Extending a permutation along `m23CoordEquiv` intertwines `m23CoordPerm ∘ Fin.castSucc`. -/
@[simp]
theorem extendDomain_m23CoordEquiv_apply_castSucc (σ : Equiv.Perm (Fin 23)) (i : Fin 23) :
    σ.extendDomain m23CoordEquiv (m23CoordPerm i.castSucc) = m23CoordPerm (σ i).castSucc := by
  simpa only [coe_m23CoordEquiv_apply] using
    Equiv.Perm.extendDomain_apply_image σ m23CoordEquiv i

/-- The group homomorphism `M23 →* MulAction.stabilizer M24 (0 : Fin 24)` induced by domain
extension along `m23CoordEquiv`. -/
private def m23ToStabilizerZeroHom : M23 →* MulAction.stabilizer M24 (0 : Fin 24) where
  toFun g := ⟨⟨(g : Equiv.Perm (Fin 23)).extendDomain m23CoordEquiv,
    extendDomain_m23CoordEquiv_mem g.2⟩, by
      rw [MulAction.mem_stabilizer_iff, Subgroup.mk_smul, Equiv.Perm.smul_def,
        extendDomain_m23CoordEquiv_apply_zero]⟩
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [Equiv.Perm.extendDomain_mul]

private theorem m23ToStabilizerZeroHom_bijective : Function.Bijective m23ToStabilizerZeroHom := by
  have hinj : Function.Injective m23ToStabilizerZeroHom := fun g h hgh ↦ by
    apply Subtype.ext
    apply Equiv.Perm.extendDomainHom_injective m23CoordEquiv
    exact congrArg (fun x : MulAction.stabilizer M24 (0 : Fin 24) ↦
      ((x : M24) : Equiv.Perm (Fin 24))) hgh
  have : Finite (MulAction.stabilizer M24 (0 : Fin 24)) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_stabilizer_zero]; decide)
  exact hinj.bijective_of_nat_card_le (by rw [natCard_stabilizer_zero, card_M23])

/-- **Point-stabilizer identification for `M₂₄`.** Explicit multiplicative equivalence between the
stabilizer of `0 : Fin 24` in `M24` and the canonical `23`-point permutation model `M23`. -/
noncomputable def stabilizerZeroEquivM23 :
    MulAction.stabilizer M24 (0 : Fin 24) ≃* M23 :=
  (MulEquiv.ofBijective m23ToStabilizerZeroHom m23ToStabilizerZeroHom_bijective).symm

/-- `stabilizerZeroEquivM23.symm` sends `g : M23` to its domain extension along `m23CoordEquiv`. -/
@[simp]
theorem coe_stabilizerZeroEquivM23_symm_apply (g : M23) :
    ((stabilizerZeroEquivM23.symm g : M24) : Equiv.Perm (Fin 24)) =
      (g : Equiv.Perm (Fin 23)).extendDomain m23CoordEquiv := by
  rfl

/-- `stabilizerZeroEquivM23.symm` intertwines the action of `M23` on `Fin 23` with that of `M24`
on `{x : Fin 24 // x ≠ 0}` along `m23CoordPerm ∘ Fin.castSucc`. -/
@[simp]
theorem stabilizerZeroEquivM23_symm_smul_castSucc (g : M23) (i : Fin 23) :
    (stabilizerZeroEquivM23.symm g : M24) • m23CoordPerm i.castSucc =
      m23CoordPerm (g • i).castSucc := by
  rw [Subgroup.smul_def, coe_stabilizerZeroEquivM23_symm_apply, Equiv.Perm.smul_def,
    extendDomain_m23CoordEquiv_apply_castSucc, Subgroup.smul_def, Equiv.Perm.smul_def]

/-- `stabilizerZeroEquivM23` transports the action of `MulAction.stabilizer M24 (0 : Fin 24)` on
`m23CoordPerm i.castSucc` to the natural action of `M23` on `i : Fin 23`. -/
theorem m23CoordPerm_stabilizerZeroEquivM23_smul_castSucc
    (h : MulAction.stabilizer M24 (0 : Fin 24)) (i : Fin 23) :
    m23CoordPerm (stabilizerZeroEquivM23 h • i).castSucc =
      (h : M24) • m23CoordPerm i.castSucc := by
  conv_rhs => rw [← stabilizerZeroEquivM23.symm_apply_apply h]
  exact (stabilizerZeroEquivM23_symm_smul_castSucc (stabilizerZeroEquivM23 h) i).symm

/-- Explicit equivariant bijection from `SubMulAction.ofStabilizer M24 (0 : Fin 24)` to `Fin 23`
along `stabilizerZeroEquivM23`. -/
noncomputable def ofStabilizerZeroMulActionHom :
    SubMulAction.ofStabilizer M24 (0 : Fin 24) →ₑ[stabilizerZeroEquivM23] Fin 23 where
  toFun x := m23CoordEquiv.symm ⟨x.1, x.2⟩
  map_smul' h x := by
    apply m23CoordEquiv.injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply, coe_m23CoordEquiv_apply,
      m23CoordPerm_stabilizerZeroEquivM23_smul_castSucc,
      m23CoordPerm_m23CoordEquiv_symm_castSucc]
    rfl

@[simp]
theorem ofStabilizerZeroMulActionHom_apply (x : SubMulAction.ofStabilizer M24 (0 : Fin 24)) :
    ofStabilizerZeroMulActionHom x = m23CoordEquiv.symm ⟨x.1, x.2⟩ := by
  rfl

theorem ofStabilizerZeroMulActionHom_bijective :
    Function.Bijective ofStabilizerZeroMulActionHom :=
  m23CoordEquiv.symm.bijective

/-! ### Double transitivity, primitivity, and simplicity -/

/-- The stabilizer of `0 : Fin 24` in `M24` acts transitively on `{x : Fin 24 // x ≠ 0}`. -/
instance isPretransitive_ofStabilizer_zero :
    MulAction.IsPretransitive (MulAction.stabilizer M24 (0 : Fin 24))
      (SubMulAction.ofStabilizer M24 (0 : Fin 24)) :=
  (MulAction.isPretransitive_congr stabilizerZeroEquivM23.surjective
    ofStabilizerZeroMulActionHom_bijective).mpr M23.isPretransitive

/-- Multiple transitivity of `M24` on `Fin 24` of degree `n + 1` is equivalent to multiple
transitivity of `M23` on `Fin 23` of degree `n`. -/
theorem isMultiplyPretransitive_succ_iff (n : ℕ) :
    MulAction.IsMultiplyPretransitive M24 (Fin 24) (n + 1) ↔
      MulAction.IsMultiplyPretransitive M23 (Fin 23) n :=
  (SubMulAction.ofStabilizer.isMultiplyPretransitive (a := (0 : Fin 24))).trans
    (MulAction.IsPretransitive.of_embedding_congr stabilizerZeroEquivM23.surjective
      ofStabilizerZeroMulActionHom_bijective)

/-- The canonical permutation model `M24` acts doubly transitively on `Fin 24`. -/
instance isMultiplyPretransitive_two : MulAction.IsMultiplyPretransitive M24 (Fin 24) 2 :=
  (isMultiplyPretransitive_succ_iff 1).mpr (MulAction.is_one_pretransitive_iff.mpr inferInstance)

/-- The canonical permutation model `M24` acts primitively on `Fin 24`. -/
instance isPreprimitive : MulAction.IsPreprimitive M24 (Fin 24) :=
  MulAction.isPreprimitive_of_is_two_pretransitive isMultiplyPretransitive_two

/-- The stabilizer of `0 : Fin 24` in `M24` is simple, being isomorphic to `M23`. -/
instance isSimpleGroup_stabilizer_zero :
    IsSimpleGroup (MulAction.stabilizer M24 (0 : Fin 24)) :=
  stabilizerZeroEquivM23.isSimpleGroup

end M24

/-- **The canonical `24`-point permutation model of `M₂₄` is simple.** -/
instance isSimpleGroup_M24 : IsSimpleGroup M24 :=
  TauCeti.isSimpleGroup_of_isSimpleGroup_stabilizer_of_card_eq_succ (X := Fin 24) (0 : Fin 24)
    (p := 23) (q := 2) (r := 3)
    (by decide) (by rw [Nat.card_fin])
    Nat.prime_two Nat.prime_three (by decide)
    (by rw [Nat.card_fin]; decide) (by rw [Nat.card_fin]; decide)
    ⟨⟨M24.b⁻¹ * M24.a, M24.b_inv_mul_a_mem⟩, M24.b_inv_mul_a_mem_stabilizer_zero⟩
    (by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact M24.orderOf_b_inv_mul_a)

end TauCeti.Sporadic
