/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commensurable
public import Mathlib.NumberTheory.HeckeRing.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Commensurability of compact open subgroups

In a topological group with separately continuous multiplication, an open subgroup `H` meets any
compact subgroup `K` in an open subgroup `H.subgroupOf K` of the compact group `K`. Since an open
subgroup of a compact group has finite coset space, `H ⊓ K` has finite index in `K`, that is,
`H.IsFiniteRelIndex K`.

Applying this symmetrically to two compact open subgroups `H` and `K` shows that any two compact
open subgroups are commensurable (`Subgroup.commensurable_of_isCompact_of_isOpen`). Because
conjugation by a fixed group element is a composition of left and right translations, hence a
homeomorphism under separate continuity of multiplication alone, every conjugate `g U g⁻¹` of a
compact open subgroup `U` is again compact and open; consequently
`Subgroup.Commensurable.commensurator U = ⊤`, and `(⊤, U₁, U₂)` is a Hecke triple
(`Subgroup.isHeckeTriple_top_of_isCompact_of_isOpen`).

For a group action on `S`, the stabilizer in `stabilizer G x` of another point `y` is
`(stabilizer G y).subgroupOf (stabilizer G x)`. Hence when `stabilizer G x` is compact and
`stabilizer G y` is open, the `(stabilizer G x)`-orbit of `y` is finite
(`MulAction.finite_orbit_stabilizer_of_isCompact_of_isOpen`). This is the finiteness input that
makes matrix convolution of `G`-invariant kernels on `S × S` and their action on the permutation
module `A[S]` finite sums.

## Main results

* `Subgroup.finite_quotient_subgroupOf_of_isOpen_of_isCompact`: `K ⧸ H.subgroupOf K` is finite when
  `H` is open and `K` is compact.
* `Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact`: `H.IsFiniteRelIndex K` when `H` is open and
  `K` is compact, with `OpenSubgroup.isFiniteRelIndex_of_isCompact` its bundled counterpart.
* `Subgroup.commensurable_of_isCompact_of_isOpen`: compact open subgroups are commensurable, with
  `OpenSubgroup.commensurable_of_isCompact` its bundled counterpart.
* `Subgroup.commensurator_eq_top_of_isCompact_of_isOpen`: a compact open subgroup is commensurated
  by the whole ambient group.
* `Subgroup.isHeckeTriple_top_of_isCompact_of_isOpen` and
  `OpenSubgroup.isHeckeTriple_top_of_isCompact`: any two compact open subgroups form a Hecke triple
  with `⊤ : Submonoid G`.
* `MulAction.isFiniteRelIndex_stabilizer_of_isOpen_of_isCompact` and
  `MulAction.finite_orbit_stabilizer_of_isCompact_of_isOpen`: finiteness of stabilizer orbits when
  one point stabilizer is compact and the other is open.
-/

public section

open scoped Pointwise

section Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- If `H` is an open subgroup and `K` is a compact subgroup of `G`, then the coset space
`K ⧸ H.subgroupOf K` is finite. -/
@[to_additive /-- If `H` is an open additive subgroup and `K` is a compact additive subgroup of `G`,
then the coset space `K ⧸ H.addSubgroupOf K` is finite. -/]
theorem Subgroup.finite_quotient_subgroupOf_of_isOpen_of_isCompact {H K : Subgroup G}
    (hH : IsOpen (H : Set G)) (hK : IsCompact (K : Set G)) :
    Finite (K ⧸ H.subgroupOf K) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : SeparatelyContinuousMul K := K.toSubmonoid.separatelyContinuousMul
  exact Subgroup.quotient_finite_of_isOpen (H.subgroupOf K) (Subgroup.subgroupOf_isOpen K H hH)

/-- An open subgroup `H` has finite relative index in any compact subgroup `K`: `H ⊓ K` has finite
index in `K`. -/
@[to_additive /-- An open additive subgroup `H` has finite relative index in any compact additive
subgroup `K`: `H ⊓ K` has finite index in `K`. -/]
theorem Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact {H K : Subgroup G}
    (hH : IsOpen (H : Set G)) (hK : IsCompact (K : Set G)) :
    H.IsFiniteRelIndex K := by
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  have := Subgroup.finite_quotient_subgroupOf_of_isOpen_of_isCompact hH hK
  exact Subgroup.finiteIndex_of_finite_quotient

/-- A bundled open subgroup has finite relative index in any compact subgroup. -/
@[to_additive /-- A bundled open additive subgroup has finite relative index in any compact additive
subgroup. -/]
theorem OpenSubgroup.isFiniteRelIndex_of_isCompact (U : OpenSubgroup G) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) : U.toSubgroup.IsFiniteRelIndex K :=
  Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact U.isOpen hK

/-- Any two compact open subgroups of a group with separately continuous multiplication are
commensurable. -/
@[to_additive /-- Any two compact open additive subgroups of an additive group with separately
continuous addition are commensurable. -/]
theorem Subgroup.commensurable_of_isCompact_of_isOpen {H K : Subgroup G}
    (hHc : IsCompact (H : Set G)) (hHo : IsOpen (H : Set G))
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    Subgroup.Commensurable H K :=
  ⟨Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact hHo hKc,
    Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact hKo hHc⟩

/-- Bundled open subgroups that are compact are commensurable. -/
@[to_additive /-- Bundled open additive subgroups that are compact are commensurable. -/]
theorem OpenSubgroup.commensurable_of_isCompact {U V : OpenSubgroup G}
    (hU : IsCompact (U : Set G)) (hV : IsCompact (V : Set G)) :
    Subgroup.Commensurable U.toSubgroup V.toSubgroup :=
  Subgroup.commensurable_of_isCompact_of_isOpen hU U.isOpen hV V.isOpen

/-- Conjugating a subgroup by `g` applies the homeomorphism `x ↦ g * x * g⁻¹` to its underlying
set, so compactness and openness are preserved under separate continuity of multiplication alone. -/
private theorem coe_conj_smul_eq_image (U : Subgroup G) (g : G) :
    ((MulAut.conj g • U : Subgroup G) : Set G) =
      ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)) '' (U : Set G) := by
  ext x
  simp [Set.mem_smul_set, MulAut.conj_apply, mul_assoc]

/-- Every element of `G` commensurates a compact open subgroup `U`. -/
theorem Subgroup.commensurator_eq_top_of_isCompact_of_isOpen {U : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) :
    Subgroup.Commensurable.commensurator U = ⊤ := by
  rw [eq_top_iff']
  intro g
  rw [Subgroup.Commensurable.commensurator_mem_iff]
  let e := (Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)
  have hconj_c : IsCompact ((MulAut.conj g • U : Subgroup G) : Set G) := by
    rw [coe_conj_smul_eq_image]
    exact hUc.image e.continuous
  have hconj_o : IsOpen ((MulAut.conj g • U : Subgroup G) : Set G) := by
    rw [coe_conj_smul_eq_image]
    exact e.isOpenMap _ hUo
  exact Subgroup.commensurable_of_isCompact_of_isOpen hconj_c hconj_o hUc hUo

/-- Any two compact open subgroups `U₁` and `U₂` form a Hecke triple `(⊤, U₁, U₂)` in `G`. -/
theorem Subgroup.isHeckeTriple_top_of_isCompact_of_isOpen {U₁ U₂ : Subgroup G}
    (hU₁c : IsCompact (U₁ : Set G)) (hU₁o : IsOpen (U₁ : Set G))
    (hU₂c : IsCompact (U₂ : Set G)) (hU₂o : IsOpen (U₂ : Set G)) :
    IsHeckeTriple (⊤ : Submonoid G) U₁ U₂ where
  left_le := le_top
  right_le := le_top
  commensurable := Subgroup.commensurable_of_isCompact_of_isOpen hU₁c hU₁o hU₂c hU₂o
  le_commensurator_right := by
    rw [Subgroup.commensurator_eq_top_of_isCompact_of_isOpen hU₂c hU₂o]
    exact le_rfl

/-- Bundled compact open subgroups `U₁` and `U₂` form a Hecke triple `(⊤, U₁, U₂)`. -/
theorem OpenSubgroup.isHeckeTriple_top_of_isCompact {U₁ U₂ : OpenSubgroup G}
    (hU₁ : IsCompact (U₁ : Set G)) (hU₂ : IsCompact (U₂ : Set G)) :
    IsHeckeTriple (⊤ : Submonoid G) U₁.toSubgroup U₂.toSubgroup :=
  Subgroup.isHeckeTriple_top_of_isCompact_of_isOpen hU₁ U₁.isOpen hU₂ U₂.isOpen

/-- Any two compact `OpenSubgroup`s automatically form a Hecke triple `(⊤, U₁, U₂)`. -/
instance OpenSubgroup.instIsHeckeTripleTopOfCompactSpace {U₁ U₂ : OpenSubgroup G}
    [CompactSpace U₁] [CompactSpace U₂] :
    IsHeckeTriple (⊤ : Submonoid G) U₁.toSubgroup U₂.toSubgroup :=
  OpenSubgroup.isHeckeTriple_top_of_isCompact
    (isCompact_iff_compactSpace.mpr inferInstance)
    (isCompact_iff_compactSpace.mpr inferInstance)

end Subgroup

section MulAction

variable {G S : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] [MulAction G S]

/-- For a group action on `S`, if the stabilizer of `y` is open and the stabilizer of `x` is
compact, then `stabilizer G y` has finite relative index in `stabilizer G x`. -/
theorem MulAction.isFiniteRelIndex_stabilizer_of_isOpen_of_isCompact {x y : S}
    (hy : IsOpen (MulAction.stabilizer G y : Set G))
    (hx : IsCompact (MulAction.stabilizer G x : Set G)) :
    (MulAction.stabilizer G y).IsFiniteRelIndex (MulAction.stabilizer G x) :=
  Subgroup.isFiniteRelIndex_of_isOpen_of_isCompact hy hx

/-- **Finiteness of stabilizer orbits from compact open stabilizers.** If `stabilizer G x` is
compact and `stabilizer G y` is open, then the `(stabilizer G x)`-orbit of `y` is finite. -/
theorem MulAction.finite_orbit_stabilizer_of_isCompact_of_isOpen {x y : S}
    (hx : IsCompact (MulAction.stabilizer G x : Set G))
    (hy : IsOpen (MulAction.stabilizer G y : Set G)) :
    Finite ↥(MulAction.orbit (MulAction.stabilizer G x) y) := by
  have hfin : Finite (MulAction.stabilizer G x ⧸
      (MulAction.stabilizer G y).subgroupOf (MulAction.stabilizer G x)) :=
    Subgroup.finite_quotient_subgroupOf_of_isOpen_of_isCompact hy hx
  rw [MulAction.stabilizer_subgroupOf] at hfin
  exact Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer (MulAction.stabilizer G x) y).symm

end MulAction

end
