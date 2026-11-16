/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.TwoDivisible
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.PathSpace.Moore.Comparison.HomotopyGroup
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Mod-two homology of the basepoint loop component and higher homotopy groups

For a pointed space `(X, x)`, the based loop space `Ω X x` need not be path-connected when
`π₁(X, x)` is nontrivial, so Hurewicz and Whitehead-tower arguments do not apply directly to
`Ω X x`. Passing to the path component `Ω₀ X = pathComponent (Path.refl x)` of the constant loop
produces a path-connected space whose positive-dimensional homotopy groups are still shifted
homotopy groups of `X`:

`πₖ(Ω₀ X) ≅ πₖ(Ω X x) ≅ πₖ₊₁(X, x)` for all `k ≥ 1`.

Combining this shift with the Whitehead-tower mod-two vanishing theorem
`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology` yields:

* if `πₖ(X, x)` vanishes for `2 ≤ k < r + 3` and `H_q(Ω₀ X; 𝔽₂) = 0` for `r + 2 ≤ q ≤ n + 3`
  (`r ≤ n`), then `π_{n+3}(X, x)` is uniquely two-divisible;
* in particular, when `π₂(X, x)` is trivial (with no hypothesis on `π₁(X, x)`), `Ω₀ X` is simply
  connected: if `H_q(Ω₀ X; 𝔽₂) = 0` for `2 ≤ q ≤ n + 3`, then `π_{n+3}(X, x)` is uniquely
  two-divisible, and contrapositively `π_{n+3}(X, x) ⊗[ℤ] ℤ/2 ≠ 0` forces `H_q(Ω₀ X; 𝔽₂) ≠ 0`
  for some degree `2 ≤ q ≤ n + 3`.

Both the fixed-interval loop space `Ω X x` and the Moore loop space `MooreLoopSpace X x` are
treated, in both simplicial singular homology and normalized cubical homology.

This supplies the topological half of Theorem 5.15 of Barraud--Damian--Humilière--Oancea: for a
pointed space `Q` with `π₂(Q) = 0` and `πᵢ(Q) ⊗ ℤ/2 ≠ 0` for some `i ≥ 3`, the basepoint component
`Ω₀ Q` of the based loop space has nontrivial positive-degree mod-two homology. The Floer-theoretic
spectral sequence argument relating `H_*(Ω₀ Q; 𝔽₂)` to Lagrangian Floer homology with DG local
systems is separate.

## Main results

* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_loopSpace_singularHomology`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_loopSpace_cubicalHomology`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_loopSpace_of_subsingleton_pi2`:
  unique two-divisibility of `π_{n+3}(X, x)` from mod-two vanishing on
  `pathComponent (Path.refl x)`.
* `TauCeti.exists_nontrivial_pathComponent_loopSpace_singularHomology_mod_two`,
  `TauCeti.exists_nontrivial_pathComponent_loopSpace_cubicalHomology_mod_two`: when `π₂(X, x)` is
  trivial and `π_{n+3}(X, x) ⊗ ℤ/2` is nontrivial, `pathComponent (Path.refl x)` has nontrivial
  mod-two homology in some degree `2 ≤ q ≤ n + 3`.
* `TauCeti.MooreLoopSpace.isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_singularHomology`,
  `TauCeti.MooreLoopSpace.isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_cubicalHomology`,
  `TauCeti.MooreLoopSpace.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_pi2`,
  `TauCeti.MooreLoopSpace.exists_nontrivial_pathComponent_singularHomology_mod_two`,
  `TauCeti.MooreLoopSpace.exists_nontrivial_pathComponent_cubicalHomology_mod_two`: the same for
  `pathComponent (1 : MooreLoopSpace X x)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorem 5.15.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  Chapter III.
-/

public noncomputable section

open AlgebraicTopology CategoryTheory
open scoped Topology Topology.Homotopy

namespace TauCeti

section Shift

variable {X L : Type} [TopologicalSpace X] [TopologicalSpace L] {x : X} {l : L}

/-- Positive-dimensional homotopy groups of the path component `pathComponent l`, composed with a
loop-space shift `π_{m+1}(L, l) ≃* π_{m+2}(X, x)`. -/
private def pathComponentShiftMulEquiv (e : ∀ m : ℕ, π_ (m + 1) L l ≃* π_ (m + 2) X x) (m : ℕ) :
    π_ (m + 1) ↥(pathComponent l) ⟨l, mem_pathComponent_self l⟩ ≃* π_ (m + 2) X x :=
  (MulEquiv.ofBijective
    (HomotopyGroup.mapHom (N := Fin (m + 1)) ⟨Subtype.val, continuous_subtype_val⟩ rfl)
    (HomotopyGroup.bijective_map_subtypeVal_of_pathComponent_subset subset_rfl rfl)).trans (e m)

private theorem isUniquelyTwoDivisible_of_loop_shift
    (e : ∀ m : ℕ, π_ (m + 1) L l ≃* π_ (m + 2) X x) {r n : ℕ} (hr : r ≤ n)
    (hconn : ∀ k, 2 ≤ k → k < r + 3 → Subsingleton (π_ k X x))
    (hH : ∀ q, r + 2 ≤ q → q ≤ n + 3 →
      Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of ↥(pathComponent l))).homology q)) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) := by
  have : PathConnectedSpace ↥(pathComponent l) :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent
  have hconn₀ (k : ℕ) (hk0 : k ≠ 0) (hk : k < r + 2) :
      Subsingleton (π_ k ↥(pathComponent l) ⟨l, mem_pathComponent_self l⟩) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have := hconn (m + 2) (by omega) (by omega)
    exact (pathComponentShiftMulEquiv e m).toEquiv.subsingleton
  have h₀ : IsUniquelyTwoDivisible
      (Additive (π_ (n + 2) ↥(pathComponent l) ⟨l, mem_pathComponent_self l⟩)) :=
    isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology hr hconn₀ hH
  exact h₀.of_addEquiv (MulEquiv.toAdditive (pathComponentShiftMulEquiv e (n + 1)))

end Shift

section PathLoopSpace

variable {X : Type} [TopologicalSpace X] {x : X}

/-- **Mod-two vanishing for `π_{n+3}(X, x)` via the basepoint component of `Ω X x` (simplicial
singular homology).** If `πₖ(X, x)` vanishes for `2 ≤ k < r + 3` (`r ≤ n`) and the mod-two
singular homology of `pathComponent (Path.refl x)` vanishes in degrees `r + 2 ≤ q ≤ n + 3`, then
`π_{n+3}(X, x)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_loopSpace_singularHomology
    {r n : ℕ} (hr : r ≤ n) (hconn : ∀ k, 2 ≤ k → k < r + 3 → Subsingleton (π_ k X x))
    (hH : ∀ q, r + 2 ≤ q → q ≤ n + 3 → Subsingleton
      (((singularChains (ZMod 2)).obj (TopCat.of ↥(pathComponent (Path.refl x)))).homology q)) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) :=
  isUniquelyTwoDivisible_of_loop_shift HomotopyGroup.pathLoopSpaceMulEquiv hr hconn hH

/-- **Mod-two vanishing for `π_{n+3}(X, x)` via the basepoint component of `Ω X x` (normalized
cubical homology).** -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_loopSpace_cubicalHomology
    {r n : ℕ} (hr : r ≤ n) (hconn : ∀ k, 2 ≤ k → k < r + 3 → Subsingleton (π_ k X x))
    (hH : ∀ q, r + 2 ≤ q → q ≤ n + 3 → Subsingleton (((normalizedCubicalChainComplex (ZMod 2)).obj
      (TopCat.of ↥(pathComponent (Path.refl x)))).homology q)) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_loopSpace_singularHomology
    hr hconn fun q hq₁ hq₂ ↦
      have := hH q hq₁ hq₂
      (singularCubicalHomologyIso (ZMod 2) _ q).toLinearEquiv.toEquiv.subsingleton

section SubsingletonPi2

variable [Subsingleton (π_ 2 X x)]

/-- When `π₂(X, x)` is trivial (with no hypothesis on `π₁(X, x)`), vanishing of `H_q(Ω₀ X; 𝔽₂)` for
`2 ≤ q ≤ n + 3` makes `π_{n+3}(X, x)` uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_loopSpace_of_subsingleton_pi2
    {n : ℕ} (hH : ∀ q, 2 ≤ q → q ≤ n + 3 → Subsingleton
      (((singularChains (ZMod 2)).obj (TopCat.of ↥(pathComponent (Path.refl x)))).homology q)) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_loopSpace_singularHomology
    (Nat.zero_le n) (fun k hk₁ hk₂ ↦ by obtain rfl : k = 2 := by omega
                                        infer_instance) hH

/-- **Topological input to Theorem 5.15 of Barraud--Damian--Humilière--Oancea (simplicial singular
homology).** If `π₂(X, x)` is trivial and `π_{n+3}(X, x) ⊗[ℤ] ℤ/2` is nontrivial, then the
basepoint component `pathComponent (Path.refl x)` of `Ω X x` has nontrivial mod-two singular
homology in some degree `2 ≤ q ≤ n + 3`. -/
theorem exists_nontrivial_pathComponent_loopSpace_singularHomology_mod_two {n : ℕ}
    (hπ : Nontrivial (TensorProduct ℤ (Additive (π_ (n + 3) X x)) (ZMod 2))) :
    ∃ q, 2 ≤ q ∧ q ≤ n + 3 ∧ Nontrivial
      (((singularChains (ZMod 2)).obj (TopCat.of ↥(pathComponent (Path.refl x)))).homology q) := by
  by_contra! h
  have := (isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_loopSpace_of_subsingleton_pi2
    (x := x) h).subsingleton_tensorProduct_zmod_two
  exact false_of_nontrivial_of_subsingleton (TensorProduct ℤ (Additive (π_ (n + 3) X x)) (ZMod 2))

/-- **Topological input to Theorem 5.15 of Barraud--Damian--Humilière--Oancea (normalized cubical
homology).** If `π₂(X, x)` is trivial and `π_{n+3}(X, x) ⊗[ℤ] ℤ/2` is nontrivial, then the
basepoint component `pathComponent (Path.refl x)` of `Ω X x` has nontrivial mod-two cubical
homology in some degree `2 ≤ q ≤ n + 3`. -/
theorem exists_nontrivial_pathComponent_loopSpace_cubicalHomology_mod_two {n : ℕ}
    (hπ : Nontrivial (TensorProduct ℤ (Additive (π_ (n + 3) X x)) (ZMod 2))) :
    ∃ q, 2 ≤ q ∧ q ≤ n + 3 ∧ Nontrivial (((normalizedCubicalChainComplex (ZMod 2)).obj
      (TopCat.of ↥(pathComponent (Path.refl x)))).homology q) := by
  obtain ⟨q, hq₁, hq₂, hq⟩ :=
    exists_nontrivial_pathComponent_loopSpace_singularHomology_mod_two hπ
  exact ⟨q, hq₁, hq₂,
    (singularCubicalHomologyIso (ZMod 2) _ q).symm.toLinearEquiv.toEquiv.nontrivial⟩

end SubsingletonPi2

end PathLoopSpace

namespace MooreLoopSpace

variable {X : Type} [TopologicalSpace X] {x : X}

/-- **Mod-two vanishing for `π_{n+3}(X, x)` via the unit component of `MooreLoopSpace X x`
(simplicial singular homology).** -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_singularHomology
    {r n : ℕ} (hr : r ≤ n) (hconn : ∀ k, 2 ≤ k → k < r + 3 → Subsingleton (π_ k X x))
    (hH : ∀ q, r + 2 ≤ q → q ≤ n + 3 → Subsingleton (((singularChains (ZMod 2)).obj
      (TopCat.of ↥(pathComponent (1 : MooreLoopSpace X x)))).homology q)) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) :=
  isUniquelyTwoDivisible_of_loop_shift (homotopyGroupMulEquiv x) hr hconn hH

/-- **Mod-two vanishing for `π_{n+3}(X, x)` via the unit component of `MooreLoopSpace X x`
(normalized cubical homology).** -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_cubicalHomology
    {r n : ℕ} (hr : r ≤ n) (hconn : ∀ k, 2 ≤ k → k < r + 3 → Subsingleton (π_ k X x))
    (hH : ∀ q, r + 2 ≤ q → q ≤ n + 3 → Subsingleton (((normalizedCubicalChainComplex (ZMod 2)).obj
      (TopCat.of ↥(pathComponent (1 : MooreLoopSpace X x)))).homology q)) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_singularHomology
    hr hconn fun q hq₁ hq₂ ↦
      have := hH q hq₁ hq₂
      (singularCubicalHomologyIso (ZMod 2) _ q).toLinearEquiv.toEquiv.subsingleton

section SubsingletonPi2

variable [Subsingleton (π_ 2 X x)]

/-- When `π₂(X, x)` is trivial, vanishing of the mod-two singular homology of the unit component of
`MooreLoopSpace X x` in degrees `2 ≤ q ≤ n + 3` makes `π_{n+3}(X, x)` uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_pi2
    {n : ℕ} (hH : ∀ q, 2 ≤ q → q ≤ n + 3 → Subsingleton (((singularChains (ZMod 2)).obj
      (TopCat.of ↥(pathComponent (1 : MooreLoopSpace X x)))).homology q)) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_pathComponent_singularHomology
    (Nat.zero_le n) (fun k hk₁ hk₂ ↦ by obtain rfl : k = 2 := by omega
                                        infer_instance) hH

/-- **Topological input to Theorem 5.15 of Barraud--Damian--Humilière--Oancea, for Moore loops
(simplicial singular homology).** If `π₂(X, x)` is trivial and `π_{n+3}(X, x) ⊗[ℤ] ℤ/2` is
nontrivial, then `pathComponent (1 : MooreLoopSpace X x)` has nontrivial mod-two singular homology
in some degree `2 ≤ q ≤ n + 3`. -/
theorem exists_nontrivial_pathComponent_singularHomology_mod_two {n : ℕ}
    (hπ : Nontrivial (TensorProduct ℤ (Additive (π_ (n + 3) X x)) (ZMod 2))) :
    ∃ q, 2 ≤ q ∧ q ≤ n + 3 ∧ Nontrivial (((singularChains (ZMod 2)).obj
      (TopCat.of ↥(pathComponent (1 : MooreLoopSpace X x)))).homology q) := by
  by_contra! h
  have := (isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_pi2
    (x := x) h).subsingleton_tensorProduct_zmod_two
  exact false_of_nontrivial_of_subsingleton (TensorProduct ℤ (Additive (π_ (n + 3) X x)) (ZMod 2))

/-- **Topological input to Theorem 5.15 of Barraud--Damian--Humilière--Oancea, for Moore loops
(normalized cubical homology).** If `π₂(X, x)` is trivial and `π_{n+3}(X, x) ⊗[ℤ] ℤ/2` is
nontrivial, then `pathComponent (1 : MooreLoopSpace X x)` has nontrivial mod-two cubical homology
in some degree `2 ≤ q ≤ n + 3`. -/
theorem exists_nontrivial_pathComponent_cubicalHomology_mod_two {n : ℕ}
    (hπ : Nontrivial (TensorProduct ℤ (Additive (π_ (n + 3) X x)) (ZMod 2))) :
    ∃ q, 2 ≤ q ∧ q ≤ n + 3 ∧ Nontrivial (((normalizedCubicalChainComplex (ZMod 2)).obj
      (TopCat.of ↥(pathComponent (1 : MooreLoopSpace X x)))).homology q) := by
  obtain ⟨q, hq₁, hq₂, hq⟩ := exists_nontrivial_pathComponent_singularHomology_mod_two hπ
  exact ⟨q, hq₁, hq₂,
    (singularCubicalHomologyIso (ZMod 2) _ q).symm.toLinearEquiv.toEquiv.nontrivial⟩

end SubsingletonPi2

end MooreLoopSpace

end TauCeti
