/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ULift
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Comparison
public import TauCeti.AlgebraicTopology.Singular.Coefficients.TwoDivisible
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Basic
import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover.Homology
import TauCeti.AlgebraicTopology.Singular.Coefficients.ModTwo
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# Mod-two vanishing of homotopy groups via the Whitehead tower

Let `X` be a path-connected space whose homotopy groups vanish in dimensions `1 ≤ k < r + 2`. If
the mod-two singular homology `H_q(X; 𝔽₂)` vanishes in the range `r + 2 ≤ q ≤ n + 3` (`r ≤ n`),
then the homotopy group `π_{n+2}(X, x)` is uniquely two-divisible
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`). In particular it
is a module over `ℤ[1/2]`, and its tensor product `π_{n+2}(X, x) ⊗ ℤ/2` vanishes. No finite
generation, Hausdorffness, or CW hypothesis on `X` is needed.

When `X` is simply connected (`r = 0`) and mod-two acyclic in degrees `2 ≤ q ≤ n + 3`, every
higher homotopy group up to `π_{n+2}(X, x)` is uniquely two-divisible
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace`);
contrapositively, if `π_{n+2}(X, x) ⊗ ℤ/2` is nontrivial, then `H_q(X; 𝔽₂) ≠ 0` for some degree
`2 ≤ q ≤ n + 3`
(`TauCeti.exists_nontrivial_singularHomology_mod_two_of_nontrivial_tensorProduct`, and its cubical
counterpart `TauCeti.exists_nontrivial_cubicalHomology_mod_two_of_nontrivial_tensorProduct`).

The proof climbs the Whitehead tower of a CW approximation of `X`:

1. **Base step** (`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_mod_two`): for an
   `(r + 1)`-connected space, the Hurewicz isomorphism identifies `π_{r+2}` with `H_{r+2}(X; ℤ)`,
   on which vanishing of mod-two homology in degrees `r + 2` and `r + 3` makes multiplication by
   two bijective via the coefficient exact sequence `0 → ℤ → ℤ → ℤ/2 → 0`.
2. **Inductive step**: on a Hausdorff `(r + 1)`-connected space whose `π_{r+2}` is uniquely
   two-divisible, the `(r + 2)`-connected cover `X⟨r + 2⟩ → X` is a Serre fibration with fibres of
   type `K(π_{r+2}, r + 1)`, which have the mod-two homology of a point
   (`TauCeti.IsEilenbergMacLaneSpace.isIso_singularHomologyMap_to_point_of_isUniquelyTwoDivisible`),
   so `H_*(X⟨r + 2⟩; 𝔽₂) ≅ H_*(X; 𝔽₂)` (`TauCeti.nConnectedCoverSingularHomologyModTwoIso`) while
   `π_k(X⟨r + 2⟩) ≅ π_k(X)` for `k > r + 2`.
3. **Arbitrary spaces**: precomposing with `TauCeti.cwApproximationMap` reduces from any
   path-connected space to a Hausdorff CW complex without changing homotopy groups or singular
   homology.

## Main results

* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_mod_two`: base case for the first
  possible nonzero homotopy group `π_{n+2}` from integral `ℤ/2`-homology in degrees `n + 2` and
  `n + 3`.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_cubicalHomology`: general
  `(r + 1)`-connected, degree-bounded mod-two vanishing for simplicial and cubical homology.
* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace_of_cubicalHomology`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_reducedSingularHomology_mod_two`:
  simply connected specializations.
* `TauCeti.exists_nontrivial_singularHomology_mod_two_of_nontrivial_tensorProduct`,
  `TauCeti.exists_nontrivial_cubicalHomology_mod_two_of_nontrivial_tensorProduct`: nonvanishing of
  `π_{n+2}(X, x) ⊗ ℤ/2` forces nontrivial mod-two homology in some degree `2 ≤ q ≤ n + 3`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Sections 3.A, 4.2, and 4.3.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  Chapter III.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorem 5.15.
-/

public noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy

namespace TauCeti

section BaseStep

variable {X : Type} [TopologicalSpace X] {x : X} {n : ℕ}

/-- If all lower homotopy groups vanish, vanishing of mod-two homology in two adjacent
higher degrees makes the first possible nonzero homotopy group uniquely two-divisible.
The group is written additively to use its canonical integer action. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_mod_two
    (hX : ∀ k < n + 2, Subsingleton (HomotopyGroup (Fin k) X x))
    (hn : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ (ZMod 2))).obj (TopCat.of X)))
    (hn' : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 3)).obj
      (ModuleCat.of ℤ (ZMod 2))).obj (TopCat.of X))) :
    IsUniquelyTwoDivisible (Additive (HomotopyGroup (Fin (n + 2)) X x)) := by
  -- The coefficient exact sequence uses lifted coefficients; transport the two zero objects.
  have liftZero (k : ℕ)
      (hk : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
        (ModuleCat.of ℤ (ZMod 2))).obj (TopCat.of X))) :
      Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj
        (ModuleCat.of ℤ (ULift.{0} (ZMod 2)))).obj (TopCat.of X)) :=
    hk.of_iso (((singularHomologyFunctor (ModuleCat.{0} ℤ) k).mapIso
      (ULift.moduleEquiv : ULift.{0} (ZMod 2) ≃ₗ[ℤ] ZMod 2).toModuleIso).app (TopCat.of X))
  have h := (TopCat.of X).isUniquelyTwoDivisible_singularHomology_of_isZero_mod_two
    (n + 2) (liftZero _ hn) (liftZero _ hn')
  let e : (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).obj (TopCat.of X)) ≃+
      ((singularChains ℤ).obj (TopCat.of X)).homology (n + 2) :=
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 2)).mapIso
      (ULift.moduleEquiv : ULift ℤ ≃ₗ[ℤ] ℤ).toModuleIso).app
        (TopCat.of X)).toLinearEquiv.toAddEquiv
  exact (h.of_addEquiv e).of_addEquiv
    (HomotopyGroup.cubicalHurewiczSingularHomologyAddEquiv hX).symm

end BaseStep

/-! ### Climbing the Whitehead tower -/

private theorem isZero_singularHomology_int_zmod_two_of_subsingleton {X : TopCat.{0}} {q : ℕ}
    (hq : Subsingleton (((singularChains (ZMod 2)).obj X).homology q)) :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj
      (ModuleCat.of ℤ (ZMod 2))).obj X) := by
  have hF₂ : Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj
      (ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2)))).obj X) :=
    (ModuleCat.isZero_iff_subsingleton.2 hq).of_iso
      (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).mapIso
        (ULift.moduleEquiv : ULift.{0} (ZMod 2) ≃ₗ[ZMod 2] ZMod 2).toModuleIso).app X)
  exact ((X.isZero_singularHomology_modTwo_iff q).2 hF₂).of_iso
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) q).mapIso
      (ULift.moduleEquiv : ULift.{0} (ZMod 2) ≃ₗ[ℤ] ZMod 2).symm.toModuleIso).app X)

private theorem isUniquelyTwoDivisible_first_homotopyGroup_of_subsingleton_mod_two
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] {x : X} {r : ℕ}
    (hconn : ∀ k, k ≠ 0 → k < r + 2 → Subsingleton (π_ k X x))
    (h₁ : Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of X)).homology (r + 2)))
    (h₂ : Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of X)).homology (r + 3))) :
    IsUniquelyTwoDivisible (Additive (π_ (r + 2) X x)) := by
  refine isUniquelyTwoDivisible_homotopyGroup_of_isZero_mod_two (fun k hk ↦ ?_)
    (isZero_singularHomology_int_zmod_two_of_subsingleton h₁)
    (isZero_singularHomology_int_zmod_two_of_subsingleton h₂)
  rcases eq_or_ne k 0 with rfl | hk0
  · exact (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero x).1 inferInstance
  · exact hconn k hk0 hk

private theorem isUniquelyTwoDivisible_homotopyGroup_of_t2Space :
    ∀ {m r : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [PathConnectedSpace X] {x : X},
      (∀ k, k ≠ 0 → k < r + 2 → Subsingleton (π_ k X x)) →
      (∀ q, r + 2 ≤ q → q ≤ r + m + 3 →
        Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of X)).homology q)) →
      IsUniquelyTwoDivisible (Additive (π_ (r + m + 2) X x))
  | 0, r, X, _, _, _, x, hconn, hH =>
    isUniquelyTwoDivisible_first_homotopyGroup_of_subsingleton_mod_two hconn
      (hH (r + 2) (by omega) (by omega)) (hH (r + 3) (by omega) (by omega))
  | m + 1, r, X, _, hT2, hPC, x, hconn, hH => by
    have : T2Space (TopCat.of X) := hT2
    have : PathConnectedSpace (TopCat.of X) := hPC
    have hπ₀ : IsUniquelyTwoDivisible (Additive (π_ (r + 2) X x)) :=
      isUniquelyTwoDivisible_first_homotopyGroup_of_subsingleton_mod_two hconn
        (hH (r + 2) (by omega) (by omega)) (hH (r + 3) (by omega) (by omega))
    -- Pass to the `(r + 2)`-connected cover `Y = X⟨r + 2⟩`, which has the same mod-two homology.
    let Y : TopCat.{0} := nConnectedCover (r + 2) (TopCat.of X) x
    let y : Y := nConnectedCoverBasepoint (r + 2) (TopCat.of X) x
    have : T2Space Y := inferInstanceAs (T2Space (nConnectedCover (r + 2) (TopCat.of X) x))
    have : PathConnectedSpace Y := pathConnectedSpace_nConnectedCover (r + 2) (TopCat.of X) x
    have hYconn (k : ℕ) (hk0 : k ≠ 0) (hk : k < (r + 1) + 2) : Subsingleton (π_ k Y y) :=
      subsingleton_homotopyGroup_nConnectedCover (r + 2) (TopCat.of X) x hk0 (by omega)
    have hYH (q : ℕ) (hq₁ : (r + 1) + 2 ≤ q) (hq₂ : q ≤ (r + 1) + m + 3) :
        Subsingleton (((singularChains (ZMod 2)).obj Y).homology q) := by
      have := hH q (by omega) (by omega)
      exact (nConnectedCoverSingularHomologyModTwoIso (X := TopCat.of X) hconn hπ₀
        q).toLinearEquiv.toEquiv.subsingleton
    have hY : IsUniquelyTwoDivisible (Additive (π_ ((r + 1) + m + 2) Y y)) :=
      isUniquelyTwoDivisible_homotopyGroup_of_t2Space (r := r + 1) (X := Y) (x := y) hYconn hYH
    rw [show r + (m + 1) = (r + 1) + m by omega]
    let eπ : π_ ((r + 1) + m + 2) Y y ≃* π_ ((r + 1) + m + 2) X x :=
      nConnectedCoverHomotopyGroupMulEquiv (r + 2) (TopCat.of X) x ((r + 1) + m + 2) (by omega)
    exact hY.of_addEquiv (MulEquiv.toAdditive eπ)

section General

variable {X : Type} [TopologicalSpace X] [PathConnectedSpace X] {x : X}

/-- **Mod-two vanishing of homotopy groups (simplicial singular homology).** Let `X` be a
path-connected space (not assumed Hausdorff or of CW type) whose homotopy groups `πₖ(X, x)` vanish
for `1 ≤ k < r + 2`. If `H_q(X; 𝔽₂) = 0` for `r + 2 ≤ q ≤ n + 3` (`r ≤ n`), then
`π_{n+2}(X, x)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology {r n : ℕ}
    (hr : r ≤ n) (hconn : ∀ k, k ≠ 0 → k < r + 2 → Subsingleton (π_ k X x))
    (hH : ∀ q, r + 2 ≤ q → q ≤ n + 3 →
      Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of X)).homology q)) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 2) X x)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr
  -- Replace `X` by its CW approximation `W`, which is Hausdorff and weakly homotopy equivalent.
  let W : TopCat.{0} := cwApproximation (TopCat.of X) x
  let w : W := cwApproximationBasepoint (TopCat.of X) x
  have : T2Space W := instT2SpaceCWApproximation (TopCat.of X) x
  have : PathConnectedSpace W :=
    inferInstanceAs (PathConnectedSpace (cwApproximation (TopCat.of X) x))
  let g := cwApproximationMap (TopCat.of X) x
  have hg : g.hom.IsWeakHomotopyEquivalence :=
    isWeakHomotopyEquivalence_cwApproximationMap (TopCat.of X) x
  have ebij (k : ℕ) : Function.Bijective (HomotopyGroup.map (N := Fin (k + 1)) g.hom
      (cwApproximationMap_cwApproximationBasepoint (TopCat.of X) x)) :=
    (HomotopyGroup.bijective_map_congr rfl rfl
      (cwApproximationMap_cwApproximationBasepoint (TopCat.of X) x)).1
        (bijective_homotopyGroupMap_cwApproximationMap (TopCat.of X) x k w)
  have hWconn (k : ℕ) (hk0 : k ≠ 0) (hk : k < r + 2) : Subsingleton (π_ k W w) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have := hconn (j + 1) j.succ_ne_zero hk
    exact (Equiv.ofBijective _ (ebij j)).subsingleton
  have hWH (q : ℕ) (hq₁ : r + 2 ≤ q) (hq₂ : q ≤ r + m + 3) :
      Subsingleton (((singularChains (ZMod 2)).obj W).homology q) := by
    have : Subsingleton (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj
        (ModuleCat.of (ZMod 2) (ZMod 2))).obj (TopCat.of X)) := hH q hq₁ hq₂
    have := hg.isIso_singularHomologyMap (ModuleCat.of (ZMod 2) (ZMod 2)) q
    exact (asIso (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj
      (ModuleCat.of (ZMod 2) (ZMod 2))).map g)).toLinearEquiv.toEquiv.subsingleton
  have hW : IsUniquelyTwoDivisible (Additive (π_ (r + m + 2) W w)) :=
    isUniquelyTwoDivisible_homotopyGroup_of_t2Space (X := W) (x := w) hWconn hWH
  let eπ : π_ (r + m + 2) W w ≃* π_ (r + m + 2) X x :=
    MulEquiv.ofBijective (HomotopyGroup.mapHom g.hom
      (cwApproximationMap_cwApproximationBasepoint (TopCat.of X) x)) (ebij (r + m + 1))
  exact hW.of_addEquiv (MulEquiv.toAdditive eπ)

/-- **Mod-two vanishing of homotopy groups (normalized cubical homology).** Let `X` be a
path-connected space whose homotopy groups `πₖ(X, x)` vanish for `1 ≤ k < r + 2`. If the
normalized cubical mod-two homology vanishes in degrees `r + 2 ≤ q ≤ n + 3` (`r ≤ n`), then
`π_{n+2}(X, x)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_cubicalHomology {r n : ℕ}
    (hr : r ≤ n) (hconn : ∀ k, k ≠ 0 → k < r + 2 → Subsingleton (π_ k X x))
    (hH : ∀ q, r + 2 ≤ q → q ≤ n + 3 →
      Subsingleton (((normalizedCubicalChainComplex (ZMod 2)).obj (TopCat.of X)).homology q)) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 2) X x)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology hr hconn fun q hq₁ hq₂ ↦
    have := hH q hq₁ hq₂
    (singularCubicalHomologyIso (ZMod 2) (TopCat.of X) q).toLinearEquiv.toEquiv.subsingleton

end General

/-! ### Simply connected spaces -/

section SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] {x : X}

/-- **Degree-bounded mod-two vanishing for simply connected spaces.** If `X` is simply connected
and `H_q(X; 𝔽₂) = 0` for `2 ≤ q ≤ n + 3`, then `π_{n+2}(X, x)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace
    {n : ℕ} (hH : ∀ q, 2 ≤ q → q ≤ n + 3 →
      Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of X)).homology q)) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 2) X x)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology (Nat.zero_le n)
    (fun k hk0 hk ↦ by obtain rfl : k = 1 := by omega
                       exact HomotopyGroup.pi1EquivFundamentalGroup.subsingleton) hH

/-- **Degree-bounded cubical mod-two vanishing for simply connected spaces.** If `X` is simply
connected and its normalized cubical mod-two homology vanishes in degrees `2 ≤ q ≤ n + 3`, then
`π_{n+2}(X, x)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace_of_cubicalHomology
    {n : ℕ} (hH : ∀ q, 2 ≤ q → q ≤ n + 3 →
      Subsingleton (((normalizedCubicalChainComplex (ZMod 2)).obj (TopCat.of X)).homology q)) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 2) X x)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_cubicalHomology (Nat.zero_le n)
    (fun k hk0 hk ↦ by obtain rfl : k = 1 := by omega
                       exact HomotopyGroup.pi1EquivFundamentalGroup.subsingleton) hH

/-- **Mod-two acyclic simply connected spaces have uniquely two-divisible homotopy groups.** If `X`
is simply connected and its reduced mod-two singular homology vanishes in every degree `≥ 2`, then
every higher homotopy group `π_{n+2}(X, x)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_isZero_reducedSingularHomology_mod_two
    (hH : ∀ q, 2 ≤ q → Limits.IsZero
      ((reducedSingularHomologyFunctor (ModuleCat.of (ZMod 2) (ZMod 2)) q).obj (TopCat.of X)))
    (n : ℕ) :
    IsUniquelyTwoDivisible (Additive (π_ (n + 2) X x)) :=
  isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace
    fun q hq _ ↦ by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      exact ModuleCat.isZero_iff_subsingleton.1 <| (hH (r + 1) hq).of_iso
        ((reducedSingularHomologySuccIso (ModuleCat.of (ZMod 2) (ZMod 2)) r).app
          (TopCat.of X)).symm

/-- If `X` is simply connected and `H_q(X; 𝔽₂) = 0` for `2 ≤ q ≤ n + 3`, then
`π_{n+2}(X, x) ⊗[ℤ] ℤ/2 = 0`. -/
theorem subsingleton_tensorProduct_zmod_two_homotopyGroup_of_simplyConnectedSpace {n : ℕ}
    (hH : ∀ q, 2 ≤ q → q ≤ n + 3 →
      Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of X)).homology q)) :
    Subsingleton (TensorProduct ℤ (Additive (π_ (n + 2) X x)) (ZMod 2)) :=
  (isUniquelyTwoDivisible_homotopyGroup_of_simplyConnectedSpace
    hH).subsingleton_tensorProduct_zmod_two

/-- **Nonvanishing of `π_{n+2}(X, x) ⊗ ℤ/2` forces nontrivial mod-two singular homology.** If `X`
is simply connected and `π_{n+2}(X, x) ⊗[ℤ] ℤ/2` is nontrivial, then `H_q(X; 𝔽₂)` is nontrivial in
some degree `2 ≤ q ≤ n + 3`. -/
theorem exists_nontrivial_singularHomology_mod_two_of_nontrivial_tensorProduct {n : ℕ}
    (hπ : Nontrivial (TensorProduct ℤ (Additive (π_ (n + 2) X x)) (ZMod 2))) :
    ∃ q, 2 ≤ q ∧ q ≤ n + 3 ∧
      Nontrivial (((singularChains (ZMod 2)).obj (TopCat.of X)).homology q) := by
  by_contra! h
  have := subsingleton_tensorProduct_zmod_two_homotopyGroup_of_simplyConnectedSpace (x := x) h
  exact false_of_nontrivial_of_subsingleton (TensorProduct ℤ (Additive (π_ (n + 2) X x)) (ZMod 2))

/-- **Nonvanishing of `π_{n+2}(X, x) ⊗ ℤ/2` forces nontrivial mod-two cubical homology.** If `X`
is simply connected and `π_{n+2}(X, x) ⊗[ℤ] ℤ/2` is nontrivial, then the normalized cubical
mod-two homology of `X` is nontrivial in some degree `2 ≤ q ≤ n + 3`. -/
theorem exists_nontrivial_cubicalHomology_mod_two_of_nontrivial_tensorProduct {n : ℕ}
    (hπ : Nontrivial (TensorProduct ℤ (Additive (π_ (n + 2) X x)) (ZMod 2))) :
    ∃ q, 2 ≤ q ∧ q ≤ n + 3 ∧
      Nontrivial (((normalizedCubicalChainComplex (ZMod 2)).obj (TopCat.of X)).homology q) := by
  obtain ⟨q, hq₁, hq₂, hq⟩ :=
    exists_nontrivial_singularHomology_mod_two_of_nontrivial_tensorProduct hπ
  exact ⟨q, hq₁, hq₂,
    (singularCubicalHomologyIso (ZMod 2) (TopCat.of X) q).symm.toLinearEquiv.toEquiv.nontrivial⟩

end SimplyConnected

end TauCeti
