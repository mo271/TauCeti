/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Homology
public import TauCeti.AlgebraicTopology.Homotopy.NConnectedCover.Basic
import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison

/-!
# Singular homology of connected covers

Let `X` be a path-connected Hausdorff space that is `(m + 1)`-connected (`m ≥ 0`), so its homotopy
groups `πᵢ(X, x)` vanish for `1 ≤ i < m + 2`. Killing the homotopy groups of `X` above dimension
`m + 2` produces an Eilenberg--Mac Lane space `P_{m+2} X` of type `K(π_{m+2}(X, x), m + 2)`, and
every fibre of the `(m + 2)`-connected cover projection

`p : X⟨m + 2⟩ ⟶ X`

has the homotopy type of the loop space `Ω(P_{m+2} X)`, hence is a `K(π_{m+2}(X, x), m + 1)` space.

When multiplication by an integer `d` is bijective on `π_{m+2}(X, x)` and `k` is a commutative
semisimple ring in which `d = 0`, every fibre of `p` has the `k`-homology of a point
(`TauCeti.IsEilenbergMacLaneSpace.isIso_singularHomologyMap_to_point_of_bijective_zsmul`). Since
`p` is a Serre fibration, the fibration comparison theorem
`TauCeti.TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point` implies that `p` induces an
isomorphism on singular homology with `k`-coefficients in every degree
(`TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_of_bijective_zsmul`,
`TauCeti.nConnectedCoverSingularHomologyIsoOfBijectiveZsmul`).

Specializing to `d = 2` and `k = 𝔽₂`: whenever `π_{m+2}(X, x)` is uniquely two-divisible, passing
to the `(m + 2)`-connected cover `X⟨m + 2⟩` preserves mod-two singular homology in every degree
(`TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_of_isUniquelyTwoDivisible`,
`TauCeti.nConnectedCoverSingularHomologyModTwoIso`). Iterating this step climbs the Whitehead tower
of a space whose mod-two homology vanishes in a range of degrees.

## Main results

* `TauCeti.nonempty_fiber_nConnectedCoverProj`: over a path-connected space, every fibre of the
  `n`-connected cover projection is nonempty.
* `TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_of_bijective_zsmul`,
  `TauCeti.nConnectedCoverSingularHomologyIsoOfBijectiveZsmul`: `H_q(X⟨m + 2⟩; k) ≅ H_q(X; k)`
  when `X` is `(m + 1)`-connected, multiplication by `d` is bijective on `π_{m+2}(X, x)`, and
  `(d : k) = 0` in the commutative semisimple ring `k`.
* `TauCeti.isIso_singularHomologyMap_nConnectedCoverProj_of_isUniquelyTwoDivisible`,
  `TauCeti.nConnectedCoverSingularHomologyModTwoIso`: `H_q(X⟨m + 2⟩; 𝔽₂) ≅ H_q(X; 𝔽₂)` when
  `π_{m+2}(X, x)` is uniquely two-divisible.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.3, Postnikov and
  Whitehead towers.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  Chapter II.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti

private lemma nConnectedCoverProj_preimage_singleton (n : ℕ) (X : TopCat.{u}) (x b : X) :
    (nConnectedCoverProj n X x) ⁻¹' {b} =
      {z | MappingPathFiber.proj (killHomotopyGroupsIncl (n + 1) X x).hom
        (killHomotopyGroupsIncl (n + 1) X x x) z = b} :=
  Set.ext fun z ↦ by
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred,
      TopCat.Hom.homotopyFiberProj_apply, MappingPathFiber.proj_apply]

/-- Over a path-connected space `X`, every fibre of the `n`-connected cover projection
`X⟨n⟩ ⟶ X` is nonempty. -/
instance nonempty_fiber_nConnectedCoverProj (n : ℕ) (X : TopCat.{u}) [PathConnectedSpace X]
    (x b : X) : Nonempty ((nConnectedCoverProj n X x).fiber b) :=
  (Homeomorph.setCongr (nConnectedCoverProj_preimage_singleton n X x b)).toEquiv.nonempty_congr.2 <|
    (MappingPathFiber.nonempty_projFiber_iff _ _ b).2 <|
      (PathConnectedSpace.joined b x).map (killHomotopyGroupsIncl (n + 1) X x).hom.continuous

section Homology

variable (k : Type) [CommRing k] [IsSemisimpleRing k] {d : ℤ}
variable {X : TopCat.{0}} [T2Space X] [PathConnectedSpace X] {x : X} {m : ℕ}

/-- **Homology isomorphism for the `(m + 2)`-connected cover modulo `d`.** Let `X` be a
path-connected Hausdorff `(m + 1)`-connected space. If multiplication by `d` is bijective on
`π_{m+2}(X, x)` and `(d : k) = 0` in the commutative semisimple ring `k`, then the projection
`X⟨m + 2⟩ ⟶ X` induces an isomorphism on `H_q(-; k)` in every degree `q`. -/
theorem isIso_singularHomologyMap_nConnectedCoverProj_of_bijective_zsmul (hdk : (d : k) = 0)
    (hX : ∀ i, i ≠ 0 → i < m + 2 → Subsingleton (π_ i X x))
    (hd : Function.Bijective fun a : Additive (π_ (m + 2) X x) ↦ d • a) (q : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} k) q).obj (ModuleCat.of k k)).map
      (nConnectedCoverProj (m + 2) X x)) := by
  refine TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point
    (serreFibrations_nConnectedCoverProj (m + 2) X x) k q fun b r _ ↦ ?_
  let j := killHomotopyGroupsIncl (m + 3) X x
  let α : Path (j b) (j x) := ((PathConnectedSpace.joined b x).map j.hom.continuous).somePath
  let e := (Homeomorph.setCongr
      (nConnectedCoverProj_preimage_singleton (m + 2) X x b)).toHomotopyEquiv.trans
    (MappingPathFiber.projFiberHomotopyEquivLoopSpace j.hom (j x) b α)
  have hfib : IsEilenbergMacLaneSpace (Multiplicative (Additive (π_ (m + 2) X x))) (m + 1)
      ((nConnectedCoverProj (m + 2) X x) ⁻¹' {b}) (e.symm (Path.refl (j x))) :=
    ((isEilenbergMacLaneSpace_killHomotopyGroups (m + 2) X x hX).loopSpace.of_homotopyEquiv
      e.symm (e.symm (Path.refl (j x)))).of_mulEquiv
        (AddEquiv.toMultiplicativeRight (.refl _))
  exact hfib.isIso_singularHomologyMap_to_point_of_bijective_zsmul k hdk hd r

/-- The singular homology isomorphism `H_q(X⟨m + 2⟩; k) ≅ H_q(X; k)` induced by the projection of
the `(m + 2)`-connected cover when `X` is `(m + 1)`-connected, multiplication by `d` is bijective
on `π_{m+2}(X, x)`, and `(d : k) = 0` in the commutative semisimple ring `k`. -/
def nConnectedCoverSingularHomologyIsoOfBijectiveZsmul (hdk : (d : k) = 0)
    (hX : ∀ i, i ≠ 0 → i < m + 2 → Subsingleton (π_ i X x))
    (hd : Function.Bijective fun a : Additive (π_ (m + 2) X x) ↦ d • a) (q : ℕ) :
    ((singularChains k).obj (nConnectedCover (m + 2) X x)).homology q ≅
      ((singularChains k).obj X).homology q :=
  @asIso _ _ _ _
    (((singularHomologyFunctor (ModuleCat.{0} k) q).obj (ModuleCat.of k k)).map
      (nConnectedCoverProj (m + 2) X x))
    (isIso_singularHomologyMap_nConnectedCoverProj_of_bijective_zsmul k hdk hX hd q)

@[simp]
theorem nConnectedCoverSingularHomologyIsoOfBijectiveZsmul_hom (hdk : (d : k) = 0)
    (hX : ∀ i, i ≠ 0 → i < m + 2 → Subsingleton (π_ i X x))
    (hd : Function.Bijective fun a : Additive (π_ (m + 2) X x) ↦ d • a) (q : ℕ) :
    (nConnectedCoverSingularHomologyIsoOfBijectiveZsmul k hdk hX hd q).hom =
      ((singularHomologyFunctor (ModuleCat.{0} k) q).obj (ModuleCat.of k k)).map
        (nConnectedCoverProj (m + 2) X x) :=
  (rfl)

/-- **Mod-two homology isomorphism for the `(m + 2)`-connected cover.** Let `X` be a
path-connected Hausdorff `(m + 1)`-connected space whose `(m + 2)`-nd homotopy group is uniquely
two-divisible. Then the projection `X⟨m + 2⟩ ⟶ X` induces an isomorphism on mod-two singular
homology in every degree. -/
theorem isIso_singularHomologyMap_nConnectedCoverProj_of_isUniquelyTwoDivisible
    (hX : ∀ i, i ≠ 0 → i < m + 2 → Subsingleton (π_ i X x))
    (hπ : IsUniquelyTwoDivisible (Additive (π_ (m + 2) X x))) (q : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj
      (ModuleCat.of (ZMod 2) (ZMod 2))).map (nConnectedCoverProj (m + 2) X x)) :=
  isIso_singularHomologyMap_nConnectedCoverProj_of_bijective_zsmul (ZMod 2) (d := 2) (by decide)
    hX ((isUniquelyTwoDivisible_iff _).1 hπ) q

/-- The mod-two singular homology isomorphism `H_q(X⟨m + 2⟩; 𝔽₂) ≅ H_q(X; 𝔽₂)` induced by the
projection of the `(m + 2)`-connected cover when `X` is `(m + 1)`-connected and `π_{m+2}(X, x)` is
uniquely two-divisible. -/
def nConnectedCoverSingularHomologyModTwoIso
    (hX : ∀ i, i ≠ 0 → i < m + 2 → Subsingleton (π_ i X x))
    (hπ : IsUniquelyTwoDivisible (Additive (π_ (m + 2) X x))) (q : ℕ) :
    ((singularChains (ZMod 2)).obj (nConnectedCover (m + 2) X x)).homology q ≅
      ((singularChains (ZMod 2)).obj X).homology q :=
  nConnectedCoverSingularHomologyIsoOfBijectiveZsmul (ZMod 2) (d := 2) (by decide) hX
    ((isUniquelyTwoDivisible_iff _).1 hπ) q

@[simp]
theorem nConnectedCoverSingularHomologyModTwoIso_hom
    (hX : ∀ i, i ≠ 0 → i < m + 2 → Subsingleton (π_ i X x))
    (hπ : IsUniquelyTwoDivisible (Additive (π_ (m + 2) X x))) (q : ℕ) :
    (nConnectedCoverSingularHomologyModTwoIso hX hπ q).hom =
      ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj
        (ModuleCat.of (ZMod 2) (ZMod 2))).map (nConnectedCoverProj (m + 2) X x) :=
  (rfl)

end Homology

end TauCeti
