/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Homology
public import TauCeti.AlgebraicTopology.ClassifyingSpace.UniquelyDivisible
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Degree
public import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.AlgebraicTopology.ClassifyingSpace.Uniqueness
import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv
import TauCeti.AlgebraicTopology.EilenbergMacLane.LoopSpace
import TauCeti.AlgebraicTopology.Singular.Contractible
import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
import TauCeti.Topology.Homotopy.MappingPath.PathFibration

/-!
# The singular homology of `K(G, 1)` spaces and acyclicity of `K(A, n)` spaces

Every `K(G, 1)` space `X`, of any kind, receives a weak homotopy equivalence from Milnor's
classifying space `classifyingSpace G`
(`TauCeti.IsEilenbergMacLaneSpaceOne.exists_isWeakHomotopyEquivalence_classifyingSpace`), and weak
homotopy equivalences induce isomorphisms on singular homology. So the singular homology of `X`
with coefficients in a commutative ring `k` is the group homology of `G` with trivial coefficients
`k` (`TauCeti.IsEilenbergMacLaneSpaceOne.nonempty_singularHomologyIsoGroupHomology`):

`Hₙ(X; k) ≅ Hₙ(G, k)`.

The spaces of interest need not have CW type. The loop space of a `K(A, n + 2)` space is a
`K(A, n + 1)` space, and so is every fibre of the fixed-end path fibration over it. If `A` is an
abelian group on which multiplication by an integer `m` is bijective and `k` is a commutative
semisimple ring in which `m = 0`, then:

* in degree `n = 1`, every `K(A, 1)` space has the `k`-homology of a point
  (`TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul`), by
  comparison with the group homology of `A`;
* by induction on `n ≥ 1` along the fixed-end path fibration `ΩX → PX → X`, whose total space is
  contractible and whose fibres have the homotopy type of `ΩX`, every `K(A, n)` space has the
  `k`-homology of a point
  (`TauCeti.IsEilenbergMacLaneSpace.isIso_singularHomologyMap_to_point_of_bijective_zsmul`,
  `TauCeti.IsEilenbergMacLaneSpace.isZero_reducedSingularHomologyFunctor_of_bijective_zsmul`,
  `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`), via the
  fibration homology comparison `TauCeti.TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point`.

For `m = 2` and `k = 𝔽₂`: every `K(A, n)` space (`n ≥ 1`) of a uniquely two-divisible abelian
group `A` has the mod-two homology of a point
(`TauCeti.IsEilenbergMacLaneSpace.isIso_singularHomologyMap_to_point_of_isUniquelyTwoDivisible`,
`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`). Stated
for every space having the homotopy groups of `K(A, n)`, this applies directly to the fibres of
the Whitehead tower without choosing functorial CW models.

## Main results

* `TauCeti.IsEilenbergMacLaneSpaceOne.nonempty_singularHomologyIsoGroupHomology`: the singular
  homology of a `K(G, 1)` space is the group homology of `G`.
* `TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul`,
  `TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_isUniquelyTwoDivisible`:
  acyclicity of `K(A, 1)` spaces modulo `m` and modulo `2`.
* `TauCeti.IsEilenbergMacLaneSpace.isIso_singularHomologyMap_to_point_of_bijective_zsmul`,
  `TauCeti.IsEilenbergMacLaneSpace.isZero_reducedSingularHomologyFunctor_of_bijective_zsmul`,
  `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`:
  acyclicity of `K(A, n)` spaces (`n ≥ 1`) modulo `m`.
* `TauCeti.IsEilenbergMacLaneSpace.isIso_singularHomologyMap_to_point_of_isUniquelyTwoDivisible`,
  `TauCeti.IsEilenbergMacLaneSpace.isZero_reducedSingularHomologyFunctor_of_isUniquelyTwoDivisible`,
  `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`:
  mod-two acyclicity of `K(A, n)` spaces (`n ≥ 1`) of uniquely two-divisible abelian groups.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.1,
  Proposition 4.21, and Section 4.2, Proposition 4.30.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  Chapter I and Chapter II.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory

universe u

namespace TauCeti

namespace IsEilenbergMacLaneSpaceOne

/-- **The singular homology of a `K(G, 1)` space is the group homology of `G`.** For every
`K(G, 1)` space `X`, with no hypothesis of CW type, and every commutative ring `k`,
`Hₙ(X; k) ≅ Hₙ(G, k)`, the group homology of `G` with trivial coefficients `k`. -/
theorem nonempty_singularHomologyIsoGroupHomology {G : Type u} [Group G] {X : Type u}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpaceOne G X x) (k : Type u)
    [CommRing k] (n : ℕ) :
    Nonempty (((singularChains k).obj (TopCat.of X)).homology n ≅
      groupHomology (Rep.trivial k G k) n) := by
  obtain ⟨f, hf⟩ := hX.exists_isWeakHomotopyEquivalence_classifyingSpace
  have := hf.isIso_singularHomologyMap (ModuleCat.of k k) n
  exact ⟨(asIso (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
    (TopCat.ofHom f))).symm ≪≫ classifyingSpaceSingularHomologyIsoGroupHomology k G n⟩

variable (k : Type) [CommRing k] [IsSemisimpleRing k] {m : ℤ}

/-- **`K(A, 1)` spaces of uniquely `m`-divisible groups are acyclic modulo `m`.** If
multiplication by the integer `m` is a bijection of the abelian group `A`, then every `K(A, 1)`
space has no homology in positive degrees with coefficients in a commutative semisimple ring `k`
in which `m = 0`. -/
theorem subsingleton_singularHomology_of_bijective_zsmul (hmk : (m : k) = 0) {A : Type*}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) {X : Type} [TopologicalSpace X]
    {x : X} (hX : IsEilenbergMacLaneSpaceOne (Multiplicative A) X x) (n : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (n + 1)) := by
  obtain ⟨e⟩ := hX.nonempty_fundamentalGroupMulEquiv
  let : CommGroup (FundamentalGroup X x) := e.toMonoidHom.commGroupOfInjective e.injective
  let eA : Additive (FundamentalGroup X x) ≃+ A := MulEquiv.toAdditiveLeft e
  have hB : Function.Bijective fun b : Additive (FundamentalGroup X x) ↦ m • b := by
    convert eA.symm.bijective.comp (hA.comp eA.bijective) using 1
    ext b
    simp [map_zsmul]
  have := subsingleton_groupHomology_of_bijective_zsmul k hmk hB n
  have hX' := hX.of_mulEquiv (e.symm.trans (AddEquiv.toMultiplicativeRight (.refl _)))
  exact (hX'.nonempty_singularHomologyIsoGroupHomology k
    (n + 1)).some.toLinearEquiv.toEquiv.subsingleton

/-- **Mod-two acyclicity of `K(A, 1)` spaces.** For a uniquely two-divisible abelian group `A`,
every `K(A, 1)` space has the mod-two homology of a point: `Hᵢ(X; 𝔽₂) = 0` for all `i > 0`. -/
theorem subsingleton_singularHomology_of_isUniquelyTwoDivisible {A : Type*} [AddCommGroup A]
    (hA : IsUniquelyTwoDivisible A) {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpaceOne (Multiplicative A) X x) (n : ℕ) :
    Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of X)).homology (n + 1)) :=
  subsingleton_singularHomology_of_bijective_zsmul (ZMod 2) (m := 2) (by decide)
    ((isUniquelyTwoDivisible_iff A).1 hA) hX n

end IsEilenbergMacLaneSpaceOne

namespace IsEilenbergMacLaneSpace

variable (k : Type) [CommRing k] [IsSemisimpleRing k] {m : ℤ}

private theorem isIso_singularHomologyMap_to_point_succ (hmk : (m : k) = 0) {A : Type*}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) :
    ∀ {d : ℕ} {X : Type} [TopologicalSpace X] {x : X},
      IsEilenbergMacLaneSpace (Multiplicative A) (d + 1) X x → ∀ q : ℕ,
        IsIso (((singularHomologyFunctor (ModuleCat.{0} k) q).obj (ModuleCat.of k k)).map
          (TopCat.isTerminalPUnit.from (TopCat.of X)))
  | 0, X, _, x, hX, q => by
    have : PathConnectedSpace (TopCat.of X) := hX.pathConnectedSpace
    have : Nonempty (TopCat.of X) := ⟨x⟩
    rw [isIso_singularHomologyFunctor_map_iff_isZero_reducedSingularHomologyFunctor]
    cases q with
    | zero => exact isZero_reducedSingularHomologyFunctor_zero (ModuleCat.of k k) (TopCat.of X)
    | succ q =>
      have :=
        (isEilenbergMacLaneSpace_one_iff.1 hX).subsingleton_singularHomology_of_bijective_zsmul
          k hmk hA q
      exact (ModuleCat.isZero_iff_subsingleton.2 this).of_iso
        ((reducedSingularHomologySuccIso (ModuleCat.of k k) q).app (TopCat.of X))
  | d + 1, X, _, x, hX, q => by
    -- Apply fibration comparison to the fixed-end path fibration `ΩX → PX → X`.
    have : PathConnectedSpace X := hX.pathConnectedSpace
    let E : TopCat.{0} := TopCat.of (MappingPathFiber (.id X) x)
    let p : E ⟶ TopCat.of X := TopCat.ofHom (MappingPathFiber.proj (.id X) x)
    have hp : TopCat.serreFibrations p :=
      (MappingPathFiber.isHurewiczFibration_proj.{0} (.id X) x).mem_serreFibrations
    have : IsIso (((singularHomologyFunctor (ModuleCat.{0} k) q).obj (ModuleCat.of k k)).map p) :=
      TopCat.isIso_singularHomologyMap_of_isIso_fiber_to_point hp k q fun b r _ ↦ by
        let α : Path ((ContinuousMap.id X) b) x := (PathConnectedSpace.joined b x).somePath
        let e := MappingPathFiber.projFiberHomotopyEquivLoopSpace (.id X) x b α
        exact isIso_singularHomologyMap_to_point_succ hmk hA
          (hX.loopSpace.of_homotopyEquiv e.symm (e.symm (Path.refl x))) r
    have hfac : p ≫ TopCat.isTerminalPUnit.from (TopCat.of X) = TopCat.isTerminalPUnit.from E :=
      TopCat.isTerminalPUnit.hom_ext _ _
    have hE : IsIso (((singularHomologyFunctor (ModuleCat.{0} k) q).obj (ModuleCat.of k k)).map
        (p ≫ TopCat.isTerminalPUnit.from (TopCat.of X))) := by
      rw [hfac]
      exact isIso_singularHomologyFunctor_map_of_contractibleSpace (ModuleCat.of k k) _ q
    rw [Functor.map_comp] at hE
    exact IsIso.of_isIso_comp_left
      (((singularHomologyFunctor (ModuleCat.{0} k) q).obj (ModuleCat.of k k)).map p) _

/-- **`K(A, n)` spaces of uniquely `m`-divisible groups have the `k`-homology of a point.** If
multiplication by `m` is bijective on the abelian group `A` and `(m : k) = 0` in the commutative
semisimple ring `k`, then for every `n ≥ 1` and every `K(A, n)` space `X`, the map from `X` to a
point induces an isomorphism on `H_q(-; k)` in every degree `q`. -/
theorem isIso_singularHomologyMap_to_point_of_bijective_zsmul (hmk : (m : k) = 0) {A : Type*}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) {n : ℕ} [NeZero n] {X : Type}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (q : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} k) q).obj (ModuleCat.of k k)).map
      (TopCat.isTerminalPUnit.from (TopCat.of X))) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact isIso_singularHomologyMap_to_point_succ k hmk hA hX q

/-- **The reduced `k`-homology of a `K(A, n)` space vanishes when multiplication by `m` is
bijective on `A` and `(m : k) = 0`.** -/
theorem isZero_reducedSingularHomologyFunctor_of_bijective_zsmul (hmk : (m : k) = 0) {A : Type*}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) {n : ℕ} [NeZero n] {X : Type}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (q : ℕ) :
    Limits.IsZero ((reducedSingularHomologyFunctor (ModuleCat.of k k) q).obj (TopCat.of X)) := by
  have : Nonempty (TopCat.of X) := ⟨x⟩
  exact (isIso_singularHomologyFunctor_map_iff_isZero_reducedSingularHomologyFunctor
    (ModuleCat.of k k) (TopCat.isTerminalPUnit.from (TopCat.of X)) q).1
      (hX.isIso_singularHomologyMap_to_point_of_bijective_zsmul k hmk hA q)

/-- **`K(A, n)` spaces of uniquely `m`-divisible groups are acyclic modulo `m`.** For every
`n ≥ 1`, if multiplication by `m` is bijective on `A` and `(m : k) = 0` in the commutative
semisimple ring `k`, then `H_{q+1}(X; k) = 0` for every `K(A, n)` space `X` and every `q`. -/
theorem subsingleton_singularHomology_of_bijective_zsmul (hmk : (m : k) = 0) {A : Type*}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) {n : ℕ} [NeZero n] {X : Type}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (q : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (q + 1)) :=
  ModuleCat.isZero_iff_subsingleton.1 <|
    (hX.isZero_reducedSingularHomologyFunctor_of_bijective_zsmul k hmk hA (q + 1)).of_iso
      ((reducedSingularHomologySuccIso (ModuleCat.of k k) q).app (TopCat.of X)).symm

/-- **Mod-two homology isomorphism to a point for `K(A, n)` spaces.** For a uniquely two-divisible
abelian group `A` and `n ≥ 1`, the map from any `K(A, n)` space to a point induces an isomorphism
on mod-two singular homology in every degree. -/
theorem isIso_singularHomologyMap_to_point_of_isUniquelyTwoDivisible {A : Type*} [AddCommGroup A]
    (hA : IsUniquelyTwoDivisible A) {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (q : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj
      (ModuleCat.of (ZMod 2) (ZMod 2))).map (TopCat.isTerminalPUnit.from (TopCat.of X))) :=
  hX.isIso_singularHomologyMap_to_point_of_bijective_zsmul (ZMod 2) (m := 2) (by decide)
    ((isUniquelyTwoDivisible_iff A).1 hA) q

/-- **Mod-two reduced acyclicity of `K(A, n)` spaces.** For a uniquely two-divisible abelian group
`A` and `n ≥ 1`, the reduced mod-two singular homology of any `K(A, n)` space vanishes in every
degree. -/
theorem isZero_reducedSingularHomologyFunctor_of_isUniquelyTwoDivisible {A : Type*}
    [AddCommGroup A] (hA : IsUniquelyTwoDivisible A) {n : ℕ} [NeZero n] {X : Type}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (q : ℕ) :
    Limits.IsZero ((reducedSingularHomologyFunctor (ModuleCat.of (ZMod 2) (ZMod 2)) q).obj
      (TopCat.of X)) :=
  hX.isZero_reducedSingularHomologyFunctor_of_bijective_zsmul (ZMod 2) (m := 2) (by decide)
    ((isUniquelyTwoDivisible_iff A).1 hA) q

/-- **Mod-two acyclicity of `K(A, n)` spaces.** For a uniquely two-divisible abelian group `A` and
`n ≥ 1`, every `K(A, n)` space has the mod-two homology of a point: `Hᵢ(X; 𝔽₂) = 0` for all
`i > 0`. -/
theorem subsingleton_singularHomology_of_isUniquelyTwoDivisible {A : Type*} [AddCommGroup A]
    (hA : IsUniquelyTwoDivisible A) {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (q : ℕ) :
    Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of X)).homology (q + 1)) :=
  hX.subsingleton_singularHomology_of_bijective_zsmul (ZMod 2) (m := 2) (by decide)
    ((isUniquelyTwoDivisible_iff A).1 hA) q

end IsEilenbergMacLaneSpace

end TauCeti
