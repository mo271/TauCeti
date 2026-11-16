/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.Homology
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.PullbackCup

/-!
# The Thom isomorphism over trivializable bundles and finite trivializing unions

Let `E → B` be a real vector bundle with finite-dimensional model fibre `F` of rank
`r = finrank ℝ F`, Thom pair `(E, E₀)` (`TauCeti.thomPair`), and projection `π : E ⟶ B`
(`TauCeti.thomPairProj`). For a commutative ring `K`, a `K`-module `M` and a relative class
`u ∈ Hʳ(E, E₀; K)`, the Thom map (`TauCeti.thomMap`) sends `a ∈ Hᵖ(B; M)` to
`π^* a ⌣ u ∈ Hᵖ⁺ʳ(E, E₀; M)`. Over a subset `W` of `B`, restricting `π` (`TauCeti.thomPairOverProj`)
and `u` gives the restricted Thom map `TauCeti.thomMapOver` from `Hᵖ(W; M)` to
`Hᵖ⁺ʳ(E|_W, E₀|_W; M)`.

This file establishes the **Thom isomorphism** (`Φ_u : Hᵖ(B; M) ≃ₗ[K] Hᵖ⁺ʳ(E, E₀; M)`) over
trivializing subsets, globally trivializable bundles, finite unions of trivializing open sets,
and compact bases:

* Over a subset `W` of the base set of a linear trivialization `e`, `e` identifies the restricted
  Thom pair `(E|_W, E₀|_W)` with the product Thom pair `(W × F, W × (F ∖ {0}))`, transporting
  `TauCeti.bijective_pullbackCup_prodThomPair` to any local class generating every fibre over `W`
  (`Bundle.Trivialization.bijective_pullbackCup_thomPairOver`,
  `Bundle.Trivialization.thomPairOverPullbackCupEquiv`) and to `TauCeti.thomMapOver` of a global
  class (`Bundle.Trivialization.bijective_thomMapOver`).
* When `e.baseSet = Set.univ`, in particular for the trivial bundle `Bundle.Trivial B F`, the Thom
  map of any Thom class (`TauCeti.IsThomClass`) is bijective over an arbitrary base `B`
  (`Bundle.Trivialization.thomEquiv`, `TauCeti.IsThomClass.trivialThomEquiv`).
* Over a finite union `⋃ i ∈ s, W i` of open subsets lying in the base sets of linear
  trivializations, `TauCeti.thomMapOver` is bijective whenever `u` restricts to a generator on
  every fibre over the union (`TauCeti.bijective_thomMapOver_biUnion`,
  `TauCeti.thomOverBiUnionEquiv`).
* Consequently, for any Thom class `u` (`TauCeti.IsThomClass`), the Thom map is an isomorphism
  whenever `B` is covered by finitely many trivializing open sets
  (`TauCeti.IsThomClass.thomEquivOfBiUnionEqUniv`), and in particular over every compact base
  (`TauCeti.IsThomClass.thomEquivOfCompactSpace`). Because `TauCeti.IsThomClass` requires no
  orientation hypothesis of its own, this covers both unoriented vector bundles over rings with
  `Subsingleton Kˣ` (such as `ZMod 2`, via `TauCeti.existsUnique_isThomClass_of_subsingleton_units`)
  and oriented vector bundles over arbitrary commutative rings (`TauCeti.VectorBundleOrientation`,
  `TauCeti.VectorBundleOrientation.thomEquivOfCompactSpace`).
* Over a field `K`, Kronecker duality (`TauCeti.bijective_homologyThomMap_iff`) yields the
  corresponding bijectivity of the homology Thom map `x ↦ π_*(x ⌢ u)` (`TauCeti.homologyThomMap`).

## Main definitions and results

* `TauCeti.thomPairOverProj`, `TauCeti.thomMapOver`: the bundle projection and Thom map restricted
  over a subset `W` of the base.
* `Bundle.Trivialization.bijective_pullbackCup_thomPairOver`,
  `Bundle.Trivialization.thomPairOverPullbackCupEquiv`,
  `Bundle.Trivialization.bijective_thomMapOver`: the local Thom isomorphism over a subset of a
  linear trivialization's base set.
* `Bundle.Trivialization.bijective_thomMap`, `Bundle.Trivialization.thomEquiv`,
  `Bundle.Trivialization.bijective_homologyThomMap`: the Thom isomorphism for a globally
  trivializable bundle over an arbitrary base.
* `TauCeti.bijective_thomMapOver_biUnion`, `TauCeti.thomOverBiUnionEquiv`: the Thom isomorphism
  over a finite union of trivializing open sets.
* `TauCeti.IsThomClass.bijective_thomMap_trivial`, `TauCeti.IsThomClass.trivialThomEquiv`,
  `TauCeti.IsThomClass.bijective_thomMap_of_biUnion_eq_univ`,
  `TauCeti.IsThomClass.thomEquivOfBiUnionEqUniv`,
  `TauCeti.IsThomClass.bijective_thomMap_of_compactSpace`,
  `TauCeti.IsThomClass.thomEquivOfCompactSpace`: the cohomology Thom isomorphism for a Thom class.
* `TauCeti.IsThomClass.bijective_homologyThomMap_trivial`,
  `TauCeti.IsThomClass.bijective_homologyThomMap_of_biUnion_eq_univ`,
  `TauCeti.IsThomClass.bijective_homologyThomMap_of_compactSpace`: the homology Thom isomorphism
  over a field.
* `TauCeti.VectorBundleOrientation.bijective_thomMap_thomClassOfModel_of_biUnion_eq_univ`,
  `TauCeti.VectorBundleOrientation.bijective_thomMap_thomClassOfModel_of_compactSpace`,
  `TauCeti.VectorBundleOrientation.thomEquivOfCompactSpace`,
  `TauCeti.VectorBundleOrientation.bijective_homologyThomMap_thomClassOfModel_of_compactSpace`:
  the Thom isomorphism for the Thom class of an oriented real vector bundle.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 4.D, Theorem 4D.10.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module Set

universe w

namespace TauCeti

section Projection

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- The bundle projection `E|_W ⟶ W` over a subset `W` of the base, as a morphism out of the
ambient space of `TauCeti.thomPairOver`. -/
def thomPairOverProj (W : Set B) : (thomPairOver F E W).fst ⟶ TopCat.of W :=
  TopCat.ofHom ((⟨π F E, FiberBundle.continuous_proj F E⟩ :
    C(TotalSpace F E, B)).restrictPreimage W)

/-- `TauCeti.thomPairOverProj` is `ContinuousMap.restrictPreimage` of the bundle projection. -/
theorem thomPairOverProj_def (W : Set B) :
    thomPairOverProj F E W =
      TopCat.ofHom ((⟨π F E, FiberBundle.continuous_proj F E⟩ :
        C(TotalSpace F E, B)).restrictPreimage W) :=
  (rfl)

@[simp]
theorem thomPairOverProj_apply (W : Set B) (v : π F E ⁻¹' W) :
    thomPairOverProj F E W v = ⟨v.1.proj, v.2⟩ :=
  (rfl)

/-- **The Thom map over a subset `W` of the base**: for a relative class `u ∈ Hⁿ(E, E₀; K)`, the
map `Hᵖ(W; M) ⟶ Hᵐ(E|_W, E₀|_W; M)`, `p + n = m`, sending `a` to `π|_W^* a ⌣ u|_W`. -/
def thomMapOver {K : Type w} [CommRing K] (M : ModuleCat.{w} K) (W : Set B) (n p m : ℕ)
    (h : p + n = m) :
    (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p →ₗ[K]
        (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K M m :=
  TopCat.pullbackCupRestrict
    (TopCat.ofHom (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
      ⟨π F E, FiberBundle.continuous_proj F E⟩)
    (zeroSectionCompl F E) M W n p m h

/-- `TauCeti.thomMapOver` is `TopCat.pullbackCupRestrict` of the bundle projection and the
complement of the zero section. -/
theorem thomMapOver_def {K : Type w} [CommRing K] (M : ModuleCat.{w} K) (W : Set B)
    (n p m : ℕ) (h : p + n = m) :
    thomMapOver F E M W n p m h =
      TopCat.pullbackCupRestrict
        (TopCat.ofHom (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
          ⟨π F E, FiberBundle.continuous_proj F E⟩)
        (zeroSectionCompl F E) M W n p m h :=
  (rfl)

/-- `TauCeti.thomMapOver` evaluates as `TopPair.pullbackCup` along `TauCeti.thomPairOverProj` of
the restriction of `u` to `TauCeti.thomPairOver F E W`. -/
theorem thomMapOver_apply {K : Type w} [CommRing K] {M : ModuleCat.{w} K} (W : Set B)
    {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    thomMapOver F E M W n p m h u =
      (thomPairOver F E W).pullbackCup M (thomPairOverProj F E W) n p m h
        (TopPair.singularCohomologyMap
          (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
            (zeroSectionCompl F E) W) n u) := by
  rw [thomMapOver_def, TopCat.pullbackCupRestrict_apply, thomPairOverProj_def]
  rfl

/-- Over `Set.univ`, `TauCeti.thomMapOver` is bijective if and only if `TauCeti.thomMap` is. -/
theorem bijective_thomMapOver_univ_iff {K : Type w} [CommRing K] {M : ModuleCat.{w} K}
    {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (thomMapOver F E M Set.univ n p m h u) ↔
      Function.Bijective (thomMap F E M n p m h u) := by
  rw [thomMapOver_def, TopCat.bijective_pullbackCupRestrict_univ_iff, thomMap_def,
    thomPairProj_def]

end Projection

end TauCeti

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ] {K : Type w} [CommRing K]

section Subset

variable [FiniteDimensional ℝ F]

/-- **The local Thom isomorphism over a subset of a linear trivialization.** If `W ⊆ e.baseSet` and
`u ∈ Hʳ(E|_W, E₀|_W; K)` restricts on the fibre over every `b ∈ W` to a generator of
`Hʳ(E_b, E_b ∖ {0}; K)`, `r = finrank ℝ F`, then `a ↦ π|_W^* a ⌣ u` is bijective from `Hᵖ(W; M)`
to `Hᵐ(E|_W, E₀|_W; M)` whenever `p + r = m`. -/
theorem bijective_pullbackCup_thomPairOver {W : Set B} (hW : W ⊆ e.baseSet) (M : ModuleCat.{w} K)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ b (hb : b ∈ W), Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) (finrank ℝ F) u} = ⊤) :
    Function.Bijective
      ((thomPairOver F E W).pullbackCup M (thomPairOverProj F E W) (finrank ℝ F) p m h u) := by
  let φ := e.thomPairOverIso ℝ hW
  have hhom : TopPair.Hom.fst φ.hom ≫ prodThomPairProj W F = thomPairOverProj F E W :=
    TopCat.ext fun (v : π F E ⁻¹' W) ↦
      (congrArg (prodThomPairProj W F) (e.thomPairOverIso_hom_fst_apply ℝ hW v)).trans
        ((prodThomPairProj_apply F _).trans (thomPairOverProj_apply F E W v).symm)
  have hg : TopPair.Hom.fst φ.inv ≫ thomPairOverProj F E W =
      prodThomPairProj W F ≫ 𝟙 (TopCat.of W) := by
    rw [Category.comp_id, ← hhom, ← Category.assoc, ← TopPair.Hom.fst_comp, φ.inv_hom_id,
      TopPair.Hom.fst_id, Category.id_comp]
  refine (TopPair.bijective_pullbackCup_iff_of_isIso φ.inv (𝟙 (TopCat.of W)) hg h u).1
    (bijective_pullbackCup_prodThomPair M W F h fun b ↦ ?_)
  have hφ : prodThomPairFiberMap F b ≫ φ.inv =
      (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso.inv ≫
        fiberThomPairOverMap F E b.2 := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
      e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hW b.2]
  rw [← TopPair.singularCohomologyMap_comp_apply, hφ, TopPair.singularCohomologyMap_comp_apply]
  exact ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K (ModuleCat.of K K)
    (finrank ℝ F)).mapIso
      (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso.symm.op
        ).toLinearEquiv.span_singleton_apply_eq_top_iff.2 (hu b.1 b.2)

/-- **The local Thom isomorphism `Hᵖ(W; M) ≃ₗ[K] Hᵐ(E|_W, E₀|_W; M)`** over a subset `W` of the
base set of a linear trivialization `e`, for any local class `u ∈ Hʳ(E|_W, E₀|_W; K)` restricting
to a generator on every fibre over `W`. -/
def thomPairOverPullbackCupEquiv {W : Set B} (hW : W ⊆ e.baseSet) (M : ModuleCat.{w} K)
    (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b (hb : b ∈ W), Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) (finrank ℝ F) u} = ⊤) :
    (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective
    ((thomPairOver F E W).pullbackCup M (thomPairOverProj F E W) (finrank ℝ F) p m h u)
    (e.bijective_pullbackCup_thomPairOver hW M h hu)

/-- The underlying linear map of `Bundle.Trivialization.thomPairOverPullbackCupEquiv` is
`TopPair.pullbackCup` along `TauCeti.thomPairOverProj`. -/
@[simp]
theorem toLinearMap_thomPairOverPullbackCupEquiv {W : Set B} (hW : W ⊆ e.baseSet)
    (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b (hb : b ∈ W), Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) (finrank ℝ F) u} = ⊤) :
    (e.thomPairOverPullbackCupEquiv hW M p m h u hu).toLinearMap =
      (thomPairOver F E W).pullbackCup M (thomPairOverProj F E W) (finrank ℝ F) p m h u :=
  (rfl)

/-- `Bundle.Trivialization.thomPairOverPullbackCupEquiv` evaluates by `TopPair.pullbackCup` along
`TauCeti.thomPairOverProj`. -/
@[simp]
theorem thomPairOverPullbackCupEquiv_apply {W : Set B} (hW : W ⊆ e.baseSet) (M : ModuleCat.{w} K)
    (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b (hb : b ∈ W), Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) (finrank ℝ F) u} = ⊤)
    (a : (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p) :
    e.thomPairOverPullbackCupEquiv hW M p m h u hu a =
      (thomPairOver F E W).pullbackCup M (thomPairOverProj F E W) (finrank ℝ F) p m h u a :=
  (rfl)

/-- Over a subset `W` of the base set of a linear trivialization `e`, `TauCeti.thomMapOver` of a
class `u ∈ Hʳ(E, E₀; K)` is bijective whenever `u` restricts to a generator of
`Hʳ(E_b, E_b ∖ {0}; K)` over every point `b ∈ W`. -/
theorem bijective_thomMapOver {W : Set B} (hW : W ⊆ e.baseSet)
    (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ W, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    Function.Bijective (thomMapOver F E M W (finrank ℝ F) p m h u) := by
  rw [thomMapOver_apply]
  refine e.bijective_pullbackCup_thomPairOver hW M h fun b hb ↦ ?_
  rw [← TopPair.singularCohomologyMap_comp_apply,
    fiberThomPairOverMap_comp_restrictPreimagePairMap]
  exact hu b hb

end Subset

section Global

/-- **The Thom isomorphism for a globally trivializable bundle.** For a linear trivialization `e`
over the whole base `B` and a Thom class `u` of `E`, the Thom map `Hᵖ(B; M) ⟶ Hᵐ(E, E₀; M)`,
`p + finrank ℝ F = m`, is bijective. The base `B` is an arbitrary topological space. -/
theorem bijective_thomMap (he : e.baseSet = Set.univ) (M : ModuleCat.{w} K) {p m : ℕ}
    (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨_, hu'⟩ := isThomClass_iff.1 hu
  exact (bijective_thomMapOver_univ_iff F E h u).1
    (e.bijective_thomMapOver he.ge M h fun b _ ↦ hu' b)

/-- **The Thom isomorphism `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` for a globally trivializable bundle**,
over an arbitrary base `B`, given by a linear trivialization `e` with `e.baseSet = Set.univ` and a
Thom class `u`. -/
def thomEquiv (he : e.baseSet = Set.univ) (M : ModuleCat.{w} K) (p m : ℕ)
    (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u) (e.bijective_thomMap he M h hu)

/-- The underlying linear map of `Bundle.Trivialization.thomEquiv` is `TauCeti.thomMap`. -/
@[simp]
theorem toLinearMap_thomEquiv (he : e.baseSet = Set.univ) (M : ModuleCat.{w} K) (p m : ℕ)
    (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u) :
    (e.thomEquiv he M p m h u hu).toLinearMap = thomMap F E M (finrank ℝ F) p m h u :=
  (rfl)

/-- `Bundle.Trivialization.thomEquiv` evaluates via `TauCeti.thomMap`. -/
@[simp]
theorem thomEquiv_apply (he : e.baseSet = Set.univ) (M : ModuleCat.{w} K) (p m : ℕ)
    (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    e.thomEquiv he M p m h u hu a = thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

/-- **The homology Thom isomorphism for a globally trivializable bundle over a field.** If `e` is a
linear trivialization with `e.baseSet = Set.univ` and `u` is a Thom class with coefficients in a
field `K`, then the homology Thom map `Hₘ(E, E₀; K) ⟶ Hₚ(B; K)`, `finrank ℝ F + p = m`, is
bijective. -/
theorem bijective_homologyThomMap {K : Type w} [Field K] (he : e.baseSet = Set.univ) {p m : ℕ}
    (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (bijective_homologyThomMap_iff F E h u).2 (e.bijective_thomMap he (ModuleCat.of K K) (by lia) hu)

end Global

end Bundle.Trivialization

namespace TauCeti

section FiniteUnion

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **The Thom isomorphism over a finite union of trivializing open sets.** Let `W i`, `i ∈ s`, be
finitely many open subsets of `B`, each contained in the base set of a linear trivialization of `E`,
and let `u ∈ Hʳ(E, E₀; K)`, `r = finrank ℝ F`, restrict to a generator of `Hʳ(E_b, E_b ∖ {0}; K)`
over every point `b ∈ ⋃ i ∈ s, W i`. Then `TauCeti.thomMapOver` of `u` over `⋃ i ∈ s, W i` is
bijective from `Hᵖ(⋃ i ∈ s, W i; M)` to `Hᵐ(E|_{⋃ i ∈ s, W i}, E₀|_{⋃ i ∈ s, W i}; M)` for
`p + r = m`. -/
theorem bijective_thomMapOver_biUnion {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMapOver F E M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  classical
  induction s using Finset.induction_on generalizing W p m with
  | empty =>
    have hdom : Subsingleton ((TopCat.of ↥(⋃ i ∈ (∅ : Finset ι), W i)).singularCohomology
        (ModuleCat.of K K) K M p) := by
      have : IsEmpty ↥(⋃ i ∈ (∅ : Finset ι), W i) := by simp
      exact ModuleCat.subsingleton_of_isZero
        (isZero_singularCohomology_of_isEmpty (ModuleCat.of K K) K M _ p)
    have hcod : Subsingleton ((thomPairOver F E (⋃ i ∈ (∅ : Finset ι), W i)).singularCohomology
        (ModuleCat.of K K) K M m) := by
      refine ModuleCat.subsingleton_of_isZero
        (TopPair.isZero_singularCohomology_of_isZero_singularHomology _ _ _ _ fun j _ ↦ ?_)
      simpa using isZero_singularHomology_thomPairOver_empty (F := F) (E := E) (ModuleCat.of K K) j
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  | insert a s _ ih =>
    rw [thomMapOver_def, Finset.set_biUnion_insert]
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert a s := Finset.mem_insert_of_mem hi
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    refine TopCat.bijective_pullbackCupRestrict_union
      (TopCat.ofHom (X := TopCat.of (TotalSpace F E)) (Y := TopCat.of B)
        ⟨π F E, FiberBundle.continuous_proj F E⟩)
      (zeroSectionCompl F E) M
      (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (hs i hi)) u
      (fun q _ ↦ e.bijective_thomMapOver he M rfl fun b hb ↦
        hu b (mem_iUnion₂.2 ⟨a, Finset.mem_insert_self a s, hb⟩))
      (fun q _ ↦ ih (fun i hi ↦ hWo i (hs i hi)) (fun i hi ↦ hWe i (hs i hi))
        (fun b hb ↦ by
          obtain ⟨i, hi, hbi⟩ := mem_iUnion₂.1 hb
          exact hu b (mem_iUnion₂.2 ⟨i, hs i hi, hbi⟩)) rfl)
      (fun q _ ↦ ?_) (fun j hj ↦ ?_) h
    · rw [← thomMapOver_def, inter_iUnion₂]
      refine ih (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter (hWo i (hs i hi)))
        (fun i hi ↦ ?_) (fun b hb ↦ ?_) rfl
      · obtain ⟨e', he', hi'⟩ := hWe i (hs i hi)
        exact ⟨e', he', inter_subset_right.trans hi'⟩
      · obtain ⟨i, hi, _, hbi⟩ := mem_iUnion₂.1 hb
        exact hu b (mem_iUnion₂.2 ⟨i, hs i hi, hbi⟩)
    · rw [inter_iUnion₂]
      refine isZero_singularCohomology_thomPairOver_biUnion (ModuleCat.of K K) M s
        (fun i hi ↦ (hWo a (Finset.mem_insert_self a s)).inter (hWo i (hs i hi)))
        (fun i hi ↦ ?_) (by lia)
      obtain ⟨e', he', hi'⟩ := hWe i (hs i hi)
      exact ⟨e', he', inter_subset_right.trans hi'⟩

/-- **The Thom isomorphism over a finite union of trivializing open sets**, as a `K`-linear
equivalence `Hᵖ(W; M) ≃ₗ[K] Hᵐ(E|_W, E₀|_W; M)` for `W = ⋃ i ∈ s, W i` and `p + finrank ℝ F = m`. -/
def thomOverBiUnionEquiv {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    (TopCat.of ↥(⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPairOver F E (⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective
    (thomMapOver F E M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u)
    (bijective_thomMapOver_biUnion M s hWo hWe hu h)

/-- The underlying linear map of `TauCeti.thomOverBiUnionEquiv` is `TauCeti.thomMapOver` over
`⋃ i ∈ s, W i`. -/
@[simp]
theorem toLinearMap_thomOverBiUnionEquiv {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    (thomOverBiUnionEquiv M s hWo hWe p m h u hu).toLinearMap =
      thomMapOver F E M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u :=
  (rfl)

/-- `TauCeti.thomOverBiUnionEquiv` evaluates via `TauCeti.thomMapOver` over `⋃ i ∈ s, W i`. -/
@[simp]
theorem thomOverBiUnionEquiv_apply {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤)
    (a : (TopCat.of ↥(⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M p) :
    thomOverBiUnionEquiv M s hWo hWe p m h u hu a =
      thomMapOver F E M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u a :=
  (rfl)

end FiniteUnion

namespace IsThomClass

section Trivial

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The Thom isomorphism for the trivial vector bundle `Bundle.Trivial B F`** over an arbitrary
base `B`: for any Thom class `u`, the Thom map `Hᵖ(B; M) ⟶ Hᵐ(B × F, B × (F ∖ {0}); M)`,
`p + finrank ℝ F = m`, is bijective. -/
theorem bijective_thomMap_trivial {K : Type w} [CommRing K]
    {u : (thomPair F (Bundle.Trivial B F)).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F (Bundle.Trivial B F) u) (M : ModuleCat.{w} K) {p m : ℕ}
    (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F (Bundle.Trivial B F) M (finrank ℝ F) p m h u) :=
  (Bundle.Trivial.trivialization B F).bijective_thomMap (Bundle.Trivial.trivialization_baseSet B F)
    M h hu

/-- **The Thom isomorphism `Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)`** for the trivial vector
bundle `Bundle.Trivial B F` and a Thom class `u`. -/
def trivialThomEquiv {K : Type w} [CommRing K]
    {u : (thomPair F (Bundle.Trivial B F)).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F (Bundle.Trivial B F) u) (M : ModuleCat.{w} K) (p m : ℕ)
    (h : p + finrank ℝ F = m := by lia) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F (Bundle.Trivial B F)).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F (Bundle.Trivial B F) M (finrank ℝ F) p m h u)
    (hu.bijective_thomMap_trivial M h)

/-- The underlying linear map of `TauCeti.IsThomClass.trivialThomEquiv` is `TauCeti.thomMap`. -/
@[simp]
theorem toLinearMap_trivialThomEquiv {K : Type w} [CommRing K]
    {u : (thomPair F (Bundle.Trivial B F)).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F (Bundle.Trivial B F) u) (M : ModuleCat.{w} K) (p m : ℕ)
    (h : p + finrank ℝ F = m) :
    (hu.trivialThomEquiv M p m h).toLinearMap =
      thomMap F (Bundle.Trivial B F) M (finrank ℝ F) p m h u :=
  (rfl)

/-- `TauCeti.IsThomClass.trivialThomEquiv` evaluates via `TauCeti.thomMap`. -/
@[simp]
theorem trivialThomEquiv_apply {K : Type w} [CommRing K]
    {u : (thomPair F (Bundle.Trivial B F)).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F (Bundle.Trivial B F) u) (M : ModuleCat.{w} K) (p m : ℕ)
    (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    hu.trivialThomEquiv M p m h a = thomMap F (Bundle.Trivial B F) M (finrank ℝ F) p m h u a :=
  (rfl)

/-- **The homology Thom isomorphism for the trivial bundle over a field.** -/
theorem bijective_homologyThomMap_trivial {K : Type w} [Field K]
    {u : (thomPair F (Bundle.Trivial B F)).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F (Bundle.Trivial B F) u) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective
      (homologyThomMap F (Bundle.Trivial B F) (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (Bundle.Trivial.trivialization B F).bijective_homologyThomMap
    (Bundle.Trivial.trivialization_baseSet B F) h hu

end Trivial

section FiniteCover

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- **The Thom isomorphism for a bundle covered by finitely many trivializing open sets.** If `u`
is a Thom class of `E` and `B = ⋃ i ∈ s, W i` for finitely many open sets `W i`, each contained in
the base set of a linear trivialization, then the Thom map `Hᵖ(B; M) ⟶ Hᵐ(E, E₀; M)`,
`p + finrank ℝ F = m`, is bijective. -/
theorem bijective_thomMap_of_biUnion_eq_univ {K : Type w} [CommRing K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hW : ⋃ i ∈ s, W i = Set.univ) (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨_, hu'⟩ := isThomClass_iff.1 hu
  have hbij := bijective_thomMapOver_biUnion M s hWo hWe (fun b _ ↦ hu' b) h
  rwa [hW, bijective_thomMapOver_univ_iff] at hbij

/-- **The Thom isomorphism `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`** for a Thom class `u` when finitely many
trivializing open sets cover `B`. -/
def thomEquivOfBiUnionEqUniv {K : Type w} [CommRing K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hW : ⋃ i ∈ s, W i = Set.univ) (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (p m : ℕ) (h : p + finrank ℝ F = m := by lia) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u)
    (hu.bijective_thomMap_of_biUnion_eq_univ M s hW hWo hWe h)

/-- The underlying linear map of `TauCeti.IsThomClass.thomEquivOfBiUnionEqUniv` is
`TauCeti.thomMap`. -/
@[simp]
theorem toLinearMap_thomEquivOfBiUnionEqUniv {K : Type w} [CommRing K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hW : ⋃ i ∈ s, W i = Set.univ) (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (p m : ℕ) (h : p + finrank ℝ F = m) :
    (hu.thomEquivOfBiUnionEqUniv M s hW hWo hWe p m h).toLinearMap =
      thomMap F E M (finrank ℝ F) p m h u :=
  (rfl)

/-- `TauCeti.IsThomClass.thomEquivOfBiUnionEqUniv` evaluates via `TauCeti.thomMap`. -/
@[simp]
theorem thomEquivOfBiUnionEqUniv_apply {K : Type w} [CommRing K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hW : ⋃ i ∈ s, W i = Set.univ) (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (p m : ℕ) (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    hu.thomEquivOfBiUnionEqUniv M s hW hWo hWe p m h a = thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

/-- **The homology Thom isomorphism over a field for a finite trivializing open cover.** -/
theorem bijective_homologyThomMap_of_biUnion_eq_univ {K : Type w} [Field K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hW : ⋃ i ∈ s, W i = Set.univ) (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (bijective_homologyThomMap_iff F E h u).2
    (hu.bijective_thomMap_of_biUnion_eq_univ (ModuleCat.of K K) s hW hWo hWe (by lia))

/-- **The Thom isomorphism over a compact base.** Let `E → B` be a real vector bundle over a
compact space `B` and `u` a Thom class of `E` with coefficients in a commutative ring `K`. For any
`K`-module `M`, the Thom map `Hᵖ(B; M) ⟶ Hᵐ(E, E₀; M)`, `p + finrank ℝ F = m`, `a ↦ π^* a ⌣ u`,
is bijective. -/
theorem bijective_thomMap_of_compactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {K : Type w} [CommRing K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet)
    (fun b ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
  exact hu.bijective_thomMap_of_biUnion_eq_univ M s (univ_subset_iff.1 hs)
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) h

/-- **The Thom isomorphism `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`** for a real vector bundle `E → B` over a
compact base `B` and any Thom class `u`, sending `a` to `π^* a ⌣ u`. -/
def thomEquivOfCompactSpace [CompactSpace B] [VectorBundle ℝ F E] {K : Type w} [CommRing K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m := by lia) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u)
    (hu.bijective_thomMap_of_compactSpace M h)

/-- The underlying linear map of `TauCeti.IsThomClass.thomEquivOfCompactSpace` is
`TauCeti.thomMap`. -/
@[simp]
theorem toLinearMap_thomEquivOfCompactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {K : Type w} [CommRing K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m) :
    (hu.thomEquivOfCompactSpace M p m h).toLinearMap = thomMap F E M (finrank ℝ F) p m h u :=
  (rfl)

/-- `TauCeti.IsThomClass.thomEquivOfCompactSpace` evaluates via `TauCeti.thomMap`. -/
@[simp]
theorem thomEquivOfCompactSpace_apply [CompactSpace B] [VectorBundle ℝ F E]
    {K : Type w} [CommRing K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    hu.thomEquivOfCompactSpace M p m h a = thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

/-- **The homology Thom isomorphism over a compact base and a field.** For a real vector bundle
`E → B` over a compact space `B` and a Thom class `u` with coefficients in a field `K`, the
homology Thom map `Hₘ(E, E₀; K) ⟶ Hₚ(B; K)`, `finrank ℝ F + p = m`, `x ↦ π_*(x ⌢ u)`, is
bijective. -/
theorem bijective_homologyThomMap_of_compactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {K : Type w} [Field K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (bijective_homologyThomMap_iff F E h u).2
    (hu.bijective_thomMap_of_compactSpace (ModuleCat.of K K) (by lia))

end FiniteCover

end IsThomClass

namespace VectorBundleOrientation

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] {ι : Type*} [Fintype ι]

/-- **The Thom isomorphism for an oriented real vector bundle** covered by finitely many
trivializing open sets, with respect to the Thom class `o.thomClassOfModel hι ω g` normalized by an
orientation `ω` of `F` and a generator `g` of `Hʳ(F, F ∖ {0}; K)`. -/
theorem bijective_thomMap_thomClassOfModel_of_biUnion_eq_univ (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι) {K : Type w} [CommRing K]
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (M : ModuleCat.{w} K) {κ : Type*} (s : Finset κ)
    {W : κ → Set B} (hW : ⋃ i ∈ s, W i = Set.univ) (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g)) :=
  (o.isThomClass_thomClassOfModel hι ω hg).bijective_thomMap_of_biUnion_eq_univ M s hW hWo hWe h

/-- **The Thom isomorphism for an oriented real vector bundle over a compact base**, with respect
to the Thom class `o.thomClassOfModel hι ω g` normalized by `(ω, g)` and coefficients in any
commutative ring `K` and `K`-module `M`. -/
theorem bijective_thomMap_thomClassOfModel_of_compactSpace [CompactSpace B]
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)
    {K : Type w} [CommRing K]
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g)) :=
  (o.isThomClass_thomClassOfModel hι ω hg).bijective_thomMap_of_compactSpace M h

/-- **The Thom isomorphism `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)`** of an oriented real vector bundle over a
compact base, associated to `o.thomClassOfModel hι ω g`. -/
def thomEquivOfCompactSpace [CompactSpace B] (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι) {K : Type w} [CommRing K]
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hg : Submodule.span K {g} = ⊤) (M : ModuleCat.{w} K) (p m : ℕ)
    (h : p + finrank ℝ F = m := by lia) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  (o.isThomClass_thomClassOfModel hι ω hg).thomEquivOfCompactSpace M p m h

/-- The underlying linear map of `TauCeti.VectorBundleOrientation.thomEquivOfCompactSpace` is
`TauCeti.thomMap` of `o.thomClassOfModel hι ω g`. -/
@[simp]
theorem toLinearMap_thomEquivOfCompactSpace [CompactSpace B] (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι) {K : Type w} [CommRing K]
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hg : Submodule.span K {g} = ⊤) (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m) :
    (o.thomEquivOfCompactSpace hι ω g hg M p m h).toLinearMap =
      thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g) :=
  (rfl)

/-- `TauCeti.VectorBundleOrientation.thomEquivOfCompactSpace` evaluates via `TauCeti.thomMap` of
`o.thomClassOfModel hι ω g`. -/
@[simp]
theorem thomEquivOfCompactSpace_apply [CompactSpace B] (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι) {K : Type w} [CommRing K]
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F))
    (hg : Submodule.span K {g} = ⊤) (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    o.thomEquivOfCompactSpace hι ω g hg M p m h a =
      thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g) a :=
  (rfl)

/-- **The homology Thom isomorphism for an oriented real vector bundle** over a compact base and a
field `K`, with respect to `o.thomClassOfModel hι ω g`. -/
theorem bijective_homologyThomMap_thomClassOfModel_of_compactSpace [CompactSpace B]
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)
    {K : Type w} [Field K]
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective
      (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h
        (o.thomClassOfModel hι ω g)).hom :=
  (o.isThomClass_thomClassOfModel hι ω hg).bijective_homologyThomMap_of_compactSpace h

end VectorBundleOrientation

end TauCeti

end
