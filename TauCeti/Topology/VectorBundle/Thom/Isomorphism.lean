/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import TauCeti.Algebra.Homology.Monoidal.Cap.ChainMap
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.Topology.VectorBundle.EulerClass
import TauCeti.Algebra.Homology.DerivedCategory.KProjective
import TauCeti.Algebra.Ring.NegOnePow
import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative
import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Isomorphism
import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
import TauCeti.Topology.VectorBundle.Thom.Class

/-!
# The Thom isomorphism in singular cohomology

Let `E → B` be a vector bundle with Thom pair `(E, E₀)`, `E₀` the complement of the zero section,
and let `u ∈ Hⁿ(E, E₀; K)` be a relative class with coefficients in a commutative ring `K`. The
**Thom map** of `u` is

`Φ_u : Hᵖ(B; M) ⟶ Hᵖ⁺ⁿ(E, E₀; M)`,  `a ↦ π^*a ⌣ u`,

the pull-back along the projection `π : E ⟶ B` followed by the cup product of absolute and
relative cohomology (`TopPair.singularCup`), for any `K`-module of coefficients `M`: the map
`TopPair.pullbackCup` of the Thom pair and its projection. When `u` is a Thom class of a
finite-dimensional real vector bundle of rank `r`, this file proves the **Thom isomorphism**
(Milnor and Stasheff, Theorem 10.4; Hatcher, Theorem 4D.10): `Φ_u` is bijective in every degree,
for every commutative ring `K`, every `K`-module `M`, and every base space `B` — without
compactness, separation, or paracompactness assumptions on `B`, and in all ranks `r ≥ 0`.

The first section sets up the Thom map and its basic properties: `K`-bilinearity in `u` and `a`
(`TauCeti.thomMap`), `Φ_u(1) = u` (`TauCeti.thomMap_one`), naturality in maps of Thom pairs and
pull-back bundles (`TauCeti.thomMap_naturality`, `TauCeti.thomMap_pullback`), linearity over the
cohomology ring `H^*(B; K)` of the base (`TauCeti.thomMap_singularCup`), and restriction to a
fibre pair (`TauCeti.singularCohomologyMap_fiberThomPairMap_thomMap`).

Over a subset `W` of the base set of a linear trivialization `e`, `e` identifies `(E|_W, E₀|_W)`
with the Thom pair of the product bundle `W × F` (`Bundle.Trivialization.thomPairOverIso`) and
carries the restriction of a Thom class to a class restricting to a generator on every fibre, so
the product case `TauCeti.bijective_pullbackCup_prodThomPair` gives bijectivity over `W` in every
rank `r ≥ 0` (`TauCeti.IsThomClass.bijective_pullbackCupRestrict_of_subset_baseSet`). Induction
via the Mayer–Vietoris step `TopCat.bijective_pullbackCupRestrict_union` extends this to every
finite union of trivializing open sets
(`TauCeti.IsThomClass.bijective_pullbackCupRestrict_biUnion`).

To pass from finite trivializing unions to an arbitrary base without taking an inverse limit in
cohomology (which would face a `lim¹` obstruction), we lift the homology Thom map to a chain map

`thomCapChainMap F E A r φ : C(E, E₀; A) ⟶ C(B; A)[r]`

by capping with a relative cocycle `φ` representing `u` (`TauCeti.ChainComplex.capChainMap`) and
pushing forward along `π : E ⟶ B`. On cohomology with coefficients in any `K`-module `M`,
precomposition with `thomCapChainMap` agrees (under graded commutativity of the cup product) with
`Φ_u` on the nose. Over each finite trivializing union `W`, `Φ_u` is bijective for every `M` and
below-rank relative cohomology vanishes, so `Hom(-, M)` detects that `thomCapChainMap` over `W` is
a quasi-isomorphism (`ChainComplex.quasiIso_of_forall_quasiIso_linearYonedaFunctor`). Passing to
the filtered colimit of homology over all finite unions of the chosen trivializing open sets shows
that `thomCapChainMap` over the whole base `B` is a quasi-isomorphism with coefficients in `K`
(`TauCeti.IsThomClass.quasiIso_thomCapChainMap`). Since both singular chain complexes are
degreewise projective, `Hom(-, M)` carries this quasi-isomorphism to a quasi-isomorphism for every
`K`-module `M` (`ChainComplex.quasiIso_linearYonedaFunctor_map_of_projective`), proving the Thom
isomorphism `TauCeti.IsThomClass.bijective_thomMap` and `TauCeti.IsThomClass.thomEquiv`.

## Main definitions and results

* `TauCeti.thomMap`: the Thom map `a ↦ π^*a ⌣ u`, bilinear in `u` and `a`.
* `TauCeti.thomMap_one`: `Φ_u(1) = u`.
* `TauCeti.thomMap_naturality`, `TauCeti.thomMap_pullback`: naturality.
* `TauCeti.thomMap_singularCup`: linearity over the cohomology of the base.
* `TauCeti.singularCohomologyMap_fiberThomPairMap_thomMap`: the restriction to a fibre.
* `TauCeti.thomCapChainMap`: capping with a relative cocycle and projecting to the base as a chain
  map into the shifted singular chain complex of the base.
* `TauCeti.IsThomClass.bijective_pullbackCupRestrict_of_subset_baseSet`: the Thom isomorphism over
  a subset of the base set of a linear trivialization.
* `TauCeti.IsThomClass.bijective_pullbackCupRestrict_biUnion`: the Thom isomorphism over a finite
  union of trivializing open sets.
* `TauCeti.IsThomClass.bijective_thomMap_of_baseSet_eq_univ`: the Thom isomorphism for a bundle
  with a linear trivialization over its whole base.
* `TauCeti.IsThomClass.quasiIso_thomCapChainMap`: `thomCapChainMap` with `K`-coefficients is a
  quasi-isomorphism over an arbitrary base.
* `TauCeti.IsThomClass.bijective_thomMap`, `TauCeti.IsThomClass.thomEquiv`: the Thom isomorphism
  in singular cohomology over an arbitrary base, for every commutative ring `K`, every `K`-module
  `M`, and every rank `r ≥ 0`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory Module Opposite

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **The Thom map** `a ↦ π^*a ⌣ u` of a relative class `u ∈ Hⁿ(E, E₀; K)`, from `Hᵖ(B; M)` to
`Hᵐ(E, E₀; M)`, `p + n = m`, as a `K`-bilinear map of `u` and `a`. The chain coefficients are `K`,
and the pairing of values is the right unitor `M ⊗ K ≅ M`. For a Thom class `u` of a real vector
bundle of rank `n` it is the Thom isomorphism. -/
def thomMap (n p m : ℕ) (h : p + n = m) :
    (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p →ₗ[K]
        (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  (thomPair F E).pullbackCup M (thomPairProj F E) n p m h

/-- The Thom map of a vector bundle is `TopPair.pullbackCup` of its Thom pair and its projection,
so the results stated for the latter, such as the Mayer–Vietoris step
`TopCat.bijective_pullbackCupRestrict_union`, apply to it. -/
theorem thomMap_def (n p m : ℕ) (h : p + n = m) :
    thomMap F E M n p m h = (thomPair F E).pullbackCup M (thomPairProj F E) n p m h :=
  (rfl)

variable {M}

/-- The Thom map is the cup product of the pull-back to the total space with `u`. -/
theorem thomMap_apply {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomMap F E M n p m h u a =
      (thomPair F E).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
        (TopCat.singularCohomologyMap (thomPairProj F E) p a) u :=
  TopPair.pullbackCup_apply _ _ h u a

/-- **The Thom map sends `1` to `u`**: the image of the class of the constant `0`-cocycle with
value `1 ∈ K` is `u`. -/
@[simp]
theorem thomMap_one {n : ℕ} (h : 0 + n = n)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    thomMap F E (ModuleCat.of K K) n 0 n h u
        (((TopCat.of B).singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ 0
          ((TopCat.of B).constSingularCocycle K (𝟙 (ModuleCat.of K K)))) = u :=
  TopPair.pullbackCup_one _ _ h u

/-- **Naturality of the Thom map.** A map of Thom pairs `φ : (E', E'₀) ⟶ (E, E₀)` covering a map
of bases `g : B' ⟶ B` intertwines the Thom map of `u` with that of its pull-back `φ^*u`:
`Φ_{φ^*u}(g^*a) = φ^*Φ_u(a)`. -/
theorem thomMap_naturality {B' : Type w} [TopologicalSpace B'] {F' : Type*} [TopologicalSpace F']
    {E' : B' → Type w} [TopologicalSpace (TotalSpace F' E')] [∀ b, Zero (E' b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E']
    (φ : thomPair F' E' ⟶ thomPair F E) (g : TopCat.of B' ⟶ TopCat.of B)
    (hφ : TopPair.Hom.fst φ ≫ thomPairProj F E = thomPairProj F' E' ≫ g) {n p m : ℕ}
    (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomMap F' E' M n p m h (TopPair.singularCohomologyMap φ n u)
        (TopCat.singularCohomologyMap g p a) =
      TopPair.singularCohomologyMap φ m (thomMap F E M n p m h u a) :=
  TopPair.pullbackCup_naturality φ _ _ g hφ h u a

attribute [local instance] pullbackFiberZero in
/-- **The Thom map of a pull-back bundle.** For a continuous map `f : B' ⟶ B`, the Thom map of
the pull-back of `u` to `f^*E` sends `f^*a` to the pull-back of `Φ_u(a)`. -/
theorem thomMap_pullback {B' : Type w} [TopologicalSpace B'] (f : C(B', B)) {n p m : ℕ}
    (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomMap F ((⇑f) *ᵖ E) M n p m h
        (TopPair.singularCohomologyMap (pullbackThomPairMap F E f) n u)
        (TopCat.singularCohomologyMap (TopCat.ofHom f) p a) =
      TopPair.singularCohomologyMap (pullbackThomPairMap F E f) m (thomMap F E M n p m h u a) :=
  thomMap_naturality F E _ _ (pullbackThomPairMap_fst_comp_thomPairProj F E f) h u a

/-- **The Thom map on a fibre.** Restricted to the fibre pair `(E_b, E_b ∖ {0})`, the Thom map
of `u` is the cup product of the pull-back of `a` along the constant map at `b` with the
restriction of `u`. -/
theorem singularCohomologyMap_fiberThomPairMap_thomMap (b : B) {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    TopPair.singularCohomologyMap (fiberThomPairMap F E b) m (thomMap F E M n p m h u a) =
      (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularCup K
        (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
        (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.const (E b) b)) p a)
        (TopPair.singularCohomologyMap (fiberThomPairMap F E b) n u) := by
  rw [thomMap_apply, ← TopPair.singularCup_naturality, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, fiberThomPairMap_fst_comp_thomPairProj]
  rfl

/-- **The Thom map is linear over the cohomology of the base**: for `a ∈ H^q(B; K)` and
`b ∈ Hᵖ(B; M)`, `Φ_u(a ⌣ b) = π^*a ⌣ Φ_u(b)`. -/
theorem thomMap_singularCup {n p q r m s : ℕ} (h : p + n = m) (hqp : q + p = r)
    (hrn : r + n = s) (hqm : q + m = s)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) q)
    (b : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomMap F E M n r s hrn u
        ((TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom q p r hqp a b) =
      (thomPair F E).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom q m s hqm
        (TopCat.singularCohomologyMap (thomPairProj F E) q a) (thomMap F E M n p m h u b) := by
  rw [thomMap_apply, thomMap_apply, ← TopCat.singularCup_naturality]
  exact TopPair.singularCup_assoc K (thomPair F E) (by monoidal) (by monoidal) hqp hrn h hqm _ _ _

end TauCeti

/-! ### Capping with a relative cocycle as a chain map -/

namespace TauCeti

section CapChainMap

variable {K : Type w} [CommRing K]

/-- Scaling a morphism by `(-1) ^ n` preserves and reflects being an isomorphism. -/
private theorem isIso_neg_one_pow_zsmul_iff {C : Type*} [Category* C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    IsIso (((-1 : ℤ) ^ n) • f) ↔ IsIso f := by
  constructor
  · intro hf
    refine ⟨⟨((-1 : ℤ) ^ n) • inv (((-1 : ℤ) ^ n) • f), ?_, ?_⟩⟩
    · rw [Preadditive.comp_zsmul, ← Preadditive.zsmul_comp, IsIso.hom_inv_id]
    · rw [Preadditive.zsmul_comp, ← Preadditive.comp_zsmul, IsIso.inv_hom_id]
  · intro hf
    refine ⟨⟨((-1 : ℤ) ^ n) • inv f, ?_, ?_⟩⟩
    · rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, neg_one_pow_smul_neg_one_pow_smul,
        IsIso.hom_inv_id]
    · rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, neg_one_pow_smul_neg_one_pow_smul,
        IsIso.inv_hom_id]

/-- Capping relative chains of a topological pair `P` with a relative cocycle `φ` of degree `r` and
pushing forward along `g : P.fst ⟶ Y`, as a chain map into the shifted chain complex of `Y`. -/
private def pairCapChainMap (P : TopPair.{w}) {Y : TopCat.{w}} (g : P.fst ⟶ Y)
    (A : ModuleCat.{w} K) (r : ℕ)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    P.singularChainComplex A ⟶
      ((TopCat.toSSet.obj Y).chainComplex A).extend (ComplexShape.embeddingDownNatAdd r) :=
  ChainComplex.capChainMap K (P.alexanderWhitneyDiagonal (λ_ A).inv)
      ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom) r φ ≫
    HomologicalComplex.extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) A)
      (ComplexShape.embeddingDownNatAdd r)

/-- On homology in degree `m = r + p`, `pairCapChainMap` induces `(-1)^(r * p)` times the relative
cap product with `[φ]` followed by `g_*`. -/
private theorem homologyMap_pairCapChainMap_comp_extendHomologyIso_hom
    (P : TopPair.{w}) {Y : TopCat.{w}} (g : P.fst ⟶ Y) (A : ModuleCat.{w} K)
    {r p m : ℕ} (h : r + p = m)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    HomologicalComplex.homologyMap (pairCapChainMap P g A r φ) m ≫
        (((TopCat.toSSet.obj Y).chainComplex A).extendHomologyIso
          (ComplexShape.embeddingDownNatAdd r) (by simp; omega)).hom =
      ((-1 : ℤ) ^ (r * p)) •
        (P.singularCap K (λ_ A).inv (λ_ A).hom r p m h
            ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ) ≫
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map g) := by
  rw [pairCapChainMap, HomologicalComplex.homologyMap_comp, Category.assoc,
    HomologicalComplex.extendHomologyIso_hom_naturality,
    reassoc_of% (ChainComplex.homologyMap_capChainMap_comp_extendHomologyIso_hom
      (k := K) (P.alexanderWhitneyDiagonal (λ_ A).inv)
      ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ A).hom) r p m h φ),
    Preadditive.zsmul_comp, TopPair.singularCap_def, TauCeti.singularHomologyFunctor_obj_map,
    SSet.homologyMap]
  rfl

/-- On cohomology in degree `m = p + r` with values in any `K`-module `M`, precomposition with
`pairCapChainMap` agrees with `TopPair.pullbackCup`: the sign `(-1)^(r * p)` from `capChainMap`
cancels the graded-commutativity sign `(-1)^(p * r)` moving `[φ]` to the right. -/
private theorem homologyMap_linearYonedaFunctor_map_pairCapChainMap_apply
    (P : TopPair.{w}) {Y : TopCat.{w}} (g : P.fst ⟶ Y) (M : ModuleCat.{w} K)
    {r p m : ℕ} (h : p + r = m)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r)
    (a : Y.singularCohomology (ModuleCat.of K K) K M p) :
    HomologicalComplex.homologyMap
        ((ChainComplex.linearYonedaObjExtendIso K M
            ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of K K))
            (ComplexShape.embeddingDownNatAdd r) (ComplexShape.embeddingUpNatAdd r)
            (fun _ ↦ by simp)).inv ≫
          (ChainComplex.linearYonedaFunctor K M).map
            (pairCapChainMap P g (ModuleCat.of K K) r φ).op) m
        (((Y.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
          (ComplexShape.embeddingUpNatAdd r) (by simp; omega)).inv a) =
      P.pullbackCup M g r p m h
        ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ) a := by
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  let gStar : Y.singularCochainComplex (ModuleCat.of K K) K M ⟶
      P.fst.singularCochainComplex (ModuleCat.of K K) K M :=
    (ChainComplex.linearYonedaFunctor K M).map
      (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K)).op
  have hfac :
      (ChainComplex.linearYonedaObjExtendIso K M
          ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of K K))
          (ComplexShape.embeddingDownNatAdd r) (ComplexShape.embeddingUpNatAdd r)
          (fun _ ↦ by simp)).inv ≫
        (ChainComplex.linearYonedaFunctor K M).map
          (pairCapChainMap P g (ModuleCat.of K K) r φ).op =
      HomologicalComplex.extendMap gStar (ComplexShape.embeddingUpNatAdd r) ≫
        (ChainComplex.linearYonedaObjExtendIso K M
            ((TopCat.toSSet.obj P.fst).chainComplex (ModuleCat.of K K))
            (ComplexShape.embeddingDownNatAdd r) (ComplexShape.embeddingUpNatAdd r)
            (fun _ ↦ by simp)).inv ≫
          (ChainComplex.linearYonedaFunctor K M).map
            (ChainComplex.capChainMap K (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
              ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom) r
              φ).op :=
    (congrArg ((ChainComplex.linearYonedaObjExtendIso K M
        ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of K K))
        (ComplexShape.embeddingDownNatAdd r) (ComplexShape.embeddingUpNatAdd r)
        (fun _ ↦ by simp)).inv ≫ ·)
      ((ChainComplex.linearYonedaFunctor K M).map_comp
        (HomologicalComplex.extendMap
          (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K))
          (ComplexShape.embeddingDownNatAdd r)).op
        (ChainComplex.capChainMap K (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
          ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom) r
          φ).op)).trans
    ((Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ (ChainComplex.linearYonedaFunctor K M).map
          (ChainComplex.capChainMap K (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
            ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom) r
            φ).op)
        (ChainComplex.linearYonedaObjExtendIso_inv_naturality K M
          (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of K K))
          (ComplexShape.embeddingDownNatAdd r) (ComplexShape.embeddingUpNatAdd r)
          (fun _ ↦ by simp))).trans
      (Category.assoc _ _ _))
  rw [hfac, HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply]
  have hext :
      HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap gStar (ComplexShape.embeddingUpNatAdd r)) m
          (((Y.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
            (ComplexShape.embeddingUpNatAdd r) (by simp; omega)).inv
              ((Y.singularCochainComplex (ModuleCat.of K K) K M).homologyπ p ψ)) =
        ((P.fst.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
          (ComplexShape.embeddingUpNatAdd r) (by simp; omega)).inv
            ((P.fst.singularCochainComplex (ModuleCat.of K K) K M).homologyπ p
              (HomologicalComplex.cyclesMap gStar p ψ)) := by
    have hnat :
        ((Y.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
            (ComplexShape.embeddingUpNatAdd r) (by simp; omega)).inv ≫
          HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap gStar (ComplexShape.embeddingUpNatAdd r)) m =
        HomologicalComplex.homologyMap gStar p ≫
          ((P.fst.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
            (ComplexShape.embeddingUpNatAdd r) (by simp; omega)).inv := by
      rw [← cancel_mono ((P.fst.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
          (ComplexShape.embeddingUpNatAdd r) (by simp; omega)).hom,
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        HomologicalComplex.extendHomologyIso_hom_naturality, Iso.inv_hom_id_assoc]
    have h1 := ConcreteCategory.congr_hom hnat
      ((Y.singularCochainComplex (ModuleCat.of K K) K M).homologyπ p ψ)
    have h2 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality gStar p) ψ
    simp only [ConcreteCategory.comp_apply] at h1 h2
    rw [h1, h2]
  rw [hext, ChainComplex.homologyMap_linearYonedaFunctor_map_capChainMap_apply (k := K)
    (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
    ((TopCat.toSSet.obj P.fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
    (λ_ M).hom r p m (by omega) φ
    (HomologicalComplex.cyclesMap gStar p ψ) (HomologicalComplex.cyclesMap gStar p ψ)
    (by
      rw [SSet.chainComplexPairing_leftUnitor_hom_f]
      exact (leftUnitor_naturality
        ((P.fst.singularCochainComplex (ModuleCat.of K K) K M).iCycles p
          (HomologicalComplex.cyclesMap gStar p ψ))).symm)]
  have hpull :
      (P.fst.singularCochainComplex (ModuleCat.of K K) K M).homologyπ p
          (HomologicalComplex.cyclesMap gStar p ψ) =
        TopCat.singularCohomologyMap g p
          ((Y.singularCochainComplex (ModuleCat.of K K) K M).homologyπ p ψ) := by
    have h0 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality gStar p) ψ
    simp only [ConcreteCategory.comp_apply] at h0
    exact h0.symm
  have hcomm :
      ChainComplex.cup K (P.alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
          (λ_ M).hom r p m (by omega)
          ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ)
          ((P.fst.singularCochainComplex (ModuleCat.of K K) K M).homologyπ p
            (HomologicalComplex.cyclesMap gStar p ψ)) =
        ((-1 : ℤ) ^ (p * r)) •
          P.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p r m h
            ((P.fst.singularCochainComplex (ModuleCat.of K K) K M).homologyπ p
              (HomologicalComplex.cyclesMap gStar p ψ))
            ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ) :=
    TopPair.singularCup_gradedComm K P
      (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (u' := (λ_ (ModuleCat.of K K)).inv)
      (μ := (ρ_ M).hom) (μ' := (λ_ M).hom)
      (by rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, ← unitors_inv_equal]; rfl)
      (braiding_leftUnitor M) h _ _
  refine (congrArg (((-1 : ℤ) ^ (r * p)) • ·) hcomm).trans ?_
  rw [mul_comm p r]
  exact (neg_one_pow_smul_neg_one_pow_smul (r * p) _).trans <| by
    rw [hpull, TopPair.pullbackCup_apply]
    rfl

/-- `TopPair.pullbackCup` is bijective in degree `p` (with `p + r = m`) if and only if
`pairCapChainMap` induces an isomorphism on `Hᵐ(-; M)`. -/
private theorem bijective_pullbackCup_iff_isIso_homologyMap_linearYonedaFunctor_map_pairCapChainMap
    (P : TopPair.{w}) {Y : TopCat.{w}} (g : P.fst ⟶ Y) (M : ModuleCat.{w} K)
    {r p m : ℕ} (h : p + r = m)
    (φ : (P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    Function.Bijective (P.pullbackCup M g r p m h
        ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ)) ↔
      IsIso (HomologicalComplex.homologyMap
        ((ChainComplex.linearYonedaFunctor K M).map
          (pairCapChainMap P g (ModuleCat.of K K) r φ).op) m) := by
  have heq :
      ModuleCat.ofHom (P.pullbackCup M g r p m h
        ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ)) =
      ((Y.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
          (ComplexShape.embeddingUpNatAdd r) (by simp; omega)).inv ≫
        HomologicalComplex.homologyMap
          (ChainComplex.linearYonedaObjExtendIso K M
            ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of K K))
            (ComplexShape.embeddingDownNatAdd r) (ComplexShape.embeddingUpNatAdd r)
            (fun _ ↦ by simp)).inv m ≫
        HomologicalComplex.homologyMap
          ((ChainComplex.linearYonedaFunctor K M).map
            (pairCapChainMap P g (ModuleCat.of K K) r φ).op) m := by
    ext a
    simp only [ModuleCat.hom_ofHom]
    have hcomp := ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_comp
      (ChainComplex.linearYonedaObjExtendIso K M
        ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of K K))
        (ComplexShape.embeddingDownNatAdd r) (ComplexShape.embeddingUpNatAdd r)
        (fun _ ↦ by simp)).inv
      ((ChainComplex.linearYonedaFunctor K M).map
        (pairCapChainMap P g (ModuleCat.of K K) r φ).op) m)
      (((Y.singularCochainComplex (ModuleCat.of K K) K M).extendHomologyIso
        (ComplexShape.embeddingUpNatAdd r) (by simp; omega)).inv a)
    simp only [ConcreteCategory.comp_apply] at hcomp
    exact (homologyMap_linearYonedaFunctor_map_pairCapChainMap_apply P g M h φ a).symm.trans hcomp
  have : IsIso (HomologicalComplex.homologyMap
      (ChainComplex.linearYonedaObjExtendIso K M
        ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of K K))
        (ComplexShape.embeddingDownNatAdd r) (ComplexShape.embeddingUpNatAdd r)
        (fun _ ↦ by simp)).inv m) :=
    ((HomologicalComplex.homologyFunctor _ _ m).mapIso
      (ChainComplex.linearYonedaObjExtendIso K M
        ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of K K))
        (ComplexShape.embeddingDownNatAdd r) (ComplexShape.embeddingUpNatAdd r)
        (fun _ ↦ by simp))).isIso_inv
  change Function.Bijective (ModuleCat.ofHom (P.pullbackCup M g r p m h
      ((P.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ r φ))) ↔ _
  rw [← ConcreteCategory.isIso_iff_bijective, heq]
  exact (isIso_comp_left_iff _ _).trans (isIso_comp_left_iff _ _)

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- **Capping with a relative cocycle and projecting to the base, as a chain map**: for a relative
cocycle `φ` of degree `r` on the Thom pair `(E, E₀)` with coefficients in `K`, capping relative
chains with `φ` along the relative Alexander–Whitney diagonal (`TauCeti.ChainComplex.capChainMap`)
and pushing forward along the bundle projection `π : E ⟶ B` gives a chain map
`C(E, E₀; A) ⟶ C(B; A)[r]` into the shifted singular chain complex of the base. -/
def thomCapChainMap (A : ModuleCat.{w} K) (r : ℕ)
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    (thomPair F E).singularChainComplex A ⟶
      ((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extend
        (ComplexShape.embeddingDownNatAdd r) :=
  pairCapChainMap (thomPair F E) (thomPairProj F E) A r φ

/-- In degree `m = r + p`, `thomCapChainMap` caps with `φ`, pushes forward along `π`, and shifts
into the extended complex with the sign `(-1)^(r * p)`. -/
theorem thomCapChainMap_f (A : ModuleCat.{w} K) {r p m : ℕ} (h : r + p = m)
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    (thomCapChainMap F E A r φ).f m =
      ((-1 : ℤ) ^ (r * p)) •
        ChainComplex.capChain K ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
          ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom) r p m h
          (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).iCycles
            r φ) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) A).f p ≫
        (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendXIso
          (ComplexShape.embeddingDownNatAdd r) (by simp; omega)).inv := by
  dsimp [thomCapChainMap, pairCapChainMap]
  rw [ChainComplex.capChainMap_f _ _ r p m h φ, Preadditive.zsmul_comp, Category.assoc,
    HomologicalComplex.extendMap_f _ _ (i := p) (i' := m) (by simp; omega),
    Iso.inv_hom_id_assoc]

/-- In degrees `m < r`, `thomCapChainMap` vanishes. -/
theorem thomCapChainMap_f_of_lt (A : ModuleCat.{w} K) {r m : ℕ} (h : m < r)
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    (thomCapChainMap F E A r φ).f m = 0 := by
  dsimp [thomCapChainMap, pairCapChainMap]
  rw [ChainComplex.capChainMap_f_of_lt _ _ r m h φ, zero_comp]

/-- On homology in degree `m = r + p`, `thomCapChainMap` induces `(-1)^(r * p)` times the relative
cap product with `[φ]` followed by `π_*`. -/
theorem homologyMap_thomCapChainMap_comp_extendHomologyIso_hom (A : ModuleCat.{w} K)
    {r p m : ℕ} (h : r + p = m)
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    HomologicalComplex.homologyMap (thomCapChainMap F E A r φ) m ≫
        (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendHomologyIso
          (ComplexShape.embeddingDownNatAdd r) (by simp; omega)).hom =
      ((-1 : ℤ) ^ (r * p)) •
        ((thomPair F E).singularCap K (λ_ A).inv (λ_ A).hom r p m h
            (((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
              (ModuleCat.of K K)).homologyπ r φ) ≫
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map
            (thomPairProj F E)) :=
  homologyMap_pairCapChainMap_comp_extendHomologyIso_hom (thomPair F E) (thomPairProj F E) A h φ

end CapChainMap

end TauCeti

/-! ### The Thom isomorphism over trivializing sets and finite unions -/

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- Over a subset `W` of the base set of a linear trivialization `e`, the restriction of a Thom
class `u` to `(E|_W, E₀|_W)`, read on the product bundle `W × F` through `e`, restricts on the fibre
over each point of `W` to a generator: it is the restriction of `u` to the fibre pair
`(E_b, E_b ∖ {0})`, read through the isomorphism of fibre pairs given by `e` at `b`. -/
private theorem span_singularCohomologyMap_prodThomPairFiberMap_thomPairOverIso_inv
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) (e : Trivialization F (π F E)) [e.IsLinear ℝ] {W : Set B}
    (hW : W ⊆ e.baseSet) (b : W) :
    Submodule.span K {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) <|
      TopPair.singularCohomologyMap (e.thomPairOverIso ℝ hW).inv (finrank ℝ F) <|
        TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
          (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) (finrank ℝ F) u} =
      ⊤ := by
  set ψ := (e.continuousLinearEquivAt ℝ b.1 (hW b.2)).complZeroPairIso
  have hψ : Function.Surjective (TopPair.singularCohomologyMap (R := ModuleCat.of K K) (k := K)
      (M := ModuleCat.of K K) ψ.inv (finrank ℝ F)).hom := fun y ↦
    ⟨TopPair.singularCohomologyMap ψ.hom _ y, by
      rw [← TopPair.singularCohomologyMap_comp_apply, ψ.inv_hom_id,
        TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]⟩
  have hb := congrArg (Submodule.map (TopPair.singularCohomologyMap ψ.inv _).hom)
    ((isThomClass_iff.1 hu).2 b.1)
  rw [Submodule.map_span, Set.image_singleton, Submodule.map_top,
    LinearMap.range_eq_top.2 hψ] at hb
  rw [← TopPair.singularCohomologyMap_comp_apply,
    e.prodThomPairFiberMap_comp_thomPairOverIso_inv ℝ hW, TopPair.singularCohomologyMap_comp_apply,
    ← TopPair.singularCohomologyMap_comp_apply (fiberThomPairOverMap F E b.2),
    fiberThomPairOverMap_comp_restrictPreimagePairMap]
  exact hb

/-- **The Thom isomorphism over a trivializing set.** Let `E` be a real vector bundle of any
finite rank `r ≥ 0`, let `u ∈ Hʳ(E, E₀; K)` be a Thom class, and let `W` be contained in the base
set of a linear trivialization `e`. Then for every `K`-module `M` and every degree `p`, the Thom
map of the restriction of `u` to the Thom pair `(E|_W, E₀|_W)` of the restriction of the bundle to
`W`, `Hᵖ(W; M) ⟶ Hᵖ⁺ʳ(E|_W, E₀|_W; M)`, `a ↦ π^*a ⌣ u|` (`TopCat.pullbackCupRestrict`), is
bijective. These are the sets over which the Mayer–Vietoris step
`TopCat.bijective_pullbackCupRestrict_union` starts. -/
theorem IsThomClass.bijective_pullbackCupRestrict_of_subset_baseSet
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {W : Set B} (hW : W ⊆ e.baseSet) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (TopCat.pullbackCupRestrict (thomPairProj F E) (zeroSectionCompl F E) M W
      _ p m h u) := by
  have := (isThomClass_iff.1 hu).1
  -- The trivialization identifies `(E|_W, E₀|_W)` with `(W × F, W × (F ∖ {0}))` over `W`.
  set φ := e.thomPairOverIso ℝ hW
  set g : (thomPairOver F E W).fst ⟶ TopCat.of W := TopCat.ofHom
    ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).restrictPreimage W)
  have hg : TopPair.Hom.fst φ.hom ≫ prodThomPairProj W F = g ≫ 𝟙 _ :=
    TopCat.ext fun v ↦ (prodThomPairProj_apply F _).trans
      (congrArg Prod.fst (e.thomPairOverIso_hom_fst_apply ℝ hW v))
  set uW := TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
    (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) _ u
  have hφ : TopPair.singularCohomologyMap φ.hom _ (TopPair.singularCohomologyMap φ.inv _ uW) =
      uW := by
    rw [← TopPair.singularCohomologyMap_comp_apply, φ.hom_inv_id,
      TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply]
  -- So the Thom map over `W` is that of the product bundle, bijective by the product case.
  have key := (TopPair.bijective_pullbackCup_iff_of_isIso φ.hom (𝟙 _) hg h
    (TopPair.singularCohomologyMap φ.inv _ uW)).2
    (bijective_pullbackCup_prodThomPair M _
      (span_singularCohomologyMap_prodThomPairFiberMap_thomPairOverIso_inv hu e hW) h)
  rw [hφ] at key
  -- The pair over `W` built from the projection `thomPairProj F E` is `thomPairOver F E W`, once
  -- the projection is unfolded by `thomPairProj_def`; it occurs in the type of that pair, so it is
  -- first replaced by a variable.
  suffices ∀ π' : TopCat.of (TotalSpace F E) ⟶ TopCat.of B, π' = thomPairProj F E →
      Function.Bijective (TopCat.pullbackCupRestrict π' (zeroSectionCompl F E) M W _ p m h u) from
    this _ rfl
  intro π' hπ'
  rw [TopCat.pullbackCupRestrict_apply]
  rw [thomPairProj_def] at hπ'
  subst hπ'
  exact key

/-- Relative cohomology of `(π⁻¹ W, π⁻¹ W ∩ E₀)` vanishes below the rank when `W` lies in the base
set of a linear trivialization. -/
private theorem isZero_singularCohomology_restrictPreimage_of_subset_baseSet
    [FiniteDimensional ℝ F] (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    {W : Set B} (hW : W ⊆ e.baseSet) {j : ℕ} (hj : j < finrank ℝ F) :
    IsZero ((TopPair.ofInclusion (Set.inter_subset_left :
      (thomPairProj F E) ⁻¹' W ∩ zeroSectionCompl F E ⊆
        (thomPairProj F E) ⁻¹' W)).singularCohomology (ModuleCat.of K K) K M j) := by
  suffices ∀ π' : TopCat.of (TotalSpace F E) ⟶ TopCat.of B, π' = thomPairProj F E →
      IsZero ((TopPair.ofInclusion (Set.inter_subset_left :
        π' ⁻¹' W ∩ zeroSectionCompl F E ⊆ π' ⁻¹' W)).singularCohomology
          (ModuleCat.of K K) K M j) from this _ rfl
  intro π' hπ'
  rw [thomPairProj_def] at hπ'
  subst hπ'
  exact TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of K K) M j
    fun _ h ↦ e.isZero_singularHomology_thomPairOver hW (ModuleCat.of K K) (h.trans_lt hj)

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] in
/-- Relative cohomology of the Thom pair over the empty set vanishes in every degree. -/
private theorem isZero_singularCohomology_restrictPreimage_empty (m : ℕ) :
    IsZero ((TopPair.ofInclusion (Set.inter_subset_left :
      (thomPairProj F E) ⁻¹' (∅ : Set B) ∩ zeroSectionCompl F E ⊆
        (thomPairProj F E) ⁻¹' (∅ : Set B))).singularCohomology (ModuleCat.of K K) K M m) := by
  suffices ∀ π' : TopCat.of (TotalSpace F E) ⟶ TopCat.of B, π' = thomPairProj F E →
      IsZero ((TopPair.ofInclusion (Set.inter_subset_left :
        π' ⁻¹' (∅ : Set B) ∩ zeroSectionCompl F E ⊆ π' ⁻¹' (∅ : Set B))).singularCohomology
          (ModuleCat.of K K) K M m) from this _ rfl
  intro π' hπ'
  rw [thomPairProj_def] at hπ'
  subst hπ'
  exact TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of K K) M m
    fun j _ ↦ isZero_singularHomology_thomPairOver_empty (F := F) (E := E) (ModuleCat.of K K) j

/-- **The Thom isomorphism over a finite union of trivializing open sets.** Let `E` be a real
vector bundle of any finite rank `r ≥ 0` with Thom class `u ∈ Hʳ(E, E₀; K)`, and let `W i`, `i ∈ s`,
be finitely many open sets of the base, each contained in the base set of a linear trivialization.
Then for every `K`-module `M` and every degree `p`, the Thom map of `u` over `⋃ i ∈ s, W i` is
bijective. -/
theorem IsThomClass.bijective_pullbackCupRestrict_biUnion
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (TopCat.pullbackCupRestrict (thomPairProj F E) (zeroSectionCompl F E) M
      (⋃ i ∈ s, W i) _ p m h u) := by
  classical
  have := (isThomClass_iff.1 hu).1
  induction s using Finset.induction_on generalizing p m with
  | empty =>
    rw [show (⋃ i ∈ (∅ : Finset ι), W i) = ∅ by simp]
    have hsrc : Subsingleton ((TopCat.of (∅ : Set B)).singularCohomology
        (ModuleCat.of K K) K M p) :=
      ModuleCat.isZero_iff_subsingleton.1
        (isZero_singularCohomology_of_isEmpty (ModuleCat.of K K) K M (TopCat.of (∅ : Set B)) p)
    have htgt : Subsingleton ((TopPair.ofInclusion (Set.inter_subset_left :
        (thomPairProj F E) ⁻¹' (∅ : Set B) ∩ zeroSectionCompl F E ⊆
          (thomPairProj F E) ⁻¹' (∅ : Set B))).singularCohomology
          (ModuleCat.of K K) K M m) :=
      ModuleCat.isZero_iff_subsingleton.1
        (isZero_singularCohomology_restrictPreimage_empty M m)
    exact (Function.bijective_iff_existsUnique _).2 fun y ↦
      ⟨0, Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert a s := Finset.mem_insert_of_mem hi
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    exact TopCat.bijective_pullbackCupRestrict_union (thomPairProj F E) (zeroSectionCompl F E) M
      (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (hs i hi)) u
      (fun q _ ↦ hu.bijective_pullbackCupRestrict_of_subset_baseSet M e he rfl)
      (fun q _ ↦ ih (fun i hi ↦ hWo i (hs i hi)) (fun i hi ↦ hWe i (hs i hi)) rfl)
      (fun q _ ↦ hu.bijective_pullbackCupRestrict_of_subset_baseSet M e
        (Set.inter_subset_left.trans he) rfl)
      (fun j hj ↦ isZero_singularCohomology_restrictPreimage_of_subset_baseSet M e
        (Set.inter_subset_left.trans he) (by omega))
      h

/-- **The Thom isomorphism for a trivializable bundle.** For a real vector bundle `E` of any finite
rank `r ≥ 0` with a linear trivialization over its whole base, the Thom map
`Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(E, E₀; M)`, `a ↦ π^*a ⌣ u`, of every Thom class `u` is bijective, for every
`K`-module `M` and every degree `p`. -/
theorem IsThomClass.bijective_thomMap_of_baseSet_eq_univ
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : IsThomClass F E u) (e : Trivialization F (π F E))
    [e.IsLinear ℝ] (he : e.baseSet = Set.univ) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M _ p m h u) := by
  rw [thomMap_def]
  exact (TopCat.bijective_pullbackCupRestrict_univ_iff _ _ M h u).1
    (hu.bijective_pullbackCupRestrict_of_subset_baseSet M e he.ge h)

end TauCeti

/-! ### The Thom isomorphism over an arbitrary base -/

namespace TauCeti

section ArbitraryBase

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K]

/-- The projection of the restricted Thom pair `(E|_W, E₀|_W)` to `W`. -/
private def thomPairOverProj (W : Set B) : (thomPairOver F E W).fst ⟶ TopCat.of W :=
  TopCat.ofHom
    ((⟨π F E, FiberBundle.continuous_proj F E⟩ : C(TotalSpace F E, B)).restrictPreimage W)

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] in
/-- Over a subset `W` of the base, `TopCat.restrictPreimagePairMap` for `π F E` agrees with the
inclusion `thomPairOverMap F E (subset_univ _) ≫ (thomPairOverUnivIso F E).hom`. -/
private theorem restrictPreimagePairMap_eq_thomPairOverMap_comp (W : Set B) :
    TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E))
        (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (zeroSectionCompl F E) W =
      thomPairOverMap F E (Set.subset_univ W) ≫ (thomPairOverUnivIso F E).hom :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦
    (TopCat.restrictPreimagePairMap_fst_apply (X := TopCat.of (TotalSpace F E))
      (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (zeroSectionCompl F E) W x).trans
      ((thomPairOverUnivIso_hom_fst_apply F E _).trans
        (congrArg Subtype.val (thomPairOverMap_fst_apply F E (Set.subset_univ W) x))).symm)

/-- Over a finite union of the chosen trivializing open sets, capping with a cocycle representing
the restriction of a Thom class is a quasi-isomorphism on `K`-chains, because `Hom(-, M)` turns it
into the cohomology Thom map, which is bijective for every `K`-module `M`. -/
private theorem quasiIso_pairCapChainMap_finiteTrivializingUnion
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (s : Finset B)
    (φ : ((thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularCochainComplex
      (ModuleCat.of K K) K (ModuleCat.of K K)).cycles (finrank ℝ F))
    (hφ : ((thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularCochainComplex
        (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ (finrank ℝ F) φ =
      TopPair.singularCohomologyMap
        (thomPairOverMap F E (Set.subset_univ _) ≫ (thomPairOverUnivIso F E).hom) _ u) :
    QuasiIso (pairCapChainMap
      (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet))
      (thomPairOverProj (F := F) (E := E) (⋃ b ∈ s, (trivializationAt F E b).baseSet))
      (ModuleCat.of K K) (finrank ℝ F) φ) := by
  have := (isThomClass_iff.1 hu).1
  refine _root_.ChainComplex.quasiIso_of_forall_quasiIso_linearYonedaFunctor K _ fun M ↦ ?_
  rw [quasiIso_iff]
  intro m
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hm : finrank ℝ F ≤ m
  · have hpm : (m - finrank ℝ F) + finrank ℝ F = m := by omega
    rw [← bijective_pullbackCup_iff_isIso_homologyMap_linearYonedaFunctor_map_pairCapChainMap
      (thomPairOver F E _) (thomPairOverProj _) M hpm φ, hφ]
    have hbij := hu.bijective_pullbackCupRestrict_biUnion M s
      (fun b _ ↦ (trivializationAt F E b).open_baseSet)
      (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) hpm
    suffices ∀ π' : TopCat.of (TotalSpace F E) ⟶ TopCat.of B, π' = thomPairProj F E →
        Function.Bijective (TopCat.pullbackCupRestrict π' (zeroSectionCompl F E) M
          (⋃ b ∈ s, (trivializationAt F E b).baseSet) _ (m - finrank ℝ F) m hpm u) →
        Function.Bijective
          ((thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).pullbackCup
            M (thomPairOverProj _) _ (m - finrank ℝ F) m hpm (TopPair.singularCohomologyMap
              (thomPairOverMap F E (Set.subset_univ _) ≫ (thomPairOverUnivIso F E).hom) _ u)) from
      this _ rfl hbij
    intro π' hπ' h'
    rw [thomPairProj_def] at hπ'
    subst hπ'
    rw [TopCat.pullbackCupRestrict_apply, restrictPreimagePairMap_eq_thomPairOverMap_comp] at h'
    exact h'
  · have hlt : m < finrank ℝ F := Nat.lt_of_not_ge hm
    have hsrc : IsZero ((((ChainComplex.linearYonedaFunctor K M).obj
        (op (((TopCat.toSSet.obj
          (TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet))).chainComplex
            (ModuleCat.of K K)).extend
          (ComplexShape.embeddingDownNatAdd (finrank ℝ F)))))).homology m) := by
      refine IsZero.of_iso ?_ (((HomologicalComplex.homologyFunctor _ _ m).mapIso
        (ChainComplex.linearYonedaObjExtendIso K M
          ((TopCat.toSSet.obj
            (TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet))).chainComplex
              (ModuleCat.of K K))
          (ComplexShape.embeddingDownNatAdd (finrank ℝ F))
          (ComplexShape.embeddingUpNatAdd (finrank ℝ F)) (fun _ ↦ by simp))))
      exact (HomologicalComplex.exactAt_iff_isZero_homology _ m).1
        (HomologicalComplex.extend_exactAt _ (ComplexShape.embeddingUpNatAdd (finrank ℝ F)) m
          (by simp; omega))
    have htgt : IsZero
        ((thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularCohomology
          (ModuleCat.of K K) K M m) :=
      isZero_singularCohomology_thomPairOver_biUnion (ModuleCat.of K K) M s
        (fun b _ ↦ (trivializationAt F E b).open_baseSet)
        (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) hlt
    exact IsZero.isIso hsrc htgt _

/-- Over each finite union of the chosen trivializing open sets, the homology Thom map with
coefficients in `K` is an isomorphism in every degree. -/
private theorem isIso_homologyThomOver_finiteTrivializingUnion
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (s : Finset B) (p : ℕ) :
    IsIso ((thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularCap K
        (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom (finrank ℝ F) p (finrank ℝ F + p)
        rfl (TopPair.singularCohomologyMap
          (thomPairOverMap F E (Set.subset_univ _) ≫ (thomPairOverUnivIso F E).hom) _ u) ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
        (thomPairOverProj (F := F) (E := E) (⋃ b ∈ s, (trivializationAt F E b).baseSet))) := by
  obtain ⟨φ, hφ⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ (finrank ℝ F)
    (TopPair.singularCohomologyMap
      (thomPairOverMap F E (Set.subset_univ _) ≫ (thomPairOverUnivIso F E).hom) _ u)
  have hqi := quasiIso_pairCapChainMap_finiteTrivializingUnion hu s φ hφ
  have hiso : IsIso (HomologicalComplex.homologyMap
      (pairCapChainMap (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet))
        (thomPairOverProj _) (ModuleCat.of K K) (finrank ℝ F) φ) (finrank ℝ F + p)) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 ((quasiIso_iff _).1 hqi _)
  have hcomp := homologyMap_pairCapChainMap_comp_extendHomologyIso_hom
    (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)) (thomPairOverProj _)
    (ModuleCat.of K K) (p := p) rfl φ
  rw [hφ] at hcomp
  have hcompIso : IsIso (HomologicalComplex.homologyMap
        (pairCapChainMap (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet))
          (thomPairOverProj _) (ModuleCat.of K K) (finrank ℝ F) φ) (finrank ℝ F + p) ≫
      (((TopCat.toSSet.obj (TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet))).chainComplex
        (ModuleCat.of K K)).extendHomologyIso
          (ComplexShape.embeddingDownNatAdd (finrank ℝ F)) (j := p) (by simp; omega)).hom) :=
    inferInstance
  rw [hcomp] at hcompIso
  exact (isIso_neg_one_pow_zsmul_iff _ (finrank ℝ F * p)).1 hcompIso

variable (F E) in
/-- The finite unions of the chosen trivializing open sets, as subspaces of the base. -/
private def baseFiniteTrivializingUnionDiagram : Finset B ⥤ TopCat.{w} where
  obj s := TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet)
  map f := TopCat.ofHom
    (ContinuousMap.inclusion (Set.biUnion_subset_biUnion_left (Finset.coe_subset.2 f.le)))

variable (F E) in
/-- The inclusions of the finite unions of the chosen trivializing open sets into the base. -/
private def baseFiniteTrivializingUnionCocone :
    Cocone (baseFiniteTrivializingUnionDiagram (B := B) F E) where
  pt := TopCat.of B
  ι := { app _ := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ }

variable (F E K) in
/-- In every degree `p`, the homology of the base is the filtered colimit of the homologies of the
finite unions of the chosen trivializing open sets. -/
private def isColimitSingularHomologyBaseFiniteTrivializingUnion (p : ℕ) :
    IsColimit (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj
      (ModuleCat.of K K)).mapCocone (baseFiniteTrivializingUnionCocone (B := B) F E)) :=
  isColimitMapCoconeSingularHomology (ModuleCat.of K K) p
    (baseFiniteTrivializingUnionCocone F E) (fun _ ↦ Topology.IsEmbedding.subtypeVal)
    fun L hL ↦ by
      obtain ⟨s, hs⟩ := hL.elim_finite_subcover _
        (fun b ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦
          Set.mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
      exact ⟨s, fun b hb ↦ ⟨⟨b, hs hb⟩, rfl⟩⟩

/-- Passing to the filtered colimit over finite unions of trivializing open sets shows that the
homology Thom map over the whole base with `K`-coefficients is an isomorphism in every degree. -/
private theorem isIso_homologyThomMap_self
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) (p : ℕ) :
    IsIso ((thomPair F E).singularCap K (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom
        (finrank ℝ F) p (finrank ℝ F + p) rfl u ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
        (thomPairProj F E)) := by
  have := (isThomClass_iff.1 hu).1
  let m := finrank ℝ F + p
  let P₁ := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    (ModuleCat.of K K) m
  let P₂ := isColimitSingularHomologyBaseFiniteTrivializingUnion F E K p
  let f (s : Finset B) :
      (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology
          (ModuleCat.of K K) m ⟶
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj
          (ModuleCat.of K K)).obj (TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet)) :=
    (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularCap K
        (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom (finrank ℝ F) p m rfl
        (TopPair.singularCohomologyMap
          (thomPairOverMap F E (Set.subset_univ _) ≫ (thomPairOverUnivIso F E).hom) _ u) ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
        (thomPairOverProj (F := F) (E := E) (⋃ b ∈ s, (trivializationAt F E b).baseSet))
  have hobj (s : Finset B) :
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) m).obj
        ((thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).obj s) =
      (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology
        (ModuleCat.of K K) m := by
    rw [thomPairFiniteTrivializingUnionDiagram_obj, TopPair.singularHomologyFunctor_obj]
  have hpt :
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) m).obj
        (thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).pt =
      (thomPair F E).singularHomology (ModuleCat.of K K) m := by
    rw [thomPairFiniteTrivializingUnionCocone_pt, TopPair.singularHomologyFunctor_obj]
  let α : thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
        TopPair.singularHomologyFunctor (ModuleCat.of K K) m ≅
      baseFiniteTrivializingUnionDiagram F E ⋙
        (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K) :=
    NatIso.ofComponents
      (fun s ↦ eqToIso (hobj s) ≪≫ @asIso _ _ _ _ (f s)
        (isIso_homologyThomOver_finiteTrivializingUnion hu s p))
      fun {s t} hst ↦ by
        dsimp only [Functor.comp_obj, Functor.comp_map, baseFiniteTrivializingUnionDiagram]
        simp only [thomPairFiniteTrivializingUnionDiagram_map, TopPair.singularHomologyFunctor_map,
          Iso.trans_hom, eqToIso.hom, Category.assoc, TopPair.singularHomologyMap_comp,
          TopPair.singularHomologyMap_eqToHom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        congr 1
        have hsub :
            (⋃ b ∈ s, (trivializationAt F E b).baseSet) ⊆
              ⋃ b ∈ t, (trivializationAt F E b).baseSet :=
          Set.biUnion_subset_biUnion_left (Finset.coe_subset.2 hst.le)
        change TopPair.singularHomologyMap (thomPairOverMap F E hsub) (ModuleCat.of K K) m ≫ f t =
          f s ≫ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj
            (ModuleCat.of K K)).map (TopCat.ofHom (ContinuousMap.inclusion hsub))
        dsimp only [f]
        have hproj :
            TopPair.Hom.fst (thomPairOverMap F E hsub) ≫
                thomPairOverProj (F := F) (E := E) (⋃ b ∈ t, (trivializationAt F E b).baseSet) =
              thomPairOverProj (F := F) (E := E) (⋃ b ∈ s, (trivializationAt F E b).baseSet) ≫
                TopCat.ofHom (ContinuousMap.inclusion hsub) :=
          TopCat.ext fun v ↦
            Subtype.ext (congrArg (fun w ↦ π F E w.1) (thomPairOverMap_fst_apply F E hsub v))
        have hcap := TopPair.singularCap_naturality (thomPairOverMap F E hsub) K
          (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom (finrank ℝ F) p m rfl
          (TopPair.singularCohomologyMap
            (thomPairOverMap F E (Set.subset_univ _) ≫ (thomPairOverUnivIso F E).hom) _ u)
        rw [← TopPair.singularCohomologyMap_comp_apply,
          thomPairOverMap_comp_thomPairOverMap_assoc] at hcap
        rw [← Category.assoc, ← hcap, Category.assoc, ← Functor.map_comp, hproj, Functor.map_comp,
          ← Category.assoc]
  let g : (thomPair F E).singularHomology (ModuleCat.of K K) m ⟶
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj
        (ModuleCat.of K K)).obj (TopCat.of B) :=
    (thomPair F E).singularCap K (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom
        (finrank ℝ F) p m rfl u ≫
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
        (thomPairProj F E)
  have hcolim : eqToHom hpt ≫ g = (P₁.coconePointsIsoOfNatIso P₂ α).hom := by
    refine P₁.hom_ext fun s ↦ ?_
    refine (?_ : ((TopPair.singularHomologyFunctor (ModuleCat.of K K) m).mapCocone
        (thomPairFiniteTrivializingUnionCocone (F := F) (E := E))).ι.app s ≫ eqToHom hpt ≫ g =
      α.hom.app s ≫ (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj
        (ModuleCat.of K K)).mapCocone (baseFiniteTrivializingUnionCocone F E)).ι.app s).trans
      (P₁.comp_coconePointsIsoOfNatIso_hom P₂ α s).symm
    dsimp only [Functor.mapCocone_ι_app, α, NatIso.ofComponents_hom_app,
      baseFiniteTrivializingUnionCocone]
    simp only [thomPairFiniteTrivializingUnionCocone_ι_app, TopPair.singularHomologyFunctor_map,
      Iso.trans_hom, eqToIso.hom, Category.assoc, TopPair.singularHomologyMap_comp,
      TopPair.singularHomologyMap_eqToHom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    congr 1
    rw [← Category.assoc, ← TopPair.singularHomologyMap_comp]
    change TopPair.singularHomologyMap
        (thomPairOverMap F E (Set.subset_univ _) ≫ (thomPairOverUnivIso F E).hom)
        (ModuleCat.of K K) m ≫ g =
      f s ≫ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj
        (ModuleCat.of K K)).map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    dsimp only [f, g]
    have hproj :
        TopPair.Hom.fst (thomPairOverMap F E (Set.subset_univ _) ≫ (thomPairOverUnivIso F E).hom) ≫
            thomPairProj F E =
          thomPairOverProj (F := F) (E := E) (⋃ b ∈ s, (trivializationAt F E b).baseSet) ≫
            TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :=
      TopCat.ext fun v ↦
        (thomPairProj_apply F E _).trans <|
          congrArg (π F E) <|
            (thomPairOverUnivIso_hom_fst_apply F E _).trans
              (congrArg Subtype.val (thomPairOverMap_fst_apply F E (Set.subset_univ _) v))
    have hcap := TopPair.singularCap_naturality
      (thomPairOverMap F E (Set.subset_univ (⋃ b ∈ s, (trivializationAt F E b).baseSet)) ≫
        (thomPairOverUnivIso F E).hom) K
      (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom (finrank ℝ F) p m rfl u
    rw [← Category.assoc, ← hcap, Category.assoc, ← Functor.map_comp, hproj, Functor.map_comp,
      ← Category.assoc]
  have : IsIso (eqToHom hpt ≫ g) := by
    rw [hcolim]
    exact (P₁.coconePointsIsoOfNatIso P₂ α).isIso_hom
  exact IsIso.of_isIso_comp_left (eqToHom hpt) g

/-- **The chain-level Thom map is a quasi-isomorphism with `K`-coefficients**: for any Thom class
`u ∈ Hʳ(E, E₀; K)` of a finite-dimensional real vector bundle over an arbitrary base, and any
relative cocycle `φ` representing `u`, the chain map
`thomCapChainMap F E (ModuleCat.of K K) r φ : C(E, E₀; K) ⟶ C(B; K)[r]` is a quasi-isomorphism. -/
theorem IsThomClass.quasiIso_thomCapChainMap
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
      (ModuleCat.of K K)).cycles (finrank ℝ F))
    (hφ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K
      (ModuleCat.of K K)).homologyπ (finrank ℝ F) φ = u) :
    QuasiIso (thomCapChainMap F E (ModuleCat.of K K) (finrank ℝ F) φ) := by
  have := (isThomClass_iff.1 hu).1
  rw [quasiIso_iff]
  intro m
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hm : finrank ℝ F ≤ m
  · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hcomp := homologyMap_thomCapChainMap_comp_extendHomologyIso_hom F E (ModuleCat.of K K)
      (p := p) rfl φ
    rw [hφ] at hcomp
    have hiso : IsIso (HomologicalComplex.homologyMap
        (thomCapChainMap F E (ModuleCat.of K K) (finrank ℝ F) φ) (finrank ℝ F + p) ≫
      (((TopCat.toSSet.obj (TopCat.of B)).chainComplex (ModuleCat.of K K)).extendHomologyIso
        (ComplexShape.embeddingDownNatAdd (finrank ℝ F)) (j := p) (by simp; omega)).hom) := by
      rw [hcomp]
      exact (isIso_neg_one_pow_zsmul_iff _ (finrank ℝ F * p)).2 (isIso_homologyThomMap_self hu p)
    exact (isIso_comp_right_iff _ _).1 hiso
  · have hlt : m < finrank ℝ F := Nat.lt_of_not_ge hm
    have hsrc : IsZero ((thomPair F E).singularHomology (ModuleCat.of K K) m) :=
      isZero_singularHomology_thomPair (ModuleCat.of K K) hlt
    have htgt : IsZero ((((TopCat.toSSet.obj (TopCat.of B)).chainComplex
        (ModuleCat.of K K)).extend (ComplexShape.embeddingDownNatAdd (finrank ℝ F))).homology m) :=
      (HomologicalComplex.exactAt_iff_isZero_homology _ m).1
        (HomologicalComplex.extend_exactAt _ (ComplexShape.embeddingDownNatAdd (finrank ℝ F)) m
          (by simp; omega))
    exact IsZero.isIso hsrc htgt _

/-- **The Thom isomorphism in singular cohomology** (Milnor and Stasheff, Theorem 10.4; Hatcher,
Theorem 4D.10). Let `E → B` be a finite-dimensional real vector bundle of any rank `r ≥ 0` over an
arbitrary topological space `B`, and let `u ∈ Hʳ(E, E₀; K)` be a Thom class with coefficients in a
commutative ring `K`. Then for every `K`-module `M` and every degree `p`, the Thom map
`Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(E, E₀; M)`, `a ↦ π^*a ⌣ u`, is bijective. -/
theorem IsThomClass.bijective_thomMap (M : ModuleCat.{w} K)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ (finrank ℝ F) u
  have := hu.quasiIso_thomCapChainMap φ rfl
  have hqi := _root_.ChainComplex.quasiIso_linearYonedaFunctor_map_of_projective
    (thomCapChainMap F E (ModuleCat.of K K) (finrank ℝ F) φ) K M
  rw [thomMap_def,
    bijective_pullbackCup_iff_isIso_homologyMap_linearYonedaFunctor_map_pairCapChainMap
      (thomPair F E) (thomPairProj F E) M h φ]
  exact (quasiIsoAt_iff_isIso_homologyMap _ m).1 ((quasiIso_iff _).1 hqi m)

/-- **The Thom isomorphism in singular cohomology**, packaged as a `K`-linear equivalence
`Hᵖ(B; M) ≃ₗ[K] Hᵖ⁺ʳ(E, E₀; M)`, `a ↦ π^*a ⌣ u`, for a real vector bundle of rank `r ≥ 0` over an
arbitrary base with Thom class `u ∈ Hʳ(E, E₀; K)`. -/
def IsThomClass.thomEquiv (M : ModuleCat.{w} K)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : p + finrank ℝ F = m) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u) (hu.bijective_thomMap M h)

@[simp]
theorem IsThomClass.thomEquiv_apply (M : ModuleCat.{w} K)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    hu.thomEquiv M h a = thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

end ArbitraryBase

end TauCeti
