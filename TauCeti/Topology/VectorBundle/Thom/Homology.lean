/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism
import TauCeti.Algebra.Homology.DerivedCategory.KProjective
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Pairing

/-!
# The Thom isomorphism in singular homology

Let `E → B` be a vector bundle with Thom pair `(E, E₀)`, `E₀` the complement of the zero section,
and let `u ∈ Hⁿ(E, E₀; K)` be a relative class with coefficients in a commutative ring `K`. The
**homology Thom map** of `u` is

`Φ_u : Hₘ(E, E₀; A) ⟶ Hₚ(B; A)`,  `x ↦ π_*(x ⌢ u)`,  `n + p = m`,

the relative cap product `Hₘ(E, E₀) ⟶ Hₚ(E)` with `u` (`TopPair.singularCap`) followed by the
push-forward along the projection `π : E ⟶ B`, for any `K`-module of coefficients `A`. When `u` is
a Thom class of a finite-dimensional real vector bundle of rank `r ≥ 0` (for instance the unique
Thom class with coefficients in `ZMod 2`, or the Thom class of an orientation), this file proves the
**Thom isomorphism in singular homology** (Spanier, Chapter 5, Section 7): `Φ_u` is an isomorphism
in every degree, for every base space `B`, every commutative ring `K`, and every `K`-module `A` of
coefficients. It is the homological counterpart of the cohomology Thom isomorphism
`TauCeti.IsThomClass.bijective_thomMap` (`a ↦ π^*a ⌣ u`, Milnor and Stasheff's Theorem 10.4).

Relative homology of Thom pairs is what attaching a disc bundle produces: when a bundle `ν` is
attached along its sphere bundle, the relative homology of the attachment is that of the Thom pair
`(ν, ν₀)`. So the homology Thom map is the map which identifies such a relative group, shifted by
the rank, with the homology of the base, as in the relative homology of a sublevel pair across a
Morse–Bott critical level.

The first part of the file sets up the map and its basic properties. It is `K`-linear in `u`
(`TauCeti.homologyThomMap`). It is natural in maps of Thom pairs covering maps of the bases
(`TauCeti.homologyThomMap_naturality`), in particular in pull-backs of bundles
(`TauCeti.homologyThomMap_pullback`), so it commutes with the restriction to open sets of the base.
On the fibre pair `(E_b, E_b ∖ {0})` over a point `b`, it is the cap product with the restriction of
`u`, pushed forward along the constant map at `b`
(`TauCeti.singularHomologyMap_fiberThomPairMap_comp_homologyThomMap`).

With coefficients in `K` itself, the homology Thom map is the transpose of the cohomology Thom map
`TauCeti.thomMap` under the Kronecker pairing, up to a sign:
`⟨a, Φ_u(x)⟩ = (-1)^(n p) ⟨π^*a ⌣ u, x⟩` for `a ∈ Hᵖ(B; K)` and `x ∈ Hₘ(E, E₀; K)`
(`TauCeti.homologyThomMap_comp_singularKronecker`). The cap product with `u` is adjoint to the cup
product `u ⌣ π^*a` with `u` on the left, and graded commutativity of the cup product of relative
and absolute classes (`TopPair.singularCup_gradedComm`) moves `u` to the right, where the Thom map
has it. Over a field the Kronecker pairing identifies cohomology with the dual of homology, so the
homology Thom map is bijective in a degree exactly when the Thom map is bijective in the
corresponding degree (`TauCeti.bijective_homologyThomMap_iff`).

For a general commutative ring `K` and an arbitrary `K`-module `A`, we deduce the homology Thom
isomorphism from the chain-level quasi-isomorphism `TauCeti.IsThomClass.quasiIso_thomCapChainMap`.
Picking a relative cocycle `φ` representing `u`, the chain map
`thomCapChainMap F E (ModuleCat.of K K) r φ : C(E, E₀; K) ⟶ C(B; K)[r]` is a quasi-isomorphism
between degreewise projective `ℕ`-graded chain complexes, hence a chain homotopy equivalence
(`ChainComplex.quasiIso_iff_of_projective`). The additive functor `A ⊗ -` carries it to a chain
homotopy equivalence (hence a quasi-isomorphism), which is identified with
`thomCapChainMap F E A r φ : C(E, E₀; A) ⟶ C(B; A)[r]` via the coefficient-pairing isomorphisms
`A ⊗ C(E, E₀; K) ≅ C(E, E₀; A)` (`SSetPair.isIso_chainComplexPairing`) and
`A ⊗ C(B; K)[r] ≅ C(B; A)[r]` (`SSet.isIso_chainComplexPairing`). Taking homology yields
`TauCeti.IsThomClass.isIso_homologyThomMap`, `TauCeti.IsThomClass.bijective_homologyThomMap`, and
`TauCeti.IsThomClass.homologyThomIso`.

## Main definitions and results

* `TauCeti.homologyThomMap`: the homology Thom map `x ↦ π_*(x ⌢ u)`, linear in `u`.
* `TauCeti.homologyThomMap_naturality`, `TauCeti.homologyThomMap_pullback`: naturality.
* `TauCeti.singularHomologyMap_fiberThomPairMap_comp_homologyThomMap`: the restriction to a fibre.
* `TauCeti.homologyThomMap_comp_singularKronecker`: the homology Thom map is the transpose of the
  Thom map, up to the sign `(-1)^(n p)`.
* `TauCeti.bijective_homologyThomMap_iff`: over a field, the homology Thom map is bijective exactly
  when the Thom map is.
* `TauCeti.IsThomClass.isIso_homologyThomMap`, `TauCeti.IsThomClass.bijective_homologyThomMap`,
  `TauCeti.IsThomClass.homologyThomIso`: the Thom isomorphism in singular homology over an
  arbitrary base, for every commutative ring `K`, every `K`-module `A`, and every rank `r ≥ 0`.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.3, the identity
  `⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ, x⟩`.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory Module AlgebraicTopology

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (A : ModuleCat.{w} K)

/-- **The homology Thom map** `x ↦ π_*(x ⌢ u)` of a relative class `u ∈ Hⁿ(E, E₀; K)`, from
`Hₘ(E, E₀; A)` to `Hₚ(B; A)`, `n + p = m`, as a `K`-linear function of `u`. The cochain
coefficients are `K`, and both the coefficient morphism and the pairing of values are the left
unitor `K ⊗ A ≅ A`. For a Thom class `u` of a real vector bundle of rank `n` it is the map of
the Thom isomorphism in homology. -/
def homologyThomMap (n p m : ℕ) (h : n + p = m) :
    (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      ((thomPair F E).singularHomology A m ⟶
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).obj (TopCat.of B)) :=
  Linear.rightComp K _ (((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map
      (thomPairProj F E)) ∘ₗ
    (thomPair F E).singularCap K (λ_ A).inv (λ_ A).hom n p m h

variable {A}

/-- The homology Thom map is the relative cap product with `u` followed by the push-forward along
the projection. -/
theorem homologyThomMap_apply {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    homologyThomMap F E A n p m h u =
      (thomPair F E).singularCap K (λ_ A).inv (λ_ A).hom n p m h u ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map (thomPairProj F E) :=
  (rfl)

/-- **Naturality of the homology Thom map.** A map of Thom pairs `φ : (E', E'₀) ⟶ (E, E₀)` covering
a map of bases `g : B' ⟶ B` intertwines the homology Thom map of the pull-back `φ^*u` with that of
`u`: `g_* Φ_{φ^*u}(x) = Φ_u(φ_* x)`. -/
theorem homologyThomMap_naturality {B' : Type w} [TopologicalSpace B'] {F' : Type*}
    [TopologicalSpace F'] {E' : B' → Type w} [TopologicalSpace (TotalSpace F' E')]
    [∀ b, Zero (E' b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E']
    (φ : thomPair F' E' ⟶ thomPair F E) (g : TopCat.of B' ⟶ TopCat.of B)
    (hφ : TopPair.Hom.fst φ ≫ thomPairProj F E = thomPairProj F' E' ≫ g) {n p m : ℕ}
    (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    homologyThomMap F' E' A n p m h (TopPair.singularCohomologyMap φ n u) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map g =
      TopPair.singularHomologyMap φ A m ≫ homologyThomMap F E A n p m h u := by
  rw [homologyThomMap_apply, homologyThomMap_apply, Category.assoc, ← Functor.map_comp, ← hφ,
    Functor.map_comp, ← Category.assoc, TopPair.singularCap_naturality, Category.assoc]

attribute [local instance] pullbackFiberZero in
/-- **The homology Thom map of a pull-back bundle.** For a continuous map `f : B' ⟶ B`, pushing
the homology Thom map of the pull-back of `u` to `f^*E` forward along `f` is the homology Thom map
of `u` on the push-forward to the Thom pair of `E`. -/
theorem homologyThomMap_pullback {B' : Type w} [TopologicalSpace B'] (f : C(B', B)) {n p m : ℕ}
    (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    homologyThomMap F ((⇑f) *ᵖ E) A n p m h
          (TopPair.singularCohomologyMap (pullbackThomPairMap F E f) n u) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map (TopCat.ofHom f) =
      TopPair.singularHomologyMap (pullbackThomPairMap F E f) A m ≫
        homologyThomMap F E A n p m h u :=
  homologyThomMap_naturality F E _ _ (pullbackThomPairMap_fst_comp_thomPairProj F E f) h u

/-- **The homology Thom map on a fibre.** On the image of the fibre pair `(E_b, E_b ∖ {0})`, the
homology Thom map of `u` is the cap product with the restriction of `u` to the fibre, pushed forward
along the constant map at `b`. -/
theorem singularHomologyMap_fiberThomPairMap_comp_homologyThomMap (b : B) {n p m : ℕ}
    (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    TopPair.singularHomologyMap (fiberThomPairMap F E b) A m ≫ homologyThomMap F E A n p m h u =
      (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularCap K (λ_ A).inv
          (λ_ A).hom n p m h (TopPair.singularCohomologyMap (fiberThomPairMap F E b) n u) ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).map
          (TopCat.ofHom (ContinuousMap.const (E b) b)) := by
  rw [homologyThomMap_apply, ← Category.assoc, ← TopPair.singularCap_naturality, Category.assoc,
    ← Functor.map_comp, fiberThomPairMap_fst_comp_thomPairProj]

/-- **The homology Thom map is the transpose of the Thom map**: for `u ∈ Hⁿ(E, E₀; K)`,
`a ∈ Hᵖ(B; K)` and `x ∈ Hₘ(E, E₀; K)`, `m = n + p`, the Kronecker pairing of `a` with the homology
Thom map `Φ_u(x) = π_*(x ⌢ u)` is `(-1)^(n p)` times the pairing of the Thom map
`π^*a ⌣ u` (`TauCeti.thomMap`) with `x`. -/
theorem homologyThomMap_comp_singularKronecker {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p) :
    homologyThomMap F E (ModuleCat.of K K) n p m h u ≫ (TopCat.of B).singularKronecker K p a =
      ((-1 : ℤ) ^ (n * p)) • (thomPair F E).singularKronecker K m
        (thomMap F E (ModuleCat.of K K) n p m (by omega) u a) := by
  -- `⟨a, π_*(x ⌢ u)⟩ = ⟨π^*a, x ⌢ u⟩ = ⟨u ⌣ π^*a, x⟩`, and `u ⌣ π^*a = (-1)^(n p) π^*a ⌣ u`.
  rw [homologyThomMap_apply, Category.assoc, ← TopCat.singularKronecker_naturality,
    TopPair.singularCap_comp_singularKronecker, thomMap_apply,
    TopPair.singularCup_gradedComm K (thomPair F E) (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u' := (λ_ (ModuleCat.of K K)).inv) (μ' := (λ_ (ModuleCat.of K K)).hom)
      (μ := (ρ_ (ModuleCat.of K K)).hom) ?_ ?_ (by omega), map_zsmul, mul_comm]
  -- `thomMap` cups along `(λ_ (𝟙_ (ModuleCat K))).inv`, while the cap product side uses
  -- `ModuleCat.of K K`; both remaining `rfl`s close the definitional equality
  -- `𝟙_ (ModuleCat K) = ModuleCat.of K K` of Mathlib's monoidal structure on `ModuleCat K`.
  · rfl
  · rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, ← unitors_inv_equal]
    rfl
  · exact braiding_leftUnitor _

/-- **Over a field, the homology Thom map is bijective exactly when the Thom map is**: for
`u ∈ Hⁿ(E, E₀; K)` and `m = n + p`, the homology Thom map `Hₘ(E, E₀; K) ⟶ Hₚ(B; K)` is bijective
if and only if the Thom map `Hᵖ(B; K) ⟶ Hᵐ(E, E₀; K)` is. Through the universal coefficient
isomorphisms `TopCat.singularCohomologyDualEquiv` and `TopPair.singularCohomologyDualEquiv`, the
Thom map is `±` the dual map of the homology Thom map
(`TauCeti.homologyThomMap_comp_singularKronecker`), and a linear map between vector spaces is
bijective exactly when its dual map is. -/
theorem bijective_homologyThomMap_iff {K : Type w} [Field K] {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) n p m h u).hom ↔
      Function.Bijective (thomMap F E (ModuleCat.of K K) n p m (by omega) u) := by
  set T := (homologyThomMap F E (ModuleCat.of K K) n p m h u).hom
  have hc : ((-1 : K) ^ (n * p)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  -- The linear form of `π^*a ⌣ u` is `(-1)^(n p)` times the dual map of `T` applied to that
  -- of `a`.
  have key : ∀ a, (thomPair F E).singularCohomologyDualEquiv m
      (thomMap F E (ModuleCat.of K K) n p m (by omega) u a) =
      LinearEquiv.smulOfNeZero K _ _ hc
        (T.dualMap ((TopCat.of B).singularCohomologyDualEquiv p a)) := by
    intro a
    ext x
    have hx := congrArg (fun φ ↦ φ.hom x) (homologyThomMap_comp_singularKronecker F E h u a)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zsmul,
      LinearMap.smul_apply] at hx
    rw [LinearEquiv.smulOfNeZero_apply, LinearMap.smul_apply, LinearMap.dualMap_apply,
      TopPair.singularCohomologyDualEquiv_apply, TopCat.singularCohomologyDualEquiv_apply, hx]
    simp [← Int.cast_smul_eq_zsmul K, ← mul_assoc, ← mul_pow]
  have e : ⇑(thomMap F E (ModuleCat.of K K) n p m (by omega) u) =
      ⇑((thomPair F E).singularCohomologyDualEquiv m).symm ∘ ⇑(LinearEquiv.smulOfNeZero K _ _ hc) ∘
        ⇑T.dualMap ∘ ⇑((TopCat.of B).singularCohomologyDualEquiv p) := by
    funext a
    simp only [Function.comp_apply, ← key, LinearEquiv.symm_apply_apply]
  rw [e, EquivLike.comp_bijective, EquivLike.comp_bijective, EquivLike.bijective_comp,
    LinearMap.dualMap_bijective_iff]

/-! ### The Thom isomorphism in singular homology -/

section HomologyIsomorphism

/-- Scalar compatibility between capping with a `K`-valued cochain on `K`-chains tensored with `A`
and capping directly on `A`-chains. -/
private theorem whiskerLeft_capCoeff_comp_rightUnitor_hom {K : Type w} [CommRing K]
    (A : ModuleCat.{w} K) (α : ModuleCat.of K K ⟶ ModuleCat.of K K) :
    (A ◁ ((λ_ (ModuleCat.of K K)).inv ≫ (α ▷ ModuleCat.of K K) ≫
        (λ_ (ModuleCat.of K K)).hom)) ≫ (ρ_ A).hom =
      (ρ_ A).hom ≫ (λ_ A).inv ≫ (α ▷ A) ≫ (λ_ A).hom := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun (a : A) (c : K) ↦ ?_
  change ((A ◁ ((λ_ (ModuleCat.of K K)).inv ≫ (α ▷ ModuleCat.of K K) ≫
      (λ_ (ModuleCat.of K K)).hom)) ≫ (ρ_ A).hom) (a ⊗ₜ[K] c) =
    ((ρ_ A).hom ≫ (λ_ A).inv ≫ (α ▷ A) ≫ (λ_ A).hom) (a ⊗ₜ[K] c)
  have h1 : (A ◁ ((λ_ (ModuleCat.of K K)).inv ≫ (α ▷ ModuleCat.of K K) ≫
      (λ_ (ModuleCat.of K K)).hom)) (a ⊗ₜ[K] c) =
      a ⊗ₜ[K] (((α (1 : K) : K) • c : K)) := by
    rw [ModuleCat.MonoidalCategory.whiskerLeft_apply]
    congr 1
  rw [ConcreteCategory.comp_apply, h1, ModuleCat.MonoidalCategory.rightUnitor_hom_apply,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_hom_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]
  exact (smul_assoc (α (1 : K) : K) c a).trans
    (ModuleCat.MonoidalCategory.leftUnitor_hom_apply (α (1 : K) : K) (c • a)).symm

/-- For a simplicial set `X`, a `K`-module `A`, and a degree shift `r`, tensoring the shifted
`K`-chain complex `C(X; K)[r]` with `A` on the left is isomorphic to `C(X; A)[r]` via the
coefficient-pairing isomorphism `X.chainComplexPairing (ρ_ A).hom`. -/
private def tensorLeftExtendChainComplexPairingIso {K : Type w} [CommRing K]
    (X : SSet.{w}) (A : ModuleCat.{w} K) (r : ℕ) :
    ((tensorLeft A).mapHomologicalComplex _).obj
        ((X.chainComplex (ModuleCat.of K K)).extend (ComplexShape.embeddingDownNatAdd r)) ≅
      (X.chainComplex A).extend (ComplexShape.embeddingDownNatAdd r) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m ↦
      if hm : r ≤ m then
        (tensorLeft A).mapIso
            ((X.chainComplex (ModuleCat.of K K)).extendXIso
              (ComplexShape.embeddingDownNatAdd r) (i := m - r) (by simp; omega)) ≪≫
          asIso ((X.chainComplexPairing (ρ_ A).hom).f (m - r)) ≪≫
          ((X.chainComplex A).extendXIso
            (ComplexShape.embeddingDownNatAdd r) (i := m - r) (by simp; omega)).symm
      else
        IsZero.iso
          ((tensorLeft A).map_isZero
            (HomologicalComplex.isZero_extend_X _ (ComplexShape.embeddingDownNatAdd r) m
              (by simp; omega)))
          (HomologicalComplex.isZero_extend_X _ (ComplexShape.embeddingDownNatAdd r) m
            (by simp; omega)))
    fun m₁ m₂ hm ↦ by
      by_cases hm₂ : r ≤ m₂
      · have hm₁ : r ≤ m₁ := by
          change m₂ + 1 = m₁ at hm
          omega
        split_ifs
        simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom,
          Functor.mapHomologicalComplex_obj_d, Category.assoc]
        rw [HomologicalComplex.extend_d_eq (X.chainComplex A)
            (ComplexShape.embeddingDownNatAdd r) (i := m₁ - r) (j := m₂ - r) (by simp; omega)
            (by simp; omega),
          HomologicalComplex.extend_d_eq (X.chainComplex (ModuleCat.of K K))
            (ComplexShape.embeddingDownNatAdd r) (i := m₁ - r) (j := m₂ - r) (by simp; omega)
            (by simp; omega),
          Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, Category.assoc, Category.assoc,
          Iso.inv_hom_id, Category.comp_id, Functor.map_comp, Category.assoc]
        have hcomm := (X.chainComplexPairing (ρ_ A).hom).comm (m₁ - r) (m₂ - r)
        dsimp only [Functor.mapHomologicalComplex_obj_d] at hcomm
        rw [reassoc_of% hcomm]
        rfl
      · exact (HomologicalComplex.isZero_extend_X _ (ComplexShape.embeddingDownNatAdd r) m₂
          (by simp; omega)).eq_of_tgt _ _

/-- Tensoring the chain-level Thom map `thomCapChainMap F E (ModuleCat.of K K) r φ` with a
`K`-module `A` on the left agrees with `thomCapChainMap F E A r φ` under the coefficient-pairing
isomorphisms on `(E, E₀)` and on `B`. -/
private theorem tensorLeft_thomCapChainMap_comp_iso
    {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
    (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    {K : Type w} [CommRing K] (A : ModuleCat.{w} K) (r : ℕ)
    (φ : ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).cycles r) :
    ((tensorLeft A).mapHomologicalComplex _).map
        (thomCapChainMap F E (ModuleCat.of K K) r φ) ≫
      (tensorLeftExtendChainComplexPairingIso (TopCat.toSSet.obj (TopCat.of B)) A r).hom =
    (TopPair.toSSetPair.obj (thomPair F E)).chainComplexPairing (ρ_ A).hom ≫
      thomCapChainMap F E A r φ := by
  ext m : 1
  by_cases hm : r ≤ m
  · have hpm : r + (m - r) = m := by omega
    dsimp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      tensorLeftExtendChainComplexPairingIso, HomologicalComplex.Hom.isoOfComponents_hom_f]
    split_ifs
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom,
      thomCapChainMap_f F E _ hpm φ, Functor.map_zsmul, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul]
    congr 1
    rw [← Functor.map_comp_assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Functor.map_comp, Category.assoc]
    let φ' : ((thomPair F E).singularChainComplex (ModuleCat.of K K)).X r ⟶ ModuleCat.of K K :=
      ((thomPair F E).singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).iCycles r φ
    change (A ◁ ChainComplex.capChain K
          ((thomPair F E).alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
          ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
          r (m - r) m hpm φ') ≫
        (A ◁ (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E))
          (ModuleCat.of K K)).f (m - r)) ≫
        ((TopCat.toSSet.obj (TopCat.of B)).chainComplexPairing (ρ_ A).hom).f (m - r) ≫
        (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendXIso
          (ComplexShape.embeddingDownNatAdd r) (by simp; omega)).inv =
      ((TopPair.toSSetPair.obj (thomPair F E)).chainComplexPairing (ρ_ A).hom).f m ≫
        ChainComplex.capChain K ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
          ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom)
          r (m - r) m hpm φ' ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) A).f (m - r) ≫
        (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendXIso
          (ComplexShape.embeddingDownNatAdd r) (by simp; omega)).inv
    have hnat :
        (A ◁ (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E))
          (ModuleCat.of K K)).f (m - r)) ≫
          ((TopCat.toSSet.obj (TopCat.of B)).chainComplexPairing (ρ_ A).hom).f (m - r) =
        ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (ρ_ A).hom).f (m - r) ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (thomPairProj F E)) A).f (m - r) :=
      congrArg (fun f ↦ f.f (m - r))
        (SSet.chainComplexPairing_naturality (TopCat.toSSet.map (thomPairProj F E)) (ρ_ A).hom)
    rw [reassoc_of% hnat]
    rw [← Category.assoc ((TopPair.toSSetPair.obj (thomPair F E)).chainComplexPairing _ |>.f m),
      ← Category.assoc (A ◁ _)]
    congr 1
    suffices ∀ σ : (TopCat.toSSet.obj (thomPair F E).fst).obj
        (Opposite.op (SimplexCategory.mk m)),
        (A ◁ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex σ) ≫
          (A ◁ ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f m) ≫
          (A ◁ ChainComplex.capChain K
            ((thomPair F E).alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
            r (m - r) m hpm φ') ≫
          ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (ρ_ A).hom).f (m - r) =
        (A ◁ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex σ) ≫
          (A ◁ ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f m) ≫
          ((TopPair.toSSetPair.obj (thomPair F E)).chainComplexPairing (ρ_ A).hom).f m ≫
          ChainComplex.capChain K ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom)
            r (m - r) m hpm φ' by
      rw [← cancel_epi (A ◁ ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f m)]
      apply (cancel_epi (((SSet.chainComplexFunctorObjCompMapIso (tensorLeft A)
        (ModuleCat.of K K)).inv.app (TopCat.toSSet.obj (thomPair F E).fst)).f m)).1
      refine SSet.chainComplex_hom_ext fun σ ↦ ?_
      have hι := SSet.ιChainComplex_chainComplexFunctorObjCompMapIso_inv_app_f
        (TopCat.toSSet.obj (thomPair F E).fst) (tensorLeft A) (ModuleCat.of K K) σ
      exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hι).trans <|
        (this σ).trans <| (congrArg (· ≫ _) hι.symm).trans (Category.assoc _ _ _)
    intro σ
    have hCapK := TopPair.ιChainComplex_singularChainComplexπ_capChain_alexanderWhitneyDiagonal
      (thomPair F E) K (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom r (m - r) m hpm
      φ' σ
    have hCapA := TopPair.ιChainComplex_singularChainComplexπ_capChain_alexanderWhitneyDiagonal
      (thomPair F E) K (λ_ A).inv (λ_ A).hom r (m - r) m hpm φ' σ
    have hPairπ :
        (A ◁ ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f m) ≫
          ((TopPair.toSSetPair.obj (thomPair F E)).chainComplexPairing (ρ_ A).hom).f m =
        ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (ρ_ A).hom).f m ≫
          ((thomPair F E).singularChainComplexπ A).f m :=
      SSetPair.whiskerLeft_chainComplexπ_f_chainComplexPairing_f
        (TopPair.toSSetPair.obj (thomPair F E)) (ρ_ A).hom m
    have hPairι :
        (A ◁ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex σ) ≫
          ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (ρ_ A).hom).f m =
        (ρ_ A).hom ≫ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex σ :=
      SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f
        (TopCat.toSSet.obj (thomPair F E).fst) (ρ_ A).hom σ
    have hPairBack :
        (A ◁ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex
            ((TopCat.toSSet.obj (thomPair F E).fst).map
              (SimplexCategory.subinterval r (m - r) (by omega)).op σ)) ≫
          ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (ρ_ A).hom).f (m - r) =
        (ρ_ A).hom ≫ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex
            ((TopCat.toSSet.obj (thomPair F E).fst).map
              (SimplexCategory.subinterval r (m - r) (by omega)).op σ) :=
      SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f
        (TopCat.toSSet.obj (thomPair F E).fst) (ρ_ A).hom _
    have hWhisker :
        (A ◁ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex σ) ≫
          (A ◁ ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f m) ≫
          (A ◁ ChainComplex.capChain K
            ((thomPair F E).alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
            r (m - r) m hpm φ') =
        A ◁ ((TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex σ ≫
          ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f m ≫
          ChainComplex.capChain K
            ((thomPair F E).alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
            r (m - r) m hpm φ') :=
      (congrArg ((A ◁ _) ≫ ·) (MonoidalCategory.whiskerLeft_comp A _ _).symm).trans
        (MonoidalCategory.whiskerLeft_comp A _ _).symm
    have hL :
        (A ◁ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex σ) ≫
          (A ◁ ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f m) ≫
          (A ◁ ChainComplex.capChain K
            ((thomPair F E).alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ (ModuleCat.of K K)).hom)
            r (m - r) m hpm φ') ≫
          ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (ρ_ A).hom).f (m - r) =
        (ρ_ A).hom ≫ (λ_ A).inv ≫
          (((TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex
              ((TopCat.toSSet.obj (thomPair F E).fst).map
                (SimplexCategory.subinterval 0 r (by omega)).op σ) ≫
              ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f r ≫ φ') ▷ A) ≫
          (λ_ A).hom ≫ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex
              ((TopCat.toSSet.obj (thomPair F E).fst).map
                (SimplexCategory.subinterval r (m - r) (by omega)).op σ) := by
      calc _ = ((A ◁ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex σ) ≫
              (A ◁ ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f m) ≫
              (A ◁ ChainComplex.capChain K
                ((thomPair F E).alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
                ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing
                  (λ_ (ModuleCat.of K K)).hom)
                r (m - r) m hpm φ')) ≫
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (ρ_ A).hom).f (m - r) := by
            simp only [Category.assoc]
        _ = (A ◁ ((TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex σ ≫
              ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f m ≫
              ChainComplex.capChain K
                ((thomPair F E).alexanderWhitneyDiagonal (λ_ (ModuleCat.of K K)).inv)
                ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing
                  (λ_ (ModuleCat.of K K)).hom)
                r (m - r) m hpm φ')) ≫
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (ρ_ A).hom).f (m - r) :=
            congrArg (· ≫ _) hWhisker
        _ = (A ◁ ((λ_ (ModuleCat.of K K)).inv ≫
              (((TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex
                  ((TopCat.toSSet.obj (thomPair F E).fst).map
                    (SimplexCategory.subinterval 0 r (by omega)).op σ) ≫
                  ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f r ≫ φ') ▷
                ModuleCat.of K K) ≫
              (λ_ (ModuleCat.of K K)).hom ≫
              (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex
                ((TopCat.toSSet.obj (thomPair F E).fst).map
                  (SimplexCategory.subinterval r (m - r) (by omega)).op σ))) ≫
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (ρ_ A).hom).f (m - r) :=
            congrArg (fun f ↦ (A ◁ f) ≫ _) hCapK
        _ = (A ◁ ((λ_ (ModuleCat.of K K)).inv ≫
              (((TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex
                  ((TopCat.toSSet.obj (thomPair F E).fst).map
                    (SimplexCategory.subinterval 0 r (by omega)).op σ) ≫
                  ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f r ≫ φ') ▷
                ModuleCat.of K K) ≫
              (λ_ (ModuleCat.of K K)).hom)) ≫
            (A ◁ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex
                ((TopCat.toSSet.obj (thomPair F E).fst).map
                  (SimplexCategory.subinterval r (m - r) (by omega)).op σ)) ≫
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (ρ_ A).hom).f (m - r) := by
            simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
        _ = ((A ◁ ((λ_ (ModuleCat.of K K)).inv ≫
              (((TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex
                  ((TopCat.toSSet.obj (thomPair F E).fst).map
                    (SimplexCategory.subinterval 0 r (by omega)).op σ) ≫
                  ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f r ≫ φ') ▷
                ModuleCat.of K K) ≫
              (λ_ (ModuleCat.of K K)).hom)) ≫ (ρ_ A).hom) ≫
            (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex
              ((TopCat.toSSet.obj (thomPair F E).fst).map
                (SimplexCategory.subinterval r (m - r) (by omega)).op σ) := by
            rw [hPairBack, Category.assoc]
        _ = _ := by
            rw [whiskerLeft_capCoeff_comp_rightUnitor_hom A]
            simp only [Category.assoc]
    have hR :
        (A ◁ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex σ) ≫
          (A ◁ ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f m) ≫
          ((TopPair.toSSetPair.obj (thomPair F E)).chainComplexPairing (ρ_ A).hom).f m ≫
          ChainComplex.capChain K ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom)
            r (m - r) m hpm φ' =
        (ρ_ A).hom ≫ (λ_ A).inv ≫
          (((TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex
              ((TopCat.toSSet.obj (thomPair F E).fst).map
                (SimplexCategory.subinterval 0 r (by omega)).op σ) ≫
              ((thomPair F E).singularChainComplexπ (ModuleCat.of K K)).f r ≫ φ') ▷ A) ≫
          (λ_ A).hom ≫ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex
              ((TopCat.toSSet.obj (thomPair F E).fst).map
                (SimplexCategory.subinterval r (m - r) (by omega)).op σ) := by
      calc _ = (A ◁ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex σ) ≫
            ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (ρ_ A).hom).f m ≫
            ((thomPair F E).singularChainComplexπ A).f m ≫
            ChainComplex.capChain K ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
              ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom)
              r (m - r) m hpm φ' :=
            congrArg ((A ◁ _) ≫ ·) ((reassoc_of% hPairπ) _)
        _ = (ρ_ A).hom ≫ (TopCat.toSSet.obj (thomPair F E).fst).ιChainComplex σ ≫
            ((thomPair F E).singularChainComplexπ A).f m ≫
            ChainComplex.capChain K ((thomPair F E).alexanderWhitneyDiagonal (λ_ A).inv)
              ((TopCat.toSSet.obj (thomPair F E).fst).chainComplexPairing (λ_ A).hom)
              r (m - r) m hpm φ' := (reassoc_of% hPairι) _
        _ = _ := congrArg ((ρ_ A).hom ≫ ·) hCapA
    exact hL.trans hR.symm
  · exact (HomologicalComplex.isZero_extend_X _ (ComplexShape.embeddingDownNatAdd r) m
      (by simp; omega)).eq_of_tgt _ _

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K]

/-- **The Thom isomorphism in singular homology** (Spanier, Chapter 5, Section 7): for a
finite-dimensional real vector bundle `E → B` of any rank `r ≥ 0` over an arbitrary topological
space `B`, a Thom class `u ∈ Hʳ(E, E₀; K)` with coefficients in a commutative ring `K`, and any
`K`-module `A` of coefficients, the homology Thom map `Hₘ(E, E₀; A) ⟶ Hₚ(B; A)` (`r + p = m`),
`x ↦ π_*(x ⌢ u)`, is an isomorphism in `ModuleCat K`. -/
theorem IsThomClass.isIso_homologyThomMap (A : ModuleCat.{w} K)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : finrank ℝ F + p = m) :
    IsIso (homologyThomMap F E A (finrank ℝ F) p m h u) := by
  obtain ⟨φ, hφ⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ (finrank ℝ F) u
  have hqiK : QuasiIso (thomCapChainMap F E (ModuleCat.of K K) (finrank ℝ F) φ) :=
    hu.quasiIso_thomCapChainMap φ hφ
  have hqiTensor : QuasiIso (((tensorLeft A).mapHomologicalComplex _).map
      (thomCapChainMap F E (ModuleCat.of K K) (finrank ℝ F) φ)) :=
    homotopyEquivalences_le_quasiIso _ _ _
      ((tensorLeft A).homotopyEquivalences_mapHomologicalComplex_map _
        ((_root_.ChainComplex.quasiIso_iff_of_projective _).1 hqiK))
  have hsq := congrArg (fun f ↦ HomologicalComplex.homologyMap f m)
    (tensorLeft_thomCapChainMap_comp_iso F E A (finrank ℝ F) φ)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
  have hIsoTensor : IsIso (HomologicalComplex.homologyMap
      (((tensorLeft A).mapHomologicalComplex _).map
        (thomCapChainMap F E (ModuleCat.of K K) (finrank ℝ F) φ)) m) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 ((quasiIso_iff _).1 hqiTensor m)
  have hIsoTau : IsIso (HomologicalComplex.homologyMap
      (tensorLeftExtendChainComplexPairingIso (TopCat.toSSet.obj (TopCat.of B)) A
        (finrank ℝ F)).hom m) :=
    ((HomologicalComplex.homologyFunctor _ _ m).mapIso
      (tensorLeftExtendChainComplexPairingIso (TopCat.toSSet.obj (TopCat.of B)) A
        (finrank ℝ F))).isIso_hom
  have hIsoPair : IsIso (HomologicalComplex.homologyMap
      ((TopPair.toSSetPair.obj (thomPair F E)).chainComplexPairing (ρ_ A).hom) m) :=
    ((HomologicalComplex.homologyFunctor _ _ m).mapIso
      (asIso ((TopPair.toSSetPair.obj (thomPair F E)).chainComplexPairing (ρ_ A).hom))).isIso_hom
  have hIsoCap : IsIso (HomologicalComplex.homologyMap
      (thomCapChainMap F E A (finrank ℝ F) φ) m) :=
    IsIso.of_isIso_fac_left (hh := (inferInstance : IsIso (_ ≫ _))) hsq.symm
  have hcomp := homologyMap_thomCapChainMap_comp_extendHomologyIso_hom F E A h φ
  rw [hφ] at hcomp
  have hcompIso : IsIso (HomologicalComplex.homologyMap
        (thomCapChainMap F E A (finrank ℝ F) φ) m ≫
      (((TopCat.toSSet.obj (TopCat.of B)).chainComplex A).extendHomologyIso
        (ComplexShape.embeddingDownNatAdd (finrank ℝ F)) (j := p) (by simp; omega)).hom) :=
    inferInstance
  rw [hcomp] at hcompIso
  rcases neg_one_pow_eq_or ℤ (finrank ℝ F * p) with hsign | hsign
  · rwa [hsign, one_zsmul] at hcompIso
  · rw [hsign, neg_one_zsmul] at hcompIso
    have : IsIso (-homologyThomMap F E A (finrank ℝ F) p m h u) := hcompIso
    exact ⟨⟨-inv (-homologyThomMap F E A (finrank ℝ F) p m h u),
      by rw [Preadditive.comp_neg, ← Preadditive.neg_comp, IsIso.hom_inv_id],
      by rw [Preadditive.neg_comp, ← Preadditive.comp_neg, IsIso.inv_hom_id]⟩⟩

/-- **The Thom isomorphism in singular homology**: the homology Thom map `Hₘ(E, E₀; A) ⟶ Hₚ(B; A)`
(`r + p = m`), `x ↦ π_*(x ⌢ u)`, is bijective for every `K`-module `A` and every rank `r ≥ 0`. -/
theorem IsThomClass.bijective_homologyThomMap (A : ModuleCat.{w} K)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective (homologyThomMap F E A (finrank ℝ F) p m h u).hom :=
  (ConcreteCategory.isIso_iff_bijective _).1 (hu.isIso_homologyThomMap A h)

/-- **The Thom isomorphism in singular homology**, packaged as an isomorphism
`Hₘ(E, E₀; A) ≅ Hₚ(B; A)` (`r + p = m`) in `ModuleCat K`, for a finite-dimensional real vector
bundle of rank `r ≥ 0` over an arbitrary base with Thom class `u ∈ Hʳ(E, E₀; K)`. -/
def IsThomClass.homologyThomIso (A : ModuleCat.{w} K)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : finrank ℝ F + p = m) :
    (thomPair F E).singularHomology A m ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj A).obj (TopCat.of B) :=
  @asIso _ _ _ _ (homologyThomMap F E A (finrank ℝ F) p m h u) (hu.isIso_homologyThomMap A h)

@[simp]
theorem IsThomClass.homologyThomIso_hom (A : ModuleCat.{w} K)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : finrank ℝ F + p = m) :
    (hu.homologyThomIso A h).hom = homologyThomMap F E A (finrank ℝ F) p m h u :=
  (rfl)

end HomologyIsomorphism

end TauCeti
