/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Singular.ProdThomPair
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic
import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere

/-!
# The Thom isomorphism for product bundles

Let `B` be a topological space, `F` a finite-dimensional real normed space of dimension `r`, `K` a
commutative ring, and `M` a `K`-module. For a relative class `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` on
the Thom pair `TauCeti.prodThomPair` of the product bundle `B × F → B`, this file proves that the
Thom map

`Hᵖ(B; M) ⟶ Hᵐ(B × F, B × (F ∖ {0}); M)`,  `a ↦ π^* a ⌣ u`,  `p + r = m`,

(`TopPair.pullbackCup` along `TauCeti.prodThomPairProj`) is bijective whenever the restriction of
`u` to every fibre pair `(F, F ∖ {0})` generates `Hʳ(F, F ∖ {0}; K)`
(`TauCeti.bijective_pullbackCup_prodThomPair`), giving a `K`-linear equivalence
`TauCeti.prodThomPairPullbackCupEquiv`. This is the local input over trivializing open sets for the
Mayer–Vietoris proof of the Thom isomorphism of a vector bundle.

The proof treats a model class pulled back from `(F, F ∖ {0})` first, in the three cases `r = 0`,
`r = 1`, and `r = d + 2`, and then passes to an arbitrary fibrewise-generating class `u`:

* For `r = 0`, `B × (F ∖ {0})` is empty, so the map `H*(B × F, ∅) ⟶ H*(B × F)` is an isomorphism
  (`TopPair.isIso_singularCohomologyπ_of_isEmpty`) and intertwines cup product with the lift of
  `1 ∈ H⁰(B × F; K)` with the identity, while `π : B × F → B` is a homotopy equivalence.
* For `r = 1`, `B × (F ∖ {0})` deforms fibrewise onto the disjoint union of two sections `B ⊔ B`,
  splitting `Hⁿ(B × (F ∖ {0}); M)` as `π₀^* b + σ ⌣ π₀^* c` for the indicator class `σ` of one
  half-line (`TauCeti.isLimitFanSingularCohomology`). In the long exact sequence of the pair, `δ`
  carries `c ↦ δ (σ ⌣ π₀^* c)` bijectively onto `Hⁿ⁺¹(B × F, B × (F ∖ {0}); M)`.
* For `r = d + 2`, `TauCeti.prodThomPairSingularCohomologySphereEquiv` already shows that
  `c ↦ δ (σ ⌣ π₀^* c)` is a linear equivalence for `σ = TauCeti.prodThomPairPuncturedClass`.
* In both positive-rank cases, graded commutativity (`TopCat.singularCup_gradedComm`) and
  `H*(B × F)`-linearity of the connecting morphism (`TopPair.singularCohomologyδ_singularCup`)
  identify `δ (σ ⌣ π₀^* c)` up to sign with `π^* c ⌣ δ σ`.
* Finally, if `u₀` is the model class and `u` is any class whose fibre restrictions generate
  `Hʳ(F, F ∖ {0}; K)`, surjectivity for `u₀` in base degree `0` writes `u = π^* f ⌣ u₀` with
  `f ∈ H⁰(B; K)`. Restricting to each fibre `b ∈ B` multiplies the fibre generator by the value of
  `f` at `b` (`TauCeti.singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul`), which is
  therefore a unit in `K` (`TauCeti.singularCohomologyComplSingletonFinrankEquivSelf`). Hence `f`
  is a cup-product unit in `H⁰(B; K)` (`TauCeti.exists_singularCup_eq_one`), and associativity
  (`TopPair.singularCup_assoc`) expresses the map of `u` as composition of the map of `u₀` with
  cup multiplication by `f`.

## Main definitions and results

* `TauCeti.bijective_pullbackCup_prodThomPair`: `a ↦ π^* a ⌣ u` is bijective in every degree when
  `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` generates `Hʳ(F, F ∖ {0}; K)` on every fibre.
* `TauCeti.prodThomPairPullbackCupEquiv`: the resulting `K`-linear equivalence
  `Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)` for `p + finrank ℝ F = m`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.2 and Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Module

universe w

namespace TauCeti

namespace ProdThomPairPullbackCup

/-! ### Connecting morphism and `TopPair.pullbackCup` -/

section ConnectingSign

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- Graded commutativity and `TopPair.singularCohomologyδ_singularCup` identify
`δ (σ ⌣ (i ≫ g)^* c)` up to the Koszul sign `(-1)^(p * q + p)` with `g^* c ⌣ δ σ`. -/
private theorem singularCohomologyδ_singularCup_eq_zsmul_pullbackCup
    (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z)
    {q r p qp m : ℕ} (hqp : q + p = qp) (hr : q + 1 = r) (hm : qp + 1 = m) (h : p + r = m)
    (σ : P.snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) q)
    (c : Z.singularCohomology (ModuleCat.of K K) K M p) :
    P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M qp m hm
        (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom q p qp hqp σ
          (TopCat.singularCohomologyMap (P.map ≫ g) p c)) =
      ((-1 : ℤ) ^ (p * q + p)) •
        P.pullbackCup M g r p m h
          (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) q r hr σ) c := by
  subst hqp hr hm
  have hu : (λ_ (𝟙_ (ModuleCat.{w} K))).inv ≫
      (β_ (𝟙_ (ModuleCat.{w} K)) (𝟙_ (ModuleCat.{w} K))).hom =
      (λ_ (𝟙_ (ModuleCat.{w} K))).inv := by
    rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal]
  have hμ : (β_ M (𝟙_ (ModuleCat.{w} K))).hom ≫ (λ_ M).hom = (ρ_ M).hom := by
    rw [braiding_tensorUnit_right, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hcomm := P.snd.singularCup_gradedComm K hu hμ (add_comm p q)
    (TopCat.singularCohomologyMap P.map p (TopCat.singularCohomologyMap g p c)) σ
  have hcup : P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom q p (q + p) rfl σ
        (TopCat.singularCohomologyMap (P.map ≫ g) p c) =
      ((-1 : ℤ) ^ (p * q)) •
        P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p q (q + p)
          (add_comm p q)
          (TopCat.singularCohomologyMap P.map p (TopCat.singularCohomologyMap g p c)) σ := by
    rw [TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]
    exact hcomm
  rw [hcup, map_zsmul, P.singularCohomologyδ_singularCup K
    (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom (add_comm p q) rfl rfl h
    (TopCat.singularCohomologyMap g p c) σ, smul_smul, ← pow_add, TopPair.pullbackCup_apply]

/-- Since `(-1)^(p * q + p)` is a unit in `ℤ`, `TopPair.pullbackCup` for `δ σ` is bijective
whenever `c ↦ δ (σ ⌣ (i ≫ g)^* c)` is bijective. -/
private theorem bijective_pullbackCup_singularCohomologyδ_of_bijective
    (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z)
    {q r p qp m : ℕ} (hqp : q + p = qp) (hr : q + 1 = r) (hm : qp + 1 = m) (h : p + r = m)
    (σ : P.snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) q)
    (hbij : Function.Bijective
      (fun c : Z.singularCohomology (ModuleCat.of K K) K M p ↦
        P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M qp m hm
          (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom q p qp hqp σ
            (TopCat.singularCohomologyMap (P.map ≫ g) p c)))) :
    Function.Bijective
      (P.pullbackCup M g r p m h
        (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) q r hr σ)) := by
  let ε : ℤˣ := IsUnit.unit (isUnit_neg_one.pow (p * q + p))
  have hε : Function.Bijective
      (fun y : P.singularCohomology (ModuleCat.of K K) K M m ↦ (ε : ℤ) • y) :=
    MulAction.bijective ε
  have hcomp : (fun y ↦ (ε : ℤ) • y) ∘
        ⇑(P.pullbackCup M g r p m h
          (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) q r hr σ)) =
      fun c ↦ P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M qp m hm
        (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom q p qp hqp σ
          (TopCat.singularCohomologyMap (P.map ≫ g) p c)) := by
    funext c
    exact (singularCohomologyδ_singularCup_eq_zsmul_pullbackCup M P g hqp hr hm h σ c).symm
  exact (Function.Bijective.of_comp_iff' hε _).1 (hcomp ▸ hbij)

end ConnectingSign

/-! ### Rank `0` (`Subsingleton F`) -/

section RankZero

variable {K : Type w} [CommRing K]

/-- When `F` is a subsingleton, `B × (F ∖ {0})` is empty. -/
private lemma isEmpty_prodThomPair_snd (B : Type w) [TopologicalSpace B]
    (F : Type w) [TopologicalSpace F] [Zero F] [Subsingleton F] :
    IsEmpty (prodThomPair B F).snd :=
  ⟨fun p ↦ p.2 (Subsingleton.elim p.1.2 0)⟩

/-- In rank `0`, the model class on `(B × F, ∅)` is the lift across `H⁰(B × F, ∅) ≅ H⁰(B × F)` of
the cup-product unit `1 ∈ H⁰(B × F; K)`. -/
private def rankZeroClass (K : Type w) [CommRing K] (B : Type w) [TopologicalSpace B]
    (F : Type w) [TopologicalSpace F] [Zero F] [Subsingleton F] :
    (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 :=
  have := isEmpty_prodThomPair_snd B F
  inv ((prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (prodThomPair B F).fst.singularCohomologyZeroOne

private lemma singularCohomologyπ_rankZeroClass (B : Type w) [TopologicalSpace B]
    (F : Type w) [TopologicalSpace F] [Zero F] [Subsingleton F] :
    (prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0
        (rankZeroClass K B F) =
      (prodThomPair B F).fst.singularCohomologyZeroOne := by
  have := isEmpty_prodThomPair_snd B F
  rw [rankZeroClass, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

/-- The rank-`0` model class is natural in continuous maps of the base. -/
private lemma singularCohomologyMap_prodThomPairMap_rankZeroClass
    {B B' : Type w} [TopologicalSpace B] [TopologicalSpace B'] (g : C(B, B'))
    (F : Type w) [TopologicalSpace F] [Zero F] [Subsingleton F] :
    TopPair.singularCohomologyMap (prodThomPairMap F g) 0 (rankZeroClass K B' F) =
      rankZeroClass K B F := by
  have := isEmpty_prodThomPair_snd B F
  apply (ModuleCat.mono_iff_injective
    ((prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K
      (𝟙_ (ModuleCat.{w} K)) 0)).1 inferInstance
  rw [← ConcreteCategory.comp_apply, ← TopPair.singularCohomologyπ_naturality,
    ConcreteCategory.comp_apply, singularCohomologyπ_rankZeroClass,
    singularCohomologyπ_rankZeroClass, singularCohomologyMap_singularCohomologyZeroOne]

/-- In rank `0`, `TopPair.pullbackCup` for `rankZeroClass` is bijective in every degree: composed
with the isomorphism `Hᵖ(B × F, ∅; M) ⟶ Hᵖ(B × F; M)` it is `π^*`, and `F` is contractible. -/
private theorem bijective_pullbackCup_rankZeroClass (M : ModuleCat.{w} K)
    (B : Type w) [TopologicalSpace B] (F : Type w) [TopologicalSpace F] [Zero F] [Subsingleton F]
    {p m : ℕ} (h : p + 0 = m) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p m h (rankZeroClass K B F)) := by
  subst h
  have := isEmpty_prodThomPair_snd B F
  have : Unique F := ⟨⟨0⟩, fun x ↦ Subsingleton.elim x 0⟩
  have hprojIso : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      (prodThomPairProj B F) p) := by
    have hfst := (ContinuousMap.HomotopyEquiv.prodContractible B F).isIso_singularCohomologyMap
      (𝟙_ (ModuleCat.{w} K)) K M p
    rw [ContinuousMap.HomotopyEquiv.prodContractible_toFun] at hfst
    have heq : TopCat.ofHom ContinuousMap.fst = prodThomPairProj B F :=
      TopCat.ext fun q ↦ (prodThomPairProj_apply F q).symm
    exact heq ▸ hfst
  have hπ : Function.Bijective
      ((prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p) :=
    (asIso ((prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M
      p)).toLinearEquiv.bijective
  have hproj : Function.Bijective
      (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (prodThomPairProj B F) p) :=
    (asIso (TopCat.singularCohomologyMap (prodThomPairProj B F) p)).toLinearEquiv.bijective
  have hcomp : ⇑((prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p) ∘
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p p (Nat.add_zero p)
        (rankZeroClass K B F)) =
      ⇑(TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (prodThomPairProj B F) p) := by
    funext a
    rw [Function.comp_apply, TopPair.pullbackCup_apply, TopPair.singularCohomologyπ_singularCup,
      singularCohomologyπ_rankZeroClass, TopCat.singularCohomologyZeroOne_def]
    refine (prodThomPair B F).fst.singularCup_constSingularCocycle_right K (η := 𝟙 _)
      ?_ ?_ (Nat.add_zero p)
      (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (prodThomPairProj B F) p a) <;>
      monoidal
  exact (Function.Bijective.of_comp_iff' hπ _).1 (hcomp ▸ hproj)

end RankZero

/-! ### Rank `1` (`e : F ≃L[ℝ] ℝ`) -/

section RankOne

/-- Two copies of `B`, indexed by `ULift.{w} Bool` so the index lives in `Type w`. -/
private abbrev twoCopies (B : Type w) [TopologicalSpace B] : ULift.{w} Bool → TopCat.{w} :=
  fun _ ↦ TopCat.of B

/-- Binary product universal property of a `Fan` indexed by `ULift.{w} Bool` in `ModuleCat.{w} K`:
any limit cone has bijective pair of projections `(proj ⟨true⟩, proj ⟨false⟩)`. -/
private theorem bijective_fanBool {K : Type w} [CommRing K]
    {A : ULift.{w} Bool → ModuleCat.{w} K} {P : ModuleCat.{w} K}
    {proj : ∀ i, P ⟶ A i} (hL : IsLimit (Fan.mk P proj)) :
    Function.Bijective ((proj ⟨true⟩).hom.prod (proj ⟨false⟩).hom) := by
  let Q : ModuleCat.{w} K := ModuleCat.of K (A ⟨true⟩ × A ⟨false⟩)
  let πQ : ∀ i : ULift.{w} Bool, Q ⟶ A i := fun i ↦
    match i with
    | ⟨true⟩ => ModuleCat.ofHom (LinearMap.fst K (A ⟨true⟩) (A ⟨false⟩))
    | ⟨false⟩ => ModuleCat.ofHom (LinearMap.snd K (A ⟨true⟩) (A ⟨false⟩))
  let invMor : Q ⟶ P := hL.lift (Fan.mk Q πQ)
  let toMor : P ⟶ Q := ModuleCat.ofHom ((proj ⟨true⟩).hom.prod (proj ⟨false⟩).hom)
  have htrue : invMor ≫ proj ⟨true⟩ =
      ModuleCat.ofHom (LinearMap.fst K (A ⟨true⟩) (A ⟨false⟩)) :=
    hL.fac (Fan.mk Q πQ) ⟨⟨true⟩⟩
  have hfalse : invMor ≫ proj ⟨false⟩ =
      ModuleCat.ofHom (LinearMap.snd K (A ⟨true⟩) (A ⟨false⟩)) :=
    hL.fac (Fan.mk Q πQ) ⟨⟨false⟩⟩
  have hleft : toMor ≫ invMor = 𝟙 P := by
    refine hL.hom_ext fun ⟨⟨b⟩⟩ ↦ ?_
    cases b
    · rw [Fan.mk_π_app, Category.assoc, hfalse, Category.id_comp]
      rfl
    · rw [Fan.mk_π_app, Category.assoc, htrue, Category.id_comp]
      rfl
  refine ⟨Function.LeftInverse.injective (g := invMor) fun x ↦ ConcreteCategory.congr_hom hleft x,
    Function.RightInverse.surjective (g := invMor) fun ab ↦ Prod.ext ?_ ?_⟩
  · exact (ConcreteCategory.comp_apply invMor (proj ⟨true⟩) ab).symm.trans
      (ConcreteCategory.congr_hom htrue ab)
  · exact (ConcreteCategory.comp_apply invMor (proj ⟨false⟩) ab).symm.trans
      (ConcreteCategory.congr_hom hfalse ab)

section Geometry

variable {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Chosen nonzero vector `± e⁻¹ 1` in the positive or negative half-line of `F`. -/
private def rankOneVec (e : F ≃L[ℝ] ℝ) (b : Bool) : F :=
  if b then e.symm 1 else -e.symm 1

private lemma rankOneVec_ne_zero (e : F ≃L[ℝ] ℝ) (b : Bool) : rankOneVec e b ≠ 0 := by
  cases b <;> simp [rankOneVec]

@[simp]
private lemma apply_rankOneVec_true (e : F ≃L[ℝ] ℝ) : e (rankOneVec e true) = 1 := by
  simp [rankOneVec]

@[simp]
private lemma apply_rankOneVec_false (e : F ≃L[ℝ] ℝ) : e (rankOneVec e false) = -1 := by
  simp [rankOneVec]

/-- Inclusion `(b, ± e⁻¹ 1)` of `B ⊔ B` into `B × (F ∖ {0})`. -/
private def rankOneSigmaToSnd (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ) :
    TopCat.of (Σ i, twoCopies B i) ⟶ (prodThomPair B F).snd :=
  TopCat.ofHom
    { toFun q := ⟨(q.2, rankOneVec e q.1.down), rankOneVec_ne_zero e q.1.down⟩
      continuous_toFun := continuous_sigma_iff.2 fun _ ↦ by fun_prop }

@[simp]
private lemma rankOneSigmaToSnd_apply (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ)
    (q : Σ i, twoCopies B i) :
    rankOneSigmaToSnd B e q = ⟨(q.2, rankOneVec e q.1.down), rankOneVec_ne_zero e q.1.down⟩ :=
  (rfl)

/-- Projection `(b, y) ↦ (sign(e y), b)` from `B × (F ∖ {0})` to `B ⊔ B`: continuous because the
two open half-spaces `0 < e y` and `e y < 0` cover `B × (F ∖ {0})`. -/
private def rankOneSndToSigma (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ) :
    (prodThomPair B F).snd ⟶ TopCat.of (Σ i, twoCopies B i) :=
  TopCat.ofHom
    { toFun p := ⟨if 0 < e p.1.2 then ULift.up.{w, 0} true else ULift.up.{w, 0} false, p.1.1⟩
      continuous_toFun := by
        let Upos : Set (prodThomPair B F).snd := {p | 0 < e p.1.2}
        let Uneg : Set (prodThomPair B F).snd := {p | e p.1.2 < 0}
        have hUpos : IsOpen Upos := isOpen_lt continuous_const
          (e.continuous.comp (continuous_snd.comp continuous_subtype_val))
        have hUneg : IsOpen Uneg := isOpen_lt
          (e.continuous.comp (continuous_snd.comp continuous_subtype_val)) continuous_const
        have hcov : Upos ∪ Uneg = Set.univ := by
          refine Set.eq_univ_of_forall fun p ↦ ?_
          have hne : e p.1.2 ≠ 0 := (map_ne_zero_iff e e.injective).2 p.2
          exact (lt_or_gt_of_ne hne).symm
        refine continuousOn_univ.1 (hcov ▸ ContinuousOn.union_of_isOpen ?_ ?_ hUpos hUneg)
        · refine ContinuousOn.congr (f := fun p : (prodThomPair B F).snd ↦
            (⟨ULift.up.{w, 0} true, p.1.1⟩ : Σ i, twoCopies B i)) ?_ fun p hp ↦ ?_
          · exact ((ContinuousMap.sigmaMk (X := fun i ↦ (twoCopies B i : Type w))
              (ULift.up.{w, 0} true)).continuous.comp
              (continuous_fst.comp continuous_subtype_val)).continuousOn
          · have hp' : 0 < e p.1.2 := hp
            dsimp only
            rw [ite_eq_left hp']
        · refine ContinuousOn.congr (f := fun p : (prodThomPair B F).snd ↦
            (⟨ULift.up.{w, 0} false, p.1.1⟩ : Σ i, twoCopies B i)) ?_ fun p hp ↦ ?_
          · exact ((ContinuousMap.sigmaMk (X := fun i ↦ (twoCopies B i : Type w))
              (ULift.up.{w, 0} false)).continuous.comp
              (continuous_fst.comp continuous_subtype_val)).continuousOn
          · have hp' : e p.1.2 < 0 := hp
            dsimp only
            rw [ite_eq_right (not_lt_of_gt hp')] }

@[simp]
private lemma rankOneSndToSigma_apply (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ)
    (p : (prodThomPair B F).snd) :
    rankOneSndToSigma B e p =
      ⟨if 0 < e p.1.2 then ULift.up.{w, 0} true else ULift.up.{w, 0} false, p.1.1⟩ :=
  (rfl)

private lemma rankOneSigmaToSnd_comp_rankOneSndToSigma (B : Type w) [TopologicalSpace B]
    (e : F ≃L[ℝ] ℝ) :
    rankOneSigmaToSnd B e ≫ rankOneSndToSigma B e = 𝟙 _ := by
  apply TopCat.ext
  rintro ⟨⟨b⟩, x⟩
  rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply, rankOneSndToSigma_apply,
    rankOneSigmaToSnd_apply]
  cases b
  · dsimp only
    rw [apply_rankOneVec_false e, ite_eq_right (by norm_num : ¬ (0 : ℝ) < -1)]
  · dsimp only
    rw [apply_rankOneVec_true e, ite_eq_left (zero_lt_one : (0 : ℝ) < 1)]

/-- Fibrewise straight-line homotopy equivalence `(prodThomPair B F).snd ≃ₕ B ⊔ B` in rank `1`. -/
private def rankOnePuncturedHomotopyEquiv (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ) :
    ContinuousMap.HomotopyEquiv (prodThomPair B F).snd (TopCat.of (Σ i, twoCopies B i)) where
  toFun := (rankOneSndToSigma B e).hom
  invFun := (rankOneSigmaToSnd B e).hom
  left_inv :=
    ⟨({ toFun tp :=
          ⟨(tp.2.1.1, (1 - (tp.1 : ℝ)) • tp.2.1.2 +
              (tp.1 : ℝ) • (rankOneSigmaToSnd B e (rankOneSndToSigma B e tp.2)).1.2), by
            intro hzero
            have he0 : (1 - (tp.1 : ℝ)) * e tp.2.1.2 +
                (tp.1 : ℝ) * e (rankOneSigmaToSnd B e (rankOneSndToSigma B e tp.2)).1.2 = 0 := by
              simpa [map_add, map_smul] using congrArg e hzero
            have ht0 : (0 : ℝ) ≤ tp.1 := tp.1.2.1
            have ht1 : (0 : ℝ) ≤ 1 - tp.1 := sub_nonneg.2 tp.1.2.2
            have hne : e tp.2.1.2 ≠ 0 := (map_ne_zero_iff e e.injective).2 tp.2.2
            by_cases hpos : 0 < e tp.2.1.2
            · have hw : e (rankOneSigmaToSnd B e (rankOneSndToSigma B e tp.2)).1.2 = 1 := by
                rw [rankOneSndToSigma_apply, rankOneSigmaToSnd_apply]
                dsimp only
                rw [ite_eq_left hpos, apply_rankOneVec_true e]
              rw [hw, mul_one] at he0
              have hprod : 0 ≤ (1 - (tp.1 : ℝ)) * e tp.2.1.2 := mul_nonneg ht1 hpos.le
              have ht_zero : (tp.1 : ℝ) = 0 := by linarith
              have : e tp.2.1.2 = 0 := by rw [ht_zero] at he0; linarith
              exact hne this
            · have hneg : e tp.2.1.2 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hne
              have hw : e (rankOneSigmaToSnd B e (rankOneSndToSigma B e tp.2)).1.2 = -1 := by
                rw [rankOneSndToSigma_apply, rankOneSigmaToSnd_apply]
                dsimp only
                rw [ite_eq_right hpos, apply_rankOneVec_false e]
              rw [hw, mul_neg_one] at he0
              have hprod : (1 - (tp.1 : ℝ)) * e tp.2.1.2 ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos ht1 hneg.le
              have ht_zero : (tp.1 : ℝ) = 0 := by linarith
              have : e tp.2.1.2 = 0 := by rw [ht_zero] at he0; linarith
              exact hne this⟩
        continuous_toFun := by fun_prop
        map_zero_left p := Subtype.ext (Prod.ext rfl (by simp))
        map_one_left p := Subtype.ext (Prod.ext rfl (by simp)) } :
        ContinuousMap.Homotopy (ContinuousMap.id _)
          ((rankOneSigmaToSnd B e).hom.comp (rankOneSndToSigma B e).hom)).symm⟩
  right_inv := by
    have h : (rankOneSndToSigma B e).hom.comp (rankOneSigmaToSnd B e).hom =
        ContinuousMap.id _ :=
      congrArg TopCat.Hom.hom (rankOneSigmaToSnd_comp_rankOneSndToSigma B e)
    exact ⟨h.symm ▸ ContinuousMap.Homotopy.refl _⟩

/-- The `+e⁻¹ 1` and `-e⁻¹ 1` sections `B ⟶ B × (F ∖ {0})`. -/
private def rankOneSection (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ) (b : Bool) :
    TopCat.of B ⟶ (prodThomPair B F).snd :=
  TopCat.ofHom
    { toFun x := ⟨(x, rankOneVec e b), rankOneVec_ne_zero e b⟩
      continuous_toFun := Continuous.subtype_mk (continuous_id.prodMk continuous_const) _ }

private lemma sigmaι_comp_rankOneSigmaToSnd (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ)
    (b : Bool) :
    TopCat.sigmaι.{w, w} (twoCopies B) (ULift.up.{w, 0} b) ≫ rankOneSigmaToSnd B e =
      rankOneSection B e b :=
  TopCat.ext fun _ ↦ rfl

private lemma rankOneSection_comp_prodThomPairPuncturedProj (B : Type w) [TopologicalSpace B]
    (e : F ≃L[ℝ] ℝ) (b : Bool) :
    rankOneSection B e b ≫ prodThomPairPuncturedProj B F = 𝟙 _ :=
  TopCat.ext fun x ↦ prodThomPairPuncturedProj_apply F (rankOneSection B e b x)

private lemma rankOneSection_comp_snd_prodThomPairMap
    {B B' : Type w} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B, B')) (e : F ≃L[ℝ] ℝ) (b : Bool) :
    rankOneSection B e b ≫ TopPair.Hom.snd (prodThomPairMap F g) =
      TopCat.ofHom g ≫ rankOneSection B' e b :=
  TopCat.ext fun x ↦ Subtype.ext (prodThomPairMap_snd_apply F g (rankOneSection B e b x))

end Geometry

section Cohomology

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K)
  {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pair of restrictions along the two sections `± e⁻¹ 1` in degree `n`. -/
private def rankOnePuncturedRestrictionsMap (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ)
    (n : ℕ) :
    (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n →ₗ[K]
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
        (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n :=
  (TopCat.singularCohomologyMap (rankOneSection B e true) n).hom.prod
    (TopCat.singularCohomologyMap (rankOneSection B e false) n).hom

private theorem bijective_rankOnePuncturedRestrictionsMap (B : Type w) [TopologicalSpace B]
    (e : F ≃L[ℝ] ℝ) (n : ℕ) :
    Function.Bijective (rankOnePuncturedRestrictionsMap M B e n) := by
  have hisoTo := (rankOnePuncturedHomotopyEquiv B e).isIso_singularCohomologyMap
    (𝟙_ (ModuleCat.{w} K)) K M n
  have hto : TopCat.ofHom (rankOnePuncturedHomotopyEquiv B e).toFun = rankOneSndToSigma B e :=
    TopCat.ext fun _ ↦ rfl
  have : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      (rankOneSndToSigma B e) n) := hto ▸ hisoTo
  have hisoSigma : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      (rankOneSigmaToSnd B e) n) := by
    have hcomp := rankOneSigmaToSnd_comp_rankOneSndToSigma B e
    have hiso : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (rankOneSigmaToSnd B e ≫ rankOneSndToSigma B e) n) := by
      rw [hcomp, TopCat.singularCohomologyMap_id]
      infer_instance
    rw [TopCat.singularCohomologyMap_comp] at hiso
    exact IsIso.of_isIso_comp_left
      (TopCat.singularCohomologyMap (rankOneSndToSigma B e) n)
      (TopCat.singularCohomologyMap (rankOneSigmaToSnd B e) n)
  have hbijSigma : Function.Bijective
      (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (rankOneSigmaToSnd B e) n) :=
    (asIso (TopCat.singularCohomologyMap (rankOneSigmaToSnd B e) n)).toLinearEquiv.bijective
  have hbijFan := bijective_fanBool (isLimitFanSingularCohomology (twoCopies B) (ModuleCat.{w} K)
    (𝟙_ (ModuleCat.{w} K)) K M n)
  have heq : ⇑(rankOnePuncturedRestrictionsMap M B e n) =
      ⇑((TopCat.singularCohomologyMap
            (TopCat.sigmaι.{w, w} (twoCopies B) (ULift.up.{w, 0} true)) n).hom.prod
          (TopCat.singularCohomologyMap
            (TopCat.sigmaι.{w, w} (twoCopies B) (ULift.up.{w, 0} false)) n).hom) ∘
        ⇑(TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
          (rankOneSigmaToSnd B e) n) := by
    funext x
    simp only [rankOnePuncturedRestrictionsMap, LinearMap.prod_apply, Function.comp_apply,
      ← sigmaι_comp_rankOneSigmaToSnd, TopCat.singularCohomologyMap_comp]
    rfl
  exact heq ▸ hbijFan.comp hbijSigma

/-- Restricting along the two sections `± e⁻¹ 1` gives `Hⁿ(B × (F ∖ {0}); M) ≃ₗ[K] Hⁿ(B; M)²`. -/
private def rankOnePuncturedRestrictionsEquiv (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ)
    (n : ℕ) :
    (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ≃ₗ[K]
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
        (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n :=
  LinearEquiv.ofBijective (rankOnePuncturedRestrictionsMap M B e n)
    (bijective_rankOnePuncturedRestrictionsMap M B e n)

@[simp]
private lemma rankOnePuncturedRestrictionsEquiv_apply (B : Type w) [TopologicalSpace B]
    (e : F ≃L[ℝ] ℝ) (n : ℕ)
    (x : (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) :
    rankOnePuncturedRestrictionsEquiv M B e n x =
      (TopCat.singularCohomologyMap (rankOneSection B e true) n x,
        TopCat.singularCohomologyMap (rankOneSection B e false) n x) :=
  (rfl)

/-- The indicator class `σ₁ ∈ H⁰(B × (F ∖ {0}); K)` equal to `1` on the positive half-space and `0`
on the negative half-space. -/
private def rankOnePuncturedClass (K : Type w) [CommRing K] (B : Type w) [TopologicalSpace B]
    (e : F ≃L[ℝ] ℝ) :
    (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 :=
  (rankOnePuncturedRestrictionsEquiv (𝟙_ (ModuleCat.{w} K)) B e 0).symm
    ((TopCat.of B).singularCohomologyZeroOne, 0)

private lemma singularCohomologyMap_rankOneSection_true_rankOnePuncturedClass
    (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ) :
    TopCat.singularCohomologyMap (rankOneSection B e true) 0 (rankOnePuncturedClass K B e) =
      (TopCat.of B).singularCohomologyZeroOne := by
  have h := (rankOnePuncturedRestrictionsEquiv (𝟙_ (ModuleCat.{w} K)) B e 0).apply_symm_apply
    ((TopCat.of B).singularCohomologyZeroOne, 0)
  rw [rankOnePuncturedRestrictionsEquiv_apply] at h
  exact congrArg Prod.fst h

private lemma singularCohomologyMap_rankOneSection_false_rankOnePuncturedClass
    (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ) :
    TopCat.singularCohomologyMap (rankOneSection B e false) 0
      (rankOnePuncturedClass K B e) = 0 := by
  have h := (rankOnePuncturedRestrictionsEquiv (𝟙_ (ModuleCat.{w} K)) B e 0).apply_symm_apply
    ((TopCat.of B).singularCohomologyZeroOne, 0)
  rw [rankOnePuncturedRestrictionsEquiv_apply] at h
  exact congrArg Prod.snd h

private lemma singularCohomologyMap_snd_prodThomPairMap_rankOnePuncturedClass
    {B' : Type w} [TopologicalSpace B'] (g : C(B, B')) (e : F ≃L[ℝ] ℝ) :
    TopCat.singularCohomologyMap (TopPair.Hom.snd (prodThomPairMap F g)) 0
        (rankOnePuncturedClass K B' e) =
      rankOnePuncturedClass K B e := by
  apply (rankOnePuncturedRestrictionsEquiv (𝟙_ (ModuleCat.{w} K)) B e 0).injective
  rw [rankOnePuncturedRestrictionsEquiv_apply, rankOnePuncturedRestrictionsEquiv_apply,
    singularCohomologyMap_rankOneSection_true_rankOnePuncturedClass,
    singularCohomologyMap_rankOneSection_false_rankOnePuncturedClass]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
      rankOneSection_comp_snd_prodThomPairMap, TopCat.singularCohomologyMap_comp,
      ConcreteCategory.comp_apply,
      singularCohomologyMap_rankOneSection_true_rankOnePuncturedClass,
      singularCohomologyMap_singularCohomologyZeroOne]
  · dsimp only
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
      rankOneSection_comp_snd_prodThomPairMap, TopCat.singularCohomologyMap_comp,
      ConcreteCategory.comp_apply,
      singularCohomologyMap_rankOneSection_false_rankOnePuncturedClass, map_zero]

/-- The map `(b, c) ↦ π₀^* b + σ₁ ⌣ π₀^* c` into `Hⁿ(B × (F ∖ {0}); M)` in rank `1`. -/
private def rankOnePuncturedMap (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ) (n : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) →ₗ[K]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n :=
  LinearMap.coprod (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n).hom
    ((prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
        0 n n (zero_add n) (rankOnePuncturedClass K B e) ∘ₗ
      (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n).hom)

@[simp]
private lemma rankOnePuncturedMap_apply (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ) (n : ℕ)
    (b c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) :
    rankOnePuncturedMap M B e n (b, c) =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n b +
        (prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
          0 n n (zero_add n) (rankOnePuncturedClass K B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n c) :=
  (rfl)

private theorem bijective_rankOnePuncturedMap (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ)
    (n : ℕ) :
    Function.Bijective (rankOnePuncturedMap M B e n) := by
  have hcomp : ⇑(rankOnePuncturedRestrictionsEquiv M B e n) ∘ ⇑(rankOnePuncturedMap M B e n) =
      fun bc ↦ (bc.1 + bc.2, bc.1) := by
    funext ⟨b, c⟩
    have hsec (s : Bool) (x : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) :
        TopCat.singularCohomologyMap (rankOneSection B e s) n
            (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n x) = x := by
      rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
        rankOneSection_comp_prodThomPairPuncturedProj, TopCat.singularCohomologyMap_id,
        ConcreteCategory.id_apply]
    rw [Function.comp_apply, rankOnePuncturedMap_apply, rankOnePuncturedRestrictionsEquiv_apply,
      map_add, map_add,
      ← TopCat.singularCup_naturality, ← TopCat.singularCup_naturality,
      hsec true b, hsec true c, hsec false b, hsec false c,
      singularCohomologyMap_rankOneSection_true_rankOnePuncturedClass,
      singularCohomologyMap_rankOneSection_false_rankOnePuncturedClass,
      map_zero, LinearMap.zero_apply, add_zero, TopCat.singularCohomologyZeroOne_def]
    congr 2
    refine (TopCat.of B).singularCup_constSingularCocycle_left K (η := 𝟙 _)
      ?_ ?_ (zero_add n) c <;> monoidal
  have hshear : Function.Bijective
      (fun bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
        (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ↦ (bc.1 + bc.2, bc.1)) :=
    ⟨fun ⟨b₁, c₁⟩ ⟨b₂, c₂⟩ h ↦ by
        have hb : b₁ = b₂ := congrArg Prod.snd h
        have hc : b₁ + c₁ = b₂ + c₂ := congrArg Prod.fst h
        exact Prod.ext hb (add_left_cancel (hb ▸ hc)),
      fun ⟨x, y⟩ ↦ ⟨(y, x - y), Prod.ext (add_sub_cancel y x) rfl⟩⟩
  exact (Function.Bijective.of_comp_iff' (rankOnePuncturedRestrictionsEquiv M B e n).bijective _).1
    (hcomp ▸ hshear)

/-- The decomposition `(b, c) ↦ π₀^* b + σ₁ ⌣ π₀^* c` of `Hⁿ(B × (F ∖ {0}); M)` in rank `1`. -/
private def rankOnePuncturedEquiv (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ) (n : ℕ) :
    ((TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) ≃ₗ[K]
      (prodThomPair B F).snd.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n :=
  LinearEquiv.ofBijective (rankOnePuncturedMap M B e n) (bijective_rankOnePuncturedMap M B e n)

@[simp]
private lemma rankOnePuncturedEquiv_apply (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ) (n : ℕ)
    (bc : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) :
    rankOnePuncturedEquiv M B e n bc =
      TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.1 +
        (prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
          0 n n (zero_add n) (rankOnePuncturedClass K B e)
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) n bc.2) :=
  (rfl)

/-- Every class of `Hⁿ(B × F; M)` is pulled back from `B`, since `F ≃L[ℝ] ℝ` is contractible. -/
private lemma exists_singularCohomologyMap_prodThomPairProj_eq_of_rankOne (e : F ≃L[ℝ] ℝ) (n : ℕ)
    (y : (prodThomPair B F).fst.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M n) :
    ∃ b, TopCat.singularCohomologyMap (prodThomPairProj B F) n b = y := by
  have := e.toHomeomorph.contractibleSpace
  have hiso := (ContinuousMap.HomotopyEquiv.prodContractible B F).isIso_singularCohomologyMap
    (𝟙_ (ModuleCat.{w} K)) K M n
  rw [ContinuousMap.HomotopyEquiv.prodContractible_toFun] at hiso
  have hproj : TopCat.ofHom ContinuousMap.fst = prodThomPairProj B F :=
    TopCat.ext fun p ↦ (prodThomPairProj_apply F p).symm
  have : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      (prodThomPairProj B F) n) := hproj ▸ hiso
  refine ⟨inv (TopCat.singularCohomologyMap (prodThomPairProj B F) n) y, ?_⟩
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

/-- In rank `1`, the long exact sequence of `(B × F, B × (F ∖ {0}))` makes `c ↦ δ (σ₁ ⌣ π₀^* c)`
bijective, hence `TopPair.pullbackCup` for `δ σ₁` is bijective. -/
private theorem bijective_pullbackCup_rankOne (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] ℝ)
    {p m : ℕ} (h : p + 1 = m) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 1 p m h
        ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          0 1 rfl (rankOnePuncturedClass K B e))) := by
  refine bijective_pullbackCup_singularCohomologyδ_of_bijective M (prodThomPair B F)
    (prodThomPairProj B F) (zero_add p) rfl h h (rankOnePuncturedClass K B e) ?_
  let P := prodThomPair B F
  let D := rankOnePuncturedEquiv M B e p
  have hfun (c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p) :
      P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h (D (0, c)) =
        P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h
          (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom 0 p p (zero_add p)
            (rankOnePuncturedClass K B e)
            (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p c)) := by
    rw [rankOnePuncturedEquiv_apply, map_zero, zero_add]
  suffices Function.Bijective
      (fun c : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p ↦
        P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h (D (0, c))) by
    have heq : (fun c : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ↦
          P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h
            (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom 0 p p (zero_add p)
              (rankOnePuncturedClass K B e)
              (TopCat.singularCohomologyMap (P.map ≫ prodThomPairProj B F) p c))) =
        fun c ↦ P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h (D (0, c)) := by
      funext c
      rw [map_comp_prodThomPairProj]
      exact (hfun c).symm
    exact heq ▸ this
  have hD0 (b : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p) :
      D (b, 0) = TopCat.singularCohomologyMap P.map p
        (TopCat.singularCohomologyMap (prodThomPairProj B F) p b) := by
    rw [rankOnePuncturedEquiv_apply, map_zero, map_zero, add_zero, ← ConcreteCategory.comp_apply,
      ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj]
  refine ⟨fun c₁ c₂ hc ↦ ?_, fun z ↦ ?_⟩
  · dsimp only at hc
    have hsub_D : D (0, c₁ - c₂) = D (0, c₁) - D (0, c₂) := by
      rw [← map_sub]
      congr 1
      simp
    have hsub : P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h (D (0, c₁ - c₂)) = 0 := by
      rw [hsub_D, map_sub, hc, sub_self]
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (P.singularCohomology_exact_subspace (𝟙_ (ModuleCat.{w} K)) K M p m h) _ hsub
    obtain ⟨b, rfl⟩ := exists_singularCohomologyMap_prodThomPairProj_eq_of_rankOne M e p y
    rw [← hD0 b] at hy
    exact sub_eq_zero.1 (congrArg Prod.snd (D.injective hy).symm)
  · obtain ⟨b, hb⟩ := exists_singularCohomologyMap_prodThomPairProj_eq_of_rankOne M e m
      (P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M m z)
    have hπ : P.singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M m z = 0 := by
      have h0 := ConcreteCategory.congr_hom
        (P.singularCohomologyπ_comp_singularCohomologyMap (𝟙_ (ModuleCat.{w} K)) K M m) z
      rw [ConcreteCategory.comp_apply, ← hb, ← ConcreteCategory.comp_apply,
        ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj] at h0
      have hinj : Function.Injective
          (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
            (M := M) (prodThomPairPuncturedProj B F) m) :=
        Function.LeftInverse.injective
          (g := TopCat.singularCohomologyMap (rankOneSection B e true) m) fun x ↦ by
            rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
              rankOneSection_comp_prodThomPairPuncturedProj, TopCat.singularCohomologyMap_id,
              ConcreteCategory.id_apply]
      rw [← hb, hinj (h0.trans (map_zero _).symm), map_zero]
    obtain ⟨x, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (P.singularCohomology_exact_relative (𝟙_ (ModuleCat.{w} K)) K M p m h) z hπ
    obtain ⟨⟨b', c⟩, rfl⟩ := D.surjective x
    refine ⟨c, ?_⟩
    have hδ0 : P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h (D (b', 0)) = 0 := by
      rw [hD0 b', ← ConcreteCategory.comp_apply,
        P.singularCohomologyMap_comp_singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h]
      simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
    have hbc : D (b', c) = D (b', 0) + D (0, c) := by
      rw [← map_add]
      congr 1
      simp
    rw [hbc, map_add, hδ0, zero_add]

end Cohomology

end RankOne

/-! ### Rank `d + 2` (`e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))`) -/

section RankGeTwo

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K)
  {B : Type w} [TopologicalSpace B] {F : Type w} [TopologicalSpace F]
  [AddCommMonoid F] [Module ℝ F] {d : ℕ}

/-- In rank `d + 2`, `TauCeti.prodThomPairSingularCohomologySphereEquiv` and
`bijective_pullbackCup_singularCohomologyδ_of_bijective` make `TopPair.pullbackCup` bijective for
`δ (prodThomPairPuncturedClass K B e)`. -/
private theorem bijective_pullbackCup_rankGeTwo
    (B : Type w) [TopologicalSpace B] (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)))
    {p m : ℕ} (h : p + (d + 2) = m) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
        ((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          (d + 1) (d + 2) rfl (prodThomPairPuncturedClass K B e))) := by
  refine bijective_pullbackCup_singularCohomologyδ_of_bijective M (prodThomPair B F)
    (prodThomPairProj B F) rfl rfl (by omega) h (prodThomPairPuncturedClass K B e) ?_
  have heq : (fun c ↦ (prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M
        (d + 1 + p) m (by omega)
        ((prodThomPair B F).snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom
          (d + 1) p (d + 1 + p) rfl (prodThomPairPuncturedClass K B e)
          (TopCat.singularCohomologyMap ((prodThomPair B F).map ≫ prodThomPairProj B F) p c))) =
      ⇑(prodThomPairSingularCohomologySphereEquiv M B e p m h) := by
    funext c
    rw [map_comp_prodThomPairProj]
    exact (prodThomPairSingularCohomologySphereEquiv_apply M e p m h c).symm
  exact heq ▸ (prodThomPairSingularCohomologySphereEquiv M B e p m h).bijective

end RankGeTwo

/-! ### Existence of a model fibre class in every finite rank -/

section ModelClass

variable {K : Type w} [CommRing K]

/-- A family of classes `u B` natural in `B` is the pull-back along `prodThomPairSnd B F` of its
restriction to the fibre over `PUnit`. -/
private lemma eq_singularCohomologyMap_prodThomPairSnd_of_natural
    {F : Type w} [TopologicalSpace F] [Zero F] {r : ℕ}
    (u : ∀ (B : Type w) [TopologicalSpace B],
      (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) r)
    (hnat : ∀ {B B' : Type w} [TopologicalSpace B] [TopologicalSpace B'] (g : C(B, B')),
      TopPair.singularCohomologyMap (prodThomPairMap F g) r (u B') = u B)
    (B : Type w) [TopologicalSpace B] :
    TopPair.singularCohomologyMap (prodThomPairSnd B F) r
        (TopPair.singularCohomologyMap (prodThomPairFiberMap F (PUnit.unit : PUnit.{w + 1})) r
          (u PUnit.{w + 1})) =
      u B := by
  have hcomp : prodThomPairSnd B F ≫ prodThomPairFiberMap F (PUnit.unit : PUnit.{w + 1}) =
      prodThomPairMap F (ContinuousMap.const B PUnit.unit) :=
    TopPair.hom_ext_of_fst _ (TopCat.ext fun p ↦
      (prodThomPairFiberMap_fst_apply F _ _).trans
        ((congrArg (Prod.mk PUnit.unit) (prodThomPairSnd_fst_apply F p)).trans
          (prodThomPairMap_fst_apply F _ p).symm))
  rw [← TopPair.singularCohomologyMap_comp_apply, hcomp, hnat]

/-- For every finite-dimensional real normed space `F`, there exists a class
`g₀ ∈ Hʳ(F, F ∖ {0}; K)` whose pull-back `u₀ = pr₂^* g₀` to `prodThomPair B F` makes
`TopPair.pullbackCup` bijective in every degree and for every coefficient module `M`. -/
private theorem exists_model_generator (K : Type w) [CommRing K]
    (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] :
    ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
        (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) (finrank ℝ F),
      ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) {p m : ℕ}
        (h : p + finrank ℝ F = m),
        Function.Bijective
          ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h
            (TopPair.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
              (M := 𝟙_ (ModuleCat.{w} K)) (prodThomPairSnd B F) (finrank ℝ F) g₀)) := by
  have key : ∀ r : ℕ, finrank ℝ F = r →
      ∃ g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
          (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) r,
        ∀ (B : Type w) [TopologicalSpace B] (M : ModuleCat.{w} K) {p m : ℕ} (h : p + r = m),
          Function.Bijective
            ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) r p m h
              (TopPair.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
                (M := 𝟙_ (ModuleCat.{w} K)) (prodThomPairSnd B F) r g₀)) := by
    intro r hr
    match r, hr with
    | 0, hr =>
      have : Subsingleton F := Module.finrank_zero_iff.1 hr
      refine ⟨TopPair.singularCohomologyMap (prodThomPairFiberMap F (PUnit.unit : PUnit.{w + 1})) 0
        (rankZeroClass K PUnit.{w + 1} F), fun B _ M {p m} h ↦ ?_⟩
      have heq := eq_singularCohomologyMap_prodThomPairSnd_of_natural
        (fun B _ ↦ rankZeroClass K B F)
        (fun g ↦ singularCohomologyMap_prodThomPairMap_rankZeroClass g F) B
      rw [heq]
      exact bijective_pullbackCup_rankZeroClass M B F h
    | 1, hr =>
      let e : F ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (hr.trans (Module.finrank_self ℝ).symm)
      let u : ∀ (B : Type w) [TopologicalSpace B],
          (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 1 :=
        fun B _ ↦ (prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
          (𝟙_ (ModuleCat.{w} K)) 0 1 rfl (rankOnePuncturedClass K B e)
      have hnat : ∀ {B B' : Type w} [TopologicalSpace B] [TopologicalSpace B'] (g : C(B, B')),
          TopPair.singularCohomologyMap (prodThomPairMap F g) 1 (u B') = u B := fun g ↦ by
        dsimp [u]
        rw [← ConcreteCategory.comp_apply,
          TopPair.singularCohomologyδ_naturality (prodThomPairMap F g) 0 1 rfl,
          ConcreteCategory.comp_apply,
          singularCohomologyMap_snd_prodThomPairMap_rankOnePuncturedClass]
      refine ⟨TopPair.singularCohomologyMap (prodThomPairFiberMap F (PUnit.unit : PUnit.{w + 1})) 1
        (u PUnit.{w + 1}), fun B _ M {p m} h ↦ ?_⟩
      have heq := eq_singularCohomologyMap_prodThomPairSnd_of_natural u (fun g ↦ hnat g) B
      rw [heq]
      exact bijective_pullbackCup_rankOne M B e h
    | d + 2, hr =>
      let e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
        ContinuousLinearEquiv.ofFinrankEq (hr.trans finrank_euclideanSpace_fin.symm)
      let u : ∀ (B : Type w) [TopologicalSpace B],
          (prodThomPair B F).singularCohomology
            (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) (d + 2) :=
        fun B _ ↦ (prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K
          (𝟙_ (ModuleCat.{w} K)) (d + 1) (d + 2) rfl (prodThomPairPuncturedClass K B e)
      have hnat : ∀ {B B' : Type w} [TopologicalSpace B] [TopologicalSpace B'] (g : C(B, B')),
          TopPair.singularCohomologyMap (prodThomPairMap F g) (d + 2) (u B') = u B := fun g ↦ by
        dsimp [u]
        rw [← ConcreteCategory.comp_apply,
          TopPair.singularCohomologyδ_naturality (prodThomPairMap F g) (d + 1) (d + 2) rfl,
          ConcreteCategory.comp_apply,
          singularCohomologyMap_snd_prodThomPairMap_prodThomPairPuncturedClass]
      refine ⟨TopPair.singularCohomologyMap (prodThomPairFiberMap F (PUnit.unit : PUnit.{w + 1}))
        (d + 2) (u PUnit.{w + 1}), fun B _ M {p m} h ↦ ?_⟩
      have heq := eq_singularCohomologyMap_prodThomPairSnd_of_natural u (fun g ↦ hnat g) B
      rw [heq]
      exact bijective_pullbackCup_rankGeTwo M B e h
  exact key (finrank ℝ F) rfl

end ModelClass

/-! ### Passage from a model generator to any fibrewise-generating class -/

section ArbitraryClass

variable {K : Type w} [CommRing K]

/-- Right cup multiplication on `Hᵖ(B; M)` by a cup-invertible degree-zero class `f ∈ H⁰(B; K)` is
bijective. -/
private lemma bijective_singularCup_right_of_exists_inv (M : ModuleCat.{w} K) (X : TopCat.{w})
    (p : ℕ) {f f' : X.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0}
    (hff' : X.singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl f f' = X.singularCohomologyZeroOne)
    (hf'f : X.singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl f' f = X.singularCohomologyZeroOne) :
    Function.Bijective
      (fun a : X.singularCohomology (ModuleCat.of K K) K M p ↦
        X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (Nat.add_zero p) a f) := by
  let mulR (w : X.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
      (a : X.singularCohomology (ModuleCat.of K K) K M p) :
      X.singularCohomology (ModuleCat.of K K) K M p :=
    X.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p (Nat.add_zero p) a w
  have hcomp (w₁ w₂ : X.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
      (hw : X.singularCup K (λ_ _).inv (λ_ _).hom 0 0 0 rfl w₁ w₂ = X.singularCohomologyZeroOne)
      (a : X.singularCohomology (ModuleCat.of K K) K M p) : mulR w₂ (mulR w₁ a) = a := by
    dsimp [mulR]
    rw [X.singularCup_assoc K (u₁₂ := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (u₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (by monoidal)
      (μ₁₂ := (ρ_ M).hom) (μ := (ρ_ M).hom) (μ₂₃ := (λ_ (𝟙_ (ModuleCat.{w} K))).hom)
      (μ' := (ρ_ M).hom) (by monoidal) (m' := 0) (Nat.add_zero p) (Nat.add_zero p) rfl
      (Nat.add_zero p) a w₁ w₂, hw, TopCat.singularCohomologyZeroOne_def]
    exact X.singularCup_constSingularCocycle_right K (η := 𝟙 _)
      (by monoidal) (by monoidal) (Nat.add_zero p) a
  exact ⟨Function.LeftInverse.injective (hcomp f f' hff'),
    Function.RightInverse.surjective (hcomp f' f hf'f)⟩

/-- Transfers a fibre-generation hypothesis from `ModuleCat.of K K` to `𝟙_ (ModuleCat.{w} K)`
by rewriting along `ModuleCat.of K K = 𝟙_ (ModuleCat.{w} K)` without unfolding
`TopPair.singularCohomologyMap`. -/
private lemma span_fiber_at_tensorUnit
    {P Q : TopPair.{w}} (φ : Q ⟶ P) {r : ℕ}
    {U : ModuleCat.{w} K} (hU : U = 𝟙_ (ModuleCat.{w} K))
    (u : P.singularCohomology U K U r)
    (u' : P.singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) r)
    (hu' : HEq u u')
    (hspan : Submodule.span K {TopPair.singularCohomologyMap φ r u} = ⊤) :
    Submodule.span K {TopPair.singularCohomologyMap φ r u'} = ⊤ := by
  subst hU
  cases eq_of_heq hu'
  exact hspan

/-- Restricting `π^* f ⌣ pr₂^* g₀` to the fibre over `b ∈ B` scales `g₀` by the value of `f` at
`b`. -/
private lemma singularCohomologyMap_prodThomPairFiberMap_pullbackCup_zero
    {B : Type w} [TopologicalSpace B] {F : Type w} [TopologicalSpace F] [Zero F] {r : ℕ}
    (g₀ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) r)
    (f : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
    (b : B) :
    TopPair.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := 𝟙_ (ModuleCat.{w} K))
        (prodThomPairFiberMap F b) r
        ((prodThomPair B F).pullbackCup (𝟙_ (ModuleCat.{w} K)) (prodThomPairProj B F) r 0 r
          (zero_add r)
          (TopPair.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
            (M := 𝟙_ (ModuleCat.{w} K)) (prodThomPairSnd B F) r g₀) f) =
      singularCohomologyZeroEval b f • g₀ := by
  let P₀ := TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)
  have hg : TopPair.Hom.fst (prodThomPairFiberMap F b) ≫ prodThomPairProj B F =
      TopCat.const (X := P₀.fst) b :=
    TopCat.ext fun x ↦ (prodThomPairProj_apply F _).trans
      (congrArg Prod.fst (prodThomPairFiberMap_fst_apply F b x))
  rw [TopPair.pullbackCup_apply, ← TopPair.singularCup_naturality,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hg,
    ← TopPair.singularCohomologyMap_comp_apply, prodThomPairFiberMap_comp_prodThomPairSnd,
    TopPair.singularCohomologyMap_id, ConcreteCategory.id_apply,
    singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul, map_smul, LinearMap.smul_apply,
    TopCat.singularCohomologyZeroOne_def]
  congr 1
  refine P₀.singularCup_constSingularCocycle_left K (η := 𝟙 _)
    ?_ ?_ (zero_add r) g₀ <;> monoidal

end ArbitraryClass

end ProdThomPairPullbackCup

open ProdThomPairPullbackCup

variable {K : Type w} [CommRing K]

/-- **The Thom isomorphism for a product bundle.** Let `B` be a topological space, `F` a
finite-dimensional real normed space of dimension `r = finrank ℝ F`, `K` a commutative ring, and
`M` a `K`-module. If `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` restricts on the fibre over every point
`b ∈ B` to a generator of `Hʳ(F, F ∖ {0}; K)`, then the map `a ↦ π^* a ⌣ u`
(`TopPair.pullbackCup` along `TauCeti.prodThomPairProj`) from `Hᵖ(B; M)` to
`Hᵐ(B × F, B × (F ∖ {0}); M)`, `p + r = m`, is bijective. -/
theorem bijective_pullbackCup_prodThomPair (M : ModuleCat.{w} K)
    (B : Type w) [TopologicalSpace B]
    (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)}
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤) :
    Function.Bijective
      ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) := by
  obtain ⟨g₀, hg₀⟩ := exists_model_generator K F
  let u₀ := TopPair.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
    (M := 𝟙_ (ModuleCat.{w} K)) (prodThomPairSnd B F) (finrank ℝ F) g₀
  obtain ⟨f, hf⟩ := (hg₀ B (𝟙_ (ModuleCat.{w} K)) (zero_add (finrank ℝ F))).2 u
  let f₁ : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 := f
  -- On every fibre `b`, `u` restricts to `(eval b f₁) • g₀`; since that spans `Hʳ ≅ K`, `eval b f₁`
  -- is a unit in `K`.
  have hunit (b : B) : IsUnit (singularCohomologyZeroEval b f₁) := by
    let φ := singularCohomologyComplSingletonFinrankEquivSelf (𝟙_ (ModuleCat.{w} K))
      (OpenPartialHomeomorph.refl F) (Set.mem_univ (0 : F))
    have hspan : Submodule.span K {φ (singularCohomologyZeroEval b f₁ • g₀)} = ⊤ := by
      refine φ.span_singleton_apply_eq_top_iff.2 ?_
      rw [← singularCohomologyMap_prodThomPairFiberMap_pullbackCup_zero g₀ f₁ b]
      have hf' : (prodThomPair B F).pullbackCup (𝟙_ (ModuleCat.{w} K)) (prodThomPairProj B F)
          (finrank ℝ F) 0 (finrank ℝ F) (zero_add (finrank ℝ F))
          (TopPair.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K)
            (M := 𝟙_ (ModuleCat.{w} K)) (prodThomPairSnd B F) (finrank ℝ F) g₀) f₁ = u := hf
      rw [hf']
      exact span_fiber_at_tensorUnit (prodThomPairFiberMap F b) rfl u u (HEq.refl u) (hu b)
    obtain ⟨s, hs⟩ := (Submodule.span_singleton_eq_top_iff K _).1 hspan (1 : K)
    rw [map_smul, smul_eq_mul, smul_eq_mul] at hs
    exact IsUnit.of_mul_eq_one (s * φ g₀) (by linear_combination hs)
  obtain ⟨f', hff', hf'f⟩ := exists_singularCup_eq_one f₁ hunit
  -- Cup associativity factors `pullbackCup` of `u = π^* f ⌣ u₀` through right multiplication by
  -- `f₁` followed by `pullbackCup` of `u₀`.
  have hfac : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u) =
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u₀) ∘
        fun a ↦ (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom
          p 0 p (Nat.add_zero p) a f₁ := by
    funext a
    have hf' : ((prodThomPair B F).pullbackCup (𝟙_ (ModuleCat.{w} K)) (prodThomPairProj B F)
        (finrank ℝ F) 0 (finrank ℝ F) (zero_add (finrank ℝ F)) u₀ f₁ :
          (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
            (finrank ℝ F)) = u := hf
    rw [Function.comp_apply, ← hf', TopPair.pullbackCup_apply, TopPair.pullbackCup_apply,
      TopPair.pullbackCup_apply, ← TopCat.singularCup_naturality]
    exact (TopPair.singularCup_assoc K (prodThomPair B F) (by monoidal) (by monoidal)
      (Nat.add_zero p) h (zero_add (finrank ℝ F)) h
      (TopCat.singularCohomologyMap (prodThomPairProj B F) p a)
      (TopCat.singularCohomologyMap (prodThomPairProj B F) 0 f₁) u₀).symm
  rw [hfac]
  exact (hg₀ B M h).comp (bijective_singularCup_right_of_exists_inv M (TopCat.of B) p hff' hf'f)

/-- **The Thom isomorphism `Hᵖ(B; M) ≃ₗ[K] Hᵐ(B × F, B × (F ∖ {0}); M)` for a product bundle**,
sending `a` to `π^* a ⌣ u` (`TauCeti.prodThomPairPullbackCupEquiv_apply`), for any class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` restricting to a generator on every fibre. -/
def prodThomPairPullbackCupEquiv (M : ModuleCat.{w} K)
    (B : Type w) [TopologicalSpace B]
    (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (p m : ℕ) (h : p + finrank ℝ F = m := by lia)
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (prodThomPair B F).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective
    ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u)
    (bijective_pullbackCup_prodThomPair M B F h hu)

/-- The underlying linear map of `TauCeti.prodThomPairPullbackCupEquiv` is `TopPair.pullbackCup`
along the bundle projection. -/
@[simp]
theorem toLinearMap_prodThomPairPullbackCupEquiv (M : ModuleCat.{w} K)
    (B : Type w) [TopologicalSpace B]
    (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤) :
    (prodThomPairPullbackCupEquiv M B F p m h u hu).toLinearMap =
      (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u :=
  (rfl)

/-- `TauCeti.prodThomPairPullbackCupEquiv` acts by `TopPair.pullbackCup` along the bundle
projection. -/
@[simp]
theorem prodThomPairPullbackCupEquiv_apply (M : ModuleCat.{w} K)
    (B : Type w) [TopologicalSpace B]
    (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (p m : ℕ) (h : p + finrank ℝ F = m)
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b : B, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    prodThomPairPullbackCupEquiv M B F p m h u hu a =
      (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (finrank ℝ F) p m h u a :=
  (rfl)

end TauCeti
