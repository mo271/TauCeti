/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.Sphere
import Mathlib.Algebra.Category.ModuleCat.Products
import TauCeti.Algebra.Ring.NegOnePow
import TauCeti.AlgebraicTopology.Cohomology.Additivity.Basic
import TauCeti.AlgebraicTopology.Cohomology.Cup.Connecting
import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
import TauCeti.AlgebraicTopology.Cohomology.GradedCommutativity
import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
import TauCeti.AlgebraicTopology.Cohomology.Local.Basic

/-!
# The Thom isomorphism for a product bundle

Let `B` be a topological space and `F` a finite-dimensional real normed space of dimension `r`.
The product bundle `B × F → B` has Thom pair `(B × F, B × (F ∖ {0}))` (`TauCeti.prodThomPair`)
and projection `π : B × F → B` (`TauCeti.prodThomPairProj`). For a class
`u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` with coefficients in a commutative ring `K`, the map

`Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)`,  `a ↦ π^*a ⌣ u`

(`TopPair.pullbackCup`) is the Thom map of `u`. This file proves that it is bijective in every
degree and for every module of coefficients `M` as soon as `u` restricts on the fibre pair
`(F, F ∖ {0})` over every point to a generator of `Hʳ(F, F ∖ {0}; K) ≅ K`
(`TauCeti.bijective_pullbackCup_prodThomPair`). This is the Thom isomorphism over a single
trivializing open set, the case that the Mayer–Vietoris step
`TopCat.bijective_pullbackCupRestrict_union` extends to unions of trivializing open sets.

The proof first produces, in every rank `r`, a single class `v ∈ Hʳ(B × F, B × (F ∖ {0}); K)`
whose Thom map is bijective in every degree and for every module of coefficients:

* **Rank `0`**: `F ∖ {0}` is empty, so `Hᵖ(B × F, ∅; M) ≅ Hᵖ(B × F; M) ≅ Hᵖ(B; M)`, and the
  class `v` corresponding to `1 ∈ H⁰(B × F; K)` acts by `π^*` under
  `Hᵖ(B × F, ∅; M) ⟶ Hᵖ(B × F; M)`.
* **Rank `1`**: choosing `e : F ≃L[ℝ] ℝ`, the punctured product `B × (F ∖ {0})` is homotopy
  equivalent to two copies of `B`, so `Hᵖ(B × (F ∖ {0}); M) ≅ Hᵖ(B; M) × Hᵖ(B; M)` by additivity
  (`TauCeti.isLimitFanSingularCohomology`). Taking `σ ∈ H⁰(B × (F ∖ {0}); K)` equal to `1` on the
  positive sheet and `0` on the negative sheet, the long exact sequence of the pair shows that
  `a ↦ δ (σ ⌣ π^*a)` is bijective, and `π^*a ⌣ δ σ = (-1)ᵖ δ (σ ⌣ π^*a)`.
* **Rank `r ≥ 2`**: for the class `σ ∈ Hʳ⁻¹(B × (F ∖ {0}); K)` pulled back from the generator of
  the cohomology of the sphere (`TauCeti.prodThomPairPuncturedClass`), the connecting morphism is
  linear over the cohomology of `B × F` up to sign (`TopPair.singularCohomologyδ_singularCup`), and
  the cup product is graded commutative (`TopCat.singularCup_gradedComm`), so

  `π^*a ⌣ δ σ = (-1)^(p r) δ (σ ⌣ π^*a)`

  for `a` of degree `p` (`TauCeti.pullbackCup_prodThomPair_singularCohomologyδ`). The right-hand
  side is, up to that sign, the equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv`
  computed from the cohomology of `Sʳ⁻¹ × B`, so the Thom map of `δ σ` is bijective.

A general class `u` is then `π^*c ⌣ v` for a unique `c ∈ H⁰(B; K)`. Restricted to the fibre over
`b`, it is the value `c(b)` times the restriction of `v`; since `Hʳ(F, F ∖ {0}; K)` is one copy of
`K`, it can only generate if `c(b)` is a unit. A degree-zero class whose values are units is a unit
for the cup product (`TauCeti.exists_singularCup_eq_one`), and the Thom map of `u` is that of `v`
composed with the cup product by `c`, which is then bijective.

## Main results

* `TauCeti.pullbackCup_prodThomPair_singularCohomologyδ`: for rank `d + 2 ≥ 2`, the Thom map of
  `δ σ` is, up to the sign `(-1)^(p (d + 2))`, the equivalence
  `TauCeti.prodThomPairSingularCohomologySphereEquiv`.
* `TauCeti.bijective_pullbackCup_prodThomPair`: **the Thom isomorphism for a product bundle** of
  any finite rank.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof, which starts from the product case.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof (the Thom
  isomorphism, first for a product bundle and then by Mayer–Vietoris).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Module

universe w

namespace TauCeti

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K)
  {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The Thom map of the class pulled back from the sphere -/

section Sphere

variable {d : ℕ}

/-- **The Thom map of `δ σ`.** For a continuous linear equivalence `e : F ≃L[ℝ] ℝᵈ⁺²` and the class
`σ = TauCeti.prodThomPairPuncturedClass` of `B × (F ∖ {0})`, the Thom map `a ↦ π^*a ⌣ δ σ` of the
product bundle sends `a ∈ Hᵖ(B; M)` to `(-1)^(p (d + 2)) δ (σ ⌣ π^*a)`, the image of `a` under the
equivalence `TauCeti.prodThomPairSingularCohomologySphereEquiv` up to that sign. -/
theorem pullbackCup_prodThomPair_singularCohomologyδ (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2)))
    {p m : ℕ} (h : p + (d + 2) = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    (prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
        (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
          (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e)) a =
      ((-1 : ℤ) ^ (p * (d + 2))) •
        prodThomPairSingularCohomologySphereEquiv M B e p m (by lia) a := by
  -- The connecting morphism moves the cup product with `π^*a` past `δ`, up to `(-1)ᵖ`.
  have hδ := TopPair.singularCohomologyδ_singularCup K (prodThomPair B F)
    (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom (p := p) (q := d + 1) (n := d + 1 + p)
    (q' := d + 2) (m := m) (by lia) rfl (by lia) h
    (TopCat.singularCohomologyMap (prodThomPairProj B F) p a) (prodThomPairPuncturedClass K B e)
  -- Graded commutativity exchanges `π^*a` and `σ`, up to `(-1)^(p (d + 1))`.
  have hcomm := TopCat.singularCup_gradedComm (prodThomPair B F).snd K
    (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
    (by rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal])
    (μ := (ρ_ M).hom) (μ' := (λ_ M).hom) (braiding_leftUnitor M) (p := p) (q := d + 1)
    (n := d + 1 + p) (by lia)
    (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a)
    (prodThomPairPuncturedClass K B e)
  rw [← map_comp_prodThomPairProj, TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]
    at hcomm
  rw [prodThomPairSingularCohomologySphereEquiv_apply, ← map_comp_prodThomPairProj,
    TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply, hcomm, map_zsmul, hδ,
    smul_smul, TopPair.pullbackCup_apply]
  -- The signs combine to `(-1)^(p (d + 2))` twice, which cancel.
  rw [smul_smul, mul_assoc, ← pow_add, show p * (d + 1) + p = p * (d + 2) by ring, mul_smul,
    neg_one_pow_smul_neg_one_pow_smul]

/-- The Thom map of `δ σ` is bijective in every degree, since it is the equivalence
`TauCeti.prodThomPairSingularCohomologySphereEquiv` up to a sign. -/
private theorem bijective_pullbackCup_prodThomPair_singularCohomologyδ
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) {p m : ℕ} (h : p + (d + 2) = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
      (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
        (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e))) := by
  have hcomp : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) (d + 2) p m h
      (((prodThomPair B F).singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
        (d + 1) (d + 2)) (prodThomPairPuncturedClass K B e))) =
      (((-1 : ℤ) ^ (p * (d + 2))) • ·) ∘ prodThomPairSingularCohomologySphereEquiv M B e p m
        (by lia) :=
    funext (pullbackCup_prodThomPair_singularCohomologyδ M e h)
  rw [hcomp]
  exact Function.Involutive.bijective (neg_one_pow_smul_neg_one_pow_smul _) |>.comp
    (LinearEquiv.bijective _)

end Sphere

/-! ### Rank zero -/

section RankZero

omit [NormedSpace ℝ F] in
/-- In rank `0`, `F ∖ {0}` is empty and `B × F ≅ B`, so the class corresponding to
`1 ∈ H⁰(B × F; K)` has bijective Thom map in every degree and for every module of coefficients. -/
private theorem exists_forall_bijective_pullbackCup_prodThomPair_zero [Subsingleton F] :
    ∃ v : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0,
      ∀ (M : ModuleCat.{w} K) (p m : ℕ) (h : p + 0 = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p m h v) := by
  have : IsEmpty (prodThomPair B F).snd := ⟨fun p ↦ p.2 (Subsingleton.elim _ _)⟩
  let v : (prodThomPair B F).singularCohomology (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 :=
    inv ((prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0)
      (prodThomPair B F).fst.singularCohomologyZeroOne
  have hvπ : (prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K))
      0 v = (prodThomPair B F).fst.singularCohomologyZeroOne := by
    rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
  have hProj : IsIso (prodThomPairProj B F) :=
    ⟨⟨TopCat.ofHom ⟨fun b ↦ (b, 0), by fun_prop⟩,
      TopCat.ext fun p ↦ Prod.ext (prodThomPairProj_apply F p) (Subsingleton.elim _ _),
      TopCat.ext fun b ↦ prodThomPairProj_apply F (b, 0)⟩⟩
  refine ⟨v, fun M p m h ↦ ?_⟩
  subst h
  have : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      (prodThomPairProj B F) p) :=
    (TauCeti.singularCohomologyFunctor (𝟙_ (ModuleCat.{w} K)) K M p).map_isIso
      (prodThomPairProj B F).op
  have hcomp : ⇑((prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p) ∘
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p p rfl v) =
      ⇑(TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (prodThomPairProj B F) p) := by
    funext a
    change (prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p
        ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 0 p p rfl v a) = _
    rw [TopPair.pullbackCup_apply, TopPair.singularCohomologyπ_singularCup, hvπ,
      TopCat.singularCohomologyZeroOne_def]
    exact TopCat.singularCup_constSingularCocycle_right _ K (η := 𝟙 _) (by monoidal)
      (by monoidal) rfl _
  have hπ := ConcreteCategory.bijective_of_isIso
    ((prodThomPair B F).singularCohomologyπ (𝟙_ (ModuleCat.{w} K)) K M p)
  have hproj := ConcreteCategory.bijective_of_isIso
    (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      (prodThomPairProj B F) p)
  exact (hπ.of_comp_iff' _).1 (hcomp.symm ▸ hproj)

end RankZero

/-! ### Rank one -/

section RankOne

open Limits

/-- The two sheet sections `b ↦ (b, e⁻¹ (±1))` of the punctured rank-`1` product bundle. -/
private def rankOneSection (e : F ≃L[ℝ] ℝ) (s : Bool) :
    TopCat.of B ⟶ (prodThomPair B F).snd :=
  TopCat.ofHom ⟨fun b ↦ ⟨(b, e.symm (if s then 1 else -1)), by cases s <;> simp⟩, by fun_prop⟩

private lemma rankOneSection_comp_proj (e : F ≃L[ℝ] ℝ) (s : Bool) :
    rankOneSection (B := B) e s ≫ prodThomPairPuncturedProj B F = 𝟙 _ :=
  TopCat.ext fun b ↦ prodThomPairPuncturedProj_apply F (rankOneSection e s b)

/-- The sign `p ↦ (0 < e p.1.2)` on `B × (F ∖ {0})` is continuous into the discrete type
`ULift Bool`. -/
private lemma continuous_rankOneSign (e : F ≃L[ℝ] ℝ) :
    Continuous (fun p : (prodThomPair B F).snd ↦ ULift.up.{w} (decide (0 < e p.1.2))) := by
  rw [continuous_discrete_rng]
  rintro ⟨b⟩
  have hcont : Continuous (fun p : (prodThomPair B F).snd ↦ e p.1.2) :=
    e.continuous.comp (continuous_snd.comp continuous_subtype_val)
  cases b
  · have hpre : (fun p : (prodThomPair B F).snd ↦ ULift.up.{w} (decide (0 < e p.1.2))) ⁻¹'
        {ULift.up false} = {p | e p.1.2 < 0} := by
      ext p
      have hne : e p.1.2 ≠ 0 := by simpa using p.2
      simp only [Set.mem_preimage, Set.mem_singleton_iff, ULift.up.injEq,
        decide_eq_false_iff_not, not_lt, Set.mem_ofPred_eq]
      exact ⟨fun h ↦ lt_of_le_of_ne h hne, fun h ↦ le_of_lt h⟩
    rw [hpre]
    exact isOpen_lt hcont continuous_const
  · have hpre : (fun p : (prodThomPair B F).snd ↦ ULift.up.{w} (decide (0 < e p.1.2))) ⁻¹'
        {ULift.up true} = {p | 0 < e p.1.2} := by
      ext p
      simp
    rw [hpre]
    exact isOpen_lt continuous_const hcont

/-- The map `(b, x) ↦ (sign(e x), b)` into the disjoint union of two copies of `B` is continuous. -/
private lemma continuous_rankOneInvFun (e : F ≃L[ℝ] ℝ) :
    Continuous (fun p : (prodThomPair B F).snd ↦
      (⟨ULift.up.{w} (decide (0 < e p.1.2)), p.1.1⟩ : Σ _ : ULift.{w} Bool, TopCat.of B)) := by
  rw [continuous_def]
  intro U hU
  have hpre : (fun p : (prodThomPair B F).snd ↦
      (⟨ULift.up.{w} (decide (0 < e p.1.2)), p.1.1⟩ : Σ _ : ULift.{w} Bool, TopCat.of B)) ⁻¹' U =
      ⋃ i : ULift.{w} Bool,
        ((fun p : (prodThomPair B F).snd ↦ ULift.up.{w} (decide (0 < e p.1.2))) ⁻¹' {i}) ∩
          ((fun p : (prodThomPair B F).snd ↦ p.1.1) ⁻¹'
            ((fun b : B ↦ (⟨i, b⟩ : Σ _ : ULift.{w} Bool, TopCat.of B)) ⁻¹' U)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun hp ↦ ⟨_, rfl, hp⟩, fun ⟨_, hi, hp⟩ ↦ hi ▸ hp⟩
  rw [hpre]
  exact isOpen_iUnion fun i ↦
    ((isOpen_discrete {i}).preimage (continuous_rankOneSign e)).inter
      ((isOpen_sigma_iff.1 hU i).preimage (continuous_fst.comp continuous_subtype_val))

private def rankOneToFun (e : F ≃L[ℝ] ℝ) :
    C(TopCat.of (Σ _ : ULift.{w} Bool, TopCat.of B), (prodThomPair B F).snd) :=
  ⟨fun p ↦ ⟨(p.2, e.symm (if p.1.down then 1 else -1)), by cases p.1.down <;> simp⟩,
    continuous_sigma fun ⟨s⟩ ↦ (rankOneSection (B := B) e s).hom.continuous⟩

/-- For `e : F ≃L[ℝ] ℝ`, the punctured product `B × (F ∖ {0})` is homotopy equivalent to the
disjoint union of two copies of `B`, via the sheet inclusions `b ↦ (b, e⁻¹ (±1))`. -/
private def rankOnePuncturedHomotopyEquiv (e : F ≃L[ℝ] ℝ) :
    ContinuousMap.HomotopyEquiv
      (TopCat.of (Σ _ : ULift.{w} Bool, TopCat.of B)) (prodThomPair B F).snd where
  toFun := rankOneToFun e
  invFun := ⟨fun p ↦ ⟨ULift.up.{w} (decide (0 < e p.1.2)), p.1.1⟩, continuous_rankOneInvFun e⟩
  left_inv := by
    have hcomp :
        (⟨fun p ↦ ⟨ULift.up.{w} (decide (0 < e p.1.2)), p.1.1⟩,
          continuous_rankOneInvFun e⟩ :
            C((prodThomPair B F).snd, Σ _ : ULift.{w} Bool, TopCat.of B)).comp
        (rankOneToFun e) =
        ContinuousMap.id _ := by
      apply ContinuousMap.ext
      rintro ⟨⟨s⟩, b⟩
      cases s
      · refine Sigma.ext ?_ HEq.rfl
        change ULift.up.{w} (decide (0 < e (e.symm (-1)))) = ULift.up.{w} false
        simp
      · refine Sigma.ext ?_ HEq.rfl
        change ULift.up.{w} (decide (0 < e (e.symm 1))) = ULift.up.{w} true
        simp
    rw [hcomp]
  right_inv := by
    have hsgn : Continuous (fun p : (prodThomPair B F).snd ↦
        if (ULift.up.{w} (decide (0 < e p.1.2))).down then (1 : ℝ) else -1) :=
      continuous_of_discreteTopology (f := fun i : ULift.{w} Bool ↦
        if i.down then (1 : ℝ) else -1) |>.comp (continuous_rankOneSign e)
    have hcont_t : Continuous (fun q : unitInterval × (prodThomPair B F).snd ↦ (q.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hcont_ex : Continuous (fun q : unitInterval × (prodThomPair B F).snd ↦ e q.2.1.2) :=
      e.continuous.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
    refine ⟨{
      toFun q := ⟨(q.2.1.1, e.symm ((1 - (q.1 : ℝ)) *
        (if (ULift.up.{w} (decide (0 < e q.2.1.2))).down then (1 : ℝ) else -1) +
        (q.1 : ℝ) * e q.2.1.2)), by
        intro h0
        have hval : (1 - (q.1 : ℝ)) *
            (if 0 < e q.2.1.2 then (1 : ℝ) else -1) + (q.1 : ℝ) * e q.2.1.2 = 0 := by
          simpa using congrArg e h0
        have hne : e q.2.1.2 ≠ 0 := by simpa using q.2.2
        have ht0 : (0 : ℝ) ≤ q.1 := q.1.2.1
        have ht1 : (q.1 : ℝ) ≤ 1 := q.1.2.2
        by_cases hpos : 0 < e q.2.1.2
        · simp only [hpos, ↓reduceIte] at hval
          by_cases ht : (q.1 : ℝ) = 0
          · rw [ht] at hval; norm_num at hval
          · have htpos : (0 : ℝ) < q.1 := lt_of_le_of_ne ht0 (Ne.symm ht)
            nlinarith
        · have hneg : e q.2.1.2 < 0 := lt_of_le_of_ne (not_lt.1 hpos) hne
          simp only [hpos, ↓reduceIte] at hval
          by_cases ht : (q.1 : ℝ) = 0
          · rw [ht] at hval; norm_num at hval
          · have htpos : (0 : ℝ) < q.1 := lt_of_le_of_ne ht0 (Ne.symm ht)
            nlinarith⟩
      continuous_toFun := by
        refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
        · exact continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
        · exact e.symm.continuous.comp (((continuous_const.sub hcont_t).mul
            (hsgn.comp continuous_snd)).add (hcont_t.mul hcont_ex))
      map_zero_left p := by
        apply Subtype.ext
        change (p.1.1, e.symm _) = (p.1.1, e.symm _)
        simp
      map_one_left p := by
        apply Subtype.ext
        simp }⟩

/-- Pullback along the two sheets `b ↦ (b, e⁻¹ (±1))` separates classes on `B × (F ∖ {0})` and
surjects onto `Hᵖ(B; M) × Hᵖ(B; M)`. -/
private theorem rankOne_sheet_bijective (e : F ≃L[ℝ] ℝ) (p : ℕ) :
    Function.Bijective fun y : (prodThomPair B F).snd.singularCohomology
        (𝟙_ (ModuleCat.{w} K)) K M p ↦
      (TopCat.singularCohomologyMap (rankOneSection (B := B) e true) p y,
       TopCat.singularCohomologyMap (rankOneSection (B := B) e false) p y) := by
  let f : TopCat.of (Σ _ : ULift.{w} Bool, TopCat.of B) ⟶ (prodThomPair B F).snd :=
    TopCat.ofHom (rankOnePuncturedHomotopyEquiv e).toFun
  have hf_iso : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
      f p) :=
    (rankOnePuncturedHomotopyEquiv e).isIso_singularCohomologyMap _ K M p
  have hcomp (s : Bool) :
      TopCat.sigmaι (fun _ : ULift.{w} Bool ↦ TopCat.of B) (ULift.up s) ≫ f =
        rankOneSection e s :=
    TopCat.ext fun _ ↦ rfl
  let Z : ULift.{w} Bool → ModuleCat.{w} K :=
    fun _ ↦ (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p
  let eIso : (TopCat.of (Σ _ : ULift.{w} Bool, TopCat.of B)).singularCohomology
      (𝟙_ (ModuleCat.{w} K)) K M p ≅ ModuleCat.of K (∀ i : ULift.{w} Bool, Z i) :=
    (isLimitFanSingularCohomology (fun _ : ULift.{w} Bool ↦ TopCat.of B)
      (ModuleCat.{w} K) (𝟙_ (ModuleCat.{w} K)) K M p).conePointUniqueUpToIso
      (ModuleCat.productConeIsLimit Z)
  have heIso (x) (s : Bool) :
      eIso.hom x (ULift.up s) =
        TopCat.singularCohomologyMap
          (TopCat.sigmaι (fun _ : ULift.{w} Bool ↦ TopCat.of B) (ULift.up s)) p x := by
    have hfac := ConcreteCategory.congr_hom
      ((isLimitFanSingularCohomology (fun _ : ULift.{w} Bool ↦ TopCat.of B)
        (ModuleCat.{w} K) (𝟙_ (ModuleCat.{w} K)) K M p).conePointUniqueUpToIso_hom_comp
        (ModuleCat.productConeIsLimit Z) ⟨ULift.up s⟩) x
    simp only [ConcreteCategory.comp_apply, ModuleCat.productCone, Fan.mk_π_app] at hfac
    exact hfac
  let equivPair : (∀ i : ULift.{w} Bool, Z i) ≃
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p ×
      (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p :=
    { toFun g := (g (ULift.up true), g (ULift.up false))
      invFun ab i := if i.down then ab.1 else ab.2
      left_inv g := by funext ⟨s⟩; cases s <;> rfl
      right_inv _ := rfl }
  have hbij : Function.Bijective (equivPair ∘ eIso.hom ∘
      TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M) f p) :=
    equivPair.bijective.comp ((ConcreteCategory.bijective_of_isIso eIso.hom).comp
      (ConcreteCategory.bijective_of_isIso _))
  have heq : (equivPair ∘ eIso.hom ∘
      TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M) f p) =
      fun y ↦
        (TopCat.singularCohomologyMap (rankOneSection (B := B) e true) p y,
         TopCat.singularCohomologyMap (rankOneSection (B := B) e false) p y) := by
    funext y
    dsimp only [Function.comp_apply, equivPair, Equiv.coe_fn_mk]
    simp only [heIso, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, hcomp]
  exact heq ▸ hbij

/-- In rank `1`, the product bundle has a class whose Thom map is bijective in every degree and
for every module of coefficients: the connecting image `δ σ` of the degree-`0` class equal to `1`
on the positive sheet and `0` on the negative sheet. -/
private theorem exists_forall_bijective_pullbackCup_prodThomPair_one (e : F ≃L[ℝ] ℝ) :
    ∃ v : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 1,
      ∀ (M : ModuleCat.{w} K) (p m : ℕ) (h : p + 1 = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) 1 p m h v) := by
  have hcontract : ContractibleSpace F := e.toHomeomorph.contractibleSpace
  obtain ⟨σ, hσ⟩ := (rankOne_sheet_bijective (B := B) (𝟙_ (ModuleCat.{w} K)) e 0).2
    ((TopCat.of B).singularCohomologyZeroOne, 0)
  have hσ_pos : TopCat.singularCohomologyMap (rankOneSection (B := B) e true) 0 σ =
      (TopCat.of B).singularCohomologyZeroOne := congrArg Prod.fst hσ
  have hσ_neg : TopCat.singularCohomologyMap (rankOneSection (B := B) e false) 0 σ = 0 :=
    congrArg Prod.snd hσ
  let P := prodThomPair B F
  let v : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 1 :=
    P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K (𝟙_ (ModuleCat.{w} K)) 0 1 rfl σ
  refine ⟨v, fun M p m h ↦ ?_⟩
  -- Pullback along `π : B × F → B` is an isomorphism in every degree since `F` is contractible.
  have hproj_surj (q : ℕ) (y : P.fst.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M q) :
      ∃ b, TopCat.singularCohomologyMap (prodThomPairProj B F) q b = y := by
    have h1 := (ContinuousMap.HomotopyEquiv.prodContractible B F).isIso_singularCohomologyMap
      (𝟙_ (ModuleCat.{w} K)) K M q
    rw [ContinuousMap.HomotopyEquiv.prodContractible_toFun] at h1
    have hproj : TopCat.ofHom ContinuousMap.fst = prodThomPairProj B F :=
      TopCat.ext fun x ↦ (prodThomPairProj_apply F x).symm
    have : IsIso (TopCat.singularCohomologyMap (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M)
        (prodThomPairProj B F) q) := hproj ▸ h1
    exact (ConcreteCategory.bijective_of_isIso _).2 y
  -- Pullback along the punctured projection `π₀` is injective in every degree.
  have hpunct_inj (q : ℕ) : Function.Injective (TopCat.singularCohomologyMap
      (R := 𝟙_ (ModuleCat.{w} K)) (k := K) (M := M) (prodThomPairPuncturedProj B F) q) := by
    refine Function.LeftInverse.injective
      (g := TopCat.singularCohomologyMap (rankOneSection e true) q) fun b ↦ ?_
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
      rankOneSection_comp_proj, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]
  -- Evaluate `σ ⌣ π₀^* a` on both sheets.
  have hcup_pos (a : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p) :
      TopCat.singularCohomologyMap (rankOneSection e true) p
          (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom 0 p p (zero_add p) σ
            (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a)) = a := by
    rw [← TopCat.singularCup_naturality, hσ_pos, ← ConcreteCategory.comp_apply,
      ← TopCat.singularCohomologyMap_comp, rankOneSection_comp_proj,
      TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
      TopCat.singularCohomologyZeroOne_def]
    exact TopCat.singularCup_constSingularCocycle_left _ K (η := 𝟙 _) (by monoidal)
      (by monoidal) (zero_add p) a
  have hcup_neg (a : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p) :
      TopCat.singularCohomologyMap (rankOneSection e false) p
          (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom 0 p p (zero_add p) σ
            (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a)) = 0 := by
    rw [← TopCat.singularCup_naturality, hσ_neg, map_zero, LinearMap.zero_apply]
  -- `φ(a) = δ (σ ⌣ π₀^* a)` is bijective by the long exact sequence of the pair.
  let φ : (TopCat.of B).singularCohomology (𝟙_ (ModuleCat.{w} K)) K M p →ₗ[K]
      P.singularCohomology (𝟙_ (ModuleCat.{w} K)) K M m :=
    (P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h).hom ∘ₗ
      (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom 0 p p (zero_add p) σ) ∘ₗ
        (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p).hom
  have hφ_bij : Function.Bijective φ := by
    constructor
    · refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
      obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).1
        (P.singularCohomology_exact_subspace (𝟙_ (ModuleCat.{w} K)) K M p m h) _ ha
      obtain ⟨b, rfl⟩ := hproj_surj p w
      rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
        map_comp_prodThomPairProj, LinearMap.comp_apply] at hw
      have hneg := congrArg (TopCat.singularCohomologyMap (rankOneSection e false) p) hw
      rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
        rankOneSection_comp_proj, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
        hcup_neg] at hneg
      have hpos := congrArg (TopCat.singularCohomologyMap (rankOneSection e true) p) hw
      rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
        rankOneSection_comp_proj, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
        hcup_pos, hneg] at hpos
      exact hpos.symm
    · intro z
      obtain ⟨b₀, hb₀⟩ := hproj_surj m (P.singularCohomologyπ _ K M m z)
      have hπ : P.singularCohomologyπ _ K M m z = 0 := by
        have h0 := ConcreteCategory.congr_hom
          (P.singularCohomologyπ_comp_singularCohomologyMap (𝟙_ (ModuleCat.{w} K)) K M m) z
        rw [ConcreteCategory.comp_apply, ← hb₀, ← ConcreteCategory.comp_apply,
          ← TopCat.singularCohomologyMap_comp, map_comp_prodThomPairProj] at h0
        rw [← hb₀, hpunct_inj m (h0.trans (map_zero _).symm), map_zero]
      obtain ⟨y, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
        (P.singularCohomology_exact_relative (𝟙_ (ModuleCat.{w} K)) K M p m h) z hπ
      let b := TopCat.singularCohomologyMap (rankOneSection e false) p y
      let a := TopCat.singularCohomologyMap (rankOneSection e true) p y - b
      have hy : y = TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p b +
          P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom 0 p p (zero_add p) σ
            (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a) := by
        apply (rankOne_sheet_bijective M e p).1
        apply Prod.ext
        · dsimp only
          rw [map_add, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
            rankOneSection_comp_proj, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
            hcup_pos, add_sub_cancel]
        · dsimp only
          rw [map_add, ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
            rankOneSection_comp_proj, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply,
            hcup_neg, add_zero]
      refine ⟨a, ?_⟩
      have hδb : P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p b) = 0 := by
        rw [← map_comp_prodThomPairProj, TopCat.singularCohomologyMap_comp,
          ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          P.singularCohomologyMap_comp_singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h]
        simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
      rw [hy, map_add, hδb, zero_add]
      rfl
  -- The Thom map of `δ σ` equals `(-1)^p • φ`.
  have hcomp : ⇑(P.pullbackCup M (prodThomPairProj B F) 1 p m h v) =
      (((-1 : ℤ) ^ p) • ·) ∘ φ := by
    funext a
    have hδ := TopPair.singularCohomologyδ_singularCup K P
      (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom (p := p) (q := 0) (n := p)
      (q' := 1) (m := m) (add_zero p) rfl h h
      (TopCat.singularCohomologyMap (prodThomPairProj B F) p a) σ
    have hcomm := TopCat.singularCup_gradedComm P.snd K
      (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv) (u' := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
      (by rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, unitors_inv_equal])
      (μ := (ρ_ M).hom) (μ' := (λ_ M).hom) (braiding_leftUnitor M) (p := p) (q := 0)
      (n := p) (add_zero p)
      (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a) σ
    rw [← map_comp_prodThomPairProj, TopCat.singularCohomologyMap_comp,
      ConcreteCategory.comp_apply] at hcomm
    simp only [mul_zero, pow_zero, one_zsmul] at hcomm
    have hφa : φ a = ((-1 : ℤ) ^ p) • P.pullbackCup M (prodThomPairProj B F) 1 p m h v a := by
      change P.singularCohomologyδ (𝟙_ (ModuleCat.{w} K)) K M p m h
        (P.snd.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (λ_ M).hom 0 p p (zero_add p) σ
          (TopCat.singularCohomologyMap (prodThomPairPuncturedProj B F) p a)) = _
      rw [← map_comp_prodThomPairProj, TopCat.singularCohomologyMap_comp,
        ConcreteCategory.comp_apply, hcomm, hδ, TopPair.pullbackCup_apply]
    change P.pullbackCup M (prodThomPairProj B F) 1 p m h v a = ((-1 : ℤ) ^ p) • φ a
    rw [hφa, neg_one_pow_smul_neg_one_pow_smul]
  rw [hcomp]
  exact (Function.Involutive.bijective (neg_one_pow_smul_neg_one_pow_smul _)).comp hφ_bij

end RankOne

/-! ### The Thom map of a general class -/

omit [NormedSpace ℝ F] in
/-- On the fibre over `b`, the class `π^*c ⌣ v` restricts to the value of `c` at `b` times the
restriction of `v`. -/
private theorem singularCohomologyMap_prodThomPairFiberMap_pullbackCup {r : ℕ} (b : B)
    (v : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) r)
    (c : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) 0) :
    TopPair.singularCohomologyMap (prodThomPairFiberMap F b) r
        ((prodThomPair B F).pullbackCup (ModuleCat.of K K) (prodThomPairProj B F) r 0 r
          (zero_add r) v c) =
      singularCohomologyZeroEval b c •
        TopPair.singularCohomologyMap (prodThomPairFiberMap F b) r v := by
  have hg : TopPair.Hom.fst (prodThomPairFiberMap F b) ≫ prodThomPairProj B F =
      TopCat.const (X := (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).fst)
        (Y := TopCat.of B) b ≫ 𝟙 _ :=
    TopCat.ext fun x ↦
      (congrArg (prodThomPairProj B F) (prodThomPairFiberMap_fst_apply F b x)).trans
        (prodThomPairProj_apply F (b, x))
  rw [← TopPair.pullbackCup_naturality (prodThomPairFiberMap F b) _ (prodThomPairProj B F) (𝟙 _)
      hg, TopCat.singularCohomologyMap_id,
    ConcreteCategory.id_apply, TopPair.pullbackCup_apply,
    singularCohomologyMap_const_eq_singularCohomologyZeroEval_smul, map_smul,
    LinearMap.smul_apply, TopCat.singularCohomologyZeroOne_def,
    TopPair.singularCup_constSingularCocycle_left K _ (η := 𝟙 _) (by monoidal) (by monoidal)]

/-- Every finite-rank product bundle has a class whose Thom map is bijective in every degree and
for every module of coefficients. -/
private theorem exists_forall_bijective_pullbackCup_prodThomPair [FiniteDimensional ℝ F] :
    ∃ v : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
        (finrank ℝ F),
      ∀ (M : ModuleCat.{w} K) (p m : ℕ) (h : p + finrank ℝ F = m),
        Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) _ p m h v) := by
  match hr : finrank ℝ F with
  | 0 =>
    have : Subsingleton F := Module.finrank_zero_iff.mp hr
    exact exists_forall_bijective_pullbackCup_prodThomPair_zero
  | 1 =>
    obtain ⟨e⟩ : Nonempty (F ≃L[ℝ] ℝ) :=
      ⟨ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_self, hr])⟩
    exact exists_forall_bijective_pullbackCup_prodThomPair_one e
  | d + 2 =>
    obtain ⟨e⟩ : Nonempty (F ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 2))) :=
      ⟨ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin, hr])⟩
    exact ⟨_, fun M p m h ↦ bijective_pullbackCup_prodThomPair_singularCohomologyδ M e h⟩

/-- **The Thom isomorphism for a product bundle.** Let `F` be a finite-dimensional real normed
space of dimension `r`, and let `u ∈ Hʳ(B × F, B × (F ∖ {0}); K)` restrict on the fibre pair
`(F, F ∖ {0})` over every point of `B` to a generator of the `K`-module `Hʳ(F, F ∖ {0}; K)`.
Then for every `K`-module `M` and every degree `p`, the Thom map
`Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(B × F, B × (F ∖ {0}); M)`, `a ↦ π^*a ⌣ u`, is bijective. -/
theorem bijective_pullbackCup_prodThomPair [FiniteDimensional ℝ F]
    (u : (prodThomPair B F).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F))
    (hu : ∀ b, Submodule.span K
      {TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F) u} = ⊤)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective ((prodThomPair B F).pullbackCup M (prodThomPairProj B F) _ p m h u) := by
  obtain ⟨v, hv⟩ := exists_forall_bijective_pullbackCup_prodThomPair (B := B) (F := F) (K := K)
  -- `u = π^*c ⌣ v` for a degree-zero class `c`, since the Thom map of `v` is onto in degree `0`.
  obtain ⟨c, rfl⟩ := (hv (ModuleCat.of K K) 0 _ (zero_add _)).2 u
  -- The values of `c` are units: on the fibre over `b`, `u` is `c(b)` times the restriction of
  -- `v`, and generates the local cohomology `Hʳ(F, F ∖ {0}; K) ≅ K`.
  have hc (b : B) : IsUnit (singularCohomologyZeroEval b c) := by
    have hb := congrArg (Submodule.map (singularCohomologyComplSingletonFinrankEquivSelf
      (ModuleCat.of K K) (OpenPartialHomeomorph.refl F) (Set.mem_univ 0)).toLinearMap) (hu b)
    rw [Submodule.map_span, Set.image_singleton,
      singularCohomologyMap_prodThomPairFiberMap_pullbackCup, LinearEquiv.coe_toLinearMap,
      map_smul, Submodule.map_top, LinearEquiv.range] at hb
    exact isUnit_of_mul_isUnit_left (Ideal.span_singleton_eq_top.1 hb)
  obtain ⟨c', hcc', hc'c⟩ := exists_singularCup_eq_one c hc
  -- So the Thom map of `u` is that of `v` after the bijective cup product with `c`.
  have hcomp : ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) _ p m h
      ((prodThomPair B F).pullbackCup (ModuleCat.of K K) (prodThomPairProj B F) _ 0 _
        (zero_add _) v c)) =
      ⇑((prodThomPair B F).pullbackCup M (prodThomPairProj B F) _ p m h v) ∘ fun a ↦
        (TopCat.of B).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p 0 p rfl a c :=
    funext (TopPair.pullbackCup_pullbackCup _ _ (add_zero p) (zero_add _) h h v c)
  rw [hcomp]
  exact (hv M p m h).comp (bijective_singularCup_left_of_singularCup_eq_one hcc' hc'c M p)

end TauCeti
