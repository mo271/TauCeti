/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.InverseLimit
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inhomogeneous.InverseLimit
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inhomogeneous.LowDegree
import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.Naturality

/-!
# Milnor exact sequence for `continuousCohomology` and the `ℤ_[p]` inverse-limit check

Over a locally compact topological group `G`, the all-degree comparison isomorphism
`inhomogeneousCochainsIsoHomogeneous` transfers the inverse-limit isomorphism
`inhomogeneousCochainsLimIso` and the Milnor exact sequence of
`TauCeti.RepresentationTheory.Homological.ContCohomology.Inhomogeneous.InverseLimit` directly to
Mathlib's `TopRep.homogeneousCochains` and `continuousCohomology`:

`0 → lim¹ Hⁿ(G, Tₖ) → Hⁿ⁺¹(G, lim Tₖ) → lim Hⁿ⁺¹(G, Tₖ) → 0`.

In degree `0`, the canonical map `H⁰(G, lim Tₖ) → lim H⁰(G, Tₖ)` is bijective for every sequential
inverse limit in `TopRep R G`, requiring neither local compactness nor discreteness nor surjectivity
(`continuousCohomologyToLim_bijective_zero`). In positive degrees, whenever every level `Tₖ` is
discrete with surjective transitions `Tₖ₊₁ → Tₖ` and `lim¹ Hⁿ(G, Tₖ)` vanishes,
`Hⁿ⁺¹(G, lim Tₖ) → lim Hⁿ⁺¹(G, Tₖ)` is bijective (`continuousCohomologyToLim_bijective_succ`).

The final section instantiates the theory for `ℤ_[p] = lim ZMod (p ^ n)` with trivial `G`-action,
exhibiting `ℤ_[p]` as a limit cone in `TopRep ℤ G`, identifying `H⁰` and `H¹` explicitly, and
deducing the bijection `H¹(G, ℤ_[p]) → lim H¹(G, ZMod (p ^ n))`.

## Main definitions

* `TauCeti.ContinuousCohomology.homogeneousCochainsTower`,
  `TauCeti.ContinuousCohomology.homogeneousCochainsLimIso`: the tower and inverse-limit isomorphism
  for `TopRep.homogeneousCochains` over a locally compact topological group.
* `TauCeti.ContinuousCohomology.continuousCohomologyTower`,
  `TauCeti.ContinuousCohomology.continuousCohomologyToLim`,
  `TauCeti.ContinuousCohomology.continuousCohomologyLimOneTo`: the tower of continuous cohomology
  modules and the two maps of the Milnor sequence.
* `TauCeti.ContinuousCohomology.zmodPowTrivialTower`,
  `TauCeti.ContinuousCohomology.padicIntTrivialCone`: the inverse-limit presentation
  `ℤ_[p] = lim ZMod (p ^ n)` with trivial `G`-action.

## Main results

* `TauCeti.ContinuousCohomology.continuousCohomologyLimOneTo_injective`,
  `TauCeti.ContinuousCohomology.exact_continuousCohomologyLimOneTo_continuousCohomologyToLim`,
  `TauCeti.ContinuousCohomology.continuousCohomologyToLim_surjective`,
  `TauCeti.ContinuousCohomology.continuousCohomologyToLim_bijective_zero`,
  `TauCeti.ContinuousCohomology.continuousCohomologyToLim_bijective_succ`: the Milnor short exact
  sequence and `lim¹ = 0` isomorphism criterion for `continuousCohomology`.
* `TauCeti.ContinuousCohomology.padicIntTrivialCochainsLimIso`,
  `TauCeti.ContinuousCohomology.padicIntTrivialH0Equiv`,
  `TauCeti.ContinuousCohomology.padicIntTrivialH1EquivContinuousMonoidHom`,
  `TauCeti.ContinuousCohomology.padicIntTrivial_H1_lim_bijective`: the inverse-limit check for
  `ℤ_[p] = lim ZMod (p ^ n)` with trivial `G`-action.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.ContinuousCohomology

universe u v w

/-! ### Transfer to `TopRep.homogeneousCochains` and Milnor sequence for `continuousCohomology` -/

section ContinuousCohomologyMilnor

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The tower of underlying `ModuleCat` complexes of `TopRep.homogeneousCochains` for a tower
`T`. -/
@[expose]
noncomputable def homogeneousCochainsTower (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G) :
    ComplexTower.{max v w} R (ComplexShape.up ℕ) where
  obj n :=
    ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapHomologicalComplex _).obj
      (TopRep.homogeneousCochains (T.obj n))
  map f :=
    ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapHomologicalComplex _).map
      (_root_.ContinuousCohomology.cochainsMap (.id G) (T.map f))
  map_id n := by
    rw [T.map_id, _root_.ContinuousCohomology.cochainsMap_id, CategoryTheory.Functor.map_id]
  map_comp f g := by
    rw [T.map_comp,
      ← ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapHomologicalComplex _
        ).map_comp]
    exact congrArg
      ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapHomologicalComplex _).map
      (_root_.ContinuousCohomology.cochainsMap_comp (.id G) (.id G) (T.map f) (T.map g))

/-- The tower of degree-`j` continuous cohomology `R`-modules of a tower `T : ℕᵒᵖ ⥤ TopRep R G`. -/
noncomputable abbrev continuousCohomologyTower (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G) (j : ℕ) :
    ModuleTower.{max v w} R :=
  T ⋙ continuousCohomologyFunctor R G j ⋙
    forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)

/-- The canonical map `Hʲ(G, c.pt) → lim Hʲ(G, Tₙ)` on `continuousCohomology` induced by the
projections of a cone `c : Limits.Cone T`. -/
noncomputable def continuousCohomologyToLim (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G)
    (c : Limits.Cone T) (j : ℕ) :
    continuousCohomology j c.pt →ₗ[R] (continuousCohomologyTower T j).lim :=
  (continuousCohomologyTower T j).limLift
    (fun n ↦ (coeffMap (c.π.app (op n)) j).hom.toLinearMap)
    fun n ↦ by
      ext x
      change ((continuousCohomologyTower T j).transition n)
          ((coeffMap (c.π.app (op (n + 1))) j) x) = coeffMap (c.π.app (op n)) j x
      rw [ModuleTower.transition_def]
      have h : coeffMap (c.π.app (op (n + 1))) j ≫ coeffMap (T.map (homOfLE (Nat.le_succ n)).op) j
          = coeffMap (c.π.app (op n)) j := by
        rw [← coeffMap_comp, c.w (homOfLE (Nat.le_succ n)).op]
      exact ConcreteCategory.congr_hom h x

@[simp]
theorem coe_continuousCohomologyToLim_apply (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G)
    (c : Limits.Cone T) (j : ℕ) (x : continuousCohomology j c.pt) (n : ℕ) :
    (continuousCohomologyToLim T c j x : (continuousCohomologyTower T j).Product) n =
      coeffMap (c.π.app (op n)) j x :=
  ModuleTower.coe_limLift_apply (continuousCohomologyTower T j) _ _ x n

/-- In degree `0`, `H⁰(G, lim Tₙ) → lim H⁰(G, Tₙ)` is bijective for every sequential inverse limit
in `TopRep R G`, requiring neither local compactness, joint continuity, discreteness, nor
surjectivity of the transition maps. -/
theorem continuousCohomologyToLim_bijective_zero (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G)
    (c : Limits.Cone T) (hc : Limits.IsLimit c) :
    Function.Bijective (continuousCohomologyToLim T c 0) := by
  have hEmb := isEmbedding_of_isLimit T c hc
  have hRange := range_of_isLimit T c hc
  let πn (n : ℕ) : c.pt ⟶ T.obj (op n) := c.π.app (op n)
  have hzero_inj {X : TopRep.{max v w} R G} :
      Function.Injective (_root_.ContinuousCohomology.zeroIso X).hom := fun a b hab ↦ by
    have h := congrArg (_root_.ContinuousCohomology.zeroIso X).inv hab
    simpa only [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply] using h
  constructor
  · intro x₁ x₂ hx
    apply hzero_inj
    apply Subtype.ext
    apply hEmb.injective
    funext n
    have h1 := congrArg (fun u : (continuousCohomologyTower T 0).lim ↦ u.1 n) hx
    simp only [coe_continuousCohomologyToLim_apply] at h1
    have hnat₁ := ConcreteCategory.congr_hom (coeffMap_comp_zeroIso_hom (πn n)) x₁
    have hnat₂ := ConcreteCategory.congr_hom (coeffMap_comp_zeroIso_hom (πn n)) x₂
    simp only [ConcreteCategory.comp_apply] at hnat₁ hnat₂
    exact congrArg Subtype.val (hnat₁.symm.trans ((congrArg _ h1).trans hnat₂))
  · intro y
    let yn (k : ℕ) : continuousCohomology 0 (T.obj (op k)) := y.1 k
    let v (n : ℕ) : (T.obj (op n)).V :=
      ((_root_.ContinuousCohomology.zeroIso (T.obj (op n))).hom (yn n)).1
    have hvMem : v ∈ Set.range (fun x : c.pt.V ↦ fun n : ℕ ↦ (πn n).hom x) := by
      rw [hRange]
      intro n
      have hy : coeffMap (T.map (homOfLE (Nat.le_succ n)).op) 0 (yn (n + 1)) = yn n := by
        have h := (continuousCohomologyTower T 0).transition_coe_lim_succ y n
        rwa [ModuleTower.transition_def] at h
      have hnat := ConcreteCategory.congr_hom
        (coeffMap_comp_zeroIso_hom (T.map (homOfLE (Nat.le_succ n)).op)) (yn (n + 1))
      simp only [ConcreteCategory.comp_apply] at hnat
      exact congrArg Subtype.val (hnat.symm.trans (congrArg _ hy))
    obtain ⟨x, hx⟩ := hvMem
    have hx_n (n : ℕ) : (πn n).hom x = v n := congrFun hx n
    have hxInv : x ∈ c.pt.ρ.invariants := fun g ↦ hEmb.injective <| funext fun n ↦ by
      change (πn n).hom (c.pt.ρ g x) = (πn n).hom x
      rw [TopRep.hom_comm_apply (πn n) g x, hx_n n]
      exact ((_root_.ContinuousCohomology.zeroIso (T.obj (op n))).hom (yn n)).2 g
    refine ⟨(_root_.ContinuousCohomology.zeroIso c.pt).inv ⟨x, hxInv⟩,
      (continuousCohomologyTower T 0).lim_ext fun n ↦ ?_⟩
    rw [ModuleTower.limπ_apply, ModuleTower.limπ_apply, coe_continuousCohomologyToLim_apply]
    change coeffMap (πn n) 0 ((_root_.ContinuousCohomology.zeroIso c.pt).inv ⟨x, hxInv⟩) = yn n
    apply hzero_inj
    have hnat := ConcreteCategory.congr_hom (coeffMap_comp_zeroIso_hom (πn n))
      ((_root_.ContinuousCohomology.zeroIso c.pt).inv ⟨x, hxInv⟩)
    simp only [ConcreteCategory.comp_apply] at hnat
    have hinv : (_root_.ContinuousCohomology.zeroIso c.pt).hom
        ((_root_.ContinuousCohomology.zeroIso c.pt).inv ⟨x, hxInv⟩) = ⟨x, hxInv⟩ := by
      have h := ConcreteCategory.congr_hom
        (_root_.ContinuousCohomology.zeroIso c.pt).inv_hom_id ⟨x, hxInv⟩
      simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using h
    rw [hnat, hinv]
    exact Subtype.ext (hx_n n)

variable [LocallyCompactSpace G]

/-- The all-degree inhomogeneous-to-homogeneous comparison as a natural isomorphism of complex
towers. -/
noncomputable def inhomogeneousCochainsTowerIsoHomogeneous (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2) :
    inhomogeneousCochainsTower T hT ≅ homogeneousCochainsTower T :=
  NatIso.ofComponents (fun n ↦ inhomogeneousCochainsIsoHomogeneous (T.obj n) (hT (unop n)))
    fun {m n} f ↦ inhomogeneousCochainsIsoHomogeneous_coeffMap_naturality (T.map f)
      (hT (unop m)) (hT (unop n))

/-- An isomorphism of complex towers induces an isomorphism of their limit complexes. -/
private noncomputable def limComplexIsoOfIso {C D : ComplexTower.{w} R (ComplexShape.up ℕ)}
    (e : C ≅ D) : C.limComplex ≅ D.limComplex where
  hom := ComplexTower.limComplexMap e.hom
  inv := ComplexTower.limComplexMap e.inv
  hom_inv_id := by
    rw [← ComplexTower.limComplexMap_comp, e.hom_inv_id, ComplexTower.limComplexMap_id]
  inv_hom_id := by
    rw [← ComplexTower.limComplexMap_comp, e.inv_hom_id, ComplexTower.limComplexMap_id]

/-- Over a locally compact topological group `G`, the underlying `ModuleCat` complex of
`TopRep.homogeneousCochains` commutes with sequential inverse limits in `TopRep R G`. -/
noncomputable def homogeneousCochainsLimIso (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c) :
    ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapHomologicalComplex _).obj
        (TopRep.homogeneousCochains c.pt) ≅
      (homogeneousCochainsTower T).limComplex :=
  (inhomogeneousCochainsIsoHomogeneous c.pt (continuous_ρ_of_isLimit T hT c hc)).symm ≪≫
    inhomogeneousCochainsLimIso T hT c hc ≪≫
    limComplexIsoOfIso (inhomogeneousCochainsTowerIsoHomogeneous T hT)

/-- Natural isomorphism between the tower of inhomogeneous cohomology modules and
`continuousCohomologyTower T j`. -/
noncomputable def inhomogeneousCohomologyTowerIso (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2) (j : ℕ) :
    (inhomogeneousCochainsTower T hT).homology j ≅ continuousCohomologyTower T j :=
  NatIso.ofComponents (fun n ↦ inhomogeneousCohomologyIso (T.obj n) (hT (unop n)) j)
    fun {m n} f ↦ by
      change HomologicalComplex.homologyMap
          (inhomogeneousCochainsCoeffMap (T.map f) (hT (unop m)) (hT (unop n))) j ≫
          (inhomogeneousCohomologyIso (T.obj n) (hT (unop n)) j).hom =
        (inhomogeneousCohomologyIso (T.obj m) (hT (unop m)) j).hom ≫
          (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).map (coeffMap (T.map f) j)
      rw [inhomogeneousCochainsCoeffMap_def, coeffMap_def]
      exact inhomogeneousCohomologyIso_naturality (.id G) (T.map f) (hT (unop m)) (hT (unop n)) j

/-- Compatibility of `continuousCohomologyToLim` with `inhomogeneousHomologyToLim` under the
all-degree comparison isomorphism `inhomogeneousCohomologyIso`. -/
theorem continuousCohomologyToLim_comp_inhomogeneousCohomologyIso
    (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c) (j : ℕ) :
    continuousCohomologyToLim T c j ∘ₗ
        (inhomogeneousCohomologyIso c.pt (continuous_ρ_of_isLimit T hT c hc) j).hom.hom =
      (ModuleTower.limEquivOfIso (inhomogeneousCohomologyTowerIso T hT j)).toLinearMap ∘ₗ
        inhomogeneousHomologyToLim T hT c hc j := by
  refine (continuousCohomologyTower T j).lim_hom_ext fun n ↦ LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.comp_apply, ModuleTower.limπ_apply, coe_continuousCohomologyToLim_apply,
    LinearEquiv.coe_coe, ModuleTower.limEquivOfIso_apply, ModuleTower.coe_limMap_apply,
    ModuleTower.productMap_apply, coe_inhomogeneousHomologyToLim_apply]
  have hnat := ConcreteCategory.congr_hom
    (inhomogeneousCohomologyIso_naturality (.id G) (c.π.app (op n))
      (continuous_ρ_of_isLimit T hT c hc) (hT n) j) x
  rw [inhomogeneousCochainsCoeffMap_def, coeffMap_def]
  exact hnat.symm

/-- The connecting map `lim¹ Hⁿ(G, Tₖ) → Hⁿ⁺¹(G, c.pt)` of the Milnor exact sequence for
`continuousCohomology`. -/
noncomputable def continuousCohomologyLimOneTo (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c)
    [∀ n, DiscreteTopology (T.obj (op n)).V]
    (hsurj : ∀ n, Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom) (n : ℕ) :
    (continuousCohomologyTower T n).limOne →ₗ[R] continuousCohomology (n + 1) c.pt :=
  (inhomogeneousCohomologyIso c.pt (continuous_ρ_of_isLimit T hT c hc) (n + 1)).hom.hom ∘ₗ
    inhomogeneousLimOneToHomology T hT c hc hsurj n ∘ₗ
    (ModuleTower.limOneEquivOfIso (inhomogeneousCohomologyTowerIso T hT n)).symm.toLinearMap

/-- **Milnor sequence for `continuousCohomology` (injectivity at `lim¹`).** -/
theorem continuousCohomologyLimOneTo_injective (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c)
    [∀ n, DiscreteTopology (T.obj (op n)).V]
    (hsurj : ∀ n, Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom) (n : ℕ) :
    Function.Injective (continuousCohomologyLimOneTo T hT c hc hsurj n) :=
  ((inhomogeneousCohomologyIso c.pt (continuous_ρ_of_isLimit T hT c hc) (n + 1)
      ).toLinearEquiv.injective.comp
    (inhomogeneousLimOneToHomology_injective T hT c hc hsurj n)).comp
    (ModuleTower.limOneEquivOfIso (inhomogeneousCohomologyTowerIso T hT n)).symm.injective

/-- **Milnor sequence for `continuousCohomology` (exactness in the middle).** -/
theorem exact_continuousCohomologyLimOneTo_continuousCohomologyToLim
    (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c)
    [∀ n, DiscreteTopology (T.obj (op n)).V]
    (hsurj : ∀ n, Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom) (n : ℕ) :
    Function.Exact (continuousCohomologyLimOneTo T hT c hc hsurj n)
      (continuousCohomologyToLim T c (n + 1)) := by
  let eH := (inhomogeneousCohomologyIso c.pt (continuous_ρ_of_isLimit T hT c hc) (n + 1)
    ).toLinearEquiv
  let eL := ModuleTower.limEquivOfIso (inhomogeneousCohomologyTowerIso T hT (n + 1))
  let e1 := ModuleTower.limOneEquivOfIso (inhomogeneousCohomologyTowerIso T hT n)
  have hsq (u) : continuousCohomologyToLim T c (n + 1) (eH u) =
      eL (inhomogeneousHomologyToLim T hT c hc (n + 1) u) :=
    LinearMap.congr_fun
      (continuousCohomologyToLim_comp_inhomogeneousCohomologyIso T hT c hc (n + 1)) u
  intro x
  obtain ⟨u, rfl⟩ := eH.surjective x
  rw [hsq, map_eq_zero_iff _ eL.injective]
  have hex := exact_inhomogeneousLimOneToHomology_inhomogeneousHomologyToLim T hT c hc hsurj n u
  constructor
  · intro hu
    obtain ⟨y, hy⟩ := hex.1 hu
    refine ⟨e1 y, ?_⟩
    change eH (inhomogeneousLimOneToHomology T hT c hc hsurj n (e1.symm (e1 y))) = eH u
    rw [e1.symm_apply_apply, hy]
  · rintro ⟨z, hz⟩
    exact hex.2 ⟨e1.symm z, eH.injective hz⟩

/-- **Milnor sequence for `continuousCohomology` (surjectivity onto `lim`).** -/
theorem continuousCohomologyToLim_surjective (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c)
    [∀ n, DiscreteTopology (T.obj (op n)).V]
    (hsurj : ∀ n, Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom) (j : ℕ) :
    Function.Surjective (continuousCohomologyToLim T c j) := by
  have hsq := continuousCohomologyToLim_comp_inhomogeneousCohomologyIso T hT c hc j
  have hcomp : Function.Surjective (continuousCohomologyToLim T c j ∘ₗ
      (inhomogeneousCohomologyIso c.pt (continuous_ρ_of_isLimit T hT c hc) j).hom.hom) := by
    rw [hsq]
    exact (ModuleTower.limEquivOfIso (inhomogeneousCohomologyTowerIso T hT j)).surjective.comp
      (inhomogeneousHomologyToLim_surjective T hT c hc hsurj j)
  exact Function.Surjective.of_comp hcomp

/-- **Tate/Milnor inverse-limit criterion:** if every level `Tₖ` is discrete with surjective
transitions and `lim¹ Hⁿ(G, Tₖ)` vanishes, then `Hⁿ⁺¹(G, lim Tₖ) → lim Hⁿ⁺¹(G, Tₖ)` is
bijective. -/
theorem continuousCohomologyToLim_bijective_succ (T : ℕᵒᵖ ⥤ TopRep.{max v w} R G)
    (hT : ∀ n, Continuous fun p : G × (T.obj (op n)).V ↦ (T.obj (op n)).ρ p.1 p.2)
    (c : Limits.Cone T) (hc : Limits.IsLimit c)
    [∀ n, DiscreteTopology (T.obj (op n)).V]
    (hsurj : ∀ n, Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom) (n : ℕ)
    [Subsingleton (continuousCohomologyTower T n).limOne] :
    Function.Bijective (continuousCohomologyToLim T c (n + 1)) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_,
    continuousCohomologyToLim_surjective T hT c hc hsurj (n + 1)⟩
  obtain ⟨y, rfl⟩ :=
    (exact_continuousCohomologyLimOneTo_continuousCohomologyToLim T hT c hc hsurj n x).1 hx
  rw [Subsingleton.elim y 0, map_zero]

end ContinuousCohomologyMilnor

/-! ### Inverse-limit check for `ℤ_[p] = lim ZMod (p ^ n)` -/

section PadicIntCheck

variable (p : ℕ) (G : Type v) [Group G]

/-- The tower `n ↦ ZMod (p ^ n)` with trivial `G`-action in `TopRep ℤ G`. -/
@[expose]
def zmodPowTrivialTower : ℕᵒᵖ ⥤ TopRep.{0} ℤ G :=
  Functor.ofOpSequence
    (X := fun n ↦ TopRep.of (ContRepresentation.trivial ℤ G (ZMod (p ^ n))))
    fun n ↦ TopRep.ofHom
      { toLinearMap := (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))).toAddMonoidHom
          |>.toIntLinearMap
        cont := continuous_of_discreteTopology
        isIntertwining' := fun _ ↦ rfl }

/-- Every level of `zmodPowTrivialTower p G` carries the discrete topology. -/
instance zmodPowTrivialTower_discreteTopology (n : ℕ) :
    DiscreteTopology ((zmodPowTrivialTower p G).obj (op n)).V :=
  inferInstanceAs (DiscreteTopology (ZMod (p ^ n)))

/-- The consecutive transition map `ZMod (p ^ (n + 1)) → ZMod (p ^ n)` of `zmodPowTrivialTower p G`
is `ZMod.castHom`. -/
@[simp]
theorem zmodPowTrivialTower_map_succ_apply (n : ℕ) (x : ZMod (p ^ (n + 1))) :
    ((zmodPowTrivialTower p G).map (homOfLE (Nat.le_succ n)).op).hom x =
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x := by
  have h := Functor.ofOpSequence_map_homOfLE_succ
    (X := fun k ↦ TopRep.of (ContRepresentation.trivial ℤ G (ZMod (p ^ k))))
    (fun k ↦ TopRep.ofHom
      { toLinearMap := (ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))).toAddMonoidHom
          |>.toIntLinearMap
        cont := continuous_of_discreteTopology
        isIntertwining' := fun _ ↦ rfl }) n
  exact congrArg
    (fun q : TopRep.of (ContRepresentation.trivial ℤ G (ZMod (p ^ (n + 1)))) ⟶
        TopRep.of (ContRepresentation.trivial ℤ G (ZMod (p ^ n))) ↦ q.hom x) h

/-- Every level of `zmodPowTrivialTower p G` has a jointly continuous (trivial) `G`-action. -/
theorem zmodPowTrivialTower_continuous_ρ [TopologicalSpace G] (n : ℕ) :
    Continuous fun q : G × ((zmodPowTrivialTower p G).obj (op n)).V ↦
      ((zmodPowTrivialTower p G).obj (op n)).ρ q.1 q.2 :=
  continuous_snd

/-- Every transition map of the cochain tower `Cⁱ(G, ZMod (p ^ (n + 1))) → Cⁱ(G, ZMod (p ^ n))`
is surjective, for every topological group `G` and every degree `i`. -/
theorem zmodPowTrivialTower_cochains_transition_surjective [TopologicalSpace G] [ContinuousMul G]
    (i n : ℕ) :
    Function.Surjective
      (((inhomogeneousCochainsTower (zmodPowTrivialTower p G)
        (zmodPowTrivialTower_continuous_ρ p G)).term i).transition n) := by
  refine inhomogeneousCochainsTower_transition_surjective (zmodPowTrivialTower p G)
    (zmodPowTrivialTower_continuous_ρ p G) i n fun y ↦ ?_
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective (pow_dvd_pow p (Nat.le_succ n)) y
  exact ⟨x, (zmodPowTrivialTower_map_succ_apply p G n x).trans hx⟩

variable [Fact p.Prime]

/-- The cone over `zmodPowTrivialTower p G` with vertex `ℤ_[p]` (trivial `G`-action) and
projections `PadicInt.toZModPow`. -/
@[expose]
noncomputable def padicIntTrivialCone : Limits.Cone (zmodPowTrivialTower p G) where
  pt := TopRep.of (ContRepresentation.trivial ℤ G ℤ_[p])
  π := NatTrans.ofOpSequence
    (fun n ↦ TopRep.ofHom
      { toLinearMap := (PadicInt.toZModPow n).toAddMonoidHom.toIntLinearMap
        cont := PadicInt.continuous_toZModPow n
        isIntertwining' := fun _ ↦ rfl })
    fun n ↦ by
      ext x
      change PadicInt.toZModPow n x =
        ((zmodPowTrivialTower p G).map (homOfLE (Nat.le_succ n)).op).hom
          (PadicInt.toZModPow (n + 1) x)
      rw [zmodPowTrivialTower_map_succ_apply, ZMod.castHom_apply]
      exact (PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) x).symm

theorem padicIntTrivialCone_π_app_hom_apply (n : ℕ) (x : ℤ_[p]) :
    ((padicIntTrivialCone p G).π.app (op n)).hom x = PadicInt.toZModPow n x := by
  rfl

/-- `ℤ_[p]` with trivial `G`-action is the inverse limit of `zmodPowTrivialTower p G` in
`TopRep ℤ G`. -/
noncomputable def isLimitPadicIntTrivialCone : Limits.IsLimit (padicIntTrivialCone p G) := by
  refine isLimitOfIsEmbeddingRange (zmodPowTrivialTower p G) (padicIntTrivialCone p G) ?_ ?_
  · change Topology.IsEmbedding (fun x : ℤ_[p] ↦ fun n : ℕ ↦ PadicInt.toZModPow n x)
    have hfun : (fun x : ℤ_[p] ↦ fun n : ℕ ↦ PadicInt.toZModPow n x) =
        Subtype.val ∘ PadicInt.inverseLimitHomeomorph p := by
      funext x n
      change PadicInt.toZModPow n x =
        ((PadicInt.inverseLimitHomeomorph p : ℤ_[p] ≃ PadicInt.inverseLimit p) x).1 n
      simp only [PadicInt.inverseLimitHomeomorph_toEquiv, RingEquiv.coe_toEquiv,
        PadicInt.inverseLimitRingEquiv_apply, PadicInt.toInverseLimit_apply]
    rw [hfun]
    exact Topology.IsEmbedding.subtypeVal.comp (PadicInt.inverseLimitHomeomorph p).isEmbedding
  · ext y
    let y' : ∀ n : ℕ, ZMod (p ^ n) := y
    constructor
    · rintro ⟨x, rfl⟩ n
      change ((zmodPowTrivialTower p G).map (homOfLE (Nat.le_succ n)).op).hom
          (PadicInt.toZModPow (n + 1) x) = PadicInt.toZModPow n x
      rw [zmodPowTrivialTower_map_succ_apply, ZMod.castHom_apply]
      exact PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) x
    · intro hy
      have hcompat : ∀ ⦃m n : ℕ⦄, m ≤ n → (ZMod.cast (y' n) : ZMod (p ^ m)) = y' m := by
        intro m n hmn
        induction hmn with
        | refl => exact ZMod.cast_id _ (y' m)
        | @step k hmk ih =>
          have hstep : (ZMod.cast (y' (k + 1)) : ZMod (p ^ k)) = y' k := by
            have hk : ((zmodPowTrivialTower p G).map (homOfLE (Nat.le_succ k)).op).hom
                (y' (k + 1)) = y' k := hy k
            rw [zmodPowTrivialTower_map_succ_apply, ZMod.castHom_apply] at hk
            exact hk
          have hcomp := RingHom.congr_fun
            (ZMod.castHom_comp (pow_dvd_pow p hmk) (pow_dvd_pow p (Nat.le_succ k))) (y' (k + 1))
          simp only [RingHom.comp_apply, ZMod.castHom_apply] at hcomp
          rw [hstep, ih] at hcomp
          exact hcomp.symm
      have hyMem : y' ∈ PadicInt.inverseLimit p := PadicInt.mem_inverseLimit_iff.mpr hcompat
      refine ⟨PadicInt.fromInverseLimit p ⟨y', hyMem⟩, funext fun n ↦ ?_⟩
      change PadicInt.toZModPow n (PadicInt.fromInverseLimit p ⟨y', hyMem⟩) = y' n
      have h := RingHom.congr_fun (PadicInt.toZModPow_fromInverseLimit p n) ⟨y', hyMem⟩
      rwa [RingHom.comp_apply, PadicInt.inverseLimit.proj_apply] at h

variable [TopologicalSpace G] [ContinuousMul G]

/-- The inhomogeneous cochain complex of `ℤ_[p]` (trivial `G`-action) is canonically isomorphic
to the inverse limit of the inhomogeneous cochain complexes of `ZMod (p ^ n)`. -/
noncomputable def padicIntTrivialCochainsLimIso :
    inhomogeneousCochains (TopRep.of (ContRepresentation.trivial ℤ G ℤ_[p])) continuous_snd ≅
      (inhomogeneousCochainsTower (zmodPowTrivialTower p G)
        (zmodPowTrivialTower_continuous_ρ p G)).limComplex :=
  inhomogeneousCochainsLimIso (zmodPowTrivialTower p G)
    (zmodPowTrivialTower_continuous_ρ p G)
    (padicIntTrivialCone p G) (isLimitPadicIntTrivialCone p G)

/-- In degree `0`, the cohomology of `inhomogeneousCochains` on `ℤ_[p]` with trivial `G`-action is
`ℤ_[p]`. -/
noncomputable def padicIntTrivialH0Equiv :
    ((inhomogeneousCochains (TopRep.of (ContRepresentation.trivial ℤ G ℤ_[p]))
        continuous_snd).homology 0 : Type v) ≃ₗ[ℤ] ℤ_[p] :=
  (inhomogeneousCohomologyZeroLinearEquiv (TopRep.of (ContRepresentation.trivial ℤ G ℤ_[p]))
      continuous_snd).trans
    { toFun := Subtype.val
      invFun := fun x ↦ ⟨x, fun _ ↦ rfl⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- In degree `1`, the cohomology of `inhomogeneousCochains` on `ℤ_[p]` with trivial `G`-action
identifies with continuous homomorphisms `G →ₜ* Multiplicative ℤ_[p]`. -/
noncomputable def padicIntTrivialH1EquivContinuousMonoidHom :
    ((inhomogeneousCochains (TopRep.of (ContRepresentation.trivial ℤ G ℤ_[p]))
        continuous_snd).homology 1 : Type v) ≃+
      Additive (ContinuousMonoidHom G (Multiplicative ℤ_[p])) := by
  letI : DistribMulAction G (TopRep.of (ContRepresentation.trivial ℤ G ℤ_[p])).V :=
    TopRep.distribMulAction _
  haveI : ContinuousSMul G (TopRep.of (ContRepresentation.trivial ℤ G ℤ_[p])).V :=
    ⟨continuous_snd.congr fun q ↦ (TopRep.distribMulAction_smul _ q.1 q.2).symm⟩
  exact (inhomogeneousCohomologyOneAddEquiv
      (TopRep.of (ContRepresentation.trivial ℤ G ℤ_[p]))).symm.trans
    (TauCeti.ContCohomology.H1EquivOfSmulEqSelf fun _ _ ↦ rfl)

/-- For `ℤ_[p] = lim ZMod (p ^ n)` with trivial `G`-action, `H¹(G, ℤ_[p]) → lim H¹(G, ZMod (p ^ n))`
is bijective for every topological group `G`, because `H⁰(G, ZMod (p ^ n)) ≅ ZMod (p ^ n)` has
surjective transitions and hence vanishing `lim¹`. -/
theorem padicIntTrivial_H1_lim_bijective :
    Function.Bijective
      (inhomogeneousHomologyToLim (zmodPowTrivialTower p G)
        (zmodPowTrivialTower_continuous_ρ p G)
        (padicIntTrivialCone p G) (isLimitPadicIntTrivialCone p G) 1) := by
  have hsurj : ∀ n, Function.Surjective
      (((zmodPowTrivialTower p G).map (homOfLE (Nat.le_succ n)).op).hom) := fun n y ↦ by
    obtain ⟨x, hx⟩ := ZMod.castHom_surjective (pow_dvd_pow p (Nat.le_succ n)) y
    exact ⟨x, (zmodPowTrivialTower_map_succ_apply p G n x).trans hx⟩
  have : Subsingleton (((inhomogeneousCochainsTower (zmodPowTrivialTower p G)
      (zmodPowTrivialTower_continuous_ρ p G)).homology 0).limOne) := by
    refine ModuleTower.subsingleton_limOne_of_surjective
      ((inhomogeneousCochainsTower (zmodPowTrivialTower p G)
        (zmodPowTrivialTower_continuous_ρ p G)).homology 0) fun n y ↦ ?_
    let e0 (k : ℕ) :
        (((inhomogeneousCochainsTower (zmodPowTrivialTower p G)
            (zmodPowTrivialTower_continuous_ρ p G)).obj (op k)).homology 0 : Type v) ≃ₗ[ℤ]
          ZMod (p ^ k) :=
      (inhomogeneousCohomologyZeroLinearEquiv ((zmodPowTrivialTower p G).obj (op k))
          (zmodPowTrivialTower_continuous_ρ p G k)).trans
        { toFun := Subtype.val
          invFun := fun z ↦ ⟨z, fun _ ↦ rfl⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
    obtain ⟨z, hz⟩ := ZMod.castHom_surjective (pow_dvd_pow p (Nat.le_succ n)) (e0 n y)
    refine ⟨(e0 (n + 1)).symm z, (e0 n).injective ?_⟩
    have hnat := inhomogeneousCohomologyZeroLinearEquiv_naturality
      ((zmodPowTrivialTower p G).map (homOfLE (Nat.le_succ n)).op)
      (zmodPowTrivialTower_continuous_ρ p G (n + 1))
      (zmodPowTrivialTower_continuous_ρ p G n)
      ((e0 (n + 1)).symm z)
    have hinv : (inhomogeneousCohomologyZeroLinearEquiv
        ((zmodPowTrivialTower p G).obj (op (n + 1)))
        (zmodPowTrivialTower_continuous_ρ p G (n + 1)) ((e0 (n + 1)).symm z)).1 = z :=
      (e0 (n + 1)).apply_symm_apply z
    rw [ComplexTower.homology_transition]
    change (inhomogeneousCohomologyZeroLinearEquiv ((zmodPowTrivialTower p G).obj (op n))
      (zmodPowTrivialTower_continuous_ρ p G n)
      (HomologicalComplex.homologyMap
        (inhomogeneousCochainsCoeffMap ((zmodPowTrivialTower p G).map (homOfLE (Nat.le_succ n)).op)
          (zmodPowTrivialTower_continuous_ρ p G (n + 1))
          (zmodPowTrivialTower_continuous_ρ p G n)) 0 ((e0 (n + 1)).symm z))).1 = e0 n y
    rw [hnat, hinv, ← hz]
    exact zmodPowTrivialTower_map_succ_apply p G n z
  exact inhomogeneousHomologyToLim_bijective_succ (zmodPowTrivialTower p G)
    (zmodPowTrivialTower_continuous_ρ p G)
    (padicIntTrivialCone p G) (isLimitPadicIntTrivialCone p G) hsurj 0

end PadicIntCheck

end TauCeti.ContinuousCohomology
