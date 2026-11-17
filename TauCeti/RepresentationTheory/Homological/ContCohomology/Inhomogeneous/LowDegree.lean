/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inhomogeneous.Comparison

/-!
# Low-degree comparison for inhomogeneous continuous cochains

This file identifies the degree-`1` and degree-`2` cohomology of `inhomogeneousCochains X` with
Tau Ceti's explicit `H¹` and `H²` groups (`TauCeti.ContCohomology.H1` and
`TauCeti.ContCohomology.H2`) for an arbitrary jointly continuous topological representation `X`
(requiring neither discreteness of `X.V` nor local compactness of `G`).

Over a locally compact topological group `G`, composing with the all-degree comparison
`inhomogeneousCohomologyIso` produces additive equivalences
`H1AddEquivContinuousCohomology` and `H2AddEquivContinuousCohomology` between `H¹(G, X.V)` /
`H²(G, X.V)` and Mathlib's `continuousCohomology 1 X` / `continuousCohomology 2 X` for arbitrary
jointly continuous coefficients `X`. When `X = ofDiscreteModule ℤ G M` is a discrete smooth
`G`-module, these agree pointwise with the existing discrete low-degree comparisons
`TauCeti.ContCohomology.cochainEquiv0`–`cochainEquiv2` and
`TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology` /
`explicitH2AddEquivContinuousCohomology`.

## Main definitions

* `TauCeti.ContinuousCohomology.inhomogeneousCohomologyOneAddEquiv` and
  `TauCeti.ContinuousCohomology.inhomogeneousCohomologyTwoAddEquiv`: additive equivalences
  identifying `TauCeti.ContCohomology.H1 G X.V` and `H2 G X.V` with the degree-`1` and degree-`2`
  homology of `inhomogeneousCochains X`.
* `TauCeti.ContinuousCohomology.H1AddEquivContinuousCohomology` and
  `TauCeti.ContinuousCohomology.H2AddEquivContinuousCohomology`: additive equivalences identifying
  `H1 G X.V` and `H2 G X.V` with `continuousCohomology 1 X` and `continuousCohomology 2 X` for
  arbitrary jointly continuous `X`.

## Main results

* `TauCeti.ContinuousCohomology.inhomogeneousToHomogeneousEquiv_zero_ofDiscreteModule_eq`,
  `TauCeti.ContinuousCohomology.inhomogeneousToHomogeneousEquiv_one_ofDiscreteModule_eq`,
  `TauCeti.ContinuousCohomology.inhomogeneousToHomogeneousEquiv_two_ofDiscreteModule_eq`:
  agreement on cochains with `cochainEquiv0`, `cochainEquiv1`, and `cochainEquiv2`.
* `TauCeti.ContinuousCohomology.H1AddEquivContinuousCohomology_ofDiscreteModule_eq` and
  `TauCeti.ContinuousCohomology.H2AddEquivContinuousCohomology_ofDiscreteModule_eq`: agreement
  on cohomology classes with `explicitH1AddEquivContinuousCohomology` and
  `explicitH2AddEquivContinuousCohomology`.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

universe u v w

section ContinuousSMulBridge

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G]

attribute [local instance] TopRep.distribMulAction

/-- Under `TopRep.distribMulAction`, `ContinuousSMul G X.V` supplies the joint continuity
hypothesis expected by `inhomogeneousCochains`. -/
theorem continuous_ρ_of_continuousSMul (X : TopRep.{w} R G) [ContinuousSMul G X.V] :
    Continuous fun p : G × X.V ↦ X.ρ p.1 p.2 :=
  continuous_smul

end ContinuousSMulBridge

section DegreesOneAndTwo

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [ContinuousMul G]
  (X : TopRep.{w} R G)

attribute [local instance] TopRep.distribMulAction

variable [ContinuousSMul G X.V]

/-- `C(Fin 1 → G, X.V)` identifies with `TauCeti.ContCohomology.C1 G X.V` by evaluating at
`1`-tuples. -/
private def continuousMapFinOneEquiv : C(Fin 1 → G, X.V) ≃+ TauCeti.ContCohomology.C1 G X.V where
  toFun f := ⟨fun g ↦ f ![g],
    TauCeti.ContCohomology.mem_C1_iff.mpr <|
      f.continuous.comp (continuous_pi fun i ↦ by fin_cases i; exact continuous_id)⟩
  invFun c := ⟨fun g ↦ c.1 (g 0),
    (TauCeti.ContCohomology.mem_C1_iff.mp c.2).comp (continuous_apply 0)⟩
  left_inv f := ContinuousMap.ext fun g ↦ congrArg f (funext fun i ↦ by fin_cases i; rfl)
  right_inv _ := Subtype.ext (funext fun _ ↦ rfl)
  map_add' _ _ := rfl

/-- `C(Fin 2 → G, X.V)` identifies with `TauCeti.ContCohomology.C2 G X.V` by evaluating at pairs
`![g, h]`. -/
private def continuousMapFinTwoEquiv : C(Fin 2 → G, X.V) ≃+ TauCeti.ContCohomology.C2 G X.V where
  toFun f := ⟨fun p ↦ f ![p.1, p.2],
    TauCeti.ContCohomology.mem_C2_iff.mpr <|
      f.continuous.comp (continuous_pi fun i ↦ by
        fin_cases i
        · exact continuous_fst
        · exact continuous_snd)⟩
  invFun c := ⟨fun g ↦ c.1 (g 0, g 1),
    (TauCeti.ContCohomology.mem_C2_iff.mp c.2).comp
      ((continuous_apply 0).prodMk (continuous_apply 1))⟩
  left_inv f := ContinuousMap.ext fun g ↦ congrArg f (funext fun i ↦ by fin_cases i <;> rfl)
  right_inv _ := Subtype.ext (funext fun _ ↦ rfl)
  map_add' _ _ := rfl

/-- The kernel of `d¹` in `inhomogeneousCochains X` is `TauCeti.ContCohomology.Z1 G X.V`. -/
private def inhomogeneousCocyclesOneEquiv :
    TauCeti.ContCohomology.Z1 G X.V ≃+
      LinearMap.ker (((inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).sc' 0 1 2).g.hom)
      where
  toFun c :=
    ⟨(continuousMapFinOneEquiv X).symm ⟨c.1, TauCeti.ContCohomology.Z1_le_C1 G X.V c.2⟩, by
      change ((inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).d 1 2).hom
          ((continuousMapFinOneEquiv X).symm ⟨c.1, TauCeti.ContCohomology.Z1_le_C1 G X.V c.2⟩) = 0
      ext g
      rw [inhomogeneousCochains_d_apply, inhomogeneousCochainsD_one_apply]
      change X.ρ (g 0) (c.1 (g 1)) - c.1 (g 0 * g 1) + c.1 (g 0) = 0
      have hd1 := congrFun (TauCeti.ContCohomology.d1_apply_eq_zero_iff.mpr
        ((TauCeti.ContCohomology.mem_Z1_iff.mp c.2).2)) (g 0, g 1)
      simpa only [TauCeti.ContCohomology.d1_apply, TopRep.distribMulAction_smul, Pi.zero_apply]
        using hd1⟩
  invFun c :=
    let f : C(Fin 1 → G, X.V) := c.1
    ⟨((continuousMapFinOneEquiv X) f).1, by
      rw [TauCeti.ContCohomology.mem_Z1_iff]
      refine ⟨TauCeti.ContCohomology.mem_C1_iff.mp ((continuousMapFinOneEquiv X) f).2,
        TauCeti.ContCohomology.d1_apply_eq_zero_iff.mp (funext fun ⟨g, h⟩ ↦ ?_)⟩
      have hker : ((inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).d 1 2).hom f = 0 :=
        c.2
      have hc := congrArg (fun u : C(Fin 2 → G, X.V) ↦ u ![g, h]) hker
      rw [inhomogeneousCochains_d_apply, inhomogeneousCochainsD_one_apply] at hc
      rw [TauCeti.ContCohomology.d1_apply, TopRep.distribMulAction_smul]
      change X.ρ g (f ![h]) - f ![g * h] + f ![g] = 0
      simpa only [ContinuousMap.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using hc⟩
  left_inv _ := Subtype.ext (funext fun _ ↦ rfl)
  right_inv c := by
    let f : C(Fin 1 → G, X.V) := c.1
    exact Subtype.ext (ContinuousMap.ext fun g ↦
      congrArg f (funext fun (i : Fin 1) ↦ by fin_cases i; rfl))
  map_add' _ _ := rfl

/-- **Degree one of `inhomogeneousCochains` is `TauCeti.ContCohomology.H1`**, for an arbitrary
jointly continuous topological representation `X` (no discreteness or local compactness
needed). -/
noncomputable def inhomogeneousCohomologyOneAddEquiv :
    TauCeti.ContCohomology.H1 G X.V ≃+
      (inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).homology 1 := by
  let K := inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)
  let S := K.sc' 0 1 2
  let q : TauCeti.ContCohomology.Z1 G X.V →+
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    (Submodule.mkQ (LinearMap.range S.moduleCatToCycles)).toAddMonoidHom.comp
      (inhomogeneousCocyclesOneEquiv X).toAddMonoidHom
  have hsurj : Function.Surjective q :=
    (Submodule.mkQ_surjective _).comp (inhomogeneousCocyclesOneEquiv X).surjective
  have hker : (TauCeti.ContCohomology.B1 G X.V).addSubgroupOf (TauCeti.ContCohomology.Z1 G X.V) =
      q.ker := by
    ext c
    rw [AddSubgroup.mem_addSubgroupOf, TauCeti.ContCohomology.mem_B1_iff,
      AddMonoidHom.mem_ker]
    change groupCohomology.IsCoboundary₁ c.1 ↔
      Submodule.Quotient.mk (inhomogeneousCocyclesOneEquiv X c) =
        (0 : LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨ContinuousMap.const (Fin 0 → G) m, Subtype.ext ?_⟩
      change (K.d 0 1).hom (ContinuousMap.const (Fin 0 → G) m) =
        (continuousMapFinOneEquiv X).symm ⟨c.1, TauCeti.ContCohomology.Z1_le_C1 G X.V c.2⟩
      ext g
      rw [inhomogeneousCochains_d_apply, inhomogeneousCochainsD_zero_apply,
        ContinuousMap.const_apply]
      exact hm (g 0)
    · rintro ⟨f, hf⟩
      let f' : C(Fin 0 → G, X.V) := f
      refine ⟨f' Fin.elim0, fun g ↦ ?_⟩
      have h := congrArg (fun u : LinearMap.ker S.g.hom ↦
        let f_u : C(Fin 1 → G, X.V) := u.1; f_u ![g]) hf
      have hL : (let f_u : C(Fin 1 → G, X.V) := (S.moduleCatToCycles f).1; f_u ![g]) =
          (K.d 0 1).hom f' ![g] := rfl
      have hR : (let f_u : C(Fin 1 → G, X.V) := (inhomogeneousCocyclesOneEquiv X c).1; f_u ![g]) =
          c.1 g := by
        change c.1 (![g] 0) = c.1 g
        simp only [Matrix.cons_val_zero]
      rw [hL, hR, inhomogeneousCochains_d_apply, inhomogeneousCochainsD_zero_apply] at h
      exact h
  exact (QuotientAddGroup.liftEquiv _ hsurj hker).trans
    (S.moduleCatHomologyIso.symm ≪≫
      (K.homologyIsoSc' 0 1 2 (by simp) (by simp)).symm).toLinearEquiv.toAddEquiv

private theorem inhomogeneousCohomologyOneAddEquiv_mk (c : TauCeti.ContCohomology.Z1 G X.V) :
    inhomogeneousCohomologyOneAddEquiv X (QuotientAddGroup.mk c) =
      ((inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).homologyIsoSc' 0 1 2
          (by simp) (by simp)).inv
        (((inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).sc' 0 1 2
          ).moduleCatHomologyIso.inv
          (Submodule.Quotient.mk (inhomogeneousCocyclesOneEquiv X c))) :=
  rfl

/-- The kernel of `d²` in `inhomogeneousCochains X` is `TauCeti.ContCohomology.Z2 G X.V`. -/
private def inhomogeneousCocyclesTwoEquiv :
    TauCeti.ContCohomology.Z2 G X.V ≃+
      LinearMap.ker (((inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).sc' 1 2 3).g.hom)
      where
  toFun c :=
    ⟨(continuousMapFinTwoEquiv X).symm ⟨c.1, TauCeti.ContCohomology.Z2_le_C2 G X.V c.2⟩, by
      change ((inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).d 2 3).hom
          ((continuousMapFinTwoEquiv X).symm ⟨c.1, TauCeti.ContCohomology.Z2_le_C2 G X.V c.2⟩) = 0
      ext g
      rw [inhomogeneousCochains_d_apply, inhomogeneousCochainsD_two_apply]
      change X.ρ (g 0) (c.1 (g 1, g 2)) - c.1 (g 0 * g 1, g 2) + c.1 (g 0, g 1 * g 2) -
        c.1 (g 0, g 1) = 0
      have hd2 := congrFun (TauCeti.ContCohomology.d2_apply_eq_zero_iff.mpr
        ((TauCeti.ContCohomology.mem_Z2_iff.mp c.2).2)) (g 0, g 1, g 2)
      simpa only [TauCeti.ContCohomology.d2_apply, TopRep.distribMulAction_smul, Pi.zero_apply]
        using hd2⟩
  invFun c :=
    let f : C(Fin 2 → G, X.V) := c.1
    ⟨((continuousMapFinTwoEquiv X) f).1, by
      rw [TauCeti.ContCohomology.mem_Z2_iff]
      refine ⟨TauCeti.ContCohomology.mem_C2_iff.mp ((continuousMapFinTwoEquiv X) f).2,
        TauCeti.ContCohomology.d2_apply_eq_zero_iff.mp (funext fun ⟨g, h, k⟩ ↦ ?_)⟩
      have hker : ((inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).d 2 3).hom f = 0 :=
        c.2
      have hc := congrArg (fun u : C(Fin 3 → G, X.V) ↦ u ![g, h, k]) hker
      rw [inhomogeneousCochains_d_apply, inhomogeneousCochainsD_two_apply] at hc
      rw [TauCeti.ContCohomology.d2_apply, TopRep.distribMulAction_smul]
      change X.ρ g (f ![h, k]) - f ![g * h, k] + f ![g, h * k] - f ![g, h] = 0
      simpa only [ContinuousMap.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using hc⟩
  left_inv _ := Subtype.ext (funext fun _ ↦ rfl)
  right_inv c := by
    let f : C(Fin 2 → G, X.V) := c.1
    exact Subtype.ext (ContinuousMap.ext fun g ↦
      congrArg f (funext fun (i : Fin 2) ↦ by fin_cases i <;> rfl))
  map_add' _ _ := rfl

/-- **Degree two of `inhomogeneousCochains` is `TauCeti.ContCohomology.H2`**, for an arbitrary
jointly continuous topological representation `X`. -/
noncomputable def inhomogeneousCohomologyTwoAddEquiv :
    TauCeti.ContCohomology.H2 G X.V ≃+
      (inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).homology 2 := by
  let K := inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)
  let S := K.sc' 1 2 3
  let q : TauCeti.ContCohomology.Z2 G X.V →+
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    (Submodule.mkQ (LinearMap.range S.moduleCatToCycles)).toAddMonoidHom.comp
      (inhomogeneousCocyclesTwoEquiv X).toAddMonoidHom
  have hsurj : Function.Surjective q :=
    (Submodule.mkQ_surjective _).comp (inhomogeneousCocyclesTwoEquiv X).surjective
  have hker : (TauCeti.ContCohomology.B2 G X.V).addSubgroupOf (TauCeti.ContCohomology.Z2 G X.V) =
      q.ker := by
    ext c
    rw [AddSubgroup.mem_addSubgroupOf, TauCeti.ContCohomology.mem_B2_iff',
      AddMonoidHom.mem_ker]
    change (∃ f : G → X.V, Continuous f ∧ ∀ g h : G, g • f h - f (g * h) + f g = c.1 (g, h)) ↔
      Submodule.Quotient.mk (inhomogeneousCocyclesTwoEquiv X c) =
        (0 : LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨f, hfcont, hf⟩
      let f0 : C(Fin 1 → G, X.V) :=
        (continuousMapFinOneEquiv X).symm ⟨f, TauCeti.ContCohomology.mem_C1_iff.mpr hfcont⟩
      refine ⟨f0, Subtype.ext ?_⟩
      change (K.d 1 2).hom f0 =
        (continuousMapFinTwoEquiv X).symm ⟨c.1, TauCeti.ContCohomology.Z2_le_C2 G X.V c.2⟩
      ext g
      rw [inhomogeneousCochains_d_apply, inhomogeneousCochainsD_one_apply]
      exact hf (g 0) (g 1)
    · rintro ⟨f, hf⟩
      let f' : C(Fin 1 → G, X.V) := f
      refine ⟨((continuousMapFinOneEquiv X) f').1,
        TauCeti.ContCohomology.mem_C1_iff.mp ((continuousMapFinOneEquiv X) f').2, fun g h ↦ ?_⟩
      have h' := congrArg (fun u : LinearMap.ker S.g.hom ↦
        let f_u : C(Fin 2 → G, X.V) := u.1; f_u ![g, h]) hf
      have hL : (let f_u : C(Fin 2 → G, X.V) := (S.moduleCatToCycles f).1; f_u ![g, h]) =
          (K.d 1 2).hom f' ![g, h] := rfl
      have hR : (let f_u : C(Fin 2 → G, X.V) := (inhomogeneousCocyclesTwoEquiv X c).1;
          f_u ![g, h]) = c.1 (g, h) := by
        change c.1 (![g, h] 0, ![g, h] 1) = c.1 (g, h)
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hL, hR, inhomogeneousCochains_d_apply, inhomogeneousCochainsD_one_apply] at h'
      change X.ρ g (f' ![h]) - f' ![g * h] + f' ![g] = c.1 (g, h)
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using h'
  exact (QuotientAddGroup.liftEquiv _ hsurj hker).trans
    (S.moduleCatHomologyIso.symm ≪≫
      (K.homologyIsoSc' 1 2 3 (by simp) (by simp)).symm).toLinearEquiv.toAddEquiv

private theorem inhomogeneousCohomologyTwoAddEquiv_mk (c : TauCeti.ContCohomology.Z2 G X.V) :
    inhomogeneousCohomologyTwoAddEquiv X (QuotientAddGroup.mk c) =
      ((inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).homologyIsoSc' 1 2 3
          (by simp) (by simp)).inv
        (((inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).sc' 1 2 3
          ).moduleCatHomologyIso.inv
          (Submodule.Quotient.mk (inhomogeneousCocyclesTwoEquiv X c))) :=
  rfl

end DegreesOneAndTwo

section LowDegreeComparison

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  (X : TopRep.{max v w} R G)

attribute [local instance] TopRep.distribMulAction

variable [ContinuousSMul G X.V]

/-- **Degree-one continuous cohomology for arbitrary jointly continuous coefficients.** Over a
locally compact group `G`, `TauCeti.ContCohomology.H1 G X.V` (continuous crossed homomorphisms
modulo principal ones) is additively equivalent to `continuousCohomology 1 X`. -/
noncomputable def H1AddEquivContinuousCohomology :
    TauCeti.ContCohomology.H1 G X.V ≃+ continuousCohomology 1 X :=
  (inhomogeneousCohomologyOneAddEquiv X).trans
    (inhomogeneousCohomologyIso X (continuous_ρ_of_continuousSMul X) 1).toLinearEquiv.toAddEquiv

/-- **Degree-two continuous cohomology for arbitrary jointly continuous coefficients.** Over a
locally compact group `G`, `TauCeti.ContCohomology.H2 G X.V` (continuous `2`-cocycles modulo
coboundaries) is additively equivalent to `continuousCohomology 2 X`. -/
noncomputable def H2AddEquivContinuousCohomology :
    TauCeti.ContCohomology.H2 G X.V ≃+ continuousCohomology 2 X :=
  (inhomogeneousCohomologyTwoAddEquiv X).trans
    (inhomogeneousCohomologyIso X (continuous_ρ_of_continuousSMul X) 2).toLinearEquiv.toAddEquiv

/-- Transporting a cocycle `c` of `inhomogeneousCochains X` (in the explicit short complex
`K.sc' n (n + 1) (n + 2)`) across `inhomogeneousCohomologyIso` produces the canonical cohomology
class of its image under `inhomogeneousToHomogeneousEquiv`. -/
private theorem inhomogeneousCohomologyIso_hom_sc'_inv (n : ℕ)
    (c : LinearMap.ker (((inhomogeneousCochains X
      (continuous_ρ_of_continuousSMul X)).sc' n (n + 1) (n + 2)).g.hom)) :
    (inhomogeneousCohomologyIso X (continuous_ρ_of_continuousSMul X) (n + 1)).hom
        (((inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).homologyIsoSc' n (n + 1)
          (n + 2) (by simp) (by simp)).inv
          ((((inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).sc' n (n + 1)
            (n + 2)).moduleCatHomologyIso.inv (Submodule.Quotient.mk c)))) =
      (TopRep.homogeneousCochains X).homologyπ (n + 1)
        ((TopRep.homogeneousCochains X).cyclesMkOfEq
          (inhomogeneousToHomogeneousEquiv X (continuous_ρ_of_continuousSMul X) (n + 1) c.1)
          (n + 2) (CochainComplex.next ℕ (n + 1)) (by
            rw [inhomogeneousToHomogeneousEquiv_d]
            have hc : (inhomogeneousCochainsD X (continuous_ρ_of_continuousSMul X) (n + 1)).hom
                c.1 = 0 := by
              let f : C(Fin (n + 1) → G, X.V) := c.1
              have h : ((inhomogeneousCochains X (continuous_ρ_of_continuousSMul X)).d (n + 1)
                  (n + 2)).hom f = 0 := c.2
              rwa [inhomogeneousCochains_d] at h
            rw [hc, map_zero])) := by
  let hX := continuous_ρ_of_continuousSMul X
  let K := inhomogeneousCochains X hX
  let S' := K.sc' n (n + 1) (n + 2)
  let S := (TopRep.homogeneousCochains X).sc (n + 1)
  let F := forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)
  let φ := inhomogeneousCochainsIsoHomogeneous X hX
  let z : K.cycles (n + 1) :=
    (K.cyclesIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).inv (S'.moduleCatCyclesIso.inv c)
  have hstep1 : (K.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).inv
      (S'.moduleCatHomologyIso.inv (Submodule.Quotient.mk c)) = K.homologyπ (n + 1) z := by
    have h1 := ConcreteCategory.congr_hom S'.moduleCatCyclesIso_inv_π c
    have h2 := ConcreteCategory.congr_hom
      (K.π_homologyIsoSc'_inv n (n + 1) (n + 2) (by simp) (by simp))
      (S'.moduleCatCyclesIso.inv c)
    simp only [ConcreteCategory.comp_apply] at h1 h2
    change (K.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).inv
      (S'.moduleCatHomologyIso.inv (S'.moduleCatLeftHomologyData.π c)) = K.homologyπ (n + 1) z
    rw [← h1]
    exact h2
  rw [hstep1]
  have hstep2 := homologyπ_comp_inhomogeneousCohomologyIso_hom X hX (n + 1)
  have hval := ConcreteCategory.congr_hom hstep2 z
  simp only [ConcreteCategory.comp_apply] at hval
  refine hval.trans ?_
  change (TopRep.homogeneousCochains X).homologyπ (n + 1) _ = _
  congr 1
  apply (TopRep.homogeneousCochains X).iCycles_injective (n + 1)
  rw [HomologicalComplex.iCycles_cyclesMkOfEq]
  have hi1 : F.map S.iCycles ((S.mapCyclesIso F).hom (HomologicalComplex.cyclesMap φ.hom (n + 1) z))
      = (S.map F).iCycles (HomologicalComplex.cyclesMap φ.hom (n + 1) z) :=
    ConcreteCategory.congr_hom (S.mapCyclesIso_hom_iCycles F)
      (HomologicalComplex.cyclesMap φ.hom (n + 1) z)
  have hi2 : (S.map F).iCycles (HomologicalComplex.cyclesMap φ.hom (n + 1) z) =
      φ.hom.f (n + 1) (K.iCycles (n + 1) z) :=
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ.hom (n + 1)) z
  have hi3 : K.iCycles (n + 1) z = c.1 := by
    have h3a := ConcreteCategory.congr_hom
      (K.cyclesIsoSc'_inv_iCycles n (n + 1) (n + 2) (by simp) (by simp))
      (S'.moduleCatCyclesIso.inv c)
    have h3b := ConcreteCategory.congr_hom S'.moduleCatCyclesIso_inv_iCycles c
    simp only [ConcreteCategory.comp_apply] at h3a
    exact h3a.trans h3b
  refine (hi1.trans hi2).trans ?_
  rw [hi3]
  exact inhomogeneousCochainsIsoHomogeneous_hom_f_apply X hX (n + 1) c.1

end LowDegreeComparison

/-! ### Compatibility with the discrete low-degree comparisons -/

section DiscreteCompatibility

variable {G M : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- In degree `0`, `inhomogeneousToHomogeneousEquiv` on a discrete `ℤ`-module agrees with
`TauCeti.ContCohomology.cochainEquiv0`. -/
theorem inhomogeneousToHomogeneousEquiv_zero_ofDiscreteModule_eq (m : M) :
    inhomogeneousToHomogeneousEquiv (ofDiscreteModule ℤ G M)
        (continuous_ρ_of_isSmoothDiscrete (ofDiscreteModule_isSmoothDiscrete ℤ G M)) 0
        (ContinuousMap.const _ m) =
      TauCeti.ContCohomology.cochainEquiv0 G M m := by
  apply Subtype.ext
  apply (resolutionXEquiv (ofDiscreteModule ℤ G M) 1).injective
  ext g
  rw [resolutionXEquiv_inhomogeneousToHomogeneousEquiv_apply, homogenize_apply,
    resolutionXEquiv_one_apply, TauCeti.ContCohomology.cochainEquiv0_apply]
  rfl

/-- In degree `1`, `inhomogeneousToHomogeneousEquiv` on a discrete `ℤ`-module agrees with
`TauCeti.ContCohomology.cochainEquiv1`. -/
theorem inhomogeneousToHomogeneousEquiv_one_ofDiscreteModule_eq
    (c : TauCeti.ContCohomology.C1 G M) :
    inhomogeneousToHomogeneousEquiv (ofDiscreteModule ℤ G M)
        (continuous_ρ_of_isSmoothDiscrete (ofDiscreteModule_isSmoothDiscrete ℤ G M)) 1
        ⟨fun g ↦ c.1 (g 0),
          (TauCeti.ContCohomology.mem_C1_iff.mp c.2).comp (continuous_apply 0)⟩ =
      TauCeti.ContCohomology.cochainEquiv1 G M c := by
  apply Subtype.ext
  apply (resolutionXEquiv (ofDiscreteModule ℤ G M) 2).injective
  ext g
  rw [resolutionXEquiv_inhomogeneousToHomogeneousEquiv_apply, homogenize_apply,
    resolutionXEquiv_two_apply, TauCeti.ContCohomology.cochainEquiv1_apply,
    TauCeti.ContCohomology.homogeneous1_apply]
  rfl

/-- In degree `2`, `inhomogeneousToHomogeneousEquiv` on a discrete `ℤ`-module agrees with
`TauCeti.ContCohomology.cochainEquiv2`. -/
theorem inhomogeneousToHomogeneousEquiv_two_ofDiscreteModule_eq
    (c : TauCeti.ContCohomology.C2 G M) :
    inhomogeneousToHomogeneousEquiv (ofDiscreteModule ℤ G M)
        (continuous_ρ_of_isSmoothDiscrete (ofDiscreteModule_isSmoothDiscrete ℤ G M)) 2
        ⟨fun g ↦ c.1 (g 0, g 1),
          (TauCeti.ContCohomology.mem_C2_iff.mp c.2).comp
            ((continuous_apply 0).prodMk (continuous_apply 1))⟩ =
      TauCeti.ContCohomology.cochainEquiv2 G M c := by
  apply Subtype.ext
  apply (resolutionXEquiv (ofDiscreteModule ℤ G M) 3).injective
  ext g
  rw [resolutionXEquiv_inhomogeneousToHomogeneousEquiv_apply, homogenize_apply,
    resolutionXEquiv_three_apply, TauCeti.ContCohomology.cochainEquiv2_apply,
    TauCeti.ContCohomology.homogeneous2_apply]
  rfl

attribute [local instance] TopRep.distribMulAction

local instance : ContinuousSMul G (ofDiscreteModule ℤ G M).V :=
  ⟨continuous_ρ_of_isSmoothDiscrete (ofDiscreteModule_isSmoothDiscrete ℤ G M)⟩

/-- In degree `1`, the all-degree comparison on `ofDiscreteModule ℤ G M` agrees with
`TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology`. -/
theorem H1AddEquivContinuousCohomology_ofDiscreteModule_eq
    (x : TauCeti.ContCohomology.H1 G M) :
    H1AddEquivContinuousCohomology (ofDiscreteModule ℤ G M) x =
      TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology G M x := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_apply]
    let c' : TauCeti.ContCohomology.Z1 G (ofDiscreteModule ℤ G M).V := c
    change H1AddEquivContinuousCohomology (ofDiscreteModule ℤ G M) (QuotientAddGroup.mk c') = _
    rw [H1AddEquivContinuousCohomology, AddEquiv.trans_apply,
      inhomogeneousCohomologyOneAddEquiv_mk]
    change (inhomogeneousCohomologyIso (ofDiscreteModule ℤ G M) _ 1).hom _ = _
    rw [inhomogeneousCohomologyIso_hom_sc'_inv]
    congr 1
    apply (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles_injective 1
    rw [HomologicalComplex.iCycles_cyclesMkOfEq]
    refine (inhomogeneousToHomogeneousEquiv_one_ofDiscreteModule_eq
      ⟨c.1, TauCeti.ContCohomology.Z1_le_C1 G M c.2⟩).trans ?_
    exact (TauCeti.ContCohomology.iCycles_cocycleEquiv1 G M c).symm

/-- In degree `2`, the all-degree comparison on `ofDiscreteModule ℤ G M` agrees with
`TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology`. -/
theorem H2AddEquivContinuousCohomology_ofDiscreteModule_eq
    (x : TauCeti.ContCohomology.H2 G M) :
    H2AddEquivContinuousCohomology (ofDiscreteModule ℤ G M) x =
      TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology G M x := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology_apply]
    let c' : TauCeti.ContCohomology.Z2 G (ofDiscreteModule ℤ G M).V := c
    change H2AddEquivContinuousCohomology (ofDiscreteModule ℤ G M) (QuotientAddGroup.mk c') = _
    rw [H2AddEquivContinuousCohomology, AddEquiv.trans_apply,
      inhomogeneousCohomologyTwoAddEquiv_mk]
    change (inhomogeneousCohomologyIso (ofDiscreteModule ℤ G M) _ 2).hom _ = _
    rw [inhomogeneousCohomologyIso_hom_sc'_inv]
    congr 1
    apply (TopRep.homogeneousCochains (ofDiscreteModule ℤ G M)).iCycles_injective 2
    rw [HomologicalComplex.iCycles_cyclesMkOfEq]
    refine (inhomogeneousToHomogeneousEquiv_two_ofDiscreteModule_eq
      ⟨c.1, TauCeti.ContCohomology.Z2_le_C2 G M c.2⟩).trans ?_
    exact (TauCeti.ContCohomology.iCycles_cocycleEquiv2 G M c).symm

end DiscreteCompatibility

end TauCeti.ContinuousCohomology
