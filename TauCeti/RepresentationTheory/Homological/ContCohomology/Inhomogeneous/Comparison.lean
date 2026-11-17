/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import Mathlib.Topology.CompactOpen
public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology
public import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inhomogeneous.Basic

/-!
# Comparison between inhomogeneous and homogeneous continuous cochains

For a locally compact topological group `G`, a topological ring `R`, and a topological
representation `X : TopRep R G` with jointly continuous action `G × X.V → X.V`, this file
constructs the all-degree isomorphism between the inhomogeneous continuous cochain complex
`inhomogeneousCochainsTop X hX` (respectively `inhomogeneousCochains X hX`) and Mathlib's
homogeneous cochain complex `TopRep.homogeneousCochains X`, together with its consequences on
continuous cohomology in every degree.

First, iterated currying (`resolutionXEquiv`) identifies `(TopRep.resolutionX X n).V`, the
`n`-th term of Mathlib's coinduced resolution, with `C(Fin n → G, X.V)` as a topological
`R`-module for the compact-open topology, sending the `G`-action to diagonal translation and the
resolution differential `TopRep.d X n` to the alternating face-map sum. Next, homogenization and
evaluation at partial products (`inhomogeneousToHomogeneousEquiv`) identify `C(Fin n → G, X.V)`
with the `G`-invariants of `TopRep.resolutionX X (n + 1)` as topological `R`-modules, intertwining
the inhomogeneous and homogeneous differentials.

This yields isomorphisms of cochain complexes and of cohomology objects both in `TopModuleCat R`
(preserving the quotient topology on continuous cohomology) and in `ModuleCat R` (after forgetting
topologies), natural in compatible pairs `(φ : H →ₜ* G, f : TopRep.res φ X ⟶ Y)`. In degree `0`,
`inhomogeneousCohomologyZeroLinearEquiv` and `inhomogeneousCohomologyZeroIso` identify the zeroth
cohomology with `X.ρ.invariants` compatibly with Mathlib's `ContinuousCohomology.zeroIso`.

## Main definitions

* `TauCeti.ContinuousCohomology.resolutionXEquiv`: iterated compact-open currying identifying
  `(TopRep.resolutionX X n).V` with `C(Fin n → G, X.V)`.
* `TauCeti.ContinuousCohomology.inhomogeneousToHomogeneousEquiv`: topological `R`-linear
  equivalence `C(Fin n → G, X.V) ≃L[R] (TopRep.resolutionX X (n + 1)).ρ.invariants`.
* `TauCeti.ContinuousCohomology.inhomogeneousCochainsTopIsoHomogeneous` and
  `TauCeti.ContinuousCohomology.inhomogeneousCohomologyTopIso`: the all-degree cochain and
  cohomology isomorphisms in `TopModuleCat R`.
* `TauCeti.ContinuousCohomology.inhomogeneousCochainsIsoHomogeneous` and
  `TauCeti.ContinuousCohomology.inhomogeneousCohomologyIso`: the all-degree cochain and cohomology
  isomorphisms in `ModuleCat R`.
* `TauCeti.ContinuousCohomology.inhomogeneousCohomologyZeroLinearEquiv` and
  `TauCeti.ContinuousCohomology.inhomogeneousCohomologyZeroIso`: degree-zero identification with
  `X.ρ.invariants`.

## Main results

* `TauCeti.ContinuousCohomology.resolutionXEquiv_ρ_apply`,
  `TauCeti.ContinuousCohomology.resolutionXEquiv_d_apply`,
  `TauCeti.ContinuousCohomology.resolutionXEquiv_resolutionMap_apply`: transport of the `G`-action,
  resolution differential, and compatible-pair maps under iterated currying.
* `TauCeti.ContinuousCohomology.inhomogeneousCochainsTopIsoHomogeneous_naturality`,
  `TauCeti.ContinuousCohomology.inhomogeneousCochainsIsoHomogeneous_naturality`,
  `TauCeti.ContinuousCohomology.inhomogeneousCohomologyIso_naturality`: naturality in compatible
  pairs.
* `TauCeti.ContinuousCohomology.inhomogeneousCohomologyIso_zero_comp_zeroIso`: compatibility in
  degree `0` with `ContinuousCohomology.zeroIso`.

## References

* K. Rubin, *Euler Systems*, Appendix B, §2, Definition 2.1, p. 151.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

universe u v w

/-! ### Iterated compact-open currying of the coinduced resolution -/

section IteratedCurrying

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Splitting off the leading coordinate of a finite tuple `Fin (n + 1) → G` is a homeomorphism. -/
private def finSuccHomeomorph (n : ℕ) : G × (Fin n → G) ≃ₜ (Fin (n + 1) → G) where
  toFun p := Fin.cons p.1 p.2
  invFun g := (g 0, Fin.tail g)
  left_inv p := by
    cases p
    refine Prod.ext ?_ ?_ <;> simp
  right_inv g := Fin.cons_self_tail g
  continuous_toFun := continuous_pi fun i ↦
    Fin.cases continuous_fst (fun j ↦ (continuous_apply j).comp continuous_snd) i
  continuous_invFun := (continuous_apply 0).prodMk (continuous_pi fun i ↦ continuous_apply i.succ)

/-- One inductive step of iterated compact-open currying as a topological `R`-linear
equivalence. -/
private def resolutionXEquivStep {V : Type (max v w)} [AddCommGroup V] [Module R V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul R V]
    {W : Type (max v w)} [AddCommGroup W] [Module R W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul R W]
    {n : ℕ} (e : V ≃L[R] C(Fin n → G, W)) :
    C(G, V) ≃L[R] C(Fin (n + 1) → G, W) :=
  let ef : C(V, C(Fin n → G, W)) := ⟨e, e.continuous⟩
  let eg : C(C(Fin n → G, W), V) := ⟨e.symm, e.symm.continuous⟩
  let hf : C(G × (Fin n → G), Fin (n + 1) → G) :=
    ⟨finSuccHomeomorph n, (finSuccHomeomorph n).continuous⟩
  let hs : C(Fin (n + 1) → G, G × (Fin n → G)) :=
    ⟨(finSuccHomeomorph n).symm, (finSuccHomeomorph n).symm.continuous⟩
  let post : C(G, V) ≃L[R] C(G, C(Fin n → G, W)) :=
    { toFun F := ef.comp F
      invFun F := eg.comp F
      left_inv F := ContinuousMap.ext fun g ↦ e.symm_apply_apply (F g)
      right_inv F := ContinuousMap.ext fun g ↦ e.apply_symm_apply (F g)
      map_add' _ _ := ContinuousMap.ext fun _ ↦ map_add e _ _
      map_smul' _ _ := ContinuousMap.ext fun _ ↦ map_smul e _ _
      continuous_toFun := ContinuousMap.continuous_postcomp ef
      continuous_invFun := ContinuousMap.continuous_postcomp eg }
  let uncurry : C(G, C(Fin n → G, W)) ≃L[R] C(G × (Fin n → G), W) :=
    { toEquiv := (Homeomorph.curry (X := G) (Y := Fin n → G) (Z := W)).symm.toEquiv
      map_add' _ _ := ContinuousMap.ext fun _ ↦ rfl
      map_smul' _ _ := ContinuousMap.ext fun _ ↦ rfl
      continuous_toFun := (Homeomorph.curry (X := G) (Y := Fin n → G) (Z := W)).symm.continuous
      continuous_invFun := (Homeomorph.curry (X := G) (Y := Fin n → G) (Z := W)).continuous }
  let reindex : C(G × (Fin n → G), W) ≃L[R] C(Fin (n + 1) → G, W) :=
    { toFun F := F.comp hs
      invFun F := F.comp hf
      left_inv F := ContinuousMap.ext fun p ↦ congrArg F ((finSuccHomeomorph n).left_inv p)
      right_inv F := ContinuousMap.ext fun g ↦ congrArg F ((finSuccHomeomorph n).right_inv g)
      map_add' _ _ := ContinuousMap.ext fun _ ↦ rfl
      map_smul' _ _ := ContinuousMap.ext fun _ ↦ rfl
      continuous_toFun := ContinuousMap.continuous_precomp hs
      continuous_invFun := ContinuousMap.continuous_precomp hf }
  post.trans (uncurry.trans reindex)

/-- **Iterated compact-open currying.** For locally compact `G`, the `n`-th term of Mathlib's
coinduced resolution `TopRep.resolutionX X n` is topologically `R`-linearly equivalent to
`C(Fin n → G, X.V)` with the compact-open topology. -/
def resolutionXEquiv (X : TopRep.{max v w} R G) :
    ∀ n : ℕ, (TopRep.resolutionX X n).V ≃L[R] C(Fin n → G, X.V)
  | 0 =>
    { toEquiv := (Homeomorph.continuousMapOfUnique (X := Fin 0 → G) (Y := X.V)).toEquiv
      map_add' _ _ := ContinuousMap.ext fun _ ↦ rfl
      map_smul' _ _ := ContinuousMap.ext fun _ ↦ rfl
      continuous_toFun := (Homeomorph.continuousMapOfUnique (X := Fin 0 → G) (Y := X.V)).continuous
      continuous_invFun :=
        (Homeomorph.continuousMapOfUnique (X := Fin 0 → G) (Y := X.V)).symm.continuous }
  | n + 1 => resolutionXEquivStep (resolutionXEquiv X n)

theorem resolutionXEquiv_zero_apply (X : TopRep.{max v w} R G) (x : X.V) (g : Fin 0 → G) :
    resolutionXEquiv X 0 x g = x := (rfl)

theorem resolutionXEquiv_zero_symm_apply (X : TopRep.{max v w} R G) (f : C(Fin 0 → G, X.V)) :
    (resolutionXEquiv X 0).symm f = f Fin.elim0 :=
  congrArg f (Subsingleton.elim default Fin.elim0)

@[simp]
theorem resolutionXEquiv_succ_apply (X : TopRep.{max v w} R G) (n : ℕ)
    (F : (TopRep.resolutionX X (n + 1)).V) (g : Fin (n + 1) → G) :
    resolutionXEquiv X (n + 1) F g = resolutionXEquiv X n (F (g 0)) (Fin.tail g) := (rfl)

@[simp]
theorem resolutionXEquiv_one_apply (X : TopRep.{max v w} R G) (F : C(G, X.V)) (g : Fin 1 → G) :
    resolutionXEquiv X 1 F g = F (g 0) := (rfl)

@[simp]
theorem resolutionXEquiv_two_apply (X : TopRep.{max v w} R G) (F : C(G, C(G, X.V)))
    (g : Fin 2 → G) :
    resolutionXEquiv X 2 F g = F (g 0) (g 1) := (rfl)

@[simp]
theorem resolutionXEquiv_three_apply (X : TopRep.{max v w} R G) (F : C(G, C(G, C(G, X.V))))
    (g : Fin 3 → G) :
    resolutionXEquiv X 3 F g = F (g 0) (g 1) (g 2) := (rfl)

/-- Under iterated currying, the `G`-action on `TopRep.resolutionX X n` is diagonal left
translation twisted by `X.ρ`. -/
theorem resolutionXEquiv_ρ_apply (X : TopRep.{max v w} R G) (n : ℕ) (k : G)
    (F : (TopRep.resolutionX X n).V) (g : Fin n → G) :
    resolutionXEquiv X n ((TopRep.resolutionX X n).ρ k F) g =
      X.ρ k (resolutionXEquiv X n F (k⁻¹ • g)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [resolutionXEquiv_succ_apply, ContRepresentation.coind₁_apply_apply, ih,
      resolutionXEquiv_succ_apply]
    rfl

/-- Under iterated currying, the resolution differential `TopRep.d X n` becomes the alternating
face-map sum. -/
theorem resolutionXEquiv_d_apply (X : TopRep.{max v w} R G) (n : ℕ)
    (F : (TopRep.resolutionX X n).V) (g : Fin (n + 1) → G) :
    resolutionXEquiv X (n + 1) ((TopRep.d X n).hom F) g =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • resolutionXEquiv X n F (g ∘ i.succAbove) := by
  induction n with
  | zero =>
    rw [resolutionXEquiv_succ_apply, Fin.sum_univ_one]
    simp only [TopRep.d_zero, TopRep.hom_ofHom, ContRepresentation.coind₁ι_toFun,
      ContinuousMap.const_apply, Fin.val_zero, pow_zero, one_zsmul]
    rfl
  | succ n ih =>
    rw [resolutionXEquiv_succ_apply, TopRep.hom_d_succ, ContIntertwiningMap.sub_apply,
      ContRepresentation.coind₁ι_toFun, ContRepresentation.coind₁Map_toFun,
      ContinuousMap.sub_apply, ContinuousMap.const_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, map_sub]
    change resolutionXEquiv X (n + 1) F (Fin.tail g) -
        resolutionXEquiv X (n + 1) ((TopRep.d X n).hom (F (g 0))) (Fin.tail g) = _
    rw [ih (F (g 0)) (Fin.tail g), sub_eq_add_neg, ← Finset.sum_neg_distrib]
    conv_rhs => rw [Fin.sum_univ_succ]
    congr 1
    · simp only [Fin.val_zero, pow_zero, one_zsmul]
      rfl
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Fin.val_succ, pow_succ, mul_neg_one, neg_zsmul, resolutionXEquiv_succ_apply]
      congr 2
      rw [show (g ∘ j.succ.succAbove) 0 = g 0 by simp]
      exact congrArg (resolutionXEquiv X n (F (g 0)))
        (funext fun k ↦ by simp [Function.comp_apply, Fin.tail, Fin.succ_succAbove_succ])

/-- Iterated currying is natural in compatible pairs `(φ : H →ₜ* G, f : TopRep.res φ X ⟶ Y)`. -/
theorem resolutionXEquiv_resolutionMap_apply
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    (φ : H →ₜ* G) {X : TopRep.{max v w} R G} {Y : TopRep.{max v w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ)
    (F : (TopRep.resolutionX X n).V) (h : Fin n → H) :
    resolutionXEquiv Y n ((_root_.ContinuousCohomology.resolutionMap φ f n).hom F) h =
      f.hom (resolutionXEquiv X n F (φ ∘ h)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [resolutionXEquiv_succ_apply, _root_.ContinuousCohomology.resolutionMap_succ,
      TopRep.hom_ofHom, ContRepresentation.coind₁ResMap_apply, ih, resolutionXEquiv_succ_apply]
    rfl

end IteratedCurrying

/-! ### All-degree comparison of cochain complexes and continuous cohomology -/

section Comparison

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Homogenization of a continuous `n`-cochain as a continuous map `C(Fin (n + 1) → G, X.V)`. -/
private def homogenizeContinuousMap (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ)
    (f : C(Fin n → G, X.V)) : C(Fin (n + 1) → G, X.V) where
  toFun := homogenize X n f
  continuous_toFun :=
    (hX.comp ((continuous_apply 0).prodMk
      (f.continuous.comp (adjacentRatioMap n).continuous))).congr fun g ↦ by
        dsimp only [Function.comp_apply]
        rw [homogenize_apply]
        congr 2
        exact funext (adjacentRatioMap_apply n g)

omit [LocallyCompactSpace G] in
private theorem homogenizeContinuousMap_apply (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ)
    (f : C(Fin n → G, X.V)) (g : Fin (n + 1) → G) :
    homogenizeContinuousMap X hX n f g = homogenize X n f g := rfl

private theorem continuous_homogenizeContinuousMap (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    Continuous (homogenizeContinuousMap X hX n) := by
  refine ContinuousMap.continuous_of_continuous_uncurry (homogenizeContinuousMap X hX n) ?_
  have hev : Continuous fun p : C(Fin n → G, X.V) × (Fin (n + 1) → G) ↦
      p.1 (adjacentRatioMap n p.2) :=
    continuous_eval.comp
      (continuous_fst.prodMk ((adjacentRatioMap n).continuous.comp continuous_snd))
  exact (hX.comp (((continuous_apply 0).comp continuous_snd).prodMk hev)).congr fun p ↦ by
    dsimp only [Function.comp_apply, Function.uncurry]
    rw [homogenizeContinuousMap_apply, homogenize_apply]
    congr 2
    exact funext (adjacentRatioMap_apply n p.2)

private theorem homogenizeContinuousMap_mem_invariants (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) (f : C(Fin n → G, X.V)) :
    (resolutionXEquiv X (n + 1)).symm (homogenizeContinuousMap X hX n f) ∈
      (TopRep.resolutionX X (n + 1)).ρ.invariants := by
  intro k
  apply (resolutionXEquiv X (n + 1)).injective
  ext g
  rw [resolutionXEquiv_ρ_apply, ContinuousLinearEquiv.apply_symm_apply,
    homogenizeContinuousMap_apply, homogenizeContinuousMap_apply, ← homogenize_smul, smul_inv_smul]

/-- **Dehomogenization as a topological `R`-linear equivalence.** In every degree `n`, the space
`C(Fin n → G, X.V)` of inhomogeneous continuous `n`-cochains is topologically `R`-linearly
equivalent to the space `(TopRep.resolutionX X (n + 1)).ρ.invariants` of homogeneous `n`-cochains
for the compact-open topology. -/
def inhomogeneousToHomogeneousEquiv (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    C(Fin n → G, X.V) ≃L[R] (TopRep.resolutionX X (n + 1)).ρ.invariants where
  toFun f := ⟨(resolutionXEquiv X (n + 1)).symm (homogenizeContinuousMap X hX n f),
    homogenizeContinuousMap_mem_invariants X hX n f⟩
  invFun F := (resolutionXEquiv X (n + 1) F.1).comp (partialProdMap n)
  left_inv f := ContinuousMap.ext fun h ↦ by
    simp only [ContinuousMap.comp_apply, partialProdMap_apply,
      ContinuousLinearEquiv.apply_symm_apply, homogenizeContinuousMap_apply]
    exact homogenize_partialProd X n f h
  right_inv F := by
    apply Subtype.ext
    apply (resolutionXEquiv X (n + 1)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    ext g
    rw [homogenizeContinuousMap_apply, homogenize_apply]
    simp only [ContinuousMap.comp_apply, partialProdMap_apply]
    have hinv := congrArg (fun u : (TopRep.resolutionX X (n + 1)).V ↦
      resolutionXEquiv X (n + 1) u g) (F.2 (g 0))
    rw [resolutionXEquiv_ρ_apply] at hinv
    have hpar : (g 0)⁻¹ • g = Fin.partialProd (fun i ↦ (g i.castSucc)⁻¹ * g i.succ) :=
      inv_smul_eq_iff.mpr (Fin.partialProd_left_inv g).symm
    rw [← hpar]
    exact hinv
  map_add' f₁ f₂ := by
    apply Subtype.ext
    apply (resolutionXEquiv X (n + 1)).injective
    simp only [Submodule.coe_add, map_add, ContinuousLinearEquiv.apply_symm_apply]
    ext g
    simp [homogenizeContinuousMap_apply, homogenize_apply]
  map_smul' r f := by
    apply Subtype.ext
    apply (resolutionXEquiv X (n + 1)).injective
    simp only [RingHom.id_apply, Submodule.coe_smul_of_tower, map_smul,
      ContinuousLinearEquiv.apply_symm_apply]
    ext g
    simp [homogenizeContinuousMap_apply, homogenize_apply]
  continuous_toFun :=
    ((resolutionXEquiv X (n + 1)).symm.continuous.comp
      (continuous_homogenizeContinuousMap X hX n)).subtype_mk _
  continuous_invFun :=
    (ContinuousMap.continuous_precomp (partialProdMap n)).comp
      ((resolutionXEquiv X (n + 1)).continuous.comp continuous_subtype_val)

/-- Pointwise evaluation of `inhomogeneousToHomogeneousEquiv` after iterated currying. -/
@[simp]
theorem resolutionXEquiv_inhomogeneousToHomogeneousEquiv_apply (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ)
    (f : C(Fin n → G, X.V)) (g : Fin (n + 1) → G) :
    resolutionXEquiv X (n + 1) (inhomogeneousToHomogeneousEquiv X hX n f).1 g =
      homogenize X n f g := by
  change resolutionXEquiv X (n + 1)
    ((resolutionXEquiv X (n + 1)).symm (homogenizeContinuousMap X hX n f)) g = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- Pointwise evaluation of the inverse `inhomogeneousToHomogeneousEquiv.symm`. -/
@[simp]
theorem inhomogeneousToHomogeneousEquiv_symm_apply (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ)
    (F : (TopRep.resolutionX X (n + 1)).ρ.invariants) (h : Fin n → G) :
    (inhomogeneousToHomogeneousEquiv X hX n).symm F h =
      resolutionXEquiv X (n + 1) F.1 (Fin.partialProd h) := by
  change resolutionXEquiv X (n + 1) F.1 (partialProdMap n h) = _
  rw [partialProdMap_apply]

/-- `inhomogeneousToHomogeneousEquiv` intertwines the inhomogeneous and homogeneous
differentials in every degree. -/
theorem inhomogeneousToHomogeneousEquiv_d (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) (f : C(Fin n → G, X.V)) :
    ((TopRep.homogeneousCochains X).d n (n + 1)).hom
        (inhomogeneousToHomogeneousEquiv X hX n f) =
      inhomogeneousToHomogeneousEquiv X hX (n + 1)
        ((inhomogeneousCochainsD X hX n).hom f) := by
  apply Subtype.ext
  apply (resolutionXEquiv X (n + 2)).injective
  ext g
  rw [TopRep.homogeneousCochains.d_apply, resolutionXEquiv_d_apply,
    resolutionXEquiv_inhomogeneousToHomogeneousEquiv_apply]
  have hstep (i : Fin (n + 2)) :
      resolutionXEquiv X (n + 1) (inhomogeneousToHomogeneousEquiv X hX n f).1 (g ∘ i.succAbove) =
        homogenize X n f (g ∘ i.succAbove) :=
    resolutionXEquiv_inhomogeneousToHomogeneousEquiv_apply X hX n f (g ∘ i.succAbove)
  simp_rw [hstep]
  refine (alternatingFaceSum_homogenize X f g).trans ?_
  rw [homogenize_apply, homogenize_apply]
  congr 1
  exact (inhomogeneousCochainsD_apply X hX n f (fun i ↦ (g i.castSucc)⁻¹ * g i.succ)).symm

/-- **All-degree topological comparison of cochain complexes.** For locally compact `G` and
jointly continuous `X`, the inhomogeneous cochain complex `inhomogeneousCochainsTop X hX` is
isomorphic to Mathlib's `TopRep.homogeneousCochains X` in `CochainComplex (TopModuleCat R) ℕ`. -/
noncomputable def inhomogeneousCochainsTopIsoHomogeneous (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) :
    inhomogeneousCochainsTop X hX ≅ TopRep.homogeneousCochains X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ TopModuleCat.ofIso (inhomogeneousToHomogeneousEquiv X hX n))
    fun i j (hij : i + 1 = j) ↦ by
      subst hij
      rw [inhomogeneousCochainsTop_d]
      ext f
      refine (inhomogeneousToHomogeneousEquiv_d X hX i f).trans ?_
      exact congrArg (inhomogeneousToHomogeneousEquiv X hX (i + 1))
        (ContinuousMap.ext fun g ↦ (inhomogeneousCochainsTopD_apply X hX i f g).symm)

/-- **All-degree topological cohomology comparison.** In every degree `n`, the homology of
`inhomogeneousCochainsTop X hX` is isomorphic in `TopModuleCat R` (preserving the quotient
topology) to Mathlib's `continuousCohomology n X`. -/
noncomputable def inhomogeneousCohomologyTopIso (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    (inhomogeneousCochainsTop X hX).homology n ≅ continuousCohomology n X :=
  HomologicalComplex.homologyMapIso (inhomogeneousCochainsTopIsoHomogeneous X hX) n

/-- **All-degree algebraic comparison of cochain complexes.** For locally compact `G` and jointly
continuous `X`, the inhomogeneous cochain complex `inhomogeneousCochains X hX` is isomorphic in
`CochainComplex (ModuleCat R) ℕ` to Mathlib's `TopRep.homogeneousCochains X` after forgetting
topologies. -/
noncomputable def inhomogeneousCochainsIsoHomogeneous (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) :
    inhomogeneousCochains X hX ≅
      ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapHomologicalComplex _).obj
        (TopRep.homogeneousCochains X) :=
  (forget₂MapInhomogeneousCochainsTopIso X hX).symm ≪≫
    ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapHomologicalComplex _).mapIso
      (inhomogeneousCochainsTopIsoHomogeneous X hX)

/-- The degree-`n` component of `inhomogeneousCochainsIsoHomogeneous` applies
`inhomogeneousToHomogeneousEquiv`. -/
theorem inhomogeneousCochainsIsoHomogeneous_hom_f_apply (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) (f : C(Fin n → G, X.V)) :
    ((inhomogeneousCochainsIsoHomogeneous X hX).hom.f n).hom f =
      inhomogeneousToHomogeneousEquiv X hX n f := by
  simp only [inhomogeneousCochainsIsoHomogeneous, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.comp_f, forget₂MapInhomogeneousCochainsTopIso_inv_f, Category.id_comp,
    Functor.mapHomologicalComplex_map_f, Functor.mapIso_hom,
    inhomogeneousCochainsTopIsoHomogeneous, HomologicalComplex.Hom.isoOfComponents_hom_f,
    TopModuleCat.ofIso]
  rfl

/-- **All-degree algebraic cohomology comparison.** In every degree `n`, the homology of
`inhomogeneousCochains X hX` is isomorphic in `ModuleCat R` to the underlying `R`-module of
Mathlib's `continuousCohomology n X`. -/
noncomputable def inhomogeneousCohomologyIso (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    (inhomogeneousCochains X hX).homology n ≅
      (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).obj
        (continuousCohomology n X) :=
  HomologicalComplex.homologyMapIso (inhomogeneousCochainsIsoHomogeneous X hX) n ≪≫
    ((TopRep.homogeneousCochains X).sc n).mapHomologyIso
      (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R))

/-- The topological cochain comparison is natural in compatible pairs `(φ, f)`. -/
@[reassoc]
theorem inhomogeneousCochainsTopIsoHomogeneous_naturality
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    (φ : H →ₜ* G) {X : TopRep.{max v w} R G} {Y : TopRep.{max v w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : H × Y.V ↦ Y.ρ p.1 p.2) :
    inhomogeneousCochainsTopMap φ f hX hY ≫ (inhomogeneousCochainsTopIsoHomogeneous Y hY).hom =
      (inhomogeneousCochainsTopIsoHomogeneous X hX).hom ≫
        _root_.ContinuousCohomology.cochainsMap φ f := by
  ext n : 2
  ext c
  apply Subtype.ext
  apply (resolutionXEquiv Y (n + 1)).injective
  ext h
  simp only [HomologicalComplex.comp_f, TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply,
    inhomogeneousCochainsTopIsoHomogeneous, HomologicalComplex.Hom.isoOfComponents_hom_f,
    TopModuleCat.ofIso, TopModuleCat.hom_ofHom, ContinuousLinearEquiv.coe_coe,
    _root_.ContinuousCohomology.cochainsMap_f, TopRep.invariantsResMap]
  rw [ContIntertwiningMap.mapInvariantsOfRes_apply, resolutionXEquiv_resolutionMap_apply,
    resolutionXEquiv_inhomogeneousToHomogeneousEquiv_apply,
    resolutionXEquiv_inhomogeneousToHomogeneousEquiv_apply, homogenize_apply, homogenize_apply,
    inhomogeneousCochainsTopMap_f_apply, ← TopRep.hom_comm_apply f (h 0)]
  congr 1
  change X.ρ (φ (h 0)) (c (φ ∘ fun i ↦ (h i.castSucc)⁻¹ * h i.succ)) =
    X.ρ (φ (h 0)) (c fun i ↦ (φ (h i.castSucc))⁻¹ * φ (h i.succ))
  congr 2
  ext i
  simp [map_mul, map_inv]

/-- The algebraic cochain comparison is natural in compatible pairs `(φ, f)`. -/
@[reassoc]
theorem inhomogeneousCochainsIsoHomogeneous_naturality
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    (φ : H →ₜ* G) {X : TopRep.{max v w} R G} {Y : TopRep.{max v w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : H × Y.V ↦ Y.ρ p.1 p.2) :
    inhomogeneousCochainsMap φ f hX hY ≫ (inhomogeneousCochainsIsoHomogeneous Y hY).hom =
      (inhomogeneousCochainsIsoHomogeneous X hX).hom ≫
        ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapHomologicalComplex _).map
          (_root_.ContinuousCohomology.cochainsMap φ f) := by
  let F := (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  have htop : F.map (inhomogeneousCochainsTopMap φ f hX hY) ≫
      F.map (inhomogeneousCochainsTopIsoHomogeneous Y hY).hom =
      F.map (inhomogeneousCochainsTopIsoHomogeneous X hX).hom ≫
        F.map (_root_.ContinuousCohomology.cochainsMap φ f) := by
    rw [← F.map_comp, ← F.map_comp, inhomogeneousCochainsTopIsoHomogeneous_naturality]
  have hforget : inhomogeneousCochainsMap φ f hX hY ≫
      (forget₂MapInhomogeneousCochainsTopIso Y hY).inv =
      (forget₂MapInhomogeneousCochainsTopIso X hX).inv ≫
        F.map (inhomogeneousCochainsTopMap φ f hX hY) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact (forget₂Map_inhomogeneousCochainsTopMap φ f hX hY).symm
  calc
    inhomogeneousCochainsMap φ f hX hY ≫ (inhomogeneousCochainsIsoHomogeneous Y hY).hom
      = (inhomogeneousCochainsMap φ f hX hY ≫ (forget₂MapInhomogeneousCochainsTopIso Y hY).inv) ≫
          F.map (inhomogeneousCochainsTopIsoHomogeneous Y hY).hom := by
        simp [inhomogeneousCochainsIsoHomogeneous, F, Category.assoc]
    _ = (forget₂MapInhomogeneousCochainsTopIso X hX).inv ≫
          (F.map (inhomogeneousCochainsTopMap φ f hX hY) ≫
            F.map (inhomogeneousCochainsTopIsoHomogeneous Y hY).hom) := by
        rw [hforget, Category.assoc]
    _ = (inhomogeneousCochainsIsoHomogeneous X hX).hom ≫
          F.map (_root_.ContinuousCohomology.cochainsMap φ f) := by
        rw [htop, ← Category.assoc]
        rfl

/-- The algebraic cochain comparison is natural in coefficient morphisms `f : X ⟶ Y`. -/
@[reassoc]
theorem inhomogeneousCochainsIsoHomogeneous_coeffMap_naturality
    {X Y : TopRep.{max v w} R G} (f : X ⟶ Y)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2) :
    inhomogeneousCochainsCoeffMap f hX hY ≫ (inhomogeneousCochainsIsoHomogeneous Y hY).hom =
      (inhomogeneousCochainsIsoHomogeneous X hX).hom ≫
        ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapHomologicalComplex _).map
          (_root_.ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) f) := by
  rw [inhomogeneousCochainsCoeffMap_def]
  exact inhomogeneousCochainsIsoHomogeneous_naturality (ContinuousMonoidHom.id G) f hX hY

/-- The algebraic cohomology comparison is natural in compatible pairs `(φ, f)`. -/
@[reassoc]
theorem inhomogeneousCohomologyIso_naturality
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    (φ : H →ₜ* G) {X : TopRep.{max v w} R G} {Y : TopRep.{max v w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : H × Y.V ↦ Y.ρ p.1 p.2) (n : ℕ) :
    HomologicalComplex.homologyMap (inhomogeneousCochainsMap φ f hX hY) n ≫
        (inhomogeneousCohomologyIso Y hY n).hom =
      (inhomogeneousCohomologyIso X hX n).hom ≫
        (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).map
          (_root_.ContinuousCohomology.map φ f n) := by
  let F := forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)
  have h1 : HomologicalComplex.homologyMap (inhomogeneousCochainsMap φ f hX hY) n ≫
      HomologicalComplex.homologyMap (inhomogeneousCochainsIsoHomogeneous Y hY).hom n =
      HomologicalComplex.homologyMap (inhomogeneousCochainsIsoHomogeneous X hX).hom n ≫
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex _).map (_root_.ContinuousCohomology.cochainsMap φ f)) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      inhomogeneousCochainsIsoHomogeneous_naturality]
  have h2 := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (_root_.ContinuousCohomology.cochainsMap φ f)) F
  calc
    HomologicalComplex.homologyMap (inhomogeneousCochainsMap φ f hX hY) n ≫
        (inhomogeneousCohomologyIso Y hY n).hom
      = (HomologicalComplex.homologyMap (inhomogeneousCochainsMap φ f hX hY) n ≫
          HomologicalComplex.homologyMap (inhomogeneousCochainsIsoHomogeneous Y hY).hom n) ≫
          (((TopRep.homogeneousCochains Y).sc n).mapHomologyIso F).hom := by
        simp only [inhomogeneousCohomologyIso, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom,
          Category.assoc]
        rfl
    _ = HomologicalComplex.homologyMap (inhomogeneousCochainsIsoHomogeneous X hX).hom n ≫
          (HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex _).map (_root_.ContinuousCohomology.cochainsMap φ f)) n ≫
            (((TopRep.homogeneousCochains Y).sc n).mapHomologyIso F).hom) := by
        rw [h1, Category.assoc]
    _ = (inhomogeneousCohomologyIso X hX n).hom ≫
          F.map (_root_.ContinuousCohomology.map φ f n) := by
        rw [inhomogeneousCohomologyIso, Iso.trans_hom, Category.assoc]
        exact congrArg (_ ≫ ·) h2

/-- Applying `inhomogeneousCohomologyIso` to a cohomology class `K.homologyπ n z` commutes with
`HomologicalComplex.cyclesMap` and `ShortComplex.mapCyclesIso`. -/
@[reassoc]
theorem homologyπ_comp_inhomogeneousCohomologyIso_hom (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    (inhomogeneousCochains X hX).homologyπ n ≫ (inhomogeneousCohomologyIso X hX n).hom =
      HomologicalComplex.cyclesMap (inhomogeneousCochainsIsoHomogeneous X hX).hom n ≫
        (((TopRep.homogeneousCochains X).sc n).mapCyclesIso
          (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R))).hom ≫
        (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).map
          ((TopRep.homogeneousCochains X).homologyπ n) := by
  rw [inhomogeneousCohomologyIso, Iso.trans_hom, ← Category.assoc,
    HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyπ_naturality,
    Category.assoc]
  exact congrArg (HomologicalComplex.cyclesMap (inhomogeneousCochainsIsoHomogeneous X hX).hom n ≫ ·)
    (((TopRep.homogeneousCochains X).sc n).homologyπ_comp_mapHomologyIso_hom
      (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)))

end Comparison

/-! ### Degree-zero identification and compatibility with `ContinuousCohomology.zeroIso` -/

section DegreeZero

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [ContinuousMul G]

/-- Evaluation at `Fin.elim0` identifies the degree-`0` cocycles of `inhomogeneousCochains X hX`
with the invariant submodule `X.ρ.invariants`. -/
private def inhomogeneousCocyclesZeroEquiv (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) :
    LinearMap.ker (((inhomogeneousCochains X hX).sc' 0 0 1).g.hom) ≃ₗ[R] X.ρ.invariants where
  toFun c :=
    let f : C(Fin 0 → G, X.V) := c.1
    ⟨f Fin.elim0, fun g ↦ by
      have hker : ((inhomogeneousCochains X hX).d 0 1).hom f = 0 := c.2
      have hc := congrArg (fun u : C(Fin 1 → G, X.V) ↦ u (fun _ ↦ g)) hker
      rw [inhomogeneousCochains_d_apply, inhomogeneousCochainsD_zero_apply] at hc
      exact sub_eq_zero.mp hc⟩
  invFun u := ⟨ContinuousMap.const _ u.1, by
    change ((inhomogeneousCochains X hX).d 0 1).hom (ContinuousMap.const _ u.1) = 0
    ext g
    rw [inhomogeneousCochains_d_apply, inhomogeneousCochainsD_zero_apply,
      ContinuousMap.const_apply, u.2 (g 0), sub_self]
    rfl⟩
  left_inv c := by
    let f : C(Fin 0 → G, X.V) := c.1
    exact Subtype.ext (ContinuousMap.ext fun g ↦ congrArg f (Subsingleton.elim Fin.elim0 g))
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Degree zero of `inhomogeneousCochains` is `X.ρ.invariants`**, as an `R`-linear equivalence
with no local compactness or universe restriction on `X`. -/
noncomputable def inhomogeneousCohomologyZeroLinearEquiv (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) :
    ((inhomogeneousCochains X hX).homology 0 : Type (max v w)) ≃ₗ[R] X.ρ.invariants :=
  ((inhomogeneousCochains X hX).isoHomologyπ₀.symm ≪≫
    (inhomogeneousCochains X hX).cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫
    ((inhomogeneousCochains X hX).sc' 0 0 1).moduleCatCyclesIso).toLinearEquiv.trans
    (inhomogeneousCocyclesZeroEquiv X hX)

/-- **Degree zero of `inhomogeneousCochains` is `ModuleCat.of R X.ρ.invariants`.** -/
noncomputable def inhomogeneousCohomologyZeroIso (X : TopRep.{max v w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) :
    (inhomogeneousCochains X hX).homology 0 ≅ ModuleCat.of R X.ρ.invariants :=
  (inhomogeneousCohomologyZeroLinearEquiv X hX).toModuleIso

/-- Evaluating `inhomogeneousCohomologyZeroLinearEquiv` on a degree-`0` cohomology class
`K.homologyπ 0 c` recovers the value of the underlying `0`-cocycle at `Fin.elim0`. -/
theorem coe_inhomogeneousCohomologyZeroLinearEquiv_homologyπ (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (c : (inhomogeneousCochains X hX).cycles 0) :
    (inhomogeneousCohomologyZeroLinearEquiv X hX
        ((inhomogeneousCochains X hX).homologyπ 0 c)).1 =
      ((inhomogeneousCochains X hX).iCycles 0 c) Fin.elim0 := by
  let K := inhomogeneousCochains X hX
  let S0 := K.sc' 0 0 1
  have h1 : K.isoHomologyπ₀.inv (K.homologyπ 0 c) = c := by
    have := ConcreteCategory.congr_hom (K.isoHomologyπ_hom_inv_id _ 0 rfl (by simp)) c
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using this
  have h2 : ((S0.moduleCatCyclesIso.hom
      ((K.cyclesIsoSc' 0 0 1 (by simp) (by simp)).hom c)).1 : C(Fin 0 → G, X.V)) =
      K.iCycles 0 c := by
    have h2a := ConcreteCategory.congr_hom S0.moduleCatCyclesIso_hom_i
      ((K.cyclesIsoSc' 0 0 1 (by simp) (by simp)).hom c)
    have h2b := ConcreteCategory.congr_hom (K.cyclesIsoSc'_hom_iCycles 0 0 1 (by simp) (by simp)) c
    exact h2a.trans h2b
  change (inhomogeneousCocyclesZeroEquiv X hX
      (S0.moduleCatCyclesIso.hom ((K.cyclesIsoSc' 0 0 1 (by simp) (by simp)).hom
        (K.isoHomologyπ₀.inv (K.homologyπ 0 c))))).1 = (K.iCycles 0 c) Fin.elim0
  rw [h1]
  let f : C(Fin 0 → G, X.V) :=
    (S0.moduleCatCyclesIso.hom ((K.cyclesIsoSc' 0 0 1 (by simp) (by simp)).hom c)).1
  change f Fin.elim0 = _
  exact congrArg (fun u : C(Fin 0 → G, X.V) ↦ u Fin.elim0) h2

/-- `inhomogeneousCohomologyZeroLinearEquiv` is natural in coefficient morphisms `f : X ⟶ Y`. -/
theorem inhomogeneousCohomologyZeroLinearEquiv_naturality {X Y : TopRep.{w} R G}
    (f : X ⟶ Y) (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2)
    (x : (inhomogeneousCochains X hX).homology 0) :
    (inhomogeneousCohomologyZeroLinearEquiv Y hY
        (HomologicalComplex.homologyMap (inhomogeneousCochainsCoeffMap f hX hY) 0 x)).1 =
      f.hom (inhomogeneousCohomologyZeroLinearEquiv X hX x).1 := by
  obtain ⟨c, rfl⟩ := (inhomogeneousCochains X hX).isoHomologyπ₀.toLinearEquiv.surjective x
  change (inhomogeneousCohomologyZeroLinearEquiv Y hY
      (HomologicalComplex.homologyMap (inhomogeneousCochainsCoeffMap f hX hY) 0
        ((inhomogeneousCochains X hX).homologyπ 0 c))).1 =
    f.hom (inhomogeneousCohomologyZeroLinearEquiv X hX
      ((inhomogeneousCochains X hX).homologyπ 0 c)).1
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, coe_inhomogeneousCohomologyZeroLinearEquiv_homologyπ,
    coe_inhomogeneousCohomologyZeroLinearEquiv_homologyπ]
  have hi := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (inhomogeneousCochainsCoeffMap f hX hY) 0) c
  simp only [ConcreteCategory.comp_apply] at hi
  refine (congrArg (fun u : C(Fin 0 → G, Y.V) ↦ u Fin.elim0) hi).trans ?_
  rw [inhomogeneousCochainsCoeffMap_f]
  exact (inhomogeneousCochainsMapF_apply (ContinuousMonoidHom.id G) f 0
    ((inhomogeneousCochains X hX).iCycles 0 c) Fin.elim0).trans
    (congrArg f.hom (congrArg _ (Subsingleton.elim _ _)))

end DegreeZero

section DegreeZeroComparison

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Under the all-degree comparison `inhomogeneousCohomologyIso`, Mathlib's
`ContinuousCohomology.zeroIso` agrees with `inhomogeneousCohomologyZeroIso`. -/
theorem inhomogeneousCohomologyIso_zero_comp_zeroIso
    (X : TopRep.{max v w} R G) (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) :
    (inhomogeneousCohomologyIso X hX 0).hom ≫
        (forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).map
          (_root_.ContinuousCohomology.zeroIso X).hom =
      (inhomogeneousCohomologyZeroIso X hX).hom := by
  let F := forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)
  let K := inhomogeneousCochains X hX
  rw [← cancel_epi (K.homologyπ 0)]
  ext c
  apply Subtype.ext
  have hR : (((K.homologyπ 0 ≫ (inhomogeneousCohomologyZeroIso X hX).hom) c : X.ρ.invariants) :
      X.V) = (K.iCycles 0 c) Fin.elim0 :=
    coe_inhomogeneousCohomologyZeroLinearEquiv_homologyπ X hX c
  rw [hR]
  let φ := inhomogeneousCochainsIsoHomogeneous X hX
  let S := (TopRep.homogeneousCochains X).sc 0
  have hL1 := homologyπ_comp_inhomogeneousCohomologyIso_hom X hX 0
  have hcomp : K.homologyπ 0 ≫ (inhomogeneousCohomologyIso X hX 0).hom ≫
        F.map (_root_.ContinuousCohomology.zeroIso X).hom =
      HomologicalComplex.cyclesMap φ.hom 0 ≫ (S.mapCyclesIso F).hom ≫
        F.map ((TopRep.homogeneousCochains X).homologyπ 0 ≫
          (_root_.ContinuousCohomology.zeroIso X).hom) := by
    rw [← Category.assoc, hL1, Category.assoc, Category.assoc, ← F.map_comp]
  have hL := ConcreteCategory.congr_hom hcomp c
  refine (congrArg Subtype.val hL).trans ?_
  simp only [ConcreteCategory.comp_apply]
  let σ : _root_.ContinuousCohomology.cocycles X 0 :=
    (S.mapCyclesIso F).hom (HomologicalComplex.cyclesMap φ.hom 0 c)
  change (((_root_.ContinuousCohomology.zeroIso X).hom
    (_root_.ContinuousCohomology.π X 0 σ)) : X.V) = _
  rw [coe_zeroIso_hom_π X σ]
  have hi1 : F.map S.iCycles σ =
      ((S.map F).iCycles ((HomologicalComplex.cyclesMap φ.hom 0) c)) := by
    have := ConcreteCategory.congr_hom (S.mapCyclesIso_hom_iCycles F)
      (HomologicalComplex.cyclesMap φ.hom 0 c)
    simpa only [ConcreteCategory.comp_apply] using this
  have hi2 : (S.map F).iCycles ((HomologicalComplex.cyclesMap φ.hom 0) c) =
      φ.hom.f 0 (K.iCycles 0 c) := by
    change ((F.mapHomologicalComplex _).obj (TopRep.homogeneousCochains X)).iCycles 0
      ((HomologicalComplex.cyclesMap φ.hom 0) c) = _
    have := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ.hom 0) c
    simpa only [ConcreteCategory.comp_apply] using this
  have hi : ((TopRep.homogeneousCochains X).iCycles 0 σ).1 1 =
      (inhomogeneousToHomogeneousEquiv X hX 0 (K.iCycles 0 c)).1 1 := by
    have h12 := hi1.trans hi2
    rw [inhomogeneousCochainsIsoHomogeneous_hom_f_apply] at h12
    exact congrArg (fun u : (TopRep.homogeneousCochains X).X 0 ↦ u.1 1) h12
  rw [hi]
  have hev := resolutionXEquiv_inhomogeneousToHomogeneousEquiv_apply X hX 0
    (K.iCycles 0 c) (fun _ ↦ (1 : G))
  change resolutionXEquiv X 1 (inhomogeneousToHomogeneousEquiv X hX 0 (K.iCycles 0 c)).1
      (fun _ ↦ 1) = (K.iCycles 0 c) Fin.elim0
  rw [hev, homogenize_apply, map_one, one_apply_eq_self]
  exact congrArg (K.iCycles 0 c) (Subsingleton.elim _ _)

end DegreeZeroComparison

end TauCeti.ContinuousCohomology
