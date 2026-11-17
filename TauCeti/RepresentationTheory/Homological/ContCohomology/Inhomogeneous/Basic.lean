/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.Continuous.TopRep
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic

/-!
# Inhomogeneous continuous cochains in every degree

Given a topological group `G`, a topological ring `R`, and a topological representation
`X : TopRep R G` whose action `G × X.V → X.V` is jointly continuous, this file constructs the
all-degree complex of inhomogeneous continuous cochains

```text
0 → C(G⁰, X) → C(G¹, X) → C(G², X) → ⋯
```

with degree-`n` term `C(Fin n → G, X.V)` and standard inhomogeneous coboundary

```text
(dⁿ f)(g₀, …, gₙ) = ρ(g₀)(f(g₁, …, gₙ))
  + ∑_{j=0}^{n} (-1)^{j+1} • f(g₀, …, gⱼgⱼ₊₁, …, gₙ)
```

where the last term (`j = n`) drops `gₙ`, written with Mathlib's `Fin.contractNth`. The algebraic
cochain complex `inhomogeneousCochains X hX : CochainComplex (ModuleCat R) ℕ` needs no local
compactness on `G` and works over an arbitrary (not necessarily commutative) topological ring `R`;
when `G` is locally compact, the differentials are continuous for the compact-open topology,
yielding the topological cochain complex
`inhomogeneousCochainsTop X hX : CochainComplex (TopModuleCat R) ℕ`.

The identity `d ∘ d = 0` is proved directly by transporting the differential to the alternating
face-map sum on homogeneous functions `(Fin (n + 1) → G) → X.V` via `Fin.partialProd` and
cancelling pairs under the involution `(i, j) ↦ (i.succAbove j, j.predAbove i)`. The same
transport identity also drives the all-degree comparison with Mathlib's `TopRep.homogeneousCochains`
in `Comparison.lean`.

## Main definitions

* `TauCeti.ContinuousCohomology.homogenize`: the pointwise homogeneous form
  `(g₀, …, gₙ) ↦ ρ(g₀)(f(g₀⁻¹g₁, …, gₙ₋₁⁻¹gₙ))` of an inhomogeneous `n`-cochain.
* `TauCeti.ContinuousCohomology.inhomogeneousCochainsD`,
  `TauCeti.ContinuousCohomology.inhomogeneousCochains`: the inhomogeneous differential and cochain
  complex in `ModuleCat R`.
* `TauCeti.ContinuousCohomology.inhomogeneousCochainsTopD`,
  `TauCeti.ContinuousCohomology.inhomogeneousCochainsTop`: the compact-open topological differential
  and cochain complex in `TopModuleCat R`, for locally compact `G`.
* `TauCeti.ContinuousCohomology.inhomogeneousCochainsMap`,
  `TauCeti.ContinuousCohomology.inhomogeneousCochainsCoeffMap`,
  `TauCeti.ContinuousCohomology.inhomogeneousCochainsTopMap`: functoriality in compatible pairs
  `(φ : H →ₜ* G, f : TopRep.res φ X ⟶ Y)` and coefficient morphisms `f : X ⟶ Y`.

## Main results

* `TauCeti.ContinuousCohomology.alternatingFaceSum_homogenize`: the homogeneous alternating sum of
  `homogenize X n f` is `homogenize X (n + 1)` of the inhomogeneous differential of `f`.
* `TauCeti.ContinuousCohomology.inhomogeneousCochainsD_comp_d`: `dⁿ ≫ dⁿ⁺¹ = 0` in all degrees.
* `TauCeti.ContinuousCohomology.forget₂MapInhomogeneousCochainsTopIso`: forgetting topology from
  `inhomogeneousCochainsTop` recovers `inhomogeneousCochains`.
* `TauCeti.ContinuousCohomology.inhomogeneousCochainsD_even_of_subsingleton`,
  `TauCeti.ContinuousCohomology.inhomogeneousCochainsD_odd_of_subsingleton`,
  `TauCeti.ContinuousCohomology.exactAt_inhomogeneousCochains_succ_of_subsingleton`:
  for a trivial group `G`, every term identifies with `X.V`, the differentials alternate between
  zero and the identity, and all positive cohomology vanishes.

## References

* K. Rubin, *Euler Systems*, Appendix B, §2, Definition 2.1, p. 151.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

universe u v w

/-! ### Tuple maps and simplicial cancellation -/

section Simplicial

variable {G : Type v} [TopologicalSpace G]

/-- The continuous map `(Fin (n + 1) → G) → (Fin n → G)` contracting the `j`-th adjacent pair
by multiplication (or dropping the last entry when `j = Fin.last n`). -/
def contractNthMap [Mul G] [ContinuousMul G] (n : ℕ) (j : Fin (n + 1)) :
    C(Fin (n + 1) → G, Fin n → G) where
  toFun g := j.contractNth (· * ·) g
  continuous_toFun := continuous_pi fun k ↦ by
    rcases lt_trichotomy (k : ℕ) j with h | h | h
    · exact (continuous_apply k.castSucc).congr fun g ↦
        (Fin.contractNth_apply_of_lt j (· * ·) g k h).symm
    · exact ((continuous_apply k.castSucc).mul (continuous_apply k.succ)).congr fun g ↦
        (Fin.contractNth_apply_of_eq j (· * ·) g k h).symm
    · exact (continuous_apply k.succ).congr fun g ↦
        (Fin.contractNth_apply_of_gt j (· * ·) g k h).symm

@[simp]
theorem contractNthMap_apply [Mul G] [ContinuousMul G] (n : ℕ) (j : Fin (n + 1))
    (g : Fin (n + 1) → G) :
    contractNthMap n j g = j.contractNth (· * ·) g := (rfl)

/-- The continuous map `(Fin n → G) → (Fin (n + 1) → G)` taking `(g₀, …, gₙ₋₁)` to its partial
products `(1, g₀, g₀g₁, …, g₀⋯gₙ₋₁)`. -/
def partialProdMap [Monoid G] [ContinuousMul G] (n : ℕ) :
    C(Fin n → G, Fin (n + 1) → G) where
  toFun g := Fin.partialProd g
  continuous_toFun := continuous_pi fun i ↦
    Fin.inductionOn i
      (continuous_const.congr fun g ↦ (Fin.partialProd_zero g).symm)
      (fun j ih ↦ (ih.mul (continuous_apply j)).congr fun g ↦ (Fin.partialProd_succ g j).symm)

@[simp]
theorem partialProdMap_apply [Monoid G] [ContinuousMul G] (n : ℕ) (g : Fin n → G) :
    partialProdMap n g = Fin.partialProd g := (rfl)

/-- The continuous map `(Fin (n + 1) → G) → (Fin n → G)` dropping the leading coordinate. -/
def tailMap (n : ℕ) : C(Fin (n + 1) → G, Fin n → G) where
  toFun g := Fin.tail g
  continuous_toFun := continuous_pi fun i ↦ continuous_apply i.succ

@[simp]
theorem tailMap_apply (n : ℕ) (g : Fin (n + 1) → G) :
    tailMap n g = Fin.tail g := (rfl)

/-- The continuous map `(Fin (n + 1) → G) → (Fin n → G)` taking `(g₀, …, gₙ)` to the adjacent
ratios `(g₀⁻¹g₁, …, gₙ₋₁⁻¹gₙ)`. -/
def adjacentRatioMap [Group G] [IsTopologicalGroup G] (n : ℕ) :
    C(Fin (n + 1) → G, Fin n → G) where
  toFun g i := (g i.castSucc)⁻¹ * g i.succ
  continuous_toFun := continuous_pi fun i ↦
    (continuous_apply i.castSucc).inv.mul (continuous_apply i.succ)

@[simp]
theorem adjacentRatioMap_apply [Group G] [IsTopologicalGroup G] (n : ℕ)
    (g : Fin (n + 1) → G) (i : Fin n) :
    adjacentRatioMap n g i = (g i.castSucc)⁻¹ * g i.succ := (rfl)

/-- The sign changes by `-1` under the simplicial involution
`(i, j) ↦ (i.succAbove j, j.predAbove i)`. -/
private theorem neg_one_pow_succAbove_add_predAbove {n : ℕ}
    (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (-1 : ℤ) ^ ((i.succAbove j : ℕ) + (j.predAbove i : ℕ)) =
      -((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) := by
  cases Fin.lt_or_le j.castSucc i with
  | inl h =>
    have hi : 1 ≤ (i : ℕ) := by
      have : (j : ℕ) < (i : ℕ) := h
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.predAbove_of_castSucc_lt _ _ h,
      Fin.val_castSucc, Fin.val_pred]
    have hsum : (i : ℕ) + (j : ℕ) = ((j : ℕ) + ((i : ℕ) - 1)) + 1 := by omega
    rw [hsum, pow_succ, mul_neg_one, neg_neg]
  | inr h =>
    rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.predAbove_of_le_castSucc _ _ h,
      Fin.val_succ, Fin.coe_castPred]
    have hsum : (j : ℕ) + 1 + (i : ℕ) = ((i : ℕ) + (j : ℕ)) + 1 := by omega
    rw [hsum, pow_succ, mul_neg_one]

/-- Iterated alternating face sums vanish identically on any function of tuples. -/
theorem alternatingFaceSum_comp_alternatingFaceSum {α A : Type*} [AddCommGroup A] {n : ℕ}
    (F : (Fin (n + 1) → α) → A) (g : Fin (n + 3) → α) :
    ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • F (g ∘ i.succAbove ∘ j.succAbove) = 0 := by
  have hrewrite :
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • F (g ∘ i.succAbove ∘ j.succAbove) =
      ∑ p : Fin (n + 3) × Fin (n + 2),
        (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) • F (g ∘ p.1.succAbove ∘ p.2.succAbove) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← mul_zsmul, ← pow_add]
  rw [hrewrite]
  refine Finset.sum_involution
    (fun (p : Fin (n + 3) × Fin (n + 2)) _ ↦ (p.1.succAbove p.2, p.2.predAbove p.1))
    ?_ ?_ (fun _ _ ↦ Finset.mem_univ _) ?_
  · intro p _
    have hcomp : g ∘ (p.1.succAbove p.2).succAbove ∘ (p.2.predAbove p.1).succAbove =
        g ∘ p.1.succAbove ∘ p.2.succAbove :=
      funext fun k ↦ congrArg g (Fin.succAbove_succAbove_succAbove_predAbove p.1 p.2 k)
    rw [hcomp, neg_one_pow_succAbove_add_predAbove, neg_zsmul, add_neg_cancel]
  · intro p _ _ h
    exact Fin.succAbove_ne p.1 p.2 (congrArg Prod.fst h)
  · intro p _
    exact Prod.ext (Fin.succAbove_succAbove_predAbove p.1 p.2)
      (Fin.predAbove_predAbove_succAbove p.1 p.2)

end Simplicial

/-! ### Homogenization and the inhomogeneous differential -/

section Pointwise

variable {R : Type u} [Ring R] [TopologicalSpace R] {G : Type v} [Group G]

/-- The pointwise homogeneous form `(g₀, …, gₙ) ↦ ρ(g₀)(f(g₀⁻¹g₁, …, gₙ₋₁⁻¹gₙ))` of a function
`f : (Fin n → G) → X.V`. -/
def homogenize (X : TopRep.{w} R G) (n : ℕ) (f : (Fin n → G) → X.V)
    (g : Fin (n + 1) → G) : X.V :=
  X.ρ (g 0) (f fun i ↦ (g i.castSucc)⁻¹ * g i.succ)

@[simp]
theorem homogenize_apply (X : TopRep.{w} R G) (n : ℕ) (f : (Fin n → G) → X.V)
    (g : Fin (n + 1) → G) :
    homogenize X n f g = X.ρ (g 0) (f fun i ↦ (g i.castSucc)⁻¹ * g i.succ) := (rfl)

/-- Evaluating `homogenize X n f` at the partial products `Fin.partialProd h` recovers `f h`. -/
theorem homogenize_partialProd (X : TopRep.{w} R G) (n : ℕ) (f : (Fin n → G) → X.V)
    (h : Fin n → G) :
    homogenize X n f (Fin.partialProd h) = f h := by
  simp only [homogenize_apply, Fin.partialProd_zero, map_one, one_apply_eq_self]
  congr 1
  exact funext fun i ↦ Fin.partialProd_right_inv h i

/-- `homogenize X n f` is `G`-equivariant for the diagonal left action on `Fin (n + 1) → G`. -/
theorem homogenize_smul (X : TopRep.{w} R G) (n : ℕ) (f : (Fin n → G) → X.V)
    (k : G) (g : Fin (n + 1) → G) :
    homogenize X n f (k • g) = X.ρ k (homogenize X n f g) := by
  simp only [homogenize_apply, Pi.smul_apply, smul_eq_mul, map_mul,
    mul_apply_eq_comp, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/-- **Differential transport under homogenization.** The homogeneous alternating face-map sum of
`homogenize X n f` is the homogenization of the inhomogeneous differential of `f`. -/
theorem alternatingFaceSum_homogenize (X : TopRep.{w} R G) {n : ℕ}
    (f : (Fin n → G) → X.V) (g : Fin (n + 2) → G) :
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • homogenize X n f (g ∘ i.succAbove) =
      homogenize X (n + 1)
        (fun h ↦ X.ρ (h 0) (f (Fin.tail h)) +
          ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • f (j.contractNth (· * ·) h)) g := by
  have hpartial : ∀ h : Fin (n + 1) → G,
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        homogenize X n f (Fin.partialProd h ∘ i.succAbove) =
      X.ρ (h 0) (f (Fin.tail h)) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • f (j.contractNth (· * ·) h) := by
    intro h
    rw [Fin.sum_univ_succ]
    congr 1
    · simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.succAbove_zero, homogenize_apply,
        Function.comp_apply, Fin.partialProd_succ', Fin.partialProd_zero, mul_one]
      congr 2
      ext k
      simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left,
        Fin.partialProd_right_inv, Fin.tail]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Fin.partialProd_contractNth h j, homogenize_partialProd, Fin.val_succ]
  set r : Fin (n + 1) → G := fun i ↦ (g i.castSucc)⁻¹ * g i.succ
  have hg : g = g 0 • Fin.partialProd r := (Fin.partialProd_left_inv g).symm
  have hcomp (i : Fin (n + 2)) : g ∘ i.succAbove = g 0 • (Fin.partialProd r ∘ i.succAbove) := by
    ext k
    exact congrFun hg (i.succAbove k)
  calc
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • homogenize X n f (g ∘ i.succAbove)
        = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
            X.ρ (g 0) (homogenize X n f (Fin.partialProd r ∘ i.succAbove)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hcomp i, homogenize_smul]
    _ = X.ρ (g 0) (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
            homogenize X n f (Fin.partialProd r ∘ i.succAbove)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_zsmul]
    _ = homogenize X (n + 1)
          (fun h ↦ X.ρ (h 0) (f (Fin.tail h)) +
            ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • f (j.contractNth (· * ·) h)) g := by
          rw [hpartial r]
          rfl

end Pointwise

/-! ### The inhomogeneous continuous cochain complex in `ModuleCat R` -/

section AlgebraicComplex

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [TopologicalSpace G]

/-- A topological representation with trivial action has jointly continuous action. -/
theorem continuous_ρ_of_eq_self [Monoid G] {X : TopRep.{w} R G}
    (htriv : ∀ (g : G) (x : X.V), X.ρ g x = x) :
    Continuous fun p : G × X.V ↦ X.ρ p.1 p.2 := by
  simpa only [htriv] using continuous_snd

/-- A smooth discrete topological representation has jointly continuous action. -/
theorem continuous_ρ_of_isSmoothDiscrete [Group G] [IsTopologicalGroup G]
    {X : TopRep.{w} R G} (hX : IsSmoothDiscrete R X) :
    Continuous fun p : G × X.V ↦ X.ρ p.1 p.2 := by
  let _ : DistribMulAction G X.V := X.distribMulAction
  exact hX.continuousSMul.continuous_smul

variable [Group G] [ContinuousMul G]

/-- Underlying continuous map of the `n`-th inhomogeneous coboundary. -/
private def inhomogeneousCochainsDFun (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ)
    (f : C(Fin n → G, X.V)) : C(Fin (n + 1) → G, X.V) where
  toFun g := X.ρ (g 0) (f (Fin.tail g)) +
    ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • f (j.contractNth (· * ·) g)
  continuous_toFun :=
    (hX.comp ((continuous_apply 0).prodMk (f.continuous.comp (tailMap n).continuous))).add
      (continuous_finsetSum _ fun j _ ↦
        ((f.continuous.comp (contractNthMap n j).continuous).const_smul
          ((-1 : ℤ) ^ ((j : ℕ) + 1))).congr fun _ ↦ rfl)

private theorem inhomogeneousCochainsDFun_apply (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ)
    (f : C(Fin n → G, X.V)) (g : Fin (n + 1) → G) :
    inhomogeneousCochainsDFun X hX n f g =
      X.ρ (g 0) (f (Fin.tail g)) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • f (j.contractNth (· * ·) g) := rfl

/-- The `n`-th inhomogeneous coboundary `C(Fin n → G, X.V) → C(Fin (n + 1) → G, X.V)` as an
`R`-linear morphism in `ModuleCat R`. No local compactness on `G` is required. -/
def inhomogeneousCochainsD (X : TopRep.{w} R G) (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (n : ℕ) :
    ModuleCat.of R C(Fin n → G, X.V) ⟶ ModuleCat.of R C(Fin (n + 1) → G, X.V) :=
  ModuleCat.ofHom
    { toFun := inhomogeneousCochainsDFun X hX n
      map_add' f₁ f₂ := by
        ext g
        simp only [ContinuousMap.add_apply, inhomogeneousCochainsDFun_apply, map_add, zsmul_add,
          Finset.sum_add_distrib]
        abel
      map_smul' r f := by
        ext g
        simp only [RingHom.id_apply, ContinuousMap.smul_apply, inhomogeneousCochainsDFun_apply,
          map_smul, smul_add, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        exact smul_comm ((-1 : ℤ) ^ ((j : ℕ) + 1)) r _ }

/-- Pointwise evaluation formula for `inhomogeneousCochainsD`. -/
@[simp]
theorem inhomogeneousCochainsD_apply (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ)
    (f : C(Fin n → G, X.V)) (g : Fin (n + 1) → G) :
    (inhomogeneousCochainsD X hX n).hom f g =
      X.ρ (g 0) (f (Fin.tail g)) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • f (j.contractNth (· * ·) g) := (rfl)

/-- In degree `0`, the inhomogeneous differential is `(d⁰ f)(g) = ρ(g₀)(f(∅)) - f(∅)`. -/
theorem inhomogeneousCochainsD_zero_apply (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (f : C(Fin 0 → G, X.V)) (g : Fin 1 → G) :
    (inhomogeneousCochainsD X hX 0).hom f g =
      X.ρ (g 0) (f Fin.elim0) - f Fin.elim0 := by
  rw [inhomogeneousCochainsD_apply, Fin.sum_univ_one]
  have h1 : Fin.tail g = Fin.elim0 := Subsingleton.elim _ _
  have h2 : (0 : Fin 1).contractNth (· * ·) g = Fin.elim0 := Subsingleton.elim _ _
  rw [h1, h2]
  simp [sub_eq_add_neg]

/-- In degree `1`, the inhomogeneous differential is
`(d¹ f)(g₀, g₁) = ρ(g₀)(f(g₁)) - f(g₀g₁) + f(g₀)`. -/
theorem inhomogeneousCochainsD_one_apply (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (f : C(Fin 1 → G, X.V)) (g : Fin 2 → G) :
    (inhomogeneousCochainsD X hX 1).hom f g =
      X.ρ (g 0) (f ![g 1]) - f ![g 0 * g 1] + f ![g 0] := by
  rw [inhomogeneousCochainsD_apply, Fin.sum_univ_two]
  have ht : Fin.tail g = ![g 1] := funext fun i ↦ by fin_cases i; rfl
  have hc0 : (0 : Fin 2).contractNth (· * ·) g = ![g 0 * g 1] :=
    funext fun i ↦ by fin_cases i; simp [Fin.contractNth_apply_of_eq]
  have hc1 : (1 : Fin 2).contractNth (· * ·) g = ![g 0] :=
    funext fun i ↦ by fin_cases i; simp [Fin.contractNth_apply_of_lt]
  rw [ht, hc0, hc1]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_zsmul, Fin.val_one,
    show (-1 : ℤ) ^ (1 + 1) = 1 by decide]
  abel

/-- In degree `2`, the inhomogeneous differential is
`(d² f)(g₀, g₁, g₂) = ρ(g₀)(f(g₁, g₂)) - f(g₀g₁, g₂) + f(g₀, g₁g₂) - f(g₀, g₁)`. -/
theorem inhomogeneousCochainsD_two_apply (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (f : C(Fin 2 → G, X.V)) (g : Fin 3 → G) :
    (inhomogeneousCochainsD X hX 2).hom f g =
      X.ρ (g 0) (f ![g 1, g 2]) - f ![g 0 * g 1, g 2] + f ![g 0, g 1 * g 2] - f ![g 0, g 1] := by
  rw [inhomogeneousCochainsD_apply, Fin.sum_univ_three]
  have ht : Fin.tail g = ![g 1, g 2] := funext fun i ↦ by fin_cases i <;> rfl
  have hc0 : (0 : Fin 3).contractNth (· * ·) g = ![g 0 * g 1, g 2] :=
    funext fun i ↦ by
      fin_cases i
      · simp [Fin.contractNth_apply_of_eq]
      · simp [Fin.contractNth_apply_of_gt]
  have hc1 : (1 : Fin 3).contractNth (· * ·) g = ![g 0, g 1 * g 2] :=
    funext fun i ↦ by
      fin_cases i
      · simp [Fin.contractNth_apply_of_lt]
      · simp [Fin.contractNth_apply_of_eq]
  have hc2 : (2 : Fin 3).contractNth (· * ·) g = ![g 0, g 1] :=
    funext fun i ↦ by
      fin_cases i <;> simp [Fin.contractNth_apply_of_lt]
  rw [ht, hc0, hc1, hc2]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_zsmul, Fin.val_one, Fin.val_two,
    show (-1 : ℤ) ^ (1 + 1) = 1 by decide, show (-1 : ℤ) ^ (2 + 1) = -1 by decide]
  abel

/-- Consecutive inhomogeneous differentials compose to zero in every degree. -/
theorem inhomogeneousCochainsD_comp_d (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    inhomogeneousCochainsD X hX n ≫ inhomogeneousCochainsD X hX (n + 1) = 0 := by
  ext f g
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
    ContinuousMap.zero_apply]
  have hf1 : ⇑((inhomogeneousCochainsD X hX n).hom f) =
      fun h ↦ X.ρ (h 0) (f (Fin.tail h)) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • f (j.contractNth (· * ·) h) :=
    funext (inhomogeneousCochainsD_apply X hX n f)
  have hf2 : ⇑((inhomogeneousCochainsD X hX (n + 1)).hom ((inhomogeneousCochainsD X hX n).hom f)) =
      fun h ↦ X.ρ (h 0) (((inhomogeneousCochainsD X hX n).hom f) (Fin.tail h)) +
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ ((j : ℕ) + 1) •
          ((inhomogeneousCochainsD X hX n).hom f) (j.contractNth (· * ·) h) :=
    funext (inhomogeneousCochainsD_apply X hX (n + 1) ((inhomogeneousCochainsD X hX n).hom f))
  have h1 : (inhomogeneousCochainsD X hX (n + 1)).hom ((inhomogeneousCochainsD X hX n).hom f) g =
      homogenize X (n + 2)
        ((inhomogeneousCochainsD X hX (n + 1)).hom ((inhomogeneousCochainsD X hX n).hom f))
        (Fin.partialProd g) :=
    (homogenize_partialProd X (n + 2) _ g).symm
  rw [h1, hf2, ← alternatingFaceSum_homogenize X ((inhomogeneousCochainsD X hX n).hom f)]
  have h2 (i : Fin (n + 3)) :
      homogenize X (n + 1) ((inhomogeneousCochainsD X hX n).hom f)
          (Fin.partialProd g ∘ i.succAbove) =
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
          homogenize X n f (Fin.partialProd g ∘ i.succAbove ∘ j.succAbove) := by
    rw [hf1]
    exact (alternatingFaceSum_homogenize X f (Fin.partialProd g ∘ i.succAbove)).symm
  simp_rw [h2]
  exact alternatingFaceSum_comp_alternatingFaceSum (homogenize X n f) (Fin.partialProd g)

/-- The cochain complex of inhomogeneous continuous cochains `C(Fin n → G, X.V)` in `ModuleCat R`,
for a topological representation `X` with jointly continuous action. The abbreviation retains the
degreewise carriers `ModuleCat.of R C(Fin n → G, X.V)`. -/
noncomputable abbrev inhomogeneousCochains (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) :
    CochainComplex (ModuleCat.{max v w} R) ℕ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of R C(Fin n → G, X.V))
    (inhomogeneousCochainsD X hX)
    (inhomogeneousCochainsD_comp_d X hX)

/-- The degree-`n` object of `inhomogeneousCochains X hX` is `C(Fin n → G, X.V)`. -/
@[simp]
theorem inhomogeneousCochains_X (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    (inhomogeneousCochains X hX).X n = ModuleCat.of R C(Fin n → G, X.V) := (rfl)

/-- The differential `(inhomogeneousCochains X hX).d n (n + 1)` is
`inhomogeneousCochainsD X hX n`. -/
theorem inhomogeneousCochains_d (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    (inhomogeneousCochains X hX).d n (n + 1) = inhomogeneousCochainsD X hX n := by
  apply CochainComplex.of_d

/-- Pointwise evaluation formula for `(inhomogeneousCochains X hX).d n (n + 1)`. -/
theorem inhomogeneousCochains_d_apply (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ)
    (f : C(Fin n → G, X.V)) (g : Fin (n + 1) → G) :
    ((inhomogeneousCochains X hX).d n (n + 1)).hom f g =
      (inhomogeneousCochainsD X hX n).hom f g := by
  rw [inhomogeneousCochains_d]

end AlgebraicComplex

/-! ### The topological cochain complex for locally compact `G` -/

section TopologicalComplex

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [ContinuousMul G] [LocallyCompactSpace G]

/-- When `G` is locally compact, the inhomogeneous differential `dⁿ` is continuous for the
compact-open topology on `C(Fin n → G, X.V)`. -/
theorem continuous_inhomogeneousCochainsD (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    Continuous (inhomogeneousCochainsD X hX n).hom := by
  let lead (f : C(Fin n → G, X.V)) : C(Fin (n + 1) → G, X.V) :=
    ⟨fun g ↦ X.ρ (g 0) (f (Fin.tail g)),
      hX.comp ((continuous_apply 0).prodMk (f.continuous.comp (tailMap n).continuous))⟩
  have hlead : Continuous lead := by
    refine ContinuousMap.continuous_of_continuous_uncurry lead ?_
    have hev : Continuous fun p : C(Fin n → G, X.V) × (Fin (n + 1) → G) ↦ p.1 (Fin.tail p.2) :=
      continuous_eval.comp (continuous_fst.prodMk ((tailMap n).continuous.comp continuous_snd))
    exact hX.comp (((continuous_apply 0).comp continuous_snd).prodMk hev)
  have hsum : Continuous fun f : C(Fin n → G, X.V) ↦
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • f.comp (contractNthMap n j) :=
    continuous_finsetSum _ fun j _ ↦
      ((ContinuousMap.continuous_precomp (contractNthMap n j)).const_smul
        ((-1 : ℤ) ^ ((j : ℕ) + 1))).congr fun _ ↦ rfl
  refine (hlead.add hsum).congr fun f ↦ ContinuousMap.ext fun g ↦ ?_
  rw [Pi.add_apply, ContinuousMap.add_apply, inhomogeneousCochainsD_apply, ContinuousMap.sum_apply]
  simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, contractNthMap_apply]
  rfl

/-- The `n`-th inhomogeneous differential as a morphism in `TopModuleCat R` (compact-open
topology), for locally compact `G`. -/
def inhomogeneousCochainsTopD (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    TopModuleCat.of R C(Fin n → G, X.V) ⟶ TopModuleCat.of R C(Fin (n + 1) → G, X.V) :=
  TopModuleCat.ofHom ⟨(inhomogeneousCochainsD X hX n).hom,
    continuous_inhomogeneousCochainsD X hX n⟩

@[simp]
theorem inhomogeneousCochainsTopD_apply (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ)
    (f : C(Fin n → G, X.V)) (g : Fin (n + 1) → G) :
    (inhomogeneousCochainsTopD X hX n).hom f g =
      (inhomogeneousCochainsD X hX n).hom f g := (rfl)

/-- Consecutive topological inhomogeneous differentials compose to zero. -/
theorem inhomogeneousCochainsTopD_comp_d (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    inhomogeneousCochainsTopD X hX n ≫ inhomogeneousCochainsTopD X hX (n + 1) = 0 := by
  ext f g
  exact congrArg (fun h : C(Fin (n + 2) → G, X.V) ↦ h g)
    (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (inhomogeneousCochainsD_comp_d X hX n)) f)

/-- The cochain complex of inhomogeneous continuous cochains in `TopModuleCat R`, with the
compact-open topology in every degree, for locally compact `G`. The abbreviation retains the
degreewise carriers `TopModuleCat.of R C(Fin n → G, X.V)`. -/
noncomputable abbrev inhomogeneousCochainsTop (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) :
    CochainComplex (TopModuleCat.{max v w} R) ℕ :=
  CochainComplex.of
    (fun n ↦ TopModuleCat.of R C(Fin n → G, X.V))
    (inhomogeneousCochainsTopD X hX)
    (inhomogeneousCochainsTopD_comp_d X hX)

@[simp]
theorem inhomogeneousCochainsTop_X (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    (inhomogeneousCochainsTop X hX).X n = TopModuleCat.of R C(Fin n → G, X.V) := (rfl)

/-- The `n`-th differential of `inhomogeneousCochainsTop` is `inhomogeneousCochainsTopD`. -/
theorem inhomogeneousCochainsTop_d (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    (inhomogeneousCochainsTop X hX).d n (n + 1) = inhomogeneousCochainsTopD X hX n := by
  apply CochainComplex.of_d

/-- Forgetting topology from `inhomogeneousCochainsTop` recovers `inhomogeneousCochains`. -/
noncomputable def forget₂MapInhomogeneousCochainsTopIso (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) :
    ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapHomologicalComplex _).obj
      (inhomogeneousCochainsTop X hX) ≅ inhomogeneousCochains X hX :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) fun i j (hij : i + 1 = j) ↦ by
    subst hij
    rw [Functor.mapHomologicalComplex_obj_d, Iso.refl_hom, Iso.refl_hom,
      Category.id_comp, Category.comp_id, inhomogeneousCochains_d, inhomogeneousCochainsTop_d]
    rfl

@[simp]
theorem forget₂MapInhomogeneousCochainsTopIso_hom_f (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    (forget₂MapInhomogeneousCochainsTopIso X hX).hom.f n = 𝟙 _ := (rfl)

@[simp]
theorem forget₂MapInhomogeneousCochainsTopIso_inv_f (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    (forget₂MapInhomogeneousCochainsTopIso X hX).inv.f n = 𝟙 _ := (rfl)

end TopologicalComplex

/-! ### Functoriality in compatible pairs and coefficient morphisms -/

section Functoriality

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G H K : Type v} [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H]
  [Group K] [TopologicalSpace K]

/-- The degree-`n` map on inhomogeneous continuous cochains induced by a compatible pair
`(φ : H →ₜ* G, f : TopRep.res φ X ⟶ Y)`, sending `c ↦ f ∘ c ∘ φ`. -/
def inhomogeneousCochainsMapF (φ : H →ₜ* G) {X : TopRep.{w} R G} {Y : TopRep.{w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    ModuleCat.of R C(Fin n → G, X.V) ⟶ ModuleCat.of R C(Fin n → H, Y.V) :=
  ModuleCat.ofHom
    { toFun c := ⟨fun h ↦ f.hom (c (φ ∘ h)),
        f.hom.continuous.comp (c.continuous.comp (continuous_pi fun i ↦
          φ.continuous.comp (continuous_apply i)))⟩
      map_add' _ _ := by ext h; simp
      map_smul' _ _ := by ext h; simp }

@[simp]
theorem inhomogeneousCochainsMapF_apply (φ : H →ₜ* G) {X : TopRep.{w} R G} {Y : TopRep.{w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) (c : C(Fin n → G, X.V)) (h : Fin n → H) :
    (inhomogeneousCochainsMapF φ f n).hom c h = f.hom (c (φ ∘ h)) := (rfl)

variable [ContinuousMul G] [ContinuousMul H] [ContinuousMul K]

/-- The cochain map `inhomogeneousCochains X hX ⟶ inhomogeneousCochains Y hY` induced by a
compatible pair `(φ : H →ₜ* G, f : TopRep.res φ X ⟶ Y)`. -/
noncomputable def inhomogeneousCochainsMap (φ : H →ₜ* G) {X : TopRep.{w} R G} {Y : TopRep.{w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : H × Y.V ↦ Y.ρ p.1 p.2) :
    inhomogeneousCochains X hX ⟶ inhomogeneousCochains Y hY where
  f n := inhomogeneousCochainsMapF φ f n
  comm' i j (hij : i + 1 = j) := by
    subst hij
    rw [inhomogeneousCochains_d, inhomogeneousCochains_d]
    ext c h
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [inhomogeneousCochainsD_apply, inhomogeneousCochainsMapF_apply,
      inhomogeneousCochainsMapF_apply, inhomogeneousCochainsD_apply]
    simp only [map_add, map_sum, map_zsmul]
    congr 1
    · exact (TopRep.hom_comm_apply f (h 0) (c (Fin.tail (φ ∘ h)))).symm
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      have hcon : φ ∘ k.contractNth (· * ·) h = k.contractNth (· * ·) (φ ∘ h) :=
        Fin.comp_contractNth (· * ·) (· * ·) (fun a b ↦ map_mul φ a b) k h
      rw [inhomogeneousCochainsMapF_apply, hcon]

@[simp]
theorem inhomogeneousCochainsMap_f (φ : H →ₜ* G) {X : TopRep.{w} R G} {Y : TopRep.{w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : H × Y.V ↦ Y.ρ p.1 p.2) (n : ℕ) :
    (inhomogeneousCochainsMap φ f hX hY).f n = inhomogeneousCochainsMapF φ f n := (rfl)

@[simp]
theorem inhomogeneousCochainsMap_id (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) :
    inhomogeneousCochainsMap (ContinuousMonoidHom.id G) (𝟙 X) hX hX =
      𝟙 (inhomogeneousCochains X hX) := by
  ext n c g
  rfl

/-- Composition of compatible-pair maps on `inhomogeneousCochains`. -/
@[reassoc]
theorem inhomogeneousCochainsMap_comp (φ : H →ₜ* G) (ψ : K →ₜ* H)
    {X : TopRep.{w} R G} {Y : TopRep.{w} R H} {Z : TopRep.{w} R K}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (g : TopRep.res (ψ : K →* H) Y ⟶ Z)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : H × Y.V ↦ Y.ρ p.1 p.2)
    (hZ : Continuous fun p : K × Z.V ↦ Z.ρ p.1 p.2) :
    inhomogeneousCochainsMap (φ.comp ψ)
        ((TopRep.resFunctor (ψ : K →* H)).map f ≫ g) hX hZ =
      inhomogeneousCochainsMap φ f hX hY ≫ inhomogeneousCochainsMap ψ g hY hZ := by
  ext n c k
  rfl

/-- The cochain map `inhomogeneousCochains X hX ⟶ inhomogeneousCochains Y hY` induced by a
coefficient morphism `f : X ⟶ Y`. -/
noncomputable def inhomogeneousCochainsCoeffMap {X Y : TopRep.{w} R G} (f : X ⟶ Y)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2) :
    inhomogeneousCochains X hX ⟶ inhomogeneousCochains Y hY :=
  inhomogeneousCochainsMap (ContinuousMonoidHom.id G) f hX hY

/-- The defining equation of `inhomogeneousCochainsCoeffMap`: it is `inhomogeneousCochainsMap` at
`φ = id`. -/
theorem inhomogeneousCochainsCoeffMap_def {X Y : TopRep.{w} R G} (f : X ⟶ Y)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2) :
    inhomogeneousCochainsCoeffMap f hX hY =
      inhomogeneousCochainsMap (ContinuousMonoidHom.id G) f hX hY := (rfl)

@[simp]
theorem inhomogeneousCochainsCoeffMap_f {X Y : TopRep.{w} R G} (f : X ⟶ Y)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2) (n : ℕ) :
    (inhomogeneousCochainsCoeffMap f hX hY).f n =
      inhomogeneousCochainsMapF (ContinuousMonoidHom.id G) f n := (rfl)

@[simp]
theorem inhomogeneousCochainsCoeffMap_id (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) :
    inhomogeneousCochainsCoeffMap (𝟙 X) hX hX = 𝟙 (inhomogeneousCochains X hX) :=
  inhomogeneousCochainsMap_id X hX

@[simp, reassoc]
theorem inhomogeneousCochainsCoeffMap_comp {X Y Z : TopRep.{w} R G}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2)
    (hZ : Continuous fun p : G × Z.V ↦ Z.ρ p.1 p.2) :
    inhomogeneousCochainsCoeffMap (f ≫ g) hX hZ =
      inhomogeneousCochainsCoeffMap f hX hY ≫ inhomogeneousCochainsCoeffMap g hY hZ := by
  ext n c x
  rfl

@[simp]
theorem inhomogeneousCochainsCoeffMap_zero {X Y : TopRep.{w} R G}
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2) :
    inhomogeneousCochainsCoeffMap (0 : X ⟶ Y) hX hY = 0 := by
  ext n c x
  rfl

@[simp]
theorem inhomogeneousCochainsCoeffMap_add {X Y : TopRep.{w} R G} (f g : X ⟶ Y)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : G × Y.V ↦ Y.ρ p.1 p.2) :
    inhomogeneousCochainsCoeffMap (f + g) hX hY =
      inhomogeneousCochainsCoeffMap f hX hY + inhomogeneousCochainsCoeffMap g hX hY := by
  ext n c x
  rfl

/-- The topological cochain map `inhomogeneousCochainsTop X hX ⟶ inhomogeneousCochainsTop Y hY`
induced by a compatible pair `(φ : H →ₜ* G, f : TopRep.res φ X ⟶ Y)` between locally compact
groups. -/
noncomputable def inhomogeneousCochainsTopMap [LocallyCompactSpace G] [LocallyCompactSpace H]
    (φ : H →ₜ* G) {X : TopRep.{w} R G} {Y : TopRep.{w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : H × Y.V ↦ Y.ρ p.1 p.2) :
    inhomogeneousCochainsTop X hX ⟶ inhomogeneousCochainsTop Y hY where
  f n := TopModuleCat.ofHom
    { toLinearMap := (inhomogeneousCochainsMapF φ f n).hom
      cont := by
        let pre : C(Fin n → H, Fin n → G) :=
          ⟨fun h i ↦ φ (h i), continuous_pi fun i ↦ φ.continuous.comp (continuous_apply i)⟩
        let post : C(X.V, Y.V) := ⟨f.hom, f.hom.continuous⟩
        exact (ContinuousMap.continuous_postcomp post).comp (ContinuousMap.continuous_precomp pre) }
  comm' i j (hij : i + 1 = j) := by
    subst hij
    rw [inhomogeneousCochainsTop_d, inhomogeneousCochainsTop_d]
    have hcomm := (inhomogeneousCochainsMap φ f hX hY).comm i (i + 1)
    rw [inhomogeneousCochainsMap_f, inhomogeneousCochainsMap_f,
      inhomogeneousCochains_d, inhomogeneousCochains_d] at hcomm
    ext c h
    exact congrArg (fun k : C(Fin (i + 1) → H, Y.V) ↦ k h)
      (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcomm) c)

@[simp]
theorem inhomogeneousCochainsTopMap_f_apply [LocallyCompactSpace G] [LocallyCompactSpace H]
    (φ : H →ₜ* G) {X : TopRep.{w} R G} {Y : TopRep.{w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : H × Y.V ↦ Y.ρ p.1 p.2) (n : ℕ)
    (c : C(Fin n → G, X.V)) (h : Fin n → H) :
    ((inhomogeneousCochainsTopMap φ f hX hY).f n).hom c h = f.hom (c (φ ∘ h)) := (rfl)

/-- Forgetting topology intertwines `inhomogeneousCochainsTopMap` with
`inhomogeneousCochainsMap`. -/
@[reassoc]
theorem forget₂Map_inhomogeneousCochainsTopMap [LocallyCompactSpace G] [LocallyCompactSpace H]
    (φ : H →ₜ* G) {X : TopRep.{w} R G} {Y : TopRep.{w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (hY : Continuous fun p : H × Y.V ↦ Y.ρ p.1 p.2) :
    ((forget₂ (TopModuleCat.{max v w} R) (ModuleCat.{max v w} R)).mapHomologicalComplex _).map
        (inhomogeneousCochainsTopMap φ f hX hY) ≫
      (forget₂MapInhomogeneousCochainsTopIso Y hY).hom =
    (forget₂MapInhomogeneousCochainsTopIso X hX).hom ≫
      inhomogeneousCochainsMap φ f hX hY := by
  ext n c h
  rfl

end Functoriality

/-! ### Check: trivial group -/

section TrivialGroup

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [Subsingleton G]

/-- Over a trivial group, every degree-`n` inhomogeneous cochain space `C(Fin n → G, X.V)` is
linearly equivalent to `X.V` by evaluation at the constant tuple `1`. -/
def inhomogeneousCochainsTermEquivOfSubsingleton (X : TopRep.{w} R G) (n : ℕ) :
    C(Fin n → G, X.V) ≃ₗ[R] X.V where
  toFun f := f (fun _ ↦ 1)
  invFun x := ContinuousMap.const _ x
  left_inv f := ContinuousMap.ext fun _ ↦ congrArg f (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem inhomogeneousCochainsTermEquivOfSubsingleton_apply (X : TopRep.{w} R G) (n : ℕ)
    (f : C(Fin n → G, X.V)) :
    inhomogeneousCochainsTermEquivOfSubsingleton X n f = f (fun _ ↦ 1) := (rfl)

@[simp]
theorem inhomogeneousCochainsTermEquivOfSubsingleton_symm_apply (X : TopRep.{w} R G) (n : ℕ)
    (x : X.V) (g : Fin n → G) :
    (inhomogeneousCochainsTermEquivOfSubsingleton X n).symm x g = x := (rfl)

variable [ContinuousMul G]

/-- The alternating sum `∑ i : Fin m, (-1 : ℤ) ^ (i : ℕ)` is `0` for even `m` and `1` for
odd `m`. -/
private theorem sum_neg_one_pow_fin :
    ∀ k : ℕ, (∑ i : Fin (2 * k), (-1 : ℤ) ^ (i : ℕ) = 0) ∧
      (∑ i : Fin (2 * k + 1), (-1 : ℤ) ^ (i : ℕ) = 1)
  | 0 => by simp
  | k + 1 => by
    obtain ⟨_, hodd⟩ := sum_neg_one_pow_fin k
    have h2 : ∑ i : Fin (2 * (k + 1)), (-1 : ℤ) ^ (i : ℕ) = 0 := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, hodd, pow_add, pow_mul]
      norm_num
    refine ⟨h2, ?_⟩
    rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by omega, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, h2, zero_add, pow_mul]
    norm_num

/-- Over a trivial group, every even-degree inhomogeneous differential vanishes. -/
theorem inhomogeneousCochainsD_even_of_subsingleton (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (k : ℕ) :
    inhomogeneousCochainsD X hX (2 * k) = 0 := by
  ext f g
  rw [inhomogeneousCochainsD_apply]
  have hg0 : g 0 = 1 := Subsingleton.elim _ _
  have htail : Fin.tail g = fun _ ↦ 1 := Subsingleton.elim _ _
  have hcon (j : Fin (2 * k + 1)) : j.contractNth (· * ·) g = fun _ ↦ 1 := Subsingleton.elim _ _
  simp only [hg0, htail, hcon, map_one, one_apply_eq_self, ModuleCat.hom_zero, LinearMap.zero_apply,
    ContinuousMap.zero_apply]
  have hsum : (1 : ℤ) + ∑ j : Fin (2 * k + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) = 0 := by
    have := (sum_neg_one_pow_fin (k + 1)).1
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Fin.sum_univ_succ] at this
    simpa only [Fin.val_zero, pow_zero, Fin.val_succ] using this
  calc
    f (fun _ ↦ 1) + ∑ j : Fin (2 * k + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • f (fun _ ↦ 1)
        = ((1 : ℤ) + ∑ j : Fin (2 * k + 1), (-1 : ℤ) ^ ((j : ℕ) + 1)) • f (fun _ ↦ 1) := by
          rw [add_zsmul, one_zsmul, Finset.sum_smul]
    _ = 0 := by rw [hsum, zero_zsmul]

/-- Over a trivial group, every odd-degree inhomogeneous differential acts as the identity under
the identification `C(Fin n → G, X.V) ≃ₗ[R] X.V`. -/
theorem inhomogeneousCochainsD_odd_of_subsingleton (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (k : ℕ)
    (f : C(Fin (2 * k + 1) → G, X.V)) (g : Fin (2 * k + 2) → G) :
    (inhomogeneousCochainsD X hX (2 * k + 1)).hom f g = f (fun _ ↦ 1) := by
  rw [inhomogeneousCochainsD_apply]
  have hg0 : g 0 = 1 := Subsingleton.elim _ _
  have htail : Fin.tail g = fun _ ↦ 1 := Subsingleton.elim _ _
  have hcon (j : Fin (2 * k + 2)) : j.contractNth (· * ·) g = fun _ ↦ 1 := Subsingleton.elim _ _
  simp only [hg0, htail, hcon, map_one, one_apply_eq_self]
  have hsum : (1 : ℤ) + ∑ j : Fin (2 * k + 2), (-1 : ℤ) ^ ((j : ℕ) + 1) = 1 := by
    have := (sum_neg_one_pow_fin (k + 1)).2
    rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega, Fin.sum_univ_succ] at this
    simpa only [Fin.val_zero, pow_zero, Fin.val_succ] using this
  calc
    f (fun _ ↦ 1) + ∑ j : Fin (2 * k + 2), (-1 : ℤ) ^ ((j : ℕ) + 1) • f (fun _ ↦ 1)
        = ((1 : ℤ) + ∑ j : Fin (2 * k + 2), (-1 : ℤ) ^ ((j : ℕ) + 1)) • f (fun _ ↦ 1) := by
          rw [add_zsmul, one_zsmul, Finset.sum_smul]
    _ = f (fun _ ↦ 1) := by rw [hsum, one_zsmul]

/-- Over a trivial group, the inhomogeneous continuous cochain complex is exact in every positive
degree. -/
theorem exactAt_inhomogeneousCochains_succ_of_subsingleton (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    (inhomogeneousCochains X hX).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro (f : C(Fin (n + 1) → G, X.V)) hf
  rw [LinearMap.mem_ker] at hf
  rw [LinearMap.mem_range]
  rcases Nat.even_or_odd (n + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hn : n = 2 * m + 1 := by omega
    subst hn
    refine ⟨ContinuousMap.const _ (f (fun _ ↦ 1)), ContinuousMap.ext fun g ↦ ?_⟩
    rw [HomologicalComplex.shortComplexFunctor'_obj_f, inhomogeneousCochains_d_apply,
      inhomogeneousCochainsD_odd_of_subsingleton]
    exact congrArg f (Subsingleton.elim _ _)
  · have hn : n = 2 * k := by omega
    subst hn
    refine ⟨0, ContinuousMap.ext fun g ↦ ?_⟩
    rw [map_zero]
    have hval := congrArg (fun h : C(Fin (2 * k + 2) → G, X.V) ↦ h (fun _ ↦ 1)) hf
    rw [HomologicalComplex.shortComplexFunctor'_obj_g, inhomogeneousCochains_d_apply,
      inhomogeneousCochainsD_odd_of_subsingleton] at hval
    exact hval.symm.trans (congrArg f (Subsingleton.elim (fun _ ↦ 1) g))

/-- Over a trivial group, every positive-degree cohomology module of the inhomogeneous continuous
cochain complex vanishes. -/
theorem isZero_inhomogeneousCochains_homology_succ_of_subsingleton (X : TopRep.{w} R G)
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    Limits.IsZero ((inhomogeneousCochains X hX).homology (n + 1)) :=
  (exactAt_inhomogeneousCochains_succ_of_subsingleton X hX n).isZero_homology

end TrivialGroup

end TauCeti.ContinuousCohomology
