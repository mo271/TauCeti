/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.StdBasis
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Complex.Weierstrass
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass
import TauCeti.Geometry.Manifold.ContMDiff.Analytic

/-!
# Oka's coherence theorem

For a finite tuple or matrix of holomorphic functions on an open subset `U` of a
finite-dimensional complex normed space or boundaryless complex manifold, near every point `x ∈ U`
there exist an open neighbourhood `V ⊆ U` of `x` and finitely many holomorphic relation tuples on
`V` whose germs generate the module of germs of relations at every point `y ∈ V`. Equivalently,
the sheaf of relations (the kernel of any morphism between finite free modules over the holomorphic
structure sheaf) is locally finitely generated, the heart of Oka's coherence theorem.

## Proof outline

The normed-space theorem is proved by induction on the complex dimension `n` of the base space:

1. **System-to-scalar reduction:** Induction on the number of equations reduces finite systems
   `F : κ → ι → E → ℂ` to a single scalar equation `f : ι → E → ℂ` by pulling back the remaining
   equation along local relation generators of the preceding equations.
2. **Base dimension zero:** Every point equals the base point, every function is constant, and the
   relation space is the kernel of a `ℂ`-linear functional spanned by a finite `ℂ`-basis.
3. **Inductive step on `(Fin n → ℂ) × ℂ`:** By inner induction on the number `k` of functions:
   * If `k = 0`, the empty family suffices; if some `f i₀` vanishes near `p₀`, splitting off the
     basis vector at `i₀` reduces from `k + 1` to `k` functions.
   * Otherwise `∏ i, f i` does not vanish identically near `p₀` (holomorphic stalks are domains),
     so a coordinate change (`AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`) and
     translation place `p₀` at `(0, 0)` with vertical slices of finite analytic order `d i`.
   * Local Weierstrass preparation (`AnalyticAt.exists_weierstrassPreparation`) factors each `f i`
     on `W₀ ×ˢ W₁` into a monic vertical polynomial `P i` times a nonvanishing analytic unit `u i`.
   * At any `(y, η) ∈ W₀ ×ˢ W₁`, stalkwise Weierstrass preparation and polynomial divisibility
     (`existsUnique_weierstrassPreparation`, `evalVertical_dvd_iff_of_isDistinguishedAt`) factor
     `P_last = D * Q` centered at `η` with `D` distinguished at `y` and `Q` a unit germ at `(y, η)`.
     Weierstrass division (`existsUnique_weierstrassDivision_of_isDistinguishedAt`) of the first `k`
     components by `D` and subtraction of Koszul relations reduce any germ relation (up to the unit
     `Q`) to a polynomial relation in `𝒪_{B, y}[w]` of degree `< d` (`d = (sup_i d_i) ⊔ 1`), which
     corresponds to `2 d` scalar analytic equations on `W₀` handled by the dimension-`n` hypothesis.

Holomorphic charts transfer the normed-space theorem to `TauCeti.holomorphicStructureSheaf` on any
boundaryless `C¹` complex manifold without Hausdorffness or second-countability assumptions, and
`smoothSectionsEquiv` together with `smoothStalkIso` exports it to `smoothSheafCommRing`.

## Main results

* `TauCeti.exists_analyticOnNhd_systemRelationGenerators`,
  `TauCeti.exists_analyticOnNhd_relationGenerators`: Oka's coherence theorem for finite systems and
  tuples of analytic functions on open subsets of a finite-dimensional complex normed space.
* `TauCeti.holomorphicStructureSheaf.exists_span_germ_eq_ker_mulVecLin`,
  `TauCeti.holomorphicStructureSheaf.exists_span_germ_eq_ker_linearCombination`: local finite
  generation of stalk relation kernels for `holomorphicStructureSheaf` on complex manifolds.
* `TauCeti.holomorphicStructureSheaf.exists_span_smoothStalk_germ_eq_ker_mulVecLin`,
  `TauCeti.holomorphicStructureSheaf.exists_span_smoothStalk_germ_eq_ker_linearCombination`: the
  corresponding theorems for Mathlib's `smoothSheafCommRing`.

## References

* K. Oka, *Sur les fonctions analytiques de plusieurs variables. VII*, Bull. Soc. Math. France 78
  (1950), 1–27.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, §3.3, Theorem 3.19.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.4, Theorem 6.4.1.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. IV, §B, Thm. 3.
* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Chapter 2, §5.
-/

public noncomputable section

open CategoryTheory Filter Function IsManifold Metric Opposite Polynomial Set TopologicalSpace
  Topology
open scoped ContDiff Manifold PowerSeries

namespace TauCeti

section Aux

/-- Auxiliary predicate for the induction: near `x ∈ U`, the simultaneous germ relations of a
family of analytic rows `F : κ → ι → E → ℂ` are generated at every point of an open neighbourhood
`V ⊆ U` of `x` by finitely many analytic relation vectors on `V`. -/
private def HasLocalRelationGenerators {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {κ ι : Type*} [Fintype ι] (U : Set E) (F : κ → ι → E → ℂ) (x : E) : Prop :=
  ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ (m : ℕ) (r : Fin m → ι → E → ℂ),
    (∀ j i, AnalyticOnNhd ℂ (r j i) V) ∧
    (∀ j l, ∀ y ∈ V, ∑ i, r j i y * F l i y = 0) ∧
    ∀ y ∈ V, ∀ a : ι → E → ℂ, (∀ i, AnalyticAt ℂ (a i) y) →
      (∀ l, (fun z ↦ ∑ i, a i z * F l i z) =ᶠ[𝓝 y] 0) →
      ∃ b : Fin m → E → ℂ, (∀ j, AnalyticAt ℂ (b j) y) ∧
        ∀ i, a i =ᶠ[𝓝 y] fun z ↦ ∑ j, b j z * r j i z

section BasicReductions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Enlarging the ambient set `U` preserves local generation of relations at `x`. -/
private theorem HasLocalRelationGenerators.mono {κ ι : Type*} [Fintype ι] {U U' : Set E}
    {F : κ → ι → E → ℂ} {x : E} (h : HasLocalRelationGenerators U F x) (hUU' : U ⊆ U') :
    HasLocalRelationGenerators U' F x := by
  obtain ⟨V, hVo, hxV, hVU, m, r, hr_an, hr_rel, hr_gen⟩ := h
  exact ⟨V, hVo, hxV, hVU.trans hUU', m, r, hr_an, hr_rel, hr_gen⟩

/-- Replacing `F` by a family `G` agreeing with `F` on `U` preserves local relation generation. -/
private theorem HasLocalRelationGenerators.congr_eqOn {κ ι : Type*} [Fintype ι] {U : Set E}
    {F G : κ → ι → E → ℂ} {x : E} (h : HasLocalRelationGenerators U F x)
    (hFG : ∀ l i, EqOn (F l i) (G l i) U) :
    HasLocalRelationGenerators U G x := by
  obtain ⟨V, hVo, hxV, hVU, m, r, hr_an, hr_rel, hr_gen⟩ := h
  refine ⟨V, hVo, hxV, hVU, m, r, hr_an, fun j l y hy ↦ ?_, fun y hy a ha hrel ↦ ?_⟩
  · simpa only [fun i ↦ hFG l i (hVU hy)] using hr_rel j l y hy
  · refine hr_gen y hy a ha fun l ↦ (hrel l).mp ?_
    filter_upwards [hVo.mem_nhds hy] with z hz h0
    simpa only [fun i ↦ hFG l i (hVU hz)] using h0

/-- Reindexing the columns along an equivalence preserves local relation generation. -/
private theorem HasLocalRelationGenerators.reindex_cols {κ ι ι' : Type*} [Fintype ι] [Fintype ι']
    {U : Set E} {F : κ → ι → E → ℂ} {x : E} (e : ι' ≃ ι)
    (h : HasLocalRelationGenerators U (fun l i' ↦ F l (e i')) x) :
    HasLocalRelationGenerators U F x := by
  obtain ⟨V, hVo, hxV, hVU, m, r, hr_an, hr_rel, hr_gen⟩ := h
  refine ⟨V, hVo, hxV, hVU, m, fun j i ↦ r j (e.symm i),
    fun j i ↦ hr_an j (e.symm i), fun j l y hy ↦ ?_, fun y hy a ha hrel ↦ ?_⟩
  · rw [← e.sum_comp]
    simpa only [Equiv.symm_apply_apply] using hr_rel j l y hy
  · have hrel' (l : κ) : (fun z ↦ ∑ i', a (e i') z * F l (e i') z) =ᶠ[𝓝 y] 0 :=
      (hrel l).mono fun z h0 ↦ (e.sum_comp fun i ↦ a i z * F l i z).trans h0
    obtain ⟨b, hb_an, hb⟩ := hr_gen y hy (fun i' ↦ a (e i')) (fun i' ↦ ha (e i')) hrel'
    exact ⟨b, hb_an, fun i ↦ by simpa only [Equiv.apply_symm_apply] using hb (e.symm i)⟩

/-- Reindexing the rows along an equivalence preserves local relation generation. -/
private theorem HasLocalRelationGenerators.reindex_rows {κ κ' ι : Type*} [Fintype ι]
    {U : Set E} {F : κ → ι → E → ℂ} {x : E} (e : κ' ≃ κ)
    (h : HasLocalRelationGenerators U (fun l' i ↦ F (e l') i) x) :
    HasLocalRelationGenerators U F x := by
  obtain ⟨V, hVo, hxV, hVU, m, r, hr_an, hr_rel, hr_gen⟩ := h
  refine ⟨V, hVo, hxV, hVU, m, r, hr_an, fun j l y hy ↦ ?_, fun y hy a ha hrel ↦ ?_⟩
  · simpa only [Equiv.apply_symm_apply] using hr_rel j (e.symm l) y hy
  · exact hr_gen y hy a ha fun l' ↦ hrel (e l')

/-- Transporting local relation generation along a global analytic equivalence `φ : E' → E` with
analytic inverse `ψ : E → E'`. -/
private theorem HasLocalRelationGenerators.of_analytic_equiv
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {κ ι : Type*} [Fintype ι] {U : Set E} {F : κ → ι → E → ℂ}
    {φ : E' → E} {ψ : E → E'} (hφ : ∀ z, AnalyticAt ℂ φ z) (hψ : ∀ w, AnalyticAt ℂ ψ w)
    (hleft : LeftInverse ψ φ) (hright : RightInverse ψ φ) {z₀ : E'}
    (h : HasLocalRelationGenerators (φ ⁻¹' U) (fun l i z ↦ F l i (φ z)) z₀) :
    HasLocalRelationGenerators U F (φ z₀) := by
  obtain ⟨V₁, hV₁o, hz₀, hV₁U, m, r₁, hr₁_an, hr₁_rel, hr₁_gen⟩ := h
  have hψ_cont : Continuous ψ := continuous_iff_continuousAt.2 fun w ↦ (hψ w).continuousAt
  refine ⟨ψ ⁻¹' V₁, hV₁o.preimage hψ_cont, by simpa only [mem_preimage, hleft z₀] using hz₀,
    fun w hw ↦ ?_, m, fun j i w ↦ r₁ j i (ψ w),
    fun j i w hw ↦ (hr₁_an j i (ψ w) hw).comp (hψ w),
    fun j l w hw ↦ by simpa only [hright w] using hr₁_rel j l (ψ w) hw,
    fun y hy a ha hrel ↦ ?_⟩
  · have hmem : φ (ψ w) ∈ U := hV₁U hw
    rwa [hright w] at hmem
  · have hφ_tendsto : Tendsto φ (𝓝 (ψ y)) (𝓝 y) := by
      simpa only [hright y] using (hφ (ψ y)).continuousAt.tendsto
    have hrel' (l : κ) : (fun z ↦ ∑ i, a i (φ z) * F l i (φ z)) =ᶠ[𝓝 (ψ y)] 0 :=
      hφ_tendsto.eventually (hrel l)
    obtain ⟨b₁, hb₁_an, hb₁⟩ := hr₁_gen (ψ y) hy (fun i z ↦ a i (φ z))
      (fun i ↦ (hright y ▸ ha i).comp (hφ (ψ y))) hrel'
    have hψ_tendsto : Tendsto ψ (𝓝 y) (𝓝 (ψ y)) := (hψ y).continuousAt.tendsto
    refine ⟨fun j w ↦ b₁ j (ψ w), fun j ↦ (hb₁_an j).comp (hψ y), fun i ↦ ?_⟩
    filter_upwards [hψ_tendsto.eventually (hb₁ i)] with w hw
    simpa only [hright w] using hw

/-- Multiplying each column `i` by an analytic function `u i` nonvanishing on `U` preserves local
relation generation. -/
private theorem HasLocalRelationGenerators.mul_nonvanishing {κ ι : Type*} [Fintype ι] {U : Set E}
    {F : κ → ι → E → ℂ} {u : ι → E → ℂ} {x : E}
    (hu_an : ∀ i, AnalyticOnNhd ℂ (u i) U) (hu_ne : ∀ i, ∀ y ∈ U, u i y ≠ 0)
    (h : HasLocalRelationGenerators U F x) :
    HasLocalRelationGenerators U (fun l i z ↦ F l i z * u i z) x := by
  obtain ⟨V, hVo, hxV, hVU, m, r, hr_an, hr_rel, hr_gen⟩ := h
  refine ⟨V, hVo, hxV, hVU, m, fun j i z ↦ r j i z * (u i z)⁻¹,
    fun j i y hy ↦ (hr_an j i y hy).fun_mul ((hu_an i y (hVU hy)).inv (hu_ne i y (hVU hy))),
    fun j l y hy ↦ ?_, fun y hy a ha hrel ↦ ?_⟩
  · have hcancel (i : ι) : r j i y * (u i y)⁻¹ * (F l i y * u i y) = r j i y * F l i y := by
      rw [mul_right_comm (r j i y), ← mul_assoc, mul_inv_cancel_right₀ (hu_ne i y (hVU hy))]
    simpa only [hcancel] using hr_rel j l y hy
  · have hrel' (l : κ) : (fun z ↦ ∑ i, (a i z * u i z) * F l i z) =ᶠ[𝓝 y] 0 := by
      simpa only [mul_assoc, mul_comm (u _ _)] using hrel l
    obtain ⟨b, hb_an, hb⟩ := hr_gen y hy (fun i z ↦ a i z * u i z)
      (fun i ↦ (ha i).fun_mul (hu_an i y (hVU hy))) hrel'
    refine ⟨b, hb_an, fun i ↦ ?_⟩
    filter_upwards [hVo.mem_nhds hy, hb i] with z hz hbz
    rw [← mul_one (a i z), ← mul_inv_cancel₀ (hu_ne i z (hVU hz)), ← mul_assoc, hbz]
    simp_rw [Finset.sum_mul, mul_assoc]

/-- For an empty system of equations (`Fin 0`), the standard basis generates all tuples. -/
private theorem hasLocalRelationGenerators_fin_zero {ι : Type*} [Fintype ι] {U : Set E}
    (hU : IsOpen U) {F : Fin 0 → ι → E → ℂ} {x : E} (hx : x ∈ U) :
    HasLocalRelationGenerators U F x := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨U, hU, hx, Subset.rfl, Fintype.card ι, fun j i _ ↦ if e i = j then 1 else 0,
    fun _ _ _ _ ↦ analyticAt_const, fun _ l ↦ l.elim0, fun _ _ a ha _ ↦
      ⟨fun j ↦ a (e.symm j), fun j ↦ ha (e.symm j), fun i ↦ Eventually.of_forall fun _ ↦ ?_⟩⟩
  dsimp only
  rw [Finset.sum_eq_single (e i) (fun j _ hj ↦ by simp [hj.symm])
    (fun h ↦ (h (Finset.mem_univ _)).elim)]
  simp

/-- Extending local relation generation from `p` equations to `p + 1` equations using single-row
relation generation on the induced scalar relation for the last row. -/
private theorem hasLocalRelationGenerators_fin_succ {p : ℕ} {ι : Type*} [Fintype ι]
    (h_single : ∀ (m₀ : ℕ) (U' : Set E), IsOpen U' → ∀ x' ∈ U',
      ∀ g : Fin m₀ → E → ℂ, (∀ j, AnalyticOnNhd ℂ (g j) U') →
        HasLocalRelationGenerators U' (fun _ : Unit ↦ g) x')
    {U : Set E} {F : Fin (p + 1) → ι → E → ℂ} {x : E}
    (hF : ∀ l i, AnalyticOnNhd ℂ (F l i) U)
    (ih : HasLocalRelationGenerators U (fun l : Fin p ↦ F l.castSucc) x) :
    HasLocalRelationGenerators U F x := by
  obtain ⟨V₁, hV₁o, hxV₁, hV₁U, m₁, r₁, hr₁_an, hr₁_rel, hr₁_gen⟩ := ih
  let g : Fin m₁ → E → ℂ := fun j z ↦ ∑ i, r₁ j i z * F (Fin.last p) i z
  have hg_an (j : Fin m₁) : AnalyticOnNhd ℂ (g j) V₁ := fun y hy ↦
    Finset.analyticAt_fun_sum _ fun i _ ↦ (hr₁_an j i y hy).fun_mul (hF _ i y (hV₁U hy))
  obtain ⟨V₂, hV₂o, hxV₂, hV₂V₁, m₂, s, hs_an, hs_rel, hs_gen⟩ :=
    h_single m₁ V₁ hV₁o x hxV₁ g hg_an
  have hswap (w : Fin m₁ → ℂ) (l : Fin (p + 1)) (z : E) :
      ∑ i, (∑ j, w j * r₁ j i z) * F l i z = ∑ j, w j * ∑ i, r₁ j i z * F l i z := by
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]; exact Finset.sum_comm
  refine ⟨V₂, hV₂o, hxV₂, hV₂V₁.trans hV₁U, m₂, fun q i z ↦ ∑ j, s q j z * r₁ j i z,
    fun q i y hy ↦ Finset.analyticAt_fun_sum _ fun j _ ↦
      (hs_an q j y hy).fun_mul (hr₁_an j i y (hV₂V₁ hy)),
    fun q l y hy ↦ ?_, fun y hy a ha hrel ↦ ?_⟩
  · refine Fin.lastCases ?_ (fun l₀ ↦ ?_) l
    · rw [hswap (s q · y)]; exact hs_rel q () y hy
    · rw [hswap (s q · y)]; simp [hr₁_rel _ l₀ y (hV₂V₁ hy)]
  · obtain ⟨c, hc_an, hc⟩ := hr₁_gen y (hV₂V₁ hy) a ha fun l₀ ↦ hrel l₀.castSucc
    have hcg : (fun z ↦ ∑ j, c j z * g j z) =ᶠ[𝓝 y] 0 :=
      (hrel (Fin.last p)).mp ((eventually_all.2 hc).mono fun z hz h0 ↦ by
        dsimp only [g]; rw [← hswap (c · z)]; simp_rw [← hz]; exact h0)
    obtain ⟨b, hb_an, hb⟩ := hs_gen y hy c hc_an fun _ ↦ hcg
    refine ⟨b, hb_an, fun i ↦ ?_⟩
    filter_upwards [hc i, eventually_all.2 hb] with z hcz hbz
    rw [hcz]; simp_rw [hbz, Finset.sum_mul, Finset.mul_sum, mul_assoc]; exact Finset.sum_comm

private theorem hasLocalRelationGenerators_fin_rows
    (h_single : ∀ (m₀ : ℕ) (U' : Set E), IsOpen U' → ∀ x' ∈ U',
      ∀ g : Fin m₀ → E → ℂ, (∀ j, AnalyticOnNhd ℂ (g j) U') →
        HasLocalRelationGenerators U' (fun _ : Unit ↦ g) x') :
    ∀ (p : ℕ) {ι : Type*} [Fintype ι] {U : Set E}, IsOpen U →
      ∀ {F : Fin p → ι → E → ℂ}, (∀ l i, AnalyticOnNhd ℂ (F l i) U) →
      ∀ {x : E}, x ∈ U → HasLocalRelationGenerators U F x
  | 0, _, _, _, hU, _, _, _, hx => hasLocalRelationGenerators_fin_zero hU hx
  | _ + 1, _, _, _, hU, _, hF, _, hx =>
    hasLocalRelationGenerators_fin_succ h_single hF
      (hasLocalRelationGenerators_fin_rows h_single _ hU (fun l i ↦ hF l.castSucc i) hx)

/-- Single-equation relation generation on `E` (for every `Fin m₀`) implies relation generation for
every finite system `F : κ → ι → E → ℂ`. -/
private theorem hasLocalRelationGenerators_system_of_single {κ ι : Type*} [Finite κ] [Fintype ι]
    (h_single : ∀ (m₀ : ℕ) (U' : Set E), IsOpen U' → ∀ x' ∈ U',
      ∀ g : Fin m₀ → E → ℂ, (∀ j, AnalyticOnNhd ℂ (g j) U') →
        HasLocalRelationGenerators U' (fun _ : Unit ↦ g) x')
    {U : Set E} (hU : IsOpen U) {F : κ → ι → E → ℂ} (hF : ∀ l i, AnalyticOnNhd ℂ (F l i) U)
    {x : E} (hx : x ∈ U) : HasLocalRelationGenerators U F x := by
  classical
  cases nonempty_fintype κ
  let e := Fintype.equivFin κ
  exact HasLocalRelationGenerators.reindex_rows e.symm
    (hasLocalRelationGenerators_fin_rows h_single (Fintype.card κ) hU
      (fun l' i ↦ hF (e.symm l') i) hx)

/-- On a zero-dimensional complex normed space, local relation generation holds because every
point equals the base point and the relation space is a `ℂ`-linear subspace of `Fin k → ℂ`. -/
private theorem hasLocalRelationGenerators_of_finrank_eq_zero [FiniteDimensional ℂ E]
    (hE : Module.finrank ℂ E = 0) {k : ℕ} {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    {f : Fin k → E → ℂ} :
    HasLocalRelationGenerators U (fun _ : Unit ↦ f) x := by
  have hall (z : E) : z = x :=
    (finrank_zero_iff_forall_zero.1 hE z).trans (finrank_zero_iff_forall_zero.1 hE x).symm
  let Λ : (Fin k → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun v ↦ ∑ i, v i * f i x
      map_add' := fun u v ↦ by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v ↦ by simp [mul_assoc, Finset.mul_sum] }
  let B := Module.finBasis ℂ (LinearMap.ker Λ)
  refine ⟨U, hU, hx, Subset.rfl, Module.finrank ℂ (LinearMap.ker Λ),
    fun j i _ ↦ (B j : Fin k → ℂ) i,
    fun _ _ _ _ ↦ analyticAt_const, fun j _ y _ ↦ ?_, fun y _ a _ hrel ↦ ?_⟩
  · rw [hall y]
    exact (B j).2
  · have hv : (fun i ↦ a i x) ∈ LinearMap.ker Λ := by
      have h0 : ∑ i, a i y * f i y = 0 := (hrel ()).self_of_nhds
      simpa only [hall y, LinearMap.mem_ker, Λ, LinearMap.coe_mk, AddHom.coe_mk] using h0
    let w : LinearMap.ker Λ := ⟨fun i ↦ a i x, hv⟩
    refine ⟨fun j _ ↦ B.repr w j, fun _ ↦ analyticAt_const, fun i ↦ Eventually.of_forall fun z ↦ ?_⟩
    have hrepr := congrArg (fun u : LinearMap.ker Λ ↦ (u : Fin k → ℂ) i) (B.sum_repr w).symm
    simpa only [hall z, Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using hrepr

/-- Splitting off a last entry `f (Fin.last k)` that vanishes on a neighbourhood of `x` reduces
local relation generation from `k + 1` functions to `k` functions. -/
private theorem hasLocalRelationGenerators_of_last_eventuallyEq_zero {k : ℕ} {U : Set E}
    (hU : IsOpen U) {x : E} (hx : x ∈ U) {f : Fin (k + 1) → E → ℂ}
    (hzero : f (Fin.last k) =ᶠ[𝓝 x] 0)
    (ih : ∀ U' : Set E, IsOpen U' → U' ⊆ U → x ∈ U' →
      HasLocalRelationGenerators U' (fun _ : Unit ↦ fun i : Fin k ↦ f i.castSucc) x) :
    HasLocalRelationGenerators U (fun _ : Unit ↦ f) x := by
  obtain ⟨W, hW_sub, hWo, hxW⟩ := _root_.mem_nhds_iff.1 (inter_mem (hU.mem_nhds hx) hzero)
  obtain ⟨V, hVo, hxV, hVW, m, r₀, hr₀_an, hr₀_rel, hr₀_gen⟩ :=
    ih W hWo (fun y hy ↦ (hW_sub hy).1) hxW
  let r : Fin (m + 1) → Fin (k + 1) → E → ℂ :=
    Fin.snoc (fun j ↦ Fin.snoc (r₀ j) 0) (fun i _ ↦ if i = Fin.last k then 1 else 0)
  have hr_an (j : Fin (m + 1)) (i : Fin (k + 1)) : AnalyticOnNhd ℂ (r j i) V := by
    refine Fin.lastCases ?_ (fun j₀ ↦ Fin.lastCases ?_ (fun i₀ ↦ ?_) i) j
    · simp only [r, Fin.snoc_last]; exact analyticOnNhd_const
    · simp only [r, Fin.snoc_castSucc, Fin.snoc_last]; exact analyticOnNhd_const
    · simp only [r, Fin.snoc_castSucc]; exact hr₀_an j₀ i₀
  refine ⟨V, hVo, hxV, fun y hy ↦ (hW_sub (hVW hy)).1, m + 1, r, hr_an,
    fun j _ y hy ↦ ?_, fun y hy a ha hrel ↦ ?_⟩
  · have hf_last : f (Fin.last k) y = 0 := (hW_sub (hVW hy)).2
    refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j
    · simp [r, hf_last]
    · simp [r, Fin.sum_univ_castSucc, hr₀_rel j₀ () y hy]
  · have hrel₀ : (fun z ↦ ∑ i : Fin k, a i.castSucc z * f i.castSucc z) =ᶠ[𝓝 y] 0 := by
      refine (hrel ()).mp ?_
      filter_upwards [hVo.mem_nhds hy] with z hz h0
      have hf_last : f (Fin.last k) z = 0 := (hW_sub (hVW hz)).2
      simpa [Fin.sum_univ_castSucc, hf_last] using h0
    obtain ⟨b₀, hb₀_an, hb₀⟩ :=
      hr₀_gen y hy (fun i ↦ a i.castSucc) (fun i ↦ ha i.castSucc) fun _ ↦ hrel₀
    refine ⟨Fin.snoc b₀ (a (Fin.last k)),
      fun j ↦ Fin.lastCases (by rw [Fin.snoc_last]; exact ha (Fin.last k))
        (fun j₀ ↦ by rw [Fin.snoc_castSucc]; exact hb₀_an j₀) j,
      fun i ↦ ?_⟩
    refine Fin.lastCases ?_ (fun i₀ ↦ ?_) i
    · exact Eventually.of_forall fun z ↦ by simp [r, Fin.sum_univ_castSucc]
    · filter_upwards [hb₀ i₀] with z hz
      simp [r, Fin.sum_univ_castSucc, Fin.castSucc_ne_last, hz]

end BasicReductions

private theorem germ_coe_sum {α ι : Type*} (l : Filter α) (s : Finset ι) (f : ι → α → ℂ) :
    (∑ i ∈ s, (f i : Germ l ℂ)) = (fun z ↦ ∑ i ∈ s, f i z) :=
  (map_sum (Germ.coeAddHom (M := ℂ) l) f s).symm.trans (congrArg _ (funext fun _ ↦ by simp))

/-- Degree bound for the quotient polynomial `r_last` in the stalkwise Oka reduction when
`-∑ j, r₀ j * P_j = D * r_last` over a domain. -/
private theorem degree_lt_of_mul_eq_neg_sum {R : Type*} [CommRing R] [IsDomain R] {k d : ℕ}
    {D r_last : R[X]} (hD0 : D ≠ 0) {r₀ P : Fin k → R[X]}
    (hr₀ : ∀ j, (r₀ j).degree < D.natDegree) (hP0 : ∀ j, P j ≠ 0)
    (hP_deg : ∀ j, (P j).natDegree ≤ d) (hEq : -∑ j, r₀ j * P j = D * r_last) :
    r_last.degree < d := by
  rcases eq_or_ne r_last 0 with hr0 | hr0
  · rw [hr0, degree_zero]; exact WithBot.bot_lt_coe d
  · have hS0 : (-∑ j, r₀ j * P j) ≠ 0 := hEq ▸ mul_ne_zero hD0 hr0
    have hbot : (⊥ : WithBot ℕ) < ((D.natDegree + d : ℕ) : WithBot ℕ) :=
      WithBot.bot_lt_coe (D.natDegree + d)
    have hS_deg : (-∑ j, r₀ j * P j).degree < ((D.natDegree + d : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_neg]
      refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff hbot).2 fun j _ ↦ ?_)
      rcases eq_or_ne (r₀ j) 0 with hj0 | hj0
      · rw [hj0, zero_mul, degree_zero]; exact hbot
      · rw [degree_eq_natDegree (mul_ne_zero hj0 (hP0 j)), Nat.cast_lt, natDegree_mul hj0 (hP0 j)]
        exact Nat.add_lt_add_of_lt_of_le ((natDegree_lt_iff_degree_lt hj0).2 (hr₀ j)) (hP_deg j)
    have hnat := (natDegree_lt_iff_degree_lt hS0).2 hS_deg
    rw [hEq, natDegree_mul hD0 hr0] at hnat
    exact (natDegree_lt_iff_degree_lt hr0).1 (by omega)

/-! ### Stalkwise reduction of relations among monic polynomials -/

section StalkMonicReduction

open TauCeti.holomorphicStructureSheaf

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]

omit [FiniteDimensional ℂ B] in
/-- For a monic polynomial `P` over the holomorphic stalk at `y`, the vertical power series of
`evalVertical y η P` has nonzero residue mod the maximal ideal. -/
private theorem map_residue_verticalPowerSeries_evalVertical_ne_zero_of_monic {y : B} {η : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y)[X]} (hP : P.Monic) :
    (verticalPowerSeries y η (evalVertical y η P)).map
      (IsLocalRing.residue ((holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y)) ≠ 0 := by
  rw [verticalPowerSeries_evalVertical]
  intro h0
  have h1 := congrArg (PowerSeries.coeff P.natDegree) h0
  simp [hP.coeff_natDegree] at h1

/-- Stalkwise Weierstrass factorization of a monic polynomial `P` at `(y, η)`: `P = D * Q` in
`𝒪_{B, y}[X]` where `D` is distinguished at `y` and `evalVertical y η Q` is a unit germ. -/
private theorem exists_isDistinguishedAt_mul_isUnit_of_monic {y : B} {η : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y)[X]} (hP : P.Monic) :
    ∃ D Q : ((holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y)[X],
      D.IsDistinguishedAt
        (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y)) ∧
      P = D * Q ∧ Q ≠ 0 ∧ D.natDegree + Q.natDegree = P.natDegree ∧
      IsUnit (evalVertical y η Q) := by
  obtain ⟨⟨D, u⟩, ⟨hD, hu, hfac⟩, -⟩ := existsUnique_weierstrassPreparation
    (map_residue_verticalPowerSeries_evalVertical_ne_zero_of_monic (η := η) hP)
  obtain ⟨Q, hPQ⟩ := (evalVertical_dvd_iff_of_isDistinguishedAt hD).2 ⟨u, hfac⟩
  have hQ0 : Q ≠ 0 := right_ne_zero_of_mul (hPQ ▸ hP.ne_zero)
  have hEvD : evalVertical y η D ≠ 0 := fun h0 ↦
    hD.monic.ne_zero (evalVertical_injective y η (h0.trans (map_zero _).symm))
  have hEvQ : evalVertical y η Q = u := by
    apply mul_left_cancel₀ hEvD
    rw [← map_mul, ← hPQ, hfac]
  exact ⟨D, Q, hD, hPQ, hQ0, by rw [hPQ, natDegree_mul hD.monic.ne_zero hQ0], hEvQ ▸ hu⟩

/-- Algebraic identity for the stalkwise Oka reduction: if `P_last = D * Q` and `r_last` satisfies
`-∑ j, r₀ j * P_j = D * r_last`, then `Fin.snoc (Q * r₀ ·) r_last` is a polynomial relation of
`P`. -/
private theorem sum_snoc_mul_eq_zero_of_mul_eq_neg_sum {R : Type*} [CommRing R] {k : ℕ}
    {D Q r_last : R[X]} {r₀ : Fin k → R[X]} {P : Fin (k + 1) → R[X]}
    (hPQ : P (Fin.last k) = D * Q)
    (hDr_last : -∑ j : Fin k, r₀ j * P j.castSucc = D * r_last) :
    ∑ i : Fin (k + 1), Fin.snoc (α := fun _ ↦ R[X]) (fun j ↦ Q * r₀ j) r_last i * P i = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, hPQ]
  calc
    (∑ j, Q * r₀ j * P j.castSucc) + r_last * (D * Q) =
        (∑ j, Q * (r₀ j * P j.castSucc)) + Q * (D * r_last) := by
      congr 1; · exact Finset.sum_congr rfl fun _ _ ↦ mul_assoc _ _ _
      · ring
    _ = Q * ((∑ j, r₀ j * P j.castSucc) + (-∑ j, r₀ j * P j.castSucc)) := by
      rw [← hDr_last, mul_add, Finset.mul_sum]
    _ = 0 := by rw [add_neg_cancel, mul_zero]

/-- **Stalkwise Oka reduction for centered monic polynomials.** Given monic polynomials
`P : Fin (k + 1) → 𝒪_{B, y}[X]` of `natDegree ≤ d` and a germ relation `a` of
`evalVertical y η ∘ P` in `𝒪_{B × ℂ, (y, η)}`, multiplying `a` by a unit `u` decomposes `u * a`
into a combination of the `k` Koszul relations together with a polynomial relation `r` in
`𝒪_{B, y}[X]` of degree `< d`. -/
private theorem exists_stalk_koszul_add_poly_of_monic {k d : ℕ} {y : B} {η : ℂ}
    {P : Fin (k + 1) → ((holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y)[X]}
    (hP_monic : ∀ i, (P i).Monic) (hP_deg : ∀ i, (P i).natDegree ≤ d)
    {a : Fin (k + 1) → (holomorphicStructureSheaf 𝓘(ℂ, B × ℂ) (B × ℂ)).presheaf.stalk (y, η)}
    (ha : ∑ i, a i * evalVertical y η (P i) = 0) :
    ∃ (u : (holomorphicStructureSheaf 𝓘(ℂ, B × ℂ) (B × ℂ)).presheaf.stalk (y, η))
      (q : Fin k → (holomorphicStructureSheaf 𝓘(ℂ, B × ℂ) (B × ℂ)).presheaf.stalk (y, η))
      (r : Fin (k + 1) → ((holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y)[X]),
      IsUnit u ∧ (∀ i, (r i).degree < d) ∧ ∑ i, r i * P i = 0 ∧
      (∀ j : Fin k, u * a j.castSucc =
        q j * evalVertical y η (P (Fin.last k)) + evalVertical y η (r j.castSucc)) ∧
      u * a (Fin.last k) =
        -(∑ j : Fin k, q j * evalVertical y η (P j.castSucc)) +
          evalVertical y η (r (Fin.last k)) := by
  let ev := evalVertical y η
  obtain ⟨D, Q, hD, hPQ, hQ0, hdegDQ, hu⟩ :=
    exists_isDistinguishedAt_mul_isUnit_of_monic (η := η) (hP_monic (Fin.last k))
  choose qr hqr using fun j : Fin k ↦
    (existsUnique_weierstrassDivision_of_isDistinguishedAt hD (a j.castSucc)).exists
  let q : Fin k → _ := fun j ↦ (qr j).1
  let r₀ : Fin k → _ := fun j ↦ (qr j).2
  let S_poly := -∑ j : Fin k, r₀ j * P j.castSucc
  let r'_last := ev Q * a (Fin.last k) + ∑ j : Fin k, q j * ev (P j.castSucc)
  have hmul_init (j : Fin k) :
      ev Q * a j.castSucc = q j * ev (P (Fin.last k)) + ev (Q * r₀ j) := by
    dsimp only [ev, q, r₀]; rw [(hqr j).2, hPQ, map_mul, map_mul]; ring
  have hEvS : ev S_poly = ev D * r'_last := by
    apply hu.mul_left_cancel
    have hsum_a : ∑ j : Fin k, a j.castSucc * ev (P j.castSucc) =
        -(a (Fin.last k) * ev (P (Fin.last k))) := by
      rw [Fin.sum_univ_castSucc] at ha; linear_combination ha
    calc
      ev Q * ev S_poly = -∑ j : Fin k, (ev Q * a j.castSucc - q j * ev (P (Fin.last k))) *
            ev (P j.castSucc) := by
        simp only [S_poly, map_neg, map_sum, map_mul, mul_neg, Finset.mul_sum, ← mul_assoc]
        exact congrArg Neg.neg (Finset.sum_congr rfl fun j _ ↦ by
          rw [hmul_init j, add_sub_cancel_left, map_mul])
      _ = -ev Q * (∑ j : Fin k, a j.castSucc * ev (P j.castSucc)) +
            ev (P (Fin.last k)) * ∑ j : Fin k, q j * ev (P j.castSucc) := by
        rw [neg_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
          ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ = ev Q * (ev D * r'_last) := by
        dsimp only [ev, r'_last] at hsum_a ⊢; rw [hsum_a, hPQ, map_mul]; ring
  obtain ⟨r_last, hDr_last⟩ := (evalVertical_dvd_iff_of_isDistinguishedAt hD).2 ⟨r'_last, hEvS⟩
  have hEvD : ev D ≠ 0 := fun h0 ↦
    hD.monic.ne_zero (evalVertical_injective y η (h0.trans (map_zero _).symm))
  have hEv_last : ev r_last = r'_last :=
    mul_left_cancel₀ hEvD (by rw [← map_mul, ← hDr_last, hEvS])
  have hdeg_init (j : Fin k) : (Q * r₀ j).degree < d := by
    rcases eq_or_ne (r₀ j) 0 with hr0 | hr0
    · rw [hr0, mul_zero, degree_zero]; exact WithBot.bot_lt_coe d
    · rw [degree_eq_natDegree (mul_ne_zero hQ0 hr0), Nat.cast_lt, natDegree_mul hQ0 hr0]
      exact (Nat.add_lt_add_left ((natDegree_lt_iff_degree_lt hr0).2 (hqr j).1) _).trans_le
        ((Nat.add_comm _ _).trans_le (hdegDQ.trans_le (hP_deg (Fin.last k))))
  have hdeg_last : r_last.degree < d :=
    degree_lt_of_mul_eq_neg_sum hD.monic.ne_zero (fun j ↦ (hqr j).1)
      (fun j ↦ (hP_monic j.castSucc).ne_zero) (fun j ↦ hP_deg j.castSucc) hDr_last
  refine ⟨ev Q, q, Fin.snoc (fun j ↦ Q * r₀ j) r_last, hu,
    Fin.lastCases (by rw [Fin.snoc_last]; exact hdeg_last)
      (fun j ↦ by rw [Fin.snoc_castSucc]; exact hdeg_init j),
    sum_snoc_mul_eq_zero_of_mul_eq_neg_sum hPQ hDr_last,
    fun j ↦ by rw [Fin.snoc_castSucc]; exact hmul_init j, ?_⟩
  dsimp only [ev, r'_last] at hEv_last ⊢
  rw [Fin.snoc_last, hEv_last]; ring

/-- Shifting Lemma `exists_stalk_koszul_add_poly_of_monic` from centered variable `X = w - η` to
the uncentered vertical variable `w` using `Polynomial.taylor`. -/
private theorem exists_stalk_uncentered_koszul_add_poly_of_monic {k d : ℕ} {y : B} {η : ℂ}
    {P : Fin (k + 1) → ((holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y)[X]}
    (hP_monic : ∀ i, (P i).Monic) (hP_deg : ∀ i, (P i).natDegree ≤ d)
    {a : Fin (k + 1) → (holomorphicStructureSheaf 𝓘(ℂ, B × ℂ) (B × ℂ)).presheaf.stalk (y, η)}
    (ha : ∑ i, a i * evalVertical y η
      (taylor (germOfContMDiff (fun _ : B ↦ η) contMDiff_const y) (P i)) = 0) :
    ∃ (u : (holomorphicStructureSheaf 𝓘(ℂ, B × ℂ) (B × ℂ)).presheaf.stalk (y, η))
      (q : Fin k → (holomorphicStructureSheaf 𝓘(ℂ, B × ℂ) (B × ℂ)).presheaf.stalk (y, η))
      (r : Fin (k + 1) → ((holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y)[X]),
      IsUnit u ∧ (∀ i, (r i).degree < d) ∧ ∑ i, r i * P i = 0 ∧
      (∀ j : Fin k, u * a j.castSucc = q j * evalVertical y η
          (taylor (germOfContMDiff (fun _ : B ↦ η) contMDiff_const y) (P (Fin.last k))) +
        evalVertical y η
          (taylor (germOfContMDiff (fun _ : B ↦ η) contMDiff_const y) (r j.castSucc))) ∧
      u * a (Fin.last k) = -(∑ j : Fin k, q j * evalVertical y η
          (taylor (germOfContMDiff (fun _ : B ↦ η) contMDiff_const y) (P j.castSucc))) +
        evalVertical y η
          (taylor (germOfContMDiff (fun _ : B ↦ η) contMDiff_const y) (r (Fin.last k))) := by
  set η₀ : (holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y :=
    germOfContMDiff (fun _ : B ↦ η) contMDiff_const y
  obtain ⟨u, q, r', hu, hr'_deg, hr'_sum, hinit, hlast⟩ :=
    exists_stalk_koszul_add_poly_of_monic
      (fun i ↦ by rw [Polynomial.Monic, leadingCoeff_taylor]; exact hP_monic i)
      (fun i ↦ by rw [natDegree_taylor]; exact hP_deg i) ha
  let r : Fin (k + 1) → _ := fun i ↦ taylor (-η₀) (r' i)
  have htaylor_r (i : Fin (k + 1)) : taylor η₀ (r i) = r' i := by simp [r, taylor_taylor]
  refine ⟨u, q, r, hu, fun i ↦ by simpa only [r, degree_taylor] using hr'_deg i, ?_,
    fun j ↦ by simpa only [htaylor_r] using hinit j, by simpa only [htaylor_r] using hlast⟩
  apply taylor_injective η₀; rw [map_sum, map_zero]
  simpa only [taylor_mul, htaylor_r] using hr'_sum

omit [FiniteDimensional ℂ B] in
/-- Evaluating `taylor (germOfContMDiff (fun _ ↦ η) _ y) (∑ α : Fin m, monomial α (g α))` via
`evalVertical y η` represents `(x, w) ↦ ∑ α, G α x * w ^ α` near `(y, η)`. -/
private theorem toFilterGerm_evalVertical_taylor_sum_monomial {y : B} {η : ℂ} {m : ℕ}
    {g : Fin m → (holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y} {G : Fin m → B → ℂ}
    (hG : ∀ α, toFilterGerm 𝓘(ℂ, B) B y (𝓝 y) le_rfl (g α) = G α) :
    toFilterGerm 𝓘(ℂ, B × ℂ) (B × ℂ) (y, η) (𝓝 (y, η)) le_rfl
        (evalVertical y η (taylor (germOfContMDiff (fun _ : B ↦ η) contMDiff_const y)
          (∑ α : Fin m, Polynomial.monomial (α : ℕ) (g α)))) =
      (fun p : B × ℂ ↦ ∑ α : Fin m, G α p.1 * p.2 ^ (α : ℕ)) := by
  set η₀ : (holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y :=
    germOfContMDiff (fun _ : B ↦ η) contMDiff_const y
  have hX : toFilterGerm 𝓘(ℂ, B × ℂ) (B × ℂ) (y, η) (𝓝 (y, η)) le_rfl
      (evalVertical y η (Polynomial.X + Polynomial.C η₀)) = (fun p : B × ℂ ↦ p.2) := by
    rw [map_add, map_add, evalVertical_X, evalVertical_C, toFilterGerm_germOfContMDiff,
      toFilterGerm_stalkPrecomp, toFilterGerm_germOfContMDiff, Germ.coe_compTendsto, ← Germ.coe_add]
    exact congrArg _ (funext fun _ ↦ by simp)
  have hterm (α : Fin m) : toFilterGerm 𝓘(ℂ, B × ℂ) (B × ℂ) (y, η) (𝓝 (y, η)) le_rfl
      (evalVertical y η (taylor η₀ (Polynomial.monomial (α : ℕ) (g α)))) =
      (fun p : B × ℂ ↦ G α p.1 * p.2 ^ (α : ℕ)) := by
    rw [taylor_monomial, map_mul, map_pow, map_mul, map_pow, evalVertical_C,
      toFilterGerm_stalkPrecomp, hG α, Germ.coe_compTendsto, hX, ← Germ.coe_pow, ← Germ.coe_mul]
    rfl
  rw [map_sum, map_sum, map_sum]; simp_rw [hterm]; exact germ_coe_sum _ _ _

end StalkMonicReduction

/-! ### Local relation generation for monic vertical polynomials on `B × ℂ` -/

/-- Summing `monomial β` of the padded coefficients reconstructs `monicOfCoeff`. -/
private theorem sum_monomial_padded_eq_monicOfCoeff {R : Type*} [CommRing R] {m d : ℕ}
    (hm : m ≤ d) (s : Fin m → R) :
    (∑ β : Fin (d + 1), Polynomial.monomial (β : ℕ)
      (if hlt : (β : ℕ) < m then s ⟨β, hlt⟩ else if (β : ℕ) = m then 1 else 0)) =
      TauCeti.Polynomial.monicOfCoeff s := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  ext n
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply]
  have hhigh {n : ℕ} (hnm : m < n) : (TauCeti.Polynomial.monicOfCoeff s).coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [TauCeti.Polynomial.natDegree_monicOfCoeff s]; exact hnm)
  rcases lt_or_ge n (d + 1) with hnd | hnd
  · rw [Finset.sum_eq_single ⟨n, hnd⟩
      (fun β _ hβ ↦ by simp [show (β : ℕ) ≠ n from fun h ↦ hβ (Fin.ext h)])
      (fun h ↦ (h (Finset.mem_univ _)).elim)]
    dsimp only; rw [ite_eq_left rfl]
    rcases lt_trichotomy n m with hnm | rfl | hnm
    · simp [hnm, TauCeti.Polynomial.coeff_monicOfCoeff s ⟨n, hnm⟩]
    · simp
    · simp [show ¬n < m by omega, show n ≠ m by omega, hhigh hnm]
  · rw [Finset.sum_eq_zero fun β _ ↦ by simp [show (β : ℕ) ≠ n by omega]]
    exact (hhigh (by omega)).symm

private theorem eq_sum_fin_monomial_of_degree_lt {R : Type*} [Semiring R] {d : ℕ} (hd : 0 < d)
    {p : R[X]} (hp : p.degree < d) :
    p = ∑ α : Fin d, Polynomial.monomial (α : ℕ) (p.coeff α) := by
  have hnat : p.natDegree < d := by
    rcases eq_or_ne p 0 with rfl | hp0; · simpa using hd
    rwa [degree_eq_natDegree hp0, Nat.cast_lt] at hp
  exact (p.as_sum_range' d hnat).trans
    (Fin.sum_univ_eq_sum_range (fun α ↦ Polynomial.monomial α (p.coeff α)) d).symm

/-- Coefficient formula for `∑ i, r i * monicOfCoeff (s i)` when `(r i).degree < d` (`0 < d`). -/
private theorem coeff_sum_mul_monicOfCoeff {R : Type*} [CommRing R] {k d : ℕ} (hd : 0 < d)
    {deg : Fin (k + 1) → ℕ} (hdeg : ∀ i, deg i ≤ d) (s : ∀ i, Fin (deg i) → R)
    {r : Fin (k + 1) → R[X]} (hr : ∀ i, (r i).degree < d) (γ : Fin (2 * d)) :
    (∑ i : Fin (k + 1), r i * TauCeti.Polynomial.monicOfCoeff (s i)).coeff γ =
      ∑ p : Fin (k + 1) × Fin d, (r p.1).coeff p.2 * ∑ β : Fin (d + 1),
        if (p.2 : ℕ) + (β : ℕ) = (γ : ℕ) then
          (if hlt : (β : ℕ) < deg p.1 then s p.1 ⟨β, hlt⟩ else if (β : ℕ) = deg p.1 then 1 else 0)
        else 0 := by
  have hsum : ∑ i : Fin (k + 1), r i * TauCeti.Polynomial.monicOfCoeff (s i) =
      ∑ i : Fin (k + 1), (∑ α : Fin d, Polynomial.monomial (α : ℕ) ((r i).coeff α)) *
        ∑ β : Fin (d + 1), Polynomial.monomial (β : ℕ)
          (if hlt : (β : ℕ) < deg i then s i ⟨β, hlt⟩ else if (β : ℕ) = deg i then 1 else 0) :=
    Finset.sum_congr rfl fun i _ ↦ by
      rw [← eq_sum_fin_monomial_of_degree_lt hd (hr i),
        sum_monomial_padded_eq_monicOfCoeff (hdeg i) (s i)]
  rw [hsum, Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Finsupp.single_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun α _ ↦
    Finset.sum_congr rfl fun β _ ↦ ?_
  by_cases h : (α : ℕ) + (β : ℕ) = (γ : ℕ) <;> simp [h]

section MonicNeighborhood

open TauCeti.holomorphicStructureSheaf

variable {B : Type}

/-- Padded coefficient `(i, β) ↦ p_{i, β}(x)` (`β : Fin (d + 1)`) of `monicOfCoeff (c i · x)`. -/
private def paddedMonicCoeff {k d : ℕ} (deg : Fin (k + 1) → ℕ)
    (c : ∀ i, Fin (deg i) → B → ℂ) (i : Fin (k + 1)) (β : Fin (d + 1)) (x : B) : ℂ :=
  if hlt : (β : ℕ) < deg i then c i ⟨β, hlt⟩ x else if (β : ℕ) = deg i then 1 else 0

private theorem sum_paddedMonicCoeff_eq_eval_monicOfCoeff {k d : ℕ} {deg : Fin (k + 1) → ℕ}
    (hdeg : ∀ i, deg i ≤ d) (c : ∀ i, Fin (deg i) → B → ℂ) (i : Fin (k + 1)) (x : B) (w : ℂ) :
    ∑ β : Fin (d + 1), paddedMonicCoeff deg c i β x * w ^ (β : ℕ) =
      (TauCeti.Polynomial.monicOfCoeff (fun α ↦ c i α x)).eval w := by
  unfold paddedMonicCoeff
  have hd_mem : deg i < d + 1 := Nat.lt_succ_of_le (hdeg i)
  rw [Fin.sum_univ_eq_sum_range (fun n ↦
      (if h : n < deg i then c i ⟨n, h⟩ x else if n = deg i then 1 else 0) * w ^ n) (d + 1),
    ← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hd_mem), Finset.sum_range_succ,
    TauCeti.Polynomial.eval_monicOfCoeff, Finset.sum_fin_eq_sum_range]
  have htail : ∑ n ∈ Finset.Ico (deg i + 1) (d + 1),
      (if h : n < deg i then c i ⟨n, h⟩ x else if n = deg i then (1 : ℂ) else 0) * w ^ n = 0 :=
    Finset.sum_eq_zero fun n hn ↦ by
      have hn' := (Finset.mem_Ico.1 hn).1
      simp [show ¬n < deg i by omega, show n ≠ deg i by omega]
  have hlow : ∑ n ∈ Finset.range (deg i),
      (if h : n < deg i then c i ⟨n, h⟩ x else if n = deg i then (1 : ℂ) else 0) * w ^ n =
      ∑ n ∈ Finset.range (deg i), if h : n < deg i then c i ⟨n, h⟩ x * w ^ n else 0 :=
    Finset.sum_congr rfl fun n hn ↦ by simp [Finset.mem_range.1 hn]
  rw [htail, add_zero, hlow]; simp [add_comm]

/-- Convolution matrix `M γ (i, α) x` expressing the `w ^ γ` coefficient (`γ : Fin (2 * d)`) of
`∑ i, (∑ α : Fin d, h (i, α) x * w ^ α) * P_i(x, w)`. -/
private def polyRelMatrix {k d : ℕ} (deg : Fin (k + 1) → ℕ)
    (c : ∀ i, Fin (deg i) → B → ℂ) (γ : Fin (2 * d)) (p : Fin (k + 1) × Fin d) (x : B) : ℂ :=
  ∑ β : Fin (d + 1), if (p.2 : ℕ) + (β : ℕ) = (γ : ℕ) then paddedMonicCoeff deg c p.1 β x else 0

/-- Pointwise polynomial convolution identity for `polyRelMatrix`. -/
private theorem sum_poly_mul_eval_eq_sum_polyRelMatrix {k d : ℕ} {deg : Fin (k + 1) → ℕ}
    (hdeg : ∀ i, deg i ≤ d) (c : ∀ i, Fin (deg i) → B → ℂ)
    (h : (Fin (k + 1) × Fin d) → B → ℂ) (x : B) (w : ℂ) :
    ∑ i : Fin (k + 1), (∑ α : Fin d, h (i, α) x * w ^ (α : ℕ)) *
        (TauCeti.Polynomial.monicOfCoeff (fun α ↦ c i α x)).eval w =
      ∑ γ : Fin (2 * d), (∑ p : Fin (k + 1) × Fin d, h p x * polyRelMatrix deg c γ p x) *
        w ^ (γ : ℕ) := by
  simp_rw [← sum_paddedMonicCoeff_eq_eval_monicOfCoeff hdeg c, polyRelMatrix]
  have hpart (i : Fin (k + 1)) (α : Fin d) (β : Fin (d + 1)) :
      (h (i, α) x * w ^ (α : ℕ)) * (paddedMonicCoeff deg c i β x * w ^ (β : ℕ)) =
      ∑ γ : Fin (2 * d), h (i, α) x *
        (if (α : ℕ) + (β : ℕ) = (γ : ℕ) then paddedMonicCoeff deg c i β x else 0) *
        w ^ (γ : ℕ) := by
    rw [Finset.sum_eq_single ⟨(α : ℕ) + (β : ℕ), by omega⟩
      (fun γ _ hγ ↦ by rw [ite_eq_right (fun heq ↦ hγ (Fin.ext heq.symm)), mul_zero, zero_mul])
      (fun h ↦ (h (Finset.mem_univ _)).elim)]
    dsimp only; rw [ite_eq_left rfl, pow_add]; ring
  calc
    ∑ i : Fin (k + 1), (∑ α : Fin d, h (i, α) x * w ^ (α : ℕ)) *
          ∑ β : Fin (d + 1), paddedMonicCoeff deg c i β x * w ^ (β : ℕ) =
        ∑ i : Fin (k + 1), ∑ α : Fin d, ∑ β : Fin (d + 1), ∑ γ : Fin (2 * d), h (i, α) x *
          (if (α : ℕ) + (β : ℕ) = (γ : ℕ) then paddedMonicCoeff deg c i β x else 0) *
          w ^ (γ : ℕ) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun α _ ↦ ?_
      rw [Finset.mul_sum]; simp_rw [hpart]
    _ = ∑ γ : Fin (2 * d), ∑ i : Fin (k + 1), ∑ α : Fin d, ∑ β : Fin (d + 1), h (i, α) x *
          (if (α : ℕ) + (β : ℕ) = (γ : ℕ) then paddedMonicCoeff deg c i β x else 0) *
          w ^ (γ : ℕ) := by
      conv_lhs => arg 2; ext i; arg 2; ext α; rw [Finset.sum_comm]
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      exact Finset.sum_comm
    _ = ∑ γ : Fin (2 * d), (∑ p : Fin (k + 1) × Fin d, h p x * ∑ β : Fin (d + 1),
          if (p.2 : ℕ) + (β : ℕ) = (γ : ℕ) then paddedMonicCoeff deg c p.1 β x else 0) *
          w ^ (γ : ℕ) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]

variable [NormedAddCommGroup B] [NormedSpace ℂ B]

private theorem analyticOnNhd_paddedMonicCoeff {k d : ℕ} {deg : Fin (k + 1) → ℕ}
    {c : ∀ i, Fin (deg i) → B → ℂ} {W₀ : Set B}
    (hc : ∀ i α, AnalyticOnNhd ℂ (c i α) W₀) (i : Fin (k + 1)) (β : Fin (d + 1)) :
    AnalyticOnNhd ℂ (paddedMonicCoeff deg c i β) W₀ := by
  unfold paddedMonicCoeff; split_ifs with hlt <;> [exact hc i ⟨β, hlt⟩; exact analyticOnNhd_const;
    exact analyticOnNhd_const]

private theorem analyticOnNhd_polyRelMatrix {k d : ℕ} {deg : Fin (k + 1) → ℕ}
    {c : ∀ i, Fin (deg i) → B → ℂ} {W₀ : Set B}
    (hc : ∀ i α, AnalyticOnNhd ℂ (c i α) W₀) (γ : Fin (2 * d)) (p : Fin (k + 1) × Fin d) :
    AnalyticOnNhd ℂ (polyRelMatrix deg c γ p) W₀ := fun y hy ↦ by
  unfold polyRelMatrix; refine Finset.analyticAt_fun_sum _ fun β _ ↦ ?_
  split_ifs; exacts [analyticOnNhd_paddedMonicCoeff hc p.1 β y hy, analyticAt_const]

private theorem toFilterGerm_paddedStalk {k d : ℕ} {deg : Fin (k + 1) → ℕ}
    {c : ∀ i, Fin (deg i) → B → ℂ} {y : B}
    {c_stalk : ∀ i, Fin (deg i) → (holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y}
    (hc_stalk : ∀ i α, toFilterGerm 𝓘(ℂ, B) B y (𝓝 y) le_rfl (c_stalk i α) = c i α)
    (i : Fin (k + 1)) (β : Fin (d + 1)) :
    toFilterGerm 𝓘(ℂ, B) B y (𝓝 y) le_rfl
        (if hlt : (β : ℕ) < deg i then c_stalk i ⟨β, hlt⟩
         else if (β : ℕ) = deg i then 1 else 0) = paddedMonicCoeff deg c i β := by
  unfold paddedMonicCoeff; split_ifs with hlt heq
  · exact hc_stalk i ⟨β, hlt⟩
  · rw [map_one]; rfl
  · rw [map_zero]; rfl

private theorem toFilterGerm_evalVertical_taylor_monicOfCoeff {k d : ℕ} {deg : Fin (k + 1) → ℕ}
    (hdeg : ∀ i, deg i ≤ d) {c : ∀ i, Fin (deg i) → B → ℂ} {y : B} {η : ℂ}
    {c_stalk : ∀ i, Fin (deg i) → (holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y}
    (hc_stalk : ∀ i α, toFilterGerm 𝓘(ℂ, B) B y (𝓝 y) le_rfl (c_stalk i α) = c i α)
    (i : Fin (k + 1)) :
    toFilterGerm 𝓘(ℂ, B × ℂ) (B × ℂ) (y, η) (𝓝 (y, η)) le_rfl
        (evalVertical y η (taylor (germOfContMDiff (fun _ : B ↦ η) contMDiff_const y)
          (TauCeti.Polynomial.monicOfCoeff (c_stalk i)))) =
      (fun p : B × ℂ ↦ (TauCeti.Polynomial.monicOfCoeff (fun α ↦ c i α p.1)).eval p.2) := by
  rw [← sum_monomial_padded_eq_monicOfCoeff (hdeg i) (c_stalk i),
    toFilterGerm_evalVertical_taylor_sum_monomial (toFilterGerm_paddedStalk hc_stalk i)]
  exact congrArg _ (funext fun p ↦ sum_paddedMonicCoeff_eq_eval_monicOfCoeff hdeg c i p.1 p.2)

/-- Translates a stalk polynomial relation `∑ i, r_stalk i * monicOfCoeff (c_stalk i) = 0` of
degree `< d` at `y ∈ B` into the `2 * d` germ equations on `B` defined by `polyRelMatrix`. -/
private theorem eventuallyEq_zero_sum_polyRelMatrix {k d : ℕ} (hd : 0 < d)
    {deg : Fin (k + 1) → ℕ} (hdeg : ∀ i, deg i ≤ d) {c : ∀ i, Fin (deg i) → B → ℂ} {y : B}
    {c_stalk : ∀ i, Fin (deg i) → (holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y}
    (hc_stalk : ∀ i α, toFilterGerm 𝓘(ℂ, B) B y (𝓝 y) le_rfl (c_stalk i α) = c i α)
    {r_stalk : Fin (k + 1) → ((holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y)[X]}
    (hr_deg : ∀ i, (r_stalk i).degree < d)
    (hr_sum : ∑ i, r_stalk i * TauCeti.Polynomial.monicOfCoeff (c_stalk i) = 0)
    {G : (Fin (k + 1) × Fin d) → B → ℂ}
    (hG : ∀ p, toFilterGerm 𝓘(ℂ, B) B y (𝓝 y) le_rfl ((r_stalk p.1).coeff p.2) = G p)
    (γ : Fin (2 * d)) :
    (fun x ↦ ∑ p, G p x * polyRelMatrix deg c γ p x) =ᶠ[𝓝 y] 0 := by
  have hcoeff : (∑ i, r_stalk i * TauCeti.Polynomial.monicOfCoeff (c_stalk i)).coeff γ = 0 := by
    rw [hr_sum, coeff_zero]
  rw [coeff_sum_mul_monicOfCoeff hd hdeg c_stalk hr_deg γ] at hcoeff
  have hfg := congrArg (toFilterGerm 𝓘(ℂ, B) B y (𝓝 y) le_rfl) hcoeff
  rw [map_sum, map_zero] at hfg
  have hpad (p : Fin (k + 1) × Fin d) :
      toFilterGerm 𝓘(ℂ, B) B y (𝓝 y) le_rfl
        (∑ β : Fin (d + 1), if (p.2 : ℕ) + (β : ℕ) = (γ : ℕ) then
          (if hlt : (β : ℕ) < deg p.1 then c_stalk p.1 ⟨β, hlt⟩
           else if (β : ℕ) = deg p.1 then 1 else 0) else 0) = polyRelMatrix deg c γ p := by
    rw [map_sum]
    have hterm (β : Fin (d + 1)) : toFilterGerm 𝓘(ℂ, B) B y (𝓝 y) le_rfl
        (if (p.2 : ℕ) + (β : ℕ) = (γ : ℕ) then
          (if hlt : (β : ℕ) < deg p.1 then c_stalk p.1 ⟨β, hlt⟩
           else if (β : ℕ) = deg p.1 then 1 else 0) else 0) =
        (fun x ↦ if (p.2 : ℕ) + (β : ℕ) = (γ : ℕ) then paddedMonicCoeff deg c p.1 β x else 0) := by
      by_cases hsum_eq : (p.2 : ℕ) + (β : ℕ) = (γ : ℕ)
      · simp only [hsum_eq, ↓reduceIte]; exact toFilterGerm_paddedStalk hc_stalk p.1 β
      · simp only [hsum_eq, ↓reduceIte, map_zero]; rfl
    simp_rw [hterm, germ_coe_sum]; rfl
  simp_rw [map_mul, hG _, hpad, ← Germ.coe_mul] at hfg
  rwa [germ_coe_sum, ← Germ.coe_zero, Germ.coe_eq] at hfg

/-- Lifts `exists_stalk_uncentered_koszul_add_poly_of_monic` to analytic function representatives
`U_inv`, `Q_fun`, `G` near `(y, η)` and `y`. -/
private theorem exists_analytic_koszul_add_poly_of_monicOfCoeff [FiniteDimensional ℂ B]
    {k d : ℕ} (hd : 0 < d) {deg : Fin (k + 1) → ℕ} (hdeg : ∀ i, deg i ≤ d)
    {c : ∀ i, Fin (deg i) → B → ℂ} {y : B} {η : ℂ}
    (hc : ∀ i α, AnalyticAt ℂ (c i α) y)
    {a : Fin (k + 1) → B × ℂ → ℂ} (ha : ∀ i, AnalyticAt ℂ (a i) (y, η))
    (hrel : (fun z : B × ℂ ↦ ∑ i, a i z *
      (TauCeti.Polynomial.monicOfCoeff (fun α ↦ c i α z.1)).eval z.2) =ᶠ[𝓝 (y, η)] 0) :
    let P_fun (i : Fin (k + 1)) (p : B × ℂ) : ℂ :=
      (TauCeti.Polynomial.monicOfCoeff (fun α ↦ c i α p.1)).eval p.2
    ∃ (U_inv : B × ℂ → ℂ) (Q_fun : Fin k → B × ℂ → ℂ)
      (G : (Fin (k + 1) × Fin d) → B → ℂ),
      AnalyticAt ℂ U_inv (y, η) ∧ (∀ j, AnalyticAt ℂ (Q_fun j) (y, η)) ∧
      (∀ p, AnalyticAt ℂ (G p) y) ∧
      (∀ γ, (fun x ↦ ∑ p, G p x * polyRelMatrix deg c γ p x) =ᶠ[𝓝 y] 0) ∧
      (∀ j₀ : Fin k, a j₀.castSucc =ᶠ[𝓝 (y, η)] fun z ↦
        U_inv z * (Q_fun j₀ z * P_fun (Fin.last k) z +
          ∑ α : Fin d, G (j₀.castSucc, α) z.1 * z.2 ^ (α : ℕ))) ∧
      a (Fin.last k) =ᶠ[𝓝 (y, η)] fun z ↦
        U_inv z * (-(∑ j : Fin k, Q_fun j z * P_fun j.castSucc z) +
          ∑ α : Fin d, G (Fin.last k, α) z.1 * z.2 ^ (α : ℕ)) := by
  intro P_fun
  choose c_stalk hc_stalk using fun i α ↦ exists_toFilterGerm_eq_of_analyticAt (hc i α)
  choose a_stalk ha_stalk using fun i ↦ exists_toFilterGerm_eq_of_analyticAt (ha i)
  let P_stalk (i : Fin (k + 1)) := TauCeti.Polynomial.monicOfCoeff (c_stalk i)
  set η₀ : (holomorphicStructureSheaf 𝓘(ℂ, B) B).presheaf.stalk y :=
    germOfContMDiff (fun _ : B ↦ η) contMDiff_const y
  have hP_germ (i : Fin (k + 1)) :
      toFilterGerm 𝓘(ℂ, B × ℂ) (B × ℂ) (y, η) (𝓝 (y, η)) le_rfl
        (evalVertical y η (taylor η₀ (P_stalk i))) = P_fun i :=
    toFilterGerm_evalVertical_taylor_monicOfCoeff hdeg (fun i' α ↦ hc_stalk i' α _ le_rfl) i
  have ha_stalk_rel : ∑ i, a_stalk i * evalVertical y η (taylor η₀ (P_stalk i)) = 0 := by
    apply toFilterGerm_nhds_injective (y, η)
    rw [map_sum, map_zero]
    simp_rw [map_mul, ha_stalk _ _ le_rfl, hP_germ, ← Germ.coe_mul]
    rw [germ_coe_sum, ← Germ.coe_zero, Germ.coe_eq]; exact hrel
  obtain ⟨_, q_stalk, r_stalk, ⟨u_unit, rfl⟩, hr_deg, hr_sum, hinit, hlast⟩ :=
    exists_stalk_uncentered_koszul_add_poly_of_monic
      (fun i ↦ TauCeti.Polynomial.monic_monicOfCoeff _)
      (fun i ↦ by rw [TauCeti.Polynomial.natDegree_monicOfCoeff]; exact hdeg i) ha_stalk_rel
  let u_inv : (holomorphicStructureSheaf 𝓘(ℂ, B × ℂ) (B × ℂ)).presheaf.stalk (y, η) := ↑u_unit⁻¹
  obtain ⟨U_inv, hU_an, hU_germ⟩ := exists_analyticAt_toFilterGerm_eq (y, η) u_inv
  choose Q_fun hQ_spec using fun j ↦ exists_analyticAt_toFilterGerm_eq (y, η) (q_stalk j)
  choose G hG_spec using fun p : Fin (k + 1) × Fin d ↦
    exists_analyticAt_toFilterGerm_eq y ((r_stalk p.1).coeff p.2)
  have hr_germ (i : Fin (k + 1)) :
      toFilterGerm 𝓘(ℂ, B × ℂ) (B × ℂ) (y, η) (𝓝 (y, η)) le_rfl
        (evalVertical y η (taylor η₀ (r_stalk i))) =
      (fun p : B × ℂ ↦ ∑ α : Fin d, G (i, α) p.1 * p.2 ^ (α : ℕ)) := by
    conv_lhs => rw [eq_sum_fin_monomial_of_degree_lt hd (hr_deg i)]
    exact toFilterGerm_evalVertical_taylor_sum_monomial fun α ↦ (hG_spec (i, α)).2 _ le_rfl
  have ha_eq (i : Fin (k + 1)) : a_stalk i = u_inv * (↑u_unit * a_stalk i) := by
    dsimp only [u_inv]; rw [← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨U_inv, Q_fun, G, hU_an, fun j ↦ (hQ_spec j).1, fun p ↦ (hG_spec p).1,
    eventuallyEq_zero_sum_polyRelMatrix hd hdeg (fun i' α ↦ hc_stalk i' α _ le_rfl)
      hr_deg hr_sum (fun p ↦ (hG_spec p).2 _ le_rfl),
    fun j₀ ↦ ?_, ?_⟩
  · have hfg := congrArg (toFilterGerm 𝓘(ℂ, B × ℂ) (B × ℂ) (y, η) (𝓝 (y, η)) le_rfl)
      ((ha_eq j₀.castSucc).trans (congrArg (u_inv * ·) (hinit j₀)))
    rw [ha_stalk _ _ le_rfl, map_mul, hU_germ _ le_rfl, map_add, map_mul,
      (hQ_spec j₀).2 _ le_rfl, hP_germ, hr_germ j₀.castSucc, ← Germ.coe_mul, ← Germ.coe_add,
      ← Germ.coe_mul, Germ.coe_eq] at hfg
    exact hfg
  · have hsum_fg : toFilterGerm 𝓘(ℂ, B × ℂ) (B × ℂ) (y, η) (𝓝 (y, η)) le_rfl
        (∑ j : Fin k, q_stalk j * evalVertical y η (taylor η₀ (P_stalk j.castSucc))) =
        (fun z ↦ ∑ j : Fin k, Q_fun j z * P_fun j.castSucc z) := by
      rw [map_sum, ← germ_coe_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by
        rw [map_mul, (hQ_spec j).2 _ le_rfl, hP_germ, ← Germ.coe_mul]; rfl
    have hfg := congrArg (toFilterGerm 𝓘(ℂ, B × ℂ) (B × ℂ) (y, η) (𝓝 (y, η)) le_rfl)
      ((ha_eq (Fin.last k)).trans (congrArg (u_inv * ·) hlast))
    rw [ha_stalk _ _ le_rfl, map_mul, hU_germ _ le_rfl, map_add, map_neg, hsum_fg,
      hr_germ (Fin.last k), ← Germ.coe_neg, ← Germ.coe_add, ← Germ.coe_mul, Germ.coe_eq] at hfg
    exact hfg

private def monicKoszulGen {k : ℕ} {deg : Fin (k + 1) → ℕ} (c : ∀ i, Fin (deg i) → B → ℂ)
    (j : Fin k) : Fin (k + 1) → B × ℂ → ℂ :=
  Fin.snoc
    (fun j' p ↦ if j' = j then
      (TauCeti.Polynomial.monicOfCoeff (fun α ↦ c (Fin.last k) α p.1)).eval p.2 else 0)
    (fun p ↦ -(TauCeti.Polynomial.monicOfCoeff (fun α ↦ c j.castSucc α p.1)).eval p.2)

private def monicPolyGen {k d m₀ : ℕ} (s₀ : Fin m₀ → (Fin (k + 1) × Fin d) → B → ℂ)
    (q : Fin m₀) (i : Fin (k + 1)) (p : B × ℂ) : ℂ :=
  ∑ α : Fin d, s₀ q (i, α) p.1 * p.2 ^ (α : ℕ)

/-- Pointwise decomposition of an analytic relation `a` of
`(x, w) ↦ (monicOfCoeff (c i · x)).eval w` at `(y, η) ∈ V₀ ×ˢ W₁` into the `k` Koszul relations and
`m₀` base-generated polynomial relations. -/
private theorem exists_monicOfCoeff_relation_decomp [FiniteDimensional ℂ B]
    {k d m₀ : ℕ} (hd : 0 < d) {deg : Fin (k + 1) → ℕ} (hdeg : ∀ i, deg i ≤ d)
    {W₀ V₀ : Set B} (hV₀W₀ : V₀ ⊆ W₀) {c : ∀ i, Fin (deg i) → B → ℂ}
    (hc : ∀ i α, AnalyticOnNhd ℂ (c i α) W₀)
    {s₀ : Fin m₀ → (Fin (k + 1) × Fin d) → B → ℂ}
    (hs₀_gen : ∀ y ∈ V₀, ∀ G : (Fin (k + 1) × Fin d) → B → ℂ, (∀ p, AnalyticAt ℂ (G p) y) →
      (∀ γ, (fun x ↦ ∑ p, G p x * polyRelMatrix deg c γ p x) =ᶠ[𝓝 y] 0) →
      ∃ B₀ : Fin m₀ → B → ℂ, (∀ q, AnalyticAt ℂ (B₀ q) y) ∧
        ∀ p, G p =ᶠ[𝓝 y] fun x ↦ ∑ q, B₀ q x * s₀ q p x)
    {y : B} (hy : y ∈ V₀) {η : ℂ}
    {a : Fin (k + 1) → B × ℂ → ℂ} (ha : ∀ i, AnalyticAt ℂ (a i) (y, η))
    (hrel : (fun z : B × ℂ ↦ ∑ i, a i z *
      (TauCeti.Polynomial.monicOfCoeff (fun α ↦ c i α z.1)).eval z.2) =ᶠ[𝓝 (y, η)] 0) :
    ∃ b : Fin (k + m₀) → B × ℂ → ℂ, (∀ l, AnalyticAt ℂ (b l) (y, η)) ∧
      ∀ i, a i =ᶠ[𝓝 (y, η)] fun z ↦
        ∑ l, b l z * Fin.addCases (monicKoszulGen c) (monicPolyGen s₀) l i z := by
  obtain ⟨U_inv, Q_fun, G, hU_an, hQ_an, hG_an, hG_rel, hinit, hlast⟩ :=
    exists_analytic_koszul_add_poly_of_monicOfCoeff hd hdeg (fun i α ↦ hc i α y (hV₀W₀ hy)) ha hrel
  obtain ⟨B₀, hB₀_an, hB₀⟩ := hs₀_gen y hy G hG_an hG_rel
  have hB₀_pull : ∀ᶠ z : B × ℂ in 𝓝 (y, η), ∀ p, G p z.1 = ∑ q, B₀ q z.1 * s₀ q p z.1 :=
    (continuous_fst.tendsto (y, η)).eventually (eventually_all.2 hB₀)
  let b : Fin (k + m₀) → B × ℂ → ℂ :=
    Fin.addCases (fun j z ↦ U_inv z * Q_fun j z) (fun q z ↦ U_inv z * B₀ q z.1)
  have hb_an (l : Fin (k + m₀)) : AnalyticAt ℂ (b l) (y, η) :=
    Fin.addCases (motive := fun l ↦ AnalyticAt ℂ (b l) (y, η))
      (fun j ↦ by dsimp only [b]; rw [Fin.addCases_left]; exact hU_an.fun_mul (hQ_an j))
      (fun q ↦ by
        dsimp only [b]; rw [Fin.addCases_right]
        exact hU_an.fun_mul ((hB₀_an q).comp analyticAt_fst)) l
  refine ⟨b, hb_an, Fin.lastCases ?_ fun j₀ ↦ ?_⟩
  · filter_upwards [hlast, hB₀_pull] with z hz hGz
    rw [hz]
    simp only [b, monicKoszulGen, monicPolyGen, Fin.sum_univ_add, Fin.addCases_left,
      Fin.addCases_right, Fin.snoc_last, hGz, mul_add, mul_neg, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm (s := Finset.univ (α := Fin d))]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ ↦ by ring
    · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  · filter_upwards [hinit j₀, hB₀_pull] with z hz hGz
    rw [hz]
    have hkoszul : ∑ j : Fin k, U_inv z * Q_fun j z * monicKoszulGen c j j₀.castSucc z =
        U_inv z * (Q_fun j₀ z *
          (TauCeti.Polynomial.monicOfCoeff (fun α ↦ c (Fin.last k) α z.1)).eval z.2) := by
      simp only [monicKoszulGen, Fin.snoc_castSucc]
      rw [Finset.sum_eq_single j₀
        (fun j _ hj ↦ by simp [hj.symm]) (fun h ↦ (h (Finset.mem_univ _)).elim)]
      simp [mul_assoc]
    simp only [b, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, hkoszul, monicPolyGen,
      hGz, mul_add, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (s := Finset.univ (α := Fin d))]
    exact congrArg (_ + ·) (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring)

/-- Local relation generation on `W₀ ×ˢ W₁` at `(x₀, w₀)` for a family of monic vertical
polynomials `(x, w) ↦ (monicOfCoeff (c i · x)).eval w`, assuming local relation generation holds for
all finite systems on `B`. -/
private theorem hasLocalRelationGenerators_monicOfCoeff [FiniteDimensional ℂ B]
    (hB_sys : ∀ {κ ι : Type} [Finite κ] [Fintype ι] {U : Set B}, IsOpen U →
      ∀ {F : κ → ι → B → ℂ}, (∀ l i, AnalyticOnNhd ℂ (F l i) U) →
      ∀ {x : B}, x ∈ U → HasLocalRelationGenerators U F x)
    {W₀ : Set B} (hW₀ : IsOpen W₀) {x₀ : B} (hx₀ : x₀ ∈ W₀)
    {W₁ : Set ℂ} (hW₁ : IsOpen W₁) {w₀ : ℂ} (hw₀ : w₀ ∈ W₁)
    {k : ℕ} {deg : Fin (k + 1) → ℕ} {c : ∀ i, Fin (deg i) → B → ℂ}
    (hc : ∀ i α, AnalyticOnNhd ℂ (c i α) W₀) :
    HasLocalRelationGenerators (W₀ ×ˢ W₁)
      (fun _ : Unit ↦ fun i (p : B × ℂ) ↦
        (TauCeti.Polynomial.monicOfCoeff (fun α ↦ c i α p.1)).eval p.2) (x₀, w₀) := by
  let d : ℕ := (Finset.univ.sup deg) ⊔ 1
  have hd : 0 < d := by simp [d]
  have hdeg (i : Fin (k + 1)) : deg i ≤ d :=
    le_sup_of_le_left (Finset.le_sup (Finset.mem_univ i))
  obtain ⟨V₀, hV₀o, hx₀V₀, hV₀W₀, m₀, s₀, hs₀_an, hs₀_rel, hs₀_gen⟩ :=
    hB_sys hW₀ (fun γ p ↦ analyticOnNhd_polyRelMatrix (d := d) hc γ p) hx₀
  have hP_an (i : Fin (k + 1)) : AnalyticOnNhd ℂ
      (fun p : B × ℂ ↦ (TauCeti.Polynomial.monicOfCoeff (fun α ↦ c i α p.1)).eval p.2)
      (V₀ ×ˢ W₁) := fun p hp ↦ by
    simp_rw [TauCeti.Polynomial.eval_monicOfCoeff]
    exact (analyticAt_snd.pow _).fun_add <| Finset.analyticAt_fun_sum _ fun α _ ↦
      ((hc i α p.1 (hV₀W₀ hp.1)).comp analyticAt_fst).fun_mul (analyticAt_snd.pow _)
  have hgen_an (l : Fin (k + m₀)) (i : Fin (k + 1)) :
      AnalyticOnNhd ℂ (Fin.addCases (monicKoszulGen c) (monicPolyGen s₀) l i) (V₀ ×ˢ W₁) := by
    refine Fin.addCases (motive := fun l ↦
      AnalyticOnNhd ℂ (Fin.addCases (monicKoszulGen c) (monicPolyGen s₀) l i) (V₀ ×ˢ W₁))
      (fun j ↦ ?_) (fun q ↦ ?_) l
    · rw [Fin.addCases_left]
      refine Fin.lastCases
        (motive := fun i ↦ AnalyticOnNhd ℂ (monicKoszulGen c j i) (V₀ ×ˢ W₁)) ?_ (fun i₀ ↦ ?_) i
      · simp only [monicKoszulGen, Fin.snoc_last]; exact fun p hp ↦ (hP_an j.castSucc p hp).fun_neg
      · simp only [monicKoszulGen, Fin.snoc_castSucc]
        by_cases hij : i₀ = j <;> simp only [hij, ↓reduceIte]
        exacts [hP_an (Fin.last k), analyticOnNhd_const]
    · rw [Fin.addCases_right]
      exact fun p hp ↦ Finset.analyticAt_fun_sum _ fun α _ ↦
        ((hs₀_an q (i, α) p.1 hp.1).comp analyticAt_fst).fun_mul (analyticAt_snd.pow _)
  refine ⟨V₀ ×ˢ W₁, hV₀o.prod hW₁, ⟨hx₀V₀, hw₀⟩, prod_mono hV₀W₀ Subset.rfl, k + m₀,
    Fin.addCases (monicKoszulGen c) (monicPolyGen s₀), hgen_an, fun l _ p hp ↦ ?_,
    fun p hp a ha hrel ↦ exists_monicOfCoeff_relation_decomp hd hdeg hV₀W₀ hc hs₀_gen hp.1 ha
      (hrel ())⟩
  refine Fin.addCases (fun j ↦ ?_) (fun q ↦ ?_) l
  · simp only [Fin.addCases_left, Fin.sum_univ_castSucc, monicKoszulGen, Fin.snoc_castSucc,
      Fin.snoc_last]
    rw [Finset.sum_eq_single j
      (fun j' _ hj' ↦ by simp [hj']) (fun h ↦ (h (Finset.mem_univ _)).elim)]
    simp; ring
  · simp only [Fin.addCases_right, monicPolyGen]
    rw [sum_poly_mul_eval_eq_sum_polyRelMatrix hdeg c (s₀ q) p.1 p.2]
    exact Finset.sum_eq_zero fun γ _ ↦ by rw [hs₀_rel q γ p.1 hp.1, zero_mul]

end MonicNeighborhood

/-! ### Inductive step on `B × ℂ` and dimension induction -/

section DimensionInduction

open TauCeti.holomorphicStructureSheaf

/-- Because the holomorphic stalk on `B × ℂ` is an integral domain, a finite product of functions
analytic at `p₀` cannot vanish on a neighbourhood of `p₀` unless one of the factors does. -/
private theorem not_eventuallyEq_zero_prod_of_analyticAt
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
    {ι : Type*} [Fintype ι] {f : ι → B × ℂ → ℂ} {p₀ : B × ℂ}
    (hf_an : ∀ i, AnalyticAt ℂ (f i) p₀) (hf_ne : ∀ i, ¬f i =ᶠ[𝓝 p₀] 0) :
    ¬(fun z ↦ ∏ i, f i z) =ᶠ[𝓝 p₀] 0 := by
  choose s_germ hs_germ using fun i ↦ exists_toFilterGerm_eq_of_analyticAt (hf_an i)
  have hs_ne (i : ι) : s_germ i ≠ 0 := fun h0 ↦
    hf_ne i ((eq_zero_iff_of_toFilterGerm_eq (hs_germ i _ le_rfl)).1 h0)
  have hfg : toFilterGerm 𝓘(ℂ, B × ℂ) (B × ℂ) p₀ (𝓝 p₀) le_rfl (∏ i, s_germ i) =
      (fun z ↦ ∏ i, f i z) := by
    rw [map_prod]
    simp_rw [hs_germ _ _ le_rfl]
    exact (map_prod (Germ.coeMulHom (M := ℂ) (𝓝 p₀)) _ Finset.univ).symm.trans
      (congrArg _ (funext fun _ ↦ by simp))
  exact (eq_zero_iff_of_toFilterGerm_eq hfg).not.1
    (Finset.prod_ne_zero_iff.2 fun i _ ↦ hs_ne i)

/-- Local Weierstrass preparation step at `(0, 0) ∈ U'` when every vertical slice `t ↦ g i (0, t)`
has finite analytic order at `0`. -/
private theorem hasLocalRelationGenerators_prod_of_analyticOrderAt_ne_top
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
    (hB_sys : ∀ {κ ι : Type} [Finite κ] [Fintype ι] {U : Set B}, IsOpen U →
      ∀ {F : κ → ι → B → ℂ}, (∀ l i, AnalyticOnNhd ℂ (F l i) U) →
      ∀ {x : B}, x ∈ U → HasLocalRelationGenerators U F x)
    {k : ℕ} {U' : Set (B × ℂ)} (hU' : IsOpen U') (h0_mem : ((0, 0) : B × ℂ) ∈ U')
    {g : Fin (k + 1) → B × ℂ → ℂ} (hg_an : ∀ i, AnalyticOnNhd ℂ (g i) U')
    (hg_ord : ∀ i, analyticOrderAt (fun t ↦ g i (0, t)) 0 ≠ ⊤) :
    HasLocalRelationGenerators U' (fun _ : Unit ↦ g) (0, 0) := by
  choose deg hdeg using fun i ↦ ENat.ne_top_iff_exists.1 (hg_ord i)
  choose c u hc_an _ hu_an hu0 hgu using fun i ↦
    (hg_an i (0, 0) h0_mem).exists_weierstrassPreparation (hdeg i).symm
  let P_fun (i : Fin (k + 1)) (p : B × ℂ) : ℂ :=
    (TauCeti.Polynomial.monicOfCoeff (fun α ↦ c i α p.1)).eval p.2
  have hgu' (i : Fin (k + 1)) : g i =ᶠ[𝓝 (0, 0)] fun p ↦ P_fun i p * u i p := by
    simpa only [sub_zero] using hgu i
  have hev_prod : ∀ᶠ p : B × ℂ in 𝓝 (0, 0), p ∈ U' ∧
      ∀ i, AnalyticAt ℂ (u i) p ∧ u i p ≠ 0 ∧ g i p = P_fun i p * u i p :=
    (eventually_mem_set.2 (hU'.mem_nhds h0_mem)).and <| eventually_all.2 fun i ↦
      (hu_an i).eventually_analyticAt.and <|
        ((hu_an i).continuousAt.eventually_ne (hu0 i)).and (hgu' i)
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at hev_prod
  obtain ⟨pB, hpB, pC, hpC, hpBC⟩ := hev_prod
  have hev_c : ∀ᶠ x : B in 𝓝 0, ∀ i α, AnalyticAt ℂ (c i α) x :=
    eventually_all.2 fun i ↦ eventually_all.2 fun α ↦ (hc_an i α).eventually_analyticAt
  obtain ⟨W₀, hW₀_sub, hW₀o, h0W₀⟩ := _root_.mem_nhds_iff.1 (hpB.and hev_c)
  obtain ⟨W₁, hW₁_sub, hW₁o, h0W₁⟩ := _root_.mem_nhds_iff.1 hpC
  have hprod_prop {p : B × ℂ} (hp : p ∈ W₀ ×ˢ W₁) := hpBC (hW₀_sub hp.1).1 (hW₁_sub hp.2)
  have hmonic := hasLocalRelationGenerators_monicOfCoeff hB_sys hW₀o h0W₀ hW₁o h0W₁
    (c := c) fun i α x hx ↦ (hW₀_sub hx).2 i α
  have hmul := hmonic.mul_nonvanishing (u := u)
    (fun i p hp ↦ (hprod_prop hp).2 i |>.1) (fun i p hp ↦ (hprod_prop hp).2 i |>.2.1)
  exact (hmul.congr_eqOn fun _ i p hp ↦ ((hprod_prop hp).2 i |>.2.2).symm).mono
    fun p hp ↦ (hprod_prop hp).1

/-- Inductive step from `B` to `B × ℂ` for a single analytic equation in `k` unknowns, proved by
inner induction on `k` via general position and Weierstrass preparation. -/
private theorem hasLocalRelationGenerators_prod_step
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
    (hB_sys : ∀ {κ ι : Type} [Finite κ] [Fintype ι] {U : Set B}, IsOpen U →
      ∀ {F : κ → ι → B → ℂ}, (∀ l i, AnalyticOnNhd ℂ (F l i) U) →
      ∀ {x : B}, x ∈ U → HasLocalRelationGenerators U F x) :
    ∀ (k : ℕ) {U : Set (B × ℂ)}, IsOpen U → ∀ {p₀ : B × ℂ}, p₀ ∈ U →
      ∀ {f : Fin k → B × ℂ → ℂ}, (∀ i, AnalyticOnNhd ℂ (f i) U) →
      HasLocalRelationGenerators U (fun _ : Unit ↦ f) p₀
  | 0, U, hU, p₀, hp₀, _, _ =>
    ⟨U, hU, hp₀, Subset.rfl, 0, Fin.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0,
      fun _ _ _ _ _ ↦ ⟨Fin.elim0, fun j ↦ j.elim0, fun i ↦ i.elim0⟩⟩
  | k + 1, U, hU, p₀, hp₀, f, hf => by
    by_cases hex : ∃ i₀ : Fin (k + 1), f i₀ =ᶠ[𝓝 p₀] 0
    · obtain ⟨i₀, hi₀⟩ := hex
      let e := Equiv.swap i₀ (Fin.last k)
      refine HasLocalRelationGenerators.reindex_cols e <|
        hasLocalRelationGenerators_of_last_eventuallyEq_zero hU hp₀
          (by simpa only [e, Equiv.swap_apply_right] using hi₀) fun U' hU'o hU'U hp₀' ↦
          hasLocalRelationGenerators_prod_step hB_sys k hU'o hp₀'
            fun i ↦ (hf (e i.castSucc)).mono hU'U
    · have hprod_ne := not_eventuallyEq_zero_prod_of_analyticAt
        (fun i ↦ hf i p₀ hp₀) fun i h ↦ hex ⟨i, h⟩
      obtain ⟨L, q, hLq, hord⟩ :=
        (Finset.univ.analyticAt_fun_prod fun i _ ↦ hf i p₀ hp₀)
          |>.exists_continuousLinearEquiv_analyticOrderAt_ne_top hprod_ne
      let φ : B × ℂ → B × ℂ := fun z ↦ L (q + z)
      let ψ : B × ℂ → B × ℂ := fun w ↦ L.symm w - q
      have hφ_an (z : B × ℂ) : AnalyticAt ℂ φ z :=
        (L.analyticAt _).comp (analyticAt_const.fun_add analyticAt_id)
      have hψ_an (w : B × ℂ) : AnalyticAt ℂ ψ w :=
        (L.symm.analyticAt w).fun_sub analyticAt_const
      have hφ0 : φ (0, 0) = p₀ := by dsimp only [φ]; rw [Prod.mk_zero_zero, add_zero, hLq]
      rw [← hφ0]
      refine HasLocalRelationGenerators.of_analytic_equiv hφ_an hψ_an
        (fun z ↦ by simp [φ, ψ]) (fun w ↦ by simp [φ, ψ]) ?_
      let g (i : Fin (k + 1)) (z : B × ℂ) : ℂ := f i (φ z)
      refine hasLocalRelationGenerators_prod_of_analyticOrderAt_ne_top hB_sys
        (hU.preimage (continuous_iff_continuousAt.2 fun z ↦ (hφ_an z).continuousAt))
        (by simpa only [mem_preimage, hφ0] using hp₀)
        (fun i z hz ↦ (hf i (φ z) hz).comp (hφ_an z)) fun i ↦ ?_
      rw [Ne, analyticOrderAt_eq_top]
      intro hgi0
      have htr : Tendsto (fun t : ℂ ↦ t - q.2) (𝓝 q.2) (𝓝 0) :=
        (continuous_id.fun_sub continuous_const).tendsto' q.2 0 (sub_self q.2)
      have hprod_zero : (fun t ↦ ∏ j, f j (L (q.1, t))) =ᶠ[𝓝 q.2] 0 := by
        filter_upwards [htr.eventually hgi0] with t ht
        have hqt : q + (0, t - q.2) = (q.1, t) := Prod.ext (add_zero q.1) (add_sub_cancel q.2 t)
        have hfi : f i (L (q.1, t)) = 0 := by simpa only [g, φ, hqt] using ht
        exact Finset.prod_eq_zero (Finset.mem_univ i) hfi
      exact hord (analyticOrderAt_eq_top.2 hprod_zero)

/-- Dimension induction on `Fin n → ℂ` for single-equation relation generation. -/
private theorem hasLocalRelationGenerators_fin_pi :
    ∀ (n k : ℕ) {U : Set (Fin n → ℂ)}, IsOpen U → ∀ {x : Fin n → ℂ}, x ∈ U →
      ∀ {f : Fin k → (Fin n → ℂ) → ℂ}, (∀ i, AnalyticOnNhd ℂ (f i) U) →
      HasLocalRelationGenerators U (fun _ : Unit ↦ f) x
  | 0, _, _, hU, _, hx, _, _ => hasLocalRelationGenerators_of_finrank_eq_zero (by simp) hU hx
  | n + 1, k, U, hU, x, hx, f, hf => by
    let e : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin n → ℂ) × ℂ :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    have h_prod := hasLocalRelationGenerators_prod_step
      (hasLocalRelationGenerators_system_of_single
        fun m₀ _ hU₀ _ hx₀ _ hg ↦ hasLocalRelationGenerators_fin_pi n m₀ hU₀ hx₀ hg)
      k (hU.preimage e.symm.continuous) (p₀ := e x) (by simpa using hx)
      (f := fun i z ↦ f i (e.symm z))
      (fun i z hz ↦ (hf i (e.symm z) hz).comp (e.symm.analyticAt z))
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      h_prod.of_analytic_equiv (fun z ↦ e.symm.analyticAt z) (fun w ↦ e.analyticAt w)
        e.apply_symm_apply e.symm_apply_apply

end DimensionInduction

end Aux

/-! ### Oka's coherence theorem on complex normed spaces -/

/-- **Oka's coherence theorem for finite analytic systems.** Let `U` be an open subset of a
finite-dimensional complex normed space `E`, `x ∈ U`, and `F : κ → ι → E → ℂ` a finite matrix of
functions analytic on `U`. Then there exist an open neighbourhood `V ⊆ U` of `x` and finitely many
analytic relation tuples `r : Fin m → ι → E → ℂ` on `V` whose germs at every `y ∈ V` generate all
simultaneous analytic germ relations of `F` at `y`. -/
theorem exists_analyticOnNhd_systemRelationGenerators
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {κ ι : Type*} [Finite κ] [Fintype ι] {U : Set E} (hU : IsOpen U)
    {F : κ → ι → E → ℂ} (hF : ∀ l i, AnalyticOnNhd ℂ (F l i) U) {x : E} (hx : x ∈ U) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ (m : ℕ) (r : Fin m → ι → E → ℂ),
      (∀ j i, AnalyticOnNhd ℂ (r j i) V) ∧
      (∀ j l, ∀ y ∈ V, ∑ i, r j i y * F l i y = 0) ∧
      ∀ y ∈ V, ∀ a : ι → E → ℂ, (∀ i, AnalyticAt ℂ (a i) y) →
        (∀ l, (fun z ↦ ∑ i, a i z * F l i z) =ᶠ[𝓝 y] 0) →
        ∃ b : Fin m → E → ℂ, (∀ j, AnalyticAt ℂ (b j) y) ∧
          ∀ i, a i =ᶠ[𝓝 y] fun z ↦ ∑ j, b j z * r j i z := by
  let e : E ≃L[ℂ] Fin (Module.finrank ℂ E) → ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine hasLocalRelationGenerators_system_of_single (fun m₀ U' hU' x' hx' g hg ↦ ?_) hU hF hx
  have h₀ := hasLocalRelationGenerators_fin_pi (Module.finrank ℂ E) m₀
    (hU'.preimage e.symm.continuous) (x := e x') (by simpa using hx')
    (f := fun j z ↦ g j (e.symm z))
    (fun j z hz ↦ (hg j (e.symm z) hz).comp (e.symm.analyticAt z))
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using
    h₀.of_analytic_equiv (fun z ↦ e.symm.analyticAt z) (fun w ↦ e.analyticAt w)
      e.apply_symm_apply e.symm_apply_apply

/-- **Oka's coherence theorem (primitive local form).** Let `U` be an open subset of a
finite-dimensional complex normed space `E`, `x ∈ U`, and `f : ι → E → ℂ` a finite family of
functions analytic on `U`. Then there exist an open neighbourhood `V ⊆ U` of `x` and finitely many
analytic relation tuples `r : Fin m → ι → E → ℂ` on `V` such that `∑ i, r j i y * f i y = 0` for
all `y ∈ V` and, at every `y ∈ V`, every germ relation `∑ i, a i * f i =ᶠ[𝓝 y] 0` with `a i`
analytic at `y` is an analytic linear combination of the `r j` near `y`. -/
theorem exists_analyticOnNhd_relationGenerators
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] {U : Set E} (hU : IsOpen U)
    {f : ι → E → ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) U) {x : E} (hx : x ∈ U) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ (m : ℕ) (r : Fin m → ι → E → ℂ),
      (∀ j i, AnalyticOnNhd ℂ (r j i) V) ∧
      (∀ j, ∀ y ∈ V, ∑ i, r j i y * f i y = 0) ∧
      ∀ y ∈ V, ∀ a : ι → E → ℂ, (∀ i, AnalyticAt ℂ (a i) y) →
        (fun z ↦ ∑ i, a i z * f i z) =ᶠ[𝓝 y] 0 →
        ∃ b : Fin m → E → ℂ, (∀ j, AnalyticAt ℂ (b j) y) ∧
          ∀ i, a i =ᶠ[𝓝 y] fun z ↦ ∑ j, b j z * r j i z := by
  obtain ⟨V, hVo, hxV, hVU, m, r, hr_an, hr_rel, hr_gen⟩ :=
    exists_analyticOnNhd_systemRelationGenerators hU (F := fun _ : Unit ↦ f) (fun _ ↦ hf) hx
  exact ⟨V, hVo, hxV, hVU, m, r, hr_an, fun j ↦ hr_rel j (),
    fun y hy a ha hrel ↦ hr_gen y hy a ha fun _ ↦ hrel⟩

/-! ### Oka's coherence theorem on complex manifolds -/

namespace holomorphicStructureSheaf

section RingHelpers

private theorem ker_mulVecLin_map_unit_eq_ker_linearCombination {A R ι : Type*} [CommRing R]
    [Fintype ι] (f : ι → A) (φ : A → R) :
    LinearMap.ker (Matrix.mulVecLin ((Matrix.of fun _ : Unit ↦ f).map φ)) =
      LinearMap.ker (Fintype.linearCombination R (fun i ↦ φ (f i))) := by
  ext a
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Fintype.linearCombination_apply,
    smul_eq_mul, funext_iff, Unique.forall_iff, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Matrix.of_apply, Pi.zero_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ mul_comm (φ (f i)) (a i)]

private theorem span_range_map_ringEquiv_eq_ker_mulVecLin {R S κ ι : Type*} [CommRing R]
    [CommRing S] [Fintype ι] (e : R ≃+* S) {m : ℕ} (v : Fin m → ι → R) (M : Matrix κ ι R)
    (h : Submodule.span R (Set.range v) = LinearMap.ker M.mulVecLin) :
    Submodule.span S (Set.range fun j i ↦ e (v j i)) =
      LinearMap.ker (M.map e).mulVecLin := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun a ha ↦ ?_
  · rintro _ ⟨j, rfl⟩
    have hj : v j ∈ LinearMap.ker M.mulVecLin := h ▸ Submodule.subset_span ⟨j, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hj
    rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    ext l
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, ← map_mul, ← map_sum,
      Pi.zero_apply, map_eq_zero_iff e e.injective] using congrFun hj l
  · have ha₀ : (fun i ↦ e.symm (a i)) ∈ LinearMap.ker M.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at ha ⊢
      ext l
      apply e.injective
      simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, RingEquiv.apply_symm_apply,
        Matrix.map_apply, Pi.zero_apply, map_zero] using congrFun ha l
    rw [← h, ← Fintype.range_linearCombination, LinearMap.mem_range] at ha₀
    obtain ⟨c, hc⟩ := ha₀
    rw [← Fintype.range_linearCombination, LinearMap.mem_range]
    refine ⟨fun j ↦ e (c j), funext fun i ↦ ?_⟩
    have hci := congrArg e (congrFun hc i)
    simpa only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      map_sum, map_mul, RingEquiv.apply_symm_apply] using hci

end RingHelpers

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]

omit [FiniteDimensional ℂ E] [I.Boundaryless] in
private theorem sum_apply {ι : Type*} {U : (Opens (TopCat.of X))ᵒᵖ} (s : Finset ι)
    (f : ι → (holomorphicStructureSheaf I X).obj.obj U) (x : ↥(unop U)) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_apply]
  | @insert a s ha ih => simp only [Finset.sum_insert ha, add_apply, ih]

omit [FiniteDimensional ℂ E] in
/-- Pulls back a coordinate-space relation decomposition at `e.extend I y` to stalk membership on
`X` at `y ∈ V`. -/
private theorem mem_span_germ_of_mem_ker_mulVecLin
    {κ ι : Type*} [Fintype ι] {e : OpenPartialHomeomorph X H} (he : e ∈ maximalAtlas I ω X)
    {U V : Opens X} (hVU : V ≤ U) (hVe : (V : Set X) ⊆ e.source) {W : Set E}
    (hVW : ∀ z ∈ V, e.extend I z ∈ W)
    {F : Matrix κ ι ((holomorphicStructureSheaf I X).obj.obj (op U))}
    {m : ℕ} {r_E : Fin m → ι → E → ℂ}
    {r : Fin m → ι → (holomorphicStructureSheaf I X).obj.obj (op V)}
    (hr_val : ∀ j i (z : V), toFun I X (op V) (r j i) z = r_E j i (e.extend I z))
    (hr_E_gen : ∀ w ∈ W, ∀ a : ι → E → ℂ, (∀ i, AnalyticAt ℂ (a i) w) →
      (∀ l, (fun w' ↦ ∑ i, a i w' *
        (Subtype.val.extend (toFun I X (op U) (F l i)) 0 ∘ (e.extend I).symm) w') =ᶠ[𝓝 w] 0) →
      ∃ b : Fin m → E → ℂ, (∀ j, AnalyticAt ℂ (b j) w) ∧
        ∀ i, a i =ᶠ[𝓝 w] fun w' ↦ ∑ j, b j w' * r_E j i w')
    {y : X} (hy : y ∈ V)
    {a_stalk : ι → (holomorphicStructureSheaf I X).presheaf.stalk y}
    (ha_stalk : a_stalk ∈ LinearMap.ker
      (Matrix.mulVecLin (F.map ((holomorphicStructureSheaf I X).presheaf.germ U y (hVU hy))))) :
    a_stalk ∈ Submodule.span ((holomorphicStructureSheaf I X).presheaf.stalk y)
      (Set.range fun j i ↦ (holomorphicStructureSheaf I X).presheaf.germ V y hy (r j i)) := by
  choose A hA_cmd hA_germ using fun i ↦ exists_toFilterGerm_eq y (a_stalk i)
  let F_ext (l : κ) (i : ι) : X → ℂ := Subtype.val.extend (toFun I X (op U) (F l i)) 0
  have hy_e : y ∈ e.source := hVe hy
  have hy_c : y ∈ (e.extend I).source := by rwa [e.extend_source]
  have hA_an (i : ι) : AnalyticAt ℂ (A i ∘ (e.extend I).symm) (e.extend I y) :=
    (TauCeti.contMDiffAt_omega_iff_analyticAt_of_mem_maximalAtlas he hy_e).1
      (hA_cmd i).self_of_nhds
  have hsymm_tendsto : Tendsto (e.extend I).symm (𝓝 (e.extend I y)) (𝓝 y) := by
    simpa only [(e.extend I).left_inv hy_c] using
      (e.continuousAt_extend_symm (I := I) hy_e).tendsto
  have hrel_E (l : κ) :
      (fun w ↦ ∑ i, (A i ∘ (e.extend I).symm) w * (F_ext l i ∘ (e.extend I).symm) w) =ᶠ[
        𝓝 (e.extend I y)] 0 := by
    have hl0 : ∑ i, (holomorphicStructureSheaf I X).presheaf.germ U y (hVU hy) (F l i) *
        a_stalk i = 0 := by
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
        Pi.zero_apply] using congrFun (LinearMap.mem_ker.1 ha_stalk) l
    have hfg := congrArg (toFilterGerm I X y (𝓝 y) le_rfl) hl0
    have hF_germ (i : ι) : toFilterGerm I X y (𝓝 y) le_rfl
        ((holomorphicStructureSheaf I X).presheaf.germ U y (hVU hy) (F l i)) = F_ext l i :=
      toFilterGerm_germ le_rfl (hVU hy) (F l i) (F_ext l i) fun z ↦
        (Subtype.val_injective.extend_apply _ (0 : X → ℂ) z).symm
    rw [map_sum, map_zero] at hfg
    simp_rw [map_mul, hF_germ, hA_germ _ _ le_rfl, mul_comm, ← Germ.coe_mul] at hfg
    rw [germ_coe_sum, ← Germ.coe_zero, Germ.coe_eq] at hfg
    exact hsymm_tendsto.eventually hfg
  obtain ⟨b_E, hb_E_an, hb_E_eq⟩ := hr_E_gen (e.extend I y) (hVW y hy)
    (fun i ↦ A i ∘ (e.extend I).symm) hA_an hrel_E
  have hc_tendsto : Tendsto (e.extend I) (𝓝 y) (𝓝 (e.extend I y)) :=
    (e.continuousAt_extend (I := I) hy_e).tendsto
  have hb_cmd (j : Fin m) : ∀ᶠ z in 𝓝 y, ContMDiffAt I 𝓘(ℂ) ω (b_E j ∘ e.extend I) z := by
    filter_upwards [e.open_source.mem_nhds hy_e,
      hc_tendsto.eventually (hb_E_an j).eventually_analyticAt] with z hz_e hz_an
    exact (TauCeti.contMDiffAt_modelSpace_omega_iff_analyticAt.2 hz_an).comp z
      (e.contMDiffAt_extend he hz_e)
  choose b_stalk hb_stalk using fun j ↦
    exists_toFilterGerm_eq_of_eventually_contMDiffAt (hb_cmd j)
  rw [← Fintype.range_linearCombination, LinearMap.mem_range]
  refine ⟨b_stalk, funext fun i ↦ ?_⟩
  apply toFilterGerm_nhds_injective y
  simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_sum, map_mul, hb_stalk _ _ le_rfl, hA_germ i _ le_rfl]
  have hr_germ (j : Fin m) : toFilterGerm I X y (𝓝 y) le_rfl
      ((holomorphicStructureSheaf I X).presheaf.germ V y hy (r j i)) = r_E j i ∘ e.extend I :=
    toFilterGerm_germ le_rfl hy (r j i) _ (hr_val j i)
  simp_rw [hr_germ, ← Germ.coe_mul]
  rw [germ_coe_sum, eq_comm, Germ.coe_eq]
  filter_upwards [e.open_source.mem_nhds hy_e, hc_tendsto.eventually (hb_E_eq i)] with z hz_e hz
  have hz_c : z ∈ (e.extend I).source := by rwa [e.extend_source]
  simpa only [Pi.mul_apply, Function.comp_apply, (e.extend I).left_inv hz_c] using hz

variable [IsManifold I 1 X]

/-- **Oka's coherence theorem for systems on complex manifolds.** Let `F` be a `κ × ι` matrix of
holomorphic sections on an open subset `U` of a boundaryless finite-dimensional complex manifold
`X`, and let `x ∈ U`. Then there exist an open neighbourhood `V ≤ U` of `x` and finitely many
holomorphic section tuples `r : Fin m → ι → 𝒪_X(V)` that satisfy `(F|_V) *ᵥ r j = 0` on `V` and
whose germs at every `y ∈ V` span the stalk kernel of `F`. No Hausdorffness or second-countability
assumption on `X` is needed. -/
theorem exists_span_germ_eq_ker_mulVecLin {κ ι : Type*} [Finite κ] [Fintype ι]
    {U : Opens X} {x : X} (hx : x ∈ U)
    (F : Matrix κ ι ((holomorphicStructureSheaf I X).obj.obj (op U))) :
    ∃ V : Opens X, x ∈ V ∧ ∃ (hVU : V ≤ U) (m : ℕ)
      (r : Fin m → ι → (holomorphicStructureSheaf I X).obj.obj (op V)),
      (∀ j, (F.map (restrictAlgHom I hVU)).mulVec (r j) = 0) ∧
      ∀ (y : X) (hy : y ∈ V),
        Submodule.span ((holomorphicStructureSheaf I X).presheaf.stalk y)
            (Set.range fun j i ↦
              (holomorphicStructureSheaf I X).presheaf.germ V y hy (r j i)) =
          LinearMap.ker (Matrix.mulVecLin
            (F.map ((holomorphicStructureSheaf I X).presheaf.germ U y (hVU hy)))) := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  let e := chartAt H x
  have he : e ∈ maximalAtlas I ω X := chart_mem_maximalAtlas x
  have hx_e : x ∈ e.source := mem_chart_source H x
  let U₀ : Set X := (U : Set X) ∩ e.source
  have hU₀_open : IsOpen U₀ := U.isOpen.inter e.open_source
  have hU_E_open : IsOpen (e.extend I '' U₀) := isOpen_iff_mem_nhds.2 fun _ ⟨_, hy, h⟩ ↦
    h ▸ e.extend_image_nhds_mem_nhds_of_boundaryless hy.2 (hU₀_open.mem_nhds hy)
  let F_ext (l : κ) (i : ι) : X → ℂ := Subtype.val.extend (toFun I X (op U) (F l i)) 0
  have hF_E (l : κ) (i : ι) : AnalyticOnNhd ℂ (F_ext l i ∘ (e.extend I).symm) (e.extend I '' U₀) :=
    (TauCeti.contMDiffOn_omega_iff_analyticOnNhd_of_mem_maximalAtlas
      he hU₀_open inter_subset_right).1 fun y hy ↦
        (((contMDiff (F l i)).contMDiffAt (x := ⟨y, hy.1⟩)).extend_subtypeVal 0).contMDiffWithinAt
  obtain ⟨W, hWo, hcxW, _, m, r_E, hr_E_an, hr_E_rel, hr_E_gen⟩ :=
    TauCeti.exists_analyticOnNhd_systemRelationGenerators hU_E_open hF_E ⟨x, ⟨hx, hx_e⟩, rfl⟩
  let V : Opens X := ⟨(U : Set X) ∩ (e.source ∩ e.extend I ⁻¹' W),
    U.isOpen.inter (e.isOpen_extend_preimage (I := I) hWo)⟩
  have hVU : V ≤ U := fun _ hz ↦ hz.1
  let r (j : Fin m) (i : ι) : (holomorphicStructureSheaf I X).obj.obj (op V) :=
    ofContMDiff (fun z : V ↦ r_E j i (e.extend I z)) fun z ↦
      (contMDiffAt_subtype_iff (f := fun w : X ↦ r_E j i (e.extend I w))).2 <|
        (TauCeti.contMDiffAt_modelSpace_omega_iff_analyticAt.2
          (hr_E_an j i _ z.2.2.2)).comp (z : X) (e.contMDiffAt_extend he z.2.2.1)
  have hr_z (j : Fin m) (i : ι) (z : V) : r j i z = r_E j i (e.extend I z) :=
    ofContMDiff_apply _ _ z
  have hr_mulVec (j : Fin m) : (F.map (restrictAlgHom I hVU)).mulVec (r j) = 0 := by
    funext l; ext z
    have hz_c : (z : X) ∈ (e.extend I).source := by rw [e.extend_source]; exact z.2.2.1
    have hFz (i : ι) : F l i (Opens.inclusion hVU z) =
        (F_ext l i ∘ (e.extend I).symm) (e.extend I z) := by
      simp only [F_ext, Function.comp_apply, (e.extend I).left_inv hz_c]
      exact (Subtype.val_injective.extend_apply _ (0 : X → ℂ) (Opens.inclusion hVU z)).symm
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, zero_apply,
      sum_apply, mul_apply]
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans (hr_E_rel j l (e.extend I z) z.2.2.2)
    rw [restrictAlgHom_apply hVU (F l i) z, hFz i, hr_z j i z, mul_comm]
  refine ⟨V, ⟨hx, hx_e, hcxW⟩, hVU, m, r, hr_mulVec, fun y hy ↦
    le_antisymm (Submodule.span_le.2 ?_) fun a_stalk ha_stalk ↦
      mem_span_germ_of_mem_ker_mulVecLin he hVU (fun _ hz ↦ hz.2.1) (fun _ hz ↦ hz.2.2)
        hr_z hr_E_gen hy ha_stalk⟩
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  ext l
  have hj0 := congrArg ((holomorphicStructureSheaf I X).presheaf.germ V y hy).hom
    (congrFun (hr_mulVec j) l)
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, map_sum, map_mul,
    map_zero] at hj0 ⊢
  exact (Finset.sum_congr rfl fun i _ ↦ by
    rw [← germ_restrictAlgHom hVU y hy (F l i)]).trans hj0

/-- **Oka's coherence theorem on complex manifolds (linear-combination form).** For a finite family
`f : ι → 𝒪_X(U)` of holomorphic sections on an open subset `U` of a boundaryless finite-dimensional
complex manifold `X` and `x ∈ U`, there exist an open neighbourhood `V ≤ U` of `x` and finitely many
holomorphic relation tuples `r : Fin m → ι → 𝒪_X(V)` whose germs at every `y ∈ V` span the stalk
kernel of `Fintype.linearCombination 𝒪_{X, y} (germ U y (hVU hy) ∘ f)`. -/
theorem exists_span_germ_eq_ker_linearCombination {ι : Type*} [Fintype ι]
    {U : Opens X} {x : X} (hx : x ∈ U)
    (f : ι → (holomorphicStructureSheaf I X).obj.obj (op U)) :
    ∃ V : Opens X, x ∈ V ∧ ∃ (hVU : V ≤ U) (m : ℕ)
      (r : Fin m → ι → (holomorphicStructureSheaf I X).obj.obj (op V)),
      (∀ j, ∑ i, r j i * restrictAlgHom I hVU (f i) = 0) ∧
      ∀ (y : X) (hy : y ∈ V),
        Submodule.span ((holomorphicStructureSheaf I X).presheaf.stalk y)
            (Set.range fun j i ↦
              (holomorphicStructureSheaf I X).presheaf.germ V y hy (r j i)) =
          LinearMap.ker (Fintype.linearCombination
            ((holomorphicStructureSheaf I X).presheaf.stalk y)
            (fun i ↦ (holomorphicStructureSheaf I X).presheaf.germ U y (hVU hy) (f i))) := by
  obtain ⟨V, hxV, hVU, m, r, hr_rel, hr_ker⟩ :=
    exists_span_germ_eq_ker_mulVecLin hx (Matrix.of fun _ : Unit ↦ f)
  refine ⟨V, hxV, hVU, m, r, fun j ↦ ?_, fun y hy ↦ ?_⟩
  · have hj0 := congrFun (hr_rel j) ()
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Pi.zero_apply] at hj0
    exact (Finset.sum_congr rfl fun i _ ↦ mul_comm _ _).trans hj0
  · exact (hr_ker y hy).trans (ker_mulVecLin_map_unit_eq_ker_linearCombination f _)

/-- **Oka's coherence theorem for Mathlib's complex-smooth structure sheaf (matrix form).**
Transfers `exists_span_germ_eq_ker_mulVecLin` along `smoothSectionsEquiv` and `smoothStalkIso` to
`smoothSheafCommRing I 𝓘(ℂ) X ℂ`. -/
theorem exists_span_smoothStalk_germ_eq_ker_mulVecLin {κ ι : Type*} [Finite κ] [Fintype ι]
    {U : Opens X} {x : X} (hx : x ∈ U)
    (F : Matrix κ ι ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U))) :
    ∃ V : Opens X, x ∈ V ∧ ∃ (hVU : V ≤ U) (m : ℕ)
      (r : Fin m → ι → (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op V)),
      (∀ j, (F.map ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.map (op (homOfLE hVU)))).mulVec
        (r j) = 0) ∧
      ∀ (y : X) (hy : y ∈ V),
        Submodule.span ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk y)
            (Set.range fun j i ↦
              (smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.germ V y hy (r j i)) =
          LinearMap.ker (Matrix.mulVecLin
            (F.map ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.germ U y (hVU hy)))) := by
  let F₀ : Matrix κ ι ((holomorphicStructureSheaf I X).obj.obj (op U)) :=
    F.map (smoothSectionsEquiv I X U).symm
  obtain ⟨V, hxV, hVU, m, r₀, hr₀_rel, hr₀_ker⟩ := exists_span_germ_eq_ker_mulVecLin hx F₀
  let r (j : Fin m) (i : ι) := smoothSectionsEquiv I X V (r₀ j i)
  have hres (s : (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U)) :
      (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.map (op (homOfLE hVU)) s =
        smoothSectionsEquiv I X V (restrictAlgHom I hVU ((smoothSectionsEquiv I X U).symm s)) :=
    ContMDiffMap.ext fun z ↦
      (smoothSectionsEquiv_symm_apply U s (Opens.inclusion hVU z)).symm.trans
        ((restrictAlgHom_apply hVU _ z).symm.trans (smoothSectionsEquiv_apply V _ z).symm)
  refine ⟨V, hxV, hVU, m, r, fun j ↦ ?_, fun y hy ↦ ?_⟩
  · ext l
    have hj0 := congrArg (smoothSectionsEquiv I X V) (congrFun (hr₀_rel j) l)
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, F₀, r, hres, map_sum, map_mul,
      Pi.zero_apply, map_zero] using hj0
  · let e_y := (smoothStalkIso I X y).commRingCatIsoToRingEquiv
    have he_r (j : Fin m) (i : ι) :
        e_y ((holomorphicStructureSheaf I X).presheaf.germ V y hy (r₀ j i)) =
          (smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.germ V y hy (r j i) :=
      smoothStalkIso_hom_germ y V hy (r₀ j i)
    have he_F : (F₀.map ((holomorphicStructureSheaf I X).presheaf.germ U y (hVU hy))).map e_y =
        F.map ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.germ U y (hVU hy)) := by
      ext l i
      simp only [Matrix.map_apply, F₀]
      exact (smoothStalkIso_hom_germ y U (hVU hy) ((smoothSectionsEquiv I X U).symm (F l i))).trans
        (congrArg _ (RingEquiv.apply_symm_apply _ (F l i)))
    simpa only [he_r, he_F] using
      span_range_map_ringEquiv_eq_ker_mulVecLin e_y _ _ (hr₀_ker y hy)

/-- **Oka's coherence theorem for Mathlib's complex-smooth structure sheaf (linear-combination
form).** -/
theorem exists_span_smoothStalk_germ_eq_ker_linearCombination {ι : Type*} [Fintype ι]
    {U : Opens X} {x : X} (hx : x ∈ U)
    (f : ι → (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op U)) :
    ∃ V : Opens X, x ∈ V ∧ ∃ (hVU : V ≤ U) (m : ℕ)
      (r : Fin m → ι → (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.obj (op V)),
      (∀ j, ∑ i, r j i *
        (smoothSheafCommRing I 𝓘(ℂ) X ℂ).obj.map (op (homOfLE hVU)) (f i) = 0) ∧
      ∀ (y : X) (hy : y ∈ V),
        Submodule.span ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk y)
            (Set.range fun j i ↦
              (smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.germ V y hy (r j i)) =
          LinearMap.ker (Fintype.linearCombination
            ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk y)
            (fun i ↦ (smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.germ U y (hVU hy) (f i))) := by
  obtain ⟨V, hxV, hVU, m, r, hr_rel, hr_ker⟩ :=
    exists_span_smoothStalk_germ_eq_ker_mulVecLin hx (Matrix.of fun _ : Unit ↦ f)
  refine ⟨V, hxV, hVU, m, r, fun j ↦ ?_, fun y hy ↦ ?_⟩
  · have hj0 := congrFun (hr_rel j) ()
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Pi.zero_apply] at hj0
    exact (Finset.sum_congr rfl fun i _ ↦ mul_comm _ _).trans hj0
  · exact (hr_ker y hy).trans (ker_mulVecLin_map_unit_eq_ker_linearCombination f _)

end Manifold

end holomorphicStructureSheaf

end TauCeti
