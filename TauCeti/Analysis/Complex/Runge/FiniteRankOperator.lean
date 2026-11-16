/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Complex.ClosedAnnulus
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Complex.Runge.SimpleFraction

/-!
# Finite-rank Runge approximation operators

Let `Ω ⊆ ℂ` be open and let `K ⊆ Ω` be a compact subset filled in `Ω` (`TauCeti.IsFilledIn K Ω`,
meaning no connected component of `Ω \ K` is relatively compact in `Ω`). Given an open
neighbourhood `V` of `K` and `ε > 0`, this file constructs finitely many evaluation nodes
`ζ i ∈ V \ K`, scalar weights `w i ∈ ℂ` and scalar functions `g i : ℂ → ℂ` holomorphic on all of
`Ω`, depending only on `Ω`, `K`, `V` and `ε`, such that for every complex normed space `F` and
every `f : ℂ → F` holomorphic on `V` and bounded by `M` there,

`‖f z - ∑ i, (w i * g i z) • f (ζ i)‖ ≤ ε * M`  for all `z ∈ K`

(`TauCeti.IsFilledIn.exists_norm_sub_sum_mul_smul_le`). Specializing `V` to the interior of a
compact collar `L ⊆ U ∩ Ω` with `K ⊆ interior L` bounds the uniform error on `K` by
`ε * sSup ((‖f ·‖) '' L)` (`TauCeti.IsFilledIn.exists_sSup_norm_sub_sum_mul_smul_le`).

The construction combines the discretized Cauchy–Pompeiu formula
(`IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le`), which approximates `f` on `K` within
`(ε / 2) * M` by a linear combination `∑ i, (c i * (z - ζ i)⁻¹) • f (ζ i)` with fixed poles
`ζ i ∈ V \ K`, and Runge approximation of each simple fraction `(z - ζ i)⁻¹` on `K` by a function
`g i` holomorphic on `Ω` (`TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`).

Because the nodes `ζ i`, weights `w i` and holomorphic basis functions `g i` do not depend on `f`
or on the target normed space `F`, applying the operator slicewise to a family `h : P → ℂ → F`
produces a function holomorphic in the plane variable on `Ω` that is jointly `C^n` whenever the
point evaluations `p ↦ h p (ζ i)` are `C^n`, preserves complex differentiability in external
complex parameters, and commutes with iterated Fréchet derivatives in external real parameters.

Finally, the filledness hypothesis is essential: for `0 < r₁ ≤ r₂` and `r₁ < R`, the closed
annulus `Complex.closedAnnulus r₁ r₂` is not filled in `ball 0 R`, and Cauchy's integral theorem
around the inner circle `sphere 0 r₁` rules out approximating `z⁻¹` on the annulus within
`ε * s₁⁻¹` by any function holomorphic on `ball 0 R` when `ε < s₁ / r₁` (for instance `ε < 3 / 4`
for the annulus `2 ≤ ‖z‖ ≤ 3` in `ball 0 4` with collar `3 / 2 ≤ ‖z‖ ≤ 7 / 2`).

## Main results

* `TauCeti.IsFilledIn.exists_norm_sub_sum_mul_smul_le`: finite-rank Runge operator on `(Ω, K, V)`
  for bounded holomorphic maps into an arbitrary complex normed space.
* `TauCeti.IsFilledIn.exists_sSup_norm_sub_sum_mul_smul_le`: supremum-norm form on a compact
  collar `L ⊆ U ∩ Ω` with `K ⊆ interior L`.
* `TauCeti.differentiableOn_sum_mul_smul`, `TauCeti.conjWirtingerDeriv_sum_mul_smul_eq_zero`,
  `TauCeti.contDiffOn_sum_mul_smul_prod`, `TauCeti.differentiableOn_sum_mul_smul_param`,
  `TauCeti.iteratedFDeriv_sum_mul_smul_param`: plane holomorphy, vanishing of `\bar∂`, joint
  smoothness, preservation of parameter holomorphy, and commutation with iterated parameter
  derivatives for finite-rank combinations.
* `TauCeti.not_isFilledIn_closedAnnulus_ball`,
  `TauCeti.inv_le_of_differentiableOn_ball_norm_inv_sub_le_closedAnnulus`, and
  `TauCeti.not_exists_differentiableOn_ball_norm_inv_sub_le_closedAnnulus`: failure of filledness
  and quantitative obstruction to holomorphic approximation on an annulus inside a disc.

## References

* A. Rainer, *Advanced Complex Analysis*, lecture notes, Theorem 10.3 and Theorem 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.2.1 and Theorem 1.3.9.
-/

public section

open Complex Filter Function Metric Set
open scoped Real Topology ContDiff

universe u

namespace TauCeti

section FiniteRankOperator

variable {K V U L Ω : Set ℂ}

/-- **Finite-rank Runge approximation operator.** Let `Ω ⊆ ℂ` be open, let `K ⊆ Ω` be compact and
filled in `Ω`, and let `V ⊆ ℂ` be an open neighbourhood of `K`. For every `ε > 0` there exist
finitely many evaluation points `ζ i ∈ V \ K`, scalar weights `w i ∈ ℂ` and functions `g i : ℂ → ℂ`
holomorphic on `Ω`, independent of `f` and of the target normed space `F`, such that every
`f : ℂ → F` holomorphic on `V` with `‖f z‖ ≤ M` on `V` satisfies
`‖f z - ∑ i, (w i * g i z) • f (ζ i)‖ ≤ ε * M` for all `z ∈ K`. -/
theorem IsFilledIn.exists_norm_sub_sum_mul_smul_le (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hV : IsOpen V) (hKV : K ⊆ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (w : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
      (∀ i, ζ i ∈ V \ K) ∧ (∀ i, DifferentiableOn ℂ (g i) Ω) ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] (f : ℂ → F) (M : ℝ),
        DifferentiableOn ℂ f V → (∀ z ∈ V, ‖f z‖ ≤ M) →
        ∀ z ∈ K, ‖f z - ∑ i, (w i * g i z) • f (ζ i)‖ ≤ ε * M := by
  -- Step 1: discretize the Cauchy–Pompeiu cutoff integral on `V` to error `(ε / 2) * M`.
  obtain ⟨N, ζ, c, hζ, hrat⟩ :=
    hK.exists_norm_sub_sum_mul_sub_inv_smul_le.{u} hV hKV (half_pos hε)
  -- Step 2: approximate each simple fraction `(z - ζ i)⁻¹` on `K` by `g i` holomorphic on `Ω`.
  set C : ℝ := ∑ i : Fin N, ‖c i‖
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hC1 : 0 < C + 1 := by linarith
  set δ : ℝ := ε / 2 / (C + 1)
  have hδ : 0 < δ := div_pos (half_pos hε) hC1
  choose g hg_hol hg_est using fun i : Fin N ↦
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ (hζ i).2 hδ
  refine ⟨N, ζ, c, g, hζ, hg_hol, fun {F} _ _ f M hf hM z hz ↦ ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg (f z)).trans (hM z (hKV hz))
  have hdiff_split :
      f z - ∑ i, (c i * g i z) • f (ζ i) =
        (f z - ∑ i, (c i * (z - ζ i)⁻¹) • f (ζ i)) +
          ∑ i, (c i * ((z - ζ i)⁻¹ - g i z)) • f (ζ i) := by
    have hterm (i : Fin N) :
        (c i * ((z - ζ i)⁻¹ - g i z)) • f (ζ i) =
          (c i * (z - ζ i)⁻¹) • f (ζ i) - (c i * g i z) • f (ζ i) := by
      rw [mul_sub, sub_smul]
    simp_rw [hterm, Finset.sum_sub_distrib]
    abel
  have htail :
      ‖∑ i, (c i * ((z - ζ i)⁻¹ - g i z)) • f (ζ i)‖ ≤ ε / 2 * M := by
    calc ‖∑ i, (c i * ((z - ζ i)⁻¹ - g i z)) • f (ζ i)‖
        ≤ ∑ i, ‖(c i * ((z - ζ i)⁻¹ - g i z)) • f (ζ i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * δ * M := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [norm_smul, norm_mul]
          have hgi : ‖(z - ζ i)⁻¹ - g i z‖ ≤ δ := (hg_est i z hz).le
          have hfi : ‖f (ζ i)‖ ≤ M := hM (ζ i) (hζ i).1
          exact mul_le_mul (mul_le_mul_of_nonneg_left hgi (norm_nonneg _)) hfi (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) hδ.le)
      _ = C * δ * M := by
          simp only [C, Finset.sum_mul]
      _ ≤ ε / 2 * M := by
          have hCδ : C * δ ≤ ε / 2 := by
            rw [show C * δ = ε / 2 * (C / (C + 1)) by simp only [δ]; ring]
            exact mul_le_of_le_one_right (half_pos hε).le ((div_le_one hC1).2 (by linarith))
          exact mul_le_mul_of_nonneg_right hCδ hM0
  rw [hdiff_split]
  calc ‖(f z - ∑ i, (c i * (z - ζ i)⁻¹) • f (ζ i)) +
          ∑ i, (c i * ((z - ζ i)⁻¹ - g i z)) • f (ζ i)‖
      ≤ ‖f z - ∑ i, (c i * (z - ζ i)⁻¹) • f (ζ i)‖ +
          ‖∑ i, (c i * ((z - ζ i)⁻¹ - g i z)) • f (ζ i)‖ := norm_add_le _ _
    _ ≤ ε / 2 * M + ε / 2 * M := add_le_add (hrat f M hf hM z hz) htail
    _ = ε * M := by ring

/-- **Collar supremum form of the finite-rank Runge operator.** Let `Ω ⊆ ℂ` be open, `K ⊆ Ω`
compact and filled in `Ω`, `U ⊇ K` open, and `L ⊆ U ∩ Ω` a compact collar with `K ⊆ interior L`.
For every `ε > 0` there exist evaluation nodes `ζ i ∈ interior L \ K`, weights `w i ∈ ℂ` and
functions `g i : ℂ → ℂ` holomorphic on `Ω`, depending only on `Ω`, `K`, `L` and `ε`, such that
every `f : ℂ → F` holomorphic on `U` satisfies both the pointwise estimate
`‖f z - ∑ i, (w i * g i z) • f (ζ i)‖ ≤ ε * sSup ((‖f ·‖) '' L)` on `K` and the supremum estimate
`sSup ((fun z ↦ ‖f z - ∑ i, (w i * g i z) • f (ζ i)‖) '' K) ≤ ε * sSup ((‖f ·‖) '' L)`. -/
theorem IsFilledIn.exists_sSup_norm_sub_sum_mul_smul_le (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {U L : Set ℂ} (hLU : L ⊆ U ∩ Ω) (hL : IsCompact L)
    (hKL : K ⊆ interior L) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (w : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
      (∀ i, ζ i ∈ interior L \ K) ∧ (∀ i, DifferentiableOn ℂ (g i) Ω) ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] (f : ℂ → F),
        DifferentiableOn ℂ f U →
        (∀ z ∈ K, ‖f z - ∑ i, (w i * g i z) • f (ζ i)‖ ≤ ε * sSup ((‖f ·‖) '' L)) ∧
        sSup ((fun z ↦ ‖f z - ∑ i, (w i * g i z) • f (ζ i)‖) '' K) ≤
          ε * sSup ((‖f ·‖) '' L) := by
  obtain ⟨N, ζ, w, g, hζ, hg, hop⟩ :=
    hfill.exists_norm_sub_sum_mul_smul_le.{u} hΩ hK hKΩ isOpen_interior hKL hε
  refine ⟨N, ζ, w, g, hζ, hg, fun {F} _ _ f hf ↦ ?_⟩
  have hfL : ContinuousOn (fun z ↦ ‖f z‖) L :=
    (hf.continuousOn.mono (hLU.trans inter_subset_left)).norm
  have hbddL : BddAbove ((‖f ·‖) '' L) := (hL.image_of_continuousOn hfL).bddAbove
  have hleL (z : ℂ) (hz : z ∈ interior L) : ‖f z‖ ≤ sSup ((‖f ·‖) '' L) :=
    le_csSup hbddL ⟨z, interior_subset hz, rfl⟩
  have hpt : ∀ z ∈ K, ‖f z - ∑ i, (w i * g i z) • f (ζ i)‖ ≤ ε * sSup ((‖f ·‖) '' L) :=
    hop f (sSup ((‖f ·‖) '' L)) (hf.mono (interior_subset.trans (hLU.trans inter_subset_left))) hleL
  refine ⟨hpt, ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp only [image_empty, Real.sSup_empty]
    rcases L.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
    · simp
    · exact mul_nonneg hε.le ((norm_nonneg (f z₀)).trans (le_csSup hbddL ⟨z₀, hz₀, rfl⟩))
  · exact csSup_le (hKne.image _) (forall_mem_image.2 hpt)

end FiniteRankOperator

/-! ### Calculus of finite-rank holomorphic combinations with parameters -/

section ParameterCalculus

variable {ι : Type*} [Fintype ι] {Ω : Set ℂ}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A finite combination `z ↦ ∑ i, (w i * g i z) • v i` with basis functions `g i` holomorphic on
`Ω` is holomorphic on `Ω`. -/
theorem differentiableOn_sum_mul_smul (w : ι → ℂ) {g : ι → ℂ → ℂ}
    (hg : ∀ i, DifferentiableOn ℂ (g i) Ω) (v : ι → F) :
    DifferentiableOn ℂ (fun z ↦ ∑ i, (w i * g i z) • v i) Ω :=
  DifferentiableOn.fun_sum fun i _ ↦ ((hg i).const_mul (w i)).smul_const (v i)

/-- The conjugate Wirtinger derivative of `z ↦ ∑ i, (w i * g i z) • v i` vanishes on an open set
`Ω` where each `g i` is holomorphic. -/
theorem conjWirtingerDeriv_sum_mul_smul_eq_zero (hΩ : IsOpen Ω) (w : ι → ℂ) {g : ι → ℂ → ℂ}
    (hg : ∀ i, DifferentiableOn ℂ (g i) Ω) (v : ι → F) {z : ℂ} (hz : z ∈ Ω) :
    conjWirtingerDeriv (fun y ↦ ∑ i, (w i * g i y) • v i) z 1 = 0 := by
  have hd := (differentiableOn_sum_mul_smul w hg v).differentiableAt (hΩ.mem_nhds hz)
  simp [hd.conjWirtingerDeriv_eq_zero]

/-- **Joint smoothness in parameters and the plane variable.** If each `g i` is holomorphic on an
open set `Ω ⊆ ℂ` and each coefficient map `v i : P → F` is `C^n` on `s ⊆ P`, then
`(p, z) ↦ ∑ i, (w i * g i z) • v i p` is `C^n` on `s ×ˢ Ω`. -/
theorem contDiffOn_sum_mul_smul_prod {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {s : Set P} {n : WithTop ℕ∞} (hΩ : IsOpen Ω) (w : ι → ℂ) {g : ι → ℂ → ℂ}
    (hg : ∀ i, DifferentiableOn ℂ (g i) Ω) {v : ι → P → F}
    (hv : ∀ i, ContDiffOn ℝ n (v i) s) :
    ContDiffOn ℝ n (fun q : P × ℂ ↦ ∑ i, (w i * g i q.2) • v i q.1) (s ×ˢ Ω) := by
  refine ContDiffOn.sum fun i _ ↦ ?_
  have hgi : ContDiffOn ℝ n (fun q : P × ℂ ↦ w i * g i q.2) (s ×ˢ Ω) :=
    contDiffOn_const.mul ((((hg i).contDiffOn hΩ).restrict_scalars ℝ).comp contDiffOn_snd
      fun _ hq ↦ hq.2)
  exact hgi.smul ((hv i).comp contDiffOn_fst fun _ hq ↦ hq.1)

/-- **Preservation of parameter holomorphy.** If each `v i : Q → F` is holomorphic on `Q`, then
`q ↦ ∑ i, (w i * g i z) • v i q` is holomorphic on `Q` for every `z : ℂ`. -/
theorem differentiableOn_sum_mul_smul_param {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    {U : Set Q} (w : ι → ℂ) (g : ι → ℂ → ℂ) {v : ι → Q → F}
    (hv : ∀ i, DifferentiableOn ℂ (v i) U) (z : ℂ) :
    DifferentiableOn ℂ (fun q ↦ ∑ i, (w i * g i z) • v i q) U :=
  DifferentiableOn.fun_sum fun i _ ↦ (hv i).const_smul (w i * g i z)

/-- **Commutation with iterated parameter derivatives.** For an open set `s` in a real normed space
`P` and `C^m` coefficient maps `v i : P → F`, differentiating `p ↦ ∑ i, (w i * g i z) • v i p` `m`
times at `p ∈ s` applies the same finite-rank scalar weights to `iteratedFDeriv ℝ m (v i) p`. -/
theorem iteratedFDeriv_sum_mul_smul_param {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {s : Set P} {m : ℕ} (hs : IsOpen s) (w : ι → ℂ) (g : ι → ℂ → ℂ) {v : ι → P → F}
    (hv : ∀ i, ContDiffOn ℝ m (v i) s) {p : P} (hp : p ∈ s) (z : ℂ) :
    iteratedFDeriv ℝ m (fun q ↦ ∑ i, (w i * g i z) • v i q) p =
      ∑ i, (w i * g i z) • iteratedFDeriv ℝ m (v i) p := by
  have hvi (i : ι) : ContDiffAt ℝ m (v i) p := (hv i).contDiffAt (hs.mem_nhds hp)
  have hsmul (i : ι) : ContDiffAt ℝ m (fun q ↦ (w i * g i z) • v i q) p :=
    (hvi i).const_smul (w i * g i z)
  -- Express constant complex scalar multiplication through a continuous `ℝ`-linear map so
  -- `ContinuousLinearMap.iteratedFDeriv_comp_left` commutes it past `iteratedFDeriv ℝ m`.
  have hterm (i : ι) :
      iteratedFDeriv ℝ m (fun q ↦ (w i * g i z) • v i q) p =
        (w i * g i z) • iteratedFDeriv ℝ m (v i) p := by
    let L : F →L[ℝ] F := (ContinuousLinearMap.lsmul ℂ ℂ (w i * g i z)).restrictScalars ℝ
    have hL := L.iteratedFDeriv_comp_left (hvi i) le_rfl
    ext u
    exact DFunLike.congr_fun hL u
  have hsum :
      ∀ S : Finset ι,
        iteratedFDeriv ℝ m (fun q ↦ ∑ i ∈ S, (w i * g i z) • v i q) p =
          ∑ i ∈ S, iteratedFDeriv ℝ m (fun q ↦ (w i * g i z) • v i q) p := by
    intro S
    induction S using Finset.cons_induction with
    | empty => simp
    | cons a S haS ih =>
      simp only [Finset.sum_cons]
      exact (iteratedFDeriv_add_apply (f := fun q ↦ (w a * g a z) • v a q)
        (g := fun q ↦ ∑ i ∈ S, (w i * g i z) • v i q)
        (hsmul a) (ContDiffAt.sum fun i _ ↦ hsmul i)).trans (by rw [ih])
  rw [hsum Finset.univ]
  exact Finset.sum_congr rfl fun i _ ↦ hterm i

end ParameterCalculus

/-! ### Sharpness on an annulus in a disc -/

section AnnulusObstruction

/-- For `0 < r₁ ≤ r₂` and `r₁ < R`, the closed annulus `Complex.closedAnnulus r₁ r₂` is **not**
filled in `ball 0 R`: the central hole `ball 0 r₁` is a connected component of
`ball 0 R \ Complex.closedAnnulus r₁ r₂` whose closure `closedBall 0 r₁` is compact and lies inside
`ball 0 R`. -/
theorem not_isFilledIn_closedAnnulus_ball {r₁ r₂ R : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂)
    (hrR : r₁ < R) : ¬ IsFilledIn (Complex.closedAnnulus r₁ r₂) (ball 0 R) := by
  intro hfill
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R \ Complex.closedAnnulus r₁ r₂ := by
    simp [Complex.mem_closedAnnulus, hr₁.trans hrR, not_le.2 hr₁]
  refine isFilledIn_iff.1 hfill 0 h0 ?_
  -- Every point outside the closed annulus lies in the disjoint open union
  -- `ball 0 r₁ ∪ (closedBall 0 r₁)ᶜ`, so the component of `0` stays in `ball 0 r₁`.
  have hcomp :
      connectedComponentIn (ball (0 : ℂ) R \ Complex.closedAnnulus r₁ r₂) 0 ⊆ ball 0 r₁ := by
    refine isPreconnected_connectedComponentIn.subset_left_of_subset_union isOpen_ball
      isClosed_closedBall.isOpen_compl (disjoint_compl_right.mono_left ball_subset_closedBall) ?_
      ⟨0, mem_connectedComponentIn h0, mem_ball_self hr₁⟩
    intro z hz
    have hz_out := connectedComponentIn_subset _ _ hz
    by_cases hlt : ‖z‖ < r₁
    · exact Or.inl (mem_ball_zero_iff.2 hlt)
    · refine Or.inr ?_
      rw [mem_compl_iff, mem_closedBall_zero_iff, not_le]
      have hr₂ : r₂ < ‖z‖ := by
        by_contra hle
        exact hz_out.2 (Complex.mem_closedAnnulus.2 ⟨not_lt.1 hlt, not_lt.1 hle⟩)
      exact hr₁₂.trans_lt hr₂
  have hcl : closure (connectedComponentIn (ball (0 : ℂ) R \ Complex.closedAnnulus r₁ r₂) 0) ⊆
      closedBall 0 r₁ := (closure_mono hcomp).trans closure_ball_subset_closedBall
  exact ⟨(isCompact_closedBall 0 r₁).of_isClosed_subset isClosed_closure hcl,
    hcl.trans (closedBall_subset_ball hrR)⟩

/-- **Contour-integral lower bound on an annulus.** If `0 < r₁ ≤ r₂`, `r₁ < R` and `G : ℂ → ℂ` is
holomorphic on `ball 0 R` with `‖z⁻¹ - G z‖ ≤ B` on `Complex.closedAnnulus r₁ r₂`, then
`r₁⁻¹ ≤ B`. Integrating `z⁻¹ - G z` around `C(0, r₁)` gives `2πi`, because `G` extends
holomorphically across the hole `ball 0 r₁`. -/
theorem inv_le_of_differentiableOn_ball_norm_inv_sub_le_closedAnnulus {r₁ r₂ R B : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂) (hrR : r₁ < R) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball 0 R))
    (hB : ∀ z ∈ Complex.closedAnnulus r₁ r₂, ‖z⁻¹ - G z‖ ≤ B) : r₁⁻¹ ≤ B := by
  have hG_zero : (∮ z in C(0, r₁), G z) = 0 :=
    ((hG.mono (closure_ball_subset_closedBall.trans (closedBall_subset_ball hrR))).diffContOnCl)
      |>.circleIntegral_eq_zero hr₁.le
  have hinv_int : (∮ z in C(0, r₁), z⁻¹) = 2 * π * I := by
    simpa using circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := 0) (mem_ball_self hr₁)
  have hG_ci : CircleIntegrable G 0 r₁ :=
    (hG.continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hrR)))
      |>.circleIntegrable hr₁.le
  have hinv_ci : CircleIntegrable (fun z : ℂ ↦ z⁻¹) 0 r₁ :=
    (ContinuousOn.inv₀ continuousOn_id fun z hz ↦
      ne_of_mem_sphere hz hr₁.ne').circleIntegrable hr₁.le
  have hint_sub : (∮ z in C(0, r₁), (z⁻¹ - G z)) = 2 * π * I := by
    rw [circleIntegral.integral_sub hinv_ci hG_ci, hinv_int, hG_zero, sub_zero]
  have hsph : ∀ z ∈ sphere (0 : ℂ) r₁, ‖z⁻¹ - G z‖ ≤ B := fun z hz ↦ by
    have hnorm : ‖z‖ = r₁ := by simpa [abs_of_pos hr₁] using mem_sphere_zero_iff_norm.1 hz
    exact hB z (Complex.mem_closedAnnulus.2 ⟨hnorm.ge, hnorm.le.trans hr₁₂⟩)
  have hnorm_int := circleIntegral.norm_integral_le_of_norm_le_const hr₁.le hsph
  rw [hint_sub, norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg
    Real.pi_pos.le, norm_I, mul_one] at hnorm_int
  have h1 : 1 ≤ B * r₁ := by
    nlinarith [Real.pi_pos]
  rwa [inv_le_iff_one_le_mul₀ hr₁]

/-- **Sharpness of filledness for Runge operators on an annulus.** Let `0 < s₁ ≤ r₁ ≤ r₂ ≤ s₂`
and `r₁ < R`. For `ε < s₁ / r₁`, no function `G` holomorphic on `ball 0 R` (in particular, no
linear combination `∑ i, w i * g i z * f (ζ i)` with `g i` holomorphic on `ball 0 R`) satisfies the
collar Runge estimate `‖f z - G z‖ ≤ ε * sSup ((‖f ·‖) '' Complex.closedAnnulus s₁ s₂)` on
`Complex.closedAnnulus r₁ r₂` for `f z = z⁻¹`. For `r₁ = 2`, `r₂ = 3`, `R = 4`, `s₁ = 3 / 2` and
`s₂ = 7 / 2`, this rules out every `ε < 3 / 4`. -/
theorem not_exists_differentiableOn_ball_norm_inv_sub_le_closedAnnulus
    {s₁ r₁ r₂ s₂ R ε : ℝ} (hs₁ : 0 < s₁) (hsr₁ : s₁ ≤ r₁) (hr₁₂ : r₁ ≤ r₂) (hrs₂ : r₂ ≤ s₂)
    (hrR : r₁ < R) (hε : ε < s₁ / r₁) :
    ¬ ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 R) ∧
      ∀ z ∈ Complex.closedAnnulus r₁ r₂,
        ‖z⁻¹ - G z‖ ≤ ε * sSup ((fun w : ℂ ↦ ‖w⁻¹‖) '' Complex.closedAnnulus s₁ s₂) := by
  rintro ⟨G, hG, hB⟩
  have hr₁ : 0 < r₁ := hs₁.trans_le hsr₁
  have hs₁₂ : s₁ ≤ s₂ := hsr₁.trans (hr₁₂.trans hrs₂)
  have hmem : (s₁ : ℂ) ∈ Complex.closedAnnulus s₁ s₂ := by
    rw [Complex.mem_closedAnnulus, Complex.norm_real, Real.norm_of_nonneg hs₁.le]
    exact ⟨le_rfl, hs₁₂⟩
  have hbdd_fn : ∀ x ∈ (fun w : ℂ ↦ ‖w⁻¹‖) '' Complex.closedAnnulus s₁ s₂, x ≤ s₁⁻¹ := by
    rintro _ ⟨w, hw, rfl⟩
    dsimp only
    rw [norm_inv]
    exact inv_anti₀ hs₁ (Complex.mem_closedAnnulus.1 hw).1
  have hsup_le : sSup ((fun w : ℂ ↦ ‖w⁻¹‖) '' Complex.closedAnnulus s₁ s₂) ≤ s₁⁻¹ :=
    csSup_le ⟨_, ⟨(s₁ : ℂ), hmem, rfl⟩⟩ hbdd_fn
  have hsup_nonneg : 0 ≤ sSup ((fun w : ℂ ↦ ‖w⁻¹‖) '' Complex.closedAnnulus s₁ s₂) :=
    (norm_nonneg ((s₁ : ℂ)⁻¹)).trans (le_csSup ⟨s₁⁻¹, hbdd_fn⟩ ⟨(s₁ : ℂ), hmem, rfl⟩)
  have hinv_le :=
    inv_le_of_differentiableOn_ball_norm_inv_sub_le_closedAnnulus hr₁ hr₁₂ hrR hG hB
  -- Even if `ε < 0`, `r₁⁻¹ ≤ ε * sSup` forces `0 < ε` since `r₁⁻¹ > 0` and `sSup ≥ 0`.
  have hε_pos : 0 < ε := by
    by_contra hle
    have hneg : ε * sSup ((fun w : ℂ ↦ ‖w⁻¹‖) '' Complex.closedAnnulus s₁ s₂) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hle) hsup_nonneg
    linarith [inv_pos.2 hr₁]
  have h1 : r₁⁻¹ ≤ ε * s₁⁻¹ :=
    hinv_le.trans (mul_le_mul_of_nonneg_left hsup_le hε_pos.le)
  have h2 : s₁ / r₁ ≤ ε := by
    rw [div_le_iff₀ hr₁]
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hs₁.le) hr₁.le
    have lhs_eq : r₁ * (s₁ * r₁⁻¹) = s₁ := by field_simp
    have rhs_eq : r₁ * (s₁ * (ε * s₁⁻¹)) = ε * r₁ := by field_simp
    linarith
  exact hε.not_ge h2

end AnnulusObstruction

end TauCeti
