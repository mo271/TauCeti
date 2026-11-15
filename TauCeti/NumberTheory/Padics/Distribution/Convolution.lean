/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.NumberTheory.Padics.Measure.Monoid
public import TauCeti.NumberTheory.Padics.Distribution.Comul
public import TauCeti.NumberTheory.Padics.Distribution.Dual
import TauCeti.NumberTheory.Padics.Measure.Dirac

/-!
# Additive convolution of locally analytic distributions on `ℤ_p`

Addition on `ℤ_p` induces a convolution product on the locally analytic distributions
`TauCeti.LocallyAnalyticDistribution p K`, constructed directly from the bounded two-variable stage
pairing and stage comultiplication (`TauCeti.AnalyticStage.comul`), without appeal to the Amice
transform.

At each analytic level `h`:

* `stagePair h μ ν` pairs a two-variable coefficient family in
  `C₀((ZMod (pʰ) × ℕ) × (ZMod (pʰ) × ℕ), K)` against `ν` in the inner coordinate and `μ` in the
  outer coordinate, with operator norm at most `stageSeminorm h μ * stageSeminorm h ν`. Because
  finite coordinate sums are dense in `C₀`, swapping the two variables swaps `μ` and `ν`
  (`stagePair_comp_prodComm`).
* `stageConvolveRight h ν` comultiplies a stage vector `c ∈ LA_h(K)` and applies `stage h ν` to the
  inner stage. Compatibility of `comul` with stage re-expansion (`comul_transition`) glues these
  operators to a `K`-linear endomorphism `convolveRight ν` of the algebraic direct limit
  `LA(ℤ_p, K)`.

The convolution `μ * ν` is `(μ : Module.Dual K _) ∘ₗ convolveRight ν`, whose stage-`h` restriction
is `stage h μ ∘L stageConvolveRight h ν` (equivalently `stagePair h μ ν` applied to `comul K`).
Coassociativity (`comul_assoc`), cocommutativity (`comul_comm`), and counitality at `(0, 0)` make
`LocallyAnalyticDistribution p K` a commutative `K`-algebra with identity `1 = dirac 0` and
submultiplicative stage seminorms:

`stageSeminorm h (μ * ν) ≤ stageSeminorm h μ * stageSeminorm h ν`.

Finally, `ofMultiplicativeMeasure` embeds Mathlib's convolution algebra `D(Multiplicative ℤ_[p], K)`
of `K`-valued measures injectively as a `K`-subalgebra of `LocallyAnalyticDistribution p K`,
compatibly with Dirac distributions and stage seminorm bounds.

## Main definitions

* `TauCeti.LocallyAnalyticDistribution.stagePair`: bounded two-variable stage pairing on
  `C₀((ZMod (pʰ) × ℕ)², K)`.
* `TauCeti.LocallyAnalyticDistribution.stageConvolveRight`: right convolution on stage `LA_h(K)`.
* `TauCeti.LocallyAnalyticDistribution.convolveRight`: right convolution on `LA(ℤ_p, K)`.
* `TauCeti.LocallyAnalyticDistribution.dirac`: the Dirac distribution at `x ∈ ℤ_p`.
* `TauCeti.LocallyAnalyticDistribution.instCommRing`,
  `TauCeti.LocallyAnalyticDistribution.instAlgebra`: commutative `K`-algebra structure on
  `LocallyAnalyticDistribution p K` under additive convolution.
* `TauCeti.LocallyAnalyticDistribution.diracHom`: `Multiplicative ℤ_[p] →*` into distributions.
* `TauCeti.LocallyAnalyticDistribution.ofMultiplicativeMeasure`: `K`-algebra embedding of
  `D(Multiplicative ℤ_[p], K)` into `LocallyAnalyticDistribution p K`.

## Main results

* `TauCeti.LocallyAnalyticDistribution.stagePair_comp_prodComm`: Fubini symmetry of `stagePair`.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_mul_le`: submultiplicativity of every stage
  seminorm under convolution.
* `TauCeti.LocallyAnalyticDistribution.stageSeminorm_dirac`: every Dirac distribution has stage
  seminorm `1` at every level.
* `TauCeti.LocallyAnalyticDistribution.dirac_add`: `dirac (x + y) = dirac x * dirac y`.
* `TauCeti.LocallyAnalyticDistribution.ofMultiplicativeMeasure_injective`: injectivity of the
  measure-algebra embedding.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

open ZeroAtInftyContinuousMap
open scoped AbstractMeasure ZeroAtInfty

namespace TauCeti

open AnalyticStage LocallyAnalytic

namespace LocallyAnalyticDistribution

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

/-! ### Bounded two-variable stage pairing -/

/-- **Bounded two-variable stage pairing.** Given locally analytic distributions `μ` and `ν`,
`stagePair h μ ν` curries a two-variable coefficient family on `(ZMod (p ^ h) × ℕ)²` vanishing at
infinity, applies `stage h ν` to the inner stage, and applies `stage h μ` to the resulting outer
stage. -/
noncomputable def stagePair (h : ℕ) (μ ν : LocallyAnalyticDistribution p K) :
    C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), K) →L[K] K :=
  stage h μ ∘L compLeft (stage h ν) ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩ ∘L
    (curryEquiv (I := ZMod (p ^ h) × ℕ) (J := ZMod (p ^ h) × ℕ) K K :
      C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), K) →L[K]
        AnalyticStage p h (AnalyticStage p h K))

/-- `stagePair h μ ν` curries a two-variable coefficient family, integrates the inner coordinate
against `ν`, and integrates the outer coordinate against `μ`. -/
theorem stagePair_apply (h : ℕ) (μ ν : LocallyAnalyticDistribution p K)
    (F : C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), K)) :
    stagePair h μ ν F =
      stage h μ (compLeft (stage h ν) ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩
        (curryEquiv K K F)) := by
  simp [stagePair]

/-- On a two-variable coordinate vector `single (x, y) a`, `stagePair h μ ν` factors as
`a * stage h μ (single x 1) * stage h ν (single y 1)`. -/
@[simp]
theorem stagePair_single (h : ℕ) (μ ν : LocallyAnalyticDistribution p K)
    (x y : ZMod (p ^ h) × ℕ) (a : K) :
    stagePair h μ ν (single (x, y) a) =
      a * stage h μ (single x 1) * stage h ν (single y 1) := by
  rw [stagePair_apply, curryEquiv_single, compLeft_single, ← smul_single_one y a,
    ContinuousLinearMap.map_smul, ← smul_single_one x (a • stage h ν (single y 1)),
    ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- The operator norm of `stagePair h μ ν` is bounded by `stageSeminorm h μ * stageSeminorm h ν`. -/
theorem opNorm_stagePair_le (h : ℕ) (μ ν : LocallyAnalyticDistribution p K) :
    ‖stagePair h μ ν‖ ≤ stageSeminorm h μ * stageSeminorm h ν := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (by rw [stageSeminorm_apply, stageSeminorm_apply]; positivity) fun F ↦ ?_
  rw [stagePair_apply]
  calc ‖stage h μ (compLeft (stage h ν) ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩
          (curryEquiv K K F))‖
      ≤ ‖stage h μ‖ * ‖compLeft (stage h ν) ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩
          (curryEquiv K K F)‖ := (stage h μ).le_opNorm _
    _ ≤ ‖stage h μ‖ * (‖stage h ν‖ * ‖curryEquiv K K F‖) := by
        gcongr
        exact norm_compLeft_apply_le (stage h ν) (stage h ν).le_opNorm _
    _ = stageSeminorm h μ * stageSeminorm h ν * ‖F‖ := by
        rw [LinearIsometryEquiv.norm_map, stageSeminorm_apply, stageSeminorm_apply, mul_assoc]

/-- **Fubini symmetry of the two-variable stage pairing.** Precomposing with the coordinate swap on
`(ZMod (p ^ h) × ℕ)²` exchanges the roles of `μ` and `ν`. -/
theorem stagePair_comp_prodComm (h : ℕ) (μ ν : LocallyAnalyticDistribution p K) :
    stagePair h μ ν ∘L
      (congrLeft K K (Homeomorph.prodComm (ZMod (p ^ h) × ℕ) (ZMod (p ^ h) × ℕ)) :
        C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), K) →L[K]
          C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), K)) =
      stagePair h ν μ := by
  refine continuousLinearMap_ext_single_one fun ⟨x, y⟩ ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'', congrLeft_single,
    Homeomorph.coe_prodComm, Prod.swap_prod_mk, stagePair_single]
  ring

/-! ### Right convolution on stages and on locally analytic functions -/

/-- **Right convolution on an analytic stage.** Given a distribution `ν`, `stageConvolveRight h ν`
comultiplies `c ∈ LA_h(K)` and applies `stage h ν` to the inner stage, bundled `K`-linearly in
`ν`. -/
noncomputable def stageConvolveRight (h : ℕ) :
    LocallyAnalyticDistribution p K →ₗ[K] AnalyticStage p h K →L[K] AnalyticStage p h K where
  toFun ν := compLeft (stage h ν) ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩ ∘L comul K
  map_add' _ _ := by ext c x; simp
  map_smul' _ _ := by ext c x; simp

/-- The `x`-coordinate of `stageConvolveRight h ν c` pairs the `x`-slice of `comul K c` against
`stage h ν`. -/
@[simp]
theorem stageConvolveRight_apply_apply (h : ℕ) (ν : LocallyAnalyticDistribution p K)
    (c : AnalyticStage p h K) (x : ZMod (p ^ h) × ℕ) :
    stageConvolveRight h ν c x = stage h ν (comul K c x) := by
  simp [stageConvolveRight]

/-- Integrating `stageConvolveRight h ν c` against `stage h μ` is `stagePair h μ ν` applied to the
uncurried comultiplication of `c`. -/
theorem stage_stageConvolveRight_eq_stagePair (h : ℕ) (μ ν : LocallyAnalyticDistribution p K)
    (c : AnalyticStage p h K) :
    stage h μ (stageConvolveRight h ν c) =
      stagePair h μ ν ((curryEquiv K K).symm (comul K c)) := by
  simp [stagePair_apply, stageConvolveRight]

/-- Right convolution on stage `h` is bounded by `stageSeminorm h ν`. -/
theorem norm_stageConvolveRight_apply_le (h : ℕ) (ν : LocallyAnalyticDistribution p K)
    (c : AnalyticStage p h K) :
    ‖stageConvolveRight h ν c‖ ≤ stageSeminorm h ν * ‖c‖ := by
  simpa only [stageConvolveRight, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.comp_apply,
    norm_comul, stageSeminorm_apply] using
    norm_compLeft_apply_le (stage h ν) (stage h ν).le_opNorm (comul K c)

/-- The operator norm of `stageConvolveRight h ν` is at most `stageSeminorm h ν`. -/
theorem opNorm_stageConvolveRight_le (h : ℕ) (ν : LocallyAnalyticDistribution p K) :
    ‖stageConvolveRight h ν‖ ≤ stageSeminorm h ν :=
  ContinuousLinearMap.opNorm_le_bound _ (by rw [stageSeminorm_apply]; positivity)
    (norm_stageConvolveRight_apply_le h ν)

/-- Evaluating `stageConvolveRight h ν c` at `x ∈ ℤ_p` applies `stage h ν` to the `x`-evaluated
outer stage of `comul K c`. -/
@[simp]
theorem eval_stageConvolveRight_apply (h : ℕ) (ν : LocallyAnalyticDistribution p K)
    (c : AnalyticStage p h K) (x : ℤ_[p]) :
    AnalyticStage.eval K (stageConvolveRight h ν c) x =
      stage h ν (AnalyticStage.eval K (comul K c) x) :=
  eval_compLeft_apply K (stage h ν) ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩ (comul K c) x

/-- Right convolution commutes with adjacent stage re-expansion. -/
theorem transition_stageConvolveRight (h : ℕ) (ν : LocallyAnalyticDistribution p K)
    (c : AnalyticStage p h K) :
    transition K (stageConvolveRight h ν c) = stageConvolveRight (h + 1) ν (transition K c) := by
  ext x
  rw [stageConvolveRight_apply_apply, comul_transition K, compLeft_apply,
    ← ContinuousLinearMap.comp_apply (stage (h + 1) ν) (transition K), stage_comp_transition]
  simpa only [stageConvolveRight, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.comp_apply,
    compLeft_apply] using
    DFunLike.congr_fun
      (transition_compLeft K (stage h ν) ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩ (comul K c)) x

/-- Right convolution commutes with multi-level stage re-expansion. -/
theorem transitionLE_stageConvolveRight {h k : ℕ} (hhk : h ≤ k)
    (ν : LocallyAnalyticDistribution p K) (c : AnalyticStage p h K) :
    transitionLE K hhk (stageConvolveRight h ν c) =
      stageConvolveRight k ν (transitionLE K hhk c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ K hhk, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ih, transition_stageConvolveRight]

/-- **Right convolution on locally analytic functions.** The stage endomorphisms
`stageConvolveRight h ν` descend along `transitionLE K` to a `K`-linear endomorphism of the
direct limit `LA(ℤ_p, K)`, bundled `K`-linearly in `ν`. -/
noncomputable def convolveRight :
    LocallyAnalyticDistribution p K →ₗ[K] LocallyAnalytic p K K →ₗ[K] LocallyAnalytic p K K where
  toFun ν := Module.DirectLimit.lift K ℕ _ _
    (fun h ↦ ofStage K h ∘ₗ (stageConvolveRight h ν).toLinearMap)
    fun _ _ hhk c ↦ by
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ← transitionLE_stageConvolveRight hhk ν c, ofStage_transitionLE]
  map_add' _ _ := Module.DirectLimit.hom_ext fun h ↦ LinearMap.ext fun c ↦ by simp [← ofStage_def]
  map_smul' _ _ := Module.DirectLimit.hom_ext fun h ↦ LinearMap.ext fun c ↦ by simp [← ofStage_def]

/-- On a stage representative `ofStage K h c`, `convolveRight ν` applies `stageConvolveRight h ν` at
level `h`. -/
@[simp]
theorem convolveRight_ofStage (ν : LocallyAnalyticDistribution p K) (h : ℕ)
    (c : AnalyticStage p h K) :
    convolveRight ν (ofStage K h c) = ofStage K h (stageConvolveRight h ν c) := by
  simp only [convolveRight, LinearMap.coe_mk, AddHom.coe_mk]
  exact lift_ofStage K _ _ h c

/-! ### Dirac distributions and the convolution algebra -/

/-- **Dirac locally analytic distribution.** Evaluation of a locally analytic function at `x ∈ ℤ_p`,
defined as the distribution attached to `AbstractMeasure.dirac K x`. -/
noncomputable def dirac (x : ℤ_[p]) : LocallyAnalyticDistribution p K :=
  ofMeasure (AbstractMeasure.dirac K x)

/-- The Dirac distribution at `x` evaluates a locally analytic function at `x`. -/
@[simp]
theorem coe_dirac_apply (x : ℤ_[p]) (f : LocallyAnalytic p K K) :
    (dirac (p := p) (K := K) x : Module.Dual K (LocallyAnalytic p K K)) f =
      LocallyAnalytic.eval K f x := by
  simp [dirac]

/-- On stage `h`, the Dirac distribution at `x` evaluates the stage series at `x`. -/
theorem stage_dirac_apply (h : ℕ) (x : ℤ_[p]) (c : AnalyticStage p h K) :
    stage h (dirac (p := p) (K := K) x) c = AnalyticStage.eval K c x := by
  simp

/-- The stage restriction of every Dirac distribution has operator norm `1`. -/
@[simp]
theorem norm_stage_dirac (h : ℕ) (x : ℤ_[p]) :
    ‖stage h (dirac (p := p) (K := K) x)‖ = 1 := by
  refine le_antisymm ?_ ?_
  · simpa [dirac] using stageSeminorm_ofMeasure_le (AbstractMeasure.dirac K x) h
  · let c : AnalyticStage p h K := single (PadicInt.toZModPow h x, 0) 1
    have hc : ‖c‖ ≤ 1 := by simp [c]
    have heval : stage h (dirac (p := p) (K := K) x) c = 1 := by
      rw [stage_dirac_apply, AnalyticStage.eval_apply, tsum_eq_single 0]
      · simp [c]
      · intro n hn
        simp [c, single_apply, hn]
    simpa [heval] using (stage h (dirac (p := p) (K := K) x)).unit_le_opNorm c hc

/-- Every Dirac distribution has stage seminorm `1` at every level `h`. -/
theorem stageSeminorm_dirac (h : ℕ) (x : ℤ_[p]) :
    stageSeminorm h (dirac (p := p) (K := K) x) = 1 := by
  rw [stageSeminorm_apply, norm_stage_dirac]

/-- Distinct points of `ℤ_p` determine distinct Dirac locally analytic distributions. -/
theorem dirac_injective : Function.Injective (dirac (p := p) (K := K)) := by
  intro x y hxy
  by_contra hne
  have hmeas : AbstractMeasure.dirac K x = AbstractMeasure.dirac K y := ofMeasure_injective hxy
  have h1 := TauCeti.AbstractMeasure.one_le_norm_dirac_sub (K := K) hne
  simp [hmeas] at h1
  linarith

/-- The multiplicative identity for convolution is the Dirac distribution at `0 ∈ ℤ_p`. -/
noncomputable instance instOne : One (LocallyAnalyticDistribution p K) where
  one := dirac 0

/-- `1` in `LocallyAnalyticDistribution p K` is `dirac 0`. -/
theorem one_def : (1 : LocallyAnalyticDistribution p K) = dirac 0 := (rfl)

/-- The Dirac distribution at `0` is the multiplicative identity `1`. -/
@[simp]
theorem dirac_zero : dirac (p := p) (K := K) 0 = 1 := (rfl)

/-- Applying `1` to a locally analytic function evaluates it at `0`. -/
@[simp]
theorem coe_one_apply (f : LocallyAnalytic p K K) :
    ((1 : LocallyAnalyticDistribution p K) : Module.Dual K (LocallyAnalytic p K K)) f =
      LocallyAnalytic.eval K f 0 :=
  coe_dirac_apply 0 f

/-- On stage `h`, `1 = dirac 0` reads the constant-term coefficient `c (0, 0)` on `pʰℤ_p`. -/
theorem stage_one_apply (h : ℕ) (c : AnalyticStage p h K) :
    stage h (1 : LocallyAnalyticDistribution p K) c = c (0, 0) := by
  simp

/-- The stage restriction of `1` has operator norm `1` at every level. -/
@[simp]
theorem norm_stage_one (h : ℕ) :
    ‖stage h (1 : LocallyAnalyticDistribution p K)‖ = 1 :=
  norm_stage_dirac h 0

/-- The identity distribution `1` has stage seminorm `1` at every level. -/
theorem stageSeminorm_one (h : ℕ) :
    stageSeminorm h (1 : LocallyAnalyticDistribution p K) = 1 := by
  rw [stageSeminorm_apply, norm_stage_one]

/-- Right convolution on stage `h` by `1` is the identity map. -/
@[simp]
theorem stageConvolveRight_one (h : ℕ) :
    stageConvolveRight h (1 : LocallyAnalyticDistribution p K) = ContinuousLinearMap.id K _ := by
  ext c x
  simp

/-- Right convolution on `LA(ℤ_p, K)` by `1` is the identity map. -/
@[simp]
theorem convolveRight_one :
    convolveRight (1 : LocallyAnalyticDistribution p K) = LinearMap.id :=
  Module.DirectLimit.hom_ext fun h ↦ LinearMap.ext fun c ↦ by simp [← ofStage_def]

/-- **Additive convolution of locally analytic distributions.** On the direct limit `LA(ℤ_p, K)`,
`μ * ν` applies `μ` after `convolveRight ν`; on each analytic stage `LA_h(K)` it restricts to
`stage h μ ∘L stageConvolveRight h ν`. -/
noncomputable instance instMul : Mul (LocallyAnalyticDistribution p K) where
  mul μ ν :=
    ⟨(μ : Module.Dual K (LocallyAnalytic p K K)) ∘ₗ convolveRight ν,
      mem_iff.mpr fun h ↦ by
        convert (stage h μ ∘L stageConvolveRight h ν).continuous using 1
        ext c
        simp⟩

/-- Evaluating `μ * ν` on a locally analytic function `f` applies `μ` to `convolveRight ν f`. -/
@[simp]
theorem coe_mul_apply (μ ν : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K) :
    ((μ * ν : LocallyAnalyticDistribution p K) : Module.Dual K (LocallyAnalytic p K K)) f =
      (μ : Module.Dual K (LocallyAnalytic p K K)) (convolveRight ν f) :=
  (rfl)

/-- On stage `h`, `μ * ν` restricts to `stage h μ ∘L stageConvolveRight h ν`. -/
@[simp]
theorem stage_mul (h : ℕ) (μ ν : LocallyAnalyticDistribution p K) :
    stage h (μ * ν) = stage h μ ∘L stageConvolveRight h ν := by
  ext c
  simp

/-- On stage `h`, `stage h (μ * ν) c` is the two-variable stage pairing `stagePair h μ ν` applied to
the uncurried comultiplication of `c`. -/
theorem stage_mul_eq_stagePair (h : ℕ) (μ ν : LocallyAnalyticDistribution p K)
    (c : AnalyticStage p h K) :
    stage h (μ * ν) c = stagePair h μ ν ((curryEquiv K K).symm (comul K c)) := by
  rw [stage_mul, ContinuousLinearMap.comp_apply, stage_stageConvolveRight_eq_stagePair]

/-- **Stage seminorms are submultiplicative under convolution.** -/
theorem stageSeminorm_mul_le (h : ℕ) (μ ν : LocallyAnalyticDistribution p K) :
    stageSeminorm h (μ * ν) ≤ stageSeminorm h μ * stageSeminorm h ν := by
  rw [stageSeminorm_apply, stage_mul, stageSeminorm_apply]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (opNorm_stageConvolveRight_le h ν) (norm_nonneg _))

/-- Right convolution on stage `h` converts convolution of distributions into composition. -/
@[simp]
theorem stageConvolveRight_mul (h : ℕ) (μ ν : LocallyAnalyticDistribution p K) :
    stageConvolveRight h (μ * ν) = stageConvolveRight h μ ∘L stageConvolveRight h ν := by
  ext c x
  have hcomul : comul K (stageConvolveRight h ν c) x = stageConvolveRight h ν (comul K c x) := by
    have hdef : stageConvolveRight h ν c =
        compLeft (stage h ν) ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩ (comul K c) := rfl
    have hassoc : comul K (comul K c) x = comul K (comul K c x) :=
      (DFunLike.congr_fun (comul_assoc K (hc := ⟨1, fun d ↦ by simp⟩) c).symm x).trans
        (compLeft_apply _ _ _ _)
    rw [hdef, comul_compLeft K, compLeft_apply, hassoc]
    simp [stageConvolveRight]
  simp [hcomul]

/-- Right convolution on `LA(ℤ_p, K)` converts convolution of distributions into composition. -/
@[simp]
theorem convolveRight_mul (μ ν : LocallyAnalyticDistribution p K) :
    convolveRight (μ * ν) = convolveRight μ ∘ₗ convolveRight ν :=
  Module.DirectLimit.hom_ext fun h ↦ LinearMap.ext fun c ↦ by simp [← ofStage_def]

/-- **Commutative ring structure on locally analytic distributions** under additive convolution,
preserving the underlying `Submodule.addCommGroup` definitional structure. -/
noncomputable instance instCommRing : CommRing (LocallyAnalyticDistribution p K) where
  left_distrib μ ν ρ := by ext h c; simp
  right_distrib μ ν ρ := by ext h c; simp
  zero_mul ν := by ext h c; simp
  mul_zero μ := by ext h c; simp
  mul_assoc μ ν ρ := by ext h; simp [ContinuousLinearMap.comp_assoc]
  one_mul μ := by ext h c; simp
  mul_one μ := by ext h c; simp
  mul_comm μ ν := by
    ext h c
    have hswap : congrLeft K K (Homeomorph.prodComm (ZMod (p ^ h) × ℕ) (ZMod (p ^ h) × ℕ))
        ((curryEquiv K K).symm (comul K c)) = (curryEquiv K K).symm (comul K c) := by
      ext ⟨x, y⟩
      simp [comul_comm K c y x]
    calc stage h (μ * ν) c
        = stagePair h μ ν ((curryEquiv K K).symm (comul K c)) :=
            stage_mul_eq_stagePair h μ ν c
      _ = (stagePair h μ ν ∘L
            (congrLeft K K (Homeomorph.prodComm (ZMod (p ^ h) × ℕ) (ZMod (p ^ h) × ℕ)) :
              C₀((ZMod (p ^ h) × ℕ) × (ZMod (p ^ h) × ℕ), K) →L[K] _))
            ((curryEquiv K K).symm (comul K c)) := by
            simp [hswap]
      _ = stagePair h ν μ ((curryEquiv K K).symm (comul K c)) := by
            rw [stagePair_comp_prodComm]
      _ = stage h (ν * μ) c := (stage_mul_eq_stagePair h ν μ c).symm

/-- **`K`-algebra structure on locally analytic distributions** under additive convolution,
preserving the underlying `Submodule.module` definitional structure. -/
noncomputable instance instAlgebra : Algebra K (LocallyAnalyticDistribution p K) :=
  Algebra.ofModule (fun a μ ν ↦ by ext h c; simp) (fun a μ ν ↦ by ext h c; simp)

-- Verify absence of additive-group and `K`-module diamonds against `Submodule` instances.
example : (instCommRing (p := p) (K := K)).toAddCommGroup =
    Submodule.addCommGroup (LocallyAnalyticDistribution p K) := by
  with_reducible_and_instances rfl

example : (instAlgebra (p := p) (K := K)).toModule =
    Submodule.module (LocallyAnalyticDistribution p K) := by
  with_reducible_and_instances rfl

/-- Stage seminorms satisfy `stageSeminorm h (μ ^ n) ≤ stageSeminorm h μ ^ n` for all `n : ℕ`. -/
theorem stageSeminorm_pow_le (h : ℕ) (μ : LocallyAnalyticDistribution p K) (n : ℕ) :
    stageSeminorm h (μ ^ n) ≤ stageSeminorm h μ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (stageSeminorm_mul_le h (μ ^ n) μ).trans
      (mul_le_mul_of_nonneg_right ih (apply_nonneg _ _))

/-- Convolution of Dirac distributions corresponds to addition in `ℤ_p`. -/
@[simp]
theorem dirac_add (x y : ℤ_[p]) :
    dirac (p := p) (K := K) (x + y) = dirac x * dirac y := by
  ext h c
  simp

/-- The Dirac map `Multiplicative ℤ_[p] →* LocallyAnalyticDistribution p K` as a monoid
homomorphism. -/
noncomputable def diracHom : Multiplicative ℤ_[p] →* LocallyAnalyticDistribution p K where
  toFun x := dirac x.toAdd
  map_one' := by simp
  map_mul' x y := by simp [toAdd_mul]

/-- `diracHom` sends `x : Multiplicative ℤ_[p]` to `dirac x.toAdd`. -/
@[simp]
theorem diracHom_apply (x : Multiplicative ℤ_[p]) :
    diracHom (p := p) (K := K) x = dirac x.toAdd :=
  (rfl)

/-! ### Comparison with native measure convolution -/

/-- **Embedding of the measure convolution algebra.** Transporting a measure in
`D(Multiplicative ℤ_[p], K)` along `Homeomorph.ofAdd.symm` and restricting to locally analytic
functions gives an injective `K`-algebra homomorphism into `LocallyAnalyticDistribution p K`. -/
noncomputable def ofMultiplicativeMeasure :
    D(Multiplicative ℤ_[p], K) →ₐ[K] LocallyAnalyticDistribution p K :=
  AlgHom.ofLinearMap
    (ofMeasure.comp (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm).toLinearMap)
    (by
      change ofMeasure (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm 1) = 1
      simp [AbstractMeasure.one_def, AbstractMeasure.coe_arrowCongrLeft, one_def, dirac])
    (fun μ ν ↦ by
      ext h c
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, stage_ofMeasure, stage_mul,
        ContinuousLinearMap.comp_apply, AbstractMeasure.coe_toCLMEquiv,
        AbstractMeasure.arrowCongrLeft_apply, AbstractMeasure.mul_apply]
      congr 1
      ext x
      rw [AbstractMeasure.convolveFunRight_apply, ContinuousMap.comp_apply,
        ContinuousMap.coe_ofClass, Homeomorph.ofAdd_symm_apply, eval_stageConvolveRight_apply,
        stage_ofMeasure, ContinuousLinearMap.comp_apply, AbstractMeasure.coe_toCLMEquiv,
        AbstractMeasure.arrowCongrLeft_apply]
      congr 1
      ext y
      simp [toAdd_mul])

/-- `ofMultiplicativeMeasure` agrees with `ofMeasure` after transporting along
`Homeomorph.ofAdd.symm`. -/
theorem ofMultiplicativeMeasure_eq_ofMeasure (μ : D(Multiplicative ℤ_[p], K)) :
    ofMultiplicativeMeasure (p := p) (K := K) μ =
      ofMeasure (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm μ) :=
  (rfl)

/-- `ofMultiplicativeMeasure μ` integrates evaluated locally analytic functions transported to
`Multiplicative ℤ_[p]`. -/
@[simp]
theorem coe_ofMultiplicativeMeasure_apply (μ : D(Multiplicative ℤ_[p], K))
    (f : LocallyAnalytic p K K) :
    (ofMultiplicativeMeasure (p := p) (K := K) μ :
      Module.Dual K (LocallyAnalytic p K K)) f =
      μ ((LocallyAnalytic.eval K f).comp
        ((Homeomorph.ofAdd (X := ℤ_[p])).symm : C(Multiplicative ℤ_[p], ℤ_[p]))) := by
  simp [ofMultiplicativeMeasure_eq_ofMeasure]

/-- On stage `h`, `ofMultiplicativeMeasure μ` integrates evaluated stage series transported to
`Multiplicative ℤ_[p]`. -/
theorem stage_ofMultiplicativeMeasure_apply (h : ℕ) (μ : D(Multiplicative ℤ_[p], K))
    (c : AnalyticStage p h K) :
    stage h (ofMultiplicativeMeasure (p := p) (K := K) μ) c =
      μ ((AnalyticStage.eval K c).comp
        ((Homeomorph.ofAdd (X := ℤ_[p])).symm : C(Multiplicative ℤ_[p], ℤ_[p]))) := by
  simp

/-- `ofMultiplicativeMeasure` sends a Dirac measure on `Multiplicative ℤ_[p]` to the corresponding
Dirac locally analytic distribution. -/
@[simp]
theorem ofMultiplicativeMeasure_dirac (x : Multiplicative ℤ_[p]) :
    ofMultiplicativeMeasure (p := p) (K := K) (AbstractMeasure.dirac K x) = dirac x.toAdd := by
  simp [ofMultiplicativeMeasure_eq_ofMeasure, AbstractMeasure.coe_arrowCongrLeft, dirac]

/-- Precomposing `ofMultiplicativeMeasure` with `AbstractMeasure.diracHom` recovers `diracHom`. -/
@[simp]
theorem ofMultiplicativeMeasure_comp_diracHom :
    (ofMultiplicativeMeasure (p := p) (K := K) :
      D(Multiplicative ℤ_[p], K) →* LocallyAnalyticDistribution p K).comp
        AbstractMeasure.diracHom = diracHom := by
  ext x
  simp

/-- The measure-algebra embedding into locally analytic distributions is injective. -/
theorem ofMultiplicativeMeasure_injective :
    Function.Injective (ofMultiplicativeMeasure (p := p) (K := K)) :=
  ofMeasure_injective.comp (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm).injective

/-- Every stage seminorm of `algebraMap K (LocallyAnalyticDistribution p K) a` equals `‖a‖`. -/
theorem stageSeminorm_algebraMap (h : ℕ) (a : K) :
    stageSeminorm h (algebraMap K (LocallyAnalyticDistribution p K) a) = ‖a‖ := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul_eq_mul, stageSeminorm_one, mul_one]

/-- Every stage seminorm of `ofMultiplicativeMeasure μ` is bounded by the operator norm of `μ`. -/
theorem stageSeminorm_ofMultiplicativeMeasure_le (μ : D(Multiplicative ℤ_[p], K)) (h : ℕ) :
    stageSeminorm h (ofMultiplicativeMeasure (p := p) (K := K) μ) ≤
      ‖AbstractMeasure.toCLMEquiv μ‖ := by
  rw [stageSeminorm_apply]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun c ↦ ?_
  rw [stage_ofMultiplicativeMeasure_apply, ← AbstractMeasure.coe_toCLMEquiv]
  refine ((AbstractMeasure.toCLMEquiv μ).le_opNorm _).trans ?_
  gcongr
  refine ((ContinuousMap.norm_le _ (norm_nonneg (AnalyticStage.eval K c))).mpr fun x ↦ ?_).trans
    (norm_eval_le K c)
  exact (AnalyticStage.eval K c).norm_coe_le_norm _

end LocallyAnalyticDistribution

end TauCeti
