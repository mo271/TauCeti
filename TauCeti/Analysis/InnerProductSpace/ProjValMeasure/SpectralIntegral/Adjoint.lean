/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.SpectralIntegral.Basic
public import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# Adjoint, closedness, graph cores, and self-adjointness of unbounded spectral integrals

Let `P` be a normalized projection-valued measure on a measurable space `X` acting on a complex
Hilbert space `H`, and let `f : X → ℂ` be measurable. Continuing from
`TauCeti.Analysis.InnerProductSpace.ProjValMeasure.SpectralIntegral.Basic`, this file proves the
unbounded Hilbert-space operator properties of `P.spectralIntegral f hf`:

* **Hilbert adjoint (`adjoint_spectralIntegral`, `adjoint_spectralIntegral_apply`):** the Hilbert
  adjoint of `P.spectralIntegral f hf` is
  `P.spectralIntegral (star f) (continuous_star.measurable.comp hf)`, with the same maximal
  second-moment domain (`adjoint_spectralIntegral_domain`) and conjugate matrix elements
  (`inner_adjoint_spectralIntegral_apply`).
* **Normality (`norm_adjoint_spectralIntegral_apply`):** for every vector in the common domain,
  `‖(P.spectralIntegral f hf).adjoint x‖ = ‖P.spectralIntegral f hf y‖` when `(x : H) = y`.
* **Closedness and spectral projection cores (`isClosed_spectralIntegral`,
  `spectralIntegral_hasCore_iSup_range_proj_iff_of_eventually_mem`,
  `spectralIntegral_hasCore_iSup_range_proj`):** `P.spectralIntegral f hf` is closed, and the
  supremum of the ranges of any `P.ae`-exhausting countably generated family of spectral
  projections into the domain (in particular `P({t | ‖f t‖ ≤ n})`) is a graph core.
* **Self-adjointness (`isSelfAdjoint_spectralIntegral_iff`):** `P.spectralIntegral f hf` is
  self-adjoint if and only if `f` is `P`-almost everywhere real-valued (`star (f t) = f t`).
* **Existence and uniqueness package (`existsUnique_spectralIntegral`):** there is a unique partial
  linear operator `T : H →ₗ.[ℂ] H` satisfying the full conjunction of having the second-moment
  domain and polarized matrix elements of `f`, being densely defined and closed, satisfying the
  second-moment norm identity, and having Hilbert adjoint on the same domain with the polarized
  matrix elements of `star f` (for characterization by domain and matrix elements alone, see
  `eq_spectralIntegral_iff`).

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS GSM 99, 2009, Section 3.1,
  Theorem 3.2 and equations (3.25)–(3.29).
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.3, Theorem 4.16.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace TauCeti.ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Hilbert adjoint and normality -/

private theorem setLIntegral_norm_le_adjoint (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (y : (P.spectralIntegral f hf).adjoint.domain) (n : ℕ) :
    (∫⁻ t in {s | ‖f s‖ ≤ (n : ℝ)}, ‖f t‖ₑ ^ 2 ∂(P.diag y)) ≤
      ‖(P.spectralIntegral f hf).adjoint y‖ₑ ^ 2 := by
  set B : Set X := {s | ‖f s‖ ≤ (n : ℝ)}
  have hB : MeasurableSet B := measurableSet_le hf.norm measurable_const
  let fn := BoundedBorelFunction.cutoff f hf n
  let z : H := (P.spectralIntegral f hf).adjoint y
  have hz : P.proj B hB z = P.integral (star fn) y := by
    refine ext_inner_right ℂ fun w => ?_
    have hmem : P.proj B hB w ∈ (P.spectralIntegral f hf).domain :=
      (P.spectralIntegral_domain f hf).ge
        (P.proj_apply_mem_spectralIntegralDomain hB (M := n)
          (Eventually.of_forall fun _ ht => ht) w)
    calc ⟪P.proj B hB z, w⟫_ℂ
        = ⟪z, P.proj B hB w⟫_ℂ := (P.isSelfAdjoint_proj B hB).isSymmetric z w
      _ = ⟪(y : H), P.spectralIntegral f hf ⟨P.proj B hB w, hmem⟩⟫_ℂ :=
            (LinearPMap.adjoint_isFormalAdjoint (P.dense_spectralIntegral_domain f hf))
              y ⟨P.proj B hB w, hmem⟩
      _ = ⟪(y : H), P.integral fn w⟫_ℂ := by rw [P.spectralIntegral_apply_proj_norm_le]
      _ = ⟪P.integral (star fn) y, w⟫_ℂ := by
            rw [← ContinuousLinearMap.adjoint_inner_left,
              ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  have henorm : ∫⁻ t, ‖(star fn) t‖ₑ ^ 2 ∂(P.diag y) = ‖P.integral (star fn) y‖ₑ ^ 2 := by
    let g := star fn
    have hy : (y : H) ∈ (P.spectralIntegral g g.measurable).domain := by simp
    rw [show star fn = g from rfl, ← P.enorm_sq_spectralIntegral_apply g g.measurable ⟨y, hy⟩,
      P.spectralIntegral_boundedBorelFunction_apply g ⟨y, hy⟩]
  rw [← lintegral_indicator hB]
  refine (lintegral_congr fun t => ?_).le.trans (henorm.trans_le ?_)
  · by_cases ht : t ∈ B <;> simp [fn, B] at ht ⊢ <;> simp [ht]
  · rw [← hz, ← ofReal_norm, ← ofReal_norm]
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (P.norm_proj_apply_le B hB z)) 2

/-- **Hilbert adjoint** of the unbounded spectral integral: the adjoint of `P.spectralIntegral f hf`
is the spectral integral of the complex-conjugate symbol `star f`. -/
@[simp]
theorem adjoint_spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    (P.spectralIntegral f hf).adjoint =
      P.spectralIntegral (star f) (continuous_star.measurable.comp hf) := by
  let hfs : Measurable (star f) := continuous_star.measurable.comp hf
  have hdense := P.dense_spectralIntegral_domain f hf
  have hformal : (P.spectralIntegral f hf).IsFormalAdjoint (P.spectralIntegral (star f) hfs) :=
    fun x y => P.inner_spectralIntegral_star hf x y
  have hle := hformal.le_adjoint hdense
  have hdom :
      (P.spectralIntegral f hf).adjoint.domain ≤ (P.spectralIntegral (star f) hfs).domain := by
    intro y hy
    rw [P.spectralIntegral_domain, P.mem_spectralIntegralDomain_iff]
    have hU : (⋃ n : ℕ, {s | ‖f s‖ ≤ (n : ℝ)}) = Set.univ :=
      Set.eq_univ_of_forall fun t => Set.mem_iUnion.2 (exists_nat_ge ‖f t‖)
    have hdir : Directed (· ⊆ ·) (fun n : ℕ => {s | ‖f s‖ ≤ (n : ℝ)}) :=
      Monotone.directed_le fun m n hmn _ ht =>
        Set.mem_ofPred.2 ((Set.mem_ofPred.1 ht).trans (Nat.cast_le.2 hmn))
    calc (∫⁻ t, ‖(star f) t‖ₑ ^ 2 ∂(P.diag y))
        = ∫⁻ t in ⋃ n : ℕ, {s | ‖f s‖ ≤ (n : ℝ)}, ‖f t‖ₑ ^ 2 ∂(P.diag y) := by
            rw [hU, Measure.restrict_univ]
            exact lintegral_congr fun t => by simp
      _ = ⨆ n : ℕ, ∫⁻ t in {s | ‖f s‖ ≤ (n : ℝ)}, ‖f t‖ₑ ^ 2 ∂(P.diag y) :=
            setLIntegral_iUnion_of_directed _ hdir
      _ ≤ ‖(P.spectralIntegral f hf).adjoint ⟨y, hy⟩‖ₑ ^ 2 :=
            iSup_le (setLIntegral_norm_le_adjoint P hf ⟨y, hy⟩)
      _ < ∞ := ENNReal.pow_lt_top eNorm_lt_top
  exact (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

/-- The Hilbert adjoint of `P.spectralIntegral f hf` has the same domain as
`P.spectralIntegral f hf`. -/
theorem adjoint_spectralIntegral_domain (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    (P.spectralIntegral f hf).adjoint.domain = (P.spectralIntegral f hf).domain := by
  simp

/-- Pointwise evaluation of `(P.spectralIntegral f hf).adjoint` as `P.spectralIntegral (star f)`. -/
theorem adjoint_spectralIntegral_apply (P : ProjValMeasure X H) {f : X → ℂ} (hf : Measurable f)
    {hstar : Measurable (star f)}
    ⦃x : (P.spectralIntegral f hf).adjoint.domain⦄
    ⦃y : (P.spectralIntegral (star f) hstar).domain⦄ (hxy : (x : H) = y) :
    (P.spectralIntegral f hf).adjoint x = P.spectralIntegral (star f) hstar y := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  dsimp only at hxy
  subst hxy
  exact LinearPMap.congr_fun (P.adjoint_spectralIntegral f hf) hx hy

/-- **Adjoint matrix-element identity**: for `x` in the adjoint domain and every `y : H`,
`⟪y, (P.spectralIntegral f hf).adjoint x⟫_ℂ` is the polarized integral of `t ↦ star (f t)`. -/
theorem inner_adjoint_spectralIntegral_apply (P : ProjValMeasure X H) (f : X → ℂ)
    (hf : Measurable f) (x : (P.spectralIntegral f hf).adjoint.domain) (y : H) :
    ⟪y, (P.spectralIntegral f hf).adjoint x⟫_ℂ =
      ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x] := by
  have hx' : (x : H) ∈ (P.spectralIntegral (star f) (continuous_star.measurable.comp hf)).domain :=
    by simpa using x.2
  rw [P.adjoint_spectralIntegral_apply hf (y := ⟨x, hx'⟩) rfl]
  exact P.inner_spectralIntegral_apply (star f) (continuous_star.measurable.comp hf) ⟨x, hx'⟩ y

/-- **Normality** of the unbounded spectral integral: on the common domain
`D(T†) = D(T)`, the operator and its Hilbert adjoint have equal norms on every vector. -/
theorem norm_adjoint_spectralIntegral_apply (P : ProjValMeasure X H) (f : X → ℂ)
    (hf : Measurable f) ⦃x : (P.spectralIntegral f hf).adjoint.domain⦄
    ⦃y : (P.spectralIntegral f hf).domain⦄ (hxy : (x : H) = y) :
    ‖(P.spectralIntegral f hf).adjoint x‖ = ‖P.spectralIntegral f hf y‖ := by
  have hx' : (x : H) ∈ (P.spectralIntegral (star f) (continuous_star.measurable.comp hf)).domain :=
    by simpa using x.2
  rw [P.adjoint_spectralIntegral_apply hf (y := ⟨x, hx'⟩) rfl,
    P.norm_spectralIntegral_apply, P.norm_spectralIntegral_apply]
  simp [hxy]

/-! ### Closedness, spectral cutoff cores, self-adjointness, and uniqueness package -/

/-- Every unbounded spectral integral `P.spectralIntegral f hf` is a closed operator. -/
theorem isClosed_spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    (P.spectralIntegral f hf).IsClosed := by
  have hstar : Measurable (star f) := continuous_star.measurable.comp hf
  have hadj := P.adjoint_spectralIntegral (star f) hstar
  have heq : P.spectralIntegral (star (star f)) (continuous_star.measurable.comp hstar) =
      P.spectralIntegral f hf :=
    P.spectralIntegral_congr_ae _ hf (Eventually.of_forall fun t => star_star (f t))
  rw [← heq, ← hadj]
  exact LinearPMap.adjoint_isClosed (P.dense_spectralIntegral_domain (star f) hstar)

/-- For any family of measurable sets `B i` along a nontrivial countably generated filter `l` that
`P`-almost everywhere eventually contains every point, the supremum of the ranges of
`P.proj (B i) (hB i)` is a graph core for `P.spectralIntegral f hf` if and only if each projection
range lies in the domain. -/
theorem spectralIntegral_hasCore_iSup_range_proj_iff_of_eventually_mem (P : ProjValMeasure X H)
    {f : X → ℂ} (hf : Measurable f) {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot]
    {B : ι → Set X} (hB : ∀ i, MeasurableSet (B i))
    (h : ∀ᶠ t in P.ae, ∀ᶠ i in l, t ∈ B i) :
    (P.spectralIntegral f hf).HasCore (⨆ i, (P.proj (B i) (hB i)).range) ↔
      ∀ i, (P.proj (B i) (hB i)).range ≤ (P.spectralIntegral f hf).domain := by
  refine ⟨fun hcore => iSup_le_iff.1 hcore.1, fun hdom => ?_⟩
  let S : Submodule ℂ H := ⨆ i, (P.proj (B i) (hB i)).range
  have hS : S ≤ (P.spectralIntegral f hf).domain := iSup_le hdom
  rw [(P.isClosed_spectralIntegral f hf).hasCore_iff_graph_subset_closure hS]
  intro p hp
  obtain ⟨x, hx1, hx2⟩ := (P.spectralIntegral f hf).mem_graph_iff.1 hp
  rw [show p = ((x : H), P.spectralIntegral f hf x) from Prod.ext hx1.symm hx2.symm]
  have hlim := (P.tendsto_proj_of_eventually_mem hB h x).prodMk_nhds
    (P.tendsto_spectralIntegral_proj_of_eventually_mem hf hB h x)
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun i => ?_)
  let u := P.proj (B i) (hB i) x
  have huS : u ∈ S := Submodule.mem_iSup_of_mem i ⟨x, rfl⟩
  have huT : u ∈ (P.spectralIntegral f hf).domain :=
    (P.spectralIntegral_domain f hf).ge
      (P.proj_apply_mem_spectralIntegralDomain_of_mem (hB i)
        ((P.spectralIntegral_domain f hf).le x.2))
  let ui : ↥(S ⊓ (P.spectralIntegral f hf).domain) := ⟨u, ⟨huS, huT⟩⟩
  have hdom_apply : (P.spectralIntegral f hf).domRestrict S ui =
      P.spectralIntegral f hf ⟨u, huT⟩ :=
    LinearPMap.domRestrict_apply (x := ui) (y := ⟨u, huT⟩) rfl
  rw [← hdom_apply]
  exact ((P.spectralIntegral f hf).domRestrict S).mem_graph ui

/-- The supremum of the ranges of the spectral cutoff projections `P({t | ‖f t‖ ≤ n})` is a graph
core for `P.spectralIntegral f hf`. -/
theorem spectralIntegral_hasCore_iSup_range_proj (P : ProjValMeasure X H) (f : X → ℂ)
    (hf : Measurable f) :
    (P.spectralIntegral f hf).HasCore
      (⨆ n : ℕ, (P.proj {t | ‖f t‖ ≤ n} (measurableSet_le hf.norm measurable_const)).range) := by
  refine (P.spectralIntegral_hasCore_iSup_range_proj_iff_of_eventually_mem (l := atTop) hf
    (fun _ => measurableSet_le hf.norm measurable_const)
    (Eventually.of_forall fun t => tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖f t‖)).2 ?_
  rintro n _ ⟨w, rfl⟩
  rw [P.spectralIntegral_domain]
  exact P.proj_apply_mem_spectralIntegralDomain (measurableSet_le hf.norm measurable_const)
    (M := n) (Eventually.of_forall fun _ ht => ht) w

/-- **Self-adjointness criterion** for the unbounded spectral integral: `P.spectralIntegral f hf`
is self-adjoint if and only if `f` is `P`-almost everywhere real-valued (`star (f t) = f t`). -/
theorem isSelfAdjoint_spectralIntegral_iff (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) :
    IsSelfAdjoint (P.spectralIntegral f hf) ↔ ∀ᶠ t in P.ae, star (f t) = f t := by
  rw [LinearPMap.isSelfAdjoint_def, P.adjoint_spectralIntegral f hf,
    P.spectralIntegral_eq_spectralIntegral_iff]
  simp only [Filter.EventuallyEq, Pi.star_apply]

/-- A measurable symbol that is `P`-almost everywhere real-valued defines a self-adjoint unbounded
spectral integral. -/
theorem isSelfAdjoint_spectralIntegral_of_ae (P : ProjValMeasure X H) {f : X → ℂ}
    (hf : Measurable f) (h : ∀ᶠ t in P.ae, star (f t) = f t) :
    IsSelfAdjoint (P.spectralIntegral f hf) :=
  (P.isSelfAdjoint_spectralIntegral_iff hf).2 h

/-- **Existence and uniqueness** of the unbounded spectral integral: for every normalized
projection-valued measure `P` on a measurable space `X` and every measurable symbol `f : X → ℂ`,
there is a unique partial linear operator `T : H →ₗ.[ℂ] H` satisfying the full conjunction of
having the second-moment domain `{x | ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞}` and the polarized matrix
elements of `f`, being densely defined and closed, satisfying the second-moment norm identity, and
having Hilbert adjoint on the same domain with the polarized matrix elements of `star f`. For
uniqueness from the domain and polarized matrix elements alone, see `eq_spectralIntegral_iff`. -/
theorem existsUnique_spectralIntegral (P : ProjValMeasure X H) (f : X → ℂ) (hf : Measurable f) :
    ∃! T : H →ₗ.[ℂ] H,
      (∀ x : H, x ∈ T.domain ↔ ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag x) < ∞) ∧
      (∀ (x : T.domain) (y : H),
        ⟪y, T x⟫_ℂ = ∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) ∧
      Dense (T.domain : Set H) ∧ T.IsClosed ∧
      (∀ x : T.domain, ‖T x‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂(P.diag x)) ∧
      T.adjoint.domain = T.domain ∧
      (∀ (x : T.adjoint.domain) (y : H),
        ⟪y, T.adjoint x⟫_ℂ =
          ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure y x]) := by
  refine ⟨P.spectralIntegral f hf,
    ⟨fun x => by rw [P.spectralIntegral_domain, P.mem_spectralIntegralDomain_iff],
      P.inner_spectralIntegral_apply f hf,
      P.dense_spectralIntegral_domain f hf,
      P.isClosed_spectralIntegral f hf,
      P.norm_sq_spectralIntegral_apply f hf,
      P.adjoint_spectralIntegral_domain f hf,
      P.inner_adjoint_spectralIntegral_apply f hf⟩, ?_⟩
  rintro T ⟨hdom, hinner, -⟩
  exact (P.eq_spectralIntegral_iff hf T).2 ⟨hdom, hinner⟩

end TauCeti.ProjValMeasure
