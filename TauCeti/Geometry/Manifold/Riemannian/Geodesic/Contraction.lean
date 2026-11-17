/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Convex
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Smooth radial geodesic contractions

On a normal ball `exp_q '' B(0, r)` centred at `q` in a Riemannian manifold, the raw radial
geodesic homotopy `geodesicContractionRaw I M q r (s, x) = exp_q (s • log_q x)` is smooth on its
natural open domain `geodesicContractionDomain I M q r`, which contains `[0, 1] × W` for any
subset `W ⊆ exp_q '' B(0, r)`.

Reparametrizing time by `Real.smoothTransition` produces a globally defined smooth homotopy
`geodesicContraction I M q r (t, x) = exp_q (Real.smoothTransition t • log_q x)` on `ℝ × W`
that equals `q` for `t ≤ 0`, equals `x` for `1 ≤ t`, and fixes `q` at all times. When `W` is
strongly geodesically convex (`TauCeti.Manifold.IsStronglyGeodesicallyConvex`) and open, this
restricts to a globally smooth self-map `geodesicContractionOpens : ℝ × W → W`.

## Main definitions and results

* `TauCeti.Manifold.geodesicContractionDomain`, `TauCeti.Manifold.geodesicContractionRaw`: the raw
  radial geodesic contraction and its natural open domain.
* `TauCeti.Manifold.isOpen_geodesicContractionDomain`,
  `TauCeti.Manifold.Icc_prod_subset_geodesicContractionDomain`,
  `TauCeti.Manifold.contMDiffOn_geodesicContractionRaw`,
  `TauCeti.Manifold.mapsTo_geodesicContractionRaw`: domain openness, smoothness, and invariance of
  strongly geodesically convex sets.
* `TauCeti.Manifold.geodesicContraction`, `TauCeti.Manifold.contMDiffOn_geodesicContraction`,
  `TauCeti.Manifold.mapsTo_geodesicContraction`: the `Real.smoothTransition`-reparametrized radial
  geodesic contraction on `ℝ × W`.
* `TauCeti.Manifold.geodesicContractionOpens`,
  `TauCeti.Manifold.contMDiff_geodesicContractionOpens`: globally smooth contraction `ℝ × W → W`
  on an open submanifold `W : TopologicalSpace.Opens M`.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Springer GTM 82, 1982, §5.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018, Ch. 6.
-/

public section

noncomputable section

open Bundle Manifold Metric Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

section Basic

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The natural open domain of the raw radial geodesic homotopy `(s, x) ↦ exp_q (s • log_q x)`
centred at `q` with normal ball radius `r`: pairs `(s, x)` with `x ∈ exp_q '' B(0, r)` and
`s • log_q x ∈ expDomain I M q`. -/
def geodesicContractionDomain (q : M) (r : ℝ) : Set (ℝ × M) :=
  {p : ℝ × M | p.2 ∈ riemannianExp I M q '' Metric.ball 0 r ∧
    p.1 • riemannianLog I M q (Metric.ball 0 r) p.2 ∈ expDomain I M q}

variable (I M) in
/-- The raw radial geodesic homotopy centred at `q` relative to the normal ball `Metric.ball 0 r`:
`H(s, x) = exp_q (s • log_q x)`. -/
def geodesicContractionRaw (q : M) (r : ℝ) (p : ℝ × M) : M :=
  riemannianExp I M q (p.1 • riemannianLog I M q (Metric.ball 0 r) p.2)

/-- When `W ⊆ exp_q '' B(0, r)` for a normal ball at `q`, the cylinder `[0, 1] × W` lies in the
natural open domain of the raw radial geodesic contraction. -/
theorem Icc_prod_subset_geodesicContractionDomain {q : M} {r : ℝ} {W : Set M}
    (hN : IsNormalDomain I M q (Metric.ball 0 r))
    (hWr : W ⊆ riemannianExp I M q '' Metric.ball 0 r) :
    Icc (0 : ℝ) 1 ×ˢ W ⊆ geodesicContractionDomain I M q r := by
  rintro ⟨s, x⟩ ⟨hs, hx⟩
  exact ⟨hWr hx, hN.subset_expDomain (hN.smul_mem (riemannianLog_mem (hWr hx)) hs.1 hs.2)⟩

/-- At time `1`, the raw radial geodesic contraction is the identity on the normal ball. -/
theorem geodesicContractionRaw_one {q : M} {r : ℝ} {x : M}
    (hx : x ∈ riemannianExp I M q '' Metric.ball 0 r) :
    geodesicContractionRaw I M q r (1, x) = x := by
  simp [geodesicContractionRaw, riemannianExp_riemannianLog hx]

variable (I M) in
/-- The globally defined smooth reparametrization of the radial geodesic contraction via
`Real.smoothTransition`: `(t, x) ↦ exp_q (Real.smoothTransition t • log_q x)`. -/
def geodesicContraction (q : M) (r : ℝ) (p : ℝ × M) : M :=
  geodesicContractionRaw I M q r (Real.smoothTransition p.1, p.2)

/-- For `1 ≤ t`, the reparametrized radial geodesic contraction is the identity on the normal
ball. -/
theorem geodesicContraction_of_one_le {q : M} {r : ℝ} {t : ℝ} (ht : 1 ≤ t) {x : M}
    (hx : x ∈ riemannianExp I M q '' Metric.ball 0 r) :
    geodesicContraction I M q r (t, x) = x := by
  simp [geodesicContraction, Real.smoothTransition.one_of_one_le ht, geodesicContractionRaw_one hx]

/-- At time `1`, the reparametrized radial geodesic contraction is the identity on the normal
ball. -/
theorem geodesicContraction_one {q : M} {r : ℝ} {x : M}
    (hx : x ∈ riemannianExp I M q '' Metric.ball 0 r) :
    geodesicContraction I M q r (1, x) = x :=
  geodesicContraction_of_one_le le_rfl hx

section Boundaryless

variable [I.Boundaryless] [T2Space M]

/-- The natural domain of the raw radial geodesic contraction is open. -/
theorem isOpen_geodesicContractionDomain {q : M} {r : ℝ}
    (hN : IsNormalDomain I M q (Metric.ball 0 r)) :
    IsOpen (geodesicContractionDomain I M q r) := by
  have hcont : ContinuousOn (fun p : ℝ × M ↦ p.1 • riemannianLog I M q (Metric.ball 0 r) p.2)
      (univ ×ˢ (riemannianExp I M q '' Metric.ball 0 r)) :=
    continuousOn_fst.smul (hN.continuousOn_riemannianLog.comp continuousOn_snd
      (fun _ hp ↦ hp.2))
  have hopen := hcont.isOpen_inter_preimage (isOpen_univ.prod hN.isOpen_image)
    (isOpen_expDomain (I := I) (M := M) q)
  convert hopen using 1
  ext ⟨s, x⟩
  simp [geodesicContractionDomain]

/-- The raw radial geodesic contraction is smooth on its natural open domain. -/
theorem contMDiffOn_geodesicContractionRaw {q : M} {r : ℝ}
    (hN : IsNormalDomain I M q (Metric.ball 0 r)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (geodesicContractionRaw I M q r)
      (geodesicContractionDomain I M q r) := by
  rintro ⟨s, x⟩ ⟨hx, hsx⟩
  have hlog : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, TangentSpace I q) ∞
      (fun p : ℝ × M ↦ riemannianLog I M q (Metric.ball 0 r) p.2) (s, x) :=
    (hN.contMDiffOn_riemannianLog.contMDiffAt (hN.isOpen_image.mem_nhds hx)).comp (s, x)
      contMDiffAt_snd
  have hsmul : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, TangentSpace I q) ∞
      (fun p : ℝ × M ↦ p.1 • riemannianLog I M q (Metric.ball 0 r) p.2) (s, x) :=
    contMDiffAt_fst.smul hlog
  have hexp : ContMDiffAt 𝓘(ℝ, TangentSpace I q) I ∞ (riemannianExp I M q)
      (s • riemannianLog I M q (Metric.ball 0 r) x) :=
    (contMDiffOn_riemannianExp (I := I) (M := M) q).contMDiffAt
      ((isOpen_expDomain (I := I) (M := M) q).mem_nhds hsx)
  exact (hexp.comp (s, x) hsmul).contMDiffWithinAt

/-- At time `0`, the raw radial geodesic contraction collapses every point to the centre `q`. -/
@[simp]
theorem geodesicContractionRaw_zero (q : M) (r : ℝ) (x : M) :
    geodesicContractionRaw I M q r (0, x) = q := by
  simp [geodesicContractionRaw]

/-- The raw radial geodesic contraction fixes the centre `q` at all times. -/
theorem geodesicContractionRaw_centre {q : M} {r : ℝ}
    (hN : IsNormalDomain I M q (Metric.ball 0 r)) (s : ℝ) :
    geodesicContractionRaw I M q r (s, q) = q := by
  simp [geodesicContractionRaw, hN.riemannianLog_self]

/-- The reparametrized radial geodesic contraction is smooth on `ℝ × W` whenever `W` lies in the
normal ball `exp_q '' B(0, r)`. -/
theorem contMDiffOn_geodesicContraction {q : M} {r : ℝ} {W : Set M}
    (hN : IsNormalDomain I M q (Metric.ball 0 r))
    (hWr : W ⊆ riemannianExp I M q '' Metric.ball 0 r) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (geodesicContraction I M q r) (univ ×ˢ W) := by
  have hstep : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M ↦ (Real.smoothTransition p.1, p.2)) :=
    ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).contMDiff.comp contMDiff_fst).prodMk
      contMDiff_snd
  refine (contMDiffOn_geodesicContractionRaw hN).comp hstep.contMDiffOn ?_
  rintro ⟨t, x⟩ ⟨_, hx⟩
  exact Icc_prod_subset_geodesicContractionDomain hN hWr
    ⟨⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩, hx⟩

/-- For `t ≤ 0`, the reparametrized radial geodesic contraction takes the constant value `q`. -/
theorem geodesicContraction_of_nonpos {q : M} {r : ℝ} {t : ℝ} (ht : t ≤ 0) (x : M) :
    geodesicContraction I M q r (t, x) = q := by
  simp [geodesicContraction, Real.smoothTransition.zero_of_nonpos ht]

/-- At time `0`, the reparametrized radial geodesic contraction collapses every point to `q`. -/
@[simp]
theorem geodesicContraction_zero (q : M) (r : ℝ) (x : M) :
    geodesicContraction I M q r (0, x) = q :=
  geodesicContraction_of_nonpos le_rfl x

/-- The reparametrized radial geodesic contraction fixes the centre `q` at all times. -/
theorem geodesicContraction_centre {q : M} {r : ℝ}
    (hN : IsNormalDomain I M q (Metric.ball 0 r)) (t : ℝ) :
    geodesicContraction I M q r (t, q) = q :=
  geodesicContractionRaw_centre hN (Real.smoothTransition t)

end Boundaryless

end Basic

section StronglyConvex

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- On a strongly geodesically convex set `W` inside a normal ball `exp_q '' B(0, r)` at `q ∈ W`,
the raw radial geodesic contraction maps `[0, 1] × W` into `W`. -/
theorem mapsTo_geodesicContractionRaw {q : M} {r : ℝ} {W : Set M}
    (hW : IsStronglyGeodesicallyConvex I M W) (hq : q ∈ W)
    (hN : IsNormalDomain I M q (Metric.ball 0 r))
    (hWr : W ⊆ riemannianExp I M q '' Metric.ball 0 r) :
    MapsTo (geodesicContractionRaw I M q r) (Icc (0 : ℝ) 1 ×ˢ W) W := by
  rintro ⟨s, x⟩ ⟨hs, hx⟩
  exact hW.mapsTo_riemannianExp_smul_riemannianLog hq hN hWr hx hs

/-- The reparametrized radial geodesic contraction maps `ℝ × W` into `W` for any strongly
geodesically convex set `W` inside a normal ball `exp_q '' B(0, r)` about `q ∈ W`. -/
theorem mapsTo_geodesicContraction {q : M} {r : ℝ} {W : Set M}
    (hW : IsStronglyGeodesicallyConvex I M W) (hq : q ∈ W)
    (hN : IsNormalDomain I M q (Metric.ball 0 r))
    (hWr : W ⊆ riemannianExp I M q '' Metric.ball 0 r) :
    MapsTo (geodesicContraction I M q r) (univ ×ˢ W) W := by
  rintro ⟨t, x⟩ ⟨_, hx⟩
  exact mapsTo_geodesicContractionRaw hW hq hN hWr
    ⟨⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩, hx⟩

/-- The globally smooth reparametrized geodesic contraction packaged as a self-map `ℝ × W → W`
of an open strongly geodesically convex subset `W` lying in a normal ball `exp_q '' B(0, r)`. -/
def geodesicContractionOpens {W : TopologicalSpace.Opens M}
    (hW : IsStronglyGeodesicallyConvex I M (W : Set M)) (q : W) {r : ℝ}
    (hN : IsNormalDomain I M q.1 (Metric.ball 0 r))
    (hWr : (W : Set M) ⊆ riemannianExp I M q.1 '' Metric.ball 0 r)
    (p : ℝ × W) : W :=
  ⟨geodesicContraction I M q.1 r (p.1, p.2.1),
    mapsTo_geodesicContraction hW q.2 hN hWr ⟨mem_univ p.1, p.2.2⟩⟩

/-- `geodesicContractionOpens` is globally smooth on `ℝ × W`. -/
theorem contMDiff_geodesicContractionOpens {W : TopologicalSpace.Opens M}
    (hW : IsStronglyGeodesicallyConvex I M (W : Set M)) (q : W) {r : ℝ}
    (hN : IsNormalDomain I M q.1 (Metric.ball 0 r))
    (hWr : (W : Set M) ⊆ riemannianExp I M q.1 '' Metric.ball 0 r) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (geodesicContractionOpens hW q hN hWr) := by
  rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
  have hincl : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × W ↦ (p.1, p.2.1)) :=
    contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
  have hcomp : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (Subtype.val ∘ geodesicContractionOpens hW q hN hWr) univ :=
    (contMDiffOn_geodesicContraction hN hWr).comp hincl.contMDiffOn
      fun p _ ↦ ⟨mem_univ p.1, p.2.2⟩
  exact contMDiffOn_univ.1 hcomp

/-- At time `0`, `geodesicContractionOpens` collapses every point to the centre `q`. -/
@[simp]
theorem geodesicContractionOpens_zero {W : TopologicalSpace.Opens M}
    (hW : IsStronglyGeodesicallyConvex I M (W : Set M)) (q : W) {r : ℝ}
    (hN : IsNormalDomain I M q.1 (Metric.ball 0 r))
    (hWr : (W : Set M) ⊆ riemannianExp I M q.1 '' Metric.ball 0 r) (x : W) :
    geodesicContractionOpens hW q hN hWr (0, x) = q :=
  Subtype.ext (geodesicContraction_zero q.1 r x.1)

/-- At time `1`, `geodesicContractionOpens` is the identity on `W`. -/
@[simp]
theorem geodesicContractionOpens_one {W : TopologicalSpace.Opens M}
    (hW : IsStronglyGeodesicallyConvex I M (W : Set M)) (q : W) {r : ℝ}
    (hN : IsNormalDomain I M q.1 (Metric.ball 0 r))
    (hWr : (W : Set M) ⊆ riemannianExp I M q.1 '' Metric.ball 0 r) (x : W) :
    geodesicContractionOpens hW q hN hWr (1, x) = x :=
  Subtype.ext (geodesicContraction_one (hWr x.2))

/-- `geodesicContractionOpens` fixes the centre `q` at all times. -/
@[simp]
theorem geodesicContractionOpens_centre {W : TopologicalSpace.Opens M}
    (hW : IsStronglyGeodesicallyConvex I M (W : Set M)) (q : W) {r : ℝ}
    (hN : IsNormalDomain I M q.1 (Metric.ball 0 r))
    (hWr : (W : Set M) ⊆ riemannianExp I M q.1 '' Metric.ball 0 r) (t : ℝ) :
    geodesicContractionOpens hW q hN hWr (t, q) = q :=
  Subtype.ext (geodesicContraction_centre hN t)

end StronglyConvex

end TauCeti.Manifold

end
