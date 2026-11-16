/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.Reaction
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple.Basic
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Parabolic maximum and comparison principles on evolving Riemannian manifolds

Let `M` be a `C²` boundaryless manifold and `t ↦ g t` a family of `C¹` Riemannian metrics on `M`,
accompanied by a time-dependent drift vector field `t ↦ X t`. At any spatial local maximum `x` of a
`C²` function `f : M → ℝ`, the differential `mvfderiv I f x` vanishes because `M` is boundaryless,
and the Laplace–Beltrami operator `(g t).laplaceBeltrami hn f x` is nonpositive by the elliptic
second-derivative test. Consequently the combined drift-diffusion operator
`Δ_{g(t)} f + d f (X t)` is nonpositive at every spatial local maximum and nonnegative at every
spatial local minimum, with **no** continuity or differentiability assumptions in time on `g` and
**no** regularity or boundedness assumptions in space or time on the drift vector field `X`.

Combining these pointwise sign lemmas with the abstract parabolic comparison and ODE barrier
principles from `TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.Reaction` yields the scalar
parabolic maximum principle on compact space-time cylinders `[a, b] × K` and on closed boundaryless
manifolds:

* **Explicit-metric derivative tests** (`Bundle.ContMDiffRiemannianMetric`): nonpositivity and
  nonnegativity of `g.hessian`, `g.laplaceBeltrami`, and `g.laplaceBeltrami + d f (v)` at spatial
  local extrema.
* **Parabolic cylinder comparison with left-hand time derivatives**: strict barrier comparison
  (requiring no Lipschitz hypothesis on the reaction) and locally Lipschitz reaction–diffusion
  comparison on `[a, b] × K` for functions having one-sided left-hand time derivatives
  `HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t`.
* **Closed-manifold maximum, comparison, and uniqueness principles**: weak maximum and minimum
  principles for `∂ₜu ≤ Δ_{g(t)} u + d u (X t)`, two-function comparison and uniqueness for
  `∂ₜu = Δ_{g(t)} u + d u (X t) + F(t, u)` with `F` locally Lipschitz on `[a, b] × ℝ`, and upper
  and lower ODE–PDE comparison principles.
* **Concrete barriers and scalar-curvature blow-up**: exponential Gronwall bounds, preservation of
  nonnegativity (`0 ≤ F(t, 0)`), strict inward positive improvement (`0 < δ ≤ F(t, 0)` implies
  `0 < u t x` for `t > a`), and the `n`-dimensional quadratic reaction lower bound
  `s₀ / (1 - (2 / n) s₀ (t - a)) ≤ u t x` together with the maximal lifespan bound
  `b - a < n / (2 s₀)` for positive initial data `0 < s₀ ≤ u a`.

## References

* B. Chow, P. Lu, and L. Ni, *Hamilton's Ricci Flow*, Graduate Studies in Mathematics 77,
  American Mathematical Society, 2006, Chapter 3.
* P. Topping, *Lectures on the Ricci Flow*, London Mathematical Society Lecture Note Series 325,
  Cambridge University Press, 2006, Chapter 3.
-/

public section

open Bundle Set
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M] {n : ℕ∞ω}

/-- At a local maximum of a `C²` function on a boundaryless manifold, the scalar Hessian with
respect to an explicit `C^n` (`1 ≤ n`) Riemannian metric `g` is negative semidefinite. -/
protected theorem hessian_self_nonpos_of_isLocalMax
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hmax : IsLocalMax f x)
    (v : TangentSpace I x) :
    g.hessian hn f x v v ≤ 0 := by
  rw [g.hessian_def]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  exact TauCeti.Manifold.hessian_self_nonpos_of_isLocalMax hf hmax v

/-- At a local minimum of a `C²` function on a boundaryless manifold, the scalar Hessian with
respect to an explicit `C^n` (`1 ≤ n`) Riemannian metric `g` is positive semidefinite. -/
protected theorem hessian_self_nonneg_of_isLocalMin
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hmin : IsLocalMin f x)
    (v : TangentSpace I x) :
    0 ≤ g.hessian hn f x v v := by
  rw [g.hessian_def]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  exact TauCeti.Manifold.hessian_self_nonneg_of_isLocalMin hf hmin v

/-- At a local maximum of a `C²` function on a boundaryless manifold, the Laplace–Beltrami operator
with respect to an explicit `C^n` (`1 ≤ n`) Riemannian metric `g` is nonpositive. -/
protected theorem laplaceBeltrami_nonpos_of_isLocalMax
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hmax : IsLocalMax f x) :
    g.laplaceBeltrami hn f x ≤ 0 := by
  rw [g.laplaceBeltrami_def]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  exact TauCeti.Manifold.laplaceBeltrami_nonpos_of_isLocalMax hf hmax

/-- At a local minimum of a `C²` function on a boundaryless manifold, the Laplace–Beltrami operator
with respect to an explicit `C^n` (`1 ≤ n`) Riemannian metric `g` is nonnegative. -/
protected theorem laplaceBeltrami_nonneg_of_isLocalMin
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hmin : IsLocalMin f x) :
    0 ≤ g.laplaceBeltrami hn f x := by
  rw [g.laplaceBeltrami_def]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  exact TauCeti.Manifold.laplaceBeltrami_nonneg_of_isLocalMin hf hmin

/-- At a local maximum of a `C²` function `f` on a boundaryless manifold, `Δ_g f + d f (v) ≤ 0`
for every tangent vector `v`. -/
theorem laplaceBeltrami_add_mvfderiv_nonpos_of_isLocalMax
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hmax : IsLocalMax f x)
    (v : TangentSpace I x) :
    g.laplaceBeltrami hn f x + mvfderiv I f x v ≤ 0 := by
  rw [TauCeti.mem_criticalPoints.1 (hmax.mem_criticalPoints (I := I)), zero_apply, add_zero]
  exact g.laplaceBeltrami_nonpos_of_isLocalMax hn hf hmax

/-- At a local minimum of a `C²` function `f` on a boundaryless manifold, `0 ≤ Δ_g f + d f (v)`
for every tangent vector `v`. -/
theorem laplaceBeltrami_add_mvfderiv_nonneg_of_isLocalMin
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hmin : IsLocalMin f x)
    (v : TangentSpace I x) :
    0 ≤ g.laplaceBeltrami hn f x + mvfderiv I f x v := by
  rw [TauCeti.mem_criticalPoints.1 (hmin.mem_criticalPoints (I := I)), zero_apply, add_zero]
  exact g.laplaceBeltrami_nonneg_of_isLocalMin hn hf hmin

/-- At a local maximum of `f₁ - f₂` on a boundaryless manifold where both functions are `C²`,
`(Δ_g f₁ - Δ_g f₂) + (d f₁ (v) - d f₂ (v)) ≤ 0`. -/
theorem laplaceBeltrami_sub_add_mvfderiv_sub_nonpos_of_isLocalMax
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f₁ f₂ : M → ℝ} {x : M} (hf₁ : ContMDiffAt I 𝓘(ℝ) 2 f₁ x) (hf₂ : ContMDiffAt I 𝓘(ℝ) 2 f₂ x)
    (hmax : IsLocalMax (f₁ - f₂) x) (v : TangentSpace I x) :
    g.laplaceBeltrami hn f₁ x - g.laplaceBeltrami hn f₂ x +
      (mvfderiv I f₁ x v - mvfderiv I f₂ x v) ≤ 0 := by
  have hsub : ContMDiffAt I 𝓘(ℝ) 2 (f₁ - f₂) x := hf₁.sub hf₂
  have h := g.laplaceBeltrami_add_mvfderiv_nonpos_of_isLocalMax hn hsub hmax v
  rwa [g.laplaceBeltrami_sub_of_contMDiffAt hn hf₁ hf₂,
    mvfderiv_sub (g := f₁) (g' := f₂) (hf₁.mdifferentiableAt (by simp))
      (hf₂.mdifferentiableAt (by simp)),
    sub_apply] at h

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M] {n : ℕ∞ω}

section Cylinder

variable {K : Set M} {a b : ℝ} {u v u' v' : ℝ → M → ℝ}

/-- **Strict parabolic barrier comparison on `[a, b] × K` for an evolving metric and drift.**

Let `K ⊆ M` be compact, `g` a time-indexed family of `C^n` (`1 ≤ n`) Riemannian metrics, and `X` a
time-dependent vector field on `M`. Suppose `u` and `v` are continuous on `[a, b] × K`, `C²` in
space and left-differentiable in time on `(a, b] × interior K`, satisfy `u < v` on the parabolic
boundary, and obey the strict differential inequality
`u' - Δ_{g(t)} u - d u (X t) < v' - Δ_{g(t)} v - d v (X t)` at every point of
`(a, b] × interior K` where `u t x = v t x`. Then `u < v` on all of `[a, b] × K`. No Lipschitz
condition is needed. -/
theorem lt_of_hasDerivWithinAt_Iic_sub_laplaceBeltrami_sub_mvfderiv_lt_parabolicBoundary
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) (hK : IsCompact K)
    (hucont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ K))
    (huderiv : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hvderiv : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ v s x) (v' t x) (Iic t) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K → ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hv2 : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K → ContMDiffAt I 𝓘(ℝ) 2 (v t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K → u t x = v t x →
      u' t x - (g t).laplaceBeltrami hn (u t) x - mvfderiv I (u t) x (X t x) <
        v' t x - (g t).laplaceBeltrami hn (v t) x - mvfderiv I (v t) x (X t x))
    (hinit : ∀ ⦃x⦄, x ∈ K → u a x < v a x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → u t x < v t x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → u t x < v t x :=
  TauCeti.lt_of_hasDerivWithinAt_Iic_lt_of_isLocalMax_sub_lt_parabolicBoundary hK hucont hvcont
    huderiv hvderiv
    (fun t ht x hx hmax heq ↦ by
      have hlap := (g t).laplaceBeltrami_sub_add_mvfderiv_sub_nonpos_of_isLocalMax hn
        (hu2 ht hx) (hv2 ht hx) hmax (X t x)
      linarith [hpde ht hx heq])
    hinit hlat

/-- **Reaction–diffusion comparison on `[a, b] × K` for an evolving metric and drift.**

Let `F` be locally Lipschitz on `[a, b] × ℝ`. If `u ≤ v` on the parabolic boundary of `[a, b] × K`
and `u' - Δ_{g(t)} u - d u (X t) - F(t, u) ≤ v' - Δ_{g(t)} v - d v (X t) - F(t, v)` on the open
cylinder `(a, b) × interior K` for left-hand time derivatives `u'` and `v'`, then `u ≤ v` on all
of `[a, b] × K`. -/
theorem le_of_hasDerivWithinAt_Iic_sub_laplaceBeltrami_sub_mvfderiv_sub_le_parabolicBoundary
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) (hK : IsCompact K) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    (hucont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ K))
    (huderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hvderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ v s x) (v' t x) (Iic t) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K → ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hv2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K → ContMDiffAt I 𝓘(ℝ) 2 (v t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      u' t x - (g t).laplaceBeltrami hn (u t) x - mvfderiv I (u t) x (X t x) - F t (u t x) ≤
        v' t x - (g t).laplaceBeltrami hn (v t) x - mvfderiv I (v t) x (X t x) - F t (v t x))
    (hinit : ∀ ⦃x⦄, x ∈ K → u a x ≤ v a x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ v t x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → u t x ≤ v t x :=
  TauCeti.le_of_hasDerivWithinAt_Iic_sub_le_sub_of_locallyLipschitzOn_le_parabolicBoundary hK hF
    hucont hvcont huderiv hvderiv
    (fun t ht x hx hmax _ ↦ by
      have hlap := (g t).laplaceBeltrami_sub_add_mvfderiv_sub_nonpos_of_isLocalMax hn
        (hu2 ht hx) (hv2 ht hx) hmax (X t x)
      linarith [hpde ht hx])
    hinit hlat

end Cylinder

section ClosedManifold

variable [CompactSpace M] {a b : ℝ} {u v u' v' : ℝ → M → ℝ}

/-- **Reaction–diffusion comparison on a closed manifold with left-hand time derivatives.** -/
theorem le_of_hasDerivWithinAt_Iic_sub_laplaceBeltrami_sub_mvfderiv_sub_le
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    (hucont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ univ))
    (huderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hvderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, HasDerivWithinAt (fun s ↦ v s x) (v' t x) (Iic t) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hv2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (v t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      u' t x - (g t).laplaceBeltrami hn (u t) x - mvfderiv I (u t) x (X t x) - F t (u t x) ≤
        v' t x - (g t).laplaceBeltrami hn (v t) x - mvfderiv I (v t) x (X t x) - F t (v t x))
    (hinit : ∀ x, u a x ≤ v a x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, u t x ≤ v t x := fun t ht x ↦
  le_of_hasDerivWithinAt_Iic_sub_laplaceBeltrami_sub_mvfderiv_sub_le_parabolicBoundary g hn X
    isCompact_univ hF hucont hvcont (fun _ hs y _ ↦ huderiv hs y) (fun _ hs y _ ↦ hvderiv hs y)
    (fun _ hs y _ ↦ hu2 hs y) (fun _ hs y _ ↦ hv2 hs y) (fun _ hs y _ ↦ hpde hs y)
    (fun y _ ↦ hinit y) (fun _ _ _ hy ↦ by simp at hy) ht (mem_univ x)

/-- **Reaction–diffusion comparison on a closed manifold.**

If `F` is locally Lipschitz on `[a, b] × ℝ`, `u a ≤ v a` on a closed boundaryless manifold `M`,
and `∂ₜu - Δ_{g(t)} u - d u (X t) - F(t, u) ≤ ∂ₜv - Δ_{g(t)} v - d v (X t) - F(t, v)` on
`(a, b) × M`, then `u t x ≤ v t x` for all `t ∈ [a, b]` and `x : M`. -/
theorem le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    (hucont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ univ))
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hv2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (v t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      deriv (fun s ↦ u s x) t - (g t).laplaceBeltrami hn (u t) x -
          mvfderiv I (u t) x (X t x) - F t (u t x) ≤
        deriv (fun s ↦ v s x) t - (g t).laplaceBeltrami hn (v t) x -
          mvfderiv I (v t) x (X t x) - F t (v t x))
    (hinit : ∀ x, u a x ≤ v a x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, u t x ≤ v t x :=
  le_of_hasDerivWithinAt_Iic_sub_laplaceBeltrami_sub_mvfderiv_sub_le g hn X hF hucont hvcont
    (fun _ hs x ↦ (hudiff hs x).hasDerivAt.hasDerivWithinAt)
    (fun _ hs x ↦ (hvdiff hs x).hasDerivAt.hasDerivWithinAt) hu2 hv2 hpde hinit

/-- **Uniqueness for semilinear drift-diffusion equations on a closed evolving manifold.**

Two classical solutions of `∂ₜu - Δ_{g(t)} u - d u (X t) - F(t, u) = 0` on `(a, b) × M` (or more
generally two functions with equal differential operator values) that agree at time `a` coincide at
every time `t ∈ [a, b]`. -/
theorem eq_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_eq
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    (hucont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ univ))
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hv2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (v t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      deriv (fun s ↦ u s x) t - (g t).laplaceBeltrami hn (u t) x -
          mvfderiv I (u t) x (X t x) - F t (u t x) =
        deriv (fun s ↦ v s x) t - (g t).laplaceBeltrami hn (v t) x -
          mvfderiv I (v t) x (X t x) - F t (v t x))
    (hinit : u a = v a) :
    ∀ ⦃t⦄, t ∈ Icc a b → u t = v t := fun t ht ↦ by
  funext x
  exact le_antisymm
    (le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le g hn X hF hucont hvcont hudiff hvdiff
      hu2 hv2 (fun _ hs y ↦ (hpde hs y).le) (fun y ↦ (congrFun hinit y).le) ht x)
    (le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le g hn X hF hvcont hucont hvdiff hudiff
      hv2 hu2 (fun _ hs y ↦ (hpde hs y).ge) (fun y ↦ (congrFun hinit y).ge) ht x)

/-- **Weak parabolic maximum principle on a closed evolving manifold.**

If `∂ₜu ≤ Δ_{g(t)} u + d u (X t)` on `(a, b) × M` and `u a ≤ m` on `M`, then `u t x ≤ m` for every
`t ∈ [a, b]` and `x : M`. -/
theorem le_of_deriv_le_laplaceBeltrami_add_mvfderiv
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {m : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      deriv (fun s ↦ u s x) t ≤ (g t).laplaceBeltrami hn (u t) x + mvfderiv I (u t) x (X t x))
    (hinit : ∀ x, u a x ≤ m) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, u t x ≤ m := fun t ht x ↦
  TauCeti.le_of_hasDerivWithinAt_Iic_nonpos_of_isLocalMax_Ioo_le_parabolicBoundary isCompact_univ
    hcont (fun _ hs y _ ↦ (hdiff hs y).hasDerivAt.hasDerivWithinAt)
    (fun s hs y _ hmax _ ↦
      (hpde hs y).trans ((g s).laplaceBeltrami_add_mvfderiv_nonpos_of_isLocalMax hn (hu2 hs y)
        hmax (X s y)))
    (fun y _ ↦ hinit y) (fun _ _ _ hy ↦ by simp at hy) ht (mem_univ x)

/-- **Weak parabolic minimum principle on a closed evolving manifold.**

If `Δ_{g(t)} u + d u (X t) ≤ ∂ₜu` on `(a, b) × M` and `m ≤ u a` on `M`, then `m ≤ u t x` for every
`t ∈ [a, b]` and `x : M`. -/
theorem ge_of_laplaceBeltrami_add_mvfderiv_le_deriv
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {m : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      (g t).laplaceBeltrami hn (u t) x + mvfderiv I (u t) x (X t x) ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, m ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, m ≤ u t x := fun t ht x ↦
  TauCeti.ge_of_nonneg_hasDerivWithinAt_Iic_of_isLocalMin_Ioo_ge_parabolicBoundary isCompact_univ
    hcont (fun _ hs y _ ↦ (hdiff hs y).hasDerivAt.hasDerivWithinAt)
    (fun s hs y _ hmin _ ↦
      ((g s).laplaceBeltrami_add_mvfderiv_nonneg_of_isLocalMin hn (hu2 hs y) hmin
        (X s y)).trans (hpde hs y))
    (fun y _ ↦ hinit y) (fun _ _ _ hy ↦ by simp at hy) ht (mem_univ x)

/-- **Upper ODE–PDE comparison on a closed evolving manifold with left-hand time derivatives.**

Let `F` be locally Lipschitz on `[a, b] × ℝ` and `φ : ℝ → ℝ` a continuous function on `[a, b]`
with left-hand derivative `φ'` satisfying `F t (φ t) ≤ φ' t` on `(a, b)`. If `u a ≤ φ a` and
`u' t x ≤ Δ_{g(t)} u + d u (X t) + F t (u t x)` on `(a, b) × M`, then `u t x ≤ φ t` on
`[a, b] × M`. -/
theorem le_of_hasDerivWithinAt_Iic_le_laplaceBeltrami_add_mvfderiv_add_of_locallyLipschitzOn
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    {φ φ' : ℝ → ℝ} (hφcont : ContinuousOn φ (Icc a b))
    (hφderiv : ∀ ⦃t⦄, t ∈ Ioo a b → HasDerivWithinAt φ (φ' t) (Iic t) t)
    (hφ : ∀ ⦃t⦄, t ∈ Ioo a b → F t (φ t) ≤ φ' t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      u' t x ≤ (g t).laplaceBeltrami hn (u t) x + mvfderiv I (u t) x (X t x) + F t (u t x))
    (hinit : ∀ x, u a x ≤ φ a) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, u t x ≤ φ t := fun t ht x ↦
  TauCeti.le_of_hasDerivWithinAt_Iic_le_of_locallyLipschitzOn_le_parabolicBoundary isCompact_univ
    hF hφcont hφderiv hφ hcont (fun _ hs y _ ↦ hderiv hs y)
    (fun s hs y _ hmax _ ↦ (hpde hs y).trans <| add_le_of_nonpos_left <|
      (g s).laplaceBeltrami_add_mvfderiv_nonpos_of_isLocalMax hn (hu2 hs y) hmax (X s y))
    (fun y _ ↦ hinit y) (fun _ _ _ hy ↦ by simp at hy) ht (mem_univ x)

/-- **Upper ODE–PDE comparison on a closed evolving manifold.** -/
theorem le_of_deriv_le_laplaceBeltrami_add_mvfderiv_add_of_locallyLipschitzOn
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    {φ : ℝ → ℝ} (hφcont : ContinuousOn φ (Icc a b))
    (hφdiff : ∀ ⦃t⦄, t ∈ Ioo a b → DifferentiableAt ℝ φ t)
    (hφ : ∀ ⦃t⦄, t ∈ Ioo a b → F t (φ t) ≤ deriv φ t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      deriv (fun s ↦ u s x) t ≤
        (g t).laplaceBeltrami hn (u t) x + mvfderiv I (u t) x (X t x) + F t (u t x))
    (hinit : ∀ x, u a x ≤ φ a) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, u t x ≤ φ t :=
  le_of_hasDerivWithinAt_Iic_le_laplaceBeltrami_add_mvfderiv_add_of_locallyLipschitzOn g hn X hF
    hφcont (fun _ hs ↦ (hφdiff hs).hasDerivAt.hasDerivWithinAt) hφ hcont
    (fun _ hs x ↦ (hdiff hs x).hasDerivAt.hasDerivWithinAt) hu2 hpde hinit

/-- **Lower ODE–PDE comparison on a closed evolving manifold.**

If `F` is locally Lipschitz on `[a, b] × ℝ`, `φ` satisfies `deriv φ t ≤ F t (φ t)` on `(a, b)`,
`φ a ≤ u a` on `M`, and `Δ_{g(t)} u + d u (X t) + F t (u t x) ≤ ∂ₜu` on `(a, b) × M`, then
`φ t ≤ u t x` on `[a, b] × M`. -/
theorem ge_of_laplaceBeltrami_add_mvfderiv_add_le_deriv_of_locallyLipschitzOn
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    {φ : ℝ → ℝ} (hφcont : ContinuousOn φ (Icc a b))
    (hφdiff : ∀ ⦃t⦄, t ∈ Ioo a b → DifferentiableAt ℝ φ t)
    (hφ : ∀ ⦃t⦄, t ∈ Ioo a b → deriv φ t ≤ F t (φ t))
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      (g t).laplaceBeltrami hn (u t) x + mvfderiv I (u t) x (X t x) + F t (u t x) ≤
        deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, φ a ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, φ t ≤ u t x :=
  TauCeti.ge_of_le_deriv_of_locallyLipschitzOn_of_isLocalMin hF hφcont hφdiff hφ hcont hdiff
    (fun s hs y hmin _ ↦ (le_add_of_nonneg_left <|
      (g s).laplaceBeltrami_add_mvfderiv_nonneg_of_isLocalMin hn (hu2 hs y) hmin (X s y)).trans
      (hpde hs y))
    hinit

/-- **Parabolic Gronwall upper bound on a closed evolving manifold.**

For any real constants `m` and `k`, if `u a ≤ m` and `∂ₜu ≤ Δ_{g(t)} u + d u (X t) + k * u` on
`(a, b) × M`, then `u t x ≤ m * Real.exp (k * (t - a))` on `[a, b] × M`. -/
theorem le_mul_exp_of_deriv_le_laplaceBeltrami_add_mvfderiv_add_mul
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {m k : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      deriv (fun s ↦ u s x) t ≤
        (g t).laplaceBeltrami hn (u t) x + mvfderiv I (u t) x (X t x) + k * u t x)
    (hinit : ∀ x, u a x ≤ m) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, u t x ≤ m * Real.exp (k * (t - a)) :=
  TauCeti.le_mul_exp_of_deriv_le_mul_of_isLocalMax hcont hdiff
    (fun s hs y hmax _ ↦ (hpde hs y).trans <| add_le_of_nonpos_left <|
      (g s).laplaceBeltrami_add_mvfderiv_nonpos_of_isLocalMax hn (hu2 hs y) hmax (X s y))
    hinit

/-- **Parabolic Gronwall lower bound on a closed evolving manifold.**

For any real constants `m` and `k`, if `m ≤ u a` and `Δ_{g(t)} u + d u (X t) + k * u ≤ ∂ₜu` on
`(a, b) × M`, then `m * Real.exp (k * (t - a)) ≤ u t x` on `[a, b] × M`. -/
theorem mul_exp_le_of_laplaceBeltrami_add_mvfderiv_add_mul_le_deriv
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {m k : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      (g t).laplaceBeltrami hn (u t) x + mvfderiv I (u t) x (X t x) + k * u t x ≤
        deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, m ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, m * Real.exp (k * (t - a)) ≤ u t x :=
  TauCeti.mul_exp_le_of_mul_le_deriv_of_isLocalMin hcont hdiff
    (fun s hs y hmin _ ↦ (le_add_of_nonneg_left <|
      (g s).laplaceBeltrami_add_mvfderiv_nonneg_of_isLocalMin hn (hu2 hs y) hmin (X s y)).trans
      (hpde hs y))
    hinit

/-- **Preservation of nonnegativity on a closed evolving manifold.**

If `F` is locally Lipschitz on `[a, b] × ℝ` with `0 ≤ F t 0` on `(a, b)`, `0 ≤ u a` on `M`, and
`Δ_{g(t)} u + d u (X t) + F t (u t x) ≤ ∂ₜu` on `(a, b) × M`, then `0 ≤ u t x` on `[a, b] × M`. -/
theorem nonneg_of_laplaceBeltrami_add_mvfderiv_add_le_deriv_of_locallyLipschitzOn
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    (hF0 : ∀ ⦃t⦄, t ∈ Ioo a b → 0 ≤ F t 0)
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      (g t).laplaceBeltrami hn (u t) x + mvfderiv I (u t) x (X t x) + F t (u t x) ≤
        deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, 0 ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, 0 ≤ u t x :=
  TauCeti.nonneg_of_le_deriv_of_locallyLipschitzOn_of_isLocalMin hF hF0 hcont hdiff
    (fun s hs y hmin _ ↦ (le_add_of_nonneg_left <|
      (g s).laplaceBeltrami_add_mvfderiv_nonneg_of_isLocalMin hn (hu2 hs y) hmin (X s y)).trans
      (hpde hs y))
    hinit

/-- **Strict inward positive improvement on a closed evolving manifold.**

If `F` is locally Lipschitz on `[a, b] × ℝ` and satisfies `δ ≤ F t 0` on `(a, b)` for some `δ > 0`,
then any nonnegative initial datum `0 ≤ u a` satisfying `Δ_{g(t)} u + d u (X t) + F t (u t x) ≤ ∂ₜu`
on `(a, b) × M` becomes strictly positive (`0 < u t x`) for all `t ∈ (a, b]` and `x : M`. -/
theorem pos_of_laplaceBeltrami_add_mvfderiv_add_le_deriv_of_locallyLipschitzOn
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    {δ : ℝ} (hδ : 0 < δ) (hF0 : ∀ ⦃t⦄, t ∈ Ioo a b → δ ≤ F t 0)
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      (g t).laplaceBeltrami hn (u t) x + mvfderiv I (u t) x (X t x) + F t (u t x) ≤
        deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, 0 ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Ioc a b → ∀ x, 0 < u t x :=
  TauCeti.pos_of_le_deriv_of_locallyLipschitzOn_of_isLocalMin hF hδ hF0 hcont hdiff
    (fun s hs y hmin ↦ (le_add_of_nonneg_left <|
      (g s).laplaceBeltrami_add_mvfderiv_nonneg_of_isLocalMin hn (hu2 hs y) hmin (X s y)).trans
      (hpde hs y))
    hinit

/-- **Quadratic reaction lower bound with dimensional coefficient `2 / dim M` on a closed evolving
manifold.**

Along an `n`-dimensional Ricci flow `∂ₜg = -2 Ric` (or DeTurck Ricci flow with drift `X`), the
scalar curvature `R` satisfies `Δ_{g(t)} R + d R (X t) + (2 / n) R² ≤ ∂ₜR`. For any real initial
lower bound `s₀ ≤ u a` with `0 < 1 - (2 / n) s₀ (b - a)`, the solution satisfies
`s₀ / (1 - (2 / n) s₀ (t - a)) ≤ u t x` on `[a, b] × M`. -/
theorem div_one_sub_mul_le_of_laplaceBeltrami_add_mvfderiv_add_two_div_finrank_mul_sq_le_deriv
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {s₀ : ℝ}
    (hb : 0 < 1 - 2 / (Module.finrank ℝ E : ℝ) * s₀ * (b - a))
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      (g t).laplaceBeltrami hn (u t) x + mvfderiv I (u t) x (X t x) +
        2 / (Module.finrank ℝ E : ℝ) * u t x ^ 2 ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, s₀ ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x,
      s₀ / (1 - 2 / (Module.finrank ℝ E : ℝ) * s₀ * (t - a)) ≤ u t x :=
  TauCeti.div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin (by positivity) hb hcont hdiff
    (fun s hs y hmin _ ↦ (le_add_of_nonneg_left <|
      (g s).laplaceBeltrami_add_mvfderiv_nonneg_of_isLocalMin hn (hu2 hs y) hmin (X s y)).trans
      (hpde hs y))
    hinit

/-- **Finite-time blow-up bound `b - a < dim M / (2 s₀)` on a nonempty closed evolving manifold.**

On a nonempty closed manifold `M` of positive dimension `0 < Module.finrank ℝ E`, if a continuous
function `u` on `[a, b] × M` satisfies `Δ_{g(t)} u + d u (X t) + (2 / dim M) u² ≤ ∂ₜu` on
`(a, b) × M` and `0 < s₀ ≤ u a` everywhere on `M`, then `b - a < (dim M) / (2 s₀)`. -/
theorem
    sub_lt_finrank_div_two_mul_of_laplaceBeltrami_add_mvfderiv_add_two_div_finrank_mul_sq_le_deriv
    [Nonempty M] (hdim : 0 < Module.finrank ℝ E)
    (g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    (X : ℝ → (x : M) → TangentSpace I x) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      (g t).laplaceBeltrami hn (u t) x + mvfderiv I (u t) x (X t x) +
        2 / (Module.finrank ℝ E : ℝ) * u t x ^ 2 ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, s₀ ≤ u a x) :
    b - a < (Module.finrank ℝ E : ℝ) / (2 * s₀) := by
  have hdim' : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr hdim
  have hlt := TauCeti.sub_lt_inv_mul_of_mul_sq_le_deriv_of_isLocalMin
    (c := 2 / (Module.finrank ℝ E : ℝ)) (div_pos two_pos hdim') hs₀ hcont hdiff
    (fun s hs y hmin ↦ (le_add_of_nonneg_left <|
      (g s).laplaceBeltrami_add_mvfderiv_nonneg_of_isLocalMin hn (hu2 hs y) hmin (X s y)).trans
      (hpde hs y))
    hinit
  refine hlt.trans_eq ?_
  have hs₀' : s₀ ≠ 0 := hs₀.ne'
  have hd' : (Module.finrank ℝ E : ℝ) ≠ 0 := hdim'.ne'
  field_simp

/-- **Reaction–diffusion comparison for a static Riemannian bundle metric on a closed manifold.** -/
theorem le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_riemannianBundle
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (X : ℝ → (x : M) → TangentSpace I x) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    (hucont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ univ))
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hu2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hv2 : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, ContMDiffAt I 𝓘(ℝ) 2 (v t) x)
    (hpde : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x,
      deriv (fun s ↦ u s x) t - laplaceBeltrami I (u t) x -
          mvfderiv I (u t) x (X t x) - F t (u t x) ≤
        deriv (fun s ↦ v s x) t - laplaceBeltrami I (v t) x -
          mvfderiv I (v t) x (X t x) - F t (v t x))
    (hinit : ∀ x, u a x ≤ v a x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, u t x ≤ v t x := by
  let g₀ : ContMDiffRiemannianMetric I 1 E (fun x : M ↦ TangentSpace I x) :=
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := 1)
  have hg₀ : ∀ y (v w : TangentSpace I y), g₀.inner y v w = inner ℝ v w :=
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner (IB := I) (n := 1)
  exact le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le (fun _ ↦ g₀) le_rfl X hF hucont hvcont
    hudiff hvdiff hu2 hv2
    (fun s hs x ↦ by
      rw [g₀.laplaceBeltrami_eq_laplaceBeltrami le_rfl hg₀,
        g₀.laplaceBeltrami_eq_laplaceBeltrami le_rfl hg₀]
      exact hpde hs x)
    hinit

end ClosedManifold

end TauCeti.Manifold
