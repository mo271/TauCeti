/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.QuadraticReaction
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Parabolic comparison and ODE barrier principles for reaction terms

On a space-time cylinder `[a, b] × K` over a compact subset `K` of a topological space `X`, a
parabolic subsolution `∂ₜu ≤ L u + F(t, u)` whose spatial operator `L` is nonpositive at local
maxima satisfies the differential inequality `∂ₜu ≤ F(t, u)` at every interior spatial local
maximum. Extending the constant-bound principle of
`TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.Basic` and the quadratic lower-barrier comparison
of `TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.QuadraticReaction`, this file develops the
scalar comparison and ODE barrier principles that follow from this pointwise sign condition alone,
without assuming a metric or linear structure on `X` and requiring only one-sided left-hand time
derivatives `HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t` (the natural time regularity of
pointwise suprema and distance-to-set functions along geometric flows).

1. **Strict barriers and one-sided derivatives.** Strict upper and lower barrier bounds hold on
   `[a, b] × K` when the strict sign condition on the left-hand time derivative holds only at exact
   interior contact points `u t x = m`; consequently, strict two-function comparison requires no
   Lipschitz hypothesis on the reaction term. Weak maximum and minimum principles for left-hand time
   derivatives on `(a, b)` and under linear growth bounds `u' ≤ L (u - m)` (for `L : ℝ` of any sign)
   follow on arbitrary intervals `[a, b]`.
2. **Locally Lipschitz reaction comparison.** When `F(t, ·)` is locally Lipschitz on `[a, b] × ℝ`
   (or uniformly Lipschitz on bounded value intervals for `t ∈ (a, b)`), a subsolution and
   supersolution satisfying `u ≤ v` on the parabolic boundary satisfy `u ≤ v` on all of
   `[a, b] × K`, including autonomous reactions `f(u)` with `LocallyLipschitz f`.
3. **ODE–PDE comparison and concrete barriers.** Comparing a PDE subsolution or supersolution with a
   spatially constant ODE supersolution `F(t, φ) ≤ φ'` or subsolution `φ' ≤ F(t, φ)` yields upper
   and lower Gronwall bounds `m exp (k (t - a))` (for arbitrary real `m` and `k`), constant-drift
   bounds `m + c (t - a)`, preservation of nonnegativity when `0 ≤ F(t, 0)`, strict positive
   improvement `0 < u t x` on `(a, b]` under an inward reaction `0 < δ ≤ F(t, 0)`, and the
   finite-time lifespan bound `b - a < (c ρ)⁻¹` for `∂ₜu ≥ c u²` (`c > 0`, `ρ > 0`) on a nonempty
   compact space.

## Main results

* `TauCeti.lt_of_hasDerivWithinAt_Iic_lt_zero_of_isLocalMax_lt_parabolicBoundary`: strict barrier
  principle with exact-contact hypothesis `u t x = m` and left-hand time derivatives.
* `TauCeti.le_of_hasDerivWithinAt_Iic_nonpos_of_isLocalMax_Ioo_le_parabolicBoundary`: weak maximum
  principle on `[a, b] × K` for left-hand time derivatives on `(a, b)`.
* `TauCeti.le_of_hasDerivWithinAt_Iic_le_mul_sub_of_isLocalMax_le_parabolicBoundary`: weak maximum
  principle under a one-sided linear growth bound `u' ≤ L (u - m)`.
* `TauCeti.lt_of_hasDerivWithinAt_Iic_lt_of_isLocalMax_sub_lt_parabolicBoundary`: strict
  two-function comparison without Lipschitz assumptions.
* `TauCeti.le_of_hasDerivWithinAt_Iic_sub_le_sub_of_locallyLipschitzOn_le_parabolicBoundary`:
  parabolic comparison for locally Lipschitz reactions `F(t, u)` on `[a, b] × K`.
* `TauCeti.le_of_hasDerivWithinAt_Iic_le_of_locallyLipschitzOn_le_parabolicBoundary`,
  `TauCeti.ge_of_le_hasDerivWithinAt_Iic_of_locallyLipschitzOn_ge_parabolicBoundary`: upper and
  lower ODE–PDE comparison principles on `[a, b] × K`.
* `TauCeti.le_mul_exp_of_deriv_le_mul_of_isLocalMax`,
  `TauCeti.mul_exp_le_of_mul_le_deriv_of_isLocalMin`: parabolic Gronwall upper and lower bounds.
* `TauCeti.nonneg_of_le_deriv_of_locallyLipschitzOn_of_isLocalMin`,
  `TauCeti.pos_of_le_deriv_of_locallyLipschitzOn_of_isLocalMin`: preservation of nonnegativity and
  strict inward positive improvement on compact spaces.
* `TauCeti.sub_lt_inv_mul_of_mul_sq_le_deriv_of_isLocalMin`: finite-time lifespan bound
  `b - a < (c ρ)⁻¹` for `∂ₜu ≥ c u²` at spatial minima on a nonempty compact space.

## References

* R. S. Hamilton, *Three-manifolds with positive Ricci curvature*, J. Differential Geom. 17
  (1982), 255–306.
* B. Chow, P. Lu, and L. Ni, *Hamilton's Ricci Flow*, Graduate Studies in Mathematics 77,
  American Mathematical Society (2006), Chapter 3.
* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), Chapter 3.
-/

public section

namespace TauCeti

open Filter NNReal Set
open scoped Topology

section StrictAndLeftDeriv

variable {X : Type*} [TopologicalSpace X] {K : Set X} {a b : ℝ}
  {u u' : ℝ → X → ℝ}

/-- **Strict parabolic barrier principle with left-hand time derivatives.**

Let `K` be compact, and let `u` be continuous on `[a, b] × K` with left-hand time derivatives
`u' t x` on `(a, b] × interior K`. Suppose `u' t x < 0` at every point `(t, x)` of
`(a, b] × interior K` where `x` is a spatial local maximum of `u t` with exact contact `u t x = m`.
If `u < m` on the parabolic boundary `({a} × K) ∪ ([a, b] × frontier K)`, then `u < m` on all of
`[a, b] × K`. -/
theorem lt_of_hasDerivWithinAt_Iic_lt_zero_of_isLocalMax_lt_parabolicBoundary (hK : IsCompact K)
    {m : ℝ} (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hderiv : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMax (u t) x → u t x = m → u' t x < 0)
    (hinit : ∀ ⦃x⦄, x ∈ K → u a x < m)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → u t x < m) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → u t x < m := by
  intro t₁ ht₁ x₁ hx₁
  by_contra! hge
  -- Project the compact superlevel `u ≥ m` inside `[a, b] × K` to its time coordinate `S`.
  have : CompactSpace ↑(Icc a b ×ˢ K) := isCompact_iff_compactSpace.mp (isCompact_Icc.prod hK)
  let Q : Set ↑(Icc a b ×ˢ K) := (Icc a b ×ˢ K).domRestrict (Function.uncurry u) ⁻¹' Ici m
  let S : Set ℝ := (fun p : ↑(Icc a b ×ˢ K) ↦ p.1.1) '' Q
  have hScomp : IsCompact S :=
    ((isClosed_Ici.preimage (continuousOn_iff_continuous_domRestrict.mp hcont)).isCompact).image
      (continuous_fst.comp continuous_subtype_val)
  obtain ⟨⟨⟨t', y₀⟩, ⟨ht₀, hy₀⟩⟩, hy₀m, hty⟩ :=
    hScomp.sInf_mem ⟨t₁, ⟨(t₁, x₁), ht₁, hx₁⟩, hge, rfl⟩
  have hy₀m' : m ≤ u t' y₀ := hy₀m
  dsimp only at hty ht₀
  set t₀ : ℝ := sInf S
  rw [hty] at ht₀ hy₀m'
  -- Maximize `u t₀` on `K` at the first contact time `t₀ = inf S`.
  obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn ⟨y₀, hy₀⟩
    (hcont.comp (continuousOn_const.prodMk continuousOn_id) fun y hy ↦ ⟨ht₀, hy⟩)
  have hx₀m : m ≤ u t₀ x₀ := hy₀m'.trans (isMaxOn_iff.mp hmax y₀ hy₀)
  have hpos : a < t₀ := ht₀.1.lt_of_ne' fun h0 ↦ (hinit hx₀).not_ge (h0 ▸ hx₀m)
  have ht₀_Ioc : t₀ ∈ Ioc a b := ⟨hpos, ht₀.2⟩
  have hint : x₀ ∈ interior K := by
    by_contra hni
    exact (hlat ht₀ ⟨subset_closure hx₀, hni⟩).not_ge hx₀m
  -- For `s < t₀` we have `u s x₀ < m`, so left-continuity gives `u t₀ x₀ = m` and `0 ≤ u' t₀ x₀`.
  have hbefore : ∀ s ∈ Ico a t₀, u s x₀ < m := fun s hs ↦ by_contra fun hsm ↦
    hs.2.not_ge <| csInf_le hScomp.bddBelow
      ⟨⟨(s, x₀), ⟨hs.1, hs.2.le.trans ht₀.2⟩, hx₀⟩, not_lt.mp hsm, rfl⟩
  have hcw : ContinuousWithinAt (fun s ↦ u s x₀) (Ico a t₀) t₀ :=
    ((hcont.comp (continuousOn_id.prodMk continuousOn_const) fun s (hs : s ∈ Icc a t₀) ↦
      ⟨⟨hs.1, hs.2.trans ht₀.2⟩, hx₀⟩) t₀ ⟨ht₀.1, le_rfl⟩).mono Ico_subset_Icc_self
  have heq : u t₀ x₀ = m := le_antisymm
    (hcw.closure_le (by rw [closure_Ico hpos.ne]; exact ⟨ht₀.1, le_rfl⟩)
      continuousWithinAt_const fun s hs ↦ (hbefore s hs).le) hx₀m
  have hlocmax : IsLocalMax (u t₀) x₀ :=
    eventually_of_mem (isOpen_interior.mem_nhds hint) fun y hy ↦
      isMaxOn_iff.mp hmax y (interior_subset hy)
  have hleft : IsLocalMaxOn (fun s ↦ u s x₀) (Iic t₀) t₀ :=
    mem_of_superset (Icc_mem_nhdsLE hpos) fun s hs ↦
      hs.2.eq_or_lt.elim (fun h ↦ h ▸ le_rfl) fun hslt ↦ (hbefore s ⟨hs.1, hslt⟩).le.trans heq.ge
  exact (hloc ht₀_Ioc hint hlocmax heq).not_ge
    (hleft.hasDerivWithinAt_Iic_nonneg (hderiv ht₀_Ioc hint))

/-- **Strict lower parabolic barrier principle with left-hand time derivatives.**

Dual of `lt_of_hasDerivWithinAt_Iic_lt_zero_of_isLocalMax_lt_parabolicBoundary`: if `m < u` on the
parabolic boundary of `[a, b] × K` and `0 < u' t x` at every interior spatial local minimum where
`u t x = m`, then `m < u` on all of `[a, b] × K`. -/
theorem gt_of_zero_lt_hasDerivWithinAt_Iic_of_isLocalMin_gt_parabolicBoundary (hK : IsCompact K)
    {m : ℝ} (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hderiv : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMin (u t) x → u t x = m → 0 < u' t x)
    (hinit : ∀ ⦃x⦄, x ∈ K → m < u a x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → m < u t x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → m < u t x := by
  intro t ht x hx
  have h := lt_of_hasDerivWithinAt_Iic_lt_zero_of_isLocalMax_lt_parabolicBoundary
    (u := -u) (u' := -u') (m := -m) hK hcont.neg
    (fun s hs y hy ↦ (hderiv hs hy).neg)
    (fun s hs y hy hmax heq ↦ by
      have hmin : IsLocalMin (u s) y := hmax.mono fun z hz ↦ by
        simp only [Pi.neg_apply] at hz
        linarith
      exact neg_lt_zero.mpr (hloc hs hy hmin (neg_inj.mp (by simpa using heq))))
    (fun y hy ↦ neg_lt_neg (hinit hy))
    (fun s hs y hy ↦ neg_lt_neg (hlat hs hy)) ht hx
  exact neg_lt_neg_iff.mp h

/-- **Weak parabolic maximum principle with left-hand time derivatives on `(a, b]`.**

If `u` is continuous on `[a, b] × K`, has left-hand time derivatives `u' t x` on
`(a, b] × interior K` satisfying `u' t x ≤ 0` at every interior spatial local maximum where
`m < u t x`, and `u ≤ m` on the parabolic boundary, then `u ≤ m` on all of `[a, b] × K`. -/
theorem le_of_hasDerivWithinAt_Iic_nonpos_of_isLocalMax_le_parabolicBoundary (hK : IsCompact K)
    {m : ℝ} (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hderiv : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMax (u t) x → m < u t x → u' t x ≤ 0)
    (hinit : ∀ ⦃x⦄, x ∈ K → u a x ≤ m)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ m) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → u t x ≤ m := by
  intro t ht x hx
  -- Perturb `u` by `-ε * (s - a + 1)`, which is strictly below `m` on the parabolic boundary.
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  set c : ℝ := b - a + 1
  have hc : 0 < c := by linarith [ht.1, ht.2]
  set δ : ℝ := ε / (2 * c)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let w : ℝ → X → ℝ := fun s y ↦ u s y - δ * (s - a + 1)
  let w' : ℝ → X → ℝ := fun s y ↦ u' s y - δ
  have hwcont : ContinuousOn (Function.uncurry w) (Icc a b ×ˢ K) :=
    hcont.sub (continuousOn_const.mul ((continuousOn_fst.sub continuousOn_const).add
      continuousOn_const))
  have hwderiv : ∀ ⦃s⦄, s ∈ Ioc a b → ∀ ⦃y⦄, y ∈ interior K →
      HasDerivWithinAt (fun r ↦ w r y) (w' s y) (Iic s) s := by
    intro s hs y hy
    have hlin : HasDerivAt (fun r : ℝ ↦ δ * (r - a + 1)) δ s := by
      simpa using (((hasDerivAt_id s).sub_const a).add_const 1).const_mul δ
    exact (hderiv hs hy).fun_sub hlin.hasDerivWithinAt
  have hlt := lt_of_hasDerivWithinAt_Iic_lt_zero_of_isLocalMax_lt_parabolicBoundary
    (u := w) (u' := w') (m := m) hK hwcont hwderiv
    (fun s hs y hy hmax heq ↦ by
      have humax : IsLocalMax (u s) y := hmax.mono fun z hz ↦ by linarith
      have hum : m < u s y := by
        have : 0 < δ * (s - a + 1) := mul_pos hδ (by linarith [hs.1])
        linarith [heq]
      linarith [hloc hs hy humax hum])
    (fun y hy ↦ by
      dsimp only [w]
      linarith [hinit hy])
    (fun s hs y hy ↦ by
      have : 0 < δ * (s - a + 1) := mul_pos hδ (by linarith [hs.1])
      dsimp only [w]
      linarith [hlat hs hy])
    ht hx
  have hbound : δ * (t - a + 1) ≤ ε / 2 := by
    have hle : t - a + 1 ≤ c := by linarith [ht.2]
    calc δ * (t - a + 1) ≤ δ * c := mul_le_mul_of_nonneg_left hle hδ.le
      _ = ε / 2 := by
        dsimp only [δ]
        field_simp
  dsimp only [w] at hlt
  linarith

/-- **Weak parabolic maximum principle with left-hand time derivatives on `(a, b)`.**

Refinement of `le_of_hasDerivWithinAt_Iic_nonpos_of_isLocalMax_le_parabolicBoundary` requiring
time differentiability and the interior sign condition only on the open interval `(a, b)`. -/
theorem le_of_hasDerivWithinAt_Iic_nonpos_of_isLocalMax_Ioo_le_parabolicBoundary (hK : IsCompact K)
    {m : ℝ} (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMax (u t) x → m < u t x → u' t x ≤ 0)
    (hinit : ∀ ⦃x⦄, x ∈ K → u a x ≤ m)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ m) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → u t x ≤ m := by
  intro t ht x hx
  -- Restrict to `[a, τ]` for `τ ∈ [a, b)` and pass to `t = b` by continuity.
  have hIco : ∀ τ ∈ Ico a b, u τ x ≤ m := fun τ hτ ↦
    le_of_hasDerivWithinAt_Iic_nonpos_of_isLocalMax_le_parabolicBoundary (a := a) (b := τ) hK
      (hcont.mono (prod_mono (Icc_subset_Icc_right hτ.2.le) Subset.rfl))
      (fun s hs y hy ↦ hderiv ⟨hs.1, lt_of_le_of_lt hs.2 hτ.2⟩ hy)
      (fun s hs y hy ↦ hloc ⟨hs.1, lt_of_le_of_lt hs.2 hτ.2⟩ hy)
      hinit (fun s hs y hy ↦ hlat ⟨hs.1, hs.2.trans hτ.2.le⟩ hy) ⟨hτ.1, le_rfl⟩ hx
  rcases ht.2.lt_or_eq with htb | rfl
  · exact hIco t ⟨ht.1, htb⟩
  rcases ht.1.eq_or_lt with rfl | hpos
  · exact hinit hx
  have hcw : ContinuousWithinAt (fun s ↦ u s x) (Ico a t) t :=
    ((hcont.comp (continuousOn_id.prodMk continuousOn_const) fun s hs ↦ ⟨hs, hx⟩) t ht).mono
      Ico_subset_Icc_self
  exact hcw.closure_le (by rw [closure_Ico hpos.ne]; exact ht) continuousWithinAt_const hIco

/-- **Weak parabolic minimum principle with left-hand time derivatives on `(a, b)`.**

Dual of `le_of_hasDerivWithinAt_Iic_nonpos_of_isLocalMax_Ioo_le_parabolicBoundary`: if `m ≤ u` on
the parabolic boundary of `[a, b] × K` and `0 ≤ u' t x` at every interior spatial local minimum
where `u t x < m`, then `m ≤ u` on all of `[a, b] × K`. -/
theorem ge_of_nonneg_hasDerivWithinAt_Iic_of_isLocalMin_Ioo_ge_parabolicBoundary (hK : IsCompact K)
    {m : ℝ} (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMin (u t) x → u t x < m → 0 ≤ u' t x)
    (hinit : ∀ ⦃x⦄, x ∈ K → m ≤ u a x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → m ≤ u t x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → m ≤ u t x := by
  intro t ht x hx
  have h := le_of_hasDerivWithinAt_Iic_nonpos_of_isLocalMax_Ioo_le_parabolicBoundary
    (u := -u) (u' := -u') (m := -m) hK hcont.neg
    (fun s hs y hy ↦ (hderiv hs hy).neg)
    (fun s hs y hy hmax hlt ↦ by
      have hmin : IsLocalMin (u s) y := hmax.mono fun z hz ↦ by
        simp only [Pi.neg_apply] at hz
        linarith
      exact neg_nonpos.mpr (hloc hs hy hmin (neg_lt_neg_iff.mp hlt)))
    (fun y hy ↦ neg_le_neg (hinit hy))
    (fun s hs y hy ↦ neg_le_neg (hlat hs hy)) ht hx
  exact neg_le_neg_iff.mp h

/-- **Exponential-weight maximum principle for linear growth above a bound.**

For any real constant `L` (of any sign), if `u ≤ m` on the parabolic boundary of `[a, b] × K` and
`u' t x ≤ L * (u t x - m)` at every interior spatial local maximum on `(a, b) × interior K` where
`m < u t x`, then `u ≤ m` on all of `[a, b] × K`. -/
theorem le_of_hasDerivWithinAt_Iic_le_mul_sub_of_isLocalMax_le_parabolicBoundary (hK : IsCompact K)
    {m L : ℝ} (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMax (u t) x → m < u t x → u' t x ≤ L * (u t x - m))
    (hinit : ∀ ⦃x⦄, x ∈ K → u a x ≤ m)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ m) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → u t x ≤ m := by
  intro t ht x hx
  let w : ℝ → X → ℝ := fun s y ↦ Real.exp (-(L * (s - a))) * (u s y - m)
  let w' : ℝ → X → ℝ := fun s y ↦
    Real.exp (-(L * (s - a))) * -L * (u s y - m) + Real.exp (-(L * (s - a))) * u' s y
  have hwcont : ContinuousOn (Function.uncurry w) (Icc a b ×ˢ K) :=
    (by fun_prop : ContinuousOn (fun p : ℝ × X ↦ Real.exp (-(L * (p.1 - a)))) _).mul
      (hcont.sub continuousOn_const)
  have hwderiv : ∀ ⦃s⦄, s ∈ Ioo a b → ∀ ⦃y⦄, y ∈ interior K →
      HasDerivWithinAt (fun r ↦ w r y) (w' s y) (Iic s) s := by
    intro s hs y hy
    have hlin : HasDerivAt (fun r : ℝ ↦ -(L * (r - a))) (-L) s := by
      convert (((hasDerivAt_id s).sub_const a).const_mul L).neg using 1
      · ext r
        rfl
      · simp
    have hexp : HasDerivAt (fun r : ℝ ↦ Real.exp (-(L * (r - a))))
        (Real.exp (-(L * (s - a))) * -L) s := hlin.exp
    convert hexp.hasDerivWithinAt.fun_mul
      ((hderiv hs hy).fun_sub (hasDerivWithinAt_const s (Iic s) m)) using 1
    ring
  have h := le_of_hasDerivWithinAt_Iic_nonpos_of_isLocalMax_Ioo_le_parabolicBoundary
    (u := w) (u' := w') (m := 0) hK hwcont hwderiv
    (fun s hs y hy hmax hpos ↦ by
      have hexp_pos : 0 < Real.exp (-(L * (s - a))) := Real.exp_pos _
      have hum : m < u s y := by
        have := pos_of_mul_pos_right hpos hexp_pos.le
        linarith
      have humax : IsLocalMax (u s) y := hmax.mono fun z hz ↦ by
        linarith [le_of_mul_le_mul_left hz hexp_pos]
      have hkey : u' s y - L * (u s y - m) ≤ 0 := by linarith [hloc hs hy humax hum]
      have := mul_nonpos_of_nonneg_of_nonpos hexp_pos.le hkey
      dsimp only [w']
      linarith)
    (fun y hy ↦ mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (hinit hy)))
    (fun s hs y hy ↦ mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (sub_nonpos.mpr (hlat hs hy)))
    ht hx
  have := nonpos_of_mul_nonpos_right h (Real.exp_pos _)
  linarith

end StrictAndLeftDeriv

section ReactionComparison

variable {X : Type*} [TopologicalSpace X] {K : Set X} {a b : ℝ}
  {u u' v v' : ℝ → X → ℝ}

/-- **Strict two-function parabolic comparison without Lipschitz assumptions.**

If `u < v` on the parabolic boundary of `[a, b] × K` and `u' t x < v' t x` at every point of
`(a, b] × interior K` where `x` is a spatial local maximum of `u t - v t` with `u t x = v t x`,
then `u < v` on all of `[a, b] × K`. Because comparison is checked only where `u t x = v t x`, any
zero-order reaction `F(t, x, w)` cancels at contact without needing continuity or Lipschitz
regularity in `w`. -/
theorem lt_of_hasDerivWithinAt_Iic_lt_of_isLocalMax_sub_lt_parabolicBoundary (hK : IsCompact K)
    (hucont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ K))
    (huderiv : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hvderiv : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ v s x) (v' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioc a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMax (u t - v t) x → u t x = v t x → u' t x < v' t x)
    (hinit : ∀ ⦃x⦄, x ∈ K → u a x < v a x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → u t x < v t x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → u t x < v t x := by
  intro t ht x hx
  have h := lt_of_hasDerivWithinAt_Iic_lt_zero_of_isLocalMax_lt_parabolicBoundary
    (u := u - v) (u' := u' - v') (m := 0) hK (hucont.sub hvcont)
    (fun s hs y hy ↦ (huderiv hs hy).sub (hvderiv hs hy))
    (fun s hs y hy hmax heq ↦ sub_lt_zero.mpr <|
      hloc hs hy hmax (sub_eq_zero.mp heq))
    (fun y hy ↦ sub_lt_zero.mpr (hinit hy))
    (fun s hs y hy ↦ sub_lt_zero.mpr (hlat hs hy)) ht hx
  exact sub_lt_zero.mp h

/-- **Two-function parabolic comparison under a one-sided linear difference bound.**

For any real constant `L`, if `u ≤ v` on the parabolic boundary of `[a, b] × K` and
`u' t x - v' t x ≤ L * (u t x - v t x)` at every interior point where `x` is a spatial local
maximum of `u t - v t` and `v t x < u t x`, then `u ≤ v` on all of `[a, b] × K`. -/
theorem le_of_hasDerivWithinAt_Iic_sub_le_mul_sub_of_isLocalMax_sub_le_parabolicBoundary
    (hK : IsCompact K) {L : ℝ}
    (hucont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ K))
    (huderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hvderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ v s x) (v' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMax (u t - v t) x → v t x < u t x → u' t x - v' t x ≤ L * (u t x - v t x))
    (hinit : ∀ ⦃x⦄, x ∈ K → u a x ≤ v a x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ v t x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → u t x ≤ v t x := by
  intro t ht x hx
  have h := le_of_hasDerivWithinAt_Iic_le_mul_sub_of_isLocalMax_le_parabolicBoundary
    (u := u - v) (u' := u' - v') (m := 0) (L := L) hK (hucont.sub hvcont)
    (fun s hs y hy ↦ (huderiv hs hy).sub (hvderiv hs hy))
    (fun s hs y hy hmax hpos ↦ by
      simpa using hloc hs hy hmax (sub_pos.mp hpos))
    (fun y hy ↦ sub_nonpos.mpr (hinit hy))
    (fun s hs y hy ↦ sub_nonpos.mpr (hlat hs hy)) ht hx
  exact sub_nonpos.mp h

/-- A reaction `F : ℝ → ℝ → ℝ` that is locally Lipschitz on `[a, b] × ℝ` is Lipschitz in its second
argument on `[-R, R]` uniformly for `t ∈ [a, b]`. -/
theorem exists_lipschitzOnWith_Icc_of_locallyLipschitzOn {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F)) (R : ℝ) :
    ∃ L : ℝ≥0, ∀ ⦃t⦄, t ∈ Icc a b → LipschitzOnWith L (F t) (Icc (-R) R) := by
  have hsub : Icc a b ×ˢ Icc (-R) R ⊆ Icc a b ×ˢ univ :=
    prod_mono Subset.rfl (subset_univ _)
  obtain ⟨L, hL⟩ :=
    (hF.mono hsub).exists_lipschitzOnWith_of_compact (isCompact_Icc.prod isCompact_Icc)
  refine ⟨L, fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun r₁ hr₁ r₂ hr₂ ↦ ?_⟩
  simpa [Prod.dist_eq] using hL.dist_le_mul (t, r₁) ⟨ht, hr₁⟩ (t, r₂) ⟨ht, hr₂⟩

/-- **Parabolic comparison for reactions Lipschitz on bounded value intervals.**

Suppose that for every `R : ℝ` there exists `L : ℝ≥0` such that `F t` is `L`-Lipschitz on
`[-R, R]` for all `t ∈ (a, b)`. If `u ≤ v` on the parabolic boundary of `[a, b] × K` and
`u' t x - F t (u t x) ≤ v' t x - F t (v t x)` at every interior spatial local maximum of
`u t - v t` where `v t x < u t x`, then `u ≤ v` on all of `[a, b] × K`. -/
theorem le_of_hasDerivWithinAt_Iic_sub_le_sub_of_lipschitzOnWith_le_parabolicBoundary
    (hK : IsCompact K) {F : ℝ → ℝ → ℝ}
    (hF : ∀ R : ℝ, ∃ L : ℝ≥0, ∀ ⦃t⦄, t ∈ Ioo a b → LipschitzOnWith L (F t) (Icc (-R) R))
    (hucont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ K))
    (huderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hvderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ v s x) (v' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMax (u t - v t) x → v t x < u t x →
        u' t x - F t (u t x) ≤ v' t x - F t (v t x))
    (hinit : ∀ ⦃x⦄, x ∈ K → u a x ≤ v a x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ v t x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → u t x ≤ v t x := by
  intro t ht x hx
  -- Bound `|u|` and `|v|` uniformly on the compact cylinder `[a, b] × K`.
  have hcomp : IsCompact (Icc a b ×ˢ K) := isCompact_Icc.prod hK
  have hne : (Icc a b ×ˢ K).Nonempty := ⟨(t, x), ht, hx⟩
  obtain ⟨p₁, -, hmax_u⟩ := hcomp.exists_isMaxOn hne hucont.abs
  obtain ⟨p₂, -, hmax_v⟩ := hcomp.exists_isMaxOn hne hvcont.abs
  set R : ℝ := max |Function.uncurry u p₁| |Function.uncurry v p₂|
  obtain ⟨L, hL⟩ := hF R
  refine le_of_hasDerivWithinAt_Iic_sub_le_mul_sub_of_isLocalMax_sub_le_parabolicBoundary
    (L := L) hK hucont hvcont huderiv hvderiv (fun s hs y hy hmax hlt ↦ ?_) hinit hlat ht hx
  have hus : u s y ∈ Icc (-R) R := abs_le.mp <|
    (isMaxOn_iff.mp hmax_u (s, y) ⟨Ioo_subset_Icc_self hs, interior_subset hy⟩).trans
      (le_max_left _ _)
  have hvs : v s y ∈ Icc (-R) R := abs_le.mp <|
    (isMaxOn_iff.mp hmax_v (s, y) ⟨Ioo_subset_Icc_self hs, interior_subset hy⟩).trans
      (le_max_right _ _)
  have hdist : F s (u s y) - F s (v s y) ≤ (L : ℝ) * (u s y - v s y) := by
    calc F s (u s y) - F s (v s y)
        ≤ |F s (u s y) - F s (v s y)| := le_abs_self _
      _ = dist (F s (u s y)) (F s (v s y)) := (Real.dist_eq _ _).symm
      _ ≤ (L : ℝ) * dist (u s y) (v s y) := (hL hs).dist_le_mul (u s y) hus (v s y) hvs
      _ = (L : ℝ) * (u s y - v s y) := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hlt)]
  linarith [hloc hs hy hmax hlt]

/-- **Parabolic comparison for locally Lipschitz reactions `F(t, u)` on `[a, b] × K`.**

Let `F` be locally Lipschitz on `[a, b] × ℝ`. If `u ≤ v` on the parabolic boundary of `[a, b] × K`
and `u' t x - F t (u t x) ≤ v' t x - F t (v t x)` at every interior point where `x` is a spatial
local maximum of `u t - v t` and `v t x < u t x`, then `u ≤ v` on all of `[a, b] × K`. -/
theorem le_of_hasDerivWithinAt_Iic_sub_le_sub_of_locallyLipschitzOn_le_parabolicBoundary
    (hK : IsCompact K) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    (hucont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ K))
    (huderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hvderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ v s x) (v' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMax (u t - v t) x → v t x < u t x →
        u' t x - F t (u t x) ≤ v' t x - F t (v t x))
    (hinit : ∀ ⦃x⦄, x ∈ K → u a x ≤ v a x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ v t x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → u t x ≤ v t x :=
  le_of_hasDerivWithinAt_Iic_sub_le_sub_of_lipschitzOnWith_le_parabolicBoundary hK
    (fun R ↦ let ⟨L, hL⟩ := exists_lipschitzOnWith_Icc_of_locallyLipschitzOn hF R
      ⟨L, fun _ ht ↦ hL (Ioo_subset_Icc_self ht)⟩)
    hucont hvcont huderiv hvderiv hloc hinit hlat

/-- **Parabolic comparison for autonomous locally Lipschitz reactions `f(u)` on `[a, b] × K`.** -/
theorem le_of_hasDerivWithinAt_Iic_sub_le_sub_of_locallyLipschitz_le_parabolicBoundary
    (hK : IsCompact K) {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    (hucont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ K))
    (huderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hvderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ v s x) (v' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMax (u t - v t) x → v t x < u t x → u' t x - f (u t x) ≤ v' t x - f (v t x))
    (hinit : ∀ ⦃x⦄, x ∈ K → u a x ≤ v a x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ v t x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → u t x ≤ v t x :=
  le_of_hasDerivWithinAt_Iic_sub_le_sub_of_lipschitzOnWith_le_parabolicBoundary
    (F := fun _ ↦ f) hK
    (fun R ↦ let ⟨L, hL⟩ :=
      hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact (s := Icc (-R) R) isCompact_Icc
      ⟨L, fun _ _ ↦ hL⟩)
    hucont hvcont huderiv hvderiv hloc hinit hlat

end ReactionComparison

section ODEComparison

variable {X : Type*} [TopologicalSpace X] {K : Set X} {a b : ℝ}
  {u u' : ℝ → X → ℝ}

/-- **Upper ODE–PDE comparison principle on `[a, b] × K` with left-hand time derivatives.**

Let `F` be locally Lipschitz on `[a, b] × ℝ` and let `φ : ℝ → ℝ` be continuous on `[a, b]` with
left-hand derivative `φ'` on `(a, b)` satisfying `F t (φ t) ≤ φ' t` (an ODE supersolution). If
`u ≤ φ` on the parabolic boundary of `[a, b] × K` and `u' t x ≤ F t (u t x)` at every interior
spatial local maximum of `u t` where `φ t < u t x`, then `u t x ≤ φ t` on all of `[a, b] × K`. -/
theorem le_of_hasDerivWithinAt_Iic_le_of_locallyLipschitzOn_le_parabolicBoundary
    (hK : IsCompact K) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    {φ φ' : ℝ → ℝ} (hφcont : ContinuousOn φ (Icc a b))
    (hφderiv : ∀ ⦃t⦄, t ∈ Ioo a b → HasDerivWithinAt φ (φ' t) (Iic t) t)
    (hφ : ∀ ⦃t⦄, t ∈ Ioo a b → F t (φ t) ≤ φ' t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMax (u t) x → φ t < u t x → u' t x ≤ F t (u t x))
    (hinit : ∀ ⦃x⦄, x ∈ K → u a x ≤ φ a)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → u t x ≤ φ t) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → u t x ≤ φ t :=
  le_of_hasDerivWithinAt_Iic_sub_le_sub_of_locallyLipschitzOn_le_parabolicBoundary
    (v := fun s _ ↦ φ s) (v' := fun s _ ↦ φ' s) hK hF hcont
    (hφcont.comp continuousOn_fst mapsTo_fst_prod) hderiv
    (fun _ ht _ _ ↦ hφderiv ht)
    (fun s hs y hy hmax hlt ↦ by
      have humax : IsLocalMax (u s) y := hmax.mono fun z hz ↦ by
        simp only [Pi.sub_apply] at hz
        linarith
      linarith [hloc hs hy humax hlt, hφ hs])
    hinit hlat

/-- **Lower ODE–PDE comparison principle on `[a, b] × K` with left-hand time derivatives.**

Dual of `le_of_hasDerivWithinAt_Iic_le_of_locallyLipschitzOn_le_parabolicBoundary`: if `φ' t ≤
F t (φ t)` on `(a, b)` (an ODE subsolution), `φ ≤ u` on the parabolic boundary of `[a, b] × K`, and
`F t (u t x) ≤ u' t x` at every interior spatial local minimum of `u t` where `u t x < φ t`, then
`φ t ≤ u t x` on all of `[a, b] × K`. -/
theorem ge_of_le_hasDerivWithinAt_Iic_of_locallyLipschitzOn_ge_parabolicBoundary
    (hK : IsCompact K) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    {φ φ' : ℝ → ℝ} (hφcont : ContinuousOn φ (Icc a b))
    (hφderiv : ∀ ⦃t⦄, t ∈ Ioo a b → HasDerivWithinAt φ (φ' t) (Iic t) t)
    (hφ : ∀ ⦃t⦄, t ∈ Ioo a b → φ' t ≤ F t (φ t))
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMin (u t) x → u t x < φ t → F t (u t x) ≤ u' t x)
    (hinit : ∀ ⦃x⦄, x ∈ K → φ a ≤ u a x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → φ t ≤ u t x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → φ t ≤ u t x :=
  le_of_hasDerivWithinAt_Iic_sub_le_sub_of_locallyLipschitzOn_le_parabolicBoundary
    (u := fun s _ ↦ φ s) (u' := fun s _ ↦ φ' s) (v := u) (v' := u') hK hF
    (hφcont.comp continuousOn_fst mapsTo_fst_prod) hcont
    (fun _ ht _ _ ↦ hφderiv ht) hderiv
    (fun s hs y hy hmax hlt ↦ by
      have humin : IsLocalMin (u s) y := hmax.mono fun z hz ↦ by
        simp only [Pi.sub_apply] at hz
        linarith
      linarith [hloc hs hy humin hlt, hφ hs])
    hinit hlat

/-- **Upper ODE–PDE comparison principle on a compact space.**

On a compact space `X` without lateral boundary, if `F` is locally Lipschitz on `[a, b] × ℝ`,
`φ` is an ODE supersolution `F t (φ t) ≤ deriv φ t` on `(a, b)`, `∂ₜu ≤ F t (u t x)` at every
spatial local maximum where `φ t < u t x`, and `u a ≤ φ a`, then `u t x ≤ φ t` on `[a, b] × X`. -/
theorem le_of_deriv_le_of_locallyLipschitzOn_of_isLocalMax [CompactSpace X] {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    {φ : ℝ → ℝ} (hφcont : ContinuousOn φ (Icc a b))
    (hφdiff : ∀ ⦃t⦄, t ∈ Ioo a b → DifferentiableAt ℝ φ t)
    (hφ : ∀ ⦃t⦄, t ∈ Ioo a b → F t (φ t) ≤ deriv φ t)
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, IsLocalMax (u t) x → φ t < u t x →
      deriv (fun s ↦ u s x) t ≤ F t (u t x))
    (hinit : ∀ x, u a x ≤ φ a) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, u t x ≤ φ t := fun t ht x ↦
  le_of_hasDerivWithinAt_Iic_le_of_locallyLipschitzOn_le_parabolicBoundary
    (u' := fun s y ↦ deriv (fun r ↦ u r y) s) (φ' := deriv φ) isCompact_univ hF hφcont
    (fun _ hs ↦ (hφdiff hs).hasDerivAt.hasDerivWithinAt) hφ hcont
    (fun _ hs y _ ↦ (hdiff hs y).hasDerivAt.hasDerivWithinAt)
    (fun _ hs y _ ↦ hloc hs y) (fun y _ ↦ hinit y)
    (fun _ _ _ hy ↦ by simp at hy) ht (mem_univ x)

/-- **Lower ODE–PDE comparison principle on a compact space.**

Dual of `le_of_deriv_le_of_locallyLipschitzOn_of_isLocalMax`: if `deriv φ t ≤ F t (φ t)` on
`(a, b)`, `F t (u t x) ≤ ∂ₜu` at every spatial local minimum where `u t x < φ t`, and `φ a ≤ u a`,
then `φ t ≤ u t x` on `[a, b] × X`. -/
theorem ge_of_le_deriv_of_locallyLipschitzOn_of_isLocalMin [CompactSpace X] {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    {φ : ℝ → ℝ} (hφcont : ContinuousOn φ (Icc a b))
    (hφdiff : ∀ ⦃t⦄, t ∈ Ioo a b → DifferentiableAt ℝ φ t)
    (hφ : ∀ ⦃t⦄, t ∈ Ioo a b → deriv φ t ≤ F t (φ t))
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, IsLocalMin (u t) x → u t x < φ t →
      F t (u t x) ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, φ a ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, φ t ≤ u t x := fun t ht x ↦
  ge_of_le_hasDerivWithinAt_Iic_of_locallyLipschitzOn_ge_parabolicBoundary
    (u' := fun s y ↦ deriv (fun r ↦ u r y) s) (φ' := deriv φ) isCompact_univ hF hφcont
    (fun _ hs ↦ (hφdiff hs).hasDerivAt.hasDerivWithinAt) hφ hcont
    (fun _ hs y _ ↦ (hdiff hs y).hasDerivAt.hasDerivWithinAt)
    (fun _ hs y _ ↦ hloc hs y) (fun y _ ↦ hinit y)
    (fun _ _ _ hy ↦ by simp at hy) ht (mem_univ x)

end ODEComparison

section Barriers

variable {X : Type*} [TopologicalSpace X] {K : Set X} {a b : ℝ} {u : ℝ → X → ℝ}

/-- **Parabolic Gronwall upper bound on a cylinder.**

For any real constants `m` and `k` (of any signs), if `u ≤ m * exp (k * (t - a))` on the parabolic
boundary of `[a, b] × K` (in particular `u a ≤ m` on `K`) and `∂ₜu ≤ k * u` at every interior
spatial local maximum lying above `m * exp (k * (t - a))`, then `u t x ≤ m * exp (k * (t - a))` on
all of `[a, b] × K`. -/
theorem le_mul_exp_of_deriv_le_mul_of_isLocalMax_le_parabolicBoundary (hK : IsCompact K)
    {m k : ℝ} (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K → IsLocalMax (u t) x →
      m * Real.exp (k * (t - a)) < u t x → deriv (fun s ↦ u s x) t ≤ k * u t x)
    (hinit : ∀ ⦃x⦄, x ∈ K → u a x ≤ m)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K →
      u t x ≤ m * Real.exp (k * (t - a))) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → u t x ≤ m * Real.exp (k * (t - a)) := by
  have hF : LocallyLipschitzOn (Icc a b ×ˢ univ)
      (Function.uncurry fun _ r : ℝ ↦ k * r) := by
    refine (LipschitzWith.of_dist_le_mul (K := ⟨|k|, abs_nonneg k⟩)
      fun ⟨t₁, r₁⟩ ⟨t₂, r₂⟩ ↦ ?_).locallyLipschitz.locallyLipschitzOn
    simp only [Function.uncurry_apply_pair, Real.dist_eq, ← mul_sub, abs_mul, Prod.dist_eq]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg k)
  have hφderiv (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ m * Real.exp (k * (s - a)))
        (k * (m * Real.exp (k * (t - a)))) t := by
    have hlin : HasDerivAt (fun s : ℝ ↦ k * (s - a)) k t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul k
    convert hlin.exp.const_mul m using 1
    ring
  exact le_of_hasDerivWithinAt_Iic_le_of_locallyLipschitzOn_le_parabolicBoundary
    (u' := fun s y ↦ deriv (fun r ↦ u r y) s) (F := fun _ r ↦ k * r)
    (φ := fun s ↦ m * Real.exp (k * (s - a)))
    (φ' := fun s ↦ k * (m * Real.exp (k * (s - a))))
    hK hF (by fun_prop) (fun s _ ↦ (hφderiv s).hasDerivWithinAt) (fun _ _ ↦ le_rfl) hcont
    (fun s hs y hy ↦ (hdiff hs hy).hasDerivAt.hasDerivWithinAt) hloc
    (fun x hx ↦ by simpa using hinit hx) hlat

/-- **Parabolic Gronwall upper bound on a compact space.** -/
theorem le_mul_exp_of_deriv_le_mul_of_isLocalMax [CompactSpace X] {m k : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, IsLocalMax (u t) x →
      m * Real.exp (k * (t - a)) < u t x → deriv (fun s ↦ u s x) t ≤ k * u t x)
    (hinit : ∀ x, u a x ≤ m) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, u t x ≤ m * Real.exp (k * (t - a)) := fun t ht x ↦
  le_mul_exp_of_deriv_le_mul_of_isLocalMax_le_parabolicBoundary isCompact_univ hcont
    (fun s hs y _ ↦ hdiff hs y) (fun s hs y _ ↦ hloc hs y) (fun y _ ↦ hinit y)
    (fun _ _ _ hy ↦ by simp at hy) ht (mem_univ x)

/-- **Parabolic Gronwall lower bound on a compact space.**

Dual of `le_mul_exp_of_deriv_le_mul_of_isLocalMax`: for any real constants `m` and `k`, if
`m ≤ u a` and `k * u ≤ ∂ₜu` at every spatial local minimum below `m * exp (k * (t - a))`, then
`m * exp (k * (t - a)) ≤ u t x` on `[a, b] × X`. -/
theorem mul_exp_le_of_mul_le_deriv_of_isLocalMin [CompactSpace X] {m k : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, IsLocalMin (u t) x →
      u t x < m * Real.exp (k * (t - a)) → k * u t x ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, m ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, m * Real.exp (k * (t - a)) ≤ u t x := by
  intro t ht x
  have h := le_mul_exp_of_deriv_le_mul_of_isLocalMax (u := -u) (m := -m) (k := k) hcont.neg
    (fun s hs y ↦ (hdiff hs y).neg)
    (fun s hs y hmax hlt ↦ by
      have hmin : IsLocalMin (u s) y := hmax.mono fun z hz ↦ by
        simp only [Pi.neg_apply] at hz
        linarith
      simp only [Pi.neg_apply, deriv.fun_neg] at hlt ⊢
      linarith [hloc hs y hmin (by linarith)])
    (fun y ↦ neg_le_neg (hinit y)) ht x
  simp only [Pi.neg_apply] at h
  linarith

/-- **Constant-drift upper bound on a compact space.**

If `u a ≤ m` and `∂ₜu ≤ c` at every spatial local maximum above `m + c * (t - a)`, then
`u t x ≤ m + c * (t - a)` on `[a, b] × X`. -/
theorem le_add_mul_sub_of_deriv_le_const_of_isLocalMax [CompactSpace X] {m c : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, IsLocalMax (u t) x →
      m + c * (t - a) < u t x → deriv (fun s ↦ u s x) t ≤ c)
    (hinit : ∀ x, u a x ≤ m) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, u t x ≤ m + c * (t - a) := by
  have hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry fun _ _ : ℝ ↦ c) :=
    (LocallyLipschitz.const c).locallyLipschitzOn
  have hφderiv (t : ℝ) : HasDerivAt (fun s : ℝ ↦ m + c * (s - a)) c t := by
    simpa using (((hasDerivAt_id t).sub_const a).const_mul c).const_add m
  exact le_of_deriv_le_of_locallyLipschitzOn_of_isLocalMax (F := fun _ _ ↦ c) hF
    (by fun_prop) (fun s _ ↦ (hφderiv s).differentiableAt)
    (fun s _ ↦ (hφderiv s).deriv.ge) hcont hdiff hloc
    (fun x ↦ by simpa using hinit x)

/-- **Constant-drift lower bound on a compact space.** -/
theorem add_mul_sub_le_of_const_le_deriv_of_isLocalMin [CompactSpace X] {m c : ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, IsLocalMin (u t) x →
      u t x < m + c * (t - a) → c ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, m ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, m + c * (t - a) ≤ u t x := by
  intro t ht x
  have h := le_add_mul_sub_of_deriv_le_const_of_isLocalMax (u := -u) (m := -m) (c := -c) hcont.neg
    (fun s hs y ↦ (hdiff hs y).neg)
    (fun s hs y hmax hlt ↦ by
      have hmin : IsLocalMin (u s) y := hmax.mono fun z hz ↦ by
        simp only [Pi.neg_apply] at hz
        linarith
      simp only [Pi.neg_apply, deriv.fun_neg] at hlt ⊢
      linarith [hloc hs y hmin (by linarith)])
    (fun y ↦ neg_le_neg (hinit y)) ht x
  simp only [Pi.neg_apply] at h
  linarith

/-- **Preservation of nonnegativity on a cylinder.**

Let `F` be locally Lipschitz on `[a, b] × ℝ` with `0 ≤ F t 0` for `t ∈ (a, b)`. If `0 ≤ u` on the
parabolic boundary of `[a, b] × K` and `F t (u t x) ≤ u' t x` at every interior spatial local
minimum where `u t x < 0`, then `0 ≤ u t x` on all of `[a, b] × K`. -/
theorem nonneg_of_le_hasDerivWithinAt_Iic_of_locallyLipschitzOn_nonneg_parabolicBoundary
    (hK : IsCompact K) {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    (hF0 : ∀ ⦃t⦄, t ∈ Ioo a b → 0 ≤ F t 0)
    {u' : ℝ → X → ℝ} (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ K))
    (hderiv : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      HasDerivWithinAt (fun s ↦ u s x) (u' t x) (Iic t) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ ⦃x⦄, x ∈ interior K →
      IsLocalMin (u t) x → u t x < 0 → F t (u t x) ≤ u' t x)
    (hinit : ∀ ⦃x⦄, x ∈ K → 0 ≤ u a x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ frontier K → 0 ≤ u t x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ ⦃x⦄, x ∈ K → 0 ≤ u t x :=
  ge_of_le_hasDerivWithinAt_Iic_of_locallyLipschitzOn_ge_parabolicBoundary
    (φ := fun _ ↦ 0) (φ' := fun _ ↦ 0) hK hF continuousOn_const
    (fun s _ ↦ hasDerivWithinAt_const s (Iic s) 0) hF0 hcont hderiv hloc hinit hlat

/-- **Preservation of nonnegativity on a compact space.** -/
theorem nonneg_of_le_deriv_of_locallyLipschitzOn_of_isLocalMin [CompactSpace X] {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    (hF0 : ∀ ⦃t⦄, t ∈ Ioo a b → 0 ≤ F t 0)
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, IsLocalMin (u t) x → u t x < 0 →
      F t (u t x) ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, 0 ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Icc a b → ∀ x, 0 ≤ u t x := fun t ht x ↦
  nonneg_of_le_hasDerivWithinAt_Iic_of_locallyLipschitzOn_nonneg_parabolicBoundary
    (u' := fun s y ↦ deriv (fun r ↦ u r y) s) isCompact_univ hF hF0 hcont
    (fun _ hs y _ ↦ (hdiff hs y).hasDerivAt.hasDerivWithinAt)
    (fun _ hs y _ ↦ hloc hs y) (fun y _ ↦ hinit y)
    (fun _ _ _ hy ↦ by simp at hy) ht (mem_univ x)

/-- **Strict positive improvement under an inward reaction at zero.**

On a compact space `X`, let `F` be locally Lipschitz on `[a, b] × ℝ` and satisfy an inward lower
bound `δ ≤ F t 0` on `(a, b)` for some `δ > 0`. If `0 ≤ u a` and `F t (u t x) ≤ ∂ₜu` at every
spatial local minimum on `(a, b) × X`, then `0 < u t x` at every later time `t ∈ (a, b]` and every
`x : X`. -/
theorem pos_of_le_deriv_of_locallyLipschitzOn_of_isLocalMin [CompactSpace X] {F : ℝ → ℝ → ℝ}
    (hF : LocallyLipschitzOn (Icc a b ×ˢ univ) (Function.uncurry F))
    {δ : ℝ} (hδ : 0 < δ) (hF0 : ∀ ⦃t⦄, t ∈ Ioo a b → δ ≤ F t 0)
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, IsLocalMin (u t) x →
      F t (u t x) ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, 0 ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Ioc a b → ∀ x, 0 < u t x := by
  intro t ht x
  -- Build the global ODE subsolution `φ s = (δ₀ / k) * (1 - exp (-k * (s - a))) ∈ [0, 1]`.
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_Icc_of_locallyLipschitzOn hF 1
  set k : ℝ := (L : ℝ) + 1
  have hk1 : 1 ≤ k := by
    dsimp only [k]
    linarith [(L : ℝ≥0).coe_nonneg]
  have hk : 0 < k := zero_lt_one.trans_le hk1
  set δ₀ : ℝ := min δ 1
  have hδ₀ : 0 < δ₀ := lt_min hδ zero_lt_one
  let φ : ℝ → ℝ := fun s ↦ (δ₀ / k) * (1 - Real.exp (-k * (s - a)))
  have hφderiv (s : ℝ) : HasDerivAt φ (δ₀ * Real.exp (-k * (s - a))) s :=
    (((((hasDerivAt_id s).sub_const a).const_mul (-k)).exp).const_sub 1).const_mul (δ₀ / k)
      |>.congr_deriv (by dsimp only [id]; field_simp)
  have hφsub : ∀ ⦃s⦄, s ∈ Ioo a b → deriv φ s ≤ F s (φ s) := by
    intro s hs
    have hexp_le : Real.exp (-k * (s - a)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hs.1, hk])
    have hφ_nonneg : 0 ≤ φ s :=
      mul_nonneg (div_nonneg hδ₀.le hk.le) (sub_nonneg.mpr hexp_le)
    have hφ_le_one : φ s ≤ 1 := by
      have h1 : 1 - Real.exp (-k * (s - a)) ≤ 1 := by linarith [Real.exp_pos (-k * (s - a))]
      have h2 : δ₀ / k ≤ 1 := (div_le_one hk).mpr ((min_le_right δ 1).trans hk1)
      nlinarith [mul_le_mul h2 h1 (sub_nonneg.mpr hexp_le) zero_le_one]
    have hlip : F s 0 - F s (φ s) ≤ (L : ℝ) * φ s := by
      calc F s 0 - F s (φ s)
          ≤ |F s 0 - F s (φ s)| := le_abs_self _
        _ = dist (F s 0) (F s (φ s)) := (Real.dist_eq _ _).symm
        _ ≤ (L : ℝ) * dist 0 (φ s) :=
          (hL (Ioo_subset_Icc_self hs)).dist_le_mul 0 ⟨by norm_num, by norm_num⟩
            (φ s) ⟨by linarith, hφ_le_one⟩
        _ = (L : ℝ) * φ s := by
          rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hφ_nonneg]
    have hrel : δ₀ * Real.exp (-k * (s - a)) = δ₀ - k * φ s := by
      dsimp only [φ]
      field_simp
      ring
    rw [(hφderiv s).deriv, hrel]
    have hLk : (L : ℝ) * φ s ≤ k * φ s :=
      mul_le_mul_of_nonneg_right (by dsimp only [k]; linarith) hφ_nonneg
    linarith [min_le_left δ 1, hF0 hs, hLk]
  have hle := ge_of_le_deriv_of_locallyLipschitzOn_of_isLocalMin hF
    (by fun_prop) (fun s _ ↦ (hφderiv s).differentiableAt) hφsub hcont hdiff
    (fun s hs y hmin _ ↦ hloc hs y hmin)
    (fun y ↦ by simpa [φ] using hinit y) ⟨ht.1.le, ht.2⟩ x
  have hφpos : 0 < φ t := by
    refine mul_pos (div_pos hδ₀ hk) (sub_pos.mpr ?_)
    exact Real.exp_lt_one_iff.mpr (by nlinarith [ht.1, hk])
  exact hφpos.trans_le hle

/-- **Finite-time blow-up bound for a quadratic lower reaction on a compact space.**

On a nonempty compact space `X`, let `c > 0` and `ρ > 0`. Suppose `u` is continuous on
`[a, b] × X` and differentiable in time on `(a, b) × X`, with `c * (u t x) ^ 2 ≤ ∂ₜu` at every
spatial local minimum on `(a, b) × X` and `ρ ≤ u a` everywhere on `X`. Then the existence interval
satisfies `b - a < (c * ρ)⁻¹` (equivalently `c * ρ * (b - a) < 1`). -/
theorem sub_lt_inv_mul_of_mul_sq_le_deriv_of_isLocalMin [CompactSpace X] [Nonempty X]
    {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ)
    (hcont : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ univ))
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hloc : ∀ ⦃t⦄, t ∈ Ioo a b → ∀ x, IsLocalMin (u t) x →
      c * u t x ^ 2 ≤ deriv (fun s ↦ u s x) t)
    (hinit : ∀ x, ρ ≤ u a x) :
    b - a < (c * ρ)⁻¹ := by
  by_contra! hge
  -- At `T = a + (c * ρ)⁻¹ ≤ b`, multiplying the barrier bound by `1 - c * ρ * (τ - a) > 0`
  -- on `[a, T)` and letting `τ → T⁻` yields `ρ ≤ 0`.
  have hcρ : 0 < c * ρ := mul_pos hc hρ
  have hinv : 0 < (c * ρ)⁻¹ := inv_pos.mpr hcρ
  set T : ℝ := a + (c * ρ)⁻¹
  have haT : a < T := by linarith
  have hTb : T ≤ b := by linarith
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hprod : ∀ τ ∈ Ico a T, ρ ≤ u τ x₀ * (1 - c * ρ * (τ - a)) := by
    intro τ hτ
    have hden : 0 < 1 - c * ρ * (τ - a) := by
      have : c * ρ * (τ - a) < c * ρ * (c * ρ)⁻¹ :=
        mul_lt_mul_of_pos_left (by dsimp only [T] at hτ; linarith [hτ.2]) hcρ
      rw [mul_inv_cancel₀ hcρ.ne'] at this
      linarith
    have hτb : τ < b := lt_of_lt_of_le hτ.2 hTb
    have hle := div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin (a := a) (b := τ) hc.le hden
      (hcont.mono (prod_mono (Icc_subset_Icc_right hτb.le) Subset.rfl))
      (fun s hs y ↦ hdiff ⟨hs.1, lt_trans hs.2 hτb⟩ y)
      (fun s hs y hmin _ ↦ hloc ⟨hs.1, lt_trans hs.2 hτb⟩ y hmin)
      hinit ⟨hτ.1, le_rfl⟩ x₀
    exact (div_le_iff₀ hden).mp hle
  have huT : ContinuousOn (fun s ↦ u s x₀) (Icc a T) :=
    hcont.comp (continuousOn_id.prodMk continuousOn_const) fun s hs ↦
      ⟨⟨hs.1, hs.2.trans hTb⟩, mem_univ x₀⟩
  have hgT : ContinuousWithinAt (fun s ↦ u s x₀ * (1 - c * ρ * (s - a))) (Ico a T) T :=
    ((huT.mul (continuousOn_const.sub (continuousOn_const.mul
      (continuousOn_id.sub continuousOn_const)))) T ⟨haT.le, le_rfl⟩).mono Ico_subset_Icc_self
  have hlim : ρ ≤ u T x₀ * (1 - c * ρ * (T - a)) :=
    ContinuousWithinAt.closure_le (f := fun _ : ℝ ↦ ρ)
      (g := fun s ↦ u s x₀ * (1 - c * ρ * (s - a)))
      (by rw [closure_Ico haT.ne]; exact ⟨haT.le, le_rfl⟩)
      continuousWithinAt_const hgT hprod
  have hzero : 1 - c * ρ * (T - a) = 0 := by
    dsimp only [T]
    rw [add_sub_cancel_left, mul_inv_cancel₀ hcρ.ne', sub_self]
  rw [hzero, mul_zero] at hlim
  exact hρ.not_ge hlim

end Barriers

end TauCeti
