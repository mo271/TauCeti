/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.CStarAlgebra.State.Space
import TauCeti.Analysis.CStarAlgebra.State.Spectrum
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.HahnBanach
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Unitization extension and Jordan decomposition of functionals on C⋆-algebras

Every positive continuous linear functional `f : A →P[ℂ] ℂ` on a (possibly nonunital) C⋆-algebra
extends canonically to a positive continuous linear functional
`PositiveContinuousLinearMap.unitizationExtend f : Unitization ℂ A →P[ℂ] ℂ` of the same norm,
given by `g (z, a) = z * ‖f‖ + f a`. Along an increasing approximate unit `e` of `A`, the norm
bound `‖f (z • e + a * e)‖ ≤ ‖f‖ * ‖(z, a)‖` passes to the limit to show `‖g‖ = ‖f‖ = g 1`,
whence positivity follows from `ContinuousLinearMap.monotone_iff_opNorm_eq_map_one`.

Every bounded Hermitian (`φ (star a) = star (φ a)`) linear functional `φ : A →L[ℂ] ℂ` on a
(possibly nonunital) C⋆-algebra admits a norm-preserving Jordan decomposition `φ = φ₁ - φ₂` into
positive continuous linear functionals satisfying `‖φ₁‖ + ‖φ₂‖ = ‖φ‖`,
`ContinuousLinearMap.exists_positiveContinuousLinearMap_sub_of_map_star`. For unital `A`, the set
`{t • ω₁ - (1 - t) • ω₂ | t ∈ [0, 1], ω₁, ω₂ ∈ stateSpace A}` is convex and weak-* compact;
Hahn–Banach separation in `WeakDual ℂ A` together with spectral norm-attaining states shows that it
contains every Hermitian functional of norm at most `1`. For nonunital `A`, Hahn–Banach extends
`φ` with the same norm to `Unitization ℂ A`, symmetrization preserves the norm, and restricting the
unital decomposition back to `A` preserves the sum of the norms.

Splitting an arbitrary `φ : A →L[ℂ] ℂ` into its Hermitian real and imaginary parts yields a
four-term decomposition into positive continuous linear functionals,
`ContinuousLinearMap.exists_positiveContinuousLinearMap_decomp`. In particular, weak convergence in
a C⋆-algebra is completely tested by positive continuous linear functionals,
`TauCeti.CStarAlgebra.tendsto_toWeakSpace_iff_forall_positiveContinuousLinearMap`.

## References

* B. Blackadar, *Operator Algebras*, Section II.6.3.
* G. K. Pedersen, *C*-Algebras and Their Automorphism Groups*, Section 3.2.
* M. Takesaki, *Theory of Operator Algebras I*, Theorem III.2.1.
-/

public section

noncomputable section

open Filter Set Topology Unitization
open scoped CStarAlgebra ComplexOrder

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The underlying continuous linear functional `(z, a) ↦ z * ‖f‖ + f a` on `Unitization ℂ A`. -/
private def unitizationExtendCLM (f : A →P[ℂ] ℂ) : Unitization ℂ A →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => x.fst * (‖(f : A →L[ℂ] ℂ)‖ : ℂ) + f x.snd
      map_add' := fun x y => by
        simp only [Unitization.fst_add, Unitization.snd_add, map_add]
        ring
      map_smul' := fun c x => by
        simp only [Unitization.fst_smul, Unitization.snd_smul, smul_eq_mul, map_smul,
          RingHom.id_apply]
        ring }
    ‖(f : A →L[ℂ] ℂ)‖ fun x => by
      have hl := CStarAlgebra.increasingApproximateUnit A
      have := hl.neBot
      have hlim : Tendsto (fun e : A => f (x.fst • e + x.snd * e))
          (CStarAlgebra.approximateUnit A)
          (𝓝 (x.fst * (‖(f : A →L[ℂ] ℂ)‖ : ℂ) + f x.snd)) := by
        have h1 : Tendsto (fun e : A => x.fst * f e) (CStarAlgebra.approximateUnit A)
            (𝓝 (x.fst * (‖(f : A →L[ℂ] ℂ)‖ : ℂ))) :=
          (f.tendsto_nhds_opNorm hl).const_mul x.fst
        have h2 : Tendsto (fun e : A => f (x.snd * e)) (CStarAlgebra.approximateUnit A)
            (𝓝 (f x.snd)) :=
          ((f : A →L[ℂ] ℂ).continuous.tendsto x.snd).comp (hl.tendsto_mul_left x.snd)
        exact (h1.add h2).congr fun e => by simp [map_add, map_smul]
      refine le_of_tendsto hlim.norm ?_
      filter_upwards [hl.eventually_norm] with e he
      have hmul : ((x.fst • e + x.snd * e : A) : A⁺¹) = x * (e : A⁺¹) := by
        ext <;> simp
      calc ‖f (x.fst • e + x.snd * e)‖
          ≤ ‖(f : A →L[ℂ] ℂ)‖ * ‖x.fst • e + x.snd * e‖ :=
            (f : A →L[ℂ] ℂ).le_opNorm _
        _ = ‖(f : A →L[ℂ] ℂ)‖ * ‖x * (e : A⁺¹)‖ := by
            rw [← Unitization.norm_inr (𝕜 := ℂ), hmul]
        _ ≤ ‖(f : A →L[ℂ] ℂ)‖ * (‖x‖ * ‖(e : A⁺¹)‖) := by
            gcongr; exact norm_mul_le _ _
        _ ≤ ‖(f : A →L[ℂ] ℂ)‖ * ‖x‖ := by
            rw [Unitization.norm_inr]
            gcongr
            exact mul_le_of_le_one_right (norm_nonneg x) he

private theorem opNorm_unitizationExtendCLM (f : A →P[ℂ] ℂ) :
    ‖unitizationExtendCLM f‖ = ‖(f : A →L[ℂ] ℂ)‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _) ?_
  have h1 := (unitizationExtendCLM f).le_opNorm (1 : A⁺¹)
  have hval : unitizationExtendCLM f 1 = (‖(f : A →L[ℂ] ℂ)‖ : ℂ) := by
    simp [unitizationExtendCLM]
  rw [hval, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), norm_one, mul_one] at h1
  exact h1

/-- Canonical norm-preserving extension of a positive continuous linear functional `f : A →P[ℂ] ℂ`
on a possibly nonunital C⋆-algebra to the unitization `Unitization ℂ A`, given by
`(z, a) ↦ z * ‖f‖ + f a`. -/
def unitizationExtend (f : A →P[ℂ] ℂ) : Unitization ℂ A →P[ℂ] ℂ :=
  { toContinuousLinearMap := unitizationExtendCLM f
    monotone' := ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.2 <| by
      rw [opNorm_unitizationExtendCLM]
      simp [unitizationExtendCLM] }

/-- Evaluation formula for the canonical extension of a positive functional to `Unitization ℂ A`. -/
theorem unitizationExtend_apply (f : A →P[ℂ] ℂ) (x : Unitization ℂ A) :
    f.unitizationExtend x = x.fst * (‖(f : A →L[ℂ] ℂ)‖ : ℂ) + f x.snd := by
  rfl

/-- The canonical unitization extension agrees with `f` on `A`. -/
@[simp]
theorem unitizationExtend_inr (f : A →P[ℂ] ℂ) (a : A) :
    f.unitizationExtend (a : Unitization ℂ A) = f a := by
  simp [unitizationExtend_apply]

/-- The canonical unitization extension evaluates at `1` to the norm of `f`. -/
@[simp]
theorem unitizationExtend_one (f : A →P[ℂ] ℂ) :
    f.unitizationExtend 1 = (‖(f : A →L[ℂ] ℂ)‖ : ℂ) := by
  simp [unitizationExtend_apply]

/-- Extending a positive continuous linear functional to the unitization preserves its norm. -/
@[simp]
theorem opNorm_unitizationExtend (f : A →P[ℂ] ℂ) :
    ‖(f.unitizationExtend : Unitization ℂ A →L[ℂ] ℂ)‖ = ‖(f : A →L[ℂ] ℂ)‖ :=
  opNorm_unitizationExtendCLM f

/-- Pulling `f.unitizationExtend` back along `Unitization.inrNonUnitalStarAlgHom` recovers `f`. -/
@[simp]
theorem unitizationExtend_comp_inr (f : A →P[ℂ] ℂ) :
    f.unitizationExtend.comp (.ofClass (Unitization.inrNonUnitalStarAlgHom ℂ A)) = f := by
  ext a
  exact f.unitizationExtend_inr a

end PositiveContinuousLinearMap

section JordanHelpers

/-- The adjoint functional `a ↦ star (φ (star a))` of a continuous complex-linear functional. -/
private def starConjFunctional {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [StarAddMonoid E] [StarModule ℂ E] [NormedStarGroup E] (φ : E →L[ℂ] ℂ) : E →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => star (φ (star a))
      map_add' := fun a b => by simp [star_add]
      map_smul' := fun c a => by simp [star_smul, star_mul, mul_comm] }
    ‖φ‖ fun a => by
      simpa [norm_star] using φ.le_opNorm (star a)

private theorem opNorm_starConjFunctional_le {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] [StarAddMonoid E] [StarModule ℂ E] [NormedStarGroup E] (φ : E →L[ℂ] ℂ) :
    ‖starConjFunctional φ‖ ≤ ‖φ‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg φ) _

/-- The Hermitian part `2⁻¹ • (φ + φ*)` of a continuous complex-linear functional. -/
private def hermitianPart {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [StarAddMonoid E] [StarModule ℂ E] [NormedStarGroup E] (φ : E →L[ℂ] ℂ) : E →L[ℂ] ℂ :=
  ((2 : ℂ)⁻¹) • (φ + starConjFunctional φ)

private theorem hermitianPart_star {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [StarAddMonoid E] [StarModule ℂ E] [NormedStarGroup E] (φ : E →L[ℂ] ℂ) (a : E) :
    hermitianPart φ (star a) = star (hermitianPart φ a) := by
  simp only [hermitianPart, smul_apply, add_apply,
    starConjFunctional, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, star_star,
    smul_eq_mul, Complex.star_def, map_mul, map_inv₀, map_ofNat, map_add, starRingEnd_self_apply]
  ring

private theorem opNorm_hermitianPart_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [StarAddMonoid E] [StarModule ℂ E] [NormedStarGroup E] (φ : E →L[ℂ] ℂ) :
    ‖hermitianPart φ‖ ≤ ‖φ‖ := by
  calc ‖hermitianPart φ‖ = ‖(2 : ℂ)⁻¹‖ * ‖φ + starConjFunctional φ‖ := norm_smul _ _
    _ ≤ 2⁻¹ * (‖φ‖ + ‖starConjFunctional φ‖) := by
        simp only [norm_inv, Complex.norm_ofNat]; gcongr; exact norm_add_le _ _
    _ ≤ 2⁻¹ * (‖φ‖ + ‖φ‖) := by gcongr; exact opNorm_starConjFunctional_le φ
    _ = ‖φ‖ := by ring

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Convex combinations `t • ω₁ - (1 - t) • ω₂` of states and negated states, used to prove the
Jordan decomposition on a unital C⋆-algebra via weak-* separation. -/
private def stateDiffHull (A : Type*) [CStarAlgebra A] [PartialOrder A] : Set (WeakDual ℂ A) :=
  {ψ | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ ω₁ ∈ TauCeti.stateSpace A, ∃ ω₂ ∈ TauCeti.stateSpace A,
    ψ = t • ω₁ - (1 - t) • ω₂}

private theorem isCompact_stateDiffHull : IsCompact (stateDiffHull A) := by
  have himg : stateDiffHull A =
      (fun p : ℝ × WeakDual ℂ A × WeakDual ℂ A => p.1 • p.2.1 - (1 - p.1) • p.2.2) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ TauCeti.stateSpace A ×ˢ TauCeti.stateSpace A) := by
    ext ψ
    simp only [stateDiffHull, mem_ofPred_eq, mem_image, mem_prod, Prod.exists]
    constructor
    · rintro ⟨t, ht, ω₁, h₁, ω₂, h₂, rfl⟩
      exact ⟨t, ω₁, ω₂, ⟨ht, h₁, h₂⟩, rfl⟩
    · rintro ⟨t, ω₁, ω₂, ⟨ht, h₁, h₂⟩, rfl⟩
      exact ⟨t, ht, ω₁, h₁, ω₂, h₂, rfl⟩
  rw [himg]
  refine (isCompact_Icc.prod
    (TauCeti.isCompact_stateSpace.prod TauCeti.isCompact_stateSpace)).image ?_
  have hsmul : Continuous fun p : ℝ × WeakDual ℂ A => p.1 • p.2 := by
    have h : (fun p : ℝ × WeakDual ℂ A => p.1 • p.2) =
        fun p => (p.1 : ℂ) • p.2 := funext fun p => WeakDual.real_smul_eq_coe_smul p.1 p.2
    rw [h]
    exact (Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd
  exact (hsmul.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).sub
    (hsmul.comp ((continuous_const.sub continuous_fst).prodMk (continuous_snd.comp continuous_snd)))

private theorem convex_stateDiffHull : Convex ℝ (stateDiffHull A) := by
  rintro _ ⟨t, ht, ω₁, h₁, ω₂, h₂, rfl⟩ _ ⟨t', ht', ω₁', h₁', ω₂', h₂', rfl⟩ a b ha hb hab
  let s : ℝ := a * t + b * t'
  have hs0 : 0 ≤ s := by positivity [ht.1, ht'.1]
  have hs1 : s ≤ 1 := by
    calc a * t + b * t' ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left ht.2 ha) (mul_le_mul_of_nonneg_left ht'.2 hb)
      _ = 1 := by linarith
  have hpos_part : ∃ η₁ ∈ TauCeti.stateSpace A, s • η₁ = (a * t) • ω₁ + (b * t') • ω₁' := by
    by_cases hs : s = 0
    · have hat : a * t = 0 := by nlinarith [ht.1, ht'.1]
      have hbt : b * t' = 0 := by nlinarith [ht.1, ht'.1]
      exact ⟨ω₁, h₁, DFunLike.ext _ _ fun x => by simp [hs, hat, hbt]⟩
    · refine ⟨(a * t / s) • ω₁ + (b * t' / s) • ω₁',
        TauCeti.convex_stateSpace h₁ h₁' (by positivity [ht.1]) (by positivity [ht'.1])
          (by field_simp; rfl), DFunLike.ext _ _ fun x => ?_⟩
      simp only [add_apply, WeakDual.real_smul_apply]
      have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
      push_cast
      field_simp [hsc]
  have hneg_part : ∃ η₂ ∈ TauCeti.stateSpace A,
      (1 - s) • η₂ = (a * (1 - t)) • ω₂ + (b * (1 - t')) • ω₂' := by
    by_cases hs : 1 - s = 0
    · have hat : a * (1 - t) = 0 := by nlinarith [ht.2, ht'.2]
      have hbt : b * (1 - t') = 0 := by nlinarith [ht.2, ht'.2]
      exact ⟨ω₂, h₂, DFunLike.ext _ _ fun x => by simp [hs, hat, hbt]⟩
    · refine ⟨(a * (1 - t) / (1 - s)) • ω₂ + (b * (1 - t') / (1 - s)) • ω₂',
        TauCeti.convex_stateSpace h₂ h₂' (by positivity [sub_nonneg.mpr ht.2, sub_nonneg.mpr hs1])
          (by positivity [sub_nonneg.mpr ht'.2, sub_nonneg.mpr hs1]) (by field_simp; linarith),
        DFunLike.ext _ _ fun x => ?_⟩
      simp only [add_apply, WeakDual.real_smul_apply]
      have hsc : (1 - (s : ℂ)) ≠ 0 := by
        exact_mod_cast hs
      push_cast
      field_simp [hsc]
  obtain ⟨η₁, hη₁, hη₁_eq⟩ := hpos_part
  obtain ⟨η₂, hη₂, hη₂_eq⟩ := hneg_part
  refine ⟨s, ⟨hs0, hs1⟩, η₁, hη₁, η₂, hη₂, DFunLike.ext _ _ fun x => ?_⟩
  have hsub (f g : WeakDual ℂ A) : (f - g) x = f x - g x := rfl
  have h1x := congrArg (fun ψ : WeakDual ℂ A => ψ x) hη₁_eq
  have h2x := congrArg (fun ψ : WeakDual ℂ A => ψ x) hη₂_eq
  simp only [add_apply, hsub, WeakDual.real_smul_apply] at h1x h2x ⊢
  rw [h1x, h2x]
  push_cast
  ring

/-- Every Hermitian functional of norm at most `1` on a nontrivial unital C⋆-algebra lies in
`stateDiffHull A`. -/
private theorem toWeakDual_mem_stateDiffHull [Nontrivial A] {φ : A →L[ℂ] ℂ}
    (hφ_star : ∀ a, φ (star a) = star (φ a)) (hφ_norm : ‖φ‖ ≤ 1) :
    StrongDual.toWeakDual φ ∈ stateDiffHull A := by
  by_contra hnot
  let K' : Set (WeakBilin (topDualPairing ℂ A)) := stateDiffHull A
  let φ' : WeakBilin (topDualPairing ℂ A) := StrongDual.toWeakDual φ
  have hK'_conv : Convex ℝ K' := fun _ hu _ hv _ _ ha hb hab =>
    convex_stateDiffHull (A := A) hu hv ha hb hab
  have hK'_closed : IsClosed K' := (isCompact_stateDiffHull (A := A)).isClosed
  have hnot' : φ' ∉ K' := hnot
  obtain ⟨l, u, hlK', hlu'⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) (E := WeakBilin (topDualPairing ℂ A))
      hK'_conv hK'_closed hnot'
  obtain ⟨a, ha⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℂ A) l
  have hlK : ∀ ψ ∈ stateDiffHull A, (ψ a).re < u := fun ψ hψ => by
    have h := hlK' ψ hψ
    rw [← ha] at h
    exact h
  have hlu : u < (φ a).re := by
    rw [← ha] at hlu'
    exact hlu'
  let b : A := ((2 : ℝ)⁻¹ : ℂ) • (a + star a)
  have hb_sa : IsSelfAdjoint b := by
    rw [IsSelfAdjoint, star_smul, star_add, star_star, add_comm]
    simp [b]
  have hre_eq : ∀ ψ : A →L[ℂ] ℂ, (∀ x, ψ (star x) = star (ψ x)) → (ψ b).re = (ψ a).re := by
    intro ψ hψ
    have hval : ψ b = (((2 : ℝ)⁻¹ : ℝ) : ℂ) * (ψ a + star (ψ a)) := by
      simp [b, map_smul, map_add, hψ a]
      ring
    rw [hval, Complex.re_ofReal_mul]
    simp
    ring
  have hstate_star : ∀ ω ∈ TauCeti.stateSpace A,
      ∀ x : A, WeakDual.toStrongDual ω (star x) = star (WeakDual.toStrongDual ω x) := by
    intro ω hω x
    let ω' : A →P[ℂ] ℂ := .mk₀ (WeakDual.toStrongDual ω)
      fun _ => TauCeti.map_nonneg_of_mem_stateSpace hω
    exact map_star ω' x
  have hstate_lt : ∀ ω ∈ TauCeti.stateSpace A, |(ω b).re| < u := by
    intro ω hω
    have hsub (f g : WeakDual ℂ A) (x : A) : (f - g) x = f x - g x := rfl
    have hneg (f : WeakDual ℂ A) (x : A) : (-f) x = -(f x) := rfl
    have hω_mem : ω ∈ stateDiffHull A :=
      ⟨1, ⟨zero_le_one, le_rfl⟩, ω, hω, ω, hω, DFunLike.ext _ _ fun x => by simp [hsub]⟩
    have hneg_mem : -ω ∈ stateDiffHull A :=
      ⟨0, ⟨le_rfl, zero_le_one⟩, ω, hω, ω, hω, DFunLike.ext _ _ fun x => by simp [hsub, hneg]⟩
    have hre_ω : (ω b).re = (ω a).re := hre_eq (WeakDual.toStrongDual ω) (hstate_star ω hω)
    rw [abs_lt]
    refine ⟨?_, by rw [hre_ω]; exact hlK ω hω_mem⟩
    have h1 := hlK (-ω) hneg_mem
    rw [hneg, Complex.neg_re] at h1
    linarith
  have hnorm_lt : ‖b‖ < u := by
    have hspec : ∃ r : ℝ, r ∈ spectrum ℝ b ∧ |r| = ‖b‖ := by
      rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum b hb_sa with h | h
      · exact ⟨‖b‖, h, abs_of_nonneg (norm_nonneg b)⟩
      · exact ⟨-‖b‖, h, by rw [abs_neg, abs_of_nonneg (norm_nonneg b)]⟩
    obtain ⟨r, hr_spec, hr_abs⟩ := hspec
    have := hb_sa.isStarNormal
    open TauCeti.CStarAlgebra in
    obtain ⟨ω, -, hω_norm, hω_pow⟩ :=
      exists_positiveContinuousLinearMap_apply_star_pow_mul_pow_eq_of_mem_spectrum
        (spectrum.algebraMap_mem ℂ hr_spec)
    have hωb : ω b = (r : ℂ) := by simpa using hω_pow 0 1
    have hω_mem : StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈ TauCeti.stateSpace A :=
      ω.toWeakDual_mem_stateSpace_iff.2 hω_norm
    have hlt := hstate_lt _ hω_mem
    simpa [StrongDual.toWeakDual_apply, hωb, hr_abs] using hlt
  have hφb : (φ b).re ≤ ‖b‖ := by
    calc (φ b).re ≤ ‖φ b‖ := Complex.re_le_norm (φ b)
      _ ≤ ‖φ‖ * ‖b‖ := φ.le_opNorm b
      _ ≤ 1 * ‖b‖ := by gcongr
      _ = ‖b‖ := one_mul _
  linarith [hre_eq φ hφ_star]

/-- **Jordan decomposition on a unital C⋆-algebra.** -/
private theorem exists_positiveContinuousLinearMap_sub_of_map_star_unital (φ : A →L[ℂ] ℂ)
    (hφ : ∀ a, φ (star a) = star (φ a)) :
    ∃ φ₁ φ₂ : A →P[ℂ] ℂ,
      (φ₁ : A →L[ℂ] ℂ) - (φ₂ : A →L[ℂ] ℂ) = φ ∧
      ‖(φ₁ : A →L[ℂ] ℂ)‖ + ‖(φ₂ : A →L[ℂ] ℂ)‖ = ‖φ‖ := by
  by_cases h0 : φ = 0
  · refine ⟨0, 0, by simp [h0], by simp [h0]⟩
  have hpos : 0 < ‖φ‖ := norm_pos_iff.2 h0
  have hnt : Nontrivial A := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    exact h0 (ContinuousLinearMap.ext fun a => by
      rw [Subsingleton.elim a 0, map_zero, zero_apply])
  let φ₀ : A →L[ℂ] ℂ := ((‖φ‖⁻¹ : ℝ) : ℂ) • φ
  have hφ₀_star : ∀ a, φ₀ (star a) = star (φ₀ a) := fun a => by
    simp [φ₀, hφ a]
  have hφ₀_norm : ‖φ₀‖ ≤ 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg φ)),
      inv_mul_cancel₀ hpos.ne']
  obtain ⟨t, ht, ω₁, h₁, ω₂, h₂, hdecomp⟩ :=
    toWeakDual_mem_stateDiffHull hφ₀_star hφ₀_norm
  let φ₁ : A →P[ℂ] ℂ := .mk₀ (((‖φ‖ * t : ℝ) : ℂ) • WeakDual.toStrongDual ω₁) fun a ha => by
    have hcoeff : 0 ≤ ((‖φ‖ * t : ℝ) : ℂ) := by
      exact_mod_cast mul_nonneg (norm_nonneg φ) ht.1
    simpa [smul_eq_mul] using mul_nonneg hcoeff (TauCeti.map_nonneg_of_mem_stateSpace h₁ ha)
  let φ₂ : A →P[ℂ] ℂ := .mk₀ (((‖φ‖ * (1 - t) : ℝ) : ℂ) • WeakDual.toStrongDual ω₂) fun a ha => by
    have hcoeff : 0 ≤ ((‖φ‖ * (1 - t) : ℝ) : ℂ) := by
      exact_mod_cast mul_nonneg (norm_nonneg φ) (sub_nonneg.2 ht.2)
    simpa [smul_eq_mul] using mul_nonneg hcoeff (TauCeti.map_nonneg_of_mem_stateSpace h₂ ha)
  refine ⟨φ₁, φ₂, ?_, ?_⟩
  · ext a
    have hsub (f g : WeakDual ℂ A) : (f - g) a = f a - g a := rfl
    have hpt := congrArg (fun ψ : WeakDual ℂ A => ψ a) hdecomp
    simp only [StrongDual.toWeakDual_apply, hsub, φ₀, smul_apply, smul_eq_mul,
      Complex.real_smul] at hpt
    have hmul := congrArg (fun z : ℂ => (‖φ‖ : ℂ) * z) hpt
    have hne : (‖φ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
    simp only [PositiveContinuousLinearMap.toContinuousLinearMap_mk₀, sub_apply, smul_apply,
      WeakDual.toStrongDual_apply, smul_eq_mul, φ₁, φ₂]
    rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul] at hmul
    rw [hmul]
    push_cast
    ring
  · have hn₁ : ‖(φ₁ : A →L[ℂ] ℂ)‖ = ‖φ‖ * t := by
      simp only [φ₁, PositiveContinuousLinearMap.toContinuousLinearMap_mk₀, norm_smul,
        Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (norm_nonneg φ) ht.1),
        TauCeti.norm_toStrongDual_of_mem_stateSpace h₁, mul_one]
    have hn₂ : ‖(φ₂ : A →L[ℂ] ℂ)‖ = ‖φ‖ * (1 - t) := by
      simp only [φ₂, PositiveContinuousLinearMap.toContinuousLinearMap_mk₀, norm_smul,
        Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (norm_nonneg φ) (sub_nonneg.2 ht.2)),
        TauCeti.norm_toStrongDual_of_mem_stateSpace h₂, mul_one]
    rw [hn₁, hn₂]
    ring

end JordanHelpers

namespace ContinuousLinearMap

section HermitianSplit

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
  [StarAddMonoid E] [StarModule ℂ E] [NormedStarGroup E]

/-- Every continuous linear functional on a normed complex star vector space decomposes as
`φ = φ₁ + I • φ₂`, where `φ₁` and `φ₂` commute with `star` and have norm at most `‖φ‖`. -/
theorem exists_map_star_add_I_smul (φ : E →L[ℂ] ℂ) :
    ∃ φ₁ φ₂ : E →L[ℂ] ℂ,
      (∀ a, φ₁ (star a) = star (φ₁ a)) ∧
      (∀ a, φ₂ (star a) = star (φ₂ a)) ∧
      φ = φ₁ + Complex.I • φ₂ ∧
      ‖φ₁‖ ≤ ‖φ‖ ∧ ‖φ₂‖ ≤ ‖φ‖ := by
  let φ₁ : E →L[ℂ] ℂ := hermitianPart φ
  let φ₂ : E →L[ℂ] ℂ := hermitianPart ((-Complex.I) • φ)
  have hnorm_negI : ‖(-Complex.I) • φ‖ = ‖φ‖ := by simp [norm_smul]
  refine ⟨φ₁, φ₂, hermitianPart_star φ, hermitianPart_star _, ?_,
    opNorm_hermitianPart_le φ, hnorm_negI ▸ opNorm_hermitianPart_le _⟩
  ext a
  simp only [φ₁, φ₂, hermitianPart, starConjFunctional, add_apply, smul_apply,
    LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul,
    Complex.star_def, map_mul, map_neg, Complex.conj_I, neg_neg]
  ring_nf
  simp only [Complex.I_sq]
  ring

end HermitianSplit

section JordanNonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Jordan decomposition of Hermitian functionals on a C⋆-algebra.** Every bounded Hermitian
functional `φ : A →L[ℂ] ℂ` (satisfying `φ (star a) = star (φ a)`) on a possibly nonunital
C⋆-algebra is the difference `φ₁ - φ₂` of two positive continuous linear functionals with
`‖φ₁‖ + ‖φ₂‖ = ‖φ‖`. -/
theorem exists_positiveContinuousLinearMap_sub_of_map_star (φ : A →L[ℂ] ℂ)
    (hφ : ∀ a, φ (star a) = star (φ a)) :
    ∃ φ₁ φ₂ : A →P[ℂ] ℂ,
      (φ₁ : A →L[ℂ] ℂ) - (φ₂ : A →L[ℂ] ℂ) = φ ∧
      ‖(φ₁ : A →L[ℂ] ℂ)‖ + ‖(φ₂ : A →L[ℂ] ℂ)‖ = ‖φ‖ := by
  let ι : A →ₗᵢ[ℂ] Unitization ℂ A :=
    { toFun := Unitization.inr
      map_add' := Unitization.inr_add ℂ
      map_smul' := Unitization.inr_smul ℂ
      norm_map' := Unitization.norm_inr }
  obtain ⟨ψ₀, hψ₀_ext, hψ₀_norm⟩ := ι.exists_extension_norm_eq φ
  let ψ : Unitization ℂ A →L[ℂ] ℂ := hermitianPart ψ₀
  have hψ_inr : ∀ a : A, ψ (a : Unitization ℂ A) = φ a := fun a => by
    have ha : ψ₀ (a : Unitization ℂ A) = φ a := congrArg (fun f : A →L[ℂ] ℂ => f a) hψ₀_ext
    have hsa : ψ₀ (star (a : Unitization ℂ A)) = star (φ a) := by
      rw [← Unitization.inr_star, ← hφ a]
      exact congrArg (fun f : A →L[ℂ] ℂ => f (star a)) hψ₀_ext
    simp only [ψ, hermitianPart, smul_apply, add_apply, starConjFunctional,
      LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk, ha, hsa, star_star,
      smul_eq_mul]
    ring
  have hψ_norm : ‖ψ‖ = ‖φ‖ := by
    refine le_antisymm ((opNorm_hermitianPart_le ψ₀).trans_eq hψ₀_norm) ?_
    exact φ.opNorm_le_bound (norm_nonneg ψ) fun a => by
      simpa [hψ_inr a, Unitization.norm_inr] using ψ.le_opNorm (a : Unitization ℂ A)
  obtain ⟨ψ₁, ψ₂, hψ_sub, hψ_sum⟩ :=
    exists_positiveContinuousLinearMap_sub_of_map_star_unital ψ (hermitianPart_star ψ₀)
  let φ₁ : A →P[ℂ] ℂ := ψ₁.comp (.ofClass (Unitization.inrNonUnitalStarAlgHom ℂ A))
  let φ₂ : A →P[ℂ] ℂ := ψ₂.comp (.ofClass (Unitization.inrNonUnitalStarAlgHom ℂ A))
  have hsub : (φ₁ : A →L[ℂ] ℂ) - (φ₂ : A →L[ℂ] ℂ) = φ := by
    ext a
    have hpt := congrArg (fun f : Unitization ℂ A →L[ℂ] ℂ => f (a : Unitization ℂ A)) hψ_sub
    simpa [φ₁, φ₂, hψ_inr a] using hpt
  have hle (η : Unitization ℂ A →P[ℂ] ℂ) :
      ‖((η.comp (.ofClass (Unitization.inrNonUnitalStarAlgHom ℂ A)) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ)‖ ≤
        ‖(η : Unitization ℂ A →L[ℂ] ℂ)‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun a => by
      simpa [Unitization.norm_inr] using
        (η : Unitization ℂ A →L[ℂ] ℂ).le_opNorm (a : Unitization ℂ A)
  refine ⟨φ₁, φ₂, hsub, le_antisymm ?_ ?_⟩
  · calc ‖(φ₁ : A →L[ℂ] ℂ)‖ + ‖(φ₂ : A →L[ℂ] ℂ)‖
        ≤ ‖(ψ₁ : Unitization ℂ A →L[ℂ] ℂ)‖ + ‖(ψ₂ : Unitization ℂ A →L[ℂ] ℂ)‖ :=
          add_le_add (hle ψ₁) (hle ψ₂)
      _ = ‖φ‖ := hψ_sum.trans hψ_norm
  · simpa [hsub] using norm_sub_le (φ₁ : A →L[ℂ] ℂ) (φ₂ : A →L[ℂ] ℂ)

/-- Every continuous linear functional on a (possibly nonunital) C⋆-algebra is a complex linear
combination `(φ₁ - φ₂) + I • (φ₃ - φ₄)` of four positive continuous linear functionals with
`‖φ₁‖ + ‖φ₂‖ ≤ ‖φ‖` and `‖φ₃‖ + ‖φ₄‖ ≤ ‖φ‖`. -/
theorem exists_positiveContinuousLinearMap_decomp (φ : A →L[ℂ] ℂ) :
    ∃ φ₁ φ₂ φ₃ φ₄ : A →P[ℂ] ℂ,
      φ = ((φ₁ : A →L[ℂ] ℂ) - (φ₂ : A →L[ℂ] ℂ)) +
          Complex.I • ((φ₃ : A →L[ℂ] ℂ) - (φ₄ : A →L[ℂ] ℂ)) ∧
      ‖(φ₁ : A →L[ℂ] ℂ)‖ + ‖(φ₂ : A →L[ℂ] ℂ)‖ ≤ ‖φ‖ ∧
      ‖(φ₃ : A →L[ℂ] ℂ)‖ + ‖(φ₄ : A →L[ℂ] ℂ)‖ ≤ ‖φ‖ := by
  obtain ⟨ψ_re, ψ_im, hre_star, him_star, hdecomp, hre_norm, him_norm⟩ :=
    φ.exists_map_star_add_I_smul
  obtain ⟨φ₁, φ₂, h12, hn12⟩ := ψ_re.exists_positiveContinuousLinearMap_sub_of_map_star hre_star
  obtain ⟨φ₃, φ₄, h34, hn34⟩ := ψ_im.exists_positiveContinuousLinearMap_sub_of_map_star him_star
  exact ⟨φ₁, φ₂, φ₃, φ₄, by rw [h12, h34, hdecomp], hn12.le.trans hre_norm, hn34.le.trans him_norm⟩

end JordanNonUnital

end ContinuousLinearMap

namespace TauCeti.CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Weak convergence in a C⋆-algebra is completely tested by positive continuous linear
functionals. -/
theorem tendsto_toWeakSpace_iff_forall_positiveContinuousLinearMap
    {ι : Type*} {l : Filter ι} {u : ι → A} {a : A} :
    Tendsto (fun i => toWeakSpace ℂ A (u i)) l (𝓝 (toWeakSpace ℂ A a)) ↔
      ∀ f : A →P[ℂ] ℂ, Tendsto (fun i => f (u i)) l (𝓝 (f a)) := by
  rw [TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto]
  refine ⟨fun h f => by simpa using h (f : A →L[ℂ] ℂ), fun h φ => ?_⟩
  obtain ⟨φ₁, φ₂, φ₃, φ₄, hφ, -, -⟩ := φ.exists_positiveContinuousLinearMap_decomp
  have h12 := (h φ₁).sub (h φ₂)
  have h34 := ((h φ₃).sub (h φ₄)).const_smul Complex.I
  simpa [hφ] using h12.add h34

end TauCeti.CStarAlgebra

end
