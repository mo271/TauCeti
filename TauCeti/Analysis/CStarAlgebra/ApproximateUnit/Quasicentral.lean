/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.Representation.EssentialSubspace
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional.Jordan
import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
import TauCeti.Analysis.LocallyConvex.Mazur
import TauCeti.Topology.Algebra.Module.WeakSpace
import TauCeti.Topology.MetricSpace.SimultaneousApproximation

/-!
# Quasicentral approximate units for closed two-sided ideals

Every closed two-sided ideal `I` of a (possibly nonunital) complex C⋆-algebra `A` admits a
*quasicentral approximate unit*: a filter (or net) of positive contractions in `I` that acts as a
two-sided approximate unit for `I` and asymptotically commutes with every element of `A`.

Following Arveson's argument, the proof combines four ingredients:

1. **Strong convergence in representations**: along any eventually norm-bounded left approximate
   unit of a C⋆-algebra, a Hilbert-space representation `π` converges strongly to the orthogonal
   projection onto `π.essentialSubspace`
   (`NonUnitalStarAlgHom.tendsto_apply_starProjection_essentialSubspace`).
2. **Ideal-projection commutation**: for a closed two-sided ideal `I`, the essential subspace of
   `π.comp I.starAlgHom` is invariant under every `π a` and its adjoint `π (star a)`, hence its
   orthogonal projection commutes with `π a`
   (`NonUnitalStarAlgHom.commute_starProjection_essentialSubspace_comp_ideal`).
3. **Weak convergence of commutators**: extending any positive functional `f` on `A` to
   `Unitization ℂ A` and passing to its GNS representation shows `f (e * a - a * e) → 0` along any
   bounded left approximate unit of `I`. By the Jordan decomposition of bounded linear functionals,
   the commutators `e * a - a * e` converge weakly to `0` in `A`
   (`TauCeti.CStarAlgebra.tendsto_toWeakSpace_mul_sub_mul`).
4. **Mazur convexification**: applying Mazur's theorem (`Convex.mem_of_tendsto_weak`) to the
   finite tuple of commutators `(e * a - a * e)_{a ∈ F}` over a convex tail of the canonical
   approximate unit of `I` yields a positive strict contraction above any prescribed `e₀` that
   simultaneously approximates the unit on a finite `G ⊆ I` and almost commutes with `F ⊆ A`
   (`TauCeti.CStarAlgebra.exists_mem_ideal_quasicentral_finset_ge`).

Passing from finite sets to a filter gives Arveson's theorem
`TauCeti.CStarAlgebra.exists_quasicentral_approximateUnit`; when `A` is separable, iterating the
step `e₀ ≤ e` along dense sequences produces a monotone sequential quasicentral approximate unit
(`TauCeti.CStarAlgebra.exists_monotone_quasicentral_seq_of_separableSpace`).

## References

* William Arveson, *Notes on extensions of C*-algebras*, Duke Math. J. 44 (1977), 329–355.
* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Section II.4.3.
* Gert K. Pedersen, *C*-Algebras and Their Automorphism Groups*, Theorem 3.12.14.
-/

public section

noncomputable section

open Filter Set Topology Unitization
open scoped CStarAlgebra ComplexOrder InnerProductSpace

namespace NonUnitalStarAlgHom

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Along any eventually norm-bounded net `e` with `e * a → a` for all `a : A`, a Hilbert-space
representation `π` converges strongly on all of `H` to the orthogonal projection onto its
essential subspace. -/
theorem tendsto_apply_starProjection_essentialSubspace
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) (ξ : H) :
    Tendsto (fun e => π e ξ) l (𝓝 (π.essentialSubspace.starProjection ξ)) := by
  have hlim : Tendsto
      (fun e => (π.restrictEssentialSubspace e
        (π.essentialSubspace.orthogonalProjectionOnto ξ) : H))
      l (𝓝 (π.essentialSubspace.starProjection ξ)) := by
    simpa only [Function.comp_def, Submodule.subtypeL_apply,
        Submodule.coe_orthogonalProjectionOnto_apply] using
      (π.essentialSubspace.subtypeL.continuous.tendsto _).comp <|
        (π.restrictEssentialSubspace.isNondegenerate_iff_tendsto hC hl).1
          π.isNondegenerate_restrictEssentialSubspace
          (π.essentialSubspace.orthogonalProjectionOnto ξ)
  refine hlim.congr fun e => ?_
  calc (π.restrictEssentialSubspace e (π.essentialSubspace.orthogonalProjectionOnto ξ) : H)
      = π e (π.essentialSubspace.starProjection ξ) +
          π e (ξ - π.essentialSubspace.starProjection ξ) := by
        rw [π.coe_restrictEssentialSubspace_apply, Submodule.coe_orthogonalProjectionOnto_apply,
          π.apply_eq_zero_of_mem_orthogonal_essentialSubspace
            (π.essentialSubspace.sub_starProjection_mem_orthogonal ξ), add_zero]
    _ = π e ξ := by rw [← map_add, add_sub_cancel]

/-- For a closed two-sided ideal `I` of a C⋆-algebra `A` and any Hilbert-space representation `π`
of `A`, the orthogonal projection onto the essential subspace of `π|_I` commutes with `π a` for
every `a : A`. -/
theorem commute_starProjection_essentialSubspace_comp_ideal
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (I : TwoSidedIdeal A) [IsClosed (I : Set A)] (a : A) :
    Commute (π.comp I.starAlgHom).essentialSubspace.starProjection (π a) := by
  set U := (π.comp I.starAlgHom).essentialSubspace
  have hinv (b : A) : U ∈ Module.End.invtSubmodule ((π b : H →L[ℂ] H) : Module.End ℂ H) := by
    rw [Module.End.mem_invtSubmodule]
    refine (essentialSubspace_le_iff
      ((π.comp I.starAlgHom).isClosed_essentialSubspace.preimage (π b).continuous)).2 fun x ξ => ?_
    rw [Submodule.mem_comap, NonUnitalStarAlgHom.comp_apply, TwoSidedIdeal.starAlgHom_apply]
    change π b (π (x : A) ξ) ∈ U
    have hmul : π b (π (x : A) ξ) = (π.comp I.starAlgHom) ⟨b * x, I.mul_mem_left b x x.2⟩ ξ := by
      rw [NonUnitalStarAlgHom.comp_apply, TwoSidedIdeal.starAlgHom_apply, map_mul]
      rfl
    rw [hmul]
    exact (π.comp I.starAlgHom).apply_mem_essentialSubspace _ ξ
  have hadj : U ∈ Module.End.invtSubmodule ((π a).adjoint : Module.End ℂ H) := by
    have hstar : (π a).adjoint = π (star a) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    rw [hstar]
    exact hinv (star a)
  exact Submodule.isReducing_coe_iff_commute_starProjection.mp <|
    ContinuousLinearMap.isReducing_iff_mem_invtSubmodule_adjoint.mpr ⟨hinv a, hadj⟩

end NonUnitalStarAlgHom

namespace TauCeti.CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Along any eventually norm-bounded left approximate unit `l` of a closed two-sided ideal `I`,
the commutators `e * a - a * e` converge weakly to `0` in `A` for every `a : A`. -/
theorem tendsto_toWeakSpace_mul_sub_mul
    {I : TwoSidedIdeal A} [IsClosed (I : Set A)] {l : Filter A} [l.NeBot] {C : ℝ}
    (hmem : ∀ᶠ e in l, e ∈ I) (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ x ∈ I, Tendsto (fun e => e * x) l (𝓝 x)) (a : A) :
    Tendsto (fun e => toWeakSpace ℂ A (e * a - a * e)) l (𝓝 0) := by
  let lI : Filter I := Filter.comap ((↑) : I → A) l
  have : lI.NeBot := Filter.comap_neBot fun t ht => by
    obtain ⟨e, het, heI⟩ := ‹l.NeBot›.nonempty_of_mem (Filter.inter_mem ht hmem)
    exact ⟨⟨e, heI⟩, het⟩
  have hmap : Filter.map ((↑) : I → A) lI = l := by
    rw [Filter.map_comap, Subtype.range_coe_subtype, inf_eq_left.2 (le_principal_iff.2 hmem)]
  rw [← hmap, tendsto_map'_iff]
  change Tendsto (fun e : I => toWeakSpace ℂ A ((e : A) * a - a * (e : A))) lI (𝓝 0)
  have hCI : ∀ᶠ e : I in lI, ‖e‖ ≤ C :=
    eventually_comap.2 <| hC.mono fun _ he e h => by change ‖(e : A)‖ ≤ C; rwa [h]
  have hlI : ∀ x : I, Tendsto (· * x) lI (𝓝 x) := fun x => by
    rw [tendsto_subtype_rng]
    exact (hl x x.2).comp tendsto_comap
  rw [← map_zero (toWeakSpace ℂ A), tendsto_toWeakSpace_iff_forall_positiveContinuousLinearMap]
  intro f
  rw [map_zero]
  let g : Unitization ℂ A →ₚ[ℂ] ℂ := f.unitizationExtend.toPositiveLinearMap
  let ξ : g.GNS := g.gnsVector
  let π : A →⋆ₙₐ[ℂ] (g.GNS →L[ℂ] g.GNS) :=
    g.gnsNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hf_eq (b : A) : f b = inner ℂ ξ (π b ξ) := by
    change f b = inner ℂ g.gnsVector (g.gnsNonUnitalStarAlgHom (b : A⁺¹) g.gnsVector)
    rw [g.gnsNonUnitalStarAlgHom_apply_gnsVector, g.inner_gnsVector_coe]
    exact (f.unitizationExtend_inr b).symm
  set P := (π.comp I.starAlgHom).essentialSubspace.starProjection
  have h1 : Tendsto (fun e : I => π (e : A) (π a ξ)) lI (𝓝 (P (π a ξ))) := by
    simpa only [NonUnitalStarAlgHom.comp_apply, TwoSidedIdeal.starAlgHom_apply] using
      (π.comp I.starAlgHom).tendsto_apply_starProjection_essentialSubspace hCI hlI (π a ξ)
  have h2 : Tendsto (fun e : I => π a (π (e : A) ξ)) lI (𝓝 (π a (P ξ))) :=
    ((π a).continuous.tendsto (P ξ)).comp <| by
      simpa only [NonUnitalStarAlgHom.comp_apply, TwoSidedIdeal.starAlgHom_apply] using
        (π.comp I.starAlgHom).tendsto_apply_starProjection_essentialSubspace hCI hlI ξ
  have hcomm : P (π a ξ) = π a (P ξ) :=
    congrArg (fun T : g.GNS →L[ℂ] g.GNS => T ξ)
      (π.commute_starProjection_essentialSubspace_comp_ideal I a).eq
  have hdiff : Tendsto (fun e : I => π (e : A) (π a ξ) - π a (π (e : A) ξ)) lI (𝓝 0) := by
    simpa only [hcomm, sub_self] using h1.sub h2
  have hinner : Tendsto (fun e : I => inner ℂ ξ (π (e : A) (π a ξ) - π a (π (e : A) ξ))) lI
      (𝓝 (inner ℂ ξ (0 : g.GNS))) :=
    (continuous_const.inner continuous_id).tendsto 0 |>.comp hdiff
  rw [inner_zero_right] at hinner
  refine hinner.congr fun e => ?_
  rw [hf_eq, map_sub, map_mul, map_mul]
  rfl

/-- **Arveson's finite-set quasicentral lemma**, with lower bound `e₀ ≤ e` and strict norm bound
`‖e‖ < 1`. Given a closed two-sided ideal `I`, a positive strict contraction `e₀ ∈ I`, finite sets
`G ⊆ I` and `F ⊆ A`, and `ε > 0`, there exists `e ∈ I` with `e₀ ≤ e`, `‖e‖ < 1`, acting as an
`ε`-approximate unit on `G` and `ε`-commuting with every element of `F`. -/
theorem exists_mem_ideal_quasicentral_finset_ge
    {I : TwoSidedIdeal A} (hI : IsClosed (I : Set A))
    {e₀ : A} (he₀I : e₀ ∈ I) (he₀_nonneg : 0 ≤ e₀) (he₀_norm : ‖e₀‖ < 1)
    (G : Finset A) (hG : ∀ x ∈ G, x ∈ I) (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∃ e ∈ I, e₀ ≤ e ∧ ‖e‖ < 1 ∧
      (∀ x ∈ G, ‖e * x - x‖ < ε ∧ ‖x * e - x‖ < ε) ∧
      (∀ a ∈ F, ‖e * a - a * e‖ < ε) := by
  have : IsClosed (I : Set A) := hI
  -- Step 1: Choose `r ∈ (‖e₀‖, 1)` close enough to `1` so scaling a positive contraction by `r`
  -- keeps `e₀ ≤ r • u`, forces `‖r • u‖ < 1`, and preserves `ε`-errors on `G`.
  let M : ℝ := ((G.sup fun x : A => ‖x‖₊ : NNReal) : ℝ) + 1
  have hM_pos : 0 < M := by positivity
  have hM_gt : ∀ x ∈ G, ‖x‖ < M := fun x hx => by
    have hle : (‖x‖₊ : ℝ) ≤ ((G.sup fun y : A => ‖y‖₊ : NNReal) : ℝ) := by
      exact_mod_cast Finset.le_sup (f := fun y : A => ‖y‖₊) hx
    linarith [coe_nnNorm x]
  let δ : ℝ := min (1 / 2) (ε / (2 * M))
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  let r : ℝ := max ((‖e₀‖ + 1) / 2) (1 - δ)
  have hr_gt : ‖e₀‖ < r := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hr_pos : 0 < r := (norm_nonneg e₀).trans_lt hr_gt
  have hr_lt_one : r < 1 := max_lt (by linarith) (by linarith)
  have h1r_le : 1 - r ≤ ε / (2 * M) := by
    have h1 : 1 - δ ≤ r := le_max_right _ _
    have h2 : δ ≤ ε / (2 * M) := min_le_right _ _
    linarith
  let e₀' : A := r⁻¹ • e₀
  have he₀'I : e₀' ∈ I := by
    change ((r⁻¹ : ℝ) : ℂ) • e₀ ∈ I
    exact I.smul_mem_of_isClosed _ he₀I
  have he₀'_nonneg : 0 ≤ e₀' := smul_nonneg (inv_nonneg.2 hr_pos.le) he₀_nonneg
  have he₀'_norm : ‖e₀'‖ < 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr_pos.le), inv_mul_lt_iff₀ hr_pos, mul_one]
    exact hr_gt
  -- Step 2: Work on the convex set `U` of positive contractions in `I` above `e₀'` with
  -- `(ε / 2)`-approximate-unit errors on `G`.
  let U : Set A :=
    { u : A | u ∈ I ∧ e₀' ≤ u ∧ ‖u‖ ≤ 1 ∧
      ∀ x ∈ G, ‖u * x - x‖ ≤ ε / 2 ∧ ‖x * u - x‖ ≤ ε / 2 }
  have hU_conv : Convex ℝ U := by
    rintro u ⟨huI, hue₀, hun, huG⟩ v ⟨hvI, hve₀, hvn, hvG⟩ s t hs ht hst
    have hcomb {w₁ w₂ : A} (h₁ : ‖w₁‖ ≤ ε / 2) (h₂ : ‖w₂‖ ≤ ε / 2) :
        ‖s • w₁ + t • w₂‖ ≤ ε / 2 :=
      calc ‖s • w₁ + t • w₂‖ ≤ ‖s • w₁‖ + ‖t • w₂‖ := norm_add_le _ _
        _ = s * ‖w₁‖ + t * ‖w₂‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
        _ ≤ s * (ε / 2) + t * (ε / 2) :=
          add_le_add (mul_le_mul_of_nonneg_left h₁ hs) (mul_le_mul_of_nonneg_left h₂ ht)
        _ = ε / 2 := by nlinarith
    refine ⟨?_, ?_, ?_, fun x hx => ⟨?_, ?_⟩⟩
    · exact I.add_mem (I.toSubmodule.smul_mem (s : ℂ) huI) (I.toSubmodule.smul_mem (t : ℂ) hvI)
    · calc e₀' = (s + t) • e₀' := by rw [hst, one_smul]
        _ = s • e₀' + t • e₀' := add_smul s t e₀'
        _ ≤ s • u + t • v := add_le_add (smul_le_smul_of_nonneg_left hue₀ hs)
            (smul_le_smul_of_nonneg_left hve₀ ht)
    · calc ‖s • u + t • v‖ ≤ ‖s • u‖ + ‖t • v‖ := norm_add_le _ _
        _ = s * ‖u‖ + t * ‖v‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
        _ ≤ s * 1 + t * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hun hs) (mul_le_mul_of_nonneg_left hvn ht)
        _ = 1 := by linarith
    · have heq : (s • u + t • v) * x - x = s • (u * x - x) + t • (v * x - x) := by
        nth_rw 2 [← one_smul ℝ x]
        rw [← hst, add_smul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_sub, smul_sub]
        abel
      rw [heq]
      exact hcomb (huG x hx).1 (hvG x hx).1
    · have heq : x * (s • u + t • v) - x = s • (x * u - x) + t • (x * v - x) := by
        nth_rw 2 [← one_smul ℝ x]
        rw [← hst, add_smul, mul_add, mul_smul_comm, mul_smul_comm, smul_sub, smul_sub]
        abel
      rw [heq]
      exact hcomb (huG x hx).2 (hvG x hx).2
  -- Step 3: Equip the closed star subalgebra `S = I.toNonUnitalStarSubalgebra` with the subtype
  -- order so that `0 ≤ e` and `e₀' ≤ e` agree with `A`.
  let S := I.toNonUnitalStarSubalgebra
  have hS_closed : IsClosed (S : Set A) := I.isClosed_toNonUnitalStarSubalgebra
  let _ : NonUnitalCStarAlgebra S :=
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hS_closed)
  have _ : StarOrderedRing S := Subtype.starOrderedRing S (hs := hS_closed)
  let lS : Filter S := _root_.CStarAlgebra.approximateUnit S
  have hlS : lS.IsIncreasingApproximateUnit := _root_.CStarAlgebra.increasingApproximateUnit S
  have : lS.NeBot := hlS.neBot
  -- Step 4: The canonical approximate unit `lS` of `S` eventually enters `U`.
  have hU_ev : ∀ᶠ e : S in lS, (e : A) ∈ U := by
    have hge_ev : ∀ᶠ e : S in lS, (⟨e₀', I.mem_toNonUnitalStarSubalgebra.2 he₀'I⟩ : S) ≤ e := by
      rw [(_root_.CStarAlgebra.hasBasis_approximateUnit S).eventually_iff]
      exact ⟨⟨e₀', I.mem_toNonUnitalStarSubalgebra.2 he₀'I⟩, ⟨he₀'_nonneg, he₀'_norm⟩,
        fun e he => he.1⟩
    have hG_ev :
        ∀ᶠ e : S in lS, ∀ x ∈ G, ‖(e : A) * x - x‖ ≤ ε / 2 ∧ ‖x * (e : A) - x‖ ≤ ε / 2 :=
      (G.eventually_all).2 fun x hx => by
        let xS : S := ⟨x, I.mem_toNonUnitalStarSubalgebra.2 (hG x hx)⟩
        have h1 : ∀ᶠ e : S in lS, ‖(e : A) * x - x‖ < ε / 2 :=
          (Metric.tendsto_nhds.1 (hlS.tendsto_mul_right xS) (ε / 2) (half_pos hε)).mono
            fun e he => by rw [Subtype.dist_eq, dist_eq_norm] at he; exact he
        have h2 : ∀ᶠ e : S in lS, ‖x * (e : A) - x‖ < ε / 2 :=
          (Metric.tendsto_nhds.1 (hlS.tendsto_mul_left xS) (ε / 2) (half_pos hε)).mono
            fun e he => by rw [Subtype.dist_eq, dist_eq_norm] at he; exact he
        filter_upwards [h1, h2] with e he1 he2
        exact ⟨he1.le, he2.le⟩
    filter_upwards [hge_ev, hlS.eventually_norm, hG_ev] with e hge hnorm hG'
    exact ⟨I.mem_toNonUnitalStarSubalgebra.1 e.2, hge, hnorm, hG'⟩
  -- Step 5: Consider the commutator map `T : A →L[ℂ] (F → A)` and show `0 ∈ closure (T '' U)`
  -- by weak convergence of `T (e : A) → 0` and Mazur's theorem.
  let T : A →L[ℂ] (F → A) :=
    { toLinearMap :=
        { toFun := fun u a => u * (a : A) - (a : A) * u
          map_add' := fun u v => by
            ext a
            simp only [Pi.add_apply, add_mul, mul_add]
            abel
          map_smul' := fun c u => by
            ext a
            simp only [Pi.smul_apply, RingHom.id_apply, smul_mul_assoc, mul_smul_comm, smul_sub] }
      cont := continuous_pi fun a =>
        (continuous_id.mul continuous_const).sub (continuous_const.mul continuous_id) }
  have hT_apply (u : A) (a : F) : T u a = u * (a : A) - (a : A) * u := rfl
  have hT_weak : Tendsto (fun e : S => toWeakSpace ℂ (F → A) (T (e : A))) lS
      (𝓝 (toWeakSpace ℂ (F → A) 0)) := by
    classical
    rw [TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto]
    intro Φ
    simp only [map_zero]
    let ι (a : F) : A →L[ℂ] (F → A) :=
      ContinuousLinearMap.pi fun b : F => if b = a then .id ℂ A else 0
    have hdecomp (v : F → A) : ∑ a : F, ι a (v a) = v := by
      ext b
      simp only [Finset.sum_apply, ι, ContinuousLinearMap.pi_apply]
      trans ∑ a : F, if b = a then v a else 0
      · refine Finset.sum_congr rfl fun a _ => ?_
        split_ifs <;> simp
      · simp
    have hterm (a : F) :
        Tendsto (fun e : S => (Φ.comp (ι a)) ((e : A) * (a : A) - (a : A) * (e : A))) lS (𝓝 0) := by
      have hw := tendsto_toWeakSpace_mul_sub_mul (I := I) (l := lS.map ((↑) : S → A)) (C := 1)
        (eventually_map.2 (.of_forall fun e => I.mem_toNonUnitalStarSubalgebra.1 e.2))
        (eventually_map.2 hlS.eventually_norm)
        (fun x hx => by
          rw [tendsto_map'_iff]
          exact (continuous_subtype_val.tendsto _).comp
            (hlS.tendsto_mul_right ⟨x, I.mem_toNonUnitalStarSubalgebra.2 hx⟩))
        (a : A)
      rw [← map_zero (toWeakSpace ℂ A), TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto] at hw
      simpa [tendsto_map'_iff, Function.comp_def] using hw (Φ.comp (ι a))
    have hsum :
        Tendsto (fun e : S => ∑ a : F, Φ (ι a (T (e : A) a))) lS (𝓝 (∑ _a : F, (0 : ℂ))) :=
      tendsto_finsetSum Finset.univ fun a _ => hterm a
    rw [Finset.sum_const_zero] at hsum
    refine hsum.congr fun e => ?_
    rw [← map_sum, hdecomp]
  let subIdx := { e : S // (e : A) ∈ U }
  let lSub : Filter subIdx := comap Subtype.val lS
  have : lSub.NeBot := Filter.comap_neBot fun t ht => by
    obtain ⟨e, het, heU⟩ := hlS.neBot.nonempty_of_mem (Filter.inter_mem ht hU_ev)
    exact ⟨⟨e, heU⟩, het⟩
  have : LocallyConvexSpace ℝ (F → A) := NormedSpace.toLocallyConvexSpace' ℂ
  have hK_conv : Convex ℝ (closure (T '' U)) :=
    (hU_conv.linear_image (T.toLinearMap.restrictScalars ℝ)).closure
  have h0_mem : (0 : F → A) ∈ closure (T '' U) :=
    hK_conv.mem_of_tendsto_weak (𝕜 := ℂ) isClosed_closure
      (fun e : subIdx => subset_closure ⟨(e.1 : A), e.2, rfl⟩)
      (hT_weak.comp tendsto_comap)
  -- Step 6: Pick `u ∈ U` with `‖T u‖ < ε` and scale to `e = r • u`.
  obtain ⟨_, ⟨u, huU, rfl⟩, hTu⟩ := Metric.mem_closure_iff.1 h0_mem ε hε
  rw [dist_zero_left] at hTu
  obtain ⟨huI, hue₀', hu_norm, huG⟩ := huU
  have hscale {w x : A} (hx : x ∈ G) (hw : ‖w‖ ≤ ε / 2) : ‖r • w - (1 - r) • x‖ < ε :=
    calc ‖r • w - (1 - r) • x‖
        ≤ ‖r • w‖ + ‖(1 - r) • x‖ := norm_sub_le _ _
      _ = r * ‖w‖ + (1 - r) * ‖x‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hr_pos.le,
          Real.norm_of_nonneg (sub_nonneg.2 hr_lt_one.le)]
      _ ≤ 1 * (ε / 2) + (1 - r) * ‖x‖ :=
        add_le_add (mul_le_mul hr_lt_one.le hw (norm_nonneg _) zero_le_one) le_rfl
      _ < ε / 2 + (ε / (2 * M)) * M := by
        rw [one_mul]
        have h1 : (1 - r) * ‖x‖ < (1 - r) * M :=
          mul_lt_mul_of_pos_left (hM_gt x hx) (sub_pos.2 hr_lt_one)
        have h2 : (1 - r) * M ≤ (ε / (2 * M)) * M :=
          mul_le_mul_of_nonneg_right h1r_le hM_pos.le
        linarith
      _ = ε := by field_simp [hM_pos.ne']; ring
  refine ⟨r • u, I.toSubmodule.smul_mem (r : ℂ) huI, ?_, ?_, fun x hx => ⟨?_, ?_⟩, fun a ha => ?_⟩
  · calc e₀ = r • e₀' := by rw [smul_smul, mul_inv_cancel₀ hr_pos.ne', one_smul]
      _ ≤ r • u := smul_le_smul_of_nonneg_left hue₀' hr_pos.le
  · calc ‖r • u‖ = r * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hr_pos.le]
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hu_norm hr_pos.le
      _ < 1 := by linarith
  · have heq : (r • u) * x - x = r • (u * x - x) - (1 - r) • x := by
      rw [smul_mul_assoc, smul_sub, sub_smul, one_smul]
      abel
    rw [heq]
    exact hscale hx (huG x hx).1
  · have heq : x * (r • u) - x = r • (x * u - x) - (1 - r) • x := by
      rw [mul_smul_comm, smul_sub, sub_smul, one_smul]
      abel
    rw [heq]
    exact hscale hx (huG x hx).2
  · have hcomm : (r • u) * a - a * (r • u) = r • T u ⟨a, ha⟩ := by
      rw [hT_apply, smul_mul_assoc, mul_smul_comm, smul_sub]
    rw [hcomm, norm_smul, Real.norm_of_nonneg hr_pos.le]
    have ha_lt : ‖T u ⟨a, ha⟩‖ < ε := (pi_norm_lt_iff hε).1 hTu ⟨a, ha⟩
    calc r * ‖T u ⟨a, ha⟩‖ ≤ 1 * ‖T u ⟨a, ha⟩‖ :=
          mul_le_mul_of_nonneg_right hr_lt_one.le (norm_nonneg _)
      _ = ‖T u ⟨a, ha⟩‖ := one_mul _
      _ < ε := ha_lt

/-- **Arveson's theorem on quasicentral approximate units.** Every closed two-sided ideal `I` of a
(possibly nonunital) C⋆-algebra `A` admits a quasicentral approximate unit: a proper filter of
positive contractions in `I` acting as a two-sided approximate unit for `I` and asymptotically
commuting with every element of `A`. -/
theorem exists_quasicentral_approximateUnit (I : TwoSidedIdeal A)
    (hI : IsClosed (I : Set A)) :
    ∃ l : Filter A, l.NeBot ∧ (∀ᶠ e in l, e ∈ I ∧ 0 ≤ e ∧ ‖e‖ ≤ 1) ∧
      (∀ a ∈ I, Tendsto (fun e => e * a) l (𝓝 a)) ∧
      (∀ a ∈ I, Tendsto (fun e => a * e) l (𝓝 a)) ∧
      (∀ a : A, Tendsto (fun e => e * a - a * e) l (𝓝 0)) := by
  classical
  let p : A → Prop := fun e => e ∈ I ∧ 0 ≤ e ∧ ‖e‖ ≤ 1
  let F : I ⊕ A → A → A × A := fun k e =>
    match k with
    | Sum.inl x => (e * (x : A), (x : A) * e)
    | Sum.inr a => (e * a - a * e, 0)
  let x : I ⊕ A → A × A := fun k =>
    match k with
    | Sum.inl y => ((y : A), (y : A))
    | Sum.inr _ => (0, 0)
  have hfin : ∀ s : Finset (I ⊕ A), ∀ ε > 0, ∃ e, p e ∧ ∀ k ∈ s, dist (F k e) (x k) < ε := by
    intro s ε hε
    let G : Finset A := s.biUnion fun k =>
      match k with
      | Sum.inl y => {(y : A)}
      | Sum.inr _ => ∅
    let H : Finset A := s.biUnion fun k =>
      match k with
      | Sum.inl _ => ∅
      | Sum.inr a => {a}
    have hG : ∀ y ∈ G, y ∈ I := by
      intro y hy
      rcases Finset.mem_biUnion.1 hy with ⟨k, -, hk⟩
      cases k with
      | inl z =>
        simp only [Finset.mem_singleton] at hk
        exact hk ▸ z.2
      | inr _ => simp at hk
    obtain ⟨e, heI, he0, hen, heG, heH⟩ :=
      exists_mem_ideal_quasicentral_finset_ge hI I.zero_mem le_rfl (by simp) G hG H hε
    refine ⟨e, ⟨heI, he0, hen.le⟩, fun k hk => ?_⟩
    cases k with
    | inl y =>
      have hyG : (y : A) ∈ G := Finset.mem_biUnion.2 ⟨Sum.inl y, hk, Finset.mem_singleton_self _⟩
      obtain ⟨hl, hr⟩ := heG (y : A) hyG
      simpa [F, x, Prod.dist_eq, dist_eq_norm] using ⟨hl, hr⟩
    | inr a =>
      have haH : a ∈ H := Finset.mem_biUnion.2 ⟨Sum.inr a, hk, Finset.mem_singleton_self _⟩
      have hcomm := heH a haH
      simpa [F, x, Prod.dist_eq, dist_eq_norm, hε] using hcomm
  obtain ⟨l, hl_neBot, hp, hF⟩ :=
    TauCeti.exists_neBot_tendsto_iff_forall_finset_dist_lt.2 hfin
  refine ⟨l, hl_neBot, hp, ?_, ?_, ?_⟩
  · intro a ha
    have h := hF (Sum.inl ⟨a, ha⟩)
    rw [nhds_prod_eq, tendsto_prod_iff'] at h
    exact h.1
  · intro a ha
    have h := hF (Sum.inl ⟨a, ha⟩)
    rw [nhds_prod_eq, tendsto_prod_iff'] at h
    exact h.2
  · intro a
    have h := hF (Sum.inr a)
    rw [nhds_prod_eq, tendsto_prod_iff'] at h
    exact h.1

/-- In a separable C⋆-algebra, every closed two-sided ideal admits a monotone sequential
quasicentral approximate unit consisting of positive strict contractions. -/
theorem exists_monotone_quasicentral_seq_of_separableSpace
    [TopologicalSpace.SeparableSpace A] (I : TwoSidedIdeal A) (hI : IsClosed (I : Set A)) :
    ∃ e : ℕ → A, Monotone e ∧ (∀ n, e n ∈ I ∧ 0 ≤ e n ∧ ‖e n‖ < 1) ∧
      (∀ a ∈ I, Tendsto (fun n => e n * a) atTop (𝓝 a)) ∧
      (∀ a ∈ I, Tendsto (fun n => a * e n) atTop (𝓝 a)) ∧
      (∀ a : A, Tendsto (fun n => e n * a - a * e n) atTop (𝓝 0)) := by
  classical
  obtain ⟨dA, hdA⟩ := TopologicalSpace.exists_dense_seq A
  have : Nonempty I := ⟨0⟩
  obtain ⟨dI, hdI⟩ := TopologicalSpace.exists_dense_seq I
  let State := { x : A // x ∈ I ∧ 0 ≤ x ∧ ‖x‖ < 1 }
  let next (n : ℕ) (s : State) :
      { t : State // s.1 ≤ t.1 ∧
        (∀ k ≤ n, ‖t.1 * (dI k : A) - (dI k : A)‖ < 1 / (n + 1 : ℝ) ∧
          ‖(dI k : A) * t.1 - (dI k : A)‖ < 1 / (n + 1 : ℝ)) ∧
        (∀ k ≤ n, ‖t.1 * dA k - dA k * t.1‖ < 1 / (n + 1 : ℝ)) } := by
    let G := (Finset.range (n + 1)).image (fun k => (dI k : A))
    let F := (Finset.range (n + 1)).image dA
    have hG : ∀ x ∈ G, x ∈ I := by
      intro x hx
      rcases Finset.mem_image.1 hx with ⟨k, -, rfl⟩
      exact (dI k).2
    have hex := exists_mem_ideal_quasicentral_finset_ge hI s.2.1 s.2.2.1 s.2.2.2 G hG F
      (show (0 : ℝ) < 1 / (n + 1 : ℝ) by positivity)
    refine ⟨⟨Classical.choose hex, (Classical.choose_spec hex).1,
      s.2.2.1.trans (Classical.choose_spec hex).2.1, (Classical.choose_spec hex).2.2.1⟩,
      (Classical.choose_spec hex).2.1, fun k hk => ?_, fun k hk => ?_⟩
    · exact (Classical.choose_spec hex).2.2.2.1 (dI k : A)
        (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hk), rfl⟩)
    · exact (Classical.choose_spec hex).2.2.2.2 (dA k)
        (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hk), rfl⟩)
  let seq : ℕ → State := Nat.rec ⟨0, I.zero_mem, le_rfl, by simp⟩ fun n s => (next n s).1
  let e : ℕ → A := fun n => (seq n).1
  have hmono : Monotone e := monotone_nat_of_le_succ fun n => (next n (seq n)).2.1
  have hprops : ∀ n, e n ∈ I ∧ 0 ≤ e n ∧ ‖e n‖ < 1 := fun n => (seq n).2
  have hstep_I (n k : ℕ) (hk : k ≤ n) :
      ‖e (n + 1) * (dI k : A) - (dI k : A)‖ < 1 / (n + 1 : ℝ) ∧
      ‖(dI k : A) * e (n + 1) - (dI k : A)‖ < 1 / (n + 1 : ℝ) :=
    (next n (seq n)).2.2.1 k hk
  have hstep_A (n k : ℕ) (hk : k ≤ n) :
      ‖e (n + 1) * dA k - dA k * e (n + 1)‖ < 1 / (n + 1 : ℝ) :=
    (next n (seq n)).2.2.2 k hk
  have : IsClosed (I : Set A) := hI
  have hleft : ∀ a ∈ I, Tendsto (fun n => e n * a) atTop (𝓝 a) := by
    intro a ha
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := hdI.exists_dist_lt (⟨a, ha⟩ : I) (show 0 < ε / 3 by positivity)
    have hka : ‖a - (dI k : A)‖ < ε / 3 := by simpa [Subtype.dist_eq, dist_eq_norm] using hk
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
    refine ⟨max (k + 1) (N + 1), fun m hm => ?_⟩
    have hm1 : 1 ≤ m := by omega
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.sub_add_cancel hm1).symm⟩
    have hkn : k ≤ n := by omega
    have hNn : N ≤ n := by omega
    have hbound : ‖e (n + 1) * (dI k : A) - (dI k : A)‖ < ε / 3 :=
      (hstep_I n k hkn).1.trans_le <| le_trans (by gcongr) hN.le
    rw [dist_eq_norm]
    have hsplit : e (n + 1) * a - a =
        e (n + 1) * (a - (dI k : A)) + (e (n + 1) * (dI k : A) - (dI k : A)) -
          (a - (dI k : A)) := by
      rw [mul_sub]
      abel
    rw [hsplit]
    calc ‖e (n + 1) * (a - (dI k : A)) + (e (n + 1) * (dI k : A) - (dI k : A)) -
            (a - (dI k : A))‖
        ≤ ‖e (n + 1) * (a - (dI k : A))‖ + ‖e (n + 1) * (dI k : A) - (dI k : A)‖ +
            ‖a - (dI k : A)‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ 1 * ‖a - (dI k : A)‖ + ‖e (n + 1) * (dI k : A) - (dI k : A)‖ + ‖a - (dI k : A)‖ := by
        gcongr
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (hprops (n + 1)).2.2.le (norm_nonneg _))
      _ < ε / 3 + ε / 3 + ε / 3 := by linarith
      _ = ε := by ring
  refine ⟨e, hmono, hprops, hleft, fun a ha => ?_, ?_⟩
  · have h : Tendsto (fun n => star (e n * star a)) atTop (𝓝 a) := by
      simpa only [Function.comp_def, star_star] using
        (continuous_star.tendsto (star a)).comp (hleft (star a) (I.star_mem_of_isClosed ha))
    refine h.congr fun n => ?_
    simp only [star_mul, star_star, (hprops n).2.1.isSelfAdjoint.star_eq]
  · intro a
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := hdA.exists_dist_lt a (show 0 < ε / 3 by positivity)
    have hka : ‖a - dA k‖ < ε / 3 := by simpa [dist_eq_norm] using hk
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
    refine ⟨max (k + 1) (N + 1), fun m hm => ?_⟩
    have hm1 : 1 ≤ m := by omega
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.sub_add_cancel hm1).symm⟩
    have hkn : k ≤ n := by omega
    have hNn : N ≤ n := by omega
    have hbound : ‖e (n + 1) * dA k - dA k * e (n + 1)‖ < ε / 3 :=
      (hstep_A n k hkn).trans_le <| le_trans (by gcongr) hN.le
    rw [dist_zero_right]
    have hsplit : e (n + 1) * a - a * e (n + 1) =
        e (n + 1) * (a - dA k) + (e (n + 1) * dA k - dA k * e (n + 1)) -
          (a - dA k) * e (n + 1) := by
      rw [mul_sub, sub_mul]
      abel
    rw [hsplit]
    calc ‖e (n + 1) * (a - dA k) + (e (n + 1) * dA k - dA k * e (n + 1)) -
            (a - dA k) * e (n + 1)‖
        ≤ ‖e (n + 1) * (a - dA k)‖ + ‖e (n + 1) * dA k - dA k * e (n + 1)‖ +
            ‖(a - dA k) * e (n + 1)‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ 1 * ‖a - dA k‖ + ‖e (n + 1) * dA k - dA k * e (n + 1)‖ + ‖a - dA k‖ * 1 := by
        gcongr
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hprops (n + 1)).2.2.le (norm_nonneg _))
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left (hprops (n + 1)).2.2.le (norm_nonneg _))
      _ < ε / 3 + ε / 3 + ε / 3 := by linarith
      _ = ε := by ring

end TauCeti.CStarAlgebra

end
