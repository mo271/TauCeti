/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.KacMoody.CartanInjective

import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import TauCeti.Algebra.Lie.Basic
import TauCeti.Algebra.Lie.Presentation.Serre.Triangular

/-!
# Triangular decomposition, derived algebra, and sharpness of Serre's relations

Let `A` be a square matrix of integers and `R` a realization of `A` over a field `K`
(`TauCeti.CartanRealization`). Write `𝔤 = TauCeti.KacMoody.PresentedLieAlgebra R`, `n⁺` and `n⁻`
for `TauCeti.KacMoody.positiveSubalgebra R` and `TauCeti.KacMoody.negativeSubalgebra R`, and `𝔥`
for `TauCeti.KacMoody.cartanSubalgebra R`.

For an arbitrary integer matrix `A`, the Lie algebra `𝔤` is spanned as a `K`-vector space by its
three triangular parts `n⁻`, `𝔥`, and `n⁺`
(`TauCeti.KacMoody.negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra`).

When `A` is a generalized Cartan matrix (`Matrix.IsGeneralizedCartan`), combining this spanning
statement with the master vanishing criterion of `TauCeti/Algebra/Lie/KacMoody/SerreIdeal.lean`
yields over every field `K` (without characteristic, finiteness, or symmetrizability hypotheses):

1. **Direct-sum triangular decomposition** (`TauCeti.KacMoody.triangularEquiv`):
   `n⁻ × H × n⁺ ≃ₗ[K] PresentedLieAlgebra R`, together with the three linear projections
   `TauCeti.KacMoody.negativeProj`, `TauCeti.KacMoody.cartanProj`, and
   `TauCeti.KacMoody.positiveProj`.
2. **Comparison with Serre's presentation `Matrix.ToLieAlgebra K A`**:
   `TauCeti.KacMoody.serreHom` is injective (`TauCeti.KacMoody.serreHom_injective`) and identifies
   `Matrix.ToLieAlgebra K A` with the derived subalgebra `⁅𝔤, 𝔤⁆`
   (`TauCeti.KacMoody.serreEquivDerived`), while `⁅𝔤, 𝔤⁆ ∩ 𝔥` is precisely the image of the coroot
   span `R.corootSpan` (`TauCeti.KacMoody.derivedSeries_one_inf_cartanSubalgebra`).
3. **Degenerate empty index set**: when `I` is empty, `PresentedLieAlgebra R` is abelian and
   linearly isomorphic to `H` via `cartanElement R`, whereas `Matrix.ToLieAlgebra K A` is zero.
4. **Sharpness of Serre's exponent**: for distinct indices `i ≠ j` and every `k ≤ (-A i j).toNat`,
   the iterated brackets `(ad eᵢ) ^ k eⱼ` and `(ad fᵢ) ^ k fⱼ` are nonzero in
   `PresentedLieAlgebra R` (`TauCeti.KacMoody.ad_pow_positiveGenerator_ne_zero`,
   `TauCeti.KacMoody.ad_pow_negativeGenerator_ne_zero`).

## Main definitions

* `TauCeti.KacMoody.triangularEquiv`: the linear equivalence
  `(negativeSubalgebra R × H × positiveSubalgebra R) ≃ₗ[K] PresentedLieAlgebra R`.
* `TauCeti.KacMoody.negativeProj`, `TauCeti.KacMoody.cartanProj`, `TauCeti.KacMoody.positiveProj`:
  the three linear projections associated to the triangular decomposition.
* `TauCeti.KacMoody.serreEquivDerived`: the Lie algebra isomorphism
  `Matrix.ToLieAlgebra K A ≃ₗ⁅K⁆ derivedSeries K (PresentedLieAlgebra R) 1`.
* `TauCeti.KacMoody.cartanLinearEquivOfIsEmpty`: the linear equivalence
  `H ≃ₗ[K] PresentedLieAlgebra R` when `I` is empty.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §1.2–1.3, Theorem 1.2, and §3.3.
-/

public section

open LieAlgebra

namespace TauCeti.KacMoody

/-! ## Triangular spanning for an arbitrary integer matrix -/

section Spanning

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- The image of `TauCeti.KacMoody.serreHom` decomposes as `n⁻ + H' + n⁺`, where `H'` is the image
of `R.corootSpan` under `cartanElement R`. -/
theorem toSubmodule_range_serreHom [DecidableEq I] :
    (serreHom R).range.toSubmodule =
      (negativeSubalgebra R).toSubmodule ⊔
        R.corootSpan.map (cartanElement R) ⊔
        (positiveSubalgebra R).toSubmodule := by
  have hrange : (serreHom R).range.toSubmodule =
      (⊤ : Submodule K (Matrix.ToLieAlgebra K A)).map (serreHom R).toLinearMap := by
    rw [Submodule.map_top]
    rfl
  rw [hrange, ← lieSpan_serreF_sup_span_serreH_sup_lieSpan_serreE_eq_top K A,
    Submodule.map_sup, Submodule.map_sup]
  congr 1
  · congr 1
    · rw [← LieSubalgebra.map_toSubmodule, LieSubalgebra.map_lieSpan, ← Set.range_comp,
        negativeSubalgebra_def]
      congr 2; ext i; simp
    · rw [R.corootSpan_def, LinearMap.map_span, LinearMap.map_span, ← Set.range_comp,
        ← Set.range_comp]
      congr 1; ext i; simp
  · rw [← LieSubalgebra.map_toSubmodule, LieSubalgebra.map_lieSpan, ← Set.range_comp,
      positiveSubalgebra_def]
    congr 2; ext i; simp

/-- **Triangular spanning.** For any integer matrix `A`, `PresentedLieAlgebra R` is the sum of its
negative, Cartan, and positive subalgebras: `𝔤 = n⁻ + 𝔥 + n⁺`. -/
theorem negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra :
    (negativeSubalgebra R).toSubmodule ⊔
      (cartanSubalgebra R).toSubmodule ⊔
      (positiveSubalgebra R).toSubmodule = ⊤ := by
  classical
  refine eq_top_iff.mpr ?_
  rw [← range_serreHom_sup_range_cartanElement R, toSubmodule_range_serreHom R,
    toSubmodule_cartanSubalgebra]
  refine sup_le ?_ (le_sup_of_le_left le_sup_right)
  refine sup_le (sup_le ?_ ?_) le_sup_right
  · exact le_sup_of_le_left le_sup_left
  · exact le_sup_of_le_left (LinearMap.map_le_range.trans le_sup_right)

end Spanning

/-! ## Direct-sum triangular decomposition and projections -/

section TriangularEquiv

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- **Triangular linear independence.** For a generalized Cartan matrix `A`, if `yF ∈ n⁻`,
`x : H`, and `yE ∈ n⁺` satisfy `yF + cartanElement R x + yE = 0`, then `yF = 0`, `x = 0`, and
`yE = 0`. -/
theorem eq_zero_of_negative_add_cartanElement_add_positive_eq_zero
    (hA : A.IsGeneralizedCartan) {yF yE : PresentedLieAlgebra R} {x : H}
    (hyF : yF ∈ negativeSubalgebra R) (hyE : yE ∈ positiveSubalgebra R)
    (h : yF + cartanElement R x + yE = 0) :
    yF = 0 ∧ x = 0 ∧ yE = 0 := by
  rw [← range_negativeFreeLift] at hyF
  rw [← range_positiveFreeLift] at hyE
  obtain ⟨uF, rfl⟩ := hyF
  obtain ⟨uE, rfl⟩ := hyE
  obtain ⟨huF, hx, huE⟩ :=
    (negativeFreeLift_add_cartanElement_add_positiveFreeLift_eq_zero_iff R hA).mp h
  exact ⟨serreIdeal_le_ker_negativeFreeLift R huF, hx, serreIdeal_le_ker_positiveFreeLift R huE⟩

/-- For a generalized Cartan matrix `A`, `𝔥` and `n⁺` have zero intersection. -/
theorem disjoint_cartanSubalgebra_positiveSubalgebra (hA : A.IsGeneralizedCartan) :
    Disjoint (cartanSubalgebra R).toSubmodule (positiveSubalgebra R).toSubmodule := by
  rw [toSubmodule_cartanSubalgebra, Submodule.disjoint_def]
  rintro _ ⟨x, rfl⟩ hz
  have h0 : (0 : PresentedLieAlgebra R) + cartanElement R x + (-cartanElement R x) = 0 := by abel
  have hx := (eq_zero_of_negative_add_cartanElement_add_positive_eq_zero R hA (zero_mem _)
    (neg_mem hz) h0).2.1
  simp [hx]

/-- For a generalized Cartan matrix `A`, `n⁻` and `𝔥` have zero intersection. -/
theorem disjoint_negativeSubalgebra_cartanSubalgebra (hA : A.IsGeneralizedCartan) :
    Disjoint (negativeSubalgebra R).toSubmodule (cartanSubalgebra R).toSubmodule := by
  rw [toSubmodule_cartanSubalgebra, Submodule.disjoint_def]
  rintro z hz ⟨x, hzx⟩
  have h0 : z + cartanElement R (-x) + 0 = 0 := by simp [hzx]
  exact (eq_zero_of_negative_add_cartanElement_add_positive_eq_zero R hA hz (zero_mem _) h0).1

/-- For a generalized Cartan matrix `A`, `n⁻` and `n⁺` have zero intersection. -/
theorem disjoint_negativeSubalgebra_positiveSubalgebra (hA : A.IsGeneralizedCartan) :
    Disjoint (negativeSubalgebra R).toSubmodule (positiveSubalgebra R).toSubmodule := by
  rw [Submodule.disjoint_def]
  intro z hzF hzE
  have h0 : z + cartanElement R 0 + (-z) = 0 := by simp
  exact (eq_zero_of_negative_add_cartanElement_add_positive_eq_zero R hA hzF
    (neg_mem hzE) h0).1

/-- For a generalized Cartan matrix `A`, `n⁻` has zero intersection with the upper Borel
`𝔥 ⊕ n⁺`. -/
theorem disjoint_negativeSubalgebra_sup (hA : A.IsGeneralizedCartan) :
    Disjoint (negativeSubalgebra R).toSubmodule
      ((cartanSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule) := by
  rw [toSubmodule_cartanSubalgebra, Submodule.disjoint_def]
  intro z hzF hzHE
  obtain ⟨_, ⟨x, rfl⟩, yE, hyE, hsum⟩ := Submodule.mem_sup.mp hzHE
  have h0 : (-z) + cartanElement R x + yE = 0 := by
    rw [← sub_eq_zero]
    convert sub_eq_zero.mpr hsum using 1
    abel
  exact neg_eq_zero.mp
    (eq_zero_of_negative_add_cartanElement_add_positive_eq_zero R hA (neg_mem hzF) hyE h0).1

/-- `n⁻` and the upper Borel `𝔥 ⊕ n⁺` are complementary subspaces of `PresentedLieAlgebra R`. -/
theorem isCompl_negativeSubalgebra_sup (hA : A.IsGeneralizedCartan) :
    IsCompl (negativeSubalgebra R).toSubmodule
      ((cartanSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule) :=
  ⟨disjoint_negativeSubalgebra_sup R hA,
    codisjoint_iff.mpr <| by
      rw [← sup_assoc, negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra]⟩

private noncomputable def triangularMap :
    (negativeSubalgebra R × H × positiveSubalgebra R) →ₗ[K] PresentedLieAlgebra R where
  toFun p := (p.1 : PresentedLieAlgebra R) + cartanElement R p.2.1 + (p.2.2 : PresentedLieAlgebra R)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, AddMemClass.coe_add, map_add]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, map_smul, RingHom.id_apply, smul_add]

/-- **Triangular decomposition.** For a generalized Cartan matrix `A`, addition induces a `K`-linear
isomorphism `n⁻ × H × n⁺ ≃ₗ[K] PresentedLieAlgebra R`. -/
noncomputable def triangularEquiv (hA : A.IsGeneralizedCartan) :
    (negativeSubalgebra R × H × positiveSubalgebra R) ≃ₗ[K] PresentedLieAlgebra R :=
  LinearEquiv.ofBijective (triangularMap R) ⟨by
    refine (injective_iff_map_eq_zero _).mpr ?_
    rintro ⟨⟨yF, hyF⟩, x, ⟨yE, hyE⟩⟩ h0
    obtain ⟨rfl, rfl, rfl⟩ :=
      eq_zero_of_negative_add_cartanElement_add_positive_eq_zero R hA hyF hyE h0
    rfl, fun z => by
    have hz : z ∈ (negativeSubalgebra R).toSubmodule ⊔
        (cartanSubalgebra R).toSubmodule ⊔ (positiveSubalgebra R).toSubmodule := by
      rw [negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra]
      exact Submodule.mem_top
    obtain ⟨ab, hab, yE, hyE, rfl⟩ := Submodule.mem_sup.mp hz
    rw [toSubmodule_cartanSubalgebra] at hab
    obtain ⟨yF, hyF, _, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hab
    exact ⟨(⟨yF, hyF⟩, x, ⟨yE, hyE⟩), rfl⟩⟩

@[simp]
theorem triangularEquiv_apply (hA : A.IsGeneralizedCartan)
    (p : negativeSubalgebra R × H × positiveSubalgebra R) :
    triangularEquiv R hA p =
      (p.1 : PresentedLieAlgebra R) + cartanElement R p.2.1 + (p.2.2 : PresentedLieAlgebra R) :=
  (rfl)

@[simp]
theorem triangularEquiv_symm_add_add (hA : A.IsGeneralizedCartan)
    (yF : negativeSubalgebra R) (x : H) (yE : positiveSubalgebra R) :
    (triangularEquiv R hA).symm
        ((yF : PresentedLieAlgebra R) + cartanElement R x + (yE : PresentedLieAlgebra R)) =
      (yF, x, yE) :=
  (triangularEquiv R hA).symm_apply_eq.mpr rfl

/-- The linear projection `PresentedLieAlgebra R →ₗ[K] negativeSubalgebra R` along `𝔥 ⊕ n⁺`. -/
noncomputable def negativeProj (hA : A.IsGeneralizedCartan) :
    PresentedLieAlgebra R →ₗ[K] negativeSubalgebra R :=
  (LinearMap.fst K (negativeSubalgebra R) (H × positiveSubalgebra R)).comp
    (triangularEquiv R hA).symm.toLinearMap

/-- The linear projection `PresentedLieAlgebra R →ₗ[K] H` along `n⁻ ⊕ n⁺`. -/
noncomputable def cartanProj (hA : A.IsGeneralizedCartan) :
    PresentedLieAlgebra R →ₗ[K] H :=
  (LinearMap.fst K H (positiveSubalgebra R)).comp <|
    (LinearMap.snd K (negativeSubalgebra R) (H × positiveSubalgebra R)).comp
      (triangularEquiv R hA).symm.toLinearMap

/-- The linear projection `PresentedLieAlgebra R →ₗ[K] positiveSubalgebra R` along `n⁻ ⊕ 𝔥`. -/
noncomputable def positiveProj (hA : A.IsGeneralizedCartan) :
    PresentedLieAlgebra R →ₗ[K] positiveSubalgebra R :=
  (LinearMap.snd K H (positiveSubalgebra R)).comp <|
    (LinearMap.snd K (negativeSubalgebra R) (H × positiveSubalgebra R)).comp
      (triangularEquiv R hA).symm.toLinearMap

/-- Every element of `PresentedLieAlgebra R` equals the sum of its three triangular projections. -/
@[simp]
theorem coe_negativeProj_add_cartanElement_cartanProj_add_coe_positiveProj
    (hA : A.IsGeneralizedCartan) (z : PresentedLieAlgebra R) :
    (negativeProj R hA z : PresentedLieAlgebra R) +
      cartanElement R (cartanProj R hA z) +
      (positiveProj R hA z : PresentedLieAlgebra R) = z :=
  (triangularEquiv R hA).apply_symm_apply z

@[simp]
theorem negativeProj_add_add (hA : A.IsGeneralizedCartan)
    (yF : negativeSubalgebra R) (x : H) (yE : positiveSubalgebra R) :
    negativeProj R hA
        ((yF : PresentedLieAlgebra R) + cartanElement R x + (yE : PresentedLieAlgebra R)) =
      yF := by
  simp [negativeProj]

@[simp]
theorem cartanProj_add_add (hA : A.IsGeneralizedCartan)
    (yF : negativeSubalgebra R) (x : H) (yE : positiveSubalgebra R) :
    cartanProj R hA
        ((yF : PresentedLieAlgebra R) + cartanElement R x + (yE : PresentedLieAlgebra R)) =
      x := by
  simp [cartanProj]

@[simp]
theorem positiveProj_add_add (hA : A.IsGeneralizedCartan)
    (yF : negativeSubalgebra R) (x : H) (yE : positiveSubalgebra R) :
    positiveProj R hA
        ((yF : PresentedLieAlgebra R) + cartanElement R x + (yE : PresentedLieAlgebra R)) =
      yE := by
  simp [positiveProj]

@[simp]
theorem negativeProj_coe_negative (hA : A.IsGeneralizedCartan) (yF : negativeSubalgebra R) :
    negativeProj R hA (yF : PresentedLieAlgebra R) = yF := by
  simpa using negativeProj_add_add R hA yF 0 0

@[simp]
theorem negativeProj_cartanElement (hA : A.IsGeneralizedCartan) (x : H) :
    negativeProj R hA (cartanElement R x) = 0 := by
  simpa using negativeProj_add_add R hA 0 x 0

@[simp]
theorem negativeProj_coe_positive (hA : A.IsGeneralizedCartan) (yE : positiveSubalgebra R) :
    negativeProj R hA (yE : PresentedLieAlgebra R) = 0 := by
  simpa using negativeProj_add_add R hA 0 0 yE

@[simp]
theorem cartanProj_coe_negative (hA : A.IsGeneralizedCartan) (yF : negativeSubalgebra R) :
    cartanProj R hA (yF : PresentedLieAlgebra R) = 0 := by
  simpa using cartanProj_add_add R hA yF 0 0

@[simp]
theorem cartanProj_cartanElement (hA : A.IsGeneralizedCartan) (x : H) :
    cartanProj R hA (cartanElement R x) = x := by
  simpa using cartanProj_add_add R hA 0 x 0

@[simp]
theorem cartanProj_coe_positive (hA : A.IsGeneralizedCartan) (yE : positiveSubalgebra R) :
    cartanProj R hA (yE : PresentedLieAlgebra R) = 0 := by
  simpa using cartanProj_add_add R hA 0 0 yE

@[simp]
theorem positiveProj_coe_negative (hA : A.IsGeneralizedCartan) (yF : negativeSubalgebra R) :
    positiveProj R hA (yF : PresentedLieAlgebra R) = 0 := by
  simpa using positiveProj_add_add R hA yF 0 0

@[simp]
theorem positiveProj_cartanElement (hA : A.IsGeneralizedCartan) (x : H) :
    positiveProj R hA (cartanElement R x) = 0 := by
  simpa using positiveProj_add_add R hA 0 x 0

@[simp]
theorem positiveProj_coe_positive (hA : A.IsGeneralizedCartan) (yE : positiveSubalgebra R) :
    positiveProj R hA (yE : PresentedLieAlgebra R) = yE := by
  simpa using positiveProj_add_add R hA 0 0 yE

@[simp]
theorem cartanProj_positiveGenerator (hA : A.IsGeneralizedCartan) (i : I) :
    cartanProj R hA (positiveGenerator R i) = 0 :=
  cartanProj_coe_positive R hA ⟨positiveGenerator R i, positiveGenerator_mem_positiveSubalgebra R i⟩

@[simp]
theorem cartanProj_negativeGenerator (hA : A.IsGeneralizedCartan) (i : I) :
    cartanProj R hA (negativeGenerator R i) = 0 :=
  cartanProj_coe_negative R hA ⟨negativeGenerator R i, negativeGenerator_mem_negativeSubalgebra R i⟩

end TriangularEquiv

/-! ## Injectivity of `serreHom` and the derived algebra -/

section DerivedAlgebra

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- **Injectivity of `serreHom`.** For a generalized Cartan matrix `A`, the canonical homomorphism
`Matrix.ToLieAlgebra K A →ₗ⁅K⁆ PresentedLieAlgebra R` is injective: Mathlib's Serre presentation
embeds faithfully as the derived subalgebra `⁅𝔤, 𝔤⁆`. -/
theorem serreHom_injective [DecidableEq I] (hA : A.IsGeneralizedCartan) :
    Function.Injective (serreHom R) := by
  rw [← LieHom.ker_eq_bot, LieSubmodule.eq_bot_iff]
  intro z hz
  rw [LieHom.mem_ker] at hz
  have htop : z ∈
      (LieSubalgebra.lieSpan K (Matrix.ToLieAlgebra K A) (Set.range (serreF K A))).toSubmodule ⊔
        Submodule.span K (Set.range (serreH K A)) ⊔
      (LieSubalgebra.lieSpan K (Matrix.ToLieAlgebra K A) (Set.range (serreE K A))).toSubmodule := by
    rw [lieSpan_serreF_sup_span_serreH_sup_lieSpan_serreE_eq_top K A]
    exact Submodule.mem_top
  obtain ⟨ab, hab, yE, hyE, rfl⟩ := Submodule.mem_sup.mp htop
  obtain ⟨yF, hyF, yH, hyH, rfl⟩ := Submodule.mem_sup.mp hab
  let liftF : FreeLieAlgebra K I →ₗ⁅K⁆ Matrix.ToLieAlgebra K A :=
    FreeLieAlgebra.lift K (serreF K A)
  let liftE : FreeLieAlgebra K I →ₗ⁅K⁆ Matrix.ToLieAlgebra K A :=
    FreeLieAlgebra.lift K (serreE K A)
  have hrangeF : liftF.range =
      LieSubalgebra.lieSpan K (Matrix.ToLieAlgebra K A) (Set.range (serreF K A)) := by
    rw [LieHom.range_eq_map, ← TauCeti.FreeLieAlgebra.lieSpan_range_of_eq_top,
      LieSubalgebra.map_lieSpan, ← Set.range_comp]
    congr 1; ext i; simp [liftF]
  have hrangeE : liftE.range =
      LieSubalgebra.lieSpan K (Matrix.ToLieAlgebra K A) (Set.range (serreE K A)) := by
    rw [LieHom.range_eq_map, ← TauCeti.FreeLieAlgebra.lieSpan_range_of_eq_top,
      LieSubalgebra.map_lieSpan, ← Set.range_comp]
    congr 1; ext i; simp [liftE]
  rw [LieSubalgebra.mem_toSubmodule, ← hrangeF] at hyF
  rw [LieSubalgebra.mem_toSubmodule, ← hrangeE] at hyE
  obtain ⟨uF, rfl⟩ := hyF
  obtain ⟨uE, rfl⟩ := hyE
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hyH
  have hcompF : (serreHom R).comp liftF = negativeFreeLift R := by
    refine FreeLieAlgebra.hom_ext fun i => ?_
    simp [liftF]
  have hcompE : (serreHom R).comp liftE = positiveFreeLift R := by
    refine FreeLieAlgebra.hom_ext fun i => ?_
    simp [liftE]
  have hmapH : serreHom R (c.sum fun i r => r • serreH K A i) =
      cartanElement R (c.sum fun i r => r • R.coroot i) := by
    simp only [map_finsuppSum, map_smul, serreHom_serreH]
  simp only [map_add, LieHom.coe_toLinearMap, ← LieHom.comp_apply, hcompF, hcompE, hmapH] at hz
  obtain ⟨huF, hcoroot, huE⟩ :=
    (negativeFreeLift_add_cartanElement_add_positiveFreeLift_eq_zero_iff R hA).mp hz
  have hc0 : c = 0 := linearIndependent_iff.mp R.coroot_linearIndependent c hcoroot
  have hkerF : serreIdeal K A ≤ liftF.ker :=
    serreIdeal_le_ker_lift_iff.mpr (isSerreSystem_serre K A).ad_pow_lie_F_F
  have hkerE : serreIdeal K A ≤ liftE.ker :=
    serreIdeal_le_ker_lift_iff.mpr (isSerreSystem_serre K A).ad_pow_lie_E_E
  have hF0 : liftF uF = 0 := hkerF huF
  have hE0 : liftE uE = 0 := hkerE huE
  simp [hF0, hc0, hE0]

/-- **Isomorphism of `Matrix.ToLieAlgebra K A` onto the derived subalgebra `⁅𝔤, 𝔤⁆`.** -/
noncomputable def serreEquivDerived [DecidableEq I] (hA : A.IsGeneralizedCartan) :
    Matrix.ToLieAlgebra K A ≃ₗ⁅K⁆ derivedSeries K (PresentedLieAlgebra R) 1 :=
  ((serreHom R).equivRangeOfInjective (serreHom_injective R hA)).trans <|
    LieEquiv.ofEq (serreHom R).range
      (derivedSeries K (PresentedLieAlgebra R) 1 : LieSubalgebra K (PresentedLieAlgebra R))
      (congrArg SetLike.coe (range_serreHom_eq_derivedSeries R))

@[simp]
theorem coe_serreEquivDerived_apply [DecidableEq I] (hA : A.IsGeneralizedCartan)
    (x : Matrix.ToLieAlgebra K A) :
    (serreEquivDerived R hA x : PresentedLieAlgebra R) = serreHom R x :=
  (rfl)

/-- For a generalized Cartan matrix `A`, the intersection of the image of `serreHom R` with the
Cartan elements is the image of the coroot span `R.corootSpan`. -/
theorem range_serreHom_inf_range_cartanElement [DecidableEq I] (hA : A.IsGeneralizedCartan) :
    (serreHom R).range.toSubmodule ⊓ LinearMap.range (cartanElement R) =
      R.corootSpan.map (cartanElement R) := by
  refine le_antisymm ?_ (le_inf ?_ LinearMap.map_le_range)
  · rintro z ⟨hzS, x, rfl⟩
    rw [toSubmodule_range_serreHom R] at hzS
    obtain ⟨ab, hab, yE, hyE, hsum⟩ := Submodule.mem_sup.mp hzS
    obtain ⟨yF, hyF, _, ⟨x₀, hx₀, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hab
    have h0 : yF + cartanElement R (x₀ - x) + yE = 0 := by
      rw [map_sub]
      rw [← sub_eq_zero] at hsum
      convert hsum using 1
      abel
    have hx := sub_eq_zero.mp
      (eq_zero_of_negative_add_cartanElement_add_positive_eq_zero R hA hyF hyE h0).2.1
    exact ⟨x₀, hx₀, hx ▸ rfl⟩
  · rw [toSubmodule_range_serreHom R]
    exact le_sup_of_le_left le_sup_right

/-- **Derived intersection with the Cartan subalgebra.** For a generalized Cartan matrix `A`,
`⁅𝔤, 𝔤⁆ ∩ 𝔥` is precisely the image of `R.corootSpan` under `cartanElement R`. -/
theorem derivedSeries_one_inf_cartanSubalgebra (hA : A.IsGeneralizedCartan) :
    (derivedSeries K (PresentedLieAlgebra R) 1).toSubmodule ⊓ (cartanSubalgebra R).toSubmodule =
      R.corootSpan.map (cartanElement R) := by
  classical
  have hD : (derivedSeries K (PresentedLieAlgebra R) 1).toSubmodule =
      (serreHom R).range.toSubmodule :=
    congrArg LieSubalgebra.toSubmodule (range_serreHom_eq_derivedSeries R).symm
  rw [hD, toSubmodule_cartanSubalgebra, range_serreHom_inf_range_cartanElement R hA]

end DerivedAlgebra

/-! ## The degenerate empty-index-set case -/

section EmptyIndex

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

@[simp]
theorem positiveSubalgebra_eq_bot_of_isEmpty [IsEmpty I] : positiveSubalgebra R = ⊥ := by
  simp [positiveSubalgebra_def, Set.range_eq_empty]

@[simp]
theorem negativeSubalgebra_eq_bot_of_isEmpty [IsEmpty I] : negativeSubalgebra R = ⊥ := by
  simp [negativeSubalgebra_def, Set.range_eq_empty]

@[simp]
theorem cartanSubalgebra_eq_top_of_isEmpty [IsEmpty I] : cartanSubalgebra R = ⊤ := by
  rw [← LieSubalgebra.toSubmodule_inj]
  have h := negativeSubalgebra_sup_cartanSubalgebra_sup_positiveSubalgebra R
  simpa using h

/-- When `I` is empty, `cartanElement R : H →ₗ[K] PresentedLieAlgebra R` is bijective. -/
theorem cartanElement_bijective_of_isEmpty [IsEmpty I] :
    Function.Bijective (cartanElement R) := by
  refine ⟨cartanElement_injective R (Matrix.isGeneralizedCartan_of_isEmpty A), ?_⟩
  rw [← LinearMap.range_eq_top, ← toSubmodule_cartanSubalgebra]
  exact congrArg LieSubalgebra.toSubmodule (cartanSubalgebra_eq_top_of_isEmpty R)

/-- When `I` is empty, `cartanElement R` is a `K`-linear isomorphism `H ≃ₗ[K] PresentedLieAlgebra R`
onto an abelian Lie algebra of the full dimension of `H`. -/
noncomputable def cartanLinearEquivOfIsEmpty [IsEmpty I] :
    H ≃ₗ[K] PresentedLieAlgebra R :=
  LinearEquiv.ofBijective (cartanElement R) (cartanElement_bijective_of_isEmpty R)

@[simp]
theorem cartanLinearEquivOfIsEmpty_apply [IsEmpty I] (x : H) :
    cartanLinearEquivOfIsEmpty R x = cartanElement R x := (rfl)

instance [IsEmpty I] : IsLieAbelian (PresentedLieAlgebra R) := by
  constructor
  intro y z
  obtain ⟨u, rfl⟩ := (cartanElement_bijective_of_isEmpty R).2 y
  obtain ⟨v, rfl⟩ := (cartanElement_bijective_of_isEmpty R).2 z
  exact lie_cartanElement_cartanElement R u v

end EmptyIndex

/-! ## Sharpness of the Serre exponent -/

section SharpSerre

attribute [local instance 100] LieRing.ofAssociativeRing

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- **Sharpness of the Serre exponent (positive generators).** For a generalized Cartan matrix `A`,
distinct indices `i ≠ j`, and every `k ≤ (-A i j).toNat`, the iterated bracket `(ad eᵢ) ^ k eⱼ` is
nonzero in `PresentedLieAlgebra R` over any field `K`. For `k = (-A i j).toNat + 1`, the next
iterate vanishes by `ad_pow_lie_positiveGenerator_positiveGenerator`. -/
theorem ad_pow_positiveGenerator_ne_zero (hA : A.IsGeneralizedCartan) {i j : I} (hij : i ≠ j)
    {k : ℕ} (hk : k ≤ (-A i j).toNat) :
    (ad K (PresentedLieAlgebra R) (positiveGenerator R i) ^ k) (positiveGenerator R j) ≠ 0 := by
  classical
  set m : ℕ := (-A i j).toNat
  have hbracket : ∀ X Y : Module.End K (Fin (m + 2) → K), ⁅X, Y⁆ = X * Y - Y * X := fun X Y =>
    LinearMap.ext fun v => by
      simp only [LieHom.lie_apply, Module.End.lie_apply, LinearMap.sub_apply, mul_apply_eq_comp]
  let Ti : Module.End K (Fin (m + 2) → K) :=
    { toFun := fun v r => if h : 0 < r.1 ∧ r.1 ≤ m then v ⟨r.1 - 1, by omega⟩ else 0
      map_add' := fun v w => by ext r; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c v => by
        ext r; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
  let Tj : Module.End K (Fin (m + 2) → K) :=
    { toFun := fun v r => if r.1 = 0 then v ⟨m + 1, by omega⟩ else 0
      map_add' := fun v w => by ext r; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c v => by
        ext r; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
  have hji : Tj * Ti = 0 := by
    refine LinearMap.ext fun v => funext fun r => ?_
    simp only [mul_apply_eq_comp, LinearMap.zero_apply, Pi.zero_apply, Ti, Tj,
      LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs with h1 h2
    · omega
    · rfl
    · rfl
  have hjj : Tj * Tj = 0 := by
    refine LinearMap.ext fun v => funext fun r => ?_
    simp only [mul_apply_eq_comp, LinearMap.zero_apply, Pi.zero_apply, Tj,
      LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs with h1 h2
    · simp at h2
    · rfl
    · rfl
  have had_pow : ∀ n : ℕ, (ad K _ Ti ^ n) Tj = Ti ^ n * Tj := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ad_apply, ih, hbracket, ← mul_assoc, ← pow_succ',
        mul_assoc (Ti ^ n) Tj Ti, hji, mul_zero, sub_zero]
  have hpow_eval : ∀ n : ℕ, n ≤ m → ∀ (v : Fin (m + 2) → K) (r : Fin (m + 2)),
      ((Ti ^ n * Tj) v) r = if r.1 = n then v ⟨m + 1, by omega⟩ else 0 := by
    intro n hn
    induction n with
    | zero =>
      intro v r
      simp [Tj]
    | succ n ih =>
      intro v r
      have hstep : Ti ^ (n + 1) * Tj = Ti * (Ti ^ n * Tj) := by rw [pow_succ', mul_assoc]
      rw [hstep, mul_apply_eq_comp]
      dsimp only [Ti, LinearMap.coe_mk, AddHom.coe_mk]
      split_ifs with h1 h2
      · rw [ih (by omega) v ⟨r.1 - 1, by omega⟩]
        have heq : r.1 - 1 = n := by omega
        simp [heq]
      · rw [ih (by omega) v ⟨r.1 - 1, by omega⟩]
        have hne : r.1 - 1 ≠ n := by omega
        simp [hne]
      · omega
      · rfl
  have hpow_zero : Ti ^ (m + 1) * Tj = 0 := by
    refine LinearMap.ext fun v => funext fun r => ?_
    have hstep : Ti ^ (m + 1) * Tj = Ti * (Ti ^ m * Tj) := by rw [pow_succ', mul_assoc]
    rw [hstep, mul_apply_eq_comp, LinearMap.zero_apply, Pi.zero_apply]
    dsimp only [Ti, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs with h1
    · rw [hpow_eval m le_rfl v ⟨r.1 - 1, by omega⟩]
      have hne : r.1 - 1 ≠ m := by omega
      simp [hne]
    · rfl
  have hTj_rel : (ad K _ Tj ^ (-A j i).toNat) ⁅Tj, Ti⁆ = 0 := by
    rcases eq_or_ne (A i j) 0 with h0 | h0
    · have hm0 : m = 0 := by simp [m, h0]
      have hTi0 : Ti = 0 := by
        refine LinearMap.ext fun v => funext fun r => ?_
        dsimp only [Ti, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, Pi.zero_apply]
        split_ifs with h1
        · omega
        · rfl
      rw [hTi0, lie_zero, map_zero]
    · have hji_ne : A j i ≠ 0 := mt (hA.zero_comm i j).mpr h0
      obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero
        (hA.toNat_neg_pos_of_ne_of_ne_zero hij.symm hji_ne).ne'
      rw [hp, TauCeti.ad_pow_succ_apply]
      have h2 : ⁅Tj, ⁅Tj, Ti⁆⁆ = 0 := by
        rw [hbracket Tj Ti, hji, zero_sub, lie_neg, hbracket Tj (Ti * Tj), ← mul_assoc, hji,
          zero_mul, mul_assoc Ti Tj Tj, hjj, mul_zero, sub_self, neg_zero]
      rw [h2, map_zero]
  let f : I → Module.End K (Fin (m + 2) → K) := fun a =>
    if a = i then Ti else if a = j then Tj else 0
  let π : FreeLieAlgebra K I →ₗ⁅K⁆ Module.End K (Fin (m + 2) → K) := FreeLieAlgebra.lift K f
  have hker : serreIdeal K A ≤ π.ker :=
    serreIdeal_le_ker_lift_iff.mpr fun a b => by
      rcases eq_or_ne a b with rfl | hab
      · rw [lie_self, map_zero]
      by_cases hai : a = i
      · subst hai
        by_cases hbj : b = j
        · subst hbj
          simp only [f, ↓reduceIte, hab.symm]
          rw [← TauCeti.ad_pow_succ_apply, had_pow (m + 1), hpow_zero]
        · simp [f, hab.symm, hbj]
      by_cases haj : a = j
      · subst haj
        by_cases hbi : b = i
        · subst hbi
          simpa [f, hai] using hTj_rel
        · simp [f, hai, hbi, hab.symm]
      · simp [f, hai, haj]
  intro hzero
  let u : FreeLieAlgebra K I := (ad K _ (FreeLieAlgebra.of K i) ^ k) (FreeLieAlgebra.of K j)
  have hu_mem : u ∈ serreIdeal K A := by
    rw [← ker_positiveFreeLift R hA, LieHom.mem_ker]
    simpa [u, LieHom.map_ad_pow] using hzero
  have hπu : π u = 0 := hker hu_mem
  have hπu_eq : π u = Ti ^ k * Tj := by
    simp [u, π, f, hij.symm, LieHom.map_ad_pow, had_pow]
  rw [hπu_eq] at hπu
  let v₀ : Fin (m + 2) → K := fun s => if s.1 = m + 1 then 1 else 0
  have heval := congrFun (LinearMap.congr_fun hπu v₀) ⟨k, by omega⟩
  rw [hpow_eval k hk v₀ ⟨k, by omega⟩] at heval
  simp [v₀] at heval

/-- **Sharpness of the Serre exponent (negative generators).** For a generalized Cartan matrix `A`,
distinct indices `i ≠ j`, and every `k ≤ (-A i j).toNat`, the iterated bracket `(ad fᵢ) ^ k fⱼ` is
nonzero in `PresentedLieAlgebra R`. -/
theorem ad_pow_negativeGenerator_ne_zero (hA : A.IsGeneralizedCartan) {i j : I} (hij : i ≠ j)
    {k : ℕ} (hk : k ≤ (-A i j).toNat) :
    (ad K (PresentedLieAlgebra R) (negativeGenerator R i) ^ k) (negativeGenerator R j) ≠ 0 := by
  intro hzero
  apply ad_pow_positiveGenerator_ne_zero R hA hij hk
  have hchev := congrArg (chevalleyInvolution R).toLieHom hzero
  rw [LieHom.map_ad_pow, map_zero] at hchev
  simp only [LieEquiv.coe_toLieHom, chevalleyInvolution_negativeGenerator, map_neg] at hchev
  have hneg : (-ad K (PresentedLieAlgebra R) (positiveGenerator R i)) ^ k =
      ((-1 : K) ^ k) • ad K (PresentedLieAlgebra R) (positiveGenerator R i) ^ k := by
    rw [← neg_one_smul K (ad K (PresentedLieAlgebra R) (positiveGenerator R i)), smul_pow]
  rw [hneg, LinearMap.smul_apply, neg_eq_zero, smul_eq_zero] at hchev
  exact hchev.resolve_left (pow_ne_zero k (neg_ne_zero.mpr one_ne_zero))

end SharpSerre

/-! ### Examples -/

section Examples

variable {K H : Type*} [Field K] [AddCommGroup H] [Module K H]

/-- **Affine `A₁⁽¹⁾` Serre exponent check.** For `A = !![2, -2; -2, 2]` (`a₀₁ = -2`), the Serre
relation gives `(ad e₀) ^ 3 e₁ = 0`, whereas `(ad e₀) ^ 2 e₁ ≠ 0` over every field `K`. -/
example (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map
    (Int.cast : ℤ → K)) H) :
    (ad K _ (positiveGenerator R 0) ^ 3) (positiveGenerator R 1) = 0 ∧
      (ad K _ (positiveGenerator R 0) ^ 2) (positiveGenerator R 1) ≠ 0 := by
  have hA : (!![(2 : ℤ), -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).IsGeneralizedCartan :=
    { diag := by decide
      offDiag_nonpos := by simp [Fin.forall_fin_two]
      zero_comm := by simp [Fin.forall_fin_two] }
  refine ⟨?_, ad_pow_positiveGenerator_ne_zero R hA (by decide) (by decide)⟩
  have hserre := ad_pow_lie_positiveGenerator_positiveGenerator R 0 1
  rwa [← TauCeti.ad_pow_succ_apply] at hserre

/-- **Degenerate empty index set (`Fin 0`).** `Matrix.ToLieAlgebra K !![]` is zero (`Subsingleton`),
whereas `PresentedLieAlgebra R` is linearly isomorphic to `H` (and nontrivial whenever `H` is). -/
example (R : CartanRealization ((!![] : Matrix (Fin 0) (Fin 0) ℤ).map (Int.cast : ℤ → K)) H) :
    Subsingleton (Matrix.ToLieAlgebra K (!![] : Matrix (Fin 0) (Fin 0) ℤ)) ∧
      Nonempty (H ≃ₗ[K] PresentedLieAlgebra R) := by
  refine ⟨⟨fun x y => ?_⟩, ⟨cartanLinearEquivOfIsEmpty R⟩⟩
  have hbot : (⊤ : LieSubalgebra K (Matrix.ToLieAlgebra K (!![] : Matrix (Fin 0) (Fin 0) ℤ))) =
      ⊥ := by
    rw [← lieSpan_serreE_union_serreF_eq_top K (!![] : Matrix (Fin 0) (Fin 0) ℤ)]
    simp [Set.range_eq_empty]
  have hx : x ∈ (⊥ : LieSubalgebra K _) := hbot ▸ trivial
  have hy : y ∈ (⊥ : LieSubalgebra K _) := hbot ▸ trivial
  rw [(LieSubalgebra.mem_bot _).mp hx, (LieSubalgebra.mem_bot _).mp hy]

/-- **Necessity of zero-symmetry (`A i j = 0 ↔ A j i = 0`) for Cartan injectivity.** For the
matrix `A = !![2, -1; 0, 2]`, which satisfies `A i i = 2` and `A i j ≤ 0` (`i ≠ j`) but violates
`A 1 0 = 0 ↔ A 0 1 = 0`, the Serre relator `⁅e₁, e₀⁆ = 0` forces `e₁ = 0` and
`cartanElement R (R.coroot 1) = 0`, so `cartanElement R` is not injective. -/
example (R : CartanRealization ((!![(2 : ℤ), -1; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ).map
    (Int.cast : ℤ → K)) H) :
    ¬ Function.Injective (cartanElement R) := by
  have he10 : ⁅positiveGenerator R 1, positiveGenerator R 0⁆ = 0 := by
    simpa using ad_pow_lie_positiveGenerator_positiveGenerator R 1 0
  have hf0 := congrArg (fun z => ⁅negativeGenerator R 0, z⁆) he10
  rw [lie_zero, leibniz_lie, ← lie_skew (negativeGenerator R 0) (positiveGenerator R 1),
    lie_positiveGenerator_negativeGenerator_of_ne R (by decide), neg_zero, zero_lie, zero_add,
    ← lie_skew (negativeGenerator R 0) (positiveGenerator R 0),
    lie_positiveGenerator_negativeGenerator_self, lie_neg,
    ← lie_skew (positiveGenerator R 1), neg_neg, lie_cartanElement_positiveGenerator,
    R.root_coroot] at hf0
  have he1 : positiveGenerator R 1 = 0 := by simpa using hf0
  have hh1 : cartanElement R (R.coroot 1) = 0 := by
    rw [← lie_positiveGenerator_negativeGenerator_self, he1, zero_lie]
  exact fun hinj => R.coroot_linearIndependent.ne_zero 1
    (hinj (hh1.trans (map_zero (cartanElement R)).symm))

end Examples

end TauCeti.KacMoody
