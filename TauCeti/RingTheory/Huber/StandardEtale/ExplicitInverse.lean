/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.StandardEtale.Basic

/-!
# Explicit-inverse normal form for standard étale presentations

A standard étale presentation of `(C, C⁺)` over `(A, A⁺)` at scale `ϖ` requires the Jacobian
determinant `J_F = det (∂Fᵢ/∂Tⱼ)` of `F₁, …, F_N ∈ A⁺⟨T₁, …, T_N⟩` to become a unit `u` in `C`
satisfying `ϖ ^ k · u⁻¹ ∈ C⁺`, without requiring `u⁻¹` to be represented by an explicit coordinate
variable. Adjoining one auxiliary restricted variable `S = T_{N+1}` and the defining equation
`S · J_F - ϖ ^ k` (`TauCeti.Huber.explicitInverse`) puts the presentation into *explicit-inverse
form*:

* every equation of `explicitInverse ϖ F k` still lies in `A⁺⟨T₁, …, T_N, S⟩`, because `ϖ` is a
  pseudouniformiser and hence `ϖ ^ k ∈ A⁺` (`TauCeti.Huber.IsPseudoUniformizer.pow_mem_plus`);
* the `(N + 1) × (N + 1)` Jacobian matrix is block lower-triangular with bottom-right entry `J_F`,
  so `tateSeriesJacobian (explicitInverse ϖ F k)` equals `(ι J_F) ^ 2`
  (`TauCeti.Huber.tateSeriesJacobian_explicitInverse`);
* when `C` is a complete uniform Huber ring, any standard étale presentation `P` refines to an
  explicit-inverse presentation `P.withInverse` of the *same* Huber pair `(C, C⁺)` in `P.N + 1`
  variables with exponent `2 * P.k`, sending `S` to `ϖ ^ P.k · P.jacobianUnit⁻¹ ∈ C⁺`
  (`TauCeti.Huber.StandardEtalePresentation.withInverse`); and
* conversely, for *arbitrary* `F₁, …, F_N ∈ A⁺⟨T₁, …, T_N⟩` and `k : ℕ`, the quotient of
  `(A⟨T₁, …, T_N, S⟩, A⁺⟨T₁, …, T_N, S⟩)` by the closure of `(explicitInverse ϖ F k)` automatically
  carries a standard étale presentation with exponent `2 * k`
  (`TauCeti.Huber.StandardEtalePresentation.ofExplicitInverse`).

## Main definitions

* `TauCeti.Huber.explicitInverse`: adjoins `S` and the relation `S · J_F - ϖ ^ k` to a system
  `F : Fin N → tateSeries N A`.
* `TauCeti.Huber.StandardEtalePresentation.withInverse`: refines any presentation of a complete
  Huber pair `(C, C⁺)` to explicit-inverse form `(P.N + 1, explicitInverse ϖ P.F P.k, 2 * P.k, _)`.
* `TauCeti.Huber.StandardEtalePresentation.ofExplicitInverse`: the canonical quotient presentation
  cut out by `explicitInverse ϖ F k`.

## Main results

* `TauCeti.Huber.IsPseudoUniformizer.pow_mem_plus`: `ϖ ^ k ∈ A⁺` for every pseudouniformiser `ϖ`
  and every `k : ℕ`.
* `TauCeti.Huber.tateSeriesJacobian_explicitInverse`: the Jacobian determinant of
  `explicitInverse ϖ F k` is `(ι (tateSeriesJacobian F)) ^ 2`.
* `TauCeti.Huber.StandardEtalePresentation.ker_of_comp_renameAlgHom_and_last`: any continuous
  extension of `P.π` sending `S` to `ϖ ^ P.k · P.jacobianUnit⁻¹` has kernel equal to the closure of
  `(explicitInverse ϖ P.F P.k)`.
* `TauCeti.Huber.StandardEtalePresentation.nonempty_ofExplicitInverse`: every explicit-inverse
  system presents its canonical quotient Huber pair with exponent `2 * k`.

## References

* [R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*][huber1996], §1.6.
* [P. Scholze, *Étale cohomology of diamonds*][scholze2017], §24.
* [K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*][kedlaya_liu2015], §3.1.
-/

public section

open Topology

namespace TauCeti.Huber

/-! ### Powers of pseudouniformisers and the `explicitInverse` tuple -/

/-- Every natural-number power `ϖ ^ k` of a pseudouniformiser `ϖ` lies in `A⁺`, because `ϖ` is
topologically nilpotent (`A°° ⊆ A⁺`) and `A⁺` is a subring. -/
theorem IsPseudoUniformizer.pow_mem_plus {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    (Aplus : Pair A) (k : ℕ) : ϖ ^ k ∈ Aplus.plus :=
  Aplus.plus.pow_mem
    (Aplus.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent) k

section ExplicitInverseSystem

variable {N : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **The explicit-inverse system associated to `(F, k)` at scale `ϖ`.** Given `F : Fin N →
tateSeries N A`, this tuple in `N + 1` variables renames `F₀, …, F_{N-1}` into the first `N`
variables and appends `S · J_F - ϖ ^ k` in the last variable `S = X (Fin.last N)`. -/
noncomputable def explicitInverse (ϖ : A) (F : Fin N → tateSeries N A) (k : ℕ) :
    Fin (N + 1) → tateSeries (N + 1) A :=
  Fin.snoc
    (fun i ↦ tateSeries.renameAlgHom Fin.castSuccEmb (F i))
    (tateSeries.X (N + 1) A (Fin.last N) *
        tateSeries.renameAlgHom Fin.castSuccEmb (tateSeriesJacobian F) -
      algebraMap A (tateSeries (N + 1) A) (ϖ ^ k))

@[simp]
theorem explicitInverse_castSucc (ϖ : A) (F : Fin N → tateSeries N A) (k : ℕ) (i : Fin N) :
    explicitInverse ϖ F k i.castSucc = tateSeries.renameAlgHom Fin.castSuccEmb (F i) :=
  Fin.snoc_castSucc _ _ i

@[simp]
theorem explicitInverse_last (ϖ : A) (F : Fin N → tateSeries N A) (k : ℕ) :
    explicitInverse ϖ F k (Fin.last N) =
      tateSeries.X (N + 1) A (Fin.last N) *
          tateSeries.renameAlgHom Fin.castSuccEmb (tateSeriesJacobian F) -
        algebraMap A (tateSeries (N + 1) A) (ϖ ^ k) :=
  Fin.snoc_last _ _

/-- In zero variables (`N = 0`), `explicitInverse ϖ F k` consists of the single linear equation
`S - ϖ ^ k`. -/
@[simp]
theorem explicitInverse_zero (ϖ : A) (F : Fin 0 → tateSeries 0 A) (k : ℕ) :
    explicitInverse ϖ F k 0 =
      tateSeries.X 1 A 0 - algebraMap A (tateSeries 1 A) (ϖ ^ k) := by
  simpa using explicitInverse_last ϖ F k

/-- If every `F i` lies in `tateSeriesPlus N A Aplus` and `ϖ ^ k ∈ Aplus`, then every component of
`explicitInverse ϖ F k` lies in `tateSeriesPlus (N + 1) A Aplus`. -/
theorem explicitInverse_mem_tateSeriesPlus {Aplus : Subring A} {ϖ : A} {F : Fin N → tateSeries N A}
    {k : ℕ} (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus) (hϖk : ϖ ^ k ∈ Aplus)
    (i : Fin (N + 1)) :
    explicitInverse ϖ F k i ∈ tateSeriesPlus (N + 1) A Aplus := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [explicitInverse_last]
    refine sub_mem (mul_mem (tateSeries.X_mem_tateSeriesPlus Aplus _) ?_)
      (algebraMap_mem_tateSeriesPlus_iff.mpr hϖk)
    exact (tateSeries.renameAlgHom_mem_tateSeriesPlus_iff Fin.castSuccEmb).mpr
      (tateSeriesJacobian_mem_tateSeriesPlus hF)
  · rw [explicitInverse_castSucc]
    exact (tateSeries.renameAlgHom_mem_tateSeriesPlus_iff Fin.castSuccEmb).mpr (hF j)

/-- **The Jacobian determinant of `explicitInverse ϖ F k` is the square of the renamed Jacobian of
`F`.** Expanding along the last column (`S = X (Fin.last N)`), all top `N` entries vanish and the
bottom-right entry is `ι (tateSeriesJacobian F)`. -/
@[simp]
theorem tateSeriesJacobian_explicitInverse (ϖ : A) (F : Fin N → tateSeries N A) (k : ℕ) :
    tateSeriesJacobian (explicitInverse ϖ F k) =
      (tateSeries.renameAlgHom Fin.castSuccEmb (tateSeriesJacobian F)) ^ 2 := by
  rw [tateSeriesJacobian_def, Matrix.det_succ_column _ (Fin.last N)]
  have hnotMem : Fin.last N ∉ Set.range (Fin.castSuccEmb : Fin N ↪ Fin (N + 1)) := by
    rintro ⟨j, hj⟩
    exact Fin.castSucc_ne_last j hj
  rw [Finset.sum_eq_single (Fin.last N)]
  · have hsign : (-1 : tateSeries (N + 1) A) ^ ((Fin.last N : ℕ) + (Fin.last N : ℕ)) = 1 := by
      rw [Fin.val_last, ← two_mul, pow_mul]
      simp
    have hlast_entry :
        tateSeriesJacobianMatrix (explicitInverse ϖ F k) (Fin.last N) (Fin.last N) =
          tateSeries.renameAlgHom Fin.castSuccEmb (tateSeriesJacobian F) := by
      rw [tateSeriesJacobianMatrix_apply, explicitInverse_last, map_sub,
        tateSeries.pderiv_algebraMap, sub_zero, tateSeries.pderiv_mul,
        tateSeries.pderiv_renameAlgHom_of_notMem_range Fin.castSuccEmb hnotMem,
        tateSeries.pderiv_X_self, mul_zero, zero_add, mul_one]
    have hminor :
        ((tateSeriesJacobianMatrix (explicitInverse ϖ F k)).submatrix
            (Fin.last N).succAbove (Fin.last N).succAbove).det =
          tateSeries.renameAlgHom Fin.castSuccEmb (tateSeriesJacobian F) := by
      have hmat :
          (tateSeriesJacobianMatrix (explicitInverse ϖ F k)).submatrix
              (Fin.last N).succAbove (Fin.last N).succAbove =
            (tateSeries.renameAlgHom (A := A) Fin.castSuccEmb).toRingHom.mapMatrix
              (tateSeriesJacobianMatrix F) := by
        refine Matrix.ext fun i j ↦ ?_
        simp only [Matrix.submatrix_apply, Fin.succAbove_last, tateSeriesJacobianMatrix_apply,
          explicitInverse_castSucc, RingHom.mapMatrix_apply, Matrix.map_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [← Fin.castSuccEmb_apply]
        exact tateSeries.pderiv_renameAlgHom_apply Fin.castSuccEmb j (F i)
      rw [hmat, ← RingHom.map_det, tateSeriesJacobian_def]
      rfl
    rw [hsign, one_mul, hlast_entry, hminor, sq]
  · intro i _ hi
    obtain ⟨i₀, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    rw [tateSeriesJacobianMatrix_apply, explicitInverse_castSucc,
      tateSeries.pderiv_renameAlgHom_of_notMem_range Fin.castSuccEmb hnotMem, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (Fin.last N)) h

end ExplicitInverseSystem

/-! ### Extending presentations to explicit-inverse form and constructing quotient presentations -/

namespace StandardEtalePresentation

section ExplicitInverseExtension

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsTateRing A] {Aplus : Pair A} {ϖ : A}
  {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  [Algebra A C] {Cplus : Pair C}

/-- Any continuous `A`-algebra map `π' : tateSeries (P.N + 1) A →ₐ[A] C` extending `P.π` along
`Fin.castSuccEmb` is automatically a topological quotient map. -/
theorem isQuotientMap_of_comp_renameAlgHom (P : StandardEtalePresentation Aplus ϖ Cplus)
    {π' : tateSeries (P.N + 1) A →ₐ[A] C} (hπ' : Continuous π')
    (hcomp : π'.comp (tateSeries.renameAlgHom Fin.castSuccEmb) = P.π) :
    IsQuotientMap π' := by
  have hfn : (π' : tateSeries (P.N + 1) A → C) ∘ tateSeries.renameAlgHom Fin.castSuccEmb = P.π :=
    congrArg DFunLike.coe hcomp
  exact IsQuotientMap.of_comp (tateSeries.continuous_renameAlgHom Fin.castSuccEmb) hπ'
    (hfn ▸ P.isQuotientMap_π)

private theorem exists_continuous_algHom_to_explicitInverseQuotient
    (P : StandardEtalePresentation Aplus ϖ Cplus) :
    ∃ ψ : C →ₐ[A] tateSeries (P.N + 1) A ⧸
        (Ideal.span (Set.range (explicitInverse ϖ P.F P.k))).closure,
      Continuous ψ ∧
      ∀ f : tateSeries P.N A, ψ (P.π f) =
        Ideal.Quotient.mkₐ A (Ideal.span (Set.range (explicitInverse ϖ P.F P.k))).closure
          (tateSeries.renameAlgHom Fin.castSuccEmb f) := by
  let K : Ideal (tateSeries (P.N + 1) A) :=
    (Ideal.span (Set.range (explicitInverse ϖ P.F P.k))).closure
  have : IsClosed (K : Set (tateSeries (P.N + 1) A)) := by
    rw [Ideal.coe_closure]
    exact isClosed_closure
  have : T1Space (tateSeries (P.N + 1) A ⧸ K) := Ideal.Quotient.instT1Space K
  let q : tateSeries (P.N + 1) A →ₐ[A] tateSeries (P.N + 1) A ⧸ K := Ideal.Quotient.mkₐ A K
  let ι : tateSeries P.N A →ₐ[A] tateSeries (P.N + 1) A := tateSeries.renameAlgHom Fin.castSuccEmb
  have hqι_cont : Continuous (q.comp ι).toRingHom :=
    continuous_quotient_mk'.comp (tateSeries.continuous_renameAlgHom Fin.castSuccEmb)
  have hker_le : RingHom.ker P.toPairHom.toRingHom ≤ RingHom.ker (q.comp ι).toRingHom := by
    have hspan : (Ideal.span (Set.range P.F) : Set (tateSeries P.N A)) ⊆
        (RingHom.ker (q.comp ι).toRingHom : Set (tateSeries P.N A)) := by
      refine SetLike.coe_subset_coe.mpr (Ideal.span_le.mpr ?_)
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      change q (ι (P.F i)) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, ← SetLike.mem_coe,
        Ideal.coe_closure]
      exact subset_closure (Ideal.subset_span ⟨i.castSucc, explicitInverse_castSucc ϖ P.F P.k i⟩)
    have hcl : ((Ideal.span (Set.range P.F)).closure : Set (tateSeries P.N A)) ⊆
        (RingHom.ker (q.comp ι).toRingHom : Set (tateSeries P.N A)) := by
      rw [Ideal.coe_closure]
      exact closure_minimal hspan (isClosed_singleton.preimage hqι_cont)
    rw [P.toRingHom_toPairHom]
    exact P.ker_π.trans_le (SetLike.coe_subset_coe.mp hcl)
  have hI : ∀ a ∈ RingHom.ker P.toPairHom.toRingHom, (q.comp ι).toRingHom a = 0 :=
    fun _ hf ↦ RingHom.mem_ker.mp (hker_le hf)
  let ψ₀ : C →+* tateSeries (P.N + 1) A ⧸ K :=
    (Ideal.Quotient.lift (RingHom.ker P.toPairHom.toRingHom) (q.comp ι).toRingHom hI).comp
      P.isQuotientMapping_toPairHom.quotientKerInverse.toRingHom
  have hψ₀_cont : Continuous ψ₀ :=
    (Ideal.Quotient.continuous_lift (RingHom.ker P.toPairHom.toRingHom) hqι_cont hI).comp
      P.isQuotientMapping_toPairHom.quotientKerInverse.continuous_toRingHom
  have hψ₀_π : ∀ f : tateSeries P.N A, ψ₀ (P.π f) = q (ι f) := fun f ↦ by
    have hf : P.π f = P.toPairHom.toRingHom f := by rw [P.toRingHom_toPairHom]; rfl
    simp only [ψ₀, RingHom.comp_apply, Pair.Hom.IsQuotientMapping.toRingHom_quotientKerInverse,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [hf, RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]
    rfl
  exact ⟨{ ψ₀ with
      commutes' a := by
        rw [RingHom.toFun_eq_coe, ← P.π.commutes a, hψ₀_π, AlgHom.commutes, AlgHom.commutes] },
    hψ₀_cont, hψ₀_π⟩

private theorem ker_le_of_comp_renameAlgHom_and_last (P : StandardEtalePresentation Aplus ϖ Cplus)
    {π' : tateSeries (P.N + 1) A →ₐ[A] C} (hπ' : Continuous π')
    (hcomp : π'.comp (tateSeries.renameAlgHom Fin.castSuccEmb) = P.π)
    (hlast : π' (tateSeries.X (P.N + 1) A (Fin.last P.N)) =
      algebraMap A C (ϖ ^ P.k) * ↑P.jacobianUnit⁻¹) :
    RingHom.ker π' ≤ (Ideal.span (Set.range (explicitInverse ϖ P.F P.k))).closure := by
  let K : Ideal (tateSeries (P.N + 1) A) :=
    (Ideal.span (Set.range (explicitInverse ϖ P.F P.k))).closure
  have : IsClosed (K : Set (tateSeries (P.N + 1) A)) := by
    rw [Ideal.coe_closure]
    exact isClosed_closure
  have : T1Space (tateSeries (P.N + 1) A ⧸ K) := Ideal.Quotient.instT1Space K
  let q : tateSeries (P.N + 1) A →ₐ[A] tateSeries (P.N + 1) A ⧸ K := Ideal.Quotient.mkₐ A K
  obtain ⟨ψ, hψ_cont, hψ_π⟩ := P.exists_continuous_algHom_to_explicitInverseQuotient
  have hψπ'_eq_q : ψ.comp π' = q := by
    refine tateSeries.algHom_ext_of_continuous (hψ_cont.comp hπ') continuous_quotient_mk'
      fun i ↦ Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [AlgHom.comp_apply, hlast]
      have h0 : q (explicitInverse ϖ P.F P.k (Fin.last P.N)) = 0 := by
        rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, ← SetLike.mem_coe,
          Ideal.coe_closure]
        exact subset_closure (Ideal.subset_span ⟨Fin.last P.N, rfl⟩)
      rw [explicitInverse_last, map_sub, map_mul, sub_eq_zero] at h0
      have hψu : ψ P.jacobianUnit = q (tateSeries.renameAlgHom Fin.castSuccEmb P.jacobian) :=
        P.coe_jacobianUnit ▸ hψ_π P.jacobian
      have hprod :
          ψ (algebraMap A C (ϖ ^ P.k) * ↑P.jacobianUnit⁻¹) * ψ P.jacobianUnit =
            q (tateSeries.X (P.N + 1) A (Fin.last P.N)) * ψ P.jacobianUnit := by
        rw [← map_mul, mul_assoc, Units.inv_mul, mul_one, ψ.commutes, hψu, h0, q.commutes]
      simpa only [mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one] using
        congrArg (· * ψ ↑P.jacobianUnit⁻¹) hprod
    · rw [← Fin.castSuccEmb_apply, ← tateSeries.renameAlgHom_X Fin.castSuccEmb j,
        AlgHom.comp_apply, ← AlgHom.comp_apply π', hcomp]
      exact hψ_π (tateSeries.X P.N A j)
  intro h hh
  have hqh : q h = 0 := by
    rw [← hψπ'_eq_q, AlgHom.comp_apply, RingHom.mem_ker.mp hh, map_zero]
  rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hqh

private theorem closure_le_ker_of_comp_renameAlgHom_and_last
    (P : StandardEtalePresentation Aplus ϖ Cplus)
    {π' : tateSeries (P.N + 1) A →ₐ[A] C} (hπ' : Continuous π')
    (hcomp : π'.comp (tateSeries.renameAlgHom Fin.castSuccEmb) = P.π)
    (hlast : π' (tateSeries.X (P.N + 1) A (Fin.last P.N)) =
      algebraMap A C (ϖ ^ P.k) * ↑P.jacobianUnit⁻¹) :
    (Ideal.span (Set.range (explicitInverse ϖ P.F P.k))).closure ≤ RingHom.ker π' := by
  have : T2Space C := P.t2Space_target
  have hspan : (Ideal.span (Set.range (explicitInverse ϖ P.F P.k)) :
      Set (tateSeries (P.N + 1) A)) ⊆ (RingHom.ker π' : Set (tateSeries (P.N + 1) A)) := by
    refine SetLike.coe_subset_coe.mpr (Ideal.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · have hJ : π' (tateSeries.renameAlgHom Fin.castSuccEmb P.jacobian) = P.jacobianUnit := by
        rw [← AlgHom.comp_apply, hcomp, P.coe_jacobianUnit]
      rw [explicitInverse_last, map_sub, map_mul, π'.commutes, hlast, hJ, mul_assoc,
        Units.inv_mul, mul_one, sub_self]
    · rw [explicitInverse_castSucc, ← AlgHom.comp_apply, hcomp, P.π_F_eq_zero]
  have hcl : ((Ideal.span (Set.range (explicitInverse ϖ P.F P.k))).closure :
      Set (tateSeries (P.N + 1) A)) ⊆ (RingHom.ker π' : Set (tateSeries (P.N + 1) A)) := by
    rw [Ideal.coe_closure]
    exact closure_minimal hspan (isClosed_singleton.preimage hπ')
  exact SetLike.coe_subset_coe.mp hcl

/-- **Universal kernel characterization for explicit-inverse extensions.** Any continuous
`A`-algebra map `π' : tateSeries (P.N + 1) A →ₐ[A] C` extending `P.π` along `Fin.castSuccEmb` and
sending the auxiliary variable `S = X (Fin.last P.N)` to `ϖ ^ P.k · P.jacobianUnit⁻¹` has kernel
equal to the closure of `(explicitInverse ϖ P.F P.k)`. -/
theorem ker_of_comp_renameAlgHom_and_last (P : StandardEtalePresentation Aplus ϖ Cplus)
    {π' : tateSeries (P.N + 1) A →ₐ[A] C} (hπ' : Continuous π')
    (hcomp : π'.comp (tateSeries.renameAlgHom Fin.castSuccEmb) = P.π)
    (hlast : π' (tateSeries.X (P.N + 1) A (Fin.last P.N)) =
      algebraMap A C (ϖ ^ P.k) * ↑P.jacobianUnit⁻¹) :
    RingHom.ker π' = (Ideal.span (Set.range (explicitInverse ϖ P.F P.k))).closure :=
  le_antisymm (P.ker_le_of_comp_renameAlgHom_and_last hπ' hcomp hlast)
    (P.closure_le_ker_of_comp_renameAlgHom_and_last hπ' hcomp hlast)

/-- Any continuous extension `π'` of `P.π` sending `S` to `ϖ ^ P.k · P.jacobianUnit⁻¹` preserves the
integral-closure characterization of `Cplus.plus`. -/
theorem mem_plus_iff_of_comp_renameAlgHom_and_last (P : StandardEtalePresentation Aplus ϖ Cplus)
    {π' : tateSeries (P.N + 1) A →ₐ[A] C} (hπ' : Continuous π')
    (hcomp : π'.comp (tateSeries.renameAlgHom Fin.castSuccEmb) = P.π)
    (hlast : π' (tateSeries.X (P.N + 1) A (Fin.last P.N)) =
      algebraMap A C (ϖ ^ P.k) * ↑P.jacobianUnit⁻¹)
    (c : C) :
    c ∈ Cplus.plus ↔
      ((tateSeriesPlus (P.N + 1) A Aplus.plus).map
        (π' : tateSeries (P.N + 1) A →+* C)).subtype.IsIntegralElem c := by
  let R₀ : Subring C := (tateSeriesPlus P.N A Aplus.plus).map (P.π : tateSeries P.N A →+* C)
  let R₁ : Subring C :=
    (tateSeriesPlus (P.N + 1) A Aplus.plus).map (π' : tateSeries (P.N + 1) A →+* C)
  have hR₀_le_R₁ : R₀ ≤ R₁ := by
    rintro _ ⟨f, hf, rfl⟩
    refine Subring.mem_map.mpr ⟨tateSeries.renameAlgHom Fin.castSuccEmb f,
      (tateSeries.renameAlgHom_mem_tateSeriesPlus_iff Fin.castSuccEmb).mpr hf, ?_⟩
    exact congrArg (fun g : tateSeries P.N A →ₐ[A] C ↦ g f) hcomp
  have hR₁_le_Cplus : R₁ ≤ Cplus.plus := by
    rintro _ ⟨g, hg, rfl⟩
    have hpair := Aplus.weighted_plus_le_comap (k := P.N + 1) isWeightFamily_one_weight Cplus
      (ψ := (π' : tateSeries (P.N + 1) A →+* C)) hπ'
      (fun a ha ↦ by
        rw [← algebraMap_weightedRestrictedSubring, RingHom.coe_coe, π'.commutes]
        exact P.algebraMap_mem_plus ha)
      (fun i t ht ↦ by
        obtain rfl : t = 1 := Set.mem_singleton_iff.mp ht
        rw [map_one, one_mul, ← tateSeries.X_eq_weightedX, RingHom.coe_coe]
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · rw [hlast]
          exact P.pow_mul_jacobianUnit_inv_mem_plus
        · rw [← Fin.castSuccEmb_apply, ← tateSeries.renameAlgHom_X Fin.castSuccEmb j,
            ← AlgHom.comp_apply, hcomp]
          exact P.map_mem_plus (tateSeries.X_mem_tateSeriesPlus Aplus.plus j))
    exact hpair ((Aplus.weighted_plus_eq_tateSeriesPlus (P.N + 1)).symm ▸ hg)
  have := Cplus.isRingOfIntegralElements.isIntegrallyClosedIn
  refine ⟨fun hc ↦ ?_, fun hint ↦ ?_⟩
  · exact (P.mem_plus_iff_isIntegral.mp hc).map_of_comp_eq (Subring.inclusion hR₀_le_R₁)
      (RingHom.id C) (by ext; rfl)
  · have hint' : IsIntegral R₁ c := hint
    exact Subring.isIntegrallyClosedIn_iff.mp ‹_›
      (hint'.map_of_comp_eq (Subring.inclusion hR₁_le_Cplus) (RingHom.id C) (by ext; rfl))

/-- Any `A`-algebra map `π'` extending `P.π` along `Fin.castSuccEmb` maps the Jacobian of
`explicitInverse ϖ P.F P.k` to `P.jacobianUnit ^ 2`, with inverse bounded at exponent `2 * P.k`. -/
theorem exists_unit_jacobian_of_comp_renameAlgHom (P : StandardEtalePresentation Aplus ϖ Cplus)
    {π' : tateSeries (P.N + 1) A →ₐ[A] C}
    (hcomp : π'.comp (tateSeries.renameAlgHom Fin.castSuccEmb) = P.π) :
    ∃ J : tateSeries (P.N + 1) A,
      (J : MvPowerSeries (Fin (P.N + 1)) A) =
        (Matrix.of fun i j ↦
          MvPowerSeries.pderiv j (explicitInverse ϖ P.F P.k i :
            MvPowerSeries (Fin (P.N + 1)) A)).det ∧
      ∃ u : Cˣ, (u : C) = π' J ∧ algebraMap A C (ϖ ^ (2 * P.k)) * ↑u⁻¹ ∈ Cplus.plus := by
  refine ⟨tateSeriesJacobian (explicitInverse ϖ P.F P.k), coe_tateSeriesJacobian _,
    P.jacobianUnit ^ 2, ?_, ?_⟩
  · rw [Units.val_pow_eq_pow_val, P.coe_jacobianUnit, tateSeriesJacobian_explicitInverse, map_pow,
      ← AlgHom.comp_apply, hcomp]
  · have hsq :
        algebraMap A C (ϖ ^ (2 * P.k)) * ↑((P.jacobianUnit ^ 2)⁻¹) =
          (algebraMap A C (ϖ ^ P.k) * ↑P.jacobianUnit⁻¹) ^ 2 := by
      rw [mul_comm 2 P.k, pow_mul, map_pow, ← inv_pow, Units.val_pow_eq_pow_val, mul_pow]
    rw [hsq]
    exact Cplus.plus.pow_mem P.pow_mul_jacobianUnit_inv_mem_plus 2

end ExplicitInverseExtension

section WithInverseCoords

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsTateRing A] {Aplus : Pair A} {ϖ : A}
  {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsHuberRing C] [Algebra A C] {Cplus : Pair C}

/-- Evaluation tuple in `C` for `P.withInverse`: the images of the old variables `X 0, …, X (N - 1)`
followed by `ϖ ^ P.k · P.jacobianUnit⁻¹`. -/
noncomputable def withInverseCoords (P : StandardEtalePresentation Aplus ϖ Cplus) :
    Fin (P.N + 1) → C :=
  Fin.snoc (fun i ↦ P.π (tateSeries.X P.N A i))
    (algebraMap A C (ϖ ^ P.k) * ↑P.jacobianUnit⁻¹)

/-- Every coordinate of `P.withInverseCoords` lies in `Cplus.plus`. -/
theorem withInverseCoords_mem_plus (P : StandardEtalePresentation Aplus ϖ Cplus)
    (i : Fin (P.N + 1)) :
    P.withInverseCoords i ∈ Cplus.plus := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa [withInverseCoords] using P.pow_mul_jacobianUnit_inv_mem_plus
  · simpa [withInverseCoords] using P.map_mem_plus (tateSeries.X_mem_tateSeriesPlus Aplus.plus j)

/-- Every coordinate of `P.withInverseCoords` is power-bounded in `C`. -/
theorem isPowerBounded_withInverseCoords (P : StandardEtalePresentation Aplus ϖ Cplus)
    (i : Fin (P.N + 1)) :
    IsPowerBounded (P.withInverseCoords i) :=
  Cplus.isRingOfIntegralElements.isPowerBounded_of_mem (P.withInverseCoords_mem_plus i)

end WithInverseCoords

section WithInverse

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsTateRing A] {Aplus : Pair A} {ϖ : A}
  {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [IsHuberRing C] [CompleteSpace C] [Algebra A C] {Cplus : Pair C}

/-- The evaluation `A`-algebra homomorphism `tateSeries (P.N + 1) A →ₐ[A] C` at
`P.withInverseCoords`. -/
noncomputable def withInverseEvalAlgHom (P : StandardEtalePresentation Aplus ϖ Cplus) :
    tateSeries (P.N + 1) A →ₐ[A] C :=
  letI : T2Space C := P.t2Space_target
  tateSeries.evalAlgHom P.continuous_algebraMap.continuousAt P.isPowerBounded_withInverseCoords

theorem continuous_withInverseEvalAlgHom (P : StandardEtalePresentation Aplus ϖ Cplus) :
    Continuous P.withInverseEvalAlgHom := by
  have : T2Space C := P.t2Space_target
  exact tateSeries.continuous_evalAlgHom P.continuous_algebraMap.continuousAt
    P.isPowerBounded_withInverseCoords

@[simp]
theorem withInverseEvalAlgHom_X (P : StandardEtalePresentation Aplus ϖ Cplus)
    (i : Fin (P.N + 1)) :
    P.withInverseEvalAlgHom (tateSeries.X (P.N + 1) A i) = P.withInverseCoords i := by
  have : T2Space C := P.t2Space_target
  exact tateSeries.evalAlgHom_X P.continuous_algebraMap.continuousAt
    P.isPowerBounded_withInverseCoords i

theorem withInverseEvalAlgHom_comp_renameAlgHom (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverseEvalAlgHom.comp (tateSeries.renameAlgHom Fin.castSuccEmb) = P.π := by
  have : T2Space C := P.t2Space_target
  refine tateSeries.algHom_ext_of_continuous
    (P.continuous_withInverseEvalAlgHom.comp (tateSeries.continuous_renameAlgHom Fin.castSuccEmb))
    P.continuous_π fun i ↦ ?_
  simp [withInverseCoords]

theorem withInverseEvalAlgHom_last (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverseEvalAlgHom (tateSeries.X (P.N + 1) A (Fin.last P.N)) =
      algebraMap A C (ϖ ^ P.k) * ↑P.jacobianUnit⁻¹ := by
  simp [withInverseCoords]

/-- **Refinement of a standard étale presentation to explicit-inverse form.** Over a complete
uniform Huber pair `(C, C⁺)`, any presentation `P` refines to a presentation `P.withInverse` of
the same pair `(C, C⁺)` with `N' = P.N + 1`, `F' = explicitInverse ϖ P.F P.k`, and `k' = 2 * P.k`,
evaluating the new variable `S` to `ϖ ^ P.k · P.jacobianUnit⁻¹ ∈ C⁺`.

Marked `@[expose]` so `P.withInverse.N` is definitionally `P.N + 1`, allowing `withInverse_F`,
`withInverse_π_castSucc`, and `withInverse_π_last` to elaborate across modules. -/
@[expose]
noncomputable def withInverse (P : StandardEtalePresentation Aplus ϖ Cplus) :
    StandardEtalePresentation Aplus ϖ Cplus where
  isPseudoUniformizer := P.isPseudoUniformizer
  N := P.N + 1
  F := explicitInverse ϖ P.F P.k
  F_mem_plus := explicitInverse_mem_tateSeriesPlus P.F_mem_plus
    (P.isPseudoUniformizer.pow_mem_plus Aplus P.k)
  k := 2 * P.k
  π := P.withInverseEvalAlgHom
  isQuotientMap_π := P.isQuotientMap_of_comp_renameAlgHom P.continuous_withInverseEvalAlgHom
    P.withInverseEvalAlgHom_comp_renameAlgHom
  ker_π := P.ker_of_comp_renameAlgHom_and_last P.continuous_withInverseEvalAlgHom
    P.withInverseEvalAlgHom_comp_renameAlgHom P.withInverseEvalAlgHom_last
  mem_plus_iff := P.mem_plus_iff_of_comp_renameAlgHom_and_last P.continuous_withInverseEvalAlgHom
    P.withInverseEvalAlgHom_comp_renameAlgHom P.withInverseEvalAlgHom_last
  exists_unit_jacobian := P.exists_unit_jacobian_of_comp_renameAlgHom
    P.withInverseEvalAlgHom_comp_renameAlgHom

@[simp]
theorem withInverse_N (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverse.N = P.N + 1 :=
  (rfl)

@[simp]
theorem withInverse_F (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverse.F = explicitInverse ϖ P.F P.k :=
  (rfl)

@[simp]
theorem withInverse_k (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverse.k = 2 * P.k :=
  (rfl)

/-- `P.withInverse.π` extends `P.π` along `Fin.castSuccEmb`. -/
theorem withInverse_π_comp_renameAlgHom (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverse.π.comp (tateSeries.renameAlgHom Fin.castSuccEmb) = P.π :=
  P.withInverseEvalAlgHom_comp_renameAlgHom

@[simp]
theorem withInverse_π_castSucc (P : StandardEtalePresentation Aplus ϖ Cplus) (i : Fin P.N) :
    P.withInverse.π (tateSeries.X (P.N + 1) A i.castSucc) = P.π (tateSeries.X P.N A i) :=
  (P.withInverseEvalAlgHom_X i.castSucc).trans (Fin.snoc_castSucc _ _ i)

@[simp]
theorem withInverse_π_last (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverse.π (tateSeries.X (P.N + 1) A (Fin.last P.N)) =
      algebraMap A C (ϖ ^ P.k) * ↑P.jacobianUnit⁻¹ :=
  P.withInverseEvalAlgHom_last

/-- In `P.withInverse`, the image of the auxiliary variable `S = X (Fin.last P.N)` satisfies
`π' S * P.π P.jacobian = ϖ ^ P.k` in `C`. -/
theorem withInverse_π_last_mul_jacobian (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverse.π (tateSeries.X (P.N + 1) A (Fin.last P.N)) * P.π P.jacobian =
      algebraMap A C (ϖ ^ P.k) := by
  rw [P.withInverse_π_last, mul_assoc, ← P.coe_jacobianUnit, Units.inv_mul, mul_one]

end WithInverse

section OfExplicitInverse

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

/-- In the quotient of `(A⟨T₁, …, T_N, S⟩, A⁺⟨T₁, …, T_N, S⟩)` by the closure of
`(explicitInverse ϖ F k)`, the Jacobian determinant of `explicitInverse ϖ F k` automatically maps to
a unit `u` satisfying `ϖ ^ (2 * k) · u⁻¹ ∈ Q⁺`, with no assumption on `F`. -/
theorem exists_unit_jacobian_explicitInverse {N : ℕ} (Aplus : Pair A) {ϖ : A}
    (hϖ : IsPseudoUniformizer ϖ) (F : Fin N → tateSeries N A) (k : ℕ) :
    ∃ u : (tateSeries (N + 1) A ⧸
        (Ideal.span (Set.range (explicitInverse ϖ F k))).closure)ˣ,
      (u : tateSeries (N + 1) A ⧸
          (Ideal.span (Set.range (explicitInverse ϖ F k))).closure) =
        Ideal.Quotient.mk (Ideal.span (Set.range (explicitInverse ϖ F k))).closure
          (tateSeriesJacobian (explicitInverse ϖ F k)) ∧
      algebraMap A (tateSeries (N + 1) A ⧸
          (Ideal.span (Set.range (explicitInverse ϖ F k))).closure) (ϖ ^ (2 * k)) * ↑u⁻¹ ∈
        ((Aplus.weighted (k := N + 1) isWeightFamily_one_weight).quotient
          (Ideal.span (Set.range (explicitInverse ϖ F k))).closure).plus := by
  let G := explicitInverse ϖ F k
  let K : Ideal (tateSeries (N + 1) A) := (Ideal.span (Set.range G)).closure
  let q : tateSeries (N + 1) A →+* tateSeries (N + 1) A ⧸ K := Ideal.Quotient.mk K
  let sQ : tateSeries (N + 1) A ⧸ K := q (tateSeries.X (N + 1) A (Fin.last N))
  let jQ : tateSeries (N + 1) A ⧸ K :=
    q (tateSeries.renameAlgHom Fin.castSuccEmb (tateSeriesJacobian F))
  obtain ⟨uϖ, huϖ⟩ := hϖ.isUnit
  let v : (tateSeries (N + 1) A ⧸ K)ˣ :=
    Units.map (algebraMap A (tateSeries (N + 1) A ⧸ K)).toMonoidHom (uϖ ^ k)
  have hv : (v : tateSeries (N + 1) A ⧸ K) = algebraMap A _ (ϖ ^ k) := by
    simp [v, huϖ]
  have hrel : sQ * jQ = (v : tateSeries (N + 1) A ⧸ K) := by
    have hmem : G (Fin.last N) ∈ K := by
      rw [← SetLike.mem_coe, Ideal.coe_closure]
      exact subset_closure (Ideal.subset_span ⟨Fin.last N, rfl⟩)
    have h0 : q (G (Fin.last N)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    dsimp only [G] at h0
    rw [explicitInverse_last, map_sub, map_mul, sub_eq_zero] at h0
    exact h0.trans hv.symm
  have hjQ_unit : jQ * (↑v⁻¹ * sQ) = 1 := by
    rw [mul_comm jQ, mul_assoc, hrel, Units.inv_mul]
  let w : (tateSeries (N + 1) A ⧸ K)ˣ :=
    ⟨jQ, ↑v⁻¹ * sQ, hjQ_unit, by rw [mul_comm]; exact hjQ_unit⟩
  have hw_inv_bound : algebraMap A (tateSeries (N + 1) A ⧸ K) (ϖ ^ k) * ↑w⁻¹ = sQ := by
    rw [← hv]
    change (v : tateSeries (N + 1) A ⧸ K) * (↑v⁻¹ * sQ) = sQ
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hsQ_mem :
      sQ ∈ ((Aplus.weighted (k := N + 1) isWeightFamily_one_weight).quotient K).plus := by
    simpa only [Pair.Hom.toRingHom_quotientHom] using
      (Pair.quotientHom (Aplus.weighted (k := N + 1) isWeightFamily_one_weight) K).map_mem_plus
        (tateSeries.X (N + 1) A (Fin.last N))
        ((Aplus.weighted_plus_eq_tateSeriesPlus (N + 1)).symm ▸
          tateSeries.X_mem_tateSeriesPlus Aplus.plus (Fin.last N))
  refine ⟨w ^ 2, ?_, ?_⟩
  · rw [Units.val_pow_eq_pow_val]
    change jQ ^ 2 = q (tateSeriesJacobian G)
    rw [tateSeriesJacobian_explicitInverse, map_pow]
  · have hsq :
        algebraMap A (tateSeries (N + 1) A ⧸ K) (ϖ ^ (2 * k)) * ↑((w ^ 2)⁻¹) = sQ ^ 2 := by
      rw [mul_comm 2 k, pow_mul, map_pow, ← inv_pow, Units.val_pow_eq_pow_val, ← mul_pow,
        hw_inv_bound]
    rw [hsq]
    exact pow_mem hsQ_mem 2

/-- **Canonical quotient presentation of any explicit-inverse system.** Given arbitrary
`F : Fin N → tateSeries N A` with coefficients in `A⁺`, any `k : ℕ`, and `hϖ : IsPseudoUniformizer
ϖ`, the quotient of `(A⟨T₁, …, T_N, S⟩, A⁺⟨T₁, …, T_N, S⟩)` by the closure of `(explicitInverse ϖ F
k)` carries a standard étale presentation with `N' = N + 1`, `F' = explicitInverse ϖ F k`, and
`k' = 2 * k`.

Marked `@[expose]` so `(ofExplicitInverse …).N` is definitionally `N + 1`. -/
@[expose]
noncomputable def ofExplicitInverse {N : ℕ} (Aplus : Pair A) {ϖ : A}
    (hϖ : IsPseudoUniformizer ϖ) (F : Fin N → tateSeries N A)
    (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus.plus) (k : ℕ) :
    StandardEtalePresentation Aplus ϖ
      ((Aplus.weighted (k := N + 1) isWeightFamily_one_weight).quotient
        (Ideal.span (Set.range (explicitInverse ϖ F k))).closure) :=
  ofQuotient Aplus hϖ (explicitInverse ϖ F k)
    (explicitInverse_mem_tateSeriesPlus hF (hϖ.pow_mem_plus Aplus k))
    (2 * k) (exists_unit_jacobian_explicitInverse Aplus hϖ F k)

@[simp]
theorem ofExplicitInverse_N {N : ℕ} (Aplus : Pair A) {ϖ : A}
    (hϖ : IsPseudoUniformizer ϖ) (F : Fin N → tateSeries N A)
    (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus.plus) (k : ℕ) :
    (ofExplicitInverse Aplus hϖ F hF k).N = N + 1 :=
  (rfl)

@[simp]
theorem ofExplicitInverse_F {N : ℕ} (Aplus : Pair A) {ϖ : A}
    (hϖ : IsPseudoUniformizer ϖ) (F : Fin N → tateSeries N A)
    (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus.plus) (k : ℕ) :
    (ofExplicitInverse Aplus hϖ F hF k).F = explicitInverse ϖ F k :=
  (rfl)

@[simp]
theorem ofExplicitInverse_k {N : ℕ} (Aplus : Pair A) {ϖ : A}
    (hϖ : IsPseudoUniformizer ϖ) (F : Fin N → tateSeries N A)
    (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus.plus) (k : ℕ) :
    (ofExplicitInverse Aplus hϖ F hF k).k = 2 * k :=
  (rfl)

@[simp]
theorem ofExplicitInverse_π {N : ℕ} (Aplus : Pair A) {ϖ : A}
    (hϖ : IsPseudoUniformizer ϖ) (F : Fin N → tateSeries N A)
    (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus.plus) (k : ℕ) :
    (ofExplicitInverse Aplus hϖ F hF k).π =
      Ideal.Quotient.mkₐ A (Ideal.span (Set.range (explicitInverse ϖ F k))).closure :=
  (rfl)

/-- Every explicit-inverse system presents its canonical quotient Huber pair with exponent
`2 * k`. -/
theorem nonempty_ofExplicitInverse {N : ℕ} (Aplus : Pair A) {ϖ : A}
    (hϖ : IsPseudoUniformizer ϖ) (F : Fin N → tateSeries N A)
    (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus.plus) (k : ℕ) :
    Nonempty (StandardEtalePresentation Aplus ϖ
      ((Aplus.weighted (k := N + 1) isWeightFamily_one_weight).quotient
        (Ideal.span (Set.range (explicitInverse ϖ F k))).closure)) :=
  ⟨ofExplicitInverse Aplus hϖ F hF k⟩

end OfExplicitInverse

end StandardEtalePresentation

end TauCeti.Huber

end
