/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.RingTheory.Ideal.Quotient.Star
import TauCeti.RingTheory.TraceFunctional.Positive

/-!
# The Jones quotient at `δ = √3` as the inversion-fixed cubic quantum torus

Building on `cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)`, this file
defines coordinate inclusions `cubicIncl` and `cubicFixedIncl`, proves the Markov trace identity
`tr m x = (√3) ^ m * scalarTrace (cubicFactor (m - 1)) (cubicFixedHom m x)`
(`isMarkovTrace_cubicFixedTrace`), establishes positivity, identifies the trace radical with
`RingHom.ker (cubicFixedHom m)`, constructs the Jones quotient equivalence
`IsMarkovTrace.quotientCubicFixedEquiv`, packages `exists_cubicFixedModel`, and proves
`cubicFixedHom_jonesWenzl_five`.
-/

public section

open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

open TwistedMonoidAlgebra (basis scalarTrace mapStarAlgHom scalarTracePositiveFunctional
  nullSubmodule_scalarTracePositiveFunctional)

private def cubicSnocHom (N : ℕ) :
    Multiplicative (Fin N → ZMod 3) →* Multiplicative (Fin (N + 1) → ZMod 3) where
  toFun a := Multiplicative.ofAdd (Fin.snoc a.toAdd 0)
  map_one' := Multiplicative.toAdd.injective <| funext fun k ↦
    Fin.lastCases (by simp) (fun _ ↦ by simp) k
  map_mul' _ _ := Multiplicative.toAdd.injective <| funext fun k ↦
    Fin.lastCases (by simp) (fun _ ↦ by simp) k
private theorem cubicSnocHom_injective (N : ℕ) : Function.Injective (cubicSnocHom N) :=
  fun _ _ hab ↦ Multiplicative.toAdd.injective <| funext fun i ↦ by
    simpa [cubicSnocHom] using congrFun (congrArg Multiplicative.toAdd hab) i.castSucc
theorem chainForm_snoc_zero (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm (N + 1) (Fin.snoc a 0) (Fin.snoc b 0) = chainForm N a b := by
  cases N with
  | zero => simp [chainForm_def]
  | succ n =>
    rw [chainForm_def, chainForm_def]; change ∑ i : Fin (n + 1), _ = ∑ i : Fin n, _
    rw [Fin.sum_univ_castSucc]
    have hlast : (⟨(Fin.last n).1 + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) :=
      Fin.ext (by simp)
    simp only [hlast, Fin.snoc_last, mul_zero, sub_self, add_zero]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h0 : (⟨i.castSucc.1, by omega⟩ : Fin (n + 2)) =
      (⟨i.1, by omega⟩ : Fin (n + 1)).castSucc := rfl
    have h1 : (⟨i.castSucc.1 + 1, by omega⟩ : Fin (n + 2)) =
      (⟨i.1 + 1, by omega⟩ : Fin (n + 1)).castSucc := rfl
    rw [h0, h1]; simp only [Fin.snoc_castSucc]
private theorem cubicFactor_cubicSnocHom (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor (N + 1) (cubicSnocHom N a) (cubicSnocHom N b) = cubicFactor N a b := by
  simp [cubicFactor_def, cubicSnocHom, chainForm_snoc_zero]

/-- Coordinate `⋆`-algebra inclusion `CubicTorus N →⋆ₐ[ℂ] CubicTorus (N + 1)` extending
`Fin N → ZMod 3` by zero in the last coordinate. -/
noncomputable def cubicIncl (N : ℕ) : CubicTorus N →⋆ₐ[ℂ] CubicTorus (N + 1) :=
  mapStarAlgHom (cubicSnocHom N) (cubicFactor_cubicSnocHom N)
@[simp] theorem cubicIncl_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicIncl N (weyl N a) = weyl (N + 1) (Multiplicative.ofAdd (Fin.snoc a.toAdd 0)) := by
  rw [cubicIncl, weyl_def, weyl_def]
  exact TwistedMonoidAlgebra.mapStarAlgHom_of (cubicSnocHom N) (cubicFactor_cubicSnocHom N) a
@[simp] theorem cubicIncl_cubicSite (N : ℕ) (j : Fin N) :
    cubicIncl N (cubicSite N j) = cubicSite (N + 1) j.castSucc := by
  have hsnoc : Fin.snoc (Pi.single j (1 : ZMod 3) : Fin N → ZMod 3) 0 =
      (Pi.single j.castSucc (1 : ZMod 3) : Fin (N + 1) → ZMod 3) :=
    funext fun k ↦ Fin.lastCases (by simp [(Fin.castSucc_lt_last j).ne'])
      (fun _ ↦ by simp [Pi.single_apply]) k
  simp [cubicSite_def, hsnoc]
@[simp] theorem cubicIncl_cubicProjection (N : ℕ) (j : Fin N) :
    cubicIncl N (cubicProjection N j) = cubicProjection (N + 1) j.castSucc := by
  simp [cubicProjection_def]
@[simp] theorem cubicIncl_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicIncl N (cubicInversion N x) = cubicInversion (N + 1) (cubicIncl N x) :=
  AlgHom.congr_fun (TwistedMonoidAlgebra.algHom_ext fun a ↦ by
    simp only [AlgHom.comp_apply, StarAlgHom.coe_toAlgHom, ← weyl_def, cubicInversion_weyl,
      cubicIncl_weyl]
    exact congrArg (weyl (N + 1)) <| Multiplicative.toAdd.injective <| funext fun k ↦
      Fin.lastCases (by simp) (fun _ ↦ by simp) k :
    (cubicIncl N).toAlgHom.comp (cubicInversion N).toAlgHom =
      (cubicInversion (N + 1)).toAlgHom.comp (cubicIncl N).toAlgHom) x
@[simp] theorem scalarTrace_cubicIncl (N : ℕ) (x : CubicTorus N) :
    scalarTrace (cubicFactor (N + 1)) (cubicIncl N x) = scalarTrace (cubicFactor N) x :=
  TwistedMonoidAlgebra.scalarTrace_mapStarAlgHom
    (cubicFactor_cubicSnocHom N) (cubicSnocHom_injective N) x
theorem cubicIncl_injective (N : ℕ) : Function.Injective (cubicIncl N) :=
  TwistedMonoidAlgebra.mapStarAlgHom_injective
    (cubicFactor_cubicSnocHom N) (cubicSnocHom_injective N)
theorem cubicIncl_mem_cubicFixed (N : ℕ) {x : CubicTorus N} (hx : x ∈ cubicFixed N) :
    cubicIncl N x ∈ cubicFixed (N + 1) := by
  rw [mem_cubicFixed, ← cubicIncl_cubicInversion, mem_cubicFixed.mp hx]
theorem cubicIncl_mem_cubicFixed_iff (N : ℕ) {x : CubicTorus N} :
    cubicIncl N x ∈ cubicFixed (N + 1) ↔ x ∈ cubicFixed N :=
  ⟨fun h ↦ by
    rw [mem_cubicFixed] at h ⊢; exact cubicIncl_injective N (by rw [cubicIncl_cubicInversion, h]),
    cubicIncl_mem_cubicFixed N⟩

/-- The restricted coordinate `⋆`-algebra inclusion `cubicFixed N →⋆ₐ[ℂ] cubicFixed (N + 1)`. -/
noncomputable def cubicFixedIncl (N : ℕ) : cubicFixed N →⋆ₐ[ℂ] cubicFixed (N + 1) :=
  ((cubicIncl N).comp (cubicFixed N).subtype).codRestrict (cubicFixed (N + 1)) fun x ↦
    cubicIncl_mem_cubicFixed N x.2
@[simp] theorem coe_cubicFixedIncl (N : ℕ) (x : cubicFixed N) :
    (cubicFixedIncl N x : CubicTorus (N + 1)) = cubicIncl N x := (rfl)
theorem cubicFixedIncl_injective (N : ℕ) : Function.Injective (cubicFixedIncl N) :=
  fun _ _ hxy ↦ Subtype.ext (cubicIncl_injective N (congrArg Subtype.val hxy))
theorem cubicFixedHom_strandIncl (n : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1)) :
    cubicFixedHom (n + 2) (strandIncl x) = cubicFixedIncl n (cubicFixedHom (n + 1) x) :=
  AlgHom.congr_fun (TemperleyLieb.hom_ext fun i ↦ Subtype.ext <| by
    simp only [AlgHom.comp_apply, StarAlgHom.coe_toAlgHom, strandIncl_e, coe_cubicFixedHom_e,
      coe_cubicFixedIncl, map_smul]
    exact congrArg ((Real.sqrt 3 : ℂ) • ·) (cubicIncl_cubicProjection n i).symm :
    (cubicFixedHom (n + 2)).toAlgHom.comp strandIncl =
      (cubicFixedIncl n).toAlgHom.comp (cubicFixedHom (n + 1)).toAlgHom) x
theorem scalarTrace_cubicIncl_mul_cubicProjection_last (N : ℕ) (x : CubicTorus N) :
    scalarTrace (cubicFactor (N + 1))
        (cubicIncl N x * cubicProjection (N + 1) (Fin.last N)) =
      (3 : ℂ)⁻¹ * scalarTrace (cubicFactor N) x :=
  LinearMap.congr_fun ((basis ℂ _ (cubicFactor N)).ext fun a ↦ by
    have hne1 : Multiplicative.ofAdd (Fin.snoc a.toAdd 0) *
        Multiplicative.ofAdd (Pi.single (Fin.last N) (1 : ZMod 3) : Fin (N + 1) → ZMod 3) ≠ 1 :=
      fun h ↦ by simpa using congrFun (congrArg Multiplicative.toAdd h) (Fin.last N)
    have hne2 : Multiplicative.ofAdd (Fin.snoc a.toAdd 0) *
        (Multiplicative.ofAdd
          (Pi.single (Fin.last N) (1 : ZMod 3) : Fin (N + 1) → ZMod 3))⁻¹ ≠ 1 :=
      fun h ↦ by simpa using congrFun (congrArg Multiplicative.toAdd h) (Fin.last N)
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
      StarAlgHom.coe_toAlgHom, LinearMap.smul_apply, smul_eq_mul,
      TwistedMonoidAlgebra.basis_apply, ← weyl_def, cubicIncl_weyl, cubicProjection_def,
      cubicSite_def, weyl_sq, mul_smul_comm, mul_add, mul_one, weyl_mul, map_smul, map_add]
    rw [weyl_def, weyl_def, weyl_def, TwistedMonoidAlgebra.scalarTrace_of_ne_one _ hne1,
      TwistedMonoidAlgebra.scalarTrace_of_ne_one _ hne2, ← weyl_def, ← cubicIncl_weyl,
      scalarTrace_cubicIncl]; simp :
    (scalarTrace (cubicFactor (N + 1))).comp
      ((LinearMap.mulRight ℂ (cubicProjection (N + 1) (Fin.last N))).comp
        (cubicIncl N).toAlgHom.toLinearMap) = (3 : ℂ)⁻¹ • scalarTrace (cubicFactor N)) x

/-- The unnormalized Markov trace on `TemperleyLieb ℂ (√3 : ℂ) m` pulled back from
`scalarTrace` along `cubicFixedHom m`. -/
noncomputable def cubicFixedTrace (m : ℕ) : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₗ[ℂ] ℂ :=
  ((Real.sqrt 3 : ℂ) ^ m) • (scalarTrace (cubicFactor (m - 1)) ∘ₗ
    (cubicFixed (m - 1)).subtype.toAlgHom.toLinearMap ∘ₗ
    (cubicFixedHom m).toAlgHom.toLinearMap)
theorem cubicFixedTrace_apply (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicFixedTrace m x = (Real.sqrt 3 : ℂ) ^ m *
      scalarTrace (cubicFactor (m - 1)) (cubicFixedHom m x) := by simp [cubicFixedTrace]
/-- **The cubic quantum torus scalar trace defines a Markov trace at `δ = √3`.** -/
theorem isMarkovTrace_cubicFixedTrace : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) cubicFixedTrace where
  map_one m := by simp [cubicFixedTrace_apply]
  map_mul_comm m x y := by
    rw [cubicFixedTrace_apply, cubicFixedTrace_apply, map_mul, map_mul, MulMemClass.coe_mul,
      MulMemClass.coe_mul, TwistedMonoidAlgebra.scalarTrace_mul_comm]
  map_strandIncl n x := by
    rw [cubicFixedTrace_apply, cubicFixedHom_strandIncl, coe_cubicFixedIncl, cubicFixedTrace_apply]
    change (Real.sqrt 3 : ℂ) ^ (n + 2) *
        scalarTrace (cubicFactor (n + 1)) (cubicIncl n (cubicFixedHom (n + 1) x).1) =
      (Real.sqrt 3 : ℂ) * ((Real.sqrt 3 : ℂ) ^ (n + 1) *
        scalarTrace (cubicFactor n) (cubicFixedHom (n + 1) x).1)
    rw [scalarTrace_cubicIncl, pow_succ', mul_assoc]
  map_strandIncl_mul_e_last n x := by
    have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    rw [cubicFixedTrace_apply, map_mul, MulMemClass.coe_mul, cubicFixedHom_strandIncl,
      coe_cubicFixedIncl, coe_cubicFixedHom_e, mul_smul_comm, map_smul, smul_eq_mul,
      cubicFixedTrace_apply]
    change (Real.sqrt 3 : ℂ) ^ (n + 2) * ((Real.sqrt 3 : ℂ) *
        scalarTrace (cubicFactor (n + 1))
          (cubicIncl n (cubicFixedHom (n + 1) x).1 * cubicProjection (n + 1) (Fin.last n))) =
      (Real.sqrt 3 : ℂ) ^ (n + 1) * scalarTrace (cubicFactor n) (cubicFixedHom (n + 1) x).1
    rw [scalarTrace_cubicIncl_mul_cubicProjection_last]
    linear_combination ((Real.sqrt 3 : ℂ) ^ (n + 1) * (3 : ℂ)⁻¹ *
      scalarTrace (cubicFactor n) (cubicFixedHom (n + 1) x).1) * hsqrt

namespace IsMarkovTrace
variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}
  (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr)
include htr
theorem eq_cubicFixedTrace : tr = cubicFixedTrace := htr.unique isMarkovTrace_cubicFixedTrace
/-- **The Markov trace at `δ = √3` as the cubic quantum torus scalar trace.** -/
theorem apply_eq_mul_scalarTrace_cubicFixedHom (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    tr m x = (Real.sqrt 3 : ℂ) ^ m * scalarTrace (cubicFactor (m - 1)) (cubicFixedHom m x) := by
  rw [htr.eq_cubicFixedTrace, cubicFixedTrace_apply]
/-- **Positivity of the Markov trace at `δ = √3`.** -/
theorem map_star_mul_self_nonneg_sqrt_three {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    0 ≤ tr m (star x * x) := by
  set y : CubicTorus (m - 1) := (cubicFixedHom m x).1
  have hz := TwistedMonoidAlgebra.scalarTrace_star_mul_self_nonneg (cubicFactor (m - 1)) y
  have hreal : scalarTrace (cubicFactor (m - 1)) (star y * y) =
      ((scalarTrace (cubicFactor (m - 1)) (star y * y)).re : ℂ) :=
    Complex.ext rfl (by simp [(Complex.nonneg_iff.mp hz).2])
  rw [htr.apply_eq_mul_scalarTrace_cubicFixedHom, map_mul, MulMemClass.coe_mul,
    cubicFixedHom_star, StarMemClass.coe_star]
  change 0 ≤ (Real.sqrt 3 : ℂ) ^ m * scalarTrace (cubicFactor (m - 1)) (star y * y)
  rw [hreal, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.zero_le_real]
  exact mul_nonneg (by positivity) (Complex.nonneg_iff.mp hz).1
theorem map_star_mul_self_eq_zero_iff_cubicFixedHom_eq_zero {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} : tr m (star x * x) = 0 ↔ cubicFixedHom m x = 0 := by
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  rw [htr.apply_eq_mul_scalarTrace_cubicFixedHom, map_mul, MulMemClass.coe_mul,
    cubicFixedHom_star, StarMemClass.coe_star, mul_eq_zero]
  simp [pow_ne_zero m hne]
/-- **The trace radical at `δ = √3` is the kernel of `cubicFixedHom`.** -/
theorem traceRadical_eq_ker_cubicFixedHom (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (cubicFixedHom m) := by
  have hne : (Real.sqrt 3 : ℂ) ^ m ≠ 0 :=
    pow_ne_zero m (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num)))
  let τ : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₗ[ℂ] ℂ := ((Real.sqrt 3 : ℂ) ^ m)⁻¹ • tr m
  have hτ : ∀ x y, τ (x * y) = τ (y * x) := fun x y ↦ by simp [τ, htr.map_mul_comm m x y]
  have hrad_eq : (tr m).traceRadical (htr.map_mul_comm m) = τ.traceRadical hτ :=
    Ideal.ext fun x ↦ by simp [LinearMap.mem_traceRadical, τ, hne]
  let f : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →⋆ₐ[ℂ] CubicTorus (m - 1) :=
    (cubicFixed (m - 1)).subtype.comp (cubicFixedHom m)
  have hf (a) : scalarTracePositiveFunctional (cubicFactor (m - 1)) (f a) = τ a := by
    simp only [TwistedMonoidAlgebra.scalarTracePositiveFunctional_apply, f, StarAlgHom.comp_apply,
      StarSubalgebra.coe_subtype, τ, LinearMap.smul_apply, smul_eq_mul,
      htr.apply_eq_mul_scalarTrace_cubicFixedHom]
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hrad_eq, ← show RingHom.ker f = RingHom.ker (cubicFixedHom m) from
    Ideal.ext fun x ↦ by simp [RingHom.mem_ker, f]]
  exact LinearMap.traceRadical_eq_ker_of_nullSubmodule_eq_bot τ hτ _
    (nullSubmodule_scalarTracePositiveFunctional (cubicFactor (m - 1))) f hf
theorem map_star_mul_self_eq_zero_iff_mem_traceRadical_sqrt_three {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} :
    tr m (star x * x) = 0 ↔ x ∈ (tr m).traceRadical (htr.map_mul_comm m) := by
  rw [htr.map_star_mul_self_eq_zero_iff_cubicFixedHom_eq_zero,
    htr.traceRadical_eq_ker_cubicFixedHom, RingHom.mem_ker]
/-- **The Jones quotient at `δ = √3` is isomorphic to `cubicFixed (m - 1)`.** -/
noncomputable def quotientCubicFixedEquiv (m : ℕ) :
    (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) ≃ₐ[ℂ]
      cubicFixed (m - 1) :=
  (Ideal.quotientEquivAlgOfEq ℂ ((htr.traceRadical_eq_ker_cubicFixedHom m).trans
    (Ideal.ext (I := RingHom.ker (cubicFixedHom m))
      (J := RingHom.ker (cubicFixedHom m).toAlgHom) fun _ ↦ Iff.rfl))).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := (cubicFixedHom m).toAlgHom)
      (cubicFixedHom_surjective m))
@[simp] theorem quotientCubicFixedEquiv_mk (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    htr.quotientCubicFixedEquiv m
        (Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x) =
      cubicFixedHom m x := by simp [quotientCubicFixedEquiv, Ideal.quotientEquivAlgOfEq_mk]
theorem isStar_traceRadical_sqrt_three (m : ℕ) :
    Ideal.IsStar ((tr m).traceRadical (htr.map_mul_comm m)) where
  star_mem {x} hx := by
    rw [htr.traceRadical_eq_ker_cubicFixedHom] at hx ⊢
    simpa [RingHom.mem_ker] using congrArg star (RingHom.mem_ker.mp hx)
@[simp] theorem quotientCubicFixedEquiv_star (m : ℕ)
    [Ideal.IsStar ((tr m).traceRadical (htr.map_mul_comm m))]
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) :
    htr.quotientCubicFixedEquiv m (star q) = star (htr.quotientCubicFixedEquiv m q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q; simp
theorem quotientCubicFixedEquiv_quotientStrandIncl (n : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1) ⧸
      (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientCubicFixedEquiv (n + 2) (htr.quotientStrandIncl n q) =
      cubicFixedIncl n (htr.quotientCubicFixedEquiv (n + 1) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [htr.quotientStrandIncl_mk, htr.quotientCubicFixedEquiv_mk,
    htr.quotientCubicFixedEquiv_mk, cubicFixedHom_strandIncl]
@[simp] theorem quotientCubicFixedEquiv_symm_cubicFixedHom (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (htr.quotientCubicFixedEquiv m).symm (cubicFixedHom m x) =
      Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x :=
  (htr.quotientCubicFixedEquiv m).injective (by simp)
theorem quotientCubicFixedEquiv_symm_cubicFixedIncl (n : ℕ) (y : cubicFixed n) :
    (htr.quotientCubicFixedEquiv (n + 2)).symm (cubicFixedIncl n y) =
      htr.quotientStrandIncl n ((htr.quotientCubicFixedEquiv (n + 1)).symm y) :=
  (htr.quotientCubicFixedEquiv (n + 2)).injective <| by
    rw [AlgEquiv.apply_symm_apply, htr.quotientCubicFixedEquiv_quotientStrandIncl,
      AlgEquiv.apply_symm_apply]
theorem quotientTrace_eq_mul_scalarTrace_quotientCubicFixedEquiv (m : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) :
    (tr m).quotientTrace (htr.map_mul_comm m) q = (Real.sqrt 3 : ℂ) ^ m *
      scalarTrace (cubicFactor (m - 1)) (htr.quotientCubicFixedEquiv m q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [htr.apply_eq_mul_scalarTrace_cubicFixedHom]
@[simp] theorem quotientTrace_quotientCubicFixedEquiv_symm (m : ℕ) (x : cubicFixed (m - 1)) :
    (tr m).quotientTrace (htr.map_mul_comm m) ((htr.quotientCubicFixedEquiv m).symm x) =
      (Real.sqrt 3 : ℂ) ^ m * scalarTrace (cubicFactor (m - 1)) x := by
  simp [htr.quotientTrace_eq_mul_scalarTrace_quotientCubicFixedEquiv]
@[simp] theorem finrank_quotient_traceRadical_sqrt_three (m : ℕ) :
    Module.finrank ℂ
        (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) =
      (3 ^ (m - 1) + 1) / 2 := by
  rw [(htr.quotientCubicFixedEquiv m).toLinearEquiv.finrank_eq, finrank_cubicFixed]
end IsMarkovTrace

theorem markovTrace_eq_mul_scalarTrace_cubicFixedHom (q : ℂˣ)
    (hq : (Real.sqrt 3 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    markovTrace q hq x = (Real.sqrt 3 : ℂ) ^ m *
      scalarTrace (cubicFactor (m - 1)) (cubicFixedHom m x) :=
  (isMarkovTrace_markovTrace q hq).apply_eq_mul_scalarTrace_cubicFixedHom m x
/-- **The inversion-fixed cubic quantum torus model of `TemperleyLieb ℂ (√3 : ℂ) m`.** -/
theorem exists_cubicFixedModel
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    ∃ F : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1),
      Function.Surjective F ∧
      (∀ j : Fin (m - 1), (F (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
        (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m,
        tr m x = (Real.sqrt 3 : ℂ) ^ m * scalarTrace (cubicFactor (m - 1)) (F x)) ∧
      RingHom.ker F = (tr m).traceRadical (htr.map_mul_comm m) :=
  ⟨cubicFixedHom m, cubicFixedHom_surjective m, coe_cubicFixedHom_e m,
    htr.apply_eq_mul_scalarTrace_cubicFixedHom m, (htr.traceRadical_eq_ker_cubicFixedHom m).symm⟩
/-- At `δ = √3`, `cubicFixedHom 5` maps `jonesWenzl (√3 : ℂ) 5` to `0`. -/
@[simp] theorem cubicFixedHom_jonesWenzl_five :
    cubicFixedHom 5 (jonesWenzl (Real.sqrt 3 : ℂ) 5) = 0 := by
  have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hq3 : qInt ℂ (Real.sqrt 3 : ℂ) 3 = 2 := by
    rw [qInt_add_two _ 1, qInt_two, qInt_one, hsqrt]; norm_num
  have hq4 : qInt ℂ (Real.sqrt 3 : ℂ) 4 = (Real.sqrt 3 : ℂ) := by
    rw [qInt_add_two _ 2, hq3, qInt_two]; ring
  have hq5 : qInt ℂ (Real.sqrt 3 : ℂ) 5 = 1 := by
    rw [qInt_add_two _ 3, hq4, hq3, hsqrt]; norm_num
  have hunits : ∀ k ∈ Finset.Icc 1 5, IsUnit (qInt ℂ (Real.sqrt 3 : ℂ) k) := fun k hk ↦ by
    obtain ⟨hk1, hk5⟩ := Finset.mem_Icc.mp hk
    interval_cases k <;> simp [qInt_two, hq3, hq4, hq5]
  rw [← RingHom.mem_ker, ← isMarkovTrace_cubicFixedTrace.traceRadical_eq_ker_cubicFixedHom 5,
    isMarkovTrace_cubicFixedTrace.jonesWenzl_mem_traceRadical_iff hunits, qInt_add_two _ 4,
    hq5, hq4]; ring

end TauCeti.TemperleyLieb
