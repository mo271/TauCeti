/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.FormallyEtale
public import TauCeti.RingTheory.Kaehler.Trace.Basic

/-!
# The trace of differentials along formally unramified and étale extensions

Let `k → R → B` be a tower of commutative rings with `B` finite and free over `R`, and let
`D : R → M` be a `k`-derivation into an `R`-module. Evaluating the matrix trace form
`Derivation.traceDerivForm D` against the identity matrix gives `D` applied to the matrix trace, so
already without any unramifiedness hypothesis the differential trace `Derivation.traceLin D`
satisfies:

* **Commutation with `d`:** `traceLin D (d a) = D (Tr_{B/R}(a))`
  (`Derivation.traceLin_D_eq`).
* **Projection formula:** `traceLin D (b • map η) = Tr_{B/R}(b) • D.liftKaehlerDifferential η`
  for `b ∈ B` and `η ∈ Ω[R⁄k]` (`Derivation.traceLin_smul_map`).

When `B` is formally unramified over `R` and `D : R → R` extends to a `k`-derivation `D' : B → B`,
the trace derivation `a ↦ (c ↦ traceDeriv D a c)` and `a ↦ (c ↦ Tr_{B/R}(c * D' a))` agree on `R`,
hence agree on all of `B` by `Derivation.eq_of_formallyUnramified`. Consequently:

* `traceDeriv D a c = Tr_{B/R}(c * D' a)` (`Derivation.traceDeriv_eq_trace_mul`);
* **`D` and `D'` commute with `Algebra.trace R B`:** `D (Tr_{B/R}(a)) = Tr_{B/R}(D' a)`
  (`Derivation.map_trace_of_formallyUnramified`);
* `traceLin D ω = Tr_{B/R}(D'.liftKaehlerDifferential ω)`
  (`Derivation.traceLin_eq_trace_liftKaehlerDifferential`).

When `B` is formally étale over `R`, these apply to the canonical extension
`Derivation.extendOfFormallyEtale`, and `Derivation.traceLin` identifies under
`B ⊗[R] Ω[R⁄k] ≃ Ω[B⁄k]` (`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`) with
`Algebra.trace R B` acting on the first tensor factor.

## References

* E. Kunz, *Kähler Differentials*, Vieweg (1986), §16, for the differential trace of a finite free
  extension and its projection and étale base-change formulas.
-/

public section

open Matrix Algebra TensorProduct TauCeti.Algebra

namespace Derivation

section FiniteFree

variable {k R B M : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module k M] (D : Derivation k R M)

/-- Evaluating `traceDerivForm D` on the identity matrix on the left applies `D` to the matrix
trace. -/
@[simp]
theorem traceDerivForm_one_left {m : Type*} [Fintype m] [DecidableEq m] (Y : Matrix m m R) :
    traceDerivForm D (1 : Matrix m m R) Y = D Y.trace := by
  simp only [traceDerivForm_def, Matrix.one_apply, Matrix.trace, Matrix.diag, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [ite_eq_right (Ne.symm hj), zero_smul])
    (fun hi ↦ (hi (Finset.mem_univ i)).elim), ite_eq_left rfl, one_smul]

/-- In any basis `b` of `B` over `R`, evaluating the trace derivation at `1` gives `D` of the
algebra trace. -/
theorem traceDerivOfBasis_one_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R B) (a : B) :
    traceDerivOfBasis D b a 1 = D (Algebra.trace R B a) := by
  rw [traceDerivOfBasis_def, map_one, traceDerivForm_one_left, Algebra.trace_eq_matrix_trace b]

variable [Module.Free R B] [Module.Finite R B]

/-- Evaluating `traceDeriv D a` at `1` gives `D` applied to `Tr_{B/R}(a)`. -/
theorem traceDeriv_one_right (a : B) :
    traceDeriv D a 1 = D (Algebra.trace R B a) := by
  classical
  rw [traceDeriv_def]
  exact traceDerivOfBasis_one_right D (Module.Free.chooseBasis R B) a

variable [Algebra k B] [IsScalarTower k R B] [IsScalarTower k R M]

/-- **Differential trace commutes with `d`.** For any finite free extension `B/R`, the differential
trace of `d a` is `D (Tr_{B/R}(a))`. -/
theorem traceLin_D_eq (a : B) :
    traceLin D (KaehlerDifferential.D k B a) = D (Algebra.trace R B a) := by
  rw [traceLin_D, traceDeriv_one_right]

/-- **Projection formula for the differential trace.** Pulling back `η ∈ Ω[R⁄k]` to `Ω[B⁄k]`,
multiplying by `b ∈ B`, and taking `traceLin D` scales `D.liftKaehlerDifferential η` by
`Tr_{B/R}(b)`. -/
@[simp]
theorem traceLin_smul_map (b : B) (η : Ω[R⁄k]) :
    traceLin D (b • KaehlerDifferential.map k k R B η) =
      Algebra.trace R B b • D.liftKaehlerDifferential η := by
  have hη : η ∈ Submodule.span R (Set.range (KaehlerDifferential.D k R)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hη using Submodule.span_induction with
  | mem _ hx =>
    rcases hx with ⟨r, rfl⟩
    simp [traceDeriv_algebraMap]
  | zero => simp
  | add _ _ _ _ hx hy => simp [smul_add, hx, hy]
  | smul r x _ hx =>
    rw [LinearMap.map_smul, smul_comm b r, LinearMap.map_smul, hx, LinearMap.map_smul, smul_comm]

/-- For `D = d : R → Ω[R⁄k]`, the differential trace satisfies `Tr(b · map η) = Tr(b) • η`. -/
theorem traceLin_D_smul_map (b : B) (η : Ω[R⁄k]) :
    traceLin (KaehlerDifferential.D k R) (b • KaehlerDifferential.map k k R B η) =
      Algebra.trace R B b • η := by
  rw [traceLin_smul_map, Derivation.liftKaehlerDifferential_D, LinearMap.id_apply]

end FiniteFree

section FormallyUnramified

variable {k R B : Type*} [CommRing k] [CommRing R] [CommRing B] [Algebra R B] [Algebra k B]

/-- The `k`-derivation `B → Hom_R(B, R)` sending `a` to `c ↦ Tr_{B/R}(c * D' a)`. -/
private noncomputable def traceMulDerivation (D' : Derivation k B B) :
    Derivation k B (PrecompLinearMap R B R) :=
  Derivation.mk'
    { toFun a := PrecompLinearMap.ofLinearMap (Algebra.trace R B ∘ₗ LinearMap.mulRight R (D' a))
      map_add' a b := PrecompLinearMap.ext fun c ↦ by simp [mul_add]
      map_smul' x a := PrecompLinearMap.ext fun c ↦ by
        simp only [PrecompLinearMap.smul_apply, PrecompLinearMap.ofLinearMap_apply,
          LinearMap.comp_apply, LinearMap.mulRight_apply, RingHom.id_apply, Derivation.map_smul,
          mul_smul_comm, smul_mul_assoc] }
    fun a b ↦ PrecompLinearMap.ext fun c ↦ by
      simp only [PrecompLinearMap.add_apply, PrecompLinearMap.smul_apply, LinearMap.coe_mk,
        AddHom.coe_mk, PrecompLinearMap.ofLinearMap_apply, LinearMap.comp_apply,
        LinearMap.mulRight_apply, Derivation.leibniz, smul_eq_mul, ← map_add]
      exact congrArg (Algebra.trace R B) (by ring)

@[simp]
private theorem traceMulDerivation_apply (D' : Derivation k B B) (a c : B) :
    traceMulDerivation (R := R) D' a c = Algebra.trace R B (c * D' a) := by
  simp [traceMulDerivation, Derivation.mk']

variable [Algebra k R] [IsScalarTower k R B]
  [Module.Free R B] [Module.Finite R B] [Algebra.FormallyUnramified R B]

/-- Over a finite free formally unramified extension `B/R`, if `D' : B → B` extends `D : R → R`,
then `traceDerivation D` is `a ↦ (c ↦ Tr_{B/R}(c * D' a))`. -/
private theorem traceDerivation_eq_of_formallyUnramified (D : Derivation k R R)
    (D' : Derivation k B B)
    (hD' : ∀ r : R, D' (algebraMap R B r) = algebraMap R B (D r)) :
    traceDerivation (B := B) D = traceMulDerivation (R := R) D' :=
  eq_of_formallyUnramified (S := R) fun r ↦ PrecompLinearMap.ext fun c ↦ by
    rw [traceDerivation_apply, traceDeriv_algebraMap, traceMulDerivation_apply, hD',
      mul_comm c, ← Algebra.smul_def, _root_.map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

/-- Over a finite free formally unramified extension `B/R`, `traceDeriv D a c = Tr_{B/R}(c * D' a)`
for every derivation `D'` of `B` extending `D`. -/
theorem traceDeriv_eq_trace_mul (D : Derivation k R R) (D' : Derivation k B B)
    (hD' : ∀ r : R, D' (algebraMap R B r) = algebraMap R B (D r)) (a c : B) :
    traceDeriv D a c = Algebra.trace R B (c * D' a) := by
  have h := DFunLike.congr_fun (traceDerivation_eq_of_formallyUnramified D D' hD') a
  simpa using congrArg (fun φ : PrecompLinearMap R B R ↦ φ c) h

/-- **Derivations commute with trace on formally unramified finite free extensions.** If `B/R` is
finite free and formally unramified and `D' : B → B` extends `D : R → R`, then
`D (Tr_{B/R}(a)) = Tr_{B/R}(D' a)`. -/
theorem map_trace_of_formallyUnramified (D : Derivation k R R) (D' : Derivation k B B)
    (hD' : ∀ r : R, D' (algebraMap R B r) = algebraMap R B (D r)) (a : B) :
    D (Algebra.trace R B a) = Algebra.trace R B (D' a) := by
  rw [← traceDeriv_one_right D a, traceDeriv_eq_trace_mul D D' hD', one_mul]

/-- Over a finite free formally unramified extension `B/R`, the Kähler lift of `traceDerivation D`
sends `(ω, c)` to `Tr_{B/R}(c * D'.liftKaehlerDifferential ω)`. -/
theorem liftKaehlerDifferential_traceDerivation_eq_trace_mul (D : Derivation k R R)
    (D' : Derivation k B B) (hD' : ∀ r : R, D' (algebraMap R B r) = algebraMap R B (D r))
    (ω : Ω[B⁄k]) (c : B) :
    (traceDerivation (B := B) D).liftKaehlerDifferential ω c =
      Algebra.trace R B (c * D'.liftKaehlerDifferential ω) := by
  let Φ : Ω[B⁄k] →ₗ[B] PrecompLinearMap R B R :=
    { toFun η := PrecompLinearMap.ofLinearMap
        (Algebra.trace R B ∘ₗ LinearMap.mulRight R (D'.liftKaehlerDifferential η))
      map_add' η₁ η₂ := PrecompLinearMap.ext fun x ↦ by simp [mul_add]
      map_smul' b η := PrecompLinearMap.ext fun x ↦ by
        simp only [PrecompLinearMap.smul_apply, PrecompLinearMap.ofLinearMap_apply,
          LinearMap.comp_apply, LinearMap.mulRight_apply, _root_.map_smul, smul_eq_mul,
          RingHom.id_apply]
        exact congrArg (Algebra.trace R B) (by ring) }
  have hΦ : (traceDerivation (B := B) D).liftKaehlerDifferential = Φ :=
    LinearMap.ext_on (KaehlerDifferential.span_range_derivation k B) <| by
      rintro _ ⟨a, rfl⟩
      exact PrecompLinearMap.ext fun x ↦ by
        simp [Φ, traceDeriv_eq_trace_mul D D' hD']
  simpa [Φ] using congrArg (fun φ : PrecompLinearMap R B R ↦ φ c) (DFunLike.congr_fun hΦ ω)

/-- Over a finite free formally unramified extension `B/R`, `traceLin D` is `Algebra.trace R B`
composed with the Kähler lift of `D'`. -/
theorem traceLin_eq_trace_liftKaehlerDifferential (D : Derivation k R R) (D' : Derivation k B B)
    (hD' : ∀ r : R, D' (algebraMap R B r) = algebraMap R B (D r)) (ω : Ω[B⁄k]) :
    traceLin D ω = Algebra.trace R B (D'.liftKaehlerDifferential ω) := by
  rw [traceLin_apply, liftKaehlerDifferential_traceDerivation_eq_trace_mul D D' hD', one_mul]

end FormallyUnramified

section FormallyEtale

variable {k R B : Type*} [CommRing k] [CommRing R] [CommRing B]
  [Algebra k R] [Algebra R B] [Algebra k B] [IsScalarTower k R B]
  [Module.Free R B] [Module.Finite R B] [Algebra.FormallyEtale R B]

/-- **Derivations commute with trace along finite free formally étale extensions.** The étale
extension of `D : R → R` to `B` satisfies `D (Tr_{B/R}(a)) = Tr_{B/R}(D_B a)`. -/
theorem map_trace_eq_trace_extendOfFormallyEtale (D : Derivation k R R) (a : B) :
    D (Algebra.trace R B a) =
      Algebra.trace R B (((Algebra.linearMap R B).compDer D).extendOfFormallyEtale B a) :=
  map_trace_of_formallyUnramified D _ (fun r ↦ by simp) a

/-- Along a finite free formally étale extension `B/R`, `traceLin D` is `Algebra.trace R B`
composed with the Kähler lift of the étale extension of `D`. -/
theorem traceLin_eq_trace_liftKaehlerDifferential_extendOfFormallyEtale
    (D : Derivation k R R) (ω : Ω[B⁄k]) :
    traceLin D ω =
      Algebra.trace R B
        ((((Algebra.linearMap R B).compDer D).extendOfFormallyEtale B).liftKaehlerDifferential
          ω) :=
  traceLin_eq_trace_liftKaehlerDifferential D _ (fun r ↦ by simp) ω

/-- **Differential trace under étale base change.** Under `B ⊗[R] Ω[R⁄k] ≃ Ω[B⁄k]`, `traceLin D`
acts as `Algebra.trace R B` on the first tensor factor and `D.liftKaehlerDifferential` on the
second; in particular, for `D = d : R → Ω[R⁄k]`, it acts as `Algebra.trace R B` on the first
factor. -/
theorem traceLin_D_comp_tensorKaehlerEquivOfFormallyEtale :
    traceLin (KaehlerDifferential.D k R) ∘ₗ
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R B).toLinearMap.restrictScalars
          R =
      (TensorProduct.lid R Ω[R⁄k]).toLinearMap ∘ₗ (Algebra.trace R B).rTensor Ω[R⁄k] := by
  ext b r
  simp [traceDeriv_algebraMap]

end FormallyEtale

end Derivation
