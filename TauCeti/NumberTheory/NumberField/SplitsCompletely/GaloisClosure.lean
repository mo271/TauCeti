/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.RingTheory.Unramified.Locus
public import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.NumberTheory.RamificationInertia.Unramified
import TauCeti.NumberTheory.RamificationInertia.Splitting
import TauCeti.RingTheory.Unramified.AlgEquiv

/-!
# Complete splitting and unramifiedness in composita and Galois closures

Let `M / K` be a finite Galois extension of number fields with group `G`, let `E` be an
intermediate field, and let `𝔭` be a prime of `𝓞 K`. Say that `𝔭` *splits completely* in `E`
when it has `[E : K]` primes above it in `𝓞 E`. This file proves

* `𝔭` splits completely in `E` exactly when every decomposition group `D(Q) ≤ G`, for `Q` a prime
  of `𝓞 M` above `𝔭`, fixes `E` pointwise;
* `𝔭` is unramified in `E` exactly when every inertia group `I(Q)` fixes `E` pointwise.

Both conditions are about the fixing subgroup of `E`, and the Galois correspondence turns a join
of fields into a meet of fixing subgroups. So both properties pass to composita: `𝔭` splits
completely (or is unramified) in `E₁ ⊔ E₂` exactly when it does in `E₁` and in `E₂`, and likewise
for an arbitrary join. Conjugating `E` by `σ ∈ G` conjugates its fixing subgroup, while the
decomposition and inertia groups over `𝔭` are permuted among themselves by the same conjugation;
so neither property changes. As the normal closure of `E` in `M` is the join of the conjugates of
`E`, the prime `𝔭` splits completely (or is unramified) in `E` exactly when it does in the normal
closure. When `M` is itself the normal closure of `E`, this compares `E` with `M` directly.

For unramifiedness, embedding `normalClosure K L M` into a finite Galois extension of `K` removes
both the normality and finiteness hypotheses on the ambient `K`-field `M`: if an ideal of `𝓞 K`
is unramified in a number field `L`, it remains unramified in `normalClosure K L M`
(`Ideal.isUnramifiedIn_normalClosure`), and consequently formal unramifiedness of `𝓞 L` over `𝓞 K`
passes to `𝓞 (normalClosure K L M)` (`Algebra.FormallyUnramified.ringOfIntegers_normalClosure`).

The decomposition-group criterion rests on the local degree formula
`e(Q ∩ E / 𝔭) f(Q ∩ E / 𝔭) = [D(Q) : D(Q) ∩ Gal(M/E)]`, together with the non-Galois count
criterion (`[E : K]` primes above `𝔭` exactly when `e = f = 1` at each). The inertia-group
criterion rests likewise on `e(Q ∩ E / 𝔭) = [I(Q) : I(Q) ∩ Gal(M/E)]`.

## Main results

* `Ideal.ncard_primesOver_eq_finrank_iff_forall_stabilizer_le`: `𝔭` splits completely in `E`
  iff every decomposition group above `𝔭` lies in `Gal(M/E)`.
* `Ideal.ncard_primesOver_eq_finrank_iff_forall_stabilizer_eq_bot`: `𝔭` splits completely in `M`
  iff every decomposition group above `𝔭` is trivial.
* `Ideal.ncard_primesOver_sup_eq_finrank_iff`, `Ideal.ncard_primesOver_iSup_eq_finrank_iff`:
  complete splitting in a compositum.
* `Ideal.ncard_primesOver_map_eq_finrank_iff`: complete splitting in a conjugate field.
* `Ideal.ncard_primesOver_normalClosure_eq_finrank_iff`: `𝔭` splits completely in `E` iff it
  splits completely in the normal closure of `E`.
* `Ideal.ncard_primesOver_eq_finrank_iff_of_normalClosure_eq_top`: the same, when `M` is the
  normal closure of `E`.
* `Ideal.isUnramifiedIn_iff_forall_inertia_le`: `𝔭` is unramified in `E` iff every inertia group
  above `𝔭` lies in `Gal(M/E)`.
* `Ideal.isUnramifiedIn_sup_iff`, `Ideal.isUnramifiedIn_iSup_iff`,
  `Ideal.isUnramifiedIn_map_iff`, `Ideal.isUnramifiedIn_normalClosure`,
  `Ideal.isUnramifiedIn_normalClosure_iff`,
  `Algebra.FormallyUnramified.ringOfIntegers_normalClosure`: unramifiedness in composita,
  conjugate fields, and normal closures inside arbitrary ambient extensions.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9, Exercise 4.
-/

public section

open IntermediateField Module

open scoped NumberField Pointwise

namespace Ideal

section GaloisAmbient

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

/-! ### Complete splitting -/

/-- **Complete splitting through decomposition groups.** For `M / K` Galois and `E` an
intermediate field, a prime `p` of `𝓞 K` has `[E : K]` primes above it in `𝓞 E` exactly when the
decomposition group of every prime of `𝓞 M` above `p` fixes `E` pointwise. -/
theorem ncard_primesOver_eq_finrank_iff_forall_stabilizer_le (p : Ideal (𝓞 K)) [p.IsPrime]
    (E : IntermediateField K M) :
    (p.primesOver (𝓞 E)).ncard = finrank K E ↔
      ∀ Q ∈ p.primesOver (𝓞 M), MulAction.stabilizer (M ≃ₐ[K] M) Q ≤ E.fixingSubgroup := by
  obtain ⟨H, rfl⟩ : ∃ H, fixedField H = E := ⟨_, IsGalois.fixedField_fixingSubgroup E⟩
  rw [fixingSubgroup_fixedField, IsFractionRing.finrank_eq (𝓞 K) K (𝓞 (fixedField H)),
    Ideal.ncard_primesOver_eq_finrank_iff_forall_ramificationIdx_eq_one_and_inertiaDeg_eq_one]
  -- at each prime, `e = f = 1` says the index `[D(Q) : D(Q) ∩ H]` is one
  simp_rw [← mul_eq_one, ← Subgroup.relIndex_eq_one]
  refine ⟨fun h Q hQ ↦ ?_, fun h P hP ↦ ?_⟩
  · have := hQ.1
    rw [← ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex]
    have : Q.under (𝓞 ↥(fixedField H)) ∈ p.primesOver (𝓞 ↥(fixedField H)) := by
      exact ⟨inferInstance, ⟨by rw [under_under]; exact hQ.2.over⟩⟩
    exact h _ this
  · have := hP.1
    have := hP.2
    obtain ⟨⟨Q, hQprime, hQover⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 M)))
    have : Q.IsPrime := hQprime
    have : Q.LiesOver P := hQover
    rw [← (over_def Q P).symm]
    rw [ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex]
    exact h Q ⟨inferInstance, LiesOver.trans Q P p⟩

/-- **Complete splitting in a Galois extension.** For `M / K` Galois, a prime `p` of `𝓞 K` has
`[M : K]` primes above it exactly when the decomposition group of every prime above it is
trivial. -/
theorem ncard_primesOver_eq_finrank_iff_forall_stabilizer_eq_bot (p : Ideal (𝓞 K))
    [p.IsPrime] :
    (p.primesOver (𝓞 M)).ncard = finrank K M ↔
      ∀ Q ∈ p.primesOver (𝓞 M), MulAction.stabilizer (M ≃ₐ[K] M) Q = ⊥ := by
  rw [← IsGaloisGroup.card_eq_finrank (M ≃ₐ[K] M) K M,
    ncard_primesOver_eq_natCard_iff_forall_stabilizer_eq_bot]

/-- **Complete splitting in a compositum.** A prime `p` of `𝓞 K` splits completely in `E₁ ⊔ E₂`
exactly when it splits completely in `E₁` and in `E₂`. -/
theorem ncard_primesOver_sup_eq_finrank_iff (p : Ideal (𝓞 K)) [p.IsPrime]
    (E₁ E₂ : IntermediateField K M) :
    (p.primesOver (𝓞 ↥(E₁ ⊔ E₂))).ncard = finrank K ↥(E₁ ⊔ E₂) ↔
      (p.primesOver (𝓞 E₁)).ncard = finrank K E₁ ∧
        (p.primesOver (𝓞 E₂)).ncard = finrank K E₂ := by
  simp only [ncard_primesOver_eq_finrank_iff_forall_stabilizer_le, fixingSubgroup_sup,
    le_inf_iff, ← forall_and]

/-- **Complete splitting in an arbitrary compositum.** A prime `p` of `𝓞 K` splits completely in
`⨆ i, E i` exactly when it splits completely in every `E i`. -/
theorem ncard_primesOver_iSup_eq_finrank_iff (p : Ideal (𝓞 K)) [p.IsPrime]
    {ι : Sort*} (E : ι → IntermediateField K M) :
    (p.primesOver (𝓞 ↥(⨆ i, E i))).ncard = finrank K ↥(⨆ i, E i) ↔
      ∀ i, (p.primesOver (𝓞 (E i))).ncard = finrank K (E i) := by
  simp only [ncard_primesOver_eq_finrank_iff_forall_stabilizer_le, fixingSubgroup_iSup,
    le_iInf_iff]
  exact ⟨fun h i Q hQ ↦ h Q hQ i, fun h Q hQ i ↦ h i Q hQ⟩

/-- **Complete splitting in a conjugate field.** A prime `p` of `𝓞 K` splits completely in
`σ E` exactly when it splits completely in `E`. -/
theorem ncard_primesOver_map_eq_finrank_iff (p : Ideal (𝓞 K)) [p.IsPrime]
    (E : IntermediateField K M) (σ : M ≃ₐ[K] M) :
    (p.primesOver (𝓞 ↥(E.map (σ : M →ₐ[K] M)))).ncard = finrank K ↥(E.map (σ : M →ₐ[K] M)) ↔
      (p.primesOver (𝓞 E)).ncard = finrank K E := by
  obtain ⟨H, rfl⟩ : ∃ H, fixedField H = E := ⟨_, IsGalois.fixedField_fixingSubgroup E⟩
  rw [← H.fixedField_map_conj σ, ncard_primesOver_eq_finrank_iff_forall_stabilizer_le,
    ncard_primesOver_eq_finrank_iff_forall_stabilizer_le, fixingSubgroup_fixedField,
    fixingSubgroup_fixedField]
  -- `D(σ • Q) = σ D(Q) σ⁻¹`, and `σ` permutes the primes above `p`
  refine ⟨fun h Q hQ ↦ ?_, fun h Q hQ ↦ ?_⟩
  · have hσQ : σ • Q ∈ p.primesOver (𝓞 M) := by
      have := hQ.1
      have := hQ.2
      exact ⟨inferInstance, inferInstance⟩
    have := h _ hσQ
    rwa [MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
      Subgroup.map_le_map_iff_of_injective (MulAut.conj σ).injective] at this
  · rw [← smul_inv_smul σ Q, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    have hσQ : σ⁻¹ • Q ∈ p.primesOver (𝓞 M) := by
      have := hQ.1
      have := hQ.2
      exact ⟨inferInstance, inferInstance⟩
    exact Subgroup.map_mono (h _ hσQ)

/-- **Complete splitting in the normal closure.** A prime `p` of `𝓞 K` splits completely in an
intermediate field `E` of `M / K` exactly when it splits completely in the normal closure of `E`
in `M`. -/
theorem ncard_primesOver_normalClosure_eq_finrank_iff (p : Ideal (𝓞 K)) [p.IsPrime]
    (E : IntermediateField K M) :
    (p.primesOver (𝓞 (normalClosure K E M))).ncard = finrank K (normalClosure K E M) ↔
      (p.primesOver (𝓞 E)).ncard = finrank K E := by
  rw [normalClosure_def'' E, ncard_primesOver_iSup_eq_finrank_iff]
  simp only [ncard_primesOver_map_eq_finrank_iff, forall_const]

/-- **Complete splitting in a field and in its Galois closure.** If `M` is the normal closure of
the intermediate field `E`, a prime `p` of `𝓞 K` splits completely in `E` exactly when it splits
completely in `M`. -/
theorem ncard_primesOver_eq_finrank_iff_of_normalClosure_eq_top (p : Ideal (𝓞 K)) [p.IsPrime]
    {E : IntermediateField K M} (hE : normalClosure K E M = ⊤) :
    (p.primesOver (𝓞 E)).ncard = finrank K E ↔
      (p.primesOver (𝓞 M)).ncard = finrank K M := by
  rw [← ncard_primesOver_normalClosure_eq_finrank_iff,
    ncard_primesOver_eq_finrank_iff_forall_stabilizer_le, hE, fixingSubgroup_top,
    ncard_primesOver_eq_finrank_iff_forall_stabilizer_eq_bot]
  simp only [le_bot_iff]

/-! ### Unramifiedness -/

/-- **Unramifiedness through inertia groups.** For `M / K` Galois and `E` an intermediate field,
an ideal `p` of `𝓞 K` is unramified in `E` exactly when the inertia group of every prime of `𝓞 M`
above `p` fixes `E` pointwise. -/
theorem isUnramifiedIn_iff_forall_inertia_le (p : Ideal (𝓞 K)) (E : IntermediateField K M) :
    Algebra.IsUnramifiedIn (𝓞 E) p ↔
      ∀ Q ∈ p.primesOver (𝓞 M), Q.inertia (M ≃ₐ[K] M) ≤ E.fixingSubgroup := by
  obtain ⟨H, rfl⟩ : ∃ H, fixedField H = E := ⟨_, IsGalois.fixedField_fixingSubgroup E⟩
  rw [fixingSubgroup_fixedField, Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  -- at each prime, `e = 1` says the index `[I(Q) : I(Q) ∩ H]` is one
  simp_rw [← Subgroup.relIndex_eq_one]
  refine ⟨fun h Q hQ ↦ ?_, fun h P _ hP ↦ ?_⟩
  · have := hQ.1
    rw [← ramificationIdx_under_fixedField_eq_relIndex]
    have : Q.under (𝓞 ↥(fixedField H)) ∈ p.primesOver (𝓞 ↥(fixedField H)) := by
      exact ⟨inferInstance, ⟨by rw [under_under]; exact hQ.2.over⟩⟩
    exact h _ this.2
  · have : P.IsPrime := inferInstance
    have : P.LiesOver p := hP
    obtain ⟨⟨Q, hQprime, hQover⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 M)))
    have : Q.IsPrime := hQprime
    have : Q.LiesOver P := hQover
    rw [← (over_def Q P).symm]
    rw [ramificationIdx_under_fixedField_eq_relIndex]
    exact h Q ⟨inferInstance, LiesOver.trans Q P p⟩

/-- **Unramifiedness in a compositum.** An ideal `p` of `𝓞 K` is unramified in `E₁ ⊔ E₂` exactly
when it is unramified in `E₁` and in `E₂`. -/
theorem isUnramifiedIn_sup_iff (p : Ideal (𝓞 K)) (E₁ E₂ : IntermediateField K M) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E₁ ⊔ E₂)) p ↔
      Algebra.IsUnramifiedIn (𝓞 E₁) p ∧ Algebra.IsUnramifiedIn (𝓞 E₂) p := by
  simp only [isUnramifiedIn_iff_forall_inertia_le, fixingSubgroup_sup, le_inf_iff, ← forall_and]

/-- **Unramifiedness in an arbitrary compositum.** An ideal `p` of `𝓞 K` is unramified in
`⨆ i, E i` exactly when it is unramified in every `E i`. -/
theorem isUnramifiedIn_iSup_iff (p : Ideal (𝓞 K)) {ι : Sort*} (E : ι → IntermediateField K M) :
    Algebra.IsUnramifiedIn (𝓞 ↥(⨆ i, E i)) p ↔ ∀ i, Algebra.IsUnramifiedIn (𝓞 (E i)) p := by
  simp only [isUnramifiedIn_iff_forall_inertia_le, fixingSubgroup_iSup, le_iInf_iff]
  exact ⟨fun h i Q hQ ↦ h Q hQ i, fun h Q hQ i ↦ h i Q hQ⟩

/-- **Unramifiedness in a conjugate field.** An ideal `p` of `𝓞 K` is unramified in `σ E` exactly
when it is unramified in `E`. -/
theorem isUnramifiedIn_map_iff (p : Ideal (𝓞 K)) (E : IntermediateField K M) (σ : M ≃ₐ[K] M) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E.map (σ : M →ₐ[K] M))) p ↔ Algebra.IsUnramifiedIn (𝓞 E) p := by
  obtain ⟨H, rfl⟩ : ∃ H, fixedField H = E := ⟨_, IsGalois.fixedField_fixingSubgroup E⟩
  rw [← H.fixedField_map_conj σ, isUnramifiedIn_iff_forall_inertia_le,
    isUnramifiedIn_iff_forall_inertia_le, fixingSubgroup_fixedField, fixingSubgroup_fixedField]
  -- `I(σ • Q) = σ I(Q) σ⁻¹`, and `σ` permutes the primes above `p`
  refine ⟨fun h Q hQ ↦ ?_, fun h Q hQ ↦ ?_⟩
  · have hσQ : σ • Q ∈ p.primesOver (𝓞 M) := by
      have := hQ.1
      have := hQ.2
      exact ⟨inferInstance, inferInstance⟩
    have := h _ hσQ
    rwa [Ideal.inertia_smul,
      Subgroup.map_le_map_iff_of_injective (MulAut.conj σ).injective] at this
  · rw [← smul_inv_smul σ Q, Ideal.inertia_smul]
    have hσQ : σ⁻¹ • Q ∈ p.primesOver (𝓞 M) := by
      have := hQ.1
      have := hQ.2
      exact ⟨inferInstance, inferInstance⟩
    exact Subgroup.map_mono (h _ hσQ)

end GaloisAmbient

section AmbientNormalClosure

/-- The image of a field extension under a `K`-algebra homomorphism is unramified above an ideal
`p` of `𝓞 K` if and only if the source extension is. -/
theorem _root_.AlgHom.isUnramifiedIn_fieldRange_iff {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] (f : L →ₐ[K] M) (p : Ideal (𝓞 K)) :
    Algebra.IsUnramifiedIn (𝓞 f.fieldRange) p ↔ Algebra.IsUnramifiedIn (𝓞 L) p :=
  (NumberField.RingOfIntegers.mapAlgEquiv f.equivFieldRange.symm).isUnramifiedIn_iff p

/-- **Unramifiedness in the normal closure.** Taking the normal closure of a finite extension
`L / K` of a number field `K` inside an arbitrary ambient `K`-field `M` preserves unramifiedness of
any ideal `p` of `𝓞 K`. The ambient field `M` need not be finite, normal, or an `L`-algebra. -/
theorem isUnramifiedIn_normalClosure {K L : Type*} [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] (p : Ideal (𝓞 K))
    (M : Type*) [Field M] [Algebra K M] (h : Algebra.IsUnramifiedIn (𝓞 L) p) :
    Algebra.IsUnramifiedIn (𝓞 (normalClosure K L M)) p := by
  let N := normalClosure K L M
  let _ : NumberField N := NumberField.of_module_finite K N
  let G := normalClosure K N (SeparableClosure K)
  let _ : NumberField G := NumberField.of_module_finite K G
  have : IsGalois K G := {}
  let φ : N →ₐ[K] G := (normalClosure.algHomEquiv K N (SeparableClosure K)).symm IsSepClosed.lift
  let E : (L →ₐ[K] M) → IntermediateField K G :=
    fun f ↦ (φ.comp ((normalClosure.algHomEquiv K L M).symm f)).fieldRange
  have hφ : φ.fieldRange = ⨆ f : L →ₐ[K] M, E f := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have hx : (x : M) ∈ ⨆ f : L →ₐ[K] M, f.fieldRange := x.2
      have hmap : (⨆ f : L →ₐ[K] M, ((normalClosure.algHomEquiv K L M).symm f).fieldRange).map
          N.val = ⨆ f : L →ₐ[K] M, f.fieldRange := by
        rw [IntermediateField.map_iSup]
        refine iSup_congr fun f ↦ ?_
        rw [AlgHom.map_fieldRange]
        rfl
      rw [← hmap] at hx
      rcases hx with ⟨y, hy, hyx⟩
      obtain rfl : y = x := N.val.injective hyx
      have hsub : ((⨆ f : L →ₐ[K] M,
          ((normalClosure.algHomEquiv K L M).symm f).fieldRange).map φ :
            IntermediateField K G) = ⨆ f : L →ₐ[K] M, E f := by
        rw [IntermediateField.map_iSup]
        exact iSup_congr fun f ↦ AlgHom.map_fieldRange _ φ
      rw [← hsub]
      exact ⟨y, hy, rfl⟩
    · exact iSup_le fun f ↦ by
        rintro _ ⟨z, rfl⟩
        exact ⟨(normalClosure.algHomEquiv K L M).symm f z, rfl⟩
  rw [← φ.isUnramifiedIn_fieldRange_iff, hφ, isUnramifiedIn_iSup_iff]
  intro f
  exact ((φ.comp ((normalClosure.algHomEquiv K L M).symm f)).isUnramifiedIn_fieldRange_iff p).mpr h

/-- **Unramifiedness in a field and in its normal closure.** In a tower `M / L / K` of fields with
`K` a number field and `L / K` finite, an ideal `p` of `𝓞 K` is unramified in
`normalClosure K L M` if and only if it is unramified in `L`. -/
@[simp]
theorem isUnramifiedIn_normalClosure_iff {K : Type*} [Field K] [NumberField K]
    (p : Ideal (𝓞 K)) (L M : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] :
    Algebra.IsUnramifiedIn (𝓞 (normalClosure K L M)) p ↔ Algebra.IsUnramifiedIn (𝓞 L) p := by
  refine ⟨fun h P hP hPp ↦ ?_, p.isUnramifiedIn_normalClosure M⟩
  let _ : NumberField L := NumberField.of_module_finite K L
  let N := normalClosure K L M
  let _ : NumberField N := NumberField.of_module_finite K N
  have : P.IsPrime := hP
  have : P.LiesOver p := hPp
  obtain ⟨⟨Q, hQprime, hQover⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 N)))
  have : Q.IsPrime := hQprime
  have : Q.LiesOver P := hQover
  have : Algebra.IsUnramifiedAt (𝓞 K) Q := h Q hQprime (LiesOver.trans Q P p)
  exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) P Q

/-- If `L / K` is a finite extension of a number field `K` and `𝓞 L` is formally unramified over
`𝓞 K`, then so is the ring of integers of `normalClosure K L M` inside any ambient `K`-field `M`. -/
theorem _root_.Algebra.FormallyUnramified.ringOfIntegers_normalClosure
    {K : Type*} [Field K] [NumberField K] (L M : Type*)
    [Field L] [Algebra K L] [FiniteDimensional K L] [Field M] [Algebra K M]
    [Algebra.FormallyUnramified (𝓞 K) (𝓞 L)] :
    Algebra.FormallyUnramified (𝓞 K) (𝓞 (normalClosure K L M)) :=
  Algebra.formallyUnramified_iff_forall.mpr fun Q ↦
    ((Q.asIdeal.under (𝓞 K)).isUnramifiedIn_normalClosure M fun P hP _ ↦
      Algebra.formallyUnramified_iff_forall.mp ‹_› ⟨P, hP⟩) Q.asIdeal Q.isPrime ⟨rfl⟩

end AmbientNormalClosure

end Ideal
