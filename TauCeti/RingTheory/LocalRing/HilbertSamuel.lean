/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Length

import Mathlib.RingTheory.LocalRing.RingHom.Basic
import TauCeti.Algebra.Module.Equiv.Length
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.Length

/-!
# The Hilbert–Samuel function of a local ring quotient

For a local ring `(A, 𝔪)` and an ideal `I` of `A`, the Hilbert–Samuel function of `A ⧸ I` is
`H_{A / I}(n) = length_A(A ⧸ (I ⊔ 𝔪 ^ (n + 1)))` (`TauCeti.localQuotientHilbertSamuel A I n`),
valued in `ℕ∞`. Measuring by local-ring length rather than ground-field dimension ensures that the
value at `0` is `1` for every proper ideal `I ≠ ⊤`, regardless of the degree of the residue field
over a base field, while the unit ideal `I = ⊤` yields the identically zero function.

## Main definitions and results

* `TauCeti.localQuotientHilbertSamuel`: `H_{A / I}(n) = length_A(A ⧸ (I ⊔ 𝔪 ^ (n + 1)))`.
* `TauCeti.localQuotientHilbertSamuel_eq_zero_iff`: `H_{A / I}(n) = 0 ↔ I = ⊤`.
* `TauCeti.localQuotientHilbertSamuel_zero_of_ne_top`: `H_{A / I}(0) = 1` for every proper ideal
  `I ≠ ⊤`, and `TauCeti.localQuotientHilbertSamuel_field_bot`: `H_K(n) = 1` for any field `K`.
* `TauCeti.localQuotientHilbertSamuel_anti` and `TauCeti.localQuotientHilbertSamuel_mono`:
  antitonicity in the ideal and monotonicity in `n`.
* `TauCeti.localQuotientHilbertSamuel_map_of_surjective`,
  `TauCeti.localQuotientHilbertSamuel_map_equiv`, and
  `TauCeti.localQuotientHilbertSamuel_quotient`: behaviour under surjective homomorphisms, ring
  isomorphisms, and quotients of local rings.
* `TauCeti.localQuotientHilbertSamuel_ne_top`: finiteness when `A` is Noetherian.
* `TauCeti.localQuotientHilbertSamuel_map_adicCompletion_of_fg` and
  `TauCeti.localQuotientHilbertSamuel_map_adicCompletion`: invariance under `𝔪`-adic completion
  when `𝔪` is finitely generated (in particular when `A` is Noetherian).

## References

* E. Bierstone and P. D. Milman, *Canonical desingularization in characteristic zero by blowing
  up the maximum strata of a local invariant*, Invent. Math. **128** (1997), 207–302, Remarks 1.3.
-/

public section

namespace TauCeti

open IsLocalRing

section Basic

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- The Hilbert–Samuel function of `A ⧸ I`, measured by local-ring length:
`H_{A / I}(n) = length_A(A ⧸ (I ⊔ 𝔪 ^ (n + 1)))`. This includes the zero quotient for `I = ⊤`,
and takes finite values whenever `A` is Noetherian. -/
noncomputable def localQuotientHilbertSamuel (A : Type*) [CommRing A] [IsLocalRing A]
    (I : Ideal A) (n : ℕ) : ℕ∞ :=
  Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1)))

/-- Definitional unfolding of `localQuotientHilbertSamuel`. -/
theorem localQuotientHilbertSamuel_def (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n = Module.length A (A ⧸ (I ⊔ maximalIdeal A ^ (n + 1))) :=
  (rfl)

/-- For the zero ideal `⊥`, `localQuotientHilbertSamuel A ⊥ n` is the length of
`A ⧸ 𝔪 ^ (n + 1)`. -/
theorem localQuotientHilbertSamuel_bot (n : ℕ) :
    localQuotientHilbertSamuel A ⊥ n = Module.length A (A ⧸ maximalIdeal A ^ (n + 1)) := by
  rw [localQuotientHilbertSamuel_def, bot_sup_eq]

/-- The Hilbert–Samuel function of the zero quotient `A ⧸ ⊤` is identically zero. -/
@[simp]
theorem localQuotientHilbertSamuel_top (n : ℕ) :
    localQuotientHilbertSamuel A ⊤ n = 0 := by
  rw [localQuotientHilbertSamuel_def, top_sup_eq, Module.length_eq_zero_iff]
  exact Submodule.Quotient.subsingleton_iff.mpr rfl

/-- The Hilbert–Samuel function of `A ⧸ I` vanishes at any degree `n` if and only if `I = ⊤`. -/
@[simp]
theorem localQuotientHilbertSamuel_eq_zero_iff (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n = 0 ↔ I = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ localQuotientHilbertSamuel_top n⟩
  rw [localQuotientHilbertSamuel_def, Module.length_eq_zero_iff,
    Submodule.Quotient.subsingleton_iff] at h
  by_contra hI
  have hle : I ⊔ maximalIdeal A ^ (n + 1) ≤ maximalIdeal A :=
    sup_le (le_maximalIdeal hI) ((Ideal.pow_le_pow_right (Nat.succ_pos n)).trans (by simp))
  exact (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ hle))

/-- For any proper ideal `I ≠ ⊤`, `H_{A / I}(0) = 1`: `A ⧸ (I ⊔ 𝔪) = A ⧸ 𝔪` is a simple
`A`-module regardless of the residue field's degree over any ground field. -/
theorem localQuotientHilbertSamuel_zero_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) :
    localQuotientHilbertSamuel A I 0 = 1 := by
  have hsup : I ⊔ maximalIdeal A ^ 1 = maximalIdeal A := by
    rw [pow_one, sup_eq_right]
    exact le_maximalIdeal hI
  rw [localQuotientHilbertSamuel_def, zero_add, hsup, Ideal.length_quotient_eq_one]

/-- Every local ring satisfies `H_A(0) = 1`. -/
@[simp]
theorem localQuotientHilbertSamuel_zero_bot :
    localQuotientHilbertSamuel A ⊥ 0 = 1 :=
  localQuotientHilbertSamuel_zero_of_ne_top bot_ne_top

/-- The Hilbert–Samuel function of a field is identically `1`, regardless of its degree over any
base field. -/
@[simp]
theorem localQuotientHilbertSamuel_field_bot {K : Type*} [Field K] (n : ℕ) :
    localQuotientHilbertSamuel K ⊥ n = 1 := by
  have hpow : maximalIdeal K ^ (n + 1) = maximalIdeal K := by
    rw [maximalIdeal_eq_bot, ← Ideal.zero_eq_bot, zero_pow (Nat.succ_ne_zero n)]
  rw [localQuotientHilbertSamuel_bot, hpow, Ideal.length_quotient_eq_one]

/-- Enlarging the ideal cannot increase the Hilbert–Samuel function. -/
theorem localQuotientHilbertSamuel_anti {I J : Ideal A} (h : I ≤ J) (n : ℕ) :
    localQuotientHilbertSamuel A J n ≤ localQuotientHilbertSamuel A I n :=
  length_quotient_anti (sup_le_sup_right h _)

/-- The Hilbert–Samuel function of `A ⧸ I` is nondecreasing in `n`. -/
theorem localQuotientHilbertSamuel_mono (I : Ideal A) :
    Monotone (localQuotientHilbertSamuel A I) := fun _ _ h ↦
  length_quotient_anti (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) I)

/-- Along a surjective homomorphism `ψ : A →+* B` of local rings, the Hilbert–Samuel function of
`B ⧸ ψ(I)` equals that of `A ⧸ (I ⊔ ker ψ)`. -/
theorem localQuotientHilbertSamuel_map_of_surjective {B : Type*} [CommRing B] [IsLocalRing B]
    {ψ : A →+* B} (hψ : Function.Surjective ψ) (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel B (I.map ψ) n =
      localQuotientHilbertSamuel A (I ⊔ RingHom.ker ψ) n := by
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_def,
    ← map_maximalIdeal_of_surjective ψ hψ, ← Ideal.map_pow, ← Ideal.map_sup,
    Ideal.length_quotient_map_of_surjective _ hψ, sup_right_comm]

/-- A ring isomorphism of local rings preserves the Hilbert–Samuel function. -/
theorem localQuotientHilbertSamuel_map_equiv {B : Type*} [CommRing B] [IsLocalRing B]
    (e : A ≃+* B) (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel B (I.map (e : A →+* B)) n =
      localQuotientHilbertSamuel A I n := by
  have hker : RingHom.ker (e : A →+* B) = ⊥ :=
    eq_bot_iff.mpr fun x hx ↦ e.injective (by simpa using hx)
  rw [localQuotientHilbertSamuel_map_of_surjective e.surjective, hker, sup_bot_eq]

/-- Passing to a local quotient `A ⧸ I` computes the same Hilbert–Samuel function as adjoining `I`
in `A`. -/
theorem localQuotientHilbertSamuel_quotient (I J : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    localQuotientHilbertSamuel (A ⧸ I) (J.map (Ideal.Quotient.mk I)) n =
      localQuotientHilbertSamuel A (I ⊔ J) n := by
  rw [localQuotientHilbertSamuel_map_of_surjective Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, sup_comm]

/-- For a local quotient `A ⧸ I`, `localQuotientHilbertSamuel A I` coincides with the intrinsic
Hilbert–Samuel function `localQuotientHilbertSamuel (A ⧸ I) ⊥`. -/
theorem localQuotientHilbertSamuel_quotient_bot (I : Ideal A) [IsLocalRing (A ⧸ I)] (n : ℕ) :
    localQuotientHilbertSamuel (A ⧸ I) ⊥ n = localQuotientHilbertSamuel A I n := by
  simpa using localQuotientHilbertSamuel_quotient I ⊥ n

end Basic

section Noetherian

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- In a Noetherian local ring `A`, `A ⧸ (I ⊔ 𝔪 ^ n)` has finite length for every ideal `I` and
every `n`. -/
theorem isFiniteLength_quotient_sup_maximalIdeal_pow (I : Ideal A) (n : ℕ) :
    IsFiniteLength A (A ⧸ (I ⊔ maximalIdeal A ^ n)) :=
  (isFiniteLength_quotient_maximalIdeal_pow (A := A) n).of_surjective
    (f := Submodule.factor le_sup_right) (Submodule.factor_surjective le_sup_right)

/-- In a Noetherian local ring, every value of `localQuotientHilbertSamuel` is finite, including
for `I = ⊤`. -/
theorem localQuotientHilbertSamuel_ne_top (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel A I n ≠ ⊤ :=
  Module.length_ne_top_iff.mpr (isFiniteLength_quotient_sup_maximalIdeal_pow I (n + 1))

/-- Casting the `ℕ`-valued Hilbert–Samuel count back to `ℕ∞` recovers
`localQuotientHilbertSamuel A I n` for a Noetherian local ring `A`. -/
@[simp]
theorem natCast_toNat_localQuotientHilbertSamuel (I : Ideal A) (n : ℕ) :
    ((localQuotientHilbertSamuel A I n).toNat : ℕ∞) = localQuotientHilbertSamuel A I n :=
  ENat.natCast_toNat (localQuotientHilbertSamuel_ne_top I n)

end Noetherian

section Completion

/-- **Completion invariance of the Hilbert–Samuel function** for a local ring with finitely
generated maximal ideal: extending an ideal `I` to the `𝔪`-adic completion `Â` preserves every
value `H_{A / I}(n)`. -/
theorem localQuotientHilbertSamuel_map_adicCompletion_of_fg {A : Type*} [CommRing A]
    [IsLocalRing A] (fg : (maximalIdeal A).FG)
    [IsLocalRing (AdicCompletion (maximalIdeal A) A)] (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A)
        (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) n =
      localQuotientHilbertSamuel A I n := by
  let Ahat := AdicCompletion (maximalIdeal A) A
  have hmax : maximalIdeal Ahat = (maximalIdeal A).map (algebraMap A Ahat) :=
    (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ le_rfl fg)).symm
  rw [localQuotientHilbertSamuel_def, localQuotientHilbertSamuel_def, hmax]
  set Khat : Ideal Ahat :=
    I.map (algebraMap A Ahat) ⊔ ((maximalIdeal A).map (algebraMap A Ahat)) ^ (n + 1)
  set K : Ideal A := I ⊔ maximalIdeal A ^ (n + 1)
  have h1 : Module.length Ahat (Ahat ⧸ Khat) = Module.length (Ahat ⧸ Khat) (Ahat ⧸ Khat) :=
    Module.length_eq_of_surjective (R := Ahat ⧸ Khat) (S := Ahat) (M := Ahat ⧸ Khat)
      Ideal.Quotient.mk_surjective
  have h2 : Module.length A (A ⧸ K) = Module.length (A ⧸ K) (A ⧸ K) :=
    Module.length_eq_of_surjective (R := A ⧸ K) (S := A) (M := A ⧸ K)
      Ideal.Quotient.mk_surjective
  rw [h1, h2]
  exact (AdicCompletion.quotientMapSupPowAlgEquiv fg I (n + 1)).toRingEquiv.length_self_eq

/-- **Completion invariance of the Hilbert–Samuel function** for a Noetherian local ring `A`:
extending any ideal `I` to the `𝔪`-adic completion `Â` preserves `localQuotientHilbertSamuel`. -/
theorem localQuotientHilbertSamuel_map_adicCompletion {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A)
        (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) n =
      localQuotientHilbertSamuel A I n :=
  localQuotientHilbertSamuel_map_adicCompletion_of_fg (maximalIdeal A).fg_of_isNoetherianRing I n

/-- Passing to the `𝔪`-adic completion of a Noetherian local ring preserves its Hilbert–Samuel
function `H_A(n)`. -/
@[simp]
theorem localQuotientHilbertSamuel_adicCompletion_bot {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (n : ℕ) :
    localQuotientHilbertSamuel (AdicCompletion (maximalIdeal A) A) ⊥ n =
      localQuotientHilbertSamuel A ⊥ n := by
  simpa using localQuotientHilbertSamuel_map_adicCompletion (A := A) ⊥ n

end Completion

end TauCeti
