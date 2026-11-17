/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Trace.Star

/-!
# The sign isomorphism on the Temperley–Lieb tower

For every commutative ring `R`, loop parameter `δ : R`, and number of strands `n`, the
Temperley–Lieb algebras at `δ` and `-δ` are isomorphic via the **sign isomorphism**
`TauCeti.TemperleyLieb.signEquiv δ n : TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n`,
sending each generator `e δ i` to `-e (-δ) i`. Indeed `(-e (-δ) i) ^ 2 = (-δ) • e (-δ) i =
δ • (-e (-δ) i)`, while the adjacent zigzag and distant commutation relations are unchanged under
negating every generator. In contrast, an algebra homomorphism on two strands sending the generator
to the generator forces the loop parameters to coincide
(`TauCeti.TemperleyLieb.eq_of_algHom_map_e`), so no generator-fixing homomorphism
`TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2` exists unless `2 * δ = 0`.

This file develops the compatibility of `signEquiv` with the algebraic, star, Markov-trace, and
trace-radical quotient structure of the Temperley–Lieb tower over arbitrary commutative rings and
fields (with no analytic or real/complex assumptions):

* **Tower, crossings, and Jones–Wenzl projections**: `signEquiv` commutes with `strandIncl`,
  preserves `aug`, maps `crossing δ α β i` to `crossing (-δ) α (-β) i`, and maps
  `jonesWenzl δ n` to `jonesWenzl (-δ) n` unconditionally over every commutative ring (with no
  invertibility assumption on the quantum integers, because
  `qInt R (-δ) n = (-1) ^ (n + 1) * qInt R δ n` cancels the sign flip on `e (-δ) (Fin.last m)`
  inside Wenzl's recursion).
* **Analytic adjoint**: for a self-adjoint loop parameter `δ`, `signEquiv` preserves the analytic
  adjoint `star`, giving a `⋆`-algebra equivalence `TauCeti.TemperleyLieb.signStarEquiv`.
* **Markov traces and sesquilinear forms**: pulling back any Markov trace at `-δ` along `signEquiv`
  and scaling level `n` by `(-1) ^ n` gives a Markov trace at `δ`. By Markov uniqueness, any two
  Markov traces `tr` at `δ` and `tr'` at `-δ` satisfy
  `tr' n (signEquiv δ n x) = (-1) ^ n * tr n x`. Consequently, the normalized traces
  `Ring.inverse δ ^ n * tr n` (or `(δ ^ n)⁻¹ * tr n` over a field) and normalized Hermitian forms
  are invariant under `signEquiv`.
* **Trace-radical quotients**: `signEquiv` preserves and reflects membership in the trace radical,
  descending to algebra isomorphisms `quotientSignEquiv` and `⋆`-algebra isomorphisms
  `quotientSignStarEquiv` between the trace-radical quotients at `δ` and `-δ`, intertwining
  `quotientStrandIncl` and `quotientStrandInclStarAlgHom`, scaling `quotientTrace` by `(-1) ^ n`,
  and preserving the normalized quotient trace.

For the resulting positivity classification at negative and nonzero real loop parameters over `ℂ`,
see `TauCeti.Algebra.TemperleyLieb.Sign.Positivity`.

## Main definitions

* `TauCeti.TemperleyLieb.signEquiv`: the `R`-algebra isomorphism
  `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n` sending `e δ i` to `-e (-δ) i`.
* `TauCeti.TemperleyLieb.signStarEquiv`: `signEquiv` upgraded to a `⋆`-algebra equivalence.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignStarEquiv`: the induced algebra and `⋆`-algebra
  isomorphisms between the trace-radical quotients at `δ` and `-δ`.

## Main results

* `TauCeti.TemperleyLieb.eq_of_algHom_map_e`,
  `TauCeti.TemperleyLieb.two_mul_eq_zero_of_algHom_map_e_neg`: rigidity of the loop parameter
  under generator-fixing algebra homomorphisms on two strands.
* `TauCeti.TemperleyLieb.signEquiv_strandIncl`, `TauCeti.TemperleyLieb.signEquiv_jonesWenzl`,
  `TauCeti.TemperleyLieb.signEquiv_neg_apply_signEquiv`: tower compatibility, unconditional
  invariance of Jones–Wenzl projections, and involutivity across opposite fibers.
* `TauCeti.TemperleyLieb.IsMarkovTrace.compSignEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.compSignEquivSymm`: transport of Markov traces between `δ`
  and `-δ` with the sign factor `(-1) ^ n`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_signEquiv`,
  `TauCeti.TemperleyLieb.markovTrace_signEquiv`: trace scaling
  `tr' n (signEquiv δ n x) = (-1) ^ n * tr n x`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.inverse_pow_mul_map_signEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.inv_pow_mul_map_signEquiv`: invariance of normalized traces
  under `signEquiv`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.inverse_pow_mul_quotientTrace_quotientSignEquiv`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.inv_pow_mul_quotientTrace_quotientSignEquiv`: invariance of
  normalized quotient traces under `quotientSignEquiv`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignStarEquiv_comp_quotientStrandInclStarAlgHom`:
  `⋆`-algebra tower compatibility on trace-radical quotients.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Facts 4.4.14 (TB6), p. 155, and
  Sections 4.3–4.5.
* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
-/

public section

namespace TauCeti.TemperleyLieb

section Rigidity

variable {R : Type*}

/-- An algebra homomorphism `TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R δ' 2` sending the
two-strand generator to the generator forces `δ = δ'`: applying it to `e² = δ • e` yields
`δ' • e = δ • e`, and distinct scalar multiples of the two-strand generator are distinct. -/
theorem eq_of_algHom_map_e [CommSemiring R] {δ δ' : R}
    (f : TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R δ' 2) (i : Fin (2 - 1))
    (hf : f (e δ i) = e δ' i) : δ = δ' := by
  apply smul_left_injective_e_two (δ := δ') i
  have h := congrArg f (e_mul_self (δ := δ) i)
  rw [map_mul, map_smul, hf, e_mul_self] at h
  exact h.symm

/-- A generator-fixing algebra homomorphism `TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2`
forces `2 * δ = 0`. In particular, over a ring where `2 * δ ≠ 0`, no generator-fixing algebra
map connects `δ` and `-δ`. -/
theorem two_mul_eq_zero_of_algHom_map_e_neg [CommRing R] {δ : R}
    (f : TemperleyLieb R δ 2 →ₐ[R] TemperleyLieb R (-δ) 2) (i : Fin (2 - 1))
    (hf : f (e δ i) = e (-δ) i) : 2 * δ = 0 := by
  rw [two_mul]
  exact add_eq_zero_iff_eq_neg.mpr (eq_of_algHom_map_e f i hf)

end Rigidity

section SignEquiv

variable {R : Type*} [CommRing R]

private def signHom (δ : R) (n : ℕ) :
    TemperleyLieb R δ n →ₐ[R] TemperleyLieb R (-δ) n :=
  lift (fun i ↦ -e (-δ) i)
    (fun i ↦ by rw [neg_mul_neg, e_mul_self, neg_smul, smul_neg])
    (fun h ↦ by simp [e_mul_e_mul_e h])
    (fun h ↦ by rw [neg_mul_neg, neg_mul_neg, (commute_e h).eq])

private def signHomInv (δ : R) (n : ℕ) :
    TemperleyLieb R (-δ) n →ₐ[R] TemperleyLieb R δ n :=
  lift (fun i ↦ -e δ i)
    (fun i ↦ by rw [neg_mul_neg, e_mul_self, neg_smul, smul_neg, neg_neg])
    (fun h ↦ by simp [e_mul_e_mul_e h])
    (fun h ↦ by rw [neg_mul_neg, neg_mul_neg, (commute_e h).eq])

/-- The **sign isomorphism** `TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n`, sending each
generator `e δ i` to `-e (-δ) i`. Its inverse acts by the same formula `e (-δ) i ↦ -e δ i`. -/
def signEquiv (δ : R) (n : ℕ) :
    TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R (-δ) n :=
  AlgEquiv.ofAlgHom (signHom δ n) (signHomInv δ n)
    (hom_ext fun i ↦ by simp [signHom, signHomInv])
    (hom_ext fun i ↦ by simp [signHom, signHomInv])

variable {δ : R} {n : ℕ}

/-- The sign isomorphism negates every generator. -/
@[simp]
theorem signEquiv_e (i : Fin (n - 1)) : signEquiv δ n (e δ i) = -e (-δ) i := by
  simp [signEquiv, signHom]

/-- The inverse of the sign isomorphism negates every generator. -/
@[simp]
theorem signEquiv_symm_e (i : Fin (n - 1)) :
    (signEquiv δ n).symm (e (-δ) i) = -e δ i := by
  simp [signEquiv, signHomInv]

/-- An algebra homomorphism `TemperleyLieb R δ n →ₐ[R] TemperleyLieb R (-δ) n` that negates every
generator equals `signEquiv δ n`. -/
theorem eq_signEquiv_of_map_e {f : TemperleyLieb R δ n →ₐ[R] TemperleyLieb R (-δ) n}
    (hf : ∀ i : Fin (n - 1), f (e δ i) = -e (-δ) i) :
    f = (signEquiv δ n).toAlgHom :=
  hom_ext fun i ↦ by simp [hf]

/-- An algebra homomorphism `TemperleyLieb R (-δ) n →ₐ[R] TemperleyLieb R δ n` that negates every
generator equals `(signEquiv δ n).symm`. -/
theorem eq_signEquiv_symm_of_map_e {f : TemperleyLieb R (-δ) n →ₐ[R] TemperleyLieb R δ n}
    (hf : ∀ i : Fin (n - 1), f (e (-δ) i) = -e δ i) :
    f = (signEquiv δ n).symm.toAlgHom :=
  hom_ext fun i ↦ by simp [hf]

/-- Involutivity of `signEquiv` across the two fibers: applying `signEquiv (-δ) n` after
`signEquiv δ n` agrees with transporting along `-(-δ) = δ`. -/
theorem signEquiv_neg_apply_signEquiv (δ : R) (n : ℕ) (x : TemperleyLieb R δ n) :
    signEquiv (-δ) n (signEquiv δ n x) = (neg_neg δ).symm ▸ x := by
  have he_rec : ∀ {a : R} (h : δ = a) (i : Fin (n - 1)),
      h ▸ e δ i = e a i := by
    rintro _ rfl _; rfl
  have halg_rec : ∀ {a : R} (h : δ = a) (r : R),
      h ▸ algebraMap R (TemperleyLieb R δ n) r = algebraMap R (TemperleyLieb R a n) r := by
    rintro _ rfl _; rfl
  have hadd_rec : ∀ {a : R} (h : δ = a) (y z : TemperleyLieb R δ n),
      h ▸ (y + z) = (h ▸ y) + (h ▸ z) := by
    rintro _ rfl _ _; rfl
  have hmul_rec : ∀ {a : R} (h : δ = a) (y z : TemperleyLieb R δ n),
      h ▸ (y * z) = (h ▸ y) * (h ▸ z) := by
    rintro _ rfl _ _; rfl
  induction x using TemperleyLieb.induction with
  | e i =>
    rw [signEquiv_e, map_neg, signEquiv_e, neg_neg (e (- -δ) i)]
    exact (he_rec _ i).symm
  | algebraMap r =>
    rw [AlgEquiv.commutes, AlgEquiv.commutes]
    exact (halg_rec _ r).symm
  | add y z hy hz =>
    rw [map_add, map_add, hy, hz]
    exact (hadd_rec _ y z).symm
  | mul y z hy hz =>
    rw [map_mul, map_mul, hy, hz]
    exact (hmul_rec _ y z).symm

/-- The sign isomorphism commutes with adding a straight strand. -/
@[simp]
theorem signEquiv_strandIncl (x : TemperleyLieb R δ (n + 1)) :
    signEquiv δ (n + 2) (strandIncl x) = strandIncl (signEquiv δ (n + 1) x) := by
  have h : ((signEquiv δ (n + 2)).toAlgHom).comp strandIncl =
      strandIncl.comp (signEquiv δ (n + 1)).toAlgHom :=
    hom_ext fun i ↦ by simp
  exact AlgHom.congr_fun h x

/-- The inverse sign isomorphism commutes with adding a straight strand. -/
@[simp]
theorem signEquiv_symm_strandIncl (x : TemperleyLieb R (-δ) (n + 1)) :
    (signEquiv δ (n + 2)).symm (strandIncl x) = strandIncl ((signEquiv δ (n + 1)).symm x) := by
  apply (signEquiv δ (n + 2)).injective
  simp only [AlgEquiv.apply_symm_apply, signEquiv_strandIncl]

/-- The sign isomorphism preserves the augmentation. -/
@[simp]
theorem aug_signEquiv (x : TemperleyLieb R δ n) : aug (signEquiv δ n x) = aug x := by
  have h : aug.comp (signEquiv δ n).toAlgHom = aug :=
    hom_ext fun i ↦ by simp
  exact AlgHom.congr_fun h x

/-- The inverse sign isomorphism preserves the augmentation. -/
@[simp]
theorem aug_signEquiv_symm (x : TemperleyLieb R (-δ) n) :
    aug ((signEquiv δ n).symm x) = aug x := by
  simpa only [AlgEquiv.apply_symm_apply] using (aug_signEquiv ((signEquiv δ n).symm x)).symm

/-- The sign isomorphism negates the cup-cap coefficient of a Kauffman crossing. -/
theorem signEquiv_crossing (α β : R) (i : Fin (n - 1)) :
    signEquiv δ n (crossing δ α β i) = crossing (-δ) α (-β) i := by
  simp [crossing_def]

/-- The inverse sign isomorphism negates the cup-cap coefficient of a Kauffman crossing. -/
theorem signEquiv_symm_crossing (α β : R) (i : Fin (n - 1)) :
    (signEquiv δ n).symm (crossing (-δ) α β i) = crossing δ α (-β) i := by
  simp [crossing_def]

/-- The sign isomorphism maps every Jones–Wenzl projection at `δ` to the corresponding
Jones–Wenzl projection at `-δ`. This holds unconditionally over every commutative ring, with no
invertibility assumption on the quantum integers. -/
@[simp]
theorem signEquiv_jonesWenzl (δ : R) :
    ∀ n : ℕ, signEquiv δ n (jonesWenzl δ n) = jonesWenzl (-δ) n
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    have hinv_neg_one : Ring.inverse (-1 : R) = -1 := by
      simpa using Ring.inverse_unit (-1 : Rˣ)
    have hinv_pow :
        Ring.inverse ((-1 : R) ^ (m + 3) * qInt R δ (m + 2)) =
          (-1 : R) ^ (m + 3) * Ring.inverse (qInt R δ (m + 2)) := by
      rw [Ring.inverse_mul (Or.inl (isUnit_one.neg.pow (m + 3))), ← Ring.inverse_pow,
        hinv_neg_one, mul_comm]
    have hcoeff :
        qInt R (-δ) (m + 1) * Ring.inverse (qInt R (-δ) (m + 2)) =
          -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by
      rw [qInt_neg, qInt_neg, hinv_pow]
      have hexp : m + 2 + (m + 3) = 2 * (m + 2) + 1 := by omega
      have hsign : (-1 : R) ^ (m + 2) * (-1 : R) ^ (m + 3) = -1 := by
        rw [← pow_add, hexp, pow_succ, pow_mul]
        simp
      calc
        (-1 : R) ^ (m + 2) * qInt R δ (m + 1) *
            ((-1 : R) ^ (m + 3) * Ring.inverse (qInt R δ (m + 2)))
          = ((-1 : R) ^ (m + 2) * (-1 : R) ^ (m + 3)) *
              (qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by ring
        _ = -(qInt R δ (m + 1) * Ring.inverse (qInt R δ (m + 2))) := by rw [hsign, neg_one_mul]
    rw [jonesWenzl_add_two, jonesWenzl_add_two, map_sub, map_smul, map_mul, map_mul,
      signEquiv_strandIncl, signEquiv_e, signEquiv_jonesWenzl δ (m + 1), hcoeff]
    simp only [mul_neg, neg_mul, smul_neg, neg_smul]

/-- The inverse sign isomorphism maps every Jones–Wenzl projection at `-δ` to the corresponding
Jones–Wenzl projection at `δ`. -/
@[simp]
theorem signEquiv_symm_jonesWenzl (δ : R) (n : ℕ) :
    (signEquiv δ n).symm (jonesWenzl (-δ) n) = jonesWenzl δ n :=
  (signEquiv δ n).symm_apply_eq.mpr (signEquiv_jonesWenzl δ n).symm

end SignEquiv

section Star

variable {R : Type*} [CommRing R] [StarRing R] {δ : R} {n : ℕ}
  [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]

/-- The sign isomorphism preserves the analytic adjoint. -/
@[simp]
theorem signEquiv_star (x : TemperleyLieb R δ n) :
    signEquiv δ n (star x) = star (signEquiv δ n x) :=
  map_star_iff (F := (signEquiv δ n).toAlgHom) |>.mpr
    (fun i ↦ by simpa only [AlgEquiv.coe_toAlgHom, signEquiv_e] using
      (isSelfAdjoint_e (δ := -δ) i).neg) x

/-- The inverse sign isomorphism preserves the analytic adjoint. -/
@[simp]
theorem signEquiv_symm_star (x : TemperleyLieb R (-δ) n) :
    (signEquiv δ n).symm (star x) = star ((signEquiv δ n).symm x) := by
  apply (signEquiv δ n).injective
  simp only [AlgEquiv.apply_symm_apply, signEquiv_star]

/-- The sign isomorphism upgraded to a `⋆`-algebra equivalence
`TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R (-δ) n`. Both `Fact (IsSelfAdjoint δ)` and
`Fact (IsSelfAdjoint (-δ))` are taken explicitly (the latter can be supplied locally via
`⟨hδ.out.neg⟩`) to avoid introducing a looping global `Fact` instance under negation. -/
def signStarEquiv (δ : R) (n : ℕ) [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))] :
    TemperleyLieb R δ n ≃⋆ₐ[R] TemperleyLieb R (-δ) n :=
  { (signEquiv δ n).toRingEquiv with
    map_smul' := fun r x ↦ map_smul (signEquiv δ n) r x
    map_star' := signEquiv_star }

/-- Forgetting star preservation from `signStarEquiv` recovers `signEquiv`. -/
@[simp]
theorem signStarEquiv_toAlgEquiv :
    (signStarEquiv δ n).toAlgEquiv = signEquiv δ n := by
  ext x
  rfl

/-- Applying `signStarEquiv` evaluates `signEquiv`. -/
@[simp]
theorem signStarEquiv_apply (x : TemperleyLieb R δ n) :
    signStarEquiv δ n x = signEquiv δ n x := (rfl)

/-- Applying `(signStarEquiv δ n).symm` evaluates `(signEquiv δ n).symm`. -/
@[simp]
theorem signStarEquiv_symm_apply (x : TemperleyLieb R (-δ) n) :
    (signStarEquiv δ n).symm x = (signEquiv δ n).symm x := (rfl)

end Star

section MarkovTrace

variable {R : Type*} [CommRing R]

private theorem isMarkovTrace_comp_sign {δ₁ δ₂ : R} (hδ : δ₁ + δ₂ = 0)
    (f : ∀ n, TemperleyLieb R δ₁ n ≃ₐ[R] TemperleyLieb R δ₂ n)
    (hf_e : ∀ n (i : Fin (n - 1)), f n (e δ₁ i) = -e δ₂ i)
    (hf_incl : ∀ n (x : TemperleyLieb R δ₁ (n + 1)),
      f (n + 2) (strandIncl x) = strandIncl (f (n + 1) x))
    {tr₂ : ∀ n : ℕ, TemperleyLieb R δ₂ n →ₗ[R] R} (htr₂ : IsMarkovTrace R δ₂ tr₂) :
    IsMarkovTrace R δ₁ (fun n ↦ ((-1 : R) ^ n) • (tr₂ n ∘ₗ (f n).toLinearMap)) where
  map_one n := by
    have hδ₂ : δ₂ = -δ₁ := eq_neg_of_add_eq_zero_right hδ
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_one,
      htr₂.map_one, smul_eq_mul, hδ₂, ← mul_pow, neg_one_mul, neg_neg]
  map_mul_comm n x y := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      smul_eq_mul, htr₂.map_mul_comm n (f n x)]
  map_strandIncl n x := by
    have hδ₂ : δ₂ = -δ₁ := eq_neg_of_add_eq_zero_right hδ
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      hf_incl, htr₂.map_strandIncl, smul_eq_mul, hδ₂, pow_succ]
    ring
  map_strandIncl_mul_e_last n x := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      hf_incl, hf_e, mul_neg, map_neg, htr₂.map_strandIncl_mul_e_last, smul_eq_mul, pow_succ]
    ring

namespace IsMarkovTrace

variable {δ : R} {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}

/-- Pulling back a Markov trace at `-δ` along `signEquiv` and scaling level `n` by `(-1) ^ n`
produces a Markov trace at `δ`. -/
theorem compSignEquiv (htr' : IsMarkovTrace R (-δ) tr') :
    IsMarkovTrace R δ (fun n ↦ ((-1 : R) ^ n) • (tr' n ∘ₗ (signEquiv δ n).toLinearMap)) :=
  isMarkovTrace_comp_sign (add_neg_cancel δ) (signEquiv δ)
    (fun _ i ↦ signEquiv_e i) (fun _ x ↦ signEquiv_strandIncl x) htr'

/-- Pulling back a Markov trace at `δ` along `(signEquiv δ n).symm` and scaling level `n` by
`(-1) ^ n` produces a Markov trace at `-δ`. -/
theorem compSignEquivSymm (htr : IsMarkovTrace R δ tr) :
    IsMarkovTrace R (-δ) (fun n ↦ ((-1 : R) ^ n) • (tr n ∘ₗ (signEquiv δ n).symm.toLinearMap)) :=
  isMarkovTrace_comp_sign (neg_add_cancel δ) (fun n ↦ (signEquiv δ n).symm)
    (fun _ i ↦ signEquiv_symm_e i) (fun _ x ↦ signEquiv_symm_strandIncl x) htr

/-- **Trace scaling under the sign isomorphism.** Any two Markov traces `tr` at `δ` and `tr'`
at `-δ` satisfy `tr' n (signEquiv δ n x) = (-1) ^ n * tr n x`. -/
theorem map_signEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) (x : TemperleyLieb R δ n) :
    tr' n (signEquiv δ n x) = (-1 : R) ^ n * tr n x := by
  have heq := LinearMap.congr_fun (congrFun (htr.unique htr'.compSignEquiv) n) x
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    smul_eq_mul] at heq
  rw [heq, ← mul_assoc, ← mul_pow]
  simp

/-- Pointwise trace scaling under `(signEquiv δ n).symm`. -/
theorem map_signEquiv_symm (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) (y : TemperleyLieb R (-δ) n) :
    tr n ((signEquiv δ n).symm y) = (-1 : R) ^ n * tr' n y := by
  have heq := LinearMap.congr_fun (congrFun (htr'.unique htr.compSignEquivSymm) n) y
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    smul_eq_mul] at heq
  rw [heq, ← mul_assoc, ← mul_pow]
  simp

/-- Over every commutative ring, `Ring.inverse (-δ) ^ n * tr' n (signEquiv δ n x) =
Ring.inverse δ ^ n * tr n x` with no invertibility assumption on `δ`. -/
theorem inverse_pow_mul_map_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) (x : TemperleyLieb R δ n) :
    Ring.inverse (-δ) ^ n * tr' n (signEquiv δ n x) = Ring.inverse δ ^ n * tr n x := by
  have hinv_neg_one : Ring.inverse (-1 : R) = -1 := by
    simpa using Ring.inverse_unit (-1 : Rˣ)
  have hinv : Ring.inverse (-δ) = -Ring.inverse δ := by
    rw [neg_eq_neg_one_mul δ, Ring.inverse_mul (Or.inl isUnit_one.neg), hinv_neg_one, mul_neg_one]
  rw [hinv, neg_eq_neg_one_mul (Ring.inverse δ), mul_pow, htr.map_signEquiv htr']
  calc
    (-1 : R) ^ n * Ring.inverse δ ^ n * ((-1 : R) ^ n * tr n x)
      = ((-1 : R) * (-1 : R)) ^ n * (Ring.inverse δ ^ n * tr n x) := by rw [mul_pow]; ring
    _ = Ring.inverse δ ^ n * tr n x := by simp

/-- Over a field, the normalized Markov trace `(δ ^ n)⁻¹ * tr n` is invariant under
`signEquiv`. -/
theorem inv_pow_mul_map_signEquiv {K : Type*} [Field K] {δ : K}
    {tr : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K}
    {tr' : ∀ n : ℕ, TemperleyLieb K (-δ) n →ₗ[K] K}
    (htr : IsMarkovTrace K δ tr) (htr' : IsMarkovTrace K (-δ) tr')
    (n : ℕ) (x : TemperleyLieb K δ n) :
    ((-δ) ^ n)⁻¹ * tr' n (signEquiv δ n x) = (δ ^ n)⁻¹ * tr n x := by
  simpa only [Ring.inverse_eq_inv', inv_pow] using
    htr.inverse_pow_mul_map_signEquiv htr' n x

section Sesquilinear

variable [StarRing R] [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]

/-- The sign isomorphism scales the Hermitian trace form by `(-1) ^ n`. -/
theorem traceSesqForm_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) (x y : TemperleyLieb R δ n) :
    (tr' n).traceSesqForm (signEquiv δ n x) (signEquiv δ n y) =
      (-1 : R) ^ n * (tr n).traceSesqForm x y := by
  simp only [LinearMap.traceSesqForm_apply, ← signEquiv_star, ← map_mul,
    htr.map_signEquiv htr']

/-- The inverse sign isomorphism scales the Hermitian trace form by `(-1) ^ n`. -/
theorem traceSesqForm_signEquiv_symm (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) (x y : TemperleyLieb R (-δ) n) :
    (tr n).traceSesqForm ((signEquiv δ n).symm x) ((signEquiv δ n).symm y) =
      (-1 : R) ^ n * (tr' n).traceSesqForm x y := by
  simp only [LinearMap.traceSesqForm_apply, ← signEquiv_symm_star, ← map_mul,
    htr.map_signEquiv_symm htr']

/-- Over every commutative star ring, the `Ring.inverse`-normalized Hermitian trace form is
invariant under `signEquiv`. -/
theorem inverse_pow_mul_traceSesqForm_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) (x y : TemperleyLieb R δ n) :
    Ring.inverse (-δ) ^ n * (tr' n).traceSesqForm (signEquiv δ n x) (signEquiv δ n y) =
      Ring.inverse δ ^ n * (tr n).traceSesqForm x y := by
  simp only [LinearMap.traceSesqForm_apply, ← signEquiv_star, ← map_mul,
    htr.inverse_pow_mul_map_signEquiv htr']

/-- Over a star field, the normalized Hermitian trace form `(δ ^ n)⁻¹ * tr n (star x * y)` is
invariant under `signEquiv`. -/
theorem inv_pow_mul_traceSesqForm_signEquiv {K : Type*} [Field K] [StarRing K] {δ : K}
    [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]
    {tr : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K}
    {tr' : ∀ n : ℕ, TemperleyLieb K (-δ) n →ₗ[K] K}
    (htr : IsMarkovTrace K δ tr) (htr' : IsMarkovTrace K (-δ) tr')
    (n : ℕ) (x y : TemperleyLieb K δ n) :
    ((-δ) ^ n)⁻¹ * (tr' n).traceSesqForm (signEquiv δ n x) (signEquiv δ n y) =
      (δ ^ n)⁻¹ * (tr n).traceSesqForm x y := by
  simpa only [Ring.inverse_eq_inv', inv_pow] using
    htr.inverse_pow_mul_traceSesqForm_signEquiv htr' n x y

end Sesquilinear

end IsMarkovTrace

/-- If `q` realizes `δ = -(q + q⁻¹)`, then `-q` realizes `-δ = -((-q) + (-q)⁻¹)`. -/
theorem neg_eq_neg_add_inv {q : Rˣ} {δ : R}
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) :
    -δ = -(((-q : Rˣ) : R) + (((-q)⁻¹ : Rˣ) : R)) := by
  rw [hq, Units.val_neg, inv_neg, Units.val_neg]
  ring

/-- The spin-model Markov trace scales by `(-1) ^ n` under `signEquiv`, for any unit `q'`
realizing `-δ` (in particular `q' = -q`). -/
theorem markovTrace_signEquiv {q q' : Rˣ} {δ : R}
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (hq' : -δ = -((q' : R) + ((q'⁻¹ : Rˣ) : R)))
    {n : ℕ} (x : TemperleyLieb R δ n) :
    markovTrace q' hq' (signEquiv δ n x) = (-1 : R) ^ n * markovTrace q hq x :=
  (isMarkovTrace_markovTrace q hq).map_signEquiv (isMarkovTrace_markovTrace q' hq') n x

/-- The spin-model Markov trace scales by `(-1) ^ n` under `(signEquiv δ n).symm`. -/
theorem markovTrace_signEquiv_symm {q q' : Rˣ} {δ : R}
    (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R)))
    (hq' : -δ = -((q' : R) + ((q'⁻¹ : Rˣ) : R)))
    {n : ℕ} (y : TemperleyLieb R (-δ) n) :
    markovTrace q hq ((signEquiv δ n).symm y) = (-1 : R) ^ n * markovTrace q' hq' y :=
  (isMarkovTrace_markovTrace q hq).map_signEquiv_symm (isMarkovTrace_markovTrace q' hq') n y

end MarkovTrace

section TraceRadicalQuotient

namespace IsMarkovTrace

variable {R : Type*} [CommRing R] {δ : R}
  {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}

/-- Pulling back the trace radical at `-δ` along `signEquiv` yields the trace radical at `δ`. -/
theorem comap_traceRadical_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    Ideal.comap (signEquiv δ n).toAlgHom
      ((tr' n).traceRadical (htr'.map_mul_comm n)) =
        (tr n).traceRadical (htr.map_mul_comm n) := by
  have hcomp : tr' n ∘ₗ (signEquiv δ n).toAlgHom.toLinearMap = ((-1 : R) ^ n) • tr n := by
    ext x
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom,
      LinearMap.smul_apply, smul_eq_mul, htr.map_signEquiv htr']
  have hmul : ∀ x y, (((-1 : R) ^ n) • tr n) (x * y) = (((-1 : R) ^ n) • tr n) (y * x) :=
    fun x y ↦ by simp [htr.map_mul_comm]
  rw [LinearMap.comap_traceRadical_of_surjective hmul (htr'.map_mul_comm n)
    (signEquiv δ n).toAlgHom hcomp (signEquiv δ n).surjective]
  exact LinearMap.traceRadical_smul (tr n) (htr.map_mul_comm n)
    (isUnit_one.neg.pow n).isRegular.left

/-- Mapping the trace radical at `δ` forward along `signEquiv` yields the trace radical at `-δ`. -/
theorem map_traceRadical_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    ((tr n).traceRadical (htr.map_mul_comm n)).map
      (signEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n) =
        (tr' n).traceRadical (htr'.map_mul_comm n) := by
  have h := htr.comap_traceRadical_signEquiv htr' n
  rw [← h]
  exact Ideal.map_comap_of_surjective _ (signEquiv δ n).surjective _

/-- The sign isomorphism preserves and reflects trace-radical membership. -/
theorem signEquiv_mem_traceRadical_iff (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') {n : ℕ} (x : TemperleyLieb R δ n) :
    signEquiv δ n x ∈ (tr' n).traceRadical (htr'.map_mul_comm n) ↔
      x ∈ (tr n).traceRadical (htr.map_mul_comm n) := by
  simpa only [Ideal.mem_comap, AlgEquiv.coe_toAlgHom] using
    SetLike.ext_iff.mp (htr.comap_traceRadical_signEquiv htr' n) x

/-- The algebra isomorphism induced by `signEquiv` between the trace-radical quotients at `δ`
and `-δ`. -/
def quotientSignEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃ₐ[R]
      TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n) :=
  Ideal.quotientEquivAlg _ _ (signEquiv δ n)
    (htr.map_traceRadical_signEquiv htr' n).symm

/-- `quotientSignEquiv` acts on representatives by `signEquiv`. -/
@[simp]
theorem quotientSignEquiv_mk (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) (x : TemperleyLieb R δ n) :
    htr.quotientSignEquiv htr' n
      (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) x) =
        Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) (signEquiv δ n x) := (rfl)

/-- `(quotientSignEquiv).symm` acts on representatives by `(signEquiv δ n).symm`. -/
@[simp]
theorem quotientSignEquiv_symm_mk (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) (y : TemperleyLieb R (-δ) n) :
    (htr.quotientSignEquiv htr' n).symm
      (Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) y) =
        Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n))
          ((signEquiv δ n).symm y) := (rfl)

/-- `quotientSignEquiv` intertwines the quotient strand inclusions at `δ` and `-δ`. -/
@[simp]
theorem quotientSignEquiv_quotientStrandIncl (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (q : TemperleyLieb R δ (n + 1) ⧸
      (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientSignEquiv htr' (n + 2) (htr.quotientStrandIncl n q) =
      htr'.quotientStrandIncl n (htr.quotientSignEquiv htr' (n + 1) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp only [htr.quotientStrandIncl_mk, htr.quotientSignEquiv_mk, htr'.quotientStrandIncl_mk,
    signEquiv_strandIncl]

/-- `(quotientSignEquiv).symm` intertwines the quotient strand inclusions at `-δ` and `δ`. -/
@[simp]
theorem quotientSignEquiv_symm_quotientStrandIncl (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (q : TemperleyLieb R (-δ) (n + 1) ⧸
      (tr' (n + 1)).traceRadical (htr'.map_mul_comm (n + 1))) :
    (htr.quotientSignEquiv htr' (n + 2)).symm (htr'.quotientStrandIncl n q) =
      htr.quotientStrandIncl n ((htr.quotientSignEquiv htr' (n + 1)).symm q) :=
  (htr.quotientSignEquiv htr' (n + 2)).injective (by simp)

/-- The quotient trace at `-δ` composed with `quotientSignEquiv` is `(-1) ^ n` times the
quotient trace at `δ`. -/
@[simp]
theorem quotientTrace_quotientSignEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (q : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    (tr' n).quotientTrace (htr'.map_mul_comm n) (htr.quotientSignEquiv htr' n q) =
      (-1 : R) ^ n * (tr n).quotientTrace (htr.map_mul_comm n) q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp only [htr.quotientSignEquiv_mk, LinearMap.quotientTrace_mk, htr.map_signEquiv htr']

/-- The quotient trace at `δ` composed with `(quotientSignEquiv).symm` is `(-1) ^ n` times the
quotient trace at `-δ`. -/
@[simp]
theorem quotientTrace_quotientSignEquiv_symm (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (q : TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :
    (tr n).quotientTrace (htr.map_mul_comm n) ((htr.quotientSignEquiv htr' n).symm q) =
      (-1 : R) ^ n * (tr' n).quotientTrace (htr'.map_mul_comm n) q := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp only [htr.quotientSignEquiv_symm_mk, LinearMap.quotientTrace_mk,
    htr.map_signEquiv_symm htr']

/-- Over every commutative ring, the `Ring.inverse`-normalized quotient traces at `δ` and `-δ`
agree under `quotientSignEquiv`. -/
theorem inverse_pow_mul_quotientTrace_quotientSignEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (q : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    Ring.inverse (-δ) ^ n * (tr' n).quotientTrace (htr'.map_mul_comm n)
        (htr.quotientSignEquiv htr' n q) =
      Ring.inverse δ ^ n * (tr n).quotientTrace (htr.map_mul_comm n) q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp only [htr.quotientSignEquiv_mk, LinearMap.quotientTrace_mk,
    htr.inverse_pow_mul_map_signEquiv htr']

/-- Over a field, the normalized quotient traces at `δ` and `-δ` agree under
`quotientSignEquiv`. -/
theorem inv_pow_mul_quotientTrace_quotientSignEquiv {K : Type*} [Field K] {δ : K}
    {tr : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K}
    {tr' : ∀ n : ℕ, TemperleyLieb K (-δ) n →ₗ[K] K}
    (htr : IsMarkovTrace K δ tr) (htr' : IsMarkovTrace K (-δ) tr') (n : ℕ)
    (q : TemperleyLieb K δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    ((-δ) ^ n)⁻¹ * (tr' n).quotientTrace (htr'.map_mul_comm n)
        (htr.quotientSignEquiv htr' n q) =
      (δ ^ n)⁻¹ * (tr n).quotientTrace (htr.map_mul_comm n) q := by
  simpa only [Ring.inverse_eq_inv', inv_pow] using
    htr.inverse_pow_mul_quotientTrace_quotientSignEquiv htr' n q

section StarQuotient

variable [StarRing R] [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint (-δ))]

/-- The `⋆`-algebra isomorphism induced by `signStarEquiv` between the trace-radical quotients
at `δ` and `-δ`. The required `Ideal.IsStar` instances are provided by
`IsMarkovTrace.isStar_traceRadical`. -/
def quotientSignStarEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃⋆ₐ[R]
      TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n) :=
  Ideal.quotientEquivStarAlg _ _ (signStarEquiv δ n) (by
    have hring :
        (signStarEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n) =
          (signEquiv δ n : TemperleyLieb R δ n →+* TemperleyLieb R (-δ) n) :=
      RingHom.ext fun _ ↦ rfl
    rw [hring]
    exact (htr.map_traceRadical_signEquiv htr' n).symm)

/-- `quotientSignStarEquiv` acts on representatives by `signEquiv`. -/
theorem quotientSignStarEquiv_mk (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (x : TemperleyLieb R δ n) :
    htr.quotientSignStarEquiv htr' n
      (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) x) =
        Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) (signEquiv δ n x) := by
  rw [quotientSignStarEquiv, Ideal.quotientEquivStarAlg_mk, signStarEquiv_apply]

/-- `(quotientSignStarEquiv).symm` acts on representatives by `(signEquiv δ n).symm`. -/
theorem quotientSignStarEquiv_symm_mk (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (y : TemperleyLieb R (-δ) n) :
    (htr.quotientSignStarEquiv htr' n).symm
      (Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) y) =
        Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n))
          ((signEquiv δ n).symm y) := by
  rw [quotientSignStarEquiv, Ideal.quotientEquivStarAlg_symm_mk, signStarEquiv_symm_apply]

/-- Applying `quotientSignStarEquiv` evaluates `quotientSignEquiv`. -/
@[simp]
theorem quotientSignStarEquiv_apply (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (q : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.quotientSignStarEquiv htr' n q = htr.quotientSignEquiv htr' n q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp only [htr.quotientSignStarEquiv_mk, htr.quotientSignEquiv_mk]

/-- Applying `(quotientSignStarEquiv).symm` evaluates `(quotientSignEquiv).symm`. -/
@[simp]
theorem quotientSignStarEquiv_symm_apply (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar]
    (q : TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :
    (htr.quotientSignStarEquiv htr' n).symm q = (htr.quotientSignEquiv htr' n).symm q := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp only [htr.quotientSignStarEquiv_symm_mk, htr.quotientSignEquiv_symm_mk]

/-- Forgetting star preservation from `quotientSignStarEquiv` recovers `quotientSignEquiv`. -/
@[simp]
theorem quotientSignStarEquiv_toAlgEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    [((tr' n).traceRadical (htr'.map_mul_comm n)).IsStar] :
    (htr.quotientSignStarEquiv htr' n).toAlgEquiv = htr.quotientSignEquiv htr' n := by
  ext q
  exact htr.quotientSignStarEquiv_apply htr' n q

/-- `quotientSignStarEquiv` intertwines the `⋆`-algebra strand inclusions on the trace-radical
quotients. -/
theorem quotientSignStarEquiv_comp_quotientStrandInclStarAlgHom (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar]
    [((tr' (n + 1)).traceRadical (htr'.map_mul_comm (n + 1))).IsStar]
    [((tr' (n + 2)).traceRadical (htr'.map_mul_comm (n + 2))).IsStar] :
    (htr.quotientSignStarEquiv htr' (n + 2)).toStarAlgHom.comp
      (htr.quotientStrandInclStarAlgHom n) =
    (htr'.quotientStrandInclStarAlgHom n).comp
      (htr.quotientSignStarEquiv htr' (n + 1)).toStarAlgHom := by
  ext q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp only [StarAlgHom.comp_apply, StarAlgEquiv.toStarAlgHom_apply,
    htr.quotientStrandInclStarAlgHom_mk, htr'.quotientStrandInclStarAlgHom_mk,
    htr.quotientSignStarEquiv_mk, signEquiv_strandIncl]

end StarQuotient

end IsMarkovTrace

end TraceRadicalQuotient

end TauCeti.TemperleyLieb
