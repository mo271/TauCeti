/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Coassoc
public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration.GradedCoderivation
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoalgHom
public import TauCeti.LinearAlgebra.TensorCoalgebra.OddSquare

/-!
# Transitivity and symmetry of coalgebra homotopies

Let `M` and `N` carry internal integer gradings `G` and `H`, and let `b_M` and `b_N` be degree-one,
square-zero graded coderivations of the reduced tensor coalgebras `Tᶜ(M)` and `Tᶜ(N)`.  For
degree-zero coalgebra morphisms `F F' : Tᶜ(M) ⟶ Tᶜ(N)` intertwining `b_M` and `b_N`, a coalgebra
homotopy from `F` to `F'` is a degree-`(-1)` coderivation `D` along `F` and `F'` at twist parameter
one satisfying `F - F' = b_N ∘ D + D ∘ b_M`.

Unlike ordinary chain homotopies, the naïve sum `H₁ + H₂` of an `(F, F')`-coderivation `H₁` and an
`(F', F'')`-coderivation `H₂` is not an `(F, F'')`-coderivation, and `-D` is not an
`(F', F)`-coderivation: the intermediate morphism `F'` in the co-Leibniz rule does not cancel.
Following Lefèvre-Hasegawa and Lyubashenko, one corrects both defects by adding a graded commutator
`b_N ∘ Φ - Φ ∘ b_M` with a degree-`(-2)` map `Φ : Tᶜ(M) ⟶ Tᶜ(N)` built recursively along the
conilpotence filtration so as to satisfy the second-order co-Leibniz identity

`Δ ∘ Φ = (Φ ⊗ F'' + (H₁ ∘ τ_M) ⊗ H₂ + F ⊗ Φ) ∘ Δ`.

Because `b_M` and `b_N` square to zero, the commutator `b_N ∘ Φ - Φ ∘ b_M` leaves the homotopy
boundary unchanged while its co-Leibniz defect cancels the mismatch between `F'` and `F, F''`.

## Main definitions

* `TauCeti.ReducedTensorWords.filtrationLimit`: the limit of a sequence of linear maps out of
  `Tᶜ(M)` that stabilises on each filtration stage `filtration R M n`.
* `TauCeti.ReducedTensorWords.prependLetter`: prepending the letter component of the left tensor
  factor to the right tensor factor.
* `TauCeti.ReducedTensorWords.gradedCoderivAlongTrans`: the composite coalgebra homotopy from `F`
  to `F''` built from homotopies `H₁` (`F ~ F'`) and `H₂` (`F' ~ F''`).
* `TauCeti.ReducedTensorWords.gradedCoderivAlongSymm`: the inverse coalgebra homotopy from `F'` to
  `F` built from a homotopy `D` (`F ~ F'`).

## Main results

* `TauCeti.ReducedTensorWords.ofLetter_letter_add_prependLetter_deconcatenation`: every reduced
  tensor word decomposes into its letter component and `prependLetter` of its deconcatenation.
* `TauCeti.ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlongTrans`,
  `TauCeti.ReducedTensorWords.isHomogeneous_gradedCoderivAlongTrans`, and
  `TauCeti.ReducedTensorWords.sub_eq_comp_add_comp_gradedCoderivAlongTrans`: transitivity of
  coalgebra homotopies.
* `TauCeti.ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlongSymm`,
  `TauCeti.ReducedTensorWords.isHomogeneous_gradedCoderivAlongSymm`, and
  `TauCeti.ReducedTensorWords.sub_eq_comp_add_comp_gradedCoderivAlongSymm`: symmetry of coalgebra
  homotopies.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Chapter 1, Section 1.3.
* V. Lyubashenko, *Category of A-infinity-categories*, Homology Homotopy Appl. 5 (2003), Section 2.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM uN uP

namespace TauCeti

namespace ReducedTensorWords

/-! ### Stabilising sequences along the word-length filtration -/

section FiltrationLimit

variable {R : Type uR} {M : Type uM} {P : Type uP} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid P] [Module R P]

/-- Assemble a sequence of linear maps `f n : Tᶜ(M) ⟶ P` into a single linear map by evaluating
`f k` on tensor words of length `k`.  When the sequence stabilises on `filtration R M n`, the
resulting map agrees with `f n` on `filtration R M n` for every `n`. -/
noncomputable def filtrationLimit (f : ℕ → ReducedTensorWords R M →ₗ[R] P) :
    ReducedTensorWords R M →ₗ[R] P :=
  DirectSum.toModule R {n : ℕ // 0 < n} P fun k ↦ f k.1 ∘ₗ of R M k

private theorem filtrationLimit_apply_eq_of_le {f : ℕ → ReducedTensorWords R M →ₗ[R] P}
    (hf : ∀ n, ∀ z ∈ filtration R M n, f (n + 1) z = f n z) {k n : ℕ} (hkn : k ≤ n)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M k) : f n z = f k z := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih => rw [hf n z (filtration_monotone R M hkn hz), ih]

/-- On words of length at most `n`, `filtrationLimit f` agrees with `f n`. -/
theorem filtrationLimit_apply_of_mem_filtration {f : ℕ → ReducedTensorWords R M →ₗ[R] P}
    (hf : ∀ n, ∀ z ∈ filtration R M n, f (n + 1) z = f n z) {n : ℕ}
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    filtrationLimit f z = f n z := by
  have h : filtration R M n ≤ LinearMap.eqLocus (filtrationLimit f) (f n) := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    rw [LinearMap.mem_eqLocus, filtrationLimit, toModule_of, LinearMap.comp_apply,
      filtrationLimit_apply_eq_of_le hf hk (of_mem_filtration R M le_rfl x)]
  exact h hz

/-- If each stage `f n` of a stabilising sequence is homogeneous of degree `p`, so is its
`filtrationLimit`. -/
theorem isHomogeneous_filtrationLimit {R : Type uR} {M : Type uM} {P : Type uP} [CommRing R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid P] [Module R P]
    {G : InternalGrading R M ℤ} {Q : ℤ → Submodule R P} {p : ℤ}
    {f : ℕ → ReducedTensorWords R M →ₗ[R] P}
    (hf : ∀ n, ∀ z ∈ filtration R M n, f (n + 1) z = f n z)
    (hhom : ∀ n, LinearMap.IsHomogeneous (f n) (gradedPiece G) Q p) :
    LinearMap.IsHomogeneous (filtrationLimit f) (gradedPiece G) Q p := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  rw [filtrationLimit_apply_of_mem_filtration hf hn]
  exact (hhom n).map_mem hz

end FiltrationLimit

/-! ### Unfolding words via `prependLetter` -/

section PrependLetter

variable (R : Type uR) (N : Type uN) [CommSemiring R] [AddCommMonoid N] [Module R N]

/-- Prepend the letter component of the left tensor factor to the right tensor factor. -/
noncomputable def prependLetter :
    ReducedTensorWords R N ⊗[R] ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N :=
  TensorProduct.lift ((prepend R N).compl₁₂ (letter R N) LinearMap.id)

variable {R N}

/-- On a pure tensor `u ⊗ v`, `prependLetter` prepends `letter u` to `v`. -/
@[simp]
theorem prependLetter_tmul (u v : ReducedTensorWords R N) :
    prependLetter R N (u ⊗ₜ[R] v) = prepend R N (letter R N u) v := by
  simp [prependLetter]

/-- Words produced by `prependLetter` have length at least two, so their letter component is
zero. -/
@[simp]
theorem letter_comp_prependLetter :
    letter R N ∘ₗ prependLetter R N = 0 :=
  TensorProduct.ext' fun u v ↦ by simp

/-- Evaluating `letter` on `prependLetter` gives zero. -/
@[simp]
theorem letter_prependLetter (W : ReducedTensorWords R N ⊗[R] ReducedTensorWords R N) :
    letter R N (prependLetter R N W) = 0 := by
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun (letter_comp_prependLetter (R := R) (N := N)) W

/-- Every reduced tensor word is the sum of its single-letter part and `prependLetter` applied to
its reduced deconcatenation. -/
theorem ofLetter_letter_add_prependLetter_deconcatenation (z : ReducedTensorWords R N) :
    ofLetter R N (letter R N z) + prependLetter R N (deconcatenation R N z) = z := by
  have hid : coalgHom R (letter R N) = LinearMap.id := by
    simpa only [LinearMap.id_comp, map_id] using coalgHom_comp_letter (LinearMap.id : N →ₗ[R] N)
  have h : ofLetter R N ∘ₗ letter R N +
      prependLetter R N ∘ₗ deconcatenation R N = LinearMap.id := by
    refine linearMap_ext R N fun n x ↦ ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      of_tprod_eq_subword R n.2 x]
    have hsub := coalgHom_subword (letter R N) x 0 n.1
    simp only [hid, LinearMap.id_apply] at hsub
    rw [deconcatenation_subword, sum_Ioo_eq_sum_range _ _
      (by rw [subword_length_zero, TensorProduct.zero_tmul]), map_sum]
    simp only [prependLetter_tmul]
    exact hsub.symm
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun h z

/-- Reduced deconcatenation of `prependLetter`: cutting `prepend (letter u) v` either separates the
leading letter `ofLetter (letter u)` from `v` or cuts inside `v`. -/
theorem deconcatenation_prependLetter
    (W : ReducedTensorWords R N ⊗[R] ReducedTensorWords R N) :
    deconcatenation R N (prependLetter R N W) =
      TensorProduct.map (ofLetter R N ∘ₗ letter R N) LinearMap.id W +
        LinearMap.rTensor (ReducedTensorWords R N) (prependLetter R N)
          ((TensorProduct.assoc R (ReducedTensorWords R N) (ReducedTensorWords R N)
            (ReducedTensorWords R N)).symm
            (LinearMap.lTensor (ReducedTensorWords R N) (deconcatenation R N) W)) := by
  have h : deconcatenation R N ∘ₗ prependLetter R N =
      TensorProduct.map (ofLetter R N ∘ₗ letter R N) LinearMap.id +
        LinearMap.rTensor (ReducedTensorWords R N) (prependLetter R N) ∘ₗ
          (TensorProduct.assoc R (ReducedTensorWords R N) (ReducedTensorWords R N)
            (ReducedTensorWords R N)).symm.toLinearMap ∘ₗ
          LinearMap.lTensor (ReducedTensorWords R N) (deconcatenation R N) := by
    refine TensorProduct.ext' fun u v ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, prependLetter_tmul,
      deconcatenation_prepend, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.lTensor_tmul, LinearEquiv.coe_coe]
    congr 1
    induction deconcatenation R N v using TensorProduct.inductionOn with
    | tmul w₁ w₂ =>
        simp only [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, prependLetter_tmul]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  exact LinearMap.congr_fun h W

end PrependLetter

/-! ### Filtration preservation and second-order co-Leibniz identities -/

section SecondOrder

variable {R : Type uR} {M : Type uM} {N : Type uN} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ}

/-- Every graded coderivation preserves the word-length filtration. -/
theorem IsGradedCoderivation.mem_filtration {q : ℤ}
    {b : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hb : IsGradedCoderivation G q b)
    {n : ℕ} {z : ReducedTensorWords R M} (hz : z ∈ filtration R M n) :
    b z ∈ filtration R M n := by
  have heq : b = gradedCoderiv G (letter R M ∘ₗ b) q :=
    (isGradedCoderivationAlong_id_id_iff.2 hb).eq_of_letter_comp_eq
      (isGradedCoderivationAlong_id_id_iff.2
        (isGradedCoderivation_gradedCoderiv G (letter R M ∘ₗ b) q))
      (letter_comp_gradedCoderiv G (letter R M ∘ₗ b) q).symm
  rw [heq]
  exact gradedCoderiv_mem_filtration G (letter R M ∘ₗ b) q hz

/-- One recursive step of the second-order homotopy operator: cut a word in `Tᶜ(M)`, apply `A` and
`B` to the two halves, and prepend the letter of the left image to the right image. -/
private noncomputable def prependCut
    (A B : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  prependLetter R N ∘ₗ TensorProduct.map A B ∘ₗ deconcatenation R M

private theorem deconcatenation_eq_zero_of_mem_filtration_one {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M 1) : deconcatenation R M z = 0 := by
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M 0 ⟨z, hz, rfl⟩
  rw [← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      have hu : u.1 = 0 := (Submodule.mem_bot R).1 (by simpa only [filtration_zero] using u.2)
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype, hu,
        TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

private theorem prependCut_apply_eq_zero_of_mem_filtration_one
    (A B : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M 1) : prependCut A B z = 0 := by
  rw [prependCut, LinearMap.comp_apply, LinearMap.comp_apply,
    deconcatenation_eq_zero_of_mem_filtration_one hz, map_zero, map_zero]

private theorem prependCut_apply_congr_of_mem_filtration
    {A₁ B₁ A₂ B₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N} {k : ℕ}
    (hA : ∀ u ∈ filtration R M k, A₁ u = A₂ u)
    (hB : ∀ v ∈ filtration R M k, B₁ v = B₂ v)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (k + 1)) :
    prependCut A₁ B₁ z = prependCut A₂ B₂ z := by
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M k ⟨z, hz, rfl⟩
  rw [prependCut, prependCut, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, ← hw]
  congr 1
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
        hA u.1 u.2, hB v.1 v.2]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem isHomogeneous_prependCut {p q : ℤ}
    {A B : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hA : LinearMap.IsHomogeneous A (gradedPiece G) (gradedPiece H) p)
    (hB : LinearMap.IsHomogeneous B (gradedPiece G) (gradedPiece H) q) :
    LinearMap.IsHomogeneous (prependCut A B) (gradedPiece G) (gradedPiece H) (p + q) := by
  have hAl : LinearMap.IsHomogeneous (letter R N ∘ₗ A) (gradedPiece G) H.piece p := by
    simpa only [add_zero] using (isHomogeneous_letter H).comp hA
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  refine gradedPiece_induction
    (motive := fun w ↦ prependCut A B w ∈ gradedPiece H (D + (p + q))) hz ?_
    (fun _ _ _ _ hu hv ↦ by rw [map_add]; exact add_mem hu hv)
    (fun c _ _ hu ↦ by rw [map_smul]; exact Submodule.smul_mem _ c hu)
  intro n hn 𝒟 x hx hD
  set g : ℕ → ℤ := fun k ↦ if h : k < n then 𝒟 ⟨k, h⟩ else 0 with hg
  have hxg : ∀ i : Fin n, x i ∈ G.piece (g i) := fun i ↦ by simpa [hg] using hx i
  have hsum : ∑ j ∈ Finset.range n, g (0 + j) = D := by
    rw [← hD, ← Fin.sum_univ_eq_sum_range (fun j ↦ g (0 + j)) n]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [hg]
  rw [prependCut, LinearMap.comp_apply, LinearMap.comp_apply, of_tprod_eq_subword R hn x,
    deconcatenation_subword, map_sum, map_sum]
  refine Submodule.sum_mem _ fun c hc ↦ ?_
  rw [Finset.mem_Ioo] at hc
  simp only [TensorProduct.map_tmul, prependLetter_tmul, ← LinearMap.comp_apply (letter R N)]
  have hsplit : D + (p + q) =
      ((∑ j ∈ Finset.range c, g (0 + j)) + p) +
        ((∑ j ∈ Finset.range (n - c), g (c + j)) + q) := by
    rw [← hsum, ← Nat.add_sub_cancel' hc.2.le, Finset.sum_range_add, Nat.add_sub_cancel_left]
    simp only [Nat.zero_add]; ring
  rw [hsplit]
  exact prepend_mem_gradedPiece
    (hAl.map_mem (subword_mem_gradedPiece x g hxg 0 c))
    (hB.map_mem (by simpa only [Nat.zero_add] using subword_mem_gradedPiece x g hxg c (n - c)))

private theorem map_koszulTwist_comp_self (G : InternalGrading R M ℤ) (q : ℤ) :
    ReducedTensorWords.map (R := R) (G.koszulTwist q) ∘ₗ
      ReducedTensorWords.map (R := R) (G.koszulTwist q) = LinearMap.id := by
  rw [← ReducedTensorWords.map_comp, InternalGrading.koszulTwist_comp_self,
    ReducedTensorWords.map_id]

private theorem deconcatenation_comp_koszulTwist_apply
    {F F' H₁ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hH₁ : IsGradedCoderivationAlong G 1 F F' H₁) (w : ReducedTensorWords R M) :
    deconcatenation R N (H₁ (ReducedTensorWords.map (R := R) (G.koszulTwist 1) w)) =
      TensorProduct.map (H₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1))
          (F' ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) (deconcatenation R M w) +
        TensorProduct.map F (H₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1))
          (deconcatenation R M w) := by
  rw [hH₁.deconcatenation_apply, (isCoalgHom_map (G.koszulTwist 1)).deconcatenation_apply]
  have hττ : ∀ u, ReducedTensorWords.map (R := R) (G.koszulTwist 1)
      (ReducedTensorWords.map (R := R) (G.koszulTwist 1) u) = u := fun u ↦ by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun (map_koszulTwist_comp_self G 1) u
  induction deconcatenation R M w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply, hττ]
  | add x y hx hy =>
      simp only [map_add] at hx hy ⊢
      rw [add_add_add_comm, hx, hy, add_add_add_comm]

private theorem rTensor_prependLetter_assoc_symm_map
    (X Y Z : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N)
    (T : (ReducedTensorWords R M ⊗[R] ReducedTensorWords R M) ⊗[R] ReducedTensorWords R M) :
    LinearMap.rTensor (ReducedTensorWords R N) (prependLetter R N)
        ((TensorProduct.assoc R (ReducedTensorWords R N) (ReducedTensorWords R N)
          (ReducedTensorWords R N)).symm
          (TensorProduct.map X (TensorProduct.map Y Z)
            (TensorProduct.assoc R (ReducedTensorWords R M) (ReducedTensorWords R M)
              (ReducedTensorWords R M) T))) =
      TensorProduct.map (prependLetter R N ∘ₗ TensorProduct.map X Y) Z T := by
  have h : LinearMap.rTensor (ReducedTensorWords R N) (prependLetter R N) ∘ₗ
      (TensorProduct.assoc R (ReducedTensorWords R N) (ReducedTensorWords R N)
        (ReducedTensorWords R N)).symm.toLinearMap ∘ₗ
      TensorProduct.map X (TensorProduct.map Y Z) ∘ₗ
      (TensorProduct.assoc R (ReducedTensorWords R M) (ReducedTensorWords R M)
        (ReducedTensorWords R M)).toLinearMap =
      TensorProduct.map (prependLetter R N ∘ₗ TensorProduct.map X Y) Z :=
    TensorProduct.ext_threefold fun u v w ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_tmul,
        TensorProduct.map_tmul, TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul]
  exact LinearMap.congr_fun h T

/-- When `b_M² = 0` and `b_N² = 0`, any graded commutator `b_N ∘ Φ - Φ ∘ b_M` is killed by
`b_N ∘ (·) + (·) ∘ b_M`. -/
private theorem comp_add_comp_commutator_eq_zero
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    (hbM_sq : bM ∘ₗ bM = 0) (hbN_sq : bN ∘ₗ bN = 0)
    (Φ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    bN ∘ₗ (bN ∘ₗ Φ - Φ ∘ₗ bM) + (bN ∘ₗ Φ - Φ ∘ₗ bM) ∘ₗ bM = 0 := by
  refine LinearMap.ext fun z ↦ ?_
  have hbMz : bM (bM z) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using LinearMap.congr_fun hbM_sq z
  have hbNz : bN (bN (Φ z)) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using LinearMap.congr_fun hbN_sq (Φ z)
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    map_sub, hbMz, hbNz, map_zero]
  abel

private theorem lTensor_deconcatenation_map_eq_of_filtration
    {A B : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    {T : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M →ₗ[R]
      ReducedTensorWords R N ⊗[R] ReducedTensorWords R N} {n : ℕ}
    (hB : ∀ v ∈ filtration R M n, deconcatenation R N (B v) = T (deconcatenation R M v))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    LinearMap.lTensor (ReducedTensorWords R N) (deconcatenation R N)
      (TensorProduct.map A B (deconcatenation R M z)) =
      TensorProduct.map A T
        (LinearMap.lTensor (ReducedTensorWords R M) (deconcatenation R M)
          (deconcatenation R M z)) := by
  obtain ⟨w, hw⟩ := map_deconcatenation_filtration_succ_le R M n ⟨z, hz, rfl⟩
  rw [← hw]; clear hw
  induction w using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
        LinearMap.lTensor_tmul, hB v.1 v.2]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Inductive step for the second-order co-Leibniz identity: if `Φ` satisfies the fixed-point
equation `Φ = prependCut (H₁ ∘ τ_M) H₂ + prependCut F Φ`, and both `H₂` and `Φ` satisfy their
co-Leibniz rules on `filtration R M n`, then `Φ` satisfies its second-order co-Leibniz rule on
`filtration R M (n + 1)`. -/
private theorem deconcatenation_secondOrder_of_mem_filtration
    {F F' F'' H₁ H₂ Φ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hH₁ : IsGradedCoderivationAlong G 1 F F' H₁)
    (hfix : Φ = prependCut (H₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) H₂ +
      prependCut F Φ) {n : ℕ}
    (hH₂ : ∀ v ∈ filtration R M n, deconcatenation R N (H₂ v) =
      (TensorProduct.map H₂ F'' +
        TensorProduct.map (F' ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) H₂)
          (deconcatenation R M v))
    (hΦ : ∀ v ∈ filtration R M n, deconcatenation R N (Φ v) =
      (TensorProduct.map Φ F'' +
        TensorProduct.map (H₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) H₂ +
        TensorProduct.map F Φ) (deconcatenation R M v))
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M (n + 1)) :
    deconcatenation R N (Φ z) =
      (TensorProduct.map Φ F'' +
        TensorProduct.map (H₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) H₂ +
        TensorProduct.map F Φ) (deconcatenation R M z) := by
  set τ := ReducedTensorWords.map (R := R) (G.koszulTwist 1)
  set A := H₁ ∘ₗ τ
  have hcoassoc := LinearMap.congr_fun (deconcatenation_coassoc R M).symm z
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hcoassoc
  have hΦz : Φ z = prependCut A H₂ z + prependCut F Φ z := by
    simpa only [LinearMap.add_apply] using LinearMap.congr_fun hfix z
  rw [hΦz, map_add, prependCut, prependCut, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, deconcatenation_prependLetter,
    deconcatenation_prependLetter, lTensor_deconcatenation_map_eq_of_filtration hH₂ hz,
    lTensor_deconcatenation_map_eq_of_filtration hΦ hz, hcoassoc]
  simp only [TensorProduct.map_add_right, LinearMap.add_apply, map_add,
    rTensor_prependLetter_assoc_symm_map]
  induction deconcatenation R M z using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.comp_apply,
        LinearMap.id_apply]
      have hFu : ofLetter R N (letter R N (F u)) +
          prependLetter R N (TensorProduct.map F F (deconcatenation R M u)) = F u := by
        rw [← hF.deconcatenation_apply, ofLetter_letter_add_prependLetter_deconcatenation]
      have hAu : ofLetter R N (letter R N (A u)) +
          (prependLetter R N (TensorProduct.map A (F' ∘ₗ τ) (deconcatenation R M u)) +
            prependLetter R N (TensorProduct.map F A (deconcatenation R M u))) = A u := by
        rw [← map_add, ← deconcatenation_comp_koszulTwist_apply hH₁ u]
        exact ofLetter_letter_add_prependLetter_deconcatenation (A u)
      have hΦu : prependLetter R N (TensorProduct.map A H₂ (deconcatenation R M u)) +
          prependLetter R N (TensorProduct.map F Φ (deconcatenation R M u)) = Φ u :=
        (LinearMap.congr_fun hfix u).symm
      conv_rhs => rw [← hFu, ← hAu, ← hΦu]
      simp only [TensorProduct.add_tmul]
      abel
  | add x y hx hy =>
      simp only [map_add] at hx hy ⊢
      convert congrArg₂ (· + ·) hx hy using 1 <;> abel

/-- Algebraic commutator calculation for a degree-`(-2)` map `Φ` satisfying the second-order
co-Leibniz identity at `z` and `b_M z`: the co-Leibniz defect of `b_N ∘ Φ - Φ ∘ b_M` produces the
exact mismatch terms `((F - F') ∘ τ_M) ⊗ H₂ + (-H₁) ⊗ (F' - F'')`. -/
private theorem deconcatenation_commutator_secondOrder
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    {F F' F'' H₁ H₂ Φ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G 1 bM)
    (hbM_hom : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    (hbN : IsGradedCoderivation H 1 bN)
    (hF_hom : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF_int : bN ∘ₗ F = F ∘ₗ bM) (hF''_int : bN ∘ₗ F'' = F'' ∘ₗ bM)
    (hH₁_hom : LinearMap.IsHomogeneous H₁ (gradedPiece G) (gradedPiece H) (-1))
    (hH₁_eq : F - F' = bN ∘ₗ H₁ + H₁ ∘ₗ bM)
    (hH₂_eq : F' - F'' = bN ∘ₗ H₂ + H₂ ∘ₗ bM)
    (hΦ_hom : LinearMap.IsHomogeneous Φ (gradedPiece G) (gradedPiece H) (-2))
    {z : ReducedTensorWords R M}
    (hΦz : deconcatenation R N (Φ z) =
      (TensorProduct.map Φ F'' +
        TensorProduct.map (H₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) H₂ +
        TensorProduct.map F Φ) (deconcatenation R M z))
    (hΦbz : deconcatenation R N (Φ (bM z)) =
      (TensorProduct.map Φ F'' +
        TensorProduct.map (H₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) H₂ +
        TensorProduct.map F Φ) (deconcatenation R M (bM z))) :
    deconcatenation R N ((bN ∘ₗ Φ - Φ ∘ₗ bM) z) =
      (TensorProduct.map (bN ∘ₗ Φ - Φ ∘ₗ bM) F'' +
        TensorProduct.map (F ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1))
          (bN ∘ₗ Φ - Φ ∘ₗ bM) +
        TensorProduct.map ((F - F') ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) H₂ +
        TensorProduct.map (-H₁) (F' - F'')) (deconcatenation R M z) := by
  have hτF : ∀ u, ReducedTensorWords.map (R := R) (H.koszulTwist 1) (F u) =
      F (ReducedTensorWords.map (R := R) (G.koszulTwist 1) u) := fun u ↦ by
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using LinearMap.congr_fun (hF_hom.map_koszulTwist_comp 1) u
  have hτΦ : ∀ u, ReducedTensorWords.map (R := R) (H.koszulTwist 1) (Φ u) =
      Φ (ReducedTensorWords.map (R := R) (G.koszulTwist 1) u) := fun u ↦ by
    simpa only [show (1 : ℤ) * (-2) = -(2 * 1) by ring, Int.negOnePow_neg, Int.negOnePow_two_mul,
      Units.val_one, Int.cast_one, one_smul, LinearMap.comp_apply] using
      LinearMap.congr_fun (hΦ_hom.map_koszulTwist_comp 1) u
  have hτH₁ : ∀ u, ReducedTensorWords.map (R := R) (H.koszulTwist 1)
      (H₁ (ReducedTensorWords.map (R := R) (G.koszulTwist 1) u)) = -H₁ u := fun u ↦ by
    have h1 := LinearMap.congr_fun (hH₁_hom.map_koszulTwist_comp 1)
      (ReducedTensorWords.map (R := R) (G.koszulTwist 1) u)
    have h2 := LinearMap.congr_fun (map_koszulTwist_comp_self G 1) u
    simp only [mul_neg, mul_one, Int.negOnePow_neg, Int.negOnePow_one, Units.val_neg, Units.val_one,
      Int.cast_neg, Int.cast_one, neg_one_smul, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at h1 h2
    rw [h1, h2]
  have hτbM : ∀ u, ReducedTensorWords.map (R := R) (G.koszulTwist 1) (bM u) =
      -bM (ReducedTensorWords.map (R := R) (G.koszulTwist 1) u) := fun u ↦ by
    have h := LinearMap.congr_fun hbM_hom.anticommute_map_koszulTwist_one u
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at h
    exact eq_neg_of_add_eq_zero_right h
  have hττ : ∀ u, ReducedTensorWords.map (R := R) (G.koszulTwist 1)
      (ReducedTensorWords.map (R := R) (G.koszulTwist 1) u) = u := fun u ↦ by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun (map_koszulTwist_comp_self G 1) u
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_sub,
    (isGradedCoderivationAlong_id_id_iff.2 hbN).deconcatenation_apply, hΦz, hΦbz,
    (isGradedCoderivationAlong_id_id_iff.2 hbM).deconcatenation_apply]
  induction deconcatenation R M z using TensorProduct.inductionOn with
  | tmul u v =>
      have hFu : bN (F u) = F (bM u) := by
        simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hF_int u
      have hF''v : bN (F'' v) = F'' (bM v) := by
        simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hF''_int v
      rw [hH₁_eq, hH₂_eq]
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
        TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.id_apply, LinearMap.comp_apply,
        map_add, hτF, hτΦ, hτH₁, hτbM, hττ, hFu, hF''v, map_neg]
      simp only [TensorProduct.neg_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_sub,
        TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel
  | add x y hx hy =>
      simp only [map_add] at hx hy ⊢
      convert congrArg₂ (· + ·) hx hy using 1; abel

/-! ### Transitivity of coalgebra homotopies -/

/-- Recursive stages of the degree-`(-2)` correction `Φ` for transitivity of coalgebra
homotopies. -/
private noncomputable def transSecondOrderSeq (G : InternalGrading R M ℤ)
    (F H₁ H₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ℕ → ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N
  | 0 => 0
  | k + 1 =>
      prependCut (H₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) H₂ +
        prependCut F (transSecondOrderSeq G F H₁ H₂ k)

private theorem transSecondOrderSeq_stabilises (G : InternalGrading R M ℤ)
    (F H₁ H₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ∀ k, ∀ z ∈ filtration R M (k + 1),
      transSecondOrderSeq G F H₁ H₂ (k + 1) z = transSecondOrderSeq G F H₁ H₂ k z := by
  intro k
  induction k with
  | zero =>
      intro z hz
      simp only [transSecondOrderSeq, LinearMap.add_apply, LinearMap.zero_apply,
        prependCut_apply_eq_zero_of_mem_filtration_one _ _ hz, add_zero]
  | succ m ih =>
      intro z hz
      simp only [transSecondOrderSeq, LinearMap.add_apply]
      congr 1
      exact prependCut_apply_congr_of_mem_filtration (fun _ _ ↦ rfl) ih hz

private theorem transSecondOrderSeq_stabilises_filtration (G : InternalGrading R M ℤ)
    (F H₁ H₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) (k : ℕ)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M k) :
    transSecondOrderSeq G F H₁ H₂ (k + 1) z = transSecondOrderSeq G F H₁ H₂ k z :=
  transSecondOrderSeq_stabilises G F H₁ H₂ k z (filtration_monotone R M k.le_succ hz)

/-- The composite coalgebra homotopy from `F` to `F''` built from a coalgebra homotopy `H₁` from
`F` to `F'` and a coalgebra homotopy `H₂` from `F'` to `F''`: the sum `H₁ + H₂` corrected by the
commutator `b_N ∘ Φ - Φ ∘ b_M` with the recursively constructed degree-`(-2)` map `Φ`. -/
noncomputable def gradedCoderivAlongTrans (G : InternalGrading R M ℤ)
    (bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N)
    (F H₁ H₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  let Φ := filtrationLimit (transSecondOrderSeq G F H₁ H₂)
  H₁ + H₂ + (bN ∘ₗ Φ - Φ ∘ₗ bM)

private theorem filtrationLimit_transSecondOrderSeq_fixedPoint (G : InternalGrading R M ℤ)
    (F H₁ H₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    filtrationLimit (transSecondOrderSeq G F H₁ H₂) =
      prependCut (H₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) H₂ +
        prependCut F (filtrationLimit (transSecondOrderSeq G F H₁ H₂)) := by
  have hstab := transSecondOrderSeq_stabilises_filtration G F H₁ H₂
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨k, hk⟩ := exists_mem_filtration R M z
  have hk1 : z ∈ filtration R M (k + 1) := filtration_monotone R M k.le_succ hk
  rw [filtrationLimit_apply_of_mem_filtration hstab hk1, transSecondOrderSeq]
  simp only [LinearMap.add_apply]
  congr 1
  exact prependCut_apply_congr_of_mem_filtration (fun _ _ ↦ rfl)
    (fun v hv ↦ (filtrationLimit_apply_of_mem_filtration hstab hv).symm) hk1

private theorem deconcatenation_filtrationLimit_transSecondOrderSeq
    {F F' F'' H₁ H₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : IsCoalgHom R F) (hH₁ : IsGradedCoderivationAlong G 1 F F' H₁)
    (hH₂ : IsGradedCoderivationAlong G 1 F' F'' H₂) (z : ReducedTensorWords R M) :
    deconcatenation R N (filtrationLimit (transSecondOrderSeq G F H₁ H₂) z) =
      (TensorProduct.map (filtrationLimit (transSecondOrderSeq G F H₁ H₂)) F'' +
        TensorProduct.map (H₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) H₂ +
        TensorProduct.map F (filtrationLimit (transSecondOrderSeq G F H₁ H₂)))
        (deconcatenation R M z) := by
  have hH₂' : ∀ v, deconcatenation R N (H₂ v) =
      (TensorProduct.map H₂ F'' +
        TensorProduct.map (F' ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) H₂)
          (deconcatenation R M v) := fun v ↦ by
    rw [hH₂.deconcatenation_apply, LinearMap.add_apply]
    congr 1
    induction deconcatenation R M v using TensorProduct.inductionOn with
    | tmul x y => simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.comp_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have key : ∀ n, ∀ w ∈ filtration R M n,
      deconcatenation R N (filtrationLimit (transSecondOrderSeq G F H₁ H₂) w) =
        (TensorProduct.map (filtrationLimit (transSecondOrderSeq G F H₁ H₂)) F'' +
          TensorProduct.map (H₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) H₂ +
          TensorProduct.map F (filtrationLimit (transSecondOrderSeq G F H₁ H₂)))
          (deconcatenation R M w) := by
    intro n
    induction n with
    | zero =>
        intro w hw
        rw [filtration_zero] at hw
        simp only [(Submodule.mem_bot R).1 hw, map_zero]
    | succ n ih =>
        intro w hw
        exact deconcatenation_secondOrder_of_mem_filtration hF hH₁
          (filtrationLimit_transSecondOrderSeq_fixedPoint G F H₁ H₂) (fun v _ ↦ hH₂' v) ih hw
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  exact key n z hn

private theorem isHomogeneous_filtrationLimit_transSecondOrderSeq
    {F H₁ H₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hH₁ : LinearMap.IsHomogeneous H₁ (gradedPiece G) (gradedPiece H) (-1))
    (hH₂ : LinearMap.IsHomogeneous H₂ (gradedPiece G) (gradedPiece H) (-1)) :
    LinearMap.IsHomogeneous (filtrationLimit (transSecondOrderSeq G F H₁ H₂))
      (gradedPiece G) (gradedPiece H) (-2) := by
  refine isHomogeneous_filtrationLimit (transSecondOrderSeq_stabilises_filtration G F H₁ H₂)
    fun k ↦ ?_
  induction k with
  | zero => exact LinearMap.isHomogeneous_zero _ _ _
  | succ k ih =>
      rw [transSecondOrderSeq]
      have hA : LinearMap.IsHomogeneous
          (H₁ ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1))
          (gradedPiece G) (gradedPiece H) (-1) := by
        simpa only [zero_add] using hH₁.comp (isHomogeneous_map_koszulTwist G 1)
      refine LinearMap.IsHomogeneous.add ?_ ?_
      · simpa only [show (-1 : ℤ) + (-1) = -2 by ring] using isHomogeneous_prependCut hA hH₂
      · simpa only [zero_add] using isHomogeneous_prependCut hF ih

/-- If `H₁` and `H₂` have degree `-1`, `F` has degree `0`, and `b_M`, `b_N` have degree `1`, then
`gradedCoderivAlongTrans G bM bN F H₁ H₂` has degree `-1`. -/
theorem isHomogeneous_gradedCoderivAlongTrans
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    {F H₁ H₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hbM : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    (hbN : LinearMap.IsHomogeneous bN (gradedPiece H) (gradedPiece H) 1)
    (hF : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hH₁ : LinearMap.IsHomogeneous H₁ (gradedPiece G) (gradedPiece H) (-1))
    (hH₂ : LinearMap.IsHomogeneous H₂ (gradedPiece G) (gradedPiece H) (-1)) :
    LinearMap.IsHomogeneous (gradedCoderivAlongTrans G bM bN F H₁ H₂)
      (gradedPiece G) (gradedPiece H) (-1) := by
  have hΦ := isHomogeneous_filtrationLimit_transSecondOrderSeq hF hH₁ hH₂
  have hbNΦ : LinearMap.IsHomogeneous
      (bN ∘ₗ filtrationLimit (transSecondOrderSeq G F H₁ H₂))
      (gradedPiece G) (gradedPiece H) (-1) := by
    simpa only [show (-2 : ℤ) + 1 = -1 by ring] using hbN.comp hΦ
  have hΦbM : LinearMap.IsHomogeneous
      (filtrationLimit (transSecondOrderSeq G F H₁ H₂) ∘ₗ bM)
      (gradedPiece G) (gradedPiece H) (-1) := by
    simpa only [show (1 : ℤ) + (-2) = -1 by ring] using hΦ.comp hbM
  exact (hH₁.add hH₂).add (hbNΦ.sub hΦbM)

/-- The composite coalgebra homotopy `gradedCoderivAlongTrans` is a coderivation along `F` and
`F''` at twist parameter one. -/
theorem isGradedCoderivationAlong_gradedCoderivAlongTrans
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    {F F' F'' H₁ H₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G 1 bM)
    (hbM_hom : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    (hbN : IsGradedCoderivation H 1 bN)
    (hF : IsCoalgHom R F) (hF_hom : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF_int : bN ∘ₗ F = F ∘ₗ bM) (hF''_int : bN ∘ₗ F'' = F'' ∘ₗ bM)
    (hH₁ : IsGradedCoderivationAlong G 1 F F' H₁)
    (hH₁_hom : LinearMap.IsHomogeneous H₁ (gradedPiece G) (gradedPiece H) (-1))
    (hH₁_eq : F - F' = bN ∘ₗ H₁ + H₁ ∘ₗ bM)
    (hH₂ : IsGradedCoderivationAlong G 1 F' F'' H₂)
    (hH₂_hom : LinearMap.IsHomogeneous H₂ (gradedPiece G) (gradedPiece H) (-1))
    (hH₂_eq : F' - F'' = bN ∘ₗ H₂ + H₂ ∘ₗ bM) :
    IsGradedCoderivationAlong G 1 F F'' (gradedCoderivAlongTrans G bM bN F H₁ H₂) := by
  rw [isGradedCoderivationAlong_iff]
  refine LinearMap.ext fun z ↦ ?_
  have hΨ := deconcatenation_commutator_secondOrder hbM hbM_hom hbN hF_hom hF_int hF''_int
    hH₁_hom hH₁_eq hH₂_eq (isHomogeneous_filtrationLimit_transSecondOrderSeq hF_hom hH₁_hom hH₂_hom)
    (deconcatenation_filtrationLimit_transSecondOrderSeq hF hH₁ hH₂ z)
    (deconcatenation_filtrationLimit_transSecondOrderSeq hF hH₁ hH₂ (bM z))
  simp only [gradedCoderivAlongTrans, LinearMap.comp_apply, LinearMap.add_apply]
  rw [map_add, map_add, hH₁.deconcatenation_apply, hH₂.deconcatenation_apply, hΨ]
  induction deconcatenation R M z using TensorProduct.inductionOn with
  | tmul u v =>
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
        TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply,
        TensorProduct.add_tmul, TensorProduct.sub_tmul, TensorProduct.neg_tmul,
        TensorProduct.tmul_add, TensorProduct.tmul_sub]
      abel
  | add x y hx hy =>
      simp only [map_add] at hx hy ⊢
      convert congrArg₂ (· + ·) hx hy using 1 <;> abel

/-- When `b_M² = 0` and `b_N² = 0`, `gradedCoderivAlongTrans` satisfies the homotopy equation
`F - F'' = b_N ∘ D + D ∘ b_M`. -/
theorem sub_eq_comp_add_comp_gradedCoderivAlongTrans
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    {F F' F'' H₁ H₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hbM_sq : bM ∘ₗ bM = 0) (hbN_sq : bN ∘ₗ bN = 0)
    (hH₁_eq : F - F' = bN ∘ₗ H₁ + H₁ ∘ₗ bM) (hH₂_eq : F' - F'' = bN ∘ₗ H₂ + H₂ ∘ₗ bM) :
    F - F'' = bN ∘ₗ gradedCoderivAlongTrans G bM bN F H₁ H₂ +
      gradedCoderivAlongTrans G bM bN F H₁ H₂ ∘ₗ bM := by
  set Φ := filtrationLimit (transSecondOrderSeq G F H₁ H₂)
  rw [gradedCoderivAlongTrans, LinearMap.comp_add, LinearMap.comp_add, LinearMap.add_comp,
    LinearMap.add_comp, show (bN ∘ₗ H₁ + bN ∘ₗ H₂ + bN ∘ₗ (bN ∘ₗ Φ - Φ ∘ₗ bM)) +
      (H₁ ∘ₗ bM + H₂ ∘ₗ bM + (bN ∘ₗ Φ - Φ ∘ₗ bM) ∘ₗ bM) =
      (bN ∘ₗ H₁ + H₁ ∘ₗ bM) + (bN ∘ₗ H₂ + H₂ ∘ₗ bM) +
        (bN ∘ₗ (bN ∘ₗ Φ - Φ ∘ₗ bM) + (bN ∘ₗ Φ - Φ ∘ₗ bM) ∘ₗ bM) by abel,
    comp_add_comp_commutator_eq_zero hbM_sq hbN_sq Φ, add_zero, ← hH₁_eq, ← hH₂_eq]
  abel

/-- On single letters, the second-order correction in `gradedCoderivAlongTrans` vanishes, so the
composite homotopy acts simply as `H₁ + H₂`. -/
@[simp]
theorem gradedCoderivAlongTrans_comp_ofLetter
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    {F H₁ H₂ : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G 1 bM) :
    gradedCoderivAlongTrans G bM bN F H₁ H₂ ∘ₗ ofLetter R M =
      (H₁ + H₂) ∘ₗ ofLetter R M := by
  have hstab := transSecondOrderSeq_stabilises_filtration G F H₁ H₂
  have hΦ₁ : ∀ w ∈ filtration R M 1,
      filtrationLimit (transSecondOrderSeq G F H₁ H₂) w = 0 := fun w hw ↦ by
    rw [filtrationLimit_apply_of_mem_filtration hstab hw,
      transSecondOrderSeq_stabilises G F H₁ H₂ 0 w hw, transSecondOrderSeq, LinearMap.zero_apply]
  refine LinearMap.ext fun a ↦ ?_
  have ha : ofLetter R M a ∈ filtration R M 1 := ofLetter_mem_filtration R M a
  simp only [gradedCoderivAlongTrans, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.sub_apply, hΦ₁ _ ha, hΦ₁ _ (hbM.mem_filtration ha), map_zero, sub_self, add_zero]

/-! ### Symmetry of coalgebra homotopies -/

/-- Recursive stages of the degree-`(-2)` correction `Φ` for symmetry of coalgebra homotopies. -/
private noncomputable def symmSecondOrderSeq (G : InternalGrading R M ℤ)
    (bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N)
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ℕ → ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N
  | 0 => 0
  | k + 1 =>
      prependCut (D ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1))
          (-D - (bN ∘ₗ symmSecondOrderSeq G bM bN F D k -
            symmSecondOrderSeq G bM bN F D k ∘ₗ bM)) +
        prependCut F (symmSecondOrderSeq G bM bN F D k)

private theorem symmSecondOrderSeq_stabilises
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hbM : IsGradedCoderivation G 1 bM)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N)
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ∀ k, ∀ z ∈ filtration R M (k + 1),
      symmSecondOrderSeq G bM bN F D (k + 1) z = symmSecondOrderSeq G bM bN F D k z := by
  intro k
  induction k with
  | zero =>
      intro z hz
      simp only [symmSecondOrderSeq, LinearMap.add_apply, LinearMap.zero_apply,
        prependCut_apply_eq_zero_of_mem_filtration_one _ _ hz, add_zero]
  | succ m ih =>
      intro z hz
      conv_lhs => rw [symmSecondOrderSeq]
      conv_rhs => rw [symmSecondOrderSeq]
      simp only [LinearMap.add_apply]
      refine congrArg₂ (· + ·) ?_ (prependCut_apply_congr_of_mem_filtration (fun _ _ ↦ rfl) ih hz)
      refine prependCut_apply_congr_of_mem_filtration (fun _ _ ↦ rfl) (fun v hv ↦ ?_) hz
      simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply,
        ih v hv, ih (bM v) (hbM.mem_filtration hv)]

private theorem symmSecondOrderSeq_stabilises_filtration
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hbM : IsGradedCoderivation G 1 bM)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N)
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) (k : ℕ)
    {z : ReducedTensorWords R M} (hz : z ∈ filtration R M k) :
    symmSecondOrderSeq G bM bN F D (k + 1) z = symmSecondOrderSeq G bM bN F D k z :=
  symmSecondOrderSeq_stabilises hbM bN F D k z (filtration_monotone R M k.le_succ hz)

/-- The inverse coalgebra homotopy from `F'` to `F` built from a coalgebra homotopy `D` from `F`
to `F'`: `-D` corrected by `-(b_N ∘ Φ - Φ ∘ b_M)` for the recursively constructed degree-`(-2)`
map `Φ`. -/
noncomputable def gradedCoderivAlongSymm (G : InternalGrading R M ℤ)
    (bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N)
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N :=
  -D - (bN ∘ₗ filtrationLimit (symmSecondOrderSeq G bM bN F D) -
    filtrationLimit (symmSecondOrderSeq G bM bN F D) ∘ₗ bM)

private theorem filtrationLimit_symmSecondOrderSeq_fixedPoint
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hbM : IsGradedCoderivation G 1 bM)
    (bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N)
    (F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N) :
    filtrationLimit (symmSecondOrderSeq G bM bN F D) =
      prependCut (D ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1))
          (gradedCoderivAlongSymm G bM bN F D) +
        prependCut F (filtrationLimit (symmSecondOrderSeq G bM bN F D)) := by
  have hstab := symmSecondOrderSeq_stabilises_filtration hbM bN F D
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨k, hk⟩ := exists_mem_filtration R M z
  have hk1 : z ∈ filtration R M (k + 1) := filtration_monotone R M k.le_succ hk
  rw [filtrationLimit_apply_of_mem_filtration hstab hk1, symmSecondOrderSeq]
  simp only [LinearMap.add_apply]
  refine congrArg₂ (· + ·) ?_
    (prependCut_apply_congr_of_mem_filtration (fun _ _ ↦ rfl)
      (fun v hv ↦ (filtrationLimit_apply_of_mem_filtration hstab hv).symm) hk1)
  refine prependCut_apply_congr_of_mem_filtration (fun _ _ ↦ rfl) (fun v hv ↦ ?_) hk1
  simp only [gradedCoderivAlongSymm, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, filtrationLimit_apply_of_mem_filtration hstab hv,
    filtrationLimit_apply_of_mem_filtration hstab (hbM.mem_filtration hv)]

private theorem isHomogeneous_filtrationLimit_symmSecondOrderSeq
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hbM : IsGradedCoderivation G 1 bM)
    (hbM_hom : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    {F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hbN_hom : LinearMap.IsHomogeneous bN (gradedPiece H) (gradedPiece H) 1)
    (hF_hom : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hD_hom : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) (-1)) :
    LinearMap.IsHomogeneous (filtrationLimit (symmSecondOrderSeq G bM bN F D))
      (gradedPiece G) (gradedPiece H) (-2) := by
  have hA : LinearMap.IsHomogeneous
      (D ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1))
      (gradedPiece G) (gradedPiece H) (-1) := by
    simpa only [zero_add] using hD_hom.comp (isHomogeneous_map_koszulTwist G 1)
  refine isHomogeneous_filtrationLimit (symmSecondOrderSeq_stabilises_filtration hbM bN F D)
    fun k ↦ ?_
  induction k with
  | zero => exact LinearMap.isHomogeneous_zero _ _ _
  | succ k ih =>
      rw [symmSecondOrderSeq]
      have hbNΦ : LinearMap.IsHomogeneous
          (bN ∘ₗ symmSecondOrderSeq G bM bN F D k) (gradedPiece G) (gradedPiece H) (-1) := by
        simpa only [show (-2 : ℤ) + 1 = -1 by ring] using hbN_hom.comp ih
      have hΦbM : LinearMap.IsHomogeneous
          (symmSecondOrderSeq G bM bN F D k ∘ₗ bM) (gradedPiece G) (gradedPiece H) (-1) := by
        simpa only [show (1 : ℤ) + (-2) = -1 by ring] using ih.comp hbM_hom
      have hB : LinearMap.IsHomogeneous
          (-D - (bN ∘ₗ symmSecondOrderSeq G bM bN F D k -
            symmSecondOrderSeq G bM bN F D k ∘ₗ bM))
          (gradedPiece G) (gradedPiece H) (-1) :=
        hD_hom.neg.sub (hbNΦ.sub hΦbM)
      refine LinearMap.IsHomogeneous.add ?_ ?_
      · simpa only [show (-1 : ℤ) + (-1) = -2 by ring] using isHomogeneous_prependCut hA hB
      · simpa only [zero_add] using isHomogeneous_prependCut hF_hom ih

/-- If `D` has degree `-1`, `F` has degree `0`, and `b_M`, `b_N` have degree `1`, then
`gradedCoderivAlongSymm G bM bN F D` has degree `-1`. -/
theorem isHomogeneous_gradedCoderivAlongSymm
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M} (hbM : IsGradedCoderivation G 1 bM)
    (hbM_hom : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1)
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    {F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hbN_hom : LinearMap.IsHomogeneous bN (gradedPiece H) (gradedPiece H) 1)
    (hF_hom : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hD_hom : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) (-1)) :
    LinearMap.IsHomogeneous (gradedCoderivAlongSymm G bM bN F D)
      (gradedPiece G) (gradedPiece H) (-1) := by
  have hΦ := isHomogeneous_filtrationLimit_symmSecondOrderSeq hbM hbM_hom hbN_hom hF_hom hD_hom
  have hbNΦ : LinearMap.IsHomogeneous
      (bN ∘ₗ filtrationLimit (symmSecondOrderSeq G bM bN F D))
      (gradedPiece G) (gradedPiece H) (-1) := by
    simpa only [show (-2 : ℤ) + 1 = -1 by ring] using hbN_hom.comp hΦ
  have hΦbM : LinearMap.IsHomogeneous
      (filtrationLimit (symmSecondOrderSeq G bM bN F D) ∘ₗ bM)
      (gradedPiece G) (gradedPiece H) (-1) := by
    simpa only [show (1 : ℤ) + (-2) = -1 by ring] using hΦ.comp hbM_hom
  exact hD_hom.neg.sub (hbNΦ.sub hΦbM)

/-- When `b_M² = 0` and `b_N² = 0`, `gradedCoderivAlongSymm` satisfies the reversed homotopy
equation `F' - F = b_N ∘ D' + D' ∘ b_M`. -/
theorem sub_eq_comp_add_comp_gradedCoderivAlongSymm
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hbM_sq : bM ∘ₗ bM = 0) (hbN_sq : bN ∘ₗ bN = 0)
    (hD_eq : F - F' = bN ∘ₗ D + D ∘ₗ bM) :
    F' - F = bN ∘ₗ gradedCoderivAlongSymm G bM bN F D +
      gradedCoderivAlongSymm G bM bN F D ∘ₗ bM := by
  have hcomm := comp_add_comp_commutator_eq_zero hbM_sq hbN_sq
    (filtrationLimit (symmSecondOrderSeq G bM bN F D))
  have h1 : bN ∘ₗ gradedCoderivAlongSymm G bM bN F D +
      gradedCoderivAlongSymm G bM bN F D ∘ₗ bM =
      -(bN ∘ₗ D + D ∘ₗ bM) -
        (bN ∘ₗ (bN ∘ₗ filtrationLimit (symmSecondOrderSeq G bM bN F D) -
            filtrationLimit (symmSecondOrderSeq G bM bN F D) ∘ₗ bM) +
          (bN ∘ₗ filtrationLimit (symmSecondOrderSeq G bM bN F D) -
            filtrationLimit (symmSecondOrderSeq G bM bN F D) ∘ₗ bM) ∘ₗ bM) := by
    simp only [gradedCoderivAlongSymm, LinearMap.comp_sub, LinearMap.comp_neg,
      LinearMap.sub_comp, LinearMap.neg_comp]
    abel
  rw [h1, hcomm, ← hD_eq]
  abel

/-- Simultaneous filtration induction for `gradedCoderivAlongSymm`: on `filtration R M n`, `Φ`
satisfies the second-order co-Leibniz rule and `D'` satisfies the `(F', F)`-coderivation rule. -/
private theorem deconcatenation_symm_filtration
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G 1 bM)
    (hbM_hom : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1) (hbM_sq : bM ∘ₗ bM = 0)
    (hbN : IsGradedCoderivation H 1 bN)
    (hbN_hom : LinearMap.IsHomogeneous bN (gradedPiece H) (gradedPiece H) 1) (hbN_sq : bN ∘ₗ bN = 0)
    (hF : IsCoalgHom R F) (hF_hom : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF_int : bN ∘ₗ F = F ∘ₗ bM)
    (hD : IsGradedCoderivationAlong G 1 F F' D)
    (hD_hom : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) (-1))
    (hD_eq : F - F' = bN ∘ₗ D + D ∘ₗ bM) (n : ℕ) :
    (∀ z ∈ filtration R M n,
      deconcatenation R N (filtrationLimit (symmSecondOrderSeq G bM bN F D) z) =
        (TensorProduct.map (filtrationLimit (symmSecondOrderSeq G bM bN F D)) F +
          TensorProduct.map (D ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1))
            (gradedCoderivAlongSymm G bM bN F D) +
          TensorProduct.map F (filtrationLimit (symmSecondOrderSeq G bM bN F D)))
          (deconcatenation R M z)) ∧
    (∀ z ∈ filtration R M n,
      deconcatenation R N (gradedCoderivAlongSymm G bM bN F D z) =
        (TensorProduct.map (gradedCoderivAlongSymm G bM bN F D) F +
          TensorProduct.map (F' ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1))
            (gradedCoderivAlongSymm G bM bN F D)) (deconcatenation R M z)) := by
  set Φ := filtrationLimit (symmSecondOrderSeq G bM bN F D)
  set D' := gradedCoderivAlongSymm G bM bN F D
  have hΦ_hom := isHomogeneous_filtrationLimit_symmSecondOrderSeq hbM hbM_hom hbN_hom hF_hom hD_hom
  have hD'_eq := sub_eq_comp_add_comp_gradedCoderivAlongSymm (G := G) hbM_sq hbN_sq hD_eq
  induction n with
  | zero =>
      refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩ <;>
      · rw [filtration_zero] at hz
        simp only [(Submodule.mem_bot R).1 hz, map_zero]
  | succ n ih =>
      have hΦ_succ : ∀ w ∈ filtration R M (n + 1),
          deconcatenation R N (Φ w) =
            (TensorProduct.map Φ F +
              TensorProduct.map (D ∘ₗ ReducedTensorWords.map (R := R) (G.koszulTwist 1)) D' +
              TensorProduct.map F Φ) (deconcatenation R M w) := fun w hw ↦
        deconcatenation_secondOrder_of_mem_filtration hF hD
          (filtrationLimit_symmSecondOrderSeq_fixedPoint hbM bN F D) ih.2 ih.1 hw
      refine ⟨hΦ_succ, fun z hz ↦ ?_⟩
      have hΨ := deconcatenation_commutator_secondOrder hbM hbM_hom hbN hF_hom hF_int hF_int
        hD_hom hD_eq hD'_eq hΦ_hom (hΦ_succ z hz) (hΦ_succ (bM z) (hbM.mem_filtration hz))
      have hDz := hD.deconcatenation_apply z
      have hD'z : D' z = -D z - (bN ∘ₗ Φ - Φ ∘ₗ bM) z := rfl
      rw [hD'z, map_sub, map_neg, hDz, hΨ]
      induction deconcatenation R M z using TensorProduct.inductionOn with
      | tmul u v =>
          simp only [D', gradedCoderivAlongSymm, LinearMap.add_apply, LinearMap.sub_apply,
            LinearMap.neg_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
            LinearMap.comp_apply, TensorProduct.sub_tmul, TensorProduct.neg_tmul,
            TensorProduct.tmul_sub, TensorProduct.tmul_neg]
          abel
      | add x y hx hy =>
          simp only [map_add] at hx hy ⊢
          convert congrArg₂ (· + ·) hx hy using 1; abel

/-- The inverse coalgebra homotopy `gradedCoderivAlongSymm` is a coderivation along `F'` and `F` at
twist parameter one. -/
theorem isGradedCoderivationAlong_gradedCoderivAlongSymm
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    {F F' D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G 1 bM)
    (hbM_hom : LinearMap.IsHomogeneous bM (gradedPiece G) (gradedPiece G) 1) (hbM_sq : bM ∘ₗ bM = 0)
    (hbN : IsGradedCoderivation H 1 bN)
    (hbN_hom : LinearMap.IsHomogeneous bN (gradedPiece H) (gradedPiece H) 1) (hbN_sq : bN ∘ₗ bN = 0)
    (hF : IsCoalgHom R F) (hF_hom : LinearMap.IsHomogeneous F (gradedPiece G) (gradedPiece H) 0)
    (hF_int : bN ∘ₗ F = F ∘ₗ bM)
    (hD : IsGradedCoderivationAlong G 1 F F' D)
    (hD_hom : LinearMap.IsHomogeneous D (gradedPiece G) (gradedPiece H) (-1))
    (hD_eq : F - F' = bN ∘ₗ D + D ∘ₗ bM) :
    IsGradedCoderivationAlong G 1 F' F (gradedCoderivAlongSymm G bM bN F D) := by
  rw [isGradedCoderivationAlong_iff]
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R M z
  have h := (deconcatenation_symm_filtration hbM hbM_hom hbM_sq hbN hbN_hom hbN_sq hF hF_hom
    hF_int hD hD_hom hD_eq n).2 z hn
  simp only [LinearMap.comp_apply, LinearMap.add_apply] at h ⊢
  rw [h]
  congr 1
  induction deconcatenation R M z using TensorProduct.inductionOn with
  | tmul u v => simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- On single letters, the second-order correction in `gradedCoderivAlongSymm` vanishes, so the
inverse homotopy acts simply as `-D`. -/
@[simp]
theorem gradedCoderivAlongSymm_comp_ofLetter
    {bM : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    {bN : ReducedTensorWords R N →ₗ[R] ReducedTensorWords R N}
    {F D : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R N}
    (hbM : IsGradedCoderivation G 1 bM) :
    gradedCoderivAlongSymm G bM bN F D ∘ₗ ofLetter R M = -D ∘ₗ ofLetter R M := by
  have hstab := symmSecondOrderSeq_stabilises_filtration hbM bN F D
  have hΦ₁ : ∀ w ∈ filtration R M 1,
      filtrationLimit (symmSecondOrderSeq G bM bN F D) w = 0 := fun w hw ↦ by
    rw [filtrationLimit_apply_of_mem_filtration hstab hw,
      symmSecondOrderSeq_stabilises hbM bN F D 0 w hw, symmSecondOrderSeq, LinearMap.zero_apply]
  refine LinearMap.ext fun a ↦ ?_
  have ha : ofLetter R M a ∈ filtration R M 1 := ofLetter_mem_filtration R M a
  simp only [gradedCoderivAlongSymm, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, hΦ₁ _ ha, hΦ₁ _ (hbM.mem_filtration ha), map_zero, sub_self, sub_zero]

end SecondOrder

end ReducedTensorWords

end TauCeti
