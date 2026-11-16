/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import TauCeti.Algebra.BrauerAlgebra.Discriminant
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Equivariance
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.RingTheory.Artinian.Ring
import TauCeti.Algebra.Star.SelfAdjoint

/-!
# The symplectic Brauer action is faithful in the stable range; `B_k(-2n)` is semisimple

The Brauer algebra `B_k(-2n)` acts on the tensor power `(R^{2n})^{⊗k}` through the standard
alternating form (`TauCeti.brauerActionSymp`), a diagram `D` acting by its Pfaffian-signed matrix
`TauCeti.BrauerDiagram.symplecticActionMatrix`. When the symplectic rank `n` is smaller than the
number `k` of strands, the action need not be faithful (for instance at `n = 1` and `k = 3`, where
`B₃(-2)` has rank `15` while the three single-arc subspaces already satisfy a linear relation).
Once `k ≤ n`, however, the action is faithful over **every** commutative ring
(`TauCeti.brauerActionSymp_injective`).

In the orthogonal case (`TauCeti.BrauerDiagram.exists_forall_isConstantOnArcs_iff_eq`) one labels
the `k` arcs of `D` by distinct basis indices so that both endpoints of an arc carry the same
label. For `Matrix.J` a cap or cup vanishes on equal labels and pairs `Sum.inl c` with `Sum.inr c`
instead, whereas a through strand pairs equal labels across the two boundaries. Given an injection
`g` from the `k` lower ends of `D` into `l`, we therefore assign `Sum.inl (g x)` to each lower end
`x` and `Sum.inr (g x)` to its partner `D.val x`, and swap the two halves of `l ⊕ l` on the top
boundary (`TauCeti.BrauerDiagram.exists_isUnit_symplecticActionMatrix_apply_and_eq_zero_of_ne`):
every arc of `D` then carries weight `±1`, while every diagram `D' ≠ D` has an arc whose endpoints
are not swap-partners and hence carries weight `0`. Evaluating at that single matrix entry makes the
matrices of the diagrams linearly independent
(`TauCeti.BrauerDiagram.linearIndependent_symplecticActionMatrix`) and `brauerActionSymp` injective.

Combining faithfulness with `TauCeti.BrauerDiagram.conjTranspose_symplecticActionMatrix` shows that
for `k ≤ n` the image of `B_k(-2n)` over a star-ordered field is a `⋆`-closed subalgebra of a
matrix algebra, so its Jacobson radical vanishes and `B_k(-2n)` is semisimple
(`TauCeti.BrauerAlgebra.isSemisimpleRing_neg_two_mul_of_le`). Specializing to `ℚ` shows that the
integer discriminant `TauCeti.BrauerAlgebra.discr k` does not vanish at `-2n`
(`TauCeti.BrauerAlgebra.eval_neg_two_mul_discr_ne_zero`), which transfers Brown's semisimplicity
theorem (`TauCeti.BrauerAlgebra.isSemisimpleRing_neg_two_mul_of_le_of_charZero`) to **every** field
of characteristic zero.

## Main results

* `TauCeti.BrauerDiagram.exists_isUnit_symplecticActionMatrix_apply_and_eq_zero_of_ne`: when
  `k ≤ card l`, each diagram `D` admits a matrix entry at which `M(D)` is `±1` (hence a unit) and
  `M(D') = 0` for all `D' ≠ D`.
* `TauCeti.BrauerDiagram.linearIndependent_symplecticActionMatrix`: when `k ≤ card l`, the
  symplectic diagram matrices on `k` strands are linearly independent over any commutative ring.
* `TauCeti.brauerActionSymp_injective`: **faithfulness of the symplectic Brauer action** for
  `k ≤ n` over every commutative ring.
* `TauCeti.finrank_centralizer_stdSymplecticRep_tensorPower_two` and
  `TauCeti.finrank_centralizer_stdSymplecticRep_tensorPower_two_of_charZero`: for `2 ≤ n`, the
  commutant of the symplectic group on `(K^{2n})^{⊗2}` has dimension `3`.
* `TauCeti.BrauerAlgebra.isSemisimpleRing_neg_two_mul_of_le` and
  `TauCeti.BrauerAlgebra.isSemisimpleRing_neg_two_mul_of_le_of_charZero`: **Brown's theorem in the
  stable range** — for `k ≤ n`, `B_k(-2n)` is semisimple over every star-ordered field and over
  every field of characteristic zero.

## References

* W. P. Brown, *The semisimplicity of `ω_f^n`*, Annals of Mathematics 63 (1956), 324-335.
* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
* S. Dipper, S. Doty and J. Hu, *Brauer algebras, symplectic Schur algebras and Schur-Weyl duality*,
  Transactions of the American Mathematical Society 360 (2008), 189-213.
-/

public section

open scoped Matrix

namespace TauCeti

universe u

namespace BrauerDiagram

section isolatingEntry

variable {l : Type*} {k : ℕ}

/-- The boundary labelling associated to an embedding `g` of the lower ends of `D` into `l`: lower
ends receive `Sum.inl` labels and their partners receive the matching `Sum.inr` labels. -/
private def isolatingBoundaryMap (D : BrauerDiagram k) (g : {x // D.IsLowerEnd x} ↪ l)
    (x : Fin k ⊕ Fin k) : l ⊕ l :=
  if hx : D.IsLowerEnd x then Sum.inl (g ⟨x, hx⟩)
  else Sum.inr (g ⟨D.val x, D.isLowerEnd_val_of_not_isLowerEnd hx⟩)

private theorem isolatingBoundaryMap_injective (D : BrauerDiagram k)
    (g : {x // D.IsLowerEnd x} ↪ l) : Function.Injective (isolatingBoundaryMap D g) := by
  intro x y hxy
  by_cases hx : D.IsLowerEnd x <;> by_cases hy : D.IsLowerEnd y <;>
    simp only [isolatingBoundaryMap, hx, hy, ↓reduceDIte] at hxy
  · exact congrArg Subtype.val (g.injective (Sum.inl.inj hxy))
  · exact nomatch hxy
  · exact nomatch hxy
  · exact D.val.injective (congrArg Subtype.val (g.injective (Sum.inr.inj hxy)))

private theorem isolatingBoundaryMap_val (D : BrauerDiagram k) (g : {x // D.IsLowerEnd x} ↪ l)
    (x : Fin k ⊕ Fin k) :
    isolatingBoundaryMap D g (D.val x) = (isolatingBoundaryMap D g x).swap := by
  by_cases hx : D.IsLowerEnd x
  · simp [isolatingBoundaryMap, hx, D.not_isLowerEnd_val hx, D.apply_apply]
  · simp [isolatingBoundaryMap, hx, D.isLowerEnd_val_of_not_isLowerEnd hx]

private theorem isolatingBoundaryMap_eq_swap_iff (D : BrauerDiagram k)
    (g : {x // D.IsLowerEnd x} ↪ l) (x y : Fin k ⊕ Fin k) :
    isolatingBoundaryMap D g y = (isolatingBoundaryMap D g x).swap ↔ y = D.val x := by
  rw [← isolatingBoundaryMap_val D g x, (isolatingBoundaryMap_injective D g).eq_iff]

variable [DecidableEq l]

private theorem symplecticArcWeight_isolating_eq_zero {R : Type u} [CommRing R]
    (D : BrauerDiagram k) (g : {x // D.IsLowerEnd x} ↪ l) {x y : Fin k ⊕ Fin k}
    (hxy : y ≠ D.val x) :
    symplecticArcWeight R l
      (Sum.elim (fun i => isolatingBoundaryMap D g (Sum.inl i))
        (fun j => (isolatingBoundaryMap D g (Sum.inr j)).swap)) x y = 0 := by
  have hJ0 {z₁ z₂ : l ⊕ l} (hz : z₂ ≠ z₁.swap) : Matrix.J l R z₁ z₂ = 0 := by
    rcases z₁ with a | a <;> rcases z₂ with b | b <;> simp_all [Matrix.J, eq_comm]
  have hmy : isolatingBoundaryMap D g y ≠ (isolatingBoundaryMap D g x).swap :=
    mt (isolatingBoundaryMap_eq_swap_iff D g x y).mp hxy
  rcases x with i | i <;> rcases y with j | j
  · rw [symplecticArcWeight_inl_inl, Sum.elim_inl, Sum.elim_inl]
    exact hJ0 hmy
  · rw [symplecticArcWeight_inl_inr]
    split_ifs with h
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      have h' : (isolatingBoundaryMap D g (Sum.inl i)).swap = isolatingBoundaryMap D g (Sum.inr j)
        := by simpa using congrArg Sum.swap h
      exact (hmy h'.symm).elim
    · rfl
  · rw [symplecticArcWeight_inr_inl]
    split_ifs with h
    · simp only [Sum.elim_inr, Sum.elim_inl] at h
      exact (hmy h.symm).elim
    · rfl
  · rw [symplecticArcWeight_inr_inr, Sum.elim_inr, Sum.elim_inr]
    refine hJ0 fun h => hmy ?_
    simpa using congrArg Sum.swap h

private theorem isUnit_symplecticArcWeight_isolating {R : Type u} [CommRing R]
    (D : BrauerDiagram k) (g : {x // D.IsLowerEnd x} ↪ l) (x : Fin k ⊕ Fin k) :
    IsUnit (symplecticArcWeight R l
      (Sum.elim (fun i => isolatingBoundaryMap D g (Sum.inl i))
        (fun j => (isolatingBoundaryMap D g (Sum.inr j)).swap)) x (D.val x)) := by
  have hunitJ (z : l ⊕ l) : IsUnit (Matrix.J l R z z.swap) := by
    rcases z with a | a <;> simp [Matrix.J]
  set y := D.val x
  have hy : isolatingBoundaryMap D g y = (isolatingBoundaryMap D g x).swap :=
    isolatingBoundaryMap_val D g x
  rcases hx_sum : x with i | i <;> rcases hy_sum : y with j | j
  · rw [symplecticArcWeight_inl_inl, Sum.elim_inl, Sum.elim_inl, ← hx_sum, ← hy_sum, hy]
    exact hunitJ _
  · rw [symplecticArcWeight_inl_inr, Sum.elim_inl, Sum.elim_inr, ← hx_sum, ← hy_sum, hy,
      Sum.swap_swap]
    simp
  · rw [symplecticArcWeight_inr_inl, Sum.elim_inr, Sum.elim_inl, ← hx_sum, ← hy_sum, hy]
    simp
  · rw [symplecticArcWeight_inr_inr, Sum.elim_inr, Sum.elim_inr, ← hx_sum, ← hy_sum, hy]
    exact hunitJ _

/-- **An entry that singles out a diagram in the symplectic action.** When `k ≤ Fintype.card l`,
each `k`-strand Brauer diagram `D` admits row and column labellings `v, u : Fin k → l ⊕ l` at which
`D.symplecticActionMatrix R l v u` is a unit (`±1`) while `D'.symplecticActionMatrix R l v u = 0`
for every `D' ≠ D`. -/
theorem exists_isUnit_symplecticActionMatrix_apply_and_eq_zero_of_ne (R : Type u) [CommRing R]
    (l : Type*) [DecidableEq l] [Fintype l] (hk : k ≤ Fintype.card l) (D : BrauerDiagram k) :
    ∃ v u : Fin k → l ⊕ l,
      IsUnit (D.symplecticActionMatrix R l v u) ∧
        ∀ D' : BrauerDiagram k, D' ≠ D → D'.symplecticActionMatrix R l v u = 0 := by
  obtain ⟨g⟩ : Nonempty ({x // D.IsLowerEnd x} ↪ l) :=
    Function.Embedding.nonempty_of_card_le (by rwa [D.card_isLowerEnd])
  let u : Fin k → l ⊕ l := fun i => isolatingBoundaryMap D g (Sum.inl i)
  let v : Fin k → l ⊕ l := fun j => (isolatingBoundaryMap D g (Sum.inr j)).swap
  refine ⟨v, u, ?_, fun D' hD' => ?_⟩
  · rw [symplecticActionMatrix_apply, signedWeight_def, zsmul_eq_mul]
    refine IsUnit.mul ?_ (Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
      fun r _ => ?_)
    · rcases Int.units_eq_one_or (Equiv.Perm.sign D.arcPerm) with h | h <;> simp [h]
    · rw [arcPerm_inr]
      exact isUnit_symplecticArcWeight_isolating D g _
  · have hex : ∃ r : Fin k, D'.arcPerm (Sum.inr r) ≠ D.val (D'.arcPerm (Sum.inl r)) := by
      by_contra h
      push Not at h
      refine hD' (Subtype.ext (Equiv.ext fun x => ?_))
      rcases hx : D'.arcPerm.symm x with r | r
      · have hxr := D'.arcPerm.eq_symm_apply.mp hx.symm
        simpa only [arcPerm_inr, hxr] using h r
      · have hxr := D'.arcPerm.eq_symm_apply.mp hx.symm
        have hr : D'.val (D'.arcPerm (Sum.inl r)) = D.val (D'.arcPerm (Sum.inl r)) := by
          simpa only [arcPerm_inr] using h r
        rw [arcPerm_inr] at hxr
        rw [← hxr, D'.apply_apply, hr, D.apply_apply]
    obtain ⟨r, hr⟩ := hex
    rw [symplecticActionMatrix_apply, signedWeight_def,
      Finset.prod_eq_zero (Finset.mem_univ r) (symplecticArcWeight_isolating_eq_zero D g hr),
      smul_zero]

/-- **The symplectic diagram matrices are linearly independent** over every commutative ring as soon
as `k ≤ Fintype.card l`. -/
theorem linearIndependent_symplecticActionMatrix (R : Type u) [CommRing R] (l : Type*)
    [DecidableEq l] [Fintype l] (hk : k ≤ Fintype.card l) :
    LinearIndependent R fun D : BrauerDiagram k => D.symplecticActionMatrix R l := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  intro f g hfg
  ext D
  obtain ⟨v, u, hunit, hzero⟩ :=
    exists_isUnit_symplecticActionMatrix_apply_and_eq_zero_of_ne R l hk D
  have hcoeff (c : BrauerDiagram k →₀ R) :
      Finsupp.linearCombination R (fun D' : BrauerDiagram k => D'.symplecticActionMatrix R l) c v u
        = c D * D.symplecticActionMatrix R l v u := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul]
    by_cases hmem : D ∈ c.support
    · rw [Finset.sum_eq_single D]
      · intro D' _ hne
        rw [hzero D' hne, mul_zero]
      · exact fun h => (h hmem).elim
    · rw [Finset.sum_eq_zero, Finsupp.notMem_support_iff.mp hmem, zero_mul]
      intro D' hD'
      have hne : D' ≠ D := fun e => hmem (e ▸ hD')
      rw [hzero D' hne, mul_zero]
  have heq : f D * D.symplecticActionMatrix R l v u = g D * D.symplecticActionMatrix R l v u := by
    rw [← hcoeff f, ← hcoeff g, hfg]
  exact hunit.mul_right_cancel heq

end isolatingEntry

end BrauerDiagram

section Faithfulness

variable (R : Type u) [CommRing R] (n k : ℕ)

/-- **The symplectic Brauer action is faithful in the stable range**: when `k ≤ n`, distinct
elements of `B_k(-2n)` act differently on `((Fin n ⊕ Fin n) → R)^{⊗k}`, over every commutative
ring. -/
theorem brauerActionSymp_injective (hk : k ≤ n) : Function.Injective (brauerActionSymp R n k) := by
  intro x y h
  have hmat := congrArg
    (LinearMap.toMatrix (symplecticTensorPowerBasis R n k) (symplecticTensorPowerBasis R n k)) h
  rw [toMatrix_brauerActionSymp, toMatrix_brauerActionSymp] at hmat
  exact BrauerAlgebra.ext ((BrauerDiagram.linearIndependent_symplecticActionMatrix R (Fin n)
    (by simpa using hk)).finsuppLinearCombination_injective hmat)

end Faithfulness

section TwoStrandRank

/-- **The commutant of the symplectic group on `(K^{2n})^{⊗2}` has rank three** when `2 ≤ n`, over
an integral domain containing a unit `t` with `t ^ m ≠ 1` for `0 < m ≤ 4`: it is the faithful image
of `B₂(-2n)`, which is free on its three diagrams. -/
theorem finrank_centralizer_stdSymplecticRep_tensorPower_two {K : Type u} [CommRing K] [IsDomain K]
    {n : ℕ} (hn : 2 ≤ n) (ht : ∃ t : Kˣ, ∀ m : ℕ, 0 < m → m ≤ 4 → t ^ m ≠ 1) :
    Module.finrank K
      (Subalgebra.centralizer K (Set.range ((stdSymplecticRep K n).tensorPower 2))) = 3 := by
  rw [← range_brauerActionSymp_two_eq_centralizer n ht,
    ← (AlgEquiv.ofInjective _ (brauerActionSymp_injective K n 2 hn)).toLinearEquiv.finrank_eq,
    BrauerAlgebra.finrank_eq_doubleFactorial]
  rfl

/-- **The commutant of the symplectic group on `(K^{2n})^{⊗2}` has dimension three** in
characteristic zero whenever `2 ≤ n`. -/
theorem finrank_centralizer_stdSymplecticRep_tensorPower_two_of_charZero {K : Type u} [Field K]
    [CharZero K] {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank K
      (Subalgebra.centralizer K (Set.range ((stdSymplecticRep K n).tensorPower 2))) = 3 := by
  rw [← range_brauerActionSymp_two_eq_centralizer_of_charZero n,
    ← (AlgEquiv.ofInjective _ (brauerActionSymp_injective K n 2 hn)).toLinearEquiv.finrank_eq,
    BrauerAlgebra.finrank_eq_doubleFactorial]
  rfl

end TwoStrandRank

/-! ### Semisimplicity at symplectic loop values in the stable range -/

namespace BrauerAlgebra

variable {n k : ℕ}

private theorem aeval_neg_two_mul {R : Type*} [CommRing R] (p : Polynomial ℤ) (n : ℕ) :
    Polynomial.aeval (-(2 * n : R)) p = ((Polynomial.eval (-(2 * n : ℤ)) p : ℤ) : R) := by
  have hm : (-(2 * n : R)) = Int.castRingHom R (-(2 * n : ℤ)) := by simp
  have hhom : algebraMap ℤ R = Int.castRingHom R := RingHom.ext_int _ _
  have h := Polynomial.hom_eval₂ p (RingHom.id ℤ) (Int.castRingHom R) (-(2 * n : ℤ))
  rw [RingHom.comp_id] at h
  rw [Polynomial.aeval_def, hhom, hm, ← h]
  rfl

/-- **Brown's theorem over a star-ordered field**: when `k ≤ n`, the Brauer algebra `B_k(-2n)` at
the symplectic loop value `-2n` is semisimple over every star-ordered field, such as `ℚ`, `ℝ` or
`ℂ` (with `ComplexOrder`). -/
theorem isSemisimpleRing_neg_two_mul_of_le {K : Type*} [Field K] [PartialOrder K] [StarRing K]
    [StarOrderedRing K] (hk : k ≤ n) :
    IsSemisimpleRing (BrauerAlgebra K (-(2 * n : K)) k) := by
  let Φ : BrauerAlgebra K (-(2 * n : K)) k →ₐ[K]
      Matrix (Fin k → Fin n ⊕ Fin n) (Fin k → Fin n ⊕ Fin n) K :=
    (LinearMap.toMatrixAlgEquiv (symplecticTensorPowerBasis K n k)).toAlgHom.comp
      (brauerActionSymp K n k)
  have hΦ (x : BrauerAlgebra K (-(2 * n : K)) k) : Φ x = Finsupp.linearCombination K
      (fun D : BrauerDiagram k => D.symplecticActionMatrix K (Fin n)) x.coeff := by
    rw [← toMatrix_brauerActionSymp]
    ext i j
    simp [Φ, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have hinj : Function.Injective Φ :=
    (LinearMap.toMatrixAlgEquiv _).injective.comp (brauerActionSymp_injective K n k hk)
  have := IsArtinianRing.of_finite K (BrauerAlgebra K (-(2 * n : K)) k)
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson]
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson (BrauerAlgebra K (-(2 * n : K)) k)
  refine eq_bot_iff.mpr fun x hx => ?_
  let y : BrauerAlgebra K (-(2 * n : K)) k :=
    ∑ D ∈ x.coeff.support, star (x.coeff D) • BrauerAlgebra.of D.flip
  have hof (D : BrauerDiagram k) : Φ (BrauerAlgebra.of D) = D.symplecticActionMatrix K (Fin n) := by
    simp [hΦ]
  have hy : Φ y = (Φ x)ᴴ := by
    rw [hΦ x]
    simp [y, hof, Finsupp.linearCombination_apply, Finsupp.sum, Matrix.conjTranspose_sum]
  have hnil : IsNilpotent ((Φ x)ᴴ * Φ x) := by
    refine ⟨m, ?_⟩
    have hpow := Ideal.pow_mem_pow ((Ring.jacobson _).smul_mem y hx) m
    rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot, smul_eq_mul] at hpow
    rw [← hy, ← map_mul, ← map_pow, hpow, map_zero]
  have h0 := (IsSelfAdjoint.star_mul_self (Φ x)).eq_zero_of_isNilpotent hnil
  rw [star_mul_self_eq_zero, ← map_zero Φ] at h0
  exact (Submodule.mem_bot _).mpr (hinj h0)

/-- **The discriminant of `B_k` does not vanish at `-2n` when `k ≤ n`.** -/
theorem eval_neg_two_mul_discr_ne_zero (hk : k ≤ n) :
    Polynomial.eval (-(2 * n : ℤ)) (discr k) ≠ 0 := by
  intro h
  refine (isSemisimpleRing_iff_aeval_discr_ne_zero (K := ℚ) (δ := -(2 * n : ℚ))).mp
    (isSemisimpleRing_neg_two_mul_of_le hk) ?_
  rw [aeval_neg_two_mul, h, Int.cast_zero]

/-- **Brown's theorem in the stable range**: over every field of characteristic zero, the Brauer
algebra `B_k(-2n)` at the symplectic loop value `-2n` is semisimple whenever `k ≤ n`. -/
theorem isSemisimpleRing_neg_two_mul_of_le_of_charZero {K : Type*} [Field K] [CharZero K]
    (hk : k ≤ n) :
    IsSemisimpleRing (BrauerAlgebra K (-(2 * n : K)) k) := by
  refine isSemisimpleRing_of_aeval_discr_ne_zero ?_
  rw [aeval_neg_two_mul]
  exact Int.cast_ne_zero.mpr (eval_neg_two_mul_discr_ne_zero hk)

end BrauerAlgebra

end TauCeti
