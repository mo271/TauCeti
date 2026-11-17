/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Tower

/-!
# Abstract Markov traces

An unnormalized Markov trace on the Temperley–Lieb tower takes the value `δ ^ n` on the
identity on `n` strands. Adding a strand multiplies the trace by `δ`, whereas capping that
strand with the last generator recovers the trace one level down.

This file defines `TauCeti.TemperleyLieb.IsMarkovTrace` and proves the trace reduction for
a last generator sandwiched between two included elements. This reduction is used for the
capped terms in the tower's normal form and for quantum-dimension calculations.

Together with the tower normal form
`TauCeti.TemperleyLieb.span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top`, the two
compatibilities determine a Markov trace on `n + 2` strands from its values on `n + 1` strands,
and the normalization determines it on at most one strand, where the algebra is the base ring.
So there is at most one Markov trace at each loop parameter
(`TauCeti.TemperleyLieb.IsMarkovTrace.unique`), over every commutative semiring. This file does
not assert the existence of a Markov trace at every loop parameter.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTrace.map_strandIncl_mul_e_last_mul`: the trace reduction for
  `strandIncl a * e δ (Fin.last n) * strandIncl b`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_e`: every generator `e δ i` on `n` strands has trace
  `δ ^ (n - 1)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_of_le_one`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_zero_strands`: evaluation on at most one strand.
* `TauCeti.TemperleyLieb.IsMarkovTrace.unique`: uniqueness of the Markov trace.
* `TauCeti.TemperleyLieb.IsMarkovTrace.eq_zero_of_pos`: at loop parameter `δ = 0`, every Markov
  trace vanishes on every positive number of strands.

## References

* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
-/

public section

namespace TauCeti.TemperleyLieb

/-- An **unnormalized Markov trace** on the Temperley–Lieb tower: a family of linear forms
with `tr n 1 = δ ^ n`, traciality, strand-inclusion compatibility, and the Markov property.
The normalization is specified in every degree, including degrees zero and one, since
`strandIncl` starts at one strand. -/
structure IsMarkovTrace (R : Type*) [CommSemiring R] (δ : R)
    (tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R) : Prop where
  map_one : ∀ n, tr n 1 = δ ^ n
  map_mul_comm : ∀ n (x y : TemperleyLieb R δ n), tr n (x * y) = tr n (y * x)
  map_strandIncl : ∀ n (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) (strandIncl x) = δ * tr (n + 1) x
  map_strandIncl_mul_e_last : ∀ n (x : TemperleyLieb R δ (n + 1)),
    tr (n + 2) (strandIncl x * e δ (Fin.last n)) = tr (n + 1) x

variable {R : Type*} [CommSemiring R] {δ : R}
  {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}

namespace IsMarkovTrace

/-- The Markov property for a last generator sandwiched between two included elements.
This is the trace reduction for the capped terms in the tower's normal form. -/
@[simp]
theorem map_strandIncl_mul_e_last_mul (htr : IsMarkovTrace R δ tr) {n : ℕ}
    (a b : TemperleyLieb R δ (n + 1)) :
    tr (n + 2) (strandIncl a * e δ (Fin.last n) * strandIncl b) = tr (n + 1) (a * b) := by
  rw [htr.map_mul_comm, ← mul_assoc, ← map_mul, htr.map_strandIncl_mul_e_last,
    htr.map_mul_comm]

/-- Every generator `e δ i` on `n` strands has trace `δ ^ (n - 1)`: its closure has `n - 1`
loops. -/
@[simp]
theorem map_e (htr : IsMarkovTrace R δ tr) :
    ∀ {n : ℕ} (i : Fin (n - 1)), tr n (e δ i) = δ ^ (n - 1)
  | 0, i => Fin.elim0 i
  | 1, i => Fin.elim0 i
  | m + 2, i => by
    induction i using Fin.lastCases with
    | last =>
      have h := htr.map_strandIncl_mul_e_last m 1
      rw [_root_.map_one, one_mul, htr.map_one] at h
      exact h
    | cast j =>
      rw [← strandIncl_e, htr.map_strandIncl, htr.map_e (n := m + 1) j, ← pow_succ']
      rfl

/-- On at most one strand the algebra is the base ring, so every unnormalized Markov trace
evaluates as `aug x * δ ^ n`. -/
theorem map_of_le_one (htr : IsMarkovTrace R δ tr) {n : ℕ} (hn : n ≤ 1)
    (x : TemperleyLieb R δ n) : tr n x = aug x * δ ^ n :=
  calc
    tr n x = tr n ((algEquivOfLeOne δ hn).symm (algEquivOfLeOne δ hn x)) := by
      rw [(algEquivOfLeOne δ hn).symm_apply_apply]
    _ = tr n (aug x • (1 : TemperleyLieb R δ n)) := by
      rw [algEquivOfLeOne_symm_apply, algEquivOfLeOne_apply, Algebra.algebraMap_eq_smul_one]
    _ = aug x * δ ^ n := by rw [map_smul, htr.map_one, smul_eq_mul]

/-- On zero strands, every unnormalized Markov trace agrees with the augmentation. -/
@[simp]
theorem map_zero_strands (htr : IsMarkovTrace R δ tr) (x : TemperleyLieb R δ 0) :
    tr 0 x = aug x := by
  simpa only [pow_zero, mul_one] using htr.map_of_le_one (Nat.zero_le 1) x

/-- On at most one strand the algebra is the base ring, so a Markov trace is determined there by
its normalization `tr n 1 = δ ^ n`. -/
private theorem eq_of_le_one {tr' : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
    (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ tr') {n : ℕ} (hn : n ≤ 1) :
    tr n = tr' n := by
  ext x
  rw [htr.map_of_le_one hn, htr'.map_of_le_one hn]

/-- **Uniqueness of the Markov trace.** Over every commutative semiring and at every loop parameter
there is at most one unnormalized Markov trace on the Temperley–Lieb tower: on `n + 2` strands it
is determined on the spanning elements `strandIncl a` and
`strandIncl a * e δ (Fin.last n) * strandIncl b` by its values on `n + 1` strands. -/
theorem unique {tr' : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ tr') : tr = tr' := by
  funext n
  obtain _ | n := n
  · exact eq_of_le_one htr htr' (by omega)
  induction n with
  | zero => exact eq_of_le_one htr htr' le_rfl
  | succ n ih =>
    refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top n) ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · rw [htr.map_strandIncl, htr'.map_strandIncl, ih]
    · rw [htr.map_strandIncl_mul_e_last_mul, htr'.map_strandIncl_mul_e_last_mul, ih]

/-- At loop parameter `δ = 0`, every unnormalized Markov trace vanishes on every positive number
of strands: the closure of any nonempty diagram contains a closed loop. -/
theorem eq_zero_of_pos {tr₀ : ∀ n : ℕ, TemperleyLieb R 0 n →ₗ[R] R}
    (htr : IsMarkovTrace R 0 tr₀) : ∀ {n : ℕ}, 0 < n → tr₀ n = 0
  | 0, hn => absurd hn (lt_irrefl 0)
  | 1, _ => by
    ext x
    rw [htr.map_of_le_one le_rfl, pow_one, mul_zero, LinearMap.zero_apply]
  | n + 2, _ => by
    refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top n) ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
    · rw [htr.map_strandIncl, zero_mul, LinearMap.zero_apply]
    · rw [htr.map_strandIncl_mul_e_last_mul, htr.eq_zero_of_pos (Nat.succ_pos n),
        LinearMap.zero_apply, LinearMap.zero_apply]

/-- Pointwise vanishing of a Markov trace at loop parameter `δ = 0` on every positive number of
strands. -/
theorem map_eq_zero_of_pos {tr₀ : ∀ n : ℕ, TemperleyLieb R 0 n →ₗ[R] R}
    (htr : IsMarkovTrace R 0 tr₀) {n : ℕ} (hn : 0 < n)
    (x : TemperleyLieb R 0 n) : tr₀ n x = 0 := by
  rw [htr.eq_zero_of_pos hn, LinearMap.zero_apply]

end IsMarkovTrace

end TauCeti.TemperleyLieb
