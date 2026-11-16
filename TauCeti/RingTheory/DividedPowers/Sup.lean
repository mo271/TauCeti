/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import TauCeti.RingTheory.DividedPowers.Generators

/-!
# Gluing divided powers on compatible sums of ideals

Given two ideals `I` and `J` of a commutative ring `A` equipped with divided power structures
`γ : DividedPowers I` and `ε : DividedPowers J`, a divided power structure on `I ⊔ J` restricting
to `γ` on `I` and to `ε` on `J` must evaluate on `x + y` (`x ∈ I`, `y ∈ J`) via the antidiagonal
convolution
`γ.dpowConv ε n x y = ∑ k ∈ antidiagonal n, γ.dpow k.1 x * ε.dpow k.2 y`.

Following Berthelot (1974, I.1.6.1) and
[Stacks Lemma 07GQ](https://stacks.math.columbia.edu/tag/07GQ), this file shows:

1. `γ.dpowConv ε n x y` is the degree-`n` coefficient of the formal power series product
   `γ.exp x * ε.exp y`;
2. if `γ` and `ε` agree in all degrees on `I ⊓ J`, then `γ.dpowConv ε n x y` depends only on the
   sum `x + y ∈ I ⊔ J`, defining an additive divided-power candidate `γ.supAdditivePowers ε h` on
   `I ⊔ J` that restricts to `γ` on `I` and to `ε` on `J`;
3. applying the generator criterion `TauCeti.AdditivePowers.toDividedPowers` on `(I : Set A) ∪ J`
   yields the unique divided power structure `γ.sup ε h : DividedPowers (I ⊔ J)` extending `γ` and
   `ε`, together with its universal property for `DividedPowers.IsDPMorphism`;
4. in particular, when `I ⊓ J = I * J`, agreement on `I ⊓ J` holds unconditionally by
   `DividedPowers.coincide_on_smul`, giving `γ.supOfInfEqMul ε hIJ`.

## Main declarations

* `DividedPowers.dpowConv`: the antidiagonal convolution of two divided power structures.
* `DividedPowers.coeff_exp_mul`: `PowerSeries.coeff n (γ.exp x * ε.exp y) = γ.dpowConv ε n x y`.
* `DividedPowers.dpowConv_eq_of_add_eq`: independence of the decomposition `x + y = x' + y'` when
  `γ` and `ε` agree on `I ⊓ J`.
* `DividedPowers.supAdditivePowers`: the glued `TauCeti.AdditivePowers (I ⊔ J)` candidate.
* `DividedPowers.sup`: the unique `DividedPowers (I ⊔ J)` extending compatible `γ` and `ε`.
* `DividedPowers.isDPMorphism_sup_iff`: universal property of `γ.sup ε h` with respect to
  `DividedPowers.IsDPMorphism`.
* `DividedPowers.existsUnique_sup_iff`: a common extension to `I ⊔ J` exists (and is unique) if and
  only if `γ` and `ε` agree on `I ⊓ J`.
* `DividedPowers.supOfInfEqMul`: unconditional gluing on `I ⊔ J` when `I ⊓ J = I * J`.

## References

* [Stacks: Divided power algebra, Lemma 07GQ](https://stacks.math.columbia.edu/tag/07GQ).
* P. Berthelot, *Cohomologie cristalline des schémas de caractéristique $p > 0$*, Lecture Notes in
  Mathematics 407, Springer (1974), Chapitre I, Proposition 1.6.1.
* N. Roby, *Les algèbres à puissances dividées*, Bull. Sci. Math. (2) 89 (1965), 75–91.
-/

public section

open Finset Nat

namespace DividedPowers

section CommSemiring

variable {A : Type*} [CommSemiring A] {I J : Ideal A}

/-- The antidiagonal convolution `∑_{i + j = n} γᵢ(x) εⱼ(y)` of two divided power structures `γ`
on `I` and `ε` on `J`. -/
def dpowConv (γ : DividedPowers I) (ε : DividedPowers J) (n : ℕ) (x y : A) : A :=
  ∑ k ∈ antidiagonal n, γ.dpow k.1 x * ε.dpow k.2 y

theorem dpowConv_def (γ : DividedPowers I) (ε : DividedPowers J) (n : ℕ) (x y : A) :
    γ.dpowConv ε n x y = ∑ k ∈ antidiagonal n, γ.dpow k.1 x * ε.dpow k.2 y :=
  (rfl)

theorem dpowConv_comm (γ : DividedPowers I) (ε : DividedPowers J) (n : ℕ) (x y : A) :
    γ.dpowConv ε n x y = ε.dpowConv γ n y x := by
  rw [dpowConv_def, dpowConv_def, ← Nat.sum_antidiagonal_swap]
  refine sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- `γ.dpowConv ε n x y` is the `n`-th coefficient of `(γ.exp x) * (ε.exp y)`. -/
theorem coeff_exp_mul (γ : DividedPowers I) (ε : DividedPowers J) (n : ℕ) (x y : A) :
    PowerSeries.coeff n (γ.exp x * ε.exp y) = γ.dpowConv ε n x y := by
  simp [DividedPowers.exp, PowerSeries.coeff_mul, dpowConv_def]

@[simp]
theorem dpowConv_zero_deg (γ : DividedPowers I) (ε : DividedPowers J)
    {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    γ.dpowConv ε 0 x y = 1 := by
  simp [dpowConv_def, γ.dpow_zero hx, ε.dpow_zero hy]

theorem dpowConv_one_deg (γ : DividedPowers I) (ε : DividedPowers J)
    {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    γ.dpowConv ε 1 x y = x + y := by
  have h1 : antidiagonal 1 = {(0, 1), (1, 0)} := rfl
  rw [dpowConv_def, h1]
  simp [γ.dpow_zero hx, γ.dpow_one hx, ε.dpow_zero hy, ε.dpow_one hy, add_comm]

theorem dpowConv_two_deg (γ : DividedPowers I) (ε : DividedPowers J)
    {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    γ.dpowConv ε 2 x y = γ.dpow 2 x + x * y + ε.dpow 2 y := by
  have h2 : antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := rfl
  rw [dpowConv_def, h2, sum_insert (by decide), sum_insert (by decide), sum_singleton,
    γ.dpow_zero hx, γ.dpow_one hx, ε.dpow_zero hy, ε.dpow_one hy]
  ring

theorem dpowConv_self (γ : DividedPowers I) {x y : A} (hx : x ∈ I) (hy : y ∈ I) (n : ℕ) :
    γ.dpowConv γ n x y = γ.dpow n (x + y) :=
  (γ.dpow_add hx hy).symm

theorem dpowConv_mem (γ : DividedPowers I) (ε : DividedPowers J)
    {n : ℕ} (hn : n ≠ 0) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    γ.dpowConv ε n x y ∈ I ⊔ J := by
  rw [dpowConv_def]
  refine Submodule.sum_mem (I ⊔ J) fun k hk ↦ ?_
  have hsum : k.1 + k.2 = n := mem_antidiagonal.mp hk
  rcases eq_or_ne k.1 0 with hk1 | hk1
  · have hk2 : k.2 ≠ 0 := by omega
    exact Ideal.mul_mem_left _ _ (Submodule.mem_sup_right (ε.dpow_mem hk2 hy))
  · exact Ideal.mul_mem_right _ _ (Submodule.mem_sup_left (γ.dpow_mem hk1 hx))

@[simp]
theorem dpowConv_zero_right (γ : DividedPowers I) (ε : DividedPowers J) (n : ℕ) (x : A) :
    γ.dpowConv ε n x 0 = γ.dpow n x := by
  rw [dpowConv_def, sum_eq_single (n, 0)]
  · simp [ε.dpow_zero J.zero_mem]
  · intro k hk hne
    have hk2 : k.2 ≠ 0 := by
      have hsum := mem_antidiagonal.mp hk
      intro h0
      exact hne (Prod.ext (by omega) h0)
    simp [ε.dpow_eval_zero hk2]
  · intro hn
    exact absurd (mem_antidiagonal.mpr (add_zero n)) hn

@[simp]
theorem dpowConv_zero_left (γ : DividedPowers I) (ε : DividedPowers J) (n : ℕ) (y : A) :
    γ.dpowConv ε n 0 y = ε.dpow n y := by
  rw [dpowConv_comm, dpowConv_zero_right]

theorem dpowConv_mul (γ : DividedPowers I) (ε : DividedPowers J)
    (n : ℕ) (a : A) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    γ.dpowConv ε n (a * x) (a * y) = a ^ n * γ.dpowConv ε n x y := by
  rw [dpowConv_def, dpowConv_def, mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [γ.dpow_mul hx, ε.dpow_mul hy, ← mem_antidiagonal.mp hk]
  ring

theorem dpowConv_add (γ : DividedPowers I) (ε : DividedPowers J)
    (n : ℕ) {x₁ x₂ y₁ y₂ : A} (hx₁ : x₁ ∈ I) (hx₂ : x₂ ∈ I) (hy₁ : y₁ ∈ J) (hy₂ : y₂ ∈ J) :
    γ.dpowConv ε n (x₁ + x₂) (y₁ + y₂) =
      ∑ k ∈ antidiagonal n, γ.dpowConv ε k.1 x₁ y₁ * γ.dpowConv ε k.2 x₂ y₂ := by
  rw [← coeff_exp_mul, γ.exp_add hx₁ hx₂, ε.exp_add hy₁ hy₂]
  have hmul :
      γ.exp x₁ * γ.exp x₂ * (ε.exp y₁ * ε.exp y₂) =
        (γ.exp x₁ * ε.exp y₁) * (γ.exp x₂ * ε.exp y₂) := by ring
  rw [hmul, PowerSeries.coeff_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [coeff_exp_mul, coeff_exp_mul]

end CommSemiring

section CommRing

variable {A : Type*} [CommRing A] {I J : Ideal A}

/-- **Decomposition independence of convolution**
([Stacks Lemma 07GQ](https://stacks.math.columbia.edu/tag/07GQ)): if `γ` and `ε` agree on `I ⊓ J`
in every degree, then `γ.dpowConv ε n x y` depends only on the sum `x + y` for `x ∈ I` and
`y ∈ J`. -/
theorem dpowConv_eq_of_add_eq (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w)
    {x x' y y' : A} (hx : x ∈ I) (hx' : x' ∈ I) (hy : y ∈ J) (hy' : y' ∈ J)
    (hxy : x + y = x' + y') (n : ℕ) :
    γ.dpowConv ε n x y = γ.dpowConv ε n x' y' := by
  let w : A := x - x'
  have hwI : w ∈ I := I.sub_mem hx hx'
  have hw_eq : w = y' - y :=
    calc
      x - x' = x + y - x' - y := by ring
      _ = x' + y' - x' - y := by rw [hxy]
      _ = y' - y := by ring
  have hwJ : w ∈ J := hw_eq ▸ J.sub_mem hy' hy
  have hwIJ : w ∈ I ⊓ J := ⟨hwI, hwJ⟩
  have hexp_w : γ.exp w = ε.exp w := PowerSeries.ext fun k ↦ by
    simp [DividedPowers.exp, h k w hwIJ]
  have hx_decomp : x = x' + w := (add_sub_cancel x' x).symm
  have hy_decomp : y' = w + y := by
    rw [hw_eq, sub_add_cancel]
  rw [← coeff_exp_mul, ← coeff_exp_mul, hx_decomp, hy_decomp,
    γ.exp_add hx' hwI, ε.exp_add hwJ hy, hexp_w, mul_assoc]

private noncomputable def supDpowAux (γ : DividedPowers I) (ε : DividedPowers J)
    (n : ℕ) (z : A) : A :=
  open scoped Classical in
  if hz : z ∈ I ⊔ J then
    γ.dpowConv ε n (Submodule.mem_sup.mp hz).choose
      (Submodule.mem_sup.mp hz).choose_spec.2.choose
  else 0

private theorem supDpowAux_add (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w)
    (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    γ.supDpowAux ε n (x + y) = γ.dpowConv ε n x y := by
  have hxy : x + y ∈ I ⊔ J := Submodule.add_mem_sup hx hy
  simp only [supDpowAux, hxy, ↓reduceDIte]
  have hs := (Submodule.mem_sup.mp hxy).choose_spec
  exact γ.dpowConv_eq_of_add_eq ε h hs.1 hx hs.2.choose_spec.1 hy hs.2.choose_spec.2 n

/-- The glued additive divided-power candidate on `I ⊔ J` associated to two divided power
structures `γ` on `I` and `ε` on `J` that agree on `I ⊓ J`. -/
noncomputable def supAdditivePowers (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w) :
    TauCeti.AdditivePowers (I ⊔ J) where
  dpow := γ.supDpowAux ε
  dpow_null {n z} hz := by simp [supDpowAux, hz]
  dpow_zero {z} hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [γ.supDpowAux_add ε h 0 hx hy, γ.dpowConv_zero_deg ε hx hy]
  dpow_one {z} hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [γ.supDpowAux_add ε h 1 hx hy, γ.dpowConv_one_deg ε hx hy]
  dpow_mem {n z} hn hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [γ.supDpowAux_add ε h n hx hy]
    exact γ.dpowConv_mem ε hn hx hy
  dpow_add {n z₁ z₂} hz₁ hz₂ := by
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hz₁
    obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hz₂
    rw [add_add_add_comm x₁ y₁ x₂ y₂,
      γ.supDpowAux_add ε h n (I.add_mem hx₁ hx₂) (J.add_mem hy₁ hy₂),
      γ.dpowConv_add ε n hx₁ hx₂ hy₁ hy₂]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [γ.supDpowAux_add ε h k.1 hx₁ hy₁, γ.supDpowAux_add ε h k.2 hx₂ hy₂]
  dpow_mul {n a z} hz := by
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [mul_add, γ.supDpowAux_add ε h n (I.mul_mem_left a hx) (J.mul_mem_left a hy),
      γ.supDpowAux_add ε h n hx hy, γ.dpowConv_mul ε n a hx hy]

theorem supAdditivePowers_dpow_add (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w)
    (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    (γ.supAdditivePowers ε h).dpow n (x + y) = γ.dpowConv ε n x y :=
  γ.supDpowAux_add ε h n hx hy

theorem supAdditivePowers_dpow_mem_left (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w) (n : ℕ) {x : A} (hx : x ∈ I) :
    (γ.supAdditivePowers ε h).dpow n x = γ.dpow n x := by
  simpa using γ.supAdditivePowers_dpow_add ε h n hx J.zero_mem

theorem supAdditivePowers_dpow_mem_right (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w) (n : ℕ) {y : A} (hy : y ∈ J) :
    (γ.supAdditivePowers ε h).dpow n y = ε.dpow n y := by
  simpa using γ.supAdditivePowers_dpow_add ε h n I.zero_mem hy

/-- **Gluing divided powers on a compatible sum of ideals**
([Stacks Lemma 07GQ](https://stacks.math.columbia.edu/tag/07GQ)): if `γ : DividedPowers I` and
`ε : DividedPowers J` agree on `I ⊓ J` in every degree, `γ.sup ε h` is the unique divided power
structure on `I ⊔ J` restricting to `γ` on `I` and to `ε` on `J`. -/
noncomputable def sup (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w) :
    DividedPowers (I ⊔ J) :=
  (γ.supAdditivePowers ε h).toDividedPowers
    (S := (I : Set A) ∪ (J : Set A))
    (by rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq])
    (fun s hs m n ↦ by
      rcases hs with hsI | hsJ
      · simp only [γ.supAdditivePowers_dpow_mem_left ε h _ hsI]
        exact γ.mul_dpow hsI
      · simp only [γ.supAdditivePowers_dpow_mem_right ε h _ hsJ]
        exact ε.mul_dpow hsJ)
    (fun s hs m {n} hn ↦ by
      rcases hs with hsI | hsJ
      · rw [γ.supAdditivePowers_dpow_mem_left ε h n hsI,
          γ.supAdditivePowers_dpow_mem_left ε h m (γ.dpow_mem hn hsI),
          γ.supAdditivePowers_dpow_mem_left ε h (m * n) hsI]
        exact γ.dpow_comp hn hsI
      · rw [γ.supAdditivePowers_dpow_mem_right ε h n hsJ,
          γ.supAdditivePowers_dpow_mem_right ε h m (ε.dpow_mem hn hsJ),
          γ.supAdditivePowers_dpow_mem_right ε h (m * n) hsJ]
        exact ε.dpow_comp hn hsJ)

@[simp]
theorem sup_dpow_eq_supAdditivePowers (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w) :
    (γ.sup ε h).dpow = (γ.supAdditivePowers ε h).dpow := by
  simp [sup]

theorem sup_dpow_add (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w)
    (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    (γ.sup ε h).dpow n (x + y) = γ.dpowConv ε n x y := by
  rw [sup_dpow_eq_supAdditivePowers]
  exact γ.supAdditivePowers_dpow_add ε h n hx hy

theorem sup_dpow_mem_left (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w)
    (n : ℕ) {x : A} (hx : x ∈ I) :
    (γ.sup ε h).dpow n x = γ.dpow n x := by
  rw [sup_dpow_eq_supAdditivePowers]
  exact γ.supAdditivePowers_dpow_mem_left ε h n hx

theorem sup_dpow_mem_right (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w)
    (n : ℕ) {y : A} (hy : y ∈ J) :
    (γ.sup ε h).dpow n y = ε.dpow n y := by
  rw [sup_dpow_eq_supAdditivePowers]
  exact γ.supAdditivePowers_dpow_mem_right ε h n hy

/-- The identity map is a divided power morphism `(A, I, γ) → (A, I ⊔ J, γ.sup ε h)`. -/
theorem isDPMorphism_sup_left (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w) :
    IsDPMorphism γ (γ.sup ε h) (RingHom.id A) :=
  ⟨by rw [Ideal.map_id]; exact le_sup_left, fun {n} a ha ↦ by
    simpa using γ.sup_dpow_mem_left ε h n ha⟩

/-- The identity map is a divided power morphism `(A, J, ε) → (A, I ⊔ J, γ.sup ε h)`. -/
theorem isDPMorphism_sup_right (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w) :
    IsDPMorphism ε (γ.sup ε h) (RingHom.id A) :=
  ⟨by rw [Ideal.map_id]; exact le_sup_right, fun {n} b hb ↦ by
    simpa using γ.sup_dpow_mem_right ε h n hb⟩

/-- **Universal property of the glued divided power structure**: a ring homomorphism `g : A →+* C`
is a PD morphism from `(I ⊔ J, γ.sup ε h)` to `(K, κ)` if and only if it is a PD morphism from both
`(I, γ)` and `(J, ε)` to `(K, κ)`. -/
theorem isDPMorphism_sup_iff {C : Type*} [CommSemiring C] {K : Ideal C}
    (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w)
    (κ : DividedPowers K) (g : A →+* C) :
    IsDPMorphism (γ.sup ε h) κ g ↔ IsDPMorphism γ κ g ∧ IsDPMorphism ε κ g := by
  constructor
  · intro hg
    exact ⟨by simpa using IsDPMorphism.comp κ hg (γ.isDPMorphism_sup_left ε h),
      by simpa using IsDPMorphism.comp κ hg (γ.isDPMorphism_sup_right ε h)⟩
  · rintro ⟨hgI, hgJ⟩
    have hspan : I ⊔ J = Ideal.span ((I : Set A) ∪ (J : Set A)) := by
      rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq]
    refine IsDPMorphism.on_span (γ.sup ε h) κ hspan ?_ fun {n} s hs ↦ ?_
    · rintro s (hsI | hsJ)
      · exact hgI.1 (Ideal.mem_map_of_mem g hsI)
      · exact hgJ.1 (Ideal.mem_map_of_mem g hsJ)
    · rcases hs with hsI | hsJ
      · rw [γ.sup_dpow_mem_left ε h n hsI]
        exact hgI.map_dpow hsI
      · rw [γ.sup_dpow_mem_right ε h n hsJ]
        exact hgJ.map_dpow hsJ

/-- Characterization of `γ.sup ε h` as the unique divided power structure on `I ⊔ J` restricting to
`γ` on `I` and to `ε` on `J`. -/
theorem eq_sup_iff (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w)
    (θ : DividedPowers (I ⊔ J)) :
    θ = γ.sup ε h ↔
      (∀ n, ∀ x ∈ I, θ.dpow n x = γ.dpow n x) ∧
      (∀ n, ∀ y ∈ J, θ.dpow n y = ε.dpow n y) := by
  constructor
  · rintro rfl
    exact ⟨γ.sup_dpow_mem_left ε h, γ.sup_dpow_mem_right ε h⟩
  · rintro ⟨hθI, hθJ⟩
    have hspan : I ⊔ J = Ideal.span ((I : Set A) ∪ (J : Set A)) := by
      rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq]
    refine dpow_eq_from_gens (γ.sup ε h) θ hspan fun {n} s hs ↦ ?_
    rcases hs with hsI | hsJ
    · rw [γ.sup_dpow_mem_left ε h n hsI, hθI n s hsI]
    · rw [γ.sup_dpow_mem_right ε h n hsJ, hθJ n s hsJ]

/-- A divided power structure on `I ⊔ J` restricting to `γ` on `I` and `ε` on `J` exists if and
only if `γ` and `ε` agree in all degrees on `I ⊓ J`. -/
theorem exists_sup_iff (γ : DividedPowers I) (ε : DividedPowers J) :
    (∃ θ : DividedPowers (I ⊔ J),
      (∀ n, ∀ x ∈ I, θ.dpow n x = γ.dpow n x) ∧
      (∀ n, ∀ y ∈ J, θ.dpow n y = ε.dpow n y)) ↔
    ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w := by
  constructor
  · rintro ⟨θ, hθI, hθJ⟩ n w ⟨hwI, hwJ⟩
    rw [← hθI n w hwI, hθJ n w hwJ]
  · intro h
    exact ⟨γ.sup ε h, γ.sup_dpow_mem_left ε h, γ.sup_dpow_mem_right ε h⟩

/-- A divided power structure on `I ⊔ J` restricting to `γ` on `I` and `ε` on `J` exists and is
unique if and only if `γ` and `ε` agree in all degrees on `I ⊓ J`. -/
theorem existsUnique_sup_iff (γ : DividedPowers I) (ε : DividedPowers J) :
    (∃! θ : DividedPowers (I ⊔ J),
      (∀ n, ∀ x ∈ I, θ.dpow n x = γ.dpow n x) ∧
      (∀ n, ∀ y ∈ J, θ.dpow n y = ε.dpow n y)) ↔
    ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w := by
  constructor
  · intro huniq
    exact (γ.exists_sup_iff ε).mp huniq.exists
  · intro h
    exact ⟨γ.sup ε h, ⟨γ.sup_dpow_mem_left ε h, γ.sup_dpow_mem_right ε h⟩,
      fun θ hθ ↦ (γ.eq_sup_iff ε h θ).mpr hθ⟩

theorem sup_self_dpow (γ : DividedPowers I) (n : ℕ) (x : A) :
    (γ.sup γ fun _ _ _ ↦ rfl).dpow n x = γ.dpow n x := by
  by_cases hx : x ∈ I
  · exact γ.sup_dpow_mem_left γ (fun _ _ _ ↦ rfl) n hx
  · have hx' : x ∉ I ⊔ I := by rwa [sup_idem]
    rw [(γ.sup γ fun _ _ _ ↦ rfl).dpow_null hx', γ.dpow_null hx]

theorem coincide_bot (γ : DividedPowers I) (n : ℕ) {w : A} (hw : w ∈ I ⊓ (⊥ : Ideal A)) :
    γ.dpow n w = (dividedPowersBot A).dpow n w := by
  rw [inf_bot_eq, Submodule.mem_bot] at hw
  subst hw
  rcases eq_or_ne n 0 with rfl | hn
  · rw [γ.dpow_zero I.zero_mem, (dividedPowersBot A).dpow_zero (Submodule.zero_mem ⊥)]
  · rw [γ.dpow_eval_zero hn, (dividedPowersBot A).dpow_eval_zero hn]

theorem sup_bot_dpow (γ : DividedPowers I) (n : ℕ) (x : A) :
    (γ.sup (dividedPowersBot A) fun m _ hw ↦ γ.coincide_bot m hw).dpow n x = γ.dpow n x := by
  by_cases hx : x ∈ I
  · exact γ.sup_dpow_mem_left (dividedPowersBot A) _ n hx
  · have hx' : x ∉ I ⊔ ⊥ := by rwa [sup_bot_eq]
    rw [(γ.sup (dividedPowersBot A) _).dpow_null hx', γ.dpow_null hx]

theorem sup_comm_dpow (γ : DividedPowers I) (ε : DividedPowers J)
    (h : ∀ n, ∀ w ∈ I ⊓ J, γ.dpow n w = ε.dpow n w) (n : ℕ) (z : A) :
    (γ.sup ε h).dpow n z =
      (ε.sup γ fun m w hw ↦ (h m w (inf_comm (a := J) (b := I) ▸ hw)).symm).dpow n z := by
  by_cases hz : z ∈ I ⊔ J
  · obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    rw [γ.sup_dpow_add ε h n hx hy, add_comm, ε.sup_dpow_add γ _ n hy hx, dpowConv_comm]
  · have hz' : z ∉ J ⊔ I := sup_comm (a := I) (b := J) ▸ hz
    rw [(γ.sup ε h).dpow_null hz, (ε.sup γ _).dpow_null hz']

/-- **Agreement when intersection equals product**
([Stacks Lemma 07GQ(1)](https://stacks.math.columbia.edu/tag/07GQ)): if `I ⊓ J = I * J`, then any
two divided power structures `γ : DividedPowers I` and `ε : DividedPowers J` agree in every degree
on `I ⊓ J`. -/
theorem coincide_of_inf_eq_mul {B : Type*} [CommSemiring B] {I' J' : Ideal B}
    (γ : DividedPowers I') (ε : DividedPowers J')
    (hIJ : I' ⊓ J' = I' * J') (n : ℕ) {w : B} (hw : w ∈ I' ⊓ J') :
    γ.dpow n w = ε.dpow n w := by
  rw [hIJ, ← Ideal.smul_eq_mul] at hw
  exact γ.coincide_on_smul ε hw

/-- **Unconditional gluing when `I ⊓ J = I * J`**
([Stacks Lemma 07GQ](https://stacks.math.columbia.edu/tag/07GQ)): any divided power structures `γ`
on `I` and `ε` on `J` glue uniquely to `I ⊔ J` whenever `I ⊓ J = I * J`. -/
noncomputable def supOfInfEqMul (γ : DividedPowers I) (ε : DividedPowers J)
    (hIJ : I ⊓ J = I * J) : DividedPowers (I ⊔ J) :=
  γ.sup ε fun n _ hw ↦ γ.coincide_of_inf_eq_mul ε hIJ n hw

theorem supOfInfEqMul_eq_sup (γ : DividedPowers I) (ε : DividedPowers J)
    (hIJ : I ⊓ J = I * J) :
    γ.supOfInfEqMul ε hIJ =
      γ.sup ε (fun n _ hw ↦ γ.coincide_of_inf_eq_mul ε hIJ n hw) :=
  (rfl)

theorem supOfInfEqMul_dpow_add (γ : DividedPowers I) (ε : DividedPowers J)
    (hIJ : I ⊓ J = I * J) (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    (γ.supOfInfEqMul ε hIJ).dpow n (x + y) = γ.dpowConv ε n x y :=
  γ.sup_dpow_add ε _ n hx hy

theorem supOfInfEqMul_dpow_mem_left (γ : DividedPowers I) (ε : DividedPowers J)
    (hIJ : I ⊓ J = I * J) (n : ℕ) {x : A} (hx : x ∈ I) :
    (γ.supOfInfEqMul ε hIJ).dpow n x = γ.dpow n x :=
  γ.sup_dpow_mem_left ε _ n hx

theorem supOfInfEqMul_dpow_mem_right (γ : DividedPowers I) (ε : DividedPowers J)
    (hIJ : I ⊓ J = I * J) (n : ℕ) {y : A} (hy : y ∈ J) :
    (γ.supOfInfEqMul ε hIJ).dpow n y = ε.dpow n y :=
  γ.sup_dpow_mem_right ε _ n hy

theorem isDPMorphism_supOfInfEqMul_iff {C : Type*} [CommSemiring C] {K : Ideal C}
    (γ : DividedPowers I) (ε : DividedPowers J) (hIJ : I ⊓ J = I * J)
    (κ : DividedPowers K) (g : A →+* C) :
    IsDPMorphism (γ.supOfInfEqMul ε hIJ) κ g ↔ IsDPMorphism γ κ g ∧ IsDPMorphism ε κ g :=
  γ.isDPMorphism_sup_iff ε _ κ g

end CommRing

end DividedPowers
