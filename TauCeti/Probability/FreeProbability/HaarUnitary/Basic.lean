/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import TauCeti.Probability.FreeProbability.Cumulant.Cyclic
public import TauCeti.Probability.FreeProbability.RDiagonal.Tracial
import TauCeti.Data.Finset.Basic

/-!
# Haar unitary elements and their free cumulants

A unitary element `u` of a star algebra is *Haar unitary* for a linear functional `φ` when `φ` is
normalized (`φ 1 = 1`) and every nonzero integer power of `u` — equivalently every positive power
of `u` and of `star u` — has zero expectation. Because `u` and `star u` are mutual inverses, any
star word in `u` reduces to an integer power determined by the signed count of generators and
adjoints, so all Haar unitaries share the same star distribution, without assuming positivity or a
global trace.

On joint free cumulants, only nonempty even alternating words in `u` and `star u` survive:
a Haar unitary is R-diagonal, and both of its determining sequences are the signed Catalan numbers
`κ_{2(n+1)}(u, star u, …, u, star u) = κ_{2(n+1)}(star u, u, …, star u, u) = (-1)^n C_n`.
The proof avoids generating-function inversion: since `u` and `star u` commute, their joint free
cumulants factor through `Multiplicative ℤ` and are invariant under cyclic rotation; rotating any
nonconstant word brings an opposite adjacent pair `u_0 * u_1 = 1` to the front, and grouping
`{0, 1}` via the product formula for free cumulants together with vanishing of cumulants containing
`1` yields the signed Catalan recurrence.

## Main definitions

* `TauCeti.IsHaarUnitary φ u` — `u` is unitary, `φ 1 = 1`, and `φ (u ^ n) = 0 = φ (star u ^ n)`
  for all `n ≥ 1`.

## Main results

* `TauCeti.IsHaarUnitary.apply_zpow` and `TauCeti.isHaarUnitary_iff_apply_zpow` — integer-power
  characterization `φ (u ^ k) = δ_{k, 0}`.
* `TauCeti.IsHaarUnitary.star`, `TauCeti.IsHaarUnitary.smul`, `TauCeti.IsHaarUnitary.zpow`,
  `TauCeti.IsHaarUnitary.map` — invariance under adjoints, unitary scalar multiples, nonzero
  integer powers, and state-preserving star algebra homomorphisms.
* `TauCeti.IsHaarUnitary.starDistribution_eq` — all Haar unitaries have the same star distribution.
* `TauCeti.IsHaarUnitary.isRDiagonal` and `TauCeti.IsHaarUnitary.rDiagonalDeterminingSequence` —
  Haar unitaries are R-diagonal with determining sequences `(-1) ^ n * catalan n`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Examples 1.14 and
  11.24, and Lecture 15 (Example 15.3).
-/

public section

open Finset

namespace TauCeti

section Semiring

variable {R A B : Type*} [CommSemiring R]
  [Semiring A] [Algebra R A] [StarRing A]
  [Semiring B] [Algebra R B] [StarRing B]
  {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {u : A} {v : B}

/-- An element `u` is *Haar unitary* for `φ` if it is unitary (`star u * u = 1` and
`u * star u = 1`), `φ` is normalized, and all positive powers of `u` and of `star u` lie in the
kernel of `φ`. Neither positivity nor star-preservation of `φ` is assumed. -/
structure IsHaarUnitary (φ : A →ₗ[R] R) (u : A) : Prop where
  /-- The element is unitary. -/
  mem_unitary : u ∈ unitary A
  /-- The functional is normalized. -/
  apply_one : φ 1 = 1
  /-- Positive powers of `u` have zero expectation. -/
  apply_pow_eq_zero {n : ℕ} (hn : n ≠ 0) : φ (u ^ n) = 0
  /-- Positive powers of `star u` have zero expectation. -/
  apply_star_pow_eq_zero {n : ℕ} (hn : n ≠ 0) : φ (star u ^ n) = 0

namespace IsHaarUnitary

/-- A Haar unitary has zero expectation. -/
@[simp]
theorem apply_eq_zero (h : IsHaarUnitary φ u) : φ u = 0 := by
  simpa using h.apply_pow_eq_zero one_ne_zero

/-- The adjoint of a Haar unitary has zero expectation. -/
theorem apply_star_eq_zero (h : IsHaarUnitary φ u) : φ (star u) = 0 := by
  simpa using h.apply_star_pow_eq_zero one_ne_zero

/-- The expectation of `u ^ n` for a Haar unitary `u` is `1` at `0` and `0` elsewhere. -/
theorem apply_pow (h : IsHaarUnitary φ u) (n : ℕ) :
    φ (u ^ n) = if n = 0 then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [h.apply_one]
  · simp [hn, h.apply_pow_eq_zero hn]

/-- The expectation of `star u ^ n` for a Haar unitary `u` is `1` at `0` and `0` elsewhere. -/
theorem apply_star_pow (h : IsHaarUnitary φ u) (n : ℕ) :
    φ (star u ^ n) = if n = 0 then 1 else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [h.apply_one]
  · simp [hn, h.apply_star_pow_eq_zero hn]

/-- The expectation of any integer power of a Haar unitary in `unitary A` is `1` at `0` and `0`
elsewhere. -/
theorem apply_zpow (h : IsHaarUnitary φ u) (k : ℤ) :
    φ (((⟨u, h.mem_unitary⟩ : unitary A) ^ k : unitary A) : A) = if k = 0 then 1 else 0 := by
  cases k with
  | ofNat n =>
    simpa [SubmonoidClass.coe_pow] using h.apply_pow n
  | negSucc n =>
    have hinv : (((⟨u, h.mem_unitary⟩ : unitary A) ^ Int.negSucc n : unitary A) : A) =
        star u ^ (n + 1) := by
      rw [zpow_negSucc, ← inv_pow, SubmonoidClass.coe_pow, ← Unitary.star_eq_inv, Unitary.coe_star]
    rw [hinv, h.apply_star_pow]
    simp

/-- Adjoint preserves Haar unitarity. -/
theorem star (h : IsHaarUnitary φ u) : IsHaarUnitary φ (Star.star u) where
  mem_unitary := Unitary.star_mem h.mem_unitary
  apply_one := h.apply_one
  apply_pow_eq_zero hn := h.apply_star_pow_eq_zero hn
  apply_star_pow_eq_zero hn := by simpa only [star_star] using h.apply_pow_eq_zero hn

/-- Scaling a Haar unitary by a unitary scalar preserves Haar unitarity. -/
theorem smul [StarMul R] [StarModule R A] (h : IsHaarUnitary φ u) {z : R}
    (hz : z ∈ unitary R) : IsHaarUnitary φ (z • u) where
  mem_unitary := by
    rw [Unitary.mem_iff] at hz ⊢
    rw [star_smul, smul_mul_smul_comm, smul_mul_smul_comm, hz.1, hz.2,
      Unitary.star_mul_self_of_mem h.mem_unitary, Unitary.mul_star_self_of_mem h.mem_unitary,
      one_smul, and_self]
  apply_one := h.apply_one
  apply_pow_eq_zero hn := by
    rw [smul_pow, map_smul, h.apply_pow_eq_zero hn, smul_zero]
  apply_star_pow_eq_zero hn := by
    rw [star_smul, smul_pow, map_smul, h.apply_star_pow_eq_zero hn, smul_zero]

/-- Every nonzero integer power of a Haar unitary is again a Haar unitary. -/
theorem zpow (h : IsHaarUnitary φ u) {k : ℤ} (hk : k ≠ 0) :
    IsHaarUnitary φ (((⟨u, h.mem_unitary⟩ : unitary A) ^ k : unitary A) : A) where
  mem_unitary := Subtype.prop _
  apply_one := h.apply_one
  apply_pow_eq_zero {n} hn := by
    have hpow : ((((⟨u, h.mem_unitary⟩ : unitary A) ^ k : unitary A) : A) ^ n) =
        (((⟨u, h.mem_unitary⟩ : unitary A) ^ (k * (n : ℤ)) : unitary A) : A) := by
      rw [← SubmonoidClass.coe_pow, ← zpow_natCast, ← zpow_mul]
    rw [hpow, h.apply_zpow, ite_eq_right (mul_ne_zero hk (Nat.cast_ne_zero.2 hn))]
  apply_star_pow_eq_zero {n} hn := by
    have hpow : (Star.star (((⟨u, h.mem_unitary⟩ : unitary A) ^ k : unitary A) : A)) ^ n =
        (((⟨u, h.mem_unitary⟩ : unitary A) ^ (-(k * (n : ℤ))) : unitary A) : A) := by
      rw [← Unitary.coe_star, Unitary.star_eq_inv, ← SubmonoidClass.coe_pow, ← zpow_natCast,
        ← zpow_neg, ← zpow_mul]
      simp [neg_mul]
    rw [hpow, h.apply_zpow, ite_eq_right (neg_ne_zero.2 (mul_ne_zero hk (Nat.cast_ne_zero.2 hn)))]

/-- A state-preserving star algebra homomorphism sends a Haar unitary to a Haar unitary. -/
theorem map (h : IsHaarUnitary φ u) (f : A →⋆ₐ[R] B)
    (hf : ψ.comp f.toAlgHom.toLinearMap = φ) : IsHaarUnitary ψ (f u) where
  mem_unitary := by
    rw [Unitary.mem_iff, ← map_star, ← map_mul, ← map_mul,
      Unitary.star_mul_self_of_mem h.mem_unitary, Unitary.mul_star_self_of_mem h.mem_unitary,
      map_one, and_self]
  apply_one := by simpa [← hf] using h.apply_one
  apply_pow_eq_zero hn := by
    have := h.apply_pow_eq_zero hn
    rwa [← hf, LinearMap.comp_apply, AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom,
      map_pow] at this
  apply_star_pow_eq_zero hn := by
    have := h.apply_star_pow_eq_zero hn
    rwa [← hf, LinearMap.comp_apply, AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom,
      map_pow, map_star] at this

end IsHaarUnitary

/-- An element's adjoint is Haar unitary if and only if the element itself is Haar unitary. -/
@[simp]
theorem isHaarUnitary_star_iff : IsHaarUnitary φ (star u) ↔ IsHaarUnitary φ u :=
  ⟨fun h => by simpa only [star_star] using h.star, IsHaarUnitary.star⟩

/-- A unitary element `u : unitary A` is Haar unitary iff `φ (u ^ k) = δ_{k, 0}` for all `k : ℤ`. -/
theorem isHaarUnitary_iff_apply_zpow {u : unitary A} :
    IsHaarUnitary φ (u : A) ↔
      ∀ k : ℤ, φ (((u ^ k : unitary A) : A)) = if k = 0 then 1 else 0 := by
  refine ⟨fun h => h.apply_zpow, fun h => ⟨u.2, by simpa using h 0, fun {n} hn => ?_,
      fun {n} hn => ?_⟩⟩
  · simpa [SubmonoidClass.coe_pow, hn] using h n
  · have hneg := h (-(n : ℤ))
    have hinv : (((u ^ (-(n : ℤ)) : unitary A) : A)) = star (u : A) ^ n := by
      rw [zpow_neg, zpow_natCast, ← inv_pow, SubmonoidClass.coe_pow, ← Unitary.star_eq_inv,
        Unitary.coe_star]
    rwa [hinv, ite_eq_right (neg_ne_zero.2 (Nat.cast_ne_zero.2 hn))] at hneg

/-- For a star-preserving functional, vanishing on positive powers of `u` already implies vanishing
on positive powers of `star u`. -/
theorem isHaarUnitary_of_apply_pow_eq_zero [StarAddMonoid R] (hφ : ∀ x, φ (star x) = star (φ x))
    (hu : u ∈ unitary A) (hone : φ 1 = 1) (hpow : ∀ {n : ℕ}, n ≠ 0 → φ (u ^ n) = 0) :
    IsHaarUnitary φ u where
  mem_unitary := hu
  apply_one := hone
  apply_pow_eq_zero hn := hpow hn
  apply_star_pow_eq_zero hn := by rw [← star_pow, hφ, hpow hn, star_zero]

/-- Any list product of `u` and `star u` for `u : unitary A` equals `u` raised to the signed count
of `false` (`+1`) and `true` (`-1`) labels. -/
private theorem prod_map_ite_star_eq_zpow (u : unitary A) (l : List Bool) :
    (l.map fun b => if b then star (u : A) else (u : A)).prod =
      (((u ^ (l.map fun b => if b then (-1 : ℤ) else 1).sum : unitary A) : A)) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, zpow_add,
      Submonoid.coe_mul]
    cases b <;> simp [← Unitary.star_eq_inv]

namespace IsHaarUnitary

/-- The moment of any star word in a Haar unitary is `1` when generators and adjoints appear an
equal number of times and `0` otherwise. -/
theorem apply_list_prod_withStar (h : IsHaarUnitary φ u) (w : List (Unit × Bool)) :
    φ (w.map (StarPolynomial.withStar (fun _ : Unit => u))).prod =
      if (w.map fun p => if p.2 then (-1 : ℤ) else 1).sum = 0 then 1 else 0 := by
  have hmap : w.map (StarPolynomial.withStar (fun _ : Unit => u)) =
      (w.map Prod.snd).map (fun b => if b then Star.star u else u) := by
    simp [List.map_map, StarPolynomial.withStar_def]
  rw [hmap, prod_map_ite_star_eq_zpow ⟨u, h.mem_unitary⟩, h.apply_zpow, List.map_map]
  rfl

/-- All Haar unitaries, even in different algebras, have the same star distribution. -/
theorem starDistribution_eq [StarRing R] [StarModule R A] [StarModule R B]
    (h : IsHaarUnitary φ u) (h' : IsHaarUnitary ψ v) :
    starDistribution φ (fun _ : Unit => u) = starDistribution ψ (fun _ : Unit => v) := by
  rw [starDistribution_eq_iff]
  intro w
  rw [h.apply_list_prod_withStar, h'.apply_list_prod_withStar]

/-- A unitary element with the same star distribution as a Haar unitary is itself Haar unitary.
Unitarity of `v` cannot be dropped when `ψ` is not faithful. -/
theorem of_starDistribution_eq [StarRing R] [StarModule R A] [StarModule R B]
    (h : IsHaarUnitary φ u) (hv : v ∈ unitary B)
    (heq : starDistribution φ (fun _ : Unit => u) = starDistribution ψ (fun _ : Unit => v)) :
    IsHaarUnitary ψ v where
  mem_unitary := hv
  apply_one := by
    have h1 := (starDistribution_eq_iff.1 heq) []
    simpa using h1.symm.trans h.apply_one
  apply_pow_eq_zero {n} hn := by
    have hw := (starDistribution_eq_iff.1 heq) (List.replicate n ((), false))
    simp only [List.map_replicate, StarPolynomial.withStar_def, List.prod_replicate] at hw
    exact hw.symm.trans (h.apply_pow_eq_zero hn)
  apply_star_pow_eq_zero {n} hn := by
    have hw := (starDistribution_eq_iff.1 heq) (List.replicate n ((), true))
    simp only [List.map_replicate, StarPolynomial.withStar_def, List.prod_replicate] at hw
    exact hw.symm.trans (h.apply_star_pow_eq_zero hn)

end IsHaarUnitary

end Semiring

section CommRing

variable {R A : Type*} [CommRing R] [Semiring A] [Algebra R A] [StarRing A]
  {φ : A →ₗ[R] R} {u : A}

/-- Along any finite set `s` of positions, the moment of a star word in a Haar unitary is `1` when
its signed exponent sum vanishes and `0` otherwise. -/
private theorem IsHaarUnitary.apply_prod_sort_ite_star {α : Type*} [LinearOrder α]
    (h : IsHaarUnitary φ u) (w : α → Bool) (s : Finset α) :
    φ ((s.sort.map fun x => if w x then Star.star u else u).prod) =
      if (∑ x ∈ s, if w x then (-1 : ℤ) else 1) = 0 then 1 else 0 := by
  have hmap : (s.sort.map fun x => if w x then Star.star u else u) =
      (s.sort.map w).map (fun b => if b then Star.star u else u) := by
    rw [List.map_map]; rfl
  have hsum : ((s.sort.map w).map fun b => if b then (-1 : ℤ) else 1).sum =
      ∑ x ∈ s, if w x then (-1 : ℤ) else 1 := by
    rw [List.map_map, ← Multiset.sum_coe, ← Multiset.map_coe, s.sort_eq]
    rfl
  rw [hmap, prod_map_ite_star_eq_zpow ⟨u, h.mem_unitary⟩, hsum, h.apply_zpow]

/-- Joint free cumulants of `u` and `star u` for a unitary `u` factor through the commutative group
`Multiplicative ℤ` and are therefore invariant under every cyclic rotation, without assuming a
global trace on `φ`. -/
private theorem freeCumulant_ite_star_comp_finRotate_pow (hu : u ∈ unitary A) {n : ℕ}
    (w : Fin n → Bool) (k : ℕ) :
    freeCumulant φ ((fun i => if w i then star u else u) ∘ ⇑(finRotate n ^ k)) univ =
      freeCumulant φ (fun i => if w i then star u else u) univ := by
  let ι : Multiplicative ℤ →* A :=
    (unitary A).subtype.comp (zpowersHom (unitary A) ⟨u, hu⟩)
  let b : Fin n → Multiplicative ℤ := fun i =>
    Multiplicative.ofAdd (if w i then (-1 : ℤ) else 1)
  have hb : (fun i => if w i then star u else u) = ι ∘ b := by
    funext i
    dsimp [ι, b]
    cases w i <;> simp [← Unitary.star_eq_inv]
  have hpull (c : Fin n → Multiplicative ℤ) :
      freeCumulant φ (ι ∘ c) univ = freeCumulant (φ ∘ ι) c univ := by
    simp only [freeCumulant_eq_sum_mu_mul_partitionMoment, partitionMoment_def]
    refine sum_congr rfl fun π _ => congrArg (_ * ·) (prod_congr rfl fun B _ => ?_)
    dsimp only [Function.comp_apply]
    congr 1
    rw [← List.map_map, map_list_prod]
  rw [hb, Function.comp_assoc, hpull,
    freeCumulant_comp_finRotate_pow (fun x y => by dsimp; rw [mul_comm]) b k, ← hpull]

/-- A nonempty constant star word in a Haar unitary has zero free cumulant. -/
private theorem IsHaarUnitary.freeCumulant_ite_star_eq_zero_of_const (h : IsHaarUnitary φ u)
    {n : ℕ} (hn : n ≠ 0) {w : Fin n → Bool} (b : Bool) (hw : ∀ i, w i = b) :
    freeCumulant φ (fun i => if w i then Star.star u else u) univ = 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  rw [freeCumulant_eq_sum_mu_mul_partitionMoment]
  refine sum_eq_zero fun π _ => mul_eq_zero_of_right _ ?_
  obtain ⟨B, hB⟩ := π.1.parts_nonempty univ_nonempty.ne_empty
  rw [partitionMoment_def]
  refine prod_eq_zero hB ?_
  rw [h.apply_prod_sort_ite_star, ite_eq_right_iff]
  intro hsum
  have hBne := π.1.nonempty_of_mem_parts hB
  simp only [hw, sum_const, nsmul_eq_mul] at hsum
  cases b <;> simp [hBne.card_pos.ne'] at hsum

/-- An odd-length star word in a Haar unitary has zero free cumulant: every partition of an odd
set has an odd-sized part, whose signed exponent sum is odd and therefore nonzero. -/
private theorem IsHaarUnitary.freeCumulant_ite_star_eq_zero_of_odd (h : IsHaarUnitary φ u)
    {n : ℕ} (hodd : Odd n) (w : Fin n → Bool) :
    freeCumulant φ (fun i => if w i then Star.star u else u) univ = 0 := by
  rw [freeCumulant_eq_sum_mu_mul_partitionMoment]
  refine sum_eq_zero fun π _ => mul_eq_zero_of_right _ ?_
  have hex : ∃ B ∈ π.1.parts, Odd #B := by
    by_contra! hall
    have hsum : Even (∑ B ∈ π.1.parts, #B) :=
      even_sum _ fun B hB => Nat.not_odd_iff_even.1 (hall B hB)
    rw [Finpartition.sum_card_parts, card_univ, Fintype.card_fin] at hsum
    exact Nat.not_even_iff_odd.2 hodd hsum
  obtain ⟨B, hB, hBodd⟩ := hex
  rw [partitionMoment_def]
  refine prod_eq_zero hB ?_
  rw [h.apply_prod_sort_ite_star, ite_eq_right_iff]
  intro hsum
  have hmod : (∑ x ∈ B, if w x then (-1 : ℤ) else 1) % 2 = (#B : ℤ) % 2 := by
    rw [sum_int_mod, card_eq_sum_ones, Nat.cast_sum, sum_int_mod]
    refine congrArg (· % 2) (sum_congr rfl fun x _ => ?_)
    cases w x <;> decide
  obtain ⟨k, hk⟩ := hBodd
  omega

/-- Pulling back `⊥` along `Fin.cases 0 id : Fin (m + 2) → Fin (m + 1)` gives the partition
pairing `0` and `1` and leaving all other positions as singletons. -/
private theorem comap_cases_bot_eq_pairPartition {m : ℕ}
    (hf : MonotoneOn (Fin.cases 0 id : Fin (m + 2) → Fin (m + 1))
      ((univ : Finset (Fin (m + 2))) : Set (Fin (m + 2)))) :
    NoncrossingPartition.comap hf ⊥ =
      ⟨Finpartition.pairPartition univ (0 : Fin (m + 2)) 1 (subset_univ _),
        Finpartition.isNoncrossing_pairPartition
          (subset_univ ({(0 : Fin (m + 2)), 1} : Finset (Fin (m + 2))))⟩ := by
  let f : Fin (m + 2) → Fin (m + 1) := Fin.cases 0 id
  have hpair : ({(0 : Fin (m + 2)), 1} : Finset (Fin (m + 2))) ⊆ univ := subset_univ _
  refine Subtype.ext <| le_antisymm ?_ (Finpartition.pairPartition_le ?_)
  · refine Finpartition.le_iff_forall_part_subset.2 fun x w hw => ?_
    rw [NoncrossingPartition.coe_comap, NoncrossingPartition.coe_bot,
      Finpartition.part_comap_bot (mem_univ x), mem_filter] at hw
    rcases eq_or_ne w x with rfl | hne
    · exact Finpartition.mem_part_self _ |>.2 (mem_univ w)
    have h0 : ∀ {z : Fin (m + 2)}, f z = 0 ↔ z = 0 ∨ z = 1 := by
      intro z; cases z using Fin.cases with
      | zero => exact iff_of_true rfl (Or.inl rfl)
      | succ j =>
        cases j using Fin.cases with
        | zero => exact iff_of_true rfl (Or.inr rfl)
        | succ k =>
          exact iff_of_false (Fin.succ_ne_zero k) (by
            rintro (h | h)
            exacts [Fin.succ_ne_zero _ h, Fin.succ_ne_zero k (Fin.succ_inj.1 h)])
    have hwx : (w = 0 ∨ w = 1) ∧ (x = 0 ∨ x = 1) := by
      by_cases hx0 : f x = 0
      · exact ⟨h0.1 (hw.2.trans hx0), h0.1 hx0⟩
      · exfalso
        cases w using Fin.cases with
        | zero => exact hx0 hw.2.symm
        | succ k =>
          cases x using Fin.cases with
          | zero => exact hx0 rfl
          | succ j => exact hne (congrArg Fin.succ hw.2)
    have h10 : (Finpartition.pairPartition univ (0 : Fin (m + 2)) 1 hpair).part 1 =
        (Finpartition.pairPartition univ 0 1 hpair).part 0 :=
      ((Finpartition.pairPartition univ 0 1 hpair).mem_part_iff_part_eq_part
        (mem_univ 1) (mem_univ 0)).1
        (by rw [Finpartition.part_pairPartition]; exact mem_insert_of_mem (mem_singleton_self _))
    rcases hwx.2 with rfl | rfl <;> simp only [h10, Finpartition.part_pairPartition] <;>
      rcases hwx.1 with rfl | rfl <;> simp
  · rw [NoncrossingPartition.coe_comap, NoncrossingPartition.coe_bot,
      Finpartition.part_comap_bot (mem_univ 0), mem_filter]
    exact ⟨mem_univ 1, rfl⟩

/-- If the parts of `x ∈ NC(m + 2)` through `0` and `1` are distinct and cover `univ`, then the
part through `1` is the interval `{1, …, max (x.1.part 1)}`. -/
private theorem filter_erase_zero_le_max'_eq_part {m : ℕ}
    {x : NoncrossingPartition (univ : Finset (Fin (m + 2)))}
    (hu : x.1.part 0 ∪ x.1.part 1 = univ) (hne : x.1.part 0 ≠ x.1.part 1) :
    {z ∈ (univ : Finset (Fin (m + 2))).erase 0 |
      z ≤ (x.1.part 1).max' (x.1.part_nonempty.2 (mem_univ 1))} = x.1.part 1 := by
  have h01 : (0 : Fin (m + 2)) ∉ x.1.part 1 := fun h =>
    hne ((x.1.mem_part_iff_part_eq_part (mem_univ 0) (mem_univ 1)).1 h)
  set y := (x.1.part 1).max' (x.1.part_nonempty.2 (mem_univ 1))
  have hy1 : y ∈ x.1.part 1 := max'_mem _ _
  ext z
  simp only [mem_filter, mem_erase, mem_univ, and_true]
  refine ⟨fun ⟨hz0, hzy⟩ => by_contra fun hz1 => ?_,
    fun hz => ⟨fun h => h01 (h ▸ hz), le_max' _ _ hz⟩⟩
  have hz0' : z ∈ x.1.part 0 := (mem_union.1 (hu.symm ▸ mem_univ z)).resolve_right hz1
  have h1le : (1 : Fin (m + 2)) ≤ z := Nat.pos_of_ne_zero (Fin.val_ne_of_ne hz0)
  have h1z : (1 : Fin (m + 2)) < z := h1le.lt_of_ne
    fun h => hz1 (h ▸ x.1.mem_part_self.2 (mem_univ 1))
  exact hne (x.2.part_eq_part (mem_univ 0) (mem_univ 1)
    ((x.1.mem_part_iff_part_eq_part (mem_univ z) (mem_univ 0)).1 hz0').symm
    ((x.1.mem_part_iff_part_eq_part (mem_univ y) (mem_univ 1)).1 hy1).symm
    Fin.zero_lt_one h1z (hzy.lt_of_ne fun h => hz1 (h ▸ hy1)))

private theorem splitPartition_filter_erase_zero_eq {m : ℕ}
    {x : NoncrossingPartition (univ : Finset (Fin (m + 2)))}
    (hu : x.1.part 0 ∪ x.1.part 1 = univ) (hne : x.1.part 0 ≠ x.1.part 1)
    (hCne : ({z ∈ (univ : Finset (Fin (m + 2))).erase 0 |
      z ≤ (x.1.part 1).max' (x.1.part_nonempty.2 (mem_univ 1))}).Nonempty) :
    Finpartition.splitPartition univ _ hCne (subset_univ _) = x.1 := by
  have hCx := filter_erase_zero_le_max'_eq_part hu hne
  refine Finpartition.ext_of_part fun z hz => ?_
  by_cases hzC : z ∈ x.1.part 1
  · rw [Finpartition.part_splitPartition_of_mem (hCx.symm ▸ hzC), hCx,
      (x.1.mem_part_iff_part_eq_part hz (mem_univ 1)).1 hzC]
  · rw [Finpartition.part_splitPartition_of_notMem hz (hCx.symm ▸ hzC), hCx,
      ← x.1.part_eq_sdiff_part hu hne,
      (x.1.mem_part_iff_part_eq_part hz (mem_univ 0)).1
        ((mem_union.1 (hu.symm ▸ hz)).resolve_right hzC)]

/-- The non-top partitions `x ∈ NC(m + 2)` whose join with `{0, 1}` is `⊤` correspond
bijectively to `y ∈ univ.erase 0` via `splitPartition` on `{1, …, y}`. -/
private theorem sum_erase_top_sup_pairPartition_eq {m : ℕ} (g : Finset (Fin (m + 2)) → R) :
    ∑ x ∈ ({x : NoncrossingPartition (univ : Finset (Fin (m + 2))) |
        x ⊔ ⟨Finpartition.pairPartition univ (0 : Fin (m + 2)) 1 (subset_univ _),
          Finpartition.isNoncrossing_pairPartition
            (subset_univ ({(0 : Fin (m + 2)), 1} : Finset (Fin (m + 2))))⟩ = ⊤} :
          Finset _).erase ⊤,
        ∏ B ∈ x.1.parts, g B =
      ∑ y ∈ (univ : Finset (Fin (m + 2))).erase 0,
        g {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y} *
          g (univ \ {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y}) := by
  have hmin₁ : ∀ z ∈ (univ : Finset (Fin (m + 2))), (0 : Fin (m + 2)) ≤ z :=
    fun _ _ => Fin.zero_le _
  have hadj : ∀ z ∈ (univ : Finset (Fin (m + 2))), z ≤ 0 ∨ 1 ≤ z := fun z _ =>
    if hz : z = 0 then Or.inl hz.le else Or.inr (Nat.pos_of_ne_zero (Fin.val_ne_of_ne hz))
  have hC {y : Fin (m + 2)} (hy : y ∈ (univ : Finset (Fin (m + 2))).erase 0) :
      y ∈ {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y} := mem_filter.2 ⟨hy, le_rfl⟩
  have hCne {y : Fin (m + 2)} (hy : y ∈ (univ : Finset (Fin (m + 2))).erase 0) :
      ({z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y}).Nonempty := ⟨y, hC hy⟩
  have hm₂C {y : Fin (m + 2)} (hy : y ∈ (univ : Finset (Fin (m + 2))).erase 0) :
      (1 : Fin (m + 2)) ∈ {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y} :=
    mem_filter.2 ⟨mem_erase.2 ⟨Fin.zero_ne_one.symm, mem_univ _⟩,
      Nat.pos_of_ne_zero (Fin.val_ne_of_ne (mem_erase.1 hy).1)⟩
  have hm₁C (y : Fin (m + 2)) :
      (0 : Fin (m + 2)) ∉ {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y} :=
    fun h0 => (mem_erase.1 (mem_filter.1 h0).1).1 rfl
  symm
  refine sum_bij'
    (fun y hy => ⟨Finpartition.splitPartition univ _ (hCne hy) (subset_univ _),
      Finpartition.isNoncrossing_splitPartition (Finset.convex_filter_erase_le hmin₁ y)⟩)
    (fun x _ => (x.1.part 1).max' (x.1.part_nonempty.2 (mem_univ 1)))
    (fun y hy => NoncrossingPartition.splitPartition_mem_erase_top_sup_pairPartition
      (subset_univ _) (hCne hy) (subset_univ _) (Finset.convex_filter_erase_le hmin₁ y)
      (hm₂C hy) (hm₁C y))
    (fun x hx => by
      obtain ⟨_, hne⟩ := NoncrossingPartition.part_union_eq_of_sup_pairPartition_eq_top
        (subset_univ _) (Fin.zero_le _) hadj (mem_erase.1 hx).1 (mem_filter.1 (mem_erase.1 hx).2).2
      have hmax := max'_mem (x.1.part 1) (x.1.part_nonempty.2 (mem_univ 1))
      exact mem_erase.2 ⟨fun h0 => hne ((x.1.mem_part_iff_part_eq_part (mem_univ 0)
        (mem_univ 1)).1 (h0 ▸ hmax)), mem_univ _⟩)
    (fun y hy => by
      change ((Finpartition.splitPartition univ _ (hCne hy) (subset_univ _)).part 1).max' _ = y
      simp only [Finpartition.part_splitPartition_of_mem (hm₂C hy)]
      exact le_antisymm (max'_le _ _ _ fun z hz => (mem_filter.1 hz).2) (le_max' _ _ (hC hy)))
    (fun x hx => by
      obtain ⟨hu, hne⟩ := NoncrossingPartition.part_union_eq_of_sup_pairPartition_eq_top
        (subset_univ _) (Fin.zero_le _) hadj (mem_erase.1 hx).1 (mem_filter.1 (mem_erase.1 hx).2).2
      exact Subtype.ext (splitPartition_filter_erase_zero_eq hu hne _))
    (fun y hy => by
      have hsC : (univ \ {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y}).Nonempty :=
        ⟨0, mem_sdiff.2 ⟨mem_univ 0, hm₁C y⟩⟩
      change _ = ∏ B ∈ (Finpartition.splitPartition univ _ (hCne hy) (subset_univ _)).parts, g B
      rw [Finpartition.parts_splitPartition hsC,
        prod_pair fun heq => (mem_sdiff.1 (heq ▸ hC hy)).2 (hC hy)])

/-- Grouping the first two positions `0` and `1` of `Fin (m + 2)` (`m ≥ 1`) when `w 0 ≠ w 1`
produces a unit letter in a word of length `m + 1 ≥ 2`, yielding the quadratic recurrence for Haar
unitary cumulants. -/
private theorem IsHaarUnitary.freeCumulant_ite_star_eq_neg_sum (h : IsHaarUnitary φ u)
    {m : ℕ} (hm : m ≠ 0) {w : Fin (m + 2) → Bool} (hw01 : w 0 ≠ w 1) :
    let a : Fin (m + 2) → A := fun i => if w i then Star.star u else u
    freeCumulant φ a univ =
      -∑ y ∈ (univ : Finset (Fin (m + 2))).erase 0,
        freeCumulant φ a {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y} *
          freeCumulant φ a (univ \ {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y}) := by
  intro a
  let f : Fin (m + 2) → Fin (m + 1) := Fin.cases 0 id
  have hf : MonotoneOn f ((univ : Finset (Fin (m + 2))) : Set (Fin (m + 2))) :=
    fun i _ j _ hij => by
      cases i using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ i =>
        cases j using Fin.cases with
        | zero => exact absurd hij (Fin.not_lt.2 (Fin.zero_le _))
        | succ j => exact Fin.succ_le_succ_iff.1 hij
  have himg : (univ : Finset (Fin (m + 2))).image f = univ := by
    ext j; exact ⟨fun _ => mem_univ _, fun _ => mem_image.2 ⟨j.succ, mem_univ _, rfl⟩⟩
  have hfib0 : fiberProd a univ f 0 = 1 := by
    have hset : {x ∈ (univ : Finset (Fin (m + 2))) | f x = 0} = {0, 1} := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, f]
      cases x using Fin.cases with
      | zero => exact iff_of_true rfl (Or.inl rfl)
      | succ j =>
        cases j using Fin.cases with
        | zero => exact iff_of_true rfl (Or.inr rfl)
        | succ k =>
          exact iff_of_false (Fin.succ_ne_zero k) (by
            rintro (h | h)
            exacts [Fin.succ_ne_zero _ h, Fin.succ_ne_zero k (Fin.succ_inj.1 h)])
    rw [fiberProd_def, hset, sort_pair (· ≤ ·) (Fin.zero_le _) Fin.zero_ne_one]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, a]
    cases h0 : w 0 <;> cases h1 : w 1
    · exact absurd (h0.trans h1.symm) hw01
    · exact Unitary.mul_star_self_of_mem h.mem_unitary
    · exact Unitary.star_mul_self_of_mem h.mem_unitary
    · exact absurd (h0.trans h1.symm) hw01
  have hzero : freeCumulant φ (fiberProd a univ f)
      ((univ : Finset (Fin (m + 2))).image f) = 0 := by
    rw [himg]
    exact freeCumulant_eq_zero_of_apply_eq_one φ _ h.apply_one hfib0 (mem_univ 0) (by simp; omega)
  rw [freeCumulant_fiberProd_eq_sum_prod φ a hf, comap_cases_bot_eq_pairPartition hf] at hzero
  have htop_mem : (⊤ : NoncrossingPartition (univ : Finset (Fin (m + 2)))) ∈
      ({x | x ⊔ ⟨Finpartition.pairPartition univ (0 : Fin (m + 2)) 1 (subset_univ _),
        Finpartition.isNoncrossing_pairPartition
          (subset_univ ({(0 : Fin (m + 2)), 1} : Finset (Fin (m + 2))))⟩ = ⊤} : Finset _) := by
    simp
  rw [← add_sum_erase _ _ htop_mem, NoncrossingPartition.coe_top,
    Finpartition.parts_top univ_nonempty.ne_empty, prod_singleton,
    sum_erase_top_sup_pairPartition_eq, add_eq_zero_iff_eq_neg] at hzero
  exact hzero

private def sliceLeft {m : ℕ} (y : Fin (m + 2)) (i : Fin (y : ℕ)) : Fin (m + 2) :=
  ⟨(i : ℕ) + 1, by omega⟩

private def sliceRight {m : ℕ} (y : Fin (m + 2)) (i : Fin (m + 2 - (y : ℕ))) : Fin (m + 2) :=
  if (i : ℕ) = 0 then 0 else ⟨(y : ℕ) + (i : ℕ), by omega⟩

omit [StarRing A] in
private theorem freeCumulant_sliceLeft {m : ℕ} (a : Fin (m + 2) → A) (y : Fin (m + 2)) :
    freeCumulant φ a {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y} =
      freeCumulant φ (a ∘ sliceLeft y) univ := by
  have hsm : StrictMonoOn (sliceLeft y) ((univ : Finset (Fin (y : ℕ))) : Set (Fin (y : ℕ))) :=
    fun i _ j _ hij => Fin.mk_lt_mk.2 (Nat.add_lt_add_right hij 1)
  have himg : (univ : Finset (Fin (y : ℕ))).image (sliceLeft y) =
      {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y} := by
    ext z
    simp only [sliceLeft, mem_image, mem_filter, mem_erase, mem_univ, and_true, true_and,
      Fin.le_def]
    refine ⟨?_, fun ⟨hz0, _⟩ => ?_⟩
    · rintro ⟨i, rfl⟩
      have := i.2
      exact ⟨by simp [Fin.ext_iff], by dsimp; omega⟩
    · have hzpos : 0 < (z : ℕ) := Nat.pos_of_ne_zero (Fin.val_ne_of_ne hz0)
      exact ⟨⟨(z : ℕ) - 1, by omega⟩, Fin.ext (by dsimp; omega)⟩
  rw [← himg, ← freeCumulant_comp_of_strictMonoOn φ hsm a]

omit [StarRing A] in
private theorem freeCumulant_sliceRight {m : ℕ} (a : Fin (m + 2) → A) {y : Fin (m + 2)}
    (hy : y ≠ 0) :
    freeCumulant φ a (univ \ {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y}) =
      freeCumulant φ (a ∘ sliceRight y) univ := by
  have hypos : 0 < (y : ℕ) := Nat.pos_of_ne_zero (Fin.val_ne_of_ne hy)
  have hsm : StrictMonoOn (sliceRight y)
      ((univ : Finset (Fin (m + 2 - (y : ℕ)))) : Set (Fin (m + 2 - (y : ℕ)))) :=
    fun i _ j _ hij => by
      have : (i : ℕ) < (j : ℕ) := hij
      have := j.2
      simp only [sliceRight]
      split_ifs <;> simp only [Fin.lt_def, Fin.val_zero] <;> omega
  have himg : (univ : Finset (Fin (m + 2 - (y : ℕ)))).image (sliceRight y) =
      univ \ {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y} := by
    ext z
    simp only [sliceRight, mem_image, mem_sdiff, mem_filter, mem_erase, mem_univ, and_true,
      true_and, Fin.le_def, not_and]
    refine ⟨?_, fun h => ?_⟩
    · rintro ⟨i, rfl⟩
      split_ifs with hi0
      · exact fun h0 => absurd rfl h0
      · exact fun _ => by dsimp; omega
    · by_cases hz0 : z = 0
      · subst hz0
        exact ⟨⟨0, by omega⟩, by simp⟩
      · have hgt : (y : ℕ) < (z : ℕ) := Nat.lt_of_not_ge (h hz0)
        refine ⟨⟨(z : ℕ) - (y : ℕ), by omega⟩, ?_⟩
        rw [ite_eq_right (by dsimp; omega)]
        exact Fin.ext (by dsimp; omega)
  rw [← himg, ← freeCumulant_comp_of_strictMonoOn φ hsm a]

/-- At an even cut `y = 2 * (j + 1)`, `w` is an `rDiagonalWord` iff both slices `w ∘ sliceLeft y`
and `w ∘ sliceRight y` are `rDiagonalWord`s (given `w 0 ≠ w 1`). -/
private theorem rDiagonalWord_slice_iff {m k' j : ℕ} (hk : m + 2 = 2 * (k' + 2)) (hj : j < k' + 1)
    {w : Fin (m + 2) → Bool} (hw01 : w 0 ≠ w 1) :
    let y : Fin (m + 2) := ⟨2 * (j + 1), by omega⟩
    ((Even (y : ℕ) ∧ ∃ c₁, ∀ i, (w ∘ sliceLeft y) i = rDiagonalWord c₁ (y : ℕ) i) ∧
      (Even (m + 2 - (y : ℕ)) ∧
        ∃ c₂, ∀ i, (w ∘ sliceRight y) i = rDiagonalWord c₂ (m + 2 - (y : ℕ)) i)) ↔
      (Even (m + 2) ∧ ∃ c, ∀ x, w x = rDiagonalWord c (m + 2) x) := by
  intro y
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨-, c₁, h₁⟩, ⟨-, c₂, h₂⟩⟩
    have hw1 : w 1 = c₁ := by
      simpa [sliceLeft, rDiagonalWord_apply] using h₁ ⟨0, by dsimp [y]; omega⟩
    have hw0 : w 0 = c₂ := by
      simpa [sliceRight, rDiagonalWord_apply] using h₂ ⟨0, by dsimp [y]; omega⟩
    have hc12 : c₁ = !c₂ := by cases c₁ <;> cases c₂ <;> simp_all
    refine ⟨⟨k' + 2, by omega⟩, c₂, fun x => ?_⟩
    by_cases hx0 : (x : ℕ) = 0
    · have : x = 0 := Fin.ext hx0
      subst this; simp [hw0, rDiagonalWord_apply]
    · by_cases hxy : (x : ℕ) ≤ 2 * (j + 1)
      · have hx' := h₁ ⟨(x : ℕ) - 1, by dsimp [y]; omega⟩
        have hxeq : sliceLeft y ⟨(x : ℕ) - 1, by dsimp [y]; omega⟩ = x :=
          Fin.ext (by dsimp [sliceLeft]; omega)
        rw [Function.comp_apply, hxeq, hc12] at hx'
        rw [hx', rDiagonalWord_apply, rDiagonalWord_apply]
        have hpar : Even ((x : ℕ) - 1) ↔ ¬ Even (x : ℕ) := by
          obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hx0
          simp [ht, Nat.even_add_one]
        split_ifs <;> simp_all
      · have hx' := h₂ ⟨(x : ℕ) - 2 * (j + 1), by dsimp [y]; omega⟩
        have hxeq : sliceRight y ⟨(x : ℕ) - 2 * (j + 1), by dsimp [y]; omega⟩ = x := by
          dsimp [sliceRight]
          rw [ite_eq_right (by omega)]
          exact Fin.ext (by dsimp [y]; omega)
        rw [Function.comp_apply, hxeq] at hx'
        rw [hx', rDiagonalWord_apply, rDiagonalWord_apply]
        have hpar : Even ((x : ℕ) - 2 * (j + 1)) ↔ Even (x : ℕ) := by
          have hsub : (x : ℕ) = ((x : ℕ) - 2 * (j + 1)) + 2 * (j + 1) := by omega
          conv_rhs => rw [hsub]
          simp [Nat.even_add]
        split_ifs <;> simp_all
  · rintro ⟨-, c, hwc⟩
    refine ⟨⟨⟨j + 1, by dsimp [y]; omega⟩, !c, fun i => ?_⟩,
      ⟨⟨k' + 1 - j, by dsimp [y]; omega⟩, c, fun i => ?_⟩⟩
    · dsimp [Function.comp_apply, sliceLeft]
      rw [hwc, rDiagonalWord_apply, rDiagonalWord_apply]
      simp only [Nat.even_add_one]
      split_ifs <;> simp
    · dsimp [Function.comp_apply, sliceRight, y]
      split_ifs with hi0
      · rw [hwc, rDiagonalWord_apply, rDiagonalWord_apply]
        simp [hi0]
      · rw [hwc, rDiagonalWord_apply, rDiagonalWord_apply]
        simp [Nat.even_add]

/-- Odd cuts `y` contribute `0` to the recurrence sum, leaving only `y = 2 * (j + 1)` for
`j : Fin (k' + 1)`. -/
private theorem IsHaarUnitary.freeCumulant_ite_star_sum_even (h : IsHaarUnitary φ u)
    {m k' : ℕ} (hk : m + 2 = 2 * (k' + 2)) (w : Fin (m + 2) → Bool) :
    let a : Fin (m + 2) → A := fun i => if w i then Star.star u else u
    ∑ y ∈ (univ : Finset (Fin (m + 2))).erase 0,
        freeCumulant φ a {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y} *
          freeCumulant φ a (univ \ {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y}) =
      ∑ j : Fin (k' + 1),
        freeCumulant φ a {z ∈ (univ : Finset (Fin (m + 2))).erase 0 |
            z ≤ (⟨2 * ((j : ℕ) + 1), by omega⟩ : Fin (m + 2))} *
          freeCumulant φ a (univ \ {z ∈ (univ : Finset (Fin (m + 2))).erase 0 |
            z ≤ (⟨2 * ((j : ℕ) + 1), by omega⟩ : Fin (m + 2))}) := by
  intro a
  let g : Fin (k' + 1) → Fin (m + 2) := fun j => ⟨2 * ((j : ℕ) + 1), by omega⟩
  have hg_inj : Function.Injective g :=
    fun j₁ j₂ h12 => Fin.ext (by have := Fin.mk.inj h12; omega)
  have hg_ne (j : Fin (k' + 1)) : g j ≠ 0 := fun h0 => by
    have := congrArg Fin.val h0; dsimp [g] at this; omega
  have hsub : (univ : Finset (Fin (k' + 1))).image g ⊆ (univ : Finset (Fin (m + 2))).erase 0 := by
    intro y hy
    obtain ⟨j, -, rfl⟩ := mem_image.1 hy
    exact mem_erase.2 ⟨hg_ne j, mem_univ _⟩
  have hvan : ∀ y ∈ (univ : Finset (Fin (m + 2))).erase 0,
      y ∉ (univ : Finset (Fin (k' + 1))).image g →
      freeCumulant φ a {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y} *
        freeCumulant φ a (univ \ {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ y}) = 0 := by
    intro y hy hny
    have hyodd : Odd (y : ℕ) := by
      by_contra hnotodd
      obtain ⟨r, hr⟩ := Nat.not_odd_iff_even.1 hnotodd
      have hypos : 0 < (y : ℕ) := Nat.pos_of_ne_zero (Fin.val_ne_of_ne (mem_erase.1 hy).1)
      have := y.2
      exact hny (mem_image.2 ⟨⟨r - 1, by omega⟩, mem_univ _, Fin.ext (by dsimp [g]; omega)⟩)
    rw [freeCumulant_sliceLeft, show a ∘ sliceLeft y = fun i => if (w ∘ sliceLeft y) i then
      Star.star u else u from rfl, h.freeCumulant_ite_star_eq_zero_of_odd hyodd, zero_mul]
  rw [← sum_subset hsub hvan, sum_image hg_inj.injOn]

/-- Evaluating the quadratic recurrence of `freeCumulant_ite_star_eq_neg_sum` by strong induction:
for a word `w : Fin (m + 2) → Bool` with `w 0 ≠ w 1` (`m ≥ 1`), if every shorter word has
signed-Catalan even-alternating cumulants and zero cumulants elsewhere, then so does `w`. -/
private theorem IsHaarUnitary.freeCumulant_ite_star_step (h : IsHaarUnitary φ u)
    {m : ℕ} (hm : m ≠ 0) {w : Fin (m + 2) → Bool} (hw01 : w 0 ≠ w 1)
    (ih : ∀ n' < m + 2, n' ≠ 0 → ∀ w' : Fin n' → Bool,
      freeCumulant φ (fun i => if w' i then Star.star u else u) univ =
        if Even n' ∧ ∃ c, ∀ i, w' i = rDiagonalWord c n' i then
          (-1) ^ (n' / 2 - 1) * (catalan (n' / 2 - 1) : R)
        else 0) :
    freeCumulant φ (fun i => if w i then Star.star u else u) univ =
      if Even (m + 2) ∧ ∃ c, ∀ i, w i = rDiagonalWord c (m + 2) i then
        (-1) ^ ((m + 2) / 2 - 1) * (catalan ((m + 2) / 2 - 1) : R)
      else 0 := by
  let a : Fin (m + 2) → A := fun i => if w i then Star.star u else u
  by_cases hodd : Odd (m + 2)
  · rw [h.freeCumulant_ite_star_eq_zero_of_odd hodd, eq_comm, ite_eq_right_iff]
    exact fun ⟨heven, _⟩ => absurd heven (Nat.not_even_iff_odd.2 hodd)
  obtain ⟨k', hk⟩ : ∃ k', m + 2 = 2 * (k' + 2) := by
    obtain ⟨r, hr⟩ := Nat.not_odd_iff_even.1 hodd
    exact ⟨r - 2, by omega⟩
  rw [h.freeCumulant_ite_star_eq_neg_sum hm hw01, h.freeCumulant_ite_star_sum_even hk w]
  let g : Fin (k' + 1) → Fin (m + 2) := fun j => ⟨2 * ((j : ℕ) + 1), by omega⟩
  have hgj (j : Fin (k' + 1)) : g j ≠ 0 := Fin.ne_of_val_ne (by dsimp [g]; omega)
  have heval (j : Fin (k' + 1)) :
      freeCumulant φ a {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ g j} *
          freeCumulant φ a (univ \ {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ g j}) =
        (if Even (g j : ℕ) ∧ ∃ c₁, ∀ i, (w ∘ sliceLeft (g j)) i = rDiagonalWord c₁ (g j : ℕ) i
          then (-1) ^ ((g j : ℕ) / 2 - 1) * (catalan ((g j : ℕ) / 2 - 1) : R) else 0) *
        (if Even (m + 2 - (g j : ℕ)) ∧
            ∃ c₂, ∀ i, (w ∘ sliceRight (g j)) i = rDiagonalWord c₂ (m + 2 - (g j : ℕ)) i
          then (-1) ^ ((m + 2 - (g j : ℕ)) / 2 - 1) * (catalan ((m + 2 - (g j : ℕ)) / 2 - 1) : R)
          else 0) := by
    rw [freeCumulant_sliceLeft, freeCumulant_sliceRight a (hgj j),
      show a ∘ sliceLeft (g j) = fun i => if (w ∘ sliceLeft (g j)) i then Star.star u else u
        from rfl,
      show a ∘ sliceRight (g j) = fun i => if (w ∘ sliceRight (g j)) i then Star.star u else u
        from rfl,
      ih (g j : ℕ) (g j).2 (by dsimp [g]; omega),
      ih (m + 2 - (g j : ℕ)) (by dsimp [g]; omega) (by dsimp [g]; omega)]
  by_cases halt : Even (m + 2) ∧ ∃ c, ∀ i, w i = rDiagonalWord c (m + 2) i
  · rw [ite_eq_left halt]
    have hterm (j : Fin (k' + 1)) :
        freeCumulant φ a {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ g j} *
            freeCumulant φ a (univ \ {z ∈ (univ : Finset (Fin (m + 2))).erase 0 | z ≤ g j}) =
          (-1 : R) ^ k' * ((catalan j : R) * (catalan (k' - j) : R)) := by
      obtain ⟨h₁, h₂⟩ := (rDiagonalWord_slice_iff hk j.2 hw01).2 halt
      rw [heval, ite_eq_left h₁, ite_eq_left h₂,
        show (g j : ℕ) / 2 - 1 = (j : ℕ) by dsimp [g]; omega,
        show (m + 2 - (g j : ℕ)) / 2 - 1 = k' - (j : ℕ) by dsimp [g]; omega,
        mul_mul_mul_comm, ← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.1 j.2)]
    rw [sum_congr rfl fun j _ => hterm j, ← mul_sum,
      sum_congr rfl fun j _ => (Nat.cast_mul _ _).symm, ← Nat.cast_sum, ← catalan_succ,
      show (m + 2) / 2 - 1 = k' + 1 by omega, pow_succ]
    ring
  · rw [ite_eq_right halt, sum_eq_zero, neg_zero]
    intro j _
    have hnot := mt (rDiagonalWord_slice_iff hk j.2 hw01).1 halt
    rw [heval]
    by_cases h₁ :
        Even (g j : ℕ) ∧ ∃ c₁, ∀ i, (w ∘ sliceLeft (g j)) i = rDiagonalWord c₁ (g j : ℕ) i
    · rw [ite_eq_right (fun h₂ => hnot ⟨h₁, h₂⟩), mul_zero]
    · rw [ite_eq_right h₁, zero_mul]

/-- Rotating an even-length word preserves being an `rDiagonalWord`. -/
private theorem rDiagonalWord_comp_finRotate_pow_iff {n : ℕ} (w : Fin n → Bool) (r : ℕ) :
    (Even n ∧ ∃ c, ∀ i, (w ∘ ⇑(finRotate n ^ r)) i = rDiagonalWord c n i) ↔
      Even n ∧ ∃ c, ∀ i, w i = rDiagonalWord c n i := by
  have hstep (v : Fin n → Bool) :
      (Even n ∧ ∃ c, ∀ i, (v ∘ finRotate n) i = rDiagonalWord c n i) ↔
        Even n ∧ ∃ c, ∀ i, v i = rDiagonalWord c n i := by
    rcases eq_or_ne n 0 with rfl | hn0
    · exact Iff.rfl
    refine ⟨fun ⟨⟨t, ht⟩, c, hv⟩ => ?_, fun ⟨⟨t, ht⟩, c, hv⟩ => ?_⟩
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * (k + 1) := ⟨t - 1, by omega⟩
      refine ⟨⟨k + 1, by ring⟩, !c, fun i => ?_⟩
      obtain ⟨j, rfl⟩ := (finRotate (2 * (k + 1))).surjective i
      have hrot := congrFun (rDiagonalWord_comp_finRotate (!c) k) j
      simp only [Function.comp_apply, Bool.not_not] at hrot
      exact (hv j).trans hrot.symm
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * (k + 1) := ⟨t - 1, by omega⟩
      refine ⟨⟨k + 1, by ring⟩, !c, fun j => ?_⟩
      exact (hv (finRotate (2 * (k + 1)) j)).trans (congrFun (rDiagonalWord_comp_finRotate c k) j)
  rw [Equiv.Perm.coe_pow]
  induction r with
  | zero => rfl
  | succ r ihr =>
    rw [Function.iterate_succ, ← Function.comp_assoc, hstep]
    exact ihr

/-- A nonconstant word `w : Fin (m + 2) → Bool` has a cyclic rotation starting with two distinct
letters. -/
private theorem exists_finRotate_pow_zero_ne_one {m : ℕ} {w : Fin (m + 2) → Bool}
    (hnc : ¬ ∀ i, w i = w 0) :
    ∃ r : ℕ, (w ∘ ⇑(finRotate (m + 2) ^ r)) 0 ≠ (w ∘ ⇑(finRotate (m + 2) ^ r)) 1 := by
  have hex : ∃ r : ℕ, ∃ hr : r + 1 < m + 2, w ⟨r, by omega⟩ ≠ w ⟨r + 1, hr⟩ := by
    by_contra! hall
    apply hnc
    intro ⟨i, hi⟩
    induction i with
    | zero => rfl
    | succ i ih => exact (hall i hi).symm.trans (ih (by omega))
  obtain ⟨r, hr, hne⟩ := hex
  have pow_apply (t : ℕ) (x : Fin (m + 2)) (hx : (x : ℕ) + t < m + 2) :
      ((finRotate (m + 2) ^ t) x : ℕ) = (x : ℕ) + t := by
    rw [Equiv.Perm.coe_pow]
    induction t generalizing x with
    | zero => simp
    | succ t iht =>
      rw [Function.iterate_succ_apply]
      have hxlast : x ≠ Fin.last (m + 1) := by simp [Fin.ext_iff]; omega
      rw [iht _ (by rw [coe_finRotate_of_ne_last hxlast]; omega), coe_finRotate_of_ne_last hxlast]
      omega
  refine ⟨r, ?_⟩
  dsimp only [Function.comp_apply]
  have h0 : (finRotate (m + 2) ^ r) 0 = ⟨r, by omega⟩ := Fin.ext (by
    simpa using pow_apply r 0 (by simp; omega))
  have h1 : (finRotate (m + 2) ^ r) 1 = ⟨r + 1, hr⟩ := Fin.ext (by
    simpa [Nat.add_comm] using pow_apply r 1 (by simp; omega))
  rwa [h0, h1]

namespace IsHaarUnitary

/-- Every positive-order constant free cumulant of a Haar unitary vanishes. -/
theorem freeCumulant_const_eq_zero (h : IsHaarUnitary φ u) {n : ℕ} (hn : n ≠ 0) :
    freeCumulant φ (fun _ : Fin n => u) univ = 0 :=
  h.freeCumulant_ite_star_eq_zero_of_const hn false fun _ => rfl

/-- Explicit joint free cumulants of `u` and `star u` for a Haar unitary `u`: nonempty even
alternating words evaluate to signed Catalan numbers `(-1) ^ (n / 2 - 1) * catalan (n / 2 - 1)`,
and all other nonempty star words evaluate to `0`. -/
theorem freeCumulant_ite_star (h : IsHaarUnitary φ u) {n : ℕ} (hn : n ≠ 0) (w : Fin n → Bool) :
    freeCumulant φ (fun i => if w i then Star.star u else u) univ =
      if Even n ∧ ∃ c, ∀ i, w i = rDiagonalWord c n i then
        (-1) ^ (n / 2 - 1) * (catalan (n / 2 - 1) : R)
      else 0 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases n with _ | _ | m
    · exact absurd rfl hn
    · rw [h.freeCumulant_ite_star_eq_zero_of_const (by omega) (w 0) fun i => by fin_cases i; rfl,
        eq_comm, ite_eq_right_iff]
      rintro ⟨⟨k, hk⟩, -⟩; omega
    · by_cases hconst : ∀ i, w i = w 0
      · rw [h.freeCumulant_ite_star_eq_zero_of_const (by omega) (w 0) hconst,
          eq_comm, ite_eq_right_iff]
        rintro ⟨-, c, hwc⟩
        have h0 := (hwc 0).symm.trans ((hconst 1).symm.trans (hwc 1))
        simp [rDiagonalWord_apply] at h0
      rcases eq_or_ne m 0 with rfl | hm
      · have hw01 : w 0 ≠ w 1 := fun h01 => hconst fun i => by fin_cases i <;> simp [h01]
        have halt : Even 2 ∧ ∃ c, ∀ i : Fin 2, w i = rDiagonalWord c 2 i := by
          refine ⟨even_two, w 0, fun i => ?_⟩
          fin_cases i <;> cases h0 : w 0 <;> cases h1 : w 1 <;> simp_all [rDiagonalWord_apply]
        rw [ite_eq_left halt, univ_fin2, freeCumulant_pair φ _ Fin.zero_lt_one]
        have hu0 : φ u = 0 := h.apply_eq_zero
        have hsu0 : φ (Star.star u) = 0 := h.apply_star_eq_zero
        cases h0 : w 0 <;> cases h1 : w 1
        · exact absurd (h0.trans h1.symm) hw01
        · simp [Unitary.mul_star_self_of_mem h.mem_unitary, h.apply_one, hu0]
        · simp [Unitary.star_mul_self_of_mem h.mem_unitary, h.apply_one, hsu0]
        · exact absurd (h0.trans h1.symm) hw01
      · obtain ⟨r, hr⟩ := exists_finRotate_pow_zero_ne_one hconst
        rw [← freeCumulant_ite_star_comp_finRotate_pow h.mem_unitary w r,
          show ((fun i => if w i then Star.star u else u) ∘ ⇑(finRotate (m + 2) ^ r)) =
            (fun i => if (w ∘ ⇑(finRotate (m + 2) ^ r)) i then Star.star u else u) from rfl,
          h.freeCumulant_ite_star_step hm hr ih]
        simp only [rDiagonalWord_comp_finRotate_pow_iff]

/-- Every Haar unitary element is R-diagonal. -/
theorem isRDiagonal (h : IsHaarUnitary φ u) : IsRDiagonal φ u where
  apply_one := h.apply_one
  freeCumulant_eq_zero {n} hn w hw := by
    rw [h.freeCumulant_ite_star hn w, ite_eq_right_iff]
    rintro ⟨⟨t, ht⟩, c, hc⟩
    exact absurd ⟨t - 1, c, by omega, hc⟩ hw

/-- Both R-diagonal determining sequences of a Haar unitary are the signed Catalan numbers
`(-1) ^ n * catalan n`. -/
@[simp]
theorem rDiagonalDeterminingSequence (h : IsHaarUnitary φ u) (c : Bool) (n : ℕ) :
    TauCeti.rDiagonalDeterminingSequence φ u c n = (-1) ^ n * (catalan n : R) := by
  rw [rDiagonalDeterminingSequence_def, h.freeCumulant_ite_star (by omega),
    ite_eq_left ⟨⟨n + 1, by ring⟩, c, fun _ => rfl⟩]
  have hd : 2 * (n + 1) / 2 - 1 = n := by omega
  rw [hd]

end IsHaarUnitary

end CommRing

end TauCeti
