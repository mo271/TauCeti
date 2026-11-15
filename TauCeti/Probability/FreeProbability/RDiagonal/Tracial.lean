/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.Cyclic
public import TauCeti.Probability.FreeProbability.RDiagonal.Basic

/-!
# Star-distribution invariance and traciality for R-diagonal elements

This file relates R-diagonality and its two determining sequences to star distributions and
traciality on the generated star subalgebra.

## Main results

* R-diagonality depends only on the one-variable star distribution
  (`TauCeti.isRDiagonal_iff_of_starDistribution_eq`), and scaling an R-diagonal element by a
  unitary scalar preserves its star distribution (`TauCeti.IsRDiagonal.starDistribution_smul_eq`).
* Rotating an even alternating Boolean word by one step exchanges the two starting letters
  (`TauCeti.rDiagonalWord_comp_finRotate`). Consequently, if `φ` is tracial on the generated
  star subalgebra `StarAlgebra.adjoin R {a}`, the two determining sequences of `a` agree without
  assuming R-diagonality (`TauCeti.rDiagonalDeterminingSequence_false_eq_true`).
* Conversely, for an R-diagonal element `a`, equality of the two determining sequences makes all
  joint free cumulants in `a` and `star a` cyclically invariant
  (`TauCeti.IsRDiagonal.freeCumulant_comp_finRotate`), which implies that `φ` is tracial on
  `StarAlgebra.adjoin R {a}` (`TauCeti.IsRDiagonal.forall_mem_adjoin_mul_comm_iff`).

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Proposition 15.1 and
  Remark 15.4.
-/

public section

open Finset

namespace TauCeti

section CyclicMoments

variable {R A κ : Type*} [CommRing R] [Monoid A]

/-- If free cumulants of words drawn from `x : κ → A` are invariant under `finRotate`, then on
every subset `B ⊆ Fin m` precomposing with `finRotate m` shifts the subset by `finRotate m`. -/
private theorem freeCumulant_comp_finRotate_part {φ : A → R} {x : κ → A}
    (hc : ∀ m (w : Fin m → κ),
      freeCumulant φ (x ∘ w ∘ finRotate m) univ = freeCumulant φ (x ∘ w) univ)
    {m : ℕ} (w : Fin m → κ) (B : Finset (Fin m)) :
    freeCumulant φ (x ∘ w ∘ finRotate m) B =
      freeCumulant φ (x ∘ w) (B.map (finRotate m).toEmbedding) := by
  have hc_pow : ∀ k (v : Fin k → κ) (r : ℕ),
      freeCumulant φ (x ∘ v ∘ ⇑(finRotate k ^ r)) univ = freeCumulant φ (x ∘ v) univ := by
    intro k v r
    induction r generalizing v with
    | zero => simp [Function.comp_def]
    | succ r ih =>
      calc
        freeCumulant φ (x ∘ v ∘ ⇑(finRotate k ^ (r + 1))) univ
            = freeCumulant φ (x ∘ (v ∘ ⇑(finRotate k)) ∘ ⇑(finRotate k ^ r)) univ := by
              rw [pow_succ', Equiv.Perm.coe_mul]; rfl
        _ = freeCumulant φ (x ∘ v) univ := (ih (v ∘ finRotate k)).trans (hc k v)
  let e := (finRotate m).toEmbedding
  obtain ⟨r, hr⟩ := (B.isRotated_sort_map_finRotate).symm
  have hsort₁ : List.ofFn (B.orderEmbOfFin rfl) = B.sort := by
    rw [List.ofFn_eq_map, listMap_orderEmbOfFin_finRange]
  have hsort₂ : List.ofFn ((B.map e).orderEmbOfFin (card_map e)) = (B.map e).sort := by
    rw [List.ofFn_eq_map, listMap_orderEmbOfFin_finRange]
  have hfn : finRotate m ∘ B.orderEmbOfFin rfl =
      (B.map e).orderEmbOfFin (card_map e) ∘ ⇑(finRotate #B ^ r) := by
    apply List.ofFn_inj.1
    rw [List.ofFn_comp_finRotate_pow, hsort₂, hr, ← hsort₁, ← List.map_ofFn]
  rw [freeCumulant_eq_freeCumulant_comp_orderEmbOfFin φ _ B]
  have hcomp : (x ∘ w ∘ finRotate m) ∘ B.orderEmbOfFin rfl =
      x ∘ (w ∘ ⇑((B.map e).orderEmbOfFin (card_map e))) ∘ ⇑(finRotate #B ^ r) := by
    change (x ∘ w) ∘ (finRotate m ∘ B.orderEmbOfFin rfl) = _
    rw [hfn]; rfl
  rw [hcomp, hc_pow]
  change freeCumulant φ ((x ∘ w) ∘ ⇑((B.map e).orderEmbOfFin (card_map e))) univ = _
  rw [freeCumulant_comp_of_strictMonoOn φ
    (((B.map e).orderEmbOfFin (card_map e)).strictMono.strictMonoOn _), image_orderEmbOfFin_univ]

/-- If all free cumulants of words drawn from `x : κ → A` are invariant under `finRotate`, then
every ordered product moment of two words from `x` commutes under `φ`. -/
private theorem apply_prod_mul_comm_of_freeCumulant_comp_finRotate {φ : A → R} {x : κ → A}
    (hc : ∀ m (w : Fin m → κ),
      freeCumulant φ (x ∘ w ∘ finRotate m) univ = freeCumulant φ (x ∘ w) univ)
    (u v : List κ) :
    φ ((u.map x).prod * (v.map x).prod) = φ ((v.map x).prod * (u.map x).prod) := by
  have hrot_one : ∀ {m : ℕ}, m ≠ 0 → ∀ w : Fin m → κ,
      φ (List.ofFn (x ∘ w ∘ finRotate m)).prod = φ (List.ofFn (x ∘ w)).prod := by
    intro m hm w
    rw [apply_prod_ofFn_eq_sum_prod_freeCumulant φ hm,
      apply_prod_ofFn_eq_sum_prod_freeCumulant φ hm]
    conv_rhs => rw [← (NoncrossingPartition.rotate m).toEquiv.sum_comp]
    refine Fintype.sum_congr _ _ fun π => ?_
    rw [OrderIso.coe_toEquiv, NoncrossingPartition.prod_parts_rotate]
    exact prod_congr rfl fun B _ => freeCumulant_comp_finRotate_part hc w B
  have hrot_pow : ∀ {m : ℕ}, m ≠ 0 → ∀ (w : Fin m → κ) (r : ℕ),
      φ (List.ofFn (x ∘ w ∘ ⇑(finRotate m ^ r))).prod = φ (List.ofFn (x ∘ w)).prod := by
    intro m hm w r
    induction r generalizing w with
    | zero => simp [Function.comp_def]
    | succ r ih =>
      calc
        φ (List.ofFn (x ∘ w ∘ ⇑(finRotate m ^ (r + 1)))).prod
            = φ (List.ofFn (x ∘ (w ∘ ⇑(finRotate m)) ∘ ⇑(finRotate m ^ r))).prod := by
              rw [pow_succ', Equiv.Perm.coe_mul]; rfl
        _ = φ (List.ofFn (x ∘ w)).prod := (ih (w ∘ finRotate m)).trans (hrot_one hm w)
  rw [← List.prod_append, ← List.prod_append, ← List.map_append, ← List.map_append]
  obtain ⟨r, hr⟩ : (u ++ v) ~r (v ++ u) := List.isRotated_append
  set l := u ++ v
  rw [← hr]
  by_cases hl : l.length = 0
  · rw [List.length_eq_zero_iff.1 hl, List.rotate_nil]
  · have hget : List.ofFn l.get = l := List.ofFn_get l
    calc
      φ (l.map x).prod = φ (List.ofFn (x ∘ l.get)).prod := by rw [← List.map_ofFn, hget]
      _ = φ (List.ofFn (x ∘ l.get ∘ ⇑(finRotate l.length ^ r))).prod :=
        (hrot_pow hl l.get r).symm
      _ = φ ((l.rotate r).map x).prod := by
        rw [show x ∘ l.get ∘ ⇑(finRotate l.length ^ r) =
            x ∘ (l.get ∘ ⇑(finRotate l.length ^ r)) from rfl,
          ← List.map_ofFn, List.ofFn_comp_finRotate_pow, hget]

end CyclicMoments

section RDiagonal

variable {R A B : Type*} [CommRing R]
  [Semiring A] [Algebra R A] [StarRing A]
  [Semiring B] [Algebra R B] [StarRing B]
  {φ : A →ₗ[R] R} {ψ : B →ₗ[R] R} {a : A} {b : B}

/-- Rotating an even alternating Boolean word by one step exchanges its starting letter with its
negation. -/
@[simp]
theorem rDiagonalWord_comp_finRotate (c : Bool) (n : ℕ) :
    rDiagonalWord c (2 * (n + 1)) ∘ finRotate (2 * (n + 1)) =
      rDiagonalWord (!c) (2 * (n + 1)) := by
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
  funext i
  rw [Function.comp_apply]
  by_cases hi : i = Fin.last (2 * n + 1)
  · subst hi
    simp [rDiagonalWord_apply, Fin.val_last]
  · simp only [rDiagonalWord_apply, coe_finRotate_of_ne_last hi, Nat.even_add_one]
    by_cases he : Even (i : ℕ) <;> simp [he]

private theorem isRDiagonal_of_starDistribution_eq [StarRing R] [StarModule R A] [StarModule R B]
    (h : starDistribution φ (fun _ : Unit => a) = starDistribution ψ (fun _ : Unit => b))
    (ha : IsRDiagonal φ a) : IsRDiagonal ψ b where
  apply_one := by
    have h1 := LinearMap.congr_fun h 1
    simpa [ha.apply_one] using h1.symm
  freeCumulant_eq_zero hn w hw := by
    have hj := starDistribution_eq_iff_jointDistribution_withStar_eq.1 h
    have hR := (jointRSeries_eq_iff_jointDistribution_eq
      (by simpa using LinearMap.congr_fun h 1)).2 hj
    have he := congrArg (WordSeries.coeff (FreeMonoid.ofList
      (List.ofFn fun i : Fin _ => ((), w i)))) hR
    rw [coeff_jointRSeries_ofFn _ _ _ hn, coeff_jointRSeries_ofFn _ _ _ hn] at he
    have hzero := ha.freeCumulant_eq_zero hn w hw
    simpa only [Function.comp_def, StarPolynomial.withStar_def, hzero] using he.symm

/-- R-diagonality depends only on the one-variable star distribution. -/
theorem isRDiagonal_iff_of_starDistribution_eq [StarRing R] [StarModule R A] [StarModule R B]
    (h : starDistribution φ (fun _ : Unit => a) = starDistribution ψ (fun _ : Unit => b)) :
    IsRDiagonal φ a ↔ IsRDiagonal ψ b :=
  ⟨isRDiagonal_of_starDistribution_eq h, isRDiagonal_of_starDistribution_eq h.symm⟩

/-- Scaling an R-diagonal element by a unitary scalar preserves its star distribution. -/
theorem IsRDiagonal.starDistribution_smul_eq [StarRing R] [StarModule R A]
    (h : IsRDiagonal φ a) {z : R} (hz : z ∈ unitary R) :
    starDistribution φ (fun _ : Unit => z • a) = starDistribution φ (fun _ : Unit => a) := by
  refine (h.smul z).starDistribution_eq h fun c n => ?_
  rw [rDiagonalDeterminingSequence_smul, (Unitary.mem_iff.1 hz).2, one_pow, one_mul]

/-- If `φ` is tracial on the generated star subalgebra `StarAlgebra.adjoin R {a}`, the two
determining sequences of `a` agree (without assuming R-diagonality). -/
theorem rDiagonalDeterminingSequence_false_eq_true [StarRing R] [StarModule R A]
    (hφ : ∀ x ∈ StarAlgebra.adjoin R {a}, ∀ y ∈ StarAlgebra.adjoin R {a}, φ (x * y) = φ (y * x))
    (n : ℕ) :
    rDiagonalDeterminingSequence φ a false n = rDiagonalDeterminingSequence φ a true n := by
  rw [rDiagonalDeterminingSequence_def, rDiagonalDeterminingSequence_def]
  let S := StarAlgebra.adjoin R ({a} : Set A)
  let φS : S → R := fun x => φ x.1
  have htr : ∀ x y : S, φS (x * y) = φS (y * x) := fun x y => hφ x.1 x.2 y.1 y.2
  have haS : a ∈ S := StarAlgebra.subset_adjoin R {a} rfl
  let u : Fin (2 * (n + 1)) → S := fun i =>
    if rDiagonalWord false (2 * (n + 1)) i then ⟨star a, star_mem haS⟩ else ⟨a, haS⟩
  have hpm : ∀ {w : Fin (2 * (n + 1)) → S} (P : Finpartition (univ : Finset (Fin (2 * (n + 1))))),
      partitionMoment φS w P = partitionMoment φ (Subtype.val ∘ w) P := by
    intro w P
    rw [partitionMoment_def, partitionMoment_def]
    refine prod_congr rfl fun C _ => congrArg φ ?_
    rw [← List.map_map]
    exact SubmonoidClass.coe_list_prod (C.sort.map w)
  have hfc : ∀ w : Fin (2 * (n + 1)) → S,
      freeCumulant φS w univ = freeCumulant φ (Subtype.val ∘ w) univ := fun w => by
    simp only [freeCumulant_eq_sum_mu_mul_partitionMoment, hpm]
  have hrot := freeCumulant_comp_finRotate htr u
  rw [hfc, hfc] at hrot
  have hword (i : Fin (2 * (n + 1))) :
      rDiagonalWord false (2 * (n + 1)) (finRotate (2 * (n + 1)) i) =
        rDiagonalWord true (2 * (n + 1)) i :=
    congrFun (rDiagonalWord_comp_finRotate false n) i
  have hlhs : Subtype.val ∘ (u ∘ finRotate (2 * (n + 1))) =
      fun i => if rDiagonalWord true (2 * (n + 1)) i then star a else a := by
    funext i
    simp only [Function.comp_apply, u, hword i]
    split_ifs <;> rfl
  have hrhs : Subtype.val ∘ u =
      fun i => if rDiagonalWord false (2 * (n + 1)) i then star a else a := by
    funext i
    simp only [Function.comp_apply, u]
    split_ifs <;> rfl
  rw [hlhs, hrhs] at hrot
  exact hrot.symm

namespace IsRDiagonal

/-- For an R-diagonal element whose two determining sequences agree, every joint free cumulant in
`a` and `star a` is invariant under cyclic rotation. -/
theorem freeCumulant_comp_finRotate (h : IsRDiagonal φ a)
    (heq : ∀ n, rDiagonalDeterminingSequence φ a false n = rDiagonalDeterminingSequence φ a true n)
    {m : ℕ} (w : Fin m → Bool) :
    freeCumulant φ ((fun i => if w i then Star.star a else a) ∘ finRotate m) univ =
      freeCumulant φ (fun i => if w i then Star.star a else a) univ := by
  change freeCumulant φ (fun i => if (w ∘ finRotate m) i then Star.star a else a) univ = _
  by_cases hm : m = 0
  · subst hm
    simp [freeCumulant_empty]
  by_cases hw : ∃ k c, m = 2 * (k + 1) ∧ ∀ i, w i = rDiagonalWord c m i
  · obtain ⟨k, c, rfl, hw⟩ := hw
    have hw' : ∀ i, (w ∘ finRotate (2 * (k + 1))) i = rDiagonalWord (!c) (2 * (k + 1)) i := by
      intro i
      simpa [hw] using congrFun (rDiagonalWord_comp_finRotate c k) i
    simp only [hw', hw, ← rDiagonalDeterminingSequence_def]
    cases c
    · exact (heq k).symm
    · exact heq k
  · have hw' : ¬ ∃ k c, m = 2 * (k + 1) ∧ ∀ i, (w ∘ finRotate m) i = rDiagonalWord c m i := by
      rintro ⟨k, c, rfl, hc⟩
      refine hw ⟨k, !c, rfl, fun j => ?_⟩
      have hj := hc ((finRotate (2 * (k + 1))).symm j)
      have hrot := congrFun (rDiagonalWord_comp_finRotate (!c) k)
        ((finRotate (2 * (k + 1))).symm j)
      simp only [Function.comp_apply, Equiv.apply_symm_apply, Bool.not_not] at hj hrot
      exact hj.trans hrot.symm
    rw [h.freeCumulant_eq_zero hm _ hw', h.freeCumulant_eq_zero hm w hw]

/-- *Nica–Speicher, Proposition 15.1 / Remark 15.4*: for an R-diagonal element `a`, the functional
`φ` is tracial on `StarAlgebra.adjoin R {a}` if and only if the two determining sequences of `a`
agree. -/
theorem forall_mem_adjoin_mul_comm_iff [StarRing R] [StarModule R A] (h : IsRDiagonal φ a) :
    (∀ x ∈ StarAlgebra.adjoin R {a}, ∀ y ∈ StarAlgebra.adjoin R {a}, φ (x * y) = φ (y * x)) ↔
      ∀ n, rDiagonalDeterminingSequence φ a false n = rDiagonalDeterminingSequence φ a true n := by
  refine ⟨rDiagonalDeterminingSequence_false_eq_true, fun heq => ?_⟩
  let f : Unit → A := fun _ => a
  let μ := starDistribution φ f
  have hword : ∀ u v : List (Unit × Bool),
      μ ((u.map (StarPolynomial.withStar StarPolynomial.X)).prod *
          (v.map (StarPolynomial.withStar StarPolynomial.X)).prod) =
        μ ((v.map (StarPolynomial.withStar StarPolynomial.X)).prod *
          (u.map (StarPolynomial.withStar StarPolynomial.X)).prod) := by
    intro u v
    dsimp only [μ]
    rw [← List.prod_append, ← List.prod_append, ← List.map_append, ← List.map_append,
      starDistribution_list_prod, starDistribution_list_prod,
      List.map_append, List.map_append, List.prod_append, List.prod_append]
    refine apply_prod_mul_comm_of_freeCumulant_comp_finRotate (fun m w => ?_) u v
    simpa only [Function.comp_def, StarPolynomial.withStar_def, f] using
      h.freeCumulant_comp_finRotate heq (fun i => (w i).2)
  have hspan := StarPolynomial.span_range_list_prod_withStar (R := R) (ι := Unit)
  have hpoly : ∀ p q : StarPolynomial R Unit, μ (p * q) = μ (q * p) := by
    intro p q
    have hp : p ∈ Submodule.span R
        (Set.range fun w : List (Unit × Bool) =>
          (w.map (StarPolynomial.withStar StarPolynomial.X)).prod) := by
      rw [hspan]; trivial
    refine Submodule.span_induction ?_ (by simp)
      (fun p₁ p₂ _ _ h₁ h₂ => by rw [add_mul, mul_add, map_add, map_add, h₁, h₂])
      (fun r p₁ _ h₁ => by rw [smul_mul_assoc, mul_smul_comm, map_smul, map_smul, h₁]) hp
    rintro _ ⟨u, rfl⟩
    have hq : q ∈ Submodule.span R
        (Set.range fun w : List (Unit × Bool) =>
          (w.map (StarPolynomial.withStar StarPolynomial.X)).prod) := by
      rw [hspan]; trivial
    refine Submodule.span_induction ?_ (by simp)
      (fun q₁ q₂ _ _ h₁ h₂ => by rw [mul_add, add_mul, map_add, map_add, h₁, h₂])
      (fun r q₁ _ h₁ => by rw [mul_smul_comm, smul_mul_assoc, map_smul, map_smul, h₁]) hq
    rintro _ ⟨v, rfl⟩
    exact hword u v
  have hadj : ∀ z ∈ StarAlgebra.adjoin R ({a} : Set A),
      ∃ p : StarPolynomial R Unit, StarPolynomial.lift f p = z := by
    intro z hz
    rw [show ({a} : Set A) = Set.range f from Set.range_const.symm,
      ← StarPolynomial.range_lift] at hz
    obtain ⟨p, hp⟩ := hz
    exact ⟨p, by simpa using hp⟩
  intro x hx y hy
  obtain ⟨p, rfl⟩ := hadj x hx
  obtain ⟨q, rfl⟩ := hadj y hy
  simpa only [μ, starDistribution_apply, map_mul] using hpoly p q

end IsRDiagonal

end RDiagonal

end TauCeti
