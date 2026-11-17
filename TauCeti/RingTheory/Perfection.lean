/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfection

/-!
# Coordinates of the perfection of a monoid

For a commutative monoid `M`, Mathlib's `Perfection M p` is the monoid of compatible systems
`(xₙ)ₙ` with `xₙ₊₁ ^ p = xₙ`. If every element of `M` has a `p`-th root, every element of `M`
starts such a system, and more generally every coordinate map `Perfection M p → M` is surjective.
Mathlib proves this for rings of characteristic `p` with surjective Frobenius
(`Perfection.coeff_surjective`); the statement here needs no ring structure, and applies for
instance to the multiplicative monoid of an algebraically closed field of any characteristic.

## Main definitions

* `PreTilt.equivPerfection`: the ring isomorphism `PreTilt O p ≃+* Perfection (ModP O p) p`.
* `PreTilt.mapOfModP`, `PreTilt.map`: functoriality of `PreTilt` along ring homomorphisms
  `ModP O p →+* ModP O' p` and `O →+* O'`.

## Main results

* `Perfection.coeffMonoidHom_surjective`: if `x ↦ x ^ p` is surjective on `M`, so is every
  coordinate map `Perfection.coeffMonoidHom M p n`.
* `Perfection.isReduced`, `PreTilt.isReduced`: `Perfection R p` and `PreTilt O p` are reduced.
* `Perfection.coeff_eq_zero_iff`: in the perfection of a reduced ring of characteristic `p`, an
  element vanishes as soon as one of its coordinates does.
* `PreTilt.ext`, `PreTilt.coeff_equivPerfection`, `PreTilt.coeff_equivPerfection_symm`: coordinate
  extensionality and coordinate formulas for `PreTilt.equivPerfection`.
* `PreTilt.coeff_mapOfModP`, `PreTilt.coeff_map`, `PreTilt.equivPerfection_mapOfModP`,
  `PreTilt.equivPerfection_map`, `PreTilt.map_eq_mapOfModP`, `PreTilt.map_id`, `PreTilt.map_comp`:
  coordinate and functoriality identities for `PreTilt.mapOfModP` and `PreTilt.map`.
* `PreTilt.coeff_eq_zero_iff`: in `PreTilt O p`, each coordinate detects zero when `O ⧸ p` is
  reduced.
* `TauCeti.dvd_of_compatible_roots`: in a compatible root sequence, later roots divide earlier ones.
-/

public section

namespace Perfection

variable {M : Type*} [CommMonoid M] {p : ℕ}

/-- **If every element of `M` has a `p`-th root, every coordinate of `Perfection M p` is
surjective.** -/
theorem coeffMonoidHom_surjective (h : Function.Surjective fun x : M ↦ x ^ p) (n : ℕ) :
    Function.Surjective (coeffMonoidHom M p n) := by
  intro x
  -- iterating a choice of `p`-th roots starting at `x` gives a compatible system `f` with zeroth
  -- term `x`, and raising `f` to the `p ^ n`-th power moves `x` to the `n`-th term
  choose r hr using h
  let f : Perfection M p := ⟨fun k ↦ r^[k] x, fun k ↦ by
    simp only [Function.iterate_succ_apply', hr]⟩
  refine ⟨f ^ p ^ n, ?_⟩
  have hf := coeffMonoidHom_pow_p_pow f 0 n
  rw [zero_add] at hf
  exact hf.trans (coeffMonoidHom_mk _ _ 0)

/-- The perfection of any commutative semiring of prime characteristic `p` is reduced. -/
instance isReduced {R : Type*} [CommSemiring R] [hp : Fact p.Prime] [CharP R p] :
    IsReduced (Perfection R p) where
  eq_zero f := fun ⟨n, hn⟩ ↦ by
    have hpow : f ^ p ^ n = 0 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.lt_pow_self hp.out.one_lt (n := n)).le
      rw [hk, pow_add, hn, zero_mul]
    ext m
    have hcoeff : coeff R p (m + n) (f ^ p ^ n) = coeff R p m f :=
      coeffMonoidHom_pow_p_pow f m n
    rw [map_zero, ← hcoeff, hpow, map_zero]

section Reduced

variable {R : Type*} [CommSemiring R] [Fact p.Prime] [CharP R p] [IsReduced R]

/-- **In the perfection of a reduced ring, each coordinate detects zero.** For `f` in the
perfection of a reduced ring of characteristic `p`, `coeff n f = 0` if and only if `f = 0`. -/
@[simp]
theorem coeff_eq_zero_iff (n : ℕ) {f : Perfection R p} : coeff R p n f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  have hlater (m : ℕ) : coeff R p (n + m) f = 0 := by
    induction m with
    | zero => exact h
    | succ m ih => exact IsNilpotent.eq_zero ⟨p, by rw [← add_assoc, coeff_pow_p', ih]⟩
  ext k
  rw [map_zero]
  exact not_not.mp fun hk ↦ coeff_ne_zero_of_le hk (Nat.le_add_left k n) (hlater k)

end Reduced

end Perfection

namespace PreTilt

variable {O : Type*} [CommRing O] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : O)]

/-- Two elements of `PreTilt O p` are equal if all of their `ModP O p` coordinates agree. -/
@[ext]
theorem ext {f g : PreTilt O p} (h : ∀ n, coeff n f = coeff n g) : f = g :=
  Perfection.ext h

/-- The ring isomorphism `PreTilt O p ≃+* Perfection (ModP O p) p`. -/
def equivPerfection : PreTilt O p ≃+* Perfection (ModP O p) p :=
  RingEquiv.refl (Perfection (ModP O p) p)

/-- `PreTilt.equivPerfection` preserves coordinates in `ModP O p`. -/
@[simp]
theorem coeff_equivPerfection (x : PreTilt O p) (n : ℕ) :
    Perfection.coeff (ModP O p) p n (equivPerfection x) = coeff n x := by
  rw [equivPerfection, coeff_def]
  rfl

/-- `PreTilt.equivPerfection.symm` preserves coordinates in `ModP O p`. -/
@[simp]
theorem coeff_equivPerfection_symm (x : Perfection (ModP O p) p) (n : ℕ) :
    coeff n (equivPerfection.symm x) = Perfection.coeff (ModP O p) p n x := by
  rw [equivPerfection, coeff_def]
  rfl

/-- `PreTilt O p` is reduced. -/
instance isReduced : IsReduced (PreTilt O p) :=
  isReduced_of_injective equivPerfection equivPerfection.injective

/-- **If `O ⧸ p` is reduced, each coordinate of the tilt detects zero.** For `f` in
`PreTilt O p`, `coeff n f = 0` if and only if `f = 0`. -/
@[simp]
theorem coeff_eq_zero_iff [IsReduced (ModP O p)] (n : ℕ) {f : PreTilt O p} :
    coeff n f = 0 ↔ f = 0 :=
  -- `PreTilt O p` is by definition `Perfection (ModP O p) p`, with `coeff` its coordinate maps
  Perfection.coeff_eq_zero_iff (R := ModP O p) n

/-- Functoriality of `PreTilt` along a ring homomorphism `ModP O p →+* ModP O' p`. -/
def mapOfModP {O' : Type*} [CommRing O'] [Fact ¬IsUnit (p : O')]
    (g : ModP O p →+* ModP O' p) : PreTilt O p →+* PreTilt O' p :=
  equivPerfection.symm.toRingHom.comp ((Perfection.map p g).comp equivPerfection.toRingHom)

/-- `PreTilt.mapOfModP g` applies `g` to every `ModP` coordinate. -/
@[simp]
theorem coeff_mapOfModP {O' : Type*} [CommRing O'] [Fact ¬IsUnit (p : O')]
    (g : ModP O p →+* ModP O' p) (x : PreTilt O p) (n : ℕ) :
    coeff n (mapOfModP g x) = g (coeff n x) := by
  simp [mapOfModP]

/-- Across `PreTilt.equivPerfection`, `PreTilt.mapOfModP g` is `Perfection.map p g`. -/
@[simp]
theorem equivPerfection_mapOfModP {O' : Type*} [CommRing O'] [Fact ¬IsUnit (p : O')]
    (g : ModP O p →+* ModP O' p) (x : PreTilt O p) :
    equivPerfection (mapOfModP g x) = Perfection.map p g (equivPerfection x) := by
  simp [mapOfModP]

@[simp]
theorem mapOfModP_id :
    mapOfModP (RingHom.id (ModP O p)) = RingHom.id (PreTilt O p) := by
  ext x n
  simp

theorem mapOfModP_comp {O' O'' : Type*} [CommRing O'] [CommRing O'']
    [Fact ¬IsUnit (p : O')] [Fact ¬IsUnit (p : O'')]
    (h : ModP O' p →+* ModP O'' p) (g : ModP O p →+* ModP O' p) :
    mapOfModP (h.comp g) = (mapOfModP h).comp (mapOfModP g) := by
  ext x n
  simp

@[simp]
theorem mapOfModP_comp_apply {O' O'' : Type*} [CommRing O'] [CommRing O'']
    [Fact ¬IsUnit (p : O')] [Fact ¬IsUnit (p : O'')]
    (h : ModP O' p →+* ModP O'' p) (g : ModP O p →+* ModP O' p) (x : PreTilt O p) :
    mapOfModP (h.comp g) x = mapOfModP h (mapOfModP g x) := by
  rw [mapOfModP_comp, RingHom.comp_apply]

/-- Functoriality of `PreTilt` along a ring homomorphism `f : O →+* O'`, obtained by reducing `f`
modulo `p` and applying `Perfection.map`. -/
def map (p : ℕ) [Fact p.Prime] {O O' : Type*} [CommRing O] [CommRing O']
    [Fact ¬IsUnit (p : O)] [Fact ¬IsUnit (p : O')] (f : O →+* O') :
    PreTilt O p →+* PreTilt O' p :=
  mapOfModP (Ideal.quotientMap (Ideal.span {(p : O')}) f (by rw [Ideal.span_le]; simp))

/-- Any ring homomorphism `g : ModP O p →+* ModP O' p` commuting with the quotient maps from
`f : O →+* O'` induces the same map on `PreTilt` as `PreTilt.map p f`. -/
theorem map_eq_mapOfModP {O' : Type*} [CommRing O'] [Fact ¬IsUnit (p : O')]
    {f : O →+* O'} {g : ModP O p →+* ModP O' p}
    (hg : g.comp (Ideal.Quotient.mk (Ideal.span {(p : O)})) =
      (Ideal.Quotient.mk (Ideal.span {(p : O')})).comp f) :
    map p f = mapOfModP g := by
  ext x n
  simp only [map, coeff_mapOfModP]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (coeff n x)
  rw [← ha, Ideal.quotientMap_mk]
  exact (RingHom.congr_fun hg a).symm

/-- `PreTilt.map p f` reduces each `ModP` coordinate via `Ideal.quotientMap`. -/
@[simp]
theorem coeff_map {O' : Type*} [CommRing O'] [Fact ¬IsUnit (p : O')]
    (f : O →+* O') (x : PreTilt O p) (n : ℕ) :
    coeff n (map p f x) =
      Ideal.quotientMap (Ideal.span {(p : O')}) f (by rw [Ideal.span_le]; simp) (coeff n x) :=
  coeff_mapOfModP _ x n

/-- Across `PreTilt.equivPerfection`, `PreTilt.map p f` is `Perfection.map` of
`Ideal.quotientMap`. -/
@[simp]
theorem equivPerfection_map {O' : Type*} [CommRing O'] [Fact ¬IsUnit (p : O')]
    (f : O →+* O') (x : PreTilt O p) :
    equivPerfection (map p f x) =
      Perfection.map p (Ideal.quotientMap (Ideal.span {(p : O')}) f (by rw [Ideal.span_le]; simp))
        (equivPerfection x) :=
  equivPerfection_mapOfModP _ x

@[simp]
theorem map_id : map p (RingHom.id O) = RingHom.id (PreTilt O p) := by
  rw [map_eq_mapOfModP (g := RingHom.id (ModP O p)) rfl, mapOfModP_id]

theorem map_comp {O' O'' : Type*} [CommRing O'] [CommRing O'']
    [Fact ¬IsUnit (p : O')] [Fact ¬IsUnit (p : O'')]
    (g : O' →+* O'') (f : O →+* O') :
    map p (g.comp f) = (map p g).comp (map p f) := by
  ext x n
  simp only [RingHom.comp_apply, coeff_map]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (coeff n x)
  rw [← ha, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk, RingHom.comp_apply]

@[simp]
theorem map_comp_apply {O' O'' : Type*} [CommRing O'] [CommRing O'']
    [Fact ¬IsUnit (p : O')] [Fact ¬IsUnit (p : O'')]
    (g : O' →+* O'') (f : O →+* O') (x : PreTilt O p) :
    map p (g.comp f) x = map p g (map p f x) := by
  rw [map_comp, RingHom.comp_apply]

end PreTilt

namespace TauCeti

section CommMonoid

variable {R : Type*} [CommMonoid R] {p : ℕ} {r : ℕ → R}

/-- In a compatible root sequence, every later root divides every earlier root. -/
theorem dvd_of_compatible_roots (hr : ∀ n, r (n + 1) ^ p = r n)
    {m n : ℕ} (hmn : m ≤ n) : r n ∣ r m := by
  by_cases hp : p = 0
  · have hone (n : ℕ) : r n = 1 := by
      simpa only [hp, pow_zero] using (hr n).symm
    simp only [hone, dvd_refl]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hpow : r (m + k) ^ p ^ k = r m := by
    simpa only [Perfection.coeffMonoidHom_mk] using
      Perfection.coeffMonoidHom_pow_p_pow' (⟨r, hr⟩ : Perfection R p) m k
  rw [← hpow]
  exact dvd_pow_self _ (pow_ne_zero k hp)

end CommMonoid

end TauCeti
