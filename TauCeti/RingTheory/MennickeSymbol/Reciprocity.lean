/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.MennickeSymbol.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# Quotient-unit homomorphisms, Kervaire reciprocity, and Euclidean vanishing

Over an arbitrary commutative ring `A` and ideal `I`, any `q ∈ I` and `a : A` with
`a - 1 ∈ Ideal.span {q}` determine a canonical monoid homomorphism
`unitHom : (A ⧸ Ideal.span {a})ˣ →* C`, sending the class of `b` to `s(a, b * q) = [b * q / a]`,
for any Mennicke symbol `s : MennickeSymbol A I C` into an arbitrary monoid `C`. Global units of
`A` map to `1` under `unitHom`.

The same elementary moves yield **Kervaire reciprocity** (Bass–Milnor–Serre Lemma 2.10): whenever
`q ∈ I`, `a ≡ 1 (mod q)`, `d ≡ 1 (mod q)`, and `IsCoprime a d`,
```
[d * q / a] = [a * q / d].
```
For a Euclidean domain `E` and `I = ⊤`, well-founded induction along the Euclidean division
relation shows that every Mennicke symbol is identically `1`.

## Main definitions

* `TauCeti.MennickeSymbol.unitHom`: the homomorphism `(A ⧸ Ideal.span {a})ˣ →* C` sending
  `b mod a ↦ [b * q / a]`.

## Main results

* `TauCeti.MennickeSymbol.map_eq_one_of_sub_one_mem_span`: `[b / a] = 1` whenever
  `a - 1 ∈ Ideal.span {b}`.
* `TauCeti.MennickeSymbol.unitHom_apply_of_mk_eq`: evaluation of `unitHom` on any representative.
* `TauCeti.MennickeSymbol.unitHom_map_unit`: `unitHom` kills the image of global units `Aˣ`.
* `TauCeti.MennickeSymbol.mem_mrange_unitHom`: every pair `(a, c)` with `q ∣ c` lies in the
  range of `unitHom`.
* `TauCeti.MennickeSymbol.kervaire_reciprocity`: `[d * q / a] = [a * q / d]` when `q ∈ I` and
  `a - 1, d - 1 ∈ Ideal.span {q}`.
* `TauCeti.MennickeSymbol.map_mul_fst_of_sub_one_mem_span`: denominator multiplication
  `[b / a₁ * a₂] = [b / a₁] * [b / a₂]` whenever `a₁ - 1, a₂ - 1 ∈ Ideal.span {q}` for some
  `q ∈ I`, over an arbitrary commutative ring `A` and monoid `C`.
* `TauCeti.MennickeSymbol.map_eq_one_of_euclideanDomain`: over a Euclidean domain, every Mennicke
  symbol at `I = ⊤` is trivial.

## References

* H. Bass, J. Milnor, and J.-P. Serre, *Solution of the congruence subgroup problem for `SL_n`
  (`n ≥ 3`) and `Sp_{2n}` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), §2, Lemmas 2.7 and 2.10,
  pp. 67–69.
-/

public section

namespace TauCeti

namespace MennickeSymbol

variable {A : Type*} [CommRing A] {I : Ideal A} {C : Type*} [Monoid C]

/-- If `a - 1 ∈ Ideal.span {q}`, then `a` and `q` are coprime. -/
private theorem isCoprime_of_sub_one_mem_span {q a : A} (ha : a - 1 ∈ Ideal.span {q}) :
    IsCoprime a q := by
  simpa using IsCoprime.add_one_left_of_dvd (Ideal.mem_span_singleton.mp ha)

/-- If `p.fst - 1 ∈ Ideal.span {p.snd}`, then `s p = 1`. -/
theorem map_eq_one_of_sub_one_mem_span (s : MennickeSymbol A I C) {p : MennickePair A I}
    (hp : p.fst - 1 ∈ Ideal.span {p.snd}) : s p = 1 := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hp
  have h1 : (p.shiftFst (-r)).fst = 1 := by
    simp only [MennickePair.shiftFst_fst]
    linear_combination hr
  rw [← s.map_shiftFst p (-r)]
  exact s.map_eq_one_of_fst_eq_one h1

/-- A representative of a unit in `A ⧸ Ideal.span {a}` is coprime to `a`. -/
private theorem isCoprime_of_quotientMk_eq_unit {a b : A} {u : (A ⧸ Ideal.span {a})ˣ}
    (hb : Ideal.Quotient.mk (Ideal.span {a}) b = u) : IsCoprime a b := by
  have htop : Ideal.span {b} ⊔ Ideal.span {a} = ⊤ :=
    Ideal.Quotient.isUnit_mk_iff.mp (hb ▸ u.isUnit)
  exact (Ideal.isCoprime_span_singleton_iff a b).mp
    (Ideal.isCoprime_iff_sup_eq.mpr (by rwa [sup_comm]))

/-- Construct the admissible pair `(a, b * q)` from `q ∈ I`, `a - 1 ∈ Ideal.span {q}`, and
`IsCoprime a b`. -/
private def mkMulPair {q : A} (hq : q ∈ I) {a : A} (ha : a - 1 ∈ Ideal.span {q}) {b : A}
    (hab : IsCoprime a b) : MennickePair A I where
  fst := a
  snd := b * q
  sub_one_mem := Ideal.span_singleton_le_iff_mem I |>.mpr hq ha
  snd_mem := I.mul_mem_left b hq
  isCoprime := hab.mul_right (isCoprime_of_sub_one_mem_span ha)

/-- For fixed `q ∈ I` and `a ≡ 1 (mod q)`, `s(a, b * q)` depends only on `b mod a`. -/
private theorem mkMulPair_congr (s : MennickeSymbol A I C) {q : A} (hq : q ∈ I) {a : A}
    (ha : a - 1 ∈ Ideal.span {q}) {b₁ b₂ : A} (h₁ : IsCoprime a b₁) (h₂ : IsCoprime a b₂)
    (heq : Ideal.Quotient.mk (Ideal.span {a}) b₁ = Ideal.Quotient.mk (Ideal.span {a}) b₂) :
    s (mkMulPair hq ha h₁) = s (mkMulPair hq ha h₂) := by
  have hsub : b₁ - b₂ ∈ Ideal.span {a} := (Ideal.Quotient.mk_eq_mk_iff_sub_mem b₁ b₂).mp heq
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hsub
  refine s.map_eq_of_snd_eq_add_mul rfl (I.mul_mem_left t hq) ?_
  simp only [mkMulPair]
  linear_combination q * ht

/-- For `q ∈ I` and `a - 1 ∈ Ideal.span {q}`, the canonical monoid homomorphism
`(A ⧸ Ideal.span {a})ˣ →* C` sending the class of `b` to `s(a, b * q) = [b * q / a]`. -/
noncomputable def unitHom (s : MennickeSymbol A I C) {q : A} (hq : q ∈ I) {a : A}
    (ha : a - 1 ∈ Ideal.span {q}) : (A ⧸ Ideal.span {a})ˣ →* C where
  toFun u :=
    let hb := (Ideal.Quotient.mk_surjective (u : A ⧸ Ideal.span {a})).choose_spec
    s (mkMulPair hq ha (isCoprime_of_quotientMk_eq_unit hb))
  map_one' := by
    have hspec :=
      (Ideal.Quotient.mk_surjective ((1 : (A ⧸ Ideal.span {a})ˣ) : A ⧸ Ideal.span {a})).choose_spec
    have h1 : Ideal.Quotient.mk (Ideal.span {a}) 1 =
        ((1 : (A ⧸ Ideal.span {a})ˣ) : A ⧸ Ideal.span {a}) := by
      simp
    rw [mkMulPair_congr s hq ha _ isCoprime_one_right (hspec.trans h1.symm)]
    exact s.map_eq_one_of_sub_one_mem_span (by simpa [mkMulPair] using ha)
  map_mul' u v := by
    set b₁ := (Ideal.Quotient.mk_surjective (u : A ⧸ Ideal.span {a})).choose
    have hb₁ : Ideal.Quotient.mk (Ideal.span {a}) b₁ = u :=
      (Ideal.Quotient.mk_surjective (u : A ⧸ Ideal.span {a})).choose_spec
    set b₂ := (Ideal.Quotient.mk_surjective (v : A ⧸ Ideal.span {a})).choose
    have hb₂ : Ideal.Quotient.mk (Ideal.span {a}) b₂ = v :=
      (Ideal.Quotient.mk_surjective (v : A ⧸ Ideal.span {a})).choose_spec
    have hspec := (Ideal.Quotient.mk_surjective
      ((u * v : (A ⧸ Ideal.span {a})ˣ) : A ⧸ Ideal.span {a})).choose_spec
    have hmul_mk : Ideal.Quotient.mk (Ideal.span {a}) (b₁ * b₂) =
        ((u * v : (A ⧸ Ideal.span {a})ˣ) : A ⧸ Ideal.span {a}) := by
      rw [map_mul, hb₁, hb₂, Units.val_mul]
    have hcop₁ : IsCoprime a b₁ := isCoprime_of_quotientMk_eq_unit hb₁
    have hcop₂ : IsCoprime a b₂ := isCoprime_of_quotientMk_eq_unit hb₂
    rw [mkMulPair_congr s hq ha _ (hcop₁.mul_right hcop₂) (hspec.trans hmul_mk.symm)]
    let p₁ := mkMulPair hq ha hcop₁
    let p₂ := mkMulPair hq ha hcop₂
    let p₁₂ := mkMulPair hq ha (hcop₁.mul_right hcop₂)
    let pq := mkMulPair hq ha isCoprime_one_right
    have hpq1 : s pq = 1 :=
      s.map_eq_one_of_sub_one_mem_span (by simpa [pq, mkMulPair] using ha)
    have hprod : p₁₂.mulSnd pq rfl = p₁.mulSnd p₂ rfl := by
      ext
      · simp [p₁₂, p₁, mkMulPair]
      · simp only [MennickePair.mulSnd_snd, p₁₂, pq, p₁, p₂, mkMulPair]
        ring
    calc
      s p₁₂ = s p₁₂ * s pq := by rw [hpq1, mul_one]
      _ = s (p₁₂.mulSnd pq rfl) := (s.map_mulSnd p₁₂ pq rfl).symm
      _ = s (p₁.mulSnd p₂ rfl) := by rw [hprod]
      _ = s p₁ * s p₂ := s.map_mulSnd p₁ p₂ rfl

/-- Evaluation of `unitHom` on any representative `b` of `u ∈ (A ⧸ Ideal.span {a})ˣ`. -/
theorem unitHom_apply_of_mk_eq (s : MennickeSymbol A I C) {q : A} (hq : q ∈ I) {a : A}
    (ha : a - 1 ∈ Ideal.span {q}) {u : (A ⧸ Ideal.span {a})ˣ} {b : A}
    (hb : Ideal.Quotient.mk (Ideal.span {a}) b = u) {p : MennickePair A I}
    (hp_fst : p.fst = a) (hp_snd : p.snd = b * q) :
    s.unitHom hq ha u = s p := by
  have hspec := (Ideal.Quotient.mk_surjective (u : A ⧸ Ideal.span {a})).choose_spec
  have hcop : IsCoprime a b := isCoprime_of_quotientMk_eq_unit hb
  have heq : mkMulPair hq ha hcop = p := by
    ext
    · simp [mkMulPair, hp_fst]
    · simp [mkMulPair, hp_snd]
  dsimp only [unitHom, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [mkMulPair_congr s hq ha _ hcop (hspec.trans hb.symm), heq]

/-- `unitHom` kills the image of global units `Aˣ`. -/
@[simp]
theorem unitHom_map_unit (s : MennickeSymbol A I C) {q : A} (hq : q ∈ I) {a : A}
    (ha : a - 1 ∈ Ideal.span {q}) (v : Aˣ) :
    s.unitHom hq ha (Units.map ↑(Ideal.Quotient.mk (Ideal.span {a})) v) = 1 := by
  let p : MennickePair A I := mkMulPair hq ha (isCoprime_of_quotientMk_eq_unit (u := Units.map
    ↑(Ideal.Quotient.mk (Ideal.span {a})) v) rfl)
  let pq : MennickePair A I := mkMulPair hq ha isCoprime_one_right
  rw [s.unitHom_apply_of_mk_eq hq ha (b := (v : A)) rfl (p := p) rfl rfl]
  have hpq : s p = s pq := s.map_unit_mul_snd v rfl (by simp [p, pq, mkMulPair])
  rw [hpq]
  exact s.map_eq_one_of_sub_one_mem_span (by simpa [pq, mkMulPair] using ha)

/-- Any pair `(a, c)` with `a - 1 ∈ Ideal.span {q}` and `c ∈ Ideal.span {q}` evaluates in the
multiplicative range of `unitHom`. -/
theorem mem_mrange_unitHom (s : MennickeSymbol A I C) {q : A} (hq : q ∈ I) {p : MennickePair A I}
    (ha : p.fst - 1 ∈ Ideal.span {q}) (hc : p.snd ∈ Ideal.span {q}) :
    s p ∈ MonoidHom.mrange (s.unitHom hq ha) := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hc
  have hcop : IsCoprime p.fst b := by
    have hp := p.isCoprime
    rw [hb] at hp
    exact hp.of_mul_right_right
  have htop : Ideal.span {b} ⊔ Ideal.span {p.fst} = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.mp (by
      rw [Ideal.isCoprime_span_singleton_iff]
      exact hcop.symm)
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {p.fst}) b) :=
    Ideal.Quotient.isUnit_mk_iff.mpr htop
  exact ⟨hu.unit, s.unitHom_apply_of_mk_eq hq ha (b := b) hu.unit_spec.symm rfl
    (by rw [hb, mul_comm])⟩

/-! ### Kervaire reciprocity -/

/-- Construct the admissible pair `(a, d - a)` from `a - 1, d - 1 ∈ I` and `IsCoprime a d`. -/
private def mkSubPair {a d : A} (ha : a - 1 ∈ I) (hd : d - 1 ∈ I) (had : IsCoprime a d) :
    MennickePair A I where
  fst := a
  snd := d - a
  sub_one_mem := ha
  snd_mem := by
    have heq : d - a = (d - 1) - (a - 1) := by ring
    rw [heq]
    exact sub_mem hd ha
  isCoprime := by
    obtain ⟨x, y, hxy⟩ := had
    exact ⟨x + y, y, by linear_combination hxy⟩

/-- Helper for Kervaire reciprocity: when `a - 1 ∈ Ideal.span {q}` and `d - 1 ∈ I`,
`[d * q / a] = [d - a / a]`. -/
private theorem map_mul_eq_map_sub (s : MennickeSymbol A I C) {q : A} (hq : q ∈ I)
    {p : MennickePair A I} {d : A} (ha : p.fst - 1 ∈ Ideal.span {q}) (hd : d - 1 ∈ I)
    (hp : p.snd = d * q) (had : IsCoprime p.fst d) :
    s p = s (mkSubPair p.sub_one_mem hd had) := by
  let pq : MennickePair A I :=
    { fst := p.fst
      snd := q
      sub_one_mem := p.sub_one_mem
      snd_mem := hq
      isCoprime := isCoprime_of_sub_one_mem_span ha }
  have hpq1 : s pq = 1 := s.map_eq_one_of_sub_one_mem_span ha
  let psub := mkSubPair p.sub_one_mem hd had
  have hshift : p.shiftSnd (neg_mem hq) = psub.mulSnd pq rfl := by
    ext
    · simp [psub, mkSubPair]
    · simp only [MennickePair.shiftSnd_snd, MennickePair.mulSnd_snd, psub, pq, mkSubPair, hp]
      ring
  rw [← s.map_shiftSnd p (neg_mem hq), hshift, s.map_mulSnd psub pq rfl, hpq1, mul_one]

/-- **Kervaire reciprocity** (Bass–Milnor–Serre Lemma 2.10): if `q ∈ I` and
`a - 1, d - 1 ∈ Ideal.span {q}`, then `[d * q / a] = [a * q / d]` for any Mennicke symbol into
an arbitrary monoid `C`. -/
theorem kervaire_reciprocity (s : MennickeSymbol A I C) {q : A} (hq : q ∈ I)
    {p₁ p₂ : MennickePair A I} (ha : p₁.fst - 1 ∈ Ideal.span {q})
    (hd : p₂.fst - 1 ∈ Ideal.span {q}) (hp₁ : p₁.snd = p₂.fst * q) (hp₂ : p₂.snd = p₁.fst * q) :
    s p₁ = s p₂ := by
  have had : IsCoprime p₁.fst p₂.fst := by
    have hc := p₁.isCoprime
    rw [hp₁] at hc
    exact hc.of_mul_right_left
  let r₁ := mkSubPair p₁.sub_one_mem p₂.sub_one_mem had
  let r₂ := mkSubPair p₂.sub_one_mem p₁.sub_one_mem had.symm
  have h1 : s p₁ = s r₁ := map_mul_eq_map_sub s hq ha p₂.sub_one_mem hp₁ had
  have h2 : s p₂ = s r₂ := map_mul_eq_map_sub s hq hd p₁.sub_one_mem hp₂ had.symm
  rw [h1, h2, ← s.map_shiftFst r₁ 1]
  refine (s.map_neg_snd ?_ ?_).symm
  · simp only [MennickePair.shiftFst_fst, r₁, r₂, mkSubPair]
    ring
  · simp only [MennickePair.shiftFst_snd, r₁, r₂, mkSubPair]
    ring

/-- Auxiliary step for denominator multiplication: if `q ∈ I`, `p.fst - 1 ∈ Ideal.span {q}`,
`d = p.snd + (1 - p.snd) * (p.fst * c)` satisfies `d - 1 ∈ Ideal.span {q}`, then
`s p = s(d, p.fst * q)`. -/
private theorem map_eq_kervaire_flip (s : MennickeSymbol A I C) {q : A} (hq : q ∈ I)
    {p : MennickePair A I} {c d : A} (ha : p.fst - 1 ∈ Ideal.span {q})
    (hd : d - 1 ∈ Ideal.span {q}) (hd_eq : d = p.snd + (1 - p.snd) * (p.fst * c))
    (hcop : IsCoprime d p.fst) :
    s p = s (mkMulPair hq hd hcop) := by
  let pq : MennickePair A I :=
    { fst := p.fst
      snd := q
      sub_one_mem := p.sub_one_mem
      snd_mem := hq
      isCoprime := isCoprime_of_sub_one_mem_span ha }
  have hpq1 : s pq = 1 := s.map_eq_one_of_sub_one_mem_span ha
  have hfst_d : IsCoprime p.fst d := hcop.symm
  let pbq : MennickePair A I := p.mulSnd pq rfl
  let pdq : MennickePair A I := mkMulPair hq ha hfst_d
  have ht : (1 - p.snd) * c * q ∈ I := I.mul_mem_left ((1 - p.snd) * c) hq
  have hshift : s pdq = s pbq := by
    refine s.map_eq_of_snd_eq_add_mul (by simp [pdq, pbq, mkMulPair]) ht ?_
    simp only [pdq, pbq, pq, mkMulPair, MennickePair.mulSnd_fst, MennickePair.mulSnd_snd, hd_eq]
    ring
  have hrec : s pdq = s (mkMulPair hq hd hcop) :=
    s.kervaire_reciprocity hq ha hd rfl rfl
  calc
    s p = s p * s pq := by rw [hpq1, mul_one]
    _ = s pbq := (s.map_mulSnd p pq rfl).symm
    _ = s pdq := hshift.symm
    _ = s (mkMulPair hq hd hcop) := hrec

/-- Denominator multiplication for pairs whose first entries are congruent to `1` modulo a single
element `q ∈ I`. This holds over an arbitrary commutative ring `A` and arbitrary monoid `C`
without any commutativity assumption on `C`. -/
theorem map_mul_fst_of_sub_one_mem_span (s : MennickeSymbol A I C) {q : A} (hq : q ∈ I)
    {p₁ p₂ p₁₂ : MennickePair A I} (hsnd₁ : p₂.snd = p₁.snd) (hsnd₂ : p₁₂.snd = p₁.snd)
    (hfst : p₁₂.fst = p₁.fst * p₂.fst)
    (ha₁ : p₁.fst - 1 ∈ Ideal.span {q}) (ha₂ : p₂.fst - 1 ∈ Ideal.span {q}) :
    s p₁₂ = s p₁ * s p₂ := by
  set b := p₁.snd
  have ha₁₂ : p₁₂.fst - 1 ∈ Ideal.span {q} := by
    have heq : p₁₂.fst - 1 = p₁.fst * (p₂.fst - 1) + (p₁.fst - 1) := by rw [hfst]; ring
    rw [heq]
    exact add_mem (Ideal.mul_mem_left _ _ ha₂) ha₁
  let d := b + (1 - b) * (p₁.fst * p₂.fst)
  have hd : d - 1 ∈ Ideal.span {q} := by
    have heq : d - 1 = (1 - b) * (p₁₂.fst - 1) := by simp only [d, hfst]; ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ ha₁₂
  have hcop₁ : IsCoprime d p₁.fst := by
    obtain ⟨x, y, hxy⟩ := p₁.isCoprime
    exact ⟨y, x - y * (1 - b) * p₂.fst, by simp only [d, b]; linear_combination hxy⟩
  have hcop₂ : IsCoprime d p₂.fst := by
    obtain ⟨x, y, hxy⟩ := p₂.isCoprime
    exact ⟨y, x - y * (1 - b) * p₁.fst, by simp only [d, b, ← hsnd₁]; linear_combination hxy⟩
  have hcop₁₂ : IsCoprime d p₁₂.fst := by rw [hfst]; exact hcop₁.mul_right hcop₂
  have h₁ := map_eq_kervaire_flip s hq (c := p₂.fst) (d := d) ha₁ hd rfl hcop₁
  have h₂ := map_eq_kervaire_flip s hq (c := p₁.fst) (d := d) ha₂ hd
    (by simp only [d, b, hsnd₁]; ring) hcop₂
  have h₁₂ := map_eq_kervaire_flip s hq (c := 1) (d := d) ha₁₂ hd
    (by simp only [d, b, hsnd₂, hfst]; ring) hcop₁₂
  let r₁ := mkMulPair hq hd hcop₁
  let r₂ := mkMulPair hq hd hcop₂
  let r₁₂ := mkMulPair hq hd hcop₁₂
  let rq := mkMulPair hq hd isCoprime_one_right
  have hrq1 : s rq = 1 := s.map_eq_one_of_sub_one_mem_span (by simpa [rq, mkMulPair] using hd)
  have hprod : r₁₂.mulSnd rq rfl = r₁.mulSnd r₂ rfl := by
    ext
    · simp [r₁₂, r₁, mkMulPair]
    · simp only [MennickePair.mulSnd_snd, r₁₂, rq, r₁, r₂, mkMulPair, hfst]
      ring
  calc
    s p₁₂ = s r₁₂ := h₁₂
    _ = s r₁₂ * s rq := by rw [hrq1, mul_one]
    _ = s (r₁₂.mulSnd rq rfl) := (s.map_mulSnd r₁₂ rq rfl).symm
    _ = s (r₁.mulSnd r₂ rfl) := by rw [hprod]
    _ = s r₁ * s r₂ := s.map_mulSnd r₁ r₂ rfl
    _ = s p₁ * s p₂ := by rw [h₁, h₂]

/-! ### Vanishing over a Euclidean domain -/

/-- Over a Euclidean domain `E`, every Mennicke symbol at `I = ⊤` into an arbitrary monoid `C`
is identically `1`. -/
theorem map_eq_one_of_euclideanDomain {E : Type*} [EuclideanDomain E]
    (s : MennickeSymbol E ⊤ C) (p : MennickePair E ⊤) : s p = 1 := by
  suffices h : ∀ x : E, ∀ q : MennickePair E ⊤, q.fst = x ∨ q.snd = x → s q = 1 by
    exact h p.fst p (Or.inl rfl)
  intro x
  refine WellFounded.induction
    (C := fun x ↦ ∀ q : MennickePair E ⊤, q.fst = x ∨ q.snd = x → s q = 1)
    EuclideanDomain.r_wellFounded x ?_
  intro x ih q hq
  by_cases hx : x = 0
  · subst hx
    rcases hq with hfst | hsnd
    · have hcop := q.isCoprime
      rw [hfst] at hcop
      exact s.map_eq_one_of_isUnit_snd (isCoprime_zero_left.mp hcop)
    · exact s.map_eq_one_of_snd_eq_zero hsnd
  · rcases hq with hfst | hsnd
    · have hlt : EuclideanDomain.r (q.snd % x) x := EuclideanDomain.mod_lt q.snd hx
      let q' := q.shiftSnd (Submodule.mem_top (x := -(q.snd / x)))
      have hsnd' : q'.snd = q.snd % x := by
        simp only [q', MennickePair.shiftSnd_snd, hfst]
        linear_combination -EuclideanDomain.div_add_mod q.snd x
      rw [← s.map_shiftSnd q (Submodule.mem_top (x := -(q.snd / x)))]
      exact ih (q.snd % x) hlt q' (Or.inr hsnd')
    · have hlt : EuclideanDomain.r (q.fst % x) x := EuclideanDomain.mod_lt q.fst hx
      let q' := q.shiftFst (-(q.fst / x))
      have hfst' : q'.fst = q.fst % x := by
        simp only [q', MennickePair.shiftFst_fst, hsnd]
        linear_combination -EuclideanDomain.div_add_mod q.fst x
      rw [← s.map_shiftFst q (-(q.fst / x))]
      exact ih (q.fst % x) hlt q' (Or.inl hfst')

end MennickeSymbol

end TauCeti
