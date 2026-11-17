/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.LinearCombination

/-!
# Admissible pairs and Mennicke symbols

Let `A` be a commutative ring and `I` an ideal of `A`. The set `W(A, I)` of **admissible pairs**
modulo `I` (`TauCeti.MennickePair A I`) consists of unimodular pairs `(a, b) : A × A` satisfying
`a - 1 ∈ I`, `b ∈ I`, and `IsCoprime a b`.

A **Mennicke symbol** (`TauCeti.MennickeSymbol A I C`) with values in an arbitrary monoid `C`
(not assumed commutative, nor even a group) is a function `s : MennickePair A I → C` satisfying:
* `s(1, 0) = 1`,
* **MS1a** (`map_shiftSnd`): `s(a, b + t * a) = s(a, b)` for `t ∈ I`,
* **MS1b** (`map_shiftFst`): `s(a + t * b, b) = s(a, b)` for `t : A`,
* **MS2** (`map_mulSnd`): `s(a, b₁ * b₂) = s(a, b₁) * s(a, b₂)` whenever `(a, b₁)` and `(a, b₂)`
  are admissible pairs.

In the notation of Bass–Milnor–Serre, `s(a, b)` is written `[b / a]`. The asymmetry between the
two elementary moves is intentional: `b` may only be shifted by `I`-multiples of `a`, whereas `a`
may be shifted by arbitrary `A`-multiples of `b`.

Every value `s(a, b)` in an arbitrary monoid `C` is automatically a two-sided unit, with explicit
inverse `s(a, y * (1 - a))` whenever `x * a + y * b = 1`. In a left-cancellative monoid (in
particular, in any group), `s(1, 0) = 1` follows automatically from `MS2` on `0 * 0 = 0`
(`MennickeSymbol.ofIsLeftCancelMul`).

## Main definitions

* `TauCeti.MennickePair`: admissible pairs `(a, b)` with `a - 1 ∈ I`, `b ∈ I`, and `IsCoprime a b`.
* `TauCeti.MennickeSymbol`: bundled Mennicke symbols `MennickePair A I → C` into an arbitrary
  monoid `C`.
* `TauCeti.MennickeSymbol.toUnits`: canonical factorization of any Mennicke symbol into `Cˣ`.

## Main results

* `TauCeti.MennickePair.subsingleton_bot`: when `I = ⊥`, `(1, 0)` is the unique admissible pair.
* `TauCeti.MennickeSymbol.map_mul_one_sub_fst`: `s(a, b * (1 - a)) = s(a, b)`.
* `TauCeti.MennickeSymbol.map_unit_mul_snd`: `s(a, u * b) = s(a, b)` for any global unit `u : Aˣ`.
* `TauCeti.MennickeSymbol.map_eq_one_of_isUnit_fst`, `map_eq_one_of_snd_eq_zero`, and
  `map_eq_one_of_isUnit_snd`: `[b / u] = [0 / u] = [v / a] = 1` for units `u, v`.
* `TauCeti.MennickeSymbol.map_eq_one_of_fst_congr_unit` and
  `TauCeti.MennickeSymbol.map_eq_one_of_snd_congr_unit`: near-unit reductions; if `a` is congruent
  to a unit modulo `b`, or `b` is congruent to a unit modulo `a` (even when that unit does not lie
  in `I`), then `s(a, b) = 1`.
* `TauCeti.MennickeSymbol.isUnit`: every value of a Mennicke symbol in an arbitrary monoid is a
  unit.

## References

* H. Bass, J. Milnor, and J.-P. Serre, *Solution of the congruence subgroup problem for `SL_n`
  (`n ≥ 3`) and `Sp_{2n}` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), §2, Definition 2.5 and
  Lemmas 2.1–2.2, pp. 65–66.
-/

public section

namespace TauCeti

section MennickePair

variable {A : Type*} [CommRing A] {I J : Ideal A}

/-- An admissible pair `(a, b)` modulo an ideal `I` of a commutative ring `A`: unimodular with
`a - 1 ∈ I`, `b ∈ I`, and `IsCoprime a b`. -/
@[ext]
structure MennickePair (A : Type*) [CommRing A] (I : Ideal A) where
  /-- First entry of the pair (`a` in `[b / a]`). -/
  fst : A
  /-- Second entry of the pair (`b` in `[b / a]`). -/
  snd : A
  /-- Congruence condition `a ≡ 1 (mod I)`. -/
  sub_one_mem : fst - 1 ∈ I
  /-- Congruence condition `b ≡ 0 (mod I)`. -/
  snd_mem : snd ∈ I
  /-- Unimodularity `a * A + b * A = A`. -/
  isCoprime : IsCoprime fst snd

namespace MennickePair

/-- The trivial admissible pair `(1, 0)`. -/
def oneZero : MennickePair A I where
  fst := 1
  snd := 0
  sub_one_mem := by simp
  snd_mem := zero_mem I
  isCoprime := isCoprime_one_left

@[simp] theorem oneZero_fst : (oneZero (A := A) (I := I)).fst = 1 := (rfl)
@[simp] theorem oneZero_snd : (oneZero (A := A) (I := I)).snd = 0 := (rfl)

instance : Inhabited (MennickePair A I) := ⟨oneZero⟩

/-- At the zero ideal `I = ⊥`, every admissible pair is `(1, 0)`. -/
theorem eq_oneZero_of_bot (p : MennickePair A ⊥) : p = oneZero := by
  ext
  · have h : p.fst - 1 = 0 := Ideal.mem_bot.mp p.sub_one_mem
    exact sub_eq_zero.mp h
  · exact Ideal.mem_bot.mp p.snd_mem

instance subsingleton_bot : Subsingleton (MennickePair A ⊥) :=
  ⟨fun p q ↦ (eq_oneZero_of_bot p).trans (eq_oneZero_of_bot q).symm⟩

/-- Elementary move MS1a: shift the second entry by `t * fst` for `t ∈ I`. -/
def shiftSnd (p : MennickePair A I) {t : A} (ht : t ∈ I) : MennickePair A I where
  fst := p.fst
  snd := p.snd + t * p.fst
  sub_one_mem := p.sub_one_mem
  snd_mem := add_mem p.snd_mem (I.mul_mem_right p.fst ht)
  isCoprime := by
    obtain ⟨x, y, hxy⟩ := p.isCoprime
    exact ⟨x - y * t, y, by linear_combination hxy⟩

@[simp] theorem shiftSnd_fst (p : MennickePair A I) {t : A} (ht : t ∈ I) :
    (p.shiftSnd ht).fst = p.fst := (rfl)

@[simp] theorem shiftSnd_snd (p : MennickePair A I) {t : A} (ht : t ∈ I) :
    (p.shiftSnd ht).snd = p.snd + t * p.fst := (rfl)

/-- Elementary move MS1b: shift the first entry by `t * snd` for any `t : A`. -/
def shiftFst (p : MennickePair A I) (t : A) : MennickePair A I where
  fst := p.fst + t * p.snd
  snd := p.snd
  sub_one_mem := by
    have h : p.fst + t * p.snd - 1 = (p.fst - 1) + t * p.snd := by ring
    rw [h]
    exact add_mem p.sub_one_mem (I.mul_mem_left t p.snd_mem)
  snd_mem := p.snd_mem
  isCoprime := by
    obtain ⟨x, y, hxy⟩ := p.isCoprime
    exact ⟨x, y - x * t, by linear_combination hxy⟩

@[simp] theorem shiftFst_fst (p : MennickePair A I) (t : A) :
    (p.shiftFst t).fst = p.fst + t * p.snd := (rfl)

@[simp] theorem shiftFst_snd (p : MennickePair A I) (t : A) :
    (p.shiftFst t).snd = p.snd := (rfl)

/-- Multiply the second entries of two admissible pairs sharing the same first entry. -/
def mulSnd (p q : MennickePair A I) (h : p.fst = q.fst) : MennickePair A I where
  fst := p.fst
  snd := p.snd * q.snd
  sub_one_mem := p.sub_one_mem
  snd_mem := I.mul_mem_right q.snd p.snd_mem
  isCoprime := p.isCoprime.mul_right (h ▸ q.isCoprime)

@[simp] theorem mulSnd_fst (p q : MennickePair A I) (h : p.fst = q.fst) :
    (p.mulSnd q h).fst = p.fst := (rfl)

@[simp] theorem mulSnd_snd (p q : MennickePair A I) (h : p.fst = q.fst) :
    (p.mulSnd q h).snd = p.snd * q.snd := (rfl)

/-- The admissible pair `(a, 1 - a)` associated to any `a` congruent to `1` modulo `I`. -/
def oneSubFst (a : A) (ha : a - 1 ∈ I) : MennickePair A I where
  fst := a
  snd := 1 - a
  sub_one_mem := ha
  snd_mem := by
    have h : 1 - a = -(a - 1) := by ring
    rw [h]
    exact neg_mem ha
  isCoprime := ⟨1, 1, by ring⟩

@[simp] theorem oneSubFst_fst (a : A) (ha : a - 1 ∈ I) : (oneSubFst a ha).fst = a := (rfl)
@[simp] theorem oneSubFst_snd (a : A) (ha : a - 1 ∈ I) : (oneSubFst a ha).snd = 1 - a := (rfl)

/-- Given a Bézout identity `x * p.fst + y * p.snd = 1`, the admissible pair
`(p.fst, y * (1 - p.fst))` whose symbol value is the explicit two-sided inverse of `s p`. -/
def bezoutInvPair (p : MennickePair A I) {x y : A} (hxy : x * p.fst + y * p.snd = 1) :
    MennickePair A I where
  fst := p.fst
  snd := y * (1 - p.fst)
  sub_one_mem := p.sub_one_mem
  snd_mem := by
    have h : 1 - p.fst = -(p.fst - 1) := by ring
    rw [h]
    exact I.mul_mem_left y (neg_mem p.sub_one_mem)
  isCoprime := by
    have hy : IsCoprime p.fst y := ⟨x, p.snd, by linear_combination hxy⟩
    exact hy.mul_right ⟨1, 1, by ring⟩

@[simp] theorem bezoutInvPair_fst (p : MennickePair A I) {x y : A}
    (hxy : x * p.fst + y * p.snd = 1) :
    (p.bezoutInvPair hxy).fst = p.fst := (rfl)

@[simp] theorem bezoutInvPair_snd (p : MennickePair A I) {x y : A}
    (hxy : x * p.fst + y * p.snd = 1) :
    (p.bezoutInvPair hxy).snd = y * (1 - p.fst) := (rfl)

/-- Inclusion of admissible pairs induced by an inclusion of ideals `J ≤ I`. -/
def mapIdeal (hJI : J ≤ I) (p : MennickePair A J) : MennickePair A I where
  fst := p.fst
  snd := p.snd
  sub_one_mem := hJI p.sub_one_mem
  snd_mem := hJI p.snd_mem
  isCoprime := p.isCoprime

@[simp] theorem mapIdeal_fst (hJI : J ≤ I) (p : MennickePair A J) :
    (p.mapIdeal hJI).fst = p.fst := (rfl)

@[simp] theorem mapIdeal_snd (hJI : J ≤ I) (p : MennickePair A J) :
    (p.mapIdeal hJI).snd = p.snd := (rfl)

theorem mapIdeal_injective (hJI : J ≤ I) : Function.Injective (mapIdeal hJI) := by
  intro p q h
  ext
  · simpa using congrArg MennickePair.fst h
  · simpa using congrArg MennickePair.snd h

@[simp] theorem mapIdeal_id (p : MennickePair A I) : p.mapIdeal le_rfl = p := by
  ext <;> simp

@[simp] theorem mapIdeal_comp {K : Ideal A} (hJK : J ≤ K) (hKI : K ≤ I) (p : MennickePair A J) :
    (p.mapIdeal hJK).mapIdeal hKI = p.mapIdeal (hJK.trans hKI) := by
  ext <;> simp

@[simp] theorem mapIdeal_oneZero (hJI : J ≤ I) :
    (oneZero (A := A) (I := J)).mapIdeal hJI = oneZero := by
  ext <;> simp

@[simp] theorem mapIdeal_shiftSnd (hJI : J ≤ I) (p : MennickePair A J) {t : A} (ht : t ∈ J) :
    (p.shiftSnd ht).mapIdeal hJI = (p.mapIdeal hJI).shiftSnd (hJI ht) := by
  ext <;> simp

@[simp] theorem mapIdeal_shiftFst (hJI : J ≤ I) (p : MennickePair A J) (t : A) :
    (p.shiftFst t).mapIdeal hJI = (p.mapIdeal hJI).shiftFst t := by
  ext <;> simp

@[simp] theorem mapIdeal_mulSnd (hJI : J ≤ I) (p q : MennickePair A J) (h : p.fst = q.fst) :
    (p.mulSnd q h).mapIdeal hJI =
      (p.mapIdeal hJI).mulSnd (q.mapIdeal hJI) (by simp [h]) := by
  ext <;> simp

/-- Pushforward of an admissible pair along a ring homomorphism `f : A →+* B` with `I.map f ≤ J`. -/
def map {B : Type*} [CommRing B] {J : Ideal B} (f : A →+* B) (hf : I.map f ≤ J)
    (p : MennickePair A I) : MennickePair B J where
  fst := f p.fst
  snd := f p.snd
  sub_one_mem := by
    rw [← map_one f, ← map_sub]
    exact hf (Ideal.mem_map_of_mem f p.sub_one_mem)
  snd_mem := hf (Ideal.mem_map_of_mem f p.snd_mem)
  isCoprime := p.isCoprime.map f

@[simp] theorem map_fst {B : Type*} [CommRing B] {J : Ideal B} (f : A →+* B) (hf : I.map f ≤ J)
    (p : MennickePair A I) : (p.map f hf).fst = f p.fst := (rfl)

@[simp] theorem map_snd {B : Type*} [CommRing B] {J : Ideal B} (f : A →+* B) (hf : I.map f ≤ J)
    (p : MennickePair A I) : (p.map f hf).snd = f p.snd := (rfl)

@[simp] theorem map_id (p : MennickePair A I) :
    p.map (RingHom.id A) (by simp) = p := by
  ext <;> simp

@[simp] theorem map_comp {B C : Type*} [CommRing B] [CommRing C] {J : Ideal B} {K : Ideal C}
    (f : A →+* B) (g : B →+* C) (hf : I.map f ≤ J) (hg : J.map g ≤ K) (p : MennickePair A I) :
    (p.map f hf).map g hg =
      p.map (g.comp f) (by rw [← Ideal.map_map]; exact (Ideal.map_mono hf).trans hg) := by
  ext <;> simp

@[simp] theorem map_oneZero {B : Type*} [CommRing B] {J : Ideal B} (f : A →+* B)
    (hf : I.map f ≤ J) :
    (oneZero (A := A) (I := I)).map f hf = oneZero := by
  ext <;> simp

@[simp] theorem map_shiftSnd {B : Type*} [CommRing B] {J : Ideal B} (f : A →+* B)
    (hf : I.map f ≤ J) (p : MennickePair A I) {t : A} (ht : t ∈ I) :
    (p.shiftSnd ht).map f hf = (p.map f hf).shiftSnd (hf (Ideal.mem_map_of_mem f ht)) := by
  ext <;> simp

@[simp] theorem map_shiftFst {B : Type*} [CommRing B] {J : Ideal B} (f : A →+* B)
    (hf : I.map f ≤ J) (p : MennickePair A I) (t : A) :
    (p.shiftFst t).map f hf = (p.map f hf).shiftFst (f t) := by
  ext <;> simp

@[simp] theorem map_mulSnd {B : Type*} [CommRing B] {J : Ideal B} (f : A →+* B)
    (hf : I.map f ≤ J) (p q : MennickePair A I) (h : p.fst = q.fst) :
    (p.mulSnd q h).map f hf =
      (p.map f hf).mulSnd (q.map f hf) (by simp [h]) := by
  ext <;> simp

end MennickePair

end MennickePair

section MennickeSymbol

variable {A : Type*} [CommRing A] {I J : Ideal A} {C D : Type*} [Monoid C] [Monoid D]

/-- A Mennicke symbol on `(A, I)` with values in an arbitrary monoid `C`.

In Bass–Milnor–Serre notation, `s p` for `p = (a, b)` is written `[b / a]`. No commutativity
assumption is placed on `C`. -/
structure MennickeSymbol (A : Type*) [CommRing A] (I : Ideal A) (C : Type*) [Monoid C] where
  /-- Underlying function on admissible pairs. -/
  toFun : MennickePair A I → C
  /-- Normalization on the trivial pair `(1, 0)`. -/
  map_oneZero' : toFun .oneZero = 1
  /-- Elementary move MS1a: invariance under `(a, b) ↦ (a, b + t * a)` for `t ∈ I`. -/
  map_shiftSnd' : ∀ (p : MennickePair A I) {t : A} (ht : t ∈ I),
    toFun (p.shiftSnd ht) = toFun p
  /-- Elementary move MS1b: invariance under `(a, b) ↦ (a + t * b, b)` for `t : A`. -/
  map_shiftFst' : ∀ (p : MennickePair A I) (t : A),
    toFun (p.shiftFst t) = toFun p
  /-- Multiplicativity in the second entry (MS2): `s(a, b₁ * b₂) = s(a, b₁) * s(a, b₂)`. -/
  map_mulSnd' : ∀ (p q : MennickePair A I) (h : p.fst = q.fst),
    toFun (p.mulSnd q h) = toFun p * toFun q

namespace MennickeSymbol

instance : FunLike (MennickeSymbol A I C) (MennickePair A I) C where
  coe s := s.toFun
  coe_injective := fun f g h ↦ by
    cases f
    cases g
    congr

@[ext]
theorem ext {s₁ s₂ : MennickeSymbol A I C} (h : ∀ p, s₁ p = s₂ p) : s₁ = s₂ :=
  DFunLike.ext s₁ s₂ h

@[simp]
theorem coe_mk (f : MennickePair A I → C) (h0 h1 h2 h3) :
    ⇑(⟨f, h0, h1, h2, h3⟩ : MennickeSymbol A I C) = f := (rfl)

/-- In a left-cancellative monoid (such as any group), `s(1, 0) = 1` follows from `MS2` applied to
`(1, 0) * (1, 0) = (1, 0)`. -/
def ofIsLeftCancelMul [IsLeftCancelMul C] (toFun : MennickePair A I → C)
    (map_shiftSnd' : ∀ (p : MennickePair A I) {t : A} (ht : t ∈ I),
      toFun (p.shiftSnd ht) = toFun p)
    (map_shiftFst' : ∀ (p : MennickePair A I) (t : A),
      toFun (p.shiftFst t) = toFun p)
    (map_mulSnd' : ∀ (p q : MennickePair A I) (h : p.fst = q.fst),
      toFun (p.mulSnd q h) = toFun p * toFun q) : MennickeSymbol A I C where
  toFun := toFun
  map_oneZero' := by
    have hmul := map_mulSnd' .oneZero .oneZero rfl
    have heq : MennickePair.oneZero.mulSnd MennickePair.oneZero rfl =
        (MennickePair.oneZero : MennickePair A I) := by
      ext <;> simp
    rw [heq] at hmul
    exact (mul_left_cancel (a := toFun .oneZero) (by rw [mul_one, ← hmul])).symm
  map_shiftSnd' := map_shiftSnd'
  map_shiftFst' := map_shiftFst'
  map_mulSnd' := map_mulSnd'

@[simp]
theorem ofIsLeftCancelMul_apply [IsLeftCancelMul C] (f : MennickePair A I → C) (h1 h2 h3)
    (p : MennickePair A I) :
    ofIsLeftCancelMul f h1 h2 h3 p = f p := (rfl)

@[simp]
theorem map_oneZero (s : MennickeSymbol A I C) : s .oneZero = 1 :=
  s.map_oneZero'

@[simp]
theorem map_shiftSnd (s : MennickeSymbol A I C) (p : MennickePair A I) {t : A} (ht : t ∈ I) :
    s (p.shiftSnd ht) = s p :=
  s.map_shiftSnd' p ht

@[simp]
theorem map_shiftFst (s : MennickeSymbol A I C) (p : MennickePair A I) (t : A) :
    s (p.shiftFst t) = s p :=
  s.map_shiftFst' p t

theorem map_mulSnd (s : MennickeSymbol A I C) (p q : MennickePair A I) (h : p.fst = q.fst) :
    s (p.mulSnd q h) = s p * s q :=
  s.map_mulSnd' p q h

/-- Invariance of `s` under adding an `I`-multiple of `fst` to `snd`, phrased on two pairs. -/
theorem map_eq_of_snd_eq_add_mul (s : MennickeSymbol A I C) {p q : MennickePair A I}
    (hfst : q.fst = p.fst) {t : A} (ht : t ∈ I) (hsnd : q.snd = p.snd + t * p.fst) :
    s q = s p := by
  have heq : q = p.shiftSnd ht := by
    ext
    · simp [hfst]
    · simp [hsnd]
  rw [heq, s.map_shiftSnd]

/-- Invariance of `s` under adding an `A`-multiple of `snd` to `fst`, phrased on two pairs. -/
theorem map_eq_of_fst_eq_add_mul (s : MennickeSymbol A I C) {p q : MennickePair A I}
    (hsnd : q.snd = p.snd) {t : A} (hfst : q.fst = p.fst + t * p.snd) :
    s q = s p := by
  have heq : q = p.shiftFst t := by
    ext
    · simp [hfst]
    · simp [hsnd]
  rw [heq, s.map_shiftFst]

/-- Multiplicativity in `snd`, phrased on any triple of pairs with the same first entry. -/
theorem map_mul_snd_eq (s : MennickeSymbol A I C) {p q r : MennickePair A I}
    (hq : p.fst = q.fst) (hr_fst : r.fst = p.fst) (hr_snd : r.snd = p.snd * q.snd) :
    s r = s p * s q := by
  have heq : r = p.mulSnd q hq := by
    ext
    · simp [hr_fst]
    · simp [hr_snd]
  rw [heq, s.map_mulSnd]

/-- Pairs with the same first entry have commuting symbol values. -/
theorem commute_of_fst_eq (s : MennickeSymbol A I C) {p q : MennickePair A I}
    (h : p.fst = q.fst) : Commute (s p) (s q) := by
  unfold Commute SemiconjBy
  have heq : p.mulSnd q h = q.mulSnd p h.symm := by
    ext
    · simp [h]
    · simp [mul_comm]
  rw [← s.map_mulSnd p q h, heq, s.map_mulSnd q p h.symm]

/-- The trivial Mennicke symbol sending every admissible pair to `1`. -/
def trivial : MennickeSymbol A I C where
  toFun _ := 1
  map_oneZero' := rfl
  map_shiftSnd' _ _ _ := rfl
  map_shiftFst' _ _ := rfl
  map_mulSnd' _ _ _ := (mul_one 1).symm

@[simp] theorem trivial_apply (p : MennickePair A I) :
    (trivial (A := A) (I := I) (C := C)) p = 1 := (rfl)

instance : Inhabited (MennickeSymbol A I C) := ⟨trivial⟩

/-- Post-composition of a Mennicke symbol with a monoid homomorphism. -/
def comp (s : MennickeSymbol A I C) (φ : C →* D) : MennickeSymbol A I D where
  toFun p := φ (s p)
  map_oneZero' := by simp
  map_shiftSnd' p _ _ := by simp
  map_shiftFst' p _ := by simp
  map_mulSnd' p q h := by rw [s.map_mulSnd p q h, map_mul]

@[simp] theorem comp_apply (s : MennickeSymbol A I C) (φ : C →* D) (p : MennickePair A I) :
    s.comp φ p = φ (s p) := (rfl)

@[simp] theorem comp_id (s : MennickeSymbol A I C) : s.comp (MonoidHom.id C) = s :=
  ext fun _ ↦ rfl

theorem comp_assoc {E : Type*} [Monoid E] (s : MennickeSymbol A I C) (φ : C →* D) (ψ : D →* E) :
    (s.comp φ).comp ψ = s.comp (ψ.comp φ) :=
  ext fun _ ↦ rfl

/-- Restriction of a Mennicke symbol along an inclusion of ideals `J ≤ I`. -/
def comapIdeal (hJI : J ≤ I) (s : MennickeSymbol A I C) : MennickeSymbol A J C where
  toFun p := s (p.mapIdeal hJI)
  map_oneZero' := by simp
  map_shiftSnd' p _ _ := by simp
  map_shiftFst' p _ := by simp
  map_mulSnd' p q h := by
    rw [MennickePair.mapIdeal_mulSnd, s.map_mulSnd]

@[simp] theorem comapIdeal_apply (hJI : J ≤ I) (s : MennickeSymbol A I C) (p : MennickePair A J) :
    s.comapIdeal hJI p = s (p.mapIdeal hJI) := (rfl)

@[simp] theorem comapIdeal_id (s : MennickeSymbol A I C) : s.comapIdeal le_rfl = s :=
  ext fun _ ↦ by simp

theorem comapIdeal_comp {K : Ideal A} (hJK : J ≤ K) (hKI : K ≤ I) (s : MennickeSymbol A I C) :
    (s.comapIdeal hKI).comapIdeal hJK = s.comapIdeal (hJK.trans hKI) :=
  ext fun _ ↦ by simp

/-- Pullback of a Mennicke symbol along a ring homomorphism `f : A →+* B` with `I.map f ≤ J`. -/
def comapRingHom {B : Type*} [CommRing B] {J : Ideal B} (f : A →+* B) (hf : I.map f ≤ J)
    (s : MennickeSymbol B J C) : MennickeSymbol A I C where
  toFun p := s (p.map f hf)
  map_oneZero' := by simp
  map_shiftSnd' p _ _ := by simp
  map_shiftFst' p _ := by simp
  map_mulSnd' p q h := by
    rw [MennickePair.map_mulSnd, s.map_mulSnd]

@[simp] theorem comapRingHom_apply {B : Type*} [CommRing B] {J : Ideal B} (f : A →+* B)
    (hf : I.map f ≤ J) (s : MennickeSymbol B J C) (p : MennickePair A I) :
    s.comapRingHom f hf p = s (p.map f hf) := (rfl)

@[simp] theorem comapRingHom_id (s : MennickeSymbol A I C) :
    s.comapRingHom (RingHom.id A) (by simp) = s :=
  ext fun _ ↦ by simp

theorem comapRingHom_comp {B E : Type*} [CommRing B] [CommRing E] {J : Ideal B} {K : Ideal E}
    (f : A →+* B) (g : B →+* E) (hf : I.map f ≤ J) (hg : J.map g ≤ K)
    (s : MennickeSymbol E K C) :
    (s.comapRingHom g hg).comapRingHom f hf =
      s.comapRingHom (g.comp f) (by rw [← Ideal.map_map]; exact (Ideal.map_mono hf).trans hg) :=
  ext fun _ ↦ by simp

/-! ### Elementary identities over an arbitrary commutative ring -/

/-- Any pair with first entry `1` has symbol value `1`: `[b / 1] = 1`. -/
theorem map_eq_one_of_fst_eq_one (s : MennickeSymbol A I C) {p : MennickePair A I}
    (h : p.fst = 1) : s p = 1 := by
  have hneg : -p.snd ∈ I := neg_mem p.snd_mem
  have hshift : p.shiftSnd hneg = .oneZero := by
    ext
    · simp [h]
    · simp [h]
  rw [← s.map_shiftSnd p hneg, hshift, s.map_oneZero]

/-- `[1 - a / a] = 1`. -/
@[simp]
theorem map_oneSubFst (s : MennickeSymbol A I C) (a : A) (ha : a - 1 ∈ I) :
    s (.oneSubFst a ha) = 1 := by
  have h1 : ((MennickePair.oneSubFst a ha).shiftFst 1).fst = 1 := by simp
  rw [← s.map_shiftFst (.oneSubFst a ha) 1]
  exact s.map_eq_one_of_fst_eq_one h1

/-- `[u * (1 - a) / a] = 1` for any global unit `u : Aˣ`. -/
theorem map_eq_one_of_snd_eq_unit_mul_one_sub (s : MennickeSymbol A I C) {p : MennickePair A I}
    (u : Aˣ) (hp : p.snd = u * (1 - p.fst)) : s p = 1 := by
  have h1 : (p.shiftFst (u⁻¹ : Aˣ)).fst = 1 := by
    simp only [MennickePair.shiftFst_fst, hp]
    calc
      p.fst + (↑u⁻¹ : A) * (↑u * (1 - p.fst))
        = p.fst + ((↑u⁻¹ : A) * ↑u) * (1 - p.fst) := by ring
      _ = 1 := by simp
  rw [← s.map_shiftFst p (u⁻¹ : Aˣ)]
  exact s.map_eq_one_of_fst_eq_one h1

/-- Equivalence of `(a, b)` and `(a, b * (1 - a))`: `[b * (1 - a) / a] = [b / a]`. -/
theorem map_mul_one_sub_fst (s : MennickeSymbol A I C) {p q : MennickePair A I}
    (hfst : q.fst = p.fst) (hsnd : q.snd = p.snd * (1 - p.fst)) : s q = s p := by
  refine s.map_eq_of_snd_eq_add_mul hfst (neg_mem p.snd_mem) ?_
  rw [hsnd]
  ring

/-- Global-unit scaling invariance: `[u * b / a] = [b / a]` for any `u : Aˣ`. -/
theorem map_unit_mul_snd (s : MennickeSymbol A I C) {p q : MennickePair A I} (u : Aˣ)
    (hfst : q.fst = p.fst) (hsnd : q.snd = u * p.snd) : s q = s p := by
  have hsub : 1 - p.fst ∈ I := by
    have heq : 1 - p.fst = -(p.fst - 1) := by ring
    rw [heq]
    exact neg_mem p.sub_one_mem
  have hcu : IsCoprime p.fst (u : A) := ⟨0, (↑u⁻¹ : A), by simp⟩
  let r : MennickePair A I :=
    { fst := p.fst
      snd := (u : A) * (1 - p.fst)
      sub_one_mem := p.sub_one_mem
      snd_mem := I.mul_mem_left (u : A) hsub
      isCoprime := hcu.mul_right ⟨1, 1, by ring⟩ }
  have hpr : (p.mulSnd r rfl).snd = q.snd * (1 - q.fst) := by
    simp only [MennickePair.mulSnd_snd, hsnd, hfst, r]
    ring
  have hr1 : s r = 1 := s.map_eq_one_of_snd_eq_unit_mul_one_sub u rfl
  have hmul : s (p.mulSnd r rfl) = s q :=
    s.map_mul_one_sub_fst (p := q) (by simp [hfst]) hpr
  rw [← hmul, s.map_mulSnd, hr1, mul_one]

/-- Sign invariance in the second entry: `[-b / a] = [b / a]`. -/
theorem map_neg_snd (s : MennickeSymbol A I C) {p q : MennickePair A I}
    (hfst : q.fst = p.fst) (hsnd : q.snd = -p.snd) : s q = s p :=
  s.map_unit_mul_snd (-1 : Aˣ) hfst (by simpa using hsnd)

/-- Any pair whose first entry is a unit has symbol value `1`: `[b / u] = 1`. -/
theorem map_eq_one_of_isUnit_fst (s : MennickeSymbol A I C) {p : MennickePair A I}
    (hu : IsUnit p.fst) : s p = 1 := by
  obtain ⟨u, hu'⟩ := hu
  have h1u : 1 - p.fst ∈ I := by
    have heq : 1 - p.fst = -(p.fst - 1) := by ring
    rw [heq]
    exact neg_mem p.sub_one_mem
  have ht : (1 - p.fst - p.snd) * (↑u⁻¹ : A) ∈ I :=
    I.mul_mem_right (↑u⁻¹ : A) (sub_mem h1u p.snd_mem)
  have hshift : p.shiftSnd ht = MennickePair.oneSubFst p.fst p.sub_one_mem := by
    ext
    · simp
    · simp only [MennickePair.shiftSnd_snd, MennickePair.oneSubFst_snd, ← hu']
      calc
        p.snd + (1 - (u : A) - p.snd) * (↑u⁻¹ : A) * (u : A)
          = p.snd + (1 - (u : A) - p.snd) * ((↑u⁻¹ : A) * (u : A)) := by ring
        _ = 1 - (u : A) := by simp
  rw [← s.map_shiftSnd p ht, hshift, s.map_oneSubFst]

/-- Any pair with second entry `0` has symbol value `1`: `[0 / u] = 1`. -/
theorem map_eq_one_of_snd_eq_zero (s : MennickeSymbol A I C) {p : MennickePair A I}
    (h : p.snd = 0) : s p = 1 := by
  have hu : IsUnit p.fst := by
    obtain ⟨x, _, hxy⟩ := p.isCoprime
    rw [h, mul_zero, add_zero] at hxy
    exact isUnit_iff_exists_inv.mpr ⟨x, by rw [mul_comm, hxy]⟩
  exact s.map_eq_one_of_isUnit_fst hu

/-- Any pair whose second entry is a unit has symbol value `1`. -/
theorem map_eq_one_of_isUnit_snd (s : MennickeSymbol A I C) {p : MennickePair A I}
    (hv : IsUnit p.snd) : s p = 1 := by
  obtain ⟨v, hv'⟩ := hv
  have hshift : (p.shiftFst ((1 - p.fst) * (↑v⁻¹ : A))).fst = 1 := by
    simp only [MennickePair.shiftFst_fst, ← hv']
    calc
      p.fst + (1 - p.fst) * (↑v⁻¹ : A) * (v : A)
        = p.fst + (1 - p.fst) * ((↑v⁻¹ : A) * (v : A)) := by ring
      _ = 1 := by simp
  rw [← s.map_shiftFst p ((1 - p.fst) * (↑v⁻¹ : A))]
  exact s.map_eq_one_of_fst_eq_one hshift

/-- **Near-unit reduction in the first entry**: if `a` is congruent modulo `b` to a unit of `A`,
then `s(a, b) = 1`. -/
theorem map_eq_one_of_fst_congr_unit (s : MennickeSymbol A I C) {p : MennickePair A I}
    {u : Aˣ} {t : A} (h : p.fst + t * p.snd = u) : s p = 1 := by
  rw [← s.map_shiftFst p t]
  exact s.map_eq_one_of_isUnit_fst (by rw [MennickePair.shiftFst_fst, h]; exact u.isUnit)

/-- **Near-unit reduction in the second entry**: if `b` is congruent modulo `a` to a unit `u` of
`A` (even when `u ∉ I`), then `s(a, b) = 1`. -/
theorem map_eq_one_of_snd_congr_unit (s : MennickeSymbol A I C) {p : MennickePair A I}
    {u : Aˣ} {r : A} (h : p.snd = u + r * p.fst) : s p = 1 := by
  have h1a : 1 - p.fst ∈ I := by
    have heq : 1 - p.fst = -(p.fst - 1) := by ring
    rw [heq]
    exact neg_mem p.sub_one_mem
  have hcu : IsCoprime p.fst (u : A) := ⟨0, (↑u⁻¹ : A), by simp⟩
  let q : MennickePair A I :=
    { fst := p.fst
      snd := (u : A) * (1 - p.fst)
      sub_one_mem := p.sub_one_mem
      snd_mem := I.mul_mem_left (u : A) h1a
      isCoprime := hcu.mul_right ⟨1, 1, by ring⟩ }
  have hmul : s (q.shiftSnd (I.mul_mem_left r h1a)) = s p :=
    s.map_mul_one_sub_fst (p := p) (by simp [q])
      (by simp only [MennickePair.shiftSnd_snd, q, h]; ring)
  rw [← hmul, s.map_shiftSnd]
  exact s.map_eq_one_of_snd_eq_unit_mul_one_sub u rfl

/-! ### Explicit two-sided inverses and unit factorization -/

/-- Product of `s(a, b)` with its Bézout inverse `s(a, y * (1 - a))` equals `1`. -/
theorem mul_bezoutInvPair_eq_one (s : MennickeSymbol A I C) (p : MennickePair A I)
    {x y : A} (hxy : x * p.fst + y * p.snd = 1) :
    s p * s (p.bezoutInvPair hxy) = 1 := by
  have h1a : 1 - p.fst ∈ I := by
    have heq : 1 - p.fst = -(p.fst - 1) := by ring
    rw [heq]
    exact neg_mem p.sub_one_mem
  have ht : -x * (1 - p.fst) ∈ I := I.mul_mem_left (-x) h1a
  have hfst : p.fst = (p.bezoutInvPair hxy).fst := (p.bezoutInvPair_fst hxy).symm
  have hprod : p.mulSnd (p.bezoutInvPair hxy) hfst =
      (MennickePair.oneSubFst p.fst p.sub_one_mem).shiftSnd ht := by
    ext
    · simp
    · simp only [MennickePair.mulSnd_snd, MennickePair.bezoutInvPair_snd,
        MennickePair.shiftSnd_snd, MennickePair.oneSubFst_snd, MennickePair.oneSubFst_fst]
      linear_combination (1 - p.fst) * hxy
  rw [← s.map_mulSnd p (p.bezoutInvPair hxy) hfst, hprod, s.map_shiftSnd, s.map_oneSubFst]

/-- Product of the Bézout inverse `s(a, y * (1 - a))` with `s(a, b)` equals `1`. -/
theorem bezoutInvPair_mul_eq_one (s : MennickeSymbol A I C) (p : MennickePair A I)
    {x y : A} (hxy : x * p.fst + y * p.snd = 1) :
    s (p.bezoutInvPair hxy) * s p = 1 := by
  rw [(s.commute_of_fst_eq (p := p.bezoutInvPair hxy) (q := p) (p.bezoutInvPair_fst hxy)).eq]
  exact s.mul_bezoutInvPair_eq_one p hxy

/-- Every value of a Mennicke symbol in an arbitrary monoid `C` is a unit. -/
theorem isUnit (s : MennickeSymbol A I C) (p : MennickePair A I) : IsUnit (s p) := by
  obtain ⟨x, y, hxy⟩ := p.isCoprime
  exact ⟨⟨s p, s (p.bezoutInvPair hxy),
    s.mul_bezoutInvPair_eq_one p hxy, s.bezoutInvPair_mul_eq_one p hxy⟩, rfl⟩

/-- In a group `G`, the inverse of `s(a, b)` is explicitly `s(a, y * (1 - a))`. -/
theorem map_inv_eq_bezoutInvPair {G : Type*} [Group G] (s : MennickeSymbol A I G)
    (p : MennickePair A I) {x y : A} (hxy : x * p.fst + y * p.snd = 1) :
    (s p)⁻¹ = s (p.bezoutInvPair hxy) :=
  inv_eq_of_mul_eq_one_right (s.mul_bezoutInvPair_eq_one p hxy)

/-- Every Mennicke symbol into a monoid `C` factors canonically through the unit group `Cˣ`. -/
noncomputable def toUnits (s : MennickeSymbol A I C) : MennickeSymbol A I Cˣ where
  toFun p := (s.isUnit p).unit
  map_oneZero' := Units.ext (by simp)
  map_shiftSnd' p _ _ := Units.ext (by simp)
  map_shiftFst' p _ := Units.ext (by simp)
  map_mulSnd' p q h := Units.ext (by simp [s.map_mulSnd p q h])

@[simp]
theorem coe_toUnits_apply (s : MennickeSymbol A I C) (p : MennickePair A I) :
    (s.toUnits p : C) = s p :=
  (s.isUnit p).unit_spec

end MennickeSymbol

end MennickeSymbol

end TauCeti
