/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import TauCeti.RingTheory.MennickeSymbol.Reciprocity
public import TauCeti.RingTheory.MennickeSymbol.Universal
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.DedekindDomain.Ideal.CoprimeShift

/-!
# Mennicke symbols over Dedekind domains

Let `A` be a Dedekind domain and `I : Ideal A`. Using the coprime linear shift lemmas of
`TauCeti.RingTheory.DedekindDomain.Ideal.CoprimeShift` and the Chinese remainder theorem, this file
establishes the core structural theorems of Bass–Milnor–Serre §2:

1. **Descent and surjectivity**: for any nonzero ideal `J ≤ I`, every pair in `MennickePair A I`
   is equivalent in `MennickeGroup A I` to the image of a pair in `MennickePair A J`; hence
   `MennickeGroup.mapIdeal hJI` is surjective.
2. **Mennicke–Newman common-denominator lemma**: for any ideal `I` (including `I = ⊥`) and any
   finite family `p : ι → MennickePair A I`, there exists a single denominator `a` with `a - 1 ∈ I`
   and equivalent pairs `q i` all sharing `fst = a`.
3. **Common `unitHom` image and abelianness**: for any nonzero `q ∈ I`, any finite family of
   symbol values (or elements of `MennickeGroup A I`) lies in the image of a single homomorphism
   `unitHom : (A ⧸ Ideal.span {a})ˣ →* C`. Consequently, the values of *every* Mennicke symbol into
   an arbitrary (possibly nonabelian) monoid `C` pairwise commute, and `MennickeGroup A I` is a
   `CommGroup` (extending its existing `Group` instance definitionally, with no instance diamond).
4. **Lam's denominator multiplication** (BMS Lemma 2.11):
   `[b / a₁ * a₂] = [b / a₁] * [b / a₂]` for any Mennicke symbol into an arbitrary monoid `C`,
   proved directly via Kervaire reciprocity without assuming commutativity of `C`.

## Main results

* `TauCeti.MennickeGroup.exists_of_eq_mapIdeal_of` and `mapIdeal_surjective`: descent for nonzero
  `J ≤ I`.
* `TauCeti.MennickeSymbol.exists_pair_of_le_ne_bot`: descent stated for an arbitrary symbol `s`.
* `TauCeti.MennickeGroup.exists_common_fst` and `TauCeti.MennickeSymbol.exists_common_fst`:
  Mennicke–Newman common-denominator lemma for finite families (including `I = ⊥`).
* `TauCeti.MennickeSymbol.exists_subset_mrange_unitHom` and
  `TauCeti.MennickeGroup.exists_subset_mrange_unitHom`: common `unitHom` image for finite families.
* `TauCeti.MennickeGroup.instCommGroup`: `CommGroup` instance on `MennickeGroup A I` over a
  Dedekind domain, definitionally compatible with `instGroup`.
* `TauCeti.MennickeSymbol.commute` and `commute_of_mem_mclosure`: abelianness of symbol values
  inside an arbitrary monoid `C`.
* `TauCeti.MennickeSymbol.map_mul_fst`: Lam's denominator multiplication lemma.

## References

* H. Bass, J. Milnor, and J.-P. Serre, *Solution of the congruence subgroup problem for `SL_n`
  (`n ≥ 3`) and `Sp_{2n}` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), §2, Lemmas 2.6–2.11, pp. 66–69.
-/

public section

namespace TauCeti

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {I J : Ideal A} {C : Type*} [Monoid C]

/-! ### Descent for nonzero ideals -/

namespace MennickeGroup

/-- **Descent lemma** (Bass–Milnor–Serre Lemma 2.8): over a Dedekind domain, if `0 ≠ J ≤ I`,
every admissible pair modulo `I` is equivalent in `MennickeGroup A I` to a pair modulo `J`. -/
theorem exists_of_eq_mapIdeal_of (hJ : J ≠ ⊥) (hJI : J ≤ I) (p : MennickePair A I) :
    ∃ q : MennickePair A J, of p = mapIdeal hJI (of q) := by
  obtain ⟨t, htI, _, hsup⟩ :=
    Ideal.exists_mem_span_add_mul_sup_eq I J hJ hJI p.snd_mem p.isCoprime
  let p₁ : MennickePair A I := p.shiftSnd htI
  have ha_mem : p₁.fst - 1 ∈ Ideal.span {p₁.snd} ⊔ J := by
    rw [MennickePair.shiftSnd_snd, hsup]
    exact p₁.sub_one_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp ha_mem
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hu
  let p₂ : MennickePair A I := p₁.shiftFst (-r)
  have hp₂_fst : p₂.fst - 1 ∈ J := by
    have heq : p₂.fst - 1 = v := by
      simp only [p₂, MennickePair.shiftFst_fst]
      linear_combination -huv
    rwa [heq]
  let p₃ : MennickePair A I := p₂.shiftSnd (neg_mem p₂.snd_mem)
  have hp₃_snd : p₃.snd ∈ J := by
    have heq : p₃.snd = -p₂.snd * (p₂.fst - 1) := by
      simp only [p₃, MennickePair.shiftSnd_snd]
      ring
    rw [heq]
    exact J.mul_mem_left (-p₂.snd) hp₂_fst
  let q : MennickePair A J :=
    { fst := p₃.fst
      snd := p₃.snd
      sub_one_mem := by simpa [p₃] using hp₂_fst
      snd_mem := hp₃_snd
      isCoprime := p₃.isCoprime }
  refine ⟨q, ?_⟩
  have hq_map : q.mapIdeal hJI = p₃ := by
    ext <;> simp [q]
  rw [mapIdeal_of, hq_map]
  calc
    of p = of p₁ := (of.map_shiftSnd p htI).symm
    _ = of p₂ := (of.map_shiftFst p₁ (-r)).symm
    _ = of p₃ := (of.map_shiftSnd p₂ (neg_mem p₂.snd_mem)).symm

/-- Over a Dedekind domain, for any nonzero ideal `J ≤ I`, the transition map
`mapIdeal hJI : MennickeGroup A J →* MennickeGroup A I` is surjective. -/
theorem mapIdeal_surjective (hJ : J ≠ ⊥) (hJI : J ≤ I) :
    Function.Surjective (mapIdeal hJI) := by
  intro x
  refine induction_on x ⟨1, map_one _⟩ ?_ ?_
  · intro p
    obtain ⟨q, hq⟩ := exists_of_eq_mapIdeal_of hJ hJI p
    exact ⟨of q, hq.symm⟩
  · rintro _ _ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by rw [map_mul, ha, hb]⟩

/-! ### Mennicke–Newman common-denominator lemma -/

/-- Inductive construction of shifts `t i ∈ I` and pairwise coprime cofactor ideals `K i`
(also coprime to `I`) factoring `Ideal.span {(p i).snd + t i * (p i).fst} = I * K i`. -/
private theorem exists_coprime_factor_family (hI : I ≠ ⊥) :
    ∀ (n : ℕ) (p : Fin n → MennickePair A I),
      ∃ (t : Fin n → A) (K : Fin n → Ideal A),
        (∀ i, t i ∈ I) ∧
        (∀ i, (p i).snd + t i * (p i).fst ≠ 0) ∧
        (∀ i, Ideal.span {(p i).snd + t i * (p i).fst} = I * K i) ∧
        (∀ i, IsCoprime (K i) I) ∧
        Pairwise (Function.onFun IsCoprime K)
  | 0, _ =>
    ⟨Fin.elim0, Fin.elim0, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i,
      fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | n + 1, p => by
    obtain ⟨t, K, htI, hb0, hspan, hKI, hpair⟩ :=
      exists_coprime_factor_family hI n (fun i ↦ p i.castSucc)
    have hK_ne : ∀ i : Fin n, K i ≠ 0 := by
      intro i h0
      have hsp := hspan i
      rw [h0, mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at hsp
      exact hb0 i hsp
    have hprod_ne : (∏ i : Fin n, K i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ ↦ hK_ne i
    have hJ_ne : I * (∏ i : Fin n, K i) ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact mul_ne_zero (by rwa [Ideal.zero_eq_bot]) hprod_ne
    obtain ⟨tLast, htLast, KLast, hbLast0, hspanLast, hcopLast⟩ :=
      Ideal.exists_mem_span_add_mul_eq_mul_and_isCoprime I (I * ∏ i : Fin n, K i) hI hJ_ne
        (p (Fin.last n)).snd_mem (p (Fin.last n)).isCoprime
    have hKLast_I : IsCoprime KLast I := hcopLast.of_mul_right_left
    have hKLast_K : ∀ i : Fin n, IsCoprime KLast (K i) := fun i ↦
      hcopLast.of_mul_right_right.of_prod_right i (Finset.mem_univ i)
    refine ⟨Fin.snoc t tLast, Fin.snoc K KLast, ?_, ?_, ?_, ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun i ↦ ?_)
      · simpa using htLast
      · simpa using htI i
    · refine Fin.lastCases ?_ (fun i ↦ ?_)
      · simpa using hbLast0
      · simpa using hb0 i
    · refine Fin.lastCases ?_ (fun i ↦ ?_)
      · simpa using hspanLast
      · simpa using hspan i
    · refine Fin.lastCases ?_ (fun i ↦ ?_)
      · simpa using hKLast_I
      · simpa using hKI i
    · intro i j hij
      refine Fin.lastCases (fun j hij ↦ ?_) (fun i j hij ↦ ?_) i j hij
      · refine Fin.lastCases (fun h ↦ (h rfl).elim) (fun j _ ↦ ?_) j hij
        simpa [Function.onFun] using hKLast_K j
      · refine Fin.lastCases (fun _ ↦ ?_) (fun j hij ↦ ?_) j hij
        · simpa [Function.onFun] using (hKLast_K i).symm
        · have hij' : i ≠ j := fun h ↦ hij (congrArg Fin.castSucc h)
          simpa [Function.onFun] using hpair hij'

/-- **Mennicke–Newman common-denominator lemma** (indexed by `Fin n`), valid for every ideal
`I : Ideal A` including `I = ⊥`. -/
theorem exists_common_fst_fin {n : ℕ} (p : Fin n → MennickePair A I) :
    ∃ (a : A), a - 1 ∈ I ∧ ∃ (q : Fin n → MennickePair A I),
      ∀ i, (q i).fst = a ∧ of (p i) = of (q i) := by
  by_cases hI : I = ⊥
  · subst hI
    refine ⟨1, by simp, fun _ ↦ .oneZero, fun i ↦ ?_⟩
    rw [MennickePair.eq_oneZero_of_bot (p i)]
    exact ⟨by simp, rfl⟩
  · obtain ⟨t, K, htI, _, hspan, hKI, hpair⟩ := exists_coprime_factor_family hI n p
    let L : Option (Fin n) → Ideal A := Option.elim' I K
    have hLpair : Pairwise (Function.onFun IsCoprime L) := by
      intro x y hxy
      cases x with
      | none =>
        cases y with
        | none => exact (hxy rfl).elim
        | some j => exact (hKI j).symm
      | some i =>
        cases y with
        | none => exact hKI i
        | some j =>
          exact hpair fun h ↦ hxy (congrArg some h)
    let target : (x : Option (Fin n)) → A ⧸ L x
      | none => Ideal.Quotient.mk I 1
      | some i => Ideal.Quotient.mk (K i) (p i).fst
    obtain ⟨qa, hqa⟩ := Ideal.quotientInfToPiQuotient_surj hLpair target
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective qa
    have haI : a - 1 ∈ I := by
      have h0 := congr_fun hqa none
      rw [Ideal.quotientInfToPiQuotient_mk'] at h0
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem a 1).mp h0
    have haK : ∀ i : Fin n, a - (p i).fst ∈ K i := by
      intro i
      have hi := congr_fun hqa (some i)
      rw [Ideal.quotientInfToPiQuotient_mk'] at hi
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem a (p i).fst).mp hi
    have hr_ex : ∀ i : Fin n, ∃ r : A, a = (p i).fst + r * ((p i).snd + t i * (p i).fst) := by
      intro i
      have hmemI : a - (p i).fst ∈ I := by
        have heq : a - (p i).fst = (a - 1) - ((p i).fst - 1) := by ring
        rw [heq]
        exact sub_mem haI (p i).sub_one_mem
      have hmemInf : a - (p i).fst ∈ I ⊓ K i := ⟨hmemI, haK i⟩
      rw [← Ideal.mul_eq_inf_of_isCoprime (hKI i).symm, ← hspan i] at hmemInf
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hmemInf
      exact ⟨r, by linear_combination hr⟩
    choose r hr using hr_ex
    let q : Fin n → MennickePair A I := fun i ↦ ((p i).shiftSnd (htI i)).shiftFst (r i)
    refine ⟨a, haI, q, fun i ↦ ⟨?_, ?_⟩⟩
    · simp only [q, MennickePair.shiftFst_fst, MennickePair.shiftSnd_fst, MennickePair.shiftSnd_snd]
      exact (hr i).symm
    · simp [q]

/-- **Mennicke–Newman common-denominator lemma** (for any finite index type `ι` and any ideal
`I : Ideal A`, including `I = ⊥`). -/
theorem exists_common_fst {ι : Type*} [Finite ι] (p : ι → MennickePair A I) :
    ∃ (a : A), a - 1 ∈ I ∧ ∃ (q : ι → MennickePair A I),
      ∀ i, (q i).fst = a ∧ of (p i) = of (q i) := by
  cases nonempty_fintype ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  obtain ⟨a, ha, q, hq⟩ := exists_common_fst_fin (fun j ↦ p (e.symm j))
  refine ⟨a, ha, fun i ↦ q (e i), fun i ↦ ?_⟩
  simpa using hq (e i)

/-! ### Common `unitHom` image and commutativity -/

/-- Any two generators `of p` and `of q` of `MennickeGroup A I` commute over a Dedekind domain. -/
theorem commute_of (p q : MennickePair A I) : Commute (of p) (of q) := by
  let fam : Bool → MennickePair A I := fun b ↦ cond b p q
  obtain ⟨a, _, r, hr⟩ := exists_common_fst fam
  have hp : of p = of (r true) := (hr true).2
  have hq : of q = of (r false) := (hr false).2
  have hfst : (r true).fst = (r false).fst := ((hr true).1).trans ((hr false).1).symm
  rw [hp, hq]
  exact of.commute_of_fst_eq hfst

/-- Over a Dedekind domain, `MennickeGroup A I` is abelian. -/
theorem mul_comm (x y : MennickeGroup A I) : x * y = y * x := by
  have hc : Commute x y := by
    refine induction_on x (Commute.one_left y) (fun p ↦ ?_) (fun _ _ ha hb ↦ ha.mul_left hb)
    refine induction_on y (Commute.one_right (of p)) (fun q ↦ commute_of p q)
      (fun _ _ ha hb ↦ ha.mul_right hb)
  exact hc.eq

/-- Over a Dedekind domain, `MennickeGroup A I` carries a canonical `CommGroup` instance whose
underlying `Group` is definitionally identical to `instGroup`. -/
instance instCommGroup : CommGroup (MennickeGroup A I) :=
  { instGroup with mul_comm := mul_comm }

private example :
    (inferInstance : CommGroup (MennickeGroup A I)).toGroup =
      (inferInstance : Group (MennickeGroup A I)) :=
  rfl

end MennickeGroup

namespace MennickeSymbol

/-- Descent for an arbitrary Mennicke symbol `s` into a monoid `C`: when `0 ≠ J ≤ I`, every pair
modulo `I` has the same symbol value as some pair modulo `J`. -/
theorem exists_pair_of_le_ne_bot (s : MennickeSymbol A I C) (hJ : J ≠ ⊥) (hJI : J ≤ I)
    (p : MennickePair A I) :
    ∃ q : MennickePair A J, s p = s (q.mapIdeal hJI) := by
  obtain ⟨q, hq⟩ := MennickeGroup.exists_of_eq_mapIdeal_of hJ hJI p
  refine ⟨q, ?_⟩
  have h := congrArg (MennickeGroup.lift s) hq
  simpa using h

/-- **Mennicke–Newman common-denominator lemma** for an arbitrary Mennicke symbol `s` into a
monoid `C` (valid for all ideals `I`, including `I = ⊥`). -/
theorem exists_common_fst (s : MennickeSymbol A I C) {ι : Type*} [Finite ι]
    (p : ι → MennickePair A I) :
    ∃ (a : A), a - 1 ∈ I ∧ ∃ (q : ι → MennickePair A I),
      ∀ i, (q i).fst = a ∧ s (p i) = s (q i) := by
  obtain ⟨a, ha, q, hq⟩ := MennickeGroup.exists_common_fst p
  refine ⟨a, ha, q, fun i ↦ ⟨(hq i).1, ?_⟩⟩
  have h := congrArg (MennickeGroup.lift s) (hq i).2
  simpa using h

/-- For any nonzero `q ∈ I` and any finite family of admissible pairs `p : ι → MennickePair A I`,
all values `s (p i)` lie simultaneously in the range of a single quotient-unit homomorphism
`s.unitHom hq ha : (A ⧸ Ideal.span {a})ˣ →* C` (Bass–Milnor–Serre Lemma 2.9). -/
theorem exists_subset_mrange_unitHom (s : MennickeSymbol A I C) {ι : Type*} [Finite ι]
    {q : A} (hq : q ∈ I) (hq0 : q ≠ 0) (p : ι → MennickePair A I) :
    ∃ (a : A) (ha : a - 1 ∈ Ideal.span {q}),
      ∀ i, s (p i) ∈ MonoidHom.mrange (s.unitHom hq ha) := by
  have hJ : Ideal.span {q} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hq0
  have hJI : Ideal.span {q} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hq
  choose r hr using fun i ↦ s.exists_pair_of_le_ne_bot hJ hJI (p i)
  obtain ⟨a, ha, r', hr'⟩ := (s.comapIdeal hJI).exists_common_fst r
  refine ⟨a, ha, fun i ↦ ?_⟩
  let p' : MennickePair A I :=
    { fst := a
      snd := (r' i).snd
      sub_one_mem := hJI ha
      snd_mem := hJI (r' i).snd_mem
      isCoprime := (hr' i).1 ▸ (r' i).isCoprime }
  have hp'_eq : (r' i).mapIdeal hJI = p' := by
    ext
    · simpa [p'] using (hr' i).1
    · simp [p']
  have hs_eq : s (p i) = s p' := by
    rw [hr i]
    simpa [hp'_eq] using (hr' i).2
  rw [hs_eq]
  exact s.mem_mrange_unitHom hq (p := p') ha (r' i).snd_mem

/-- Over a Dedekind domain, any two values of a Mennicke symbol into an arbitrary (possibly
nonabelian) monoid `C` commute. -/
theorem commute (s : MennickeSymbol A I C) (p q : MennickePair A I) :
    Commute (s p) (s q) := by
  have hc := MennickeGroup.commute_of p q
  simpa using hc.map (MennickeGroup.lift s)

/-- Any two elements of the submonoid generated by the image of a Mennicke symbol `s` commute in
an arbitrary (possibly nonabelian) monoid `C`. -/
theorem commute_of_mem_mclosure (s : MennickeSymbol A I C) {x y : C}
    (hx : x ∈ Submonoid.closure (Set.range (s : MennickePair A I → C)))
    (hy : y ∈ Submonoid.closure (Set.range (s : MennickePair A I → C))) :
    Commute x y := by
  refine Submonoid.closure_induction ?_ (Commute.one_left y)
    (fun _ _ _ _ ha hb ↦ ha.mul_left hb) hx
  rintro _ ⟨p, rfl⟩
  refine Submonoid.closure_induction ?_ (Commute.one_right (s p))
    (fun _ _ _ _ ha hb ↦ ha.mul_right hb) hy
  rintro _ ⟨q, rfl⟩
  exact s.commute p q

/-! ### Lam's denominator multiplication (BMS Lemma 2.11) -/

omit [IsDedekindDomain A] in
/-- Helper: shift a pair's first entry modulo `b` so that it becomes `≡ 1 (mod q)`, given
`Ideal.span {q} ⊔ Ideal.span {b} = I`. -/
private theorem exists_shift_sub_one_mem_span {q b : A} (hsup : Ideal.span {q} ⊔ Ideal.span {b} = I)
    (p : MennickePair A I) (hp : p.snd = b) :
    ∃ r : A, (p.shiftFst (-r)).fst - 1 ∈ Ideal.span {q} := by
  have hmem : p.fst - 1 ∈ Ideal.span {q} ⊔ Ideal.span {b} := hsup ▸ p.sub_one_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hv
  refine ⟨r, ?_⟩
  have heq : (p.shiftFst (-r)).fst - 1 = u := by
    simp only [MennickePair.shiftFst_fst, hp]
    linear_combination -huv
  rwa [heq]

/-- **Lam's denominator multiplication lemma** (Bass–Milnor–Serre Lemma 2.11): over a Dedekind
domain, `[b / a₁ * a₂] = [b / a₁] * [b / a₂]` for any Mennicke symbol into an arbitrary monoid `C`
(proved directly via Kervaire reciprocity, without assuming commutativity of `C`). -/
theorem map_mul_fst (s : MennickeSymbol A I C) {p₁ p₂ p₁₂ : MennickePair A I}
    (hsnd₁ : p₂.snd = p₁.snd) (hsnd₂ : p₁₂.snd = p₁.snd)
    (hfst : p₁₂.fst = p₁.fst * p₂.fst) :
    s p₁₂ = s p₁ * s p₂ := by
  by_cases hb0 : p₁.snd = 0
  · rw [s.map_eq_one_of_snd_eq_zero hb0,
      s.map_eq_one_of_snd_eq_zero (hsnd₁.trans hb0),
      s.map_eq_one_of_snd_eq_zero (hsnd₂.trans hb0), mul_one]
  · set b := p₁.snd
    have hb0_ideal : Ideal.span {b} ≠ 0 := by
      simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hb0
    have hbI : Ideal.span {b} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr p₁.snd_mem
    obtain ⟨q, hsup'⟩ := IsDedekindDomain.exists_sup_span_eq hbI hb0_ideal
    have hsup : Ideal.span {q} ⊔ Ideal.span {b} = I := by rwa [sup_comm] at hsup'
    have hqI : q ∈ I := hsup ▸ Submodule.mem_sup_left (Ideal.mem_span_singleton_self q)
    obtain ⟨r₁, hr₁⟩ := exists_shift_sub_one_mem_span hsup p₁ rfl
    obtain ⟨r₂, hr₂⟩ := exists_shift_sub_one_mem_span hsup p₂ hsnd₁
    let p₁' := p₁.shiftFst (-r₁)
    let p₂' := p₂.shiftFst (-r₂)
    let t₁₂ := -r₁ * p₂.fst - r₂ * p₁.fst + r₁ * r₂ * b
    let p₁₂' := p₁₂.shiftFst t₁₂
    have hsnd₁' : p₂'.snd = p₁'.snd := by simp [p₁', p₂', hsnd₁, b]
    have hsnd₂' : p₁₂'.snd = p₁'.snd := by simp [p₁', p₁₂', hsnd₂, b]
    have hfst' : p₁₂'.fst = p₁'.fst * p₂'.fst := by
      simp only [p₁', p₂', p₁₂', MennickePair.shiftFst_fst, hfst, hsnd₁, hsnd₂, t₁₂, b]
      ring
    calc
      s p₁₂ = s p₁₂' := (s.map_shiftFst p₁₂ t₁₂).symm
      _ = s p₁' * s p₂' :=
        s.map_mul_fst_of_sub_one_mem_span hqI hsnd₁' hsnd₂' hfst' hr₁ hr₂
      _ = s p₁ * s p₂ := by rw [s.map_shiftFst, s.map_shiftFst]

end MennickeSymbol

namespace MennickeGroup

/-- For any nonzero `q ∈ I`, any finite family of elements `x : ι → MennickeGroup A I` lies
simultaneously in the range of a single quotient-unit homomorphism
`of.unitHom hq ha : (A ⧸ Ideal.span {a})ˣ →* MennickeGroup A I`. -/
theorem exists_subset_mrange_unitHom {ι : Type*} [Finite ι] {q : A} (hq : q ∈ I) (hq0 : q ≠ 0)
    (x : ι → MennickeGroup A I) :
    ∃ (a : A) (ha : a - 1 ∈ Ideal.span {q}),
      ∀ i, x i ∈ MonoidHom.mrange (of.unitHom hq ha) := by
  choose l hl using fun i ↦ exists_list_prod_of (x i)
  let fam : (i : ι) × Fin (l i).length → MennickePair A I := fun ⟨i, j⟩ ↦ (l i)[j]
  obtain ⟨a, ha, hmem⟩ := of.exists_subset_mrange_unitHom hq hq0 fam
  refine ⟨a, ha, fun i ↦ ?_⟩
  rw [hl i]
  refine Submonoid.list_prod_mem _ ?_
  intro y hy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp
  exact hmem ⟨i, ⟨j, hj⟩⟩

end MennickeGroup

end TauCeti
