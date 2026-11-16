/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Compare
public import TauCeti.RingTheory.WittVector.Units

/-!
# Finite-length Witt operators and their identities

For a prime `p` and a commutative ring `R`, Mathlib defines the ring `TruncatedWittVector p n R` of
`p`-typical Witt vectors of length `n` together with the quotient maps `WittVector.truncate n` and
the restriction homomorphisms `TruncatedWittVector.truncate`. This file constructs the remaining
operators on `TruncatedWittVector` by descending the infinite-length operators along truncation and
establishes their algebraic identities, restriction kernels, and ghost-component injectivity,
supplying the finite-level operator calculus for de Rham–Witt towers, crystalline cohomology, and
truncated period maps `W_n(R) → A / p^n`.

Because the `k`-th Frobenius polynomial `WittVector.frobeniusPoly p k` involves only the variables
`X 0, …, X (k + 1)` (`WittVector.frobeniusPoly_vars_subset`), the infinite Witt Frobenius descends
to a ring homomorphism
`TruncatedWittVector.frobenius : TruncatedWittVector p (n + 1) R →+* TruncatedWittVector p n R`
commuting with truncation (`TruncatedWittVector.frobenius_wittVector_truncate`) and with restriction
(`TruncatedWittVector.truncate_frobenius`). At length two its zeroth coordinate is `x₀ ^ p + p * x₁`
without any characteristic-`p` assumption (`TruncatedWittVector.coeff_frobenius_zero`), while in
characteristic `p` it acts coordinatewise by `p`-th powers
(`TruncatedWittVector.coeff_frobenius_charP`).

Likewise, `WittVector.verschiebung` descends to an injective additive homomorphism
`TruncatedWittVector.verschiebung : TruncatedWittVector p n R →+ TruncatedWittVector p (n + 1) R`
acting by coordinate shift. The infinite `F`–`V` relations descend to the finite identities
`frobenius (verschiebung x) = x * p` and `verschiebung (x * frobenius y) = verschiebung x * y` over
every commutative ring, together with `verschiebung (frobenius x) = x * p` on
`TruncatedWittVector p (n + 1) R` in characteristic `p`. More generally, the `r`-fold shift
`TruncatedWittVector.iterateVerschiebung r` identifies `TruncatedWittVector p m R` with the kernel
of restriction `TruncatedWittVector p (r + m) R →+* TruncatedWittVector p r R`; at `m = 1`, combined
with `TruncatedWittVector.constantCoeffEquiv : TruncatedWittVector p 1 R ≃+* R`, this identifies the
kernel of `W_{r + 1}(R) →+* W_r(R)` with the image of the `r`-fold Verschiebung from `R`.

Finally, the first `n` ghost components descend to `TruncatedWittVector.ghostComponent` and package
into `TruncatedWittVector.ghostMap : TruncatedWittVector p n R →+* (Fin n → R)`. When multiplication
by `p` is injective on `R`, the first `n` ghost components are jointly injective on
`TruncatedWittVector p n R` (`TruncatedWittVector.ghostComponent_out_injective`,
`TruncatedWittVector.ghostMap_injective`), even when `p` is not invertible in `R`.

## Main definitions

* `TruncatedWittVector.constantCoeff`: the zeroth Witt coordinate as a ring homomorphism on
  `TruncatedWittVector p (n + 1) R`.
* `TruncatedWittVector.constantCoeffEquiv`: the canonical ring isomorphism
  `TruncatedWittVector p 1 R ≃+* R`.
* `TruncatedWittVector.map`: functoriality of `TruncatedWittVector p n` along a ring homomorphism.
* `TruncatedWittVector.teichmuller`: the Teichmüller multiplicative lift
  `R →* TruncatedWittVector p n R`.
* `TruncatedWittVector.frobenius`: the finite Witt Frobenius
  `TruncatedWittVector p (n + 1) R →+* TruncatedWittVector p n R`.
* `TruncatedWittVector.verschiebung`: the finite Witt Verschiebung
  `TruncatedWittVector p n R →+ TruncatedWittVector p (n + 1) R`.
* `TruncatedWittVector.iterateVerschiebung`: the `r`-fold Verschiebung
  `TruncatedWittVector p m R →+ TruncatedWittVector p (r + m) R`.
* `TruncatedWittVector.ghostComponent`, `TruncatedWittVector.ghostMap`: the ghost components and
  bundled ghost map on `TruncatedWittVector p n R`.

## Main results

* `TruncatedWittVector.truncate_frobenius`, `TruncatedWittVector.coeff_frobenius_zero`,
  `TruncatedWittVector.coeff_frobenius_charP`: compatibility of finite Frobenius with restriction
  and its coordinate formulas.
* `TruncatedWittVector.verschiebung_injective`, `TruncatedWittVector.frobenius_verschiebung`,
  `TruncatedWittVector.verschiebung_mul_frobenius`, `TruncatedWittVector.verschiebung_frobenius`:
  injectivity of finite Verschiebung and the finite `F`–`V` and projection identities.
* `TruncatedWittVector.ker_truncate_toAddMonoidHom_eq_range_iterateVerschiebung`,
  `TruncatedWittVector.ker_truncate_succ_eq_range`: the kernel of restriction is the image of
  iterated Verschiebung.
* `TruncatedWittVector.ghostComponent_out_injective`, `TruncatedWittVector.ghostMap_injective`:
  joint injectivity of the first `n` ghost components when multiplication by `p` on `R` is
  injective.

## References

* B. Bhatt, J. Lurie, and A. Mathew, *Revisiting the de Rham–Witt complex*, Astérisque 424 (2021),
  §3.6, Proposition 3.6.2.
* B. Bhatt, M. Morrow, and P. Scholze, *Integral `p`-adic Hodge theory*, Publ. Math. Inst. Hautes
  Études Sci. 128 (2018), Lemma 3.2.
* C. Davis and K. S. Kedlaya, *On the Witt vector Frobenius*, Proc. Amer. Math. Soc. 142 (2014),
  2211–2226, §1.
* A. Langer and T. Zink, *De Rham–Witt cohomology for a proper and smooth morphism*, J. Inst. Math.
  Jussieu 3 (2004), §1.2.
-/

public section

noncomputable section

namespace WittVector

open MvPolynomial

variable {p : ℕ} [hp : Fact p.Prime] {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

local notation "𝕎" => WittVector p

variable (p) in
/-- The `n`-th rational Frobenius polynomial uses only the variables `X 0, …, X (n + 1)`. -/
theorem frobeniusPolyRat_vars_subset (n : ℕ) :
    (frobeniusPolyRat p n).vars ⊆ Finset.range (n + 2) := by
  classical
  intro j hj
  rw [frobeniusPolyRat] at hj
  obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp (vars_bind₁ _ _ hj)
  have hi' : i < n + 1 := Finset.mem_range.mp (xInTermsOfW_vars_subset p n hi)
  have hj' : j < i + 2 := Finset.mem_range.mp (wittPolynomial_vars_subset p ℚ (i + 1) hj)
  exact Finset.mem_range.mpr (by omega)

variable (p) in
/-- The `n`-th integral Frobenius polynomial uses only the variables `X 0, …, X (n + 1)`. -/
theorem frobeniusPoly_vars_subset (n : ℕ) :
    (frobeniusPoly p n).vars ⊆ Finset.range (n + 2) := by
  rw [← vars_map_of_injective (p := frobeniusPoly p n) (f := Int.castRingHom ℚ) Int.cast_injective,
    map_frobeniusPoly]
  exact frobeniusPolyRat_vars_subset p n

/-- The `n`-th Witt coordinate of `frobenius x` depends only on the first `n + 2` Witt coordinates
of `x`. -/
theorem coeff_frobenius_congr {x y : 𝕎 R} {n : ℕ} (h : ∀ k < n + 2, x.coeff k = y.coeff k) :
    (frobenius x).coeff n = (frobenius y).coeff n := by
  rw [coeff_frobenius, coeff_frobenius, aeval_eq_eval₂Hom, aeval_eq_eval₂Hom]
  exact eval₂Hom_congr' rfl
    (fun k hk _ ↦ h k (Finset.mem_range.mp (frobeniusPoly_vars_subset p n hk))) rfl

/-- The `n`-th ghost component `ghostComponent n x` depends only on the first `n + 1` Witt
coordinates of `x`. -/
theorem ghostComponent_congr {x y : 𝕎 R} {n : ℕ} (h : ∀ k < n + 1, x.coeff k = y.coeff k) :
    ghostComponent n x = ghostComponent n y := by
  rw [ghostComponent_apply, ghostComponent_apply, aeval_eq_eval₂Hom, aeval_eq_eval₂Hom]
  exact eval₂Hom_congr' rfl
    (fun k hk _ ↦ h k (Finset.mem_range.mp (wittPolynomial_vars_subset p ℤ n hk))) rfl

/-- Witt Frobenius is natural with respect to ring homomorphisms. -/
@[simp]
theorem map_frobenius (f : R →+* S) (x : 𝕎 R) : map f (frobenius x) = frobenius (map f x) := by
  ext n
  rw [map_coeff, coeff_frobenius, coeff_frobenius, map_aeval]
  exact eval₂Hom_congr (RingHom.ext_int _ _) rfl rfl

/-- Bundled ring-homomorphism form of `WittVector.map_frobenius`. -/
theorem map_comp_frobenius (f : R →+* S) :
    (map (p := p) f).comp frobenius = frobenius.comp (map f) := by
  ext1 x
  exact map_frobenius f x

/-- Over any commutative ring `R`, the Witt Frobenius sends a Teichmüller representative `[r]` to
`[r ^ p]`. -/
theorem frobenius_teichmuller_eq (r : R) :
    frobenius (teichmuller p r) = teichmuller p (r ^ p) := by
  have hQ : ∀ x : MvPolynomial R ℚ,
      frobenius (teichmuller p x) = teichmuller p (x ^ p) := fun x ↦ by
    apply (ghostMap.bijective_of_invertible p (MvPolynomial R ℚ)).injective
    ext k
    simp [ghostComponent_frobenius, pow_succ, pow_mul]
  have hZ : ∀ x : MvPolynomial R ℤ,
      frobenius (teichmuller p x) = teichmuller p (x ^ p) := fun x ↦ by
    refine map_injective (MvPolynomial.map (Int.castRingHom ℚ))
      (MvPolynomial.map_injective _ Int.cast_injective) ?_
    rw [map_frobenius, map_teichmuller, map_teichmuller, map_pow, hQ]
  obtain ⟨x, rfl⟩ := counit_surjective R r
  have hx := congrArg (WittVector.map (p := p) (counit R)) (hZ x)
  simpa only [map_frobenius, map_teichmuller, map_pow] using hx

/-- Over any commutative ring `R`, `frobenius (teichmuller p r) = teichmuller p r ^ p`. -/
theorem frobenius_teichmuller_eq_pow (r : R) :
    frobenius (teichmuller p r) = teichmuller p r ^ p := by
  rw [frobenius_teichmuller_eq, map_pow]

/-- If multiplication by `p` on `R` is injective and two Witt vectors have the same first `n` ghost
components, then their first `n` Witt coordinates coincide. -/
theorem eq_of_ghostComponent_eq {x y : 𝕎 R}
    (hp_inj : Function.Injective (fun a : R ↦ (p : R) * a)) {n : ℕ}
    (h : ∀ i < n, ghostComponent i x = ghostComponent i y) :
    ∀ i < n, x.coeff i = y.coeff i := by
  have hp_pow_inj : ∀ k : ℕ, Function.Injective (fun a : R ↦ (p : R) ^ k * a) := by
    intro k
    induction k with
    | zero =>
      intro a b hab
      simpa using hab
    | succ k ih =>
      intro a b hab
      apply ih
      apply hp_inj
      simpa [pow_succ', mul_assoc] using hab
  intro i
  refine Nat.strong_induction_on i fun i ih hi ↦ ?_
  have hghost := h i hi
  rw [ghostComponent_apply, ghostComponent_apply, aeval_wittPolynomial, aeval_wittPolynomial,
    Finset.sum_range_succ, Finset.sum_range_succ] at hghost
  have hinit :
      ∑ j ∈ Finset.range i, (p : R) ^ j * x.coeff j ^ p ^ (i - j) =
        ∑ j ∈ Finset.range i, (p : R) ^ j * y.coeff j ^ p ^ (i - j) :=
    Finset.sum_congr rfl fun j hj ↦ by
      have hjlt : j < i := Finset.mem_range.mp hj
      rw [ih j hjlt (hjlt.trans hi)]
  rw [hinit] at hghost
  have hlast := add_left_cancel hghost
  rw [Nat.sub_self, pow_zero, pow_one, pow_one] at hlast
  exact hp_pow_inj i hlast

/-- If multiplication by `p` on `R` is injective, then `WittVector.ghostMap` is injective. -/
theorem ghostMap_injective_of_p_mul_injective
    (hp_inj : Function.Injective (fun a : R ↦ (p : R) * a)) :
    Function.Injective (ghostMap : 𝕎 R → ℕ → R) := by
  intro x y h
  ext i
  exact eq_of_ghostComponent_eq hp_inj (n := i + 1)
    (fun j _ ↦ congrFun h j) i (Nat.lt_succ_self i)

end WittVector

namespace TruncatedWittVector

open WittVector

section ZeroLength

/-- Length-zero truncated Witt vectors form a subsingleton. -/
instance instSubsingletonZero {p : ℕ} {R : Type*} : Subsingleton (TruncatedWittVector p 0 R) :=
  ⟨fun _ _ ↦ ext fun i ↦ Fin.elim0 i⟩

end ZeroLength

variable {p n : ℕ} [hp : Fact p.Prime] {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

local notation "𝕎" => WittVector p

/-! ### Truncation, coordinates, functoriality, and Teichmüller lifts -/

/-- `WittVector.truncate n` is a left inverse to `TruncatedWittVector.out`. -/
@[simp]
theorem wittVector_truncate_out (x : TruncatedWittVector p n R) :
    WittVector.truncate n x.out = x :=
  truncateFun_out x

omit hp in
/-- All coordinates of `x.out` at indices `≥ n` vanish. -/
theorem coeff_out_of_le {k : ℕ} (hk : n ≤ k) (x : TruncatedWittVector p n R) :
    x.out.coeff k = 0 := by
  have hlt : ¬ k < n := not_lt.mpr hk
  simp [out, hlt]

/-- The `0`-th coordinate of `1` in `TruncatedWittVector p (n + 1) R` is `1`. -/
@[simp]
theorem coeff_one_zero : (1 : TruncatedWittVector p (n + 1) R).coeff 0 = 1 := by
  rw [← map_one (WittVector.truncate (p := p) (R := R) (n + 1)), WittVector.coeff_truncate]
  exact WittVector.one_coeff_zero p R

/-- Positive coordinates of `1` in `TruncatedWittVector p (n + 1) R` vanish. -/
@[simp]
theorem coeff_one_succ (i : Fin n) : (1 : TruncatedWittVector p (n + 1) R).coeff i.succ = 0 := by
  rw [← map_one (WittVector.truncate (p := p) (R := R) (n + 1)), WittVector.coeff_truncate]
  exact WittVector.one_coeff_eq_of_pos p R i.succ i.succ_pos

/-- The `0`-th coordinate of a natural-number cast in `TruncatedWittVector p (n + 1) R` is the cast
in `R`. -/
@[simp]
theorem coeff_natCast_zero (k : ℕ) : (k : TruncatedWittVector p (n + 1) R).coeff 0 = k := by
  rw [← map_natCast (WittVector.truncate (p := p) (R := R) (n + 1)) k, WittVector.coeff_truncate]
  exact map_natCast (WittVector.constantCoeff (p := p) (R := R)) k

/-- The `0`-th coordinate of an integer cast in `TruncatedWittVector p (n + 1) R` is the cast in
`R`. -/
@[simp]
theorem coeff_intCast_zero (z : ℤ) : (z : TruncatedWittVector p (n + 1) R).coeff 0 = z := by
  rw [← map_intCast (WittVector.truncate (p := p) (R := R) (n + 1)) z, WittVector.coeff_truncate]
  exact map_intCast (WittVector.constantCoeff (p := p) (R := R)) z

/-- The zeroth Witt coordinate on `TruncatedWittVector p (n + 1) R` as a ring homomorphism. -/
def constantCoeff : TruncatedWittVector p (n + 1) R →+* R :=
  RingHom.liftOfRightInverse (WittVector.truncate (n + 1)) out truncateFun_out
    ⟨WittVector.constantCoeff, fun x hx ↦ by
      rw [WittVector.mem_ker_truncate] at hx
      exact hx 0 (Nat.succ_pos n)⟩

/-- `TruncatedWittVector.constantCoeff` composed with `WittVector.truncate` recovers
`WittVector.constantCoeff`. -/
@[simp]
theorem constantCoeff_comp_wittVector_truncate :
    (constantCoeff (p := p) (n := n) (R := R)).comp (WittVector.truncate (n + 1)) =
      WittVector.constantCoeff :=
  RingHom.liftOfRightInverse_comp _ _ _ _

/-- `TruncatedWittVector.constantCoeff` on a truncated Witt vector evaluates the `0`-th coordinate
of any lift. -/
theorem constantCoeff_wittVector_truncate (x : 𝕎 R) :
    constantCoeff (WittVector.truncate (n + 1) x) = x.coeff 0 :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- `TruncatedWittVector.constantCoeff` evaluates the `0`-th Witt coordinate. -/
@[simp]
theorem constantCoeff_apply (x : TruncatedWittVector p (n + 1) R) :
    constantCoeff x = x.coeff 0 := by
  conv_lhs => rw [← wittVector_truncate_out x]
  rw [constantCoeff_wittVector_truncate]
  exact coeff_out x 0

/-- The `0`-th coordinate of a numeral `ofNat(k)` (`k ≥ 2`) in `TruncatedWittVector p (n + 1) R` is
the numeral in `R`. -/
@[simp]
theorem coeff_ofNat_zero (k : ℕ) [k.AtLeastTwo] :
    (ofNat(k) : TruncatedWittVector p (n + 1) R).coeff 0 = ofNat(k) := by
  rw [← constantCoeff_apply, map_ofNat]

/-- The `0`-th coordinate homomorphism `TruncatedWittVector.constantCoeff` is surjective. -/
theorem constantCoeff_surjective :
    Function.Surjective (constantCoeff : TruncatedWittVector p (n + 1) R → R) := fun r ↦
  ⟨WittVector.truncate (n + 1) (WittVector.teichmuller p r), by simp⟩

variable (p R) in
/-- Truncated Witt vectors of length `1` are canonically isomorphic to the base ring `R` via the
zeroth Witt coordinate. -/
def constantCoeffEquiv : TruncatedWittVector p 1 R ≃+* R :=
  RingEquiv.ofBijective constantCoeff
    ⟨fun x y h ↦ ext fun i ↦ by
      rw [Fin.eq_zero i]
      simpa only [constantCoeff_apply] using h,
      constantCoeff_surjective⟩

/-- `TruncatedWittVector.constantCoeffEquiv` evaluates the `0`-th coordinate. -/
@[simp]
theorem constantCoeffEquiv_apply (x : TruncatedWittVector p 1 R) :
    constantCoeffEquiv p R x = x.coeff 0 :=
  constantCoeff_apply x

/-- The `0`-th coordinate of `(constantCoeffEquiv p R).symm r` is `r`. -/
@[simp]
theorem coeff_constantCoeffEquiv_symm_zero (r : R) :
    ((constantCoeffEquiv p R).symm r).coeff 0 = r := by
  simpa only [constantCoeffEquiv_apply] using (constantCoeffEquiv p R).apply_symm_apply r

/-- `(constantCoeffEquiv p R).symm r` is the length-one Witt vector with sole entry `r`. -/
theorem constantCoeffEquiv_symm_apply (r : R) :
    (constantCoeffEquiv p R).symm r = mk p fun _ ↦ r := by
  ext i
  rw [Fin.eq_zero i, coeff_constantCoeffEquiv_symm_zero, coeff_mk]

/-- `TruncatedWittVector.constantCoeffEquiv` sends the length-one truncation of `x : 𝕎 R` to
`x.coeff 0`. -/
theorem constantCoeffEquiv_wittVector_truncate (x : 𝕎 R) :
    constantCoeffEquiv p R (WittVector.truncate 1 x) = x.coeff 0 := by
  simp

/-- Functoriality of `TruncatedWittVector p n` along a ring homomorphism `f : R →+* S`, acting
coordinatewise. -/
def map (f : R →+* S) : TruncatedWittVector p n R →+* TruncatedWittVector p n S :=
  RingHom.liftOfRightInverse (WittVector.truncate n) out truncateFun_out
    ⟨(WittVector.truncate n).comp (WittVector.map f), fun x hx ↦ by
      rw [WittVector.mem_ker_truncate] at hx
      rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, WittVector.mem_ker_truncate]
      intro i hi
      rw [WittVector.map_coeff, hx i hi, map_zero]⟩

/-- `TruncatedWittVector.map f` commutes with `WittVector.truncate` as a ring homomorphism. -/
@[simp]
theorem map_comp_wittVector_truncate (f : R →+* S) :
    (map (p := p) (n := n) f).comp (WittVector.truncate n) =
      (WittVector.truncate n).comp (WittVector.map f) :=
  RingHom.liftOfRightInverse_comp _ _ _ _

/-- Pointwise form of `TruncatedWittVector.map_comp_wittVector_truncate`. -/
@[simp]
theorem map_wittVector_truncate (f : R →+* S) (x : 𝕎 R) :
    map f (WittVector.truncate n x) = WittVector.truncate n (WittVector.map f x) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- `TruncatedWittVector.map f` applies `f` to each Witt coordinate. -/
@[simp]
theorem coeff_map (f : R →+* S) (x : TruncatedWittVector p n R) (i : Fin n) :
    (map f x).coeff i = f (x.coeff i) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  simp

/-- Mapping along the identity ring homomorphism is the identity on `TruncatedWittVector p n R`. -/
@[simp]
theorem map_id : map (p := p) (n := n) (RingHom.id R) = RingHom.id (TruncatedWittVector p n R) := by
  ext x i
  simp

/-- `TruncatedWittVector.map` respects composition of ring homomorphisms. -/
theorem map_comp (g : S →+* T) (f : R →+* S) :
    map (p := p) (n := n) (g.comp f) = (map g).comp (map f) := by
  ext x i
  simp

/-- Pointwise composition law for `TruncatedWittVector.map`. -/
@[simp]
theorem map_map (g : S →+* T) (f : R →+* S) (x : TruncatedWittVector p n R) :
    map g (map f x) = map (g.comp f) x := by
  rw [map_comp, RingHom.comp_apply]

/-- `TruncatedWittVector.map` commutes with restriction `TruncatedWittVector.truncate`. -/
@[simp]
theorem truncate_map {m : ℕ} (hm : n ≤ m) (f : R →+* S) (x : TruncatedWittVector p m R) :
    truncate hm (map f x) = map f (truncate hm x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p m R x
  simp

/-- Bundled ring-homomorphism form of `TruncatedWittVector.truncate_map`. -/
theorem truncate_comp_map {m : ℕ} (hm : n ≤ m) (f : R →+* S) :
    (truncate (p := p) hm).comp (map f) = (map f).comp (truncate hm) := by
  ext1 x
  exact truncate_map hm f x

/-- `TruncatedWittVector.map f` is injective when `f` is injective. -/
theorem map_injective (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (map f : TruncatedWittVector p n R → TruncatedWittVector p n S) := by
  intro x y h
  ext i
  exact hf (by simpa only [coeff_map] using congrArg (coeff i) h)

/-- `TruncatedWittVector.map f` is surjective when `f` is surjective. -/
theorem map_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (map f : TruncatedWittVector p n R → TruncatedWittVector p n S) := by
  intro y
  refine ⟨mk p fun i ↦ Classical.choose (hf (y.coeff i)), ?_⟩
  ext i
  simp [Classical.choose_spec (hf (y.coeff i))]

variable (p n) in
/-- The Teichmüller multiplicative lift `R →* TruncatedWittVector p n R`, obtained by truncating
`WittVector.teichmuller`. -/
def teichmuller : R →* TruncatedWittVector p n R :=
  (WittVector.truncate n).toMonoidHom.comp (WittVector.teichmuller p)

/-- `TruncatedWittVector.teichmuller` is the truncation of `WittVector.teichmuller`. -/
theorem teichmuller_eq_wittVector_truncate (r : R) :
    teichmuller p n r = WittVector.truncate n (WittVector.teichmuller p r) :=
  (rfl)

/-- The Teichmüller lift of `0` in `TruncatedWittVector p n R` is `0`. -/
@[simp]
theorem teichmuller_zero : teichmuller p n (0 : R) = 0 := by
  simp [teichmuller_eq_wittVector_truncate]

/-- The `0`-th coordinate of the Teichmüller lift `[r]` in length `n + 1` is `r`. -/
@[simp]
theorem coeff_teichmuller_zero (r : R) : (teichmuller p (n + 1) r).coeff 0 = r := by
  simp [teichmuller_eq_wittVector_truncate]

/-- Positive coordinates of the Teichmüller lift `[r]` in length `n + 1` vanish. -/
@[simp]
theorem coeff_teichmuller_succ (r : R) (i : Fin n) :
    (teichmuller p (n + 1) r).coeff i.succ = 0 := by
  simp [teichmuller_eq_wittVector_truncate]

/-- Restriction preserves Teichmüller lifts. -/
@[simp]
theorem truncate_teichmuller {m : ℕ} (hm : n ≤ m) (r : R) :
    truncate hm (teichmuller p m r) = teichmuller p n r := by
  simp [teichmuller_eq_wittVector_truncate]

/-- `TruncatedWittVector.map` preserves Teichmüller lifts. -/
@[simp]
theorem map_teichmuller (f : R →+* S) (r : R) :
    map f (teichmuller p n r) = teichmuller p n (f r) := by
  simp [teichmuller_eq_wittVector_truncate]

/-! ### Finite Witt Frobenius -/

/-- The finite Witt Frobenius homomorphism
`TruncatedWittVector p (n + 1) R →+* TruncatedWittVector p n R`, descended from
`WittVector.frobenius` along truncation. -/
def frobenius : TruncatedWittVector p (n + 1) R →+* TruncatedWittVector p n R :=
  RingHom.liftOfRightInverse (WittVector.truncate (n + 1)) out truncateFun_out
    ⟨(WittVector.truncate n).comp WittVector.frobenius, fun x hx ↦ by
      rw [WittVector.mem_ker_truncate] at hx
      rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, WittVector.mem_ker_truncate]
      intro i hi
      have hcongr :
          (WittVector.frobenius x).coeff i = (WittVector.frobenius (0 : 𝕎 R)).coeff i :=
        WittVector.coeff_frobenius_congr fun k hk ↦ by
          rw [hx k (by omega), WittVector.zero_coeff]
      rw [hcongr, map_zero, WittVector.zero_coeff]⟩

/-- Finite Witt Frobenius is the quotient of infinite Witt Frobenius through truncation. -/
@[simp]
theorem frobenius_comp_wittVector_truncate :
    (frobenius (p := p) (n := n) (R := R)).comp (WittVector.truncate (n + 1)) =
      (WittVector.truncate n).comp WittVector.frobenius :=
  RingHom.liftOfRightInverse_comp _ _ _ _

/-- Pointwise form of `TruncatedWittVector.frobenius_comp_wittVector_truncate`. -/
@[simp]
theorem frobenius_wittVector_truncate (x : 𝕎 R) :
    frobenius (WittVector.truncate (n + 1) x) = WittVector.truncate n (WittVector.frobenius x) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- Computing finite Witt Frobenius via the canonical zero-padded lift `out`. -/
theorem frobenius_out (x : TruncatedWittVector p (n + 1) R) :
    WittVector.truncate n (WittVector.frobenius x.out) = frobenius x := by
  rw [← frobenius_wittVector_truncate, wittVector_truncate_out]

/-- Uniqueness of finite Witt Frobenius: it is the unique ring homomorphism
`TruncatedWittVector p (n + 1) R →+* TruncatedWittVector p n R` intertwining `WittVector.truncate`
with `WittVector.frobenius`. -/
theorem eq_frobenius_of_comp_wittVector_truncate
    {g : TruncatedWittVector p (n + 1) R →+* TruncatedWittVector p n R}
    (hg : g.comp (WittVector.truncate (n + 1)) =
      (WittVector.truncate n).comp WittVector.frobenius) :
    g = frobenius := by
  ext1 x
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 1) R x
  simpa using congrArg (fun φ : 𝕎 R →+* TruncatedWittVector p n R ↦ φ x) hg

/-- Finite Witt Frobenius commutes with restriction `TruncatedWittVector.truncate`. -/
@[simp]
theorem truncate_frobenius {m : ℕ} (hm : n ≤ m) (x : TruncatedWittVector p (m + 1) R) :
    truncate hm (frobenius x) = frobenius (truncate (Nat.succ_le_succ hm) x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (m + 1) R x
  simp

/-- Bundled ring-homomorphism form of `TruncatedWittVector.truncate_frobenius`:
`res_n ∘ F_m = F_n ∘ res_{m + 1}` for `n ≤ m`. -/
@[simp]
theorem truncate_comp_frobenius {m : ℕ} (hm : n ≤ m) :
    (truncate (p := p) (R := R) hm).comp frobenius =
      frobenius.comp (truncate (Nat.succ_le_succ hm)) := by
  ext1 x
  exact truncate_frobenius hm x

/-- The `i`-th coordinate of `frobenius x` agrees with the `i`-th coordinate of
`WittVector.frobenius x.out`. -/
theorem coeff_frobenius (x : TruncatedWittVector p (n + 1) R) (i : Fin n) :
    (frobenius x).coeff i = (WittVector.frobenius x.out).coeff i := by
  rw [← frobenius_out, WittVector.coeff_truncate]

/-- Without any characteristic-`p` assumption, the zeroth coordinate of `frobenius x` on
`TruncatedWittVector p (n + 2) R` is `x₀ ^ p + p * x₁`. At `n = 0` this gives the length-two
formula `F(x₀, x₁) = x₀ ^ p + p * x₁`. -/
theorem coeff_frobenius_zero (x : TruncatedWittVector p (n + 2) R) :
    (frobenius x).coeff 0 = x.coeff 0 ^ p + p * x.coeff 1 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 2) R x
  rw [frobenius_wittVector_truncate, WittVector.coeff_truncate, Fin.val_zero,
    WittVector.coeff_frobenius_zero, WittVector.coeff_truncate, Fin.val_zero,
    WittVector.coeff_truncate]
  congr 2

/-- In characteristic `p`, finite Witt Frobenius acts coordinatewise by `p`-th powers along the
inclusion `Fin.castSucc : Fin n → Fin (n + 1)`. -/
@[simp]
theorem coeff_frobenius_charP [CharP R p] (x : TruncatedWittVector p (n + 1) R) (i : Fin n) :
    (frobenius x).coeff i = x.coeff i.castSucc ^ p := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 1) R x
  simp

/-- Finite Witt Frobenius is natural with respect to ring homomorphisms. -/
@[simp]
theorem map_frobenius (f : R →+* S) (x : TruncatedWittVector p (n + 1) R) :
    map f (frobenius x) = frobenius (map f x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 1) R x
  simp

/-- Bundled ring-homomorphism form of `TruncatedWittVector.map_frobenius`. -/
theorem map_comp_frobenius (f : R →+* S) :
    (map (p := p) (n := n) f).comp frobenius = frobenius.comp (map f) := by
  ext1 x
  exact map_frobenius f x

/-- Finite Witt Frobenius sends the Teichmüller lift `[r]` in length `n + 1` to `[r ^ p]` in
length `n`. -/
theorem frobenius_teichmuller_eq_teichmuller_pow (r : R) :
    frobenius (teichmuller p (n + 1) r) = teichmuller p n (r ^ p) := by
  rw [teichmuller_eq_wittVector_truncate, frobenius_wittVector_truncate,
    WittVector.frobenius_teichmuller_eq, ← teichmuller_eq_wittVector_truncate]

/-- Finite Witt Frobenius sends `[r]` in length `n + 1` to `[r] ^ p` in length `n`. -/
@[simp]
theorem frobenius_teichmuller (r : R) :
    frobenius (teichmuller p (n + 1) r) = teichmuller p n r ^ p := by
  rw [frobenius_teichmuller_eq_teichmuller_pow, map_pow]

/-! ### Finite Witt Verschiebung and `F`–`V` identities -/

/-- The finite Witt Verschiebung additive homomorphism
`TruncatedWittVector p n R →+ TruncatedWittVector p (n + 1) R`, descended from
`WittVector.verschiebung` along truncation. -/
def verschiebung : TruncatedWittVector p n R →+ TruncatedWittVector p (n + 1) R :=
  AddMonoidHom.liftOfRightInverse (WittVector.truncate n).toAddMonoidHom out
    (fun x ↦ wittVector_truncate_out x)
    ⟨(WittVector.truncate (n + 1)).toAddMonoidHom.comp WittVector.verschiebung, fun x hx ↦ by
      have hx' : ∀ i < n, x.coeff i = 0 := (WittVector.mem_ker_truncate n x).mp hx
      refine (WittVector.mem_ker_truncate (n + 1) (WittVector.verschiebung x)).mpr ?_
      rintro (_ | i) hi
      · exact WittVector.verschiebung_coeff_zero x
      · rw [WittVector.verschiebung_coeff_succ]
        exact hx' i (Nat.lt_of_succ_lt_succ hi)⟩

/-- Finite Witt Verschiebung commutes with `WittVector.truncate`. -/
@[simp]
theorem verschiebung_wittVector_truncate (x : 𝕎 R) :
    verschiebung (WittVector.truncate n x) =
      WittVector.truncate (n + 1) (WittVector.verschiebung x) :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- Bundled additive-homomorphism form of `TruncatedWittVector.verschiebung_wittVector_truncate`. -/
theorem verschiebung_comp_wittVector_truncate :
    (verschiebung (p := p) (n := n) (R := R)).comp (WittVector.truncate n).toAddMonoidHom =
      (WittVector.truncate (n + 1)).toAddMonoidHom.comp WittVector.verschiebung :=
  AddMonoidHom.liftOfRightInverse_comp _ _ _ _

/-- Computing finite Witt Verschiebung via the canonical zero-padded lift `out`. -/
theorem verschiebung_out (x : TruncatedWittVector p n R) :
    WittVector.truncate (n + 1) (WittVector.verschiebung x.out) = verschiebung x := by
  rw [← verschiebung_wittVector_truncate, wittVector_truncate_out]

/-- The `0`-th coordinate of `verschiebung x` vanishes. -/
@[simp]
theorem verschiebung_coeff_zero (x : TruncatedWittVector p n R) :
    (verschiebung x).coeff 0 = 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  simp

/-- Finite Witt Verschiebung shifts coordinates up by one: `(V x)_{i + 1} = x_i`. -/
@[simp]
theorem verschiebung_coeff_succ (x : TruncatedWittVector p n R) (i : Fin n) :
    (verschiebung x).coeff i.succ = x.coeff i := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  simp

/-- Finite Witt Verschiebung is injective over every commutative ring `R`, including rings with
`p`-torsion. -/
theorem verschiebung_injective :
    Function.Injective
      (verschiebung : TruncatedWittVector p n R → TruncatedWittVector p (n + 1) R) := by
  intro x y h
  ext i
  simpa only [verschiebung_coeff_succ] using congrArg (coeff i.succ) h

/-- Finite Witt Verschiebung commutes with restriction `TruncatedWittVector.truncate`. -/
@[simp]
theorem truncate_verschiebung {m : ℕ} (hm : n ≤ m) (x : TruncatedWittVector p m R) :
    truncate (Nat.succ_le_succ hm) (verschiebung x) = verschiebung (truncate hm x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p m R x
  simp

/-- Bundled additive-homomorphism form of `TruncatedWittVector.truncate_verschiebung`. -/
theorem truncate_comp_verschiebung {m : ℕ} (hm : n ≤ m) :
    (truncate (p := p) (R := R) (Nat.succ_le_succ hm)).toAddMonoidHom.comp verschiebung =
      verschiebung.comp (truncate hm).toAddMonoidHom := by
  ext1 x
  exact truncate_verschiebung hm x

/-- Finite Witt Verschiebung is natural with respect to ring homomorphisms. -/
@[simp]
theorem map_verschiebung (f : R →+* S) (x : TruncatedWittVector p n R) :
    map f (verschiebung x) = verschiebung (map f x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  simp

/-- Over every commutative ring `R`, the composition `F ∘ V` on `TruncatedWittVector p n R` is
multiplication by `p`. -/
@[simp]
theorem frobenius_verschiebung (x : TruncatedWittVector p n R) :
    frobenius (verschiebung x) = x * p := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  simp [WittVector.frobenius_verschiebung]

/-- Bundled additive-homomorphism form of `TruncatedWittVector.frobenius_verschiebung`:
`F_n ∘ V_n = p • id`. -/
theorem frobenius_comp_verschiebung :
    (frobenius : TruncatedWittVector p (n + 1) R →+* TruncatedWittVector p n R).toAddMonoidHom.comp
      verschiebung = p • AddMonoidHom.id (TruncatedWittVector p n R) := by
  ext1 x
  simp [nsmul_eq_mul, mul_comm]

/-- The projection formula for finite Frobenius and Verschiebung over any commutative ring `R`:
`V(x * F(y)) = V(x) * y`. -/
theorem verschiebung_mul_frobenius (x : TruncatedWittVector p n R)
    (y : TruncatedWittVector p (n + 1) R) :
    verschiebung (x * frobenius y) = verschiebung x * y := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p (n + 1) R y
  rw [frobenius_wittVector_truncate, ← map_mul, verschiebung_wittVector_truncate,
    WittVector.verschiebung_mul_frobenius, map_mul, verschiebung_wittVector_truncate]

/-- Symmetric form of the finite projection formula: `V(F(x) * y) = x * V(y)`. -/
theorem verschiebung_frobenius_mul (x : TruncatedWittVector p (n + 1) R)
    (y : TruncatedWittVector p n R) :
    verschiebung (frobenius x * y) = x * verschiebung y := by
  rw [mul_comm, verschiebung_mul_frobenius, mul_comm]

/-- Over any commutative ring `R`, `V(F(y)) = V(1) * y` on `TruncatedWittVector p (n + 1) R`. -/
theorem verschiebung_frobenius_eq_verschiebung_one_mul (y : TruncatedWittVector p (n + 1) R) :
    verschiebung (frobenius y) = verschiebung 1 * y := by
  simpa using verschiebung_mul_frobenius (1 : TruncatedWittVector p n R) y

/-- Over a ring `R` of characteristic `p`, `V(F(x)) = x * p` on `TruncatedWittVector p (n + 1) R`
(i.e. on `W_r(R)` for every `r ≥ 1`). -/
theorem verschiebung_frobenius [CharP R p] (x : TruncatedWittVector p (n + 1) R) :
    verschiebung (frobenius x) = x * p := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 1) R x
  simp [WittVector.verschiebung_frobenius]

/-- Bundled additive-homomorphism form of `TruncatedWittVector.verschiebung_frobenius` in
characteristic `p`. -/
theorem verschiebung_comp_frobenius [CharP R p] :
    (verschiebung : TruncatedWittVector p n R →+ TruncatedWittVector p (n + 1) R).comp
      frobenius.toAddMonoidHom = p • AddMonoidHom.id (TruncatedWittVector p (n + 1) R) := by
  ext1 x
  simp [verschiebung_frobenius, nsmul_eq_mul, mul_comm]

/-- Over `ZMod p`, finite Frobenius on `TruncatedWittVector p (n + 1) (ZMod p)` coincides with
restriction `TruncatedWittVector.truncate (Nat.le_succ n)`. -/
theorem frobenius_zmodp (x : TruncatedWittVector p (n + 1) (ZMod p)) :
    frobenius x = truncate (Nat.le_succ n) x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 1) (ZMod p) x
  simp

/-- Over `ZMod p`, applying restriction followed by finite Verschiebung on
`TruncatedWittVector p (n + 1) (ZMod p)` is multiplication by `p`. -/
theorem verschiebung_truncate_zmodp (x : TruncatedWittVector p (n + 1) (ZMod p)) :
    verschiebung (truncate (Nat.le_succ n) x) = x * p := by
  rw [← frobenius_zmodp, verschiebung_frobenius]

/-- Under `TruncatedWittVector.zmodEquivTrunc : ZMod (p ^ r) ≃+* TruncatedWittVector p r (ZMod p)`,
finite Verschiebung corresponds to multiplication by `p` from `ZMod (p ^ n)` to
`ZMod (p ^ (n + 1))`. -/
theorem zmodEquivTrunc_symm_verschiebung (x : ZMod (p ^ (n + 1))) :
    (zmodEquivTrunc p (n + 1)).symm
      (verschiebung (zmodEquivTrunc p n (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) _ x))) =
      p * x := by
  rw [← commutes' p n (Nat.le_succ n) x, verschiebung_truncate_zmodp, map_mul, map_natCast,
    RingEquiv.symm_apply_apply, mul_comm]

/-! ### Iterated Verschiebung and the kernel of restriction -/

/-- Auxiliary additive monoid homomorphism packaging `WittVector.verschiebung^[r]`. -/
private def iterateVerschiebungHom (r : ℕ) : 𝕎 R →+ 𝕎 R where
  toFun := WittVector.verschiebung^[r]
  map_zero' := by
    induction r with
    | zero => rfl
    | succ r ih => simp [Function.iterate_succ_apply', ih]
  map_add' x y := by
    induction r with
    | zero => rfl
    | succ r ih => simp [Function.iterate_succ_apply', ih]

/-- The `r`-fold shift `TruncatedWittVector p m R →+ TruncatedWittVector p (r + m) R`, descended
from `WittVector.verschiebung^[r]` along truncation. -/
def iterateVerschiebung {m : ℕ} (r : ℕ) :
    TruncatedWittVector p m R →+ TruncatedWittVector p (r + m) R :=
  AddMonoidHom.liftOfRightInverse (WittVector.truncate m).toAddMonoidHom out
    (fun x ↦ wittVector_truncate_out x)
    ⟨(WittVector.truncate (r + m)).toAddMonoidHom.comp (iterateVerschiebungHom r), fun x hx ↦ by
      have hx' : ∀ i < m, x.coeff i = 0 := (WittVector.mem_ker_truncate m x).mp hx
      refine (WittVector.mem_ker_truncate (r + m)
        (WittVector.verschiebung^[r] x)).mpr fun j hj ↦ ?_
      by_cases hjr : j < r
      · exact WittVector.iterate_verschiebung_coeff_eq_zero x hjr
      · have hsub : j - r + r = j := Nat.sub_add_cancel (not_lt.mp hjr)
        rw [← hsub, WittVector.iterate_verschiebung_coeff]
        exact hx' (j - r) (by omega)⟩

/-- `TruncatedWittVector.iterateVerschiebung r` commutes with `WittVector.truncate` and
`WittVector.verschiebung^[r]`. -/
@[simp]
theorem iterateVerschiebung_wittVector_truncate {m : ℕ} (r : ℕ) (x : 𝕎 R) :
    iterateVerschiebung r (WittVector.truncate m x) =
      WittVector.truncate (r + m) (WittVector.verschiebung^[r] x) :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- Coordinates below `r` of `iterateVerschiebung r x` vanish. -/
theorem iterateVerschiebung_coeff_of_lt {m : ℕ} (r : ℕ) (x : TruncatedWittVector p m R)
    {i : Fin (r + m)} (hi : (i : ℕ) < r) :
    (iterateVerschiebung r x).coeff i = 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p m R x
  rw [iterateVerschiebung_wittVector_truncate, WittVector.coeff_truncate]
  exact WittVector.iterate_verschiebung_coeff_eq_zero x hi

/-- Coordinates at `r + i` of `iterateVerschiebung r x` recover the `i`-th coordinate of `x`. -/
@[simp]
theorem iterateVerschiebung_coeff_add {m : ℕ} (r : ℕ) (x : TruncatedWittVector p m R)
    (i : Fin m) :
    (iterateVerschiebung r x).coeff ⟨r + i, Nat.add_lt_add_left i.is_lt r⟩ = x.coeff i := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p m R x
  rw [iterateVerschiebung_wittVector_truncate, WittVector.coeff_truncate, Fin.val_mk,
    add_comm r (i : ℕ), WittVector.iterate_verschiebung_coeff, WittVector.coeff_truncate]

/-- Iterated Verschiebung is injective for every `r` and `m`. -/
theorem iterateVerschiebung_injective {m : ℕ} (r : ℕ) :
    Function.Injective
      (iterateVerschiebung r : TruncatedWittVector p m R → TruncatedWittVector p (r + m) R) := by
  intro x y h
  ext i
  simpa only [iterateVerschiebung_coeff_add] using
    congrArg (coeff ⟨r + i, Nat.add_lt_add_left i.is_lt r⟩) h

/-- Compatibility of `iterateVerschiebung` with single-step `verschiebung`. -/
theorem iterateVerschiebung_verschiebung {m : ℕ} (r : ℕ) (x : TruncatedWittVector p m R) :
    iterateVerschiebung r (verschiebung x) = verschiebung (iterateVerschiebung r x) := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p m R x
  rw [verschiebung_wittVector_truncate, iterateVerschiebung_wittVector_truncate,
    iterateVerschiebung_wittVector_truncate, verschiebung_wittVector_truncate,
    ← Function.iterate_succ_apply, Function.iterate_succ_apply']
  rfl

/-- Restricting `iterateVerschiebung r x` to the first `r` coordinates yields `0`. -/
@[simp]
theorem truncate_iterateVerschiebung_self {m : ℕ} (r : ℕ) (h : r ≤ r + m)
    (x : TruncatedWittVector p m R) :
    truncate h (iterateVerschiebung r x) = 0 := by
  ext i
  rw [coeff_truncate, coeff_zero]
  exact iterateVerschiebung_coeff_of_lt r x i.is_lt

/-- An element of `TruncatedWittVector p (r + m) R` lies in the kernel of restriction to length `r`
if and only if it lies in the image of `iterateVerschiebung r`. -/
theorem mem_ker_truncate_iff_mem_range_iterateVerschiebung {m : ℕ} (r : ℕ) (h : r ≤ r + m)
    (x : TruncatedWittVector p (r + m) R) :
    x ∈ RingHom.ker (truncate h) ↔
      x ∈ Set.range (iterateVerschiebung r : TruncatedWittVector p m R → _) := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · refine ⟨WittVector.truncate m (x.out.shift r), ?_⟩
    have hout : ∀ i < r, x.out.coeff i = 0 := by
      intro i hi
      have hx0 : (truncate h x).coeff ⟨i, hi⟩ = 0 := by
        rw [RingHom.mem_ker.mp hx, coeff_zero]
      rw [coeff_truncate] at hx0
      simpa only [Fin.val_castLE] using (coeff_out x (Fin.castLE h ⟨i, hi⟩)).trans hx0
    rw [iterateVerschiebung_wittVector_truncate, ← WittVector.eq_iterate_verschiebung hout,
      wittVector_truncate_out]
  · rintro ⟨y, rfl⟩
    exact truncate_iterateVerschiebung_self r h y

/-- Additive-subgroup form: the kernel of restriction
`TruncatedWittVector p (r + m) R →+* TruncatedWittVector p r R` is the additive range of
`iterateVerschiebung r`. -/
theorem ker_truncate_toAddMonoidHom_eq_range_iterateVerschiebung {m : ℕ} (r : ℕ) (h : r ≤ r + m) :
    (truncate (p := p) (R := R) h).toAddMonoidHom.ker =
      (iterateVerschiebung (p := p) (m := m) (R := R) r).range := by
  ext x
  exact mem_ker_truncate_iff_mem_range_iterateVerschiebung r h x

/-- The kernel of one-step restriction `W_{r + 1}(R) →+* W_r(R)` is the image of the `r`-fold
Verschiebung from `R` (identified with `W_1(R)` via `constantCoeffEquiv`). -/
theorem ker_truncate_succ_eq_range (r : ℕ) :
    (truncate (p := p) (R := R) (Nat.le_succ r)).toAddMonoidHom.ker =
      ((iterateVerschiebung (p := p) (m := 1) (R := R) r).comp
        (constantCoeffEquiv p R).symm.toAddMonoidHom).range := by
  rw [ker_truncate_toAddMonoidHom_eq_range_iterateVerschiebung (m := 1) r (Nat.le_succ r)]
  ext x
  simp only [AddMonoidHom.mem_range, AddMonoidHom.coe_comp, Function.comp_apply]
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨constantCoeffEquiv p R y, ?_⟩, fun ⟨a, ha⟩ ↦ ⟨_, ha⟩⟩
  rw [← hy]
  exact congrArg (iterateVerschiebung r) ((constantCoeffEquiv p R).symm_apply_apply y)

/-- Elementwise form of `TruncatedWittVector.ker_truncate_succ_eq_range`: an element of
`W_{r + 1}(R)` restricts to `0` in `W_r(R)` iff it is the `r`-fold Verschiebung of an element of
`W_1(R) ≃+* R`. -/
theorem mem_ker_truncate_succ_iff (r : ℕ) (x : TruncatedWittVector p (r + 1) R) :
    x ∈ RingHom.ker (truncate (Nat.le_succ r)) ↔
      ∃ a : R, iterateVerschiebung r ((constantCoeffEquiv p R).symm a) = x := by
  simpa [RingHom.mem_ker, AddMonoidHom.mem_ker, AddMonoidHom.mem_range] using
    SetLike.ext_iff.mp (ker_truncate_succ_eq_range (p := p) (R := R) r) x

/-! ### Ghost components and joint ghost injectivity -/

/-- The `i`-th ghost component (`i : Fin n`) on `TruncatedWittVector p n R`, descended from
`WittVector.ghostComponent i` along truncation. -/
def ghostComponent (i : Fin n) : TruncatedWittVector p n R →+* R :=
  RingHom.liftOfRightInverse (WittVector.truncate n) out truncateFun_out
    ⟨WittVector.ghostComponent i, fun x hx ↦ by
      rw [WittVector.mem_ker_truncate] at hx
      rw [RingHom.mem_ker]
      have hcongr : WittVector.ghostComponent i x = WittVector.ghostComponent i (0 : 𝕎 R) :=
        WittVector.ghostComponent_congr fun k hk ↦ by
          rw [hx k (lt_of_lt_of_le hk i.is_lt), WittVector.zero_coeff]
      rw [hcongr, map_zero]⟩

/-- `TruncatedWittVector.ghostComponent i` composed with `WittVector.truncate n` recovers
`WittVector.ghostComponent i`. -/
@[simp]
theorem ghostComponent_comp_wittVector_truncate (i : Fin n) :
    (ghostComponent (p := p) (R := R) i).comp (WittVector.truncate n) =
      WittVector.ghostComponent i :=
  RingHom.liftOfRightInverse_comp _ _ _ _

/-- Pointwise form of `TruncatedWittVector.ghostComponent_comp_wittVector_truncate`. -/
@[simp]
theorem ghostComponent_wittVector_truncate (i : Fin n) (x : 𝕎 R) :
    ghostComponent i (WittVector.truncate n x) = WittVector.ghostComponent i x :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- `TruncatedWittVector.ghostComponent i x` agrees with `WittVector.ghostComponent i x.out`. -/
theorem ghostComponent_eq_out (i : Fin n) (x : TruncatedWittVector p n R) :
    ghostComponent i x = WittVector.ghostComponent i x.out := by
  conv_lhs => rw [← wittVector_truncate_out x]
  rw [ghostComponent_wittVector_truncate]

/-- The `0`-th ghost component on `TruncatedWittVector p (n + 1) R` is the `0`-th Witt
coordinate. -/
theorem ghostComponent_zero (x : TruncatedWittVector p (n + 1) R) :
    ghostComponent 0 x = x.coeff 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 1) R x
  simp [WittVector.ghostComponent_apply, wittPolynomial_zero]

/-- The `1`-st ghost component on `TruncatedWittVector p (n + 2) R` is `x₀ ^ p + p * x₁`. -/
theorem ghostComponent_one (x : TruncatedWittVector p (n + 2) R) :
    ghostComponent 1 x = x.coeff 0 ^ p + p * x.coeff 1 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 2) R x
  rw [ghostComponent_wittVector_truncate, Fin.val_one, WittVector.ghostComponent_apply,
    wittPolynomial_one, WittVector.coeff_truncate, Fin.val_zero, WittVector.coeff_truncate,
    Fin.val_one]
  simp only [MvPolynomial.aeval_X, map_add, map_mul, map_pow, map_natCast]
  ring

/-- Restriction preserves ghost components along `Fin.castLE`. -/
@[simp]
theorem ghostComponent_truncate {m : ℕ} (hm : n ≤ m) (i : Fin n)
    (x : TruncatedWittVector p m R) :
    ghostComponent i (truncate hm x) = ghostComponent (Fin.castLE hm i) x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p m R x
  simp

/-- The `i`-th ghost component of `frobenius x` is the `(i + 1)`-st ghost component of `x`. -/
@[simp]
theorem ghostComponent_frobenius (i : Fin n) (x : TruncatedWittVector p (n + 1) R) :
    ghostComponent i (frobenius x) = ghostComponent i.succ x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p (n + 1) R x
  simp [WittVector.ghostComponent_frobenius]

/-- The `0`-th ghost component of `verschiebung x` vanishes. -/
@[simp]
theorem ghostComponent_zero_verschiebung (x : TruncatedWittVector p n R) :
    ghostComponent 0 (verschiebung x) = 0 := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  simp [WittVector.ghostComponent_zero_verschiebung]

/-- The `(i + 1)`-st ghost component of `verschiebung x` is `p` times the `i`-th ghost component of
`x`. -/
@[simp]
theorem ghostComponent_succ_verschiebung (i : Fin n) (x : TruncatedWittVector p n R) :
    ghostComponent i.succ (verschiebung x) = p * ghostComponent i x := by
  obtain ⟨x, rfl⟩ := WittVector.truncate_surjective p n R x
  simp [WittVector.ghostComponent_verschiebung]

/-- The bundled finite ghost map `TruncatedWittVector p n R →+* (Fin n → R)` packaging the first
`n` ghost components. -/
def ghostMap : TruncatedWittVector p n R →+* (Fin n → R) :=
  RingHom.pi ghostComponent

/-- Coordinate evaluation of `TruncatedWittVector.ghostMap`. -/
@[simp]
theorem ghostMap_apply (x : TruncatedWittVector p n R) (i : Fin n) :
    ghostMap x i = ghostComponent i x :=
  (rfl)

/-- `TruncatedWittVector.ghostMap` agrees with evaluating `WittVector.ghostComponent` on `out`. -/
theorem ghostMap_eq_fun_out :
    (ghostMap : TruncatedWittVector p n R → Fin n → R) =
      fun x (i : Fin n) ↦ WittVector.ghostComponent i x.out := by
  funext x i
  exact ghostComponent_eq_out i x

/-- If multiplication by `p` on `R` is injective, then the first `n` ghost components
`x ↦ (WittVector.ghostComponent i x.out)_{i < n}` are jointly injective on
`TruncatedWittVector p n R`. -/
theorem ghostComponent_out_injective
    (hp_inj : Function.Injective (fun a : R ↦ (p : R) * a)) :
    Function.Injective
      (fun (x : TruncatedWittVector p n R) (i : Fin n) ↦ WittVector.ghostComponent i x.out) := by
  intro x y h
  have hout := WittVector.eq_of_ghostComponent_eq hp_inj (x := x.out) (y := y.out) (n := n)
    fun i hi ↦ congrFun h ⟨i, hi⟩
  ext i
  simpa only [coeff_out] using hout i i.is_lt

/-- If multiplication by `p` on `R` is injective, then `TruncatedWittVector.ghostMap` is
injective. -/
theorem ghostMap_injective
    (hp_inj : Function.Injective (fun a : R ↦ (p : R) * a)) :
    Function.Injective (ghostMap : TruncatedWittVector p n R → Fin n → R) := by
  rw [ghostMap_eq_fun_out]
  exact ghostComponent_out_injective hp_inj

end TruncatedWittVector

end
