/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.Defs
public import TauCeti.RingTheory.DividedPowers.Generators
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Localization

/-!
# Extension of divided powers along principal ideals, flat algebras, and localizations

Let `f : A →+* B` be a homomorphism of commutative rings and `γ : DividedPowers I` a divided power
structure on an ideal `I ≤ A`. Whenever a divided power structure `θ` on `I.map f` makes `f` a
divided power morphism `(I, γ) → (I.map f, θ)`, `θ` is uniquely determined on every finite linear
combination `∑ i, b i * f (x i)` (`x i ∈ I`) by the multinomial formula
`γ.scalarExtendCoeff f n b x = ∑ e ∈ piAntidiag univ n, ∏ i, b i ^ e i * f (γ.dpow (e i) (x i))`.

Following Roby (1965), Berthelot (1974, I.1.6.2–1.6.3), and
[Stacks Lemma 07H1](https://stacks.math.columbia.edu/tag/07H1), this file proves uniqueness of such
extensions in general and constructs `θ : DividedPowers (I.map f)` in three settings:

1. **Principal ideals** (`DividedPowers.extendSpanSingleton`): when `I = Ideal.span {x}`, along an
   arbitrary ring homomorphism `f : A →+* B`, via `b * f x ↦ b ^ n * f (γ.dpow n x)`.
2. **Flat algebras** (`DividedPowers.flatExtend`): when `B` is a flat `A`-algebra, by combining the
   equational criterion for flatness (`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`) with the
   substitution invariance of `DividedPowers.scalarExtendCoeff` and the generator criterion
   `TauCeti.AdditivePowers.toDividedPowers`.
3. **Localizations** (`DividedPowers.localization`): for any multiplicative submonoid
   `M : Submonoid A` and localization `B` (`[IsLocalization M B]`), with the explicit fraction
   formula `(γ.localization M B).dpow n (mk' B x s) = mk' B (γ.dpow n x) (s ^ n)` for `x ∈ I`.

## Main declarations

* `DividedPowers.eq_of_isDPMorphism_map`: at most one `DividedPowers (I.map f)` makes `f` a PD
  morphism from `(I, γ)`.
* `DividedPowers.extendSpanSingleton`: extension of `γ` along any `f : A →+* B` when
  `I = Ideal.span {x}`.
* `DividedPowers.scalarExtendCoeff`: the forced degree-`n` coefficient on `∑ i, b i * f (x i)`.
* `DividedPowers.scalarExtendCoeff_subst`: invariance of `scalarExtendCoeff` under matrix
  factorizations `b i = ∑ j, f (a i j) * c j`, `y j = ∑ i, a i j * x i`.
* `DividedPowers.flatAdditivePowers`: the `TauCeti.AdditivePowers` candidate on
  `I.map (algebraMap A B)` for a flat `A`-algebra `B`.
* `DividedPowers.flatExtend`: the unique `DividedPowers (I.map (algebraMap A B))` extending `γ` to
  a flat `A`-algebra `B`.
* `DividedPowers.isDPMorphism_flatExtend_iff`: universal property of `γ.flatExtend B` for ring
  homomorphisms `B →+* C`.
* `DividedPowers.localization`: extension of `γ` to `I.map (algebraMap A B)` for any localization
  `[IsLocalization M B]`, together with `DividedPowers.localization_dpow_mk'`.

## References

* [Stacks: Divided power algebra, Lemma 07H1](https://stacks.math.columbia.edu/tag/07H1).
* P. Berthelot, *Cohomologie cristalline des schémas de caractéristique $p > 0$*, Lecture Notes in
  Mathematics 407, Springer (1974), Chapitre I, Propositions 1.6.2–1.6.3.
* N. Roby, *Les algèbres à puissances dividées*, Bull. Sci. Math. (2) 89 (1965), 75–91.
-/

public section

open Finset Nat

namespace DividedPowers

/-! ### Uniqueness on the extended ideal `I.map f` -/

section Uniqueness

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A}

/-- At most one divided power structure on `I.map f` makes `f : A →+* B` a divided power morphism
from `(I, γ)`. -/
theorem eq_of_isDPMorphism_map (γ : DividedPowers I) (f : A →+* B)
    {θ₁ θ₂ : DividedPowers (I.map f)} (h₁ : IsDPMorphism γ θ₁ f) (h₂ : IsDPMorphism γ θ₂ f) :
    θ₁ = θ₂ := by
  ext n z
  by_cases hz : z ∈ I.map f
  · exact ((mem_dpEqualizer_iff θ₁ θ₂).mp
      (γ.le_equalizer_of_isDPMorphism f le_rfl θ₁ θ₂ h₁ h₂ hz)).2 n
  · rw [θ₁.dpow_null hz, θ₂.dpow_null hz]

end Uniqueness

/-! ### Extension of divided powers on a principal ideal -/

section PrincipalIdeal

variable {A B : Type*} [CommRing A] [CommRing B] {I : Ideal A}

/-- If `I = Ideal.span {x}` carries divided powers `γ` and `b * f x = c * f x`, then
`b ^ n * f (γ.dpow n x) = c ^ n * f (γ.dpow n x)` for every `n : ℕ`. -/
theorem pow_mul_map_eq_of_mul_map_eq (γ : DividedPowers I) {x : A} (hI : I = Ideal.span {x})
    (f : A →+* B) {b c : B} (hbc : b * f x = c * f x) (n : ℕ) :
    b ^ n * f (γ.dpow n x) = c ^ n * f (γ.dpow n x) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hx : x ∈ I := hI ▸ Ideal.mem_span_singleton_self x
    have hmem : γ.dpow n x ∈ Ideal.span {x} := hI ▸ γ.dpow_mem hn hx
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow b c n
    have hsub : (b - c) * f x = 0 := by
      rw [sub_mul, hbc, sub_self]
    rw [← sub_eq_zero, ← sub_mul, ← hr, map_mul, hd]
    calc
      (b - c) * d * (f r * f x) = ((b - c) * f x) * (d * f r) := by ring
      _ = 0 := by rw [hsub, zero_mul]

private theorem mem_map_span_singleton_iff {x : A} (hI : I = Ideal.span {x}) (f : A →+* B)
    {z : B} : z ∈ I.map f ↔ ∃ b : B, b * f x = z := by
  rw [hI, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']

private noncomputable def spanSingletonDpowAux (γ : DividedPowers I) {x : A}
    (hI : I = Ideal.span {x}) (f : A →+* B) (n : ℕ) (z : B) : B :=
  open scoped Classical in
  if hz : z ∈ I.map f then
    ((mem_map_span_singleton_iff hI f).mp hz).choose ^ n * f (γ.dpow n x)
  else 0

private theorem spanSingletonDpowAux_mul_map (γ : DividedPowers I) {x : A}
    (hI : I = Ideal.span {x}) (f : A →+* B) (n : ℕ) (b : B) :
    γ.spanSingletonDpowAux hI f n (b * f x) = b ^ n * f (γ.dpow n x) := by
  have hz : b * f x ∈ I.map f := (mem_map_span_singleton_iff hI f).mpr ⟨b, rfl⟩
  simp only [spanSingletonDpowAux, hz, ↓reduceDIte]
  exact γ.pow_mul_map_eq_of_mul_map_eq hI f
    ((mem_map_span_singleton_iff hI f).mp hz).choose_spec n

/-- **Extension of divided powers along a principal ideal**
([Stacks Lemma 07H1(1)](https://stacks.math.columbia.edu/tag/07H1)): if `I = Ideal.span {x}`, then
any `γ : DividedPowers I` extends uniquely along any ring homomorphism `f : A →+* B` to a divided
power structure on `I.map f`, sending `b * f x` to `b ^ n * f (γ.dpow n x)`. -/
noncomputable def extendSpanSingleton (γ : DividedPowers I) {x : A}
    (hI : I = Ideal.span {x}) (f : A →+* B) : DividedPowers (I.map f) :=
  have hx : x ∈ I := hI ▸ Ideal.mem_span_singleton_self x
  { dpow := γ.spanSingletonDpowAux hI f
    dpow_null := fun {_ _} hz ↦ by simp [spanSingletonDpowAux, hz]
    dpow_zero := fun {_} hz ↦ by
      obtain ⟨b, rfl⟩ := (mem_map_span_singleton_iff hI f).mp hz
      rw [γ.spanSingletonDpowAux_mul_map hI f 0 b, pow_zero, γ.dpow_zero hx, map_one, one_mul]
    dpow_one := fun {_} hz ↦ by
      obtain ⟨b, rfl⟩ := (mem_map_span_singleton_iff hI f).mp hz
      rw [γ.spanSingletonDpowAux_mul_map hI f 1 b, pow_one, γ.dpow_one hx]
    dpow_mem := fun {n _} hn hz ↦ by
      obtain ⟨b, rfl⟩ := (mem_map_span_singleton_iff hI f).mp hz
      rw [γ.spanSingletonDpowAux_mul_map hI f n b]
      exact Ideal.mul_mem_left _ (b ^ n) (Ideal.mem_map_of_mem f (γ.dpow_mem hn hx))
    dpow_add := fun {n _ _} hz₁ hz₂ ↦ by
      obtain ⟨b₁, rfl⟩ := (mem_map_span_singleton_iff hI f).mp hz₁
      obtain ⟨b₂, rfl⟩ := (mem_map_span_singleton_iff hI f).mp hz₂
      rw [← add_mul, γ.spanSingletonDpowAux_mul_map hI f n (b₁ + b₂),
        (Commute.all b₁ b₂).add_pow', sum_mul]
      refine sum_congr rfl fun k hk ↦ ?_
      rw [γ.spanSingletonDpowAux_mul_map hI f k.1 b₁, γ.spanSingletonDpowAux_mul_map hI f k.2 b₂,
        nsmul_eq_mul]
      have hmul : f (γ.dpow k.1 x) * f (γ.dpow k.2 x) =
          (n.choose k.1 : B) * f (γ.dpow n x) := by
        rw [← map_mul, γ.mul_dpow hx, mem_antidiagonal.mp hk, map_mul, map_natCast]
      calc (n.choose k.1 : B) * (b₁ ^ k.1 * b₂ ^ k.2) * f (γ.dpow n x)
          = b₁ ^ k.1 * b₂ ^ k.2 * ((n.choose k.1 : B) * f (γ.dpow n x)) := by ring
        _ = b₁ ^ k.1 * f (γ.dpow k.1 x) * (b₂ ^ k.2 * f (γ.dpow k.2 x)) := by rw [← hmul]; ring
    dpow_mul := fun {n c _} hz ↦ by
      obtain ⟨b, rfl⟩ := (mem_map_span_singleton_iff hI f).mp hz
      rw [← mul_assoc, γ.spanSingletonDpowAux_mul_map hI f n (c * b),
        γ.spanSingletonDpowAux_mul_map hI f n b, mul_pow, mul_assoc]
    mul_dpow := fun {m n _} hz ↦ by
      obtain ⟨b, rfl⟩ := (mem_map_span_singleton_iff hI f).mp hz
      simp only [γ.spanSingletonDpowAux_mul_map hI f _ b]
      calc b ^ m * f (γ.dpow m x) * (b ^ n * f (γ.dpow n x))
          = b ^ (m + n) * f (γ.dpow m x * γ.dpow n x) := by rw [pow_add, map_mul]; ring
        _ = (m + n).choose m * (b ^ (m + n) * f (γ.dpow (m + n) x)) := by
            rw [γ.mul_dpow hx, map_mul, map_natCast]; ring
    dpow_comp := fun {m n _} hn hz ↦ by
      obtain ⟨b, rfl⟩ := (mem_map_span_singleton_iff hI f).mp hz
      have hmem : γ.dpow n x ∈ Ideal.span {x} := hI ▸ γ.dpow_mem hn hx
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
      rw [γ.spanSingletonDpowAux_mul_map hI f n b, γ.spanSingletonDpowAux_mul_map hI f (m * n) b,
        show b ^ n * f (γ.dpow n x) = (b ^ n * f r) * f x by rw [← hr, map_mul, mul_assoc],
        γ.spanSingletonDpowAux_mul_map hI f m (b ^ n * f r)]
      calc (b ^ n * f r) ^ m * f (γ.dpow m x)
          = b ^ (m * n) * f (r ^ m * γ.dpow m x) := by
            rw [mul_pow, ← pow_mul, mul_comm n m, map_mul, map_pow, mul_assoc]
        _ = b ^ (m * n) * f (γ.dpow m (γ.dpow n x)) := by rw [← γ.dpow_mul hx, hr]
        _ = uniformBell m n * (b ^ (m * n) * f (γ.dpow (m * n) x)) := by
            rw [γ.dpow_comp hn hx, map_mul, map_natCast]; ring }

@[simp]
theorem extendSpanSingleton_dpow_mul_map (γ : DividedPowers I) {x : A}
    (hI : I = Ideal.span {x}) (f : A →+* B) (n : ℕ) (b : B) :
    (γ.extendSpanSingleton hI f).dpow n (b * f x) = b ^ n * f (γ.dpow n x) :=
  γ.spanSingletonDpowAux_mul_map hI f n b

theorem isDPMorphism_extendSpanSingleton (γ : DividedPowers I) {x : A}
    (hI : I = Ideal.span {x}) (f : A →+* B) :
    IsDPMorphism γ (γ.extendSpanSingleton hI f) f := by
  have hx : x ∈ I := hI ▸ Ideal.mem_span_singleton_self x
  refine ⟨le_rfl, fun {n} a ha ↦ ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp (hI ▸ ha)
  rw [map_mul, γ.extendSpanSingleton_dpow_mul_map hI f n (f r), γ.dpow_mul hx, map_mul, map_pow]

theorem eq_extendSpanSingleton_iff_isDPMorphism (γ : DividedPowers I) {x : A}
    (hI : I = Ideal.span {x}) (f : A →+* B) (θ : DividedPowers (I.map f)) :
    θ = γ.extendSpanSingleton hI f ↔ IsDPMorphism γ θ f :=
  ⟨fun h ↦ h ▸ γ.isDPMorphism_extendSpanSingleton hI f,
    fun hθ ↦ γ.eq_of_isDPMorphism_map f hθ (γ.isDPMorphism_extendSpanSingleton hI f)⟩

/-- **Universal property of principal-ideal divided power extension**: a ring homomorphism
`g : B →+* C` is a PD morphism from `(I.map f, γ.extendSpanSingleton hI f)` to `(K, κ)` if and only
if `g.comp f` is a PD morphism from `(I, γ)` to `(K, κ)`. -/
theorem isDPMorphism_extendSpanSingleton_iff {C : Type*} [CommSemiring C] {K : Ideal C}
    (γ : DividedPowers I) {x : A} (hI : I = Ideal.span {x}) (f : A →+* B)
    (κ : DividedPowers K) (g : B →+* C) :
    IsDPMorphism (γ.extendSpanSingleton hI f) κ g ↔ IsDPMorphism γ κ (g.comp f) :=
  ⟨fun hg ↦ IsDPMorphism.comp κ hg (γ.isDPMorphism_extendSpanSingleton hI f),
    fun hcomp ↦ IsDPMorphism.of_comp γ (γ.extendSpanSingleton hI f) κ f g rfl
      (γ.isDPMorphism_extendSpanSingleton hI f) hcomp⟩

/-- `DividedPowers.extendSpanSingleton` is independent of the chosen principal generator of `I`. -/
theorem extendSpanSingleton_congr (γ : DividedPowers I) {x₁ x₂ : A}
    (hI₁ : I = Ideal.span {x₁}) (hI₂ : I = Ideal.span {x₂}) (f : A →+* B) :
    γ.extendSpanSingleton hI₁ f = γ.extendSpanSingleton hI₂ f :=
  γ.eq_of_isDPMorphism_map f
    (γ.isDPMorphism_extendSpanSingleton hI₁ f) (γ.isDPMorphism_extendSpanSingleton hI₂ f)

end PrincipalIdeal

/-! ### Multinomial coefficient formula on scalar extensions and substitution invariance -/

section ScalarExtendCoeff

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A}

/-- The multinomial divided-power candidate
`∑ e ∈ piAntidiag univ n, ∏ i, b i ^ e i * f (γ.dpow (e i) (x i))` for the `n`-th divided power of
`∑ i, b i * f (x i)` along `f : A →+* B`. -/
noncomputable def scalarExtendCoeff (γ : DividedPowers I) (f : A →+* B) (n : ℕ)
    {ι : Type*} [Fintype ι] (b : ι → B) (x : ι → A) : B :=
  open scoped Classical in
  ∑ e ∈ piAntidiag univ n, ∏ i, b i ^ e i * f (γ.dpow (e i) (x i))

theorem scalarExtendCoeff_eq_sum_piAntidiag (γ : DividedPowers I) (f : A →+* B) (n : ℕ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → B) (x : ι → A) :
    γ.scalarExtendCoeff f n b x =
      ∑ e ∈ piAntidiag univ n, ∏ i, b i ^ e i * f (γ.dpow (e i) (x i)) := by
  unfold scalarExtendCoeff
  congr 1
  ext e
  simp [mem_piAntidiag]

/-- Any divided power structure `θ` on `I.map f` compatible with `(I, γ)` evaluates on
`∑ i, b i * f (x i)` via `γ.scalarExtendCoeff f n b x`. -/
theorem dpow_sum_mul_map_eq_scalarExtendCoeff (γ : DividedPowers I) (f : A →+* B)
    {θ : DividedPowers (I.map f)} (hf : IsDPMorphism γ θ f) (n : ℕ)
    {ι : Type*} [Fintype ι] (b : ι → B) {x : ι → A} (hx : ∀ i, x i ∈ I) :
    θ.dpow n (∑ i, b i * f (x i)) = γ.scalarExtendCoeff f n b x := by
  classical
  rw [γ.scalarExtendCoeff_eq_sum_piAntidiag,
    θ.dpow_sum_piAntidiag (fun i _ ↦ Ideal.mul_mem_left _ (b i) (Ideal.mem_map_of_mem f (hx i)))]
  refine sum_congr rfl fun e _ ↦ prod_congr rfl fun i _ ↦ ?_
  rw [θ.dpow_mul (Ideal.mem_map_of_mem f (hx i)), hf.dpow_comp (x i) (hx i)]

@[simp]
theorem scalarExtendCoeff_zero_deg (γ : DividedPowers I) (f : A →+* B)
    {ι : Type*} [Fintype ι] (b : ι → B) {x : ι → A} (hx : ∀ i, x i ∈ I) :
    γ.scalarExtendCoeff f 0 b x = 1 := by
  classical
  rw [γ.scalarExtendCoeff_eq_sum_piAntidiag, piAntidiag_zero, sum_singleton]
  exact prod_eq_one fun i _ ↦ by simp [γ.dpow_zero (hx i)]

theorem scalarExtendCoeff_one_deg (γ : DividedPowers I) (f : A →+* B)
    {ι : Type*} [Fintype ι] (b : ι → B) {x : ι → A} (hx : ∀ i, x i ∈ I) :
    γ.scalarExtendCoeff f 1 b x = ∑ j, b j * f (x j) := by
  classical
  rw [γ.scalarExtendCoeff_eq_sum_piAntidiag]
  have h1 : piAntidiag (univ : Finset ι) 1 = univ.image (fun j ↦ Pi.single j 1) := by
    ext e
    simp only [mem_piAntidiag, mem_univ, implies_true, and_true, mem_image, true_and]
    refine ⟨fun he ↦ ?_, by rintro ⟨j, rfl⟩; simp⟩
    obtain ⟨j, hj⟩ : ∃ j, e j ≠ 0 := by by_contra! h0; simp [h0] at he
    refine ⟨j, funext fun i ↦ ?_⟩
    by_cases hij : i = j
    · subst hij
      have hle : e i ≤ ∑ k, e k := single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
      rw [he] at hle; rw [Pi.single_eq_same]; omega
    · have hpair : e i + e j ≤ ∑ k, e k := by
        rw [← sum_pair hij]; exact sum_le_sum_of_subset (subset_univ _)
      rw [he] at hpair; rw [Pi.single_eq_of_ne hij]; omega
  rw [h1, sum_image fun i _ j _ hij ↦ by
    by_contra hne
    simpa [Pi.single_eq_same, Pi.single_eq_of_ne hne] using congr_fun hij i]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [prod_eq_single j]
  · rw [Pi.single_eq_same, pow_one, γ.dpow_one (hx j)]
  · intro i _ hij; rw [Pi.single_eq_of_ne hij, pow_zero, γ.dpow_zero (hx i), map_one, mul_one]
  · exact fun hj ↦ absurd (mem_univ j) hj

theorem scalarExtendCoeff_mem (γ : DividedPowers I) (f : A →+* B) {n : ℕ} (hn : n ≠ 0)
    {ι : Type*} [Fintype ι] (b : ι → B) {x : ι → A} (hx : ∀ i, x i ∈ I) :
    γ.scalarExtendCoeff f n b x ∈ I.map f := by
  classical
  rw [γ.scalarExtendCoeff_eq_sum_piAntidiag]
  refine Submodule.sum_mem (I.map f) fun e he ↦ ?_
  have hsum : ∑ i, e i = n := (mem_piAntidiag.mp he).1
  obtain ⟨j, hj⟩ : ∃ j, e j ≠ 0 := by by_contra! h0; simp [h0] at hsum; exact hn hsum.symm
  rw [← mul_prod_erase univ _ (mem_univ j)]
  exact Ideal.mul_mem_right _ _
    (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem f (γ.dpow_mem hj (hx j))))

theorem scalarExtendCoeff_unique (γ : DividedPowers I) (f : A →+* B) (n : ℕ)
    {ι : Type*} [Unique ι] (b : ι → B) (x : ι → A) :
    γ.scalarExtendCoeff f n b x = b default ^ n * f (γ.dpow n (x default)) := by
  classical
  rw [γ.scalarExtendCoeff_eq_sum_piAntidiag, sum_eq_single (fun _ ↦ n)]
  · rw [Fintype.prod_unique]
  · intro e he hne
    refine absurd (funext fun i ↦ ?_) hne
    rw [Unique.eq_default i]
    have hsum : ∑ j, e j = n := (mem_piAntidiag.mp he).1
    rwa [Fintype.sum_unique] at hsum
  · exact fun hn ↦ absurd (mem_piAntidiag.mpr ⟨by simp, fun _ _ ↦ mem_univ _⟩) hn

theorem scalarExtendCoeff_mul_left (γ : DividedPowers I) (f : A →+* B) (n : ℕ) (c : B)
    {ι : Type*} [Fintype ι] (b : ι → B) (x : ι → A) :
    γ.scalarExtendCoeff f n (fun i ↦ c * b i) x = c ^ n * γ.scalarExtendCoeff f n b x := by
  classical
  rw [γ.scalarExtendCoeff_eq_sum_piAntidiag, γ.scalarExtendCoeff_eq_sum_piAntidiag, mul_sum]
  refine sum_congr rfl fun e he ↦ ?_
  calc ∏ i, (c * b i) ^ e i * f (γ.dpow (e i) (x i))
      = (∏ i, c ^ e i) * ∏ i, b i ^ e i * f (γ.dpow (e i) (x i)) := by
        rw [← prod_mul_distrib]; exact prod_congr rfl fun _ _ ↦ by rw [mul_pow, mul_assoc]
    _ = c ^ n * ∏ i, b i ^ e i * f (γ.dpow (e i) (x i)) := by
        rw [prod_pow_eq_pow_sum, (mem_piAntidiag.mp he).1]

theorem scalarExtendCoeff_sumElim (γ : DividedPowers I) (f : A →+* B) (n : ℕ)
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (b₁ : ι₁ → B) (b₂ : ι₂ → B) (x₁ : ι₁ → A) (x₂ : ι₂ → A) :
    γ.scalarExtendCoeff f n (Sum.elim b₁ b₂) (Sum.elim x₁ x₂) =
      ∑ k ∈ antidiagonal n,
        γ.scalarExtendCoeff f k.1 b₁ x₁ * γ.scalarExtendCoeff f k.2 b₂ x₂ := by
  classical
  simp_rw [γ.scalarExtendCoeff_eq_sum_piAntidiag, sum_mul_sum, ← sum_product']
  rw [sum_sigma']
  refine (sum_bij' (fun s _ ↦ Sum.elim s.2.1 s.2.2)
    (fun e _ ↦ ⟨(∑ i, e (Sum.inl i), ∑ j, e (Sum.inr j)), (e ∘ Sum.inl, e ∘ Sum.inr)⟩)
    (fun s hs ↦ ?_) (fun e he ↦ ?_) (fun s hs ↦ ?_)
    (fun _ _ ↦ by ext (_ | _) <;> rfl) (fun _ _ ↦ by rw [Fintype.prod_sum_type]; rfl)).symm
  · rcases mem_sigma.mp hs with ⟨hk, he12⟩
    rcases mem_product.mp he12 with ⟨he1, he2⟩
    refine mem_piAntidiag.mpr ⟨?_, fun _ _ ↦ mem_univ _⟩
    rw [Fintype.sum_sum_type]
    simp [(mem_piAntidiag.mp he1).1, (mem_piAntidiag.mp he2).1, mem_antidiagonal.mp hk]
  · refine mem_sigma.mpr ⟨?_, mem_product.mpr
      ⟨mem_piAntidiag.mpr ⟨rfl, fun _ _ ↦ mem_univ _⟩,
       mem_piAntidiag.mpr ⟨rfl, fun _ _ ↦ mem_univ _⟩⟩⟩
    rw [mem_antidiagonal, ← Fintype.sum_sum_type]
    exact (mem_piAntidiag.mp he).1
  · rcases mem_sigma.mp hs with ⟨_, he12⟩
    rcases mem_product.mp he12 with ⟨he1, he2⟩
    exact Sigma.ext (Prod.ext (mem_piAntidiag.mp he1).1 (mem_piAntidiag.mp he2).1)
      (heq_of_eq (Prod.ext rfl rfl))

private theorem piAntidiag_prod_sum {ι κ R : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] [CommSemiring R] (n : ℕ) (Φ : ι → κ → ℕ → R) :
    (∑ e ∈ piAntidiag univ n, ∏ i : ι, ∑ r ∈ piAntidiag univ (e i), ∏ j : κ, Φ i j (r j)) =
      ∑ m ∈ piAntidiag (univ : Finset (ι × κ)) n, ∏ p : ι × κ, Φ p.1 p.2 (m p) := by
  simp_rw [prod_univ_sum, sum_sigma']
  refine sum_bij' (fun s _ p ↦ s.2 p.1 p.2)
    (fun m _ ↦ ⟨fun i ↦ ∑ j, m (i, j), fun i j ↦ m (i, j)⟩)
    (fun s hs ↦ ?_) (fun m hm ↦ ?_) (fun s hs ↦ ?_) (fun _ _ ↦ rfl)
    (fun s _ ↦ (Fintype.prod_prod_type fun p : ι × κ ↦ Φ p.1 p.2 (s.2 p.1 p.2)).symm)
  · rcases mem_sigma.mp hs with ⟨he, hr⟩
    refine mem_piAntidiag.mpr ⟨?_, fun _ _ ↦ mem_univ _⟩
    rw [Fintype.sum_prod_type]
    have hr_sum : ∀ i, ∑ j, s.2 i j = s.1 i := fun i ↦
      (mem_piAntidiag.mp (Fintype.mem_piFinset.mp hr i)).1
    simp_rw [hr_sum]
    exact (mem_piAntidiag.mp he).1
  · refine mem_sigma.mpr ⟨?_, Fintype.mem_piFinset.mpr fun _ ↦
      mem_piAntidiag.mpr ⟨rfl, fun _ _ ↦ mem_univ _⟩⟩
    refine mem_piAntidiag.mpr ⟨?_, fun _ _ ↦ mem_univ _⟩
    rw [← Fintype.sum_prod_type]
    exact (mem_piAntidiag.mp hm).1
  · rcases mem_sigma.mp hs with ⟨_, hr⟩
    exact Sigma.ext (funext fun i ↦ (mem_piAntidiag.mp (Fintype.mem_piFinset.mp hr i)).1)
      (heq_of_eq rfl)

private theorem scalarExtendCoeff_row_factor (γ : DividedPowers I) (f : A →+* B)
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    {b : ι → B} {x : ι → A} (hx : ∀ i, x i ∈ I) {c : κ → B} {a : ι → κ → A}
    (hb : ∀ i, b i = ∑ j, f (a i j) * c j) (i : ι) (k : ℕ) :
    b i ^ k * f (γ.dpow k (x i)) =
      ∑ r ∈ piAntidiag univ k, ∏ j : κ, c j ^ r j * f (γ.dpow (r j) (a i j * x i)) := by
  rw [hb i, sum_pow_eq_sum_piAntidiag, sum_mul]
  refine sum_congr rfl fun r hr ↦ ?_
  have hmult : (multinomial univ r : B) * f (γ.dpow k (x i)) =
      ∏ j : κ, f (γ.dpow (r j) (x i)) := by
    rw [← (mem_piAntidiag.mp hr).1, ← map_natCast f, ← map_mul, ← γ.prod_dpow (hx i), map_prod]
  calc (multinomial univ r : B) * (∏ j, (f (a i j) * c j) ^ r j) * f (γ.dpow k (x i))
      = (∏ j, (f (a i j) * c j) ^ r j) * ∏ j, f (γ.dpow (r j) (x i)) := by rw [← hmult]; ring
    _ = ∏ j, c j ^ r j * f (γ.dpow (r j) (a i j * x i)) := by
        rw [← prod_mul_distrib]
        exact prod_congr rfl fun j _ ↦ by rw [mul_pow, γ.dpow_mul (hx i), map_mul, map_pow]; ring

private theorem scalarExtendCoeff_col_factor (γ : DividedPowers I) (f : A →+* B)
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {x : ι → A} (hx : ∀ i, x i ∈ I) {c : κ → B} {y : κ → A} {a : ι → κ → A}
    (hy_eq : ∀ j, y j = ∑ i, a i j * x i) (j : κ) (k : ℕ) :
    c j ^ k * f (γ.dpow k (y j)) =
      ∑ q ∈ piAntidiag univ k, ∏ i : ι, c j ^ q i * f (γ.dpow (q i) (a i j * x i)) := by
  rw [hy_eq j, γ.dpow_sum_piAntidiag (fun i _ ↦ I.mul_mem_left (a i j) (hx i)), map_sum, mul_sum]
  refine sum_congr rfl fun q hq ↦ ?_
  rw [show c j ^ k = ∏ i : ι, c j ^ q i by rw [prod_pow_eq_pow_sum, (mem_piAntidiag.mp hq).1],
    map_prod, ← prod_mul_distrib]

/-- **Substitution invariance of `scalarExtendCoeff`**
([Stacks Lemma 07H1(2)](https://stacks.math.columbia.edu/tag/07H1)): if
`b i = ∑ j, f (a i j) * c j` and `y j = ∑ i, a i j * x i` with `x i ∈ I`, then
`γ.scalarExtendCoeff f n b x = γ.scalarExtendCoeff f n c y`. -/
theorem scalarExtendCoeff_subst (γ : DividedPowers I) (f : A →+* B) (n : ℕ)
    {ι κ : Type*} [Fintype ι] [Fintype κ] {b : ι → B} {x : ι → A} (hx : ∀ i, x i ∈ I)
    {c : κ → B} {y : κ → A} {a : ι → κ → A}
    (hb : ∀ i, b i = ∑ j, f (a i j) * c j) (hy_eq : ∀ j, y j = ∑ i, a i j * x i) :
    γ.scalarExtendCoeff f n b x = γ.scalarExtendCoeff f n c y := by
  classical
  let Φ : ι → κ → ℕ → B := fun i j k ↦ c j ^ k * f (γ.dpow k (a i j * x i))
  have hlhs : γ.scalarExtendCoeff f n b x =
      ∑ m ∈ piAntidiag (univ : Finset (ι × κ)) n, ∏ p : ι × κ, Φ p.1 p.2 (m p) := by
    rw [γ.scalarExtendCoeff_eq_sum_piAntidiag]
    simp_rw [γ.scalarExtendCoeff_row_factor f hx hb]
    exact piAntidiag_prod_sum n Φ
  have hrhs : γ.scalarExtendCoeff f n c y =
      ∑ m' ∈ piAntidiag (univ : Finset (κ × ι)) n, ∏ p' : κ × ι, Φ p'.2 p'.1 (m' p') := by
    rw [γ.scalarExtendCoeff_eq_sum_piAntidiag]
    simp_rw [γ.scalarExtendCoeff_col_factor f hx hy_eq]
    exact piAntidiag_prod_sum n (fun j i k ↦ Φ i j k)
  rw [hlhs, hrhs]
  refine sum_bij' (fun m _ ↦ m ∘ Prod.swap) (fun m' _ ↦ m' ∘ Prod.swap)
    (fun m hm ↦ mem_piAntidiag.mpr
      ⟨by simpa using (Equiv.prodComm κ ι).sum_comp m |>.trans (mem_piAntidiag.mp hm).1,
       fun _ _ ↦ mem_univ _⟩)
    (fun m' hm' ↦ mem_piAntidiag.mpr
      ⟨by simpa using (Equiv.prodComm ι κ).sum_comp m' |>.trans (mem_piAntidiag.mp hm').1,
       fun _ _ ↦ mem_univ _⟩)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun m _ ↦ ((Equiv.prodComm κ ι).prod_comp fun p : ι × κ ↦ Φ p.1 p.2 (m p)).symm)

end ScalarExtendCoeff

/-! ### Extension of divided powers along a flat algebra -/

section FlatExtend

variable {A : Type*} [CommRing A] {I : Ideal A}

/-- **Presentation independence over a flat algebra**
([Stacks Lemma 07H1(2)](https://stacks.math.columbia.edu/tag/07H1)): when `B` is flat over `A`,
`γ.scalarExtendCoeff (algebraMap A B) n b x` depends only on `∑ i, b i * algebraMap A B (x i)` for
families `x i ∈ I`. -/
theorem scalarExtendCoeff_eq_of_sum_eq (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] (n : ℕ) {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (b : ι → B) {x : ι → A} (hx : ∀ i, x i ∈ I) (b' : ι' → B) {x' : ι' → A} (hx' : ∀ i', x' i' ∈ I)
    (hsum : ∑ i, b i * algebraMap A B (x i) = ∑ i', b' i' * algebraMap A B (x' i')) :
    γ.scalarExtendCoeff (algebraMap A B) n b x = γ.scalarExtendCoeff (algebraMap A B) n b' x' := by
  have hrel : ∑ s : ι ⊕ ι', Sum.elim x (-x') s • Sum.elim b b' s = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, Algebra.smul_def, map_neg, neg_mul,
      sum_neg_distrib]
    rw [sum_congr rfl fun i _ ↦ mul_comm (algebraMap A B (x i)) (b i),
      sum_congr rfl fun i' _ ↦ mul_comm (algebraMap A B (x' i')) (b' i'), hsum, add_neg_cancel]
  obtain ⟨k, a, c, hc, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  let y : Fin k → A := fun j ↦ ∑ i : ι, a (Sum.inl i) j * x i
  have hb_eq (i : ι) : b i = ∑ j : Fin k, algebraMap A B (a (Sum.inl i) j) * c j := by
    simpa [Algebra.smul_def] using hc (Sum.inl i)
  have hb'_eq (i' : ι') : b' i' = ∑ j : Fin k, algebraMap A B (a (Sum.inr i') j) * c j := by
    simpa [Algebra.smul_def] using hc (Sum.inr i')
  have hy'_eq (j : Fin k) : y j = ∑ i' : ι', a (Sum.inr i') j * x' i' := by
    have haj := ha j
    rw [Fintype.sum_sum_type] at haj
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, sum_neg_distrib] at haj
    calc y j = ∑ i : ι, x i * a (Sum.inl i) j := sum_congr rfl fun _ _ ↦ mul_comm _ _
      _ = ∑ i' : ι', x' i' * a (Sum.inr i') j :=
        eq_of_sub_eq_zero (by rwa [← sub_eq_add_neg] at haj)
      _ = ∑ i' : ι', a (Sum.inr i') j * x' i' := sum_congr rfl fun _ _ ↦ mul_comm _ _
  exact (γ.scalarExtendCoeff_subst (algebraMap A B) n hx hb_eq (fun _ ↦ rfl)).trans
    (γ.scalarExtendCoeff_subst (algebraMap A B) n hx' hb'_eq hy'_eq).symm

private theorem exists_fin_presentation {C D : Type*} [CommSemiring C] [CommSemiring D]
    {J : Ideal C} (f : C →+* D) {z : D} (hz : z ∈ J.map f) :
    ∃ (m : ℕ) (b : Fin m → D) (x : Fin m → C), (∀ i, x i ∈ J) ∧ z = ∑ i, b i * f (x i) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨a, ha, rfl⟩; exact ⟨1, fun _ ↦ 1, fun _ ↦ a, fun _ ↦ ha, by simp⟩
  · exact ⟨0, Fin.elim0, Fin.elim0, fun i ↦ i.elim0, by simp⟩
  · rintro _ _ _ _ ⟨m₁, b₁, x₁, hx₁, rfl⟩ ⟨m₂, b₂, x₂, hx₂, rfl⟩
    refine ⟨m₁ + m₂, Fin.append b₁ b₂, Fin.append x₁ x₂, fun i ↦ i.addCases
      (fun i₁ ↦ by simpa [Fin.append_left] using hx₁ i₁)
      (fun i₂ ↦ by simpa [Fin.append_right] using hx₂ i₂), ?_⟩
    rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]
  · rintro c _ _ ⟨m, b, x, hx, rfl⟩
    refine ⟨m, fun i ↦ c * b i, x, hx, ?_⟩
    rw [smul_eq_mul, mul_sum]; exact sum_congr rfl fun i _ ↦ (mul_assoc c (b i) (f (x i))).symm

private noncomputable def flatDpowAux (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] (n : ℕ) (z : B) : B :=
  open scoped Classical in
  if hz : z ∈ I.map (algebraMap A B) then
    let p := exists_fin_presentation (algebraMap A B) hz
    γ.scalarExtendCoeff (algebraMap A B) n p.choose_spec.choose p.choose_spec.choose_spec.choose
  else 0

private theorem flatDpowAux_sum (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] (n : ℕ)
    {ι : Type*} [Fintype ι] (b : ι → B) {x : ι → A} (hx : ∀ i, x i ∈ I) :
    γ.flatDpowAux B n (∑ i, b i * algebraMap A B (x i)) =
      γ.scalarExtendCoeff (algebraMap A B) n b x := by
  have hz : ∑ i, b i * algebraMap A B (x i) ∈ I.map (algebraMap A B) :=
    Submodule.sum_mem (I.map (algebraMap A B)) fun i _ ↦
      Ideal.mul_mem_left _ (b i) (Ideal.mem_map_of_mem (algebraMap A B) (hx i))
  simp only [flatDpowAux, hz, ↓reduceDIte]
  have hp := (exists_fin_presentation (algebraMap A B) hz).choose_spec.choose_spec.choose_spec
  exact γ.scalarExtendCoeff_eq_of_sum_eq B n _ hp.1 b hx hp.2.symm

/-- The additive divided-power candidate on `I.map (algebraMap A B)` for a flat `A`-algebra `B`. -/
noncomputable def flatAdditivePowers (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] : TauCeti.AdditivePowers (I.map (algebraMap A B)) where
  dpow := γ.flatDpowAux B
  dpow_null {n z} hz := by simp [flatDpowAux, hz]
  dpow_zero {z} hz := by
    obtain ⟨m, b, x, hx, rfl⟩ := exists_fin_presentation (algebraMap A B) hz
    rw [γ.flatDpowAux_sum B 0 b hx, γ.scalarExtendCoeff_zero_deg (algebraMap A B) b hx]
  dpow_one {z} hz := by
    obtain ⟨m, b, x, hx, rfl⟩ := exists_fin_presentation (algebraMap A B) hz
    rw [γ.flatDpowAux_sum B 1 b hx, γ.scalarExtendCoeff_one_deg (algebraMap A B) b hx]
  dpow_mem {n z} hn hz := by
    obtain ⟨m, b, x, hx, rfl⟩ := exists_fin_presentation (algebraMap A B) hz
    rw [γ.flatDpowAux_sum B n b hx]; exact γ.scalarExtendCoeff_mem (algebraMap A B) hn b hx
  dpow_add {n z₁ z₂} hz₁ hz₂ := by
    obtain ⟨m₁, b₁, x₁, hx₁, rfl⟩ := exists_fin_presentation (algebraMap A B) hz₁
    obtain ⟨m₂, b₂, x₂, hx₂, rfl⟩ := exists_fin_presentation (algebraMap A B) hz₂
    have hsum : (∑ i, b₁ i * algebraMap A B (x₁ i)) + ∑ j, b₂ j * algebraMap A B (x₂ j) =
        ∑ s : Fin m₁ ⊕ Fin m₂, Sum.elim b₁ b₂ s * algebraMap A B (Sum.elim x₁ x₂ s) := by
      rw [Fintype.sum_sum_type]; rfl
    have hx₁₂ : ∀ s : Fin m₁ ⊕ Fin m₂, Sum.elim x₁ x₂ s ∈ I := by
      rintro (i | j); exacts [hx₁ i, hx₂ j]
    rw [hsum, γ.flatDpowAux_sum B n (Sum.elim b₁ b₂) hx₁₂, γ.scalarExtendCoeff_sumElim]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [γ.flatDpowAux_sum B k.1 b₁ hx₁, γ.flatDpowAux_sum B k.2 b₂ hx₂]
  dpow_mul {n c z} hz := by
    obtain ⟨m, b, x, hx, rfl⟩ := exists_fin_presentation (algebraMap A B) hz
    have hmul : c * ∑ i, b i * algebraMap A B (x i) = ∑ i, (c * b i) * algebraMap A B (x i) := by
      rw [mul_sum]; exact sum_congr rfl fun i _ ↦ (mul_assoc c (b i) _).symm
    rw [hmul, γ.flatDpowAux_sum B n (fun i ↦ c * b i) hx,
      γ.flatDpowAux_sum B n b hx, γ.scalarExtendCoeff_mul_left]

theorem flatAdditivePowers_dpow_sum (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] (n : ℕ)
    {ι : Type*} [Fintype ι] (b : ι → B) {x : ι → A} (hx : ∀ i, x i ∈ I) :
    (γ.flatAdditivePowers B).dpow n (∑ i, b i * algebraMap A B (x i)) =
      γ.scalarExtendCoeff (algebraMap A B) n b x :=
  γ.flatDpowAux_sum B n b hx

theorem flatAdditivePowers_dpow_mul_algebraMap (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] (n : ℕ) (b : B) {x : A} (hx : x ∈ I) :
    (γ.flatAdditivePowers B).dpow n (b * algebraMap A B x) =
      b ^ n * algebraMap A B (γ.dpow n x) := by
  simpa [γ.scalarExtendCoeff_unique] using
    γ.flatAdditivePowers_dpow_sum B n (fun _ : Unit ↦ b) (x := fun _ ↦ x) (fun _ ↦ hx)

theorem flatAdditivePowers_dpow_algebraMap (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] (n : ℕ) {x : A} (hx : x ∈ I) :
    (γ.flatAdditivePowers B).dpow n (algebraMap A B x) = algebraMap A B (γ.dpow n x) := by
  simpa using γ.flatAdditivePowers_dpow_mul_algebraMap B n 1 hx

/-- **Flat extension of divided powers**
([Stacks Lemma 07H1(2)](https://stacks.math.columbia.edu/tag/07H1)): if `B` is a flat `A`-algebra,
`γ.flatExtend B` is the unique divided power structure on `I.map (algebraMap A B)` making
`algebraMap A B` a divided power morphism from `(I, γ)`. -/
noncomputable def flatExtend (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] : DividedPowers (I.map (algebraMap A B)) :=
  (γ.flatAdditivePowers B).toDividedPowers (S := (algebraMap A B) '' (I : Set A))
    (show I.map (algebraMap A B) = Ideal.span ((algebraMap A B) '' (I : Set A)) from rfl)
    (fun _ hs m n ↦ by
      rcases hs with ⟨x, hx, rfl⟩
      simp only [γ.flatAdditivePowers_dpow_algebraMap B _ hx]
      rw [← map_mul, γ.mul_dpow hx, map_mul, map_natCast])
    (fun _ hs m {n} hn ↦ by
      rcases hs with ⟨x, hx, rfl⟩
      rw [γ.flatAdditivePowers_dpow_algebraMap B n hx,
        γ.flatAdditivePowers_dpow_algebraMap B m (γ.dpow_mem hn hx),
        γ.flatAdditivePowers_dpow_algebraMap B (m * n) hx, γ.dpow_comp hn hx, map_mul, map_natCast])

@[simp]
theorem flatExtend_dpow_eq_flatAdditivePowers (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] :
    (γ.flatExtend B).dpow = (γ.flatAdditivePowers B).dpow := by
  simp [flatExtend]

theorem flatExtend_dpow_sum (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] (n : ℕ)
    {ι : Type*} [Fintype ι] (b : ι → B) {x : ι → A} (hx : ∀ i, x i ∈ I) :
    (γ.flatExtend B).dpow n (∑ i, b i * algebraMap A B (x i)) =
      γ.scalarExtendCoeff (algebraMap A B) n b x := by
  rw [flatExtend_dpow_eq_flatAdditivePowers]; exact γ.flatAdditivePowers_dpow_sum B n b hx

theorem flatExtend_dpow_mul_algebraMap (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] (n : ℕ) (b : B) {x : A} (hx : x ∈ I) :
    (γ.flatExtend B).dpow n (b * algebraMap A B x) = b ^ n * algebraMap A B (γ.dpow n x) := by
  rw [flatExtend_dpow_eq_flatAdditivePowers]
  exact γ.flatAdditivePowers_dpow_mul_algebraMap B n b hx

@[simp]
theorem flatExtend_dpow_algebraMap (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] (n : ℕ) {x : A} (hx : x ∈ I) :
    (γ.flatExtend B).dpow n (algebraMap A B x) = algebraMap A B (γ.dpow n x) := by
  rw [flatExtend_dpow_eq_flatAdditivePowers]; exact γ.flatAdditivePowers_dpow_algebraMap B n hx

theorem isDPMorphism_algebraMap_flatExtend (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] : IsDPMorphism γ (γ.flatExtend B) (algebraMap A B) :=
  ⟨le_rfl, fun {n} _ hx ↦ γ.flatExtend_dpow_algebraMap B n hx⟩

theorem eq_flatExtend_iff_isDPMorphism (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] (θ : DividedPowers (I.map (algebraMap A B))) :
    θ = γ.flatExtend B ↔ IsDPMorphism γ θ (algebraMap A B) :=
  ⟨fun h ↦ h ▸ γ.isDPMorphism_algebraMap_flatExtend B,
    fun hθ ↦ γ.eq_of_isDPMorphism_map (algebraMap A B) hθ
      (γ.isDPMorphism_algebraMap_flatExtend B)⟩

/-- **Universal property of flat divided power extension**: a ring homomorphism `g : B →+* C` out
of a flat `A`-algebra `B` is a PD morphism from `(I.map (algebraMap A B), γ.flatExtend B)` to
`(K, κ)` if and only if `g.comp (algebraMap A B)` is a PD morphism from `(I, γ)` to `(K, κ)`. -/
theorem isDPMorphism_flatExtend_iff {C : Type*} [CommSemiring C] {K : Ideal C}
    (γ : DividedPowers I) (B : Type*) [CommRing B] [Algebra A B] [Module.Flat A B]
    (κ : DividedPowers K) (g : B →+* C) :
    IsDPMorphism (γ.flatExtend B) κ g ↔ IsDPMorphism γ κ (g.comp (algebraMap A B)) :=
  ⟨fun hg ↦ IsDPMorphism.comp κ hg (γ.isDPMorphism_algebraMap_flatExtend B),
    fun hcomp ↦ IsDPMorphism.of_comp γ (γ.flatExtend B) κ (algebraMap A B) g rfl
      (γ.isDPMorphism_algebraMap_flatExtend B) hcomp⟩

/-- Over a flat `A`-algebra `B` and a principal ideal `I = Ideal.span {x}`, `γ.flatExtend B` agrees
with `γ.extendSpanSingleton hI (algebraMap A B)`. -/
theorem flatExtend_eq_extendSpanSingleton (γ : DividedPowers I) (B : Type*) [CommRing B]
    [Algebra A B] [Module.Flat A B] {x : A} (hI : I = Ideal.span {x}) :
    γ.flatExtend B = γ.extendSpanSingleton hI (algebraMap A B) :=
  ((γ.eq_flatExtend_iff_isDPMorphism B _).mpr
    (γ.isDPMorphism_extendSpanSingleton hI (algebraMap A B))).symm

@[simp]
theorem flatExtend_self_dpow (γ : DividedPowers I) (n : ℕ) (x : A) :
    (γ.flatExtend A).dpow n x = γ.dpow n x := by
  by_cases hx : x ∈ I
  · simpa using γ.flatExtend_dpow_algebraMap A n hx
  · have hx' : x ∉ I.map (algebraMap A A) := by rwa [Algebra.algebraMap_self, Ideal.map_id]
    rw [(γ.flatExtend A).dpow_null hx', γ.dpow_null hx]

/-- **Transitivity of `flatExtend` along a tower of flat algebras** `A → B → C`. -/
theorem flatExtend_flatExtend_dpow (γ : DividedPowers I)
    (B : Type*) [CommRing B] [Algebra A B] [Module.Flat A B]
    (C : Type*) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Module.Flat B C] [Module.Flat A C] (n : ℕ) (z : C) :
    ((γ.flatExtend B).flatExtend C).dpow n z = (γ.flatExtend C).dpow n z := by
  have hmap : (I.map (algebraMap A B)).map (algebraMap B C) = I.map (algebraMap A C) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B C]
  by_cases hz : z ∈ I.map (algebraMap A C)
  · have hcomp : IsDPMorphism γ ((γ.flatExtend B).flatExtend C) (algebraMap A C) := by
      rw [IsScalarTower.algebraMap_eq A B C]
      exact IsDPMorphism.comp ((γ.flatExtend B).flatExtend C)
        ((γ.flatExtend B).isDPMorphism_algebraMap_flatExtend C)
        (γ.isDPMorphism_algebraMap_flatExtend B)
    have hid : IsDPMorphism (γ.flatExtend C) ((γ.flatExtend B).flatExtend C) (RingHom.id C) :=
      IsDPMorphism.of_comp γ (γ.flatExtend C) ((γ.flatExtend B).flatExtend C)
        (algebraMap A C) (RingHom.id C) rfl (γ.isDPMorphism_algebraMap_flatExtend C)
        (by simpa using hcomp)
    simpa using hid.dpow_comp z hz
  · rw [((γ.flatExtend B).flatExtend C).dpow_null (hmap.symm ▸ hz), (γ.flatExtend C).dpow_null hz]

end FlatExtend

/-! ### Localization of divided powers -/

section Localization

variable {A : Type*} [CommRing A] {I : Ideal A}

/-- **Divided powers on a localization**
([Stacks Lemma 07H1(3)](https://stacks.math.columbia.edu/tag/07H1)): for any multiplicative
submonoid `M : Submonoid A` and localization `B` (`[IsLocalization M B]`), `γ.localization M B` is
the unique divided power structure on `I.map (algebraMap A B)` making `algebraMap A B` a divided
power morphism from `(I, γ)`. -/
noncomputable def localization (γ : DividedPowers I) (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B] :
    DividedPowers (I.map (algebraMap A B)) :=
  haveI : Module.Flat A B := IsLocalization.flat B M
  γ.flatExtend B

theorem localization_eq_flatExtend (γ : DividedPowers I) (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B] [Module.Flat A B] :
    γ.localization M B = γ.flatExtend B := by
  unfold localization; rfl

theorem isDPMorphism_algebraMap_localization (γ : DividedPowers I) (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B] :
    IsDPMorphism γ (γ.localization M B) (algebraMap A B) := by
  have : Module.Flat A B := IsLocalization.flat B M
  rw [γ.localization_eq_flatExtend M B]; exact γ.isDPMorphism_algebraMap_flatExtend B

theorem eq_localization_iff_isDPMorphism (γ : DividedPowers I) (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B]
    (θ : DividedPowers (I.map (algebraMap A B))) :
    θ = γ.localization M B ↔ IsDPMorphism γ θ (algebraMap A B) := by
  have : Module.Flat A B := IsLocalization.flat B M
  rw [γ.localization_eq_flatExtend M B]; exact γ.eq_flatExtend_iff_isDPMorphism B θ

theorem isDPMorphism_localization_iff {C : Type*} [CommSemiring C] {K : Ideal C}
    (γ : DividedPowers I) (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B]
    (κ : DividedPowers K) (g : B →+* C) :
    IsDPMorphism (γ.localization M B) κ g ↔ IsDPMorphism γ κ (g.comp (algebraMap A B)) := by
  have : Module.Flat A B := IsLocalization.flat B M
  rw [γ.localization_eq_flatExtend M B]; exact γ.isDPMorphism_flatExtend_iff B κ g

@[simp]
theorem localization_dpow_algebraMap (γ : DividedPowers I) (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B] (n : ℕ) {x : A} (hx : x ∈ I) :
    (γ.localization M B).dpow n (algebraMap A B x) = algebraMap A B (γ.dpow n x) := by
  have : Module.Flat A B := IsLocalization.flat B M
  rw [γ.localization_eq_flatExtend M B]; exact γ.flatExtend_dpow_algebraMap B n hx

/-- Explicit formula for localized divided powers on fractions:
`(γ.localization M B).dpow n (x / s) = γ.dpow n x / s ^ n` for `x ∈ I` and `s ∈ M`. -/
@[simp]
theorem localization_dpow_mk' (γ : DividedPowers I) (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B]
    (n : ℕ) {x : A} (hx : x ∈ I) (s : M) :
    (γ.localization M B).dpow n (IsLocalization.mk' B x s) =
      IsLocalization.mk' B (γ.dpow n x) (s ^ n) := by
  rw [IsLocalization.mk'_eq_mul_mk'_one x s, mul_comm,
    (γ.localization M B).dpow_mul (Ideal.mem_map_of_mem (algebraMap A B) hx),
    γ.localization_dpow_algebraMap M B n hx, ← IsLocalization.mk'_pow, one_pow, mul_comm,
    ← IsLocalization.mk'_eq_mul_mk'_one]

end Localization

end DividedPowers
