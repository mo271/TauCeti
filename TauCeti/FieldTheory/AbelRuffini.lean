/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.AbelRuffini
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.GroupTheory.Solvable

/-!
# The radical criterion for finite Galois extensions and polynomials

Mathlib's `Mathlib/FieldTheory/AbelRuffini.lean` proves one direction of the Abel–Ruffini
theorem: an element in `solvableByRad F Ω` has a minimal polynomial with solvable Galois group.
This file supplies the converse and combines both directions into the radical criterion for
finite Galois extensions and polynomials.

For a finite Galois extension `E/F` embedded by `ι : E →ₐ[F] Ω` into a field `Ω`, the Galois
group `Gal(E/F)` is solvable whenever `ι(E) ⊆ solvableByRad F Ω`, with no hypothesis on the
characteristic of `F` or on roots of unity in `Ω`. Conversely, as soon as `Ω` contains a
primitive `[E : F]`-th root of unity `ζ`, solvability of `Gal(E/F)` implies that `ι(E)` lies
in `solvableByRad F Ω`: adjoining `ζ` lands in `solvableByRad F Ω`, and descending along normal
subgroups of prime index via Kummer theory writes the compositum `ι(E)(ζ)` as a tower of
prime-degree radical extensions. In characteristic zero, every separably closed extension `Ω`
(in particular `AlgebraicClosure F`) automatically contains all roots of unity, giving the
unconditional equivalence.

Passing to splitting fields transfers the criterion to polynomials `q : F[X]` over a field of
characteristic zero: `q.Gal` is solvable if and only if every root of `q` in `Ω` lies in
`solvableByRad F Ω` (and, when `q` is irreducible, if and only if some root does). Combining
this with the full-symmetric-group criterion for prime-degree rational polynomials with two
nonreal roots shows that no root of such a polynomial of degree at least `5` is expressible by
radicals.

## Main results

* `TauCeti.isSolvable_of_forall_mem_solvableByRad`: if `ι : E →ₐ[F] Ω` lands in
  `solvableByRad F Ω`, then `Gal(E/F)` is solvable (characteristic-free).
* `TauCeti.isSolvable_iff_forall_mem_solvableByRad_of_isPrimitiveRoot`: the full equivalence
  whenever `Ω` contains a primitive `[E : F]`-th root of unity (characteristic-free).
* `TauCeti.isSolvable_iff_forall_mem_solvableByRad`: **the radical criterion for finite Galois
  extensions** in characteristic zero, into any separably closed extension `Ω`.
* `TauCeti.isSolvable_gal_iff_forall_rootSet_mem_solvableByRad`: **the radical criterion for
  polynomials** in characteristic zero.
* `TauCeti.isSolvable_gal_iff_exists_rootSet_mem_solvableByRad`: the single-root form for an
  irreducible polynomial in characteristic zero.
* `TauCeti.not_mem_solvableByRad_of_prime_degree`: an irreducible rational polynomial of prime
  degree at least `5` with two nonreal roots has no root solvable by radicals in any extension.

## References

* J. S. Milne, *Fields and Galois Theory*, v5.10, Theorem 5.34, p. 77.
-/

public section

open Polynomial IntermediateField

namespace TauCeti

/-- If `E/F` is a finite Galois extension and an `F`-embedding `ι : E →ₐ[F] Ω` lands inside
`solvableByRad F Ω`, then `Gal(E/F)` is solvable.

This direction needs no assumption on the characteristic of `F` or on roots of unity in `Ω`. -/
theorem isSolvable_of_forall_mem_solvableByRad
    (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {Ω : Type*} [Field Ω] [Algebra F Ω] (ι : E →ₐ[F] Ω)
    (h : ∀ x : E, ι x ∈ solvableByRad F Ω) :
    Group.IsSolvable (E ≃ₐ[F] E) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hsplit : (minpoly F α).IsSplittingField F E := by
    refine ⟨IsGalois.splits F α, ?_⟩
    rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← hα,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    refine Algebra.adjoin_mono ?_
    rw [Set.singleton_subset_iff, mem_rootSet]
    exact ⟨minpoly.ne_zero hint, minpoly.aeval F α⟩
  have hmin : minpoly F (ι α) = minpoly F α := minpoly.algHom_eq ι ι.injective α
  have hsol : Group.IsSolvable (minpoly F α).Gal := hmin ▸ isSolvable_gal_minpoly (h α)
  exact ((IsSplittingField.algEquiv E (minpoly F α)).autCongr.isSolvable_congr).mpr hsol

-- One Kummer step: if `H ◁ Gal(L/K)` has prime index `p` with `[L : K] ∣ N` and `K` contains a
-- primitive `N`-th root of unity and lies inside `solvableByRad F Ω`, then `fixedField H` has
-- degree `p` over `K` and also lies inside `solvableByRad F Ω`.
private theorem fixedField_mem_solvableByRad_of_index_prime
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    {L : IntermediateField F Ω} {K : IntermediateField F L}
    [FiniteDimensional K L] [IsGalois K L]
    {H : Subgroup (L ≃ₐ[K] L)} [H.Normal] (hp : H.index.Prime)
    {N : ℕ} (hN : N ≠ 0) (hdvd : Module.finrank K L ∣ N)
    {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    (hK : ∀ x : K, ((x : L) : Ω) ∈ solvableByRad F Ω) :
    Module.finrank K (IntermediateField.fixedField H) = H.index ∧
      ∀ y : IntermediateField.fixedField H, ((y : L) : Ω) ∈ solvableByRad F Ω := by
  set p := H.index
  set M : IntermediateField K L := IntermediateField.fixedField H
  have : Fact p.Prime := ⟨hp⟩
  have hMdeg : Module.finrank K M = p := by
    rw [← IsGalois.card_aut_eq_finrank K M,
      Nat.card_congr (IsGalois.normalAutEquivQuotient H).symm.toEquiv]
    exact H.index_eq_card.symm
  have : IsCyclic (M ≃ₐ[K] M) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank K M, hMdeg])
  have hp_dvd_N : p ∣ N :=
    dvd_trans ⟨Module.finrank M L, by rw [← hMdeg, Module.finrank_mul_finrank K M L]⟩ hdvd
  have hk_ne : N / p ≠ 0 :=
    Nat.div_ne_zero_iff.mpr ⟨hp.ne_zero, Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hp_dvd_N⟩
  have hζp : IsPrimitiveRoot (ζ ^ (N / p)) p := by
    have h := hζ.pow_of_dvd hk_ne (Nat.div_dvd_of_dvd hp_dvd_N)
    rwa [Nat.div_div_self hp_dvd_N hN] at h
  have hprim : (primitiveRoots (Module.finrank K M) K).Nonempty :=
    ⟨ζ ^ (N / p), (mem_primitiveRoots (hMdeg ▸ hp.pos)).mpr (hMdeg ▸ hζp)⟩
  obtain ⟨α, ⟨c, hc⟩, hαgen⟩ := exists_root_adjoin_eq_top_of_isCyclic K M hprim
  have hα_rad : ((α : L) : Ω) ∈ solvableByRad F Ω := by
    refine solvableByRad.rad_mem (n := p) hp.ne_zero ?_
    have hpow_eq : ((α : L) : Ω) ^ p = ((c : L) : Ω) := by
      have h1 : (α ^ p : M) = algebraMap K M c := by simpa [hMdeg] using hc.symm
      have h2 := congrArg (fun y : M => ((y : L) : Ω)) h1
      simpa using h2
    rw [hpow_eq]
    exact hK c
  refine ⟨hMdeg, fun y => ?_⟩
  let fM : M →+* Ω := L.val.toRingHom.comp M.val.toRingHom
  let T : IntermediateField K M :=
    ((solvableByRad F Ω).toSubfield.comap fM).toIntermediateField fun x => hK x
  have hleT : K⟮α⟯ ≤ T := IntermediateField.adjoin_simple_le_iff.mpr hα_rad
  exact hleT (hαgen ▸ (trivial : y ∈ (⊤ : IntermediateField K M)))

-- Core Kummer-tower induction: if `L/K` is finite Galois with solvable Galois group, `K` lies in
-- `solvableByRad F Ω`, and `K` contains a primitive `N`-th root of unity with `[L : K] ∣ N`,
-- then `L` lies in `solvableByRad F Ω`.
private theorem forall_mem_solvableByRad_of_isSolvable_aux
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (L : IntermediateField F Ω) {N : ℕ} (hN : N ≠ 0) :
    ∀ n : ℕ, ∀ K : IntermediateField F L,
      FiniteDimensional K L → IsGalois K L → Group.IsSolvable (L ≃ₐ[K] L) →
      Module.finrank K L = n → Module.finrank K L ∣ N →
      (∃ ζ : K, IsPrimitiveRoot ζ N) →
      (∀ x : K, ((x : L) : Ω) ∈ solvableByRad F Ω) →
      ∀ x : L, (x : Ω) ∈ solvableByRad F Ω := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro K hfin hgal hsol hdeg hdvd ⟨ζ, hζ⟩ hK
    have hpos : 0 < Module.finrank K L := Module.finrank_pos
    rcases (Nat.succ_le_of_lt hpos).eq_or_lt with h1 | hgt
    · -- `[L : K] = 1`, so `K = ⊤` and every element of `L` already lies in `K`.
      have htop : K = ⊤ := IntermediateField.finrank_eq_one_iff_eq_top.mp h1.symm
      exact fun x => hK ⟨x, htop ▸ trivial⟩
    · -- `Gal(L/K)` is nontrivial finite solvable, so it has a normal subgroup of prime index `p`.
      have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
      have : Nontrivial (L ≃ₐ[K] L) := Finite.one_lt_card_iff_nontrivial.mp (hcard ▸ hgt)
      obtain ⟨H, _, hp⟩ := Group.IsSolvable.exists_normal_index_prime (L ≃ₐ[K] L)
      set M : IntermediateField K L := IntermediateField.fixedField H
      obtain ⟨hMdeg, hM_rad⟩ := fixedField_mem_solvableByRad_of_index_prime hp hN hdvd hζ hK
      -- Descend along the strict tower step `K < M ≤ L`.
      let M' : IntermediateField F L := M.restrictScalars F
      have hfinM' : FiniteDimensional M' L := inferInstanceAs (FiniteDimensional M L)
      have hgalM' : IsGalois M' L := IsGalois.tower_top_of_isGalois K M L
      have hsolM' : Group.IsSolvable (L ≃ₐ[M'] L) :=
        M.fixingSubgroupEquiv.isSolvable_congr.mp inferInstance
      have hmul : H.index * Module.finrank M L = Module.finrank K L := by
        rw [← hMdeg]
        exact Module.finrank_mul_finrank K M L
      -- `M.restrictScalars F` shares the underlying carrier and scalar action of `M` on `L`.
      have hfin_eq : Module.finrank M' L = Module.finrank M L := rfl
      have hlt : Module.finrank M' L < n := by
        have hp2 : 2 ≤ H.index := hp.two_le
        rw [hfin_eq]
        nlinarith
      have hMdvd : Module.finrank M' L ∣ N :=
        dvd_trans ⟨H.index, by rw [hfin_eq]; linarith⟩ hdvd
      have hζM' : ∃ ξ : M', IsPrimitiveRoot ξ N :=
        ⟨algebraMap K M ζ, hζ.map_of_injective (algebraMap K M).injective⟩
      exact ih (Module.finrank M' L) hlt M' hfinM' hgalM' hsolM' rfl hMdvd hζM' hM_rad

/-- **The radical criterion for finite Galois extensions with a primitive root of unity.**
Let `E/F` be a finite Galois extension embedded by `ι : E →ₐ[F] Ω` into a field `Ω` containing a
primitive `[E : F]`-th root of unity. Then `Gal(E/F)` is solvable if and only if every element of
`ι(E)` lies in `solvableByRad F Ω`.

This characteristic-free form applies whenever `Ω` supplies the `[E : F]`-th roots of unity,
including in positive characteristic coprime to `[E : F]`. -/
theorem isSolvable_iff_forall_mem_solvableByRad_of_isPrimitiveRoot
    (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {Ω : Type*} [Field Ω] [Algebra F Ω] (ι : E →ₐ[F] Ω)
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ (Module.finrank F E)) :
    Group.IsSolvable (E ≃ₐ[F] E) ↔ ∀ x : E, ι x ∈ solvableByRad F Ω := by
  refine ⟨fun hsol => ?_, isSolvable_of_forall_mem_solvableByRad F E ι⟩
  set N := Module.finrank F E
  have hNpos : 0 < N := Module.finrank_pos
  have hζ_int : IsIntegral F ζ :=
    ⟨X ^ N - 1, monic_X_pow_sub_C 1 hNpos.ne', by simp [hζ.pow_eq_one]⟩
  have : FiniteDimensional F F⟮ζ⟯ := IntermediateField.adjoin.finiteDimensional hζ_int
  have hζ_rad : ζ ∈ solvableByRad F Ω :=
    solvableByRad.rad_mem hNpos.ne' (by rw [hζ.pow_eq_one]; exact one_mem _)
  have : FiniteDimensional F ι.fieldRange :=
    Module.Finite.equiv ι.equivFieldRange.toLinearEquiv
  -- Form the compositum `L = ι(E)(ζ)` inside `Ω` and restrict to the Galois extension `L / F(ζ)`.
  let L : IntermediateField F Ω := ι.fieldRange ⊔ F⟮ζ⟯
  let E₁ : IntermediateField F L := ι.fieldRange.restrict le_sup_left
  let K₁ : IntermediateField F L := F⟮ζ⟯.restrict le_sup_right
  have hsup : E₁ ⊔ K₁ = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top, IntermediateField.lift_sup,
      IntermediateField.lift_restrict le_sup_left, IntermediateField.lift_restrict le_sup_right]
  have eE₁ : E ≃ₐ[F] E₁ :=
    ι.equivFieldRange.trans (IntermediateField.restrictAlgEquiv le_sup_left)
  have : FiniteDimensional F E₁ := Module.Finite.equiv eE₁.toLinearEquiv
  have : IsGalois F E₁ := IsGalois.of_algEquiv eE₁
  have : FiniteDimensional K₁ L := FiniteDimensional.right F K₁ L
  have : IsGalois K₁ L := IsGalois.sup_right E₁ K₁ hsup
  have hinj : Function.Injective (IntermediateField.restrictRestrictAlgEquivMapHom F E₁ K₁ L) :=
    IntermediateField.restrictRestrictAlgEquivMapHom_injective E₁ K₁ hsup
  have hsolE₁ : Group.IsSolvable (E₁ ≃ₐ[F] E₁) := eE₁.autCongr.isSolvable_congr.mp hsol
  have hsolL : Group.IsSolvable (L ≃ₐ[K₁] L) :=
    Group.isSolvable_of_isSolvable_injective hinj
  have hdvd : Module.finrank K₁ L ∣ N := by
    have hcard := Subgroup.card_dvd_of_injective _ hinj
    rwa [IsGalois.card_aut_eq_finrank K₁ L, IsGalois.card_aut_eq_finrank F E₁,
      LinearEquiv.finrank_eq eE₁.symm.toLinearEquiv] at hcard
  have hK₁_rad : ∀ x : K₁, ((x : L) : Ω) ∈ solvableByRad F Ω := by
    have hle : F⟮ζ⟯ ≤ solvableByRad F Ω :=
      IntermediateField.adjoin_simple_le_iff.mpr hζ_rad
    exact fun x => hle ((IntermediateField.mem_restrict (le_sup_right : F⟮ζ⟯ ≤ L) x.1).mp x.2)
  have hζK₁ : ∃ ξ : K₁, IsPrimitiveRoot ξ N := by
    have hζ_mem_L : ζ ∈ L :=
      (le_sup_right : F⟮ζ⟯ ≤ L) (IntermediateField.mem_adjoin_simple_self F ζ)
    have hζ_mem_K₁ : (⟨ζ, hζ_mem_L⟩ : L) ∈ K₁ :=
      (IntermediateField.mem_restrict (le_sup_right : F⟮ζ⟯ ≤ L) _).mpr
        (IntermediateField.mem_adjoin_simple_self F ζ)
    exact ⟨⟨⟨ζ, hζ_mem_L⟩, hζ_mem_K₁⟩,
      hζ.of_map_of_injective (f := (IsScalarTower.toAlgHom F K₁ Ω).toRingHom)
        (IsScalarTower.toAlgHom F K₁ Ω).injective⟩
  have hL_rad := forall_mem_solvableByRad_of_isSolvable_aux L hNpos.ne' (Module.finrank K₁ L) K₁
    inferInstance inferInstance hsolL rfl hdvd hζK₁ hK₁_rad
  exact fun x => hL_rad ⟨ι x, (le_sup_left : ι.fieldRange ≤ L) ⟨x, rfl⟩⟩

/-- **The radical criterion for finite Galois extensions** (Milne, *Fields and Galois Theory*,
Theorem 5.34). In characteristic zero, a finite Galois extension `E/F` has solvable Galois group
if and only if, under an `F`-embedding `ι` into a separably closed extension `Ω` (such as
`AlgebraicClosure F`), every element of `E` lands in `solvableByRad F Ω`. -/
theorem isSolvable_iff_forall_mem_solvableByRad
    (F E : Type*) [Field F] [CharZero F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    {Ω : Type*} [Field Ω] [Algebra F Ω] [IsSepClosed Ω] (ι : E →ₐ[F] Ω) :
    Group.IsSolvable (E ≃ₐ[F] E) ↔ ∀ x : E, ι x ∈ solvableByRad F Ω := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((Module.finrank F E : ℕ) : Ω) :=
    ⟨Nat.cast_ne_zero.mpr Module.finrank_pos.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω (Module.finrank F E)
  exact isSolvable_iff_forall_mem_solvableByRad_of_isPrimitiveRoot F E ι hζ

/-- **The radical criterion for polynomials.** In characteristic zero, a polynomial `q : F[X]` has
solvable Galois group if and only if every root of `q` in a separably closed extension `Ω` (such
as `AlgebraicClosure F`) lies in `solvableByRad F Ω`.

Reducible polynomials, polynomials with repeated factors, `0`, and constants are all included. -/
theorem isSolvable_gal_iff_forall_rootSet_mem_solvableByRad
    {F : Type*} (Ω : Type*) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] [IsSepClosed Ω]
    (q : F[X]) :
    Group.IsSolvable q.Gal ↔ ∀ x ∈ q.rootSet Ω, x ∈ solvableByRad F Ω := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := inferInstance
  have : Algebra.IsSeparable F q.SplittingField :=
    Algebra.IsSeparable.of_integral F q.SplittingField
  have : IsGalois F q.SplittingField := {}
  let ι : q.SplittingField →ₐ[F] Ω := IsAlgClosed.lift
  refine (isSolvable_iff_forall_mem_solvableByRad F q.SplittingField ι).trans ?_
  have himg : ι '' q.rootSet q.SplittingField = q.rootSet Ω :=
    (SplittingField.splits q).image_rootSet ι
  constructor
  · intro h x hx
    rw [← himg] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact h y
  · intro h y
    have hsub : Algebra.adjoin F (q.rootSet q.SplittingField) ≤
        (solvableByRad F Ω).toSubalgebra.comap ι := by
      rw [Algebra.adjoin_le_iff]
      intro z hz
      exact h (ι z) (himg ▸ Set.mem_image_of_mem ι hz)
    have htop : Algebra.adjoin F (q.rootSet q.SplittingField) = ⊤ :=
      IsSplittingField.adjoin_rootSet q.SplittingField q
    exact hsub (htop ▸ Algebra.mem_top)

/-- **The radical criterion for irreducible polynomials.** In characteristic zero, an irreducible
polynomial `q : F[X]` has solvable Galois group if and only if some root of `q` in a separably
closed extension `Ω` lies in `solvableByRad F Ω`. -/
theorem isSolvable_gal_iff_exists_rootSet_mem_solvableByRad
    {F : Type*} (Ω : Type*) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] [IsSepClosed Ω]
    {q : F[X]} (hq : Irreducible q) :
    Group.IsSolvable q.Gal ↔ ∃ x ∈ q.rootSet Ω, x ∈ solvableByRad F Ω := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := inferInstance
  refine ⟨fun hsol => ?_, fun ⟨x, hx, hrad⟩ =>
    isSolvable_gal_of_irreducible hrad hq (aeval_eq_zero_of_mem_rootSet hx)⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (q.map (algebraMap F Ω))
    (by rw [degree_map]; exact (degree_pos_of_irreducible hq).ne')
  have hxmem : x ∈ q.rootSet Ω :=
    mem_rootSet.mpr ⟨hq.ne_zero, by rwa [aeval_def, ← eval_map]⟩
  exact ⟨x, hxmem, (isSolvable_gal_iff_forall_rootSet_mem_solvableByRad Ω q).mp hsol x hxmem⟩

/-- An irreducible rational polynomial of prime degree at least `5` with exactly two nonreal roots
has no root solvable by radicals in any field extension of `ℚ`. -/
theorem not_mem_solvableByRad_of_prime_degree
    {Ω : Type*} [Field Ω] [Algebra ℚ Ω] {q : ℚ[X]}
    (hq : Irreducible q) (hdeg : q.natDegree.Prime) (h5 : 5 ≤ q.natDegree)
    (hroots : Fintype.card (q.rootSet ℂ) = Fintype.card (q.rootSet ℝ) + 2)
    {x : Ω} (hx : x ∈ q.rootSet Ω) :
    x ∉ solvableByRad ℚ Ω := by
  intro hrad
  have hsol : Group.IsSolvable q.Gal :=
    isSolvable_gal_of_irreducible hrad hq (aeval_eq_zero_of_mem_rootSet hx)
  have hbij := Gal.galActionHom_bijective_of_prime_degree hq hdeg hroots
  have hperm : Group.IsSolvable (Equiv.Perm (q.rootSet ℂ)) :=
    (MulEquiv.ofBijective _ hbij).isSolvable_congr.mp hsol
  have hcard : Fintype.card (q.rootSet ℂ) = q.natDegree :=
    card_rootSet_eq_natDegree hq.separable (IsAlgClosed.splits _)
  have h5' : (5 : Cardinal) ≤ Cardinal.mk (q.rootSet ℂ) := by
    rw [Cardinal.mk_fintype, hcard]
    exact_mod_cast h5
  exact Equiv.Perm.not_isSolvable (q.rootSet ℂ) h5' hperm

end TauCeti
