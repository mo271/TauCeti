/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.FieldTheory.AbelRuffini.Basic

import Mathlib.Topology.Order.IntermediateValue
import TauCeti.FieldTheory.GaloisGroups.Cubic

/-!
# Real and complex obstructions and sharpness in solvability by radicals

This file isolates two consequences of real and complex embeddings for `solvableByRad`:

* **Prime-degree unsolvability over `ℚ`.** If `q : ℚ[X]` is irreducible of prime degree `p ≥ 5`
  and has between one and three non-real complex roots (in particular, exactly two non-real roots),
  then `Polynomial.Gal.galActionHom_bijective_of_prime_degree'` identifies `q.Gal` with the full
  symmetric group on `q.rootSet ℂ`, which is nonsolvable (`Equiv.Perm.not_isSolvable`). Hence
  `q.Gal` is not solvable and no root of `q` in any `ℚ`-extension `E` lies in `solvableByRad ℚ E`.
* **Casus irreducibilis and sharpness of the ambient algebraically closed field.** In
  `TauCeti.isSolvable_iff_forall_mem_solvableByRad`, the roots of unity used to reach a solvable
  Galois extension `E / F` by radicals live in an ambient algebraically closed field `Ω`, not in
  `E` itself. Whenever `E / F` is a finite normal extension of odd degree admitting an
  `F`-embedding into a strictly ordered field `K` (such as `ℝ`), `solvableByRad F E = ⊥`
  (`TauCeti.solvableByRad_eq_bot_of_odd_finrank`): an odd-degree radical step over `F` would force
  its minimal polynomial to split in `K`, whereas `x ↦ x ^ p` is strictly monotone for odd `p`, and
  a quadratic step is excluded by oddness of `[E : F]`. The totally real cyclic cubic
  `X³ - 3X - 1 : ℚ[X]` realizes this phenomenon: its Galois group is cyclic of order `3` (hence
  solvable), yet `solvableByRad ℚ (X³ - 3X - 1).SplittingField = ⊥`.

## Main results

* `TauCeti.not_isSolvable_gal_of_prime_natDegree'`,
  `TauCeti.not_isSolvable_gal_of_prime_natDegree`: an irreducible rational polynomial of prime
  degree `p ≥ 5` with `1`–`3` (in particular, `2`) non-real roots has nonsolvable Galois group.
* `TauCeti.not_mem_solvableByRad_of_prime_natDegree'`,
  `TauCeti.not_mem_solvableByRad_of_prime_natDegree`: no root of such a polynomial in any extension
  `E / ℚ` is solvable by radicals over `ℚ`.
* `TauCeti.solvableByRad_eq_bot_of_odd_finrank`: **casus irreducibilis** for odd-degree normal
  extensions embeddable into a strictly ordered field.
* `TauCeti.isSolvable_gal_X_pow_three_sub_three_mul_X_sub_one`,
  `TauCeti.solvableByRad_splittingField_X_pow_three_sub_three_mul_X_sub_one`: `X³ - 3X - 1` over
  `ℚ` has solvable Galois group while `solvableByRad ℚ (X³ - 3X - 1).SplittingField = ⊥`.

## References

* J. S. Milne, *Fields and Galois Theory*, v5.10 (2022), Remark 5.36 and Example 5.42.
-/

public section

open IntermediateField Polynomial

namespace TauCeti

section PrimeDegree

/-- **Prime-degree unsolvability over `ℚ` (1–3 non-real roots).** If `q : ℚ[X]` is irreducible of
prime degree `p ≥ 5` and has between one and three non-real complex roots, then `q.Gal` is not
solvable. -/
theorem not_isSolvable_gal_of_prime_natDegree' {q : ℚ[X]} (hq_irr : Irreducible q)
    (hq_prime : q.natDegree.Prime) (hq_five : 5 ≤ q.natDegree)
    (hroots₁ : Fintype.card (q.rootSet ℝ) + 1 ≤ Fintype.card (q.rootSet ℂ))
    (hroots₂ : Fintype.card (q.rootSet ℂ) ≤ Fintype.card (q.rootSet ℝ) + 3) :
    ¬ Group.IsSolvable q.Gal := by
  have : Fact ((q.map (algebraMap ℚ ℂ)).Splits) := Polynomial.Gal.splits_ℚ_ℂ
  have hbij :=
    Polynomial.Gal.galActionHom_bijective_of_prime_degree' hq_irr hq_prime hroots₁ hroots₂
  let e : q.Gal ≃* Equiv.Perm (q.rootSet ℂ) :=
    MulEquiv.ofBijective (Polynomial.Gal.galActionHom q ℂ) hbij
  have hcard : Fintype.card (q.rootSet ℂ) = q.natDegree :=
    card_rootSet_eq_natDegree hq_irr.separable (IsAlgClosed.splits _)
  have hfive : (5 : Cardinal) ≤ Cardinal.mk (q.rootSet ℂ) := by
    rw [Cardinal.mk_fintype, ← Nat.cast_ofNat]
    exact Nat.cast_le.mpr (hcard ▸ hq_five)
  exact fun hsol ↦ Equiv.Perm.not_isSolvable (q.rootSet ℂ) hfive
    ((MulEquiv.isSolvable_congr e).mp hsol)

/-- **Prime-degree unsolvability over `ℚ` (two non-real roots).** If `q : ℚ[X]` is irreducible of
prime degree `p ≥ 5` and has exactly two non-real complex roots, then `q.Gal` is not solvable. -/
theorem not_isSolvable_gal_of_prime_natDegree {q : ℚ[X]} (hq_irr : Irreducible q)
    (hq_prime : q.natDegree.Prime) (hq_five : 5 ≤ q.natDegree)
    (hroots : Fintype.card (q.rootSet ℂ) = Fintype.card (q.rootSet ℝ) + 2) :
    ¬ Group.IsSolvable q.Gal :=
  not_isSolvable_gal_of_prime_natDegree' hq_irr hq_prime hq_five (by omega) (by omega)

/-- **No root is solvable by radicals (1–3 non-real roots).** For an irreducible `q : ℚ[X]` of
prime degree `p ≥ 5` with between one and three non-real complex roots, no root of `q` in any field
extension `E / ℚ` lies in `solvableByRad ℚ E`. -/
theorem not_mem_solvableByRad_of_prime_natDegree' {E : Type*} [Field E] [Algebra ℚ E] {q : ℚ[X]}
    (hq_irr : Irreducible q) (hq_prime : q.natDegree.Prime) (hq_five : 5 ≤ q.natDegree)
    (hroots₁ : Fintype.card (q.rootSet ℝ) + 1 ≤ Fintype.card (q.rootSet ℂ))
    (hroots₂ : Fintype.card (q.rootSet ℂ) ≤ Fintype.card (q.rootSet ℝ) + 3) {x : E}
    (hx : x ∈ q.rootSet E) : x ∉ solvableByRad ℚ E :=
  fun hrad ↦ not_isSolvable_gal_of_prime_natDegree' hq_irr hq_prime hq_five hroots₁ hroots₂
    (isSolvable_gal_of_irreducible hrad hq_irr (aeval_eq_zero_of_mem_rootSet hx))

/-- **No root is solvable by radicals (two non-real roots).** For an irreducible `q : ℚ[X]` of
prime degree `p ≥ 5` with exactly two non-real complex roots, no root of `q` in any field extension
`E / ℚ` lies in `solvableByRad ℚ E`. -/
theorem not_mem_solvableByRad_of_prime_natDegree {E : Type*} [Field E] [Algebra ℚ E] {q : ℚ[X]}
    (hq_irr : Irreducible q) (hq_prime : q.natDegree.Prime) (hq_five : 5 ≤ q.natDegree)
    (hroots : Fintype.card (q.rootSet ℂ) = Fintype.card (q.rootSet ℝ) + 2) {x : E}
    (hx : x ∈ q.rootSet E) : x ∉ solvableByRad ℚ E :=
  not_mem_solvableByRad_of_prime_natDegree' hq_irr hq_prime hq_five (by omega) (by omega) hx

end PrimeDegree

section CasusIrreducibilis

/-- **Casus irreducibilis for odd-degree normal extensions.** If `E / F` is a finite normal
extension of odd degree that admits an `F`-embedding into a strictly ordered field `K` (such as
`ℝ`), then `solvableByRad F E = ⊥`.

In particular, when `1 < [E : F]` and `Gal(E/F)` is solvable, `E` cannot be generated by radicals
inside `E` itself: the algebraically closed ambient field `Ω` in
`TauCeti.isSolvable_iff_forall_mem_solvableByRad` is essential. -/
theorem solvableByRad_eq_bot_of_odd_finrank {F E K : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Normal F E] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Algebra F K] (ι : E →ₐ[F] K) (hodd : Odd (Module.finrank F E)) :
    solvableByRad F E = ⊥ := by
  have : CharZero E := ι.toRingHom.charZero
  have : CharZero F := (algebraMap F E).charZero
  -- Prime radical step: `y ^ p ∈ F` forces `y ∈ F` by parity (`p = 2`) or monotonicity (`Odd p`).
  have hprime : ∀ (y : E) {p : ℕ}, p.Prime → y ^ p ∈ (⊥ : IntermediateField F E) →
      y ∈ (⊥ : IntermediateField F E) := by
    intro y p hp hyp
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hyp
    have hdvd : minpoly F y ∣ X ^ p - C a :=
      minpoly.dvd F y (by rw [map_sub, aeval_X_pow, aeval_C, ← ha, sub_self])
    have hfin_dvd : Module.finrank F F⟮y⟯ ∣ Module.finrank F E :=
      ⟨Module.finrank F⟮y⟯ E, (Module.finrank_mul_finrank F F⟮y⟯ E).symm⟩
    have hdeg_pos : 0 < Module.finrank F F⟮y⟯ := Module.finrank_pos
    have hfin_eq : Module.finrank F F⟮y⟯ = 1 := by
      rcases hp.eq_two_or_odd' with rfl | hp_odd
      · have hle2 : Module.finrank F F⟮y⟯ ≤ 2 := by
          rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral y)]
          exact (natDegree_le_of_dvd hdvd (X_pow_sub_C_ne_zero (by decide) a)).trans
            (natDegree_X_pow_sub_C (n := 2) (a := a)).le
        rcases (show Module.finrank F F⟮y⟯ = 1 ∨ Module.finrank F F⟮y⟯ = 2 by omega) with h1 | h2
        · exact h1
        · exfalso
          obtain ⟨m, hm⟩ := hodd
          obtain ⟨k, hk⟩ := hfin_dvd
          rw [h2] at hk
          omega
      · have hsep : (minpoly F y).Separable := Algebra.IsSeparable.isSeparable F y
        have hsplits : ((minpoly F y).map (algebraMap F E)).Splits := Normal.splits' y
        have hcard_le : Fintype.card ((minpoly F y).rootSet E) ≤ 1 := by
          refine Fintype.card_le_one_iff.mpr fun u v ↦ Subtype.ext ?_
          have hu : (u : E) ^ p = algebraMap F E a := by
            have h0 := aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (aeval_eq_zero_of_mem_rootSet u.2)
            rwa [map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at h0
          have hv : (v : E) ^ p = algebraMap F E a := by
            have h0 := aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (aeval_eq_zero_of_mem_rootSet v.2)
            rwa [map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at h0
          have hι : (ι u) ^ p = (ι v) ^ p := by rw [← map_pow, ← map_pow, hu, hv]
          exact ι.injective (hp_odd.strictMono_pow.injective hι)
        have hle1 : Module.finrank F F⟮y⟯ ≤ 1 := by
          rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral y),
            ← card_rootSet_eq_natDegree hsep hsplits]
          exact hcard_le
        omega
    rw [← IntermediateField.finrank_eq_one_iff.mp hfin_eq]
    exact IntermediateField.mem_adjoin_simple_self F y
  -- General `n ≠ 0` follows by strong induction on `n` via `n.minFac`.
  refine eq_bot_iff.mpr (solvableByRad_le fun x n hn hx ↦ ?_)
  induction n using Nat.strongRecOn generalizing x with
  | ind n ih =>
    by_cases hn1 : n = 1
    · rwa [hn1, pow_one] at hx
    · have hp : n.minFac.Prime := Nat.minFac_prime hn1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hn (by simpa using hm)
      have hm_lt : m < n :=
        hm ▸ lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hp.one_lt
      have hxm : x ^ m ∈ (⊥ : IntermediateField F E) := by
        refine hprime (x ^ m) hp ?_
        rwa [← pow_mul, mul_comm, ← hm]
      exact ih m hm_lt x hm0 hxm

/-- The cyclic cubic `X³ - 3X - 1 : ℚ[X]` splits completely over `ℝ`: by the intermediate value
theorem it has roots in `(-2, -1)`, `(-1, 0)`, and `(0, 2)`. -/
theorem splits_real_X_pow_three_sub_three_mul_X_sub_one :
    ((X ^ 3 - 3 * X - 1 : ℚ[X]).map (algebraMap ℚ ℝ)).Splits := by
  set P : ℝ[X] := (X ^ 3 - 3 * X - 1 : ℚ[X]).map (algebraMap ℚ ℝ)
  have hP_eval : ∀ r : ℝ, P.eval r = r ^ 3 - 3 * r - 1 := fun r ↦ by simp [P]
  have hP_deg : P.natDegree = 3 := by
    rw [natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective]
    compute_degree!
  have hP_ne : P ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hP_deg
    omega
  obtain ⟨r₁, hr₁_mem, hr₁⟩ := intermediate_value_Ioo (a := (-2 : ℝ)) (b := -1) (by norm_num)
    P.continuous.continuousOn (show (0 : ℝ) ∈ Set.Ioo _ _ by rw [hP_eval, hP_eval]; norm_num)
  obtain ⟨r₂, hr₂_mem, hr₂⟩ := intermediate_value_Ioo' (a := (-1 : ℝ)) (b := 0) (by norm_num)
    P.continuous.continuousOn (show (0 : ℝ) ∈ Set.Ioo _ _ by rw [hP_eval, hP_eval]; norm_num)
  obtain ⟨r₃, hr₃_mem, hr₃⟩ := intermediate_value_Ioo (a := (0 : ℝ)) (b := 2) (by norm_num)
    P.continuous.continuousOn (show (0 : ℝ) ∈ Set.Ioo _ _ by rw [hP_eval, hP_eval]; norm_num)
  have h12 : r₁ ≠ r₂ := by linarith [hr₁_mem.2, hr₂_mem.1]
  have h23 : r₂ ≠ r₃ := by linarith [hr₂_mem.2, hr₃_mem.1]
  have h13 : r₁ ≠ r₃ := by linarith [hr₁_mem.2, hr₂_mem.1, hr₂_mem.2, hr₃_mem.1]
  let S : Finset ℝ := {r₁, r₂, r₃}
  have hS_card : S.card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
  have hS_le : S.val ≤ P.roots := by
    refine (Multiset.le_iff_subset S.nodup).mpr fun r hr ↦ (mem_roots hP_ne).mpr ?_
    simp only [S, Finset.mem_val, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact hr₁
    · exact hr₂
    · exact hr₃
  have hcard_ge : 3 ≤ P.roots.card := by
    have hle := Multiset.card_le_card hS_le
    rwa [← Finset.card_def, hS_card] at hle
  have hcard_le : P.roots.card ≤ 3 := hP_deg ▸ card_roots' P
  exact splits_iff_card_roots.mpr (by omega)

/-- The cubic `X³ - 3X - 1 : ℚ[X]` has solvable Galois group. -/
theorem isSolvable_gal_X_pow_three_sub_three_mul_X_sub_one :
    Group.IsSolvable (X ^ 3 - 3 * X - 1 : ℚ[X]).Gal :=
  Polynomial.isSolvable_gal_of_natDegree_le_four (by compute_degree!)

/-- **Sharpness of the ambient field in `TauCeti.isSolvable_iff_forall_mem_solvableByRad`.**
Although `X³ - 3X - 1 : ℚ[X]` is Galois over `ℚ` with cyclic (hence solvable) Galois group of
order `3`, its splitting field has `solvableByRad ℚ (X³ - 3X - 1).SplittingField = ⊥`, whereas
`SplittingField ℚ (X³ - 3X - 1)` is nontrivial of degree `3` over `ℚ`. -/
theorem solvableByRad_splittingField_X_pow_three_sub_three_mul_X_sub_one :
    solvableByRad ℚ (X ^ 3 - 3 * X - 1 : ℚ[X]).SplittingField = ⊥ := by
  set p : ℚ[X] := X ^ 3 - 3 * X - 1
  have : IsGalois ℚ p.SplittingField :=
    IsGalois.of_separable_splitting_field irreducible_X_pow_three_sub_three_mul_X_sub_one.separable
  let ι : p.SplittingField →ₐ[ℚ] ℝ :=
    SplittingField.lift p splits_real_X_pow_three_sub_three_mul_X_sub_one
  have hfin : Module.finrank ℚ p.SplittingField = 3 := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact natCard_gal_X_pow_three_sub_three_mul_X_sub_one
  exact solvableByRad_eq_bot_of_odd_finrank ι ⟨1, by omega⟩

end CasusIrreducibilis

end TauCeti
