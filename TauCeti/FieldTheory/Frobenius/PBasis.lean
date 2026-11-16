/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.FieldTheory.Frobenius.PIndependent
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Finsupp.Single
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Zorn

/-!
# `p`-bases of fields in positive characteristic

Let `k` be a field of characteristic `p > 0` and `k ^ p = (frobenius k p).fieldRange` its subfield
of `p`-th powers. A family `b : ι → k` is a **`p`-basis** of `k` (`TauCeti.IsPBasis`) if its
`p`-monomials `pMonomial p b` (`e : ι →₀ Fin p`, so finitely many nonzero exponents, each `< p`)
form a `k ^ p`-basis of `k`: they are linearly independent over `k ^ p` and span `k` over `k ^ p`.

Without any finiteness assumption on `[k : k ^ p]`:
* Every `p`-independent subset or family in `k` extends to a `p`-basis
  (`IsPIndependent.exists_isPBasis_superset`, `IsPIndependent.exists_isPBasis_range_superset`), and
  in particular every field of characteristic `p` admits a (possibly infinite) `p`-basis
  (`exists_isPBasis`).
* A `p`-basis `b : ι → k` has a finite index type if and only if `k` is finite-dimensional over
  `k ^ p` (`IsPBasis.finite_iff_finiteDimensional`), in which case
  `[k : k ^ p] = p ^ Fintype.card ι` (`IsPBasis.finrank_fieldRange_frobenius`).
* An empty family is a `p`-basis if and only if `k` is perfect
  (`isPBasis_of_isEmpty_iff_perfectField`), equivalently `[k : k ^ p] = 1`
  (`finrank_fieldRange_frobenius_eq_one_iff_perfectField`).

## Main definitions

* `TauCeti.IsPBasis`: `b : ι → k` is a `p`-basis of `k` over `k ^ p`.
* `TauCeti.IsPBasis.basis`: the `k ^ p`-basis of `k` indexed by `ι →₀ Fin p` formed by the
  `p`-monomials of `b`.

## Main results

* `TauCeti.isPBasis_iff_of_fintype`: on a finite index type `ι`, `IsPBasis p b` is equivalent to
  linear independence and spanning of `fun e : ι → Fin p ↦ ∏ i, b i ^ (e i : ℕ)` over `k ^ p`.
* `TauCeti.isPBasis_iff_isPIndependent_and_adjoin_eq_top`: `b` is a `p`-basis iff `b` is
  `p`-independent and `k ^ p[b] = k`.
* `TauCeti.IsPIndependent.exists_isPBasis_superset`, `TauCeti.exists_isPBasis`: existence of
  `p`-bases via Zorn's lemma.
* `TauCeti.IsPBasis.finite_iff_finiteDimensional`, `TauCeti.IsPBasis.finrank_fieldRange_frobenius`:
  finiteness equivalence and the degree formula `[k : k ^ p] = p ^ |ι|`.
* `TauCeti.isPBasis_of_isEmpty_iff_perfectField`,
  `TauCeti.finrank_fieldRange_frobenius_eq_one_iff_perfectField`: characterizations of perfect
  fields.

## References

* H. Matsumura, *Commutative Ring Theory*, 2nd ed., Cambridge Univ. Press, 1989, §26.
* The Stacks Project, Definition 15.47.1 (Tag 07P1).
* D. Clausen, A. Mathew, and M. Morrow, *K-theory and topological cyclic homology of henselian
  pairs*, J. Amer. Math. Soc. 34 (2021), §5.1, Footnote 10.
-/

public section

open Finset

namespace TauCeti

section Basic

variable (p : ℕ) [NeZero p] {k : Type*} [Field k] [ExpChar k p] {ι ι' : Type*}

/-- A family `b : ι → k` in a field of exponential characteristic `p` is a **`p`-basis** if its
`p`-monomials `pMonomial p b` (`e : ι →₀ Fin p`) are linearly independent over `k ^ p` and span
`k` over `k ^ p`. -/
def IsPBasis (b : ι → k) : Prop :=
  IsPIndependent p b ∧
    Submodule.span (frobenius k p).fieldRange (Set.range (pMonomial p b)) = ⊤

theorem isPBasis_def {b : ι → k} :
    IsPBasis p b ↔
      IsPIndependent p b ∧
        Submodule.span (frobenius k p).fieldRange (Set.range (pMonomial p b)) = ⊤ :=
  (Iff.rfl)

variable {p}

theorem IsPBasis.isPIndependent {b : ι → k} (hb : IsPBasis p b) : IsPIndependent p b :=
  hb.1

theorem IsPBasis.span_eq {b : ι → k} (hb : IsPBasis p b) :
    Submodule.span (frobenius k p).fieldRange (Set.range (pMonomial p b)) = ⊤ :=
  hb.2

/-- On a finite index type `ι`, `IsPBasis p b` is equivalent to the `k ^ p`-basis conditions on
the finitely indexed monomials `fun e : ι → Fin p ↦ ∏ i, b i ^ (e i : ℕ)`. -/
theorem isPBasis_iff_of_fintype [Fintype ι] {b : ι → k} :
    IsPBasis p b ↔
      LinearIndependent (frobenius k p).fieldRange (fun e : ι → Fin p ↦ ∏ i, b i ^ (e i : ℕ)) ∧
        Submodule.span (frobenius k p).fieldRange
          (Set.range fun e : ι → Fin p ↦ ∏ i, b i ^ (e i : ℕ)) = ⊤ := by
  rw [isPBasis_def, isPIndependent_iff_of_fintype]
  refine and_congr_right' ?_
  have hrange : Set.range (pMonomial p b) =
      Set.range (fun e : ι → Fin p ↦ ∏ i, b i ^ (e i : ℕ)) := by
    ext x
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨Finsupp.equivFunOnFinite e, by simp [pMonomial_eq_prod]⟩
    · rintro ⟨e, rfl⟩
      exact ⟨Finsupp.equivFunOnFinite.symm e, by simp⟩
  rw [hrange]

/-- The `k ^ p`-basis of `k` indexed by `ι →₀ Fin p` formed by the `p`-monomials of a `p`-basis. -/
noncomputable def IsPBasis.basis {b : ι → k} (hb : IsPBasis p b) :
    Module.Basis (ι →₀ Fin p) (frobenius k p).fieldRange k :=
  Module.Basis.mk ((isPIndependent_def p).mp hb.isPIndependent) hb.span_eq.ge

@[simp]
theorem IsPBasis.basis_apply {b : ι → k} (hb : IsPBasis p b) (e : ι →₀ Fin p) :
    hb.basis e = pMonomial p b e :=
  Module.Basis.mk_apply ((isPIndependent_def p).mp hb.isPIndependent) hb.span_eq.ge e

/-- Reindexing along an equivalence preserves being a `p`-basis. -/
theorem isPBasis_equiv (e : ι' ≃ ι) {b : ι → k} :
    IsPBasis p (b ∘ e) ↔ IsPBasis p b := by
  rw [isPBasis_def, isPBasis_def, isPIndependent_equiv e]
  refine and_congr_right' ?_
  have hrange : Set.range (pMonomial p (b ∘ e)) = Set.range (pMonomial p b) := by
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f.equivMapDomain e, pMonomial_equivMapDomain p b e f⟩
    · rintro ⟨f, rfl⟩
      exact ⟨f.equivMapDomain e.symm, by simp [Function.comp_def]⟩
  rw [hrange]

theorem IsPBasis.reindex {b : ι → k} (hb : IsPBasis p b) (e : ι' ≃ ι) : IsPBasis p (b ∘ e) :=
  (isPBasis_equiv e).mpr hb

/-- For `1 < p`, every `p`-basis is injective. -/
theorem IsPBasis.injective (hp : 1 < p) {b : ι → k} (hb : IsPBasis p b) : Function.Injective b :=
  hb.isPIndependent.injective hp

/-- For `1 < p`, no member of a `p`-basis can lie in `k ^ p`. -/
theorem not_isPBasis_of_mem_fieldRange_frobenius (hp : 1 < p) {b : ι → k} {i : ι}
    (hi : b i ∈ (frobenius k p).fieldRange) : ¬ IsPBasis p b :=
  fun hb ↦ not_isPIndependent_of_mem_fieldRange_frobenius hp hi hb.isPIndependent

/-- For a finite `p`-basis `b : ι → k`, the degree `[k : k ^ p]` equals `p ^ Fintype.card ι`. -/
theorem IsPBasis.finrank_fieldRange_frobenius [Fintype ι] {b : ι → k} (hb : IsPBasis p b) :
    Module.finrank (frobenius k p).fieldRange k = p ^ Fintype.card ι := by
  classical
  rw [Module.finrank_eq_card_basis hb.basis, Fintype.card_congr Finsupp.equivFunOnFinite,
    Fintype.card_fun, Fintype.card_fin]

end Basic

section PrimeChar

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*} [Field k] [CharP k p] {ι : Type*}

/-- A family `b : ι → k` is a `p`-basis if and only if it is `p`-independent and generates `k` as a
`k ^ p`-algebra. -/
theorem isPBasis_iff_isPIndependent_and_adjoin_eq_top {b : ι → k} :
    IsPBasis p b ↔
      IsPIndependent p b ∧ Algebra.adjoin (frobenius k p).fieldRange (Set.range b) = ⊤ := by
  rw [isPBasis_def, ← adjoin_fieldRange_frobenius_toSubmodule]
  refine and_congr_right' ?_
  rw [eq_top_iff, eq_top_iff]
  exact ⟨fun h x hx ↦ h hx, fun h x hx ↦ h hx⟩

/-- A family `b : ι → k` is a `p`-basis if and only if it is `p`-independent and generates `k` as
an intermediate field over `k ^ p`. -/
theorem isPBasis_iff_isPIndependent_and_intermediateField_adjoin_eq_top {b : ι → k} :
    IsPBasis p b ↔
      IsPIndependent p b ∧
        IntermediateField.adjoin (frobenius k p).fieldRange (Set.range b) = ⊤ := by
  rw [isPBasis_def]
  refine and_congr_right' ?_
  have hcoe := coe_intermediateField_adjoin_fieldRange_frobenius (p := p) b
  simp_rw [SetLike.ext'_iff, ← hcoe]
  simp

/-- Every `p`-independent subset `s : Set k` extends to a `p`-basis of `k`. -/
theorem IsPIndependent.exists_isPBasis_superset {s : Set k}
    (hs : IsPIndependent p ((↑) : s → k)) :
    ∃ t : Set k, s ⊆ t ∧ IsPBasis p ((↑) : t → k) := by
  let S : Set (Set k) := {t | IsPIndependent p ((↑) : t → k)}
  obtain ⟨t, hst, hmax⟩ := zorn_subset_nonempty S
    (fun c hcS hchain _ ↦ ⟨⋃₀ c, isPIndependent_sUnion_of_isChain hchain fun u hu ↦ hcS hu,
      fun _ ↦ Set.subset_sUnion_of_mem⟩) s hs
  refine ⟨t, hst, hmax.prop, ?_⟩
  rw [eq_top_iff]
  intro x _
  by_contra hx
  have hxt : x ∉ t := fun hmem ↦ hx <| by
    have : x = pMonomial p ((↑) : t → k) (Finsupp.single ⟨x, hmem⟩ ⟨1, hp.out.one_lt⟩) := by simp
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hins : insert x t ∈ S := (isPIndependent_insert_iff hxt).mpr ⟨hmax.prop, hx⟩
  exact hxt (hmax.eq_of_subset hins (Set.subset_insert x t) ▸ Set.mem_insert x t)

/-- The range of a `p`-independent family in prime characteristic is `p`-independent as a subset. -/
theorem IsPIndependent.subtype_range {b : ι → k} (hb : IsPIndependent p b) :
    IsPIndependent p ((↑) : Set.range b → k) := by
  have hinj := hb.injective hp.out.one_lt
  have hcomp : (((↑) : Set.range b → k) ∘ Equiv.ofInjective b hinj) = b := by
    ext i
    simp
  exact (isPIndependent_equiv (Equiv.ofInjective b hinj)).mp (hcomp.symm ▸ hb)

/-- The range of any `p`-independent family `b : ι → k` is contained in a `p`-basis of `k`. -/
theorem IsPIndependent.exists_isPBasis_range_superset {b : ι → k} (hb : IsPIndependent p b) :
    ∃ t : Set k, Set.range b ⊆ t ∧ IsPBasis p ((↑) : t → k) :=
  hb.subtype_range.exists_isPBasis_superset

/-- Every field `k` of prime characteristic `p` possesses a (possibly infinite) `p`-basis. -/
theorem exists_isPBasis (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] :
    ∃ s : Set k, IsPBasis p ((↑) : s → k) := by
  have hempty := isPIndependent_of_isEmpty p ((↑) : (∅ : Set k) → k)
  obtain ⟨t, _, ht⟩ := hempty.exists_isPBasis_superset
  exact ⟨t, ht⟩

/-- A `p`-basis `b : ι → k` has a finite index type if and only if `k` is finite-dimensional over
`k ^ p`. -/
theorem IsPBasis.finite_iff_finiteDimensional {b : ι → k} (hb : IsPBasis p b) :
    Finite ι ↔ FiniteDimensional (frobenius k p).fieldRange k := by
  classical
  constructor
  · intro _
    cases nonempty_fintype ι
    exact hb.basis.finiteDimensional_of_finite
  · intro _
    let _ : Fintype (ι →₀ Fin p) := FiniteDimensional.fintypeBasisIndex hb.basis
    exact Finite.of_injective (fun i : ι ↦ Finsupp.single i (⟨1, hp.out.one_lt⟩ : Fin p))
      (Finsupp.single_left_injective (Fin.ne_of_gt Nat.zero_lt_one))

/-- A field `k` of characteristic `p` satisfies `k ^ p = k` if and only if `k` is perfect. -/
theorem fieldRange_frobenius_eq_top_iff_perfectField :
    (frobenius k p).fieldRange = ⊤ ↔ PerfectField k := by
  constructor
  · intro htop
    have hsurj : Function.Surjective (frobenius k p) := fun x ↦
      RingHom.mem_fieldRange.mp (htop.symm ▸ Subfield.mem_top x)
    let _ : PerfectRing k p := PerfectRing.ofSurjective k p hsurj
    exact PerfectRing.toPerfectField k p
  · intro _
    rw [eq_top_iff]
    intro x _
    exact ⟨(frobeniusEquiv k p).symm x, frobenius_apply_frobeniusEquiv_symm k p x⟩

/-- An empty family `b : ι → k` is a `p`-basis of `k` if and only if `k` is perfect. -/
theorem isPBasis_of_isEmpty_iff_perfectField [IsEmpty ι] (b : ι → k) :
    IsPBasis p b ↔ PerfectField k := by
  rw [isPBasis_def, and_iff_right (isPIndependent_of_isEmpty p b),
    ← fieldRange_frobenius_eq_top_iff_perfectField]
  have hrange : Set.range (pMonomial p b) = {(1 : k)} := by
    ext x
    simp [eq_comm, Subsingleton.elim _ (0 : ι →₀ Fin p)]
  rw [hrange]
  constructor
  · intro hspan
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span (frobenius k p).fieldRange {(1 : k)} := hspan.symm ▸ trivial
    rcases Submodule.mem_span_singleton.mp hx with ⟨c, rfl⟩
    rw [Subfield.smul_def, smul_eq_mul, mul_one]
    exact c.2
  · intro htop
    rw [eq_top_iff]
    intro x _
    exact Submodule.mem_span_singleton.mpr
      ⟨⟨x, htop.symm ▸ Subfield.mem_top x⟩, by simp [Subfield.smul_def]⟩

/-- Over a perfect field `k` of characteristic `p`, every empty family is a `p`-basis. -/
theorem isPBasis_of_isEmpty [PerfectField k] [IsEmpty ι] (b : ι → k) : IsPBasis p b :=
  (isPBasis_of_isEmpty_iff_perfectField b).mpr ‹_›

/-- For a perfect field `k` of characteristic `p`, `[k : k ^ p] = 1`. -/
@[simp]
theorem finrank_fieldRange_frobenius_of_perfectField [PerfectField k] :
    Module.finrank (frobenius k p).fieldRange k = 1 := by
  simpa using (isPBasis_of_isEmpty (p := p) (Empty.elim : Empty → k)).finrank_fieldRange_frobenius

/-- For a field `k` of characteristic `p`, `[k : k ^ p] = 1` if and only if `k` is perfect. -/
theorem finrank_fieldRange_frobenius_eq_one_iff_perfectField :
    Module.finrank (frobenius k p).fieldRange k = 1 ↔ PerfectField k := by
  refine ⟨fun h1 ↦ ?_, fun _ ↦ finrank_fieldRange_frobenius_of_perfectField⟩
  obtain ⟨s, hs⟩ := exists_isPBasis p k
  have hfd : FiniteDimensional (frobenius k p).fieldRange k :=
    Module.finite_of_finrank_pos (h1 ▸ Nat.one_pos)
  have : Finite s := hs.finite_iff_finiteDimensional.mpr hfd
  cases nonempty_fintype s
  have hpow := hs.finrank_fieldRange_frobenius
  rw [h1] at hpow
  have hcard : Fintype.card s = 0 := by
    by_contra hne
    exact (one_lt_pow₀ hp.out.one_lt hne).ne hpow
  have : IsEmpty s := Fintype.card_eq_zero_iff.mp hcard
  exact (isPBasis_of_isEmpty_iff_perfectField ((↑) : s → k)).mp hs

end PrimeChar

end TauCeti
