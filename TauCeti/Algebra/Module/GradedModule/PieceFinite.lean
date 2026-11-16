/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Coarsen
public import TauCeti.RingTheory.GradedAlgebra.FiniteType
public import TauCeti.RingTheory.MvPolynomial.Finrank
import TauCeti.Algebra.DirectSum.Internal

/-!
# Piecewise finiteness and degree lower bounds for graded modules

Let `M` be a finitely generated `B`-module carrying an internal `ℤ`-grading by `R`-submodules.

* When `B` has an internal `ℤ`-decomposition `𝒜` compatible with `M` whose negative-degree pieces
  vanish, only finitely many degrees occur among the homogeneous components of a finite
  `B`-generating set of `M`, so the nonzero homogeneous pieces of `M` are bounded below
  (`TauCeti.InternalGrading.bddBelow_setOf_piece_ne_bot`, dual to
  `TauCeti.InternalGrading.bddAbove_setOf_piece_ne_bot` for degree-lowering polynomial actions).
* Independently of any nonnegativity assumption on `𝒜`, if every piece `𝒜 i` is a finite `R`-module
  and `R`, `B`, `M` form a scalar tower, then every piece `G.piece d` is a finite `R`-module
  (`TauCeti.InternalGrading.piece_finite`): if `g₁, …, gₙ` are homogeneous `B`-generators of `M` of
  degrees `q₁, …, qₙ`, then `M_d = ∑ₖ B_{d - qₖ} • gₖ`.

Both results hold over arbitrary (possibly noncommutative, non-Noetherian) semirings `R` and `B`.
Coarsening an `ℕ`-indexed decomposition `ℬ : ℕ → Submodule R B` along `(Nat.cast : ℕ → ℤ)` transfers
both conclusions to `ℕ`-graded algebras, in particular to `MvPolynomial σ R` for `[Finite σ]` and to
any `ℕ`-graded `R`-algebra `B` of finite type over `ℬ 0` with `[Module.Finite R (ℬ 0)]` (including
every finite-type `R`-algebra with `B₀ = R`).

## Main results

* `TauCeti.InternalGrading.exists_fin_mem_piece_and_span_eq_top`: a finitely generated `B`-module
  has finitely many homogeneous `B`-generators.
* `TauCeti.InternalGrading.bddBelow_setOf_piece_ne_bot` and
  `TauCeti.InternalGrading.exists_piece_eq_bot_of_lt`: degree lower bound over a nonnegatively
  graded scalar semiring.
* `TauCeti.InternalGrading.piece_finite`: piece-by-piece `R`-module finiteness when the scalar
  semiring has `R`-finite graded pieces.
* `TauCeti.gradedPiecesFinite_of_decomposition`, `TauCeti.gradedPiecesFinite_mvPolynomial`,
  `TauCeti.gradedPiecesFinite`, and `TauCeti.gradedPiecesFinite_of_gradeZero_le_bot`: piecewise
  finiteness and uniform lower degree bound for `ℕ`-graded algebras.
-/

public section

namespace TauCeti

namespace InternalGrading

section HomogeneousGenerators

variable {R M ι : Type*} [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]

/-- A finitely generated `B`-module equipped with an internal `R`-grading admits a finite family of
homogeneous elements whose `B`-span is the whole module. No compatibility between the `B`-action and
the grading is needed. -/
theorem exists_fin_mem_piece_and_span_eq_top (G : InternalGrading R M ι)
    (B : Type*) [Semiring B] [Module B M] [Module.Finite B M] :
    ∃ (n : ℕ) (deg : Fin n → ι) (g : Fin n → M),
      (∀ i, g i ∈ G.piece (deg i)) ∧ Submodule.span B (Set.range g) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := M)
  let I := Σ x : s, (DirectSum.decompose G.piece x.1).support
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let val (p : I) : M := (DirectSum.decompose G.piece p.1.1 p.2.1 : M)
  refine ⟨Fintype.card I, fun i ↦ (e i).2.1, fun i ↦ val (e i),
    fun i ↦ (DirectSum.decompose G.piece (e i).1.1 (e i).2.1).2, ?_⟩
  rw [← top_le_iff, ← hs, Submodule.span_le]
  intro x hx
  rw [← DirectSum.sum_support_decompose G.piece x]
  refine Submodule.sum_mem _ fun q hq ↦ Submodule.subset_span ?_
  refine ⟨e.symm ⟨⟨x, hx⟩, ⟨q, hq⟩⟩, ?_⟩
  change val (e (e.symm ⟨⟨x, hx⟩, ⟨q, hq⟩⟩)) = _
  rw [Equiv.apply_symm_apply]

end HomogeneousGenerators

section IntGraded

variable {R B M : Type*} [Semiring R] [Semiring B] [Module R B]
  [AddCommMonoid M] [Module R M] [Module B M]
  (𝒜 : ℤ → Submodule R B) [DirectSum.Decomposition 𝒜]
  (G : InternalGrading R M ℤ) [SetLike.GradedSMul 𝒜 G.piece]

/-- A finitely generated `B`-module over a nonnegatively `ℤ`-graded semiring `B` has homogeneous
degrees bounded below. -/
theorem bddBelow_setOf_piece_ne_bot [Module.Finite B M] (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) :
    BddBelow {p : ℤ | G.piece p ≠ ⊥} := by
  classical
  obtain ⟨n, deg, g, hmem, hspan⟩ := G.exists_fin_mem_piece_and_span_eq_top B
  obtain ⟨d₀, hd₀⟩ := (Set.finite_range deg).bddBelow
  refine ⟨d₀, fun p hp ↦ ?_⟩
  by_contra! hlt
  refine hp ((Submodule.eq_bot_iff _).2 fun x hx ↦ ?_)
  obtain ⟨k, c, u, rfl⟩ := Submodule.mem_span_set'.1
    (hspan ▸ Submodule.mem_top : x ∈ Submodule.span B (Set.range g))
  rw [← DirectSum.decompose_of_mem_same G.piece hx, DirectSum.decompose_sum,
    DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  obtain ⟨i, hi⟩ := (u j).2
  have hgi : (u j : M) ∈ G.piece (deg i) := hi ▸ hmem i
  have hcomp := DirectSum.coe_decompose_smul_add_of_right_mem 𝒜 G.piece hgi
    (a := c j) (i := p - deg i)
  rw [sub_add_cancel] at hcomp
  have hdeg : d₀ ≤ deg i := hd₀ ⟨i, rfl⟩
  have hzero : (DirectSum.decompose 𝒜 (c j) (p - deg i) : B) = 0 :=
    (Submodule.eq_bot_iff _).1 (h𝒜 (p - deg i) (by omega)) _
      (DirectSum.decompose 𝒜 (c j) (p - deg i)).2
  rw [hcomp, hzero, zero_smul]

/-- A finitely generated `B`-module over a nonnegatively `ℤ`-graded semiring `B` vanishes in all
degrees below a uniform threshold `d₀`. -/
theorem exists_piece_eq_bot_of_lt [Module.Finite B M] (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) :
    ∃ d₀ : ℤ, ∀ d < d₀, G.piece d = ⊥ := by
  obtain ⟨d₀, hd₀⟩ := G.bddBelow_setOf_piece_ne_bot 𝒜 h𝒜
  refine ⟨d₀, fun d hd ↦ ?_⟩
  by_contra hne
  exact (hd₀ hne).not_gt hd

/-- If `M` is a finitely generated `B`-module and every piece `𝒜 i` of `B` is a finite `R`-module,
then every homogeneous piece `G.piece d` of `M` is a finite `R`-module. Nonnegativity of the grading
on `B` is not required. -/
theorem piece_finite [IsScalarTower R B M] [Module.Finite B M]
    (hfin : ∀ i : ℤ, Module.Finite R (𝒜 i)) (d : ℤ) :
    Module.Finite R (G.piece d) := by
  classical
  obtain ⟨n, deg, g, hmem, hspan⟩ := G.exists_fin_mem_piece_and_span_eq_top B
  let smulMap (i : Fin n) : B →ₗ[R] M :=
    { toFun b := b • g i
      map_add' b₁ b₂ := add_smul b₁ b₂ (g i)
      map_smul' r b := smul_assoc r b (g i) }
  let C : Submodule R M := ⨆ i : Fin n, (𝒜 (d - deg i)).map (smulMap i)
  have hC_le : C ≤ G.piece d := iSup_le fun i ↦ Submodule.map_le_iff_le_comap.2 fun b hb ↦ by
    rw [Submodule.mem_comap]
    simpa only [smulMap, LinearMap.coe_mk, AddHom.coe_mk, vadd_eq_add, sub_add_cancel] using
      SetLike.GradedSMul.smul_mem hb (hmem i)
  have hle_C : G.piece d ≤ C := fun x hx ↦ by
    obtain ⟨k, c, u, rfl⟩ := Submodule.mem_span_set'.1
      (hspan ▸ Submodule.mem_top : x ∈ Submodule.span B (Set.range g))
    rw [← DirectSum.decompose_of_mem_same G.piece hx, DirectSum.decompose_sum,
      DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
    refine C.sum_mem fun j _ ↦ ?_
    obtain ⟨i, hi⟩ := (u j).2
    have hgi : (u j : M) ∈ G.piece (deg i) := hi ▸ hmem i
    have hcomp := DirectSum.coe_decompose_smul_add_of_right_mem 𝒜 G.piece hgi
      (a := c j) (i := d - deg i)
    rw [sub_add_cancel] at hcomp
    rw [hcomp, ← hi]
    exact Submodule.mem_iSup_of_mem i
      (Submodule.mem_map.2 ⟨(DirectSum.decompose 𝒜 (c j) (d - deg i) : B),
        (DirectSum.decompose 𝒜 (c j) (d - deg i)).2, rfl⟩)
  rw [Module.Finite.iff_fg, le_antisymm hle_C hC_le]
  exact Submodule.fg_iSup _ fun i ↦ (Module.Finite.iff_fg.1 (hfin (d - deg i))).map (smulMap i)

end IntGraded

end InternalGrading

section NatGraded

/-- Let `B` be an `ℕ`-graded `R`-semiring whose graded pieces `ℬ i` are finite `R`-modules, and let
`M` be a finitely generated `B`-module with an internal `ℤ`-decomposition `ℳ` into `R`-submodules
compatible with `ℬ`. Then every `ℳ d` is a finite `R`-module and `ℳ d = ⊥` for all `d < d₀`. -/
theorem gradedPiecesFinite_of_decomposition {R B M : Type*} [Semiring R] [Semiring B]
    [Module R B] [AddCommMonoid M] [Module R M] [Module B M] [IsScalarTower R B M]
    (ℬ : ℕ → Submodule R B) [DirectSum.Decomposition ℬ] [Module.Finite B M]
    (hfin : ∀ i : ℕ, Module.Finite R (ℬ i))
    (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
    (hsmul : ∀ (i : ℕ) (j : ℤ), ∀ b ∈ ℬ i, ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i)) :
    (∀ d : ℤ, Module.Finite R (ℳ d)) ∧ ∃ d₀ : ℤ, ∀ d < d₀, ℳ d = ⊥ := by
  let 𝒜 : ℤ → Submodule R B := coarsenGrading ℬ (Nat.cast : ℕ → ℤ)
  have h𝒜_neg (i : ℤ) (hi : i < 0) : 𝒜 i = ⊥ :=
    coarsenGrading_eq_bot_of_forall_ne ℬ fun n hn ↦ (Int.natCast_nonneg n).not_gt (hn ▸ hi)
  have h𝒜_nat (n : ℕ) : 𝒜 (n : ℤ) = ℬ n :=
    coarsenGrading_apply_of_injective ℬ Nat.cast_injective n
  have h𝒜_fin (i : ℤ) : Module.Finite R (𝒜 i) := by
    rcases lt_or_ge i 0 with hi | hi
    · rw [h𝒜_neg i hi]
      infer_instance
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      rw [h𝒜_nat n]
      exact hfin n
  have : SetLike.GradedSMul 𝒜 (InternalGrading.ofDecomposition ℳ).piece :=
    { smul_mem := fun {i j b m} hb hm ↦
        coarsenGrading_induction hb
          (fun n hn b' hb' ↦ by
            subst hn
            rw [InternalGrading.ofDecomposition_piece] at hm ⊢
            simpa only [vadd_eq_add, add_comm (n : ℤ) j] using hsmul n j b' hb' m hm)
          (by simp)
          (fun x y hx hy ↦ by
            simpa only [add_smul, vadd_eq_add] using
              ((InternalGrading.ofDecomposition ℳ).piece (i + j)).add_mem hx hy) }
  refine ⟨fun d ↦ ?_, ?_⟩
  · have h := (InternalGrading.ofDecomposition ℳ).piece_finite 𝒜 h𝒜_fin d
    rwa [InternalGrading.ofDecomposition_piece] at h
  · simpa only [InternalGrading.ofDecomposition_piece] using
      (InternalGrading.ofDecomposition ℳ).exists_piece_eq_bot_of_lt 𝒜 h𝒜_neg

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- Over `MvPolynomial σ R` in finitely many variables `[Finite σ]`, every finitely generated
`ℤ`-graded module has `R`-finite homogeneous pieces and vanishes below a uniform degree `d₀`. -/
theorem gradedPiecesFinite_mvPolynomial {R σ M : Type*} [CommSemiring R] [Finite σ]
    [AddCommMonoid M] [Module R M] [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M] [Module.Finite (MvPolynomial σ R) M]
    (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
    (hsmul : ∀ (i : ℕ) (j : ℤ), ∀ b ∈ MvPolynomial.homogeneousSubmodule σ R i, ∀ m ∈ ℳ j,
      b • m ∈ ℳ (j + i)) :
    (∀ d : ℤ, Module.Finite R (ℳ d)) ∧ ∃ d₀ : ℤ, ∀ d < d₀, ℳ d = ⊥ :=
  gradedPiecesFinite_of_decomposition (MvPolynomial.homogeneousSubmodule σ R)
    homogeneousSubmodule_moduleFinite ℳ hsmul

/-- Let `B` be an `ℕ`-graded commutative `R`-algebra of finite type over `ℬ 0` with `ℬ 0` finite
over `R` (in particular any graded `R`-algebra `[Algebra.FiniteType R B]` with
`[Module.Finite R (ℬ 0)]`). Every finitely generated `ℤ`-graded `B`-module has `R`-finite
homogeneous pieces and vanishes below a uniform degree `d₀`, without assuming `R` is Noetherian. -/
theorem gradedPiecesFinite {R B M : Type*} [CommSemiring R] [CommSemiring B] [Algebra R B]
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [Algebra.FiniteType (ℬ 0) B] [Module.Finite R (ℬ 0)]
    [AddCommMonoid M] [Module R M] [Module B M] [IsScalarTower R B M] [Module.Finite B M]
    (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
    (hsmul : ∀ (i : ℕ) (j : ℤ), ∀ b ∈ ℬ i, ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i)) :
    (∀ d : ℤ, Module.Finite R (ℳ d)) ∧ ∃ d₀ : ℤ, ∀ d < d₀, ℳ d = ⊥ :=
  gradedPiecesFinite_of_decomposition ℬ (GradedAlgebra.finite_grade ℬ) ℳ hsmul

/-- Specialization of `gradedPiecesFinite` when `B` is of finite type over `R` and `ℬ 0` consists of
scalars from `R`: every homogeneous piece of a finitely generated `ℤ`-graded `B`-module is a finite
`R`-module and the pieces vanish below a uniform degree `d₀`. -/
theorem gradedPiecesFinite_of_gradeZero_le_bot {R B M : Type*} [CommSemiring R] [CommSemiring B]
    [Algebra R B] (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] [Algebra.FiniteType R B]
    (hℬ₀ : ∀ x ∈ ℬ 0, x ∈ (⊥ : Subalgebra R B))
    [AddCommMonoid M] [Module R M] [Module B M] [IsScalarTower R B M] [Module.Finite B M]
    (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
    (hsmul : ∀ (i : ℕ) (j : ℤ), ∀ b ∈ ℬ i, ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i)) :
    (∀ d : ℤ, Module.Finite R (ℳ d)) ∧ ∃ d₀ : ℤ, ∀ d < d₀, ℳ d = ⊥ := by
  have : Module.Finite R (ℬ 0) := GradedAlgebra.finite_gradeZero_of_forall_mem_bot ℬ hℬ₀
  exact gradedPiecesFinite ℬ ℳ hsmul

end NatGraded

end TauCeti
