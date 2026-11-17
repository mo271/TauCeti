/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Noetherian.Defs
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.ElementaryDivisors.Basic
import TauCeti.LinearAlgebra.Matrix.BilinearForm

/-!
# Alternating elementary divisor theorem over a PID

Every alternating bilinear form `B` on a finite free module `M` over a principal ideal domain `R`
admits a basis in which its Gram matrix is the block matrix

```text
  [  0   D   0 ]
  [ -D   0   0 ]
  [  0   0   0 ]
```

with `D = Matrix.diagonal d` for nonzero elements `d : Fin r → R` forming a divisibility chain
`d₀ ∣ d₁ ∣ ⋯ ∣ d_{r-1}`, in every characteristic (including characteristic two).

The proof uses strong induction on `Module.finrank R M` via a maximal functional range
`J = LinearMap.range (B e)` in the Noetherian ring `R`, avoiding Euclidean division and division
by two.

## Main results

* `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_fromBlocks_zero`: alternating elementary
  divisor theorem over a PID, including singular forms.
* `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_fromBlocks_diagonal`: nondegenerate case.
* `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_fromBlocks_diagonal_of_finrank_eq`:
  fixed-rank version when `Module.finrank R M = 2 * g`.
* `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_of_isPerfPair`: unimodular alternating
  forms over a PID admit a symplectic basis with Gram matrix `Matrix.J`, generalizing
  `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J` from fields to PIDs.
* `LinearMap.BilinForm.IsAlt.isSquare_det_toMatrix`: the Gram determinant of an alternating form
  over a PID is a square, for both singular and nondegenerate forms, in every characteristic.
* `Matrix.exists_isUnit_det_transpose_mul_mul_eq_fromBlocks_zero` and
  `Matrix.exists_isUnit_det_transpose_mul_mul_eq_fromBlocks_diagonal`: congruence normal forms for
  skew-symmetric matrices with zero diagonal over a PID.

## References

* N. Bourbaki, *Algèbre*, Chapitre IX, §5, Théorème 1.
* N. Jacobson, *Basic Algebra I*, second edition, W. H. Freeman, 1985, §3.9.
-/

public section

open Module Submodule

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

section PID

variable {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M]

omit [IsDomain R] in
/-- Choose a nonzero generator `d` of a maximal ideal in `{range (B x) | x : M}` and a witnessing
pair `e, f` with `B e f = d`. -/
private lemma exists_maximal_range_pair {B : BilinForm R M} (hB₀ : B ≠ 0) :
    ∃ (e f : M) (d : R), d ≠ 0 ∧ B e f = d ∧ LinearMap.range (B e) = Ideal.span {d} ∧
      ∀ x : M, Ideal.span {d} ≤ LinearMap.range (B x) →
        LinearMap.range (B x) = Ideal.span {d} := by
  let S : Set (Ideal R) := Set.range fun x : M ↦ LinearMap.range (B x)
  have hne : S.Nonempty := ⟨LinearMap.range (B 0), 0, rfl⟩
  obtain ⟨J, ⟨e, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) S hne
  have hJ₀ : LinearMap.range (B e) ≠ ⊥ := by
    intro hbot
    obtain ⟨x₀, y₀, hxy⟩ : ∃ x₀ y₀, B x₀ y₀ ≠ 0 := by
      by_contra! h
      exact hB₀ (LinearMap.ext₂ h)
    have hlt : LinearMap.range (B e) < LinearMap.range (B x₀) := by
      rw [hbot]
      exact bot_lt_iff_ne_bot.mpr fun hx ↦ hxy (by
        have hmem : B x₀ y₀ ∈ LinearMap.range (B x₀) := ⟨y₀, rfl⟩
        rw [hx] at hmem
        simpa using hmem)
    exact hmax (LinearMap.range (B x₀)) ⟨x₀, rfl⟩ hlt
  let d := Submodule.IsPrincipal.generator (LinearMap.range (B e))
  have hspan : LinearMap.range (B e) = Ideal.span {d} :=
    (Submodule.IsPrincipal.span_singleton_generator (LinearMap.range (B e))).symm
  have hd₀ : d ≠ 0 := by
    intro h
    apply hJ₀
    rw [hspan, h, Ideal.span_singleton_eq_bot]
  have hdmem : d ∈ LinearMap.range (B e) := by
    rw [hspan]
    exact Ideal.subset_span rfl
  obtain ⟨f, hf⟩ := hdmem
  refine ⟨e, f, d, hd₀, hf, hspan, fun x hx ↦ ?_⟩
  by_contra hne'
  have hlt : LinearMap.range (B e) < LinearMap.range (B x) :=
    lt_of_le_of_ne (hspan.symm ▸ hx) fun heq ↦ hne' (heq.symm.trans hspan)
  exact hmax _ ⟨x, rfl⟩ hlt

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- For a maximal pair `(e, f, d)`, the generator `d` divides `B x y` for all
`x, y ∈ ker (B e) ⊓ ker (B f)`. -/
private lemma dvd_apply_of_maximal_range {B : BilinForm R M} (hB : B.IsAlt) {e f : M} {d : R}
    (hef : B e f = d)
    (hmax : ∀ x : M, Ideal.span {d} ≤ LinearMap.range (B x) →
      LinearMap.range (B x) = Ideal.span {d})
    {x y : M} (hx : x ∈ LinearMap.ker (B e) ⊓ LinearMap.ker (B f))
    (hy : y ∈ LinearMap.ker (B e) ⊓ LinearMap.ker (B f)) :
    d ∣ B x y := by
  have hxf : B x f = 0 := by rw [← hB.neg_eq f x, LinearMap.mem_ker.mp hx.2, neg_zero]
  have hey : B e y = 0 := LinearMap.mem_ker.mp hy.1
  have hJex : LinearMap.range (B (e + x)) = Ideal.span {d} :=
    hmax (e + x) ((Submodule.span_singleton_le_iff_mem d _).mpr
      ⟨f, by simp [map_add, LinearMap.add_apply, hef, hxf]⟩)
  have hmem : B x y ∈ Ideal.span {d} := by
    rw [← hJex]
    exact ⟨y, by simp [map_add, LinearMap.add_apply, hey]⟩
  exact Ideal.mem_span_singleton.mp hmem

/-- The splitting linear map `((a, b), z) ↦ a • e + b • f + z`. -/
private def pairSplitMap (e f : M) (N : Submodule R M) : ((R × R) × N) →ₗ[R] M where
  toFun p := p.1.1 • e + p.1.2 • f + (p.2 : M)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul, Submodule.coe_add]
    abel
  map_smul' r p := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_add, Submodule.coe_smul,
      smul_eq_mul, mul_smul]

omit [IsDomain R] [IsPrincipalIdealRing R] in
private lemma pairSplitMap_apply (e f : M) (N : Submodule R M) (a b : R) (z : N) :
    pairSplitMap e f N ((a, b), z) = a • e + b • f + (z : M) :=
  rfl

omit [IsPrincipalIdealRing R] in
private lemma pairSplitMap_injective {B : BilinForm R M} (hB : B.IsAlt) {e f : M} {d : R}
    (hd : d ≠ 0) (hef : B e f = d) :
    Function.Injective (pairSplitMap e f (LinearMap.ker (B e) ⊓ LinearMap.ker (B f))) := by
  have hfe : B f e = -d := by rw [← hB.neg_eq e f, hef]
  rw [injective_iff_map_eq_zero]
  rintro ⟨⟨a, b⟩, z⟩ hz
  rw [pairSplitMap_apply] at hz
  have hze : B e z = 0 := LinearMap.mem_ker.mp z.2.1
  have hzf : B f z = 0 := LinearMap.mem_ker.mp z.2.2
  have hb0 : b = 0 := by
    have h1 := congrArg (B e) hz
    simp only [map_add, map_smul, map_zero, hB.self_eq_zero, hef, hze, smul_eq_mul, mul_zero,
      zero_add, add_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_right hd
  have ha0 : a = 0 := by
    have h2 := congrArg (B f) hz
    simp only [map_add, map_smul, map_zero, hB.self_eq_zero, hfe, hzf, smul_eq_mul, mul_zero,
      add_zero, mul_neg, neg_eq_zero] at h2
    exact (mul_eq_zero.mp h2).resolve_right hd
  have hz0 : z = 0 := Subtype.ext (by simpa [ha0, hb0] using hz)
  simp [ha0, hb0, hz0]

omit [IsDomain R] [IsPrincipalIdealRing R] in
private lemma pairSplitMap_surjective {B : BilinForm R M} (hB : B.IsAlt) {e f : M} {d : R}
    (hef : B e f = d) (hJe : LinearMap.range (B e) = Ideal.span {d})
    (hJf : LinearMap.range (B f) = Ideal.span {d}) :
    Function.Surjective (pairSplitMap e f (LinearMap.ker (B e) ⊓ LinearMap.ker (B f))) := by
  have hfe : B f e = -d := by rw [← hB.neg_eq e f, hef]
  intro v
  have hmem_e : B e v ∈ Ideal.span {d} := by rw [← hJe]; exact ⟨v, rfl⟩
  have hmem_f : B f v ∈ Ideal.span {d} := by rw [← hJf]; exact ⟨v, rfl⟩
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem_e
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton.mp hmem_f
  let zval : M := v - (-a') • e - b • f
  have hze : B e zval = 0 := by
    simp only [zval, map_sub, map_smul, hB.self_eq_zero, hef, smul_eq_mul, mul_zero, sub_zero]
    rw [hb, mul_comm]
    exact sub_self _
  have hzf : B f zval = 0 := by
    simp only [zval, map_sub, map_smul, hB.self_eq_zero, hfe, smul_eq_mul, mul_zero, sub_zero,
      neg_mul, mul_neg, neg_neg]
    rw [ha', mul_comm]
    exact sub_self _
  refine ⟨((-a', b), ⟨zval, LinearMap.mem_ker.mpr hze, LinearMap.mem_ker.mpr hzf⟩), ?_⟩
  rw [pairSplitMap_apply]
  dsimp only [zval]
  abel

omit [IsPrincipalIdealRing R] in
/-- For a maximal pair `(e, f, d)` of an alternating form `B`, the module splits as
`(R × R) × (ker (B e) ⊓ ker (B f))` and `d` divides every value of `B` on the complement. -/
private lemma maximal_range_split {B : BilinForm R M} (hB : B.IsAlt) {e f : M} {d : R}
    (hd : d ≠ 0) (hef : B e f = d) (hJe : LinearMap.range (B e) = Ideal.span {d})
    (hmax : ∀ x : M, Ideal.span {d} ≤ LinearMap.range (B x) →
      LinearMap.range (B x) = Ideal.span {d}) :
    let N : Submodule R M := LinearMap.ker (B e) ⊓ LinearMap.ker (B f)
    (∀ x ∈ N, ∀ y ∈ N, d ∣ B x y) ∧
      ∃ φ : ((R × R) × N) ≃ₗ[R] M,
        ∀ a b z, φ ((a, b), z) = a • e + b • f + (z : M) := by
  intro N
  have hfe : B f e = -d := by rw [← hB.neg_eq e f, hef]
  have hJf : LinearMap.range (B f) = Ideal.span {d} :=
    hmax f ((Submodule.span_singleton_le_iff_mem d _).mpr ⟨-e, by simp [hfe]⟩)
  exact ⟨fun x hx y hy ↦ dvd_apply_of_maximal_range hB hef hmax hx hy,
    LinearEquiv.ofBijective (pairSplitMap e f N)
      ⟨pairSplitMap_injective hB hd hef, pairSplitMap_surjective hB hef hJe hJf⟩,
    fun _ _ _ ↦ rfl⟩

/-- Index bijection assembling a hyperbolic pair `(e, f)` and an alternating block basis of the
orthogonal complement `N` into an alternating block basis of `M`. -/
private def consBlockEquiv (r k : ℕ) :
    (Unit ⊕ Unit) ⊕ ((Fin r ⊕ Fin r) ⊕ Fin k) ≃
      (Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin k where
  toFun
    | Sum.inl (Sum.inl ()) => Sum.inl (Sum.inl 0)
    | Sum.inl (Sum.inr ()) => Sum.inl (Sum.inr 0)
    | Sum.inr (Sum.inl (Sum.inl i)) => Sum.inl (Sum.inl i.succ)
    | Sum.inr (Sum.inl (Sum.inr i)) => Sum.inl (Sum.inr i.succ)
    | Sum.inr (Sum.inr j) => Sum.inr j
  invFun
    | Sum.inl (Sum.inl i) =>
        Fin.cases (Sum.inl (Sum.inl ())) (fun j ↦ Sum.inr (Sum.inl (Sum.inl j))) i
    | Sum.inl (Sum.inr i) =>
        Fin.cases (Sum.inl (Sum.inr ())) (fun j ↦ Sum.inr (Sum.inl (Sum.inr j))) i
    | Sum.inr j => Sum.inr (Sum.inr j)
  left_inv x := by rcases x with (⟨⟩ | ⟨⟩) | ((i | i) | j) <;> rfl
  right_inv x := by
    rcases x with (i | i) | j
    · induction i using Fin.cases <;> rfl
    · induction i using Fin.cases <;> rfl
    · rfl

private noncomputable def consBasis {N : Submodule R M} {r k : ℕ}
    (φ : ((R × R) × N) ≃ₗ[R] M) (b' : Basis ((Fin r ⊕ Fin r) ⊕ Fin k) R N) :
    Basis ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin k) R M :=
  ((((Basis.singleton Unit R).prod (Basis.singleton Unit R)).prod b').map φ).reindex
    (consBlockEquiv r k)

omit [IsDomain R] [IsPrincipalIdealRing R] in
private lemma consBasis_eval {e f : M} {N : Submodule R M} {r k : ℕ}
    (φ : ((R × R) × N) ≃ₗ[R] M)
    (hφ : ∀ a b z, φ ((a, b), z) = a • e + b • f + (z : M))
    (b' : Basis ((Fin r ⊕ Fin r) ⊕ Fin k) R N) :
    consBasis φ b' (Sum.inl (Sum.inl 0)) = e ∧
    consBasis φ b' (Sum.inl (Sum.inr 0)) = f ∧
    (∀ i : Fin r, consBasis φ b' (Sum.inl (Sum.inl i.succ)) = (b' (Sum.inl (Sum.inl i)) : M)) ∧
    (∀ i : Fin r, consBasis φ b' (Sum.inl (Sum.inr i.succ)) = (b' (Sum.inl (Sum.inr i)) : M)) ∧
    (∀ j : Fin k, consBasis φ b' (Sum.inr j) = (b' (Sum.inr j) : M)) := by
  refine ⟨?_, ?_, fun i ↦ ?_, fun i ↦ ?_, fun j ↦ ?_⟩
  · simp [consBasis, consBlockEquiv, hφ]
  · simp [consBasis, consBlockEquiv, hφ]
  · simp [consBasis, consBlockEquiv, hφ]
  · simp [consBasis, consBlockEquiv, hφ]
  · simp [consBasis, consBlockEquiv, hφ]

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Adjoin a pair `(e, f)` with `B e f = d` to a basis `b'` of `N = ker (B e) ⊓ ker (B f)` whose
Gram matrix is the singular alternating block matrix of `d'`, obtaining a basis of `M` whose Gram
matrix is the singular alternating block matrix of `Fin.cons d d'`. -/
private lemma cons_basis_toMatrix {B : BilinForm R M} (hB : B.IsAlt) {e f : M} {d : R}
    (hef : B e f = d) {N : Submodule R M} (hN : N = LinearMap.ker (B e) ⊓ LinearMap.ker (B f))
    (φ : ((R × R) × N) ≃ₗ[R] M)
    (hφ : ∀ a b z, φ ((a, b), z) = a • e + b • f + (z : M))
    {r k : ℕ} {d' : Fin r → R} (b' : Basis ((Fin r ⊕ Fin r) ⊕ Fin k) R N)
    (hb' : (B.restrict N).toMatrix b' = Matrix.fromBlocks
      (Matrix.fromBlocks 0 (Matrix.diagonal d') (-Matrix.diagonal d') 0) 0 0 0) :
    ∃ b : Basis ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin k) R M,
      B.toMatrix b = Matrix.fromBlocks
        (Matrix.fromBlocks 0 (Matrix.diagonal (Fin.cons d d'))
          (-Matrix.diagonal (Fin.cons d d')) 0) 0 0 0 := by
  subst hN
  obtain ⟨hbe, hbf, hbl, hbr, hbk⟩ := consBasis_eval φ hφ b'
  have hfe : B f e = -d := by rw [← hB.neg_eq e f, hef]
  have hez : ∀ z : ↥(LinearMap.ker (B e) ⊓ LinearMap.ker (B f)), B e z = 0 :=
    fun z ↦ LinearMap.mem_ker.mp z.2.1
  have hfz : ∀ z : ↥(LinearMap.ker (B e) ⊓ LinearMap.ker (B f)), B f z = 0 :=
    fun z ↦ LinearMap.mem_ker.mp z.2.2
  have hze : ∀ z : ↥(LinearMap.ker (B e) ⊓ LinearMap.ker (B f)), B z e = 0 :=
    fun z ↦ by rw [← hB.neg_eq e z, hez, neg_zero]
  have hzf : ∀ z : ↥(LinearMap.ker (B e) ⊓ LinearMap.ker (B f)), B z f = 0 :=
    fun z ↦ by rw [← hB.neg_eq f z, hfz, neg_zero]
  have hB' : ∀ x y, B (b' x) (b' y) = Matrix.fromBlocks
      (Matrix.fromBlocks (0 : Matrix (Fin r) (Fin r) R)
        (Matrix.diagonal d') (-Matrix.diagonal d') 0) 0 0 0 x y := fun x y ↦ by
    simpa [toMatrix_apply] using congrFun (congrFun hb' x) y
  refine ⟨consBasis φ b', ?_⟩
  ext x y
  rw [toMatrix_apply]
  rcases x with (i | i) | j <;> rcases y with (i' | i') | j'
  · induction i using Fin.cases <;> induction i' using Fin.cases <;>
      simp [hbe, hbl, hB.self_eq_zero, hez, hze, hB']
  · induction i using Fin.cases <;> induction i' using Fin.cases <;>
      simp [hbe, hbf, hbl, hbr, hef, hez, hzf, hB', Matrix.diagonal_apply, Fin.ext_iff]
  · induction i using Fin.cases <;> simp [hbe, hbl, hbk, hez, hB']
  · induction i using Fin.cases <;> induction i' using Fin.cases <;>
      simp [hbe, hbf, hbl, hbr, hfe, hfz, hze, hB', Matrix.diagonal_apply, Fin.ext_iff]
  · induction i using Fin.cases <;> induction i' using Fin.cases <;>
      simp [hbf, hbr, hB.self_eq_zero, hfz, hzf, hB']
  · induction i using Fin.cases <;> simp [hbf, hbr, hbk, hfz, hB']
  · induction i' using Fin.cases <;> simp [hbe, hbl, hbk, hze, hB']
  · induction i' using Fin.cases <;> simp [hbf, hbr, hbk, hzf, hB']
  · simp [hbk, hB']

omit [IsPrincipalIdealRing R] in
/-- Base case (`B = 0`) of the alternating elementary divisor theorem. -/
private lemma exists_basis_toMatrix_zero_form [Module.Free R M] [Module.Finite R M]
    {n : ℕ} (hn : Module.finrank R M = n) :
    ∃ (r k : ℕ) (d : Fin r → R) (b : Basis ((Fin r ⊕ Fin r) ⊕ Fin k) R M),
      (∀ i, d i ≠ 0) ∧ (∀ ⦃i j : Fin r⦄, i ≤ j → d i ∣ d j) ∧
      (0 : BilinForm R M).toMatrix b = Matrix.fromBlocks
        (Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) 0 0 0 := by
  let b₀ := Module.Free.chooseBasis R M
  let e : Module.Free.ChooseBasisIndex R M ≃ (Fin 0 ⊕ Fin 0) ⊕ Fin n :=
    (Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis b₀, hn])).trans
      (Equiv.emptySum (Fin 0 ⊕ Fin 0) (Fin n)).symm
  refine ⟨0, n, Fin.elim0, b₀.reindex e, fun i ↦ i.elim0, fun i ↦ i.elim0, ?_⟩
  ext x y
  rcases x with (i | i) | j
  · exact i.elim0
  · exact i.elim0
  · rcases y with (i' | i') | j'
    · exact i'.elim0
    · exact i'.elim0
    · simp [toMatrix_apply]

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Prepends `d` to a divisibility chain `d'` when `d` divides every `d' j`. -/
private lemma fin_cons_dvd_chain {r : ℕ} {d : R} {d' : Fin r → R}
    (hd : ∀ j, d ∣ d' j) (hd' : ∀ ⦃i j : Fin r⦄, i ≤ j → d' i ∣ d' j) :
    ∀ ⦃i j : Fin (r + 1)⦄, i ≤ j →
      (Fin.cons d d' : Fin (r + 1) → R) i ∣ (Fin.cons d d' : Fin (r + 1) → R) j := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact dvd_rfl
    | succ j => simpa using hd j
  | succ i =>
    induction j using Fin.cases with
    | zero => exact (Fin.not_lt_zero _ (lt_of_lt_of_le (Fin.succ_pos i) hij)).elim
    | succ j => exact hd' (Fin.succ_le_succ_iff.mp hij)

/-- Inductive proof of the alternating elementary divisor theorem over a PID, indexed by the rank
`n = Module.finrank R M`. -/
private theorem exists_basis_toMatrix_eq_fromBlocks_zero_aux (n : ℕ) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M],
      Module.finrank R M = n → ∀ (B : BilinForm R M), B.IsAlt →
      ∃ (r k : ℕ) (d : Fin r → R) (b : Basis ((Fin r ⊕ Fin r) ⊕ Fin k) R M),
        (∀ i, d i ≠ 0) ∧ (∀ ⦃i j : Fin r⦄, i ≤ j → d i ∣ d j) ∧
        B.toMatrix b = Matrix.fromBlocks
          (Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) 0 0 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ _ _ _ hn B hB
    by_cases hB₀ : B = 0
    · subst hB₀; exact exists_basis_toMatrix_zero_form hn
    · obtain ⟨e, f, d, hd₀, hef, hJe, hmax⟩ := exists_maximal_range_pair hB₀
      let N : Submodule R M := LinearMap.ker (B e) ⊓ LinearMap.ker (B f)
      obtain ⟨hdvd, φ, hφ⟩ := maximal_range_split hB hd₀ hef hJe hmax
      have : Module.Finite R N := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N)
      have hfinN : Module.finrank R N + 2 = n := by
        have h : Module.finrank R ((R × R) × N) = Module.finrank R M := φ.finrank_eq
        rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, hn] at h
        omega
      obtain ⟨r, k, d', b', hd'₀, hd'chain, hb'⟩ :=
        ih (Module.finrank R N) (by omega) N rfl (B.restrict N) (fun z ↦ hB.self_eq_zero z)
      obtain ⟨b, hb⟩ := cons_basis_toMatrix hB hef rfl φ hφ b' hb'
      refine ⟨r + 1, k, Fin.cons d d', b, ?_, fin_cons_dvd_chain ?_ hd'chain, hb⟩
      · intro i; induction i using Fin.cases with | zero => exact hd₀ | succ i => exact hd'₀ i
      · intro j
        have hval : d' j = B (b' (Sum.inl (Sum.inl j))) (b' (Sum.inl (Sum.inr j))) := by
          simpa [toMatrix_apply] using
            (congrFun (congrFun hb' (Sum.inl (Sum.inl j))) (Sum.inl (Sum.inr j))).symm
        rw [hval]
        exact hdvd _ (b' (Sum.inl (Sum.inl j))).2 _ (b' (Sum.inl (Sum.inr j))).2

section FreeFinite

variable [Module.Free R M] [Module.Finite R M]

/-- **Alternating elementary divisor theorem over a PID (general, possibly singular case).**
Every alternating bilinear form `B` on a finite free module `M` over a principal ideal domain `R`
has a basis indexed by `(Fin r ⊕ Fin r) ⊕ Fin k` in which its Gram matrix is
`fromBlocks [[0, D], [-D, 0]] 0 0 0` with `D = Matrix.diagonal d`, every `d i ≠ 0`, and
`d i ∣ d j` for `i ≤ j`. Holds in every characteristic, including characteristic two. -/
theorem IsAlt.exists_basis_toMatrix_eq_fromBlocks_zero {B : BilinForm R M} (hB : B.IsAlt) :
    ∃ (r k : ℕ) (d : Fin r → R) (b : Basis ((Fin r ⊕ Fin r) ⊕ Fin k) R M),
      (∀ i, d i ≠ 0) ∧ (∀ ⦃i j : Fin r⦄, i ≤ j → d i ∣ d j) ∧
      B.toMatrix b = Matrix.fromBlocks
        (Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0) 0 0 0 :=
  exists_basis_toMatrix_eq_fromBlocks_zero_aux (Module.finrank R M) M rfl B hB

/-- **Alternating elementary divisor theorem over a PID (nondegenerate case).** Every nondegenerate
alternating bilinear form `B` on a finite free module `M` over a principal ideal domain `R` has a
symplectic basis indexed by `Fin g ⊕ Fin g` in which its Gram matrix is
`Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0` with nonzero `d : Fin g → R`
forming a divisibility chain `d₀ ∣ d₁ ∣ ⋯ ∣ d_{g-1}`. -/
theorem IsAlt.exists_basis_toMatrix_eq_fromBlocks_diagonal {B : BilinForm R M} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) :
    ∃ (g : ℕ) (d : Fin g → R) (b : Basis (Fin g ⊕ Fin g) R M),
      (∀ i, d i ≠ 0) ∧ (∀ ⦃i j : Fin g⦄, i ≤ j → d i ∣ d j) ∧
      B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0 := by
  obtain ⟨r, k, d, b, hd₀, hdchain, hb⟩ := hB.exists_basis_toMatrix_eq_fromBlocks_zero
  have hk : k = 0 := by
    have hker := finrank_ker_eq_card_of_toMatrix_eq_fromBlocks_zero
      (fun i ↦ mem_nonZeroDivisors_of_ne_zero (hd₀ i)) hb
    rw [hnd.ker_eq_bot, finrank_bot, Fintype.card_fin] at hker
    exact hker.symm
  subst hk
  let e : (Fin r ⊕ Fin r) ⊕ Fin 0 ≃ Fin r ⊕ Fin r := Equiv.sumEmpty _ _
  refine ⟨r, d, b.reindex e, hd₀, hdchain, ?_⟩
  ext x y
  rw [toMatrix_reindex, Matrix.reindex_apply, Matrix.submatrix_apply, hb]
  rcases x with i | i <;> rcases y with j | j <;> simp [e]

/-- Fixed-rank version of `IsAlt.exists_basis_toMatrix_eq_fromBlocks_diagonal` when
`Module.finrank R M = 2 * g`. -/
theorem IsAlt.exists_basis_toMatrix_eq_fromBlocks_diagonal_of_finrank_eq {B : BilinForm R M}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) {g : ℕ} (hdim : Module.finrank R M = 2 * g) :
    ∃ (d : Fin g → R) (b : Basis (Fin g ⊕ Fin g) R M),
      (∀ i, d i ≠ 0) ∧ (∀ ⦃i j : Fin g⦄, i ≤ j → d i ∣ d j) ∧
      B.toMatrix b = Matrix.fromBlocks 0 (Matrix.diagonal d) (-Matrix.diagonal d) 0 := by
  obtain ⟨r, d, b, hd₀, hdchain, hb⟩ := hB.exists_basis_toMatrix_eq_fromBlocks_diagonal hnd
  have hr : r = g := by
    have := Module.finrank_eq_card_basis b
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  subst hr
  exact ⟨d, b, hd₀, hdchain, hb⟩

/-- **Symplectic basis for unimodular alternating forms over a PID.** A unimodular alternating form
(i.e. a perfect pairing) on a finite free module over a principal ideal domain has a basis indexed
by `Fin g ⊕ Fin g` in which its Gram matrix is `Matrix.J (Fin g) R`. This generalizes
`LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J` from fields to principal ideal domains. -/
theorem IsAlt.exists_basis_toMatrix_eq_J_of_isPerfPair {B : BilinForm R M} (hB : B.IsAlt)
    (hperf : B.IsPerfPair) :
    ∃ (g : ℕ) (b : Basis (Fin g ⊕ Fin g) R M), B.toMatrix b = Matrix.J (Fin g) R := by
  have hnd : B.Nondegenerate :=
    nondegenerate_iff_ker_eq_bot.mpr (LinearMap.ker_eq_bot.mpr hperf.bijective_left.injective)
  obtain ⟨g, d, b, -, -, hb⟩ := hB.exists_basis_toMatrix_eq_fromBlocks_diagonal hnd
  have hunit := (isPerfPair_iff_forall_isUnit_of_toMatrix_eq_fromBlocks_diagonal hb).mp hperf
  obtain ⟨b', hb'⟩ := exists_basis_toMatrix_eq_J_of_toMatrix_eq_fromBlocks_diagonal hb hunit
  exact ⟨g, b', hb'⟩

end FreeFinite

/-- **The Gram determinant of an alternating form over a PID is a square**, for both singular and
nondegenerate forms, in every characteristic. -/
theorem IsAlt.isSquare_det_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : BilinForm R M} (hB : B.IsAlt) (c : Basis ι R M) : IsSquare (B.toMatrix c).det := by
  have : Module.Free R M := .of_basis c
  have : Module.Finite R M := .of_basis c
  by_cases hdet : (B.toMatrix c).det = 0
  · exact hdet ▸ IsSquare.zero
  · have hnd : B.Nondegenerate := (nondegenerate_iff_det_ne_zero c).mpr hdet
    obtain ⟨g, d, b, -, -, hb⟩ := hB.exists_basis_toMatrix_eq_fromBlocks_diagonal hnd
    obtain ⟨u, hu⟩ := exists_det_toMatrix_eq_unit_sq_mul_prod_sq hb c
    exact ⟨(u : R) * ∏ i, d i, by rw [hu]; ring⟩

end PID

end LinearMap.BilinForm

namespace Matrix

/-- **Congruence normal form for skew-symmetric matrices with zero diagonal over a PID.** Every
matrix `A` with `Aᵀ = -A` and `A i i = 0` is congruent via a matrix `P` of unit determinant to the
reindexed alternating block matrix `fromBlocks [[0, D], [-D, 0]] 0 0 0`, with nonzero `d` forming a
divisibility chain. -/
theorem exists_isUnit_det_transpose_mul_mul_eq_fromBlocks_zero {R ι : Type*}
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι R} (hA : Aᵀ = -A) (hd : ∀ i, A i i = 0) :
    ∃ (r k : ℕ) (e : (Fin r ⊕ Fin r) ⊕ Fin k ≃ ι) (d : Fin r → R) (P : Matrix ι ι R),
      IsUnit P.det ∧ (∀ i, d i ≠ 0) ∧ (∀ ⦃i j : Fin r⦄, i ≤ j → d i ∣ d j) ∧
      Pᵀ * A * P = reindex e e
        (fromBlocks (fromBlocks 0 (diagonal d) (-diagonal d) 0) 0 0 0) := by
  have halt : A.toBilin'.IsAlt := (isAlt_toBilin'_iff A).mpr ⟨hA, hd⟩
  obtain ⟨r, k, d, b, hd₀, hdchain, hb⟩ := halt.exists_basis_toMatrix_eq_fromBlocks_zero
  let e : (Fin r ⊕ Fin r) ⊕ Fin k ≃ ι := b.indexEquiv (Pi.basisFun R ι)
  let c := b.reindex e
  have hkey := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun R ι) c A.toBilin'
  rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin',
    LinearMap.BilinForm.toMatrix_reindex, hb] at hkey
  refine ⟨r, k, e, d, (Pi.basisFun R ι).toMatrix c,
    isUnit_det_of_right_inverse ((Pi.basisFun R ι).toMatrix_mul_toMatrix_flip c),
    hd₀, hdchain, hkey⟩

/-- **Congruence normal form for nonsingular skew-symmetric matrices with zero diagonal over a
PID.** -/
theorem exists_isUnit_det_transpose_mul_mul_eq_fromBlocks_diagonal {R ι : Type*}
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι R} (hA : Aᵀ = -A) (hd : ∀ i, A i i = 0) (hdet : A.det ≠ 0) :
    ∃ (g : ℕ) (e : Fin g ⊕ Fin g ≃ ι) (d : Fin g → R) (P : Matrix ι ι R),
      IsUnit P.det ∧ (∀ i, d i ≠ 0) ∧ (∀ ⦃i j : Fin g⦄, i ≤ j → d i ∣ d j) ∧
      Pᵀ * A * P = reindex e e (fromBlocks 0 (diagonal d) (-diagonal d) 0) := by
  have halt : A.toBilin'.IsAlt := (isAlt_toBilin'_iff A).mpr ⟨hA, hd⟩
  have hnd : A.toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  obtain ⟨g, d, b, hd₀, hdchain, hb⟩ := halt.exists_basis_toMatrix_eq_fromBlocks_diagonal hnd
  let e : Fin g ⊕ Fin g ≃ ι := b.indexEquiv (Pi.basisFun R ι)
  let c := b.reindex e
  have hkey := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun R ι) c A.toBilin'
  rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin',
    LinearMap.BilinForm.toMatrix_reindex, hb] at hkey
  refine ⟨g, e, d, (Pi.basisFun R ι).toMatrix c,
    isUnit_det_of_right_inverse ((Pi.basisFun R ι).toMatrix_mul_toMatrix_flip c),
    hd₀, hdchain, hkey⟩

end Matrix
