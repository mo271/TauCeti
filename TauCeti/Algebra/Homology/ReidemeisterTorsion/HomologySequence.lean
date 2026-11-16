/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Homology
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Interleave
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.Algebra.Homology.ShortComplex.Splitting
import TauCeti.LinearAlgebra.Alternating.Append
import TauCeti.LinearAlgebra.Exact

/-!
# Multiplicativity of Reidemeister torsion with homology bases

Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of `ℤ`-graded chain complexes of
vector spaces over a field `F`, with compatible chain bases `c₁`, `c₃`, `c₂` and ordered bases
`b₁`, `b₂`, `b₃` of the homology groups. Its long exact homology sequence is the acyclic chain
complex `CategoryTheory.ShortComplex.ShortExact.homologySequenceComplex`, with `Hᵢ(S.X₁)`,
`Hᵢ(S.X₂)` and `Hᵢ(S.X₃)` in degrees `3i + 2`, `3i + 1` and `3i`. Ordered bases of the homology
groups assemble into ordered bases `ChainComplex.interleave.basis` of its terms, whose Reidemeister
torsion is nonzero if and only if only finitely many homology groups of `S.X₁` and `S.X₃` are
nonzero
(`CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero_iff`,
`CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero`).

This file proves Milnor's multiplicativity formula for Reidemeister torsion with homology bases
(`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact`):

`τ(S.X₂, c₂, b₂) = ε · τ(S.X₁, c₁, b₁) · τ(S.X₃, c₃, b₃) · τ(H, B)`,

where `H` is `hS.homologySequenceComplex`, `B` is `ChainComplex.interleave.basis`, and the Koszul
sign in degree `j` is

`(-1) ^ (dim B₃,ⱼ₊₁ · (dim im Hⱼ₊₁(S.f) + dim B₁,ⱼ) + dim im Hⱼ₊₁(S.g) · dim B₁,ⱼ)`.

Combined with `ChainComplex.interleave.reidemeisterTorsion_basis_eq_mul` and the homology
basis-change law `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology`,
the multiplicativity identity is invariant under changes of `(b₁, b₂, b₃)`, reducing it to adapted
homology bases where `τ(H, B) = 1` (`ChainComplex.interleave.reidemeisterTorsion_basis_eq_one`).
In each degree `j`, the cycles `Pⱼ` of `S.X₁` whose homology class lies in `ker Hⱼ(S.f)` fit into
two short exact sequences `0 → B₁,ⱼ → Pⱼ → im δⱼ → 0` and `0 → Pⱼ → B₂,ⱼ → B₃,ⱼ → 0`; lifting along
`δⱼ` via `CategoryTheory.ShortComplex.ShortExact.moduleCat_exists_d_eq_of_δ_eq` and reordering the
three interleaved pairs of blocks in `S.X₂` via `AlternatingMap.map_append_append_append_comm`
factors each bracket of `S.X₂` into the product of the brackets of `S.X₁` and `S.X₃`.

Three specializations follow directly:
* when the homology bases `b₁`, `b₃`, `b₂` are themselves compatible with `Hᵢ(S.f)` and `Hᵢ(S.g)`,
  the connecting homomorphisms vanish, `τ(H, B) = 1`, and the Koszul sign involves `dim Hⱼ₊₁(S.X₁)`
  and `dim Hⱼ₊₁(S.X₃)`
  (`HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_homologyMap`);
* for a direct sum `C₁ ⊞ C₃` based by `HomologicalComplex.biprodXBasis` and
  `HomologicalComplex.biprodHomologyBasis`
  (`HomologicalComplex.reidemeisterTorsionWithHomology_biprod`);
* when the middle complex `S.X₂` is acyclic, `S.X₂.reidemeisterTorsion c₂` is expressed in terms of
  `τ(S.X₁, c₁, b₁)`, `τ(S.X₃, c₃, b₃)` and the alternating product of the determinants of the
  connecting isomorphisms `δᵢ : Hᵢ₊₁(S.X₃) → Hᵢ(S.X₁)`
  (`HomologicalComplex.reidemeisterTorsion_eq_mul_reidemeisterTorsionWithHomology_of_shortExact`,
  using `HomologicalComplex.card_homology_eq_of_exactAt`).

## Main declarations

* `CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero_iff`:
  the based long exact homology sequence has nonzero torsion iff `H(S.X₁)` and `H(S.X₃)` are
  finitely supported.
* `CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero`: the
  based long exact homology sequence has nonzero torsion when `H(S.X₁)` and `H(S.X₃)` are finitely
  supported.
* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact`: Milnor's
  multiplicativity formula for Reidemeister torsion with homology bases.
* `HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_homologyMap`:
  multiplicativity when both chain and homology bases are compatible with the short exact sequence.
* `HomologicalComplex.reidemeisterTorsionWithHomology_biprod`: torsion with homology bases of a
  direct sum of complexes.
* `HomologicalComplex.card_homology_eq_of_exactAt`: exactness of `S.X₂` at `i + 1` and `i` equates
  the dimensions of `Hᵢ(S.X₁)` and `Hᵢ₊₁(S.X₃)`.
* `HomologicalComplex.reidemeisterTorsion_eq_mul_reidemeisterTorsionWithHomology_of_shortExact`:
  torsion of an acyclic middle complex in terms of the outer torsions with homology bases and the
  connecting isomorphisms.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3, Theorem 3.2.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, Theorems 1.5, 1.14 and
  2.2.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Appendix A.
-/

public section

noncomputable section

open CategoryTheory Module

private theorem append_cast_castAdd {α : Type*} {m n m' n' : ℕ} (hm : m' = m) (hn : n' = n)
    {h : m' + n' = m + n} (a : Fin m → α) (b : Fin n → α) (i : Fin m') :
    Fin.append a b (Fin.cast h (Fin.castAdd n' i)) = a (Fin.cast hm i) := by
  subst hm hn; simp

private theorem append_cast_natAdd {α : Type*} {m n m' n' : ℕ} (hm : m' = m) (hn : n' = n)
    {h : m' + n' = m + n} (a : Fin m → α) (b : Fin n → α) (j : Fin n') :
    Fin.append a b (Fin.cast h (Fin.natAdd m' j)) = b (Fin.cast hn j) := by
  subst hm hn; simp

private theorem funext_comp_cast_iff {α : Type*} {p q : ℕ} (h : p = q) (f : Fin p → α)
    (g : Fin q → α) :
    f = g ∘ Fin.cast h ↔ ∀ m : Fin q, f (Fin.cast h.symm m) = g m :=
  ⟨fun hf m ↦ by simp [hf], fun hf ↦ funext fun k ↦ by simpa using hf (Fin.cast h k)⟩

private theorem comp_cast_eq_comp_cast {α : Type*} {n m₁ m₂ : ℕ} {h₁ : n = m₁} {h₂ : n = m₂}
    {v₁ : Fin m₁ → α} {v₂ : Fin m₂ → α}
    (hv : ∀ k : Fin m₂, v₁ (Fin.cast (h₂.symm.trans h₁) k) = v₂ k) :
    v₁ ∘ Fin.cast h₁ = v₂ ∘ Fin.cast h₂ :=
  funext fun i ↦ hv (Fin.cast h₂ i)

namespace CategoryTheory.ShortComplex.ShortExact

variable {F : Type*} [Field F] {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
  (hS : S.ShortExact) {m₁ m₂ m₃ : ℤ → ℕ} (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
  (b₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
  (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))

/-- The long exact homology sequence, based by ordered bases of the homology groups, has nonzero
Reidemeister torsion if and only if only finitely many homology groups of `S.X₁` and `S.X₃` are
nonempty. -/
theorem reidemeisterTorsion_homologySequenceComplex_ne_zero_iff :
    hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) ≠ 0 ↔
      {i | m₁ i ≠ 0}.Finite ∧ {i | m₃ i ≠ 0}.Finite := by
  refine ⟨fun hne ↦ ?_, fun ⟨h₁, h₃⟩ ↦ ?_⟩
  · have hr : {n | ChainComplex.interleave.rank m₁ m₂ m₃ n ≠ 0}.Finite := by
      by_contra hr
      exact hne (HomologicalComplex.reidemeisterTorsion_of_not_finite _ _ hr)
    obtain ⟨h₁, _, h₃⟩ := ChainComplex.interleave.finite_setOf_rank_ne_zero_iff.1 hr
    exact ⟨h₁, h₃⟩
  · have h₂ : {i | m₂ i ≠ 0}.Finite :=
      (h₁.union h₃).subset fun i hi ↦ by
        simp only [Set.mem_union, Set.mem_ofPred_eq] at hi ⊢
        have : Module.Finite F (S.X₁.homology i) := .of_basis (b₁ i)
        have : Module.Finite F (S.X₂.homology i) := .of_basis (b₂ i)
        have : Module.Finite F (S.X₃.homology i) := .of_basis (b₃ i)
        have hker : LinearMap.range (HomologicalComplex.homologyMap S.f i).hom =
            LinearMap.ker (HomologicalComplex.homologyMap S.g i).hom :=
          (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (hS.homology_exact₂ i)
        have hrk :=
          LinearMap.finrank_range_add_finrank_ker (HomologicalComplex.homologyMap S.g i).hom
        have hle₁ := LinearMap.finrank_range_le (HomologicalComplex.homologyMap S.f i).hom
        have hle₃ := Submodule.finrank_le
          (LinearMap.range (HomologicalComplex.homologyMap S.g i).hom)
        rw [← hker, finrank_eq_card_basis (b₂ i), Fintype.card_fin] at hrk
        rw [finrank_eq_card_basis (b₁ i), Fintype.card_fin] at hle₁
        rw [finrank_eq_card_basis (b₃ i), Fintype.card_fin] at hle₃
        omega
    exact HomologicalComplex.reidemeisterTorsion_ne_zero _ _
      (ChainComplex.interleave.finite_setOf_rank_ne_zero h₁ h₂ h₃)
      hS.acyclic_homologySequenceComplex

/-- The long exact homology sequence, based by ordered bases of the homology groups, has nonzero
Reidemeister torsion when only finitely many homology groups of `S.X₁` and `S.X₃` are nonempty. -/
theorem reidemeisterTorsion_homologySequenceComplex_ne_zero (h₁ : {i | m₁ i ≠ 0}.Finite)
    (h₃ : {i | m₃ i ≠ 0}.Finite) :
    hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) ≠ 0 :=
  (hS.reidemeisterTorsion_homologySequenceComplex_ne_zero_iff b₁ b₂ b₃).2 ⟨h₁, h₃⟩

end CategoryTheory.ShortComplex.ShortExact

namespace HomologicalComplex

variable {F : Type*} [Field F]

section BoundaryWithHomology

/-! ### Boundary bases of the middle term of a short exact sequence -/

/-- The submodule `Pⱼ ⊆ Zⱼ(S.X₁)` of degree-`j` cycles of `S.X₁` whose homology class lies in the
kernel of `homologyMap S.f j`, equivalently whose image in `S.X₂` is a boundary. -/
private def kerHomologyMapSubmodule (S : ShortComplex (ChainComplex (ModuleCat F) ℤ)) (j : ℤ) :
    Submodule F (LinearMap.ker (S.X₁.d j (j - 1)).hom) :=
  LinearMap.ker ((homologyMap S.f j).hom ∘ₗ
    S.X₁.moduleCatKerHomologyClass ((ComplexShape.down ℤ).next_eq' (by simp)))

/-- A cycle `z` of `S.X₁` lies in `kerHomologyMapSubmodule` if and only if its image in `S.X₂` is
a boundary. -/
private theorem mem_kerHomologyMapSubmodule_iff {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
    {j : ℤ} (z : LinearMap.ker (S.X₁.d j (j - 1)).hom) :
    z ∈ kerHomologyMapSubmodule S j ↔
      (S.f.f j).hom z.1 ∈ LinearMap.range (S.X₂.d (j + 1) j).hom := by
  have hm : (ComplexShape.down ℤ).next j = j - 1 := (ComplexShape.down ℤ).next_eq' (by simp)
  have hp : (ComplexShape.down ℤ).prev j = j + 1 := (ComplexShape.down ℤ).prev_eq' (by simp)
  rw [kerHomologyMapSubmodule, LinearMap.mem_ker, LinearMap.comp_apply,
    homologyMap_moduleCatKerHomologyClass hm S.f z,
    (S.X₂.exact_inclusion_moduleCatKerHomologyClass hm hp) _]
  exact ⟨fun ⟨b, hb⟩ ↦ by
      have h : (b : S.X₂.X j) = (S.f.f j).hom z.1 := by simpa using congrArg Subtype.val hb
      exact h ▸ b.2,
    fun hb ↦ ⟨⟨_, hb⟩, rfl⟩⟩

/-- Inclusion of `Bⱼ(S.X₁)` into `kerHomologyMapSubmodule S j`. -/
private def boundaryToKerHomologyMap (S : ShortComplex (ChainComplex (ModuleCat F) ℤ)) (j : ℤ) :
    LinearMap.range (S.X₁.d (j + 1) j).hom →ₗ[F] kerHomologyMapSubmodule S j :=
  (Submodule.inclusion (S.X₁.range_d_le_ker_d j (j + 1) (j - 1))).codRestrict _ fun b ↦ by
    have hm : (ComplexShape.down ℤ).next j = j - 1 := (ComplexShape.down ℤ).next_eq' (by simp)
    have hp : (ComplexShape.down ℤ).prev j = j + 1 := (ComplexShape.down ℤ).prev_eq' (by simp)
    rw [kerHomologyMapSubmodule, LinearMap.mem_ker, LinearMap.comp_apply,
      (S.X₁.exact_inclusion_moduleCatKerHomologyClass hm hp).apply_apply_eq_zero b, map_zero]

/-- Inclusion of `kerHomologyMapSubmodule S j` into `Bⱼ(S.X₂)`. -/
private def kerHomologyMapToBoundary (S : ShortComplex (ChainComplex (ModuleCat F) ℤ)) (j : ℤ) :
    kerHomologyMapSubmodule S j →ₗ[F] LinearMap.range (S.X₂.d (j + 1) j).hom :=
  ((S.f.f j).hom ∘ₗ (LinearMap.ker (S.X₁.d j (j - 1)).hom).subtype ∘ₗ
    (kerHomologyMapSubmodule S j).subtype).codRestrict _ fun z ↦
    (mem_kerHomologyMapSubmodule_iff z.1).1 z.2

variable {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)

/-- Projection from `kerHomologyMapSubmodule S j` to `im δⱼ = ker Hⱼ(S.f)`. -/
private def kerHomologyMapToRangeDelta (j : ℤ) :
    kerHomologyMapSubmodule S j →ₗ[F] LinearMap.range (hS.δ (j + 1) j rfl).hom :=
  (S.X₁.moduleCatKerHomologyClass ((ComplexShape.down ℤ).next_eq' (by simp)) ∘ₗ
    (kerHomologyMapSubmodule S j).subtype).codRestrict _ fun z ↦ by
    rw [(ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (hS.homology_exact₁ (j + 1) j rfl)]
    exact z.2

private theorem exact_boundaryToKerHomologyMap (j : ℤ) :
    Function.Exact (boundaryToKerHomologyMap S j) (kerHomologyMapToRangeDelta hS j) := by
  have hm : (ComplexShape.down ℤ).next j = j - 1 := (ComplexShape.down ℤ).next_eq' (by simp)
  have hp : (ComplexShape.down ℤ).prev j = j + 1 := (ComplexShape.down ℤ).prev_eq' (by simp)
  intro z
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero]
  exact ⟨fun hz ↦ by
      obtain ⟨b, hb⟩ := ((S.X₁.exact_inclusion_moduleCatKerHomologyClass hm hp) z.1).1 hz
      exact ⟨b, Subtype.ext hb⟩,
    fun ⟨b, hb⟩ ↦ by
      rw [← hb]
      exact (S.X₁.exact_inclusion_moduleCatKerHomologyClass hm hp).apply_apply_eq_zero b⟩

include hS in
private theorem exact_kerHomologyMapToBoundary (j : ℤ) :
    Function.Exact (kerHomologyMapToBoundary S j) (S.g.boundaryMap (j + 1) j) := by
  have hS' := (shortExact_iff_degreewise_shortExact S).1 hS
  have hf (i : ℤ) : Function.Injective (S.f.f i).hom := (hS' i).moduleCat_injective_f
  have hfg (i : ℤ) : Function.Exact (S.f.f i).hom (S.g.f i).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hS' i).exact
  intro w
  refine ⟨fun hw ↦ ?_, fun ⟨z, hz⟩ ↦ ?_⟩
  · obtain ⟨x₁, hx₁⟩ := (hfg j w.1).1
      ((Hom.coe_boundaryMap S.g (j + 1) j w).symm.trans (congrArg Subtype.val hw))
    have hdx₁ : x₁ ∈ LinearMap.ker (S.X₁.d j (j - 1)).hom := by
      rw [LinearMap.mem_ker]
      apply hf (j - 1)
      obtain ⟨y₂, hy₂⟩ := w.2
      rw [← Hom.comm_apply, hx₁, ← hy₂, d_comp_d_apply, map_zero]
    exact ⟨⟨⟨x₁, hdx₁⟩, (mem_kerHomologyMapSubmodule_iff ⟨x₁, hdx₁⟩).2 (hx₁.symm ▸ w.2)⟩,
      Subtype.ext hx₁⟩
  · rw [← hz]
    exact Subtype.ext ((Hom.coe_boundaryMap S.g (j + 1) j _).trans ((hfg j).apply_apply_eq_zero _))

private theorem boundaryToKerHomologyMap_injective
    (S : ShortComplex (ChainComplex (ModuleCat F) ℤ)) (j : ℤ) :
    Function.Injective (boundaryToKerHomologyMap S j) := fun _ _ h ↦
  Submodule.inclusion_injective _ (congrArg Subtype.val h)

include hS in
private theorem kerHomologyMapToBoundary_injective (j : ℤ) :
    Function.Injective (kerHomologyMapToBoundary S j) := fun _ _ h ↦
  Subtype.ext (Subtype.ext
    (((shortExact_iff_degreewise_shortExact S).1 hS j).moduleCat_injective_f
      (congrArg Subtype.val h)))

/-- The basis of `Bⱼ(S.X₂)` built from a basis `b'` of `Bⱼ(S.X₁)`, cycle representatives `zu` of a
basis `u` of `im δⱼ`, and lifts `t` to `S.X₂.X (j + 1)` of a basis `b''` of `Bⱼ(S.X₃)`. -/
private def shortExactBoundaryBasisWithHomology {j : ℤ} {p' α p'' : ℕ}
    (b' : Basis (Fin p') F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (u : Basis (Fin α) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (zu : Fin α → S.X₁.cycles j) (hzu : ∀ k, S.X₁.homologyπ j (zu k) = u k)
    (b'' : Basis (Fin p'') F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t : Fin p'' → S.X₂.X (j + 1))
    (ht : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t k)) = b'' k) :
    Basis (Fin (p' + α + p'')) F (LinearMap.range (S.X₂.d (j + 1) j).hom) :=
  let hm : (ComplexShape.down ℤ).next j = j - 1 := (ComplexShape.down ℤ).next_eq' (by simp)
  let zu' (k : Fin α) : kerHomologyMapSubmodule S j :=
    ⟨S.X₁.moduleCatCyclesToKer j (j - 1) (zu k), by
      rw [kerHomologyMapSubmodule, LinearMap.mem_ker, LinearMap.comp_apply,
        S.X₁.moduleCatKerHomologyClass_moduleCatCyclesToKer hm, hzu k]
      obtain ⟨w, hw⟩ := (u k).2
      rw [← hw, ← ModuleCat.comp_apply, hS.δ_comp (j + 1) j rfl]
      simp⟩
  let bP : Basis (Fin (p' + α)) F (kerHomologyMapSubmodule S j) :=
    (Basis.ofExactLift (boundaryToKerHomologyMap_injective S j)
      (exact_boundaryToKerHomologyMap hS j) b' u zu' fun k ↦
        Subtype.ext ((S.X₁.moduleCatKerHomologyClass_moduleCatCyclesToKer hm (zu k)).trans (hzu k))
      ).reindex finSumFinEquiv
  (Basis.ofExactLift (kerHomologyMapToBoundary_injective hS j)
    (exact_kerHomologyMapToBoundary hS j) bP b''
    (fun k ↦ ⟨(S.X₂.d (j + 1) j).hom (t k), t k, rfl⟩)
    fun k ↦ Subtype.ext ((Hom.coe_boundaryMap S.g (j + 1) j _).trans
      ((Hom.comm_apply S.g (j + 1) j (t k)).symm.trans (ht k)))).reindex finSumFinEquiv

private theorem coe_shortExactBoundaryBasisWithHomology {j : ℤ} {p' α p'' : ℕ}
    (b' : Basis (Fin p') F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (u : Basis (Fin α) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (zu : Fin α → S.X₁.cycles j) (hzu : ∀ k, S.X₁.homologyπ j (zu k) = u k)
    (b'' : Basis (Fin p'') F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t : Fin p'' → S.X₂.X (j + 1))
    (ht : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t k)) = b'' k) :
    (fun k ↦ (shortExactBoundaryBasisWithHomology hS b' u zu hzu b'' t ht k : S.X₂.X j)) =
      Fin.append (Fin.append (fun k ↦ (S.f.f j).hom (b' k))
        fun k ↦ (S.f.f j).hom (S.X₁.iCycles j (zu k)))
        (fun k ↦ (S.X₂.d (j + 1) j).hom (t k)) := by
  change Subtype.val ∘ ⇑(shortExactBoundaryBasisWithHomology hS b' u zu hzu b'' t ht) = _
  dsimp only [shortExactBoundaryBasisWithHomology]
  rw [Basis.coe_reindex_ofExactLift, Basis.coe_reindex_ofExactLift]
  ext k
  induction k using Fin.addCases with
  | left k =>
    induction k using Fin.addCases with
    | left k => simp only [Function.comp_apply, Fin.append_left]; rfl
    | right k =>
      simp only [Function.comp_apply, Fin.append_left, Fin.append_right]
      exact congrArg (S.f.f j).hom (S.X₁.coe_moduleCatCyclesToKer j (j - 1) (zu k))
  | right k => simp only [Function.comp_apply, Fin.append_right]

private theorem shortExactBoundaryLift_spec {j : ℤ} {p' α p'' : ℕ}
    (b' : Basis (Fin p') F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (s' : Fin p' → S.X₁.X (j + 1)) (hs' : ∀ k, (S.X₁.d (j + 1) j).hom (s' k) = b' k)
    (u : Basis (Fin α) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (zu : Fin α → S.X₁.cycles j) (hzu : ∀ k, S.X₁.homologyπ j (zu k) = u k)
    (xhat : Fin α → S.X₂.X (j + 1))
    (hxhat : ∀ k, (S.X₂.d (j + 1) j).hom (xhat k) = (S.f.f j).hom (S.X₁.iCycles j (zu k)))
    (b'' : Basis (Fin p'') F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t : Fin p'' → S.X₂.X (j + 1))
    (ht : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t k)) = b'' k)
    (k : Fin (p' + α + p'')) :
    (S.X₂.d (j + 1) j).hom
      (Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (s' k)) xhat) t k) =
      shortExactBoundaryBasisWithHomology hS b' u zu hzu b'' t ht k := by
  rw [congrFun (coe_shortExactBoundaryBasisWithHomology hS b' u zu hzu b'' t ht) k]
  induction k using Fin.addCases with
  | left k => induction k using Fin.addCases <;> simp [Hom.comm_apply, hxhat, hs']
  | right k => simp

end BoundaryWithHomology

section BracketShortExact

/-- The dimension `n (j + 1)` of `Cⱼ₊₁` is the sum of the dimensions of `Bⱼ₊₁`, `Hⱼ₊₁`, and
`Bⱼ`. -/
private theorem card_X_eq_add_add {C : ChainComplex (ModuleCat F) ℤ} {n : ℤ → ℕ}
    (c : ∀ i, Basis (Fin (n i)) F (C.X i)) {j : ℤ} {p m q : ℕ}
    (b₁ : Basis (Fin p) F (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom))
    (h : Basis (Fin m) F (C.homology (j + 1)))
    (b₀ : Basis (Fin q) F (LinearMap.range (C.d (j + 1) j).hom)) :
    n (j + 1) = p + m + q := by
  have : Module.Finite F (C.X (j + 1)) := .of_basis (c (j + 1))
  have hZ := (C.exact_inclusion_moduleCatKerHomologyClass
    ((ComplexShape.down ℤ).next_eq' (i := j + 1) (j := j) (by simp))
    (ChainComplex.prev ℤ (j + 1))).finrank_eq_add (Submodule.inclusion_injective _)
    (C.moduleCatKerHomologyClass_surjective _)
  have hX := LinearMap.finrank_range_add_finrank_ker (C.d (j + 1) j).hom
  rw [finrank_eq_card_basis b₁, finrank_eq_card_basis h] at hZ
  rw [finrank_eq_card_basis b₀, finrank_eq_card_basis (c (j + 1))] at hX
  simp only [Fintype.card_fin] at hZ hX
  omega

/-- In a short exact sequence `0 → A → B → C → 0` with compatible bases `a`, `c`, `b`, the
determinant with respect to `b` of a concatenation `(f ∘ x, z)` where `g ∘ z = y` factors as
`a.det (x ∘ Fin.cast hm) * c.det (y ∘ Fin.cast hn)`. -/
private theorem det_append_eq_mul_of_exact {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module F A] [Module F B] [Module F C] {f : A →ₗ[F] B} {g : B →ₗ[F] C}
    (hf : Function.Injective f) (hfg : Function.Exact f g) {m n m' n' : ℕ}
    (a : Basis (Fin m) F A) (c : Basis (Fin n) F C) (b : Basis (Fin (m + n)) F B)
    (hb : ∀ k, b (Fin.castAdd n k) = f (a k)) (hb' : ∀ k, g (b (Fin.natAdd m k)) = c k)
    (hm : m = m') (hn : n = n') (x : Fin m' → A) (y : Fin n' → C) (z : Fin n' → B)
    (hz : ∀ k, g (z k) = y k) :
    (b.reindex (finCongr (congrArg₂ (· + ·) hm hn))).det (Fin.append (f ∘ x) z) =
      a.det (x ∘ Fin.cast hm) * c.det (y ∘ Fin.cast hn) := by
  subst hm hn
  rw [finCongr_refl, Basis.reindex_refl, Basis.eq_reindex_ofExactLift hf hfg a c b hb hb',
    Basis.det_reindex]
  exact Basis.ofExactLift_det_eq_mul hf hfg a c _ hb' x y _ (by simp) (by simp [hz])

/-- Reassociating `(((x, y), z), w)` into `((x, (y, z)), w)` up to `Fin.cast`. -/
private theorem append_append_right_assoc {α : Type*} {p q r s : ℕ}
    (x : Fin p → α) (y : Fin q → α) (z : Fin r → α) (w : Fin s → α) :
    Fin.append (Fin.append (Fin.append x y) z) w =
      Fin.append (Fin.append x (Fin.append y z)) w ∘ Fin.cast (by omega) := by
  rw [Fin.append_assoc x y z, Fin.append_cast_left]

/-- Reassociating `((x, y), (z, w))` into `((x, (y, z)), w)` up to `Fin.cast`. -/
private theorem append_append_left_assoc {α : Type*} {p q r s : ℕ}
    (x : Fin p → α) (y : Fin q → α) (z : Fin r → α) (w : Fin s → α) :
    Fin.append (Fin.append x y) (Fin.append z w) =
      Fin.append (Fin.append x (Fin.append y z)) w ∘ Fin.cast (by omega) := by
  have h := (Fin.append_assoc (Fin.append x y) z w).symm.trans (append_append_right_assoc x y z w)
  ext k
  simpa using congrFun h (Fin.cast (Nat.add_assoc (p + q) r s).symm k)

/-- Factor a determinant of six interleaved blocks in a short exact sequence `0 → A → B → C → 0`
into the product of the determinants on `A` and `C`, with Koszul sign. -/
private theorem det_interleaved_shortExact {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module F A] [Module F B] [Module F C] {f : A →ₗ[F] B} {g : B →ₗ[F] C}
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    {n₁ n₃ p'₁ α₁ β₁ p'₀ p''₁ γ₁ α₀ p''₀ : ℕ}
    (c₁ : Basis (Fin n₁) F A) (c₃ : Basis (Fin n₃) F C) (c₂ : Basis (Fin (n₁ + n₃)) F B)
    (hc₁ : ∀ k, c₂ (Fin.castAdd n₃ k) = f (c₁ k))
    (hc₃ : ∀ k, g (c₂ (Fin.natAdd n₁ k)) = c₃ k)
    (hn₁ : n₁ = p'₁ + (α₁ + β₁) + p'₀) (hn₃ : n₃ = p''₁ + (γ₁ + α₀) + p''₀)
    (x₁ : Fin p'₁ → A) (u₁ : Fin α₁ → A) (v₁ : Fin β₁ → A) (z₁ : Fin p'₀ → A)
    (x₂ : Fin p''₁ → B) (w₂ : Fin γ₁ → B) (u₂ : Fin α₀ → B) (z₂ : Fin p''₀ → B)
    (x₃ : Fin p''₁ → C) (u₃ : Fin α₀ → C)
    (hx₃ : ∀ k, g (x₂ k) = x₃ k) (hu₃ : ∀ k, g (u₂ k) = u₃ k) :
    c₂.det (Fin.append
        (Fin.append (Fin.append (Fin.append (f ∘ x₁) (f ∘ u₁)) x₂) (Fin.append (f ∘ v₁) w₂))
        (Fin.append (f ∘ z₁) (Fin.append u₂ z₂)) ∘ Fin.cast (by omega)) =
      (-1 : F) ^ (p''₁ * (β₁ + p'₀) + γ₁ * p'₀) *
        (c₁.det (Fin.append (Fin.append x₁ (Fin.append u₁ v₁)) z₁ ∘ Fin.cast hn₁) *
          c₃.det (Fin.append (Fin.append x₃ (Fin.append (g ∘ w₂) u₃)) (g ∘ z₂) ∘
            Fin.cast hn₃)) := by
  have hm₁ : n₁ = (p'₁ + α₁) + β₁ + p'₀ := by omega
  have hm₃ : n₃ = p''₁ + γ₁ + (α₀ + p''₀) := by omega
  have hsw := (c₂.reindex (finCongr (congrArg₂ (· + ·) hm₁ hm₃))).det.map_append_append_append_comm
    (Fin.append (f ∘ x₁) (f ∘ u₁)) (f ∘ v₁) (f ∘ z₁) x₂ w₂ (Fin.append u₂ z₂)
  rw [Basis.det_reindex] at hsw
  rw [show Fin.cast (by omega : n₁ + n₃ =
        p'₁ + α₁ + p''₁ + (β₁ + γ₁) + (p'₀ + (α₀ + p''₀))) =
      Fin.cast (by omega) ∘ finCongr (congrArg₂ (· + ·) hm₁ hm₃) from funext fun _ ↦ by simp,
    ← Function.comp_assoc, hsw]
  have hmap : Fin.append (Fin.append (Fin.append (f ∘ x₁) (f ∘ u₁)) (f ∘ v₁)) (f ∘ z₁) =
      f ∘ Fin.append (Fin.append (Fin.append x₁ u₁) v₁) z₁ := by
    ext k
    induction k using Fin.addCases with
    | left k =>
      induction k using Fin.addCases with
      | left k => induction k using Fin.addCases <;> simp
      | right k => simp
    | right k => simp
  rw [hmap, det_append_eq_mul_of_exact hf hfg c₁ c₃ c₂ hc₁ hc₃ hm₁ hm₃ _
    (Fin.append (Fin.append x₃ (g ∘ w₂)) (Fin.append u₃ (g ∘ z₂))) _ (fun k ↦ by
      induction k using Fin.addCases with
      | left k => induction k using Fin.addCases <;> simp [hx₃]
      | right k => induction k using Fin.addCases <;> simp [hu₃])]
  simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one]
  congr 2
  · congr 1; rw [append_append_right_assoc]; ext k; simp
  · congr 1; rw [append_append_left_assoc]; ext k; simp

/-- **Degreewise bracket factorization.** In adapted homology bases where `τ(H, B) = 1`, the
bracket of `S.X₂` in degree `j + 1` is the product of the brackets of `S.X₁` and `S.X₃`, up to the
Koszul sign `(-1) ^ (p''₁ * (β₁ + p'₀) + γ₁ * p'₀)`. -/
private theorem torsionBracketWithHomology_shortExact
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) {j : ℤ}
    {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    {p'₁ p'₀ p''₁ p''₀ α₁ α₀ β₁ γ₁ : ℕ}
    (b'₁ : Basis (Fin p'₁) F (LinearMap.range (S.X₁.d (j + 1 + 1) (j + 1)).hom))
    (b'₀ : Basis (Fin p'₀) F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (s'₀ : Fin p'₀ → S.X₁.X (j + 1)) (hs'₀ : ∀ k, (S.X₁.d (j + 1) j).hom (s'₀ k) = b'₀ k)
    (b''₁ : Basis (Fin p''₁) F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom))
    (b''₀ : Basis (Fin p''₀) F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t₁ : Fin p''₁ → S.X₂.X (j + 1 + 1))
    (ht₁ : ∀ k, (S.X₃.d (j + 1 + 1) (j + 1)).hom ((S.g.f (j + 1 + 1)).hom (t₁ k)) = b''₁ k)
    (t₀ : Fin p''₀ → S.X₂.X (j + 1))
    (ht₀ : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t₀ k)) = b''₀ k)
    (u₁ : Basis (Fin α₁) F (LinearMap.range (hS.δ (j + 1 + 1) (j + 1) rfl).hom))
    (zu₁ : Fin α₁ → S.X₁.cycles (j + 1)) (hzu₁ : ∀ k, S.X₁.homologyπ (j + 1) (zu₁ k) = u₁ k)
    (u₀ : Basis (Fin α₀) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (zu₀ : Fin α₀ → S.X₁.cycles j) (hzu₀ : ∀ k, S.X₁.homologyπ j (zu₀ k) = u₀ k)
    (xhat : Fin α₀ → S.X₂.X (j + 1)) (zu₃ : Fin α₀ → S.X₃.cycles (j + 1))
    (hxhat : ∀ k, (S.X₂.d (j + 1) j).hom (xhat k) = (S.f.f j).hom (S.X₁.iCycles j (zu₀ k)))
    (hzu₃ : ∀ k, (S.g.f (j + 1)).hom (xhat k) = S.X₃.iCycles (j + 1) (zu₃ k))
    (zv : Fin β₁ → S.X₁.cycles (j + 1)) (zw : Fin γ₁ → S.X₂.cycles (j + 1))
    (h₁ : Basis (Fin (α₁ + β₁)) F (S.X₁.homology (j + 1)))
    (hh₁ : ∀ k, S.X₁.homologyπ (j + 1) (Fin.append zu₁ zv k) = h₁ k)
    (h₂ : Basis (Fin (β₁ + γ₁)) F (S.X₂.homology (j + 1)))
    (hh₂ : ∀ k, S.X₂.homologyπ (j + 1)
      (Fin.append (fun k ↦ cyclesMap S.f (j + 1) (zv k)) zw k) = h₂ k)
    (h₃ : Basis (Fin (γ₁ + α₀)) F (S.X₃.homology (j + 1)))
    (hh₃ : ∀ k, S.X₃.homologyπ (j + 1)
      (Fin.append (fun k ↦ cyclesMap S.g (j + 1) (zw k)) zu₃ k) = h₃ k) :
    torsionBracketWithHomology c₂
        (shortExactBoundaryBasisWithHomology hS b'₁ u₁ zu₁ hzu₁ b''₁ t₁ ht₁) h₂ _ hh₂
        (shortExactBoundaryBasisWithHomology hS b'₀ u₀ zu₀ hzu₀ b''₀ t₀ ht₀) _
        (shortExactBoundaryLift_spec hS b'₀ s'₀ hs'₀ u₀ zu₀ hzu₀ xhat hxhat b''₀ t₀ ht₀) =
      (-1 : F) ^ (p''₁ * (β₁ + p'₀) + γ₁ * p'₀) *
        (torsionBracketWithHomology c₁ b'₁ h₁ _ hh₁ b'₀ s'₀ hs'₀ *
          torsionBracketWithHomology c₃ b''₁ h₃ _ hh₃ b''₀
            (fun k ↦ (S.g.f (j + 1)).hom (t₀ k)) ht₀) := by
  have hS' := (shortExact_iff_degreewise_shortExact S).1 hS (j + 1)
  have hn₁ := card_X_eq_add_add c₁ b'₁ h₁ b'₀
  have hn₃ := card_X_eq_add_add c₃ b''₁ h₃ b''₀
  rw [torsionBracketWithHomology_eq_det_append c₂ _ h₂ _ hh₂ _ _ _ (by omega),
    coe_shortExactBoundaryBasisWithHomology,
    torsionBracketWithHomology_eq_det_append c₁ b'₁ h₁ _ hh₁ b'₀ s'₀ hs'₀ hn₁,
    torsionBracketWithHomology_eq_det_append c₃ b''₁ h₃ _ hh₃ b''₀ _ ht₀ hn₃]
  refine Eq.trans ?_ ((det_interleaved_shortExact (f := (S.f.f (j + 1)).hom)
    (g := (S.g.f (j + 1)).hom) hS'.moduleCat_injective_f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS'.exact)
    (c₁ (j + 1)) (c₃ (j + 1)) (c₂ (j + 1)) (hc₁ (j + 1)) (hc₃ (j + 1)) hn₁ hn₃
    (fun k ↦ (b'₁ k : S.X₁.X (j + 1))) (fun k ↦ S.X₁.iCycles (j + 1) (zu₁ k))
    (fun k ↦ S.X₁.iCycles (j + 1) (zv k)) s'₀
    (fun k ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t₁ k))
    (fun k ↦ S.X₂.iCycles (j + 1) (zw k)) xhat t₀
    (fun k ↦ (b''₁ k : S.X₃.X (j + 1))) (fun k ↦ S.X₃.iCycles (j + 1) (zu₃ k))
    (fun k ↦ by rw [← Hom.comm_apply, ht₁]) hzu₃).trans ?_)
  · congr 1
    refine comp_cast_eq_comp_cast fun m ↦ ?_
    induction m using Fin.addCases with
    | left m =>
      rw [append_cast_castAdd rfl (Nat.add_assoc p'₀ α₀ p''₀).symm, Fin.append_left]
      simp only [Fin.cast_eq_self]
      induction m using Fin.addCases with
      | left m => rw [Fin.append_left, Fin.append_left]; rfl
      | right m =>
        rw [Fin.append_right, Fin.append_right]
        induction m using Fin.addCases <;> simp
    | right m =>
      rw [append_cast_natAdd rfl (Nat.add_assoc p'₀ α₀ p''₀).symm, Fin.append_right,
        Fin.append_assoc]
      simp; rfl
  · congr 2
    · congr 1
      have h : (fun k ↦ S.X₁.iCycles (j + 1) (Fin.append zu₁ zv k)) =
          Fin.append (fun k ↦ S.X₁.iCycles (j + 1) (zu₁ k))
            (fun k ↦ S.X₁.iCycles (j + 1) (zv k)) := by
        ext k; induction k using Fin.addCases <;> simp
      rw [h]
    · congr 1
      have h : (fun k ↦ S.X₃.iCycles (j + 1)
          (Fin.append (fun k ↦ cyclesMap S.g (j + 1) (zw k)) zu₃ k)) =
          Fin.append ((S.g.f (j + 1)).hom ∘ fun k ↦ S.X₂.iCycles (j + 1) (zw k))
            (fun k ↦ S.X₃.iCycles (j + 1) (zu₃ k)) := by
        ext k; induction k using Fin.addCases <;> simp
      rw [h]; rfl

end BracketShortExact

section HomologyBasisInvariance

/-- If a based chain complex is bounded, only finitely many of its homology bases are nonempty. -/
private theorem finite_setOf_homology_rank_ne_zero {C : ChainComplex (ModuleCat F) ℤ}
    {n m : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i))
    (h : ∀ i, Basis (Fin (m i)) F (C.homology i)) (hn : {i | n i ≠ 0}.Finite) :
    {i | m i ≠ 0}.Finite :=
  hn.subset fun i hi ↦ by
    simp only [Set.mem_ofPred_eq] at hi ⊢
    have : Module.Finite F (C.X i) := .of_basis (c i)
    have hle := C.finrank_homology_le_finrank_X i
    rw [finrank_eq_card_basis (c i), finrank_eq_card_basis (h i), Fintype.card_fin,
      Fintype.card_fin] at hle
    omega

/-- The product of `∏ᶠ q, d q ^ (-1) ^ (q + 1)` and `∏ᶠ q, d q ^ (-1) ^ q` is `1` for any
finitely supported family of units. -/
private theorem finprod_det_zpow_mul_add_one {M : ℤ → Type*} [∀ q, AddCommGroup (M q)]
    [∀ q, Module F (M q)] {m : ℤ → ℕ} (hm : {q | m q ≠ 0}.Finite)
    (b b' : ∀ q, Basis (Fin (m q)) F (M q)) :
    (∏ᶠ q : ℤ, (b q).det (b' q) ^ ((q + 1).negOnePow : ℤ)) *
      (∏ᶠ q : ℤ, (b q).det (b' q) ^ (q.negOnePow : ℤ)) = 1 := by
  have hs (e : ℤ → ℤ) : Function.HasFiniteMulSupport fun q : ℤ ↦ (b q).det (b' q) ^ e q :=
    hm.subset <| Function.mulSupport_subset_iff'.2 fun q hq ↦ by
      have : IsEmpty (Fin (m q)) := by rw [show m q = 0 by simpa using hq]; infer_instance
      simp
  rw [← finprod_mul_distrib (hs _) (hs _)]
  refine finprod_eq_one_of_forall_eq_one fun q ↦ ?_
  rw [Int.negOnePow_succ, Units.val_neg, zpow_neg, inv_mul_cancel₀
    (zpow_ne_zero _ (Basis.isUnit_det _ _).ne_zero)]

/-- **Homology-basis invariance.** Once Milnor's multiplicativity formula holds for one choice of
homology bases `(b₁', b₂', b₃')`, it holds for every choice `(b₁, b₂, b₃)`. -/
private theorem reidemeisterTorsionWithHomology_eq_mul_of_adapted
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
    {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hn₁ : {i | n₁ i ≠ 0}.Finite) (hn₃ : {i | n₃ i ≠ 0}.Finite)
    (b₁' b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (b₂' b₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (b₃' b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (ε : F)
    (h₀ : S.X₂.reidemeisterTorsionWithHomology c₂ b₂' =
      ε * (S.X₁.reidemeisterTorsionWithHomology c₁ b₁' *
        S.X₃.reidemeisterTorsionWithHomology c₃ b₃' *
        hS.homologySequenceComplex.reidemeisterTorsion
          (ChainComplex.interleave.basis _ _ _ b₁' b₂' b₃'))) :
    S.X₂.reidemeisterTorsionWithHomology c₂ b₂ =
      ε * (S.X₁.reidemeisterTorsionWithHomology c₁ b₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ b₃ *
        hS.homologySequenceComplex.reidemeisterTorsion
          (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃)) := by
  have hm₁ := finite_setOf_homology_rank_ne_zero c₁ b₁' hn₁
  have hm₃ := finite_setOf_homology_rank_ne_zero c₃ b₃' hn₃
  rw [reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology (h := b₂') b₂,
    reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology (h := b₁') b₁,
    reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology (h := b₃') b₃,
    ChainComplex.interleave.reidemeisterTorsion_basis_eq_mul _ _ _ b₁' b₁ b₂' b₂ b₃' b₃, h₀]
  have h (a τ₁ τ₃ τH p₁' p₁ p₂' p₃' p₃ : F) (h₁ : p₁' * p₁ = 1) (h₃ : p₃' * p₃ = 1) :
      a * (τ₁ * τ₃ * τH) * p₂' =
        a * ((τ₁ * p₁') * (τ₃ * p₃') * (τH * (p₁ * p₂' * p₃))) := by
    calc a * (τ₁ * τ₃ * τH) * p₂'
      _ = a * (τ₁ * τ₃ * τH) * p₂' * (p₁' * p₁) * (p₃' * p₃) := by rw [h₁, h₃, mul_one, mul_one]
      _ = a * ((τ₁ * p₁') * (τ₃ * p₃') * (τH * (p₁ * p₂' * p₃))) := by ring
  exact h _ _ _ _ _ _ _ _ _ (finprod_det_zpow_mul_add_one hm₁ b₁' b₁)
    (finprod_det_zpow_mul_add_one hm₃ b₃' b₃)

end HomologyBasisInvariance

section MainTheorem

/-- Shift a `ℤ`-indexed family `f : ∀ q, P (q + 1)` to `∀ i, P i` so that its value at `q + 1` is
propositionally equal to `f q`. -/
private def shiftAux (P : ℤ → Type*) (f : ∀ q : ℤ, P (q + 1)) (p i : ℤ) (h : p + 1 = i) : P i :=
  h ▸ f p

private def shiftFamily (P : ℤ → Type*) (f : ∀ q : ℤ, P (q + 1)) (i : ℤ) : P i :=
  shiftAux P f (i - 1) i (sub_add_cancel i 1)

private theorem shiftFamily_add_one (P : ℤ → Type*) (f : ∀ q : ℤ, P (q + 1)) (q : ℤ) :
    shiftFamily P f (q + 1) = f q := by
  have h : ∀ (p : ℤ) (_ : p = q) (h₁ : p + 1 = q + 1), shiftAux P f p (q + 1) h₁ = f q := by
    rintro _ rfl ⟨⟩; rfl
  exact h (q + 1 - 1) (add_sub_cancel_right q 1) (sub_add_cancel (q + 1) 1)

/-- Assemble a basis of the middle object of an exact short complex `A ⟶ B ⟶ C` of vector spaces
from bases of `im φ` and `im ψ` and lifts, reindexed to match an existing `Fin m` basis of `B`. -/
private def exactRangeBasis {A B C : ModuleCat F} {φ : A ⟶ B} {ψ : B ⟶ C} {hφψ : φ ≫ ψ = 0}
    (h : (ShortComplex.mk φ ψ hφψ).Exact) {m α β : ℕ} (b : Basis (Fin m) F B)
    (u : Basis (Fin α) F (LinearMap.range φ.hom))
    (v : Basis (Fin β) F (LinearMap.range ψ.hom))
    (v' : Fin β → B) (hv' : ∀ k, ψ.hom (v' k) = v k) :
    { hm : m = α + β // ∃ b' : Basis (Fin m) F B,
      ⇑b' = Fin.append (fun k ↦ (u k : B)) v' ∘ Fin.cast hm } := by
  have hex : Function.Exact (LinearMap.range φ.hom).subtype ψ.hom.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
    exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 h).symm
  let bsum := (Basis.ofExactLift (Submodule.injective_subtype _) hex u v v' fun k ↦
    Subtype.ext (hv' k)).reindex finSumFinEquiv
  have hm : m = α + β := by simpa using Fintype.card_congr (b.indexEquiv bsum)
  refine ⟨hm, bsum.reindex (finCongr hm.symm), ?_⟩
  rw [Basis.coe_reindex, Basis.coe_reindex_ofExactLift]
  rfl

private def rangeLift {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module F A] [Module F B]
    (φ : A →ₗ[F] B) {α : ℕ} (u : Fin α → LinearMap.range φ) : Fin α → A :=
  Function.surjInv φ.surjective_rangeRestrict ∘ u

private theorem apply_rangeLift {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module F A]
    [Module F B] (φ : A →ₗ[F] B) {α : ℕ} (u : Fin α → LinearMap.range φ) (k : Fin α) :
    φ (rangeLift φ u k) = u k :=
  congrArg Subtype.val (Function.surjInv_eq φ.surjective_rangeRestrict (u k))

private def cycleLift (C : ChainComplex (ModuleCat F) ℤ) (q : ℤ) {α : ℕ}
    (x : Fin α → C.homology q) : Fin α → C.cycles q :=
  Function.surjInv (C.moduleCat_homologyπ_surjective q) ∘ x

private theorem homologyπ_cycleLift (C : ChainComplex (ModuleCat F) ℤ) (q : ℤ) {α : ℕ}
    (x : Fin α → C.homology q) (k : Fin α) :
    C.homologyπ q (cycleLift C q x k) = x k :=
  Function.surjInv_eq (C.moduleCat_homologyπ_surjective q) (x k)

private theorem map_append_comp_cast_eq {M N : Type*} {m α β : ℕ} (π : M → N)
    {b : Fin m → N} {a : Fin α → N} {c : Fin β → N} {hm : m = α + β}
    (hb : b = Fin.append a c ∘ Fin.cast hm)
    {za : Fin α → M} {zc : Fin β → M} (ha : ∀ k, π (za k) = a k) (hc : ∀ k, π (zc k) = c k)
    (k : Fin m) :
    π ((Fin.append za zc ∘ Fin.cast hm) k) = b k := by
  rw [hb, Function.comp_apply, Function.comp_apply]
  generalize Fin.cast hm k = l
  induction l using Fin.addCases <;> simp [ha, hc]

/-- Unbounded case of Milnor's multiplicativity formula: if `S.X₂` is unbounded, so is `S.X₁` or
`S.X₃`, and both sides vanish. -/
private theorem reidemeisterTorsionWithHomology_eq_mul_of_not_finite
    {C₁ C₂ C₃ : ChainComplex (ModuleCat F) ℤ} {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (C₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (C₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (C₂.X i))
    (b₁ : ∀ i, Basis (Fin (m₁ i)) F (C₁.homology i))
    (b₂ : ∀ i, Basis (Fin (m₂ i)) F (C₂.homology i))
    (b₃ : ∀ i, Basis (Fin (m₃ i)) F (C₃.homology i))
    (hn : ¬{i | n₁ i + n₃ i ≠ 0}.Finite) (ε τH : F) :
    C₂.reidemeisterTorsionWithHomology c₂ b₂ =
      ε * (C₁.reidemeisterTorsionWithHomology c₁ b₁ *
        C₃.reidemeisterTorsionWithHomology c₃ b₃ * τH) := by
  rw [reidemeisterTorsionWithHomology_of_not_finite C₂ c₂ b₂ hn]
  by_cases hn₁ : {i | n₁ i ≠ 0}.Finite
  · have hn₃ : ¬{i | n₃ i ≠ 0}.Finite := fun hn₃ ↦
      hn ((hn₁.union hn₃).subset fun i hi ↦ by
        simp only [Set.mem_union, Set.mem_ofPred_eq] at hi ⊢; omega)
    simp [reidemeisterTorsionWithHomology_of_not_finite C₃ c₃ b₃ hn₃]
  · simp [reidemeisterTorsionWithHomology_of_not_finite C₁ c₁ b₁ hn₁]

/-- For a bounded complex `S.X₃`, the Koszul sign factors of a short exact sequence have finite
multiplicative support. -/
private theorem hasFiniteMulSupport_shortExact_sign
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} {n₃ : ℤ → ℕ}
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i)) (hn₃ : {i | n₃ i ≠ 0}.Finite) :
    Function.HasFiniteMulSupport fun j : ℤ ↦ (-1 : F) ^
      (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
        (finrank F (LinearMap.range (homologyMap S.f (j + 1)).hom) +
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) +
      finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom) *
        finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) :=
  (hn₃.preimage (add_left_injective (1 : ℤ)).injOn).subset <|
    Function.mulSupport_subset_iff'.2 fun j hj ↦ by
      have hj₀ : n₃ (j + 1) = 0 := by simpa using hj
      have : Module.Finite F (S.X₃.X (j + 1)) := .of_basis (c₃ (j + 1))
      have : Module.Finite F (S.X₃.homology (j + 1)) :=
        .of_surjective _ (S.X₃.moduleCatKerHomologyClass_surjective
          ((ComplexShape.down ℤ).next_eq' (show (ComplexShape.down ℤ).Rel (j + 1) j by simp)))
      have hH₃ : finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom) = 0 := by
        have h₁ := Submodule.finrank_le (LinearMap.range (homologyMap S.g (j + 1)).hom)
        have h₂ := S.X₃.finrank_homology_le_finrank_X (j + 1)
        rw [finrank_eq_card_basis (c₃ (j + 1)), Fintype.card_fin, hj₀] at h₂
        omega
      simp [finrank_range_d_eq_zero S.X₃ c₃ hj₀, hH₃]

private theorem homologyπ_reindex {C : ChainComplex (ModuleCat F) ℤ} {i : ℤ} {m m' : ℕ}
    {h : Basis (Fin m) F (C.homology i)} {hm : m = m'} {y : Fin m → C.cycles i}
    {y' : Fin m' → C.cycles i} (hyy' : y = y' ∘ Fin.cast hm)
    (hy : ∀ k, C.homologyπ i (y k) = h k) (k : Fin m') :
    C.homologyπ i (y' k) = (h.reindex (finCongr hm)) k := by
  simpa [hyy'] using hy (Fin.cast hm.symm k)

/-- Reindexing the homology basis in `torsionBracketWithHomology` along `hm : m = m'` and
replacing `y` by an equal family `y' ∘ Fin.cast hm` does not change the bracket. -/
private theorem torsionBracketWithHomology_reindex_of_eq
    {C : ChainComplex (ModuleCat F) ℤ} {n : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i))
    {j : ℤ} {p m m' q : ℕ}
    (b₁ : Basis (Fin p) F (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom))
    (h : Basis (Fin m) F (C.homology (j + 1))) (hm : m = m')
    {y : Fin m → C.cycles (j + 1)} {y' : Fin m' → C.cycles (j + 1)}
    (hyy' : y = y' ∘ Fin.cast hm)
    (hy : ∀ k, C.homologyπ (j + 1) (y k) = h k)
    (b₀ : Basis (Fin q) F (LinearMap.range (C.d (j + 1) j).hom))
    (s : Fin q → C.X (j + 1)) (hs : ∀ k, (C.d (j + 1) j).hom (s k) = b₀ k) :
    torsionBracketWithHomology c b₁ h y hy b₀ s hs =
      torsionBracketWithHomology c b₁ (h.reindex (finCongr hm)) y' (homologyπ_reindex hyy' hy)
        b₀ s hs := by
  subst hm
  have hy_eq : y = y' := hyy'
  subst hy_eq
  rw [torsionBracketWithHomology_eq_det_append c b₁ h y hy b₀ s hs
      (card_X_eq_add_add c b₁ h b₀),
    torsionBracketWithHomology_eq_det_append c b₁ (h.reindex (finCongr rfl)) y _ b₀ s hs
      (card_X_eq_add_add c b₁ (h.reindex (finCongr rfl)) b₀)]

/-- Evaluate `τ(S.X₂, c₂, b₂')` in adapted homology bases `(b₁', b₂', b₃')` equipped with cycle and
chain lifts along the connecting homomorphism. -/
private theorem reidemeisterTorsionWithHomology_eq_mul_of_cycle_lifts
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
    {n₁ n₃ m₁ m₂ m₃ α β γ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (hn : {i | n₁ i + n₃ i ≠ 0}.Finite)
    (u : ∀ q, Basis (Fin (α q)) F (LinearMap.range (hS.δ (q + 1) q rfl).hom))
    (v : ∀ q, Basis (Fin (β q)) F (LinearMap.range (homologyMap S.f q).hom))
    (w : ∀ q, Basis (Fin (γ q)) F (LinearMap.range (homologyMap S.g q).hom))
    (zu : ∀ q, Fin (α q) → S.X₁.cycles q) (hzu : ∀ q k, S.X₁.homologyπ q (zu q k) = u q k)
    (zv : ∀ q, Fin (β q) → S.X₁.cycles q)
    (zw : ∀ q, Fin (γ q) → S.X₂.cycles q)
    (xhat : ∀ q, Fin (α q) → S.X₂.X (q + 1))
    (zu₃ : ∀ q, Fin (α q) → S.X₃.cycles (q + 1))
    (hxhat : ∀ q k, (S.X₂.d (q + 1) q).hom (xhat q k) = (S.f.f q).hom (S.X₁.iCycles q (zu q k)))
    (hzu₃ : ∀ q k, (S.g.f (q + 1)).hom (xhat q k) = S.X₃.iCycles (q + 1) (zu₃ q k))
    (b₁' : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (hm₁ : ∀ q, m₁ q = α q + β q)
    (hy₁ : ∀ q k, S.X₁.homologyπ q ((Fin.append (zu q) (zv q) ∘ Fin.cast (hm₁ q)) k) = b₁' q k)
    (b₂' : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (hm₂ : ∀ q, m₂ q = β q + γ q)
    (hy₂ : ∀ q k, S.X₂.homologyπ q
      ((Fin.append (fun k ↦ cyclesMap S.f q (zv q k)) (zw q) ∘ Fin.cast (hm₂ q)) k) = b₂' q k)
    (b₃' : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (hm₃ : ∀ q, m₃ (q + 1) = γ (q + 1) + α q)
    (hY₃ : ∀ q k, S.X₃.homologyπ (q + 1)
      ((Fin.append (fun k ↦ cyclesMap S.g (q + 1) (zw (q + 1) k)) (zu₃ q) ∘ Fin.cast (hm₃ q)) k) =
        b₃' (q + 1) k) :
    S.X₂.reidemeisterTorsionWithHomology c₂ b₂' =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
          (finrank F (LinearMap.range (homologyMap S.f (j + 1)).hom) +
            finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) +
        finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ b₁' *
        S.X₃.reidemeisterTorsionWithHomology c₃ b₃') := by
  have hn₁ : {i | n₁ i ≠ 0}.Finite := hn.subset fun i hi ↦ by simp_all
  have hn₃ : {i | n₃ i ≠ 0}.Finite := hn.subset fun i hi ↦ by simp_all
  have hg (i : ℤ) : Function.Surjective (S.g.f i).hom :=
    ((shortExact_iff_degreewise_shortExact S).1 hS i).moduleCat_surjective_g
  let B₁ (j : ℤ) := chosenBoundaryBasis S.X₁ c₁ (j + 1) j
  let s₁ (j : ℤ) := chosenBoundaryLift S.X₁ c₁ (j + 1) j
  have hs₁ (j : ℤ) (k) : (S.X₁.d (j + 1) j).hom (s₁ j k) = B₁ j k :=
    chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j k
  let B₃ (j : ℤ) := chosenBoundaryBasis S.X₃ c₃ (j + 1) j
  let t (j : ℤ) (k) := Function.surjInv (hg (j + 1)) (chosenBoundaryLift S.X₃ c₃ (j + 1) j k)
  have ht (j : ℤ) (k) : (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t j k)) = B₃ j k := by
    rw [Function.surjInv_eq (hg (j + 1)), chosenBoundaryLift_spec]
  let B₂ (j : ℤ) := shortExactBoundaryBasisWithHomology hS (B₁ j) (u j) (zu j) (hzu j) (B₃ j)
    (t j) (ht j)
  let s₂ (j : ℤ) := Fin.append (Fin.append (fun k ↦ (S.f.f (j + 1)).hom (s₁ j k)) (xhat j)) (t j)
  have hs₂ (j : ℤ) := shortExactBoundaryLift_spec hS (B₁ j) (s₁ j) (hs₁ j) (u j) (zu j) (hzu j)
    (xhat j) (hxhat j) (B₃ j) (t j) (ht j)
  let y₃ := shiftFamily (fun i ↦ Fin (m₃ i) → S.X₃.cycles i) fun q ↦
    Fin.append (fun k ↦ cyclesMap S.g (q + 1) (zw (q + 1) k)) (zu₃ q) ∘ Fin.cast (hm₃ q)
  have hy₃ (i : ℤ) (k) : S.X₃.homologyπ i (y₃ i k) = b₃' i k := by
    obtain ⟨q, rfl⟩ : ∃ q, i = q + 1 := ⟨i - 1, by omega⟩
    simpa only [y₃, shiftFamily_add_one] using hY₃ q k
  have hτ₁ := hasFiniteMulSupport_torsionBracketWithHomology (c := c₁) (h := b₁') hn₁ B₁ _ hy₁ s₁
    hs₁
  have hτ₃ := hasFiniteMulSupport_torsionBracketWithHomology (c := c₃) (h := b₃') hn₃ B₃ y₃ hy₃
    (fun j k ↦ (S.g.f (j + 1)).hom (t j k)) ht
  rw [reidemeisterTorsionWithHomology_eq_finprod hn B₂ _ hy₂ s₂ hs₂,
    reidemeisterTorsionWithHomology_eq_finprod hn₁ B₁ _ hy₁ s₁ hs₁,
    reidemeisterTorsionWithHomology_eq_finprod hn₃ B₃ y₃ hy₃
      (fun j k ↦ (S.g.f (j + 1)).hom (t j k)) ht,
    ← finprod_mul_distrib hτ₁ hτ₃,
    ← finprod_mul_distrib (hasFiniteMulSupport_shortExact_sign c₃ hn₃) (hτ₁.fun_mul hτ₃)]
  refine finprod_congr fun j ↦ ?_
  rw [torsionBracketWithHomology_reindex_of_eq c₂ (B₂ (j + 1)) (b₂' (j + 1)) (hm₂ (j + 1)) rfl
      (hy₂ (j + 1)) (B₂ j) (s₂ j) (hs₂ j),
    torsionBracketWithHomology_reindex_of_eq c₁ (B₁ (j + 1)) (b₁' (j + 1)) (hm₁ (j + 1)) rfl
      (hy₁ (j + 1)) (B₁ j) (s₁ j) (hs₁ j),
    torsionBracketWithHomology_reindex_of_eq c₃ (B₃ (j + 1)) (b₃' (j + 1)) (hm₃ j)
      (shiftFamily_add_one _ _ j) (hy₃ (j + 1)) (B₃ j) (fun k ↦ (S.g.f (j + 1)).hom (t j k))
      (ht j),
    torsionBracketWithHomology_shortExact hS c₁ c₃ c₂ hc₁ hc₃ (B₁ (j + 1)) (B₁ j) (s₁ j) (hs₁ j)
      (B₃ (j + 1)) (B₃ j) (t (j + 1)) (ht (j + 1)) (t j) (ht j) (u (j + 1)) (zu (j + 1))
      (hzu (j + 1)) (u j) (zu j) (hzu j) (xhat j) (zu₃ j) (hxhat j) (hzu₃ j) (zv (j + 1))
      (zw (j + 1)) ((b₁' (j + 1)).reindex (finCongr (hm₁ (j + 1))))
      (homologyπ_reindex rfl (hy₁ (j + 1))) ((b₂' (j + 1)).reindex (finCongr (hm₂ (j + 1))))
      (homologyπ_reindex rfl (hy₂ (j + 1))) ((b₃' (j + 1)).reindex (finCongr (hm₃ j)))
      (homologyπ_reindex (shiftFamily_add_one _ _ j) (hy₃ (j + 1))),
    mul_zpow, mul_zpow]
  congr 1
  rw [finrank_eq_card_basis (v (j + 1)), finrank_eq_card_basis (w (j + 1)), Fintype.card_fin,
    Fintype.card_fin]
  rcases Int.units_eq_one_or j.negOnePow with hj | hj <;> simp [hj, ← inv_pow]

/-- **Multiplicativity of Reidemeister torsion with homology bases.** Let
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of `ℤ`-graded chain complexes of vector
spaces over a field `F`, with compatible chain bases `c₁`, `c₃`, `c₂` and arbitrary ordered bases
`b₁`, `b₂`, `b₃` of the homology groups. Then
`τ(S.X₂, c₂, b₂) = ε · τ(S.X₁, c₁, b₁) · τ(S.X₃, c₃, b₃) · τ(H, B)`, where `H` is the long exact
homology sequence `hS.homologySequenceComplex`, `B` is `ChainComplex.interleave.basis`, and `ε` is
the Koszul sign determined by the dimensions of the boundaries and of the images of `Hⱼ₊₁(S.f)`
and `Hⱼ₊₁(S.g)`. Both sides vanish when `S.X₂` is unbounded. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_shortExact
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
    {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (b₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) :
    S.X₂.reidemeisterTorsionWithHomology c₂ b₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
          (finrank F (LinearMap.range (homologyMap S.f (j + 1)).hom) +
            finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) +
        finrank F (LinearMap.range (homologyMap S.g (j + 1)).hom) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ b₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ b₃ *
        hS.homologySequenceComplex.reidemeisterTorsion
          (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃)) := by
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · exact reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂ b₁ b₂ b₃ hn _ _
  have hn₁ : {i | n₁ i ≠ 0}.Finite := hn.subset fun i hi ↦ by simp_all
  have hn₃ : {i | n₃ i ≠ 0}.Finite := hn.subset fun i hi ↦ by simp_all
  have (i : ℤ) : Module.Finite F (S.X₁.homology i) := .of_basis (b₁ i)
  have (i : ℤ) : Module.Finite F (S.X₂.homology i) := .of_basis (b₂ i)
  have (i : ℤ) : Module.Finite F (S.X₃.homology i) := .of_basis (b₃ i)
  let u (q : ℤ) := finBasis F (LinearMap.range (hS.δ (q + 1) q rfl).hom)
  let v (q : ℤ) := finBasis F (LinearMap.range (homologyMap S.f q).hom)
  let w (q : ℤ) := finBasis F (LinearMap.range (homologyMap S.g q).hom)
  let u' (q : ℤ) := rangeLift (hS.δ (q + 1) q rfl).hom (u q)
  let v' (q : ℤ) := rangeLift (homologyMap S.f q).hom (v q)
  let w' (q : ℤ) := rangeLift (homologyMap S.g q).hom (w q)
  let E₁ (q : ℤ) := exactRangeBasis (hS.homology_exact₁ (q + 1) q rfl) (b₁ q) (u q) (v q) (v' q)
    (apply_rangeLift _ _)
  let E₂ (q : ℤ) := exactRangeBasis (hS.homology_exact₂ q) (b₂ q) (v q) (w q) (w' q)
    (apply_rangeLift _ _)
  let E₃ (q : ℤ) := exactRangeBasis (hS.homology_exact₃ (q + 1) q rfl) (b₃ (q + 1)) (w (q + 1))
    (u q) (u' q) (apply_rangeLift _ _)
  let b₃' := shiftFamily (fun i ↦ Basis (Fin (m₃ i)) F (S.X₃.homology i)) fun q ↦ (E₃ q).2.choose
  have hb₃' (q : ℤ) : ⇑(b₃' (q + 1)) =
      Fin.append (fun k ↦ (w (q + 1) k : S.X₃.homology (q + 1))) (u' q) ∘ Fin.cast (E₃ q).1 := by
    rw [show b₃' (q + 1) = (E₃ q).2.choose from shiftFamily_add_one _ _ q]
    exact (E₃ q).2.choose_spec
  refine reidemeisterTorsionWithHomology_eq_mul_of_adapted hS c₁ c₃ c₂ hn₁ hn₃
    (fun q ↦ (E₁ q).2.choose) b₁ (fun q ↦ (E₂ q).2.choose) b₂ b₃' b₃ _ ?_
  rw [ChainComplex.interleave.reidemeisterTorsion_basis_eq_one _ _ b₃' u v w v'
      (fun q ↦ apply_rangeLift _ (v q)) w' (fun q ↦ apply_rangeLift _ (w q)) u'
      (fun q ↦ apply_rangeLift _ (u q))
      (ChainComplex.interleave.finite_setOf_rank_ne_zero
        (finite_setOf_homology_rank_ne_zero c₁ b₁ hn₁)
        (finite_setOf_homology_rank_ne_zero c₂ b₂ hn)
        (finite_setOf_homology_rank_ne_zero c₃ b₃ hn₃))
      (fun q ↦ (E₁ q).1) (fun q ↦ (E₂ q).1) (fun q ↦ (E₃ q).1)
      (fun q ↦ (E₁ q).2.choose_spec) (fun q ↦ (E₂ q).2.choose_spec) hb₃', mul_one]
  let zu (q : ℤ) := cycleLift S.X₁ q (Subtype.val ∘ u q)
  choose xhat zu₃ hxhat hzu₃ hπ₃ using fun (q : ℤ) k ↦
    hS.moduleCat_exists_d_eq_of_δ_eq (q + 1) q rfl (u' q k) (zu q k)
      ((apply_rangeLift _ (u q) k).trans (homologyπ_cycleLift S.X₁ q (Subtype.val ∘ u q) k).symm)
  exact reidemeisterTorsionWithHomology_eq_mul_of_cycle_lifts hS c₁ c₃ c₂ hc₁ hc₃ hn u v w zu
    (fun q ↦ homologyπ_cycleLift S.X₁ q _) (fun q ↦ cycleLift S.X₁ q (v' q))
    (fun q ↦ cycleLift S.X₂ q (w' q)) xhat zu₃ hxhat hzu₃ _ (fun q ↦ (E₁ q).1)
    (fun q ↦ map_append_comp_cast_eq _ (E₁ q).2.choose_spec (homologyπ_cycleLift S.X₁ q _)
      (homologyπ_cycleLift S.X₁ q _)) _ (fun q ↦ (E₂ q).1)
    (fun q ↦ map_append_comp_cast_eq _ (E₂ q).2.choose_spec
      (fun k ↦ by rw [← moduleCat_homologyMap_homologyπ, homologyπ_cycleLift, apply_rangeLift])
      (homologyπ_cycleLift S.X₂ q _)) b₃' (fun q ↦ (E₃ q).1)
    (fun q ↦ map_append_comp_cast_eq _ (hb₃' q)
      (fun k ↦ by rw [← moduleCat_homologyMap_homologyπ, homologyπ_cycleLift, apply_rangeLift])
      (hπ₃ q))

end MainTheorem

section Corollaries

/-! ### Compatible homology bases, direct sums, and acyclic middle complexes -/

/-- When the homology bases `b₁`, `b₃`, `b₂` are compatible with `homologyMap S.f` and
`homologyMap S.g` and finitely supported, the based long exact homology sequence has torsion `1`. -/
private theorem reidemeisterTorsion_homologySequenceComplex_eq_one_of_homologyMap
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) {m₁ m₃ : ℤ → ℕ}
    (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (b₂ : ∀ i, Basis (Fin (m₁ i + m₃ i)) F (S.X₂.homology i))
    (hb₁ : ∀ i k, b₂ i (Fin.castAdd (m₃ i) k) = (homologyMap S.f i).hom (b₁ i k))
    (hb₃ : ∀ i k, (homologyMap S.g i).hom (b₂ i (Fin.natAdd (m₁ i) k)) = b₃ i k)
    (hm₁ : {i | m₁ i ≠ 0}.Finite) (hm₃ : {i | m₃ i ≠ 0}.Finite)
    (hrg : ∀ i, LinearMap.range (homologyMap S.g i).hom = ⊤)
    (hδ₀ : ∀ i, (hS.δ (i + 1) i rfl).hom = 0)
    (hfinj : ∀ i, Function.Injective (homologyMap S.f i).hom) :
    hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) = 1 := by
  have hm₂ : {i | m₁ i + m₃ i ≠ 0}.Finite :=
    (hm₁.union hm₃).subset fun i hi ↦ by
      simp only [Set.mem_union, Set.mem_ofPred_eq] at hi ⊢; omega
  let u (q : ℤ) : Basis (Fin 0) F (LinearMap.range (hS.δ (q + 1) q rfl).hom) :=
    have : Subsingleton (LinearMap.range (hS.δ (q + 1) q rfl).hom) := by
      rw [hδ₀, LinearMap.range_zero]; infer_instance
    Basis.empty _
  let v (q : ℤ) := (b₁ q).map (LinearEquiv.ofInjective _ (hfinj q))
  let w (q : ℤ) := (b₃ q).map (LinearEquiv.ofTop _ (hrg q)).symm
  have hw_coe (q : ℤ) (k : Fin (m₃ q)) : (w q k : S.X₃.homology q) = b₃ q k := by
    rw [Basis.map_apply]; rfl
  exact ChainComplex.interleave.reidemeisterTorsion_basis_eq_one b₁ b₂ b₃ u v w (fun q k ↦ b₁ q k)
    (fun q k ↦ by rw [Basis.map_apply]; rfl) (fun q k ↦ b₂ q (Fin.natAdd (m₁ q) k))
    (fun q k ↦ by rw [hw_coe, hb₃]) (fun _ ↦ Fin.elim0) (fun _ k ↦ Fin.elim0 k)
    (ChainComplex.interleave.finite_setOf_rank_ne_zero hm₁ hm₂ hm₃)
    (fun _ ↦ (Nat.zero_add _).symm) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun q ↦ (funext_comp_cast_iff (Nat.zero_add (m₁ q)).symm _ _).2 fun m ↦ by
      induction m using Fin.addCases with
      | left m => exact Fin.elim0 m
      | right m => rw [Fin.append_right]; congr 1; ext; simp)
    (fun q ↦ by
      ext k; induction k using Fin.addCases with
      | left k => simp [v, Basis.map_apply, hb₁]
      | right k => simp)
    (fun q ↦ by ext k; simp [hw_coe, Fin.append_right_nil _ _ rfl])

/-- **Multiplicativity with compatible homology bases.** If, in addition to compatible chain bases,
the homology bases `b₁`, `b₃`, `b₂` are compatible with `homologyMap S.f` and `homologyMap S.g`,
then the connecting homomorphisms vanish, the long exact homology sequence has torsion `1`, and
`τ(S.X₂, c₂, b₂) = ε · τ(S.X₁, c₁, b₁) · τ(S.X₃, c₃, b₃)`. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_homologyMap
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact)
    {n₁ n₃ m₁ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (b₂ : ∀ i, Basis (Fin (m₁ i + m₃ i)) F (S.X₂.homology i))
    (hb₁ : ∀ i k, b₂ i (Fin.castAdd (m₃ i) k) = (homologyMap S.f i).hom (b₁ i k))
    (hb₃ : ∀ i k, (homologyMap S.g i).hom (b₂ i (Fin.natAdd (m₁ i) k)) = b₃ i k) :
    S.X₂.reidemeisterTorsionWithHomology c₂ b₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
          (finrank F (S.X₁.homology (j + 1)) +
            finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) +
        finrank F (S.X₃.homology (j + 1)) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ b₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ b₃) := by
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · simpa only [mul_one] using
      reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂ b₁ b₂ b₃ hn _ 1
  have hn₁ : {i | n₁ i ≠ 0}.Finite := hn.subset fun i hi ↦ by simp_all
  have hn₃ : {i | n₃ i ≠ 0}.Finite := hn.subset fun i hi ↦ by simp_all
  have hrg (i : ℤ) : LinearMap.range (homologyMap S.g i).hom = ⊤ :=
    eq_top_iff.2 (by
      rw [← (b₃ i).span_eq, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact ⟨b₂ i (Fin.natAdd (m₁ i) k), hb₃ i k⟩)
  have hδ₀ (i : ℤ) : (hS.δ (i + 1) i rfl).hom = 0 := by
    have hker := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
      (hS.homology_exact₃ (i + 1) i rfl)
    exact LinearMap.ker_eq_top.1 (hker.symm.trans (hrg (i + 1)))
  have hfinj (i : ℤ) : Function.Injective (homologyMap S.f i).hom := by
    rw [← LinearMap.ker_eq_bot,
      ← (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (hS.homology_exact₁ (i + 1) i rfl),
      hδ₀ i, LinearMap.range_zero]
  rw [reidemeisterTorsionWithHomology_eq_mul_of_shortExact hS c₁ c₃ c₂ hc₁ hc₃ b₁ b₂ b₃,
    reidemeisterTorsion_homologySequenceComplex_eq_one_of_homologyMap hS b₁ b₃ b₂ hb₁ hb₃
      (finite_setOf_homology_rank_ne_zero c₁ b₁ hn₁)
      (finite_setOf_homology_rank_ne_zero c₃ b₃ hn₃) hrg hδ₀ hfinj, mul_one]
  congr 1
  refine finprod_congr fun j ↦ ?_
  have : Module.Finite F (S.X₁.homology (j + 1)) := .of_basis (b₁ (j + 1))
  have : Module.Finite F (S.X₃.homology (j + 1)) := .of_basis (b₃ (j + 1))
  rw [LinearMap.finrank_range_of_inj (hfinj (j + 1)), hrg (j + 1), finrank_top]

/-- **Torsion with homology bases of a direct sum.** For two chain complexes `C₁` and `C₃` based by
`c₁`, `c₃` and with homology based by `b₁`, `b₃`, the biproduct `C₁ ⊞ C₃` based by `biprodXBasis`
and `biprodHomologyBasis` has torsion `ε · τ(C₁, c₁, b₁) · τ(C₃, c₃, b₃)`. -/
theorem reidemeisterTorsionWithHomology_biprod {C₁ C₃ : ChainComplex (ModuleCat F) ℤ}
    {n₁ n₃ m₁ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (C₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (C₃.X i))
    (b₁ : ∀ i, Basis (Fin (m₁ i)) F (C₁.homology i))
    (b₃ : ∀ i, Basis (Fin (m₃ i)) F (C₃.homology i)) :
    (C₁ ⊞ C₃).reidemeisterTorsionWithHomology
        (fun i ↦ (biprodXBasis (c₁ i) (c₃ i)).reindex finSumFinEquiv)
        (fun i ↦ (biprodHomologyBasis (b₁ i) (b₃ i)).reindex finSumFinEquiv) =
      (∏ᶠ j : ℤ, (-1 : F) ^
        (finrank F (LinearMap.range (C₃.d (j + 1 + 1) (j + 1)).hom) *
          (finrank F (C₁.homology (j + 1)) +
            finrank F (LinearMap.range (C₁.d (j + 1) j).hom)) +
        finrank F (C₃.homology (j + 1)) *
          finrank F (LinearMap.range (C₁.d (j + 1) j).hom))) *
      (C₁.reidemeisterTorsionWithHomology c₁ b₁ *
        C₃.reidemeisterTorsionWithHomology c₃ b₃) :=
  reidemeisterTorsionWithHomology_eq_mul_of_shortExact_of_homologyMap
    (ShortComplex.Splitting.ofHasBinaryBiproduct C₁ C₃).shortExact c₁ c₃ _ (by simp)
    (by simp [← ModuleCat.comp_apply]) b₁ b₃ _ (by simp) fun i k ↦ by
      rw [Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd, biprodHomologyBasis_inr,
        ← ModuleCat.comp_apply, ← homologyMap_comp, Limits.biprod.inr_snd, homologyMap_id,
        ModuleCat.id_apply]

/-- When the middle complex `S.X₂` of a short exact sequence is exact in degrees `i + 1` and `i`,
the connecting isomorphism `hS.δIso (i + 1) i rfl` identifies the sizes of homology bases of
`S.X₁.homology i` and `S.X₃.homology (i + 1)`. -/
theorem card_homology_eq_of_exactAt {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
    (hS : S.ShortExact) {i : ℤ} (h₂₁ : S.X₂.ExactAt (i + 1)) (h₂₀ : S.X₂.ExactAt i) {m₁ m₃ : ℕ}
    (b₁ : Basis (Fin m₁) F (S.X₁.homology i)) (b₃ : Basis (Fin m₃) F (S.X₃.homology (i + 1))) :
    m₁ = m₃ := by
  simpa using Fintype.card_congr (b₁.indexEquiv
    (b₃.map (hS.δIso (i + 1) i rfl h₂₁.isZero_homology h₂₀.isZero_homology).toLinearEquiv))

/-- When `S.X₂` is acyclic and `H(S.X₁)`, `H(S.X₃)` are finitely supported, the torsion of the
based long exact homology sequence is the alternating product of the determinants of `δᵢ`. -/
private theorem reidemeisterTorsion_homologySequenceComplex_of_acyclic_X₂
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) (h₂ : S.X₂.Acyclic)
    {m₁ m₃ : ℤ → ℕ}
    (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (b₂ : ∀ i, Basis (Fin 0) F (S.X₂.homology i))
    (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (hm₁_fin : {i | m₁ i ≠ 0}.Finite) (hm₃_fin : {i | m₃ i ≠ 0}.Finite) :
    hS.homologySequenceComplex.reidemeisterTorsion
        (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) =
      ∏ᶠ i : ℤ, ((b₁ i).det fun k ↦
        (hS.δ (i + 1) i rfl).hom (b₃ (i + 1)
          (Fin.cast (card_homology_eq_of_exactAt hS (h₂ (i + 1)) (h₂ i) (b₁ i) (b₃ (i + 1)))
            k))) ^ ((i + 1).negOnePow : ℤ) := by
  have hsub (i : ℤ) : Subsingleton (S.X₂.homology i) :=
    ModuleCat.subsingleton_of_isZero (h₂ i).isZero_homology
  let eδ (i : ℤ) := (hS.δIso (i + 1) i rfl (h₂ (i + 1)).isZero_homology
    (h₂ i).isZero_homology).toLinearEquiv
  have hδ (i : ℤ) (x) : eδ i x = (hS.δ (i + 1) i rfl).hom x := rfl
  have hm (i : ℤ) := card_homology_eq_of_exactAt hS (h₂ (i + 1)) (h₂ i) (b₁ i) (b₃ (i + 1))
  let b₁' (i : ℤ) : Basis (Fin (m₁ i)) F (S.X₁.homology i) :=
    ((b₃ (i + 1)).reindex (finCongr (hm i).symm)).map (eδ i)
  have hb₁' (i : ℤ) :
      ⇑(b₁' i) = fun k ↦ (hS.δ (i + 1) i rfl).hom (b₃ (i + 1) (Fin.cast (hm i) k)) :=
    funext fun k ↦ by rw [Basis.map_apply, Basis.reindex_apply, finCongr_symm_apply, hδ]
  have hrg (q : ℤ) : LinearMap.range (hS.δ (q + 1) q rfl).hom = ⊤ :=
    LinearMap.range_eq_top.2 fun y ↦ ⟨(eδ q).symm y, by simp [← hδ]⟩
  let u (q : ℤ) : Basis (Fin (m₁ q)) F (LinearMap.range (hS.δ (q + 1) q rfl).hom) :=
    (b₁' q).map (LinearEquiv.ofTop _ (hrg q)).symm
  have hu_coe (q : ℤ) (k : Fin (m₁ q)) : (u q k : S.X₁.homology q) = b₁' q k := by
    rw [Basis.map_apply]; rfl
  have hg₀ (q : ℤ) : LinearMap.range (homologyMap S.g q).hom = ⊥ := by
    rw [Subsingleton.elim (homologyMap S.g q).hom 0, LinearMap.range_zero]
  let v (q : ℤ) : Basis (Fin 0) F (LinearMap.range (homologyMap S.f q).hom) := Basis.empty _
  let w (q : ℤ) : Basis (Fin 0) F (LinearMap.range (homologyMap S.g q).hom) :=
    have : Subsingleton (LinearMap.range (homologyMap S.g q).hom) := by rw [hg₀]; infer_instance
    Basis.empty _
  have hm₃ (q : ℤ) : m₃ (q + 1) = 0 + m₁ q := (hm q).symm.trans (Nat.zero_add _).symm
  have hH₀ : hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ b₁' b₂ b₃) = 1 :=
    ChainComplex.interleave.reidemeisterTorsion_basis_eq_one b₁' b₂ b₃ u v w
      (fun _ ↦ Fin.elim0) (fun _ k ↦ Fin.elim0 k) (fun _ ↦ Fin.elim0) (fun _ k ↦ Fin.elim0 k)
      (fun q k ↦ b₃ (q + 1) (Fin.cast (hm q) k)) (fun q k ↦ by rw [hu_coe, hb₁'])
      (ChainComplex.interleave.finite_setOf_rank_ne_zero hm₁_fin (by simp) hm₃_fin)
      (fun _ ↦ rfl) (fun _ ↦ rfl) hm₃
      (fun q ↦ by ext k; simp [hu_coe, Fin.append_right_nil _ _ rfl])
      (fun _ ↦ by ext k; exact Fin.elim0 k)
      (fun q ↦ (funext_comp_cast_iff (hm₃ q) _ _).2 fun m ↦ by
        induction m using Fin.addCases with
        | left m => exact Fin.elim0 m
        | right m => rw [Fin.append_right]; congr 1; ext; simp)
  rw [ChainComplex.interleave.reidemeisterTorsion_basis_eq_mul _ _ _ b₁' b₁ b₂ b₂ b₃ b₃, hH₀]
  simp only [Basis.det_self, one_zpow, finprod_one, mul_one, one_mul]
  refine finprod_congr fun i ↦ ?_
  have hinv : (b₁' i).det (b₁ i) = ((b₁ i).det (b₁' i))⁻¹ :=
    eq_inv_of_mul_eq_one_left <| by rw [Basis.det_mul_det, Basis.det_self]
  rw [hinv, hb₁', inv_zpow, ← zpow_neg, ← Units.val_neg, ← Int.negOnePow_succ]

/-- **Torsion of an acyclic middle complex.** When the middle complex `S.X₂` of a short exact
sequence `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` is acyclic, its Reidemeister torsion `τ(S.X₂, c₂)` equals
the product of the Koszul sign `∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim B₁,ⱼ)`, the torsions with homology
bases `τ(S.X₁, c₁, b₁)` and `τ(S.X₃, c₃, b₃)`, and the alternating product of the determinants of
the connecting isomorphisms `δᵢ : Hᵢ₊₁(S.X₃) → Hᵢ(S.X₁)` in the bases `b₃ (i + 1)` and `b₁ i`. -/
theorem reidemeisterTorsion_eq_mul_reidemeisterTorsionWithHomology_of_shortExact
    {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)} (hS : S.ShortExact) (h₂ : S.X₂.Acyclic)
    {n₁ n₃ m₁ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i))
    (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) :
    S.X₂.reidemeisterTorsion c₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^ (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
        finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ b₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ b₃ *
        ∏ᶠ i : ℤ, ((b₁ i).det fun k ↦
          (hS.δ (i + 1) i rfl).hom (b₃ (i + 1)
            (Fin.cast (card_homology_eq_of_exactAt hS (h₂ (i + 1)) (h₂ i) (b₁ i) (b₃ (i + 1)))
              k))) ^ ((i + 1).negOnePow : ℤ)) := by
  have hsub (i : ℤ) : Subsingleton (S.X₂.homology i) :=
    ModuleCat.subsingleton_of_isZero (h₂ i).isZero_homology
  let b₂ (i : ℤ) : Basis (Fin 0) F (S.X₂.homology i) := Basis.empty _
  rw [← reidemeisterTorsionWithHomology_eq_reidemeisterTorsion (c := c₂) (h := b₂) h₂]
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · exact reidemeisterTorsionWithHomology_eq_mul_of_not_finite c₁ c₃ c₂ b₁ b₂ b₃ hn _ _
  have hn₁ : {i | n₁ i ≠ 0}.Finite := hn.subset fun i hi ↦ by simp_all
  have hn₃ : {i | n₃ i ≠ 0}.Finite := hn.subset fun i hi ↦ by simp_all
  rw [reidemeisterTorsionWithHomology_eq_mul_of_shortExact hS c₁ c₃ c₂ hc₁ hc₃ b₁ b₂ b₃,
    reidemeisterTorsion_homologySequenceComplex_of_acyclic_X₂ hS h₂ b₁ b₂ b₃
      (finite_setOf_homology_rank_ne_zero c₁ b₁ hn₁)
      (finite_setOf_homology_rank_ne_zero c₃ b₃ hn₃)]
  congr 1
  refine finprod_congr fun j ↦ ?_
  have hf₀ : LinearMap.range (homologyMap S.f (j + 1)).hom = ⊥ := by
    rw [Subsingleton.elim (homologyMap S.f (j + 1)).hom 0, LinearMap.range_zero]
  have hg₀ : LinearMap.range (homologyMap S.g (j + 1)).hom = ⊥ := by
    rw [Subsingleton.elim (homologyMap S.g (j + 1)).hom 0, LinearMap.range_zero]
  rw [hf₀, hg₀, finrank_bot, finrank_bot, zero_add, zero_mul, add_zero]

end Corollaries

end HomologicalComplex
