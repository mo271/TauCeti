/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Interleave
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Homology
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.LinearAlgebra.Alternating.Append

/-!
# Multiplicativity of torsion with homology bases

Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of `ℤ`-graded chain complexes of
vector spaces over a field `F`. Its long exact homology sequence is the acyclic chain complex
`CategoryTheory.ShortComplex.ShortExact.homologySequenceComplex`, with `Hᵢ(S.X₁)`, `Hᵢ(S.X₂)` and
`Hᵢ(S.X₃)` in degrees `3i + 2`, `3i + 1` and `3i`. Ordered bases of the homology groups assemble
into ordered bases of this complex (`ChainComplex.interleave.basis`), whose Reidemeister torsion is
nonzero once only finitely many homology groups are nonzero
(`CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero`).

This file proves Milnor's multiplicativity formula for the torsion with homology bases of a short
exact sequence of complexes that need not be acyclic
(`CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsionWithHomology_eq_mul`): with compatible
chain bases `(c₁, c₂, c₃)` and arbitrary homology bases `(h₁, h₂, h₃)`,

`τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃) · τ(H)`,

where `H` is the based long exact homology sequence and
`ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim im(f_*)_{j+1} + (dim B₃,ⱼ₊₁ + dim im(g_*)_{j+1}) · dim B₁,ⱼ)`
is the explicit Koszul sign.

When the connecting homomorphisms vanish (in particular for a split short exact sequence or a
biproduct `C₁ ⊞ C₃`) and the homology bases are compatible, the torsion of the long exact homology
sequence is `1`
(`CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_eq_one`), so
the formula simplifies to a direct product of the torsions of the outer terms
(`CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsionWithHomology_eq_mul_of_δ_eq_zero`,
`CategoryTheory.ShortComplex.Splitting.reidemeisterTorsionWithHomology_eq_mul`,
`HomologicalComplex.reidemeisterTorsionWithHomology_biprod`).

## Main declarations

* `ChainComplex.interleave.reidemeisterTorsion_basis_eq_mul`: basis-change formula for the
  Reidemeister torsion of an interleaved complex.
* `ChainComplex.interleave.reidemeisterTorsion_basis_eq_one`: an interleaved complex with bases
  adapted to its differentials has Reidemeister torsion `1`.
* `CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero`: the
  based long exact homology sequence has nonzero torsion.
* `CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsionWithHomology_eq_mul`: Milnor's
  multiplicativity formula for torsion with homology bases in a short exact sequence.
* `CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_eq_one`:
  when the connecting maps vanish and the homology bases are compatible, the torsion of the long
  exact homology sequence is `1`.
* `CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsionWithHomology_eq_mul_of_δ_eq_zero`,
  `CategoryTheory.ShortComplex.Splitting.reidemeisterTorsionWithHomology_eq_mul`,
  `HomologicalComplex.reidemeisterTorsionWithHomology_biprod`: multiplicativity for sequences with
  vanishing connecting maps, split short exact sequences, and direct sums.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3, Theorem 3.2.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, Theorem 1.14.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Appendix A, Proposition A.2.
-/

public section

noncomputable section

open CategoryTheory Module

namespace ChainComplex.interleave

variable {F : Type*} [Field F] {X₁ X₂ X₃ : ℤ → ModuleCat F} {f : ∀ q, X₁ q ⟶ X₂ q}
  {g : ∀ q, X₂ q ⟶ X₃ q} {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q} (hfg : ∀ q, f q ≫ g q = 0)
  (hgδ : ∀ q, g (q + 1) ≫ δ q = 0) (hδf : ∀ q, δ q ≫ f q = 0)

section BasisChange

variable {m₁ m₂ m₃ : ℤ → ℕ}
  (b₁ b₁' : ∀ q, Basis (Fin (m₁ q)) F (X₁ q))
  (b₂ b₂' : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
  (b₃ b₃' : ∀ q, Basis (Fin (m₃ q)) F (X₃ q))

private theorem det_basis_of_iso {A B : ModuleCat F} {n m : ℕ} (e : A ≅ B)
    (b b' : Basis (Fin n) F A) (c c' : Basis (Fin m) F B) (hm : n = m)
    (hb : ∀ i, e.hom.hom (b i) = c (Fin.cast hm i))
    (hb' : ∀ i, e.hom.hom (b' i) = c' (Fin.cast hm i)) :
    b.det b' = c.det c' := by
  have h1 : b = (c.reindex (finCongr hm.symm)).map e.toLinearEquiv.symm :=
    Basis.eq_of_apply_eq fun i ↦ by
      apply e.toLinearEquiv.injective
      simp [hb]
  have h2 : b' = (c'.reindex (finCongr hm.symm)).map e.toLinearEquiv.symm :=
    Basis.eq_of_apply_eq fun i ↦ by
      apply e.toLinearEquiv.injective
      simp [hb']
  rw [h1, h2, Basis.det_map, Basis.det_reindex]
  congr 1
  ext i
  simp

/-- The basis-change formula for an interleaved complex: replacing the three families of bases
`(b₁, b₂, b₃)` by `(b₁', b₂', b₃')` multiplies the Reidemeister torsion by the alternating
products of the basis-change determinants, with exponents `(-1) ^ q`, `(-1) ^ (q + 1)` and
`(-1) ^ q` according to the degrees `3q + 2`, `3q + 1` and `3q`. This holds unconditionally, both
sides being `0` when the interleaved complex is unbounded or not acyclic. -/
theorem reidemeisterTorsion_basis_eq_mul :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion
        (interleave.basis hfg hgδ hδf b₁' b₂' b₃') =
      (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion
        (interleave.basis hfg hgδ hδf b₁ b₂ b₃) *
        ((∏ᶠ q : ℤ, (b₁ q).det (b₁' q) ^ (q.negOnePow : ℤ)) *
          (∏ᶠ q : ℤ, (b₂ q).det (b₂' q) ^ ((q + 1).negOnePow : ℤ)) *
          (∏ᶠ q : ℤ, (b₃ q).det (b₃' q) ^ (q.negOnePow : ℤ))) := by
  by_cases hn : {n | interleave.rank m₁ m₂ m₃ n ≠ 0}.Finite
  swap
  · simp [HomologicalComplex.reidemeisterTorsion_of_not_finite _ _ hn]
  rw [HomologicalComplex.reidemeisterTorsion_eq_mul_finprod_det _
    (interleave.basis hfg hgδ hδf b₁ b₂ b₃) (interleave.basis hfg hgδ hδf b₁' b₂' b₃')]
  congr 1
  let D : ℤ → F := fun n ↦
    (interleave.basis hfg hgδ hδf b₁ b₂ b₃ n).det
      (interleave.basis hfg hgδ hδf b₁' b₂' b₃' n) ^ (n.negOnePow : ℤ)
  have hD : Function.HasFiniteMulSupport D :=
    hn.subset <| Function.mulSupport_subset_iff'.2 fun n h0 ↦ by
      have hr : interleave.rank m₁ m₂ m₃ n = 0 := by simpa using h0
      have : IsEmpty (Fin (interleave.rank m₁ m₂ m₃ n)) := by rw [hr]; infer_instance
      simp [D]
  have hD' : Function.HasFiniteMulSupport (Function.uncurry fun q (r : Fin 3) ↦ D (q * 3 + r)) :=
    hD.preimage (Int.divModEquiv 3).symm.injective.injOn
  have hsplit : ∏ᶠ n : ℤ, D n =
      (∏ᶠ q : ℤ, D (3 * q)) * (∏ᶠ q : ℤ, D (3 * q + 1)) * (∏ᶠ q : ℤ, D (3 * q + 2)) :=
    calc ∏ᶠ n : ℤ, D n
        = ∏ᶠ p : ℤ × Fin 3, D (p.1 * 3 + p.2) :=
          (finprod_comp_equiv (Int.divModEquiv 3).symm).symm
      _ = ∏ᶠ q : ℤ, ∏ᶠ r : Fin 3, D (q * 3 + r) := finprod_curry _ hD'
      _ = ∏ᶠ r : Fin 3, ∏ᶠ q : ℤ, D (q * 3 + r) := TauCeti.finprod_comm hD'
      _ = ∏ r : Fin 3, ∏ᶠ q : ℤ, D (q * 3 + r) := finprod_eq_prod_of_fintype _
      _ = (∏ᶠ q : ℤ, D (3 * q)) * (∏ᶠ q : ℤ, D (3 * q + 1)) * (∏ᶠ q : ℤ, D (3 * q + 2)) := by
          simp [Fin.prod_univ_three, mul_comm (3 : ℤ)]
  have hp0 (q : ℤ) : (3 * q).negOnePow = q.negOnePow := by
    rw [show 3 * q = q + 2 * q by omega, Int.negOnePow_add,
      Int.negOnePow_even (2 * q) (even_two_mul q), mul_one]
  have hp1 (q : ℤ) : (3 * q + 1).negOnePow = (q + 1).negOnePow := by
    rw [show 3 * q + 1 = (q + 1) + 2 * q by omega, Int.negOnePow_add,
      Int.negOnePow_even (2 * q) (even_two_mul q), mul_one]
  have hp2 (q : ℤ) : (3 * q + 2).negOnePow = q.negOnePow := by
    rw [show 3 * q + 2 = q + 2 * (q + 1) by omega, Int.negOnePow_add,
      Int.negOnePow_even (2 * (q + 1)) (even_two_mul (q + 1)), mul_one]
  have h0 : ∏ᶠ q : ℤ, D (3 * q) = ∏ᶠ q : ℤ, (b₃ q).det (b₃' q) ^ (q.negOnePow : ℤ) :=
    finprod_congr fun q ↦ by
      dsimp only [D]
      rw [det_basis_of_iso (XIso₃ hfg hgδ hδf (3 * q) q rfl) _ _ (b₃ q) (b₃' q)
        (rank_of_eq_three_mul rfl)
        (fun i ↦ XIso₃_hom_basis hfg hgδ hδf b₁ b₂ b₃ rfl i)
        (fun i ↦ XIso₃_hom_basis hfg hgδ hδf b₁' b₂' b₃' rfl i), hp0]
  have h1 : ∏ᶠ q : ℤ, D (3 * q + 1) = ∏ᶠ q : ℤ, (b₂ q).det (b₂' q) ^ ((q + 1).negOnePow : ℤ) :=
    finprod_congr fun q ↦ by
      dsimp only [D]
      rw [det_basis_of_iso (XIso₂ hfg hgδ hδf (3 * q + 1) q rfl) _ _ (b₂ q) (b₂' q)
        (rank_of_eq_three_mul_add_one rfl)
        (fun i ↦ XIso₂_hom_basis hfg hgδ hδf b₁ b₂ b₃ rfl i)
        (fun i ↦ XIso₂_hom_basis hfg hgδ hδf b₁' b₂' b₃' rfl i), hp1]
  have h2 : ∏ᶠ q : ℤ, D (3 * q + 2) = ∏ᶠ q : ℤ, (b₁ q).det (b₁' q) ^ (q.negOnePow : ℤ) :=
    finprod_congr fun q ↦ by
      dsimp only [D]
      rw [det_basis_of_iso (XIso₁ hfg hgδ hδf (3 * q + 2) q rfl) _ _ (b₁ q) (b₁' q)
        (rank_of_eq_three_mul_add_two rfl)
        (fun i ↦ XIso₁_hom_basis hfg hgδ hδf b₁ b₂ b₃ rfl i)
        (fun i ↦ XIso₁_hom_basis hfg hgδ hδf b₁' b₂' b₃' rfl i), hp2]
  rw [show (∏ᶠ n : ℤ, _) = ∏ᶠ n : ℤ, D n from rfl, hsplit, h0, h1, h2]
  ring

end BasisChange

section Adapted

private theorem hom_inv_hom_apply {A B : ModuleCat F} (e : A ≅ B) (x : B) :
    e.hom.hom (e.inv.hom x) = x :=
  Iso.inv_hom_id_apply e x

/-- Transport the range of a morphism `v : A' ⟶ B'` along isomorphisms `e₁ : A ≅ A'` and
`e₂ : B ≅ B'` to the range of `u = e₁.hom ≫ v ≫ e₂.inv`. -/
private def rangeEquivOfIso {A A' B B' : ModuleCat F} (e₁ : A ≅ A') (e₂ : B ≅ B')
    {u : A ⟶ B} {v : A' ⟶ B'} (h : u = e₁.hom ≫ v ≫ e₂.inv) :
    LinearMap.range v.hom ≃ₗ[F] LinearMap.range u.hom :=
  (e₂.symm.toLinearEquiv.submoduleMap (LinearMap.range v.hom)).trans <|
    LinearEquiv.ofEq _ _ <| by
      ext y
      simp only [h, ModuleCat.hom_comp, Submodule.mem_map, LinearMap.mem_range,
        LinearMap.comp_apply]
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨e₁.inv.hom x, by rw [hom_inv_hom_apply]; rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨v.hom (e₁.hom.hom x), ⟨e₁.hom.hom x, rfl⟩, rfl⟩

private theorem coe_rangeEquivOfIso {A A' B B' : ModuleCat F} (e₁ : A ≅ A') (e₂ : B ≅ B')
    {u : A ⟶ B} {v : A' ⟶ B'} (h : u = e₁.hom ≫ v ≫ e₂.inv) (x : LinearMap.range v.hom) :
    (rangeEquivOfIso e₁ e₂ h x : B) = e₂.inv.hom x :=
  rfl

/-- If the three families of bases `(b₁, b₂, b₃)` of a bounded interleaved complex are adapted to
its differentials — each basis lists a basis of the incoming image followed by lifts of a basis of
the outgoing image — then the interleaved complex is acyclic and its Reidemeister torsion is `1`. -/
theorem reidemeisterTorsion_basis_eq_one {m₁ m₂ m₃ a b g' : ℤ → ℕ}
    (b₁ : ∀ q, Basis (Fin (m₁ q)) F (X₁ q)) (b₂ : ∀ q, Basis (Fin (m₂ q)) F (X₂ q))
    (b₃ : ∀ q, Basis (Fin (m₃ q)) F (X₃ q))
    (h₁ : {q | m₁ q ≠ 0}.Finite) (h₂ : {q | m₂ q ≠ 0}.Finite) (h₃ : {q | m₃ q ≠ 0}.Finite)
    (α : ∀ q, Basis (Fin (a q)) F (LinearMap.range (δ q).hom))
    (β : ∀ q, Basis (Fin (b q)) F (LinearMap.range (f q).hom))
    (γ : ∀ q, Basis (Fin (g' q)) F (LinearMap.range (g q).hom))
    (sα : ∀ q, Fin (a q) → X₃ (q + 1)) (hsα : ∀ q k, (δ q).hom (sα q k) = α q k)
    (sβ : ∀ q, Fin (b q) → X₁ q) (hsβ : ∀ q k, (f q).hom (sβ q k) = β q k)
    (sγ : ∀ q, Fin (g' q) → X₂ q) (hsγ : ∀ q k, (g q).hom (sγ q k) = γ q k)
    (hm₁ : ∀ q, m₁ q = a q + b q)
    (hb₁ : ∀ q, ⇑(b₁ q) = Fin.append (fun k ↦ (α q k : X₁ q)) (sβ q) ∘ Fin.cast (hm₁ q))
    (hm₂ : ∀ q, m₂ q = b q + g' q)
    (hb₂ : ∀ q, ⇑(b₂ q) = Fin.append (fun k ↦ (β q k : X₂ q)) (sγ q) ∘ Fin.cast (hm₂ q))
    (hm₃ : ∀ q, m₃ (q + 1) = g' (q + 1) + a q)
    (hb₃ : ∀ q, ⇑(b₃ (q + 1)) =
      Fin.append (fun k ↦ (γ (q + 1) k : X₃ (q + 1))) (sα q) ∘ Fin.cast (hm₃ q)) :
    (interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).reidemeisterTorsion
        (interleave.basis hfg hgδ hδf b₁ b₂ b₃) = 1 := by
  let K := interleave X₁ X₂ X₃ f g δ hfg hgδ hδf
  let r (n : ℤ) : ℕ :=
    if n % 3 = 0 then g' (n / 3) else if n % 3 = 1 then b (n / 3) else a (n / 3)
  let B (n : ℤ) : Basis (Fin (r n)) F (LinearMap.range (K.d (n + 1) n).hom) :=
    if h₀ : n % 3 = 0 then
      ((γ (n / 3)).reindex (finCongr (by simp only [r, h₀, ↓reduceIte]))).map
        (rangeEquivOfIso (XIso₂ hfg hgδ hδf (n + 1) (n / 3) (by omega))
          (XIso₃ hfg hgδ hδf n (n / 3) (by omega))
          (interleave_d_eq_of_eq_three_mul hfg hgδ hδf (by omega)))
    else if h₁' : n % 3 = 1 then
      ((β (n / 3)).reindex (finCongr (by simp only [r, h₁', one_ne_zero, ↓reduceIte]))).map
        (rangeEquivOfIso (XIso₁ hfg hgδ hδf (n + 1) (n / 3) (by omega))
          (XIso₂ hfg hgδ hδf n (n / 3) (by omega))
          (interleave_d_eq_of_eq_three_mul_add_one hfg hgδ hδf (by omega)))
    else
      ((α (n / 3)).reindex (finCongr (by simp only [r, h₀, h₁', ↓reduceIte]))).map
        (rangeEquivOfIso (XIso₃ hfg hgδ hδf (n + 1) (n / 3 + 1) (by omega))
          (XIso₁ hfg hgδ hδf n (n / 3) (by omega))
          (interleave_d_eq_of_eq_three_mul_add_two hfg hgδ hδf (by omega)))
  let s (n : ℤ) : Fin (r n) → K.X (n + 1) :=
    if h₀ : n % 3 = 0 then
      fun k ↦ (XIso₂ hfg hgδ hδf (n + 1) (n / 3) (by omega)).inv.hom
        (sγ (n / 3) (Fin.cast (by simp only [r, h₀, ↓reduceIte]) k))
    else if h₁' : n % 3 = 1 then
      fun k ↦ (XIso₁ hfg hgδ hδf (n + 1) (n / 3) (by omega)).inv.hom
        (sβ (n / 3) (Fin.cast (by simp only [r, h₁', one_ne_zero, ↓reduceIte]) k))
    else
      fun k ↦ (XIso₃ hfg hgδ hδf (n + 1) (n / 3 + 1) (by omega)).inv.hom
        (sα (n / 3) (Fin.cast (by simp only [r, h₀, h₁', ↓reduceIte]) k))
  have hs (n : ℤ) (k : Fin (r n)) : (K.d (n + 1) n).hom (s n k) = B n k := by
    by_cases h₀ : n % 3 = 0
    · simp only [s, B, h₀, ↓reduceDIte, Basis.map_apply, coe_rangeEquivOfIso, Basis.reindex_apply,
        finCongr_symm, finCongr_apply]
      rw [interleave_d_eq_of_eq_three_mul hfg hgδ hδf (q := n / 3) (by omega)]
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hom_inv_hom_apply, hsγ]
    · by_cases h₁' : n % 3 = 1
      · simp only [s, B, h₁', one_ne_zero, ↓reduceDIte, Basis.map_apply, coe_rangeEquivOfIso,
          Basis.reindex_apply, finCongr_symm, finCongr_apply]
        rw [interleave_d_eq_of_eq_three_mul_add_one hfg hgδ hδf (q := n / 3) (by omega)]
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hom_inv_hom_apply, hsβ]
      · simp only [s, B, h₀, h₁', ↓reduceDIte, Basis.map_apply, coe_rangeEquivOfIso,
          Basis.reindex_apply, finCongr_symm, finCongr_apply]
        rw [interleave_d_eq_of_eq_three_mul_add_two hfg hgδ hδf (q := n / 3) (by omega)]
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hom_inv_hom_apply, hsα]
  have hr (n : ℤ) : interleave.rank m₁ m₂ m₃ (n + 1) = r (n + 1) + r n := by
    obtain ⟨q, hq | hq | hq⟩ : ∃ q, n = 3 * q ∨ n = 3 * q + 1 ∨ n = 3 * q + 2 :=
      ⟨n / 3, by omega⟩
    · rw [rank_of_eq_three_mul_add_one (q := q) (by omega), hm₂ q]
      simp only [r, show (n + 1) % 3 = 1 by omega, show (n + 1) / 3 = q by omega,
        show n % 3 = 0 by omega, show n / 3 = q by omega, one_ne_zero, ↓reduceIte]
    · rw [rank_of_eq_three_mul_add_two (q := q) (by omega), hm₁ q]
      simp only [r, show (n + 1) % 3 = 2 by omega, show (n + 1) / 3 = q by omega,
        show n % 3 = 1 by omega, show n / 3 = q by omega, one_ne_zero, ↓reduceIte,
        show (2 : ℤ) ≠ 0 by omega, show (2 : ℤ) ≠ 1 by omega]
    · rw [rank_of_eq_three_mul (q := q + 1) (by omega), hm₃ q]
      simp only [r, show (n + 1) % 3 = 0 by omega, show (n + 1) / 3 = q + 1 by omega,
        show n % 3 = 2 by omega, show n / 3 = q by omega, ↓reduceIte,
        show (2 : ℤ) ≠ 0 by omega, show (2 : ℤ) ≠ 1 by omega]
  refine HomologicalComplex.reidemeisterTorsion_eq_one_of_eq_append
    (finite_setOf_rank_ne_zero h₁ h₂ h₃) B s hs hr fun n ↦ funext fun k ↦ ?_
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, n = 3 * q ∨ n = 3 * q + 1 ∨ n = 3 * q + 2 :=
    ⟨n / 3, by omega⟩
  · apply (XIso₂ hfg hgδ hδf (n + 1) q (by omega)).toLinearEquiv.injective
    rw [Iso.toLinearEquiv_apply, XIso₂_hom_basis hfg hgδ hδf b₁ b₂ b₃ (by omega),
      congrFun (hb₂ q) _, Function.comp_apply, Function.comp_apply]
    have hq1 : (n + 1) % 3 = 1 := by omega
    have hq0 : n % 3 = 0 := by omega
    have hd1 : (n + 1) / 3 = q := by omega
    have hd0 : n / 3 = q := by omega
    have hr1 : r (n + 1) = b q := by simp only [r, hq1, hd1, one_ne_zero, ↓reduceIte]
    have hr0 : r n = g' q := by simp only [r, hq0, hd0, ↓reduceIte]
    obtain ⟨m, rfl⟩ := (finCongr (hr n).symm).surjective k
    simp only [finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq]
    induction m using Fin.addCases with
    | left l =>
      have hl : Fin.cast (by omega) (Fin.castAdd (r n) l) =
          Fin.castAdd (g' q) (Fin.cast hr1 l) := Fin.ext (by simp)
      rw [hl, Fin.append_left, Fin.append_left]
      simp only [B, hq1, one_ne_zero, ↓reduceDIte, Basis.map_apply,
        coe_rangeEquivOfIso, Basis.reindex_apply, finCongr_symm, finCongr_apply,
        Iso.toLinearEquiv_apply]
      clear hl
      subst hd1
      exact (hom_inv_hom_apply (XIso₂ hfg hgδ hδf (n + 1) ((n + 1) / 3) (by omega)) _).symm
    | right l =>
      have hl : Fin.cast (by omega) (Fin.natAdd (r (n + 1)) l) =
          Fin.natAdd (b q) (Fin.cast hr0 l) := Fin.ext (by simp [hr1])
      rw [hl, Fin.append_right, Fin.append_right]
      simp only [s, hq0, ↓reduceDIte, Iso.toLinearEquiv_apply]
      clear hl
      subst hd0
      exact (hom_inv_hom_apply (XIso₂ hfg hgδ hδf (n + 1) (n / 3) (by omega)) _).symm
  · apply (XIso₁ hfg hgδ hδf (n + 1) q (by omega)).toLinearEquiv.injective
    rw [Iso.toLinearEquiv_apply, XIso₁_hom_basis hfg hgδ hδf b₁ b₂ b₃ (by omega),
      congrFun (hb₁ q) _, Function.comp_apply, Function.comp_apply]
    have hq2 : (n + 1) % 3 = 2 := by omega
    have hq1 : n % 3 = 1 := by omega
    have hd1 : (n + 1) / 3 = q := by omega
    have hd0 : n / 3 = q := by omega
    have hr1 : r (n + 1) = a q := by
      simp only [r, hq2, hd1, show (2 : ℤ) ≠ 0 by omega, show (2 : ℤ) ≠ 1 by omega, ↓reduceIte]
    have hr0 : r n = b q := by simp only [r, hq1, hd0, one_ne_zero, ↓reduceIte]
    obtain ⟨m, rfl⟩ := (finCongr (hr n).symm).surjective k
    simp only [finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq]
    induction m using Fin.addCases with
    | left l =>
      have hl : Fin.cast (by omega) (Fin.castAdd (r n) l) =
          Fin.castAdd (b q) (Fin.cast hr1 l) := Fin.ext (by simp)
      rw [hl, Fin.append_left, Fin.append_left]
      simp only [B, show (n + 1) % 3 ≠ 0 by omega, show (n + 1) % 3 ≠ 1 by omega, ↓reduceDIte,
        Basis.map_apply, coe_rangeEquivOfIso, Basis.reindex_apply, finCongr_symm, finCongr_apply,
        Iso.toLinearEquiv_apply]
      clear hl
      subst hd1
      exact (hom_inv_hom_apply (XIso₁ hfg hgδ hδf (n + 1) ((n + 1) / 3) (by omega)) _).symm
    | right l =>
      have hl : Fin.cast (by omega) (Fin.natAdd (r (n + 1)) l) =
          Fin.natAdd (a q) (Fin.cast hr0 l) := Fin.ext (by simp [hr1])
      rw [hl, Fin.append_right, Fin.append_right]
      simp only [s, hq1, one_ne_zero, ↓reduceDIte, Iso.toLinearEquiv_apply]
      clear hl
      subst hd0
      exact (hom_inv_hom_apply (XIso₁ hfg hgδ hδf (n + 1) (n / 3) (by omega)) _).symm
  · apply (XIso₃ hfg hgδ hδf (n + 1) (q + 1) (by omega)).toLinearEquiv.injective
    rw [Iso.toLinearEquiv_apply, XIso₃_hom_basis hfg hgδ hδf b₁ b₂ b₃ (by omega),
      congrFun (hb₃ q) _, Function.comp_apply, Function.comp_apply]
    have hq0 : (n + 1) % 3 = 0 := by omega
    have hq2 : n % 3 = 2 := by omega
    have hd1 : (n + 1) / 3 = q + 1 := by omega
    have hd0 : n / 3 = q := by omega
    have hr1 : r (n + 1) = g' (q + 1) := by simp only [r, hq0, hd1, ↓reduceIte]
    have hr0 : r n = a q := by
      simp only [r, hq2, hd0, show (2 : ℤ) ≠ 0 by omega, show (2 : ℤ) ≠ 1 by omega, ↓reduceIte]
    obtain ⟨m, rfl⟩ := (finCongr (hr n).symm).surjective k
    simp only [finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq]
    induction m using Fin.addCases with
    | left l =>
      have hl : Fin.cast (by omega) (Fin.castAdd (r n) l) =
          Fin.castAdd (a q) (Fin.cast hr1 l) := Fin.ext (by simp)
      rw [hl, Fin.append_left, Fin.append_left]
      simp only [B, hq0, ↓reduceDIte, Basis.map_apply, coe_rangeEquivOfIso, Basis.reindex_apply,
        finCongr_symm, finCongr_apply, Iso.toLinearEquiv_apply]
      have hdiv : ∀ (d : ℤ) (h1 : n + 1 = 3 * d) (h2 : r (n + 1) = g' d), d = q + 1 →
          (γ (q + 1) (Fin.cast hr1 l) : X₃ (q + 1)) =
            (XIso₃ hfg hgδ hδf (n + 1) (q + 1) (by omega)).hom.hom
              ((XIso₃ hfg hgδ hδf (n + 1) d h1).inv.hom (γ d (Fin.cast h2 l))) := by
        rintro _ h1 h2 rfl
        exact (hom_inv_hom_apply (XIso₃ hfg hgδ hδf (n + 1) (q + 1) h1) _).symm
      exact hdiv ((n + 1) / 3) (by omega) _ hd1
    | right l =>
      have hl : Fin.cast (by omega) (Fin.natAdd (r (n + 1)) l) =
          Fin.natAdd (g' (q + 1)) (Fin.cast hr0 l) := Fin.ext (by simp [hr1])
      rw [hl, Fin.append_right, Fin.append_right]
      simp only [s, show n % 3 ≠ 0 by omega, show n % 3 ≠ 1 by omega, ↓reduceDIte,
        Iso.toLinearEquiv_apply]
      clear hl
      subst hd0
      exact (hom_inv_hom_apply (XIso₃ hfg hgδ hδf (n + 1) (n / 3 + 1) (by omega)) _).symm

end Adapted

end ChainComplex.interleave

namespace CategoryTheory.ShortComplex.ShortExact

variable {F : Type*} [Field F] {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
  (hS : S.ShortExact)

section Nonzero

variable {m₁ m₂ m₃ : ℤ → ℕ} (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
  (b₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
  (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))

/-- The long exact homology sequence, based by ordered bases of the homology groups of which only
finitely many are nonempty, has nonzero Reidemeister torsion. -/
theorem reidemeisterTorsion_homologySequenceComplex_ne_zero (h₁ : {i | m₁ i ≠ 0}.Finite)
    (h₂ : {i | m₂ i ≠ 0}.Finite) (h₃ : {i | m₃ i ≠ 0}.Finite) :
    hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) ≠ 0 :=
  HomologicalComplex.reidemeisterTorsion_ne_zero _ _
    (ChainComplex.interleave.finite_setOf_rank_ne_zero h₁ h₂ h₃)
    hS.acyclic_homologySequenceComplex

end Nonzero

section Multiplicativity

/-- Reordering six concatenated blocks `(A, B, C, D, E, G)` of arguments of an alternating map
into `((A, C, E), (B, D, G))` multiplies its value by `(-1) ^ (b * c + (b + d) * e)`, moving `B`
past `C` and then `(B, D)` past `E`. -/
private theorem map_append_six {M N : Type*} [AddCommMonoid M] [Module F M]
    [AddCommGroup N] [Module F N] {a b c d e f : ℕ}
    (φ : M [⋀^Fin ((a + c + e) + (b + d + f))]→ₗ[F] N)
    (A : Fin a → M) (B : Fin b → M) (C : Fin c → M) (D : Fin d → M)
    (E : Fin e → M) (G : Fin f → M) :
    φ (Fin.append (Fin.append (Fin.append A B) (Fin.append C D)) (Fin.append E G) ∘
        Fin.cast (by omega)) =
      (-1 : ℤˣ) ^ (b * c + (b + d) * e) •
        φ (Fin.append (Fin.append (Fin.append A C) E) (Fin.append (Fin.append B D) G)) := by
  let σ := finCongr (show (a + c + e) + (b + d + f) = (a + c) + (b + (d + (e + f))) by omega)
  have h1 := φ.map_append_append_comm (Fin.append A C) E (Fin.append B D) G
  have h2 := (φ.domDomCongr σ).map_append_append_comm A C B (Fin.append D (Fin.append E G))
  simp only [AlternatingMap.domDomCongr_apply] at h2
  have hL : Fin.append (Fin.append (Fin.append A B) (Fin.append C D)) (Fin.append E G) ∘
      Fin.cast (show (a + c + e) + (b + d + f) = ((a + b) + (c + d)) + (e + f) by omega) =
      (Fin.append (Fin.append A B) (Fin.append C (Fin.append D (Fin.append E G))) ∘
        Fin.cast (show (a + c) + (b + (d + (e + f))) = (a + b) + (c + (d + (e + f))) by omega)) ∘
        σ := by
    rw [Fin.append_assoc, Fin.append_assoc C D (Fin.append E G)]
    ext k
    simp only [σ, Function.comp_apply, finCongr_apply, Fin.cast_cast]
    obtain ⟨m, rfl⟩ := (finCongr (show (a + b) + (c + (d + (e + f))) =
      (a + c + e) + (b + d + f) by omega)).surjective k
    simp only [finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq]
    induction m using Fin.addCases with
    | left l =>
      have hcast : Fin.cast (show (a + b) + (c + (d + (e + f))) = (a + b) + (c + d + (e + f))
          by omega) (Fin.castAdd (c + (d + (e + f))) l) = Fin.castAdd (c + d + (e + f)) l :=
        Fin.ext rfl
      rw [hcast, Fin.append_left, Fin.append_left]
    | right r =>
      have hcast : Fin.cast (show (a + b) + (c + (d + (e + f))) = (a + b) + (c + d + (e + f))
          by omega) (Fin.natAdd (a + b) r) =
          Fin.natAdd (a + b) (Fin.cast (show c + (d + (e + f)) = c + d + (e + f) by omega) r) :=
        Fin.ext (by simp)
      rw [hcast, Fin.append_right, Fin.append_right, Function.comp_apply]
      congr 1
  have hR : Fin.append (Fin.append A C) (Fin.append B (Fin.append D (Fin.append E G))) ∘ σ =
      Fin.append (Fin.append (Fin.append A C) (Fin.append B D)) (Fin.append E G) ∘
        Fin.cast (show (a + c + e) + (b + d + f) = ((a + c) + (b + d)) + (e + f) by omega) := by
    rw [Fin.append_assoc (Fin.append A C) (Fin.append B D), Fin.append_assoc B D]
    ext k
    simp only [σ, Function.comp_apply, finCongr_apply, Fin.cast_cast]
    obtain ⟨m, rfl⟩ := (finCongr (show (a + c) + (b + (d + (e + f))) =
      (a + c + e) + (b + d + f) by omega)).surjective k
    simp only [finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq]
    induction m using Fin.addCases with
    | left l =>
      have hcast : Fin.cast (show (a + c) + (b + (d + (e + f))) = (a + c) + (b + d + (e + f))
          by omega) (Fin.castAdd (b + (d + (e + f))) l) = Fin.castAdd (b + d + (e + f)) l :=
        Fin.ext rfl
      rw [hcast, Fin.append_left, Fin.append_left]
    | right r =>
      have hcast : Fin.cast (show (a + c) + (b + (d + (e + f))) = (a + c) + (b + d + (e + f))
          by omega) (Fin.natAdd (a + c) r) =
          Fin.natAdd (a + c) (Fin.cast (show b + (d + (e + f)) = b + d + (e + f) by omega) r) :=
        Fin.ext (by simp)
      rw [hcast, Fin.append_right, Fin.append_right, Function.comp_apply]
      congr 1
  rw [hL, h2, hR, h1, ← mul_smul, ← pow_add, mul_comm c b, mul_comm e (b + d)]

/-- The submodule of degree-`j` cycles of `S.X₁` whose homology class lies in the image of the
connecting homomorphism `hS.δ (j + 1) j`. Under `S.f`, this maps isomorphically onto the
boundaries of `S.X₂` in degree `j` that vanish in `S.X₃`. -/
private def deltaPreimage (j : ℤ) :
    Submodule F (LinearMap.ker (S.X₁.d j ((ComplexShape.down ℤ).next j)).hom) :=
  (LinearMap.range (hS.δ (j + 1) j (ComplexShape.down_mk _ _ rfl)).hom).comap
    (S.X₁.moduleCatKerHomologyClass rfl)

private def deltaPreimageIncl (j : ℤ) :
    LinearMap.range (S.X₁.d (j + 1) j).hom →ₗ[F] deltaPreimage hS j :=
  (Submodule.inclusion (S.X₁.range_d_le_ker_d j (j + 1) _)).codRestrict (deltaPreimage hS j)
    fun y ↦ by
      have hprev : (ComplexShape.down ℤ).prev j = j + 1 :=
        (ComplexShape.down ℤ).prev_eq' (ComplexShape.down_mk _ _ rfl)
      simp only [deltaPreimage, Submodule.mem_comap]
      rw [(S.X₁.exact_inclusion_moduleCatKerHomologyClass (n := j) rfl hprev).apply_apply_eq_zero y]
      exact zero_mem _

private def deltaPreimageProj (j : ℤ) :
    deltaPreimage hS j →ₗ[F]
      LinearMap.range (hS.δ (j + 1) j (ComplexShape.down_mk _ _ rfl)).hom :=
  ((S.X₁.moduleCatKerHomologyClass rfl).domRestrict (deltaPreimage hS j)).codRestrict _
    fun z ↦ by
      rw [LinearMap.domRestrict_apply]
      exact z.2

private theorem deltaPreimageIncl_injective (j : ℤ) :
    Function.Injective (deltaPreimageIncl hS j) := fun _ _ h ↦
  Submodule.inclusion_injective _ (congrArg Subtype.val h)

private theorem exact_deltaPreimageIncl_deltaPreimageProj (j : ℤ) :
    Function.Exact (deltaPreimageIncl hS j) (deltaPreimageProj hS j) := fun z ↦ by
  have hprev : (ComplexShape.down ℤ).prev j = j + 1 :=
    (ComplexShape.down ℤ).prev_eq' (ComplexShape.down_mk _ _ rfl)
  rw [Subtype.ext_iff]
  change S.X₁.moduleCatKerHomologyClass rfl z.1 = 0 ↔ z ∈ Set.range (deltaPreimageIncl hS j)
  rw [S.X₁.exact_inclusion_moduleCatKerHomologyClass (n := j) rfl hprev z.1]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, Subtype.ext hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, congrArg Subtype.val hy⟩⟩

/-- A basis of `deltaPreimage hS j`, made of a basis `b₁` of the boundaries `B₁,ⱼ` followed by
cycles `x` representing a basis `α` of `im (hS.δ (j + 1) j)`. -/
private def deltaPreimageBasis {j : ℤ} {p₁ a : ℕ}
    (b₁ : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (α : Basis (Fin a) F (LinearMap.range (hS.δ (j + 1) j (ComplexShape.down_mk _ _ rfl)).hom))
    (x : Fin a → S.X₁.cycles j) (hx : ∀ k, (S.X₁.homologyπ j).hom (x k) = α k) :
    Basis (Fin (p₁ + a)) F (deltaPreimage hS j) :=
  (Basis.ofExactLift (deltaPreimageIncl_injective hS j)
    (exact_deltaPreimageIncl_deltaPreimageProj hS j) b₁ α
    (fun k ↦ ⟨S.X₁.moduleCatCyclesToKer j _ (x k), by
      simp only [deltaPreimage, Submodule.mem_comap,
        HomologicalComplex.moduleCatKerHomologyClass_moduleCatCyclesToKer]
      rw [show (S.X₁.homologyπ j) (x k) = α k from hx k]
      exact (α k).2⟩)
    fun k ↦ Subtype.ext <| by
      change S.X₁.moduleCatKerHomologyClass rfl (S.X₁.moduleCatCyclesToKer j _ (x k)) = α k
      rw [HomologicalComplex.moduleCatKerHomologyClass_moduleCatCyclesToKer]
      exact hx k).reindex finSumFinEquiv

private theorem coe_deltaPreimageBasis {j : ℤ} {p₁ a : ℕ}
    (b₁ : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (α : Basis (Fin a) F (LinearMap.range (hS.δ (j + 1) j (ComplexShape.down_mk _ _ rfl)).hom))
    (x : Fin a → S.X₁.cycles j) (hx : ∀ k, (S.X₁.homologyπ j).hom (x k) = α k) :
    (fun k ↦ ((deltaPreimageBasis hS b₁ α x hx k).1 : S.X₁.X j)) =
      Fin.append (fun k ↦ (b₁ k : S.X₁.X j)) (fun k ↦ (S.X₁.iCycles j).hom (x k)) := by
  funext k
  induction k using Fin.addCases with
  | left i =>
    simp [deltaPreimageBasis, deltaPreimageIncl]
  | right i =>
    simp [deltaPreimageBasis]

private def deltaPreimageToRange (j : ℤ) :
    deltaPreimage hS j →ₗ[F] LinearMap.range (S.X₂.d (j + 1) j).hom :=
  (((S.f.f j).hom.comp (Submodule.subtype _)).comp (Submodule.subtype _)).codRestrict _ fun z ↦
    ((hS.moduleCat_mem_range_d_and_g_eq_zero_iff (j + 1) j _ (ComplexShape.down_mk _ _ rfl) rfl
      ((S.f.f j).hom z.1.1)).2 ⟨z.1, rfl, z.2⟩).1

private theorem coe_deltaPreimageToRange (j : ℤ) (z : deltaPreimage hS j) :
    (deltaPreimageToRange hS j z : S.X₂.X j) = (S.f.f j).hom z.1.1 :=
  rfl

private theorem deltaPreimageToRange_injective (j : ℤ) :
    Function.Injective (deltaPreimageToRange hS j) := fun _ _ h ↦
  Subtype.ext <| Subtype.ext <|
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS j).moduleCat_injective_f
      (congrArg Subtype.val h)

private theorem exact_deltaPreimageToRange_boundaryMap (j : ℤ) :
    Function.Exact (deltaPreimageToRange hS j) (S.g.boundaryMap (j + 1) j) := fun y ↦ by
  rw [Subtype.ext_iff, HomologicalComplex.Hom.coe_boundaryMap, ZeroMemClass.coe_zero]
  constructor
  · intro hgy
    obtain ⟨z, hfz, hz⟩ :=
      (hS.moduleCat_mem_range_d_and_g_eq_zero_iff (j + 1) j _ (ComplexShape.down_mk _ _ rfl) rfl
        y.1).1 ⟨y.2, hgy⟩
    exact ⟨⟨z, hz⟩, Subtype.ext hfz⟩
  · rintro ⟨z, rfl⟩
    exact ((hS.moduleCat_mem_range_d_and_g_eq_zero_iff (j + 1) j _
      (ComplexShape.down_mk _ _ rfl) rfl ((S.f.f j).hom z.1.1)).2 ⟨z.1, rfl, z.2⟩).2

/-- A basis of the boundaries `B₂,ⱼ` of the middle term `S.X₂` of a short exact sequence of chain
complexes, assembled from a basis `b₁` of `B₁,ⱼ`, cycles `x` representing a basis `α` of
`im (hS.δ (j + 1) j)`, and differentials of lifts `t₃` of lifts of a basis `b₃` of `B₃,ⱼ`. -/
private def shortExactBoundaryBasisWithHomology {j : ℤ} {p₁ a p₃ : ℕ}
    (b₁ : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (α : Basis (Fin a) F (LinearMap.range (hS.δ (j + 1) j (ComplexShape.down_mk _ _ rfl)).hom))
    (x : Fin a → S.X₁.cycles j) (hx : ∀ k, (S.X₁.homologyπ j).hom (x k) = α k)
    (b₃ : Basis (Fin p₃) F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t₃ : Fin p₃ → S.X₂.X (j + 1))
    (ht₃ : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t₃ k)) = b₃ k) :
    Basis (Fin (p₁ + a + p₃)) F (LinearMap.range (S.X₂.d (j + 1) j).hom) :=
  (Basis.ofExactLift (deltaPreimageToRange_injective hS j)
    (exact_deltaPreimageToRange_boundaryMap hS j) (deltaPreimageBasis hS b₁ α x hx) b₃
    (fun k ↦ ⟨(S.X₂.d (j + 1) j).hom (t₃ k), t₃ k, rfl⟩)
    fun k ↦ Subtype.ext <|
      (HomologicalComplex.Hom.coe_boundaryMap S.g _ _ _).trans <|
        (HomologicalComplex.Hom.comm_apply S.g _ _ _).symm.trans (ht₃ k)).reindex finSumFinEquiv

private theorem coe_shortExactBoundaryBasisWithHomology {j : ℤ} {p₁ a p₃ : ℕ}
    (b₁ : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (α : Basis (Fin a) F (LinearMap.range (hS.δ (j + 1) j (ComplexShape.down_mk _ _ rfl)).hom))
    (x : Fin a → S.X₁.cycles j) (hx : ∀ k, (S.X₁.homologyπ j).hom (x k) = α k)
    (b₃ : Basis (Fin p₃) F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t₃ : Fin p₃ → S.X₂.X (j + 1))
    (ht₃ : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t₃ k)) = b₃ k) :
    (fun k ↦ (shortExactBoundaryBasisWithHomology hS b₁ α x hx b₃ t₃ ht₃ k : S.X₂.X j)) =
      Fin.append (Fin.append (fun k ↦ (S.f.f j).hom (b₁ k))
          (fun k ↦ (S.f.f j).hom ((S.X₁.iCycles j).hom (x k))))
        (fun k ↦ (S.X₂.d (j + 1) j).hom (t₃ k)) := by
  funext k
  induction k using Fin.addCases with
  | left l =>
    simp only [shortExactBoundaryBasisWithHomology, Basis.reindex_apply,
      finSumFinEquiv_symm_apply_castAdd, Basis.ofExactLift_inl, coe_deltaPreimageToRange,
      Fin.append_left]
    rw [congrFun (coe_deltaPreimageBasis hS b₁ α x hx) l]
    induction l using Fin.addCases <;> simp
  | right r =>
    simp [shortExactBoundaryBasisWithHomology]

private theorem rank_eq_add_add {C : ChainComplex (ModuleCat F) ℤ} {j : ℤ} {n p m q : ℕ}
    (c : Basis (Fin n) F (C.X (j + 1)))
    (b₁ : Basis (Fin p) F (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom))
    (h : Basis (Fin m) F (C.homology (j + 1)))
    (y : Fin m → C.cycles (j + 1)) (hy : ∀ k, (C.homologyπ (j + 1)).hom (y k) = h k)
    (b₀ : Basis (Fin q) F (LinearMap.range (C.d (j + 1) j).hom))
    (s : Fin q → C.X (j + 1)) (hs : ∀ k, (C.d (j + 1) j).hom (s k) = b₀ k) :
    n = p + m + q := by
  let bZ := Basis.ofExactLift (Submodule.inclusion_injective _)
    (C.exact_inclusion_moduleCatKerHomologyClass ((ComplexShape.down ℤ).next_eq' rfl)
      (ChainComplex.prev ℤ (j + 1))) b₁ h (C.moduleCatCyclesToKer (j + 1) j ∘ y) fun k ↦ by
    rw [Function.comp_apply, HomologicalComplex.moduleCatKerHomologyClass_moduleCatCyclesToKer]
    exact hy k
  let bX := Basis.ofExactLift (Submodule.injective_subtype _)
    (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
    bZ b₀ s fun k ↦ Subtype.ext (hs k)
  simpa using Fintype.card_congr (c.indexEquiv bX)

/-- The degree-`(j + 1)` bracket of the middle term `S.X₂` for adapted homology bases and the
boundary bases `shortExactBoundaryBasisWithHomology` is `(-1) ^ (p₃' * b' + (p₃' + g') * p₁)`
times the product of the brackets of `S.X₁` and `S.X₃`. -/
private theorem torsionBracketWithHomology_shortExactBoundaryBasis {j : ℤ} {n₁ n₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    {p₁' a' p₃' b' g' p₁ a p₃ m₁' m₂' m₃' : ℕ}
    (b₁' : Basis (Fin p₁') F (LinearMap.range (S.X₁.d (j + 1 + 1) (j + 1)).hom))
    (α' : Basis (Fin a') F (LinearMap.range (hS.δ (j + 1 + 1) (j + 1) rfl).hom))
    (x' : Fin a' → S.X₁.cycles (j + 1)) (hx' : ∀ k, (S.X₁.homologyπ (j + 1)).hom (x' k) = α' k)
    (b₃' : Basis (Fin p₃') F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom))
    (t₃' : Fin p₃' → S.X₂.X (j + 1 + 1))
    (ht₃' : ∀ k, (S.X₃.d (j + 1 + 1) (j + 1)).hom ((S.g.f (j + 1 + 1)).hom (t₃' k)) = b₃' k)
    (u' : Fin b' → S.X₁.cycles (j + 1)) (v' : Fin g' → S.X₂.cycles (j + 1))
    (b₁ : Basis (Fin p₁) F (LinearMap.range (S.X₁.d (j + 1) j).hom))
    (s₁ : Fin p₁ → S.X₁.X (j + 1)) (hs₁ : ∀ k, (S.X₁.d (j + 1) j).hom (s₁ k) = b₁ k)
    (α : Basis (Fin a) F (LinearMap.range (hS.δ (j + 1) j rfl).hom))
    (x : Fin a → S.X₁.cycles j) (hx : ∀ k, (S.X₁.homologyπ j).hom (x k) = α k)
    (w : Fin a → S.X₂.X (j + 1)) (z₃ : Fin a → S.X₃.cycles (j + 1))
    (hw_g : ∀ k, (S.g.f (j + 1)).hom (w k) = (S.X₃.iCycles (j + 1)).hom (z₃ k))
    (b₃ : Basis (Fin p₃) F (LinearMap.range (S.X₃.d (j + 1) j).hom))
    (t₃ : Fin p₃ → S.X₂.X (j + 1))
    (ht₃ : ∀ k, (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t₃ k)) = b₃ k)
    (h₁' : Basis (Fin m₁') F (S.X₁.homology (j + 1))) (hm₁' : m₁' = a' + b')
    (hy₁' : ∀ k, (S.X₁.homologyπ (j + 1)).hom (Fin.append x' u' (Fin.cast hm₁' k)) = h₁' k)
    (h₂' : Basis (Fin m₂') F (S.X₂.homology (j + 1))) (hm₂' : m₂' = b' + g')
    (hy₂' : ∀ k, (S.X₂.homologyπ (j + 1)).hom
      (Fin.append (fun l ↦ (HomologicalComplex.cyclesMap S.f (j + 1)).hom (u' l)) v'
        (Fin.cast hm₂' k)) = h₂' k)
    (h₃' : Basis (Fin m₃') F (S.X₃.homology (j + 1))) (hm₃' : m₃' = g' + a)
    (hy₃' : ∀ k, (S.X₃.homologyπ (j + 1)).hom
      (Fin.append (fun l ↦ (HomologicalComplex.cyclesMap S.g (j + 1)).hom (v' l)) z₃
        (Fin.cast hm₃' k)) = h₃' k)
    (hs₂ : ∀ k, (S.X₂.d (j + 1) j).hom
        (Fin.append (Fin.append (fun l ↦ (S.f.f (j + 1)).hom (s₁ l)) w) t₃ k) =
      shortExactBoundaryBasisWithHomology hS b₁ α x hx b₃ t₃ ht₃ k) :
    HomologicalComplex.torsionBracketWithHomology c₂
        (shortExactBoundaryBasisWithHomology hS b₁' α' x' hx' b₃' t₃' ht₃')
        h₂' (Fin.append (fun l ↦ (HomologicalComplex.cyclesMap S.f (j + 1)).hom (u' l)) v' ∘
          Fin.cast hm₂') hy₂'
        (shortExactBoundaryBasisWithHomology hS b₁ α x hx b₃ t₃ ht₃)
        (Fin.append (Fin.append (fun l ↦ (S.f.f (j + 1)).hom (s₁ l)) w) t₃) hs₂ =
      (-1) ^ (p₃' * b' + (p₃' + g') * p₁) *
        (HomologicalComplex.torsionBracketWithHomology c₁ b₁' h₁'
            (Fin.append x' u' ∘ Fin.cast hm₁') hy₁' b₁ s₁ hs₁ *
          HomologicalComplex.torsionBracketWithHomology c₃ b₃' h₃'
            (Fin.append (fun l ↦ (HomologicalComplex.cyclesMap S.g (j + 1)).hom (v' l)) z₃ ∘
              Fin.cast hm₃') hy₃'
            b₃ (fun l ↦ (S.g.f (j + 1)).hom (t₃ l)) ht₃) := by
  have hS' := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS (j + 1)
  have hf := hS'.moduleCat_injective_f
  have hfg := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS'.exact
  have hn₁ : n₁ (j + 1) = p₁' + m₁' + p₁ :=
    rank_eq_add_add (c₁ (j + 1)) b₁' h₁' (Fin.append x' u' ∘ Fin.cast hm₁') hy₁' b₁ s₁ hs₁
  have hn₃ : n₃ (j + 1) = p₃' + m₃' + p₃ :=
    rank_eq_add_add (c₃ (j + 1)) b₃' h₃'
      (Fin.append (fun l ↦ (HomologicalComplex.cyclesMap S.g (j + 1)).hom (v' l)) z₃ ∘
        Fin.cast hm₃') hy₃' b₃ (fun l ↦ (S.g.f (j + 1)).hom (t₃ l)) ht₃
  have hn₂ : n₁ (j + 1) + n₃ (j + 1) = (p₁' + a' + p₃') + m₂' + (p₁ + a + p₃) := by omega
  have hN : n₁ (j + 1) + n₃ (j + 1) = (p₁' + a' + b' + p₁) + (p₃' + g' + (a + p₃)) := by omega
  rw [HomologicalComplex.torsionBracketWithHomology_eq_det_append c₂ _ _ _ _ _ _ _ hn₂,
    coe_shortExactBoundaryBasisWithHomology,
    HomologicalComplex.torsionBracketWithHomology_eq_det_append c₁ _ _ _ _ _ _ _ hn₁,
    HomologicalComplex.torsionBracketWithHomology_eq_det_append c₃ _ _ _ _ _ _ _ hn₃]
  -- Identify the six blocks of the `S.X₂` bracket family.
  let A : Fin (p₁' + a') → S.X₂.X (j + 1) :=
    Fin.append (fun l ↦ (S.f.f (j + 1)).hom (b₁' l))
      (fun l ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (x' l)))
  let B : Fin p₃' → S.X₂.X (j + 1) := fun l ↦ (S.X₂.d (j + 1 + 1) (j + 1)).hom (t₃' l)
  let C : Fin b' → S.X₂.X (j + 1) :=
    fun l ↦ (S.f.f (j + 1)).hom ((S.X₁.iCycles (j + 1)).hom (u' l))
  let D : Fin g' → S.X₂.X (j + 1) := fun l ↦ (S.X₂.iCycles (j + 1)).hom (v' l)
  let E : Fin p₁ → S.X₂.X (j + 1) := fun l ↦ (S.f.f (j + 1)).hom (s₁ l)
  let G : Fin (a + p₃) → S.X₂.X (j + 1) := Fin.append w t₃
  have hfam : Fin.append (Fin.append (Fin.append A B)
        (fun k ↦ (S.X₂.iCycles (j + 1)).hom
          ((Fin.append (fun l ↦ (HomologicalComplex.cyclesMap S.f (j + 1)).hom (u' l)) v' ∘
            Fin.cast hm₂') k)))
        (Fin.append (Fin.append E w) t₃) ∘ Fin.cast hn₂ =
      (Fin.append (Fin.append (Fin.append A B) (Fin.append C D)) (Fin.append E G) ∘
        Fin.cast (by omega)) ∘ finCongr hN := by
    ext k
    simp only [Function.comp_apply, finCongr_apply, Fin.cast_cast]
    obtain ⟨m, rfl⟩ := (finCongr hn₂.symm).surjective k
    simp only [finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq]
    induction m using Fin.addCases with
    | left m =>
      induction m using Fin.addCases with
      | left l =>
        have hcast : Fin.cast (by omega) (Fin.castAdd (p₁ + a + p₃) (Fin.castAdd m₂' l)) =
            Fin.castAdd (p₁ + (a + p₃)) (Fin.castAdd (b' + g') l) := Fin.ext rfl
        rw [hcast, Fin.append_left, Fin.append_left, Fin.append_left, Fin.append_left]
      | right r =>
        have hcast : Fin.cast (by omega) (Fin.castAdd (p₁ + a + p₃)
            (Fin.natAdd (p₁' + a' + p₃') r)) =
            Fin.castAdd (p₁ + (a + p₃)) (Fin.natAdd (p₁' + a' + p₃') (Fin.cast hm₂' r)) :=
          Fin.ext (by simp)
        rw [hcast, Fin.append_left, Fin.append_right, Fin.append_left, Fin.append_right]
        generalize Fin.cast hm₂' r = r'
        induction r' using Fin.addCases with
        | left l =>
          rw [Fin.append_left, Fin.append_left]
          simp only [C, ← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i]
        | right l =>
          rw [Fin.append_right, Fin.append_right]
    | right r =>
      have hcast : Fin.cast (by omega) (Fin.natAdd (p₁' + a' + p₃' + m₂') r) =
          Fin.natAdd (p₁' + a' + p₃' + (b' + g')) (Fin.cast (add_assoc p₁ a p₃) r) :=
        Fin.ext (by simp; omega)
      rw [hcast, Fin.append_right, Fin.append_right, Fin.append_assoc E w t₃, Function.comp_apply]
  have hsw := map_append_six ((c₂ (j + 1)).reindex (finCongr hN)).det A B C D E G
  rw [Basis.det_reindex, Basis.det_reindex] at hsw
  rw [hfam, hsw, Basis.eq_reindex_ofExactLift hf hfg (c₁ (j + 1)) (c₃ (j + 1)) _
      (hc₁ (j + 1)) (hc₃ (j + 1)), Basis.det_reindex,
    Basis.ofExactLift_det_eq_mul _ _ _ _ _ _
      (Fin.append (Fin.append (fun k ↦ (b₁' k : S.X₁.X (j + 1)))
        fun k ↦ (S.X₁.iCycles (j + 1)).hom ((Fin.append x' u' ∘ Fin.cast hm₁') k)) s₁ ∘
          Fin.cast hn₁)
      (Fin.append (Fin.append (fun k ↦ (b₃' k : S.X₃.X (j + 1)))
        fun k ↦ (S.X₃.iCycles (j + 1)).hom
          ((Fin.append (fun l ↦ (HomologicalComplex.cyclesMap S.g (j + 1)).hom (v' l)) z₃ ∘
            Fin.cast hm₃') k))
        (fun l ↦ (S.g.f (j + 1)).hom (t₃ l)) ∘ Fin.cast hn₃) _ ?_ ?_]
  · simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  · -- Left block: image under `S.f` of `(b₁', (x', u'), s₁)`.
    intro i
    change _ = (S.f.f (j + 1)).hom _
    obtain ⟨m, rfl⟩ := (finCongr hn₁.symm).surjective i
    simp only [Function.comp_apply, finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq]
    have hl : Fin.cast hN (finSumFinEquiv (.inl (Fin.cast hn₁.symm m))) =
        Fin.castAdd (p₃' + g' + (a + p₃)) (Fin.cast (by omega) m) := Fin.ext (by simp)
    rw [hl, Fin.append_left]
    induction m using Fin.addCases with
    | left m =>
      have hcast : Fin.cast (by omega) (Fin.castAdd p₁ m) =
          Fin.castAdd p₁ (Fin.cast (show p₁' + m₁' = p₁' + a' + b' by omega) m) := Fin.ext rfl
      rw [hcast, Fin.append_left, Fin.append_left]
      induction m using Fin.addCases with
      | left l =>
        have hcast' : Fin.cast (by omega) (Fin.castAdd m₁' l) =
            Fin.castAdd b' (Fin.castAdd a' l) := Fin.ext rfl
        rw [hcast', Fin.append_left, Fin.append_left]
        simp only [A, Fin.append_left]
      | right r =>
        rw [Fin.append_right]
        generalize hrr' : Fin.cast hm₁' r = r'
        induction r' using Fin.addCases with
        | left l =>
          have hcast' : Fin.cast (by omega) (Fin.natAdd p₁' r) =
              Fin.castAdd b' (Fin.natAdd p₁' l) := Fin.ext (by
                have := congrArg Fin.val hrr'; simp at this ⊢; omega)
          rw [hcast', Fin.append_left]
          simp only [A, Fin.append_right, Fin.append_left]
        | right l =>
          have hcast' : Fin.cast (by omega) (Fin.natAdd p₁' r) =
              Fin.natAdd (p₁' + a') l := Fin.ext (by
                have := congrArg Fin.val hrr'; simp at this ⊢; omega)
          rw [hcast', Fin.append_right, Fin.append_right]
    | right r =>
      have hcast : Fin.cast (by omega) (Fin.natAdd (p₁' + m₁') r) =
          Fin.natAdd (p₁' + a' + b') r := Fin.ext (by simp)
      rw [hcast, Fin.append_right, Fin.append_right]
  · -- Right block: lifts under `S.g` of `(b₃', (cyclesMap g v', z₃), g ∘ t₃)`.
    intro i
    change (S.g.f (j + 1)).hom _ = _
    obtain ⟨m, rfl⟩ := (finCongr hn₃.symm).surjective i
    simp only [Function.comp_apply, finCongr_apply, Fin.cast_cast, Fin.cast_refl, id_eq]
    have hr : Fin.cast hN (finSumFinEquiv (.inr (Fin.cast hn₃.symm m))) =
        Fin.natAdd (p₁' + a' + b' + p₁) (Fin.cast (by omega) m) := Fin.ext (by simp; omega)
    rw [hr, Fin.append_right]
    induction m using Fin.addCases with
    | left m =>
      induction m using Fin.addCases with
      | left l =>
        have hcast : Fin.cast (by omega) (Fin.castAdd p₃ (Fin.castAdd m₃' l)) =
            Fin.castAdd (a + p₃) (Fin.castAdd g' l) := Fin.ext rfl
        rw [hcast, Fin.append_left, Fin.append_left, Fin.append_left, Fin.append_left]
        simp only [B, ← HomologicalComplex.Hom.comm_apply, ht₃']
      | right r =>
        rw [Fin.append_left, Fin.append_right]
        generalize hrr' : Fin.cast hm₃' r = r'
        induction r' using Fin.addCases with
        | left l =>
          have hcast : Fin.cast (by omega) (Fin.castAdd p₃ (Fin.natAdd p₃' r)) =
              Fin.castAdd (a + p₃) (Fin.natAdd p₃' l) := Fin.ext (by
                have := congrArg Fin.val hrr'; simp at this ⊢; omega)
          rw [hcast, Fin.append_left, Fin.append_right, Fin.append_left]
          calc (S.g.f (j + 1)).hom (D l)
              = (S.X₂.iCycles (j + 1) ≫ S.g.f (j + 1)).hom (v' l) := rfl
            _ = (HomologicalComplex.cyclesMap S.g (j + 1) ≫ S.X₃.iCycles (j + 1)).hom (v' l) := by
                rw [HomologicalComplex.cyclesMap_i]
            _ = (S.X₃.iCycles (j + 1)).hom
                  ((HomologicalComplex.cyclesMap S.g (j + 1)).hom (v' l)) := rfl
        | right l =>
          have hcast : Fin.cast (by omega) (Fin.castAdd p₃ (Fin.natAdd p₃' r)) =
              Fin.natAdd (p₃' + g') (Fin.castAdd p₃ l) := Fin.ext (by
                have := congrArg Fin.val hrr'; simp at this ⊢; omega)
          rw [hcast, Fin.append_right]
          simp only [G, Fin.append_left, Fin.append_right, hw_g]
    | right r =>
      have hcast : Fin.cast (by omega) (Fin.natAdd (p₃' + m₃') r) =
          Fin.natAdd (p₃' + g') (Fin.natAdd a r) := Fin.ext (by simp; omega)
      rw [hcast, Fin.append_right, Fin.append_right]
      simp only [G, Fin.append_right]

private theorem finite_setOf_homology_rank_ne_zero {C : ChainComplex (ModuleCat F) ℤ}
    {n m : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) F (C.X i))
    (h : ∀ i, Basis (Fin (m i)) F (C.homology i)) (hn : {i | n i ≠ 0}.Finite) :
    {i | m i ≠ 0}.Finite :=
  hn.subset fun i hi ↦ by
    have : Module.Finite F (C.X i) := .of_basis (c i)
    have hle := C.finrank_homology_le_finrank_X i
    rw [finrank_eq_card_basis (h i), finrank_eq_card_basis (c i), Fintype.card_fin,
      Fintype.card_fin] at hle
    simp only [Set.mem_ofPred_eq] at hi ⊢
    omega

/-- The product of alternating basis-change determinants with opposite signs `i.negOnePow` and
`(i + 1).negOnePow` is `1`. -/
private theorem finprod_det_zpow_negOnePow_mul_succ {X : ℤ → ModuleCat F} {m : ℤ → ℕ}
    (h h' : ∀ i, Basis (Fin (m i)) F (X i)) (hm : {i | m i ≠ 0}.Finite) :
    (∏ᶠ i : ℤ, (h i).det (h' i) ^ ((i + 1).negOnePow : ℤ)) *
        (∏ᶠ i : ℤ, (h i).det (h' i) ^ (i.negOnePow : ℤ)) = 1 := by
  have h1 : Function.HasFiniteMulSupport fun i : ℤ ↦
      (h i).det (h' i) ^ ((i + 1).negOnePow : ℤ) :=
    hm.subset <| Function.mulSupport_subset_iff'.2 fun i hi ↦ by
      have hm0 : m i = 0 := by simpa using hi
      have : IsEmpty (Fin (m i)) := by rw [hm0]; infer_instance
      simp
  have h2 : Function.HasFiniteMulSupport fun i : ℤ ↦ (h i).det (h' i) ^ (i.negOnePow : ℤ) :=
    hm.subset <| Function.mulSupport_subset_iff'.2 fun i hi ↦ by
      have hm0 : m i = 0 := by simpa using hi
      have : IsEmpty (Fin (m i)) := by rw [hm0]; infer_instance
      simp
  rw [← finprod_mul_distrib h1 h2]
  refine (finprod_congr fun i ↦ ?_).trans finprod_one
  rw [← zpow_add₀ (Basis.isUnit_det (h i) (h' i)).ne_zero, Int.negOnePow_succ, Units.val_neg,
    neg_add_cancel, zpow_zero]

private theorem reidemeisterTorsionWithHomology_mul_eq_zero_of_not_finite {n₁ n₃ m₁ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (hn : ¬{i | n₁ i + n₃ i ≠ 0}.Finite) :
    S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
      S.X₃.reidemeisterTorsionWithHomology c₃ h₃ = 0 := by
  by_cases hn₁ : {i | n₁ i ≠ 0}.Finite
  · have hn₃ : ¬{i | n₃ i ≠ 0}.Finite := fun hn₃ ↦
      hn ((hn₁.union hn₃).subset fun i hi ↦ by
        simp only [Set.mem_union, Set.mem_ofPred_eq] at hi ⊢; omega)
    rw [S.X₃.reidemeisterTorsionWithHomology_of_not_finite c₃ h₃ hn₃, mul_zero]
  · rw [S.X₁.reidemeisterTorsionWithHomology_of_not_finite c₁ h₁ hn₁, zero_mul]

/-- Multiplicativity of torsion with homology bases for bounded complexes equipped with adapted
homology bases `(h₁', h₂', h₃')` built from bases `(α, β, γ)` of the images of `(δ, f_*, g_*)`. -/
private theorem reidemeisterTorsionWithHomology_eq_mul_of_adapted {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (hn : {i | n₁ i + n₃ i ≠ 0}.Finite)
    {a b g' : ℤ → ℕ}
    (α : ∀ i, Basis (Fin (a i)) F (LinearMap.range (hS.δ (i + 1) i rfl).hom))
    (β : ∀ i, Basis (Fin (b i)) F (LinearMap.range (HomologicalComplex.homologyMap S.f i).hom))
    (γ : ∀ i, Basis (Fin (g' i)) F (LinearMap.range (HomologicalComplex.homologyMap S.g i).hom))
    (sα : ∀ i, Fin (a i) → S.X₃.homology (i + 1))
    (hsα : ∀ i k, (hS.δ (i + 1) i rfl).hom (sα i k) = α i k)
    (sβ : ∀ i, Fin (b i) → S.X₁.homology i)
    (hsβ : ∀ i k, (HomologicalComplex.homologyMap S.f i).hom (sβ i k) = β i k)
    (sγ : ∀ i, Fin (g' i) → S.X₂.homology i)
    (hsγ : ∀ i k, (HomologicalComplex.homologyMap S.g i).hom (sγ i k) = γ i k)
    (h₁' : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i)) (hm₁ : ∀ i, m₁ i = a i + b i)
    (hh₁' : ∀ i, ⇑(h₁' i) = Fin.append (fun k ↦ (α i k : S.X₁.homology i)) (sβ i) ∘
      Fin.cast (hm₁ i))
    (h₂' : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i)) (hm₂ : ∀ i, m₂ i = b i + g' i)
    (hh₂' : ∀ i, ⇑(h₂' i) = Fin.append (fun k ↦ (β i k : S.X₂.homology i)) (sγ i) ∘
      Fin.cast (hm₂ i))
    (h₃' : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) (hm₃ : ∀ j, m₃ (j + 1) = g' (j + 1) + a j)
    (hh₃' : ∀ j, ⇑(h₃' (j + 1)) =
      Fin.append (fun k ↦ (γ (j + 1) k : S.X₃.homology (j + 1))) (sα j) ∘ Fin.cast (hm₃ j)) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂' =
      (∏ᶠ j : ℤ, (-1 : F) ^ (
        finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) * b (j + 1) +
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + g' (j + 1)) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁' *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃') := by
  have hn₁ : {i | n₁ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hn₃ : {i | n₃ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hS' := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  have hg (i : ℤ) : Function.Surjective (S.g.f i).hom := (hS' i).moduleCat_surjective_g
  let b₁ (j : ℤ) := HomologicalComplex.chosenBoundaryBasis S.X₁ c₁ (j + 1) j
  let s₁ (j : ℤ) := HomologicalComplex.chosenBoundaryLift S.X₁ c₁ (j + 1) j
  have hs₁ (j : ℤ) := HomologicalComplex.chosenBoundaryLift_spec S.X₁ c₁ (j + 1) j
  let b₃ (j : ℤ) := HomologicalComplex.chosenBoundaryBasis S.X₃ c₃ (j + 1) j
  let t₃ (j : ℤ) (k : Fin (finrank F (LinearMap.range (S.X₃.d (j + 1) j).hom))) : S.X₂.X (j + 1) :=
    Function.surjInv (hg (j + 1)) (HomologicalComplex.chosenBoundaryLift S.X₃ c₃ (j + 1) j k)
  have ht₃ (j : ℤ) (k) : (S.X₃.d (j + 1) j).hom ((S.g.f (j + 1)).hom (t₃ j k)) = b₃ j k := by
    rw [Function.surjInv_eq (hg (j + 1)), HomologicalComplex.chosenBoundaryLift_spec]
  let x (j : ℤ) (k : Fin (a j)) : S.X₁.cycles j :=
    Function.surjInv (S.X₁.moduleCat_homologyπ_surjective j) (α j k)
  have hx (j : ℤ) (k : Fin (a j)) : (S.X₁.homologyπ j).hom (x j k) = α j k :=
    Function.surjInv_eq (S.X₁.moduleCat_homologyπ_surjective j) _
  let u (i : ℤ) (k : Fin (b i)) : S.X₁.cycles i :=
    Function.surjInv (S.X₁.moduleCat_homologyπ_surjective i) (sβ i k)
  have hu (i : ℤ) (k : Fin (b i)) : (S.X₁.homologyπ i).hom (u i k) = sβ i k :=
    Function.surjInv_eq (S.X₁.moduleCat_homologyπ_surjective i) _
  let v (i : ℤ) (k : Fin (g' i)) : S.X₂.cycles i :=
    Function.surjInv (S.X₂.moduleCat_homologyπ_surjective i) (sγ i k)
  have hv (i : ℤ) (k : Fin (g' i)) : (S.X₂.homologyπ i).hom (v i k) = sγ i k :=
    Function.surjInv_eq (S.X₂.moduleCat_homologyπ_surjective i) _
  have hwz (j : ℤ) (k : Fin (a j)) :=
    hS.moduleCat_exists_d_eq_of_δ_eq (j + 1) j rfl (sα j k) (x j k) (by rw [hsα, hx])
  let w (j : ℤ) (k : Fin (a j)) : S.X₂.X (j + 1) := Classical.choose (hwz j k)
  let z₃ (j : ℤ) (k : Fin (a j)) : S.X₃.cycles (j + 1) :=
    Classical.choose (Classical.choose_spec (hwz j k))
  have hw_d (j : ℤ) (k : Fin (a j)) :
      (S.X₂.d (j + 1) j).hom (w j k) = (S.f.f j).hom ((S.X₁.iCycles j).hom (x j k)) :=
    (Classical.choose_spec (Classical.choose_spec (hwz j k))).1
  have hw_g (j : ℤ) (k : Fin (a j)) :
      (S.g.f (j + 1)).hom (w j k) = (S.X₃.iCycles (j + 1)).hom (z₃ j k) :=
    (Classical.choose_spec (Classical.choose_spec (hwz j k))).2.1
  have hz₃ (j : ℤ) (k : Fin (a j)) : (S.X₃.homologyπ (j + 1)).hom (z₃ j k) = sα j k :=
    (Classical.choose_spec (Classical.choose_spec (hwz j k))).2.2
  let y₁ (i : ℤ) : Fin (m₁ i) → S.X₁.cycles i := Fin.append (x i) (u i) ∘ Fin.cast (hm₁ i)
  have hy₁ (i : ℤ) (k : Fin (m₁ i)) : (S.X₁.homologyπ i).hom (y₁ i k) = h₁' i k := by
    rw [congrFun (hh₁' i) k]
    simp only [y₁, Function.comp_apply]
    generalize Fin.cast (hm₁ i) k = l
    induction l using Fin.addCases <;> simp [hx, hu]
  let y₂ (i : ℤ) : Fin (m₂ i) → S.X₂.cycles i :=
    Fin.append (fun l ↦ (HomologicalComplex.cyclesMap S.f i).hom (u i l)) (v i) ∘ Fin.cast (hm₂ i)
  have hy₂ (i : ℤ) (k : Fin (m₂ i)) : (S.X₂.homologyπ i).hom (y₂ i k) = h₂' i k := by
    rw [congrFun (hh₂' i) k]
    simp only [y₂, Function.comp_apply]
    generalize Fin.cast (hm₂ i) k = l
    induction l using Fin.addCases with
    | left l =>
      rw [Fin.append_left, Fin.append_left]
      calc (S.X₂.homologyπ i).hom ((HomologicalComplex.cyclesMap S.f i).hom (u i l))
          = (HomologicalComplex.cyclesMap S.f i ≫ S.X₂.homologyπ i).hom (u i l) := rfl
        _ = (S.X₁.homologyπ i ≫ HomologicalComplex.homologyMap S.f i).hom (u i l) := by
            rw [HomologicalComplex.homologyπ_naturality]
        _ = (HomologicalComplex.homologyMap S.f i).hom ((S.X₁.homologyπ i).hom (u i l)) := rfl
        _ = β i l := by rw [hu, hsβ]
    | right l =>
      simp [hv]
  let y₃Succ (j : ℤ) : Fin (m₃ (j + 1)) → S.X₃.cycles (j + 1) :=
    Fin.append (fun l ↦ (HomologicalComplex.cyclesMap S.g (j + 1)).hom (v (j + 1) l)) (z₃ j) ∘
      Fin.cast (hm₃ j)
  have hy₃Succ (j : ℤ) (k : Fin (m₃ (j + 1))) :
      (S.X₃.homologyπ (j + 1)).hom (y₃Succ j k) = h₃' (j + 1) k := by
    rw [congrFun (hh₃' j) k]
    simp only [y₃Succ, Function.comp_apply]
    generalize Fin.cast (hm₃ j) k = l
    induction l using Fin.addCases with
    | left l =>
      rw [Fin.append_left, Fin.append_left]
      calc (S.X₃.homologyπ (j + 1)).hom
              ((HomologicalComplex.cyclesMap S.g (j + 1)).hom (v (j + 1) l))
          = (HomologicalComplex.cyclesMap S.g (j + 1) ≫ S.X₃.homologyπ (j + 1)).hom
              (v (j + 1) l) := rfl
        _ = (S.X₂.homologyπ (j + 1) ≫ HomologicalComplex.homologyMap S.g (j + 1)).hom
              (v (j + 1) l) := by
            rw [HomologicalComplex.homologyπ_naturality]
        _ = (HomologicalComplex.homologyMap S.g (j + 1)).hom
              ((S.X₂.homologyπ (j + 1)).hom (v (j + 1) l)) := rfl
        _ = γ (j + 1) l := by rw [hv, hsγ]
    | right l =>
      simp [hz₃]
  let y₃ (i : ℤ) : Fin (m₃ i) → S.X₃.cycles i := fun k ↦
    (eqToIso (congrArg (fun k ↦ S.X₃.cycles k) (sub_add_cancel i 1)) :
      S.X₃.cycles (i - 1 + 1) ≅ S.X₃.cycles i).hom.hom
      (y₃Succ (i - 1) (Fin.cast (by rw [sub_add_cancel]) k))
  have hy₃_succ (j : ℤ) : y₃ (j + 1) = y₃Succ j := by
    have hgen : ∀ (d : ℤ) (hd : d + 1 = j + 1) (hm : m₃ (j + 1) = m₃ (d + 1)), d = j →
        (fun k ↦ (eqToIso (congrArg (fun k ↦ S.X₃.cycles k) hd) :
          S.X₃.cycles (d + 1) ≅ S.X₃.cycles (j + 1)).hom.hom
          (y₃Succ d (Fin.cast hm k))) = y₃Succ j := by
      rintro _ hd hm rfl
      ext k
      simp
    exact hgen (j + 1 - 1) (sub_add_cancel (j + 1) 1) _ (add_sub_cancel_right j 1)
  have hy₃ (i : ℤ) (k : Fin (m₃ i)) : (S.X₃.homologyπ i).hom (y₃ i k) = h₃' i k := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, (sub_add_cancel i 1).symm⟩
    rw [hy₃_succ]
    exact hy₃Succ j k
  let B₂ (j : ℤ) := shortExactBoundaryBasisWithHomology hS (b₁ j) (α j) (x j) (hx j) (b₃ j)
    (t₃ j) (ht₃ j)
  let s₂ (j : ℤ) := Fin.append (Fin.append (fun l ↦ (S.f.f (j + 1)).hom (s₁ j l)) (w j)) (t₃ j)
  have hs₂ (j : ℤ) (k) : (S.X₂.d (j + 1) j).hom (s₂ j k) = B₂ j k := by
    rw [congrFun (coe_shortExactBoundaryBasisWithHomology hS (b₁ j) (α j) (x j) (hx j) (b₃ j)
      (t₃ j) (ht₃ j)) k]
    induction k using Fin.addCases with
    | left l =>
      induction l using Fin.addCases with
      | left l =>
        simp only [s₂, Fin.append_left]
        rw [show (S.X₂.d (j + 1) j).hom ((S.f.f (j + 1)).hom (s₁ j l)) =
            (S.f.f j).hom ((S.X₁.d (j + 1) j).hom (s₁ j l)) from
          HomologicalComplex.Hom.comm_apply S.f (j + 1) j (s₁ j l), hs₁]
      | right l => simp [s₂, hw_d]
    | right l => simp [s₂]
  have hτ₁' : Function.HasFiniteMulSupport fun j : ℤ ↦
      HomologicalComplex.torsionBracketWithHomology c₁ (b₁ (j + 1)) (h₁' (j + 1)) (y₁ (j + 1))
        (hy₁ (j + 1)) (b₁ j) (s₁ j) (hs₁ j) ^ (j.negOnePow : ℤ) :=
    (hn₁.preimage (add_left_injective (1 : ℤ)).injOn).subset <|
      Function.mulSupport_subset_iff'.2 fun j hj ↦ by
        rw [HomologicalComplex.torsionBracketWithHomology_eq_one c₁ _ _ _ _ _ _ _
          (by simpa using hj), one_zpow]
  have hτ₃' : Function.HasFiniteMulSupport fun j : ℤ ↦
      HomologicalComplex.torsionBracketWithHomology c₃ (b₃ (j + 1)) (h₃' (j + 1)) (y₃ (j + 1))
        (hy₃ (j + 1)) (b₃ j) (fun l ↦ (S.g.f (j + 1)).hom (t₃ j l)) (ht₃ j) ^ (j.negOnePow : ℤ) :=
    (hn₃.preimage (add_left_injective (1 : ℤ)).injOn).subset <|
      Function.mulSupport_subset_iff'.2 fun j hj ↦ by
        rw [HomologicalComplex.torsionBracketWithHomology_eq_one c₃ _ _ _ _ _ _ _
          (by simpa using hj), one_zpow]
  have hε : Function.HasFiniteMulSupport fun j : ℤ ↦ (-1 : F) ^ (
      finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) * b (j + 1) +
      (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) + g' (j + 1)) *
        finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom)) :=
    ((hn₃.preimage (add_left_injective (1 : ℤ)).injOn).union hn₁).subset <|
      Function.mulSupport_subset_iff'.2 fun j hj ↦ by
        simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, not_or, not_not] at hj
        simp [HomologicalComplex.finrank_range_d_eq_zero S.X₃ c₃ hj.1,
          HomologicalComplex.finrank_range_d_eq_zero S.X₁ c₁ hj.2]
  rw [HomologicalComplex.reidemeisterTorsionWithHomology_eq_finprod hn B₂ y₂ hy₂ s₂ hs₂,
    HomologicalComplex.reidemeisterTorsionWithHomology_eq_finprod hn₁ b₁ y₁ hy₁ s₁ hs₁,
    HomologicalComplex.reidemeisterTorsionWithHomology_eq_finprod hn₃ b₃ y₃ hy₃
      (fun j l ↦ (S.g.f (j + 1)).hom (t₃ j l)) ht₃,
    ← finprod_mul_distrib hτ₁' hτ₃',
    ← finprod_mul_distrib hε ((hτ₁'.union hτ₃').subset (Function.mulSupport_mul _ _))]
  refine finprod_congr fun j ↦ ?_
  have hbr := hS.torsionBracketWithHomology_shortExactBoundaryBasis c₁ c₃ c₂ hc₁ hc₃
    (b₁ (j + 1)) (α (j + 1)) (x (j + 1)) (hx (j + 1)) (b₃ (j + 1)) (t₃ (j + 1)) (ht₃ (j + 1))
    (u (j + 1)) (v (j + 1)) (b₁ j) (s₁ j) (hs₁ j) (α j) (x j) (hx j) (w j) (z₃ j)
    (hw_g j) (b₃ j) (t₃ j) (ht₃ j) (h₁' (j + 1)) (hm₁ (j + 1)) (hy₁ (j + 1))
    (h₂' (j + 1)) (hm₂ (j + 1)) (hy₂ (j + 1)) (h₃' (j + 1)) (hm₃ j) (hy₃Succ j) (hs₂ j)
  have hbr' : HomologicalComplex.torsionBracketWithHomology c₃ (b₃ (j + 1)) (h₃' (j + 1))
      (y₃ (j + 1)) (hy₃ (j + 1)) (b₃ j) (fun l ↦ (S.g.f (j + 1)).hom (t₃ j l)) (ht₃ j) =
      HomologicalComplex.torsionBracketWithHomology c₃ (b₃ (j + 1)) (h₃' (j + 1))
        (y₃Succ j) (hy₃Succ j) (b₃ j) (fun l ↦ (S.g.f (j + 1)).hom (t₃ j l)) (ht₃ j) := by
    congr 1
    exact hy₃_succ j
  rw [hbr', hbr, mul_zpow, mul_zpow]
  congr 1
  rcases Int.units_eq_one_or j.negOnePow with hj | hj <;> simp [hj, ← inv_pow]

/-- **Multiplicativity of torsion with homology bases (Milnor's theorem).** Let
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of `ℤ`-graded chain complexes of vector
spaces over a field `F`, with compatible chain bases `(c₁, c₂, c₃)` (each `c₂ i` is the image of
`c₁ i` followed by lifts of `c₃ i`) and arbitrary homology bases `(h₁, h₂, h₃)`. Then

`τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃) · τ(H)`,

where `H = hS.homologySequenceComplex` is the long exact homology sequence based by `(h₁, h₂, h₃)`
and `ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim im(f_*)_{j+1} + (dim B₃,ⱼ₊₁ + dim im(g_*)_{j+1}) · dim B₁,ⱼ)`.
This holds unconditionally, both sides being `0` when the complexes are unbounded. -/
theorem reidemeisterTorsionWithHomology_eq_mul {n₁ n₃ m₁ m₂ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i)) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^ (
        finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
          finrank F (LinearMap.range (HomologicalComplex.homologyMap S.f (j + 1)).hom) +
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) +
          finrank F (LinearMap.range (HomologicalComplex.homologyMap S.g (j + 1)).hom)) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃ *
        hS.homologySequenceComplex.reidemeisterTorsion
          (ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃)) := by
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · rw [S.X₂.reidemeisterTorsionWithHomology_of_not_finite c₂ h₂ hn,
      reidemeisterTorsionWithHomology_mul_eq_zero_of_not_finite c₁ c₃ h₁ h₃ hn,
      zero_mul, mul_zero]
  have hn₁ : {i | n₁ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hn₃ : {i | n₃ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hm₁_fin := finite_setOf_homology_rank_ne_zero c₁ h₁ hn₁
  have hm₂_fin := finite_setOf_homology_rank_ne_zero c₂ h₂ hn
  have hm₃_fin := finite_setOf_homology_rank_ne_zero c₃ h₃ hn₃
  -- Choose bases of the images of `δ`, `f_*` and `g_*` and build adapted homology bases
  -- `(h₁', h₂', h₃')` for which the based long exact homology sequence has torsion `1`.
  have (i : ℤ) : Module.Finite F (S.X₁.homology i) := .of_basis (h₁ i)
  have (i : ℤ) : Module.Finite F (S.X₂.homology i) := .of_basis (h₂ i)
  have (i : ℤ) : Module.Finite F (S.X₃.homology i) := .of_basis (h₃ i)
  let a (i : ℤ) := finrank F (LinearMap.range (hS.δ (i + 1) i rfl).hom)
  let b (i : ℤ) := finrank F (LinearMap.range (HomologicalComplex.homologyMap S.f i).hom)
  let g' (i : ℤ) := finrank F (LinearMap.range (HomologicalComplex.homologyMap S.g i).hom)
  let α (i : ℤ) : Basis (Fin (a i)) F (LinearMap.range (hS.δ (i + 1) i rfl).hom) :=
    Module.finBasis F _
  let β (i : ℤ) :
      Basis (Fin (b i)) F (LinearMap.range (HomologicalComplex.homologyMap S.f i).hom) :=
    Module.finBasis F _
  let γ (i : ℤ) :
      Basis (Fin (g' i)) F (LinearMap.range (HomologicalComplex.homologyMap S.g i).hom) :=
    Module.finBasis F _
  let sα (i : ℤ) (k : Fin (a i)) : S.X₃.homology (i + 1) := Classical.choose (α i k).2
  have hsα (i : ℤ) (k : Fin (a i)) : (hS.δ (i + 1) i rfl).hom (sα i k) = α i k :=
    Classical.choose_spec (α i k).2
  let sβ (i : ℤ) (k : Fin (b i)) : S.X₁.homology i := Classical.choose (β i k).2
  have hsβ (i : ℤ) (k : Fin (b i)) : (HomologicalComplex.homologyMap S.f i).hom (sβ i k) = β i k :=
    Classical.choose_spec (β i k).2
  let sγ (i : ℤ) (k : Fin (g' i)) : S.X₂.homology i := Classical.choose (γ i k).2
  have hsγ (i : ℤ) (k : Fin (g' i)) : (HomologicalComplex.homologyMap S.g i).hom (sγ i k) = γ i k :=
    Classical.choose_spec (γ i k).2
  have hex₁ (i : ℤ) : Function.Exact (LinearMap.range (hS.δ (i + 1) i rfl).hom).subtype
      (HomologicalComplex.homologyMap S.f i).hom.rangeRestrict :=
    LinearMap.exact_iff.2 <| by
      rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype, ← LinearMap.exact_iff]
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (hS.homology_exact₁ (i + 1) i rfl)
  have hex₂ (i : ℤ) : Function.Exact
      (LinearMap.range (HomologicalComplex.homologyMap S.f i).hom).subtype
      (HomologicalComplex.homologyMap S.g i).hom.rangeRestrict :=
    LinearMap.exact_iff.2 <| by
      rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype, ← LinearMap.exact_iff]
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hS.homology_exact₂ i)
  have hex₃ (j : ℤ) : Function.Exact
      (LinearMap.range (HomologicalComplex.homologyMap S.g (j + 1)).hom).subtype
      (hS.δ (j + 1) j rfl).hom.rangeRestrict :=
    LinearMap.exact_iff.2 <| by
      rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype, ← LinearMap.exact_iff]
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (hS.homology_exact₃ (j + 1) j rfl)
  let h₁Raw (i : ℤ) : Basis (Fin (a i + b i)) F (S.X₁.homology i) :=
    (Basis.ofExactLift (Submodule.injective_subtype _) (hex₁ i) (α i) (β i) (sβ i)
      fun k ↦ Subtype.ext (hsβ i k)).reindex finSumFinEquiv
  let h₂Raw (i : ℤ) : Basis (Fin (b i + g' i)) F (S.X₂.homology i) :=
    (Basis.ofExactLift (Submodule.injective_subtype _) (hex₂ i) (β i) (γ i) (sγ i)
      fun k ↦ Subtype.ext (hsγ i k)).reindex finSumFinEquiv
  let h₃RawSucc (j : ℤ) : Basis (Fin (g' (j + 1) + a j)) F (S.X₃.homology (j + 1)) :=
    (Basis.ofExactLift (Submodule.injective_subtype _) (hex₃ j) (γ (j + 1)) (α j) (sα j)
      fun k ↦ Subtype.ext (hsα j k)).reindex finSumFinEquiv
  have hm₁ (i : ℤ) : m₁ i = a i + b i := by
    simpa using Fintype.card_congr ((h₁ i).indexEquiv (h₁Raw i))
  have hm₂ (i : ℤ) : m₂ i = b i + g' i := by
    simpa using Fintype.card_congr ((h₂ i).indexEquiv (h₂Raw i))
  have hm₃ (j : ℤ) : m₃ (j + 1) = g' (j + 1) + a j := by
    simpa using Fintype.card_congr ((h₃ (j + 1)).indexEquiv (h₃RawSucc j))
  let h₁' (i : ℤ) : Basis (Fin (m₁ i)) F (S.X₁.homology i) :=
    (h₁Raw i).reindex (finCongr (hm₁ i).symm)
  let h₂' (i : ℤ) : Basis (Fin (m₂ i)) F (S.X₂.homology i) :=
    (h₂Raw i).reindex (finCongr (hm₂ i).symm)
  let h₃' (i : ℤ) : Basis (Fin (m₃ i)) F (S.X₃.homology i) :=
    ((h₃RawSucc (i - 1)).map
      (eqToIso (congrArg (fun k ↦ S.X₃.homology k) (sub_add_cancel i 1)) :
        S.X₃.homology (i - 1 + 1) ≅ S.X₃.homology i).toLinearEquiv).reindex
        (finCongr (by rw [← hm₃ (i - 1), sub_add_cancel]))
  have hh₃'_eq (j : ℤ) : h₃' (j + 1) = (h₃RawSucc j).reindex (finCongr (hm₃ j).symm) := by
    have hgen : ∀ (d : ℤ) (hd : d + 1 = j + 1) (hm : g' (d + 1) + a d = m₃ (j + 1)), d = j →
        ((h₃RawSucc d).map (eqToIso (congrArg (fun k ↦ S.X₃.homology k) hd) :
          S.X₃.homology (d + 1) ≅ S.X₃.homology (j + 1)).toLinearEquiv).reindex
          (finCongr hm) = (h₃RawSucc j).reindex (finCongr (hm₃ j).symm) := by
      rintro _ hd hm rfl
      ext k
      simp
    exact hgen (j + 1 - 1) (sub_add_cancel (j + 1) 1) _ (add_sub_cancel_right j 1)
  have hh₁' (i : ℤ) : ⇑(h₁' i) = Fin.append (fun k ↦ (α i k : S.X₁.homology i)) (sβ i) ∘
      Fin.cast (hm₁ i) := by
    ext k
    simp only [h₁', Basis.reindex_apply, finCongr_symm, finCongr_apply, Function.comp_apply]
    exact congrFun (Basis.coe_reindex_ofExactLift _ _ (α i) (β i) (sβ i) _) (Fin.cast (hm₁ i) k)
  have hh₂' (i : ℤ) : ⇑(h₂' i) = Fin.append (fun k ↦ (β i k : S.X₂.homology i)) (sγ i) ∘
      Fin.cast (hm₂ i) := by
    ext k
    simp only [h₂', Basis.reindex_apply, finCongr_symm, finCongr_apply, Function.comp_apply]
    exact congrFun (Basis.coe_reindex_ofExactLift _ _ (β i) (γ i) (sγ i) _) (Fin.cast (hm₂ i) k)
  have hh₃' (j : ℤ) : ⇑(h₃' (j + 1)) =
      Fin.append (fun k ↦ (γ (j + 1) k : S.X₃.homology (j + 1))) (sα j) ∘ Fin.cast (hm₃ j) := by
    rw [hh₃'_eq]
    ext k
    simp only [Basis.reindex_apply, finCongr_symm, finCongr_apply, Function.comp_apply]
    exact congrFun (Basis.coe_reindex_ofExactLift _ _ (γ (j + 1)) (α j) (sα j) _)
      (Fin.cast (hm₃ j) k)
  have hτH' : hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ h₁' h₂' h₃') = 1 :=
    ChainComplex.interleave.reidemeisterTorsion_basis_eq_one _ _ _ h₁' h₂' h₃'
      hm₁_fin hm₂_fin hm₃_fin α β γ sα hsα sβ hsβ sγ hsγ hm₁ hh₁' hm₂ hh₂' hm₃ hh₃'
  have h_adapted := hS.reidemeisterTorsionWithHomology_eq_mul_of_adapted c₁ c₃ c₂ hc₁ hc₃ hn
    α β γ sα hsα sβ hsβ sγ hsγ h₁' hm₁ hh₁' h₂' hm₂ hh₂' h₃' hm₃ hh₃'
  -- Pass from the adapted homology bases `(h₁', h₂', h₃')` to `(h₁, h₂, h₃)`.
  rw [HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology
      (c := c₁) (h := h₁') h₁,
    HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology
      (c := c₂) (h := h₂') h₂,
    HomologicalComplex.reidemeisterTorsionWithHomology_eq_mul_finprod_det_homology
      (c := c₃) (h := h₃') h₃,
    ChainComplex.interleave.reidemeisterTorsion_basis_eq_mul _ _ _ h₁' h₁ h₂' h₂ h₃' h₃,
    hτH', h_adapted]
  have hD₁ := finprod_det_zpow_negOnePow_mul_succ h₁' h₁ hm₁_fin
  have hD₃ := finprod_det_zpow_negOnePow_mul_succ h₃' h₃ hm₃_fin
  calc _ = _ * ((∏ᶠ i : ℤ, (h₁' i).det (h₁ i) ^ ((i + 1).negOnePow : ℤ)) *
            (∏ᶠ i : ℤ, (h₁' i).det (h₁ i) ^ (i.negOnePow : ℤ))) *
          ((∏ᶠ i : ℤ, (h₃' i).det (h₃ i) ^ ((i + 1).negOnePow : ℤ)) *
            (∏ᶠ i : ℤ, (h₃' i).det (h₃ i) ^ (i.negOnePow : ℤ))) := by
        rw [hD₁, hD₃, mul_one, mul_one]
    _ = _ := by ring

end Multiplicativity

section VanishingConnecting

private theorem homologyMap_f_injective_of_δ_eq_zero
    (hδ : ∀ i : ℤ, hS.δ (i + 1) i rfl = 0) (i : ℤ) :
    Function.Injective (HomologicalComplex.homologyMap S.f i).hom := by
  have hex : LinearMap.ker (HomologicalComplex.homologyMap S.f i).hom =
      LinearMap.range (hS.δ (i + 1) i rfl).hom :=
    LinearMap.exact_iff.1 ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₁ (i + 1) i rfl))
  rw [← LinearMap.ker_eq_bot, hex, hδ i, ModuleCat.hom_zero, LinearMap.range_zero]

private theorem homologyMap_g_surjective_of_δ_eq_zero
    (hδ : ∀ i : ℤ, hS.δ (i + 1) i rfl = 0) (i : ℤ) :
    Function.Surjective (HomologicalComplex.homologyMap S.g i).hom := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, (sub_add_cancel i 1).symm⟩
  have hex : LinearMap.ker (hS.δ (j + 1) j rfl).hom =
      LinearMap.range (HomologicalComplex.homologyMap S.g (j + 1)).hom :=
    LinearMap.exact_iff.1 ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hS.homology_exact₃ (j + 1) j rfl))
  rw [← LinearMap.range_eq_top, ← hex, hδ j, ModuleCat.hom_zero, LinearMap.ker_zero]

/-- When all connecting homomorphisms of a short exact sequence of chain complexes vanish, the
long exact homology sequence splits into short exact sequences; for compatible homology bases
(each `h₂ i` is the image of `h₁ i` followed by lifts of `h₃ i`) with finite support, its
Reidemeister torsion is `1`. -/
theorem reidemeisterTorsion_homologySequenceComplex_eq_one
    (hδ : ∀ i : ℤ, hS.δ (i + 1) i rfl = 0) {m₁ m₃ : ℤ → ℕ}
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (h₂ : ∀ i, Basis (Fin (m₁ i + m₃ i)) F (S.X₂.homology i))
    (hh₁ : ∀ i k, h₂ i (Fin.castAdd (m₃ i) k) =
      (HomologicalComplex.homologyMap S.f i).hom (h₁ i k))
    (hh₃ : ∀ i k, (HomologicalComplex.homologyMap S.g i).hom
      (h₂ i (Fin.natAdd (m₁ i) k)) = h₃ i k)
    (hm₁ : {i | m₁ i ≠ 0}.Finite) (hm₃ : {i | m₃ i ≠ 0}.Finite) :
    hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ h₁ h₂ h₃) = 1 := by
  have hm₂ : {i | m₁ i + m₃ i ≠ 0}.Finite :=
    (hm₁.union hm₃).subset fun i hi ↦ by
      simp only [Set.mem_union, Set.mem_ofPred_eq] at hi ⊢; omega
  have hfinj := hS.homologyMap_f_injective_of_δ_eq_zero hδ
  have hgsurj := hS.homologyMap_g_surjective_of_δ_eq_zero hδ
  let α (i : ℤ) : Basis (Fin 0) F (LinearMap.range (hS.δ (i + 1) i rfl).hom) :=
    Basis.mk (v := Fin.elim0) linearIndependent_empty_type <| by
      rintro ⟨y, hy⟩ _
      rw [hδ i, ModuleCat.hom_zero, LinearMap.range_zero, Submodule.mem_bot] at hy
      subst hy
      exact zero_mem _
  let β (i : ℤ) :
      Basis (Fin (m₁ i)) F (LinearMap.range (HomologicalComplex.homologyMap S.f i).hom) :=
    (h₁ i).map (LinearEquiv.ofInjective _ (hfinj i))
  let γ (i : ℤ) :
      Basis (Fin (m₃ i)) F (LinearMap.range (HomologicalComplex.homologyMap S.g i).hom) :=
    (h₃ i).map (Submodule.topEquiv.symm.trans
      (LinearEquiv.ofEq ⊤ _ (LinearMap.range_eq_top.2 (hgsurj i)).symm))
  refine ChainComplex.interleave.reidemeisterTorsion_basis_eq_one _ _ _ h₁ h₂ h₃
    hm₁ hm₂ hm₃ α β γ (fun _ ↦ Fin.elim0) (fun _ k ↦ Fin.elim0 k) (fun i k ↦ h₁ i k)
    (fun i k ↦ by simp [β]) (fun i k ↦ h₂ i (Fin.natAdd (m₁ i) k))
    (fun i k ↦ by simp [γ, hh₃]) (fun i ↦ (Nat.zero_add _).symm)
    (fun i ↦ by ext k; simp [Fin.append_left_nil _ _ rfl])
    (fun _ ↦ rfl) (fun i ↦ by
      ext k
      induction k using Fin.addCases <;> simp [β, hh₁])
    (fun _ ↦ rfl) (fun j ↦ by ext k; simp [γ, Fin.append_right_nil _ _ rfl])

/-- Multiplicativity of torsion with homology bases when the connecting homomorphisms vanish:
with compatible chain bases `(c₁, c₂, c₃)` and compatible homology bases `(h₁, h₂, h₃)`, the
torsion of the long exact homology sequence is `1`, and

`τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃)`,

where `ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim H₁,ⱼ₊₁ + (dim B₃,ⱼ₊₁ + dim H₃,ⱼ₊₁) · dim B₁,ⱼ)`.
This holds unconditionally, both sides being `0` when the complexes are unbounded. -/
theorem reidemeisterTorsionWithHomology_eq_mul_of_δ_eq_zero
    (hδ : ∀ i : ℤ, hS.δ (i + 1) i rfl = 0) {n₁ n₃ m₁ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (h₂ : ∀ i, Basis (Fin (m₁ i + m₃ i)) F (S.X₂.homology i))
    (hh₁ : ∀ i k, h₂ i (Fin.castAdd (m₃ i) k) =
      (HomologicalComplex.homologyMap S.f i).hom (h₁ i k))
    (hh₃ : ∀ i k, (HomologicalComplex.homologyMap S.g i).hom
      (h₂ i (Fin.natAdd (m₁ i) k)) = h₃ i k) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^ (
        finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
          finrank F (S.X₁.homology (j + 1)) +
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) +
          finrank F (S.X₃.homology (j + 1))) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃) := by
  by_cases hn : {i | n₁ i + n₃ i ≠ 0}.Finite
  swap
  · rw [S.X₂.reidemeisterTorsionWithHomology_of_not_finite c₂ h₂ hn,
      reidemeisterTorsionWithHomology_mul_eq_zero_of_not_finite c₁ c₃ h₁ h₃ hn, mul_zero]
  have hn₁ : {i | n₁ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hn₃ : {i | n₃ i ≠ 0}.Finite :=
    hn.subset fun i hi ↦ by simp only [Set.mem_ofPred_eq] at hi ⊢; omega
  have hm₁ := finite_setOf_homology_rank_ne_zero c₁ h₁ hn₁
  have hm₃ := finite_setOf_homology_rank_ne_zero c₃ h₃ hn₃
  rw [hS.reidemeisterTorsionWithHomology_eq_mul c₁ c₃ c₂ hc₁ hc₃ h₁ h₂ h₃,
    hS.reidemeisterTorsion_homologySequenceComplex_eq_one hδ h₁ h₃ h₂ hh₁ hh₃ hm₁ hm₃, mul_one]
  congr 1
  refine finprod_congr fun j ↦ ?_
  rw [LinearMap.finrank_range_of_inj (hS.homologyMap_f_injective_of_δ_eq_zero hδ (j + 1)),
    LinearMap.range_eq_top.2 (hS.homologyMap_g_surjective_of_δ_eq_zero hδ (j + 1)), finrank_top]

end VanishingConnecting

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.ShortComplex.Splitting

variable {F : Type*} [Field F] {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}

/-- **Torsion with homology bases of a split short exact sequence.** Let
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a split short exact sequence of `ℤ`-graded chain complexes of
vector spaces over a field `F`, with compatible chain bases `(c₁, c₂, c₃)` and compatible homology
bases `(h₁, h₂, h₃)`. Then `τ(S.X₂, c₂, h₂) = ε · τ(S.X₁, c₁, h₁) · τ(S.X₃, c₃, h₃)`, where
`ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim H₁,ⱼ₊₁ + (dim B₃,ⱼ₊₁ + dim H₃,ⱼ₊₁) · dim B₁,ⱼ)`. -/
theorem reidemeisterTorsionWithHomology_eq_mul (σ : S.Splitting) {n₁ n₃ m₁ m₃ : ℤ → ℕ}
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (S.X₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (S.X₃.X i))
    (c₂ : ∀ i, Basis (Fin (n₁ i + n₃ i)) F (S.X₂.X i))
    (hc₁ : ∀ i k, c₂ i (Fin.castAdd (n₃ i) k) = (S.f.f i).hom (c₁ i k))
    (hc₃ : ∀ i k, (S.g.f i).hom (c₂ i (Fin.natAdd (n₁ i) k)) = c₃ i k)
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))
    (h₂ : ∀ i, Basis (Fin (m₁ i + m₃ i)) F (S.X₂.homology i))
    (hh₁ : ∀ i k, h₂ i (Fin.castAdd (m₃ i) k) =
      (HomologicalComplex.homologyMap S.f i).hom (h₁ i k))
    (hh₃ : ∀ i k, (HomologicalComplex.homologyMap S.g i).hom
      (h₂ i (Fin.natAdd (m₁ i) k)) = h₃ i k) :
    S.X₂.reidemeisterTorsionWithHomology c₂ h₂ =
      (∏ᶠ j : ℤ, (-1 : F) ^ (
        finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) *
          finrank F (S.X₁.homology (j + 1)) +
        (finrank F (LinearMap.range (S.X₃.d (j + 1 + 1) (j + 1)).hom) +
          finrank F (S.X₃.homology (j + 1))) *
          finrank F (LinearMap.range (S.X₁.d (j + 1) j).hom))) *
      (S.X₁.reidemeisterTorsionWithHomology c₁ h₁ *
        S.X₃.reidemeisterTorsionWithHomology c₃ h₃) := by
  refine σ.shortExact.reidemeisterTorsionWithHomology_eq_mul_of_δ_eq_zero ?_
    c₁ c₃ c₂ hc₁ hc₃ h₁ h₃ h₂ hh₁ hh₃
  intro i
  have hcomp := σ.shortExact.comp_δ (i + 1) i rfl
  rw [← Category.id_comp (σ.shortExact.δ (i + 1) i rfl),
    ← HomologicalComplex.homologyMap_id, ← σ.s_g, HomologicalComplex.homologyMap_comp,
    Category.assoc, hcomp, Limits.comp_zero]

end CategoryTheory.ShortComplex.Splitting

namespace HomologicalComplex

variable {F : Type*} [Field F] {C₁ C₃ : ChainComplex (ModuleCat F) ℤ} {n₁ n₃ m₁ m₃ : ℤ → ℕ}

/-- **Torsion with homology bases of a direct sum.** The torsion of the biproduct `C₁ ⊞ C₃` of two
based chain complexes with based homology, based in each degree by the bases of `C₁` followed by
the bases of `C₃`, is `τ(C₁ ⊞ C₃) = ε · τ(C₁) · τ(C₃)`, with the sign
`ε = ∏ⱼ (-1) ^ (dim B₃,ⱼ₊₁ · dim H₁,ⱼ₊₁ + (dim B₃,ⱼ₊₁ + dim H₃,ⱼ₊₁) · dim B₁,ⱼ)`. -/
theorem reidemeisterTorsionWithHomology_biprod
    (c₁ : ∀ i, Basis (Fin (n₁ i)) F (C₁.X i)) (c₃ : ∀ i, Basis (Fin (n₃ i)) F (C₃.X i))
    (h₁ : ∀ i, Basis (Fin (m₁ i)) F (C₁.homology i))
    (h₃ : ∀ i, Basis (Fin (m₃ i)) F (C₃.homology i)) :
    (C₁ ⊞ C₃).reidemeisterTorsionWithHomology
        (fun i ↦ (biprodXBasis (c₁ i) (c₃ i)).reindex finSumFinEquiv)
        (fun i ↦ (biprodHomologyBasis (h₁ i) (h₃ i)).reindex finSumFinEquiv) =
      (∏ᶠ j : ℤ, (-1 : F) ^ (
        finrank F (LinearMap.range (C₃.d (j + 1 + 1) (j + 1)).hom) *
          finrank F (C₁.homology (j + 1)) +
        (finrank F (LinearMap.range (C₃.d (j + 1 + 1) (j + 1)).hom) +
          finrank F (C₃.homology (j + 1))) *
          finrank F (LinearMap.range (C₁.d (j + 1) j).hom))) *
      (C₁.reidemeisterTorsionWithHomology c₁ h₁ * C₃.reidemeisterTorsionWithHomology c₃ h₃) :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct C₁ C₃).reidemeisterTorsionWithHomology_eq_mul
    c₁ c₃ _ (by simp) (by simp [← ModuleCat.comp_apply]) h₁ h₃ _
    (by simp) (by simp [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp])

end HomologicalComplex
