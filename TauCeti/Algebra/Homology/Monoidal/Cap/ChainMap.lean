/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import TauCeti.Algebra.Homology.Embedding.DownNatAdd
public import TauCeti.Algebra.Homology.Embedding.UpNatAdd
public import TauCeti.Algebra.Homology.Monoidal.Cap.Kronecker

/-!
# Capping with a fixed cocycle as a chain map

Let `D : E ⟶ A ⊗ B` be a diagonal of `ℕ`-indexed chain complexes in a `k`-linear monoidal abelian
category, let `a : M ⊗ B ⟶ B'` be an action of the coefficient object `M`, and let
`φ : (A.linearYonedaObj k M).cycles p` be a cocycle of degree `p`.  By the boundary formula
`TauCeti.ChainComplex.capChain_comp_d_of_cycles`,
`∂(x ⌢ φ) = (-1)^p ∂x ⌢ φ`.  Multiplying the degree-`(p + q)` cap product by the sign
`(-1)^(p * q)` cancels the factor `(-1)^p` at each step `q + 1 ↦ q`, turning capping with `φ` into
a chain map

`capChainMap k D a p φ : E ⟶ B'.extend (ComplexShape.embeddingDownNatAdd p)`

into `B'` shifted upward by `p` degrees (zero in degrees `< p`, and `B'_q` in degree `p + q`).

On homology in degree `n = p + q`, `capChainMap k D a p φ` induces `(-1)^(p * q)` times the
homology cap product `TauCeti.ChainComplex.cap` with the cohomology class of `φ`.  On cohomology
with coefficients in an object `N'`, precomposition with `capChainMap k D a p φ` agrees (under the
shift identification `TauCeti.ChainComplex.linearYonedaObjExtendIso`) with `(-1)^(p * q)` times
the cup product `TauCeti.ChainComplex.cup` with the class of `φ`, via the Kronecker compatibility
`TauCeti.ChainComplex.capChain_comp`.

## Main definitions and results

* `TauCeti.ChainComplex.capChainMap`: capping with a cocycle of degree `p` as a chain map into
  `B'.extend (ComplexShape.embeddingDownNatAdd p)`.
* `TauCeti.ChainComplex.capChainMap_f` and `TauCeti.ChainComplex.capChainMap_f_of_lt`: the
  components of `capChainMap`.
* `TauCeti.ChainComplex.capChainMap_naturality`: naturality along maps of diagonals and actions.
* `TauCeti.ChainComplex.homologyMap_capChainMap_comp_extendHomologyIso_hom`: the map induced on
  homology is `(-1)^(p * q)` times `TauCeti.ChainComplex.cap`.
* `TauCeti.ChainComplex.homologyMap_linearYonedaFunctor_map_capChainMap_apply`: the map induced on
  cohomology is `(-1)^(p * q)` times `TauCeti.ChainComplex.cup`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the cap product and its relation to the cup product.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex Opposite

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]

section Ring

variable {A B B' E : ChainComplex C ℕ} [A.HasTensor B] {M : C}
  {k : Type*} [Ring k] [Linear k C] [MonoidalLinear k C]
  (D : E ⟶ HomologicalComplex.tensorObj A B)
  (a : ((tensorLeft M).mapHomologicalComplex _).obj B ⟶ B')

variable (k) in
/-- **Capping with a cocycle as a chain map**: for a cocycle `φ` of degree `p`, the chain map
`E ⟶ B'.extend (ComplexShape.embeddingDownNatAdd p)` whose component in degree `n = p + q` is
`(-1)^(p * q)` times `capChain k D a p q n _ φ` composed with `(B'.extendXIso _ _).inv`, and `0` in
degrees below `p`. -/
def capChainMap (p : ℕ) (φ : (A.linearYonedaObj k M).cycles p) :
    E ⟶ B'.extend (ComplexShape.embeddingDownNatAdd p) where
  f m :=
    if h : p ≤ m then
      ((-1 : ℤ) ^ (p * (m - p))) •
        capChain k D a p (m - p) m (by omega) ((A.linearYonedaObj k M).iCycles p φ) ≫
          (B'.extendXIso (ComplexShape.embeddingDownNatAdd p) (by simp; omega)).inv
    else 0
  comm' m n hmn := by
    obtain rfl : n + 1 = m := hmn
    by_cases hn : p ≤ n
    · have hm : p ≤ n + 1 := by omega
      set q := n - p
      have hq : p + q = n := by omega
      have hcap := capChain_comp_d_of_cycles (k := k) D a p q n hq φ
      have hsign : ((-1 : ℤ) ^ (p * (q + 1))) * ((-1 : ℤ) ^ p) = (-1 : ℤ) ^ (p * q) := by
        rw [← pow_add, show p * (q + 1) + p = p * q + 2 * p by ring, pow_add,
          pow_mul (-1 : ℤ) 2 p, neg_one_sq, one_pow, mul_one]
      let φ₀ : A.X p ⟶ M := (A.linearYonedaObj k M).iCycles p φ
      change (if h : p ≤ n + 1 then _ else 0) ≫ _ = _ ≫ (if h : p ≤ n then _ else 0)
      rw [dite_eq_left hm, dite_eq_left hn]
      suffices ∀ (q₁ : ℕ) (h1 : p + q₁ = n + 1)
          (h2 : (ComplexShape.embeddingDownNatAdd p).f q₁ = n + 1),
          (((-1 : ℤ) ^ (p * q₁)) •
            (capChain k D a p q₁ (n + 1) h1 φ₀ ≫
              (B'.extendXIso (ComplexShape.embeddingDownNatAdd p) h2).inv)) ≫
            (B'.extend (ComplexShape.embeddingDownNatAdd p)).d (n + 1) n =
          E.d (n + 1) n ≫ (((-1 : ℤ) ^ (p * q)) •
            (capChain k D a p q n hq φ₀ ≫
              (B'.extendXIso (ComplexShape.embeddingDownNatAdd p)
                (i := q) (i' := n) (by simp; omega)).inv)) from
        this (n + 1 - p) (by omega) (by simp; omega)
      intro q₁ h1 h2
      obtain rfl : q₁ = q + 1 := by omega
      have hd : (B'.extendXIso (ComplexShape.embeddingDownNatAdd p) h2).inv ≫
          (B'.extend (ComplexShape.embeddingDownNatAdd p)).d (n + 1) n =
          B'.d (q + 1) q ≫
            (B'.extendXIso (ComplexShape.embeddingDownNatAdd p)
              (i := q) (i' := n) (by simp; omega)).inv := by
        rw [B'.extend_d_eq (ComplexShape.embeddingDownNatAdd p)
          (i := q + 1) (j := q) h2 (by simp; omega), Iso.inv_hom_id_assoc]
      have hcap' : capChain k D a p (q + 1) (n + 1) h1 φ₀ ≫ B'.d (q + 1) q =
          ((-1 : ℤ) ^ p) • (E.d (n + 1) n ≫ capChain k D a p q n hq φ₀) := hcap
      rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc, hd, reassoc_of% hcap',
        Preadditive.zsmul_comp, smul_smul, hsign, Category.assoc]
    · exact (B'.isZero_extend_X (ComplexShape.embeddingDownNatAdd p) n
        (by simp; omega)).eq_of_tgt _ _

/-- In degree `n = p + q`, `capChainMap` is `(-1)^(p * q)` times `capChain` composed with the
inverse of `extendXIso`. -/
lemma capChainMap_f (p q n : ℕ) (h : p + q = n) (φ : (A.linearYonedaObj k M).cycles p) :
    (capChainMap k D a p φ).f n =
      ((-1 : ℤ) ^ (p * q)) •
        capChain k D a p q n h ((A.linearYonedaObj k M).iCycles p φ) ≫
          (B'.extendXIso (ComplexShape.embeddingDownNatAdd p) (by simp; omega)).inv := by
  have hle : p ≤ n := by omega
  have hsub : n - p = q := by omega
  dsimp [capChainMap]
  rw [dite_eq_left hle]
  subst hsub
  rfl

/-- In degrees `n < p`, `capChainMap` vanishes. -/
lemma capChainMap_f_of_lt (p n : ℕ) (h : n < p) (φ : (A.linearYonedaObj k M).cycles p) :
    (capChainMap k D a p φ).f n = 0 := by
  dsimp [capChainMap]
  exact dite_eq_right (by omega)

/-- **Naturality of `capChainMap`** along maps of diagonals and actions: if `φ'` is a cocycle of
`Hom(A', M)` whose underlying cochain is the pullback of `φ` along `f`, then capping along `D'`
with `φ'` and pushing forward along `g'` agrees with pushing forward along `e` and capping along
`D` with `φ`. -/
lemma capChainMap_naturality {A' B₁ B₁' E' : ChainComplex C ℕ} [A'.HasTensor B₁]
    (D' : E' ⟶ HomologicalComplex.tensorObj A' B₁)
    (a' : ((tensorLeft M).mapHomologicalComplex _).obj B₁ ⟶ B₁') (e : E' ⟶ E) (f : A' ⟶ A)
    (g : B₁ ⟶ B) (g' : B₁' ⟶ B') (hD : e ≫ D = D' ≫ HomologicalComplex.tensorHom f g)
    (ha : a' ≫ g' = ((tensorLeft M).mapHomologicalComplex _).map g ≫ a) (p : ℕ)
    (φ : (A.linearYonedaObj k M).cycles p) (φ' : (A'.linearYonedaObj k M).cycles p)
    (hφ : (A'.linearYonedaObj k M).iCycles p φ' = f.f p ≫ (A.linearYonedaObj k M).iCycles p φ) :
    capChainMap k D' a' p φ' ≫
        HomologicalComplex.extendMap g' (ComplexShape.embeddingDownNatAdd p) =
      e ≫ capChainMap k D a p φ := by
  ext m
  by_cases hm : p ≤ m
  · have hq : p + (m - p) = m := by omega
    simp only [comp_f, capChainMap_f D' a' p (m - p) m hq φ', capChainMap_f D a p (m - p) m hq φ,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
    rw [HomologicalComplex.extendMap_f g' (ComplexShape.embeddingDownNatAdd p)
      (i := m - p) (i' := m) (by simp; omega), Iso.inv_hom_id_assoc, hφ,
      reassoc_of% (capChain_naturality (k := k) D a D' a' e f g g' hD ha p (m - p) m hq
        ((A.linearYonedaObj k M).iCycles p φ))]
  · exact (B'.isZero_extend_X (ComplexShape.embeddingDownNatAdd p) m
      (by simp; omega)).eq_of_tgt _ _

/-- **Action of `capChainMap` on homology**: in degree `n = p + q`, under `extendHomologyIso`, the
induced map on homology is `(-1)^(p * q)` times `TauCeti.ChainComplex.cap`. -/
theorem homologyMap_capChainMap_comp_extendHomologyIso_hom (p q n : ℕ) (h : p + q = n)
    (φ : (A.linearYonedaObj k M).cycles p) :
    homologyMap (capChainMap k D a p φ) n ≫
        (B'.extendHomologyIso (ComplexShape.embeddingDownNatAdd p) (by simp; omega)).hom =
      ((-1 : ℤ) ^ (p * q)) •
        cap k D a p q n h ((A.linearYonedaObj k M).homologyπ p φ) := by
  rw [← cancel_epi (E.homologyπ n), homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom,
    ← Category.assoc, Preadditive.comp_zsmul, cap_homologyπ, ← Preadditive.zsmul_comp]
  congr 1
  rw [← cancel_mono (B'.iCycles q), Category.assoc, extendCyclesIso_hom_iCycles, cyclesMap_i_assoc,
    capChainMap_f D a p q n h φ, Preadditive.zsmul_comp, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Preadditive.comp_zsmul, Preadditive.zsmul_comp, capCycles_i]

end Ring

section CommRing

variable {A B B' E : ChainComplex C ℕ} [A.HasTensor B] {M N N' : C}
  {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C]
  (D : E ⟶ HomologicalComplex.tensorObj A B)
  (a : ((tensorLeft M).mapHomologicalComplex _).obj B ⟶ B') (ν : M ⊗ N ⟶ N')

/-- **Action of `capChainMap` on cohomology**: in degree `n = p + q`, under
`linearYonedaObjExtendIso` and `extendHomologyIso`, precomposition with `capChainMap k D a p φ`
sends the class of a cocycle `ψ` (compatible with `ψ'` along `a` and `ν`) to `(-1)^(p * q)` times
the cup product of the classes of `φ` and `ψ'`. -/
theorem homologyMap_linearYonedaFunctor_map_capChainMap_apply (p q n : ℕ) (h : p + q = n)
    (φ : (A.linearYonedaObj k M).cycles p)
    (ψ : (B'.linearYonedaObj k N').cycles q)
    (ψ' : (B.linearYonedaObj k N).cycles q)
    (hψ : a.f q ≫ (B'.linearYonedaObj k N').iCycles q ψ =
      (M ◁ (B.linearYonedaObj k N).iCycles q ψ') ≫ ν) :
    homologyMap
        ((linearYonedaObjExtendIso k N' B' (ComplexShape.embeddingDownNatAdd p)
          (ComplexShape.embeddingUpNatAdd p) (fun _ ↦ by simp)).inv ≫
          (linearYonedaFunctor k N').map (capChainMap k D a p φ).op) n
        (((B'.linearYonedaObj k N').extendHomologyIso (ComplexShape.embeddingUpNatAdd p)
          (by simp; omega)).inv ((B'.linearYonedaObj k N').homologyπ q ψ)) =
      ((-1 : ℤ) ^ (p * q)) •
        cup k D ν p q n h ((A.linearYonedaObj k M).homologyπ p φ)
          ((B.linearYonedaObj k N).homologyπ q ψ') := by
  let f : (B'.linearYonedaObj k N').extend (ComplexShape.embeddingUpNatAdd p) ⟶
      E.linearYonedaObj k N' :=
    (linearYonedaObjExtendIso k N' B' (ComplexShape.embeddingDownNatAdd p)
      (ComplexShape.embeddingUpNatAdd p) (fun _ ↦ by simp)).inv ≫
      (linearYonedaFunctor k N').map (capChainMap k D a p φ).op
  have heq :
      (((B'.linearYonedaObj k N').extendHomologyIso (ComplexShape.embeddingUpNatAdd p)
        (by simp; omega)).inv ((B'.linearYonedaObj k N').homologyπ q ψ)) =
      ((B'.linearYonedaObj k N').extend (ComplexShape.embeddingUpNatAdd p)).homologyπ n
        (((B'.linearYonedaObj k N').extendCyclesIso (ComplexShape.embeddingUpNatAdd p)
          (by simp; omega)).inv ψ) :=
    ConcreteCategory.congr_hom (homologyπ_extendHomologyIso_inv _ _ _) ψ
  have hnat :
      homologyMap f n
        (((B'.linearYonedaObj k N').extend (ComplexShape.embeddingUpNatAdd p)).homologyπ n
          (((B'.linearYonedaObj k N').extendCyclesIso (ComplexShape.embeddingUpNatAdd p)
            (by simp; omega)).inv ψ)) =
      (E.linearYonedaObj k N').homologyπ n
        (cyclesMap f n
          (((B'.linearYonedaObj k N').extendCyclesIso (ComplexShape.embeddingUpNatAdd p)
            (by simp; omega)).inv ψ)) :=
    ConcreteCategory.congr_hom (homologyπ_naturality f n) _
  change homologyMap f n _ = _
  rw [heq, hnat, cup_homologyπ, ← map_zsmul]
  congr 1
  apply (ModuleCat.mono_iff_injective ((E.linearYonedaObj k N').iCycles n)).mp inferInstance
  have hi : (E.linearYonedaObj k N').iCycles n
      (cyclesMap f n
        (((B'.linearYonedaObj k N').extendCyclesIso (ComplexShape.embeddingUpNatAdd p)
          (by simp; omega)).inv ψ)) =
      f.f n (((B'.linearYonedaObj k N').extend (ComplexShape.embeddingUpNatAdd p)).iCycles n
        (((B'.linearYonedaObj k N').extendCyclesIso (ComplexShape.embeddingUpNatAdd p)
          (by simp; omega)).inv ψ)) :=
    ConcreteCategory.congr_hom (cyclesMap_i f n) _
  have hi₃ : ((B'.linearYonedaObj k N').extend (ComplexShape.embeddingUpNatAdd p)).iCycles n
        (((B'.linearYonedaObj k N').extendCyclesIso (ComplexShape.embeddingUpNatAdd p)
          (j := q) (j' := n) (by simp; omega)).inv ψ) =
      ((B'.linearYonedaObj k N').extendXIso (ComplexShape.embeddingUpNatAdd p)
        (i := q) (i' := n) (by simp; omega)).inv ((B'.linearYonedaObj k N').iCycles q ψ) :=
    ConcreteCategory.congr_hom
      (extendCyclesIso_inv_iCycles (B'.linearYonedaObj k N')
        (ComplexShape.embeddingUpNatAdd p) (j := q) (j' := n) (by simp; omega)) ψ
  have hinv : ((B'.linearYonedaObj k N').extendXIso (ComplexShape.embeddingUpNatAdd p)
      (i := q) (i' := n) (by simp; omega)).hom
      (((B'.linearYonedaObj k N').extendXIso (ComplexShape.embeddingUpNatAdd p)
        (i := q) (i' := n) (by simp; omega)).inv ((B'.linearYonedaObj k N').iCycles q ψ)) =
      (B'.linearYonedaObj k N').iCycles q ψ :=
    ConcreteCategory.congr_hom
      ((B'.linearYonedaObj k N').extendXIso (ComplexShape.embeddingUpNatAdd p)
        (i := q) (i' := n) (by simp; omega)).inv_hom_id _
  rw [hi, hi₃]
  let φ₀ : A.X p ⟶ M := (A.linearYonedaObj k M).iCycles p φ
  let ψ₀ : B'.X q ⟶ N' := (B'.linearYonedaObj k N').iCycles q ψ
  let ψ₀' : B.X q ⟶ N := (B.linearYonedaObj k N).iCycles q ψ'
  have hf_apply : (f.f n
      (((B'.linearYonedaObj k N').extendXIso (ComplexShape.embeddingUpNatAdd p)
        (i := q) (i' := n) (by simp; omega)).inv ((B'.linearYonedaObj k N').iCycles q ψ)) :
        E.X n ⟶ N') =
      (capChainMap k D a p φ).f n ≫
        (B'.extendXIso (ComplexShape.embeddingDownNatAdd p)
          (i := q) (i' := n) (by simp; omega)).hom ≫ ψ₀ := by
    have h₁ := linearYonedaObjExtendIso_inv_f_apply k N' B'
      (ComplexShape.embeddingDownNatAdd p) (ComplexShape.embeddingUpNatAdd p) (fun _ ↦ by simp)
      (i := q) (i' := n) (by simp; omega)
      (((B'.linearYonedaObj k N').extendXIso (ComplexShape.embeddingUpNatAdd p)
        (i := q) (i' := n) (by simp; omega)).inv ((B'.linearYonedaObj k N').iCycles q ψ))
    rw [hinv] at h₁
    exact congrArg ((capChainMap k D a p φ).f n ≫ ·) h₁
  have hcomp : (capChainMap k D a p φ).f n ≫
      (B'.extendXIso (ComplexShape.embeddingDownNatAdd p)
        (i := q) (i' := n) (by simp; omega)).hom ≫ ψ₀ =
      ((-1 : ℤ) ^ (p * q)) • cupCochain k D ν p q n h φ₀ ψ₀' := by
    have hfm : (capChainMap k D a p φ).f n =
        ((-1 : ℤ) ^ (p * q)) • capChain k D a p q n h φ₀ ≫
          (B'.extendXIso (ComplexShape.embeddingDownNatAdd p)
            (i := q) (i' := n) (by simp; omega)).inv :=
      capChainMap_f D a p q n h φ
    rw [hfm, Preadditive.zsmul_comp, Category.assoc, Iso.inv_hom_id_assoc,
      capChain_comp D a ν p q n h φ₀ ψ₀ ψ₀' hψ]
  rw [map_zsmul]
  exact hf_apply.trans (hcomp.trans
    (congrArg (((-1 : ℤ) ^ (p * q)) • ·) (iCycles_cupCycles D ν p q n h φ ψ').symm))

end CommRing

end TauCeti.ChainComplex
