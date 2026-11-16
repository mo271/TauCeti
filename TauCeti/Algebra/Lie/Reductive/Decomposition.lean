/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Killing
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.LinearAlgebra.Projection
public import TauCeti.Algebra.Lie.Reductive.Basic
import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Algebra.Lie.Subalgebra.Automorphism

/-!
# Centre/derived splitting from a Killing derived ideal and automorphism assembly

Let `L` be a Lie algebra over a field `K`. When the derived ideal `⁅L, L⁆ = derivedSeries K L 1`
has nondegenerate Killing form (`LieAlgebra.IsKilling K (derivedSeries K L 1)`), every derivation
of `⁅L, L⁆` is inner (`LieDerivation.IsKilling.exists_eq_ad`), and `⁅L, L⁆` is automatically
finite-dimensional (`TauCeti.finite_of_isKilling`) and centreless. Subtracting from any `x : L`
the element of `⁅L, L⁆` inducing the same derivation on `⁅L, L⁆` produces a vector `z`
centralizing `⁅L, L⁆`; by the Jacobi identity every bracket `⁅y, z⁆` then lies in the centre of
`⁅L, L⁆`, which is trivial, so `z` is central in `L`. Hence `L = Z(L) ⊕ ⁅L, L⁆` and `L` has
central radical, with no characteristic-zero hypothesis on `K` and no finite-dimensionality
assumption on `Z(L)`.

Over an arbitrary commutative ring `R`, any Lie algebra equivalence `L₁ ≃ₗ⁅R⁆ L₂` restricts to
equivalences on the centres (`LieEquiv.restrictCenter`) and on each term of the derived series
(`LieEquiv.restrictDerivedSeries`). Conversely, whenever `center R L` and `derivedSeries R L 1`
are complementary, `L` is canonically isomorphic as a Lie algebra to their product
(`LieEquiv.centerDerivedProdEquiv`), and a pair of automorphisms of `center R L` and of
`derivedSeries R L 1` assembles into an automorphism of `L` (`LieEquiv.ofCenterDerived`).

## Main declarations

* `LieIdeal.adRestrict`: the derivation of a Lie ideal `I` induced by bracketing with an ambient
  element `x : L`.
* `TauCeti.isCompl_center_derivedSeries_of_isKilling_derivedSeries`: over any field `K`, if
  `derivedSeries K L 1` is Killing, then `IsCompl (center K L) (derivedSeries K L 1)`.
* `TauCeti.hasCentralRadical_of_isKilling_derivedSeries`: under the same hypothesis, `L` has
  central radical.
* `LieEquiv.restrictCenter` and `LieEquiv.restrictDerivedSeries`: restriction of a Lie equivalence
  to the centres and to the `k`-th derived ideals.
* `LieEquiv.centerDerivedProdEquiv`: the product Lie-algebra isomorphism
  `(center R L × derivedSeries R L 1) ≃ₗ⁅R⁆ L` associated with a direct-sum decomposition.
* `LieEquiv.ofCenterDerived`: assembles automorphisms of `center R L` and `derivedSeries R L 1`
  into an automorphism of `L`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §6.2 and §6.4.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter I, §7 and Chapter VI, §2.
-/

public section

open LieAlgebra

namespace LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Bracketing with an ambient element `x : L` restricts to a Lie derivation of any Lie ideal
`I`. -/
def adRestrict (I : LieIdeal R L) (x : L) : LieDerivation R I I where
  toFun w := ⟨⁅x, (w : L)⁆, I.lie_mem w.2⟩
  map_add' a b := Subtype.ext (lie_add x (a : L) (b : L))
  map_smul' r a := Subtype.ext (lie_smul r x (a : L))
  leibniz' a b := Subtype.ext <| by
    simp only [AddSubgroupClass.coe_sub, LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [leibniz_lie x (a : L) (b : L), ← lie_skew ⁅x, (a : L)⁆ (b : L), sub_eq_add_neg, add_comm]

@[simp]
theorem coe_adRestrict_apply (I : LieIdeal R L) (x : L) (w : I) :
    (I.adRestrict x w : L) = ⁅x, (w : L)⁆ :=
  (rfl)

end LieIdeal

namespace TauCeti

section KillingDerived

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [IsKilling K (derivedSeries K L 1)]

/-- **Centre/derived splitting from a Killing derived ideal.** Over any field `K` (with no
characteristic-zero hypothesis and no finiteness assumption on `center K L`), if the derived ideal
`derivedSeries K L 1` has nondegenerate Killing form, then `L` is the direct sum of its centre and
its derived ideal. -/
theorem isCompl_center_derivedSeries_of_isKilling_derivedSeries :
    IsCompl (center K L) (derivedSeries K L 1) := by
  have _f : Module.Finite K (derivedSeries K L 1) :=
    finite_of_isKilling (R := K) (L := derivedSeries K L 1)
  refine ⟨disjoint_iff.mpr (eq_bot_iff.mpr fun z hz ↦ ?_),
    codisjoint_iff.mpr (eq_top_iff.mpr fun x _ ↦ ?_)⟩
  · -- Any central element of `L` lying in `derivedSeries K L 1` is central there, hence zero.
    have hzc : (⟨z, hz.2⟩ : derivedSeries K L 1) ∈ center K (derivedSeries K L 1) := by
      rw [LieModule.mem_maxTrivSubmodule]
      intro y
      exact Subtype.ext ((LieModule.mem_maxTrivSubmodule K L L z).mp hz.1 y)
    rw [LieAlgebra.center_eq_bot] at hzc
    exact (LieSubmodule.mem_bot _).mpr (congrArg Subtype.val ((LieSubmodule.mem_bot _).mp hzc))
  · -- Match the derivation `w ↦ ⁅x, w⁆` on `derivedSeries K L 1` by an inner derivation `ad d`.
    obtain ⟨d, hd⟩ := LieDerivation.IsKilling.exists_eq_ad ((derivedSeries K L 1).adRestrict x)
    have hdx (w : derivedSeries K L 1) : ⁅(d : L), (w : L)⁆ = ⁅x, (w : L)⁆ := by
      simpa using congrArg Subtype.val (LieDerivation.congr_fun hd w)
    have hzD (w : derivedSeries K L 1) : ⁅x - (d : L), (w : L)⁆ = 0 := by
      rw [sub_lie, hdx w, sub_self]
    -- By Jacobi, every bracket `⁅y, x - d⁆` centralizes `derivedSeries K L 1`, hence vanishes.
    have hz : x - (d : L) ∈ center K L := by
      rw [LieModule.mem_maxTrivSubmodule]
      intro y
      have hyz : (⟨⁅y, x - (d : L)⁆, lie_mem_derivedSeries_one y (x - d)⟩ :
          derivedSeries K L 1) ∈ center K (derivedSeries K L 1) := by
        rw [LieModule.mem_maxTrivSubmodule]
        intro w
        apply Subtype.ext
        simp only [LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket,
          ZeroMemClass.coe_zero]
        have hwy : ⁅(w : L), y⁆ ∈ derivedSeries K L 1 := lie_mem_derivedSeries_one (w : L) y
        have h1 : ⁅⁅(w : L), y⁆, x - (d : L)⁆ = 0 := by
          rw [← lie_skew, hzD ⟨⁅(w : L), y⁆, hwy⟩, neg_zero]
        have h2 : ⁅(w : L), x - (d : L)⁆ = 0 := by
          rw [← lie_skew, hzD w, neg_zero]
        rw [leibniz_lie, h1, h2, lie_zero, add_zero]
      rw [LieAlgebra.center_eq_bot] at hyz
      exact congrArg Subtype.val ((LieSubmodule.mem_bot _).mp hyz)
    rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.sup_toSubmodule]
    exact Submodule.mem_sup.mpr ⟨x - d, hz, d, d.2, sub_add_cancel x d⟩

/-- Over any field `K`, a Lie algebra whose derived ideal has nondegenerate Killing form has
central radical. -/
theorem hasCentralRadical_of_isKilling_derivedSeries : HasCentralRadical K L := by
  have _f : Module.Finite K (derivedSeries K L 1) :=
    finite_of_isKilling (R := K) (L := derivedSeries K L 1)
  exact hasCentralRadical_of_hasTrivialRadical_derivedSeries K L

end KillingDerived

end TauCeti

namespace LieEquiv

section Restrict

variable {R L₁ L₂ L₃ : Type*} [CommRing R] [LieRing L₁] [LieAlgebra R L₁]
  [LieRing L₂] [LieAlgebra R L₂] [LieRing L₃] [LieAlgebra R L₃]

/-- A Lie algebra equivalence maps central elements to central elements. -/
theorem apply_mem_center (e : L₁ ≃ₗ⁅R⁆ L₂) {z : L₁} (hz : z ∈ center R L₁) :
    e z ∈ center R L₂ := by
  rw [LieModule.mem_maxTrivSubmodule]
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  simp only [coe_toLieHom]
  rw [← e.map_lie, (LieModule.mem_maxTrivSubmodule R L₁ L₁ z).mp hz x, map_zero]

/-- A Lie algebra equivalence maps the centre onto the centre. -/
theorem map_center (e : L₁ ≃ₗ⁅R⁆ L₂) :
    (center R L₁).toLieSubalgebra.map e = (center R L₂).toLieSubalgebra :=
  LieSubalgebra.map_eq_of_mem e (fun _ hz ↦ e.apply_mem_center hz)
    (fun _ hz ↦ e.symm.apply_mem_center hz)

/-- Restrict a Lie algebra equivalence to an equivalence between the centres. -/
def restrictCenter (e : L₁ ≃ₗ⁅R⁆ L₂) : center R L₁ ≃ₗ⁅R⁆ center R L₂ :=
  e.ofSubalgebras _ _ e.map_center

@[simp]
theorem coe_restrictCenter (e : L₁ ≃ₗ⁅R⁆ L₂) (z : center R L₁) :
    (e.restrictCenter z : L₂) = e z :=
  (rfl)

@[simp]
theorem restrictCenter_symm (e : L₁ ≃ₗ⁅R⁆ L₂) :
    e.restrictCenter.symm = e.symm.restrictCenter :=
  LieEquiv.ext fun _ ↦ Subtype.ext rfl

@[simp]
theorem restrictCenter_refl :
    (LieEquiv.refl : L₁ ≃ₗ⁅R⁆ L₁).restrictCenter = LieEquiv.refl :=
  LieEquiv.ext fun z ↦ Subtype.ext (coe_restrictCenter _ z)

@[simp]
theorem restrictCenter_trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) :
    (e₁.trans e₂).restrictCenter = e₁.restrictCenter.trans e₂.restrictCenter :=
  LieEquiv.ext fun z ↦ Subtype.ext (by simp)

/-- An involutive automorphism restricts to an involutive automorphism of the centre. -/
theorem involutive_restrictCenter {e : L₁ ≃ₗ⁅R⁆ L₁} (he : Function.Involutive e) :
    Function.Involutive e.restrictCenter :=
  fun z ↦ Subtype.ext (by simpa using he z)

/-- A Lie algebra equivalence maps the `k`-th derived ideal into the `k`-th derived ideal. -/
theorem apply_mem_derivedSeries (e : L₁ ≃ₗ⁅R⁆ L₂) (k : ℕ) {x : L₁}
    (hx : x ∈ derivedSeries R L₁ k) : e x ∈ derivedSeries R L₂ k :=
  LieIdeal.derivedSeries_map_le (f := e.toLieHom) k (LieIdeal.mem_map hx)

/-- A Lie algebra equivalence maps the `k`-th derived ideal onto the `k`-th derived ideal. -/
theorem map_derivedSeries (e : L₁ ≃ₗ⁅R⁆ L₂) (k : ℕ) :
    (derivedSeries R L₁ k).toLieSubalgebra.map e = (derivedSeries R L₂ k).toLieSubalgebra :=
  LieSubalgebra.map_eq_of_mem e (fun _ hx ↦ e.apply_mem_derivedSeries k hx)
    (fun _ hx ↦ e.symm.apply_mem_derivedSeries k hx)

/-- Restrict a Lie algebra equivalence to the `k`-th terms of the derived series. -/
def restrictDerivedSeries (e : L₁ ≃ₗ⁅R⁆ L₂) (k : ℕ) :
    derivedSeries R L₁ k ≃ₗ⁅R⁆ derivedSeries R L₂ k :=
  e.ofSubalgebras _ _ (e.map_derivedSeries k)

@[simp]
theorem coe_restrictDerivedSeries (e : L₁ ≃ₗ⁅R⁆ L₂) (k : ℕ) (x : derivedSeries R L₁ k) :
    (e.restrictDerivedSeries k x : L₂) = e x :=
  (rfl)

@[simp]
theorem restrictDerivedSeries_symm (e : L₁ ≃ₗ⁅R⁆ L₂) (k : ℕ) :
    (e.restrictDerivedSeries k).symm = e.symm.restrictDerivedSeries k :=
  LieEquiv.ext fun _ ↦ Subtype.ext rfl

@[simp]
theorem restrictDerivedSeries_refl (k : ℕ) :
    (LieEquiv.refl : L₁ ≃ₗ⁅R⁆ L₁).restrictDerivedSeries k = LieEquiv.refl :=
  LieEquiv.ext fun x ↦ Subtype.ext (coe_restrictDerivedSeries _ k x)

@[simp]
theorem restrictDerivedSeries_trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (k : ℕ) :
    (e₁.trans e₂).restrictDerivedSeries k =
      (e₁.restrictDerivedSeries k).trans (e₂.restrictDerivedSeries k) :=
  LieEquiv.ext fun x ↦ Subtype.ext (by simp)

/-- An involutive automorphism restricts to an involutive automorphism of each derived ideal. -/
theorem involutive_restrictDerivedSeries {e : L₁ ≃ₗ⁅R⁆ L₁} (he : Function.Involutive e) (k : ℕ) :
    Function.Involutive (e.restrictDerivedSeries k) :=
  fun x ↦ Subtype.ext (by simpa using he x)

end Restrict

section Assemble

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- When the centre and the derived ideal of `L` are complementary, addition identifies their
product Lie algebra with `L`. -/
noncomputable def centerDerivedProdEquiv
    (h : IsCompl (center R L) (derivedSeries R L 1)) :
    (center R L × derivedSeries R L 1) ≃ₗ⁅R⁆ L where
  __ := (center R L).toSubmodule.prodEquivOfIsCompl (derivedSeries R L 1).toSubmodule
    (LieSubmodule.isCompl_toSubmodule.mpr h)
  map_lie' {p q} := by
    have hz (z : center R L) (y : L) : ⁅y, (z : L)⁆ = 0 :=
      (LieModule.mem_maxTrivSubmodule R L L z).mp z.2 y
    have hzl (z : center R L) (y : L) : ⁅(z : L), y⁆ = 0 := by
      rw [← lie_skew, hz z y, neg_zero]
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      Submodule.coe_prodEquivOfIsCompl', LieAlgebra.Prod.bracket_apply]
    simp [add_lie, lie_add, hz, hzl]

@[simp]
theorem centerDerivedProdEquiv_apply (h : IsCompl (center R L) (derivedSeries R L 1))
    (p : center R L × derivedSeries R L 1) :
    centerDerivedProdEquiv h p = (p.1 : L) + p.2 :=
  (rfl)

@[simp]
theorem centerDerivedProdEquiv_symm_center (h : IsCompl (center R L) (derivedSeries R L 1))
    (z : center R L) :
    (centerDerivedProdEquiv h).symm z = (z, 0) := by
  simp [centerDerivedProdEquiv]

@[simp]
theorem centerDerivedProdEquiv_symm_derivedSeries (h : IsCompl (center R L) (derivedSeries R L 1))
    (d : derivedSeries R L 1) :
    (centerDerivedProdEquiv h).symm d = (0, d) :=
  (centerDerivedProdEquiv h).symm_apply_eq.mpr (by simp)

/-- Assemble automorphisms of `center R L` and `derivedSeries R L 1` into an automorphism of `L`
along a direct-sum decomposition `L = center R L ⊕ derivedSeries R L 1`. -/
noncomputable def ofCenterDerived (h : IsCompl (center R L) (derivedSeries R L 1))
    (e_z : center R L ≃ₗ⁅R⁆ center R L)
    (e_d : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) : L ≃ₗ⁅R⁆ L :=
  (centerDerivedProdEquiv h).symm.trans <|
    ({ __ := e_z.toLieHom.prodMap e_d.toLieHom
       invFun := Prod.map e_z.symm e_d.symm
       left_inv := fun p ↦ Prod.ext (e_z.symm_apply_apply p.1) (e_d.symm_apply_apply p.2)
       right_inv := fun p ↦ Prod.ext (e_z.apply_symm_apply p.1) (e_d.apply_symm_apply p.2) } :
      (center R L × derivedSeries R L 1) ≃ₗ⁅R⁆ (center R L × derivedSeries R L 1)).trans
      (centerDerivedProdEquiv h)

@[simp]
theorem ofCenterDerived_apply_center (h : IsCompl (center R L) (derivedSeries R L 1))
    (e_z : center R L ≃ₗ⁅R⁆ center R L)
    (e_d : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) (z : center R L) :
    ofCenterDerived h e_z e_d z = e_z z := by
  simp [ofCenterDerived]

@[simp]
theorem ofCenterDerived_apply_derivedSeries (h : IsCompl (center R L) (derivedSeries R L 1))
    (e_z : center R L ≃ₗ⁅R⁆ center R L)
    (e_d : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) (d : derivedSeries R L 1) :
    ofCenterDerived h e_z e_d d = e_d d := by
  simp [ofCenterDerived]

@[simp]
theorem restrictCenter_ofCenterDerived (h : IsCompl (center R L) (derivedSeries R L 1))
    (e_z : center R L ≃ₗ⁅R⁆ center R L)
    (e_d : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofCenterDerived h e_z e_d).restrictCenter = e_z :=
  LieEquiv.ext fun z ↦ Subtype.ext (by simp)

@[simp]
theorem restrictDerivedSeries_one_ofCenterDerived (h : IsCompl (center R L) (derivedSeries R L 1))
    (e_z : center R L ≃ₗ⁅R⁆ center R L)
    (e_d : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    (ofCenterDerived h e_z e_d).restrictDerivedSeries 1 = e_d :=
  LieEquiv.ext fun d ↦ Subtype.ext (by simp)

/-- The assembled automorphism `ofCenterDerived h e_z e_d` is involutive if and only if both `e_z`
and `e_d` are involutive. -/
theorem involutive_ofCenterDerived_iff (h : IsCompl (center R L) (derivedSeries R L 1))
    (e_z : center R L ≃ₗ⁅R⁆ center R L)
    (e_d : derivedSeries R L 1 ≃ₗ⁅R⁆ derivedSeries R L 1) :
    Function.Involutive (ofCenterDerived h e_z e_d) ↔
      Function.Involutive e_z ∧ Function.Involutive e_d := by
  refine ⟨fun hinv ↦ ⟨?_, ?_⟩, fun ⟨hz, hd⟩ x ↦ ?_⟩
  · simpa using involutive_restrictCenter hinv
  · simpa using involutive_restrictDerivedSeries hinv 1
  · obtain ⟨⟨z, d⟩, rfl⟩ := (centerDerivedProdEquiv h).surjective x
    simp [map_add, hz z, hd d]

end Assemble

end LieEquiv
