/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Hereditary.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import TauCeti.Analysis.Normed.Module.CohenFactorization.Basic
import TauCeti.Analysis.Normed.Module.Essential

/-!
# Left ideals, hereditary cones, and Cohen–Hewitt factorization

This file establishes the bijective order-preserving correspondences among closed hereditary
C⋆-subalgebras, closed left ideals, and closed hereditary positive cones of a (possibly nonunital)
C⋆-algebra `A` (Blackadar II.5.3.2), together with the Cohen–Hewitt factorization theorem for
closed left ideals (Blackadar II.5.3.7):

1. **Order isomorphisms** (Blackadar II.5.3.2):
   The maps `B ↦ {x : A | star x * x ∈ B}`, `L ↦ L ∩ L⋆`, `B ↦ {a ∈ B | 0 ≤ a}`, and
   `C ↦ {x : A | star x * x ∈ C}` establish order isomorphisms among
   * closed hereditary C⋆-subalgebras `B` of `A`,
   * closed left ideals `L` of `A` (represented as `Submodule ℂ A` satisfying `L.IsLeftIdeal`), and
   * closed hereditary positive cones `C ⊆ A` (`TauCeti.CStarAlgebra.IsHereditaryCone`).

2. **Cohen–Hewitt factorization for closed left ideals** (Blackadar II.5.3.7):
   Every element `x` of the closed left ideal `L = {x : A | star x * x ∈ B}` associated to a closed
   hereditary C⋆-subalgebra `B` factors as `x = a * b` with `a ∈ L`, `b ∈ B`, `‖b‖ ≤ 1`, and
   `‖a - x‖ < ε` for any prescribed `ε > 0`. In particular, `L = {a * b | a ∈ A, b ∈ B}`.

## Main declarations

* `Submodule.IsLeftIdeal` and `Submodule.symmetricCore`: left ideals of a possibly nonunital
  algebra and their symmetric cores `L ∩ L⋆`, with `Submodule.isHereditary_symmetricCore`.
* `TauCeti.CStarAlgebra.IsHereditaryCone` and `TauCeti.CStarAlgebra.leftIdealOfCone`: hereditary
  positive cones and their associated left ideals `{x | star x * x ∈ C}`.
* `NonUnitalStarSubalgebra.leftIdeal`, `NonUnitalStarSubalgebra.symmetricCore_leftIdeal`,
  `Submodule.leftIdeal_symmetricCore`, and `TauCeti.CStarAlgebra.hereditaryOrderIsoLeftIdeal`,
  `TauCeti.CStarAlgebra.hereditaryOrderIsoCone`, `TauCeti.CStarAlgebra.leftIdealOrderIsoCone`:
  the Blackadar II.5.3.2 correspondences.
* `NonUnitalStarSubalgebra.exists_mul_eq_of_mem_leftIdeal`,
  `NonUnitalStarSubalgebra.mem_leftIdeal_iff_exists_mul`, and
  `Submodule.exists_mul_eq_of_isLeftIdeal`: Cohen–Hewitt factorization (Blackadar II.5.3.7).

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.5.3.2, II.5.3.7.
* Gerard J. Murphy, *C*-Algebras and Operator Theory*, Section 3.2.
-/

public section

open Filter Topology
open scoped CStarAlgebra

/-! ### Left ideals and symmetric cores -/

namespace Submodule

section LeftIdeal

variable {R A : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

/-- A submodule `L` of a possibly nonunital algebra `A` is a *left ideal* if it is closed under
left multiplication by all elements of `A`. -/
def IsLeftIdeal (L : Submodule R A) : Prop :=
  ∀ a : A, ∀ ⦃x : A⦄, x ∈ L → a * x ∈ L

theorem isLeftIdeal_iff {L : Submodule R A} :
    L.IsLeftIdeal ↔ ∀ a : A, ∀ ⦃x : A⦄, x ∈ L → a * x ∈ L :=
  Iff.rfl

/-- Elimination rule for left ideals: if `L` is a left ideal and `x ∈ L`, then `a * x ∈ L`. -/
theorem IsLeftIdeal.mul_mem_left {L : Submodule R A} (hL : L.IsLeftIdeal) (a : A) {x : A}
    (hx : x ∈ L) : a * x ∈ L :=
  hL a hx

end LeftIdeal

section SymmetricCore

variable {R A : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
  [Module R A] [StarModule R A]

/-- The symmetric core `L ∩ L⋆` of a left ideal `L` in a `⋆`-algebra, as a nonunital
`⋆`-subalgebra. -/
def symmetricCore (L : Submodule R A) (hL : L.IsLeftIdeal) : NonUnitalStarSubalgebra R A where
  carrier := {x : A | x ∈ L ∧ star x ∈ L}
  zero_mem' := ⟨L.zero_mem, by rw [star_zero]; exact L.zero_mem⟩
  add_mem' := fun {x y} hx hy =>
    ⟨L.add_mem hx.1 hy.1, by rw [star_add]; exact L.add_mem hx.2 hy.2⟩
  mul_mem' := fun {x y} hx hy =>
    ⟨hL x hy.1, by rw [star_mul]; exact hL (star y) hx.2⟩
  smul_mem' := fun c {x} hx =>
    ⟨L.smul_mem c hx.1, by rw [star_smul]; exact L.smul_mem (star c) hx.2⟩
  star_mem' := fun {x} hx => ⟨hx.2, by rw [star_star]; exact hx.1⟩

@[simp]
theorem mem_symmetricCore {L : Submodule R A} (hL : L.IsLeftIdeal) {x : A} :
    x ∈ L.symmetricCore hL ↔ x ∈ L ∧ star x ∈ L := by
  rfl

@[simp]
theorem coe_symmetricCore (L : Submodule R A) (hL : L.IsLeftIdeal) :
    (L.symmetricCore hL : Set A) = (L : Set A) ∩ star ⁻¹' (L : Set A) := by
  rfl

theorem symmetricCore_mono {L₁ L₂ : Submodule R A} (h₁ : L₁.IsLeftIdeal) (h₂ : L₂.IsLeftIdeal)
    (h : L₁ ≤ L₂) : L₁.symmetricCore h₁ ≤ L₂.symmetricCore h₂ :=
  fun _ hx => ⟨h hx.1, h hx.2⟩

/-- A nonnegative element belongs to the symmetric core `L ∩ L⋆` if and only if it belongs to `L`.
-/
theorem mem_symmetricCore_of_nonneg [PartialOrder A] [StarOrderedRing A]
    {L : Submodule R A} (hL : L.IsLeftIdeal) {a : A} (ha : 0 ≤ a) :
    a ∈ L.symmetricCore hL ↔ a ∈ L := by
  rw [mem_symmetricCore, (IsSelfAdjoint.of_nonneg ha).star_eq, and_self]

/-- The symmetric core of a closed left ideal is closed. -/
theorem isClosed_symmetricCore [TopologicalSpace A] [ContinuousStar A]
    {L : Submodule R A} (hL : L.IsLeftIdeal) (hL_closed : IsClosed (L : Set A)) :
    IsClosed (L.symmetricCore hL : Set A) := by
  rw [coe_symmetricCore]
  exact hL_closed.inter (hL_closed.preimage continuous_star)

end SymmetricCore

section SymmetricCoreCStar

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The symmetric core `L ∩ L⋆` of a closed left ideal `L` in a C⋆-algebra is a hereditary
C⋆-subalgebra. -/
theorem isHereditary_symmetricCore {L : Submodule ℂ A} (hL : L.IsLeftIdeal)
    (hL_closed : IsClosed (L : Set A)) : (L.symmetricCore hL).IsHereditary := by
  have : IsClosed (L.symmetricCore hL : Set A) := isClosed_symmetricCore hL hL_closed
  rw [NonUnitalStarSubalgebra.isHereditary_iff_mul_mul_mem]
  intro b₁ b₂ hb₁ hb₂ x
  refine ⟨hL (b₁ * x) hb₂.1, ?_⟩
  rw [star_mul, star_mul, ← mul_assoc]
  exact hL (star b₂ * star x) hb₁.2

end SymmetricCoreCStar

end Submodule

/-! ### Hereditary positive cones and associated left ideals -/

namespace TauCeti

namespace CStarAlgebra

section ConeDef

variable {A : Type*} [AddCommMonoid A] [SMul ℝ A] [LE A]

/-- A *hereditary cone* in an ordered real cone is a set `C` of nonnegative elements containing `0`,
closed under addition and nonnegative real scalar multiplication, and downward closed among
nonnegative elements. -/
structure IsHereditaryCone (C : Set A) : Prop where
  /-- Every element of a hereditary cone is nonnegative. -/
  nonneg : ∀ ⦃a : A⦄, a ∈ C → 0 ≤ a
  /-- A hereditary cone contains `0`. -/
  zero_mem : (0 : A) ∈ C
  /-- A hereditary cone is closed under addition. -/
  add_mem : ∀ ⦃a b : A⦄, a ∈ C → b ∈ C → a + b ∈ C
  /-- A hereditary cone is closed under nonnegative real scalar multiplication. -/
  smul_mem : ∀ ⦃r : ℝ⦄, 0 ≤ r → ∀ ⦃a : A⦄, a ∈ C → r • a ∈ C
  /-- A hereditary cone is downward closed among nonnegative elements. -/
  hereditary : ∀ ⦃a b : A⦄, 0 ≤ a → a ≤ b → b ∈ C → a ∈ C

end ConeDef

section ConeCStar

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The positive part `{a ∈ B | 0 ≤ a}` of a hereditary nonunital `⋆`-subalgebra `B` is a
hereditary cone. -/
theorem isHereditaryCone_nonneg {B : NonUnitalStarSubalgebra ℂ A} (hB : B.IsHereditary) :
    IsHereditaryCone {a : A | a ∈ B ∧ 0 ≤ a} where
  nonneg _ ha := ha.2
  zero_mem := ⟨zero_mem B, le_rfl⟩
  add_mem _ _ ha hb := ⟨add_mem ha.1 hb.1, add_nonneg ha.2 hb.2⟩
  smul_mem _ hr _ ha :=
    ⟨by rw [← Complex.coe_smul]; exact SMulMemClass.smul_mem (_ : ℂ) ha.1, smul_nonneg hr ha.2⟩
  hereditary _ _ ha hab hb := ⟨hB.mem_of_nonneg_of_le ha hab hb.1, ha⟩

/-- The positive part `{a ∈ B | 0 ≤ a}` of a closed subalgebra `B` is closed. -/
theorem isClosed_nonneg_inter {B : NonUnitalStarSubalgebra ℂ A}
    [hB_closed : IsClosed (B : Set A)] :
    IsClosed {a : A | a ∈ B ∧ 0 ≤ a} :=
  hB_closed.inter _root_.CStarAlgebra.isClosed_nonneg

/-- The left ideal `{x : A | star x * x ∈ C}` associated to a hereditary cone `C` in a C⋆-algebra.
-/
def leftIdealOfCone (C : Set A) (hC : IsHereditaryCone C) : Submodule ℂ A where
  carrier := {x : A | star x * x ∈ C}
  zero_mem' := by simpa using hC.zero_mem
  add_mem' := fun {x y} hx hy => by
    have hpar : star (x + y) * (x + y) + star (x - y) * (x - y) =
        (2 : ℝ) • (star x * x + star y * y) := by
      simp only [star_add, star_sub, add_mul, sub_mul, mul_add, mul_sub]
      module
    have hle : star (x + y) * (x + y) ≤ (2 : ℝ) • (star x * x + star y * y) := by
      rw [← hpar]
      exact le_add_of_nonneg_right (star_mul_self_nonneg (x - y))
    exact hC.hereditary (star_mul_self_nonneg _) hle
      (hC.smul_mem (by norm_num) (hC.add_mem hx hy))
  smul_mem' := fun c x hx => by
    have heq : star (c • x) * (c • x) = (‖c‖ ^ 2 : ℝ) • (star x * x) := by
      rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.star_def,
        Complex.conj_mul', ← Complex.ofReal_pow, Complex.coe_smul]
    simp only [Set.mem_ofPred_eq, heq]
    exact hC.smul_mem (sq_nonneg ‖c‖) hx

@[simp]
theorem mem_leftIdealOfCone {C : Set A} (hC : IsHereditaryCone C) {x : A} :
    x ∈ leftIdealOfCone C hC ↔ star x * x ∈ C := by
  rfl

/-- The submodule `{x : A | star x * x ∈ C}` associated to a hereditary cone `C` is a left ideal. -/
theorem isLeftIdeal_leftIdealOfCone (C : Set A) (hC : IsHereditaryCone C) :
    (leftIdealOfCone C hC).IsLeftIdeal := by
  intro a x hx
  rw [mem_leftIdealOfCone] at hx ⊢
  have heq : star (a * x) * (a * x) = star x * (star a * a) * x := by
    simp only [star_mul, mul_assoc]
  rw [heq]
  exact hC.hereditary (star_left_conjugate_nonneg (star_mul_self_nonneg a) x)
    (_root_.CStarAlgebra.star_left_conjugate_le_norm_smul x (star a * a))
    (hC.smul_mem (norm_nonneg _) hx)

/-- If `C` is a closed hereditary cone, then `leftIdealOfCone C hC` is a closed left ideal. -/
theorem isClosed_leftIdealOfCone {C : Set A} (hC : IsHereditaryCone C) (hC_closed : IsClosed C) :
    IsClosed (leftIdealOfCone C hC : Set A) := by
  have hset : (leftIdealOfCone C hC : Set A) = (fun x : A => star x * x) ⁻¹' C := rfl
  rw [hset]
  exact hC_closed.preimage (continuous_star.mul continuous_id)

theorem leftIdealOfCone_mono {C₁ C₂ : Set A} (h₁ : IsHereditaryCone C₁) (h₂ : IsHereditaryCone C₂)
    (h : C₁ ⊆ C₂) : leftIdealOfCone C₁ h₁ ≤ leftIdealOfCone C₂ h₂ :=
  fun _ hx => h hx

end ConeCStar

end CStarAlgebra

end TauCeti

/-! ### Associated left ideal of a hereditary C⋆-subalgebra and Blackadar II.5.3.2 -/

namespace NonUnitalStarSubalgebra

section LeftIdealCStar

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The left ideal `{x : A | star x * x ∈ B}` associated to a hereditary nonunital `⋆`-subalgebra
`B` of a C⋆-algebra `A`. -/
def leftIdeal (B : NonUnitalStarSubalgebra ℂ A) (hB : B.IsHereditary) : Submodule ℂ A :=
  TauCeti.CStarAlgebra.leftIdealOfCone {a : A | a ∈ B ∧ 0 ≤ a}
    (TauCeti.CStarAlgebra.isHereditaryCone_nonneg hB)

@[simp]
theorem mem_leftIdeal {B : NonUnitalStarSubalgebra ℂ A} (hB : B.IsHereditary) {x : A} :
    x ∈ B.leftIdeal hB ↔ star x * x ∈ B := by
  rw [leftIdeal, TauCeti.CStarAlgebra.mem_leftIdealOfCone, Set.mem_ofPred_eq]
  exact and_iff_left (star_mul_self_nonneg x)

theorem isLeftIdeal_leftIdeal (B : NonUnitalStarSubalgebra ℂ A) (hB : B.IsHereditary) :
    (B.leftIdeal hB).IsLeftIdeal :=
  TauCeti.CStarAlgebra.isLeftIdeal_leftIdealOfCone _ _

theorem isClosed_leftIdeal (B : NonUnitalStarSubalgebra ℂ A) [IsClosed (B : Set A)]
    (hB : B.IsHereditary) : IsClosed (B.leftIdeal hB : Set A) :=
  TauCeti.CStarAlgebra.isClosed_leftIdealOfCone _
    (TauCeti.CStarAlgebra.isClosed_nonneg_inter (B := B))

theorem leftIdeal_mono {B₁ B₂ : NonUnitalStarSubalgebra ℂ A} (h₁ : B₁.IsHereditary)
    (h₂ : B₂.IsHereditary) (h : B₁ ≤ B₂) : B₁.leftIdeal h₁ ≤ B₂.leftIdeal h₂ :=
  fun _ hx => (mem_leftIdeal h₂).mpr (h ((mem_leftIdeal h₁).mp hx))

/-- First round-trip of Blackadar II.5.3.2: for a closed hereditary C⋆-subalgebra `B`, the
symmetric core of `B.leftIdeal hB` is `B`. -/
theorem symmetricCore_leftIdeal (B : NonUnitalStarSubalgebra ℂ A)
    [hB_closed : IsClosed (B : Set A)] (hB : B.IsHereditary) :
    (B.leftIdeal hB).symmetricCore (B.isLeftIdeal_leftIdeal hB) = B := by
  ext x
  rw [Submodule.mem_symmetricCore, mem_leftIdeal, mem_leftIdeal, star_star]
  constructor
  · rintro ⟨hx₁, hx₂⟩
    have : StarOrderedRing B := Subtype.starOrderedRing B
    have hl := CStarAlgebra.increasingApproximateUnit B
    have := hl.neBot
    have hright : Tendsto (fun e : B => x * (e : A)) (CStarAlgebra.approximateUnit B) (𝓝 x) :=
      B.tendsto_mul_approximateUnit_of_star_mul_self_le hx₁ le_rfl
    have hstar_right :
        Tendsto (fun e : B => star x * (e : A)) (CStarAlgebra.approximateUnit B) (𝓝 (star x)) :=
      B.tendsto_mul_approximateUnit_of_star_mul_self_le (by rwa [star_star]) le_rfl
    have hleft : Tendsto (fun e : B => (e : A) * x) (CStarAlgebra.approximateUnit B) (𝓝 x) := by
      have hstar := (continuous_star.tendsto (star x)).comp hstar_right
      rw [star_star] at hstar
      refine hstar.congr' (hl.eventually_nonneg.mono fun e (he : 0 ≤ (e : A)) => ?_)
      simp [star_mul, he.star_eq]
    have hboth : Tendsto (fun e : B => (e : A) * x * (e : A))
        (CStarAlgebra.approximateUnit B) (𝓝 x) := by
      rw [tendsto_iff_norm_sub_tendsto_zero] at hright hleft ⊢
      have hsum : Tendsto (fun e : B => ‖x * (e : A) - x‖ + ‖(e : A) * x - x‖)
          (CStarAlgebra.approximateUnit B) (𝓝 0) := by
        simpa using hright.add hleft
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsum
      filter_upwards [hl.eventually_norm] with e he
      have hdecomp : (e : A) * x * (e : A) - x =
          (e : A) * (x * (e : A) - x) + ((e : A) * x - x) := by
        rw [mul_sub, ← mul_assoc, sub_add_sub_cancel]
      have he_coe : ‖(e : A)‖ ≤ 1 := he
      calc
        ‖(e : A) * x * (e : A) - x‖
            ≤ ‖(e : A) * (x * (e : A) - x)‖ + ‖(e : A) * x - x‖ := by
              rw [hdecomp]; exact norm_add_le _ _
        _ ≤ ‖(e : A)‖ * ‖x * (e : A) - x‖ + ‖(e : A) * x - x‖ := by
              gcongr; exact norm_mul_le _ _
        _ ≤ 1 * ‖x * (e : A) - x‖ + ‖(e : A) * x - x‖ := by gcongr
        _ = ‖x * (e : A) - x‖ + ‖(e : A) * x - x‖ := by rw [one_mul]
    exact hB_closed.mem_of_tendsto hboth
      (Eventually.of_forall fun e => hB.mul_mul_mem e.2 e.2 x)
  · intro hx
    exact ⟨mul_mem (star_mem hx) hx, mul_mem hx (star_mem hx)⟩

end LeftIdealCStar

end NonUnitalStarSubalgebra

namespace Submodule

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Second round-trip of Blackadar II.5.3.2: for a closed left ideal `L` of a C⋆-algebra, the left
ideal associated to its symmetric core `L ∩ L⋆` is `L`. -/
theorem leftIdeal_symmetricCore {L : Submodule ℂ A} (hL : L.IsLeftIdeal)
    (hL_closed : IsClosed (L : Set A)) :
    (L.symmetricCore hL).leftIdeal (L.isHereditary_symmetricCore hL hL_closed) = L := by
  ext x
  rw [NonUnitalStarSubalgebra.mem_leftIdeal, mem_symmetricCore]
  constructor
  · intro hx
    let B := L.symmetricCore hL
    have : IsClosed (B : Set A) := isClosed_symmetricCore hL hL_closed
    have : StarOrderedRing B := Subtype.starOrderedRing B
    have := (CStarAlgebra.increasingApproximateUnit B).neBot
    have hlim : Tendsto (fun e : B => x * (e : A)) (CStarAlgebra.approximateUnit B) (𝓝 x) :=
      B.tendsto_mul_approximateUnit_of_star_mul_self_le hx le_rfl
    exact hL_closed.mem_of_tendsto hlim (Eventually.of_forall fun e => hL x e.2.1)
  · intro hx
    have hxx : star x * x ∈ L := hL (star x) hx
    refine ⟨hxx, ?_⟩
    rwa [star_mul, star_star]

end Submodule

namespace TauCeti.CStarAlgebra

section OrderIsos

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Round-trip for closed hereditary cones (Blackadar II.5.3.2): recovering `C` as the positive
part of the closed hereditary C⋆-subalgebra `L_C ∩ L_C⋆`. -/
theorem nonneg_symmetricCore_leftIdealOfCone {C : Set A} (hC : IsHereditaryCone C)
    (hC_closed : IsClosed C) :
    {a : A | a ∈ (leftIdealOfCone C hC).symmetricCore (isLeftIdeal_leftIdealOfCone C hC) ∧
      0 ≤ a} = C := by
  ext a
  constructor
  · rintro ⟨haB, ha0⟩
    let B := (leftIdealOfCone C hC).symmetricCore (isLeftIdeal_leftIdealOfCone C hC)
    have : IsClosed (B : Set A) :=
      Submodule.isClosed_symmetricCore _ (isClosed_leftIdealOfCone hC hC_closed)
    have hsqrt_mem : CFC.sqrt a ∈ B := by
      rw [CFC.sqrt, cfcₙ_nnreal_eq_real NNReal.sqrt a ha0]
      exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) _ haB
    have hsq : star (CFC.sqrt a) * CFC.sqrt a = a := by
      rw [(CFC.sqrt_nonneg a).star_eq]
      exact CFC.sqrt_mul_sqrt_self a ha0
    exact hsq ▸ hsqrt_mem.1
  · intro haC
    have ha0 : 0 ≤ a := hC.nonneg haC
    have ha_sq_le : a * a ≤ ‖a‖ • a := by
      have hs :=
        _root_.CStarAlgebra.star_left_conjugate_le_norm_smul (CFC.sqrt a) a ha0.isSelfAdjoint
      have hsqrt : CFC.sqrt a * CFC.sqrt a = a := CFC.sqrt_mul_sqrt_self a ha0
      rw [(CFC.sqrt_nonneg a).star_eq, hsqrt] at hs
      have hlhs : CFC.sqrt a * a * CFC.sqrt a = a * a := by
        calc
          CFC.sqrt a * a * CFC.sqrt a = CFC.sqrt a * (CFC.sqrt a * CFC.sqrt a) * CFC.sqrt a := by
            rw [hsqrt]
          _ = (CFC.sqrt a * CFC.sqrt a) * (CFC.sqrt a * CFC.sqrt a) := by simp only [mul_assoc]
          _ = a * a := by rw [hsqrt]
      rwa [hlhs] at hs
    have haa : star a * a ∈ C := by
      have ha_sq_nonneg : 0 ≤ a * a := by
        simpa [ha0.star_eq] using star_mul_self_nonneg a
      rw [ha0.star_eq]
      exact hC.hereditary ha_sq_nonneg ha_sq_le (hC.smul_mem (norm_nonneg a) haC)
    refine ⟨⟨haa, ?_⟩, ha0⟩
    rwa [ha0.star_eq]

/-- Order isomorphism between closed hereditary C⋆-subalgebras and closed left ideals of a
C⋆-algebra (Blackadar II.5.3.2). -/
def hereditaryOrderIsoLeftIdeal (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] :
    {B : NonUnitalStarSubalgebra ℂ A // IsClosed (B : Set A) ∧ B.IsHereditary} ≃o
      {L : Submodule ℂ A // IsClosed (L : Set A) ∧ L.IsLeftIdeal} where
  toFun B :=
    haveI := B.2.1
    ⟨B.1.leftIdeal B.2.2, B.1.isClosed_leftIdeal B.2.2, B.1.isLeftIdeal_leftIdeal B.2.2⟩
  invFun L :=
    ⟨L.1.symmetricCore L.2.2, Submodule.isClosed_symmetricCore L.2.2 L.2.1,
      Submodule.isHereditary_symmetricCore L.2.2 L.2.1⟩
  left_inv B := Subtype.ext <| by
    have := B.2.1
    exact B.1.symmetricCore_leftIdeal B.2.2
  right_inv L := Subtype.ext <| Submodule.leftIdeal_symmetricCore L.2.2 L.2.1
  map_rel_iff' := by
    intro B₁ B₂
    have := B₁.2.1
    have := B₂.2.1
    constructor
    · intro h
      have hsym := Submodule.symmetricCore_mono (B₁.1.isLeftIdeal_leftIdeal B₁.2.2)
        (B₂.1.isLeftIdeal_leftIdeal B₂.2.2) h
      rwa [B₁.1.symmetricCore_leftIdeal B₁.2.2, B₂.1.symmetricCore_leftIdeal B₂.2.2] at hsym
    · intro h
      exact NonUnitalStarSubalgebra.leftIdeal_mono B₁.2.2 B₂.2.2 h

@[simp]
theorem hereditaryOrderIsoLeftIdeal_apply
    (B : {B : NonUnitalStarSubalgebra ℂ A // IsClosed (B : Set A) ∧ B.IsHereditary}) :
    (hereditaryOrderIsoLeftIdeal A B : Submodule ℂ A) = B.1.leftIdeal B.2.2 := by
  rfl

@[simp]
theorem hereditaryOrderIsoLeftIdeal_symm_apply
    (L : {L : Submodule ℂ A // IsClosed (L : Set A) ∧ L.IsLeftIdeal}) :
    ((hereditaryOrderIsoLeftIdeal A).symm L : NonUnitalStarSubalgebra ℂ A) =
      L.1.symmetricCore L.2.2 := by
  rfl

/-- Order isomorphism between closed hereditary C⋆-subalgebras and closed hereditary positive cones
of a C⋆-algebra (Blackadar II.5.3.2). -/
def hereditaryOrderIsoCone (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] :
    {B : NonUnitalStarSubalgebra ℂ A // IsClosed (B : Set A) ∧ B.IsHereditary} ≃o
      {C : Set A // IsClosed C ∧ IsHereditaryCone C} where
  toFun B :=
    haveI := B.2.1
    ⟨{a : A | a ∈ B.1 ∧ 0 ≤ a}, isClosed_nonneg_inter (B := B.1), isHereditaryCone_nonneg B.2.2⟩
  invFun C :=
    ⟨(leftIdealOfCone C.1 C.2.2).symmetricCore (isLeftIdeal_leftIdealOfCone C.1 C.2.2),
      Submodule.isClosed_symmetricCore _ (isClosed_leftIdealOfCone C.2.2 C.2.1),
      Submodule.isHereditary_symmetricCore _ (isClosed_leftIdealOfCone C.2.2 C.2.1)⟩
  left_inv B := Subtype.ext <| by
    have := B.2.1
    exact B.1.symmetricCore_leftIdeal B.2.2
  right_inv C := Subtype.ext <| nonneg_symmetricCore_leftIdealOfCone C.2.2 C.2.1
  map_rel_iff' := by
    intro B₁ B₂
    have := B₁.2.1
    have := B₂.2.1
    constructor
    · intro h
      have hL := leftIdealOfCone_mono (isHereditaryCone_nonneg B₁.2.2)
        (isHereditaryCone_nonneg B₂.2.2) h
      have hsym := Submodule.symmetricCore_mono (B₁.1.isLeftIdeal_leftIdeal B₁.2.2)
        (B₂.1.isLeftIdeal_leftIdeal B₂.2.2) hL
      rwa [B₁.1.symmetricCore_leftIdeal B₁.2.2, B₂.1.symmetricCore_leftIdeal B₂.2.2] at hsym
    · intro h a ha
      exact ⟨h ha.1, ha.2⟩

@[simp]
theorem hereditaryOrderIsoCone_apply
    (B : {B : NonUnitalStarSubalgebra ℂ A // IsClosed (B : Set A) ∧ B.IsHereditary}) :
    (hereditaryOrderIsoCone A B : Set A) = {a : A | a ∈ B.1 ∧ 0 ≤ a} := by
  rfl

@[simp]
theorem hereditaryOrderIsoCone_symm_apply
    (C : {C : Set A // IsClosed C ∧ IsHereditaryCone C}) :
    ((hereditaryOrderIsoCone A).symm C : NonUnitalStarSubalgebra ℂ A) =
      (leftIdealOfCone C.1 C.2.2).symmetricCore (isLeftIdeal_leftIdealOfCone C.1 C.2.2) := by
  rfl

/-- Order isomorphism between closed left ideals and closed hereditary positive cones of a
C⋆-algebra (Blackadar II.5.3.2). -/
def leftIdealOrderIsoCone (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] :
    {L : Submodule ℂ A // IsClosed (L : Set A) ∧ L.IsLeftIdeal} ≃o
      {C : Set A // IsClosed C ∧ IsHereditaryCone C} where
  toFun L :=
    ⟨{a : A | a ∈ L.1 ∧ 0 ≤ a}, L.2.1.inter _root_.CStarAlgebra.isClosed_nonneg, by
      have hset : {a : A | a ∈ L.1 ∧ 0 ≤ a} = {a : A | a ∈ L.1.symmetricCore L.2.2 ∧ 0 ≤ a} :=
        Set.ext fun a => and_congr_left fun ha => (L.1.mem_symmetricCore_of_nonneg L.2.2 ha).symm
      rw [hset]
      exact isHereditaryCone_nonneg (Submodule.isHereditary_symmetricCore L.2.2 L.2.1)⟩
  invFun C :=
    ⟨leftIdealOfCone C.1 C.2.2, isClosed_leftIdealOfCone C.2.2 C.2.1,
      isLeftIdeal_leftIdealOfCone C.1 C.2.2⟩
  left_inv L := Subtype.ext <| by
    have hL' := Submodule.leftIdeal_symmetricCore L.2.2 L.2.1
    ext x
    dsimp only
    rw [mem_leftIdealOfCone, Set.mem_ofPred_eq, and_iff_left (star_mul_self_nonneg x),
      ← L.1.mem_symmetricCore_of_nonneg L.2.2 (star_mul_self_nonneg x),
      ← NonUnitalStarSubalgebra.mem_leftIdeal (Submodule.isHereditary_symmetricCore L.2.2 L.2.1),
      hL']
  right_inv C := Subtype.ext <| by
    dsimp only
    have hset : {a : A | a ∈ leftIdealOfCone C.1 C.2.2 ∧ 0 ≤ a} =
        {a : A | a ∈ (leftIdealOfCone C.1 C.2.2).symmetricCore
          (isLeftIdeal_leftIdealOfCone C.1 C.2.2) ∧ 0 ≤ a} :=
      Set.ext fun a => and_congr_left fun ha =>
        ((leftIdealOfCone C.1 C.2.2).mem_symmetricCore_of_nonneg
          (isLeftIdeal_leftIdealOfCone C.1 C.2.2) ha).symm
    rw [hset]
    exact nonneg_symmetricCore_leftIdealOfCone C.2.2 C.2.1
  map_rel_iff' := by
    intro L₁ L₂
    constructor
    · intro h x hx
      have hx₁ : star x * x ∈ {a : A | a ∈ L₁.1 ∧ 0 ≤ a} :=
        ⟨L₁.2.2 (star x) hx, star_mul_self_nonneg x⟩
      have hx₂ : star x * x ∈ L₂.1 := (h hx₁).1
      rw [← Submodule.leftIdeal_symmetricCore L₂.2.2 L₂.2.1,
        NonUnitalStarSubalgebra.mem_leftIdeal, Submodule.mem_symmetricCore]
      exact ⟨hx₂, by rwa [star_mul, star_star]⟩
    · intro h a ha
      exact ⟨h ha.1, ha.2⟩

@[simp]
theorem leftIdealOrderIsoCone_apply
    (L : {L : Submodule ℂ A // IsClosed (L : Set A) ∧ L.IsLeftIdeal}) :
    (leftIdealOrderIsoCone A L : Set A) = {a : A | a ∈ L.1 ∧ 0 ≤ a} := by
  rfl

@[simp]
theorem leftIdealOrderIsoCone_symm_apply
    (C : {C : Set A // IsClosed C ∧ IsHereditaryCone C}) :
    ((leftIdealOrderIsoCone A).symm C : Submodule ℂ A) = leftIdealOfCone C.1 C.2.2 := by
  rfl

end OrderIsos

end TauCeti.CStarAlgebra

/-! ### Cohen–Hewitt factorization for closed left ideals (Blackadar II.5.3.7) -/

namespace NonUnitalStarSubalgebra

section CohenHewitt

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Cohen–Hewitt factorization for left ideals of a C⋆-algebra** (Blackadar II.5.3.7): if `B` is
a closed hereditary C⋆-subalgebra and `x ∈ B.leftIdeal hB`, then for every `ε > 0` there exist
`a ∈ B.leftIdeal hB` and `b ∈ B` with `‖b‖ ≤ 1`, `‖a - x‖ < ε`, and `a * b = x`. -/
theorem exists_mul_eq_of_mem_leftIdeal {B : NonUnitalStarSubalgebra ℂ A}
    [hB_closed : IsClosed (B : Set A)] (hB : B.IsHereditary) {x : A} (hx : x ∈ B.leftIdeal hB)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ B.leftIdeal hB, ∃ b ∈ B, ‖b‖ ≤ 1 ∧ ‖a - x‖ < ε ∧ a * b = x := by
  have : StarOrderedRing B := Subtype.starOrderedRing B
  have hl := CStarAlgebra.increasingApproximateUnit B
  have := hl.neBot
  let ι : B →L[ℂ] A :=
    LinearMap.mkContinuous
      { toFun := fun b => (b : A)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      1 (fun b => by simp)
  let L : B →L[ℂ] A →L[ℂ] A := (ContinuousLinearMap.mul ℂ A).comp ι
  have hL_apply : ∀ (b : B) (z : A), L b z = (b : A) * z := fun _ _ => rfl
  have hL : ∀ b₁ b₂ z, L (b₁ * b₂) z = L b₁ (L b₂ z) := fun b₁ b₂ z => by
    simp only [hL_apply, MulMemClass.coe_mul, mul_assoc]
  have hright : Tendsto (fun e : B => x * (e : A)) (CStarAlgebra.approximateUnit B) (𝓝 x) :=
    B.tendsto_mul_approximateUnit_of_star_mul_self_le ((mem_leftIdeal hB).mp hx) le_rfl
  have hlim :
      Tendsto (fun e : B => L e (star x)) (CStarAlgebra.approximateUnit B) (𝓝 (star x)) := by
    have hstar := (continuous_star.tendsto x).comp hright
    refine hstar.congr' (hl.eventually_nonneg.mono fun e (he : 0 ≤ (e : A)) => ?_)
    simp [hL_apply, star_mul, he.star_eq]
  have hmem := (ContinuousLinearMap.tendsto_apply_iff_mem_topologicalClosure_span
    L hL hl.eventually_norm hl.tendsto_mul_right).mp hlim
  obtain ⟨b₀, y, hb₀, hy_cl, hy_dist, hfac⟩ :=
    ContinuousLinearMap.exists_apply_eq_of_mem_topologicalClosure_span
      L hL hl.eventually_norm hl.tendsto_mul_right hmem hε
  refine ⟨star y, ?_, star (b₀ : A), star_mem b₀.2, ?_, ?_, ?_⟩
  · -- `star y ∈ B.leftIdeal hB` since `y ∈ closure (B * star x)` and `B.leftIdeal hB` is closed.
    have hclosed : IsClosed (B.leftIdeal hB : Set A) := B.isClosed_leftIdeal hB
    rw [← SetLike.mem_coe, ← hclosed.closure_eq]
    refine map_mem_closure (f := star) continuous_star hy_cl ?_
    rintro _ ⟨u, rfl⟩
    rw [SetLike.mem_coe, mem_leftIdeal]
    have hrew : star (star (L u (star x))) * star (L u (star x)) =
        (u : A) * (star x * x) * star (u : A) := by
      simp only [hL_apply, star_star, star_mul, mul_assoc]
    rw [hrew]
    exact mul_mem (mul_mem u.2 ((mem_leftIdeal hB).mp hx)) (star_mem u.2)
  · simpa using hb₀
  · have hrew : star y - x = star (y - star x) := by rw [star_sub, star_star]
    rwa [hrew, norm_star]
  · rw [← star_mul, ← hL_apply, hfac, star_star]

/-- Characterization of the left ideal associated to a closed hereditary C⋆-subalgebra `B`
(Blackadar II.5.3.7): `star x * x ∈ B` if and only if `x = a * b` for some `a ∈ A` and `b ∈ B`. -/
theorem mem_leftIdeal_iff_exists_mul {B : NonUnitalStarSubalgebra ℂ A}
    [IsClosed (B : Set A)] (hB : B.IsHereditary) {x : A} :
    x ∈ B.leftIdeal hB ↔ ∃ a : A, ∃ b ∈ B, a * b = x := by
  constructor
  · intro hx
    obtain ⟨a, _, b, hb, _, _, hab⟩ := exists_mul_eq_of_mem_leftIdeal hB hx one_pos
    exact ⟨a, b, hb, hab⟩
  · rintro ⟨a, b, hb, rfl⟩
    rw [mem_leftIdeal]
    have heq : star (a * b) * (a * b) = star b * (star a * a) * b := by
      simp only [star_mul, mul_assoc]
    rw [heq]
    exact hB.mul_mul_mem (star_mem hb) hb (star a * a)

end CohenHewitt

end NonUnitalStarSubalgebra

namespace Submodule

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Every element `x` of a closed left ideal `L` in a C⋆-algebra factors as `x = a * b` with
`a ∈ L`, `b ∈ L ∩ L⋆`, `‖b‖ ≤ 1`, and `‖a - x‖ < ε` (Blackadar II.5.3.7). -/
theorem exists_mul_eq_of_isLeftIdeal {L : Submodule ℂ A} (hL : L.IsLeftIdeal)
    (hL_closed : IsClosed (L : Set A)) {x : A} (hx : x ∈ L) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ L, ∃ b ∈ L.symmetricCore hL, ‖b‖ ≤ 1 ∧ ‖a - x‖ < ε ∧ a * b = x := by
  have : IsClosed (L.symmetricCore hL : Set A) := isClosed_symmetricCore hL hL_closed
  have hEq := L.leftIdeal_symmetricCore hL hL_closed
  have hx' : x ∈ (L.symmetricCore hL).leftIdeal (L.isHereditary_symmetricCore hL hL_closed) :=
    hEq.symm ▸ hx
  obtain ⟨a, ha, b, hb, hb_norm, hdist, hab⟩ :=
    NonUnitalStarSubalgebra.exists_mul_eq_of_mem_leftIdeal
      (L.isHereditary_symmetricCore hL hL_closed) hx' hε
  exact ⟨a, hEq ▸ ha, b, hb, hb_norm, hdist, hab⟩

end Submodule
