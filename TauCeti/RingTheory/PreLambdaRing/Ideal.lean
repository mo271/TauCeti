/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.PreLambdaRing.Hom

/-!
# `λ`-subrings, `λ`-ideals, and quotient pre-`λ`-rings

This file develops the subobject and quotient theory of pre-`λ`-rings:

* **`λ`-subrings** (`Subring.IsLambdaSubring`): subrings `S ≤ R` closed under every `λ^n`
  (equivalently `λ^n` for `n ≥ 2`). Such a subring inherits a unique `PreLambdaRing` structure
  making `S.subtype : S →+* R` a pre-`λ` morphism (`Subring.preLambdaRing_unique`), and ranges and
  equalizers of pre-`λ` morphisms are `λ`-subrings.
* **`λ`-ideals** (`Ideal.IsLambdaIdeal`): ideals `I` of `R` closed under `λ^n` for all `n ≥ 1`.
  Stability begins at `n = 1` because `λ^0(0) = 1` lies outside every proper ideal
  (`Ideal.not_forall_lambdaOp_mem_of_ne_top`). The zero and whole ideals, intersections, preimages,
  and kernels of pre-`λ` morphisms are `λ`-ideals.
* **Quotient pre-`λ`-rings** (`Ideal.Quotient.instPreLambdaRing`): when `I` is a `λ`-ideal,
  `R ⧸ I` carries a unique `PreLambdaRing` structure making `Ideal.Quotient.mk I` a pre-`λ`
  morphism (`Ideal.Quotient.preLambdaRing_unique`), with universal property
  `Ideal.Quotient.liftPreLambdaEquiv`. Conversely, `R ⧸ I` admits such a structure if and only if
  `I` is a `λ`-ideal (`Ideal.isLambdaIdeal_iff_exists_preLambdaRing_quotient`).

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, §II.4.1–4.1.1 (p. 90).
-/

public section

noncomputable section

open Finset

/-! ### `λ`-subrings -/

namespace Subring

section LambdaSubring

variable {R A : Type*} [CommRing R] [TauCeti.PreLambdaRing R]
  [CommRing A] [TauCeti.PreLambdaRing A]

/-- A subring `S` of a pre-`λ`-ring `R` is a **`λ`-subring** if it is closed under `lambdaOp n`
for all `n : ℕ`. -/
class IsLambdaSubring (S : Subring R) : Prop where
  /-- Closure under all `λ`-operations. -/
  lambdaOp_mem' : ∀ ⦃n : ℕ⦄ ⦃x : R⦄, x ∈ S → TauCeti.lambdaOp n x ∈ S

theorem isLambdaSubring_iff {S : Subring R} :
    S.IsLambdaSubring ↔ ∀ ⦃n : ℕ⦄ ⦃x : R⦄, x ∈ S → TauCeti.lambdaOp n x ∈ S :=
  ⟨fun h ↦ h.lambdaOp_mem', fun h ↦ ⟨h⟩⟩

theorem lambdaOp_mem (S : Subring R) [hS : S.IsLambdaSubring] (n : ℕ) {x : R} (hx : x ∈ S) :
    TauCeti.lambdaOp n x ∈ S :=
  hS.lambdaOp_mem' hx

/-- Since a subring contains `1 = λ^0(x)` and `x = λ^1(x)`, stability under `λ^n` for `n ≥ 2`
suffices for `IsLambdaSubring`. -/
theorem isLambdaSubring_iff_two_le {S : Subring R} :
    S.IsLambdaSubring ↔ ∀ ⦃n : ℕ⦄, 2 ≤ n → ∀ ⦃x : R⦄, x ∈ S → TauCeti.lambdaOp n x ∈ S := by
  rw [isLambdaSubring_iff]
  refine ⟨fun h n _ x hx ↦ h hx, fun h n x hx ↦ ?_⟩
  match n with
  | 0 => simp [S.one_mem]
  | 1 => simp [hx]
  | n + 2 => exact h (Nat.le_add_left 2 n) hx

instance instIsLambdaSubringTop : (⊤ : Subring R).IsLambdaSubring :=
  ⟨fun _ _ _ ↦ mem_top _⟩

instance instIsLambdaSubringInf (S T : Subring R) [S.IsLambdaSubring] [T.IsLambdaSubring] :
    (S ⊓ T).IsLambdaSubring :=
  ⟨fun n _ hx ↦ ⟨S.lambdaOp_mem n hx.1, T.lambdaOp_mem n hx.2⟩⟩

instance instIsLambdaSubringIInf {ι : Type*} (S : ι → Subring R) [∀ i, (S i).IsLambdaSubring] :
    (⨅ i, S i).IsLambdaSubring :=
  ⟨fun n _ hx ↦ mem_iInf.mpr fun i ↦ (S i).lambdaOp_mem n (mem_iInf.mp hx i)⟩

theorem IsLambdaSubring.comap {F : Type*} [FunLike F R A] [RingHomClass F R A]
    [TauCeti.PreLambdaHomClass F R A] (f : F) (S : Subring A) [S.IsLambdaSubring] :
    (S.comap (f : R →+* A)).IsLambdaSubring :=
  ⟨fun n x hx ↦ by
    rw [mem_comap, RingHom.coe_coe, TauCeti.map_lambdaOp]
    exact S.lambdaOp_mem n hx⟩

theorem IsLambdaSubring.map {F : Type*} [FunLike F R A] [RingHomClass F R A]
    [TauCeti.PreLambdaHomClass F R A] (f : F) (S : Subring R) [S.IsLambdaSubring] :
    (S.map (f : R →+* A)).IsLambdaSubring :=
  ⟨fun n _ hx ↦ by
    rcases mem_map.mp hx with ⟨x, hxS, rfl⟩
    exact mem_map.mpr ⟨TauCeti.lambdaOp n x, S.lambdaOp_mem n hxS, by simp⟩⟩

instance instPreLambdaRing (S : Subring R) [S.IsLambdaSubring] : TauCeti.PreLambdaRing S where
  lambdaOp n x := ⟨TauCeti.lambdaOp n x.1, S.lambdaOp_mem n x.2⟩
  lambdaOp_zero x := Subtype.ext (TauCeti.lambdaOp_zero x.1)
  lambdaOp_one x := Subtype.ext (TauCeti.lambdaOp_one x.1)
  lambdaOp_add n x y := by
    apply S.subtype_injective
    simp [TauCeti.lambdaOp_add]

@[simp, norm_cast]
theorem coe_lambdaOp (S : Subring R) [S.IsLambdaSubring] (n : ℕ) (x : S) :
    ((TauCeti.lambdaOp n x : S) : R) = TauCeti.lambdaOp n (x : R) :=
  (rfl)

theorem isPreLambdaHom_subtype (S : Subring R) [S.IsLambdaSubring] :
    S.subtype.IsPreLambdaHom :=
  RingHom.IsPreLambdaHom.mk fun _ _ ↦ rfl

/-- The inclusion `S → R` of a `λ`-subring as a bundled `PreLambdaRingHom`. -/
def subtypePreLambda (S : Subring R) [S.IsLambdaSubring] : TauCeti.PreLambdaRingHom S R :=
  TauCeti.PreLambdaRingHom.ofIsPreLambdaHom S.subtype S.isPreLambdaHom_subtype

@[simp]
theorem coe_subtypePreLambda (S : Subring R) [S.IsLambdaSubring] (x : S) :
    S.subtypePreLambda x = (x : R) := by
  simp [subtypePreLambda]

/-- The restricted `PreLambdaRing` structure on a `λ`-subring `S` is the unique `PreLambdaRing`
structure on `S` making `S.subtype` a pre-`λ` morphism. -/
theorem preLambdaRing_unique (S : Subring R) [S.IsLambdaSubring] (l : TauCeti.PreLambdaRing S)
    (hl : @RingHom.IsPreLambdaHom S R _ l _ _ S.subtype) :
    l = S.instPreLambdaRing :=
  TauCeti.PreLambdaRing.eq_of_injective_isPreLambdaHom S.subtype_injective hl
    S.isPreLambdaHom_subtype

/-- `S` is a `λ`-subring of `R` if and only if `S` admits a `PreLambdaRing` structure making
`S.subtype : S →+* R` a pre-`λ` morphism. -/
theorem isLambdaSubring_iff_exists_preLambdaRing {S : Subring R} :
    S.IsLambdaSubring ↔
      ∃ l : TauCeti.PreLambdaRing S, @RingHom.IsPreLambdaHom S R _ l _ _ S.subtype := by
  refine ⟨fun _ ↦ ⟨S.instPreLambdaRing, S.isPreLambdaHom_subtype⟩, ?_⟩
  rintro ⟨l, hl⟩
  refine ⟨fun n x hx ↦ ?_⟩
  have h := @RingHom.IsPreLambdaHom.apply S R _ l _ _ S.subtype hl n ⟨x, hx⟩
  simpa using h ▸ (@TauCeti.lambdaOp S _ l n ⟨x, hx⟩).2

end LambdaSubring

end Subring

namespace TauCeti.PreLambdaRingHom

section SubringOps

variable {R S T : Type*} [CommRing R] [PreLambdaRing R] [CommRing S] [PreLambdaRing S]
  [CommRing T] [PreLambdaRing T]

/-- Range of a `PreLambdaRingHom` as a subring of the codomain. -/
def range (f : PreLambdaRingHom R S) : Subring S :=
  f.toRingHom.range

@[simp]
theorem mem_range {f : PreLambdaRingHom R S} {y : S} :
    y ∈ f.range ↔ ∃ x : R, f x = y :=
  RingHom.mem_range

instance instIsLambdaSubringRange (f : PreLambdaRingHom R S) : f.range.IsLambdaSubring :=
  ⟨fun n _ hx ↦ by
    rcases mem_range.mp hx with ⟨x, rfl⟩
    exact mem_range.mpr ⟨lambdaOp n x, map_lambdaOp f n x⟩⟩

/-- Equalizer subring of two `PreLambdaRingHom`s. -/
def eqLocus (f g : PreLambdaRingHom R S) : Subring R :=
  f.toRingHom.eqLocus g.toRingHom

@[simp]
theorem mem_eqLocus {f g : PreLambdaRingHom R S} {x : R} :
    x ∈ f.eqLocus g ↔ f x = g x :=
  (Iff.rfl)

instance instIsLambdaSubringEqLocus (f g : PreLambdaRingHom R S) :
    (f.eqLocus g).IsLambdaSubring :=
  ⟨fun n x hx ↦ by
    have hfg : f x = g x := mem_eqLocus.mp hx
    exact mem_eqLocus.mpr (by rw [map_lambdaOp, map_lambdaOp, hfg])⟩

/-- Restrict the codomain of a `PreLambdaRingHom` to a `λ`-subring containing its image. -/
def codRestrict (f : PreLambdaRingHom T R) (S : Subring R) [S.IsLambdaSubring]
    (h : ∀ x, f x ∈ S) : PreLambdaRingHom T S :=
  ofIsPreLambdaHom (f.toRingHom.codRestrict S h)
    (RingHom.IsPreLambdaHom.mk fun n x ↦ Subtype.ext (map_lambdaOp f n x))

@[simp, norm_cast]
theorem coe_codRestrict_apply (f : PreLambdaRingHom T R) (S : Subring R) [S.IsLambdaSubring]
    (h : ∀ x, f x ∈ S) (x : T) : ((f.codRestrict S h x : S) : R) = f x := by
  simp [codRestrict]

@[simp]
theorem subtype_comp_codRestrict (f : PreLambdaRingHom T R) (S : Subring R) [S.IsLambdaSubring]
    (h : ∀ x, f x ∈ S) : S.subtypePreLambda.comp (f.codRestrict S h) = f := by
  ext x
  simp

end SubringOps

end TauCeti.PreLambdaRingHom

/-! ### `λ`-ideals and quotient pre-`λ`-rings -/

namespace Ideal

section LambdaIdeal

variable {R S : Type*} [CommRing R] [TauCeti.PreLambdaRing R]
  [CommRing S] [TauCeti.PreLambdaRing S]

/-- An ideal `I` of a pre-`λ`-ring `R` is a **`λ`-ideal** if `λ^n(x) ∈ I` for all `x ∈ I` and all
`n ≥ 1` (Weibel, *The K-book*, Definition II.4.1.1). -/
class IsLambdaIdeal (I : Ideal R) : Prop where
  /-- Stability under positive-degree `λ`-operations (`n ≥ 1`). -/
  lambdaOp_mem' : ∀ ⦃n : ℕ⦄, 1 ≤ n → ∀ ⦃x : R⦄, x ∈ I → TauCeti.lambdaOp n x ∈ I

theorem isLambdaIdeal_iff {I : Ideal R} :
    I.IsLambdaIdeal ↔ ∀ ⦃n : ℕ⦄, 1 ≤ n → ∀ ⦃x : R⦄, x ∈ I → TauCeti.lambdaOp n x ∈ I :=
  ⟨fun h ↦ h.lambdaOp_mem', fun h ↦ ⟨h⟩⟩

theorem isLambdaIdeal_iff_ne_zero {I : Ideal R} :
    I.IsLambdaIdeal ↔ ∀ ⦃n : ℕ⦄, n ≠ 0 → ∀ ⦃x : R⦄, x ∈ I → TauCeti.lambdaOp n x ∈ I := by
  rw [isLambdaIdeal_iff]
  refine ⟨fun h n hn ↦ h (Nat.one_le_iff_ne_zero.mpr hn),
    fun h n hn ↦ h (Nat.one_le_iff_ne_zero.mp hn)⟩

theorem lambdaOp_mem (I : Ideal R) [hI : I.IsLambdaIdeal] {n : ℕ} (hn : 1 ≤ n) {x : R}
    (hx : x ∈ I) : TauCeti.lambdaOp n x ∈ I :=
  hI.lambdaOp_mem' hn hx

theorem lambdaOp_mem_of_ne_zero (I : Ideal R) [I.IsLambdaIdeal] {n : ℕ} (hn : n ≠ 0) {x : R}
    (hx : x ∈ I) : TauCeti.lambdaOp n x ∈ I :=
  I.lambdaOp_mem (Nat.one_le_iff_ne_zero.mpr hn) hx

/-- No proper ideal of `R` is closed under `λ^0`, since `0 ∈ I` and `λ^0(0) = 1 ∉ I`. Thus ideal
stability must begin at `n = 1`. -/
theorem not_forall_lambdaOp_mem_of_ne_top {I : Ideal R} (hI : I ≠ ⊤) :
    ¬ ∀ (n : ℕ) ⦃x : R⦄, x ∈ I → TauCeti.lambdaOp n x ∈ I := by
  intro h
  apply hI
  rw [eq_top_iff_one]
  simpa using h 0 I.zero_mem

instance instIsLambdaIdealBot : (⊥ : Ideal R).IsLambdaIdeal :=
  isLambdaIdeal_iff_ne_zero.mpr fun _ hn _ hx ↦ by
    rw [mem_bot.mp hx, TauCeti.PreLambdaRing.lambdaOp_zero_right_of_ne_zero hn, mem_bot]

instance instIsLambdaIdealTop : (⊤ : Ideal R).IsLambdaIdeal :=
  ⟨fun _ _ _ _ ↦ Submodule.mem_top⟩

instance instIsLambdaIdealInf (I J : Ideal R) [I.IsLambdaIdeal] [J.IsLambdaIdeal] :
    (I ⊓ J).IsLambdaIdeal :=
  ⟨fun _ hn _ hx ↦ ⟨I.lambdaOp_mem hn hx.1, J.lambdaOp_mem hn hx.2⟩⟩

instance instIsLambdaIdealIInf {ι : Type*} (I : ι → Ideal R) [∀ i, (I i).IsLambdaIdeal] :
    (⨅ i, I i).IsLambdaIdeal :=
  ⟨fun _ hn _ hx ↦ mem_iInf.mpr fun i ↦ (I i).lambdaOp_mem hn (mem_iInf.mp hx i)⟩

theorem IsLambdaIdeal.comap {F : Type*} [FunLike F R S] [RingHomClass F R S]
    [TauCeti.PreLambdaHomClass F R S] (f : F) (I : Ideal S) [I.IsLambdaIdeal] :
    (I.comap (f : R →+* S)).IsLambdaIdeal :=
  ⟨fun n hn x hx ↦ by
    rw [mem_comap, RingHom.coe_coe, TauCeti.map_lambdaOp]
    exact I.lambdaOp_mem hn hx⟩

/-- The kernel of a pre-`λ` ring homomorphism is a `λ`-ideal. -/
theorem _root_.RingHom.IsPreLambdaHom.isLambdaIdeal_ker {f : R →+* S} (hf : f.IsPreLambdaHom) :
    (RingHom.ker f).IsLambdaIdeal :=
  isLambdaIdeal_iff_ne_zero.mpr fun n hn x hx ↦ by
    rw [RingHom.mem_ker, hf.apply n x, RingHom.mem_ker.mp hx,
      TauCeti.PreLambdaRing.lambdaOp_zero_right_of_ne_zero hn]

instance instIsLambdaIdealKer {F : Type*} [FunLike F R S] [RingHomClass F R S]
    [TauCeti.PreLambdaHomClass F R S] (f : F) :
    (RingHom.ker (f : R →+* S)).IsLambdaIdeal :=
  (TauCeti.toRingHom_isPreLambdaHom f).isLambdaIdeal_ker

/-- Congruence modulo a `λ`-ideal: if `x - y ∈ I`, then `λ^n(x) - λ^n(y) ∈ I` for every `n : ℕ`. -/
theorem lambdaOp_sub_mem (I : Ideal R) [I.IsLambdaIdeal] {x y : R} (hxy : x - y ∈ I) (n : ℕ) :
    TauCeti.lambdaOp n x - TauCeti.lambdaOp n y ∈ I := by
  have hx : x = y + (x - y) := (add_sub_cancel y x).symm
  rw [hx, TauCeti.lambdaOp_add]
  have hmem : (n, 0) ∈ antidiagonal n := mem_antidiagonal.mpr (add_zero n)
  rw [← Finset.add_sum_erase _ _ hmem, TauCeti.lambdaOp_zero, mul_one, add_sub_cancel_left]
  refine Submodule.sum_mem I fun ij hij ↦ ?_
  have hij_ne : ij ≠ (n, 0) := ne_of_mem_erase hij
  have hij_sum : ij.1 + ij.2 = n := mem_antidiagonal.mp (mem_of_mem_erase hij)
  have hij2 : ij.2 ≠ 0 := by
    intro h0
    apply hij_ne
    ext <;> omega
  exact I.mul_mem_left _ (I.lambdaOp_mem_of_ne_zero hij2 hxy)

/-! ### Quotient pre-`λ`-rings -/

/-- Induced `PreLambdaRing` structure on `R ⧸ I` for a `λ`-ideal `I`. -/
instance Quotient.instPreLambdaRing (I : Ideal R) [I.IsLambdaIdeal] :
    TauCeti.PreLambdaRing (R ⧸ I) where
  lambdaOp n := _root_.Quotient.map' (TauCeti.lambdaOp n) fun _ _ h ↦
    I.quotientRel_def.mpr (I.lambdaOp_sub_mem (I.quotientRel_def.mp h) n)
  lambdaOp_zero q := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact congrArg (Ideal.Quotient.mk I) (TauCeti.lambdaOp_zero x)
  lambdaOp_one q := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact congrArg (Ideal.Quotient.mk I) (TauCeti.lambdaOp_one x)
  lambdaOp_add n p q := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective p
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hmk : ∀ m (a : R),
        _root_.Quotient.map' (TauCeti.lambdaOp m)
          (fun _ _ h ↦ I.quotientRel_def.mpr (I.lambdaOp_sub_mem (I.quotientRel_def.mp h) m))
          (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (TauCeti.lambdaOp m a) := fun _ _ ↦ rfl
    rw [← map_add, hmk, TauCeti.lambdaOp_add, map_sum]
    refine Finset.sum_congr rfl fun ij _ ↦ ?_
    rw [map_mul, hmk, hmk]

@[simp]
theorem Quotient.mk_lambdaOp (I : Ideal R) [I.IsLambdaIdeal] (n : ℕ) (x : R) :
    Ideal.Quotient.mk I (TauCeti.lambdaOp n x) = TauCeti.lambdaOp n (Ideal.Quotient.mk I x) :=
  (rfl)

theorem Quotient.isPreLambdaHom_mk (I : Ideal R) [I.IsLambdaIdeal] :
    (Ideal.Quotient.mk I).IsPreLambdaHom :=
  RingHom.IsPreLambdaHom.mk fun _ _ ↦ rfl

/-- The quotient homomorphism `R → R ⧸ I` by a `λ`-ideal as a bundled `PreLambdaRingHom`. -/
def Quotient.mkPreLambda (I : Ideal R) [I.IsLambdaIdeal] :
    TauCeti.PreLambdaRingHom R (R ⧸ I) :=
  TauCeti.PreLambdaRingHom.ofIsPreLambdaHom (Ideal.Quotient.mk I) (Quotient.isPreLambdaHom_mk I)

@[simp]
theorem Quotient.mkPreLambda_apply (I : Ideal R) [I.IsLambdaIdeal] (x : R) :
    Quotient.mkPreLambda I x = Ideal.Quotient.mk I x := by
  simp [Quotient.mkPreLambda]

/-- Descend a `PreLambdaRingHom` vanishing on a `λ`-ideal `I` to `R ⧸ I`. -/
def Quotient.liftPreLambda (I : Ideal R) [I.IsLambdaIdeal]
    (f : TauCeti.PreLambdaRingHom R S) (hf : ∀ a ∈ I, f a = 0) :
    TauCeti.PreLambdaRingHom (R ⧸ I) S :=
  TauCeti.PreLambdaRingHom.ofIsPreLambdaHom (Ideal.Quotient.lift I f.toRingHom hf)
    (RingHom.IsPreLambdaHom.mk fun n q ↦ by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [← Quotient.mk_lambdaOp, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
      exact TauCeti.map_lambdaOp f n x)

@[simp]
theorem Quotient.liftPreLambda_mk (I : Ideal R) [I.IsLambdaIdeal]
    (f : TauCeti.PreLambdaRingHom R S) (hf : ∀ a ∈ I, f a = 0) (x : R) :
    Quotient.liftPreLambda I f hf (Ideal.Quotient.mk I x) = f x := by
  simp [Quotient.liftPreLambda]

@[simp]
theorem Quotient.liftPreLambda_comp_mkPreLambda (I : Ideal R) [I.IsLambdaIdeal]
    (f : TauCeti.PreLambdaRingHom R S) (hf : ∀ a ∈ I, f a = 0) :
    (Quotient.liftPreLambda I f hf).comp (Quotient.mkPreLambda I) = f := by
  ext x
  simp

/-- Universal property of the quotient pre-`λ`-ring `R ⧸ I`. -/
def Quotient.liftPreLambdaEquiv (I : Ideal R) [I.IsLambdaIdeal] :
    { f : TauCeti.PreLambdaRingHom R S // I ≤ RingHom.ker f.toRingHom } ≃
      TauCeti.PreLambdaRingHom (R ⧸ I) S where
  toFun f := Quotient.liftPreLambda I f.1 fun a ha ↦ by
    rw [← TauCeti.PreLambdaRingHom.coe_toRingHom, ← RingHom.mem_ker]
    exact f.2 ha
  invFun g := ⟨g.comp (Quotient.mkPreLambda I), fun a ha ↦ by
    rw [RingHom.mem_ker, TauCeti.PreLambdaRingHom.coe_toRingHom,
      TauCeti.PreLambdaRingHom.comp_apply, Quotient.mkPreLambda_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]⟩
  left_inv f := Subtype.ext (Quotient.liftPreLambda_comp_mkPreLambda I f.1 _)
  right_inv g := by
    ext q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    dsimp only
    rw [Quotient.liftPreLambda_mk, TauCeti.PreLambdaRingHom.comp_apply,
      Quotient.mkPreLambda_apply]

variable (R) in
/-- Quotienting a pre-`λ`-ring by the zero `λ`-ideal `⊥` is canonically pre-`λ`-isomorphic
to `R`. -/
def quotientBotPreLambdaRingEquiv : TauCeti.PreLambdaRingEquiv (R ⧸ (⊥ : Ideal R)) R :=
  (TauCeti.PreLambdaRingEquiv.ofBijective (Quotient.mkPreLambda (⊥ : Ideal R))
    ⟨fun x y h ↦ sub_eq_zero.mp (Ideal.mem_bot.mp (Ideal.Quotient.eq.mp (by simpa using h))),
      fun q ↦ by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
        exact ⟨x, by simp⟩⟩).symm

/-- `Ideal.Quotient.instPreLambdaRing I` is the unique `PreLambdaRing` structure on `R ⧸ I` making
`Ideal.Quotient.mk I` a pre-`λ` morphism. -/
theorem Quotient.preLambdaRing_unique (I : Ideal R) [I.IsLambdaIdeal]
    (l : TauCeti.PreLambdaRing (R ⧸ I))
    (hl : @RingHom.IsPreLambdaHom R (R ⧸ I) _ _ _ l (Ideal.Quotient.mk I)) :
    l = Quotient.instPreLambdaRing I :=
  TauCeti.PreLambdaRing.eq_of_surjective_isPreLambdaHom Ideal.Quotient.mk_surjective hl
    (Quotient.isPreLambdaHom_mk I)

/-- An ideal `I` of `R` is a `λ`-ideal if and only if `R ⧸ I` admits a `PreLambdaRing` structure
making `Ideal.Quotient.mk I` a pre-`λ` morphism. -/
theorem isLambdaIdeal_iff_exists_preLambdaRing_quotient {I : Ideal R} :
    I.IsLambdaIdeal ↔
      ∃ l : TauCeti.PreLambdaRing (R ⧸ I),
        @RingHom.IsPreLambdaHom R (R ⧸ I) _ _ _ l (Ideal.Quotient.mk I) := by
  refine ⟨fun _ ↦ ⟨Quotient.instPreLambdaRing I, Quotient.isPreLambdaHom_mk I⟩, ?_⟩
  rintro ⟨l, hl⟩
  have hker := @RingHom.IsPreLambdaHom.isLambdaIdeal_ker R (R ⧸ I) _ _ _ l
    (Ideal.Quotient.mk I) hl
  rwa [Ideal.mk_ker] at hker

/-- For a `λ`-ideal `I` of `R`, the subring `{(a, c) ∈ R × R | c - a ∈ I}` is a `λ`-subring of
`R × R` (realized as the equalizer of the two projections composed with `mkPreLambda I`). -/
def pairSubring (I : Ideal R) [I.IsLambdaIdeal] : Subring (R × R) :=
  ((Quotient.mkPreLambda I).comp (TauCeti.PreLambdaRingHom.fst R R)).eqLocus
    ((Quotient.mkPreLambda I).comp (TauCeti.PreLambdaRingHom.snd R R))

@[simp]
theorem mem_pairSubring {I : Ideal R} [I.IsLambdaIdeal] {p : R × R} :
    p ∈ I.pairSubring ↔ p.2 - p.1 ∈ I := by
  rw [pairSubring, TauCeti.PreLambdaRingHom.mem_eqLocus]
  simp only [TauCeti.PreLambdaRingHom.comp_apply, TauCeti.PreLambdaRingHom.fst_apply,
    TauCeti.PreLambdaRingHom.snd_apply, Quotient.mkPreLambda_apply,
    eq_comm (a := Ideal.Quotient.mk I p.1)]
  exact Ideal.Quotient.eq

instance instIsLambdaSubringPairSubring (I : Ideal R) [I.IsLambdaIdeal] :
    I.pairSubring.IsLambdaSubring := by
  rw [pairSubring]
  infer_instance

end LambdaIdeal

end Ideal
