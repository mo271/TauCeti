/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Basic
public import TauCeti.RingTheory.PreLambdaRing.Basic

/-!
# Morphisms, equivalences, and products of pre-`λ`-rings

A **pre-`λ` morphism** between pre-`λ`-rings `R` and `S` is a ring homomorphism `f : R →+* S`
commuting with every coefficient operation `λ^n` (`f (λ^n x) = λ^n (f x)`), or equivalently
commuting with `λ^n` for `n ≥ 2`, or pushing the total series `λ_t(x)` to `λ_t(f x)` along
`PowerSeries.map f`.

This file provides:
* the unbundled predicate `RingHom.IsPreLambdaHom` on `R →+* S`;
* the morphism typeclass `TauCeti.PreLambdaHomClass` and bundled structures
  `TauCeti.PreLambdaRingHom` and `TauCeti.PreLambdaRingEquiv`, with identity, composition,
  inversion, extensionality, and constructors from `n ≥ 2` and from total series;
* uniqueness of restricted pre-`λ`-structures along injective ring homomorphisms
  (`TauCeti.PreLambdaRing.eq_of_injective_isPreLambdaHom`) and of quotient/coinduced structures
  along surjective ring homomorphisms (`TauCeti.PreLambdaRing.eq_of_surjective_isPreLambdaHom`);
* componentwise `PreLambdaRing` instances and universal properties for binary products `R × S` and
  indexed products `∀ i, R i`, plus uniqueness of `PreLambdaRing` on subsingleton rings.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, §II.4.1 (p. 90).
-/

public section

noncomputable section

open Finset PowerSeries

/-! ### Unbundled pre-`λ` ring homomorphisms -/

namespace RingHom

section IsPreLambdaHom

variable {R S T : Type*} [CommRing R] [TauCeti.PreLambdaRing R]
  [CommRing S] [TauCeti.PreLambdaRing S] [CommRing T] [TauCeti.PreLambdaRing T]

/-- A ring homomorphism `f : R →+* S` is a **pre-`λ` morphism** if it commutes with `lambdaOp n`
for every `n : ℕ`. -/
def IsPreLambdaHom (f : R →+* S) : Prop :=
  ∀ (n : ℕ) (x : R), f (TauCeti.lambdaOp n x) = TauCeti.lambdaOp n (f x)

theorem isPreLambdaHom_def (f : R →+* S) :
    f.IsPreLambdaHom ↔
      ∀ (n : ℕ) (x : R), f (TauCeti.lambdaOp n x) = TauCeti.lambdaOp n (f x) :=
  (Iff.rfl)

theorem IsPreLambdaHom.mk {f : R →+* S}
    (h : ∀ (n : ℕ) (x : R), f (TauCeti.lambdaOp n x) = TauCeti.lambdaOp n (f x)) :
    f.IsPreLambdaHom :=
  h

theorem IsPreLambdaHom.apply {f : R →+* S} (hf : f.IsPreLambdaHom) (n : ℕ) (x : R) :
    f (TauCeti.lambdaOp n x) = TauCeti.lambdaOp n (f x) :=
  hf n x

/-- Since `f` preserves `1` and is `f` in degree `1`, commuting with `λ^n` for `n ≥ 2` suffices. -/
theorem isPreLambdaHom_iff_two_le {f : R →+* S} :
    f.IsPreLambdaHom ↔
      ∀ ⦃n : ℕ⦄, 2 ≤ n → ∀ x : R, f (TauCeti.lambdaOp n x) = TauCeti.lambdaOp n (f x) := by
  refine ⟨fun hf _ _ x ↦ hf _ x, fun hf n x ↦ ?_⟩
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => exact hf (Nat.le_add_left 2 n) x

/-- `f : R →+* S` is a pre-`λ` morphism if and only if `PowerSeries.map f` carries `totalSeries x`
to `totalSeries (f x)`. -/
theorem isPreLambdaHom_iff_map_totalSeries {f : R →+* S} :
    f.IsPreLambdaHom ↔
      ∀ x : R, (TauCeti.PreLambdaRing.totalSeries x).map f =
        TauCeti.PreLambdaRing.totalSeries (f x) := by
  simp [isPreLambdaHom_def, PowerSeries.ext_iff, forall_comm (α := R) (β := ℕ)]

theorem IsPreLambdaHom.id : (RingHom.id R).IsPreLambdaHom :=
  fun _ _ ↦ rfl

theorem IsPreLambdaHom.comp {g : S →+* T} {f : R →+* S}
    (hg : g.IsPreLambdaHom) (hf : f.IsPreLambdaHom) : (g.comp f).IsPreLambdaHom :=
  fun n x ↦ by rw [comp_apply, hf n x, hg n (f x), comp_apply]

theorem IsPreLambdaHom.map_totalSeries {f : R →+* S} (hf : f.IsPreLambdaHom) (x : R) :
    (TauCeti.PreLambdaRing.totalSeries x).map f = TauCeti.PreLambdaRing.totalSeries (f x) :=
  isPreLambdaHom_iff_map_totalSeries.mp hf x

theorem IsPreLambdaHom.map_totalLambda {f : R →+* S} (hf : f.IsPreLambdaHom) (x : R) :
    principalUnitMap f (TauCeti.PreLambdaRing.totalLambda R (Multiplicative.ofAdd x)) =
      TauCeti.PreLambdaRing.totalLambda S (Multiplicative.ofAdd (f x)) := by
  apply principalUnit_ext
  simp [hf.map_totalSeries]

theorem IsPreLambdaHom.isLineElement {f : R →+* S} (hf : f.IsPreLambdaHom) {l : R}
    (hl : TauCeti.IsLineElement l) : TauCeti.IsLineElement (f l) := by
  rw [TauCeti.PreLambdaRing.isLineElement_def, ← hf.map_totalSeries, hl.totalSeries_eq]
  simp

/-- A ring homomorphism `f : R →+* S` that commutes with `totalSeries` on a set `s` generating `R`
as an additive subgroup is a pre-`λ` morphism. -/
theorem isPreLambdaHom_of_addSubgroupClosure {f : R →+* S} {s : Set R}
    (hspan : AddSubgroup.closure s = ⊤)
    (hs : ∀ x ∈ s, (TauCeti.PreLambdaRing.totalSeries x).map f =
      TauCeti.PreLambdaRing.totalSeries (f x)) :
    f.IsPreLambdaHom := by
  let K : AddSubgroup R :=
    { carrier := {x : R | principalUnitMap f
          (TauCeti.PreLambdaRing.totalLambda R (Multiplicative.ofAdd x)) =
        TauCeti.PreLambdaRing.totalLambda S (Multiplicative.ofAdd (f x))}
      zero_mem' := by simp
      add_mem' := fun {x y} hx hy ↦ by
        rw [Set.mem_ofPred_eq] at hx hy ⊢
        rw [f.map_add, ofAdd_add, ofAdd_add, map_mul, map_mul, map_mul, hx, hy]
      neg_mem' := fun {x} hx ↦ by
        rw [Set.mem_ofPred_eq] at hx ⊢
        rw [f.map_neg, ofAdd_neg, ofAdd_neg, map_inv, map_inv, map_inv, hx] }
  have hle : AddSubgroup.closure s ≤ K := (AddSubgroup.closure_le K).mpr fun x hx ↦ by
    apply principalUnit_ext
    simpa using hs x hx
  rw [isPreLambdaHom_iff_map_totalSeries]
  intro x
  have hmem : x ∈ K := (hspan ▸ hle) (AddSubgroup.mem_top x)
  simpa using congrArg principalUnitSeries hmem

/-- A ring homomorphism `f : R →+* S` carrying an additively generating set of line elements in `R`
to line elements in `S` is a pre-`λ` morphism. -/
theorem isPreLambdaHom_of_isLineElement_addSubgroupClosure {f : R →+* S} {s : Set R}
    (hspan : AddSubgroup.closure s = ⊤)
    (hl : ∀ l ∈ s, TauCeti.IsLineElement l)
    (hfl : ∀ l ∈ s, TauCeti.IsLineElement (f l)) :
    f.IsPreLambdaHom :=
  isPreLambdaHom_of_addSubgroupClosure hspan fun l hls ↦ by
    rw [(hl l hls).totalSeries_eq, (hfl l hls).totalSeries_eq]
    simp

end IsPreLambdaHom

end RingHom

namespace TauCeti

/-! ### Uniqueness of restricted and coinduced structures -/

namespace PreLambdaRing

/-- Along an injective ring homomorphism `f : S →+* R`, there is at most one `PreLambdaRing`
structure on `S` making `f` a pre-`λ` morphism. -/
theorem eq_of_injective_isPreLambdaHom {S R : Type*} [CommRing S] [CommRing R] [PreLambdaRing R]
    {f : S →+* R} (hinj : Function.Injective f) {l₁ l₂ : PreLambdaRing S}
    (h₁ : @RingHom.IsPreLambdaHom S R _ l₁ _ _ f)
    (h₂ : @RingHom.IsPreLambdaHom S R _ l₂ _ _ f) : l₁ = l₂ := by
  ext n x
  apply hinj
  rw [h₁ n x, h₂ n x]

/-- Along a surjective ring homomorphism `f : R →+* Q`, there is at most one `PreLambdaRing`
structure on `Q` making `f` a pre-`λ` morphism. -/
theorem eq_of_surjective_isPreLambdaHom {R Q : Type*} [CommRing R] [PreLambdaRing R] [CommRing Q]
    {f : R →+* Q} (hsurj : Function.Surjective f) {l₁ l₂ : PreLambdaRing Q}
    (h₁ : @RingHom.IsPreLambdaHom R Q _ _ _ l₁ f)
    (h₂ : @RingHom.IsPreLambdaHom R Q _ _ _ l₂ f) : l₁ = l₂ := by
  ext n q
  obtain ⟨x, rfl⟩ := hsurj q
  rw [← h₁ n x, ← h₂ n x]

/-- A subsingleton commutative ring admits at most one `PreLambdaRing` structure. -/
instance instSubsingletonOfSubsingleton (R : Type*) [CommRing R] [Subsingleton R] :
    Subsingleton (PreLambdaRing R) :=
  ⟨fun _ _ ↦ by ext; exact Subsingleton.elim _ _⟩

end PreLambdaRing

/-! ### Bundled morphisms and morphism classes -/

/-- `PreLambdaHomClass F R S` states that `F` is a type of maps preserving all `λ`-operations. -/
class PreLambdaHomClass (F : Type*) (R S : outParam Type*)
    [CommRing R] [PreLambdaRing R] [CommRing S] [PreLambdaRing S] [FunLike F R S] : Prop where
  /-- A pre-`λ` homomorphism commutes with `lambdaOp n` for every `n : ℕ`. -/
  map_lambdaOp (f : F) (n : ℕ) (x : R) : f (lambdaOp n x) = lambdaOp n (f x)

export PreLambdaHomClass (map_lambdaOp)

attribute [simp] map_lambdaOp

section HomClassLemmas

variable {F R S : Type*} [CommRing R] [PreLambdaRing R] [CommRing S] [PreLambdaRing S]
  [FunLike F R S] [RingHomClass F R S] [PreLambdaHomClass F R S]

theorem toRingHom_isPreLambdaHom (f : F) : (f : R →+* S).IsPreLambdaHom :=
  fun n x ↦ map_lambdaOp f n x

@[simp]
theorem map_totalSeries (f : F) (x : R) :
    (PreLambdaRing.totalSeries x).map (f : R →+* S) = PreLambdaRing.totalSeries (f x) :=
  (toRingHom_isPreLambdaHom f).map_totalSeries x

theorem map_totalLambda (f : F) (x : R) :
    principalUnitMap (f : R →+* S) (PreLambdaRing.totalLambda R (Multiplicative.ofAdd x)) =
      PreLambdaRing.totalLambda S (Multiplicative.ofAdd (f x)) :=
  (toRingHom_isPreLambdaHom f).map_totalLambda x

/-- Pre-`λ` morphisms preserve line elements. -/
theorem PreLambdaRing.IsLineElement.map {l : R} (hl : IsLineElement l) (f : F) :
    IsLineElement (f l) :=
  (toRingHom_isPreLambdaHom f).isLineElement hl

end HomClassLemmas

/-- A bundled **pre-`λ` ring homomorphism** between pre-`λ`-rings `R` and `S`. -/
structure PreLambdaRingHom (R S : Type*) [CommRing R] [PreLambdaRing R]
    [CommRing S] [PreLambdaRing S] extends R →+* S where
  /-- Commutation with all `λ`-operations. -/
  map_lambdaOp' (n : ℕ) (x : R) : toFun (lambdaOp n x) = lambdaOp n (toFun x)

namespace PreLambdaRingHom

section Basic

variable {R S T U : Type*} [CommRing R] [PreLambdaRing R] [CommRing S] [PreLambdaRing S]
  [CommRing T] [PreLambdaRing T] [CommRing U] [PreLambdaRing U]

instance instFunLike : FunLike (PreLambdaRingHom R S) R S where
  coe f := f.toRingHom
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h

instance instRingHomClass : RingHomClass (PreLambdaRingHom R S) R S where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_add f := f.map_add'
  map_zero f := f.map_zero'

instance instPreLambdaHomClass : PreLambdaHomClass (PreLambdaRingHom R S) R S where
  map_lambdaOp f := f.map_lambdaOp'

theorem coe_toRingHom (f : PreLambdaRingHom R S) : ⇑f.toRingHom = f :=
  (rfl)

@[simp]
theorem toRingHom_eq_coe (f : PreLambdaRingHom R S) : f.toRingHom = (f : R →+* S) :=
  (rfl)

theorem isPreLambdaHom_toRingHom (f : PreLambdaRingHom R S) : f.toRingHom.IsPreLambdaHom :=
  f.map_lambdaOp'

@[simp]
theorem coe_mk (f : R →+* S) (h) : ⇑(⟨f, h⟩ : PreLambdaRingHom R S) = f :=
  (rfl)

/-- Two pre-`λ` morphisms are equal if and only if they agree on every element. -/
@[ext]
theorem ext {f g : PreLambdaRingHom R S} (h : ∀ x : R, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `PreLambdaRingHom` with a new underlying function equal to the old one. -/
protected def copy (f : PreLambdaRingHom R S) (f' : R → S) (h : f' = f) :
    PreLambdaRingHom R S where
  toFun := f'
  map_one' := h.symm ▸ map_one f
  map_mul' := h.symm ▸ map_mul f
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_lambdaOp' := h.symm ▸ map_lambdaOp f

@[simp]
theorem coe_copy (f : PreLambdaRingHom R S) (f' : R → S) (h : f' = f) :
    ⇑(f.copy f' h) = f' :=
  (rfl)

theorem copy_eq (f : PreLambdaRingHom R S) (f' : R → S) (h : f' = f) :
    f.copy f' h = f :=
  DFunLike.ext' h

/-- Bundle a ring homomorphism satisfying `RingHom.IsPreLambdaHom`. -/
def ofIsPreLambdaHom (f : R →+* S) (hf : f.IsPreLambdaHom) : PreLambdaRingHom R S :=
  ⟨f, hf⟩

@[simp]
theorem coe_ofIsPreLambdaHom (f : R →+* S) (hf : f.IsPreLambdaHom) :
    ⇑(ofIsPreLambdaHom f hf) = f :=
  (rfl)

@[simp]
theorem ofIsPreLambdaHom_apply (f : R →+* S) (hf : f.IsPreLambdaHom) (x : R) :
    ofIsPreLambdaHom f hf x = f x :=
  (rfl)

theorem toRingHom_ofIsPreLambdaHom (f : R →+* S) (hf : f.IsPreLambdaHom) :
    (ofIsPreLambdaHom f hf).toRingHom = f :=
  (rfl)

@[simp]
theorem coe_ringHom_ofIsPreLambdaHom (f : R →+* S) (hf : f.IsPreLambdaHom) :
    (ofIsPreLambdaHom f hf : R →+* S) = f :=
  (rfl)

/-- Construct a `PreLambdaRingHom` from a ring homomorphism commuting with `λ^n` for `n ≥ 2`. -/
def ofMapTwoLe (f : R →+* S)
    (hf : ∀ ⦃n : ℕ⦄, 2 ≤ n → ∀ x : R, f (lambdaOp n x) = lambdaOp n (f x)) :
    PreLambdaRingHom R S :=
  ofIsPreLambdaHom f (RingHom.isPreLambdaHom_iff_two_le.mpr hf)

@[simp]
theorem coe_ofMapTwoLe (f : R →+* S) (hf) : ⇑(ofMapTwoLe f hf) = f :=
  (rfl)

@[simp]
theorem ofMapTwoLe_apply (f : R →+* S) (hf) (x : R) : ofMapTwoLe f hf x = f x :=
  (rfl)

/-- Construct a `PreLambdaRingHom` from a ring homomorphism commuting with `totalSeries`. -/
def ofMapTotalSeries (f : R →+* S)
    (hf : ∀ x : R, (PreLambdaRing.totalSeries x).map f = PreLambdaRing.totalSeries (f x)) :
    PreLambdaRingHom R S :=
  ofIsPreLambdaHom f (RingHom.isPreLambdaHom_iff_map_totalSeries.mpr hf)

@[simp]
theorem coe_ofMapTotalSeries (f : R →+* S) (hf) : ⇑(ofMapTotalSeries f hf) = f :=
  (rfl)

@[simp]
theorem ofMapTotalSeries_apply (f : R →+* S) (hf) (x : R) : ofMapTotalSeries f hf x = f x :=
  (rfl)

variable (R) in
/-- Identity pre-`λ` morphism on `R`. -/
protected def id : PreLambdaRingHom R R :=
  ofIsPreLambdaHom (RingHom.id R) RingHom.IsPreLambdaHom.id

@[simp, norm_cast]
theorem coe_id : ⇑(PreLambdaRingHom.id R) = _root_.id :=
  (rfl)

@[simp]
theorem id_apply (x : R) : PreLambdaRingHom.id R x = x :=
  (rfl)

theorem toRingHom_id : (PreLambdaRingHom.id R).toRingHom = RingHom.id R :=
  (rfl)

@[simp]
theorem coe_ringHom_id : (PreLambdaRingHom.id R : R →+* R) = RingHom.id R :=
  (rfl)

/-- Composition of pre-`λ` morphisms. -/
def comp (g : PreLambdaRingHom S T) (f : PreLambdaRingHom R S) : PreLambdaRingHom R T :=
  ofIsPreLambdaHom (g.toRingHom.comp f.toRingHom)
    (g.isPreLambdaHom_toRingHom.comp f.isPreLambdaHom_toRingHom)

@[simp]
theorem coe_comp (g : PreLambdaRingHom S T) (f : PreLambdaRingHom R S) :
    ⇑(g.comp f) = g ∘ f :=
  (rfl)

@[simp]
theorem comp_apply (g : PreLambdaRingHom S T) (f : PreLambdaRingHom R S) (x : R) :
    g.comp f x = g (f x) :=
  (rfl)

theorem toRingHom_comp (g : PreLambdaRingHom S T) (f : PreLambdaRingHom R S) :
    (g.comp f).toRingHom = g.toRingHom.comp f.toRingHom :=
  (rfl)

@[simp]
theorem coe_ringHom_comp (g : PreLambdaRingHom S T) (f : PreLambdaRingHom R S) :
    (g.comp f : R →+* T) = (g : S →+* T).comp (f : R →+* S) :=
  (rfl)

theorem comp_assoc (h : PreLambdaRingHom T U) (g : PreLambdaRingHom S T)
    (f : PreLambdaRingHom R S) : (h.comp g).comp f = h.comp (g.comp f) :=
  ext fun _ ↦ rfl

@[simp]
theorem id_comp (f : PreLambdaRingHom R S) : (PreLambdaRingHom.id S).comp f = f :=
  ext fun _ ↦ rfl

@[simp]
theorem comp_id (f : PreLambdaRingHom R S) : f.comp (PreLambdaRingHom.id R) = f :=
  ext fun _ ↦ rfl

/-- Two pre-`λ` morphisms that agree on a generating set `s` of `R` as a subring are equal. -/
theorem eq_of_eqOn_subringClosure {f g : PreLambdaRingHom R S} {s : Set R}
    (hspan : Subring.closure s = ⊤) (hs : Set.EqOn f g s) : f = g := by
  ext x
  have hmem : x ∈ (f.toRingHom.eqLocus g.toRingHom) :=
    (hspan ▸ Subring.closure_le.mpr hs) (Subring.mem_top x)
  exact hmem

end Basic

end PreLambdaRingHom

/-! ### Pre-`λ` ring equivalences -/

/-- A bundled **pre-`λ` ring isomorphism** between pre-`λ`-rings `R` and `S`. -/
structure PreLambdaRingEquiv (R S : Type*) [CommRing R] [PreLambdaRing R]
    [CommRing S] [PreLambdaRing S] extends R ≃+* S where
  /-- Commutation with all `λ`-operations. -/
  map_lambdaOp' (n : ℕ) (x : R) : toFun (lambdaOp n x) = lambdaOp n (toFun x)

namespace PreLambdaRingEquiv

variable {R S T : Type*} [CommRing R] [PreLambdaRing R] [CommRing S] [PreLambdaRing S]
  [CommRing T] [PreLambdaRing T]

instance instEquivLike : EquivLike (PreLambdaRingEquiv R S) R S where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by
    rcases e₁ with ⟨⟨⟨_, _, _, _⟩, _, _⟩, _⟩
    rcases e₂ with ⟨⟨⟨_, _, _, _⟩, _, _⟩, _⟩
    congr

instance instRingEquivClass : RingEquivClass (PreLambdaRingEquiv R S) R S where
  map_mul e := e.map_mul'
  map_add e := e.map_add'

instance instPreLambdaHomClass : PreLambdaHomClass (PreLambdaRingEquiv R S) R S where
  map_lambdaOp e := e.map_lambdaOp'

@[simp]
theorem coe_toRingEquiv (e : PreLambdaRingEquiv R S) : ⇑e.toRingEquiv = e :=
  (rfl)

@[ext]
theorem ext {e₁ e₂ : PreLambdaRingEquiv R S} (h : ∀ x : R, e₁ x = e₂ x) : e₁ = e₂ :=
  DFunLike.ext e₁ e₂ h

/-- Reinterpret a `PreLambdaRingEquiv` as a `PreLambdaRingHom`. -/
def toPreLambdaRingHom (e : PreLambdaRingEquiv R S) : PreLambdaRingHom R S where
  toRingHom := e.toRingEquiv.toRingHom
  map_lambdaOp' := e.map_lambdaOp'

@[simp]
theorem coe_toPreLambdaRingHom (e : PreLambdaRingEquiv R S) : ⇑e.toPreLambdaRingHom = e :=
  (rfl)

variable (R) in
/-- Identity pre-`λ` ring equivalence. -/
protected def refl : PreLambdaRingEquiv R R where
  toRingEquiv := RingEquiv.refl R
  map_lambdaOp' _ _ := rfl

@[simp]
theorem refl_apply (x : R) : PreLambdaRingEquiv.refl R x = x :=
  (rfl)

/-- Inverse of a `PreLambdaRingEquiv`. -/
protected def symm (e : PreLambdaRingEquiv R S) : PreLambdaRingEquiv S R where
  toRingEquiv := e.toRingEquiv.symm
  map_lambdaOp' n y := e.toEquiv.injective <|
    (e.right_inv (lambdaOp n y)).trans <|
      (congrArg (lambdaOp n) (e.right_inv y).symm).trans (e.map_lambdaOp' n (e.invFun y)).symm

@[simp]
theorem symm_toRingEquiv (e : PreLambdaRingEquiv R S) :
    e.symm.toRingEquiv = e.toRingEquiv.symm :=
  (rfl)

@[simp]
theorem symm_symm (e : PreLambdaRingEquiv R S) : e.symm.symm = e := by
  ext
  rfl

@[simp]
theorem apply_symm_apply (e : PreLambdaRingEquiv R S) (y : S) : e (e.symm y) = y :=
  e.toRingEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (e : PreLambdaRingEquiv R S) (x : R) : e.symm (e x) = x :=
  e.toRingEquiv.symm_apply_apply x

/-- Composition of pre-`λ` ring equivalences. -/
protected def trans (e₁ : PreLambdaRingEquiv R S) (e₂ : PreLambdaRingEquiv S T) :
    PreLambdaRingEquiv R T where
  toRingEquiv := e₁.toRingEquiv.trans e₂.toRingEquiv
  map_lambdaOp' n x := by simp

@[simp]
theorem trans_apply (e₁ : PreLambdaRingEquiv R S) (e₂ : PreLambdaRingEquiv S T) (x : R) :
    e₁.trans e₂ x = e₂ (e₁ x) :=
  (rfl)

/-- A bijective `PreLambdaRingHom` upgrades to a `PreLambdaRingEquiv`. -/
def ofBijective (f : PreLambdaRingHom R S) (hf : Function.Bijective f) :
    PreLambdaRingEquiv R S where
  toRingEquiv := RingEquiv.ofBijective f.toRingHom hf
  map_lambdaOp' := f.map_lambdaOp'

@[simp]
theorem coe_ofBijective (f : PreLambdaRingHom R S) (hf : Function.Bijective f) :
    ⇑(ofBijective f hf) = f :=
  (rfl)

end PreLambdaRingEquiv

/-! ### Binary and indexed products -/

section Prod

variable {R S T : Type*} [CommRing R] [PreLambdaRing R] [CommRing S] [PreLambdaRing S]
  [CommRing T] [PreLambdaRing T]

instance PreLambdaRing.instProd : PreLambdaRing (R × S) where
  lambdaOp n p := (lambdaOp n p.1, lambdaOp n p.2)
  lambdaOp_zero _ := Prod.ext (lambdaOp_zero _) (lambdaOp_zero _)
  lambdaOp_one _ := Prod.ext (lambdaOp_one _) (lambdaOp_one _)
  lambdaOp_add n p q := Prod.ext
    (by simp [lambdaOp_add, Prod.fst_sum])
    (by simp [lambdaOp_add, Prod.snd_sum])

@[simp]
theorem fst_lambdaOp (n : ℕ) (p : R × S) : (lambdaOp n p).1 = lambdaOp n p.1 :=
  (rfl)

@[simp]
theorem snd_lambdaOp (n : ℕ) (p : R × S) : (lambdaOp n p).2 = lambdaOp n p.2 :=
  (rfl)

theorem lambdaOp_prodMk (n : ℕ) (r : R) (s : S) :
    lambdaOp n (r, s) = (lambdaOp n r, lambdaOp n s) :=
  (rfl)

namespace PreLambdaRingHom

variable (R S) in
/-- First projection `R × S → R` as a `PreLambdaRingHom`. -/
def fst : PreLambdaRingHom (R × S) R where
  toRingHom := RingHom.fst R S
  map_lambdaOp' _ _ := rfl

variable (R S) in
/-- Second projection `R × S → S` as a `PreLambdaRingHom`. -/
def snd : PreLambdaRingHom (R × S) S where
  toRingHom := RingHom.snd R S
  map_lambdaOp' _ _ := rfl

@[simp]
theorem fst_apply (p : R × S) : fst R S p = p.1 :=
  (rfl)

@[simp]
theorem snd_apply (p : R × S) : snd R S p = p.2 :=
  (rfl)

/-- Pairing `T → R × S` of two pre-`λ` morphisms. -/
def prod (f : PreLambdaRingHom T R) (g : PreLambdaRingHom T S) : PreLambdaRingHom T (R × S) where
  toRingHom := f.toRingHom.prod g.toRingHom
  map_lambdaOp' n x := Prod.ext (map_lambdaOp f n x) (map_lambdaOp g n x)

@[simp]
theorem prod_apply (f : PreLambdaRingHom T R) (g : PreLambdaRingHom T S) (x : T) :
    f.prod g x = (f x, g x) :=
  (rfl)

@[simp]
theorem fst_comp_prod (f : PreLambdaRingHom T R) (g : PreLambdaRingHom T S) :
    (fst R S).comp (f.prod g) = f :=
  ext fun _ ↦ rfl

@[simp]
theorem snd_comp_prod (f : PreLambdaRingHom T R) (g : PreLambdaRingHom T S) :
    (snd R S).comp (f.prod g) = g :=
  ext fun _ ↦ rfl

/-- Universal property of the binary product `R × S` of pre-`λ`-rings. -/
def prodEquiv :
    PreLambdaRingHom T (R × S) ≃ PreLambdaRingHom T R × PreLambdaRingHom T S where
  toFun h := ((fst R S).comp h, (snd R S).comp h)
  invFun fg := fg.1.prod fg.2
  left_inv _ := ext fun _ ↦ rfl
  right_inv _ := Prod.ext (ext fun _ ↦ rfl) (ext fun _ ↦ rfl)

end PreLambdaRingHom

end Prod

section Pi

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, PreLambdaRing (R i)]
  {T : Type*} [CommRing T] [PreLambdaRing T]

instance PreLambdaRing.instPi : PreLambdaRing (∀ i, R i) where
  lambdaOp n f i := lambdaOp n (f i)
  lambdaOp_zero _ := funext fun _ ↦ lambdaOp_zero _
  lambdaOp_one _ := funext fun _ ↦ lambdaOp_one _
  lambdaOp_add n f g := funext fun i ↦ by simp [lambdaOp_add]

@[simp]
theorem lambdaOp_pi_apply (n : ℕ) (f : ∀ i, R i) (i : ι) :
    lambdaOp n f i = lambdaOp n (f i) :=
  (rfl)

namespace PreLambdaRingHom

/-- Coordinate projection `(∀ i, R i) → R i` as a `PreLambdaRingHom`. -/
def proj (i : ι) : PreLambdaRingHom (∀ i, R i) (R i) where
  toRingHom := Pi.evalRingHom R i
  map_lambdaOp' _ _ := rfl

@[simp]
theorem proj_apply (i : ι) (f : ∀ i, R i) : proj i f = f i :=
  (rfl)

/-- Indexed product morphism `T → ∀ i, R i` from a family of pre-`λ` morphisms. -/
def pi (f : ∀ i, PreLambdaRingHom T (R i)) : PreLambdaRingHom T (∀ i, R i) where
  toRingHom := RingHom.pi fun i ↦ (f i).toRingHom
  map_lambdaOp' n x := funext fun i ↦ map_lambdaOp (f i) n x

@[simp]
theorem pi_apply (f : ∀ i, PreLambdaRingHom T (R i)) (x : T) (i : ι) :
    pi f x i = f i x :=
  (rfl)

/-- Universal property of the indexed product `∀ i, R i` of pre-`λ`-rings. -/
def piEquiv : PreLambdaRingHom T (∀ i, R i) ≃ ∀ i, PreLambdaRingHom T (R i) where
  toFun h i := (proj i).comp h
  invFun f := pi f
  left_inv _ := ext fun _ ↦ rfl
  right_inv _ := funext fun _ ↦ ext fun _ ↦ rfl

end PreLambdaRingHom

end Pi

end TauCeti
