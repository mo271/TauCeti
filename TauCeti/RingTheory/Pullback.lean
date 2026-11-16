/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.NonUnitalSubring.Defs

/-!
# Fibre products of ring homomorphisms and Milnor squares

Given unital ring homomorphisms `f : R →+* T` and `g : S →+* T` over possibly noncommutative
rings `R` and `S` and a semiring `T`, Mathlib defines their fibre product
`RingHom.pullback f g : Subring (R × S)` together with the projections
`RingHom.pullbackFst f g : f.pullback g →+* R` and
`RingHom.pullbackSnd f g : f.pullback g →+* S`.

This file develops the algebraic interface of `RingHom.pullback` without commutativity or
locality hypotheses:

1. **Universal property:** compatible pairs of ring homomorphisms `(φ : B →+* R, ψ : B →+* S)`
   satisfying `f.comp φ = g.comp ψ` correspond bijectively to ring homomorphisms
   `B →+* f.pullback g` via `RingHom.pullbackLift` and `RingHom.pullbackLiftEquiv`.
2. **Symmetry, functoriality, and degenerate squares:** swapping the legs gives
   `RingHom.pullbackComm`, morphisms of squares induce `RingHom.pullbackMap` and
   `RingHom.pullbackCongr`, a subsingleton corner gives `f.pullback g ≃+* R × S`, and a
   bijective leg identifies the fibre product with the opposite ring.
3. **Units:** invertible elements of `f.pullback g` correspond to pairs of units `(u, v)` in
   `Rˣ × Sˣ` with the same image in `Tˣ` (`RingHom.pullbackUnitsLift`,
   `RingHom.pullbackUnitsEquiv`).
4. **Kernels and Milnor-square quotients:** the projection `f.pullbackFst g` restricts
   unconditionally to a nonunital ring isomorphism
   `RingHom.ker (f.pullbackSnd g) ≃+* RingHom.ker f` (`RingHom.kerPullbackSndEquiv`), and
   when `f` is surjective (`Milnor` square hypothesis) the second projection induces a ring
   isomorphism `(f.pullback g) ⧸ RingHom.ker (f.pullbackSnd g) ≃+* S`
   (`RingHom.quotientKerPullbackSndEquiv`), with symmetric statements along the other leg.

## Main definitions

* `RingHom.pullbackLift`: universal lift `B →+* f.pullback g` of a compatible pair of ring maps.
* `RingHom.pullbackLiftEquiv`: bijection between compatible pairs into `(R, S)` and ring maps
  into `f.pullback g`.
* `RingHom.pullbackComm`: symmetry isomorphism `f.pullback g ≃+* g.pullback f`.
* `RingHom.pullbackMap`, `RingHom.pullbackCongr`: functoriality of `RingHom.pullback` with
  respect to morphisms and equivalences of cospans.
* `RingHom.pullbackEquivProd`, `RingHom.pullbackEquivLeftOfBijective`,
  `RingHom.pullbackEquivRightOfBijective`: canonical equivalences for degenerate squares.
* `RingHom.pullbackUnitsLift`, `RingHom.pullbackUnitsEquiv`: description of `(f.pullback g)ˣ`.
* `RingHom.kerPullbackSndEquiv`, `RingHom.kerPullbackFstEquiv`: nonunital ring equivalences
  `ker (f.pullbackSnd g) ≃+* ker f` and `ker (f.pullbackFst g) ≃+* ker g`.
* `RingHom.quotientKerPullbackSndEquiv`, `RingHom.quotientKerPullbackFstEquiv`: quotient
  isomorphisms `(f.pullback g) ⧸ ker p₂ ≃+* S` (when `f` is surjective) and
  `(f.pullback g) ⧸ ker p₁ ≃+* R` (when `g` is surjective).

## Main results

* `RingHom.pullback_hom_ext`: morphisms into `f.pullback g` are determined by their two
  projections.
* `RingHom.map_pullbackFst_ker_pullbackSnd_eq`: `Ideal.map p₁ (ker p₂) = ker f`, symmetric to
  `RingHom.map_pullbackSnd_ker_pullbackFst_eq`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971),
  §2 (fibre products and Milnor squares).
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter I, §2.6 and Chapter III, §2.
-/

public section

namespace RingHom

section Projections

variable {R S T : Type*} [Ring R] [Ring S] [Semiring T]

/-- Membership in `f.pullback g` means that `f` on the first coordinate equals `g` on the
second. -/
theorem mem_pullback_iff (f : R →+* T) (g : S →+* T) {x : R × S} :
    x ∈ f.pullback g ↔ f x.1 = g x.2 :=
  Iff.rfl

/-- `RingHom.pullbackFst` evaluates to the first coordinate of the underlying pair. -/
theorem pullbackFst_apply (f : R →+* T) (g : S →+* T) (x : f.pullback g) :
    f.pullbackFst g x = x.1.1 :=
  (rfl)

/-- `RingHom.pullbackSnd` evaluates to the second coordinate of the underlying pair. -/
theorem pullbackSnd_apply (f : R →+* T) (g : S →+* T) (x : f.pullback g) :
    f.pullbackSnd g x = x.1.2 :=
  (rfl)

/-- Elements of `f.pullback g` satisfy the defining compatibility equation in `T`. -/
theorem pullback_eq (f : R →+* T) (g : S →+* T) (x : f.pullback g) :
    f (f.pullbackFst g x) = g (f.pullbackSnd g x) :=
  x.2

/-- Two elements of `f.pullback g` are equal when their projections to `R` and `S` agree. -/
theorem pullback_ext {f : R →+* T} {g : S →+* T} {x y : f.pullback g}
    (h₁ : f.pullbackFst g x = f.pullbackFst g y)
    (h₂ : f.pullbackSnd g x = f.pullbackSnd g y) : x = y :=
  Subtype.ext (Prod.ext h₁ h₂)

end Projections

/-! ## Universal property -/

section UniversalProperty

variable {B C R S T : Type*} [Semiring B] [Semiring C] [Ring R] [Ring S] [Semiring T]

/-- **Universal property of `RingHom.pullback`**: a pair of ring homomorphisms `φ : B →+* R`
and `ψ : B →+* S` equalized by `f` and `g` lifts to a ring homomorphism `B →+* f.pullback g`. -/
def pullbackLift (f : R →+* T) (g : S →+* T) (φ : B →+* R) (ψ : B →+* S)
    (h : f.comp φ = g.comp ψ) : B →+* f.pullback g :=
  (φ.prod ψ).codRestrict (f.pullback g) fun b ↦ congr($h b)

/-- The underlying pair of `pullbackLift` at `b` is `(φ b, ψ b)`. -/
@[simp]
theorem coe_pullbackLift_apply (f : R →+* T) (g : S →+* T) (φ : B →+* R) (ψ : B →+* S)
    (h : f.comp φ = g.comp ψ) (b : B) :
    (f.pullbackLift g φ ψ h b : R × S) = (φ b, ψ b) :=
  (rfl)

/-- Composing `pullbackLift` with the first projection recovers `φ`. -/
@[simp]
theorem pullbackFst_comp_pullbackLift (f : R →+* T) (g : S →+* T) (φ : B →+* R) (ψ : B →+* S)
    (h : f.comp φ = g.comp ψ) :
    (f.pullbackFst g).comp (f.pullbackLift g φ ψ h) = φ := by
  ext
  rfl

/-- Composing `pullbackLift` with the second projection recovers `ψ`. -/
@[simp]
theorem pullbackSnd_comp_pullbackLift (f : R →+* T) (g : S →+* T) (φ : B →+* R) (ψ : B →+* S)
    (h : f.comp φ = g.comp ψ) :
    (f.pullbackSnd g).comp (f.pullbackLift g φ ψ h) = ψ := by
  ext
  rfl

/-- Applying the first projection to `pullbackLift` at `b` gives `φ b`. -/
@[simp]
theorem pullbackFst_pullbackLift_apply (f : R →+* T) (g : S →+* T) (φ : B →+* R) (ψ : B →+* S)
    (h : f.comp φ = g.comp ψ) (b : B) :
    f.pullbackFst g (f.pullbackLift g φ ψ h b) = φ b :=
  (rfl)

/-- Applying the second projection to `pullbackLift` at `b` gives `ψ b`. -/
@[simp]
theorem pullbackSnd_pullbackLift_apply (f : R →+* T) (g : S →+* T) (φ : B →+* R) (ψ : B →+* S)
    (h : f.comp φ = g.comp ψ) (b : B) :
    f.pullbackSnd g (f.pullbackLift g φ ψ h b) = ψ b :=
  (rfl)

/-- Ring homomorphisms into `f.pullback g` are uniquely determined by their compositions with
`pullbackFst` and `pullbackSnd`. -/
theorem pullback_hom_ext {f : R →+* T} {g : S →+* T} {ψ₁ ψ₂ : B →+* f.pullback g}
    (h₁ : (f.pullbackFst g).comp ψ₁ = (f.pullbackFst g).comp ψ₂)
    (h₂ : (f.pullbackSnd g).comp ψ₁ = (f.pullbackSnd g).comp ψ₂) : ψ₁ = ψ₂ :=
  ext fun b ↦ pullback_ext congr($h₁ b) congr($h₂ b)

/-- Precomposing `pullbackLift` with `θ : C →+* B` lifts the precomposed pair. -/
theorem pullbackLift_comp (f : R →+* T) (g : S →+* T) (φ : B →+* R) (ψ : B →+* S)
    (h : f.comp φ = g.comp ψ) (θ : C →+* B) :
    (f.pullbackLift g φ ψ h).comp θ =
      f.pullbackLift g (φ.comp θ) (ψ.comp θ) (by rw [← comp_assoc, h, comp_assoc]) :=
  pullback_hom_ext (by ext; rfl) (by ext; rfl)

/-- Lifting the two canonical projections of `f.pullback g` recovers the identity. -/
@[simp]
theorem pullbackLift_pullbackFst_pullbackSnd (f : R →+* T) (g : S →+* T) :
    f.pullbackLift g (f.pullbackFst g) (f.pullbackSnd g) (f.pullback_comm_sq g) =
      RingHom.id (f.pullback g) :=
  pullback_hom_ext (by ext; rfl) (by ext; rfl)

/-- The universal property of `f.pullback g` as a bijection between compatible pairs of ring
homomorphisms `(φ : B →+* R, ψ : B →+* S)` and ring homomorphisms `B →+* f.pullback g`. -/
def pullbackLiftEquiv (f : R →+* T) (g : S →+* T) :
    {p : (B →+* R) × (B →+* S) // f.comp p.1 = g.comp p.2} ≃ (B →+* f.pullback g) where
  toFun p := f.pullbackLift g p.1.1 p.1.2 p.2
  invFun η := ⟨((f.pullbackFst g).comp η, (f.pullbackSnd g).comp η), by
    rw [← comp_assoc, f.pullback_comm_sq g, comp_assoc]⟩
  left_inv _ := Subtype.ext (Prod.ext (by ext; rfl) (by ext; rfl))
  right_inv _ := pullback_hom_ext (by ext; rfl) (by ext; rfl)

/-- Forward evaluation of `pullbackLiftEquiv`. -/
@[simp]
theorem pullbackLiftEquiv_apply (f : R →+* T) (g : S →+* T)
    (p : {p : (B →+* R) × (B →+* S) // f.comp p.1 = g.comp p.2}) :
    f.pullbackLiftEquiv g p = f.pullbackLift g p.1.1 p.1.2 p.2 :=
  (rfl)

/-- Inverse evaluation of `pullbackLiftEquiv`. -/
@[simp]
theorem coe_pullbackLiftEquiv_symm_apply (f : R →+* T) (g : S →+* T) (η : B →+* f.pullback g) :
    ((f.pullbackLiftEquiv g).symm η : (B →+* R) × (B →+* S)) =
      ((f.pullbackFst g).comp η, (f.pullbackSnd g).comp η) :=
  (rfl)

end UniversalProperty

/-! ## Symmetry, functoriality, and degenerate squares -/

section Functoriality

variable {R S T R' S' T' R'' S'' T'' : Type*}
  [Ring R] [Ring S] [Semiring T]
  [Ring R'] [Ring S'] [Semiring T']
  [Ring R''] [Ring S''] [Semiring T'']

/-- Symmetry of the fibre product: swapping the two factors gives a ring isomorphism
`f.pullback g ≃+* g.pullback f`. -/
def pullbackComm (f : R →+* T) (g : S →+* T) : f.pullback g ≃+* g.pullback f :=
  RingEquiv.ofRingHom
    (g.pullbackLift f (f.pullbackSnd g) (f.pullbackFst g) (f.pullback_comm_sq g).symm)
    (f.pullbackLift g (g.pullbackSnd f) (g.pullbackFst f) (g.pullback_comm_sq f).symm)
    (pullback_hom_ext (by ext; rfl) (by ext; rfl))
    (pullback_hom_ext (by ext; rfl) (by ext; rfl))

/-- The inverse of `pullbackComm` is `pullbackComm` with the legs swapped. -/
@[simp]
theorem pullbackComm_symm (f : R →+* T) (g : S →+* T) :
    (f.pullbackComm g).symm = g.pullbackComm f :=
  (rfl)

/-- First projection after `pullbackComm` is the second projection. -/
@[simp]
theorem pullbackFst_pullbackComm_apply (f : R →+* T) (g : S →+* T) (x : f.pullback g) :
    g.pullbackFst f (f.pullbackComm g x) = f.pullbackSnd g x :=
  (rfl)

/-- Second projection after `pullbackComm` is the first projection. -/
@[simp]
theorem pullbackSnd_pullbackComm_apply (f : R →+* T) (g : S →+* T) (x : f.pullback g) :
    g.pullbackSnd f (f.pullbackComm g x) = f.pullbackFst g x :=
  (rfl)

/-- Composing the first projection with `pullbackComm` gives the second projection. -/
@[simp]
theorem pullbackFst_comp_pullbackComm (f : R →+* T) (g : S →+* T) :
    (g.pullbackFst f).comp (f.pullbackComm g : f.pullback g →+* g.pullback f) =
      f.pullbackSnd g :=
  (rfl)

/-- Composing the second projection with `pullbackComm` gives the first projection. -/
@[simp]
theorem pullbackSnd_comp_pullbackComm (f : R →+* T) (g : S →+* T) :
    (g.pullbackSnd f).comp (f.pullbackComm g : f.pullback g →+* g.pullback f) =
      f.pullbackFst g :=
  (rfl)

/-- **Functoriality of `RingHom.pullback`**: a morphism between cospans `(R → T ← S)` and
`(R' → T' ← S')` induces a ring homomorphism between their fibre products. -/
def pullbackMap (f : R →+* T) (g : S →+* T) (f' : R' →+* T') (g' : S' →+* T')
    (α : R →+* R') (β : S →+* S') (γ : T →+* T')
    (h₁ : f'.comp α = γ.comp f) (h₂ : g'.comp β = γ.comp g) :
    f.pullback g →+* f'.pullback g' :=
  f'.pullbackLift g' (α.comp (f.pullbackFst g)) (β.comp (f.pullbackSnd g)) <| by
    rw [← comp_assoc, h₁, comp_assoc, f.pullback_comm_sq g, ← comp_assoc, ← h₂, comp_assoc]

/-- First projection of `pullbackMap` as a composition. -/
@[simp]
theorem pullbackFst_comp_pullbackMap (f : R →+* T) (g : S →+* T)
    (f' : R' →+* T') (g' : S' →+* T') (α : R →+* R') (β : S →+* S') (γ : T →+* T')
    (h₁ : f'.comp α = γ.comp f) (h₂ : g'.comp β = γ.comp g) :
    (f'.pullbackFst g').comp (f.pullbackMap g f' g' α β γ h₁ h₂) = α.comp (f.pullbackFst g) :=
  pullbackFst_comp_pullbackLift ..

/-- Second projection of `pullbackMap` as a composition. -/
@[simp]
theorem pullbackSnd_comp_pullbackMap (f : R →+* T) (g : S →+* T)
    (f' : R' →+* T') (g' : S' →+* T') (α : R →+* R') (β : S →+* S') (γ : T →+* T')
    (h₁ : f'.comp α = γ.comp f) (h₂ : g'.comp β = γ.comp g) :
    (f'.pullbackSnd g').comp (f.pullbackMap g f' g' α β γ h₁ h₂) = β.comp (f.pullbackSnd g) :=
  pullbackSnd_comp_pullbackLift ..

/-- First projection of `pullbackMap` evaluated on an element. -/
@[simp]
theorem pullbackFst_pullbackMap_apply (f : R →+* T) (g : S →+* T)
    (f' : R' →+* T') (g' : S' →+* T') (α : R →+* R') (β : S →+* S') (γ : T →+* T')
    (h₁ : f'.comp α = γ.comp f) (h₂ : g'.comp β = γ.comp g) (x : f.pullback g) :
    f'.pullbackFst g' (f.pullbackMap g f' g' α β γ h₁ h₂ x) = α (f.pullbackFst g x) :=
  (rfl)

/-- Second projection of `pullbackMap` evaluated on an element. -/
@[simp]
theorem pullbackSnd_pullbackMap_apply (f : R →+* T) (g : S →+* T)
    (f' : R' →+* T') (g' : S' →+* T') (α : R →+* R') (β : S →+* S') (γ : T →+* T')
    (h₁ : f'.comp α = γ.comp f) (h₂ : g'.comp β = γ.comp g) (x : f.pullback g) :
    f'.pullbackSnd g' (f.pullbackMap g f' g' α β γ h₁ h₂ x) = β (f.pullbackSnd g x) :=
  (rfl)

/-- `pullbackMap` along identity morphisms is the identity on `f.pullback g`. -/
@[simp]
theorem pullbackMap_id (f : R →+* T) (g : S →+* T) :
    f.pullbackMap g f g (.id R) (.id S) (.id T) (by simp) (by simp) = .id (f.pullback g) :=
  pullback_hom_ext (by ext; rfl) (by ext; rfl)

/-- `pullbackMap` respects composition of morphisms of cospans. -/
theorem pullbackMap_comp (f : R →+* T) (g : S →+* T)
    (f' : R' →+* T') (g' : S' →+* T') (f'' : R'' →+* T'') (g'' : S'' →+* T'')
    (α : R →+* R') (β : S →+* S') (γ : T →+* T')
    (α' : R' →+* R'') (β' : S' →+* S'') (γ' : T' →+* T'')
    (h₁ : f'.comp α = γ.comp f) (h₂ : g'.comp β = γ.comp g)
    (h₁' : f''.comp α' = γ'.comp f') (h₂' : g''.comp β' = γ'.comp g') :
    (f'.pullbackMap g' f'' g'' α' β' γ' h₁' h₂').comp (f.pullbackMap g f' g' α β γ h₁ h₂) =
      f.pullbackMap g f'' g'' (α'.comp α) (β'.comp β) (γ'.comp γ)
        (by rw [← comp_assoc, h₁', comp_assoc, h₁, comp_assoc])
        (by rw [← comp_assoc, h₂', comp_assoc, h₂, comp_assoc]) :=
  pullback_hom_ext (by ext; rfl) (by ext; rfl)

/-- Compatible ring equivalences on the vertices of a cospan induce a ring equivalence between
the fibre products. -/
def pullbackCongr (f : R →+* T) (g : S →+* T) (f' : R' →+* T') (g' : S' →+* T')
    (e₁ : R ≃+* R') (e₂ : S ≃+* S') (e₃ : T ≃+* T')
    (h₁ : f'.comp e₁.toRingHom = e₃.toRingHom.comp f)
    (h₂ : g'.comp e₂.toRingHom = e₃.toRingHom.comp g) :
    f.pullback g ≃+* f'.pullback g' :=
  have h₁' : f.comp e₁.symm.toRingHom = e₃.symm.toRingHom.comp f' := by
    ext r'
    exact e₃.injective (by simpa using (congr($h₁ (e₁.symm r'))).symm)
  have h₂' : g.comp e₂.symm.toRingHom = e₃.symm.toRingHom.comp g' := by
    ext s'
    exact e₃.injective (by simpa using (congr($h₂ (e₂.symm s'))).symm)
  RingEquiv.ofRingHom
    (f.pullbackMap g f' g' e₁.toRingHom e₂.toRingHom e₃.toRingHom h₁ h₂)
    (f'.pullbackMap g' f g e₁.symm.toRingHom e₂.symm.toRingHom e₃.symm.toRingHom h₁' h₂')
    (by
      rw [pullbackMap_comp]
      convert pullbackMap_id f' g' <;> ext <;> simp)
    (by
      rw [pullbackMap_comp]
      convert pullbackMap_id f g <;> ext <;> simp)

/-- First projection of `pullbackCongr` evaluated on an element. -/
@[simp]
theorem pullbackFst_pullbackCongr_apply (f : R →+* T) (g : S →+* T)
    (f' : R' →+* T') (g' : S' →+* T')
    (e₁ : R ≃+* R') (e₂ : S ≃+* S') (e₃ : T ≃+* T')
    (h₁ : f'.comp e₁.toRingHom = e₃.toRingHom.comp f)
    (h₂ : g'.comp e₂.toRingHom = e₃.toRingHom.comp g) (x : f.pullback g) :
    f'.pullbackFst g' (f.pullbackCongr g f' g' e₁ e₂ e₃ h₁ h₂ x) = e₁ (f.pullbackFst g x) :=
  (rfl)

/-- Second projection of `pullbackCongr` evaluated on an element. -/
@[simp]
theorem pullbackSnd_pullbackCongr_apply (f : R →+* T) (g : S →+* T)
    (f' : R' →+* T') (g' : S' →+* T')
    (e₁ : R ≃+* R') (e₂ : S ≃+* S') (e₃ : T ≃+* T')
    (h₁ : f'.comp e₁.toRingHom = e₃.toRingHom.comp f)
    (h₂ : g'.comp e₂.toRingHom = e₃.toRingHom.comp g) (x : f.pullback g) :
    f'.pullbackSnd g' (f.pullbackCongr g f' g' e₁ e₂ e₃ h₁ h₂ x) = e₂ (f.pullbackSnd g x) :=
  (rfl)

/-- Over a subsingleton target `T`, the fibre product `f.pullback g` is canonically isomorphic
to the product ring `R × S`. -/
def pullbackEquivProd (f : R →+* T) (g : S →+* T) [Subsingleton T] :
    f.pullback g ≃+* R × S :=
  RingEquiv.ofRingHom
    (f.pullback g).subtype
    (f.pullbackLift g (fst R S) (snd R S) (ext fun _ ↦ Subsingleton.elim _ _))
    (by ext <;> rfl)
    (pullback_hom_ext (by ext; rfl) (by ext; rfl))

/-- Forward evaluation of `pullbackEquivProd` is the subring inclusion into `R × S`. -/
@[simp]
theorem pullbackEquivProd_apply (f : R →+* T) (g : S →+* T) [Subsingleton T]
    (x : f.pullback g) : f.pullbackEquivProd g x = (x : R × S) :=
  (rfl)

/-- Inverse evaluation of `pullbackEquivProd` embeds `(r, s)` directly into `f.pullback g`. -/
@[simp]
theorem coe_pullbackEquivProd_symm_apply (f : R →+* T) (g : S →+* T) [Subsingleton T]
    (p : R × S) : ((f.pullbackEquivProd g).symm p : R × S) = p :=
  (rfl)

/-- When `g : S →+* T` is bijective (in particular when `g = RingHom.id T`), the first
projection `f.pullbackFst g` is a ring isomorphism `f.pullback g ≃+* R`. -/
noncomputable def pullbackEquivLeftOfBijective (f : R →+* T) (g : S →+* T)
    (hg : Function.Bijective g) : f.pullback g ≃+* R :=
  let e := RingEquiv.ofBijective g hg
  RingEquiv.ofRingHom
    (f.pullbackFst g)
    (f.pullbackLift g (.id R) (e.symm.toRingHom.comp f)
      (ext fun r ↦ (e.apply_symm_apply (f r)).symm))
    (by ext; simp)
    (pullback_hom_ext (by ext; simp) <| ext fun x ↦ e.injective <| by
      simpa [e] using f.pullback_eq g x)

/-- Forward evaluation of `pullbackEquivLeftOfBijective` is `pullbackFst`. -/
@[simp]
theorem pullbackEquivLeftOfBijective_apply (f : R →+* T) (g : S →+* T)
    (hg : Function.Bijective g) (x : f.pullback g) :
    f.pullbackEquivLeftOfBijective g hg x = f.pullbackFst g x :=
  (rfl)

/-- Underlying ring homomorphism of `pullbackEquivLeftOfBijective` is `pullbackFst`. -/
@[simp]
theorem coe_pullbackEquivLeftOfBijective (f : R →+* T) (g : S →+* T)
    (hg : Function.Bijective g) :
    (f.pullbackEquivLeftOfBijective g hg : f.pullback g →+* R) = f.pullbackFst g :=
  (rfl)

/-- First projection of `(pullbackEquivLeftOfBijective hg).symm r` is `r`. -/
@[simp]
theorem pullbackFst_pullbackEquivLeftOfBijective_symm_apply (f : R →+* T) (g : S →+* T)
    (hg : Function.Bijective g) (r : R) :
    f.pullbackFst g ((f.pullbackEquivLeftOfBijective g hg).symm r) = r :=
  (rfl)

/-- Second projection of `(pullbackEquivLeftOfBijective hg).symm r` is `g⁻¹ (f r)`. -/
@[simp]
theorem pullbackSnd_pullbackEquivLeftOfBijective_symm_apply (f : R →+* T) (g : S →+* T)
    (hg : Function.Bijective g) (r : R) :
    f.pullbackSnd g ((f.pullbackEquivLeftOfBijective g hg).symm r) =
      (RingEquiv.ofBijective g hg).symm (f r) :=
  (rfl)

/-- When `f : R →+* T` is bijective (in particular when `f = RingHom.id T`), the second
projection `f.pullbackSnd g` is a ring isomorphism `f.pullback g ≃+* S`. -/
noncomputable def pullbackEquivRightOfBijective (f : R →+* T) (g : S →+* T)
    (hf : Function.Bijective f) : f.pullback g ≃+* S :=
  (f.pullbackComm g).trans (g.pullbackEquivLeftOfBijective f hf)

/-- Forward evaluation of `pullbackEquivRightOfBijective` is `pullbackSnd`. -/
@[simp]
theorem pullbackEquivRightOfBijective_apply (f : R →+* T) (g : S →+* T)
    (hf : Function.Bijective f) (x : f.pullback g) :
    f.pullbackEquivRightOfBijective g hf x = f.pullbackSnd g x :=
  (rfl)

/-- Underlying ring homomorphism of `pullbackEquivRightOfBijective` is `pullbackSnd`. -/
@[simp]
theorem coe_pullbackEquivRightOfBijective (f : R →+* T) (g : S →+* T)
    (hf : Function.Bijective f) :
    (f.pullbackEquivRightOfBijective g hf : f.pullback g →+* S) = f.pullbackSnd g :=
  (rfl)

/-- Second projection of `(pullbackEquivRightOfBijective hf).symm s` is `s`. -/
@[simp]
theorem pullbackSnd_pullbackEquivRightOfBijective_symm_apply (f : R →+* T) (g : S →+* T)
    (hf : Function.Bijective f) (s : S) :
    f.pullbackSnd g ((f.pullbackEquivRightOfBijective g hf).symm s) = s :=
  (rfl)

/-- First projection of `(pullbackEquivRightOfBijective hf).symm s` is `f⁻¹ (g s)`. -/
@[simp]
theorem pullbackFst_pullbackEquivRightOfBijective_symm_apply (f : R →+* T) (g : S →+* T)
    (hf : Function.Bijective f) (s : S) :
    f.pullbackFst g ((f.pullbackEquivRightOfBijective g hf).symm s) =
      (RingEquiv.ofBijective f hf).symm (g s) :=
  (rfl)

end Functoriality

/-! ## Units of a fibre product -/

section Units

variable {R S T : Type*} [Ring R] [Ring S] [Semiring T]

/-- A pair of units `(u, v) ∈ Rˣ × Sˣ` with equal images in `Tˣ` defines a unit of
`f.pullback g`. -/
def pullbackUnitsLift (f : R →+* T) (g : S →+* T) (u : Rˣ) (v : Sˣ)
    (h : Units.map (f : R →* T) u = Units.map (g : S →* T) v) : (f.pullback g)ˣ where
  val := ⟨(u, v), congrArg Units.val h⟩
  inv := ⟨(↑u⁻¹, ↑v⁻¹), congrArg Units.val (congrArg Inv.inv h)⟩
  val_inv := Subtype.ext (Prod.ext u.mul_inv v.mul_inv)
  inv_val := Subtype.ext (Prod.ext u.inv_mul v.inv_mul)

/-- Mapping `pullbackUnitsLift` along `pullbackFst` recovers `u`. -/
@[simp]
theorem unitsMap_pullbackFst_pullbackUnitsLift (f : R →+* T) (g : S →+* T) (u : Rˣ) (v : Sˣ)
    (h : Units.map (f : R →* T) u = Units.map (g : S →* T) v) :
    Units.map (f.pullbackFst g : f.pullback g →* R) (f.pullbackUnitsLift g u v h) = u :=
  Units.ext rfl

/-- Mapping `pullbackUnitsLift` along `pullbackSnd` recovers `v`. -/
@[simp]
theorem unitsMap_pullbackSnd_pullbackUnitsLift (f : R →+* T) (g : S →+* T) (u : Rˣ) (v : Sˣ)
    (h : Units.map (f : R →* T) u = Units.map (g : S →* T) v) :
    Units.map (f.pullbackSnd g : f.pullback g →* S) (f.pullbackUnitsLift g u v h) = v :=
  Units.ext rfl

/-- The group of units `(f.pullback g)ˣ` is canonically isomorphic to the subgroup of pairs
`(u, v) ∈ Rˣ × Sˣ` whose images in `Tˣ` coincide. -/
def pullbackUnitsEquiv (f : R →+* T) (g : S →+* T) :
    (f.pullback g)ˣ ≃*
      ((Units.map (f : R →* T)).comp (MonoidHom.fst Rˣ Sˣ)).eqLocus
        ((Units.map (g : S →* T)).comp (MonoidHom.snd Rˣ Sˣ)) where
  toFun w := ⟨(Units.map (f.pullbackFst g : f.pullback g →* R) w,
      Units.map (f.pullbackSnd g : f.pullback g →* S) w),
    Units.ext (f.pullback_eq g w.val)⟩
  invFun p := f.pullbackUnitsLift g p.1.1 p.1.2 p.2
  left_inv _ := Units.ext (Subtype.ext (Prod.ext rfl rfl))
  right_inv _ := Subtype.ext (Prod.ext (Units.ext rfl) (Units.ext rfl))
  map_mul' _ _ := Subtype.ext (Prod.ext (Units.ext rfl) (Units.ext rfl))

/-- Underlying pair of units associated to `w : (f.pullback g)ˣ` by `pullbackUnitsEquiv`. -/
@[simp]
theorem coe_pullbackUnitsEquiv_apply (f : R →+* T) (g : S →+* T) (w : (f.pullback g)ˣ) :
    ((f.pullbackUnitsEquiv g w :
      ((Units.map (f : R →* T)).comp (MonoidHom.fst Rˣ Sˣ)).eqLocus
        ((Units.map (g : S →* T)).comp (MonoidHom.snd Rˣ Sˣ))) : Rˣ × Sˣ) =
      (Units.map (f.pullbackFst g : f.pullback g →* R) w,
        Units.map (f.pullbackSnd g : f.pullback g →* S) w) :=
  (rfl)

/-- Inverse of `pullbackUnitsEquiv` on a compatible pair of units is `pullbackUnitsLift`. -/
@[simp]
theorem pullbackUnitsEquiv_symm_apply (f : R →+* T) (g : S →+* T)
    (p : ((Units.map (f : R →* T)).comp (MonoidHom.fst Rˣ Sˣ)).eqLocus
      ((Units.map (g : S →* T)).comp (MonoidHom.snd Rˣ Sˣ))) :
    (f.pullbackUnitsEquiv g).symm p = f.pullbackUnitsLift g p.1.1 p.1.2 p.2 :=
  (rfl)

end Units

/-! ## Kernels and Milnor-square quotients -/

section KernelsAndQuotients

variable {R S T : Type*} [Ring R] [Ring S] [Semiring T]

/-- An element of `f.pullback g` lies in `ker (f.pullbackSnd g)` if and only if its first
coordinate lies in `ker f` and its second coordinate is zero. -/
theorem mem_ker_pullbackSnd_iff (f : R →+* T) (g : S →+* T) {x : f.pullback g} :
    x ∈ RingHom.ker (f.pullbackSnd g) ↔
      f.pullbackFst g x ∈ RingHom.ker f ∧ f.pullbackSnd g x = 0 := by
  refine ⟨fun hx ↦ ?_, fun h ↦ h.2⟩
  rw [RingHom.mem_ker] at hx ⊢
  exact ⟨(f.pullback_eq g x).trans (by rw [hx, map_zero]), hx⟩

/-- An element of `f.pullback g` lies in `ker (f.pullbackFst g)` if and only if its first
coordinate is zero and its second coordinate lies in `ker g`. -/
theorem mem_ker_pullbackFst_iff (f : R →+* T) (g : S →+* T) {x : f.pullback g} :
    x ∈ RingHom.ker (f.pullbackFst g) ↔
      f.pullbackFst g x = 0 ∧ f.pullbackSnd g x ∈ RingHom.ker g := by
  refine ⟨fun hx ↦ ?_, fun h ↦ h.1⟩
  rw [RingHom.mem_ker] at hx ⊢
  exact ⟨hx, (f.pullback_eq g x).symm.trans (by rw [hx, map_zero])⟩

/-- Pushing `ker (f.pullbackSnd g)` forward along `f.pullbackFst g` gives `ker f`, symmetric to
`RingHom.map_pullbackSnd_ker_pullbackFst_eq`. -/
theorem map_pullbackFst_ker_pullbackSnd_eq (f : R →+* T) (g : S →+* T) :
    Ideal.map (f.pullbackFst g) (RingHom.ker (f.pullbackSnd g)) = RingHom.ker f := by
  refine le_antisymm ?_ fun r hr ↦ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact ((f.mem_ker_pullbackSnd_iff g).1 hx).1
  · exact Ideal.mem_map_of_mem (f.pullbackFst g)
      (I := RingHom.ker (f.pullbackSnd g))
      (x := ⟨(r, 0), by simpa using RingHom.mem_ker.1 hr⟩) (by simp [pullbackSnd_apply])

/-- The first projection `f.pullbackFst g` restricts to a nonunital ring isomorphism
`ker (f.pullbackSnd g) ≃+* ker f`, with inverse `r ↦ (r, 0)`. -/
def kerPullbackSndEquiv (f : R →+* T) (g : S →+* T) :
    RingHom.ker (f.pullbackSnd g) ≃+* RingHom.ker f where
  toFun x := ⟨f.pullbackFst g x.1, ((f.mem_ker_pullbackSnd_iff g).1 x.2).1⟩
  invFun r := ⟨⟨(r.1, 0), by simpa using RingHom.mem_ker.1 r.2⟩, rfl⟩
  left_inv x := Subtype.ext <| pullback_ext rfl (((f.mem_ker_pullbackSnd_iff g).1 x.2).2.symm)
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Underlying element of `kerPullbackSndEquiv x` in `R` is `f.pullbackFst g x`. -/
@[simp]
theorem coe_kerPullbackSndEquiv_apply (f : R →+* T) (g : S →+* T)
    (x : RingHom.ker (f.pullbackSnd g)) :
    (f.kerPullbackSndEquiv g x : R) = f.pullbackFst g x.1 :=
  (rfl)

/-- Underlying pair of `(kerPullbackSndEquiv).symm r` in `R × S` is `(r, 0)`. -/
@[simp]
theorem coe_kerPullbackSndEquiv_symm_apply (f : R →+* T) (g : S →+* T) (r : RingHom.ker f) :
    (((f.kerPullbackSndEquiv g).symm r : f.pullback g) : R × S) = (r.1, 0) :=
  (rfl)

/-- The second projection `f.pullbackSnd g` restricts to a nonunital ring isomorphism
`ker (f.pullbackFst g) ≃+* ker g`, with inverse `s ↦ (0, s)`. -/
def kerPullbackFstEquiv (f : R →+* T) (g : S →+* T) :
    RingHom.ker (f.pullbackFst g) ≃+* RingHom.ker g where
  toFun x := ⟨f.pullbackSnd g x.1, ((f.mem_ker_pullbackFst_iff g).1 x.2).2⟩
  invFun s := ⟨⟨(0, s.1), by simpa [eq_comm] using RingHom.mem_ker.1 s.2⟩, rfl⟩
  left_inv x := Subtype.ext <| pullback_ext (((f.mem_ker_pullbackFst_iff g).1 x.2).1.symm) rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Underlying element of `kerPullbackFstEquiv x` in `S` is `f.pullbackSnd g x`. -/
@[simp]
theorem coe_kerPullbackFstEquiv_apply (f : R →+* T) (g : S →+* T)
    (x : RingHom.ker (f.pullbackFst g)) :
    (f.kerPullbackFstEquiv g x : S) = f.pullbackSnd g x.1 :=
  (rfl)

/-- Underlying pair of `(kerPullbackFstEquiv).symm s` in `R × S` is `(0, s)`. -/
@[simp]
theorem coe_kerPullbackFstEquiv_symm_apply (f : R →+* T) (g : S →+* T) (s : RingHom.ker g) :
    (((f.kerPullbackFstEquiv g).symm s : f.pullback g) : R × S) = (0, s.1) :=
  (rfl)

/-- In a Milnor square where `f : R →+* T` is surjective, the second projection induces a ring
isomorphism `(f.pullback g) ⧸ ker (f.pullbackSnd g) ≃+* S`. -/
noncomputable def quotientKerPullbackSndEquiv (f : R →+* T) (g : S →+* T)
    (hf : Function.Surjective f) :
    (f.pullback g) ⧸ RingHom.ker (f.pullbackSnd g) ≃+* S :=
  RingHom.quotientKerEquivOfSurjective (f.surjective_pullbackSnd_of_surjective g hf)

/-- `quotientKerPullbackSndEquiv` sends the residue class of `x` to `f.pullbackSnd g x`. -/
@[simp]
theorem quotientKerPullbackSndEquiv_mk (f : R →+* T) (g : S →+* T)
    (hf : Function.Surjective f) (x : f.pullback g) :
    f.quotientKerPullbackSndEquiv g hf (Ideal.Quotient.mk _ x) = f.pullbackSnd g x :=
  (rfl)

/-- In a Milnor square where `g : S →+* T` is surjective, the first projection induces a ring
isomorphism `(f.pullback g) ⧸ ker (f.pullbackFst g) ≃+* R`. -/
noncomputable def quotientKerPullbackFstEquiv (f : R →+* T) (g : S →+* T)
    (hg : Function.Surjective g) :
    (f.pullback g) ⧸ RingHom.ker (f.pullbackFst g) ≃+* R :=
  RingHom.quotientKerEquivOfSurjective (f.surjective_pullbackFst_of_surjective g hg)

/-- `quotientKerPullbackFstEquiv` sends the residue class of `x` to `f.pullbackFst g x`. -/
@[simp]
theorem quotientKerPullbackFstEquiv_mk (f : R →+* T) (g : S →+* T)
    (hg : Function.Surjective g) (x : f.pullback g) :
    f.quotientKerPullbackFstEquiv g hg (Ideal.Quotient.mk _ x) = f.pullbackFst g x :=
  (rfl)

end KernelsAndQuotients

end RingHom
