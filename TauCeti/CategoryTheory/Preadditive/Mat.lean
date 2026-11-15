/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Finite.Sigma
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Preadditive.Mat
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct

/-!
# Monomial isomorphisms, biproducts, and base change in matrix categories

Mathlib defines two matrix categories in `Mathlib/CategoryTheory/Preadditive/Mat.lean`:

* `CategoryTheory.Mat_ C`, the additive envelope of a preadditive category `C`, whose objects are
  finite families `M.X : M.ι → C` and whose morphisms are matrices of morphisms of `C`;
* `CategoryTheory.Mat R`, whose objects are finite types in `Type u` and whose morphisms `M ⟶ N`
  are `M × N` matrices over a semiring `R : Type u`.

In the first half of this file, for `Mat_ C`, given an equivalence `e : M.ι ≃ N.ι` of index types
and isomorphisms `φ i : M.X i ≅ N.X (e i)`, we construct the *monomial* isomorphism
`Mat_.isoOfEquiv e φ : M ≅ N` whose only nonzero entries are `φ i` at `(i, e i)`, and record its
entrywise composition and functoriality laws (`Mat_.isoOfEquiv_refl`, `Mat_.isoOfEquiv_trans`,
`Mat_.isoOfEquiv_symm`).

In the second half of this file, we complete the categorical and additive infrastructure of
`Mat R` across arbitrary universes `u` (Mathlib equips `Mat R` with `Preadditive` only at
`R : Type 0` and leaves biproducts and block matrices as a `TODO`):

* Universe-polymorphic `HasZeroMorphisms (Mat R)` over any `Semiring R` and `Preadditive (Mat R)`
  over any `Ring R`, definitionally agreeing with Mathlib's `Type 0` instances.
* Object constructors `Mat.of` and `Mat.unit`, permutation isomorphisms `Mat.isoOfEquiv`, zero
  object characterizations (`Mat.isZero_iff_isEmpty`), and isomorphism classification by cardinality
  (`Mat.nonempty_iso_iff_natCard_eq`) over any semiring with `InvariantBasisNumber`.
* `HasZeroObject (Mat R)`, explicit sum-indexed binary biproducts (`Mat.biprodIsoSum`, identifying
  `biprod.lift`, `biprod.desc`, and `biprod.map` with `Matrix.fromCols`, `Matrix.fromRows`, and
  `Matrix.fromBlocks`), `HasFiniteBiproducts (Mat R)`, and the canonical bicone `Mat.unitBicone`
  exhibiting every object `M` as the biproduct of `M`-many copies of `Mat.unit R`.
* Essential smallness (`EssentiallySmall.{u} (Mat R)` and `Mat.essentiallySmall_of_small`).
* Base-change functors `Mat.mapRingHom` and equivalences `Mat.mapRingEquiv` along semiring
  homomorphisms and equivalences, preserving zero morphisms and finite biproducts.

## Main declarations

* `CategoryTheory.Mat_.isoOfEquiv`: monomial isomorphism `M ≅ N` in `Mat_ C`.
* `CategoryTheory.Mat.of`, `CategoryTheory.Mat.unit`: finite-type and singleton objects of `Mat R`.
* `CategoryTheory.Mat.isoOfEquiv`: permutation isomorphism `M ≅ N` in `Mat R` from `M ≃ N`.
* `CategoryTheory.Mat.nonempty_iso_iff_natCard_eq`: over a semiring with `InvariantBasisNumber`,
  two objects of `Mat R` are isomorphic if and only if they have the same cardinality.
* `CategoryTheory.Mat.biprodIsoSum`: `M ⊞ N ≅ Mat.of R (M ⊕ N)`, under which `biprod.map f g`
  becomes the block-diagonal matrix `Matrix.fromBlocks f 0 0 g`.
* `CategoryTheory.Mat.unitBicone`, `CategoryTheory.Mat.isoFinBiproductUnit`: decomposition of
  every object `M : Mat R` as a finite biproduct of copies of `Mat.unit R`.
* `CategoryTheory.Mat.mapRingHom`, `CategoryTheory.Mat.mapRingEquiv`: scalar extension on `Mat R`.

## References

* Saunders Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Springer, 1998, §VIII.2.
* Builds on `CategoryTheory.Mat` by Kim Morrison and the Mathlib contributors in
  `Mathlib.CategoryTheory.Preadditive.Mat`.
-/

public section

open CategoryTheory

noncomputable section

namespace CategoryTheory.Mat_

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

@[simp]
theorem zero_apply {M N : Mat_ C} (i : M.ι) (j : N.ι) : (0 : M ⟶ N) i j = 0 := rfl

/-- A one-term family is indexed by a singleton. -/
instance (X : C) : Unique ((embedding C).obj X).ι := inferInstanceAs (Unique PUnit)

/-- The entry of a one-by-one matrix, with the indices typed as those of the one-term families.
Mathlib's `Mat_.embedding_map` types the indices by the unfolded structure instead, so `simp` does
not apply it to indices of type `((embedding C).obj X).ι`. -/
@[simp]
theorem embedding_map_apply {X Y : C} (f : X ⟶ Y) (i : ((embedding C).obj X).ι)
    (j : ((embedding C).obj Y).ι) : (embedding C).map f i j = f :=
  rfl

open scoped Classical in
/-- The matrix of `Mat_.isoOfEquiv e φ`. -/
private def homOfEquiv {M N : Mat_ C} (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) : M ⟶ N :=
  fun i j ↦ if h : e i = j then (φ i).hom ≫ eqToHom (congrArg N.X h) else 0

open scoped Classical in
/-- The matrix of the inverse of `Mat_.isoOfEquiv e φ`. -/
private def invOfEquiv {M N : Mat_ C} (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) : N ⟶ M :=
  fun j i ↦ if h : e i = j then eqToHom (congrArg N.X h.symm) ≫ (φ i).inv else 0

/-- The **monomial isomorphism** `M ≅ N` determined by an equivalence `e : M.ι ≃ N.ι` of index types
and isomorphisms `φ i : M.X i ≅ N.X (e i)`: its matrix has the entry `φ i` at the position
`(i, e i)` and zeros elsewhere. -/
def isoOfEquiv {M N : Mat_ C} (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) : M ≅ N where
  hom := homOfEquiv e φ
  inv := invOfEquiv e φ
  hom_inv_id := by
    ext i i'
    rw [Mat_.comp_apply,
      Finset.sum_eq_single (e i) (fun j _ hj ↦ by simp [homOfEquiv, Ne.symm hj]) (by simp)]
    by_cases h : i = i'
    · subst h
      simp [homOfEquiv, invOfEquiv]
    · simp [homOfEquiv, invOfEquiv, h, Ne.symm h]
  inv_hom_id := by
    ext j j'
    rw [Mat_.comp_apply, Finset.sum_eq_single (e.symm j) (fun i _ hi ↦ by
      simp [invOfEquiv, show e i ≠ j from fun h ↦ hi (by simp [← h])]) (by simp)]
    by_cases h : j = j'
    · subst h
      simp [homOfEquiv, invOfEquiv]
    · simp [homOfEquiv, invOfEquiv, h]

variable {M N P : Mat_ C}

open scoped Classical in
theorem isoOfEquiv_hom_apply (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (i : M.ι) (j : N.ι) :
    (isoOfEquiv e φ).hom i j = if h : e i = j then (φ i).hom ≫ eqToHom (congrArg N.X h) else 0 :=
  (rfl)

open scoped Classical in
theorem isoOfEquiv_inv_apply (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (j : N.ι) (i : M.ι) :
    (isoOfEquiv e φ).inv j i =
      if h : e i = j then eqToHom (congrArg N.X h.symm) ≫ (φ i).inv else 0 :=
  (rfl)

@[simp]
theorem isoOfEquiv_hom_apply_self (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (i : M.ι) :
    (isoOfEquiv e φ).hom i (e i) = (φ i).hom := by
  simp [isoOfEquiv_hom_apply]

@[simp]
theorem isoOfEquiv_inv_apply_self (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (i : M.ι) :
    (isoOfEquiv e φ).inv (e i) i = (φ i).inv := by
  simp [isoOfEquiv_inv_apply]

/-- Precomposing with a monomial isomorphism moves the rows along the equivalence and multiplies
them by the entries. -/
theorem isoOfEquiv_hom_comp_apply (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (g : N ⟶ P)
    (i : M.ι) (k : P.ι) : ((isoOfEquiv e φ).hom ≫ g) i k = (φ i).hom ≫ g (e i) k := by
  rw [comp_apply, Finset.sum_eq_single (e i)]
  · simp
  · intro j _ hj
    simp [isoOfEquiv_hom_apply, Ne.symm hj]
  · simp

/-- Postcomposing with the inverse of a monomial isomorphism moves the columns along the
equivalence and multiplies them by the inverse entries. -/
theorem comp_isoOfEquiv_inv_apply (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (f : P ⟶ N)
    (k : P.ι) (i : M.ι) : (f ≫ (isoOfEquiv e φ).inv) k i = f k (e i) ≫ (φ i).inv := by
  rw [comp_apply, Finset.sum_eq_single (e i)]
  · simp
  · intro j _ hj
    simp [isoOfEquiv_inv_apply, Ne.symm hj]
  · simp

/-- The monomial isomorphism over the identity equivalence with identity entries is the identity
isomorphism. -/
@[simp]
theorem isoOfEquiv_refl (M : Mat_ C) : isoOfEquiv (Equiv.refl M.ι) (fun _ ↦ Iso.refl _) =
    Iso.refl M := by
  ext i j
  rw [isoOfEquiv_hom_apply (Equiv.refl _) (fun _ ↦ Iso.refl _)]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- Monomial isomorphisms compose along the composite equivalence, with composite entries. -/
theorem isoOfEquiv_trans (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (e' : N.ι ≃ P.ι)
    (ψ : ∀ j, N.X j ≅ P.X (e' j)) :
    isoOfEquiv e φ ≪≫ isoOfEquiv e' ψ = isoOfEquiv (e.trans e') fun i ↦ φ i ≪≫ ψ (e i) := by
  ext i k
  rw [Iso.trans_hom, isoOfEquiv_hom_comp_apply, isoOfEquiv_hom_apply, isoOfEquiv_hom_apply]
  by_cases h : e' (e i) = k
  · subst h
    simp
  · simp [h]

/-- The inverse of a monomial isomorphism is monomial over the inverse equivalence. -/
theorem isoOfEquiv_symm (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) :
    (isoOfEquiv e φ).symm =
      isoOfEquiv e.symm fun j ↦ eqToIso (congrArg N.X (e.apply_symm_apply j).symm) ≪≫
        (φ (e.symm j)).symm := by
  ext j i
  by_cases h : e i = j
  · subst h
    simp [isoOfEquiv_hom_apply, isoOfEquiv_inv_apply]
  · simp [isoOfEquiv_hom_apply, isoOfEquiv_inv_apply, h, e.symm_apply_eq, Ne.symm h]

end CategoryTheory.Mat_

namespace CategoryTheory.Mat

open Limits ZeroObject

universe w u

instance instFinite {R : Type u} (M : Mat R) : Finite M :=
  M.property

/-- Local `Fintype` instance on objects of `Mat R` for matrix sums and identity matrices. -/
@[instance_reducible]
private noncomputable def fintype {R : Type u} {M : Mat R} : Fintype M :=
  Fintype.ofFinite M

section Semiring

variable {R : Type u} [Semiring R]

/-- Finite-type constructor for objects of `Mat R`. -/
abbrev of (R : Type u) (α : Type u) [Finite α] : Mat R :=
  ⟨α, ‹_›⟩

/-- The singleton object of `Mat R`, representing the rank-one free module. -/
abbrev unit (R : Type u) : Mat R :=
  of R PUnit.{u + 1}

instance (R : Type u) : Unique (unit R) :=
  inferInstanceAs (Unique PUnit.{u + 1})

/-- Morphisms in `Mat R` over any semiring form an additive commutative monoid entrywise. -/
instance instAddCommMonoidHom (M N : Mat R) : AddCommMonoid (M ⟶ N) :=
  inferInstanceAs <| AddCommMonoid (Matrix M N R)

@[simp]
theorem zero_apply {M N : Mat R} (i : M) (j : N) : (0 : M ⟶ N) i j = 0 :=
  (rfl)

/-- Addition of morphisms in `Mat R` acts entrywise across arbitrary universes; primed because
Mathlib's `Mat.add_apply` is specialized to `R : Type` and `Ring R`. -/
@[simp]
theorem add_apply' {M N : Mat R} (f g : M ⟶ N) (i : M) (j : N) :
    (f + g) i j = f i j + g i j :=
  (rfl)

@[simp]
theorem nsmul_apply {M N : Mat R} (n : ℕ) (f : M ⟶ N) (i : M) (j : N) :
    (n • f) i j = n • f i j :=
  (rfl)

/-- `Mat R` has zero morphisms over any semiring `R : Type u`. -/
instance instHasZeroMorphisms (R : Type u) [Semiring R] : HasZeroMorphisms (Mat R) where
  zero := fun M N ↦ ⟨(0 : Matrix M N R)⟩
  comp_zero _ _ := by
    apply hom_ext
    intro i j
    simp
  zero_comp _ _ _ _ := by
    apply hom_ext
    intro i j
    simp

section IsoOfEquiv

open scoped Classical in
/-- Auxiliary permutation matrix for `Mat.isoOfEquiv`. -/
private def homOfEquiv {M N : Mat R} (e : M ≃ N) : M ⟶ N :=
  Matrix.of fun i j ↦ if e i = j then 1 else 0

attribute [local instance] fintype in
/-- The **permutation isomorphism** `M ≅ N` in `Mat R` induced by a bijection `e : M ≃ N` of the
underlying finite index types, with entry `1` at `(i, e i)` and `0` elsewhere. -/
def isoOfEquiv {M N : Mat R} (e : M ≃ N) : M ≅ N where
  hom := homOfEquiv e
  inv := homOfEquiv e.symm
  hom_inv_id := by
    apply hom_ext
    intro i i'
    rw [comp_apply,
      Finset.sum_eq_single (e i) (fun j _ hj ↦ by simp [homOfEquiv, Ne.symm hj]) (by simp)]
    by_cases h : i = i'
    · subst h
      simp [homOfEquiv]
    · simp [homOfEquiv, h]
  inv_hom_id := by
    apply hom_ext
    intro j j'
    rw [comp_apply,
      Finset.sum_eq_single (e.symm j) (fun i _ hi ↦ by simp [homOfEquiv, Ne.symm hi]) (by simp)]
    by_cases h : j = j'
    · subst h
      simp [homOfEquiv]
    · simp [homOfEquiv, h]

variable {M N P : Mat R}

open scoped Classical in
theorem isoOfEquiv_hom_apply (e : M ≃ N) (i : M) (j : N) :
    (isoOfEquiv (R := R) e).hom i j = if e i = j then 1 else 0 :=
  (rfl)

open scoped Classical in
theorem isoOfEquiv_inv_apply (e : M ≃ N) (j : N) (i : M) :
    (isoOfEquiv (R := R) e).inv j i = if e.symm j = i then 1 else 0 :=
  (rfl)

@[simp]
theorem isoOfEquiv_hom_apply_self (e : M ≃ N) (i : M) :
    (isoOfEquiv (R := R) e).hom i (e i) = 1 := by
  simp [isoOfEquiv_hom_apply]

@[simp]
theorem isoOfEquiv_inv_apply_self (e : M ≃ N) (i : M) :
    (isoOfEquiv (R := R) e).inv (e i) i = 1 := by
  simp [isoOfEquiv_inv_apply]

attribute [local instance] fintype in
/-- Precomposing with a permutation isomorphism reindexes rows along `e`. -/
theorem isoOfEquiv_hom_comp_apply (e : M ≃ N) (g : N ⟶ P) (i : M) (k : P) :
    ((isoOfEquiv (R := R) e).hom ≫ g) i k = g (e i) k := by
  rw [comp_apply, Finset.sum_eq_single (e i)]
  · simp
  · intro j _ hj
    simp [isoOfEquiv_hom_apply, Ne.symm hj]
  · simp

attribute [local instance] fintype in
/-- Postcomposing with the inverse of a permutation isomorphism reindexes columns along `e`. -/
theorem comp_isoOfEquiv_inv_apply (e : M ≃ N) (f : P ⟶ N) (k : P) (i : M) :
    (f ≫ (isoOfEquiv (R := R) e).inv) k i = f k (e i) := by
  rw [comp_apply, Finset.sum_eq_single (e i)]
  · simp
  · intro j _ hj
    have hj' : e.symm j ≠ i := fun h ↦ hj (by rw [← h, e.apply_symm_apply])
    simp [isoOfEquiv_inv_apply, hj']
  · simp

@[simp]
theorem isoOfEquiv_refl (M : Mat R) :
    isoOfEquiv (R := R) (Equiv.refl M) = Iso.refl M := by
  apply Iso.ext
  apply hom_ext
  intro i j
  rw [Iso.refl_hom, isoOfEquiv_hom_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

theorem isoOfEquiv_trans (e : M ≃ N) (e' : N ≃ P) :
    isoOfEquiv (R := R) e ≪≫ isoOfEquiv (R := R) e' = isoOfEquiv (R := R) (e.trans e') := by
  apply Iso.ext
  apply hom_ext
  intro i k
  rw [Iso.trans_hom, isoOfEquiv_hom_comp_apply, isoOfEquiv_hom_apply, isoOfEquiv_hom_apply]
  rfl

@[simp]
theorem isoOfEquiv_symm (e : M ≃ N) :
    (isoOfEquiv (R := R) e).symm = isoOfEquiv (R := R) e.symm :=
  Iso.ext rfl

end IsoOfEquiv

section Classification

/-- Over a subsingleton semiring, every object of `Mat R` is a zero object. -/
theorem isZero_of_subsingleton [Subsingleton R] (M : Mat R) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply hom_ext
  intro i j
  exact Subsingleton.elim _ _

/-- An object of `Mat R` indexed by an empty type is a zero object. -/
theorem isZero_of_isEmpty (M : Mat R) [IsEmpty M] : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply hom_ext
  intro i
  exact isEmptyElim i

/-- Over a nontrivial semiring, a zero object of `Mat R` has an empty underlying type. -/
theorem isEmpty_of_isZero [Nontrivial R] {M : Mat R} (hM : IsZero M) : IsEmpty M := by
  refine ⟨fun i ↦ one_ne_zero (α := R) ?_⟩
  have hid : (𝟙 M : M ⟶ M) = 0 := hM.eq_of_src _ _
  have hii : (𝟙 M : M ⟶ M) i i = (0 : M ⟶ M) i i := congrArg (fun f : M ⟶ M ↦ f i i) hid
  rwa [id_apply_self, zero_apply] at hii

/-- Over a nontrivial semiring, an object of `Mat R` is zero if and only if its index type is
empty. -/
theorem isZero_iff_isEmpty [Nontrivial R] {M : Mat R} : IsZero M ↔ IsEmpty M :=
  ⟨isEmpty_of_isZero, fun _ ↦ isZero_of_isEmpty M⟩

/-- Over a semiring with invariant basis number, isomorphic objects of `Mat R` have the same
cardinality. -/
theorem natCard_eq_of_iso [InvariantBasisNumber R] {M N : Mat R} (f : M ≅ N) :
    Nat.card M = Nat.card N := by
  classical
  let _ : Fintype M := fintype
  let _ : Fintype N := fintype
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Matrix.square_of_invertible f.hom f.inv f.hom_inv_id f.inv_hom_id

/-- Over a semiring with invariant basis number, isomorphic objects of `Mat R` have equivalent
underlying index types. -/
theorem nonempty_equiv_of_iso [InvariantBasisNumber R] {M N : Mat R} (f : M ≅ N) :
    Nonempty (M ≃ N) :=
  ⟨(Finite.equivFinOfCardEq (natCard_eq_of_iso f)).trans (Finite.equivFin N).symm⟩

/-- Over a semiring with invariant basis number, two objects of `Mat R` are isomorphic if and only
if their underlying finite index types are equivalent. -/
theorem nonempty_iso_iff_nonempty_equiv [InvariantBasisNumber R] {M N : Mat R} :
    Nonempty (M ≅ N) ↔ Nonempty (M ≃ N) :=
  ⟨fun ⟨f⟩ ↦ nonempty_equiv_of_iso f, fun ⟨e⟩ ↦ ⟨isoOfEquiv e⟩⟩

/-- Over a semiring with invariant basis number, two objects of `Mat R` are isomorphic if and only
if their underlying finite index types have the same cardinality. -/
theorem nonempty_iso_iff_natCard_eq [InvariantBasisNumber R] {M N : Mat R} :
    Nonempty (M ≅ N) ↔ Nat.card M = Nat.card N :=
  ⟨fun ⟨f⟩ ↦ natCard_eq_of_iso f,
    fun h ↦ ⟨isoOfEquiv ((Finite.equivFinOfCardEq h).trans (Finite.equivFin N).symm)⟩⟩

end Classification

section Biproducts

/-- `Mat R` has a zero object, realized by `PEmpty`. -/
instance instHasZeroObject (R : Type u) [Semiring R] : HasZeroObject (Mat R) :=
  ⟨⟨of R PEmpty, isZero_of_isEmpty (of R PEmpty)⟩⟩

instance [Nontrivial R] : IsEmpty (0 : Mat R) :=
  isEmpty_of_isZero (Limits.isZero_zero (Mat R))

/-- Entrywise evaluation of a composite in `Mat R` when at most one intermediate index
contributes. -/
theorem comp_apply_eq_single {M N P : Mat R} (f : M ⟶ N) (g : N ⟶ P) (i : M) (k : P) (j : N)
    (h : ∀ j' : N, j' ≠ j → f i j' * g j' k = 0) :
    (f ≫ g) i k = f i j * g j k :=
  (comp_apply R f g i k).trans
    (Finset.sum_eq_single (s := @Finset.univ _ (@FintypeCat.fintype N))
      (f := fun j' : N ↦ f i j' * g j' k) j
      (fun j' _ hj' ↦ h j' hj')
      (fun hj ↦ absurd (@Finset.mem_univ _ (@FintypeCat.fintype N) j) hj))

-- `@[expose]` is forced by dependent typing: `(biprodIsoSum M N).hom` has target `of R (M ⊕ N)`,
-- so composing it with `(sumBinaryBicone M N).fst` in public theorem statements requires
-- `(sumBinaryBicone M N).pt` to reduce to `of R (M ⊕ N)`.
open scoped Classical in
attribute [local instance] FintypeCat.fintype in
/-- The explicit binary bicone in `Mat R` with point `of R (M ⊕ N)`, projections assembled by
`Matrix.fromRows`, and inclusions assembled by `Matrix.fromCols`. -/
@[expose] noncomputable def sumBinaryBicone (M N : Mat R) : BinaryBicone M N where
  pt := of R (M ⊕ N)
  fst := Matrix.fromRows (1 : Matrix M M R) 0
  snd := Matrix.fromRows 0 (1 : Matrix N N R)
  inl := Matrix.fromCols (1 : Matrix M M R) 0
  inr := Matrix.fromCols 0 (1 : Matrix N N R)
  inl_fst := Matrix.ext fun i i' ↦
    (comp_apply_eq_single _ _ i i' (Sum.inl i)
      fun x hx ↦ by rcases x with m | n <;> simp_all [eq_comm]).trans
      (by
        by_cases h : i = i'
        · subst h; simp
        · simp [h])
  inl_snd := Matrix.ext fun i j ↦
    (comp_apply_eq_single _ _ i j (Sum.inl i)
      fun x hx ↦ by rcases x with m | n <;> simp_all [eq_comm]).trans (by simp)
  inr_fst := Matrix.ext fun i j ↦
    (comp_apply_eq_single _ _ i j (Sum.inr i)
      fun x hx ↦ by rcases x with m | n <;> simp_all [eq_comm]).trans (by simp)
  inr_snd := Matrix.ext fun j j' ↦
    (comp_apply_eq_single _ _ j j' (Sum.inr j)
      fun x hx ↦ by rcases x with m | n <;> simp_all [eq_comm]).trans
      (by
        by_cases h : j = j'
        · subst h; simp
        · simp [h])

open scoped Classical in
attribute [local instance] FintypeCat.fintype in
/-- `Mat.sumBinaryBicone M N` is a bilimit bicone, exhibiting `of R (M ⊕ N)` as a binary biproduct
of `M` and `N` in `Mat R`. -/
noncomputable def isBilimitSumBinaryBicone (M N : Mat R) : (sumBinaryBicone M N).IsBilimit where
  isLimit := BinaryFan.IsLimit.mk _ (fun f g ↦ (Matrix.fromCols f g : _ ⟶ of R (M ⊕ N)))
    (fun f g ↦ Matrix.ext fun i j ↦
      (comp_apply_eq_single _ _ i j (Sum.inl j)
        fun x hx ↦ by rcases x with m | n <;> simp_all [sumBinaryBicone, eq_comm]).trans
        (by simp [sumBinaryBicone]))
    (fun f g ↦ Matrix.ext fun i j ↦
      (comp_apply_eq_single _ _ i j (Sum.inr j)
        fun x hx ↦ by rcases x with m | n <;> simp_all [sumBinaryBicone, eq_comm]).trans
        (by simp [sumBinaryBicone]))
    (fun {T} f g m h₁ h₂ ↦ by
      subst h₁ h₂
      refine Matrix.ext fun i x ↦ ?_
      rcases x with j | j
      · exact ((comp_apply_eq_single _ _ i j (Sum.inl j)
          fun y hy ↦ by rcases y with m' | n' <;> simp_all [sumBinaryBicone, eq_comm]).trans
          (by simp [sumBinaryBicone])).symm
      · exact ((comp_apply_eq_single _ _ i j (Sum.inr j)
          fun y hy ↦ by rcases y with m' | n' <;> simp_all [sumBinaryBicone, eq_comm]).trans
          (by simp [sumBinaryBicone])).symm)
  isColimit := BinaryCofan.IsColimit.mk _ (fun f g ↦ (Matrix.fromRows f g : of R (M ⊕ N) ⟶ _))
    (fun f g ↦ Matrix.ext fun i j ↦
      (comp_apply_eq_single _ _ i j (Sum.inl i)
        fun x hx ↦ by rcases x with m | n <;> simp_all [sumBinaryBicone, eq_comm]).trans
        (by simp [sumBinaryBicone]))
    (fun f g ↦ Matrix.ext fun i j ↦
      (comp_apply_eq_single _ _ i j (Sum.inr i)
        fun x hx ↦ by rcases x with m | n <;> simp_all [sumBinaryBicone, eq_comm]).trans
        (by simp [sumBinaryBicone]))
    (fun {T} f g m h₁ h₂ ↦ by
      subst h₁ h₂
      refine Matrix.ext fun x j ↦ ?_
      rcases x with i | i
      · exact ((comp_apply_eq_single _ _ i j (Sum.inl i)
          fun y hy ↦ by rcases y with m' | n' <;> simp_all [sumBinaryBicone, eq_comm]).trans
          (by simp [sumBinaryBicone])).symm
      · exact ((comp_apply_eq_single _ _ i j (Sum.inr i)
          fun y hy ↦ by rcases y with m' | n' <;> simp_all [sumBinaryBicone, eq_comm]).trans
          (by simp [sumBinaryBicone])).symm)

instance instHasBinaryBiproduct (M N : Mat R) : HasBinaryBiproduct M N :=
  HasBinaryBiproduct.mk ⟨sumBinaryBicone M N, isBilimitSumBinaryBicone M N⟩

instance instHasBinaryBiproducts (R : Type u) [Semiring R] : HasBinaryBiproducts (Mat R) :=
  ⟨fun _ _ ↦ inferInstance⟩

/-- The canonical isomorphism `M ⊞ N ≅ of R (M ⊕ N)` in `Mat R`. -/
noncomputable def biprodIsoSum (M N : Mat R) : M ⊞ N ≅ of R (M ⊕ N) :=
  (biprod.uniqueUpToIso M N (isBilimitSumBinaryBicone M N)).symm

@[reassoc (attr := simp)]
theorem biprodIsoSum_inv_fst (M N : Mat R) :
    (biprodIsoSum M N).inv ≫ biprod.fst = (sumBinaryBicone M N).fst := by
  unfold biprodIsoSum
  exact (congrArg (· ≫ biprod.fst)
    (biprod.uniqueUpToIso_hom M N (isBilimitSumBinaryBicone M N))).trans (biprod.lift_fst _ _)

@[reassoc (attr := simp)]
theorem biprodIsoSum_inv_snd (M N : Mat R) :
    (biprodIsoSum M N).inv ≫ biprod.snd = (sumBinaryBicone M N).snd := by
  unfold biprodIsoSum
  exact (congrArg (· ≫ biprod.snd)
    (biprod.uniqueUpToIso_hom M N (isBilimitSumBinaryBicone M N))).trans (biprod.lift_snd _ _)

@[reassoc (attr := simp)]
theorem inl_biprodIsoSum_hom (M N : Mat R) :
    biprod.inl ≫ (biprodIsoSum M N).hom = (sumBinaryBicone M N).inl := by
  unfold biprodIsoSum
  exact (congrArg (biprod.inl ≫ ·)
    (biprod.uniqueUpToIso_inv M N (isBilimitSumBinaryBicone M N))).trans (biprod.inl_desc _ _)

@[reassoc (attr := simp)]
theorem inr_biprodIsoSum_hom (M N : Mat R) :
    biprod.inr ≫ (biprodIsoSum M N).hom = (sumBinaryBicone M N).inr := by
  unfold biprodIsoSum
  exact (congrArg (biprod.inr ≫ ·)
    (biprod.uniqueUpToIso_inv M N (isBilimitSumBinaryBicone M N))).trans (biprod.inr_desc _ _)

@[reassoc, simp]
theorem biprodIsoSum_hom_fst (M N : Mat R) :
    (biprodIsoSum M N).hom ≫ (sumBinaryBicone M N).fst = biprod.fst :=
  ((Iso.inv_comp_eq (biprodIsoSum M N)).mp (biprodIsoSum_inv_fst M N)).symm

@[reassoc, simp]
theorem biprodIsoSum_hom_snd (M N : Mat R) :
    (biprodIsoSum M N).hom ≫ (sumBinaryBicone M N).snd = biprod.snd :=
  ((Iso.inv_comp_eq (biprodIsoSum M N)).mp (biprodIsoSum_inv_snd M N)).symm

@[reassoc, simp]
theorem inl_biprodIsoSum_inv (M N : Mat R) :
    (sumBinaryBicone M N).inl ≫ (biprodIsoSum M N).inv = biprod.inl :=
  (Iso.comp_inv_eq (biprodIsoSum M N)).mpr (inl_biprodIsoSum_hom M N).symm

@[reassoc, simp]
theorem inr_biprodIsoSum_inv (M N : Mat R) :
    (sumBinaryBicone M N).inr ≫ (biprodIsoSum M N).inv = biprod.inr :=
  (Iso.comp_inv_eq (biprodIsoSum M N)).mpr (inr_biprodIsoSum_hom M N).symm

open scoped Classical in
attribute [local instance] FintypeCat.fintype in
/-- Under `Mat.biprodIsoSum`, `biprod.lift f g` is horizontal concatenation
`Matrix.fromCols f g`. -/
theorem biprod_lift_comp_biprodIsoSum_hom {P M N : Mat R} (f : P ⟶ M) (g : P ⟶ N) :
    biprod.lift f g ≫ (biprodIsoSum M N).hom = (Matrix.fromCols f g : P ⟶ of R (M ⊕ N)) := by
  let col : P ⟶ of R (M ⊕ N) := Matrix.fromCols f g
  have hfst : col ≫ (sumBinaryBicone M N).fst = f :=
    Matrix.ext fun i j ↦
      (comp_apply_eq_single col (sumBinaryBicone M N).fst i j (Sum.inl j) fun x hx ↦ by
        rcases x with m | n
        · simp [col, sumBinaryBicone, Sum.inl.inj_iff.not.mp hx]
        · simp [col, sumBinaryBicone]).trans (by simp [col, sumBinaryBicone])
  have hsnd : col ≫ (sumBinaryBicone M N).snd = g :=
    Matrix.ext fun i j ↦
      (comp_apply_eq_single col (sumBinaryBicone M N).snd i j (Sum.inr j) fun x hx ↦ by
        rcases x with m | n
        · simp [col, sumBinaryBicone]
        · simp [col, sumBinaryBicone, Sum.inr.inj_iff.not.mp hx]).trans
        (by simp [col, sumBinaryBicone])
  exact BinaryFan.IsLimit.hom_ext (isBilimitSumBinaryBicone M N).isLimit
    (((Category.assoc _ _ _).trans
      ((congrArg (biprod.lift f g ≫ ·) (biprodIsoSum_hom_fst M N)).trans
        (biprod.lift_fst f g))).trans hfst.symm)
    (((Category.assoc _ _ _).trans
      ((congrArg (biprod.lift f g ≫ ·) (biprodIsoSum_hom_snd M N)).trans
        (biprod.lift_snd f g))).trans hsnd.symm)

open scoped Classical in
attribute [local instance] FintypeCat.fintype in
/-- Under `Mat.biprodIsoSum`, `biprod.desc f g` is vertical concatenation
`Matrix.fromRows f g`. -/
theorem biprodIsoSum_inv_comp_biprod_desc {M N P : Mat R} (f : M ⟶ P) (g : N ⟶ P) :
    (biprodIsoSum M N).inv ≫ biprod.desc f g = (Matrix.fromRows f g : of R (M ⊕ N) ⟶ P) := by
  let row : of R (M ⊕ N) ⟶ P := Matrix.fromRows f g
  have hinl : (sumBinaryBicone M N).inl ≫ row = f :=
    Matrix.ext fun i j ↦
      (comp_apply_eq_single (sumBinaryBicone M N).inl row i j (Sum.inl i) fun x hx ↦ by
        rcases x with m | n
        · simp [row, sumBinaryBicone, Ne.symm (Sum.inl.inj_iff.not.mp hx)]
        · simp [row, sumBinaryBicone]).trans (by simp [row, sumBinaryBicone])
  have hinr : (sumBinaryBicone M N).inr ≫ row = g :=
    Matrix.ext fun i j ↦
      (comp_apply_eq_single (sumBinaryBicone M N).inr row i j (Sum.inr i) fun x hx ↦ by
        rcases x with m | n
        · simp [row, sumBinaryBicone]
        · simp [row, sumBinaryBicone, Ne.symm (Sum.inr.inj_iff.not.mp hx)]).trans
        (by simp [row, sumBinaryBicone])
  exact BinaryCofan.IsColimit.hom_ext (isBilimitSumBinaryBicone M N).isColimit
    ((Category.assoc _ _ _).symm.trans
      (((inl_biprodIsoSum_inv_assoc M N _).trans (biprod.inl_desc f g)).trans hinl.symm))
    ((Category.assoc _ _ _).symm.trans
      (((inr_biprodIsoSum_inv_assoc M N _).trans (biprod.inr_desc f g)).trans hinr.symm))

open scoped Classical in
attribute [local instance] FintypeCat.fintype in
private theorem sumBinaryBicone_inl_comp_fromBlocks
    {M₁ N₁ M₂ N₂ : Mat R} (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    (let blk : (sumBinaryBicone M₁ N₁).pt ⟶ (sumBinaryBicone M₂ N₂).pt :=
      Matrix.fromBlocks f (0 : M₁ ⟶ N₂) (0 : N₁ ⟶ M₂) g
    (sumBinaryBicone M₁ N₁).inl ≫ blk = f ≫ (sumBinaryBicone M₂ N₂).inl) := by
  let blk : (sumBinaryBicone M₁ N₁).pt ⟶ (sumBinaryBicone M₂ N₂).pt :=
    Matrix.fromBlocks f (0 : M₁ ⟶ N₂) (0 : N₁ ⟶ M₂) g
  refine Matrix.ext fun i y ↦
    ((comp_apply_eq_single (sumBinaryBicone M₁ N₁).inl blk i y (Sum.inl i) fun x hx ↦ by
      rcases x with m | n
      · rcases y with j | j <;>
          simp [blk, sumBinaryBicone, Ne.symm (Sum.inl.inj_iff.not.mp hx)]
      · rcases y with j | j <;> simp [blk, sumBinaryBicone]).trans ?_)
  rcases y with j | j
  · exact (by simp [blk, sumBinaryBicone] :
        (sumBinaryBicone M₁ N₁).inl i (Sum.inl i) * blk (Sum.inl i) (Sum.inl j) = f i j).trans
      ((comp_apply_eq_single f (sumBinaryBicone M₂ N₂).inl i (Sum.inl j) j
        fun k hk ↦ by simp [sumBinaryBicone, hk]).trans (by simp [sumBinaryBicone])).symm
  · exact (by simp [blk, sumBinaryBicone] :
        (sumBinaryBicone M₁ N₁).inl i (Sum.inl i) * blk (Sum.inl i) (Sum.inr j) = 0).trans
      ((comp_apply R f (sumBinaryBicone M₂ N₂).inl i (Sum.inr j)).trans
        (by simp [sumBinaryBicone])).symm

open scoped Classical in
attribute [local instance] FintypeCat.fintype in
private theorem sumBinaryBicone_inr_comp_fromBlocks
    {M₁ N₁ M₂ N₂ : Mat R} (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    (let blk : (sumBinaryBicone M₁ N₁).pt ⟶ (sumBinaryBicone M₂ N₂).pt :=
      Matrix.fromBlocks f (0 : M₁ ⟶ N₂) (0 : N₁ ⟶ M₂) g
    (sumBinaryBicone M₁ N₁).inr ≫ blk = g ≫ (sumBinaryBicone M₂ N₂).inr) := by
  let blk : (sumBinaryBicone M₁ N₁).pt ⟶ (sumBinaryBicone M₂ N₂).pt :=
    Matrix.fromBlocks f (0 : M₁ ⟶ N₂) (0 : N₁ ⟶ M₂) g
  refine Matrix.ext fun i y ↦
    ((comp_apply_eq_single (sumBinaryBicone M₁ N₁).inr blk i y (Sum.inr i) fun x hx ↦ by
      rcases x with m | n
      · rcases y with j | j <;> simp [blk, sumBinaryBicone]
      · rcases y with j | j <;>
          simp [blk, sumBinaryBicone, Ne.symm (Sum.inr.inj_iff.not.mp hx)]).trans ?_)
  rcases y with j | j
  · exact (by simp [blk, sumBinaryBicone] :
        (sumBinaryBicone M₁ N₁).inr i (Sum.inr i) * blk (Sum.inr i) (Sum.inl j) = 0).trans
      ((comp_apply R g (sumBinaryBicone M₂ N₂).inr i (Sum.inl j)).trans
        (by simp [sumBinaryBicone])).symm
  · exact (by simp [blk, sumBinaryBicone] :
        (sumBinaryBicone M₁ N₁).inr i (Sum.inr i) * blk (Sum.inr i) (Sum.inr j) = g i j).trans
      ((comp_apply_eq_single g (sumBinaryBicone M₂ N₂).inr i (Sum.inr j) j
        fun k hk ↦ by simp [sumBinaryBicone, hk]).trans (by simp [sumBinaryBicone])).symm

/-- Under `Mat.biprodIsoSum`, `biprod.map f g` is the block-diagonal matrix
`Matrix.fromBlocks f 0 0 g`. -/
theorem biprodIsoSum_inv_comp_biprod_map_comp_biprodIsoSum_hom
    {M₁ N₁ M₂ N₂ : Mat R} (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    (biprodIsoSum M₁ N₁).inv ≫ biprod.map f g ≫ (biprodIsoSum M₂ N₂).hom =
      (Matrix.fromBlocks f (0 : M₁ ⟶ N₂) (0 : N₁ ⟶ M₂) g :
        of R (M₁ ⊕ N₁) ⟶ of R (M₂ ⊕ N₂)) :=
  BinaryCofan.IsColimit.hom_ext (isBilimitSumBinaryBicone M₁ N₁).isColimit
    ((Category.assoc _ _ _).symm.trans
      (((inl_biprodIsoSum_inv_assoc M₁ N₁ _).trans
        ((biprod.inl_map_assoc f g _).trans
          (congrArg (f ≫ ·) (inl_biprodIsoSum_hom M₂ N₂)))).trans
        (sumBinaryBicone_inl_comp_fromBlocks f g).symm))
    ((Category.assoc _ _ _).symm.trans
      (((inr_biprodIsoSum_inv_assoc M₁ N₁ _).trans
        ((biprod.inr_map_assoc f g _).trans
          (congrArg (g ≫ ·) (inr_biprodIsoSum_hom M₂ N₂)))).trans
        (sumBinaryBicone_inr_comp_fromBlocks f g).symm))

/-- Over a semiring with invariant basis number, the cardinality of a binary biproduct in `Mat R`
is the sum of the cardinalities. -/
@[simp]
theorem natCard_biprod [InvariantBasisNumber R] (M N : Mat R) :
    Nat.card (M ⊞ N : Mat R) = Nat.card M + Nat.card N :=
  (natCard_eq_of_iso (biprodIsoSum M N)).trans Nat.card_sum

instance instHasFiniteBiproducts (R : Type u) [Semiring R] : HasFiniteBiproducts (Mat R) :=
  TauCeti.hasFiniteBiproducts_of_hasBinaryBiproducts

-- `@[expose]` is forced by dependent typing: `biproductIsoSigma` and preservation of finite
-- biproducts by `mapRingHom` require `(sigmaBicone f).pt` to reduce to `of R (Σ j, f j)`.
open scoped Classical in
/-- The canonical bicone exhibiting `of R (Σ j, f j)` as the biproduct of a finite family
`f : J → Mat R`, with block projections and inclusions indexed by the sigma type. -/
@[expose] noncomputable def sigmaBicone {J : Type} [Finite J] (f : J → Mat R) : Bicone f where
  pt := of R (Σ j, f j)
  π j := Matrix.of fun p x ↦ if p = ⟨j, x⟩ then 1 else 0
  ι j := Matrix.of fun x p ↦ if p = ⟨j, x⟩ then 1 else 0
  ι_π i j := Matrix.ext fun x y ↦ by
    let ιi : f i ⟶ of R (Σ k, f k) := Matrix.of fun x' p ↦ if p = ⟨i, x'⟩ then 1 else 0
    let πj : of R (Σ k, f k) ⟶ f j := Matrix.of fun p y' ↦ if p = ⟨j, y'⟩ then 1 else 0
    refine (comp_apply_eq_single ιi πj x y ⟨i, x⟩
      fun p hp ↦ (congrArg (· * πj p y) (ite_eq_right hp)).trans (zero_mul _)).trans ?_
    by_cases h : i = j
    · subst h
      have hrhs :
          (if h' : i = i then eqToHom (congrArg f h') else 0) x y = (𝟙 (f i)) x y :=
        congrArg (fun m : f i ⟶ f i ↦ m x y) (dite_eq_left rfl)
      by_cases hxy : x = y
      · subst hxy
        exact (congrArg (· * πj ⟨i, x⟩ x) (ite_eq_left rfl)).trans
          ((one_mul _).trans ((ite_eq_left rfl).trans
            ((id_apply_self R (f i) x).symm.trans hrhs.symm)))
      · have hne : (⟨i, x⟩ : Σ k, f k) ≠ ⟨i, y⟩ :=
          fun heq ↦ hxy (eq_of_heq (Sigma.mk.inj_iff.mp heq).2)
        exact (congrArg (· * πj ⟨i, x⟩ y) (ite_eq_left rfl)).trans
          ((one_mul _).trans ((ite_eq_right hne).trans
            ((id_apply_of_ne R (f i) x y hxy).symm.trans hrhs.symm)))
    · have hne : (⟨i, x⟩ : Σ k, f k) ≠ ⟨j, y⟩ :=
        fun heq ↦ h (Sigma.mk.inj_iff.mp heq).1
      have hrhs : (if h' : i = j then eqToHom (congrArg f h') else 0) x y = 0 :=
        congrArg (fun m : f i ⟶ f j ↦ m x y) (dite_eq_right h)
      exact (congrArg (· * πj ⟨i, x⟩ y) (ite_eq_left rfl)).trans
        ((one_mul _).trans ((ite_eq_right hne).trans hrhs.symm))

open scoped Classical in
/-- `Mat.sigmaBicone f` is a bilimit bicone, exhibiting `of R (Σ j, f j)` as `⨁ f`. -/
noncomputable def isBilimitSigmaBicone {J : Type} [Finite J] (f : J → Mat R) :
    (sigmaBicone f).IsBilimit where
  isLimit := Fan.IsLimit.mk _
    (fun s ↦ (Matrix.of fun q (p : Σ j, f j) ↦ s.proj p.1 q p.2 : s.pt ⟶ of R (Σ j, f j)))
    (fun s j ↦ Matrix.ext fun q x ↦ by
      let liftS : s.pt ⟶ of R (Σ k, f k) := Matrix.of fun q' p ↦ s.proj p.1 q' p.2
      exact (comp_apply_eq_single liftS ((sigmaBicone f).π j) q x ⟨j, x⟩
        fun p hp ↦ (congrArg (s.proj p.1 q p.2 * ·) (ite_eq_right hp)).trans (mul_zero _)).trans
        ((congrArg (s.proj j q x * ·) (ite_eq_left rfl)).trans (mul_one _)))
    (fun s m hm ↦ Matrix.ext fun q ⟨j, x⟩ ↦
      (((comp_apply_eq_single m ((sigmaBicone f).π j) q x ⟨j, x⟩
        fun p hp ↦ (congrArg (m q p * ·) (ite_eq_right hp)).trans (mul_zero _)).trans
        ((congrArg (m q ⟨j, x⟩ * ·) (ite_eq_left rfl)).trans (mul_one _))).symm.trans
        (congrArg (fun g : s.pt ⟶ f j ↦ g q x) (hm j))))
  isColimit := Cofan.IsColimit.mk _
    (fun s ↦ (Matrix.of fun (p : Σ j, f j) q ↦ s.inj p.1 p.2 q : of R (Σ j, f j) ⟶ s.pt))
    (fun s i ↦ Matrix.ext fun x q ↦ by
      let descS : of R (Σ k, f k) ⟶ s.pt := Matrix.of fun p q' ↦ s.inj p.1 p.2 q'
      exact (comp_apply_eq_single ((sigmaBicone f).ι i) descS x q ⟨i, x⟩
        fun p hp ↦ (congrArg (· * s.inj p.1 p.2 q) (ite_eq_right hp)).trans (zero_mul _)).trans
        ((congrArg (· * s.inj i x q) (ite_eq_left rfl)).trans (one_mul _)))
    (fun s m hm ↦ Matrix.ext fun ⟨i, x⟩ q ↦
      (((comp_apply_eq_single ((sigmaBicone f).ι i) m x q ⟨i, x⟩
        fun p hp ↦ (congrArg (· * m p q) (ite_eq_right hp)).trans (zero_mul _)).trans
        ((congrArg (· * m ⟨i, x⟩ q) (ite_eq_left rfl)).trans (one_mul _))).symm.trans
        (congrArg (fun g : f i ⟶ s.pt ↦ g x q) (hm i))))

/-- The canonical isomorphism `⨁ f ≅ of R (Σ j, f j)` for a finite family `f : J → Mat R`. -/
noncomputable def biproductIsoSigma {J : Type} [Finite J] (f : J → Mat R) :
    ⨁ f ≅ of R (Σ j, f j) :=
  (biproduct.uniqueUpToIso f (isBilimitSigmaBicone f)).symm

-- `@[expose]` is forced by dependent typing: `isoBiproductUnit` and `isoFinBiproductUnit` have
-- source `M`, which requires `(unitBicone M).pt` to reduce to `M`.
open scoped Classical in
/-- The canonical bicone exhibiting `M : Mat R` as the biproduct of `M`-many copies of
`Mat.unit R`, with projections and inclusions given by the standard basis vectors. -/
@[expose] noncomputable def unitBicone (M : Mat R) : Bicone (fun _ : M ↦ unit R) where
  pt := M
  π j := Matrix.of fun i _ ↦ if i = j then 1 else 0
  ι i := Matrix.of fun _ j ↦ if i = j then 1 else 0
  ι_π i j := Matrix.ext fun ⟨⟩ ⟨⟩ ↦ by
    let ιi : unit R ⟶ M := Matrix.of fun _ j' ↦ if i = j' then 1 else 0
    let πj : M ⟶ unit R := Matrix.of fun i' _ ↦ if i' = j then 1 else 0
    refine (comp_apply_eq_single ιi πj PUnit.unit PUnit.unit i
      fun m hm ↦ (congrArg (· * πj m PUnit.unit) (ite_eq_right (Ne.symm hm))).trans
        (zero_mul _)).trans ?_
    by_cases h : i = j
    · subst h
      have hrhs :
          (if h' : i = i then eqToHom (congrArg (fun _ : M ↦ unit R) h') else 0)
            PUnit.unit PUnit.unit = 1 :=
        (congrArg (fun m : unit R ⟶ unit R ↦ m PUnit.unit PUnit.unit) (dite_eq_left rfl)).trans
          (id_apply_self R (unit R) PUnit.unit)
      exact (congrArg (· * πj i PUnit.unit) (ite_eq_left rfl)).trans
        ((one_mul _).trans ((ite_eq_left rfl).trans hrhs.symm))
    · have hrhs :
          (if h' : i = j then eqToHom (congrArg (fun _ : M ↦ unit R) h') else 0)
            PUnit.unit PUnit.unit = 0 :=
        congrArg (fun m : unit R ⟶ unit R ↦ m PUnit.unit PUnit.unit) (dite_eq_right h)
      exact (congrArg (· * πj i PUnit.unit) (ite_eq_left rfl)).trans
        ((one_mul _).trans ((ite_eq_right h).trans hrhs.symm))

open scoped Classical in
/-- `Mat.unitBicone M` is a bilimit bicone, exhibiting `M` as `⨁ fun _ : M ↦ Mat.unit R`. -/
noncomputable def isBilimitUnitBicone (M : Mat R) : (unitBicone M).IsBilimit where
  isLimit := Fan.IsLimit.mk _ (fun s ↦ (Matrix.of fun p j ↦ s.proj j p PUnit.unit : s.pt ⟶ M))
    (fun s j ↦ Matrix.ext fun p ⟨⟩ ↦ by
      let liftS : s.pt ⟶ M := Matrix.of fun p' j' ↦ s.proj j' p' PUnit.unit
      exact (comp_apply_eq_single liftS ((unitBicone M).π j) p PUnit.unit j
        fun k hk ↦ (congrArg (s.proj k p PUnit.unit * ·) (ite_eq_right hk)).trans
          (mul_zero _)).trans
        ((congrArg (s.proj j p PUnit.unit * ·) (ite_eq_left rfl)).trans (mul_one _)))
    (fun s m hm ↦ Matrix.ext fun p j ↦
      (((comp_apply_eq_single m ((unitBicone M).π j) p PUnit.unit j
        fun k hk ↦ (congrArg (m p k * ·) (ite_eq_right hk)).trans (mul_zero _)).trans
        ((congrArg (m p j * ·) (ite_eq_left rfl)).trans (mul_one _))).symm.trans
        (congrArg (fun f : s.pt ⟶ unit R ↦ f p PUnit.unit) (hm j))))
  isColimit := Cofan.IsColimit.mk _ (fun s ↦ (Matrix.of fun i p ↦ s.inj i PUnit.unit p : M ⟶ s.pt))
    (fun s i ↦ Matrix.ext fun ⟨⟩ p ↦ by
      let descS : M ⟶ s.pt := Matrix.of fun i' p' ↦ s.inj i' PUnit.unit p'
      exact (comp_apply_eq_single ((unitBicone M).ι i) descS PUnit.unit p i
        fun k hk ↦ (congrArg (· * s.inj k PUnit.unit p) (ite_eq_right (Ne.symm hk))).trans
          (zero_mul _)).trans
        ((congrArg (· * s.inj i PUnit.unit p) (ite_eq_left rfl)).trans (one_mul _)))
    (fun s m hm ↦ Matrix.ext fun i p ↦
      (((comp_apply_eq_single ((unitBicone M).ι i) m PUnit.unit p i
        fun k hk ↦ (congrArg (· * m k p) (ite_eq_right (Ne.symm hk))).trans (zero_mul _)).trans
        ((congrArg (· * m i p) (ite_eq_left rfl)).trans (one_mul _))).symm.trans
        (congrArg (fun f : unit R ⟶ s.pt ↦ f PUnit.unit p) (hm i))))

instance instHasBiproductUnit (M : Mat R) : HasBiproduct (fun _ : M ↦ unit R) :=
  HasBiproduct.mk ⟨unitBicone M, isBilimitUnitBicone M⟩

/-- Every object `M : Mat R` is canonically isomorphic to the `M`-indexed biproduct of copies of
`Mat.unit R`. -/
noncomputable def isoBiproductUnit (M : Mat R) : M ≅ ⨁ fun _ : M ↦ unit R :=
  biproduct.uniqueUpToIso _ (isBilimitUnitBicone M)

/-- Every object `M : Mat R` is isomorphic to the `Fin (Nat.card M)`-indexed biproduct of copies of
`Mat.unit R`. -/
noncomputable def isoFinBiproductUnit (M : Mat R) : M ≅ ⨁ fun _ : Fin (Nat.card M) ↦ unit R :=
  let e : M ≃ Fin (Nat.card M) := Finite.equivFinOfCardEq rfl
  let hb : ((unitBicone M).whisker e.symm).IsBilimit :=
    (Bicone.whiskerIsBilimitIff (unitBicone M) e.symm).2 (isBilimitUnitBicone M)
  biproduct.uniqueUpToIso (fun _ : Fin (Nat.card M) ↦ unit R) hb

end Biproducts

section EssentiallySmall

/-- The skeleton of `Mat R` is small in every universe `w`, since every object is isomorphic to
`of R (ULift (Fin n))` for `n = Nat.card M`. -/
instance instSmallSkeleton (R : Type u) [Semiring R] : Small.{w} (Skeleton (Mat R)) := by
  refine small_of_surjective
    (f := fun n : ULift.{w} ℕ ↦ toSkeleton (of R (ULift.{u} (Fin n.down)))) ?_
  intro S
  let X : Mat R := (fromSkeleton (Mat R)).obj S
  refine ⟨⟨Nat.card X⟩, ?_⟩
  rw [← toSkeleton_fromSkeleton_obj S, toSkeleton_eq_toSkeleton_iff]
  exact ⟨isoOfEquiv (Equiv.ulift.trans (Finite.equivFinOfCardEq (α := X) rfl).symm)⟩

/-- `Mat R` is essentially small in its own universe `u`. -/
instance instEssentiallySmall (R : Type u) [Semiring R] : EssentiallySmall.{u} (Mat R) :=
  (essentiallySmall_iff (Mat R)).2 ⟨inferInstance, inferInstance⟩

/-- Whenever `R` is `w`-small, `Mat R` is `w`-essentially small. Stated as a theorem rather than an
instance because `w` is an `outParam` of `EssentiallySmall`. -/
theorem essentiallySmall_of_small {R : Type u} [Semiring R] [Small.{w} R] :
    EssentiallySmall.{w} (Mat R) := by
  have : LocallySmall.{w} (Mat R) :=
    ⟨fun M N ↦ by
      obtain ⟨n, ⟨eM⟩⟩ := Finite.exists_equiv_fin M
      obtain ⟨m, ⟨eN⟩⟩ := Finite.exists_equiv_fin N
      change Small.{w} (Matrix M N R)
      exact ⟨ULift.{w} (Fin n) → ULift.{w} (Fin m) → Shrink.{w} R,
        ⟨Matrix.of.symm.trans <| Equiv.arrowCongr (eM.trans Equiv.ulift.symm)
          (Equiv.arrowCongr (eN.trans Equiv.ulift.symm) (equivShrink.{w} R))⟩⟩⟩
  exact (essentiallySmall_iff (Mat R)).2 ⟨inferInstance, this⟩

end EssentiallySmall

end Semiring

section Ring

variable {R : Type u} [Ring R]

/-- Morphisms in `Mat R` over any ring `R : Type u` form an additive commutative group entrywise,
generalizing Mathlib's `Type 0` instance across universes with identical definitional behavior. -/
instance addCommGroupHom (M N : Mat R) : AddCommGroup (M ⟶ N) :=
  inferInstanceAs <| AddCommGroup (Matrix M N R)

@[simp]
theorem neg_apply {M N : Mat R} (f : M ⟶ N) (i : M) (j : N) : (-f) i j = -f i j :=
  (rfl)

@[simp]
theorem sub_apply {M N : Mat R} (f g : M ⟶ N) (i : M) (j : N) : (f - g) i j = f i j - g i j :=
  (rfl)

@[simp]
theorem zsmul_apply {M N : Mat R} (n : ℤ) (f : M ⟶ N) (i : M) (j : N) :
    (n • f) i j = n • f i j :=
  (rfl)

attribute [local instance] FintypeCat.fintype in
/-- `Mat R` is preadditive over any ring `R : Type u`, generalizing Mathlib's `Type 0` instance. -/
instance preadditive (R : Type u) [Ring R] : Preadditive (Mat R) where
  homGroup M N := addCommGroupHom M N
  add_comp _ _ _ f g h := Matrix.ext fun i k ↦
    (comp_apply R (f + g) h i k).trans
      ((Finset.sum_congr rfl fun j _ ↦ add_mul (f i j) (g i j) (h j k)).trans
        (Finset.sum_add_distrib.trans
          (congrArg₂ (· + ·) (comp_apply R f h i k).symm (comp_apply R g h i k).symm)))
  comp_add _ _ _ f g h := Matrix.ext fun i k ↦
    (comp_apply R f (g + h) i k).trans
      ((Finset.sum_congr rfl fun j _ ↦ mul_add (f i j) (g j k) (h j k)).trans
        (Finset.sum_add_distrib.trans
          (congrArg₂ (· + ·) (comp_apply R f g i k).symm (comp_apply R f h i k).symm)))

end Ring

section MapRingHom

section Semiring

variable {R S T : Type u} [Semiring R] [Semiring S] [Semiring T]

-- `@[expose]` is forced by dependent typing of component matrices: without `(mapRingHom φ).obj M`
-- reducing to the same underlying `FintypeCat` object, `((mapRingHom φ).map f) i j` cannot be
-- indexed by `i : M` and `j : N`, and `mapRingHom_id` / `mapRingHom_comp` would need `eqToHom`.
attribute [local instance] FintypeCat.fintype in
/-- Base change on `Mat` along a semiring homomorphism `φ : R →+* S`, acting as the identity on the
underlying finite index types and applying `φ` entrywise to matrices. -/
@[expose] def mapRingHom (φ : R →+* S) : Mat R ⥤ Mat S where
  obj M := (M : FintypeCat.{u})
  map {M N} f := (Matrix.map f φ : Matrix M N S)
  map_id M := Matrix.ext fun i j ↦ by
    let MS : Mat S := (M : FintypeCat.{u})
    by_cases h : i = j
    · subst h
      exact (congrArg φ (id_apply_self R M i)).trans
        ((map_one φ).trans (id_apply_self S MS i).symm)
    · exact (congrArg φ (id_apply_of_ne R M i j h)).trans
        ((map_zero φ).trans (id_apply_of_ne S MS i j h).symm)
  map_comp {M N P} f g := Matrix.ext fun i k ↦ by
    let MS : Mat S := (M : FintypeCat.{u})
    let NS : Mat S := (N : FintypeCat.{u})
    let PS : Mat S := (P : FintypeCat.{u})
    exact (congrArg φ (comp_apply R f g i k)).trans
      ((map_sum φ _ _).trans
        ((Finset.sum_congr rfl fun j _ ↦ map_mul φ (f i j) (g j k)).trans
          (comp_apply S (M := MS) (N := NS) (K := PS)
            (Matrix.map f φ) (Matrix.map g φ) i k).symm))

@[simp]
theorem mapRingHom_obj_of (φ : R →+* S) (α : Type u) [Finite α] :
    (mapRingHom φ).obj (of R α) = of S α :=
  (rfl)

@[simp]
theorem mapRingHom_coe_obj (φ : R →+* S) (M : Mat R) :
    ((mapRingHom φ).obj M : Type u) = M :=
  (rfl)

@[simp]
theorem mapRingHom_map_apply (φ : R →+* S) {M N : Mat R} (f : M ⟶ N) (i : M) (j : N) :
    ((mapRingHom φ).map f) i j = φ (f i j) :=
  (rfl)

@[simp]
theorem mapRingHom_id (R : Type u) [Semiring R] :
    mapRingHom (RingHom.id R) = 𝟭 (Mat R) :=
  Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦
    (Matrix.ext fun _ _ ↦ rfl).trans ((Category.comp_id _).symm.trans (Category.id_comp _).symm)

theorem mapRingHom_comp (φ : R →+* S) (ψ : S →+* T) :
    mapRingHom (ψ.comp φ) = mapRingHom φ ⋙ mapRingHom ψ :=
  Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦
    (Matrix.ext fun _ _ ↦ rfl).trans ((Category.comp_id _).symm.trans (Category.id_comp _).symm)

instance (φ : R →+* S) : (mapRingHom φ).PreservesZeroMorphisms where
  map_zero _ _ := Matrix.ext fun _ _ ↦ map_zero φ

open scoped Classical in
private theorem mapRingHom_sigmaBicone_π (φ : R →+* S) {J : Type} [Finite J]
    (f : J → Mat R) (j : J) :
    (mapRingHom φ).map ((sigmaBicone f).π j) =
      (sigmaBicone ((mapRingHom φ).obj ∘ f)).π j :=
  Matrix.ext fun p x ↦ by
    by_cases hp : p = ⟨j, x⟩
    · exact (congrArg φ (ite_eq_left hp)).trans ((map_one φ).trans (ite_eq_left hp).symm)
    · exact (congrArg φ (ite_eq_right hp)).trans ((map_zero φ).trans (ite_eq_right hp).symm)

open scoped Classical in
private theorem mapRingHom_sigmaBicone_ι (φ : R →+* S) {J : Type} [Finite J]
    (f : J → Mat R) (j : J) :
    (mapRingHom φ).map ((sigmaBicone f).ι j) =
      (sigmaBicone ((mapRingHom φ).obj ∘ f)).ι j :=
  Matrix.ext fun x p ↦ by
    by_cases hp : p = ⟨j, x⟩
    · exact (congrArg φ (ite_eq_left hp)).trans ((map_one φ).trans (ite_eq_left hp).symm)
    · exact (congrArg φ (ite_eq_right hp)).trans ((map_zero φ).trans (ite_eq_right hp).symm)

/-- `Mat.mapRingHom φ` preserves finite biproducts over any semiring homomorphism `φ`, since
applying `φ` entrywise sends `Mat.sigmaBicone f` to `Mat.sigmaBicone ((mapRingHom φ).obj ∘ f)`. -/
instance instPreservesFiniteBiproductsMapRingHom (φ : R →+* S) :
    PreservesFiniteBiproducts (mapRingHom φ) where
  preserves {J} _ :=
    { preserves {f} :=
        { preserves {b} hb := by
            let u₁ : b.pt ≅ ⨁ f := biproduct.uniqueUpToIso f hb
            let u₂ : (sigmaBicone f).pt ≅ ⨁ f :=
              biproduct.uniqueUpToIso f (isBilimitSigmaBicone f)
            let e : b.pt ≅ (sigmaBicone f).pt := u₁ ≪≫ u₂.symm
            have hu₁_π (j : J) : u₁.inv ≫ b.π j = biproduct.π f j :=
              (Iso.inv_comp_eq u₁).mpr
                ((congrArg (· ≫ biproduct.π f j) (biproduct.uniqueUpToIso_hom f hb)).trans
                  (biproduct.lift_π b.π j)).symm
            have hu₂_π (j : J) : u₂.hom ≫ biproduct.π f j = (sigmaBicone f).π j :=
              (congrArg (· ≫ biproduct.π f j)
                (biproduct.uniqueUpToIso_hom f (isBilimitSigmaBicone f))).trans
                (biproduct.lift_π (sigmaBicone f).π j)
            have he_π (j : J) : e.inv ≫ b.π j = (sigmaBicone f).π j :=
              (Category.assoc u₂.hom u₁.inv (b.π j)).trans
                ((congrArg (u₂.hom ≫ ·) (hu₁_π j)).trans (hu₂_π j))
            have hu₂_ι (j : J) : (sigmaBicone f).ι j ≫ u₂.hom = biproduct.ι f j :=
              ((Iso.comp_inv_eq u₂).mp
                ((congrArg (biproduct.ι f j ≫ ·)
                  (biproduct.uniqueUpToIso_inv f (isBilimitSigmaBicone f))).trans
                  (biproduct.ι_desc (sigmaBicone f).ι j))).symm
            have hu₁_ι (j : J) : biproduct.ι f j ≫ u₁.inv = b.ι j :=
              (congrArg (biproduct.ι f j ≫ ·) (biproduct.uniqueUpToIso_inv f hb)).trans
                (biproduct.ι_desc b.ι j)
            have he_ι (j : J) : (sigmaBicone f).ι j ≫ e.inv = b.ι j :=
              (Category.assoc ((sigmaBicone f).ι j) u₂.hom u₁.inv).symm.trans
                ((congrArg (· ≫ u₁.inv) (hu₂_ι j)).trans (hu₁_ι j))
            exact ⟨{
              isLimit := IsLimit.ofIsoLimit
                (isBilimitSigmaBicone ((mapRingHom φ).obj ∘ f)).isLimit
                (Cone.ext ((mapRingHom φ).mapIso e).symm fun ⟨j⟩ ↦
                  (mapRingHom_sigmaBicone_π φ f j).symm.trans
                    (((mapRingHom φ).map_comp e.inv (b.π j)).symm.trans
                      (congrArg ((mapRingHom φ).map ·) (he_π j))).symm)
              isColimit := IsColimit.ofIsoColimit
                (isBilimitSigmaBicone ((mapRingHom φ).obj ∘ f)).isColimit
                (Cocone.ext ((mapRingHom φ).mapIso e).symm fun ⟨j⟩ ↦
                  (congrArg (· ≫ (mapRingHom φ).map e.inv)
                    (mapRingHom_sigmaBicone_ι φ f j).symm).trans
                    (((mapRingHom φ).map_comp ((sigmaBicone f).ι j) e.inv).symm.trans
                      (congrArg ((mapRingHom φ).map ·) (he_ι j)))) }⟩ } }

/-- `Mat.mapRingHom φ` preserves binary biproducts over any semiring homomorphism `φ`. -/
instance instPreservesBinaryBiproductsMapRingHom (φ : R →+* S) :
    PreservesBinaryBiproducts (mapRingHom φ) :=
  preservesBinaryBiproducts_of_preservesBiproducts (mapRingHom φ)

/-- A semiring isomorphism `e : R ≃+* S` induces an equivalence of categories `Mat R ≌ Mat S`. -/
def mapRingEquiv (e : R ≃+* S) : Mat R ≌ Mat S where
  functor := mapRingHom e.toRingHom
  inverse := mapRingHom e.symm.toRingHom
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦
    (Category.comp_id _).trans
      ((Matrix.ext fun i j ↦ (e.symm_apply_apply (f i j)).symm).trans
        (Category.id_comp ((mapRingHom e.toRingHom ⋙ mapRingHom e.symm.toRingHom).map f)).symm)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦
    (Category.comp_id _).trans
      ((Matrix.ext fun i j ↦ e.apply_symm_apply (f i j)).trans (Category.id_comp _).symm)
  functor_unitIso_comp X :=
    (Category.comp_id _).trans ((mapRingHom e.toRingHom).map_id X)

@[simp]
theorem mapRingEquiv_functor (e : R ≃+* S) :
    (mapRingEquiv e).functor = mapRingHom e.toRingHom := by
  unfold mapRingEquiv
  rfl

@[simp]
theorem mapRingEquiv_inverse (e : R ≃+* S) :
    (mapRingEquiv e).inverse = mapRingHom e.symm.toRingHom := by
  unfold mapRingEquiv
  rfl

end Semiring

section Ring

variable {R S : Type u} [Ring R] [Ring S]

instance (φ : R →+* S) : (mapRingHom φ).Additive where
  map_add := Matrix.ext fun _ _ ↦ map_add φ _ _

end Ring

end MapRingHom

end CategoryTheory.Mat

