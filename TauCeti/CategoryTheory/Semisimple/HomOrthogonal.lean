/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import TauCeti.CategoryTheory.Functor.RingEquivEnd
public import TauCeti.CategoryTheory.Idempotents.Split
public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.CategoryTheory.Linear.Mat
public import TauCeti.CategoryTheory.Linear.SingleObj
public import TauCeti.CategoryTheory.Preadditive.HomOrthogonal
public import TauCeti.CategoryTheory.Preadditive.Mat
public import TauCeti.CategoryTheory.Semisimple.Finite

/-!
# Finite semisimplicity from Hom-orthogonal biproduct decompositions

Combining the abelianization theorem of `TauCeti/CategoryTheory/Preadditive/HomOrthogonal.lean` with
`TauCeti.IsFiniteSemisimpleCategory.of_forall_exists_biproduct` and
`TauCeti.finite_simpleClasses_of_forall_exists_biproduct`, this file shows that a category with
finite biproducts in which every object decomposes as a finite biproduct of a Hom-orthogonal family
`X : ι → C` with division endomorphism rings (or scalar endomorphism algebras `End (X i) ≃ₐ[K] K`
over a field `K`) is finite semisimple, and has finitely many simple isomorphism classes when `ι`
is finite.

We apply this criterion to the additive envelope `Mat_ C` of any Hom-orthogonal preadditive
category `C` whose objects have division endomorphism rings, and in particular to
`Mat_ (SingleObj D)` for a division ring `D` (obtaining canonical `Abelian`,
`IsIdempotentComplete`, `IsFiniteSemisimpleCategory`, and `Finite (SimpleClasses _)` instances,
along with finite-dimensional Hom spaces over a field `K`).

Finally, we establish sharpness of the two structural hypotheses over any field `K`:

* Dropping `HomOrthogonal`: the matrix category of the two-object `K`-linear $A_2$ quiver
  ($0 \to 1$) is `K`-linear, idempotent complete, has finite-dimensional Hom spaces, and decomposes
  every object as a finite biproduct of two objects with scalar endomorphism algebras `K`, yet has a
  morphism that is both monomorphic and epimorphic without being an isomorphism, so it admits no
  `Abelian` structure.
* Dropping division endomorphism rings: `Mat_ (SingleObj (DualNumber K))` is `K`-linear, idempotent
  complete, has finite-dimensional Hom spaces, and decomposes every object as a finite biproduct of
  a singleton Hom-orthogonal family, yet multiplication by `ε` has no kernel, so it admits no
  `Abelian` structure.

## Main results

* `CategoryTheory.HomOrthogonal.isFiniteSemisimpleCategory`,
  `CategoryTheory.HomOrthogonal.isFiniteSemisimpleCategory_of_algEquiv`: finite semisimplicity from
  Hom-orthogonal biproduct decompositions.
* `CategoryTheory.HomOrthogonal.finite_simpleClasses`,
  `CategoryTheory.HomOrthogonal.finite_simpleClasses_of_algEquiv`: finiteness of `SimpleClasses C`
  when the indexing type `ι` is finite.
* `CategoryTheory.Mat_.abelianOfHomOrthogonal`,
  `CategoryTheory.Mat_.isIdempotentComplete_of_homOrthogonal`,
  `CategoryTheory.Mat_.isFiniteSemisimpleCategory_of_homOrthogonal`,
  `CategoryTheory.Mat_.finite_simpleClasses_of_homOrthogonal`: abelian and semisimple structure on
  `Mat_ C` for a Hom-orthogonal preadditive category `C` with division endomorphism rings.
* `CategoryTheory.Mat_.singleObjAbelian`, `CategoryTheory.Mat_.singleObj_isIdempotentComplete`,
  `CategoryTheory.Mat_.singleObj_isFiniteSemisimpleCategory`,
  `CategoryTheory.Mat_.singleObj_finite_simpleClasses`: canonical instances on
  `Mat_ (SingleObj D)` for a division ring `D`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§1.3, 1.8.
* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2], Chapter 1.
-/

public section

universe t w v u

namespace CategoryTheory.HomOrthogonal

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]
variable {ι : Type w} {X : ι → C}

/-- An abelian category with finite biproducts in which every object decomposes as a finite
biproduct of a Hom-orthogonal family with division endomorphism rings is finite semisimple. -/
theorem isFiniteSemisimpleCategory [∀ i, Nontrivial (End (X i))] (o : HomOrthogonal X)
    (hunit : ∀ i (f : End (X i)), f ≠ 0 → IsUnit f)
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) :
    TauCeti.IsFiniteSemisimpleCategory C := by
  have _ (i : ι) : Simple (X i) := o.simple hunit hgen i
  exact TauCeti.IsFiniteSemisimpleCategory.of_forall_exists_biproduct X hgen

/-- If in addition the indexing type `ι` is finite, `SimpleClasses C` is finite. -/
theorem finite_simpleClasses [Finite ι] [∀ i, Nontrivial (End (X i))] (o : HomOrthogonal X)
    (hunit : ∀ i (f : End (X i)), f ≠ 0 → IsUnit f)
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) :
    Finite (TauCeti.SimpleClasses C) := by
  have _ : TauCeti.IsFiniteSemisimpleCategory C := o.isFiniteSemisimpleCategory hunit hgen
  exact TauCeti.finite_simpleClasses_of_forall_exists_biproduct X hgen

/-- Over a field `K`, an abelian `K`-linear category with finite biproducts in which every object
decomposes as a finite biproduct of a Hom-orthogonal family `X` with `End (X i) ≃ₐ[K] K` is finite
semisimple. -/
theorem isFiniteSemisimpleCategory_of_algEquiv (o : HomOrthogonal X) (K : Type t) [Field K]
    [Linear K C] (hend : ∀ i, Nonempty (End (X i) ≃ₐ[K] K))
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) :
    TauCeti.IsFiniteSemisimpleCategory C := by
  have _ (i : ι) : Simple (X i) := o.simple_of_algEquiv K hend hgen i
  exact TauCeti.IsFiniteSemisimpleCategory.of_forall_exists_biproduct X hgen

/-- Over a field `K`, if `ι` is finite and every object decomposes as a finite biproduct of a
Hom-orthogonal family `X` with `End (X i) ≃ₐ[K] K`, then `SimpleClasses C` is finite. -/
theorem finite_simpleClasses_of_algEquiv [Finite ι] (o : HomOrthogonal X) (K : Type t) [Field K]
    [Linear K C] (hend : ∀ i, Nonempty (End (X i) ≃ₐ[K] K))
    (hgen : ∀ Y : C, ∃ (α : Type) (_ : Finite α) (a : α → ι),
      Nonempty (Y ≅ ⨁ fun p ↦ X (a p))) :
    Finite (TauCeti.SimpleClasses C) := by
  have _ : TauCeti.IsFiniteSemisimpleCategory C :=
    o.isFiniteSemisimpleCategory_of_algEquiv K hend hgen
  exact TauCeti.finite_simpleClasses_of_forall_exists_biproduct X hgen

end CategoryTheory.HomOrthogonal

namespace CategoryTheory.Mat_

open Limits

section HomOrthogonalBase

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- If the objects of `C` are pairwise Hom-orthogonal, so are their images under
`Mat_.embedding C`. -/
theorem homOrthogonal_embedding (o : HomOrthogonal (id : C → C)) :
    HomOrthogonal (embedding C).obj := fun i j hij ↦
  have _ : Subsingleton (i ⟶ j) := o hij
  (Functor.FullyFaithful.ofFullyFaithful (embedding C)).homEquiv.symm.subsingleton

private theorem end_nontrivial_embedding [∀ c : C, Nontrivial (End c)] (c : C) :
    Nontrivial (End ((embedding C).obj c)) :=
  ((Functor.FullyFaithful.ofFullyFaithful (embedding C)).ringEquivEnd c).symm.toEquiv.nontrivial

private theorem end_isUnit_embedding (hunit : ∀ (c : C) (f : End c), f ≠ 0 → IsUnit f)
    (c : C) (f : End ((embedding C).obj c)) (hf : f ≠ 0) : IsUnit f := by
  let e := (Functor.FullyFaithful.ofFullyFaithful (embedding C)).ringEquivEnd c
  have hne : e.symm f ≠ 0 := by simpa using hf
  simpa using (hunit c (e.symm f) hne).map e.toMonoidHom

private theorem exists_biproduct_embedding (M : Mat_ C) :
    ∃ (α : Type) (_ : Finite α) (a : α → C),
      Nonempty (M ≅ ⨁ fun p ↦ (embedding C).obj (a p)) :=
  ⟨M.ι, inferInstance, M.X, ⟨M.isoBiproductEmbedding⟩⟩

/-- When the objects of a preadditive category `C` are pairwise Hom-orthogonal with division
endomorphism rings, the matrix category `Mat_ C` is abelian. -/
@[instance_reducible]
noncomputable def abelianOfHomOrthogonal [∀ c : C, Nontrivial (End c)]
    (o : HomOrthogonal (id : C → C)) (hunit : ∀ (c : C) (f : End c), f ≠ 0 → IsUnit f) :
    Abelian (Mat_ C) :=
  let _ (c : C) : Nontrivial (End ((embedding C).obj c)) := end_nontrivial_embedding c
  (homOrthogonal_embedding o).abelian (end_isUnit_embedding hunit) exists_biproduct_embedding

/-- When the objects of `C` are pairwise Hom-orthogonal with division endomorphism rings, `Mat_ C`
is idempotent complete. -/
theorem isIdempotentComplete_of_homOrthogonal [∀ c : C, Nontrivial (End c)]
    (o : HomOrthogonal (id : C → C)) (hunit : ∀ (c : C) (f : End c), f ≠ 0 → IsUnit f) :
    IsIdempotentComplete (Mat_ C) :=
  let _ (c : C) : Nontrivial (End ((embedding C).obj c)) := end_nontrivial_embedding c
  (homOrthogonal_embedding o).isIdempotentComplete (end_isUnit_embedding hunit)
    exists_biproduct_embedding

/-- When `Mat_ C` is abelian and the objects of `C` are pairwise Hom-orthogonal with division
endomorphism rings, `Mat_ C` is finite semisimple. -/
theorem isFiniteSemisimpleCategory_of_homOrthogonal [hab : Abelian (Mat_ C)]
    [∀ c : C, Nontrivial (End c)] (o : HomOrthogonal (id : C → C))
    (hunit : ∀ (c : C) (f : End c), f ≠ 0 → IsUnit f) :
    TauCeti.IsFiniteSemisimpleCategory (Mat_ C) := by
  have _ : HasBinaryBiproducts (Mat_ C) := hasBinaryBiproducts_of_finite_biproducts _
  let pre₀ : Preadditive (Mat_ C) := inferInstance
  have hsub : Subsingleton (Preadditive (Mat_ C)) := inferInstance
  rcases hab with @⟨pre, hnm, hne, hfp, hk, hck⟩
  obtain rfl : pre = pre₀ := @Subsingleton.elim _ hsub _ _
  let _ : Abelian (Mat_ C) := @Abelian.mk _ _ pre₀ hnm hne hfp hk hck
  have _ (c : C) : Nontrivial (End ((embedding C).obj c)) := end_nontrivial_embedding c
  exact (homOrthogonal_embedding o).isFiniteSemisimpleCategory (end_isUnit_embedding hunit)
    exists_biproduct_embedding

/-- When in addition `C` has finitely many objects, `SimpleClasses (Mat_ C)` is finite. -/
theorem finite_simpleClasses_of_homOrthogonal [hab : Abelian (Mat_ C)] [Finite C]
    [∀ c : C, Nontrivial (End c)] (o : HomOrthogonal (id : C → C))
    (hunit : ∀ (c : C) (f : End c), f ≠ 0 → IsUnit f) :
    Finite (TauCeti.SimpleClasses (Mat_ C)) := by
  have _ : HasBinaryBiproducts (Mat_ C) := hasBinaryBiproducts_of_finite_biproducts _
  let pre₀ : Preadditive (Mat_ C) := inferInstance
  have hsub : Subsingleton (Preadditive (Mat_ C)) := inferInstance
  rcases hab with @⟨pre, hnm, hne, hfp, hk, hck⟩
  obtain rfl : pre = pre₀ := @Subsingleton.elim _ hsub _ _
  let _ : Abelian (Mat_ C) := @Abelian.mk _ _ pre₀ hnm hne hfp hk hck
  have _ : TauCeti.IsFiniteSemisimpleCategory (Mat_ C) :=
    isFiniteSemisimpleCategory_of_homOrthogonal o hunit
  exact TauCeti.finite_simpleClasses_of_forall_exists_biproduct
    (embedding C).obj exists_biproduct_embedding

end HomOrthogonalBase

section SingleObj

/-- For any division ring `D`, the matrix category `Mat_ (SingleObj D)` is abelian. -/
noncomputable instance singleObjAbelian (D : Type u) [DivisionRing D] :
    Abelian (Mat_ (SingleObj D)) :=
  abelianOfHomOrthogonal Subsingleton.pairwise fun _ _ hf ↦ SingleObj.isUnit_end_of_ne_zero hf

/-- For any division ring `D`, `Mat_ (SingleObj D)` is idempotent complete. -/
instance singleObj_isIdempotentComplete (D : Type u) [DivisionRing D] :
    IsIdempotentComplete (Mat_ (SingleObj D)) :=
  isIdempotentComplete_of_homOrthogonal Subsingleton.pairwise
    fun _ _ hf ↦ SingleObj.isUnit_end_of_ne_zero hf

/-- For any division ring `D`, `Mat_ (SingleObj D)` is a finite semisimple category. -/
instance singleObj_isFiniteSemisimpleCategory (D : Type u) [DivisionRing D] :
    TauCeti.IsFiniteSemisimpleCategory (Mat_ (SingleObj D)) :=
  isFiniteSemisimpleCategory_of_homOrthogonal Subsingleton.pairwise
    fun _ _ hf ↦ SingleObj.isUnit_end_of_ne_zero hf

/-- For any division ring `D`, `Mat_ (SingleObj D)` has finitely many simple isomorphism classes. -/
instance singleObj_finite_simpleClasses (D : Type u) [DivisionRing D] :
    Finite (TauCeti.SimpleClasses (Mat_ (SingleObj D))) :=
  finite_simpleClasses_of_homOrthogonal Subsingleton.pairwise
    fun _ _ hf ↦ SingleObj.isUnit_end_of_ne_zero hf

end SingleObj

end CategoryTheory.Mat_

/-! ### Sharpness of hypotheses -/

section Sharpness

open CategoryTheory CategoryTheory.Limits DualNumber

/-! #### Counterexample 1: dropping `HomOrthogonal`

The two-object `K`-linear $A_2$ quiver ($0 \to 1$) has scalar endomorphisms on both objects, and its
matrix category `Mat_ (ArrowQuiver K)` is `K`-linear, idempotent complete, has finite-dimensional
Hom spaces, and decomposes every object as a finite biproduct of those two embedded objects, yet it
is not abelian because the generating arrow `0 → 1` is both monomorphic and epimorphic without being
invertible. -/

private structure ArrowQuiver (K : Type u) : Type where
  val : Bool

private def arrowHomSubmodule (K : Type u) [Field K] (b c : Bool) : Submodule K K :=
  if b ≤ c then ⊤ else ⊥

private theorem mul_mem_arrowHomSubmodule {K : Type u} [Field K] {a b c : Bool}
    (f : ↥(arrowHomSubmodule K a b)) (g : ↥(arrowHomSubmodule K b c)) :
    f.1 * g.1 ∈ arrowHomSubmodule K a c := by
  by_cases hac : a ≤ c
  · simp [arrowHomSubmodule, hac]
  · have h : ¬ a ≤ b ∨ ¬ b ≤ c := by
      by_contra! hle
      exact hac (le_trans hle.1 hle.2)
    rcases h with hab | hbc
    · have hf : f.1 = 0 := by simpa [arrowHomSubmodule, hab] using f.2
      simp [arrowHomSubmodule, hac, hf]
    · have hg : g.1 = 0 := by simpa [arrowHomSubmodule, hbc] using g.2
      simp [arrowHomSubmodule, hac, hg]

private instance (K : Type u) [Field K] : Category.{u} (ArrowQuiver K) where
  Hom X Y := ↥(arrowHomSubmodule K X.val Y.val)
  id X := ⟨1, by simp [arrowHomSubmodule]⟩
  comp f g := ⟨f.1 * g.1, mul_mem_arrowHomSubmodule f g⟩
  id_comp f := Subtype.ext (one_mul f.1)
  comp_id f := Subtype.ext (mul_one f.1)
  assoc f g h := Subtype.ext (mul_assoc f.1 g.1 h.1)

private instance (K : Type u) [Field K] : Preadditive (ArrowQuiver K) where
  homGroup X Y := inferInstanceAs (AddCommGroup ↥(arrowHomSubmodule K X.val Y.val))
  add_comp _ _ _ f f' g := Subtype.ext (add_mul f.1 f'.1 g.1)
  comp_add _ _ _ f g g' := Subtype.ext (mul_add f.1 g.1 g'.1)

private instance (K : Type u) [Field K] : Linear K (ArrowQuiver K) where
  homModule X Y := inferInstanceAs (Module K ↥(arrowHomSubmodule K X.val Y.val))
  smul_comp _ _ _ r f g := Subtype.ext (smul_mul_assoc r f.1 g.1)
  comp_smul _ _ _ f r g := Subtype.ext (mul_smul_comm r f.1 g.1)

private instance (K : Type u) [Field K] (X Y : ArrowQuiver K) :
    Module.Finite K (X ⟶ Y) :=
  inferInstanceAs (Module.Finite K ↥(arrowHomSubmodule K X.val Y.val))

private structure DiagQuiver (K : Type u) : Type where
  val : Bool

private def diagHomSubmodule (K : Type u) [Field K] (b c : Bool) : Submodule K K :=
  if b = c then ⊤ else ⊥

private theorem mul_mem_diagHomSubmodule {K : Type u} [Field K] {a b c : Bool}
    (f : ↥(diagHomSubmodule K a b)) (g : ↥(diagHomSubmodule K b c)) :
    f.1 * g.1 ∈ diagHomSubmodule K a c := by
  by_cases hac : a = c
  · simp [diagHomSubmodule, hac]
  · by_cases hab : a = b
    · have hbc : b ≠ c := fun h ↦ hac (hab.trans h)
      have hg : g.1 = 0 := by simpa [diagHomSubmodule, hbc] using g.2
      simp [diagHomSubmodule, hac, hg]
    · have hf : f.1 = 0 := by simpa [diagHomSubmodule, hab] using f.2
      simp [diagHomSubmodule, hac, hf]

private instance (K : Type u) [Field K] : Category.{u} (DiagQuiver K) where
  Hom X Y := ↥(diagHomSubmodule K X.val Y.val)
  id X := ⟨1, by simp [diagHomSubmodule]⟩
  comp f g := ⟨f.1 * g.1, mul_mem_diagHomSubmodule f g⟩
  id_comp f := Subtype.ext (one_mul f.1)
  comp_id f := Subtype.ext (mul_one f.1)
  assoc f g h := Subtype.ext (mul_assoc f.1 g.1 h.1)

private instance (K : Type u) [Field K] : Preadditive (DiagQuiver K) where
  homGroup X Y := inferInstanceAs (AddCommGroup ↥(diagHomSubmodule K X.val Y.val))
  add_comp _ _ _ f f' g := Subtype.ext (add_mul f.1 f'.1 g.1)
  comp_add _ _ _ f g g' := Subtype.ext (mul_add f.1 g.1 g'.1)

private def diagQuiverEndRingEquiv {K : Type u} [Field K] (X : DiagQuiver K) :
    End X ≃+* K where
  toFun f := f.asHom.1
  invFun r := End.of ⟨r, by simp [diagHomSubmodule]⟩
  left_inv f := End.ext (Subtype.ext rfl)
  right_inv _ := rfl
  map_mul' f g := mul_comm g.asHom.1 f.asHom.1
  map_add' _ _ := rfl

private theorem diagQuiver_isIdempotentComplete (K : Type u) [Field K] :
    IsIdempotentComplete (Mat_ (DiagQuiver K)) := by
  have _ (X : DiagQuiver K) : Nontrivial (End X) := (diagQuiverEndRingEquiv X).toEquiv.nontrivial
  refine Mat_.isIdempotentComplete_of_homOrthogonal (fun X Y hXY ↦ ?_) (fun X f hf ↦ ?_)
  · have hval : X.val ≠ Y.val := fun h ↦ hXY (by cases X; cases Y; cases h; rfl)
    refine ⟨fun f g ↦ Subtype.ext ?_⟩
    have hf0 : f.1 = 0 := by simpa [diagHomSubmodule, hval] using f.2
    have hg0 : g.1 = 0 := by simpa [diagHomSubmodule, hval] using g.2
    exact hf0.trans hg0.symm
  · let e := diagQuiverEndRingEquiv X
    have hne : e f ≠ 0 := by simpa using hf
    simpa using (isUnit_iff_ne_zero.mpr hne).map e.symm.toMonoidHom

@[simp]
private theorem ArrowQuiver.comp_val {K : Type u} [Field K] {X Y Z : ArrowQuiver K}
    (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).1 = f.1 * g.1 :=
  rfl

private theorem arrowQuiver_hom_eq_zero {K : Type u} [Field K] {X Y : ArrowQuiver K}
    (hX : X.val = true) (hY : Y.val = false) (f : X ⟶ Y) : f = 0 := by
  have htf : ¬ (true ≤ false) := by decide
  exact Subtype.ext (by simpa [arrowHomSubmodule, hX, hY, htf] using f.2)

private def arrowToDiag (K : Type u) [Field K] : ArrowQuiver K ⥤ DiagQuiver K where
  obj X := ⟨X.val⟩
  map {X Y} f := if h : X.val = Y.val then ⟨f.1, by simp [diagHomSubmodule, h]⟩ else 0
  map_id := fun ⟨b⟩ ↦ by cases b <;> exact Subtype.ext rfl
  map_comp := fun {X Y Z} f g ↦ by
    rcases X with ⟨a⟩; rcases Y with ⟨b⟩; rcases Z with ⟨c⟩
    cases a <;> cases b <;> cases c
    · exact Subtype.ext rfl
    · simp
    · rw [arrowQuiver_hom_eq_zero rfl rfl g, comp_zero]; apply Subtype.ext; simp
    · simp
    · simp
    · rw [arrowQuiver_hom_eq_zero rfl rfl f, zero_comp]; apply Subtype.ext; simp
    · simp
    · exact Subtype.ext rfl

private instance (K : Type u) [Field K] : (arrowToDiag K).Additive where
  map_add := fun {X Y} f g ↦ by
    rcases X with ⟨a⟩; rcases Y with ⟨b⟩
    cases a <;> cases b <;> apply Subtype.ext
    · rfl
    · change (0 : K) = 0 + 0; simp
    · change (0 : K) = 0 + 0; simp
    · rfl

private def diagToArrow (K : Type u) [Field K] : DiagQuiver K ⥤ ArrowQuiver K where
  obj X := ⟨X.val⟩
  map {X Y} f := ⟨f.1, by
    by_cases h : X.val = Y.val
    · simp [arrowHomSubmodule, h]
    · have hf : f.1 = 0 := by simpa [diagHomSubmodule, h] using f.2
      simp [arrowHomSubmodule, hf]⟩

private instance (K : Type u) [Field K] : (diagToArrow K).Additive where

private theorem arrowQuiver_isIdempotentComplete (K : Type u) [Field K] :
    IsIdempotentComplete (Mat_ (ArrowQuiver K)) := by
  have _ := diagQuiver_isIdempotentComplete K
  refine ⟨fun M p hp ↦ ?_⟩
  let πF := (arrowToDiag K).mapMat_
  let ιF := (diagToArrow K).mapMat_
  let pD : πF.obj M ⟶ πF.obj M := πF.map p
  have hpD : pD ≫ pD = pD := by simp [pD, ← CategoryTheory.Functor.map_comp, hp]
  obtain ⟨Y, iD, rD, hirD, hriD⟩ := IsIdempotentComplete.idempotents_split (πF.obj M) pD hpD
  have hir' : ιF.map iD ≫ ιF.map rD = 𝟙 (ιF.obj Y) := by
    rw [← ιF.map_comp, hirD, ιF.map_id]
  have hri' : ιF.map rD ≫ ιF.map iD = ιF.map pD := by rw [← ιF.map_comp, hriD]
  let e : M ⟶ M := ιF.map pD
  have he : e ≫ e = e := by
    change ιF.map pD ≫ ιF.map pD = ιF.map pD
    rw [← ιF.map_comp, hpD]
  have hsplit_e : ∃ (Z : Mat_ (ArrowQuiver K)) (i : Z ⟶ M) (r : M ⟶ Z),
      i ≫ r = 𝟙 Z ∧ r ≫ i = e :=
    ⟨ιF.obj Y, ιF.map iD, ιF.map rD, hir', hri'⟩
  let u : M ⟶ M := p - e
  have hu_diag (i j : M.ι) (hij : (M.X i).val = (M.X j).val) : u i j = 0 := by
    apply Subtype.ext
    change (p i j).1 - ((arrowToDiag K).map (p i j)).1 = 0
    simp [arrowToDiag, hij]
  have hu : u ≫ u = 0 := by
    ext i k
    rw [Mat_.comp_apply, Mat_.zero_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    cases hb1 : (M.X i).val <;> cases hb2 : (M.X j).val <;> cases hb3 : (M.X k).val
    · rw [hu_diag i j (hb1.trans hb2.symm), zero_comp]
    · rw [hu_diag i j (hb1.trans hb2.symm), zero_comp]
    · rw [arrowQuiver_hom_eq_zero hb2 hb3 (u j k), comp_zero]
    · rw [hu_diag j k (hb2.trans hb3.symm), comp_zero]
    · rw [hu_diag j k (hb2.trans hb3.symm), comp_zero]
    · rw [arrowQuiver_hom_eq_zero hb1 hb2 (u i j), zero_comp]
    · rw [hu_diag i j (hb1.trans hb2.symm), zero_comp]
    · rw [hu_diag i j (hb1.trans hb2.symm), zero_comp]
  have heu : e + u = p := add_sub_cancel e p
  exact heu ▸ TauCeti.exists_split_add_of_sq_eq_zero he hu (heu.symm ▸ hp) hsplit_e

private def arrowQuiverEndAlgEquiv {K : Type u} [Field K] (b : Bool) :
    End (⟨b⟩ : ArrowQuiver K) ≃ₐ[K] K where
  toFun f := f.asHom.1
  invFun r := End.of ⟨r, by simp [arrowHomSubmodule]⟩
  left_inv _ := End.ext (Subtype.ext rfl)
  right_inv _ := rfl
  map_mul' f g := mul_comm g.asHom.1 f.asHom.1
  map_add' _ _ := rfl
  commutes' r := by
    change (r • (1 : K)) = r
    exact mul_one r

private abbrev arrowGen (K : Type u) [Field K] :
    (⟨false⟩ : ArrowQuiver K) ⟶ ⟨true⟩ :=
  ⟨1, by simp [arrowHomSubmodule]⟩

private theorem arrowQuiver_comp_map_gen {K : Type u} [Field K] {M : Mat_ (ArrowQuiver K)}
    (h : M ⟶ (Mat_.embedding (ArrowQuiver K)).obj ⟨false⟩) (i : M.ι) :
    ((h ≫ (Mat_.embedding (ArrowQuiver K)).map (arrowGen K)) i default).1 = (h i default).1 := by
  have hsum : (h ≫ (Mat_.embedding (ArrowQuiver K)).map (arrowGen K)) i default =
      h i default ≫ ((Mat_.embedding (ArrowQuiver K)).map (arrowGen K)) default default := by
    rw [Mat_.comp_apply]
    exact Finset.sum_eq_single_of_mem default (Finset.mem_univ _)
      fun q _ hq ↦ (hq (Subsingleton.elim _ _)).elim
  rw [congrArg Subtype.val hsum]
  exact mul_one (h i default).1

private theorem arrowQuiver_map_gen_comp {K : Type u} [Field K] {N : Mat_ (ArrowQuiver K)}
    (k : (Mat_.embedding (ArrowQuiver K)).obj ⟨true⟩ ⟶ N) (j : N.ι) :
    (((Mat_.embedding (ArrowQuiver K)).map (arrowGen K) ≫ k) default j).1 = (k default j).1 := by
  have hsum : ((Mat_.embedding (ArrowQuiver K)).map (arrowGen K) ≫ k) default j =
      ((Mat_.embedding (ArrowQuiver K)).map (arrowGen K)) default default ≫ k default j := by
    rw [Mat_.comp_apply]
    exact Finset.sum_eq_single_of_mem default (Finset.mem_univ _)
      fun q _ hq ↦ (hq (Subsingleton.elim _ _)).elim
  rw [congrArg Subtype.val hsum]
  exact one_mul (k default j).1

private theorem arrowQuiver_not_abelian (K : Type u) [Field K]
    (hab : Abelian (Mat_ (ArrowQuiver K))) : False := by
  have _ : HasBinaryBiproducts (Mat_ (ArrowQuiver K)) :=
    hasBinaryBiproducts_of_finite_biproducts _
  let pre₀ : Preadditive (Mat_ (ArrowQuiver K)) := inferInstance
  have hsub : Subsingleton (Preadditive (Mat_ (ArrowQuiver K))) := inferInstance
  rcases hab with @⟨pre, hnm, _, _, _, _⟩
  obtain rfl : pre = pre₀ := @Subsingleton.elim _ hsub _ _
  have _ := hnm
  let P (b : Bool) : Mat_ (ArrowQuiver K) := (Mat_.embedding (ArrowQuiver K)).obj ⟨b⟩
  let g : P false ⟶ P true := (Mat_.embedding (ArrowQuiver K)).map (arrowGen K)
  have _ : Mono g := ⟨fun h₁ h₂ heq ↦ by
    ext i j
    obtain rfl : j = default := Subsingleton.elim _ _
    exact Subtype.ext ((arrowQuiver_comp_map_gen h₁ i).symm.trans
      ((congrArg (fun m : _ ⟶ P true ↦ (m i default).1) heq).trans
        (arrowQuiver_comp_map_gen h₂ i)))⟩
  have _ : Epi g := ⟨fun k₁ k₂ heq ↦ by
    ext i j
    obtain rfl : i = default := Subsingleton.elim _ _
    exact Subtype.ext ((arrowQuiver_map_gen_comp k₁ j).symm.trans
      ((congrArg (fun m : P false ⟶ _ ↦ (m default j).1) heq).trans
        (arrowQuiver_map_gen_comp k₂ j)))⟩
  let nm : NormalMono g := Classical.choice (IsNormalMonoCategory.normalMonoOfMono g)
  have hnm0 : nm.g = 0 := (cancel_epi g).1 (by simp [nm.w])
  obtain ⟨r, hrg⟩ := NormalMono.lift' g (𝟙 (P true)) (by simp [hnm0])
  have hr0 : (r default default).1 = 0 :=
    congrArg Subtype.val (arrowQuiver_hom_eq_zero rfl rfl (r default default))
  have hcomp0 : ((r ≫ g) default default).1 = 0 :=
    (arrowQuiver_comp_map_gen r default).trans hr0
  have hid : ((r ≫ g) default default).1 = 1 := by
    have h1 := congrArg (fun m : P true ⟶ P true ↦ (m default default).1) hrg
    have h2 : ((𝟙 (P true) : P true ⟶ P true) default default).1 = 1 := by
      rw [Mat_.id_apply_self]
      rfl
    exact h1.trans h2
  exact zero_ne_one (hcomp0.symm.trans hid)

/-- Sharpness of `HomOrthogonal`: over any field `K`, `Mat_ (ArrowQuiver K)` is `K`-linear,
idempotent complete, has finite-dimensional Hom spaces, and decomposes every object as a finite
biproduct of two objects with endomorphism `K`-algebras isomorphic to `K`, yet admits no `Abelian`
structure. -/
example (K : Type u) [Field K] :
    let P : Bool → Mat_ (ArrowQuiver K) := fun b ↦ (Mat_.embedding (ArrowQuiver K)).obj ⟨b⟩
    (∀ b, Nonempty (End (P b) ≃ₐ[K] K)) ∧
      (∀ M : Mat_ (ArrowQuiver K), ∃ (α : Type) (_ : Finite α) (a : α → Bool),
        Nonempty (M ≅ ⨁ fun p ↦ P (a p))) ∧
      (∀ M N : Mat_ (ArrowQuiver K), FiniteDimensional K (M ⟶ N)) ∧
      IsIdempotentComplete (Mat_ (ArrowQuiver K)) ∧
      IsEmpty (Abelian (Mat_ (ArrowQuiver K))) := by
  intro P
  refine ⟨fun b ↦ ?_, fun M ↦ ⟨M.ι, inferInstance, fun p ↦ (M.X p).val, ⟨M.isoBiproductEmbedding⟩⟩,
    fun M N ↦ inferInstance, arrowQuiver_isIdempotentComplete K,
    ⟨arrowQuiver_not_abelian K⟩⟩
  let eF := AlgEquiv.ofBijective
    ((Mat_.embedding (ArrowQuiver K)).mapEndAlgHom K ⟨b⟩)
    ((Mat_.embedding (ArrowQuiver K)).mapEndAlgHom_bijective K ⟨b⟩
      (Functor.FullyFaithful.ofFullyFaithful (Mat_.embedding (ArrowQuiver K))).homEquiv.bijective)
  exact ⟨eF.symm.trans (arrowQuiverEndAlgEquiv b)⟩

/-! #### Counterexample 2: dropping division/scalar endomorphisms

For `DualNumber K` over a field `K`, `Mat_ (SingleObj (DualNumber K))` is `K`-linear, idempotent
complete, has finite-dimensional Hom spaces, and decomposes every object as a finite biproduct of a
singleton Hom-orthogonal family, yet multiplication by `ε` has no kernel, so it admits no `Abelian`
structure. -/

private instance (K : Type u) [Field K] : SMulCommClass K (DualNumber K) (DualNumber K) :=
  ⟨fun _ _ _ ↦ by ext <;> simp [mul_add, smul_eq_mul, mul_left_comm]⟩

private instance (K : Type u) [Field K] : IsScalarTower K (DualNumber K) (DualNumber K) :=
  ⟨fun _ _ _ ↦ by ext <;> simp [mul_add, smul_eq_mul, mul_assoc]⟩

private def dualNumberLinearEquivProd (K : Type u) [CommSemiring K] :
    DualNumber K ≃ₗ[K] K × K where
  toFun x := (x.fst, x.snd)
  invFun p := TrivSqZeroExt.inl p.1 + TrivSqZeroExt.inr p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := TrivSqZeroExt.inl_fst_add_inr_snd_eq x
  right_inv p := by ext <;> simp

private instance (K : Type u) [Field K] : Module.Finite K (DualNumber K) :=
  Module.Finite.equiv (dualNumberLinearEquivProd K).symm

private abbrev homVal {A : Type u} {x y : SingleObj A} (f : x ⟶ y) : A :=
  f

private theorem dualNumber_mat_isIdempotentComplete (K : Type u) [Field K] :
    IsIdempotentComplete (Mat_ (SingleObj (DualNumber K))) := by
  refine ⟨fun M p hp ↦ ?_⟩
  let πF := (SingleObj.mapHom (DualNumber K) K
    (TrivSqZeroExt.fstHom K K K).toRingHom.toMonoidHom).mapMat_
  let ιF := (SingleObj.mapHom K (DualNumber K)
    (TrivSqZeroExt.inlAlgHom K K K).toRingHom.toMonoidHom).mapMat_
  let pK : πF.obj M ⟶ πF.obj M := πF.map p
  have hpK : pK ≫ pK = pK := by simp [pK, ← CategoryTheory.Functor.map_comp, hp]
  obtain ⟨Y, iK, rK, hirK, hriK⟩ := IsIdempotentComplete.idempotents_split (πF.obj M) pK hpK
  have hir' : ιF.map iK ≫ ιF.map rK = 𝟙 (ιF.obj Y) := by
    rw [← ιF.map_comp, hirK, ιF.map_id]
  have hri' : ιF.map rK ≫ ιF.map iK = ιF.map pK := by
    rw [← ιF.map_comp, hriK]
  have he' : ιF.map pK ≫ ιF.map pK = ιF.map pK := by
    rw [← ιF.map_comp, hpK]
  let e : M ⟶ M := ιF.map pK
  have he : e ≫ e = e := he'
  have hsplit_e : ∃ (Z : Mat_ (SingleObj (DualNumber K))) (i : Z ⟶ M) (r : M ⟶ Z),
      i ≫ r = 𝟙 Z ∧ r ≫ i = e :=
    ⟨ιF.obj Y, ιF.map iK, ιF.map rK, hir', hri'⟩
  let u : M ⟶ M := p - e
  have hu_fst (i j : M.ι) : (homVal (u i j)).fst = 0 := by
    change (homVal (p i j)).fst - (TrivSqZeroExt.inl (homVal (p i j)).fst : DualNumber K).fst = 0
    simp
  have hu : u ≫ u = 0 := by
    ext i k
    change (∑ j : M.ι, homVal (u j k) * homVal (u i j)) = (0 : DualNumber K)
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    ext <;> simp [hu_fst]
  have heu : e + u = p := add_sub_cancel e p
  exact heu ▸ TauCeti.exists_split_add_of_sq_eq_zero he hu (heu.symm ▸ hp) hsplit_e

private theorem dualNumber_fst_eq_zero_of_comp_eps {K : Type u} [Field K]
    {M : Mat_ (SingleObj (DualNumber K))}
    (ι : M ⟶ (Mat_.embedding (SingleObj (DualNumber K))).obj (SingleObj.star (DualNumber K)))
    (h0 : ι ≫ (Mat_.embedding (SingleObj (DualNumber K))).map (ε : DualNumber K) =
      (0 : M ⟶ (Mat_.embedding (SingleObj (DualNumber K))).obj (SingleObj.star (DualNumber K))))
    (j : M.ι) : (homVal (ι j default)).fst = 0 := by
  let P := (Mat_.embedding (SingleObj (DualNumber K))).obj (SingleObj.star (DualNumber K))
  let g : P ⟶ P := (Mat_.embedding (SingleObj (DualNumber K))).map
    ((ε : DualNumber K) : SingleObj.star (DualNumber K) ⟶ SingleObj.star (DualNumber K))
  have hj0 : homVal ((ι ≫ g) j default) = 0 :=
    congrArg (fun m : M ⟶ P ↦ homVal (m j default)) h0
  have hsum : (ι ≫ g) j default = ι j default ≫ g default default := by
    rw [Mat_.comp_apply]
    exact Finset.sum_eq_single_of_mem default (Finset.mem_univ _)
      fun q _ hq ↦ (hq (Subsingleton.elim _ _)).elim
  have hmul : (ε : DualNumber K) * homVal (ι j default) = 0 := by
    simpa [g, Mat_.embedding, homVal, SingleObj.comp_as_mul] using hsum.symm.trans hj0
  simpa using congrArg TrivSqZeroExt.snd hmul

private theorem dualNumber_mat_not_abelian (K : Type u) [Field K]
    (hab : Abelian (Mat_ (SingleObj (DualNumber K)))) : False := by
  classical
  have _ : HasBinaryBiproducts (Mat_ (SingleObj (DualNumber K))) :=
    hasBinaryBiproducts_of_finite_biproducts _
  let pre₀ : Preadditive (Mat_ (SingleObj (DualNumber K))) := inferInstance
  have hsub : Subsingleton (Preadditive (Mat_ (SingleObj (DualNumber K)))) := inferInstance
  rcases hab with @⟨pre, _, _, _, hk, _⟩
  obtain rfl : pre = pre₀ := @Subsingleton.elim _ hsub _ _
  have _ := hk
  let P : Mat_ (SingleObj (DualNumber K)) :=
    (Mat_.embedding (SingleObj (DualNumber K))).obj (SingleObj.star (DualNumber K))
  let g : P ⟶ P := (Mat_.embedding (SingleObj (DualNumber K))).map (ε : DualNumber K)
  have hg_sq : g ≫ g = 0 := by
    let e : SingleObj.star (DualNumber K) ⟶ SingleObj.star (DualNumber K) := (ε : DualNumber K)
    have he : e ≫ e = 0 := DualNumber.eps_mul_eps
    exact ((Mat_.embedding (SingleObj (DualNumber K))).map_comp e e).symm.trans
      ((congrArg _ he).trans ((Mat_.embedding (SingleObj (DualNumber K))).map_zero _ _))
  let ι : kernel g ⟶ P := kernel.ι g
  have hne : Nonempty (kernel g).ι := by
    by_contra hemp
    have : IsEmpty (kernel g).ι := not_nonempty_iff.mp hemp
    have hfac : (∑ j : (kernel g).ι,
        homVal (ι j default) * homVal (kernel.lift g g hg_sq default j)) =
        homVal (g default default) :=
      congrArg (fun m : P ⟶ P ↦ homVal (m default default)) (kernel.lift_ι g g hg_sq)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hfac
    have hsnd := congrArg TrivSqZeroExt.snd hfac.symm
    simp [g, Mat_.embedding, homVal] at hsnd
  obtain ⟨j₀⟩ := hne
  let w : P ⟶ kernel g := fun _ j ↦ if j = j₀ then (ε : DualNumber K) else (0 : DualNumber K)
  have hwι : w ≫ ι = 0 := by
    ext i k
    obtain rfl : i = default := Subsingleton.elim _ _
    obtain rfl : k = default := Subsingleton.elim _ _
    change (∑ j : (kernel g).ι, homVal (ι j default) *
      (if j = j₀ then (ε : DualNumber K) else 0)) = (0 : DualNumber K)
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    by_cases hj : j = j₀
    · subst hj
      simp only [↓reduceIte]
      ext <;> simp [dualNumber_fst_eq_zero_of_comp_eps ι (kernel.condition g) j]
    · simp [hj]
  have hw0 : w = 0 := (cancel_mono ι).1 (by simp [hwι])
  have heps0 : (ε : DualNumber K) = 0 := by
    have hpt : homVal (w default j₀) = 0 :=
      congrArg (fun m : P ⟶ kernel g ↦ homVal (m default j₀)) hw0
    simpa [w, homVal] using hpt
  have hsnd := congrArg TrivSqZeroExt.snd heps0
  simp at hsnd

/-- Sharpness of division/scalar endomorphisms: over any field `K`,
`Mat_ (SingleObj (DualNumber K))` is `K`-linear, idempotent complete, has finite-dimensional Hom
spaces, and decomposes every object as a finite biproduct of a singleton Hom-orthogonal family, yet
admits no `Abelian` structure. -/
example (K : Type u) [Field K] :
    let X : SingleObj (DualNumber K) → Mat_ (SingleObj (DualNumber K)) :=
      (Mat_.embedding (SingleObj (DualNumber K))).obj
    HomOrthogonal X ∧
      (∀ M : Mat_ (SingleObj (DualNumber K)),
        ∃ (α : Type) (_ : Finite α) (a : α → SingleObj (DualNumber K)),
          Nonempty (M ≅ ⨁ fun p ↦ X (a p))) ∧
      (∀ M N : Mat_ (SingleObj (DualNumber K)), FiniteDimensional K (M ⟶ N)) ∧
      IsIdempotentComplete (Mat_ (SingleObj (DualNumber K))) ∧
      IsEmpty (Abelian (Mat_ (SingleObj (DualNumber K)))) := by
  intro X
  exact ⟨Mat_.homOrthogonal_embedding Subsingleton.pairwise,
    fun M ↦ ⟨M.ι, inferInstance, M.X, ⟨M.isoBiproductEmbedding⟩⟩,
    fun M N ↦ inferInstance, dualNumber_mat_isIdempotentComplete K,
    ⟨dualNumber_mat_not_abelian K⟩⟩

end Sharpness
