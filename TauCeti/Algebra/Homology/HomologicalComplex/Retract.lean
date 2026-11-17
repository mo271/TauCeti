/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Retracts of homotopy equivalences

A retract of a homotopy equivalence of homological complexes in a preadditive category is again
a homotopy equivalence: if `h : RetractArrow f f'` and `e` is a homotopy equivalence with
`e.hom = f'`, then `h.i.right ≫ e.inv ≫ h.r.left` is a homotopy inverse to `f`, with the
homotopies whiskered along the retract data (`HomotopyEquiv.ofRetractArrow`).

Consequently, the morphism property `HomologicalComplex.homotopyEquivalences V c` is stable
under retracts.
-/

public section

open CategoryTheory

universe v u

namespace HomotopyEquiv

variable {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}

/-- A retract of a homotopy equivalence of homological complexes is a homotopy equivalence,
with `hom` equal to the retracted morphism. -/
@[expose, simps hom inv]
def ofRetractArrow {C D C' D' : HomologicalComplex V c}
    {f : C ⟶ D} {f' : C' ⟶ D'} (h : RetractArrow f f')
    (e : HomotopyEquiv C' D') (he : e.hom = f') : HomotopyEquiv C D where
  hom := f
  inv := h.i.right ≫ e.inv ≫ h.r.left
  homotopyHomInvId := by
    subst he
    exact (Homotopy.ofEq (by
        rw [← Category.assoc, ← h.i_w, Category.assoc, Category.assoc])).trans
      (((e.homotopyHomInvId.compRight h.r.left).compLeft h.i.left).trans
        (Homotopy.ofEq (by simp)))
  homotopyInvHomId := by
    subst he
    exact (Homotopy.ofEq (by
        rw [Category.assoc, Category.assoc, h.r_w, ← Category.assoc e.inv])).trans
      (((e.homotopyInvHomId.compRight h.r.right).compLeft h.i.right).trans
        (Homotopy.ofEq (by simp)))

end HomotopyEquiv

namespace HomologicalComplex

variable {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}

/-- Homotopy equivalences of homological complexes are stable under retracts. -/
instance : (homotopyEquivalences V c).IsStableUnderRetracts where
  of_retract h := by
    rintro ⟨e, rfl⟩
    exact ⟨e.ofRetractArrow h rfl, rfl⟩

end HomologicalComplex
