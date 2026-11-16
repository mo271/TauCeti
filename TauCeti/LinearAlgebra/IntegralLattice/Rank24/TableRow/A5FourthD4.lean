/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Niemeier
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Triality
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The triality-lifted block rotation of the table row `A₅⁴ D₄`

The row `A₅⁴ D₄` (`TauCeti.RootfulNiemeierType.a5FourthD4`) of Conway--Sloane's rootful rank-24
table has five ordered components `A₅, A₅, A₅, A₅, D₄` and four glue patterns:
`[2(024)0]`, `[33001]`, `[30302]` and `[30033]`.  It is the unique row of the table in which an
indicated pattern symmetry — the 3-cycle `1 ↦ 2 ↦ 3 ↦ 1` of the three `A₅` positions marked in
`[2(024)0]` (`TauCeti.RootfulNiemeierType.a5FourthD4BlockPerm`) — is not a pure coordinate glue
symmetry: permuting the three `A₅` positions while acting trivially on the `D₄` component fails to
preserve the literal generators `[33001]`, `[30302]` and `[30033]`.

Those three literal generators pair the cyclic shifts `(300) ↦ (030) ↦ (003)` on the marked `A₅`
positions with the cyclic permutation `1 ↦ 2 ↦ 3 ↦ 1` (`s ↦ v ↦ c ↦ s`) of the nonzero `D₄` glue
labels.  By `TauCeti.DynkinType.typeD4TrialityGlueAlphabetIsometry_glueLabelEquiv`, the root-lattice
triality `TauCeti.DynkinType.typeD4Triality` induces exactly that 3-cycle on `(D 4).glueAlphabet`,
while fixing the zero label in `[2(024)0]`.  Combining the coordinate 3-cycle on the marked `A₅`
components with `typeD4Triality` on the `D₄` component through
`TauCeti.DynkinType.gluedLatticePiCongrIsometry` therefore preserves the glue subgroup and yields an
order-`3` self-isometry `TauCeti.RootfulNiemeierType.a5FourthD4BlockRotationIsometry` of the
Niemeier lattice `TauCeti.niemeierA5FourthD4`, together with a faithful action of `p.symmetries` on
`niemeierA5FourthD4` for every glue pattern `p` of the row
(`TauCeti.RootfulNiemeierType.a5FourthD4PatternIsometryHom`).

## Main declarations

* `TauCeti.RootfulNiemeierType.a5FourthD4BlockPerm`: the order-`3` permutation fixing positions `0`
  and `4` and cycling `1 ↦ 2 ↦ 3 ↦ 1`, which generates
  `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries`.
* `TauCeti.RootfulNiemeierType.a5FourthD4ComponentIsometry`,
  `TauCeti.RootfulNiemeierType.a5FourthD4GlueAlphabetIsometry`: the componentwise root-lattice and
  glue-alphabet isometries acting trivially on the four `A₅` components and by `typeD4Triality` on
  the `D₄` component.
* `TauCeti.RootfulNiemeierType.a5FourthD4TrialityGlueWordIsometry`: the resulting self-isometry of
  `a5FourthD4.glueModule`, which preserves `a5FourthD4.glueSubgroup`
  (`a5FourthD4TrialityGlueWordIsometry_mem_glueSubgroup_iff`).
* `TauCeti.RootfulNiemeierType.a5FourthD4BlockRotationIsometry`: the order-`3` self-isometry of
  `niemeierA5FourthD4` cycling the three marked `A₅` components and acting by `typeD4Triality` on
  the `D₄` component.
* `TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom`,
  `TauCeti.RootfulNiemeierType.a5FourthD4PatternIsometryHom`: the faithful action of the pattern
  symmetries of `A₅⁴ D₄` on `niemeierA5FourthD4`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §§3 and 7, and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti

namespace RootfulNiemeierType

open DynkinType IntegralLattice

/-! ### Component metadata and the marked block permutation -/

/-- The row `A₅⁴ D₄` has five components. -/
@[simp]
theorem length_components_a5FourthD4 : a5FourthD4.components.length = 5 :=
  (rfl)

/-- Component `0` of `A₅⁴ D₄` has type `A₅`. -/
@[simp]
theorem componentType_a5FourthD4_zero : a5FourthD4.componentType ⟨0, by decide⟩ = A 5 :=
  (rfl)

/-- Component `1` of `A₅⁴ D₄` has type `A₅`. -/
@[simp]
theorem componentType_a5FourthD4_one : a5FourthD4.componentType ⟨1, by decide⟩ = A 5 :=
  (rfl)

/-- Component `2` of `A₅⁴ D₄` has type `A₅`. -/
@[simp]
theorem componentType_a5FourthD4_two : a5FourthD4.componentType ⟨2, by decide⟩ = A 5 :=
  (rfl)

/-- Component `3` of `A₅⁴ D₄` has type `A₅`. -/
@[simp]
theorem componentType_a5FourthD4_three : a5FourthD4.componentType ⟨3, by decide⟩ = A 5 :=
  (rfl)

/-- Component `4` of `A₅⁴ D₄` has type `D₄`. -/
@[simp]
theorem componentType_a5FourthD4_four : a5FourthD4.componentType ⟨4, by decide⟩ = D 4 :=
  (rfl)

/-- Every component of `A₅⁴ D₄` other than position `4` has type `A₅`. -/
theorem componentType_a5FourthD4_of_ne_four {i : Fin a5FourthD4.components.length}
    (hi : i ≠ ⟨4, by decide⟩) : a5FourthD4.componentType i = A 5 := by
  fin_cases i <;> first | rfl | exact absurd rfl hi

/-- The marked block rotation on the first four coordinates `Fin (1 + 3)`. -/
private def blockPerm4 : Equiv.Perm (Fin (1 + 3)) :=
  Equiv.Perm.finSumPerm 1 (finRotate 3)

/-- The marked block rotation on `Fin ((1 + 3) + 1)`: fixing `0` and `4` and cycling
`1 ↦ 2 ↦ 3 ↦ 1`. -/
private def blockPerm5 : Equiv.Perm (Fin ((1 + 3) + 1)) :=
  Equiv.Perm.finSumPerm blockPerm4 1

private theorem blockPerm5_zero : blockPerm5 0 = 0 := by
  change blockPerm5 (Fin.castAdd 1 (Fin.castAdd 3 0)) = 0
  rw [blockPerm5, Equiv.Perm.finSumPerm_apply_castAdd, blockPerm4,
    Equiv.Perm.finSumPerm_apply_castAdd]
  rfl

private theorem blockPerm5_one : blockPerm5 1 = 2 := by
  change blockPerm5 (Fin.castAdd 1 (Fin.natAdd 1 0)) = 2
  rw [blockPerm5, Equiv.Perm.finSumPerm_apply_castAdd, blockPerm4,
    Equiv.Perm.finSumPerm_apply_natAdd]
  decide

private theorem blockPerm5_two : blockPerm5 2 = 3 := by
  change blockPerm5 (Fin.castAdd 1 (Fin.natAdd 1 1)) = 3
  rw [blockPerm5, Equiv.Perm.finSumPerm_apply_castAdd, blockPerm4,
    Equiv.Perm.finSumPerm_apply_natAdd]
  decide

private theorem blockPerm5_three : blockPerm5 3 = 1 := by
  change blockPerm5 (Fin.castAdd 1 (Fin.natAdd 1 2)) = 1
  rw [blockPerm5, Equiv.Perm.finSumPerm_apply_castAdd, blockPerm4,
    Equiv.Perm.finSumPerm_apply_natAdd]
  decide

private theorem blockPerm5_four : blockPerm5 4 = 4 := by
  change blockPerm5 (Fin.natAdd (1 + 3) 0) = 4
  rw [blockPerm5, Equiv.Perm.finSumPerm_apply_natAdd]
  rfl

private theorem blockPerm5_pow_three : blockPerm5 ^ 3 = 1 := by
  rw [blockPerm5, Equiv.Perm.finSumPerm_pow, blockPerm4, Equiv.Perm.finSumPerm_pow, one_pow,
    show finRotate 3 ^ 3 = 1 by decide, Equiv.Perm.finSumPerm_one, Equiv.Perm.finSumPerm_one]

/-- **The marked block rotation of `A₅⁴ D₄`**: the coordinate permutation fixing positions `0` and
`4` and cycling the three marked `A₅` positions `1 ↦ 2 ↦ 3 ↦ 1` of the cyclic pattern `[2(024)0]`.
Read on the pattern positions, it is the canonical generator of
`(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries`. -/
def a5FourthD4BlockPerm : Equiv.Perm (Fin a5FourthD4.components.length) :=
  (finCongr rfl).permCongr blockPerm5

/-- `a5FourthD4BlockPerm` fixes position `0`. -/
@[simp]
theorem a5FourthD4BlockPerm_zero : a5FourthD4BlockPerm ⟨0, by decide⟩ = ⟨0, by decide⟩ :=
  Fin.ext (congrArg Fin.val blockPerm5_zero)

/-- `a5FourthD4BlockPerm` sends position `1` to position `2`. -/
@[simp]
theorem a5FourthD4BlockPerm_one : a5FourthD4BlockPerm ⟨1, by decide⟩ = ⟨2, by decide⟩ :=
  Fin.ext (congrArg Fin.val blockPerm5_one)

/-- `a5FourthD4BlockPerm` sends position `2` to position `3`. -/
@[simp]
theorem a5FourthD4BlockPerm_two : a5FourthD4BlockPerm ⟨2, by decide⟩ = ⟨3, by decide⟩ :=
  Fin.ext (congrArg Fin.val blockPerm5_two)

/-- `a5FourthD4BlockPerm` sends position `3` to position `1`. -/
@[simp]
theorem a5FourthD4BlockPerm_three : a5FourthD4BlockPerm ⟨3, by decide⟩ = ⟨1, by decide⟩ :=
  Fin.ext (congrArg Fin.val blockPerm5_three)

/-- `a5FourthD4BlockPerm` fixes position `4`. -/
@[simp]
theorem a5FourthD4BlockPerm_four : a5FourthD4BlockPerm ⟨4, by decide⟩ = ⟨4, by decide⟩ :=
  Fin.ext (congrArg Fin.val blockPerm5_four)

/-- `a5FourthD4BlockPerm.symm` fixes position `0`. -/
@[simp]
theorem a5FourthD4BlockPerm_symm_zero :
    a5FourthD4BlockPerm.symm ⟨0, by decide⟩ = ⟨0, by decide⟩ :=
  a5FourthD4BlockPerm.symm_apply_eq.mpr a5FourthD4BlockPerm_zero.symm

/-- `a5FourthD4BlockPerm.symm` sends position `1` to position `3`. -/
@[simp]
theorem a5FourthD4BlockPerm_symm_one :
    a5FourthD4BlockPerm.symm ⟨1, by decide⟩ = ⟨3, by decide⟩ :=
  a5FourthD4BlockPerm.symm_apply_eq.mpr a5FourthD4BlockPerm_three.symm

/-- `a5FourthD4BlockPerm.symm` sends position `2` to position `1`. -/
@[simp]
theorem a5FourthD4BlockPerm_symm_two :
    a5FourthD4BlockPerm.symm ⟨2, by decide⟩ = ⟨1, by decide⟩ :=
  a5FourthD4BlockPerm.symm_apply_eq.mpr a5FourthD4BlockPerm_one.symm

/-- `a5FourthD4BlockPerm.symm` sends position `3` to position `2`. -/
@[simp]
theorem a5FourthD4BlockPerm_symm_three :
    a5FourthD4BlockPerm.symm ⟨3, by decide⟩ = ⟨2, by decide⟩ :=
  a5FourthD4BlockPerm.symm_apply_eq.mpr a5FourthD4BlockPerm_two.symm

/-- `a5FourthD4BlockPerm.symm` fixes position `4`. -/
@[simp]
theorem a5FourthD4BlockPerm_symm_four :
    a5FourthD4BlockPerm.symm ⟨4, by decide⟩ = ⟨4, by decide⟩ :=
  a5FourthD4BlockPerm.symm_apply_eq.mpr a5FourthD4BlockPerm_four.symm

/-- `a5FourthD4BlockPerm` preserves the Dynkin type of every component of `A₅⁴ D₄`. -/
theorem componentType_a5FourthD4BlockPerm (i : Fin a5FourthD4.components.length) :
    a5FourthD4.componentType (a5FourthD4BlockPerm i) = a5FourthD4.componentType i := by
  fin_cases i <;> simp

/-- Three applications of `a5FourthD4BlockPerm` give the identity. -/
@[simp]
theorem a5FourthD4BlockPerm_pow_three : a5FourthD4BlockPerm ^ 3 = 1 :=
  ((map_pow ((finCongr (rfl : (1 + 3) + 1 = a5FourthD4.components.length)).permCongrHom)
    blockPerm5 3).symm.trans (congrArg _ blockPerm5_pow_three)).trans (map_one _)

/-- `a5FourthD4BlockPerm` is not the identity permutation. -/
theorem a5FourthD4BlockPerm_ne_one : a5FourthD4BlockPerm ≠ 1 := by
  intro h
  have h1 := Equiv.Perm.ext_iff.mp h ⟨1, by decide⟩
  simp at h1

/-- **`a5FourthD4BlockPerm` has exact order `3`.** -/
@[simp]
theorem orderOf_a5FourthD4BlockPerm : orderOf a5FourthD4BlockPerm = 3 :=
  orderOf_eq_prime a5FourthD4BlockPerm_pow_three a5FourthD4BlockPerm_ne_one

/-! ### Componentwise root-lattice and glue-alphabet isometries -/

/-- **The componentwise root-lattice isometries paired with `a5FourthD4BlockPerm`**: the canonical
identification of equal `A₅` root lattices on positions `0, 1, 2, 3`, and `typeD4Triality` on the
`D₄` component in position `4`. -/
noncomputable def a5FourthD4ComponentIsometry (i : Fin a5FourthD4.components.length) :
    IntegralLattice.Isometry
      ((a5FourthD4.componentType i).rootLattice (a5FourthD4.isSimplyLaced_componentType i))
      ((a5FourthD4.componentType (a5FourthD4BlockPerm i)).rootLattice
        (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm i))) :=
  if hi : i = ⟨4, by decide⟩ then
    ((a5FourthD4.componentType i).rootLatticeIsometryOfEq
        (a5FourthD4.isSimplyLaced_componentType i)
        (hi ▸ componentType_a5FourthD4_four) (isSimplyLaced_D 4)).trans <|
      (typeD4Triality (isSimplyLaced_D 4)).trans <|
        (D 4).rootLatticeIsometryOfEq (isSimplyLaced_D 4)
          ((hi ▸ componentType_a5FourthD4_four).symm.trans
            (componentType_a5FourthD4BlockPerm i).symm)
          (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm i))
  else
    (a5FourthD4.componentType i).rootLatticeIsometryOfEq
      (a5FourthD4.isSimplyLaced_componentType i)
      (componentType_a5FourthD4BlockPerm i).symm
      (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm i))

/-- On each `A₅` component `i ≠ 4`, `a5FourthD4ComponentIsometry i` is `rootLatticeIsometryOfEq`. -/
theorem a5FourthD4ComponentIsometry_of_ne_four {i : Fin a5FourthD4.components.length}
    (hi : i ≠ ⟨4, by decide⟩) :
    a5FourthD4ComponentIsometry i =
      (a5FourthD4.componentType i).rootLatticeIsometryOfEq
        (a5FourthD4.isSimplyLaced_componentType i)
        (componentType_a5FourthD4BlockPerm i).symm
        (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm i)) :=
  dite_eq_right hi

/-- **The componentwise glue-alphabet isometries paired with `a5FourthD4BlockPerm`**, induced by
`a5FourthD4ComponentIsometry` through `glueAlphabetIsometryOfRootLatticeIsometry`. -/
noncomputable def a5FourthD4GlueAlphabetIsometry (i : Fin a5FourthD4.components.length) :
    FiniteQuadraticModule.Isometry
      ((a5FourthD4.componentType i).glueAlphabet (a5FourthD4.isSimplyLaced_componentType i))
      ((a5FourthD4.componentType (a5FourthD4BlockPerm i)).glueAlphabet
        (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm i))) :=
  glueAlphabetIsometryOfRootLatticeIsometry (a5FourthD4.valid_componentType i)
    (a5FourthD4.valid_componentType (a5FourthD4BlockPerm i))
    (a5FourthD4.isSimplyLaced_componentType i)
    (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm i))
    (a5FourthD4ComponentIsometry i)

/-- On each `A₅` component `i ≠ 4`, `a5FourthD4GlueAlphabetIsometry i` preserves the Conway--Sloane
digit. -/
private theorem val_glueLabelEquiv_symm_a5FourthD4GlueAlphabetIsometry_of_ne_four
    {i : Fin a5FourthD4.components.length} (hi : i ≠ ⟨4, by decide⟩)
    (x : (a5FourthD4.componentType i).glueAlphabet (a5FourthD4.isSimplyLaced_componentType i)) :
    (((a5FourthD4.componentType (a5FourthD4BlockPerm i)).glueLabelEquiv
        (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm i))).symm
          (a5FourthD4GlueAlphabetIsometry i x)).val =
      (((a5FourthD4.componentType i).glueLabelEquiv
        (a5FourthD4.isSimplyLaced_componentType i)).symm x).val := by
  rw [a5FourthD4GlueAlphabetIsometry, a5FourthD4ComponentIsometry_of_ne_four hi,
    glueAlphabetIsometryOfRootLatticeIsometry_ofEq]
  exact val_glueLabelEquiv_symm_ofEq (componentType_a5FourthD4BlockPerm i).symm _ _ x

/-- On the `D₄` component `4`, `a5FourthD4GlueAlphabetIsometry 4` applies multiplication by `ω²`
(`0 ↦ 0, 1 ↦ 2, 2 ↦ 3, 3 ↦ 1`) to the Conway--Sloane digit. -/
private theorem val_glueLabelEquiv_symm_a5FourthD4GlueAlphabetIsometry_four
    (x : (a5FourthD4.componentType ⟨4, by decide⟩).glueAlphabet
      (a5FourthD4.isSimplyLaced_componentType ⟨4, by decide⟩)) :
    (((a5FourthD4.componentType (a5FourthD4BlockPerm ⟨4, by decide⟩)).glueLabelEquiv
        (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm ⟨4, by decide⟩))).symm
          (a5FourthD4GlueAlphabetIsometry ⟨4, by decide⟩ x)).val =
      GlueSpanMode.f4OmegaLabel (GlueSpanMode.f4OmegaLabel
        (((a5FourthD4.componentType ⟨4, by decide⟩).glueLabelEquiv
          (a5FourthD4.isSimplyLaced_componentType ⟨4, by decide⟩)).symm x).val) := by
  rw [a5FourthD4GlueAlphabetIsometry, a5FourthD4ComponentIsometry, dite_eq_left rfl,
    glueAlphabetIsometryOfRootLatticeIsometry_trans _ (valid_D.mpr le_rfl),
    glueAlphabetIsometryOfRootLatticeIsometry_trans (valid_D.mpr le_rfl) (valid_D.mpr le_rfl),
    glueAlphabetIsometryOfRootLatticeIsometry_ofEq,
    glueAlphabetIsometryOfRootLatticeIsometry_ofEq,
    glueAlphabetIsometryOfRootLatticeIsometry_typeD4Triality,
    QuadraticMap.IsometryEquiv.trans_apply, QuadraticMap.IsometryEquiv.trans_apply,
    val_glueLabelEquiv_symm_ofEq (by simp)]
  set y : (D 4).glueAlphabet (isSimplyLaced_D 4) :=
    FiniteQuadraticModule.Isometry.ofEq
      (glueAlphabet_congr componentType_a5FourthD4_four
        (a5FourthD4.isSimplyLaced_componentType ⟨4, by decide⟩) (isSimplyLaced_D 4)) x
  have hy := congrArg Fin.val
    (glueLabelEquiv_symm_typeD4TrialityGlueAlphabetIsometry (isSimplyLaced_D 4) y)
  refine hy.trans ?_
  have hyval : (((D 4).glueLabelEquiv (isSimplyLaced_D 4)).symm y).val =
      (((a5FourthD4.componentType ⟨4, by decide⟩).glueLabelEquiv
        (a5FourthD4.isSimplyLaced_componentType ⟨4, by decide⟩)).symm x).val :=
    val_glueLabelEquiv_symm_ofEq componentType_a5FourthD4_four _ _ x
  have hd (d : Fin 4) :
      (![0, 2, 3, 1] d : Fin 4).val =
        GlueSpanMode.f4OmegaLabel (GlueSpanMode.f4OmegaLabel d.val) := by
    fin_cases d <;> rfl
  rw [← hyval]
  exact hd _

/-! ### Action on glue words and invariance of the glue subgroup -/

/-- **The triality-lifted glue-word isometry of `A₅⁴ D₄`**: the self-isometry of
`a5FourthD4.glueModule` moving coordinate `i` by `a5FourthD4GlueAlphabetIsometry i` to position
`a5FourthD4BlockPerm i`. -/
noncomputable def a5FourthD4TrialityGlueWordIsometry :
    FiniteQuadraticModule.Isometry a5FourthD4.glueModule a5FourthD4.glueModule :=
  QuadraticMap.IsometryEquiv.piCongr a5FourthD4BlockPerm a5FourthD4GlueAlphabetIsometry

/-- The action of `a5FourthD4TrialityGlueWordIsometry` on Conway--Sloane digit lists: it fixes
position `0`, cycles positions `1, 2, 3` (`[d₀, d₁, d₂, d₃, d₄] ↦ [d₀, d₃, d₁, d₂, …]`), and
applies `ω²` (`0 ↦ 0, 1 ↦ 2, 2 ↦ 3, 3 ↦ 1`) to the `D₄` digit in position `4`. -/
@[expose] def a5FourthD4TrialityDigits (l : List ℕ) : List ℕ :=
  [l.getD 0 0, l.getD 3 0, l.getD 1 0, l.getD 2 0,
    GlueSpanMode.f4OmegaLabel (GlueSpanMode.f4OmegaLabel (l.getD 4 0))]

/-- **Digits of a glue word after `a5FourthD4TrialityGlueWordIsometry`.** -/
@[simp]
theorem encodeGlueWord_a5FourthD4TrialityGlueWordIsometry (w : a5FourthD4.glueModule) :
    encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
        (a5FourthD4TrialityGlueWordIsometry w) =
      a5FourthD4TrialityDigits
        (encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType w) := by
  have hval (i : Fin a5FourthD4.components.length) :
      (((a5FourthD4.componentType (a5FourthD4BlockPerm i)).glueLabelEquiv
          (a5FourthD4.isSimplyLaced_componentType (a5FourthD4BlockPerm i))).symm
            (a5FourthD4TrialityGlueWordIsometry w (a5FourthD4BlockPerm i))).val =
        if i = ⟨4, by decide⟩ then
          GlueSpanMode.f4OmegaLabel (GlueSpanMode.f4OmegaLabel
            (((a5FourthD4.componentType ⟨4, by decide⟩).glueLabelEquiv
              (a5FourthD4.isSimplyLaced_componentType ⟨4, by decide⟩)).symm
                (w ⟨4, by decide⟩)).val)
        else
          (((a5FourthD4.componentType i).glueLabelEquiv
            (a5FourthD4.isSimplyLaced_componentType i)).symm (w i)).val := by
    rw [a5FourthD4TrialityGlueWordIsometry, QuadraticMap.IsometryEquiv.piCongr_apply_apply]
    split_ifs with hi
    · subst hi
      exact val_glueLabelEquiv_symm_a5FourthD4GlueAlphabetIsometry_four (w ⟨4, by decide⟩)
    · exact val_glueLabelEquiv_symm_a5FourthD4GlueAlphabetIsometry_of_ne_four hi (w i)
  have hget (k : ℕ) (hk : k < a5FourthD4.components.length) :
      (encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType w).getD
          k 0 =
        (((a5FourthD4.componentType ⟨k, hk⟩).glueLabelEquiv
          (a5FourthD4.isSimplyLaced_componentType ⟨k, hk⟩)).symm (w ⟨k, hk⟩)).val := by
    rw [List.getD_eq_getElem _ _ ((length_encodeGlueWord _ _ w).symm ▸ hk)]
    exact getElem_encodeGlueWord _ _ w ⟨k, hk⟩
  have h0 := a5FourthD4BlockPerm_zero ▸ hval ⟨0, by decide⟩
  have h1 := a5FourthD4BlockPerm_one ▸ hval ⟨1, by decide⟩
  have h2 := a5FourthD4BlockPerm_two ▸ hval ⟨2, by decide⟩
  have h3 := a5FourthD4BlockPerm_three ▸ hval ⟨3, by decide⟩
  have h4 := a5FourthD4BlockPerm_four ▸ hval ⟨4, by decide⟩
  apply List.ext_getElem
  · simp [a5FourthD4TrialityDigits]
  · intro k hk₁ hk₂
    have hk5 : k < a5FourthD4.components.length := by simpa only [length_encodeGlueWord] using hk₁
    have hk5' : k < 5 := hk5
    refine (getElem_encodeGlueWord _ _ _ ⟨k, hk5⟩).trans ?_
    interval_cases k
    · dsimp only [a5FourthD4TrialityDigits, List.getElem_cons_zero, List.getElem_cons_succ]
      rw [hget 0 (by decide)]
      simpa using h0
    · dsimp only [a5FourthD4TrialityDigits, List.getElem_cons_zero, List.getElem_cons_succ]
      rw [hget 3 (by decide)]
      simpa using h3
    · dsimp only [a5FourthD4TrialityDigits, List.getElem_cons_zero, List.getElem_cons_succ]
      rw [hget 1 (by decide)]
      simpa using h1
    · dsimp only [a5FourthD4TrialityDigits, List.getElem_cons_zero, List.getElem_cons_succ]
      rw [hget 2 (by decide)]
      simpa using h2
    · dsimp only [a5FourthD4TrialityDigits, List.getElem_cons_zero, List.getElem_cons_succ]
      rw [hget 4 (by decide)]
      simpa using h4

/-- `a5FourthD4TrialityDigits` maps every digit word of `A₅⁴ D₄` into `a5FourthD4.glueWords`. -/
theorem a5FourthD4TrialityDigits_mem_glueWords {l : List ℕ} (hl : l ∈ a5FourthD4.glueWords) :
    a5FourthD4TrialityDigits l ∈ a5FourthD4.glueWords := by
  revert l
  decide

/-- Three applications of `a5FourthD4TrialityDigits` recover any 5-digit word. -/
theorem a5FourthD4TrialityDigits_iter_three {l : List ℕ} (hl : l.length = 5) :
    a5FourthD4TrialityDigits (a5FourthD4TrialityDigits (a5FourthD4TrialityDigits l)) = l := by
  rcases l with _ | ⟨d₀, _ | ⟨d₁, _ | ⟨d₂, _ | ⟨d₃, _ | ⟨d₄, _ | _⟩⟩⟩⟩⟩ <;>
    simp_all [a5FourthD4TrialityDigits]

/-- A 5-digit list has its `a5FourthD4TrialityDigits` image in `a5FourthD4.glueWords` if and only
if the list itself lies in `a5FourthD4.glueWords`. -/
theorem a5FourthD4TrialityDigits_mem_glueWords_iff {l : List ℕ} (hl : l.length = 5) :
    a5FourthD4TrialityDigits l ∈ a5FourthD4.glueWords ↔ l ∈ a5FourthD4.glueWords := by
  refine ⟨fun h ↦ ?_, a5FourthD4TrialityDigits_mem_glueWords⟩
  rw [← a5FourthD4TrialityDigits_iter_three hl]
  exact a5FourthD4TrialityDigits_mem_glueWords (a5FourthD4TrialityDigits_mem_glueWords h)

/-- **`a5FourthD4TrialityGlueWordIsometry` preserves the glue subgroup of `A₅⁴ D₄`.** -/
@[simp]
theorem a5FourthD4TrialityGlueWordIsometry_mem_glueSubgroup_iff (w : a5FourthD4.glueModule) :
    a5FourthD4TrialityGlueWordIsometry w ∈ a5FourthD4.glueSubgroup ↔
      w ∈ a5FourthD4.glueSubgroup :=
  a5FourthD4.mem_glueSubgroup_iff_of_glueWords a5FourthD4TrialityGlueWordIsometry
    (fun v ↦ by
      rw [encodeGlueWord_a5FourthD4TrialityGlueWordIsometry]
      exact a5FourthD4TrialityDigits_mem_glueWords_iff (length_encodeGlueWord _ _ v)) w

/-! ### The lifted self-isometry of `niemeierA5FourthD4` -/

/-- **The triality-lifted block rotation of `niemeierA5FourthD4`**: the self-isometry of the
Niemeier lattice `A₅⁴ D₄` that fixes the leading `A₅` component, cycles the three marked `A₅`
components `1 ↦ 2 ↦ 3 ↦ 1`, and acts by `typeD4Triality` on the `D₄` component. -/
noncomputable def a5FourthD4BlockRotationIsometry :
    IntegralLattice.Isometry niemeierA5FourthD4 niemeierA5FourthD4 :=
  (Isometry.ofEq (lattice_def a5FourthD4)).trans <|
    (gluedLatticePiCongrIsometry a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
      a5FourthD4.valid_componentType a5FourthD4.glueSubgroup a5FourthD4.isIsotropic_glueSubgroup
      a5FourthD4.valid_componentType a5FourthD4.isIsotropic_glueSubgroup a5FourthD4BlockPerm
      a5FourthD4ComponentIsometry (fun i ↦ a5FourthD4GlueAlphabetIsometry i)
      (fun i x ↦ glueAlphabetIsometry_glueAlphabetIsometryOfRootLatticeIsometry _ _ _ _ _ x)
      (fun w ↦ by
        have hw :
            Equiv.piCongrLeft
                (fun k ↦ (a5FourthD4.componentType k).glueAlphabet
                  (a5FourthD4.isSimplyLaced_componentType k))
                a5FourthD4BlockPerm (fun i ↦ a5FourthD4GlueAlphabetIsometry i (w i)) =
              a5FourthD4TrialityGlueWordIsometry w := by
          funext k
          obtain ⟨i, rfl⟩ := a5FourthD4BlockPerm.surjective k
          rw [Equiv.piCongrLeft_apply_apply, a5FourthD4TrialityGlueWordIsometry,
            QuadraticMap.IsometryEquiv.piCongr_apply_apply]
        rw [hw]
        exact a5FourthD4TrialityGlueWordIsometry_mem_glueSubgroup_iff w)).trans
    (Isometry.ofEq (lattice_def a5FourthD4).symm)

/-- Evaluating `a5FourthD4BlockRotationIsometry` at `a5FourthD4BlockPerm i` applies
`a5FourthD4ComponentIsometry i` to component `i`. -/
theorem a5FourthD4BlockRotationIsometry_apply_blockPerm
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ)
    (i : Fin a5FourthD4.components.length) :
    a5FourthD4BlockRotationIsometry x (a5FourthD4BlockPerm i) =
      a5FourthD4ComponentIsometry i (x i) := by
  rw [a5FourthD4BlockRotationIsometry, Isometry.trans_apply, Isometry.trans_apply,
    Isometry.ofEq_apply, Isometry.ofEq_apply]
  exact gluedLatticePiCongrIsometry_apply _ _ _ _ _ _ _ _ _ _ _ _ x i

/-- Reading coordinates of `a5FourthD4BlockRotationIsometry x` across an equality of positions
whose Dynkin types are `t`. -/
private theorem apply_eq_of_blockPerm_eq {t : DynkinType}
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ)
    {i k : Fin a5FourthD4.components.length} (hik : a5FourthD4BlockPerm i = k)
    (ht : a5FourthD4.componentType k = t)
    (y : Fin t.rank → ℚ)
    (hy : ∀ j : Fin (a5FourthD4.componentType (a5FourthD4BlockPerm i)).rank,
      a5FourthD4ComponentIsometry i (x i) j =
        y (Fin.cast (congrArg rank ((congrArg a5FourthD4.componentType hik).trans ht)) j))
    (j : Fin (a5FourthD4.componentType k).rank) :
    a5FourthD4BlockRotationIsometry x k j = y (Fin.cast (congrArg rank ht) j) := by
  subst hik
  exact (congrFun (a5FourthD4BlockRotationIsometry_apply_blockPerm x i) j).trans (hy j)

/-- `a5FourthD4BlockRotationIsometry` fixes component `0`. -/
@[simp]
theorem a5FourthD4BlockRotationIsometry_apply_zero
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4BlockRotationIsometry x ⟨0, by decide⟩ = x ⟨0, by decide⟩ := by
  ext j
  refine apply_eq_of_blockPerm_eq x a5FourthD4BlockPerm_zero rfl (x ⟨0, by decide⟩)
    (fun j' ↦ ?_) j
  rw [a5FourthD4ComponentIsometry_of_ne_four (by decide), rootLatticeIsometryOfEq_apply]

/-- `a5FourthD4BlockRotationIsometry` reads component `1` from component `3`. -/
@[simp]
theorem a5FourthD4BlockRotationIsometry_apply_one
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4BlockRotationIsometry x ⟨1, by decide⟩ = x ⟨3, by decide⟩ := by
  ext j
  refine apply_eq_of_blockPerm_eq x a5FourthD4BlockPerm_three rfl (x ⟨3, by decide⟩)
    (fun j' ↦ ?_) j
  rw [a5FourthD4ComponentIsometry_of_ne_four (by decide), rootLatticeIsometryOfEq_apply]
  exact congrArg _ (Fin.ext rfl)

/-- `a5FourthD4BlockRotationIsometry` reads component `2` from component `1`. -/
@[simp]
theorem a5FourthD4BlockRotationIsometry_apply_two
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4BlockRotationIsometry x ⟨2, by decide⟩ = x ⟨1, by decide⟩ := by
  ext j
  refine apply_eq_of_blockPerm_eq x a5FourthD4BlockPerm_one rfl (x ⟨1, by decide⟩)
    (fun j' ↦ ?_) j
  rw [a5FourthD4ComponentIsometry_of_ne_four (by decide), rootLatticeIsometryOfEq_apply]
  exact congrArg _ (Fin.ext rfl)

/-- `a5FourthD4BlockRotationIsometry` reads component `3` from component `2`. -/
@[simp]
theorem a5FourthD4BlockRotationIsometry_apply_three
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4BlockRotationIsometry x ⟨3, by decide⟩ = x ⟨2, by decide⟩ := by
  ext j
  refine apply_eq_of_blockPerm_eq x a5FourthD4BlockPerm_two rfl (x ⟨2, by decide⟩)
    (fun j' ↦ ?_) j
  rw [a5FourthD4ComponentIsometry_of_ne_four (by decide), rootLatticeIsometryOfEq_apply]
  exact congrArg _ (Fin.ext rfl)

/-- `a5FourthD4BlockRotationIsometry` acts on component `4` by `typeD4Triality`. -/
@[simp]
theorem a5FourthD4BlockRotationIsometry_apply_four
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4BlockRotationIsometry x ⟨4, by decide⟩ =
      typeD4Triality (isSimplyLaced_D 4) (x ⟨4, by decide⟩) := by
  ext j
  refine apply_eq_of_blockPerm_eq x a5FourthD4BlockPerm_four rfl
    (typeD4Triality (isSimplyLaced_D 4) (x ⟨4, by decide⟩)) (fun j' ↦ ?_) j
  rw [a5FourthD4ComponentIsometry, dite_eq_left rfl, Isometry.trans_apply, Isometry.trans_apply,
    rootLatticeIsometryOfEq_apply]
  refine congrFun (congrArg (typeD4Triality (isSimplyLaced_D 4)) ?_) _
  ext k
  exact rootLatticeIsometryOfEq_apply _ _ _ _ _ k

/-- **Three applications of `a5FourthD4BlockRotationIsometry` give the identity.** -/
@[simp]
theorem a5FourthD4BlockRotationIsometry_pow_three : a5FourthD4BlockRotationIsometry ^ 3 = 1 := by
  refine Isometry.ext fun x ↦ funext fun k ↦ ?_
  rw [pow_three, Isometry.mul_apply, Isometry.mul_apply, Isometry.one_apply]
  fin_cases k
  · simp
  · simp
  · simp
  · simp
  · change a5FourthD4BlockRotationIsometry
        (a5FourthD4BlockRotationIsometry (a5FourthD4BlockRotationIsometry x)) ⟨4, by decide⟩ =
      x ⟨4, by decide⟩
    rw [a5FourthD4BlockRotationIsometry_apply_four, a5FourthD4BlockRotationIsometry_apply_four,
      a5FourthD4BlockRotationIsometry_apply_four]
    have htri (v : Fin (D 4).rank → ℚ) :
        typeD4Triality (isSimplyLaced_D 4)
          (typeD4Triality (isSimplyLaced_D 4) (typeD4Triality (isSimplyLaced_D 4) v)) = v := by
      have h := DFunLike.congr_fun (typeD4Triality_pow_three (isSimplyLaced_D 4)) v
      rwa [pow_three, Isometry.mul_apply, Isometry.mul_apply, Isometry.one_apply] at h
    exact htri (x ⟨4, by decide⟩)

/-- `a5FourthD4BlockRotationIsometry` is not the identity isometry. -/
theorem a5FourthD4BlockRotationIsometry_ne_one : a5FourthD4BlockRotationIsometry ≠ 1 := by
  intro h
  have hx := congrFun (congrFun (DFunLike.congr_fun h
    (Pi.single (⟨3, by decide⟩ : Fin a5FourthD4.components.length) fun _ ↦ (1 : ℚ)))
    ⟨1, by decide⟩) ⟨0, by decide⟩
  rw [a5FourthD4BlockRotationIsometry_apply_one, Isometry.one_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide)] at hx
  exact one_ne_zero hx

/-- **`a5FourthD4BlockRotationIsometry` has exact order `3`.** -/
@[simp]
theorem orderOf_a5FourthD4BlockRotationIsometry :
    orderOf a5FourthD4BlockRotationIsometry = 3 :=
  orderOf_eq_prime a5FourthD4BlockRotationIsometry_pow_three a5FourthD4BlockRotationIsometry_ne_one

/-! ### Action of the pattern symmetries of `A₅⁴ D₄` on `niemeierA5FourthD4` -/

/-- The canonical generator of `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries`, typed on the
pattern's positions `Fin (GluePattern.cyclic [2] [0, 2, 4] [0]).length`. -/
def a5FourthD4PatternGen : (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries :=
  ⟨Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm 1 (finRotate [0, 2, 4].length)) 1, by
    rw [GluePattern.symmetries_cyclic]
    exact Subgroup.mem_zpowers _⟩

/-- Reading `a5FourthD4PatternGen` on `Fin a5FourthD4.components.length` gives
`a5FourthD4BlockPerm`. -/
@[simp]
theorem permCongr_a5FourthD4PatternGen
    (hlen : (GluePattern.cyclic [2] [0, 2, 4] [0]).length = a5FourthD4.components.length) :
    (finCongr hlen).permCongr a5FourthD4PatternGen = a5FourthD4BlockPerm :=
  (rfl)

/-- `a5FourthD4PatternGen` has exact order `3`. -/
@[simp]
theorem orderOf_a5FourthD4PatternGen : orderOf a5FourthD4PatternGen = 3 := by
  have h := orderOf_injective
    ((finCongr (rfl : (GluePattern.cyclic [2] [0, 2, 4] [0]).length =
      a5FourthD4.components.length)).permCongrHom.toMonoidHom.comp
        (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries.subtype)
    (by
      rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
      exact (MulEquiv.injective _).comp (Subgroup.subtype_injective _))
    a5FourthD4PatternGen
  exact h.symm.trans orderOf_a5FourthD4BlockPerm

/-- Every element of `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries` is an integer power of
`a5FourthD4PatternGen`. -/
private theorem forall_mem_zpowers_a5FourthD4PatternGen :
    ∀ x : (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries,
      x ∈ Subgroup.zpowers a5FourthD4PatternGen
  | ⟨x, hx⟩ => by
    rw [GluePattern.symmetries_cyclic] at hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, Subtype.ext hk⟩

/-- **The faithful action of the cyclic pattern symmetries of `[2(024)0]` on `niemeierA5FourthD4`**,
sending the generator `a5FourthD4PatternGen` to `a5FourthD4BlockRotationIsometry`. -/
noncomputable def a5FourthD4CyclicSymmetryHom :
    (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries →*
      IntegralLattice.Isometry niemeierA5FourthD4 niemeierA5FourthD4 :=
  (Subgroup.zpowers a5FourthD4BlockRotationIsometry).subtype.comp
    (mulEquivOfOrderOfEq
      (g := a5FourthD4PatternGen)
      (g' := (⟨a5FourthD4BlockRotationIsometry, Subgroup.mem_zpowers _⟩ :
        Subgroup.zpowers a5FourthD4BlockRotationIsometry))
      forall_mem_zpowers_a5FourthD4PatternGen
      (fun ⟨_, k, hk⟩ ↦ ⟨k, Subtype.ext hk⟩)
      (by
        rw [orderOf_a5FourthD4PatternGen, ← Subgroup.orderOf_coe,
          orderOf_a5FourthD4BlockRotationIsometry])).toMonoidHom

/-- `a5FourthD4CyclicSymmetryHom` sends `a5FourthD4PatternGen` to
`a5FourthD4BlockRotationIsometry`. -/
@[simp]
theorem a5FourthD4CyclicSymmetryHom_gen :
    a5FourthD4CyclicSymmetryHom a5FourthD4PatternGen =
      a5FourthD4BlockRotationIsometry := by
  simp [a5FourthD4CyclicSymmetryHom]

/-- `a5FourthD4CyclicSymmetryHom` sends `a5FourthD4PatternGen ^ k` (`k : ℤ`) to
`a5FourthD4BlockRotationIsometry ^ k`. -/
@[simp]
theorem a5FourthD4CyclicSymmetryHom_zpow (k : ℤ) :
    a5FourthD4CyclicSymmetryHom (a5FourthD4PatternGen ^ k) =
      a5FourthD4BlockRotationIsometry ^ k := by
  rw [map_zpow, a5FourthD4CyclicSymmetryHom_gen]

/-- `a5FourthD4CyclicSymmetryHom` sends `a5FourthD4PatternGen ^ k` (`k : ℕ`) to
`a5FourthD4BlockRotationIsometry ^ k`. -/
@[simp]
theorem a5FourthD4CyclicSymmetryHom_pow (k : ℕ) :
    a5FourthD4CyclicSymmetryHom (a5FourthD4PatternGen ^ k) =
      a5FourthD4BlockRotationIsometry ^ k := by
  rw [map_pow, a5FourthD4CyclicSymmetryHom_gen]

/-- `a5FourthD4CyclicSymmetryHom` is injective. -/
theorem a5FourthD4CyclicSymmetryHom_injective :
    Function.Injective a5FourthD4CyclicSymmetryHom :=
  (Subgroup.subtype_injective _).comp (MulEquiv.injective _)

/-- **The indicated symmetries of every glue pattern of `A₅⁴ D₄` act on `niemeierA5FourthD4`**,
acting trivially for the three literal patterns and by `a5FourthD4CyclicSymmetryHom` for
`[2(024)0]`. -/
noncomputable def a5FourthD4PatternIsometryHom :
    ∀ {p : GluePattern}, p ∈ a5FourthD4.gluePatterns →
      p.symmetries →* IntegralLattice.Isometry a5FourthD4.lattice a5FourthD4.lattice
  | .literal _, _ => 1
  | .cyclic pre block post, hp =>
    have h : GluePattern.cyclic pre block post = .cyclic [2] [0, 2, 4] [0] := by
      obtain ⟨rfl, rfl, rfl⟩ : pre = [2] ∧ block = [0, 2, 4] ∧ post = [0] := by
        simpa [gluePatterns] using hp
      rfl
    h ▸ a5FourthD4CyclicSymmetryHom
  | .evenPermutations _, hp => absurd hp (by simp [gluePatterns])

/-- On a literal pattern of `A₅⁴ D₄`, `a5FourthD4PatternIsometryHom` is the trivial homomorphism. -/
@[simp]
theorem a5FourthD4PatternIsometryHom_literal {w : List ℕ}
    (hw : GluePattern.literal w ∈ a5FourthD4.gluePatterns) :
    a5FourthD4PatternIsometryHom hw = 1 :=
  (rfl)

/-- On `[2(024)0]`, `a5FourthD4PatternIsometryHom` is `a5FourthD4CyclicSymmetryHom`. -/
@[simp]
theorem a5FourthD4PatternIsometryHom_cyclic
    (hp : GluePattern.cyclic [2] [0, 2, 4] [0] ∈ a5FourthD4.gluePatterns) :
    a5FourthD4PatternIsometryHom hp = a5FourthD4CyclicSymmetryHom :=
  (rfl)

/-- **`a5FourthD4PatternIsometryHom` is injective for every glue pattern of `A₅⁴ D₄`.** -/
theorem a5FourthD4PatternIsometryHom_injective :
    ∀ {p : GluePattern} (hp : p ∈ a5FourthD4.gluePatterns),
      Function.Injective (a5FourthD4PatternIsometryHom hp)
  | .literal w, _ => by
    have : Subsingleton (GluePattern.literal w).symmetries := by
      rw [GluePattern.symmetries_literal]
      infer_instance
    exact fun a b _ ↦ Subsingleton.elim a b
  | .cyclic pre block post, hp => by
    obtain ⟨rfl, rfl, rfl⟩ : pre = [2] ∧ block = [0, 2, 4] ∧ post = [0] := by
      simpa [gluePatterns] using hp
    exact a5FourthD4CyclicSymmetryHom_injective
  | .evenPermutations _, hp => absurd hp (by simp [gluePatterns])

end RootfulNiemeierType

end TauCeti
