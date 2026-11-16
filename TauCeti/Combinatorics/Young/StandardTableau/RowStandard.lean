/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.StandardTableau.Reading
public import TauCeti.GroupTheory.SpecificGroups.Braid.Basic

/-!
# Row-standard Young tableaux

A **row-standard Young tableau** of shape `μ` is a bijective filling of the cells of `μ` by
`Fin μ.card` whose entries increase strictly from left to right along every row, with no
monotonicity condition along columns (`TauCeti.RowStandardYoungTableau`).

Every standard Young tableau is row-standard
(`TauCeti.StandardYoungTableau.toRowStandardYoungTableau`). Like standard Young tableaux, a
row-standard Young tableau is completely determined by the row containing each label
(`TauCeti.RowStandardYoungTableau.rowIndex_injective`): once the set of labels in each row is
chosen, strict monotonicity along the row fixes their positions uniquely. Consequently,
row-standard tableaux of shape `μ` are in canonical bijection both with `μ`-tabloids and with
minimal left coset representatives of the Young subgroup `S_μ` in `S_{|μ|}`, indexing the
Dipper–James–Mathas basis of the Hecke Young permutation module `M^μ`.

Swapping two adjacent labels `strand i` and `strandSucc i` by `BraidGroup.transposition i`
preserves row-strictness precisely when the two labels lie in distinct rows
(`TauCeti.RowStandardYoungTableau.swap`,
`TauCeti.RowStandardYoungTableau.not_exists_relabel_transposition_of_rowIndex_eq`), and preserves
standardness when they lie in both distinct rows and distinct columns
(`TauCeti.StandardYoungTableau.swap`).

## References

* R. Dipper and G. James, *Representations of Hecke algebras of general linear groups*,
  Proc. London Math. Soc. (3) 52 (1986), 20–52, Section 3.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999), Section 3.2.
-/

public section

namespace TauCeti

open YoungTableau TauCeti.BraidGroup

/-- A **row-standard Young tableau** of shape `μ`: a bijective labeling of the cells of `μ` by
`Fin μ.card` whose labels increase strictly from left to right along every row. -/
structure RowStandardYoungTableau (μ : YoungDiagram) where
  /-- The underlying `μ`-tableau. -/
  toTableau : YoungTableau μ
  /-- Labels increase strictly from left to right along each row. -/
  row_strict' : ∀ {i j₁ j₂ : ℕ} (h : j₁ < j₂) (hcell : (i, j₂) ∈ μ),
    toTableau ⟨(i, j₁), μ.up_left_mem le_rfl h.le hcell⟩ < toTableau ⟨(i, j₂), hcell⟩

namespace RowStandardYoungTableau

variable {μ : YoungDiagram}

instance instFunLike : FunLike (RowStandardYoungTableau μ) ↥μ.cells (Fin μ.card) where
  coe T := T.toTableau
  coe_injective T U h := by
    cases T with
    | mk e _ =>
      cases U with
      | mk e' _ =>
        congr
        exact Equiv.ext fun c ↦ congrFun h c

@[simp]
theorem coe_toTableau (T : RowStandardYoungTableau μ) : ⇑T.toTableau = T :=
  (rfl)

@[simp]
theorem toTableau_apply (T : RowStandardYoungTableau μ) (c : ↥μ.cells) : T.toTableau c = T c :=
  (rfl)

@[ext]
theorem ext {T U : RowStandardYoungTableau μ} (h : ∀ c, T c = U c) : T = U :=
  DFunLike.ext T U h

/-- `RowStandardYoungTableau.toTableau` is injective. -/
theorem toTableau_injective :
    Function.Injective (RowStandardYoungTableau.toTableau (μ := μ)) := fun _ _ h ↦
  ext fun c ↦ congr($h c)

/-- A row-standard Young tableau is a bijection from `μ.cells` to `Fin μ.card`. -/
theorem bijective (T : RowStandardYoungTableau μ) : Function.Bijective T :=
  T.toTableau.bijective

/-- A row-standard Young tableau is injective on `μ.cells`. -/
theorem injective (T : RowStandardYoungTableau μ) : Function.Injective T :=
  T.toTableau.injective

/-- A row-standard Young tableau is surjective onto `Fin μ.card`. -/
theorem surjective (T : RowStandardYoungTableau μ) : Function.Surjective T :=
  T.toTableau.surjective

/-- Entries of a row-standard Young tableau increase strictly from left to right. -/
theorem row_strict (T : RowStandardYoungTableau μ) {i j₁ j₂ : ℕ} (h : j₁ < j₂)
    (hcell : (i, j₂) ∈ μ) :
    T ⟨(i, j₁), μ.up_left_mem le_rfl h.le hcell⟩ < T ⟨(i, j₂), hcell⟩ :=
  T.row_strict' h hcell

noncomputable instance instFintype (μ : YoungDiagram) : Fintype (RowStandardYoungTableau μ) :=
  FunLike.fintype (RowStandardYoungTableau μ)

end RowStandardYoungTableau

namespace StandardYoungTableau

variable {μ : YoungDiagram}

/-- Forget column strictness, viewing a standard Young tableau as a row-standard Young tableau. -/
def toRowStandardYoungTableau (T : StandardYoungTableau μ) : RowStandardYoungTableau μ where
  toTableau := T.toTableau
  row_strict' := T.row_strict'

@[simp]
theorem toRowStandardYoungTableau_toTableau (T : StandardYoungTableau μ) :
    T.toRowStandardYoungTableau.toTableau = T.toTableau :=
  (rfl)

@[simp]
theorem toRowStandardYoungTableau_apply (T : StandardYoungTableau μ) (c : ↥μ.cells) :
    T.toRowStandardYoungTableau c = T c :=
  (rfl)

/-- `StandardYoungTableau.toRowStandardYoungTableau` is injective. -/
theorem toRowStandardYoungTableau_injective :
    Function.Injective (toRowStandardYoungTableau (μ := μ)) := fun _ _ h ↦
  ext fun c ↦ congrArg (· c) h

end StandardYoungTableau

namespace RowStandardYoungTableau

variable {μ : YoungDiagram}

instance instNonempty (μ : YoungDiagram) : Nonempty (RowStandardYoungTableau μ) :=
  ⟨(StandardYoungTableau.rowSuperstandard μ).toRowStandardYoungTableau⟩

private theorem apply_eq_of_coe_eq (T : RowStandardYoungTableau μ) (x : Fin μ.card) {c : ↥μ.cells}
    (h : (c : ℕ × ℕ) = (rowIndex T.toTableau x, colIndex T.toTableau x)) : T c = x := by
  have hc : c = T.toTableau.symm x := Subtype.ext (by rw [h, rowIndex_def, colIndex_def])
  rw [hc]
  exact T.toTableau.apply_symm_apply x

/-- Of two labels of a row-standard Young tableau lying in a common row, the one in the earlier
column is the smaller. -/
theorem lt_of_colIndex_lt (T : RowStandardYoungTableau μ) {x y : Fin μ.card}
    (hrow : rowIndex T.toTableau x = rowIndex T.toTableau y)
    (hcol : colIndex T.toTableau x < colIndex T.toTableau y) : x < y := by
  have hlt := T.row_strict hcol (rowIndex_colIndex_mem T.toTableau y)
  rwa [apply_eq_of_coe_eq T x (by simp [hrow]), apply_eq_of_coe_eq T y rfl] at hlt

/-- **Two labels of a row-standard Young tableau in a common row are ordered as their columns
are.** -/
theorem lt_iff_colIndex_lt (T : RowStandardYoungTableau μ) {x y : Fin μ.card}
    (hrow : rowIndex T.toTableau x = rowIndex T.toTableau y) :
    x < y ↔ colIndex T.toTableau x < colIndex T.toTableau y := by
  refine ⟨fun hxy ↦ ?_, lt_of_colIndex_lt T hrow⟩
  rcases lt_trichotomy (colIndex T.toTableau x) (colIndex T.toTableau y) with hc | hc | hc
  · exact hc
  · exact absurd (rowIndex_colIndex_injective T.toTableau (Prod.ext hrow hc)) hxy.ne
  · exact absurd (lt_of_colIndex_lt T hrow.symm hc) (asymm hxy)

/-- **A row-standard Young tableau is determined by the row of each of its labels.** -/
theorem rowIndex_injective (μ : YoungDiagram) :
    Function.Injective fun T : RowStandardYoungTableau μ ↦ rowIndex T.toTableau := by
  intro T U h
  have h' : rowIndex T.toTableau = rowIndex U.toTableau := h
  let rowEmb (S : RowStandardYoungTableau μ) (i : ℕ) : Fin (μ.rowLen i) ↪o Fin μ.card :=
    OrderEmbedding.ofStrictMono
      (fun j ↦ S ⟨(i, j.1), YoungDiagram.mem_iff_lt_rowLen.mpr j.2⟩)
      fun _ _ hlt ↦ S.row_strict (Fin.lt_def.mp hlt) _
  have hrange (S : RowStandardYoungTableau μ) (i : ℕ) :
      Set.range (rowEmb S i) = {k : Fin μ.card | rowIndex S.toTableau k = i} := by
    ext k
    simp only [Set.mem_range, Set.mem_ofPred_eq, rowEmb]
    refine ⟨?_, fun hk ↦ ⟨⟨colIndex S.toTableau k, hk ▸ colIndex_lt_rowLen S.toTableau k⟩,
      apply_eq_of_coe_eq S k (Prod.ext hk.symm rfl)⟩⟩
    rintro ⟨j, rfl⟩
    exact rowIndex_apply S.toTableau _
  refine ext fun ⟨⟨i, j⟩, hc⟩ ↦ ?_
  have heq : rowEmb T i = rowEmb U i :=
    OrderEmbedding.range_eq_iff.mp (by rw [hrange, hrange, h'])
  exact congr($heq ⟨j, YoungDiagram.mem_iff_lt_rowLen.mp hc⟩)

/-- On a diagram with at most one row, every row-standard Young tableau equals the
row-superstandard tableau. -/
theorem eq_rowSuperstandard_of_colLen_le_one (h : μ.colLen 0 ≤ 1)
    (T : RowStandardYoungTableau μ) :
    T = (StandardYoungTableau.rowSuperstandard μ).toRowStandardYoungTableau := by
  refine rowIndex_injective μ (funext fun x ↦ ?_)
  dsimp only
  rw [StandardYoungTableau.toRowStandardYoungTableau_toTableau]
  have h₁ := rowIndex_lt_colLen_zero T.toTableau x
  have h₂ := rowIndex_lt_colLen_zero (StandardYoungTableau.rowSuperstandard μ).toTableau x
  omega

/-- A diagram with at most one row has a unique row-standard Young tableau. -/
theorem subsingleton_of_colLen_le_one (h : μ.colLen 0 ≤ 1) :
    Subsingleton (RowStandardYoungTableau μ) :=
  ⟨fun T U ↦
    (eq_rowSuperstandard_of_colLen_le_one h T).trans
      (eq_rowSuperstandard_of_colLen_le_one h U).symm⟩

end RowStandardYoungTableau

/-- **A tableau is row-standard exactly when its labels increase along each row.** -/
theorem exists_rowStandardYoungTableau_toTableau_eq_iff {μ : YoungDiagram} (t : YoungTableau μ) :
    (∃ T : RowStandardYoungTableau μ, T.toTableau = t) ↔
      ∀ ⦃x y : Fin μ.card⦄, rowIndex t x = rowIndex t y → colIndex t x < colIndex t y → x < y := by
  constructor
  · rintro ⟨T, rfl⟩ x y hrow hcol
    exact T.lt_of_colIndex_lt hrow hcol
  · intro hrow
    exact ⟨⟨t, fun {_ _ _} h _ ↦
      hrow (by simp only [rowIndex_apply]) (by simp only [colIndex_apply]; exact h)⟩, rfl⟩

/-! ### Adjacent label swaps -/

namespace YoungTableau

variable {μ : YoungDiagram}

/-- Relabeling a tableau twice by the same adjacent transposition restores the tableau. -/
theorem relabel_transposition_involutive (i : Fin (μ.card - 1)) (t : YoungTableau μ) :
    relabel (transposition i) (relabel (transposition i) t) = t := by
  ext c
  simp [transposition_eq_swap]

/-- Relabeling `t` by `transposition i` moves `strandSucc i` into the cell of `strand i`. -/
theorem rowIndex_relabel_transposition_strand (i : Fin (μ.card - 1)) (t : YoungTableau μ) :
    rowIndex (relabel (transposition i) t) (strand i) = rowIndex t (strandSucc i) := by
  have hinv : (transposition i)⁻¹ = transposition i := by
    ext x
    simp [transposition_eq_swap]
  simp [hinv]

/-- Relabeling `t` by `transposition i` moves `strand i` into the cell of `strandSucc i`. -/
theorem rowIndex_relabel_transposition_strandSucc (i : Fin (μ.card - 1)) (t : YoungTableau μ) :
    rowIndex (relabel (transposition i) t) (strandSucc i) = rowIndex t (strand i) := by
  have hinv : (transposition i)⁻¹ = transposition i := by
    ext x
    simp [transposition_eq_swap]
  simp [hinv]

end YoungTableau

private theorem transposition_lt_transposition_of_lt {n : ℕ} {i : Fin (n - 1)} {x y : Fin n}
    (hxy : x < y) (hne : ¬(x = strand i ∧ y = strandSucc i)) :
    transposition i x < transposition i y := by
  rcases ((transposition i).injective.ne hxy.ne).lt_or_gt with hlt | hgt
  · exact hlt
  · exact absurd (eq_strand_of_transposition_lt hxy hgt) hne

namespace RowStandardYoungTableau

variable {μ : YoungDiagram}

/-- **Swapping two adjacent labels in distinct rows preserves row-standardness.** -/
def swap (T : RowStandardYoungTableau μ) (i : Fin (μ.card - 1))
    (h : rowIndex T.toTableau (strand i) ≠ rowIndex T.toTableau (strandSucc i)) :
    RowStandardYoungTableau μ where
  toTableau := relabel (transposition i) T.toTableau
  row_strict' {r j₁ j₂} hj hcell := by
    rw [relabel_apply, relabel_apply]
    refine transposition_lt_transposition_of_lt (T.row_strict hj hcell) ?_
    rintro ⟨hx, hy⟩
    apply h
    rw [← hx, ← hy, rowIndex_apply, rowIndex_apply]

@[simp]
theorem swap_toTableau (T : RowStandardYoungTableau μ) (i : Fin (μ.card - 1))
    (h : rowIndex T.toTableau (strand i) ≠ rowIndex T.toTableau (strandSucc i)) :
    (T.swap i h).toTableau = relabel (transposition i) T.toTableau :=
  (rfl)

@[simp]
theorem swap_apply (T : RowStandardYoungTableau μ) (i : Fin (μ.card - 1))
    (h : rowIndex T.toTableau (strand i) ≠ rowIndex T.toTableau (strandSucc i)) (c : ↥μ.cells) :
    T.swap i h c = transposition i (T c) := by
  rw [← toTableau_apply, swap_toTableau, relabel_apply, toTableau_apply]

/-- `RowStandardYoungTableau.swap` is an involution between pairs of tableaux with `strand i` and
`strandSucc i` in distinct rows. -/
theorem swap_eq_iff {S S' : RowStandardYoungTableau μ} {i : Fin (μ.card - 1)}
    (h : rowIndex S.toTableau (strand i) ≠ rowIndex S.toTableau (strandSucc i))
    (h' : rowIndex S'.toTableau (strand i) ≠ rowIndex S'.toTableau (strandSucc i)) :
    S'.swap i h' = S ↔ S' = S.swap i h := by
  constructor <;> rintro rfl <;> apply toTableau_injective <;>
    rw [swap_toTableau, swap_toTableau, relabel_transposition_involutive]

/-- Swapping `strand i` and `strandSucc i` from distinct rows cannot produce a tableau in which
they lie in the same row. -/
theorem swap_ne_of_rowIndex_eq {S S' : RowStandardYoungTableau μ} {i : Fin (μ.card - 1)}
    (h' : rowIndex S'.toTableau (strand i) ≠ rowIndex S'.toTableau (strandSucc i))
    (hS : rowIndex S.toTableau (strand i) = rowIndex S.toTableau (strandSucc i)) :
    S'.swap i h' ≠ S := by
  intro heq
  rw [← heq, S'.swap_toTableau, rowIndex_relabel_transposition_strand,
    rowIndex_relabel_transposition_strandSucc] at hS
  exact h' hS.symm

/-- Swapping two adjacent labels in the same row destroys row-standardness. -/
theorem not_exists_relabel_transposition_of_rowIndex_eq (T : RowStandardYoungTableau μ)
    {i : Fin (μ.card - 1)}
    (h : rowIndex T.toTableau (strand i) = rowIndex T.toTableau (strandSucc i)) :
    ¬ ∃ U : RowStandardYoungTableau μ, U.toTableau = relabel (transposition i) T.toTableau := by
  rw [exists_rowStandardYoungTableau_toTableau_eq_iff]
  intro hmono
  have hcol : colIndex T.toTableau (strand i) < colIndex T.toTableau (strandSucc i) :=
    (T.lt_iff_colIndex_lt h).mp (Fin.lt_def.mpr (by simp))
  have hinv : (transposition i)⁻¹ = transposition i := by
    ext x
    simp [transposition_eq_swap]
  have hrow' : rowIndex (relabel (transposition i) T.toTableau) (strandSucc i) =
      rowIndex (relabel (transposition i) T.toTableau) (strand i) := by
    rw [rowIndex_relabel_transposition_strandSucc, rowIndex_relabel_transposition_strand, h]
  have hcol' : colIndex (relabel (transposition i) T.toTableau) (strandSucc i) <
      colIndex (relabel (transposition i) T.toTableau) (strand i) := by
    simpa [hinv] using hcol
  exact lt_asymm (hmono hrow' hcol') (Fin.lt_def.mpr (by simp))

end RowStandardYoungTableau

namespace StandardYoungTableau

variable {μ : YoungDiagram}

/-- **Swapping two adjacent labels in distinct rows and distinct columns preserves
standardness.** -/
def swap (T : StandardYoungTableau μ) (i : Fin (μ.card - 1))
    (hrow : rowIndex T.toTableau (strand i) ≠ rowIndex T.toTableau (strandSucc i))
    (hcol : colIndex T.toTableau (strand i) ≠ colIndex T.toTableau (strandSucc i)) :
    StandardYoungTableau μ where
  toTableau := relabel (transposition i) T.toTableau
  row_strict' {r j₁ j₂} hj hcell := by
    rw [relabel_apply, relabel_apply]
    refine transposition_lt_transposition_of_lt (T.row_strict hj hcell) ?_
    rintro ⟨hx, hy⟩
    apply hrow
    rw [← hx, ← hy, rowIndex_apply, rowIndex_apply]
  col_strict' {r₁ r₂ c} hr hcell := by
    rw [relabel_apply, relabel_apply]
    refine transposition_lt_transposition_of_lt (T.col_strict hr hcell) ?_
    rintro ⟨hx, hy⟩
    apply hcol
    rw [← hx, ← hy, colIndex_apply, colIndex_apply]

@[simp]
theorem swap_toTableau (T : StandardYoungTableau μ) (i : Fin (μ.card - 1))
    (hrow : rowIndex T.toTableau (strand i) ≠ rowIndex T.toTableau (strandSucc i))
    (hcol : colIndex T.toTableau (strand i) ≠ colIndex T.toTableau (strandSucc i)) :
    (T.swap i hrow hcol).toTableau = relabel (transposition i) T.toTableau :=
  (rfl)

@[simp]
theorem swap_toRowStandardYoungTableau (T : StandardYoungTableau μ) (i : Fin (μ.card - 1))
    (hrow : rowIndex T.toTableau (strand i) ≠ rowIndex T.toTableau (strandSucc i))
    (hcol : colIndex T.toTableau (strand i) ≠ colIndex T.toTableau (strandSucc i)) :
    (T.swap i hrow hcol).toRowStandardYoungTableau =
      T.toRowStandardYoungTableau.swap i (by simpa using hrow) :=
  RowStandardYoungTableau.toTableau_injective (by simp)

end StandardYoungTableau

end TauCeti
