/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.StandardTableau.RowStandard
public import TauCeti.GroupTheory.Perm.Parabolic
public import TauCeti.RepresentationTheory.Symmetric.Specht.StandardBasis

/-!
# Young parabolic subgroups, row-standard coset representatives, and dominance

This file connects the Coxeter parabolic theory of `Equiv.Perm (Fin n)` with Young subgroups,
row-standard Young tableaux, tabloids, and the dominance order:

* **Young subgroups as standard parabolic subgroups.** For `μ : n.Partition`, the block map
  `TauCeti.youngBlock μ` is monotone (`TauCeti.monotone_youngBlock`), so `TauCeti.youngSubgroup μ`
  is the standard parabolic subgroup `(permCoxeterSystem n).parabolic (youngGenSet μ)`
  (`TauCeti.parabolic_youngGenSet`), and its length generating function is the product of the
  quantum factorials of the parts of `μ`
  (`TauCeti.sum_pow_permCoxeterSystem_length_youngSubgroup`).
  Likewise, the column-index map of the column-superstandard tableau is monotone
  (`TauCeti.monotone_colIndex_colSuperstandard`), realizing its column group as a standard parabolic
  subgroup (`TauCeti.parabolic_colSuperstandardGenSet`).
* **Row-standard Young tableaux as minimal coset representatives.** The permutation
  `YoungTableau.rowYoungConjugator t` establishes a bijection between `μ`-tableaux and permutations
  of `Fin μ.card`, equal to `1` at `rowSuperstandard μ`, and it is a minimal left coset
  representative of `youngGenSet (shapePartition μ)` if and only if `t` is row-standard
  (`TauCeti.YoungTableau.isMinimalCosetRep_youngGenSet_rowYoungConjugator_iff`). This identifies
  `RowStandardYoungTableau μ` with both minimal coset representatives
  (`TauCeti.RowStandardYoungTableau.equivMinimalCosetRep`) and `μ`-tabloids
  (`TauCeti.RowStandardYoungTableau.equivTabloid`), and characterizes left descents of
  `rowYoungConjugator T.toTableau` by row-index inversions
  (`TauCeti.RowStandardYoungTableau.isLeftDescent_rowYoungConjugator_iff`).
* **Column-superstandard coset factorizations and dominance.** The conjugator of
  `colSuperstandard μ` has no left descent in `colSuperstandardGenSet μ`, every column-group
  relabeling of `colSuperstandard μ` is row-standard
  (`TauCeti.RowStandardYoungTableau.colSuperstandardRelabel`), every left descent of
  `relabelPerm (colSuperstandard μ).toTableau T.toTableau` swaps a standard pair of cells in `T`,
  and `TabloidDominates` satisfies Dipper–James's transposition diamond property
  (`TauCeti.YoungTableau.TabloidDominates.relabel_transposition`).

## References

* R. Dipper and G. James, *Representations of Hecke algebras of general linear groups*,
  Proc. London Math. Soc. (3) 52 (1986), 20–52, Sections 3–4.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999), Sections 3.1–3.2.
-/

public section

namespace TauCeti

open Finset YoungTableau TauCeti.BraidGroup

/-! ### Young subgroups as standard Coxeter parabolic subgroups -/

/-- The consecutive-block map `youngBlock μ` of a partition `μ` of `n` is monotone. -/
theorem monotone_youngBlock {n : ℕ} (μ : n.Partition) : Monotone (youngBlock μ) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := (youngBlocksEquiv μ).surjective a
  obtain ⟨y, rfl⟩ := (youngBlocksEquiv μ).surjective b
  rw [youngBlock_youngBlocksEquiv, youngBlock_youngBlocksEquiv]
  by_contra hlt
  have hyx : (y.1 : ℕ) < (x.1 : ℕ) := not_le.mp hlt
  let f (r : ℕ) : ℕ :=
    if hr : r < (μ.parts.sort (· ≥ ·)).length then (μ.parts.sort (· ≥ ·))[r] else 0
  have hsum (z : Σ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Fin ((μ.parts.sort (· ≥ ·)).get i)) :
      (youngBlocksEquiv μ z : ℕ) = ∑ r ∈ range z.1, f r + z.2 := by
    rw [youngBlocksEquiv_apply, ← Fin.sum_univ_eq_sum_range]
    congr 1
    refine sum_congr rfl fun r _ ↦ ?_
    simp only [f, List.get_eq_getElem, Fin.val_castLE, r.2.trans z.1.2, ↓reduceDIte]
  have hle : ∑ r ∈ range (y.1 + 1), f r ≤ ∑ r ∈ range x.1, f r :=
    sum_le_sum_of_subset fun r hr ↦ mem_range.mpr ((mem_range.mp hr).trans_le hyx)
  rw [sum_range_succ] at hle
  have hy2 : (y.2 : ℕ) < f y.1 := by
    simpa only [f, y.1.2, ↓reduceDIte, List.get_eq_getElem] using y.2.2
  have hba : (youngBlocksEquiv μ y : ℕ) < (youngBlocksEquiv μ x : ℕ) := by
    rw [hsum y, hsum x]
    omega
  exact not_lt_of_ge (Fin.le_def.mp hab) hba

/-- The set of Coxeter generator indices whose crossed strands lie in the same consecutive block of
`μ : n.Partition`. -/
noncomputable def youngGenSet {n : ℕ} (μ : n.Partition) : Set (Fin (n - 1)) :=
  fiberGenSet (youngBlock μ)

theorem youngGenSet_def {n : ℕ} (μ : n.Partition) :
    youngGenSet μ = fiberGenSet (youngBlock μ) :=
  (rfl)

@[simp]
theorem mem_youngGenSet {n : ℕ} {μ : n.Partition} {i : Fin (n - 1)} :
    i ∈ youngGenSet μ ↔ youngBlock μ (strand i) = youngBlock μ (strandSucc i) := by
  rw [youngGenSet, mem_fiberGenSet]

/-- **Young subgroups are standard Coxeter parabolic subgroups.** -/
theorem parabolic_youngGenSet {n : ℕ} (μ : n.Partition) :
    (permCoxeterSystem n).parabolic (youngGenSet μ) = youngSubgroup μ := by
  rw [youngGenSet, parabolic_fiberGenSet (monotone_youngBlock μ), youngSubgroup_eq_fiberSubgroup]

private theorem card_filter_youngBlock_eq {n : ℕ} (μ : n.Partition)
    (i : Fin (μ.parts.sort (· ≥ ·)).length) :
    #{a : Fin n | youngBlock μ a = i} = (μ.parts.sort (· ≥ ·)).get i := by
  classical
  rw [← Fintype.card_subtype, List.get_eq_getElem]
  exact (Fintype.card_congr (youngBlockEquiv μ i)).symm.trans (Fintype.card_fin _)

/-- **Length generating function of a Young parabolic subgroup.** It is the product of the quantum
factorials of the parts of `μ`. -/
theorem sum_pow_permCoxeterSystem_length_parabolic_youngGenSet {n : ℕ} (μ : n.Partition)
    {R : Type*} [CommSemiring R]
    [Fintype ((permCoxeterSystem n).parabolic (youngGenSet μ))] (x : R) :
    (∑ σ : (permCoxeterSystem n).parabolic (youngGenSet μ),
        x ^ (permCoxeterSystem n).length (σ : Equiv.Perm (Fin n))) =
      (μ.parts.map fun p ↦ ∏ d ∈ Icc 1 p, ∑ j ∈ range d, x ^ j).prod := by
  classical
  let eqv : (permCoxeterSystem n).parabolic (youngGenSet μ) ≃
      (permCoxeterSystem n).parabolic (fiberGenSet (youngBlock μ)) :=
    Equiv.subtypeEquivRight fun _ ↦ Iff.rfl
  let _ : Fintype ((permCoxeterSystem n).parabolic (fiberGenSet (youngBlock μ))) :=
    Fintype.ofFinite _
  have heqv :
      (∑ σ : (permCoxeterSystem n).parabolic (youngGenSet μ),
          x ^ (permCoxeterSystem n).length (σ : Equiv.Perm (Fin n))) =
        ∑ σ : (permCoxeterSystem n).parabolic (fiberGenSet (youngBlock μ)),
          x ^ (permCoxeterSystem n).length (σ : Equiv.Perm (Fin n)) :=
    Fintype.sum_equiv eqv _ _ fun _ ↦ rfl
  rw [heqv, sum_pow_permCoxeterSystem_length_parabolic_fiberGenSet (monotone_youngBlock μ) x]
  have hprod :
      (∏ i : Fin (μ.parts.sort (· ≥ ·)).length,
          ∏ d ∈ Icc 1 #{a : Fin n | youngBlock μ a = i}, ∑ j ∈ range d, x ^ j) =
        ∏ i : Fin (μ.parts.sort (· ≥ ·)).length,
          ∏ d ∈ Icc 1 ((μ.parts.sort (· ≥ ·))[i.1]), ∑ j ∈ range d, x ^ j :=
    prod_congr rfl fun i _ ↦ by rw [card_filter_youngBlock_eq, List.get_eq_getElem]
  rw [hprod, Fin.prod_univ_fun_getElem _ (fun p ↦ ∏ d ∈ Icc 1 p, ∑ j ∈ range d, x ^ j),
    ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.sort_eq]

/-- **Length generating function of a Young subgroup.** -/
theorem sum_pow_permCoxeterSystem_length_youngSubgroup {n : ℕ} (μ : n.Partition)
    {R : Type*} [CommSemiring R] [Fintype (youngSubgroup μ)] (x : R) :
    (∑ σ : youngSubgroup μ, x ^ (permCoxeterSystem n).length (σ : Equiv.Perm (Fin n))) =
      (μ.parts.map fun p ↦ ∏ d ∈ Icc 1 p, ∑ j ∈ range d, x ^ j).prod := by
  let _ : Fintype ((permCoxeterSystem n).parabolic (youngGenSet μ)) := Fintype.ofFinite _
  let eqv : youngSubgroup μ ≃ (permCoxeterSystem n).parabolic (youngGenSet μ) :=
    Equiv.subtypeEquivRight fun σ ↦ by rw [parabolic_youngGenSet]
  rw [← sum_pow_permCoxeterSystem_length_parabolic_youngGenSet μ x, ← eqv.sum_comp]
  rfl

/-! ### The column subgroup of the column-superstandard tableau as a standard parabolic subgroup -/

/-- Along the column-superstandard tableau, column indices increase weakly with the label. -/
theorem monotone_colIndex_colSuperstandard (μ : YoungDiagram) :
    Monotone (colIndex (StandardYoungTableau.colSuperstandard μ).toTableau) := by
  intro x y hxy
  by_contra hlt
  set t := (StandardYoungTableau.colSuperstandard μ).toTableau
  set c := t.symm x
  set d := t.symm y
  have hdc : d.1.swap.1 < c.1.swap.1 := by
    simpa only [Prod.fst_swap, colIndex_def] using not_le.mp hlt
  have hd_mem : d.1.swap ∈ μ.transpose :=
    YoungDiagram.mem_transpose.mpr ((YoungDiagram.mem_cells _).mp d.2)
  have hread := YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt hd_mem hdc
  have hx : (x : ℕ) = YoungDiagram.readingIndex μ.transpose c.1.swap := by
    have := StandardYoungTableau.colSuperstandard_apply_val μ c
    rwa [← StandardYoungTableau.toTableau_apply, Equiv.apply_symm_apply] at this
  have hy : (y : ℕ) = YoungDiagram.readingIndex μ.transpose d.1.swap := by
    have := StandardYoungTableau.colSuperstandard_apply_val μ d
    rwa [← StandardYoungTableau.toTableau_apply, Equiv.apply_symm_apply] at this
  exact not_lt_of_ge (Fin.le_def.mp hxy) (by omega)

/-- The set of Coxeter generator indices whose crossed strands lie in the same column of
`StandardYoungTableau.colSuperstandard μ`. -/
noncomputable def colSuperstandardGenSet (μ : YoungDiagram) : Set (Fin (μ.card - 1)) :=
  fiberGenSet (colIndex (StandardYoungTableau.colSuperstandard μ).toTableau)

theorem colSuperstandardGenSet_def (μ : YoungDiagram) :
    colSuperstandardGenSet μ =
      fiberGenSet (colIndex (StandardYoungTableau.colSuperstandard μ).toTableau) :=
  (rfl)

@[simp]
theorem mem_colSuperstandardGenSet {μ : YoungDiagram} {i : Fin (μ.card - 1)} :
    i ∈ colSuperstandardGenSet μ ↔
      colIndex (StandardYoungTableau.colSuperstandard μ).toTableau (strand i) =
        colIndex (StandardYoungTableau.colSuperstandard μ).toTableau (strandSucc i) := by
  rw [colSuperstandardGenSet, mem_fiberGenSet]

/-- **The column group of `colSuperstandard μ` is a standard Coxeter parabolic subgroup.** -/
theorem parabolic_colSuperstandardGenSet (μ : YoungDiagram) :
    (permCoxeterSystem μ.card).parabolic (colSuperstandardGenSet μ) =
      colSubgroup (StandardYoungTableau.colSuperstandard μ).toTableau := by
  rw [colSuperstandardGenSet, parabolic_fiberGenSet (monotone_colIndex_colSuperstandard μ),
    colSubgroup_def]

/-- **Length generating function of the column parabolic subgroup of `colSuperstandard μ`.** It is
the product of the quantum factorials of the column lengths of `μ`. -/
theorem sum_pow_permCoxeterSystem_length_parabolic_colSuperstandardGenSet (μ : YoungDiagram)
    {R : Type*} [CommSemiring R]
    [Fintype ((permCoxeterSystem μ.card).parabolic (colSuperstandardGenSet μ))] (x : R) :
    (∑ σ : (permCoxeterSystem μ.card).parabolic (colSuperstandardGenSet μ),
        x ^ (permCoxeterSystem μ.card).length (σ : Equiv.Perm (Fin μ.card))) =
      (μ.transpose.rowLens.map fun c ↦ ∏ d ∈ Icc 1 c, ∑ j ∈ range d, x ^ j).prod := by
  classical
  set t := (StandardYoungTableau.colSuperstandard μ).toTableau
  let colFin (a : Fin μ.card) : Fin (μ.rowLen 0) :=
    ⟨colIndex t a, (colIndex_lt_rowLen t a).trans_le (μ.rowLen_anti 0 _ (Nat.zero_le _))⟩
  have hmono : Monotone colFin := fun a b hab ↦
    Fin.le_def.mpr (monotone_colIndex_colSuperstandard μ hab)
  have hgen : colSuperstandardGenSet μ = fiberGenSet colFin := by
    ext i
    simp [colSuperstandardGenSet, colFin, t, Fin.ext_iff]
  let eqv : (permCoxeterSystem μ.card).parabolic (colSuperstandardGenSet μ) ≃
      (permCoxeterSystem μ.card).parabolic (fiberGenSet colFin) :=
    Equiv.subtypeEquivRight fun σ ↦ by rw [hgen]
  let _ : Fintype ((permCoxeterSystem μ.card).parabolic (fiberGenSet colFin)) := Fintype.ofFinite _
  have heqv :
      (∑ σ : (permCoxeterSystem μ.card).parabolic (colSuperstandardGenSet μ),
          x ^ (permCoxeterSystem μ.card).length (σ : Equiv.Perm (Fin μ.card))) =
        ∑ σ : (permCoxeterSystem μ.card).parabolic (fiberGenSet colFin),
          x ^ (permCoxeterSystem μ.card).length (σ : Equiv.Perm (Fin μ.card)) :=
    Fintype.sum_equiv eqv _ _ fun _ ↦ rfl
  rw [heqv, sum_pow_permCoxeterSystem_length_parabolic_fiberGenSet hmono x]
  have hcard (j : Fin (μ.rowLen 0)) :
      #{a : Fin μ.card | colFin a = j} = μ.transpose.rowLen j := by
    have hflt : (univ.filter fun a : Fin μ.card ↦ colFin a = j) =
        univ.filter fun a : Fin μ.card ↦ colIndex t a = (j : ℕ) := by
      ext a
      simp [colFin, Fin.ext_iff]
    rw [hflt, card_filter_colIndex_eq, YoungDiagram.rowLen_transpose]
  have hlen : μ.transpose.rowLens.length = μ.rowLen 0 := by
    rw [YoungDiagram.length_rowLens, YoungDiagram.colLen_transpose]
  have hprod :
      (∏ j : Fin (μ.rowLen 0),
          ∏ d ∈ Icc 1 #{a : Fin μ.card | colFin a = j}, ∑ k ∈ range d, x ^ k) =
        ∏ j : Fin μ.transpose.rowLens.length,
          ∏ d ∈ Icc 1 (μ.transpose.rowLens[j.1]), ∑ k ∈ range d, x ^ k := by
    refine Fintype.prod_equiv (finCongr hlen.symm) _ _ fun j ↦ ?_
    rw [hcard j, YoungDiagram.get_rowLens]
    rfl
  rw [hprod, Fin.prod_univ_fun_getElem _ (fun c ↦ ∏ d ∈ Icc 1 c, ∑ k ∈ range d, x ^ k)]

/-! ### Row-standard tableaux, `rowYoungConjugator`, and minimal coset representatives -/

namespace YoungTableau

variable {μ : YoungDiagram}

/-- At the row-superstandard tableau, `rowYoungConjugator` is the identity permutation. -/
@[simp]
theorem rowYoungConjugator_rowSuperstandard (μ : YoungDiagram) :
    rowYoungConjugator (StandardYoungTableau.rowSuperstandard μ).toTableau = 1 := by
  ext k
  obtain ⟨x, rfl⟩ := (youngBlocksEquiv (shapePartition μ)).surjective k
  rw [Equiv.Perm.one_apply, rowYoungConjugator_youngBlocksEquiv,
    StandardYoungTableau.toTableau_apply, StandardYoungTableau.rowSuperstandard_apply_val,
    YoungDiagram.readingIndex_def, youngBlocksEquiv_apply]
  dsimp only
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [List.get_eq_getElem]
  simp only [Fin.val_castLE, shapePartition_parts_sort, YoungDiagram.get_rowLens]

/-- `rowYoungConjugator t` is the relabeling permutation from `rowSuperstandard μ` to `t`. -/
theorem rowYoungConjugator_eq_relabelPerm_rowSuperstandard (t : YoungTableau μ) :
    rowYoungConjugator t =
      relabelPerm (StandardYoungTableau.rowSuperstandard μ).toTableau t := by
  conv_lhs => rw [← relabel_relabelPerm (StandardYoungTableau.rowSuperstandard μ).toTableau t]
  rw [rowYoungConjugator_relabel, rowYoungConjugator_rowSuperstandard, mul_one]

/-- Relabeling `rowSuperstandard μ` by `rowYoungConjugator t` recovers `t`. -/
@[simp]
theorem relabel_rowYoungConjugator_rowSuperstandard (t : YoungTableau μ) :
    relabel (rowYoungConjugator t) (StandardYoungTableau.rowSuperstandard μ).toTableau = t := by
  rw [rowYoungConjugator_eq_relabelPerm_rowSuperstandard, relabel_relabelPerm]

/-- `rowYoungConjugator` identifies `μ`-tableaux bijectively with `Equiv.Perm (Fin μ.card)`. -/
noncomputable def rowYoungConjugatorEquiv (μ : YoungDiagram) :
    YoungTableau μ ≃ Equiv.Perm (Fin μ.card) where
  toFun := rowYoungConjugator
  invFun σ := relabel σ (StandardYoungTableau.rowSuperstandard μ).toTableau
  left_inv := relabel_rowYoungConjugator_rowSuperstandard
  right_inv σ := by rw [rowYoungConjugator_relabel, rowYoungConjugator_rowSuperstandard, mul_one]

@[simp]
theorem rowYoungConjugatorEquiv_apply (t : YoungTableau μ) :
    rowYoungConjugatorEquiv μ t = rowYoungConjugator t :=
  (rfl)

@[simp]
theorem rowYoungConjugatorEquiv_symm_apply (σ : Equiv.Perm (Fin μ.card)) :
    (rowYoungConjugatorEquiv μ).symm σ =
      relabel σ (StandardYoungTableau.rowSuperstandard μ).toTableau :=
  (rfl)

/-- In `rowSuperstandard μ`, the row index of `k` coincides with
`youngBlock (shapePartition μ) k`. -/
theorem rowIndex_rowSuperstandard (k : Fin μ.card) :
    rowIndex (StandardYoungTableau.rowSuperstandard μ).toTableau k =
      youngBlock (shapePartition μ) k := by
  simpa using rowIndex_rowYoungConjugator (StandardYoungTableau.rowSuperstandard μ).toTableau k

/-- `rowYoungConjugator t` sends each `k` to a label in the same column as `k` in
`rowSuperstandard μ`. -/
theorem colIndex_rowYoungConjugator (t : YoungTableau μ) (k : Fin μ.card) :
    colIndex t (rowYoungConjugator t k) =
      colIndex (StandardYoungTableau.rowSuperstandard μ).toTableau k := by
  have h := colIndex_relabel (rowYoungConjugator t)
    (StandardYoungTableau.rowSuperstandard μ).toTableau (rowYoungConjugator t k)
  rwa [relabel_rowYoungConjugator_rowSuperstandard, Equiv.Perm.inv_def,
    Equiv.symm_apply_apply] at h

/-- **Minimal coset representative criterion for `rowYoungConjugator`.** The permutation
`rowYoungConjugator t` is a minimal left coset representative of `youngGenSet (shapePartition μ)`
if and only if `t` is row-standard. -/
theorem isMinimalCosetRep_youngGenSet_rowYoungConjugator_iff (t : YoungTableau μ) :
    (permCoxeterSystem μ.card).IsMinimalCosetRep (youngGenSet (shapePartition μ))
        (rowYoungConjugator t) ↔
      ∃ T : RowStandardYoungTableau μ, T.toTableau = t := by
  rw [youngGenSet, isMinimalCosetRep_fiberGenSet_iff (monotone_youngBlock (shapePartition μ)),
    exists_rowStandardYoungTableau_toTableau_eq_iff]
  set t₀ := (StandardYoungTableau.rowSuperstandard μ)
  constructor
  · intro hmin x y hrow hcol
    obtain ⟨a, rfl⟩ := (rowYoungConjugator t).surjective x
    obtain ⟨b, rfl⟩ := (rowYoungConjugator t).surjective y
    have hab_blk : youngBlock (shapePartition μ) a = youngBlock (shapePartition μ) b := by
      apply Fin.ext
      simpa only [rowIndex_rowYoungConjugator] using hrow
    have hab_row : rowIndex t₀.toTableau a = rowIndex t₀.toTableau b := by
      rw [rowIndex_rowSuperstandard, rowIndex_rowSuperstandard, hab_blk]
    have hab_lt : a < b := by
      rw [t₀.lt_iff_colIndex_lt hab_row]
      simpa only [colIndex_rowYoungConjugator] using hcol
    exact hmin hab_lt hab_blk
  · intro hrow a b hab hab_blk
    have hrow_eq : rowIndex t (rowYoungConjugator t a) = rowIndex t (rowYoungConjugator t b) := by
      rw [rowIndex_rowYoungConjugator, rowIndex_rowYoungConjugator, hab_blk]
    have hab_row₀ : rowIndex t₀.toTableau a = rowIndex t₀.toTableau b := by
      rw [rowIndex_rowSuperstandard, rowIndex_rowSuperstandard, hab_blk]
    have hcol_lt : colIndex t (rowYoungConjugator t a) < colIndex t (rowYoungConjugator t b) := by
      rw [colIndex_rowYoungConjugator, colIndex_rowYoungConjugator]
      exact (t₀.lt_iff_colIndex_lt hab_row₀).mp hab
    exact hrow hrow_eq hcol_lt

end YoungTableau

namespace RowStandardYoungTableau

variable {μ : YoungDiagram}

/-- For a row-standard tableau `T`, `rowYoungConjugator T.toTableau` is a minimal left coset
representative of `youngGenSet (shapePartition μ)`. -/
theorem isMinimalCosetRep_rowYoungConjugator (T : RowStandardYoungTableau μ) :
    (permCoxeterSystem μ.card).IsMinimalCosetRep (youngGenSet (shapePartition μ))
      (rowYoungConjugator T.toTableau) :=
  (isMinimalCosetRep_youngGenSet_rowYoungConjugator_iff T.toTableau).mpr ⟨T, rfl⟩

/-- **Equivalence between row-standard Young tableaux and minimal left coset representatives** of
the Young parabolic subgroup `youngGenSet (shapePartition μ)`. -/
noncomputable def equivMinimalCosetRep (μ : YoungDiagram) :
    RowStandardYoungTableau μ ≃
      {d : Equiv.Perm (Fin μ.card) //
        (permCoxeterSystem μ.card).IsMinimalCosetRep (youngGenSet (shapePartition μ)) d} :=
  Equiv.ofBijective
    (fun T ↦ ⟨rowYoungConjugator T.toTableau, T.isMinimalCosetRep_rowYoungConjugator⟩)
    ⟨fun _ _ h ↦
      toTableau_injective ((rowYoungConjugatorEquiv μ).injective (congrArg Subtype.val h)),
      fun ⟨d, hd⟩ ↦ by
        obtain ⟨T, hT⟩ := (isMinimalCosetRep_youngGenSet_rowYoungConjugator_iff
          ((rowYoungConjugatorEquiv μ).symm d)).mp
          (by simpa using hd)
        refine ⟨T, Subtype.ext ?_⟩
        dsimp only
        rw [hT]
        exact (rowYoungConjugatorEquiv μ).apply_symm_apply d⟩

@[simp]
theorem coe_equivMinimalCosetRep (T : RowStandardYoungTableau μ) :
    (equivMinimalCosetRep μ T : Equiv.Perm (Fin μ.card)) = rowYoungConjugator T.toTableau :=
  (rfl)

/-- **Equivalence between row-standard Young tableaux and `μ`-tabloids.** -/
noncomputable def equivTabloid (μ : YoungDiagram) :
    RowStandardYoungTableau μ ≃ Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ) :=
  Equiv.ofBijective (fun T ↦ tabloid T.toTableau)
    ⟨fun T U h ↦ rowIndex_injective μ (tabloid_eq_iff_rowIndex_eq.mp h), fun q ↦ by
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
      let d := (permCoxeterSystem μ.card).minimalCosetRep (youngGenSet (shapePartition μ)) w
      have hd : (permCoxeterSystem μ.card).IsMinimalCosetRep (youngGenSet (shapePartition μ)) d :=
        (permCoxeterSystem μ.card).isMinimalCosetRep_minimalCosetRep _ w
      let T := (equivMinimalCosetRep μ).symm ⟨d, hd⟩
      have hTd : rowYoungConjugator T.toTableau = d := by
        simpa only [← coe_equivMinimalCosetRep] using
          congrArg Subtype.val ((equivMinimalCosetRep μ).apply_symm_apply ⟨d, hd⟩)
      have hmem : w⁻¹ * d ∈ youngSubgroup (shapePartition μ) := by
        rw [← parabolic_youngGenSet]
        exact (permCoxeterSystem μ.card).inv_mul_minimalCosetRep_mem _ w
      refine ⟨T, ?_⟩
      dsimp only
      rw [tabloid_def, hTd, eq_comm, QuotientGroup.eq]
      exact hmem⟩

@[simp]
theorem equivTabloid_apply (T : RowStandardYoungTableau μ) :
    equivTabloid μ T = tabloid T.toTableau :=
  (rfl)

/-- **The number of row-standard Young tableaux of shape `μ`** is the multinomial coefficient
`|μ|! / ∏ i, μᵢ!`. -/
theorem card (μ : YoungDiagram) :
    Fintype.card (RowStandardYoungTableau μ) =
      μ.card.factorial / (μ.rowLens.map Nat.factorial).prod := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (equivTabloid μ), ← Subgroup.index_eq_card,
    youngSubgroup_index, shapePartition_parts, Multiset.map_coe, Multiset.prod_coe]

/-- For a row-standard tableau `T`, `i` is a left descent of `rowYoungConjugator T.toTableau`
precisely when `strandSucc i` sits in an earlier row of `T` than `strand i`. -/
theorem isLeftDescent_rowYoungConjugator_iff (T : RowStandardYoungTableau μ)
    (i : Fin (μ.card - 1)) :
    (permCoxeterSystem μ.card).IsLeftDescent (rowYoungConjugator T.toTableau) i ↔
      rowIndex T.toTableau (strandSucc i) < rowIndex T.toTableau (strand i) := by
  rw [isLeftDescent_permCoxeterSystem_iff]
  set w := rowYoungConjugator T.toTableau
  set t₀ := StandardYoungTableau.rowSuperstandard μ
  -- Pull row and column indices of `T` back along `w⁻¹` to `rowSuperstandard μ`.
  have hrow (x : Fin μ.card) : rowIndex T.toTableau x = rowIndex t₀.toTableau (w⁻¹ x) := by
    rw [rowIndex_rowSuperstandard, ← rowIndex_rowYoungConjugator T.toTableau (w⁻¹ x)]
    simp only [w, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  have hcol (x : Fin μ.card) : colIndex T.toTableau x = colIndex t₀.toTableau (w⁻¹ x) := by
    rw [← colIndex_rowYoungConjugator T.toTableau (w⁻¹ x)]
    simp only [w, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  -- In `rowSuperstandard μ`, strictly earlier rows carry strictly smaller labels.
  have hcell_lt {a b : Fin μ.card} (hr : rowIndex t₀.toTableau a < rowIndex t₀.toTableau b) :
      a < b := by
    set ca := t₀.toTableau.symm a
    set cb := t₀.toTableau.symm b
    have hfst : ca.1.1 < cb.1.1 := by simpa only [rowIndex_def] using hr
    have hread := YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt
      ((YoungDiagram.mem_cells _).mp ca.2) hfst
    have ha : (a : ℕ) = YoungDiagram.readingIndex μ ca.1 := by
      have := StandardYoungTableau.rowSuperstandard_apply_val μ ca
      rwa [← StandardYoungTableau.toTableau_apply, Equiv.apply_symm_apply] at this
    have hb : (b : ℕ) = YoungDiagram.readingIndex μ cb.1 := by
      have := StandardYoungTableau.rowSuperstandard_apply_val μ cb
      rwa [← StandardYoungTableau.toTableau_apply, Equiv.apply_symm_apply] at this
    exact Fin.lt_def.mpr (by omega)
  constructor
  · intro hlt
    rcases lt_trichotomy (rowIndex T.toTableau (strandSucc i))
        (rowIndex T.toTableau (strand i)) with hr | hr | hr
    · exact hr
    · exfalso
      have hr₀ : rowIndex t₀.toTableau (w⁻¹ (strandSucc i)) =
          rowIndex t₀.toTableau (w⁻¹ (strand i)) := by
        rwa [hrow, hrow] at hr
      have hcT : colIndex T.toTableau (strand i) < colIndex T.toTableau (strandSucc i) :=
        (T.lt_iff_colIndex_lt hr.symm).mp (Fin.lt_def.mpr (by simp))
      rw [hcol, hcol] at hcT
      exact lt_asymm hlt ((t₀.lt_iff_colIndex_lt hr₀.symm).mpr hcT)
    · rw [hrow, hrow] at hr
      exact absurd (hcell_lt hr) (lt_asymm hlt)
  · intro hr
    rw [hrow, hrow] at hr
    exact hcell_lt hr

/-- When `strand i` and `strandSucc i` lie in the same row of `T`, left multiplication by the
simple reflection `i` leaves minimal coset representatives. -/
theorem not_isMinimalCosetRep_simple_mul_of_rowIndex_eq (T : RowStandardYoungTableau μ)
    {i : Fin (μ.card - 1)}
    (h : rowIndex T.toTableau (strand i) = rowIndex T.toTableau (strandSucc i)) :
    ¬ (permCoxeterSystem μ.card).IsMinimalCosetRep (youngGenSet (shapePartition μ))
      ((permCoxeterSystem μ.card).simple i * rowYoungConjugator T.toTableau) := by
  rw [permCoxeterSystem_simple, ← rowYoungConjugator_relabel,
    isMinimalCosetRep_youngGenSet_rowYoungConjugator_iff]
  exact T.not_exists_relabel_transposition_of_rowIndex_eq h

end RowStandardYoungTableau

/-! ### Column-superstandard coset properties and Dipper–James dominance lemmas -/

/-- `rowYoungConjugator (colSuperstandard μ).toTableau` has no left descent in
`colSuperstandardGenSet μ`. -/
theorem forall_not_isLeftDescent_colSuperstandardGenSet_rowYoungConjugator (μ : YoungDiagram) :
    ∀ i ∈ colSuperstandardGenSet μ,
      ¬ (permCoxeterSystem μ.card).IsLeftDescent
        (rowYoungConjugator (StandardYoungTableau.colSuperstandard μ).toTableau) i := by
  rw [colSuperstandardGenSet,
    forall_not_isLeftDescent_fiberGenSet_iff (monotone_colIndex_colSuperstandard μ)]
  intro x y hxy hcol
  set t_c := StandardYoungTableau.colSuperstandard μ
  set t₀ := StandardYoungTableau.rowSuperstandard μ
  set w := rowYoungConjugator t_c.toTableau
  have hrow_lt : rowIndex t_c.toTableau x < rowIndex t_c.toTableau y :=
    (t_c.lt_iff_rowIndex_lt hcol).mp hxy
  have hrow₀ : rowIndex t₀.toTableau (w⁻¹ x) < rowIndex t₀.toTableau (w⁻¹ y) := by
    rw [rowIndex_rowSuperstandard, rowIndex_rowSuperstandard,
      ← rowIndex_rowYoungConjugator t_c.toTableau (w⁻¹ x),
      ← rowIndex_rowYoungConjugator t_c.toTableau (w⁻¹ y)]
    simpa only [w, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using hrow_lt
  set cx := t₀.toTableau.symm (w⁻¹ x)
  set cy := t₀.toTableau.symm (w⁻¹ y)
  have hfst : cx.1.1 < cy.1.1 := by simpa only [rowIndex_def] using hrow₀
  have hread := YoungDiagram.readingIndex_lt_readingIndex_of_fst_lt
    ((YoungDiagram.mem_cells _).mp cx.2) hfst
  have hx : (w⁻¹ x : ℕ) = YoungDiagram.readingIndex μ cx.1 := by
    have := StandardYoungTableau.rowSuperstandard_apply_val μ cx
    rwa [← StandardYoungTableau.toTableau_apply, Equiv.apply_symm_apply] at this
  have hy : (w⁻¹ y : ℕ) = YoungDiagram.readingIndex μ cy.1 := by
    have := StandardYoungTableau.rowSuperstandard_apply_val μ cy
    rwa [← StandardYoungTableau.toTableau_apply, Equiv.apply_symm_apply] at this
  exact Fin.lt_def.mpr (by omega)

/-- Coxeter lengths add across `v * rowYoungConjugator (colSuperstandard μ).toTableau` for every
`v` in the column group of `colSuperstandard μ`. -/
theorem length_mul_rowYoungConjugator_colSuperstandard {μ : YoungDiagram}
    {v : Equiv.Perm (Fin μ.card)}
    (hv : v ∈ colSubgroup (StandardYoungTableau.colSuperstandard μ).toTableau) :
    (permCoxeterSystem μ.card).length
        (v * rowYoungConjugator (StandardYoungTableau.colSuperstandard μ).toTableau) =
      (permCoxeterSystem μ.card).length v +
        (permCoxeterSystem μ.card).length
          (rowYoungConjugator (StandardYoungTableau.colSuperstandard μ).toTableau) := by
  rw [← parabolic_colSuperstandardGenSet] at hv
  exact (permCoxeterSystem μ.card).length_mul_of_forall_not_isLeftDescent hv
    (forall_not_isLeftDescent_colSuperstandardGenSet_rowYoungConjugator μ)

namespace RowStandardYoungTableau

variable {μ : YoungDiagram}

/-- **Every column-group relabeling of `colSuperstandard μ` is row-standard.** -/
noncomputable def colSuperstandardRelabel
    (v : colSubgroup (StandardYoungTableau.colSuperstandard μ).toTableau) :
    RowStandardYoungTableau μ where
  toTableau :=
    relabel (v : Equiv.Perm (Fin μ.card)) (StandardYoungTableau.colSuperstandard μ).toTableau
  row_strict' {r j₁ j₂} hj hcell := by
    let σ : Equiv.Perm (Fin μ.card) := v
    have hσ : σ ∈ colSubgroup (StandardYoungTableau.colSuperstandard μ).toTableau := v.2
    set t_c := (StandardYoungTableau.colSuperstandard μ).toTableau
    rw [relabel_apply, relabel_apply]
    set x := t_c ⟨(r, j₁), μ.up_left_mem le_rfl hj.le hcell⟩
    set y := t_c ⟨(r, j₂), hcell⟩
    have hcx : colIndex t_c (σ x) = j₁ := by
      rw [mem_colSubgroup.mp hσ x]
      exact colIndex_apply t_c _
    have hcy : colIndex t_c (σ y) = j₂ := by
      rw [mem_colSubgroup.mp hσ y]
      exact colIndex_apply t_c _
    by_contra hge
    have hle : colIndex t_c (σ y) ≤ colIndex t_c (σ x) :=
      monotone_colIndex_colSuperstandard μ (not_lt.mp hge)
    rw [hcx, hcy] at hle
    exact not_lt_of_ge hle hj

@[simp]
theorem colSuperstandardRelabel_toTableau
    (v : colSubgroup (StandardYoungTableau.colSuperstandard μ).toTableau) :
    (colSuperstandardRelabel v).toTableau =
      relabel (v : Equiv.Perm (Fin μ.card)) (StandardYoungTableau.colSuperstandard μ).toTableau :=
  (rfl)

@[simp]
theorem colSuperstandardRelabel_one :
    colSuperstandardRelabel (1 : colSubgroup (StandardYoungTableau.colSuperstandard μ).toTableau) =
      (StandardYoungTableau.colSuperstandard μ).toRowStandardYoungTableau :=
  toTableau_injective (by simp)

/-- Distinct elements of `colSubgroup (colSuperstandard μ)` produce distinct row-standard
tableaux. -/
theorem colSuperstandardRelabel_injective :
    Function.Injective (colSuperstandardRelabel (μ := μ)) := by
  intro v₁ v₂ h
  have htab : tabloid (colSuperstandardRelabel v₁).toTableau =
      tabloid (colSuperstandardRelabel v₂).toTableau := congrArg (fun S ↦ tabloid S.toTableau) h
  rw [colSuperstandardRelabel_toTableau, colSuperstandardRelabel_toTableau,
    tabloid_relabel, tabloid_relabel] at htab
  exact smul_tabloid_injective (StandardYoungTableau.colSuperstandard μ).toTableau htab

end RowStandardYoungTableau

namespace StandardYoungTableau

variable {μ : YoungDiagram}

/-- If `i` is a left descent of `relabelPerm (colSuperstandard μ).toTableau T.toTableau` for a
standard tableau `T`, then `strandSucc i` sits strictly to the left of and strictly below
`strand i` in `T`. -/
theorem colIndex_lt_and_rowIndex_lt_of_isLeftDescent_relabelPerm_colSuperstandard
    (T : StandardYoungTableau μ) {i : Fin (μ.card - 1)}
    (hi : (permCoxeterSystem μ.card).IsLeftDescent
      (relabelPerm (colSuperstandard μ).toTableau T.toTableau) i) :
    colIndex T.toTableau (strandSucc i) < colIndex T.toTableau (strand i) ∧
      rowIndex T.toTableau (strand i) < rowIndex T.toTableau (strandSucc i) := by
  rw [isLeftDescent_permCoxeterSystem_iff] at hi
  set t_c := colSuperstandard μ
  set d := relabelPerm t_c.toTableau T.toTableau
  have hd_rel : relabel d t_c.toTableau = T.toTableau := relabel_relabelPerm _ _
  have hrow_d (x : Fin μ.card) : rowIndex t_c.toTableau (d⁻¹ x) = rowIndex T.toTableau x := by
    rw [← hd_rel, rowIndex_relabel]
  have hcol_d (x : Fin μ.card) : colIndex t_c.toTableau (d⁻¹ x) = colIndex T.toTableau x := by
    rw [← hd_rel, colIndex_relabel]
  -- Monotonicity of `colIndex` on `colSuperstandard μ` forces `strandSucc i` weakly left of
  -- `strand i`, and column-strictness of `T` rules out equality of columns.
  have hcol_le : colIndex T.toTableau (strandSucc i) ≤ colIndex T.toTableau (strand i) := by
    rw [← hcol_d, ← hcol_d]
    exact monotone_colIndex_colSuperstandard μ hi.le
  have hcol_lt : colIndex T.toTableau (strandSucc i) < colIndex T.toTableau (strand i) := by
    refine lt_of_le_of_ne hcol_le fun heq ↦ ?_
    have hrow_T : rowIndex T.toTableau (strand i) < rowIndex T.toTableau (strandSucc i) :=
      (T.lt_iff_rowIndex_lt heq.symm).mp (Fin.lt_def.mpr (by simp))
    rw [← hrow_d, ← hrow_d] at hrow_T
    rw [← hcol_d, ← hcol_d] at heq
    exact lt_asymm hi (t_c.lt_of_rowIndex_lt heq.symm hrow_T)
  -- If `strandSucc i` were also in the same or an earlier row than `strand i`, the corner cell
  -- `(r₁, c₂)` would make `strandSucc i < strand i` by row- and column-strictness of `T`.
  refine ⟨hcol_lt, ?_⟩
  rcases lt_trichotomy (rowIndex T.toTableau (strand i))
      (rowIndex T.toTableau (strandSucc i)) with hr | hr | hr
  · exact hr
  · exact absurd
      ((T.lt_iff_colIndex_lt hr).mp (Fin.lt_def.mpr (by simp))) (not_lt_of_gt hcol_lt)
  · exfalso
    set r₁ := rowIndex T.toTableau (strandSucc i)
    set c₁ := colIndex T.toTableau (strandSucc i)
    set r₂ := rowIndex T.toTableau (strand i)
    set c₂ := colIndex T.toTableau (strand i)
    have hm₂ : (r₂, c₂) ∈ μ := rowIndex_colIndex_mem T.toTableau (strand i)
    have hm₁₂ : (r₁, c₂) ∈ μ := μ.up_left_mem hr.le le_rfl hm₂
    have hm₁₁ : (r₁, c₁) ∈ μ := μ.up_left_mem le_rfl hcol_lt.le hm₁₂
    have h₁ : T ⟨(r₁, c₁), hm₁₁⟩ < T ⟨(r₁, c₂), hm₁₂⟩ := T.row_strict hcol_lt hm₁₂
    have h₂ : T ⟨(r₁, c₂), hm₁₂⟩ < T ⟨(r₂, c₂), hm₂⟩ := T.col_strict hr hm₂
    have hs₁ : T ⟨(r₁, c₁), hm₁₁⟩ = strandSucc i := by
      rw [← toTableau_apply]
      refine rowIndex_colIndex_injective T.toTableau (Prod.ext ?_ ?_)
      · exact rowIndex_apply T.toTableau ⟨(r₁, c₁), hm₁₁⟩
      · exact colIndex_apply T.toTableau ⟨(r₁, c₁), hm₁₁⟩
    have hs₂ : T ⟨(r₂, c₂), hm₂⟩ = strand i := by
      rw [← toTableau_apply]
      refine rowIndex_colIndex_injective T.toTableau (Prod.ext ?_ ?_)
      · exact rowIndex_apply T.toTableau ⟨(r₂, c₂), hm₂⟩
      · exact colIndex_apply T.toTableau ⟨(r₂, c₂), hm₂⟩
    rw [hs₁] at h₁
    rw [hs₂] at h₂
    exact lt_asymm (h₁.trans h₂) (Fin.lt_def.mpr (by simp))

end StandardYoungTableau

namespace YoungTableau

variable {μ : YoungDiagram}

private theorem rowCount_relabel_transposition_eq (s : YoungTableau μ) (i : Fin (μ.card - 1))
    {m : ℕ} (hm : m ≤ (i : ℕ) ∨ (i : ℕ) + 2 ≤ m) (r : ℕ) :
    rowCount (relabel (transposition i) s) m r = rowCount s m r := by
  classical
  have hinv : (transposition i)⁻¹ = transposition i := by
    ext x
    simp [transposition_eq_swap]
  have hself (x : Fin μ.card) : transposition i (transposition i x) = x := by
    simp [transposition_eq_swap]
  rw [rowCount_def, rowCount_def]
  symm
  refine Finset.card_equiv (transposition i) fun x ↦ ?_
  simp only [mem_filter, mem_univ, true_and, rowIndex_relabel, hinv, hself,
    val_transposition_apply]
  refine and_congr_left' ?_
  split_ifs <;> omega

private theorem rowCount_relabel_transposition_succ (s : YoungTableau μ) (i : Fin (μ.card - 1))
    (r : ℕ) :
    rowCount (relabel (transposition i) s) ((i : ℕ) + 1) r =
      rowCount s (i : ℕ) r + if rowIndex s (strandSucc i) ≤ r then 1 else 0 := by
  have h := rowCount_succ (relabel (transposition i) s) (strand i) r
  have hinv : (transposition i)⁻¹ (strand i) = strandSucc i := by
    have hi : (transposition i)⁻¹ = transposition i := by ext x; simp [transposition_eq_swap]
    simp [hi]
  rw [val_strand, rowCount_relabel_transposition_eq s i (Or.inl le_rfl) r,
    rowIndex_relabel, hinv] at h
  exact h

/-- Swapping `strand i` and `strandSucc i` when `strandSucc i` lies in an earlier row than
`strand i` raises the tabloid in the dominance order. -/
theorem tabloidDominates_relabel_transposition_self {u : YoungTableau μ} {i : Fin (μ.card - 1)}
    (h : rowIndex u (strandSucc i) < rowIndex u (strand i)) :
    TabloidDominates (relabel (transposition i) u) u := by
  rw [tabloidDominates_iff]
  intro m r
  rcases eq_or_ne m ((i : ℕ) + 1) with rfl | hm
  · rw [rowCount_relabel_transposition_succ]
    have hu := rowCount_succ u (strand i) r
    rw [val_strand] at hu
    rw [hu]
    split_ifs <;> omega
  · rw [rowCount_relabel_transposition_eq u i (by omega) r]

/-- **Dipper–James transposition diamond property for `TabloidDominates`.** If `{u}` dominates
`{s}` and `strandSucc i` sits in an earlier row of `u` than `strand i`, then
`{relabel (transposition i) u}` dominates `{relabel (transposition i) s}`. -/
theorem TabloidDominates.relabel_transposition {u s : YoungTableau μ} {i : Fin (μ.card - 1)}
    (hus : TabloidDominates u s) (hu : rowIndex u (strandSucc i) < rowIndex u (strand i)) :
    TabloidDominates (relabel (transposition i) u) (relabel (transposition i) s) := by
  rw [tabloidDominates_iff] at hus ⊢
  intro m r
  rcases eq_or_ne m ((i : ℕ) + 1) with rfl | hm
  · rw [rowCount_relabel_transposition_succ, rowCount_relabel_transposition_succ]
    have hsk := hus (i : ℕ) r
    have hsk2 := hus ((i : ℕ) + 1 + 1) r
    have hu1 := rowCount_succ u (strand i) r
    have hu2 := rowCount_succ u (strandSucc i) r
    have hs1 := rowCount_succ s (strand i) r
    have hs2 := rowCount_succ s (strandSucc i) r
    rw [val_strand] at hu1 hs1
    rw [val_strandSucc] at hu2 hs2
    split_ifs at hu1 hu2 hs1 hs2 ⊢ <;> omega
  · rw [rowCount_relabel_transposition_eq u i (by omega) r,
      rowCount_relabel_transposition_eq s i (by omega) r]
    exact hus m r

end YoungTableau

end TauCeti
