/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.TopologicalRing
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.MonoidAlgebra.Grading
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Homogeneous Novikov series

Let `f : H → ι` be a degree function on the exponents of Novikov series. A Novikov series is
*homogeneous of degree `i`* when its support lies in the fibre `f ⁻¹' {i}`. These series form the
submodule `TauCeti.NovikovSeries.gradeBy R N f i`, the Novikov analogue of Mathlib's
`AddMonoidAlgebra.gradeBy`. For an additive degree function the pieces multiply as a graded
monoid, and they are independent.

Unlike the group ring, the Novikov ring is in general *not* the direct sum of its homogeneous
pieces: every finite sum of homogeneous series meets only finitely many degrees, whereas a
completed series may meet infinitely many fibres. When `f` takes only finitely many values,
cutting a series along the fibres (`TauCeti.NovikovSeries.gradeProj`) decomposes the whole
completion as the internal direct sum of its homogeneous pieces. Conversely, whenever the period
`N` is bounded above on every fibre of `f`, for instance when `f` is injective, the homogeneous
pieces span only the finitely supported series, so the group ring `R[H]` is their span and the
Novikov ring is its period completion.

For coefficients in a ring, each homogeneous piece is closed in the period topology and the span of
the homogeneous pieces is dense. Restricting to nonnegative periods cuts the nonnegative subring
into closed homogeneous pieces `TauCeti.NovikovSeries.nonnegGradeBy R N f i`. Over a commutative
ring, an additive degree function makes their direct sum an injective graded subalgebra of the
nonnegative subring (`TauCeti.NovikovSeries.coeAlgHom_nonnegGradeBy_injective`), dense in the
period topology (`TauCeti.NovikovSeries.denseRange_coeAlgHom_nonnegGradeBy`). If a sequence of
nonnegative-period exponents tends to `+∞` in period through pairwise distinct degrees, the sum of
its unit monomials lies in the nonnegative subring and in no finite sum of homogeneous pieces
(`TauCeti.NovikovSeries.iSup_nonnegGradeBy_ne_top_of_tendsto`).

## Main definitions

* `TauCeti.NovikovSeries.supported R N s`: the Novikov series supported in the set `s`.
* `TauCeti.NovikovSeries.gradeBy R N f i`: the Novikov series of degree `i` for the degree
  function `f`.
* `TauCeti.NovikovSeries.gradeProj R N f i`: the homogeneous part of degree `i` of a Novikov
  series.
* `TauCeti.NovikovSeries.nonnegGradeBy R N f i`: the series of the nonnegative subring homogeneous
  of degree `i`.

## Main results

* `TauCeti.NovikovSeries.gradeBy.gradedMonoid`: for an additive degree function, the homogeneous
  pieces form a graded monoid.
* `TauCeti.NovikovSeries.iSupIndep_gradeBy`: the homogeneous pieces are independent.
* `TauCeti.NovikovSeries.isInternal_gradeBy`: for a degree function with finite range, the Novikov
  ring is the internal direct sum of its homogeneous pieces.
* `TauCeti.NovikovSeries.finite_image_support_of_mem_iSup_gradeBy`: every finite sum of homogeneous
  series meets only finitely many degrees.
* `TauCeti.NovikovSeries.isClosed_gradeBy` and `TauCeti.NovikovSeries.dense_iSup_gradeBy`: each
  homogeneous piece is closed in the period topology, and their span is dense.
* `TauCeti.NovikovSeries.coeAlgHom_nonnegGradeBy_injective` and
  `TauCeti.NovikovSeries.denseRange_coeAlgHom_nonnegGradeBy`: the direct sum of the nonnegative
  homogeneous pieces embeds as a dense subalgebra of the nonnegative subring.
* `TauCeti.NovikovSeries.iSup_nonnegGradeBy_ne_top_of_tendsto`: when nonnegative periods tend to
  `+∞` across infinitely many degrees, the homogeneous pieces do not span the nonnegative subring.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the construction of
  the Novikov ring in the chapter on quantum cohomology.
-/

public section

noncomputable section

open Filter Function Set Topology
open scoped DirectSum

namespace TauCeti

namespace NovikovSeries

variable {R H ι : Type*}

section Semiring

variable [Semiring R]

section AddZeroClass

variable [AddZeroClass H] {N : H →+ ℝ}

variable (R N) in
/-- The Novikov series supported in the set `s`, the Novikov analogue of `Finsupp.supported`. -/
def supported (s : Set H) : Submodule R (NovikovSeries R H N) where
  carrier := {a | a.support ⊆ s}
  zero_mem' := by simp
  add_mem' ha hb := (support_add_subset _ _).trans (union_subset ha hb)
  smul_mem' r _ ha := (support_smul_subset r _).trans ha

/-- A series lies in `supported R N s` exactly when its support lies in `s`. -/
theorem mem_supported {s : Set H} {a : NovikovSeries R H N} :
    a ∈ supported R N s ↔ a.support ⊆ s :=
  Iff.rfl

variable (R N) in
/-- The Novikov series of degree `i` for the degree function `f`: those whose support lies in
the fibre `f ⁻¹' {i}`. -/
def gradeBy (f : H → ι) (i : ι) : Submodule R (NovikovSeries R H N) :=
  supported R N (f ⁻¹' {i})

/-- A series has degree `i` exactly when its support lies in the fibre over `i`. -/
theorem mem_gradeBy_iff {f : H → ι} {i : ι} {a : NovikovSeries R H N} :
    a ∈ gradeBy R N f i ↔ a.support ⊆ f ⁻¹' {i} :=
  Iff.rfl

/-- The monomial `r e^h` has degree `f h`. -/
theorem single_mem_gradeBy (f : H → ι) (h : H) (r : R) :
    (single h r : NovikovSeries R H N) ∈ gradeBy R N f (f h) := fun _ hg => by
  rw [mem_singleton_iff.1 (support_single_subset h r hg), mem_preimage, mem_singleton_iff]

/-- There are no nonzero series of a degree that no exponent has. -/
theorem gradeBy_eq_bot {f : H → ι} {i : ι} (hi : i ∉ range f) : gradeBy R N f i = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun a ha => support_eq_empty.1 ?_
  exact eq_empty_of_forall_notMem fun h hh => hi ⟨h, ha hh⟩

/-- If every exponent has degree `i`, every series is homogeneous of degree `i`. -/
theorem gradeBy_eq_top {f : H → ι} {i : ι} (hf : ∀ h, f h = i) : gradeBy R N f i = ⊤ :=
  Submodule.eq_top_iff'.2 fun _ h _ => hf h

/-- Homogeneous series of different degrees span independent submodules. -/
theorem iSupIndep_gradeBy (f : H → ι) : iSupIndep (gradeBy R N f) := by
  intro i
  -- Every homogeneous piece of degree `j ≠ i` consists of series avoiding the fibre over `i`.
  have hle : ⨆ (j) (_ : j ≠ i), gradeBy R N f j ≤ supported R N (f ⁻¹' {i})ᶜ :=
    iSup₂_le fun j hj a ha h hh => by
      rw [mem_compl_iff, mem_preimage, mem_singleton_iff, (ha hh : f h = j)]
      exact hj
  refine (Submodule.disjoint_def.2 fun a ha ha' => support_eq_empty.1 ?_).mono_right hle
  exact eq_empty_of_forall_notMem fun h hh => ha' hh (ha hh)

/-- A homogeneous series is finitely supported if the period is bounded above on its fibre. -/
theorem finite_support_of_mem_gradeBy {f : H → ι} {i : ι} (hf : BddAbove (N '' (f ⁻¹' {i})))
    {a : NovikovSeries R H N} (ha : a ∈ gradeBy R N f i) : a.support.Finite :=
  finite_support_of_bddAbove_image (hf.mono (image_mono ha))

/-- A finitely supported series is a finite sum of homogeneous series. -/
theorem ofFinsupp_mem_iSup_gradeBy (f : H → ι) (x : H →₀ R) :
    ofFinsupp x ∈ ⨆ i, gradeBy R N f i := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add h r x _ _ hx =>
    rw [map_add, ofFinsupp_single]
    exact add_mem (Submodule.mem_iSup_of_mem (f h) (single_mem_gradeBy f h r)) hx

/-- If the period is bounded above on every fibre of the degree function, the homogeneous series
span exactly the finitely supported series. -/
theorem mem_iSup_gradeBy_iff {f : H → ι} (hf : ∀ i, BddAbove (N '' (f ⁻¹' {i})))
    {a : NovikovSeries R H N} : a ∈ ⨆ i, gradeBy R N f i ↔ a.support.Finite := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · exact Submodule.iSup_induction (motive := fun b => b.support.Finite) _ ha
      (fun i _ hb => finite_support_of_mem_gradeBy (hf i) hb) (by simp)
      fun _ _ hb hc => (hb.union hc).subset (support_add_subset _ _)
  · obtain ⟨x, rfl⟩ := mem_range_ofFinsupp_iff.2 ha
    exact ofFinsupp_mem_iSup_gradeBy f x

/-- For an injective degree function, a series of the degree of `h` is the monomial at `h`
with its own coefficient. -/
theorem eq_single_of_mem_gradeBy {f : H → ι} (hf : Injective f) {h : H}
    {a : NovikovSeries R H N} (ha : a ∈ gradeBy R N f (f h)) : a = single h (a.coeff h) := by
  ext g
  by_cases hg : g = h
  · rw [hg, coeff_single_same]
  · rw [coeff_single_of_ne hg]
    by_contra hag
    exact hg (hf (ha (mem_support.2 hag)))

/-- Every finite sum of homogeneous Novikov series meets only finitely many degrees. -/
theorem finite_image_support_of_mem_iSup_gradeBy {f : H → ι} {a : NovikovSeries R H N}
    (ha : a ∈ ⨆ i, gradeBy R N f i) : (f '' a.support).Finite :=
  Submodule.iSup_induction (motive := fun b => (f '' b.support).Finite) _ ha
    (fun i _ hb => (finite_singleton i).subset (image_subset_iff.2 hb)) (by simp)
    fun a b ha hb => (ha.union hb).subset <|
      (image_mono (support_add_subset a b)).trans (image_union f _ _).le

section Proj

variable [DecidableEq ι]

variable (R N) in
/-- The homogeneous part of degree `i` of a Novikov series: the coefficients at exponents of
degree `i`, with all other coefficients set to zero. -/
def gradeProj (f : H → ι) (i : ι) : NovikovSeries R H N →ₗ[R] NovikovSeries R H N where
  toFun a := ⟨fun h => if f h = i then a.coeff h else 0, fun C =>
    (a.finite_lt C).subset fun h hh => ⟨fun ha => hh.1 (by simp [ha]), hh.2⟩⟩
  map_add' a b := by
    ext h
    by_cases hf : f h = i <;> simp [hf, coeff_add]
  map_smul' r a := by
    ext h
    by_cases hf : f h = i <;> simp [hf, coeff_smul]

@[simp]
theorem coeff_gradeProj (f : H → ι) (i : ι) (a : NovikovSeries R H N) (h : H) :
    (gradeProj R N f i a).coeff h = if f h = i then a.coeff h else 0 :=
  (rfl)

theorem gradeProj_mem_gradeBy (f : H → ι) (i : ι) (a : NovikovSeries R H N) :
    gradeProj R N f i a ∈ gradeBy R N f i :=
  mem_gradeBy_iff.2 fun h hh => by
    by_contra hne
    have hne' : f h ≠ i := hne
    exact mem_support.1 hh (by simp [hne'])

theorem gradeProj_eq_self_of_mem_gradeBy {f : H → ι} {i : ι} {a : NovikovSeries R H N}
    (ha : a ∈ gradeBy R N f i) : gradeProj R N f i a = a := by
  ext h
  by_cases hf : f h = i
  · simp [hf]
  · have hzero : a.coeff h = 0 := by_contra fun hh => hf (ha (mem_support.2 hh))
    simp [hf, hzero]

theorem gradeProj_eq_zero_of_mem_gradeBy {f : H → ι} {i j : ι} (hij : i ≠ j)
    {a : NovikovSeries R H N} (ha : a ∈ gradeBy R N f i) : gradeProj R N f j a = 0 := by
  ext h
  by_cases hf : f h = j
  · have hzero : a.coeff h = 0 :=
      by_contra fun hh => hij ((ha (mem_support.2 hh)).symm.trans hf)
    simp [hf, hzero]
  · simp [hf]

/-- If every exponent degree lies in the finite set `T`, a Novikov series is the sum of its
homogeneous parts of degrees in `T`. -/
theorem sum_gradeProj {f : H → ι} (T : Finset ι) (hT : ∀ h, f h ∈ T) (a : NovikovSeries R H N) :
    ∑ i ∈ T, gradeProj R N f i a = a := by
  ext h
  simp [hT h]

end Proj

/-- For a degree function with finite range, the homogeneous pieces span the Novikov ring. -/
theorem iSup_gradeBy_eq_top_of_finite_range {f : H → ι} (hf : (range f).Finite) :
    ⨆ i, gradeBy R N f i = ⊤ := by
  classical
  refine eq_top_iff.2 fun a _ => ?_
  rw [← sum_gradeProj hf.toFinset (fun h => hf.mem_toFinset.2 ⟨h, rfl⟩) a]
  exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i (gradeProj_mem_gradeBy f i a)

end AddZeroClass

/-- For an additive degree function, the homogeneous Novikov series form a graded monoid. -/
instance gradeBy.gradedMonoid [AddMonoid H] {N : H →+ ℝ} [AddMonoid ι] (f : H →+ ι) :
    SetLike.GradedMonoid (gradeBy R N f) where
  one_mem h hh := by
    rw [← single_zero_one] at hh
    rw [mem_preimage, mem_singleton_iff, mem_singleton_iff.1 (support_single_subset 0 1 hh),
      map_zero]
  mul_mem i j a b ha hb h hh := by
    obtain ⟨u, hu, v, hv, rfl⟩ := support_mul_subset a b hh
    rw [mem_preimage, mem_singleton_iff, map_add, (ha hu : f u = i), (hb hv : f v = j)]

end Semiring

/-- The inclusion of the group ring into the Novikov series preserves and reflects the degree. -/
theorem ofAddMonoidAlgebra_mem_gradeBy_iff [CommSemiring R] [AddMonoid H] {N : H →+ ℝ}
    {f : H → ι} {i : ι} {x : AddMonoidAlgebra R H} :
    (ofAddMonoidAlgebra x : NovikovSeries R H N) ∈ gradeBy R N f i ↔
      x ∈ AddMonoidAlgebra.gradeBy R f i := by
  simp only [mem_gradeBy_iff, AddMonoidAlgebra.mem_gradeBy_iff, subset_def, mem_support,
    coeff_ofAddMonoidAlgebra, Finset.mem_coe, Finsupp.mem_support_iff]

section Topology

section Ring

variable [Ring R] [AddZeroClass H] {N : H →+ ℝ}

/-- For a degree function with finite range, the Novikov ring is the internal direct sum of its
homogeneous pieces. -/
theorem isInternal_gradeBy [DecidableEq ι] {f : H → ι} (hf : (range f).Finite) :
    DirectSum.IsInternal (gradeBy R N f) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_gradeBy f) (iSup_gradeBy_eq_top_of_finite_range hf)

/-- The series supported in a set `s` form a closed subset in the period topology. -/
theorem isClosed_supported (s : Set H) :
    IsClosed (supported R N s : Set (NovikovSeries R H N)) := by
  have hset : (supported R N s : Set (NovikovSeries R H N)) =
      ⋂ h ∈ sᶜ, {a : NovikovSeries R H N | a.coeff h = 0} := by
    ext a
    simp only [SetLike.mem_coe, mem_supported, subset_def, mem_support, mem_iInter, mem_compl_iff]
    exact ⟨fun ha h hns => by_contra fun hc => hns (ha h hc),
      fun ha h hc => by_contra fun hns => hc (ha h hns)⟩
  rw [hset]
  exact isClosed_biInter fun h _ => (isLocallyConstant_coeff h).isClosed_fiber 0

/-- Every homogeneous piece of Novikov series is closed in the period topology. -/
theorem isClosed_gradeBy (f : H → ι) (i : ι) :
    IsClosed (gradeBy R N f i : Set (NovikovSeries R H N)) :=
  isClosed_supported (f ⁻¹' {i})

instance (f : H → ι) (i : ι) : CompleteSpace (gradeBy R N f i) :=
  (isClosed_gradeBy f i).completeSpace_coe

/-- The span of the homogeneous pieces is dense in the Novikov ring: it contains all finitely
supported series. -/
theorem dense_iSup_gradeBy (f : H → ι) :
    Dense ((⨆ i, gradeBy R N f i : Submodule R (NovikovSeries R H N)) :
      Set (NovikovSeries R H N)) :=
  denseRange_ofFinsupp.mono <| by
    rintro _ ⟨x, rfl⟩
    exact ofFinsupp_mem_iSup_gradeBy f x

@[simp]
theorem topologicalClosure_iSup_gradeBy (f : H → ι) :
    (⨆ i, gradeBy R N f i).topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.1 (dense_iSup_gradeBy f)

/-- If an injective sequence of exponents has periods tending to `+∞`, the monomials along it have
convergent sum with those prescribed coefficients. -/
theorem hasSum_single_of_tendsto {g : ℕ → H} (hg : Injective g)
    (htend : Tendsto (fun n => N (g n)) atTop atTop) (c : ℕ → R) :
    ∃ a : NovikovSeries R H N, HasSum (fun n => single (g n) (c n)) a ∧
      (∀ n, a.coeff (g n) = c n) ∧ ∀ h ∉ range g, a.coeff h = 0 := by
  classical
  let coeffFn : H → R := fun h => if hh : h ∈ range g then c hh.choose else 0
  have hcg (n : ℕ) : coeffFn (g n) = c n := by
    have hr : g n ∈ range g := ⟨n, rfl⟩
    dsimp only [coeffFn]
    rw [dite_eq_left hr, hg hr.choose_spec]
  have hczero (h : H) (hh : h ∉ range g) : coeffFn h = 0 := by
    dsimp only [coeffFn]
    exact dite_eq_right hh
  have hfin (C : ℝ) : {h | coeffFn h ≠ 0 ∧ N h < C}.Finite := by
    obtain ⟨M, hM⟩ := eventually_atTop.1 (htend.eventually_ge_atTop C)
    refine ((Finset.range M).finite_toSet.image g).subset fun h ⟨hh, hlt⟩ => ?_
    by_cases hr : h ∈ range g
    · refine ⟨hr.choose, Finset.mem_coe.2 (Finset.mem_range.2 ?_), hr.choose_spec⟩
      by_contra hge
      exact (hM hr.choose (le_of_not_gt hge)).not_gt (hr.choose_spec.symm ▸ hlt)
    · exact absurd (hczero h hr) hh
  let a : NovikovSeries R H N := ⟨coeffFn, hfin⟩
  refine ⟨a, ?_, hcg, hczero⟩
  rw [HasSum, tendsto_nhds_iff]
  intro C
  obtain ⟨M, hM⟩ := eventually_atTop.1 (htend.eventually_ge_atTop C)
  filter_upwards [eventually_ge_atTop (Finset.range M)] with s hs h hh
  have hsum := congrArg (fun x : H → R => x h)
    (map_sum (coeffAddMonoidHom (R := R) (N := N)) (fun n => single (g n) (c n)) s)
  simp only [coeffAddMonoidHom_apply, Finset.sum_apply] at hsum
  rw [hsum]
  by_cases hr : h ∈ range g
  · obtain ⟨n, rfl⟩ := hr
    have hnM : n < M := by_contra fun hge => (hM n (le_of_not_gt hge)).not_gt hh
    have hns : n ∈ s := hs (Finset.mem_range.2 hnM)
    rw [Finset.sum_eq_single n (fun m _ hmn => coeff_single_of_ne (mt (fun e => hg e) hmn.symm) _)
      (fun hn => absurd hns hn), coeff_single_same]
    exact (hcg n).symm
  · rw [Finset.sum_eq_zero fun m _ => coeff_single_of_ne (fun e => hr ⟨m, e.symm⟩) _]
    exact (hczero h hr).symm

end Ring

section NonnegSubring

variable [CommRing R] [AddMonoid H] {N : H →+ ℝ}

/-- The inclusion of the nonnegative subring into the Novikov series as an `R`-linear map. -/
private def nonnegSubtypeLinearMap : nonnegSubring R N →ₗ[R] NovikovSeries R H N where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' := coe_smul_nonnegSubring

variable (R N) in
/-- The homogeneous piece of degree `i` of the nonnegative subring: the series of nonnegative
periods supported on `f ⁻¹' {i}`. -/
def nonnegGradeBy (f : H → ι) (i : ι) : Submodule R (nonnegSubring R N) :=
  (gradeBy R N f i).comap nonnegSubtypeLinearMap

@[simp]
theorem mem_nonnegGradeBy_iff {f : H → ι} {i : ι} {a : nonnegSubring R N} :
    a ∈ nonnegGradeBy R N f i ↔ (a : NovikovSeries R H N) ∈ gradeBy R N f i :=
  Submodule.mem_comap

theorem single_mem_nonnegGradeBy {h : H} (hh : 0 ≤ N h) (f : H → ι) (r : R) :
    (⟨single h r, single_mem_nonnegSubring hh r⟩ : nonnegSubring R N) ∈
      nonnegGradeBy R N f (f h) :=
  mem_nonnegGradeBy_iff.2 (single_mem_gradeBy f h r)

theorem nonnegGradeBy_eq_bot {f : H → ι} {i : ι} (hi : i ∉ range f) :
    nonnegGradeBy R N f i = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun a ha => Subtype.ext <|
    (Submodule.eq_bot_iff _).1 (gradeBy_eq_bot (R := R) (N := N) hi)
      (a : NovikovSeries R H N) (mem_nonnegGradeBy_iff.1 ha)

theorem nonnegGradeBy_eq_top {f : H → ι} {i : ι} (hf : ∀ h, f h = i) :
    nonnegGradeBy R N f i = ⊤ :=
  Submodule.eq_top_iff'.2 fun a => mem_nonnegGradeBy_iff.2 <|
    Submodule.eq_top_iff'.1 (gradeBy_eq_top (R := R) (N := N) hf) (a : NovikovSeries R H N)

/-- Each homogeneous piece of the nonnegative subring is closed in the period topology. -/
theorem isClosed_nonnegGradeBy (f : H → ι) (i : ι) :
    IsClosed (nonnegGradeBy R N f i : Set (nonnegSubring R N)) := by
  have hset : (nonnegGradeBy R N f i : Set (nonnegSubring R N)) =
      Subtype.val ⁻¹' (gradeBy R N f i : Set (NovikovSeries R H N)) := by
    ext a
    exact mem_nonnegGradeBy_iff
  rw [hset]
  exact (isClosed_gradeBy f i).preimage continuous_subtype_val

instance (f : H → ι) (i : ι) : CompleteSpace (nonnegGradeBy R N f i) :=
  (isClosed_nonnegGradeBy f i).completeSpace_coe

/-- For an additive degree function, the homogeneous pieces of the nonnegative subring form a
graded monoid. -/
instance nonnegGradeBy.gradedMonoid [AddMonoid ι] (f : H →+ ι) :
    SetLike.GradedMonoid (nonnegGradeBy R N f) where
  one_mem := mem_nonnegGradeBy_iff.2 (SetLike.one_mem_graded (gradeBy R N f))
  mul_mem _ _ _ _ ha hb := mem_nonnegGradeBy_iff.2 <|
    SetLike.mul_mem_graded (mem_nonnegGradeBy_iff.1 ha) (mem_nonnegGradeBy_iff.1 hb)

/-- Homogeneous pieces of distinct degrees in the nonnegative subring are independent. -/
theorem iSupIndep_nonnegGradeBy (f : H → ι) : iSupIndep (nonnegGradeBy R N f) := by
  intro i
  rw [Submodule.disjoint_def]
  intro a ha ha'
  have hle : (⨆ (j) (_ : j ≠ i), nonnegGradeBy R N f j).map nonnegSubtypeLinearMap ≤
      ⨆ (j) (_ : j ≠ i), gradeBy R N f j := by
    rw [Submodule.map_le_iff_le_comap]
    exact iSup₂_le fun j hj x hx =>
      Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem j
        (Submodule.mem_iSup_of_mem hj (mem_nonnegGradeBy_iff.1 hx)))
  exact Subtype.ext <| Submodule.disjoint_def.1 (iSupIndep_gradeBy f i) (a : NovikovSeries R H N)
    (mem_nonnegGradeBy_iff.1 ha) (hle (Submodule.mem_map_of_mem ha'))

/-- The linear map from the direct sum of homogeneous pieces into the nonnegative subring is
injective. -/
theorem coeLinearMap_nonnegGradeBy_injective [DecidableEq ι] (f : H → ι) :
    Injective (DirectSum.coeLinearMap (nonnegGradeBy R N f)) :=
  (iSupIndep_nonnegGradeBy f).dfinsupp_lsum_injective

/-- For an additive degree function, the direct sum of homogeneous pieces embeds as a graded
subalgebra into the nonnegative subring. -/
theorem coeAlgHom_nonnegGradeBy_injective [DecidableEq ι] [AddMonoid ι] (f : H →+ ι) :
    Injective (DirectSum.coeAlgHom (nonnegGradeBy R N f)) := by
  have hcoe : (DirectSum.coeAlgHom (nonnegGradeBy R N f) : _ → nonnegSubring R N) =
      DirectSum.coeLinearMap (nonnegGradeBy R N f) := by
    ext x : 1
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i y => simp
    | add u v hu hv => simp [map_add, hu, hv]
  rw [hcoe]
  exact coeLinearMap_nonnegGradeBy_injective f

/-- A finitely supported series lies in the nonnegative subring when its support has nonnegative
periods. -/
theorem ofFinsupp_mem_nonnegSubring {x : H →₀ R} (hx : ∀ h ∈ x.support, 0 ≤ N h) :
    ofFinsupp x ∈ nonnegSubring R N :=
  mem_nonnegSubring.2 fun h hh => by
    rw [coeff_ofFinsupp]
    exact Finsupp.notMem_support_iff.1 fun hm => (hx h hm).not_gt hh

/-- A finite combination supported in nonnegative periods lies in the span of the homogeneous
pieces of the nonnegative subring. -/
theorem ofFinsupp_mem_iSup_nonnegGradeBy (f : H → ι) {x : H →₀ R}
    (hx : ∀ h ∈ x.support, 0 ≤ N h) :
    (⟨ofFinsupp x, ofFinsupp_mem_nonnegSubring hx⟩ : nonnegSubring R N) ∈
      ⨆ i, nonnegGradeBy R N f i := by
  induction x using Finsupp.induction with
  | zero =>
    convert zero_mem (⨆ i, nonnegGradeBy R N f i)
    ext h
    simp
  | single_add h r x hnotMem hr ih =>
    have hh : 0 ≤ N h := hx h <| Finsupp.mem_support_iff.2 <| by
      simpa [Finsupp.notMem_support_iff.1 hnotMem] using hr
    have hx' : ∀ g ∈ x.support, 0 ≤ N g := fun g hg => hx g <| Finsupp.mem_support_iff.2 <| by
      have hgh : g ≠ h := fun e => hnotMem (e ▸ hg)
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hgh, zero_add]
      exact Finsupp.mem_support_iff.1 hg
    have heq : (⟨ofFinsupp (Finsupp.single h r + x), ofFinsupp_mem_nonnegSubring hx⟩ :
        nonnegSubring R N) =
        ⟨single h r, single_mem_nonnegSubring hh r⟩ +
        ⟨ofFinsupp x, ofFinsupp_mem_nonnegSubring hx'⟩ := by
      ext g
      simp [map_add]
    rw [heq]
    exact add_mem (Submodule.mem_iSup_of_mem (f h) (single_mem_nonnegGradeBy hh f r)) (ih hx')

/-- The span of the homogeneous pieces is dense in the nonnegative subring: every nonnegative
series is approximated by its truncations, which are finite sums of nonnegative monomials. -/
theorem dense_iSup_nonnegGradeBy (f : H → ι) :
    Dense ((⨆ i, nonnegGradeBy R N f i : Submodule R (nonnegSubring R N)) :
      Set (nonnegSubring R N)) := by
  intro a
  have hbasis : (𝓝 a).HasBasis (fun _ : ℝ => True)
      fun C => Subtype.val ⁻¹' {b | b - (a : NovikovSeries R H N) ∈ periodFiltration R N C} := by
    rw [nhds_subtype]
    exact (hasBasis_nhds (a : NovikovSeries R H N)).comap Subtype.val
  rw [mem_closure_iff_nhds_basis hbasis]
  intro C _
  have hsupp : ∀ h ∈ (trunc C (a : NovikovSeries R H N)).support, 0 ≤ N h := by
    intro h hh
    by_contra hlt
    exact (Finsupp.mem_support_iff.1 hh) <| by
      rw [trunc_apply]
      split_ifs
      · exact mem_nonnegSubring.1 a.2 h (lt_of_not_ge hlt)
      · rfl
  let t : nonnegSubring R N := ⟨ofFinsupp (trunc C (a : NovikovSeries R H N)),
    ofFinsupp_mem_nonnegSubring hsupp⟩
  refine ⟨t, ofFinsupp_mem_iSup_nonnegGradeBy f hsupp, ?_⟩
  rw [mem_preimage, mem_ofPred_eq, ← neg_sub]
  exact neg_mem (sub_ofFinsupp_trunc_mem_periodFiltration C (a : NovikovSeries R H N))

/-- For an additive degree function, the direct sum of the nonnegative homogeneous pieces has dense
image in the nonnegative subring, so its completion in the period topology is the whole nonnegative
subring. -/
theorem denseRange_coeAlgHom_nonnegGradeBy [DecidableEq ι] [AddMonoid ι] (f : H →+ ι) :
    DenseRange (DirectSum.coeAlgHom (nonnegGradeBy R N f)) := by
  have hr : range (DirectSum.coeAlgHom (nonnegGradeBy R N f)) =
      ((⨆ i, nonnegGradeBy R N f i : Submodule R (nonnegSubring R N)) :
        Set (nonnegSubring R N)) := by
    rw [Submodule.iSup_eq_toSubmodule_range]
    rfl
  rw [DenseRange, hr]
  exact dense_iSup_nonnegGradeBy f

@[simp]
theorem topologicalClosure_iSup_nonnegGradeBy (f : H → ι) :
    (⨆ i, nonnegGradeBy R N f i).topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.1 (dense_iSup_nonnegGradeBy f)

/-- Every finite sum of nonnegative homogeneous series meets only finitely many degrees. -/
theorem finite_image_support_of_mem_iSup_nonnegGradeBy {f : H → ι} {a : nonnegSubring R N}
    (ha : a ∈ ⨆ i, nonnegGradeBy R N f i) : (f '' (a : NovikovSeries R H N).support).Finite := by
  have hle : (⨆ i, nonnegGradeBy R N f i).map nonnegSubtypeLinearMap ≤ ⨆ i, gradeBy R N f i := by
    rw [Submodule.map_le_iff_le_comap]
    exact iSup_le fun i x hx =>
      Submodule.mem_comap.2 (Submodule.mem_iSup_of_mem i (mem_nonnegGradeBy_iff.1 hx))
  exact finite_image_support_of_mem_iSup_gradeBy (hle (Submodule.mem_map_of_mem ha))

/-- For a degree function with finite range, the homogeneous pieces span the nonnegative subring. -/
theorem iSup_nonnegGradeBy_eq_top_of_finite_range {f : H → ι} (hf : (range f).Finite) :
    ⨆ i, nonnegGradeBy R N f i = ⊤ := by
  classical
  refine eq_top_iff.2 fun a _ => ?_
  have hmem (i : ι) : gradeProj R N f i (a : NovikovSeries R H N) ∈ nonnegSubring R N :=
    mem_nonnegSubring.2 fun h hh => by
      rw [coeff_gradeProj]
      split_ifs
      · exact mem_nonnegSubring.1 a.2 h hh
      · rfl
  let p (i : ι) : nonnegSubring R N := ⟨gradeProj R N f i (a : NovikovSeries R H N), hmem i⟩
  have hsum : ∑ i ∈ hf.toFinset, p i = a := Subtype.ext <|
    (map_sum (nonnegSubring R N).subtype p hf.toFinset).trans
      (sum_gradeProj hf.toFinset (fun g => hf.mem_toFinset.2 ⟨g, rfl⟩) (a : NovikovSeries R H N))
  rw [← hsum]
  exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i
    (mem_nonnegGradeBy_iff.2 (gradeProj_mem_gradeBy f i (a : NovikovSeries R H N)))

/-- For a degree function with finite range, the nonnegative subring is the internal direct sum of
its homogeneous pieces. -/
theorem isInternal_nonnegGradeBy [DecidableEq ι] {f : H → ι} (hf : (range f).Finite) :
    DirectSum.IsInternal (nonnegGradeBy R N f) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_nonnegGradeBy f) (iSup_nonnegGradeBy_eq_top_of_finite_range hf)

/-- **Dense but proper graded subalgebra.** Over a nontrivial ring, if a sequence of exponents of
nonnegative period has periods tending to `+∞` and pairwise distinct degrees, the sum of its unit
monomials lies in the nonnegative subring and in no finite sum of homogeneous pieces, so the
algebraic direct sum does not exhaust the nonnegative subring. -/
theorem iSup_nonnegGradeBy_ne_top_of_tendsto [Nontrivial R] {f : H → ι} {g : ℕ → H}
    (hnonneg : ∀ n, 0 ≤ N (g n)) (htend : Tendsto (fun n => N (g n)) atTop atTop)
    (hinj : Injective (f ∘ g)) : ⨆ i, nonnegGradeBy R N f i ≠ ⊤ := by
  obtain ⟨a, _, hcg, hzero⟩ := hasSum_single_of_tendsto hinj.of_comp htend (fun _ => (1 : R))
  have ha : a ∈ nonnegSubring R N := mem_nonnegSubring.2 fun h hh => by
    by_cases hr : h ∈ range g
    · obtain ⟨n, rfl⟩ := hr
      exact absurd hh (hnonneg n).not_gt
    · exact hzero h hr
  intro htop
  have hmem : (⟨a, ha⟩ : nonnegSubring R N) ∈ ⨆ i, nonnegGradeBy R N f i :=
    htop.symm ▸ Submodule.mem_top
  have hfin := finite_image_support_of_mem_iSup_nonnegGradeBy hmem
  refine (infinite_range_of_injective hinj) (hfin.subset ?_)
  rintro _ ⟨n, rfl⟩
  exact ⟨g n, mem_support.2 (by rw [hcg n]; exact one_ne_zero), rfl⟩

end NonnegSubring

end Topology

end NovikovSeries

end TauCeti
