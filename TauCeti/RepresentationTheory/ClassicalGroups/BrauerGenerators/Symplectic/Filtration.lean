/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerAlgebra.DiagramIdeal
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Equivariance
public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.TraceSplitting
public import TauCeti.RepresentationTheory.Subrepresentation.Quotient
import Mathlib.Algebra.Order.Star.Rat
import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.ThreeStrands

/-!
# The trace filtration of the symplectic tensor powers

The Brauer algebra `B_d(-2n)` acts on `V^{⊗d}`, `V = k^{2n}`, through the standard alternating form
(`TauCeti.brauerActionSymp`), and is filtered by its diagram ideals
`I_j = TauCeti.BrauerAlgebra.diagramIdeal k (-(2 * n : k)) d j`, the spans of the diagrams with at
least `j` caps. Pushing that filtration forward along the action defines the **symplectic trace
filtration**

`F_j = span {ρ(b) v : b ∈ I_j, v ∈ V^{⊗d}}` (`TauCeti.symplecticTraceFiltration k n d j`),

the tensors obtained by inserting at least `j` copies of the invariant bivector of `-J`. Each step
`F_j` is a subrepresentation of the symplectic group, because `B_d(-2n)` acts by intertwiners
(`TauCeti.commute_brauerActionSymp_tensorPower`), and is stable under the whole Brauer algebra,
because `I_j` is a left ideal (`TauCeti.brauerActionSymp_apply_mem_symplecticTraceFiltration`). The
steps decrease from `F_0 = ⊤` (`TauCeti.symplecticTraceFiltration_zero`) to `F_j = ⊥` once
`2 * j > d` (`TauCeti.symplecticTraceFiltration_eq_bot`).

Over every commutative ring, the first step `F_1` coincides with the space of symplectic trace
tensors `TauCeti.symplecticTraceTensors k n d`, the sum of the images of the single-arc generators
(`TauCeti.symplecticTraceFiltration_one`): each single-arc generator is the image of a cap-cup
diagram in `I_1`, and conversely every diagram with a cap stacks a cap-cup diagram loop-freely
above another diagram (`TauCeti.BrauerDiagram.exists_composeDiagram_capCup_eq`), so its image lies
in the image of that arc. Rewriting
`TauCeti.isCompl_symplecticHarmonicTensorsSubrep_symplecticTraceTensors` along
`F_1 = symplecticTraceTensors` therefore identifies the top graded piece `V^{⊗d} / F_1` over a
star-ordered field with the symplectic harmonic tensors
(`TauCeti.quotientSymplecticTraceFiltrationOneEquivHarmonicTensors`).

## Main definitions

* `TauCeti.symplecticTraceFiltration`: the step `F_j` of the trace filtration, a subrepresentation
  of the symplectic group acting on `V^{⊗d}`.
* `TauCeti.quotientSymplecticTraceFiltrationOneEquivHarmonicTensors`: over a star-ordered field, the
  top graded piece `V^{⊗d} / F_1` is equivalent as a representation of `Sp(2n)` to the symplectic
  harmonic tensors.

## Main results

* `TauCeti.range_brauerActionSymp_le_symplecticTraceFiltration` and
  `TauCeti.symplecticTraceFiltration_toSubmodule_le_iff`: `F_j` is the least submodule containing
  the image of every element of `I_j`.
* `TauCeti.brauerActionSymp_apply_mem_symplecticTraceFiltration`: `F_j` is stable under `B_d(-2n)`.
* `TauCeti.symplecticTraceFiltration_zero`, `TauCeti.symplecticTraceFiltration_antitone` and
  `TauCeti.symplecticTraceFiltration_eq_bot`: boundary values and antitonicity of the filtration.
* `TauCeti.range_brauerActionSymp_le_symplecticTraceTensors` and
  `TauCeti.symplecticTraceFiltration_one`: **`F_1` is the space of symplectic trace tensors** over
  every commutative ring.

## References

* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 10, for the symplectic harmonic tensors and the trace filtration.
* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* S. Dipper, S. Doty and J. Hu, *Brauer algebras, symplectic Schur algebras and Schur-Weyl duality*,
  Transactions of the American Mathematical Society 360 (2008), 189-213.
-/

public section

universe u

namespace TauCeti

open BrauerAlgebra
open scoped TensorProduct

section CommRing

variable (k : Type u) [CommRing k] (n d : ℕ)

/-- **The trace filtration** of the symplectic tensor power `V^{⊗d}`, `V = k^{2n}`: its step `F_j`
is the sum of the images of the elements of the diagram ideal `I_j` of `B_d(-2n)` acting through
`TauCeti.brauerActionSymp`, that is, the span of the tensors obtained by inserting at least `j`
copies of the invariant bivector of `-J`. It is a subrepresentation because the Brauer algebra acts
by intertwiners of the symplectic group. -/
noncomputable def symplecticTraceFiltration (j : ℕ) :
    Subrepresentation ((stdSymplecticRep k n).tensorPower d) where
  toSubmodule :=
    ⨆ b ∈ diagramIdeal k (-(2 * n : k)) d j, LinearMap.range (brauerActionSymp k n d b)
  apply_mem_toSubmodule g := by
    suffices h :
        (⨆ b ∈ diagramIdeal k (-(2 * n : k)) d j, LinearMap.range (brauerActionSymp k n d b)) ≤
          Submodule.comap ((stdSymplecticRep k n).tensorPower d g)
            (⨆ b ∈ diagramIdeal k (-(2 * n : k)) d j, LinearMap.range (brauerActionSymp k n d b))
      from fun x hx => h hx
    refine iSup₂_le fun b hb => ?_
    rintro _ ⟨y, rfl⟩
    have h := LinearMap.congr_fun (commute_brauerActionSymp_tensorPower k n d b g).eq y
    rw [mul_apply_eq_comp, mul_apply_eq_comp] at h
    rw [Submodule.mem_comap, ← h]
    exact Submodule.mem_iSup_of_mem b <| Submodule.mem_iSup_of_mem hb <|
      LinearMap.mem_range_self _ _

@[simp]
theorem symplecticTraceFiltration_toSubmodule (j : ℕ) :
    (symplecticTraceFiltration k n d j).toSubmodule =
      ⨆ b ∈ diagramIdeal k (-(2 * n : k)) d j, LinearMap.range (brauerActionSymp k n d b) :=
  (rfl)

variable {k n d}

/-- The image of every element of the diagram ideal `I_j` lies in the step `F_j`. In particular,
`I_(j+1)` maps `F_j` into `F_(j+1)`, so it acts by zero on the graded piece `F_j / F_(j+1)`. -/
theorem range_brauerActionSymp_le_symplecticTraceFiltration {j : ℕ}
    {b : BrauerAlgebra k (-(2 * n : k)) d} (hb : b ∈ diagramIdeal k (-(2 * n : k)) d j) :
    LinearMap.range (brauerActionSymp k n d b) ≤ (symplecticTraceFiltration k n d j).toSubmodule :=
  le_iSup₂_of_le b hb le_rfl

/-- The order-level universal property: the step `F_j` lies in a submodule exactly when the image of
every element of `I_j` does. -/
theorem symplecticTraceFiltration_toSubmodule_le_iff {j : ℕ}
    {p : Submodule k (⨂[k]^d ((Fin n ⊕ Fin n) → k))} :
    (symplecticTraceFiltration k n d j).toSubmodule ≤ p ↔
      ∀ b ∈ diagramIdeal k (-(2 * n : k)) d j, LinearMap.range (brauerActionSymp k n d b) ≤ p := by
  simp only [symplecticTraceFiltration_toSubmodule, iSup_le_iff]

/-- **The steps of the symplectic trace filtration are stable under the Brauer algebra**, because
the diagram ideals are left ideals. -/
theorem brauerActionSymp_apply_mem_symplecticTraceFiltration {j : ℕ}
    (b : BrauerAlgebra k (-(2 * n : k)) d) {x : ⨂[k]^d ((Fin n ⊕ Fin n) → k)}
    (hx : x ∈ (symplecticTraceFiltration k n d j).toSubmodule) :
    brauerActionSymp k n d b x ∈ (symplecticTraceFiltration k n d j).toSubmodule := by
  suffices h : (symplecticTraceFiltration k n d j).toSubmodule ≤
      Submodule.comap (brauerActionSymp k n d b) (symplecticTraceFiltration k n d j).toSubmodule
    from h hx
  refine symplecticTraceFiltration_toSubmodule_le_iff.mpr fun c hc => ?_
  rintro _ ⟨y, rfl⟩
  rw [Submodule.mem_comap, ← mul_apply_eq_comp, ← map_mul]
  exact range_brauerActionSymp_le_symplecticTraceFiltration
    ((diagramIdeal k (-(2 * n : k)) d j).mul_mem_left b c hc) (LinearMap.mem_range_self _ y)

variable (k n d)

/-- **The step `F_0` of the trace filtration is everything**: the unit of `B_d(-2n)` lies in `I_0`
and acts as the identity. -/
@[simp]
theorem symplecticTraceFiltration_zero : symplecticTraceFiltration k n d 0 = ⊤ := by
  refine Subrepresentation.toSubmodule_injective ?_
  rw [Subrepresentation.toSubmodule_top, eq_top_iff]
  intro x _
  have h := range_brauerActionSymp_le_symplecticTraceFiltration (b := 1)
    (by rw [diagramIdeal_zero]; exact TwoSidedIdeal.mem_top _) (LinearMap.mem_range_self _ x)
  rwa [map_one, one_apply_eq_self] at h

/-- **The symplectic trace filtration decreases**, as the diagram ideals do. -/
theorem symplecticTraceFiltration_antitone : Antitone (symplecticTraceFiltration k n d) :=
  fun _ _ hij => Subrepresentation.toSubmodule_le_toSubmodule.mp <|
    symplecticTraceFiltration_toSubmodule_le_iff.mpr fun _ hb =>
      range_brauerActionSymp_le_symplecticTraceFiltration (diagramIdeal_antitone k _ d hij hb)

/-- **The symplectic trace filtration vanishes once `2 * j > d`**, since a diagram on `d` strands
has at most `d / 2` caps. -/
theorem symplecticTraceFiltration_eq_bot {j : ℕ} (hj : d < 2 * j) :
    symplecticTraceFiltration k n d j = ⊥ := by
  refine Subrepresentation.toSubmodule_injective ?_
  rw [Subrepresentation.toSubmodule_bot, eq_bot_iff, symplecticTraceFiltration_toSubmodule_le_iff]
  intro b hb
  rw [diagramIdeal_eq_bot k _ d hj, TwoSidedIdeal.mem_bot] at hb
  simp [hb]

variable {k n d}

/-- **An element of `I_1` maps into the symplectic trace tensors.** A diagram with a cap is a
loop-free stack `capCup c e ∘ X` (`TauCeti.BrauerDiagram.exists_composeDiagram_capCup_eq`), so it
acts as the single-arc generator `TauCeti.symplecticCupCapAt k n d c e` after the action of `X`. -/
theorem range_brauerActionSymp_le_symplecticTraceTensors {b : BrauerAlgebra k (-(2 * n : k)) d}
    (hb : b ∈ diagramIdeal k (-(2 * n : k)) d 1) :
    LinearMap.range (brauerActionSymp k n d b) ≤ (symplecticTraceTensors k n d).toSubmodule := by
  rw [mem_diagramIdeal_iff_mem_span] at hb
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨D, hD, rfl⟩ := hx
    obtain ⟨a, ha⟩ : D.bottomCap.Nonempty := by
      rw [← Finset.card_pos]
      have := D.propagatingNumber_add_card_bottomCap
      simp only [Set.mem_ofPred_eq] at hD
      omega
    obtain ⟨c, e, X, hce, hloop, -, rfl⟩ := BrauerDiagram.exists_composeDiagram_capCup_eq ha
    rw [← of_mul_of_of_middleLoopCount_eq_zero hloop, map_mul, brauerActionSymp_of_capCup k n d hce,
      Module.End.mul_eq_comp, LinearMap.range_comp]
    exact LinearMap.map_le_range.trans (range_symplecticCupCapAt_le_symplecticTraceTensors hce)
  | zero => simp
  | add x y _ _ hx hy =>
    rintro _ ⟨v, rfl⟩
    rw [map_add, LinearMap.add_apply]
    exact add_mem (hx (LinearMap.mem_range_self _ v)) (hy (LinearMap.mem_range_self _ v))
  | smul r x _ hx =>
    rintro _ ⟨v, rfl⟩
    rw [map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ r (hx (LinearMap.mem_range_self _ v))

variable (k n d)

/-- **The first step of the symplectic trace filtration is the space of trace tensors**, over every
commutative ring: the tensors obtained from `I_1` are the sums of tensors obtained by inserting the
invariant bivector of `-J` into a single pair of slots. -/
theorem symplecticTraceFiltration_one :
    symplecticTraceFiltration k n d 1 = symplecticTraceTensors k n d := by
  refine Subrepresentation.toSubmodule_injective (le_antisymm ?_ ?_)
  · exact symplecticTraceFiltration_toSubmodule_le_iff.mpr fun _ hb =>
      range_brauerActionSymp_le_symplecticTraceTensors hb
  · refine symplecticTraceTensors_toSubmodule_le_iff.mpr fun i j hij => ?_
    rw [← brauerActionSymp_of_capCup k n d hij]
    exact range_brauerActionSymp_le_symplecticTraceFiltration (of_capCup_mem_diagramIdeal_one hij)

end CommRing

/-! ### The top graded piece -/

section StarOrderedField

variable (k : Type u) [Field k] [PartialOrder k] [StarRing k] [StarOrderedRing k] (n d : ℕ)

/-- **The top graded piece of the symplectic trace filtration is the space of harmonic tensors.**
Over a star-ordered field, such as `ℚ`, `ℝ` or `ℂ` (with `ComplexOrder`), the quotient
`V^{⊗d} / F_1` is equivalent, as a representation of the symplectic group, to the symplectic
harmonic tensors: these complement `F_1`, the space of trace tensors
(`TauCeti.isCompl_symplecticHarmonicTensorsSubrep_symplecticTraceTensors`), and the equivalence
sends the class of a tensor to its harmonic component
(`Subrepresentation.quotientEquivOfIsCompl`). -/
noncomputable def quotientSymplecticTraceFiltrationOneEquivHarmonicTensors :
    (symplecticTraceFiltration k n d 1).quotient.Equiv
      (symplecticHarmonicTensorsSubrep k n d).toRepresentation :=
  Subrepresentation.quotientEquivOfIsCompl <| by
    rw [symplecticTraceFiltration_one]
    exact (isCompl_symplecticHarmonicTensorsSubrep_symplecticTraceTensors k n d).symm

variable {k n d}

/-- The inverse of the equivalence sends a harmonic tensor to its class modulo `F_1`. -/
@[simp]
theorem quotientSymplecticTraceFiltrationOneEquivHarmonicTensors_symm_apply
    (v : (symplecticHarmonicTensorsSubrep k n d).toSubmodule) :
    (quotientSymplecticTraceFiltrationOneEquivHarmonicTensors k n d).symm v =
      Submodule.Quotient.mk (v : ⨂[k]^d ((Fin n ⊕ Fin n) → k)) :=
  Subrepresentation.quotientEquivOfIsCompl_symm_apply _ v

/-- The class of a symplectic harmonic tensor goes back to that tensor. -/
theorem quotientSymplecticTraceFiltrationOneEquivHarmonicTensors_apply_mk_of_mem
    {x : ⨂[k]^d ((Fin n ⊕ Fin n) → k)} (hx : x ∈ symplecticHarmonicTensors k n d) :
    (quotientSymplecticTraceFiltrationOneEquivHarmonicTensors k n d
      (Submodule.Quotient.mk x) : ⨂[k]^d ((Fin n ⊕ Fin n) → k)) = x := by
  have h := (quotientSymplecticTraceFiltrationOneEquivHarmonicTensors k n d).apply_symm_apply
    ⟨x, by rwa [symplecticHarmonicTensorsSubrep_toSubmodule]⟩
  rw [quotientSymplecticTraceFiltrationOneEquivHarmonicTensors_symm_apply] at h
  exact congrArg Subtype.val h

/-- A tensor differs from the harmonic tensor its class corresponds to by an element of `F_1`, a sum
of symplectic trace tensors. -/
theorem sub_quotientSymplecticTraceFiltrationOneEquivHarmonicTensors_apply_mk_mem
    (x : ⨂[k]^d ((Fin n ⊕ Fin n) → k)) :
    x - (quotientSymplecticTraceFiltrationOneEquivHarmonicTensors k n d
      (Submodule.Quotient.mk x) : ⨂[k]^d ((Fin n ⊕ Fin n) → k)) ∈
        symplecticTraceFiltration k n d 1 :=
  Subrepresentation.sub_quotientEquivOfIsCompl_apply_mk_mem _ x

end StarOrderedField

-- On two strands `F_1` is the symplectic trace line spanned by the invariant bivector, and
-- `F_2 = 0`; on one strand already `F_1 = 0`.
example : symplecticTraceFiltration ℚ 2 2 1 = symplecticTraceLine ℚ 2 := by
  rw [symplecticTraceFiltration_one, symplecticTraceTensors_two]

example : symplecticTraceFiltration ℚ 2 2 2 = ⊥ :=
  symplecticTraceFiltration_eq_bot ℚ 2 2 (by norm_num)

example : symplecticTraceFiltration ℚ 2 1 1 = ⊥ :=
  symplecticTraceFiltration_eq_bot ℚ 2 1 (by norm_num)

-- In symplectic rank one (`V = ℚ²`) on three strands, outside the stable range `d ≤ n`, `F_1` has
-- dimension `4` rather than `3 * 2 = 6` because the three cup placements satisfy a linear relation,
-- and the top graded piece `V^{⊗3} / F_1` has dimension `8 - 4 = 4`.
example : Module.finrank ℚ (symplecticTraceFiltration ℚ 1 3 1).toSubmodule = 4 := by
  rw [symplecticTraceFiltration_one]
  exact finrank_symplecticTraceTensors_one_three

example : Module.finrank ℚ
    (⨂[ℚ]^3 ((Fin 1 ⊕ Fin 1) → ℚ) ⧸ (symplecticTraceFiltration ℚ 1 3 1).toSubmodule) = 4 := by
  rw [LinearEquiv.finrank_eq
      (quotientSymplecticTraceFiltrationOneEquivHarmonicTensors ℚ 1 3).toLinearEquiv,
    symplecticHarmonicTensorsSubrep_toSubmodule]
  exact finrank_symplecticHarmonicTensors_one_three

end TauCeti
