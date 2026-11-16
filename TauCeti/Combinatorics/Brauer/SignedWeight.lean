/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Generator
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Pfaffian-signed arc weights of Brauer diagrams

In the orthogonal action of the Brauer algebra, an arc of a diagram carries a symmetric pairing and
the diagram weight is an unoriented product over the arcs. In the symplectic action, caps and cups
pair boundary labels against an alternating form while through strands carry Kronecker deltas with
opposite signs depending on direction, so the pair weight
`W : (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → R` is **skew-symmetric**, `W y x = -W x y`. Reversing the
orientation of an arc negates its factor, and reordering the arcs does not change the product, so an
orientation of the arcs must be accompanied by the parity of the permutation that orders their
endpoints.

Every Brauer diagram `D` on `k` strands is obtained by transporting the identity diagram
`permToBrauer 1` along a permutation `π : Equiv.Perm (Fin k ⊕ Fin k)` of the `2 * k` boundary
points: `π` sends the `r`-th identity strand `(Sum.inl r, Sum.inr r)` to an oriented arc of `D`.
This file constructs a canonical such permutation `TauCeti.BrauerDiagram.arcPerm`, listing the `k`
arcs in increasing order of their lower ends, and defines the **signed weight**

`D.signedWeight W = (sign D.arcPerm : ℤ) • ∏ r : Fin k, W (D.arcPerm (inl r)) (D.arcPerm (inr r))`.

When `W` is skew-symmetric, this value is **independent of the choice of transporting permutation**:
any `π` with `PerfectMatching.congr π (permToBrauer 1) = D` gives the same signed product
(`TauCeti.BrauerDiagram.signedWeight_eq_of_congr_permToBrauer_one`). Indeed, the stabilizer of
`permToBrauer 1` consists of the permutations that permute the `k` strands — where `sumCongr α α`
has sign `1` and reindexes the product — and flip the two endpoints of some subset `S` of strands,
where the sign `(-1) ^ #S` of the `S`-involution cancels the `#S` sign changes of `W`. This is the
same sign cancellation that makes the Pfaffian of an alternating matrix well defined.

Once transport independence is in place, every diagram operation becomes a permutation-sign
identity: transporting `D` along `π` multiplies the pulled-back signed weight by `sign π`
(`TauCeti.BrauerDiagram.signedWeight_congr`), reconnecting two distinct arcs negates the pulled-back
weight (`TauCeti.BrauerDiagram.signedWeight_reconnect`), reflecting `D` multiplies by `(-1) ^ k`
(`TauCeti.BrauerDiagram.signedWeight_flip`), a permutation diagram `permToBrauer σ` carries `sign σ`
(`TauCeti.BrauerDiagram.signedWeight_permToBrauer`), and a cap-cup diagram `capCup a b` carries `-1`
from the single transposition that bends the identity diagram into it
(`TauCeti.BrauerDiagram.signedWeight_capCup`).

## Main definitions

* `TauCeti.BrauerDiagram.arcPerm`: the canonical permutation of `Fin k ⊕ Fin k` transporting
  `permToBrauer 1` to `D`, ordering the arcs by their lower ends.
* `TauCeti.BrauerDiagram.signedWeight`: the Pfaffian-signed product of pair weights over the arcs of
  a Brauer diagram.

## Main results

* `TauCeti.BrauerDiagram.congr_arcPerm_permToBrauer_one`: `D.arcPerm` transports `permToBrauer 1` to
  `D`, with `TauCeti.BrauerDiagram.arcPerm_permToBrauer_one` showing `(permToBrauer 1).arcPerm = 1`.
* `TauCeti.BrauerDiagram.signedWeight_eq_of_congr_permToBrauer_one`: **transport independence** for
  skew-symmetric pair weights.
* `TauCeti.BrauerDiagram.signedWeight_congr`, `TauCeti.BrauerDiagram.signedWeight_reconnect` and
  `TauCeti.BrauerDiagram.signedWeight_flip`: how transport, reconnection and reflection act on the
  signed weight.
* `TauCeti.BrauerDiagram.signedWeight_permToBrauer` and `TauCeti.BrauerDiagram.signedWeight_capCup`:
  the signed weights of permutation diagrams and cap-cup generators.
* `TauCeti.BrauerDiagram.exists_congr_permToBrauer_one_of_point` and
  `TauCeti.BrauerDiagram.exists_congr_permToBrauer_one_of_val_ne`: existence of transporting
  permutations isolating one or two specified arcs at chosen strand indices.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* W. P. Brown, *The semisimplicity of `ω_f^n`*, Annals of Mathematics 63 (1956), 324-335.
* S. Dipper, S. Doty and J. Hu, *Brauer algebras, symplectic Schur algebras and Schur-Weyl duality*,
  Transactions of the American Mathematical Society 360 (2008), 189-213.
-/

public section

namespace TauCeti

namespace BrauerDiagram

variable {k : ℕ}

/-! ### The canonical arc-ordering permutation -/

/-- The `k`-element `Finset` of `Fin (k + k)` consisting of the lower ends of the arcs of `D`. -/
private def lowerEndFinset (D : BrauerDiagram k) : Finset (Fin (k + k)) :=
  (Finset.univ.filter D.IsLowerEnd).map finSumFinEquiv.toEmbedding

private theorem card_lowerEndFinset (D : BrauerDiagram k) : (lowerEndFinset D).card = k := by
  rw [lowerEndFinset, Finset.card_map, ← Fintype.card_subtype, D.card_isLowerEnd]

/-- Equivalence between `Fin k` and the lower ends of `D`, in increasing order of `Fin (k + k)`. -/
private def lowerEndEquiv (D : BrauerDiagram k) : Fin k ≃ {x // D.IsLowerEnd x} :=
  ((lowerEndFinset D).orderIsoOfFin (card_lowerEndFinset D)).toEquiv.trans
    { toFun := fun y => ⟨finSumFinEquiv.symm y.1, by
        obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp y.2
        simpa [← hxy] using (Finset.mem_filter.mp hx).2⟩
      invFun := fun x => ⟨finSumFinEquiv x.1,
        Finset.mem_map.mpr ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩, rfl⟩⟩
      left_inv := fun y => Subtype.ext (finSumFinEquiv.apply_symm_apply y.1)
      right_inv := fun x => Subtype.ext (finSumFinEquiv.symm_apply_apply x.1) }

/-- **The canonical arc permutation of a Brauer diagram.** It sends `Sum.inl r` to the `r`-th lower
end of `D` (in the order of `Fin (k + k)`) and `Sum.inr r` to its partner
`D.val (D.arcPerm (inl r))`, so transporting `permToBrauer 1` along `D.arcPerm` recovers `D`. -/
def arcPerm (D : BrauerDiagram k) : Equiv.Perm (Fin k ⊕ Fin k) :=
  (Equiv.sumCongr (lowerEndEquiv D) ((lowerEndEquiv D).trans D.notLowerEndEquiv.symm)).trans
    (Equiv.sumCompl D.IsLowerEnd)

private theorem arcPerm_inl (D : BrauerDiagram k) (r : Fin k) :
    D.arcPerm (Sum.inl r) = (lowerEndEquiv D r).1 :=
  (rfl)

@[simp]
theorem arcPerm_inr (D : BrauerDiagram k) (r : Fin k) :
    D.arcPerm (Sum.inr r) = D.val (D.arcPerm (Sum.inl r)) := by
  simp [arcPerm, Equiv.sumCompl_apply_inr, notLowerEndEquiv_symm_apply]

theorem isLowerEnd_arcPerm_inl (D : BrauerDiagram k) (r : Fin k) :
    D.IsLowerEnd (D.arcPerm (Sum.inl r)) :=
  (lowerEndEquiv D r).2

/-- **Transporting the identity diagram along `D.arcPerm` gives `D`.** -/
@[simp]
theorem congr_arcPerm_permToBrauer_one (D : BrauerDiagram k) :
    PerfectMatching.congr D.arcPerm (permToBrauer 1) = D := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  obtain ⟨z, rfl⟩ := D.arcPerm.surjective x
  rw [PerfectMatching.congr_val_apply_apply]
  rcases z with r | r
  · simp [Equiv.Perm.one_def]
  · simp [Equiv.Perm.one_def, D.apply_apply]

/-- The arc permutation of the identity diagram is the identity permutation: its lower ends are the
bottom points `Sum.inl 0, …, Sum.inl (k - 1)` in order, paired with `Sum.inr 0, …, Sum.inr (k - 1)`.
-/
@[simp]
theorem arcPerm_permToBrauer_one : (permToBrauer (1 : Equiv.Perm (Fin k))).arcPerm = 1 := by
  set D : BrauerDiagram k := permToBrauer 1 with hD
  have hmem (r : Fin k) : Fin.castAdd k r ∈ lowerEndFinset D := by
    refine Finset.mem_map.mpr ⟨Sum.inl r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      finSumFinEquiv_apply_left r⟩
    rw [isLowerEnd_def, hD, permToBrauer_val_inl, Equiv.Perm.one_apply,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def]
    simp [r.pos]
  have hemb : (Fin.castAdd k : Fin k → Fin (k + k)) =
      (lowerEndFinset D).orderEmbOfFin (card_lowerEndFinset D) :=
    Finset.orderEmbOfFin_unique (card_lowerEndFinset D) hmem fun _ _ h => h
  have hinl (r : Fin k) : D.arcPerm (Sum.inl r) = Sum.inl r :=
    (congrArg finSumFinEquiv.symm (congrFun hemb.symm r)).trans
      (finSumFinEquiv_symm_apply_castAdd r)
  refine Equiv.ext fun z => ?_
  rcases z with r | r
  · exact hinl r
  · rw [arcPerm_inr, hinl, hD, permToBrauer_val_inl, Equiv.Perm.one_apply, Equiv.Perm.one_apply]

/-! ### The Pfaffian-signed arc weight -/

section SignedWeight

variable {R : Type*} [CommRing R]

/-- **The Pfaffian-signed weight of a Brauer diagram** for a pair weight `W` on the boundary points:
the product of `W` along the `k` arcs oriented from their lower ends, multiplied by the sign of
`D.arcPerm`. When `W` is skew-symmetric, `signedWeight_eq_of_congr_permToBrauer_one` shows that any
permutation transporting `permToBrauer 1` to `D` computes the same value. -/
def signedWeight (D : BrauerDiagram k) (W : (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → R) : R :=
  (Equiv.Perm.sign D.arcPerm : ℤ) • ∏ r : Fin k, W (D.arcPerm (Sum.inl r)) (D.arcPerm (Sum.inr r))

theorem signedWeight_def (D : BrauerDiagram k) (W : (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → R) :
    D.signedWeight W =
      (Equiv.Perm.sign D.arcPerm : ℤ) •
        ∏ r : Fin k, W (D.arcPerm (Sum.inl r)) (D.arcPerm (Sum.inr r)) :=
  (rfl)

/-- The signed weight depends only on the values of `W` on the lower-oriented arcs of `D`. -/
theorem signedWeight_congr_arcs (D : BrauerDiagram k)
    {W W' : (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → R}
    (h : ∀ x, D.IsLowerEnd x → W x (D.val x) = W' x (D.val x)) :
    D.signedWeight W = D.signedWeight W' := by
  rw [signedWeight_def, signedWeight_def]
  refine congrArg _ (Finset.prod_congr rfl fun r _ => ?_)
  rw [arcPerm_inr]
  exact h _ (D.isLowerEnd_arcPerm_inl r)

/-- A ring homomorphism commutes with the signed weight of a Brauer diagram. -/
@[simp]
theorem map_signedWeight {S F : Type*} [CommRing S] [FunLike F R S] [RingHomClass F R S]
    (D : BrauerDiagram k) (f : F) (W : (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → R) :
    f (D.signedWeight W) = D.signedWeight fun x y => f (W x y) := by
  rw [signedWeight_def, signedWeight_def, map_zsmul, map_prod]

/-- The signed weight of the identity diagram is the product of `W (Sum.inl r) (Sum.inr r)` over the
`k` strands, with no skew-symmetry assumption needed. -/
@[simp]
theorem signedWeight_permToBrauer_one (W : (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → R) :
    (permToBrauer (1 : Equiv.Perm (Fin k))).signedWeight W =
      ∏ r : Fin k, W (Sum.inl r) (Sum.inr r) := by
  simp [signedWeight_def]

/-! ### Stabilizer of the identity diagram and transport independence -/

/-- A permutation `δ` that swaps `Sum.inl r` and `Sum.inr r` for `r ∈ S` and fixes both for `r ∉ S`
has sign `(-1) ^ S.card`. -/
private theorem sign_strandFlip (S : Finset (Fin k)) :
    Equiv.Perm.sign
      (Equiv.ofBijective (fun z : Fin k ⊕ Fin k => if Sum.elim id id z ∈ S then z.swap else z)
        (Function.Involutive.bijective fun z => by
          rcases z with r | r <;> by_cases hr : r ∈ S <;> simp [hr])) =
      (-1 : ℤˣ) ^ S.card := by
  set δ : Equiv.Perm (Fin k ⊕ Fin k) :=
    Equiv.ofBijective (fun z : Fin k ⊕ Fin k => if Sum.elim id id z ∈ S then z.swap else z)
      (Function.Involutive.bijective fun z => by
        rcases z with r | r <;> by_cases hr : r ∈ S <;> simp [hr])
  have hδ (z : Fin k ⊕ Fin k) : δ z = if Sum.elim id id z ∈ S then z.swap else z :=
    Equiv.ofBijective_apply _ _ z
  have hsq : δ ^ 2 = 1 := Equiv.ext fun z => by
    rw [sq, Equiv.Perm.mul_apply, hδ, hδ]
    rcases z with r | r <;> by_cases hr : r ∈ S <;> simp [hr]
  -- A boundary point is moved by `δ` iff its strand index lies in `S`, giving `2 * S.card` moved
  -- points in all.
  have hmov : Fintype.card {z : Fin k ⊕ Fin k // ¬z ∈ Function.fixedPoints δ} = 2 * S.card := by
    have hiff (z : Fin k ⊕ Fin k) : ¬z ∈ Function.fixedPoints δ ↔ Sum.elim id id z ∈ S := by
      rw [Function.mem_fixedPoints_iff, hδ]
      rcases z with r | r <;> by_cases hr : r ∈ S <;> simp [hr]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff), Fintype.card_subtype]
    have hsplit : (Finset.univ.filter fun z : Fin k ⊕ Fin k => Sum.elim id id z ∈ S) =
        S.disjSum S := by
      ext z
      rcases z with r | r <;> simp
    rw [hsplit, Finset.card_disjSum, two_mul]
  have hfix : Fintype.card {z // z ∉ Function.fixedPoints δ} =
      Fintype.card (Fin k ⊕ Fin k) - Fintype.card (Function.fixedPoints δ) :=
    Fintype.card_subtype_compl (· ∈ Function.fixedPoints δ)
  rw [Equiv.Perm.sign_of_pow_two_eq_one hsq, ← hfix, hmov, Nat.mul_div_right _ two_pos]

/-- **Stabilizer invariance.** Any permutation `τ` fixing `permToBrauer 1` under transport leaves
the signed product `sign τ • ∏ r, W (τ (inl r)) (τ (inr r))` unchanged when `W` is skew-symmetric:
`τ` decomposes into a strand permutation `sumCongr α α` of sign `1` and a strand-flip involution
whose sign cancels the endpoint-reversal signs of `W`. -/
private theorem exists_strandDecomp_of_congr_permToBrauer_one {τ : Equiv.Perm (Fin k ⊕ Fin k)}
    (hτ : PerfectMatching.congr τ (permToBrauer 1) = permToBrauer 1) :
    ∃ (α : Equiv.Perm (Fin k)) (S : Finset (Fin k)),
      Equiv.Perm.sign τ = (-1 : ℤˣ) ^ S.card ∧
      (∀ r : Fin k, τ (Sum.inl r) = if r ∈ S then Sum.inr (α r) else Sum.inl (α r)) ∧
      ∀ r : Fin k, τ (Sum.inr r) = (τ (Sum.inl r)).swap := by
  have hval_one (z : Fin k ⊕ Fin k) : (permToBrauer (1 : Equiv.Perm (Fin k))).val z = z.swap := by
    rcases z with r | r <;> simp [Equiv.Perm.one_def]
  have hswap (z : Fin k ⊕ Fin k) : τ z.swap = (τ z).swap := by
    have h := PerfectMatching.congr_val_apply_apply τ (permToBrauer 1) z
    rwa [hτ, hval_one, hval_one, eq_comm] at h
  have hinr (r : Fin k) : τ (Sum.inr r) = (τ (Sum.inl r)).swap := hswap (Sum.inl r)
  have hinj : Function.Injective fun r : Fin k => Sum.elim id id (τ (Sum.inl r)) := by
    intro r₁ r₂ h
    have hsame : τ (Sum.inl r₁) = τ (Sum.inl r₂) ∨ τ (Sum.inl r₁) = (τ (Sum.inl r₂)).swap := by
      rcases hx₁ : τ (Sum.inl r₁) with a | a <;> rcases hx₂ : τ (Sum.inl r₂) with b | b <;>
        simp_all only [Sum.elim_inl, Sum.elim_inr, id_eq, Sum.swap_inl, Sum.swap_inr, or_true,
          true_or]
    rcases hsame with heq | heq
    · exact Sum.inl_injective (τ.injective heq)
    · rw [← hswap] at heq
      exact absurd (τ.injective heq) Sum.inl_ne_inr
  let α : Equiv.Perm (Fin k) := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have hα (r : Fin k) : Sum.elim id id (τ (Sum.inl r)) = α r := rfl
  let S : Finset (Fin k) := Finset.univ.filter fun r => (τ (Sum.inl r)).isRight
  have hinl (r : Fin k) : τ (Sum.inl r) = if r ∈ S then Sum.inr (α r) else Sum.inl (α r) := by
    rcases ht : τ (Sum.inl r) with a | a <;>
      { have ha : a = α r := by simpa [ht] using hα r
        simp [S, ht, ha] }
  let δ : Equiv.Perm (Fin k ⊕ Fin k) :=
    Equiv.ofBijective (fun z : Fin k ⊕ Fin k => if Sum.elim id id z ∈ S then z.swap else z)
      (Function.Involutive.bijective fun z => by
        rcases z with r | r <;> by_cases hr : r ∈ S <;> simp [hr])
  have hfact : τ = Equiv.Perm.sumCongr α α * δ := Equiv.ext fun z => by
    have hδ (w : Fin k ⊕ Fin k) : δ w = if Sum.elim id id w ∈ S then w.swap else w :=
      Equiv.ofBijective_apply _ _ w
    rcases z with r | r
    · rw [hinl r, Equiv.Perm.mul_apply, hδ]
      by_cases hr : r ∈ S <;> simp [hr]
    · rw [hinr r, hinl r, Equiv.Perm.mul_apply, hδ]
      by_cases hr : r ∈ S <;> simp [hr]
  refine ⟨α, S, ?_, hinl, hinr⟩
  rw [hfact, map_mul, Equiv.Perm.sign_sumCongr, Int.units_mul_self, one_mul]
  exact sign_strandFlip S

private theorem sign_smul_prod_eq_of_congr_permToBrauer_one
    {W : (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → R} (hW : ∀ x y, W y x = -W x y)
    {τ : Equiv.Perm (Fin k ⊕ Fin k)}
    (hτ : PerfectMatching.congr τ (permToBrauer 1) = permToBrauer 1) :
    (Equiv.Perm.sign τ : ℤ) • ∏ r : Fin k, W (τ (Sum.inl r)) (τ (Sum.inr r)) =
      ∏ r : Fin k, W (Sum.inl r) (Sum.inr r) := by
  obtain ⟨α, S, hsign, hinl, hinr⟩ := exists_strandDecomp_of_congr_permToBrauer_one hτ
  have hterm (r : Fin k) : W (τ (Sum.inl r)) (τ (Sum.inr r)) =
      (if r ∈ S then (-1 : R) else 1) * W (Sum.inl (α r)) (Sum.inr (α r)) := by
    rw [hinr, hinl]
    by_cases hr : r ∈ S <;> simp [hr, hW (Sum.inl (α r)) (Sum.inr (α r))]
  have hSprod : (∏ r : Fin k, if r ∈ S then (-1 : R) else 1) = (-1 : R) ^ S.card := by
    rw [← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]
  have hprod_α : (∏ r : Fin k, W (Sum.inl (α r)) (Sum.inr (α r))) =
      ∏ r : Fin k, W (Sum.inl r) (Sum.inr r) :=
    Equiv.prod_comp α fun r => W (Sum.inl r) (Sum.inr r)
  rw [Finset.prod_congr rfl fun r _ => hterm r, Finset.prod_mul_distrib, hSprod, hprod_α,
    zsmul_eq_mul, hsign, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  push_cast
  rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- **Transport independence of the signed weight.** For any skew-symmetric pair weight `W` and any
permutation `π` transporting `permToBrauer 1` to `D`, the signed weight `D.signedWeight W` equals
`sign π • ∏ r, W (π (inl r)) (π (inr r))`. -/
theorem signedWeight_eq_of_congr_permToBrauer_one
    {W : (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → R} (hW : ∀ x y, W y x = -W x y)
    {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : PerfectMatching.congr π (permToBrauer 1) = D) :
    D.signedWeight W =
      (Equiv.Perm.sign π : ℤ) • ∏ r : Fin k, W (π (Sum.inl r)) (π (Sum.inr r)) := by
  let τ : Equiv.Perm (Fin k ⊕ Fin k) := D.arcPerm⁻¹ * π
  have hτ : PerfectMatching.congr τ (permToBrauer 1) = permToBrauer 1 := by
    calc PerfectMatching.congr τ (permToBrauer 1)
        = PerfectMatching.congr D.arcPerm.symm (PerfectMatching.congr π (permToBrauer 1)) :=
            (PerfectMatching.congr_trans π D.arcPerm.symm (permToBrauer 1)).symm
      _ = PerfectMatching.congr D.arcPerm.symm D := by rw [hπ]
      _ = PerfectMatching.congr D.arcPerm.symm
            (PerfectMatching.congr D.arcPerm (permToBrauer 1)) :=
            congrArg (PerfectMatching.congr D.arcPerm.symm) D.congr_arcPerm_permToBrauer_one.symm
      _ = permToBrauer 1 := by
            rw [PerfectMatching.congr_trans, Equiv.self_trans_symm, PerfectMatching.congr_refl]
  have hW' (x y : Fin k ⊕ Fin k) :
      W (D.arcPerm y) (D.arcPerm x) = -W (D.arcPerm x) (D.arcPerm y) := hW _ _
  have key := sign_smul_prod_eq_of_congr_permToBrauer_one hW' hτ
  have hπ_eq : D.arcPerm * τ = π := mul_inv_cancel_left D.arcPerm π
  have happly (z : Fin k ⊕ Fin k) : D.arcPerm (τ z) = π z := by
    rw [← Equiv.Perm.mul_apply, hπ_eq]
  rw [signedWeight_def, ← key, smul_smul, ← Units.val_mul, ← map_mul, hπ_eq]
  simp only [happly]

/-- **Transporting a Brauer diagram along a permutation `π`** multiplies the pulled-back signed
weight by `sign π`. -/
theorem signedWeight_congr {W : (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → R}
    (hW : ∀ x y, W y x = -W x y) (D : BrauerDiagram k) (π : Equiv.Perm (Fin k ⊕ Fin k)) :
    signedWeight (PerfectMatching.congr π D) W =
      (Equiv.Perm.sign π : ℤ) • D.signedWeight fun x y => W (π x) (π y) := by
  have hcongr : PerfectMatching.congr (π * D.arcPerm) (permToBrauer 1) =
      PerfectMatching.congr π D := by
    -- Group multiplication on `Equiv.Perm` is reverse `Equiv.trans`.
    change PerfectMatching.congr (D.arcPerm.trans π) (permToBrauer 1) = _
    rw [← PerfectMatching.congr_trans, D.congr_arcPerm_permToBrauer_one]
  rw [signedWeight_eq_of_congr_permToBrauer_one hW hcongr, map_mul, Units.val_mul, mul_smul,
    signedWeight_def]
  rfl

/-- **Reconnecting two distinct arcs negates the pulled-back signed weight**: `D.reconnect x y`
transports `D` along the transposition `Equiv.swap (D.val x) y`, which has sign `-1` when
`D.val x ≠ y`. -/
theorem signedWeight_reconnect {W : (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → R}
    (hW : ∀ x y, W y x = -W x y) (D : BrauerDiagram k) {x y : Fin k ⊕ Fin k}
    (h : D.val x ≠ y) :
    signedWeight (D.reconnect x y) W =
      -D.signedWeight fun a b => W (Equiv.swap (D.val x) y a) (Equiv.swap (D.val x) y b) := by
  have hrec : D.reconnect x y = PerfectMatching.congr (Equiv.swap (D.val x) y) D :=
    PerfectMatching.ext fun z => by
      rw [PerfectMatching.reconnect_val, PerfectMatching.congr_val_apply]
      rfl
  rw [hrec, signedWeight_congr hW, Equiv.Perm.sign_swap h]
  simp

/-- **Reflecting a Brauer diagram** multiplies the reflected signed weight by `(-1) ^ k`, the sign
of the fixed-point-free involution `Sum.swap` on the `2 * k` boundary points. -/
theorem signedWeight_flip {W : (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → R}
    (hW : ∀ x y, W y x = -W x y) (D : BrauerDiagram k) :
    D.flip.signedWeight W = (-1 : R) ^ k * D.signedWeight fun x y => W x.swap y.swap := by
  have hflip : D.flip = PerfectMatching.congr (Equiv.sumComm (Fin k) (Fin k)) D :=
    PerfectMatching.ext fun z => by
      rw [flip_val, PerfectMatching.congr_val_apply]
      rfl
  have hpm : IsPerfectMatching (Equiv.sumComm (Fin k) (Fin k)) :=
    isPerfectMatching_iff.mpr ⟨fun x => by cases x <;> rfl, fun x => by cases x <;> simp⟩
  have hsign : Equiv.Perm.sign (Equiv.sumComm (Fin k) (Fin k)) = (-1 : ℤˣ) ^ k := by
    rw [hpm.sign_eq, Fintype.card_sum, Fintype.card_fin]
    congr 1
    omega
  rw [hflip, signedWeight_congr hW, zsmul_eq_mul, hsign, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one]
  push_cast
  rfl

/-- **The signed weight of a permutation diagram `permToBrauer σ`** is `sign σ` times the product of
`W (Sum.inl r) (Sum.inr (σ r))` over the `k` through strands. -/
theorem signedWeight_permToBrauer {W : (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → R}
    (hW : ∀ x y, W y x = -W x y) (σ : Equiv.Perm (Fin k)) :
    (permToBrauer σ).signedWeight W =
      (Equiv.Perm.sign σ : ℤ) • ∏ r : Fin k, W (Sum.inl r) (Sum.inr (σ r)) := by
  have hcongr : PerfectMatching.congr (Equiv.Perm.sumCongr 1 σ) (permToBrauer 1) =
      permToBrauer σ := by
    refine Subtype.ext (Equiv.ext fun x => ?_)
    rcases x with i | j <;> simp [Equiv.Perm.one_def, Equiv.Perm.inv_def]
  rw [signedWeight_eq_of_congr_permToBrauer_one hW hcongr, Equiv.Perm.sign_sumCongr, map_one,
    one_mul]
  rfl

/-- **The signed weight of a cap-cup diagram `capCup a b`** on distinct strands `a ≠ b`: the
transposition `Equiv.swap (Sum.inr a) (Sum.inl b)` that bends `permToBrauer 1` into `capCup a b`
contributes `-1`, the cap contributes `W (inl a) (inl b)`, the cup contributes `W (inr a) (inr b)`,
and the remaining strands go straight through. -/
theorem signedWeight_capCup {W : (Fin k ⊕ Fin k) → (Fin k ⊕ Fin k) → R}
    (hW : ∀ x y, W y x = -W x y) {a b : Fin k} (hab : a ≠ b) :
    (capCup a b).signedWeight W =
      -(W (Sum.inl a) (Sum.inl b) * W (Sum.inr a) (Sum.inr b) *
        ∏ r ∈ (Finset.univ.erase a).erase b, W (Sum.inl r) (Sum.inr r)) := by
  set π : Equiv.Perm (Fin k ⊕ Fin k) := Equiv.swap (Sum.inr a) (Sum.inl b)
  have hcongr : PerfectMatching.congr π (permToBrauer 1) = capCup a b :=
    (eq_capCup_iff hab).mpr
      ⟨by simp [π, Equiv.Perm.one_def,
          Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr (Sum.inl_injective.ne hab)],
       by simp [π, Equiv.Perm.one_def,
          Equiv.swap_apply_of_ne_of_ne (Sum.inr_injective.ne hab.symm) Sum.inr_ne_inl],
       fun i hia hib => by simp [π, Equiv.Perm.one_def,
          Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr (Sum.inl_injective.ne hib),
          Equiv.swap_apply_of_ne_of_ne (Sum.inr_injective.ne hia) Sum.inr_ne_inl]⟩
  rw [signedWeight_eq_of_congr_permToBrauer_one hW hcongr,
    Equiv.Perm.sign_swap Sum.inr_ne_inl, Units.val_neg, Units.val_one, neg_one_smul, neg_inj]
  have ha : a ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ a
  have hb : b ∈ (Finset.univ : Finset (Fin k)).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  rw [← Finset.mul_prod_erase Finset.univ _ ha, ← Finset.mul_prod_erase (Finset.univ.erase a) _ hb,
    ← mul_assoc]
  have hpa : W (π (Sum.inl a)) (π (Sum.inr a)) = W (Sum.inl a) (Sum.inl b) := by
    simp [π, Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr (Sum.inl_injective.ne hab)]
  have hpb : W (π (Sum.inl b)) (π (Sum.inr b)) = W (Sum.inr a) (Sum.inr b) := by
    simp [π, Equiv.swap_apply_of_ne_of_ne (Sum.inr_injective.ne hab.symm) Sum.inr_ne_inl]
  rw [hpa, hpb]
  refine congrArg _ (Finset.prod_congr rfl fun r hr => ?_)
  obtain ⟨hrb, hra⟩ := Finset.mem_erase.mp hr
  have hra' : r ≠ a := (Finset.mem_erase.mp hra).1
  simp [π, Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr (Sum.inl_injective.ne hrb),
    Equiv.swap_apply_of_ne_of_ne (Sum.inr_injective.ne hra') Sum.inr_ne_inl]

end SignedWeight

/-! ### Transporting permutations adapted to one or two chosen arcs -/

/-- Swapping the two ends of a single strand of `permToBrauer 1` leaves `permToBrauer 1` unchanged.
-/
private theorem congr_swap_inl_inr_permToBrauer_one (r : Fin k) :
    PerfectMatching.congr (Equiv.swap (Sum.inl r) (Sum.inr r)) (permToBrauer 1) =
      permToBrauer 1 := by
  refine Subtype.ext (Equiv.ext fun z => ?_)
  rcases z with i | i <;> rcases eq_or_ne i r with rfl | hir
  · simp [Equiv.Perm.one_def]
  · simp [Equiv.swap_apply_of_ne_of_ne, hir]
  · simp [Equiv.Perm.one_def]
  · simp [Equiv.Perm.one_def, Equiv.swap_apply_of_ne_of_ne, hir]

/-- **Isolating one arc in a transporting permutation.** For any boundary point `x`, there is a
strand index `r₀` and a permutation `π` transporting `permToBrauer 1` to `D` that sends `Sum.inl r₀`
to `x` and `Sum.inr r₀` to `D.val x`. -/
theorem exists_congr_permToBrauer_one_of_point (D : BrauerDiagram k) (x : Fin k ⊕ Fin k) :
    ∃ (r₀ : Fin k) (π : Equiv.Perm (Fin k ⊕ Fin k)),
      PerfectMatching.congr π (permToBrauer 1) = D ∧
        π (Sum.inl r₀) = x ∧ π (Sum.inr r₀) = D.val x := by
  rcases hz : D.arcPerm.symm x with r₀ | r₀
  · have hx : D.arcPerm (Sum.inl r₀) = x := D.arcPerm.eq_symm_apply.mp hz.symm
    exact ⟨r₀, D.arcPerm, D.congr_arcPerm_permToBrauer_one, hx, by rw [arcPerm_inr, hx]⟩
  · have hx : D.arcPerm (Sum.inr r₀) = x := D.arcPerm.eq_symm_apply.mp hz.symm
    refine ⟨r₀, D.arcPerm * Equiv.swap (Sum.inl r₀) (Sum.inr r₀), ?_, ?_, ?_⟩
    · -- Group multiplication on `Equiv.Perm` is reverse `Equiv.trans`.
      change PerfectMatching.congr ((Equiv.swap (Sum.inl r₀) (Sum.inr r₀)).trans D.arcPerm)
        (permToBrauer 1) = D
      rw [← PerfectMatching.congr_trans, congr_swap_inl_inr_permToBrauer_one,
        D.congr_arcPerm_permToBrauer_one]
    · simp [hx]
    · simp [← hx, D.apply_apply]

/-- **Isolating two distinct arcs in a transporting permutation.** When `x ≠ y` and `D.val x ≠ y`,
the arcs of `D` at `x` and at `y` are distinct, so some permutation `π` transporting
`permToBrauer 1` to `D` places them at two distinct strand indices `r₁ ≠ r₂` oriented from `x` and
from `y`. -/
theorem exists_congr_permToBrauer_one_of_val_ne (D : BrauerDiagram k) {x y : Fin k ⊕ Fin k}
    (hxy : x ≠ y) (hval : D.val x ≠ y) :
    ∃ (r₁ r₂ : Fin k) (π : Equiv.Perm (Fin k ⊕ Fin k)),
      r₁ ≠ r₂ ∧ PerfectMatching.congr π (permToBrauer 1) = D ∧
        π (Sum.inl r₁) = x ∧ π (Sum.inr r₁) = D.val x ∧
        π (Sum.inl r₂) = y ∧ π (Sum.inr r₂) = D.val y := by
  obtain ⟨r₁, π₁, hD₁, hx₁, hx₁'⟩ := exists_congr_permToBrauer_one_of_point D x
  rcases hz : π₁.symm y with r₂ | r₂
  · have hy : π₁ (Sum.inl r₂) = y := π₁.eq_symm_apply.mp hz.symm
    have hr : r₁ ≠ r₂ := fun h => hxy (by rw [← hx₁, h, hy])
    have hy' : π₁ (Sum.inr r₂) = D.val y := by
      have hc := PerfectMatching.congr_val_apply_apply π₁ (permToBrauer 1) (Sum.inl r₂)
      rwa [hD₁, hy, permToBrauer_val_inl, Equiv.Perm.one_apply, eq_comm] at hc
    exact ⟨r₁, r₂, π₁, hr, hD₁, hx₁, hx₁', hy, hy'⟩
  · have hy : π₁ (Sum.inr r₂) = y := π₁.eq_symm_apply.mp hz.symm
    have hr : r₁ ≠ r₂ := fun h => hval (by rw [← hx₁', h, hy])
    have hy' : π₁ (Sum.inl r₂) = D.val y := by
      have hc := PerfectMatching.congr_val_apply_apply π₁ (permToBrauer 1) (Sum.inr r₂)
      rwa [hD₁, hy, permToBrauer_val_inr, Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_apply,
        eq_comm] at hc
    refine ⟨r₁, r₂, π₁ * Equiv.swap (Sum.inl r₂) (Sum.inr r₂), hr, ?_, ?_, ?_, ?_, ?_⟩
    · -- Group multiplication on `Equiv.Perm` is reverse `Equiv.trans`.
      change PerfectMatching.congr ((Equiv.swap (Sum.inl r₂) (Sum.inr r₂)).trans π₁)
        (permToBrauer 1) = D
      rw [← PerfectMatching.congr_trans, congr_swap_inl_inr_permToBrauer_one, hD₁]
    · simp [Equiv.swap_apply_of_ne_of_ne (Sum.inl_injective.ne hr) Sum.inl_ne_inr, hx₁]
    · simp [Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (Sum.inr_injective.ne hr), hx₁']
    · simp [hy]
    · simp [hy']

end BrauerDiagram

end TauCeti
