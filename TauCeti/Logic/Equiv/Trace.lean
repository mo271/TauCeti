/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Finite feedback trace of a bijection on a sum type

Given a bijection `e : α ⊕ γ ≃ β ⊕ γ` over a finite feedback type `γ`, iterating `e` from each
input `Sum.inl a` steps injectively through `γ` and therefore exits into `β` after at most
`Fintype.card γ` intermediate visits. Meanwhile, the elements of `γ` never visited along any open
path from `α` to `β` carry a restricted permutation whose cycles represent closed feedback loops
entirely inside `γ`.

This construction realizes the canonical trace on the symmetric monoidal category of finite sets
and bijections together with its closed-loop remainder. Taking `[Fintype γ]` supplies the explicit
step bound `Fintype.card γ`, keeping `Equiv.trace`, `Equiv.tracePerm`, and the finiteness and
decidability instances on `Equiv.TraceLoop` computable without requiring `DecidableEq` on `α`, `β`,
or `γ` for `Equiv.trace` itself.

## Main definitions

* `Equiv.TraceStep e x n y`: inductive witness that `e` carries `x : α ⊕ γ` to `y : β ⊕ γ`
  across `n` intermediate elements of `γ`.
* `Equiv.trace e : α ≃ β`: the traced bijection sending `a : α` to the unique `b : β` reached by
  iterating `e` across `γ`.
* `Equiv.IsOpenSeam e`, `Equiv.IsClosedSeam e`, `Equiv.TraceClosed e`: the partition of `γ` into
  elements lying on open traced paths between `α` and `β` and elements lying on closed feedback
  cycles inside `γ`.
* `Equiv.tracePerm e : Perm e.TraceClosed` and `Equiv.TraceLoop e`: the restricted permutation on
  closed feedback elements and its `Equiv.Perm.SameCycle` quotient of closed loops.
* `Equiv.traceLoopCongr`, `Equiv.traceLoopParallelEquiv`, `Equiv.traceLoopSumAssocEquiv`:
  invariance under equivalence, additivity under parallel disjoint sums, and sequential
  decomposition (Bekić's lemma / vanishing II) for closed feedback loops.

## References

* A. Joyal, R. Street, D. Verity, *Traced monoidal categories*, Math. Proc. Cambridge Philos. Soc.
  **119** (1996), 447–468, §2.
-/

public section

namespace Equiv

section TraceStep

variable {α β γ : Type*}

/-- `e.TraceStep x n y` witnesses that starting at `x : α ⊕ γ`, `e` steps through `n` intermediate
elements of `γ` and reaches `y : β ⊕ γ` on the `(n + 1)`-st application of `e`. -/
inductive TraceStep (e : α ⊕ γ ≃ β ⊕ γ) : α ⊕ γ → ℕ → β ⊕ γ → Prop
  | zero (x : α ⊕ γ) : TraceStep e x 0 (e x)
  | succ {x : α ⊕ γ} {c : γ} {n : ℕ} {y : β ⊕ γ} :
      e x = .inr c → TraceStep e (.inr c) n y → TraceStep e x (n + 1) y

/-- Zero intermediate feedback steps correspond to a single application of `e`. -/
@[simp]
theorem traceStep_zero_iff {e : α ⊕ γ ≃ β ⊕ γ} {x : α ⊕ γ} {y : β ⊕ γ} :
    e.TraceStep x 0 y ↔ e x = y :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .zero x⟩

/-- `n + 1` intermediate feedback steps factor through an initial visit `e x = Sum.inr c`. -/
@[simp]
theorem traceStep_succ_iff {e : α ⊕ γ ≃ β ⊕ γ} {x : α ⊕ γ} {n : ℕ} {y : β ⊕ γ} :
    e.TraceStep x (n + 1) y ↔ ∃ c : γ, e x = .inr c ∧ e.TraceStep (.inr c) n y :=
  ⟨fun h => by cases h with | succ hx h' => exact ⟨_, hx, h'⟩,
    fun ⟨_, hx, h'⟩ => .succ hx h'⟩

/-- Appending one more step across an element `c : γ` at the end of a `TraceStep` chain. -/
theorem TraceStep.snoc {e : α ⊕ γ ≃ β ⊕ γ} {x : α ⊕ γ} {n : ℕ} {c : γ}
    (h : e.TraceStep x n (.inr c)) : e.TraceStep x (n + 1) (e (.inr c)) := by
  induction n generalizing x with
  | zero => exact .succ (traceStep_zero_iff.mp h) (.zero _)
  | succ n ih =>
    obtain ⟨c₀, hx, h'⟩ := traceStep_succ_iff.mp h
    exact .succ hx (ih h')

/-- Concatenating two `TraceStep` chains meeting at `Sum.inr c`. -/
theorem TraceStep.append {e : α ⊕ γ ≃ β ⊕ γ} {x : α ⊕ γ} {m n : ℕ} {c : γ} {y : β ⊕ γ}
    (h₁ : e.TraceStep x m (.inr c)) (h₂ : e.TraceStep (.inr c) n y) :
    e.TraceStep x (m + 1 + n) y := by
  induction m generalizing x with
  | zero =>
    exact (by omega : n + 1 = 0 + 1 + n) ▸ TraceStep.succ (traceStep_zero_iff.mp h₁) h₂
  | succ m ih =>
    obtain ⟨c₀, hx, h₁'⟩ := traceStep_succ_iff.mp h₁
    exact (by omega : (m + 1 + n) + 1 = (m + 1) + 1 + n) ▸ TraceStep.succ hx (ih h₁')

/-- Reversing a `TraceStep` chain along `e.symm`. -/
theorem TraceStep.symm {e : α ⊕ γ ≃ β ⊕ γ} {x : α ⊕ γ} {n : ℕ} {y : β ⊕ γ}
    (h : e.TraceStep x n y) : e.symm.TraceStep y n x := by
  induction h with
  | zero x => simp
  | @succ x c _ _ hx _ ih => exact (e.symm_apply_eq.mpr hx.symm) ▸ ih.snoc

/-- `TraceStep` for `e.symm` is symmetric to `TraceStep` for `e`. -/
@[simp]
theorem traceStep_symm_iff {e : α ⊕ γ ≃ β ⊕ γ} {x : α ⊕ γ} {n : ℕ} {y : β ⊕ γ} :
    e.symm.TraceStep y n x ↔ e.TraceStep x n y :=
  ⟨fun h => by simpa using h.symm, TraceStep.symm⟩

/-- `TraceStep` is deterministic at any fixed step count `n`. -/
theorem TraceStep.eq_of_eq_len {e : α ⊕ γ ≃ β ⊕ γ} {x : α ⊕ γ} {n : ℕ} {y₁ y₂ : β ⊕ γ}
    (h₁ : e.TraceStep x n y₁) (h₂ : e.TraceStep x n y₂) : y₁ = y₂ := by
  induction n generalizing x with
  | zero => exact (traceStep_zero_iff.mp h₁).symm.trans (traceStep_zero_iff.mp h₂)
  | succ n ih =>
    obtain ⟨c₁, hx₁, h₁'⟩ := traceStep_succ_iff.mp h₁
    obtain ⟨c₂, hx₂, h₂'⟩ := traceStep_succ_iff.mp h₂
    cases Sum.inr.inj (hx₁.symm.trans hx₂)
    exact ih h₁' h₂'

/-- Exiting into `Sum.inl` determines both the step count and the exit value uniquely. -/
theorem TraceStep.inl_unique {e : α ⊕ γ ≃ β ⊕ γ} {x : α ⊕ γ} {m n : ℕ} {b₁ b₂ : β}
    (h₁ : e.TraceStep x m (.inl b₁)) (h₂ : e.TraceStep x n (.inl b₂)) : m = n ∧ b₁ = b₂ := by
  induction m generalizing x n with
  | zero =>
    rw [traceStep_zero_iff] at h₁
    cases n with
    | zero => exact ⟨rfl, Sum.inl.inj (h₁.symm.trans (traceStep_zero_iff.mp h₂))⟩
    | succ n =>
      obtain ⟨_, hx₂, _⟩ := traceStep_succ_iff.mp h₂
      cases h₁.symm.trans hx₂
  | succ m ih =>
    obtain ⟨c₁, hx₁, h₁'⟩ := traceStep_succ_iff.mp h₁
    cases n with
    | zero => cases hx₁.symm.trans (traceStep_zero_iff.mp h₂)
    | succ n =>
      obtain ⟨c₂, hx₂, h₂'⟩ := traceStep_succ_iff.mp h₂
      cases Sum.inr.inj (hx₁.symm.trans hx₂)
      obtain ⟨rfl, rfl⟩ := ih h₁' h₂'
      exact ⟨rfl, rfl⟩

/-- Any intermediate `Sum.inr c` along a chain exiting at `Sum.inl b` occurs strictly earlier and
initiates the remaining suffix chain to `Sum.inl b`. -/
theorem TraceStep.lt_and_drop_of_inl {e : α ⊕ γ ≃ β ⊕ γ} {x : α ⊕ γ} {N n : ℕ} {b : β} {c : γ}
    (h₁ : e.TraceStep x N (.inl b)) (h₂ : e.TraceStep x n (.inr c)) :
    n < N ∧ e.TraceStep (.inr c) (N - 1 - n) (.inl b) := by
  induction n generalizing x N with
  | zero =>
    rw [traceStep_zero_iff] at h₂
    cases N with
    | zero => cases h₂.symm.trans (traceStep_zero_iff.mp h₁)
    | succ N =>
      obtain ⟨c', hx₁, h₁'⟩ := traceStep_succ_iff.mp h₁
      cases Sum.inr.inj (h₂.symm.trans hx₁)
      exact ⟨Nat.succ_pos _, by simpa using h₁'⟩
  | succ n ih =>
    obtain ⟨c₀, hx₂, h₂'⟩ := traceStep_succ_iff.mp h₂
    cases N with
    | zero => cases hx₂.symm.trans (traceStep_zero_iff.mp h₁)
    | succ N =>
      obtain ⟨c₀', hx₁, h₁'⟩ := traceStep_succ_iff.mp h₁
      cases Sum.inr.inj (hx₂.symm.trans hx₁)
      obtain ⟨hlt, hdrop⟩ := ih h₁' h₂'
      exact ⟨Nat.succ_lt_succ hlt, (by omega : N - 1 - n = N + 1 - 1 - (n + 1)) ▸ hdrop⟩

/-- Every strictly earlier index `k < N` along a `TraceStep` chain visits an element of `γ`. -/
theorem TraceStep.prefix_inr {e : α ⊕ γ ≃ β ⊕ γ} {x : α ⊕ γ} {N : ℕ} {y : β ⊕ γ}
    (h : e.TraceStep x N y) {k : ℕ} (hk : k < N) : ∃ c : γ, e.TraceStep x k (.inr c) := by
  induction k generalizing x N with
  | zero =>
    cases N with
    | zero => exact absurd hk (Nat.not_lt_zero _)
    | succ N =>
      obtain ⟨c, hx, _⟩ := traceStep_succ_iff.mp h
      exact ⟨c, traceStep_zero_iff.mpr hx⟩
  | succ k ih =>
    cases N with
    | zero => exact absurd hk (Nat.not_lt_zero _)
    | succ N =>
      obtain ⟨c, hx, h'⟩ := traceStep_succ_iff.mp h
      obtain ⟨c', hc'⟩ := ih h' (Nat.lt_of_succ_lt_succ hk)
      exact ⟨c', .succ hx hc'⟩

/-- Computable bounded walker that iterates `e` while the current point stays in `γ`, halting as
soon as it exits into `β`. -/
def traceWalk (e : α ⊕ γ ≃ β ⊕ γ) : ℕ → α ⊕ γ → β ⊕ γ
  | 0, x => e x
  | n + 1, x =>
    match e x with
    | .inl b => .inl b
    | .inr c => e.traceWalk n (.inr c)

private theorem traceStep_of_traceWalk_eq_inr {e : α ⊕ γ ≃ β ⊕ γ} {N : ℕ} {x : α ⊕ γ} {d : γ}
    (h : e.traceWalk N x = .inr d) : e.TraceStep x N (.inr d) := by
  induction N generalizing x with
  | zero => exact traceStep_zero_iff.mpr h
  | succ N ih =>
    simp only [traceWalk] at h
    split at h
    · cases h
    · rename_i c hx
      exact .succ hx (ih h)

private theorem exists_traceStep_of_traceWalk_eq_inl {e : α ⊕ γ ≃ β ⊕ γ} {N : ℕ} {x : α ⊕ γ}
    {b : β} (h : e.traceWalk N x = .inl b) : ∃ n ≤ N, e.TraceStep x n (.inl b) := by
  induction N generalizing x with
  | zero => exact ⟨0, le_rfl, traceStep_zero_iff.mpr h⟩
  | succ N ih =>
    simp only [traceWalk] at h
    split at h
    · rename_i b' hx
      cases Sum.inl.inj h
      exact ⟨0, Nat.zero_le _, traceStep_zero_iff.mpr hx⟩
    · rename_i c hx
      obtain ⟨n, hn, hstep⟩ := ih h
      exact ⟨n + 1, Nat.succ_le_succ hn, .succ hx hstep⟩

private theorem TraceStep.traceWalk_eq_inl {e : α ⊕ γ ≃ β ⊕ γ} {x : α ⊕ γ} {n : ℕ} {b : β}
    (h : e.TraceStep x n (.inl b)) {N : ℕ} (hn : n ≤ N) : e.traceWalk N x = .inl b := by
  induction n generalizing x N with
  | zero =>
    rw [traceStep_zero_iff] at h
    cases N with
    | zero => exact h
    | succ N => simp [traceWalk, h]
  | succ n ih =>
    obtain ⟨c, hx, h'⟩ := traceStep_succ_iff.mp h
    cases N with
    | zero => exact absurd hn (Nat.not_succ_le_zero _)
    | succ N => simp [traceWalk, hx, ih h' (Nat.le_of_succ_le_succ hn)]

/-- An element `c : γ` lies on an open traced path when iterating `e` from `Sum.inr c` eventually
exits into `β`. -/
@[expose]
def IsOpenSeam (e : α ⊕ γ ≃ β ⊕ γ) (c : γ) : Prop :=
  ∃ b n, e.TraceStep (.inr c) n (.inl b)

/-- An element `c : γ` lies on a closed feedback loop when iterating `e` from `Sum.inr c` never
exits into `β`. -/
@[expose]
def IsClosedSeam (e : α ⊕ γ ≃ β ⊕ γ) (c : γ) : Prop :=
  ¬ e.IsOpenSeam c

private theorem isClosedSeam_of_apply_eq_inr {e : α ⊕ γ ≃ β ⊕ γ} {c c' : γ}
    (hc : e.IsClosedSeam c) (he : e (.inr c) = .inr c') : e.IsClosedSeam c' :=
  fun ⟨b, n, hn⟩ => hc ⟨b, n + 1, .succ he hn⟩

/-- The subtype of `γ` consisting of elements on closed feedback cycles (never exiting into `β`). -/
abbrev TraceClosed (e : α ⊕ γ ≃ β ⊕ γ) : Type _ :=
  {c : γ // e.IsClosedSeam c}

end TraceStep

section FiniteTrace

variable {α β γ : Type*} [Fintype γ]

/-- A chain starting at `Sum.inl a` cannot remain inside `γ` for `Fintype.card γ + 1` steps,
because the visited elements of `γ` are pairwise distinct. -/
theorem not_traceStep_inl_inr_card (e : α ⊕ γ ≃ β ⊕ γ) (a : α) (d : γ) :
    ¬ e.TraceStep (.inl a) (Fintype.card γ) (.inr d) := by
  intro h
  classical
  let g : Fin (Fintype.card γ + 1) → γ := fun i =>
    if hi : i.1 < Fintype.card γ then (h.prefix_inr hi).choose else d
  have hg : ∀ i : Fin (Fintype.card γ + 1), e.TraceStep (.inl a) i.1 (.inr (g i)) := by
    intro i
    by_cases hi : i.1 < Fintype.card γ
    · simpa [g, hi] using (h.prefix_inr hi).choose_spec
    · have heq : i.1 = Fintype.card γ :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp i.2) (Nat.not_lt.mp hi)
      simpa [g, hi, heq] using h
  have hinj : Function.Injective g := fun i j hij =>
    Fin.ext ((hg i).symm.inl_unique (hij ▸ (hg j).symm)).1
  have hcard := Fintype.card_le_of_injective g hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- Any chain starting inside `γ` and exiting into `β` takes fewer than `Fintype.card γ`
additional steps inside `γ`. -/
theorem TraceStep.lt_card_of_inr_inl {e : α ⊕ γ ≃ β ⊕ γ} {c : γ} {n : ℕ} {b : β}
    (h : e.TraceStep (.inr c) n (.inl b)) : n < Fintype.card γ := by
  by_contra hge
  rcases eq_or_lt_of_le (Nat.not_lt.mp hge) with rfl | hlt
  · exact e.symm.not_traceStep_inl_inr_card b c h.symm
  · obtain ⟨d, hd⟩ := h.symm.prefix_inr hlt
    exact e.symm.not_traceStep_inl_inr_card b d hd

private def traceFun (e : α ⊕ γ ≃ β ⊕ γ) (a : α) : β :=
  match h : e.traceWalk (Fintype.card γ) (.inl a) with
  | .inl b => b
  | .inr d => (e.not_traceStep_inl_inr_card a d (traceStep_of_traceWalk_eq_inr h)).elim

private theorem traceStep_traceFun (e : α ⊕ γ ≃ β ⊕ γ) (a : α) :
    ∃ n ≤ Fintype.card γ, e.TraceStep (.inl a) n (.inl (traceFun e a)) := by
  unfold traceFun
  split
  · rename_i b h
    exact exists_traceStep_of_traceWalk_eq_inl h
  · rename_i d h
    exact (e.not_traceStep_inl_inr_card a d (traceStep_of_traceWalk_eq_inr h)).elim

/-- **Finite feedback trace** of a bijection `e : α ⊕ γ ≃ β ⊕ γ`: sends each `a : α` to the unique
`b : β` reached by iterating `e` through `γ`. -/
def trace (e : α ⊕ γ ≃ β ⊕ γ) : α ≃ β where
  toFun := traceFun e
  invFun := traceFun e.symm
  left_inv a := by
    obtain ⟨_, _, h₁⟩ := traceStep_traceFun e a
    obtain ⟨_, _, h₂⟩ := traceStep_traceFun e.symm (traceFun e a)
    exact (h₁.symm.inl_unique h₂).2.symm
  right_inv b := by
    obtain ⟨_, _, h₁⟩ := traceStep_traceFun e.symm b
    obtain ⟨_, _, h₂⟩ := traceStep_traceFun e (traceFun e.symm b)
    exact (h₁.symm.inl_unique h₂).2.symm

/-- `e.trace a = b` if and only if iterating `e` from `Sum.inl a` reaches `Sum.inl b` across
finitely many steps in `γ`. -/
theorem trace_apply_eq_iff (e : α ⊕ γ ≃ β ⊕ γ) {a : α} {b : β} :
    e.trace a = b ↔ ∃ n, e.TraceStep (.inl a) n (.inl b) := by
  refine ⟨?_, fun ⟨_, h⟩ => ?_⟩
  · rintro rfl
    obtain ⟨n, _, h⟩ := traceStep_traceFun e a
    exact ⟨n, h⟩
  · obtain ⟨_, _, hm⟩ := traceStep_traceFun e a
    exact (hm.inl_unique h).2

/-- Tracing `e.symm` produces `(e.trace).symm`. -/
@[simp]
theorem trace_symm (e : α ⊕ γ ≃ β ⊕ γ) : e.symm.trace = e.trace.symm := (rfl)

/-- If `e (Sum.inl a) = Sum.inl b` directly without entering `γ`, then `e.trace a = b`. -/
@[simp]
theorem trace_apply_of_inl (e : α ⊕ γ ≃ β ⊕ γ) {a : α} {b : β} (h : e (.inl a) = .inl b) :
    e.trace a = b :=
  e.trace_apply_eq_iff.mpr ⟨0, traceStep_zero_iff.mpr h⟩

/-- If `e` sends `Sum.inl a` to `Sum.inr c` and `Sum.inr c` to `Sum.inl b`, then `e.trace a = b`. -/
theorem trace_apply_of_inr (e : α ⊕ γ ≃ β ⊕ γ) {a : α} {c : γ} {b : β}
    (ha : e (.inl a) = .inr c) (hc : e (.inr c) = .inl b) : e.trace a = b :=
  e.trace_apply_eq_iff.mpr ⟨1, .succ ha (traceStep_zero_iff.mpr hc)⟩

/-- `e.IsOpenSeam c` holds if and only if `e.traceWalk (Fintype.card γ) (.inr c)` exits into `β`. -/
theorem isOpenSeam_iff_traceWalk_inl (e : α ⊕ γ ≃ β ⊕ γ) (c : γ) :
    e.IsOpenSeam c ↔ ∃ b, e.traceWalk (Fintype.card γ) (.inr c) = .inl b :=
  ⟨fun ⟨b, _, h⟩ => ⟨b, h.traceWalk_eq_inl (Nat.le_of_lt h.lt_card_of_inr_inl)⟩,
    fun ⟨b, h⟩ => let ⟨n, _, hstep⟩ := exists_traceStep_of_traceWalk_eq_inl h; ⟨b, n, hstep⟩⟩

/-- Decidability of whether a feedback element lies on an open traced path. -/
instance instDecidablePredIsOpenSeam (e : α ⊕ γ ≃ β ⊕ γ) : DecidablePred e.IsOpenSeam := fun c =>
  match h : e.traceWalk (Fintype.card γ) (.inr c) with
  | .inl b => isTrue ((e.isOpenSeam_iff_traceWalk_inl c).mpr ⟨b, h⟩)
  | .inr _ => isFalse fun hop => by
      obtain ⟨b, hb⟩ := (e.isOpenSeam_iff_traceWalk_inl c).mp hop
      cases h.symm.trans hb

/-- Decidability of whether a feedback element lies on a closed feedback cycle. -/
instance instDecidablePredIsClosedSeam (e : α ⊕ γ ≃ β ⊕ γ) : DecidablePred e.IsClosedSeam :=
  fun c => inferInstanceAs (Decidable (¬ e.IsOpenSeam c))

omit [Fintype γ] in
/-- An element of a finite feedback type `γ` exits into `β` forward if and only if it is entered
from `α` backward. -/
theorem isOpenSeam_iff_exists_inl [Finite γ] (e : α ⊕ γ ≃ β ⊕ γ) (c : γ) :
    e.IsOpenSeam c ↔ ∃ a n, e.TraceStep (.inl a) n (.inr c) := by
  cases nonempty_fintype γ
  refine ⟨fun ⟨b, m, hm⟩ => ?_, fun ⟨a, n, hn⟩ => ?_⟩
  · obtain ⟨M, hM⟩ := e.symm.trace_apply_eq_iff.mp (rfl : e.symm.trace b = e.symm.trace b)
    exact ⟨e.symm.trace b, M - 1 - m, (hM.lt_and_drop_of_inl hm.symm).2.symm⟩
  · obtain ⟨N, hN⟩ := e.trace_apply_eq_iff.mp (rfl : e.trace a = e.trace a)
    exact ⟨e.trace a, N - 1 - n, (hN.lt_and_drop_of_inl hn).2⟩

omit [Fintype γ] in
/-- Open feedback elements are the same for `e` and `e.symm`. -/
@[simp]
theorem isOpenSeam_symm_iff [Finite γ] (e : α ⊕ γ ≃ β ⊕ γ) (c : γ) :
    e.symm.IsOpenSeam c ↔ e.IsOpenSeam c := by
  rw [e.isOpenSeam_iff_exists_inl]
  simp only [IsOpenSeam, traceStep_symm_iff]

omit [Fintype γ] in
/-- Closed feedback elements are the same for `e` and `e.symm`. -/
@[simp]
theorem isClosedSeam_symm_iff [Finite γ] (e : α ⊕ γ ≃ β ⊕ γ) (c : γ) :
    e.symm.IsClosedSeam c ↔ e.IsClosedSeam c :=
  not_congr (e.isOpenSeam_symm_iff c)

omit [Fintype γ] in
private def traceClosedNext (e : α ⊕ γ ≃ β ⊕ γ) (c : e.TraceClosed) : e.TraceClosed :=
  match h : e (.inr c.1) with
  | .inl b => (c.2 ⟨b, 0, traceStep_zero_iff.mpr h⟩).elim
  | .inr c' => ⟨c', isClosedSeam_of_apply_eq_inr c.2 h⟩

omit [Fintype γ] in
private theorem inr_traceClosedNext (e : α ⊕ γ ≃ β ⊕ γ) (c : e.TraceClosed) :
    (.inr (traceClosedNext e c).1 : β ⊕ γ) = e (.inr c.1) := by
  unfold traceClosedNext
  split
  · rename_i b h
    exact (c.2 ⟨b, 0, traceStep_zero_iff.mpr h⟩).elim
  · rename_i c' h
    exact h.symm

/-- The permutation induced by `e` on its closed feedback subtype `e.TraceClosed`. -/
def tracePerm (e : α ⊕ γ ≃ β ⊕ γ) : Perm e.TraceClosed where
  toFun := traceClosedNext e
  invFun c := ⟨(traceClosedNext e.symm ⟨c.1, (e.isClosedSeam_symm_iff c.1).mpr c.2⟩).1,
    (e.isClosedSeam_symm_iff _).mp
      (traceClosedNext e.symm ⟨c.1, (e.isClosedSeam_symm_iff c.1).mpr c.2⟩).2⟩
  left_inv c := by
    apply Subtype.ext
    apply (Sum.inr_injective (α := α))
    simp only [inr_traceClosedNext, symm_apply_apply]
  right_inv c := by
    apply Subtype.ext
    apply (Sum.inr_injective (α := β))
    simp only [inr_traceClosedNext, apply_symm_apply]

/-- Applying `e.tracePerm` agrees with applying `e` inside the `Sum.inr` summand. -/
@[simp]
theorem inr_val_tracePerm_apply (e : α ⊕ γ ≃ β ⊕ γ) (c : e.TraceClosed) :
    (.inr (e.tracePerm c).1 : β ⊕ γ) = e (.inr c.1) :=
  inr_traceClosedNext e c

/-- Applying `e.tracePerm.symm` agrees with applying `e.symm` inside the `Sum.inr` summand. -/
@[simp]
theorem inr_val_tracePerm_symm_apply (e : α ⊕ γ ≃ β ⊕ γ) (c : e.TraceClosed) :
    (.inr (e.tracePerm.symm c).1 : α ⊕ γ) = e.symm (.inr c.1) :=
  inr_traceClosedNext e.symm ⟨c.1, (e.isClosedSeam_symm_iff c.1).mpr c.2⟩

/-- **Closed feedback loops** of a bijection `e : α ⊕ γ ≃ β ⊕ γ`: the orbits of `e.tracePerm` on
closed elements of `γ`. -/
abbrev TraceLoop (e : α ⊕ γ ≃ β ⊕ γ) : Type _ :=
  Quotient (Perm.SameCycle.setoid e.tracePerm)

/-- Quotient projection from closed feedback elements to closed feedback loops. -/
def traceLoopMk (e : α ⊕ γ ≃ β ⊕ γ) (c : e.TraceClosed) : e.TraceLoop :=
  Quotient.mk (Perm.SameCycle.setoid e.tracePerm) c

/-- Two closed feedback elements represent the same loop iff they lie in the same cycle of
`e.tracePerm`. -/
@[simp]
theorem traceLoopMk_eq_iff (e : α ⊕ γ ≃ β ⊕ γ) {c₁ c₂ : e.TraceClosed} :
    e.traceLoopMk c₁ = e.traceLoopMk c₂ ↔ e.tracePerm.SameCycle c₁ c₂ :=
  Quotient.eq

/-- Advancing one step along `e.tracePerm` preserves the closed feedback loop. -/
@[simp]
theorem traceLoopMk_tracePerm (e : α ⊕ γ ≃ β ⊕ γ) (c : e.TraceClosed) :
    e.traceLoopMk (e.tracePerm c) = e.traceLoopMk c :=
  (e.traceLoopMk_eq_iff).mpr (e.tracePerm.sameCycle_apply_left.mpr Perm.SameCycle.rfl)

/-- Finite enumeration of closed feedback loops when equality on `γ` is decidable. -/
instance instFintypeTraceLoop (e : α ⊕ γ ≃ β ⊕ γ) [DecidableEq γ] : Fintype e.TraceLoop :=
  letI : DecidableRel (Perm.SameCycle.setoid e.tracePerm).r :=
    Perm.instDecidableRelSameCycle e.tracePerm
  Quotient.fintype (Perm.SameCycle.setoid e.tracePerm)

/-- Decidable equality on closed feedback loops when equality on `γ` is decidable. -/
instance instDecidableEqTraceLoop (e : α ⊕ γ ≃ β ⊕ γ) [DecidableEq γ] : DecidableEq e.TraceLoop :=
  letI : DecidableRel (Perm.SameCycle.setoid e.tracePerm).r :=
    Perm.instDecidableRelSameCycle e.tracePerm
  @Quotient.decidableEq _ (Perm.SameCycle.setoid e.tracePerm) this

/-- Over an empty feedback type, `Equiv.trace` reduces to stripping the empty right summands. -/
theorem trace_of_isEmpty (e : α ⊕ γ ≃ β ⊕ γ) [IsEmpty γ] :
    e.trace = (Equiv.sumEmpty α γ).symm.trans (e.trans (Equiv.sumEmpty β γ)) := by
  ext a
  rcases h : e (.inl a) with b | c
  · simp [e.trace_apply_of_inl h, h]
  · exact isEmptyElim c

/-- An empty feedback type has no closed feedback loops. -/
instance instIsEmptyTraceLoopOfIsEmpty (e : α ⊕ γ ≃ β ⊕ γ) [IsEmpty γ] : IsEmpty e.TraceLoop :=
  ⟨Quotient.ind fun c => isEmptyElim c.1⟩

/-- If every feedback element lies on an open traced path, no closed feedback loops are formed. -/
theorem isEmpty_traceLoop_of_forall_isOpenSeam (e : α ⊕ γ ≃ β ⊕ γ)
    (h : ∀ c : γ, e.IsOpenSeam c) : IsEmpty e.TraceLoop :=
  ⟨Quotient.ind fun c => c.2 (h c.1)⟩

/-- If `c₀` is a closed feedback element whose `e.tracePerm`-cycle exhausts `e.TraceClosed`, then
`e.TraceLoop` has a unique element `e.traceLoopMk c₀`. -/
@[reducible]
def uniqueTraceLoopOfSameCycle (e : α ⊕ γ ≃ β ⊕ γ) (c₀ : e.TraceClosed)
    (h : ∀ c : e.TraceClosed, e.tracePerm.SameCycle c₀ c) : Unique e.TraceLoop where
  default := e.traceLoopMk c₀
  uniq := Quotient.ind fun c => (e.traceLoopMk_eq_iff.mpr (h c)).symm

end FiniteTrace

section Congruence

variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*}

/-- Transporting a `TraceStep` chain along componentwise equivalences intertwining `e₁` and `e₂`. -/
theorem TraceStep.map_congr {e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁} {e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂}
    (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (hcomm : ∀ x, e₂ (ea.sumCongr ec x) = eb.sumCongr ec (e₁ x))
    {x : α₁ ⊕ γ₁} {n : ℕ} {y : β₁ ⊕ γ₁} (h : e₁.TraceStep x n y) :
    e₂.TraceStep (ea.sumCongr ec x) n (eb.sumCongr ec y) := by
  induction h with
  | zero x => exact traceStep_zero_iff.mpr (hcomm x)
  | @succ x c _ _ hx _ ih =>
    have hx' : e₂ (ea.sumCongr ec x) = .inr (ec c) := by rw [hcomm x, hx]; rfl
    exact .succ hx' ih

/-- Equivalence of closed feedback subtypes induced by componentwise equivalences intertwining
`e₁` and `e₂`. -/
def traceClosedCongr {e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁} {e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂}
    (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (hcomm : ∀ x, e₂ (ea.sumCongr ec x) = eb.sumCongr ec (e₁ x)) :
    e₁.TraceClosed ≃ e₂.TraceClosed := by
  have hcomm' : ∀ x, e₁ (ea.symm.sumCongr ec.symm x) = eb.symm.sumCongr ec.symm (e₂ x) := fun x =>
    (eb.sumCongr ec).injective (by simpa using (hcomm (ea.symm.sumCongr ec.symm x)).symm)
  refine ec.subtypeEquiv fun c => not_congr ⟨fun ⟨b, n, hn⟩ => ⟨eb b, n, ?_⟩,
    fun ⟨b, n, hn⟩ => ⟨eb.symm b, n, ?_⟩⟩
  · exact hn.map_congr ea eb ec hcomm
  · simpa using hn.map_congr ea.symm eb.symm ec.symm hcomm'

/-- `traceClosedCongr` acts on the underlying feedback value as `ec`. -/
@[simp]
theorem val_traceClosedCongr_apply {e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁} {e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂}
    (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (hcomm : ∀ x, e₂ (ea.sumCongr ec x) = eb.sumCongr ec (e₁ x)) (c : e₁.TraceClosed) :
    (traceClosedCongr ea eb ec hcomm c).1 = ec c.1 := (rfl)

variable [Fintype γ₁] [Fintype γ₂]

/-- Naturality of `Equiv.trace` with respect to equivalences on `α`, `β`, and `γ`. -/
theorem trace_congr_apply {e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁} {e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂}
    (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (hcomm : ∀ x, e₂ (ea.sumCongr ec x) = eb.sumCongr ec (e₁ x)) (a : α₁) :
    eb (e₁.trace a) = e₂.trace (ea a) := by
  symm
  rw [e₂.trace_apply_eq_iff]
  obtain ⟨n, hn⟩ := e₁.trace_apply_eq_iff.mp (rfl : e₁.trace a = e₁.trace a)
  exact ⟨n, hn.map_congr ea eb ec hcomm⟩

private theorem tracePerm_eq_permCongr {e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁} {e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂}
    (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (hcomm : ∀ x, e₂ (ea.sumCongr ec x) = eb.sumCongr ec (e₁ x)) :
    e₂.tracePerm = (traceClosedCongr ea eb ec hcomm).permCongrHom e₁.tracePerm := by
  ext c
  obtain ⟨c₁, rfl⟩ := (traceClosedCongr ea eb ec hcomm).surjective c
  apply (Sum.inr_injective (α := β₂))
  simp only [permCongrHom_coe, permCongr_apply, symm_apply_apply, inr_val_tracePerm_apply,
    val_traceClosedCongr_apply]
  have hc := hcomm (.inr c₁.1)
  simp only [sumCongr_apply, Sum.map_inr] at hc
  rw [hc, ← e₁.inr_val_tracePerm_apply]
  rfl

/-- Naturality of `Equiv.TraceLoop` with respect to equivalences on `α`, `β`, and `γ`. -/
def traceLoopCongr {e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁} {e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂}
    (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (hcomm : ∀ x, e₂ (ea.sumCongr ec x) = eb.sumCongr ec (e₁ x)) :
    e₁.TraceLoop ≃ e₂.TraceLoop :=
  Quotient.congr (traceClosedCongr ea eb ec hcomm) fun c₁ c₂ => by
    -- Unfold `Setoid.r` on `Perm.SameCycle.setoid` to `Perm.SameCycle` to rewrite `e₂.tracePerm`.
    change e₁.tracePerm.SameCycle c₁ c₂ ↔
      e₂.tracePerm.SameCycle (traceClosedCongr ea eb ec hcomm c₁)
        (traceClosedCongr ea eb ec hcomm c₂)
    rw [tracePerm_eq_permCongr ea eb ec hcomm]
    refine exists_congr fun z => ?_
    rw [← map_zpow, permCongrHom_coe, permCongr_apply, symm_apply_apply,
      (traceClosedCongr ea eb ec hcomm).injective.eq_iff]

/-- `traceLoopCongr` transports `traceLoopMk` via `traceClosedCongr`. -/
@[simp]
theorem traceLoopCongr_mk {e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁} {e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂}
    (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (hcomm : ∀ x, e₂ (ea.sumCongr ec x) = eb.sumCongr ec (e₁ x)) (c : e₁.TraceClosed) :
    traceLoopCongr ea eb ec hcomm (e₁.traceLoopMk c) =
      e₂.traceLoopMk (traceClosedCongr ea eb ec hcomm c) := (rfl)

end Congruence

section Parallel

variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*}

/-- Combining two independent feedback bijections `e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁` and
`e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂` in parallel over `γ₁ ⊕ γ₂`. -/
def parallelSum (e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁) (e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂) :
    (α₁ ⊕ α₂) ⊕ (γ₁ ⊕ γ₂) ≃ (β₁ ⊕ β₂) ⊕ (γ₁ ⊕ γ₂) :=
  (Equiv.sumSumSumComm α₁ α₂ γ₁ γ₂).trans
    ((e₁.sumCongr e₂).trans (Equiv.sumSumSumComm β₁ β₂ γ₁ γ₂).symm)

private theorem parallelSum_map_inl (e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁) (e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂)
    (x : α₁ ⊕ γ₁) :
    parallelSum e₁ e₂ (Sum.map Sum.inl Sum.inl x) = Sum.map Sum.inl Sum.inl (e₁ x) := by
  cases x <;> cases h : e₁ _ <;> simp [parallelSum, Equiv.sumSumSumComm, h]

private theorem parallelSum_map_inr (e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁) (e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂)
    (x : α₂ ⊕ γ₂) :
    parallelSum e₁ e₂ (Sum.map Sum.inr Sum.inr x) = Sum.map Sum.inr Sum.inr (e₂ x) := by
  cases x <;> cases h : e₂ _ <;> simp [parallelSum, Equiv.sumSumSumComm, h]

private theorem TraceStep.parallel_inl {e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁} (e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂)
    {x : α₁ ⊕ γ₁} {n : ℕ} {y : β₁ ⊕ γ₁} (h : e₁.TraceStep x n y) :
    (parallelSum e₁ e₂).TraceStep (Sum.map Sum.inl Sum.inl x) n (Sum.map Sum.inl Sum.inl y) := by
  induction h with
  | zero x => exact traceStep_zero_iff.mpr (parallelSum_map_inl e₁ e₂ x)
  | @succ x c _ _ hx _ ih =>
    exact .succ (by rw [parallelSum_map_inl, hx]; rfl) ih

private theorem TraceStep.parallel_inr (e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁) {e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂}
    {x : α₂ ⊕ γ₂} {n : ℕ} {y : β₂ ⊕ γ₂} (h : e₂.TraceStep x n y) :
    (parallelSum e₁ e₂).TraceStep (Sum.map Sum.inr Sum.inr x) n (Sum.map Sum.inr Sum.inr y) := by
  induction h with
  | zero x => exact traceStep_zero_iff.mpr (parallelSum_map_inr e₁ e₂ x)
  | @succ x c _ _ hx _ ih =>
    exact .succ (by rw [parallelSum_map_inr, hx]; rfl) ih

private theorem TraceStep.of_parallel_inl {e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁} {e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂}
    {x : α₁ ⊕ γ₁} {n : ℕ} {z : (β₁ ⊕ β₂) ⊕ (γ₁ ⊕ γ₂)}
    (h : (parallelSum e₁ e₂).TraceStep (Sum.map Sum.inl Sum.inl x) n z) :
    ∃ y : β₁ ⊕ γ₁, z = Sum.map Sum.inl Sum.inl y ∧ e₁.TraceStep x n y := by
  induction n generalizing x with
  | zero =>
    rw [traceStep_zero_iff, parallelSum_map_inl] at h
    exact ⟨e₁ x, h.symm, .zero x⟩
  | succ n ih =>
    obtain ⟨c, hx, h'⟩ := traceStep_succ_iff.mp h
    rw [parallelSum_map_inl] at hx
    rcases h1 : e₁ x with b₁ | c₁ <;> rw [h1] at hx
    · cases hx
    · cases Sum.inr.inj hx
      obtain ⟨y, rfl, hy⟩ := ih (x := .inr c₁) h'
      exact ⟨y, rfl, .succ h1 hy⟩

private theorem TraceStep.of_parallel_inr {e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁} {e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂}
    {x : α₂ ⊕ γ₂} {n : ℕ} {z : (β₁ ⊕ β₂) ⊕ (γ₁ ⊕ γ₂)}
    (h : (parallelSum e₁ e₂).TraceStep (Sum.map Sum.inr Sum.inr x) n z) :
    ∃ y : β₂ ⊕ γ₂, z = Sum.map Sum.inr Sum.inr y ∧ e₂.TraceStep x n y := by
  induction n generalizing x with
  | zero =>
    rw [traceStep_zero_iff, parallelSum_map_inr] at h
    exact ⟨e₂ x, h.symm, .zero x⟩
  | succ n ih =>
    obtain ⟨c, hx, h'⟩ := traceStep_succ_iff.mp h
    rw [parallelSum_map_inr] at hx
    rcases h2 : e₂ x with b₂ | c₂ <;> rw [h2] at hx
    · cases hx
    · cases Sum.inr.inj hx
      obtain ⟨y, rfl, hy⟩ := ih (x := .inr c₂) h'
      exact ⟨y, rfl, .succ h2 hy⟩

/-- Closed feedback elements of `parallelSum e₁ e₂` decompose as the disjoint union of the closed
feedback elements of `e₁` and of `e₂`. -/
def traceClosedParallelEquiv (e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁) (e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂) :
    (parallelSum e₁ e₂).TraceClosed ≃ e₁.TraceClosed ⊕ e₂.TraceClosed := by
  have hinl : ∀ c₁ : γ₁, (parallelSum e₁ e₂).IsClosedSeam (.inl c₁) ↔ e₁.IsClosedSeam c₁ := by
    refine fun c₁ => not_congr ⟨?_, fun ⟨b₁, n, hn⟩ => ⟨.inl b₁, n, hn.parallel_inl e₂⟩⟩
    rintro ⟨_, n, hn⟩
    obtain ⟨b₁ | _, hy, hs⟩ := TraceStep.of_parallel_inl (x := .inr c₁) hn
    · exact ⟨b₁, n, hs⟩
    · cases hy
  have hinr : ∀ c₂ : γ₂, (parallelSum e₁ e₂).IsClosedSeam (.inr c₂) ↔ e₂.IsClosedSeam c₂ := by
    refine fun c₂ => not_congr ⟨?_, fun ⟨b₂, n, hn⟩ => ⟨.inr b₂, n, hn.parallel_inr e₁⟩⟩
    rintro ⟨_, n, hn⟩
    obtain ⟨b₂ | _, hy, hs⟩ := TraceStep.of_parallel_inr (x := .inr c₂) hn
    · exact ⟨b₂, n, hs⟩
    · cases hy
  exact
    { toFun := fun
        | ⟨.inl c₁, hc⟩ => .inl ⟨c₁, (hinl c₁).mp hc⟩
        | ⟨.inr c₂, hc⟩ => .inr ⟨c₂, (hinr c₂).mp hc⟩
      invFun := fun
        | .inl c₁ => ⟨.inl c₁.1, (hinl c₁.1).mpr c₁.2⟩
        | .inr c₂ => ⟨.inr c₂.1, (hinr c₂.1).mpr c₂.2⟩
      left_inv := fun ⟨c, _⟩ => by cases c <;> rfl
      right_inv := fun c => by cases c <;> rfl }

private theorem val_traceClosedParallelEquiv_symm_inl
    (e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁) (e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂) (c₁ : e₁.TraceClosed) :
    ((traceClosedParallelEquiv e₁ e₂).symm (.inl c₁)).1 = .inl c₁.1 := rfl

private theorem val_traceClosedParallelEquiv_symm_inr
    (e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁) (e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂) (c₂ : e₂.TraceClosed) :
    ((traceClosedParallelEquiv e₁ e₂).symm (.inr c₂)).1 = .inr c₂.1 := rfl

variable [Fintype γ₁] [Fintype γ₂]

/-- Tracing a parallel sum of bijections is the sum of their individual traces. -/
@[simp]
theorem trace_parallelSum (e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁) (e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂) :
    (parallelSum e₁ e₂).trace = e₁.trace.sumCongr e₂.trace := by
  ext (a₁ | a₂)
  · rw [(parallelSum e₁ e₂).trace_apply_eq_iff]
    obtain ⟨n, hn⟩ := e₁.trace_apply_eq_iff.mp (rfl : e₁.trace a₁ = e₁.trace a₁)
    exact ⟨n, hn.parallel_inl e₂⟩
  · rw [(parallelSum e₁ e₂).trace_apply_eq_iff]
    obtain ⟨n, hn⟩ := e₂.trace_apply_eq_iff.mp (rfl : e₂.trace a₂ = e₂.trace a₂)
    exact ⟨n, hn.parallel_inr e₁⟩

private theorem permCongr_tracePerm_parallelSum
    (e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁) (e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂) :
    (traceClosedParallelEquiv e₁ e₂).permCongrHom (parallelSum e₁ e₂).tracePerm =
      Perm.sumCongrHom _ _ (e₁.tracePerm, e₂.tracePerm) := by
  ext (c₁ | c₂)
  · simp only [permCongrHom_coe, permCongr_apply, Perm.sumCongrHom_apply, sumCongr_apply,
      Sum.map_inl]
    refine (traceClosedParallelEquiv e₁ e₂).symm.injective
      (Subtype.ext ((Sum.inr_injective (α := β₁ ⊕ β₂)) ?_))
    rw [(traceClosedParallelEquiv e₁ e₂).symm_apply_apply, val_traceClosedParallelEquiv_symm_inl,
      (parallelSum e₁ e₂).inr_val_tracePerm_apply, val_traceClosedParallelEquiv_symm_inl]
    exact (parallelSum_map_inl e₁ e₂ (.inr c₁.1)).trans
      (by rw [← e₁.inr_val_tracePerm_apply]; rfl)
  · simp only [permCongrHom_coe, permCongr_apply, Perm.sumCongrHom_apply, sumCongr_apply,
      Sum.map_inr]
    refine (traceClosedParallelEquiv e₁ e₂).symm.injective
      (Subtype.ext ((Sum.inr_injective (α := β₁ ⊕ β₂)) ?_))
    rw [(traceClosedParallelEquiv e₁ e₂).symm_apply_apply, val_traceClosedParallelEquiv_symm_inr,
      (parallelSum e₁ e₂).inr_val_tracePerm_apply, val_traceClosedParallelEquiv_symm_inr]
    exact (parallelSum_map_inr e₁ e₂ (.inr c₂.1)).trans
      (by rw [← e₂.inr_val_tracePerm_apply]; rfl)

private theorem sameCycle_parallelSum_symm_iff
    (e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁) (e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂)
    (x y : e₁.TraceClosed ⊕ e₂.TraceClosed) :
    (parallelSum e₁ e₂).tracePerm.SameCycle ((traceClosedParallelEquiv e₁ e₂).symm x)
        ((traceClosedParallelEquiv e₁ e₂).symm y) ↔
      ((Perm.sumCongrHom _ _ (e₁.tracePerm, e₂.tracePerm)).SameCycle x y) := by
  rw [← permCongr_tracePerm_parallelSum e₁ e₂]
  refine exists_congr fun z => ?_
  rw [← map_zpow, permCongrHom_coe, permCongr_apply]
  exact (traceClosedParallelEquiv e₁ e₂).eq_symm_apply

/-- Closed feedback loops of a parallel sum decompose as the disjoint union of the closed loops of
the two factors. -/
def traceLoopParallelEquiv (e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁) (e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂) :
    (parallelSum e₁ e₂).TraceLoop ≃ e₁.TraceLoop ⊕ e₂.TraceLoop := by
  let cl := traceClosedParallelEquiv e₁ e₂
  have hsum_zpow : ∀ z : ℤ, (e₁.tracePerm.sumCongr e₂.tracePerm) ^ z =
      (e₁.tracePerm ^ z).sumCongr (e₂.tracePerm ^ z) :=
    fun z => (map_zpow (Perm.sumCongrHom _ _) (e₁.tracePerm, e₂.tracePerm) z).symm
  refine
    { toFun := Quotient.lift (Sum.map e₁.traceLoopMk e₂.traceLoopMk ∘ cl) fun c c' h => ?_
      invFun := Sum.elim
        (Quotient.lift (fun c₁ => (parallelSum e₁ e₂).traceLoopMk (cl.symm (.inl c₁)))
          fun c₁ c₁' ⟨z, hz⟩ => ((parallelSum e₁ e₂).traceLoopMk_eq_iff).mpr <|
            (sameCycle_parallelSum_symm_iff e₁ e₂ _ _).mpr ⟨z, by simp [hsum_zpow, hz]⟩)
        (Quotient.lift (fun c₂ => (parallelSum e₁ e₂).traceLoopMk (cl.symm (.inr c₂)))
          fun c₂ c₂' ⟨z, hz⟩ => ((parallelSum e₁ e₂).traceLoopMk_eq_iff).mpr <|
            (sameCycle_parallelSum_symm_iff e₁ e₂ _ _).mpr ⟨z, by simp [hsum_zpow, hz]⟩)
      left_inv := Quotient.ind fun c => by
        obtain ⟨c₁ | c₂, rfl⟩ := cl.symm.surjective c
        · exact congrArg (Sum.elim _ _)
            (congrArg (Sum.map e₁.traceLoopMk e₂.traceLoopMk) (cl.apply_symm_apply (.inl c₁)))
        · exact congrArg (Sum.elim _ _)
            (congrArg (Sum.map e₁.traceLoopMk e₂.traceLoopMk) (cl.apply_symm_apply (.inr c₂)))
      right_inv := fun
        | .inl l₁ => Quotient.inductionOn l₁ fun c₁ =>
            congrArg (Sum.map e₁.traceLoopMk e₂.traceLoopMk) (cl.apply_symm_apply (.inl c₁))
        | .inr l₂ => Quotient.inductionOn l₂ fun c₂ =>
            congrArg (Sum.map e₁.traceLoopMk e₂.traceLoopMk) (cl.apply_symm_apply (.inr c₂)) }
  obtain ⟨x, rfl⟩ := cl.symm.surjective c
  obtain ⟨y, rfl⟩ := cl.symm.surjective c'
  obtain ⟨z, hz⟩ := (sameCycle_parallelSum_symm_iff e₁ e₂ x y).mp h
  rw [Perm.sumCongrHom_apply, hsum_zpow] at hz
  rcases x with c₁ | c₂ <;> rcases y with c₁' | c₂' <;> simp only [sumCongr_apply, Sum.map] at hz
  · simp [Function.comp, Sum.inl.inj hz ▸ Perm.SameCycle.zpow_right Perm.SameCycle.rfl]
  · cases hz
  · cases hz
  · simp [Function.comp, Sum.inr.inj hz ▸ Perm.SameCycle.zpow_right Perm.SameCycle.rfl]

/-- `traceLoopParallelEquiv.symm` embeds a left closed loop into `parallelSum e₁ e₂`. -/
@[simp]
theorem traceLoopParallelEquiv_symm_inl_mk (e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁) (e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂)
    (c₁ : e₁.TraceClosed) :
    (traceLoopParallelEquiv e₁ e₂).symm (.inl (e₁.traceLoopMk c₁)) =
      (parallelSum e₁ e₂).traceLoopMk ((traceClosedParallelEquiv e₁ e₂).symm (.inl c₁)) := (rfl)

/-- `traceLoopParallelEquiv.symm` embeds a right closed loop into `parallelSum e₁ e₂`. -/
@[simp]
theorem traceLoopParallelEquiv_symm_inr_mk (e₁ : α₁ ⊕ γ₁ ≃ β₁ ⊕ γ₁) (e₂ : α₂ ⊕ γ₂ ≃ β₂ ⊕ γ₂)
    (c₂ : e₂.TraceClosed) :
    (traceLoopParallelEquiv e₁ e₂).symm (.inr (e₂.traceLoopMk c₂)) =
      (parallelSum e₁ e₂).traceLoopMk ((traceClosedParallelEquiv e₁ e₂).symm (.inr c₂)) := (rfl)

end Parallel

section Sequential

variable {α β γ₁ γ₂ : Type*}

/-- Reassociating `α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂)` so that `γ₂` is traced out first. -/
def reassocRight (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂)) :
    (α ⊕ γ₁) ⊕ γ₂ ≃ (β ⊕ γ₁) ⊕ γ₂ :=
  (Equiv.sumAssoc α γ₁ γ₂).trans (E.trans (Equiv.sumAssoc β γ₁ γ₂).symm)

private theorem apply_sumAssoc_eq_reassocRight (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂))
    (x : (α ⊕ γ₁) ⊕ γ₂) :
    E (Equiv.sumAssoc α γ₁ γ₂ x) = Equiv.sumAssoc β γ₁ γ₂ (reassocRight E x) := by
  simp [reassocRight]

private theorem TraceStep.to_reassocRight_source {E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂)}
    {x : (α ⊕ γ₁) ⊕ γ₂} {k : ℕ} {y : (β ⊕ γ₁) ⊕ γ₂}
    (h : (reassocRight E).TraceStep x k y) :
    E.TraceStep (Equiv.sumAssoc α γ₁ γ₂ x) k (Equiv.sumAssoc β γ₁ γ₂ y) := by
  induction h with
  | zero x => exact traceStep_zero_iff.mpr (apply_sumAssoc_eq_reassocRight E x)
  | @succ x c₂ _ _ hx _ ih =>
    exact .succ (by rw [apply_sumAssoc_eq_reassocRight E x, hx]; rfl) ih

private theorem TraceStep.compare_reassocRight {E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂)}
    {x : (α ⊕ γ₁) ⊕ γ₂} {k N : ℕ} {y : β ⊕ γ₁} {z : β ⊕ (γ₁ ⊕ γ₂)}
    (h' : (reassocRight E).TraceStep x k (.inl y))
    (h : E.TraceStep (Equiv.sumAssoc α γ₁ γ₂ x) N z) :
    (N < k ∧ ∃ c₂ : γ₂, z = .inr (.inr c₂)) ∨
      (N = k ∧ z = Equiv.sumAssoc β γ₁ γ₂ (.inl y)) ∨
      (k < N ∧ ∃ c₁ : γ₁, y = .inr c₁ ∧ E.TraceStep (.inr (.inl c₁)) (N - 1 - k) z) := by
  induction k generalizing x N with
  | zero =>
    rw [traceStep_zero_iff] at h'
    have hx : E (Equiv.sumAssoc α γ₁ γ₂ x) = Equiv.sumAssoc β γ₁ γ₂ (.inl y) := by
      rw [apply_sumAssoc_eq_reassocRight E x, h']
    rcases y with b | c₁ <;> cases N
    · exact .inr (.inl ⟨rfl, (traceStep_zero_iff.mp h).symm.trans hx⟩)
    · obtain ⟨_, hx', _⟩ := traceStep_succ_iff.mp h
      cases hx.symm.trans hx'
    · exact .inr (.inl ⟨rfl, (traceStep_zero_iff.mp h).symm.trans hx⟩)
    · obtain ⟨_, hx', hrest⟩ := traceStep_succ_iff.mp h
      cases Sum.inr.inj (hx.symm.trans hx')
      exact .inr (.inr ⟨Nat.succ_pos _, c₁, rfl, by simpa using hrest⟩)
  | succ k ih =>
    obtain ⟨c₂, hx, h'rest⟩ := traceStep_succ_iff.mp h'
    have hx' : E (Equiv.sumAssoc α γ₁ γ₂ x) = .inr (.inr c₂) := by
      rw [apply_sumAssoc_eq_reassocRight E x, hx]; rfl
    cases N with
    | zero => exact .inl ⟨Nat.succ_pos _, c₂, (traceStep_zero_iff.mp h).symm.trans hx'⟩
    | succ N =>
      obtain ⟨_, hx'', hrest⟩ := traceStep_succ_iff.mp h
      cases Sum.inr.inj (hx'.symm.trans hx'')
      rcases ih h'rest hrest with ⟨hlt, c₂', hc₂'⟩ | ⟨rfl, hz⟩ | ⟨hlt, c₁, hy, hstep⟩
      · exact .inl ⟨Nat.succ_lt_succ hlt, c₂', hc₂'⟩
      · exact .inr (.inl ⟨rfl, hz⟩)
      · exact .inr (.inr ⟨Nat.succ_lt_succ hlt, c₁, hy,
          (by omega : N - 1 - k = N + 1 - 1 - (k + 1)) ▸ hstep⟩)

private theorem isClosedSeam_reassocRight_inr (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂))
    (c₂ : (reassocRight E).TraceClosed) : E.IsClosedSeam (.inr c₂.1) := by
  have happ : ∀ d : γ₂, E (.inr (.inr d)) = Equiv.sumAssoc β γ₁ γ₂ (reassocRight E (.inr d)) :=
    fun d => by simp [reassocRight]
  have hstay : ∀ (N : ℕ) (d : (reassocRight E).TraceClosed) (z : β ⊕ (γ₁ ⊕ γ₂)),
      E.TraceStep (.inr (.inr d.1)) N z → ∃ d' : γ₂, z = .inr (.inr d') := by
    intro N
    induction N with
    | zero =>
      intro d z hz
      rw [traceStep_zero_iff, happ d.1] at hz
      rcases hE : reassocRight E (.inr d.1) with y | d'
      · exact (d.2 ⟨y, 0, traceStep_zero_iff.mpr hE⟩).elim
      · exact ⟨d', hz.symm.trans (by rw [hE]; rfl)⟩
    | succ N ih =>
      intro d z hz
      obtain ⟨w, hw, hrest⟩ := traceStep_succ_iff.mp hz
      rcases hE : reassocRight E (.inr d.1) with y | d'
      · exact (d.2 ⟨y, 0, traceStep_zero_iff.mpr hE⟩).elim
      · have hw' : (.inr w : β ⊕ (γ₁ ⊕ γ₂)) = .inr (.inr d') := by
          rw [← hw, happ d.1, hE]; rfl
        cases Sum.inr.inj hw'
        exact ih ⟨d', isClosedSeam_of_apply_eq_inr d.2 hE⟩ z hrest
  rintro ⟨b, N, hN⟩
  obtain ⟨_, hd'⟩ := hstay N c₂ (.inl b) hN
  cases hd'

/-- Inclusion of closed `γ₂`-elements into `E.TraceClosed`. -/
def inrTraceClosed (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂))
    (c₂ : (reassocRight E).TraceClosed) : E.TraceClosed :=
  ⟨.inr c₂.1, isClosedSeam_reassocRight_inr E c₂⟩

section Step2

variable [Fintype γ₂]

private theorem exists_traceStep_of_sumAssoc {E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂)}
    {x : α ⊕ γ₁} {N : ℕ} {b : β}
    (h : E.TraceStep (Equiv.sumAssoc α γ₁ γ₂ (.inl x)) N (.inl b)) :
    ∃ M, (reassocRight E).trace.TraceStep x M (.inl b) := by
  induction N using Nat.strong_induction_on generalizing x with
  | ind N ih =>
    obtain ⟨k, hk⟩ := (reassocRight E).trace_apply_eq_iff.mp
      (rfl : (reassocRight E).trace x = (reassocRight E).trace x)
    rcases TraceStep.compare_reassocRight hk h with ⟨_, _, hz⟩ | ⟨_, hz⟩ | ⟨_, c₁, hy, hstep⟩
    · cases hz
    · rcases hy : (reassocRight E).trace x with b' | c₁ <;> rw [hy] at hz
      · cases Sum.inl.inj hz
        exact ⟨0, traceStep_zero_iff.mpr hy⟩
      · cases hz
    · obtain ⟨M', hM'⟩ := ih (N - 1 - k) (by omega) (x := .inr c₁) hstep
      exact ⟨M' + 1, .succ hy hM'⟩

private theorem exists_sumAssoc_of_traceStep {E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂)}
    {x : α ⊕ γ₁} {M : ℕ} {y : β ⊕ γ₁}
    (h : (reassocRight E).trace.TraceStep x M y) :
    ∃ N, E.TraceStep (Equiv.sumAssoc α γ₁ γ₂ (.inl x)) N (Equiv.sumAssoc β γ₁ γ₂ (.inl y)) := by
  induction h with
  | zero x =>
    obtain ⟨k, hk⟩ := (reassocRight E).trace_apply_eq_iff.mp
      (rfl : (reassocRight E).trace x = (reassocRight E).trace x)
    exact ⟨k, hk.to_reassocRight_source⟩
  | @succ x c₁ _ _ hx _ ih =>
    obtain ⟨k, hk⟩ := (reassocRight E).trace_apply_eq_iff.mp hx
    obtain ⟨N', hN'⟩ := ih
    exact ⟨k + 1 + N', hk.to_reassocRight_source.append hN'⟩

private theorem isClosedSeam_reassocRight_inl (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂)) (c₁ : γ₁) :
    E.IsClosedSeam (.inl c₁) ↔ (reassocRight E).trace.IsClosedSeam c₁ :=
  not_congr ⟨fun ⟨b, _, hN⟩ => let ⟨M, hM⟩ := exists_traceStep_of_sumAssoc (x := .inr c₁) hN
    ⟨b, M, hM⟩,
    fun ⟨b, _, hM⟩ => let ⟨N, hN⟩ := exists_sumAssoc_of_traceStep hM; ⟨b, N, hN⟩⟩

/-- Inclusion of closed `γ₁`-elements of `(reassocRight E).trace` into `E.TraceClosed`. -/
def inlTraceClosed (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂))
    (c₁ : (reassocRight E).trace.TraceClosed) : E.TraceClosed :=
  ⟨.inl c₁.1, (isClosedSeam_reassocRight_inl E c₁.1).mpr c₁.2⟩

end Step2

variable [Fintype γ₁] [Fintype γ₂]

/-- **Sequential trace law (vanishing II)**: tracing `γ₂` and then `γ₁` produces the exact same
bijection `α ≃ β` as tracing `γ₁ ⊕ γ₂` simultaneously. -/
@[simp]
theorem trace_reassocRight (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂)) :
    (reassocRight E).trace.trace = E.trace := by
  ext a
  symm
  rw [E.trace_apply_eq_iff]
  obtain ⟨M, hM⟩ := (reassocRight E).trace.trace_apply_eq_iff.mp
    (rfl : (reassocRight E).trace.trace a = (reassocRight E).trace.trace a)
  exact exists_sumAssoc_of_traceStep hM

private theorem tracePerm_pow_inr_step {α' β' γ' : Type*} [Fintype γ']
    (e : α' ⊕ γ' ≃ β' ⊕ γ') (w : e.TraceClosed) (n : ℕ) :
    e.TraceStep (.inr w.1) n (.inr ((e.tracePerm ^ (n + 1)) w).1) := by
  induction n generalizing w with
  | zero =>
    rw [Nat.zero_add, pow_one]
    exact traceStep_zero_iff.mpr (e.inr_val_tracePerm_apply w).symm
  | succ n ih =>
    have hstep := ih (e.tracePerm w)
    rw [← Perm.mul_apply, ← pow_succ] at hstep
    exact .succ (e.inr_val_tracePerm_apply w).symm hstep

private theorem tracePerm_zpow_inrTraceClosed (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂))
    (z : ℤ) (c₂ : (reassocRight E).TraceClosed) :
    (E.tracePerm ^ z) (inrTraceClosed E c₂) =
      inrTraceClosed E (((reassocRight E).tracePerm ^ z) c₂) := by
  have hstep : ∀ x, E.tracePerm (inrTraceClosed E x) =
      inrTraceClosed E ((reassocRight E).tracePerm x) := fun x => by
    apply Subtype.ext
    apply (Sum.inr_injective (α := β))
    rw [E.inr_val_tracePerm_apply]
    have h₁ := apply_sumAssoc_eq_reassocRight E (.inr x.1)
    simp only [sumAssoc_apply_inr, inrTraceClosed] at h₁ ⊢
    rw [h₁, ← (reassocRight E).inr_val_tracePerm_apply, sumAssoc_apply_inr]
  have hinv : ∀ x, E.tracePerm⁻¹ (inrTraceClosed E x) =
      inrTraceClosed E ((reassocRight E).tracePerm⁻¹ x) := fun x =>
    E.tracePerm.injective (by simp [hstep])
  induction z generalizing c₂ with
  | zero => rfl
  | succ n ih => rw [zpow_add_one, zpow_add_one, Perm.mul_apply, Perm.mul_apply, hstep, ih]
  | pred n ih => rw [zpow_sub_one, zpow_sub_one, Perm.mul_apply, Perm.mul_apply, hinv, ih]

private theorem exists_pow_tracePerm_inlTraceClosed (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂))
    (u : (reassocRight E).trace.TraceClosed) :
    ∃ k, (E.tracePerm ^ (k + 1)) (inlTraceClosed E u) =
        inlTraceClosed E ((reassocRight E).trace.tracePerm u) ∧
      ∀ j, 0 < j → j < k + 1 → ∃ c₂ : γ₂, ((E.tracePerm ^ j) (inlTraceClosed E u)).1 = .inr c₂ := by
  obtain ⟨k, hk⟩ := (reassocRight E).trace_apply_eq_iff.mp
    ((reassocRight E).trace.inr_val_tracePerm_apply u).symm
  refine ⟨k, Subtype.ext <| Sum.inr.inj <|
    (tracePerm_pow_inr_step E (inlTraceClosed E u) k).eq_of_eq_len hk.to_reassocRight_source, ?_⟩
  intro j hjpos _
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
  rcases TraceStep.compare_reassocRight hk (tracePerm_pow_inr_step E (inlTraceClosed E u) j') with
    ⟨_, c₂, hc₂⟩ | ⟨_, _⟩ | ⟨_, _⟩
  · exact ⟨c₂, Sum.inr.inj hc₂⟩
  · omega
  · omega

private theorem sameCycle_inlTraceClosed_fwd (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂))
    {u v : (reassocRight E).trace.TraceClosed}
    (h : (reassocRight E).trace.tracePerm.SameCycle u v) :
    E.tracePerm.SameCycle (inlTraceClosed E u) (inlTraceClosed E v) := by
  have hnat : ∀ (n : ℕ) (w : (reassocRight E).trace.TraceClosed),
      E.tracePerm.SameCycle (inlTraceClosed E w)
        (inlTraceClosed E (((reassocRight E).trace.tracePerm ^ n) w)) := by
    intro n
    induction n with
    | zero => exact fun _ => Perm.SameCycle.rfl
    | succ n ih =>
      intro w
      rw [pow_succ', Perm.mul_apply]
      obtain ⟨k, hk, _⟩ := exists_pow_tracePerm_inlTraceClosed E
        (((reassocRight E).trace.tracePerm ^ n) w)
      exact (ih w).trans ⟨((k + 1 : ℕ) : ℤ), by rw [zpow_natCast, hk]⟩
  obtain ⟨n | n, hz⟩ := h
  · exact hz ▸ hnat n u
  · have hz' : ((reassocRight E).trace.tracePerm ^ (n + 1)) v = u := by
      have hzero : ((n + 1 : ℕ) : ℤ) + Int.negSucc n = 0 := by omega
      rw [← hz, ← zpow_natCast, ← Perm.mul_apply, ← zpow_add, hzero, zpow_zero, Perm.one_apply]
    exact hz' ▸ (hnat (n + 1) v).symm

private theorem sameCycle_inlTraceClosed_bwd (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂))
    {u v : (reassocRight E).trace.TraceClosed}
    (h : E.tracePerm.SameCycle (inlTraceClosed E u) (inlTraceClosed E v)) :
    (reassocRight E).trace.tracePerm.SameCycle u v := by
  have hnat : ∀ (m : ℕ) (x y : (reassocRight E).trace.TraceClosed),
      (E.tracePerm ^ m) (inlTraceClosed E x) = inlTraceClosed E y →
        (reassocRight E).trace.tracePerm.SameCycle x y := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro x y hm
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val hm)) ▸ Perm.SameCycle.rfl
      · obtain ⟨k, hk, hmid⟩ := exists_pow_tracePerm_inlTraceClosed E x
        have hge : k + 1 ≤ m := by
          by_contra hlt
          obtain ⟨_, hc₂⟩ := hmid m hmpos (Nat.lt_of_not_ge hlt)
          rw [hm] at hc₂
          cases hc₂
        have hm' : (E.tracePerm ^ (m - (k + 1)))
            (inlTraceClosed E ((reassocRight E).trace.tracePerm x)) = inlTraceClosed E y := by
          rw [← hk, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hge, hm]
        exact ((reassocRight E).trace.tracePerm.sameCycle_apply_right.mpr Perm.SameCycle.rfl).trans
          (ih (m - (k + 1)) (by omega) _ y hm')
  obtain ⟨m | m, hz⟩ := h
  · exact hnat m u v hz
  · have hz' : (E.tracePerm ^ (m + 1)) (inlTraceClosed E v) = inlTraceClosed E u := by
      have hzero : ((m + 1 : ℕ) : ℤ) + Int.negSucc m = 0 := by omega
      rw [← hz, ← zpow_natCast, ← Perm.mul_apply, ← zpow_add, hzero, zpow_zero, Perm.one_apply]
    exact (hnat (m + 1) v u hz').symm

private def traceLoopSumAssocFwd (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂)) :
    (reassocRight E).TraceLoop ⊕ (reassocRight E).trace.TraceLoop → E.TraceLoop :=
  Sum.elim
    (Quotient.lift (fun c₂ => E.traceLoopMk (inrTraceClosed E c₂))
      fun c₂ _ ⟨z, hz⟩ => (E.traceLoopMk_eq_iff).mpr
        ⟨z, (tracePerm_zpow_inrTraceClosed E z c₂).trans (by rw [hz])⟩)
    (Quotient.lift (fun c₁ => E.traceLoopMk (inlTraceClosed E c₁))
      fun _ _ huv => (E.traceLoopMk_eq_iff).mpr (sameCycle_inlTraceClosed_fwd E huv))

private theorem traceLoopSumAssocFwd_injective (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂)) :
    Function.Injective (traceLoopSumAssocFwd E) := by
  rintro (l₂ | l₁) (l₂' | l₁') h
  · refine congrArg Sum.inl (Quotient.inductionOn₂ l₂ l₂' (fun c₂ c₂' h => ?_) h)
    obtain ⟨z, hz⟩ := (E.traceLoopMk_eq_iff).mp h
    exact ((reassocRight E).traceLoopMk_eq_iff).mpr ⟨z, Subtype.ext <|
      Sum.inr.inj (congrArg Subtype.val ((tracePerm_zpow_inrTraceClosed E z c₂).symm.trans hz))⟩
  · refine Quotient.inductionOn₂ l₂ l₁' (fun c₂ _ h => ?_) h
    obtain ⟨z, hz⟩ := (E.traceLoopMk_eq_iff).mp h
    cases congrArg Subtype.val ((tracePerm_zpow_inrTraceClosed E z c₂).symm.trans hz)
  · refine Quotient.inductionOn₂ l₁ l₂' (fun _ c₂' h => ?_) h
    obtain ⟨z, hz⟩ := (E.traceLoopMk_eq_iff).mp h.symm
    cases congrArg Subtype.val ((tracePerm_zpow_inrTraceClosed E z c₂').symm.trans hz)
  · refine congrArg Sum.inr (Quotient.inductionOn₂ l₁ l₁' (fun c₁ c₁' h => ?_) h)
    exact ((reassocRight E).trace.traceLoopMk_eq_iff).mpr
      (sameCycle_inlTraceClosed_bwd E ((E.traceLoopMk_eq_iff).mp h))

private def traceLoopSumAssocBwdAux (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂))
    (w : E.TraceClosed) : (reassocRight E).TraceLoop ⊕ (reassocRight E).trace.TraceLoop :=
  match hw : w.1 with
  | .inl c₁ => .inr ((reassocRight E).trace.traceLoopMk
      ⟨c₁, (isClosedSeam_reassocRight_inl E c₁).mp (hw ▸ w.2)⟩)
  | .inr c₂ =>
    match hwalk : (reassocRight E).traceWalk (Fintype.card γ₂) (.inr c₂) with
    | .inl (.inl b) =>
      (by
        obtain ⟨k, _, hk⟩ := exists_traceStep_of_traceWalk_eq_inl hwalk
        exact (hw ▸ w.2) ⟨b, k, hk.to_reassocRight_source⟩ : False).elim
    | .inl (.inr c₁) =>
      .inr ((reassocRight E).trace.traceLoopMk ⟨c₁, by
        obtain ⟨k, _, hk⟩ := exists_traceStep_of_traceWalk_eq_inl hwalk
        have heq : ((E.tracePerm ^ (k + 1)) w).1 = .inl c₁ := Sum.inr.inj <|
          (hw ▸ tracePerm_pow_inr_step E w k).eq_of_eq_len hk.to_reassocRight_source
        exact (isClosedSeam_reassocRight_inl E c₁).mp (heq ▸ ((E.tracePerm ^ (k + 1)) w).2)⟩)
    | .inr _ =>
      .inl ((reassocRight E).traceLoopMk ⟨c₂, fun hop => by
        obtain ⟨y, hy⟩ := ((reassocRight E).isOpenSeam_iff_traceWalk_inl c₂).mp hop
        cases hwalk.symm.trans hy⟩)

private theorem traceLoopSumAssocFwd_bwdAux (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂))
    (w : E.TraceClosed) :
    traceLoopSumAssocFwd E (traceLoopSumAssocBwdAux E w) = E.traceLoopMk w := by
  rcases w with ⟨c₁ | c₂, hw⟩
  · rfl
  · dsimp only [traceLoopSumAssocBwdAux]
    split
    · rename_i b hwalk
      obtain ⟨k, _, hk⟩ := exists_traceStep_of_traceWalk_eq_inl hwalk
      exact (hw ⟨b, k, hk.to_reassocRight_source⟩).elim
    · rename_i c₁ hwalk
      obtain ⟨k, _, hk⟩ := exists_traceStep_of_traceWalk_eq_inl hwalk
      have heq : ((E.tracePerm ^ (k + 1)) ⟨.inr c₂, hw⟩).1 = .inl c₁ := Sum.inr.inj <|
        (tracePerm_pow_inr_step E ⟨.inr c₂, hw⟩ k).eq_of_eq_len hk.to_reassocRight_source
      exact (E.traceLoopMk_eq_iff).mpr <| Perm.SameCycle.symm
        ⟨((k + 1 : ℕ) : ℤ), by rw [zpow_natCast]; exact Subtype.ext heq⟩
    · rfl

/-- **Sequential loop decomposition (Bekić's lemma for closed loops)**: tracing `γ₂` first and then
`γ₁` partitions the closed feedback loops in `γ₁ ⊕ γ₂` into those staying entirely inside `γ₂` and
those visiting `γ₁`. -/
def traceLoopSumAssocEquiv (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂)) :
    (reassocRight E).TraceLoop ⊕ (reassocRight E).trace.TraceLoop ≃ E.TraceLoop where
  toFun := traceLoopSumAssocFwd E
  invFun := Quotient.lift (traceLoopSumAssocBwdAux E) fun w₁ w₂ hw =>
    traceLoopSumAssocFwd_injective E <| (traceLoopSumAssocFwd_bwdAux E w₁).trans <|
      (E.traceLoopMk_eq_iff.mpr hw).trans (traceLoopSumAssocFwd_bwdAux E w₂).symm
  left_inv x := traceLoopSumAssocFwd_injective E <| by
    rcases x with l₂ | l₁
    · exact Quotient.inductionOn l₂ fun c₂ => traceLoopSumAssocFwd_bwdAux E (inrTraceClosed E c₂)
    · exact Quotient.inductionOn l₁ fun c₁ => traceLoopSumAssocFwd_bwdAux E (inlTraceClosed E c₁)
  right_inv := Quotient.ind (traceLoopSumAssocFwd_bwdAux E)

/-- `traceLoopSumAssocEquiv` embeds a closed loop in `γ₂` via `inrTraceClosed`. -/
@[simp]
theorem traceLoopSumAssocEquiv_inl_mk (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂))
    (c₂ : (reassocRight E).TraceClosed) :
    traceLoopSumAssocEquiv E (.inl ((reassocRight E).traceLoopMk c₂)) =
      E.traceLoopMk (inrTraceClosed E c₂) := (rfl)

/-- `traceLoopSumAssocEquiv` embeds a closed loop in `γ₁` via `inlTraceClosed`. -/
@[simp]
theorem traceLoopSumAssocEquiv_inr_mk (E : α ⊕ (γ₁ ⊕ γ₂) ≃ β ⊕ (γ₁ ⊕ γ₂))
    (c₁ : (reassocRight E).trace.TraceClosed) :
    traceLoopSumAssocEquiv E (.inr ((reassocRight E).trace.traceLoopMk c₁)) =
      E.traceLoopMk (inlTraceClosed E c₁) := (rfl)

end Sequential

end Equiv
