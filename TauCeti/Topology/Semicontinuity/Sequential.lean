/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Topology.Order.IsLUB

/-!
# Sequential lower semicontinuity

A function `f : X → β` is sequentially lower semicontinuous on `s`
(`TauCeti.SeqLowerSemicontinuousOn`) if whenever a sequence in `s` converges to `x ∈ s` and
`y < f x`, eventually `y < f (u n)`. This is the sequential counterpart of Mathlib's
`LowerSemicontinuousOn` and requires only a topological space `X` and a `<` relation on `β`.

In a linear order, sequential lower semicontinuity is equivalent to sequential closedness of
sublevel sets, so it agrees with topological lower semicontinuity whenever the domain (or subtype)
is a `SequentialSpace`. In a complete linear order it is equivalent to `f x ≤ liminf (f ∘ u) atTop`;
for real-valued functions, this becomes `(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop`,
accommodating sequences unbounded above. Along convergent real sequences it implies the finite-limit
inequality `f x ≤ r`, with the converse holding whenever `f` is bounded below on `s`. Finally, a
sequentially lower semicontinuous function is bounded below and attains its minimum on every
nonempty sequentially compact set.
-/

public section

open Filter Set Topology

namespace TauCeti

section Defs

variable {X β : Type*} [TopologicalSpace X] [LT β]

/-- A function `f : X → β` is sequentially lower semicontinuous on `s` if whenever a sequence in
`s` converges to `x ∈ s` and `y < f x`, eventually `y < f (u n)`. -/
def SeqLowerSemicontinuousOn (f : X → β) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ y < f x, ∀ u : ℕ → X, (∀ n, u n ∈ s) →
    Tendsto u atTop (𝓝 x) → ∀ᶠ n in atTop, y < f (u n)

/-- A function `f : X → β` is sequentially lower semicontinuous if whenever a sequence `u`
converges to `x` and `y < f x`, eventually `y < f (u n)`. -/
def SeqLowerSemicontinuous (f : X → β) : Prop :=
  ∀ x, ∀ y < f x, ∀ u : ℕ → X, Tendsto u atTop (𝓝 x) → ∀ᶠ n in atTop, y < f (u n)

/-- Unfolding characterization of `SeqLowerSemicontinuousOn`. -/
theorem seqLowerSemicontinuousOn_iff {f : X → β} {s : Set X} :
    SeqLowerSemicontinuousOn f s ↔
      ∀ x ∈ s, ∀ y < f x, ∀ u : ℕ → X, (∀ n, u n ∈ s) →
        Tendsto u atTop (𝓝 x) → ∀ᶠ n in atTop, y < f (u n) :=
  Iff.rfl

/-- Unfolding characterization of `SeqLowerSemicontinuous`. -/
theorem seqLowerSemicontinuous_iff {f : X → β} :
    SeqLowerSemicontinuous f ↔
      ∀ x, ∀ y < f x, ∀ u : ℕ → X, Tendsto u atTop (𝓝 x) → ∀ᶠ n in atTop, y < f (u n) :=
  Iff.rfl

end Defs

section Basic

variable {X Y β : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LT β]
  {f g : X → β} {s t : Set X}

/-- Sequential lower semicontinuity on `univ` is equivalent to global sequential lower
semicontinuity. -/
@[simp]
theorem seqLowerSemicontinuousOn_univ :
    SeqLowerSemicontinuousOn f univ ↔ SeqLowerSemicontinuous f :=
  ⟨fun h x y hy u hu ↦ h x (mem_univ x) y hy u (fun _ ↦ mem_univ _) hu,
    fun h x _ y hy u _ hu ↦ h x y hy u hu⟩

/-- Sequential lower semicontinuity of the restriction to `s` is equivalent to sequential lower
semicontinuity on `s`. -/
@[simp]
theorem seqLowerSemicontinuous_domRestrict_iff :
    SeqLowerSemicontinuous (s.domRestrict f) ↔ SeqLowerSemicontinuousOn f s := by
  refine ⟨fun h x hx y hy u hu hux ↦ ?_, fun h x y hy u hux ↦ ?_⟩
  · have hv : Tendsto (fun n ↦ (⟨u n, hu n⟩ : s)) atTop (𝓝 ⟨x, hx⟩) :=
      Topology.IsInducing.subtypeVal.tendsto_nhds_iff.2 hux
    exact h ⟨x, hx⟩ y hy _ hv
  · exact h x.1 x.2 y hy (fun n ↦ (u n).1) (fun n ↦ (u n).2)
      ((continuous_subtype_val.tendsto x).comp hux)

/-- Every function is sequentially lower semicontinuous on the empty set. -/
@[simp]
theorem seqLowerSemicontinuousOn_empty : SeqLowerSemicontinuousOn f ∅ :=
  fun _ hx ↦ hx.elim

/-- Every function is sequentially lower semicontinuous on a singleton. -/
@[simp]
theorem seqLowerSemicontinuousOn_singleton (x : X) : SeqLowerSemicontinuousOn f {x} := by
  rintro a rfl y hy u hu -
  exact Eventually.of_forall fun n ↦ (hu n).symm ▸ hy

/-- Constant functions are sequentially lower semicontinuous. -/
@[simp]
theorem seqLowerSemicontinuous_const (c : β) : SeqLowerSemicontinuous fun _ : X ↦ c :=
  fun _ _ hy _ _ ↦ Eventually.of_forall fun _ ↦ hy

/-- Constant functions are sequentially lower semicontinuous on every set. -/
@[simp]
theorem seqLowerSemicontinuousOn_const (c : β) : SeqLowerSemicontinuousOn (fun _ : X ↦ c) s :=
  fun _ _ _ hy _ _ _ ↦ Eventually.of_forall fun _ ↦ hy

/-- Global sequential lower semicontinuity implies sequential lower semicontinuity on every set. -/
theorem SeqLowerSemicontinuous.seqLowerSemicontinuousOn (hf : SeqLowerSemicontinuous f)
    (s : Set X) : SeqLowerSemicontinuousOn f s :=
  fun x _ y hy u _ hu ↦ hf x y hy u hu

/-- Sequential lower semicontinuity is inherited by subsets. -/
theorem SeqLowerSemicontinuousOn.mono (hf : SeqLowerSemicontinuousOn f s) (hts : t ⊆ s) :
    SeqLowerSemicontinuousOn f t :=
  fun x hx y hy u hu hux ↦ hf x (hts hx) y hy u (fun n ↦ hts (hu n)) hux

/-- Sequential lower semicontinuity on `s` depends only on the values of the function on `s`. -/
theorem seqLowerSemicontinuousOn_congr (h : EqOn f g s) :
    SeqLowerSemicontinuousOn f s ↔ SeqLowerSemicontinuousOn g s := by
  constructor
  · intro hf x hx y hy u hu hux
    have h1 := hf x hx y (h hx ▸ hy) u hu hux
    filter_upwards [h1] with n hn using h (hu n) ▸ hn
  · intro hg x hx y hy u hu hux
    have h1 := hg x hx y ((h hx).symm ▸ hy) u hu hux
    filter_upwards [h1] with n hn using (h (hu n)).symm ▸ hn

/-- Precomposing a sequentially lower semicontinuous function with a sequentially continuous map
preserves sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuous.comp_seqContinuous (hf : SeqLowerSemicontinuous f)
    {g : Y → X} (hg : SeqContinuous g) : SeqLowerSemicontinuous (f ∘ g) :=
  fun x y hy u hux ↦ hf (g x) y hy (g ∘ u) (hg hux)

/-- Precomposing a function sequentially lower semicontinuous on `s` with a sequentially continuous
map carrying `t` into `s` yields a function sequentially lower semicontinuous on `t`. -/
theorem SeqLowerSemicontinuousOn.comp_seqContinuous (hf : SeqLowerSemicontinuousOn f s)
    {g : Y → X} (hg : SeqContinuous g) {t : Set Y} (hmaps : MapsTo g t s) :
    SeqLowerSemicontinuousOn (f ∘ g) t :=
  fun x hx y hy u hu hux ↦ hf (g x) (hmaps hx) y hy (g ∘ u) (fun n ↦ hmaps (hu n)) (hg hux)

end Basic

end TauCeti

section Bridges

variable {X β : Type*} [TopologicalSpace X] {f : X → β} {s : Set X}

/-- Every lower semicontinuous function is sequentially lower semicontinuous. -/
theorem LowerSemicontinuous.seqLowerSemicontinuous [Preorder β] (hf : LowerSemicontinuous f) :
    TauCeti.SeqLowerSemicontinuous f :=
  fun x y hy _ hu ↦ hu.eventually (hf x y hy)

/-- Every function lower semicontinuous on `s` is sequentially lower semicontinuous on `s`. -/
theorem LowerSemicontinuousOn.seqLowerSemicontinuousOn [Preorder β]
    (hf : LowerSemicontinuousOn f s) :
    TauCeti.SeqLowerSemicontinuousOn f s :=
  fun x hx y hy _ hu hux ↦
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hux
      (Eventually.of_forall hu)).eventually (hf x hx y hy)

/-- Every sequentially continuous function into a linear order with closed `Iic` intervals is
sequentially lower semicontinuous. -/
theorem SeqContinuous.seqLowerSemicontinuous [LinearOrder β] [TopologicalSpace β]
    [ClosedIicTopology β] (hf : SeqContinuous f) :
    TauCeti.SeqLowerSemicontinuous f :=
  fun _ _ hy _ hu ↦ (hf hu).eventually (Ioi_mem_nhds hy)

end Bridges

namespace TauCeti

section LinearOrder

variable {X β : Type*} [TopologicalSpace X] [LinearOrder β] {f g : X → β} {s : Set X}

/-- A function into a linear order is sequentially lower semicontinuous if and only if all of its
sublevel sets are sequentially closed. -/
theorem seqLowerSemicontinuous_iff_isSeqClosed_preimage :
    SeqLowerSemicontinuous f ↔ ∀ b : β, IsSeqClosed (f ⁻¹' Iic b) := by
  refine ⟨fun hf b u x hu hux ↦ le_of_not_gt fun hlt ↦ ?_, fun h x y hy u hux ↦ ?_⟩
  · obtain ⟨n, hn⟩ := (hf x b hlt u hux).exists
    exact (not_le_of_gt hn) (hu n)
  · by_contra hne
    have hfreq : ∃ᶠ n in atTop, f (u n) ≤ y := by
      simpa only [not_eventually, not_lt] using hne
    obtain ⟨φ, hφ, hφle⟩ := extraction_of_frequently_atTop hfreq
    exact (not_le_of_gt hy) (h y hφle (hux.comp hφ.tendsto_atTop))

/-- Every sublevel of a sequentially lower semicontinuous function is sequentially closed. -/
theorem SeqLowerSemicontinuous.isSeqClosed_preimage (hf : SeqLowerSemicontinuous f) (b : β) :
    IsSeqClosed (f ⁻¹' Iic b) :=
  seqLowerSemicontinuous_iff_isSeqClosed_preimage.1 hf b

/-- A function into a linear order is sequentially lower semicontinuous on `s` if and only if every
sublevel is sequentially closed relative to `s`. -/
theorem seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel :
    SeqLowerSemicontinuousOn f s ↔
      ∀ b : β, ∀ (u : ℕ → X) (x : X), (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → (∀ n, f (u n) ≤ b) → f x ≤ b := by
  rw [← seqLowerSemicontinuous_domRestrict_iff, seqLowerSemicontinuous_iff_isSeqClosed_preimage]
  constructor
  · intro h b u x hu hx hux hub
    have hv : Tendsto (fun n ↦ (⟨u n, hu n⟩ : s)) atTop (𝓝 ⟨x, hx⟩) :=
      Topology.IsInducing.subtypeVal.tendsto_nhds_iff.2 hux
    exact h b hub hv
  · intro h b u x hu hux
    exact h b (fun n ↦ (u n).1) x.1 (fun n ↦ (u n).2) x.2
      ((continuous_subtype_val.tendsto x).comp hux) hu

/-- On a sequentially closed set, every sublevel of a sequentially lower semicontinuous function is
sequentially closed. -/
theorem SeqLowerSemicontinuousOn.isSeqClosed_inter_preimage_Iic
    (hf : SeqLowerSemicontinuousOn f s) (hs : IsSeqClosed s) (b : β) :
    IsSeqClosed (s ∩ f ⁻¹' Iic b) := by
  intro u x hu hux
  have hx : x ∈ s := hs (fun n ↦ (hu n).1) hux
  exact ⟨hx, seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel.1 hf b u x
    (fun n ↦ (hu n).1) hx hux (fun n ↦ (hu n).2)⟩

/-- On a sequential space, sequential lower semicontinuity implies topological lower
semicontinuity. -/
theorem SeqLowerSemicontinuous.lowerSemicontinuous [SequentialSpace X]
    (hf : SeqLowerSemicontinuous f) : LowerSemicontinuous f :=
  lowerSemicontinuous_iff_isClosed_preimage.2 fun b ↦ (hf.isSeqClosed_preimage b).isClosed

/-- On a sequential space, sequential and topological lower semicontinuity agree. -/
theorem seqLowerSemicontinuous_iff_lowerSemicontinuous [SequentialSpace X] :
    SeqLowerSemicontinuous f ↔ LowerSemicontinuous f :=
  ⟨SeqLowerSemicontinuous.lowerSemicontinuous, LowerSemicontinuous.seqLowerSemicontinuous⟩

/-- If `s` is a sequential space in the subspace topology, sequential lower semicontinuity on `s`
implies topological lower semicontinuity on `s`. -/
theorem SeqLowerSemicontinuousOn.lowerSemicontinuousOn [SequentialSpace s]
    (hf : SeqLowerSemicontinuousOn f s) : LowerSemicontinuousOn f s := by
  have h : LowerSemicontinuous (s.domRestrict f) :=
    (seqLowerSemicontinuous_domRestrict_iff.2 hf).lowerSemicontinuous
  simpa only [lowerSemicontinuous_restrict_iff] using h

/-- On a subset that is a sequential space in the subspace topology, sequential and topological
lower semicontinuity agree. -/
theorem seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn [SequentialSpace s] :
    SeqLowerSemicontinuousOn f s ↔ LowerSemicontinuousOn f s :=
  ⟨SeqLowerSemicontinuousOn.lowerSemicontinuousOn, LowerSemicontinuousOn.seqLowerSemicontinuousOn⟩

/-- The pointwise supremum of two functions sequentially lower semicontinuous on `s` is
sequentially lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.sup (hf : SeqLowerSemicontinuousOn f s)
    (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun x ↦ f x ⊔ g x) s := by
  intro x hx y hy u hu hux
  simp only [lt_sup_iff] at hy ⊢
  rcases hy with hy | hy
  · filter_upwards [hf x hx y hy u hu hux] with n using Or.inl
  · filter_upwards [hg x hx y hy u hu hux] with n using Or.inr

/-- The pointwise supremum of two sequentially lower semicontinuous functions is sequentially lower
semicontinuous. -/
theorem SeqLowerSemicontinuous.sup (hf : SeqLowerSemicontinuous f)
    (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous fun x ↦ f x ⊔ g x :=
  seqLowerSemicontinuousOn_univ.1 <|
    (hf.seqLowerSemicontinuousOn univ).sup (hg.seqLowerSemicontinuousOn univ)

/-- The pointwise infimum of two functions sequentially lower semicontinuous on `s` is sequentially
lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.inf (hf : SeqLowerSemicontinuousOn f s)
    (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun x ↦ f x ⊓ g x) s := by
  intro x hx y hy u hu hux
  simp only [lt_inf_iff] at hy ⊢
  exact (hf x hx y hy.1 u hu hux).and (hg x hx y hy.2 u hu hux)

/-- The pointwise infimum of two sequentially lower semicontinuous functions is sequentially lower
semicontinuous. -/
theorem SeqLowerSemicontinuous.inf (hf : SeqLowerSemicontinuous f)
    (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous fun x ↦ f x ⊓ g x :=
  seqLowerSemicontinuousOn_univ.1 <|
    (hf.seqLowerSemicontinuousOn univ).inf (hg.seqLowerSemicontinuousOn univ)

/-- The sum of two functions sequentially lower semicontinuous on `s` into a linearly ordered
abelian group is sequentially lower semicontinuous on `s`. -/
theorem SeqLowerSemicontinuousOn.add [AddCommGroup β] [IsOrderedAddMonoid β]
    (hf : SeqLowerSemicontinuousOn f s) (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun x ↦ f x + g x) s := by
  intro x hx y hy u hu hux
  by_cases hmid : ∃ a, y - g x < a ∧ a < f x
  · obtain ⟨a, hya, haf⟩ := hmid
    filter_upwards [hf x hx a haf u hu hux, hg x hx (y - a) (sub_lt_comm.1 hya) u hu hux]
      with n hfn hgn
    simpa only [add_sub_cancel] using add_lt_add hfn hgn
  · have h1 : ∀ᶠ n in atTop, f x ≤ f (u n) :=
      (hf x hx (y - g x) (sub_lt_iff_lt_add.2 hy) u hu hux).mono fun n hn ↦
        le_of_not_gt fun hlt ↦ hmid ⟨f (u n), hn, hlt⟩
    have h2 : ∀ᶠ n in atTop, g x ≤ g (u n) :=
      (hg x hx (y - f x) (sub_lt_iff_lt_add'.2 hy) u hu hux).mono fun n hn ↦
        le_of_not_gt fun hlt ↦ hmid ⟨y - g (u n), sub_lt_sub_left hlt y, sub_lt_comm.1 hn⟩
    filter_upwards [h1, h2] with n hfn hgn
    exact hy.trans_le (add_le_add hfn hgn)

/-- The sum of two sequentially lower semicontinuous functions into a linearly ordered abelian group
is sequentially lower semicontinuous. -/
theorem SeqLowerSemicontinuous.add [AddCommGroup β] [IsOrderedAddMonoid β]
    (hf : SeqLowerSemicontinuous f) (hg : SeqLowerSemicontinuous g) :
    SeqLowerSemicontinuous fun x ↦ f x + g x :=
  seqLowerSemicontinuousOn_univ.1 <|
    (hf.seqLowerSemicontinuousOn univ).add (hg.seqLowerSemicontinuousOn univ)

end LinearOrder

section GroupWithZero

variable {X β : Type*} [TopologicalSpace X] {f : X → β} {s : Set X}

/-- Nonnegative scaling preserves sequential lower semicontinuity on `s`. -/
theorem SeqLowerSemicontinuousOn.const_mul [GroupWithZero β] [PartialOrder β] [PosMulReflectLT β]
    (hf : SeqLowerSemicontinuousOn f s) {c : β} (hc : 0 ≤ c) :
    SeqLowerSemicontinuousOn (fun x ↦ c * f x) s := by
  rcases hc.eq_or_lt with rfl | hpos
  · simpa only [zero_mul] using seqLowerSemicontinuousOn_const (0 : β)
  · intro x hx y hy u hu hux
    have hlt : c⁻¹ * y < f x := (inv_mul_lt_iff₀ hpos).2 hy
    filter_upwards [hf x hx (c⁻¹ * y) hlt u hu hux] with n hn
    exact (inv_mul_lt_iff₀ hpos).1 hn

/-- Nonnegative scaling preserves global sequential lower semicontinuity. -/
theorem SeqLowerSemicontinuous.const_mul [GroupWithZero β] [PartialOrder β] [PosMulReflectLT β]
    (hf : SeqLowerSemicontinuous f) {c : β} (hc : 0 ≤ c) :
    SeqLowerSemicontinuous fun x ↦ c * f x :=
  seqLowerSemicontinuousOn_univ.1 <|
    (hf.seqLowerSemicontinuousOn univ).const_mul hc

end GroupWithZero

section Supremum

variable {X : Type*} [TopologicalSpace X]

/-- The pointwise supremum of a pointwise bounded-above family of functions sequentially lower
semicontinuous on `s` into a conditionally complete linear order is sequentially lower
semicontinuous on `s`. -/
theorem seqLowerSemicontinuousOn_ciSup {ι : Sort*} {β : Type*} [ConditionallyCompleteLinearOrder β]
    {f : ι → X → β} {s : Set X} (bdd : ∀ x ∈ s, BddAbove (range fun i ↦ f i x))
    (hf : ∀ i, SeqLowerSemicontinuousOn (f i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ⨆ i, f i x) s := by
  cases isEmpty_or_nonempty ι
  · simpa only [iSup_of_empty'] using seqLowerSemicontinuousOn_const _
  · intro x hx y hy u hu hux
    obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup hy
    filter_upwards [hf i x hx y hi u hu hux] with n hn
    exact hn.trans_le (le_ciSup (bdd (u n) (hu n)) i)

/-- The pointwise supremum of a pointwise bounded-above family of sequentially lower semicontinuous
functions into a conditionally complete linear order is sequentially lower semicontinuous. -/
theorem seqLowerSemicontinuous_ciSup {ι : Sort*} {β : Type*} [ConditionallyCompleteLinearOrder β]
    {f : ι → X → β} (bdd : ∀ x, BddAbove (range fun i ↦ f i x))
    (hf : ∀ i, SeqLowerSemicontinuous (f i)) :
    SeqLowerSemicontinuous fun x ↦ ⨆ i, f i x :=
  seqLowerSemicontinuousOn_univ.1 <|
    seqLowerSemicontinuousOn_ciSup (fun x _ ↦ bdd x) fun i ↦ (hf i).seqLowerSemicontinuousOn univ

/-- The pointwise supremum of a family of functions sequentially lower semicontinuous on `s` is
sequentially lower semicontinuous on `s`. -/
theorem seqLowerSemicontinuousOn_iSup {ι : Sort*} {β : Type*} [CompleteLinearOrder β]
    {f : ι → X → β} {s : Set X} (hf : ∀ i, SeqLowerSemicontinuousOn (f i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ⨆ i, f i x) s :=
  seqLowerSemicontinuousOn_ciSup (by simp) hf

/-- The pointwise supremum of a family of sequentially lower semicontinuous functions is
sequentially lower semicontinuous. -/
theorem seqLowerSemicontinuous_iSup {ι : Sort*} {β : Type*} [CompleteLinearOrder β]
    {f : ι → X → β} (hf : ∀ i, SeqLowerSemicontinuous (f i)) :
    SeqLowerSemicontinuous fun x ↦ ⨆ i, f i x :=
  seqLowerSemicontinuous_ciSup (by simp) hf

end Supremum

section Liminf

variable {X β : Type*} [TopologicalSpace X] [CompleteLinearOrder β] {f : X → β} {s : Set X}

/-- In a complete linear order, sequential lower semicontinuity on `s` is equivalent to
`f x ≤ liminf (f ∘ u) atTop` along every sequence in `s` converging to `x ∈ s`. -/
theorem seqLowerSemicontinuousOn_iff_le_liminf :
    SeqLowerSemicontinuousOn f s ↔
      ∀ (u : ℕ → X) (x : X), (∀ n, u n ∈ s) → x ∈ s → Tendsto u atTop (𝓝 x) →
        f x ≤ liminf (f ∘ u) atTop := by
  refine ⟨fun h u x hu hx hux ↦ ?_, fun h x hx y hy u hu hux ↦
    eventually_lt_of_lt_liminf (hy.trans_le (h u x hu hx hux))⟩
  by_contra! hf
  obtain ⟨z, ltz, y, ylt, h₁⟩ := hf.exists_disjoint_Iio_Ioi
  exact ltz.not_ge
    (le_liminf_of_le (by isBoundedDefault) ((h x hx y ylt u hu hux).mono fun _ h₂ ↦
      le_of_not_gt fun h₃ ↦ (h₁ _ h₃ _ h₂).false))

/-- Along every sequence in `s` converging to `x ∈ s`, a sequentially lower semicontinuous function
into a complete linear order satisfies `f x ≤ liminf (f ∘ u) atTop`. -/
alias ⟨SeqLowerSemicontinuousOn.le_liminf, _⟩ := seqLowerSemicontinuousOn_iff_le_liminf

/-- In a complete linear order, global sequential lower semicontinuity is equivalent to
`f x ≤ liminf (f ∘ u) atTop` along every convergent sequence. -/
theorem seqLowerSemicontinuous_iff_le_liminf :
    SeqLowerSemicontinuous f ↔
      ∀ (u : ℕ → X) (x : X), Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  rw [← seqLowerSemicontinuousOn_univ, seqLowerSemicontinuousOn_iff_le_liminf]
  simp

/-- Along every convergent sequence, a sequentially lower semicontinuous function into a complete
linear order satisfies `f x ≤ liminf (f ∘ u) atTop`. -/
alias ⟨SeqLowerSemicontinuous.le_liminf, _⟩ := seqLowerSemicontinuous_iff_le_liminf

end Liminf

section RealEReal

variable {X : Type*} [TopologicalSpace X] {f : X → ℝ} {s : Set X}

/-- Coercing a real-valued function to `EReal` preserves and reflects sequential lower
semicontinuity. -/
@[simp]
theorem seqLowerSemicontinuousOn_coe_ereal_iff :
    SeqLowerSemicontinuousOn (fun x ↦ (f x : EReal)) s ↔ SeqLowerSemicontinuousOn f s := by
  constructor
  · intro h x hx y hy u hu hux
    simpa only [EReal.coe_lt_coe_iff] using
      h x hx (y : EReal) (EReal.coe_lt_coe_iff.2 hy) u hu hux
  · intro h x hx y hy u hu hux
    induction y with
    | bot => exact Eventually.of_forall fun _ ↦ EReal.bot_lt_coe _
    | top => exact (not_lt_of_ge le_top hy).elim
    | coe r =>
      simpa only [EReal.coe_lt_coe_iff] using
        h x hx r (EReal.coe_lt_coe_iff.1 hy) u hu hux

/-- A real-valued function is sequentially lower semicontinuous on `s` if and only if
`(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop` along every sequence in `s`
converging to `x ∈ s`. -/
theorem seqLowerSemicontinuousOn_iff_le_liminf_ereal :
    SeqLowerSemicontinuousOn f s ↔
      ∀ (u : ℕ → X) (x : X), (∀ n, u n ∈ s) → x ∈ s → Tendsto u atTop (𝓝 x) →
        (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousOn_coe_ereal_iff, seqLowerSemicontinuousOn_iff_le_liminf]
  simp only [Function.comp_def]

/-- Along every sequence in `s` converging to `x ∈ s`, a real-valued function sequentially lower
semicontinuous on `s` satisfies `(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop`. -/
alias ⟨SeqLowerSemicontinuousOn.le_liminf_ereal, _⟩ := seqLowerSemicontinuousOn_iff_le_liminf_ereal

end RealEReal

section TendstoAndMin

variable {X β : Type*} [TopologicalSpace X] {f : X → β} {s : Set X}

/-- Along a sequence in `s` converging to `x ∈ s` whose values converge to `r`, a sequentially
lower semicontinuous function satisfies `f x ≤ r`. -/
theorem SeqLowerSemicontinuousOn.le_of_tendsto [LinearOrder β] [TopologicalSpace β]
    [ClosedIciTopology β] (hf : SeqLowerSemicontinuousOn f s) {u : ℕ → X} {x : X} {r : β}
    (hu : ∀ n, u n ∈ s) (hx : x ∈ s) (hux : Tendsto u atTop (𝓝 x))
    (hr : Tendsto (f ∘ u) atTop (𝓝 r)) : f x ≤ r := by
  by_contra! hlt
  by_cases hmid : ∃ y, r < y ∧ y < f x
  · obtain ⟨y, hry, hyx⟩ := hmid
    obtain ⟨n, h1, h2⟩ := ((hf x hx y hyx u hu hux).and
      (hr.eventually (Iio_mem_nhds hry))).exists
    exact lt_asymm h1 h2
  · obtain ⟨n, h1, h2⟩ := ((hf x hx r hlt u hu hux).and
      (hr.eventually (Iio_mem_nhds hlt))).exists
    exact hmid ⟨f (u n), h1, h2⟩

/-- For a real-valued function bounded below on `s`, sequential lower semicontinuity on `s` is
equivalent to the finite-limit inequality `f x ≤ r` whenever `u n → x` in `s` and `f (u n) → r`. -/
theorem seqLowerSemicontinuousOn_iff_le_of_tendsto {f : X → ℝ} (hb : BddBelow (f '' s)) :
    SeqLowerSemicontinuousOn f s ↔
      ∀ (u : ℕ → X) (x : X) (r : ℝ), (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → Tendsto (f ∘ u) atTop (𝓝 r) → f x ≤ r := by
  refine ⟨fun hf _ _ _ hu hx hux hr ↦ hf.le_of_tendsto hu hx hux hr, fun h ↦ ?_⟩
  rw [seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel]
  intro b u x hu hx hux hub
  obtain ⟨m, hm⟩ := hb
  have hmem (n : ℕ) : f (u n) ∈ Icc m b := ⟨hm (mem_image_of_mem f (hu n)), hub n⟩
  obtain ⟨r, hr, φ, hφ, hlim⟩ := isCompact_Icc.isSeqCompact hmem
  exact (h (u ∘ φ) x r (fun n ↦ hu (φ n)) hx (hux.comp hφ.tendsto_atTop) hlim).trans hr.2

/-- The limit in `s` of a minimizing sequence for a sequentially lower semicontinuous function is a
minimizer on `s`. -/
theorem SeqLowerSemicontinuousOn.isMinOn_of_tendsto [ConditionallyCompleteLinearOrder β]
    [TopologicalSpace β] [ClosedIciTopology β] (hf : SeqLowerSemicontinuousOn f s)
    (hb : BddBelow (f '' s)) {u : ℕ → X} {x : X} (hu : ∀ n, u n ∈ s) (hx : x ∈ s)
    (hux : Tendsto u atTop (𝓝 x)) (hmin : Tendsto (f ∘ u) atTop (𝓝 (sInf (f '' s)))) :
    IsMinOn f s x :=
  fun _ hy ↦ (hf.le_of_tendsto hu hx hux hmin).trans (csInf_le hb (mem_image_of_mem f hy))

/-- A sequentially lower semicontinuous function is bounded below on every sequentially compact set,
provided `atBot` in the codomain is countably generated. -/
theorem SeqLowerSemicontinuousOn.bddBelow_of_isSeqCompact [LinearOrder β] [Nonempty β]
    [IsCountablyGenerated (atBot : Filter β)] (hf : SeqLowerSemicontinuousOn f s)
    (hs : IsSeqCompact s) : BddBelow (f '' s) := by
  by_contra hnb
  obtain ⟨b, hb⟩ := Filter.exists_seq_tendsto (atBot : Filter β)
  have hlt (n : ℕ) : ∃ a ∈ s, f a < b n := by
    by_contra! hall
    exact hnb ⟨b n, by rintro _ ⟨a, ha, rfl⟩; exact hall a ha⟩
  choose u hu hfu using hlt
  obtain ⟨x, hx, φ, hφ, hlim⟩ := hs hu
  have hnotlb : ∃ z ∈ s, f z < f x := by
    by_contra! hall
    exact hnb ⟨f x, by rintro _ ⟨z, hz, rfl⟩; exact hall z hz⟩
  obtain ⟨z, _, hzx⟩ := hnotlb
  have h1 : ∀ᶠ k in atTop, f z < f (u (φ k)) :=
    hf x hx (f z) hzx (u ∘ φ) (fun k ↦ hu (φ k)) hlim
  have h2 : ∀ᶠ k in atTop, b (φ k) ≤ f z :=
    (hb.comp hφ.tendsto_atTop).eventually (eventually_le_atBot (f z))
  obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
  exact not_lt_of_ge (hk2.trans' (hfu (φ k)).le) hk1

/-- **Sequential extreme value theorem.** A sequentially lower semicontinuous function attains its
minimum on every nonempty sequentially compact set, without assuming a prior lower bound. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_of_isSeqCompact
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [FirstCountableTopology β] [IsCountablyGenerated (atBot : Filter β)]
    (hf : SeqLowerSemicontinuousOn f s) (hne : s.Nonempty) (hs : IsSeqCompact s) :
    ∃ x ∈ s, IsMinOn f s x := by
  have : Nonempty β := hne.elim fun x _ ↦ ⟨f x⟩
  have hb : BddBelow (f '' s) := hf.bddBelow_of_isSeqCompact hs
  obtain ⟨u, hu, -, hmin⟩ := exists_seq_tendsto_sInf_image hne hb
  obtain ⟨x, hx, φ, hφ, hlim⟩ := hs hu
  exact ⟨x, hx, hf.isMinOn_of_tendsto hb (fun n ↦ hu (φ n)) hx hlim
    (hmin.comp hφ.tendsto_atTop)⟩

end TendstoAndMin

end TauCeti
