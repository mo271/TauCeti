/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Add
public import TauCeti.MeasureTheory.Group.Foelner.Int

/-!
# Amenability of the integers

The intervals `{0, …, n}` form a counting-measure additive Følner sequence on `ℤ`
(`TauCeti.isAddFoelner_int_Icc`), so `ℤ` has additive Følner sets (`TauCeti.hasAddFoelnerSets_int`)
and is an amenable topological additive group for every additive group topology
(`TauCeti.AddAmenable.int`). Transporting along `Multiplicative` gives Følner sets and amenability
for `Multiplicative ℤ` (`TauCeti.hasFoelnerSets_multiplicative_int`,
`TauCeti.Amenable.multiplicative_int`).

## Main results

* `TauCeti.hasAddFoelnerSets_int`: `ℤ` has additive Følner sets.
* `TauCeti.AddAmenable.int`: `ℤ` is additively amenable for every additive group topology.
* `TauCeti.hasFoelnerSets_multiplicative_int`: `Multiplicative ℤ` has Følner sets.
* `TauCeti.Amenable.multiplicative_int`: `Multiplicative ℤ` is amenable for every group topology.

## References

* A. Garrido, *An introduction to amenable groups*, Example 3.5.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Example G.5.4.
-/

public section

namespace TauCeti

/-- The integers have additive Følner sets, witnessed by the intervals `{0, …, n}`. -/
theorem hasAddFoelnerSets_int : HasAddFoelnerSets ℤ :=
  .of_isAddFoelner isAddFoelner_int_Icc

/-- The integers are additively amenable for every additive group topology. -/
instance AddAmenable.int {integerTopology : TopologicalSpace ℤ}
    [hTopology : letI := integerTopology; IsTopologicalAddGroup ℤ] :
    letI := integerTopology; AddAmenable ℤ := by
  let := integerTopology
  exact .of_hasAddFoelnerSets hasAddFoelnerSets_int

/-- The integer group `Multiplicative ℤ` has Følner sets. -/
theorem hasFoelnerSets_multiplicative_int : HasFoelnerSets (Multiplicative ℤ) :=
  hasFoelnerSets_multiplicative_iff.2 hasAddFoelnerSets_int

/-- The integer group `Multiplicative ℤ` is amenable for every group topology. -/
instance Amenable.multiplicative_int
    {integerTopology : TopologicalSpace (Multiplicative ℤ)}
    [hTopology : letI := integerTopology; IsTopologicalGroup (Multiplicative ℤ)] :
    letI := integerTopology; Amenable (Multiplicative ℤ) := by
  let := integerTopology
  exact .of_hasFoelnerSets hasFoelnerSets_multiplicative_int

end TauCeti
