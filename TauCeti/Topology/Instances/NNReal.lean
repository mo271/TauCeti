/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Topology.EMetricSpace.Diam
public import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Metric diameter of intervals in `ℝ≥0`

The extended metric diameter of `Set.Icc a b` in `ℝ≥0` is `(b - a : ℝ≥0)`, matching the truncated
subtraction of `ℝ≥0` whether `a ≤ b` or `b < a`.

## Main declarations

* `NNReal.ediam_Icc`: `Metric.ediam (Set.Icc a b) = (b - a : ℝ≥0)`.
-/

public section

open scoped ENNReal NNReal

namespace NNReal

/-- The extended metric diameter of a closed interval `Set.Icc a b` in `ℝ≥0` is `(b - a : ℝ≥0)`. -/
@[simp]
theorem ediam_Icc (a b : ℝ≥0) : Metric.ediam (Set.Icc a b) = (b - a : ℝ≥0) := by
  rw [← NNReal.isometry_coe.ediam_image, NNReal.image_coe_Icc, Real.ediam_Icc,
    ENNReal.ofReal_sub _ a.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal,
    ENNReal.coe_sub]

end NNReal
