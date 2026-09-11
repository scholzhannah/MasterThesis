/-
Copyright (c) 2026 Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Scholz
-/
module

public import CollarNeighbourhoods.IsInwardPointingVectorField
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic

open Set Function Filter Module EuclideanSpace Convexity
open scoped Topology Manifold ContDiff

public section

variable {M H : Type*} [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]

-- this is how we say that `M` is a smooth manifold
variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {I : ModelWithCorners ℝ E H} {n : ℕ∞} [NeZero n] [IsManifold I n M]

def IsFlowDomain (D : Set (ℝ × M)) :=
  ∀ p, IsOpen {t | (t, p) ∈ D} ∧ Convex ℝ {t | (t, p) ∈ D} ∧ (0, p) ∈ D

structure FlowOn (D : Set (ℝ × M)) (v : (x : M) → TangentSpace I x) where
  toFun : ℝ × M → M
  isMIntegralCurveOn p : IsMIntegralCurveOn (fun x ↦ toFun (x, p)) v {t | (t, p) ∈ D}
  toFun_zero p : toFun (0, p) = p
  tuFun_add t s p : toFun (t, toFun (s, p)) = toFun (t + s, p)

omit [TopologicalSpace M] in
lemma isFlowDomain_univ : IsFlowDomain (univ : Set (ℝ × M)) := by
  intro
  simp [convex_univ]

def Flow (v : (x : M) → TangentSpace I x) := FlowOn univ v

-- we this we should be good, we also need to choose a different `ε`
def hiofrh (v : (x : H) → TangentSpace I x) (U : Set H)
  (hU : CMDiff[U] n (T% v)) : FlowOn ((Icc (-1) 1) ×ˢ U) v := sorry


-- look at `https://github.com/leanprover-community/mathlib4/pull/26394`.
-- this is only for interior points
