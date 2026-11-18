/-
Copyright (c) 2026 Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Scholz
-/
module

public import CollarNeighbourhoods.IsInwardPointingVectorField
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-! Header-/

open Set Function Filter Module EuclideanSpace Convexity
open scoped Topology Manifold ContDiff

public section

variable {M H : Type*} [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]

-- this is how we say that `M` is a smooth manifold
variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] (t₀ : ℝ)
  {I : ModelWithCorners ℝ E H} {n : ℕ∞} [NeZero n] [IsManifold I n M]

def IsLocalFlowDomain (D : Set (M × ℝ)) :=
  ∀ p, IsConnected {t | (p, t) ∈ D} ∧ ({t | (p, t) ∈ D}.Nonempty → (p, t₀) ∈ D)

def IsFlowDomain (D : Set (M × ℝ)) :=
  ∀ p, IsConnected {t | (p, t) ∈ D} ∧ (p, t₀) ∈ D

structure IsFlowOn (γ : M → ℝ → M) (D : Set (M × ℝ)) (v : (x : M) → TangentSpace I x) where
  isMIntegralCurveOn p : IsMIntegralCurveOn (fun x ↦ γ p x) v {t | (p, t) ∈ D}
  toFun_zero : ∀ p, {t | (p, t) ∈ D}.Nonempty → γ p t₀ = p

omit [TopologicalSpace M] in
lemma isFlowDomain_univ : IsFlowDomain t₀ (univ : Set (M × ℝ)) := by
  intro
  simp [isConnected_univ]

/-
-- wrong
lemma isFlowDomain_ico_prod_nhd (t₀ : ℝ) {ε : ℝ} (hε : ε > 0) {x₀ : M} {u : Set M} (hu : u ∈ 𝓝 x₀) :
    IsLocalFlowDomain t₀ ((Ico t₀ (t₀ + ε)) ×ˢ u) := by
  intro p
  constructor
  · sorry
  · sorry






#check exists_isMIntegralCurveAt_of_contMDiffAt

lemma PartialEquiv.isInvertible_of_contMDiff  {H' : Type*} [TopologicalSpace H'] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {I' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    (p : M') (f : PartialEquiv M M') (hp : p ∈ f.target) (hf : CMDiff[f.source] n f) :
    (mfderiv[f.target] f.symm p).IsInvertible := by

  sorry

lemma isMIntegralCurve_pullback
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {I' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (s : Set ℝ) (hγ : IsMIntegralCurveOn γ v s)
    (f : PartialEquiv M M') (hs : γ '' s ⊆ f.source) (hf : CMDiff[f.source] n f)
    (hf : CMDiff[f.target] n f.symm) :
    IsMIntegralCurveOn (f ∘ γ)
      (VectorField.mpullbackWithin I' I f.symm v f.target) s := by
  intro t ht
  unfold VectorField.mpullbackWithin
  have : (mfderiv[f.target] f.symm ((f ∘ γ) t)).inverse = mfderiv[f.source] f (γ t) := by
    have : (mfderiv[f.target] f.symm ((f ∘ γ) t)).IsInvertible := sorry
    ext x
    rw [this.inverse_apply_eq]

    sorry
  rw [this]
  rw [comp_apply]
  rw [PartialEquiv.left_inv f (hs (mem_image_of_mem γ ht))]

  sorry

theorem isMIntegralCurve_iff_isIntegralCurve (γ : ℝ → M) (v : (x : M) → TangentSpace I x)
    (s : Set ℝ) (t : ℝ) (ht : t ∈ s) (hγ : IsMIntegralCurveOn γ v s) :
    IsMIntegralCurveOn ((extChartAt I (γ t)) ∘ γ)
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I (γ t)).symm v
      (extChartAt I (γ t)).target)
      (s ∩ (γ ⁻¹' (extChartAt I (γ t)).source)) := by
  unfold IsMIntegralCurveOn HasMFDerivWithinAt at hγ
  intro x hx
  specialize hγ x hx.1



  sorry

theorem isMIntegralCurveOn_Ico_eqOn_of_contMDiff [IsManifold I 1 M] {γ γ' : ℝ → H}
    {v : (x : H) → TangentSpace I x} {t₀ : ℝ} [T2Space M] {a : ℝ} (ha : 0 < a)
    (hγ0 : I.IsBoundaryPoint (γ 0)) (hγt : ∀ t ∈ Ioo 0 a, I.IsInteriorPoint (γ 0))
    (hv : ContMDiff I I.tangent 1 fun (x : H) => (⟨x, v x⟩ : TangentBundle I H))
    (hγ : IsMIntegralCurveOn γ v (Ioo 0 a)) (hγ' : IsMIntegralCurveOn γ' v (Ico 0 a))
    (h : γ 0 = γ' 0) :
    EqOn γ γ' (Set.Ico 0 a) := by


  suffices EqOn γ γ' (Ioo 0 a) by
    intro x hx
    rw [← Ioo_union_left ha] at hx
    rcases hx with hx | hx
    · exact this hx
    · exact hx ▸ h
  -- this doesn't work like this
  sorry-/



-- look at `https://github.com/leanprover-community/mathlib4/pull/26394`.
-- this is only for interior points
