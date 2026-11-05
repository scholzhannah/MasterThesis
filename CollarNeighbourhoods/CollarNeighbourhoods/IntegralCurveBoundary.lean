module

public import Mathlib.Analysis.ODE.Basic
public import CollarNeighbourhoods.DerivableCone
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.ExtendFrom

/-! bjkkab-/

@[expose] public section

open Function Metric Set

-- thoughts about integral curves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (v : E → E) {x₀ : E} {s : Set E} {t₁ t₂ : ℝ} (ht : t₁ < t₂)

example (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (hfx₀ : ∀ x ∈ s, inwardPointing ℝ s x (v x))
    (hf : ContDiffOn ℝ 1 v s) (γ : ℝ → E) (hγ : IsIntegralCurveOn γ (fun _ x ↦ v x) (Ico t₁ t₂))
    (hγs : MapsTo γ (Ico t₁ t₂) s) :
    ∃ γ' : ℝ → E, IsIntegralCurveOn γ' (fun _ x ↦ v x) (Icc t₁ t₂) := by
  let (eq := hγ') γ' := extendFrom (Ico t₁ t₂) γ
  use γ'
  intro x hx
  rw [← Ico_union_right ht.le] at hx
  rcases hx with hx | hx
  · apply HasDerivWithinAt.congr_set (s := Ico t₁ t₂)
    · rw [← nhdsWithin_eq_iff_eventuallyEqSet]
      suffices Ico t₁ t₂ = Icc t₁ t₂ ∩ Ioo (t₁ - 1) t₂ by
        rw [this]
        symm
        exact nhdsWithin_restrict (Icc t₁ t₂)
          ⟨lt_of_lt_of_le (sub_one_lt t₁) hx.left, hx.right⟩ isOpen_Ioo
      apply subset_antisymm
      · intro x ⟨hx1, hx2⟩
        exact ⟨⟨hx1, hx2.le⟩, lt_of_lt_of_le (sub_one_lt t₁) hx1, hx2⟩
      · intro x ⟨⟨hx1, _⟩, _, hx2⟩
        exact ⟨hx1, hx2⟩
    · have : ∀ y ∈ Ico t₁ t₂, γ' y = γ y := by
        intro y hy
        rw [hγ', extendFrom_extends hγ.continuousOn _ hy]
      rw [this x hx]
      exact (hγ x hx).congr this (this x hx)
  rw [mem_singleton_iff] at hx
  subst x
  have : ∀ u ∈ Icc t₁ t₂, γ' u = ∫ (x : ℝ) in t₁..u, v (γ' x) := by sorry
  apply HasDerivWithinAt.congr ?_ this (this _ (right_mem_Icc.mpr ht.le))
  dsimp
  have : Fact (t₂ ∈ Set.Icc t₁ t₂) := by
    constructor
    exact right_mem_Icc.mpr ht.le
  apply intervalIntegral.integral_hasDerivWithinAt_right
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.le]
    -- make this into a have, we need this below
    apply hf.continuousOn.comp
    · -- write a theorem for this like `continuousOn_Icc_extendFrom_Ioo`

      sorry
    · sorry
  · refine ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin ?_ ?_ t₂
    · sorry
    · sorry
  · sorry
