module

public import Mathlib.Analysis.ODE.Basic
public import CollarNeighbourhoods.DerivableCone
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.ExtendFrom
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Topology.Order.ExtendFrom

/-! bjkkab-/

@[expose] public section

open Function Metric Set

-- thoughts about integral curves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (v : E → E) {x₀ : E} {s : Set E} {t₁ t₂ : ℝ} (ht : t₁ < t₂)

-- this is simply wrong
example (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (hfx₀ : ∀ x ∈ s, inwardPointing s x (v x))
    (hf : ContDiffOn ℝ 1 v s) (γ : ℝ → E) (hγ : IsIntegralCurveOn γ (fun _ x ↦ v x) (Ico t₁ t₂))
    (hγs : MapsTo γ (Ico t₁ t₂) s) :
    ∃ γ' : ℝ → E, IsIntegralCurveOn γ' (fun _ x ↦ v x) (Icc t₁ t₂) := by
  let (eq := hγ') γ' := extendFrom (Ico t₁ t₂) γ
  use γ'
  intro x hx
  rw [← Ico_union_right ht.le] at hx
  rcases hx with hx | hx
  · apply HasDerivWithinAt.congr_set (s := Ico t₁ t₂)
    · -- make this a lemma
      rw [← nhdsWithin_eq_iff_eventuallyEqSet]
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
  apply HasDerivWithinAt.congr_set (s := Iic t₂)
  · rw [← nhdsWithin_eq_iff_eventuallyEqSet]
    exact (nhdsWithin_Icc_eq_nhdsLE ht).symm
  have : DifferentiableOn ℝ γ' (Ico t₁ t₂) := by
    intro x hx
    rw [hγ']
    exact (hγ x hx).differentiableWithinAt.congr (extendFrom_extends hγ.continuousOn)
      (extendFrom_extends hγ.continuousOn x hx)
  apply hasDerivWithinAt_Iic_of_tendsto_deriv this
  · -- we have the same goal below -> have
    -- here I need a lemma akin to `continuousOn_Ioc_extendFrom_Ioo`
    rw [hγ']
    -- make this a lemma
    have : EqOn (extendFrom (Ico t₁ t₂) γ) (extendFrom (Ioo t₁ t₂) γ) (Icc t₁ t₂) := by
      intro x hx
      rw [← Ioo_union_both ht.le] at hx
      simp only [union_insert, union_singleton, mem_insert_iff] at hx
      rcases hx with hx | hx | hx
      · subst x
        rw [extendFrom_extends hγ.continuousOn t₁ (left_mem_Ico.mpr ht)]
        refine (extendFrom_eq (closure_Ioo ht.ne ▸ left_mem_Icc.mpr ht.le) ?_).symm
        exact ((hγ.continuousOn.continuousWithinAt (left_mem_Ico.mpr ht)).mono
          Ioo_subset_Ico_self).tendsto
      · subst x
        rw [extendFrom, extendFrom]
        refine Filter.limUnder.congr_simp _ _ ?_ γ γ rfl
        -- write a lemma for this

        sorry
      · rw [extendFrom_extends hγ.continuousOn x (Ioo_subset_Ico_self hx),
          extendFrom_extends (hγ.continuousOn.mono Ioo_subset_Ico_self) x hx]
    apply ContinuousWithinAt.congr (f := extendFrom (Ioo t₁ t₂) γ) ?_
      (this.mono Ico_subset_Icc_self) (this (right_mem_Icc.mpr ht.le))
    apply ContinuousWithinAt.mono _ Ico_subset_Icc_self
    apply ContinuousOn.continuousWithinAt _ (right_mem_Icc.mpr ht.le)
    let f := fun u ↦ γ t₁ + ∫ x in t₁..u, v (γ x)
    apply continuousOn_Icc_extendFrom_Ioo (hγ.continuousOn.mono Ioo_subset_Ico_self) (la := γ t₁)
      (lb := f t₂)
    · apply ContinuousWithinAt.tendsto
      apply ContinuousWithinAt.congr_set (s := Ico t₁ t₂)
      · exact hγ.continuousOn.continuousWithinAt (left_mem_Ico.mpr ht)
      rw [← nhdsWithin_eq_iff_eventuallyEqSet]
      -- lemma
      sorry
    -- should probably make some version of this a lemma
    suffices EqOn γ f (Ico t₁ t₂) by
      apply Filter.Tendsto.congr' (f₁ := f)
      · rw [Filter.eventuallyEq_iff_exists_mem]
        use Ico t₁ t₂, Ico_mem_nhdsLT ht
        exact this.symm
      apply ContinuousWithinAt.tendsto
      unfold f
      refine ContinuousWithinAt.const_add ?_ (γ t₁)
      apply ContinuousWithinAt.mono ?_ Iio_subset_Iic_self
      apply ContinuousWithinAt.congr_set _
        (nhdsWithin_eq_iff_eventuallyEqSet.1 (nhdsWithin_Icc_eq_nhdsLE ht))
      apply ContinuousOn.continuousWithinAt ?_ (right_mem_Icc.mpr ht.le)
      rw [← uIcc_of_le ht.le]
      apply intervalIntegral.continuousOn_primitive_interval
      rw [uIcc_of_le ht.le]
      rw [integrableOn_Icc_iff_integrableOn_Ioo]

      sorry
    intro x hx
    unfold f
    rw [← sub_eq_iff_eq_add']


    sorry

  · exact Ico_mem_nhdsLT ht
  apply Filter.Tendsto.congr' (f₁ := fun x ↦ v (γ' x))
  · apply Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT ht)
    intro x hx
    dsimp only
    rw [← derivWithin_of_mem_nhds (s := Ico t₁ t₂) (Ico_mem_nhds_iff.mpr hx), hγ',
      extendFrom_extends hγ.continuousOn x (Ioo_subset_Ico_self hx),
      derivWithin_congr (extendFrom_extends hγ.continuousOn)
        (extendFrom_extends hγ.continuousOn x (Ioo_subset_Ico_self hx))]
    exact (HasDerivWithinAt.derivWithin (hγ x (Ioo_subset_Ico_self hx))
      ((uniqueDiffOn_Ico t₁ t₂).uniqueDiffWithinAt (Ioo_subset_Ico_self hx))).symm
  · dsimp
    apply ContinuousWithinAt.tendsto
    apply ContinuousWithinAt.congr_set (s := Ico t₁ t₂)
    · apply ContinuousWithinAt.comp
      · have : (γ' t₂) ∈ s := by
          -- make this a lemma
          rw [hγ', extendFrom]

          sorry
        exact hf.continuousOn.continuousWithinAt this
      · -- see above
        sorry
      · intro x hx
        rw [hγ', extendFrom_extends hγ.continuousOn x hx]
        exact hγs hx
    · rw [← nhdsWithin_eq_iff_eventuallyEqSet]
      exact nhdsWithin_Ico_eq_nhdsLT ht
  /-have : EqOn (fun u ↦ v (γ' u)) (derivWithin γ (Ico t₁ t₂)) (Ico t₁ t₂) := by
    intro u hu
    dsimp
    rw [hγ', extendFrom_extends hγ.continuousOn u hu]

    exact ((hγ u hu).derivWithin ((uniqueDiffOn_Ico t₁ t₂).uniqueDiffWithinAt hu)).symm
  have : EqOn (fun u ↦ v (γ' u)) (derivWithin γ (Icc t₁ t₂)) (Ico t₁ t₂) := by
    apply this.trans
    intro u hu
    apply?
    refine derivWithin_of_mem_nhdsWithin ?_ ((uniqueDiffOn_Ico t₁ t₂).uniqueDiffWithinAt hu) ?_
    · rw [mem_nhdsWithin_iff_eventuallyEqSet,
        inter_eq_self_of_subset_left (by exact Ico_subset_Icc_self)]
    ·
      sorry


  have : ∀ u ∈ Ico t₁ t₂, γ' u = ∫ (x : ℝ) in t₁..u, v (γ' x) := by
    intro u hu
    have : EqOn (fun u ↦ v (γ' u)) (derivWithin γ (Ico t₁ t₂)) (uIoo t₁ u) := by
      rw [uIoo_of_le hu.1]
      exact this.mono (Ioo_subset_Ico_self.trans (Ico_subset_Ico_right hu.2.le))
    rw [intervalIntegral.integral_congr_uIoo this]

    sorry
  have : ∀ u ∈ Icc t₁ t₂, γ' u = ∫ (x : ℝ) in t₁..u, v (γ' x) := by

    sorry
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
  · sorry-/
