module

public import Mathlib.Geometry.Manifold.MFDeriv.Tangent
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import CollarNeighbourhoods.ExistsUniqueBoundary

/-! Header -/

@[expose] public section

open scoped Manifold Topology

open Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

-- this doesn't make any sense because we cannot control the preimage
def IsMIntegralCurveAtNew (γ : ℝ → M) (v : (x : M) → TangentSpace% x) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in (𝓝 (γ t₀)).comap γ, HasMFDerivAt% γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

example (γ : ℝ → M) (v : (x : M) → TangentSpace% x) (t₀ : ℝ)
    (ht₀ : I.IsInteriorPoint (γ t₀)) :
    IsMIntegralCurveAtNew γ v t₀ ↔ IsMIntegralCurveAt γ v t₀ := by
  constructor
  · unfold IsMIntegralCurveAt IsMIntegralCurveAtNew
    simp_rw [Filter.eventually_iff_exists_mem, Filter.mem_comap]
    intro ⟨t, ⟨s, hs, hst⟩, htγ⟩
    refine ⟨t, ?_, htγ⟩
    apply Filter.mem_of_superset _ hst
    refine ((htγ t₀ ?_).mdifferentiableAt ).continuousAt.preimage_mem_nhds hs
    apply hst
    rw [mem_preimage]
    exact mem_of_mem_nhds hs
  · unfold IsMIntegralCurveAt IsMIntegralCurveAtNew
    simp_rw [Filter.eventually_iff_exists_mem]
    intro ⟨t, ht, htγ⟩
    refine ⟨t, ?_, htγ⟩
    --rw [← nhds_induced γ t₀]
    rw [Filter.mem_comap]
    --refine ⟨γ '' t, ?_, ?_⟩

    sorry

def IsRightMIntegralCurveAt (γ : ℝ → M) (v : (x : M) → TangentSpace% x) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝[≥] t₀, HasMFDerivAt[Ici t₀] γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

lemma isRightMIntegralCurveAt_iff (γ : ℝ → M) (v : (x : M) → TangentSpace% x) (t₀ : ℝ) :
    IsRightMIntegralCurveAt γ v t₀ ↔ ∃ s ∈ 𝓝[≥] t₀, IsMIntegralCurveOn γ v s := by
  unfold IsRightMIntegralCurveAt IsMIntegralCurveOn
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨fun ⟨s, hs, hsγ⟩ ↦ ?_, ?_⟩
  · use s, hs
    intro t ht
    apply (hasMFDerivWithinAt_congr_set (t := Ici t₀) ?_).2 (hsγ t ht)


    sorry
  · sorry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s : Set ℝ} (t₀ : ℝ) {x₀ : M}

theorem exists_isMIntegralCurveAt_of_contMDiffAt [CompleteSpace E]
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx : IsInwardPointingMinimal (v x₀)) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsRightMIntegralCurveAt γ v t₀ := by
  -- express the differentiability of the vector field `v` in the local chart
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
    -- use Picard-Lindelöf theorem to extract a solution to the ODE in the local chart
  let f := ((extChartAt I.tangent (⟨x₀, v x₀⟩ : Bundle.TotalSpace E (TangentSpace I))) ∘
    (fun x ↦ ⟨x, v x⟩) ∘ ↑(extChartAt I x₀).symm)
  -- factor out?
  have hf : inwardPointing ℝ (range I) ((extChartAt I x₀) x₀) (f ((extChartAt I x₀) x₀)).2 := by
    rw [isInwardPointing_iff_inwardPointing_extChartAt (n := 1)] at hx
    convert hx
    unfold f
    rw [Function.comp_apply, Function.comp_apply,
      PartialEquiv.left_inv (extChartAt I x₀) (mem_extChartAt_source x₀),
      FiberBundle.extChartAt ⟨x₀, v x₀⟩]
    simp [TangentBundle.trivializationAt_apply x₀ ⟨x₀, v x₀⟩,
      (mdifferentiableAt_extChartAt (mem_chart_source H x₀)).mvfderiv (f := I ∘ (chartAt H x₀))]
    rfl
  obtain ⟨ε, hε, α, hαt₀, hαI⟩ := ContDiffAt.exists_eq_forall_mem_Icc_hasDerivAt₀ I.convex_range
    I.nonempty_interior (x₀ := extChartAt I x₀ x₀)
    (extChartAt_target_subset_range _ <| mem_extChartAt_target x₀) hf hv.snd t₀
  have αcont : ContinuousWithinAt α (Ici t₀) t₀ := by
    apply HasDerivWithinAt.continuousWithinAt
    apply (hαI t₀ ⟨le_refl t₀, (le_add_iff_nonneg_right t₀).2 hε.le⟩).1.congr_set
    rw [← nhdsWithin_eq_iff_eventuallyEqSet,
      nhdsWithin_Icc_eq_nhdsGE ((lt_add_iff_pos_right t₀).2 hε)]
  use (extChartAt I x₀).symm ∘ α, by simp [hαt₀]


  sorry

end
