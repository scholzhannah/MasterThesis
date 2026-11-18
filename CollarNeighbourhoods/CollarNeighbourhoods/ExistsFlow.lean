module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Geometry.Manifold.IntegralCurve.Transform
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import CollarNeighbourhoods.ExistsUniqueBoundary
public import CollarNeighbourhoods.Flows
import Mathlib.Geometry.Manifold.Notation

public section

open scoped Topology
open scoped Manifold Topology

open Function Manifold Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s s' : Set ℝ} (t₀ : ℝ) {x₀ : M}

set_option backward.isDefEq.respectTransparency false in
theorem exists_mem_nhds_flowOn {v : (x : H) → TangentSpace I x} {x₀ : H} [CompleteSpace E]
    (hv1 : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I H)) x₀)
    (hx2 : IsInwardPointingMinimal (v x₀)) :
    ∃ u ∈ 𝓝 x₀, ∃ ε > (0 : ℝ), ∃ γ : H → ℝ → H, IsFlowOn t₀ γ (u ×ˢ (Ico t₀ (t₀ + ε))) v := by
  let v' : E → E := fun x ↦ mvfderiv I I (I.symm x) (v (I.symm x))
  have hv' : inwardPointing (range I) (I x₀) (v' (I x₀)) := by
    rw [isInwardPointing_iff_inwardPointing_extChartAt (n := 1)] at hx2
    unfold v'
    rw [I.left_inv x₀]
    simpa [chartAt_self_eq] using hx2
  have hv'' : ContDiffWithinAt ℝ 1 v' (range I) (I x₀) := by
    simp only [contMDiffAt_iff, extChartAt_coe_symm x₀, chartAt_self_eq,
      OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply H, id_comp,
      extChartAt_self_apply ℝ] at hv1
    convert hv1.2.snd using 1
    ext x
    rw [comp_apply, comp_apply, FiberBundle.extChartAt ⟨x₀, v x₀⟩, PartialEquiv.trans_apply]
    simp [v', I.mvfderiv_I]
    -- this proof is clearly def-eq abusy somewhere
    rfl
  have := ContDiffWithinAt.exists_mem_closedBall_eq_forall_mem_Ico_hasDerivAt
    (f := v') (x₀ := I x₀)
    I.convex_range I.isClosed_range I.nonempty_interior (mem_range_self x₀) hv' hv'' t₀
  obtain ⟨r, hr, ε, hε, α, hα⟩ := this
  use I ⁻¹' (Metric.closedBall (I x₀) r)
  constructor
  · have := extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (x' := x₀) (x := x₀) (I := I)
      (s := Metric.closedBall (I x₀) r) (mem_extChartAt_source x₀)
    simp only [extChartAt, OpenPartialHomeomorph.extend, chartAt_self_eq,
      OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans,
      ModelWithCorners.toPartialEquiv_coe] at this
    apply this
    apply mem_nhdsWithin_of_mem_nhds
    exact Metric.closedBall_mem_nhds (I x₀) hr
  use ε, hε, fun x ↦ I.symm ∘ α (I x)
  constructor
  · intro p
    by_cases hp : I p ∈ Metric.closedBall (I x₀) r
    · simp only [comp_apply, mem_prod, mem_preimage, hp, true_and, ofPred_mem_eq]
      intro t ht
      obtain ⟨hα1, hα2⟩ := hα (I p) ⟨hp, mem_range_self _⟩
      obtain ⟨hα2', hα3⟩ := hα2 t (Ico_subset_Icc_self ht)
      have :
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v ((fun x ↦ I.symm (α (I p) x)) t))) =
          (ContinuousLinearMap.id ℝ (TangentSpace (H := H) I _)) ∘SL
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v' (α (I p) t))) := by
        apply ContinuousLinearMap.ext_ring
        simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul,
          ContinuousLinearMap.id_comp]
        -- fixing some defeq issue
        --change _ = ((1 : ℝ →L[ℝ] ℝ) 1) • (v' (α (I p) t))
        simp [v', I.mvfderiv_I]
        rfl
      rw [this]
      apply (I.hasMFDerivWithinAt_symm hα3).comp
      · rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
        exact (hα2'.mono Ico_subset_Icc_self).hasFDerivWithinAt.hasMFDerivWithinAt
      · intro i hi
        exact (hα2 i (Ico_subset_Icc_self hi)).2
    simp only [comp_apply, mem_prod, mem_preimage, hp, mem_Ico, false_and, ofPred_false]
    exact fun p hp ↦  hp.elim
  · intro p hp
    simp [hα (I p) ⟨hp.left.choose_spec, mem_range_self p⟩]

-- from PR 26394 by Winston Yin
theorem Filter.eventually_prod_iff_exists_mem {p : α × β → Prop} :
    (∀ᶠ x in f ×ˢ g, p x) ↔ ∃ s ∈ f, ∃ t ∈ g, ∀ x ∈ s, ∀ y ∈ t, p ⟨x, y⟩ := by
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨fun ⟨st, hst, h⟩ ↦ ?_, fun ⟨s, hs, t, ht, h⟩ ↦ ?_⟩
  · have ⟨s, hs, t, ht, hp⟩ := Filter.mem_prod_iff.mp hst
    exact ⟨s, hs, t, ht, fun x hx y hy ↦ h _ <| hp ⟨hx, hy⟩⟩
  · exact ⟨s ×ˢ t, Filter.prod_mem_prod hs ht, fun ⟨x, y⟩ ⟨hx, hy⟩ ↦ h x hx y hy⟩

theorem ContinuousWithinAt.comp₂ {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] [TopologicalSpace δ] {f : β × γ → δ} {g : α → β} {h : α → γ} {x : α}
    {t : Set (β × γ)} {s : Set α} (hst : MapsTo (fun x ↦ (g x, h x)) s t)
    (hf : ContinuousWithinAt f t (g x, h x)) (hg : ContinuousWithinAt g s x)
    (hh : ContinuousWithinAt h s x) :
    ContinuousWithinAt (fun x ↦ f (g x, h x)) s x :=
  ContinuousWithinAt.comp hf (hg.prodMk_nhds hh) hst

set_option backward.isDefEq.respectTransparency false in
lemma hasDerivAt_extChartAt_comp_extChartAt_comp_of_hasDerivAt_tangentCoordChange
    {x₀ : M} {f : ℝ → E} {t : ℝ} {v : TangentSpace I ((extChartAt I x₀).symm (f t))}
    {ε : ℝ} (hε : MapsTo f (Ico t₀ (t₀ + ε)) (range I))
    (hmem : f t ∈ (extChartAt I x₀).target)
    (hf : let xₜ : M := (extChartAt I x₀).symm (f t)
      HasDerivWithinAt f (tangentCoordChange I xₜ x₀ xₜ v) (Ico t₀ (t₀ + ε)) t) :
    let xₜ : M := (extChartAt I x₀).symm (f t)
    HasDerivWithinAt (((extChartAt I xₜ) ∘ (extChartAt I x₀).symm) ∘ f) v (Ico t₀ (t₀ + ε)) t := by
  dsimp only
  let xₜ : M := (extChartAt I x₀).symm (f t)
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hmem (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source (I := I) xₜ
  rw [← tangentCoordChange_self (I := I) (v := v) hft2,
    ← tangentCoordChange_comp ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivWithinAt.comp_hasDerivWithinAt _ _ hf (t := range I)
  · exact hε
  · nth_rw 2 [← (extChartAt I x₀).right_inv hmem]
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

set_option backward.isDefEq.respectTransparency false in
/-- Let `f : ℝ → E` and `v` be a tangent vector field on `M`. This lemma gives what `f'(t)` needs to
be in the model space in order for $(\phi_{x_0}^{-1} ∘ f)'(t) = v(\phi_{x_0}^{-1}(f(t))$ to hold
on the manifold. -/
lemma hasMFDerivAt_extChartAt_comp_of_hasDerivAt {ε : ℝ} {v : (x : M) → TangentSpace I x} {x₀ : M}
    {f : ℝ → E} {t : ℝ} (hε : MapsTo f (Ico t₀ (t₀ + ε)) (range I))
    (hmem : f t ∈ (extChartAt I x₀).target)
    (hf : HasDerivWithinAt f (((extChartAt I.tangent (⟨x₀, v x₀⟩ : TangentBundle I M)) ∘
      (fun x ↦ ⟨x, v x⟩) ∘ (extChartAt I x₀).symm) (f t)).2 (Ico t₀ (t₀ + ε)) t) :
    HasMFDerivAt[Ico t₀ (t₀ + ε)] ((extChartAt I x₀).symm ∘ f) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((extChartAt I x₀).symm (f t)))) := by
  let xₜ : M := (extChartAt I x₀).symm (f t)
  change HasDerivWithinAt f (tangentCoordChange I xₜ x₀ xₜ (v xₜ)) (Ico t₀ (t₀ + ε)) t at hf
  refine ⟨continuousAt_extChartAt_symm'' hmem |>.comp_continuousWithinAt (x := t)
    hf.continuousWithinAt, HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps]
  exact hasDerivAt_extChartAt_comp_extChartAt_comp_of_hasDerivAt_tangentCoordChange _ hε hmem hf

theorem exists_mem_nhds_isFlowOn_Ioo_of_contMDiffAt' [CompleteSpace E]
    (hv1 : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx2 : IsInwardPointingMinimal (v x₀)) :
    ∃ u ∈ 𝓝 x₀, ∃ ε > (0 : ℝ), ∃ γ : M → ℝ → M, IsFlowOn t₀ γ (u ×ˢ (Ico t₀ (t₀ + ε))) v := by
  have hv := (contMDiffAt_iff.mp hv1).2
  let f := ((extChartAt I.tangent (⟨x₀, v x₀⟩ : Bundle.TotalSpace E (TangentSpace I))) ∘
    (fun x ↦ ⟨x, v x⟩) ∘ ↑(extChartAt I x₀).symm)
  have hf : inwardPointing (range I) ((extChartAt I x₀) x₀) (f ((extChartAt I x₀) x₀)).2 := by
    rw [isInwardPointing_iff_inwardPointing_extChartAt (n := 1)] at hx2
    convert hx2
    unfold f
    rw [Function.comp_apply, Function.comp_apply,
      PartialEquiv.left_inv (extChartAt I x₀) (mem_extChartAt_source x₀),
      FiberBundle.extChartAt ⟨x₀, v x₀⟩]
    simp [TangentBundle.trivializationAt_apply x₀ ⟨x₀, v x₀⟩,
      (mdifferentiableAt_extChartAt (mem_chart_source H x₀)).mvfderiv (f := I ∘ (chartAt H x₀))]
    rfl
  have := hv.snd
  obtain ⟨α, hα⟩ :=
    ContDiffWithinAt.exists_eventually_eq_hasDerivWithinAt_continuousWithinAt
    I.convex_range I.isClosed_range I.nonempty_interior (x₀ := extChartAt I x₀ x₀)
    (f := fun x ↦ (f x).2)
    (extChartAt_target_subset_range _ <| mem_extChartAt_target x₀) hf hv.snd t₀
  simp only [Filter.eventually_and] at hα
  obtain ⟨hα1, hα2, hα3, hα4⟩ := hα
  -- extract explicit product neighbourhoods for the continuity condition
  rw [nhdsWithin_prod_eq, Filter.eventually_prod_iff_exists_mem] at hα4
  obtain ⟨u0, hu0, s0, hs0, hα4'⟩ := hα4
  have huox₀ : extChartAt I x₀ x₀ ∈ u0 := mem_of_mem_nhdsWithin (by exact mem_range_self _) hu0
  have hs0t₀ : t₀ ∈ s0 := mem_of_mem_nhdsWithin self_mem_Ici hs0
  have hcont' : ∀ A ∈ 𝓝[range I] (α (extChartAt I x₀ x₀, t₀)), α ⁻¹' A ∈
      𝓝[(range I) ×ˢ (Ici t₀)] (extChartAt I x₀ x₀, t₀) := by
    intro A hA
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hA
    obtain ⟨u, hu, huα⟩ := hA
    suffices α ⁻¹' u ∈ 𝓝[(range I) ×ˢ (Ici t₀)] (extChartAt I x₀ x₀, t₀) by
      rw [Filter.eventually_iff_exists_mem] at hα3
      obtain ⟨v, hv, hvI⟩ := hα3
      apply Filter.mem_of_superset (Filter.inter_mem this hv)
      intro x ⟨hx1, hx2⟩
      exact huα ⟨hx1, hvI x hx2⟩
    exact hα4' _ huox₀ t₀ hs0t₀ hu
  have hnhds : α ⁻¹' ((extChartAt I x₀).target) ∈
      𝓝[(range I) ×ˢ (Ici t₀)] (extChartAt I x₀ x₀, t₀) := by
    apply hcont'
    rw [hα1.self_of_nhdsWithin (by simp)]
    exact extChartAt_target_mem_nhdsWithin x₀
  have hα5 :  ∀ᶠ (x : E × ℝ) in 𝓝[range I ×ˢ Ici t₀] ((extChartAt I x₀) x₀, t₀),
      α x ∈ (extChartAt I x₀).target := by
    rw [Filter.eventually_iff_exists_mem]
    use α ⁻¹' (extChartAt I x₀).target, hnhds
    exact fun x hx ↦ hx
  rw [nhdsWithin_prod_eq] at hα1 hα2 hα5
  obtain ⟨u, hu, s, hs, hf⟩ :=
    Filter.eventually_prod_iff_exists_mem.mp (hα1.and (hα2.and hα5))
  have ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.mp (Filter.inter_mem hs0 hs)
  rw [Real.ball_eq_Ioo t₀ ε, ← Iio_inter_Ioi, inter_assoc,
    inter_eq_self_of_subset_right (s := Ioi (t₀ - ε))
    (by exact fun i hi ↦  lt_of_lt_of_le (sub_lt_self t₀ hε) hi), Iio_inter_Ici] at hεs
  let U := (extChartAt I x₀) ⁻¹' (u0 ∩ u) ∩ (extChartAt I x₀).source
  let γ (xt : M × ℝ) := (extChartAt I x₀).symm (α (extChartAt I x₀ xt.1, xt.2))
  use U
  constructor
  · refine Filter.inter_mem ?_ (extChartAt_source_mem_nhds x₀)
    rw [← nhdsWithin_univ x₀]
    apply (continuousAt_extChartAt _).continuousWithinAt.preimage_mem_nhdsWithin'
    refine (nhdsWithin_mono _ ?_) (Filter.inter_mem hu0 hu)
    rw [image_univ, range_subset_iff]
    exact fun _ ↦ mem_range_self _
  · use ε, hε, curry γ
    constructor
    · intro p t ⟨hp, ht⟩
      simp only [curry_apply, mem_prod, hp, mem_Ico, true_and, γ]
      apply hasMFDerivAt_extChartAt_comp_of_hasDerivAt
      · intro t ht
        exact extChartAt_target_subset_range x₀ (hf (extChartAt I x₀ p) hp.1.2 t (hεs ht).2).2.2
      · exact (hf (extChartAt I x₀ p) hp.1.2 t (hεs ht).2).2.2
      · simp only [comp_apply]
        have := (hf (extChartAt I x₀ p) hp.1.2 t (hεs ht).2).2.1
        apply this.congr_set
        rw [← nhdsWithin_eq_iff_eventuallyEqSet]
        exact (nhdsWithin_Ico_eq_nhdsGE' ht.2).symm
    · intro p ⟨_, hp, _⟩
      simp_rw [curry_apply, γ,
        (hf (extChartAt I x₀ p) hp.1.2 t₀ (mem_of_mem_nhdsWithin (self_mem_Ici) hs)).1,
        PartialEquiv.left_inv (extChartAt I x₀) hp.2]


/-
/-- Existence of local flows for a $C^1$ vector field at interior points of a $C^1$ manifold. -/
theorem exists_mem_nhds_isMIntegralCurveOn_Ioo_of_contMDiffAt' [CompleteSpace E]
    (hv1 : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx2 : ∀ x, IsInwardPointingMinimal (v x)) :
    ∃ u ∈ 𝓝 x₀, ∃ ε > (0 : ℝ), ∃ γ : M → ℝ → M, IsFlowOn t₀ γ (u ×ˢ (Ico t₀ (t₀ + ε))) v := by
  let v' := mfderiv% (chartAt H x₀) x₀ ∘ v ∘ (chartAt H x₀).symm
  have hv1' : CMDiffAt 1 (fun x ↦ (⟨x, v' x⟩ : TangentBundle I H)) (chartAt H x₀ x₀) := by
    unfold v'
    rw [contMDiffAt_iff_target]
    constructor
    · unfold v'


      rw [← (tangentBundleModelSpaceHomeomorph (I := I)).comp_continuousAt_iff, comp_def,
        tangentBundleModelSpaceHomeomorph_coe, Bundle.TotalSpace.toProd]

      apply continuousAt_id.prodMk
      --unfold v'
      simp only
      apply ContinuousAt.comp
      · sorry
      · apply ContinuousAt.comp
        · rw [(chartAt H x₀).left_inv (mem_chart_source H x₀)]
          rw [contMDiffAt_iff] at hv1
          replace hv1 := hv1.1
          rw [FiberBundle.continuousAt_totalSpace E fun x ↦ ⟨x, v x⟩] at hv1
          simp at hv1
          --rw [FiberBundle.continuousAt_section E x₀] at hv1

          sorry
        · sorry
    · sorry
  have := exists_mem_nhds_flowOn t₀ hv1'
  sorry-/
