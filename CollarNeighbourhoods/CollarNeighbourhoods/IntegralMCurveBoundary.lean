module

public import Mathlib.Geometry.Manifold.MFDeriv.Tangent
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import CollarNeighbourhoods.ExistsUniqueBoundary
public import Mathlib.Analysis.ODE.ExistUnique

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

@[to_dual]
theorem nhdsWithin_Icc_eq_nhdsLE' {α : Type u} [TopologicalSpace α] [LinearOrder α]
    [ClosedIicTopology α] {a b c : α} (h : a < c) : 𝓝[Icc a b] c = 𝓝[Iic b] c :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ici_mem_nhds h

-- do `IntegralCurveWithinAt`
def IsRightMIntegralCurveAt (γ : ℝ → M) (v : (x : M) → TangentSpace% x) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝[≥] t₀, HasMFDerivAt[Ici t₀] γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

lemma isRightMIntegralCurveAt_iff {γ : ℝ → M} {v : (x : M) → TangentSpace% x} {t₀ : ℝ} :
    IsRightMIntegralCurveAt γ v t₀ ↔ ∃ s ∈ 𝓝[≥] t₀, IsMIntegralCurveOn γ v s := by
  unfold IsRightMIntegralCurveAt IsMIntegralCurveOn
  rw [Filter.eventually_iff_exists_mem]
  have htt₀ : ∀ t, ∀ i ∈ Ico t₀ t, Ico t₀ t =ᶠ[𝓝 i] Ici t₀ := by
    intro t i hi
    rw [← nhdsWithin_eq_iff_eventuallyEqSet]
    nth_rw 1 [← max_self t₀, ← Ico_inter_Ici]
    refine nhdsWithin_inter_of_mem ?_
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
    use Ioo (t₀ - 1) t, Ioo_mem_nhds (lt_of_lt_of_le (sub_one_lt t₀) hi.1) hi.2
    intro x ⟨⟨_, hxt⟩, hxt₀⟩
    exact ⟨hxt₀, hxt⟩
  refine ⟨fun ⟨s, hs, hsγ⟩ ↦ ?_, fun ⟨s, hs, hsγ⟩ ↦ ?_⟩
  · rw [mem_nhdsGE_iff_exists_Ico_subset] at hs
    obtain ⟨t, ht, hts⟩ := hs
    use Ico t₀ t, Ico_mem_nhdsGE ht
    intro i hi
    exact (hasMFDerivWithinAt_congr_set (htt₀ t i hi)).2 (hsγ i (hts hi))
  · rw [mem_nhdsGE_iff_exists_Ico_subset] at hs
    obtain ⟨t, ht, hts⟩ := hs
    use Ico t₀ t, Ico_mem_nhdsGE ht
    intro i hi
    exact (hasMFDerivWithinAt_congr_set (htt₀ t i hi).symm).2 ((hsγ i (hts hi)).mono hts)

lemma isRightMIntegralCurveAt_iff' {γ : ℝ → M} {v : (x : M) → TangentSpace% x} {t₀ : ℝ} :
    IsRightMIntegralCurveAt γ v t₀ ↔ ∃ t > t₀, IsMIntegralCurveOn γ v (Icc t₀ t) := by
  rw [isRightMIntegralCurveAt_iff]
  constructor
  · intro ⟨s, hs, hsγ⟩
    rw [mem_nhdsGE_iff_exists_Icc_subset] at hs
    obtain ⟨t, ht, hts⟩ := hs
    use t, ht, hsγ.mono hts
  · intro ⟨t, ht, htγ⟩
    use Icc t₀ t, Icc_mem_nhdsGE ht

theorem IsRightMIntegralCurveAt.continuousWithinAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {t₀ : ℝ}
    (hγ : IsRightMIntegralCurveAt γ v t₀) : ContinuousWithinAt γ (Ici t₀) t₀ := by
  have ⟨s, hs, hγ⟩ := isRightMIntegralCurveAt_iff'.mp hγ
  apply (hγ.continuousWithinAt (left_mem_Icc.mpr hs.le)).congr_set
  rw [← nhdsWithin_eq_iff_eventuallyEqSet]
  exact nhdsWithin_Icc_eq_nhdsGE' hs

theorem continuousWithinAt_def {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    {s : Set X} {x : X} : ContinuousWithinAt f s x ↔ ∀ A ∈ 𝓝 (f x), f ⁻¹' A ∈ 𝓝[s] x :=
  Iff.rfl

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s : Set ℝ} (t₀ : ℝ) {x₀ : M}

-- really I think this proof should be split up into a few things:
-- right integral curves are preserved under partial diffeomorphisms
-- and then conclude

set_option backward.isDefEq.respectTransparency false in
theorem exists_isRightMIntegralCurveAt_of_contMDiffAt [CompleteSpace E]
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
  have hcont : ContinuousWithinAt α (Ici t₀) t₀ := by
    apply HasDerivWithinAt.continuousWithinAt
    apply (hαI t₀ ⟨le_refl t₀, (le_add_iff_nonneg_right t₀).2 hε.le⟩).1.congr_set
    rw [← nhdsWithin_eq_iff_eventuallyEqSet,
      nhdsWithin_Icc_eq_nhdsGE ((lt_add_iff_pos_right t₀).2 hε)]
  --have hev : ∀ᶠ x in 𝓝[≥] t₀, α x ∈ range I := by sorry
  have hcont' : ∀ A ∈ 𝓝[range I] (α t₀), α ⁻¹' A ∈ 𝓝[≥] t₀ := by
    intro A hA
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hA
    obtain ⟨u, hu, huα⟩ := hA
    suffices α ⁻¹' u ∈ 𝓝[≥] t₀ by
      apply Filter.mem_of_superset (x := Icc t₀ (t₀ + ε) ∩ α ⁻¹' u)
        (Filter.inter_mem (Icc_mem_nhdsGE ((lt_add_iff_pos_right t₀).mpr hε)) this)
      intro i ⟨hi, hiα⟩
      exact huα ⟨hiα, (hαI i hi).2⟩
    exact hcont hu
  have hnhds : α ⁻¹' ((extChartAt I x₀).target) ∈ 𝓝[≥] t₀ := by
    apply hcont'
    rw [hαt₀]
    exact extChartAt_target_mem_nhdsWithin x₀
  have hα2 : ∀ᶠ t in 𝓝[≥] t₀, HasDerivWithinAt α (((extChartAt I.tangent ⟨x₀, v x₀⟩) ∘
      (fun x ↦ ⟨x, v x⟩ : M → Bundle.TotalSpace E (TangentSpace I)) ∘
      (extChartAt I x₀).symm) (α t)).2 (Icc t₀ (t₀ + ε)) t := by
    rw [Filter.eventually_iff_exists_mem]
    use Icc t₀ (t₀ + ε), Icc_mem_nhdsGE ((lt_add_iff_pos_right t₀).mpr hε)
    intro i hi
    exact (hαI i hi).1
  rw [← eventually_mem_nhdsWithin_iff] at hnhds
  -- obtain a neighbourhood `s` so that the above conditions both hold in `s`
  obtain ⟨s, hs, haux⟩ := (hα2.and hnhds).exists_mem
  use (extChartAt I x₀).symm ∘ α, by simp [hαt₀]
  rw [isRightMIntegralCurveAt_iff]
  use s ∩ Ico t₀ (t₀ + ε), Filter.inter_mem hs (Ico_mem_nhdsGE ((lt_add_iff_pos_right t₀).mpr hε))
  intro t ht
  -- collect useful terms in convenient forms
  let xₜ : M := (extChartAt I x₀).symm (α t) -- `xₜ := γ t`
  have h : HasDerivWithinAt α (s := Icc t₀ (t₀ + ε)) (x := t) <|
    fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I xₜ).symm)
    (range I) (extChartAt I xₜ xₜ) (v xₜ) := (haux t ht.1).1
  rw [← tangentCoordChange_def] at h
  have hf3 : α t ∈ (extChartAt I x₀).target := by
    -- this needs to stay in exactly this shape for some reason
    apply mem_of_mem_nhdsWithin ht.2.1 (haux t ht.1).2
  --have hft1 := mem_preimage.mp <|
  --  mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hcont : ContinuousWithinAt α (Ici t₀) t := by
    apply h.continuousWithinAt.congr_set
    rw [← nhdsWithin_eq_iff_eventuallyEqSet]
    exact nhdsWithin_Icc_eq_nhdsGE' ht.2.2
  have hft1 : (extChartAt I x₀).symm (α t) ∈ (extChartAt I x₀).source :=
    mem_preimage.mp (mem_of_mem_of_subset hf3 (extChartAt I x₀).target_subset_preimage_source)
  have hft2 := mem_extChartAt_source (I := I) xₜ
  refine ⟨?_, ?_⟩
  · apply ((continuousOn_extChartAt_symm _).continuousWithinAt hf3).comp
    · exact hcont.mono <| inter_subset_right.trans Ico_subset_Ici_self
    · intro x hx
      apply mem_of_mem_nhdsWithin hx.2.1 (haux x hx.1).2
  · apply HasDerivWithinAt.hasFDerivWithinAt
    simp only [mfld_simps]
    change HasDerivWithinAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ α) (v xₜ) _ t
    rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2,
      ←  tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
    apply ((extChartAt I x₀).right_inv hf3 ▸
      hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩).comp_hasDerivWithinAt _
      (h.mono (inter_subset_right.trans Ico_subset_Icc_self))
    intro x hx
    exact (hαI x (Ico_subset_Icc_self hx.2)).2

theorem exists_isMRightIntegralCurveAt_of_contMDiffAt_of_isInteriorPoint [CompleteSpace E]
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx : I.IsInteriorPoint x₀) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsRightMIntegralCurveAt γ v t₀ :=
  exists_isRightMIntegralCurveAt_of_contMDiffAt _ hv
    (isInwardPointing_of_isInteriorPoint (n := 1) hx)

variable {t₀}


open NNReal in
/-- Local uniqueness of ODE solutions. -/
theorem ODE_solution_unique_right_of_eventually {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0} {f g : ℝ → E} {t₀ : ℝ}
    (hv : ∀ᶠ t in 𝓝[≥] t₀, LipschitzOnWith K (v t) (s t))
    (hf : ∀ᶠ t in 𝓝[≥] t₀, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t)
    (hg : ∀ᶠ t in 𝓝[≥] t₀, HasDerivAt g (v t (g t)) t ∧ g t ∈ s t)
    (heq : f t₀ = g t₀) : f =ᶠ[𝓝[≥] t₀] g := by
  obtain ⟨s, hs, h⟩ := Filter.eventually_iff_exists_mem.mp (hv.and (hf.and hg))
  rw [mem_nhdsGE_iff_exists_Icc_subset] at hs
  obtain ⟨t, htt₀, ht⟩ := hs
  rw [Filter.eventuallyEq_iff_exists_mem]
  use Icc t₀ t, Icc_mem_nhdsGE htt₀
  apply ODE_solution_unique_of_mem_Icc_right
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry

/-- Local integral curves are unique.

If a $C^1$ vector field `v` admits two local integral curves `γ γ' : ℝ → M` at `t₀` with
`γ t₀ = γ' t₀`, then `γ` and `γ'` agree on some open interval containing `t₀`. -/
theorem isMIntegralCurveAt_eventuallyEq_of_contMDiffAt
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsRightMIntegralCurveAt γ v t₀) (hγ' : IsRightMIntegralCurveAt γ' v t₀)
    (h : γ t₀ = γ' t₀) :
    γ =ᶠ[𝓝[≥] t₀] γ' := by
  -- first define `v'` as the vector field expressed in the local chart around `γ t₀`
  -- this is basically what the function looks like when `hv` is unfolded
  set v' : E → E := fun x ↦
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀) ((extChartAt I (γ t₀)).symm x)
      (v ((extChartAt I (γ t₀)).symm x)) with hv'
  -- extract a set `s` on which `v'` is Lipschitz
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  have := hv.snd.exists_lipschitzOnWith I.convex_range
  obtain ⟨K, s, hs, hlip⟩ := hv.snd.exists_lipschitzOnWith I.convex_range
  have hlip (t : ℝ) : LipschitzOnWith K ((fun _ ↦ v') t) ((fun _ ↦ s) t) := hlip
  -- internal lemmas to reduce code duplication
  have hsrc {g} (hg : IsRightMIntegralCurveAt g v t₀) :
    ∀ᶠ t in 𝓝[≥] t₀, g ⁻¹' (extChartAt I (g t₀)).source ∈ 𝓝[Ici t₀] t :=
      eventually_mem_nhdsWithin_iff.mpr <| continuousWithinAt_def.mp hg.continuousWithinAt _
        (extChartAt_source_mem_nhds (g t₀))
  have hmem {g : ℝ → M} {t} (htt₀ : t₀ ≤ t)
      (ht : g ⁻¹' (extChartAt I (g t₀)).source ∈ 𝓝[Ici t₀] t) :
      g t ∈ (extChartAt I (g t₀)).source := by
    apply mem_preimage.mp
    exact mem_of_mem_nhdsWithin htt₀ ht
  have heq {g} (hg : IsRightMIntegralCurveAt g v t₀) :
      g =ᶠ[𝓝[≥] t₀] (extChartAt I (g t₀)).symm ∘ ↑(extChartAt I (g t₀)) ∘ g := by
    refine (hsrc hg).mp <| eventually_nhdsWithin_of_forall ?_
    intro t htt₀ ht
    rw [Function.comp_apply, Function.comp_apply, PartialEquiv.left_inv _ (hmem htt₀ ht)]
  -- main proof
  suffices (extChartAt I (γ t₀)) ∘ γ =ᶠ[𝓝[≥] t₀] (extChartAt I (γ' t₀)) ∘ γ' from
    (heq hγ).trans <| (this.fun_comp (extChartAt I (γ t₀)).symm).trans (h ▸ (heq hγ').symm)

  sorry

end
