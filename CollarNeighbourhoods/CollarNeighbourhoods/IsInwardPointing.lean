/-
Copyright (c) 2026 Hannah Scholz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Scholz
-/
module

public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Geometry.Convex.Cone.Basic
public import CollarNeighbourhoods.LineDeriv

/-! Header-/

@[expose] public section

open Set Function Filter Module EuclideanSpace
open scoped Topology Manifold ContDiff

section

-- this is how to say that `M` is a topological manifold
variable {M H : Type*} [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]

-- this is how we say that `M` is a smooth manifold
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

section

variable {n : ℕ} [NeZero n]

-- this is bad because you cannot pull these through charts very well
-- this is probably still correct
def IsInwardPointingTry5 {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (f : M → ℝ) (_ : CMDiff ∞ f) (_ : ∀ x ∈ I.interior M, 0 < f x)
    (_ : ∀ x ∈ I.boundary M, f x = 0), 0 < d% f p v

-- maybe use nbhs instead
-- try making it a structure
def IsInwardPointingTry5Local {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (f : M → ℝ) (U : Set M) (_ : IsOpen U) (_ : p ∈ U) (_ : CMDiff[U] ∞ f)
    (_ : ∀ x ∈ I.interior M ∩ U, 0 < f x)
    (_ : ∀ x ∈ I.boundary M ∩ U, f x = 0), 0 < d% f p v

lemma modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) :
    HasMFDerivAt[{ x : EuclideanSpace ℝ (Fin n) | 0 ≤ x 0 }] (𝓡∂ n).symm
      ((𝓡∂ n) p)
      -- this line below isn't type correct at all
      -- I think writing this as the derivative of the model with corners is already the only
      -- sensible way to write this
      -- why is this okay for `ModelWithCorners.hasMFDerivAt`?
      (ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) ((𝓡∂ n) p))) := by
  refine ⟨(𝓡∂ n).continuousOn_symm.continuousWithinAt (by simp), ?_⟩
  apply HasFDerivWithinAt.congr (f := id)
  · apply HasFDerivAt.hasFDerivWithinAt
    exact hasFDerivAt_id p.val
  · intro x hx
    simp_all [modelWithCornersEuclideanHalfSpace_symm_apply,
      modelWithCornersEuclideanHalfSpace_apply, -modelWithCornersEuclideanHalfSpace_toFun,
      chartAt_self_eq]
  · rw [modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff] at hp
    have : (update ((𝓡∂ n) p).ofLp 0 0) = ((𝓡∂ n) p).ofLp := by
      rw [update_eq_self_iff, hp]
    simp [modelWithCornersEuclideanHalfSpace_symm_apply,
      hp, this, -modelWithCornersEuclideanHalfSpace_toFun]
    rfl

lemma modelWithCornersEuclideanHalfSpace_symm_mDifferentialbleWithinAt {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) :
    MDiffAt[{ x : EuclideanSpace ℝ (Fin n) | 0 ≤ x 0 }] (𝓡∂ n).symm p.val :=
  HasMFDerivWithinAt.mdifferentiableWithinAt
    (modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt hp)

section

variable {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type u_4}
  [TopologicalSpace M] [ChartedSpace H M] {F : Type u_8} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : M → F) (x : M) {s t : Set M}

theorem mvfderivWithin_subset (st : s ⊆ t) (hs : UniqueMDiffAt[s] x) (h : MDiffAt[t] f x) :
    d[s] f x = d[t] f x :=
  mfderivWithin_subset st hs h

theorem mvfderivWithin_inter (ht : t ∈ 𝓝 x) : d[s ∩ t] f x = d[s] f x :=
  mfderivWithin_inter ht

theorem mvfderivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : d[s] f x = d% f x :=
  mfderivWithin_of_mem_nhds h

lemma mvfderivWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) : d[s] f x = d% f x :=
  mfderivWithin_of_isOpen hs hx

end

-- I need to write a lemma that says that an inward pointing vector `v` in the model space is one
-- where there is `ε > 0` s.t. `ε * v` is in the interior. Maybe we actually need to require this
-- for an interval
-- Maybe we can then simplify the proof of `prop541euclideanTry5Local` with that
-- or it will get even more complicated

lemma exists_of_inwardPointing {p : H} (hp : I.IsBoundaryPoint p) (v : TangentSpace I p) :
    IsInwardPointingTry5Local v ↔ ∃ ε > 0, ∀ i ∈ Ico 0 ε,
      I p + i • d% I p v ∈ interior I.target := by
  constructor
  · sorry
  · intro h
    unfold IsInwardPointingTry5Local
    -- take some sort of bump function
    -- this is very wrong...
    use fun x ↦ ‖I p - I x‖, univ, isOpen_univ, mem_univ p
    refine ⟨?_, ?_⟩
    · rw [contMDiffOn_univ]
      apply ContMDiff.comp (g := fun x ↦ ‖I p - x‖) (f := I) ?_ I.contMDiff
      rw [contMDiff_iff_contDiff]
      sorry
    · sorry

lemma prop541euclideanTry5Local {p : EuclideanHalfSpace n} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry5Local v ↔ 0 < ((d% (𝓡∂ n) p) v).ofLp 0 := by
  constructor
  · intro ⟨f, U, hU, hUp, hf1, hf2, hf3, hf4⟩
    by_contra! hv
    have h1 : MDerivAlongWithin f (-v) (AlongFunPreimIn (-v) U) 0 1 < 0 := by
      rw [MDerivAlongWithin_alongFunPreimIn hp _ (by simpa) _ _ (hU.mem_nhds_iff.mpr hUp)]
      · rw [MDerivAlong_eq hp _ (by simpa) _]
        · simpa
        · -- reused below -> have
          apply (hf1.mdifferentiableOn (ne_of_beq_false rfl)).mdifferentiableAt
          exact hU.mem_nhds_iff.mpr hUp
      · apply (hf1.mdifferentiableOn (ne_of_beq_false rfl)).mdifferentiableAt
        exact hU.mem_nhds_iff.mpr hUp
    have h2 : 0 ≤ MDerivAlongWithin f (-v) (AlongFunPreimIn (-v) U) 0 1 := by
      apply IsLocalMinOn.mderivAlongWithin_nonneg_alongFunPreimIn hp
      · simpa
      · apply IsMinOn.localize
        intro x hx
        by_cases h : (𝓡∂ n).IsBoundaryPoint x
        · simp [hf3 p ⟨hp, hUp⟩, hf3 x ⟨h, hx⟩]
        · rw [← ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint x] at h
          simp [hf3 p ⟨hp, hUp⟩, (hf2 x ⟨h, hx⟩).le]
      · exact hU.mem_nhds_iff.mpr hUp
    exact not_lt_of_ge h2 h1
  · intro h
    have h1 : ∀ x ∈ (𝓡∂ n).interior (EuclideanHalfSpace n), 0 < (proj 0 ∘ 𝓡∂ n) x := by
      intro x hx
      simpa [modelWithCornersEuclideanHalfSpace_apply,
        modelWithCornersEuclideanHalfSpace_interior_eq] using hx
    have h2 : ∀ x ∈ (𝓡∂ n).boundary (EuclideanHalfSpace n), (proj 0 ∘ 𝓡∂ n) x = 0 := by
      intro x hx
      simpa [modelWithCornersEuclideanHalfSpace_apply,
        modelWithCornersEuclideanHalfSpace_boundary_eq] using hx
    use proj 0 ∘ 𝓡∂ n, univ, isOpen_univ, mem_univ p,
      (ContDiff.comp_contMDiff (by fun_prop) (𝓡∂ n).contMDiff).contMDiffOn
    simp only [inter_univ]
    refine ⟨h1, h2, ?_⟩
    unfold mvfderiv
    simp only [Function.comp_apply]
    have h3 : MDiffAt (proj 0 : StrongDual ℝ (EuclideanSpace ℝ (Fin n))) ((𝓡∂ n) p) := by
      apply DifferentiableAt.mdifferentiableAt
      fun_prop
    rw [mfderiv_comp p h3 (𝓡∂ n).mdifferentiableAt,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.mfderiv_eq (proj 0 : StrongDual ℝ (EuclideanSpace ℝ (Fin n)))]
    exact h

omit [IsManifold I ∞ M] in
lemma PartialDiffeomorph.isInwardPointingTry5Local_apply {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H M'] (p : M) (v : TangentSpace I p)
    (f : PartialDiffeomorph I I M M' ∞) (hpf : p ∈ f.source) (hv : IsInwardPointingTry5Local v) :
    IsInwardPointingTry5Local (mfderiv% f p v) := by
  obtain ⟨g, U, hU, hUp, hg1, hg2, hg3, hg4⟩ := hv
  use g ∘ f.symm, (f '' (f.source ∩ U)), f.isOpen_image_source_inter hU,
    mem_image_of_mem f ⟨hpf, hUp⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : ContMDiffOn I I ∞ f.symm (f '' (f.source ∩ U)) := by
      apply f.contMDiffOn_invFun.mono
      exact subset_trans (image_mono inter_subset_left) f.image_source_subset
    apply hg1.comp h
    rw [f.image_source_inter_eq' U]
    exact inter_subset_right
  · intro x ⟨hx1, hx2⟩
    --maybe the set should already be stated like what the rewrite does?
    rw [f.image_source_inter_eq' U] at hx2
    apply hg2
    refine ⟨?_, hx2.2⟩
    change I.IsInteriorPoint (f.symm x)
    rw [← (f.symm.isLocalDiffeomorphAt I I ∞ hx2.1).isInteriorPoint_iff (ne_of_beq_false rfl)]
    exact hx1
  · intro x ⟨hx1, hx2⟩
    rw [f.image_source_inter_eq' U] at hx2
    apply hg3
    refine ⟨?_, hx2.2⟩
    change I.IsBoundaryPoint (f.symm x)
    rw [← (f.symm.isLocalDiffeomorphAt I I ∞ hx2.1).isBoundaryPoint_iff (ne_of_beq_false rfl)]
    exact hx1
  · unfold mvfderiv
    have hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g (f.symm (f p)) := by
      rw [f.symm_toPartialEquiv, f.left_inv hpf]
      exact (hg1.mdifferentiableOn (ne_of_beq_false rfl) p hUp).mdifferentiableAt
        (hU.mem_nhds_iff.mpr hUp)
    have hf1 : MDifferentiableAt I I f.symm (f p) := by
      apply f.symm.mdifferentiableAt (ne_of_beq_false rfl)
      simp [f.map_source' hpf]
    have hf2 : MDifferentiableAt I I f p := f.mdifferentiableAt (ne_of_beq_false rfl) hpf
    -- this literally always gives defeq issues...
    -- how do I fix this?
    rw [mfderiv_comp (f p) hg hf1, ← ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_apply, ← mfderiv_comp_apply p hf1 hf2 v,
      ← mfderivWithin_of_isOpen f.open_source hpf, mfderivWithin_congr (f := id)
      (f₁ := f.symm ∘ f) f.leftInvOn (f.left_inv hpf), mfderivWithin_of_isOpen f.open_source hpf,
      mfderiv_id, comp_apply, PartialDiffeomorph.symm_toPartialEquiv f, f.left_inv hpf]
    exact hg4

omit [IsManifold I ∞ M] in
lemma PartialDiffeomorph.isInwardPointing_iff {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    (p : M) (v : TangentSpace I p) (f : PartialDiffeomorph I I M M' ∞)
    (hp : p ∈ f.source) :
    IsInwardPointingTry5Local v ↔ IsInwardPointingTry5Local (mfderiv% f p v) := by
  constructor
  · intro hv
    exact f.isInwardPointingTry5Local_apply p v hp hv
  · have : v = (mfderiv% f.symm (f p)) ((mfderiv% f p) v) := by
      rw [← mfderiv_comp_apply p ?_ ?_ v]
      · rw [← mfderivWithin_of_isOpen f.open_source hp]
        rw [mfderivWithin_congr_of_mem (f := id) ?_ hp]
        · rw [mfderivWithin_of_isOpen f.open_source hp, comp_apply, mfderiv_id]
          rfl
        exact f.leftInvOn
      · apply f.symm.mdifferentiableAt (ne_of_beq_false rfl)
        simp [f.map_source' hp]
      · exact f.mdifferentiableAt (ne_of_beq_false rfl) hp
    intro hv
    rw [this]
    nth_rw 1 [← f.left_inv hp]
    apply f.symm.isInwardPointingTry5Local_apply _ ((mfderiv% f p) v) ?_ hv
    simp [f.map_source' hp]

lemma isLocalDiffeomorphAt_iff {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type u_3} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {H₁ : Type u_5}
    [TopologicalSpace H₁] {H₂ : Type u_6} [TopologicalSpace H₂] (I : ModelWithCorners 𝕜 E H₁)
    (J : ModelWithCorners 𝕜 F H₂) {M : Type u_8} [TopologicalSpace M] [ChartedSpace H₁ M]
    {N : Type u_9}
    [TopologicalSpace N] [ChartedSpace H₂ N] (n : WithTop ℕ∞) (f : M → N) (x : M) :
    IsLocalDiffeomorphAt I J n f x ↔
      ∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source := by
 sorry

omit [IsManifold I ∞ M] in
lemma IsLocalDiffeomorphAt.isInwardPointing_iff {M' : Type*} [TopologicalSpace M']
    [ChartedSpace H M'] (p : M) (v : TangentSpace I p) (f : M → M')
    (hf : IsLocalDiffeomorphAt I I ∞ f p) :
    IsInwardPointingTry5Local v ↔ IsInwardPointingTry5Local (mfderiv% f p v) := by
  rw [isLocalDiffeomorphAt_iff] at hf
  obtain ⟨φ, hpφ, hφf⟩ := hf
  rw [← mfderivWithin_of_isOpen φ.open_source hpφ, mfderivWithin_congr_of_mem hφf hpφ,
    mfderivWithin_of_isOpen φ.open_source hpφ, φ.isInwardPointing_iff p v hpφ, (hφf hpφ)]

lemma isInwardPointing_iff_of_mem_maximalAtlas {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p)
    (f : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (hpf : p ∈ f.source) (hf : f ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M) :
    IsInwardPointingTry5Local v ↔ 0 < (mvfderiv (𝓡∂ n) (f.extend (𝓡∂ n)) p v).ofLp 0 := by
  have h : MDifferentiableAt (𝓡∂ n) (𝓡∂ n) f p := by
    apply ((contMDiffOn_of_mem_maximalAtlas hf).mdifferentiableOn (ne_of_beq_false rfl)
      p hpf).mdifferentiableAt
    exact f.open_source.mem_nhds_iff.mpr hpf
  rw [f.extend_coe, mvfderiv_comp p (𝓡∂ n).mdifferentiableAt h, ContinuousLinearMap.comp_apply]
  rw [← prop541euclideanTry5Local ((Manifold.isBoundaryPoint_iff_of_mem_maximalAtlas hf hpf).mp hp)]
  rw [← (Manifold.localDiffeomorphOn_of_mem_maximalAtlas hf ⟨p, hpf⟩).isInwardPointing_iff]

lemma prop541general_part2 {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p)
    (f : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (hpf : p ∈ f.source) (hf : f ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M)
    (hv : 0 < (d% (𝓡∂ n) (f p) (mfderiv (𝓡∂ n) _ f p v)).ofLp 0) :
    IsInwardPointingTry5Local v := by
  rw [← prop541euclideanTry5Local] at hv
  · obtain ⟨g, U, hU, hUp, hg1, hg2, hg3, hg4⟩ := hv
    unfold IsInwardPointingTry5Local
    use g ∘ f, f.source ∩ f ⁻¹' U, f.isOpen_inter_preimage hU, ⟨hpf, hUp⟩,
      hg1.comp ((contMDiffOn_of_mem_maximalAtlas hf).mono inter_subset_left) inter_subset_right
    refine ⟨?_, ?_, ?_⟩
    · intro x ⟨hx1, hx2⟩
      apply hg2
      exact ⟨(Manifold.isInteriorPoint_iff_of_mem_maximalAtlas hf hx2.1).1 hx1, hx2.2⟩
    · intro x ⟨hx1, hx2⟩
      apply hg3
      exact ⟨(Manifold.isBoundaryPoint_iff_of_mem_maximalAtlas hf hx2.1).1 hx1, hx2.2⟩
    · unfold mvfderiv
      have hg : MDiffAt g (f p) :=
        (hg1.mdifferentiableOn (ne_of_beq_false rfl) (f p) hUp).mdifferentiableAt
          (hU.mem_nhds_iff.mpr hUp)
      -- separate something out
      have hf1 : MDifferentiableAt (𝓡∂ n) (𝓡∂ n) f p := by
        --apply mdifferentiableAt_of_mem_maximalAtlas
        apply ((contMDiffOn_of_mem_maximalAtlas hf).mdifferentiableOn (ne_of_beq_false rfl)
          p hpf).mdifferentiableAt
        exact f.open_source.mem_nhds_iff.mpr hpf
      rw [mfderiv_comp (g := g) (f := f) p hg hf1]
      exact hg4
  -- should probably separate this out, I also needed it above
  · rw [← ((Manifold.localDiffeomorphOn_of_mem_maximalAtlas hf) ⟨p, hpf⟩).isBoundaryPoint_iff
      (ne_of_beq_false rfl)]
    exact hp

lemma isInwardPointing_iff_forall_mem_maximalAtlas {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry5Local v ↔ ∀ (f) (_hf : f ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M)
      (_hpf : p ∈ f.source), 0 < (mvfderiv (𝓡∂ n) (f.extend (𝓡∂ n)) p v).ofLp 0 := by
  constructor
  · intro hv f hf hpf
    exact (isInwardPointing_iff_of_mem_maximalAtlas hp v f hpf hf).1 hv
  · intro h
    rw [isInwardPointing_iff_of_mem_maximalAtlas hp v (chartAt _ p)
      (mem_chart_source (EuclideanHalfSpace n) p) (IsManifold.chart_mem_maximalAtlas p)]
    exact h (chartAt _ p) (IsManifold.chart_mem_maximalAtlas p) (mem_chart_source _ p)

lemma isInwardPointing_iff_exists {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry5Local v ↔ ∃ (f : OpenPartialHomeomorph M (EuclideanHalfSpace n))
      (_hf : f ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M) (_hpf : p ∈ f.source),
      0 < (mvfderiv (𝓡∂ n) (f.extend (𝓡∂ n)) p v).ofLp 0 := by
  constructor
  · intro h
    use chartAt _ p, IsManifold.chart_mem_maximalAtlas p, mem_chart_source _ p
    exact (isInwardPointing_iff_of_mem_maximalAtlas hp v (chartAt _ p)
      (mem_chart_source (EuclideanHalfSpace n) p) (IsManifold.chart_mem_maximalAtlas p)).1 h
  · intro ⟨f, hf1, hpf, hf2⟩
    exact (isInwardPointing_iff_of_mem_maximalAtlas hp v f hpf hf1).2 hf2

lemma isInwardPointing_iff_chartAt {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry5Local v ↔
      0 < (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0 :=
  isInwardPointing_iff_of_mem_maximalAtlas hp _ _
    (mem_chart_source (EuclideanHalfSpace n) p) (IsManifold.chart_mem_maximalAtlas p)

theorem preimage_modelWithCorners_target_nontrivial {p : M} (hp : I.IsBoundaryPoint p)
    {v : TangentSpace I p} {f : M → ℝ}
    {s : Set M} (h : IsLocalMinOn f s p) (hs : s ∈ nhds p) (hv : IsInwardPointingTry5Local v) :
    ((fun (i : ℝ) ↦ (extChartAt I p) p +
      i • (d% (extChartAt I p) p) v) ⁻¹' I.target).Nontrivial := by

  sorry

theorem alongFunPreimIn_mem_nhdsWithin {p : M} (hp : I.IsBoundaryPoint p)
    {v : TangentSpace I p} {f : M → ℝ}
    {s : Set M} (h : IsLocalMinOn f s p) (hs : s ∈ nhds p) (hv : IsInwardPointingTry5Local v) :
    AlongFunPreimIn v (extChartAt I p).source ∈ 𝓝[>] 0 := by
  rw [alongFunPreimIn_extChartAt_source_eq v]
  rw [IsLocalDiffeomorphAt.isInwardPointing_iff _ _ (chartAt H p) sorry] at hv
  apply ContinuousWithinAt.preimage_mem_nhdsWithin' (by fun_prop)
  rw [zero_smul, add_zero]
  sorry

theorem IsLocalMinOn.mvfderivWithin_nonneg' {p : M} (hp : I.IsBoundaryPoint p)
    {v : TangentSpace I p} {f : M → ℝ}
    {s : Set M} (h : IsLocalMinOn f s p) (hs : s ∈ nhds p) (hv : IsInwardPointingTry5Local v) :
    (0 : ℝ) ≤ (mvfderivWithin I f s p) v := by
  by_cases hf : MDiffAt[s] f p
  · rw [mvfderivWithin_of_mem_nhds I f p hs]
    rw [← MDerivAlong_eq'' v f (hf.mdifferentiableAt hs) ?_]
    · apply (h.isLocalMin hs).mderivAlongWithin_nonneg_alongFunPreimIn' v

      sorry
    · sorry
  · simp [mvfderivWithin, mfderivWithin, hf]

-- everything starting from here should really be true for all models with corners but
-- this would require a lot of generalisation to show
-- not sure that this one is the correct approach :(
theorem IsLocalMinOn.mvfderivWithin_nonneg {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    {v : TangentSpace (𝓡∂ n) p} {f : M → ℝ}
    {s : Set M} (h : IsLocalMinOn f s p) (hs : s ∈ nhds p) (hv : IsInwardPointingTry5Local v) :
    (0 : ℝ) ≤ (mvfderivWithin (𝓡∂ n) f s p) v := by
  by_cases hf : MDifferentiableWithinAt (𝓡∂ n) 𝓘(ℝ, ℝ) f s p
  · have hv' := ((isInwardPointing_iff_chartAt hp v).mp hv).le
    rw [mvfderivWithin_of_mem_nhds (𝓡∂ n) f p hs]
    rw [← MDerivAlong_eq hp v ((isInwardPointing_iff_chartAt hp v).mp hv).le _
      (hf.mdifferentiableAt hs)]
    exact (h.isLocalMin hs).mderivAlongWithin_nonneg hp v hv' _ (hf.mdifferentiableAt hs)
  · simp [mvfderivWithin, mfderivWithin, hf]

theorem IsLocalMin.mvfderiv_nonneg {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    {v : TangentSpace (𝓡∂ n) p} {f : M → ℝ}
    (h : IsLocalMin f p) (hv : IsInwardPointingTry5Local v) :
    (0 : ℝ) ≤ (mvfderiv (𝓡∂ n) f p) v := by
  rw [← mvfderivWithin_univ]
  exact (isLocalMinOn_univ_iff.mpr h).mvfderivWithin_nonneg hp univ_mem hv

lemma mvfderiv_nonneg_of_eq_zero_boundary {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    {v : TangentSpace (𝓡∂ n) p} (hv : IsInwardPointingTry5Local v) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hpU : p ∈ U)
    (hf2 : ∀ x ∈ (𝓡∂ n).interior M ∩ U, 0 ≤ f x)
    (hf3 : ∀ x ∈ (𝓡∂ n).boundary M ∩ U, f x = 0) :
    0 ≤ (mvfderiv (𝓡∂ n) f p) v := by
  apply IsLocalMin.mvfderiv_nonneg hp ?_ hv
  apply IsMinOn.isLocalMin (s := U) ?_ (hU.mem_nhds_iff.mpr hpU)
  intro x hx
  by_cases hx' : (𝓡∂ n).IsInteriorPoint x
  · simp [hf3 p ⟨hp, hpU⟩, hf2 x ⟨hx', hx⟩]
  · rw [← ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint x] at hx'
    simp [hf3 p ⟨hp, hpU⟩, hf3 x ⟨hx', hx⟩]

def ConvexConeIsInwardPointing {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p) :
    ConvexCone ℝ (TangentSpace (𝓡∂ n) p) where
  carrier v := IsInwardPointingTry5Local v
  smul_mem' c hc v := by
    intro ⟨f, U, hU, hpU, hf1, hf2, hf3, hf4⟩
    use f, U, hU, hpU, hf1, hf2, hf3
    simp [hf4, hc]
  add_mem' v hv w hw := by
    have ⟨f, U, hU, hpU, hf1, hf2, hf3, hf4⟩ := hv
    have ⟨g, V, hV, hpV, hg1, hg2, hg3, hg4⟩ := hw
    use f + g, U ∩ V, hU.inter hV, ⟨hpU, hpV⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (hf1.mono inter_subset_left).add (hg1.mono inter_subset_right)
    · intro x ⟨hx1, hx2, hx3⟩
      exact add_pos (hf2 x ⟨hx1, hx2⟩) (hg2 x ⟨hx1, hx3⟩)
    · intro x ⟨hx1, hx2, hx3⟩
      simp [hf3 x ⟨hx1, hx2⟩, hg3 x ⟨hx1, hx3⟩]
    · rw [mvfderiv_add ?_ ?_]
      · simp only [add_apply, map_add]
        grw [← hg4, ← hf4, ← mvfderiv_nonneg_of_eq_zero_boundary hp hv hV hpV
          (fun x hx ↦ (hg2 x hx).le) hg3, ← mvfderiv_nonneg_of_eq_zero_boundary hp hw hU hpU
          (fun x hx ↦ (hf2 x hx).le) hf3]
        simp
      · apply (hf1.mdifferentiableOn (ne_of_beq_false rfl)).mdifferentiableAt
        exact hU.mem_nhds_iff.mpr hpU
      · apply (hg1.mdifferentiableOn (ne_of_beq_false rfl)).mdifferentiableAt
        exact hV.mem_nhds_iff.mpr hpV
