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
public import CollarNeighbourhoods.IsInwardPointing

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

noncomputable def MDerivAlong (f : M → ℝ) {p : M} (v : TangentSpace I p) :=
  letI y := (mvfderiv I (extChartAt I p) p) v
  d% (f ∘ (extChartAt I p).symm ∘ fun (i : ℝ) ↦ (extChartAt I p p) + i • y)

noncomputable def MDerivAlongWithin (f : M → ℝ) {p : M} (v : TangentSpace I p) (s : Set ℝ) :=
  letI y := (mvfderiv I (extChartAt I p) p) v
  d[s] (f ∘ (extChartAt I p).symm ∘ fun (i : ℝ) ↦ (extChartAt I p p) + i • y)

theorem mvfderivWithin_comp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type u_6} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {f : M → M'} (x : M) {s : Set M} {g : M' → F} {u : Set M'}
    (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x) (h : s ⊆ f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) :
    d[s] (g ∘ f) x = (d[u] g (f x)).comp (mfderiv[s] f x) := by
  unfold mvfderivWithin
  rw [mfderivWithin_comp x hg hf h hxs, ContinuousLinearMap.comp_assoc]
  rfl

theorem mvfderiv_comp_mvfderivWithin
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type u_6} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    {f : M → M'} (x : M) {s : Set M} {g : M' → F}
    (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x)
    (hxs : UniqueMDiffAt[s] x) :
    d[s] (g ∘ f) x = (d% g (f x)).comp (mfderiv[s] f x) := by
  unfold mvfderivWithin
  rw [mfderiv_comp_mfderivWithin x hg hf hxs, ← ContinuousLinearMap.comp_assoc]
  rfl

omit [IsManifold I ∞ M] in
lemma helper1 {p : M} (v : TangentSpace I p) :
    letI y := (mvfderiv I (extChartAt I p) p) v
    ((extChartAt I p).symm ∘ fun (i : ℝ) ↦ (extChartAt I p) p + i • y) 0 = p := by
  simp [(extChartAt I p).left_inv (mem_extChartAt_source p), -extChartAt]

#check MDifferentiableOn.mdifferentiableAt

-- lemma about when the inverse of the extChartAt is differentiable
lemma mdifferentiableWithinAt_extChartAt {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type u_3} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {M : Type u_4} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {x : M} :
    MDiffAt[(extChartAt I x).target] (extChartAt I x).symm ((extChartAt I x) x) := by
  simp

  sorry

-- use this instead probabaly
#check mdifferentiableWithinAt_extChartAt_symm

lemma hahaaja {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 < (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (f : M → ℝ)
    (hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f p) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) (𝓡∂ n) ((extChartAt (𝓡∂ n) p).symm ∘
      fun (i : ℝ) ↦ (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v)
        (Ici (0 : ℝ)) (0 : ℝ) := by

  sorry

instance {n : ℕ} [NeZero n] : Add (EuclideanHalfSpace n) where
  add x y := ⟨x.1 + y.1, add_nonneg x.2 y.2⟩

instance {n : ℕ} [NeZero n] : SMul NNReal (EuclideanHalfSpace n) where
  smul r x := ⟨r • x.1, smul_nonneg r.2 x.2⟩

lemma modelWithCornersEuclideanHalfSpace_add {n : ℕ} [NeZero n] (x y : EuclideanSpace ℝ (Fin n))
    (hx : 0 ≤ x.ofLp 0)
    (hy : 0 ≤ y.ofLp 0) :
    (𝓡∂ n).symm (x + y) = (𝓡∂ n).symm x + (𝓡∂ n).symm y := by
  change (𝓡∂ n).symm (⟨x + y, add_nonneg hx hy⟩ : EuclideanHalfSpace n) =
    (𝓡∂ n).symm (⟨x, hx⟩ : EuclideanHalfSpace n) + (𝓡∂ n).symm
    (⟨y, hy⟩ : EuclideanHalfSpace n)
  rw [modelWithCornersEuclideanHalfSpace_symm_val_apply,
    modelWithCornersEuclideanHalfSpace_symm_val_apply,
    modelWithCornersEuclideanHalfSpace_symm_val_apply]
  rfl

lemma MDerivAlong_eq {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : 0 < (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p v).ofLp 0)
    (f : M → ℝ)
    (hf : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) f p) :
    MDerivAlongWithin f v (Ici 0) 0 1 = mvfderiv (𝓡∂ n) f p v := by
  unfold MDerivAlongWithin
  letI y := (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v
  rw [mvfderiv_comp_mvfderivWithin 0 ((helper1 v).symm ▸ hf)]
  · sorry
  · unfold extChartAt
    rw [OpenPartialHomeomorph.extend_coe_symm, comp_assoc]

    -- mdifferentiableAt_symm_of_mem_maximalAtlas
    let g := ↑(𝓡∂ n).symm ∘ fun (i : ℝ) ↦
        ((chartAt (EuclideanHalfSpace n) p).extend (𝓡∂ n)) p +
          i • (mvfderiv (𝓡∂ n) ((chartAt (EuclideanHalfSpace n) p).extend (𝓡∂ n)) p) v
    have h1 : MDifferentiableAt (𝓡∂ n) (𝓡∂ n) (chartAt (EuclideanHalfSpace n) p).symm (g 0) := by
      apply mdifferentiableAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p)

      sorry
    --have := mdifferentiableAt_symm_of_mem_maximalAtlas
    apply h1.comp_mdifferentiableWithinAt
    unfold g
    rw [comp_def]

    have h : 0 ≤ (((chartAt (EuclideanHalfSpace n) p).extend (𝓡∂ n)) p).ofLp 0 := by
      sorry
    have h2 (x : ℝ) : 0 ≤ (x • (mvfderiv (𝓡∂ n)
      ((chartAt (EuclideanHalfSpace n) p).extend (𝓡∂ n)) p) v).ofLp 0 := by
      sorry
    --rw [fun x ↦ modelWithCornersEuclideanHalfSpace_add
    --  (((chartAt (EuclideanHalfSpace n) p).extend (𝓡∂ n)) p)
    --  (x • (mvfderiv (𝓡∂ n) ((chartAt (EuclideanHalfSpace n) p).extend (𝓡∂ n)) p) v)]
    sorry
    /-
    have h1 : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ n)
        (extChartAt (𝓡∂ n) p).symm (extChartAt (𝓡∂ n) p).target
        ((extChartAt (𝓡∂ n) p) p + (0 : ℝ) • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) := by
      apply MDifferentiableWithinAt.mono (extChartAt_target_subset_range p)
      apply mdifferentiableWithinAt_extChartAt_symm
      simp [mem_extChartAt_target p, -extChartAt]
    have h2 : MDiffAt[Ici 0] (fun (i : ℝ) ↦
        (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) 0 :=
      mdifferentiableWithinAt_const.add (mdifferentiableWithinAt_id.smul
        mdifferentiableWithinAt_const)
    let V := (fun (i : ℝ) ↦
        (extChartAt (𝓡∂ n) p) p + i • (mvfderiv (𝓡∂ n) (extChartAt (𝓡∂ n) p) p) v) ⁻¹'
        (extChartAt (𝓡∂ n) p).target
    --have hV : V ⊆ Ici 0 := by
    -- intro x
    --  simp [V]
    --  sorry
    apply MDifferentiableWithinAt.congr_nhds (s := V ∩ Ici 0)

    · apply h1.comp 0 (h2.mono inter_subset_right)
      exact inter_subset_left
    · unfold V

      sorry
      /-refine nhdsWithin_inter_of_mem ?_
      apply ContinuousWithinAt.preimage_mem_nhdsWithin' (by fun_prop)
      simp only [zero_smul, add_zero]
      apply nhdsWithin_mono (t := {x | 0 ≤ x.ofLp 0})
      · rw [← mapsTo_iff_image_subset]
        have : ((extChartAt (𝓡∂ n) p) p).ofLp 0 = 0 := by
          rw [ModelWithCorners.isBoundaryPoint_iff] at hp
          rw [range_modelWithCornersEuclideanHalfSpace n] at hp
          simp_all
        intro x hx
        simp only [mem_ofPred_eq, PiLp.add_apply, this, PiLp.smul_apply, smul_eq_mul, zero_add]
        exact (mul_nonneg_iff_of_pos_right hv).mpr hx
      ·
        sorry-/-/
  · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffWithinAt_Ici 0
