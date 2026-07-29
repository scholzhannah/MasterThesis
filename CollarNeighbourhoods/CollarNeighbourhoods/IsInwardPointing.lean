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

def IsInwardPointingTry5 {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (f : M → ℝ) (_ : CMDiff ∞ f) (_ : ∀ x ∈ I.interior M, 0 < f x)
    (_ : ∀ x ∈ I.boundary M, f x = 0), 0 < d% f p v

def IsInwardPointingTry5Local {p : M} (v : TangentSpace I p) : Prop :=
  ∃ (f : M → ℝ) (U : Set M) (_ : IsOpen U) (_ : p ∈ U) (_ : CMDiff[U] ∞ f)
    (_ : ∀ x ∈ I.interior M ∩ U, 0 < f x)
    (_ : ∀ x ∈ I.boundary M ∩ U, f x = 0), 0 < d% f p v

lemma modelWithCornersEuclideanHalfSpace_apply {p : EuclideanHalfSpace n} : (𝓡∂ n) p = p.val :=
  rfl

@[simp]
lemma modelWithCornersEuclideanHalfSpace_symm_val_apply {p : EuclideanHalfSpace n} :
    (𝓡∂ n).symm p.val = p := by
  rw [← modelWithCornersEuclideanHalfSpace_apply, ModelWithCorners.left_inv (𝓡∂ n) p]

lemma modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff {p : EuclideanHalfSpace n} :
    (𝓡∂ n).IsBoundaryPoint p ↔ ((𝓡∂ n) p).ofLp 0 = 0 := by
  simp [ModelWithCorners.isBoundaryPoint_iff, eq_comm,
    range_modelWithCornersEuclideanHalfSpace, chartAt_self_eq,
    -modelWithCornersEuclideanHalfSpace_toFun]

lemma ModelWithCorners.IsBoundaryPoint.eq_zero_of_modelWithCornersEuclideanHalfSpace
    {p : EuclideanHalfSpace n}
    (hp : (𝓡∂ n).IsBoundaryPoint p) : ((𝓡∂ n) p).ofLp 0 = 0 :=
  modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff.mp hp

lemma modelWithCornersEuclideanHalfSpace_symm_apply_of_IsBoundaryPoint {p : EuclideanHalfSpace n}
    : (𝓡∂ n).symm ((𝓡∂ n) p) = p := by
  simp [-modelWithCornersEuclideanHalfSpace_toFun]

lemma modelWithCornersEuclideanHalfSpace_boundary_eq :
    (𝓡∂ n).boundary (EuclideanHalfSpace n) = {p | ((𝓡∂ n) p).ofLp 0 = 0} := by
  simp_rw [← modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff]
  rfl

lemma modelWithCornersEuclideanHalfSpace_isInteriorPoint_iff {p : EuclideanHalfSpace n} :
    (𝓡∂ n).IsInteriorPoint p ↔ ((𝓡∂ n) p).ofLp 0 > 0 := by
  simp [ModelWithCorners.isInteriorPoint_iff, range_modelWithCornersEuclideanHalfSpace,
    chartAt_self_eq, -modelWithCornersEuclideanHalfSpace_toFun]

lemma modelWithCornersEuclideanHalfSpace_interior_eq :
    (𝓡∂ n).interior (EuclideanHalfSpace n) = {p | 0 < ((𝓡∂ n) p).ofLp 0} := by
  simp_rw [← modelWithCornersEuclideanHalfSpace_isInteriorPoint_iff]
  rfl

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

set_option backward.isDefEq.respectTransparency false in
lemma prop541euclideanTry5Local {p : EuclideanHalfSpace n} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry5Local v ↔ 0 < ((d% (𝓡∂ n) p) v).ofLp 0 := by
  constructor
  · intro ⟨f, U, hU, hUp, hf1, hf2, hf3, hf4⟩
    by_contra! hv
    let x := (mfderiv% (𝓡∂ n) p) v
    let y := (d% (𝓡∂ n) p) v
    let V := (↑(𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) ⁻¹' U
    have hV : IsOpen V := by
      apply Continuous.isOpen_preimage ?_ U hU
      exact (ModelWithCorners.continuous_symm (𝓡∂ n)).comp (by fun_prop)
    have hV0 : 0 ∈ V := by
      simp [V, hUp, -modelWithCornersEuclideanHalfSpace_toFun]
    -- one could possibly make this nicer usin `LineDeriv` but there is few API about it
    have yay1 : d[Ici (0 : ℝ) ∩ V] (f ∘ (𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 1 < 0 := by
      unfold mvfderivWithin
      have h1 : MDiffAt[U] f (((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0) := by
        simp only [comp_apply, zero_smul, sub_zero, ModelWithCorners.left_inv]
        exact (hf1 p hUp).mdifferentiableWithinAt (ne_of_beq_false rfl)
      have hh : MDiffAt[{x | 0 ≤ x.ofLp 0}] (𝓡∂ n).symm ((𝓡∂ n) p - (0 : ℝ) • y) := by
        simp only [zero_smul, sub_zero]
        exact modelWithCornersEuclideanHalfSpace_symm_mDifferentialbleWithinAt hp
      have h2'' : MDiffAt[Ici 0 ∩ V] (fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 := by
          refine DifferentiableWithinAt.mdifferentiableWithinAt ?_
          fun_prop
      have h2''' : Ici 0 ∩ V ⊆ (fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) ⁻¹' {x | 0 ≤ x.ofLp 0} := by
        intro x ⟨hx1, hx2⟩
        simp [hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, y,
          mul_nonpos_of_nonneg_of_nonpos hx1 hv, -modelWithCornersEuclideanHalfSpace_toFun]
      have h2 : MDiffAt[Ici 0 ∩ V] ((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 :=
        hh.comp 0 h2'' h2'''
      have h3 : UniqueMDiffAt[Ici (0 : ℝ) ∩ V] 0 := by
        apply UniqueMDiffWithinAt.inter
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffWithinAt_Ici 0
        · exact hV.mem_nhds_iff.mpr hV0
      have h4 : (↑(𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 = p := by
        simp [-modelWithCornersEuclideanHalfSpace_toFun]
      -- this rewrite below produces defeq issues because we're changing the precise presentation
      -- of the point in the tangent space. Even when removing this def-eq issue, we still
      -- get a def-eq issue where the lemma applies both functions  individually but we need them
      -- applied as a composition
      rw [mfderivWithin_comp (s := Ici (0 : ℝ) ∩ V) (g := f)
        (f := (𝓡∂ n).symm ∘ fun i ↦ (𝓡∂ n) p - i • y) (x := 0) h1 h2 inter_subset_right h3]
      simp only [comp_apply]
      rw [zero_smul, sub_zero, ModelWithCorners.left_inv]
      rw [← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_apply]
      suffices h : (mfderiv[Ici (0 : ℝ) ∩ V]
        ((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0) 1 = -v by
        have : d[U] f p (-v) < 0 := by simp [mvfderivWithin_of_isOpen _ f p hU hUp, hf4]
        exact h ▸ this
      rw [mfderivWithin_comp 0 hh h2'' h2''' h3]
      rw [zero_smul ℝ y]
      rw [sub_zero]
      rw [HasMFDerivWithinAt.mfderivWithin
        (modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt hp)]
      · simp only [comp_apply, mfderivWithin_eq_fderivWithin, ContinuousLinearMap.id_comp]
        change (fderivWithin ℝ (fun (i : ℝ) ↦ p.val - i • y) (Ici 0 ∩ V) 0) 1 = -v
        rw [fderivWithin_derivWithin (𝕜 := ℝ) (f := fun (i : ℝ) ↦ p.val - i • y) (s := Ici 0 ∩ V)]
        rw [derivWithin_const_sub]
        rw [derivWithin_smul_const differentiableWithinAt_fun_id y]
        rw [derivWithin_id' 0 (Ici 0 ∩ V) h3.uniqueDiffWithinAt]
        simp only [mvfderiv, (𝓡∂ n).hasMFDerivAt.mfderiv (x := p), ContinuousLinearMap.comp_id,
          ContinuousLinearEquiv.coe_coe, one_smul, neg_inj, y]
        rfl
      rw [← range_modelWithCornersEuclideanHalfSpace n]
      exact (𝓡∂ n).uniqueMDiffOn _ (mem_range_self p)
    unfold mvfderivWithin at yay1
    simp only [comp_apply, mfderivWithin_eq_fderivWithin, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] at yay1
    rw [zero_smul, sub_zero] at yay1
    -- this is major def-eq abuse caused by `mfderiv_eq_fderiv`
    simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk] at yay1
    -- this uses the assumptions hv and hf3
    have yay2 : 0 ≤ (fderivWithin ℝ (f ∘ ↑(𝓡∂ n).symm ∘ fun i ↦ (𝓡∂ n) p - i • y)
        (Ici 0 ∩ V) 0) 1 := by
      apply IsLocalMinOn.fderivWithin_nonneg
      · apply IsMinOn.localize
        intro x ⟨hx1, hx2⟩
        simp only [comp_apply, zero_smul, sub_zero, ModelWithCorners.left_inv, hf3 p ⟨hp, hUp⟩,
          mem_ofPred_eq]
        by_cases! hx' : x = 0 ∨ ((d% (𝓡∂ n) p) v).ofLp 0 = 0
        · rcases hx' with h1 | h2
          · simp only [h1, zero_smul, sub_zero, ModelWithCorners.left_inv]
            apply ge_of_eq
            apply hf3
            simp [modelWithCornersEuclideanHalfSpace_boundary_eq,
              hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, hUp,
              -modelWithCornersEuclideanHalfSpace_toFun]
          · apply ge_of_eq
            apply hf3
            simp only [modelWithCornersEuclideanHalfSpace_boundary_eq, mem_inter_iff, mem_ofPred_eq,
              y]
            rw [ModelWithCorners.right_inv]
            · simpa [hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, h2, V,
                -modelWithCornersEuclideanHalfSpace_toFun] using hx2
            · simp [range_modelWithCornersEuclideanHalfSpace n,
                hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, h2,
                -modelWithCornersEuclideanHalfSpace_toFun]
        · apply le_of_lt
          apply hf2
          simp only [modelWithCornersEuclideanHalfSpace_interior_eq, mem_inter_iff, mem_ofPred_eq]
          rw [ModelWithCorners.right_inv]
          · simp only [PiLp.sub_apply, hp.eq_zero_of_modelWithCornersEuclideanHalfSpace,
              PiLp.smul_apply, smul_eq_mul, zero_sub, Left.neg_pos_iff, y]
            refine ⟨?_, by simpa [V, -modelWithCornersEuclideanHalfSpace_toFun] using hx2⟩
            exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hx1 hx'.1.symm) (lt_of_le_of_ne hv hx'.2)
          · simp only [range_modelWithCornersEuclideanHalfSpace n, mem_ofPred_eq, PiLp.sub_apply,
              hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, PiLp.smul_apply, smul_eq_mul,
              zero_sub, Left.nonneg_neg_iff, y]
            apply le_of_lt
            exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hx1 hx'.1.symm) (lt_of_le_of_ne hv hx'.2)
      · simp only [one_mem_posTangentConeAt_iff_mem_closure, ← inter_assoc,
          inter_eq_self_of_subset_left Ioi_subset_Ici_self]
        apply hV.closure_inter
        simp [hV0]
    exact not_lt_of_ge yay2 yay1
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
    -- **Def-eq issues reproducer**:
    -- if you turn the line below into a `simp only`, this causes def-eq issues not caught by
    -- `linter.tacticCheckInstances`, this is especially bad, because this lemma is a
    -- `simp` lemma
    rw [Function.comp_apply]
    have h3 : MDiffAt (proj 0 : StrongDual ℝ (EuclideanSpace ℝ (Fin n))) ((𝓡∂ n) p) := by
      apply DifferentiableAt.mdifferentiableAt
      fun_prop
    rw [mfderiv_comp p h3 (𝓡∂ n).mdifferentiableAt,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.mfderiv_eq (proj 0 : StrongDual ℝ (EuclideanSpace ℝ (Fin n)))]
    exact h

-- **ToDo** : Fix defeq abuse tomorrow

--set_option linter.tacticCheckInstances true
--#defeq_abuse in
set_option backward.isDefEq.respectTransparency false in
lemma prop541euclideanTry5 {p : EuclideanHalfSpace n} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry5 v ↔ 0 < ((d% (𝓡∂ n) p) v).ofLp 0 := by
  constructor
  · intro ⟨f, hf1, hf2, hf3, hf4⟩
    by_contra! hv
    let x := (mfderiv% (𝓡∂ n) p) v
    let y := (d% (𝓡∂ n) p) v
    have yay1 : d[Ici (0 : ℝ)] (f ∘ (𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 1 < 0 := by
      unfold mvfderivWithin
      have h1 :  MDiffAt f p := hf1.mdifferentiableAt (ne_of_beq_false rfl)
      have hh : MDiffAt[{x | 0 ≤ x.ofLp 0}] (𝓡∂ n).symm ((𝓡∂ n) p - (0 : ℝ) • y) := by
        simp only [zero_smul, sub_zero]
        exact modelWithCornersEuclideanHalfSpace_symm_mDifferentialbleWithinAt hp
      have h2'' : MDiffAt[Ici 0] (fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 := by
          refine DifferentiableWithinAt.mdifferentiableWithinAt ?_
          fun_prop
      have h2''' : Ici 0 ⊆ (fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) ⁻¹' {x | 0 ≤ x.ofLp 0} := by
        intro x hx
        simp [hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, y,
          mul_nonpos_of_nonneg_of_nonpos hx hv, -modelWithCornersEuclideanHalfSpace_toFun]
      have h2 : MDiffAt[Ici 0] ((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 :=
        hh.comp 0 h2'' h2'''
      have h3 : UniqueMDiffAt[Ici (0 : ℝ)] 0 := by
        rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
        exact uniqueDiffWithinAt_Ici 0
      have h4 : (↑(𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0 = p := by
        simp [-modelWithCornersEuclideanHalfSpace_toFun]
      -- this rewrite below produces defeq issues because we're changing the precise presentation
      -- of the point in the tangent space. Even when removing this def-eq issue, we still
      -- get a def-eq issue where the lemma applies both functions individually but we need them
      -- applied as a composition
      rw [mfderiv_comp_mfderivWithin_of_eq h1 h2 h3 h4]
      simp only [comp_apply]
      rw [zero_smul, sub_zero, ModelWithCorners.left_inv]
      rw [← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_apply]
      suffices h : (mfderiv[Ici (0 : ℝ)] ((𝓡∂ n).symm ∘ fun (i : ℝ) ↦ (𝓡∂ n) p - i • y) 0) 1 = -v by
        have : (d% f p) (-v) < 0 := by simp [hf4]
        exact h ▸ this
      rw [mfderivWithin_comp 0 hh h2'' h2''' h3]
      rw [zero_smul ℝ y]
      rw [sub_zero]
      rw [HasMFDerivWithinAt.mfderivWithin
        (modelWithCornersEuclideanHalfSpace_symm_hasMFDerivWithinAt hp)]
      · simp only [comp_apply, mfderivWithin_eq_fderivWithin, ContinuousLinearMap.id_comp]
        change (fderivWithin ℝ (fun (i : ℝ) ↦ p.val - i • y) (Ici 0) 0) 1 = -v
        rw [fderivWithin_derivWithin (𝕜 := ℝ) (f := fun (i : ℝ) ↦ p.val - i • y) (s := Ici 0)]
        rw [derivWithin_const_sub]
        rw [derivWithin_smul_const differentiableWithinAt_fun_id y]
        rw [derivWithin_id' 0 (Ici 0) (uniqueDiffWithinAt_Ici 0)]
        simp only [mvfderiv, (𝓡∂ n).hasMFDerivAt.mfderiv (x := p), ContinuousLinearMap.comp_id,
          ContinuousLinearEquiv.coe_coe, one_smul, neg_inj, y]
        rfl
      rw [← range_modelWithCornersEuclideanHalfSpace n]
      exact (𝓡∂ n).uniqueMDiffOn _ (mem_range_self p)
    unfold mvfderivWithin at yay1
    simp only [comp_apply, mfderivWithin_eq_fderivWithin, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] at yay1
    rw [zero_smul, sub_zero] at yay1
    -- this is major def-eq abuse caused by `mfderiv_eq_fderiv`
    simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk] at yay1
    -- this uses the assumptions hv and hf3
    have yay2 : 0 ≤ (fderivWithin ℝ (f ∘ ↑(𝓡∂ n).symm ∘ fun i ↦ (𝓡∂ n) p - i • y)
        (Ici (0 : ℝ)) 0) 1 := by
      apply IsLocalMinOn.fderivWithin_nonneg
      · apply IsMinOn.localize
        intro x hx
        simp only [comp_apply, zero_smul, sub_zero, ModelWithCorners.left_inv, hf3 p hp,
          mem_ofPred_eq]
        by_cases! hx' : x = 0 ∨ ((d% (𝓡∂ n) p) v).ofLp 0 = 0
        · rcases hx' with h1 | h2
          · simp only [h1, zero_smul, sub_zero, ModelWithCorners.left_inv]
            apply ge_of_eq
            apply hf3
            simp [modelWithCornersEuclideanHalfSpace_boundary_eq,
              hp.eq_zero_of_modelWithCornersEuclideanHalfSpace,
              -modelWithCornersEuclideanHalfSpace_toFun]
          · apply ge_of_eq
            apply hf3
            simp only [modelWithCornersEuclideanHalfSpace_boundary_eq, mem_ofPred_eq, y]
            rw [ModelWithCorners.right_inv]
            · simp [hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, h2,
                -modelWithCornersEuclideanHalfSpace_toFun]
            · simp [range_modelWithCornersEuclideanHalfSpace n,
                hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, h2,
                -modelWithCornersEuclideanHalfSpace_toFun]
        · apply le_of_lt
          apply hf2
          simp only [modelWithCornersEuclideanHalfSpace_interior_eq, mem_ofPred_eq]
          rw [ModelWithCorners.right_inv]
          · simp only [PiLp.sub_apply, hp.eq_zero_of_modelWithCornersEuclideanHalfSpace,
              PiLp.smul_apply, smul_eq_mul, zero_sub, Left.neg_pos_iff, y]
            exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hx hx'.1.symm) (lt_of_le_of_ne hv hx'.2)
          · simp only [range_modelWithCornersEuclideanHalfSpace n, mem_ofPred_eq, PiLp.sub_apply,
              hp.eq_zero_of_modelWithCornersEuclideanHalfSpace, PiLp.smul_apply, smul_eq_mul,
              zero_sub, Left.nonneg_neg_iff, y]
            apply le_of_lt
            exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hx hx'.1.symm) (lt_of_le_of_ne hv hx'.2)
      · simp [one_mem_posTangentConeAt_iff_mem_closure,
          inter_eq_self_of_subset_left Ioi_subset_Ici_self]
    apply not_lt_of_ge yay2 yay1
  · intro h
    have h1 : ∀ x ∈ (𝓡∂ n).interior (EuclideanHalfSpace n), 0 < (proj 0 ∘ 𝓡∂ n) x := by
      intro x hx
      simpa [modelWithCornersEuclideanHalfSpace_apply,
        modelWithCornersEuclideanHalfSpace_interior_eq] using hx
    have h2 : ∀ x ∈ (𝓡∂ n).boundary (EuclideanHalfSpace n), (proj 0 ∘ 𝓡∂ n) x = 0 := by
      intro x hx
      simpa [modelWithCornersEuclideanHalfSpace_apply,
        modelWithCornersEuclideanHalfSpace_boundary_eq] using hx
    use proj 0 ∘ 𝓡∂ n, ContDiff.comp_contMDiff (by fun_prop) (𝓡∂ n).contMDiff, h1, h2
    unfold mvfderiv
    -- **Def-eq issues reproducer**:
    -- if you turn the line below into a `simp only`, this causes def-eq issues not caught by
    -- `linter.tacticCheckInstances`, this is especially bad, because this lemma is a
    -- `simp` lemma
    rw [Function.comp_apply]
    have h3 : MDiffAt (proj 0 : StrongDual ℝ (EuclideanSpace ℝ (Fin n))) ((𝓡∂ n) p) := by
      apply DifferentiableAt.mdifferentiableAt
      fun_prop
    rw [mfderiv_comp p h3 (𝓡∂ n).mdifferentiableAt,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.mfderiv_eq (proj 0 : StrongDual ℝ (EuclideanSpace ℝ (Fin n)))]
    exact h

def Manifold.PartialDiffeomorphOfMaximalAtlas {f : OpenPartialHomeomorph M H}
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) : PartialDiffeomorph I I M H ∞ where
  toPartialEquiv := f.toPartialEquiv
  open_source := f.open_source
  open_target := f.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hf
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hf

omit [IsManifold I ∞ M] in
lemma Manifold.localDiffeomorphOn_of_mem_maximalAtlas {f : OpenPartialHomeomorph M H}
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) : IsLocalDiffeomorphOn I I ∞ f f.source:= by
  intro x
  apply (Manifold.PartialDiffeomorphOfMaximalAtlas hf).isLocalDiffeomorphAt
  exact x.2

omit [IsManifold I ∞ M] in
lemma Manifold.localDiffeomorphOn_symm_of_mem_maximalAtlas {f : OpenPartialHomeomorph M H}
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) : IsLocalDiffeomorphOn I I ∞ f.symm f.target := by
  intro x
  apply (Manifold.PartialDiffeomorphOfMaximalAtlas hf).symm.isLocalDiffeomorphAt
  exact x.2

omit [IsManifold I ∞ M] in
lemma Manifold.isBoundaryPoint_iff_of_me_maximalAtlas {f : OpenPartialHomeomorph M H}
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) {p : M} (hpf : p ∈ f.source) :
    I.IsBoundaryPoint p ↔ I.IsBoundaryPoint (f p) := by
  exact ((Manifold.localDiffeomorphOn_of_mem_maximalAtlas hf) ⟨p, hpf⟩).isBoundaryPoint_iff
      (ne_of_beq_false rfl)

omit [IsManifold I ∞ M] in
lemma Manifold.isInteriorPoint_iff_of_me_maximalAtlas {f : OpenPartialHomeomorph M H}
    (hf : f ∈ IsManifold.maximalAtlas I ∞ M) {p : M} (hpf : p ∈ f.source) :
    I.IsInteriorPoint p ↔ I.IsInteriorPoint (f p) := by
  exact ((Manifold.localDiffeomorphOn_of_mem_maximalAtlas hf) ⟨p, hpf⟩).isInteriorPoint_iff
      (ne_of_beq_false rfl)

set_option backward.isDefEq.respectTransparency false in
lemma prop541general_part1 {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (hv : IsInwardPointingTry5Local v)
    (f : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (hpf : p ∈ f.source) (hf : f ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M) :
    0 < (d% (𝓡∂ n) (f p) (mfderiv (𝓡∂ n) _ f p v)).ofLp 0 := by
  rw [← prop541euclideanTry5Local ((Manifold.isBoundaryPoint_iff_of_me_maximalAtlas hf hpf).mp hp)]
  obtain ⟨g, U, hU, hUp, hg1, hg2, hg3, hg4⟩ := hv
  use g ∘ f.symm, (f '' (f.source ∩ U)), f.isOpen_image_source_inter hU,
    mem_image_of_mem f ⟨hpf, hUp⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : ContMDiffOn (𝓡∂ n) (𝓡∂ n) ∞ (f.symm) (f '' (f.source ∩ U)) := by
      apply (contMDiffOn_symm_of_mem_maximalAtlas hf).mono
      exact subset_trans (image_mono inter_subset_left) f.image_source_subset
    apply hg1.comp h
    rw [f.image_source_inter_eq' U]
    exact inter_subset_right
  · intro x ⟨hx1, hx2⟩
    --maybe the set should already be stated like what the rewrite does?
    rw [f.image_source_inter_eq' U] at hx2
    apply hg2
    refine ⟨?_, hx2.2⟩
    change (𝓡∂ n).IsInteriorPoint (f.symm x)
    rw [← ((Manifold.localDiffeomorphOn_symm_of_mem_maximalAtlas hf)
      ⟨x, hx2.1⟩).isInteriorPoint_iff (ne_of_beq_false rfl)]
    exact hx1
  · intro x ⟨hx1, hx2⟩
    rw [f.image_source_inter_eq' U] at hx2
    apply hg3
    refine ⟨?_, hx2.2⟩
    change (𝓡∂ n).IsBoundaryPoint (f.symm x)
    rw [← ((Manifold.localDiffeomorphOn_symm_of_mem_maximalAtlas hf)
      ⟨x, hx2.1⟩).isBoundaryPoint_iff (ne_of_beq_false rfl)]
    exact hx1
  · unfold mvfderiv
    have hg : MDifferentiableAt (𝓡∂ n) 𝓘(ℝ, ℝ) g (f.symm (f p)) := by
      rw [f.left_inv hpf]
      exact (hg1.mdifferentiableOn (ne_of_beq_false rfl) p hUp).mdifferentiableAt
        (hU.mem_nhds_iff.mpr hUp)
    have hf1 : MDifferentiableAt (𝓡∂ n) (𝓡∂ n) f.symm (f p) := by
      apply ((contMDiffOn_symm_of_mem_maximalAtlas hf).mdifferentiableOn (ne_of_beq_false rfl)
        (f p) (f.map_source hpf)).mdifferentiableAt
      exact f.open_target.mem_nhds_iff.mpr (f.map_source hpf)
    have hf2 : MDifferentiableAt (𝓡∂ n) (𝓡∂ n) f p := by
      apply ((contMDiffOn_of_mem_maximalAtlas hf).mdifferentiableOn (ne_of_beq_false rfl)
        p hpf).mdifferentiableAt
      exact f.open_source.mem_nhds_iff.mpr hpf
    -- this literally always gives defeq issues...
    -- how do I fix this?
    rw [mfderiv_comp (f p) hg hf1, ← ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_apply, ← mfderiv_comp_apply p hf1 hf2 v,
      ← mfderivWithin_of_isOpen f.open_source hpf, mfderivWithin_congr (f := id)
      (f₁ := f.symm ∘ f) f.leftInvOn (f.left_inv hpf), mfderivWithin_of_isOpen f.open_source hpf,
      mfderiv_id]
    -- I need the `simp` and then the first rewrite to fix some defeq issue again with application
    -- of composition
    simp only [comp_apply]
    rw [f.left_inv hpf, ContinuousLinearMap.id_apply (R₁ := ℝ) v]
    exact hg4

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
      exact ⟨(Manifold.isInteriorPoint_iff_of_me_maximalAtlas hf hx2.1).1 hx1, hx2.2⟩
    · intro x ⟨hx1, hx2⟩
      apply hg3
      exact ⟨(Manifold.isBoundaryPoint_iff_of_me_maximalAtlas hf hx2.1).1 hx1, hx2.2⟩
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

lemma prop541general {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry5Local v ↔ ∀ (f) (_hf : f ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M)
      (_hpf : p ∈ f.source) ,
      0 < (d% (𝓡∂ n) (f p) (mfderiv (𝓡∂ n) _ f p v)).ofLp 0 := by
  constructor
  · intro hv f hf hpf
    exact prop541general_part1 (E := E) hp v hv f hpf hf
  · intro h
    apply prop541general_part2 (E := E) hp (f := chartAt _ p) v (mem_chart_source _ p)
      (IsManifold.chart_mem_maximalAtlas p)
    exact h (chartAt _ p) (IsManifold.chart_mem_maximalAtlas p) (mem_chart_source _ p)

lemma isInwardPointing_iff_exists {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry5Local v ↔ ∃ (f : OpenPartialHomeomorph M (EuclideanHalfSpace n))
      (_hf : f ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M) (_hpf : p ∈ f.source),
      0 < (d% (𝓡∂ n) (f p) (mfderiv (𝓡∂ n) _ f p v)).ofLp 0 := by
  constructor
  · intro h
    use chartAt _ p, IsManifold.chart_mem_maximalAtlas p, mem_chart_source _ p
    exact prop541general_part1 (E := E) hp v h (chartAt _ p ) (mem_chart_source _ p)
      (IsManifold.chart_mem_maximalAtlas p)
  · intro ⟨f, hf1, hpf, hf2⟩
    exact prop541general_part2 (E := E) hp v f hpf hf1 hf2

lemma isInwardPointing_iff_chartAt {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) :
    IsInwardPointingTry5Local v ↔
      0 < (d% (𝓡∂ n) (chartAt _ p p) (mfderiv (𝓡∂ n) _ (chartAt _ p) p v)).ofLp 0 := by
  constructor
  · intro hv
    exact prop541general_part1 (E := E) hp v hv (chartAt _ p ) (mem_chart_source _ p)
      (IsManifold.chart_mem_maximalAtlas p)
  · intro h
    exact prop541general_part2 (E := E) hp v (chartAt _ p) (mem_chart_source _ p)
      (IsManifold.chart_mem_maximalAtlas p) h

#check mem_tangentConeAt_of_frequently

theorem IsLocalMinOn.mvfderivWithin_nonneg' {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (f : M → ℝ)
    (s : Set M) (h : IsMinOn f s p) (hs : s ∈ nhds p) (hv : IsInwardPointingTry5Local v) :
    (0 : ℝ) ≤ (mvfderivWithin (𝓡∂ n) f s p) v := by
  by_cases hf : MDifferentiableWithinAt (𝓡∂ n) 𝓘(ℝ, ℝ) f s p
  · let y := (mvfderiv (𝓡∂ n) ((𝓡∂ n) ∘ chartAt (EuclideanHalfSpace n) p) p) v
    let V := ((chartAt (EuclideanHalfSpace n) p).symm ∘ (𝓡∂ n).symm ∘
      fun (i : ℝ) ↦ (𝓡∂ n) (chartAt (EuclideanHalfSpace n) p p) + i • y) ⁻¹' s
    suffices 0 ≤ d[Ici (0 : ℝ) ∩ V] (f ∘ (chartAt (EuclideanHalfSpace n) p).symm ∘ (𝓡∂ n).symm ∘
        fun (i : ℝ) ↦ (𝓡∂ n) (chartAt (EuclideanHalfSpace n) p p) + i • y) 0 1 by
      unfold mvfderivWithin at this
      --rw [mfderivWithin_comp] at this
      sorry
    sorry
  · sorry

-- should be able to generlize this to IsLocalMinOn
-- and it should probably also hold for more general models with corners but no idea
theorem IsLocalMinOn.mvfderivWithin_nonneg {M : Type*}
    [TopologicalSpace M] {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M]
    [Fact (finrank ℝ E = n)] [IsManifold (𝓡∂ n) ∞ M] {p : M} (hp : (𝓡∂ n).IsBoundaryPoint p)
    (v : TangentSpace (𝓡∂ n) p) (f : M → ℝ)
    (s : Set M) (h : IsMinOn f s p) (hs : s ∈ nhds p) (hv : IsInwardPointingTry5Local v) :
    (0 : ℝ) ≤ (mvfderivWithin (𝓡∂ n) f s p) v := by
  by_cases hf : MDifferentiableWithinAt (𝓡∂ n) 𝓘(ℝ, ℝ) f s p
  · simp only [mvfderivWithin, mfderivWithin, hf, ↓reduceIte, writtenInExtChartAt, extChartAt,
      OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl,
      PartialHomeomorph.toFun_eq_coe, OpenPartialHomeomorph.coe_toPartialHomeomorph,
      PartialEquiv.coe_trans_symm, PartialHomeomorph.coe_toPartialEquiv_symm,
      OpenPartialHomeomorph.coe_toPartialHomeomorph_symm, ModelWithCorners.toPartialEquiv_coe_symm,
      PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe, comp_apply]
    change 0 ≤ fderivWithin ℝ ((chartAt ℝ (f p)) ∘ f ∘
        (chartAt (EuclideanHalfSpace n) p).symm ∘ (𝓡∂ n).symm)
        (↑(chartAt (EuclideanHalfSpace n) p).symm ∘ ↑(𝓡∂ n).symm ⁻¹' s ∩ range ↑(𝓡∂ n))
        ((𝓡∂ n) ((chartAt (EuclideanHalfSpace n) p) p)) v
    apply IsLocalMinOn.fderivWithin_nonneg
    · apply IsMinOn.localize
      intro x hx
      change ∀ x, _ at h
      simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, comp_apply,
        ModelWithCorners.left_inv, mem_chart_source, OpenPartialHomeomorph.left_inv, id_eq,
        mem_ofPred_eq]
      apply h
      exact hx.1
    · rw [isInwardPointing_iff_chartAt (E := E) hp] at hv
      unfold posTangentConeAt
      rw [modelWithCornersEuclideanHalfSpace_apply]
      rw [range_modelWithCornersEuclideanHalfSpace n]
      rw [preimage_comp]
      have : ((𝓡∂ n).symm ⁻¹' ((chartAt (EuclideanHalfSpace n) p).target ∩
            (chartAt (EuclideanHalfSpace n) p).symm ⁻¹' (interior s)) ∩ {y | 0 ≤ y.ofLp 0}) ⊆
          ((𝓡∂ n).symm ⁻¹' (chartAt (EuclideanHalfSpace n) p).symm ⁻¹' s ∩ {y | 0 ≤ y.ofLp 0}) := by
        apply inter_subset_inter_left
        apply preimage_mono
        apply subset_trans inter_subset_right
        apply preimage_mono
        exact interior_subset
      apply tangentConeAt_mono this
      rw [inter_comm, tangentConeAt_inter_nhds]
      · apply mem_posTangentConeAt_of_frequently_mem
        apply Eventually.frequently
        rw [eventually_nhdsWithin_iff]
        apply Eventually.of_forall
        intro x hx
        have : (𝓡∂ n).IsBoundaryPoint ((chartAt (EuclideanHalfSpace n) p) p) :=
          ModelWithCorners.isBoundaryPoint_iff.mpr hp
        simp [modelWithCornersEuclideanHalfSpace_isBoundaryPoint_iff] at this
        simp only [mem_ofPred_eq, PiLp.add_apply, this, zero_add, ge_iff_le]
        change 0 ≤ x • v.ofLp 0
        have : (d% (𝓡∂ n) ((chartAt (EuclideanHalfSpace n) p) p))
            ((mfderiv (𝓡∂ n) (𝓡∂ n) (chartAt (EuclideanHalfSpace n) p) p) v) = v := by
          simp only [mvfderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]

          rw [← mfderiv_comp_apply_of_eq p ?_ ?_ ?_ v]
          ·
            sorry
          · sorry
          · sorry
          · sorry
        sorry
      · have : IsOpen ((𝓡∂ n).symm ⁻¹' ((chartAt (EuclideanHalfSpace n) p).target ∩
            (chartAt (EuclideanHalfSpace n) p).symm ⁻¹' (interior s))) := by
          apply (𝓡∂ n).continuous_symm.isOpen_preimage
          apply (chartAt (EuclideanHalfSpace n) p).continuousOn_symm.isOpen_inter_preimage
          · exact (chartAt (EuclideanHalfSpace n) p).open_target
          · exact isOpen_interior
        apply this.mem_nhds_iff.mpr
        simp [mem_interior_iff_mem_nhds, hs]
  · simp [mvfderivWithin, mfderivWithin, hf]

-- needs more conditions
example (p : M) (v : TangentSpace I p) (f : M → ℝ) (U : Set M) (hU : IsOpen U) (hpU : p ∈ U)
    (hf1 : CMDiff[U] ∞ f) (hf2 : ∀ x ∈ I.interior M ∩ U, 0 ≤ f x)
    (hf3 : ∀ x ∈ I.boundary M ∩ U, f x = 0) : 0 ≤ d% f p v := by
  by_cases hfp : MDiffAt f p
  · simp [mvfderiv, mfderiv, hfp]
    sorry
  · sorry

def ConvexConeIsInwardPointing (p : M) : ConvexCone ℝ (TangentSpace I p) where
  carrier v := IsInwardPointingTry5Local v
  smul_mem' c hc v := by
    intro ⟨f, U, hU, hpU, hf1, hf2, hf3, hf4⟩
    use f, U, hU, hpU, hf1, hf2, hf3
    simp [hf4, hc]
  add_mem' := by
    intro v ⟨f, U, hU, hpU, hf1, hf2, hf3, hf4⟩ w ⟨g, V, hV, hpV, hg1, hg2, hg3, hg4⟩
    use f + g, U ∩ V, hU.inter hV, ⟨hpU, hpV⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (hf1.mono inter_subset_left).add (hg1.mono inter_subset_right)
    · intro x ⟨hx1, hx2, hx3⟩
      exact add_pos (hf2 x ⟨hx1, hx2⟩) (hg2 x ⟨hx1, hx3⟩)
    · intro x ⟨hx1, hx2, hx3⟩
      simp [hf3 x ⟨hx1, hx2⟩, hg3 x ⟨hx1, hx3⟩]
    · simp
      --rw [mvfderiv_fun_add]
      sorry
