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

@[expose] public noncomputable section

open Set Function Filter Module EuclideanSpace Metric Nat
open scoped Topology Manifold ContDiff

noncomputable section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

lemma exists_between_of_tendsto_atTop_nhds {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIciTopology β] {t : ℕ → β} (b : β) (ht : Tendsto t atTop (𝓝 b)) {x : β}
    (hx : x ∈ Ioc b (t 0)) : ∃ n, x ∈ Ioc (t (n + 1)) (t n) := by
  have h : ∃ n, t (n + 1) < x := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 ( ht.eventually_lt_const hx.1)
    exact ⟨N, hN _ (le_add_right N 1)⟩
  have h' m := Nat.find_min h (m := m)
  simp only [not_lt] at h'
  refine ⟨Nat.find h, ?_⟩
  refine ⟨?_, ?_⟩
  · simp [Nat.find_spec h]
  · by_cases! h0 : Nat.find h = 0
    · simp [h0, hx.2]
    · rw [← sub_one_add_one h0]
      exact h' _ (sub_one_lt h0)

lemma Antitone.le_of {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIciTopology β] {t : ℕ → β} (ht : Antitone t) {n m : ℕ} {x : β}
    (hxn : x ∈ Ioc (t (n + 1)) (t n))
    (hxm : x ≤ t m) : m ≤ n := by
  by_contra! hmn
  suffices t m < t m from (lt_self_iff_false (t m)).mp this
  calc
    t m ≤ t (n + 1) := ht.imp (add_one_le_iff.mpr hmn)
    _ < x := hxn.1
    _ ≤ t m := hxm

lemma existsUnique_between_of_tendsto_atTop_nhds {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIciTopology β] {t : ℕ → β} (ht : Antitone t) (b : β) (htb : Tendsto t atTop (𝓝 b))
    {x : β} (hx : x ∈ Ioc b (t 0)) : ∃! n, x ∈ Ioc (t (n + 1)) (t n) := by
  unfold ExistsUnique
  obtain ⟨n, hn⟩ := exists_between_of_tendsto_atTop_nhds b htb hx
  use n, hn
  intro y hy
  by_contra! hyn
  wlog hyn' :  y < n generalizing n y
  · exact this y hy n hn hyn.symm (lt_of_le_of_ne (not_lt.mp hyn') hyn.symm)
  · suffices n ≤ y by linarith
    exact ht.le_of hy hn.2

def decIndexSeq {Q : ℕ → ℝ → Prop}
    (hγn : ∀ (n : ℕ), ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)), ∀ j ∈ Ioc 0 i, Q n j) :
    ℕ → ℝ
  | 0 => Classical.choose (hγn 0)
  | n + 1 => min (decIndexSeq hγn n / 2) (Classical.choose (hγn (n + 1)))

lemma indexSeq_mem_ioc {Q : ℕ → ℝ → Prop}
    (hγn : ∀ (n : ℕ), ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)), ∀ j ∈ Ioc 0 i, Q n j) (n : ℕ) :
    decIndexSeq hγn n ∈ Ioc (0 : ℝ) (1 / (n + 1)) := match n with
  | 0 => (Classical.choose_spec (hγn 0)).1
  | n + 1 => by
    unfold decIndexSeq
    refine ⟨?_, ?_⟩
    · apply lt_min ?_ (Classical.choose_spec (hγn (n + 1))).1.1
      rw [div_pos_iff_of_pos_right zero_lt_two]
      exact (indexSeq_mem_ioc hγn n).1
    · apply inf_le_of_right_le
      exact (Classical.choose_spec (hγn (n + 1))).1.2

lemma indexSeq_prop {Q : ℕ → ℝ → Prop}
    (hγn : ∀ (n : ℕ), ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)), ∀ j ∈ Ioc 0 i, Q n j) (n : ℕ) :
    ∀ j ∈ Ioc 0 (decIndexSeq hγn n), Q n j := match n with
  | 0 => (Classical.choose_spec (hγn 0)).2
  | n + 1 => by
    intro j hj
    exact (Classical.choose_spec (hγn (n + 1))).2  _ ⟨hj.1, hj.2.trans Std.min_le_right⟩

lemma antitone_decIndexSeq {Q : ℕ → ℝ → Prop}
    (hγn : ∀ (n : ℕ), ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)), ∀ j ∈ Ioc 0 i, Q n j) :
    Antitone (decIndexSeq hγn) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (min_le_left _ _).trans (half_le_self (indexSeq_mem_ioc hγn n).1.le)

lemma tendsto_decIndexSeq {Q : ℕ → ℝ → Prop}
    (hγn : ∀ (n : ℕ), ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)), ∀ j ∈ Ioc 0 i, Q n j) :
    Tendsto (decIndexSeq hγn) atTop (𝓝 0) := by
  rw [NormedAddCommGroup.tendsto_atTop]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  use n
  intro m hm
  simp only [sub_zero, Real.norm_eq_abs, abs_of_pos (indexSeq_mem_ioc hγn m).1]
  apply lt_of_le_of_lt (antitone_decIndexSeq hγn hm)
  exact lt_of_le_of_lt (indexSeq_mem_ioc hγn n).2 hn

-- proof adapted from `https://arxiv.org/pdf/1810.05999`
lemma isClosed_derivable' {s : Set E} (hs : IsClosed s) {p : E} (hp : p ∈ s) :
    IsClosed {v : E |
      ∃ (γ : ℝ → E) (_ : DifferentiableWithinAt ℝ γ (Ici 0) 0), γ 0 = p ∧
      derivWithin γ (Ici 0) (0 : ℝ) = v} := by
  classical
  rw [← isSeqClosed_iff_isClosed]
  -- I need to pick the `v` such that they converge quickly enough
  intro v w h hv
  simp only [exists_and_left, exists_prop, mem_ofPred_eq] at h
  let γ := fun n ↦ Classical.choose (h n)
  have hγp : ∀ n, γ n 0 = p := fun n ↦ (Classical.choose_spec (h n)).1
  have hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0 :=
    fun n ↦ (Classical.choose_spec (h n)).2.1
  have hγv : ∀ n, (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n :=
    fun n ↦ (Classical.choose_spec (h n)).2.2
  have hγnp : ∀ (n : ℕ), ∃ i ∈ Ioi 0, Ioc 0 i ⊆ slope (γ n) 0 ⁻¹' ball (v n) (1 / (n + 1)) := by
    intro n
    have hγn : ball (v n) (1 / (n + 1)) ∈ 𝓝 (v n) := by
      rw [isOpen_ball.mem_nhds_iff]
      exact mem_ball_self one_div_pos_of_nat
    have : Tendsto (slope (γ n) 0) (𝓝[>] 0) (𝓝 (v n)) := by
      rw [← Ici_sdiff_left, ← hasDerivWithinAt_iff_tendsto_slope, ← hγv n]
      exact (hγ n).hasDerivWithinAt
    specialize this hγn
    simp_rw [mem_map, mem_nhdsGT_iff_exists_Ioc_subset] at this
    exact this
  have hγn' : ∀ (n : ℕ), ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)),
      Icc 0 i ⊆ γ n ⁻¹' ball p (1 / (n + 1)) := by
    intro n
    have : ContinuousWithinAt (γ n) (Ici 0) 0 := (hγ n).continuousWithinAt
    have hγn : Metric.ball p (1 / (n + 1)) ∈ 𝓝 (γ n 0) := by
      rw [Metric.isOpen_ball.mem_nhds_iff, hγp]
      exact mem_ball_self one_div_pos_of_nat
    specialize this hγn
    rw [mem_map, mem_nhdsGE_iff_exists_Icc_subset] at this
    obtain ⟨i, hi0, hiγ⟩ := this
    use min i (1 / (n + 1))
    refine ⟨⟨?_, Std.min_le_right⟩, subset_trans (Icc_subset_Icc_right Std.min_le_left) hiγ ⟩
    rw [lt_inf_iff]
    exact ⟨hi0, one_div_pos_of_nat⟩
  have hγn : ∀ (n : ℕ), ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)), ∀ j ∈ Ioc 0 i,
      j ∈ slope (γ n) 0 ⁻¹' ball (v n) (1 / (n + 1)) ∩ γ n ⁻¹' ball p (1 / (n + 1)) := by
    intro n
    obtain ⟨i, hi, hiv⟩ := hγnp n
    obtain ⟨j, hj, hjp⟩ := hγn' n
    use min i j
    refine ⟨?_, subset_inter_iff.mpr ⟨?_, ?_⟩⟩
    · exact ⟨lt_min hi hj.1, (min_le_right _ _).trans hj.2⟩
    · exact subset_trans (Ioc_subset_Ioc_right Std.min_le_left) hiv
    · exact subset_trans (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right Std.min_le_right)) hjp
  have hj1 := fun n j (hj : j ∈ Ioc 0 (decIndexSeq hγn n)) ↦ (indexSeq_prop hγn n j hj).1
  have hj2 := fun n j (hj : j ∈ Ioc 0 (decIndexSeq hγn n)) ↦ (indexSeq_prop hγn n j hj).2
  let δ : ℝ → E := fun x ↦
      if h : ∃ (n : ℕ), x ∈ Ioc (decIndexSeq hγn (n + 1)) (decIndexSeq hγn n) then
        letI n := (Classical.choose h)
        γ n x
      else p
  use δ
  have hδ0 : δ 0 = p := by
    apply dif_neg
    push Not
    exact fun n ↦ notMem_Ioc_of_le (indexSeq_mem_ioc hγn (n + 1)).1.le
  suffices HasDerivWithinAt δ w (Ici 0) 0 from
    ⟨this.differentiableWithinAt, hδ0,  this.derivWithin (uniqueDiffWithinAt_Ici 0)⟩
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
  unfold slope
  simp only [sub_zero, hδ0, vsub_eq_sub, tendsto_nhdsWithin_nhds, gt_iff_lt, mem_Ioi,
    dist_zero_right, Real.norm_eq_abs]
  intro ε hε
  obtain ⟨N1 , hN1⟩ := exists_nat_one_div_lt (half_pos hε)
  rw [Metric.tendsto_atTop] at hv
  obtain ⟨N2 , hN2⟩ := hv _ (half_pos hε)
  use decIndexSeq hγn (max N1 N2), (indexSeq_mem_ioc hγn (max N1 N2)).1
  intro x hx0 hxj
  rw [abs_of_pos hx0] at hxj
  unfold δ
  -- we also need to show that this `n` is unique
  have h : ∃! n, x ∈ Ioc (decIndexSeq hγn (n + 1)) (decIndexSeq hγn n) := by
    apply existsUnique_between_of_tendsto_atTop_nhds (antitone_decIndexSeq hγn) 0
      (tendsto_decIndexSeq hγn)
    refine ⟨hx0, ?_⟩
    apply hxj.le.trans
    exact antitone_decIndexSeq hγn (Nat.zero_le _)
  have h' := h.exists
  obtain ⟨n, hn, hn'⟩ := h
  have hN : max N1 N2 ≤ n := (antitone_decIndexSeq hγn).le_of hn hxj.le
  rw [dif_pos h']
  rw [hn' (Classical.choose h') (Classical.choose_spec h')]
  simp [mem_preimage, mem_ball, slope, hγp] at hj1
  apply lt_of_le_of_lt (dist_triangle _ (v n) _)
  rw [← add_halves ε]
  apply add_lt_add_of_le_of_lt
  · sorry
  · sorry
