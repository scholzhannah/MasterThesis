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
public import Mathlib.Analysis.Calculus.TangentCone.Seq
public import CollarNeighbourhoods.ToMathlib
public import Mathlib.Geometry.Manifold.Instances.Real


/-! Header

Sources:
* "Variational Analysis" by Rockafellar
* `https://arxiv.org/pdf/1810.05999`

-/

@[expose] public noncomputable section

open Set Function Filter Module EuclideanSpace Metric Nat
open scoped Topology Manifold ContDiff

noncomputable section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace 𝕜 E] [LinearOrder 𝕜] [PosMulReflectLT 𝕜] [IsStrictOrderedRing 𝕜]
  [OrderTopology 𝕜]

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

lemma indexSeq_pos {Q : ℕ → ℝ → Prop}
    (hγn : ∀ (n : ℕ), ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)), ∀ j ∈ Ioc 0 i, Q n j) (n : ℕ) :
    0 < decIndexSeq hγn n :=
  (indexSeq_mem_ioc hγn n).1

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

lemma slope_mem_ball {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) (n : ℕ) :
    ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)), ∀ j ∈ Ioc 0 i,
      slope (γ n) 0 j ∈ ball (v n) (1 / (n + 1)) := by
  have hγn : ball (v n) (1 / (n + 1)) ∈ 𝓝 (v n) := by
    rw [isOpen_ball.mem_nhds_iff]
    exact mem_ball_self one_div_pos_of_nat
  have : Tendsto (slope (γ n) 0) (𝓝[>] 0) (𝓝 (v n)) := by
    rw [← Ici_sdiff_left, ← hasDerivWithinAt_iff_tendsto_slope, ← hγv n]
    exact (hγ n).hasDerivWithinAt
  specialize this hγn
  simp_rw [mem_map, mem_nhdsGT_iff_exists_Ioc_subset] at this
  obtain ⟨i, hi, hiγ⟩ := this
  use min i (1 / (n + 1))
  refine ⟨⟨lt_min hi (one_div_pos_of_nat), (min_le_right _ _)⟩, ?_⟩
  intro j hj
  apply hiγ ⟨hj.1, hj.2.trans Std.min_le_left⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma exists_of_eventually_mem {γ : ℕ → ℝ → E} {s : Set E} (n : ℕ)
    (hs : ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s) :
    ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)), ∀ j ∈ Ioc 0 i,
      γ n j ∈ s := by
  simp_rw [eventually_iff_exists_mem, mem_nhdsGE_iff_exists_Icc_subset] at hs
  obtain ⟨v, ⟨i, hi, hiv⟩, hvs⟩ := hs
  use min i (1 / (n + 1))
  refine ⟨⟨lt_min hi (one_div_pos_of_nat), (min_le_right _ _)⟩, ?_⟩
  intro j hj
  exact hvs _ (hiv ⟨hj.1.le, hj.2.trans Std.min_le_left⟩)

lemma exists_slope_and_mem {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {s : Set E} {n : ℕ}
    (hs : ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s) :
    ∃ i ∈ Ioc (0 : ℝ) (1 / (n + 1)), ∀ j ∈ Ioc 0 i,
      slope (γ n) 0 j ∈ ball (v n) (1 / (n + 1)) ∧ γ n j ∈ s := by
  obtain ⟨i1, hi1, hi1γ⟩ := slope_mem_ball hγv hγ n
  obtain ⟨i2, hi2, hi2s⟩ := exists_of_eventually_mem n hs
  use min i1 i2
  refine ⟨⟨lt_min hi1.1 hi2.1, (min_le_right _ _).trans hi2.2⟩ , ?_⟩
  intro j hj
  exact ⟨hi1γ _ ⟨hj.1, hj.2.trans Std.min_le_left⟩, hi2s _ ⟨hj.1, hj.2.trans Std.min_le_right⟩⟩

lemma slope_mem_decIndexSeq {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {s : Set E} {n : ℕ}
    (hs : ∀ n, ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s) {j : ℝ}
    (hj : j ∈ Ioc 0 (decIndexSeq (fun n ↦ exists_slope_and_mem hγv hγ (hs n)) n)) :
    slope (γ n) 0 j ∈ ball (v n) (1 / (n + 1)) :=
  let hγn n := exists_slope_and_mem hγv hγ (hs n)
  (indexSeq_prop hγn n j hj).1

lemma mem_set_decIndexSeq {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {s : Set E} {n : ℕ}
    (hs : ∀ n, ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s) {j : ℝ}
    (hj : j ∈ Ioc 0 (decIndexSeq (fun n ↦ exists_slope_and_mem hγv hγ (hs n)) n)) :
    γ n j ∈ s :=
  let hγn n := exists_slope_and_mem hγv hγ (hs n)
  (indexSeq_prop hγn n j hj).2

open Classical in
def limitFun {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {s : Set E}
    (hs : ∀ n, ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s)
    (p : E) (x : ℝ) : E :=
  letI hγn n := exists_slope_and_mem hγv hγ (hs n)
  if h : ∃ (n : ℕ), x ∈ Ioc (decIndexSeq hγn (n + 1)) (decIndexSeq hγn n) then
        letI n := (Classical.choose h)
        γ n x
      else p

lemma limitFun_of_not_mem_Ioc {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {s : Set E}
    (hs : ∀ n, ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s) (p : E) {x : ℝ}
    (hx : x ∉ Ioc 0 (decIndexSeq (fun n ↦ exists_slope_and_mem hγv hγ (hs n)) 0)) :
    limitFun hγv hγ hs p x = p := by
  have hγn n := exists_slope_and_mem hγv hγ (hs n)
  apply dite_eq_right
  push Not
  intro n hn
  apply hx
  exact ⟨lt_trans (indexSeq_pos hγn (n + 1)) hn.1,
    le_trans hn.2 (antitone_decIndexSeq hγn n.zero_le)⟩

lemma limitFun_zero {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {s : Set E}
    (hs : ∀ n, ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s) (p : E) :
    limitFun hγv hγ hs p 0 = p := by
  apply limitFun_of_not_mem_Ioc
  exact left_notMem_Ioc

def limitFunPoint {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {s : Set E}
    (hs : ∀ n, ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s) {x : ℝ}
    (hx : x ∈ Ioc 0 (decIndexSeq (fun n ↦ exists_slope_and_mem hγv hγ (hs n)) 0)) : ℕ :=
  letI hγn := fun n ↦ exists_slope_and_mem hγv hγ (hs n)
  letI h := existsUnique_between_of_tendsto_atTop_nhds (antitone_decIndexSeq hγn) 0
      (tendsto_decIndexSeq hγn) hx
  Classical.choose h

lemma mem_Ioc_limitFunPoint {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {s : Set E}
    (hs : ∀ n, ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s) {x : ℝ}
    (hx : x ∈ Ioc 0 (decIndexSeq (fun n ↦ exists_slope_and_mem hγv hγ (hs n)) 0)) :
    letI hγn := fun n ↦ exists_slope_and_mem hγv hγ (hs n)
    letI n := limitFunPoint hγv hγ hs hx
    x ∈ Ioc (decIndexSeq hγn (n + 1)) (decIndexSeq hγn n) :=
  let hγn n := exists_slope_and_mem hγv hγ (hs n)
  let h := existsUnique_between_of_tendsto_atTop_nhds (antitone_decIndexSeq hγn) 0
      (tendsto_decIndexSeq hγn) hx
  (Classical.choose_spec h).1

lemma eq_limitFunPoint_of_mem_Ioc {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {s : Set E}
    (hs : ∀ n, ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s) {x : ℝ}
    (hx : x ∈ Ioc 0 (decIndexSeq (fun n ↦ exists_slope_and_mem hγv hγ (hs n)) 0)) {m : ℕ}
    (hxm : x ∈ Ioc (decIndexSeq (fun n ↦ exists_slope_and_mem hγv hγ (hs n)) (m + 1))
      (decIndexSeq (fun n ↦ exists_slope_and_mem hγv hγ (hs n)) m)) :
    m = limitFunPoint hγv hγ hs hx :=
  let hγn := fun n ↦ exists_slope_and_mem hγv hγ (hs n)
  let h := existsUnique_between_of_tendsto_atTop_nhds (antitone_decIndexSeq hγn) 0
      (tendsto_decIndexSeq hγn) hx
  (Classical.choose_spec h).2 m hxm

lemma limitFun_eq_limitFunPoint {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {s : Set E}
    (hs : ∀ n, ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s) (p : E) {x : ℝ}
    (hx : x ∈ Ioc 0 (decIndexSeq (fun n ↦ exists_slope_and_mem hγv hγ (hs n)) 0)) :
    limitFun hγv hγ hs p x = γ (limitFunPoint hγv hγ hs hx) x := by
  have hγn n := exists_slope_and_mem hγv hγ (hs n)
  have h := existsUnique_between_of_tendsto_atTop_nhds (antitone_decIndexSeq hγn) 0
      (tendsto_decIndexSeq hγn) hx
  unfold limitFun
  rw [dite_eq_left h.exists,
    eq_limitFunPoint_of_mem_Ioc hγv hγ hs hx (Classical.choose_spec h.exists)]

lemma limitFun_mem {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {p : E} {s : Set E} (hps : p ∈ s)
    (hs : ∀ n, ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s) (x : ℝ) :
    (limitFun hγv hγ hs p) x ∈ s := by
  by_cases hx : x ∈ Ioc 0 (decIndexSeq (fun n ↦ exists_slope_and_mem hγv hγ (hs n)) 0)
  · rw [limitFun_eq_limitFunPoint hγv hγ hs p hx]
    apply mem_set_decIndexSeq hγv hγ hs
    exact ⟨hx.1, (mem_Ioc_limitFunPoint hγv hγ hs hx).2⟩
  · rw [limitFun_of_not_mem_Ioc hγv hγ hs p hx]
    exact hps

lemma hasDerivWithinAt_limitFun {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {p : E} {s : Set E}
    (hs : ∀ n, ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s)
    (hγp : ∀ (n : ℕ), γ n 0 = p)
    {w : E} (hv : Tendsto v atTop (𝓝 w)) :
    HasDerivWithinAt (limitFun hγv hγ hs p ) w (Ici 0) 0 := by
  have hγn n := exists_slope_and_mem hγv hγ (hs n)
  have hj : ∀ (n : ℕ), ∀ j ∈ Ioc 0 (decIndexSeq hγn n),
    slope (γ n) 0 j ∈ ball (v n) (1 / (↑n + 1)) :=  fun n j hj ↦ slope_mem_decIndexSeq hγv hγ hs hj
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
  simp only [tendsto_nhdsWithin_nhds, gt_iff_lt, mem_Ioi, dist_zero_right, Real.norm_eq_abs, slope,
    sub_zero, limitFun_zero, vsub_eq_sub]
  intro ε hε
  obtain ⟨N1 , hN1⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.1 hv) _ (half_pos hε)
  use decIndexSeq hγn (max N1 N2), (indexSeq_mem_ioc hγn (max N1 N2)).1
  intro x hx0 hxj
  rw [abs_of_pos hx0] at hxj
  have hx : x ∈ Ioc 0 (decIndexSeq (fun n ↦ exists_slope_and_mem hγv hγ (hs n)) 0) :=
    ⟨hx0, hxj.le.trans (antitone_decIndexSeq _ zero_le)⟩
  have hN : max N1 N2 ≤ limitFunPoint hγv hγ hs hx := by
    refine (antitone_decIndexSeq hγn).le_of ?_ hxj.le
    exact mem_Ioc_limitFunPoint hγv hγ hs hx
  apply lt_of_le_of_lt (dist_triangle _ (v (limitFunPoint hγv hγ hs hx)) _)
  rw [limitFun_eq_limitFunPoint hγv hγ hs p hx, ← add_halves ε]
  refine add_lt_add_of_le_of_lt (le_trans ?_ hN1.le) (hN2 _ ((le_max_right _ _).trans hN))
  rw [one_div, ← hγp (limitFunPoint hγv hγ hs hx)]
  specialize hj (limitFunPoint hγv hγ hs hx) x ⟨hx0, (mem_Ioc_limitFunPoint hγv hγ hs hx).2⟩
  simp only [one_div, slope, sub_zero, vsub_eq_sub, mem_ball] at hj
  apply hj.le.trans
  rw [inv_le_inv₀ (cast_add_one_pos (limitFunPoint hγv hγ hs hx)) (cast_add_one_pos N1),
    add_le_add_iff_right 1, cast_le]
  exact (le_max_left _ _).trans hN

lemma differentiableWithinAt_limitFun {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {s : Set E}
    (hs : ∀ n, ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s) {p : E}
    (hγp : ∀ (n : ℕ), γ n 0 = p)
    {w : E} (hv : Tendsto v atTop (𝓝 w)) :
    DifferentiableWithinAt ℝ (limitFun hγv hγ hs p) (Ici 0) 0 :=
  (hasDerivWithinAt_limitFun hγv hγ hs hγp hv).differentiableWithinAt

lemma derivWithin_limitFun {γ : ℕ → ℝ → E} {v : ℕ → E}
    (hγv : ∀ (n : ℕ), (fderivWithin ℝ (γ n) (Ici 0) 0) 1 = v n)
    (hγ : ∀ n, DifferentiableWithinAt ℝ (γ n) (Ici 0) 0) {s : Set E}
    (hs : ∀ n, ∀ᶠ (x : ℝ) in 𝓝[≥] 0, γ n x ∈ s) {p : E}
    (hγp : ∀ (n : ℕ), γ n 0 = p)
    {w : E} (hv : Tendsto v atTop (𝓝 w)) :
    derivWithin (limitFun hγv hγ hs p) (Ici 0) 0 = w :=
  (hasDerivWithinAt_limitFun hγv hγ hs hγp hv).derivWithin (uniqueDiffWithinAt_Ici 0)

variable (𝕜)

def derivableWithinAt (s : Set E) (p : E) (v : E) : Prop :=
   ∃ (γ : 𝕜 → E) (_ : DifferentiableWithinAt 𝕜 γ (Ici 0) 0), γ 0 = p ∧
      derivWithin γ (Ici 0) (0 : 𝕜) = v ∧ ∀ᶠ (x : 𝕜) in 𝓝[≥] 0, γ x ∈ s

-- proof adapted from `https://arxiv.org/pdf/1810.05999`
lemma isClosed_derivable {s : Set E} {p : E} (hp : p ∈ s) :
    IsClosed {v : E | derivableWithinAt ℝ s p v} := by
  classical
  rw [← isSeqClosed_iff_isClosed]
  intro v w h hv
  simp only [derivableWithinAt, exists_and_left, exists_prop, mem_ofPred_eq] at h
  let γ := fun n ↦ Classical.choose (h n)
  have hγp n := (Classical.choose_spec (h n)).1
  have hγ n := (Classical.choose_spec (h n)).2.2.1
  have hγv n := (Classical.choose_spec (h n)).2.1
  have hs n := (Classical.choose_spec (h n)).2.2.2
  suffices ∀ (n : ℕ), ∃ i ∈ Ioi 0, Ioc 0 i ⊆ slope (γ n) 0 ⁻¹' ball (v n) (1 / (n + 1)) from
    ⟨limitFun hγv hγ hs p, differentiableWithinAt_limitFun hγv hγ hs hγp hv,
      limitFun_zero hγv hγ hs p, derivWithin_limitFun hγv hγ hs hγp hv,
      eventually_nhdsWithin_of_forall fun x a ↦ limitFun_mem hγv hγ hp hs x⟩
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

lemma Convex.posTangentConeAt_eq_closure {s : Set E} (hs : Convex ℝ s) {p : E} (hp : p ∈ s) :
    posTangentConeAt s p = closure {v | ∃ (r : ℝ) (_ : r > 0), p + r • v ∈ s} := by
  apply subset_antisymm
  · intro v hv
    obtain ⟨c, d, hd, hdp, hcd⟩ := mem_tangentConeAt_iff_exists_seq.1 hv
    rw [← seqClosure_eq_closure]
    rw [eventually_atTop] at hdp
    obtain ⟨N, hN⟩ := hdp
    use fun n ↦ (c (n + N)) • (d (n + N))
    refine ⟨?_, ?_⟩
    · intro n
      by_cases! hcn : ((c (n + N)) : ℝ) = 0
      · use 1
        simp [hcn, NNReal.smul_def, hp]
      use 1 / c (n + N)
      refine ⟨?_, by simp [NNReal.smul_def, smul_smul, inv_mul_cancel₀ hcn, hN]⟩
      rw [gt_iff_lt, one_div_pos]
      exact lt_of_le_of_ne (c (n + N)).coe_nonneg hcn.symm
    · rw [Filter.tendsto_add_atTop_iff_nat (f := fun n ↦ c n • d n)]
      exact hcd
  · rw [← seqClosure_eq_closure]
    intro v ⟨e, he, hev⟩
    simp only [gt_iff_lt, exists_prop, mem_ofPred_eq] at he
    have he' : ∀ n, ∃ (r : ℝ), 0 < r ∧ p + r • e n ∈ s ∧ ‖r • e n‖ ≤ 1 / (n + 1) := by
      intro n
      obtain ⟨r , hr, hrp⟩ := he n
      by_cases! hen : ‖e n‖ = 0
      · use r
        simp [norm_smul_of_nonneg hr.le, hen, hr, hrp, (cast_add_one_pos n).le]
      use min r ((n + 1) * ‖e n‖)⁻¹
      have h0 : 0 < min r ((↑n + 1) * ‖e n‖)⁻¹ := by
        apply lt_min hr
        rw [inv_pos]
        exact mul_pos (cast_add_one_pos n) (lt_of_le_of_ne (norm_nonneg (e n)) hen.symm)
      refine ⟨h0, ?_, ?_⟩
      · apply hs.add_smul_mem_icc hp hr hrp
        refine ⟨h0.le, min_le_left _ _⟩
      · rw [norm_smul_of_nonneg h0.le (e n), inf_mul₀ (norm_nonneg (e n))]
        apply (min_le_right _ _).trans
        rw [mul_inv_rev, one_div, mul_comm, mul_inv_cancel_left₀ hen]
    let f n := Classical.choose (he' n)
    have hf0 n : 0 < f n := (Classical.choose_spec (he' n)).1
    have hfs n : p + f n • e n ∈ s := (Classical.choose_spec (he' n)).2.1
    have hfe n : ‖f n • e n‖ ≤ 1 / (n + 1) := (Classical.choose_spec (he' n)).2.2
    have hf0' n : 0 < (f n)⁻¹ := by simp [hf0 n]
    let g n : NNReal := ⟨(f n)⁻¹, (hf0' n).le⟩
    rw [mem_tangentConeAt_iff_exists_seq]
    use g, f • e
    refine ⟨?_, Eventually.of_forall hfs, ?_⟩
    · rw [NormedAddCommGroup.tendsto_atTop]
      intro ε hε
      obtain ⟨N , hN⟩ := exists_nat_one_div_lt hε
      use N
      intro n hnN
      rw [sub_zero, Pi.smul_apply']
      apply lt_of_le_of_lt (hfe n) (lt_of_le_of_lt ?_ hN)
      rw [one_div_le_one_div (cast_add_one_pos n) (cast_add_one_pos N), add_le_add_iff_right 1]
      norm_cast
    · refine (tendsto_congr (f₂ := e) ?_).2 hev
      intro n
      simp [NNReal.smul_def, smul_smul, show g n = (f n)⁻¹ by rfl, inv_mul_cancel₀ (hf0 n).ne.symm]

lemma Convex.derivable_of_smul_mem {s : Set E} (hs : Convex ℝ s) {p : E} (hp : p ∈ s)
    {v : E} {r : ℝ} (hr : r > 0) (hrv : p + r • v ∈ s) :
    derivableWithinAt ℝ s p v := by
  use fun i ↦ p + (i • v)
  refine ⟨by fun_prop, by simp, ?_, ?_⟩
  · rw [derivWithin_const_add_fun, derivWithin_smul_const (differentiableWithinAt_fun_id) v,
      derivWithin_id' 0 (Ici 0) (uniqueDiffWithinAt_Ici 0), one_smul]
  · rw [eventually_iff_exists_mem]
    use Icc 0 r, Icc_mem_nhdsGE hr
    intro y hy
    exact hs.add_smul_mem_icc hp hr hrv hy

lemma Convex.derivable_of_mem_posTangentCone {s : Set E} (hs : Convex ℝ s) {p : E} (hp : p ∈ s)
    {v : E} (hv : v ∈ posTangentConeAt s p) :
    derivableWithinAt ℝ s p v := by
  rw [hs.posTangentConeAt_eq_closure hp] at hv
  rw [← mem_ofPred_eq (x := v) (p := derivableWithinAt ℝ s p)]
  suffices closure {v | ∃ (r : ℝ) (_ : r > 0), p + r • v ∈ s} ⊆ {y | derivableWithinAt ℝ s p y} from
    this hv
  apply closure_minimal ?_ (isClosed_derivable hp)
  intro y hy
  obtain ⟨r, hr, hrs⟩ := hy
  exact hs.derivable_of_smul_mem hp hr hrs

lemma Convex.mem_posTangentCone_of_derivable {s : Set E} (hs : Convex ℝ s) {p : E} (hp : p ∈ s)
    {v : E} (hv : derivableWithinAt ℝ s p v) : v ∈ posTangentConeAt s p := by
  rw [hs.posTangentConeAt_eq_closure hp, ← seqClosure_eq_closure]
  obtain ⟨γ, hγ, hγp, hγv, hγs⟩ := hv
  have : HasDerivWithinAt γ v (Ici 0) 0 := hγv ▸ hγ.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left] at this
  simp_rw [eventually_iff_exists_mem, mem_nhdsGE_iff_exists_Icc_subset] at hγs
  obtain ⟨u, ⟨ε, hε, hεu⟩, hus⟩ := hγs
  obtain ⟨N , hN⟩ := exists_nat_one_div_lt hε
  use fun n ↦ slope γ 0 (N + 1 + n)⁻¹
  refine ⟨?_, ?_⟩
  · intro n
    use (N + 1 + n)⁻¹
    have : 0 < (N : ℝ) + 1 + n := by linarith
    simp only [slope, sub_zero, inv_inv, hγp, vsub_eq_sub, inv_smul_smul₀ this.ne.symm,
      add_sub_cancel, gt_iff_lt, inv_pos, this, exists_const]
    refine hus _ (hεu ⟨inv_nonneg.2 this.le, ?_⟩)
    apply le_trans ?_ hN.le
    rw [one_div, inv_le_inv₀ this (cast_add_one_pos N)]
    apply le_add_of_nonneg_right (cast_nonneg' n)
  · rw [tendsto_iff_seq_tendsto] at this
    apply this
    exact tendsto_inv_atTop_nhdsGT_zero.comp
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)

lemma Convex.derivableWithinAt_iff_mem_posTangentConeAt {s : Set E} (hs : Convex ℝ s) {p : E}
    (hp : p ∈ s) {v : E} : derivableWithinAt ℝ s p v ↔ v ∈ posTangentConeAt s p :=
  ⟨mem_posTangentCone_of_derivable hs hp, derivable_of_mem_posTangentCone hs hp⟩

-- `https://hal.science/hal-01552475v1/document` has a characterisation of the interior of the
-- tangent cone

lemma posTangentConeAt_euclideanHalfSpace {n : ℕ} [NeZero n] {p : EuclideanSpace ℝ (Fin n)}
    (hp : p.ofLp 0 = 0) : posTangentConeAt {x | 0 ≤ x.ofLp 0} p = {v | 0 ≤ v.ofLp 0} := by
  rw [EuclideanHalfSpace.convex.posTangentConeAt_eq_closure (by exact hp.ge)]
  suffices {v : EuclideanSpace ℝ (Fin n) | ∃ r, 0 < r ∧ 0 ≤ r * v.ofLp 0} =  {v | 0 ≤ v.ofLp 0} by
    simp [this, hp]
  ext v
  exact ⟨fun ⟨r, hr, hv⟩ ↦ (mul_nonneg_iff_right_nonneg_of_pos hr).1 hv,
    fun hv ↦ ⟨1, zero_lt_one, (one_mul (v.ofLp 0)).symm ▸ hv⟩⟩

lemma derivableWithinAt_iff_euclideanHalfSpace {n : ℕ} [NeZero n] {p : EuclideanSpace ℝ (Fin n)}
    (hp : p.ofLp 0 = 0) {v : EuclideanSpace ℝ (Fin n)} :
    derivableWithinAt ℝ {x | 0 ≤ x.ofLp 0} p v ↔ 0 ≤ v.ofLp 0 := by
  rw [EuclideanHalfSpace.convex.derivableWithinAt_iff_mem_posTangentConeAt hp.ge,
    posTangentConeAt_euclideanHalfSpace hp, mem_ofPred]

lemma interior_posTangentConeAt_euclideanHalfSpace {n : ℕ} [NeZero n] {p : EuclideanSpace ℝ (Fin n)}
    (hp : p.ofLp 0 = 0) :
    interior (posTangentConeAt {x | 0 ≤ x.ofLp 0} p) = {v | 0 < v.ofLp 0} := by
  rw [posTangentConeAt_euclideanHalfSpace hp]
  exact interior_halfSpace 2 0 0

lemma posTangentConeAt_euclideanQuadrant {n : ℕ} [NeZero n] {p : EuclideanSpace ℝ (Fin n)}
    (hp : ∀ i, p.ofLp i = 0) :
    posTangentConeAt {x | ∀ i, 0 ≤ x.ofLp i} p = {v | ∀ i, 0 ≤ v.ofLp i} := by
  rw [EuclideanQuadrant.convex.posTangentConeAt_eq_closure (by exact fun i ↦ (hp i).ge)]
  suffices {v : EuclideanSpace ℝ (Fin n) | ∃ r, 0 < r ∧ ∀ i, 0 ≤ r * v.ofLp i} =
      {v | ∀ i, 0 ≤ v.ofLp i} by
    simp [hp, this]
  ext x
  exact ⟨fun ⟨r, hr, hrx⟩ i ↦ (mul_nonneg_iff_right_nonneg_of_pos hr).1 (hrx i),
    fun hx ↦ ⟨1, zero_lt_one, fun i ↦ (one_mul (x.ofLp i)).symm ▸ (hx i)⟩⟩

lemma derivableWithinAt_iff_euclideanQuadrant {n : ℕ} [NeZero n] {p : EuclideanSpace ℝ (Fin n)}
    (hp : ∀ i, p.ofLp i = 0) {v : EuclideanSpace ℝ (Fin n)} :
    derivableWithinAt ℝ {x | ∀ i, 0 ≤ x.ofLp i} p v ↔ ∀ i, 0 ≤ v.ofLp i := by
  rw [EuclideanQuadrant.convex.derivableWithinAt_iff_mem_posTangentConeAt (fun i ↦ (hp i).ge),
    posTangentConeAt_euclideanQuadrant hp, mem_ofPred]

lemma interior_posTangentConeAt_euclideanQuadrant {n : ℕ} [NeZero n] {p : EuclideanSpace ℝ (Fin n)}
    (hp : ∀ i, p.ofLp i = 0) :
    interior (posTangentConeAt {x | ∀ i, 0 ≤ x.ofLp i} p) = {v | ∀ i, 0 < v.ofLp i} := by
  rw [posTangentConeAt_euclideanQuadrant hp]
  exact interior_euclideanQuadrant n 2 0
