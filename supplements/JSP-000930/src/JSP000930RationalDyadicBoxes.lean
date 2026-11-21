import JSP000930PositiveRationalDyadicCylinders
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace JSP000930.Negative.Cohen

open JSP000930.Positive.Dyadic

theorem follow_inside_neighborhood (s : Interval) {x ε : ℝ}
    (hL : (s.left : ℝ) < x) (hR : x < (s.right : ℝ)) (hε : 0 < ε) :
    ∃ w : List Bool, x - ε < ((s.follow w).left : ℝ) ∧
      ((s.follow w).right : ℝ) < x + ε := by
  have hl : max (s.left : ℝ) (x - ε) < x := max_lt_iff.mpr ⟨hL, by linarith⟩
  have hr : x < min (s.right : ℝ) (x + ε) := lt_min hR (by linarith)
  obtain ⟨q, hql, hqx⟩ := exists_rat_btwn hl
  obtain ⟨a, haL, haq⟩ := exists_rat_btwn hql
  obtain ⟨b, hxb, hbR⟩ := exists_rat_btwn hr
  have hqa : a < q := by exact_mod_cast haq
  have hqb : q < b := by exact_mod_cast hqx.trans hxb
  have hLq : s.left ≤ q := by
    exact_mod_cast ((le_max_left (s.left : ℝ) (x - ε)).trans hql.le)
  have hRq : q ≤ s.right := by
    exact_mod_cast ((hqx.trans (hr.trans_le (min_le_left _ _))).le)
  obtain ⟨w, hwL, hwR⟩ := exists_descendant_inside s a q b hqa hqb hLq hRq
  have hwL' : (a : ℝ) < ((s.follow w).left : ℝ) := by exact_mod_cast hwL
  have hwR' : ((s.follow w).right : ℝ) < (b : ℝ) := by exact_mod_cast hwR
  exact ⟨w, (le_max_right _ _).trans_lt (haL.trans hwL'),
    hwR'.trans (hbR.trans_le (min_le_right _ _))⟩

def dyadicOpenBox {J : Type*} (s : J → Interval) : Set (J → ℝ) :=
  ⋂ j, (fun x : J → ℝ => x j) ⁻¹' Set.Ioo ((s j).left : ℝ) ((s j).right : ℝ)

def dyadicClosedBox {J : Type*} (s : J → Interval) : Set (J → ℝ) :=
  {x | ∀ j, ((s j).left : ℝ) ≤ x j ∧ x j ≤ ((s j).right : ℝ)}

theorem isOpen_dyadicOpenBox {J : Type*} [Finite J] (s : J → Interval) :
    IsOpen (dyadicOpenBox s) :=
  isOpen_iInter_of_finite (fun j => isOpen_Ioo.preimage (continuous_apply j))

theorem dyadicOpenBox_nonempty {J : Type*} (s : J → Interval) :
    (dyadicOpenBox s).Nonempty := by
  refine ⟨fun j => ((s j).mid : ℝ), Set.mem_iInter.mpr ?_⟩
  intro j
  change ((s j).left : ℝ) < ((s j).mid : ℝ) ∧
    ((s j).mid : ℝ) < ((s j).right : ℝ)
  have hL : (s j).left < (s j).mid := by unfold Interval.mid; linarith [(s j).positive]
  have hR : (s j).mid < (s j).right := by unfold Interval.mid; linarith [(s j).positive]
  exact ⟨by exact_mod_cast hL, by exact_mod_cast hR⟩

theorem exists_vector_append_box_subset {J : Type*} [Fintype J]
    (s : J → Interval) (u : J → List Bool) {U : Set (J → ℝ)}
    (hU : IsOpen U) (hD : Dense U) :
    ∃ v : J → List Bool,
      dyadicClosedBox (fun j => (s j).follow (u j ++ v j)) ⊆ U := by
  classical
  let t := fun j => (s j).follow (u j)
  obtain ⟨x, hxU, hxt⟩ := hD.exists_mem_open (isOpen_dyadicOpenBox t)
    (dyadicOpenBox_nonempty t)
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU x hxU
  have hEach : ∀ j, ∃ v : List Bool,
      x j - ε < (((t j).follow v).left : ℝ) ∧
      (((t j).follow v).right : ℝ) < x j + ε := by
    intro j
    have hxj : ((t j).left : ℝ) < x j ∧ x j < ((t j).right : ℝ) :=
      Set.mem_iInter.mp hxt j
    exact follow_inside_neighborhood (t j) hxj.1 hxj.2 hε
  choose v hv using hEach
  refine ⟨v, fun y hy => hεU ?_⟩
  change dist y x < ε
  apply (dist_pi_lt_iff hε).mpr
  intro j
  have hyj := hy j
  have hY : (((t j).follow (v j)).left : ℝ) ≤ y j ∧
      y j ≤ (((t j).follow (v j)).right : ℝ) := by
    simpa only [t, Interval.follow_append] using hyj
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith [(hv j).1, hY.1], by linarith [(hv j).2, hY.2]⟩

end JSP000930.Negative.Cohen
