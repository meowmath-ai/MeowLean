import JSP000930AnalyticCutMul
import JSP000930AnalyticCutCauchyMetric

open Set Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000933.BooleanNames JSP000933.PositiveForcing

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem intervalBits_checkedReal (x : ℝ) (a b : RatPresentation) :
    intervalBits (checkedRealBits (B := B) x) a b =
      crispTruth B ((a.value : ℝ) < x ∧ x < (b.value : ℝ)) := by
  by_cases hax : (a.value : ℝ) < x
  · unfold intervalBits
    rw [show checkedRealBits (B := B) x a = ⊤ by simp [checkedRealBits,crispTruth,hax],
      top_inf_eq]
    by_cases hxb : x < (b.value : ℝ)
    · simp only [crispTruth, hax, hxb, and_self, ite_true]
      obtain ⟨t0,hx,htb⟩ := exists_rat_btwn hxb
      obtain ⟨t,ht⟩ := ratPresentation_value_surjective t0
      have htr : t.value < b.value := by
        have ht' : (t.value : ℝ) < (b.value : ℝ) := by rw [ht]; exact htb
        exact_mod_cast ht'
      have hnx : ¬ (t.value : ℝ) < x := by rw [ht]; exact not_lt_of_ge hx.le
      apply top_unique
      have hval : (checkedRealBits (B := B) x t)ᶜ = ⊤ := by
        simp [checkedRealBits,crispTruth,hnx]
      exact (le_of_eq hval.symm).trans (le_iSup_of_le t (le_iSup (fun _ : t.value < b.value => (checkedRealBits (B := B) x t)ᶜ) htr))
    · simp only [crispTruth,hax,hxb,and_false,ite_false]
      apply le_bot_iff.mp
      refine iSup_le fun t => iSup_le fun ht => ?_
      have ht' : (t.value : ℝ) < (b.value : ℝ) := by exact_mod_cast ht
      have hx := ht'.trans_le (le_of_not_gt hxb)
      simp [checkedRealBits,crispTruth,hx]
  · simp [intervalBits,checkedRealBits,crispTruth,hax]

theorem exists_small_rationalBox_products {x y : ℝ} {q : RatPresentation}
    (h : (q.value : ℝ) < x*y) :
    ∃ a b c d : RatPresentation,
      (a.value : ℝ) < x ∧ x < (b.value : ℝ) ∧
      (c.value : ℝ) < y ∧ y < (d.value : ℝ) ∧
      belowRectangleProducts q a b c d := by
  let U : Set (ℝ × ℝ) := {p | (q.value : ℝ) < p.1*p.2}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_fst.mul continuous_snd)
  obtain ⟨ε,he,hε⟩ := Metric.isOpen_iff.mp hU (x,y) (show (x,y) ∈ U from h)
  obtain ⟨aa,haa,hax⟩ := exists_rat_btwn (show x-ε < x by linarith)
  obtain ⟨bb,hxb,hbb⟩ := exists_rat_btwn (show x < x+ε by linarith)
  obtain ⟨cc,hcc,hcy⟩ := exists_rat_btwn (show y-ε < y by linarith)
  obtain ⟨dd,hyd,hdd⟩ := exists_rat_btwn (show y < y+ε by linarith)
  obtain ⟨a,ha⟩ := ratPresentation_value_surjective aa
  obtain ⟨b,hb⟩ := ratPresentation_value_surjective bb
  obtain ⟨c,hc⟩ := ratPresentation_value_surjective cc
  obtain ⟨d,hd⟩ := ratPresentation_value_surjective dd
  have hab (z : ℝ) (h₁ : x-ε < z) (h₂ : z < x+ε) : dist z x < ε := by
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  have hcd (z : ℝ) (h₁ : y-ε < z) (h₂ : z < y+ε) : dist z y < ε := by
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  have hxy (v w : ℝ) (hv : dist v x < ε) (hw : dist w y < ε) :
      (q.value : ℝ) < v*w := by
    have hp : (v,w) ∈ Metric.ball (x,y) ε := by
      rw [Metric.mem_ball,Prod.dist_eq]
      exact max_lt hv hw
    exact hε hp
  refine ⟨a,b,c,d,?_,?_,?_,?_,?_⟩
  · rwa [ha]
  · rwa [hb]
  · rwa [hc]
  · rwa [hd]
  · refine ⟨?_,?_,?_,?_⟩
    · rw [ha,hc]
      exact_mod_cast hxy aa cc (hab aa haa (by linarith)) (hcd cc hcc (by linarith))
    · rw [ha,hd]
      exact_mod_cast hxy aa dd (hab aa haa (by linarith)) (hcd dd (by linarith) hdd)
    · rw [hb,hc]
      exact_mod_cast hxy bb cc (hab bb (by linarith) hbb) (hcd cc hcc (by linarith))
    · rw [hb,hd]
      exact_mod_cast hxy bb dd (hab bb (by linarith) hbb) (hcd dd (by linarith) hdd)

theorem mulCutBits_checkedReal (x y : ℝ) (q : RatPresentation) :
    mulCutBits (checkedRealBits (B := B) x) (checkedRealBits y) q =
      checkedRealBits (x*y) q := by
  by_cases h : (q.value : ℝ) < x*y
  · rw [show checkedRealBits (B := B) (x*y) q = ⊤ by simp [checkedRealBits,crispTruth,h]]
    obtain ⟨a,b,c,d,ha,hb,hc,hd,hcorners⟩ := exists_small_rationalBox_products h
    apply top_unique
    unfold mulCutBits
    have htop : intervalBits (checkedRealBits (B := B) x) a b ⊓
        intervalBits (checkedRealBits y) c d = ⊤ := by
      simp [intervalBits_checkedReal,crispTruth,ha,hb,hc,hd]
    exact (le_of_eq htop.symm).trans (le_iSup_of_le a (le_iSup_of_le b
      (le_iSup_of_le c (le_iSup_of_le d (le_iSup (fun _ : belowRectangleProducts q a b c d =>
      intervalBits (checkedRealBits (B := B) x) a b ⊓ intervalBits (checkedRealBits (B := B) y) c d) hcorners)))))
  · rw [show checkedRealBits (B := B) (x*y) q = ⊥ by simp [checkedRealBits,crispTruth,h]]
    apply le_bot_iff.mp
    unfold mulCutBits
    refine iSup_le fun a => iSup_le fun b => iSup_le fun c => iSup_le fun d => iSup_le fun hco => ?_
    by_cases hx : (a.value : ℝ) < x ∧ x < (b.value : ℝ)
    · by_cases hy : (c.value : ℝ) < y ∧ y < (d.value : ℝ)
      · exfalso
        exact h (strictLower_fourCorners hx.1.le hx.2.le hy.1.le hy.2.le
          (by exact_mod_cast hco.1) (by exact_mod_cast hco.2.1)
          (by exact_mod_cast hco.2.2.1) (by exact_mod_cast hco.2.2.2))
      · simp [intervalBits_checkedReal,crispTruth,hy]
    · simp [intervalBits_checkedReal,crispTruth,hx]

end JSP000930.BooleanAnalysis
