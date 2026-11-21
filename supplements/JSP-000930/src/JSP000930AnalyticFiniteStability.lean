import JSP000930AnalyticRealIntervalCertificate
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Data.Fintype.BigOperators

open Set
open scoped BigOperators

namespace JSP000930.Analytic

private noncomputable def finiteCoeffValue {N : ℕ} (f : Fin N → ℂ) (z : ℂ) : ℂ :=
  ∑ i : Fin N, f i * z^i.val

private theorem finiteCoeffValue_eq {N : ℕ} (f : ℕ → ℂ) (z : ℂ) :
    finiteCoeffValue (fun i : Fin N => f i.val) z = partialSum f z N :=
  Fin.sum_univ_eq_sum_range (fun j => f j * z^j) N

theorem finiteSeparation_stable {a b : ℕ → ℂ} {z : ℂ} {R A B N : ℕ}
    (hR : ‖z‖ < (R : ℝ)/2)
    (hGap : tailBudget A N + tailBudget B N <
      ‖partialSum a z N - partialSum b z N‖) :
    ∃ δ > (0 : ℝ), ∀ (a' b' : ℕ → ℂ) (z' : ℂ),
      (∀ i < N, dist (a' i) (a i) < δ) →
      (∀ i < N, dist (b' i) (b i) < δ) →
      dist z' z < δ →
      ‖z'‖ < (R : ℝ)/2 ∧ tailBudget A N + tailBudget B N <
        ‖partialSum a' z' N - partialSum b' z' N‖ := by
  let P := (Fin N → ℂ) × ((Fin N → ℂ) × ℂ)
  let A0 : P → ℂ := fun p => finiteCoeffValue p.1 p.2.2
  let B0 : P → ℂ := fun p => finiteCoeffValue p.2.1 p.2.2
  let Z0 : P → ℂ := fun p => p.2.2
  have hz : Continuous Z0 := continuous_snd.comp continuous_snd
  have ha : Continuous A0 := by
    unfold A0 finiteCoeffValue
    exact continuous_finsetSum Finset.univ
      (fun i _ => ((continuous_apply i).comp continuous_fst).mul (hz.pow i.val))
  have hb : Continuous B0 := by
    unfold B0 finiteCoeffValue
    exact continuous_finsetSum Finset.univ
      (fun i _ => ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).mul
        (hz.pow i.val))
  let U : Set P := {p | ‖Z0 p‖ < (R : ℝ)/2 ∧
    tailBudget A N + tailBudget B N < ‖A0 p - B0 p‖}
  have hu : IsOpen U := (isOpen_lt (continuous_norm.comp hz) continuous_const).inter
    (isOpen_lt continuous_const (continuous_norm.comp (ha.sub hb)))
  let p : P := (fun i : Fin N => a i.val,fun i : Fin N => b i.val,z)
  have hp : p ∈ U := by
    change ‖z‖ < (R : ℝ)/2 ∧ tailBudget A N + tailBudget B N <
      ‖finiteCoeffValue (fun i : Fin N => a i.val) z -
         finiteCoeffValue (fun i : Fin N => b i.val) z‖
    simpa only [finiteCoeffValue_eq] using And.intro hR hGap
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hu p hp
  refine ⟨δ,hδ,?_⟩
  intro a' b' z' ha' hb' hz'
  let p' : P := (fun i : Fin N => a' i.val,fun i : Fin N => b' i.val,z')
  have hp' : p' ∈ Metric.ball p δ := by
    rw [Metric.mem_ball,Prod.dist_eq,Prod.dist_eq]
    exact max_lt ((dist_pi_lt_iff hδ).2 (fun i : Fin N => ha' i i.isLt))
      (max_lt ((dist_pi_lt_iff hδ).2 (fun i : Fin N => hb' i i.isLt)) hz')
  have hr := hball hp'
  change ‖z'‖ < (R : ℝ)/2 ∧ tailBudget A N + tailBudget B N <
    ‖finiteCoeffValue (fun i : Fin N => a' i.val) z' -
       finiteCoeffValue (fun i : Fin N => b' i.val) z'‖ at hr
  simpa only [finiteCoeffValue_eq] using hr

end JSP000930.Analytic
