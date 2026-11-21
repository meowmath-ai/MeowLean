import JSP000930AnalyticComplexWitness

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis JSP000930.Positive

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem typedComplexFunction_totalComplex {n : ℕ} (v : DVec (V B) n)
    (G A : STerm n) (x : bSet B) (p : B)
    (hG : p ≤ bTruth v (typedComplexFunctionOn_f G A))
    (hx : p ≤ x ∈ᴮ bTerm v A) :
    ∃ z : ComplexBits B, z.CutOn p ∧ p ≤ bSet.pair x z.name ∈ᴮ bTerm v G := by
  let vx : DVec (V B) (n+1) := DVec.cons x v
  let X : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let Z : STerm (n+2) := imagCoordinate_f
  let M : SForm (n+2) := bd_and (complex_f Z)
    (bd_and (value_f (up2 G) (up X) Z) (sAll (fun w =>
      bd_imp (value_f (up3 G) (up2 X) w) (bd_equal (up Z) w))))
  let F (w : bSet B) : B := bTruth (DVec.cons w vx) M
  have hTot := hG
  simp only [typedComplexFunctionOn_f,bTruth_and_eq] at hTot
  have hs := hTot.trans inf_le_right
  rw [bTruth_allIn_r181] at hs
  have htx := hs.trans (iInf_le _ x)
  rw [← _root_.deduction] at htx
  have hh := (le_inf le_rfl hx).trans htx
  change p ≤ bTruth vx (sEx fun _ => M) at hh
  rw [bTruth_sEx_r181] at hh
  have hh' : p ≤ ⨆ w : bSet B, F w := hh
  obtain ⟨w,hw⟩ := bSet.maximum_principle F (bTruth_body_ext_r191 vx M)
  have hv := hh'.trans hw.le
  let vz : DVec (V B) (n+2) := DVec.cons w vx
  change p ≤ bTruth vz M at hv
  simp only [M,bTruth_and_eq] at hv
  obtain ⟨z,hz,he⟩ := complexBits_of_forcedName vz Z p (hv.trans inf_le_left)
  have hwEq : p ≤ w =ᴮ z.name := by
    exact he
  have hm : p ≤ bSet.pair x w ∈ᴮ bTerm v G := by
    have hval : p ≤ bTruth vz (value_f (up2 G) (up X) Z) :=
      hv.trans (inf_le_right.trans inf_le_left)
    rw [bTruth_value,bTerm_up2_r181 v x w G,
      (bTerm_up_r181 vx w X).trans (bTerm_current_r181 v x)] at hval
    exact hval
  exact ⟨z,hz,bSet.subst_congr_mem_left' (bSet.pair_congr (le_top.trans bSet.bv_refl) hwEq) hm⟩

theorem typedComplexFunction_functional {n : ℕ} (v : DVec (V B) n)
    (G A : STerm n) (p : B) (hG : p ≤ bTruth v (typedComplexFunctionOn_f G A)) :
    p ≤ bSet.is_func (bTerm v G) := by
  have h := hG.trans (typedComplexFunction_le_native v G A)
  exact typedGraph_func (h.trans inf_le_left) (h.trans inf_le_right)

end JSP000930.AnalyticSyntax
