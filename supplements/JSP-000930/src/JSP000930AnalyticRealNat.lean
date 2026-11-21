import JSP000930AnalyticRealNeg
import JSP000930AnalyticRealAxisName

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

def RatPresentation.ofNat (k : ℕ) : RatPresentation := ⟨k,0,1,by decide⟩

@[simp] theorem RatPresentation.ofNat_value (k : ℕ) :
    (RatPresentation.ofNat k).value = k := by
  simp [RatPresentation.ofNat,RatPresentation.value]

end JSP000930.BooleanAnalysis

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames JSP000933.CantorCodes

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_rationalNat_checked {n : ℕ} (v : DVec (V B) n) (K Q : STerm n)
    (k : ℕ) (hK : bTerm v K = bSet.of_nat k) :
    bTruth v (rationalNat_f K Q) = (bTerm v Q =ᴮ ratName (RatPresentation.ofNat k)) := by
  have hw : bTerm v (omega : STerm n) = bSet.omega := rfl
  simp only [rationalNat_f,boolean_realize_bounded_formula_and,
    boolean_realize_bounded_formula_mem',hw,hK,
    bTruth_exOmega_r192,show ((bSet.of_nat k : bSet B) ∈ᴮ bSet.omega) = ⊤
      from top_unique bSet.omega_definite,top_inf_eq]
  let t : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let w (i : ℕ) : DVec (V B) (n+1) := DVec.cons (bSet.of_nat i) v
  have hs (i : ℕ) : bTruth (w i) (successor_f zero t) = crispTruth B (i = 1) :=
    bTruth_successor_twoChecked_r192 (w i) zero t 0 i
      (bTerm_zero_checked_r192 _) (bTerm_current_r181 v (bSet.of_nat i))
  have hQ' (i : ℕ) : bTerm (w i) (up Q) = bTerm v Q := bTerm_up_r181 v (bSet.of_nat i) Q
  have hK' (i : ℕ) : bTerm (w i) (up K) = bSet.of_nat k :=
    (bTerm_up_r181 v (bSet.of_nat i) K).trans hK
  have ht (i : ℕ) : bTerm (w i) t = bSet.of_nat i := bTerm_current_r181 v (bSet.of_nat i)
  have hp (i : ℕ) : bTerm (w i) (pair' (up K) (pair' zero t)) =
      bSet.pair (bSet.of_nat k) (bSet.pair (bSet.of_nat 0) (bSet.of_nat i)) := by
    calc
      _ = bSet.pair (bTerm (w i) (up K)) (bTerm (w i) (pair' zero t)) :=
        boolean_realize_bounded_term_pair' (v := w i) (up K) (pair' zero t)
      _ = bSet.pair (bSet.of_nat k) (bSet.pair (bTerm (w i) zero) (bTerm (w i) t)) :=
        congrArg₂ bSet.pair (hK' i) (boolean_realize_bounded_term_pair' (v := w i) zero t)
      _ = _ := congrArg (bSet.pair (bSet.of_nat k))
        (congrArg₂ bSet.pair (bTerm_zero_checked_r192 (w i)) (ht i))
  change (⨆ i : ℕ, bTruth (w i) (successor_f zero t) ⊓
    bTruth (w i) (bd_equal (up Q) (pair' (up K) (pair' zero t)))) = _
  simp only [bTruth_equal_r181, hs, hQ', hp, iSup_crispEquality_select_r193,
    ratName, RatPresentation.ofNat]

theorem bTruth_realNat_weighted {n : ℕ} (v : DVec (V B) n) (K X : STerm n)
    (k : ℕ) (β : RatPresentation → B) (hK : bTerm v K = bSet.of_nat k)
    (hX : bTerm v X = weightedRationalSet β) :
    bTruth v (realNat_f K X) =
      (weightedRationalSet β =ᴮ weightedRationalSet (checkedRealBits (k : ℝ))) := by
  simp only [realNat_f,bTruth_rationalEx,weightedRationalSet_eq_bitEq]
  let d := RatPresentation.ofNat k
  let body (r : RatPresentation) : B :=
    bTruth (DVec.cons (ratName (B := B) r) v) (rationalAll_f fun q =>
      bd_biimp (mem' q (up2 X)) (rationalLT_f q (up (bd_var ⟨0,Nat.succ_pos n⟩))))
  change (⨆ r : RatPresentation, bTruth (DVec.cons (ratName r) v)
    (bd_and (rationalNat_f (up K) (bd_var ⟨0,Nat.succ_pos n⟩))
       (rationalAll_f fun q =>
         bd_biimp (mem' q (up2 X)) (rationalLT_f q (up (bd_var ⟨0,Nat.succ_pos n⟩)))))) = _
  have hs (r : RatPresentation) :
      bTruth (DVec.cons (ratName r) v) (rationalNat_f (up K) (bd_var ⟨0,Nat.succ_pos n⟩)) =
        crispTruth B (r = d) := by
    have he := bTruth_rationalNat_checked (DVec.cons (ratName r) v) (up K)
      (bd_var ⟨0,Nat.succ_pos n⟩) k ((bTerm_up_r181 v (ratName r) K).trans hK)
    exact he.trans (ratName_eq_crisp r d)
  simp only [boolean_realize_bounded_formula_and,hs]
  change (⨆ r : RatPresentation, crispTruth B (r = d) ⊓ body r) = _
  have hr : (⨆ r : RatPresentation, crispTruth B (r = d) ⊓ body r) = body d := by
    apply le_antisymm
    · refine iSup_le fun r => ?_
      by_cases h : r = d
      · subst r
        simp [crispTruth]
      · simp [crispTruth,h]
    · exact (by simpa [crispTruth] using
        (le_iSup (fun r : RatPresentation => crispTruth B (r = d) ⊓ body r) d))
  rw [hr]
  simp only [body,bTruth_rationalAll,boolean_realize_bounded_formula_biimp,
    equiv_bitEq_r181,boolean_realize_bounded_formula_mem',bTerm_current_r181,bTerm_up2_r181,
    hX,ratName_mem_weightedRationalSet]
  apply iInf_congr
  intro q
  apply congrArg (bitEq (β q))
  let w := DVec.cons (ratName (B := B) q) (DVec.cons (ratName d) v)
  let t : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let s : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  change bTruth w (rationalLT_f s (up t)) = _
  rw [bTruth_rationalLT_named w s (up t) q d (bTerm_current_r181 _ (ratName q))]
  · simp only [checkedRealBits,d,RatPresentation.ofNat_value]
    have he : (q.value < (k : ℚ)) ↔ (q.value : ℝ) < (k : ℝ) := by
      constructor <;> intro hh <;> exact_mod_cast hh
    rw [he]
  · exact (bTerm_up_r181 (DVec.cons (ratName d) v) (ratName q) t).trans
      (bTerm_current_r181 v (ratName d))

end JSP000930.AnalyticSyntax
