import JSP000930AnalyticRealAdd
import JSP000930AnalyticCutMul

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames JSP000933.CantorCodes

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_rationalInterval_weighted {n : ℕ} (v : DVec (V B) n)
    (L X R : STerm n) (β : RatPresentation → B) (a b : RatPresentation)
    (hL : bTerm v L = ratName a) (hR : bTerm v R = ratName b)
    (hX : bTerm v X = weightedRationalSet β) :
    bTruth v (rationalIntervalContainsReal_f L X R) = intervalBits β a b := by
  simp only [rationalIntervalContainsReal_f,boolean_realize_bounded_formula_and,
    boolean_realize_bounded_formula_mem',hL,hX,ratName_mem_weightedRationalSet,
    bTruth_rationalEx,boolean_realize_bounded_formula_not,bTerm_current_r181,bTerm_up_r181]
  change β a ⊓ (⨆ t : RatPresentation, bTruth (DVec.cons (ratName t) v)
    (rationalLT_f (bd_var ⟨0,Nat.succ_pos n⟩) (up R)) ⊓ (β t)ᶜ) = _
  unfold intervalBits
  apply congrArg (fun x : B => β a ⊓ x)
  apply iSup_congr
  intro t
  rw [bTruth_rationalLT_named (DVec.cons (ratName t) v)
    (bd_var ⟨0,Nat.succ_pos n⟩) (up R) t b (bTerm_current_r181 v (ratName t))
    ((bTerm_up_r181 v (ratName t) R).trans hR), inf_comm, iSup_inf_crisp_ratLower]

theorem bTruth_belowProduct_named {n : ℕ} (v : DVec (V B) n)
    (Q X Y : STerm n) (q a b : RatPresentation)
    (hQ : bTerm v Q = ratName q) (hX : bTerm v X = ratName a) (hY : bTerm v Y = ratName b) :
    bTruth v (belowProduct_f Q X Y) = crispTruth B (q.value < a.value*b.value) := by
  rw [belowProduct_f,bTruth_rationalEx,← iSup_ratCrisp_result (B := B) (a.value*b.value) q.value]
  apply iSup_congr
  intro t
  let Vt : DVec (V B) (n+1) := DVec.cons (ratName (B := B) t) v
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  have ht : bTerm Vt T = ratName t := bTerm_current_r181 v (ratName t)
  have ha : bTerm Vt (up X) = ratName a := (bTerm_up_r181 v (ratName t) X).trans hX
  have hb : bTerm Vt (up Y) = ratName b := (bTerm_up_r181 v (ratName t) Y).trans hY
  have hq : bTerm Vt (up Q) = ratName q := (bTerm_up_r181 v (ratName t) Q).trans hQ
  change bTruth Vt (bd_and (rationalMul_f (up X) (up Y) T)
    (rationalLT_f (up Q) T)) = _
  have hAnd : bTruth Vt (bd_and (rationalMul_f (up X) (up Y) T) (rationalLT_f (up Q) T)) =
      bTruth Vt (rationalMul_f (up X) (up Y) T) ⊓ bTruth Vt (rationalLT_f (up Q) T) :=
    boolean_realize_bounded_formula_and
  rw [hAnd, bTruth_rationalMul_named Vt (up X) (up Y) T a b t ha hb ht,
    bTruth_rationalLT_named Vt (up Q) T q t hq ht]

private theorem crispConj (P Q : Prop) [Decidable P] [Decidable Q] :
    crispTruth B P ⊓ crispTruth B Q = crispTruth B (P ∧ Q) := by
  by_cases h : P <;> by_cases h' : Q <;> simp [crispTruth,h,h']

theorem bTruth_realMulApprox_weighted {n : ℕ} (v : DVec (V B) n)
    (X Y Q : STerm n) (u w : RatPresentation → B) (q : RatPresentation)
    (hX : bTerm v X = weightedRationalSet u) (hY : bTerm v Y = weightedRationalSet w)
    (hQ : bTerm v Q = ratName q) :
    bTruth v (realMulApprox_f X Y Q) = mulCutBits u w q := by
  simp only [realMulApprox_f,bTruth_rationalEx,mulCutBits]
  apply iSup_congr
  intro a
  apply iSup_congr
  intro b
  apply iSup_congr
  intro c
  apply iSup_congr
  intro d
  let va : DVec (V B) (n+1) := DVec.cons (ratName (B := B) a) v
  let vb : DVec (V B) (n+2) := DVec.cons (ratName (B := B) b) va
  let vc : DVec (V B) (n+3) := DVec.cons (ratName (B := B) c) vb
  let vd : DVec (V B) (n+4) := DVec.cons (ratName (B := B) d) vc
  let A0 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let B0 : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let C0 : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  let D0 : STerm (n+4) := bd_var ⟨0,Nat.succ_pos (n+3)⟩
  let A := up3 A0
  let E := up2 B0
  let C := up C0
  let D := D0
  let X' := up2 (up2 X)
  let Y' := up2 (up2 Y)
  let Q' := up2 (up2 Q)
  have ha : bTerm vd A = ratName a := rfl
  have hb : bTerm vd E = ratName b := rfl
  have hc : bTerm vd C = ratName c := rfl
  have hd : bTerm vd D = ratName d := bTerm_current_r181 vc (ratName d)
  have hx : bTerm vd X' = weightedRationalSet u :=
    (bTerm_up2_r181 vb (ratName c) (ratName d) (up2 X)).trans
      ((bTerm_up2_r181 v (ratName a) (ratName b) X).trans hX)
  have hy : bTerm vd Y' = weightedRationalSet w :=
    (bTerm_up2_r181 vb (ratName c) (ratName d) (up2 Y)).trans
      ((bTerm_up2_r181 v (ratName a) (ratName b) Y).trans hY)
  have hq : bTerm vd Q' = ratName q :=
    (bTerm_up2_r181 vb (ratName c) (ratName d) (up2 Q)).trans
      ((bTerm_up2_r181 v (ratName a) (ratName b) Q).trans hQ)
  change bTruth vd (bd_and (rationalIntervalContainsReal_f A X' E)
    (bd_and (rationalIntervalContainsReal_f C Y' D)
      (bd_and (belowProduct_f Q' A C) (bd_and (belowProduct_f Q' A D)
        (bd_and (belowProduct_f Q' E C) (belowProduct_f Q' E D)))))) = _
  simp only [boolean_realize_bounded_formula_and,
    bTruth_rationalInterval_weighted vd A X' E u a b ha hb hx,
    bTruth_rationalInterval_weighted vd C Y' D w c d hc hd hy,
    bTruth_belowProduct_named vd Q' A C q a c hq ha hc,
    bTruth_belowProduct_named vd Q' A D q a d hq ha hd,
    bTruth_belowProduct_named vd Q' E C q b c hq hb hc,
    bTruth_belowProduct_named vd Q' E D q b d hq hb hd,
    crispConj,← inf_assoc]
  rw [iSup_inf_crisp_ratLower] <;> rfl

theorem bTruth_realMul_weighted {n : ℕ} (v : DVec (V B) n)
    (X Y Z : STerm n) (u w s : RatPresentation → B)
    (hX : bTerm v X = weightedRationalSet u) (hY : bTerm v Y = weightedRationalSet w)
    (hZ : bTerm v Z = weightedRationalSet s) :
    bTruth v (realMul_f X Y Z) = (weightedRationalSet s =ᴮ mulCutName u w) := by
  rw [realMul_f,bTruth_rationalAll,mulCutName,weightedRationalSet_eq_bitEq]
  apply iInf_congr
  intro q
  let vq := DVec.cons (ratName (B := B) q) v
  let Q : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  have hXq := (bTerm_up_r181 v (ratName q) X).trans hX
  have hYq := (bTerm_up_r181 v (ratName q) Y).trans hY
  have hZq := (bTerm_up_r181 v (ratName q) Z).trans hZ
  change bTruth vq (bd_biimp (mem' Q (up Z)) (realMulApprox_f (up X) (up Y) Q)) = _
  simp only [boolean_realize_bounded_formula_biimp,equiv_bitEq_r181,
    boolean_realize_bounded_formula_mem',hZq,bTerm_current_r181,
    ratName_mem_weightedRationalSet,
    bTruth_realMulApprox_weighted vq (up X) (up Y) Q u w q hXq hYq
      (bTerm_current_r181 v (ratName q))]
  change bitEq (bTerm vq Q ∈ᴮ bTerm vq (up Z)) (mulCutBits u w q) = _
  rw [show bTerm vq Q = ratName q from bTerm_current_r181 v (ratName q), hZq,
    ratName_mem_weightedRationalSet]

end JSP000930.AnalyticSyntax
