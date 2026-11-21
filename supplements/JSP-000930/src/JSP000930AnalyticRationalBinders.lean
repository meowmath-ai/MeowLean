import JSP000930AnalyticRationalTruth
import JSP000933CheckedAddMulFactorial

open Fol Lattice
open scoped Flypitch bSet

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def natAddBind_f {n : ℕ} (a b : STerm n) (body : STerm (n+1) → SForm (n+1)) :
    SForm n :=
  exIn omega fun t => bd_and (addition_f (up a) (up b) t) (body t)

def natMulBind_f {n : ℕ} (a b : STerm n) (body : STerm (n+1) → SForm (n+1)) :
    SForm n :=
  exIn omega fun t => bd_and (multiplication_f (up a) (up b) t) (body t)

theorem bTruth_natAddBind {n : ℕ} (v : DVec (V B) n) (a b : STerm n)
    (body : STerm (n+1) → SForm (n+1)) (x y : ℕ)
    (ha : bTerm v a = bSet.of_nat x) (hb : bTerm v b = bSet.of_nat y) :
    bTruth v (natAddBind_f a b body) =
      bTruth (DVec.cons (bSet.of_nat (x+y)) v) (body (bd_var ⟨0, Nat.succ_pos n⟩)) := by
  let t : STerm (n+1) := bd_var ⟨0, Nat.succ_pos n⟩
  let w (i : ℕ) : DVec (V B) (n+1) := DVec.cons (bSet.of_nat i) v
  have h (i : ℕ) :
      bTruth (w i) (addition_f (up a) (up b) t) = crispTruth B (i = x+y) :=
    bTruth_addition_checked_r196 (w i) (up a) (up b) t x y i
      ((bTerm_up_r181 v (bSet.of_nat i) a).trans ha)
      ((bTerm_up_r181 v (bSet.of_nat i) b).trans hb)
      (bTerm_current_r181 v (bSet.of_nat i))
  simp only [natAddBind_f, bTruth_exOmega_r192, boolean_realize_bounded_formula_and]
  change (⨆ i : ℕ, bTruth (w i) (addition_f (up a) (up b) t) ⊓
    bTruth (w i) (body t)) = bTruth (w (x+y)) (body t)
  simp only [h, iSup_crispEquality_select_r193]

theorem bTruth_natMulBind {n : ℕ} (v : DVec (V B) n) (a b : STerm n)
    (body : STerm (n+1) → SForm (n+1)) (x y : ℕ)
    (ha : bTerm v a = bSet.of_nat x) (hb : bTerm v b = bSet.of_nat y) :
    bTruth v (natMulBind_f a b body) =
      bTruth (DVec.cons (bSet.of_nat (x*y)) v) (body (bd_var ⟨0, Nat.succ_pos n⟩)) := by
  let t : STerm (n+1) := bd_var ⟨0, Nat.succ_pos n⟩
  let w (i : ℕ) : DVec (V B) (n+1) := DVec.cons (bSet.of_nat i) v
  have h (i : ℕ) :
      bTruth (w i) (multiplication_f (up a) (up b) t) = crispTruth B (i = x*y) :=
    bTruth_multiplication_checked_r196 (w i) (up a) (up b) t x y i
      ((bTerm_up_r181 v (bSet.of_nat i) a).trans ha)
      ((bTerm_up_r181 v (bSet.of_nat i) b).trans hb)
      (bTerm_current_r181 v (bSet.of_nat i))
  simp only [natMulBind_f, bTruth_exOmega_r192, boolean_realize_bounded_formula_and]
  change (⨆ i : ℕ, bTruth (w i) (multiplication_f (up a) (up b) t) ⊓
    bTruth (w i) (body t)) = bTruth (w (x*y)) (body t)
  simp only [h, iSup_crispEquality_select_r193]

theorem bTruth_unpackRational_named {n k : ℕ} (v : DVec (V B) n) (q : STerm n)
    (par : Fin k → STerm n)
    (body : ∀ {l : ℕ}, (Fin k → STerm l) → STerm l → STerm l → STerm l → SForm l)
    (r : RatPresentation) (hq : bTerm v q = ratName r) :
    let x : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    let y : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
    let z : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
    let w : DVec (V B) (n+3) := DVec.cons (bSet.of_nat r.den)
      (DVec.cons (bSet.of_nat r.neg) (DVec.cons (bSet.of_nat r.pos) v))
    bTruth v (unpackRational_f q par body) =
      bTruth w (body (fun i => up3 (par i)) (up2 x) (up y) z) := by
  let x : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let y : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let z : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  let w (a b d : ℕ) : DVec (V B) (n+3) := DVec.cons (bSet.of_nat d)
      (DVec.cons (bSet.of_nat b) (DVec.cons (bSet.of_nat a) v))
  let val (a b d : ℕ) : B :=
    bTruth (w a b d) (body (fun i => up3 (par i)) (up2 x) (up y) z)
  let guard (a b d : ℕ) : B :=
    bTruth (w a b d) (bd_not (bd_equal z zero)) ⊓
      bTruth (w a b d) (bd_equal (up3 q) (pair' (up2 x) (pair' (up y) z)))
  have hguard (a b d : ℕ) : guard a b d =
      crispTruth B (r.pos = a ∧ r.neg = b ∧ r.den = d) := by
    simp only [guard, boolean_realize_bounded_formula_not, bTruth_equal_r181,
      boolean_realize_bounded_term_pair', w, x, y, z,
      bTerm_up3_r181, bTerm_up2_r181, bTerm_up_r181, bTerm_current_r181,
      bTerm_zero_checked_r192, hq, ratName, pair_eq_inf_r189, checkedNat_eq_crisp_r189]
    by_cases ha : r.pos = a
    · by_cases hb : r.neg = b
      · by_cases hd : r.den = d
        · have hn : d ≠ 0 := hd ▸ (Nat.ne_of_gt r.den_pos)
          simp only [crispTruth, ha, hb, hd, hn, ite_true, ite_false, compl_bot, top_inf_eq, and_self]
        · simp only [crispTruth, hd, ite_false, and_false, inf_bot_eq]
      · simp only [crispTruth, hb, ite_false, false_and, and_false, bot_inf_eq, inf_bot_eq]
    · simp only [crispTruth, ha, ite_false, false_and, bot_inf_eq, inf_bot_eq]
  change bTruth v (unpackRational_f q par body) = val r.pos r.neg r.den
  simp only [unpackRational_f, bTruth_exOmega_r192, boolean_realize_bounded_formula_and]
  simp only [← inf_assoc]
  change (⨆ a : ℕ, ⨆ b : ℕ, ⨆ d : ℕ, guard a b d ⊓ val a b d) = _
  rw [show (⨆ a : ℕ, ⨆ b : ℕ, ⨆ d : ℕ, guard a b d ⊓ val a b d) =
    (⨆ a : ℕ, ⨆ b : ℕ, ⨆ d : ℕ,
      crispTruth B (r.pos = a ∧ r.neg = b ∧ r.den = d) ⊓ val a b d) by
        simp only [hguard]]
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun d => ?_
    by_cases h : r.pos = a ∧ r.neg = b ∧ r.den = d
    · rcases h with ⟨rfl,rfl,rfl⟩
      exact inf_le_right
    · simp [crispTruth, h]
  · have hh := (le_iSup (fun d : ℕ =>
      crispTruth B (r.pos = r.pos ∧ r.neg = r.neg ∧ r.den = d) ⊓ val r.pos r.neg d) r.den).trans
      ((le_iSup (fun b : ℕ => ⨆ d : ℕ,
        crispTruth B (r.pos = r.pos ∧ r.neg = b ∧ r.den = d) ⊓ val r.pos b d) r.neg).trans
        (le_iSup (fun a : ℕ => ⨆ b : ℕ, ⨆ d : ℕ,
          crispTruth B (r.pos = a ∧ r.neg = b ∧ r.den = d) ⊓ val a b d) r.pos))
    simpa [crispTruth] using hh

end JSP000930.AnalyticSyntax
