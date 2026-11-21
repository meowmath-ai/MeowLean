import JSP000930AnalyticOrderedCut
import JSP000930AnalyticWeightedRational

open Fol Lattice
open scoped Flypitch bSet

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private def denominatorsBody {n : ℕ} (q p m d : STerm n) : SForm n :=
  bd_and (bd_not (bd_equal d zero)) (bd_equal q (pair' p (pair' m d)))

theorem bTruth_rationalCode {n : ℕ} (v : DVec (V B) n) (q : STerm n) :
    bTruth v (rationalCode_f q) = (bTerm v q ∈ᴮ (ratUniverse : bSet B)) := by
  let u (a b d : ℕ) : DVec (V B) (n+3) :=
    DVec.cons (bSet.of_nat d) (DVec.cons (bSet.of_nat b) (DVec.cons (bSet.of_nat a) v))
  let x : STerm (n+1) := bd_var ⟨0, Nat.succ_pos n⟩
  let y : STerm (n+2) := bd_var ⟨0, Nat.succ_pos (n+1)⟩
  let z : STerm (n+3) := bd_var ⟨0, Nat.succ_pos (n+2)⟩
  let N (a b d : ℕ) : bSet B :=
    bSet.pair (bSet.of_nat a) (bSet.pair (bSet.of_nat b) (bSet.of_nat d))
  have hBody (a b d : ℕ) :
      bTruth (u a b d) (denominatorsBody (up3 q) (up2 x) (up y) z) =
        (crispTruth B (d = 0))ᶜ ⊓ (bTerm v q =ᴮ N a b d) := by
    simp only [denominatorsBody, boolean_realize_bounded_formula_and,
      boolean_realize_bounded_formula_not, bTruth_equal_r181,
      boolean_realize_bounded_term_pair', u, N, x, y, z,
      bTerm_up3_r181, bTerm_up2_r181, bTerm_up_r181, bTerm_current_r181,
      bTerm_zero_checked_r192, checkedNat_eq_crisp_r189]
  simp only [rationalCode_f, bTruth_exOmega_r192]
  change (⨆ a : ℕ, ⨆ b : ℕ, ⨆ d : ℕ,
    bTruth (u a b d) (denominatorsBody (up3 q) (up2 x) (up y) z)) =
      (bTerm v q ∈ᴮ (ratUniverse : bSet B))
  simp only [hBody, ratUniverse_membership]
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun d => ?_
    by_cases hd : d = 0
    · simp [crispTruth, hd]
    · have hd' : 0 < d := Nat.pos_of_ne_zero hd
      have h := le_iSup
        (fun r : RatPresentation => (bTerm v q =ᴮ ratName r)) ⟨a, b, d, hd'⟩
      simpa [crispTruth, hd, N, ratName] using h
  · apply iSup_le
    intro r
    have hd : r.den ≠ 0 := Nat.ne_of_gt r.den_pos
    have h := (le_iSup
      (fun d : ℕ => (crispTruth B (d = 0))ᶜ ⊓ (bTerm v q =ᴮ N r.pos r.neg d)) r.den).trans
      ((le_iSup (fun b : ℕ => ⨆ d : ℕ,
        (crispTruth B (d = 0))ᶜ ⊓ (bTerm v q =ᴮ N r.pos b d)) r.neg).trans
        (le_iSup (fun a : ℕ => ⨆ b : ℕ, ⨆ d : ℕ,
          (crispTruth B (d = 0))ᶜ ⊓ (bTerm v q =ᴮ N a b d)) r.pos))
    simpa [crispTruth, hd, N, ratName] using h

theorem bTruth_realLE {n : ℕ} (v : DVec (V B) n) (X Y : STerm n) :
    bTruth v (realLE_f X Y) = (bTerm v X ⊆ᴮ bTerm v Y) := by
  change bTruth v (allIn X fun q => mem' q (up Y)) = _
  rw [bTruth_allIn_r181, bSet.subset_unfold']
  simp only [boolean_realize_bounded_formula_mem', bTerm_current_r181, bTerm_up_r181]

theorem bTruth_realLT {n : ℕ} (v : DVec (V B) n) (X Y : STerm n) :
    bTruth v (realLT_f X Y) =
      (bTerm v X ⊆ᴮ bTerm v Y) ⊓ (bTerm v X =ᴮ bTerm v Y)ᶜ := by
  simp only [realLT_f, boolean_realize_bounded_formula_and,
    boolean_realize_bounded_formula_not, bTruth_realLE, bTruth_equal_r181]

theorem bTruth_realCut_types {n : ℕ} (v : DVec (V B) n) (X : STerm n) :
    bTruth v (realCut_f X) ≤ (bTerm v X ⊆ᴮ (ratUniverse : bSet B)) := by
  have h : bTruth v (allIn X fun q => rationalCode_f q) =
      (bTerm v X ⊆ᴮ (ratUniverse : bSet B)) := by
    rw [bTruth_allIn_r181, bSet.subset_unfold']
    simp only [bTruth_rationalCode, bTerm_current_r181]
  rw [← h]
  simp only [realCut_f, boolean_realize_bounded_formula_and]
  exact inf_le_right.trans inf_le_left

theorem bTruth_realCut_recover {n : ℕ} (v : DVec (V B) n) (X : STerm n) (p : B)
    (hp : p ≤ bTruth v (realCut_f X)) :
    p ≤ bTerm v X =ᴮ weightedRationalSet (extractRationalWeights (bTerm v X)) :=
  weightedRationalSet_recover (bTerm v X) p (hp.trans (bTruth_realCut_types v X))

end JSP000930.AnalyticSyntax
