import JSP000930AnalyticRationalQuantifiers

open Fol Lattice
open scoped Flypitch bSet

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_rationalEx {n : ℕ} (v : DVec (V B) n)
    (D : STerm (n+1) → SForm (n+1)) :
    bTruth v (rationalEx_f D) = ⨆ q : RatPresentation,
      bTruth (DVec.cons (ratName q) v) (D (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  simp only [rationalEx_f,bTruth_sEx_r181,boolean_realize_bounded_formula_and,
    bTruth_rationalCode,bTerm_current_r181]
  let f (z : bSet B) : B :=
    bTruth (DVec.cons z v) (D (bd_var ⟨0,Nat.succ_pos n⟩))
  change (⨆ z : bSet B, (z ∈ᴮ ratUniverse) ⊓ f z) = _
  simpa only [ratUniverse,top_inf_eq] using
    (weightedRational_exists (fun _ => (⊤ : B)) f (bTruth_body_ext_r191 v _))

theorem bTruth_rationalAll {n : ℕ} (v : DVec (V B) n)
    (D : STerm (n+1) → SForm (n+1)) :
    bTruth v (rationalAll_f D) = ⨅ q : RatPresentation,
      bTruth (DVec.cons (ratName q) v) (D (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  simp only [rationalAll_f,bTruth_sAll_r181,bTruth_imp_r181,
    bTruth_rationalCode,bTerm_current_r181]
  let f (z : bSet B) : B :=
    bTruth (DVec.cons z v) (D (bd_var ⟨0,Nat.succ_pos n⟩))
  change (⨅ z : bSet B, imp (z ∈ᴮ ratUniverse) (f z)) = _
  have ht (a : B) : imp ⊤ a = a := by
    apply le_antisymm
    · have h : imp (⊤ : B) a ≤ imp ⊤ a := le_rfl
      rw [← _root_.deduction,inf_top_eq] at h
      exact h
    · rw [← _root_.deduction,inf_top_eq] <;> exact le_rfl
  simpa only [ratUniverse,ht] using
    (weightedRational_forall (fun _ => (⊤ : B)) f (bTruth_body_ext_r191 v _))

theorem bTruth_cut_nonempty_weighted {n : ℕ} (v : DVec (V B) n) (X : STerm n)
    (β : RatPresentation → B) (hX : bTerm v X = weightedRationalSet β) :
    bTruth v (exIn X fun q => rationalCode_f q) = ⨆ q : RatPresentation, β q := by
  rw [bTruth_exInWeightedRational v X β hX]
  simp only [bTruth_rationalCode,bTerm_current_r181,ratUniverse,
    ratName_mem_weightedRationalSet,inf_top_eq]

theorem bTruth_cut_typed_weighted {n : ℕ} (v : DVec (V B) n) (X : STerm n)
    (β : RatPresentation → B) (hX : bTerm v X = weightedRationalSet β) :
    bTruth v (allIn X fun q => rationalCode_f q) = ⊤ := by
  rw [bTruth_allInWeightedRational v X β hX]
  simp only [bTruth_rationalCode,bTerm_current_r181,ratUniverse,
    ratName_mem_weightedRationalSet]
  apply top_unique
  refine le_iInf fun q => ?_
  rw [← _root_.deduction]
  exact le_top

theorem bTruth_cut_proper_weighted {n : ℕ} (v : DVec (V B) n) (X : STerm n)
    (β : RatPresentation → B) (hX : bTerm v X = weightedRationalSet β) :
    bTruth v (rationalEx_f fun q => bd_not (mem' q (up X))) =
      ⨆ q : RatPresentation, (β q)ᶜ := by
  rw [bTruth_rationalEx]
  simp only [boolean_realize_bounded_formula_not,boolean_realize_bounded_formula_mem',
    bTerm_current_r181,bTerm_up_r181,hX,ratName_mem_weightedRationalSet]

theorem bTruth_cut_lower_weighted {n : ℕ} (v : DVec (V B) n) (X : STerm n)
    (β : RatPresentation → B) (hX : bTerm v X = weightedRationalSet β) :
    bTruth v (validLowerParts_f X) =
      ⨅ r : RatPresentation, imp (β r)
        (⨅ q : RatPresentation, imp (crispTruth B (q.value ≤ r.value)) (β q)) := by
  simp only [validLowerParts_f, bTruth_allInWeightedRational v X β hX, bTruth_rationalAll,
    bTruth_imp_r181, boolean_realize_bounded_formula_mem',
    bTerm_current_r181,bTerm_up2_r181,hX,ratName_mem_weightedRationalSet]
  apply iInf_congr
  intro r
  apply congrArg (imp (β r))
  apply iInf_congr
  intro q
  let w : DVec (V B) (n+2) := DVec.cons (ratName q) (DVec.cons (ratName r) v)
  let t : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let u : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  rw [bTruth_rationalLE_named w u (up t) q r]
  · exact bTerm_current_r181 (DVec.cons (ratName r) v) (ratName q)
  · simp only [w,t,bTerm_up_r181,bTerm_current_r181]

theorem bTruth_cut_round_weighted {n : ℕ} (v : DVec (V B) n) (X : STerm n)
    (β : RatPresentation → B) (hX : bTerm v X = weightedRationalSet β) :
    bTruth v (roundedParts_f X) =
      ⨅ q : RatPresentation, imp (β q)
        (⨆ r : RatPresentation, β r ⊓ crispTruth B (q.value < r.value)) := by
  rw [roundedParts_f,bTruth_allInWeightedRational v X β hX]
  apply iInf_congr
  intro q
  apply congrArg (imp (β q))
  let w : DVec (V B) (n+1) := DVec.cons (ratName q) v
  let t : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let u : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  have hY : bTerm w (up X) = weightedRationalSet β :=
    (bTerm_up_r181 v (ratName q) X).trans hX
  rw [bTruth_exInWeightedRational w (up X) β hY]
  apply iSup_congr
  intro r
  rw [bTruth_rationalLT_named (DVec.cons (ratName r) w) (up t) u q r]
  · simp only [w,t,bTerm_up_r181,bTerm_current_r181]
  · exact bTerm_current_r181 w (ratName r)

theorem bTruth_realCut_weighted {n : ℕ} (v : DVec (V B) n) (X : STerm n)
    (β : RatPresentation → B) (hX : bTerm v X = weightedRationalSet β) :
    bTruth v (realCut_f X) =
      (⨆ q : RatPresentation, β q) ⊓ ((⨆ q : RatPresentation, (β q)ᶜ) ⊓
        ((⨅ r : RatPresentation, imp (β r)
          (⨅ q : RatPresentation, imp (crispTruth B (q.value ≤ r.value)) (β q))) ⊓
         (⨅ q : RatPresentation, imp (β q)
          (⨆ r : RatPresentation, β r ⊓ crispTruth B (q.value < r.value))))) := by
  simp only [realCut_f,boolean_realize_bounded_formula_and,
    bTruth_cut_nonempty_weighted v X β hX,bTruth_cut_typed_weighted v X β hX,
    bTruth_cut_proper_weighted v X β hX,bTruth_cut_lower_weighted v X β hX,
    bTruth_cut_round_weighted v X β hX,top_inf_eq]

end JSP000930.AnalyticSyntax
