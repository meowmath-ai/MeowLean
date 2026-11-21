import JSP000930AnalyticRationalOrder

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem weightedRational_exists (β : RatPresentation → B) (F : bSet B → B)
    (hF : bSet.B_ext F) :
    (⨆ z : bSet B, (z ∈ᴮ weightedRationalSet β) ⊓ F z) =
      ⨆ q : RatPresentation, β q ⊓ F (ratName q) := by
  apply le_antisymm
  · refine iSup_le fun z => ?_
    rw [mem_weightedRationalSet, iSup_inf_eq]
    refine iSup_le fun q => ?_
    calc
      (β q ⊓ (z =ᴮ ratName q)) ⊓ F z =
          β q ⊓ ((z =ᴮ ratName q) ⊓ F z) := inf_assoc _ _ _
      _ ≤ β q ⊓ F (ratName q) := inf_le_inf_left _ (hF z (ratName q))
      _ ≤ _ := le_iSup (fun q => β q ⊓ F (ratName q)) q
  · refine iSup_le fun q => le_iSup_of_le (ratName q) ?_
    rw [ratName_mem_weightedRationalSet]

theorem weightedRational_forall (β : RatPresentation → B) (F : bSet B → B)
    (hF : bSet.B_ext F) :
    (⨅ z : bSet B, imp (z ∈ᴮ weightedRationalSet β) (F z)) =
      ⨅ q : RatPresentation, imp (β q) (F (ratName q)) := by
  apply le_antisymm
  · refine le_iInf fun q => ?_
    have h := iInf_le (fun z : bSet B => imp (z ∈ᴮ weightedRationalSet β) (F z)) (ratName q)
    simpa only [ratName_mem_weightedRationalSet] using h
  · let p : B := ⨅ q : RatPresentation, imp (β q) (F (ratName q))
    change p ≤ _
    refine le_iInf fun z => ?_
    rw [← _root_.deduction,mem_weightedRationalSet,inf_iSup_eq]
    refine iSup_le fun q => ?_
    have hq : p ⊓ β q ≤ F (ratName q) := by
      rw [_root_.deduction]
      exact iInf_le _ q
    calc
      p ⊓ (β q ⊓ (z =ᴮ ratName q)) = (z =ᴮ ratName q) ⊓ (p ⊓ β q) := by ac_rfl
      _ ≤ (z =ᴮ ratName q) ⊓ F (ratName q) := inf_le_inf_left _ hq
      _ = (ratName q =ᴮ z) ⊓ F (ratName q) := by rw [bSet.bv_eq_symm]
      _ ≤ F z := hF (ratName q) z

theorem bTruth_exInWeightedRational {n : ℕ} (v : DVec (V B) n) (X : STerm n)
    (β : RatPresentation → B) (hX : bTerm v X = weightedRationalSet β)
    (body : STerm (n+1) → SForm (n+1)) :
    bTruth v (exIn X body) =
      ⨆ q : RatPresentation, β q ⊓
        bTruth (DVec.cons (ratName q) v) (body (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  rw [bTruth_exIn_r181,hX]
  exact weightedRational_exists β _ (bTruth_body_ext_r191 v _)

theorem bTruth_allInWeightedRational {n : ℕ} (v : DVec (V B) n) (X : STerm n)
    (β : RatPresentation → B) (hX : bTerm v X = weightedRationalSet β)
    (body : STerm (n+1) → SForm (n+1)) :
    bTruth v (allIn X body) =
      ⨅ q : RatPresentation, imp (β q)
        (bTruth (DVec.cons (ratName q) v) (body (bd_var ⟨0,Nat.succ_pos n⟩))) := by
  rw [bTruth_allIn_r181,hX]
  exact weightedRational_forall β _ (bTruth_body_ext_r191 v _)

end JSP000930.AnalyticSyntax
