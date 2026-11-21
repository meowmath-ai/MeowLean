import JSP000930NegativeExactSiteEvalImage

open Fol bSet Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.SetLanguage JSP000933.PreparedModel JSP000933.OpenGraphForcing
  JSP000933.BooleanCompletion JSP000930.Positive JSP000930.SetLanguage
  JSP000930.BooleanAnalysis JSP000930.AnalyticSyntax

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem NamedPaletteSchedule.forces_pointwiseBound {n : ℕ}
    (S : NamedPaletteSchedule B) (F₀ : CompleteValueMap PreparedBA B)
    (v : DVec (V B) n) (F M : STerm n)
    (hF : bTerm v F = S.family) (hM : bTerm v M = check BaseOmegaOne) :
    (⊤ : B) ≤ bTruth v (pointwiseBound_f actualAnalyticSyntax F M) := by
  unfold pointwiseBound_f
  rw [bTruth_sAll_r181]
  apply le_iInf
  intro z
  rw [bTruth_imp_r181,← _root_.deduction,top_inf_eq,bTruth_sEx_r181]
  let Z : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let vZ := DVec.cons z v
  let p := bTruth vZ (complex_f Z)
  change p ≤ _
  obtain ⟨zbits,hzBits,hzEq⟩ := complexBits_of_forcedName vZ Z p le_rfl
  rw [show bTerm vZ Z = z from bTerm_current_r181 v z] at hzEq
  have hSite : p ≤ ⨆ j,z =ᴮ (S.site j).name := by
    apply (le_inf hzEq (S.sitesCover zbits p hzBits)).trans
    rw [inf_iSup_eq]
    exact iSup_le fun j => le_iSup_of_le j (bv_trans inf_le_left inf_le_right)
  apply (le_inf le_rfl hSite).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro j
  let z' := (S.site j).name
  let W := S.siteImage j
  let d := p ⊓ (z =ᴮ z')
  apply le_iSup_of_le W
  let w : DVec (V B) (n+2) := DVec.cons W (DVec.cons z v)
  let w' : DVec (V B) (n+2) := DVec.cons W (DVec.cons z' v)
  let R : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let φ : SForm (n+2) := evalImage_f actualAnalyticSyntax (up2 F) (up Z) R
  change d ≤ bTruth w (bd_and φ (injects_f R (up2 M)))
  rw [bTruth_and_eq,bTruth_injects_f_r6]
  have hR : bTerm w R = W := bTerm_current_r181 (DVec.cons z v) W
  have hM' : bTerm w (up2 M) = check BaseOmegaOne :=
    (bTerm_up2_r181 v z W M).trans hM
  rw [hR,hM']
  refine le_inf ?_ (le_top.trans (S.siteImage_injects_omegaOne F₀ j))
  have hImg : (⊤ : B) ≤ bTruth w' φ :=
    S.siteImage_forces_evalImage j w' (up2 F) (up Z) R
      ((bTerm_up2_r181 v z' W F).trans hF)
      ((bTerm_up_r181 (DVec.cons z' v) W Z).trans (bTerm_current_r181 v z'))
      (bTerm_current_r181 (DVec.cons z' v) W)
  have hEq : ∀ i : Fin (n+2),d ≤ w'.nth i.val i.isLt =ᴮ w.nth i.val i.isLt := by
    intro i
    refine Fin.cases (show d ≤ W =ᴮ W from bv_refl) (fun j => ?_) i
    exact Fin.cases (show d ≤ z' =ᴮ z from bv_symm inf_le_right) (fun _ => bv_refl) j
  have hMask := bTruth_vecMask_r191 d w' w φ hEq
  exact (le_inf le_rfl (le_top.trans hImg)).trans (hMask.le.trans inf_le_right)

end JSP000930.Negative
