import JSP000930PositiveEntireTaylorNameCover
import JSP000930ActualHaymanSentence
import JSP000930BooleanCardinalSyntax

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.SetLanguage JSP000930.SetLanguage JSP000930.AnalyticSyntax

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem with_familyEntire_member {n : ℕ} (v : DVec (V B) n) (F : STerm n)
    (a : bSet B) (p : B) (hF : p ≤ bTruth v (familyEntire_f actualAnalyticSyntax F)) :
    p ⊓ (a ∈ᴮ bTerm v F) ≤ bTruth (DVec.cons a v)
      (isEntireCode_f (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  unfold familyEntire_f at hF
  rw [bTruth_allIn_r181] at hF
  have hI := hF.trans (iInf_le _ a)
  rw [← _root_.deduction] at hI
  exact hI

theorem actual_pointwise_choose_value_set {n : ℕ}
    (v : DVec (V B) n) (F m : STerm n) (z : bSet B) (p : B)
    (hPW : p ≤ bTruth v (pointwiseBound_f actualAnalyticSyntax F m))
    (hz : p ≤ bTruth (DVec.cons z v)
      (complex_f (bd_var ⟨0,Nat.succ_pos n⟩))) :
    ∃ W : bSet B, p ≤ bTruth (DVec.cons W (DVec.cons z v))
      (evalImage_f actualAnalyticSyntax (up2 F)
        (up (bd_var ⟨0,Nat.succ_pos n⟩)) (bd_var ⟨0,Nat.succ_pos (n+1)⟩)) ∧
      p ≤ injects_into W (bTerm v m) := by
  let u : DVec (V B) (n+1) := DVec.cons z v
  let Z : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let Wvar : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let body : SForm (n+2) :=
    bd_and (evalImage_f actualAnalyticSyntax (up2 F) (up Z) Wvar)
      (injects_f Wvar (up2 m))
  have h : p ≤ ⨆ W : bSet B,bTruth (DVec.cons W u) body := by
    unfold pointwiseBound_f at hPW
    rw [bTruth_sAll_r181] at hPW
    have hZ := hPW.trans (iInf_le _ z)
    rw [bTruth_imp_r181,bTruth_sEx_r181] at hZ
    have hp := (le_inf hZ hz).trans Lattice.bv_imp_elim
    exact hp
  obtain ⟨W,hW⟩ := bSet.maximum_principle
    (fun W : bSet B => bTruth (DVec.cons W u) body) (bTruth_body_ext_r191 u body)
  have hp := h.trans_eq hW
  have hAnd : bTruth (DVec.cons W u) body =
      bTruth (DVec.cons W u) (evalImage_f actualAnalyticSyntax (up2 F) (up Z) Wvar) ⊓
      bTruth (DVec.cons W u) (injects_f Wvar (up2 m)) :=
    boolean_realize_bounded_formula_and
  rw [hAnd] at hp
  refine ⟨W,hp.trans inf_le_left,?_⟩
  have hi := hp.trans inf_le_right
  rw [bTruth_injects_f_r6] at hi
  have hm : bTerm (DVec.cons W u) (up2 m) = bTerm v m := bTerm_up2_r181 v z W m
  change p ≤ injects_into W (bTerm (DVec.cons W u) (up2 m)) at hi
  rwa [hm] at hi

end JSP000930.Positive
