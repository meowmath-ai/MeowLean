import JSP000930NegativeLiteralEntireAndCanonicalEvaluation

open Fol bSet Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.SetLanguage JSP000933.BooleanNames JSP000933.PreparedModel
  JSP000930.Positive JSP000930.BooleanAnalysis JSP000930.AnalyticSyntax JSP000930.SetLanguage

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem NamedPaletteSchedule.siteImage_forces_evalImage {n : ℕ}
    (S : NamedPaletteSchedule B) (j : GroundContinuumSuccIndex)
    (v : DVec (V B) n) (F Z W : STerm n)
    (hF : bTerm v F = S.family) (hZ : bTerm v Z = (S.site j).name)
    (hW : bTerm v W = S.siteImage j) :
    (⊤ : B) ≤ bTruth v (evalImage_f actualAnalyticSyntax F Z W) := by
  unfold evalImage_f
  rw [bTruth_sAll_r181]
  apply le_iInf
  intro y
  let vY : DVec (V B) (n+1) := DVec.cons y v
  let Y : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let A : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let φ : SForm (n+2) := evalAt_f A (up2 Z) (up Y)
  let P : B := bTruth vY (complex_f Y) ⊓
    (⨆ a : bSet B,(a ∈ᴮ S.family) ⊓ bTruth (DVec.cons a vY) φ)
  have hMem : bTruth vY (mem' Y (up W)) = (y ∈ᴮ S.siteImage j) := by
    change boolean_realize_bounded_formula vY (mem' Y (up W)) DVec.nil = _
    rw [boolean_realize_bounded_formula_mem']
    change (bTerm vY Y ∈ᴮ bTerm vY (up W)) = _
    rw [bTerm_current_r181 v y, (bTerm_up_r181 v y W).trans hW]
  have hF' : bTerm vY (up F) = S.family := (bTerm_up_r181 v y F).trans hF
  change (⊤ : B) ≤ bTruth vY (bd_biimp (mem' Y (up W)) _)
  simp only [bd_biimp,bTruth_and_eq,bTruth_imp_r181,bTruth_exIn_r181,hMem,hF']
  change (⊤ : B) ≤ imp (y ∈ᴮ S.siteImage j) P ⊓ imp P (y ∈ᴮ S.siteImage j)
  have hE (i : GroundContinuumSuccIndex) (p : B) :
      p ≤ bTruth (DVec.cons (taylorCodeName (S.code i)) vY) φ ↔
        p ≤ y =ᴮ S.evalAtSite i j := by
    let a := taylorCodeName (S.code i)
    let u : DVec (V B) (n+2) := DVec.cons a vY
    have hZ' : bTerm u (up2 Z) = (S.site j).name := (bTerm_up2_r181 v y a Z).trans hZ
    have hY : bTerm u (up Y) = y :=
      (bTerm_up_r181 vY a Y).trans (bTerm_current_r181 v y)
    simpa only [φ,u,a,hY,NamedPaletteSchedule.evalAtSite] using
      (canonical_evalAt_iff_native u A (up2 Z) (up Y) (S.code i) (S.site j) p
        (bTerm_current_r181 vY a) hZ'
        (fun k => ⟨JSP000930.Positive.properCutOn_mono le_top (S.codeCut i k).1,
          JSP000930.Positive.properCutOn_mono le_top (S.codeCut i k).2⟩)
        ((S.codeGrowth i).mono le_top)
        ⟨JSP000930.Positive.properCutOn_mono le_top (S.siteCutOn j).1,
          JSP000930.Positive.properCutOn_mono le_top (S.siteCutOn j).2⟩)
  apply le_inf
  · rw [← _root_.deduction,top_inf_eq]
    simp only [NamedPaletteSchedule.siteImage,mem_familyName_r70,top_inf_eq]
    apply iSup_le
    intro i
    let p := (y =ᴮ S.evalAtSite i j)
    let T := taylorLimitBits (complexCoeffBits (S.code i)) (S.site j)
    have hCut : T.CutOn p := by
      have h := taylorLimitBits_cutOn (complexCoeffBits (S.code i)) (S.site j) ⊤
        (S.codeCut i) (S.siteCutOn j) (S.codeGrowth i)
      exact ⟨JSP000930.Positive.properCutOn_mono le_top h.1,
        JSP000930.Positive.properCutOn_mono le_top h.2⟩
    refine le_inf (force_complex_at_eq_of_native_name v y T p hCut le_rfl) ?_
    apply le_iSup_of_le (taylorCodeName (S.code i))
    exact le_inf (le_top.trans (bSet.mem_mk (fun j => taylorCodeName (S.code j)) (fun _ => (⊤ : B)) i)) ((hE i p).2 le_rfl)
  · rw [← _root_.deduction,top_inf_eq]
    apply inf_le_right.trans
    apply iSup_le
    intro a
    simp only [NamedPaletteSchedule.family,mem_familyName_r70,top_inf_eq,iSup_inf_eq]
    apply iSup_le
    intro i
    let x := taylorCodeName (S.code i)
    let p := (a =ᴮ x) ⊓ bTruth (DVec.cons a vY) φ
    have hx : p ≤ bTruth (DVec.cons x vY) φ := bTruth_body_ext_r191 vY φ a x
    have he := (hE i p).1 hx
    exact subst_congr_mem_left' (bv_symm he) (le_top.trans (bSet.mem_mk (fun k => S.evalAtSite k j) (fun _ => (⊤ : B)) i))

end JSP000930.Negative
