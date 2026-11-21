import JSP000930PositiveLiteralHaymanFamilyAndValueSet

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.SetLanguage JSP000930.SetLanguage JSP000930.AnalyticSyntax

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def valueCertificate {n : ℕ} (v : DVec (V B) n) (z W a y : bSet B) : B :=
  let Vz := DVec.cons z v
  let Vw := DVec.cons W Vz
  let Vy := DVec.cons y Vw
  let Va := DVec.cons a Vy
  let Z : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let Y : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  let A : STerm (n+4) := bd_var ⟨0,Nat.succ_pos (n+3)⟩
  bTruth Vy (complex_f Y) ⊓ bTruth Va (evalAt_f A (up2 (up Z)) (up Y))

theorem actual_evalImage_contains {n : ℕ}
    (v : DVec (V B) n) (F : STerm n) (z W a y : bSet B) (p : B)
    (hImage : p ≤ bTruth (DVec.cons W (DVec.cons z v))
      (evalImage_f actualAnalyticSyntax (up2 F)
        (up (bd_var ⟨0,Nat.succ_pos n⟩)) (bd_var ⟨0,Nat.succ_pos (n+1)⟩)))
    (ha : p ≤ a ∈ᴮ bTerm v F) (hy : p ≤ valueCertificate v z W a y) :
    p ≤ y ∈ᴮ W := by
  unfold evalImage_f at hImage
  rw [bTruth_sAll_r181] at hImage
  have hAt := hImage.trans (iInf_le _ y)
  simp only [bd_biimp,boolean_realize_bounded_formula_and,bTruth_imp_r181] at hAt
  have hImp := hAt.trans inf_le_right
  simp only [actualAnalyticSyntax,bTruth_exIn_r181,boolean_realize_bounded_formula_and,
    boolean_realize_bounded_formula_mem',bTerm_current_r181,bTerm_up_r181,
    bTerm_up2_r181,bTerm_up3_r181] at hImp
  refine (le_inf hImp ?_).trans Lattice.bv_imp_elim
  refine le_inf (hy.trans inf_le_left) ?_
  apply le_iSup_of_le a
  have hF : bTerm (DVec.cons y (DVec.cons W (DVec.cons z v))) (up (up2 F)) = bTerm v F :=
    (bTerm_up_r181 (DVec.cons W (DVec.cons z v)) y (up2 F)).trans (bTerm_up2_r181 v z W F)
  refine le_inf ?_ (hy.trans inf_le_right)
  rw [hF]
  exact ha

theorem valueCertificate_body_ext {n : ℕ} (v : DVec (V B) n)
    (z W a : bSet B) : bSet.B_ext (valueCertificate v z W a) := by
  intro x y
  let p : B := (x =ᴮ y)
  let t := DVec.cons W (DVec.cons z v)
  let Sx := DVec.cons x t
  let Sy := DVec.cons y t
  have hVec : ∀ i : Fin (n+3),p ≤ Sx.nth i.val i.isLt =ᴮ Sy.nth i.val i.isLt := by
    intro i
    exact Fin.cases (show p ≤ x =ᴮ y from le_rfl) (fun _ => bv_refl) i
  have hVec' : ∀ i : Fin (n+4),
      p ≤ (DVec.cons a Sx).nth i.val i.isLt =ᴮ (DVec.cons a Sy).nth i.val i.isLt := by
    intro i
    exact Fin.cases (show p ≤ a =ᴮ a from bv_refl) (fun j => hVec j) i
  unfold valueCertificate
  apply le_inf
  · exact (le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans
      ((bTruth_vecMask_r191 p Sx Sy _ hVec).le.trans inf_le_right)
  · exact (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans
      ((bTruth_vecMask_r191 p _ _ _ hVec').le.trans inf_le_right)

theorem choose_actual_eval_name {n : ℕ} (v : DVec (V B) n) (z W a : bSet B) :
    ∃ y : bSet B,(⨆ w : bSet B,valueCertificate v z W a w) = valueCertificate v z W a y :=
  bSet.maximum_principle _ (valueCertificate_body_ext v z W a)

end JSP000930.Positive
