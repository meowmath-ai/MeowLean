import JSP000930AnalyticTaylorLimit

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_selectReal_masked {n k : ℕ} (v : DVec (V B) n)
    (ps : Fin k → STerm n)
    (R D : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d)
    (w : RatPresentation → B) (p : B)
    (hw : ProperCutOn p w)
    (hR : ∀ u : RatPresentation → B,
      let a := weightedRationalSet u
      let Va := DVec.cons a v
      let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
      p ⊓ bTruth Va (R (fun i => up (ps i)) T) = p ⊓ (a =ᴮ weightedRationalSet w)) :
    let Vw := DVec.cons (weightedRationalSet w) v
    let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    p ⊓ bTruth v (selectReal_f ps R D) =
      p ⊓ bTruth Vw (D (fun i => up (ps i)) T) := by
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let Vx (x : bSet B) := DVec.cons x v
  let φ := R (fun i => up (ps i)) T
  let ψ := D (fun i => up (ps i)) T
  let W := weightedRationalSet w
  change p ⊓ bTruth v (selectReal_f ps R D) = p ⊓ bTruth (Vx W) ψ
  simp only [selectReal_f,bTruth_sEx_r181,boolean_realize_bounded_formula_and]
  change (p ⊓ (⨆ x : bSet B, bTruth (Vx x) (realCut_f T) ⊓
    (bTruth (Vx x) φ ⊓ bTruth (Vx x) ψ))) = _
  rw [inf_iSup_eq]
  apply le_antisymm
  · refine iSup_le fun x => ?_
    let e := p ⊓ (bTruth (Vx x) (realCut_f T) ⊓ (bTruth (Vx x) φ ⊓ bTruth (Vx x) ψ))
    change e ≤ _
    have hep : e ≤ p := inf_le_left
    have hcut : e ≤ bTruth (Vx x) (realCut_f T) := inf_le_right.trans inf_le_left
    have hφ : e ≤ bTruth (Vx x) φ := inf_le_right.trans (inf_le_right.trans inf_le_left)
    have hψ : e ≤ bTruth (Vx x) ψ := inf_le_right.trans (inf_le_right.trans inf_le_right)
    let u := extractRationalWeights x
    have he : e ≤ x =ᴮ weightedRationalSet u := by
      have he' := bTruth_realCut_recover (Vx x) T e hcut
      exact he'
    have hφu : e ≤ bTruth (Vx (weightedRationalSet u)) φ :=
      (le_inf le_rfl hφ).trans ((bTruth_oneMask v x (weightedRationalSet u) φ e he).le.trans inf_le_right)
    have he' : e ≤ weightedRationalSet u =ᴮ W :=
      (le_inf hep hφu).trans ((hR u).le.trans inf_le_right)
    have hxW : e ≤ x =ᴮ W :=
      bSet.bv_trans he he'
    exact le_inf hep ((le_inf le_rfl hψ).trans
      ((bTruth_oneMask v x W ψ e hxW).le.trans inf_le_right))
  · refine le_iSup_of_le W ?_
    have hc : p ≤ bTruth (Vx W) (realCut_f T) :=
      (forces_realCut_weighted_iff (Vx W) T w (bTerm_current_r181 v W) p).2 hw
    have hφ : p ≤ bTruth (Vx W) φ :=
      (le_inf le_rfl (le_top.trans bSet.bv_refl)).trans ((hR w).symm.le.trans inf_le_right)
    exact le_inf inf_le_left (le_inf (inf_le_left.trans hc)
      (le_inf (inf_le_left.trans hφ) inf_le_right))

theorem bTruth_selectRealNat_weighted {n k : ℕ} (v : DVec (V B) n)
    (ps : Fin k → STerm n)
    (D : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d)
    (i : Fin k) (m : ℕ) (p : B) (hi : bTerm v (ps i) = bSet.of_nat m) :
    let V := DVec.cons (weightedRationalSet (checkedRealBits (m : ℝ))) v
    let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    p ⊓ bTruth v (selectReal_f ps (fun a r => realNat_f (a i) r) D) =
      p ⊓ bTruth V (D (fun a => up (ps a)) T) := by
  apply bTruth_selectReal_weighted v ps (fun a r => realNat_f (a i) r) D
    (checkedRealBits m) p (properCutOn_mono le_top (checkedRealBits_properCut m))
  intro t
  let x := weightedRationalSet t
  let V := DVec.cons x v
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  exact bTruth_realNat_weighted V (up (ps i)) T m t
    ((bTerm_up_r181 v x (ps i)).trans hi) (bTerm_current_r181 v x)

theorem bTruth_selectNormSq_weighted {n k : ℕ} (v : DVec (V B) n)
    (ps : Fin k → STerm n)
    (D : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d)
    (i : Fin k) (z : ComplexBits B) (p : B)
    (hi : bTerm v (ps i) = z.name) (hz : z.CutOn p) :
    let V := DVec.cons (weightedRationalSet z.normSq) v
    let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    p ⊓ bTruth v (selectReal_f ps (fun a r => complexNormSq_f (a i) r) D) =
      p ⊓ bTruth V (D (fun a => up (ps a)) T) := by
  apply bTruth_selectReal_masked v ps (fun a r => complexNormSq_f (a i) r) D
    z.normSq p (ComplexBits.normSq_cutOn hz)
  intro t
  let x := weightedRationalSet t
  let V := DVec.cons x v
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  exact bTruth_complexNormSq_weighted V (up (ps i)) T z t p
    ((bTerm_up_r181 v x (ps i)).trans hi) (bTerm_current_r181 v x) hz

theorem bTruth_natExprSelect_checked {n k l : ℕ} (v : DVec (V B) n)
    (e : NatExpr k) (natParams : Fin k → STerm n) (args : Fin l → STerm n)
    (D : ∀ {d : ℕ}, (Fin l → STerm d) → STerm d → SForm d) (t : Fin k → ℕ)
    (h : ∀ i,bTerm v (natParams i) = bSet.of_nat (t i)) :
    let V := DVec.cons (bSet.of_nat (e.val t)) v
    let z : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    bTruth v (natExprSelect_f e natParams args D) =
      bTruth V (D (fun i => up (args i)) z) := by
  let V (j : ℕ) := DVec.cons (bSet.of_nat (𝔹 := B) j) v
  let z : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  change bTruth v (natExprSelect_f e natParams args D) = bTruth (V (e.val t)) (D (fun i => up (args i)) z)
  simp only [natExprSelect_f,bTruth_exOmega_r192,boolean_realize_bounded_formula_and]
  have hExpr (j : ℕ) : bTruth (V j) (e.rel_f (fun i => up (natParams i)) z) =
      crispTruth B (j = e.val t) :=
    bTruth_NatExpr_checked e (V j) _ z t j
      (fun i => (bTerm_up_r181 v (bSet.of_nat j) (natParams i)).trans (h i))
      (bTerm_current_r181 v (bSet.of_nat j))
  change (⨆ j : ℕ,bTruth (V j) (e.rel_f (fun i => up (natParams i)) z) ⊓
    bTruth (V j) (D (fun i => up (args i)) z)) = _
  simp only [hExpr,iSup_crispEquality_select_r193]

end JSP000930.AnalyticSyntax
