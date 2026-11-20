import JSP000933ActualParityCaps

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem nonzero_mask_ne_compl_r269 {p a : B} (hp : p≠⊥) : p⊓a≠p⊓aᶜ := by
  intro he
  have h0 : p⊓a≤⊥ :=
    (le_inf inf_le_right (he.le.trans inf_le_right)).trans_eq inf_compl_eq_bot'
  have h1 : p⊓aᶜ≤⊥ := he.symm.le.trans h0
  have hBot : p≤⊥ := calc
    p = p⊓(a⊔aᶜ) := by rw [sup_compl_eq_top,inf_top_eq]
    _ = (p⊓a)⊔(p⊓aᶜ) := inf_sup_left _ _ _
    _ ≤ ⊥ := sup_le h0 h1
  exact hp (le_bot_iff.mp hBot)

theorem opposedCylinders_word_ne_r269 {p : B} (hp : p≠⊥) {x y : ℕ → B} {u v : Word} {j : ℕ}
    (hU : p≤cylinderValue x u) (hV : p≤cylinderValue y v) (hu : j<u.length) (hv : j<v.length)
    (hOpp : p≤bitEq (x j) (y j)ᶜ) : u[j]'hu ≠ v[j]'hv := by
  intro he
  have hB : paddedWordBits (B := B) u j=paddedWordBits v j := by
    simp only [paddedWordBits,wordBit,dite_eq_left hu,dite_eq_left hv,he]
  have hSame : p⊓x j=p⊓y j :=
    (cylinder_fixes_paddedBits_r258 hU j hu).trans
      ((congrArg (fun b : B => p⊓b) hB).trans (cylinder_fixes_paddedBits_r258 hV j hv).symm)
  have hpOpp := (le_bitEq_iff_r126 p _ _).mp hOpp
  exact nonzero_mask_ne_compl_r269 hp (hSame.symm.trans hpOpp)

noncomputable def actualIncompCaps (e : ℕ ↪ Word) (a b : ℕ → B) : B :=
  ⨆ m : ℕ, ⨆ n : ℕ, crispTruth B (labelsIncomp (e m) (e n))⊓(a m⊓b n)

theorem opposedBranches_unboundedCaps_incomp_r269
    (x y a b : ℕ → B) (j : ℕ) {p : B}
    (hOpp : p≤bitEq (x j) (y j)ᶜ)
    (hAX : p≤bitsBelowValue a (actualBranchBits x))
    (hBY : p≤bitsBelowValue b (actualBranchBits y))
    (hAI : p≤actualUnboundedCap a) (hBI : p≤actualUnboundedCap b) :
    p≤actualIncompCaps neatBranchLabeling a b := by
  unfold actualIncompCaps
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  let C := shortBranchCut j
  obtain ⟨m,r,hr,hrq,hAR⟩ := exists_nonzero_below_choice_r135 q hq
    (fun m : {m : ℕ // C≤ m} => a m.val) (hqp.trans (hAI.trans (iInf_le _ C)))
  obtain ⟨n,s,hs,hsr,hBS⟩ := exists_nonzero_below_choice_r135 r hr
    (fun n : {n : ℕ // C≤n} => b n.val) ((hrq.trans hqp).trans (hBI.trans (iInf_le _ C)))
  have hSP := hsr.trans (hrq.trans hqp)
  have hAx : s≤actualBranchBits x m.val :=
    (le_inf hSP (hsr.trans hAR)).trans (bitsBelowValue_apply_r256 hAX m.val)
  have hBy : s≤actualBranchBits y n.val :=
    (le_inf hSP hBS).trans (bitsBelowValue_apply_r256 hBY n.val)
  obtain ⟨u,t,ht,hts,hU⟩ := exists_nonzero_below_choice_r135 s hs
    (fun w : {w : Word // m.val∈justSourceBlock (Encodable.encode w)} => cylinderValue x w.1) hAx
  obtain ⟨v,z,hz,hzt,hV⟩ := exists_nonzero_below_choice_r135 t ht
    (fun w : {w : Word // n.val∈justSourceBlock (Encodable.encode w)} => cylinderValue y w.1) (hts.trans hBy)
  have hu : j<u.val.length := by
    by_contra h
    exact (not_lt_of_ge m.property) (shortBranchCut_bounds_r265 j u.val m.val (Nat.le_of_not_gt h) u.property)
  have hv : j<v.val.length := by
    by_contra h
    exact (not_lt_of_ge n.property) (shortBranchCut_bounds_r265 j v.val n.val (Nat.le_of_not_gt h) v.property)
  have hZS := hzt.trans hts
  have hne := opposedCylinders_word_ne_r269 hz (hzt.trans hU) hV hu hv (hZS.trans (hSP.trans hOpp))
  have hComp := incompatible_labels_of_coded_late_words_r269 u.property v.property hu hv hne
  have hc : labelsIncomp (neatBranchLabeling m.val) (neatBranchLabeling n.val) := by
    intro hc
    exact hc.elim hComp.1 hComp.2
  refine ⟨z,hz,hZS.trans (hsr.trans hrq),le_iSup_of_le m.val (le_iSup_of_le n.val (le_inf ?_ ?_))⟩
  · simpa only [crispTruth,ite_eq_left hc] using (le_top : z≤⊤)
  · exact le_inf (hZS.trans (hsr.trans hAR)) (hZS.trans hBS)

end SetLanguage
end JSP000933
