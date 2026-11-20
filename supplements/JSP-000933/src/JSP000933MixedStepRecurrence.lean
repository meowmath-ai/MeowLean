import JSP000933FiniteRecursionCrisp
import JSP000933FiniteBooleanWitnesses

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def tableStepValues (G : bSet B) (n : ℕ) (S : ℕ → ℕ → ℕ → B) : B :=
  ⨅ i : Fin n, ⨅ y : ℕ, ⨅ z : ℕ,
    imp (valueAtNat G i.val y ⊓ valueAtNat G (i.val+1) z) (S i.val y z)

noncomputable def recurrenceOfGraphs (B : Type) [NontrivialCompleteBooleanAlgebra B]
    (n base out : ℕ) (S : ℕ → ℕ → ℕ → B) : B :=
  ⨆ G : bSet B, natTableTotal G n ⊓ (natTableUnique G n ⊓
    (valueAtNat G 0 base ⊓ (valueAtNat G n out ⊓ tableStepValues G n S)))

noncomputable def recurrenceOfTables (B : Type) [NontrivialCompleteBooleanAlgebra B]
    (n base out : ℕ) (S : ℕ → ℕ → ℕ → B) : B :=
  ⨆ f : Fin (n+1) → ℕ, crispTruth B (f 0 = base ∧ f (Fin.last n) = out) ⊓
    (⨅ i : Fin n, S i.val (f i.castSucc) (f i.succ))

theorem le_of_nonzero_dense_refinements_r207 (a b : B)
    (h : ∀ p : B, p ≠ ⊥ → p ≤ a → ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧ q ≤ b) : a ≤ b := by
  classical
  by_contra hn
  let p := a ⊓ bᶜ
  have hp : p ≠ ⊥ := by
    intro hz
    have hd : Disjoint a bᶜ := disjoint_iff_inf_le.mpr hz.le
    exact hn (by simpa only [compl_compl] using (le_compl_iff_disjoint_right.mpr hd))
  obtain ⟨q,hq,hqp,hqb⟩ := h p hp inf_le_left
  exact hq (le_bot_iff.mp ((le_inf hqb (hqp.trans inf_le_right)).trans_eq (inf_compl_eq_bot' (x := b))))

theorem recurrence_graphs_eq_tables_r207 (n base out : ℕ) (S : ℕ → ℕ → ℕ → B) :
    recurrenceOfGraphs B n base out S = recurrenceOfTables B n base out S := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro G
    apply le_of_nonzero_dense_refinements_r207
    intro p hp hP
    have hT : p ≤ ⨅ i : Fin (n+1), ⨆ y : ℕ, valueAtNat G i.val y := hP.trans inf_le_left
    obtain ⟨f,q,hq,hqp,hF⟩ := exists_nonzero_finiteChoices_fin_r135 (n+1)
      (fun i y => valueAtNat G i.val y) p hp hT
    have hqP := hqp.trans hP
    have hU (i : Fin (n+1)) (y z : ℕ) :
        q ≤ imp (valueAtNat G i.val y ⊓ valueAtNat G i.val z) (crispTruth B (y = z)) := by
      have hu : q ≤ natTableUnique G n := hqP.trans (inf_le_right.trans inf_le_left)
      exact hu.trans ((iInf_le _ i).trans ((iInf_le _ y).trans (iInf_le _ z)))
    have hB : q ≤ valueAtNat G 0 base :=
      hqP.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
    have hL : q ≤ valueAtNat G n out :=
      hqP.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
    have hS : q ≤ tableStepValues G n S :=
      hqP.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
    have h0 : f 0 = base := prop_of_le_crisp_nonzero_r190 hq
      (_root_.context_imp_elim (hU 0 (f 0) base) (le_inf (hF 0) hB))
    have hN : f (Fin.last n) = out := prop_of_le_crisp_nonzero_r190 hq
      (_root_.context_imp_elim (hU (Fin.last n) (f (Fin.last n)) out) (le_inf (hF (Fin.last n)) hL))
    refine ⟨q,hq,hqp,le_iSup_of_le f (le_inf ?_ ?_)⟩
    · simp [crispTruth,h0,hN]
    · apply le_iInf
      intro i
      have himp : q ≤ imp (valueAtNat G i.val (f i.castSucc) ⊓ valueAtNat G (i.val+1) (f i.succ))
          (S i.val (f i.castSucc) (f i.succ)) :=
        hS.trans ((iInf_le _ i).trans ((iInf_le _ (f i.castSucc)).trans (iInf_le _ (f i.succ))))
      exact _root_.context_imp_elim himp (le_inf (hF i.castSucc) (hF i.succ))
  · apply iSup_le
    intro f
    let G := checkedFiniteGraph (B := B) f
    apply le_iSup_of_le G
    let p := crispTruth B (f 0 = base ∧ f (Fin.last n) = out) ⊓
      (⨅ i : Fin n, S i.val (f i.castSucc) (f i.succ))
    change p ≤ _
    have hv (i : Fin (n+1)) (y : ℕ) : valueAtNat G i.val y = crispTruth B (f i = y) :=
      checkedFiniteGraph_value_at_index_r189 f i y
    by_cases hE : f 0 = base ∧ f (Fin.last n) = out
    · have hT : p ≤ natTableTotal G n := by
        apply le_iInf
        intro i
        apply le_iSup_of_le (f i)
        rw [hv]
        simp [crispTruth]
      have hU : p ≤ natTableUnique G n := by
        apply le_iInf
        intro i
        apply le_iInf
        intro y
        apply le_iInf
        intro z
        change p ≤ imp (valueAtNat G i.val y ⊓ valueAtNat G i.val z) (crispTruth B (y=z))
        rw [hv i y,hv i z,← crisp_and_r190,← crisp_imp_r190]
        have hh : (f i=y ∧ f i=z) → y=z := fun h => h.1.symm.trans h.2
        unfold crispTruth
        rw [ite_eq_left hh]
        exact le_top
      have hB : p ≤ valueAtNat G 0 base := by
        change p ≤ valueAtNat G (0 : Fin (n+1)).val base
        rw [hv]
        simp [crispTruth,hE.1]
      have hL : p ≤ valueAtNat G n out := by
        change p ≤ valueAtNat G (Fin.last n).val out
        rw [hv]
        simp [crispTruth,hE.2]
      refine le_inf hT (le_inf hU (le_inf hB (le_inf hL ?_)))
      apply le_iInf
      intro i
      apply le_iInf
      intro y
      apply le_iInf
      intro z
      change p ≤ imp (valueAtNat G i.castSucc.val y ⊓ valueAtNat G i.succ.val z) (S i.val y z)
      rw [hv i.castSucc y,hv i.succ z]
      by_cases hy : f i.castSucc = y
      · by_cases hz : f i.succ = z
        · rw [← hy,← hz]
          simpa [crispTruth,_root_.imp] using
            (show p ≤ S i.val (f i.castSucc) (f i.succ) from inf_le_right.trans (iInf_le _ i))
        · simp [crispTruth,_root_.imp,hz]
      · simp [crispTruth,_root_.imp,hy]
    · have hp : p = ⊥ := by simp [p,crispTruth,hE]
      rw [hp]
      exact bot_le

end SetLanguage
end JSP000933
