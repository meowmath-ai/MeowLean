import JSP000933FiniteCheckedGraph
import JSP000933FiniteBooleanWitnesses

open scoped Flypitch
open Lattice

namespace JSP000933
namespace PositiveForcing

open CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem prop_of_le_crisp_nonzero_r190 {p : B} {φ : Prop}
    (hp : p ≠ ⊥) (h : p ≤ crispTruth B φ) : φ := by
  classical
  by_contra hn
  exact hp (le_bot_iff.mp (by simpa [crispTruth,hn] using h))

theorem crisp_and_r190 (φ ψ : Prop) :
    crispTruth B (φ ∧ ψ) = crispTruth B φ ⊓ crispTruth B ψ := by
  classical
  by_cases hφ : φ <;> by_cases hψ : ψ <;> simp [crispTruth,hφ,hψ]

theorem crisp_imp_r190 (φ ψ : Prop) :
    crispTruth B (φ → ψ) = imp (crispTruth B φ) (crispTruth B ψ) := by
  classical
  by_cases hφ : φ <;> by_cases hψ : ψ <;> simp [crispTruth,_root_.imp,hφ,hψ]

noncomputable def natTableTotal (G : bSet B) (n : ℕ) : B :=
  ⨅ i : Fin (n+1), ⨆ y : ℕ, valueAtNat G i.val y

noncomputable def natTableUnique (G : bSet B) (n : ℕ) : B :=
  ⨅ i : Fin (n+1), ⨅ y : ℕ, ⨅ z : ℕ,
    imp (valueAtNat G i.val y ⊓ valueAtNat G i.val z) (crispTruth B (y = z))

noncomputable def natTableSteps (G : bSet B) (n : ℕ) (Step : ℕ → ℕ → ℕ → Prop) : B :=
  ⨅ i : Fin n, ⨅ y : ℕ, ⨅ z : ℕ,
    imp (valueAtNat G i.val y ⊓ valueAtNat G (i.val+1) z) (crispTruth B (Step i.val y z))

noncomputable def finiteRecursionValue (B : Type) [NontrivialCompleteBooleanAlgebra B]
    (n base result : ℕ) (Step : ℕ → ℕ → ℕ → Prop) : B :=
  ⨆ G : bSet B, natTableTotal G n ⊓ (natTableUnique G n ⊓
    (valueAtNat G 0 base ⊓ (valueAtNat G n result ⊓ natTableSteps G n Step)))

def FiniteRecursion (n base result : ℕ) (Step : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ f : Fin (n+1) → ℕ, f 0 = base ∧ f (Fin.last n) = result ∧
    ∀ i : Fin n, Step i.val (f i.castSucc) (f i.succ)

theorem finiteRecursionValue_crisp_r190 (n base result : ℕ) (Step : ℕ → ℕ → ℕ → Prop) :
    finiteRecursionValue B n base result Step = crispTruth B (FiniteRecursion n base result Step) := by
  classical
  by_cases hRec : FiniteRecursion n base result Step
  · have hR : crispTruth B (FiniteRecursion n base result Step) = ⊤ := by simp [crispTruth,hRec]
    rw [hR]
    apply top_unique
    obtain ⟨f,h0,hN,hStep⟩ := hRec
    let G := checkedFiniteGraph (B := B) f
    apply le_iSup_of_le G
    have hv (i : Fin (n+1)) (y : ℕ) : valueAtNat G i.val y = crispTruth B (f i = y) :=
      checkedFiniteGraph_value_at_index_r189 f i y
    have ht : (⊤ : B) ≤ natTableTotal G n := by
      apply le_iInf
      intro i
      apply le_iSup_of_le (f i)
      rw [hv]
      simp [crispTruth]
    have hu : (⊤ : B) ≤ natTableUnique G n := by
      apply le_iInf
      intro i
      apply le_iInf
      intro y
      apply le_iInf
      intro z
      change (⊤ : B) ≤ imp (valueAtNat G i.val y ⊓ valueAtNat G i.val z) (crispTruth B (y = z))
      rw [hv i y,hv i z,← crisp_and_r190,← crisp_imp_r190]
      have h : (f i = y ∧ f i = z) → y = z := fun h => h.1.symm.trans h.2
      unfold crispTruth
      rw [ite_eq_left h]
    have hB : (⊤ : B) ≤ valueAtNat G 0 base := by
      change (⊤ : B) ≤ valueAtNat G (0 : Fin (n+1)).val base
      rw [hv]
      simp [crispTruth,h0]
    have hL : (⊤ : B) ≤ valueAtNat G n result := by
      change (⊤ : B) ≤ valueAtNat G (Fin.last n).val result
      rw [hv]
      simp [crispTruth,hN]
    have hs : (⊤ : B) ≤ natTableSteps G n Step := by
      apply le_iInf
      intro i
      apply le_iInf
      intro y
      apply le_iInf
      intro z
      change (⊤ : B) ≤ imp (valueAtNat G i.castSucc.val y ⊓ valueAtNat G i.succ.val z)
        (crispTruth B (Step i.val y z))
      rw [hv i.castSucc y,hv i.succ z,← crisp_and_r190,← crisp_imp_r190]
      have h : (f i.castSucc = y ∧ f i.succ = z) → Step i.val y z := by
        rintro ⟨hy,hz⟩
        exact hy ▸ hz ▸ hStep i
      unfold crispTruth
      rw [ite_eq_left h]
    exact le_inf ht (le_inf hu (le_inf hB (le_inf hL hs)))
  · rw [show crispTruth B (FiniteRecursion n base result Step) = ⊥ by simp [crispTruth,hRec]]
    apply le_bot_iff.mp
    apply iSup_le
    intro G
    let p := natTableTotal G n ⊓ (natTableUnique G n ⊓
      (valueAtNat G 0 base ⊓ (valueAtNat G n result ⊓ natTableSteps G n Step)))
    change p ≤ ⊥
    by_contra hP
    have hp : p ≠ ⊥ := fun h => hP h.le
    have hT : p ≤ ⨅ i : Fin (n+1), ⨆ y : ℕ, valueAtNat G i.val y := inf_le_left
    obtain ⟨f,q,hq,hqp,hF⟩ := exists_nonzero_finiteChoices_fin_r135 (n+1)
      (fun i y => valueAtNat G i.val y) p hp hT
    have hU (i : Fin (n+1)) (y z : ℕ) : q ≤ imp (valueAtNat G i.val y ⊓ valueAtNat G i.val z)
        (crispTruth B (y = z)) := by
      have hu : q ≤ natTableUnique G n := hqp.trans (inf_le_right.trans inf_le_left)
      exact hu.trans ((iInf_le _ i).trans ((iInf_le _ y).trans (iInf_le _ z)))
    have hB : q ≤ valueAtNat G 0 base := hqp.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
    have hL : q ≤ valueAtNat G n result := hqp.trans
      (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
    have hS : q ≤ natTableSteps G n Step := hqp.trans
      (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
    apply hRec
    refine ⟨f,?_,?_,?_⟩
    · exact prop_of_le_crisp_nonzero_r190 hq
        (_root_.context_imp_elim (hU 0 (f 0) base) (le_inf (hF 0) hB))
    · exact prop_of_le_crisp_nonzero_r190 hq
        (_root_.context_imp_elim (hU (Fin.last n) (f (Fin.last n)) result)
          (le_inf (hF (Fin.last n)) hL))
    · intro i
      have himp : q ≤ imp (valueAtNat G i.val (f i.castSucc) ⊓ valueAtNat G (i.val+1) (f i.succ))
          (crispTruth B (Step i.val (f i.castSucc) (f i.succ))) :=
        hS.trans ((iInf_le _ i).trans ((iInf_le _ (f i.castSucc)).trans (iInf_le _ (f i.succ))))
      exact prop_of_le_crisp_nonzero_r190 hq
        (_root_.context_imp_elim himp (le_inf (hF i.castSucc) (hF i.succ)))

end PositiveForcing
end JSP000933
