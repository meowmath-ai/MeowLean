import JSP000933BooleanClosedCoverBaire

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

theorem wordExtends_appendBit_r221 (u : Word) (b : Bool) : ExtendsWord u (u ++ [b]) := by
  refine ⟨by simp,fun i => ?_⟩
  exact List.getElem_append_left' i.isLt [b]

theorem cylinder_appendBit_r221 (x : ℕ → B) (u : Word) (b : Bool) :
    cylinderValue x (u ++ [b]) = cylinderValue x u ⊓ literal (x u.length) b := by
  let e := fun i : Fin (u.length+1) =>
    (⟨i.val,by simpa using i.isLt⟩ : Fin (u ++ [b]).length)
  apply le_antisymm
  · apply le_inf (cylinderWord_mono_r173 x (wordExtends_appendBit_r221 u b))
    have h := iInf_le (fun i : Fin (u ++ [b]).length => literal (x i.val) ((u ++ [b])[i.val]))
      (e (Fin.last u.length))
    change cylinderValue x (u++[b]) ≤ literal (x u.length)
      ((u++[b])[u.length]'(e (Fin.last u.length)).isLt) at h
    simpa only [List.getElem_concat_length rfl] using h
  · apply le_iInf
    intro i
    by_cases hi : i.val < u.length
    · rw [show (u++[b])[i.val] = u[i.val] from (List.getElem_append_left' hi [b]).symm]
      exact inf_le_left.trans (iInf_le _ (⟨i.val,hi⟩ : Fin u.length))
    · have hEq : i.val=u.length := by
        have hh : i.val < u.length+1 := by simpa using i.isLt
        omega
      have hGet : (u++[b])[i.val] = b := List.getElem_concat_length hEq i.isLt
      rw [hGet,hEq]
      exact inf_le_right

theorem cylinder_binary_split_r221 (x : ℕ → B) (u : Word) :
    cylinderValue x (u++[false]) ⊔ cylinderValue x (u++[true]) = cylinderValue x u := by
  rw [cylinder_appendBit_r221,cylinder_appendBit_r221,← inf_sup_left]
  simp only [literal,compl_sup_eq_top,inf_top_eq]

theorem iInf_sup_antitone_r221 (f g : ℕ → B) (hf : Antitone f) (hg : Antitone g) :
    (⨅ n, f n ⊔ g n) = (⨅ n, f n) ⊔ (⨅ n, g n) := by
  apply le_antisymm
  · have h : (⨆ n, (f n)ᶜ) ⊓ (⨆ n, (g n)ᶜ) ≤ ⨆ n, (f n)ᶜ ⊓ (g n)ᶜ := by
      rw [iSup_inf_iSup]
      apply iSup_le
      intro ij
      apply le_iSup_of_le (max ij.1 ij.2)
      exact inf_le_inf (compl_le_compl (hf (le_max_left _ _))) (compl_le_compl (hg (le_max_right _ _)))
    simpa only [compl_inf,compl_iSup,compl_compl] using compl_le_compl h
  · apply le_iInf
    intro n
    exact sup_le_sup (iInf_le f n) (iInf_le g n)

end CantorCodes
end JSP000933
