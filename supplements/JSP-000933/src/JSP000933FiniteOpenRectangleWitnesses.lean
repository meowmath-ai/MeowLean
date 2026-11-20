import JSP000933FiniteBooleanWitnesses

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

theorem exists_decided_initialWord_r136 (x : ℕ → B) (n : ℕ)
    (p : B) (hp : p ≠ ⊥) :
    ∃ w : Word, w.length = n ∧ ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧ q ≤ cylinderValue x w := by
  let f (i : Fin n) (b : Bool) := literal (x i.val) b
  have hf : p ≤ ⨅ i, ⨆ b, f i b := by
    apply le_iInf
    intro i
    have ht : (⊤ : B) = (x i.val)ᶜ ⊔ x i.val := by rw [compl_sup_eq_top]
    exact le_top.trans (ht.le.trans (sup_le (le_iSup (f i) false) (le_iSup (f i) true)))
  obtain ⟨g,q,hq,hqp,hG⟩ := exists_nonzero_finiteChoices_fin_r135 n f p hp hf
  let w := List.ofFn g
  have hLen : w.length = n := List.length_ofFn
  refine ⟨w,hLen,q,hq,hqp,?_⟩
  apply le_iInf
  intro i
  have hi : i.val < n := hLen ▸ i.isLt
  have hWord : w[i.val] = g ⟨i.val,hi⟩ := List.getElem_ofFn i.isLt
  rw [hWord]
  exact hG ⟨i.val,hi⟩

theorem edgeBox_suffices_r136 (K : Word × Word → B) (x y : ℕ → B)
    (w : Word × Word) {p : B} (hk : p ≤ K w) (hx : p ≤ cylinderValue x w.1)
    (hy : p ≤ cylinderValue y w.2) : p ≤ colorValue K x y :=
  le_iSup_of_le w (le_inf hk (le_inf hx hy))

theorem exists_common_openBoxes_r136 {n m : ℕ}
    (K : Word × Word → B) (x : Fin n → ℕ → B) (y : Fin m → ℕ → B)
    (F : Finset (Fin n × Fin m)) (p : B) (hp : p ≠ ⊥)
    (hEdge : ∀ ij ∈ F, p ≤ colorValue K (x ij.1) (y ij.2)) :
    ∃ w : ↥F → Word × Word, ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧
      ∀ ij : ↥F, q ≤ K (w ij) ∧ q ≤ cylinderValue (x ij.1.1) (w ij).1 ∧
        q ≤ cylinderValue (y ij.1.2) (w ij).2 := by
  let test (ij : ↥F) (w : Word × Word) :=
    K w ⊓ (cylinderValue (x ij.1.1) w.1 ⊓ cylinderValue (y ij.1.2) w.2)
  obtain ⟨w,q,hq,hqp,hw⟩ := exists_nonzero_finiteChoices_r135 test p hp
    (le_iInf (fun ij => hEdge ij.1 ij.2))
  exact ⟨w,q,hq,hqp,fun ij => ⟨(hw ij).trans inf_le_left,
    (hw ij).trans (inf_le_right.trans inf_le_left),
    (hw ij).trans (inf_le_right.trans inf_le_right)⟩⟩

end CantorCodes
end JSP000933
