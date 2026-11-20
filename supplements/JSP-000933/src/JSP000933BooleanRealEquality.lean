import JSP000933SuccessorCliqueBelowMark

namespace JSP000933
namespace CantorCodes

open BooleanCompletion

variable {B C : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

def bitEq (x y : B) : B := (xᶜ ⊔ y) ⊓ (yᶜ ⊔ x)

noncomputable def realEqValue (x y : ℕ → B) : B :=
  ⨅ n, bitEq (x n) (y n)

theorem le_materialImp_iff_r126 (p x y : B) : p ≤ xᶜ ⊔ y ↔ p ⊓ x ≤ y := by
  constructor
  · intro h
    calc
      p ⊓ x ≤ (xᶜ ⊔ y) ⊓ x := inf_le_inf_right x h
      _ = y ⊓ x := by
        rw [inf_sup_right,show xᶜ ⊓ x = ⊥ from by rw [inf_comm,inf_compl_eq_bot'],bot_sup_eq]
      _ ≤ y := inf_le_left
  · intro h
    calc
      p = p ⊓ (xᶜ ⊔ x) := by rw [compl_sup_eq_top,inf_top_eq]
      _ = (p ⊓ xᶜ) ⊔ (p ⊓ x) := by rw [inf_sup_left]
      _ ≤ xᶜ ⊔ y := sup_le_sup inf_le_right h

theorem le_bitEq_iff_r126 (p x y : B) : p ≤ bitEq x y ↔ p ⊓ x = p ⊓ y := by
  constructor
  · intro h
    apply le_antisymm
    · exact le_inf inf_le_left ((le_materialImp_iff_r126 p x y).mp (h.trans inf_le_left))
    · exact le_inf inf_le_left ((le_materialImp_iff_r126 p y x).mp (h.trans inf_le_right))
  · intro h
    exact le_inf ((le_materialImp_iff_r126 p x y).mpr (h.le.trans inf_le_right))
      ((le_materialImp_iff_r126 p y x).mpr (h.ge.trans inf_le_right))

theorem le_realEqValue_iff_r126 (p : B) (x y : ℕ → B) :
    p ≤ realEqValue x y ↔ ∀ n, p ⊓ x n = p ⊓ y n := by
  constructor
  · intro h n
    exact (le_bitEq_iff_r126 p _ _).mp (h.trans (iInf_le _ n))
  · intro h
    exact le_iInf (fun n => (le_bitEq_iff_r126 p _ _).mpr (h n))

theorem map_realEqValue_r126 (F : CompleteValueMap B C) (x y : ℕ → B) :
    F.toFun (realEqValue x y) =
      realEqValue (fun n => F.toFun (x n)) (fun n => F.toFun (y n)) := by
  simp only [realEqValue,F.map_iInf,bitEq,F.map_inf,F.map_sup_r93,F.map_compl]

theorem mask_compl_congr_r126 {p x y : B} (h : p ⊓ x = p ⊓ y) :
    p ⊓ xᶜ = p ⊓ yᶜ := by
  have aux (z : B) : p ⊓ zᶜ = p ⊓ (p ⊓ z)ᶜ := by
    rw [compl_inf,inf_sup_left,inf_compl_eq_bot',bot_sup_eq]
  rw [aux x,aux y,h]

theorem mask_inf_congr_r126 {p x y u v : B} (h₁ : p ⊓ x = p ⊓ u) (h₂ : p ⊓ y = p ⊓ v) :
    p ⊓ (x ⊓ y) = p ⊓ (u ⊓ v) := by
  have aux (x y : B) : p ⊓ (x ⊓ y) = (p ⊓ x) ⊓ (p ⊓ y) := by
    apply le_antisymm
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
        (le_inf inf_le_left (inf_le_right.trans inf_le_right))
    · exact le_inf (inf_le_left.trans inf_le_left)
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
  rw [aux x y,aux u v,h₁,h₂]

theorem mask_iSup_congr_r126 {I : Type} {p : B} {x y : I → B}
    (h : ∀ i, p ⊓ x i = p ⊓ y i) : p ⊓ (⨆ i, x i) = p ⊓ (⨆ i, y i) := by
  rw [inf_iSup_eq,inf_iSup_eq]
  exact congrArg (fun f : I → B => iSup f) (funext h)

theorem mask_iInf_congr_r126 {I : Type} {p : B} {x y : I → B}
    (h : ∀ i, p ⊓ x i = p ⊓ y i) : p ⊓ (⨅ i, x i) = p ⊓ (⨅ i, y i) := by
  apply le_antisymm
  · apply le_inf inf_le_left
    apply le_iInf
    intro i
    exact (le_inf inf_le_left (inf_le_right.trans (iInf_le x i))).trans
      ((h i).le.trans inf_le_right)
  · apply le_inf inf_le_left
    apply le_iInf
    intro i
    exact (le_inf inf_le_left (inf_le_right.trans (iInf_le y i))).trans
      ((h i).ge.trans inf_le_right)

end CantorCodes
end JSP000933
