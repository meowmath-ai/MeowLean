import JSP000933CrossingTargetNullError
import Mathlib.Tactic.Tauto

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def SetBitExpr.join {I : Type} (a b : SetBitExpr I) : SetBitExpr I :=
  .neg (SetBitExpr.meet (.neg a) (.neg b))

def SetBitExpr.symmDiff {I : Type} (a b : SetBitExpr I) : SetBitExpr I :=
  (SetBitExpr.meet a (.neg b)).join (SetBitExpr.meet (.neg a) b)

theorem SetBitExpr.evalB_join_r249 {I : Type} (e f : SetBitExpr I) (x : I → B) :
    (e.join f).evalB x = e.evalB x ⊔ f.evalB x := by
  simp only [SetBitExpr.join,SetBitExpr.evalB,compl_inf,compl_compl]

theorem ground_anchor_crossingCover_r249 (H A C D E : Set ℕ) :
    ((A∩E) \ (D∩C)) ∪ ((D∩C) \ (A∩E)) ⊆
      (((H∩A) \ C) ∪ (C \ (H∩A))) ∪ (((H∩D) \ E) ∪ (E \ (H∩D))) := by
  classical
  intro i hi
  simp only [Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff] at hi ⊢
  tauto

def anchorFive (x a b c d : ℕ → B) (i : Fin 5) : ℕ → B :=
  if i=0 then x else if i=1 then a else if i=2 then b else if i=3 then c else d

theorem anchor_crossError_budget_r249 (h : Bool) (H a b c d : ℕ → B) (k n : ℕ) :
    nameBudgetValue h (realBitsName (bitsSymmDiff (bitsMeet H a) b)) (realBitsName (fun _ => ⊥)) (2*k) n ⊓
      nameBudgetValue h (realBitsName (bitsSymmDiff (bitsMeet H c) d)) (realBitsName (fun _ => ⊥)) (2*k) n ≤
    nameBudgetValue h (realBitsName (bitsSymmDiff (bitsMeet a d) (bitsMeet c b))) (realBitsName (fun _ => ⊥)) k n := by
  let ex : SetBitExpr (Fin 5) := (SetBitExpr.meet (.var 0) (.var 1)).symmDiff (.var 2)
  let ey : SetBitExpr (Fin 5) := (SetBitExpr.meet (.var 0) (.var 3)).symmDiff (.var 4)
  let cross : SetBitExpr (Fin 5) := (SetBitExpr.meet (.var 1) (.var 4)).symmDiff (SetBitExpr.meet (.var 3) (.var 2))
  let E : BudgetExpr (Fin 5) := ⟨h,ex,.const false,2*k⟩
  let F : BudgetExpr (Fin 5) := ⟨h,ey,.const false,2*k⟩
  let R : BudgetExpr (Fin 5) := ⟨h,cross,.const false,k⟩
  let X (i : Fin 5) := realBitsName (anchorFive H a b c d i)
  have hG (y : Fin 5 → Set ℕ) : E.groundHolds y n → F.groundHolds y n → R.groundHolds y n := by
    intro he hf
    apply GroundBudgetHolds.of_diff_cover_r232 h k n _ he hf
    intro i hi
    have hh := ground_anchor_crossingCover_r249 (y 0) (y 1) (y 2) (y 3) (y 4)
    simp only [SetBitExpr.groundSet,SetBitExpr.evalProp,SetBitExpr.join,SetBitExpr.symmDiff,
      Set.mem_ofPred_eq,Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff,E,F,R,ex,ey,cross] at hi ⊢
    have hh' : i ∈ (((y 1 ∩ y 4) \ (y 3 ∩ y 2)) ∪ ((y 3 ∩ y 2) \ (y 1 ∩ y 4))) →
        i ∈ ((((y 0 ∩ y 1) \ y 2) ∪ (y 2 \ (y 0 ∩ y 1))) ∪
          (((y 0 ∩ y 3) \ y 4) ∪ (y 4 \ (y 0 ∩ y 3)))) := fun h => hh h
    simp only [Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff] at hh'
    tauto
  have hF := finite_budget_binary_r233 E F R X n hG
  simp [E,F,R,X,ex,ey,cross,BudgetExpr.namedValue,SetBitExpr.namedSet,SetBitExpr.symmDiff,
    SetBitExpr.evalB_join_r249,SetBitExpr.evalB,anchorFive,truthBit,membershipBits_realBitsName_r128] at hF
  unfold bitsSymmDiff bitsJoin bitsMeet bitsComplement
  simpa only [compl_inf] using hF

noncomputable def smallAllPrefixes (h : Bool) (k : ℕ) (x : ℕ → B) : B :=
  ⨅ n : ℕ, nameBudgetValue h (realBitsName x) (realBitsName (fun _ => ⊥)) k n

noncomputable def smallTailPrefixes (h : Bool) (k N : ℕ) (x : ℕ → B) : B :=
  budgetTail (nameBudgetValue h (realBitsName x) (realBitsName (fun _ => ⊥))) k N

end SetLanguage
end JSP000933
