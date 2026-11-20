import JSP000933ActualSectionContinuity
import Mathlib.Tactic.Tauto

open scoped Flypitch symmDiff

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem nameErrorBudget_mask_r298 (h : Bool) (k n : ℕ) (a b z : ℕ → B) :
    nameErrorBudget h k n a b≤nameErrorBudget h k n (bitsMeet z a) (bitsMeet z b) := by
  let e : SetBitExpr (Fin 4) := (SetBitExpr.var 0).symmDiff (.var 1)
  let r : SetBitExpr (Fin 4) := (SetBitExpr.meet (.var 2) (.var 0)).symmDiff (.meet (.var 2) (.var 1))
  let E : BudgetExpr (Fin 4) := ⟨h,e,.const false,k⟩
  let R : BudgetExpr (Fin 4) := ⟨h,r,.const false,k⟩
  have hh (x : Fin 4 → Set ℕ) : E.groundHolds x n → R.groundHolds x n := by
    intro hE
    apply GroundBudgetHolds.of_diff_subset_r232 h k n _ hE
    intro m hm
    simp [E,R,e,r,SetBitExpr.groundSet,SetBitExpr.evalProp,SetBitExpr.symmDiff,
      SetBitExpr.join,Set.mem_sdiff,Set.mem_union,Set.mem_inter_iff] at hm ⊢ <;> tauto
  have hLift := finite_budget_unary_r233 E R (nameFour a b z z) n hh
  unfold nameErrorBudget bitsSymmDiff bitsJoin bitsMeet bitsComplement
  simpa [E,R,e,r,BudgetExpr.namedValue,SetBitExpr.namedSet,SetBitExpr.symmDiff,
    SetBitExpr.evalB_join_r249,SetBitExpr.evalB,nameFour,bitsSymmDiff,bitsJoin,bitsMeet,
    bitsComplement,truthBit,membershipBits_realBitsName_r128] using hLift

theorem eventuallySmallError_mask_r298 (h : Bool) (k : ℕ) (a b z : ℕ → B) :
    eventuallySmallError h k a b≤eventuallySmallError h k (bitsMeet z a) (bitsMeet z b) := by
  unfold eventuallySmallError eventualBudgetAt
  apply iSup_le
  intro N
  apply le_iSup_of_le N
  apply budgetTail_of_forall_r229
  intro n hn
  exact (budgetTail_apply_r229 _ k N n hn).trans (nameErrorBudget_mask_r298 h k n a b z)

theorem sectionFreeBits_mask_sectionPoint_r298 (P x : ℕ → B) (b : Bool) (m : ℕ) :
    sectionFreeBits P b m⊓actualSectionPoint P b x m=sectionFreeBits P b m⊓x m := by
  unfold actualSectionPoint
  rw [inf_sup_left]
  simp only [← inf_assoc,inf_idem,inf_compl_eq_bot',bot_inf_eq,sup_bot_eq]

def actualCoordinateFace (c P : ℕ → B) (b : Bool) : ℕ → B :=
  bitsMeet c (sectionFreeBits P b)

theorem actualFace_section_payload_r298 (c P x : ℕ → B) (b : Bool) :
    bitsMeet (actualCoordinateFace c P b) (bitsMeet c (actualSectionPoint P b x)) =
    bitsMeet (actualCoordinateFace c P b) x := by
  funext m
  let e := sectionFreeBits P b m
  let y := actualSectionPoint P b x m
  change (c m⊓e)⊓(c m⊓y)=(c m⊓e)⊓x m
  calc
    (c m⊓e)⊓(c m⊓y)=(c m⊓c m)⊓(e⊓y) := by ac_rfl
    _=c m⊓(e⊓x m) := by
      change (c m⊓c m)⊓(sectionFreeBits P b m⊓actualSectionPoint P b x m)=c m⊓(sectionFreeBits P b m⊓x m)
      rw [inf_idem,sectionFreeBits_mask_sectionPoint_r298 P x b m]
    _=(c m⊓e)⊓x m := (inf_assoc _ _ _).symm

theorem bitsSymmDiff_at_r298 (x y : ℕ → B) (m : ℕ) :
    bitsSymmDiff x y m=x m ∆ y m := by
  simp only [bitsSymmDiff,bitsJoin,bitsMeet,bitsComplement,symmDiff_def,sdiff_eq,inf_comm (y m) (x m)ᶜ]

theorem actualFaces_payload_xor_r298 (c P x : ℕ → B) :
    bitsSymmDiff (bitsMeet (actualCoordinateFace c P false) x)
      (bitsMeet (actualCoordinateFace c P true) x)=bitsMeet c x := by
  funext m
  rw [bitsSymmDiff_at_r298]
  let a := c m⊓x m
  let b := P (4*m)
  have h0 : bitsMeet (actualCoordinateFace c P false) x m=a⊓bᶜ := by
    change (c m⊓bᶜ)⊓x m=(c m⊓x m)⊓bᶜ
    ac_rfl
  have h1 : bitsMeet (actualCoordinateFace c P true) x m=a⊓b := by
    change (c m⊓b)⊓x m=(c m⊓x m)⊓b
    ac_rfl
  rw [h0,h1,← inf_symmDiff_distrib_left]
  have hb : bᶜ ∆ b=⊤ := by
    simp only [symmDiff_def,sdiff_eq,compl_compl,inf_idem,compl_sup_eq_top]
  rw [hb,inf_top_eq] <;> rfl

end SetLanguage
end JSP000933
