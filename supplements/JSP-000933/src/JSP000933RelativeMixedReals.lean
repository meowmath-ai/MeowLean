import JSP000933RelativeOmegaOne
import JSP000933MaximumRealName

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

def EnumeratesBooleanReals (e : OmegaOneIndex→ℕ→B) : Prop :=
  ∀ x : ℕ→B,(⨆ i,realEqValue x (e i))=⊤

noncomputable def mixIndexedReal {I : Type} (w : I→B) (x : I→ℕ→B) : ℕ→B :=
  fun n => ⨆ i,w i⊓x i n

theorem mixIndexedReal_on_weight_r439 {I : Type} (w : I→B)
    (hW : Pairwise (fun i j => Disjoint (w i) (w j))) (x : I→ℕ→B) (i : I) :
    w i≤realEqValue (mixIndexedReal w x) (x i) := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro n
  change w i⊓(⨆ j,w j⊓x j n)=w i⊓x i n
  rw [inf_iSup_eq]
  apply le_antisymm
  · apply iSup_le
    intro j
    by_cases he : i=j
    · subst j
      exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · exact ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans
        (disjoint_iff_inf_le.mp (hW he))).trans bot_le
  · apply le_iSup_of_le i
    exact le_inf inf_le_left le_rfl

theorem enumeratesBooleanReals_congr_r439 (e : OmegaOneIndex→ℕ→B)
    (hE : EnumeratesBooleanReals e) (m : B) (x : ℕ→B) :
    m=(⨆ i,m⊓realEqValue x (e i)) := by
  rw [← inf_iSup_eq,hE x,inf_top_eq]

end RelativeOCA
end JSP000933
