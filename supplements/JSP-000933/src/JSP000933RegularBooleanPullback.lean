import JSP000933RegularRestriction

namespace JSP000933
namespace BooleanCompletion

universe u v w
variable {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]

theorem regular_iSup_eq_r91 {I : Type w} (U : I → RO P) :
    (⨆ i, U i) = Heyting.Regular.toRegular (⨆ i, (U i : LowerSet P)) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    have hh := Heyting.Regular.toRegular.monotone
      (le_iSup (fun j => (U j : LowerSet P)) i)
    simpa only [Heyting.Regular.toRegular_coe] using hh
  · apply (Heyting.Regular.gi.gc _ _).mpr
    apply iSup_le
    intro i
    exact Heyting.Regular.coe_le_coe.mpr (le_iSup U i)

theorem RestrictionMap.boolPullback_injective_r91 (F : RestrictionMap P Q) :
    Function.Injective F.boolPullback := by
  intro U V h
  exact le_antisymm ((F.boolPullback_le_iff_r90 U V).mp h.le)
    ((F.boolPullback_le_iff_r90 V U).mp h.ge)

theorem RestrictionMap.boolPullback_top_r91 (F : RestrictionMap P Q) :
    F.boolPullback (⊤ : RO Q) = ⊤ := by
  apply Heyting.Regular.coe_injective
  change F.lowerPullback ((⊤ : RO Q) : LowerSet Q) = ((⊤ : RO P) : LowerSet P)
  simp only [Heyting.Regular.coe_top]
  ext p
  rfl

theorem RestrictionMap.boolPullback_bot_r91 (F : RestrictionMap P Q) :
    F.boolPullback (⊥ : RO Q) = ⊥ := by
  rw [← compl_top,F.boolPullback_compl_r90,F.boolPullback_top_r91,compl_top]

theorem RestrictionMap.boolPullback_inf_r91 (F : RestrictionMap P Q) (U V : RO Q) :
    F.boolPullback (U ⊓ V) = F.boolPullback U ⊓ F.boolPullback V := by
  apply Heyting.Regular.coe_injective
  change F.lowerPullback (↑(U ⊓ V) : LowerSet Q) =
    (↑(F.boolPullback U ⊓ F.boolPullback V) : LowerSet P)
  simp only [Heyting.Regular.coe_inf]
  ext p
  rfl

theorem RestrictionMap.boolPullback_iSup_r91 (F : RestrictionMap P Q) {I : Type w}
    (U : I → RO Q) : F.boolPullback (⨆ i, U i) = ⨆ i, F.boolPullback (U i) := by
  rw [regular_iSup_eq_r91,regular_iSup_eq_r91]
  apply Heyting.Regular.coe_injective
  change F.lowerPullback (↑(Heyting.Regular.toRegular (⨆ i, (U i : LowerSet Q))) : LowerSet Q) =
    (↑(Heyting.Regular.toRegular (⨆ i, (F.boolPullback (U i) : LowerSet P))) : LowerSet P)
  simp only [Heyting.Regular.coe_toRegular,F.lowerPullback_compl_r90,F.lowerPullback_iSup_r90] <;> rfl

theorem RestrictionMap.boolPullback_iInf_r91 (F : RestrictionMap P Q) {I : Type w}
    (U : I → RO Q) : F.boolPullback (⨅ i, U i) = ⨅ i, F.boolPullback (U i) := by
  have ht : (⨅ i, U i) = (⨆ i, (U i)ᶜ)ᶜ := by simp only [compl_iSup,compl_compl]
  rw [ht,F.boolPullback_compl_r90,F.boolPullback_iSup_r91,compl_iSup]
  simp only [F.boolPullback_compl_r90,compl_compl]

end BooleanCompletion
end JSP000933
