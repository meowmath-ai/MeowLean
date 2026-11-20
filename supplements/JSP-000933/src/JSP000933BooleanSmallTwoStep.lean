import JSP000933BooleanSmallLabels

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open BooleanCompletion BooleanTwoStep OpenGraphForcing

universe u
variable {B T : Type u} [NontrivialCompleteBooleanAlgebra B] [Preorder T]
variable [DecidableRel ((· ≤ ·) : T → T → Prop)]

def smallLabelStage (V : T → B) : Stage B T where
  admitted := V
  leVal := fun q r => if q ≤ r then ⊤ else ⊥
  reflVal q := by simp
  transVal q r s := by
    by_cases hqr : q ≤ r
    · by_cases hrs : r ≤ s
      · simp [hqr,hrs,hqr.trans hrs]
      · simp [hqr,hrs]
    · simp [hqr]

theorem labelRefinement_r82 (label : T → bSet B) (V : T → B)
    {p : B} (hN : p ≠ ⊥) (x : bSet B) (hx : p ≤ x ∈ᴮ familyName label V) :
    ∃ t : T, ∃ b : B, b ≠ ⊥ ∧ b ≤ p ∧ b ≤ V t ∧ b ≤ x =ᴮ label t := by
  rw [mem_familyName_r70] at hx
  have hSome : ∃ t : T, p ⊓ (V t ⊓ (x =ᴮ label t)) ≠ ⊥ := by
    by_contra h
    apply hN
    apply le_bot_iff.mp
    have hle :
        p ≤ p ⊓ (⨆ t, V t ⊓ (x =ᴮ label t)) := le_inf le_rfl hx
    apply hle.trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro t
    by_contra ht
    exact h ⟨t,fun he => ht he.le⟩
  obtain ⟨t,ht⟩ := hSome
  exact ⟨t,_,ht,inf_le_left,inf_le_right.trans inf_le_left,inf_le_right.trans inf_le_right⟩

def liftLabelCondition (label : T → bSet B) (V : T → B)
    (hLabel : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (p : Condition (smallLabelStage V)) :
    Condition (groundLabelStage label V hLabel) :=
  ⟨p.base,label p.name,p.nonzero,p.admitted.trans_eq (mem_familyName_self_r70 label hLabel V p.name).symm⟩

theorem liftLabelCondition_dense_r82 (label : T → bSet B) (V : T → B)
    (hLabel : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (p : Condition (groundLabelStage label V hLabel)) :
    ∃ q : Condition (smallLabelStage V), liftLabelCondition label V hLabel q ≤ p := by
  obtain ⟨t,b,hN,hb,hV,he⟩ := labelRefinement_r82 label V p.nonzero p.name p.admitted
  have hself : b ≤ bSet.pair (label t) (label t) ∈ᴮ groundEdgeName label (· ≤ ·) :=
    le_top.trans (pair_mem_groundEdge_r72 label (· ≤ ·) (le_rfl : t ≤ t))
  have hP : b ≤ bSet.pair (label t) (label t) =ᴮ bSet.pair (label t) p.name :=
    bSet.pair_congr bSet.bv_refl (he.trans_eq bSet.bv_eq_symm)
  exact ⟨⟨b,t,hN,hV⟩,hb,bSet.subst_congr_mem_left' hP hself⟩

theorem liftLabelCondition_compatible_reflects_r82 (label : T → bSet B) (V : T → B)
    (hLabel : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (p q : Condition (smallLabelStage V))
    (h : Compatible (liftLabelCondition label V hLabel p) (liftLabelCondition label V hLabel q)) :
    Compatible p q := by
  obtain ⟨r,hrp,hrq⟩ := h
  obtain ⟨t,b,hN,hb,hV,he⟩ := labelRefinement_r82 label V r.nonzero r.name r.admitted
  have aux (w : Condition (smallLabelStage V)) (hw : r ≤ liftLabelCondition label V hLabel w) :
      t ≤ w.name := by
    have hOld : b ≤ bSet.pair r.name (label w.name) ∈ᴮ groundEdgeName label (· ≤ ·) :=
      hb.trans hw.2
    have hNew : b ≤ bSet.pair (label t) (label w.name) ∈ᴮ groundEdgeName label (· ≤ ·) :=
      bSet.subst_congr_mem_left' (bSet.pair_congr he bSet.bv_refl) hOld
    rw [pair_mem_groundOrder_self_r81 label hLabel] at hNew
    by_contra hn
    rw [ite_eq_right hn] at hNew
    exact hN (le_bot_iff.mp hNew)
  have htp := aux p hrp
  have htq := aux q hrq
  exact ⟨⟨b,t,hN,hV⟩,⟨hb.trans hrp.1,by simp [smallLabelStage,htp]⟩,
    ⟨hb.trans hrq.1,by simp [smallLabelStage,htq]⟩⟩

theorem countableAntichains_smallLabelStage_r82 (label : T → bSet B) (V : T → B)
    (hLabel : ∀ i j, i ≠ j → (label i =ᴮ label j) = ⊥)
    (hB : BooleanCCC B) (h : InternalCCC (familyName label V) (groundLabelStage label V hLabel)) :
    HasCountableAntichains (Condition (smallLabelStage V)) := by
  classical
  have hBig : HasCountableAntichains (Condition (groundLabelStage label V hLabel)) :=
    countableAntichains_bSet_twoStep_r80 (hrefl := groundOrder_refl_r81 label V)
      (htrans := groundOrder_trans_r81 label hLabel) hB h
  intro F hAnt
  let f := liftLabelCondition label V hLabel
  have hI : Set.InjOn f F := by
    intro p hp q hq hpq
    by_contra hn
    apply hAnt p hp q hq hn
    apply liftLabelCondition_compatible_reflects_r82 label V hLabel p q
    exact ⟨f p,le_rfl,hpq.le⟩
  have hImage : (f '' F).Countable := by
    apply hBig
    rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ hn hh
    exact hAnt p hp q hq (fun he => hn (congrArg f he))
      (liftLabelCondition_compatible_reflects_r82 label V hLabel p q hh)
  exact Set.countable_of_injective_of_countable_image hI hImage

end BooleanNames
end JSP000933
