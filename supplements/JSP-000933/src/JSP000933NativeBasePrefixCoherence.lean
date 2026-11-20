import JSP000933NativeMarkedStaticBase
import JSP000933WholeReduction

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport

theorem image_le_iff_member {P : Type*} [Preorder P] (p : P) (x : RO P) :
    imageCondition p ≤ x ↔ p ∈ (x : LowerSet P) := by
  constructor
  · intro h
    have hh := Heyting.Regular.coe_le_coe.mpr h
    exact hh (imageCondition_mem_r50 p)
  · intro hp
    exact (Heyting.Regular.gi.gc _ _).mpr (LowerSet.Iic_le.mpr hp)

theorem le_of_image_tests {P : Type*} [Preorder P] {x y : RO P}
    (h : ∀ p, imageCondition p ≤ x → imageCondition p ≤ y) : x ≤ y := by
  apply Heyting.Regular.coe_le_coe.mp
  intro p hp
  exact (image_le_iff_member p y).mp (h p ((image_le_iff_member p x).mpr hp))

theorem image_le_regular_pullback {P Q : Type*} [Preorder P] [Preorder Q]
    (R : RestrictionMap P Q) (p : P) (x : RO Q) :
    imageCondition p ≤ R.boolPullback x ↔ imageCondition (R.toFun p) ≤ x := by
  rw [image_le_iff_member,image_le_iff_member]
  rfl

variable {A B T : Type} [LinearOrder A] [OrderBot A] [WellFoundedLT A]
  [NontrivialCompleteBooleanAlgebra B] [Preorder T] [OrderTop T]

abbrev BasedBefore (tail : BasedTailPolicy A B T) (a : A) :=
  Before (iterationRules (basedPolicy tail)) a

theorem putBase_bounded (tail : BasedTailPolicy A B T) {a : A} (ha : (⊥ : A) < a)
    (p : BasedBefore tail a) (b : B) (hb : b ≠ ⊥) (hle : b ≤ baseMask tail p.val) :
    ∀ i, present (putBase tail p.val b hb hle).trace i → i < a := by
  intro i hi
  by_cases he : i = ⊥
  · exact he.symm ▸ ha
  · obtain ⟨s,hs⟩ := hi
    exact p.property i ⟨s,by simpa [putBase,attachTrace,he] using hs⟩

noncomputable def basedEmptyBefore (tail : BasedTailPolicy A B T) (a : A) :
    BasedBefore tail a :=
  ⟨basedEmpty tail,by
    rintro i ⟨s,hs⟩
    change none = some s at hs
    cases hs⟩

noncomputable def prefixMaskRealization (tail : BasedTailPolicy A B T)
    {a : A} (ha : (⊥ : A) < a) :
    MaskRealization B (BasedBefore tail a) where
  mask := fun p => baseMask tail p.val
  positive := fun p => baseMask_positive tail p.val
  monotone := fun _ _ h => baseMask_mono tail h
  realizes b hb := by
    let p := basedEmptyBefore tail a
    let u := putBase tail p.val b hb le_top
    exact ⟨⟨u,putBase_bounded tail ha p b hb le_top⟩,putBase_mask tail p.val b hb le_top⟩
  cut p b hb := by
    let u := putBase tail p.val (baseMask tail p.val ⊓ b) hb inf_le_left
    exact ⟨⟨u,putBase_bounded tail ha p _ hb inf_le_left⟩,
      putBase_le tail p.val _ hb inf_le_left,
      putBase_mask tail p.val _ hb inf_le_left⟩

noncomputable def basedPrefixEmbed (tail : BasedTailPolicy A B T)
    {a : A} (ha : (⊥ : A) < a) :
    CompleteValueMap B (RO (BasedBefore tail a)) := by
  letI : Nonempty (BasedBefore tail a) := ⟨basedEmptyBefore tail a⟩
  exact (prefixMaskRealization tail ha).completeValueMap

theorem baseMask_restrict (tail : BasedTailPolicy A B T) (p : BasedCondition tail)
    {a : A} (ha : (⊥ : A) < a) :
    baseMask tail (restrict p a).val = baseMask tail p := by
  change ((cut p.trace a ⊥).getD (⊤,⊤)).1 = ((p.trace ⊥).getD (⊤,⊤)).1
  rw [cut_apply_of_lt ha]

theorem basedWhole_base_commutes (tail : BasedTailPolicy A B T) {a : A}
    (ha : (⊥ : A) < a) (b : B) :
    (wholeReduction (R := iterationRules (basedPolicy tail)) a).boolPullback
      ((basedPrefixEmbed tail ha).toFun b) = (basedBaseEmbed tail).toFun b := by
  apply le_antisymm
  · apply le_of_image_tests
    intro p hp
    rw [image_le_regular_pullback] at hp
    change imageCondition (restrict p a) ≤ (prefixMaskRealization tail ha).embed b at hp
    change imageCondition p ≤ (basedMaskRealization tail).embed b
    apply ((basedMaskRealization tail).image_le_iff p b).mpr
    have hh := ((prefixMaskRealization tail ha).image_le_iff (restrict p a) b).mp hp
    change baseMask tail (restrict p a).val ≤ b at hh
    change baseMask tail p ≤ b
    rwa [baseMask_restrict tail p ha] at hh
  · apply le_of_image_tests
    intro p hp
    rw [image_le_regular_pullback]
    change imageCondition p ≤ (basedMaskRealization tail).embed b at hp
    change imageCondition (restrict p a) ≤ (prefixMaskRealization tail ha).embed b
    apply ((prefixMaskRealization tail ha).image_le_iff (restrict p a) b).mpr
    change baseMask tail (restrict p a).val ≤ b
    rw [baseMask_restrict tail p ha]
    exact ((basedMaskRealization tail).image_le_iff p b).mp hp

end ForcingTransport
end JSP000933
