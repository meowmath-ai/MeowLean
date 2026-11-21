import JSP000930ActualEarlierHistoryMaps
import JSP000933NativeGroundTailCarriers

namespace JSP000930.Negative

open Cardinal JSP000930.Positive.Cohen JSP000933.PreparedModel
open JSP000933.FiniteSupport JSP000933.ForcingTransport
open scoped Cardinal

variable {A T : Type} [Top T] {Y : A → Prop}

open scoped Classical in
noncomputable def rawTailGraph (p : RawTail T Y) : Finset (A × T) :=
  p.scope.attach.image (fun i => (i.val,(p.trace i.val).getD ⊤))

theorem mem_rawTailGraph (p : RawTail T Y) (i : A) (t : T) :
    (i,t) ∈ rawTailGraph p ↔ p.trace i = some t := by
  classical
  unfold rawTailGraph
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
    have hj' := (RawTail.mem_scope p j.val).mp j.2
    obtain ⟨u,hu⟩ := hj'
    have hi : j.val = i := congrArg Prod.fst he
    have ht : (p.trace j.val).getD ⊤ = t := congrArg Prod.snd he
    rw [hu] at ht
    change u=t at ht
    rw [← hi,hu,ht]
  · intro h
    have hs : i ∈ p.scope := (RawTail.mem_scope p i).mpr ⟨t,h⟩
    apply Finset.mem_image.mpr
    exact ⟨⟨i,hs⟩,Finset.mem_attach _ _,by simp only [h,Option.getD_some]⟩

theorem rawTailGraph_injective : Function.Injective (rawTailGraph (Y := Y) (T := T)) := by
  intro p q hp
  apply RawTail.extTrace
  funext i
  cases hi : p.trace i with
  | none =>
    cases hj : q.trace i with
    | none => rfl
    | some u =>
      have hu := (mem_rawTailGraph q i u).mpr hj
      rw [← hp] at hu
      have h := (mem_rawTailGraph p i u).mp hu
      rw [hi] at h
      cases h
  | some u =>
    have hu := (mem_rawTailGraph p i u).mpr hi
    rw [hp] at hu
    exact ((mem_rawTailGraph q i u).mp hu).symm

theorem rawTail_card_le930 {κ : Cardinal} (hκ : ℵ₀≤κ) (hA : #A≤κ) (hT : #T≤κ) :
    #(RawTail T Y)≤κ := by
  apply (Cardinal.mk_le_of_injective (rawTailGraph_injective (Y := Y) (T := T))).trans
  apply finite_family_card_le _ hκ
  simp only [Cardinal.mk_prod,Cardinal.lift_id]
  exact Cardinal.mul_le_of_le hκ hA hT

theorem wetzelWholeTail_card : #(WholeTail WetzelStageIndex WetzelCertifiedLabel)≤GroundContinuumSucc :=
  rawTail_card_le930 (Cardinal.aleph0_le_continuum.trans (Order.le_succ _))
    wetzelStageIndex_card wetzelCertifiedLabels_card

end JSP000930.Negative
