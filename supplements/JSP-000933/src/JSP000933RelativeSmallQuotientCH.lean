import JSP000933RelativeShortRealTables

namespace JSP000933
namespace RelativeOCA

open MarkedForcing BooleanCompletion OpenGraphForcing CantorCodes Cardinal

variable {B N : Type} [CompleteBooleanAlgebra B]

noncomputable def cutCodeEncodable (c : OmegaOneIndex) : Encodable (CutCodeSlot c) := by
  letI : Countable (↥(Set.Iio c)) := OmegaOneIndex_initial_countable_r61 c
  exact Encodable.ofCountable (CutCodeSlot c)

noncomputable def decodeCutCode (c : OmegaOneIndex) (x : ℕ→B) : CutCodeSlot c→B := by
  letI := cutCodeEncodable c
  exact restrictEncoded x

theorem decodeCutCode_cover_r469 (e : OmegaOneIndex→ℕ→B) (hE : EnumeratesBooleanReals e)
    (c : OmegaOneIndex) (u : CutCodeSlot c→B) :
    (⨆ i,tableAgreement u (decodeCutCode c (e i)))=⊤ := by
  letI := cutCodeEncodable c
  exact mixedCH_codeCover_r441 e hE u

theorem relativeSmallCH_doubleEnumeration_r469 (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (hB : BoundsCountableOmegaOneNames B)
    (E : MixedEnumeration OmegaOneIndex N B)
    (e : OmegaOneIndex→ℕ→B) (hE : EnumeratesBooleanReals e) (x : ℕ→TotalBA Q) :
    (⨆ c : OmegaOneIndex,⨆ i : OmegaOneIndex,
      realEqValue x (initialTableReal Q E c (decodeCutCode c (e i))))=⊤ := by
  let W := actualGreedyCut Q E x
  have hW : (⨆ c,baseEmbed Q (W c))=⊤ := by
    rw [← baseEmbed_joins_r427,actualGreedyCuts_cover_r468 Q hQ hB E x,baseEmbed_top_r427]
  apply top_unique
  rw [← hW]
  apply iSup_le
  intro c
  let u (p : CutCodeSlot c) := greedyRowActive Q E (x p.1) p.2.val
  let V (i : OmegaOneIndex) := tableAgreement u (decodeCutCode c (e i))
  have hV : (⨆ i,V i)=⊤ := decodeCutCode_cover_r469 e hE c u
  have hFull : (⨆ i,baseEmbed Q (W c⊓V i))=baseEmbed Q (W c) := by
    rw [← baseEmbed_joins_r427,← inf_iSup_eq,hV,inf_top_eq]
  apply le_iSup_of_le c
  rw [← hFull]
  apply iSup_le
  intro i
  exact le_iSup_of_le i (genuineCut_encodedReal_agrees_r468 Q E x c (W c⊓V i)
    (decodeCutCode c (e i)) inf_le_left inf_le_right)

theorem omegaOne_pairEquiv_exists_r469 :
    Nonempty (OmegaOneIndex≃OmegaOneIndex×OmegaOneIndex) := by
  apply Cardinal.eq.mp
  rw [Cardinal.mk_prod]
  simp only [Cardinal.lift_id]
  symm
  apply Cardinal.mul_eq_self
  rw [mk_OmegaOneIndex_r61]
  exact Cardinal.isRegular_aleph_one.1

theorem relativeSmallCH_enumeratesBooleanReals_r469 (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (hB : BoundsCountableOmegaOneNames B)
    (E : MixedEnumeration OmegaOneIndex N B)
    (e : OmegaOneIndex→ℕ→B) (hE : EnumeratesBooleanReals e) :
    ∃ f : OmegaOneIndex→ℕ→TotalBA Q,EnumeratesBooleanReals f := by
  obtain ⟨z⟩ := omegaOne_pairEquiv_exists_r469
  let f (p : OmegaOneIndex×OmegaOneIndex) := initialTableReal Q E p.1 (decodeCutCode p.1 (e p.2))
  refine ⟨fun i => f (z i),fun x => ?_⟩
  apply top_unique
  rw [← relativeSmallCH_doubleEnumeration_r469 Q hQ hB E e hE x]
  apply iSup_le
  intro c
  apply iSup_le
  intro i
  have hz : z (z.symm (c,i))=(c,i) := z.apply_symm_apply _
  have he := congrArg (fun p => realEqValue x (f p)) hz
  exact he.ge.trans (le_iSup (fun j => realEqValue x (f (z j))) (z.symm (c,i)))

end RelativeOCA
end JSP000933
