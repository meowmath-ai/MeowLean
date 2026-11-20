import JSP000933EarlierCoverListCapture

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport MarkedForcing RelativeOCA OpenGraphForcing CantorCodes PreparedModel

theorem mask_eq_of_le {B : Type} [CompleteBooleanAlgebra B] {s m x y : B}
    (hs : s≤ m) (h : m⊓x=m⊓y) : s⊓x=s⊓y := by
  have hh := congrArg (fun z => s⊓z) h
  simpa only [←inf_assoc,inf_eq_left.mpr hs] using hh

def ProbeBook.completePoint (book : ProbeBook) (d i : GroundContinuumSuccIndex) : Prop :=
  (∀ n,book.pointBit i n<d) ∧ book.pointMember i<d

structure DecodedBookMatches (book : ProbeBook)
    (f : GroundContinuumSuccIndex→WholeTail PreparedStage CliqueLabel)
    (d : GroundContinuumSuccIndex)
    (D : (ℕ→RO (BasedCondition (scheduledTail (preparedDecoder book f)))) →
      RO (BasedCondition (scheduledTail (preparedDecoder book f))))
    (K : Word×Word→RO (BasedCondition (scheduledTail (preparedDecoder book f))))
    (p : RO (BasedCondition (scheduledTail (preparedDecoder book f))))
    (X : GroundContinuumSuccIndex→ℕ→RO (BasedCondition (scheduledTail (preparedDecoder book f)))) where
  baseMark : PreparedBA
  maskedBad_positive : (basedMaskRealization (scheduledTail (preparedDecoder book f))).embed baseMark⊓p≠⊥
  bad_below : book.badMark<d
  graph_below : ∀ w,book.graphBit w<d
  rawMatch : ∀ j<d,∀ i,present (f j).trace i → i<(d : PreparedStage)
  pointRow : ∀ i<d,∀ n,book.pointBit i n<d →
    (basedMaskRealization (scheduledTail (preparedDecoder book f))).embed baseMark⊓
      X i n =
    (basedMaskRealization (scheduledTail (preparedDecoder book f))).embed baseMark⊓
      (wholeTailPresentation (scheduledTail (preparedDecoder book f))).denseMap.pullIso
        (guessedPrefixProbe (wholeTailPresentation (scheduledTail (preparedDecoder book f))).quotient
          f d (book.pointBit i n))
  memberRow : ∀ i<d,book.pointMember i<d →
    (basedMaskRealization (scheduledTail (preparedDecoder book f))).embed baseMark⊓
      D (X i) =
    (basedMaskRealization (scheduledTail (preparedDecoder book f))).embed baseMark⊓
      (wholeTailPresentation (scheduledTail (preparedDecoder book f))).denseMap.pullIso
        (guessedPrefixProbe (wholeTailPresentation (scheduledTail (preparedDecoder book f))).quotient
          f d (book.pointMember i))
  graphRow : ∀ w,
    (basedMaskRealization (scheduledTail (preparedDecoder book f))).embed baseMark⊓K w =
    (basedMaskRealization (scheduledTail (preparedDecoder book f))).embed baseMark⊓
      (wholeTailPresentation (scheduledTail (preparedDecoder book f))).denseMap.pullIso
        (guessedPrefixProbe (wholeTailPresentation (scheduledTail (preparedDecoder book f))).quotient
          f d (book.graphBit w))
  badRow :
    (basedMaskRealization (scheduledTail (preparedDecoder book f))).embed baseMark⊓p =
    (basedMaskRealization (scheduledTail (preparedDecoder book f))).embed baseMark⊓
      (wholeTailPresentation (scheduledTail (preparedDecoder book f))).denseMap.pullIso
        (guessedPrefixProbe (wholeTailPresentation (scheduledTail (preparedDecoder book f))).quotient
          f d book.badMark)

noncomputable def actualDecodedGraph (book : ProbeBook)
    (f : GroundContinuumSuccIndex→WholeTail PreparedStage CliqueLabel)
    (d : GroundContinuumSuccIndex) :
    ScheduledGraph (PreparedPrefixBA (scheduledTail (preparedDecoder book f)) d) :=
  preparedDecoder book f (d : PreparedStage)
    (earlierValidated (basedPolicy (scheduledTail (preparedDecoder book f))) (d : PreparedStage))

theorem preparedDecoder_activates_on_witness_book
    (book : ProbeBook) (f : GroundContinuumSuccIndex→WholeTail PreparedStage CliqueLabel)
    (d : GroundContinuumSuccIndex) (hd : OmegaOneCofinalIndex d)
    (W : GroundContinuumSuccIndex→OmegaOneIndex→Bool→GroundContinuumSuccIndex)
    (hW : ∀ a<d,∀ i b,W a i b<d ∧ book.completePoint d (W a i b))
    (D : (ℕ→RO (BasedCondition (scheduledTail (preparedDecoder book f)))) →
      RO (BasedCondition (scheduledTail (preparedDecoder book f))))
    (hD : RealTestExt D)
    (K : Word×Word→RO (BasedCondition (scheduledTail (preparedDecoder book f))))
    (p : RO (BasedCondition (scheduledTail (preparedDecoder book f))))
    (X : GroundContinuumSuccIndex→ℕ→RO (BasedCondition (scheduledTail (preparedDecoder book f))))
    (M : DecodedBookMatches book f d D K p X)
    (hIrr : ∀ x,p⊓D x≤(colorValue K x x)ᶜ)
    (hSym : ∀ x y,(p⊓(D x⊓D y))⊓colorValue K x y≤colorValue K y x)
    (hFail : ∀ a i,p≤twoPointCoverFailure D K (coverListInWhole (preparedDecoder book f) a i)
      (X (W a i false)) (X (W a i true))) :
    ∃ q : PreparedPrefixBA (scheduledTail (preparedDecoder book f)) d,
      q≠⊥ ∧ (typedToWhole (scheduledTail (preparedDecoder book f)) (d : PreparedStage)).toFun q≤p ∧
      q≤(actualDecodedGraph book f d).mark ∧
      (∀ x,(typedToWhole (scheduledTail (preparedDecoder book f)) (d : PreparedStage)).toFun q⊓
        (typedToWhole (scheduledTail (preparedDecoder book f)) (d : PreparedStage)).toFun
          ((actualDecodedGraph book f d).D x) ≤
          D ((typedToWhole (scheduledTail (preparedDecoder book f)) (d : PreparedStage)).toFun ∘ x)) ∧
      ∀ w,(typedToWhole (scheduledTail (preparedDecoder book f)) (d : PreparedStage)).toFun q⊓
        (typedToWhole (scheduledTail (preparedDecoder book f)) (d : PreparedStage)).toFun
          ((actualDecodedGraph book f d).K w) =
          (typedToWhole (scheduledTail (preparedDecoder book f)) (d : PreparedStage)).toFun q⊓K w := by
  classical
  let decode := preparedDecoder book f
  let tail := scheduledTail decode
  let a : PreparedStage := (d : PreparedStage)
  let ha : (⊥ : PreparedStage)<a := WithBot.bot_lt_coe d
  let old := earlierValidated (basedPolicy tail) a
  let E := typedToWhole tail a
  let I := ↥(Set.Iio d)
  let x (i : I) := decodedBits book old f d i
  let t (i : I) := decodedMember book old f d i
  let k := decodedK book old f d
  let d0 := saturatedDomain x t
  let p0 := typedProbeRow old f d book.badMark
  let m := (basedMaskRealization tail).embed M.baseMark
  let q := typedPreparedBase old M.baseMark⊓p0
  have hRow (i : GroundContinuumSuccIndex) :
      E.toFun (typedProbeRow old f d i) =
        (wholeTailPresentation tail).denseMap.pullIso
          (guessedPrefixProbe (wholeTailPresentation tail).quotient f d i) :=
    typedToWhole_probeRow tail a ha f d i M.rawMatch
  have hq : E.toFun q=m⊓p := by
    rw [E.map_inf,typedToWhole_base tail a ha,(wholeTailPresentation tail).quotient_base_coherent]
    change m⊓E.toFun p0=m⊓p
    rw [hRow]
    exact M.badRow.symm
  have hq0 : q≠⊥ := by
    intro h
    apply M.maskedBad_positive
    change m⊓p=⊥
    rw [←hq,h,E.map_bot]
  have hqM : E.toFun q≤ m := hq.trans_le inf_le_left
  have hqp : E.toFun q≤p := hq.trans_le inf_le_right
  have hBit (i : I) (n : ℕ) (hi : book.pointBit i.val n<d) :
      m⊓E.toFun (x i n)=m⊓X i.val n := by
    rw [show x i n=typedProbeRow old f d (book.pointBit i.val n) from ite_eq_left hi,hRow]
    exact (M.pointRow i.val i.property n hi).symm
  have hMem (i : I) (hi : book.completePoint d i.val) : m⊓E.toFun (t i)=m⊓D (X i.val) := by
    rw [show t i=typedProbeRow old f d (book.pointMember i.val) from ite_eq_left hi,hRow]
    exact (M.memberRow i.val i.property hi.2).symm
  have hCode (w : Word×Word) : m⊓E.toFun (k w)=m⊓K w := by
    rw [show k w=typedProbeRow old f d (book.graphBit w) from ite_eq_left (M.graph_below w),hRow]
    exact (M.graphRow w).symm
  let X' (i : I) (n : ℕ) :=
    if book.completePoint d i.val then X i.val n else E.toFun (x i n)
  have hBits (i : I) (n : ℕ) : E.toFun q⊓E.toFun (x i n)=E.toFun q⊓X' i n := by
    by_cases hi : book.completePoint d i.val
    · simp only [X',ite_eq_left hi]
      exact mask_eq_of_le hqM (hBit i n (hi.1 n))
    · simp [X',hi]
  have hDom (i : I) : E.toFun q⊓E.toFun (t i)≤D (X' i) := by
    by_cases hi : book.completePoint d i.val
    · have he := mask_eq_of_le hqM (hMem i hi)
      simp only [X',ite_eq_left hi]
      exact he.trans_le inf_le_right
    · rw [show t i=⊥ from ite_eq_right hi,E.map_bot,inf_bot_eq]
      exact bot_le
  have hDom' (y : ℕ→PreparedPrefixBA tail d) : E.toFun q⊓E.toFun (d0 y)≤D (E.toFun ∘ y) :=
    saturatedDomain_lifts_under E _ D hD x t X' hBits hDom y
  have hCode' (w : Word×Word) : E.toFun q⊓E.toFun (k w)=E.toFun q⊓K w :=
    mask_eq_of_le hqM (hCode w)
  obtain ⟨hI,hS⟩ := graph_valid_lifts_down E q D K d0 k hDom' hCode'
    (fun y => (inf_le_inf hqp le_rfl).trans (hIrr y))
    (fun y z => (inf_le_inf (inf_le_inf hqp le_rfl) le_rfl).trans (hSym y z))
  have hNo (c : CoverCode (PreparedPrefixBA tail d)) : q≤(goodCoverValue id d0 k c)ᶜ := by
    apply join_failure_of_local_rows E q x t k D K c
    intro r hr hr0
    obtain ⟨b,j,s,hbd,hs,hs0,hCover⟩ := capture_cover_from_list decode d hd c r hr0
    have hsQ := E.monotone (hs.trans hr)
    have hsM := hsQ.trans hqM
    let i₁ : I := ⟨W b j false,(hW b hbd j false).1⟩
    let i₂ : I := ⟨W b j true,(hW b hbd j true).1⟩
    have hi₁ : book.completePoint d i₁.val := (hW b hbd j false).2
    have hi₂ : book.completePoint d i₂.val := (hW b hbd j true).2
    refine ⟨s,hs,hs0,i₁,i₂,X i₁.val,X i₂.val,coverListInWhole decode b j,?_,hCover,?_,?_,?_,?_,?_⟩
    · exact fun w => mask_eq_of_le hsM (hCode w)
    · exact (le_realEqValue_iff_r126 _ _ _).mpr fun n => mask_eq_of_le hsM (hBit i₁ n (hi₁.1 n))
    · exact (le_realEqValue_iff_r126 _ _ _).mpr fun n => mask_eq_of_le hsM (hBit i₂ n (hi₂.1 n))
    · exact mask_eq_of_le hsM (hMem i₁ hi₁)
    · exact mask_eq_of_le hsM (hMem i₂ hi₂)
    · exact (hsQ.trans hqp).trans (hFail b j)
  refine ⟨q,hq0,hqp,?_,hDom',hCode'⟩
  change q≤activationValue (if book.badMark<d then p0 else ⊥) d0 k
  rw [ite_eq_left M.bad_below]
  apply le_inf
  · apply le_inf inf_le_right
    apply le_inf
    · apply le_iInf
      intro y
      exact (le_materialImp_iff_r126 _ _ _).mpr (hI y)
    · apply le_iInf
      intro y
      apply le_iInf
      intro z
      apply (le_materialImp_iff_r126 _ _ _).mpr
      change q ⊓ ((d0 y ⊓ d0 z) ⊓ colorValue k y z) ≤ colorValue k z y
      rw [←inf_assoc]
      exact hS y z
  · rw [closedCoverExistsValue,compl_iSup]
    exact le_iInf hNo

end ForcingTransport
end JSP000933
