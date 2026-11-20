import JSP000933DiamondStageGuards

open scoped Cardinal

namespace JSP000933
namespace CantorCodes

open FiniteSupport BooleanCompletion OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

def unpackColor (v : ℕ → B) : Word × Word → B := fun w => v (Encodable.encode w)

def packColor (c : Word × Word → B) : ℕ → B := fun k =>
  match (Encodable.decode k : Option (Word × Word)) with
  | none => ⊥
  | some w => c w

theorem unpack_packColor_r120 (K : Word × Word → B) : unpackColor (packColor K) = K := by
  funext w
  simp only [unpackColor,packColor,Encodable.encodek]

variable {T : Type} {R : Rules (fun (_ : OmegaTwoIndex) => T)}

noncomputable def decodedX (S : ReflectingNameSchedule R) (a : OmegaTwoIndex) :
    ↥(Set.Iio a) → ℕ → RO (Before R a) :=
  fun i => canonicalStageDecode S.code S.stageEnumerate a i.1

noncomputable def decodedD (E : DiamondEncoder T) (a : OmegaTwoIndex)
    (G : Set OmegaTwoIndex) : ↥(Set.Iio a) → RO (Before R a) :=
  fun i => guessDomain E a G i.1

noncomputable def decodedK (S : ReflectingNameSchedule R) (a j : OmegaTwoIndex) :
    Word × Word → RO (Before R a) :=
  unpackColor (canonicalStageDecode S.code S.stageEnumerate a j)

theorem exists_guessedNoCoverStage_r120
    (hCCC : HasCountableAntichains (Condition R))
    (hSmall : ∀ a : OmegaTwoIndex, Cardinal.mk (Before R a) ≤ ℵ₁)
    (S : ReflectingNameSchedule R) (E : DiamondEncoder T)
    (G : OmegaTwoIndex → Set OmegaTwoIndex) (hDia : DiamondAtOmegaOne G)
    (D : OmegaTwoIndex → RO (Condition R)) (K : Word × Word → RO (Condition R))
    (p : Condition R)
    (hNo : ∀ c : CoverCode (RO (Condition R)),
      imageCondition p ≤ (goodCoverValue S.enumerate D K c)ᶜ) :
    ∃ a : OmegaTwoIndex, ∃ j : OmegaTwoIndex, ∃ q : Before R a,
      (omegaTwoOrdinal a).cof = ℵ₁ ∧ j < a ∧ q.1 = p ∧
      E.colorTag j < a ∧ E.colorTag j ∈ G a ∧
      E.conditionTag (E.conditionCode q.1) < a ∧ E.conditionTag (E.conditionCode q.1) ∈ G a ∧
      (∀ i, E.colorTag i < a → E.colorTag i ∈ G a → i = j) ∧
      (∀ r : Before R a, E.conditionTag (E.conditionCode r.1) < a →
        E.conditionTag (E.conditionCode r.1) ∈ G a → r = q) ∧
      ∀ c : CoverCode (RO (Before R a)),
        imageCondition q ≤ (goodCoverValue (decodedX S a) (decodedD E a (G a)) (decodedK S a j) c)ᶜ := by
  classical
  obtain ⟨j,hj⟩ := S.onto (packColor K)
  obtain ⟨C,hC,hReflect⟩ := exists_club_reflects_noCover_r116 hCCC S D K (imageCondition p)
    (imageCondition_ne_bot_r50 p) hNo
  obtain ⟨U,hU,hTags⟩ := exists_club_captures_domainTags_r119 E hSmall
  let required : Finset OmegaTwoIndex :=
    insert j (insert (E.colorTag j) (insert (E.conditionTag (E.conditionCode p)) (support p)))
  obtain ⟨floor,hFloor⟩ := OmegaTwoIndex_finite_bounded_r89 required
  obtain ⟨V,hV,hRefine⟩ := exists_club_refines_two_and_floor_r119 hC hU floor
  obtain ⟨W,hW,hRefineW⟩ := exists_club_refines_two_and_floor_r119 hV S.isClub floor
  obtain ⟨a,ha,hCo,hTrace⟩ := hDia (diamondSignal E D j p) W hW
  have hcf : (ℵ₀ : Cardinal) < (omegaTwoOrdinal a).cof := by
    rw [hCo,← Cardinal.succ_aleph0]
    exact Order.lt_succ _
  have hne := exists_stage_below_of_cof_r116 a hcf
  obtain ⟨haV,haS,haFloor⟩ := hRefineW a ha hne
  obtain ⟨haC,haU,_⟩ := hRefine a haV hne
  have hjA : j < a := (hFloor j (by simp [required])).trans haFloor
  have hColor : E.colorTag j < a :=
    (hFloor (E.colorTag j) (by simp [required])).trans haFloor
  have hCond : E.conditionTag (E.conditionCode p) < a :=
    (hFloor (E.conditionTag (E.conditionCode p)) (by simp [required])).trans haFloor
  let q : Before R a := ⟨p,fun i hi =>
    (hFloor i (by simp [required,(mem_support_r75 p i).mpr hi])).trans haFloor⟩
  obtain ⟨r⟩ := hReflect a haC hcf
  refine ⟨a,j,q,hCo,hjA,rfl,hColor,?_,hCond,?_,?_,?_,?_⟩
  · exact (hTrace _ hColor).mpr ((colorTag_mem_signal_r118 E D j j p).mpr rfl)
  · exact (hTrace _ hCond).mpr ((conditionTag_mem_signal_r118 E D j (E.conditionCode p) p).mpr rfl)
  · intro i hi h
    exact (colorTag_mem_signal_r118 E D j i p).mp ((hTrace _ hi).mp h)
  · intro v hv h
    apply Subtype.ext
    exact E.conditionCode_injective_r117 ((conditionTag_mem_signal_r118 E D j (E.conditionCode v.1) p).mp
      ((hTrace _ hv).mp h))
  · intro c
    let F := (wholeReduction a (R := R)).completeValueMap
    have hx : decodedX S a = r.x := by
      funext i n
      apply F.injective
      exact (congrFun (S.localDecode_agrees a haS i.1 i.2) n).trans
        (congrFun (r.x_agrees i) n).symm
    have hd : decodedD E a (G a) = r.d := by
      funext i
      exact guessDomain_correct_r118 E a (G a) D j p i.1 (r.d i) (r.d_agrees i)
        (hTags a haU hcf i.1 i.2) hTrace
    have hk : decodedK S a j = r.k := by
      funext w
      apply F.injective
      have h :=
        congrFun (S.localDecode_agrees a haS j hjA) (Encodable.encode w)
      exact h.trans ((congrFun ((congrArg unpackColor hj).trans (unpack_packColor_r120 K)) w).trans
        (r.k_agrees w).symm)
    have hp : imageCondition q = r.cond :=
      F.injective ((wholeReduction_basic_r100 a q).trans r.cond_agrees.symm)
    rw [hx,hd,hk,hp]
    exact r.noCover c

end CantorCodes
end JSP000933
