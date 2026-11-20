import JSP000933FixedGlobalNameSchedule

open scoped Cardinal

namespace JSP000933
namespace CantorCodes

open BooleanCompletion BooleanTwoStep FiniteSupport OpenGraphForcing

structure OCAParameters where
  CH : (𝔠 : Cardinal.{0}) = ℵ₁
  names : OmegaTwoIndex × OmegaOneIndex ↪ OmegaTwoIndex
  encoder : DiamondEncoder OCALabel
  guess : OmegaTwoIndex → Set OmegaTwoIndex

variable (P : OCAParameters) (a : OmegaTwoIndex) (old : PrefixValidator a OCALabel)
variable (persist : HistoryPersistent old) (ccc : BooleanCCC (RO (GoodPrefix old)))

structure StageMark (a : OmegaTwoIndex) (old : PrefixValidator a OCALabel) where
  color : OmegaTwoIndex
  cond : GoodPrefix old

noncomputable def historyGraphX : ↥(Set.Iio a) → ℕ → RO (GoodPrefix old) :=
  fun i => historyRealDecode P.names a old persist ccc P.CH i.1

noncomputable def historyGraphD : ↥(Set.Iio a) → RO (GoodPrefix old) :=
  fun i => historyDomain P.encoder (P.guess a) i.1

noncomputable def historyGraphK (j : OmegaTwoIndex) : Word × Word → RO (GoodPrefix old) :=
  unpackColor (historyRealDecode P.names a old persist ccc P.CH j)

noncomputable def historySaturated : (ℕ → RO (GoodPrefix old)) → RO (GoodPrefix old) :=
  saturatedDomain (historyGraphX P a old persist ccc) (historyGraphD P a old)

def StageMark.eligible (m : StageMark a old) : Prop :=
  let D := historySaturated P a old persist ccc
  let K := historyGraphK P a old persist ccc m.color
  let p := imageCondition m.cond
  m.color < a ∧ P.encoder.colorTag m.color < a ∧ P.encoder.colorTag m.color ∈ P.guess a ∧
  P.encoder.conditionTag (goodTraceCode P.encoder m.cond) < a ∧
    P.encoder.conditionTag (goodTraceCode P.encoder m.cond) ∈ P.guess a ∧
  (∀ b : CoverCode (RO (GoodPrefix old)),
    p ≤ (goodCoverValue (historyGraphX P a old persist ccc) (historyGraphD P a old) K b)ᶜ) ∧
  (∀ x, p ⊓ D x ≤ (colorValue K x x)ᶜ) ∧
  (∀ x y, (p ⊓ (D x ⊓ D y)) ⊓ colorValue K x y ≤ colorValue K y x)

structure StageChoice where
  mark : StageMark a old
  eligible : StageMark.eligible P a old persist ccc mark
  points : OmegaOneIndex → ℕ → RO (GoodPrefix old)
  allPresent : ∀ i, imageCondition mark.cond ≤ historySaturated P a old persist ccc (points i)
  separated : ∀ i j, i ≠ j → Disjoint (imageCondition mark.cond) (realEqValue (points i) (points j))
  countableAntichains : HasCountableAntichains (Condition
    (cliqueLabelStage (imageCondition mark.cond)
      (fun i => historySaturated P a old persist ccc (points i))
      (fun i j => colorValue (historyGraphK P a old persist ccc mark.color) (points i) (points j))))

noncomputable def StageChoice.admission (s : StageChoice P a old persist ccc) (q : OCALabel) :
    RO (GoodPrefix old) :=
  cliqueAdmitted (imageCondition s.mark.cond)
    (fun i => historySaturated P a old persist ccc (s.points i))
    (fun i j => colorValue (historyGraphK P a old persist ccc s.mark.color) (s.points i) (s.points j))
    (OrderDual.ofDual q)

theorem exists_stageChoice_r163 (m : StageMark a old)
    (ok : StageMark.eligible P a old persist ccc m) :
    Nonempty (StageChoice P a old persist ccc) := by
  have hCard : Cardinal.mk (GoodPrefix old) ≤ Cardinal.mk RealCode := by
    rw [mk_realCode_r61,P.CH]
    exact mk_goodCliquePrefix_le_r160 a old
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hCard
  obtain ⟨encode,hEncode⟩ := exists_completion_binaryCode_r98 ccc e e.injective
  let x := historyGraphX P a old persist ccc
  let d := historyGraphD P a old
  let K := historyGraphK P a old persist ccc m.color
  let p := imageCondition m.cond
  let D := saturatedDomain x d
  have hNo : ∀ v : CoverCode (RO (GoodPrefix old)), p ≤ (goodCoverValue id D K v)ᶜ :=
    noCover_saturation_r142 x d K p ok.2.2.2.2.2.1
  obtain ⟨Y,hY,hSep,hCCC⟩ := exists_CH_activatedCliqueFamily_r157 ccc encode hEncode P.CH
    D (saturatedDomain_ext_r142 x d) K p hNo ok.2.2.2.2.2.2.1 ok.2.2.2.2.2.2.2
  exact ⟨⟨m,ok,Y,hY,hSep,hCCC⟩⟩

end CantorCodes
end JSP000933
