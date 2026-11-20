import JSP000933ExactNativeTraceCoherence
import JSP000933LocalizedStageCliqueLifts
import JSP000933GreedyProbeCuts

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion FiniteSupport MarkedForcing RelativeOCA OpenGraphForcing CantorCodes PreparedModel

abbrev PreparedStage := WithBot GroundContinuumSuccIndex

abbrev PreparedLabels := BasedLabel PreparedBA CliqueLabel

structure ProbeBook where
  pointBit : GroundContinuumSuccIndex → ℕ → GroundContinuumSuccIndex
  pointMember : GroundContinuumSuccIndex → GroundContinuumSuccIndex
  graphBit : Word×Word → GroundContinuumSuccIndex
  badMark : GroundContinuumSuccIndex

noncomputable def typedBaseMask {a : PreparedStage} {old : PrefixValidator a PreparedLabels}
    (p : GoodPrefix old) : PreparedBA :=
  ((p.trace ⊥).getD (⊤,⊤)).1

noncomputable def typedPreparedBase {a : PreparedStage} (old : PrefixValidator a PreparedLabels)
    (b : PreparedBA) : RO (GoodPrefix old) :=
  ⨆ p : {p : GoodPrefix old // typedBaseMask p≤b}, imageCondition p.val

noncomputable def typedRawTailJoin {a : PreparedStage} (old : PrefixValidator a PreparedLabels)
    (n : WholeTail PreparedStage CliqueLabel) : RO (GoodPrefix old) :=
  ⨆ p : {p : GoodPrefix old // stripBaseTrace p.trace=n.trace}, imageCondition p.val

noncomputable def typedProbeRow {a : PreparedStage} (old : PrefixValidator a PreparedLabels)
    (f : GroundContinuumSuccIndex→WholeTail PreparedStage CliqueLabel)
    (d i : GroundContinuumSuccIndex) : RO (GoodPrefix old) :=
  ⨆ j : ↥(Set.Iio d), typedRawTailJoin old (f j.val) ⊓
    typedPreparedBase old (decodePreparedGuess d (kappaPairCode (i,j.val)))

noncomputable def decodedBits (book : ProbeBook) {a : PreparedStage}
    (old : PrefixValidator a PreparedLabels)
    (f : GroundContinuumSuccIndex→WholeTail PreparedStage CliqueLabel)
    (d : GroundContinuumSuccIndex) (i : ↥(Set.Iio d)) (n : ℕ) : RO (GoodPrefix old) :=
  if book.pointBit i.val n<d then typedProbeRow old f d (book.pointBit i.val n) else ⊥

open scoped Classical in
noncomputable def decodedMember (book : ProbeBook) {a : PreparedStage}
    (old : PrefixValidator a PreparedLabels)
    (f : GroundContinuumSuccIndex→WholeTail PreparedStage CliqueLabel)
    (d : GroundContinuumSuccIndex) (i : ↥(Set.Iio d)) : RO (GoodPrefix old) :=
  if (∀ n,book.pointBit i.val n<d) ∧ book.pointMember i.val<d
  then typedProbeRow old f d (book.pointMember i.val) else ⊥

noncomputable def decodedK (book : ProbeBook) {a : PreparedStage}
    (old : PrefixValidator a PreparedLabels)
    (f : GroundContinuumSuccIndex→WholeTail PreparedStage CliqueLabel)
    (d : GroundContinuumSuccIndex) (w : Word×Word) : RO (GoodPrefix old) :=
  if book.graphBit w<d then typedProbeRow old f d (book.graphBit w) else ⊥

noncomputable def activationValue {B : Type} [CompleteBooleanAlgebra B]
    (m : B) (D : (ℕ→B)→B) (K : Word×Word→B) : B :=
  m⊓(irreflexiveGraphValue D K⊓symmetricGraphValue D K)⊓(closedCoverExistsValue D K)ᶜ

open scoped Classical in
noncomputable def preparedDecoder (book : ProbeBook)
    (f : GroundContinuumSuccIndex→WholeTail PreparedStage CliqueLabel) :
    ActualScheduleDecoder PreparedStage PreparedBA :=
  fun a old => match a with
  | none => ⟨fun _ => ⊥,fun _ => ⊥,⊥⟩
  | some d =>
    let D := saturatedDomain (decodedBits book old f d) (decodedMember book old f d)
    let K := decodedK book old f d
    let p := if book.badMark<d then typedProbeRow old f d book.badMark else ⊥
    ⟨D,K,activationValue p D K⟩

theorem activationValue_noCover {B : Type} [CompleteBooleanAlgebra B]
    (m : B) (D : (ℕ→B)→B) (K : Word×Word→B) (c : CoverCode B) :
    activationValue m D K ≤ (goodCoverValue id D K c)ᶜ :=
  inf_le_right.trans (compl_le_compl (le_iSup (fun c => goodCoverValue id D K c) c))

theorem activationValue_irreflexive {B : Type} [CompleteBooleanAlgebra B]
    (m : B) (D : (ℕ→B)→B) (K : Word×Word→B) (x : ℕ→B) :
    activationValue m D K⊓D x≤(colorValue K x x)ᶜ := by
  apply (le_materialImp_iff_r126 _ _ _).mp
  exact inf_le_left.trans (inf_le_right.trans (inf_le_left.trans (iInf_le _ x)))

theorem activationValue_symmetric {B : Type} [CompleteBooleanAlgebra B]
    (m : B) (D : (ℕ→B)→B) (K : Word×Word→B) (x y : ℕ→B) :
    (activationValue m D K⊓(D x⊓D y))⊓colorValue K x y≤colorValue K y x := by
  rw [inf_assoc]
  apply (le_materialImp_iff_r126 _ _ _).mp
  exact inf_le_left.trans (inf_le_right.trans (inf_le_right.trans ((iInf_le _ x).trans (iInf_le _ y))))

end ForcingTransport
end JSP000933
