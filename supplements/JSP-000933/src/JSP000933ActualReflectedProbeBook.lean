import JSP000933PreparedProbeBookClosure
import JSP000933PreparedProbeWitnessPlan

namespace JSP000933
namespace ForcingTransport

open PreparedModel RelativeOCA MarkedForcing BooleanCompletion OpenGraphForcing CantorCodes

variable {N : Type}

def preparedProbeEq (Q : ValuedPoset PreparedBA N) (m : PreparedBA) (u v : TotalBA Q) : Prop :=
  baseEmbed Q m⊓u=baseEmbed Q m⊓v

structure ReflectedPreparedBook (Q : ValuedPoset PreparedBA N) (f : ProbeIndex→N)
    (scope : N→Finset ProbeIndex) (start : ProbeIndex)
    (X : ProbeIndex→ℕ→TotalBA Q) (M : ProbeIndex→TotalBA Q)
    (K : Word×Word→TotalBA Q) (pBad p : TotalBA Q) where
  d : ProbeIndex
  baseMark : PreparedBA
  master : TotalCondition Q
  cofOmegaOne : OmegaOneCofinalIndex d
  aboveStart : start<d
  closedRows : ∀ i<d,preparedProbeClosureBound i<d
  baseNonzero : baseMark≠⊥
  masterBelow : imageCondition master≤p⊓baseEmbed Q baseMark
  scopeBelow : ∀ i<d,∀ k∈scope (f i),k<d
  bitMatches : ∀ i<d,∀ n,preparedProbeEq Q baseMark (X i n)
    (guessedPrefixProbe Q f d (preparedProbeBook.pointBit i n))
  memberMatches : ∀ i<d,preparedProbeEq Q baseMark (M i)
    (guessedPrefixProbe Q f d (preparedProbeBook.pointMember i))
  graphMatches : ∀ w,preparedProbeEq Q baseMark (K w)
    (guessedPrefixProbe Q f d (preparedProbeBook.graphBit w))
  badMatches : preparedProbeEq Q baseMark pBad
    (guessedPrefixProbe Q f d preparedProbeBook.badMark)

theorem exists_actual_reflectedBook_r497 (Q : ValuedPoset PreparedBA N)
    (hQ : ForcesRelativeCCC Q) (f : ProbeIndex→N) (hf : Function.Surjective f)
    (scope : N→Finset ProbeIndex) (start : ProbeIndex)
    (X : ProbeIndex→ℕ→TotalBA Q) (M : ProbeIndex→TotalBA Q)
    (K : Word×Word→TotalBA Q) (pBad p : TotalBA Q) (hp : p≠⊥) :
    Nonempty (ReflectedPreparedBook Q f scope start X M K pBad p) := by
  obtain ⟨d,m,r,hd,ha,hE,hm,hr,hS,hEq⟩ :=
    exists_actual_reflectedProbe_absorbing_r493 Q hQ f hf scope preparedProbeClosureBound start
      (preparedProbeValues X M K pBad) p hp
  obtain ⟨hBit,hMem,hK,hBad⟩ := preparedProbeValues_tagEquations_r494 X M K pBad
  obtain ⟨hBadLt,hKLt,_⟩ := earlyPreparedProbes_below_r495 hE start ha
  have hTransfer (i : ProbeIndex) (hi : i<d) (u : TotalBA Q)
      (hu : preparedProbeValues X M K pBad i=u) :
      preparedProbeEq Q m u (guessedPrefixProbe Q f d i) := by
    rw [← hu]
    exact hEq i hi
  refine ⟨⟨d,m,r,hd,ha,hE,hm,hr,hS,?_,?_,?_,?_⟩⟩
  · intro i hi n
    obtain ⟨_,_,_,hLt,_⟩ := earlyPreparedProbes_below_r495 hE i hi
    exact hTransfer _ (hLt n) _ (hBit i n)
  · intro i hi
    obtain ⟨_,_,hLt,_⟩ := earlyPreparedProbes_below_r495 hE i hi
    exact hTransfer _ hLt _ (hMem i)
  · intro w
    exact hTransfer _ (hKLt w) _ (hK w)
  · exact hTransfer _ hBadLt _ hBad

theorem ReflectedPreparedBook.witnessMatches_r497
    {Q : ValuedPoset PreparedBA N} {f : ProbeIndex→N}
    {scope : N→Finset ProbeIndex} {start : ProbeIndex}
    {W : ProbeWitnessPlan (TotalBA Q)} {K : Word×Word→TotalBA Q} {pBad p : TotalBA Q}
    (R : ReflectedPreparedBook Q f scope start (probeWitnessBits W) (probeWitnessMember W) K pBad p)
    (a : ProbeIndex) (ha : a<R.d) (j : OmegaOneIndex) (s : Bool) :
    let i := preparedProbeWitnessIndex a j s
    i<R.d ∧
      (∀ n,preparedProbeEq Q R.baseMark ((W a j s).1 n)
        (guessedPrefixProbe Q f R.d (preparedProbeBook.pointBit i n))) ∧
      preparedProbeEq Q R.baseMark (W a j s).2
        (guessedPrefixProbe Q f R.d (preparedProbeBook.pointMember i)) := by
  dsimp only
  obtain ⟨_,_,_,_,hW⟩ := earlyPreparedProbes_below_r495 R.closedRows a ha
  have hi := (hW j s).1
  refine ⟨hi,fun n => ?_,?_⟩
  · simpa only [probeWitnessBits_at_r496] using R.bitMatches _ hi n
  · simpa only [probeWitnessMember_at_r496] using R.memberMatches _ hi

end ForcingTransport
end JSP000933
