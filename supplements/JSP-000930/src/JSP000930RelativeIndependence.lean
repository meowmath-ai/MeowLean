import JSP000930ActualWetzelAllStagesCCC
import JSP000930NegativeActualNamedPaletteSchedule
import JSP000930NegativeIterationLiteralConsistencyReceiver

open Fol bSet Cardinal Flypitch Lattice
open scoped Flypitch bSet

namespace JSP000930.Consistency

open JSP000930.SetLanguage JSP000930.Negative
open JSP000933.PreparedModel JSP000933.MarkedForcing JSP000933.BooleanCompletion
open JSP000933.ForcingTransport JSP000933.SetLanguage

abbrev ActualWetzelNegativeBA := TotalBA (nativeWetzelWholeQ actualWetzelRest)

noncomputable def actualWetzelFinalSchedule :
    NamedPaletteSchedule ActualWetzelNegativeBA :=
  actualNamedPaletteSchedule930 actualWetzelAllPriorBounds actualWetzelFinalCCC

theorem actualWetzel_forces_negative_atAlephTwo :
    (⊤ : ActualWetzelNegativeBA) ⊩[V ActualWetzelNegativeBA] refutesHaymanAtAlephTwo_f :=
  final_relativeCCC_forces_refutesHaymanAtAlephTwo
    (nativeWetzelWholeQ actualWetzelRest) actualWetzelFinalCCC wetzelWholeTail_card
    (actualCommonCohen_to_finalWetzel actualWetzelRest) actualWetzelFinalSchedule

theorem hayman_1119_literal_independence_and_same_continuum :
    (SentTheory.is_consistent (insert haymanBound_f ZFC) ∧
     SentTheory.is_consistent (insert (bd_not haymanBound_f) ZFC)) ∧
    (SentTheory.is_consistent (insert haymanBound_f (insert continuumAlephTwo_f ZFC)) ∧
     SentTheory.is_consistent (insert (bd_not haymanBound_f) (insert continuumAlephTwo_f ZFC))) :=
  literal_hayman_pairs_of_actual_negative_iteration
    (nativeWetzelWholeQ actualWetzelRest) actualWetzelFinalCCC wetzelWholeTail_card
    (actualCommonCohen_to_finalWetzel actualWetzelRest) actualWetzelFinalSchedule

theorem hayman_1119_relative_independence (_hZ : SentTheory.is_consistent ZFC) :
    SentTheory.is_consistent (insert haymanBound_f (insert continuumAlephTwo_f ZFC)) ∧
     SentTheory.is_consistent (insert (bd_not haymanBound_f) (insert continuumAlephTwo_f ZFC)) :=
  hayman_1119_literal_independence_and_same_continuum.2

end JSP000930.Consistency
