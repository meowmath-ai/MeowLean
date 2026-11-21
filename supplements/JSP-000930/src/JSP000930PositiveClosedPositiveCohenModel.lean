import JSP000930PositiveLiteralAnalyticLawFromEvalCorrespondence
import JSP000930AnalyticLiteralEvaluation

open Fol bSet Flypitch Lattice
open scoped Flypitch

namespace JSP000930.Positive.Cohen

open JSP000930.SetLanguage

theorem wetzelCohen_forces_haymanAtAlephTwo :
    (⊤ : WetzelCohenBA) ⊩[V WetzelCohenBA] haymanAtAlephTwo_f :=
  wetzelCohen_forces_haymanAtAlephTwo_of_exact_eval
    (JSP000930.AnalyticSyntax.literalTaylorEvalCorrespondence (B := WetzelCohenBA))

theorem wetzelCohen_forces_haymanBound :
    (⊤ : WetzelCohenBA) ⊩[V WetzelCohenBA] haymanBound_f :=
  wetzelCohen_forces_haymanBound_of_reserveAnalytic
    (reserveAnalyticLaw_of_literalEval
      (JSP000930.AnalyticSyntax.literalTaylorEvalCorrespondence (B := WetzelCohenBA)))

end JSP000930.Positive.Cohen
