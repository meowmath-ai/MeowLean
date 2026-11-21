import JSP000930WetzelSentence
import JSP000930AnalyticSentence

open Fol

namespace JSP000930
namespace SetLanguage

def actualAnalyticSyntax : AnalyticPredicates where
  complex := @AnalyticSyntax.complex_f
  entire := @AnalyticSyntax.isEntireCode_f
  evaluates := @AnalyticSyntax.evalAt_f

def haymanBound_f : sentence L_ZFC := wetzelBound_f actualAnalyticSyntax

def haymanRefutation_f : sentence L_ZFC := bd_not haymanBound_f

def haymanAtAlephTwo_f : sentence L_ZFC := bd_and continuumAlephTwo_f haymanBound_f

def refutesHaymanAtAlephTwo_f : sentence L_ZFC := bd_and continuumAlephTwo_f haymanRefutation_f

end SetLanguage
end JSP000930
