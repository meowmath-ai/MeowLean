import JSP000933ActualPreparedNativeOCA
import JSP000933BooleanFirstOrderOCA

open Fol
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open ForcingTransport BooleanNames

theorem actualPreparedOca_namedCantorOCA_top_r498 :
    namedCantorOCAValue ActualPreparedOcaBA=⊤ := by
  apply top_unique
  exact actualPreparedOca_nativeOCA_top.ge.trans nativeOCA_le_namedCantorOCA_r180

theorem actualPreparedOca_forces_cantorOCA_r498 :
    (⊤ : ActualPreparedOcaBA) ⊩[V ActualPreparedOcaBA] cantorOCA_f := by
  change (⊤ : ActualPreparedOcaBA)≤boolean_realize_sentence (S := V ActualPreparedOcaBA) cantorOCA_f
  simpa only [bTruth_cantorOCA_eq_r182,actualPreparedOca_namedCantorOCA_top_r498] using
    (le_rfl : (⊤ : ActualPreparedOcaBA)≤⊤)

end SetLanguage
end JSP000933
