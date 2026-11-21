import JSP000930NativeCertifiedSuccessor
import JSP000933NativeSuccessorPreservation

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.ForcingTransport

variable {B C : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

noncomputable def completeMapOfOrderIso930 (e : B ≃o C) : CompleteValueMap B C :=
  completeValueMapOfIso e

noncomputable def completeMapOfDensePull930 {P Q : Type} [Preorder P] [Preorder Q]
    (F : DenseForcingMap P Q) : CompleteValueMap (RO Q) (RO P) :=
  completeMapOfOrderIso930 F.pullIso

theorem completeMapOfDensePull930_apply {P Q : Type} [Preorder P] [Preorder Q]
    (F : DenseForcingMap P Q) (b : RO Q) :
    (completeMapOfDensePull930 F).toFun b = F.pullIso b := rfl

end JSP000930.Negative
