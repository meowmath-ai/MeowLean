import JSP000933ReflectCoverTests
import Mathlib.Logic.Equiv.List

namespace JSP000933
namespace CantorCodes

open BooleanCompletion

variable {B C : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

def unpackCover (v : ℕ → B) : CoverCode B := fun n w => v (Encodable.encode (n,w))

def packCover (c : CoverCode B) : ℕ → B := fun k =>
  match (Encodable.decode k : Option (ℕ × Word)) with
  | none => ⊥
  | some q => c q.1 q.2

theorem unpack_packCover_r115 (c : CoverCode B) : unpackCover (packCover c) = c := by
  funext n w
  simp only [unpackCover,packCover,Encodable.encodek]

theorem map_unpackCover_r115 (F : CompleteValueMap B C) (v : ℕ → B) (n : ℕ) (w : Word) :
    F.toFun (unpackCover v n w) = unpackCover (fun k => F.toFun (v k)) n w :=
  rfl

end CantorCodes
end JSP000933
