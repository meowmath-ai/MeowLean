import JSP000930SymbolicForcingDenseEquivalence

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanCompletion

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

def SymbolicAt (A : J → Prop) (t : SymbolicTrace J) : Prop :=
  ∀ x ∈ t.pins.map Prod.fst,A x

theorem pinAt_mem_symbolicSite (p : SymbolicTrace J) (i : PinNumber p) :
    (pinAt p i).1 ∈ p.pins.map Prod.fst :=
  List.mem_map.mpr ⟨pinAt p i,List.getElem_mem i.2,rfl⟩

theorem allowed_of_decode_pin {A : J → Prop} (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (t : SymbolicTrace J) (ht : SymbolicAt A t)
    {x : J} (hx : x ∈ (decodeSymbolicTrace site H t).pins) : A x := by
  classical
  exact ht x (List.mem_toFinset.mp hx)

theorem symbolVal_eq_on_log (t : SymbolicTrace J)
    (site site' : J → ComplexBits B) (H H' : J → ℕ → ComplexBits B)
    (hSite : ∀ x ∈ t.pins.map Prod.fst,site x = site' x)
    (hH : ∀ x ∈ t.pins.map Prod.fst,∀ n,H x n = H' x n) :
    symbolVal t site H = symbolVal t site' H' := by
  funext i
  rcases i with i|i
  · exact hSite _ (pinAt_mem_symbolicSite t i)
  · exact hH _ (pinAt_mem_symbolicSite t i) _

theorem decodeSymbolicTrace_eq_on_log (t : SymbolicTrace J)
    (site site' : J → ComplexBits B) (H H' : J → ℕ → ComplexBits B)
    (hSite : ∀ x ∈ t.pins.map Prod.fst,site x = site' x)
    (hH : ∀ x ∈ t.pins.map Prod.fst,∀ n,H x n = H' x n) :
    decodeSymbolicTrace site H t = decodeSymbolicTrace site' H' t := by
  unfold decodeSymbolicTrace
  rw [symbolVal_eq_on_log t site site' H H' hSite hH]

theorem decodeSymbolicTrace_completeMap_on_log (F : CompleteValueMap B C)
    (t : SymbolicTrace J) (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (site' : J → ComplexBits C) (H' : J → ℕ → ComplexBits C)
    (hSite : ∀ x ∈ t.pins.map Prod.fst,(site x).map F = site' x)
    (hH : ∀ x ∈ t.pins.map Prod.fst,∀ n,(H x n).map F = H' x n) :
    (decodeSymbolicTrace site H t).map F = decodeSymbolicTrace site' H' t := by
  rw [decodeSymbolicTrace_map]
  exact decodeSymbolicTrace_eq_on_log t _ site' _ H' hSite hH

theorem decodeSymbolicTrace_support_iff {A : J → Prop} (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (t : SymbolicTrace J) :
    (∀ i ∈ (decodeSymbolicTrace site H t).pins,A i) ↔ SymbolicAt A t := by
  classical
  change (∀ i ∈ (t.pins.map Prod.fst).toFinset,A i) ↔ _
  simp only [List.mem_toFinset,SymbolicAt]

end JSP000930.Negative
