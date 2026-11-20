import JSP000933ReflectingNameSchedule
import JSP000933BooleanCoverFailure

namespace JSP000933
namespace FiniteSupport

open OpenGraphForcing BooleanCompletion

variable {B W : Type} [CompleteBooleanAlgebra B]

def footprintBelow (a : OmegaTwoIndex) (footprint : W → Finset OmegaTwoIndex) (w : W) : Prop :=
  ∀ i ∈ footprint w, i < a

theorem exists_witnessCaptureGuard_r113 (hCCC : BooleanCCC B) (footprint : W → Finset OmegaTwoIndex)
    (term : OmegaTwoIndex → W → B) :
    ∃ guard : OmegaTwoIndex → OmegaTwoIndex,
      ∀ a j : OmegaTwoIndex, guard j < a →
        (⨆ w : {w : W // footprintBelow a footprint w}, term j w.1) = ⨆ w, term j w := by
  classical
  choose S hS hSup using (fun j => exists_countable_subjoin_r67 hCCC (term j))
  have hBound (j : OmegaTwoIndex) :
      ∃ b, ∀ q : ↥(S j), ∀ i ∈ footprint q.1, i < b := by
    letI : Countable (↥(S j)) := (hS j).to_subtype
    let U : Set OmegaTwoIndex := ⋃ q : ↥(S j), (footprint q.1 : Set OmegaTwoIndex)
    have hU : U.Countable := Set.countable_iUnion (fun q : ↥(S j) =>
      (footprint q.1).finite_toSet.countable)
    obtain ⟨b,hb⟩ := OmegaTwoIndex_countable_bounded_r101 U hU
    exact ⟨b,fun q i hi => hb i (Set.mem_iUnion.mpr ⟨q,hi⟩)⟩
  choose guard hGuard using hBound
  refine ⟨guard,fun a j hj => le_antisymm ?_ ?_⟩
  · exact iSup_le (fun w => le_iSup (term j) w.1)
  · rw [← hSup j]
    apply iSup_le
    intro w
    exact le_iSup (fun v : {v : W // footprintBelow a footprint v} => term j v.1)
      ⟨w.1,fun i hi => (hGuard j w i hi).trans hj⟩

end FiniteSupport
end JSP000933
