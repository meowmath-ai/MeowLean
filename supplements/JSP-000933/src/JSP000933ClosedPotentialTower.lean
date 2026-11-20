import JSP000933ClosedPotentialPartitions

namespace JSP000933
namespace CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

theorem exists_closedPotentialTower_r224 (p : B) (s : Word) (K : ℕ → Word → B)
    (hp : p ≤ closedPotential K s) :
    Nonempty (WordPartitionTower B p s (fun _ => closedPotential K)) := by
  classical
  let State (n : ℕ) := {P : IndexedPartition B Word p //
    (∀ u, P.weight u ≤ closedPotential K u) ∧ (∀ u, u.length < n → P.weight u = ⊥)}
  have hSeed (u : Word) : (seedWordPartition p s).weight u ≤ closedPotential K u := by
    by_cases hu : u=s
    · subst u; simpa only [seedWordPartition_weight_r217] using hp
    · simp [seedWordPartition,hu]
  let init : State 0 := ⟨seedWordPartition p s,hSeed,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  let ext (n : ℕ) (P : State n) := extend_by_closedPotential_r223 P.1 K n P.2.1 P.2.2
  let next (n : ℕ) (P : State n) : State (n+1) :=
    ⟨Classical.choose (ext n P),(Classical.choose_spec (ext n P)).2⟩
  let F := Nat.rec (motive := State) init next
  refine ⟨⟨fun n => (F n).1,rfl,?_,?_,?_⟩⟩
  · intro n
    exact (Classical.choose_spec (ext n (F n))).1
  · intro n u
    exact (F (n+1)).2.1 u
  · intro n u hu
    exact (F n).2.2 u hu

end CantorCodes
end JSP000933
