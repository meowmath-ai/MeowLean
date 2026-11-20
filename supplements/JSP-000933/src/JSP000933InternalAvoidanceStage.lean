import JSP000933BooleanAvoidanceSchedule

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

abbrev EarlierIndex (j : OmegaOneIndex) := ↥(Set.Iio j)

abbrev EarlierClusterParam (S : BooleanAvoidanceSchedule B) (j : OmegaOneIndex) :=
  Σ e : EarlierIndex j, Fin (S.sampleCode e.1).1 → EarlierIndex j

noncomputable def avoidClosedRaw (D : (ℕ → B) → B)
    (S : BooleanAvoidanceSchedule B) (e : OmegaOneIndex) (x : ℕ → B) : B :=
  D x ⊓ (openValue (S.closedCode e) x)ᶜ

noncomputable def avoidClusterRaw (D : (ℕ → B) → B) (K : Word × Word → B)
    (S : BooleanAvoidanceSchedule B) {j : OmegaOneIndex}
    (old : EarlierIndex j → ℕ → B) (q : EarlierClusterParam S j) (x : ℕ → B) : B :=
  D x ⊓ weightedCluster K (S.sampleCode q.1.1).2 (fun i => old (q.2 i)) x

def AvoidsOn (D : (ℕ → B) → B) (K : Word × Word → B) (p : B)
    (S : BooleanAvoidanceSchedule B) (j : OmegaOneIndex) (old : EarlierIndex j → ℕ → B)
    (x : ℕ → B) : Prop :=
  (p ≤ D x) ∧
  (∀ i, p ≤ (realEqValue x (old i))ᶜ) ∧
  (∀ e : EarlierIndex j, p ≤ (qualifiedObstacle K (avoidClosedRaw D S e.1) x)ᶜ) ∧
  (∀ q : EarlierClusterParam S j, p ≤ (qualifiedObstacle K (avoidClusterRaw D K S old q) x)ᶜ)

theorem exists_AvoidsOn_r145
    (D : (ℕ → B) → B) (hD : RealTestExt D) (K : Word × Word → B) (p : B)
    (hNo : ∀ c : CoverCode B, p ≤ (goodCoverValue id D K c)ᶜ)
    (hIrr : ∀ z, p ⊓ D z ≤ (colorValue K z z)ᶜ)
    (S : BooleanAvoidanceSchedule B) (j : OmegaOneIndex) (old : EarlierIndex j → ℕ → B)
    (hOld : ∀ i, p ≤ D (old i)) :
    ∃ x : ℕ → B, AvoidsOn D K p S j old x := by
  let E := EarlierIndex j
  let C := EarlierClusterParam S j
  letI : Countable E := OmegaOneIndex_initial_countable_r61 j
  let f : (E ⊕ E) ⊕ C → (ℕ → B) → B :=
    Sum.elim (Sum.elim (fun i x => realEqValue x (old i))
      (fun e => qualifiedObstacle K (avoidClosedRaw D S e.1)))
      (fun q => qualifiedObstacle K (avoidClusterRaw D K S old q))
  have hf (i : (E ⊕ E) ⊕ C) (x y : ℕ → B) :
      Disjoint (p ⊓ (f i x ⊓ f i y)) (colorValue K x y) := by
    rcases i with (i | e) | q
    · exact equalitySingleton_independent_r141 K p (old i)
        ((le_inf le_rfl (hOld i)).trans (hIrr (old i))) x y
    · exact qualifiedObstacle_independent_r141 K (avoidClosedRaw D S e.1) p x y
    · exact qualifiedObstacle_independent_r141 K (avoidClusterRaw D K S old q) p x y
  obtain ⟨x,hx,hAvoid⟩ := exists_real_avoids_independentFamily_r140 D hD K p hNo f hf
  exact ⟨x,hx,fun i => hAvoid (.inl (.inl i)),fun e => hAvoid (.inl (.inr e)),
    fun q => hAvoid (.inr q)⟩

end CantorCodes
end JSP000933
