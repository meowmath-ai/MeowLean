import JSP000933CompleteNameTransport

open Lattice

namespace JSP000933
namespace CompleteDiagram

structure System (I : Type) [LinearOrder I] where
  algebra : I → Type
  alg : ∀ i, NontrivialCompleteBooleanAlgebra (algebra i)
  transition : ∀ {i j : I}, i ≤ j → algebra i → algebra j
  identity : ∀ (i : I) (x : algebra i), transition (show i ≤ i from le_rfl) x = x
  comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : algebra i),
    transition hjk (transition hij x) = transition (hij.trans hjk) x

attribute [instance] System.alg

class IsComplete {I : Type} [LinearOrder I] (S : System I) : Prop where
  order : ∀ {i j : I} (h : i ≤ j) {a b : S.algebra i},
    S.transition h a ≤ S.transition h b ↔ a ≤ b
  top : ∀ {i j : I} (h : i ≤ j), S.transition h ⊤ = ⊤
  bot : ∀ {i j : I} (h : i ≤ j), S.transition h ⊥ = ⊥
  inf : ∀ {i j : I} (h : i ≤ j) (a b : S.algebra i),
    S.transition h (a ⊓ b) = S.transition h a ⊓ S.transition h b
  compl : ∀ {i j : I} (h : i ≤ j) (a : S.algebra i),
    S.transition h aᶜ = (S.transition h a)ᶜ
  joins : ∀ {i j : I} (h : i ≤ j) {D : Type} (v : D → S.algebra i),
    S.transition h (⨆ d, v d) = ⨆ d, S.transition h (v d)

variable {I : Type} [LinearOrder I] {S : System I} (hS : IsComplete S)

include hS in
theorem transition_mono {i j : I} (h : i ≤ j) :
    Monotone (S.transition h) :=
  fun _ _ hle => (hS.order h).mpr hle

include hS in
theorem transition_ne_bot {i j : I} (h : i ≤ j) {a : S.algebra i} (ha : a ≠ ⊥) :
    S.transition h a ≠ ⊥ := by
  intro he
  have hle : S.transition h a ≤ S.transition h ⊥ := by rw [he, hS.bot h]
  exact ha (le_bot_iff.mp ((hS.order h).mp hle))

structure Condition (S : System I) where
  stage : I
  value : S.algebra stage
  positive : value ≠ ⊥

namespace Condition

def Stronger (p q : Condition S) : Prop :=
  ∃ k : I, ∃ hp : p.stage ≤ k, ∃ hq : q.stage ≤ k,
    S.transition hp p.value ≤ S.transition hq q.value

include hS in
theorem stronger_at (p q : Condition S) {k : I} (hp : p.stage ≤ k)
    (hq : q.stage ≤ k) :
    Stronger p q ↔ S.transition hp p.value ≤ S.transition hq q.value := by
  constructor
  · rintro ⟨j, hjp, hjq, hj⟩
    let l := max j k
    have hjl : j ≤ l := le_max_left _ _
    have hkl : k ≤ l := le_max_right _ _
    apply (hS.order hkl).mp
    have hLift := transition_mono hS hjl hj
    rw [S.comp hjp hjl, S.comp hjq hjl] at hLift
    rw [S.comp hp hkl, S.comp hq hkl]
    exact hLift
  · exact fun h => ⟨k, hp, hq, h⟩

def preorder (S : System I) (hS : IsComplete S) : Preorder (Condition S) where
  le := Stronger
  le_refl p := ⟨p.stage, le_rfl, le_rfl, le_rfl⟩
  le_trans p q r hpq hqr := by
    let k := max p.stage (max q.stage r.stage)
    have hp : p.stage ≤ k := le_max_left _ _
    have hq : q.stage ≤ k := (le_max_left _ _).trans (le_max_right _ _)
    have hr : r.stage ≤ k := (le_max_right _ _).trans (le_max_right _ _)
    exact (stronger_at hS p r hp hr).mpr
      (((stronger_at hS p q hp hq).mp hpq).trans ((stronger_at hS q r hq hr).mp hqr))

instance instPreorder [h : IsComplete S] : Preorder (Condition S) := preorder S h

def atStage (i : I) (a : S.algebra i) (ha : a ≠ ⊥) : Condition S := ⟨i, a, ha⟩

theorem atStage_mono {i : I} {a b : S.algebra i} (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (hab : a ≤ b) : Stronger (atStage i a ha) (atStage i b hb) :=
  ⟨i, le_rfl, le_rfl, by simpa only [atStage, S.identity] using hab⟩

theorem promoted_equivalent {i j : I} (h : i ≤ j) (a : S.algebra i) (ha : a ≠ ⊥) :
    Stronger (atStage i a ha) (atStage j (S.transition h a) (transition_ne_bot hS h ha)) ∧
    Stronger (atStage j (S.transition h a) (transition_ne_bot hS h ha)) (atStage i a ha) := by
  constructor
  · refine ⟨j, h, le_rfl, ?_⟩
    simp only [atStage, S.identity, le_refl]
  · refine ⟨j, le_rfl, h, ?_⟩
    simp only [atStage, S.identity, le_refl]

include hS in
theorem compatibleValue_iff (p q : Condition S) {k : I} (hp : p.stage ≤ k)
    (hq : q.stage ≤ k) :
    (∃ r : Condition S, Stronger r p ∧ Stronger r q) ↔
      S.transition hp p.value ⊓ S.transition hq q.value ≠ ⊥ := by
  constructor
  · rintro ⟨r, hrp, hrq⟩ hz
    let l := max r.stage k
    have hrl : r.stage ≤ l := le_max_left _ _
    have hkl : k ≤ l := le_max_right _ _
    have hl1 := (stronger_at hS r p hrl (hp.trans hkl)).mp hrp
    have hl2 := (stronger_at hS r q hrl (hq.trans hkl)).mp hrq
    have hv := le_inf hl1 hl2
    rw [← S.comp hp hkl, ← S.comp hq hkl, ← hS.inf hkl, hz, hS.bot hkl] at hv
    exact transition_ne_bot hS hrl r.positive (le_bot_iff.mp hv)
  · intro hz
    let r := atStage k (S.transition hp p.value ⊓ S.transition hq q.value) hz
    refine ⟨r, ⟨k, (show r.stage ≤ k from le_rfl), hp, ?_⟩,
      ⟨k, (show r.stage ≤ k from le_rfl), hq, ?_⟩⟩
    · change S.transition (show k ≤ k from le_rfl)
        (S.transition hp p.value ⊓ S.transition hq q.value) ≤ _
      rw [S.identity]
      exact inf_le_left
    · change S.transition (show k ≤ k from le_rfl)
        (S.transition hp p.value ⊓ S.transition hq q.value) ≤ _
      rw [S.identity]
      exact inf_le_right

end Condition
end CompleteDiagram
end JSP000933
