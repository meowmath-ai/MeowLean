import Flypitch4.Zfc

open Fol
open scoped BigOperators

namespace JSP000933
namespace SetLanguage

abbrev STerm (n : ℕ) := bounded_term L_ZFC n
abbrev SForm (n : ℕ) := bounded_formula L_ZFC n

def up {n : ℕ} (t : STerm n) : STerm (n + 1) :=
  lift_bounded_term t 1

def up2 {n : ℕ} (t : STerm n) : STerm (n + 2) :=
  lift_bounded_term t 2

def up3 {n : ℕ} (t : STerm n) : STerm (n + 3) :=
  lift_bounded_term t 3

def up4 {n : ℕ} (t : STerm n) : STerm (n + 4) :=
  lift_bounded_term t 4

def sAll {n : ℕ} (body : STerm (n + 1) → SForm (n + 1)) : SForm n :=
  bd_all (body (bd_var ⟨0, Nat.succ_pos n⟩))

def sEx {n : ℕ} (body : STerm (n + 1) → SForm (n + 1)) : SForm n :=
  bd_ex (body (bd_var ⟨0, Nat.succ_pos n⟩))

def allIn {n : ℕ} (domain : STerm n) (body : STerm (n + 1) → SForm (n + 1)) : SForm n :=
  sAll fun x => bd_imp (mem' x (up domain)) (body x)

def exIn {n : ℕ} (domain : STerm n) (body : STerm (n + 1) → SForm (n + 1)) : SForm n :=
  sEx fun x => bd_and (mem' x (up domain)) (body x)

def zero {n : ℕ} : STerm n := emptyset'
def omega {n : ℕ} : STerm n := omega'
def powerset {n : ℕ} (t : STerm n) : STerm n := Powerset t

def omegaSubsets {n : ℕ} : STerm n := powerset omega

def natLE_f {n : ℕ} (x y : STerm n) : SForm n :=
  bd_or (mem' x y) (bd_equal x y)

def successor_f {n : ℕ} (x y : STerm n) : SForm n :=
  sAll fun z => bd_biimp (mem' z (up y))
    (bd_or (mem' z (up x)) (bd_equal z (up x)))

def value_f {n : ℕ} (g i v : STerm n) : SForm n :=
  mem' (pair' i v) g

def naturalFunctionOn_f {n : ℕ} (g domain : STerm n) : SForm n :=
  allIn domain fun i =>
    exIn omega fun v =>
      bd_and (value_f (up2 g) (up i) v)
        (allIn omega fun w =>
          bd_imp (value_f (up3 g) (up2 i) w) (bd_equal (up v) w))

def naturalRecursion_f {n k : ℕ} (m base result : STerm n)
    (param : Fin k → STerm n)
    (step : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → STerm d → STerm d → SForm d) :
    SForm n :=
  exIn omega fun endIndex =>
    bd_and (successor_f (up m) endIndex) (sEx fun g =>
      bd_and (naturalFunctionOn_f g (up endIndex))
        (bd_and (value_f g zero (up2 base))
          (bd_and (value_f g (up2 m) (up2 result))
            (allIn (up2 m) fun i =>
              allIn omega fun j =>
                allIn omega fun cur =>
                  allIn omega fun next =>
                    bd_imp (bd_and (successor_f (up3 i) (up2 j))
                      (bd_and (value_f (up4 g) (up3 i) (up cur))
                        (value_f (up4 g) (up2 j) next)))
                      (step (fun a => lift_bounded_term (param a) 6)
                        (up3 i) (up cur) next)))))

def addition_f {n : ℕ} (x y z : STerm n) : SForm n :=
  naturalRecursion_f y x z (fun i : Fin 0 => Fin.elim0 i)
    (fun _ _ cur next => successor_f cur next)

def multiplication_f {n : ℕ} (x y z : STerm n) : SForm n :=
  naturalRecursion_f y zero z (fun _ : Fin 1 => x)
    (fun param _ cur next => addition_f cur (param 0) next)

def factorial_f {n : ℕ} (m r : STerm n) : SForm n :=
  exIn omega fun one =>
    bd_and (successor_f zero one)
      (naturalRecursion_f (up m) one (up r) (fun i : Fin 0 => Fin.elim0 i)
        (fun _ i cur next =>
          exIn omega fun j =>
            bd_and (successor_f (up i) j) (multiplication_f (up cur) j (up next))))

def differenceBit_f {n : ℕ} (A B i : STerm n) : SForm n :=
  bd_and (mem' i A) (bd_not (mem' i B))

def ordinaryPrefixCount_f {n : ℕ} (A B p r : STerm n) : SForm n :=
  naturalRecursion_f p zero r (fun j : Fin 2 => if j = 0 then A else B)
    (fun param i cur next =>
      let b := differenceBit_f (param 0) (param 1) i
      bd_and (bd_imp b (successor_f cur next)) (bd_imp (bd_not b) (bd_equal cur next)))

def harmonicPrefixMass_f {n : ℕ} (allBits : Bool) (A B p r : STerm n) : SForm n :=
  exIn omega fun fac =>
    bd_and (factorial_f (up p) fac)
      (naturalRecursion_f (up p) zero (up r)
        (fun j : Fin 3 => if j = 0 then up A else if j = 1 then up B else fac)
        (fun param i cur next =>
          let b := if allBits then bd_not bd_falsum else differenceBit_f (param 0) (param 1) i
          bd_and (bd_imp b
            (exIn omega fun d =>
              exIn omega fun q =>
                bd_and (successor_f (up2 i) (up d))
                  (bd_and (multiplication_f (up d) q (up2 (param 2)))
                    (addition_f (up2 cur) q (up2 next)))))
            (bd_imp (bd_not b) (bd_equal cur next))))

def ordinaryBudget_f {n : ℕ} (A B k p : STerm n) : SForm n :=
  exIn omega fun count =>
    exIn omega fun product =>
      bd_and (ordinaryPrefixCount_f (up2 A) (up2 B) (up2 p) (up count))
        (bd_and (multiplication_f (up2 k) (up count) product)
          (natLE_f product (up2 p)))

def harmonicBudget_f {n : ℕ} (A B k p : STerm n) : SForm n :=
  exIn omega fun numerator =>
    exIn omega fun denominator =>
      exIn omega fun product =>
        bd_and (harmonicPrefixMass_f false (up3 A) (up3 B) (up3 p) (up2 numerator))
          (bd_and (harmonicPrefixMass_f true (up3 A) (up3 B) (up3 p) (up denominator))
            (bd_and (multiplication_f (up3 k) (up2 numerator) product)
              (natLE_f product (up denominator))))

def eventualBudget_f {n : ℕ} (A B : STerm n)
    (budget : ∀ {d : ℕ}, STerm d → STerm d → STerm d → STerm d → SForm d) : SForm n :=
  allIn omega fun k =>
    bd_imp (bd_not (bd_equal k zero))
      (exIn omega fun cutoff =>
        allIn omega fun p =>
          bd_imp (natLE_f (up cutoff) p)
            (budget (up3 A) (up3 B) (up2 k) p))

def ordinaryLE_f {n : ℕ} (A B : STerm n) : SForm n :=
  eventualBudget_f A B (fun A B k p => ordinaryBudget_f A B k p)

def harmonicLE_f {n : ℕ} (A B : STerm n) : SForm n :=
  eventualBudget_f A B (fun A B k p => harmonicBudget_f A B k p)

def pairsOnly_f {n : ℕ} (G : STerm n) : SForm n :=
  allIn G fun u =>
    exIn omegaSubsets fun A =>
      exIn omegaSubsets fun B =>
        bd_equal (pair' (up A) B) (up2 u)

def graphTotal_f {n : ℕ} (G : STerm n) : SForm n :=
  allIn omegaSubsets fun A =>
    exIn omegaSubsets fun B =>
      value_f (up2 G) (up A) B

def graphOnto_f {n : ℕ} (G : STerm n) : SForm n :=
  allIn omegaSubsets fun B =>
    exIn omegaSubsets fun A =>
      value_f (up2 G) A (up B)

def graphPreserveReflect_f {n : ℕ} (G : STerm n) : SForm n :=
  allIn omegaSubsets fun A =>
    allIn omegaSubsets fun A' =>
      allIn omegaSubsets fun B =>
        allIn omegaSubsets fun B' =>
          bd_imp (bd_and (value_f (up4 G) (up3 A) (up B))
            (value_f (up4 G) (up2 A') B'))
            (bd_biimp (ordinaryLE_f (up3 A) (up2 A')) (harmonicLE_f (up B) B'))

def densityQuotientIso_f : sentence L_ZFC :=
  sEx fun G =>
    bd_and (pairsOnly_f G)
      (bd_and (graphTotal_f G) (bd_and (graphOnto_f G) (graphPreserveReflect_f G)))

def densityQuotientNonIso_f : sentence L_ZFC := bd_not densityQuotientIso_f

end SetLanguage
end JSP000933
