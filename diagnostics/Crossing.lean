import Mathlib
import PEqualNP.Outside.L_meta_1485
import PEqualNP.Outside.L_meta_5242

namespace Crossing3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1485

abbrev V (n : Nat) := Fin n → Bool
def W {n : Nat} (C : Circuit) (w : Nat) (z : V n) : Prop :=
  val C (List.ofFn z) w = true

theorem read_raw {n : Nat} (C : Circuit) (x : V n) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := PEqualNP.Outside.L_meta_5242.Base.val_ofFn C x u

theorem ops {C : Circuit} (hm : Monotone2 C) {j : Nat} (hj : j < C.gates.length) :
    ((gateAt C j).op = .and ∨ (gateAt C j).op = .or) ∧ (gateAt C j).inputs.length ≤ 2 := by
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hm _ (gateAt_mem hj)

theorem monotone {n : Nat} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (x y : V n) (inc : ∀ i, x i = true → y i = true) :
    ∀ w, W C w x → W C w y := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases raw : w<n
    · let i : Fin n := ⟨w,raw⟩
      change val C (List.ofFn x) i.val = true → val C (List.ofFn y) i.val = true
      rw [read_raw C x i,read_raw C y i]
      exact inc i
    · by_cases out : n+C.gates.length ≤ w
      · intro hx
        change val C (List.ofFn x) w = true at hx
        rw [val_ge (n := n) (by simp) out] at hx
        contradiction
      · let j := w-n
        have wj : w=n+j := by dsimp [j]; omega
        have hj : j<C.gates.length := by omega
        rcases (ops hm hj).1 with hand | hor
        · intro h
          rw [wj] at h ⊢
          apply (val_and (n := n) (C := C) (x := List.ofFn y) (by simp) hj hand).mpr
          intro a ha
          obtain ⟨lt,up⟩ := (val_and (n := n) (C := C) (x := List.ofFn x) (by simp) hj hand).mp
            h a ha
          exact ⟨lt,ih a (by omega) up⟩
        · intro h
          rw [wj] at h ⊢
          obtain ⟨a,ha,lt,up⟩ := (val_or (n := n) (by simp) hj hor).mp h
          exact (val_or (by simp) hj hor).mpr ⟨a,ha,lt,ih a (by omega) up⟩

variable {n : Nat} {C : Circuit}

def P (s : Fin n → Bool) (x : V n) : V n := fun i => s i && x i
def L (s : Fin n → Bool) (x : V n) : V n := fun i => !s i && x i

def Clean (C : Circuit) (s : Fin n → Bool) (F : V n → Prop) (w : Nat) :=
  ∀ x, W C w x → W C w (P s x) ∨ W C w (L s x) ∨ F x

def Cross (C : Circuit) (s : Fin n → Bool) (a b : Nat) (x : V n) :=
  W C a (P s x) ∧ ¬ W C a (L s x) ∧ ¬ W C b (P s x) ∧ W C b (L s x)

theorem propagate (hm : Monotone2 C) (rb : ReadsBack n C) (s : Fin n → Bool)
    (F : V n → Prop) (local' : ∀ j < C.gates.length, (gateAt C j).op = .and → Clean C s F (n+j)) :
    ∀ w, Clean C s F w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro x on
    by_cases raw : w<n
    · let i : Fin n := ⟨w,raw⟩
      have read (y : V n) : W C w y ↔ y i = true := by
        change val C (List.ofFn y) i.val = true ↔ _
        rw [read_raw C y i]
      have active := (read x).mp on
      cases mark : s i with
      | false => exact Or.inr (Or.inl ((read _).mpr (by simp [L,mark,active])))
      | true => exact Or.inl ((read _).mpr (by simp [P,mark,active]))
    · by_cases out : n+C.gates.length ≤ w
      · change val C (List.ofFn x) w = true at on
        rw [val_ge (n := n) (by simp) out] at on
        contradiction
      · let j := w-n
        have wj : w=n+j := by dsimp [j]; omega
        have hj : j<C.gates.length := by omega
        rw [wj] at on ⊢
        rcases (ops hm hj).1 with hand | hor
        · exact local' j hj hand x on
        · obtain ⟨a,ha,lt,h⟩ := (val_or (by simp) hj hor).mp on
          rcases ih a (by omega) x h with p | l | f
          · exact Or.inl ((val_or (by simp) hj hor).mpr ⟨a,ha,lt,p⟩)
          · exact Or.inr (Or.inl ((val_or (by simp) hj hor).mpr ⟨a,ha,lt,l⟩))
          · exact Or.inr (Or.inr f)

private theorem two_entries {xs : List Nat} {a b : Nat} (len : xs.length ≤ 2)
    (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) :
    xs = [a,b] ∨ xs = [b,a] := by
  rcases xs with _ | ⟨u,_ | ⟨v,_ | ⟨t,ts⟩⟩⟩
  · simp at ha
  · simp only [List.mem_singleton] at ha hb
    exact (hne (ha.trans hb.symm)).elim
  · simp only [List.mem_cons,List.mem_singleton] at ha hb
    rcases ha with h | h <;> rcases hb with k | k <;> subst_vars <;> simp_all
  · simp only [List.length_cons] at len
    omega

theorem no_cross_iff (hm : Monotone2 C) (rb : ReadsBack n C) (s : Fin n → Bool)
    (F : V n → Prop) :
    (∀ j < C.gates.length, (gateAt C j).op = .and → Clean C s F (n+j)) ↔
    (∀ j < C.gates.length, (gateAt C j).op = .and → ∀ a b, (gateAt C j).inputs=[a,b] →
      ∀ x, ¬ F x → ¬ Cross C s a b x ∧ ¬ Cross C s b a x) := by
  classical
  constructor
  · intro clean j hj hand a b inp x bad
    have both (y : V n) : W C (n+j) y ↔ W C a y ∧ W C b y := by
      rw [W, val_and (n := n) (by simp) hj hand, inp]
      have la := rb j hj a (by simp [inp])
      have lb := rb j hj b (by simp [inp])
      simp [W,la,lb]
    have pp : ∀ e, W C e (P s x) → W C e x :=
      monotone hm rb _ _ (fun i h => (Bool.and_eq_true_iff.mp h).2)
    have ll : ∀ e, W C e (L s x) → W C e x :=
      monotone hm rb _ _ (fun i h => (Bool.and_eq_true_iff.mp h).2)
    constructor
    · rintro ⟨pa,na,nb,lb⟩
      rcases clean j hj hand x ((both x).mpr ⟨pp a pa,ll b lb⟩) with p | l | f
      · exact nb ((both _).mp p).2
      · exact na ((both _).mp l).1
      · exact bad f
    · rintro ⟨pb,nb,na,la⟩
      rcases clean j hj hand x ((both x).mpr ⟨ll a la,pp b pb⟩) with p | l | f
      · exact na ((both _).mp p).1
      · exact nb ((both _).mp l).2
      · exact bad f
  · intro nogo
    have all (w : Nat) : Clean C s F w := by
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro x on
        by_cases raw : w<n
        · let i : Fin n := ⟨w,raw⟩
          have read (y : V n) : W C w y ↔ y i = true := by
            change val C (List.ofFn y) i.val = true ↔ _
            rw [read_raw C y i]
          have active := (read x).mp on
          cases mark : s i with
          | false => exact Or.inr (Or.inl ((read _).mpr (by simp [L,mark,active])))
          | true => exact Or.inl ((read _).mpr (by simp [P,mark,active]))
        · by_cases out : n+C.gates.length ≤ w
          · change val C (List.ofFn x) w = true at on
            rw [val_ge (n := n) (by simp) out] at on
            contradiction
          · let j := w-n
            have wj : w=n+j := by dsimp [j]; omega
            have hj : j<C.gates.length := by omega
            rw [wj] at on ⊢
            rcases (ops hm hj).1 with hand | hor
            · by_cases fx : F x
              · exact Or.inr (Or.inr fx)
              · have both (y : V n) : W C (n+j) y ↔ ∀ a ∈ (gateAt C j).inputs, W C a y := by
                  rw [W, val_and (n := n) (by simp) hj hand]
                  exact ⟨fun h a ha => (h a ha).2,fun h a ha => ⟨rb j hj a ha,h a ha⟩⟩
                by_cases pos : ∀ a ∈ (gateAt C j).inputs, W C a (P s x)
                · exact Or.inl ((both _).mpr pos)
                · by_cases lin : ∀ a ∈ (gateAt C j).inputs, W C a (L s x)
                  · exact Or.inr (Or.inl ((both _).mpr lin))
                  · obtain ⟨a,ha,na⟩ : ∃ a ∈ (gateAt C j).inputs, ¬ W C a (P s x) := by
                      by_contra! none
                      exact pos none
                    obtain ⟨b,hb,nb⟩ : ∃ b ∈ (gateAt C j).inputs, ¬ W C b (L s x) := by
                      by_contra! none
                      exact lin none
                    have child (v) (hv : v ∈ (gateAt C j).inputs) :
                        W C v (P s x) ∨ W C v (L s x) := by
                      have rbv := rb j hj v hv
                      rcases ih v (by omega) x ((both _).mp on v hv) with p | l | f
                      · exact Or.inl p
                      · exact Or.inr l
                      · exact (fx f).elim
                    have la := (child a ha).resolve_left na
                    have pb := (child b hb).resolve_right nb
                    have ne : a≠b := fun e => na (e ▸ pb)
                    have cross : Cross C s b a x := ⟨pb,nb,na,la⟩
                    have len := (ops hm hj).2
                    have two : (gateAt C j).inputs = [a,b] ∨ (gateAt C j).inputs = [b,a] :=
                      two_entries len ha hb ne
                    rcases two with ab | ba
                    · exact ((nogo j hj hand a b ab x fx).2 cross).elim
                    · exact ((nogo j hj hand b a ba x fx).1 cross).elim
            · obtain ⟨a,ha,lt,h⟩ := (val_or (by simp) hj hor).mp on
              rcases ih a (by omega) x h with p | l | f
              · exact Or.inl ((val_or (by simp) hj hor).mpr ⟨a,ha,lt,p⟩)
              · exact Or.inr (Or.inl ((val_or (by simp) hj hor).mpr ⟨a,ha,lt,l⟩))
              · exact Or.inr (Or.inr f)
    exact fun j _ _ => all (n+j)

end Crossing3321
