import PEqualNP.Defs

namespace Paid17719

inductive Reach {α : Type} (op : Bool → α → α → α) (goal : α) : Nat → Set α → Prop
  | out {k S} (h : goal ∈ S) : Reach op goal k S
  | gate {k S a b} (d : Bool) (ha : a ∈ S) (hb : b ∈ S)
      (h : Reach op goal k (insert (op d a b) S)) : Reach op goal (k+1) S

theorem Reach.mono {α : Type} {op : Bool → α → α → α} {goal : α} {k : Nat} {S : Set α}
    (p : Reach op goal k S) : ∀ {S' : Set α}, S ⊆ S' → Reach op goal k S' := by
  induction p with
  | out h => exact fun h' => .out (h' h)
  | gate d ha hb _ ih =>
    intro T h
    exact .gate d (h ha) (h hb) (ih (Set.insert_subset_insert h))

section
variable {α β : Type} {op : Bool → α → α → α} {ob : Bool → β → β → β}
variable (phi : α → β) (zero : β)
def image (S : Set α) : Set β := insert zero (phi '' S)

theorem map_mem {S : Set α} {w : α} (h : w ∈ S) : phi w ∈ image phi zero S :=
  Set.mem_insert_of_mem _ ⟨w,h,rfl⟩

theorem map_insert (S : Set α) (v : α) : image phi zero (insert v S) =
    insert (phi v) (image phi zero S) := by
  ext y
  simp only [image, Set.image_insert_eq, Set.mem_insert_iff]
  tauto

theorem simulate {goal : α} {k S} (h : Reach op goal k S)
    (hom : ∀ d a b, phi (op d a b) = ob d (phi a) (phi b)) :
    Reach ob (phi goal) k (image phi zero S) := by
  induction h with
  | out h => exact .out (map_mem _ _ h)
  | gate d ha hb _ ih =>
    apply Reach.gate d (map_mem phi zero ha) (map_mem phi zero hb)
    rw [map_insert,hom] at ih
    exact ih

theorem paid_projection {goal : α} {k S} (h : Reach op goal k S)
    (hom : ∀ d a b, phi (op d a b) = ob d (phi a) (phi b))
    (different : α → Prop)
    (unchanged : ∀ d a b, ¬different a → ¬different b → ¬different (op d a b))
    (erasable : ∀ d a b, phi a = zero ∨ phi b = zero →
      phi (op d a b) = zero ∨ phi (op d a b) = phi a ∨ phi (op d a b) = phi b)
    (target_changes : different goal) (survives : phi goal ≠ zero)
    (initial : ∀ w ∈ S, different w → phi w = zero) :
    ∃ l < k, Reach ob (phi goal) l (image phi zero S) := by
  classical
  induction h with
  | out h => exact False.elim (survives (initial _ h target_changes))
  | @gate k S a b d ha hb cont ih =>
    by_cases hits : different a ∨ different b
    · have hz : phi a = zero ∨ phi b = zero := hits.imp (initial a ha) (initial b hb)
      have ready : phi (op d a b) ∈ image phi zero S := by
        rcases erasable d a b hz with e | e | e
        · rw [e]; exact Set.mem_insert _ _
        · rw [e]; exact map_mem phi zero ha
        · rw [e]; exact map_mem phi zero hb
      have p := simulate phi zero cont hom
      rw [map_insert] at p
      exact ⟨k, by omega, p.mono (Set.insert_subset ready (Set.Subset.rfl))⟩
    · have next : ∀ w ∈ insert (op d a b) S, different w → phi w = zero := by
        intro w hw diff
        rcases Set.mem_insert_iff.mp hw with rfl | hw
        · exact False.elim ((unchanged d a b (fun hn => hits (Or.inl hn))
              (fun hn => hits (Or.inr hn))) diff)
        · exact initial _ hw diff
      obtain ⟨l,hl,p⟩ := ih next
      rw [map_insert,hom] at p
      exact ⟨l+1, by omega, .gate d (map_mem phi zero ha) (map_mem phi zero hb) p⟩

end
end Paid17719
namespace Theta17719

open Paid17719
structure W where
  bit : Fin 24 → Bool
  x : Fin 3
  y : Fin 3
deriving DecidableEq

def sat (a b : Fin 3) : Fin 3 := ⟨min 2 (a.val+b.val), by omega⟩
def bot : W := ⟨fun _ => false,2,2⟩
def meet (d : Bool) (a b : W) : W :=
  if d then ⟨fun i => a.bit i && b.bit i, sat a.x b.x, sat a.y b.y⟩
  else ⟨fun i => a.bit i || b.bit i, min a.x b.x,min a.y b.y⟩
def cut (t : Nat) (w : W) : W :=
  ⟨fun i => if i.val < t then w.bit i else false, w.x,w.y⟩

theorem map_meet (t : Nat) (d : Bool) (a b : W) :
    cut t (meet d a b) = meet d (cut t a) (cut t b) := by
  cases d <;> congr 1 <;> try rfl
  all_goals
    funext i
    by_cases hi : i.val < t <;> simp [cut,meet,hi]

theorem zeros : (∀ g : Fin 3, sat 2 g = 2 ∧ sat g 2 = 2 ∧ min 2 g = g ∧ min g 2 = g) := by
  decide

theorem killL (d : Bool) (a : W) : meet d bot a = if d then bot else a := by
  rcases a with ⟨f,x,y⟩
  cases d <;> simp [meet,bot,zeros]

theorem killR (d : Bool) (a : W) : meet d a bot = if d then bot else a := by
  rcases a with ⟨f,x,y⟩
  cases d <;> simp [meet,bot,zeros]

def rows : List Nat := [129, 130, 2049, 2080, 4098, 4128, 4160, 8193, 8256, 99, 224, 2114, 2240, 4097, 8226, 8352, 10242, 14464, 2064, 2048, 136, 128, 8196, 8192]
def raw (t : Nat) (j : Fin 25) : W :=
  ⟨fun i => decide (i.val<t) && (rows.getD i.val 0).testBit j.val,
   if j.val=0 then 0 else if j.val=7 then 1 else 2,
   if j.val=7 then 0 else if j.val=0 then 1 else 2⟩
def target (t : Nat) : W :=
  ⟨fun i => decide (i.val<t ∧ (i.val<9 ∨ i.val=18 ∨ i.val=20 ∨ i.val=22)),2,2⟩
def bank (t : Nat) : Set W := {w | w = bot ∨ ∃ j : Fin 25, w = raw t j}
def diff (t : Nat) (w : W) : Prop := w.bit (Fin.ofNat 24 t) ≠ w.bit (Fin.ofNat 24 (t+1))

def stage (k : Fin 3) := 18+2*k.val

theorem facts : ∀ j : Fin 3, let t := stage j
    cut t (target (t+2)) = target t ∧ target t ≠ bot ∧ diff t (target (t+2)) ∧
    cut t bot = bot ∧ ¬ diff t bot ∧
    ∀ i : Fin 25, cut t (raw (t+2) i) = raw t i ∧
      (diff t (raw (t+2) i) → cut t (raw (t+2) i) = bot) := by
  unfold diff
  decide +kernel

theorem step (j : Fin 3) (n : Nat)
    (p : Reach meet (target (stage j+2)) n (bank (stage j+2))) :
    ∃ l < n, Reach meet (target (stage j)) l (bank (stage j)) := by
  let t := stage j
  obtain ⟨hgoal,hnon,hd,hbot,hnod,hraw⟩ := facts j
  have e : ∀ d a b, cut t a = bot ∨ cut t b = bot →
      cut t (meet d a b) = bot ∨ cut t (meet d a b) = cut t a ∨ cut t (meet d a b) = cut t b := by
    intro d a b h
    rw [map_meet]
    rcases h with h | h
    · rw [h,killL]; cases d <;> simp
    · rw [h,killR]; cases d <;> simp
  have un : ∀ d a b, ¬ diff t a → ¬ diff t b → ¬ diff t (meet d a b) := by
    intro d a b ha hb
    simp only [diff,not_not] at ha hb ⊢
    cases d <;> simp [meet,ha,hb]
  have init : ∀ w ∈ bank (t+2), diff t w → cut t w = bot := by
    rintro w (rfl | ⟨i,rfl⟩) h
    · exact hbot
    · exact (hraw i).2 h
  have hn : cut t (target (t+2)) ≠ bot := hgoal ▸ hnon
  obtain ⟨l,hl,h⟩ := paid_projection (cut t) bot p (map_meet t) (diff t) un e hd hn init
  rw [hgoal] at h
  refine ⟨l,hl,h.mono ?_⟩
  rintro w (h | ⟨v,hv,rfl⟩)
  · exact Or.inl h
  · rcases hv with rfl | ⟨i,rfl⟩
    · exact Or.inl hbot
    · exact Or.inr ⟨i,(hraw i).1⟩

theorem theta_of_source (s : Nat) (hs : s ≤ 15)
    (p : Reach meet (target 24) s (bank 24)) :
    ∃ l ≤ 12, Reach meet (target 18) l (bank 18) := by
  obtain ⟨u,hu,h₁⟩ := step 2 s p
  obtain ⟨v,hv,h₂⟩ := step 1 u h₁
  obtain ⟨l,hl,h₃⟩ := step 0 v h₂
  exact ⟨l,by omega,h₃⟩
end Theta17719
