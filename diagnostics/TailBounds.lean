import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9939_suffix
def raw : List Nat := [0,255,170,204,240,23,105]
def neighbors (s : List Nat) (a : Nat) := s.flatMap (fun b => [a &&& b, a ||| b])
def oneMore (s : List Nat) (t : Nat) := s.contains t || s.any (fun a => s.any (fun b =>
  (a &&& b == t) || (a ||| b == t)))
def tailCan : Nat → List Nat → Nat → Bool
  | 0,s,t => s.contains t
  | 1,s,t => oneMore s t
  | n+2,s,t => oneMore s t || s.any (fun a => (neighbors s a).any (fun z =>
      !s.contains z && tailCan (n+1) (z::s) t))
theorem ready_iff {s : List Nat} {t : Nat} :
    oneMore s t=true ↔ t∈s ∨ ∃ a∈s, ∃ b∈s, a &&& b=t ∨ a ||| b=t := by
  simp [oneMore,Bool.or_eq_true,List.any_eq_true]
inductive Program : Nat → List Nat → Nat → Prop
  | pin {n s t} : t∈s → Program n s t
  | gate {n s a b z t} : a∈s → b∈s → (z=a &&& b ∨ z=a ||| b) →
      Program n (z::s) t → Program (n+1) s t
theorem program_mono {k s t} (h : Program k s t) (s' : List Nat) (sub : ∀ x∈s, x∈s') :
    Program k s' t := by
  induction h generalizing s' with
  | pin hm => exact .pin (sub _ hm)
  | gate ha hb eq _ rec =>
    apply Program.gate (sub _ ha) (sub _ hb) eq
    apply rec
    intro x hx
    rcases List.mem_cons.mp hx with e | hh
    · exact List.mem_cons.mpr (Or.inl e)
    · exact List.mem_cons.mpr (Or.inr (sub _ hh))
theorem tail_pad_aux (n : Nat) (s : List Nat) (t : Nat) (h : tailCan n s t=true) :
    tailCan (n+1) s t=true := by
  induction n generalizing s t with
  | zero => exact ready_iff.mpr (Or.inl (List.contains_iff_mem.mp h))
  | succ n rec =>
    cases n with
    | zero =>
      simp only [tailCan,Bool.or_eq_true]
      exact Or.inl h
    | succ n =>
      simp only [tailCan,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true] at h ⊢
      rcases h with yes | ⟨a,ha,z,hz,off,yes⟩
      · exact Or.inl yes
      · exact Or.inr ⟨a,ha,z,hz,off,rec _ _ yes⟩
theorem or_join {x y : Bool} (h : x=true ∨ y=true) : (x||y)=true := by simpa only [Bool.or_eq_true] using h
theorem tail_sound {k s t} (p : Program k s t) : tailCan k s t=true := by
  induction k generalizing s t with
  | zero =>
    cases p with
    | pin h => exact List.contains_iff_mem.mpr h
  | succ k ih =>
    cases k with
    | zero =>
      apply ready_iff.mpr
      cases p with
      | pin h => exact Or.inl h
      | gate ha hb operation h =>
        cases h with
        | pin hm =>
          rcases List.mem_cons.mp hm with e | known
          · exact Or.inr ⟨_,ha,_,hb,e.symm ▸ operation⟩
          · exact Or.inl known
    | succ k =>
      cases p with
      | pin h => exact or_join (Or.inl (ready_iff.mpr (Or.inl h)))
      | @gate _ _ a b z _ ha hb eq rest =>
        by_cases hm : z∈s
        · have sub (v) (hv : v∈z::s) : v∈s :=
            (List.mem_cons.mp hv).elim (fun e => e.symm ▸ hm) id
          have r := ih (program_mono rest s sub)
          cases k with
          | zero => exact or_join (Or.inl r)
          | succ j =>
            -- Increasing the budget preserves a successful checked tail.
            exact tail_pad_aux _ _ _ r
        · apply or_join
          right
          apply List.any_eq_true.mpr
          refine ⟨a,ha,List.any_eq_true.mpr ⟨z,?_,?_⟩⟩
          · apply List.mem_flatMap.mpr
            exact ⟨b,hb,by rcases eq with rfl|rfl <;> simp⟩
          · simp [hm,ih rest]

def domain : List Nat := [0, 2, 4, 6, 16, 18, 20, 22, 23, 128, 130, 132, 134, 136, 138, 140, 142, 144, 146, 148, 150, 151, 152, 154, 156, 158, 159, 160, 162, 164, 166, 168, 170, 172, 174, 176, 178, 180, 182, 183, 184, 186, 188, 190, 191, 192, 194, 196, 198, 200, 202, 204, 206, 208, 210, 212, 214, 215, 216, 218, 220, 222, 223, 224, 226, 228, 230, 232, 234, 236, 238, 240, 242, 244, 246, 247, 248, 250, 252, 254, 255]
def banks : List (List Nat) := [[6, 136, 144, 150, 159, 224, 232, 238], [6, 136, 144, 150, 159, 232, 238, 248], [6, 136, 150, 159, 224, 232, 238, 246], [6, 136, 150, 159, 232, 238, 246, 248], [18, 132, 150, 160, 183, 200, 232, 250], [18, 132, 150, 160, 183, 232, 236, 250], [18, 150, 160, 183, 200, 222, 232, 250], [18, 150, 160, 183, 222, 232, 236, 250], [20, 130, 150, 168, 192, 215, 232, 252], [20, 130, 150, 192, 215, 232, 234, 252], [20, 150, 168, 190, 192, 215, 232, 252], [20, 150, 190, 192, 215, 232, 234, 252], [22, 128, 136, 150, 224, 232, 238, 254], [22, 128, 136, 150, 232, 238, 248, 254], [22, 128, 150, 160, 200, 232, 250, 254], [22, 128, 150, 160, 232, 236, 250, 254], [22, 128, 150, 168, 192, 232, 252, 254], [22, 128, 150, 192, 232, 234, 252, 254], [128, 136, 150, 151, 224, 232, 238, 254], [128, 136, 150, 151, 232, 238, 248, 254], [128, 150, 151, 160, 200, 232, 250, 254], [128, 150, 151, 160, 232, 236, 250, 254], [128, 150, 151, 168, 192, 232, 252, 254], [128, 150, 151, 192, 232, 234, 252, 254]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem oneMore_impossible : tailCan 1 (105::domain) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem two_need18 : tailCan 2 (105::domain.erase 18) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem two_need159 : tailCan 2 (105::domain.erase 159) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss0 : tailCan 3 (raw ++ [6, 136, 144, 150, 159, 224, 232, 238]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss1 : tailCan 3 (raw ++ [6, 136, 144, 150, 159, 232, 238, 248]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss2 : tailCan 3 (raw ++ [6, 136, 150, 159, 224, 232, 238, 246]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss3 : tailCan 3 (raw ++ [6, 136, 150, 159, 232, 238, 246, 248]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss4 : tailCan 3 (raw ++ [18, 132, 150, 160, 183, 200, 232, 250]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss5 : tailCan 3 (raw ++ [18, 132, 150, 160, 183, 232, 236, 250]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss6 : tailCan 3 (raw ++ [18, 150, 160, 183, 200, 222, 232, 250]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss7 : tailCan 3 (raw ++ [18, 150, 160, 183, 222, 232, 236, 250]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss8 : tailCan 3 (raw ++ [20, 130, 150, 168, 192, 215, 232, 252]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss9 : tailCan 3 (raw ++ [20, 130, 150, 192, 215, 232, 234, 252]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss10 : tailCan 3 (raw ++ [20, 150, 168, 190, 192, 215, 232, 252]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss11 : tailCan 3 (raw ++ [20, 150, 190, 192, 215, 232, 234, 252]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss12 : tailCan 3 (raw ++ [22, 128, 136, 150, 224, 232, 238, 254]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss13 : tailCan 3 (raw ++ [22, 128, 136, 150, 232, 238, 248, 254]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss14 : tailCan 3 (raw ++ [22, 128, 150, 160, 200, 232, 250, 254]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss15 : tailCan 3 (raw ++ [22, 128, 150, 160, 232, 236, 250, 254]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss16 : tailCan 3 (raw ++ [22, 128, 150, 168, 192, 232, 252, 254]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss17 : tailCan 3 (raw ++ [22, 128, 150, 192, 232, 234, 252, 254]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss18 : tailCan 3 (raw ++ [128, 136, 150, 151, 224, 232, 238, 254]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss19 : tailCan 3 (raw ++ [128, 136, 150, 151, 232, 238, 248, 254]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss20 : tailCan 3 (raw ++ [128, 150, 151, 160, 200, 232, 250, 254]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss21 : tailCan 3 (raw ++ [128, 150, 151, 160, 232, 236, 250, 254]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss22 : tailCan 3 (raw ++ [128, 150, 151, 168, 192, 232, 252, 254]) 27=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem miss23 : tailCan 3 (raw ++ [128, 150, 151, 192, 232, 234, 252, 254]) 27=false := by decide +kernel
theorem bank_suffix : ∀ b∈banks, ¬ Program 3 (raw++b) 27 := by
  intro b hb h
  have r := tail_sound h
  simp only [banks,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Bool.noConfusion ((miss0.symm).trans r) | exact Bool.noConfusion ((miss1.symm).trans r) | exact Bool.noConfusion ((miss2.symm).trans r) | exact Bool.noConfusion ((miss3.symm).trans r) | exact Bool.noConfusion ((miss4.symm).trans r) | exact Bool.noConfusion ((miss5.symm).trans r) | exact Bool.noConfusion ((miss6.symm).trans r) | exact Bool.noConfusion ((miss7.symm).trans r) | exact Bool.noConfusion ((miss8.symm).trans r) | exact Bool.noConfusion ((miss9.symm).trans r) | exact Bool.noConfusion ((miss10.symm).trans r) | exact Bool.noConfusion ((miss11.symm).trans r) | exact Bool.noConfusion ((miss12.symm).trans r) | exact Bool.noConfusion ((miss13.symm).trans r) | exact Bool.noConfusion ((miss14.symm).trans r) | exact Bool.noConfusion ((miss15.symm).trans r) | exact Bool.noConfusion ((miss16.symm).trans r) | exact Bool.noConfusion ((miss17.symm).trans r) | exact Bool.noConfusion ((miss18.symm).trans r) | exact Bool.noConfusion ((miss19.symm).trans r) | exact Bool.noConfusion ((miss20.symm).trans r) | exact Bool.noConfusion ((miss21.symm).trans r) | exact Bool.noConfusion ((miss22.symm).trans r) | exact Bool.noConfusion ((miss23.symm).trans r)
end PEqualNP.Outside.L_meta_9939_suffix
