import PEqualNP.Defs
namespace L9736Dominance
set_option maxRecDepth 32768
set_option maxHeartbeats 0
section Order
variable {R : Type} (target : R → Bool)
def better (v w : R → Bool) := ∀ r, v r = target r → w r = target r
def gate (d : Bool) (u v : R → Bool) (r : R) := if d then u r || v r else u r && v r
theorem better_refl (u : R → Bool) : better target u u := fun _ h => h
theorem better_trans {u v w : R → Bool} (uv : better target u v) (vw : better target v w) :
    better target u w := fun r h => vw r (uv r h)
theorem binary (d : Bool) {u v u' v' : R → Bool} (hu : better target u u') (hv : better target v v') :
    better target (gate d u v) (gate d u' v') := by
  have truth : ∀ t a a' b b' i : Bool, (a=t → a'=t) → (b=t → b'=t) →
      (if i then a || b else a && b)=t → (if i then a' || b' else a' && b')=t := by decide
  exact fun r => truth (target r) (u r) (u' r) (v r) (v' r) d (hu r) (hv r)

inductive Can : List (R → Bool) → Nat → Prop
  | done {b : List (R → Bool)} (h : target ∈ b) : Can b 0
  | step {b : List (R → Bool)} {u v : R → Bool} {k : Nat} (d : Bool)
      (hu : u∈b) (hv : v∈b) (next : Can (gate d u v :: b) k) : Can b (k+1)

def improves (b b' : List (R → Bool)) := ∀ v∈b, ∃ w∈b', better target v w

theorem lift {b : List (R → Bool)} {k : Nat} (p : Can target b k) :
    ∀ b', improves target b b' → Can target b' k := by
  induction p with
  | done h =>
    intro b' imp
    obtain ⟨w,mem,hw⟩ := imp _ h
    have eq : w=target := funext fun r => hw r rfl
    exact .done (eq ▸ mem)
  | step d hu hv _ ih =>
    intro b' imp
    obtain ⟨u',memu,au⟩ := imp _ hu
    obtain ⟨v',memv,av⟩ := imp _ hv
    refine .step d memu memv (ih _ ?_)
    intro w mem
    rcases List.mem_cons.mp mem with eq | hold
    · subst w
      exact ⟨_,List.mem_cons_self,binary target d au av⟩
    · obtain ⟨z,hz,bz⟩ := imp _ hold
      exact ⟨z,List.mem_cons_of_mem _ hz,bz⟩

theorem erase {b : List (R → Bool)} {w z : R → Bool} {k : Nat} (mem : z∈b)
    (dom : better target w z) (tail : Can target (w::b) k) : Can target b k := by
  apply lift target tail b
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact ⟨z,mem,dom⟩
  · exact ⟨y,hy,better_refl target y⟩
end Order
abbrev V := Fin 10
def edges : List (Nat × Nat) := [(0, 4), (0, 5), (1, 2), (1, 6), (2, 3), (2, 7), (3, 4), (3, 8), (4, 9), (5, 7), (5, 8), (6, 8), (6, 9), (7, 9)]
def adj (a b : V) := (a.val,b.val)∈edges ∨ (b.val,a.val)∈edges
instance (a b : V) : Decidable (adj a b) := by unfold adj; infer_instance
def perm : Fin 8 → V → V := ![![0,1,2,3,4,5,6,7,8,9],![0,1,2,7,5,4,6,3,9,8],![0,1,6,8,5,4,2,9,3,7],![0,1,6,9,4,5,2,8,7,3],![1,0,4,3,2,6,5,9,8,7],![1,0,4,9,6,2,5,3,7,8],![1,0,5,7,2,6,4,8,9,3],![1,0,5,8,6,2,4,7,3,9]]
def reps : Fin 13 → Bool × V × V := ![(true,0,1),(true,0,2),(true,0,3),(false,0,4),(true,0,4),(false,2,3),(true,2,3),(true,2,4),(true,2,6),(true,2,8),(true,3,7),(false,3,8),(true,3,8)]
theorem automorphisms : ∀ j a b, adj (perm j a) (perm j b) ↔ adj a b := by decide +kernel
theorem permutations : ∀ j, Function.Injective (perm j) := by
  unfold Function.Injective
  decide +kernel
theorem cover : ∀ (d : Bool) (a b : V), a≠b → (d=true ∨ adj a b) →
    ∃ (p : Fin 8) (k : Fin 13), (reps k).1=d ∧
     (((reps k).2.1=perm p a ∧ (reps k).2.2=perm p b) ∨
      ((reps k).2.1=perm p b ∧ (reps k).2.2=perm p a)) := by decide +kernel
end L9736Dominance
