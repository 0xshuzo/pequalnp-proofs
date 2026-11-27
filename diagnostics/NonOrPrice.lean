import PEqualNP.Outside.L_meta_9752

namespace PEqualNP.Outside.L_meta_9745.Roots
open PEqualNP.Outside.L_meta_9752.Engine
abbrev X := Fin 14 → Bool
def goal (x : Fin 14 → Bool) : Bool := (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) || (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) || (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)
def raw (i : Fin 14) : Wire X := fun x => x i
def ports : List (Wire X) := List.ofFn raw
def pin (i : Fin 14) (x : X) : X := fun j => if j=i then false else x j
def trial (i j t : Fin 14) (c b : Bool) : X :=
  fun v => if v=i then b else if v=j then c else decide (v=t)
def gate (d : Fin 4) (i j : Fin 14) : Wire X := comb d.val (raw i) (raw j)
set_option maxHeartbeats 0
set_option maxRecDepth 16000

theorem rows : ∀ i j : Fin 14, ∀ d : Fin 4, i≠j →
    ∃ c : Bool, ∃ t : Fin 14,
      goal (trial i j t c false) ≠ goal (trial i j t c true) ∧
      gate d i j (trial i j t c false) = gate d i j (trial i j t c true) := by decide +kernel

theorem runs_agree {R : Type} {u : Bool} {p n : R} {v : Wire R} {k ws}
    (h : Run u v k ws) (ok : ∀ w∈ws, w p=w n) : v p=v n := by
  induction h using Run.ind with
  | stop => exact ok v (by simp)
  | perm perm h ih => exact ih (fun w m => ok w (perm.mem_iff.mp m))
  | @two k a b rest d hd ka kb h ih =>
    apply ih
    have aa := ok a (by simp)
    have bb := ok b (by simp)
    intro w hw
    rcases List.mem_cons.mp hw with rfl | z
    · rcases allowed_four hd with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩ <;>
        simp [comb,combine,inv,aa,bb]
    · rcases mem_kept z with rfl|z
      · exact aa
      · rcases mem_kept z with rfl|z
        · exact bb
        · exact ok _ (by simp [z])

theorem operand_live (i j : Fin 14) (d : Fin 4) (ne : i≠j) {k ws}
    (h : Run true goal k ws) (sub : ∀ w∈ws, w∈gate d i j::ports) : raw i∈ws := by
  classical
  by_contra gone
  obtain ⟨c,t,hh,gg⟩ := rows i j d ne
  apply hh
  apply runs_agree h
  intro w hw
  rcases List.mem_cons.mp (sub w hw) with rfl|hr
  · exact gg
  · obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hr
    have vn : v≠i := by rintro rfl;exact gone hw
    simp [raw,trial,vn]

theorem cost_positive {R : Type} {xs : List (Wire R)} {w : Wire R}
    (hm : w∈xs) (hc : Constant w) : 1 ≤ mass xs := by
  classical
  induction xs with
  | nil => simp at hm
  | cons a xs ih =>
    rw [mass_cons]
    rcases List.mem_cons.mp hm with rfl|hi
    · simp [cost,hc]
    · have := ih hi
      omega


theorem two_sources {R S : Type} (f : Wire R → Wire S) {a b : Wire R}
    (ne : a ≠ b) (ca : Constant (f a)) (cb : Constant (f b))
    (ws : List (Wire R)) (ha : a ∈ ws) (hb : b ∈ ws) : 2 ≤ mass (ws.map f) := by
  classical
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.map_cons, mass_cons]
    rcases List.mem_cons.mp ha with ha|ha
    · subst x
      have hb' : b ∈ xs := (List.mem_cons.mp hb).resolve_left ne.symm
      have t := cost_positive (List.mem_map_of_mem (f:=f) hb') cb
      have e : cost (f a) = 1 := by simp [cost,ca]
      omega
    · rcases List.mem_cons.mp hb with hb|hb
      · subst x
        have t := cost_positive (List.mem_map_of_mem (f:=f) ha) ca
        have e : cost (f b) = 1 := by simp [cost,cb]
        omega
      · have t := ih ha hb
        omega

theorem nonOrPrice {i j : Fin 14} (ne : i ≠ j) (d : Fin 4) (type : d=0 ∨ d=2)
    {k L ws} (h : Run true goal k ws) (inputs : ∀ w ∈ ws, w ∈ gate d i j :: ports)
    (nc : ¬ Constant goal) (pc : ¬ Constant (restrictRows (pin i) goal))
    (whole : ∀ q bs, Reach true ports q bs → Available true bs goal → L+2 ≤ q)
    (face : ∀ q bs, Reach true ports q bs → Available true bs (restrictRows (pin i) goal) → L ≤ q) :
    L+3 ≤ k+1 := by
  classical
  by_cases used : gate d i j ∈ ws
  · let r := restrictRows (pin i)
    have ca : Constant (r (raw i)) := ⟨false,by funext x; simp [r,restrictRows,raw,pin]⟩
    have cb : Constant (r (gate d i j)) := by
      rcases type with rfl|rfl <;>
        exact ⟨false,by funext x;simp [r,restrictRows,gate,comb,combine,raw,inv,pin]⟩
    have diff : raw i ≠ gate d i j := by
      obtain ⟨c,t,_,eq⟩ := rows i j d ne
      intro same
      rw [←same] at eq
      simp [raw,trial] at eq
    have live := operand_live i j d ne h inputs
    have two := two_sources r diff ca cb ws live used
    have supply' : supply true ports (ws.map r) := by
      intro w hw
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
      rcases List.mem_cons.mp (inputs a ha) with rfl|port
      · exact Or.inr (Or.inl cb)
      · obtain ⟨u,rfl⟩ := List.mem_ofFn.mp port
        by_cases eq : u=i
        · subst u; exact Or.inr (Or.inl ca)
        · have he : r (raw u) = raw u := by funext x; simp [r,restrictRows,raw,pin,eq]
          rw [he]
          exact Or.inl (List.mem_ofFn.mpr ⟨u,rfl⟩)
    have bound := projected_bound (pin i) h pc (p:=0) Reach.start supply' face
    change L + mass (ws.map r) ≤ 0+k at bound
    omega
  · have s : supply true ports ws := by
      intro w hw
      rcases List.mem_cons.mp (inputs w hw) with rfl|hr
      · exact (used hw).elim
      · exact Or.inl hr
    obtain ⟨q,bs,hq,hout,hl⟩ := contraction nc h ports (Reach.start (u:=true)) s
    have p := whole q bs hq hout
    omega

end PEqualNP.Outside.L_meta_9745.Roots
