import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33669
namespace Code
def header (n : Nat) := List.replicate n true ++ [false]

theorem header_split (a b : Nat) (xs ys : List Bool) (h : header a ++ xs = header b ++ ys) :
    a = b ∧ xs = ys := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa [header] using h
    | succ b => simp [header, List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [header, List.replicate_succ] at h
    | succ b =>
      have e : header a ++ xs = header b ++ ys := by
        simpa [header, List.replicate_succ] using h
      obtain ⟨rfl,rfl⟩ := ih b e
      exact ⟨rfl,rfl⟩

theorem cut {α : Type} (a b u v : List α) (hl : a.length = b.length)
    (h : a ++ u = b ++ v) : a = b ∧ u = v := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons a as ih =>
    cases b with
    | nil => simp at hl
    | cons b bs =>
      obtain ⟨e, er⟩ := List.cons.inj h
      obtain ⟨e',e''⟩ := ih bs (by simpa using hl) er
      exact ⟨by rw [e,e'], e''⟩

theorem banks_split {α β : Type} (f : α → List β) (sz : Nat) (hl : ∀ a, (f a).length = sz)
    (inj : Function.Injective f) (xs ys : List α) (u v : List β) (hn : xs.length = ys.length)
    (h : xs.flatMap f ++ u = ys.flatMap f ++ v) : xs = ys ∧ u = v := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hn
    | cons y ys =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨ef,er⟩ := cut _ _ _ _ ((hl x).trans (hl y).symm) h
      obtain ⟨ex,ev⟩ := ih ys (by simpa using hn) er
      exact ⟨by rw [inj ef,ex], ev⟩


def nr (k : Nat) (c : Bool) := if c then k+2 else k
def nc (k : Nat) (c : Bool) := if c then k+1 else k
abbrev Sample (k : Nat) (c : Bool) := (Fin (nr k c) → Bool) × (Fin (nc k c) → Bool)
def bank {k c} (r : Sample k c) := List.ofFn r.1 ++ List.ofFn r.2
def label {k c} (r : Sample k c × Bool) := bank r.1 ++ [r.2]
def entry {k} (r : List Bool × (Fin k × Fin k)) := header r.1.length ++ r.1 ++ header r.2.1.val ++ header r.2.2.val
structure Request where
  c : Bool
  k : Nat
  hard : List (Sample k c)
  soft : List (Sample k c × Bool)
  tree : List (List Bool × (Fin k × Fin k))

def encode (s : Request) := [s.c] ++ header s.k ++ header s.hard.length ++ s.hard.flatMap bank ++
  header s.soft.length ++ s.soft.flatMap label ++ header s.tree.length ++ s.tree.flatMap entry
theorem bank_inj (k c) : Function.Injective (@bank k c) := by
  intro x y h
  obtain ⟨l,r⟩ := cut _ _ _ _ (by simp) h
  exact Prod.ext (List.ofFn_inj.mp l) (List.ofFn_inj.mp r)
theorem label_inj (k c) : Function.Injective (@label k c) := by
  intro x y h
  obtain ⟨l,r⟩ := cut (bank x.1) (bank y.1) [x.2] [y.2] (by simp [bank]) h
  exact Prod.ext (bank_inj _ _ l) (List.cons.inj r).1
theorem entry_split {k} (x y : List Bool × (Fin k × Fin k)) (u v : List Bool)
    (eq : entry x++u=entry y++v) : x=y ∧ u=v := by
  simp only [entry,List.append_assoc] at eq
  obtain ⟨len,rest⟩ := header_split _ _ _ _ eq
  obtain ⟨keys,rest⟩ := cut _ _ _ _ len rest
  obtain ⟨left,rest⟩ := header_split _ _ _ _ rest
  obtain ⟨right,tail⟩ := header_split _ _ _ _ rest
  exact ⟨Prod.ext keys (Prod.ext (Fin.ext left) (Fin.ext right)),tail⟩
theorem entries_split {k} (xs ys : List (List Bool × (Fin k × Fin k))) (u v : List Bool)
    (length : xs.length=ys.length) (eq : xs.flatMap entry++u=ys.flatMap entry++v) :
    xs=ys ∧ u=v := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at length
    | cons y ys =>
      simp only [List.flatMap_cons,List.append_assoc] at eq
      obtain ⟨rfl,rest⟩ := entry_split x y _ _ eq
      obtain ⟨rfl,uv⟩ := ih ys (by simpa using length) rest
      exact ⟨rfl,uv⟩
theorem separate (s t : Request) (u v : List Bool) (h : encode s ++ u = encode t ++ v) :
    s=t ∧ u=v := by
  rcases s with ⟨c,k,H,S,T⟩
  rcases t with ⟨d,l,J,F,Y⟩
  simp only [encode,List.append_assoc,List.cons_append,List.nil_append,List.cons.injEq] at h
  obtain ⟨rfl,body⟩ := h
  obtain ⟨rfl,body⟩ := header_split k l _ _ body
  obtain ⟨len,body⟩ := header_split H.length J.length _ _ body
  obtain ⟨rfl,body⟩ := banks_split (@bank k c) (nr k c+nc k c)
    (fun z => by simp [bank]) (bank_inj k c) H J _ _ len body
  obtain ⟨len,body⟩ := header_split S.length F.length _ _ body
  obtain ⟨rfl,body⟩ := banks_split (@label k c) (nr k c+nc k c+1)
    (fun z => by simp [label,bank]) (label_inj k c) S F _ _ len body
  obtain ⟨len,body⟩ := header_split T.length Y.length _ _ body
  obtain ⟨rfl,uv⟩ := entries_split T Y u v len body
  exact ⟨rfl,uv⟩
noncomputable def joinOutputs (localOut : Request → List Bool) (xs : List Bool) : List Bool :=
  open Classical in if h : ∃ r, encode r=xs then localOut h.choose else []
theorem join_on (localOut : Request → List Bool) (s : Request) :
    joinOutputs localOut (encode s)=localOut s := by
  classical
  have h : ∃ r, encode r=encode s := ⟨s,rfl⟩
  have ob := (separate h.choose s [] [] (by simpa using h.choose_spec)).1
  simp [joinOutputs,h,ob]
end Code
end PEqualNP.Outside.L_meta_33669
