namespace Cas

abbrev Version := Nat

inductive Cond
  | any
  | absent
  | version (v : Version)
  deriving Repr, DecidableEq

def Cond.holds : Cond → Option Version → Bool
  | .any,       _     => true
  | .absent,    cur   => cur.isNone
  | .version v, cur   => cur == some v

structure Store (κ ν : Type) where
  entries : List (κ × Version × ν) := []
  next    : Version := 1
  deriving Repr

inductive Outcome (α : Type)
  | ok (a : α)
  | rejected
  deriving Repr

variable {κ ν : Type} [BEq κ]

def Store.init : Store κ ν := {}

def Store.get (s : Store κ ν) (k : κ) : Option (ν × Version) :=
  (s.entries.find? (·.1 == k)).map fun e => (e.2.2, e.2.1)

def Store.version? (s : Store κ ν) (k : κ) : Option Version :=
  (s.get k).map (·.2)

def Store.value? (s : Store κ ν) (k : κ) : Option ν :=
  (s.get k).map (·.1)

def Store.put (s : Store κ ν) (k : κ) (v : ν) (c : Cond) : Outcome (Store κ ν × Version) :=
  if c.holds (s.version? k) then
    .ok ({ entries := (k, s.next, v) :: s.entries.filter (fun e => !(e.1 == k)),
           next    := s.next + 1 },
         s.next)
  else
    .rejected

def Store.del (s : Store κ ν) (k : κ) (c : Cond) : Outcome (Store κ ν) :=
  if c.holds (s.version? k) then
    .ok { s with entries := s.entries.filter (fun e => !(e.1 == k)) }
  else
    .rejected

def Store.keys (s : Store κ ν) (p : κ → Bool) : List κ :=
  (s.entries.map (·.1)).filter p

theorem put_version_accepted (s : Store κ ν) (k : κ) (v : ν) (ver : Version)
    (s' : Store κ ν) (ver' : Version)
    (h : s.put k v (.version ver) = .ok (s', ver')) :
    s.version? k = some ver := by
  unfold Store.put at h
  split at h
  · rename_i hc
    simpa [Cond.holds] using hc
  · cases h

theorem put_absent_accepted (s : Store κ ν) (k : κ) (v : ν)
    (s' : Store κ ν) (ver' : Version)
    (h : s.put k v .absent = .ok (s', ver')) :
    s.version? k = none := by
  unfold Store.put at h
  split at h
  · rename_i hc
    simpa [Cond.holds, Option.isNone_iff_eq_none] using hc
  · cases h

variable [LawfulBEq κ]

theorem get_put_same (s : Store κ ν) (k : κ) (v : ν) (c : Cond)
    (s' : Store κ ν) (ver' : Version)
    (h : s.put k v c = .ok (s', ver')) :
    s'.get k = some (v, ver') := by
  unfold Store.put at h
  split at h
  · cases h
    simp [Store.get, List.find?]
  · cases h

theorem find?_filter_other (l : List (κ × Version × ν)) (k k' : κ)
    (hk : k' ≠ k) :
    (l.filter (fun e => !(e.1 == k))).find? (·.1 == k') = l.find? (·.1 == k') := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    simp only [List.filter_cons]
    by_cases h1 : e.1 = k'
    · subst h1
      simp [hk]
    · split
      · simp [h1, ih]
      · simp [h1, ih]

theorem get_put_other (s : Store κ ν) (k k' : κ) (v : ν) (c : Cond)
    (s' : Store κ ν) (ver' : Version)
    (h : s.put k v c = .ok (s', ver')) (hk : k' ≠ k) :
    s'.get k' = s.get k' := by
  unfold Store.put at h
  split at h
  · cases h
    have h1 : ((k, s.next, v).1 == k') = false := by simpa using Ne.symm hk
    simp only [Store.get, List.find?_cons, h1]
    rw [find?_filter_other _ _ _ hk]
  · cases h

theorem get_del_same (s : Store κ ν) (k : κ) (c : Cond) (s' : Store κ ν)
    (h : s.del k c = .ok s') : s'.get k = none := by
  unfold Store.del at h
  split at h
  · cases h
    simp only [Store.get]
    have : (s.entries.filter (fun e => !(e.1 == k))).find? (·.1 == k) = none := by
      rw [List.find?_eq_none]
      intro e he
      have := (List.mem_filter.mp he).2
      simpa using this
    simp [this]
  · cases h

theorem get_del_other (s : Store κ ν) (k k' : κ) (c : Cond) (s' : Store κ ν)
    (h : s.del k c = .ok s') (hk : k' ≠ k) :
    s'.get k' = s.get k' := by
  unfold Store.del at h
  split at h
  · cases h
    simp only [Store.get]
    rw [find?_filter_other _ _ _ hk]
  · cases h

omit [LawfulBEq κ] in

theorem put_version_fresh (s : Store κ ν) (k : κ) (v : ν) (c : Cond)
    (s' : Store κ ν) (ver' : Version)
    (h : s.put k v c = .ok (s', ver'))
    (hinv : ∀ e ∈ s.entries, e.2.1 < s.next) :
    (∀ e ∈ s.entries, e.2.1 < ver') ∧ (∀ e ∈ s'.entries, e.2.1 < s'.next) := by
  unfold Store.put at h
  split at h
  · cases h
    refine ⟨hinv, ?_⟩
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · simp
    · exact Nat.lt_succ_of_lt (hinv e (List.mem_filter.mp he).1)
  · cases h

omit [LawfulBEq κ] in

theorem put_rejected_iff (s : Store κ ν) (k : κ) (v : ν) (c : Cond) :
    s.put k v c = .rejected ↔ c.holds (s.version? k) = false := by
  unfold Store.put
  split <;> simp_all

end Cas
