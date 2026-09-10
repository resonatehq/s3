/-!  # The CAS machine — a versioned object store with conditional writes

The abstract machine the implementation runs on. Not the protocol's
machine: this one knows nothing about promises or tasks. It knows
KEYS, VALUES and VERSIONS, and it knows how to refuse a write.

This is S3 with everything but the load-bearing part removed. An object
store holds, per key, a value and a version (S3 calls the version an
ETag). Three operations:

  `get k`          the value at `k` and its version, or nothing;
  `put k v c`      write `v` at `k` — but only if the condition `c` holds
                   of the version currently there;
  `del k c`        remove `k` — again only under `c`.

The condition is the whole point. `Cond.any` is a blind write.
`Cond.absent` is S3's `If-None-Match: *` — create only if nothing is
there. `Cond.version v` is `If-Match: <etag>` — replace only if the
object is still at the version I read. When the condition does not
hold the write is REJECTED: the store is unchanged and the caller is
told so. That refusal is what lets a machine with no transactions and
no locks commit a read-modify-write atomically: read at version `v`,
decide, write under `Cond.version v`. If anyone wrote in between, the
version moved and the write is refused — and the decision, made
against state that is now stale, is thrown away rather than applied.

VERSIONS ARE FRESH. A version is drawn from a store-wide counter that
never repeats, so a key that is written, deleted, and written again
never returns to a version it once had. Without this a reader could
see version `v`, miss two writes that took the key away and back to
`v`, and CAS against `v` successfully — the ABA problem. S3's ETags are
content hashes, which have the same weakness for equal contents; the
store here is strictly stronger, and `put_version_fresh` says so.

THE STORE IS A FUNCTION OF ITS HISTORY, and nothing else. `get` reads
the list; `put` and `del` are the only writers; both are total and
both are decidable. Everything in `impl/` that touches the bucket goes
through these three operations, so a property proved here is a
property of the whole implementation's use of the bucket. -/

namespace Cas

/-- An object's version, as the store reports it. -/
abbrev Version := Nat

/-- The precondition a write is made under. -/
inductive Cond
  | any
  | absent
  | version (v : Version)
  deriving Repr, DecidableEq

/-- What the condition asks of the version currently stored (`none` when
    nothing is stored at the key). -/
def Cond.holds : Cond → Option Version → Bool
  | .any,       _     => true
  | .absent,    cur   => cur.isNone
  | .version v, cur   => cur == some v

/-- The store: a list of entries, one per key, and the next version to
    hand out. `next` is what makes versions fresh. -/
structure Store (κ ν : Type) where
  entries : List (κ × Version × ν) := []
  next    : Version := 1
  deriving Repr

/-- A write's verdict. `rejected` carries nothing because a rejected
    write changes nothing — the store the caller holds is still the
    store. -/
inductive Outcome (α : Type)
  | ok (a : α)
  | rejected
  deriving Repr

variable {κ ν : Type} [BEq κ]

def Store.init : Store κ ν := {}

/-- Read an object and its version. -/
def Store.get (s : Store κ ν) (k : κ) : Option (ν × Version) :=
  (s.entries.find? (·.1 == k)).map fun e => (e.2.2, e.2.1)

/-- The version at `k`, or `none` when the key is absent. -/
def Store.version? (s : Store κ ν) (k : κ) : Option Version :=
  (s.get k).map (·.2)

/-- The value at `k`, without its version. -/
def Store.value? (s : Store κ ν) (k : κ) : Option ν :=
  (s.get k).map (·.1)

/-- Write `v` at `k` under `c`. The new version is returned so the writer
    can keep chaining conditional writes without re-reading. -/
def Store.put (s : Store κ ν) (k : κ) (v : ν) (c : Cond) : Outcome (Store κ ν × Version) :=
  if c.holds (s.version? k) then
    .ok ({ entries := (k, s.next, v) :: s.entries.filter (fun e => !(e.1 == k)),
           next    := s.next + 1 },
         s.next)
  else
    .rejected

/-- Remove `k` under `c`. Removing what is not there succeeds under
    `Cond.any` — the key carries the whole meaning of a timer object,
    so a second delete has nothing to get wrong. -/
def Store.del (s : Store κ ν) (k : κ) (c : Cond) : Outcome (Store κ ν) :=
  if c.holds (s.version? k) then
    .ok { s with entries := s.entries.filter (fun e => !(e.1 == k)) }
  else
    .rejected

/-- Every key satisfying `p`. The timer sweep lists a prefix; here the
    prefix is a predicate on keys. -/
def Store.keys (s : Store κ ν) (p : κ → Bool) : List κ :=
  (s.entries.map (·.1)).filter p

/-! ## What the machine guarantees

Four facts, each the semantic content of one S3 feature. Everything
the refinement proof needs from the bucket is here. -/

/-- An accepted `put` under `Cond.version v` was made against the
    version the key really held. This is the CAS: an accepted write
    proves the read it was decided from is the current state. -/
theorem put_version_accepted (s : Store κ ν) (k : κ) (v : ν) (ver : Version)
    (s' : Store κ ν) (ver' : Version)
    (h : s.put k v (.version ver) = .ok (s', ver')) :
    s.version? k = some ver := by
  unfold Store.put at h
  split at h
  · rename_i hc
    simpa [Cond.holds] using hc
  · cases h

/-- An accepted `put` under `Cond.absent` was made against an empty key. -/
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

/-- After an accepted `put`, the key holds the value written, at the
    version returned. -/
theorem get_put_same (s : Store κ ν) (k : κ) (v : ν) (c : Cond)
    (s' : Store κ ν) (ver' : Version)
    (h : s.put k v c = .ok (s', ver')) :
    s'.get k = some (v, ver') := by
  unfold Store.put at h
  split at h
  · cases h
    simp [Store.get, List.find?]
  · cases h

/-- Filtering a key out leaves lookups of every other key alone. -/
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

/-- After an accepted `put` at `k`, every other key is untouched. -/
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

/-- After an accepted `del` at `k`, the key is gone. -/
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

/-- After an accepted `del` at `k`, every other key is untouched. -/
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
/-- The version handed out by a `put` is strictly above every version
    the store held — so no version ever recurs. This is the fact that
    rules out ABA. -/
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
/-- A rejected write is exactly a write whose condition failed. -/
theorem put_rejected_iff (s : Store κ ν) (k : κ) (v : ν) (c : Cond) :
    s.put k v c = .rejected ↔ c.holds (s.version? k) = false := by
  unfold Store.put
  split <;> simp_all

end Cas
