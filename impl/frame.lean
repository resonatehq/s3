import impl.system

/-!  # The frame — a step of one origin reads and writes one origin

The protocol's handlers are written against the WHOLE state; the
implementation runs them against ONE origin's document. This file is
the proof that the difference is invisible: for a step about origin
`o`, the handler's answer and its writes depend only on the objects of
origin `o`, and every object it writes is of origin `o`.

Two predicates on a computation `act : H α`, and one lemma per handler.

  `Cong o act`    two environments that agree on every object of origin
                  `o` (and on the discipline and the configuration) get
                  the same answer and the same effects. This is what
                  lets the implementation decide from one document.

  `LocAt o act e` every effect `act` emits at `e` is a write at an id of
                  origin `o`, or a message. This is what lets the
                  implementation write back one document.

Both are proved by walking the handler's structure: `bind` composes,
`ite` splits on its condition — and the condition is exactly where the
same-origin doors hand the proof the fact it needs, that the second id
a callback or a fence names shares the first's origin — and the leaves
are the reads (`readObject` and its variants) and the writes
(`setPromise`, `setTask`, `setMessage`).

Nothing here is specific to S3. It is a fact about the specification —
that its single-origin doors deliver a single-origin frame — and it is
stated here rather than in `spec/` because this is where it is used. -/

namespace Frame

open ServerModel AbstractModel
open Equivalence (Request Response)
open Abstraction (InternalStep)


/-! ## How `H` computes -/

theorem bind_apply (x : H α) (f : α → H β) (e : Env) :
    (x >>= f) e = ((f (x e).1 e).1, (x e).2 ++ (f (x e).1 e).2) := rfl

theorem pure_apply (a : α) (e : Env) : (pure a : H α) e = (a, []) := rfl

theorem pure_bind (a : α) (f : α → H β) : ((pure a : H α) >>= f) = f a := rfl

theorem map_eq (f : α → β) (x : H α) : (f <$> x) = x >>= (fun a => pure (f a)) := rfl

theorem ite_apply {c : Prop} [Decidable c] (a b : H α) (e : Env) :
    (if c then a else b) e = if c then a e else b e := by
  split <;> rfl

theorem emit_apply (f : Effect) (e : Env) : emit f e = ((), [f]) := rfl

theorem ask_apply (e : Env) : ask e = (e, []) := rfl

theorem getObject_apply (id : Ident) (e : Env) :
    getObject id e = (e.state.objects.find? (·.id == id), []) := rfl

theorem withMat_apply (b : Bool) (act : H α) (e : Env) :
    withMat b act e = act { e with mat := b } := rfl

/-! ## Environments that agree on one origin -/

structure EnvEquiv (o : String) (e e' : Env) : Prop where
  mat    : e.mat = e'.mat
  config : e.config = e'.config
  find   : ∀ id : Ident, id.origin = o →
             e.state.objects.find? (·.id == id) = e'.state.objects.find? (·.id == id)

theorem EnvEquiv.withMat {o : String} {e e' : Env} (h : EnvEquiv o e e') (b : Bool) :
    EnvEquiv o { e with mat := b } { e' with mat := b } :=
  ⟨rfl, h.config, h.find⟩

/-! ## Congruence -/

def Cong (o : String) (act : H α) : Prop :=
  ∀ e e', EnvEquiv o e e' → act e = act e'

theorem Cong.pure {o : String} (a : α) : Cong o (pure a : H α) := fun _ _ _ => rfl

theorem Cong.emit {o : String} (f : Effect) : Cong o (emit f) := fun _ _ _ => rfl

theorem Cong.setPromise {o : String} (id : Ident) (p : PromiseObject) :
    Cong o (setPromise id p) := fun _ _ _ => rfl

theorem Cong.setTask {o : String} (id : Ident) (t : TaskObject) :
    Cong o (setTask id t) := fun _ _ _ => rfl

theorem Cong.setMessage {o : String} (a : String) (m : Message) :
    Cong o (setMessage a m) := fun _ _ _ => rfl

theorem Cong.bind {o : String} {x : H α} {f : α → H β}
    (hx : Cong o x) (hf : ∀ a, Cong o (f a)) : Cong o (x >>= f) := by
  intro e e' h
  rw [bind_apply, bind_apply, hx e e' h, hf _ e e' h]

theorem Cong.ite {o : String} {c : Prop} [Decidable c] {a b : H α}
    (ha : c → Cong o a) (hb : ¬c → Cong o b) : Cong o (if c then a else b) := by
  intro e e' h
  split
  · exact ha ‹_› e e' h
  · exact hb ‹_› e e' h

theorem Cong.ite' {o : String} {c : Prop} [Decidable c] {a b : H α}
    (ha : Cong o a) (hb : Cong o b) : Cong o (if c then a else b) :=
  Cong.ite (fun _ => ha) (fun _ => hb)

theorem Cong.withMat {o : String} {act : H α} (h : Cong o act) (b : Bool) :
    Cong o (withMat b act) := fun _ _ he => h _ _ (he.withMat b)

theorem Cong.map {o : String} {x : H α} (f : α → β) (h : Cong o x) : Cong o (f <$> x) := by
  rw [map_eq]; exact Cong.bind h (fun _ => Cong.pure _)

theorem Cong.getObject {o : String} {id : Ident} (hid : id.origin = o) :
    Cong o (getObject id) := by
  intro e e' h
  rw [getObject_apply, getObject_apply, h.find id hid]

/-- `materialise` only writes; it reads nothing. -/
theorem Cong.materialise {o : String} (id : Ident) (ob ob' : Object) :
    Cong o (materialise id ob ob') := by
  unfold AbstractModel.materialise
  apply Cong.bind
  · exact Cong.ite' (Cong.setPromise _ _) (Cong.pure _)
  · intro _
    cases ob.task <;> cases ob'.task
    all_goals first
      | exact Cong.pure _
      | exact Cong.ite' (Cong.setTask _ _) (Cong.pure _)

theorem Cong.readObject {o : String} {id : Ident} (hid : id.origin = o) (now : Nat) :
    Cong o (readObject id now) := by
  intro e e' h
  unfold AbstractModel.readObject
  rw [bind_apply, bind_apply, Cong.getObject hid e e' h]
  generalize (AbstractModel.getObject id e') = r
  rcases r with ⟨a, w⟩
  cases a with
  | none => rfl
  | some ob =>
    simp only [bind_apply, ask_apply, h.mat]
    split
    · simp only [bind_apply, pure_apply, Cong.materialise id ob (ob.project now) e e' h]
    · rfl

theorem Cong.readTaskObject {o : String} {id : Ident} (hid : id.origin = o) (now : Nat) :
    Cong o (readTaskObject id now) := by
  intro e e' h
  unfold AbstractModel.readTaskObject
  rw [bind_apply, bind_apply, Cong.getObject hid e e' h]
  generalize (AbstractModel.getObject id e') = r
  rcases r with ⟨a, w⟩
  cases a with
  | none => rfl
  | some ob =>
    simp only
    split
    · rw [Cong.readObject hid now e e' h]
    · rfl

theorem Cong.touchObject {o : String} {id : Ident} (hid : id.origin = o) (now : Nat) :
    Cong o (touchObject id now) := (Cong.readObject hid now).withMat true

theorem Cong.viewObject {o : String} {id : Ident} (hid : id.origin = o) (now : Nat) :
    Cong o (viewObject id now) := (Cong.readObject hid now).withMat false

theorem Cong.touchTaskObject {o : String} {id : Ident} (hid : id.origin = o) (now : Nat) :
    Cong o (touchTaskObject id now) := (Cong.readTaskObject hid now).withMat true

theorem Cong.viewTaskObject {o : String} {id : Ident} (hid : id.origin = o) (now : Nat) :
    Cong o (viewTaskObject id now) := (Cong.readTaskObject hid now).withMat false

/-- `createPromise` only writes. -/
theorem Cong.createPromise {o : String} (req : PromiseCreateReq) (now : Nat) :
    Cong o (createPromise req now) := by
  unfold AbstractModel.createPromise
  apply Cong.ite'
  · apply Cong.bind (Cong.setPromise _ _)
    intro _
    apply Cong.ite'
    · exact Cong.bind (Cong.setTask _ _) (fun _ => Cong.pure _)
    · exact Cong.pure _
  · apply Cong.bind (Cong.setPromise _ _)
    intro _
    apply Cong.ite'
    · exact Cong.bind (Cong.setTask _ _) (fun _ => Cong.pure _)
    · exact Cong.pure _

/-! ## Locality of effects -/

/-- A write at an id of origin `o`, or a message. Schedules are outside
    this implementation, so a schedule write is never local. -/
def Effect.Local (o : String) : Effect → Prop
  | .setPromise id _  => id.origin = o
  | .setTask id _     => id.origin = o
  | .setMessage _ _   => True
  | .setSchedule _    => False
  | .delSchedule _    => False

def LocAt (o : String) (act : H α) (e : Env) : Prop :=
  ∀ f ∈ (act e).2, Effect.Local o f

theorem LocAt.pure {o : String} (a : α) (e : Env) : LocAt o (pure a : H α) e := by
  intro f hf; simp [pure_apply] at hf

theorem LocAt.setPromise {o : String} {id : Ident} (hid : id.origin = o) (p : PromiseObject)
    (e : Env) : LocAt o (setPromise id p) e := by
  intro f hf
  simp only [AbstractModel.setPromise, emit_apply, List.mem_singleton] at hf
  subst hf; exact hid

theorem LocAt.setTask {o : String} {id : Ident} (hid : id.origin = o) (t : TaskObject)
    (e : Env) : LocAt o (setTask id t) e := by
  intro f hf
  simp only [AbstractModel.setTask, emit_apply, List.mem_singleton] at hf
  subst hf; exact hid

theorem LocAt.setMessage {o : String} (a : String) (m : Message) (e : Env) :
    LocAt o (setMessage a m) e := by
  intro f hf
  simp only [AbstractModel.setMessage, emit_apply, List.mem_singleton] at hf
  subst hf; trivial

theorem LocAt.bind {o : String} {x : H α} {f : α → H β} {e : Env}
    (hx : LocAt o x e) (hf : LocAt o (f (x e).1) e) : LocAt o (x >>= f) e := by
  intro g hg
  rw [bind_apply] at hg
  simp only [List.mem_append] at hg
  rcases hg with hg | hg
  · exact hx g hg
  · exact hf g hg

theorem LocAt.ite {o : String} {c : Prop} [Decidable c] {a b : H α} {e : Env}
    (ha : c → LocAt o a e) (hb : ¬c → LocAt o b e) : LocAt o (if c then a else b) e := by
  intro g hg
  rw [ite_apply] at hg
  split at hg
  · exact ha ‹_› g hg
  · exact hb ‹_› g hg

theorem LocAt.ite' {o : String} {c : Prop} [Decidable c] {a b : H α} {e : Env}
    (ha : LocAt o a e) (hb : LocAt o b e) : LocAt o (if c then a else b) e :=
  LocAt.ite (fun _ => ha) (fun _ => hb)

theorem LocAt.withMat {o : String} {act : H α} {e : Env} (b : Bool)
    (h : LocAt o act { e with mat := b }) : LocAt o (withMat b act) e := h

theorem LocAt.map {o : String} {x : H α} {e : Env} (f : α → β) (h : LocAt o x e) :
    LocAt o (f <$> x) e := by
  rw [map_eq]; exact LocAt.bind h (LocAt.pure _ _)

theorem LocAt.getObject {o : String} (id : Ident) (e : Env) : LocAt o (getObject id) e := by
  intro f hf; simp [getObject_apply] at hf

/-! ## What a read returns

The object a read finds is at the id asked for — `find?` says so — and
projection does not move the id. The locality proofs need this: a
handler writes back `ob.id`, and `ob.id` is the request's id. -/

theorem getObject_id {id : Ident} {e : Env} {ob : Object}
    (h : (getObject id e).1 = some ob) : ob.id = id := by
  rw [getObject_apply] at h
  have := List.find?_some h
  simpa using this

theorem project_id (ob : Object) (now : Nat) : (ob.project now).id = ob.id := rfl

theorem readObject_apply (id : Ident) (now : Nat) (e : Env) :
    readObject id now e =
      match (getObject id e).1 with
      | none    => (none, [])
      | some ob =>
          if e.mat = true
          then (some (ob.project now), (materialise id ob (ob.project now) e).2)
          else (some (ob.project now), []) := by
  unfold AbstractModel.readObject
  rw [bind_apply, getObject_apply]
  generalize e.state.objects.find? (·.id == id) = r
  cases r with
  | none => rfl
  | some ob =>
    simp only [bind_apply, ask_apply]
    split <;> (simp only [bind_apply, pure_apply, List.nil_append, List.append_nil]; try rfl)

theorem readObject_id {id : Ident} {now : Nat} {e : Env} {ob : Object}
    (h : (readObject id now e).1 = some ob) : ob.id = id := by
  rw [readObject_apply] at h
  revert h
  generalize hg : (AbstractModel.getObject id e).1 = r
  cases r with
  | none => intro h; cases h
  | some ob' =>
    intro h
    have hid := getObject_id hg
    try dsimp only at h
    split at h
    · have h' : some (ob'.project now) = some ob := h
      cases h'; exact hid
    · have h' : some (ob'.project now) = some ob := h
      cases h'; exact hid

theorem readTaskObject_apply (id : Ident) (now : Nat) (e : Env) :
    readTaskObject id now e =
      match (getObject id e).1 with
      | none    => (none, [])
      | some ob => if ob.task.isSome then readObject id now e else (none, []) := by
  unfold AbstractModel.readTaskObject
  rw [bind_apply, getObject_apply]
  generalize e.state.objects.find? (·.id == id) = r
  cases r with
  | none => rfl
  | some ob =>
    simp only
    split <;> rfl

theorem readTaskObject_id {id : Ident} {now : Nat} {e : Env} {ob : Object}
    (h : (readTaskObject id now e).1 = some ob) : ob.id = id := by
  rw [readTaskObject_apply] at h
  revert h
  generalize hg : (AbstractModel.getObject id e).1 = r
  cases r with
  | none => intro h; cases h
  | some ob' =>
    intro h
    try dsimp only at h
    split at h
    · exact readObject_id h
    · cases h

theorem LocAt.materialise {o : String} {id : Ident} (hid : id.origin = o) (ob ob' : Object)
    (e : Env) : LocAt o (materialise id ob ob') e := by
  unfold AbstractModel.materialise
  apply LocAt.bind
  · exact LocAt.ite' (LocAt.setPromise hid _ _) (LocAt.pure _ _)
  · cases ob.task <;> cases ob'.task
    all_goals first
      | exact LocAt.pure _ _
      | exact LocAt.ite' (LocAt.setTask hid _ _) (LocAt.pure _ _)

theorem LocAt.readObject {o : String} {id : Ident} (hid : id.origin = o) (now : Nat) (e : Env) :
    LocAt o (readObject id now) e := by
  intro f hf
  rw [readObject_apply] at hf
  revert hf
  generalize (AbstractModel.getObject id e).1 = r
  cases r with
  | none => intro hf; simp at hf
  | some ob =>
    intro hf
    try dsimp only at hf
    split at hf
    · exact LocAt.materialise hid ob (ob.project now) e f hf
    · simp at hf

theorem LocAt.readTaskObject {o : String} {id : Ident} (hid : id.origin = o) (now : Nat)
    (e : Env) : LocAt o (readTaskObject id now) e := by
  intro f hf
  rw [readTaskObject_apply] at hf
  revert hf
  generalize (AbstractModel.getObject id e).1 = r
  cases r with
  | none => intro hf; simp at hf
  | some ob =>
    intro hf
    try dsimp only at hf
    split at hf
    · exact LocAt.readObject hid now e f hf
    · simp at hf

theorem LocAt.touchObject {o : String} {id : Ident} (hid : id.origin = o) (now : Nat) (e : Env) :
    LocAt o (touchObject id now) e := LocAt.readObject hid now _

theorem LocAt.viewObject {o : String} {id : Ident} (hid : id.origin = o) (now : Nat) (e : Env) :
    LocAt o (viewObject id now) e := LocAt.readObject hid now _

theorem LocAt.touchTaskObject {o : String} {id : Ident} (hid : id.origin = o) (now : Nat)
    (e : Env) : LocAt o (touchTaskObject id now) e := LocAt.readTaskObject hid now _

theorem LocAt.viewTaskObject {o : String} {id : Ident} (hid : id.origin = o) (now : Nat)
    (e : Env) : LocAt o (viewTaskObject id now) e := LocAt.readTaskObject hid now _

theorem touchObject_id {id : Ident} {now : Nat} {e : Env} {ob : Object}
    (h : (touchObject id now e).1 = some ob) : ob.id = id := readObject_id h

theorem viewObject_id {id : Ident} {now : Nat} {e : Env} {ob : Object}
    (h : (viewObject id now e).1 = some ob) : ob.id = id := readObject_id h

theorem touchTaskObject_id {id : Ident} {now : Nat} {e : Env} {ob : Object}
    (h : (touchTaskObject id now e).1 = some ob) : ob.id = id := readTaskObject_id h

theorem viewTaskObject_id {id : Ident} {now : Nat} {e : Env} {ob : Object}
    (h : (viewTaskObject id now e).1 = some ob) : ob.id = id := readTaskObject_id h

theorem LocAt.createPromise {o : String} {req : PromiseCreateReq} (hid : req.id.origin = o)
    (now : Nat) (e : Env) : LocAt o (createPromise req now) e := by
  unfold AbstractModel.createPromise
  apply LocAt.ite'
  · apply LocAt.bind (LocAt.setPromise hid _ _)
    apply LocAt.ite'
    · exact LocAt.bind (LocAt.setTask hid _ _) (LocAt.pure _ _)
    · exact LocAt.pure _ _
  · apply LocAt.bind (LocAt.setPromise hid _ _)
    apply LocAt.ite'
    · exact LocAt.bind (LocAt.setTask hid _ _) (LocAt.pure _ _)
    · exact LocAt.pure _ _

/-! ## The handlers

One `Cong` and one `LocAt` lemma per handler, under the hypothesis that
the request is about origin `o`.

The proofs walk the handler's structure. Two tactics do the walking:
`cong_walk` for congruence and `loc_walk` for locality. Each tries the
leaves first (a `pure`, a write, a read at an id whose origin is in
context), then decomposes a `bind`, an `if`, or a `match`. At an `if`
whose condition is a same-origin door, the walk records what the door
guarantees — that the other id shares the origin — so the read behind
the door finds its hypothesis. At a `match` on what a read returned,
the locality walk records that the object found is at the id asked
for, so the write behind the match finds its hypothesis. -/

/-- The same-origin door, as the fact the proof needs. -/
theorem sameOrigin_eq {a b : Ident} (h : a.sameOrigin b = true) : b.origin = a.origin := by
  simp only [Ident.sameOrigin, beq_iff_eq] at h
  exact h.symm

theorem not_not_sameOrigin {a b : Ident} (h : ¬ (!a.sameOrigin b) = true) :
    b.origin = a.origin := by
  apply sameOrigin_eq
  cases hs : a.sameOrigin b
  · exact absurd (by simp [hs]) h
  · rfl

/-- Every awaited id of a suspension shares the task's origin once the
    door has been passed. -/
theorem not_any_not_sameOrigin {id : Ident} {actions : List PromiseRegisterCallbackReq}
    (h : ¬ (actions.any fun a => !a.awaited.sameOrigin id) = true) :
    ∀ a ∈ actions, a.awaited.origin = id.origin := by
  intro a ha
  have hc' : ¬ (!a.awaited.sameOrigin id) = true := fun hc => h (List.any_eq_true.mpr ⟨a, ha, hc⟩)
  exact (not_not_sameOrigin hc').symm

theorem setSettled_eq (ob : Object) (p : PromiseObject) :
    setSettled ob p = (setPromise ob.id p >>= fun _ =>
      if (p.state != PromiseState.pending) = true then
        match ob.task with
        | some t => if (t.state != TaskState.fulfilled) = true then setTask ob.id t.fulfill else pure ()
        | none   => pure ()
      else pure ()) := rfl

theorem Cong.setSettled {o : String} (ob : Object) (p : PromiseObject) :
    Cong o (setSettled ob p) := by
  rw [setSettled_eq]
  apply Cong.bind (Cong.setPromise _ _)
  intro _
  apply Cong.ite'
  · cases ob.task
    · exact Cong.pure _
    · exact Cong.ite' (Cong.setTask _ _) (Cong.pure _)
  · exact Cong.pure _

theorem LocAt.setSettled {o : String} {ob : Object} (hob : ob.id.origin = o) (p : PromiseObject)
    (e : Env) : LocAt o (setSettled ob p) e := by
  rw [setSettled_eq]
  apply LocAt.bind (LocAt.setPromise hob _ _)
  apply LocAt.ite'
  · cases ob.task
    · exact LocAt.pure _ _
    · exact LocAt.ite' (LocAt.setTask hob _ _) (LocAt.pure _ _)
  · exact LocAt.pure _ _

/-- A door's hypothesis, turned into the origin fact the walk needs. -/
syntax "note_door" : tactic
macro_rules
  | `(tactic| note_door) => `(tactic| first
      | (have hd := not_not_sameOrigin ‹_›; have hd' := hd.trans ‹_›)
      | skip)

/-- The leaves and the structure of the congruence walk. -/
syntax "cong_walk" : tactic
macro_rules
  | `(tactic| cong_walk) => `(tactic| first
      | exact Cong.pure _
      | exact Cong.setPromise _ _
      | exact Cong.setTask _ _
      | exact Cong.setMessage _ _
      | exact Cong.setSettled _ _
      | exact Cong.createPromise _ _
      | exact Cong.readObject (by assumption) _
      | exact Cong.readTaskObject (by assumption) _
      | exact Cong.touchObject (by assumption) _
      | exact Cong.viewObject (by assumption) _
      | exact Cong.touchTaskObject (by assumption) _
      | exact Cong.viewTaskObject (by assumption) _
      | (apply Cong.bind
         · cong_walk
         · intro a; cong_walk)
      | (apply Cong.ite <;> intro hc <;> note_door <;> cong_walk)
      | (split <;> (try dsimp only) <;> cong_walk))

/-- What a read returned is at the id it was asked for: record it, and
    rewrite the object's id to the request's. -/
syntax "note_id" : tactic
macro_rules
  | `(tactic| note_id) => `(tactic| first
      | (have hob := readObject_id ‹_›; have hob' := (congrArg Ident.origin hob).trans ‹_›)
      | (have hob := readTaskObject_id ‹_›; have hob' := (congrArg Ident.origin hob).trans ‹_›)
      | (have hob := touchObject_id ‹_›; have hob' := (congrArg Ident.origin hob).trans ‹_›)
      | (have hob := viewObject_id ‹_›; have hob' := (congrArg Ident.origin hob).trans ‹_›)
      | (have hob := touchTaskObject_id ‹_›; have hob' := (congrArg Ident.origin hob).trans ‹_›)
      | (have hob := viewTaskObject_id ‹_›; have hob' := (congrArg Ident.origin hob).trans ‹_›)
      | skip)

/-- The leaves and the structure of the locality walk. -/
syntax "loc_walk" : tactic
macro_rules
  | `(tactic| loc_walk) => `(tactic| first
      | exact LocAt.pure _ _
      | exact LocAt.setPromise (by assumption) _ _
      | exact LocAt.setTask (by assumption) _ _
      | exact LocAt.setMessage _ _ _
      | exact LocAt.setSettled (by assumption) _ _
      | exact LocAt.createPromise (by assumption) _ _
      | exact LocAt.readObject (by assumption) _ _
      | exact LocAt.readTaskObject (by assumption) _ _
      | exact LocAt.touchObject (by assumption) _ _
      | exact LocAt.viewObject (by assumption) _ _
      | exact LocAt.touchTaskObject (by assumption) _ _
      | exact LocAt.viewTaskObject (by assumption) _ _
      | (apply LocAt.bind
         · loc_walk
         · (try dsimp only); loc_walk)
      | (apply LocAt.ite <;> intro hc <;> note_door <;> loc_walk)
      | (split <;> (try dsimp only) <;> note_id <;> loc_walk))

section Promise

theorem Cong.promiseGet {o : String} {req : PromiseGetReq} (hid : req.id.origin = o) (now : Nat) :
    Cong o (promiseGet req now) := by
  unfold AbstractModel.promiseGet; cong_walk

theorem LocAt.promiseGet {o : String} {req : PromiseGetReq} (hid : req.id.origin = o) (now : Nat)
    (e : Env) : LocAt o (promiseGet req now) e := by
  unfold AbstractModel.promiseGet; loc_walk

theorem Cong.promiseCreate {o : String} {req : PromiseCreateReq} (hid : req.id.origin = o)
    (now : Nat) : Cong o (promiseCreate req now) := by
  unfold AbstractModel.promiseCreate; simp only [pure_bind]; cong_walk

theorem LocAt.promiseCreate {o : String} {req : PromiseCreateReq} (hid : req.id.origin = o)
    (now : Nat) (e : Env) : LocAt o (promiseCreate req now) e := by
  unfold AbstractModel.promiseCreate; simp only [pure_bind]; loc_walk

theorem Cong.promiseSettle {o : String} {req : PromiseSettleReq} (hid : req.id.origin = o)
    (now : Nat) : Cong o (promiseSettle req now) := by
  unfold AbstractModel.promiseSettle; simp only [pure_bind]; cong_walk

theorem LocAt.promiseSettle {o : String} {req : PromiseSettleReq} (hid : req.id.origin = o)
    (now : Nat) (e : Env) : LocAt o (promiseSettle req now) e := by
  unfold AbstractModel.promiseSettle; simp only [pure_bind]; loc_walk

theorem Cong.promiseRegisterCallback {o : String} {req : PromiseRegisterCallbackReq}
    (hid : req.awaited.origin = o) (now : Nat) : Cong o (promiseRegisterCallback req now) := by
  unfold AbstractModel.promiseRegisterCallback; simp only [pure_bind]; cong_walk

theorem LocAt.promiseRegisterCallback {o : String} {req : PromiseRegisterCallbackReq}
    (hid : req.awaited.origin = o) (now : Nat) (e : Env) :
    LocAt o (promiseRegisterCallback req now) e := by
  unfold AbstractModel.promiseRegisterCallback; simp only [pure_bind]; loc_walk

theorem Cong.promiseRegisterListener {o : String} {req : PromiseRegisterListenerReq}
    (hid : req.awaited.origin = o) (now : Nat) : Cong o (promiseRegisterListener req now) := by
  unfold AbstractModel.promiseRegisterListener; simp only [pure_bind]; cong_walk

theorem LocAt.promiseRegisterListener {o : String} {req : PromiseRegisterListenerReq}
    (hid : req.awaited.origin = o) (now : Nat) (e : Env) :
    LocAt o (promiseRegisterListener req now) e := by
  unfold AbstractModel.promiseRegisterListener; simp only [pure_bind]; loc_walk

end Promise

section Task

theorem Cong.taskGet {o : String} {req : TaskGetReq} (hid : req.id.origin = o) (now : Nat) :
    Cong o (taskGet req now) := by
  unfold AbstractModel.taskGet; cong_walk

theorem LocAt.taskGet {o : String} {req : TaskGetReq} (hid : req.id.origin = o) (now : Nat)
    (e : Env) : LocAt o (taskGet req now) e := by
  unfold AbstractModel.taskGet; loc_walk

theorem Cong.taskCreate {o : String} {req : TaskCreateReq} (hid : req.action.id.origin = o)
    (now : Nat) : Cong o (taskCreate req now) := by
  unfold AbstractModel.taskCreate; simp only [pure_bind]; cong_walk

theorem LocAt.taskCreate {o : String} {req : TaskCreateReq} (hid : req.action.id.origin = o)
    (now : Nat) (e : Env) : LocAt o (taskCreate req now) e := by
  unfold AbstractModel.taskCreate; simp only [pure_bind]; loc_walk

theorem Cong.taskAcquire {o : String} {req : TaskAcquireReq} (hid : req.id.origin = o) (now : Nat) :
    Cong o (taskAcquire req now) := by
  unfold AbstractModel.taskAcquire; simp only [pure_bind]; cong_walk

theorem LocAt.taskAcquire {o : String} {req : TaskAcquireReq} (hid : req.id.origin = o) (now : Nat)
    (e : Env) : LocAt o (taskAcquire req now) e := by
  unfold AbstractModel.taskAcquire; simp only [pure_bind]; loc_walk

/-- Behind the fence's same-origin door, the action's target shares the
    task's origin, whichever action it is. -/
theorem fence_target_origin {req : TaskFenceReq}
    (h : ¬ (!req.action.targetId.sameOrigin req.id) = true) :
    req.id.origin = req.action.targetId.origin := not_not_sameOrigin h

theorem Cong.taskFence {o : String} {req : TaskFenceReq} (hid : req.id.origin = o) (now : Nat) :
    Cong o (taskFence req now) := by
  unfold AbstractModel.taskFence; simp only [pure_bind]
  apply Cong.ite' (Cong.pure _)
  apply Cong.ite (fun _ => Cong.pure _)
  intro hdoor
  have htgt : req.action.targetId.origin = o := (fence_target_origin hdoor).symm.trans hid
  cases hact : req.action with
  | create r =>
    have hr : r.id.origin = o := by simpa [hact, TaskFenceAction.targetId] using htgt
    cong_walk
  | settle r =>
    have hr : r.id.origin = o := by simpa [hact, TaskFenceAction.targetId] using htgt
    cong_walk

theorem LocAt.taskFence {o : String} {req : TaskFenceReq} (hid : req.id.origin = o) (now : Nat)
    (e : Env) : LocAt o (taskFence req now) e := by
  unfold AbstractModel.taskFence; simp only [pure_bind]
  apply LocAt.ite' (LocAt.pure _ _)
  apply LocAt.ite (fun _ => LocAt.pure _ _)
  intro hdoor
  have htgt : req.action.targetId.origin = o := (fence_target_origin hdoor).symm.trans hid
  cases hact : req.action with
  | create r =>
    have hr : r.id.origin = o := by simpa [hact, TaskFenceAction.targetId] using htgt
    loc_walk
  | settle r =>
    have hr : r.id.origin = o := by simpa [hact, TaskFenceAction.targetId] using htgt
    loc_walk

theorem Cong.heartbeatOne {o : String} {ref : TaskRef} (hid : ref.id.origin = o) (pid : String)
    (now : Nat) : Cong o (heartbeatOne pid ref now) := by
  unfold AbstractModel.heartbeatOne; cong_walk

theorem LocAt.heartbeatOne {o : String} {ref : TaskRef} (hid : ref.id.origin = o) (pid : String)
    (now : Nat) (e : Env) : LocAt o (heartbeatOne pid ref now) e := by
  unfold AbstractModel.heartbeatOne; loc_walk

theorem Cong.heartbeatAll {o : String} (pid : String) (now : Nat) :
    ∀ refs : List TaskRef, (∀ r ∈ refs, r.id.origin = o) → Cong o (heartbeatAll pid now refs)
  | [], _ => by rw [AbstractModel.heartbeatAll]; exact Cong.pure _
  | ref :: refs, h => by
      rw [AbstractModel.heartbeatAll]
      exact Cong.bind (Cong.heartbeatOne (h ref (List.mem_cons_self ..)) pid now)
        (fun _ => Cong.heartbeatAll pid now refs (fun r hr => h r (List.mem_cons_of_mem _ hr)))

theorem LocAt.heartbeatAll {o : String} (pid : String) (now : Nat) (e : Env) :
    ∀ refs : List TaskRef, (∀ r ∈ refs, r.id.origin = o) → LocAt o (heartbeatAll pid now refs) e
  | [], _ => by rw [AbstractModel.heartbeatAll]; exact LocAt.pure _ _
  | ref :: refs, h => by
      rw [AbstractModel.heartbeatAll]
      exact LocAt.bind (LocAt.heartbeatOne (h ref (List.mem_cons_self ..)) pid now e)
        (LocAt.heartbeatAll pid now e refs (fun r hr => h r (List.mem_cons_of_mem _ hr)))

theorem Cong.taskHeartbeat {o : String} {req : TaskHeartbeatReq}
    (h : ∀ r ∈ req.tasks, r.id.origin = o) (now : Nat) : Cong o (taskHeartbeat req now) := by
  unfold AbstractModel.taskHeartbeat
  exact Cong.bind (Cong.heartbeatAll _ _ _ h) (fun _ => Cong.pure _)

theorem LocAt.taskHeartbeat {o : String} {req : TaskHeartbeatReq}
    (h : ∀ r ∈ req.tasks, r.id.origin = o) (now : Nat) (e : Env) :
    LocAt o (taskHeartbeat req now) e := by
  unfold AbstractModel.taskHeartbeat
  exact LocAt.bind (LocAt.heartbeatAll _ _ _ _ h) (LocAt.pure _ _)

theorem Cong.checkAwaited {o : String} (now : Nat) :
    ∀ actions : List PromiseRegisterCallbackReq, (∀ a ∈ actions, a.awaited.origin = o) →
      Cong o (checkAwaited now actions)
  | [], _ => by rw [AbstractModel.checkAwaited]; exact Cong.pure _
  | action :: rest, h => by
      rw [AbstractModel.checkAwaited]
      have ha : action.awaited.origin = o := h action (List.mem_cons_self ..)
      have hrest := Cong.checkAwaited now rest (fun a hr => h a (List.mem_cons_of_mem _ hr))
      apply Cong.bind (Cong.readObject ha now)
      intro a; cases a
      · exact Cong.pure _
      · apply Cong.ite' (Cong.pure _)
        apply Cong.bind hrest
        intro b; cases b <;> exact Cong.pure _

theorem LocAt.checkAwaited {o : String} (now : Nat) (e : Env) :
    ∀ actions : List PromiseRegisterCallbackReq, (∀ a ∈ actions, a.awaited.origin = o) →
      LocAt o (checkAwaited now actions) e
  | [], _ => by rw [AbstractModel.checkAwaited]; exact LocAt.pure _ _
  | action :: rest, h => by
      rw [AbstractModel.checkAwaited]
      have ha : action.awaited.origin = o := h action (List.mem_cons_self ..)
      have hrest := LocAt.checkAwaited now e rest (fun a hr => h a (List.mem_cons_of_mem _ hr))
      apply LocAt.bind (LocAt.readObject ha now e)
      cases (AbstractModel.readObject action.awaited now e).1
      · exact LocAt.pure _ _
      · apply LocAt.ite' (LocAt.pure _ _)
        apply LocAt.bind hrest
        cases (AbstractModel.checkAwaited now rest e).1 <;> exact LocAt.pure _ _

theorem Cong.registerAwaited {o : String} (awaiter : Ident) (now : Nat) :
    ∀ actions : List PromiseRegisterCallbackReq, (∀ a ∈ actions, a.awaited.origin = o) →
      Cong o (registerAwaited awaiter now actions)
  | [], _ => by rw [AbstractModel.registerAwaited]; exact Cong.pure _
  | action :: rest, h => by
      rw [AbstractModel.registerAwaited]
      have ha : action.awaited.origin = o := h action (List.mem_cons_self ..)
      have hrest := Cong.registerAwaited awaiter now rest (fun a hr => h a (List.mem_cons_of_mem _ hr))
      simp only [pure_bind]
      apply Cong.bind (Cong.readObject ha now)
      intro a; cases a
      · exact hrest
      · exact Cong.bind (Cong.setPromise _ _) (fun _ => hrest)

theorem LocAt.registerAwaited {o : String} (awaiter : Ident) (now : Nat) (e : Env) :
    ∀ actions : List PromiseRegisterCallbackReq, (∀ a ∈ actions, a.awaited.origin = o) →
      LocAt o (registerAwaited awaiter now actions) e
  | [], _ => by rw [AbstractModel.registerAwaited]; exact LocAt.pure _ _
  | action :: rest, h => by
      rw [AbstractModel.registerAwaited]
      have ha : action.awaited.origin = o := h action (List.mem_cons_self ..)
      have hrest := LocAt.registerAwaited awaiter now e rest (fun a hr => h a (List.mem_cons_of_mem _ hr))
      simp only [pure_bind]
      apply LocAt.bind (LocAt.readObject ha now e)
      rcases hr : (AbstractModel.readObject action.awaited now e).1 with _ | oa
      · exact hrest
      · have hoa : oa.id.origin = o := by rw [readObject_id hr]; exact ha
        exact LocAt.bind (LocAt.setPromise hoa _ _) hrest

theorem Cong.taskSuspend {o : String} {req : TaskSuspendReq} (hid : req.id.origin = o) (now : Nat) :
    Cong o (taskSuspend req now) := by
  unfold AbstractModel.taskSuspend; simp only [pure_bind]
  apply Cong.ite' (Cong.pure _)
  apply Cong.ite' (Cong.pure _)
  apply Cong.ite (fun _ => Cong.pure _)
  intro hdoor
  have hall : ∀ a ∈ req.actions, a.awaited.origin = o :=
    fun a ha => (not_any_not_sameOrigin hdoor a ha).trans hid
  apply Cong.ite' (Cong.pure _)
  apply Cong.bind (Cong.readTaskObject hid now)
  intro a
  split
  · exact Cong.pure _
  · split
    · exact Cong.pure _
    · apply Cong.ite' (Cong.pure _)
      apply Cong.ite' (Cong.pure _)
      apply Cong.ite' (Cong.pure _)
      apply Cong.bind (Cong.checkAwaited now req.actions hall)
      intro b
      split
      · exact Cong.pure _
      · exact Cong.bind (Cong.setTask _ _) (fun _ => Cong.pure _)
      · exact Cong.bind (Cong.registerAwaited req.id now req.actions hall)
          (fun _ => Cong.bind (Cong.setTask _ _) (fun _ => Cong.pure _))

theorem LocAt.taskSuspend {o : String} {req : TaskSuspendReq} (hid : req.id.origin = o) (now : Nat)
    (e : Env) : LocAt o (taskSuspend req now) e := by
  unfold AbstractModel.taskSuspend; simp only [pure_bind]
  apply LocAt.ite' (LocAt.pure _ _)
  apply LocAt.ite' (LocAt.pure _ _)
  apply LocAt.ite (fun _ => LocAt.pure _ _)
  intro hdoor
  have hall : ∀ a ∈ req.actions, a.awaited.origin = o :=
    fun a ha => (not_any_not_sameOrigin hdoor a ha).trans hid
  apply LocAt.ite' (LocAt.pure _ _)
  apply LocAt.bind (LocAt.readTaskObject hid now e)
  try dsimp only
  split
  · exact LocAt.pure _ _
  · rename_i ob hr
    have hob : ob.id.origin = o := by rw [readTaskObject_id hr]; exact hid
    split
    · exact LocAt.pure _ _
    · apply LocAt.ite' (LocAt.pure _ _)
      apply LocAt.ite' (LocAt.pure _ _)
      apply LocAt.ite' (LocAt.pure _ _)
      apply LocAt.bind (LocAt.checkAwaited now e req.actions hall)
      try dsimp only
      split
      · exact LocAt.pure _ _
      · exact LocAt.bind (LocAt.setTask hob _ _) (LocAt.pure _ _)
      · exact LocAt.bind (LocAt.registerAwaited req.id now e req.actions hall)
          (LocAt.bind (LocAt.setTask hob _ _) (LocAt.pure _ _))

theorem Cong.taskFulfill {o : String} {req : TaskFulfillReq} (hid : req.id.origin = o) (now : Nat) :
    Cong o (taskFulfill req now) := by
  unfold AbstractModel.taskFulfill; simp only [pure_bind]; cong_walk

theorem LocAt.taskFulfill {o : String} {req : TaskFulfillReq} (hid : req.id.origin = o) (now : Nat)
    (e : Env) : LocAt o (taskFulfill req now) e := by
  unfold AbstractModel.taskFulfill; simp only [pure_bind]; loc_walk

theorem Cong.taskRelease {o : String} {req : TaskReleaseReq} (hid : req.id.origin = o) (now : Nat) :
    Cong o (taskRelease req now) := by
  unfold AbstractModel.taskRelease; simp only [pure_bind]; cong_walk

theorem LocAt.taskRelease {o : String} {req : TaskReleaseReq} (hid : req.id.origin = o) (now : Nat)
    (e : Env) : LocAt o (taskRelease req now) e := by
  unfold AbstractModel.taskRelease; simp only [pure_bind]; loc_walk

theorem Cong.taskHalt {o : String} {req : TaskHaltReq} (hid : req.id.origin = o) (now : Nat) :
    Cong o (taskHalt req now) := by
  unfold AbstractModel.taskHalt; simp only [pure_bind]; cong_walk

theorem LocAt.taskHalt {o : String} {req : TaskHaltReq} (hid : req.id.origin = o) (now : Nat)
    (e : Env) : LocAt o (taskHalt req now) e := by
  unfold AbstractModel.taskHalt; simp only [pure_bind]; loc_walk

theorem Cong.taskContinue {o : String} {req : TaskContinueReq} (hid : req.id.origin = o) (now : Nat) :
    Cong o (taskContinue req now) := by
  unfold AbstractModel.taskContinue; simp only [pure_bind]; cong_walk

theorem LocAt.taskContinue {o : String} {req : TaskContinueReq} (hid : req.id.origin = o) (now : Nat)
    (e : Env) : LocAt o (taskContinue req now) e := by
  unfold AbstractModel.taskContinue; simp only [pure_bind]; loc_walk

end Task

section Internal

open AbstractModel.Internal

theorem Cong.processPromiseTimeout {o : String} {req : PromiseTimeoutReq} (hid : req.id.origin = o)
    (now : Nat) : Cong o (processPromiseTimeout req now) := by
  unfold AbstractModel.Internal.processPromiseTimeout; cong_walk

theorem LocAt.processPromiseTimeout {o : String} {req : PromiseTimeoutReq} (hid : req.id.origin = o)
    (now : Nat) (e : Env) : LocAt o (processPromiseTimeout req now) e := by
  unfold AbstractModel.Internal.processPromiseTimeout; loc_walk

theorem Cong.resumeOne {o : String} {awaiter : Ident} (hid : awaiter.origin = o) (awaited : Ident)
    (now : Nat) : Cong o (resumeOne awaited awaiter now) := by
  unfold AbstractModel.Internal.resumeOne; cong_walk

theorem LocAt.resumeOne {o : String} {awaiter : Ident} (hid : awaiter.origin = o) (awaited : Ident)
    (now : Nat) (e : Env) : LocAt o (resumeOne awaited awaiter now) e := by
  unfold AbstractModel.Internal.resumeOne; loc_walk

theorem Cong.processCallback {o : String} {req : PromiseRegisterCallbackReq}
    (hid : req.awaited.origin = o) (hid' : req.awaiter.origin = o) (now : Nat) :
    Cong o (processCallback req now) := by
  unfold AbstractModel.Internal.processCallback
  apply Cong.bind (Cong.touchObject hid now)
  intro a; cases a
  · exact Cong.pure _
  · apply Cong.ite' (Cong.pure _)
    apply Cong.ite' _ (Cong.pure _)
    exact Cong.bind (Cong.setPromise _ _) (fun _ => Cong.resumeOne hid' _ now)

theorem LocAt.processCallback {o : String} {req : PromiseRegisterCallbackReq}
    (hid : req.awaited.origin = o) (hid' : req.awaiter.origin = o) (now : Nat) (e : Env) :
    LocAt o (processCallback req now) e := by
  unfold AbstractModel.Internal.processCallback
  apply LocAt.bind (LocAt.touchObject hid now e)
  rcases hr : (AbstractModel.touchObject req.awaited now e).1 with _ | ob
  · exact LocAt.pure _ _
  · have hob : ob.id.origin = o := by rw [touchObject_id hr]; exact hid
    apply LocAt.ite' (LocAt.pure _ _)
    apply LocAt.ite' _ (LocAt.pure _ _)
    exact LocAt.bind (LocAt.setPromise hob _ _) (LocAt.resumeOne hid' _ now e)

theorem Cong.processListener {o : String} {req : PromiseRegisterListenerReq}
    (hid : req.awaited.origin = o) (now : Nat) : Cong o (processListener req now) := by
  unfold AbstractModel.Internal.processListener; cong_walk

theorem LocAt.processListener {o : String} {req : PromiseRegisterListenerReq}
    (hid : req.awaited.origin = o) (now : Nat) (e : Env) : LocAt o (processListener req now) e := by
  unfold AbstractModel.Internal.processListener; loc_walk

theorem Cong.processLeaseTimeout {o : String} {req : TaskLeaseTimeoutReq} (hid : req.id.origin = o)
    (now : Nat) : Cong o (processLeaseTimeout req now) := by
  unfold AbstractModel.Internal.processLeaseTimeout; cong_walk

theorem LocAt.processLeaseTimeout {o : String} {req : TaskLeaseTimeoutReq} (hid : req.id.origin = o)
    (now : Nat) (e : Env) : LocAt o (processLeaseTimeout req now) e := by
  unfold AbstractModel.Internal.processLeaseTimeout; loc_walk

/-- The retry step reads the configuration, which the two environments
    share; otherwise it is a plain walk. -/
theorem Cong.processRetryTimeout {o : String} {req : TaskRetryTimeoutReq} (hid : req.id.origin = o)
    (now : Nat) : Cong o (processRetryTimeout req now) := by
  unfold AbstractModel.Internal.processRetryTimeout
  apply Cong.bind (Cong.viewTaskObject hid now)
  intro a
  split
  · exact Cong.pure _
  · split
    · exact Cong.pure _
    · split
      · exact Cong.pure _
      · apply Cong.ite' _ (Cong.pure _)
        apply Cong.ite' _ (Cong.pure _)
        intro e e' h
        simp only [bind_apply, ask_apply, h.config, AbstractModel.setTask, AbstractModel.setMessage,
          emit_apply]

theorem LocAt.processRetryTimeout {o : String} {req : TaskRetryTimeoutReq} (hid : req.id.origin = o)
    (now : Nat) (e : Env) : LocAt o (processRetryTimeout req now) e := by
  unfold AbstractModel.Internal.processRetryTimeout
  apply LocAt.bind (LocAt.viewTaskObject hid now e)
  try dsimp only
  split
  · exact LocAt.pure _ _
  · rename_i ob hr
    have hob : ob.id.origin = o := by rw [viewTaskObject_id hr]; exact hid
    split
    · exact LocAt.pure _ _
    · split
      · exact LocAt.pure _ _
      · apply LocAt.ite' _ (LocAt.pure _ _)
        apply LocAt.ite' _ (LocAt.pure _ _)
        apply LocAt.bind (by intro f hf; simp [ask_apply] at hf)
        exact LocAt.bind (LocAt.setTask hob _ _) (LocAt.setMessage _ _ _)

end Internal

end Frame
