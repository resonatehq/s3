import impl.internal

namespace Concrete

open Protocol (Message OutboxEntry Request Response)

inductive Path
  | origin (name : String)
  | timer (t : Timer)
  deriving Repr, DecidableEq

inductive Blob
  | origin (org : Origin)
  | timer
  deriving Repr

structure Hasher where
  Hash : Type
  hash : Blob → Hash
  inj  : ∀ a b, hash a = hash b → a = b
  deq  : DecidableEq Hash

attribute [instance] Hasher.deq

inductive Cond (H : Hasher)
  | any
  | absent
  | hash (h : H.Hash)

def Cond.holds {H : Hasher} : Cond H → Option Blob → Bool
  | .any, _ =>
      true
  | .absent, cur =>
      cur.isNone
  | .hash h, cur =>
      cur.map H.hash == some h

def Cond.of (H : Hasher) : Option Blob → Cond H
  | some b =>
      .hash (H.hash b)
  | none =>
      .absent

structure State where
  bucket : List (Path × Blob) := []
  outbox : List OutboxEntry := []
  deriving Repr

def State.init : State := {}

def State.blob? (s : State) (p : Path) : Option Blob :=
  (s.bucket.find? (·.1 == p)).map (·.2)

def State.origin (s : State) (name : String) : Origin :=
  match s.blob? (.origin name) with
  | some (.origin org) =>
      org
  | _ =>
      {}

inductive Effect (H : Hasher)
  | put (path : Path) (blob : Blob) (cond : Cond H)
  | del (path : Path)
  | send (address : String) (msg : Message)

def Effect.apply {H : Hasher} (s : State) : Effect H → Option State
  | .put p b c =>
      if c.holds (s.blob? p) then
        some { s with bucket := (p, b) :: s.bucket.filter (·.1 != p) }
      else
        none
  | .del p =>
      some { s with bucket := s.bucket.filter (·.1 != p) }
  | .send a m =>
      let entry := OutboxEntry.mk a m
      some { s with outbox := entry :: s.outbox.filter (fun e => e.key != entry.key) }

def applyAll {H : Hasher} : State → List (Effect H) → State × Bool
  | s, [] =>
      (s, true)
  | s, e :: es =>
      match e.apply s with
      | some s' =>
          applyAll s' es
      | none =>
          (s, false)

def Commands.effects {H : Hasher} (name : String) (cond : Cond H) (c : Commands) :
    List (Effect H) :=
  c.arm.map (fun t => .put (.timer t) .timer .any)
  ++ [.put (.origin name) (.origin c.put) cond]
  ++ c.del.map (fun t => .del (.timer t))
  ++ c.send.map (fun (a, m) => .send a m)

def run (H : Hasher) (name : String) (f : Origin → α × Commands) (s : State) :
    α × State × Bool :=
  let (a, c) := f (s.origin name)
  let (s', ok) := applyAll s (c.effects name (Cond.of H (s.blob? (.origin name))))
  (a, s', ok)

def _root_.Protocol.Request.origin? : Request → Option String
  | .promiseGet req =>
      some req.id.origin
  | .promiseCreate req =>
      some req.id.origin
  | .promiseSettle req =>
      some req.id.origin
  | .promiseRegisterCallback req =>
      some req.awaited.origin
  | .promiseRegisterListener req =>
      some req.awaited.origin
  | .promiseSearch _ =>
      none
  | .scheduleGet _ =>
      none
  | .scheduleCreate _ =>
      none
  | .scheduleDelete _ =>
      none
  | .scheduleSearch _ =>
      none
  | .taskGet req =>
      some req.id.origin
  | .taskCreate req =>
      some req.action.id.origin
  | .taskAcquire req =>
      some req.id.origin
  | .taskFence req =>
      some req.id.origin
  | .taskHeartbeat req =>
      match req.tasks with
      | [] =>
          none
      | t :: ts =>
          if ts.all (·.id.origin == t.id.origin) then some t.id.origin else none
  | .taskSuspend req =>
      some req.id.origin
  | .taskFulfill req =>
      some req.id.origin
  | .taskRelease req =>
      some req.id.origin
  | .taskHalt req =>
      some req.id.origin
  | .taskContinue req =>
      some req.id.origin
  | .taskSearch _ =>
      none

inductive Event
  | external (req : Request)
  | internal (timer : Timer)
  | stutter
  deriving Repr

inductive Reply
  | external (res : Response)
  | internal
  | stutter
  deriving Repr, BEq

def handleExternal (now : Nat) (org : Origin) : Request → Response × Commands
  | .promiseGet req =>
      let (res, c) := promiseGet now org req
      (.promiseGet res, c)
  | .promiseCreate req =>
      let (res, c) := promiseCreate now org req
      (.promiseCreate res, c)
  | .promiseSettle req =>
      let (res, c) := promiseSettle now org req
      (.promiseSettle res, c)
  | .promiseRegisterCallback req =>
      let (res, c) := promiseRegisterCallback now org req
      (.promiseRegisterCallback res, c)
  | .promiseRegisterListener req =>
      let (res, c) := promiseRegisterListener now org req
      (.promiseRegisterListener res, c)
  | .promiseSearch req =>
      let (res, c) := promiseSearch now org req
      (.promiseSearch res, c)
  | .scheduleGet req =>
      let (res, c) := scheduleGet now org req
      (.scheduleGet res, c)
  | .scheduleCreate req =>
      let (res, c) := scheduleCreate now org req
      (.scheduleCreate res, c)
  | .scheduleDelete req =>
      let (res, c) := scheduleDelete now org req
      (.scheduleDelete res, c)
  | .scheduleSearch req =>
      let (res, c) := scheduleSearch now org req
      (.scheduleSearch res, c)
  | .taskGet req =>
      let (res, c) := taskGet now org req
      (.taskGet res, c)
  | .taskCreate req =>
      let (res, c) := taskCreate now org req
      (.taskCreate res, c)
  | .taskAcquire req =>
      let (res, c) := taskAcquire now org req
      (.taskAcquire res, c)
  | .taskFence req =>
      let (res, c) := taskFence now org req
      (.taskFence res, c)
  | .taskHeartbeat req =>
      let (res, c) := taskHeartbeat now org req
      (.taskHeartbeat res, c)
  | .taskSuspend req =>
      let (res, c) := taskSuspend now org req
      (.taskSuspend res, c)
  | .taskFulfill req =>
      let (res, c) := taskFulfill now org req
      (.taskFulfill res, c)
  | .taskRelease req =>
      let (res, c) := taskRelease now org req
      (.taskRelease res, c)
  | .taskHalt req =>
      let (res, c) := taskHalt now org req
      (.taskHalt res, c)
  | .taskContinue req =>
      let (res, c) := taskContinue now org req
      (.taskContinue res, c)
  | .taskSearch req =>
      let (res, c) := taskSearch now org req
      (.taskSearch res, c)

def handle (now : Nat) (org : Origin) : Event → Reply × Commands
  | .external req =>
      let swept := sweep now org
      let (res, c) := handleExternal now swept.put req
      (.external res, swept.merge c)
  | .internal _ =>
      (.internal, sweep now org)
  | .stutter =>
      (.stutter, { put := org })

def step (H : Hasher) (ev : Event) (now : Nat) (s : State) : Reply × State :=
  match ev with
  | .external req =>
      match req.origin? with
      | some name =>
          let (r, s', ok) := run H name (fun org => handle now org ev) s
          (if ok then r else .stutter, s')
      | none =>
          (.external (handleExternal now {} req).1, s)
  | .internal t =>
      if (s.blob? (.timer t)).isSome ∧ t.deadline ≤ now then
        let (r, s', ok) := run H t.id.origin (fun org => handle now org ev) s
        (if ok then r else .stutter, s')
      else
        (.stutter, s)
  | .stutter =>
      (.stutter, s)

def exec (H : Hasher) : List (Event × Nat) → State → List Reply × State
  | [], s =>
      ([], s)
  | (ev, n) :: w, s =>
      let (r, s')   := step H ev n s
      let (rs, s'') := exec H w s'
      (r :: rs, s'')

structure Frame where
  state : State
  event : Event
  reply : Reply
  now   : Nat

abbrev Trace := Nat → Frame

def Valid (H : Hasher) (tr : Trace) : Prop :=
  ∀ t : Nat,
    step H (tr t).event (tr t).now (tr t).state = ((tr t).reply, (tr (t + 1)).state) ∧
    (tr t).now ≤ (tr (t + 1)).now

theorem Valid.reply {H : Hasher} {tr : Trace} (hv : Valid H tr) (t : Nat) :
    (tr t).reply = (step H (tr t).event (tr t).now (tr t).state).1 := by
  rw [(hv t).1]

theorem Valid.state {H : Hasher} {tr : Trace} (hv : Valid H tr) (t : Nat) :
    (tr (t + 1)).state = (step H (tr t).event (tr t).now (tr t).state).2 := by
  rw [(hv t).1]

theorem Valid.now {H : Hasher} {tr : Trace} (hv : Valid H tr) (t : Nat) :
    (tr t).now ≤ (tr (t + 1)).now := (hv t).2

variable {H : Hasher}

theorem Cond.of_holds (b : Option Blob) : (Cond.of H b).holds b = true := by
  cases b <;> simp [Cond.of, Cond.holds]

theorem Cond.of_holds_iff (a : Blob) (b : Option Blob) :
    (Cond.of H (some a)).holds b = true ↔ b = some a := by
  cases b with
  | none =>
      simp [Cond.of, Cond.holds]
  | some b =>
      simp only [Cond.of, Cond.holds, Option.map_some, beq_iff_eq, Option.some.injEq]
      exact ⟨fun h => H.inj b a h, fun h => congrArg H.hash h⟩

def Effect.unconditional : Effect H → Bool
  | .put _ _ .any =>
      true
  | .put _ _ _ =>
      false
  | .del _ =>
      true
  | .send _ _ =>
      true

theorem apply_unconditional {e : Effect H} (h : e.unconditional = true) (s : State) :
    ∃ s', e.apply s = some s' := by
  cases e with
  | put p b c =>
      cases c <;> simp [Effect.unconditional] at h
      exact ⟨{ s with bucket := (p, b) :: s.bucket.filter (·.1 != p) },
             by simp [Effect.apply, Cond.holds]⟩
  | del p =>
      exact ⟨_, rfl⟩
  | send a m =>
      exact ⟨_, rfl⟩

theorem applyAll_unconditional :
    ∀ (es : List (Effect H)) (s : State), (∀ e ∈ es, e.unconditional = true) →
      (applyAll s es).2 = true
  | [], _, _ =>
      rfl
  | e :: es, s, h => by
      obtain ⟨s', hs⟩ := apply_unconditional (h e (List.mem_cons_self ..)) s
      simp only [applyAll, hs]
      exact applyAll_unconditional es s' (fun e he => h e (List.mem_cons_of_mem _ he))

theorem applyAll_append (a b : List (Effect H)) (s : State) :
    applyAll s (a ++ b) =
      if (applyAll s a).2 then applyAll (applyAll s a).1 b else applyAll s a := by
  induction a generalizing s with
  | nil =>
      simp [applyAll]
  | cons e es ih =>
      simp only [List.cons_append, applyAll]
      cases e.apply s with
      | some s' =>
          exact ih s'
      | none =>
          simp

theorem blob?_put_other {s : State} {p q : Path} {b : Blob} {c : Cond H} {s' : State}
    (h : (Effect.put p b c).apply s = some s') (hne : q ≠ p) :
    s'.blob? q = s.blob? q := by
  simp only [Effect.apply] at h
  split at h
  · cases h
    have hq : ((p, b).1 == q) = false := by simpa using Ne.symm hne
    simp only [State.blob?, List.find?_cons, hq]
    congr 1
    induction s.bucket with
    | nil =>
        rfl
    | cons x xs ih =>
        by_cases hx : x.1 = q
        · have h1 : (x.1 == q) = true := by simpa using hx
          have h2 : (x.1 != p) = true := by simpa [hx] using hne
          simp [h1, h2]
        · have h1 : (x.1 == q) = false := by simpa using hx
          by_cases hp : x.1 = p
          · have h2 : (x.1 != p) = false := by simpa using hp
            simp [h1, h2, ih]
          · have h2 : (x.1 != p) = true := by simpa using hp
            simp [h1, h2, ih]
  · cases h

theorem applyAll_arm (name : String) :
    ∀ (ts : List Timer) (s : State),
      (applyAll s (ts.map fun t => Effect.put (H := H) (.timer t) .timer .any)).2 = true ∧
      (applyAll s (ts.map fun t => Effect.put (H := H) (.timer t) .timer .any)).1.blob?
        (.origin name) = s.blob? (.origin name)
  | [], _ =>
      ⟨rfl, rfl⟩
  | t :: ts, s => by
      obtain ⟨s', hs⟩ := apply_unconditional (e := Effect.put (H := H) (.timer t) .timer .any) rfl s
      simp only [List.map_cons, applyAll, hs]
      obtain ⟨h1, h2⟩ := applyAll_arm name ts s'
      exact ⟨h1, by rw [h2, blob?_put_other hs (by simp)]⟩

theorem applyAll_accepted (s : State) (name : String) (c : Commands) :
    (applyAll s (c.effects name (Cond.of H (s.blob? (.origin name))))).2 = true := by
  unfold Commands.effects
  obtain ⟨h1, h2⟩ := applyAll_arm (H := H) name c.arm s
  simp only [List.append_assoc, List.singleton_append]
  rw [applyAll_append, if_pos h1]
  have key : ∀ s1 : State,
      (Cond.of H (s.blob? (.origin name))).holds (s1.blob? (.origin name)) = true →
      (applyAll s1 (Effect.put (.origin name) (.origin c.put) (Cond.of H (s.blob? (.origin name))) ::
        (c.del.map (fun t => Effect.del (H := H) (.timer t)) ++
         c.send.map (fun (a, m) => Effect.send (H := H) a m)))).2 = true := by
    intro s1 hh
    simp only [applyAll, Effect.apply, hh, ↓reduceIte]
    apply applyAll_unconditional
    intro e he
    simp only [List.mem_append, List.mem_map] at he
    rcases he with ⟨_, _, rfl⟩ | ⟨⟨a, m⟩, _, rfl⟩ <;> rfl
  exact key _ (by rw [h2]; exact Cond.of_holds _)

theorem run_accepted (name : String) (f : Origin → α × Commands) (s : State) :
    (run H name f s).2.2 = true := by
  simp only [run, applyAll_accepted]

theorem step_external_accepted (now : Nat) (s : State) (req : Request) (name : String)
    (h : req.origin? = some name) :
    (step H (.external req) now s).1 = (handle now (s.origin name) (.external req)).1 := by
  simp only [step, h, run, applyAll_accepted, ↓reduceIte]

theorem step_internal_accepted (now : Nat) (s : State) (t : Timer)
    (h : (s.blob? (.timer t)).isSome = true) (hd : t.deadline ≤ now) :
    (step H (.internal t) now s).1 = .internal := by
  simp only [step, h, hd, and_self, ↓reduceIte, run, applyAll_accepted, handle]

end Concrete
