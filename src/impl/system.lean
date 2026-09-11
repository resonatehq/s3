import impl.external
import «02-abstract».«system»

namespace Concrete

open ServerModel (Message OutboxEntry)
open Abstract (Request Response)

inductive Path
  | origin (name : String)
  | timer (t : Timer)
  deriving Repr, DecidableEq

inductive Blob
  | origin (org : Origin)
  | timer
  deriving Repr

abbrev Version := Nat

inductive Cond
  | any
  | absent
  | version (v : Version)
  deriving Repr, DecidableEq

def Cond.holds : Cond → Option Version → Bool
  | .any, _ =>
      true
  | .absent, cur =>
      cur.isNone
  | .version v, cur =>
      cur == some v

def Cond.of : Option Version → Cond
  | some v =>
      .version v
  | none =>
      .absent

structure State where
  bucket : List (Path × Blob × Version) := []
  outbox : List OutboxEntry := []
  next   : Version := 1
  deriving Repr

def State.init : State := {}

def State.get (s : State) (p : Path) : Option (Blob × Version) :=
  (s.bucket.find? (·.1 == p)).map (·.2)

def State.version? (s : State) (p : Path) : Option Version :=
  (s.get p).map (·.2)

def State.origin (s : State) (name : String) : Origin :=
  match s.get (.origin name) with
  | some (.origin org, _) =>
      org
  | _ =>
      {}

inductive Effect
  | put (path : Path) (blob : Blob) (cond : Cond)
  | del (path : Path)
  | send (address : String) (msg : Message)
  deriving Repr

def Effect.apply (s : State) : Effect → Option State
  | .put p b c =>
      if c.holds (s.version? p) then
        some { s with bucket := (p, b, s.next) :: s.bucket.filter (·.1 != p), next := s.next + 1 }
      else
        none
  | .del p =>
      some { s with bucket := s.bucket.filter (·.1 != p) }
  | .send a m =>
      let entry := OutboxEntry.mk a m
      some { s with outbox := entry :: s.outbox.filter (fun e => e.key != entry.key) }

def perform : State → List Effect → State × Bool
  | s, [] =>
      (s, true)
  | s, e :: es =>
      match e.apply s with
      | some s' =>
          perform s' es
      | none =>
          (s, false)

def Commands.effects (name : String) (cond : Cond) (c : Commands) : List Effect :=
  c.arm.map (fun t => .put (.timer t) .timer .any)
  ++ [.put (.origin name) (.origin c.put) cond]
  ++ c.del.map (fun t => .del (.timer t))
  ++ c.send.map (fun (a, m) => .send a m)

def _root_.Abstract.Request.origin? : Request → Option String
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

def handleInternal (_now : Nat) (org : Origin) (_t : Timer) : Commands :=
  { put := org }

def step (ev : Event) (now : Nat) (s : State) : Reply × State :=
  match ev with
  | .external req =>
      match req.origin? with
      | some name =>
          let (res, c) := handleExternal now (s.origin name) req
          let (s', ok) := perform s (c.effects name (Cond.of (s.version? (.origin name))))
          (if ok then .external res else .stutter, s')
      | none =>
          (.external (handleExternal now {} req).1, s)
  | .internal t =>
      if (s.version? (.timer t)).isSome ∧ t.deadline ≤ now then
        let name := t.id.origin
        let c := handleInternal now (s.origin name) t
        let (s', ok) := perform s (c.effects name (Cond.of (s.version? (.origin name))))
        (if ok then .internal else .stutter, s')
      else
        (.stutter, s)
  | .stutter =>
      (.stutter, s)

def exec : List (Event × Nat) → State → List Reply × State
  | [], s =>
      ([], s)
  | (ev, n) :: w, s =>
      let (r, s')   := step ev n s
      let (rs, s'') := exec w s'
      (r :: rs, s'')

structure Frame where
  state : State
  event : Event
  reply : Reply
  now   : Nat

abbrev Trace := Nat → Frame

def Valid (tr : Trace) : Prop :=
  ∀ t : Nat,
    step (tr t).event (tr t).now (tr t).state = ((tr t).reply, (tr (t + 1)).state) ∧
    (tr t).now ≤ (tr (t + 1)).now

theorem Valid.reply {tr : Trace} (hv : Valid tr) (t : Nat) :
    (tr t).reply = (step (tr t).event (tr t).now (tr t).state).1 := by
  rw [(hv t).1]

theorem Valid.state {tr : Trace} (hv : Valid tr) (t : Nat) :
    (tr (t + 1)).state = (step (tr t).event (tr t).now (tr t).state).2 := by
  rw [(hv t).1]

theorem Valid.now {tr : Trace} (hv : Valid tr) (t : Nat) :
    (tr t).now ≤ (tr (t + 1)).now := (hv t).2

theorem Cond.of_holds (v : Option Version) : (Cond.of v).holds v = true := by
  cases v <;> simp [Cond.of, Cond.holds]

def Effect.unconditional : Effect → Bool
  | .put _ _ .any =>
      true
  | .put _ _ _ =>
      false
  | .del _ =>
      true
  | .send _ _ =>
      true

theorem apply_unconditional {e : Effect} (h : e.unconditional = true) (s : State) :
    ∃ s', e.apply s = some s' := by
  cases e with
  | put p b c =>
      cases c <;> simp [Effect.unconditional] at h
      exact ⟨{ s with bucket := (p, b, s.next) :: s.bucket.filter (·.1 != p), next := s.next + 1 },
             by simp [Effect.apply, Cond.holds]⟩
  | del p =>
      exact ⟨_, rfl⟩
  | send a m =>
      exact ⟨_, rfl⟩

theorem perform_unconditional :
    ∀ (es : List Effect) (s : State), (∀ e ∈ es, e.unconditional = true) →
      (perform s es).2 = true
  | [], _, _ =>
      rfl
  | e :: es, s, h => by
      obtain ⟨s', hs⟩ := apply_unconditional (h e (List.mem_cons_self ..)) s
      simp only [perform, hs]
      exact perform_unconditional es s' (fun e he => h e (List.mem_cons_of_mem _ he))

theorem perform_append (a b : List Effect) (s : State) :
    perform s (a ++ b) =
      if (perform s a).2 then perform (perform s a).1 b else perform s a := by
  induction a generalizing s with
  | nil =>
      simp [perform]
  | cons e es ih =>
      simp only [List.cons_append, perform]
      cases e.apply s with
      | some s' =>
          exact ih s'
      | none =>
          simp

theorem version?_put_other {s : State} {p q : Path} {b : Blob} {c : Cond} {s' : State}
    (h : (Effect.put p b c).apply s = some s') (hne : q ≠ p) :
    s'.version? q = s.version? q := by
  simp only [Effect.apply] at h
  split at h
  · cases h
    have hq : ((p, b, s.next).1 == q) = false := by simpa using Ne.symm hne
    simp only [State.version?, State.get, List.find?_cons, hq]
    congr 2
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

theorem perform_arm (name : String) :
    ∀ (ts : List Timer) (s : State),
      (perform s (ts.map fun t => Effect.put (.timer t) .timer .any)).2 = true ∧
      (perform s (ts.map fun t => Effect.put (.timer t) .timer .any)).1.version? (.origin name) =
        s.version? (.origin name)
  | [], _ =>
      ⟨rfl, rfl⟩
  | t :: ts, s => by
      obtain ⟨s', hs⟩ := apply_unconditional (e := .put (.timer t) .timer .any) rfl s
      simp only [List.map_cons, perform, hs]
      obtain ⟨h1, h2⟩ := perform_arm name ts s'
      exact ⟨h1, by rw [h2, version?_put_other hs (by simp)]⟩

theorem effects_accepted (s : State) (name : String) (c : Commands) :
    (perform s (c.effects name (Cond.of (s.version? (.origin name))))).2 = true := by
  unfold Commands.effects
  obtain ⟨h1, h2⟩ := perform_arm name c.arm s
  simp only [List.append_assoc, List.singleton_append]
  rw [perform_append, if_pos h1]
  have key : ∀ s1 : State,
      (Cond.of (s.version? (.origin name))).holds (s1.version? (.origin name)) = true →
      (perform s1 (Effect.put (.origin name) (.origin c.put) (Cond.of (s.version? (.origin name))) ::
        (c.del.map (fun t => Effect.del (.timer t)) ++
         c.send.map (fun (a, m) => Effect.send a m)))).2 = true := by
    intro s1 hh
    simp only [perform, Effect.apply, hh, ↓reduceIte]
    apply perform_unconditional
    intro e he
    simp only [List.mem_append, List.mem_map] at he
    rcases he with ⟨_, _, rfl⟩ | ⟨⟨a, m⟩, _, rfl⟩ <;> rfl
  exact key _ (by rw [h2]; exact Cond.of_holds _)

theorem step_external_accepted (now : Nat) (s : State) (req : Request) (name : String)
    (h : req.origin? = some name) :
    (step (.external req) now s).1 =
      .external (handleExternal now (s.origin name) req).1 := by
  simp only [step, h, effects_accepted, ↓reduceIte]

theorem step_internal_accepted (now : Nat) (s : State) (t : Timer)
    (h : (s.version? (.timer t)).isSome = true) (hd : t.deadline ≤ now) :
    (step (.internal t) now s).1 = .internal := by
  simp only [step, h, hd, and_self, ↓reduceIte, effects_accepted]

end Concrete
