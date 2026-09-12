import «03-theorems».«handlers»

namespace Abstract

open Protocol (PromiseObject TaskObject Object)
namespace Induction

open Abstract

theorem ts_beq (a b : Protocol.TaskState) : (a == b) = decide (a = b) := rfl
theorem ps_beq (a b : Protocol.PromiseState) : (a == b) = decide (a = b) := rfl

theorem all_const {α} : ∀ (l : List α), l.all (fun _ => true) = true
  | [] => rfl
  | _ :: xs => by simp [List.all_cons, all_const xs]

def onlyPromise (f : PromiseObject → Bool) : Q :=
  { promise := fun _ => f, task := fun _ => true, schedule := fun _ => true }

def onlyTask (f : TaskObject → Bool) : Q :=
  { promise := fun _ _ => true, task := f, schedule := fun _ => true }

def onlySchedule (f : Protocol.Schedule → Bool) : Q :=
  { promise := fun _ _ => true, task := fun _ => true, schedule := f }

theorem perStore_onlyPromise {f : PromiseObject → Bool} {s : State} :
    PerStore (onlyPromise f) s = s.promises.all f := by
  rw [PerStore, allObj_split]
  simp [onlyPromise, all_const, State.promises, List.all_map, Function.comp_def]

theorem perStore_onlyTask {f : TaskObject → Bool} {s : State} :
    PerStore (onlyTask f) s = s.tasks.all f := by
  rw [PerStore, allObj_split]
  simp [onlyTask, all_const]

theorem perStore_onlySchedule {f : Protocol.Schedule → Bool} {s : State} :
    PerStore (onlySchedule f) s = s.schedules.all f := by
  rw [PerStore, allObj_split]
  simp [onlySchedule, all_const]

structure HPromise (f : PromiseObject → Bool) : Prop where
  project      : ∀ (p : PromiseObject) (n : Nat), f p = true → f (p.project n) = true
  addCallback  : ∀ (p : PromiseObject) (a : Protocol.Ident), f p = true → f (p.addCallback a) = true
  addListener  : ∀ (p : PromiseObject) (a : String), f p = true → f (p.addListener a) = true
  settle       : ∀ (p : PromiseObject) (st : Protocol.PromiseState)
                   (v : Protocol.Value) (t : Nat),
                   st.settable = true → p.state = .pending → t < p.timeoutAt → f p = true →
                   f { p with state := st, value := v, settledAt := some t } = true
  dropListener : ∀ (p : PromiseObject) (a : String), f p = true →
                   f { p with listeners := p.listeners.filter (· != a) } = true
  dropCallback : ∀ (p : PromiseObject) (a : Protocol.Ident), f p = true →
                   f { p with callbacks := p.callbacks.filter (· != a) } = true
  live         : ∀ (id : Protocol.Ident) (param : Protocol.Value) (type : Protocol.OType)
                   (timeoutAt createdAt : Nat), createdAt < timeoutAt →
                   f { state := .pending, param := param, type := type,
                       timeoutAt := timeoutAt, createdAt := createdAt } = true
  dead         : ∀ (id : Protocol.Ident) (st : Protocol.PromiseState)
                   (param : Protocol.Value) (type : Protocol.OType) (timeoutAt : Nat),
                   st = (if type == .deadline then .resolved else .rejectedTimedout) →
                   f { state := st, param := param, type := type,
                       timeoutAt := timeoutAt, createdAt := timeoutAt,
                       settledAt := some timeoutAt } = true

theorem hereditary_onlyPromise {f : PromiseObject → Bool} (h : HPromise f)
    (a : State) : Hereditary (onlyPromise f) a where
  project _ p n _ := h.project p n
  addCallback _ p c _ := h.addCallback p c
  addListener _ p c _ := h.addListener p c
  settle _ p st v t _ := h.settle p st v t
  dropListener _ p c _ _ := h.dropListener p c
  dropCallback _ p c _ _ := h.dropCallback p c
  live := fun id param type tAt cAt hlt _ => h.live id param type tAt cAt hlt
  dead := fun id st param type tAt hst _ => h.dead id st param type tAt hst
  tFulfill _ _ := rfl
  tBornPending _ := rfl
  tBornDone := rfl
  tBornHeld _ _ _ := rfl
  tAcquire _ _ _ _ _ := rfl
  tHeartbeat _ _ _ _ := rfl
  tClearResumes _ _ := rfl
  tSuspend _ _ := rfl
  tRepend _ _ _ := rfl
  tHalt _ _ := rfl
  tContinue _ _ _ _ := rfl
  tResume _ _ _ _ _ := rfl
  tAddResume _ _ _ _ _ _ := rfl
  tRearm _ _ _ _ := rfl
  cBorn _ _ _ _ _ _ _ := rfl
  cAdvance _ _ _ := rfl

theorem promise_step {f : PromiseObject → Bool} (h : HPromise f)
    (mat : Bool) (st : Event) (now : Nat) (s : State) :
    s.promises.all f = true → (step mat st now s).2.promises.all f = true := by
  intro hf
  have := perStore_step mat st now s (hereditary_onlyPromise h s)
    (by rw [perStore_onlyPromise]; exact hf)
  rwa [perStore_onlyPromise] at this

structure HTask (f : TaskObject → Bool) : Prop where
  fulfill    : ∀ (t : TaskObject), f t = true → f t.fulfill = true
  bornPending : ∀ (due : Nat),
                  f { state := .pending, version := 0, retryTimeoutAt := some due } = true
  bornDone   : f { state := .fulfilled, version := 0 } = true
  bornHeld   : ∀ (pid : String) (ttl now : Nat),
                 f { state := .acquired, version := 1, ttl := some ttl, pid := some pid, leaseTimeoutAt := some (now + ttl) } = true
  acquire    : ∀ (t : TaskObject) (pid : String) (ttl now : Nat), f t = true →
                 f { t with state := .acquired, version := t.version + 1, ttl := some ttl, pid := some pid, leaseTimeoutAt := some (now + ttl), retryTimeoutAt := none, resumes := [] } = true
  heartbeat  : ∀ (t : TaskObject) (x : Nat), (t.state == .acquired) = true →
                 f t = true → f { t with leaseTimeoutAt := some x } = true
  clearResumes : ∀ (t : TaskObject), f t = true → f { t with resumes := [] } = true
  suspend    : ∀ (t : TaskObject), f t = true →
                 f { t with state := .suspended, pid := none, ttl := none, leaseTimeoutAt := none, retryTimeoutAt := none, resumes := [] } = true
  repend     : ∀ (t : TaskObject) (n : Nat), f t = true →
                 f { t with state := .pending, pid := none, ttl := none, leaseTimeoutAt := none, retryTimeoutAt := some n } = true
  halt       : ∀ (t : TaskObject), f t = true →
                 f { t with state := .halted, pid := none, ttl := none, leaseTimeoutAt := none, retryTimeoutAt := none } = true
  cont       : ∀ (t : TaskObject) (n : Nat), (t.state == .halted) = true → f t = true →
                 f { t with state := .pending, retryTimeoutAt := some n } = true
  resume     : ∀ (t : TaskObject) (a : Protocol.Ident) (n : Nat), t.state = .suspended → f t = true →
                 f { t with state := .pending, resumes := [a], retryTimeoutAt := some n } = true
  addResume  : ∀ (t : TaskObject) (a : Protocol.Ident), t.state ≠ .suspended → t.state ≠ .fulfilled →
                 (t.resumes.contains a) = false → f t = true →
                 f { t with resumes := t.resumes ++ [a] } = true
  rearm      : ∀ (t : TaskObject) (n : Nat), (t.state == .pending) = true → f t = true →
                 f { t with retryTimeoutAt := some n } = true

theorem hereditary_onlyTask {f : TaskObject → Bool} (h : HTask f)
    (a : State) : Hereditary (onlyTask f) a where
  project _ _ _ _ _ := rfl
  addCallback _ _ _ _ _ := rfl
  addListener _ _ _ _ _ := rfl
  settle _ _ _ _ _ _ _ _ _ _ := rfl
  dropListener _ _ _ _ _ _ := rfl
  dropCallback _ _ _ _ _ _ := rfl
  live _ _ _ _ _ _ _ := rfl
  dead _ _ _ _ _ _ _ := rfl
  tFulfill := h.fulfill
  tBornPending := h.bornPending
  tBornDone := h.bornDone
  tBornHeld := h.bornHeld
  tAcquire := h.acquire
  tHeartbeat := h.heartbeat
  tClearResumes := h.clearResumes
  tSuspend := h.suspend
  tRepend := h.repend
  tHalt := h.halt
  tContinue := h.cont
  tResume := h.resume
  tAddResume := h.addResume
  tRearm := h.rearm
  cBorn _ _ _ _ _ _ _ := rfl
  cAdvance _ _ _ := rfl

theorem task_step {f : TaskObject → Bool} (h : HTask f)
    (mat : Bool) (st : Event) (now : Nat) (s : State) :
    s.tasks.all f = true → (step mat st now s).2.tasks.all f = true := by
  intro hf
  have := perStore_step mat st now s (hereditary_onlyTask h s)
    (by rw [perStore_onlyTask]; exact hf)
  rwa [perStore_onlyTask] at this

structure HSchedule (f : Protocol.Schedule → Bool) : Prop where
  born    : ∀ (id : Protocol.Ident) (cron : String) (promiseId : Protocol.Ident) (promiseTimeout : Nat)
              (promiseParam : Protocol.Value) (promiseType : Protocol.OType)
              (now : Nat),
              f { id := id, cron := cron, promiseId := promiseId,
                  promiseTimeout := promiseTimeout, promiseParam := promiseParam,
                  promiseType := promiseType, createdAt := now,
                  nextRunAt := Protocol.nextCron cron now, lastRunAt := none } = true
  advance : ∀ (c : Protocol.Schedule) (last : Nat), f c = true →
              f { c with lastRunAt := some last, nextRunAt := Protocol.nextCron c.cron last } = true

theorem hereditary_onlySchedule {f : Protocol.Schedule → Bool} (h : HSchedule f)
    (a : State) : Hereditary (onlySchedule f) a where
  project _ _ _ _ _ := rfl
  addCallback _ _ _ _ _ := rfl
  addListener _ _ _ _ _ := rfl
  settle _ _ _ _ _ _ _ _ _ _ := rfl
  dropListener _ _ _ _ _ _ := rfl
  dropCallback _ _ _ _ _ _ := rfl
  live _ _ _ _ _ _ _ := rfl
  dead _ _ _ _ _ _ _ := rfl
  tFulfill _ _ := rfl
  tBornPending _ := rfl
  tBornDone := rfl
  tBornHeld _ _ _ := rfl
  tAcquire _ _ _ _ _ := rfl
  tHeartbeat _ _ _ _ := rfl
  tClearResumes _ _ := rfl
  tSuspend _ _ := rfl
  tRepend _ _ _ := rfl
  tHalt _ _ := rfl
  tContinue _ _ _ _ := rfl
  tResume _ _ _ _ _ := rfl
  tAddResume _ _ _ _ _ _ := rfl
  tRearm _ _ _ _ := rfl
  cBorn := h.born
  cAdvance := h.advance

theorem schedule_step {f : Protocol.Schedule → Bool} (h : HSchedule f)
    (mat : Bool) (st : Event) (now : Nat) (s : State) :
    s.schedules.all f = true → (step mat st now s).2.schedules.all f = true := by
  intro hf
  have := perStore_step mat st now s (hereditary_onlySchedule h s)
    (by rw [perStore_onlySchedule]; exact hf)
  rwa [perStore_onlySchedule] at this

def qCreatedLeTimeout (p : PromiseObject) : Bool := p.createdAt ≤ p.timeoutAt

theorem hp_createdLeTimeout : HPromise qCreatedLeTimeout where
  project p n h := by
    unfold PromiseObject.project
    split
    · split <;> simpa [qCreatedLeTimeout] using h
    · simpa [qCreatedLeTimeout] using h
  addCallback p a h := by
    unfold PromiseObject.addCallback
    split <;> simpa [qCreatedLeTimeout] using h
  addListener p a h := by
    unfold PromiseObject.addListener
    split <;> simpa [qCreatedLeTimeout] using h
  settle p st v t _ _ _ h := by simpa [qCreatedLeTimeout] using h
  dropListener p a h := by simpa [qCreatedLeTimeout] using h
  dropCallback p a h := by simpa [qCreatedLeTimeout] using h
  live id param type timeoutAt createdAt h := by simp [qCreatedLeTimeout]; omega
  dead id st param type timeoutAt _ := by simp [qCreatedLeTimeout]

def qPendingBeforeDeadline (p : PromiseObject) : Bool :=
  p.state != .pending || p.createdAt < p.timeoutAt

theorem hp_pendingBeforeDeadline : HPromise qPendingBeforeDeadline where
  project p n h := by
    unfold PromiseObject.project
    split
    · split <;> simp [qPendingBeforeDeadline]
    · simpa [qPendingBeforeDeadline] using h
  addCallback p a h := by
    unfold PromiseObject.addCallback
    split <;> simpa [qPendingBeforeDeadline] using h
  addListener p a h := by
    unfold PromiseObject.addListener
    split <;> simpa [qPendingBeforeDeadline] using h
  settle p st v t hst _ _ _ := by
    cases st <;> simp_all [qPendingBeforeDeadline, Protocol.PromiseState.settable]
  dropListener p a h := by simpa [qPendingBeforeDeadline] using h
  dropCallback p a h := by simpa [qPendingBeforeDeadline] using h
  live id param type timeoutAt createdAt h := by simp [qPendingBeforeDeadline]; omega
  dead id st param type timeoutAt hst := by subst hst; split <;> simp [qPendingBeforeDeadline]

def qSettledIffStamped (p : PromiseObject) : Bool :=
  (p.state != .pending) == p.settledAt.isSome

theorem hp_settledIffStamped : HPromise qSettledIffStamped where
  project p n h := by
    unfold PromiseObject.project
    split
    · split <;> simp [qSettledIffStamped]
    · simpa [qSettledIffStamped] using h
  addCallback p a h := by
    unfold PromiseObject.addCallback
    split <;> simpa [qSettledIffStamped] using h
  addListener p a h := by
    unfold PromiseObject.addListener
    split <;> simpa [qSettledIffStamped] using h
  settle p st v t hst _ _ _ := by
    cases st <;> simp_all [qSettledIffStamped, Protocol.PromiseState.settable]
  dropListener p a h := by simpa [qSettledIffStamped] using h
  dropCallback p a h := by simpa [qSettledIffStamped] using h
  live id param type timeoutAt createdAt h := by simp [qSettledIffStamped]
  dead id st param type timeoutAt hst := by subst hst; split <;> simp [qSettledIffStamped]

def qTimedoutIsServerOwned (p : PromiseObject) : Bool :=
  p.state != .rejectedTimedout || p.settledAt == some p.timeoutAt

theorem hp_timedoutIsServerOwned : HPromise qTimedoutIsServerOwned where
  project p n h := by
    unfold PromiseObject.project
    split
    · split <;> simp [qTimedoutIsServerOwned]
    · simpa [qTimedoutIsServerOwned] using h
  addCallback p a h := by
    unfold PromiseObject.addCallback
    split <;> simpa [qTimedoutIsServerOwned] using h
  addListener p a h := by
    unfold PromiseObject.addListener
    split <;> simpa [qTimedoutIsServerOwned] using h
  settle p st v t hst _ _ _ := by
    cases st <;> simp_all [qTimedoutIsServerOwned, Protocol.PromiseState.settable]
  dropListener p a h := by simpa [qTimedoutIsServerOwned] using h
  dropCallback p a h := by simpa [qTimedoutIsServerOwned] using h
  live id param type timeoutAt createdAt h := by simp [qTimedoutIsServerOwned]
  dead id st param type timeoutAt hst := by subst hst; split <;> simp [qTimedoutIsServerOwned]

def qSettledAtLeTimeout (p : PromiseObject) : Bool :=
  match p.settledAt with
  | none => true
  | some x => x ≤ p.timeoutAt

theorem hp_settledAtLeTimeout : HPromise qSettledAtLeTimeout where
  project p n h := by
    unfold PromiseObject.project
    split
    · split <;> simp [qSettledAtLeTimeout]
    · simpa [qSettledAtLeTimeout] using h
  addCallback p a h := by
    unfold PromiseObject.addCallback
    split <;> simpa [qSettledAtLeTimeout] using h
  addListener p a h := by
    unfold PromiseObject.addListener
    split <;> simpa [qSettledAtLeTimeout] using h
  settle p st v t _ _ hdue _ := by simp [qSettledAtLeTimeout]; omega
  dropListener p a h := by simpa [qSettledAtLeTimeout] using h
  dropCallback p a h := by simpa [qSettledAtLeTimeout] using h
  live id param type timeoutAt createdAt h := by simp [qSettledAtLeTimeout]
  dead id st param type timeoutAt hst := by subst hst; split <;> simp [qSettledAtLeTimeout]

def qDeadlineVerdict (p : PromiseObject) : Bool :=
  p.settledAt != some p.timeoutAt
    || p.state == (if p.type == .deadline then .resolved else .rejectedTimedout)

theorem hp_deadlineVerdict : HPromise qDeadlineVerdict where
  project p n h := by
    unfold PromiseObject.project
    split
    · split <;> rename_i ht <;> simp_all [qDeadlineVerdict]
    · simpa [qDeadlineVerdict] using h
  addCallback p a h := by
    unfold PromiseObject.addCallback
    split <;> simpa [qDeadlineVerdict] using h
  addListener p a h := by
    unfold PromiseObject.addListener
    split <;> simpa [qDeadlineVerdict] using h
  settle p st v t _ _ hdue _ := by simp [qDeadlineVerdict]; omega
  dropListener p a h := by simpa [qDeadlineVerdict] using h
  dropCallback p a h := by simpa [qDeadlineVerdict] using h
  live id param type timeoutAt createdAt h := by simp [qDeadlineVerdict]
  dead id st param type timeoutAt hst := by subst hst; split <;> simp_all [qDeadlineVerdict]

def qNoValueUnlessSettled (p : PromiseObject) : Bool :=
  (p.state != .pending || (p.value.data.isNone && p.value.headers.isEmpty))
    && (p.settledAt != some p.timeoutAt || (p.value.data.isNone && p.value.headers.isEmpty))

theorem hp_noValueUnlessSettled : HPromise qNoValueUnlessSettled where
  project p n h := by
    unfold PromiseObject.project
    split
    · rename_i hc
      have hv : p.value.data.isNone && p.value.headers.isEmpty = true := by
        simp only [qNoValueUnlessSettled, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne] at h
        rcases h.1 with h1 | h1
        · exact absurd hc.1 (by simp_all)
        · simpa using h1
      split <;> simp_all [qNoValueUnlessSettled]
    · simpa [qNoValueUnlessSettled] using h
  addCallback p a h := by
    unfold PromiseObject.addCallback
    split <;> simpa [qNoValueUnlessSettled] using h
  addListener p a h := by
    unfold PromiseObject.addListener
    split <;> simpa [qNoValueUnlessSettled] using h
  settle p st v t hst _ hdue _ := by
    cases st <;>
      simp_all [qNoValueUnlessSettled, Protocol.PromiseState.settable] <;> omega
  dropListener p a h := by simpa [qNoValueUnlessSettled] using h
  dropCallback p a h := by simpa [qNoValueUnlessSettled] using h
  live id param type timeoutAt createdAt h := by simp [qNoValueUnlessSettled]
  dead id st param type timeoutAt hst := by subst hst; split <;> simp [qNoValueUnlessSettled]

def qTaskShape (t : TaskObject) : Bool :=
  ((t.state == .acquired) == t.pid.isSome)
    && ((t.state == .acquired) == t.ttl.isSome)
    && ((t.state == .acquired) == t.leaseTimeoutAt.isSome)
    && ((t.state == .pending) == t.retryTimeoutAt.isSome)
    && (t.state != .fulfilled
        || (t.pid.isNone && t.ttl.isNone && t.leaseTimeoutAt.isNone && t.retryTimeoutAt.isNone
            && t.resumes.isEmpty))
    && (t.state != .suspended
        || (t.pid.isNone && t.ttl.isNone && t.leaseTimeoutAt.isNone && t.retryTimeoutAt.isNone))
    && (t.state != .halted
        || (t.pid.isNone && t.ttl.isNone && t.leaseTimeoutAt.isNone && t.retryTimeoutAt.isNone))
    && (t.state != .suspended || t.resumes.isEmpty)
    && (t.state != .acquired || 1 ≤ t.version)

theorem ht_taskShape : HTask qTaskShape where
  fulfill t h := by simp [qTaskShape, TaskObject.fulfill]
  bornPending due := by simp [qTaskShape]
  bornDone := by simp [qTaskShape]
  bornHeld pid ttl now := by simp [qTaskShape]
  acquire t pid ttl now h := by simp [qTaskShape]
  heartbeat t x hacq h := by cases hst : t.state <;> simp_all [qTaskShape, ts_beq]
  clearResumes t h := by cases hst : t.state <;> simp_all [qTaskShape, ts_beq]
  suspend t h := by simp [qTaskShape]
  repend t n h := by cases hst : t.state <;> simp_all [qTaskShape, ts_beq]
  halt t h := by cases hst : t.state <;> simp_all [qTaskShape, ts_beq]
  cont t n hhalt h := by cases hst : t.state <;> simp_all [qTaskShape, ts_beq]
  resume t a n hsusp h := by cases hst : t.state <;> simp_all [qTaskShape, ts_beq]
  addResume t a hns hnf hc h := by cases hst : t.state <;> simp_all [qTaskShape, ts_beq]
  rearm t n hpend h := by cases hst : t.state <;> simp_all [qTaskShape, ts_beq]

section Entries

open Properties

theorem created_at_lte_timeout_at_init (now : Nat) :
    well_formed_promise_created_at_lte_timeout_at now State.init = true := rfl

theorem created_at_lte_timeout_at_step (mat : Bool) (st : Event) (now n' : Nat)
    (s : State) :
    well_formed_promise_created_at_lte_timeout_at now s = true →
    well_formed_promise_created_at_lte_timeout_at n' (step mat st now s).2 = true :=
  promise_step hp_createdLeTimeout mat st now s

theorem pending_created_before_deadline_init (now : Nat) :
    well_formed_promise_pending_created_before_deadline now State.init = true := rfl

theorem pending_created_before_deadline_step (mat : Bool) (st : Event) (now n' : Nat)
    (s : State) :
    well_formed_promise_pending_created_before_deadline now s = true →
    well_formed_promise_pending_created_before_deadline n' (step mat st now s).2 = true :=
  promise_step hp_pendingBeforeDeadline mat st now s

theorem settled_at_iff_not_pending_init (now : Nat) :
    well_formed_promise_settled_at_iff_not_pending now State.init = true := rfl

theorem settled_at_iff_not_pending_step (mat : Bool) (st : Event) (now n' : Nat)
    (s : State) :
    well_formed_promise_settled_at_iff_not_pending now s = true →
    well_formed_promise_settled_at_iff_not_pending n' (step mat st now s).2 = true :=
  promise_step hp_settledIffStamped mat st now s

theorem timedout_is_server_owned_init (now : Nat) :
    well_formed_promise_timedout_is_server_owned now State.init = true := rfl

theorem timedout_is_server_owned_step (mat : Bool) (st : Event) (now n' : Nat)
    (s : State) :
    well_formed_promise_timedout_is_server_owned now s = true →
    well_formed_promise_timedout_is_server_owned n' (step mat st now s).2 = true :=
  promise_step hp_timedoutIsServerOwned mat st now s

theorem settled_at_lte_timeout_at_init (now : Nat) :
    well_formed_promise_settled_at_lte_timeout_at now State.init = true := rfl

theorem settled_at_lte_timeout_at_step (mat : Bool) (st : Event) (now n' : Nat)
    (s : State) :
    well_formed_promise_settled_at_lte_timeout_at now s = true →
    well_formed_promise_settled_at_lte_timeout_at n' (step mat st now s).2 = true :=
  promise_step hp_settledAtLeTimeout mat st now s

theorem deadline_verdict_matches_timer_tag_init (now : Nat) :
    well_formed_promise_deadline_verdict_matches_timer_tag now State.init = true := rfl

theorem deadline_verdict_matches_timer_tag_step (mat : Bool) (st : Event) (now n' : Nat)
    (s : State) :
    well_formed_promise_deadline_verdict_matches_timer_tag now s = true →
    well_formed_promise_deadline_verdict_matches_timer_tag n' (step mat st now s).2 = true :=
  promise_step hp_deadlineVerdict mat st now s

theorem no_value_unless_settled_init :
    State.init.promises.all qNoValueUnlessSettled = true := rfl

theorem no_value_unless_settled_step (mat : Bool) (st : Event) (now : Nat) (s : State) :
    s.promises.all qNoValueUnlessSettled = true →
    (step mat st now s).2.promises.all qNoValueUnlessSettled = true :=
  promise_step hp_noValueUnlessSettled mat st now s

theorem pending_has_no_value_of_strengthening (now : Nat) (s : State) :
    s.promises.all qNoValueUnlessSettled = true →
    well_formed_promise_pending_has_no_value now s = true :=
  all_mono (fun _ h => (Bool.and_eq_true _ _ |>.mp h).1) _

theorem deadline_settlement_has_no_value_of_strengthening (now : Nat) (s : State) :
    s.promises.all qNoValueUnlessSettled = true →
    well_formed_promise_deadline_settlement_has_no_value now s = true :=
  all_mono (fun _ h => (Bool.and_eq_true _ _ |>.mp h).2) _

theorem task_shape_init : State.init.tasks.all qTaskShape = true := rfl

theorem task_shape_step (mat : Bool) (st : Event) (now : Nat) (s : State) :
    s.tasks.all qTaskShape = true → (step mat st now s).2.tasks.all qTaskShape = true :=
  task_step ht_taskShape mat st now s

theorem task_acquired_iff_has_pid_of_shape (now : Nat) (s : State) :
    s.tasks.all qTaskShape = true → well_formed_task_acquired_iff_has_pid now s = true :=
  all_mono (fun _ h => by
    simp only [qTaskShape, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.1) _

theorem task_acquired_iff_has_ttl_of_shape (now : Nat) (s : State) :
    s.tasks.all qTaskShape = true → well_formed_task_acquired_iff_has_ttl now s = true :=
  all_mono (fun _ h => by
    simp only [qTaskShape, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.2) _

theorem task_acquired_iff_has_lease_timeout_at_of_shape (now : Nat) (s : State) :
    s.tasks.all qTaskShape = true → well_formed_task_acquired_iff_has_lease_timeout_at now s = true :=
  all_mono (fun _ h => by
    simp only [qTaskShape, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.2) _

theorem task_pending_iff_has_retry_timeout_at_of_shape (now : Nat) (s : State) :
    s.tasks.all qTaskShape = true → well_formed_task_pending_iff_has_retry_timeout_at now s = true :=
  all_mono (fun _ h => by
    simp only [qTaskShape, Bool.and_eq_true] at h; exact h.1.1.1.1.1.2) _

theorem task_fulfilled_is_cleared_of_shape (now : Nat) (s : State) :
    s.tasks.all qTaskShape = true → well_formed_task_fulfilled_is_cleared now s = true :=
  all_mono (fun _ h => by
    simp only [qTaskShape, Bool.and_eq_true] at h; exact h.1.1.1.1.2) _

theorem task_suspended_is_cleared_of_shape (now : Nat) (s : State) :
    s.tasks.all qTaskShape = true → well_formed_task_suspended_is_cleared now s = true :=
  all_mono (fun _ h => by
    simp only [qTaskShape, Bool.and_eq_true] at h; exact h.1.1.1.2) _

theorem task_halted_is_cleared_of_shape (now : Nat) (s : State) :
    s.tasks.all qTaskShape = true → well_formed_task_halted_is_cleared now s = true :=
  all_mono (fun _ h => by
    simp only [qTaskShape, Bool.and_eq_true] at h; exact h.1.1.2) _

theorem task_suspended_has_no_resumes_of_shape (now : Nat) (s : State) :
    s.tasks.all qTaskShape = true → well_formed_task_suspended_has_no_resumes now s = true :=
  all_mono (fun _ h => by
    simp only [qTaskShape, Bool.and_eq_true] at h; exact h.1.2) _

theorem task_acquired_version_positive_of_shape (now : Nat) (s : State) :
    s.tasks.all qTaskShape = true → well_formed_task_acquired_version_positive now s = true :=
  all_mono (fun _ h => by
    simp only [qTaskShape, Bool.and_eq_true] at h; exact h.2) _

end Entries

end Induction
end Abstract
