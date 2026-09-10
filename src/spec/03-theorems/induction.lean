import «03-theorems».«system»
import «03-theorems».«lookup»
import «02-abstract».«properties»

set_option maxHeartbeats 400000

namespace Abstraction
namespace Induction

open AbstractModel

def EffectStable (P : ServerState → Bool) : Prop :=
  ∀ (e : Effect) (s : ServerState), P s = true → P (e.apply s) = true

theorem applyAll_preserves {P : ServerState → Bool} (h : EffectStable P) :
    ∀ (w : List Effect) (s : ServerState), P s = true → P (applyAll s w) = true
  | [],      _, hs => hs
  | e :: es, s, hs => applyAll_preserves h es (e.apply s) (h e s hs)

theorem step_preserves {P : ServerState → Bool} (h : EffectStable P)
    (mat : Bool) (st : Step) (now : Nat) (s : ServerState) :
    P s = true → P (stepOf mat st now s).2 = true := by
  intro hs
  show P (applyAll s ((handle st now) { state := s, mat := mat }).2) = true
  exact applyAll_preserves h _ s hs

structure Q where

  promise  : ServerModel.Ident → PromiseObject → Bool
  task     : TaskObject → Bool
  schedule : ServerModel.Schedule → Bool

def QObj (g : Q) (o : Object) : Bool := g.promise o.id o.promise && o.task.all g.task

theorem QObj_promise {g : Q} {o : Object} (h : QObj g o = true) :
    g.promise o.id o.promise = true := by
  simp only [QObj, Bool.and_eq_true] at h; exact h.1

theorem QObj_task {g : Q} {o : Object} {t : TaskObject} (h : QObj g o = true)
    (ht : o.task = some t) : g.task t = true := by
  simp only [QObj, Bool.and_eq_true] at h
  simpa [ht] using h.2

theorem all_filterMap {α β} (q : β → Bool) (m : α → Option β) :
    ∀ l : List α, (l.filterMap m).all q = l.all (fun a => (m a).all q)
  | [] => rfl
  | a :: l => by
      cases h : m a with
      | none   => simp [List.filterMap_cons, h, all_filterMap q m l]
      | some b => simp [List.filterMap_cons, h, List.all_cons, all_filterMap q m l]

theorem all_and {α} (p q : α → Bool) :
    ∀ l : List α, l.all (fun a => p a && q a) = (l.all p && l.all q)
  | [] => rfl
  | a :: l => by
      simp only [List.all_cons, all_and p q l]
      cases p a <;> cases q a <;> simp

theorem allObj_split (g : Q) (s : ServerState) :
    s.objects.all (QObj g)
      = ((s.objects.all fun o => g.promise o.id o.promise) && s.tasks.all g.task) := by
  simp only [ServerState.tasks, all_filterMap, ← all_and]
  rfl

def PerStore (g : Q) (s : ServerState) : Bool :=
  s.objects.all (QObj g) && s.schedules.all g.schedule

theorem perStore_promises {g : Q} {s : ServerState} (h : PerStore g s = true) :
    (s.objects.all fun o => g.promise o.id o.promise) = true := by
  simp only [PerStore, allObj_split, Bool.and_eq_true] at h; exact h.1.1

theorem perStore_tasks {g : Q} {s : ServerState} (h : PerStore g s = true) :
    s.tasks.all g.task = true := by
  simp only [PerStore, allObj_split, Bool.and_eq_true] at h; exact h.1.2

theorem perStore_objects {g : Q} {s : ServerState} (h : PerStore g s = true) :
    s.objects.all (QObj g) = true := by
  simp only [PerStore, Bool.and_eq_true] at h; exact h.1

theorem perStore_schedules {g : Q} {s : ServerState} (h : PerStore g s = true) :
    s.schedules.all g.schedule = true := by
  simp only [PerStore, Bool.and_eq_true] at h; exact h.2

theorem perStore_mk {g : Q} {s : ServerState}
    (h1 : (s.objects.all fun o => g.promise o.id o.promise) = true)
    (h2 : s.tasks.all g.task = true)
    (h3 : s.schedules.all g.schedule = true) : PerStore g s = true := by
  simp [PerStore, allObj_split, h1, h2, h3]

theorem perStore_mkObj {g : Q} {s : ServerState}
    (h1 : s.objects.all (QObj g) = true) (h3 : s.schedules.all g.schedule = true) :
    PerStore g s = true := by
  simp [PerStore, h1, h3]

def GoodEffect (g : Q) : Effect → Prop
  | .setPromise id p => g.promise id p = true
  | .setTask _ t    => g.task t = true
  | .setSchedule c  => g.schedule c = true
  | .delSchedule _  => True
  | .setMessage _ _ => True

theorem all_filter {α} (q : α → Bool) (f : α → Bool) :
    ∀ l : List α, l.all q = true → (l.filter f).all q = true
  | [],     _ => rfl
  | a :: l, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      by_cases hf : f a = true <;>
        simp [hf, List.all_cons, h.1, all_filter q f l h.2]

theorem all_upsert {α} (q : α → Bool) (x : α) (f : α → Bool) (l : List α)
    (hl : l.all q = true) (hx : q x = true) : ((x :: l.filter f).all q) = true := by
  simp [List.all_cons, hx, all_filter q f l hl]

theorem all_map_of {α} (q : α → Bool) (m : α → α)
    (hm : ∀ a, q a = true → q (m a) = true) :
    ∀ l : List α, l.all q = true → (l.map m).all q = true
  | [],     _ => rfl
  | a :: l, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      simp [List.map_cons, List.all_cons, hm a h.1, all_map_of q m hm l h.2]

theorem perStore_apply (g : Q) (f : Effect) (s : ServerState)
    (hs : PerStore g s = true) (hf : GoodEffect g f) :
    PerStore g (f.apply s) = true := by
  have ho := perStore_objects hs
  have h3 := perStore_schedules hs
  cases f with
  | setPromise id p =>
      have hf' : g.promise id p = true := hf
      refine perStore_mkObj (all_upsert _ _ _ _ ho ?_) h3
      cases hfind : s.objects.find? (·.id == id) with
      | none => simpa [Object.withPromise, QObj] using hf'
      | some o =>
          have hoid : o.id = id := eq_of_beq (by simpa using List.find?_some hfind)
          have hq : QObj g o = true :=
            List.all_eq_true.mp ho o (List.mem_of_find?_eq_some hfind)
          simp only [QObj, Bool.and_eq_true] at hq ⊢
          exact ⟨by simpa [Object.withPromise, hoid] using hf',
                 by simpa [Object.withPromise] using hq.2⟩
  | setTask id t =>
      refine perStore_mkObj (all_map_of _ _ (fun o hq => ?_) _ ho) h3
      by_cases hid : (o.id == id) = true
      · simp only [QObj, Bool.and_eq_true] at hq ⊢
        simpa [hid] using ⟨hq.1, hf⟩
      · simpa [hid] using hq
  | setSchedule c =>
      exact perStore_mkObj ho (all_upsert _ c _ _ h3 hf)
  | delSchedule i =>
      exact perStore_mkObj ho (all_filter _ _ _ h3)
  | setMessage a m =>
      exact perStore_mkObj ho h3

theorem perStore_applyAll (g : Q) :
    ∀ (w : List Effect) (s : ServerState), PerStore g s = true →
      (∀ f ∈ w, GoodEffect g f) → PerStore g (applyAll s w) = true
  | [],      _, hs, _  => hs
  | f :: fs, s, hs, hw =>
      perStore_applyAll g fs (f.apply s)
        (perStore_apply g f s hs (hw f (by simp)))
        (fun k hk => hw k (by simp [hk]))

theorem all_mono {α} {q r : α → Bool} (h : ∀ x, q x = true → r x = true)
    (l : List α) : l.all q = true → l.all r = true := fun hs =>
  List.all_eq_true.mpr (fun x hx => h x (List.all_eq_true.mp hs x hx))

theorem getObject_sound {g : Q} {s : ServerState} {id : ServerModel.Ident} {o : Object}
    (hs : PerStore g s = true)
    (h : s.objects.find? (·.id == id) = some o) : QObj g o = true :=
  List.all_eq_true.mp (perStore_objects hs) o (List.mem_of_find?_eq_some h)

theorem getPromise_sound {g : Q} {s : ServerState} {id : ServerModel.Ident} {o : Object}
    (hs : PerStore g s = true)
    (h : s.objects.find? (·.id == id) = some o) : g.promise o.id o.promise = true :=
  QObj_promise (getObject_sound hs h)

theorem getTask_sound {g : Q} {s : ServerState} {id : ServerModel.Ident} {t : TaskObject}
    (hs : PerStore g s = true)
    (h : s.task? id = some t) : g.task t = true := by
  unfold ServerState.task? at h
  cases hfind : s.objects.find? (·.id == id) with
  | none => rw [hfind] at h; simp at h
  | some o =>
      rw [hfind] at h
      simp only [Option.bind_some] at h
      have hq := getObject_sound hs hfind
      simp only [QObj, Bool.and_eq_true] at hq
      simpa [h] using hq.2

theorem getSchedule_sound {g : Q} {s : ServerState} {id : ServerModel.Ident}
    {c : ServerModel.Schedule} (hs : PerStore g s = true)
    (h : s.schedules.find? (·.id == id) = some c) : g.schedule c = true :=
  List.all_eq_true.mp (perStore_schedules hs) c (List.mem_of_find?_eq_some h)

def WritesGood (g : Q) (e : Env) {α : Type} (act : H α) : Prop :=
  ∀ f ∈ (act e).2, GoodEffect g f

def ReturnsGood (g : Q) (e : Env) (act : H (Option Object)) : Prop :=
  ∀ o, (act e).1 = some o → QObj g o = true

theorem writesGood_pure {α} (g : Q) (e : Env) (a : α) : WritesGood g e (pure a) := by
  intro f hf; simp [pure] at hf

theorem writesGood_setPromise (g : Q) (e : Env) (id : ServerModel.Ident) (p : PromiseObject)
    (h : g.promise id p = true) : WritesGood g e (setPromise id p) := by
  intro f hf; simp [setPromise, emit] at hf; subst hf; exact h

theorem writesGood_setTask (g : Q) (e : Env) (id : ServerModel.Ident) (t : TaskObject)
    (h : g.task t = true) : WritesGood g e (setTask id t) := by
  intro f hf; simp [setTask, emit] at hf; subst hf; exact h

theorem writesGood_setSchedule (g : Q) (e : Env) (c : ServerModel.Schedule)
    (h : g.schedule c = true) : WritesGood g e (setSchedule c) := by
  intro f hf; simp [setSchedule, emit] at hf; subst hf; exact h

theorem writesGood_setMessage (g : Q) (e : Env) (a : String) (m : ServerModel.Message) :
    WritesGood g e (setMessage a m) := by
  intro f hf; simp [setMessage, emit] at hf; subst hf; trivial

theorem writesGood_delSchedule (g : Q) (e : Env) (id : ServerModel.Ident) :
    WritesGood g e (delSchedule id) := by
  intro f hf; simp [delSchedule, emit] at hf; subst hf; trivial

theorem writesGood_ask (g : Q) (e : Env) : WritesGood g e ask := by
  intro f hf; simp [ask] at hf

theorem writesGood_getObject (g : Q) (e : Env) (id : ServerModel.Ident) :
    WritesGood g e (getObject id) := by
  intro f hf; simp [getObject, bind, ask, pure] at hf

theorem writesGood_getSchedule (g : Q) (e : Env) (id : ServerModel.Ident) :
    WritesGood g e (getSchedule id) := by
  intro f hf; simp [getSchedule, bind, ask, pure] at hf

theorem writesGood_withMat {α} (g : Q) (e : Env) (b : Bool)
    (act : H α) (h : WritesGood g { e with mat := b } act) :
    WritesGood g e (withMat b act) := h

def Stored (a : ServerState) (id : ServerModel.Ident) : Prop :=
  a.objects.find? (·.id == id) ≠ none

theorem stored_of_find? {a : ServerState} {id : ServerModel.Ident} {o : Object}
    (h : a.objects.find? (·.id == id) = some o) : Stored a id := by
  unfold Stored; rw [h]; simp

structure Hereditary (g : Q) (a : ServerState) : Prop where

  project      : ∀ (id : ServerModel.Ident) (p : PromiseObject) (n : Nat), Stored a id →
                   g.promise id p = true → g.promise id (p.project n) = true
  addCallback  : ∀ (id : ServerModel.Ident) (p : PromiseObject) (c : ServerModel.Ident), Stored a id →
                   g.promise id p = true → g.promise id (p.addCallback c) = true
  addListener  : ∀ (id : ServerModel.Ident) (p : PromiseObject) (c : String), Stored a id →
                   g.promise id p = true → g.promise id (p.addListener c) = true
  settle       : ∀ (id : ServerModel.Ident) (p : PromiseObject) (st : ServerModel.PromiseState)
                   (v : ServerModel.Value) (t : Nat), Stored a id →
                   st.settable = true → p.state = .pending → t < p.timeoutAt →
                   g.promise id p = true →
                   g.promise id { p with state := st, value := v, settledAt := some t } = true
  dropListener : ∀ (id : ServerModel.Ident) (p : PromiseObject) (c : String), Stored a id →
                   p.state ≠ .pending → g.promise id p = true →
                   g.promise id { p with listeners := p.listeners.filter (· != c) } = true
  dropCallback : ∀ (id : ServerModel.Ident) (p : PromiseObject) (c : ServerModel.Ident), Stored a id →
                   p.state ≠ .pending → g.promise id p = true →
                   g.promise id { p with callbacks := p.callbacks.filter (· != c) } = true
  live         : ∀ (id : ServerModel.Ident) (param : ServerModel.Value) (tags : ServerModel.Tags)
                   (timeoutAt createdAt : Nat), createdAt < timeoutAt →
                   a.objects.find? (·.id == id) = none →
                   g.promise id { state := .pending, param := param, tags := tags,
                                  timeoutAt := timeoutAt, createdAt := createdAt } = true
  dead         : ∀ (id : ServerModel.Ident) (st : ServerModel.PromiseState)
                   (param : ServerModel.Value) (tags : ServerModel.Tags) (timeoutAt : Nat),
                   st = (if tags.isTimer then .resolved else .rejectedTimedout) →
                   a.objects.find? (·.id == id) = none →
                   g.promise id { state := st, param := param, tags := tags,
                                  timeoutAt := timeoutAt, createdAt := timeoutAt,
                                  settledAt := some timeoutAt } = true

  tFulfill     : ∀ (t : TaskObject), g.task t = true → g.task t.fulfill = true
  tBornPending : ∀ (due : Nat),
                   g.task { state := .pending, version := 0,
                            retryTimeoutAt := some due } = true
  tBornDone    : g.task { state := .fulfilled, version := 0 } = true
  tBornHeld    : ∀ (pid : String) (ttl now : Nat),
                   g.task { state := .acquired, version := 1, ttl := some ttl,
                            pid := some pid, leaseTimeoutAt := some (now + ttl) } = true
  tAcquire     : ∀ (t : TaskObject) (pid : String) (ttl now : Nat), g.task t = true →
                   g.task { t with state := .acquired, version := t.version + 1, ttl := some ttl, pid := some pid, leaseTimeoutAt := some (now + ttl), retryTimeoutAt := none, resumes := [] } = true
  tHeartbeat   : ∀ (t : TaskObject) (x : Nat), (t.state == .acquired) = true →
                   g.task t = true → g.task { t with leaseTimeoutAt := some x } = true
  tClearResumes : ∀ (t : TaskObject), g.task t = true →
                   g.task { t with resumes := [] } = true
  tSuspend     : ∀ (t : TaskObject), g.task t = true →
                   g.task { t with state := .suspended, pid := none, ttl := none, leaseTimeoutAt := none, retryTimeoutAt := none, resumes := [] } = true
  tRepend      : ∀ (t : TaskObject) (n : Nat), g.task t = true →
                   g.task { t with state := .pending, pid := none, ttl := none, leaseTimeoutAt := none, retryTimeoutAt := some n } = true
  tHalt        : ∀ (t : TaskObject), g.task t = true →
                   g.task { t with state := .halted, pid := none, ttl := none, leaseTimeoutAt := none, retryTimeoutAt := none } = true
  tContinue    : ∀ (t : TaskObject) (n : Nat), (t.state == .halted) = true →
                   g.task t = true →
                   g.task { t with state := .pending, retryTimeoutAt := some n } = true
  tResume      : ∀ (t : TaskObject) (a : ServerModel.Ident) (n : Nat), t.state = .suspended →
                   g.task t = true →
                   g.task { t with state := .pending, resumes := [a], retryTimeoutAt := some n } = true
  tAddResume   : ∀ (t : TaskObject) (a : ServerModel.Ident), t.state ≠ .suspended →
                   t.state ≠ .fulfilled → (t.resumes.contains a) = false → g.task t = true →
                   g.task { t with resumes := t.resumes ++ [a] } = true
  tRearm       : ∀ (t : TaskObject) (n : Nat), (t.state == .pending) = true →
                   g.task t = true → g.task { t with retryTimeoutAt := some n } = true

  cBorn        : ∀ (id : ServerModel.Ident) (cron : String) (promiseId : ServerModel.Ident) (promiseTimeout : Nat)
                   (promiseParam : ServerModel.Value) (promiseTags : ServerModel.Tags)
                   (now : Nat), promiseTags.timerTargeted = false →
                   g.schedule { id := id, cron := cron, promiseId := promiseId,
                                promiseTimeout := promiseTimeout,
                                promiseParam := promiseParam, promiseTags := promiseTags,
                                createdAt := now,
                                nextRunAt := ServerModel.nextCron cron now,
                                lastRunAt := none } = true
  cAdvance     : ∀ (c : ServerModel.Schedule) (last : Nat), g.schedule c = true →
                   g.schedule { c with lastRunAt := some last, nextRunAt := ServerModel.nextCron c.cron last } = true

theorem Hereditary.tView {g : Q} {a : ServerState} (h : Hereditary g a) (t : TaskObject) (p : PromiseObject) :
    g.task t = true → g.task (t.view p) = true := by
  intro ht
  unfold TaskObject.view
  split
  · exact h.tFulfill t ht
  · exact ht

theorem pure_fst {α} (a : α) (e : Env) : ((pure a : H α) e).1 = a := rfl
theorem pure_snd {α} (a : α) (e : Env) : ((pure a : H α) e).2 = [] := rfl

theorem bind_fst {α β} (x : H α) (f : α → H β) (e : Env) :
    ((x >>= f) e).1 = (f (x e).1 e).1 := by
  simp only [bind]

theorem bind_snd {α β} (x : H α) (f : α → H β) (e : Env) :
    ((x >>= f) e).2 = (x e).2 ++ (f (x e).1 e).2 := by
  simp only [bind]

theorem writesGood_bind' {α β} (g : Q) (e : Env) (x : H α) (f : α → H β)
    (hx : WritesGood g e x) (hf : WritesGood g e (f (x e).1)) :
    WritesGood g e (x >>= f) := by
  intro k hk
  rw [bind_snd, List.mem_append] at hk
  cases hk with
  | inl h => exact hx k h
  | inr h => exact hf k h

theorem writesGood_pureBind {α β} (g : Q) (e : Env) (a : α) (f : α → H β)
    (h : WritesGood g e (f a)) : WritesGood g e (pure a >>= f) := by
  intro k hk
  rw [bind_snd] at hk
  simp only [pure_snd, pure_fst, List.nil_append] at hk
  exact h k hk

theorem writesGood_map {α β} (g : Q) (e : Env) (k : α → β) (x : H α)
    (hx : WritesGood g e x) : WritesGood g e (k <$> x) :=
  writesGood_bind' g e x _ hx (writesGood_pure g e _)

theorem writesGood_ite {α} (g : Q) (e : Env) (c : Prop) [Decidable c] (x y : H α)
    (hx : WritesGood g e x) (hy : WritesGood g e y) :
    WritesGood g e (if c then x else y) := by
  by_cases h : c
  · simpa only [if_pos h] using hx
  · simpa only [if_neg h] using hy

theorem writesGood_iteH {α} (g : Q) (e : Env) (c : Prop) [Decidable c] (x y : H α)
    (hx : c → WritesGood g e x) (hy : ¬c → WritesGood g e y) :
    WritesGood g e (if c then x else y) := by
  by_cases h : c
  · simpa only [if_pos h] using hx h
  · simpa only [if_neg h] using hy h

theorem getObject_fst (id : ServerModel.Ident) (e : Env) :
    (getObject id e).1 = e.state.objects.find? (·.id == id) := rfl

theorem getSchedule_fst (id : ServerModel.Ident) (e : Env) :
    (getSchedule id e).1 = e.state.schedules.find? (·.id == id) := rfl

theorem ask_fst (e : Env) : (ask e).1 = e := rfl

section Derived

variable {g : Q}

theorem QObj_project {a : ServerState} (hq : Hereditary g a) {o : Object}
    (hst : Stored a o.id) (h : QObj g o = true) (n : Nat) :
    QObj g (o.project n) = true := by
  have h1 : g.promise o.id o.promise = true := QObj_promise h
  simp only [QObj, Bool.and_eq_true]
  refine ⟨hq.project _ _ n hst h1, ?_⟩
  show (o.task.map (·.view (o.promise.project n))).all g.task = true
  cases hto : o.task with
  | none   => rfl
  | some t => exact hq.tView t _ (QObj_task h hto)

theorem writesGood_setSettled {e : Env} (hq : Hereditary g e.state)
    (o : Object) (ho : QObj g o = true) (p : PromiseObject) (h : g.promise o.id p = true) :
    WritesGood g e (setSettled o p) := by
  unfold setSettled
  refine writesGood_bind' _ _ _ _ (writesGood_setPromise _ _ _ _ h) ?_
  refine writesGood_ite _ _ _ _ _ ?_ (writesGood_pure _ _ _)
  split
  · rename_i t ht
    refine writesGood_ite _ _ _ _ _ ?_ (writesGood_pure _ _ _)
    exact writesGood_setTask _ _ _ _ (hq.tFulfill t (QObj_task ho ht))
  · exact writesGood_pure _ _ _

theorem writesGood_materialise {e : Env} {o' : Object} (h : QObj g o' = true)
    (id : ServerModel.Ident) (hid : o'.id = id) (o : Object) :
    WritesGood g e (materialise id o o') := by
  unfold materialise
  refine writesGood_bind' _ _ _ _ ?_ ?_
  · exact writesGood_ite _ _ _ _ _
      (writesGood_setPromise _ _ _ _ (hid ▸ QObj_promise h)) (writesGood_pure _ _ _)
  · split
    · rename_i t u _ hu
      exact writesGood_ite _ _ _ _ _
        (writesGood_setTask _ _ _ _ (QObj_task h hu)) (writesGood_pure _ _ _)
    · exact writesGood_pure _ _ _

theorem readObject_fst (id : ServerModel.Ident) (now : Nat) (e : Env) :
    (readObject id now e).1 =
      (e.state.objects.find? (·.id == id)).map (·.project now) := by
  unfold readObject
  rw [bind_fst, getObject_fst]
  cases h : e.state.objects.find? (·.id == id) with
  | none => rfl
  | some o =>
      rw [bind_fst]
      split <;> rw [bind_fst] <;> rfl

theorem writesGood_readObject {e : Env} (hq : Hereditary g e.state)
    (hs : PerStore g e.state = true) (id : ServerModel.Ident) (now : Nat) :
    WritesGood g e (readObject id now) := by
  unfold readObject
  refine writesGood_bind' _ _ _ _ (writesGood_getObject _ _ _) ?_
  rw [getObject_fst]
  split
  · exact writesGood_pure _ _ _
  · rename_i o h
    have ho : QObj g o = true := getObject_sound hs h
    have hst : Stored e.state o.id := by
      have : o.id = id := eq_of_beq (by simpa using List.find?_some h)
      rw [this]; exact stored_of_find? h
    have hpr : QObj g (o.project now) = true := QObj_project hq hst ho now
    refine writesGood_bind' _ _ _ _ (writesGood_ask _ _) ?_
    split
    · have hid : (o.project now).id = id :=
        (Lookup.project_id o now).trans (eq_of_beq (by simpa using List.find?_some h))
      exact writesGood_bind' _ _ _ _ (writesGood_materialise hpr id hid o)
        (writesGood_pure _ _ _)
    · exact writesGood_bind' _ _ _ _ (writesGood_pure _ _ _) (writesGood_pure _ _ _)

theorem returnsGood_readObject {e : Env} (hq : Hereditary g e.state)
    (hs : PerStore g e.state = true) (id : ServerModel.Ident) (now : Nat) (o : Object)
    (h : (readObject id now e).1 = some o) : QObj g o = true := by
  rw [readObject_fst] at h
  cases hf : e.state.objects.find? (fun x => x.id == id) with
  | none => rw [hf] at h; simp at h
  | some o₀ =>
      rw [hf] at h
      simp only [Option.map_some] at h
      obtain rfl := Option.some.inj h
      have hoid : o₀.id = id := eq_of_beq (by simpa using List.find?_some hf)
      exact QObj_project hq (by rw [hoid]; exact stored_of_find? hf)
        (getObject_sound hs hf) now

def NotDue (now : Nat) (p : PromiseObject) : Prop :=
  (p.state == ServerModel.PromiseState.pending) = true → now < p.timeoutAt

theorem readObject_notDue (id : ServerModel.Ident) (now : Nat) (e : Env) (o : Object)
    (h : (readObject id now e).1 = some o) : NotDue now o.promise := by
  intro hst
  rw [readObject_fst] at h
  cases hf : e.state.objects.find? (fun x => x.id == id) with
  | none => rw [hf] at h; simp at h
  | some o₀ =>
      rw [hf] at h
      simp only [Option.map_some] at h
      obtain rfl := Option.some.inj h
      exact Lookup.project_pending_not_due hst

theorem readObject_id (id : ServerModel.Ident) (now : Nat) (e : Env) (o : Object)
    (h : (readObject id now e).1 = some o) : o.id = id := by
  rw [readObject_fst] at h
  cases hf : e.state.objects.find? (fun x => x.id == id) with
  | none => rw [hf] at h; simp at h
  | some o₀ =>
      rw [hf] at h
      simp only [Option.map_some] at h
      obtain rfl := Option.some.inj h
      exact (Lookup.project_id o₀ now).trans
        (eq_of_beq (by simpa using List.find?_some hf))

theorem readObject_stored (id : ServerModel.Ident) (now : Nat) (e : Env) (o : Object)
    (h : (readObject id now e).1 = some o) : Stored e.state o.id := by
  rw [readObject_id id now e o h]
  rw [readObject_fst] at h
  cases hf : e.state.objects.find? (fun x => x.id == id) with
  | none => rw [hf] at h; simp at h
  | some o₀ => exact stored_of_find? hf

theorem writesGood_afterReadObject {α} {e : Env} (hq : Hereditary g e.state)
    (hs : PerStore g e.state = true) (id : ServerModel.Ident) (now : Nat)
    (f : Option Object → H α)
    (hnone : e.state.objects.find? (·.id == id) = none → WritesGood g e (f none))
    (hsome : ∀ o, QObj g o = true → NotDue now o.promise → Stored e.state o.id →
               WritesGood g e (f (some o))) :
    WritesGood g e (readObject id now >>= f) := by
  refine writesGood_bind' _ _ _ _ (writesGood_readObject hq hs id now) ?_
  cases h : (readObject id now e).1 with
  | none =>
      refine hnone ?_
      rw [readObject_fst] at h
      cases hf : e.state.objects.find? (·.id == id) with
      | none => rfl
      | some o₀ => rw [hf] at h; simp at h
  | some o =>
      exact hsome o (returnsGood_readObject hq hs id now o h)
        (readObject_notDue id now e o h) (readObject_stored id now e o h)

theorem writesGood_afterReadObjectP {α} {e : Env} (hq : Hereditary g e.state)
    (hs : PerStore g e.state = true) (id : ServerModel.Ident) (now : Nat)
    (f : Option Object → H α)
    (hnone : e.state.objects.find? (·.id == id) = none → WritesGood g e (f none))
    (hsome : ∀ o, g.promise o.id o.promise = true → NotDue now o.promise →
               Stored e.state o.id → WritesGood g e (f (some o))) :
    WritesGood g e (readObject id now >>= f) :=
  writesGood_afterReadObject hq hs id now f hnone
    (fun o ho => hsome o (QObj_promise ho))

theorem readTaskObject_fst_some {id : ServerModel.Ident} {now : Nat} {e : Env} {u : Object}
    (h : (readTaskObject id now e).1 = some u) : (readObject id now e).1 = some u := by
  revert h
  unfold readTaskObject
  rw [bind_fst, getObject_fst]
  cases hf : e.state.objects.find? (·.id == id) with
  | none => intro hh; simp [pure] at hh
  | some o =>
      show ((if o.task.isSome then readObject id now else pure none) e).1 = _ → _
      by_cases hto : o.task.isSome = true
      · rw [if_pos hto]; exact fun hh => hh
      · rw [if_neg hto]; intro hh; simp [pure] at hh

theorem writesGood_readTaskObject {e : Env} (hq : Hereditary g e.state)
    (hs : PerStore g e.state = true) (id : ServerModel.Ident) (now : Nat) :
    WritesGood g e (readTaskObject id now) := by
  unfold readTaskObject
  refine writesGood_bind' _ _ _ _ (writesGood_getObject _ _ _) ?_
  rw [getObject_fst]
  split
  · exact writesGood_pure _ _ _
  · exact writesGood_ite _ _ _ _ _ (writesGood_readObject hq hs id now)
      (writesGood_pure _ _ _)

theorem writesGood_afterReadTaskObject {α} {e : Env} (hq : Hereditary g e.state)
    (hs : PerStore g e.state = true) (id : ServerModel.Ident) (now : Nat)
    (f : Option Object → H α)
    (hnone : WritesGood g e (f none))
    (hsome : ∀ o, QObj g o = true → NotDue now o.promise → Stored e.state o.id →
               WritesGood g e (f (some o))) :
    WritesGood g e (readTaskObject id now >>= f) := by
  refine writesGood_bind' _ _ _ _ (writesGood_readTaskObject hq hs id now) ?_
  cases h : (readTaskObject id now e).1 with
  | none => exact hnone
  | some u =>
      have h' := readTaskObject_fst_some h
      exact hsome u (returnsGood_readObject hq hs id now u h')
        (readObject_notDue id now e u h') (readObject_stored id now e u h')

theorem writesGood_afterMatReadTaskObject {α} {e : Env} (hq : Hereditary g e.state)
    (b : Bool) (hs : PerStore g e.state = true) (id : ServerModel.Ident) (now : Nat)
    (f : Option Object → H α)
    (hnone : WritesGood g e (f none))
    (hsome : ∀ o, QObj g o = true → NotDue now o.promise → Stored e.state o.id →
               WritesGood g e (f (some o))) :
    WritesGood g e (withMat b (readTaskObject id now) >>= f) := by
  refine writesGood_bind' _ _ _ _
    (writesGood_readTaskObject (e := { e with mat := b }) hq hs id now) ?_
  show WritesGood g e (f ((readTaskObject id now { e with mat := b }).1))
  cases h : (readTaskObject id now { e with mat := b }).1 with
  | none => exact hnone
  | some u =>
      have h' := readTaskObject_fst_some h
      exact hsome u (returnsGood_readObject (e := { e with mat := b }) hq hs id now u h')
        (readObject_notDue id now { e with mat := b } u h')
        (readObject_stored id now { e with mat := b } u h')

theorem writesGood_afterMatReadObject {α} {e : Env} (hq : Hereditary g e.state) (b : Bool)
    (hs : PerStore g e.state = true) (id : ServerModel.Ident) (now : Nat)
    (f : Option Object → H α)
    (hnone : e.state.objects.find? (·.id == id) = none → WritesGood g e (f none))
    (hsome : ∀ o, QObj g o = true → NotDue now o.promise → Stored e.state o.id →
               WritesGood g e (f (some o))) :
    WritesGood g e (withMat b (readObject id now) >>= f) := by
  refine writesGood_bind' _ _ _ _
    (writesGood_readObject (e := { e with mat := b }) hq hs id now) ?_
  show WritesGood g e (f ((readObject id now { e with mat := b }).1))
  cases h : (readObject id now { e with mat := b }).1 with
  | none =>
      refine hnone ?_
      rw [readObject_fst] at h
      cases hf : e.state.objects.find? (·.id == id) with
      | none => rfl
      | some o₀ => rw [hf] at h; simp at h
  | some o =>
      exact hsome o
        (returnsGood_readObject (e := { e with mat := b }) hq hs id now o h)
        (readObject_notDue id now { e with mat := b } o h)
        (readObject_stored id now { e with mat := b } o h)

theorem writesGood_afterMatReadObjectP {α} {e : Env} (hq : Hereditary g e.state) (b : Bool)
    (hs : PerStore g e.state = true) (id : ServerModel.Ident) (now : Nat)
    (f : Option Object → H α)
    (hnone : e.state.objects.find? (·.id == id) = none → WritesGood g e (f none))
    (hsome : ∀ o, g.promise o.id o.promise = true → NotDue now o.promise →
               Stored e.state o.id → WritesGood g e (f (some o))) :
    WritesGood g e (withMat b (readObject id now) >>= f) :=
  writesGood_afterMatReadObject hq b hs id now f hnone
    (fun o ho => hsome o (QObj_promise ho))

end Derived

theorem stateHolds_init (now : Nat) :
    Properties.stateHolds now ServerState.init = true := rfl

theorem stateHolds_step (mat : Bool) (st : Step) (now : Nat) (s : ServerState) :
    Properties.stateHolds now s = true →
    Properties.stateHolds now (stepOf mat st now s).2 = true := sorry

theorem stateHolds_clock (n n' : Nat) (s : ServerState) :
    Properties.stateHolds n s = true → n ≤ n' →
    Properties.stateHolds n' s = true := sorry

theorem legalAt_step (mat : Bool) (st : Step) (now : Nat) (s : ServerState) :
    Properties.stateHolds now s = true →
    Properties.legalAt now s (stepOf mat st now s).2 = true := sorry

theorem internal_well_formed (mat : Bool) (st : Step) (now : Nat) (s : ServerState) :
    st.isInternal = true → Properties.stateHolds now s = true →
    Properties.internalWellFormed now s (stepOf mat st now s).2 = true := sorry

end Induction
end Abstraction
