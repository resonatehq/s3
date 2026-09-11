import impl.commit
import impl.equiv

namespace Refinement

open ServerModel AbstractModel
open Abstract (Request Response Reply)
open Abstract (Trigger)
open Impl (Origin World Key Blob Work Txn State Obs Commit)
open Apply Commit Equiv

def Trigger.about (o : String) : Trigger → Prop
  | .promiseTimeout r   => r.id.origin = o
  | .callback r         => r.awaited.origin = o ∧ r.awaiter.origin = o
  | .listener r         => r.awaited.origin = o
  | .taskLeaseTimeout r => r.id.origin = o
  | .taskRetryTimeout r => r.id.origin = o
  | .scheduleTimeout _  => False

def Event.about (o : String) : Abstract.Event → Prop
  | .external rq => rq.origin? = some o
  | .internal st => Trigger.about o st
  | .stutter     => True

theorem heartbeat_origins {req : TaskHeartbeatReq} {o : String}
    (h : (Request.taskHeartbeat req).origin? = some o) : ∀ r ∈ req.tasks, r.id.origin = o := by
  simp only [Request.origin?] at h
  cases hts : req.tasks with
  | nil => simp [hts] at h
  | cons t ts =>
    simp only [hts] at h
    split at h
    · rename_i hall
      cases h
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · rfl
      · have := List.all_eq_true.mp hall r hr
        simpa using this
    · cases h

theorem Cong.handleExternal {o : String} {rq : Request} (h : rq.origin? = some o) (now : Nat) :
    Frame.Cong o (Abstract.handleExternal rq now) := by
  cases rq with
  | promiseSearch _ | scheduleGet _ | scheduleCreate _ | scheduleDelete _ | scheduleSearch _
  | taskSearch _ => cases h
  | taskHeartbeat r =>
    exact Frame.Cong.map _ (Frame.Cong.taskHeartbeat (heartbeat_origins h) now)
  | promiseGet r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.promiseGet h now)
  | promiseCreate r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.promiseCreate h now)
  | promiseSettle r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.promiseSettle h now)
  | promiseRegisterCallback r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.promiseRegisterCallback h now)
  | promiseRegisterListener r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.promiseRegisterListener h now)
  | taskGet r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.taskGet h now)
  | taskCreate r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.taskCreate h now)
  | taskAcquire r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.taskAcquire h now)
  | taskFence r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.taskFence h now)
  | taskSuspend r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.taskSuspend h now)
  | taskFulfill r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.taskFulfill h now)
  | taskRelease r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.taskRelease h now)
  | taskHalt r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.taskHalt h now)
  | taskContinue r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.Cong.map _ (Frame.Cong.taskContinue h now)

theorem LocAt.handleExternal {o : String} {rq : Request} (h : rq.origin? = some o) (now : Nat)
    (e : AbstractModel.Env) : Frame.LocAt o (Abstract.handleExternal rq now) e := by
  cases rq with
  | promiseSearch _ | scheduleGet _ | scheduleCreate _ | scheduleDelete _ | scheduleSearch _
  | taskSearch _ => cases h
  | taskHeartbeat r =>
    exact Frame.LocAt.map _ (Frame.LocAt.taskHeartbeat (heartbeat_origins h) now e)
  | promiseGet r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.promiseGet h now e)
  | promiseCreate r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.promiseCreate h now e)
  | promiseSettle r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.promiseSettle h now e)
  | promiseRegisterCallback r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.promiseRegisterCallback h now e)
  | promiseRegisterListener r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.promiseRegisterListener h now e)
  | taskGet r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.taskGet h now e)
  | taskCreate r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.taskCreate h now e)
  | taskAcquire r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.taskAcquire h now e)
  | taskFence r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.taskFence h now e)
  | taskSuspend r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.taskSuspend h now e)
  | taskFulfill r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.taskFulfill h now e)
  | taskRelease r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.taskRelease h now e)
  | taskHalt r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.taskHalt h now e)
  | taskContinue r =>
    simp only [Request.origin?, Option.some.injEq] at h
    exact Frame.LocAt.map _ (Frame.LocAt.taskContinue h now e)

theorem Cong.handleInternal {o : String} {st : Trigger} (h : Trigger.about o st) (now : Nat) :
    Frame.Cong o (Abstract.handleInternal st now) := by
  cases st with
  | promiseTimeout r   => exact Frame.Cong.processPromiseTimeout h now
  | callback r         => exact Frame.Cong.processCallback h.1 h.2 now
  | listener r         => exact Frame.Cong.processListener h now
  | taskLeaseTimeout r => exact Frame.Cong.processLeaseTimeout h now
  | taskRetryTimeout r => exact Frame.Cong.processRetryTimeout h now
  | scheduleTimeout r  => exact absurd h id

theorem LocAt.handleInternal {o : String} {st : Trigger} (h : Trigger.about o st) (now : Nat)
    (e : AbstractModel.Env) : Frame.LocAt o (Abstract.handleInternal st now) e := by
  cases st with
  | promiseTimeout r   => exact Frame.LocAt.processPromiseTimeout h now e
  | callback r         => exact Frame.LocAt.processCallback h.1 h.2 now e
  | listener r         => exact Frame.LocAt.processListener h now e
  | taskLeaseTimeout r => exact Frame.LocAt.processLeaseTimeout h now e
  | taskRetryTimeout r => exact Frame.LocAt.processRetryTimeout h now e
  | scheduleTimeout r  => exact absurd h id

theorem Cong.handle {o : String} {st : Abstract.Event} (h : Event.about o st) (now : Nat) :
    Frame.Cong o (Abstract.handle st now) := by
  cases st with
  | external rq => exact Frame.Cong.map _ (Cong.handleExternal h now)
  | internal st => exact Frame.Cong.bind (Cong.handleInternal h now) (fun _ => Frame.Cong.pure _)
  | stutter     => exact Frame.Cong.pure _

theorem LocAt.handle {o : String} {st : Abstract.Event} (h : Event.about o st) (now : Nat)
    (e : AbstractModel.Env) : Frame.LocAt o (Abstract.handle st now) e := by
  cases st with
  | external rq => exact Frame.LocAt.map _ (LocAt.handleExternal h now e)
  | internal st => exact Frame.LocAt.bind (LocAt.handleInternal h now e) (Frame.LocAt.pure _ _)
  | stutter     => exact Frame.LocAt.pure _ _

def _root_.Impl.World.find? (w : World) : Lookup := fun j =>
  (current w j.origin).objects.find? (·.id == j)

structure Rel (w : World) (S : ServerState) : Prop where
  find   : ∀ j, w.find? j = lookup S j
  sched  : S.schedules = []
  outbox : S.outbox = w.wire

def virtFind (w : World) (o : String) (d : Origin) : Lookup := fun j =>
  if j.origin = o then d.objects.find? (·.id == j) else w.find? j

structure RelD (w : World) (o : String) (d : Origin) (sends : List (String × Message))
    (S : ServerState) : Prop where
  find   : ∀ j, virtFind w o d j = lookup S j
  sched  : S.schedules = []
  outbox : S.outbox = sendsFold w.wire sends

theorem RelD.init {w : World} {S : ServerState} (h : Rel w S) (o : String) :
    RelD w o (current w o) [] S where
  find := by
    intro j
    simp only [virtFind]
    split
    · rename_i hj; rw [← h.find j]; simp only [World.find?, hj]
    · exact h.find j
  sched := h.sched
  outbox := h.outbox

def DocInv (w : World) : Prop :=
  ∀ o, ∀ ob ∈ (current w o).objects, ob.id.origin = o

theorem World.find?_wf (w : World) : (Impl.World.find? w).wf := by
  intro j ob h
  have := List.find?_some h
  simpa using this

theorem step_eq (st : Abstract.Event) (now : Nat) (S : ServerState) :
    Abstract.step true st now S =
      ((Abstract.handle st now { state := S, mat := true, config := {} }).1,
       applyAll S (Abstract.handle st now { state := S, mat := true, config := {} }).2) := rfl

theorem envEquiv_of_RelD {w : World} {o : String} {d : Origin} {sends : List (String × Message)}
    {S : ServerState} (h : RelD w o d sends S) :
    Frame.EnvEquiv o (env d) { state := S, mat := true, config := {} } where
  mat := rfl
  config := rfl
  find := by
    intro j hj
    have := h.find j
    simp only [virtFind, hj, ↓reduceIte, lookup] at this
    exact this

theorem specStep_origins {o : String} {d : Origin} (hd : ∀ ob ∈ d.objects, ob.id.origin = o)
    {st : Abstract.Event} (hab : Event.about o st) (now : Nat) :
    ∀ ob ∈ (specStep st now d).2.1.objects, ob.id.origin = o := by
  unfold specStep
  exact origins_applyAll (LocAt.handle hab now _) hd

theorem specStep_sim {w : World} {o : String} {d : Origin} {sends : List (String × Message)}
    {S : ServerState} (h : RelD w o d sends S)
    {st : Abstract.Event} (hab : Event.about o st) (now : Nat) :
    (Abstract.step true st now S).1 = (specStep st now d).1 ∧
    RelD w o (specStep st now d).2.1 (sends ++ (specStep st now d).2.2)
      (Abstract.step true st now S).2 := by
  have hcong := Cong.handle hab now _ _ (envEquiv_of_RelD h)
  have hloc : ∀ f ∈ (Abstract.handle st now { state := S, mat := true, config := {} }).2,
      Frame.Effect.Local o f :=
    LocAt.handle hab now { state := S, mat := true, config := {} }
  unfold specStep
  rw [step_eq]
  simp only
  rw [hcong]
  refine ⟨rfl, ?_⟩
  generalize (Abstract.handle st now { state := S, mat := true, config := {} }).2 = fx at hloc ⊢
  have hagree : Agree o (lookup d.toState) (lookup S) := by
    intro j hj
    have := h.find j
    simpa [virtFind, hj, lookup, Origin.toState] using this
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases hj : j.origin = o
    · have h1 := lookupAfter_congr hagree fx j hj
      rw [← lookup_applyAll, ← lookup_applyAll] at h1
      simpa [virtFind, hj, lookup] using h1
    · have h1 := lookupAfter_frame (lookup_wf S) hloc j hj
      rw [← lookup_applyAll] at h1
      have h2 := h.find j
      simp only [virtFind, hj, ↓reduceIte] at h2
      simp only [virtFind, hj, ↓reduceIte]
      rw [h2, h1]
  · rw [schedules_applyAll _ hloc]; exact h.sched
  · rw [outbox_applyAll, h.outbox, sendsFold_append]

def internals (now : Nat) (sts : List Trigger) : List (Abstract.Event × Nat) :=
  sts.map fun st => (.internal st, now)

def specFold (now : Nat) : Origin → List Trigger → Origin × List (String × Message)
  | o, []        => (o, [])
  | o, st :: sts =>
      let (_, o', sends) := specStep (.internal st) now o
      let (o'', sends') := specFold now o' sts
      (o'', sends ++ sends')

theorem specFold_origins {o : String} (now : Nat) :
    ∀ (d : Origin) (sts : List Trigger), (∀ ob ∈ d.objects, ob.id.origin = o) →
      (∀ st ∈ sts, Trigger.about o st) →
      ∀ ob ∈ (specFold now d sts).1.objects, ob.id.origin = o
  | d, [], hd, _ => hd
  | d, st :: sts, hd, hab => by
      simp only [specFold]
      exact specFold_origins now _ sts
        (specStep_origins (st := .internal st) hd (hab st (List.mem_cons_self ..)) now)
        (fun s hs => hab s (List.mem_cons_of_mem _ hs))

theorem specFold_sim {w : World} {o : String} {S : ServerState} (now : Nat) :
    ∀ (d : Origin) (sends : List (String × Message)) (sts : List Trigger),
      RelD w o d sends S → (∀ ob ∈ d.objects, ob.id.origin = o) →
      (∀ st ∈ sts, Trigger.about o st) →
      (Abstract.exec true (internals now sts) S).1 = sts.map (fun _ => Reply.internal) ∧
      RelD w o (specFold now d sts).1 (sends ++ (specFold now d sts).2)
        (Abstract.exec true (internals now sts) S).2
  | d, sends, [], h, _, _ => by
      refine ⟨rfl, ?_⟩
      simpa [specFold, internals, Abstract.exec] using h
  | d, sends, st :: sts, h, hd, hab => by
      have h1 := specStep_sim h (st := .internal st) (hab st (List.mem_cons_self ..)) now
      have hd' := specStep_origins hd (st := .internal st) (hab st (List.mem_cons_self ..)) now
      have ih := specFold_sim (S := (Abstract.step true (.internal st) now S).2) now
        (specStep (.internal st) now d).2.1
        (sends ++ (specStep (.internal st) now d).2.2) sts h1.2 hd'
        (fun s hs => hab s (List.mem_cons_of_mem _ hs))
      simp only [internals, List.map_cons, Abstract.exec, specFold] at ih ⊢
      refine ⟨?_, ?_⟩
      · rw [ih.1]
        have : (Abstract.step true (.internal st) now S).1 = .internal := by
          rw [step_eq]; rfl
        rw [this]
      · simpa [List.append_assoc] using ih.2

theorem Trigger.about_notSchedule {o : String} {st : Trigger} (h : Trigger.about o st) :
    st.isSchedule = false := by
  cases st <;> first | rfl | exact absurd h id

theorem triggers_eq {o : String} (now : Nat) :
    ∀ (d : Origin) (sts : List Trigger), (∀ st ∈ sts, Trigger.about o st) →
      Impl.triggers now d sts = specFold now d sts
  | d, [], _ => rfl
  | d, st :: sts, hab => by
      have he := trigger_eq st now d (Trigger.about_notSchedule (hab st (List.mem_cons_self ..)))
      simp only [Prod.mk.injEq] at he
      simp only [Impl.triggers, specFold, he.1, he.2]
      rw [triggers_eq now _ sts (fun s hs => hab s (List.mem_cons_of_mem _ hs))]

theorem timeoutSteps_about {o : String} {d : Origin} (hd : ∀ ob ∈ d.objects, ob.id.origin = o)
    (now : Nat) : ∀ st ∈ Impl.timeoutSteps d now, Trigger.about o st := by
  intro st hst
  simp only [Impl.timeoutSteps, List.mem_append, List.mem_filterMap] at hst
  rcases hst with ⟨ob, hob, h⟩ | ⟨ob, hob, h⟩
  · split at h
    · cases h; exact hd ob hob
    · cases h
  · split at h
    · split at h
      · cases h; exact hd ob hob
      · cases h
    · cases h

theorem obligationSteps_about {o : String} {d : Origin} (hd : ∀ ob ∈ d.objects, ob.id.origin = o) :
    ∀ st ∈ Impl.obligationSteps o d, Trigger.about o st := by
  intro st hst
  simp only [Impl.obligationSteps, List.mem_flatMap] at hst
  obtain ⟨ob, hob, h⟩ := hst
  split at h
  · simp only [List.mem_append, List.mem_filterMap, List.mem_map] at h
    rcases h with ⟨aw, _, haw⟩ | ⟨a, _, ha⟩
    · split at haw
      · rename_i heq
        cases haw
        exact ⟨hd ob hob, by simpa using heq⟩
      · cases haw
    · cases ha; exact hd ob hob
  · simp at h

theorem retrySteps_about {o : String} {d : Origin} (hd : ∀ ob ∈ d.objects, ob.id.origin = o)
    (now : Nat) : ∀ st ∈ Impl.retrySteps d now, Trigger.about o st := by
  intro st hst
  simp only [Impl.retrySteps, List.mem_filterMap] at hst
  obtain ⟨ob, hob, h⟩ := hst
  split at h
  · split at h
    · cases h; exact hd ob hob
    · cases h
  · cases h

theorem drainSteps_about {o : String} {d : Origin} (hd : ∀ ob ∈ d.objects, ob.id.origin = o)
    (now : Nat) : ∀ st ∈ Impl.drainSteps o d now, Trigger.about o st := by
  intro st hst
  simp only [Impl.drainSteps, List.mem_append] at hst
  have h1 := timeoutSteps_about hd now
  have hd1 : ∀ ob ∈ (Impl.triggers now d (Impl.timeoutSteps d now)).1.objects, ob.id.origin = o := by
    rw [triggers_eq now d _ h1]; exact specFold_origins now d _ hd h1
  have h2 := obligationSteps_about hd1
  have hd2 : ∀ ob ∈ (Impl.triggers now (Impl.triggers now d (Impl.timeoutSteps d now)).1
      (Impl.obligationSteps o (Impl.triggers now d (Impl.timeoutSteps d now)).1)).1.objects,
      ob.id.origin = o := by
    rw [triggers_eq now _ _ h2]; exact specFold_origins now _ _ hd1 h2
  have h3 := retrySteps_about hd2 now
  rcases hst with (hst | hst) | hst
  · exact h1 st hst
  · exact h2 st hst
  · exact h3 st hst

theorem sendsOfC_append (a b : List Impl.Effect) : sendsOfC (a ++ b) = sendsOfC a ++ sendsOfC b := by
  induction a with
  | nil => rfl
  | cons f fs ih => cases f <;> simp [sendsOfC, ih]

theorem put_ok_holds {st st' : Cas.Store Key Blob} {k : Key} {b : Blob} {c : Cas.Cond} {v : Cas.Version}
    (h : st.put k b c = .ok (st', v)) : c.holds (st.version? k) = true := by
  unfold Cas.Store.put at h
  split at h
  · assumption
  · cases h

theorem version?_of_get_eq {st st' : Cas.Store Key Blob} {k : Key}
    (h : st'.get k = st.get k) : st'.version? k = st.version? k := by
  simp only [Cas.Store.version?, h]

theorem commit_rejected {t : Txn} {now : Nat} {w : World}
    (h : (Impl.runC (Impl.transact t.work now) (envOf t) w).1 = none) :
    (∀ o', (Impl.runC (Impl.transact t.work now) (envOf t) w).2.store.get (.origin o') =
             w.store.get (.origin o')) ∧
    (Impl.runC (Impl.transact t.work now) (envOf t) w).2.wire = w.wire ∧
    w.store.next ≤ (Impl.runC (Impl.transact t.work now) (envOf t) w).2.store.next ∧
    (SInv w.store → SInv (Impl.runC (Impl.transact t.work now) (envOf t) w).2.store) := by
  have harm := applyEffects_noput (n := t.origin) (c := (envOf t).cond) _ w
    (armFx_noput (decOf t now).2)
  rw [runC_transact] at h ⊢
  cases hp : (armed t now w).store.put (.origin t.origin) (.origin (decOf t now).2.put)
      (envOf t).cond with
  | ok x => obtain ⟨st, v⟩ := x; simp [hp] at h
  | rejected =>
    simp only
    refine ⟨harm.2.1, ?_, harm.2.2.2.1, harm.2.2.2.2⟩
    rw [show armed t now w =
        (Impl.applyEffects t.origin (envOf t).cond w
          (Impl.armFx (decOf t now).2)).1 from rfl]
    rw [harm.2.2.1, armFx_nosend]; rfl

theorem commit_accepted {t : Txn} {now : Nat} {w : World} {res : Reply}
    (h : (Impl.runC (Impl.transact t.work now) (envOf t) w).1 = some res) :
    res = (decOf t now).1 ∧
    (envOf t).cond.holds (w.store.version? (.origin t.origin)) = true ∧
    (∃ v, (Impl.runC (Impl.transact t.work now) (envOf t) w).2.store.get (.origin t.origin) =
            some (.origin (decOf t now).2.put, v)) ∧
    (∀ o', o' ≠ t.origin →
      (Impl.runC (Impl.transact t.work now) (envOf t) w).2.store.get (.origin o') =
        w.store.get (.origin o')) ∧
    (Impl.runC (Impl.transact t.work now) (envOf t) w).2.wire =
      sendsFold w.wire (decOf t now).2.send ∧
    (SInv w.store → SInv (Impl.runC (Impl.transact t.work now) (envOf t) w).2.store) ∧
    (∀ u, TxnInv w.store u →
      TxnInv (Impl.runC (Impl.transact t.work now) (envOf t) w).2.store u) := by
  have harm := applyEffects_noput (n := t.origin) (c := (envOf t).cond) _ w
    (armFx_noput (decOf t now).2)
  have harmed : armed t now w =
      (Impl.applyEffects t.origin (envOf t).cond w
        (Impl.armFx (decOf t now).2)).1 := rfl
  rw [runC_transact] at h ⊢
  cases hp : (armed t now w).store.put (.origin t.origin) (.origin (decOf t now).2.put)
      (envOf t).cond with
  | rejected => simp [hp] at h
  | ok x =>
    obtain ⟨st, v⟩ := x
    simp only [hp, Option.some.injEq] at h
    simp only
    have hrest := applyEffects_noput (n := t.origin) (c := (envOf t).cond)
      (Impl.delFx (decOf t now).2 t.work ++ Impl.sendFx (decOf t now).2.send)
      { armed t now w with store := st }
      (by intro f hf
          simp only [List.mem_append] at hf
          rcases hf with hf | hf
          · exact delFx_noput _ t.work f hf
          · exact sendFx_noput _ f hf)
    have hget_armed : ∀ o', (armed t now w).store.get (.origin o') = w.store.get (.origin o') := by
      intro o'; rw [harmed]; exact harm.2.1 o'
    refine ⟨h.symm, ?_, ⟨v, ?_⟩, ?_, ?_, ?_, ?_⟩
    · have := put_ok_holds hp
      rwa [version?_of_get_eq (hget_armed t.origin)] at this
    · rw [hrest.2.1]
      exact Cas.get_put_same _ _ _ _ _ _ hp
    · intro o' ho
      rw [hrest.2.1]
      show st.get (.origin o') = _
      rw [Cas.get_put_other _ _ _ _ _ _ _ hp (by simpa using ho)]
      exact hget_armed o'
    · rw [hrest.2.2.1]
      show sendsFold (armed t now w).wire _ = _
      rw [harmed, harm.2.2.1, armFx_nosend, sendsOfC_append, delFx_nosend, sendsOfC_sendFx]
      rfl
    · intro hs
      exact hrest.2.2.2.2 (put_ok_sinv hp (harmed ▸ harm.2.2.2.2 hs))
    · intro u hu
      have h1 : TxnInv (armed t now w).store u :=
        TxnInv.of_get_eq hget_armed (harmed ▸ harm.2.2.2.1) hu
      have h2 : TxnInv st u := TxnInv.of_put hp h1
      exact TxnInv.of_get_eq hrest.2.1 hrest.2.2.2.1 h2

theorem accepted_snapshot {t : Txn} {w : World} (hinv : TxnInv w.store t)
    (hc : (envOf t).cond.holds (w.store.version? (.origin t.origin)) = true) :
    t.snapshot = w.origin? t.origin := by
  cases hs : t.snapshot with
  | none =>
    have hc' : w.store.version? (.origin t.origin) = none := by
      have := hc
      simp only [envOf, Impl.Env.cond, hs, Cas.Cond.holds, Option.isNone_iff_eq_none] at this
      exact this
    simp only [Cas.Store.version?, Option.map_eq_none_iff] at hc'
    simp [World.origin?, hc']
  | some dv =>
    obtain ⟨d, v⟩ := dv
    have hc' : w.store.version? (.origin t.origin) = some v := by
      have := hc
      simp only [envOf, Impl.Env.cond, hs, Cas.Cond.holds, beq_iff_eq] at this
      exact this
    simp only [Cas.Store.version?, Option.map_eq_some_iff] at hc'
    obtain ⟨⟨b, v'⟩, hg, hv⟩ := hc'
    simp only at hv
    subst hv
    have := (hinv d v' hs).2 b hg
    subst this
    simp [World.origin?, hg]

theorem envOf_snap_eq_current {t : Txn} {w : World} (h : t.snapshot = w.origin? t.origin) :
    (envOf t).snap = current w t.origin := by
  simp only [envOf, Impl.Env.snap, current, h]
  cases w.origin? t.origin with
  | none => rfl
  | some dv => rfl

theorem current_of_get {w : World} {o : String} {d : Origin} {v : Cas.Version}
    (h : w.store.get (.origin o) = some (.origin d, v)) : current w o = d := by
  simp [current, World.origin?, h]

theorem current_of_get_eq {w w' : World} {o : String}
    (h : w'.store.get (.origin o) = w.store.get (.origin o)) : current w' o = current w o := by
  simp only [current, World.origin?, h]

theorem mem_of_get {st : Cas.Store Key Blob} {k : Key} {b : Blob} {v : Cas.Version}
    (h : st.get k = some (b, v)) : (k, v, b) ∈ st.entries := by
  simp only [Cas.Store.get, Option.map_eq_some_iff] at h
  obtain ⟨⟨k', v', b'⟩, hf, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hk := List.find?_some hf
  simp only [beq_iff_eq] at hk
  subst hk
  exact List.mem_of_find?_eq_some hf

theorem timers_rejected {t : Txn} {now : Nat} {w : World}
    (h : (Impl.runC (Impl.transact t.work now) (envOf t) w).1 = none)
    (hinv : TimerInv w) : TimerInv (Impl.runC (Impl.transact t.work now) (envOf t) w).2 := by
  obtain ⟨hget, _, _, _⟩ := commit_rejected h
  intro n d hd
  rw [current_of_get_eq (hget n)] at hd
  have hs := hinv n d hd
  rw [runC_transact] at h ⊢
  cases hp : (armed t now w).store.put (.origin t.origin) (.origin (decOf t now).2.put)
      (envOf t).cond with
  | ok x => obtain ⟨st, v⟩ := x; simp [hp] at h
  | rejected =>
    simp only
    by_cases hn : n = t.origin
    · subst hn
      exact applyEffects_timer_keep _ _ (armFx_nodel _ _) hs
    · unfold armed
      rw [applyEffects_timer_other hn]
      exact hs

theorem timers_accepted {t : Txn} {now : Nat} {w : World} {res : Reply}
    (h : (Impl.runC (Impl.transact t.work now) (envOf t) w).1 = some res)
    (htxn : TxnInv w.store t) (hinv : TimerInv w) :
    TimerInv (Impl.runC (Impl.transact t.work now) (envOf t) w).2 := by
  obtain ⟨_, hcond, ⟨v0, hdocget⟩, hother, _⟩ := commit_accepted h
  have hsnap := accepted_snapshot htxn hcond
  have hold : (envOf t).snap = current w t.origin := envOf_snap_eq_current hsnap
  have hcur := current_of_get hdocget
  obtain ⟨tx, htx⟩ := decOf_shape t now
  revert hcur hother
  rw [runC_transact] at h ⊢
  cases hp : (armed t now w).store.put (.origin t.origin) (.origin (decOf t now).2.put)
      (envOf t).cond with
  | rejected => simp [hp] at h
  | ok x =>
    obtain ⟨st, v⟩ := x
    simp only
    intro hother hcur n d hd
    by_cases hn : n = t.origin
    · subst hn
      rw [hcur] at hd
      have hd' := hd
      rw [htx] at hd'
      refine applyEffects_timer_keep _ _ (htx ▸ tail_nodel t.work hd') ?_
      show (st.get (.timer d t.origin)).isSome = true
      rw [Cas.get_put_other _ _ _ _ _ _ _ hp (by simp)]
      rcases commit_arm_or_old hd' with harm | hold'
      · rw [← htx] at harm
        exact applyEffects_arm _ _ harm
      · rw [hold] at hold'
        exact applyEffects_timer_keep _ _ (armFx_nodel _ _) (hinv t.origin d hold')
    · rw [current_of_get_eq (hother n hn)] at hd
      have hs := hinv n d hd
      rw [applyEffects_timer_other hn]
      show (st.get (.timer d n)).isSome = true
      rw [Cas.get_put_other _ _ _ _ _ _ _ hp (by simp)]
      unfold armed
      rw [applyEffects_timer_other hn]
      exact hs

theorem TxnInv.fresh {w : World} (hs : SInv w.store) (o : String) (work : Work) :
    TxnInv w.store ⟨o, work, w.origin? o⟩ := by
  intro d v hsnap
  simp only [World.origin?] at hsnap
  cases hg : w.store.get (.origin o) with
  | none => simp [hg] at hsnap
  | some x =>
    obtain ⟨b, v'⟩ := x
    cases b with
    | timer => simp [hg] at hsnap
    | origin d' =>
      simp only [hg, Option.some.injEq, Prod.mk.injEq] at hsnap
      obtain ⟨rfl, rfl⟩ := hsnap
      refine ⟨hs _ (mem_of_get hg), ?_⟩
      intro b hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      exact hb.1.symm

structure Inv (s : State) : Prop where
  sinv   : SInv s.world.store
  docs   : DocInv s.world
  timers : TimerInv s.world
  txns   : ∀ t ∈ s.inflight, TxnInv s.world.store t
  works  : ∀ t ∈ s.inflight, t.work.origin? t.origin = some t.origin

theorem Inv.init : Inv State.init where
  sinv := fun _ h => by simp [State.init] at h
  docs := fun o ob h => by
    simp [current, World.origin?, Cas.Store.get, State.init] at h
  timers := fun n d h => by
    simp [current, World.origin?, Cas.Store.get, State.init, Impl.Origin.deadlines] at h
  txns := fun _ h => by simp [State.init] at h
  works := fun _ h => by simp [State.init] at h

theorem Rel.init : Rel State.init.world ServerState.init where
  find := fun j => by simp [Impl.World.find?, current, World.origin?, Cas.Store.get, State.init, lookup,
    ServerState.init]
  sched := rfl
  outbox := rfl

theorem mem_of_mem_eraseIdx {α : Type} : ∀ (l : List α) (i : Nat) (x : α), x ∈ l.eraseIdx i → x ∈ l
  | [], _, _, h => by simp [List.eraseIdx] at h
  | a :: as, 0, x, h => by simp [List.eraseIdx] at h; exact List.mem_cons_of_mem _ h
  | a :: as, i + 1, x, h => by
      simp only [List.eraseIdx, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_of_mem_eraseIdx as i x h)

def specSteps (t : Txn) (now : Nat) : List Abstract.Event :=
  match t.work with
  | .request rq =>
      .external rq ::
        (Impl.drainSteps t.origin (Impl.Handle.external rq now (envOf t).snap).2.put now).map .internal
  | .sweep _ =>
      (Impl.drainSteps t.origin (envOf t).snap now).map .internal

def expand (st : Impl.Step) (now : Nat) (s : State) : List Abstract.Event :=
  match st with
  | .commit i =>
      match s.inflight[i]? with
      | none   => []
      | some t =>
          match (Impl.runC (Impl.transact t.work now) (envOf t) s.world).1 with
          | none   => []
          | some _ => specSteps t now
  | _ => []

def linearize : List (Impl.Step × Nat) → State → List (Abstract.Event × Nat)
  | [],           _ => []
  | (st, n) :: w, s =>
      (expand st n s).map (fun a => (a, n)) ++ linearize w (Impl.step st n s).2

def obsOf : List (Abstract.Event × Nat) → List Reply → List Obs
  | (.external rq, n) :: w, .external r :: rs => ⟨rq, r, n⟩ :: obsOf w rs
  | _ :: w, _ :: rs                           => obsOf w rs
  | _, _                                      => []

theorem obsOf_internals (now : Nat) : ∀ (sts : List Trigger) (rs : List Reply),
    obsOf (internals now sts) rs = []
  | [], rs => by cases rs <;> rfl
  | st :: sts, [] => rfl
  | st :: sts, r :: rs => by
      simp only [internals, List.map_cons, obsOf]
      exact obsOf_internals now sts rs

theorem exec_length : ∀ (w : List (Abstract.Event × Nat)) (S : ServerState),
    (Abstract.exec true w S).1.length = w.length
  | [], _ => rfl
  | (st, n) :: w, S => by
      simp only [Abstract.exec, List.length_cons]
      rw [exec_length w]

theorem exec_append : ∀ (a b : List (Abstract.Event × Nat)) (S : ServerState),
    Abstract.exec true (a ++ b) S =
      ((Abstract.exec true a S).1 ++ (Abstract.exec true b (Abstract.exec true a S).2).1,
       (Abstract.exec true b (Abstract.exec true a S).2).2)
  | [], b, S => by simp [Abstract.exec]
  | (st, n) :: a, b, S => by
      simp only [List.cons_append, Abstract.exec]
      rw [exec_append a b]

theorem obsOf_append : ∀ (a b : List (Abstract.Event × Nat)) (rs rs' : List Reply),
    rs.length = a.length → obsOf (a ++ b) (rs ++ rs') = obsOf a rs ++ obsOf b rs'
  | [], b, [], rs', _ => by simp [obsOf]
  | [], b, r :: rs, rs', h => by simp at h
  | x :: a, b, [], rs', h => by simp at h
  | (st, n) :: a, b, r :: rs, rs', h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      cases st with
      | external rq =>
        cases r with
        | external r => simp only [List.cons_append, obsOf]; rw [obsOf_append a b rs rs' h]
        | internal => simp only [List.cons_append, obsOf]; exact obsOf_append a b rs rs' h
        | stutter => simp only [List.cons_append, obsOf]; exact obsOf_append a b rs rs' h
      | internal _ => simp only [List.cons_append, obsOf]; exact obsOf_append a b rs rs' h
      | stutter => simp only [List.cons_append, obsOf]; exact obsOf_append a b rs rs' h

theorem run_cons (st : Impl.Step) (n : Nat) (w : List (Impl.Step × Nat)) (s : State) :
    Impl.run ((st, n) :: w) s =
      ((Impl.step st n s).1.toList ++ (Impl.run w (Impl.step st n s).2).1,
       (Impl.run w (Impl.step st n s).2).2) := rfl

theorem commit_eq {i now : Nat} {s : State} {t : Txn} (hget : s.inflight[i]? = some t) :
    Impl.commit i now s =
      ((match (Impl.runC (Impl.transact t.work now) (envOf t) s.world).1, t.work with
        | some (.external res), .request rq => some ⟨rq, res, now⟩
        | _,                    _           => none),
       { world := (Impl.runC (Impl.transact t.work now) (envOf t) s.world).2,
         inflight := s.inflight.eraseIdx i }) := by
  unfold Impl.commit
  rw [hget]
  rfl

theorem decide_request (n : String) (rq : Request) (now : Nat) (old : Origin) :
    Impl.decide n (.request rq) now old =
      (Reply.external (Impl.Handle.external rq now old).1,
       Impl.Tx.commit old
         { origin := (Impl.drain n (Impl.Handle.external rq now old).2.put now).1,
           sends := (Impl.Handle.external rq now old).2.send ++
                    (Impl.drain n (Impl.Handle.external rq now old).2.put now).2 }) := rfl

theorem decide_sweep (n : String) (fired : Nat) (now : Nat) (old : Origin) :
    Impl.decide n (.sweep fired) now old =
      (.stutter,
       Impl.Tx.commit old
         { origin := (Impl.drain n old now).1, sends := [] ++ (Impl.drain n old now).2 }) := rfl

theorem drain_eq (n : String) (o : Origin) (now : Nat) :
    Impl.drain n o now = Impl.triggers now o (Impl.drainSteps n o now) := rfl

theorem commit_put (o : Origin) (tx : Impl.Tx) : (Impl.Tx.commit o tx).put = tx.origin := rfl

theorem commit_send (o : Origin) (tx : Impl.Tx) : (Impl.Tx.commit o tx).send = tx.sends := rfl

theorem Rel.of_RelD {w w' : World} {o : String} {d : Origin} {sends : List (String × Message)}
    {S : ServerState} (h : RelD w o d sends S)
    (hdoc : (current w' o).objects = d.objects)
    (hother : ∀ o', o' ≠ o → current w' o' = current w o')
    (hwire : w'.wire = sendsFold w.wire sends) : Rel w' S where
  find := by
    intro j
    rw [← h.find j]
    simp only [Impl.World.find?, virtFind]
    split
    · rename_i hj; rw [hj, hdoc]
    · rename_i hj; rw [hother _ hj]
  sched := h.sched
  outbox := by rw [h.outbox, hwire]

def obsFor (wk : Work) (r : Reply) (now : Nat) : List Obs :=
  match wk, r with
  | .request rq, .external res => [⟨rq, res, now⟩]
  | _, _                       => []

theorem obsFor_eq (wk : Work) (r : Reply) (now : Nat) :
    obsFor wk r now =
      (match some r, wk with
       | some (Reply.external res), Work.request rq => some (⟨rq, res, now⟩ : Obs)
       | _,                         _               => none).toList := by
  cases wk <;> cases r <;> rfl

theorem step_external_reply (rq : Request) (now : Nat) (S : ServerState) :
    (Abstract.step true (.external rq) now S).1 =
      .external (Abstract.handleExternal rq now { state := S, mat := true, config := {} }).1 := rfl

theorem accepted_sim {t : Txn} {now : Nat} {w : World} {S : ServerState} {res : Reply}
    (hrel : Rel w S) (hsinv : SInv w.store) (hdocs : DocInv w) (htxn : TxnInv w.store t)
    (hwork : t.work.origin? t.origin = some t.origin)
    (hacc : (Impl.runC (Impl.transact t.work now) (envOf t) w).1 = some res) :
    let lin := (specSteps t now).map (fun a => (a, now))
    let w' := (Impl.runC (Impl.transact t.work now) (envOf t) w).2
    obsOf lin (Abstract.exec true lin S).1 = obsFor t.work res now ∧
    Rel w' (Abstract.exec true lin S).2 ∧
    DocInv w' ∧ SInv w'.store ∧ (∀ u, TxnInv w.store u → TxnInv w'.store u) := by
  intro lin w'
  obtain ⟨hres, hcond, ⟨v, hdocget⟩, hother, hwire, hsinv', htxns'⟩ := commit_accepted hacc
  have hsnap := accepted_snapshot htxn hcond
  have hdoc0 : (envOf t).snap = current w t.origin := envOf_snap_eq_current hsnap
  have hd0 : ∀ ob ∈ (current w t.origin).objects, ob.id.origin = t.origin := hdocs t.origin
  have hcur' : current w' t.origin = (decOf t now).2.put := current_of_get hdocget
  have hother' : ∀ o', o' ≠ t.origin → current w' o' = current w o' :=
    fun o' ho => current_of_get_eq (hother o' ho)
  have hdocs' : ∀ (d2 : Origin), (∀ ob ∈ d2.objects, ob.id.origin = t.origin) →
      (decOf t now).2.put.objects = d2.objects → DocInv w' := by
    intro d2 hd2 heq o ob hob
    by_cases ho : o = t.origin
    · subst ho; rw [hcur', heq] at hob; exact hd2 ob hob
    · rw [hother' o ho] at hob; exact hdocs o ob hob
  cases hw : t.work with
  | request rq =>
    have hab : Event.about t.origin (.external rq) := by
      show rq.origin? = some t.origin
      simpa [Work.origin?, hw] using hwork
    have hsome : rq.origin?.isSome := by
      have : rq.origin? = some t.origin := hab
      rw [this]; rfl
    have hext := external_eq rq now (current w t.origin) hsome
    have he1 := congrArg Prod.fst hext
    have he2 := congrArg (fun p => p.2.1) hext
    have he3 := congrArg (fun p => p.2.2) hext
    simp only at he1 he2 he3
    have hdec : decOf t now = Impl.decide t.origin (.request rq) now (current w t.origin) := by
      simp only [decOf, hw, hdoc0]
    rw [decide_request, drain_eq, he2] at hdec
    have h1 := specStep_sim (RelD.init hrel t.origin) hab now
    have hd1 := specStep_origins hd0 hab now
    rw [triggers_eq now _ _ (drainSteps_about hd1 now)] at hdec
    have h2 := specFold_sim (S := (Abstract.step true (.external rq) now S).2) now
      (specStep (.external rq) now (current w t.origin)).2.1
      ([] ++ (specStep (.external rq) now (current w t.origin)).2.2)
      (Impl.drainSteps t.origin (specStep (.external rq) now (current w t.origin)).2.1 now)
      h1.2 hd1 (drainSteps_about hd1 now)
    have hd2 := specFold_origins now _ _ hd1 (drainSteps_about hd1 now)
    have hlin : lin = (Abstract.Event.external rq, now) ::
        internals now (Impl.drainSteps t.origin
          (specStep (.external rq) now (current w t.origin)).2.1 now) := by
      simp [lin, specSteps, hw, hdoc0, internals, he2]
    rw [hlin]
    simp only [Abstract.exec]
    refine ⟨?_, ?_, ?_, hsinv' hsinv, htxns'⟩
    · rw [hres, hdec]
      simp only
      rw [he1, ← h1.1, step_external_reply]
      simp only [obsOf, obsFor, obsOf_internals]
    · refine Rel.of_RelD h2.2 ?_ hother' ?_
      · rw [hcur', hdec]; rfl
      · rw [hwire, hdec]; simp only [commit_send, he3]; rfl
    · exact hdocs' _ hd2 (by rw [hdec]; rfl)
  | sweep fired =>
    have hdec : decOf t now = Impl.decide t.origin (.sweep fired) now (current w t.origin) := by
      simp only [decOf, hw, hdoc0]
    rw [decide_sweep, drain_eq, triggers_eq now _ _ (drainSteps_about hd0 now)] at hdec
    have h2 := specFold_sim (S := S) now (current w t.origin) []
      (Impl.drainSteps t.origin (current w t.origin) now)
      (RelD.init hrel t.origin) hd0 (drainSteps_about hd0 now)
    have hd2 := specFold_origins now _ _ hd0 (drainSteps_about hd0 now)
    have hlin : lin = internals now (Impl.drainSteps t.origin (current w t.origin) now) := by
      simp [lin, specSteps, hw, hdoc0, internals]
    rw [hlin]
    refine ⟨?_, ?_, ?_, hsinv' hsinv, htxns'⟩
    · rw [obsOf_internals]; rfl
    · refine Rel.of_RelD h2.2 ?_ hother' ?_
      · rw [hcur', hdec]; rfl
      · rw [hwire, hdec]; rfl
    · exact hdocs' _ hd2 (by rw [hdec]; rfl)

theorem step_sim (st : Impl.Step) (now : Nat) (s : State) (S : ServerState)
    (hinv : Inv s) (hrel : Rel s.world S) :
    let lin := (expand st now s).map (fun a => (a, now))
    obsOf lin (Abstract.exec true lin S).1 = (Impl.step st now s).1.toList ∧
    Rel (Impl.step st now s).2.world (Abstract.exec true lin S).2 ∧
    Inv (Impl.step st now s).2 := by
  intro lin
  cases st with
  | stutter =>
    exact ⟨rfl, hrel, hinv⟩
  | «begin» o work =>
    simp only [Impl.step, Impl.begin]
    refine ⟨rfl, ?_, ?_⟩
    · split <;> exact hrel
    · split
      · rename_i hguard
        refine ⟨hinv.sinv, hinv.docs, hinv.timers, ?_, ?_⟩
        · intro t ht
          simp only [List.mem_append, List.mem_singleton] at ht
          rcases ht with ht | rfl
          · exact hinv.txns t ht
          · exact TxnInv.fresh hinv.sinv o work
        · intro t ht
          simp only [List.mem_append, List.mem_singleton] at ht
          rcases ht with ht | rfl
          · exact hinv.works t ht
          · simpa using hguard.1
      · exact hinv
  | commit i =>
    cases hget : s.inflight[i]? with
    | none =>
      have : Impl.step (.commit i) now s = (none, s) := by
        simp only [Impl.step, Impl.commit, hget]
      simp only [lin, expand, hget, List.map_nil, Abstract.exec, obsOf, this]
      exact ⟨rfl, hrel, hinv⟩
    | some t =>
      have ht : t ∈ s.inflight := List.mem_of_getElem? hget
      have hstep : Impl.step (.commit i) now s = Impl.commit i now s := rfl
      rw [hstep, commit_eq hget]
      cases hres : (Impl.runC (Impl.transact t.work now) (envOf t) s.world).1 with
      | none =>
        obtain ⟨hget', hwire, hnext, hsinv⟩ := commit_rejected hres
        have htim := timers_rejected hres hinv.timers
        have hlin : lin = [] := by simp only [lin, expand, hget, hres, List.map_nil]
        rw [hlin]
        simp only [Abstract.exec]
        generalize Impl.runC (Impl.transact t.work now) (envOf t) s.world = r
          at hget' hwire hnext hsinv htim hres ⊢
        refine ⟨?_, ?_, ?_⟩
        · cases t.work <;> rfl
        · refine ⟨?_, hrel.sched, ?_⟩
          · intro j
            rw [← hrel.find j]
            simp only [Impl.World.find?]
            rw [current_of_get_eq (hget' j.origin)]
          · rw [hrel.outbox, hwire]
        · refine ⟨hsinv hinv.sinv, ?_, htim, ?_, ?_⟩
          · intro o ob hob
            rw [current_of_get_eq (hget' o)] at hob
            exact hinv.docs o ob hob
          · intro u hu
            exact TxnInv.of_get_eq hget' hnext (hinv.txns u (mem_of_mem_eraseIdx _ _ _ hu))
          · intro u hu
            exact hinv.works u (mem_of_mem_eraseIdx _ _ _ hu)
      | some res =>
        have hlin : lin = (specSteps t now).map (fun a => (a, now)) := by
          simp only [lin, expand, hget, hres]
        rw [hlin]
        obtain ⟨hobs, hrel', hdocs', hsinv', htxns'⟩ :=
          accepted_sim (t := t) (now := now) (w := s.world) (S := S)
            hrel hinv.sinv hinv.docs (hinv.txns t ht) (hinv.works t ht) hres
        have htim := timers_accepted hres (hinv.txns t ht) hinv.timers
        generalize Impl.runC (Impl.transact t.work now) (envOf t) s.world = r
          at hobs hrel' hdocs' hsinv' htxns' htim hres ⊢
        refine ⟨?_, hrel', ?_⟩
        · rw [hobs]
          exact obsFor_eq _ _ _
        · refine ⟨hsinv', hdocs', htim, ?_, ?_⟩
          · intro u hu
            exact htxns' u (hinv.txns u (mem_of_mem_eraseIdx _ _ _ hu))
          · intro u hu
            exact hinv.works u (mem_of_mem_eraseIdx _ _ _ hu)

theorem run_sim : ∀ (w : List (Impl.Step × Nat)) (s : State) (S : ServerState),
    Inv s → Rel s.world S →
    obsOf (linearize w s) (Abstract.exec true (linearize w s) S).1 = (Impl.run w s).1 ∧
    Rel (Impl.run w s).2.world (Abstract.exec true (linearize w s) S).2 ∧
    Inv (Impl.run w s).2
  | [], s, S, hinv, hrel => ⟨rfl, hrel, hinv⟩
  | (st, n) :: w, s, S, hinv, hrel => by
      obtain ⟨h1, h2, h3⟩ := step_sim st n s S hinv hrel
      obtain ⟨ih1, ih2, ih3⟩ := run_sim w (Impl.step st n s).2
        (Abstract.exec true ((expand st n s).map (fun a => (a, n))) S).2 h3 h2
      simp only [linearize, run_cons]
      rw [exec_append]
      refine ⟨?_, ih2, ih3⟩
      simp only
      rw [obsOf_append _ _ _ _ (exec_length _ S), h1, ih1]

theorem refines (w : List (Impl.Step × Nat)) :
    obsOf (linearize w State.init)
        (Abstract.exec true (linearize w State.init) ServerState.init).1 =
      (Impl.run w State.init).1 ∧
    Rel (Impl.run w State.init).2.world
        (Abstract.exec true (linearize w State.init) ServerState.init).2 :=
  let h := run_sim w State.init ServerState.init Inv.init Rel.init
  ⟨h.1, h.2.1⟩

theorem commit_accepted_is_atomic {s : State} (hinv : Inv s) {i now : Nat} {t : Txn}
    (hget : s.inflight[i]? = some t) {res : Reply}
    (hacc : (Impl.runC (Impl.transact t.work now) (envOf t) s.world).1 = some res) :
    Impl.runC (Impl.transact t.work now) (envOf t) s.world =
      Impl.atomic t.origin t.work now s.world := by
  have ht : t ∈ s.inflight := List.mem_of_getElem? hget
  obtain ⟨_, hcond, _⟩ := commit_accepted hacc
  have hsnap := accepted_snapshot (hinv.txns t ht) hcond
  simp only [Impl.atomic, envOf, hsnap]

theorem linearize_nows_mem : ∀ (w : List (Impl.Step × Nat)) (s : State),
    ∀ n ∈ (linearize w s).map Prod.snd, n ∈ w.map Prod.snd
  | [], _, n, h => by simp [linearize] at h
  | (st, m) :: w, s, n, h => by
      simp only [linearize, List.map_append, List.mem_append, List.map_map, List.map_cons] at h ⊢
      rcases h with h | h
      · rw [List.mem_cons]; left
        simp only [List.mem_map, Function.comp] at h
        obtain ⟨_, _, hm⟩ := h
        rw [← hm]
      · rw [List.mem_cons]; right
        exact linearize_nows_mem w _ n h

theorem pairwise_map_const {α : Type} (l : List α) (m : Nat) :
    (l.map (fun _ => m)).Pairwise (· ≤ ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    refine List.Pairwise.cons ?_ ih
    intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨_, _, rfl⟩ := hb
    exact Nat.le_refl _

theorem linearize_nows_pairwise : ∀ (w : List (Impl.Step × Nat)) (s : State),
    (w.map Prod.snd).Pairwise (· ≤ ·) → ((linearize w s).map Prod.snd).Pairwise (· ≤ ·)
  | [], _, _ => List.Pairwise.nil
  | (st, m) :: w, s, h => by
      simp only [List.map_cons, List.pairwise_cons] at h
      simp only [linearize, List.map_append, List.map_map]
      rw [List.pairwise_append]
      refine ⟨?_, linearize_nows_pairwise w _ h.2, ?_⟩
      · have : (Prod.snd ∘ fun a : Abstract.Event => (a, m)) = fun _ => m := rfl
        rw [this]
        exact pairwise_map_const _ _
      · intro a ha b hb
        simp only [List.mem_map, Function.comp] at ha
        obtain ⟨_, _, rfl⟩ := ha
        exact h.1 b (linearize_nows_mem w _ b hb)

end Refinement
