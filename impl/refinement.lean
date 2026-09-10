import impl.commit

/-!  # The refinement — every behaviour of the implementation is one of
the specification

The claim, and what backs it.

THE CLAIM. Take any finite run of the implementation (`Impl.run`):
transactions beginning and committing in any interleaving, sweeps
firing whenever, the CAS accepting some commits and refusing others.
Collect what a client could see — every answered request, with its
answer and the instant it was answered. Then there is a run of the
specification (`Abstraction.runFin`) from the initial state whose
answered requests are exactly those, in that order, at those instants,
and whose final state agrees with the implementation's final world on
every lookup. The witness is CONSTRUCTED — `linearize` — not merely
asserted to exist: each accepted commit becomes the specification's
external step followed by the internal steps the sweep performed, and
everything else becomes nothing.

WHAT BACKS IT, in three layers.

  1. One specification step against one document is the same step
     against the whole state (`stepDoc_sim`): the frame lemmas of
     `frame.lean` say the handler cannot tell the two apart, and the
     lookup lemmas of `apply.lean` say the writes land the same way.
     A sweep is a sequence of such steps (`stepDocs_sim`).

  2. An accepted commit decided against the CURRENT document
     (`accepted_snapshot_current`). This is the CAS: the write was
     conditioned on the version the snapshot was read at; versions never
     recur (`Cas.put_version_fresh`); so the version still being there
     means the document still is. A refused commit changed no document
     and sent nothing (`rejected_frame`) — the only thing that landed is
     the timer it armed first, which no lookup sees.

  3. The world after an accepted commit is the old world with one
     document replaced and the sends appended to the wire
     (`accepted_world`), which is exactly the shape layer 1 produces.

The relation between a world and a specification state is by LOOKUP
(`Rel`): every id finds the same object on both sides, the schedules are
empty, and the wire is the outbox. It is not equality — the
specification's object list is in the order its own writes left it,
the world's documents are in the order the bucket lists them — and it
does not need to be, because no answer this implementation gives
depends on the order.

THE INVARIANT the induction carries (`Inv`) is three facts about the
world: every stored version is below the store's counter (what makes
versions fresh); every document holds only objects of its own origin
(what makes lookup by origin sound); and every in-flight snapshot is
either at the version still stored, in which case it IS the stored
document, or at a version that has moved (what makes layer 2 work). -/

namespace Refinement

open ServerModel AbstractModel
open Equivalence (Request Response)
open Abstraction (InternalStep)
open Impl (OriginDoc World Key Blob Work Txn State Obs)
open Apply Commit

/-! ## Which origin a step is about -/

def InternalStep.about (o : String) : InternalStep → Prop
  | .promiseTimeout r   => r.id.origin = o
  | .callback r         => r.awaited.origin = o ∧ r.awaiter.origin = o
  | .listener r         => r.awaited.origin = o
  | .taskLeaseTimeout r => r.id.origin = o
  | .taskRetryTimeout r => r.id.origin = o
  | .scheduleTimeout _  => False

def Step.about (o : String) : Abstraction.Step → Prop
  | .external rq => rq.origin? = some o
  | .internal st => InternalStep.about o st
  | .idle        => True

/-- A single-origin heartbeat names the origin of every reference. -/
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

/-! ## The handler of a step is congruent and local -/

theorem Cong.handleExternal {o : String} {rq : Request} (h : rq.origin? = some o) (now : Nat) :
    Frame.Cong o (Abstraction.handleExternal rq now) := by
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
    (e : AbstractModel.Env) : Frame.LocAt o (Abstraction.handleExternal rq now) e := by
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

theorem Cong.handleInternal {o : String} {st : InternalStep} (h : InternalStep.about o st) (now : Nat) :
    Frame.Cong o (Abstraction.handleInternal st now) := by
  cases st with
  | promiseTimeout r   => exact Frame.Cong.processPromiseTimeout h now
  | callback r         => exact Frame.Cong.processCallback h.1 h.2 now
  | listener r         => exact Frame.Cong.processListener h now
  | taskLeaseTimeout r => exact Frame.Cong.processLeaseTimeout h now
  | taskRetryTimeout r => exact Frame.Cong.processRetryTimeout h now
  | scheduleTimeout r  => exact absurd h id

theorem LocAt.handleInternal {o : String} {st : InternalStep} (h : InternalStep.about o st) (now : Nat)
    (e : AbstractModel.Env) : Frame.LocAt o (Abstraction.handleInternal st now) e := by
  cases st with
  | promiseTimeout r   => exact Frame.LocAt.processPromiseTimeout h now e
  | callback r         => exact Frame.LocAt.processCallback h.1 h.2 now e
  | listener r         => exact Frame.LocAt.processListener h now e
  | taskLeaseTimeout r => exact Frame.LocAt.processLeaseTimeout h now e
  | taskRetryTimeout r => exact Frame.LocAt.processRetryTimeout h now e
  | scheduleTimeout r  => exact absurd h id

theorem Cong.handle {o : String} {st : Abstraction.Step} (h : Step.about o st) (now : Nat) :
    Frame.Cong o (Abstraction.handle st now) := by
  cases st with
  | external rq => exact Cong.handleExternal h now
  | internal st => exact Frame.Cong.bind (Cong.handleInternal h now) (fun _ => Frame.Cong.pure _)
  | idle        => exact Frame.Cong.pure _

theorem LocAt.handle {o : String} {st : Abstraction.Step} (h : Step.about o st) (now : Nat)
    (e : AbstractModel.Env) : Frame.LocAt o (Abstraction.handle st now) e := by
  cases st with
  | external rq => exact LocAt.handleExternal h now e
  | internal st => exact Frame.LocAt.bind (LocAt.handleInternal h now e) (Frame.LocAt.pure _ _)
  | idle        => exact Frame.LocAt.pure _ _

/-! ## The relation -/

/-- What the world says about an id: look in its origin's document. -/
def _root_.Impl.World.find? (w : World) : Lookup := fun j =>
  (currentDoc w j.origin).objects.find? (·.id == j)

/-- The world and a specification state, related by lookup. -/
structure Rel (w : World) (S : ServerState) : Prop where
  find   : ∀ j, w.find? j = lookup S j
  sched  : S.schedules = []
  outbox : S.outbox = w.wire

/-- The relation during a commit: origin `o`'s document is being rewritten
    (`d` is where it stands), and `sends` is what has been owed so far. -/
def virtFind (w : World) (o : String) (d : OriginDoc) : Lookup := fun j =>
  if j.origin = o then d.objects.find? (·.id == j) else w.find? j

structure RelD (w : World) (o : String) (d : OriginDoc) (sends : List (String × Message))
    (S : ServerState) : Prop where
  find   : ∀ j, virtFind w o d j = lookup S j
  sched  : S.schedules = []
  outbox : S.outbox = sendsFold w.wire sends

theorem RelD.init {w : World} {S : ServerState} (h : Rel w S) (o : String) :
    RelD w o (currentDoc w o) [] S where
  find := by
    intro j
    simp only [virtFind]
    split
    · rename_i hj; rw [← h.find j]; simp only [World.find?, hj]
    · exact h.find j
  sched := h.sched
  outbox := h.outbox

/-- Every object a document holds is of the document's origin. -/
def DocInv (w : World) : Prop :=
  ∀ o, ∀ ob ∈ (currentDoc w o).objects, ob.id.origin = o

theorem World.find?_wf (w : World) : (Impl.World.find? w).wf := by
  intro j ob h
  have := List.find?_some h
  simpa using this

/-! ## One step against a document -/

theorem stepDoc_eq (mat : Bool) (st : Abstraction.Step) (now : Nat) (d : OriginDoc) :
    Impl.stepDoc mat st now d =
      ((Abstraction.handle st now { state := d.toState, mat := mat }).1,
       OriginDoc.ofState
         (applyAll d.toState (Abstraction.handle st now { state := d.toState, mat := mat }).2)
         d.timerAt,
       Impl.sendsOf (Abstraction.handle st now { state := d.toState, mat := mat }).2) := rfl

theorem stepOf_eq (mat : Bool) (st : Abstraction.Step) (now : Nat) (S : ServerState) :
    Abstraction.stepOf mat st now S =
      ((Abstraction.handle st now { state := S, mat := mat, config := {} }).1,
       applyAll S (Abstraction.handle st now { state := S, mat := mat, config := {} }).2) := rfl

/-- The environments of the two sides agree on origin `o`. -/
theorem envEquiv_of_RelD {w : World} {o : String} {d : OriginDoc} {sends : List (String × Message)}
    {S : ServerState} (h : RelD w o d sends S) (mat : Bool) :
    Frame.EnvEquiv o { state := d.toState, mat := mat } { state := S, mat := mat, config := {} } where
  mat := rfl
  config := rfl
  find := by
    intro j hj
    have := h.find j
    simp only [virtFind, hj, ↓reduceIte, lookup] at this
    exact this

/-- A document's objects, before and after a step: local effects keep them
    of the origin. -/
theorem stepDoc_origins {o : String} {d : OriginDoc} (hd : ∀ ob ∈ d.objects, ob.id.origin = o)
    {st : Abstraction.Step} (hab : Step.about o st) (mat : Bool) (now : Nat) :
    ∀ ob ∈ (Impl.stepDoc mat st now d).2.1.objects, ob.id.origin = o := by
  rw [stepDoc_eq]
  exact origins_applyAll (LocAt.handle hab now _) hd

theorem stepDoc_sim {w : World} {o : String} {d : OriginDoc} {sends : List (String × Message)}
    {S : ServerState} (h : RelD w o d sends S)
    {st : Abstraction.Step} (hab : Step.about o st) (mat : Bool) (now : Nat) :
    (Abstraction.stepOf mat st now S).1 = (Impl.stepDoc mat st now d).1 ∧
    RelD w o (Impl.stepDoc mat st now d).2.1 (sends ++ (Impl.stepDoc mat st now d).2.2)
      (Abstraction.stepOf mat st now S).2 := by
  have hcong := Cong.handle hab now _ _ (envEquiv_of_RelD h mat)
  have hloc : ∀ f ∈ (Abstraction.handle st now { state := S, mat := mat, config := {} }).2,
      Frame.Effect.Local o f :=
    LocAt.handle hab now { state := S, mat := mat, config := {} }
  rw [stepDoc_eq, stepOf_eq]
  simp only
  rw [hcong]
  refine ⟨rfl, ?_⟩
  generalize (Abstraction.handle st now { state := S, mat := mat, config := {} }).2 = fx at hloc ⊢
  have hagree : Agree o (lookup d.toState) (lookup S) := by
    intro j hj
    have := h.find j
    simpa [virtFind, hj, lookup, OriginDoc.toState] using this
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases hj : j.origin = o
    · have h1 := lookupAfter_congr hagree fx j hj
      rw [← lookup_applyAll, ← lookup_applyAll] at h1
      simpa [virtFind, hj, lookup, OriginDoc.ofState] using h1
    · have h1 := lookupAfter_frame (lookup_wf S) hloc j hj
      rw [← lookup_applyAll] at h1
      have h2 := h.find j
      simp only [virtFind, hj, ↓reduceIte] at h2
      simp only [virtFind, hj, ↓reduceIte]
      rw [h2, h1]
  · rw [schedules_applyAll _ hloc]; exact h.sched
  · rw [outbox_applyAll, h.outbox, sendsFold_append]

/-- A sequence of internal steps against a document. -/
def internals (now : Nat) (sts : List InternalStep) : List (Abstraction.Step × Nat) :=
  sts.map fun st => (.internal st, now)

theorem stepDocs_origins {o : String} (mat : Bool) (now : Nat) :
    ∀ (d : OriginDoc) (sts : List InternalStep), (∀ ob ∈ d.objects, ob.id.origin = o) →
      (∀ st ∈ sts, InternalStep.about o st) →
      ∀ ob ∈ (Impl.stepDocs mat now d sts).1.objects, ob.id.origin = o
  | d, [], hd, _ => hd
  | d, st :: sts, hd, hab => by
      simp only [Impl.stepDocs]
      exact stepDocs_origins mat now _ sts
        (stepDoc_origins (st := .internal st) hd (hab st (List.mem_cons_self ..)) mat now)
        (fun s hs => hab s (List.mem_cons_of_mem _ hs))

theorem stepDocs_sim {w : World} {o : String} {S : ServerState} (mat : Bool) (now : Nat) :
    ∀ (d : OriginDoc) (sends : List (String × Message)) (sts : List InternalStep),
      RelD w o d sends S → (∀ ob ∈ d.objects, ob.id.origin = o) →
      (∀ st ∈ sts, InternalStep.about o st) →
      (Abstraction.runFin mat (internals now sts) S).1 = sts.map (fun _ => Response.silent) ∧
      RelD w o (Impl.stepDocs mat now d sts).1 (sends ++ (Impl.stepDocs mat now d sts).2)
        (Abstraction.runFin mat (internals now sts) S).2
  | d, sends, [], h, _, _ => by
      refine ⟨rfl, ?_⟩
      simpa [Impl.stepDocs, internals, Abstraction.runFin] using h
  | d, sends, st :: sts, h, hd, hab => by
      have h1 := stepDoc_sim h (st := .internal st) (hab st (List.mem_cons_self ..)) mat now
      have hd' := stepDoc_origins hd (st := .internal st) (hab st (List.mem_cons_self ..)) mat now
      have ih := stepDocs_sim (S := (Abstraction.stepOf mat (.internal st) now S).2) mat now
        (Impl.stepDoc mat (.internal st) now d).2.1
        (sends ++ (Impl.stepDoc mat (.internal st) now d).2.2) sts h1.2 hd'
        (fun s hs => hab s (List.mem_cons_of_mem _ hs))
      simp only [internals, List.map_cons, Abstraction.runFin, Impl.stepDocs] at ih ⊢
      refine ⟨?_, ?_⟩
      · rw [ih.1]
        have : (Abstraction.stepOf mat (.internal st) now S).1 = .silent := by
          rw [stepOf_eq]; rfl
        rw [this]
      · simpa [List.append_assoc] using ih.2

/-! ## The sweep fires only steps about its origin -/

theorem timeoutSteps_about {o : String} {d : OriginDoc} (hd : ∀ ob ∈ d.objects, ob.id.origin = o)
    (now : Nat) : ∀ st ∈ Impl.timeoutSteps d now, InternalStep.about o st := by
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

theorem obligationSteps_about {o : String} {d : OriginDoc} (hd : ∀ ob ∈ d.objects, ob.id.origin = o) :
    ∀ st ∈ Impl.obligationSteps o d, InternalStep.about o st := by
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

theorem retrySteps_about {o : String} {d : OriginDoc} (hd : ∀ ob ∈ d.objects, ob.id.origin = o)
    (now : Nat) : ∀ st ∈ Impl.retrySteps d now, InternalStep.about o st := by
  intro st hst
  simp only [Impl.retrySteps, List.mem_filterMap] at hst
  obtain ⟨ob, hob, h⟩ := hst
  split at h
  · split at h
    · cases h; exact hd ob hob
    · cases h
  · cases h

theorem drainSteps_about {o : String} {d : OriginDoc} (hd : ∀ ob ∈ d.objects, ob.id.origin = o)
    (mat : Bool) (now : Nat) : ∀ st ∈ Impl.drainSteps mat o d now, InternalStep.about o st := by
  intro st hst
  simp only [Impl.drainSteps, List.mem_append] at hst
  have h1 := timeoutSteps_about hd now
  have hd1 := stepDocs_origins mat now d _ hd h1
  have h2 := obligationSteps_about hd1
  have hd2 := stepDocs_origins mat now _ _ hd1 h2
  have h3 := retrySteps_about hd2 now
  rcases hst with (hst | hst) | hst
  · exact h1 st hst
  · exact h2 st hst
  · exact h3 st hst

/-! ## Refused and accepted commits -/

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

/-- A refused commit: no document moved, nothing was sent. -/
theorem commit_rejected {mat : Bool} {t : Txn} {now : Nat} {w : World}
    (h : (Impl.runC (Impl.transact mat t.work now) (envOf mat t) w).1 = none) :
    (∀ o', (Impl.runC (Impl.transact mat t.work now) (envOf mat t) w).2.store.get (.doc o') =
             w.store.get (.doc o')) ∧
    (Impl.runC (Impl.transact mat t.work now) (envOf mat t) w).2.wire = w.wire ∧
    w.store.next ≤ (Impl.runC (Impl.transact mat t.work now) (envOf mat t) w).2.store.next ∧
    (SInv w.store → SInv (Impl.runC (Impl.transact mat t.work now) (envOf mat t) w).2.store) := by
  have harm := applyEffects_nodoc (o := t.origin) (c := (envOf mat t).cond) _ w
    (armFx_nodoc (envOf mat t).doc (decOf mat t now).2.1)
  rw [runC_transact] at h ⊢
  cases hp : (armed mat t now w).store.put (.doc t.origin) (.doc (decOf mat t now).2.1)
      (envOf mat t).cond with
  | ok x => obtain ⟨st, v⟩ := x; simp [hp] at h
  | rejected =>
    simp only
    refine ⟨harm.2.1, ?_, harm.2.2.2.1, harm.2.2.2.2⟩
    rw [show armed mat t now w =
        (Impl.applyEffects t.origin (envOf mat t).cond w
          (Impl.armFx (envOf mat t).doc (decOf mat t now).2.1)).1 from rfl]
    rw [harm.2.2.1, armFx_nosend]; rfl

/-- An accepted commit: the answer is the decision's, the write was made
    against the current version, the origin's document is the decided
    one, every other document is untouched, the sends are on the wire,
    and both store invariants survive. -/
theorem commit_accepted {mat : Bool} {t : Txn} {now : Nat} {w : World} {res : Response}
    (h : (Impl.runC (Impl.transact mat t.work now) (envOf mat t) w).1 = some res) :
    res = (decOf mat t now).1 ∧
    (envOf mat t).cond.holds (w.store.version? (.doc t.origin)) = true ∧
    (∃ v, (Impl.runC (Impl.transact mat t.work now) (envOf mat t) w).2.store.get (.doc t.origin) =
            some (.doc (decOf mat t now).2.1, v)) ∧
    (∀ o', o' ≠ t.origin →
      (Impl.runC (Impl.transact mat t.work now) (envOf mat t) w).2.store.get (.doc o') =
        w.store.get (.doc o')) ∧
    (Impl.runC (Impl.transact mat t.work now) (envOf mat t) w).2.wire =
      sendsFold w.wire (decOf mat t now).2.2 ∧
    (SInv w.store → SInv (Impl.runC (Impl.transact mat t.work now) (envOf mat t) w).2.store) ∧
    (∀ u, TxnInv w.store u →
      TxnInv (Impl.runC (Impl.transact mat t.work now) (envOf mat t) w).2.store u) := by
  have harm := applyEffects_nodoc (o := t.origin) (c := (envOf mat t).cond) _ w
    (armFx_nodoc (envOf mat t).doc (decOf mat t now).2.1)
  have harmed : armed mat t now w =
      (Impl.applyEffects t.origin (envOf mat t).cond w
        (Impl.armFx (envOf mat t).doc (decOf mat t now).2.1)).1 := rfl
  rw [runC_transact] at h ⊢
  cases hp : (armed mat t now w).store.put (.doc t.origin) (.doc (decOf mat t now).2.1)
      (envOf mat t).cond with
  | rejected => simp [hp] at h
  | ok x =>
    obtain ⟨st, v⟩ := x
    simp only [hp, Option.some.injEq] at h
    simp only
    have hrest := applyEffects_nodoc (o := t.origin) (c := (envOf mat t).cond)
      (Impl.delFx (envOf mat t).doc (decOf mat t now).2.1 t.work ++ Impl.sendFx (decOf mat t now).2.2)
      { armed mat t now w with store := st }
      (by intro f hf
          simp only [List.mem_append] at hf
          rcases hf with hf | hf
          · exact delFx_nodoc _ _ _ f hf
          · exact sendFx_nodoc _ f hf)
    have hget_armed : ∀ o', (armed mat t now w).store.get (.doc o') = w.store.get (.doc o') := by
      intro o'; rw [harmed]; exact harm.2.1 o'
    refine ⟨h.symm, ?_, ⟨v, ?_⟩, ?_, ?_, ?_, ?_⟩
    · have := put_ok_holds hp
      rwa [version?_of_get_eq (hget_armed t.origin)] at this
    · rw [hrest.2.1]
      exact Cas.get_put_same _ _ _ _ _ _ hp
    · intro o' ho
      rw [hrest.2.1]
      show st.get (.doc o') = _
      rw [Cas.get_put_other _ _ _ _ _ _ _ hp (by simpa using ho)]
      exact hget_armed o'
    · rw [hrest.2.2.1]
      show sendsFold (armed mat t now w).wire _ = _
      rw [harmed, harm.2.2.1, armFx_nosend, sendsOfC_append, delFx_nosend, sendsOfC_sendFx]
      rfl
    · intro hs
      exact hrest.2.2.2.2 (put_ok_sinv hp (harmed ▸ harm.2.2.2.2 hs))
    · intro u hu
      have h1 : TxnInv (armed mat t now w).store u :=
        TxnInv.of_get_eq hget_armed (harmed ▸ harm.2.2.2.1) hu
      have h2 : TxnInv st u := TxnInv.of_put hp h1
      exact TxnInv.of_get_eq hrest.2.1 hrest.2.2.2.1 h2

/-- The CAS, as the fact the simulation needs: an accepted commit's
    snapshot is the origin's current document. -/
theorem accepted_snapshot {mat : Bool} {t : Txn} {w : World} (hinv : TxnInv w.store t)
    (hc : (envOf mat t).cond.holds (w.store.version? (.doc t.origin)) = true) :
    t.snapshot = w.doc? t.origin := by
  cases hs : t.snapshot with
  | none =>
    have hc' : w.store.version? (.doc t.origin) = none := by
      have := hc
      simp only [envOf, Impl.Env.cond, hs, Cas.Cond.holds, Option.isNone_iff_eq_none] at this
      exact this
    simp only [Cas.Store.version?, Option.map_eq_none_iff] at hc'
    simp [World.doc?, hc']
  | some dv =>
    obtain ⟨d, v⟩ := dv
    have hc' : w.store.version? (.doc t.origin) = some v := by
      have := hc
      simp only [envOf, Impl.Env.cond, hs, Cas.Cond.holds, beq_iff_eq] at this
      exact this
    simp only [Cas.Store.version?, Option.map_eq_some_iff] at hc'
    obtain ⟨⟨b, v'⟩, hg, hv⟩ := hc'
    simp only at hv
    subst hv
    have := (hinv d v' hs).2 b hg
    subst this
    simp [World.doc?, hg]

theorem envOf_doc_eq_current {mat : Bool} {t : Txn} {w : World} (h : t.snapshot = w.doc? t.origin) :
    (envOf mat t).doc = currentDoc w t.origin := by
  simp only [envOf, Impl.Env.doc, currentDoc, h]
  cases w.doc? t.origin with
  | none => rfl
  | some dv => rfl

/-! ## The world, before and after -/

theorem currentDoc_of_get {w : World} {o : String} {d : OriginDoc} {v : Cas.Version}
    (h : w.store.get (.doc o) = some (.doc d, v)) : currentDoc w o = d := by
  simp [currentDoc, World.doc?, h]

theorem currentDoc_of_get_eq {w w' : World} {o : String}
    (h : w'.store.get (.doc o) = w.store.get (.doc o)) : currentDoc w' o = currentDoc w o := by
  simp only [currentDoc, World.doc?, h]

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

/-- A fresh snapshot of the current document satisfies its invariant. -/
theorem TxnInv.fresh {w : World} (hs : SInv w.store) (o : String) (work : Work) :
    TxnInv w.store ⟨o, work, w.doc? o⟩ := by
  intro d v hsnap
  simp only [World.doc?] at hsnap
  cases hg : w.store.get (.doc o) with
  | none => simp [hg] at hsnap
  | some x =>
    obtain ⟨b, v'⟩ := x
    cases b with
    | timer => simp [hg] at hsnap
    | doc d' =>
      simp only [hg, Option.some.injEq, Prod.mk.injEq] at hsnap
      obtain ⟨rfl, rfl⟩ := hsnap
      refine ⟨hs _ (mem_of_get hg), ?_⟩
      intro b hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      exact hb.1.symm

/-! ## The system -/

/-- The invariant the induction carries. -/
structure Inv (s : State) : Prop where
  sinv  : SInv s.world.store
  docs  : DocInv s.world
  txns  : ∀ t ∈ s.inflight, TxnInv s.world.store t
  works : ∀ t ∈ s.inflight, t.work.origin? t.origin = some t.origin

theorem Inv.init : Inv State.init where
  sinv := fun _ h => by simp [State.init] at h
  docs := fun o ob h => by
    simp [currentDoc, World.doc?, Cas.Store.get, State.init] at h
  txns := fun _ h => by simp [State.init] at h
  works := fun _ h => by simp [State.init] at h

theorem Rel.init : Rel State.init.world ServerState.init where
  find := fun j => by simp [Impl.World.find?, currentDoc, World.doc?, Cas.Store.get, State.init, lookup,
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

/-- The specification steps an accepted commit stands for. -/
def specSteps (mat : Bool) (t : Txn) (now : Nat) : List Abstraction.Step :=
  match t.work with
  | .request rq =>
      .external rq ::
        (Impl.drainSteps mat t.origin
          (Impl.stepDoc mat (.external rq) now (envOf mat t).doc).2.1 now).map .internal
  | .sweep _ =>
      (Impl.drainSteps mat t.origin (envOf mat t).doc now).map .internal

/-- What one implementation step becomes: an accepted commit's steps;
    nothing otherwise. -/
def expand (mat : Bool) (st : Impl.Step) (now : Nat) (s : State) : List Abstraction.Step :=
  match st with
  | .commit i =>
      match s.inflight[i]? with
      | none   => []
      | some t =>
          match (Impl.runC (Impl.transact mat t.work now) (envOf mat t) s.world).1 with
          | none   => []
          | some _ => specSteps mat t now
  | _ => []

/-- The linearization: the specification run an implementation run
    stands for, step by step. -/
def linearize (mat : Bool) : List (Impl.Step × Nat) → State → List (Abstraction.Step × Nat)
  | [],           _ => []
  | (st, n) :: w, s =>
      (expand mat st n s).map (fun a => (a, n)) ++ linearize mat w (Impl.step mat st n s).2

/-- The observations of a specification run: its answered requests. -/
def obsOf : List (Abstraction.Step × Nat) → List Response → List Obs
  | (.external rq, n) :: w, r :: rs => ⟨rq, r, n⟩ :: obsOf w rs
  | _ :: w, _ :: rs                 => obsOf w rs
  | _, _                            => []

theorem obsOf_internals (now : Nat) : ∀ (sts : List InternalStep) (rs : List Response),
    obsOf (internals now sts) rs = []
  | [], rs => by cases rs <;> rfl
  | st :: sts, [] => rfl
  | st :: sts, r :: rs => by
      simp only [internals, List.map_cons, obsOf]
      exact obsOf_internals now sts rs

theorem runFin_length (mat : Bool) : ∀ (w : List (Abstraction.Step × Nat)) (S : ServerState),
    (Abstraction.runFin mat w S).1.length = w.length
  | [], _ => rfl
  | (st, n) :: w, S => by
      simp only [Abstraction.runFin, List.length_cons]
      rw [runFin_length mat w]

theorem runFin_append (mat : Bool) : ∀ (a b : List (Abstraction.Step × Nat)) (S : ServerState),
    Abstraction.runFin mat (a ++ b) S =
      ((Abstraction.runFin mat a S).1 ++ (Abstraction.runFin mat b (Abstraction.runFin mat a S).2).1,
       (Abstraction.runFin mat b (Abstraction.runFin mat a S).2).2)
  | [], b, S => by simp [Abstraction.runFin]
  | (st, n) :: a, b, S => by
      simp only [List.cons_append, Abstraction.runFin]
      rw [runFin_append mat a b]

theorem obsOf_append : ∀ (a b : List (Abstraction.Step × Nat)) (rs rs' : List Response),
    rs.length = a.length → obsOf (a ++ b) (rs ++ rs') = obsOf a rs ++ obsOf b rs'
  | [], b, [], rs', _ => by simp [obsOf]
  | [], b, r :: rs, rs', h => by simp at h
  | x :: a, b, [], rs', h => by simp at h
  | (st, n) :: a, b, r :: rs, rs', h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      cases st with
      | external rq => simp only [List.cons_append, obsOf]; rw [obsOf_append a b rs rs' h]
      | internal _ => simp only [List.cons_append, obsOf]; exact obsOf_append a b rs rs' h
      | idle => simp only [List.cons_append, obsOf]; exact obsOf_append a b rs rs' h

theorem run_cons (mat : Bool) (st : Impl.Step) (n : Nat) (w : List (Impl.Step × Nat)) (s : State) :
    Impl.run mat ((st, n) :: w) s =
      ((Impl.step mat st n s).1.toList ++ (Impl.run mat w (Impl.step mat st n s).2).1,
       (Impl.run mat w (Impl.step mat st n s).2).2) := rfl

theorem commit_eq {mat : Bool} {i now : Nat} {s : State} {t : Txn} (hget : s.inflight[i]? = some t) :
    Impl.commit mat i now s =
      ((match (Impl.runC (Impl.transact mat t.work now) (envOf mat t) s.world).1, t.work with
        | some res, .request rq => some ⟨rq, res, now⟩
        | _,        _           => none),
       { world := (Impl.runC (Impl.transact mat t.work now) (envOf mat t) s.world).2,
         inflight := s.inflight.eraseIdx i }) := by
  unfold Impl.commit
  rw [hget]
  rfl

theorem decide_request (mat : Bool) (o : String) (rq : Request) (now : Nat) (old : OriginDoc) :
    Impl.decide mat o (.request rq) now old =
      ((Impl.stepDoc mat (.external rq) now old).1,
       { (Impl.drain mat o (Impl.stepDoc mat (.external rq) now old).2.1 now).1 with
           timerAt := (Impl.drain mat o (Impl.stepDoc mat (.external rq) now old).2.1 now).1.minDeadline },
       (Impl.stepDoc mat (.external rq) now old).2.2 ++
         (Impl.drain mat o (Impl.stepDoc mat (.external rq) now old).2.1 now).2) := rfl

theorem decide_sweep (mat : Bool) (o : String) (fired : Option Nat) (now : Nat) (old : OriginDoc) :
    Impl.decide mat o (.sweep fired) now old =
      (.silent,
       { (Impl.drain mat o old now).1 with timerAt := (Impl.drain mat o old now).1.minDeadline },
       [] ++ (Impl.drain mat o old now).2) := rfl

theorem drain_eq (mat : Bool) (o : String) (d : OriginDoc) (now : Nat) :
    Impl.drain mat o d now = Impl.stepDocs mat now d (Impl.drainSteps mat o d now) := rfl

/-- From the relation during a commit to the relation after it: the
    origin's document is now `d`, everything else is as it was, and the
    wire carries the sends. -/
theorem Rel.of_RelD {w w' : World} {o : String} {d : OriginDoc} {sends : List (String × Message)}
    {S : ServerState} (h : RelD w o d sends S)
    (hdoc : (currentDoc w' o).objects = d.objects)
    (hother : ∀ o', o' ≠ o → currentDoc w' o' = currentDoc w o')
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

/-- One accepted commit, simulated: the decision's answer, and the
    relation re-established after the specification steps it stands for. -/
theorem accepted_sim {mat : Bool} {t : Txn} {now : Nat} {w : World} {S : ServerState} {res : Response}
    (hrel : Rel w S) (hsinv : SInv w.store) (hdocs : DocInv w) (htxn : TxnInv w.store t)
    (hwork : t.work.origin? t.origin = some t.origin)
    (hacc : (Impl.runC (Impl.transact mat t.work now) (envOf mat t) w).1 = some res) :
    let lin := (specSteps mat t now).map (fun a => (a, now))
    let w' := (Impl.runC (Impl.transact mat t.work now) (envOf mat t) w).2
    obsOf lin (Abstraction.runFin mat lin S).1 =
      (match t.work with
       | .request rq => [⟨rq, res, now⟩]
       | .sweep _    => []) ∧
    Rel w' (Abstraction.runFin mat lin S).2 ∧
    DocInv w' ∧ SInv w'.store ∧ (∀ u, TxnInv w.store u → TxnInv w'.store u) := by
  intro lin w'
  obtain ⟨hres, hcond, ⟨v, hdocget⟩, hother, hwire, hsinv', htxns'⟩ := commit_accepted hacc
  have hsnap := accepted_snapshot htxn hcond
  have hdoc0 : (envOf mat t).doc = currentDoc w t.origin := envOf_doc_eq_current hsnap
  have hd0 : ∀ ob ∈ (currentDoc w t.origin).objects, ob.id.origin = t.origin := hdocs t.origin
  have hcur' : currentDoc w' t.origin = (decOf mat t now).2.1 := currentDoc_of_get hdocget
  have hother' : ∀ o', o' ≠ t.origin → currentDoc w' o' = currentDoc w o' :=
    fun o' ho => currentDoc_of_get_eq (hother o' ho)
  -- the documents of every origin stay of their origin
  have hdocs' : ∀ (d2 : OriginDoc), (∀ ob ∈ d2.objects, ob.id.origin = t.origin) →
      (decOf mat t now).2.1.objects = d2.objects → DocInv w' := by
    intro d2 hd2 heq o ob hob
    by_cases ho : o = t.origin
    · subst ho; rw [hcur', heq] at hob; exact hd2 ob hob
    · rw [hother' o ho] at hob; exact hdocs o ob hob
  cases hw : t.work with
  | request rq =>
    have hab : Step.about t.origin (.external rq) := by
      show rq.origin? = some t.origin
      simpa [Work.origin?, hw] using hwork
    have hdec : decOf mat t now = Impl.decide mat t.origin (.request rq) now (currentDoc w t.origin) := by
      simp only [decOf, hw, hdoc0]
    rw [decide_request, drain_eq] at hdec
    -- layer 1: the external step
    have h1 := stepDoc_sim (RelD.init hrel t.origin) hab mat now
    have hd1 := stepDoc_origins hd0 hab mat now
    -- layer 1: the sweep
    have h2 := stepDocs_sim (S := (Abstraction.stepOf mat (.external rq) now S).2) mat now
      (Impl.stepDoc mat (.external rq) now (currentDoc w t.origin)).2.1
      ([] ++ (Impl.stepDoc mat (.external rq) now (currentDoc w t.origin)).2.2)
      (Impl.drainSteps mat t.origin (Impl.stepDoc mat (.external rq) now (currentDoc w t.origin)).2.1 now)
      h1.2 hd1 (drainSteps_about hd1 mat now)
    have hd2 := stepDocs_origins mat now _ _ hd1
      (drainSteps_about hd1 mat now)
    have hlin : lin = (Abstraction.Step.external rq, now) ::
        internals now (Impl.drainSteps mat t.origin
          (Impl.stepDoc mat (.external rq) now (currentDoc w t.origin)).2.1 now) := by
      simp [lin, specSteps, hw, hdoc0, internals]
    rw [hlin]
    simp only [Abstraction.runFin, obsOf]
    refine ⟨?_, ?_, ?_, hsinv' hsinv, htxns'⟩
    · rw [obsOf_internals, h1.1, hres]
      try rw [hdec]
    · refine Rel.of_RelD h2.2 ?_ hother' ?_
      · rw [hcur', hdec]
      · rw [hwire, hdec]; rfl
    · exact hdocs' _ hd2 (by rw [hdec])
  | sweep fired =>
    have hdec : decOf mat t now = Impl.decide mat t.origin (.sweep fired) now (currentDoc w t.origin) := by
      simp only [decOf, hw, hdoc0]
    rw [decide_sweep, drain_eq] at hdec
    have h2 := stepDocs_sim (S := S) mat now (currentDoc w t.origin) []
      (Impl.drainSteps mat t.origin (currentDoc w t.origin) now)
      (RelD.init hrel t.origin) hd0 (drainSteps_about hd0 mat now)
    have hd2 := stepDocs_origins mat now _ _ hd0 (drainSteps_about hd0 mat now)
    have hlin : lin = internals now (Impl.drainSteps mat t.origin (currentDoc w t.origin) now) := by
      simp [lin, specSteps, hw, hdoc0, internals]
    rw [hlin]
    refine ⟨?_, ?_, ?_, hsinv' hsinv, htxns'⟩
    · rw [obsOf_internals]
    · refine Rel.of_RelD h2.2 ?_ hother' ?_
      · rw [hcur', hdec]
      · rw [hwire, hdec]
    · exact hdocs' _ hd2 (by rw [hdec])

/-- One implementation step, simulated. -/
theorem step_sim (mat : Bool) (st : Impl.Step) (now : Nat) (s : State) (S : ServerState)
    (hinv : Inv s) (hrel : Rel s.world S) :
    let lin := (expand mat st now s).map (fun a => (a, now))
    obsOf lin (Abstraction.runFin mat lin S).1 = (Impl.step mat st now s).1.toList ∧
    Rel (Impl.step mat st now s).2.world (Abstraction.runFin mat lin S).2 ∧
    Inv (Impl.step mat st now s).2 := by
  intro lin
  cases st with
  | idle =>
    exact ⟨rfl, hrel, hinv⟩
  | «begin» o work =>
    simp only [Impl.step, Impl.begin]
    refine ⟨rfl, ?_, ?_⟩
    · split <;> exact hrel
    · split
      · rename_i hguard
        refine ⟨hinv.sinv, hinv.docs, ?_, ?_⟩
        · intro t ht
          simp only [List.mem_append, List.mem_singleton] at ht
          rcases ht with ht | rfl
          · exact hinv.txns t ht
          · exact TxnInv.fresh hinv.sinv o work
        · intro t ht
          simp only [List.mem_append, List.mem_singleton] at ht
          rcases ht with ht | rfl
          · exact hinv.works t ht
          · simpa using hguard
      · exact hinv
  | commit i =>
    cases hget : s.inflight[i]? with
    | none =>
      have : Impl.step mat (.commit i) now s = (none, s) := by
        simp only [Impl.step, Impl.commit, hget]
      simp only [lin, expand, hget, List.map_nil, Abstraction.runFin, obsOf, this]
      exact ⟨rfl, hrel, hinv⟩
    | some t =>
      have ht : t ∈ s.inflight := List.mem_of_getElem? hget
      have hstep : Impl.step mat (.commit i) now s = Impl.commit mat i now s := rfl
      rw [hstep, commit_eq hget]
      cases hres : (Impl.runC (Impl.transact mat t.work now) (envOf mat t) s.world).1 with
      | none =>
        obtain ⟨hget', hwire, hnext, hsinv⟩ := commit_rejected hres
        have hlin : lin = [] := by simp only [lin, expand, hget, hres, List.map_nil]
        rw [hlin]
        simp only [Abstraction.runFin, obsOf]
        generalize Impl.runC (Impl.transact mat t.work now) (envOf mat t) s.world = r
          at hget' hwire hnext hsinv hres ⊢
        refine ⟨?_, ?_, ?_⟩
        · cases t.work <;> rfl
        · refine ⟨?_, hrel.sched, ?_⟩
          · intro j
            rw [← hrel.find j]
            simp only [Impl.World.find?]
            rw [currentDoc_of_get_eq (hget' j.origin)]
          · rw [hrel.outbox, hwire]
        · refine ⟨hsinv hinv.sinv, ?_, ?_, ?_⟩
          · intro o ob hob
            rw [currentDoc_of_get_eq (hget' o)] at hob
            exact hinv.docs o ob hob
          · intro u hu
            exact TxnInv.of_get_eq hget' hnext (hinv.txns u (mem_of_mem_eraseIdx _ _ _ hu))
          · intro u hu
            exact hinv.works u (mem_of_mem_eraseIdx _ _ _ hu)
      | some res =>
        have hlin : lin = (specSteps mat t now).map (fun a => (a, now)) := by
          simp only [lin, expand, hget, hres]
        rw [hlin]
        obtain ⟨hobs, hrel', hdocs', hsinv', htxns'⟩ :=
          accepted_sim (mat := mat) (t := t) (now := now) (w := s.world) (S := S)
            hrel hinv.sinv hinv.docs (hinv.txns t ht) (hinv.works t ht) hres
        generalize Impl.runC (Impl.transact mat t.work now) (envOf mat t) s.world = r
          at hobs hrel' hdocs' hsinv' htxns' hres ⊢
        refine ⟨?_, hrel', ?_⟩
        · rw [hobs]
          cases t.work <;> rfl
        · refine ⟨hsinv', hdocs', ?_, ?_⟩
          · intro u hu
            exact htxns' u (hinv.txns u (mem_of_mem_eraseIdx _ _ _ hu))
          · intro u hu
            exact hinv.works u (mem_of_mem_eraseIdx _ _ _ hu)

/-- A finite run, simulated. -/
theorem run_sim (mat : Bool) : ∀ (w : List (Impl.Step × Nat)) (s : State) (S : ServerState),
    Inv s → Rel s.world S →
    obsOf (linearize mat w s) (Abstraction.runFin mat (linearize mat w s) S).1 = (Impl.run mat w s).1 ∧
    Rel (Impl.run mat w s).2.world (Abstraction.runFin mat (linearize mat w s) S).2 ∧
    Inv (Impl.run mat w s).2
  | [], s, S, hinv, hrel => ⟨rfl, hrel, hinv⟩
  | (st, n) :: w, s, S, hinv, hrel => by
      obtain ⟨h1, h2, h3⟩ := step_sim mat st n s S hinv hrel
      obtain ⟨ih1, ih2, ih3⟩ := run_sim mat w (Impl.step mat st n s).2
        (Abstraction.runFin mat ((expand mat st n s).map (fun a => (a, n))) S).2 h3 h2
      simp only [linearize, run_cons]
      rw [runFin_append]
      refine ⟨?_, ih2, ih3⟩
      simp only
      rw [obsOf_append _ _ _ _ (runFin_length mat _ S), h1, ih1]

/-! ## The theorem -/

/-- Every observable behaviour of the implementation is an observable
    behaviour of the specification.

    For every finite run of the implementation from its initial state,
    the linearization is a run of the specification from ITS initial
    state whose answered requests — request, answer, instant — are
    exactly the implementation's, in order; and whose final state agrees
    with the implementation's final world on every lookup. -/
theorem refines (mat : Bool) (w : List (Impl.Step × Nat)) :
    obsOf (linearize mat w State.init)
        (Abstraction.runFin mat (linearize mat w State.init) ServerState.init).1 =
      (Impl.run mat w State.init).1 ∧
    Rel (Impl.run mat w State.init).2.world
        (Abstraction.runFin mat (linearize mat w State.init) ServerState.init).2 :=
  let h := run_sim mat w State.init ServerState.init Inv.init Rel.init
  ⟨h.1, h.2.1⟩

/-- An accepted commit is an atomic read-modify-write of the current
    document, whatever ran between its `begin` and its `commit`. -/
theorem commit_accepted_is_atomic (mat : Bool) {s : State} (hinv : Inv s) {i now : Nat} {t : Txn}
    (hget : s.inflight[i]? = some t) {res : Response}
    (hacc : (Impl.runC (Impl.transact mat t.work now) (envOf mat t) s.world).1 = some res) :
    Impl.runC (Impl.transact mat t.work now) (envOf mat t) s.world =
      Impl.atomic mat t.origin t.work now s.world := by
  have ht : t ∈ s.inflight := List.mem_of_getElem? hget
  obtain ⟨_, hcond, _⟩ := commit_accepted hacc
  have hsnap := accepted_snapshot (hinv.txns t ht) hcond
  simp only [Impl.atomic, envOf, hsnap]

/-! ## The instants

The linearization keeps every step at the instant of the implementation
step it came from, so a run whose instants never decrease linearizes to
one whose instants never decrease — which is what `Abstraction.Valid`
asks of a specification trace. -/

theorem linearize_nows_mem (mat : Bool) : ∀ (w : List (Impl.Step × Nat)) (s : State),
    ∀ n ∈ (linearize mat w s).map Prod.snd, n ∈ w.map Prod.snd
  | [], _, n, h => by simp [linearize] at h
  | (st, m) :: w, s, n, h => by
      simp only [linearize, List.map_append, List.mem_append, List.map_map, List.map_cons] at h ⊢
      rcases h with h | h
      · rw [List.mem_cons]; left
        simp only [List.mem_map, Function.comp] at h
        obtain ⟨_, _, hm⟩ := h
        rw [← hm]
      · rw [List.mem_cons]; right
        exact linearize_nows_mem mat w _ n h

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

theorem linearize_nows_pairwise (mat : Bool) : ∀ (w : List (Impl.Step × Nat)) (s : State),
    (w.map Prod.snd).Pairwise (· ≤ ·) → ((linearize mat w s).map Prod.snd).Pairwise (· ≤ ·)
  | [], _, _ => List.Pairwise.nil
  | (st, m) :: w, s, h => by
      simp only [List.map_cons, List.pairwise_cons] at h
      simp only [linearize, List.map_append, List.map_map]
      rw [List.pairwise_append]
      refine ⟨?_, linearize_nows_pairwise mat w _ h.2, ?_⟩
      · have : (Prod.snd ∘ fun a : Abstraction.Step => (a, m)) = fun _ => m := rfl
        rw [this]
        exact pairwise_map_const _ _
      · intro a ha b hb
        simp only [List.mem_map, Function.comp] at ha
        obtain ⟨_, _, rfl⟩ := ha
        exact h.1 b (linearize_nows_mem mat w _ b hb)

end Refinement
