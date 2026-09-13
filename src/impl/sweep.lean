import impl.requests

namespace Refinement

open Protocol (Ident Message OutboxEntry Object PromiseObject TaskObject PromiseState TaskState)
open Concrete (Origin Commands)
open scoped List

theorem WF_write {org : Origin} {x X : Object} (h : WF org) (hX : X ∈ org.objects)
    (hid : x.id = X.id) (hcb : x.promise.callbacks <+ X.promise.callbacks)
    (hls : x.promise.listeners <+ X.promise.listeners) : WF (org.write x) := by
  intro ob hob
  rcases mem_write hob with rfl | hob
  · obtain ⟨h1, h2, h3⟩ := h X hX
    refine ⟨h1.sublist hls, h2.sublist hcb, fun w hw => ?_⟩
    rw [hid]
    exact h3 w (hcb.subset hw)
  · exact h ob hob

theorem WF_write_fresh {org : Origin} {x : Object} (h : WF org)
    (hx : x.promise.listeners.Nodup ∧ x.promise.callbacks.Nodup ∧
      ∀ w ∈ x.promise.callbacks, w ≠ x.id ∧ w.origin = x.id.origin) : WF (org.write x) := by
  intro ob hob
  rcases mem_write hob with rfl | hob
  · exact hx
  · exact h ob hob

theorem find_self_of_nodup : ∀ {l : List Object}, (l.map (·.id)).Nodup → ∀ {ob : Object}, ob ∈ l →
    l.find? (·.id == ob.id) = some ob
  | [], _, _, h => by cases h
  | x :: xs, hnd, ob, hob => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 hob with rfl | hob
      · simp
      · have hne : x.id ≠ ob.id := fun e => hnd.1 (e ▸ List.mem_map_of_mem hob)
        have hne' : (x.id == ob.id) = false := by simpa using hne
        simp only [List.find?_cons, hne']
        exact find_self_of_nodup hnd.2 hob

theorem project_callbacks (p : PromiseObject) (n : Nat) : (p.project n).callbacks = p.callbacks := by
  unfold PromiseObject.project
  split <;> (try split) <;> rfl

theorem project_listeners (p : PromiseObject) (n : Nat) : (p.project n).listeners = p.listeners := by
  unfold PromiseObject.project
  split <;> (try split) <;> rfl

theorem callbacks_sub (X : Object) (now : Nat) :
    (X.project now).promise.callbacks <+ X.promise.callbacks := by
  show (X.promise.project now).callbacks <+ X.promise.callbacks
  rw [project_callbacks]
  exact List.Sublist.refl _

theorem toRecord_set_listeners (p : PromiseObject) (L : List String) (id : Ident) :
    ({ p with listeners := L } : PromiseObject).toRecord id = p.toRecord id := rfl

theorem listeners_sub (X : Object) (now : Nat) :
    (X.project now).promise.listeners <+ X.promise.listeners := by
  show (X.promise.project now).listeners <+ X.promise.listeners
  rw [project_listeners]
  exact List.Sublist.refl _

theorem project_eq_of_state {p : PromiseObject} {n : Nat}
    (h : ((p.project n).state != p.state) = false) : p.project n = p := by
  unfold PromiseObject.project at h ⊢
  by_cases hc : (p.state == PromiseState.pending) = true ∧ p.timeoutAt ≤ n
  · rw [if_pos hc] at h ⊢
    have hp : p.state = .pending := by simpa using hc.1
    split at h <;> simp [hp] at h
  · rw [if_neg hc]

theorem view_eq_of_state {t : TaskObject} {p : PromiseObject}
    (h : ((t.view p).state != t.state) = false) : t.view p = t := by
  unfold TaskObject.view at h ⊢
  by_cases hc : (p.state != PromiseState.pending) = true ∧ (t.state != TaskState.fulfilled) = true
  · rw [if_pos hc] at h ⊢
    exfalso
    have h2 := hc.2
    simp [TaskObject.fulfill] at h
    simp [h] at h2
  · rw [if_neg hc]

def OnlyOn (id : Ident) : List Abstract.Effect → Prop
  | [] => True
  | .setPromise i _ :: fx => i = id ∧ OnlyOn id fx
  | .setTask i _ :: fx => i = id ∧ OnlyOn id fx
  | .setMessage _ _ :: fx => OnlyOn id fx
  | .setSchedule _ :: _ => False
  | .delSchedule _ :: _ => False

theorem OnlyOn_append {id : Ident} (a b : List Abstract.Effect) :
    OnlyOn id (a ++ b) ↔ OnlyOn id a ∧ OnlyOn id b := by
  induction a with
  | nil => simp [OnlyOn]
  | cons e es ih => cases e <;> simp [OnlyOn, ih, and_assoc]

theorem Fx_of_onlyOn {o : String} {id : Ident} {fx : List Abstract.Effect} (h : OnlyOn id fx)
    (hid : id.origin = o) : Fx o fx := by
  induction fx with
  | nil => trivial
  | cons e es ih =>
      cases e with
      | setPromise i _ => exact ⟨h.1 ▸ hid, ih h.2⟩
      | setTask i _ => exact ⟨h.1 ▸ hid, ih h.2⟩
      | setMessage _ _ => exact ih h
      | setSchedule _ => exact False.elim h
      | delSchedule _ => exact False.elim h

theorem find_applyAll_onlyOn {id id' : Ident} {fx : List Abstract.Effect} (h : OnlyOn id fx)
    (hne : id' ≠ id) (T : Abstract.State) :
    find (Abstract.applyAll T fx) id' = find T id' := by
  induction fx generalizing T with
  | nil => rfl
  | cons e es ih =>
      cases e with
      | setPromise i p =>
          simp only [Abstract.applyAll]
          rw [ih h.2, find_setPromise_other _ _ _ _ (h.1 ▸ hne)]
      | setTask i t =>
          simp only [Abstract.applyAll]
          rw [ih h.2, find_setTask, if_neg (h.1 ▸ hne)]
      | setMessage a m =>
          simp only [Abstract.applyAll]
          rw [ih h, find_setMessage]
      | setSchedule _ => exact False.elim h
      | delSchedule _ => exact False.elim h

theorem materialiseFx_onlyOn (id : Ident) (X Y : Object) : OnlyOn id (materialiseFx id X Y) := by
  unfold materialiseFx
  rw [OnlyOn_append]
  constructor
  · split <;> simp [OnlyOn]
  · split
    · split <;> simp [OnlyOn]
    · trivial

theorem sendsOf_materialise (id : Ident) (X Y : Object) : sendsOf (materialiseFx id X Y) = [] := by
  unfold materialiseFx
  rw [sendsOf_append]
  have h1 : sendsOf (if Y.promise.state != X.promise.state then [Abstract.Effect.setPromise id Y.promise] else []) = [] := by
    split <;> rfl
  rw [h1]
  split
  · split <;> rfl
  · rfl

theorem find_materialise_same {T : Abstract.State} {id : Ident} {X : Object} (h : find T id = some X)
    (now : Nat) :
    find (Abstract.applyAll T (materialiseFx id X (X.project now))) id = some (X.project now) := by
  obtain ⟨xi, xp, xt⟩ := X
  have hX : xi = id := find_id h
  subst hX
  simp only [Object.project, materialiseFx]
  by_cases hp : ((xp.project now).state != xp.state) = true
  · simp only [hp, ↓reduceIte]
    cases xt with
    | none =>
        simp only [Option.map_none, List.append_nil, Abstract.applyAll, find_setPromise_same, h,
          Abstract.Object.withPromise]
    | some t =>
        simp only [Option.map_some]
        by_cases hu : ((t.view (xp.project now)).state != t.state) = true
        · simp only [hu, ↓reduceIte, List.singleton_append, Abstract.applyAll, find_setTask,
            find_setPromise_same, h, Abstract.Object.withPromise, Option.map_some]
        · have hu' : ((t.view (xp.project now)).state != t.state) = false := by simpa using hu
          simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, Abstract.applyAll,
            find_setPromise_same, h, Abstract.Object.withPromise, view_eq_of_state hu', bne_self_eq_false]
  · have hp' : ((xp.project now).state != xp.state) = false := by simpa using hp
    have hpe := project_eq_of_state hp'
    simp only [hpe, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.nil_append]
    cases xt with
    | none => simp only [Option.map_none, Abstract.applyAll, h]
    | some t =>
        simp only [Option.map_some]
        by_cases hu : ((t.view xp).state != t.state) = true
        · simp only [hu, ↓reduceIte, Abstract.applyAll, find_setTask, h, Option.map_some]
        · have hu' : ((t.view xp).state != t.state) = false := by simpa using hu
          simp only [Bool.false_eq_true, ↓reduceIte, Abstract.applyAll, h, view_eq_of_state hu',
            bne_self_eq_false]

theorem find_applyAll_sends (T : Abstract.State) (ms : List (String × Message)) (id : Ident) :
    find (Abstract.applyAll T (ms.map fun (a, m) => Abstract.Effect.setMessage a m)) id = find T id := by
  induction ms generalizing T with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨a, m⟩ := x
      simp only [List.map_cons, Abstract.applyAll]
      rw [ih, find_setMessage]

theorem sendsOf_sends (ms : List (String × Message)) :
    sendsOf (ms.map fun (a, m) => Abstract.Effect.setMessage a m) = ms := by
  induction ms with
  | nil => rfl
  | cons x xs ih => obtain ⟨a, m⟩ := x; simp [sendsOf, ih]

theorem Fx_sends {o : String} (ms : List (String × Message)) :
    Fx o (ms.map fun (a, m) => Abstract.Effect.setMessage a m) := by
  induction ms with
  | nil => trivial
  | cons x xs ih => obtain ⟨a, m⟩ := x; exact ih

def execI (l : List Abstract.Trigger) (now : Nat) (T : Abstract.State) : Abstract.State :=
  (Abstract.exec false (l.map fun t => (.internal t, now)) T).2

theorem step_internal_eq (trg : Abstract.Trigger) (now : Nat) (T : Abstract.State) :
    Abstract.step false (.internal trg) now T =
      (.internal, Abstract.applyAll T (Abstract.handleInternal trg now (env T)).2) := by
  show Abstract.run false (Abstract.handle (.internal trg) now) T = _
  rw [run_eq]
  simp only [Abstract.handle, bind_apply, pure_apply, List.append_nil]

theorem exec_cons (mat : Bool) (ev : Abstract.Event) (n : Nat) (w : List (Abstract.Event × Nat))
    (S : Abstract.State) :
    Abstract.exec mat ((ev, n) :: w) S =
      ((Abstract.step mat ev n S).1 :: (Abstract.exec mat w (Abstract.step mat ev n S).2).1,
       (Abstract.exec mat w (Abstract.step mat ev n S).2).2) := rfl

theorem exec_append (mat : Bool) (a b : List (Abstract.Event × Nat)) (S : Abstract.State) :
    Abstract.exec mat (a ++ b) S =
      ((Abstract.exec mat a S).1 ++ (Abstract.exec mat b (Abstract.exec mat a S).2).1,
       (Abstract.exec mat b (Abstract.exec mat a S).2).2) := by
  induction a generalizing S with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨ev, n⟩ := x
      simp only [List.cons_append, exec_cons, ih, List.cons_append]

theorem execI_nil (now : Nat) (T : Abstract.State) : execI [] now T = T := rfl

theorem execI_cons (t : Abstract.Trigger) (l : List Abstract.Trigger) (now : Nat) (T : Abstract.State) :
    execI (t :: l) now T = execI l now (Abstract.applyAll T (Abstract.handleInternal t now (env T)).2) := by
  simp only [execI, List.map_cons, exec_cons, step_internal_eq]

theorem execI_append (a b : List Abstract.Trigger) (now : Nat) (T : Abstract.State) :
    execI (a ++ b) now T = execI b now (execI a now T) := by
  simp only [execI, List.map_append, exec_append]

theorem exec_internal_replies (l : List Abstract.Trigger) (now : Nat) (T : Abstract.State) :
    (Abstract.exec false (l.map fun t => (.internal t, now)) T).1 = l.map fun _ => .internal := by
  induction l generalizing T with
  | nil => rfl
  | cons t l ih => simp only [List.map_cons, exec_cons, step_internal_eq, ih]

structure SwInv (o : String) (S : Abstract.State) (c : Commands) (T : Abstract.State) : Prop where
  loc   : Local o c.put T
  out   : T.outbox = sendsFold S.outbox c.send
  sch   : T.schedules = S.schedules
  orig  : ∀ ob ∈ c.put.objects, ob.id.origin = o
  nodup : (c.put.objects.map (·.id)).Nodup
  wf    : WF c.put
  other : ∀ id, id.origin ≠ o → find T id = find S id

theorem SwInv.init {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (horig : ∀ ob ∈ org.objects, ob.id.origin = o) (hnodup : (org.objects.map (·.id)).Nodup)
    (hwf : WF org) : SwInv o S { put := org } S :=
  ⟨hL, rfl, rfl, horig, hnodup, hwf, fun _ _ => rfl⟩

theorem SwInv.step {o : String} {S : Abstract.State} {c : Commands} {T : Abstract.State}
    (h : SwInv o S c T) (fx : List Abstract.Effect) (hfx : Fx o fx) {c' : Commands}
    (hloc : Local o c'.put (Abstract.applyAll T fx)) (hsend : c'.send = c.send ++ sendsOf fx)
    (horig : ∀ ob ∈ c'.put.objects, ob.id.origin = o) (hnodup : (c'.put.objects.map (·.id)).Nodup)
    (hwf : WF c'.put) : SwInv o S c' (Abstract.applyAll T fx) :=
  ⟨hloc, by rw [applyAll_outbox, h.out, hsend, sendsFold_append],
   by rw [applyAll_schedules T fx hfx, h.sch], horig, hnodup, hwf,
   fun id hid => by rw [applyAll_find_other T fx hfx id hid, h.other id hid]⟩

theorem SwInv.merge {o : String} {S : Abstract.State} {c : Commands} {T : Abstract.State}
    {d : Commands} {U : Abstract.State} (h : SwInv o S c T) (hd : SwInv o T d U) :
    SwInv o S (c.merge d) U :=
  ⟨hd.loc, by rw [hd.out, h.out, ← sendsFold_append]; rfl, hd.sch.trans h.sch, hd.orig, hd.nodup, hd.wf,
   fun id hid => (hd.other id hid).trans (h.other id hid)⟩

theorem SwInv.sends {o : String} {S : Abstract.State} {c : Commands} {T : Abstract.State}
    (h : SwInv o S c T) (ms : List (String × Message)) {c' : Commands} (hput : c'.put = c.put)
    (hsend : c'.send = c.send ++ ms) :
    SwInv o S c' (Abstract.applyAll T (ms.map fun (a, m) => Abstract.Effect.setMessage a m)) := by
  refine h.step _ (Fx_sends ms) ?_ (by rw [hsend, sendsOf_sends]) (hput ▸ h.orig) (hput ▸ h.nodup)
    (hput ▸ h.wf)
  intro id hid
  rw [find_applyAll_sends, hput, h.loc id hid]

theorem SwInv.write_proj {o : String} {S : Abstract.State} {c : Commands} {T : Abstract.State}
    (h : SwInv o S c T) {w : Ident} (hw : w.origin = o) {X : Object} (hX : Origin.find c.put w = some X)
    (now : Nat) {c' : Commands} (hput : c'.put = c.put.write (X.project now)) (hsend : c'.send = c.send) :
    SwInv o S c' (Abstract.applyAll T (materialiseFx w X (X.project now))) := by
  have hXw : X.id = w := (find_mem hX).2
  have hmem : X ∈ c.put.objects := (find_mem hX).1
  have hT : find T w = some X := (h.loc w hw).trans hX
  have hx : (X.project now).id = w := hXw
  refine h.step (materialiseFx w X (X.project now)) (Fx_of_onlyOn (materialiseFx_onlyOn ..) hw) ?_
    (by rw [hsend, sendsOf_materialise, List.append_nil]) (hput ▸ write_derived h.orig (hXw ▸ hw))
    (hput ▸ write_nodup h.nodup) (hput ▸ WF_write h.wf hmem rfl (callbacks_sub X now) (listeners_sub X now))
  intro id hid
  rw [hput]
  by_cases e : id = w
  · subst e
    rw [find_write_at hx, find_materialise_same hT]
  · have hne : id ≠ (X.project now).id := fun e' => e (e'.trans hx)
    rw [find_write_other _ _ _ hne, find_applyAll_onlyOn (materialiseFx_onlyOn ..) e, h.loc id hid]

theorem SwInv.write_task {o : String} {S : Abstract.State} {c : Commands} {T : Abstract.State}
    (h : SwInv o S c T) {w : Ident} (hw : w.origin = o) {X : Object} (hX : Origin.find c.put w = some X)
    (now : Nat) (t : TaskObject) {c' : Commands}
    (hput : c'.put = c.put.write { X.project now with task := some t }) (hsend : c'.send = c.send) :
    SwInv o S c' (Abstract.applyAll T (materialiseFx w X (X.project now) ++ [.setTask w t])) := by
  have hXw : X.id = w := (find_mem hX).2
  have hmem : X ∈ c.put.objects := (find_mem hX).1
  have hT : find T w = some X := (h.loc w hw).trans hX
  have hx : ({ X.project now with task := some t } : Object).id = w := hXw
  refine h.step (materialiseFx w X (X.project now) ++ [.setTask w t])
    ((Fx_append o (materialiseFx w X (X.project now)) [.setTask w t]).2
      ⟨Fx_of_onlyOn (materialiseFx_onlyOn ..) hw, hw, trivial⟩) ?_
    (by simp [hsend, sendsOf_append, sendsOf_materialise, sendsOf]) (hput ▸ write_derived h.orig (hXw ▸ hw))
    (hput ▸ write_nodup h.nodup) (hput ▸ WF_write h.wf hmem rfl (callbacks_sub X now) (listeners_sub X now))
  intro id hid
  rw [hput, applyAll_append]
  by_cases e : id = w
  · subst e
    rw [find_write_at hx]
    simp only [Abstract.applyAll, find_setTask, if_true, find_materialise_same hT, Option.map_some]
  · have hne : id ≠ ({ X.project now with task := some t } : Object).id := fun e' => e (e'.trans hx)
    rw [find_write_other _ _ _ hne]
    simp only [Abstract.applyAll, find_setTask, if_neg e]
    rw [find_applyAll_onlyOn (materialiseFx_onlyOn ..) e, h.loc id hid]

theorem SwInv.write_promise {o : String} {S : Abstract.State} {c : Commands} {T : Abstract.State}
    (h : SwInv o S c T) {w : Ident} (hw : w.origin = o) {X : Object} (hX : Origin.find c.put w = some X)
    (now : Nat) (p : PromiseObject) (hcb : p.callbacks <+ X.promise.callbacks)
    (hls : p.listeners <+ X.promise.listeners) {c' : Commands}
    (hput : c'.put = c.put.write { X.project now with promise := p }) (hsend : c'.send = c.send) :
    SwInv o S c' (Abstract.applyAll T (materialiseFx w X (X.project now) ++ [.setPromise w p])) := by
  have hXw : X.id = w := (find_mem hX).2
  have hmem : X ∈ c.put.objects := (find_mem hX).1
  have hT : find T w = some X := (h.loc w hw).trans hX
  have hx : ({ X.project now with promise := p } : Object).id = w := hXw
  refine h.step (materialiseFx w X (X.project now) ++ [.setPromise w p])
    ((Fx_append o (materialiseFx w X (X.project now)) [.setPromise w p]).2
      ⟨Fx_of_onlyOn (materialiseFx_onlyOn ..) hw, hw, trivial⟩) ?_
    (by simp [hsend, sendsOf_append, sendsOf_materialise, sendsOf]) (hput ▸ write_derived h.orig (hXw ▸ hw))
    (hput ▸ write_nodup h.nodup) (hput ▸ WF_write h.wf hmem rfl hcb hls)
  intro id hid
  rw [hput, applyAll_append]
  by_cases e : id = w
  · subst e
    rw [find_write_at hx]
    simp only [Abstract.applyAll, find_setPromise_same, find_materialise_same hT, Abstract.Object.withPromise]
  · have hne : id ≠ ({ X.project now with promise := p } : Object).id := fun e' => e (e'.trans hx)
    rw [find_write_other _ _ _ hne]
    simp only [Abstract.applyAll]
    rw [find_setPromise_other _ _ _ _ e, find_applyAll_onlyOn (materialiseFx_onlyOn ..) e, h.loc id hid]

theorem SwInv.write_task_plain {o : String} {S : Abstract.State} {c : Commands} {T : Abstract.State}
    (h : SwInv o S c T) {w : Ident} (hw : w.origin = o) {X : Object} (hX : Origin.find c.put w = some X)
    (t : TaskObject) {c' : Commands} (hput : c'.put = c.put.write { X with task := some t })
    (hsend : c'.send = c.send) :
    SwInv o S c' (Abstract.applyAll T [.setTask w t]) := by
  have hXw : X.id = w := (find_mem hX).2
  have hmem : X ∈ c.put.objects := (find_mem hX).1
  have hT : find T w = some X := (h.loc w hw).trans hX
  have hx : ({ X with task := some t } : Object).id = w := hXw
  refine h.step [.setTask w t] ⟨hw, trivial⟩ ?_ (by simp [hsend, sendsOf])
    (hput ▸ write_derived h.orig (hXw ▸ hw))
    (hput ▸ write_nodup h.nodup) (hput ▸ WF_write h.wf hmem rfl (List.Sublist.refl _) (List.Sublist.refl _))
  intro id hid
  rw [hput]
  by_cases e : id = w
  · subst e
    rw [find_write_at hx]
    simp only [Abstract.applyAll, find_setTask, if_true, hT, Option.map_some]
  · have hne : id ≠ ({ X with task := some t } : Object).id := fun e' => e (e'.trans hx)
    rw [find_write_other _ _ _ hne]
    simp only [Abstract.applyAll, find_setTask, if_neg e]
    exact h.loc id hid

def ptStep (now : Nat) (c : Commands) (o : Object) : Commands :=
  if o.promise.state == .pending ∧ o.promise.timeoutAt ≤ now then
    { c with put := c.put.write (o.project now), del := c.del ++ o.timers }
  else
    c

def ptTrig (now : Nat) (o : Object) : Option Abstract.Trigger :=
  if o.promise.state == .pending ∧ o.promise.timeoutAt ≤ now then
    some (.promiseTimeout ⟨o.id⟩)
  else
    none

theorem promiseTimeouts_eq (now : Nat) (org : Origin) :
    Chain.promiseTimeouts now org = org.objects.foldl (ptStep now) { put := org } := rfl

theorem promiseTimeoutTriggers_eq (now : Nat) (org : Origin) :
    Chain.promiseTimeoutTriggers now org = org.objects.filterMap (ptTrig now) := rfl

theorem processPromiseTimeout_fx (id : Ident) (now : Nat) (T : Abstract.State) :
    (Abstract.handleInternal (.promiseTimeout ⟨id⟩) now (env T)).2 =
      match find T id with
      | none => []
      | some X => materialiseFx id X (X.project now) := by
  simp only [Abstract.handleInternal, Abstract.Internal.processPromiseTimeout, bind_apply, pure_apply,
    touchObject_apply]
  cases find T id <;> simp

theorem promiseTimeouts_sim {o : String} {S : Abstract.State} (now : Nat) :
    ∀ (l : List Object) (c : Commands) (T : Abstract.State), SwInv o S c T →
      (∀ ob ∈ l, Origin.find c.put ob.id = some ob) → (l.map (·.id)).Nodup →
      SwInv o S (l.foldl (ptStep now) c) (execI (l.filterMap (ptTrig now)) now T)
  | [], _, _, h, _, _ => h
  | ob :: l, c, T, h, hfind, hnd => by
      have hob : Origin.find c.put ob.id = some ob := hfind ob (List.mem_cons_self ..)
      have hido : ob.id.origin = o := h.orig ob (find_mem hob).1
      simp only [List.map_cons, List.nodup_cons] at hnd
      simp only [List.foldl_cons]
      by_cases hc : (ob.promise.state == PromiseState.pending) = true ∧ ob.promise.timeoutAt ≤ now
      · have hstep : ptStep now c ob = { c with put := c.put.write (ob.project now), del := c.del ++ ob.timers } := by
          unfold ptStep; rw [if_pos hc]
        have htrig : ptTrig now ob = some (.promiseTimeout ⟨ob.id⟩) := by
          unfold ptTrig; rw [if_pos hc]
        rw [hstep, List.filterMap_cons_some htrig, execI_cons, processPromiseTimeout_fx, h.loc ob.id hido, hob]
        refine promiseTimeouts_sim now l _ _ (h.write_proj hido hob now rfl rfl) ?_ hnd.2
        intro ob' hob'
        have hne : ob'.id ≠ (ob.project now).id := fun e => hnd.1 (e ▸ List.mem_map_of_mem hob')
        show Origin.find (c.put.write (ob.project now)) ob'.id = some ob'
        rw [find_write_other _ _ _ hne]
        exact hfind ob' (List.mem_cons_of_mem _ hob')
      · have hstep : ptStep now c ob = c := by
          unfold ptStep; rw [if_neg hc]
        have htrig : ptTrig now ob = none := by
          unfold ptTrig; rw [if_neg hc]
        rw [hstep, List.filterMap_cons_none htrig]
        exact promiseTimeouts_sim now l c T h (fun ob' h' => hfind ob' (List.mem_cons_of_mem _ h')) hnd.2


def lsStep (now : Nat) (id : Ident) (c : Commands) (address : String) : Commands :=
  match c.put.get id now with
  | some cur =>
      if cur.promise.state != .pending ∧ cur.promise.listeners.contains address then
        { c with
          put := c.put.write { cur with promise :=
            { cur.promise with listeners := cur.promise.listeners.filter (· != address) } },
          send := c.send ++ [(address, .unblock (cur.promise.toRecord cur.id))] }
      else
        { c with put := c.put.write cur }
  | none =>
      c

def lsOuter (now : Nat) (c : Commands) (o : Object) : Commands :=
  let o := o.project now
  if o.promise.state != .pending then
    o.promise.listeners.foldl (lsStep now o.id) c
  else
    c

def lsTrig (now : Nat) (o : Object) : List Abstract.Trigger :=
  let o := o.project now
  if o.promise.state != .pending ∧ !o.promise.listeners.isEmpty then
    o.promise.listeners.map fun a => .listener ⟨o.id, a⟩
  else
    []

theorem lsTrig_eq (now : Nat) (o : Object) :
    lsTrig now o =
      if (o.project now).promise.state != .pending then
        (o.project now).promise.listeners.map fun a => .listener ⟨(o.project now).id, a⟩
      else
        [] := by
  unfold lsTrig
  by_cases hc : ((o.project now).promise.state != PromiseState.pending) = true
  · cases hl : (o.project now).promise.listeners with
    | nil => simp [hc, hl]
    | cons a as => simp [hc, hl]
  · simp [hc]

def lsBulk (now : Nat) (c : Commands) (o : Object) : Commands :=
  let o := o.project now
  if o.promise.state != .pending ∧ !o.promise.listeners.isEmpty then
    { c with
      put := c.put.write { o with promise := { o.promise with listeners := [] } },
      send := c.send ++ o.promise.listeners.map fun a => (a, .unblock (o.promise.toRecord o.id)) }
  else
    c

theorem listeners_eq (now : Nat) (org : Origin) :
    Chain.listeners now org = org.objects.foldl (lsBulk now) { put := org } := rfl

theorem listenerTriggers_eq (now : Nat) (org : Origin) :
    Chain.listenerTriggers now org = org.objects.flatMap (lsTrig now) := rfl

theorem processListener_fx (id : Ident) (a : String) (now : Nat) (T : Abstract.State) :
    (Abstract.handleInternal (.listener ⟨id, a⟩) now (env T)).2 =
      match find T id with
      | none => []
      | some X =>
          if (X.project now).promise.state == .pending then
            materialiseFx id X (X.project now)
          else if (X.project now).promise.listeners.contains a then
            (materialiseFx id X (X.project now) ++
              [.setPromise (X.project now).id
                { (X.project now).promise with
                  listeners := (X.project now).promise.listeners.filter (· != a) }]) ++
              [(a, Message.unblock ((X.project now).promise.toRecord (X.project now).id))].map
                (fun (a, m) => Abstract.Effect.setMessage a m)
          else
            materialiseFx id X (X.project now) := by
  simp only [Abstract.handleInternal, Abstract.Internal.processListener, bind_apply, touchObject_apply]
  cases find T id with
  | none => rfl
  | some X =>
      simp only
      by_cases h1 : ((X.project now).promise.state == PromiseState.pending) = true
      · simp only [h1, ↓reduceIte, pure_apply, List.append_nil]
      · have h1' : ((X.project now).promise.state == PromiseState.pending) = false := by simpa using h1
        simp only [h1', Bool.false_eq_true, ↓reduceIte]
        by_cases h2 : (X.project now).promise.listeners.contains a = true
        · simp only [h2, ↓reduceIte, bind_apply, setPromise_apply, setMessage_apply, List.map_cons,
            List.map_nil, List.append_assoc, List.singleton_append]
        · have h2' : (X.project now).promise.listeners.contains a = false := by simpa using h2
          simp only [h2', Bool.false_eq_true, ↓reduceIte, pure_apply, List.append_nil]

theorem lsStep_sim {o : String} {S : Abstract.State} (now : Nat) (id : Ident) (hido : id.origin = o) :
    ∀ (as : List String) (c : Commands) (T : Abstract.State), SwInv o S c T →
      SwInv o S (as.foldl (lsStep now id) c) (execI (as.map fun a => .listener ⟨id, a⟩) now T)
  | [], _, _, h => h
  | a :: as, c, T, h => by
      simp only [List.foldl_cons, List.map_cons, execI_cons, processListener_fx, h.loc id hido]
      cases hX : Origin.find c.put id with
      | none =>
          have hg : c.put.get id now = none := by rw [get_eq, hX]; rfl
          have hstep : lsStep now id c a = c := by unfold lsStep; rw [hg]
          rw [hstep]
          exact lsStep_sim now id hido as c T h
      | some X =>
          have hg : c.put.get id now = some (X.project now) := by rw [get_eq, hX]; rfl
          have hXid : (X.project now).id = id := (find_mem hX).2
          simp only
          rw [hXid]
          by_cases h1 : ((X.project now).promise.state != PromiseState.pending) = true
              ∧ (X.project now).promise.listeners.contains a = true
          · have h1a : ((X.project now).promise.state == PromiseState.pending) = false := by
              simpa using h1.1
            have hstep : lsStep now id c a =
                { c with
                  put := c.put.write { X.project now with promise :=
                    { (X.project now).promise with
                      listeners := (X.project now).promise.listeners.filter (· != a) } },
                  send := c.send ++ [(a, .unblock ((X.project now).promise.toRecord id))] } := by
              unfold lsStep; rw [hg]; simp only [h1, and_self, ↓reduceIte, hXid]
            rw [hstep]
            simp only [h1a, Bool.false_eq_true, ↓reduceIte, h1.2]
            refine lsStep_sim now id hido as _ _ ?_
            rw [applyAll_append]
            exact (h.write_promise hido hX now
              { (X.project now).promise with
                listeners := (X.project now).promise.listeners.filter (· != a) } (callbacks_sub X now)
              (by show ((X.promise.project now).listeners.filter _) <+ X.promise.listeners
                  rw [project_listeners]; exact List.filter_sublist)
              (c' := { c with put := c.put.write { X.project now with promise :=
                    { (X.project now).promise with
                      listeners := (X.project now).promise.listeners.filter (· != a) } } }) rfl rfl).sends
              [(a, .unblock ((X.project now).promise.toRecord id))] rfl rfl
          · have hstep : lsStep now id c a = { c with put := c.put.write (X.project now) } := by
              unfold lsStep; rw [hg]; simp only [h1, ↓reduceIte]
            rw [hstep]
            have hpc : ∀ (M R : List Abstract.Effect),
                (if ((X.project now).promise.state == PromiseState.pending) = true then M
                 else if (X.project now).promise.listeners.contains a = true then R else M) = M := by
              intro M R
              by_cases hp : ((X.project now).promise.state == PromiseState.pending) = true
              · rw [if_pos hp]
              · have hp' : ((X.project now).promise.state != PromiseState.pending) = true := by simpa using hp
                have hc : (X.project now).promise.listeners.contains a = false := by
                  by_cases hcv : (X.project now).promise.listeners.contains a = true
                  · exact absurd ⟨hp', hcv⟩ h1
                  · simpa using hcv
                rw [if_neg hp, hc]
                simp
            rw [hpc]
            exact lsStep_sim now id hido as _ _ (h.write_proj hido hX now rfl rfl)

theorem lsOuter_step {o : String} {S : Abstract.State} (now : Nat) (c : Commands) (T : Abstract.State)
    (h : SwInv o S c T) (ob : Object) (hob : ob.id.origin = o) :
    SwInv o S (lsOuter now c ob) (execI (lsTrig now ob) now T) := by
  rw [lsTrig_eq]
  by_cases hc : ((ob.project now).promise.state != PromiseState.pending) = true
  · have hstep : lsOuter now c ob = (ob.project now).promise.listeners.foldl (lsStep now (ob.project now).id) c := by
      unfold lsOuter; simp only [hc, ↓reduceIte]
    rw [hstep, if_pos hc]
    exact lsStep_sim now (ob.project now).id hob _ c T h
  · have hstep : lsOuter now c ob = c := by
      unfold lsOuter; simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [hstep, if_neg hc, execI_nil]
    exact h

theorem PromiseObject.project_idem (p : PromiseObject) (n : Nat) : (p.project n).project n = p.project n := by
  unfold PromiseObject.project
  by_cases hc : (p.state == PromiseState.pending) = true ∧ p.timeoutAt ≤ n
  · rw [if_pos hc]
    split <;> simp
  · rw [if_neg hc, if_neg hc]

theorem view_idem (t : TaskObject) (p : PromiseObject) : (t.view p).view p = t.view p := by
  unfold TaskObject.view
  by_cases hc : (p.state != PromiseState.pending) = true ∧ (t.state != TaskState.fulfilled) = true
  · rw [if_pos hc]
    simp [TaskObject.fulfill]
  · rw [if_neg hc, if_neg hc]

theorem Object.project_idem (o : Object) (n : Nat) : (o.project n).project n = o.project n := by
  obtain ⟨id, p, t⟩ := o
  simp only [Object.project, PromiseObject.project_idem]
  cases t with
  | none => rfl
  | some t => simp [view_idem]

theorem PromiseObject.project_set_listeners (p : PromiseObject) (L : List String) (n : Nat) :
    ({ p with listeners := L } : PromiseObject).project n = { p.project n with listeners := L } := by
  unfold PromiseObject.project
  by_cases hc : p.state = PromiseState.pending ∧ p.timeoutAt ≤ n
  · by_cases hd : p.type = Protocol.OType.deadline
    · simp [hc, hd]
    · simp [hc, hd]
  · simp [hc]

theorem PromiseObject.project_set_callbacks (p : PromiseObject) (L : List Ident) (n : Nat) :
    ({ p with callbacks := L } : PromiseObject).project n = { p.project n with callbacks := L } := by
  unfold PromiseObject.project
  by_cases hc : p.state = PromiseState.pending ∧ p.timeoutAt ≤ n
  · by_cases hd : p.type = Protocol.OType.deadline
    · simp [hc, hd]
    · simp [hc, hd]
  · simp [hc]

theorem Object.project_set_listeners (o : Object) (L : List String) (n : Nat) :
    ({ o with promise := { o.promise with listeners := L } } : Object).project n =
      { o.project n with promise := { (o.project n).promise with listeners := L } } := by
  simp only [Object.project, PromiseObject.project_set_listeners]
  rfl

theorem filter_cons_ne_self {a : String} {l : List String} (h : a ∉ l) : (a :: l).filter (· != a) = l := by
  simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine List.filter_eq_self.2 fun b hb => ?_
  have hne : b ≠ a := fun e => h (e ▸ hb)
  simpa using hne

theorem Origin.eq_of_objects {a b : Origin} (h : a.objects = b.objects) : a = b := by
  cases a; cases b; cases h; rfl

theorem write_write {d : Origin} {x y : Object} (h : x.id = y.id) : (d.write x).write y = d.write y := by
  have hf : ∀ o : Object, (if (if o.id == x.id then x else o).id == y.id then y else
      (if o.id == x.id then x else o)) = if o.id == y.id then y else o := by
    intro o
    by_cases e : o.id = x.id
    · simp [e, h]
    · have e' : (o.id == x.id) = false := by simpa using e
      simp [e']
  by_cases hp : d.objects.any (·.id == x.id) = true
  · have hpy : (d.write x).objects.any (·.id == y.id) = true := by
      rw [write_present hp, List.any_map]
      refine (List.any_eq_true.2 ?_)
      obtain ⟨z, hz, hzx⟩ := List.any_eq_true.1 hp
      refine ⟨z, hz, ?_⟩
      simp [Function.comp, ← h, hzx]
    have hpy' : d.objects.any (·.id == y.id) = true := by rw [← h]; exact hp
    apply Origin.eq_of_objects
    rw [write_present hpy, write_present hp, write_present hpy', List.map_map]
    congr 1
    funext o
    exact hf o
  · have hp' := eq_false_of_ne_true hp
    have hpy' : d.objects.any (·.id == y.id) = false := by rw [← h]; exact hp'
    have hpx : (d.write x).objects.any (·.id == y.id) = true := by
      rw [write_absent hp', List.any_append]
      simp [h]
    apply Origin.eq_of_objects
    rw [write_present hpx, write_absent hp', write_absent hpy', List.map_append, List.map_singleton]
    congr 1
    · conv => rhs; rw [← List.map_id d.objects]
      apply List.map_congr_left
      intro o ho
      have : (o.id == y.id) = false := by
        have := List.any_eq_false.1 hpy' o ho
        simpa using this
      simp [this]
    · simp [h]

theorem lsFold_eq (now : Nat) (o : Object) (hst : o.project now = o)
    (hnp : (o.promise.state != PromiseState.pending) = true) :
    ∀ (a : String) (as : List String) (c : Commands), (a :: as).Nodup →
      c.put.get o.id now = some { o with promise := { o.promise with listeners := a :: as } } →
      (a :: as).foldl (lsStep now o.id) c =
        { c with put := c.put.write { o with promise := { o.promise with listeners := [] } },
                 send := c.send ++ (a :: as).map fun b => (b, .unblock (o.promise.toRecord o.id)) }
  | a, [], c, _, hg => by
      simp only [List.foldl_cons, List.foldl_nil, lsStep, hg]
      have h1 : (({ o with promise := { o.promise with listeners := [a] } } : Object).promise.state
          != PromiseState.pending) = true := hnp
      have h2 : ({ o with promise := { o.promise with listeners := [a] } } : Object).promise.listeners.contains a
          = true := by simp
      simp only [h1, h2, and_self, ↓reduceIte]
      simp [toRecord_set_listeners]
  | a, b :: as, c, hnd, hg => by
      have hnd' := List.nodup_cons.1 hnd
      rw [List.foldl_cons]
      have hstep : lsStep now o.id c a =
          { c with put := c.put.write { o with promise := { o.promise with listeners := b :: as } },
                   send := c.send ++ [(a, .unblock (o.promise.toRecord o.id))] } := by
        unfold lsStep
        rw [hg]
        have h1 : (({ o with promise := { o.promise with listeners := a :: b :: as } } : Object).promise.state
            != PromiseState.pending) = true := hnp
        have h2 : ({ o with promise := { o.promise with listeners := a :: b :: as } } : Object).promise.listeners.contains a
            = true := by simp
        simp only [h1, h2, and_self, ↓reduceIte]
        simp [filter_cons_ne_self hnd'.1, toRecord_set_listeners]
      rw [hstep]
      have hg' : ({ c with put := c.put.write { o with promise := { o.promise with listeners := b :: as } },
                            send := c.send ++ [(a, .unblock (o.promise.toRecord o.id))] } : Commands).put.get o.id now =
          some { o with promise := { o.promise with listeners := b :: as } } := by
        show (c.put.write _).get o.id now = _
        rw [get_eq, find_write_at rfl, Option.map_some, Object.project_set_listeners, hst]
      rw [lsFold_eq now o hst hnp b as _ hnd'.2 hg']
      have hw := write_write (d := c.put) (x := { o with promise := { o.promise with listeners := b :: as } })
        (y := { o with promise := { o.promise with listeners := [] } }) rfl
      simp only [List.map_cons, List.append_assoc, List.singleton_append]
      rw [hw]

theorem lsBulk_eq {c : Commands} {ob : Object} (now : Nat) (hob : Origin.find c.put ob.id = some ob)
    (hnd : ob.promise.listeners.Nodup) : lsBulk now c ob = lsOuter now c ob := by
  unfold lsBulk lsOuter
  by_cases hc : ((ob.project now).promise.state != PromiseState.pending) = true
  · cases hl : (ob.project now).promise.listeners with
    | nil => simp [hc, hl]
    | cons a as =>
        have hnd' : (a :: as).Nodup := by
          rw [← hl]
          show (ob.promise.project now).listeners.Nodup
          rw [project_listeners]; exact hnd
        have hg : c.put.get ob.id now =
            some { ob.project now with promise := { (ob.project now).promise with listeners := a :: as } } := by
          rw [get_eq, hob, Option.map_some, ← hl]
        simp only [hc, hl, List.isEmpty_cons, Bool.not_false, and_self, ↓reduceIte]
        rw [lsFold_eq now (ob.project now) (Object.project_idem ob now) hc a as c hnd' hg]
  · simp [hc]

theorem lsBulk_find_other {c : Commands} {ob : Object} (now : Nat) {id : Ident} (hne : id ≠ ob.id) :
    Origin.find (lsBulk now c ob).put id = Origin.find c.put id := by
  simp only [lsBulk]
  split
  · exact find_write_other _ _ _ hne
  · rfl

theorem lsBulk_sim {o : String} {S : Abstract.State} (now : Nat) :
    ∀ (l : List Object) (c : Commands) (T : Abstract.State), SwInv o S c T →
      (∀ ob ∈ l, Origin.find c.put ob.id = some ob) → (l.map (·.id)).Nodup →
      SwInv o S (l.foldl (lsBulk now) c) (execI (l.flatMap (lsTrig now)) now T)
  | [], _, _, h, _, _ => h
  | ob :: l, c, T, h, hfind, hnd => by
      have hob : Origin.find c.put ob.id = some ob := hfind ob (List.mem_cons_self ..)
      have hido : ob.id.origin = o := h.orig ob (find_mem hob).1
      simp only [List.map_cons, List.nodup_cons] at hnd
      simp only [List.foldl_cons, List.flatMap_cons, execI_append]
      have hstep := lsOuter_step now c T h ob hido
      rw [← lsBulk_eq now hob (h.wf ob (find_mem hob).1).1] at hstep
      refine lsBulk_sim now l _ _ hstep ?_ hnd.2
      intro ob' hob'
      have hne : ob'.id ≠ ob.id := fun e => hnd.1 (e ▸ List.mem_map_of_mem hob')
      rw [lsBulk_find_other now hne]
      exact hfind ob' (List.mem_cons_of_mem _ hob')

def cbStep (now : Nat) (id : Ident) (c : Commands) (awaiter : Ident) : Commands :=
  match c.put.get id now with
  | some cur =>
      if cur.promise.state != .pending ∧ cur.promise.callbacks.contains awaiter then
        Chain.resume now id
          { c with put := c.put.write { cur with promise :=
              { cur.promise with callbacks := cur.promise.callbacks.filter (· != awaiter) } } }
          awaiter
      else
        { c with put := c.put.write cur }
  | none =>
      c

def cbOuter (now : Nat) (c : Commands) (o : Object) : Commands :=
  let o := o.project now
  if o.promise.state != .pending then
    o.promise.callbacks.foldl (cbStep now o.id) c
  else
    c

def cbTrig (now : Nat) (o : Object) : List Abstract.Trigger :=
  let o := o.project now
  if o.promise.state != .pending then
    o.promise.callbacks.map fun w => .callback ⟨o.id, w⟩
  else
    []

def cbStepOld (now : Nat) (id : Ident) (c : Commands) (awaiter : Ident) : Commands :=
  match c.put.get id now with
  | some cur =>
      Chain.resume now id
        { c with put := c.put.write { cur with promise :=
            { cur.promise with callbacks := cur.promise.callbacks.filter (· != awaiter) } } }
        awaiter
  | none =>
      c

def cbOuterOld (now : Nat) (c : Commands) (o : Object) : Commands :=
  let o := o.project now
  if o.promise.state != .pending then
    o.promise.callbacks.foldl (cbStepOld now o.id) c
  else
    c

theorem callbacks_eq (now : Nat) (org : Origin) :
    Chain.callbacks now org = org.objects.foldl (cbOuterOld now) { put := org } := rfl

theorem callbackTriggers_eq (now : Nat) (org : Origin) :
    Chain.callbackTriggers now org = org.objects.flatMap (cbTrig now) := rfl

def resumeFx (awaited w : Ident) (now : Nat) (T : Abstract.State) : List Abstract.Effect :=
  match find T w with
  | none => []
  | some Y =>
      if Y.task.isSome then
        materialiseFx w Y (Y.project now) ++
          (match (Y.project now).task with
           | none => []
           | some t =>
               match t.state with
               | .suspended =>
                   [.setTask (Y.project now).id
                     { t with state := .pending, resumes := [awaited], retryTimeoutAt := some now }]
               | .pending | .acquired | .halted =>
                   if !(t.resumes.contains awaited) then
                     [.setTask (Y.project now).id { t with resumes := t.resumes ++ [awaited] }]
                   else
                     []
               | .fulfilled => [])
      else
        []

theorem resumeFx_congr {awaited w : Ident} {now : Nat} {T T' : Abstract.State} (h : find T w = find T' w) :
    resumeFx awaited w now T = resumeFx awaited w now T' := by
  unfold resumeFx; rw [h]

theorem resumeOne_fx (awaited w : Ident) (now : Nat) (T : Abstract.State) :
    (Abstract.Internal.resumeOne awaited w now (env T)).2 = resumeFx awaited w now T := by
  unfold Abstract.Internal.resumeOne resumeFx
  simp only [bind_apply, touchTaskObject_apply]
  cases find T w with
  | none => rfl
  | some Y =>
      simp only
      by_cases ht : Y.task.isSome = true
      · simp only [ht, ↓reduceIte]
        cases (Y.project now).task with
        | none => simp [pure_apply]
        | some t =>
            simp only
            cases t.state
            all_goals (by_cases hc : awaited ∈ t.resumes <;> simp [hc, pure_apply, setTask_apply])
      · simp [ht, pure_apply]

theorem processCallback_fx (id w : Ident) (now : Nat) (T : Abstract.State) :
    (Abstract.handleInternal (.callback ⟨id, w⟩) now (env T)).2 =
      match find T id with
      | none => []
      | some X =>
          if (X.project now).promise.state == .pending then
            materialiseFx id X (X.project now)
          else if (X.project now).promise.callbacks.contains w then
            (materialiseFx id X (X.project now) ++
              [.setPromise (X.project now).id
                { (X.project now).promise with
                  callbacks := (X.project now).promise.callbacks.filter (· != w) }]) ++
              resumeFx (X.project now).id w now T
          else
            materialiseFx id X (X.project now) := by
  simp only [Abstract.handleInternal, Abstract.Internal.processCallback, bind_apply, touchObject_apply]
  cases find T id with
  | none => rfl
  | some X =>
      simp only
      by_cases h1 : ((X.project now).promise.state == PromiseState.pending) = true
      · simp only [h1, ↓reduceIte, pure_apply, List.append_nil]
      · have h1' : ((X.project now).promise.state == PromiseState.pending) = false := by simpa using h1
        simp only [h1', Bool.false_eq_true, ↓reduceIte]
        by_cases h2 : (X.project now).promise.callbacks.contains w = true
        · simp only [h2, ↓reduceIte, bind_apply, setPromise_apply, resumeOne_fx, List.append_assoc,
            List.singleton_append]
        · have h2' : (X.project now).promise.callbacks.contains w = false := by simpa using h2
          simp only [h2', Bool.false_eq_true, ↓reduceIte, pure_apply, List.append_nil]

theorem resume_sim {o : String} {S : Abstract.State} (now : Nat) (awaited w : Ident) (hw : w.origin = o)
    (c : Commands) (T : Abstract.State) (h : SwInv o S c T) :
    SwInv o S (Chain.resume now awaited c w) (Abstract.applyAll T (resumeFx awaited w now T)) := by
  unfold Chain.resume resumeFx
  rw [h.loc w hw]
  cases hY : Origin.find c.put w with
  | none =>
      have hg : c.put.get w now = none := by rw [get_eq, hY]; rfl
      simp only [hg, Option.bind_none, Abstract.applyAll]
      exact h
  | some Y =>
      have hg : c.put.get w now = some (Y.project now) := by rw [get_eq, hY]; rfl
      have hYid : (Y.project now).id = w := (find_mem hY).2
      simp only [hg, Option.bind_some, hYid]
      cases ht : Y.task with
      | none =>
          have htp : (Y.project now).task = none := by rw [project_task, ht]; rfl
          simp only [htp, Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            Abstract.applyAll]
          exact h
      | some t =>
          obtain ⟨tv, htv⟩ : ∃ tv, (Y.project now).task = some tv :=
            ⟨t.view (Y.promise.project now), by rw [project_task, ht]; rfl⟩
          simp only [htv, Option.map_some, Option.isSome_some, ↓reduceIte]
          cases hs : tv.state
          case suspended =>
            simp only
            exact h.write_task hw hY now _ rfl rfl
          case fulfilled =>
            simp only [List.append_nil]
            exact h.write_proj hw hY now rfl rfl
          all_goals
            simp only
            by_cases hc : tv.resumes.contains awaited = true
            · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_nil]
              exact h.write_proj hw hY now rfl rfl
            · have hc' : tv.resumes.contains awaited = false := by simpa using hc
              simp only [hc', Bool.not_false, ↓reduceIte]
              exact h.write_task hw hY now _ rfl rfl

theorem cbStep_sim {o : String} {S : Abstract.State} (now : Nat) (id : Ident) (hido : id.origin = o) :
    ∀ (ws : List Ident) (c : Commands) (T : Abstract.State), SwInv o S c T →
      SwInv o S (ws.foldl (cbStep now id) c) (execI (ws.map fun w => .callback ⟨id, w⟩) now T)
  | [], _, _, h => h
  | w :: ws, c, T, h => by
      simp only [List.foldl_cons, List.map_cons, execI_cons, processCallback_fx, h.loc id hido]
      cases hX : Origin.find c.put id with
      | none =>
          have hg : c.put.get id now = none := by rw [get_eq, hX]; rfl
          have hstep : cbStep now id c w = c := by unfold cbStep; rw [hg]
          rw [hstep]
          exact cbStep_sim now id hido ws c T h
      | some X =>
          have hg : c.put.get id now = some (X.project now) := by rw [get_eq, hX]; rfl
          have hXid : (X.project now).id = id := (find_mem hX).2
          have hmem : X ∈ c.put.objects := (find_mem hX).1
          simp only
          rw [hXid]
          by_cases h1 : ((X.project now).promise.state != PromiseState.pending) = true
              ∧ (X.project now).promise.callbacks.contains w = true
          · have h1a : ((X.project now).promise.state == PromiseState.pending) = false := by
              simpa using h1.1
            have hwmem : w ∈ X.promise.callbacks := by
              have := List.contains_iff_mem.1 h1.2
              have this' : w ∈ (X.promise.project now).callbacks := this
              rwa [project_callbacks] at this'
            obtain ⟨hne, hwo⟩ := (h.wf X hmem).2.2 w hwmem
            have hne' : w ≠ id := fun e => hne (e.trans hXid.symm)
            have hwo' : w.origin = o := hwo.trans (hXid ▸ hido)
            have hstep : cbStep now id c w =
                Chain.resume now id
                  { c with put := c.put.write { X.project now with promise :=
                      { (X.project now).promise with
                        callbacks := (X.project now).promise.callbacks.filter (· != w) } } }
                  w := by
              unfold cbStep; rw [hg]; simp only [h1, and_self, ↓reduceIte]
            rw [hstep]
            simp only [h1a, Bool.false_eq_true, ↓reduceIte, h1.2]
            refine cbStep_sim now id hido ws _ _ ?_
            rw [applyAll_append]
            have h2 := h.write_promise hido hX now
              { (X.project now).promise with
                callbacks := (X.project now).promise.callbacks.filter (· != w) }
              (by show ((X.promise.project now).callbacks.filter _) <+ X.promise.callbacks
                  rw [project_callbacks]; exact List.filter_sublist) (listeners_sub X now)
              (c' := { c with put := c.put.write { X.project now with promise :=
                      { (X.project now).promise with
                        callbacks := (X.project now).promise.callbacks.filter (· != w) } } }) rfl rfl
            have hfind : find T w = find (Abstract.applyAll T
                (materialiseFx id X (X.project now) ++
                  [.setPromise id { (X.project now).promise with
                    callbacks := (X.project now).promise.callbacks.filter (· != w) }])) w := by
              rw [applyAll_append]
              simp only [Abstract.applyAll]
              rw [find_setPromise_other _ _ _ _ hne', find_applyAll_onlyOn (materialiseFx_onlyOn ..) hne']
            rw [resumeFx_congr hfind]
            exact resume_sim now id w hwo' _ _ h2
          · have hstep : cbStep now id c w = { c with put := c.put.write (X.project now) } := by
              unfold cbStep; rw [hg]; simp only [h1, ↓reduceIte]
            rw [hstep]
            have hpc : ∀ (M R : List Abstract.Effect),
                (if ((X.project now).promise.state == PromiseState.pending) = true then M
                 else if (X.project now).promise.callbacks.contains w = true then R else M) = M := by
              intro M R
              by_cases hp : ((X.project now).promise.state == PromiseState.pending) = true
              · rw [if_pos hp]
              · have hp' : ((X.project now).promise.state != PromiseState.pending) = true := by simpa using hp
                have hc : (X.project now).promise.callbacks.contains w = false := by
                  by_cases hcv : (X.project now).promise.callbacks.contains w = true
                  · exact absurd ⟨hp', hcv⟩ h1
                  · simpa using hcv
                rw [if_neg hp, hc]
                simp
            rw [hpc]
            exact cbStep_sim now id hido ws _ _ (h.write_proj hido hX now rfl rfl)

theorem cbOuter_step {o : String} {S : Abstract.State} (now : Nat) (c : Commands) (T : Abstract.State)
    (h : SwInv o S c T) (ob : Object) (hob : ob.id.origin = o) :
    SwInv o S (cbOuter now c ob) (execI (cbTrig now ob) now T) := by
  by_cases hc : ((ob.project now).promise.state != PromiseState.pending) = true
  · have hstep : cbOuter now c ob =
        (ob.project now).promise.callbacks.foldl (cbStep now (ob.project now).id) c := by
      unfold cbOuter; simp only [hc, ↓reduceIte]
    have htrig : cbTrig now ob =
        (ob.project now).promise.callbacks.map fun w => .callback ⟨(ob.project now).id, w⟩ := by
      unfold cbTrig; simp only [hc, ↓reduceIte]
    rw [hstep, htrig]
    exact cbStep_sim now (ob.project now).id hob _ c T h
  · have hstep : cbOuter now c ob = c := by
      unfold cbOuter; simp only [hc, Bool.false_eq_true, ↓reduceIte]
    have htrig : cbTrig now ob = [] := by
      unfold cbTrig; simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [hstep, htrig, execI_nil]
    exact h

theorem get_id {org : Origin} {id : Ident} {now : Nat} {o : Object} (hf : org.get id now = some o) :
    o.id = id := by
  obtain ⟨ob, hfind, rfl⟩ := get_some hf
  exact (find_mem hfind).2

theorem resume_find_other (now : Nat) (awaited : Ident) (c : Commands) (w id : Ident) (h : id ≠ w) :
    Origin.find (Chain.resume now awaited c w).put id = Origin.find c.put id := by
  unfold Chain.resume
  cases hg : c.put.get w now with
  | none => rfl
  | some Y =>
      have hY : Y.id = w := get_id hg
      simp only [Option.bind_some]
      cases Y.task with
      | none => rfl
      | some t =>
          simp only [Option.map_some]
          cases t.state
          all_goals
            (by_cases hr : t.resumes.contains awaited = true <;>
              (try simp only [hr, Bool.false_eq_true, ↓reduceIte]) <;>
              first
                | rfl
                | exact find_write_other _ _ _ (fun e => h (e.trans hY)))

theorem resume_proj (now : Nat) (awaited : Ident) (c : Commands) (w id : Ident) :
    (Origin.find (Chain.resume now awaited c w).put id).map (fun cur => cur.promise.project now) =
      (Origin.find c.put id).map (fun cur => cur.promise.project now) := by
  by_cases h : id = w
  · subst h
    unfold Chain.resume
    cases hg : c.put.get id now with
    | none => rfl
    | some Y =>
        obtain ⟨X, hX, rfl⟩ := get_some hg
        have hXid : X.id = id := (find_mem hX).2
        simp only [Option.bind_some]
        cases (X.project now).task with
        | none => rfl
        | some t =>
            simp only [Option.map_some]
            have key : ∀ x : Object, x.id = id → x.promise = (X.project now).promise →
                (Origin.find (c.put.write x) id).map (fun cur => cur.promise.project now) =
                  (Origin.find c.put id).map (fun cur => cur.promise.project now) := by
              intro x hx hp
              rw [find_write_at hx, hX, Option.map_some, Option.map_some, hp, project_promise,
                PromiseObject.project_idem]
            cases t.state
            all_goals
              (by_cases hr : t.resumes.contains awaited = true <;>
                (try simp only [hr, Bool.false_eq_true, ↓reduceIte]) <;>
                first
                  | rfl
                  | exact key _ hXid rfl)
  · rw [resume_find_other now awaited c w id h]

theorem cbStep_proj {c : Commands} {id : Ident} {w : Ident} (now : Nat) {id' : Ident} (hne : id' ≠ id) :
    (Origin.find (cbStep now id c w).put id').map (fun cur => cur.promise.project now) =
      (Origin.find c.put id').map (fun cur => cur.promise.project now) := by
  unfold cbStep
  cases hg : c.put.get id now with
  | none => rfl
  | some cur =>
      have hc : cur.id = id := get_id hg
      simp only
      have hne' : id' ≠ ({ cur with promise := { cur.promise with callbacks := cur.promise.callbacks.filter (· != w) } } : Object).id :=
        fun e => hne (e.trans hc)
      split
      · rw [resume_proj, find_write_other _ _ _ hne']
      · rw [find_write_other _ _ _ (fun e => hne (e.trans hc))]

theorem cbFold_proj (now : Nat) (id : Ident) : ∀ (ws : List Ident) (c : Commands) {id' : Ident}, id' ≠ id →
    (Origin.find (ws.foldl (cbStep now id) c).put id').map (fun cur => cur.promise.project now) =
      (Origin.find c.put id').map (fun cur => cur.promise.project now)
  | [], _, _, _ => rfl
  | w :: ws, c, id', hne => by
      rw [List.foldl_cons, cbFold_proj now id ws _ hne, cbStep_proj now hne]

theorem cbOuter_proj {c : Commands} {ob : Object} (now : Nat) {id : Ident} (hne : id ≠ ob.id) :
    (Origin.find (cbOuter now c ob).put id).map (fun cur => cur.promise.project now) =
      (Origin.find c.put id).map (fun cur => cur.promise.project now) := by
  simp only [cbOuter]
  split
  · exact cbFold_proj now _ _ c hne
  · rfl

theorem cbFold_eq (now : Nat) (id : Ident) (p : PromiseObject) (hp : p.project now = p)
    (hnp : (p.state != PromiseState.pending) = true) :
    ∀ (ws : List Ident) (c : Commands), ws.Nodup → (∀ w ∈ ws, w ≠ id) →
      (Origin.find c.put id).map (fun cur => cur.promise.project now) = some { p with callbacks := ws } →
      ws.foldl (cbStepOld now id) c = ws.foldl (cbStep now id) c
  | [], _, _, _, _ => rfl
  | w :: ws, c, hnd, hne, hcur => by
      have hnd' := List.nodup_cons.1 hnd
      cases hf : Origin.find c.put id with
      | none => rw [hf] at hcur; cases hcur
      | some X =>
          rw [hf, Option.map_some, Option.some.injEq] at hcur
          have hg : c.put.get id now = some (X.project now) := by rw [get_eq, hf]; rfl
          have hcurp : (X.project now).promise = { p with callbacks := w :: ws } := hcur
          have hXid : X.id = id := (find_mem hf).2
          have hguard : ((X.project now).promise.state != PromiseState.pending) = true
              ∧ (X.project now).promise.callbacks.contains w = true := by
            rw [hcurp]; exact ⟨hnp, by simp⟩
          rw [List.foldl_cons, List.foldl_cons]
          have hstep : cbStepOld now id c w = cbStep now id c w := by
            unfold cbStepOld cbStep; rw [hg]; simp only [hguard, and_self, ↓reduceIte]
          rw [hstep]
          apply cbFold_eq now id p hp hnp ws _ hnd'.2 (fun v hv => hne v (List.mem_cons_of_mem _ hv))
          unfold cbStep
          rw [hg]
          simp only [hguard, and_self, ↓reduceIte]
          rw [resume_find_other _ _ _ _ _ (hne w (List.mem_cons_self ..)).symm]
          have hx : ({ X.project now with promise := { (X.project now).promise with
              callbacks := (X.project now).promise.callbacks.filter (· != w) } } : Object).id = id := hXid
          rw [find_write_at hx, Option.map_some]
          refine congrArg some ?_
          show ({ (X.project now).promise with
              callbacks := (X.project now).promise.callbacks.filter (· != w) } : PromiseObject).project now = _
          rw [hcurp]
          have hfl : (({ p with callbacks := w :: ws } : PromiseObject).callbacks.filter (· != w)) = ws := by
            show (w :: ws).filter (· != w) = ws
            simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
            refine List.filter_eq_self.2 fun b hb => ?_
            have hne : b ≠ w := fun e => hnd'.1 (e ▸ hb)
            simpa using hne
          rw [hfl]
          show ({ p with callbacks := ws } : PromiseObject).project now = _
          rw [PromiseObject.project_set_callbacks, hp]

theorem cbOuterOld_eq (now : Nat) (c : Commands) (ob : Object)
    (hcur : (Origin.find c.put ob.id).map (fun cur => cur.promise.project now) = some (ob.promise.project now))
    (hnd : ob.promise.callbacks.Nodup) (hne : ∀ w ∈ ob.promise.callbacks, w ≠ ob.id) :
    cbOuterOld now c ob = cbOuter now c ob := by
  unfold cbOuterOld cbOuter
  by_cases hc : ((ob.project now).promise.state != PromiseState.pending) = true
  · simp only [hc, ↓reduceIte]
    apply cbFold_eq now (ob.project now).id (ob.promise.project now) (PromiseObject.project_idem _ _) hc
    · show (ob.promise.project now).callbacks.Nodup
      rw [project_callbacks]; exact hnd
    · intro w hw
      have hw' : w ∈ (ob.promise.project now).callbacks := hw
      rw [project_callbacks] at hw'
      exact hne w hw'
    · exact hcur
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]

theorem cbOld_sim {o : String} {S : Abstract.State} {org : Origin} (hwf : WF org) (now : Nat) :
    ∀ (l : List Object) (c : Commands) (T : Abstract.State), SwInv o S c T →
      (∀ ob ∈ l, ob ∈ org.objects) → (l.map (·.id)).Nodup →
      (∀ ob ∈ l, (Origin.find c.put ob.id).map (fun cur => cur.promise.project now) =
        some (ob.promise.project now)) →
      SwInv o S (l.foldl (cbOuterOld now) c) (execI (l.flatMap (cbTrig now)) now T)
  | [], _, _, h, _, _, _ => h
  | ob :: l, c, T, h, hmem, hnd, hcur => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      simp only [List.foldl_cons, List.flatMap_cons, execI_append]
      have hob := hmem ob (List.mem_cons_self ..)
      obtain ⟨_, hcbnd, hwfo⟩ := hwf ob hob
      have hcur0 := hcur ob (List.mem_cons_self ..)
      have hido : ob.id.origin = o := by
        cases hf : Origin.find c.put ob.id with
        | none => rw [hf] at hcur0; cases hcur0
        | some cur =>
            have := h.orig cur (find_mem hf).1
            rw [(find_mem hf).2] at this
            exact this
      rw [cbOuterOld_eq now c ob hcur0 hcbnd (fun w hw => (hwfo w hw).1)]
      refine cbOld_sim hwf now l _ _ (cbOuter_step now c T h ob hido)
        (fun x hx => hmem x (List.mem_cons_of_mem _ hx)) hnd.2 ?_
      intro ob' hob'
      have hne : ob'.id ≠ ob.id := fun e => hnd.1 (e ▸ List.mem_map_of_mem hob')
      rw [cbOuter_proj now hne]
      exact hcur ob' (List.mem_cons_of_mem _ hob')

def ltStep (now : Nat) (c : Commands) (o : Object) : Commands :=
  let o := o.project now
  match o.task with
  | some t =>
      if t.state == .acquired ∧ t.leaseTimeoutAt.any (· ≤ now)
          ∧ o.promise.state == .pending then
        { c with
          arm := c.arm ++ [⟨now, o.id, .retry⟩],
          put := c.put.write { o with task := some { t with state := .pending, pid := none, ttl := none,
                                                            leaseTimeoutAt := none,
                                                            retryTimeoutAt := some now } },
          del := c.del ++ t.timers o.id }
      else
        c
  | none =>
      c

def ltTrig (now : Nat) (o : Object) : Option Abstract.Trigger :=
  let o := o.project now
  match o.task with
  | some t =>
      if t.state == .acquired ∧ t.leaseTimeoutAt.any (· ≤ now) ∧ o.promise.state == .pending then
        some (.taskLeaseTimeout ⟨o.id⟩)
      else
        none
  | none =>
      none

theorem leaseTimeouts_eq (now : Nat) (org : Origin) :
    Chain.leaseTimeouts now org = org.objects.foldl (ltStep now) { put := org } := rfl

theorem leaseTimeoutTriggers_eq (now : Nat) (org : Origin) :
    Chain.leaseTimeoutTriggers now org = org.objects.filterMap (ltTrig now) := rfl

theorem processLeaseTimeout_fx (id : Ident) (now : Nat) (T : Abstract.State) :
    (Abstract.handleInternal (.taskLeaseTimeout ⟨id⟩) now (env T)).2 =
      match (find T id).bind fun X => if X.task.isSome then some (X.project now) else none with
      | none => []
      | some o =>
          match o.task with
          | none => []
          | some t =>
              match t.leaseTimeoutAt with
              | none => []
              | some deadline =>
                  if t.state == .acquired ∧ deadline ≤ now then
                    if o.promise.state == .pending then
                      [.setTask o.id { t with state := .pending, pid := none, ttl := none,
                                              leaseTimeoutAt := none, retryTimeoutAt := some now }]
                    else
                      []
                  else
                    [] := by
  simp only [Abstract.handleInternal, Abstract.Internal.processLeaseTimeout, bind_apply,
    viewTaskObject_apply]
  cases (find T id).bind fun X => if X.task.isSome then some (X.project now) else none with
  | none => rfl
  | some ob =>
      simp only
      cases ob.task with
      | none => rfl
      | some t =>
          simp only
          cases t.leaseTimeoutAt with
          | none => rfl
          | some dl =>
              simp only
              by_cases h1 : (t.state == TaskState.acquired) = true ∧ dl ≤ now
              · simp only [h1, and_self, ↓reduceIte]
                by_cases h2 : (ob.promise.state == PromiseState.pending) = true
                · simp only [h2, ↓reduceIte, setTask_apply, List.nil_append]
                · simp only [h2, Bool.false_eq_true, ↓reduceIte, pure_apply, List.nil_append]
              · simp only [h1, ↓reduceIte, pure_apply, List.nil_append]

theorem leaseTimeouts_sim {o : String} {S : Abstract.State} (now : Nat) :
    ∀ (l : List Object) (c : Commands) (T : Abstract.State), SwInv o S c T →
      (∀ ob ∈ l, Origin.find c.put ob.id = some ob) → (l.map (·.id)).Nodup →
      SwInv o S (l.foldl (ltStep now) c) (execI (l.filterMap (ltTrig now)) now T)
  | [], _, _, h, _, _ => h
  | ob :: l, c, T, h, hfind, hnd => by
      have hob : Origin.find c.put ob.id = some ob := hfind ob (List.mem_cons_self ..)
      have hido : ob.id.origin = o := h.orig ob (find_mem hob).1
      have hT : find T ob.id = some ob := (h.loc ob.id hido).trans hob
      simp only [List.map_cons, List.nodup_cons] at hnd
      have hrest : ∀ ob' ∈ l, Origin.find c.put ob'.id = some ob' :=
        fun ob' h' => hfind ob' (List.mem_cons_of_mem _ h')
      simp only [List.foldl_cons]
      cases ht : ob.task with
      | none =>
          have htp : (ob.project now).task = none := by rw [project_task, ht]; rfl
          have hstep : ltStep now c ob = c := by unfold ltStep; simp only [htp]
          have htrig : ltTrig now ob = none := by unfold ltTrig; simp only [htp]
          rw [hstep, List.filterMap_cons_none htrig]
          exact leaseTimeouts_sim now l c T h hrest hnd.2
      | some t =>
          obtain ⟨tv, htv⟩ : ∃ tv, (ob.project now).task = some tv :=
            ⟨t.view (ob.promise.project now), by rw [project_task, ht]; rfl⟩
          by_cases hc : (tv.state == TaskState.acquired) = true ∧ tv.leaseTimeoutAt.any (· ≤ now) = true
              ∧ ((ob.project now).promise.state == PromiseState.pending) = true
          · have heq := project_pending_eq hc.2.2
            rw [heq] at htv hc
            simp only [List.filterMap_cons, ltStep, ltTrig, heq, htv, hc, and_self, ↓reduceIte, execI_cons,
              processLeaseTimeout_fx, hT, Option.bind_some, Option.isSome_some]
            cases hdl : tv.leaseTimeoutAt with
            | none => simp [hdl] at hc
            | some dl =>
                have hdln : dl ≤ now := by
                  have := hc.2.1
                  rw [hdl, Option.any_some] at this
                  exact of_decide_eq_true this
                simp only [hdln, and_self, ↓reduceIte]
                refine leaseTimeouts_sim now l _ _ (h.write_task_plain hido hob _ rfl rfl) ?_ hnd.2
                intro ob' hob'
                have hne : ob'.id ≠ ob.id := fun e => hnd.1 (e ▸ List.mem_map_of_mem hob')
                have key : ∀ x : Object, x.id = ob.id → Origin.find (c.put.write x) ob'.id = some ob' := by
                  intro x hx
                  rw [find_write_other _ _ _ (fun e => hne (e.trans hx))]
                  exact hrest ob' hob'
                exact key _ rfl
          · have hstep : ltStep now c ob = c := by
              unfold ltStep; simp only [htv]; rw [if_neg hc]
            have htrig : ltTrig now ob = none := by
              unfold ltTrig; simp only [htv]; rw [if_neg hc]
            rw [hstep, List.filterMap_cons_none htrig]
            exact leaseTimeouts_sim now l c T h hrest hnd.2

def rtStep (now : Nat) (c : Commands) (o : Object) : Commands :=
  let o := o.project now
  match o.task, o.promise.type with
  | some t, .runnable target =>
      if t.state == .pending ∧ t.retryTimeoutAt.any (· ≤ now)
          ∧ o.promise.state == .pending then
        { c with
          arm := c.arm ++ [⟨now + Concrete.retryDelay, o.id, .retry⟩],
          put := c.put.write { o with task := some { t with retryTimeoutAt := some (now + Concrete.retryDelay) } },
          del := c.del ++ t.timers o.id,
          send := c.send ++ [(target, .execute o.id t.version)] }
      else
        c
  | _, _ =>
      c

def rtTrig (now : Nat) (o : Object) : Option Abstract.Trigger :=
  let o := o.project now
  match o.task, o.promise.type with
  | some t, .runnable _ =>
      if t.state == .pending ∧ t.retryTimeoutAt.any (· ≤ now) ∧ o.promise.state == .pending then
        some (.taskRetryTimeout ⟨o.id⟩)
      else
        none
  | _, _ =>
      none

theorem retryTimeouts_eq (now : Nat) (org : Origin) :
    Chain.retryTimeouts now org = org.objects.foldl (rtStep now) { put := org } := rfl

theorem retryTimeoutTriggers_eq (now : Nat) (org : Origin) :
    Chain.retryTimeoutTriggers now org = org.objects.filterMap (rtTrig now) := rfl

theorem processRetryTimeout_fx (id : Ident) (now : Nat) (T : Abstract.State) :
    (Abstract.handleInternal (.taskRetryTimeout ⟨id⟩) now (env T)).2 =
      match (find T id).bind fun X => if X.task.isSome then some (X.project now) else none with
      | none => []
      | some o =>
          match o.task with
          | none => []
          | some t =>
              match t.retryTimeoutAt with
              | none => []
              | some due =>
                  if t.state == .pending ∧ due ≤ now then
                    if o.promise.state == .pending then
                      match o.promise.type with
                      | .runnable target =>
                          [.setTask o.id { t with retryTimeoutAt := some (now + Concrete.retryDelay) },
                           .setMessage target (.execute o.id t.version)]
                      | _ => []
                    else
                      []
                  else
                    [] := by
  simp only [Abstract.handleInternal, Abstract.Internal.processRetryTimeout, bind_apply,
    viewTaskObject_apply]
  cases (find T id).bind fun X => if X.task.isSome then some (X.project now) else none with
  | none => rfl
  | some ob =>
      simp only
      cases ob.task with
      | none => rfl
      | some t =>
          simp only
          cases t.retryTimeoutAt with
          | none => rfl
          | some due =>
              simp only
              by_cases h1 : (t.state == TaskState.pending) = true ∧ due ≤ now
              · simp only [h1, and_self, ↓reduceIte]
                by_cases h2 : (ob.promise.state == PromiseState.pending) = true
                · simp only [h2, ↓reduceIte]
                  cases ob.promise.type <;>
                    simp only [bind_apply, ask_apply, setTask_apply, setMessage_apply, pure_apply,
                      List.nil_append, List.singleton_append, List.append_nil] <;> rfl
                · simp only [h2, Bool.false_eq_true, ↓reduceIte, pure_apply, List.nil_append]
              · simp only [h1, ↓reduceIte, pure_apply, List.nil_append]

theorem retryTimeouts_sim {o : String} {S : Abstract.State} (now : Nat) :
    ∀ (l : List Object) (c : Commands) (T : Abstract.State), SwInv o S c T →
      (∀ ob ∈ l, Origin.find c.put ob.id = some ob) → (l.map (·.id)).Nodup →
      SwInv o S (l.foldl (rtStep now) c) (execI (l.filterMap (rtTrig now)) now T)
  | [], _, _, h, _, _ => h
  | ob :: l, c, T, h, hfind, hnd => by
      have hob : Origin.find c.put ob.id = some ob := hfind ob (List.mem_cons_self ..)
      have hido : ob.id.origin = o := h.orig ob (find_mem hob).1
      have hT : find T ob.id = some ob := (h.loc ob.id hido).trans hob
      simp only [List.map_cons, List.nodup_cons] at hnd
      have hrest : ∀ ob' ∈ l, Origin.find c.put ob'.id = some ob' :=
        fun ob' h' => hfind ob' (List.mem_cons_of_mem _ h')
      simp only [List.foldl_cons]
      cases ht : ob.task with
      | none =>
          have htp : (ob.project now).task = none := by rw [project_task, ht]; rfl
          have hstep : rtStep now c ob = c := by unfold rtStep; simp only [htp]
          have htrig : rtTrig now ob = none := by unfold rtTrig; simp only [htp]
          rw [hstep, List.filterMap_cons_none htrig]
          exact retryTimeouts_sim now l c T h hrest hnd.2
      | some t =>
          obtain ⟨tv, htv⟩ : ∃ tv, (ob.project now).task = some tv :=
            ⟨t.view (ob.promise.project now), by rw [project_task, ht]; rfl⟩
          cases hty : (ob.project now).promise.type
          case runnable target =>
              by_cases hc : (tv.state == TaskState.pending) = true ∧ tv.retryTimeoutAt.any (· ≤ now) = true
                  ∧ ((ob.project now).promise.state == PromiseState.pending) = true
              · have heq := project_pending_eq hc.2.2
                rw [heq] at htv hc hty
                simp only [List.filterMap_cons, rtStep, rtTrig, heq, htv, hty, hc, and_self, ↓reduceIte,
                  execI_cons, processRetryTimeout_fx, hT, Option.bind_some, Option.isSome_some]
                cases hdl : tv.retryTimeoutAt with
                | none => simp [hdl] at hc
                | some due =>
                    have hdln : due ≤ now := by
                      have := hc.2.1
                      rw [hdl, Option.any_some] at this
                      exact of_decide_eq_true this
                    simp only [hdln, and_self, ↓reduceIte]
                    have hlist : [Abstract.Effect.setTask ob.id { tv with retryTimeoutAt := some (now + Concrete.retryDelay) },
                        Abstract.Effect.setMessage target (.execute ob.id tv.version)] =
                      [Abstract.Effect.setTask ob.id { tv with retryTimeoutAt := some (now + Concrete.retryDelay) }] ++
                        [(target, Message.execute ob.id tv.version)].map (fun (a, m) => Abstract.Effect.setMessage a m) := rfl
                    rw [hlist, applyAll_append]
                    refine retryTimeouts_sim now l _ _
                      ((h.write_task_plain hido hob _
                        (c' := { c with
                          arm := c.arm ++ [⟨now + Concrete.retryDelay, ob.id, .retry⟩],
                          put := c.put.write { ob with task := some { tv with retryTimeoutAt := some (now + Concrete.retryDelay) } },
                          del := c.del ++ tv.timers ob.id }) rfl rfl).sends _ rfl rfl) ?_ hnd.2
                    intro ob' hob'
                    have hne : ob'.id ≠ ob.id := fun e => hnd.1 (e ▸ List.mem_map_of_mem hob')
                    have key : ∀ x : Object, x.id = ob.id → Origin.find (c.put.write x) ob'.id = some ob' := by
                      intro x hx
                      rw [find_write_other _ _ _ (fun e => hne (e.trans hx))]
                      exact hrest ob' hob'
                    exact key _ rfl
              · have hstep : rtStep now c ob = c := by
                  unfold rtStep; simp only [htv, hty]; rw [if_neg hc]
                have htrig : rtTrig now ob = none := by
                  unfold rtTrig; simp only [htv, hty]; rw [if_neg hc]
                rw [hstep, List.filterMap_cons_none htrig]
                exact retryTimeouts_sim now l c T h hrest hnd.2
          all_goals
            have hstep : rtStep now c ob = c := by unfold rtStep; simp only [htv, hty]
            have htrig : rtTrig now ob = none := by unfold rtTrig; simp only [htv, hty]
            rw [hstep, List.filterMap_cons_none htrig]
            exact retryTimeouts_sim now l c T h hrest hnd.2

theorem promiseTimeouts_pass {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (horig : ∀ ob ∈ org.objects, ob.id.origin = o) (hnodup : (org.objects.map (·.id)).Nodup)
    (hwf : WF org) (now : Nat) :
    SwInv o S (Chain.promiseTimeouts now org) (execI (Chain.promiseTimeoutTriggers now org) now S) := by
  rw [promiseTimeouts_eq, promiseTimeoutTriggers_eq]
  exact promiseTimeouts_sim now org.objects _ S (SwInv.init hL horig hnodup hwf)
    (fun ob hob => find_self_of_nodup hnodup hob) hnodup

theorem listeners_pass {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (horig : ∀ ob ∈ org.objects, ob.id.origin = o) (hnodup : (org.objects.map (·.id)).Nodup)
    (hwf : WF org) (now : Nat) :
    SwInv o S (Chain.listeners now org) (execI (Chain.listenerTriggers now org) now S) := by
  rw [listeners_eq, listenerTriggers_eq]
  exact lsBulk_sim now org.objects _ S (SwInv.init hL horig hnodup hwf)
    (fun ob hob => find_self_of_nodup hnodup hob) hnodup

theorem callbacks_pass {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (horig : ∀ ob ∈ org.objects, ob.id.origin = o) (hnodup : (org.objects.map (·.id)).Nodup)
    (hwf : WF org) (now : Nat) :
    SwInv o S (Chain.callbacks now org) (execI (Chain.callbackTriggers now org) now S) := by
  rw [callbacks_eq, callbackTriggers_eq]
  exact cbOld_sim hwf now org.objects _ S (SwInv.init hL horig hnodup hwf) (fun _ h => h) hnodup
    (fun ob hob => by
      show (Origin.find org ob.id).map _ = _
      unfold Origin.find
      rw [find_self_of_nodup hnodup hob]
      rfl)

theorem leaseTimeouts_pass {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (horig : ∀ ob ∈ org.objects, ob.id.origin = o) (hnodup : (org.objects.map (·.id)).Nodup)
    (hwf : WF org) (now : Nat) :
    SwInv o S (Chain.leaseTimeouts now org) (execI (Chain.leaseTimeoutTriggers now org) now S) := by
  rw [leaseTimeouts_eq, leaseTimeoutTriggers_eq]
  exact leaseTimeouts_sim now org.objects _ S (SwInv.init hL horig hnodup hwf)
    (fun ob hob => find_self_of_nodup hnodup hob) hnodup

theorem retryTimeouts_pass {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (horig : ∀ ob ∈ org.objects, ob.id.origin = o) (hnodup : (org.objects.map (·.id)).Nodup)
    (hwf : WF org) (now : Nat) :
    SwInv o S (Chain.retryTimeouts now org) (execI (Chain.retryTimeoutTriggers now org) now S) := by
  rw [retryTimeouts_eq, retryTimeoutTriggers_eq]
  exact retryTimeouts_sim now org.objects _ S (SwInv.init hL horig hnodup hwf)
    (fun ob hob => find_self_of_nodup hnodup hob) hnodup

theorem chain_sweep_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (horig : ∀ ob ∈ org.objects, ob.id.origin = o) (hnodup : (org.objects.map (·.id)).Nodup)
    (hwf : WF org) (now : Nat) :
    SwInv o S (Chain.sweep now org) (execI (Chain.sweepTriggers now org) now S) := by
  simp only [Chain.sweep, Chain.sweepTriggers, execI_append]
  have h1 := promiseTimeouts_pass hL horig hnodup hwf now
  have h2 := h1.merge (listeners_pass h1.loc h1.orig h1.nodup h1.wf now)
  have h3 := h2.merge (callbacks_pass h2.loc h2.orig h2.nodup h2.wf now)
  have h4 := h3.merge (leaseTimeouts_pass h3.loc h3.orig h3.nodup h3.wf now)
  exact h4.merge (retryTimeouts_pass h4.loc h4.orig h4.nodup h4.wf now)

end Refinement
