import refinement.sweep

namespace Refinement

open Protocol (Ident Message Object PromiseObject TaskObject PromiseState TaskState)
open Concrete (Origin Commands)
open scoped List

theorem ids_map {l : List Object} {g : Object → Object} (hg : ∀ o, (g o).id = o.id) :
    (l.map g).map (·.id) = l.map (·.id) := by
  rw [List.map_map]; congr 1; funext o; exact hg o

theorem set_map {l : List Object} {g : Object → Object} (hg : ∀ o, (g o).id = o.id) {x : Object}
    (hx : ∃ o ∈ l, o.id = x.id) :
    (⟨l.map g⟩ : Origin).set x = ⟨l.map fun o => if o.id == x.id then x else g o⟩ := by
  have hany : (l.map g).any (·.id == x.id) = true := by
    rw [List.any_map]
    refine List.any_eq_true.2 ?_
    obtain ⟨o, ho, hox⟩ := hx
    exact ⟨o, ho, by simp [Function.comp, hg, hox]⟩
  apply Origin.eq_of_objects
  rw [set_present hany, List.map_map]
  congr 1
  funext o
  simp only [Function.comp, hg]

theorem find?_map_self {l : List Object} {g : Object → Object} (hg : ∀ o, (g o).id = o.id)
    (hnd : (l.map (·.id)).Nodup) {ob : Object} (hob : ob ∈ l) :
    (l.map g).find? (·.id == ob.id) = some (g ob) := by
  rw [find?_map_id g hg, find_self_of_nodup hnd hob]
  rfl

theorem eq_of_id_nodup {l : List Object} (hnd : (l.map (·.id)).Nodup) {a b : Object} (ha : a ∈ l) (hb : b ∈ l)
    (h : a.id = b.id) : a = b := by
  have h1 := find_self_of_nodup hnd ha
  have h2 := find_self_of_nodup hnd hb
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

theorem flatMap_const_nil {α β : Type} (l : List α) : l.flatMap (fun _ => ([] : List β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem getD_id {step : Object → Option Object} (hid : ∀ o x, step o = some x → x.id = o.id) (o : Object) :
    ((step o).getD o).id = o.id := by
  cases hs : step o with
  | none => rfl
  | some x => exact hid o x hs

theorem bulk_put (step : Object → Option Object) (hid : ∀ o x, step o = some x → x.id = o.id)
    (f : Commands → Object → Commands)
    (hf : ∀ c o, (f c o).org = match step o with | some x => c.org.set x | none => c.org) :
    ∀ (P Q : List Object) (c : Commands), ((P ++ Q).map (·.id)).Nodup →
      c.org = ⟨(P ++ Q).map fun o => if o.id ∈ P.map (·.id) then (step o).getD o else o⟩ →
      (Q.foldl f c).org = ⟨(P ++ Q).map fun o => (step o).getD o⟩
  | P, [], c, _, hc => by
      rw [List.foldl_nil, hc]
      apply Origin.eq_of_objects
      apply List.map_congr_left
      intro o ho
      simp only [List.append_nil] at ho
      rw [if_pos (List.mem_map_of_mem ho)]
  | P, o :: Q, c, hnd, hc => by
      rw [List.foldl_cons]
      have hmem : o ∈ P ++ o :: Q := by simp
      have hnd' : ((P ++ [o] ++ Q).map (·.id)).Nodup := by simpa using hnd
      have hnotP : o.id ∉ P.map (·.id) := by
        intro hm
        rw [List.map_append, List.nodup_append] at hnd
        obtain ⟨_, _, hdis⟩ := hnd
        exact hdis o.id hm o.id (by simp) rfl
      have hstep : (f c o).org = ⟨(P ++ o :: Q).map fun ob =>
          if ob.id ∈ (P ++ [o]).map (·.id) then (step ob).getD ob else ob⟩ := by
        rw [hf, hc]
        cases hs : step o with
        | none =>
            apply Origin.eq_of_objects
            apply List.map_congr_left
            intro ob hob
            by_cases e : ob.id = o.id
            · have : ob = o := eq_of_id_nodup hnd hob hmem e
              subst this
              simp [hnotP, hs]
            · simp [e]
        | some x =>
            have hxo : x.id = o.id := hid o x hs
            simp only
            rw [set_map (fun ob => by split <;> first | exact getD_id hid ob | rfl) ⟨o, hmem, hxo.symm⟩]
            apply Origin.eq_of_objects
            apply List.map_congr_left
            intro ob hob
            by_cases e : ob.id = o.id
            · have : ob = o := eq_of_id_nodup hnd hob hmem e
              subst this
              simp [hxo, hs]
            · have e' : (ob.id == x.id) = false := by simp [hxo, e]
              simp [e', e]
      have := bulk_put step hid f hf (P ++ [o]) Q (f c o) hnd' (by rw [hstep]; simp)
      simpa using this

theorem bulk_send (msg : Object → List (String × Message)) (f : Commands → Object → Commands)
    (hf : ∀ c o, (f c o).send = c.send ++ msg o) :
    ∀ (Q : List Object) (c : Commands), (Q.foldl f c).send = c.send ++ Q.flatMap msg
  | [], c => by simp
  | o :: Q, c => by
      rw [List.foldl_cons, bulk_send msg f hf Q, hf, List.flatMap_cons, List.append_assoc]

theorem promiseTimeouts_put (now : Nat) (d : Origin) (hnd : (d.objects.map (·.id)).Nodup) :
    (Chain.promiseTimeouts now d).org = ⟨d.objects.map fun o => (Concrete.promiseTimeout now o).getD o⟩ := by
  rw [promiseTimeouts_eq]
  have := bulk_put (Concrete.promiseTimeout now)
    (fun o x hx => by
      unfold Concrete.promiseTimeout at hx
      split at hx
      · rw [Option.some.injEq] at hx; rw [← hx]; rfl
      · cases hx)
    (ptStep now)
    (fun c o => by unfold ptStep Concrete.promiseTimeout; split <;> rfl)
    [] d.objects { org := d } (by simpa using hnd) (by simp)
  simpa using this

theorem promiseTimeouts_send (now : Nat) (d : Origin) : (Chain.promiseTimeouts now d).send = [] := by
  rw [promiseTimeouts_eq]
  have := bulk_send (fun _ => []) (ptStep now) (fun c o => by unfold ptStep; split <;> simp) d.objects { org := d }
  rw [this, flatMap_const_nil]; rfl

def listenerObj (now : Nat) (o : Object) : Option Object := (Concrete.listener now o).map (·.1)

def listenerMsgs (now : Nat) (o : Object) : List (String × Message) :=
  ((Concrete.listener now o).map (·.2)).getD []

theorem listeners_put (now : Nat) (d : Origin) (hnd : (d.objects.map (·.id)).Nodup) :
    (Chain.listeners now d).org = ⟨d.objects.map fun o => (listenerObj now o).getD o⟩ := by
  rw [listeners_eq]
  have := bulk_put (listenerObj now)
    (fun o x hx => by
      simp only [listenerObj, Concrete.listener] at hx
      split at hx
      · simp only [Option.map_some, Option.some.injEq] at hx; rw [← hx]; rfl
      · cases hx)
    (lsBulk now)
    (fun c o => by simp only [lsBulk, listenerObj, Concrete.listener]; split <;> simp_all)
    [] d.objects { org := d } (by simpa using hnd) (by simp)
  simpa using this

theorem listeners_send (now : Nat) (d : Origin) :
    (Chain.listeners now d).send = d.objects.flatMap (listenerMsgs now) := by
  rw [listeners_eq]
  have := bulk_send (listenerMsgs now) (lsBulk now)
    (fun c o => by simp only [lsBulk, listenerMsgs, Concrete.listener]; split <;> simp_all) d.objects { org := d }
  simpa using this

theorem leaseTimeouts_put (now : Nat) (d : Origin) (hnd : (d.objects.map (·.id)).Nodup) :
    (Chain.leaseTimeouts now d).org = ⟨d.objects.map fun o => (Concrete.leaseTimeout now o).getD o⟩ := by
  rw [leaseTimeouts_eq]
  have := bulk_put (Concrete.leaseTimeout now)
    (fun o x hx => by
      simp only [Concrete.leaseTimeout] at hx
      split at hx
      · split at hx
        · rw [Option.some.injEq] at hx; rw [← hx]; rfl
        · cases hx
      · cases hx)
    (ltStep now)
    (fun c o => by
      simp only [ltStep, Concrete.leaseTimeout]
      cases ht : (o.project now).task with
      | none => rfl
      | some t =>
          simp only
          split <;> rfl)
    [] d.objects { org := d } (by simpa using hnd) (by simp)
  simpa using this

theorem leaseTimeouts_send (now : Nat) (d : Origin) : (Chain.leaseTimeouts now d).send = [] := by
  rw [leaseTimeouts_eq]
  have := bulk_send (fun _ => []) (ltStep now)
    (fun c o => by simp only [ltStep]; split <;> (try split) <;> simp) d.objects { org := d }
  rw [this, flatMap_const_nil]; rfl

def retryObj (now : Nat) (o : Object) : Option Object := (Concrete.retryTimeout now o).map (·.1)

def retryMsgs (now : Nat) (o : Object) : List (String × Message) :=
  ((Concrete.retryTimeout now o).map (·.2)).getD []

theorem retryTimeouts_put (now : Nat) (d : Origin) (hnd : (d.objects.map (·.id)).Nodup) :
    (Chain.retryTimeouts now d).org = ⟨d.objects.map fun o => (retryObj now o).getD o⟩ := by
  rw [retryTimeouts_eq]
  have := bulk_put (retryObj now)
    (fun o x hx => by
      simp only [retryObj, Concrete.retryTimeout] at hx
      split at hx
      · split at hx
        · simp only [Option.map_some, Option.some.injEq] at hx; rw [← hx]; rfl
        · cases hx
      · cases hx)
    (rtStep now)
    (fun c o => by
      simp only [rtStep, retryObj, Concrete.retryTimeout]
      cases ht : (o.project now).task with
      | none => cases (o.project now).promise.type <;> rfl
      | some t =>
          cases hty : (o.project now).promise.type
          all_goals try rfl
          simp only
          split <;> rfl)
    [] d.objects { org := d } (by simpa using hnd) (by simp)
  simpa using this

theorem retryTimeouts_send (now : Nat) (d : Origin) :
    (Chain.retryTimeouts now d).send = d.objects.flatMap (retryMsgs now) := by
  rw [retryTimeouts_eq]
  have := bulk_send (retryMsgs now) (rtStep now)
    (fun c o => by
      simp only [rtStep, retryMsgs, Concrete.retryTimeout]
      cases ht : (o.project now).task with
      | none => cases (o.project now).promise.type <;> exact (List.append_nil c.send).symm
      | some t =>
          cases hty : (o.project now).promise.type
          all_goals try exact (List.append_nil c.send).symm
          simp only
          split
          · rfl
          · exact (List.append_nil c.send).symm)
    d.objects { org := d }
  simpa using this


theorem view_fulfilled_state (t : TaskObject) (p : PromiseObject) (h : p.state ≠ .pending) :
    (t.view p).state = .fulfilled := by
  unfold TaskObject.view
  have hp : (p.state != PromiseState.pending) = true := by simpa using h
  by_cases ht : (t.state != TaskState.fulfilled) = true
  · simp [hp, ht, TaskObject.fulfill]
  · simp only [hp, ht, and_false, Bool.false_eq_true, ↓reduceIte]
    simpa using ht

theorem resume_fulfilled (now : Nat) (t : TaskObject) (a : Ident) (h : t.state = .fulfilled) :
    t.resume now a = t := by
  unfold TaskObject.resume
  rw [h]

theorem foldl_resume_fulfilled (now : Nat) (t : TaskObject) (h : t.state = .fulfilled) :
    ∀ l : List Ident, l.foldl (·.resume now ·) t = t
  | [] => rfl
  | a :: l => by rw [List.foldl_cons, resume_fulfilled now t a h, foldl_resume_fulfilled now t h l]

theorem view_of_fulfilled (t : TaskObject) (p : PromiseObject) (h : t.state = .fulfilled) : t.view p = t := by
  unfold TaskObject.view
  simp [h]

theorem view_congr (t : TaskObject) {p q : PromiseObject} (h : p.state = q.state) : t.view p = t.view q := by
  unfold TaskObject.view
  rw [h]

theorem view_foldl_resume (now : Nat) (t : TaskObject) (p : PromiseObject) (l : List Ident) :
    (l.foldl (·.resume now ·) (t.view p)).view p = l.foldl (·.resume now ·) (t.view p) := by
  by_cases hp : p.state = .pending
  · rw [view_pending _ _ hp]
  · have hf := view_fulfilled_state t p hp
    rw [foldl_resume_fulfilled now _ hf l, view_of_fulfilled _ _ hf]

theorem Object.project_set_callbacks (o : Object) (L : List Ident) (n : Nat) :
    ({ o with promise := { o.promise with callbacks := L } } : Object).project n =
      { o.project n with promise := { (o.project n).promise with callbacks := L } } := by
  simp only [Object.project, PromiseObject.project_set_callbacks]
  rfl

theorem Object.ext' {a b : Object} (h1 : a.id = b.id) (h2 : a.promise = b.promise) (h3 : a.task = b.task) : a = b := by
  cases a; cases b; simp only at h1 h2 h3; rw [h1, h2, h3]

def struckP (now : Nat) (P : List Object) (ob : Object) : Prop :=
  ob.id ∈ P.map (·.id) ∧ ((ob.project now).promise.state != PromiseState.pending) = true ∧
    (!(ob.project now).promise.callbacks.isEmpty) = true

instance (now : Nat) (P : List Object) (ob : Object) : Decidable (struckP now P ob) := by
  unfold struckP; infer_instance

def stageP (now : Nat) (P : List Object) (ob : Object) : Object :=
  { ob.project now with
    promise := if struckP now P ob then { (ob.project now).promise with callbacks := [] }
               else (ob.project now).promise,
    task := (ob.project now).task.map ((Concrete.awaiting now P ob.id).foldl (·.resume now ·)) }

def hit (now : Nat) (P : List Object) (ob : Object) : Prop :=
  struckP now P ob ∨ ((ob.project now).task.isSome = true ∧ (!(Concrete.awaiting now P ob.id).isEmpty) = true)

instance (now : Nat) (P : List Object) (ob : Object) : Decidable (hit now P ob) := by
  unfold hit; infer_instance

def stage (now : Nat) (P : List Object) (ob : Object) : Object :=
  if hit now P ob then stageP now P ob else ob

theorem stageP_id (now : Nat) (P : List Object) (ob : Object) : (stageP now P ob).id = ob.id := rfl

theorem stage_id (now : Nat) (P : List Object) (ob : Object) : (stage now P ob).id = ob.id := by
  unfold stage
  split <;> rfl

theorem stageP_promise_state (now : Nat) (P : List Object) (ob : Object) :
    (stageP now P ob).promise.state = (ob.promise.project now).state := by
  show (if struckP now P ob then { (ob.project now).promise with callbacks := [] }
    else (ob.project now).promise).state = _
  split <;> rfl

theorem stageP_project (now : Nat) (P : List Object) (ob : Object) :
    (stageP now P ob).project now = stageP now P ob := by
  have hpp : (stageP now P ob).promise.project now = (stageP now P ob).promise := by
    show (if struckP now P ob then { (ob.project now).promise with callbacks := [] }
      else (ob.project now).promise).project now =
      (if struckP now P ob then { (ob.project now).promise with callbacks := [] } else (ob.project now).promise)
    split
    · rw [PromiseObject.project_set_callbacks, project_promise, PromiseObject.project_idem]
    · rw [project_promise, PromiseObject.project_idem]
  have hstate := stageP_promise_state now P ob
  show ({ stageP now P ob with promise := (stageP now P ob).promise.project now, task := (stageP now P ob).task.map (·.view ((stageP now P ob).promise.project now)) } : Object) = stageP now P ob
  rw [hpp]
  have ht : (stageP now P ob).task.map (·.view (stageP now P ob).promise) = (stageP now P ob).task := by
    show ((ob.project now).task.map _).map _ = (ob.project now).task.map _
    rw [project_task, Option.map_map, Option.map_map]
    cases ob.task with
    | none => rfl
    | some t =>
        simp only [Option.map_some, Function.comp, Option.some.injEq]
        rw [view_congr _ hstate, view_foldl_resume]
  rw [ht]

theorem stage_project (now : Nat) (P : List Object) (ob : Object) :
    (stage now P ob).project now = stageP now P ob := by
  unfold stage
  split
  · exact stageP_project now P ob
  · rename_i hc
    unfold hit at hc
    simp only [not_or, not_and] at hc
    show ob.project now = stageP now P ob
    unfold stageP
    rw [if_neg hc.1]
    cases ht : (ob.project now).task with
    | none => exact Object.ext' rfl rfl (by rw [ht]; rfl)
    | some t =>
        have hne : (Concrete.awaiting now P ob.id).isEmpty = true := by
          have := hc.2 (by rw [ht]; rfl)
          simpa using this
        rw [List.isEmpty_iff.1 hne]
        simp only [List.foldl_nil, Option.map_id']
        exact Object.ext' rfl rfl ht

theorem stage_full {now : Nat} {d : Origin} {ob : Object} (hob : ob ∈ d.objects) :
    stage now d.objects ob = (Concrete.callback now d ob).getD ob := by
  have hm : ob.id ∈ d.objects.map (·.id) := List.mem_map_of_mem hob
  have hs : struckP now d.objects ob ↔ (((ob.project now).promise.state != PromiseState.pending) = true ∧
      (!(ob.project now).promise.callbacks.isEmpty) = true) := by
    unfold struckP; simp [hm]
  unfold stage stageP hit
  simp only [Concrete.callback, project_id]
  by_cases h1 : struckP now d.objects ob
  · have h1' := hs.1 h1
    rw [if_pos (Or.inl h1), if_pos (Or.inl h1'), if_pos h1, if_pos h1']; rfl
  · have h1' : ¬ (((ob.project now).promise.state != PromiseState.pending) = true ∧
        (!(ob.project now).promise.callbacks.isEmpty) = true) := fun h => h1 (hs.2 h)
    by_cases h2 : (ob.project now).task.isSome = true ∧ (!(Concrete.awaiting now d.objects ob.id).isEmpty) = true
    · rw [if_pos (Or.inr h2), if_pos (Or.inr h2), if_neg h1, if_neg h1']; rfl
    · rw [if_neg (not_or.2 ⟨h1, h2⟩), if_neg (not_or.2 ⟨h1', h2⟩)]; rfl

theorem awaiting_append (now : Nat) (P Q : List Object) (id : Ident) :
    Concrete.awaiting now (P ++ Q) id = Concrete.awaiting now P id ++ Concrete.awaiting now Q id := by
  unfold Concrete.awaiting; rw [List.filterMap_append]

theorem awaiting_single (now : Nat) (s : Object) (id : Ident) :
    Concrete.awaiting now [s] id =
      if ((s.project now).promise.state != .pending) = true ∧ (s.project now).promise.callbacks.contains id = true
      then [(s.project now).id] else [] := by
  by_cases hc : ((s.project now).promise.state != PromiseState.pending) = true ∧
      (s.project now).promise.callbacks.contains id = true
  · simp only [Concrete.awaiting, List.filterMap_cons, List.filterMap_nil, if_pos hc]
  · simp only [Concrete.awaiting, List.filterMap_cons, List.filterMap_nil, if_neg hc]

theorem awaiting_single_none (now : Nat) (s : Object) (id : Ident)
    (h : ((s.project now).promise.state != .pending) = true → (s.project now).promise.callbacks.contains id = false) :
    Concrete.awaiting now [s] id = [] := by
  rw [awaiting_single]
  split
  · rename_i hc; rw [h hc.1] at hc; exact absurd hc.2 Bool.false_ne_true
  · rfl

theorem struckP_append_ne {now : Nat} {P : List Object} {s ob : Object} (hne : ob.id ≠ s.id) :
    struckP now (P ++ [s]) ob ↔ struckP now P ob := by
  unfold struckP
  simp [hne]

theorem stageP_append_congr {now : Nat} {P : List Object} {s ob : Object}
    (hstruck : struckP now (P ++ [s]) ob ↔ struckP now P ob)
    (haw : Concrete.awaiting now [s] ob.id = [] ∨ ob.task = none) :
    stageP now (P ++ [s]) ob = stageP now P ob := by
  apply Object.ext'
  · rfl
  · show (if struckP now (P ++ [s]) ob then _ else _) = (if struckP now P ob then _ else _)
    simp only [hstruck]
  · show (ob.project now).task.map _ = (ob.project now).task.map _
    rcases haw with haw | haw
    · rw [awaiting_append, haw, List.append_nil]
    · rw [project_task, haw]; rfl

theorem stage_append_inert (now : Nat) (P : List Object) (s ob : Object)
    (haw : ∀ id, Concrete.awaiting now [s] id = [])
    (hns : ¬ struckP now (P ++ [s]) s) (hobs : ob.id = s.id → ob = s) :
    stage now (P ++ [s]) ob = stage now P ob := by
  have hstruck : struckP now (P ++ [s]) ob ↔ struckP now P ob := by
    by_cases e : ob.id = s.id
    · rw [hobs e]
      constructor
      · intro h; exact absurd h hns
      · intro h; exact absurd ⟨by simp only [List.map_append, List.mem_append]; exact Or.inl h.1, h.2.1, h.2.2⟩ hns
    · exact struckP_append_ne e
  have hsp := stageP_append_congr hstruck (Or.inl (haw ob.id))
  have hh : hit now (P ++ [s]) ob ↔ hit now P ob := by
    unfold hit; rw [hstruck, awaiting_append, haw ob.id, List.append_nil]
  unfold stage
  rw [hsp]
  exact ite_congr (propext hh) (fun _ => rfl) (fun _ => rfl)

theorem filter_cons_ne_self' {α : Type} [BEq α] [LawfulBEq α] {a : α} {l : List α} (h : a ∉ l) :
    (a :: l).filter (· != a) = l := by
  simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine List.filter_eq_self.2 fun b hb => ?_
  have hne : b ≠ a := fun e => h (e ▸ hb)
  simpa using hne

theorem set_task_self {wo : Object} {t : TaskObject} (h : wo.task = some t) :
    ({ wo with task := some t } : Object) = wo := by
  cases wo; simp only at h; rw [h]

theorem set_callbacks_self {p : PromiseObject} {C : List Ident} (h : p.callbacks = C) :
    ({ p with callbacks := C } : PromiseObject) = p := by
  cases p; simp only at h; rw [h]

theorem stageP_task_none {now : Nat} {P : List Object} {ob : Object} (h : ob.task = none) :
    (stageP now P ob).task = none := by
  simp [stageP, Object.project, h]

theorem stageP_task_some {now : Nat} {P : List Object} {ob : Object} {t : TaskObject} (h : ob.task = some t) :
    (stageP now P ob).task =
      some ((Concrete.awaiting now P ob.id).foldl (·.resume now ·) (t.view (ob.promise.project now))) := by
  simp [stageP, Object.project, h]

theorem stageP_promise_unstruck {now : Nat} {P : List Object} {s : Object} (h : s.id ∉ P.map (·.id)) :
    (stageP now P s).promise = (s.project now).promise := by
  show (if struckP now P s then _ else _) = _
  rw [if_neg (fun hc => h hc.1)]

def stageC (now : Nat) (P : List Object) (s : Object) (Q : List Ident) : Object :=
  { stageP now P s with promise := { (stageP now P s).promise with callbacks := Q } }

theorem stageC_id (now : Nat) (P : List Object) (s : Object) (Q : List Ident) : (stageC now P s Q).id = s.id := rfl

def inner (now : Nat) (P : List Object) (s : Object) (Q₁ Q₂ : List Ident) (ob : Object) : Object :=
  if ob.id = s.id then
    (if Q₁ = [] then stage now P s else stageC now P s Q₂)
  else if ob.id ∈ Q₁ ∧ ob.task.isSome = true then
    { stageP now P ob with task := (stageP now P ob).task.map (·.resume now s.id) }
  else
    stage now P ob

theorem inner_id (now : Nat) (P : List Object) (s : Object) (Q₁ Q₂ : List Ident) (ob : Object) :
    (inner now P s Q₁ Q₂ ob).id = ob.id := by
  unfold inner
  split
  · rename_i h
    split
    · rw [stage_id]; exact h.symm
    · exact h.symm
  · split
    · rfl
    · exact stage_id now P ob

theorem inner_start {now : Nat} {d : Origin} (hnd : (d.objects.map (·.id)).Nodup) {P : List Object} {s : Object}
    (hs : s ∈ d.objects) (L : List Ident) {ob : Object} (hob : ob ∈ d.objects) :
    inner now P s [] L ob = stage now P ob := by
  unfold inner
  split
  · rename_i h
    rw [eq_of_id_nodup hnd hob hs h, if_pos rfl]
  · rw [if_neg (fun h => by simp at h)]

theorem resume_put (now : Nat) (a : Ident) (c : Commands) (w : Ident) :
    (Chain.resume now a c w).org =
      match (c.org.get w now).bind (fun o => o.task.map (o, ·)) with
      | none => c.org
      | some (wo, t) => c.org.set { wo with task := some (t.resume now a) } := by
  unfold Chain.resume
  cases hb : (c.org.get w now).bind (fun o => o.task.map (o, ·)) with
  | none => rfl
  | some p =>
      obtain ⟨wo, t⟩ := p
      have hwt : wo.task = some t := by
        cases hg : c.org.get w now with
        | none => rw [hg] at hb; cases hb
        | some o =>
            rw [hg, Option.bind_some] at hb
            cases ho : o.task with
            | none => rw [ho] at hb; cases hb
            | some t' =>
                rw [ho, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
                obtain ⟨rfl, rfl⟩ := hb
                exact ho
      simp only
      cases hs : t.state
      case suspended => simp [TaskObject.resume, hs]
      case fulfilled =>
        simp only [TaskObject.resume, hs]
        rw [set_task_self hwt]
      all_goals
        simp only [TaskObject.resume, hs]
        by_cases hc : t.resumes.contains a = true
        · rw [if_pos hc, if_pos hc, set_task_self hwt]
        · rw [if_neg hc, if_neg hc]

theorem resume_send (now : Nat) (a : Ident) (c : Commands) (w : Ident) :
    (Chain.resume now a c w).send = c.send := by
  unfold Chain.resume
  split
  · rfl
  · split <;> (try split) <;> rfl

theorem cbStepOld_send (now : Nat) (id : Ident) (c : Commands) (w : Ident) :
    (cbStepOld now id c w).send = c.send := by
  unfold cbStepOld
  split
  · rw [resume_send]
  · rfl

theorem inner_step {now : Nat} {d : Origin} (hnd : (d.objects.map (·.id)).Nodup) {P : List Object} {s : Object}
    (hs : s ∈ d.objects) (hsP : s.id ∉ P.map (·.id))
    {L : List Ident} (hL : (s.project now).promise.callbacks = L) (hLnd : L.Nodup) (hsL : s.id ∉ L) :
    ∀ (Q₁ Q₂ : List Ident) (w : Ident) (c : Commands), L = Q₁ ++ w :: Q₂ →
      c.org = ⟨d.objects.map (inner now P s Q₁ (w :: Q₂))⟩ →
      (cbStepOld now s.id c w).org = ⟨d.objects.map (inner now P s (Q₁ ++ [w]) Q₂)⟩ := by
  intro Q₁ Q₂ w c hsplit hc
  have hwL : w ∈ L := by rw [hsplit]; simp
  have hws : w ≠ s.id := fun e => hsL (e ▸ hwL)
  have hnd' := hsplit ▸ hLnd
  rw [List.nodup_append] at hnd'
  obtain ⟨_, hnd2, hdis⟩ := hnd'
  have hwQ₁ : w ∉ Q₁ := fun hm => hdis w hm w (List.mem_cons_self ..) rfl
  have hwQ₂ : w ∉ Q₂ := (List.nodup_cons.1 hnd2).1
  have hcurS : c.org.get s.id now = some (stageC now P s (w :: Q₂)) := by
    rw [get_eq, hc]
    show ((d.objects.map (inner now P s Q₁ (w :: Q₂))).find? (·.id == s.id)).map (·.project now) = _
    rw [find?_map_self (inner_id now P s Q₁ (w :: Q₂)) hnd hs, Option.map_some, Option.some.injEq]
    unfold inner
    rw [if_pos rfl]
    split
    · rename_i hQ
      rw [stage_project]
      have : (stageP now P s).promise.callbacks = w :: Q₂ := by
        rw [stageP_promise_unstruck hsP, hL, hsplit, hQ, List.nil_append]
      show stageP now P s = { stageP now P s with promise := { (stageP now P s).promise with callbacks := w :: Q₂ } }
      rw [set_callbacks_self this]
    · show ({ stageP now P s with promise := { (stageP now P s).promise with callbacks := w :: Q₂ } } : Object).project now = _
      rw [Object.project_set_callbacks, stageP_project]
      rfl
  have hc₁ : (cbStepOld now s.id c w).org =
      (Chain.resume now s.id { c with org := c.org.set (stageC now P s Q₂) } w).org := by
    unfold cbStepOld
    rw [hcurS]
    show (Chain.resume now s.id { c with org := c.org.set { stageC now P s (w :: Q₂) with promise := { (stageC now P s (w :: Q₂)).promise with callbacks := (stageC now P s (w :: Q₂)).promise.callbacks.filter (· != w) } } } w).org = _
    show (Chain.resume now s.id { c with org := c.org.set { stageP now P s with promise := { (stageP now P s).promise with callbacks := (w :: Q₂).filter (· != w) } } } w).org = _
    rw [filter_cons_ne_self' hwQ₂]
    rfl
  rw [hc₁, resume_put]
  simp only
  have hput₁ : c.org.set (stageC now P s Q₂) =
      ⟨d.objects.map fun ob => if ob.id == s.id then stageC now P s Q₂ else inner now P s Q₁ (w :: Q₂) ob⟩ := by
    rw [hc, set_map (x := stageC now P s Q₂) (inner_id now P s Q₁ (w :: Q₂)) ⟨s, hs, rfl⟩, stageC_id]
  have hf₁ : ∀ ob, (if ob.id == s.id then stageC now P s Q₂ else inner now P s Q₁ (w :: Q₂) ob).id = ob.id := by
    intro ob
    split
    · rename_i e; exact (beq_iff_eq.1 e).symm
    · exact inner_id ..
  rw [hput₁]
  cases hfw : d.objects.find? (·.id == w) with
  | none =>
      have hnone : (d.objects.map fun ob => if ob.id == s.id then stageC now P s Q₂
          else inner now P s Q₁ (w :: Q₂) ob).find? (fun x : Object => x.id == w) = none := by
        rw [find?_map_id _ hf₁, hfw]; rfl
      have hg : (⟨d.objects.map fun ob => if ob.id == s.id then stageC now P s Q₂
          else inner now P s Q₁ (w :: Q₂) ob⟩ : Origin).get w now = none := by
        rw [get_eq]
        show ((d.objects.map _).find? (fun x : Object => x.id == w)).map _ = none
        rw [hnone]; rfl
      rw [hg, Option.bind_none]
      apply Origin.eq_of_objects
      apply List.map_congr_left
      intro ob hob
      have hobw : ob.id ≠ w := by
        intro e
        have := List.find?_eq_none.1 hfw ob hob
        exact this (by simp [e])
      by_cases e : ob.id = s.id
      · have e' : (ob.id == s.id) = true := by simp [e]
        rw [if_pos e']
        unfold inner
        rw [if_pos e, if_neg (by simp)]
      · have e' : (ob.id == s.id) = false := by simp [e]
        rw [if_neg (by simp [e'])]
        unfold inner
        rw [if_neg e, if_neg e]
        have : (ob.id ∈ Q₁ ++ [w] ∧ ob.task.isSome = true) ↔ (ob.id ∈ Q₁ ∧ ob.task.isSome = true) := by
          simp [hobw]
        simp only [this]
  | some obw =>
      have hobw : obw ∈ d.objects := List.mem_of_find?_eq_some hfw
      have hobwid : obw.id = w := by simpa using List.find?_some hfw
      have hobws : obw.id ≠ s.id := hobwid ▸ hws
      have hf₁w : (if (w == s.id) = true then stageC now P s Q₂ else inner now P s Q₁ (w :: Q₂) obw) =
          stage now P obw := by
        rw [if_neg (by simp [hws])]
        unfold inner
        rw [if_neg hobws, if_neg (fun h => hwQ₁ (hobwid ▸ h.1))]
      have hg : (⟨d.objects.map fun ob => if ob.id == s.id then stageC now P s Q₂
          else inner now P s Q₁ (w :: Q₂) ob⟩ : Origin).get w now = some (stageP now P obw) := by
        rw [get_eq]
        show ((d.objects.map _).find? (fun x : Object => x.id == w)).map _ = _
        have hfind := find?_map_self hf₁ hnd hobw
        rw [hobwid] at hfind
        rw [hfind, Option.map_some, hf₁w, stage_project]
      rw [hg, Option.bind_some]
      cases ht : obw.task with
      | none =>
          rw [stageP_task_none ht, Option.map_none]
          apply Origin.eq_of_objects
          apply List.map_congr_left
          intro ob hob
          by_cases e : ob.id = s.id
          · have e' : (ob.id == s.id) = true := by simp [e]
            rw [if_pos e']
            unfold inner
            rw [if_pos e, if_neg (by simp)]
          · have e' : (ob.id == s.id) = false := by simp [e]
            rw [if_neg (by simp [e'])]
            unfold inner
            rw [if_neg e, if_neg e]
            by_cases ew : ob.id = w
            · have : ob = obw := eq_of_id_nodup hnd hob hobw (ew.trans hobwid.symm)
              subst this
              rw [if_neg (fun h => by simp [ht] at h), if_neg (fun h => by simp [ht] at h)]
            · have : (ob.id ∈ Q₁ ++ [w] ∧ ob.task.isSome = true) ↔ (ob.id ∈ Q₁ ∧ ob.task.isSome = true) := by
                simp [ew]
              simp only [this]
      | some t =>
          rw [stageP_task_some ht, Option.map_some]
          simp only
          have hxid : ∀ t' : TaskObject, ({ stageP now P obw with task := some t' } : Object).id = w :=
            fun _ => hobwid
          rw [set_map hf₁ ⟨obw, hobw, hobwid.trans (hxid _).symm⟩]
          apply Origin.eq_of_objects
          apply List.map_congr_left
          intro ob hob
          by_cases ew : ob.id = w
          · have : ob = obw := eq_of_id_nodup hnd hob hobw (ew.trans hobwid.symm)
            subst this
            rw [if_pos (by show (ob.id == _) = true; simp [stageP_id])]
            unfold inner
            rw [if_neg hobws, if_pos ⟨by simp [hobwid], by simp [ht]⟩, stageP_task_some ht, Option.map_some]
          · rw [if_neg (by show ¬ ((ob.id == _) = true); simp [stageP_id, hobwid, ew])]
            by_cases e : ob.id = s.id
            · have e' : (ob.id == s.id) = true := by simp [e]
              rw [if_pos e']
              unfold inner
              rw [if_pos e, if_neg (by simp)]
            · have e' : (ob.id == s.id) = false := by simp [e]
              rw [if_neg (by simp [e'])]
              unfold inner
              rw [if_neg e, if_neg e]
              have : (ob.id ∈ Q₁ ++ [w] ∧ ob.task.isSome = true) ↔ (ob.id ∈ Q₁ ∧ ob.task.isSome = true) := by
                simp [ew]
              simp only [this]

theorem inner_fold {now : Nat} {d : Origin} (hnd : (d.objects.map (·.id)).Nodup) {P : List Object} {s : Object}
    (hs : s ∈ d.objects) (hsP : s.id ∉ P.map (·.id))
    {L : List Ident} (hL : (s.project now).promise.callbacks = L) (hLnd : L.Nodup) (hsL : s.id ∉ L) :
    ∀ (Q₁ Q₂ : List Ident) (c : Commands), L = Q₁ ++ Q₂ →
      c.org = ⟨d.objects.map (inner now P s Q₁ Q₂)⟩ →
      (Q₂.foldl (cbStepOld now s.id) c).org = ⟨d.objects.map (inner now P s L [])⟩
  | Q₁, [], c, hsplit, hc => by
      rw [List.foldl_nil, hc]
      rw [List.append_nil] at hsplit
      rw [hsplit]
  | Q₁, w :: Q₂, c, hsplit, hc => by
      rw [List.foldl_cons]
      exact inner_fold hnd hs hsP hL hLnd hsL (Q₁ ++ [w]) Q₂ _ (by simpa using hsplit)
        (inner_step hnd hs hsP hL hLnd hsL Q₁ Q₂ w c hsplit hc)

theorem inner_end_self {now : Nat} {P : List Object} {s : Object} (hsP : s.id ∉ P.map (·.id))
    (hset : ((s.project now).promise.state != .pending) = true)
    {L : List Ident} (hL : (s.project now).promise.callbacks = L) (hLne : L ≠ []) (hsL : s.id ∉ L) :
    inner now P s L [] s = stage now (P ++ [s]) s := by
  have hcb : (!(s.project now).promise.callbacks.isEmpty) = true := by
    rw [hL]; cases L with
    | nil => exact absurd rfl hLne
    | cons a l => rfl
  have hstruck : struckP now (P ++ [s]) s := ⟨by simp, hset, hcb⟩
  have hns : ¬ struckP now P s := fun h => hsP h.1
  have haw : Concrete.awaiting now (P ++ [s]) s.id = Concrete.awaiting now P s.id := by
    rw [awaiting_append, awaiting_single_none now s s.id (fun _ => by
      rw [hL]; exact Bool.eq_false_iff.2 (fun h => hsL (List.contains_iff_mem.1 h))), List.append_nil]
  unfold inner
  rw [if_pos rfl, if_neg hLne]
  unfold stage
  rw [if_pos (show hit now (P ++ [s]) s from Or.inl hstruck)]
  apply Object.ext'
  · rfl
  · show ({ (stageP now P s).promise with callbacks := [] } : PromiseObject) =
      (if struckP now (P ++ [s]) s then { (s.project now).promise with callbacks := [] } else (s.project now).promise)
    rw [if_pos hstruck, stageP_promise_unstruck hsP]
  · show (stageP now P s).task = (s.project now).task.map _
    show (s.project now).task.map _ = (s.project now).task.map _
    rw [haw]

theorem inner_end {now : Nat} {d : Origin} (hnd : (d.objects.map (·.id)).Nodup) {P : List Object} {s : Object}
    (hs : s ∈ d.objects) (hsP : s.id ∉ P.map (·.id)) (hset : ((s.project now).promise.state != .pending) = true)
    {L : List Ident} (hL : (s.project now).promise.callbacks = L) (hLne : L ≠ []) (hsL : s.id ∉ L)
    {ob : Object} (hob : ob ∈ d.objects) :
    inner now P s L [] ob = stage now (P ++ [s]) ob := by
  by_cases e : ob.id = s.id
  · rw [eq_of_id_nodup hnd hob hs e]
    exact inner_end_self hsP hset hL hLne hsL
  · have hs_single : Concrete.awaiting now [s] ob.id = if ob.id ∈ L then [s.id] else [] := by
      rw [awaiting_single]
      by_cases hm : ob.id ∈ L
      · rw [if_pos ⟨hset, by rw [hL]; exact List.contains_iff_mem.2 hm⟩, if_pos hm]; rfl
      · rw [if_neg (fun h => hm (by rw [← hL]; exact List.contains_iff_mem.1 h.2)), if_neg hm]
    have hstruck := struckP_append_ne (now := now) (P := P) e
    unfold inner
    rw [if_neg e]
    by_cases hm : ob.id ∈ L ∧ ob.task.isSome = true
    · rw [if_pos hm]
      obtain ⟨t, ht⟩ : ∃ t, ob.task = some t := Option.isSome_iff_exists.1 hm.2
      have haw : Concrete.awaiting now (P ++ [s]) ob.id = Concrete.awaiting now P ob.id ++ [s.id] := by
        rw [awaiting_append, hs_single, if_pos hm.1]
      have hhit : hit now (P ++ [s]) ob := Or.inr ⟨by simp [Object.project, ht], by simp [haw]⟩
      unfold stage
      rw [if_pos hhit]
      apply Object.ext'
      · rfl
      · show (stageP now P ob).promise = (stageP now (P ++ [s]) ob).promise
        show (if struckP now P ob then _ else _) = (if struckP now (P ++ [s]) ob then _ else _)
        simp only [hstruck]
      · show ((stageP now P ob).task).map _ = (stageP now (P ++ [s]) ob).task
        rw [stageP_task_some ht, stageP_task_some ht, Option.map_some, haw, List.foldl_append,
          List.foldl_cons, List.foldl_nil]
    · rw [if_neg hm]
      have haw : Concrete.awaiting now [s] ob.id = [] ∨ ob.task = none := by
        by_cases hmL : ob.id ∈ L
        · right
          cases h : ob.task with
          | none => rfl
          | some t => exact absurd ⟨hmL, by simp [h]⟩ hm
        · left; rw [hs_single, if_neg hmL]
      have hsp := stageP_append_congr hstruck haw
      have hh : hit now (P ++ [s]) ob ↔ hit now P ob := by
        unfold hit
        rw [hstruck, awaiting_append]
        rcases haw with haw | haw
        · rw [haw, List.append_nil]
        · have hns : (ob.project now).task.isSome = false := by simp [Object.project, haw]
          simp only [hns, Bool.false_eq_true, false_and, or_false]
      unfold stage
      rw [hsp]
      exact ite_congr (propext hh.symm) (fun _ => rfl) (fun _ => rfl)

theorem chain_callbacks_step {now : Nat} {d : Origin} (hnd : (d.objects.map (·.id)).Nodup) (hwf : WF d)
    {P Q : List Object} {s : Object} (hd : d.objects = P ++ s :: Q) {c : Commands}
    (hc : c.org = ⟨d.objects.map (stage now P)⟩) :
    (cbOuterOld now c s).org = ⟨d.objects.map (stage now (P ++ [s]))⟩ := by
  have hs : s ∈ d.objects := by rw [hd]; simp
  have hsP : s.id ∉ P.map (·.id) := by
    intro hm
    have hnd' := hnd
    rw [hd, List.map_append, List.nodup_append] at hnd'
    exact hnd'.2.2 s.id hm s.id (by simp) rfl
  obtain ⟨_, hcbnd, hwfs⟩ := hwf s hs
  have hsL : s.id ∉ (s.project now).promise.callbacks := by
    show s.id ∉ (s.promise.project now).callbacks
    rw [project_callbacks]
    intro hm
    exact (hwfs s.id hm).1 rfl
  have hLnd : (s.project now).promise.callbacks.Nodup := by
    show (s.promise.project now).callbacks.Nodup
    rw [project_callbacks]; exact hcbnd
  unfold cbOuterOld
  simp only [project_id]
  by_cases hset : ((s.project now).promise.state != PromiseState.pending) = true
  · rw [if_pos hset]
    cases hLe : (s.project now).promise.callbacks with
    | nil =>
        rw [List.foldl_nil, hc]
        apply Origin.eq_of_objects
        apply List.map_congr_left
        intro ob hob
        rw [stage_append_inert now P s ob
          (fun id => awaiting_single_none now s id (fun _ => by rw [hLe]; rfl))
          (fun h => by have := h.2.2; rw [hLe] at this; simp at this)
          (fun e => eq_of_id_nodup hnd hob hs e)]
    | cons w L' =>
        have hfold := inner_fold hnd hs hsP hLe (hLe ▸ hLnd) (hLe ▸ hsL) [] (w :: L') c rfl
          (by rw [hc]; apply Origin.eq_of_objects; apply List.map_congr_left
              intro ob hob; exact (inner_start hnd hs (w :: L') hob).symm)
        rw [hfold]
        apply Origin.eq_of_objects
        apply List.map_congr_left
        intro ob hob
        exact inner_end hnd hs hsP hset hLe (List.cons_ne_nil w L') (hLe ▸ hsL) hob
  · rw [if_neg hset, hc]
    apply Origin.eq_of_objects
    apply List.map_congr_left
    intro ob hob
    rw [stage_append_inert now P s ob
      (fun id => awaiting_single_none now s id (fun h => absurd h hset))
      (fun h => hset h.2.1) (fun e => eq_of_id_nodup hnd hob hs e)]

theorem stage_nil (now : Nat) (ob : Object) : stage now [] ob = ob := by
  unfold stage hit struckP
  simp [Concrete.awaiting]

theorem chain_callbacks_put (now : Nat) (d : Origin) (hnd : (d.objects.map (·.id)).Nodup) (hwf : WF d) :
    ∀ (P Q : List Object) (c : Commands), d.objects = P ++ Q →
      c.org = ⟨d.objects.map (stage now P)⟩ →
      (Q.foldl (cbOuterOld now) c).org = ⟨d.objects.map (stage now (P ++ Q))⟩
  | P, [], c, _, hc => by rw [List.foldl_nil, List.append_nil]; exact hc
  | P, s :: Q, c, hd, hc => by
      rw [List.foldl_cons]
      have hstep := chain_callbacks_step hnd hwf hd hc
      have := chain_callbacks_put now d hnd hwf (P ++ [s]) Q _
        (by rw [hd, List.append_assoc, List.singleton_append]) hstep
      rwa [List.append_assoc, List.singleton_append] at this

theorem callbacks_put (now : Nat) (d : Origin) (hnd : (d.objects.map (·.id)).Nodup) (hwf : WF d) :
    (Chain.callbacks now d).org = ⟨d.objects.map fun ob => (Concrete.callback now d ob).getD ob⟩ := by
  rw [callbacks_eq]
  have h0 : ({ org := d } : Commands).org = ⟨d.objects.map (stage now [])⟩ := by
    show d = _
    apply Origin.eq_of_objects
    show d.objects = d.objects.map (stage now [])
    conv => lhs; rw [← List.map_id d.objects]
    apply List.map_congr_left
    intro ob _
    exact (stage_nil now ob).symm
  have := chain_callbacks_put now d hnd hwf [] d.objects { org := d } rfl h0
  rw [this, List.nil_append]
  apply Origin.eq_of_objects
  apply List.map_congr_left
  intro ob hob
  exact stage_full hob

theorem inner_send (now : Nat) (id : Ident) : ∀ (L : List Ident) (c : Commands),
    (L.foldl (cbStepOld now id) c).send = c.send
  | [], _ => rfl
  | w :: L, c => by rw [List.foldl_cons, inner_send now id L, cbStepOld_send]

theorem callbacks_send (now : Nat) (d : Origin) : (Chain.callbacks now d).send = [] := by
  rw [callbacks_eq]
  have : ∀ (Q : List Object) (c : Commands), (Q.foldl (cbOuterOld now) c).send = c.send := by
    intro Q
    induction Q with
    | nil => intro c; rfl
    | cons s Q ih =>
        intro c
        rw [List.foldl_cons, ih]
        unfold cbOuterOld
        simp only
        split
        · exact inner_send ..
        · rfl
  exact this d.objects { org := d }

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
      rw [List.filterMap_cons, List.filterMap_cons, h a (List.mem_cons_self ..),
        filterMap_congr' l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem awaiting_map (now : Nat) (l : List Object) (g : Object → Object)
    (hg : ∀ s, ((g s).project now).promise.state = (s.project now).promise.state ∧
      ((g s).project now).promise.callbacks = (s.project now).promise.callbacks ∧ (g s).id = s.id) (id : Ident) :
    Concrete.awaiting now (l.map g) id = Concrete.awaiting now l id := by
  unfold Concrete.awaiting
  rw [List.filterMap_map]
  apply filterMap_congr'
  intro s _
  obtain ⟨h1, h2, h3⟩ := hg s
  simp only [Function.comp, project_id, h1, h2, h3]

theorem callback_congr {now : Nat} {d org : Origin}
    (h : ∀ id, Concrete.awaiting now d.objects id = Concrete.awaiting now org.objects id) (x : Object) :
    Concrete.callback now d x = Concrete.callback now org x := by
  simp only [Concrete.callback, h]

def g1 (now : Nat) (o : Object) : Object := (Concrete.promiseTimeout now o).getD o
def g2 (now : Nat) (o : Object) : Object := (listenerObj now o).getD o
def g3 (now : Nat) (org : Origin) (o : Object) : Object := (Concrete.callback now org o).getD o
def g4 (now : Nat) (o : Object) : Object := (Concrete.leaseTimeout now o).getD o
def g5 (now : Nat) (o : Object) : Object := (retryObj now o).getD o

theorem g1_id (now : Nat) (o : Object) : (g1 now o).id = o.id := by
  unfold g1 Concrete.promiseTimeout; split <;> rfl

theorem g1_project (now : Nat) (o : Object) : (g1 now o).project now = o.project now := by
  unfold g1 Concrete.promiseTimeout
  split
  · exact Object.project_idem o now
  · rfl

theorem g1_lists (now : Nat) (o : Object) :
    (g1 now o).promise.callbacks = o.promise.callbacks ∧ (g1 now o).promise.listeners = o.promise.listeners := by
  unfold g1 Concrete.promiseTimeout
  split
  · exact ⟨project_callbacks _ _, project_listeners _ _⟩
  · exact ⟨rfl, rfl⟩

theorem g2_id (now : Nat) (o : Object) : (g2 now o).id = o.id := by
  simp only [g2, listenerObj, Concrete.listener]; split <;> rfl

theorem g2_project (now : Nat) (o : Object) :
    (g2 now o).project now = { o.project now with promise := { (o.project now).promise with
      listeners := (g2 now o).promise.listeners } } := by
  simp only [g2, listenerObj, Concrete.listener]
  split
  · simp only [Option.map_some, Option.getD_some]
    rw [Object.project_set_listeners, Object.project_idem]
  · simp only [Option.map_none, Option.getD_none]
    refine Object.ext' rfl ?_ rfl
    show o.promise.project now = { o.promise.project now with listeners := o.promise.listeners }
    rw [← project_listeners o.promise now]

theorem g2_lists (now : Nat) (o : Object) :
    (g2 now o).promise.callbacks = o.promise.callbacks ∧ (g2 now o).promise.listeners <+ o.promise.listeners := by
  simp only [g2, listenerObj, Concrete.listener]
  split
  · simp only [Option.map_some, Option.getD_some]
    exact ⟨project_callbacks _ _, List.nil_sublist _⟩
  · exact ⟨rfl, List.Sublist.refl _⟩

theorem g21_awaiting (now : Nat) (l : List Object) (id : Ident) :
    Concrete.awaiting now (l.map fun o => g2 now (g1 now o)) id = Concrete.awaiting now l id := by
  apply awaiting_map
  intro s
  rw [g2_project, g1_project]
  exact ⟨rfl, rfl, by rw [g2_id, g1_id]⟩

theorem g3_id (now : Nat) (org : Origin) (o : Object) : (g3 now org o).id = o.id := by
  simp only [g3, Concrete.callback]; split <;> rfl

theorem g4_id (now : Nat) (o : Object) : (g4 now o).id = o.id := by
  simp only [g4, Concrete.leaseTimeout]; split <;> (try split) <;> rfl

theorem WF_map {l : List Object} (hwf : WF ⟨l⟩) (g : Object → Object) (hid : ∀ o, (g o).id = o.id)
    (hcb : ∀ o, (g o).promise.callbacks <+ o.promise.callbacks)
    (hls : ∀ o, (g o).promise.listeners <+ o.promise.listeners) : WF ⟨l.map g⟩ := by
  intro ob hob
  simp only [List.mem_map] at hob
  obtain ⟨o, ho, rfl⟩ := hob
  obtain ⟨h1, h2, h3⟩ := hwf o ho
  refine ⟨h1.sublist (hls o), h2.sublist (hcb o), fun w hw => ?_⟩
  rw [hid]
  exact h3 w ((hcb o).subset hw)

theorem getD_pair {α β : Type} (x : Option (α × β)) (a : α) (b : β) :
    x.getD (a, b) = ((x.map (·.1)).getD a, (x.map (·.2)).getD b) := by
  cases x <;> rfl

theorem sweepObject_eq (now : Nat) (org : Origin) (o : Object) :
    Concrete.sweepObject now org o =
      { obj := g5 now (g4 now (g3 now org (g2 now (g1 now o)))),
        unblocks := listenerMsgs now (g1 now o),
        executes := retryMsgs now (g4 now (g3 now org (g2 now (g1 now o)))) } := by
  simp only [Concrete.sweepObject, getD_pair]
  rfl

theorem flatMap_map' {α β γ : Type} (l : List α) (f : α → β) (g : β → List γ) :
    (l.map f).flatMap g = l.flatMap (fun a => g (f a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem chain_sweep_eq (now : Nat) (org : Origin) (hnd : (org.objects.map (·.id)).Nodup) (hwf : WF org) :
    (Chain.sweep now org).org = (Concrete.sweep now org).org ∧
    (Chain.sweep now org).send = (Concrete.sweep now org).send := by
  have hwf' : WF ⟨org.objects⟩ := hwf
  have hc1 : (Chain.promiseTimeouts now org).org = ⟨org.objects.map (g1 now)⟩ := promiseTimeouts_put now org hnd
  have hnd1 : ((Chain.promiseTimeouts now org).org.objects.map (·.id)).Nodup := by
    rw [hc1]; show ((org.objects.map (g1 now)).map (fun x : Object => x.id)).Nodup; rw [ids_map (g1_id now)]; exact hnd
  have hc2 : (Chain.listeners now (Chain.promiseTimeouts now org).org).org =
      ⟨org.objects.map fun o => g2 now (g1 now o)⟩ := by
    rw [listeners_put _ _ hnd1, hc1]
    apply Origin.eq_of_objects
    show (org.objects.map (g1 now)).map _ = _
    rw [List.map_map]; rfl
  have hnd2 : ((Chain.listeners now (Chain.promiseTimeouts now org).org).org.objects.map (·.id)).Nodup := by
    rw [hc2]; show ((org.objects.map _).map (fun x : Object => x.id)).Nodup
    rw [ids_map (fun o => by rw [g2_id, g1_id])]; exact hnd
  have hwf2 : WF (Chain.listeners now (Chain.promiseTimeouts now org).org).org := by
    rw [hc2]
    exact WF_map hwf' _ (fun o => by rw [g2_id, g1_id])
      (fun o => by rw [(g2_lists now _).1, (g1_lists now o).1]; exact List.Sublist.refl _)
      (fun o => by rw [← (g1_lists now o).2]; exact (g2_lists now _).2)
  have hc3 : (Chain.callbacks now (Chain.listeners now (Chain.promiseTimeouts now org).org).org).org =
      ⟨org.objects.map fun o => g3 now org (g2 now (g1 now o))⟩ := by
    rw [callbacks_put _ _ hnd2 hwf2]
    apply Origin.eq_of_objects
    show (Chain.listeners now (Chain.promiseTimeouts now org).org).org.objects.map _ = _
    have hcong := callback_congr (now := now) (d := ⟨org.objects.map fun o => g2 now (g1 now o)⟩) (org := org)
      (fun id => g21_awaiting now org.objects id)
    rw [hc2]
    show (org.objects.map _).map _ = _
    rw [List.map_map]
    apply List.map_congr_left
    intro o _
    show (Concrete.callback now _ (g2 now (g1 now o))).getD _ = g3 now org _
    rw [hcong]
    rfl
  have hnd3 : ((Chain.callbacks now (Chain.listeners now (Chain.promiseTimeouts now org).org).org).org.objects.map (·.id)).Nodup := by
    rw [hc3]; show ((org.objects.map _).map (fun x : Object => x.id)).Nodup
    rw [ids_map (fun o => by rw [g3_id, g2_id, g1_id])]; exact hnd
  have hc4 : (Chain.leaseTimeouts now (Chain.callbacks now (Chain.listeners now (Chain.promiseTimeouts now org).org).org).org).org =
      ⟨org.objects.map fun o => g4 now (g3 now org (g2 now (g1 now o)))⟩ := by
    rw [leaseTimeouts_put _ _ hnd3, hc3]
    apply Origin.eq_of_objects
    show (org.objects.map _).map _ = _
    rw [List.map_map]; rfl
  have hnd4 : ((Chain.leaseTimeouts now (Chain.callbacks now (Chain.listeners now (Chain.promiseTimeouts now org).org).org).org).org.objects.map (·.id)).Nodup := by
    rw [hc4]; show ((org.objects.map _).map (fun x : Object => x.id)).Nodup
    rw [ids_map (fun o => by rw [g4_id, g3_id, g2_id, g1_id])]; exact hnd
  have hc5 : (Chain.retryTimeouts now (Chain.leaseTimeouts now (Chain.callbacks now (Chain.listeners now (Chain.promiseTimeouts now org).org).org).org).org).org =
      ⟨org.objects.map fun o => g5 now (g4 now (g3 now org (g2 now (g1 now o))))⟩ := by
    rw [retryTimeouts_put _ _ hnd4, hc4]
    apply Origin.eq_of_objects
    show (org.objects.map _).map _ = _
    rw [List.map_map]; rfl
  constructor
  · show (Chain.retryTimeouts now (Chain.leaseTimeouts now (Chain.callbacks now (Chain.listeners now (Chain.promiseTimeouts now org).org).org).org).org).org = _
    rw [hc5]
    show _ = (⟨(org.objects.map (Concrete.sweepObject now org)).map (fun ch : Concrete.Change => ch.obj)⟩ : Origin)
    apply Origin.eq_of_objects
    show _ = (org.objects.map (Concrete.sweepObject now org)).map (fun ch : Concrete.Change => ch.obj)
    rw [List.map_map]
    apply List.map_congr_left
    intro o _
    show _ = (Concrete.sweepObject now org o).obj
    rw [sweepObject_eq]
  · show (Chain.promiseTimeouts now org).send ++ (Chain.listeners now (Chain.promiseTimeouts now org).org).send ++
        (Chain.callbacks now (Chain.listeners now (Chain.promiseTimeouts now org).org).org).send ++
        (Chain.leaseTimeouts now (Chain.callbacks now (Chain.listeners now (Chain.promiseTimeouts now org).org).org).org).send ++
        (Chain.retryTimeouts now (Chain.leaseTimeouts now (Chain.callbacks now (Chain.listeners now (Chain.promiseTimeouts now org).org).org).org).org).send =
      (org.objects.map (Concrete.sweepObject now org)).flatMap (·.unblocks) ++
        (org.objects.map (Concrete.sweepObject now org)).flatMap (·.executes)
    rw [promiseTimeouts_send, listeners_send, callbacks_send, leaseTimeouts_send, retryTimeouts_send, hc4, hc1]
    simp only [List.nil_append, List.append_nil, flatMap_map', sweepObject_eq]

theorem SwInv.transfer {o : String} {S : Abstract.State} {c : Commands} {T : Abstract.State}
    (h : SwInv o S c T) {c' : Commands} (hp : c'.org = c.org) (hs : c'.send = c.send) : SwInv o S c' T :=
  ⟨hp ▸ h.loc, hs ▸ h.out, h.sch, hp ▸ h.orig, hp ▸ h.nodup, hp ▸ h.wf, h.other⟩

theorem sweep_sim {o : String} {org : Origin} {S : Abstract.State} (hL : Local o org S)
    (horig : ∀ ob ∈ org.objects, ob.id.origin = o) (hnodup : (org.objects.map (·.id)).Nodup)
    (hwf : WF org) (now : Nat) :
    SwInv o S (Concrete.sweep now org) (execI (Chain.sweepTriggers now org) now S) :=
  (chain_sweep_sim hL horig hnodup hwf now).transfer (chain_sweep_eq now org hnodup hwf).1.symm
    (chain_sweep_eq now org hnodup hwf).2.symm

end Refinement
