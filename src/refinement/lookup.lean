import refinement.relation

namespace Refinement

open Protocol (Ident Message OutboxEntry Object PromiseObject TaskObject PromiseState TaskState)
open Concrete (Origin Commands)

theorem bind_apply {α β : Type} (x : Abstract.H α) (f : α → Abstract.H β) (e : Abstract.Env) :
    (x >>= f) e = ((f (x e).1 e).1, (x e).2 ++ (f (x e).1 e).2) := rfl

theorem pure_apply {α : Type} (a : α) (e : Abstract.Env) : (pure a : Abstract.H α) e = (a, []) := rfl

theorem map_apply {α β : Type} (g : α → β) (x : Abstract.H α) (e : Abstract.Env) :
    (g <$> x) e = (g (x e).1, (x e).2) := by
  show (x >>= fun a => pure (g a)) e = _
  simp [bind_apply, pure_apply]

theorem ask_apply (e : Abstract.Env) : Abstract.ask e = (e, []) := rfl

theorem setPromise_apply (id : Ident) (p : PromiseObject) (e : Abstract.Env) :
    Abstract.setPromise id p e = ((), [.setPromise id p]) := rfl

theorem setTask_apply (id : Ident) (t : TaskObject) (e : Abstract.Env) :
    Abstract.setTask id t e = ((), [.setTask id t]) := rfl

theorem setMessage_apply (a : String) (m : Message) (e : Abstract.Env) :
    Abstract.setMessage a m e = ((), [.setMessage a m]) := rfl

def env (S : Abstract.State) : Abstract.Env := { state := S, mat := false }

def find (S : Abstract.State) (id : Ident) : Option Object :=
  S.objects.find? (·.id == id)

def Origin.find (org : Origin) (id : Ident) : Option Object :=
  org.current.objects.find? (·.id == id)

theorem find_id {S : Abstract.State} {id : Ident} {o : Object} (h : find S id = some o) : o.id = id := by
  have := List.find?_some h
  simpa using this


theorem get_eq (org : Origin) (id : Ident) (now : Nat) :
    org.get id now = (Origin.find org id).map (·.project now) := rfl

theorem getObject_apply (id : Ident) (S : Abstract.State) :
    Abstract.getObject id (env S) = (find S id, []) := rfl

theorem getObject_apply_mat (id : Ident) (S : Abstract.State) :
    Abstract.getObject id { env S with mat := true } = (find S id, []) := rfl

theorem readObject_false (id : Ident) (now : Nat) (S : Abstract.State) :
    Abstract.readObject id now (env S) = ((find S id).map (·.project now), []) := by
  unfold Abstract.readObject
  simp only [bind_apply, getObject_apply]
  cases h : find S id with
  | none => rfl
  | some o => rfl

theorem readTaskObject_false (id : Ident) (now : Nat) (S : Abstract.State) :
    Abstract.readTaskObject id now (env S) =
      ((find S id).bind fun o => if o.task.isSome then some (o.project now) else none, []) := by
  unfold Abstract.readTaskObject
  simp only [bind_apply, getObject_apply]
  cases h : find S id with
  | none => rfl
  | some o =>
      dsimp only
      by_cases ht : o.task.isSome = true
      · simp only [ht, ↓reduceIte, readObject_false, h]
        simp [ht]
      · simp only [ht, Bool.false_eq_true, ↓reduceIte, pure_apply]
        simp [ht]

def materialiseFx (id : Ident) (o o' : Object) : List Abstract.Effect :=
  (if o'.promise.state != o.promise.state then [.setPromise id o'.promise] else [])
  ++ (match o.task, o'.task with
      | some t, some u => if u.state != t.state then [.setTask id u] else []
      | _, _ => [])

theorem materialise_apply (id : Ident) (o o' : Object) (e : Abstract.Env) :
    Abstract.materialise id o o' e = ((), materialiseFx id o o') := by
  unfold Abstract.materialise materialiseFx
  simp only [bind_apply]
  rcases o.task with _ | t <;> rcases o'.task with _ | u <;> dsimp only <;>
    split <;> (try split) <;> simp [pure_apply, setPromise_apply, setTask_apply]

theorem touchObject_apply (id : Ident) (now : Nat) (S : Abstract.State) :
    Abstract.touchObject id now (env S) =
      match find S id with
      | none => (none, [])
      | some o => (some (o.project now), materialiseFx id o (o.project now)) := by
  unfold Abstract.touchObject Abstract.withMat Abstract.readObject
  simp only [bind_apply, getObject_apply_mat]
  cases h : find S id with
  | none => rfl
  | some o =>
      simp [bind_apply, ask_apply, materialise_apply, pure_apply]

theorem touchTaskObject_apply (id : Ident) (now : Nat) (S : Abstract.State) :
    Abstract.touchTaskObject id now (env S) =
      match find S id with
      | none => (none, [])
      | some o =>
          if o.task.isSome then (some (o.project now), materialiseFx id o (o.project now))
          else (none, []) := by
  unfold Abstract.touchTaskObject Abstract.withMat Abstract.readTaskObject
  simp only [bind_apply, getObject_apply_mat]
  cases h : find S id with
  | none => rfl
  | some o =>
      dsimp only
      by_cases ht : o.task.isSome = true
      · simp only [ht, ↓reduceIte]
        unfold Abstract.readObject
        simp [bind_apply, getObject_apply_mat, h, ask_apply, materialise_apply, pure_apply]
      · simp only [ht, Bool.false_eq_true, ↓reduceIte, pure_apply]
        simp

theorem viewTaskObject_apply (id : Ident) (now : Nat) (S : Abstract.State) :
    Abstract.viewTaskObject id now (env S) =
      ((find S id).bind fun o => if o.task.isSome then some (o.project now) else none, []) := by
  unfold Abstract.viewTaskObject Abstract.withMat
  exact readTaskObject_false id now S

theorem run_eq {α : Type} (act : Abstract.H α) (S : Abstract.State) :
    Abstract.run false act S = ((act (env S)).1, Abstract.applyAll S (act (env S)).2) := rfl

theorem withPromise_id (S : Abstract.State) (id : Ident) (p : PromiseObject) :
    (Abstract.Object.withPromise id p (find S id)).id = id := by
  cases h : find S id with
  | none => rfl
  | some o => simpa [Abstract.Object.withPromise] using find_id h

theorem find_setPromise_same (S : Abstract.State) (id : Ident) (p : PromiseObject) :
    find ((Abstract.Effect.setPromise id p).apply S) id =
      some (Abstract.Object.withPromise id p (find S id)) := by
  have h1 : ((Abstract.Object.withPromise id p (find S id)).id == id) = true := by
    simp [withPromise_id]
  simp only [find] at h1 ⊢
  simp only [Abstract.Effect.apply, List.find?_cons, h1]

theorem find?_filter_ne (l : List Object) (id id' : Ident) (h : id' ≠ id) :
    (l.filter (·.id != id)).find? (·.id == id') = l.find? (·.id == id') := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x.id = id'
      · have h1 : (x.id == id') = true := by simpa using hx
        have h2 : (x.id != id) = true := by simpa [hx] using h
        simp [h1, h2]
      · have h1 : (x.id == id') = false := by simpa using hx
        by_cases hp : x.id = id
        · have h2 : (x.id != id) = false := by simpa using hp
          simp [h1, h2, ih]
        · have h2 : (x.id != id) = true := by simpa using hp
          simp [h1, h2, ih]

theorem find_setPromise_other (S : Abstract.State) (id id' : Ident) (p : PromiseObject)
    (h : id' ≠ id) :
    find ((Abstract.Effect.setPromise id p).apply S) id' = find S id' := by
  have h1 : ((Abstract.Object.withPromise id p (find S id)).id == id') = false := by
    rw [withPromise_id]
    simpa using Ne.symm h
  simp only [find] at h1 ⊢
  simp only [Abstract.Effect.apply, List.find?_cons, h1]
  exact find?_filter_ne _ _ _ h

theorem find?_map_id (f : Object → Object) (hf : ∀ o, (f o).id = o.id) (l : List Object) (id : Ident) :
    (l.map f).find? (·.id == id) = (l.find? (·.id == id)).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.find?_cons, hf]
      cases x.id == id <;> simp [ih]

theorem find_setTask (S : Abstract.State) (id id' : Ident) (t : TaskObject) :
    find ((Abstract.Effect.setTask id t).apply S) id' =
      if id' = id then (find S id').map (fun o => { o with task := some t }) else find S id' := by
  simp only [find, Abstract.Effect.apply]
  rw [find?_map_id _ (fun o => by split <;> rfl)]
  cases hf : S.objects.find? (·.id == id') with
  | none => simp
  | some o =>
      have ho : o.id = id' := by simpa using List.find?_some hf
      simp only [Option.map_some]
      by_cases e : id' = id
      · have : (o.id == id) = true := by simp [ho, e]
        simp [this, e]
      · have : (o.id == id) = false := by simp [ho, e]
        simp [this, e]

theorem find_setMessage (S : Abstract.State) (a : String) (m : Message) (id : Ident) :
    find ((Abstract.Effect.setMessage a m).apply S) id = find S id := rfl

def replace (objects : List Object) (o : Object) : List Object :=
  if objects.any (·.id == o.id) then objects.map fun x => if x.id == o.id then o else x else objects ++ [o]

theorem current_eq (org : Origin) : org.current = ⟨org.objects.foldl replace []⟩ := rfl

theorem current_set (org : Origin) (x : Object) : (org.set x).current = ⟨replace org.current.objects x⟩ := by
  show (⟨(org.objects ++ [x]).foldl replace []⟩ : Origin) = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem replace_present {l : List Object} {x : Object} (h : l.any (·.id == x.id) = true) :
    replace l x = l.map fun o => if o.id == x.id then x else o := by
  simp [replace, h]

theorem replace_absent {l : List Object} {x : Object} (h : l.any (·.id == x.id) = false) :
    replace l x = l ++ [x] := by
  simp [replace, h]

theorem replace_id (x o : Object) : (if o.id == x.id then x else o).id = o.id := by
  split
  · rename_i e; exact (beq_iff_eq.1 e).symm
  · rfl

theorem find?_replace_same (l : List Object) (x : Object) : (replace l x).find? (·.id == x.id) = some x := by
  by_cases h : l.any (·.id == x.id) = true
  · rw [replace_present h, find?_map_id _ (replace_id x)]
    obtain ⟨y, hy, hyx⟩ := List.any_eq_true.1 h
    cases hf : l.find? (·.id == x.id) with
    | none =>
        rw [List.find?_eq_none] at hf
        exact absurd hyx (hf y hy)
    | some z =>
        have hz : z.id = x.id := by simpa using List.find?_some hf
        simp [hz]
  · have h' := eq_false_of_ne_true h
    rw [replace_absent h', List.find?_append]
    have : l.find? (·.id == x.id) = none := by
      rw [List.find?_eq_none]
      intro a ha hp
      exact List.any_eq_false.1 h' a ha hp
    simp [this]

theorem find?_replace_other (l : List Object) (x : Object) (id : Ident) (h : id ≠ x.id) :
    (replace l x).find? (·.id == id) = l.find? (·.id == id) := by
  by_cases hp : l.any (·.id == x.id) = true
  · rw [replace_present hp, find?_map_id _ (replace_id x)]
    cases hf : l.find? (·.id == id) with
    | none => rfl
    | some y =>
        have hy : y.id = id := by simpa using List.find?_some hf
        have : y.id ≠ x.id := fun e => h (hy.symm.trans e)
        simp [this]
  · have hp' := eq_false_of_ne_true hp
    rw [replace_absent hp', List.find?_append]
    have : ([x].find? (·.id == id)) = none := by
      have : (x.id == id) = false := by simpa using Ne.symm h
      simp [this]
    rw [this, Option.or_none]

theorem find_set_same (org : Origin) (x : Object) :
    Origin.find (org.set x) x.id = some x := by
  unfold Origin.find
  rw [current_set]
  exact find?_replace_same _ _

theorem find_set_other (org : Origin) (x : Object) (id : Ident) (h : id ≠ x.id) :
    Origin.find (org.set x) id = Origin.find org id := by
  unfold Origin.find
  rw [current_set]
  exact find?_replace_other _ _ _ h

theorem mem_replace {l : List Object} {x ob : Object} (hob : ob ∈ replace l x) : ob = x ∨ ob ∈ l := by
  unfold replace at hob
  split at hob
  · simp only [List.mem_map] at hob
    obtain ⟨y, hy, rfl⟩ := hob
    split
    · exact Or.inl rfl
    · exact Or.inr hy
  · simp only [List.mem_append, List.mem_singleton] at hob
    rcases hob with hob | rfl
    · exact Or.inr hob
    · exact Or.inl rfl

theorem mem_set {org : Origin} {x ob : Object} (hob : ob ∈ (org.set x).current.objects) :
    ob = x ∨ ob ∈ org.current.objects := by
  rw [current_set] at hob
  exact mem_replace hob

theorem find_mem {org : Origin} {id : Ident} {o : Object} (h : Origin.find org id = some o) :
    o ∈ org.current.objects ∧ o.id = id := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

def Local (o : String) (org : Origin) (S : Abstract.State) : Prop :=
  ∀ id, id.origin = o → find S id = Origin.find org id

def Fx (o : String) : List Abstract.Effect → Prop
  | [] => True
  | .setPromise id _ :: fx => id.origin = o ∧ Fx o fx
  | .setTask id _ :: fx => id.origin = o ∧ Fx o fx
  | .setMessage _ _ :: fx => Fx o fx
  | .setSchedule _ :: _ => False
  | .delSchedule _ :: _ => False

theorem Fx_append (o : String) (a b : List Abstract.Effect) : Fx o (a ++ b) ↔ Fx o a ∧ Fx o b := by
  induction a with
  | nil => simp [Fx]
  | cons e es ih =>
      cases e <;> simp [Fx, ih, and_assoc]

def sendsOf : List Abstract.Effect → List (String × Message)
  | [] => []
  | .setMessage a m :: fx => (a, m) :: sendsOf fx
  | _ :: fx => sendsOf fx

theorem sendsOf_append (a b : List Abstract.Effect) : sendsOf (a ++ b) = sendsOf a ++ sendsOf b := by
  induction a with
  | nil => rfl
  | cons e es ih => cases e <;> simp [sendsOf, ih]

def sendsFold (ob : List OutboxEntry) : List (String × Message) → List OutboxEntry
  | [] => ob
  | (a, m) :: rest =>
      let entry := OutboxEntry.mk a m
      sendsFold (entry :: ob.filter (fun e => e.key != entry.key)) rest

theorem sendsFold_append (ob : List OutboxEntry) (a b : List (String × Message)) :
    sendsFold ob (a ++ b) = sendsFold (sendsFold ob a) b := by
  induction a generalizing ob with
  | nil => rfl
  | cons x xs ih => obtain ⟨a, m⟩ := x; simp [sendsFold, ih]

theorem applyAll_append (S : Abstract.State) (a b : List Abstract.Effect) :
    Abstract.applyAll S (a ++ b) = Abstract.applyAll (Abstract.applyAll S a) b := by
  induction a generalizing S with
  | nil => rfl
  | cons e es ih => simp [Abstract.applyAll, ih]

theorem applyAll_outbox (S : Abstract.State) (fx : List Abstract.Effect) :
    (Abstract.applyAll S fx).outbox = sendsFold S.outbox (sendsOf fx) := by
  induction fx generalizing S with
  | nil => rfl
  | cons e es ih =>
      cases e <;> simp [Abstract.applyAll, Abstract.Effect.apply, sendsOf, sendsFold, ih]

theorem applyAll_schedules {o : String} (S : Abstract.State) (fx : List Abstract.Effect) (h : Fx o fx) :
    (Abstract.applyAll S fx).schedules = S.schedules := by
  induction fx generalizing S with
  | nil => rfl
  | cons e es ih =>
      cases e with
      | setPromise i p => simp only [Abstract.applyAll]; rw [ih _ h.2]; rfl
      | setTask i t => simp only [Abstract.applyAll]; rw [ih _ h.2]; rfl
      | setMessage a m => simp only [Abstract.applyAll]; rw [ih _ h]; rfl
      | setSchedule c => simp [Fx] at h
      | delSchedule i => simp [Fx] at h

theorem applyAll_find_other {o : String} (S : Abstract.State) (fx : List Abstract.Effect) (h : Fx o fx)
    (id : Ident) (hid : id.origin ≠ o) :
    find (Abstract.applyAll S fx) id = find S id := by
  induction fx generalizing S with
  | nil => rfl
  | cons e es ih =>
      cases e with
      | setPromise i p =>
          obtain ⟨hi, hfx⟩ := h
          simp only [Abstract.applyAll]
          rw [ih _ hfx, find_setPromise_other _ _ _ _ (fun e => hid (by rw [e]; exact hi))]
      | setTask i t =>
          obtain ⟨hi, hfx⟩ := h
          simp only [Abstract.applyAll]
          rw [ih _ hfx, find_setTask, if_neg (fun e => hid (by rw [e]; exact hi))]
      | setMessage a m =>
          simp only [Abstract.applyAll]
          rw [ih _ h, find_setMessage]
      | setSchedule c => simp [Fx] at h
      | delSchedule i => simp [Fx] at h

theorem set_derived {o : String} {org : Origin} {x : Object}
    (h : ∀ ob ∈ org.current.objects, ob.id.origin = o) (hx : x.id.origin = o) :
    ∀ ob ∈ (org.set x).current.objects, ob.id.origin = o := by
  intro ob hob
  rcases mem_set hob with rfl | hob
  · exact hx
  · exact h ob hob

theorem nodup_append_single {α : Type} {l : List α} {w : α} (h : l.Nodup) (hw : w ∉ l) :
    (l ++ [w]).Nodup := by
  induction l with
  | nil => exact List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
  | cons x xs ih =>
      have h' := List.nodup_cons.1 h
      simp only [List.mem_cons, not_or] at hw
      refine List.nodup_cons.2 ⟨?_, ih h'.2 hw.2⟩
      intro hm
      rcases List.mem_append.1 hm with hm | hm
      · exact h'.1 hm
      · exact hw.1 (List.mem_singleton.1 hm).symm

theorem replace_ids {l : List Object} {x : Object} (h : l.any (·.id == x.id) = true) :
    (replace l x).map (·.id) = l.map (·.id) := by
  rw [replace_present h, List.map_map]
  congr 1
  funext o
  exact replace_id x o

theorem replace_nodup {l : List Object} {x : Object} (h : (l.map (·.id)).Nodup) :
    ((replace l x).map (·.id)).Nodup := by
  by_cases hp : l.any (·.id == x.id) = true
  · rw [replace_ids hp]; exact h
  · have hp' := eq_false_of_ne_true hp
    rw [replace_absent hp', List.map_append, List.map_singleton]
    apply nodup_append_single h
    intro hm
    simp only [List.mem_map] at hm
    obtain ⟨y, hy, hyx⟩ := hm
    exact List.any_eq_false.1 hp' y hy (by simp [hyx])

theorem foldl_replace_nodup : ∀ (l acc : List Object), (acc.map (·.id)).Nodup →
    ((l.foldl replace acc).map (·.id)).Nodup
  | [], _, h => h
  | _ :: l, _, h => foldl_replace_nodup l _ (replace_nodup h)

theorem current_nodup (org : Origin) : (org.current.objects.map (·.id)).Nodup :=
  foldl_replace_nodup org.objects [] List.nodup_nil

theorem mem_foldl_replace : ∀ (l acc : List Object) {ob : Object}, ob ∈ l.foldl replace acc →
    ob ∈ acc ∨ ob ∈ l
  | [], _, _, h => Or.inl h
  | o :: l, acc, ob, h => by
      rcases mem_foldl_replace l _ h with h1 | h1
      · rcases mem_replace h1 with rfl | h2
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl h2
      · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem mem_current {org : Origin} {ob : Object} (h : ob ∈ org.current.objects) : ob ∈ org.objects := by
  rcases mem_foldl_replace org.objects [] h with h | h
  · cases h
  · exact h

theorem foldl_replace_of_nodup : ∀ (l acc : List Object), ((acc ++ l).map (·.id)).Nodup →
    l.foldl replace acc = acc ++ l
  | [], acc, _ => by simp
  | o :: l, acc, h => by
      have hnot : acc.any (·.id == o.id) = false := by
        rw [List.map_append, List.map_cons, List.nodup_append] at h
        obtain ⟨_, _, hdis⟩ := h
        refine List.any_eq_false.2 fun a ha e => ?_
        have hae : a.id = o.id := beq_iff_eq.1 e
        have hm : o.id ∈ acc.map (·.id) := hae ▸ List.mem_map_of_mem ha
        exact hdis o.id hm o.id (List.mem_cons_self ..) rfl
      rw [List.foldl_cons, replace_absent hnot, foldl_replace_of_nodup l (acc ++ [o]) (by simpa using h)]
      simp

theorem current_of_nodup {org : Origin} (h : (org.objects.map (·.id)).Nodup) : org.current = org := by
  rw [current_eq, foldl_replace_of_nodup org.objects [] (by simpa using h)]
  rfl

theorem current_current (org : Origin) : org.current.current = org.current :=
  current_of_nodup (current_nodup org)

theorem find_current (org : Origin) (id : Ident) : Origin.find org.current id = Origin.find org id := by
  unfold Origin.find
  rw [current_current]

theorem current_append (l m : List Object) :
    (⟨l ++ m⟩ : Origin).current = ⟨m.foldl replace (⟨l⟩ : Origin).current.objects⟩ := by
  rw [current_eq, current_eq, List.foldl_append]

theorem current_append_current (org : Origin) (m : List Object) :
    (⟨org.current.objects ++ m⟩ : Origin).current = (⟨org.objects ++ m⟩ : Origin).current := by
  rw [current_append, current_append]
  congr 2
  exact congrArg Origin.objects (current_current org)

theorem add_nil (org : Origin) : org.add [] = org := by
  show (⟨org.objects ++ []⟩ : Origin) = org
  rw [List.append_nil]

theorem add_add (org : Origin) (a b : List Object) : (org.add a).add b = org.add (a ++ b) := by
  show (⟨(org.objects ++ a) ++ b⟩ : Origin) = ⟨org.objects ++ (a ++ b)⟩
  rw [List.append_assoc]

theorem add_snoc (org : Origin) (l : List Object) (x : Object) : org.add (l ++ [x]) = (org.add l).set x :=
  (add_add org l [x]).symm

theorem doc_empty (org : Origin) : ({} : Commands).doc org = org := add_nil org

def mask (x o : Object) : Object :=
  if o.id == x.id then x else o

theorem mask_id (x o : Object) : (mask x o).id = o.id := replace_id x o

theorem mask_self (x : Object) : mask x x = x := by
  simp [mask]

theorem ids_mask (x : Object) (l : List Object) : (l.map (mask x)).map (·.id) = l.map (·.id) := by
  rw [List.map_map]
  exact List.map_congr_left fun o _ => mask_id x o

theorem any_ids {l m : List Object} (h : l.map (·.id) = m.map (·.id)) (z : Ident) :
    l.any (·.id == z) = m.any (·.id == z) := by
  have h1 : l.any (·.id == z) = (l.map (·.id)).any (· == z) := by simp only [List.any_map, Function.comp_def]
  have h2 : m.any (·.id == z) = (m.map (·.id)).any (· == z) := by simp only [List.any_map, Function.comp_def]
  rw [h1, h2, h]

theorem mask_mask_same {x v : Object} (hv : v.id = x.id) (o : Object) : mask x (mask v o) = mask x o := by
  by_cases h : o.id = x.id <;> simp [mask, h, hv]

theorem mask_mask_ne {x z : Object} (h : z.id ≠ x.id) (o : Object) : mask x (mask z o) = mask z (mask x o) := by
  by_cases h1 : o.id = z.id
  · have h2 : o.id ≠ x.id := fun e => h (h1.symm.trans e)
    simp [mask, h1, h]
  · by_cases h2 : o.id = x.id
    · simp [mask, h2, Ne.symm h]
    · simp [mask, h1, h2]

theorem map_mask_of_not_mem {x : Object} {l : List Object} (h : x.id ∉ l.map (·.id)) : l.map (mask x) = l := by
  refine (List.map_congr_left fun o ho => ?_).trans (List.map_id l)
  have : o.id ≠ x.id := fun e => h (e ▸ List.mem_map_of_mem (f := (·.id)) ho)
  show mask x o = o
  simp [mask, this]

theorem any_of_mem_ids {l : List Object} {x : Object} (h : x.id ∈ l.map (·.id)) : l.any (·.id == x.id) = true := by
  obtain ⟨o, ho, e⟩ := List.mem_map.1 h
  exact List.any_eq_true.2 ⟨o, ho, by simp [e]⟩

theorem any_false_of_not_mem {l : List Object} {x : Object} (h : x.id ∉ l.map (·.id)) : l.any (·.id == x.id) = false := by
  rw [Bool.eq_false_iff]
  intro ha
  obtain ⟨o, ho, e⟩ := List.any_eq_true.1 ha
  exact h (List.mem_map.2 ⟨o, ho, beq_iff_eq.1 e⟩)

theorem mem_ids_replace_self (l : List Object) (x : Object) : x.id ∈ (replace l x).map (·.id) :=
  List.mem_map_of_mem (List.mem_of_find?_eq_some (find?_replace_same l x))

theorem replace_mask {x : Object} {a b : List Object} {z w : Object}
    (h : a.map (mask x) = b.map (mask x)) (hz : mask x z = mask x w) :
    (replace a z).map (mask x) = (replace b w).map (mask x) := by
  have hid : z.id = w.id := by rw [← mask_id x z, ← mask_id x w, hz]
  have hids : a.map (·.id) = b.map (·.id) := by rw [← ids_mask x a, ← ids_mask x b, h]
  show (if a.any (·.id == z.id) then a.map (mask z) else a ++ [z]).map (mask x) =
    (if b.any (·.id == w.id) then b.map (mask w) else b ++ [w]).map (mask x)
  rw [← hid, ← any_ids hids z.id]
  split
  · rw [List.map_map, List.map_map]
    by_cases hzx : z.id = x.id
    · have e : ∀ v : Object, v.id = x.id → mask x ∘ mask v = mask x := fun v hv => funext fun o => mask_mask_same hv o
      rw [e z hzx, e w (hid ▸ hzx), h]
    · have hwx : w.id ≠ x.id := fun e => hzx (hid.trans e)
      have hz' : mask x z = z := by simp [mask, hzx]
      have hw' : mask x w = w := by simp [mask, hwx]
      have hzw : z = w := by rw [← hz', hz, hw']
      subst hzw
      have e : mask x ∘ mask z = mask z ∘ mask x := funext fun o => mask_mask_ne hzx o
      rw [e, ← List.map_map, ← List.map_map, h]
  · rw [List.map_append, List.map_append, h, List.map_singleton, List.map_singleton, hz]

theorem foldl_mask {x : Object} : ∀ (l : List Object) {a b : List Object}, a.map (mask x) = b.map (mask x) →
    (l.foldl replace a).map (mask x) = (l.foldl replace b).map (mask x)
  | [], _, _, h => h
  | _ :: l, _, _, h => foldl_mask l (replace_mask h rfl)

theorem replace_of_mask {x : Object} {a b : List Object} (h : a.map (mask x) = b.map (mask x)) :
    replace a x = replace b x := by
  have hids : a.map (·.id) = b.map (·.id) := by rw [← ids_mask x a, ← ids_mask x b, h]
  show (if a.any (·.id == x.id) then a.map (mask x) else a ++ [x]) =
    (if b.any (·.id == x.id) then b.map (mask x) else b ++ [x])
  rw [← any_ids hids x.id]
  split
  · exact h
  · rename_i hn
    have ha : x.id ∉ a.map (·.id) := fun hm => hn (any_of_mem_ids hm)
    have hb : x.id ∉ b.map (·.id) := hids ▸ ha
    rw [map_mask_of_not_mem ha, map_mask_of_not_mem hb] at h
    rw [h]

theorem mask_replace (acc : List Object) (x : Object) : (replace acc x).map (mask x) = replace acc x := by
  by_cases hm : x.id ∈ acc.map (·.id)
  · rw [replace_present (any_of_mem_ids hm)]
    show (acc.map (mask x)).map (mask x) = acc.map (mask x)
    rw [List.map_map]
    refine List.map_congr_left fun o _ => ?_
    exact mask_mask_same rfl o
  · rw [replace_absent (any_false_of_not_mem hm), List.map_append, map_mask_of_not_mem hm, List.map_singleton,
      mask_self]

theorem mask_replace_ne {x z : Object} (h : z.id ≠ x.id) {l : List Object} (hl : l.map (mask x) = l) :
    (replace l z).map (mask x) = replace l z := by
  by_cases hm : z.id ∈ l.map (·.id)
  · rw [replace_present (any_of_mem_ids hm)]
    show (l.map (mask z)).map (mask x) = l.map (mask z)
    rw [List.map_map, show mask x ∘ mask z = mask z ∘ mask x from funext fun o => mask_mask_ne h o,
      ← List.map_map, hl]
  · rw [replace_absent (any_false_of_not_mem hm), List.map_append, hl, List.map_singleton]
    simp [mask, h]

theorem mem_ids_replace {l : List Object} {x z : Object} (h : x.id ∈ l.map (·.id)) :
    x.id ∈ (replace l z).map (·.id) := by
  show x.id ∈ (if l.any (·.id == z.id) then l.map (mask z) else l ++ [z]).map (·.id)
  split
  · rw [ids_mask]; exact h
  · rw [List.map_append]; exact List.mem_append_left _ h

theorem replace_self {l : List Object} {x : Object} (hl : l.map (mask x) = l) (hm : x.id ∈ l.map (·.id)) :
    replace l x = l := by
  rw [replace_present (any_of_mem_ids hm)]
  exact hl

theorem replace_foldl_self {x : Object} : ∀ (l : List Object) {acc : List Object}, x.id ∉ l.map (·.id) →
    acc.map (mask x) = acc → x.id ∈ acc.map (·.id) → replace (l.foldl replace acc) x = l.foldl replace acc
  | [], _, _, hacc, hm => replace_self hacc hm
  | z :: l, acc, hl, hacc, hm => by
      rw [List.map_cons, List.mem_cons, not_or] at hl
      rw [List.foldl_cons]
      exact replace_foldl_self l hl.2 (mask_replace_ne (Ne.symm hl.1) hacc) (mem_ids_replace hm)

theorem replace_foldl : ∀ (init acc : List Object) (x : Object),
    (replace init x).foldl replace acc = replace (init.foldl replace acc) x
  | [], acc, x => by
      rw [replace_absent rfl]
      rfl
  | y :: init, acc, x => by
      by_cases hx : x.id ∈ (y :: init).map (·.id)
      · rw [replace_present (any_of_mem_ids hx)]
        show ((y :: init).map (mask x)).foldl replace acc = replace ((y :: init).foldl replace acc) x
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        by_cases hx' : x.id ∈ init.map (·.id)
        · have hrep : init.map (mask x) = replace init x := by rw [replace_present (any_of_mem_ids hx')]; rfl
          rw [hrep, replace_foldl init (replace acc (mask x y)) x]
          exact replace_of_mask (foldl_mask init (replace_mask rfl (mask_mask_same rfl y)))
        · have hy : y.id = x.id := by
            rw [List.map_cons, List.mem_cons] at hx
            rcases hx with hx | hx
            · exact hx.symm
            · exact absurd hx hx'
          have hmy : mask x y = x := by simp [mask, hy]
          have hz : mask x y = mask x x := by rw [hmy, mask_self]
          rw [map_mask_of_not_mem hx', hmy, replace_of_mask (foldl_mask init (replace_mask (a := acc) (b := acc) rfl hz))]
          exact (replace_foldl_self init hx' (mask_replace acc x) (mem_ids_replace_self acc x)).symm
      · rw [replace_absent (any_false_of_not_mem hx), List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem foldl_replace_foldl : ∀ (m init acc : List Object),
    (m.foldl replace init).foldl replace acc = m.foldl replace (init.foldl replace acc)
  | [], _, _ => rfl
  | x :: m, init, acc => by
      rw [List.foldl_cons, List.foldl_cons, foldl_replace_foldl m, replace_foldl]

theorem add_current (org m : Origin) : (org.add m.current.objects).current = (org.add m.objects).current := by
  show (⟨(org.objects ++ m.current.objects).foldl replace []⟩ : Origin) = ⟨(org.objects ++ m.objects).foldl replace []⟩
  rw [List.foldl_append, List.foldl_append]
  exact congrArg Origin.mk (foldl_replace_foldl m.objects [] _)

theorem current_merge (c d : Commands) (org : Origin) : ((c.merge d).doc org).current = (d.doc (c.doc org)).current := by
  show (org.add (⟨c.add ++ d.add⟩ : Origin).current.objects).current = ((org.add c.add).add d.add).current
  rw [add_current, add_add]

theorem current_add_current (org : Origin) (l : List Object) : (org.current.add l).current = (org.add l).current :=
  current_append_current org l

theorem project_id (o : Object) (n : Nat) : (o.project n).id = o.id := rfl

theorem PromiseObject.project_pending (p : PromiseObject) (n : Nat)
    (h : (p.project n).state = .pending) : p.project n = p := by
  unfold PromiseObject.project at h ⊢
  by_cases hc : (p.state == PromiseState.pending) = true ∧ p.timeoutAt ≤ n
  · rw [if_pos hc] at h
    split at h <;> simp at h
  · rw [if_neg hc]

theorem view_pending (t : TaskObject) (p : PromiseObject) (h : p.state = .pending) : t.view p = t := by
  unfold TaskObject.view
  simp [h]

theorem project_pending_id (o : Object) (n : Nat)
    (h : (o.project n).promise.state = .pending) : o.project n = o := by
  have hp : o.promise.project n = o.promise := PromiseObject.project_pending _ _ h
  have hs : o.promise.state = .pending := by rw [← hp]; exact h
  cases o with
  | mk id p t =>
      simp only at hp hs
      simp [Object.project, hp, view_pending _ _ hs]

end Refinement
