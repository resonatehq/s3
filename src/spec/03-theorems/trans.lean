import «03-theorems».«frame»

namespace Abstraction
namespace Trans

open AbstractModel
open Abstraction.Induction
open Abstraction.Frame

structure HRel (R : PromiseObject → PromiseObject → Bool)
    (Rf : PromiseObject → Bool) : Prop where
  refl         : ∀ p, R p p = true
  project      : ∀ p₀ p (n : Nat), R p₀ p = true → R p₀ (p.project n) = true
  addCallback  : ∀ p₀ p (c : ServerModel.Ident), R p₀ p = true → R p₀ (p.addCallback c) = true
  addListener  : ∀ p₀ p (c : String), R p₀ p = true → R p₀ (p.addListener c) = true
  settle       : ∀ p₀ p (st : ServerModel.PromiseState) (v : ServerModel.Value) (t : Nat),
                   st.settable = true → p.state = .pending → t < p.timeoutAt →
                   R p₀ p = true →
                   R p₀ { p with state := st, value := v, settledAt := some t } = true
  dropListener : ∀ p₀ p (c : String), p.state ≠ .pending → R p₀ p = true →
                   R p₀ { p with listeners := p.listeners.filter (· != c) } = true
  dropCallback : ∀ p₀ p (c : ServerModel.Ident), p.state ≠ .pending → R p₀ p = true →
                   R p₀ { p with callbacks := p.callbacks.filter (· != c) } = true
  freshLive    : ∀ (param : ServerModel.Value) (tags : ServerModel.Tags)
                   (timeoutAt createdAt : Nat), createdAt < timeoutAt →
                   Rf { state := .pending, param := param, tags := tags,
                        timeoutAt := timeoutAt, createdAt := createdAt } = true
  freshDead    : ∀ (st : ServerModel.PromiseState)
                   (param : ServerModel.Value) (tags : ServerModel.Tags) (timeoutAt : Nat),
                   st = (if tags.isTimer then .resolved else .rejectedTimedout) →
                   Rf { state := st, param := param, tags := tags,
                        timeoutAt := timeoutAt, createdAt := timeoutAt,
                        settledAt := some timeoutAt } = true

theorem promise?_none_of_find?_none {a : ServerState} {id : ServerModel.Ident}
    (h : a.objects.find? (·.id == id) = none) : a.promise? id = none := by
  unfold ServerState.promise?; rw [h]; rfl

theorem find?_none_of_promise?_none {a : ServerState} {id : ServerModel.Ident}
    (h : a.promise? id = none) : a.objects.find? (·.id == id) = none := by
  unfold ServerState.promise? at h
  cases hfo : a.objects.find? (·.id == id) with
  | none   => rfl
  | some o => rw [hfo] at h; simp at h

def relPred (R : PromiseObject → PromiseObject → Bool) (Rf : PromiseObject → Bool)
    (a : ServerState) (id : ServerModel.Ident) (x : PromiseObject) : Bool :=
  match a.promise? id with
  | none   => Rf x
  | some p => R p x

def relQ (R : PromiseObject → PromiseObject → Bool) (Rf : PromiseObject → Bool)
    (a : ServerState) : Q :=
  { promise := relPred R Rf a, task := fun _ => true, schedule := fun _ => true }

theorem hereditary_rel {R : PromiseObject → PromiseObject → Bool}
    {Rf : PromiseObject → Bool} (h : HRel R Rf) (a : ServerState) :
    Hereditary (relQ R Rf a) a where
  project id p n hsto hp := by
    show relPred R Rf a id (p.project n) = true
    cases hf : a.promise? id with
    | none => exact absurd (find?_none_of_promise?_none hf) hsto
    | some p₀ =>
        have hp' : R p₀ p = true := by simpa [relQ, relPred, hf] using hp
        simp [relPred, hf, h.project p₀ p n hp']
  addCallback id p c hsto hp := by
    show relPred R Rf a id (p.addCallback c) = true
    cases hf : a.promise? id with
    | none => exact absurd (find?_none_of_promise?_none hf) hsto
    | some p₀ =>
        have hp' : R p₀ p = true := by simpa [relQ, relPred, hf] using hp
        simp [relPred, hf, h.addCallback p₀ p c hp']
  addListener id p c hsto hp := by
    show relPred R Rf a id (p.addListener c) = true
    cases hf : a.promise? id with
    | none => exact absurd (find?_none_of_promise?_none hf) hsto
    | some p₀ =>
        have hp' : R p₀ p = true := by simpa [relQ, relPred, hf] using hp
        simp [relPred, hf, h.addListener p₀ p c hp']
  settle id p st v t hsto hs hpend hdue hp := by
    show relPred R Rf a id _ = true
    cases hf : a.promise? id with
    | none => exact absurd (find?_none_of_promise?_none hf) hsto
    | some p₀ =>
        have hp' : R p₀ p = true := by simpa [relQ, relPred, hf] using hp
        simp [relPred, hf, h.settle p₀ p st v t hs hpend hdue hp']
  dropListener id p c hsto hns hp := by
    show relPred R Rf a id _ = true
    cases hf : a.promise? id with
    | none => exact absurd (find?_none_of_promise?_none hf) hsto
    | some p₀ =>
        have hp' : R p₀ p = true := by simpa [relQ, relPred, hf] using hp
        simp [relPred, hf, h.dropListener p₀ p c hns hp']
  dropCallback id p c hsto hns hp := by
    show relPred R Rf a id _ = true
    cases hf : a.promise? id with
    | none => exact absurd (find?_none_of_promise?_none hf) hsto
    | some p₀ =>
        have hp' : R p₀ p = true := by simpa [relQ, relPred, hf] using hp
        simp [relPred, hf, h.dropCallback p₀ p c hns hp']
  live id param tags tAt cAt hlt hfresh := by
    simp [relQ, relPred, promise?_none_of_find?_none hfresh,
          h.freshLive param tags tAt cAt hlt]
  dead id st param tags tAt hst hfresh := by
    simp [relQ, relPred, promise?_none_of_find?_none hfresh,
          h.freshDead st param tags tAt hst]
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
  cBorn _ _ _ _ _ _ _ _ := rfl
  cAdvance _ _ _ := rfl

theorem promise?_self_of_nodup {s : ServerState} (hnd : (s.objects.map (·.id)).Nodup)
    (o : Object) (ho : o ∈ s.objects) : s.promise? o.id = some o.promise := by
  unfold ServerState.promise?
  rw [find?_self_of_nodup (·.id) s.objects hnd o ho]; rfl

theorem trans_promise {R : PromiseObject → PromiseObject → Bool}
    {Rf : PromiseObject → Bool} (h : HRel R Rf)
    (mat : Bool) (st : Step) (now : Nat) (s : ServerState)
    (hnd : (s.objects.map (·.id)).Nodup) :
    ∀ o ∈ s.objects,
      ∃ q, (stepOf mat st now s).2.promise? o.id = some q ∧ R o.promise q = true := by
  intro o ho
  have hself := promise?_self_of_nodup hnd o ho
  have hstore : PerStore (relQ R Rf s) s = true := by
    refine perStore_mk ?_ (all_const _) (all_const _)
    refine List.all_eq_true.mpr (fun x hx => ?_)
    simp [relQ, relPred, promise?_self_of_nodup hnd x hx, h.refl x.promise]
  have hw := writesGood_handle (e := { state := s, mat := mat })
    (hereditary_rel h s) hstore st now
  have hstep : (stepOf mat st now s).2
      = applyAll s ((handle st now) { state := s, mat := mat }).2 := rfl
  rw [hstep]
  rcases find?_applyAll_promise ((handle st now) { state := s, mat := mat }).2 s o.id with
    hfr | ⟨x, hxw, hfr⟩
  · exact ⟨o.promise, by rw [hfr, hself], h.refl o.promise⟩
  · refine ⟨x, hfr, ?_⟩
    have hgood : relPred R Rf s o.id x = true := hw _ hxw
    simp only [relPred, hself] at hgood
    exact hgood

theorem trans_promise_post {R : PromiseObject → PromiseObject → Bool}
    {Rf : PromiseObject → Bool} (h : HRel R Rf)
    (mat : Bool) (st : Step) (now : Nat) (s : ServerState) (hnd : StoreNodup s) :
    ∀ q ∈ (stepOf mat st now s).2.objects, relPred R Rf s q.id q.promise = true := by
  intro q hq
  have hbnd : StoreNodup (stepOf mat st now s).2 := storeNodup_step mat st now s hnd
  have hself := promise?_self_of_nodup hbnd.1 q hq
  have hstore : PerStore (relQ R Rf s) s = true := by
    refine perStore_mk ?_ (all_const _) (all_const _)
    refine List.all_eq_true.mpr (fun x hx => ?_)
    simp [relQ, relPred, promise?_self_of_nodup hnd.1 x hx, h.refl x.promise]
  have hw := writesGood_handle (e := { state := s, mat := mat })
    (hereditary_rel h s) hstore st now
  have hstep : (stepOf mat st now s).2
      = applyAll s ((handle st now) { state := s, mat := mat }).2 := rfl
  rw [hstep] at hself
  rcases find?_applyAll_promise ((handle st now) { state := s, mat := mat }).2 s q.id with
    hfr | ⟨x, hxw, hfr⟩
  · have : s.promise? q.id = some q.promise := by rw [← hfr]; exact hself
    simp [relPred, this, h.refl q.promise]
  · have hxq : x = q.promise := Option.some.inj (by rw [← hfr]; exact hself)
    subst hxq
    exact hw _ hxw

section Entries

open Properties

def rBirthFields (p q : PromiseObject) : Bool :=
  q.param.data == p.param.data && q.param.headers == p.param.headers
    && q.tags == p.tags && q.timeoutAt == p.timeoutAt && q.createdAt == p.createdAt

theorem hrel_birthFields : HRel rBirthFields (fun _ => true) where
  refl p := by simp [rBirthFields]
  project p₀ p n h := by
    unfold PromiseObject.project
    split
    · split <;> simpa [rBirthFields] using h
    · simpa [rBirthFields] using h
  addCallback p₀ p c h := by
    unfold PromiseObject.addCallback
    split <;> simpa [rBirthFields] using h
  addListener p₀ p c h := by
    unfold PromiseObject.addListener
    split <;> simpa [rBirthFields] using h
  settle p₀ p st v t _ _ _ h := by simpa [rBirthFields] using h
  dropListener p₀ p c _ h := by simpa [rBirthFields] using h
  dropCallback p₀ p c _ h := by simpa [rBirthFields] using h
  freshLive _ _ _ _ _ := rfl
  freshDead _ _ _ _ _ := rfl

theorem preserved_promise_birth_fields_immutable_step (mat : Bool) (st : Step) (now n' : Nat)
    (s : ServerState) (hnd : (s.objects.map (·.id)).Nodup) :
    preserved_promise_birth_fields_immutable n' s (stepOf mat st now s).2 = true := by
  refine List.all_eq_true.mpr (fun o ho => ?_)
  obtain ⟨q, hfind, hR⟩ := trans_promise hrel_birthFields mat st now s hnd o ho
  show (match (stepOf mat st now s).2.promise? o.id with
        | none => true | some q => _) = true
  rw [hfind]
  exact hR

def rSettledRecord (p q : PromiseObject) : Bool :=
  p.state == .pending
    || (q.state == p.state && q.settledAt == p.settledAt
        && q.value.data == p.value.data && q.value.headers == p.value.headers)

theorem hrel_settledRecord : HRel rSettledRecord (fun _ => true) where
  refl p := by simp [rSettledRecord]
  project p₀ p n h := by
    by_cases hp : p₀.state = ServerModel.PromiseState.pending
    · simp [rSettledRecord, hp]
    · have hq : (p.state == p₀.state) = true := by
        simp only [rSettledRecord, Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with h | ⟨⟨⟨h1, _⟩, _⟩, _⟩
        · exact absurd (by simpa using h) hp
        · exact h1
      have hnp : p.state ≠ ServerModel.PromiseState.pending := by
        intro hc; exact hp (by rw [← eq_of_beq hq, hc])
      rw [Lookup.project_not_pending p n (by simp [hnp])]
      exact h
  addCallback p₀ p c h := by
    unfold PromiseObject.addCallback
    split <;> simpa [rSettledRecord] using h
  addListener p₀ p c h := by
    unfold PromiseObject.addListener
    split <;> simpa [rSettledRecord] using h
  settle p₀ p st v t _ hpend _ h := by
    by_cases hp : p₀.state = ServerModel.PromiseState.pending
    · simp [rSettledRecord, hp]
    · exfalso
      have hq : (p.state == p₀.state) = true := by
        simp only [rSettledRecord, Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with h | ⟨⟨⟨h1, _⟩, _⟩, _⟩
        · exact absurd (by simpa using h) hp
        · exact h1
      exact hp (by rw [← eq_of_beq hq, hpend])
  dropListener p₀ p c _ h := by simpa [rSettledRecord] using h
  dropCallback p₀ p c _ h := by simpa [rSettledRecord] using h
  freshLive _ _ _ _ _ := rfl
  freshDead _ _ _ _ _ := rfl

theorem preserved_settled_promise_record_step (mat : Bool) (st : Step) (now n' : Nat)
    (s : ServerState) (hnd : (s.objects.map (·.id)).Nodup) :
    preserved_settled_promise_record n' s (stepOf mat st now s).2 = true := by
  refine List.all_eq_true.mpr (fun o ho => ?_)
  obtain ⟨q, hfind, hR⟩ := trans_promise hrel_settledRecord mat st now s hnd o ho
  show (o.promise.state == ServerModel.PromiseState.pending ||
        (match (stepOf mat st now s).2.promise? o.id with
         | none => false | some q => _)) = true
  rw [hfind]
  simpa [rSettledRecord] using hR

theorem preserved_promise_state_frozen_once_settled_step (mat : Bool) (st : Step)
    (now n' : Nat) (s : ServerState) (hnd : (s.objects.map (·.id)).Nodup) :
    preserved_promise_state_frozen_once_settled n' s (stepOf mat st now s).2 = true := by
  refine List.all_eq_true.mpr (fun o ho => ?_)
  obtain ⟨q, hfind, hR⟩ := trans_promise hrel_settledRecord mat st now s hnd o ho
  show (o.promise.state == ServerModel.PromiseState.pending ||
        match (stepOf mat st now s).2.promise? o.id with
        | none => false | some q => q.state == o.promise.state) = true
  rw [hfind]
  simp only [rSettledRecord, Bool.or_eq_true, Bool.and_eq_true] at hR
  rcases hR with h | ⟨⟨⟨h1, _⟩, _⟩, _⟩
  · simp [h]
  · simp [h1]

def rValueUntilSettled (p q : PromiseObject) : Bool :=
  q.state != .pending
    || (q.value.data == p.value.data && q.value.headers == p.value.headers)

theorem hrel_valueUntilSettled : HRel rValueUntilSettled (fun _ => true) where
  refl p := by simp [rValueUntilSettled]
  project p₀ p n h := by
    unfold PromiseObject.project
    split
    · split <;> simp [rValueUntilSettled]
    · simpa [rValueUntilSettled] using h
  addCallback p₀ p c h := by
    unfold PromiseObject.addCallback
    split <;> simpa [rValueUntilSettled] using h
  addListener p₀ p c h := by
    unfold PromiseObject.addListener
    split <;> simpa [rValueUntilSettled] using h
  settle p₀ p st v t hst _ _ _ := by
    cases st <;> simp_all [rValueUntilSettled, ServerModel.PromiseState.settable]
  dropListener p₀ p c _ h := by simpa [rValueUntilSettled] using h
  dropCallback p₀ p c _ h := by simpa [rValueUntilSettled] using h
  freshLive _ _ _ _ _ := rfl
  freshDead _ _ _ _ _ := rfl

theorem preserved_promise_value_until_settlement_step (mat : Bool) (st : Step)
    (now n' : Nat) (s : ServerState) (hnd : (s.objects.map (·.id)).Nodup) :
    preserved_promise_value_until_settlement n' s (stepOf mat st now s).2 = true := by
  refine List.all_eq_true.mpr (fun o ho => ?_)
  obtain ⟨q, hfind, hR⟩ := trans_promise hrel_valueUntilSettled mat st now s hnd o ho
  show (match (stepOf mat st now s).2.promise? o.id with
        | none => false | some q => _) = true
  rw [hfind]
  exact hR

theorem preserved_promise_no_duplicate_ids_step (mat : Bool) (st : Step) (now n' : Nat)
    (s : ServerState) (h : StoreNodup s) :
    preserved_promise_no_duplicate_ids n' s (stepOf mat st now s).2 = true :=
  object_ids_unique_of_nodup n' _ (storeNodup_step mat st now s h)

def rOneWay (p q : PromiseObject) : Bool :=
  q.state != .pending || p.state == .pending

theorem hrel_oneWay : HRel rOneWay (fun _ => true) where
  refl p := by cases hp : p.state <;> simp [rOneWay, hp]
  project p₀ p n h := by
    by_cases hq : p.state = ServerModel.PromiseState.pending
    · by_cases hp : p₀.state = ServerModel.PromiseState.pending
      · unfold PromiseObject.project
        split
        · split <;> simp [rOneWay, hp]
        · simp [rOneWay, hp]
      · exact absurd (by simpa [rOneWay, hq] using h) hp
    · rw [Lookup.project_not_pending p n (by simp [hq])]
      exact h
  addCallback p₀ p c h := by
    unfold PromiseObject.addCallback
    split <;> simpa [rOneWay] using h
  addListener p₀ p c h := by
    unfold PromiseObject.addListener
    split <;> simpa [rOneWay] using h
  settle p₀ p st v t hst _ _ _ := by
    cases st <;> simp_all [rOneWay, ServerModel.PromiseState.settable]
  dropListener p₀ p c _ h := by simpa [rOneWay] using h
  dropCallback p₀ p c _ h := by simpa [rOneWay] using h
  freshLive _ _ _ _ _ := rfl
  freshDead _ _ _ _ _ := rfl

theorem preserved_promise_settlement_is_one_way_step (mat : Bool) (st : Step) (now n' : Nat)
    (s : ServerState) (hnd : StoreNodup s) :
    preserved_promise_settlement_is_one_way n' s (stepOf mat st now s).2 = true := by
  refine List.all_eq_true.mpr (fun q hq => ?_)
  have hR := trans_promise_post hrel_oneWay mat st now s hnd q hq
  show (q.promise.state != ServerModel.PromiseState.pending ||
        match s.promise? q.id with
        | some p => p.state == ServerModel.PromiseState.pending
        | none => true) = true
  cases hf : s.promise? q.id with
  | none => simp
  | some p =>
      simp only [relPred, hf] at hR
      simpa [rOneWay] using hR

theorem subsetOf_refl {α} [BEq α] [LawfulBEq α] (xs : List α) : Properties.subsetOf xs xs = true :=
  List.all_eq_true.mpr (fun z hz => by simpa using hz)

theorem subsetOf_append {α} [BEq α] [LawfulBEq α] (xs ys : List α) (c : α)
    (h : Properties.subsetOf xs ys = true) :
    Properties.subsetOf xs (ys ++ [c]) = true := by
  refine List.all_eq_true.mpr (fun z hz => ?_)
  have hz' := List.all_eq_true.mp h z hz
  simp only [List.contains, List.elem_eq_mem, decide_eq_true_eq] at hz' ⊢
  exact List.mem_append_left _ hz'

def rCallbacksGrow (p q : PromiseObject) : Bool :=
  q.state != .pending || Properties.subsetOf p.callbacks q.callbacks

theorem hrel_callbacksGrow :
    HRel rCallbacksGrow (fun q => q.state != .pending || q.callbacks.isEmpty) where
  refl p := by simp [rCallbacksGrow, subsetOf_refl]
  project p₀ p n h := by
    unfold PromiseObject.project
    split
    · split <;> simp [rCallbacksGrow]
    · simpa [rCallbacksGrow] using h
  addCallback p₀ p c h := by
    unfold PromiseObject.addCallback
    split
    · exact h
    · by_cases hq : p.state = ServerModel.PromiseState.pending
      · have := (by simpa [rCallbacksGrow, hq] using h : Properties.subsetOf p₀.callbacks p.callbacks = true)
        simp [rCallbacksGrow, hq, subsetOf_append _ _ c this]
      · simp [rCallbacksGrow, hq]
  addListener p₀ p c h := by
    unfold PromiseObject.addListener
    split <;> simpa [rCallbacksGrow] using h
  settle p₀ p st v t hst _ _ _ := by
    cases st <;> simp_all [rCallbacksGrow, ServerModel.PromiseState.settable]
  dropListener p₀ p c _ h := by simpa [rCallbacksGrow] using h
  dropCallback p₀ p c hns _ := by simp [rCallbacksGrow, hns]
  freshLive _ _ _ _ _ := rfl
  freshDead st param tags tAt hst := by subst hst; split <;> simp

theorem monotone_promise_callbacks_grow_while_pending_step (mat : Bool) (st : Step)
    (now n' : Nat) (s : ServerState) (hnd : StoreNodup s) :
    monotone_promise_callbacks_grow_while_pending n' s (stepOf mat st now s).2 = true := by
  refine List.all_eq_true.mpr (fun q hq => ?_)
  have hR := trans_promise_post hrel_callbacksGrow mat st now s hnd q hq
  show (q.promise.state != ServerModel.PromiseState.pending ||
        match s.promise? q.id with
        | none => q.promise.callbacks.isEmpty
        | some p => Properties.subsetOf p.callbacks q.promise.callbacks) = true
  cases hf : s.promise? q.id with
  | none => simp only [relPred, hf] at hR; simpa using hR
  | some p => simp only [relPred, hf] at hR; simpa [rCallbacksGrow] using hR

def rListenersGrow (p q : PromiseObject) : Bool :=
  q.state != .pending || Properties.subsetOf p.listeners q.listeners

theorem hrel_listenersGrow :
    HRel rListenersGrow (fun q => q.state != .pending || q.listeners.isEmpty) where
  refl p := by simp [rListenersGrow, subsetOf_refl]
  project p₀ p n h := by
    unfold PromiseObject.project
    split
    · split <;> simp [rListenersGrow]
    · simpa [rListenersGrow] using h
  addCallback p₀ p c h := by
    unfold PromiseObject.addCallback
    split <;> simpa [rListenersGrow] using h
  addListener p₀ p c h := by
    unfold PromiseObject.addListener
    split
    · exact h
    · by_cases hq : p.state = ServerModel.PromiseState.pending
      · have := (by simpa [rListenersGrow, hq] using h : Properties.subsetOf p₀.listeners p.listeners = true)
        simp [rListenersGrow, hq, subsetOf_append _ _ c this]
      · simp [rListenersGrow, hq]
  settle p₀ p st v t hst _ _ _ := by
    cases st <;> simp_all [rListenersGrow, ServerModel.PromiseState.settable]
  dropListener p₀ p c hns _ := by simp [rListenersGrow, hns]
  dropCallback p₀ p c _ h := by simpa [rListenersGrow] using h
  freshLive _ _ _ _ _ := rfl
  freshDead st param tags tAt hst := by subst hst; split <;> simp

theorem monotone_promise_listeners_grow_while_pending_step (mat : Bool) (st : Step)
    (now n' : Nat) (s : ServerState) (hnd : StoreNodup s) :
    monotone_promise_listeners_grow_while_pending n' s (stepOf mat st now s).2 = true := by
  refine List.all_eq_true.mpr (fun q hq => ?_)
  have hR := trans_promise_post hrel_listenersGrow mat st now s hnd q hq
  show (q.promise.state != ServerModel.PromiseState.pending ||
        match s.promise? q.id with
        | none => q.promise.listeners.isEmpty
        | some p => Properties.subsetOf p.listeners q.promise.listeners) = true
  cases hf : s.promise? q.id with
  | none => simp only [relPred, hf] at hR; simpa using hR
  | some p => simp only [relPred, hf] at hR; simpa [rListenersGrow] using hR

end Entries

end Trans
end Abstraction
