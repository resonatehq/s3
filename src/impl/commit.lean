import impl.apply

namespace Commit

open ServerModel AbstractModel
open Abstract (Request Response Reply)
open Impl (OriginDoc World Key Blob Work Txn State Obs)
open Apply

def currentDoc (w : World) (o : String) : OriginDoc :=
  match w.doc? o with
  | some (d, _) => d
  | none        => {}

theorem Cbind_apply (x : Impl.C α) (f : α → Impl.C β) (e : Impl.Env) :
    (x >>= f) e = ((f (x e).1 e).1, (x e).2 ++ (f (x e).1 e).2) := rfl

theorem Cpure_apply (a : α) (e : Impl.Env) : (pure a : Impl.C α) e = (a, []) := rfl

theorem emitAll_apply (fx : List Impl.Effect) (e : Impl.Env) : Impl.emitAll fx e = ((), fx) := by
  induction fx with
  | nil => rfl
  | cons f fs ih => simp [Impl.emitAll, Cbind_apply, ih, Impl.emit]

theorem transact_apply (mat : Bool) (work : Work) (now : Nat) (e : Impl.Env) :
    Impl.transact mat work now e =
      ((Impl.decide mat e.origin work now e.doc).1,
       Impl.armFx e.doc (Impl.decide mat e.origin work now e.doc).2.1 ++
        [Impl.Effect.putDoc (Impl.decide mat e.origin work now e.doc).2.1] ++
        Impl.delFx e.doc (Impl.decide mat e.origin work now e.doc).2.1 work ++
        Impl.sendFx (Impl.decide mat e.origin work now e.doc).2.2) := by
  simp [Impl.transact, Cbind_apply, Cpure_apply, emitAll_apply, Impl.ask, Impl.putDoc, Impl.emit]

def _root_.Impl.Effect.isPutDoc : Impl.Effect → Bool
  | .putDoc _ => true
  | _         => false

def sendsOfC : List Impl.Effect → List (String × Message)
  | []                => []
  | .send a m :: rest => (a, m) :: sendsOfC rest
  | _ :: rest         => sendsOfC rest

theorem sendsOfC_sendFx (sends : List (String × Message)) : sendsOfC (Impl.sendFx sends) = sends := by
  induction sends with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨a, m⟩; simp [Impl.sendFx, sendsOfC] at ih ⊢; exact ih

theorem armFx_nodoc (old new : OriginDoc) : ∀ f ∈ Impl.armFx old new, f.isPutDoc = false := by
  intro f hf
  simp only [Impl.armFx] at hf
  split at hf
  · split at hf
    · simp only [List.mem_singleton] at hf; subst hf; rfl
    · simp at hf
  · simp at hf

theorem armFx_nosend (old new : OriginDoc) : sendsOfC (Impl.armFx old new) = [] := by
  simp only [Impl.armFx]
  split
  · split <;> rfl
  · rfl

theorem delFx_nodoc (old new : OriginDoc) (work : Work) :
    ∀ f ∈ Impl.delFx old new work, f.isPutDoc = false := by
  intro f hf
  simp only [Impl.delFx, List.mem_append] at hf
  rcases hf with hf | hf
  · split at hf
    · split at hf
      · simp only [List.mem_singleton] at hf; subst hf; rfl
      · simp at hf
    · simp at hf
  · split at hf
    · split at hf
      · simp only [List.mem_singleton] at hf; subst hf; rfl
      · simp at hf
    · simp at hf

theorem delFx_nosend (old new : OriginDoc) (work : Work) : sendsOfC (Impl.delFx old new work) = [] := by
  simp only [Impl.delFx]
  split
  · split
    · simp only [List.singleton_append, sendsOfC]
      split
      · split <;> rfl
      · rfl
    · simp only [List.nil_append]
      split
      · split <;> rfl
      · rfl
  · simp only [List.nil_append]
    split
    · split <;> rfl
    · rfl

theorem sendFx_nodoc (sends : List (String × Message)) : ∀ f ∈ Impl.sendFx sends, f.isPutDoc = false := by
  intro f hf
  simp only [Impl.sendFx, List.mem_map] at hf
  obtain ⟨⟨a, m⟩, _, rfl⟩ := hf
  rfl

def SInv (st : Cas.Store Key Blob) : Prop := ∀ e ∈ st.entries, e.2.1 < st.next

theorem put_ok_next {st st' : Cas.Store Key Blob} {k : Key} {b : Blob} {c : Cas.Cond} {v : Cas.Version}
    (h : st.put k b c = .ok (st', v)) : v = st.next ∧ st'.next = st.next + 1 := by
  unfold Cas.Store.put at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

theorem put_ok_sinv {st st' : Cas.Store Key Blob} {k : Key} {b : Blob} {c : Cas.Cond} {v : Cas.Version}
    (h : st.put k b c = .ok (st', v)) (hs : SInv st) : SInv st' :=
  (Cas.put_version_fresh st k b c st' v h hs).2

theorem del_ok_next {st st' : Cas.Store Key Blob} {k : Key} {c : Cas.Cond}
    (h : st.del k c = .ok st') : st'.next = st.next := by
  unfold Cas.Store.del at h
  split at h
  · cases h; rfl
  · cases h

theorem del_ok_sinv {st st' : Cas.Store Key Blob} {k : Key} {c : Cas.Cond}
    (h : st.del k c = .ok st') (hs : SInv st) : SInv st' := by
  unfold Cas.Store.del at h
  split at h
  · cases h
    intro e he
    exact hs e (List.mem_filter.mp he).1
  · cases h

theorem any_put_ok (st : Cas.Store Key Blob) (k : Key) (b : Blob) :
    ∃ st' v, st.put k b .any = .ok (st', v) := by
  unfold Cas.Store.put
  simp [Cas.Cond.holds]

theorem any_del_ok (st : Cas.Store Key Blob) (k : Key) : ∃ st', st.del k .any = .ok st' := by
  unfold Cas.Store.del
  simp [Cas.Cond.holds]

theorem apply_nodoc {o : String} {c : Cas.Cond} {w : World} {f : Impl.Effect}
    (hf : f.isPutDoc = false) :
    ∃ w', f.apply o c w = .ok w' ∧
      (∀ o', w'.store.get (.doc o') = w.store.get (.doc o')) ∧
      w'.wire = sendsFold w.wire (sendsOfC [f]) ∧
      w.store.next ≤ w'.store.next ∧
      (SInv w.store → SInv w'.store) := by
  cases f with
  | putDoc d => cases hf
  | armTimer dl =>
    obtain ⟨st', v, hp⟩ := any_put_ok w.store (.timer dl o) .timer
    refine ⟨{ w with store := st' }, ?_, ?_, rfl, ?_, ?_⟩
    · simp [Impl.Effect.apply, hp]
    · intro o'
      exact Cas.get_put_other _ _ _ _ _ _ _ hp (by simp)
    · rw [(put_ok_next hp).2]; exact Nat.le_succ _
    · exact put_ok_sinv hp
  | delTimer dl =>
    obtain ⟨st', hp⟩ := any_del_ok w.store (.timer dl o)
    refine ⟨{ w with store := st' }, ?_, ?_, rfl, ?_, ?_⟩
    · simp [Impl.Effect.apply, hp]
    · intro o'
      exact Cas.get_del_other _ _ _ _ _ hp (by simp)
    · rw [del_ok_next hp]; exact Nat.le_refl _
    · exact del_ok_sinv hp
  | send a m =>
    refine ⟨w.send a m, rfl, fun _ => rfl, rfl, Nat.le_refl _, id⟩

theorem applyEffects_nodoc {o : String} {c : Cas.Cond} :
    ∀ (fx : List Impl.Effect) (w : World), (∀ f ∈ fx, f.isPutDoc = false) →
      (Impl.applyEffects o c w fx).2 = true ∧
      (∀ o', (Impl.applyEffects o c w fx).1.store.get (.doc o') = w.store.get (.doc o')) ∧
      (Impl.applyEffects o c w fx).1.wire = sendsFold w.wire (sendsOfC fx) ∧
      w.store.next ≤ (Impl.applyEffects o c w fx).1.store.next ∧
      (SInv w.store → SInv (Impl.applyEffects o c w fx).1.store)
  | [], w, _ => ⟨rfl, fun _ => rfl, rfl, Nat.le_refl _, id⟩
  | f :: fs, w, h => by
      obtain ⟨w', hok, hget, hwire, hnext, hsinv⟩ := apply_nodoc (o := o) (c := c) (w := w)
        (h f (List.mem_cons_self ..))
      have ih := applyEffects_nodoc (o := o) (c := c) fs w' (fun g hg => h g (List.mem_cons_of_mem _ hg))
      simp only [Impl.applyEffects, hok]
      refine ⟨ih.1, ?_, ?_, ?_, ?_⟩
      · intro o'; rw [ih.2.1 o', hget o']
      · rw [ih.2.2.1, hwire]
        cases f with
        | send a m => rfl
        | putDoc d => cases h _ (List.mem_cons_self ..)
        | armTimer dl => rfl
        | delTimer dl => rfl
      · exact Nat.le_trans hnext ih.2.2.2.1
      · exact fun hs => ih.2.2.2.2 (hsinv hs)

theorem applyEffects_append (o : String) (c : Cas.Cond) :
    ∀ (a b : List Impl.Effect) (w : World),
      Impl.applyEffects o c w (a ++ b) =
        if (Impl.applyEffects o c w a).2 then Impl.applyEffects o c (Impl.applyEffects o c w a).1 b
        else Impl.applyEffects o c w a
  | [], b, w => by simp [Impl.applyEffects]
  | f :: fs, b, w => by
      simp only [List.cons_append, Impl.applyEffects]
      split
      · exact applyEffects_append o c fs b _
      · simp

def TxnInv (st : Cas.Store Key Blob) (t : Txn) : Prop :=
  ∀ d v, t.snapshot = some (d, v) →
    v < st.next ∧ ∀ b, st.get (.doc t.origin) = some (b, v) → b = .doc d

theorem TxnInv.of_get_eq {st st' : Cas.Store Key Blob} {t : Txn}
    (hget : ∀ o', st'.get (.doc o') = st.get (.doc o')) (hnext : st.next ≤ st'.next)
    (h : TxnInv st t) : TxnInv st' t := by
  intro d v hs
  obtain ⟨h1, h2⟩ := h d v hs
  refine ⟨Nat.lt_of_lt_of_le h1 hnext, ?_⟩
  intro b hb
  rw [hget] at hb
  exact h2 b hb

theorem TxnInv.of_put {st st' : Cas.Store Key Blob} {o : String} {d : OriginDoc} {c : Cas.Cond}
    {v' : Cas.Version} (hp : st.put (.doc o) (.doc d) c = .ok (st', v')) {t : Txn}
    (h : TxnInv st t) : TxnInv st' t := by
  intro d0 v hs
  obtain ⟨h1, h2⟩ := h d0 v hs
  obtain ⟨hv', hn⟩ := put_ok_next hp
  refine ⟨by rw [hn]; exact Nat.lt_succ_of_lt h1, ?_⟩
  intro b hb
  by_cases ho : t.origin = o
  · subst ho
    rw [Cas.get_put_same _ _ _ _ _ _ hp] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨_, hvv⟩ := hb
    have hv : v = st.next := hvv ▸ hv'
    rw [hv] at h1
    exact absurd h1 (Nat.lt_irrefl _)
  · rw [Cas.get_put_other _ _ _ _ _ _ _ hp (by simpa using ho)] at hb
    exact h2 b hb

theorem snapshot_current {w : World} {t : Txn} {mat : Bool} (hinv : TxnInv w.store t)
    (hc : (Impl.Env.cond { origin := t.origin, snapshot := t.snapshot, mat := mat }).holds
            (w.store.version? (.doc t.origin)) = true) :
    (Impl.Env.doc { origin := t.origin, snapshot := t.snapshot, mat := mat }) = currentDoc w t.origin := by
  cases hs : t.snapshot with
  | none =>
    have hc' : w.store.version? (.doc t.origin) = none := by
      have := hc
      simp only [Impl.Env.cond, hs, Cas.Cond.holds, Option.isNone_iff_eq_none] at this
      exact this
    simp only [Cas.Store.version?, Option.map_eq_none_iff] at hc'
    simp [Impl.Env.doc, currentDoc, World.doc?, hc']
  | some dv =>
    obtain ⟨d, v⟩ := dv
    have hc' : w.store.version? (.doc t.origin) = some v := by
      have := hc
      simp only [Impl.Env.cond, hs, Cas.Cond.holds, beq_iff_eq] at this
      exact this
    simp only [Cas.Store.version?, Option.map_eq_some_iff] at hc'
    obtain ⟨⟨b, v'⟩, hg, hv⟩ := hc'
    simp only at hv
    subst hv
    have := (hinv d v' hs).2 b hg
    subst this
    simp [Impl.Env.doc, currentDoc, World.doc?, hg]

def envOf (mat : Bool) (t : Txn) : Impl.Env := { origin := t.origin, snapshot := t.snapshot, mat := mat }

def decOf (mat : Bool) (t : Txn) (now : Nat) : Reply × OriginDoc × List (String × Message) :=
  Impl.decide mat t.origin t.work now (envOf mat t).doc

def armed (mat : Bool) (t : Txn) (now : Nat) (w : World) : World :=
  (Impl.applyEffects t.origin (envOf mat t).cond w (Impl.armFx (envOf mat t).doc (decOf mat t now).2.1)).1

theorem envOf_origin (mat : Bool) (t : Txn) : (envOf mat t).origin = t.origin := rfl

theorem applyEffects_cons_putDoc (o : String) (c : Cas.Cond) (w : World) (d : OriginDoc)
    (fs : List Impl.Effect) :
    Impl.applyEffects o c w (.putDoc d :: fs) =
      match w.store.put (.doc o) (.doc d) c with
      | .ok (st, _) => Impl.applyEffects o c { w with store := st } fs
      | .rejected   => (w, false) := by
  show (match (Impl.Effect.putDoc d).apply o c w with
        | .ok w' => Impl.applyEffects o c w' fs
        | .rejected => (w, false)) = _
  simp only [Impl.Effect.apply]
  cases w.store.put (.doc o) (.doc d) c with
  | ok x => obtain ⟨st, v⟩ := x; rfl
  | rejected => rfl

theorem runC_transact (mat : Bool) (t : Txn) (now : Nat) (w : World) :
    Impl.runC (Impl.transact mat t.work now) (envOf mat t) w =
      match (armed mat t now w).store.put (.doc t.origin) (.doc (decOf mat t now).2.1)
              (envOf mat t).cond with
      | .ok (st, _) =>
          (some (decOf mat t now).1,
           (Impl.applyEffects t.origin (envOf mat t).cond { armed mat t now w with store := st }
             (Impl.delFx (envOf mat t).doc (decOf mat t now).2.1 t.work ++
              Impl.sendFx (decOf mat t now).2.2)).1)
      | .rejected => (none, armed mat t now w) := by
  have harm := applyEffects_nodoc (o := t.origin) (c := (envOf mat t).cond) _ w
    (armFx_nodoc (envOf mat t).doc (decOf mat t now).2.1)
  unfold Impl.runC
  rw [transact_apply]
  simp only [envOf_origin, List.append_assoc, List.singleton_append]
  rw [applyEffects_append]
  unfold decOf at harm
  unfold armed decOf
  simp only [harm.1, ↓reduceIte]
  generalize (Impl.applyEffects t.origin (envOf mat t).cond w
    (Impl.armFx (envOf mat t).doc
      (Impl.decide mat t.origin t.work now (envOf mat t).doc).2.1)).1 = w1
  simp only [List.cons_append, applyEffects_cons_putDoc]
  cases hp : w1.store.put (.doc t.origin)
      (.doc (Impl.decide mat t.origin t.work now (envOf mat t).doc).2.1) (envOf mat t).cond with
  | ok x =>
    obtain ⟨st, v⟩ := x
    have hrest := applyEffects_nodoc (o := t.origin) (c := (envOf mat t).cond)
      (Impl.delFx (envOf mat t).doc (Impl.decide mat t.origin t.work now (envOf mat t).doc).2.1 t.work ++
        Impl.sendFx (Impl.decide mat t.origin t.work now (envOf mat t).doc).2.2)
      { w1 with store := st }
      (by intro f hf
          simp only [List.mem_append] at hf
          rcases hf with hf | hf
          · exact delFx_nodoc (envOf mat t).doc _ t.work f hf
          · exact sendFx_nodoc _ f hf)
    simp only [hrest.1, ↓reduceIte]
  | rejected => rfl

end Commit
