import impl.apply

namespace Commit

open ServerModel AbstractModel
open Abstract (Request Response Reply)
open Impl (Origin World Key Blob Work Txn State Obs Commit)
open Apply

def current (w : World) (n : String) : Origin :=
  match w.origin? n with
  | some (o, _) => o
  | none        => {}

theorem Cbind_apply (x : Impl.C α) (f : α → Impl.C β) (e : Impl.Env) :
    (x >>= f) e = ((f (x e).1 e).1, (x e).2 ++ (f (x e).1 e).2) := rfl

theorem Cpure_apply (a : α) (e : Impl.Env) : (pure a : Impl.C α) e = (a, []) := rfl

theorem emitAll_apply (fx : List Impl.Effect) (e : Impl.Env) : Impl.emitAll fx e = ((), fx) := by
  induction fx with
  | nil => rfl
  | cons f fs ih => simp [Impl.emitAll, Cbind_apply, ih, Impl.emit]

theorem transact_apply (work : Work) (now : Nat) (e : Impl.Env) :
    Impl.transact work now e =
      ((Impl.decide e.origin work now e.snap).1,
       Impl.armFx (Impl.decide e.origin work now e.snap).2 ++
        [Impl.Effect.putOrigin (Impl.decide e.origin work now e.snap).2.put] ++
        Impl.delFx (Impl.decide e.origin work now e.snap).2 ++
        Impl.sendFx (Impl.decide e.origin work now e.snap).2.send) := by
  simp [Impl.transact, Cbind_apply, Cpure_apply, emitAll_apply, Impl.ask, Impl.putOrigin, Impl.emit]

def _root_.Impl.Effect.isPut : Impl.Effect → Bool
  | .putOrigin _ => true
  | _            => false

def sendsOfC : List Impl.Effect → List (String × Message)
  | []                => []
  | .send a m :: rest => (a, m) :: sendsOfC rest
  | _ :: rest         => sendsOfC rest

theorem sendsOfC_append (a b : List Impl.Effect) : sendsOfC (a ++ b) = sendsOfC a ++ sendsOfC b := by
  induction a with
  | nil => rfl
  | cons f fs ih => cases f <;> simp [sendsOfC, ih]

theorem sendsOfC_sendFx (sends : List (String × Message)) : sendsOfC (Impl.sendFx sends) = sends := by
  induction sends with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨a, m⟩; simp [Impl.sendFx, sendsOfC] at ih ⊢; exact ih

theorem armFx_noput (c : Commit) : ∀ f ∈ Impl.armFx c, f.isPut = false := by
  intro f hf
  simp only [Impl.armFx, List.mem_map] at hf
  obtain ⟨_, _, rfl⟩ := hf
  rfl

theorem armFx_nosend (c : Commit) : sendsOfC (Impl.armFx c) = [] := by
  simp only [Impl.armFx]
  induction c.arm with
  | nil => rfl
  | cons d ds ih => simp [sendsOfC, ih]

theorem delFx_noput (c : Commit) : ∀ f ∈ Impl.delFx c, f.isPut = false := by
  intro f hf
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hf
  rfl

theorem delFx_nosend (c : Commit) : sendsOfC (Impl.delFx c) = [] := by
  simp only [Impl.delFx]
  induction c.del with
  | nil => rfl
  | cons d ds ih => simp [sendsOfC, ih]

theorem sendFx_noput (sends : List (String × Message)) : ∀ f ∈ Impl.sendFx sends, f.isPut = false := by
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

theorem apply_noput {n : String} {c : Cas.Cond} {w : World} {f : Impl.Effect}
    (hf : f.isPut = false) :
    ∃ w', f.apply n c w = .ok w' ∧
      (∀ n', w'.store.get (.origin n') = w.store.get (.origin n')) ∧
      w'.wire = sendsFold w.wire (sendsOfC [f]) ∧
      w.store.next ≤ w'.store.next ∧
      (SInv w.store → SInv w'.store) := by
  cases f with
  | putOrigin o => cases hf
  | armTimer dl =>
    obtain ⟨st', v, hp⟩ := any_put_ok w.store (.timer dl n) .timer
    refine ⟨{ w with store := st' }, ?_, ?_, rfl, ?_, ?_⟩
    · simp [Impl.Effect.apply, hp]
    · intro n'
      exact Cas.get_put_other _ _ _ _ _ _ _ hp (by simp)
    · rw [(put_ok_next hp).2]; exact Nat.le_succ _
    · exact put_ok_sinv hp
  | delTimer dl =>
    obtain ⟨st', hp⟩ := any_del_ok w.store (.timer dl n)
    refine ⟨{ w with store := st' }, ?_, ?_, rfl, ?_, ?_⟩
    · simp [Impl.Effect.apply, hp]
    · intro n'
      exact Cas.get_del_other _ _ _ _ _ hp (by simp)
    · rw [del_ok_next hp]; exact Nat.le_refl _
    · exact del_ok_sinv hp
  | send a m =>
    refine ⟨w.send a m, rfl, fun _ => rfl, rfl, Nat.le_refl _, id⟩

theorem applyEffects_noput {n : String} {c : Cas.Cond} :
    ∀ (fx : List Impl.Effect) (w : World), (∀ f ∈ fx, f.isPut = false) →
      (Impl.applyEffects n c w fx).2 = true ∧
      (∀ n', (Impl.applyEffects n c w fx).1.store.get (.origin n') = w.store.get (.origin n')) ∧
      (Impl.applyEffects n c w fx).1.wire = sendsFold w.wire (sendsOfC fx) ∧
      w.store.next ≤ (Impl.applyEffects n c w fx).1.store.next ∧
      (SInv w.store → SInv (Impl.applyEffects n c w fx).1.store)
  | [], w, _ => ⟨rfl, fun _ => rfl, rfl, Nat.le_refl _, id⟩
  | f :: fs, w, h => by
      obtain ⟨w', hok, hget, hwire, hnext, hsinv⟩ := apply_noput (n := n) (c := c) (w := w)
        (h f (List.mem_cons_self ..))
      have ih := applyEffects_noput (n := n) (c := c) fs w' (fun g hg => h g (List.mem_cons_of_mem _ hg))
      simp only [Impl.applyEffects, hok]
      refine ⟨ih.1, ?_, ?_, ?_, ?_⟩
      · intro n'; rw [ih.2.1 n', hget n']
      · rw [ih.2.2.1, hwire]
        cases f with
        | send a m => rfl
        | putOrigin o => cases h _ (List.mem_cons_self ..)
        | armTimer dl => rfl
        | delTimer dl => rfl
      · exact Nat.le_trans hnext ih.2.2.2.1
      · exact fun hs => ih.2.2.2.2 (hsinv hs)

theorem applyEffects_append (n : String) (c : Cas.Cond) :
    ∀ (a b : List Impl.Effect) (w : World),
      Impl.applyEffects n c w (a ++ b) =
        if (Impl.applyEffects n c w a).2 then Impl.applyEffects n c (Impl.applyEffects n c w a).1 b
        else Impl.applyEffects n c w a
  | [], b, w => by simp [Impl.applyEffects]
  | f :: fs, b, w => by
      simp only [List.cons_append, Impl.applyEffects]
      split
      · exact applyEffects_append n c fs b _
      · simp

def TxnInv (st : Cas.Store Key Blob) (t : Txn) : Prop :=
  ∀ o v, t.snapshot = some (o, v) →
    v < st.next ∧ ∀ b, st.get (.origin t.origin) = some (b, v) → b = .origin o

theorem TxnInv.of_get_eq {st st' : Cas.Store Key Blob} {t : Txn}
    (hget : ∀ n', st'.get (.origin n') = st.get (.origin n')) (hnext : st.next ≤ st'.next)
    (h : TxnInv st t) : TxnInv st' t := by
  intro o v hs
  obtain ⟨h1, h2⟩ := h o v hs
  refine ⟨Nat.lt_of_lt_of_le h1 hnext, ?_⟩
  intro b hb
  rw [hget] at hb
  exact h2 b hb

theorem TxnInv.of_put {st st' : Cas.Store Key Blob} {n : String} {o : Origin} {c : Cas.Cond}
    {v' : Cas.Version} (hp : st.put (.origin n) (.origin o) c = .ok (st', v')) {t : Txn}
    (h : TxnInv st t) : TxnInv st' t := by
  intro o0 v hs
  obtain ⟨h1, h2⟩ := h o0 v hs
  obtain ⟨hv', hn⟩ := put_ok_next hp
  refine ⟨by rw [hn]; exact Nat.lt_succ_of_lt h1, ?_⟩
  intro b hb
  by_cases ho : t.origin = n
  · subst ho
    rw [Cas.get_put_same _ _ _ _ _ _ hp] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨_, hvv⟩ := hb
    have hv : v = st.next := hvv ▸ hv'
    rw [hv] at h1
    exact absurd h1 (Nat.lt_irrefl _)
  · rw [Cas.get_put_other _ _ _ _ _ _ _ hp (by simpa using ho)] at hb
    exact h2 b hb

def envOf (t : Txn) : Impl.Env := { origin := t.origin, snapshot := t.snapshot }

def decOf (t : Txn) (now : Nat) : Reply × Commit :=
  Impl.decide t.origin t.work now (envOf t).snap

def armed (t : Txn) (now : Nat) (w : World) : World :=
  (Impl.applyEffects t.origin (envOf t).cond w (Impl.armFx (decOf t now).2)).1

theorem envOf_origin (t : Txn) : (envOf t).origin = t.origin := rfl

theorem applyEffects_cons_put (n : String) (c : Cas.Cond) (w : World) (o : Origin)
    (fs : List Impl.Effect) :
    Impl.applyEffects n c w (.putOrigin o :: fs) =
      match w.store.put (.origin n) (.origin o) c with
      | .ok (st, _) => Impl.applyEffects n c { w with store := st } fs
      | .rejected   => (w, false) := by
  show (match (Impl.Effect.putOrigin o).apply n c w with
        | .ok w' => Impl.applyEffects n c w' fs
        | .rejected => (w, false)) = _
  simp only [Impl.Effect.apply]
  cases w.store.put (.origin n) (.origin o) c with
  | ok x => obtain ⟨st, v⟩ := x; rfl
  | rejected => rfl

theorem runC_transact (t : Txn) (now : Nat) (w : World) :
    Impl.runC (Impl.transact t.work now) (envOf t) w =
      match (armed t now w).store.put (.origin t.origin) (.origin (decOf t now).2.put)
              (envOf t).cond with
      | .ok (st, _) =>
          (some (decOf t now).1,
           (Impl.applyEffects t.origin (envOf t).cond { armed t now w with store := st }
             (Impl.delFx (decOf t now).2 ++ Impl.sendFx (decOf t now).2.send)).1)
      | .rejected => (none, armed t now w) := by
  have harm := applyEffects_noput (n := t.origin) (c := (envOf t).cond) _ w
    (armFx_noput (decOf t now).2)
  unfold Impl.runC
  rw [transact_apply]
  simp only [envOf_origin, List.append_assoc, List.singleton_append]
  rw [applyEffects_append]
  unfold decOf at harm
  unfold armed decOf
  simp only [harm.1, ↓reduceIte]
  generalize (Impl.applyEffects t.origin (envOf t).cond w
    (Impl.armFx (Impl.decide t.origin t.work now (envOf t).snap).2)).1 = w1
  simp only [List.cons_append, applyEffects_cons_put]
  cases hp : w1.store.put (.origin t.origin)
      (.origin (Impl.decide t.origin t.work now (envOf t).snap).2.put) (envOf t).cond with
  | ok x =>
    obtain ⟨st, v⟩ := x
    have hrest := applyEffects_noput (n := t.origin) (c := (envOf t).cond)
      (Impl.delFx (Impl.decide t.origin t.work now (envOf t).snap).2 ++
        Impl.sendFx (Impl.decide t.origin t.work now (envOf t).snap).2.send)
      { w1 with store := st }
      (by intro f hf
          simp only [List.mem_append] at hf
          rcases hf with hf | hf
          · exact delFx_noput _ f hf
          · exact sendFx_noput _ f hf)
    simp only [hrest.1, ↓reduceIte]
  | rejected => rfl

def TimerInv (w : World) : Prop :=
  ∀ (n : String) (d : Nat), d ∈ (current w n).deadlines → (w.store.get (.timer d n)).isSome = true

theorem apply_timer_keep {n : String} {c : Cas.Cond} {w w' : World} {f : Impl.Effect} {d : Nat}
    (hok : f.apply n c w = .ok w') (hf : f ≠ .delTimer d)
    (hs : (w.store.get (.timer d n)).isSome = true) :
    (w'.store.get (.timer d n)).isSome = true := by
  cases f with
  | putOrigin o =>
    simp only [Impl.Effect.apply] at hok
    split at hok
    · rename_i st v hp
      cases hok
      show (st.get (.timer d n)).isSome = true
      rw [Cas.get_put_other _ _ _ _ _ _ _ hp (by simp)]
      exact hs
    · cases hok
  | armTimer dl =>
    simp only [Impl.Effect.apply] at hok
    split at hok
    · rename_i st v hp
      cases hok
      show (st.get (.timer d n)).isSome = true
      by_cases hdl : dl = d
      · subst hdl
        rw [Cas.get_put_same _ _ _ _ _ _ hp]
        rfl
      · rw [Cas.get_put_other _ _ _ _ _ _ _ hp (by simp [Ne.symm hdl])]
        exact hs
    · cases hok
  | delTimer dl =>
    simp only [Impl.Effect.apply] at hok
    split at hok
    · rename_i st hp
      cases hok
      show (st.get (.timer d n)).isSome = true
      have hdl : dl ≠ d := fun h => hf (by rw [h])
      rw [Cas.get_del_other _ _ _ _ _ hp (by simp [Ne.symm hdl])]
      exact hs
    · cases hok
  | send a m =>
    cases hok
    exact hs

theorem apply_timer_other {n n' : String} {c : Cas.Cond} {w w' : World} {f : Impl.Effect} {d : Nat}
    (hok : f.apply n c w = .ok w') (hn : n' ≠ n) :
    w'.store.get (.timer d n') = w.store.get (.timer d n') := by
  cases f with
  | putOrigin o =>
    simp only [Impl.Effect.apply] at hok
    split at hok
    · rename_i st v hp
      cases hok
      exact Cas.get_put_other _ _ _ _ _ _ _ hp (by simp)
    · cases hok
  | armTimer dl =>
    simp only [Impl.Effect.apply] at hok
    split at hok
    · rename_i st v hp
      cases hok
      exact Cas.get_put_other _ _ _ _ _ _ _ hp (by simp [hn])
    · cases hok
  | delTimer dl =>
    simp only [Impl.Effect.apply] at hok
    split at hok
    · rename_i st hp
      cases hok
      exact Cas.get_del_other _ _ _ _ _ hp (by simp [hn])
    · cases hok
  | send a m =>
    cases hok
    rfl

theorem apply_arm {n : String} {c : Cas.Cond} {w w' : World} {d : Nat}
    (hok : (Impl.Effect.armTimer d).apply n c w = .ok w') :
    (w'.store.get (.timer d n)).isSome = true := by
  simp only [Impl.Effect.apply] at hok
  split at hok
  · rename_i st v hp
    cases hok
    show (st.get (.timer d n)).isSome = true
    rw [Cas.get_put_same _ _ _ _ _ _ hp]
    rfl
  · cases hok

theorem applyEffects_timer_keep {n : String} {c : Cas.Cond} {d : Nat} :
    ∀ (fx : List Impl.Effect) (w : World), (∀ f ∈ fx, f ≠ .delTimer d) →
      (w.store.get (.timer d n)).isSome = true →
      ((Impl.applyEffects n c w fx).1.store.get (.timer d n)).isSome = true
  | [], _, _, hs => hs
  | f :: fs, w, h, hs => by
      simp only [Impl.applyEffects]
      split
      · rename_i w' hok
        exact applyEffects_timer_keep fs w' (fun g hg => h g (List.mem_cons_of_mem _ hg))
          (apply_timer_keep hok (h f (List.mem_cons_self ..)) hs)
      · exact hs

theorem applyEffects_timer_other {n n' : String} {c : Cas.Cond} {d : Nat} (hn : n' ≠ n) :
    ∀ (fx : List Impl.Effect) (w : World),
      (Impl.applyEffects n c w fx).1.store.get (.timer d n') = w.store.get (.timer d n')
  | [], _ => rfl
  | f :: fs, w => by
      simp only [Impl.applyEffects]
      split
      · rename_i w' hok
        rw [applyEffects_timer_other hn fs w', apply_timer_other hok hn]
      · rfl

theorem applyEffects_arm {n : String} {c : Cas.Cond} {d : Nat} :
    ∀ (l : List Nat) (w : World), d ∈ l →
      ((Impl.applyEffects n c w (l.map .armTimer)).1.store.get (.timer d n)).isSome = true
  | [], _, h => by simp at h
  | x :: xs, w, h => by
      simp only [List.map_cons, Impl.applyEffects]
      split
      · rename_i w' hok
        rcases List.mem_cons.mp h with rfl | h
        · refine applyEffects_timer_keep _ w' ?_ (apply_arm hok)
          intro g hg
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp hg
          exact Impl.Effect.noConfusion
        · exact applyEffects_arm xs w' h
      · rename_i hrej
        obtain ⟨w', hok, _⟩ := apply_noput (n := n) (c := c) (w := w) (f := .armTimer x) rfl
        rw [hok] at hrej
        cases hrej

theorem armFx_nodel (c : Commit) (d : Nat) : ∀ f ∈ Impl.armFx c, f ≠ .delTimer d := by
  intro f hf
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hf
  exact Impl.Effect.noConfusion

theorem commit_arm_or_old {old : Origin} {tx : Impl.Tx} {d : Nat}
    (hd : d ∈ (Impl.Tx.commit old tx).put.deadlines) :
    d ∈ (Impl.Tx.commit old tx).arm ∨ d ∈ old.deadlines := by
  simp only [Impl.Tx.commit] at hd ⊢
  by_cases h : d ∈ old.deadlines
  · exact Or.inr h
  · left
    rw [List.mem_filter]
    exact ⟨hd, by simpa using h⟩

theorem commit_del_not {old : Origin} {tx : Impl.Tx} {d : Nat}
    (hd : d ∈ (Impl.Tx.commit old tx).put.deadlines) : d ∉ (Impl.Tx.commit old tx).del := by
  simp only [Impl.Tx.commit] at hd ⊢
  rw [List.mem_filter]
  intro ⟨_, h⟩
  simp at h
  exact h hd

theorem tail_nodel {old : Origin} {tx : Impl.Tx} {d : Nat}
    (hd : d ∈ (Impl.Tx.commit old tx).put.deadlines) :
    ∀ f ∈ Impl.delFx (Impl.Tx.commit old tx) ++ Impl.sendFx (Impl.Tx.commit old tx).send,
      f ≠ .delTimer d := by
  intro f hf
  rw [List.mem_append] at hf
  rcases hf with hf | hf
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hf
    intro heq
    cases heq
    exact commit_del_not hd hx
  · obtain ⟨⟨a, m⟩, _, rfl⟩ := List.mem_map.mp hf
    exact Impl.Effect.noConfusion

theorem decOf_shape (t : Txn) (now : Nat) :
    ∃ tx, (decOf t now).2 = Impl.Tx.commit (envOf t).snap tx := by
  unfold decOf
  cases t.work with
  | request rq => exact ⟨_, rfl⟩
  | sweep fired => exact ⟨_, rfl⟩

end Commit
