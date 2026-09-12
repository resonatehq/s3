import impl.relation

namespace Refinement

theorem step_sim (H : Concrete.Hasher) (ev : Concrete.Event) (now : Nat)
    (s : Concrete.State) (S : Abstract.State)
    (inv : Inv s) (rel : Equiv (abstract s) S) :
    Inv (Concrete.step H ev now s).2 ∧
    Equiv (abstract (Concrete.step H ev now s).2)
          (Abstract.exec false ((events ev now s).map (·, now)) S).2 ∧
    observations now (events ev now s) (Abstract.exec false ((events ev now s).map (·, now)) S).1 =
      (Concrete.Frame.observe ⟨s, ev, (Concrete.step H ev now s).1, now⟩).toList :=
  sorry

theorem refines (H : Concrete.Hasher) (tr : Concrete.Trace)
    (valid : Concrete.Valid H tr) (init : (tr 0).state = Concrete.State.init) :
    ∃ tr' : Abstract.Trace,
      Abstract.Valid false tr' ∧
      (tr' 0).state = Abstract.State.init ∧
      ∀ k o, Concrete.nth tr k o ↔ Abstract.nth tr' k o :=
  sorry

end Refinement
