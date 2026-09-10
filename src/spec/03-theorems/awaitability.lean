import «03-theorems».«liveness»

namespace Abstract

open ServerModel AbstractModel

private def targetTags : Tags := [("resonate:target", "poll://any@w")]
private def externalTags : Tags := [("resonate:external", "true")]
private def internalTags : Tags := []

private def idOf (suffix : String) : Ident := { origin := "o", suffix := suffix }

private def promiseWith (tags : Tags) : PromiseObject :=
  { state := .pending, param := {}, tags := tags, timeoutAt := 9000, createdAt := 0 }

private def objectWith (suffix : String) (tags : Tags) (task : Option TaskObject) : Object :=
  { id := idOf suffix, promise := promiseWith tags, task := task }

private def state : ServerState :=
  { objects := [ objectWith "root" targetTags (some { state := .acquired, version := 1 })
               , objectWith "runnable" targetTags (some { state := .pending, version := 0 })
               , objectWith "external" externalTags none
               , objectWith "internal" internalTags none ] }

private def callbackStatus (awaited : String) : Nat :=
  (run true (promiseRegisterCallback
      { awaited := idOf awaited, awaiter := idOf "root" } 100) state).1.status

private def listenerStatus (awaited : String) : Nat :=
  (run true (promiseRegisterListener
      { awaited := idOf awaited, address := "poll://any@w" } 100) state).1.status

theorem otype_of_targeted : Tags.otype targetTags = .runnable := by rfl
theorem otype_of_external : Tags.otype externalTags = .external := by rfl
theorem otype_of_neither : Tags.otype internalTags = .internal := by rfl

theorem callback_admits_runnable : callbackStatus "runnable" = 200 := by rfl
theorem callback_admits_external : callbackStatus "external" = 200 := by rfl
theorem callback_refuses_internal : callbackStatus "internal" = 422 := by rfl

theorem listener_admits_runnable : listenerStatus "runnable" = 200 := by rfl
theorem listener_admits_external : listenerStatus "external" = 200 := by rfl
theorem listener_refuses_internal : listenerStatus "internal" = 422 := by rfl

private def latePromise (tags : Tags) : PromiseObject :=
  { state := .pending, param := {}, tags := tags, timeoutAt := 50, createdAt := 0 }

private def lateState : ServerState :=
  { objects := [ { id := idOf "runnable", promise := latePromise targetTags,
                   task := some { state := .pending, version := 0 } }
               , { id := idOf "external", promise := latePromise externalTags }
               , { id := idOf "internal", promise := latePromise internalTags } ] }

private def armed (suffix : String) : Bool :=
  enabledInternal (.internal (.promiseTimeout { id := idOf suffix })) 100 lateState

theorem arms_a_runnable_deadline : armed "runnable" = true := by rfl
theorem arms_an_external_deadline : armed "external" = true := by rfl
theorem arms_no_internal_deadline : armed "internal" = false := by rfl

end Abstract
