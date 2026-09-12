import «03-theorems».«liveness»

namespace Abstract

open Protocol Abstract


private def idOf (suffix : String) : Ident := { origin := "o", suffix := suffix }

private def promiseWith (type : OType) : PromiseObject :=
  { state := .pending, param := {}, type := type, timeoutAt := 9000, createdAt := 0 }

private def objectWith (suffix : String) (type : OType) (task : Option TaskObject) : Object :=
  { id := idOf suffix, promise := promiseWith type, task := task }

private def state : State :=
  { objects := [ objectWith "root" (.runnable "poll://any@w") (some { state := .acquired, version := 1 })
               , objectWith "runnable" (.runnable "poll://any@w") (some { state := .pending, version := 0 })
               , objectWith "external" .external none
               , objectWith "internal" .internal none ] }

private def callbackStatus (awaited : String) : Nat :=
  (run true (promiseRegisterCallback
      { awaited := idOf awaited, awaiter := idOf "root" } 100) state).1.status

private def listenerStatus (awaited : String) : Nat :=
  (run true (promiseRegisterListener
      { awaited := idOf awaited, address := "poll://any@w" } 100) state).1.status

theorem callback_admits_runnable : callbackStatus "runnable" = 200 := by rfl
theorem callback_admits_external : callbackStatus "external" = 200 := by rfl
theorem callback_refuses_internal : callbackStatus "internal" = 422 := by rfl

theorem listener_admits_runnable : listenerStatus "runnable" = 200 := by rfl
theorem listener_admits_external : listenerStatus "external" = 200 := by rfl
theorem listener_refuses_internal : listenerStatus "internal" = 422 := by rfl

private def latePromise (type : OType) : PromiseObject :=
  { state := .pending, param := {}, type := type, timeoutAt := 50, createdAt := 0 }

private def lateState : State :=
  { objects := [ { id := idOf "runnable", promise := latePromise (.runnable "poll://any@w"),
                   task := some { state := .pending, version := 0 } }
               , { id := idOf "external", promise := latePromise .external }
               , { id := idOf "internal", promise := latePromise .internal } ] }

private def armed (suffix : String) : Bool :=
  enabledInternal (.internal (.promiseTimeout { id := idOf suffix })) 100 lateState

theorem arms_a_runnable_deadline : armed "runnable" = true := by rfl
theorem arms_an_external_deadline : armed "external" = true := by rfl
theorem arms_no_internal_deadline : armed "internal" = false := by rfl

end Abstract
