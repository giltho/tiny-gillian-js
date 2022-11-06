open Gillian.Concrete
module Literal = Gillian.Gil_syntax.Literal
module Expr = Gillian.Gil_syntax.Expr

type vt = Values.t

type st = Subst.t
type err_t = unit [@@deriving yojson]

type t = unit [@@deriving yojson]

type init_data = unit

let init () = ()

let copy () = ()
type action_ret = ASucc of (t * vt list) | AFail of err_t list

let execute_action _ _ _ = failwith "Implement here"

let pp _ _ = ()

let pp_err _ _ = ()