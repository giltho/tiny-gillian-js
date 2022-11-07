open Gillian.Concrete
module Literal = Gillian.Gil_syntax.Literal
module Expr = Gillian.Gil_syntax.Expr
module MemMap = Map.Make (String)
open Gillian.Utils.Syntaxes.Result

type vt = Values.t
type st = Subst.t
type err_t = MissingProp | MissingObject | DuplicatedProp [@@deriving show]

module Object = struct
  module PropMap = Map.Make (String)
  module Domain = Set.Make (String)

  type t = { props : vt PropMap.t; domain : Domain.t option }

  let pp ft t =
    let open Fmt in
    let pp_props =
      braces
        (iter_bindings ~sep:comma PropMap.iter
           (pair ~sep:(any ": ") string Values.pp))
    in
    let pp_domain = option (braces (iter ~sep:comma Domain.iter string)) in
    pf ft "%a |@ %a" pp_props t.props pp_domain t.domain

  let empty = { props = PropMap.empty; domain = Some Domain.empty }

  let load ~obj prop =
    match PropMap.find_opt prop obj.props with
    | Some v -> Ok v
    | None -> (
        match obj.domain with
        | None -> Error MissingProp
        | Some domain ->
            if Domain.mem prop domain then Error MissingProp else Ok Nono)

  let store ~(obj : t) prop value =
    match PropMap.find_opt prop obj.props with
    | Some _ ->
        let new_props = PropMap.add prop value obj.props in
        Ok { obj with props = new_props }
    | None -> (
        match obj.domain with
        | None -> Error MissingProp
        | Some domain ->
            if Domain.mem prop domain then Error MissingProp
            else
              let new_domain = Domain.add prop domain in
              let new_props = PropMap.add prop value obj.props in
              Ok { props = new_props; domain = Some new_domain })

  let get_cell = load

  let set_cell ~obj prop value =
    match PropMap.find_opt prop obj.props with
    | Some _ -> Error DuplicatedProp
    | None -> (
        match obj.domain with
        | None ->
            let new_props = PropMap.add prop value obj.props in
            Ok { obj with props = new_props }
        | Some domain ->
            if Domain.mem prop domain then
              let new_props = PropMap.add prop value obj.props in
              Ok { obj with props = new_props }
            else Error DuplicatedProp)

  let rem_cell ~obj prop =
    match PropMap.find_opt prop obj.props with
    | Some _ ->
        let new_props = PropMap.remove prop obj.props in
        let new_obj = { obj with props = new_props } in
        Ok new_obj
    | None -> (
        match obj.domain with
        | None -> Error MissingProp
        | Some domain ->
            if Domain.mem prop domain then Error MissingProp
            else
              let new_domain = Domain.add prop domain in
              let new_obj = { obj with domain = Some new_domain } in
              Ok new_obj)
end

type t = Object.t MemMap.t

let pp =
  let open Fmt in
  vbox
    (iter_bindings ~sep:(any "@ @ ") MemMap.iter
       (hvbox (pair ~sep:(any "-> ") string Object.pp)))

type init_data = unit

let init () = MemMap.empty
let copy t = t

let execute_alloc (mem : t) args =
  match args with
  | [] ->
      let new_loc = Gillian.Utils.Generators.fresh_loc () in
      let new_mem = MemMap.add new_loc Object.empty mem in
      Ok (new_mem, [ Literal.Loc new_loc ])
  | _ -> failwith "invalid parameters for alloc"

let execute_store (mem : t) (args : Literal.t list) =
  match args with
  | [ Loc loc; String prop; value ] -> (
      match MemMap.find_opt loc mem with
      | None -> Error MissingObject
      | Some obj ->
          let+ new_obj = Object.store ~obj prop value in
          let new_mem = MemMap.add loc new_obj mem in
          (new_mem, []))
  | _ -> failwith "invalid parameters for store"

let execute_load (mem : t) (args : Literal.t list) =
  match args with
  | [ Loc loc; String prop ] -> (
      match MemMap.find_opt loc mem with
      | None -> Error MissingObject
      | Some obj ->
          let+ value = Object.load ~obj prop in
          (mem, [ value ]))
  | _ -> failwith "invalid parameters for load"

type action_ret = ASucc of (t * vt list) | AFail of err_t list

let lift_ret = function Ok x -> ASucc x | Error err -> AFail [ err ]

let execute_action name mem params =
  lift_ret
  @@
  match name with
  | "alloc" -> execute_alloc mem params
  | "store" -> execute_store mem params
  | "load" -> execute_load mem params
  | _ -> Fmt.failwith "unknown action %s" name

let pp_err = pp_err_t
