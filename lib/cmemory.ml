open Gillian.Concrete
module Literal = Gillian.Gil_syntax.Literal
module Expr = Gillian.Gil_syntax.Expr
module MemMap = Map.Make (String)
open Gillian.Utils.Syntaxes.Result

type vt = Values.t
type st = Subst.t

type err_t = MissingOffset | MissingObject | DuplicatedResource | OutOfBounds
[@@deriving show]

module Object = struct
  module OffsetMap = Map.Make (Int)

  type t = { data : vt OffsetMap.t; bound : int option }

  let pp ft t =
    let open Fmt in
    let pp_props =
      braces
        (iter_bindings ~sep:comma OffsetMap.iter
           (pair ~sep:(any ": ") int Values.pp))
    in
    let pp_domain = option int in
    pf ft "%a |@ %a" pp_props t.data pp_domain t.bound

  let new_ n =
    let data = OffsetMap.empty in
    let data =
      List.fold_left
        (fun acc (i, x) -> OffsetMap.add i x acc)
        data
        (List.init n (fun i -> (i, Literal.Int Z.zero)))
    in
    let bound = Some n in
    { data; bound }

  let load ~obj offset =
    match OffsetMap.find_opt offset obj.data with
    | Some v -> Ok v
    | None -> (
        match obj.bound with
        | None -> Error MissingOffset
        | Some bound ->
            if offset >= bound then Error OutOfBounds else Error MissingOffset)

  let store ~(obj : t) offset value =
    match OffsetMap.find_opt offset obj.data with
    | Some _ ->
        let new_props = OffsetMap.add offset value obj.data in
        Ok { obj with data = new_props }
    | None -> (
        match obj.bound with
        | None -> Error MissingOffset
        | Some bound ->
            if offset <= bound then Error MissingOffset else Error OutOfBounds)

  let get_cell = load

  let set_cell ~obj offset value =
    match OffsetMap.find_opt offset obj.data with
    | Some _ -> Error DuplicatedResource
    | None -> (
        match obj.bound with
        | None ->
            let new_data = OffsetMap.add offset value obj.data in
            Ok { obj with data = new_data }
        | Some bound ->
            if offset <= bound then
              let new_props = OffsetMap.add offset value obj.data in
              Ok { obj with data = new_props }
            else Error DuplicatedResource)

  let rem_cell ~obj offset =
    match OffsetMap.find_opt offset obj.data with
    | Some _ ->
        let new_props = OffsetMap.remove offset obj.data in
        let new_obj = { obj with data = new_props } in
        Ok new_obj
    | None -> (
        match obj.bound with
        | None -> Error MissingOffset
        | Some bound ->
            if offset <= bound then Error MissingOffset else Error OutOfBounds)
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
  | [ Literal.Int size ] ->
      let size = Z.to_int size in
      let new_loc = Gillian.Utils.Generators.fresh_loc () in
      let new_mem = MemMap.add new_loc (Object.new_ size) mem in
      Ok (new_mem, [ Literal.Loc new_loc; Literal.Int Z.zero ])
  | _ -> failwith "invalid parameters for alloc"

let execute_store (mem : t) (args : Literal.t list) =
  match args with
  | [ Loc loc; Int offset; value ] -> (
      match MemMap.find_opt loc mem with
      | None -> Error MissingObject
      | Some obj ->
          let offset = Z.to_int offset in
          let+ new_obj = Object.store ~obj offset value in
          let new_mem = MemMap.add loc new_obj mem in
          (new_mem, []))
  | _ -> failwith "invalid parameters for store"

let execute_load (mem : t) (args : Literal.t list) =
  match args with
  | [ Loc loc; Int offset ] -> (
      match MemMap.find_opt loc mem with
      | None -> Error MissingObject
      | Some obj ->
          let offset = Z.to_int offset in
          let+ value = Object.load ~obj offset in
          (mem, [ value ]))
  | _ -> failwith "invalid parameters for load"

let execute_get_cell (mem : t) (args : Literal.t list) =
  match args with
  | [ Loc loc; Int offset ] -> (
      match MemMap.find_opt loc mem with
      | None -> Error MissingObject
      | Some obj ->
          let offset = Z.to_int offset in
          let+ value = Object.load ~obj offset in
          (mem, [ Literal.Loc loc; Int (Z.of_int offset); value ]))
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
