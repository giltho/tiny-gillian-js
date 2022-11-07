open Gillian.Symbolic
open Gillian.Gil_syntax
module SS = Gillian.Utils.Containers.SS
module DR = Gillian.Monadic.Delayed_result
module Delayed = Gillian.Monadic.Delayed
open Gillian.Utils.Prelude

type init_data = unit

type vt = Values.t
(** Type of GIL values *)

type st = Subst.t
(** Type of GIL substitutions *)

type c_fix_t = unit

type err_t =
  | MissingOffset
  | MissingObject
  | DuplicatedResource
  | OutOfBounds
  | InvalidLocation of Expr.t
  | UseAfterFree

module Object = struct
  module OffsetMap = Expr.Map

  type t = { data : Expr.t OffsetMap.t; bound : Expr.t option }
  [@@deriving yojson]

  let substitution subst obj =
    let subst_expr = Subst.subst_in_expr subst ~partial:true in
    let new_data =
      OffsetMap.fold
        (fun k v acc -> OffsetMap.add (subst_expr k) (subst_expr v) acc)
        obj.data OffsetMap.empty
    in
    let new_bound = Option.map subst_expr obj.bound in
    { data = new_data; bound = new_bound }

  let union o1 o2 =
    let data = OffsetMap.union (fun _ v1 _ -> Some v1) o1.data o2.data in
    let bound =
      match (o1.bound, o2.bound) with
      | None, Some b | Some b, None | Some b, Some _ -> Some b
      | None, None -> None
    in
    { data; bound }

  let empty = { data = OffsetMap.empty; bound = None }

  let lvars t =
    OffsetMap.fold
      (fun x y acc -> SS.union (Expr.lvars x) (SS.union (Expr.lvars y) acc))
      t.data
      (Option.fold ~none:SS.empty ~some:Expr.lvars t.bound)

  let alocs t =
    OffsetMap.fold
      (fun x y acc -> SS.union (Expr.alocs x) (SS.union (Expr.alocs y) acc))
      t.data
      (Option.fold ~none:SS.empty ~some:Expr.alocs t.bound)

  let pp ft t =
    let open Fmt in
    let pp_props =
      braces
        (iter_bindings ~sep:comma OffsetMap.iter
           (pair ~sep:(any ": ") Expr.pp Expr.pp))
    in
    let pp_bound = option Expr.pp in
    pf ft "%a |@ %a" pp_props t.data pp_bound t.bound

  let new_ (n : int) =
    let data = OffsetMap.empty in
    let data =
      List.fold_left
        (fun acc (i, x) -> OffsetMap.add i x acc)
        data
        (List.init n (fun i -> (Expr.int i, Expr.zero_i)))
    in
    let bound = Some (Expr.int n) in
    { data; bound }

  let load ~obj offset =
    let open DR.Syntax in
    let open Delayed.Syntax in
    let* offset = Delayed.reduce offset in
    let** () =
      match obj.bound with
      | Some bound ->
          if%sat Formula.Infix.(bound #<= offset) then DR.error OutOfBounds
          else DR.ok ()
      | None -> DR.ok ()
    in
    match OffsetMap.find_opt offset obj.data with
    | Some value -> DR.ok value
    | None ->
        let bindings = OffsetMap.bindings obj.data in
        let rec aux = function
          | [] -> DR.error MissingOffset
          | (o, v) :: r ->
              if%sat Formula.Infix.(o #== offset) then DR.ok v else aux r
        in
        aux bindings

  let store ~obj offset value =
    let open DR.Syntax in
    let open Delayed.Syntax in
    let* offset = Delayed.reduce offset in
    let** () =
      match obj.bound with
      | Some bound ->
          if%sat Formula.Infix.(bound #<= offset) then DR.error OutOfBounds
          else DR.ok ()
      | None -> DR.ok ()
    in
    match OffsetMap.find_opt offset obj.data with
    | Some _ ->
        let new_map = OffsetMap.add offset value obj.data in
        DR.ok { obj with data = new_map }
    | None ->
        let bindings = OffsetMap.bindings obj.data in
        let rec aux = function
          | [] -> DR.error MissingOffset
          | (o, _) :: r ->
              if%sat Formula.Infix.(o #== offset) then
                let map_without = OffsetMap.remove o obj.data in
                let map_with = OffsetMap.add offset value map_without in
                DR.ok { obj with data = map_with }
              else aux r
        in
        aux bindings
end

type obj_or_freed = Obj of Object.t | Freed [@@deriving yojson]

let get_obj = function Obj o -> DR.ok o | Freed -> DR.error UseAfterFree

module MemMap = Map.Make (struct
  include String

  let of_yojson = [%of_yojson: string]
  let to_yojson = [%to_yojson: string]
end)

type t = obj_or_freed MemMap.t [@@deriving yojson]
(** Type of GIL general states *)

type action_ret = Success of (t * vt list) | Failure of err_t

(** Initialisation *)
let init () = MemMap.empty

let clear _ = MemMap.empty

let resolve_loc_result loc =
  Gillian.Monadic.Delayed_result.of_do ~none:(InvalidLocation loc)
    (Delayed.resolve_loc loc)

let pp : t Fmt.t =
  let open Fmt in
  let pp_obj_or_freed ft = function
    | Obj o -> Object.pp ft o
    | Freed -> string ft "FREED"
  in
  vbox
    (iter_bindings ~sep:(any "@ @ ") MemMap.iter
       (hvbox (pair ~sep:(any "-> ") string pp_obj_or_freed)))

let execute_alloc (mem : t) args =
  match args with
  | [ Expr.Lit (Int size) ] ->
      let size = Z.to_int size in
      let new_loc = ALoc.alloc () in
      let new_mem = MemMap.add new_loc (Obj (Object.new_ size)) mem in
      DR.ok (new_mem, [ Expr.ALoc new_loc; Expr.zero_i ])
  | _ -> failwith "invalid parameters for alloc"

let execute_load (mem : t) (args : Expr.t list) =
  let open DR.Syntax in
  match args with
  | [ loc; offset ] -> (
      let** loc_name = resolve_loc_result loc in
      match MemMap.find_opt loc_name mem with
      | None -> DR.error MissingObject
      | Some obj ->
          let** obj = get_obj obj in
          let++ value = Object.load ~obj offset in
          (mem, [ value ]))
  | _ -> failwith "invalid parameters for load"

let execute_store (mem : t) (args : Expr.t list) =
  let open DR.Syntax in
  match args with
  | [ loc; offset; value ] -> (
      let** loc_name = resolve_loc_result loc in
      match MemMap.find_opt loc_name mem with
      | None -> DR.error MissingObject
      | Some obj ->
          let** obj = get_obj obj in
          let++ new_obj = Object.store ~obj offset value in
          let new_obj = Obj new_obj in
          let new_mem = MemMap.add loc_name new_obj mem in
          (new_mem, []))
  | _ -> failwith "invalid parameters for load"

(** Execute action *)
let execute_action ~action_name memory arguments =
  let res =
    match action_name with
    | "alloc" -> execute_alloc memory arguments
    | "load" -> execute_load memory arguments
    | "store" -> execute_store memory arguments
    | _ -> Fmt.failwith "unknown action %s" action_name
  in
  Delayed.map res (function Ok res -> Success res | Error e -> Failure e)

let ga_to_getter = function
  | "cell" -> "get_cell"
  | "bound" -> "get_bound"
  | _ -> failwith "unknown core predicate"

let ga_to_setter = function
  | "cell" -> "set_cell"
  | "bound" -> "set_bound"
  | _ -> failwith "unknown core predicate"

let ga_to_deleter = function
  | "cell" -> "rem_cell"
  | "bound" -> "rem_bound"
  | _ -> failwith "unknown core predicate"

let is_overlapping_asrt _ = false

let merge_loc (heap : t) new_loc old_loc =
  let old_block, new_block =
    (MemMap.find_opt old_loc heap, MemMap.find_opt new_loc heap)
  in
  match (old_block, new_block) with
  | Some Freed, Some Freed -> MemMap.remove old_loc heap
  | None, Some Freed -> heap
  | Some Freed, None ->
      let with_new_loc = MemMap.add new_loc Freed heap in
      MemMap.add old_loc Freed with_new_loc
  | _, _ -> (
      let old_block = Option.value ~default:(Obj Object.empty) old_block in
      let new_block = Option.value ~default:(Obj Object.empty) new_block in
      match (old_block, new_block) with
      | _, Freed | Freed, _ -> failwith "merging non-freed and freed block"
      | Obj old, Obj new_ ->
          let data = Object.union new_ old in
          let with_new = MemMap.add new_loc (Obj data) heap in
          MemMap.remove old_loc with_new)

let substitution_in_place subst heap =
  (* First we replace in the offset and values using fvl *)
  let with_blocs =
    MemMap.map
      (fun obj ->
        match obj with
        | Freed -> obj
        | Obj o -> Obj (Object.substitution subst o))
      heap
  in
  (* Then we replace within the locations themselves *)
  let aloc_subst =
    Subst.filter subst (fun var _ ->
        match var with ALoc _ -> true | _ -> false)
  in
  let with_merged =
    Subst.fold aloc_subst
      (fun aloc new_loc acc ->
        let aloc =
          match aloc with
          | ALoc loc -> loc
          | _ -> raise (Failure "Impossible by construction")
        in
        let new_loc_str =
          match new_loc with
          | Expr.Lit (Literal.Loc loc) -> loc
          | Expr.ALoc loc -> loc
          | _ -> Fmt.failwith "Heap susbtitution failure"
        in
        merge_loc acc new_loc_str aloc)
      with_blocs
  in
  Delayed.return with_merged

let fresh_val _ = Expr.LVar (LVar.alloc ())

let clean_up ?(keep = Expr.Set.empty) _ : Expr.Set.t * Expr.Set.t =
  (Expr.Set.empty, keep)

let lvars mem =
  MemMap.fold
    (fun _ v acc ->
      match v with Freed -> acc | Obj o -> SS.union (Object.lvars o) acc)
    mem SS.empty

let alocs mem =
  MemMap.fold
    (fun k v acc ->
      let acc =
        if Gillian.Utils.Names.is_aloc_name k then SS.add k acc else acc
      in
      match v with Freed -> acc | Obj o -> SS.union (Object.alocs o) acc)
    mem SS.empty

let assertions ?to_keep:_ _mem = failwith "implement assertions"
let mem_constraints t = []
let pp_c_fix _ _ = ()
let get_recovery_vals mem err = failwith "implement recovery vals"
let pp_err _ _ = ()
let get_failing_constraint _ = failwith "implement get_failing_constraint"
let get_fixes ?simple_fix:_ _ _ _ _ = []
let apply_fix _ _ _ = failwith "implement apply_fix"
let pp_by_need _ = pp
let get_print_info _ _ = (SS.empty, SS.empty)
let copy mem = mem