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
  | MissingOffset of (string * vt)
  | MissingObject of string
  | MissingBound of string
  | DuplicatedResource
  | OutOfBounds
  | InvalidLocation of Expr.t
  | UseAfterFree
  | NotFreed

module Object = struct
  module OffsetMap = Expr.Map

  type t = { data : Expr.t OffsetMap.t; bound : Expr.t option }
  [@@deriving yojson]

  let assertion ~loc obj =
    let cells =
      OffsetMap.to_seq obj.data
      |> Seq.map (fun (ofs, value) -> Asrt.GA ("cell", [ loc; ofs ], [ value ]))
    in
    match obj.bound with
    | None -> cells
    | Some b -> Seq.cons (Asrt.GA ("bound", [ loc ], [ b ])) cells

  let is_empty o = OffsetMap.is_empty o.data && Option.is_none o.bound

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

  let one_cell offset value =
    let data = OffsetMap.singleton offset value in
    let bound = None in
    { data; bound }

  let just_bound bound =
    let data = OffsetMap.empty in
    let bound = Some bound in
    { data; bound }

  let load ~loc ~obj offset =
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
          | [] -> DR.error (MissingOffset (loc, offset))
          | (o, v) :: r ->
              if%sat Formula.Infix.(o #== offset) then DR.ok v else aux r
        in
        aux bindings

  let store ~loc ~obj offset value =
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
          | [] -> DR.error (MissingOffset (loc, offset))
          | (o, _) :: r ->
              if%sat Formula.Infix.(o #== offset) then
                (* We just learned that o == offset.
                   We'll use the most reduced version and write it back *)
                let* reduced = Delayed.reduce o in
                if reduced != o then
                  let map_without = OffsetMap.remove o obj.data in
                  let map_with = OffsetMap.add reduced value map_without in
                  DR.ok { obj with data = map_with }
                else
                  let new_map = OffsetMap.add reduced value obj.data in
                  DR.ok { obj with data = new_map }
              else aux r
        in
        aux bindings

  let set_cell ~obj offset value =
    let open DR.Syntax in
    let open Delayed.Syntax in
    let* offset = Delayed.reduce offset in
    let** () =
      match obj.bound with
      | Some bound ->
          if%sat Formula.Infix.(bound #<= offset) then
            DR.error DuplicatedResource
          else DR.ok ()
      | None -> DR.ok ()
    in
    match OffsetMap.find_opt offset obj.data with
    | Some _ -> DR.error DuplicatedResource
    | None ->
        let bindings = OffsetMap.bindings obj.data in
        let rec aux = function
          | [] -> DR.ok { obj with data = OffsetMap.add offset value obj.data }
          | (o, _) :: r ->
              if%sat Formula.Infix.(o #== offset) then
                DR.error DuplicatedResource
              else aux r
        in
        aux bindings

  let rem_cell ~loc ~obj offset =
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
    | Some _ -> DR.ok { obj with data = OffsetMap.remove offset obj.data }
    | None ->
        let bindings = OffsetMap.bindings obj.data in
        let rec aux = function
          | [] -> DR.error (MissingOffset (loc, offset))
          | (o, _) :: r ->
              if%sat Formula.Infix.(o #== offset) then
                DR.ok { obj with data = OffsetMap.remove o obj.data }
              else aux r
        in
        aux bindings

  let get_bound ~loc ~obj =
    match obj.bound with Some b -> Ok b | None -> Error (MissingBound loc)

  let set_bound ~obj bound =
    match obj.bound with
    | None -> Ok { obj with bound = Some bound }
    | _ -> Error DuplicatedResource

  let rem_bound ~loc ~obj =
    match obj.bound with
    | Some b -> Ok { obj with bound = None }
    | None -> Error (MissingBound loc)
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

let resolve_or_create_loc_name (lvar_loc : Expr.t) : string Delayed.t =
  let open Delayed.Syntax in
  let* loc_name = Delayed.resolve_loc lvar_loc in
  match loc_name with
  | None ->
      let new_loc_name = ALoc.alloc () in
      let learned = [ Formula.Eq (ALoc new_loc_name, lvar_loc) ] in
      Logging.verbose (fun fmt ->
          fmt "Couldn't resolve loc %a, created %s" Expr.pp lvar_loc
            new_loc_name);
      Delayed.return ~learned new_loc_name
  | Some l ->
      Logging.verbose (fun fmt -> fmt "Resolved %a as %s" Expr.pp lvar_loc l);
      Delayed.return l

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
      | None -> DR.error (MissingObject loc_name)
      | Some obj ->
          let** obj = get_obj obj in
          let++ value = Object.load ~loc:loc_name ~obj offset in
          (mem, [ value ]))
  | _ -> failwith "invalid parameters for load"

let execute_get_cell (mem : t) (args : Expr.t list) =
  let open DR.Syntax in
  match args with
  | [ loc; offset ] -> (
      let** loc_name = resolve_loc_result loc in
      match MemMap.find_opt loc_name mem with
      | None -> DR.error (MissingObject loc_name)
      | Some obj ->
          let** obj = get_obj obj in
          let++ value = Object.load ~loc:loc_name ~obj offset in
          (mem, [ Expr.loc_from_loc_name loc_name; offset; value ]))
  | _ -> failwith "invalid parameters for get_cell"

let execute_get_bound (mem : t) (args : Expr.t list) =
  let open DR.Syntax in
  match args with
  | [ loc ] -> (
      let** loc_name = resolve_loc_result loc in
      match MemMap.find_opt loc_name mem with
      | None -> DR.error (MissingObject loc_name)
      | Some obj ->
          let+* obj = get_obj obj in
          Result.map
            (fun bound -> (mem, [ Expr.loc_from_loc_name loc_name; bound ]))
            (Object.get_bound ~loc:loc_name ~obj))
  | _ -> failwith "invalid parameters for get_bound"

let execute_set_cell (mem : t) (args : Expr.t list) =
  let open DR.Syntax in
  let open Delayed.Syntax in
  match args with
  | [ loc; offset; value ] -> (
      let* loc_name = resolve_or_create_loc_name loc in
      match MemMap.find_opt loc_name mem with
      | None ->
          let+ offset = Delayed.reduce offset in
          let new_obj = Obj (Object.one_cell offset value) in
          let new_mem = MemMap.add loc_name new_obj mem in
          Ok (new_mem, [])
      | Some obj ->
          let** obj = get_obj obj in
          let++ new_object = Object.set_cell ~obj offset value in
          let new_mem = MemMap.add loc_name (Obj new_object) mem in
          (new_mem, []))
  | _ -> failwith "invalid parameters for set_cell"

let execute_set_bound (mem : t) (args : Expr.t list) =
  let open DR.Syntax in
  let open Delayed.Syntax in
  match args with
  | [ loc; bound ] -> (
      let* loc_name = resolve_or_create_loc_name loc in
      let* bound = Delayed.reduce bound in
      match MemMap.find_opt loc_name mem with
      | None ->
          let new_obj = Obj (Object.just_bound bound) in
          let new_mem = MemMap.add loc_name new_obj mem in
          DR.ok (new_mem, [])
      | Some obj -> (
          let+* obj = get_obj obj in
          match Object.set_bound ~obj bound with
          | Ok new_object ->
              let new_mem = MemMap.add loc_name (Obj new_object) mem in
              Ok (new_mem, [])
          | Error _ as e -> e))
  | _ -> failwith "invalid parameters for set_bound"

let execute_rem_cell (mem : t) (args : Expr.t list) =
  let open DR.Syntax in
  match args with
  | [ loc; offset ] -> (
      let** loc_name = resolve_loc_result loc in
      match MemMap.find_opt loc_name mem with
      | None -> DR.error (MissingObject loc_name)
      | Some obj ->
          let** obj = get_obj obj in
          let++ new_object = Object.rem_cell ~loc:loc_name ~obj offset in
          if Object.is_empty new_object then (MemMap.remove loc_name mem, [])
          else
            let new_mem = MemMap.add loc_name (Obj new_object) mem in
            (new_mem, []))
  | _ -> failwith "invalid parameters for ret_cell"

let execute_rem_bound (mem : t) (args : Expr.t list) =
  let open DR.Syntax in
  match args with
  | [ loc ] -> (
      let** loc_name = resolve_loc_result loc in
      match MemMap.find_opt loc_name mem with
      | None -> DR.error (MissingObject loc_name)
      | Some obj -> (
          let+* obj = get_obj obj in
          match Object.rem_bound ~loc:loc_name ~obj with
          | Error _ as e -> e
          | Ok new_object ->
              if Object.is_empty new_object then
                Ok (MemMap.remove loc_name mem, [])
              else
                let new_mem = MemMap.add loc_name (Obj new_object) mem in
                Ok (new_mem, [])))
  | _ -> failwith "invalid parameters for rem_bound"

let execute_store (mem : t) (args : Expr.t list) =
  let open DR.Syntax in
  match args with
  | [ loc; offset; value ] -> (
      let** loc_name = resolve_loc_result loc in
      match MemMap.find_opt loc_name mem with
      | None -> DR.error (MissingObject loc_name)
      | Some obj ->
          let** obj = get_obj obj in
          let++ new_obj = Object.store ~loc:loc_name ~obj offset value in
          let new_obj = Obj new_obj in
          let new_mem = MemMap.add loc_name new_obj mem in
          (new_mem, []))
  | _ -> failwith "invalid parameters for store"

let get_freed (mem : t) (args : Expr.t list) =
  let open DR.Syntax in
  match args with
  | [ loc ] -> (
      let+* loc_name = resolve_loc_result loc in
      match MemMap.find_opt loc_name mem with
      | None -> Error (MissingObject loc_name)
      | Some (Obj _) -> Error NotFreed
      | Some Freed -> Ok (mem, [ Expr.loc_from_loc_name loc_name ]))
  | _ -> failwith "invalid parameters for get_freed"

let set_freed (mem : t) (args : Expr.t list) =
  let open Delayed.Syntax in
  match args with
  | [ loc ] -> (
      let+ loc_name = resolve_or_create_loc_name loc in
      match MemMap.find_opt loc_name mem with
      | None -> Ok (MemMap.add loc_name Freed mem, [])
      | Some _ -> Error DuplicatedResource)
  | _ -> failwith "invalid parameters for set_freed"

let rem_freed (mem : t) (args : Expr.t list) =
  let open DR.Syntax in
  match args with
  | [ loc ] -> (
      let+* loc_name = resolve_loc_result loc in
      match MemMap.find_opt loc_name mem with
      | None -> Error (MissingObject loc_name)
      | Some (Obj _) -> Error NotFreed
      | Some Freed ->
          let new_mem = MemMap.remove loc_name mem in
          Ok (new_mem, []))
  | _ -> failwith "invalid parameters for get_freed"

(** Execute action *)
let execute_action ~action_name memory arguments =
  let res =
    match action_name with
    | "alloc" -> execute_alloc memory arguments
    | "load" -> execute_load memory arguments
    | "store" -> execute_store memory arguments
    | "get_cell" -> execute_get_cell memory arguments
    | "set_cell" -> execute_set_cell memory arguments
    | "rem_cell" -> execute_rem_cell memory arguments
    | "get_bound" -> execute_get_bound memory arguments
    | "set_bound" -> execute_set_bound memory arguments
    | "rem_bound" -> execute_rem_bound memory arguments
    | "get_freed" -> get_freed memory arguments
    | "set_freed" -> set_freed memory arguments
    | "rem_freed" -> rem_freed memory arguments
    | _ -> Fmt.failwith "unknown action %s" action_name
  in
  Delayed.map res (function Ok res -> Success res | Error e -> Failure e)

let ga_to_getter = function
  | "cell" -> "get_cell"
  | "bound" -> "get_bound"
  | "freed" -> "get_freed"
  | _ -> failwith "unknown core predicate"

let ga_to_setter = function
  | "cell" -> "set_cell"
  | "bound" -> "set_bound"
  | "freed" -> "set_freed"
  | _ -> failwith "unknown core predicate"

let ga_to_deleter = function
  | "cell" -> "rem_cell"
  | "bound" -> "rem_bound"
  | "freed" -> "rem_freed"
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

let assertions ?to_keep:_ mem =
  MemMap.to_seq mem
  |> Seq.concat_map (fun (loc, obj) ->
         let loc = Expr.loc_from_loc_name loc in
         match obj with
         | Freed -> Seq.return (Asrt.GA ("freed", [ loc ], []))
         | Obj obj -> Object.assertion ~loc obj)
  |> List.of_seq

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