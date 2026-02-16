open Effect
open Ppxlib
open Ast_builder.Default

let contract_attr =
  Attribute.declare "contract"
    Attribute.Context.value_binding
    Ast_pattern.(pstr nil)
    ()

(* Define the [@@pred] attribute for types *)
let pred_attr =
  Attribute.declare "pred"
    Attribute.Context.core_type
    Ast_pattern.(single_expr_payload __)
    (fun x -> x)

let effect_t_path ~loc =
  let lid = Ldot ((Lident "Effect"), "t") in
  Located.mk ~loc lid

let rec collect_args expr acc =
  match expr.pexp_desc with
  | Pexp_function (params, _, body) ->
      (* params is a list of 'function_param' *)
      let actual_body = match body with
        | Pfunction_body e -> e
        | Pfunction_cases (cs, _, _) -> pexp_function_cases ~loc:expr.pexp_loc cs
      in
      (* We continue recursing in case there are nested functions,
         but usually, all arguments are in 'params' now. *)
      (params, actual_body)
  | _ -> ([], expr)

(* Helper to rebuild the function after injecting code *)
let rebuild_fun loc params body_expr =
  let body_kind = Pfunction_body body_expr in
  (* We pass None for the constraint (return type) for now,
     or you can pass the original one if you captured it. *)
  pexp_function ~loc params None body_kind

let make_param_effect loc name =
  (* 1. Create the name for the effect constructor (e.g., CheckParam1) *)
  let constructor_name = Located.mk ~loc name in

  let unit_node = ptyp_constr ~loc (Located.mk ~loc (Lident "unit")) [] in

  (* 2. Define the argument: 'a *)
  let arg_type = [%type: int] in
  let res_type = ptyp_constr ~loc (effect_t_path ~loc) [unit_node] in

  (* 4. Construct the extension: type _ Effect.t += ... *)
  pstr_typext ~loc (type_extension ~loc
    ~path:(effect_t_path ~loc)
    ~params:[ (ptyp_any ~loc, (NoVariance, NoInjectivity)) ]
    ~constructors:[
      extension_constructor ~loc
        ~name:constructor_name
        ~kind:(Pext_decl ([], Pcstr_tuple [arg_type], Some res_type))
    ]
    ~private_:Public)

let make_contract_module loc num_args =
  (* Generate list of CheckParam1, CheckParam2, etc. *)
  let param_effects = List.init num_args (fun i ->
    let name = Printf.sprintf "CheckParam%d" (i + 1) in
    make_param_effect loc name
  ) in

  (* For the Return effect, we can use a literal if the name doesn't change *)

  let ret_type = [%type: int] in
  let return_effect =
    [%str type _ Effect.t += CheckReturn : [%t ret_type] -> unit Effect.t]
  in

  let module_items = param_effects @ return_effect in

  (* Build: module Local = struct ... end *)
  pstr_module ~loc (module_binding ~loc
    ~name:(Located.mk ~loc (Some "Local"))
    ~expr:(pmod_structure ~loc module_items))

let wrap_with_effects (vb : value_binding) params types body_expr =
  let loc = vb.pvb_loc in
  let local_module = make_contract_module loc (List.length params) in

  let new_body = pexp_letmodule ~loc
    (Located.mk ~loc (Some "Local"))
    (match local_module.pstr_desc with Pstr_module mb -> mb.pmb_expr | _ -> assert false)
    body_expr
  in

  pexp_function ~loc params (Some types) (Pfunction_body new_body)

let transform_contract_wrapper (vb : value_binding) =
  match vb.pvb_expr.pexp_desc with
  (* for now only transform a function annotated with [@contract]
     we require type signature, because the predicate contract will be
     attached to the type signature
     we only work for body expression, for function match cases, we ignore
  *)
  | Pexp_function (params, Some types, Pfunction_body body) ->
      { vb with
        pvb_expr = wrap_with_effects vb params types body;
        pvb_attributes = [];
      }

  | _ -> vb

let expander =
  object
    inherit Ast_traverse.map as super

    method! value_binding vb =
      (* Format.eprintf "Transforming: %a@." Pprintast.expression vb.pvb_expr; *)
      match Attribute.get contract_attr vb with
      | Some () ->
          let transformed_vb = transform_contract_wrapper vb in
          let recursive_expr = super#expression transformed_vb.pvb_expr in
          { transformed_vb with pvb_expr = recursive_expr }
      | None ->
          super#value_binding vb
  end

(* 3. Register the transformation *)
let () =
  Driver.register_transformation
    ~impl:expander#structure
    "cueh.ppx_sceh"
