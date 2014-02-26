open String
open Name
open XAST
open Types
open Positions
open ElaborationErrors
open ElaborationExceptions
open ElaborationEnvironment

let curr_class_preds = ref []

let string_of_type ty      = ASTio.(XAST.(to_string pprint_ml_type ty))


let rec program p = handle_error List.(fun () ->
  flatten (fst (Misc.list_foldmap block ElaborationEnvironment.initial p))
)

(* on veut une liste de block, avec le bon env *)
and block env = function
  | BTypeDefinitions ts ->
    let env = type_definitions env ts in
    ([BTypeDefinitions ts], env)

  | BDefinition d ->
    let d, env = value_binding env d in
    ([BDefinition d], env)

  | BClassDefinition c ->
    class_definition env c

  | BInstanceDefinitions is ->
    instance_definitions env is

and concat_tname str (TName tname) = TName (str ^ tname)
and concat_tname_lname (TName tname) (LName lname) = LName (tname ^ lname)
and string_of_tname (TName name) = name
and type_of_class ?arg c =
  let arg = match arg with None -> c.class_parameter | Some arg_tname -> arg_tname in
  TyApp (c.class_position, concat_tname "class_" c.class_name,
	 [TyVar (c.class_position, arg)])
and type_of_inst pos c i =
  let param_types = List.map (fun param -> TyVar (pos, param)) i.instance_parameters in
  TyApp (pos, concat_tname "class_" c.class_name,
	 [TyApp (pos, i.instance_index, param_types)])

and add_predicate_to_exp pos env class_pred exp =
  let ClassPredicate (TName cls_name, arg_tname) = class_pred in
  let c = lookup_class pos (TName cls_name) env in
  let arg_name = name_of_var arg_tname ^ "_" in
  let lambda_arg_name = Name ("inst_" ^ arg_name ^ cls_name) in
  ELambda (
    pos,
    (lambda_arg_name, type_of_class ~arg:arg_tname c),
    exp
  )
  
and add_predicates_to_exp pos env exp =
  List.fold_right (add_predicate_to_exp pos env) !curr_class_preds exp


and add_superclasses_definition env c  =
  List.fold_left (fun members (TName superclass_name) ->
    (c.class_position,
     LName ("superclass_" ^ superclass_name),
     TyApp (
       c.class_position,
       TName ("class_" ^ superclass_name),
       [TyVar (c.class_position, c.class_parameter)]))
    :: members)
    c.class_members
    c.superclasses

and class_checking env c =
  (* unrelated class ? *)
  
  (* Does the superclasses exist in the environment ? *)
  List.iter (fun sc -> ignore (is_superclass c.class_position c.class_name sc env) ) 
    c.superclasses;
  
  (* Are the superclasses' parameters equals to ours *)
  List.iter 
    (fun sc ->
      let sc_def = lookup_class c.class_position sc env in
      let c_param = c.class_parameter in
      let sc_param = sc_def.class_parameter in
      if c_param <> sc_param then
	raise (InvalidClassParameter (c.class_position, c.class_parameter, sc_param))
    )
    c.superclasses;

  (* Are the members well-formed ? *)
  List.iter
    (function (pos, (LName n), ty) -> 
      check_wf_scheme env [c.class_parameter] ty;
    )
    c.class_members;
  
  (* Are the members already defined in the superclasses? *)
  let all_supermembers = List.concat
    (List.map
       (fun scname -> (lookup_class c.class_position scname env).class_members)
       c.superclasses) 
  in
  List.iter
    (function (pos, n, _) -> 
      List.iter (fun (s_pos, s_n, _) ->
	if n = s_n then
	  raise (AlreadyDefinedMember (pos, n, s_pos, s_n))
      ) all_supermembers
    )
    c.class_members;

  (* Are the members identifiers already used as values ? *)
  List.iter (fun (pos, LName n, _) ->
    check_value_already_defined pos (Name n) env
  ) c.class_members

and check_value_already_defined pos x env =
  try
    ignore (lookup pos x env);
    raise (AlreadyDefinedSymbol (pos, x))
  with 
    UnboundIdentifier _ -> ()

and class_definition env c =
  class_checking env c;
  let env = bind_class c.class_name c env in
  let record_members = add_superclasses_definition env c in

  let record_type = DRecordType ([c.class_parameter], record_members) in
  let type_def = TypeDef (
    c.class_position,
    KArrow (KStar, KStar),
    concat_tname "class_" c.class_name,
    record_type)
  in
  let type_defs = TypeDefs (c.class_position, [type_def]) in
  let env = type_definitions env type_defs in

  let class_members = List.map (class_member c) c.class_members in
  let superclasses_accessors = superclasses_accessors env c in
  let value_defs, env = Misc.list_foldmap value_definition env (class_members @ superclasses_accessors) in
  let value_binding = BindValue (c.class_position, value_defs) in

  ([BTypeDefinitions type_defs; BDefinition value_binding], env)
    
and class_member c (pos, LName name, ty) =
  let class_ty = type_of_class c in
  let t_args, t_res = destruct_ntyarrow ty in
  let new_ty = ntyarrow pos (class_ty :: t_args) t_res in
  let value_def =
    ValueDef (
      pos, [c.class_parameter], [], (Name name, new_ty),
      EForall (
	pos,
	[c.class_parameter],
	ELambda (
	  pos, (Name "inst", class_ty),
	  ERecordAccess (
	    pos, EVar (pos, Name "inst", []), LName name))))
  in
  value_def

and superclass_accessor c superclass =
  let pos = c.class_position in
  let class_ty = type_of_class c in
  let superclass_ty = type_of_class superclass in
  let accessor_ty = ntyarrow pos [class_ty] superclass_ty in
  let TName class_name = c.class_name in
  let TName superclass_name = superclass.class_name in
  let TName superclass_field = concat_tname "superclass_" superclass.class_name in
  let accessor_name = "superclass_" ^ superclass_name ^ "_" ^ class_name in
  let value_def =
    ValueDef (
      pos, [c.class_parameter], [], (Name accessor_name, accessor_ty),
      EForall (
	pos,
	[c.class_parameter],
	ELambda (
	  pos, (Name "inst", class_ty),
	  ERecordAccess (
	    pos,
	    EVar (pos, Name "inst", []),
	    LName superclass_field
	  )
	)
      )
    )
  in
  value_def

and superclasses_accessors env c =
  List.map (fun superclass_name ->
    let superclass = lookup_class c.class_position superclass_name env in
    superclass_accessor c superclass) c.superclasses
  
	      
and check_instance_definition env i =
  (* We check that for each superclass of the instanciated class,
     there exists an instance of that index.
     i.e : Eq 'a => Ord 'a
     Ord int requires Eq int
  *)
  List.iter 
    (fun s_i -> ignore (lookup_instance i.instance_position (s_i, i.instance_index) env))
    (lookup_class i.instance_position i.instance_class_name env).superclasses;
  
  (* is_canonical ? 
     = Checks there aren't two equal instance predicates that binds the same type
     => voir le typing_context
  *)
  
  (* elaboration ?? *)
  
  ()  


and instance_definitions env is =
  (* definitions are recursive thus we extend the typing environment *)
  let env = List.fold_left bind_instance env is in
  List.iter (check_instance_definition env) is;

  let value_defs = List.map (instance_definition env) is in
  block env (BDefinition (BindRecValue (undefined_position, value_defs)))

and fresh_instance_name =
  let r = ref 0 in
  fun () -> incr r; Name ("_instance_" ^ string_of_int !r)

and add_superclasses_fields env i =
  let pos = i.instance_position in
  let i_class = lookup_class pos i.instance_class_name env in
  let TName index_name = i.instance_index in
  List.fold_left (fun record_bindings (TName superclass_name) ->
    let rb = RecordBinding (
      LName ("superclass_" ^ superclass_name),
      EVar (pos,
	    Name (index_name ^ "_class_" ^ superclass_name),
      List.map (fun tname -> TyVar (pos, tname)) i.instance_parameters)
    ) in
    rb :: record_bindings) i.instance_members i_class.superclasses
    

and instance_definition env i =
  let instance_members = add_superclasses_fields env i in
  let pos = i.instance_position in
  let i_class = lookup_class pos i.instance_class_name env in
  let param_types = List.map (fun param -> TyVar (pos, param)) i.instance_parameters in
  let inst_ty = TyApp (pos, concat_tname "class_" i_class.class_name,
    [TyApp (pos, i.instance_index, param_types)]) in
  let record_exp =
    EForall (
      pos,
      i.instance_parameters,
      ERecordCon (
	pos,
	fresh_instance_name (),
	[TyApp (pos, i.instance_index, param_types)],
	instance_members))
  in
  let name = Name (
    Printf.sprintf "%s_class_%s"
      (string_of_tname i.instance_index)
      (string_of_tname i.instance_class_name)) in
  let value_def =
    ValueDef (
      pos,
      i.instance_parameters,
      i.instance_typing_context,
      (name, inst_ty),
      record_exp)
  in
  (*value_definition env value_def*)
  value_def
  
					    
and type_definitions env (TypeDefs (_, tdefs)) =
  let env = List.fold_left env_of_type_definition env tdefs in
  List.fold_left type_definition env tdefs

and env_of_type_definition env = function
  | (TypeDef (pos, kind, t, _)) as tdef ->
    bind_type t kind tdef env

  | (ExternalType (p, ts, t, os)) as tdef ->
    bind_type t (kind_of_arity (List.length ts)) tdef env

and type_definition env = function
  | TypeDef (pos, _, t, dt) -> datatype_definition t env dt
  | ExternalType (p, ts, t, os) -> env

and datatype_definition t env = function
  | DAlgebraic ds ->
    List.fold_left algebraic_dataconstructor env ds
  | DRecordType (ts, ltys) ->
    List.fold_left (label_type ts t) env ltys

and label_type ts rtcon env (pos, l, ty) =
  let env' = List.fold_left (fun env x -> bind_type_variable x env) env ts in
  check_wf_type env' KStar ty;
  bind_label pos l ts ty rtcon env

and algebraic_dataconstructor env (_, DName k, ts, kty) =
  check_wf_scheme env ts kty;
  bind_scheme (Name k) ts kty env

and introduce_type_parameters env ts =
  List.fold_left (fun env t -> bind_type_variable t env) env ts

and check_wf_scheme env ts ty =
  check_wf_type (introduce_type_parameters env ts) KStar ty

and check_wf_type env xkind = function
  | TyVar (pos, t) ->
    let tkind = lookup_type_kind pos t env in
    check_equivalent_kind pos xkind tkind

  | TyApp (pos, t, tys) ->
    let kt = lookup_type_kind pos t env in
    check_type_constructor_application pos env kt tys

and check_type_constructor_application pos env k tys =
  match tys, k with
  | [], KStar -> ()
  | ty :: tys, KArrow (k, ks) ->
    check_wf_type env k ty;
    check_type_constructor_application pos env ks tys
  | _ ->
    raise (IllKindedType pos)

and check_equivalent_kind pos k1 k2 =
  match k1, k2 with
    | KStar, KStar -> ()
    | KArrow (k1, k2), KArrow (k1', k2') ->
      check_equivalent_kind pos k1 k1';
      check_equivalent_kind pos k2 k2'
    | _ ->
      raise (IncompatibleKinds (pos, k1, k2))

and env_of_bindings env cdefs =
  List.(
  (function
    | BindValue (_, vs)
    | BindRecValue (_, vs) ->
      fold_left (fun env (ValueDef (_, ts, _, (x, ty), _)) ->
        bind_scheme x ts ty env
      ) env vs
    | ExternalValue (_, ts, (x, ty), _) ->
      bind_scheme x ts ty env
  ) cdefs
)

and check_equal_types pos ty1 ty2 =
  if not (equivalent ty1 ty2) then
    raise (IncompatibleTypes (pos, ty1, ty2))

and type_application pos env x tys =
  List.iter (check_wf_type env KStar) tys;
  let (ts, (_, ty)) = lookup pos x env in
  try
    substitute (List.combine ts tys) ty
  with e ->
    raise (InvalidTypeApplication pos)

(* Symbols resolution *)

and awaits_class ty =
  match ty with
  | TyApp (_, TName "->", [TyApp (_, TName class_name, [arg]); rem_ty ]) ->
    if String.length class_name > 6 && String.sub class_name 0 6 = "class_" then
      let (res_list, rem_ty2) = awaits_class rem_ty in
      ((String.sub class_name 6 ((String.length class_name) - 6), arg) :: res_list, rem_ty2)
    else
      [], ty
  | _ -> [], ty

and find_class_path pos env ?arg_tname class_name =
  let class_tname = TName class_name in
  let ClassPredicate (TName pred_cls_name, _) =
    try
      List.find (fun (ClassPredicate (ctname, arg_tname)) ->
	ctname = class_tname || is_superclass pos class_tname ctname env) !curr_class_preds
    with
    | Not_found -> failwith "No predicate oO"
  in
  let c = lookup_class pos (TName pred_cls_name) env in

  let rec loop c exp =
    if c.class_name = class_tname then
      exp
    else
      try
	let sc_tname = List.find (fun tname ->
	  tname = class_tname || is_superclass pos class_tname tname env) c.superclasses in
	let TName sc_name = sc_tname in
	let TName c_name = c.class_name in
	let sc = lookup_class pos sc_tname env in
	loop sc (EApp (pos, EVar (pos, Name ("superclass_" ^ sc_name ^ "_" ^ c_name), []), exp))
      with
      | Not_found -> assert false
  in
  
  let arg_name = match arg_tname with | None -> "" | Some tname -> name_of_var tname ^ "_" in
  
  loop c (EVar (pos, Name ("inst_" ^ arg_name ^ pred_cls_name), []))


and name_of_var (TName var_name) =
  assert (String.length var_name = 2);
  String.sub var_name 1 1

and resolve_symbol pos env sym ty e =
  match awaits_class ty with
  | [], _ -> e, ty
  | [(class_name, arg_ty)] , rem_ty ->
    begin
      match arg_ty with
      | TyVar (_, arg_tname) ->
	EApp (pos, e, find_class_path pos env ~arg_tname:arg_tname class_name), rem_ty
      | TyApp (_, TName index, []) ->
	(EApp (pos, e, EVar (pos, Name (index ^ "_class_" ^ class_name), [])), rem_ty)
      | TyApp (_, TName index, [TyVar (_, var_tname)]) ->
	let inst_exp_name = index ^ "_class_" ^ class_name in
	let (ty_binders, (_, inst_ty)) = lookup pos (Name inst_exp_name) env in
	begin
	  match awaits_class inst_ty with
	  | [], _ ->
	    EApp (pos, e, EVar (pos, Name inst_exp_name, [TyVar (pos, var_tname)])), rem_ty
	  | [(c2_name, _)], _ ->
	    EApp (pos, e,
		  EApp (pos,
			EVar (pos, Name inst_exp_name, [TyVar (pos, var_tname)]),
			EVar (pos, Name ("inst_" ^ (name_of_var var_tname) ^ "_" ^ c2_name), []))),
	    rem_ty
	  | _ -> failwith "Multiple class arguments : todo also\n"
	end
      | _ -> failwith "Unexpected type form in resolve_symbol\n";
    end
  | _ -> failwith "Multiple class arguments : todo\n"
	


and expression env = function
  | EVar (pos, ((Name s) as x), tys) as e ->
    let ty = type_application pos env x tys in
    resolve_symbol pos env s ty e

  | ELambda (pos, ((x, aty) as b), e') ->
    check_wf_type env KStar aty;
    let env = bind_simple x aty env in
    let (e, ty) = expression env  e' in
    (ELambda (pos, b, e), ntyarrow pos [aty] ty)

  | EApp (pos, a, b) ->
    let a, a_ty = expression env  a in
    let b, b_ty = expression env  b in
    begin match destruct_tyarrow a_ty with
      | None ->
        raise (ApplicationToNonFunctional pos)
      | Some (ity, oty) ->
        check_equal_types pos b_ty ity;
        (EApp (pos, a, b), oty)
    end

  | EBinding (pos, vb, e) ->
    let vb, env = value_binding env vb in
    let e, ty = expression env  e in
    (EBinding (pos, vb, e), ty)

  | EForall (pos, tvs, e) ->
    (** Because type abstractions are removed by [value_binding]. *)
    raise (OnlyLetsCanIntroduceTypeAbstraction pos)

  | ETypeConstraint (pos, e, xty) ->
    let e, ty = expression env  e in
    check_equal_types pos ty xty;
    (e, ty)

  | EExists (_, _, e) ->
    (** Because we are explicitly typed, flexible type variables
        are useless. *)
    expression env  e

  | EDCon (pos, DName x, tys, es) ->
    let ty = type_application pos env (Name x) tys in
    let (itys, oty) = destruct_ntyarrow ty in
    if List.(length itys <> length es) then
      raise (InvalidDataConstructorApplication pos)
    else
      let es =
        List.map2 (fun e xty ->
          let (e, ty) = expression env  e in
          check_equal_types pos ty xty;
          e
        ) es itys
      in
      (EDCon (pos, DName x, tys, es), oty)

  | EMatch (pos, s, bs) ->
    let (s, sty) = expression env  s in
    let bstys = List.map (branch env sty) bs in
    let bs = fst (List.split bstys) in
    let tys = snd (List.split bstys) in
    let ty = List.hd tys in
    List.iter (check_equal_types pos ty) (List.tl tys);
    (EMatch (pos, s, bs), ty)

  | ERecordAccess (pos, e, l) ->
    let e, ty = expression env  e in
    let (ts, lty, rtcon) = lookup_label pos l env in
    let ty =
      match ty with
        | TyApp (_, r, args) ->
          if rtcon <> r then
            raise (LabelDoesNotBelong (pos, l, r, rtcon))
          else
            begin try
              let s = List.combine ts args in
              Types.substitute s lty
            with _ ->
              (** Because we only well-kinded types and only store
                  well-kinded types in the environment. *)
              assert false
            end
        | _ ->
          raise (RecordExpected (pos, ty))
    in
    (ERecordAccess (pos, e, l), ty)

  | ERecordCon (pos, n, i, []) ->
    (** We syntactically forbids empty records. *)
    assert false

  | ERecordCon (pos, n, i, rbs) ->
    let rbstys = List.map (record_binding env) rbs in
    let rec check others rty = function
      | [] ->
        List.rev others, rty
      | (RecordBinding (l, e), ty) :: ls ->
        if List.exists (fun (RecordBinding (l', _)) -> l = l') others then
          raise (MultipleLabels (pos, l));

        let (ts, lty, rtcon) = lookup_label pos l env in
        let (s, rty) =
          match rty with
            | None ->
              let rty = TyApp (pos, rtcon, i) in
              let s =
                try
                  List.combine ts i
                with _ -> raise (InvalidRecordInstantiation pos)
              in
              (s, rty)
            | Some (s, rty) ->
              (s, rty)
        in
        check_equal_types pos ty (Types.substitute s lty);
        check (RecordBinding (l, e) :: others) (Some (s, rty)) ls
    in
    let (ls, rty) = check [] None rbstys in
    let rty = match rty with
      | None -> assert false
      | Some (_, rty) -> rty
    in
    (ERecordCon (pos, n, i, ls), rty)

  | ((EPrimitive (pos, p)) as e) ->
    (e, primitive pos p)

and primitive pos = function
  | PIntegerConstant _ ->
    TyApp (pos, TName "int", [])

  | PUnit ->
    TyApp (pos, TName "unit", [])

  | PCharConstant _ ->
    TyApp (pos, TName "char", [])

and branch env sty (Branch (pos, p, e)) =
  let denv = pattern env sty p in
  let env = concat pos env denv in
  let (e, ty) = expression env e in
  (Branch (pos, p, e), ty)

and concat pos env1 env2 =
  List.fold_left
    (fun env (_, (x, ty)) -> bind_simple x ty env)
    env1 (values env2)

and linear_bind pos env (ts, (x, ty)) =
  assert (ts = []); (** Because patterns only bind monomorphic values. *)
  try
    ignore (lookup pos x env);
    raise (NonLinearPattern pos)
  with UnboundIdentifier _ ->
    bind_simple x ty env

and join pos denv1 denv2 =
  List.fold_left (linear_bind pos) denv2 (values denv1)

and check_same_denv pos denv1 denv2 =
  List.iter (fun (ts, (x, ty)) ->
    assert (ts = []); (** Because patterns only bind monomorphic values. *)
    try
      let (_, (_, ty')) = lookup pos x denv2 in
      check_equal_types pos ty ty';
    with _ ->
      raise (PatternsMustBindSameVariables pos)
  ) (values denv1)

and pattern env xty = function
  | PVar (_, name) ->
    bind_simple name xty ElaborationEnvironment.empty

  | PWildcard _ ->
    ElaborationEnvironment.empty

  | PAlias (pos, name, p) ->
    linear_bind pos (pattern env xty p) ([], (name, xty))

  | PTypeConstraint (pos, p, pty) ->
    check_equal_types pos pty xty;
    pattern env xty p

  | PPrimitive (pos, p) ->
    check_equal_types pos (primitive pos p) xty;
    ElaborationEnvironment.empty

  | PData (pos, (DName x), tys, ps) ->
    let kty = type_application pos env (Name x) tys in
    let itys, oty = destruct_ntyarrow kty in
    if List.(length itys <> length ps) then
      raise (InvalidDataConstructorApplication pos)
    else
      let denvs = List.map2 (pattern env) itys ps in (
        check_equal_types pos oty xty;
        List.fold_left (join pos) ElaborationEnvironment.empty denvs
      )

  | PAnd (pos, ps) ->
    List.fold_left
      (join pos)
      ElaborationEnvironment.empty
      (List.map (pattern env xty) ps)

  | POr (pos, ps) ->
    let denvs = List.map (pattern env xty) ps in
    let denv = List.hd denvs in
    List.(iter (check_same_denv pos denv) (tl denvs));
    denv

and record_binding env (RecordBinding (l, e)) =
  let e, ty = expression env e in
  (RecordBinding (l, e), ty)

and value_binding env = function
  | BindValue (pos, vs) ->
    let (vs, env) = Misc.list_foldmap value_definition env vs in
    (BindValue (pos, vs), env)

  | BindRecValue (pos, vs) ->
    let env = List.fold_left value_declaration env vs in
    let (vs, env') = Misc.list_foldmap value_definition env vs in
    (BindRecValue (pos, vs), env)

  | ExternalValue (pos, ts, ((x, ty) as b), os) ->
    let env = bind_scheme x ts ty env in
    (ExternalValue (pos, ts, b, os), env)

and eforall pos ts e =
  match ts, e with
    | ts, EForall (pos, [], ((EForall _) as e)) ->
      eforall pos ts e
    | [], EForall (pos, [], e) ->
      e
    | [], EForall (pos, _, _) ->
      raise (InvalidNumberOfTypeAbstraction pos)
    | [], e ->
      e
    | x :: xs, EForall (pos, t :: ts, e) ->
      if x <> t then
        raise (SameNameInTypeAbstractionAndScheme pos);
      eforall pos xs (EForall (pos, ts, e))
    | _, _ ->
      raise (InvalidNumberOfTypeAbstraction pos)

and add_predicates_to_type ?preds pos ty =
  let (args_tys, res_ty) = destruct_ntyarrow ty in
  let preds_tys = List.map (fun (ClassPredicate (cls_tname, arg_tname)) ->
    TyApp (pos, concat_tname "class_" cls_tname, [TyVar (pos, arg_tname)])
  ) (match preds with None -> !curr_class_preds | Some ps -> ps) in
  ntyarrow pos (preds_tys @ args_tys) res_ty

and check_method_already_defined pos ((Name n) as name) env = 
  List.iter
    (fun c ->
      List.iter (fun (pos, LName n', _) ->
	if n' = n then
	  raise (AlreadyDefinedSymbol (pos, name))
      ) c.class_members
    )
    (get_classes env);

and value_definition env (ValueDef (pos, ts, ps, (x, xty), e)) =
  let env' = introduce_type_parameters env ts in
  check_wf_scheme env ts xty;

  if is_value_form e then begin
    let e = eforall pos ts e in

    let class_preds = !curr_class_preds in
    curr_class_preds := ps @ class_preds;
    let e = add_predicates_to_exp pos env e in
    let xty = add_predicates_to_type pos xty in
    
    (match awaits_class xty with
    | [], _ -> check_method_already_defined pos x env
    | _ -> ()
    );

    let e, ty = expression env' e in

    curr_class_preds := class_preds;

    let b = (x, ty) in
    check_equal_types pos xty ty;
    (ValueDef (pos, ts, [], b, EForall (pos, ts, e)),
     bind_scheme x ts ty env)
  end else begin
    check_method_already_defined pos x env;

    if ts <> [] then
      raise (ValueRestriction pos)
    else
      let e = eforall pos [] e in
      let e, ty = expression env' e in
      let b = (x, ty) in
      check_equal_types pos xty ty;
      (ValueDef (pos, [], [], b, e), bind_simple x ty env)
  end

and value_declaration env (ValueDef (pos, ts, ps, (x, ty), e)) =
  bind_scheme x ts (add_predicates_to_type ~preds:ps pos ty) env


and is_value_form = function
  | EVar _
  | ELambda _
  | EPrimitive _ ->
    true
  | EDCon (_, _, _, es) ->
    List.for_all is_value_form es
  | ERecordCon (_, _, _, rbs) ->
    List.for_all (fun (RecordBinding (_, e)) -> is_value_form e) rbs
  | EExists (_, _, t)
  | ETypeConstraint (_, t, _)
  | EForall (_, _, t) ->
    is_value_form t
  | _ ->
    false


and get_position = function
  | EVar (position, _, _)
  | ELambda (position, _, _)
  | EApp (position, _, _)
  | EBinding (position, _, _)
  | EPrimitive (position, _)
  | EForall (position, _, _)
  | EExists (position, _, _)
  | ETypeConstraint (position, _, _)
  | EDCon (position, _, _, _)
  | EMatch (position, _, _)
  | ERecordAccess (position, _, _)
  | ERecordCon (position, _, _, _) -> position
