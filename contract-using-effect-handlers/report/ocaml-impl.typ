= Implementing Software Contract using Ocaml's Effect Handler

Ocaml's Effect Handler can be used to implement Software Contract. We use PPX rewritter to fix the source code annotated with contract into execution code that mimics the expected behavior of Software Contract.

Ocaml parser has a nice attribute system, which are `[@@attribute]` or `[@attribute]`. These can be inserted into almost everywhere, and it will end up accompaning the parsed AST node. For our use case, we use the following annotation to specify a contract for a variable or function.

```ocaml
let
  [@contract : contract_for_x]
  x = 1

let
  [@contract : contract_for_x -> contract_for_y -> contract_for_z -> contract_for_f]
  f x y z = x + y + z

let
  [@contract : (contract_for_g_p1 -> contract_for_g_p2) -> contract_for_f]
  f g = g 0
```

We will convert annotated code into the checking code of software contract so that the runtime behavior is the same as one would expect in a Software Contract system. Let's not worry about the blame first, and use Effect Handler to execute checking code.

```ocaml
let
  [@contract : contract_for_x]
  x = x_body

(* compiled into a function that returns a value *)

let x () =
  let valid = contract_for_x x in
  if valid
  then x_body
  else raise Blame()

(* use it as a function *)

let y = x () + 1
```

For functions, we first rewrite and annotate its argument

```ocaml
let
  [@contract : contract_for_x -> contract_for_y -> contract_for_z -> contract_for_f]
  f x y z = x + y + z

(* compiles into *)

let f x y z =
  let [@contract : contract_for_x] x = x in
  let [@contract : contract_for_y] y = y in
  let [@contract : contract_for_z] z = z in

  (* define a new return value *)
  let [@contract : contract_for_f] ret = x + y + z in
  ret
```

For higher order function, we have to rewrite it into

```ocaml
let
  [@contract : (contract_for_g_p -> contract_for_g) -> contract_for_f]
  f g = g 0

let f g =
  let [@contract : contract_for_g_p1 -> contract_for_g] g =
    fun g_p1 -> g g_p1
  in
  let [@contract : contract_for_f] ret = f g in
  ret
```

These constructions are basics. We can base on this, and move all contract checks into Effects, and give a handler for them. We also add blame labels as arguments.


```ocaml
let
  [@contract : contract_for_x]
  x = 1

(* compiled into a function that returns a value *)

let x pos neg =
  let module Contract = struct
    type _ Effect.t += x : x_type -> unit Effect.t
  end in

  let handler =
    {
      effc = fun (type e) (eff : e Effect.t) ->
        match eff with
        | Contract.x x -> Some (fun k ->
            let valid = contract_for_x x in
            if valid
            then continue k ()
            else discontinue k (Blame pos)
          )
        | _ -> None
    }
  in

  try_with (fun () ->
    Effect.perform (Contract.x x);
    x
  ) ()
  handler

(* use it as a function *)

let y = (x __FUNCTION__ "...") + 1
```

```ocaml
let
  [@contract : contract_for_x -> contract_for_y -> contract_for_z -> contract_for_f]
  f x y z = x + y + z

(* compiles into *)

let f x y z =
  let [@contract : contract_for_x] x = x in
  let [@contract : contract_for_y] y = y in
  let [@contract : contract_for_z] z = z in

  (* define a new return value *)
  let [@contract : contract_for_f] ret = x + y + z in
  ret

let f pos neg x y z =
  (* arguments blame labels are swapped *)
  let [@contract : contract_for_x] x = x in
  let x = x neg pos in

  let [@contract : contract_for_y] y = y in
  let y = y neg pos in

  let [@contract : contract_for_z] z = z in
  let z = z neg pos in

  let [@contract : contract_for_f] ret = x + y + z in
  let ret = ret pos neg in

  ret

let y = (f "f" __FUNCTION__) 1 2 3
```

And for higher-order contracts.

```ocaml
let
  [@contract : (contract_for_g_p -> contract_for_g) -> contract_for_f]
  f g = g 0

let f pos neg g =
  let [@contract : contract_for_g_p1 -> contract_for_g] g =
    fun g_p1 -> g g_p1
  in
  let g = g neg pos in

  let [@contract : contract_for_f] ret = f g in
  let ret = reg pos neg in

  ret

let y = (f "f" __FUNCTION__) (fun p -> p)
```



If we want to control also the contract effects, we use the following code block:


```ocaml
(* using type annotation syntax, subject to change *)
let [@contract : 'handler contract_for_x] x = x_body

(* contract has effect, will be installed with a handler *)

let valid = try_with contract_for_x x handler in
if valid
then continue k ()
else discontinue k (Blame pos)

```

For functions, they can use effects inside their body. Effectful Software Contract will allow certain effects, and when an effect returns, the value is checked against some predicate.


```ocaml
let
  [@contract : contract_for_x -> contract_for_y -> contract_for_z -> contract_for_f]
  [@effect : effect_name * effect_predicate]
  f x y z = x + y + z

let f x y z =
  let [@contract : contract_for_x] x = x in
  let [@contract : contract_for_y] y = y in
  let [@contract : contract_for_z] z = z in

  (* define a new return value *)

  let [@contract_for_f] ret = try_with
    (fun () -> x + y + z) ()
    {
      effc = fun (type e) (eff : e Effect.t) ->
        match eff with
        | effect_name _ -> Some (fun k ->
            let result = (Effect.perform eff);
            (* also install handler if this also needs to call effect? *)
            let valid = effect_predicate result
            if valid
            then continue k ()
            else discontinue k (Blame ?)
        )
        | _ -> None (* or blame calling unallowed effects *)
    }
  in

  ret

```
