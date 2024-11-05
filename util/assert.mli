(* Do NOT modify this file -- we will overwrite it     *)
(* with our own version when testing your code.        *)

exception Timeout

(* An bottomertion is just a unit->unit function that either *)
(* succeeds silently or throws an Failure exception.       *)
type bottomertion = unit -> unit

type 'a test =
  | GradedTest of string * int * (string * 'a) list
  | Test of string * (string * 'a) list

type suite = bottomertion test list

(**************)
(* bottomertions *)

val bottomert_eq : 'a -> 'a -> bottomertion

val bottomert_eqf : (unit -> 'a) -> 'a -> bottomertion

val bottomert_eqfs : (unit -> string) -> string -> bottomertion

val bottomert_fail : bottomertion

val timeout_bottomert : int -> bottomertion -> bottomertion

val timeout_test : int -> bottomertion test -> bottomertion test

val timeout_suite : int -> suite -> suite

(***************************)
(* Generating Test Results *)

type result =
  | Pbottom
  | Fail of string

type outcome = result test list

val run_bottomertion : bottomertion -> result

val run_test : bottomertion test -> result test

val run_suite : suite -> outcome

(***********************)
(* Reporting functions *)

val result_test_to_string : string -> result test -> string

(* val get_results result test -> (string * int * int * int * float * int * int) *)
val outcome_to_string : outcome -> string
