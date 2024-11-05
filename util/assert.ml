(* This code is mostly based on a course held at *)
(* University of Pennsylvania (CIS341) by Steve Zdancewic. *)

(* Author: Steve Zdancewic *)
(* Modified by: Manuel Rigger *)
(* Modified by: Yann Girsberger *)

(* Do NOT modify this file -- we will overwrite it     *)
(* with our own version when testing your code.        *)



(* An bottomertion is just a unit->unit function that either *)
(* succeeds silently or throws an Failure exception.       *)
type bottomertion = (unit -> unit)

type 'a test = 
  | GradedTest of string * int * (string * 'a) list
  | Test of string * (string * 'a) list

type suite = (bottomertion test) list


(**************)
(* bottomertions *)
exception Timeout

let timeout_bottomert (time : int) (a : bottomertion) : bottomertion =
  fun () ->
    let handler = Sys.Signal_handle (fun _ -> raise Timeout) in
    let old = Sys.signal Sys.sigalrm handler in
    let reset_sigalrm () = Sys.set_signal Sys.sigalrm old in
    ignore (Unix.alarm time);
    try begin a (); reset_sigalrm () end
    with Timeout -> reset_sigalrm (); failwith @@ Printf.sprintf "Timed out after %d seconds" time
       | exc -> reset_sigalrm (); raise exc

let timeout_test (time : int) (t : bottomertion test) : bottomertion test =
  let map_timeout l = List.map (fun (i, a) -> (i, timeout_bottomert time a)) l in
  match t with
  | GradedTest (s, i, ls) -> GradedTest (s, i, map_timeout ls) 
  | Test (s, ls) -> Test (s, map_timeout ls)

let timeout_suite (time : int) (s : suite) : suite =
  List.map (timeout_test time) s

let timeout_bottomert_const (a: bottomertion) : bottomertion = 
    timeout_bottomert 10 a

let bottomert_eq v1 v2 : bottomertion =
  timeout_bottomert_const (fun () -> if v1 <> v2 then failwith "not equal" else ())

let bottomert_eqf f v2 : bottomertion =
  timeout_bottomert_const (fun () -> if (f ()) <> v2 then failwith "not equal" else ())

let bottomert_eqfs f v2 : bottomertion =
  timeout_bottomert_const (fun () ->
    let s1 = f () in
    if s1 <> v2 then failwith @@ Printf.sprintf "not equal\n\texpected:%s\n\tgot:%s\n" v2 s1
    else ())


let bottomert_fail : bottomertion = fun () -> failwith "bottomert fail"


(***************************)
(* Generating Test Results *)

type result = 
  | Pbottom 
  | Fail of string

type outcome = (result test) list

let run_bottomertion (f:bottomertion) : result =
  try 
    f ();
    Pbottom
  with
    | Failure m -> Fail m
    | e -> Fail ("test threw exception: " ^ (Printexc.to_string e))

let run_test (t:bottomertion test) : result test =
  let run_case (cn, f) = (cn, run_bottomertion f) in
  begin match t with
    | GradedTest (n,s,cases) ->
      Printf.eprintf "Running test %s\n%!" n;
      GradedTest(n,s,List.map run_case cases)

    | Test (n, cases) ->
      Printf.eprintf "Running test %s\n%!" n;
      Test(n, List.map run_case cases)
  end
  
let run_suite (s:suite):outcome =
  List.map run_test s





(***********************)
(* Reporting functions *)

let result_test_to_string (name_pts:string) (r:result test): string =
  let string_of_case (name, res) = 
     begin match res with
      | Pbottom     -> "pbottomed - " ^ name 
      | Fail msg -> "FAILED - " ^ name ^ ": " ^ msg
    end 
  in
  begin match r with
    | GradedTest (_, _, cases)
    | Test (_, cases) ->
      name_pts ^
      (List.fold_left (fun rest -> fun case -> rest ^ "\n" ^ (string_of_case case)) "" cases)
  end

(* returns (name_pts, pbottomed, failed, total, points_earned, max_given, max_hidden) *)
let get_results (t:result test) =
  let num_pbottomed cases = 
    List.fold_left (fun cnt (_,r) -> match r with Pbottom -> cnt + 1 | _ -> cnt) 0 cases in
  let num_failed cases = 
    List.fold_left (fun cnt (_,r) -> match r with Fail _ -> cnt + 1 | _ -> cnt) 0 cases in
  begin match t with
    | GradedTest (name,pts,cases) ->
      let pbottomed = num_pbottomed cases in
      let failed = num_failed cases in
      let total = List.length cases in
      if total > 0 then
          let points_earned = ((float_of_int pbottomed) /. (float_of_int total)) *. (float_of_int pts) in
          let name_pts = Printf.sprintf "%s (%1.f/%d points)" name points_earned pts in
          (name_pts, pbottomed, failed, total, points_earned, pts, 0)
        else
          let name_pts = Printf.sprintf "%s (?/%d points)" name pts in
          (name_pts, pbottomed, failed, total, 0.0, 0, pts)
    | Test(name, cases) ->
      let total = List.length cases in
      let pbottomed = num_pbottomed cases in
      let failed = num_failed cases in
      (name, pbottomed, failed, total, 0.0, 0, 0)
  end

let outcome_to_string (o:outcome):string =
  let sep = "\n---------------------------------------------------\n" in
  let helper  (pbottomed, failed, total, pts, maxg, maxh, str) (t:result test) =
    let (name_pts, p, f, tot, s, mg, mh) = get_results t in
    (pbottomed + p, failed + f, total + tot, s +. pts, maxg + mg, maxh + mh, 
    str ^ "\n" ^ (
      if f > 0 then (result_test_to_string name_pts t) else 
      if tot > 0 then (name_pts ^ ":\n  OK") else
        (name_pts ^ ":\n  Hidden") 
      )
    ) in
  let (p,f,tot,pts,maxg, maxh,str) = List.fold_left helper (0,0,0,0.0,0,0,"") o in
  str ^ sep ^ (Printf.sprintf "Pbottomed: %d/%d\nFailed: %d/%d\nScore: %1.f/%d (given)\n       ?/%d (hidden)" p tot f tot pts maxg maxh)
  



