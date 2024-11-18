open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None -> 
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator" 
    | Some term -> 
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None
  
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) -> 
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearer, I may do that for next time around.]]

 
   Consider globals7.oat

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 

   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },                
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index 

*)

(* Global initialized arrays:

  There is another wrinkle: To compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*) 



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (_: Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]

let load_exp ((ty, op, stream): Ll.ty * Ll.operand * stream) : Ll.ty * Ll.operand * stream =
  begin match ty with
    | Ptr rty -> begin
      let id = gensym "load" in
      rty, Id id, ( I (id, Load (ty, op)) )::stream
    end
    | _ -> (
      print_endline (string_of_ty ty);
      print_endline (string_of_operand op);
      failwith "expected pointer"
    )
  end

  
(* let printops ((ty, op, stream): Ll.ty * Ll.operand * stream) : Ll.ty * Ll.operand * stream = 
  print_endline (string_of_ty ty);
  print_endline (string_of_ty ty);
  print_endline (string_of_ty ty); *)

  
(* dummynode with debugging label *)
let dummynode (exp:'a) (label:string): 'a node = 
    { elt=exp; loc=(label, (0, 0), (0, 0))}

let ty_of_arr_el (arrty:Ll.ty) =
  match arrty with
    | Ptr (Struct ([ Ll.I64; Array (_, elty) ])) -> elty
    | _ -> (
      (print_endline (Llutil.string_of_ty arrty));
      failwith "not valid oat array"
    )

(* let access_ll_oat_array (arrty:Ll.ty) (arrop:Ll.operand) (i:Ll.operand): 
    Ll.ty * Ll.operand * stream = begin
  (* let arrvaluety, arrvalueop, arrstream = arrty, arrop, [] in *)
  let arrvaluety, arrvalueop, arrstream = load (arrty, arrop, []) in

  let elty = begin match arrvaluety with
    | Ptr (Struct ([ Ll.I64; Array (_, elty) ])) -> elty
    | _ -> (
      (print_endline (Llutil.string_of_ty arrvaluety));
      (print_endline (Llutil.string_of_operand arrvalueop));
      (print_endline (Llutil.string_of_operand i));
      failwith "not valid oat array"
    )
  end in
  
  let eluid = gensym "arr_el" in
  let accessstr = [
    I (eluid, Ll.Gep (arrvaluety, arrvalueop, [Ll.Const 0L; Ll.Const 1L; i]))
  ] @ arrstream in
  (Ll.Ptr elty, Ll.Id eluid, accessstr)
end *)

let cmp_bop (oatbinop: Ast.binop) (aop:Ll.operand) (bop:Ll.operand) = begin
  begin match oatbinop with
    | Add | Sub | Mul | Shl | Shr | Sar | And | Or | IAnd | IOr -> begin
      let llbinop, llresty = begin match oatbinop with
        | Ast.Add -> Ll.Add, Ll.I64
        | Ast.Sub -> Ll.Sub, Ll.I64
        | Ast.Mul -> Ll.Mul, Ll.I64
        | Ast.Shl -> Ll.Shl, Ll.I64
        | Ast.Shr -> Ll.Lshr, Ll.I64
        | Ast.Sar -> Ll.Ashr, Ll.I64
        | Ast.IAnd -> Ll.And, Ll.I64
        | Ast.IOr -> Ll.Or, Ll.I64
        | Ast.And -> Ll.And, Ll.I1
        | Ast.Or -> Ll.Or, Ll.I1
        | _ -> failwith "cmp_bop 1"
      end in
      llresty, Ll.Binop (llbinop, llresty, aop, bop)
    end
    | Eq | Neq | Lt | Lte | Gt | Gte -> begin
      let llbinop = begin match oatbinop with
        | Ast.Eq -> Ll.Eq
        | Ast.Neq -> Ll.Ne
        | Ast.Lt -> Ll.Slt
        | Ast.Lte -> Ll.Sle
        | Ast.Gt -> Ll.Sgt
        | Ast.Gte -> Ll.Sge
        | _ -> failwith "cmp_bop 2"
      end in
      Ll.I1, Ll.Icmp (llbinop, Ll.I64, aop, bop)
    end
  end
end

let cmp_uop (oatunop: Ast.unop) (expop:Ll.operand) = begin
  let llbinop, llresty, opa = begin match oatunop with
    | Neg -> Ll.Sub, Ll.I64, Ll.Const 0L
    | Bitnot -> Ll.Xor, Ll.I64, Ll.Const (-1L)
    | Lognot -> Ll.Xor, Ll.I1, Ll.Const 1L
  end in
  llresty, Ll.Binop (llbinop, llresty, opa, expop)
end

(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a 
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)


let rec cmp_exp (c:Ctxt.t) ({ elt=exp; _ }:Ast.exp node) : Ll.ty * Ll.operand * stream = begin

  begin match exp with
    (* | CNull of rty *)
    | CNull rty -> (cmp_ty (TRef rty), Ll.Null, [])
    (* | CBool of bool *)
    | CBool b -> (Ll.I1, Ll.Const (if b then 1L else 0L), [])
    (* | CInt of int64 *)
    | CInt i -> (Ll.I64, Ll.Const i, [])
    (* | Id of id *)
    | Id id -> begin
      match List.assoc_opt id c with
        | Some (ty, op) -> load_exp (ty, op, [])
        | None -> (
          (print_endline id);
          failwith "Unknown symbol"
        )
    end
    (* | CStr of string *)
    | CStr str -> begin
      let hoistedid = gensym "hoistedstr" in
      let rawid = gensym "rawstr" in
      let n = 1 + (String.length )str in

      let rawty = (Ll.Array (n, Ll.I8)) in
      let hoistedty = Ll.I8 in

      load_exp (Ptr (Ptr hoistedty), Ll.Gid hoistedid, [
        G (hoistedid, (Ptr hoistedty, GBitcast (Ptr rawty, Ll.GGid rawid, Ptr hoistedty)));
        G (rawid, (rawty, GString str));
      ])
    end
    (* | Index of exp node * exp node *)
    | Index (arr, i) -> begin
      let arrty, arrop, arrstream = cmp_exp c arr in
      let _, iop, istream = cmp_exp c i in

      let elty = ty_of_arr_el arrty in
      let elptr = gensym "arr_el_ptr" in
      
      let ptrexp = (Ptr elty, Ll.Id elptr, [
        I (elptr, Ll.Gep (arrty, arrop, [Ll.Const 0L; Ll.Const 1L; iop]))
      ] @ istream @ arrstream) in
      
      load_exp ptrexp
    end
    (* | CArr of ty * exp node list *)
    | CArr (ty, exps) -> begin
      let stream = ref [] in
      let count = List.length exps in
      (* compile a new array initialization using the other case of cmp_exp *)
      let arrty, arrop, arrstream = cmp_exp c (
        dummynode (NewArr (ty, dummynode (CInt (Int64.of_int count)) "cmp_exp")) "cmp_exp") in
        stream := arrstream @ !stream;
      let llelty = cmp_ty ty in
      
      (* place expressions into array *)
      exps |> (List.iteri (fun index exp -> begin
        let _, elop, elstream = cmp_exp c exp in
        let elid = gensym "carr_el" in
        let iop = Ll.Const (Int64.of_int index) in
        stream := [
          I (gensym "void", Ll.Store (llelty, elop, Ll.Id elid));
          I (elid, Ll.Gep (arrty, arrop, [Ll.Const 0L; Ll.Const 1L; iop]));
        ] @ elstream @ !stream
      end));
      (arrty, arrop, !stream)
    end
    (* | NewArr of ty * exp node *)
    | NewArr (ty, exp) -> begin
      let _, sop, sstream = cmp_exp c exp in
      let aty, aop, astream = oat_alloc_array ty sop in
      (aty, aop, astream @ sstream)
    end
    (* | Call of exp node * exp node list *)
    | Call (funexp, argexps) -> begin
      let stream = ref [] in
      let llargs = ref [] in
      (* cmp function exp *)
      (* let funty, funop, funstream = cmp_exp c funexp in *)
      let funty, funop = match funexp.elt with
        | Id id -> begin match List.assoc_opt id c with
            | Some (ty, op) -> ty, op
            | None -> (
              (print_endline id);
              failwith "unknown function"
            )
          end
        | _ -> failwith "function exp must be identifier"
      in
      (* get return type and check number args *)
      let paramtys, retty = begin match funty with
        | Ptr (Ll.Fun (paramtys, retty)) -> paramtys, retty
        | _ -> (
          (print_endline (Llutil.string_of_ty funty));
          (print_endline (Llutil.string_of_operand funop));
          failwith "not a function"
        )
      end in
      if List.length argexps <> List.length paramtys then begin
        failwith "incorrect number of args"
      end;
      (* compile args *)
      argexps |> (List.iter (fun argexp -> begin
        let argty, argop, argstream = cmp_exp c argexp in
        stream := argstream @ !stream;
        llargs := !llargs @ [(argty, argop)]
      end));
      (* make function call *)
      let retvaluid = gensym "retval" in
      stream := [
        I (retvaluid, Ll.Call (retty, funop, !llargs))
      ] @ !stream;
      (retty, Ll.Id retvaluid, !stream)
    end
    (* | Bop of binop * exp node * exp node *)
    | Bop (binop, aexp, bexp) -> begin
      let _, aop, astream = cmp_exp c aexp in
      let _, bop, bstream = cmp_exp c bexp in
            
      let resuid = gensym "binop_res" in

      let llresty, llinstr = cmp_bop binop aop bop in

      (llresty, Ll.Id resuid,
      [ 
        I (resuid, llinstr);
      ] @ bstream @ astream)
    end
    (* | Uop of unop * exp node *)
    | Uop (unop, exp) -> begin
      let _, expop, expstream = cmp_exp c exp in
      let resuid = gensym "uop_res" in
      let llresty, llinstr = cmp_uop unop expop in
      (llresty, Ll.Id resuid,
      [
        I (resuid, llinstr);
      ] @ expstream)
    end
  end
end

let rec cmp_lhs (c:Ctxt.t)({ elt; _ }:exp node): Ll.ty * Ll.operand * stream = 
  begin match elt with
    | Id id -> begin
      match List.assoc_opt id c with
        | Some (ty, op) -> (ty, op, [])
        | None -> (
          (print_endline id);
          failwith "Unknown symbol"
        )
    end
    | Index (arr, i) -> begin
      let arrty, arrop, arrstream = cmp_exp c arr in
      (* let arrty, arrop, arrstream = load_exp @@ cmp_lhs c arr in *)
      let _, iop, istream = cmp_exp c i in

      let elty = ty_of_arr_el arrty in
      let elid = gensym "lhs_ix_el" in

      (Ll.Ptr elty, Ll.Id elid, [
        I (elid, Ll.Gep (arrty, arrop, [Ll.Const 0L; Ll.Const 1L; iop]))
      ] @ arrstream @ istream)
    end
    | _ -> failwith "Invalid lhs exp"
  end

(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations
   
   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)

let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) ({ elt=stmtelt; _ }:Ast.stmt node) : Ctxt.t * stream = begin
  begin match stmtelt with 
    (* | Decl of vdecl *)
    | Decl (id, exp) -> begin
        (* %_x7 = alloca { i64, [0 x i64] }*                              ;; (1) *)
        let localsym = gensym "local_" ^ id in
        let ty, op, stream = cmp_exp c exp in 
        ( Ctxt.add c id (Ptr ty, Id localsym), [
          I (gensym "void", Ll.Store (ty, op, Id localsym));
          E (localsym, Ll.Alloca ty);
        ] @ stream)
    end
    (* | Assn of exp node * exp node *)
    | Assn (lhs, rhs) -> begin
      let _, lhsop, lhsstream = cmp_lhs c lhs in
      let rhsty, rhsop, rhsstream = cmp_exp c rhs in 
      ( c, [
        I (gensym "void", Ll.Store (rhsty, rhsop, lhsop))
      ] @ rhsstream @ lhsstream)
    end
    (* | Ret of exp node option *)
    | Ret (Some exp) -> begin
      let ty, op, stream  = cmp_exp c exp in 
      (c, [
        T (Ll.Ret (ty, Some op))
      ] @ stream)
    end
    | Ret None -> begin
      (c, [
        T (Ll.Ret (Ll.Void, None))
      ])
    end
    (* | SCall of exp node * exp node list *)
    | SCall (funexp, argexps) -> begin
      let _, _, retstream = cmp_exp c (dummynode (Ast.Call (funexp, argexps)) "SCall stmt") in
      (c, retstream)
    end
    (* | If of exp node * stmt node list * stmt node list *)
    | If (condexp, thenblock, elseblock) -> begin

      let condty, condop, condstream = cmp_exp c condexp in
      if condty <> Ll.I1 then begin
        failwith "conditional must be boolean"
      end;

      let thenlabel = gensym "then" in
      let elselabel = gensym "else" in
      let endiflabel = gensym "endif" in

      let _, thenll = cmp_block c Ll.Void thenblock in
      let _, elsell = cmp_block c Ll.Void elseblock in

      (c, [
        L endiflabel;
        T (Ll.Br endiflabel);
        ] @ elsell @ [
        L elselabel;
        T (Ll.Br endiflabel);
      ] @ thenll @ [
        L thenlabel;
        T (Ll.Cbr (condop, thenlabel, elselabel));
      ] @ condstream)
    end
    (* | While of exp node * stmt node list *)
    | While (condexp, wblock) -> begin
      let condty, condop, condstream = cmp_exp c condexp in
      if condty <> Ll.I1 then begin
        failwith "conditional must be boolean"
      end;
      
      let condlabel = gensym "cond" in
      let whileblocklabel = gensym "whileblock" in
      let whileendlabel = gensym "whileend" in

      let _, blockll = cmp_block c Ll.Void wblock in

      (c, [
        L whileendlabel;
        T (Ll.Br condlabel);
      ] @ blockll @ [
        L whileblocklabel;
        T (Ll.Cbr (condop, whileblocklabel, whileendlabel));
      ] @ condstream @ [
        L condlabel;
        T (Ll.Br (condlabel))
      ])
    end
    (* | For of vdecl list * exp node option * stmt node option * stmt node list *)
    | For (vdecls, condopt, postopt, forblock) -> begin
      (* compile for to while *)
      (* if no condition just pass true *)
      let condexp = begin match condopt with
        | Some cond -> cond
        | None -> dummynode (Ast.CBool true) "for-loop condexp"
      end in
      (* if poststatement, add behind while block *)
      let whileblock = begin match postopt with
        | Some poststmt -> forblock @ [ poststmt ]
        | None -> forblock
      end in
      (* join everything into block, var decl go first, then produced while loop *)
      let totalcode = 
        (List.map (fun vdecl -> dummynode (Decl vdecl) "for-loop vdecl") vdecls) @ [
        dummynode (While (condexp, whileblock)) "for-loop while"
      ] in
      let _, stream = cmp_block c Ll.Void totalcode in
      (* the old env is returned, no external var can be declared by for-loop *)
      (c, stream)
    end
  end
end

(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s -> 
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts

(* Adds each function identifer to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

let ty_of_gexp ({ elt; _ }:exp node): ty = begin match elt with
  | CNull rty -> Ast.TRef rty
  | CBool _ -> Ast.TBool
  | CInt _ -> Ast.TInt
  | CStr _ -> Ast.TRef (Ast.RString)
  | CArr (ty, _) -> Ast.TRef (Ast.RArray (ty))
  | _ -> failwith "illegal global exp"
end

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C). 
*)
let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t = begin
  let cref = ref c in
  let cmp_gdecl decl = begin match decl with
    | Gvdecl { elt={ name; init }; _ } -> begin
      let ty = cmp_ty (ty_of_gexp init) in
      let op = Gid name in
      cref := Ctxt.add !cref name (Ptr ty, op);
    end
    | Gfdecl { elt={ frtyp; fname; args; _ }; _ } -> begin
      let argtypes = List.map (fun (astty, _) -> cmp_ty astty) args in
      let ty = Ll.Ptr (Ll.Fun (argtypes, cmp_ret_ty frtyp)) in
      let op = Gid fname in
      cref := Ctxt.add !cref fname (ty, op);
    end
  end in
  List.iter cmp_gdecl p;
  !cref
end

let print_stream (fname)(stream: elt list) = begin
  print_endline ("\n REVERSED stream of: " ^ fname);
  List.iter (fun (e:elt) -> begin match e with
    | L lbl -> print_endline ("L  " ^ lbl)
    | I (uid, instr) -> print_endline ("I  %" ^ uid ^ " = " ^ (Llutil.string_of_insn instr))
    | T term -> print_endline ("T  " ^ (Llutil.string_of_terminator term))
    | G (gid, gdecl) -> print_endline ("G  @" ^ gid ^ " = " ^ (Llutil.string_of_gdecl gdecl))
    | E (uid, instr) -> print_endline ("E  %" ^ uid ^ " = " ^ (Llutil.string_of_insn instr))
  end) (List.rev stream);
end

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from 
 *)

let cmp_fdecl (c:Ctxt.t) ({ elt={ frtyp; fname; args; body }; _ }:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list = begin
  (* generate dummy statements for each parameter *)
  let stream = ref [] in
  let cref = ref c in
  let llfparams = ref [] in
  
  let cmp_param (index: int)(paramty, paramid) = begin
    let llty = cmp_ty paramty in
    let fparam = gensym ("param_" ^ (Int.to_string index)) in
    stream := [
      I (gensym "void", Ll.Store (llty, Id fparam, Id paramid));
      E (paramid, Ll.Alloca (llty));
    ] @ !stream;
    cref := Ctxt.add !cref paramid (Ll.Ptr llty, Id paramid);
    llfparams := !llfparams @ [ fparam ];
  end in
  List.iteri cmp_param args;

  let retstmt = match frtyp with
    | Ast.RetVoid -> Ast.Ret None
    | Ast.RetVal (Ast.TInt) -> Ast.Ret (Some (dummynode (Ast.CInt 0L) "dummyval"))
    | Ast.RetVal (Ast.TBool) -> Ast.Ret (Some (dummynode (Ast.CBool false) "dummyval"))
    | Ast.RetVal (Ast.TRef ty) -> Ast.Ret (Some (dummynode (Ast.CNull ty) "dummyval"))
  in

  let extbody = body @ [
    dummynode retstmt "dummy return void";
  ] in

  (* compile function *)
  let _, bstream = cmp_block !cref (cmp_ret_ty frtyp) extbody in
  stream := bstream @ !stream;

  (* print_stream fname !stream; *)

  let cfg, gdecls = cfg_of_stream !stream in

  (* type fdecl = { f_ty : fty; f_param : uid list; f_cfg : cfg } *)
  let llfdecl = {
    f_ty = cmp_fty (List.map (fun (aty, _) -> aty) args, frtyp);
    f_param = !llfparams;
    f_cfg = cfg;
  } in

  (llfdecl, gdecls)
end


(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)

let rec cmp_gexp c ({ elt; _ }:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  begin match elt with 
    (* | CNull of rty *)
    | CNull rty -> begin
      (Ptr (cmp_rty rty), Ll.GNull), []
    end
    (* | CBool of bool *)
    | CBool b -> begin
      (Ll.I1, Ll.GInt (if b then 1L else 0L)), []
    end
    (* | CInt of int64 *)
    | CInt i -> begin
      (Ll.I64, Ll.GInt i), []
    end
    (* | CStr of string *)
    | CStr s -> begin
      let len = 1 + String.length s in
      let rawid = gensym "rawgstr" in
      let rawty = Ll.Array (len, Ll.I8) in
      let strty = Ll.I8 in

      (Ptr strty, Ll.GBitcast (Ptr rawty, GGid rawid, Ptr strty)), [
        (rawid, (rawty, Ll.GString s))
      ]
    end
    (* | CArr of ty * exp node list *)
    | CArr (ty, exps) -> begin
      let len = List.length exps in
      let llty = cmp_ty ty in
      (* @arr = global { i64, [0 x i64] }* bitcast 
          ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
      @_global_arr5 = global { i64, [4 x i64] } 
          { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] } *)
      let helpty = Ll.Struct [ Ll.I64; Ll.Array (len, llty)] in
      let helpid = gensym "global_arr" in
      
      let mainty = Ll.Struct [ Ll.I64; Ll.Array (0, llty)] in
      let gdecl = Ll.GBitcast (Ptr helpty, GGid helpid, Ptr mainty) in

      let entries = ref [] in
      let helpers = ref [] in

      let cmp_arr_entry exp = begin
        let gdecl, nexthelpers = cmp_gexp c exp in
        helpers := !helpers @ nexthelpers;
        entries := !entries @ [ gdecl ]
      end in
      List.iter cmp_arr_entry exps;
      
      helpers := !helpers @ [
        (helpid, (helpty, GStruct [ 
          (Ll.I64, Ll.GInt (Int64.of_int len));
          (Ll.Array (len, llty), (Ll.GArray !entries))
        ]))
      ];

      (Ptr mainty, gdecl), !helpers
    end
    | _ -> failwith "Illegal node in global expression."
  end

(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* Printexc.record_backtrace true; *)

  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } -> 
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
