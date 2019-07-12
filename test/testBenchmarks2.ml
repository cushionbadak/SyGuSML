open Ast
open IntermediateTypes
open BatDeque
exception LoopOut
exception Testfail;;

let wait_time_sec : float = 1.0 (* float-second *)
let timeout_sec : float = 3.0 (* float-second *)
let sleep_between_proc_sec : float = 0.5 (* float-second *)
let kill_signal : int = 15 (* maybe SIGTERM *)

let global_parent_logfile_name : string = "glob_log_parent.txt"
let global_child_logfile_name : string = "glob_log_child.txt"
let logfile_channel_open_flag : open_flag list = [Open_wronly; Open_append; Open_creat; Open_text; ]
let logfile_open_permission : int = 0o664

(* do not touch pid_glob *)
let pid_glob = ref 1

let isSatTest testcode =
  let cfg = [] in
  let ctx = Z3.mk_context cfg in
  let test = Z3.SMT.parse_smtlib2_string ctx testcode  [] [] [] [] in
  let solver  = Z3.Solver.mk_solver ctx None in
  let inex = Z3.AST.ASTVector.to_expr_list test in
  Z3.Solver.add solver inex;
  match Z3.Solver.check solver [] with
  | UNSATISFIABLE -> true
  | UNKNOWN -> true
  | SATISFIABLE -> 
    let model = Z3.Solver.get_model solver in 
    match model with
    | None -> raise (Testfail)
    | Some (model) -> 
      let modelstring = (Z3.Model.to_string model) in
      if (modelstring = "") then (
        true
      )
      else 
        true

let verifyTest (fname, args, sort, term) cmds =
  let defFun = SmtCmd(DefineFun(fname, args, sort, term)) in
  let newAst = Transformer.synfunToDefFun cmds defFun in
  let newstring = Stringfier.astToZ3string newAst in
  try
    let z3solver = isSatTest newstring in
    if z3solver then IntermediateTypes.VerificationSuccess(newstring)
    else IntermediateTypes.VerificationFailure
  with e ->
    let msg = Printexc.to_string e in
    (* print_newline ();
       print_endline newstring;
       Printf.printf "error in z3solver: \n  %s" msg;
       print_newline ();
       print_newline (); *)
    IntermediateTypes.VerificationSuccess("error in z3 solver")

(* search by heap *)
type heapterm =
  | Node of term * int

module OrderedType = struct
  type t = heapterm
  let compare (Node(t1, i1)) (Node(t2, i2)) =
    if i1 = i2 then 0
    else if i1 > i2 then 1
    else -1
end

module Heap = BatHeap.Make (OrderedType)

let synthFuncByHeapTest
  = fun ast fname args sort initTerm grammar nonterminals costFunc ->
    let rec iter heap =
      if Heap.size heap = 0 then ""
      else 
        let Node(term,cost) = Heap.find_min heap in
        let nontermcount = Terms.countTermHasNonTerminal term nonterminals in
        if nontermcount = 0 then
          match verifyTest (fname, args, sort, term) ast with
          | VerificationSuccess(str) -> str
          | VerificationFailure -> iter (Heap.del_min heap)
        else
          let nextterms = Candidates.makeNextBodyListWithOneChange term grammar in
          let rec makeNodeList nextterms =
            match nextterms with
            | [] -> []
            | h::t -> Node(h, costFunc h nonterminals) :: (makeNodeList t)
          in 
          let nextNodes = makeNodeList nextterms  in
          let heap = List.fold_left Heap.insert (Heap.del_min heap) nextNodes in
          iter heap
    in iter (Heap.insert Heap.empty (Node(initTerm, 0)))

(** Find the synth-fun body by using heap
    @param ast parsed sygus string
    @param synfunIngredient function ingredient
    @return result sygus string with synth-fun body
*)
let searchByHeapTest
  = fun ast funcIngredients costFunc ->
    match funcIngredients with 
    | [] -> print_endline "No function to synthesize"; ""
    | (FuncIngredient(fname, args, sort, term, grammar))::otherfuncs ->
      let nonterminals = TransitionMap.fold (fun a _ c -> a::c) grammar [] in
      synthFuncByHeapTest ast fname args sort term grammar nonterminals costFunc

let testCost term nontermlist =
  let mul = 10 in
  let mul2 = 2 in
  let nonTermCount = Terms.countTermHasNonTerminal term nontermlist in
  let termCount = Terms.countTerm term in
  mul * nonTermCount + mul2 * termCount

let rec testAllFile name=
  (* print_endline(name); *)
  if Sys.is_directory name then
    let rec testFiles filelist=
      match filelist with
      | [] -> ()
      | h::t ->
        testAllFile h;
        testFiles t
    in
    testFiles (List.map (fun n -> String.concat "/" [name; n]) (Array.to_list (Sys.readdir name)))
  else
    let len = String.length name in
    if String.sub name (len-3) 3 = ".sl" then
      let rfs = Io.readfile name in
      match rfs with
      | Some(s) ->
        let res = Solver.solve s searchByHeapTest testCost in
        if res = "error in z3 solver" then
          print_endline(name)
        else
          ()
      | None ->
        Printf.printf "Can't read given file '%s'\n" name
    else
      ()

let rec wait_with_timeout : float -> float -> float -> int -> unit = 
  fun unit_wait_time timeout_sec timeout_acc pid ->
  if timeout_acc > timeout_sec 
  then 
    (
      Unix.kill pid kill_signal
    )
  else
    (
      let start_time = Unix.time () in
      let finish_time = Unix.sleepf unit_wait_time; Unix.time () in
      wait_with_timeout unit_wait_time timeout_sec (timeout_acc +. finish_time -. start_time) pid
    )

let rec testAllFile_OnebyOne : string -> out_channel -> out_channel -> unit =
  fun name log_channel_parent log_channel_child ->
  if (!pid_glob) = 0 then
    (
      (* child process *)
      (* stop execute *)
      ()
    )
  else
    (
      (* parent process *)
      (* continue execute *)
      (* I expect that sleep between process will solve out_channel problem *)
      (* let _ = Unix.fsleep sleep_between_proc_sec in *)
      let _ = flush_all () in
      if Sys.is_directory name then
        let rec testFiles filelist=
          match filelist with
          | [] -> ()
          | h::t ->
            testAllFile_OnebyOne h log_channel_parent log_channel_child;
            testFiles t
        in
        testFiles (List.map (fun n -> String.concat "/" [name; n]) (Array.to_list (Sys.readdir name)))
      else
        let len = String.length name in
        if String.sub name (len-3) 3 = ".sl" then
          let rfs = Io.readfile name in
          match rfs with
          | Some(s) ->
            (let pid = Unix.fork () in
             match pid with
             | 0 -> (* child process *)
               let _ = (pid_glob := pid) in
               let res = Solver.solve s searchByHeapTest testCost in
                (*
                below code can mix parent and child output.
                output_string log_channel (name ^ " :\n" ^ res ^ "\n\n")
                *)
               output_string log_channel_child (name ^ " :\n" ^ "CHILD-FINISH-OUTPUT." ^ "\n\n");
               close_out log_channel_child; 
             | n -> (* parent process *)
               (wait_with_timeout wait_time_sec timeout_sec 0.0 pid;
                let _, st = Unix.wait () in
                (
                  match st with
                  | Unix.WEXITED n -> (* normal *)
                    output_string log_channel_parent (name ^ " :\n" ^ "OKAY" ^ "\n\n")
                  | Unix.WSIGNALED n -> (* timeout or others *)
                    output_string log_channel_parent (name ^ ":\n" ^ "ERROR - WSIGNALED" ^ "\n\n")
                  | Unix.WSTOPPED n -> (* timeout or others *)
                    output_string log_channel_parent (name ^ ":\n" ^ "ERROR - WSTOPPED" ^ "\n\n")
                )
               )

            )
          | None ->
            let res = "Can't read given file" in
            output_string log_channel_parent (name ^ ":\n" ^ res ^ "\n\n")
        else
          (* not problem file *)
          ()
    )

(* let testdirlist = ["/newdisk/sygus-benchmarks/v2"] *)
(*


  B/euphony_space;ed"sygusBsnchmak/v2/2017/CLIATrack";  "sygusB nchmarks/v2/2018/CLIA_Track"swli e()
te"syguiBenchmatkd/v2/2017/Gensa_Track";
  "sygusBenchmarks/v2/2017/General_Track";
  "sygusBenchmarks/v2/2018/General_Track";
  "sygusBenchmarks/v2/2017/Inv_Track";
  "sygusBenchmarks/v2/2018/Inv_Track";
  "sygusBenchmarks/v2/2017/PBE_BV_Track";
  "sygusBenchmarks/v2/2018/PBE_BV_Track";
  "sygusBenchmarks/v2/2017/PBE_Strings_Track";
  "sygusBenchmarks/v2/2018/PBE_Strings_Track"
]
*)
(* let testdirlist = ["/newdisk/sygus-benchmarks/v2/2018/Inv_Track"] *)
let testdirlist = [
  "sygusBenchmarks/v2/2018/PBE_BV_Track";
  "sygusBenchmarks/v2/2018/General_Track";
]

let rec testDirs testdirlist=
  let log_channel_parent = open_out_gen logfile_channel_open_flag logfile_open_permission global_parent_logfile_name in
  let log_channel_child = open_out_gen logfile_channel_open_flag logfile_open_permission global_child_logfile_name in
  match testdirlist with
  | [] -> ()
  | h::t ->
    testAllFile_OnebyOne h log_channel_parent log_channel_child;
    testDirs t

let _ =
  print_newline();
  testDirs testdirlist

