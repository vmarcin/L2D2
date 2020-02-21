(*
 * Copyright (c) 2018-present
 *
 * Vladimir Marcin (xmarci10@stud.fit.vutbr.cz)
 * Automated Analysis and Verification Research Group (VeriFIT)
 * Brno University of Technology, Czech Republic
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
 open! IStd
 module F = Format
 module Domain = DeadlockDomain
 
 module Payload = SummaryPayload.Make (struct
   type t = DeadlockDomain.summary
   
   let field = Payloads.Fields.deadlock
   end)
 
 module TransferFunctions (CFG : ProcCfg.S) = struct
   module CFG = CFG
   module Domain = DeadlockDomain
   module Lockset = DeadlockDomain.Lockset
 
   type extras = FormalMap.t
 
   let exec_instr (astate: Domain.t) {ProcData.summary; extras} _ (instr: HilInstr.t) =
     let open ConcurrencyModels in
     let pname = Summary.get_proc_name summary in
     let get_path actuals =
       List.hd actuals |> Option.value_map ~default:[] ~f:HilExp.get_access_exprs |> List.hd
       |> Option.map ~f:HilExp.AccessExpression.to_access_path
     in
     match instr with
     | Call (_, Direct callee_pname, actuals, _, loc) ->(
       match get_lock_effect callee_pname actuals with
       | Lock locks ->
           F.printf "lock at line %a\n" Location.pp loc;
           get_path locks 
           |> Option.value_map ~default:astate ~f:(fun path -> Domain.acquire path astate loc extras pname)
       | Unlock locks ->
           get_path locks
           |> Option.value_map ~default:astate ~f:(fun path -> Domain.release path astate loc extras pname)
       (* TODO try_lock *)
       | LockedIfTrue _ | GuardConstruct _ | GuardLock _ | GuardLockedIfTrue _ | GuardUnlock _ | GuardDestroy _->
           astate
       (* User function call *)
       | NoEffect ->
         Payload.read ~caller_summary:summary ~callee_pname:callee_pname
         |> Option.value_map ~default:astate ~f:(fun summary ->
             let callee_formals = 
               match Summary.OnDisk.proc_resolve_attributes callee_pname with
               | Some callee_attr ->
                 callee_attr.ProcAttributes.formals
               | None ->
                 []
             in
             Domain.integrate_summary astate callee_pname loc summary callee_formals actuals pname
         )
     )
     | _ ->  
       astate
 
   let pp_session_name _node fmt = F.pp_print_string fmt "deadlock";
 end
 
 module L2D2 = LowerHil.MakeAbstractInterpreter (TransferFunctions (ProcCfg.Normal))
 
 let checker {Callbacks.exe_env; summary} =
   let proc_desc = Summary.get_proc_desc summary in
   let formals = FormalMap.make proc_desc in
   let procname = Procdesc.get_proc_name proc_desc in
   let tenv = Exe_env.get_tenv exe_env procname in
   let proc_data = ProcData.make summary tenv formals in 
   match L2D2.compute_post proc_data ~initial: Domain.empty with
   | Some post ->
       (* Remove local locks *)
       let post_without_locals : Domain.t =
         { 
           lockset = (Domain.Lockset.inter post.lockset post.wereLocked); 
           unlockset = post.unlockset; 
           dependencies = post.dependencies; 
           locked = post.locked; 
           unlocked = post.unlocked; 
           order = post.order; 
           wereLocked = post.wereLocked
         }
       in
       (* Report warnings *)
       DeadlockDomain.ReportSet.iter 
       (fun (dllock, dlloc, dlpname, dlstr, dltype) ->
           let locks : string sexp_list = List.fold dllock ~init:[] ~f:(fun accum elem ->
             accum@[(DeadlockDomain.LockWarning.make_string_of_lock elem)])
           in
           let message = F.asprintf "%s of %s at function '%s'\n"
             dlstr (String.concat ~sep:", " locks)  
             (Procname.to_string dlpname) 
           in
           let ltr : Errlog.loc_trace_elem list =
             [Errlog.make_trace_element 0 dlloc "" [Errlog.Procedure_start dlpname]]
           in
           Reporting.log_warning summary ~loc: dlloc ~ltr dltype message
       ) !DeadlockDomain.reportMap;
       DeadlockDomain.reportMap := DeadlockDomain.ReportSet.empty;
       F.printf "summary of %s:\n%a\n" (Procname.to_string (Procdesc.get_proc_name proc_desc)) DeadlockDomain.pp post_without_locals;
       Payload.update_summary post_without_locals summary
   | None ->
       summary
 
 (**
  * Deadlocks reporting by first creating a relation of all dependencies and 
  * computing the transitive closure of that relation. Deadlock is reported if 
  * some lock depends on itself in the transitive closure. Every deadlock found
  * by our analyser is reported twice, at each trace starting point.
  *)
 let report_deadlocks dependencies source_file =
 
   (* Returns set of all locks used in an analysed program. *)
   let get_all_locks : Domain.Edges.t -> Domain.Lockset.t =
     fun dependencies ->
       let set_of_all_locks = Domain.Lockset.empty in
       let f : Domain.Edges.elt -> Domain.Lockset.t -> Domain.Lockset.t =
         fun pair acc ->
           let first = Domain.Lockset.add (fst pair.edge) acc in
           let second = Domain.Lockset.add (snd pair.edge) acc in
           Domain.Lockset.union first second
       in
       Domain.Edges.fold f dependencies set_of_all_locks
   in
 
   (**
    * Creates a list from a set of locks used in an analysed program.
    * The lock index in this list serves as a lock index in the formed matrix. 
    *)
   let list_of_all_locks = Domain.Lockset.elements (get_all_locks dependencies) in
 
   let rec find : Domain.Lockset.elt -> Domain.Lockset.elt list -> int =
     fun x lst ->
       match lst with
       | [] -> raise (Failure "Not Found")
       | h :: t -> if Domain.LockEvent.equal x h then 0 else 1 + find x t
   in
 
   (* number of locks (matrix dimension) *)
   let n = (Domain.Lockset.cardinal (get_all_locks dependencies)) in
   let m = Array.make_matrix ~dimx:n ~dimy:n false in
 
   (* A matrix representing dependencies between locks. *)
   let matrix = Domain.Edges.fold (fun pair acc ->
         let first = find (fst pair.edge) list_of_all_locks in
         let second = find (snd pair.edge) list_of_all_locks in
         acc.(first).(second) <- true;
         acc) 
     dependencies m 
   in
 
   (* A Computing of transitive closure and reporting of deadlocks. *)
   for k = 0 to (n - 1) do
     for i = 0 to (n - 1) do
       for j = 0 to (n - 1) do
         matrix.(i).(j) <- matrix.(i).(j) || (matrix.(i).(k) && matrix.(k).(j));
         if(matrix.(i).(j) && (phys_equal i j)) then (
           (* Finding the first pair that is causing a deadlock. *)
           let first_pair =
             let e : Domain.Edge.t = 
               {edge = ((List.nth_exn list_of_all_locks k),(List.nth_exn list_of_all_locks j)); pname = Procname.empty_block}
             in 
             try Some (Domain.Edges.find e dependencies)
             with Caml.Not_found -> None
           in
           (* Finding the second pair that is causing a deadlock. *)
           let second_pair = 
             let e : Domain.Edge.t = 
               {edge = ((List.nth_exn list_of_all_locks j),(List.nth_exn list_of_all_locks k)); pname = Procname.empty_block}
             in
             try Some (Domain.Edges.find e dependencies)
             with Caml.Not_found -> None 
           in
           match (first_pair, second_pair) with
           | (Some a, Some b) ->
               if not(Domain.Edge.equal a.edge b.edge) then (
                 let message = F.asprintf "Deadlock between:\t%a\n\t\t\t%a\n"
                   Domain.Edge.pp a
                   Domain.Edge.pp b; 
                 in
                 let loc = (snd(fst(a.edge))) in
                 let ltr : Errlog.loc_trace_elem list =
                   [Errlog.make_trace_element 0 (snd(fst(a.edge))) "" [Errlog.Procedure_start a.pname]]
                 in
                 let issue : IssueLog.t =
                  Reporting.log_issue_external ~issue_log:IssueLog.empty a.pname Exceptions.Error ~loc ~ltr IssueType.deadlock message
                 in
                 IssueLog.store ~dir:Config.deadlock_issues_dir_name ~file:source_file issue
               )
           | (_,_) -> ()
         )
       done;
     done;
   done
 
 let reporting {Callbacks.procedures; source_file} =
   (* Getting all lock dependencies in the analysed program. *)
   let locks_dependencies = 
     List.fold ~f:(fun acc proc_name ->
             match Payload.read_toplevel_procedure proc_name with
             | Some summary -> Domain.Edges.union summary.dependencies acc
             | None -> acc
     ) ~init:Domain.Edges.empty procedures
   in  
   report_deadlocks locks_dependencies source_file 