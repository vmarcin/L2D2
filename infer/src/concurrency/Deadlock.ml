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
          (* F.printf "lock at line %a\n" Location.pp loc; *)
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
      let summ : Domain.t =
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
      (* F.printf "summary of %s:\n%a\n" (Procname.to_string (Procdesc.get_proc_name proc_desc)) DeadlockDomain.pp summ; *)
      Payload.update_summary summ summary
  | None ->
      summary
 
(* *
 * Deadlocks reporting by first finding an oposite dependencies and
 * then checking for guard locks
 *)
let report_deadlocks dependencies =
  let should_report (edge: Domain.Edge.t) (edge': Domain.Edge.t) deps =
    let (lock1,lock2) = edge.edge in 
    let pname1 = edge.pname in 
    let pname2 = edge'.pname in

    let get_guards lock pname =
      let guard_deps = 
        Domain.Edges.filter ( fun dep -> 
          (Domain.LockEvent.equal (snd dep.edge) lock) && (Procname.equal dep.pname pname)
        ) deps 
      in
      Domain.Edges.fold ( fun e acc -> 
        Domain.Lockset.add (fst e.edge) acc
      ) guard_deps Domain.Lockset.empty 
    in
    let common_guards = 
      Domain.Lockset.inter (get_guards lock1 pname1) (get_guards lock1 pname2)
      |> Domain.Lockset.inter (get_guards lock2 pname1) 
      |> Domain.Lockset.inter (get_guards lock2 pname2)
    in
    if  (Domain.Lockset.is_empty common_guards) then true else false
  in 

  let potential_deadlocks = 
    Domain.Edges.fold ( fun dep acc ->
      let reverse = 
        Domain.Edges.filter (fun dep' -> 
          Domain.Edge.may_deadlock dep dep'
        ) dependencies 
      in
      List.append [(dep, reverse)] acc
    ) dependencies [] 
  in

  List.fold potential_deadlocks ~init:IssueLog.empty ~f:(fun issue_log ((dep: Domain.Edge.t), rev) -> 
    Domain.Edges.fold (fun e log_report ->
      if (should_report dep e dependencies) then (
        (* F.printf "DEADLOCK %a  %a\n" Domain.Edge.pp dep Domain.Edge.pp e; *)
        let message = F.asprintf "Deadlock between:\t%a\n\t\t\t%a\n"
          Domain.Edge.pp dep
          Domain.Edge.pp e; 
        in
        let loc = (snd(fst(dep.edge))) in
        let ltr : Errlog.loc_trace_elem list =
          [Errlog.make_trace_element 0 (snd(fst(dep.edge))) "" [Errlog.Procedure_start dep.pname]]
        in
        Reporting.log_issue_external ~issue_log:log_report dep.pname Exceptions.Error ~loc ~ltr IssueType.deadlock message
      ) else log_report
    ) rev issue_log )
   
let reporting {Callbacks.procedures; source_file} =
  (* Getting all lock dependencies in the analysed program. *)
  let locks_dependencies = 
    List.fold ~f:(fun acc proc_name ->
            match Payload.read_toplevel_procedure proc_name with
            | Some summary -> Domain.Edges.union summary.dependencies acc
            | None -> acc
    ) ~init:Domain.Edges.empty procedures
  in  
  report_deadlocks locks_dependencies
  |> IssueLog.store ~dir: Config.deadlock_issues_dir_name ~file:source_file