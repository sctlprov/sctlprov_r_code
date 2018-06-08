open Term
open Formula
open Modul

(* type continuation = 
	| Basic of bool
	| Cont of State_set.t * formula * string * continuation * continuation * ((string * (int array)) list) * ((string * (int array)) list) *)

type fml_state_tbl = (string, State_set.t) Hashtbl.t

exception Error_proving_atomic
exception Unable_to_prove
exception Prove_break

(* let add_true_to_cont levl s cont = 
	match cont with
	| Cont (gamma, fml, cont_levl, contl, contr, ts, fs) -> Cont (gamma, fml, cont_levl, contl, contr, (levl, s)::ts, fs)
	| _ -> cont

let add_false_to_cont levl s cont = 
	match cont with
	| Cont (gamma, fml, cont_levl, contl, contr, ts, fs) -> Cont (gamma, fml, cont_levl, contl, contr, ts, (levl, s)::fs)
	| _ -> cont *)

(*whether state s is already in an existing merge*)
let merges = Hashtbl.create 10
let true_merge = Hashtbl.create 10
let false_merge = Hashtbl.create 10
let pre_process_merges sub_fml_tbl = 
	Hashtbl.iter (fun a b -> Hashtbl.add merges a State_set.empty) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add true_merge a (State_set.empty)) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add false_merge a (State_set.empty)) sub_fml_tbl
(* let post_process_merges () = 
	Hashtbl.iter (fun a b -> print_endline (a ^ ": " ^ (string_of_int (State_set.cardinal b)))) merges *)

let state_in_merge merg fml st = 
	let sts = Hashtbl.find merg fml in State_set.mem st sts
let add_merge merg fml sts = 
	let sts' = Hashtbl.find merg fml in
	Hashtbl.replace merg fml (State_set.union sts sts')

let is_in_true_merge s levl = 
	try
		State_set.mem s (Hashtbl.find true_merge levl)
	with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1

let is_in_false_merge s levl = 
	State_set.mem s (Hashtbl.find false_merge levl)

let add_to_true_merge s levl = 
	try
		let bss = Hashtbl.find true_merge levl in
		Hashtbl.replace true_merge levl (State_set.add s bss)
	with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1
let union_to_true_merge ss levl =  Hashtbl.replace true_merge levl (State_set.union ss (Hashtbl.find true_merge levl))
let minus_from_true_merge ss levl = Hashtbl.replace true_merge levl (State_set.diff (Hashtbl.find true_merge levl) ss)
let clear_true_merge levl = Hashtbl.replace true_merge levl State_set.empty
let add_to_false_merge s levl = 
	try
		let bss = Hashtbl.find false_merge levl in
		Hashtbl.replace false_merge levl (State_set.add s bss)
	with Not_found -> print_endline ("level not found in finding false merge: "^levl); exit 1
let union_to_false_merge ss levl = Hashtbl.replace false_merge levl (State_set.union ss (Hashtbl.find false_merge levl))
let minus_from_false_merge ss levl = Hashtbl.replace false_merge levl (State_set.diff (Hashtbl.find false_merge levl) ss)
let clear_false_merge levl = Hashtbl.replace false_merge levl State_set.empty
	

(* produce new continuations *)
(* let rec make_ax_cont gamma s fml levl sl contl contr = 
	(* State_set.fold (fun a c -> Cont (gamma, Formula.subst_s fml s (State a), levl, c, contr)) sl contl *)
	State_set.fold ( fun elem b ->
				Cont(State_set.empty, subst_s fml s (State elem), levl^"1", b, contr, [], [])
			) sl contl
let rec make_ex_cont gamma s fml levl sl contl contr =
	(* State_set.fold (fun a c -> Cont (gamma, Formula.subst_s fml s (State a), levl, contl, c)) sl contr *)
	State_set.fold (fun elem b ->
				Cont(State_set.empty, subst_s fml s (State elem), levl^"1", contl, b, [], [])
			) sl contr
let rec make_af_cont gamma x s fml levl sl contl contr =
	(* State_set.fold (fun a c -> Cont (gamma, AF (s, fml, (State a)), levl, c, contr)) sl contl *)
	State_set.fold (fun elem b ->
        Cont (State_set.add s gamma, AF(x, fml, State elem), levl, b, contr, [], [])) sl (add_true_to_cont levl (s) contl)
let rec make_eg_cont gamma s fml levl sl contl contr =
	State_set.fold (fun a c -> Cont (gamma, EG (s, fml, (State a)), levl, contl, c)) sl contr
let rec make_ar_cont gamma s s' fml1 fml2 levl sl contl contr =
	State_set.fold (fun a c -> Cont (gamma, AR (s, s', fml1, fml2, (State a)), levl, c, contr)) sl contl
let rec make_eu_cont gamma s s' fml1 fml2 levl sl contl contr =
	State_set.fold (fun a c -> Cont (gamma, EU (s, s', fml1, fml2, (State a)), levl, contl, c)) sl contr *)
	
let prove_atomic s sl modl = 
	match s with
	| "has_next" -> State_set.is_empty (next (get_array_from_state (List.hd sl)) modl.transitions modl.var_index_tbl)
	| _ -> (try (match apply_atomic (Hashtbl.find modl.atomic_tbl s) sl modl.var_index_tbl with
			| Top -> true
			| Bottom -> false
			| _ -> raise Error_proving_atomic) with Not_found -> print_endline ("Did not find atomic formula: "^s); exit 1) 

let rec prove_resursive gamma fml levl modl = 
	match fml with
	| Top -> true
	| Bottom -> false
	| Atomic (s, sl) -> if prove_atomic s sl modl then true else false
	| Neg Atomic (s, sl) -> if prove_atomic s sl modl then false else true
	| And (fml1, fml2) -> 
		let b1 = prove_resursive State_set.empty fml1 (levl^"1") modl in
		if not b1 then 
			false 
		else 
			let b2 = prove_resursive State_set.empty fml2 (levl^"2") modl in
			if b2 then 
				true 
			else 
				false
	| Or (fml1, fml2) -> 
		let b1 = prove_resursive State_set.empty fml1 (levl^"1") modl in
		if b1 then 
			true 
		else 
			let b2 = prove_resursive State_set.empty fml2 (levl^"2") modl in
			if b2 then 
				true 
			else 
				false
	| AX (s, fml1, State sa) -> 
		let nexts = next sa modl.transitions modl.var_index_tbl in
		let flag = ref true in 
		begin try
			(State_set.iter (fun a -> if not !flag then () else (if prove_resursive State_set.empty (Formula.subst_s fml1 s (State a)) (levl^"1") modl then () else flag := false)) nexts; !flag)
		with Prove_break -> false
		end
	| EX (s, fml1, State sa) -> 
		let nexts = next sa modl.transitions modl.var_index_tbl in
		let flag = ref false in
		begin try
			(State_set.iter (fun a -> if !flag then (raise Prove_break) else (if prove_resursive State_set.empty (Formula.subst_s fml1 s (State a)) (levl^"1") modl then (flag := true) else ())) nexts; !flag)
		with Prove_break -> true
		end
	| AF (s, fml1, State sa) -> 
		let result = ref true in
		if State_set.mem sa gamma then begin
			State_set.iter (fun s -> add_to_false_merge s levl) gamma;
			result := false 
		end else begin
			let nexts = next sa modl.transitions modl.var_index_tbl in
			let flag = ref true in
			if prove_resursive State_set.empty (Formula.subst_s fml1 s (State sa)) (levl^"1") modl then 
				result := true 
			else begin try
				(State_set.iter (fun a -> if not !flag then () else (if prove_resursive (State_set.add sa gamma) (AF(s, fml1, State a)) levl modl then () else flag := false)) nexts; result := !flag)
			with Prove_break -> result := false
			end
		end;
		if !result = true then
			add_to_true_merge sa levl;
		!result
	| EG (s, fml1, State sa) -> 
			let result = ref false in
			if State_set.mem sa gamma then begin
				State_set.iter (fun s -> add_to_true_merge s levl) gamma;
				result := true 
			end else begin
				let nexts = next sa modl.transitions modl.var_index_tbl in
				let flag = ref false in
				if not (prove_resursive State_set.empty (Formula.subst_s fml1 s (State sa)) (levl^"1") modl) then 
					result := false 
				else begin try
					(State_set.iter (fun a -> if !flag then () else (if prove_resursive (State_set.add sa gamma) (EG (s, fml1, State a)) levl modl then (flag := true) else ())) nexts; result := !flag)
				with Prove_break -> result := true
				end
			end;
			if !result = false then
				add_to_false_merge sa levl;
			!result
	| AR (x, y, fml1, fml2, State sa) -> 
		let result = ref true in
		if (State_set.is_empty gamma) then 
			Hashtbl.replace merges levl State_set.empty 
		else 
			add_merge merges levl gamma; 
		if State_set.mem sa gamma then 
			result := true
		else begin
			if state_in_merge merges levl sa then 
				result := true 
			else
				if prove_resursive State_set.empty (Formula.subst_s fml2 y (State sa)) (levl^"2") modl then 
					(
						if prove_resursive State_set.empty (Formula.subst_s fml1 x (State sa)) (levl^"1") modl then 
							result := true
						else 
							let nexts = next sa modl.transitions modl.var_index_tbl in
							let flag = ref true in
							try
								(State_set.iter (fun a -> if not !flag then (raise Prove_break) else (if prove_resursive (State_set.add sa gamma) (AR (x, y, fml1, fml2, State a)) levl modl then () else flag := false)) nexts; result := !flag)								
							with Prove_break ->
								result := false
					) 
				else 
					result := false
		end;
		!result
	| EU (s, s', fml1, fml2, State sa) -> 
		if (State_set.is_empty gamma) then 
			Hashtbl.replace merges levl State_set.empty 
		else 
			add_merge merges levl gamma; 
		if State_set.mem sa gamma then 
			(false) 
		else 
			(if state_in_merge merges levl sa then 
				false 
			else
				if not (prove_resursive State_set.empty (Formula.subst_s fml2 s' (State sa)) (levl^"2") modl) then 
					(
						if not (prove_resursive State_set.empty (Formula.subst_s fml1 s (State sa)) (levl^"1") modl) then 
							false
						else 
							let nexts = next sa modl.transitions modl.var_index_tbl in
							let flag = ref false in
							try
								(State_set.iter (fun a -> if !flag then (raise Prove_break) else (if prove_resursive (State_set.add sa gamma) (EU (s, s', fml1, fml2, State a)) levl modl then (flag := true) else ())) nexts; !flag)
							with Prove_break ->
								true
					) 
				else 
					true
			)
	| _ -> raise Unable_to_prove



let rec prove_model modl = 
	let spec_lst = modl.spec_list in 
	let rec prove_lst lst = 
	match lst with
	| [] -> ()
	| (s, fml) :: lst' -> ((let nnf_fml = nnf fml in 
							print_endline (fml_to_string (nnf_fml));
							pre_process_merges (select_sub_fmls (sub_fmls nnf_fml "1"));
							(* let b = (prove (Cont (State_set.empty, Formula.subst_s (nnf_fml) (SVar "ini") modl.model_init_state, "1", Basic true, Basic false)) modl) in *)
							let b = (prove_resursive State_set.empty (Formula.subst_s (nnf_fml) (SVar "ini") (State modl.init_assign)) "1" modl) in
							 print_endline (s ^ ": " ^ (string_of_bool b)));
							 prove_lst lst') in prove_lst spec_lst








