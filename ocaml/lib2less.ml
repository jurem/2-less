open Printf

(******** triplet printing *)

let print_tri (x, y, z) =
	printf "(%d,%d,%d) " x y z

let print_tris tris =
	List.iter print_tri tris ;
	printf "\n%!"

(******** generating all triplets in range 0..n-1 *)

let gen_tris n = 
	List.flatten (List.flatten
		(List.init n (fun x ->
			List.init n (fun y -> 
				List.init n (fun z ->
					(x, y, z)
		)))
	))

(******** triplet comparisons *)

let lt1 (a, b, c) (x, y, z) =
	a < x || b < y || c < z

let gt1 x y = lt1 y x

let lt2 (a, b, c) (x, y, z) =
	(a < x && (b < y || c < z)) || (b < y && c < z)

let gt2 x y = lt2 y x

let lt3 (a, b, c) (x, y, z) =
	a < x && b < y && c < z

let gt3 x y = lt3 y x

let le3 (a, b, c) (x, y, z) =
	a < x && b <= y && c <= z || a == x && b < y && c <= z || a == x && b == y && c < z

let ge3 x y = le3 y x

(* default comparison is 2-less *)

let lt = lt2

let gt = gt2


(******** interesting prefixes *)

let get_prefix i =
	match i with
		| 0 -> []
		| 1 -> [(0,0,0)]
		| 2 -> [(1,0,1); (0,0,0)]
		| 3 -> [(0,1,2); (1,0,1); (0,0,0)]
		| 4 -> [(1,1,3); (0,1,2); (1,0,1); (0,0,0)]
		| _ -> []


(******** filtering *)

(* filter candidates so that all are > any in tris *)
let filter_gt tris cands =
	let lts tri =
		List.for_all (gt tri) tris
	in
		List.filter lts cands

let filter_dominated tris =
	let is_dominating tris tri =
		not (List.exists (ge3 tri) tris)
	in
		List.filter (is_dominating tris) tris


(******** enumerate all paths *)

let solve_all_from n init_sol callback =
	let max_len = ref 0 in
	let count = ref 0 in
	let rec solve_rec n cands sol =
		let cands' = filter_gt sol cands in (
			if cands' == [] then
				let l = List.length sol in begin
					if l > !max_len then count := 0;
					if l >= !max_len then (
						count := !count + 1;
						max_len := l;
						callback count (List.rev sol)
					)
				end
			else
				List.iter (fun c -> solve_rec n (cands') (c::sol)) cands'
		)
	in
		let init_cands  = filter_gt init_sol (gen_tris n) in (
			solve_rec n init_cands init_sol;
			!count
		)

let enum_all_from n init_sol =
	solve_all_from n init_sol (fun no sol -> print_tris sol)

let count_all_from n init_sol =
	solve_all_from n init_sol (fun no sol -> ())


(******** branch & reduce algorithms *)

let solve_from n init_sol callback =
	let max_len = ref 0 in
	let count = ref 0 in
	let rec solve_rec n cands sol =
		let cands' = filter_gt sol cands in (
			(*if List.length sol == 5 then printf "*" ;
			if List.length sol == 6 then printf "." ;*)
			if cands' == [] then
				let l = List.length sol in (
					if l > !max_len then count := 0;
					if l >= !max_len then (
						count := !count + 1;
						max_len := l ;
						callback count (List.rev sol)
					)
				)
			else
				let cs = filter_dominated cands' in begin
(*					printf "Filter candidates\n";
					printf "%d %d\n" (List.length cands') (List.length cs);
					print_tris cands';
					printf "----\n";
					print_tris cs;*)
					List.iter (fun c -> solve_rec n (cands') (c::sol)) cs
				end
		)
	in
		let init_cands  = filter_gt init_sol (gen_tris n) in (
(*			printf "Candidates\n";
			print_tris init_cands;*)
			solve_rec n init_cands init_sol;
			!count
		)

let enum_from n init_sol =
	solve_from n init_sol (fun no sol -> print_tris sol)

