open Lib2less

let () = 
	let n = int_of_string (Sys.argv.(1)) in
	let arg2 = if Array.length Sys.argv >= 2
			   then int_of_string Sys.argv.(2) else 0 in
	let init_sol = Lib2less.get_prefix arg2
	in begin
		Printf.printf "count = %d\n" (Lib2less.enum_from n init_sol)
	end
