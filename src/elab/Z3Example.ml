(* So far I haven't been able to get z3 to cooperate on my machine, but assuming it was built correctly, this should be a working example.

   Assuming Z3 is installed, compile with:

   ocamlfind ocamlc -o z3example.byte -thread -package z3 -linkpkg Z3Example.ml

   Then run with './z3example.byte'
*)

let ctx = Z3.mk_context []
let solver = Z3.Solver.mk_solver ctx None

(* Create symbols x, y *)
let x = Z3.Arithmetic.Integer.mk_const_s ctx "x"
let y = Z3.Arithmetic.Integer.mk_const_s ctx "y"

(* Add the constraints 2 < y, x + y < 5 *)
let constraint1 = Z3.Arithmetic.mk_lt ctx (Z3.Arithmetic.Integer.mk_numeral_i ctx 2) y
let constraint2 = Z3.Arithmetic.mk_lt ctx (Z3.Arithmetic.mk_add ctx [x ; y]) (Z3.Arithmetic.Integer.mk_numeral_i ctx 5)
let () = Z3.Solver.add solver [constraint1 ; constraint2]

(* Check if the system is satisfiable *)
let main () = 
   match Z3.Solver.check solver [] with
   | UNSATISFIABLE -> Printf.printf "unsatisfiable\n"
   | UNKNOWN -> Printf.printf "unknown\n"
   | SATISFIABLE ->
      (Printf.printf "satisfiable\n";
      (* Get a model *)
      match Z3.Solver.get_model solver with
      | None -> ()
      | Some model ->
         Printf.printf "%s\n"
               (Z3.Model.to_string model))

let () = main ()