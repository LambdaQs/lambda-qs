module NoClone
open FStar.Mul
module L = FStar.List
module T = FStar.List.Tot





let noClonePair (p: (nat & nat)) : bool = fst p <> snd p 

let safepair = p: (nat & nat) { noClonePair p }


let makeSafepair (p : (nat & nat)) : safepair = if fst p <> snd p then p else (fst p, snd p + 1)



let s1 : safepair = (4,5)

let b : (v:bool {v = false}) = (3,5) = (4,5)


let safelist = l:list nat { (forall (x y:(n:nat{n < T.length l})). x <> y ==> T.nth l x <> T.nth l y) }

(*
let safelistpaid = p:(list nat & list nat) { T.length (fst p) = T.length (snd
*)

let cnot (s:safepair) : unit = ()

let safecnot (p : (nat & nat)) : unit = ()

let qList = (nat & nat) 






val qNth : ql:qList -> i:nat { i < snd ql } -> Tot (j:nat { j = (fst ql) + i }) (* note how the type just says what function is *)
let qNth (ql:qList) i = (fst ql) + i


val qLength : qList -> nat
let qLength ql = snd ql


(* is there a way to make safeQzip such that the resulting type is just list (nat & nat) if not safe? *)
val safeQzip : ql:qList -> ql1:qList { qLength ql1 = qLength ql /\ fst ql1 <> fst ql } -> (Tot (l:list safepair { T.length l = snd ql } )) (decreases (snd ql)) 
let rec safeQzip ql ql1 = match ql with
  | (i, 0) -> []
  | (i, j) -> match ql1 with 
             | (i1, j) -> (i,i1) :: (safeQzip (i+1, j-1) (i1+1, j-1))


(* is there a way to make safeQzip such that the resulting type is just list (nat & nat) if not safe? *)
val qzip : ql:qList -> ql1:qList { qLength ql1 = qLength ql } -> (Tot (l:list (nat & nat) { T.length l = snd ql } )) (decreases (snd ql)) 
let rec qzip ql ql1 = match ql with
  | (i, 0) -> []
  | (i, j) -> match ql1 with 
             | (i1, j) -> (i,i1) :: (qzip (i+1, j-1) (i1+1, j-1))




val qMost : ql:qList{ qLength ql >= 1 } -> qList
let qMost ql = match ql with
  | (s, l) -> (s, l - 1)


val qRest : ql:qList{ qLength ql >= 1 } -> qList
let qRest ql = match ql with
  | (s, l) -> (s + 1, l - 1)




(* similar to map, but only for operations *) 
val applyToEach : f:('a -> unit) -> list 'a -> unit 
let rec applyToEach f l = let crush u1 u2 = u1 in 
                      match l with 
                      | [] -> ()
                      | a :: l' -> crush (f a) (applyToEach f l')





val cnotchain : ql:qList { qLength ql >= 2 } -> unit
let cnotchain ql = applyToEach cnot (safeQzip (qMost ql) (qRest ql))



val cnotchainbad :  ql:qList { snd ql >= 1 } -> unit
let cnotchainbad ql = applyToEach safecnot (qzip ql ql)



(* another interesting example *)
val cnot_1_4 : ql:qList{ qLength ql > 1 } -> ql1:qList { qLength ql1 > 4 /\ fst ql1 + 3 <> fst ql } -> unit
let cnot_1_4 ql ql1 = cnot (qNth ql 1, qNth ql1 4)
