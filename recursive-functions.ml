(* week-06.ml *)
(* Introduction to Computer Science (YSC1212), Sem2, 2020-2021 *)
(* A miscellany of recursive programs from Week 06 *)

(* --------------------- *)

let show_bool b =
  (* show_bool : bool -> string *)
  if b
  then "true"
  else "false";;

let show_char c =
  (* show_char : char -> string *)
  "'" ^ (if c = '\\' then "\\\\" else if c = '\'' then "\\\'" else String.make 1 c) ^ "'";;

let show_string s =
  (* show_string : string -> string *)
  "\"" ^ s ^ "\"";;

let show_int n =
  (* show_int : int -> string *)
  if n < 0
  then "(" ^ string_of_int n ^ ")"
  else string_of_int n;;

let show_unit () =
  (* show_unit : unit -> string *)
  "()";;

(* --------------------- *)

(* tests for unary functions taking an integer that test it once *)

let positive_random_test_for_unary_function_taking_an_integer_once r name candidate witness show_result =
  let n = Random.int r
  in let expected_result = witness n
     and actual_result = candidate n
     in if actual_result = expected_result
        then true
        else let () = Printf.printf "testing %s for %d failed with result %s instead of %s\n" name n (show_result actual_result) (show_result expected_result)
             in false;;

let positive_inductive_test_for_unary_function_taking_an_integer_once r name candidate zero_case succ_case show_result =
  let actual_zero_case = candidate 0
  in let test_zero_case = (actual_zero_case = zero_case)
     in let n' = Random.int r
        in let actual_succ_case = candidate (succ n') and expected_succ_case = succ_case n' (candidate n')
           in let test_succ_case = (actual_succ_case = expected_succ_case)
              in if test_zero_case && test_succ_case
                 then true
                 else if not test_zero_case && test_succ_case
                 then let () = Printf.printf "testing %s for zero case failed with result %s instead of %s\n" name (show_result actual_zero_case) (show_result zero_case)
                      in false
                 else if test_zero_case && not test_succ_case
                 then let () = Printf.printf "testing inductive case of %s for %d failed with successor of %d resulting in %s whereas applying the correct successor function to result of applying %s to %d should give %s\n" name n' n' (show_result actual_succ_case) name n' (show_result expected_succ_case)
                      in false
                 else let () = Printf.printf "testing %s for zero case failed with result %s instead of %s and testing inductive case for %d failed with successor of %d resulting in %s whereas applying the correct successor function to result of applying %s to %d should give %s\n" name (show_result actual_zero_case) (show_result zero_case) n' n' (show_result actual_succ_case) name n' (show_result expected_succ_case)
                      in false;;

(* function which repeatedly applies a test to a candidate function, given in lecture notes *)

let repeat n_given test candidate =
  let () = assert (n_given >= 0)in
  let rec visit n =
    if n = 0
    then true
    else test candidate && visit (n - 1)
  in visit n_given;;

(* --------------------- *)

(* nat_fold_right, given in lecture notes *)

let nat_fold_right zero_case succ_case n_given =
  (* nat_fold_right : 'a -> ('a -> 'a) -> int -> 'a *)
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then zero_case
    else let n' = n - 1
         in let ih = visit n'
            in succ_case ih
  in visit n_given;;

(* nat_parafold_right, given in lecture notes *)

let nat_parafold_right zero_case succ_case n_given =
  (* nat_parafold_right : 'a -> (int -> 'a -> 'a) -> int -> 'a *)
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then zero_case
    else let n' = n - 1
         in let ih = visit n'
            in succ_case n' ih    (* <-- succ_case takes two arguments *)
  in visit n_given;;

(* --------------------- *)

(* Exercise 1 *)

(* version 1 of test_power_p

let test_power p =
  (* a few handpicked numbers: *)
  let b0 = (p 2 0 = 1)
  and b1 = (p 2 1 = 2)
  and b2 = (p 2 2 = 4)
  and b3 = (p 2 3 = 8)
  and b4 = (p 2 4 = 16)
  and b5 = (p 2 5 = 32)
  and b6 = (p 10 2 = 100)
  (* base case: *)
  and b7 = (let x = Random.int 1000
	    in p x 0 = 1)
  (* an instance of the induction step: *)
  and b8 = (let y = Random.int 10
	    and x = Random.int 10
	    in p x (succ y) = (p x y) * x)
             (* etc. *)
  in b0 && b1 && b2 && b3 && b4 && b5 && b6 &&  b7 && b8;;
 *)

let test_power candidate =

  (* a few handpicked numbers *)
  let b0 = (let expected_result = 100
            and actual_result = candidate 10 2
            in if actual_result = expected_result
               then true
               else let () = Printf.printf "test_power failed in b0 for %d as base and %d as exponent with result %d instead of %d\n" 10 2 actual_result expected_result
                    in false)
  and b1 = (let expected_result = 1024
            and actual_result = candidate 2 10
            in if actual_result = expected_result
               then true
               else let () = Printf.printf "test_power failed in b1 for %d as base and %d as exponent with result %d instead of %d\n" 2 10 actual_result expected_result
                    in false)

  (* testing the base case *)
  and b2 = (let x = Random.int 100
            in let expected_result = 1
               and actual_result = candidate x 0
               in if actual_result = expected_result
                  then true
                  else let () = Printf.printf "test_power failed in b2 with %d as random base and 0 as exponent with result %d instead of %d\n" x actual_result expected_result
                       in false)

  (* checking an absorbing element for exponentiation *)
  and b3 = (let n = Random.int 15 + 1
            in let expected_result = 0
               and actual_result = candidate 0 n
               in if actual_result = expected_result
                  then true
                  else let () = Printf.printf "test_power failed in b3 for with 0 as base and %d as random exponent with result %d instead of %d\n" n actual_result expected_result
                       in false)

  (* checking another absorbing element for exponentiation *)
  and b4 = (let n = Random.int 15
            in let expected_result = 1
               and actual_result = candidate 1 n
               in if actual_result = expected_result
                  then true
                  else let () = Printf.printf"test_power failed in b4 with 1 as base and %d as random exponent with result %d instead of %d\n" n actual_result expected_result
                       in false)
  (* checking the identity element for exponentiation *)
  and b5 = (let x = Random.int 100
            in let actual_result = candidate x 1
               and expected_result = x
               in if actual_result = expected_result
                  then true
                  else let () = Printf.printf "test_power failed in b5 with %d as random base and 1 as exponent with result %d instead of %d\n" x actual_result expected_result
                       in false)
  (* checking a property of exponentiation *)
  and b6 = (let x = Random.int 100
            and m = Random.int 10
            and n = Random.int 10
            in let p1 = candidate x (m + n)
               and p2 = candidate x m * candidate x n
               in if p1 = p2
                  then true
                  else let () = Printf.printf
                                  "test_power failed in b6 with %d as random base and (%d + %d) as exponent because %d != %d\n" x m n p1 p2
                       in false)
  in b0 && b1 && b2 && b3 && b4 && b5 && b6;;

let power x y =
  let () = assert (y >= 0) in
  nat_fold_right 1 (fun ih -> x * ih) y;;

let () = assert (test_power power);;

(* --------------------- *)

(* Exercise 2 *)

(* version 1 of test oddp
let test_oddp candidate =
      (* a few handpicked numbers: *)
  let b1 = (candidate 1 = true)
  and b2 = (candidate 2 = false)
  and b3 = (candidate 3 = true)
  and b4 = (candidate 4 = false)
  and b5 = (candidate 5 = true)
  and b6 = (candidate 1000 = false)
  and b7 = (candidate 1001 = true)
      (* testing the completeness of the odd predicate: *)
  and b8 = (let n = Random.int 1000
            in candidate (2 * n) = false)
  and b9 = (let n = Random.int 1000
            in candidate (2 * n + 1) = true)
      (* an instance of the base case: *)
  and bc = (candidate 0 = false)
      (* an instance of the induction step: *)
  and is = (let n' = Random.int 1000
            in candidate (succ n') = not (candidate n'))
  (* etc. *)
  in b1 && b2 && b3 && b4 && b5 && b6 && b7 && b8 && b9 && bc && is;;
 *)

let positive_random_test_oddp_once r name candidate =
  positive_random_test_for_unary_function_taking_an_integer_once r name candidate (fun n -> n mod 2 = 1) show_bool;;

let positive_inductive_test_oddp_once r name candidate =
  let oddp_succ_case n' ih = not ih in
  positive_inductive_test_for_unary_function_taking_an_integer_once r name candidate false oddp_succ_case show_bool;;

let test_oddp r name candidate =
  repeat 1000 (positive_random_test_oddp_once r name) candidate && repeat 1000 (positive_inductive_test_oddp_once r name) candidate;;

let oddp =
  nat_fold_right false not;;

let () = assert (test_oddp 1000 "oddp" oddp);;

(* --------------------- *)

(* Exercise 3 *)

(* version 1 of test_fac:
let test_fac candidate =
  (* intuitive numbers: *)
  let b1 = (candidate 1 = 1)
  and b2 = (candidate 2 = 2)
  and b3 = (candidate 3 = 6)
  and b4 = (candidate 4 = 24)
  and b5 = (candidate 5 = 120)
  (* base case: *)
  and bc = (candidate 0 = 1)
  (* instance of the induction step: *)
  and is = (let k = Random.int 20
            in candidate (k + 1) = (candidate k) * (k + 1))
  (* etc. *)
  in b1 && b2 && b3 && b4 && b5 && bc && is;;
 *)

let positive_random_test_fac_once r name candidate =
  let fac_witness_fun n_given = let () = assert (n_given >= 0) in
                                nat_parafold_right 1 (fun n' ih -> (succ n') * ih) n_given in
  positive_random_test_for_unary_function_taking_an_integer_once r name candidate fac_witness_fun show_int;;

let positive_inductive_test_fac_once r name candidate =
  let fac_succ_case n' ih = succ n' * ih in
  positive_inductive_test_for_unary_function_taking_an_integer_once r name candidate 1 fac_succ_case show_int;;

let test_fac r name candidate =
  repeat 1000 (positive_random_test_fac_once r name) candidate && repeat 1000 (positive_inductive_test_fac_once r name) candidate;;

(* folded version: *)

(* stores the count and the result in the inductive hypothesis *)

let fac n_given =
  let () = assert (n_given >= 0) in
  let (count, result) =
    let inductive_fun ih =
      let (x', x'_fac) = ih in
      let x = x' + 1 in
      (x, x * x'_fac) in
    nat_fold_right (0, 1) inductive_fun n_given in
  result;;

(* unfolded version *)
let fac n_given =
  let () = assert (n_given >= 0) in
  let (count, result) = nat_fold_right (0, 1) (fun (x', x'_fac) -> (x' + 1, (x' + 1) * x'_fac)) n_given in
  result;;

let () = assert (test_fac 100 "fac" fac);;

(* --------------------- *)

(* Exercise 4 *)

(* version 1 of test_sumtorial:
let test_sumtorial candidate =
  (* intuitive numbers: *)
  let b1 = (candidate 1 = 1)
  and b2 = (candidate 2 = 3)
  and b3 = (candidate 3 = 6)
  and b4 = (candidate 4 = 10)
  and b5 = (candidate 5 = 15)
  (* base case: *)
  and bc = (candidate 0 = 0)
  (* instance of the induction step: *)
  and is = (let k = Random.int 20
            in candidate (k + 1) = (candidate k) + (k + 1))
  in b1 && b2 && b3 && b4 && b5 && bc && is;;
 *)

let positive_random_test_sumtorial_once r name candidate =
  let sumtorial_witness_fun n_given = let () = assert (n_given >= 0) in
                                      n_given * (n_given + 1) / 2 in
  positive_random_test_for_unary_function_taking_an_integer_once r name candidate sumtorial_witness_fun show_int;;

let positive_inductive_test_sumtorial_once r name candidate =
  let sumtorial_succ_case n' ih = succ n' + ih in
  positive_inductive_test_for_unary_function_taking_an_integer_once r name candidate 0 sumtorial_succ_case show_int;;

let test_sumtorial r name candidate =
  repeat 1000 (positive_random_test_sumtorial_once r name) candidate && repeat 1000 (positive_inductive_test_sumtorial_once r name) candidate;;

(* recursive implementation *)

let sumtorial_v1 =
  nat_parafold_right 0 (fun n' ih -> (succ n') + ih);;

let () = assert (test_sumtorial 1000 "sumtorial_v1" sumtorial_v1);;

(* non-recursive implementation *)

let sumtorial_v2 n_given =
  let () = assert (n_given >= 0) in
  n_given * (n_given + 1) / 2;;

let () = assert (test_sumtorial 1000 "sumtorial_v2" sumtorial_v2);;

(* --------------------- *)

(* Exercise 5 *)

(* version 1 of test_sum
let test_sum candidate =
  (* base case: *)
  let f1 x = x + 2
  and f2 x = x * x
  and f3 x = 5
  and f4 x = x * x * x + 3 * x * x
  and f5 x = x
  and test_base_case f =
    (candidate f 0 = f 0)
  and test_inductive_case f =
    (let k = Random.int 20 in
     candidate f (succ k) = (candidate f k) + f (succ k)) in
  test_base_case f1 && test_base_case f2 && test_base_case f3 &&
    test_base_case f4 && test_base_case f5 &&
      test_inductive_case f1 && test_inductive_case f2 && test_inductive_case f3 &&
        test_inductive_case f4 && test_inductive_case f5;;
 *)

let test_sum_once r f fun_name candidate candidate_name =
  let actual_zero_case = candidate f 0 and expected_zero_case = f 0
  in let test_zero_case = (actual_zero_case = expected_zero_case)
     in let n' = Random.int r
        in let actual_succ_case = candidate f (succ n') and expected_succ_case = (candidate f n') + f (succ n')
           in let test_succ_case = (actual_succ_case = expected_succ_case)
              in if test_zero_case && test_succ_case
                 then true
                 else if not test_zero_case && test_succ_case
                 then let () = Printf.printf "testing %s with function %s for zero case failed with result %s instead of %s\n" candidate_name fun_name (show_int actual_zero_case) (show_int expected_zero_case)
                      in false
                 else if test_zero_case && not test_succ_case
                 then let () = Printf.printf "testing inductive case of %s with function %s for %d failed with successor of %d resulting in %s whereas applying the correct successor function to result of applying %s to %d should give %s\n" candidate_name fun_name n' n' (show_int actual_succ_case) candidate_name n' (show_int expected_succ_case)
                      in false
                 else let () = Printf.printf "testing %s with function %s for zero case failed with result %s instead of %s and testing inductive case for %d failed with successor of %d resulting in %s whereas applying the correct successor function to result of applying %s to %d should give %s\n" candidate_name fun_name (show_int actual_zero_case) (show_int expected_zero_case) n' n' (show_int actual_succ_case) candidate_name n' (show_int expected_succ_case)
                      in false;;

let test_sum r candidate candidate_name =
  (test_sum_once r (fun x -> x + 2) "fun x -> x + 2" candidate candidate_name) &&
    (test_sum_once r (fun x -> x * x) "fun x -> x * x" candidate candidate_name) &&
      (test_sum_once r (fun x -> 5) "fun x -> 5" candidate candidate_name) &&
        (test_sum_once r (fun x -> x * x * x + 3 * x * x) "fun x -> x * x * x + 3 * x * x" candidate candidate_name) &&
          (test_sum_once r (fun x -> x) "fun x -> x" candidate candidate_name);;

let sum_v1 f n_given =
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then f 0
    else let n' = n - 1
         in let ih = visit n'
            in ih + f n
  in visit n_given;;

let () = assert (test_sum 100 sum_v1 "sum_v1");;

(* We use nat_parafold_right because the inductive step requires the value to
   which the corresponding induction hypothesis applies i.e. require the index*)

let sum_v2 f =                       (* using nat_parafold_right *)
  nat_parafold_right (f 0) (fun n' ih -> f (succ n') + ih);;

let () = assert (test_sum 100 sum_v2 "sum_v2");;

let sumtorial_v3 =
  sum_v1 (fun x -> x);;

let () = assert (test_sumtorial 1000 "sumtorial_v3" sumtorial_v3);;

(* version 1 of test_sum_odd 
let test_sum_odd candidate =
  (* intuitive numbers: *)
  let b1 = (candidate 1 = 4)
  and b2 = (candidate 2 = 9)
  and b3 = (candidate 3 = 16)
  and b4 = (candidate 4 = 25)
  and b5 = (candidate 5 = 36)
  (* base case: *)
  and bc = (candidate 0 = 0)
  (* instance of the induction step: *)
  and is = (let k = Random.int 20 in
            candidate (k + 1) = (candidate k) + (2 * k + 1))
  (* using the property that the sum of the first n + 1 odd numbers is (n + 1)^2 *)
  and b6 = (let k = Random.int 20 in
            candidate k = (k + 1) * (k + 1))
  in b1 && b2 && b3 && b4 && b5 && bc && is && b6;;
 *)

let positive_random_test_sum_odd_once r name candidate =
  let sum_odd_witness_fun n_given = let () = assert (n_given >= 0) in
                                    (n_given + 1) * (n_given + 1) in
  positive_random_test_for_unary_function_taking_an_integer_once r name candidate sum_odd_witness_fun show_int;;

let positive_inductive_test_sum_odd_once r name candidate =
  let sum_odd_succ_case n' ih = ih + 2 * (n' + 1) + 1 in
  positive_inductive_test_for_unary_function_taking_an_integer_once r name candidate 1 sum_odd_succ_case show_int;;

let test_sum_odd r name candidate =
  repeat 1000 (positive_random_test_sum_odd_once r name) candidate && repeat 1000 (positive_inductive_test_sum_odd_once r name) candidate;;

let sum_odd_v1 n_given =
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then 1
    else let n' = n - 1
         in let ih = visit n'
            in ih + 2 * n + 1
  in visit n_given;;

let ()  = assert (test_sum_odd 1000 "sum_odd_v1" sum_odd_v1);;

let sum_odd_v2 =
  nat_parafold_right 1 (fun n' ih -> ih + 2 * (n' + 1) + 1);;

let ()  = assert (test_sum_odd 1000 "sum_odd_v2" sum_odd_v2);;

let sum_odd_v3 n_given =
  let () = assert (n_given >= 0) in
  (n_given + 1) * (n_given + 1);;

let () = assert (test_sum_odd 1000 "sum_odd_v3" sum_odd_v3);;

(* --------------------- *)

(* Exercise 6 *)

let nat_fold_right_v2 zero_case succ_case =
  let new_succ_case _ = succ_case in
  nat_parafold_right zero_case new_succ_case;;

(* verifying that nat_fold_right_v2 works as expected *)

let oddp_v2 = nat_fold_right_v2 false not;;
let () = assert (test_oddp 1000 "oddp_v2" oddp_v2);;

let power_v2 x y =
  let () = assert (y >= 0) in
  nat_fold_right_v2 1 (fun ih -> x * ih) y;;
let () = assert (test_power power_v2)

let fac_v2 n_given =
  let () = assert (n_given >= 0) in
  let (count, result) =
    let inductive_fun ih =
      let (x', x'_fac) = ih in
      let x = x' + 1 in
      (x, x * x'_fac) in
    nat_fold_right_v2 (0, 1) inductive_fun n_given in
  result;;
let () = assert (test_fac 100 "fac_v2" fac_v2);;

(* --------------------- *)

(* Exercise 7 *)

let nat_parafold_right_v2 zero_case succ_case n_given =
  let new_zero_case = (0, zero_case)
  and new_succ_case ih =
    let (x', x'_result) = ih in
    let x = x' + 1 in
    (x, succ_case x' x'_result) in
  let (count, result) = nat_fold_right new_zero_case new_succ_case n_given in
  result;;

(* verifying that nat_parafold_right_v2 works as expected *)

let sumtorial_v4 n_given =
  let () = assert (n_given >= 0) in
  nat_parafold_right_v2 0 (fun n' ih -> (succ n') + ih) n_given;;
let () = assert (test_sumtorial 1000 "sumtorial_v4" sumtorial_v4);;

let sum_v3 f n_given =
  let () = assert (n_given >= 0) in
  nat_parafold_right_v2 (f 0) (fun n' ih -> f (succ n') + ih) n_given;;
let () = assert (test_sum 100 sum_v3 "sum_v3");;

(* --------------------- *)

(* Exercise 8, done solely by Jerri *)

let rotate_right s g =
  let n = String.length s
  in let n' = n - g
     in String.mapi (fun i c ->
		     String.get s ((i + n') mod n))
		    s;;

let rotate_left s g =
  let n = String.length s
  in String.mapi (fun i c ->
		  String.get s ((i + g) mod n))
		 s;;

(* --------------------- *)

(* Exercise 9, also the work of Jerri *)

let rotate s g =
  let n = String.length s
  in let n' = (n - g) mod n
     in String.mapi (fun i c ->
		     String.get s ((i + n') mod n))
		    s;;

(* --------------------- *)

(* Exercise 10 *)

let test_preternp_ternp_postternp preternp ternp postternp =

  (* an instance of the base cases: *)
  let b0 = (if preternp 0
            then let () = Printf.printf "testing preternp failed for 0 with result true instead of false\n"
                 in false
            else true)
  and b1 = (if ternp 0
            then true
            else let () = Printf.printf "testing ternp failed for 0 with result false instead of true\n"
                 in false)
  and b2 = (if postternp 0
            then let () = Printf.printf "testing postternp failed for 0 with result true instead of false\n"
                 in false
            else true)

  (* an instance of the induction steps: *)
  and b3 = (let n' = Random.int 1000 in
            let preternp_of_succ_n' = preternp (succ n') and postternp_of_n' = postternp n' in
            if preternp_of_succ_n' = postternp_of_n'
            then true
            else let () = Printf.printf "testing induction step on %d failed with preternp of the successor of %d returning %b and postternp of %d returning %b\n" n' n' preternp_of_succ_n' n' postternp_of_n'
                 in false)
  and b4 = (let n' = Random.int 1000 in
            let ternp_of_succ_n' = ternp (succ n') and preternp_of_n' = preternp n' in
            if ternp_of_succ_n' = preternp_of_n'
            then true
            else let () = Printf.printf "testing induction step on %d failed with ternp of the successor of %d returning %b and pretternp of %d returning %b\n" n' n' ternp_of_succ_n' n' preternp_of_n'
                 in false)
  and b5 = (let n' = Random.int 1000 in
            let postternp_of_succ_n' = postternp (succ n') and ternp_of_n' = ternp n' in
            if postternp_of_succ_n' = ternp_of_n'
            then true
            else let () = Printf.printf "testing induction step on %d failed with postternp of the successor of %d returning %b and ternp of %d returning %b\n" n' n' postternp_of_succ_n' n' ternp_of_n'
                 in false)

  (* a sanity check, just in case *)
  and b6 = (let n = Random.int 1000
            in let a_ternary = 3 * n
               in let c1 = (if ternp a_ternary
                            then true
                            else let () = Printf.printf "testing ternp failed for %d with result false instead of true" a_ternary
                                 in false)
                  and c2 = (if not (preternp a_ternary)
                            then true
                            else let () = Printf.printf "testing prepreternp failed for %d with result true instead of false" a_ternary
                                 in false)
                  and c3 = (if not (postternp a_ternary)
                            then true
                            else let () = Printf.printf "testing postternp failed for %d with result true instead of false" a_ternary
                                 in false)
                  in c1 && c2 && c3)
  and b7 = (let n = Random.int 1000
            in let a_preternary = (3 * n) + 2
               in let c1 = (if not (ternp a_preternary)
                            then true
                            else let () = Printf.printf "testing ternp failed for %d with result true instead of false\n" a_preternary
                                 in false)
                  and c2 = (if preternp a_preternary
                            then true
                            else let () = Printf.printf "testing prepreternp failed for %d with result false instead of true\n" a_preternary
                                 in false)
                  and c3 = (if not (postternp a_preternary)
                            then true
                            else let () = Printf.printf "testing postternp failed for %d with result true instead of false\n" a_preternary
                                 in false)
                  in c1 && c2 && c3)
  and b8 = (let n = Random.int 1000
            in let a_postternary = (3 * n) + 1
               in let c1 = (if not (ternp a_postternary)
                            then true
                            else let () = Printf.printf "testing ternp failed for %d with result true instead of fals\n" a_postternary
                                 in false)
                  and c2 = (if not (preternp a_postternary)
                            then true
                            else let () = Printf.printf "testing prepreternp failed for %d with result true instead of false\n" a_postternary
                                 in false)
                  and c3 = (if postternp a_postternary
                            then true
                            else let () = Printf.printf "testing postternp failed for %d with result false instead of true\n" a_postternary
                                 in false)
                  in c1 && c2 && c3)
  in b0 && b1 && b2 && b3 && b4 && b5 && b6 && b7 && b8;;

(* implementing the predicates as single recursive functions *)

let preternp_v0 n_given =
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then false
    else let n' = n - 1
         in if n' = 0
            then false
            else let n'' = n' - 1
                 in if n'' = 0
                    then true
                    else let n''' = n'' - 1
                         in visit n'''
  in visit n_given;;

let rec ternp_v0 n_given =
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then true
    else let n' = n - 1
         in if n' = 0
            then false
            else let n'' = n' - 1
                 in if n'' = 0
                    then false
                    else let n''' = n'' - 1
                         in visit n'''
  in visit n_given;;

let rec postternp_v0 n_given =
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then false
    else let n' = n - 1
         in if n' = 0
            then true
            else let n'' = n' - 1
                 in if n'' = 0
                    then false
                    else let n''' = n'' - 1
                         in visit n'''
  in visit n_given;;

let () = assert (test_preternp_ternp_postternp preternp_v0 ternp_v0 postternp_v0);;

(* implementing the predicates as singly recursive functions using nat_fold_right *)

let nat_fold_right_for_ternary_predicates =
  nat_fold_right (false, true, false)
                 (fun ih -> let (preternp_n, ternp_n, postternp_n) = ih
                            in (postternp_n, preternp_n, ternp_n));;

let ternp_v1 n_given =
  let (preternp_n_given, ternp_n_given, postternp_n_given) =
    nat_fold_right_for_ternary_predicates n_given
  in ternp_n_given;;

let preternp_v1 n_given =
  let (preternp_n_given, ternp_n_given, postternp_n_given) =
    nat_fold_right_for_ternary_predicates n_given
  in preternp_n_given;;

let postternp_v1 n_given =
  let (preternp_n_given, ternp_n_given, postternp_n_given) =
    nat_fold_right_for_ternary_predicates n_given
  in postternp_n_given;;

let () = assert (test_preternp_ternp_postternp preternp_v1 ternp_v1 postternp_v1);;

(* implementing the predicates as mutually recursive functions *)

let rec ternp_mut_v0 n =
  if n = 0
  then true
  else let n' = n - 1
       in preternp_mut_v0 n'
and preternp_mut_v0 n =
  if n = 0
  then false
  else let n' = n - 1
       in postternp_mut_v0 n'
and postternp_mut_v0 n =
  if n = 0
  then false
  else let n' = n - 1
       in ternp_mut_v0 n';;

let () = assert (test_preternp_ternp_postternp preternp_mut_v0 ternp_mut_v0 postternp_mut_v0);;

(* traced version of mutually recursive function *)

let rec traced_ternp_mut_v0 n =
  let () = Printf.printf "ternp_v0 %d ->\n" n in
  if n = 0
  then true
  else let n' = n - 1
       in traced_preternp_mut_v0 n'
and traced_preternp_mut_v0 n =
  let () = Printf.printf "preternp_v0 %d ->\n" n in
  if n = 0
  then false
  else let n' = n - 1
       in traced_postternp_mut_v0 n'
and traced_postternp_mut_v0 n =
  let () = Printf.printf "postternp_v0 %d ->\n" n in
  if n = 0
  then false
  else let n' = n - 1
       in traced_ternp_mut_v0 n';;

(* example of trace using 10:

   # traced_ternp_mut_v0 10;;
   ternp_v0 10 ->
   preternp_v0 9 ->
   postternp_v0 8 ->
   ternp_v0 7 ->
   preternp_v0 6 ->
   postternp_v0 5 ->
   ternp_v0 4 ->
   preternp_v0 3 ->
   postternp_v0 2 ->
   ternp_v0 1 ->
   preternp_v0 0 ->
   - : bool = false
   # traced_preternp_mut_v0 10;;
   preternp_v0 10 ->
   postternp_v0 9 ->
   ternp_v0 8 ->
   preternp_v0 7 ->
   postternp_v0 6 ->
   ternp_v0 5 ->
   preternp_v0 4 ->
   postternp_v0 3 ->
   ternp_v0 2 ->
   preternp_v0 1 ->
   postternp_v0 0 ->
   - : bool = false
   # traced_postternp_mut_v0 10;;
   postternp_v0 10 ->
   ternp_v0 9 ->
   preternp_v0 8 ->
   postternp_v0 7 ->
   ternp_v0 6 ->
   preternp_v0 5 ->
   postternp_v0 4 ->
   ternp_v0 3 ->
   preternp_v0 2 ->
   postternp_v0 1 ->
   ternp_v0 0 ->
   - : bool = true

 *)

(* traced version of v2 *)

let traced_postternp_v2 n =
  let () = Printf.printf "postternp_v2 %d ->\n" n in
  let () = assert (0 <= n)
  in let result = traced_postternp_mut_v0 n
     in let () = Printf.printf "postternp_v4 %d <- %b\n" n result
	in result;;

let traced_ternp_v2 n =
  let () = Printf.printf "ternp_v2 %d ->\n" n in
  let () = assert (0 <= n)
  in let result = traced_ternp_mut_v0 n
     in let () = Printf.printf "ternp_v2 %d <- %b\n" n result
	in result;;

let traced_preternp_v2 n =
  let () = Printf.printf "preternp_v2 %d ->\n" n in
  let () = assert (0 <= n)
  in let result = traced_preternp_mut_v0 n
     in let () = Printf.printf "preternp_v2 %d <- %b\n" n result
	in result;;

(* example of trace using 5:

   # traced_postternp_v4 5;;
   postternp_v4t 5 ->
   postternp_v3 5 ->
   ternp_v3 4 ->
   preternp_v3 3 ->
   postternp_v3 2 ->
   ternp_v3 1 ->
   preternp_v3 0 ->
   postternp_v4t 5 <- false
   - : bool = false
   # traced_ternp_v4 5;;
   ternp_v4 5 ->
   ternp_v3 5 ->
   preternp_v3 4 ->
   postternp_v3 3 ->
   ternp_v3 2 ->
   preternp_v3 1 ->
   ternp_v4 5 <- false
   - : bool = false
   # traced_preternp_v4 5;;
   preternp_v4 5 ->
   preternp_v3 5 ->
   postternp_v3 4 ->
   ternp_v3 3 ->
   preternp_v3 2 ->
   preternp_v4 5 <- true
   - : bool = true

 *)

(* ********** *)

(* end of week-06.ml *)

let map_succ_0 ns_given =
  let rec visit ns =
    match ns with
    | [] ->
       []
    | n :: ns' ->
       succ n :: ns' (* visit is applied 0 times *)
  in visit ns_given;;

let map_succ_1 ns_given =
  let rec visit ns =
    match ns with
    | [] ->
       []
    | n :: ns' ->
       succ n :: visit ns' (* visit is applied 1 time *)
  in visit ns_given;;

let map_succ_2 ns_given =
  let rec visit ns =
    match ns with
    | [] ->
       []
    | n :: ns' ->
       succ n :: visit (visit ns') (* visit is applied 2 times *)
  in visit ns_given;;

let map_succ_3 ns_given =
  let rec visit ns =
    match ns with
    | [] ->
       []
    | n :: ns' ->
       succ n :: visit (visit (visit ns')) (* visit is applied 3 times *)
  in visit ns_given;;

let map_succ_4 ns_given =
  let rec visit ns =
    match ns with
    | [] ->
       []
    | n :: ns' ->
       succ n :: visit (visit (visit (visit ns'))) (* visit is applied 4 times *)
  in visit ns_given;;

let vigfus_list = [0; 0; 0; 0; 0];;

let test_map_succ_0 candidate =
  (* a specific test *)
  let b0 = (candidate vigfus_list = [1;0;0;0;0])
  (* a random test *)
  and b1 = (let length_ns' = Random.int 10
            in let ns' = List.init length_ns' (fun i -> 0)
               in candidate (0 :: ns') = succ 0 :: ns')
  (*base case*)
  and base_case = (candidate [] = [])
  in b0 && b1 && base_case;;

let test_map_succ_1 candidate =
  (* a specific test *)
  let b0 = (candidate vigfus_list = [1;1;1;1;1])
  (* a random test *)
  and b1 = (let length_ns = Random.int 10
            in let ns = List.init length_ns (fun i -> 0)
               in candidate ns = List.init length_ns (fun i -> 1))
  (*base case*)
  and base_case = (candidate [] = [])
  (* induction step *)
  and induction_step = (let length_ns' = Random.int 10
            in let ns' = List.init length_ns' (fun i -> 0)
               in candidate (0 :: ns') = succ 0 :: (candidate ns'))
  in b0 && b1 && base_case && induction_step;;

let test_map_succ_2 candidate =
  (* a specific test *)
  let b0 = (candidate vigfus_list = [1; 2; 4; 8; 16])
  (* a random test *)
  and b1 = (let length_ns = Random.int 10
            in let ns = List.init length_ns (fun i -> 0)
               in candidate ns = List.init length_ns (fun i -> power 2 i))
  (*base case*)
  and base_case = (candidate [] = [])
  (* induction step *)
  and induction_step = (let length_ns' = Random.int 10
            in let ns' = List.init length_ns' (fun i -> 0)
               in candidate (0 :: ns') = succ 0 :: (candidate (candidate ns')))
  in b0 && b1 && base_case && induction_step;;
