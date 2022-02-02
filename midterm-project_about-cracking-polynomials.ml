(* midterm-project_about-cracking-polynomials.ml *)
(* Introduction to Computer Science (YSC1212), Sem2, 2020-2021 *)

(* ********** *)

let commiseration = [|"Bummer:";
                      "Bad luck:";
                      "More bad luck:";
                      "Trouble ahead:";
                      "Commiseration city, that's what it is:";
                      "Yes, it's hard to believe, but";
                      "There we go again:";
                      "Truth be told,";
                      "Now that's bizarre:";
                      "Once again,";
                      "Well,";
                      "Unfortunately,";
                      "Argh:";
                      "The proof is not trivial:";
                      "Something is amiss:";
                      "Surprise:";
                      "You need a break:";
                      "I don't want to alarm you, but";
                      "You probably would prefer to receive a random love letter, but";
                      "This is not a pipe dream:";
                     |];;

let random_int () =
  if Random.bool ()
  then Random.int 1000
  else -(Random.int 1000);;

(* function which repeatedly applies a test to a candidate function *)
let repeat n_given test candidate =
  let () = assert (n_given >= 0)in
  let rec visit n =
    if n = 0
    then true
    else test candidate && visit (n - 1)
  in visit n_given;;

(* ********** *)

(* First degree polynomial *)

let make_polynomial_1 a1 a0 x =
  a1 * x + a0;;

let test_crack_1_once candidate =
  let a1 = random_int ()
  and a0 = random_int ()
  in let p1 = make_polynomial_1 a1 a0
     in let expected_result = (a1, a0)
        and ((a1', a0') as actual_result) = candidate p1
        in if actual_result = expected_result
           then true
           else let () = Printf.printf
                           "%s\ntest_crack_1_once failed for %i * x^1 + %i\nwith %i instead of %i and %i instead of %i\n"
                           (Array.get commiseration (Random.int (Array.length commiseration)))
                           a1 a0 a1' a1 a0' a0
                in false;;

let test_crack_1 candidate =
  repeat 100 test_crack_1_once candidate;;

let crack_1 p1 =
  let a1 = p1 1 - p1 0
  and a0 = p1 0
  in (a1, a0);;

let () = assert (test_crack_1 crack_1);;

(* ********** *)
(* Second degree polynomial *)

let make_polynomial_2 a2 a1 a0 x =
  a2 * x * x + a1 * x + a0;;

let test_crack_2_once candidate =
  let a2 = random_int ()
  and a1 = random_int ()
  and a0 = random_int ()
  in let p2 = make_polynomial_2 a2 a1 a0
     in let expected_result = (a2, a1, a0)
        and ((a2', a1', a0') as actual_result) = candidate p2
        in if actual_result = expected_result
           then true
           else let () = Printf.printf
                           "%s\ntest_crack_2_once failed for %i * x^2 + %i * x^1 + %i\nwith %i instead of %i, %i instead of %i, and %i instead of %i\n"
                           (Array.get commiseration (Random.int (Array.length commiseration)))
                           a2 a1 a0 a2' a2 a1' a1 a0' a0
                in false;;

let test_crack_2 candidate =
  repeat 100 test_crack_2_once candidate;;

let crack_2_v1 p2 =
  let a2 = (p2 3 - (2 * p2 2) + p2 1)/2
  in let a1 = p2 2 - p2 1 - (3 * a2)
     and a0 = p2 0
     in (a2, a1, a0);;

let () = assert (test_crack_2 crack_2_v1);;

(* using crack_2 to implement crack_1 *)

let crack_1_v2 p2 =
  let (_, a1, a0) = crack_2_v1 p2 in
  (a1, a0);;

let () = assert (test_crack_1 crack_1_v2);;  

(* ********** *)

(* Zero degree polynomials *)

let make_polynomial_0 a0 x =
  a0;;

let test_crack_0_once candidate =
  let a0 = random_int ()
  in let p0 = make_polynomial_0 a0
     in let expected_result = a0
        and (a0' as actual_result) = candidate p0
        in if actual_result = expected_result
           then true
           else let () = Printf.printf
                           "%s\ntest_crack_0_once failed for %i\nwith %i instead of %i\n"
                           (Array.get commiseration (Random.int (Array.length commiseration)))
                           a0 a0' a0'
                in false;;

let test_crack_0 candidate =
  repeat 100 test_crack_0_once candidate;;

let crack_0_v1 p0 =
  p0 0;;

let () = assert (test_crack_0 crack_0_v1);;

let crack_0_v2 p0 =
  p0 (random_int ());;

let () = assert (test_crack_0 crack_0_v2);;

let crack_0_v3 p0 =
  let (_, a0) = crack_1_v2 p0 in
  a0;;

let () = assert (test_crack_0 crack_0_v3);;

let crack_0_v4 p0 =
  let (_, _, a0) = crack_2_v1 p0 in
  a0;;

let () = assert (test_crack_0 crack_0_v4);;

(* ********** *)

(* Third degree polynomials *)

let make_polynomial_3 a3 a2 a1 a0 x =
  a3 * x * x * x + a2 * x * x + a1 * x + a0;;

let test_crack_3_once candidate =
  let a3 = random_int ()
  and a2 = random_int ()
  and a1 = random_int ()
  and a0 = random_int ()
  in let p3 = make_polynomial_3 a3 a2 a1 a0
     in let expected_result = (a3, a2, a1, a0)
        and ((a3', a2', a1', a0') as actual_result) = candidate p3
        in if actual_result = expected_result
           then true
           else let () = Printf.printf
                           "%s\ntest_crack_3_once failed for %i * x^3 + %i * x^2 + %i * x^1 + %i\nwith %i instead of %i, %i instead of %i, %i instead of %i, and %i instead of %i\n"
                           (Array.get commiseration (Random.int (Array.length commiseration)))
                           a3 a2 a1 a0 a3' a3 a2' a2 a1' a1 a0' a0
                in false;;

let test_crack_3 candidate =
  test_crack_3_once candidate && test_crack_3_once candidate && test_crack_3_once candidate;;

let crack_3 p3 =
  let a3 = ((p3 3) - (3 * p3 2) + (3 * p3 1) - p3 0)/6
  in let a2 = (p3 3 - (2 * p3 2) + (p3 1) - (12 * a3))/2
     in let a1 = p3 1 - p3 0 - a3 - a2
	and a0 = p3 0
	in (a3, a2, a1, a0);;

let () = assert (test_crack_3 crack_3);;

(* using crack_3 to implement crack_0, crack_1 and crack_2 *)

let crack_0_v5 p0 =
  let (_, _, _, a0) = crack_3 p0 in
  a0;;

let () = assert (test_crack_0 crack_0_v5);;

let crack_1_v3 p1 =
  let (_, _, a1, a0) = crack_3 p1 in
  (a1, a0);;

let () = assert (test_crack_1 crack_1_v3);;

let crack_2_v2 p2 =
  let (_, a2, a1, a0) = crack_3 p2 in
  (a2, a1, a0);;

let () = assert (test_crack_2 crack_2_v2);;

(* ********** *)

(* Fourth degree polynomials *)

let make_polynomial_4 a4 a3 a2 a1 a0 x =
  a4 * x * x * x *x + a3 * x * x * x + a2 * x * x + a1 * x + a0;;

let test_crack_4_once candidate =
  let a4 = random_int ()
  and a3 = random_int ()
  and a2 = random_int ()
  and a1 = random_int ()
  and a0 = random_int ()
  in let p4 = make_polynomial_4 a4 a3 a2 a1 a0
     in let expected_result = (a4, a3, a2, a1, a0)
        and ((a4', a3', a2', a1', a0') as actual_result) = candidate p4
        in if actual_result = expected_result
           then true
           else let () = Printf.printf
                           "%s\ntest_crack_4_once failed for %i * x^4 + %i * x^3 + %i * x^2 + %i * x^1 + %i\nwith %i instead of %i, %i instead of %i, %i instead of %i, %i instead of %i, and %i instead of %i\n"
                           (Array.get commiseration (Random.int (Array.length commiseration)))
                           a4 a3 a2 a1 a0 a4' a4 a3' a3 a2' a2 a1' a1 a0' a0
                in false;;

let test_crack_4 candidate =
  repeat 100 test_crack_4_once candidate;;

let crack_4 p4 =
  let a4 = (p4 4 - (4 * p4 3) + (6 * p4 2) - (4 * p4 1) + p4 0)/24
  in let a3 = (p4 4 - (3 * p4 3) + (3 * p4 2) - p4 1 - (60 * a4))/6
     in let a2 = (p4 2 - (2 * p4 1) + p4 0 - (14 * a4) - (6 * a3))/2
	in let a1 = p4 1 - p4 0 - a4 - a3 - a2
	   in let a0 = p4 0
	      in (a4, a3, a2, a1, a0);;

let () = assert (test_crack_4 crack_4);;

(* using crack_4 to implement crack_0, crack_1, crack_2 and crack_3 *)

let crack_0_v6 p0 =
  let (_, _, _, _, a0) = crack_4 p0 in
  a0;;

let () = assert (test_crack_0 crack_0_v6);;

let crack_1_v4 p1 =
  let (_, _, _, a1, a0) = crack_4 p1 in
  (a1, a0);;

let () = assert (test_crack_1 crack_1_v4);;

let crack_2_v3 p2 =
  let (_, _, a2, a1, a0) = crack_4 p2 in
  (a2, a1, a0);;

let () = assert (test_crack_2 crack_2_v3);;

let crack_3_v2 p3 =
  let (_, a3, a2, a1, a0) = crack_4 p3 in
  (a3, a2, a1, a0);;

let () = assert (test_crack_3 crack_3_v2);;

(* ********** *)

(* end of midterm-project_about-cracking-polynomials.ml *)

let end_of_file = "midterm-project_about-cracking-polynomials.ml";;
