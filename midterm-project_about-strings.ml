(* midterm-project_about-strings.ml *)
(* Introduction to Computer Science (YSC1212), Sem2, 2020-2021 *)

(* ********** *)

(* Defining some commonly used functions *)

(* generator of random strings *)
let random_string n =
  let random_char () = char_of_int (Random.int (94 + int_of_char ' ')) in
  String.map (fun _ -> random_char ()) (String.make (Random.int n) ' ');;

(* function which repeatedly applies a test to a candidate function *)
let repeat n_given test candidate =
  let () = assert (n_given >= 0)in
  let rec visit n =
    if n = 0
    then true
    else test candidate && visit (n - 1)
  in visit n_given;;

(* nat_fold_right, as given in lecture notes *)
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

(* nat_parafold_right, as given in lecture notes *)
let nat_parafold_right zero_case succ_case n_given =
  (* nat_parafold_right : 'a -> (int -> 'a -> 'a) -> int -> 'a *)
  let () = assert (n_given >= 0) in
  let rec visit n =
    if n = 0
    then zero_case
    else let n' = n - 1
         in let ih = visit n'
            in succ_case n' ih
  in visit n_given;;

(* ********** *)

(* tracing functions *)

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

(* ********** *)

let an_int n =
  (* an_int : int -> int *)
  let () = Printf.printf "processing %s...\n" (show_int n)
  in n;;

let a_bool b =
  (* a_bool : bool -> bool *)
  let () = Printf.printf "processing %s...\n" (show_bool b)
  in b;;

let a_char c =
  (* a_char : char -> char *)
  let () = Printf.printf "processing %s...\n" (show_char c)
  in c;;

let a_string s =
  (* a_string : string -> string *)
  let () = Printf.printf "processing %s...\n" (show_string s)
  in s;;

let a_unit () =
  (* a_unit : unit -> unit *)
  let () = Printf.printf "processing the unit value...\n"
  in ();;

let a_function f =
  (* a_function : ('a -> 'b) -> 'a -> 'b *)
  let () = Printf.printf "processing a function...\n"
  in f;;

(* ********** *)

(* Question 1 *)

let test_string_append_once candidate =
  let s1 = random_string 20 and s2 = random_string 20
  in let expected_result = s1 ^ s2 and actual_result = candidate s1 s2
     in if actual_result = expected_result
        then true
        else let () = Printf.printf
                        "test_string_append_once failed for \"%s\" and \"%s\" with \"%s\" instead of \"%s\"\n" s1 s2 actual_result expected_result
             in false;;

let string_append s1 s2 =
  let s1_len = String.length s1 and s2_len = String.length s2
  in let total_len = s1_len + s2_len
     in let mapping_fun i = if i < s1_len then String.get s1 i
                            else String.get s2 (i - s1_len)
        in String.init total_len mapping_fun;;

let () = assert (repeat 100 test_string_append_once string_append);;

(* ********** *)

(* Question 2 *)

(* The following interactions illustrate that the characters in a given string are accessed from left to right when String.map is applied:

   # String.map (fun c -> let () = Printf.printf "processing %s...\n" (show_char c) in c) "0123";;
   processing '0'...
   processing '1'...
   processing '2'...
   processing '3'...
   - : string = "0123"
   # String.map (fun c -> let () = Printf.printf "processing %s...\n" (show_char c) in c) "abc";;
   processing 'a'...
   processing 'b'...
   processing 'c'...
   - : string = "abc"
   # String.map (fun c -> let () = Printf.printf "processing %s...\n" (show_char c) in c) "3210";;
   processing '3'...
   processing '2'...
   processing '1'...
   processing '0'...
   - : string = "3210"
   # String.map (fun c -> let () = Printf.printf "processing %s...\n" (show_char c) in c) "cba";;
   processing 'c'...
   processing 'b'...
   processing 'a'...
   - : string = "cba"
 *)

let test_string_map_once f fun_name candidate candidate_name =
  let s1 = random_string 20
  in let expected_result = String.map f s1 and actual_result = candidate f s1
     in if actual_result = expected_result
        then true
        else let () = Printf.printf
                        "testing %s with function %s failed for \"%s\" with \"%s\" instead of \"%s\"\n" candidate_name fun_name s1 actual_result expected_result
             in false;;

let test_string_map candidate candidate_name =
  test_string_map_once (fun c -> c) "fun c -> c" candidate candidate_name &&
    test_string_map_once (fun c -> 'a') "fun c -> c" candidate candidate_name &&
      test_string_map_once (fun c -> char_of_int (int_of_char c + 1)) "fun c -> char_of_int (int_of_char c + 1" candidate candidate_name;;

let string_map_left_to_right_v1 f s =
  let s_len = String.length s in
  let rec visit index =
    if index = 0
    then ""
    else let index' = index - 1
         in let ih = visit index'
            in ih ^ (String.make 1 (f (String.get s index')))
  in visit s_len;;

let () = assert (test_string_map string_map_left_to_right_v1 "string_map_left_to_right_v1");;

let string_map_left_to_right_v2 f s =             (* using nat_parafold_right *)
  let succ_case index' ih = ih ^ (String.make 1 (f (String.get s index')))
  and s_len = String.length s
  in nat_parafold_right "" succ_case s_len;;

let () = assert (test_string_map string_map_left_to_right_v2 "string_map_left_to_right_v2");;

(* checking order in which string_map_left_to_right_v2 applies input function to characters in the input string:
   #  string_map_left_to_right_v2 (fun c -> a_char c) "abcde";;
   processing 'a'...
   processing 'b'...
   processing 'c'...
   processing 'd'...
   processing 'e'...
   - : string = "abcde"
 *)

let string_map_right_to_left_v1 f s =
  let s_len = String.length s
  in let last_index = s_len - 1
     in let rec visit index =
	  if index = 0
	  then ""
	  else let index' = index - 1
	       in let ih = visit index'
		  in (String.make 1 (f (String.get s (last_index - index')))) ^ ih
	in visit s_len;;

let () = assert (test_string_map string_map_right_to_left_v1 "string_map_right_to_left_v1");;

let string_map_right_to_left_v2 f s =             (* using nat_parafold_right *)
  let s_len = String.length s
  in let last_index = s_len - 1
     in let succ_case index' ih = String.make 1 (f (String.get s (last_index - index'))) ^ ih
	in nat_parafold_right "" succ_case s_len;;

let () = assert (test_string_map string_map_right_to_left_v2 "string_map_right_to_left_v2");;

(* checking order in which string_map_right_to_left_v2 applies input function to characters in the input string:
   # string_map_right_to_left_v2 (fun c -> a_char c) "abcde";;
   processing 'e'...
   processing 'd'...
   processing 'c'...
   processing 'b'...
   processing 'a'...
   - : string = "abcde"
 *)

(* ********** *)

(* Question 3 (optional) *)

(* The following interactions illustrate that the characters in a given string are accessed from left to right when String.mapi is applied:

   # String.mapi (fun i c -> let () = Printf.printf "processing %s...\n" (show_char c) in c) "0123";;
   processing '0'...
   processing '1'...
   processing '2'...
   processing '3'...
   - : string = "0123"
   # String.mapi (fun i c -> let () = Printf.printf "processing %s...\n" (show_char c) in c) "3210";;
   processing '3'...
   processing '2'...
   processing '1'...
   processing '0'...
   - : string = "3210"
   # String.mapi (fun i c -> let () = Printf.printf "processing %s...\n" (show_char c) in c) "abcd";;
   processing 'a'...
   processing 'b'...
   processing 'c'...
   processing 'd'...
   - : string = "abcd"
   # String.mapi (fun i c -> let () = Printf.printf "processing %s...\n" (show_char c) in c) "dcba";;
   processing 'd'...
   processing 'c'...
   processing 'b'...
   processing 'a'...
   - : string = "dcba"
 *)

let test_string_mapi_once f fun_name candidate candidate_name =
  let s1 = random_string 20
  in let expected_result = String.mapi f s1 and actual_result = candidate f s1
     in if actual_result = expected_result
        then true
        else let () = Printf.printf
                        "testing %s with function %s failed for \"%s\" with \"%s\" instead of \"%s\"\n" candidate_name fun_name s1 actual_result expected_result
             in false;;

let test_string_mapi candidate candidate_name =
  (test_string_mapi_once (fun i c -> c) "fun i c -> c" candidate candidate_name) &&
    (test_string_mapi_once (fun i c -> char_of_int i) "fun i c -> char_of_int i" candidate candidate_name) &&
      (test_string_mapi_once (fun i c -> char_of_int (int_of_char c + i)) "fun c -> char_of_int (int_of_char c + i" candidate candidate_name);;

let string_mapi_left_to_right_v1 f s =
  let s_len = String.length s in
  let rec visit index =
    if index = 0
    then ""
    else let index' = index - 1
         in let ih = visit index'
            in ih ^ (String.make 1 (f index' (String.get s index')))
  in visit s_len;;

let () = assert (test_string_mapi string_mapi_left_to_right_v1 "string_mapi_left_to_right_v1");;

let string_mapi_left_to_right_v2 f s =                                 (* using nat_parafold_right *)
  let base_case = ""
  and succ_case index' ih = ih ^ (String.make 1 (f index' (String.get s index')))
  and s_len = String.length s
  in nat_parafold_right base_case succ_case s_len;;

let () = assert (test_string_mapi string_mapi_left_to_right_v2 "string_mapi_left_to_right_v2");;

(* checking order in which string_map_right_to_left_v2 applies input function to characters in the input string:
   # string_mapi_left_to_right_v2 (fun i c -> a_char c) "abcde";;
   processing 'a'...
   processing 'b'...
   processing 'c'...
   processing 'd'...
   processing 'e'...
   - : string = "abcde"
# 
 *)
let string_mapi_right_to_left_v1 f s =
  let s_len = String.length s
  in let last_index = s_len - 1
     in let rec visit index =
	  if index = 0
	  then ""
	  else let index' = index - 1
	       in let ih = visit index'
		  in (String.make 1 (f (last_index - index') (String.get s (last_index - index')))) ^ ih
	in visit s_len;;

let () = assert (test_string_mapi string_mapi_right_to_left_v1 "string_mapi_right_to_left_v1");;


let string_mapi_right_to_left_v2 f s =             (* using nat_parafold_right *)
  let s_len = String.length s
  in let last_index = s_len - 1
     in let succ_case index' ih = String.make 1 (f (last_index - index') (String.get s (last_index - index'))) ^ ih
	in nat_parafold_right "" succ_case s_len;;

let () = assert (test_string_mapi string_mapi_right_to_left_v2 "string_mapi_right_to_left_v2");;

(* checking order in which string_map_right_to_left_v2 applies input function to characters in the input string:
   # string_mapi_right_to_left_v2 (fun i c -> a_char c) "abcde";;
   processing 'e'...
   processing 'd'...
   processing 'c'...
   processing 'b'...
   processing 'a'...
   - : string = "abcde"
 *)

(* ********** *)

(* switched order of questions 4 and 5 so a complete unit test could be written before implementing the function *)

(* Question 5 *)

(* unit test for string reverse function, not needed for Question 5 but added here so that it can be coupled with the unit test for the string reverse relationship to make a complete unit test to be used in Question 4 *)

let test_string_reverse_once candidate =
  let s1 = random_string 20
  in let expected_result = String.mapi (fun i c -> String.get s1 ((String.length s1 - 1) - i)) s1
     and actual_result = candidate s1
     in if actual_result = expected_result
        then true
        else let () = Printf.printf
                        "test_string_reverse_once failed for \"%s\" with \"%s\" instead of \"%s\"\n" s1  actual_result expected_result
             in false;;

(* unit test for the string reverse relationship, the actual answer to Question 5 *)

let unit_test_string_reverse_for_question_5_once candidate =
  let s1 = random_string 20 and s2 = random_string 20
  in let concat_then_reverse = candidate (s1 ^ s2)
     and reverse_then_concat = (candidate s2) ^ (candidate s1)
     in if concat_then_reverse = reverse_then_concat
        then true
        else let () = Printf.printf
                        "test_string_reverse_relation_once failed for \"%s\" and \"%s\" with concatenating then reversing returning \"%s\" and reversing then concatenating returning \"%s\"\n" s1 s2 concat_then_reverse reverse_then_concat
             in false;;

(* unit test that combines the above two tests, resulting in a complete test for the string reverse function *)

let test_string_reverse candidate =
  repeat 100 test_string_reverse_once candidate && repeat 100 unit_test_string_reverse_for_question_5_once candidate;;

(* ********** *)

(* Question 4 *)

let string_reverse_mapi s =
  let final_index = String.length s - 1 in
  String.mapi (fun i c -> String.get s (final_index - i)) s;;

let () = assert (test_string_reverse string_reverse_mapi);;

let string_reverse_rec_v0 s =
  let s_len = String.length s in
  let rec visit index =
    if index = 0
    then ""
    else let index' = index - 1
         in let ih = visit index'
            in (String.make 1 (String.get s index')) ^ ih
  in visit s_len;;

let () = assert (test_string_reverse string_reverse_rec_v0);;

let string_reverse_rec_v1 s =
  let s_len = String.length s in
  nat_parafold_right "" (fun index' ih -> (String.make 1 (String.get s index')) ^ ih) s_len;;

let () = assert (test_string_reverse string_reverse_rec_v1);;

(* ********** *)

(* Question 6 *)

(* creates a palindrome with fixed characters: 'a', then 'b' and so on.. *)

let make_palindrome_v0 n =
  let s = String.mapi (fun i c -> char_of_int(int_of_char(c) + i)) (String.make (n/2) 'a')
  in let final_string =
       if n mod 2 = 1
       then s ^ String.make 1 (char_of_int(int_of_char('a') + (n/2))) ^ string_reverse_rec_v0 s
       else s ^ string_reverse_rec_v0 s
     in final_string;;

let make_palindrome_v1 n =             (* eliminates if-then-else expression *)
  let s = String.mapi (fun i c -> char_of_int(int_of_char(c) + i)) (String.make (n/2) 'a')
  in s ^ String.make (n mod 2) (char_of_int(int_of_char('a') + (n/2))) ^ string_reverse_rec_v0 s;;

(* examples:
   # make_palindrome_v1 0;;
   - : string = ""
   # make_palindrome_v1 1;;
   - : string = "a"
   # make_palindrome_v1 6;;
   - : string = "abccba"
   # make_palindrome_v1 7;;
   - : string = "abcdcba"
 *)

(* creates a palindrome with random lower case letters *)

let make_palindrome_v2 n =
  let random_lower_letter_char () = char_of_int (Random.int 26 + int_of_char 'a') in
  let random_lower_letter_string n = String.map (fun _ -> random_lower_letter_char ()) (String.make n ' ') in
  let half_string = random_lower_letter_string (n / 2)
  in let other_half_string = string_reverse_mapi half_string
     in if n mod 2 = 0
        then half_string ^ other_half_string
        else half_string ^ random_lower_letter_string 1 ^ other_half_string;;

let make_palindrome_v3 n =          (* eliminates if-then-else statement *)
  let random_lower_letter_char () = char_of_int (Random.int 26 + int_of_char 'a') in
  let random_lower_letter_string n = String.map (fun _ -> random_lower_letter_char ()) (String.make n ' ') in
  let half_string = random_lower_letter_string (n / 2)
  in let other_half_string = string_reverse_mapi half_string
     in half_string ^ random_lower_letter_string (n mod 2) ^ other_half_string;;

(* examples:
   # make_palindrome_v3 0;;
   - : string = ""
   # make_palindrome_v3 1;;
   - : string = "w"
   # make_palindrome_v3 4;;
   - : string = "icci"
   # make_palindrome_v3 5;;
   - : string = "wzzzw"
 *)

(* creates a palindrome without generating a throwaway string *)

let make_palindrome_v4 n =
  let abs_x_minus_n x n = (if x - n >= 0
                           then x - n
                           else - (x - n)) in
  let char_of_index i = char_of_int ((abs_x_minus_n (2 * i + 1) n) + int_of_char 'a')
  in String.init n (fun i -> char_of_index i);;

(* examples:
   # make_palindrome_v4 0;;
   - : string = ""
   # make_palindrome_v4 1;;
   - : string = "a"
   # make_palindrome_v4 10;;
   - : string = "jhfdbbdfhj"
   # make_palindrome_v4 11;;
   - : string = "kigecacegik"
 *)

(* recursive implementation *)

let make_palindrome_v5 n_given =
  let random_lower_letter_char () = char_of_int (Random.int 26 + int_of_char 'a') in
  let random_lower_letter_string n = String.map (fun _ -> random_lower_letter_char ()) (String.make n ' ') in
  let zero_case = (random_lower_letter_string (n_given mod 2))
  and succ_case = (fun ih -> let random_letter = (random_lower_letter_string 1) in
                             random_letter ^ ih ^ random_letter)
  in nat_fold_right zero_case succ_case (n_given / 2);;

(*
   # make_palindrome_v5 0;;
   - : string = ""
   # make_palindrome_v5 1;;
   - : string = "y"
   # make_palindrome_v5 2;;
   - : string = "jj"
   # make_palindrome_v5 13;;
   - : string = "xgghgyryghggx"
 *)

(* ********** *)

(* Question 7 *)

let positive_test_palindromep_once candidate =
  let random_palindrome = make_palindrome_v2 (Random.int 20) in
  if candidate random_palindrome
  then true
  else let () = Printf.printf "testing with %s failed with result false instead of true\n" random_palindrome
       in false;;

let negative_test_palindromep candidate =
  let negative_test_palindomep_once not_palindrome = 
    if candidate not_palindrome
    then let () = Printf.printf "testing with %s failed with result true instead of false\n" not_palindrome
         in false
    else true
  in let not_palindrome_1 = "ab" and not_palindrome_2 = "123" and not_palindrome_3 = "xyzxy" and not_palindrome_4 = "!!!456" and not_palindrome_5 = "abcdeefdca" and not_palindrome_6 = "*&*&*&"
     in negative_test_palindomep_once not_palindrome_1 && negative_test_palindomep_once not_palindrome_2 && negative_test_palindomep_once not_palindrome_3 && negative_test_palindomep_once not_palindrome_4 && negative_test_palindomep_once not_palindrome_5 && negative_test_palindomep_once not_palindrome_6;;

let test_palindromep candidate =
  repeat 100 positive_test_palindromep_once candidate && negative_test_palindromep candidate;;

(* reverses input string using String.mapi to create a new string, checks that the two strings are the same *)
let palindromep_mapi s =
  s = string_reverse_mapi s;;

let () = assert (test_palindromep palindromep_mapi);;

(* reverses input string using recursive implementation to create a new string, checks that the two strings are the same *)
let palindromep_rec_v0 s =
  s = string_reverse_rec_v0 s;;

let () = assert (test_palindromep palindromep_rec_v0);;

(* checks that middle characters are the same, moving outwards, until the first character of the string *)
let palindromep_rec_outward_v0 s =
  let s_len = String.length s in
  let final_index = s_len - 1
  and mid_index = s_len / 2 in
  let rec visit index =
    if index = 0
    then true
    else let index' = index - 1 in
         let ih = visit index' in
         if ih
         then String.get s (mid_index - succ (index')) = String.get s (final_index - (mid_index - succ( index')))
         else false
  in visit mid_index;;

let () = assert (test_palindromep palindromep_rec_outward_v0);;

let palindromep_rec_outward_v1 s =           (* using nat_parafold_right *)
  let s_len = String.length s in
  let final_index = s_len - 1
  and mid_index = s_len / 2 in
  let succ_case index' ih = if ih
			    then String.get s (mid_index - succ (index')) = String.get s (final_index - (mid_index - succ( index')))
			    else false
  in nat_parafold_right true succ_case mid_index;;

let () = assert (test_palindromep palindromep_rec_outward_v1);;

(* checks that first character is the same as the last, moving inward, until the middle of the string *)
let palindromep_rec_inward_v0 s =
  let s_len = String.length s in
  let final_index = s_len - 1 in
  let rec visit index =
    if index = 0
    then true
    else let index' = index - 1 in
         let ih = visit index' in
         if ih
         then String.get s index' = String.get s (final_index - index')
         else false
  in visit (s_len / 2);;

let () = assert (test_palindromep palindromep_rec_inward_v0);;

let palindromep_rec_inward_v1 s =           (* using nat_parafold_right *)
  let s_len = String.length s in
 let final_index = s_len - 1 in
  let succ_case index' ih = if ih
			    then String.get s index' = String.get s (final_index - index')
			    else false
  in nat_parafold_right true succ_case (s_len / 2);;

let () = assert (test_palindromep palindromep_rec_inward_v1);;

(* ********** *)

(* Question 8 (not optional) *)

let reverse_palindrome s =
  let () = assert (palindromep_mapi s) in
  s;;

(* ********** *)

(* Question 9 (optional) *)

let test_warmup candidate =
  (candidate 'a' 'b' 'c' = "abc");;

let warmup char1 char2 char3 =
  String.make 1 char1 ^ String.make 1 char2 ^ String.make 1 char3;;

let () = assert (test_warmup warmup);;

(* ********** *)

(* Question 10 (optional) *)

let string_map_using_mapi f s =
  String.mapi (fun _ c -> f c) s;;

let () = assert (test_string_map string_map_using_mapi "string_map_using_mapi");;

(* ********** *)

(* Question 11 (optional) *)

let string_mapi_using_init f s =
  let s_len = String.length s
  in String.init s_len (fun i -> f i (String.get s i));;

let () = assert (test_string_mapi string_mapi_using_init "string_mapi_using_init");;

(* ********** *)

(* end of midterm-project_about-strings.ml *)

let end_of_file = "midterm-project_about-strings.ml";;
