(* Pomožni tip, ki predstavlja mrežo *)

type 'a grid = 'a Array.t Array.t

(* Funkcije za prikaz mreže.
   Te definiramo najprej, da si lahko z njimi pomagamo pri iskanju napak. *)

(* Razbije seznam [lst] v seznam seznamov dolžine [size]. Če size ne deli dolžine [lst]
bo razdelil [lst] na floor([length]/[size]) seznamov dolžine [size] in en seznam, dolžine,
ki je enaka ostanku pri deljenju [length] s [size], kjer je length dolžina seznama [lst] *)
let chunkify size lst =
  let rec aux chunk chunks n lst =
    match (n, lst) with
    | _, [] when chunk = [] -> List.rev chunks
    | _, [] -> List.rev (List.rev chunk :: chunks)
    | 0, _ :: _ -> aux [] (List.rev chunk :: chunks) size lst
    | _, x :: xs -> aux (x :: chunk) chunks (n - 1) xs
  in
  aux [] [] size lst

(* Vsak element v seznamu [lst] pretvorimo v niz s funkcijo [string_of_element] in nato vse
pretvorjene elemente združimo v niz v enakem zaporedju, kot nastopajo v [lst], vsi znaki v
nizu pa so ločeni z nizom [sep] *)
let string_of_list string_of_element sep lst =
  lst |> List.map string_of_element |> String.concat sep

(* Funkciji [string_of_element] priredimo funkcijo [string_of_nested_list], ki sprejme gnezden seznam
[lst], vsak podseznam preslika v niz s [string_of_list string_of_element inner_sep] in na koncu slike 
vseh podseznamov združi v en niz, v katerem so slike nizov ločene z nizom [outer_sep], nastopajo pa v
enakem zaporedju kot nastopajo originalni podseznami v [lst] *)
let string_of_nested_list string_of_element inner_sep outer_sep =
  string_of_list (string_of_list string_of_element inner_sep) outer_sep

(* Tabelo s podatki za posamezno vrstico pretvorimo v niz, primeren za izpis v sudokuju *)
let string_of_row string_of_cell row =
  let string_of_cells =
    row |> Array.to_list |> chunkify 3
    |> string_of_nested_list string_of_cell "" "│"
  in
  "┃" ^ string_of_cells ^ "┃\n"

(* Tabelo s tabelami vrstic pretvorimo v niz, primeren za izpis, in ta niz izpišemo. *)
let print_grid string_of_cell grid =
  let ln = "───" in
  let big = "━━━" in
  let divider = "┠" ^ ln ^ "┼" ^ ln ^ "┼" ^ ln ^ "┨\n" in
  let row_blocks =
    grid |> Array.to_list |> chunkify 3
    |> string_of_nested_list (string_of_row string_of_cell) "" divider
  in
  Printf.printf "┏%s┯%s┯%s┓\n" big big big;
  Printf.printf "%s" row_blocks;
  Printf.printf "┗%s┷%s┷%s┛\n" big big big

(* Funkcije za dostopanje do elementov mreže *)

let get_row (grid : 'a grid) (row_ind : int) = grid.(row_ind)

let rows grid = List.init 9 (get_row grid)

let get_column (grid : 'a grid) (col_ind : int) =
  Array.init 9 (fun row_ind -> grid.(row_ind).(col_ind))

let columns grid = List.init 9 (get_column grid)

let get_box (grid : 'a grid) (box_ind : int) = 
  Array.init 3 (fun row_ind -> 
        Array.init 3 (fun col_ind -> grid.(row_ind + (box_ind/3) * 3).(col_ind + (box_ind mod 3) * 3)))

let boxes grid = List.init 9 (get_box grid)

(* Funkcije za ustvarjanje novih mrež *)

let map_grid (f : 'a -> 'b) (grid : 'a grid) : 'b grid = 
  Array.init 9 (fun i -> Array.map f (get_row grid i))

let copy_grid (grid : 'a grid) : 'a grid = map_grid (fun x -> x) grid

let foldi_grid (f : int -> int -> 'a -> 'acc -> 'acc) (grid : 'a grid)
    (acc : 'acc) : 'acc =
  let acc, _ =
    Array.fold_left
      (fun (acc, row_ind) row ->
        let acc, _ =
          Array.fold_left
            (fun (acc, col_ind) cell ->
              (f row_ind col_ind cell acc, col_ind + 1))
            (acc, 0) row
        in
        (acc, row_ind + 1))
      (acc, 0) grid
  in
  acc

let row_of_string cell_of_char str =
  List.init (String.length str) (String.get str) |> List.filter_map cell_of_char

let grid_of_string cell_of_char str =
  let grid =
    str |> String.split_on_char '\n'
    |> List.map (row_of_string cell_of_char)
    |> List.filter (function [] -> false | _ -> true)
    |> List.map Array.of_list |> Array.of_list
  in
  if Array.length grid <> 9 then failwith "Nepravilno število vrstic";
  if Array.exists (fun x -> x <> 9) (Array.map Array.length grid) then
    failwith "Nepravilno število stolpcev";
  grid

(* Model za vhodne probleme *)

type problem = { initial_grid : int option grid }

let print_problem problem : unit = print_grid string_of_int problem

let problem_of_string str =
  let cell_of_char = function
    | ' ' -> Some None
    | c when '1' <= c && c <= '9' -> Some (Some (Char.code c - Char.code '0'))
    | _ -> None
  in
  { initial_grid = grid_of_string cell_of_char str }

(* Model za izhodne rešitve *)

type solution = int grid

let print_solution solution = print_grid string_of_int solution

let is_valid_solution problem solution = 
  (* Preveri, ali so v vsaki vrstici vse številke *)
  let rows_correct solution = List.for_all (fun row -> Array.for_all (fun ind -> 
          Array.exists (fun x -> x = ind) row) (Array.init 9 (fun i -> i))) (rows solution) in
  (* Preveri, ali so v vsakem stolpcu vse številke *)
  let columns_correct solution = List.for_all (fun column -> Array.for_all (fun ind -> 
          Array.exists (fun x -> x = ind) column) (Array.init 9 (fun i -> i))) (columns solution) in
  (* Preveri, ali so v vsaki škatli vse številke *)  
  let boxes_correct solution = List.for_all (fun box -> Array.for_all (fun ind -> 
          Array.exists (fun lst -> 
          Array.exists (fun x -> x = ind) lst) box) (Array.init 9 (fun i -> i))) (boxes solution) in
  (* Preveri, ali sta problem in rešitev skladni. *)
  let sol_prob_same solution problem = Array.exists (fun i ->
                                      Array.exists (fun j -> (match problem.(i).(j) with
                                        | None -> false
                                        | Some x -> solution.(i).(j) != x
                                      )) (Array.init 9 (fun j -> j))) (Array.init 9 (fun i -> i)) in
  
  (rows_correct solution) && (columns_correct solution) && (boxes_correct solution) && (not (sol_prob_same solution problem))


(*┏━━━┯━━━┯━━━┓
┃483│921│657┃
┃967│3 5│821┃
┃251│876│493┃
┠───┼───┼───┨
┃548│132│976┃
┃729│ 64│ 38┃
┃136│798│ 45┃
┠───┼───┼───┨
┃372│689│514┃
┃814│253│769┃
┃695│417│382┃
┗━━━┷━━━┷━━━┛*)

  (*[|[|Some 4; Some 8; Some 3; Some 9; Some 2; Some 1; Some 6; Some 5;
      Some 7|];
    [|Some 9; Some 6; Some 7; Some 3; None; Some 5; Some 8; Some 2; Some 1|];
    [|Some 2; Some 5; Some 1; Some 8; Some 7; Some 6; Some 4; Some 9;
      Some 3|];
    [|Some 5; Some 4; Some 8; Some 1; Some 3; Some 2; Some 9; Some 7;
      Some 6|];
    [|Some 7; Some 2; Some 9; None; Some 6; Some 4; None; Some 3; Some 8|];
    [|Some 1; Some 3; Some 6; Some 7; Some 9; Some 8; None; Some 4; Some 5|];
    [|Some 3; Some 7; Some 2; Some 6; Some 8; Some 9; Some 5; Some 1;
      Some 4|];
    [|Some 8; Some 1; Some 4; Some 2; Some 5; Some 3; Some 7; Some 6;
      Some 9|];
    [|Some 6; Some 9; Some 5; Some 4; Some 1; Some 7; Some 3; Some 8;
      Some 2|]|]}*)