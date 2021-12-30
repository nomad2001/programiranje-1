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

type problem = { initial_grid : int option grid; arrows: ((int * int) * ((int * int) List.t)) Array.t;
in_arrows: (int List.t) Array.t Array.t; thermometers : (int * int) List.t Array.t; 
in_thermos: (int List.t) Array.t Array.t; cages: (int * ((int * int) List.t)) Array.t; 
in_cages: (int List.t) Array.t Array.t}

let string_of_int_option = function
  | None -> " "
  | Some x -> string_of_int x

let print_problem (problem : problem) : unit = print_grid string_of_int_option problem.initial_grid

(* Koordinate zapisane v nizu spremeni v nabor. *)
let index_from_string str = ((int_of_char str.[1]) - (int_of_char '0'), (int_of_char str.[3]) - (int_of_char '0'))

(* Poišče vse koordinate, ki se pojavijo v nizu [str] od mesta [start] dalje. *)
let rec search_indices_from str start list = 
  let next_index = 
    try Some (Str.search_forward (Str.regexp "([0-9],[0-9])") str start) with
      Not_found -> None
  in

  match next_index with
    | None -> list
    | Some i -> (
      let matched = Str.matched_string str in
      let new_index = index_from_string matched in
      search_indices_from str (i + 1) (new_index :: list)
      )

(* Predela posebne sudokuje iz niza v obliko, s katero lahko lažje delamo. *)
let rec procces_special special proccesed = 
  let (arrow, thermo, cage) = proccesed in
  match special with
    | [] -> proccesed
    | x :: xs -> (if x = "" then proccesed else (
      match x.[0] with
        | 'K' -> (
          let start = Str.search_forward (Str.regexp "[0-9]+") x 0 in
          let matched = Str.matched_string x in
          procces_special xs (arrow, thermo, (int_of_string matched, search_indices_from x start []) :: cage)
        )
        | 'A' -> (
          let start = Str.search_forward (Str.regexp "([0-9],[0-9])") x 0 in
          let matched = Str.matched_string x in
          let first = index_from_string (matched) in
          procces_special xs ((first, search_indices_from x (start + 1) []) :: arrow, thermo, cage)
        )
        | 'T' -> procces_special xs (arrow, (List.rev (search_indices_from x 0 [])) :: thermo, cage)
        | _ -> procces_special xs proccesed
      )
    )

let rec generate_in_cages i arr = function
  | [] -> arr
  | x :: xs -> (
    let rec one_cage i arr = function
      | [] -> arr
      | y :: ys -> (
        let (c1, c2) = y in
        arr.(c1).(c2) <- (i :: arr.(c1).(c2));
        one_cage i arr ys
      )
    in

    generate_in_cages (i + 1) (one_cage i arr (snd x)) xs
  )

let rec generate_in_thermos i arr = function
  | [] -> arr
  | x :: xs -> (
    let rec one_thermo i arr = function
      | [] -> arr
      | y :: ys -> (
        let (c1, c2) = y in
        arr.(c1).(c2) <- (i :: arr.(c1).(c2));
        one_thermo i arr ys
      )
    in

    generate_in_thermos (i + 1) (one_thermo i arr x) xs
  )

let rec generate_in_arrows i arr = function
  | [] -> arr
  | x :: xs -> (
    let rec one_arrow i arr = function
      | [] -> arr
      | y :: ys -> (
        let (c1, c2) = y in
        arr.(c1).(c2) <- (i :: arr.(c1).(c2));
        one_arrow i arr ys
      )
    in

    let (c1, c2) = fst x in
    arr.(c1).(c2) <- (i :: arr.(c1).(c2));
    generate_in_arrows (i + 1) (one_arrow i arr (snd x)) xs
  )

let rec sum_of_cage solution sum = function
  | [] -> sum
  | x :: xs -> (
    let (c1, c2) = x in
    sum_of_cage solution (sum + solution.(c1).(c2)) xs
  )

let rec sum_arrow sum grid = function
  | [] -> sum
  | x :: xs -> (
    let (c1, c2) = x in
    match grid.(c1).(c2) with
      | None -> sum_arrow sum grid xs
      | Some y -> sum_arrow (sum + y) grid xs
  )

let rec check_arrows arrows grid = function
  | [] -> true
  | x :: xs -> (
    let (c1, c2) = fst arrows.(x) in
    match grid.(c1).(c2) with
      | None -> check_arrows arrows grid xs
      | Some y -> if y <> (sum_arrow 0 grid (snd arrows.(x))) then false else check_arrows arrows grid xs
    )

let problem_of_string str =
  Printf.printf "%s\n" str;
  let str2 = Str.split (Str.regexp "\r\n\r\n") str in 

  let cell_of_char = function
    | ' ' -> Some None
    | c when '1' <= c && c <= '9' -> Some (Some (Char.code c - Char.code '0'))
    | _ -> None
  in
  
  match str2 with
    | [ordinary; special] -> (
        let (arrow, thermo, cage) = procces_special (String.split_on_char '\n' special) ([], [], []) in
        { initial_grid = grid_of_string cell_of_char ordinary; arrows = Array.of_list arrow;
        in_arrows = generate_in_arrows 0 (Array.init 9 (fun i -> (Array.init 9 (fun j -> [])))) arrow;
        thermometers = Array.of_list thermo;
        in_thermos = generate_in_thermos 0 (Array.init 9 (fun i -> (Array.init 9 (fun j -> [])))) thermo; 
        cages = Array.of_list cage; 
        in_cages = generate_in_cages 0 (Array.init 9 (fun i -> (Array.init 9 (fun j -> [])))) cage }
      )
    | [ordinary] -> (
        { initial_grid = grid_of_string cell_of_char ordinary; arrows = [||]; 
        in_arrows =  (Array.init 9 (fun i -> (Array.init 9 (fun j -> [])))); thermometers = [||];
        in_thermos = (Array.init 9 (fun i -> (Array.init 9 (fun j -> [])))); cages = [||]; 
        in_cages = (Array.init 9 (fun i -> (Array.init 9 (fun j -> [])))) }
      )
  
(* Model za izhodne rešitve *)

type solution = int grid

let print_solution solution = print_grid string_of_int solution

let is_valid_solution problem solution = 
  (* Preveri, ali so v vsaki vrstici vse številke *)
  let rows_correct solution = List.for_all (fun row -> Array.for_all (fun ind -> 
          Array.exists (fun x -> x = ind) row) (Array.init 9 (fun i -> i + 1))) (rows solution) in
  (* Preveri, ali so v vsakem stolpcu vse številke *)
  let columns_correct solution = List.for_all (fun column -> Array.for_all (fun ind -> 
          Array.exists (fun x -> x = ind) column) (Array.init 9 (fun i -> i + 1))) (columns solution) in
  (* Preveri, ali so v vsaki škatli vse številke *)  
  let boxes_correct solution = List.for_all (fun box -> Array.for_all (fun ind -> 
          Array.exists (fun lst -> 
          Array.exists (fun x -> x = ind) lst) box) (Array.init 9 (fun i -> i + 1))) (boxes solution) in
  (* Preveri, ali sta problem in rešitev skladni. *)
  let sol_prob_same solution problem = Array.exists (fun i ->
                                      Array.exists (fun j -> (match problem.initial_grid.(i).(j) with
                                        | None -> false
                                        | Some x -> solution.(i).(j) != x
                                      )) (Array.init 9 (fun j -> j))) (Array.init 9 (fun i -> i)) in
  (* Ni treba preverjati, ali so v vseh kletkah same različne številke, ker to sproti preverjamo
  v datoteki [Solver.ml]. Prav tako ni treba preverjati, ali so v termometrih naraščajoča zaporedja, 
  saj tudi to sproti preverjamo v [Solver.ml] *)
  (* Preveri, ali so vsote v vseh kletkah pravilne *)
  let cages_correct solution problem = Array.for_all (fun sub -> 
    (fst sub) = (sum_of_cage solution 0 (snd sub))) problem.cages in
  (* Preveri, ali so vsote v vseh puščicah pravilne. *)
  let solution_option solution = Array.init 9 (fun i -> Array.init 9 (fun j -> Some solution.(i).(j))) in
  let arrows_correct solution problem = (
    check_arrows problem.arrows (solution_option solution) (List.init (Array.length problem.arrows) (fun j -> j))
  ) in

  (rows_correct solution) && (columns_correct solution) && (boxes_correct solution) && 
  (not (sol_prob_same solution problem)) && (cages_correct solution problem) && (arrows_correct solution problem)