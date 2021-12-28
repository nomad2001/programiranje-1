type available = { loc : int * int; possible : int list }

(* V atributu [problem] je shranjen začetni problem, v [current_grid] sudoku kot je izpolnjen v
trenutnem stanju, v [rows_taken], [cols_taken] in [boxes_taken] je označeno, kolikokrat se posamezne 
številke v trenutni postavitivi, pojavljajo v posameznih vrsticah, stolpcih in škatlah, v [cur_index] 
je shranjeno mesto celice,ki jo trenutno izpoljnjujemo, v [options] pa številke, ki po posameznih 
celicah še pridejo v poštev*)
type state = { problem : Model.problem; current_grid : int option Model.grid; rows_taken : int Array.t Array.t;
              cols_taken : int Array.t Array.t; boxes_taken : int Array.t Array.t; cages_taken : int Array.t Array.t; 
              cages_sum : int Array.t; cur_index : int * int; options : available Array.t Array.t; wrong : bool}

let print_state (state : state) : unit =
  Model.print_grid
    (function None -> "?" | Some digit -> string_of_int digit)
    state.current_grid

type response = Solved of Model.solution | Unsolved of state | Fail of state

let bool_to_int = function | true -> 1 | false -> 0

(* Preveri, ali nek element obstaja v dani škatli. *)
let exists_in_box box x = bool_to_int (Array.exists (
  fun sub -> (
    Array.exists (function | None -> false | Some y -> y = x) sub)
    ) box 
  )

let initialize_cages_sum_taken (problem : Model.problem) sum taken =
  let rec one_cage (problem : Model.problem) i sum taken = function
    | [] -> (sum, taken)
    | x :: xs -> (
      let (c1, c2) = x in
      match problem.initial_grid.(c1).(c2) with
        | None -> one_cage problem i sum taken xs
        | Some y -> (
          sum.(i) <- sum.(i) + y;
          taken.(i).(y - 1) <- taken.(i).(y - 1) + 1;
          one_cage problem i sum taken xs
        )
    )
  in 

  let rec all_cages i (problem : Model.problem) sum taken = 
    if i >= Array.length sum then (sum, taken) else (
      let (sum2, taken2) = one_cage problem i sum taken (snd problem.cages.(i)) in
      all_cages (i + 1) problem sum2 taken2
  ) 
  in

  all_cages 0 problem sum taken

(* Naključno premeša seznam. Funkcija kopirana s strani 
https://stackoverflow.com/questions/15095541/how-to-shuffle-list-in-on-in-ocaml*)
let shuffle d =
    let nd = List.map (fun c -> (Random.bits (), c)) d in
    let sond = List.sort compare nd in
    List.map snd sond

(* Generira seznam s prvimi devetimi naravnimi števili, če na [i,j]-tem mestu v sudokuju ni
števke, sicer vrne prazen seznam *)
let generate_possible grid i j = match grid.(i).(j) with
  | Some x -> [x]
  | None -> shuffle (List.init 9 (fun i -> i + 1))

(* Inicializira začetno stanje*)
let initialize_state (problem : Model.problem) : state =
  let cur_grid = Model.copy_grid problem.initial_grid in
  let cols = Array.init 9 (fun col_ind -> 
    (Array.init 9 (fun i -> 
      bool_to_int ((Array.exists ( 
       function | None -> false | Some x -> x = i + 1) (Model.get_column cur_grid col_ind)))))) in
  let rows = Array.init 9 (fun row_ind -> 
    (Array.init 9 (fun i -> 
      bool_to_int ((Array.exists (
        function | None -> false | Some x -> x = i + 1) (Model.get_row cur_grid row_ind)))))) in
  let boxes = Array.init 9 (fun box_ind -> 
          (Array.init 9 (fun i -> exists_in_box (Model.get_box cur_grid box_ind) (i + 1)))) in
  let opts = Array.init 9 (fun i -> 
              (Array.init 9 (fun j -> {loc = (i,j); possible = generate_possible cur_grid i j}))) in 
  let (cages_s, cages_t) = initialize_cages_sum_taken problem (Array.init (Array.length problem.cages)
  (fun i -> 0)) (Array.init (Array.length problem.cages) (fun i -> (Array.init 9 (fun j -> 0)))) in

  let wrong_row = Array.exists (fun sub -> (Array.exists (fun x -> x > 1) sub)) rows in
  let wrong_col = Array.exists (fun sub -> (Array.exists (fun x -> x > 1) sub)) cols in
  let wrong_box = Array.exists (fun sub -> (Array.exists (fun x -> x > 1) sub)) boxes in
  let wrong_cage = Array.exists (fun sub -> (Array.exists (fun x -> x > 1) sub)) cages_t in
  let wrong_sum = Array.exists (fun i -> cages_s.(i) > (fst problem.cages.(i))) (Array.init 
  (Array.length problem.cages) (fun j -> j)) in
  {current_grid = cur_grid; problem; rows_taken = rows; cols_taken = cols;boxes_taken = boxes; 
  cages_sum = cages_s; cages_taken = cages_t; cur_index = (0, 0); options = opts; 
  wrong = (wrong_row || wrong_col || wrong_box || wrong_cage || wrong_sum)}

(* Preveri, ali smo popolnili tabelo in če smo, preveri še, ali trenutna postavitev reši sudoku. *)
let validate_state (state : state) : response =
  let unsolved =
    Array.exists (Array.exists Option.is_none) state.current_grid
  in
  if unsolved then Unsolved state
  else
    (* Option.get ne bo sprožil izjeme, ker so vse vrednosti v mreži oblike Some x *)
    let solution = Model.map_grid Option.get state.current_grid in
    if Model.is_valid_solution state.problem solution then Solved solution
    else Fail state

let find_next_index i j = if j = 8 then (
  if i = 8 then (8, 8) else (i + 1, 0)
) else (i, j + 1)

let copy_array_of_lists arr = Array.init 9 (fun i -> 
                                (Array.init 9 (fun j -> {loc = (i, j);
                                    possible = (List.map (fun x -> x) arr.(i).(j).possible)})))

let copy_cages cages = Array.init (Array.length cages) (fun i -> (Array.map (fun x -> x) cages.(i)))

let rec update_cages x sum taken cages = function
  | [] -> false
  | y :: ys -> (
    sum.(y) <- sum.(y) + x;
    taken.(y).(x - 1) <- taken.(y).(x - 1) + 1;
    if (sum.(y) > (fst cages.(y))) || (taken.(y).(x - 1) > 1) then true else (
      update_cages x sum taken cages ys
    )
  )

(* Razvejimo stanje na 1.možnost - prva izmed možnih števk v [possible] za trenutno mesto je pravilna, 
izberemo jo in rešimo preostali sudoku - in 2. možnost - prva izmed možnih števk za trenutno mesto je 
nepravilna in z njo ne moremo rešiti preostalega sudokuja, zato je pravilna števka med preostalimi 
elementi [possible] ali pa sploh ne obstaja, zato jo lahko iščemo med preostalimi števili v [possible]*)
let branch_state (state : state) : (state * state) option =
  let (i, j) = state.cur_index in 
  match state.options.(i).(j).possible with
    | [] -> None
    | x :: xs -> (
      let grid2 = Model.copy_grid state.current_grid in
      let rows2 = Model.copy_grid state.rows_taken in
      let cols2 = Model.copy_grid state.cols_taken in
      let box2 = Model.copy_grid state.boxes_taken in
      let cages2 = copy_cages state.cages_taken in
      let sum_cages2 = Array.copy state.cages_sum in
      let options2 = copy_array_of_lists state.options in
      options2.(i).(j) <- {loc = (i, j); possible = xs};

      match state.problem.initial_grid.(i).(j) with
        | None -> (
            grid2.(i).(j) <- Some x;
            rows2.(i).(x - 1) <- rows2.(i).(x - 1) + 1 ;
            cols2.(j).(x - 1) <- cols2.(j).(x - 1) + 1;
            box2.(3 * (i/3) + j/3).(x - 1) <- box2.(3 * (i/3) + j/3).(x - 1) + 1;
            let wrong_cages = update_cages x sum_cages2 cages2 state.problem.cages state.problem.in_cages.(i).(j) in
            let wrong2 = ((rows2.(i).(x - 1) > 1) || (cols2.(j).(x - 1) > 1) || 
            (box2.(3 * (i/3) + j/3).(x - 1) > 1) || wrong_cages) in

            Some ({current_grid = grid2; problem = state.problem; rows_taken = rows2; cols_taken = cols2;
            boxes_taken = box2; cages_taken = cages2; cages_sum = sum_cages2; cur_index = (find_next_index i j); 
            options = options2; wrong = (state.wrong || wrong2)},
            {current_grid = state.current_grid; problem = state.problem; rows_taken = state.rows_taken;
            cols_taken = state.cols_taken; boxes_taken = state.boxes_taken; cages_taken = state.cages_taken;
            cages_sum = state.cages_sum; cur_index = state.cur_index; options = options2; wrong = state.wrong})
        )
        | Some y -> 
            Some ({current_grid = grid2; problem = state.problem; rows_taken = rows2; cols_taken = cols2;
            boxes_taken = box2; cages_taken = cages2; cages_sum = sum_cages2; cur_index = (find_next_index i j); 
            options = options2; wrong = state.wrong},
            {current_grid = state.current_grid; problem = state.problem; rows_taken = state.rows_taken;
            cols_taken = state.cols_taken; boxes_taken = state.boxes_taken; cages_taken = state.cages_taken;
            cages_sum = state.cages_sum; cur_index = state.cur_index; options = options2; wrong = state.wrong})
    )

(* pogledamo, če trenutno stanje vodi do rešitve *)
let rec solve_state (state : state) =
  (* uveljavimo trenutne omejitve in pogledamo, kam smo prišli *)
  (*Printf.printf "%s %s\n"(string_of_int (fst state.cur_index)) (string_of_int (snd state.cur_index));*)
  (*Model.print_problem {initial_grid = state.current_grid; arrows = []; thermometers = []; cages = [||]; in_cages = [||]};
  for i = 0 to ((Array.length state.cages_taken) - 1) do
    for j = 0 to 8 do 
      Printf.printf "%d " state.cages_taken.(i).(j)
    done;
    Printf.printf "\n";
  done;
  *)
  let x = match state.current_grid.(0).(0) with
    | None -> -1
    | Some x -> x
  in
  Printf.printf "%d\n" x;
  (*for i = 0 to ((Array.length state.cages_sum) - 1) do
    Printf.printf "%d " state.cages_sum.(i)
  done;
  Printf.printf "\n";
  *)
  (*Model.print_grid string_of_int state.rows_taken;*)
  (*Printf.printf "%B\n" (wrong_row || wrong_col || wrong_box);*)
  if state.wrong then None else (
    match validate_state state with
    | Solved solution ->
        (* če smo našli rešitev, končamo *)
        (*Printf.printf "Solved\n";*)
        Some solution
    | Fail fail ->
        (* prav tako končamo, če smo odkrili, da rešitev ni *)
        (*Printf.printf "Fail\n";*)
        None
    | Unsolved state' ->
        (* če še nismo končali, raziščemo stanje, v katerem smo končali *)
        (*Printf.printf "Unsolved\n";*)
        explore_state state'
  )

and explore_state (state : state) =
  (* pri raziskovanju najprej pogledamo, ali lahko trenutno stanje razvejimo *)
  match branch_state state with
  | None ->
      (* če stanja ne moremo razvejiti, ga ne moremo raziskati *)
      (*Printf.printf "Couldn't branch.\n";*)
      None
  | Some (st1, st2) -> (
      (* če stanje lahko razvejimo na dve možnosti, poizkusimo prvo *)
      match solve_state st1 with
      | Some solution ->
          (* če prva možnost vodi do rešitve, do nje vodi tudi prvotno stanje *)
          Some solution
      | None ->
          (* če prva možnost ne vodi do rešitve, raziščemo še drugo možnost *)
          solve_state st2 )

let solve_problem (problem : Model.problem) =
  problem |> initialize_state |> solve_state
