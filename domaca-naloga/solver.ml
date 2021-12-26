type available = { loc : int * int; possible : int list }

(* TODO: tip stanja ustrezno popravite, saj boste med reševanjem zaradi učinkovitosti
   želeli imeti še kakšno dodatno informacijo *)
(* V atributu [problem] je shranjen začetni problem, v [current_grid] sudoku kot je izpolnjen v
trenutnem stanju, v [rows_taken], [cols_taken] in [boxes_taken] so označene številke, ki so že
uporabljene v posameznih vrsticah, stolpcih in škatlah, v [cur_index] je shranjeno mesto celice,
ki jo trenutno izpoljnjujemo, v [options] pa številke, ki po posameznih celicah še pridejo v poštev*)
type state = { problem : Model.problem; current_grid : int option Model.grid; rows_taken : int Array.t Array.t;
              cols_taken : int Array.t Array.t; boxes_taken : int Array.t Array.t; cur_index : int * int;
              options : available Array.t Array.t}

let print_state (state : state) : unit =
  Model.print_grid
    (function None -> "?" | Some digit -> string_of_int digit)
    state.current_grid

type response = Solved of Model.solution | Unsolved of state | Fail of state

let bool_to_int = function | true -> 1 | false -> 0

(* Preveri, ali nek element obstaja v dani škatli. *)
let exists_in_box box x = bool_to_int (Array.exists (fun sub -> (Array.exists (fun y -> y = x) sub)) box )

(* Generira seznam s prvimi devetimi naravnimi števili, če na [i,j]-tem mestu v sudokuju ni
števke, sicer vrne prazen seznam *)
let generate_possible grid i j = match grid.(i).(j) with
  | None -> []
  | Some x -> List.init 9 (fun i -> i + 1)

let initialize_state (problem : Model.problem) : state =
  let cur_grid = Model.copy_grid problem.initial_grid in
  { current_grid = cur_grid; problem; 
  rows_taken = Array.init 9 (fun row_ind -> 
    (Array.init 9 (fun i -> 
      bool_to_int ((List.exists (fun x -> x = i + 1) (Model.get_row cur_grid row_ind)))))); 
  cols_taken = Array.init 9 (fun col_ind -> 
    (Array.init 9 (fun i -> 
      bool_to_int ((List.exists (fun x -> x = i + 1) (Model.get_col cur_grid col_ind)))))); boxes_taken = 
  Array.init 9 (fun box_ind -> (Array.init 9 (fun i -> exists_in_box (Model.get_box cur_grid box_ind) (i + 1))));
  cur_index = (0, 0); options = Array.init 9 (fun i -> 
                          (Array.init 9 (fun j -> {loc = (i,j); possible =
                                generate_possible cur_grid i j})))}

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
  if i = 8 then None else (i + 1, 0)
) else (i, j + 1)

let branch_state (state : state) : (state * state) option =
  (* TODO: Pripravite funkcijo, ki v trenutnem stanju poišče hipotezo, glede katere
     se je treba odločiti. Če ta obstaja, stanje razveji na dve stanji:
     v prvem predpostavi, da hipoteza velja, v drugem pa ravno obratno.
     Če bo vaš algoritem najprej poizkusil prvo možnost, vam morda pri drugi
     za začetek ni treba zapravljati preveč časa, saj ne bo nujno prišla v poštev. *)
    let (i, j) = state.cur_index in 
    match state.options.(i).(j) with
      | [] -> None
      | x :: xs -> (
        let grid2 = Model.copy_grid state.current_grid in
        grid2.(i).(j) <- x;
        let rows2 = Array.copy state.rows_taken in
        rows2.(i).(x) <- rows2.(i).(x) + 1 
        let cols2 = Array.copy state.cols_taken in
        cols2.(j).(x) <- cols2.(j).(x) + 1
        let box2 = Array.copy state.boxes_taken in
        box2.(3 * (i/3) + j/3).(x) <- box2.(3 * (i/3) + j/3).(x) + 1
        let options2 = Array.copy state.options in
        options2.(i).(j) <- {loc = (i, j); possible = xs}
        ({current_grid = grid2; problem = state.problem; rows_taken = rows2; cols_taken = cols2;
        boxes_taken = box2; cur_index = (find_next_index i j); options = options2},
        {current_grid = state.current_grid; problem = state.problem; rows_taken = state_rows_taken;
        cols_taken = state.cols_taken; boxes_taken = state.boxes_taken; cur_index = state.cur_index;
        options = options2})
      )
(* pogledamo, če trenutno stanje vodi do rešitve *)
let rec solve_state (state : state) =
  (* uveljavimo trenutne omejitve in pogledamo, kam smo prišli *)
  (* TODO: na tej točki je stanje smiselno počistiti in zožiti možne rešitve *)
  let wrong_row = Array.exists (fun sub -> (Array.exists (fun x -> x > 1) sub)) state.rows_taken in
  let wrong_col = Array.exists (fun sub -> (Array.exists (fun x -> x > 1) sub)) state.cols_taken in
  let wrong_box = Array.exists (fun sub -> (Array.exists (fun x -> x > 1) sub)) state.boxes_taken in

  if wrong_row || wrong col || wrong_box then None else (
    match validate_state state with
    | Solved solution ->
        (* če smo našli rešitev, končamo *)
        Some solution
    | Fail fail ->
        (* prav tako končamo, če smo odkrili, da rešitev ni *)
        None
    | Unsolved state' ->
        (* če še nismo končali, raziščemo stanje, v katerem smo končali *)
        explore_state state'
  )

and explore_state (state : state) =
  (* pri raziskovanju najprej pogledamo, ali lahko trenutno stanje razvejimo *)
  match branch_state state with
  | None ->
      (* če stanja ne moremo razvejiti, ga ne moremo raziskati *)
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
