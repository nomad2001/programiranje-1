type available = { loc : int * int; possible : int list }
(* V atributu [problem] je shranjen začetni problem, v [current_grid] sudoku kot je izpolnjen v
trenutnem stanju, v [rows_taken], [cols_taken] in [boxes_taken] je označeno, kolikokrat se posamezne 
številke v trenutni postavitivi, pojavljajo v posameznih vrsticah, stolpcih in škatlah, v [cur_index] 
je shranjeno mesto celice,ki jo trenutno izpoljnjujemo, v [options] pa številke, ki po posameznih 
celicah še pridejo v poštev*)

type state = { problem : Model.problem; current_grid : int option Model.grid; rows_taken : int Array.t Array.t;
              cols_taken : int Array.t Array.t; boxes_taken : int Array.t Array.t; cages_taken : int Array.t Array.t; 
              cages_sum : int Array.t; cur_index : int * int; order : (int * int) option Array.t; 
              index_in_order : int option Array.t Array.t; options : available Array.t Array.t; wrong : bool}

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
    if i >= (Array.length sum) then (sum, taken) else (
      let (sum2, taken2) = one_cage problem i sum taken (snd problem.cages.(i)) in
      all_cages (i + 1) problem sum2 taken2
  ) 
  in

  all_cages 0 problem sum taken

let rec count_one indices order start count = function
  | [] -> count
  | x :: xs -> (
    let (c1, c2) = x in
    match indices.(c1).(c2) with
      | None -> (
        order.(start + count) <- Some x;
        indices.(c1).(c2) <- Some (start + count);
        count_one indices order start (count + 1) xs
      )
      | Some y -> count_one indices order start count xs
  )

let rec traverse_arrows arrows i start indices order =
  if i = (Array.length arrows) then start else (
    let (c1, c2) = (fst arrows.(i)) in
    
    match indices.(c1).(c2) with
      | None -> (
          order.(start) <- Some (fst arrows.(i));
          indices.(c1).(c2) <- Some start;
          let count = count_one indices order (start + 1) 0 (snd arrows.(i)) in
          traverse_arrows arrows (i + 1) (start + count + 1) indices order
        )
      | Some x -> (
          let count = count_one indices order start 0 (snd arrows.(i)) in
          traverse_arrows arrows (i + 1) (start + count) indices order
        )
  )

let rec traverse_cages cages i start indices order =
  if i = (Array.length cages) then start else (
    let count = count_one indices order start 0 (snd cages.(i)) in
    traverse_cages cages (i + 1) (start + count) indices order
  )

let rec traverse_thermometers thermos i start indices order =
  if i = (Array.length thermos) then start else (
    let count = count_one indices order start 0 thermos.(i) in
    traverse_thermometers thermos (i + 1) (start + count) indices order
  )

let rec traverse_others indices order count i j =
  if i = 9 then (order, indices) else (
    if j = 8 then (
      if indices.(i).(j) = None then (
        indices.(i).(j) <- Some count;
        order.(count) <- Some (i, j);
        traverse_others indices order (count + 1) (i + 1) 0
      ) 
      else (
        traverse_others indices order count (i + 1) 0
      )
    )
    else (
      if indices.(i).(j) = None then (
        indices.(i).(j) <- Some count;
        order.(count) <- Some (i, j);
        traverse_others indices order (count + 1) i (j + 1)
      ) 
      else (
        traverse_others indices order count i (j + 1)
      )
    )
  )

(* Inicializira zaporedje, v katerem izpolnjujemo celie v sudokuju. Najprej izpolnjujemo celice
v enakih puščicah, nato v enakih kletkah, nato v enakih termometrih in na koncu celice izven vseh
posebnih objektov. *)
let initialize_order (problem : Model.problem) = 
  let indices = Array.init 9 (fun i -> (Array.init 9 (fun j -> None))) in
  let order = Array.init 81 (fun i -> None) in
  let start1 = traverse_arrows problem.arrows 0 0 indices order in
  let start2 = traverse_cages problem.cages 0 start1 indices order in
  let start3 = traverse_thermometers problem.thermometers 0 start2 indices order in
  traverse_others indices order start3 0 0

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
  let (order, index_in_order) = initialize_order problem in

  let wrong_row = Array.exists (fun sub -> (Array.exists (fun x -> x > 1) sub)) rows in
  let wrong_col = Array.exists (fun sub -> (Array.exists (fun x -> x > 1) sub)) cols in
  let wrong_box = Array.exists (fun sub -> (Array.exists (fun x -> x > 1) sub)) boxes in
  let wrong_cage = Array.exists (fun sub -> (Array.exists (fun x -> x > 1) sub)) cages_t in
  let wrong_sum = Array.exists (fun i -> cages_s.(i) > (fst problem.cages.(i))) (Array.init 
  (Array.length problem.cages) (fun j -> j)) in
  let Some beggining = order.(0) in
  
  {current_grid = cur_grid; problem; rows_taken = rows; cols_taken = cols;boxes_taken = boxes; 
  cages_sum = cages_s; cages_taken = cages_t; cur_index = beggining; order = order; index_in_order = index_in_order;
  options = opts; wrong = (wrong_row || wrong_col || wrong_box || wrong_cage || wrong_sum)}

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

let find_next_index state i j = 
  match state.index_in_order.(i).(j) with
    | Some x -> if x = 80 then (i, j) else (
        match state.order.(x + 1) with
          | Some y -> y
    )
(* Ko zgornjo funkcijo uporabimo, v [state.index_in_order] in [state.order] ni več nobene vrednosti 
[None] in zato tega primera ni treba obravnavati. *)

let rec update_cages x sum taken cages validate = function
  | [] -> validate
  | y :: ys -> (
    sum.(y) <- sum.(y) + x;
    taken.(y).((Int.abs x) - 1) <- taken.(y).((Int.abs x) - 1) + (x / (Int.abs x));
    if (sum.(y) > (fst cages.(y))) || (taken.(y).((Int.abs x) - 1) > 1) then update_cages x sum taken cages true ys else (
      update_cages x sum taken cages validate ys
    )
  )

let rec check_thermometers grid thermometers = function
  | [] -> false
  | x :: xs -> (
    let rec check_one previous = function
      | [] -> false
      | y :: ys -> (
        let (c1, c2) = y in
        match grid.(c1).(c2) with
          | None -> check_one previous ys
          | Some x -> if x > previous then check_one x ys else true
      ) 
    in
    (check_one (-1) thermometers.(x)) || (check_thermometers grid thermometers xs)
  ) 

let rec check_arrows arrows grid = function
  | [] -> false
  | x :: xs -> (
    let (c1, c2) = fst arrows.(x) in
    match grid.(c1).(c2) with
      | None -> check_arrows arrows grid xs
      | Some y -> if y < (Model.sum_arrow 0 grid (snd arrows.(x))) then true else check_arrows arrows grid xs
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
      state.options.(i).(j) <- {loc = (i, j); possible = xs};

      match state.problem.initial_grid.(i).(j) with
        | None -> (
            state.current_grid.(i).(j) <- Some x;
            state.rows_taken.(i).(x - 1) <- state.rows_taken.(i).(x - 1) + 1 ;
            state.cols_taken.(j).(x - 1) <- state.cols_taken.(j).(x - 1) + 1;
            state.boxes_taken.(3 * (i/3) + j/3).(x - 1) <- state.boxes_taken.(3 * (i/3) + j/3).(x - 1) + 1;
            let wrong_cages = update_cages x state.cages_sum state.cages_taken state.problem.cages false state.problem.in_cages.(i).(j) in
            let wrong_thermos = check_thermometers state.current_grid state.problem.thermometers state.problem.in_thermos.(i).(j) in
            let wrong_arrows = check_arrows state.problem.arrows state.current_grid state.problem.in_arrows.(i).(j) in
            let wrong2 = ((state.rows_taken.(i).(x - 1) > 1) || (state.cols_taken.(j).(x - 1) > 1) || 
            (state.boxes_taken.(3 * (i/3) + j/3).(x - 1) > 1) || wrong_cages  || wrong_thermos || wrong_arrows) in
            Some ({current_grid = state.current_grid; problem = state.problem; rows_taken = state.rows_taken; 
            cols_taken = state.cols_taken; boxes_taken = state.boxes_taken; cages_taken = state.cages_taken; 
            cages_sum = state.cages_sum; cur_index = (find_next_index state i j); order = state.order; 
            index_in_order = state.index_in_order; options = state.options; wrong = (state.wrong || wrong2)},
            {current_grid = state.current_grid; problem = state.problem; rows_taken = state.rows_taken;
            cols_taken = state.cols_taken; boxes_taken = state.boxes_taken; cages_taken = state.cages_taken;
            cages_sum = state.cages_sum; cur_index = state.cur_index; order = state.order; 
            index_in_order = state.index_in_order; options = state.options; wrong = state.wrong})
        )
        | Some y -> 
            Some ({current_grid = state.current_grid; problem = state.problem; rows_taken = state.rows_taken; 
            cols_taken = state.cols_taken; boxes_taken = state.boxes_taken; cages_taken = state.cages_taken; 
            cages_sum = state.cages_sum; cur_index = (find_next_index state i j); order = state.order; 
            index_in_order = state.index_in_order; options = state.options; wrong = state.wrong},
            {current_grid = state.current_grid; problem = state.problem; rows_taken = state.rows_taken;
            cols_taken = state.cols_taken; boxes_taken = state.boxes_taken; cages_taken = state.cages_taken;
            cages_sum = state.cages_sum; cur_index = state.cur_index; order = state.order; 
            index_in_order = state.index_in_order; options = state.options; wrong = state.wrong})
    )

(* pogledamo, če trenutno stanje vodi do rešitve *)
let rec solve_state (state : state) =
  (* uveljavimo trenutne omejitve in pogledamo, kam smo prišli *)
  if state.wrong then ( 
    None
  ) else (
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
  let (i, j) = state.cur_index in
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
      | None -> (
          (* če prva možnost ne vodi do rešitve, raziščemo še drugo možnost *)
          let x = match state.current_grid.(i).(j) with | Some y -> y in
          let change = match state.problem.initial_grid.(i).(j) with 
            | None -> (
                state.current_grid.(i).(j) <- None;
                state.rows_taken.(i).(x - 1) <- state.rows_taken.(i).(x - 1) - 1 ;
                state.cols_taken.(j).(x - 1) <- state.cols_taken.(j).(x - 1) - 1;
                state.boxes_taken.(3 * (i/3) + j/3).(x - 1) <- state.boxes_taken.(3 * (i/3) + j/3).(x - 1) - 1;
                update_cages (-x) state.cages_sum state.cages_taken state.problem.cages false state.problem.in_cages.(i).(j)
            )
            | Some y -> true
          in
          change;
          let answer = solve_state st2 in
          state.options.(i).(j) <- {loc = (i, j); possible = (x :: state.options.(i).(j).possible)};
          answer
        )
      )

let solve_problem (problem : Model.problem) =
  problem |> initialize_state |> solve_state
