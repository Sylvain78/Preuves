type signe = .. 
and lettre =
    | Lat_a | Lat_b | Lat_c | Lat_d | Lat_e | Lat_f | Lat_g | Lat_h | Lat_i | Lat_j | Lat_k | Lat_l | Lat_m | Lat_n | Lat_o | Lat_p | Lat_q | Lat_r | Lat_s | Lat_t | Lat_u | Lat_v | Lat_w | Lat_x | Lat_y | Lat_z 
    | Lat_A | Lat_B | Lat_C | Lat_D | Lat_E | Lat_F | Lat_G | Lat_H | Lat_I | Lat_J | Lat_K | Lat_L | Lat_M | Lat_N | Lat_O | Lat_P | Lat_Q | Lat_R | Lat_S | Lat_T | Lat_U | Lat_V | Lat_W | Lat_X | Lat_Y | Lat_Z
    | Prime of lettre        

type signe += Carre of int
type signe += Tau of int
type signe += Ou
type signe += Non
type signe += Lettre of lettre
type signe += Specifique of string * int

type assemblage = signe list

let (impl : assemblage) = [ Ou ; Non]

let (max_tau : assemblage -> int) =
  let rec max_tau_acc acc ass =
    match ass with
    | Tau n :: tl -> max_tau_acc (max acc n) tl
    | _ ::tl -> max_tau_acc acc tl
    | [] -> acc
  in 
  max_tau_acc 0

let concat_assemblage (a:assemblage) (b:assemblage) : assemblage =
  let lift = max_tau a
  in
  if lift = 0 
  then 
    a @ b
  else a @ (List.map (function 
      | Tau n -> Tau (n + lift) 
      | Carre n -> Carre (n + lift)
      | s -> s
    ) 
      b)

let tau (x:lettre) (ass:assemblage) : assemblage =
  let n = max_tau ass
  in
  Tau (n+1) :: (List.map (function 
      | Lettre l when l = x -> Carre (n+1)
      | s -> s) ass)

let figure (x:lettre) = (List.exists : (signe ->bool) -> assemblage -> bool )  ((=) (Lettre x))  

let subst (list_vars : lettre list) (list_ass: assemblage list)  (ass:assemblage) : assemblage =
  let subst_signe = List.fold_left2 (fun subs l' (ass' : assemblage) -> function Lettre l as s-> if (l = l') then ass' else subs s | s -> [s])
      (fun s -> [s]) list_vars list_ass
  in ass |> (List.map subst_signe) |> List.flatten
