module T = Kernel.Term
module B = Kernel.Basic
module S = Kernel.Subst
module R = Kernel.Rule
module E = Parsers.Entry
module P = Parsers.Parser
module Pp = Api.Pp.Default



(* THEORY MORPHISM *)


(* Morphism on ident id *)
let morphism_ident id = 
  (if B.ident_eq id B.dmark then 
    id
  else 
    B.mk_ident (String.concat "" [B.string_of_ident id ; "_mu"]))
;;

(* Morphism on mident id *)
let morphism_mident _ = 
  B.mk_mident "module_to_erase"
;;

(* Morphism on term v *)
let rec morphism_term v = 
  match v with
  | T.App (t, u, l) -> T.mk_App (morphism_term t) (morphism_term u) (List.map (fun x -> morphism_term x) l)
  | Lam (lo, id, None, t) -> T.mk_Lam lo id None (morphism_term t) 
  | Lam (lo, id, Some u, t) -> T.mk_Lam lo id (Some (morphism_term u)) (morphism_term t) 
  | Pi (lo, id, a, b) -> T.mk_Pi lo id (morphism_term a) (morphism_term b)
  | Kind -> v
  | Type _ -> v
  | DB (lo, id, n) -> T.mk_DB lo id n
  | Const (lo, n) -> T.mk_Const lo (B.mk_name (morphism_mident (B.md n)) (morphism_ident (B.id n)))
;;


(* Morphism on entry e *)
let morphism_entry e = 
  let todo lo = T.mk_Const lo (B.mk_name (B.mk_mident "module_todo") (B.mk_ident "TODO")) in
  match e with
  | E.Decl (lo, id, s1, _, t) -> [ E.Def (lo, morphism_ident id, s1, false, Some (morphism_term t), todo lo) ]
  | Def (lo, id, s, io, None, t) -> [ E.Def (lo, morphism_ident id, s, io, None, morphism_term t) ]
  | Def (lo, id, s, io, Some u, t) -> [ E.Def (lo, morphism_ident id, s, io, Some (morphism_term u), morphism_term t) ]
  | Rules (_, _) -> []
  | Eval (_, _, _) -> []
  | Check (_, _, _, _) -> []
  | Infer (_, _, _) -> []
  | Print (_, _) -> []
  | DTree (_, _, _) -> []
  | Name (_, _) -> []
  | Require (lo, mid) -> [ Require (lo, morphism_mident mid) ]
;; 




(* LOGICAL RELATION *)


(* Check if a term t is a kind *)
let rec is_kind t = 
  match t with
  | T.App (_, _, _) -> false
  | Lam (_, _, _, _) -> false
  | Pi (_, _, _, b) -> is_kind b
  | Kind -> false
  | Type _ -> true
  | DB (_, _, _) -> false
  | Const (_, _) -> false
;;

(* Apply an operation f to the De Bruijn indices of term w if they are greater of equal than i *)
let rec op_var w f i = 
  match w with
  | T.App (t, u, l) -> T.mk_App (op_var t f i) (op_var u f i) (List.map (fun x -> op_var x f i) l)
  | Lam (lo, id, None, t) -> T.mk_Lam lo id None (op_var t f (i + 1)) 
  | Lam (lo, id, Some u, t) -> T.mk_Lam lo id (Some (op_var u f i)) (op_var t f (i + 1)) 
  | Pi (lo, id, a, b) -> T.mk_Pi lo id (op_var a f i) (op_var b f (i + 1))
  | Kind -> w
  | Type _ -> w
  | DB (lo, id, n) -> 
    (if n >= i then
      T.mk_DB lo id (f n)
    else w)
  | Const (_, _) -> w
;;

(* Pre-processing so that there are no _ variables in term w *)
let rec explicit_var w = 
  let explicit_id id =
    (if B.ident_eq id B.dmark 
      then B.mk_ident "h" 
      else id)
  in match w with
  | T.App (t, u, l) -> T.mk_App (explicit_var t) (explicit_var u) (List.map (fun x -> explicit_var x) l)
  | Lam (lo, id, None, t) -> T.mk_Lam lo id None (explicit_var t) 
  | Lam (lo, id, Some u, t) -> T.mk_Lam lo id (Some (explicit_var u)) (explicit_var t) 
  | Pi (lo, id, a, b) -> T.mk_Pi lo (explicit_id id) (explicit_var a) (explicit_var b)
  | Kind -> w
  | Type _ -> w
  | DB (lo, id, n) -> T.mk_DB lo (explicit_id id) n
  | Const (_, _) -> w
;;

let morphism2_term t = op_var (morphism_term t) (fun n -> n * 2 + 1) 0;;
let add1 x = x + 1;;
let add2 x = x + 2;;

(* Return an application between an option term ty 
   (whose De Bruijn indices have been incremented twice),
   a term u and a list l *)
let app_option ty u l =
  match ty with
  | None -> None
  | Some t -> Some (T.mk_App (op_var t add2 0) u l)
;;

(* Put a prime on ident id *)
let prime_ident id = 
  (if B.ident_eq id B.dmark then 
    id
  else 
    B.mk_ident (String.concat "" [B.string_of_ident id ; "'"]))
;;

(* Logical relation on ident id *)
let relation_ident id = 
  (if B.ident_eq id B.dmark then 
    id
  else 
    B.mk_ident (String.concat "" [B.string_of_ident id ; "_rho"]))
;;

(* Logical relation on term v *)
let rec relation_term v arg = 
  match v with
  | T.App (t, u, l) -> 
    T.mk_App 
      (relation_term t None) 
      (morphism2_term u) 
      (List.cons (relation_term u None) (List.flatten (List.map (fun w -> [morphism2_term w; relation_term w None]) l)))
  | Lam (lo, id, None, t) -> 
    T.mk_Lam lo id None
      (T.mk_Lam lo (prime_ident id) None
        (relation_term t None))
  | Lam (lo, id, Some u, t) -> 
    T.mk_Lam lo id
      (Some (morphism2_term u)) 
      (T.mk_Lam lo (prime_ident id) 
        (Some (T.mk_App 
          (op_var (relation_term u None) add1 0)
          (T.mk_DB lo id 0) [])) 
        (relation_term t None))
  | Pi (lo, id, a, b) -> 
    (if is_kind b then 
      T.mk_Pi lo id 
        (morphism2_term a) 
        (T.mk_Pi lo (prime_ident id) 
          (T.mk_App (op_var (relation_term a None) add1 0) (T.mk_DB lo id 0) []) 
          (relation_term b (app_option arg (T.mk_DB lo id 1) [])))
    else 
      T.mk_Lam lo (B.mk_ident "f") 
        (Some (morphism2_term v))
        (T.mk_Pi lo id 
          (op_var (morphism2_term a) add1 0) 
          (T.mk_Pi lo (prime_ident id) 
            (T.mk_App (op_var (relation_term a None) add2 0) (T.mk_DB lo id 0) []) 
            (T.mk_App 
              (op_var (relation_term b None) add1 2)
              (T.mk_App (T.mk_DB lo (B.mk_ident "f") 2) (T.mk_DB lo id 1) []) 
              []))))
  | Kind -> v
  | Type lo -> 
    (match arg with 
    | None -> v (* Do not happen *)
    | Some t -> T.mk_Pi lo B.dmark t v)
  | DB (lo, id, n) -> T.mk_DB lo (prime_ident id) (n * 2)
  | Const (lo, n) -> T.mk_Const lo (B.mk_name (morphism_mident (B.md n)) (relation_ident (B.id n)))
;;

(* Logical relation on entry e *)
let relation_entry e = 
  let mid = B.mk_mident "module_to_erase" in 
  let todo lo = T.mk_Const lo (B.mk_name (B.mk_mident "todo") (B.mk_ident "TODO")) in
  match e with
  | E.Decl (lo, id, s1, _, t) -> 
    (if is_kind t then
      [ E.Def (lo, morphism_ident id, s1, false, Some (morphism_term t), todo lo) ;
        E.Def (lo, relation_ident id, s1, false, Some (relation_term (explicit_var t) (Some (T.mk_Const lo (B.mk_name mid (morphism_ident id))))), todo lo) ]
    else 
      [ E.Def (lo, morphism_ident id, s1, false, Some (morphism_term t), todo lo) ;
        E.Def (lo, relation_ident id, s1, false, Some (T.mk_App (relation_term (explicit_var t) None) (T.mk_Const lo (B.mk_name mid (morphism_ident id))) []), todo lo) ])
  | Def (lo, id, s, io, None, t) -> 
    [ E.Def (lo, morphism_ident id, s, io, None, morphism_term t) ; 
        E.Def (lo, relation_ident id, s, io, None, relation_term (explicit_var t) None) ]
  | Def (lo, id, s, io, Some u, t) -> 
    (if is_kind u then
      [ E.Def (lo, morphism_ident id, s, io, Some (morphism_term u), morphism_term t) ; 
        E.Def (lo, relation_ident id, s, io, Some (relation_term (explicit_var u) (Some (T.mk_Const lo (B.mk_name mid (morphism_ident id))))), relation_term (explicit_var t) None) ]
    else 
      [ E.Def (lo, morphism_ident id, s, io, Some (morphism_term u), morphism_term t) ; 
        E.Def (lo, relation_ident id, s, io, Some (T.mk_App (relation_term (explicit_var u) None) (T.mk_Const lo (B.mk_name mid (morphism_ident id))) []), relation_term (explicit_var t) None) ])
  | Rules (_, _) -> [] 
  | Eval (_, _, _) -> []
  | Check (_, _, _, _) -> []
  | Infer (_, _, _) -> []
  | Print (_, _) -> []
  | DTree (_, _, _) -> []
  | Name (_, _) -> []
  | Require (lo, mid) -> [ Require (lo, morphism_mident mid) ]
;;




(* THEORY EMBEDDING *)


(* Embedding morphism on ident id *)
let m_ident id = 
  (if B.ident_eq id B.dmark then 
    id
  else 
    B.mk_ident (String.concat "" [B.string_of_ident id ; "_m"]))
;;

(* Embedding relation on ident id *)
let r_ident id = 
  (if B.ident_eq id B.dmark then 
    id
  else 
    B.mk_ident (String.concat "" [B.string_of_ident id ; "_r"]))
;;

(* Embedding on mident id *)
let mr_mident _ = 
  B.mk_mident "module_to_erase"
;;

(* Embedding morphism on term v *)
let rec m_term v = 
  match v with
  | T.App (t, u, l) -> 
    T.mk_App 
      (m_term t) 
      (m_term u) 
      (List.cons (r_term u None) (List.flatten (List.map (fun w -> [m_term w; r_term w None]) l)))
  | Lam (lo, id, None, t) -> 
    T.mk_Lam lo id None
      (T.mk_Lam lo (prime_ident id) None
        (m_term t))
  | Lam (lo, id, Some u, t) -> 
    T.mk_Lam lo id 
      (Some (m_term u)) 
      (T.mk_Lam lo (prime_ident id) 
        (Some (T.mk_App 
          (op_var (r_term u None) add1 0)
          (T.mk_DB lo id 0) [])) 
        (m_term t))
  | Pi (lo, id, a, b) -> 
    T.mk_Pi lo id 
        (m_term a) 
        (T.mk_Pi lo (prime_ident id) 
          (T.mk_App (op_var (r_term a None) add1 0) (T.mk_DB lo id 0) []) 
          (m_term b))
  | Kind -> v
  | Type _ -> v
  | DB (lo, id, n) -> T.mk_DB lo id (2* n + 1)
  | Const (lo, n) -> T.mk_Const lo (B.mk_name (mr_mident (B.md n)) (m_ident (B.id n)))
(* Embedding relation on term v *)
and r_term v arg = 
  match v with
  | T.App (t, u, l) -> 
    T.mk_App 
      (r_term t None) 
      (m_term u) 
      (List.cons (r_term u None) (List.flatten (List.map (fun w -> [m_term w; r_term w None]) l)))
  | Lam (lo, id, None, t) -> 
    T.mk_Lam lo id None
      (T.mk_Lam lo (prime_ident id) None
        (r_term t None))
  | Lam (lo, id, Some u, t) -> 
    T.mk_Lam lo id 
      (Some (m_term u)) 
      (T.mk_Lam lo (prime_ident id) 
        (Some (T.mk_App 
          (op_var (r_term u None) add1 0)
          (T.mk_DB lo id 0) [])) 
        (r_term t None))
  | Pi (lo, id, a, b) -> 
    (if is_kind b then 
      T.mk_Pi lo id 
        (m_term a) 
        (T.mk_Pi lo (prime_ident id) 
          (T.mk_App (op_var (r_term a None) add1 0) (T.mk_DB lo id 0) []) 
          (r_term b (app_option arg (T.mk_DB lo id 1) [T.mk_DB lo (prime_ident id) 0])))
    else 
      T.mk_Lam lo (B.mk_ident "f") 
        (Some (m_term v))
        (T.mk_Pi lo id
          (op_var (m_term a) add1 0) 
          (T.mk_Pi lo (prime_ident id) 
            (T.mk_App (op_var (r_term a None) add2 0) (T.mk_DB lo id 0) []) 
            (T.mk_App 
              (op_var (r_term b None) add1 2)
              (T.mk_App (T.mk_DB lo (B.mk_ident "f") 2) (T.mk_DB lo id 1) [(T.mk_DB lo (prime_ident id) 0)]) 
              []))))
  | Kind -> v
  | Type lo -> 
    (match arg with 
    | None -> v (* Do not happen *)
    | Some t -> T.mk_Pi lo B.dmark t v)
  | DB (lo, id, n) -> T.mk_DB lo (r_ident id) (n * 2)
  | Const (lo, n) -> T.mk_Const lo (B.mk_name (mr_mident (B.md n)) (r_ident (B.id n)))
;;


(* Embedding on entry e *)
let mr_entry e = 
  let mid = B.mk_mident "module_to_erase" in 
  let todo lo = T.mk_Const lo (B.mk_name (B.mk_mident "todo") (B.mk_ident "TODO")) in
  match e with
  | E.Decl (lo, id, s1, _, t) -> 
    (if is_kind t then
      [ E.Def (lo, m_ident id, s1, false, Some (m_term (explicit_var t)), todo lo) ;
        E.Def (lo, r_ident id, s1, false, Some (r_term (explicit_var t) (Some (T.mk_Const lo (B.mk_name mid (m_ident id))))), todo lo) ]
    else 
      [ E.Def (lo, m_ident id, s1, false, Some (m_term (explicit_var t)), todo lo) ;
        E.Def (lo, r_ident id, s1, false, Some (T.mk_App (r_term (explicit_var t) None) (T.mk_Const lo (B.mk_name mid (m_ident id))) []), todo lo) ])
  | Def (lo, id, s, io, None, t) -> 
    [ E.Def (lo, m_ident id, s, io, None, m_term (explicit_var t)) ; 
        E.Def (lo, r_ident id, s, io, None, r_term (explicit_var t) None) ]
  | Def (lo, id, s, io, Some u, t) -> 
    (if is_kind u then
      [ E.Def (lo, m_ident id, s, io, Some (m_term (explicit_var u)), m_term (explicit_var t)) ; 
        E.Def (lo, r_ident id, s, io, Some (r_term (explicit_var u) (Some (T.mk_Const lo (B.mk_name mid (m_ident id))))), r_term (explicit_var t) None) ]
    else 
      [ E.Def (lo, m_ident id, s, io, Some (m_term (explicit_var u)), m_term (explicit_var t)) ; 
        E.Def (lo, r_ident id, s, io, Some (T.mk_App (r_term (explicit_var u) None) (T.mk_Const lo (B.mk_name mid (m_ident id))) []), r_term (explicit_var t) None) ])
  | Rules (_, _) -> [] 
  | Eval (_, _, _) -> []
  | Check (_, _, _, _) -> []
  | Infer (_, _, _) -> []
  | Print (_, _) -> []
  | DTree (_, _, _) -> []
  | Name (_, _) -> []
  | Require (lo, mid) -> [ Require (lo, mr_mident mid) ]
;;



(* PROCESSING *)

let usage_msg = "A tool to perform various translations between a source theory and a target theory in Dedukti.\n"
let template = ref None
let source = ref None
let target = ref None
let speclist = [( "--template", Arg.String (fun s -> template := Some s), "The name corresponding to the desired translation template") ;
                ( "--source", Arg.String (fun s -> source := Some s), "A Dedukti file representing the source of the translation") ;
                ( "--target", Arg.String (fun s -> target := Some s), "A Dedukti file representing the target of the translation")]

let () = 
  Arg.parse speclist (fun _ -> ()) usage_msg;
  match !source with
  | None -> Format.printf "[Error] No file given for the source theory\n"
  | Some s -> 
    (match !target with
    | None -> Format.printf "[Error] No file given for the target theory\n"
    | Some _ -> 
      (let parsed_file = P.(parse (input_from_file (String.concat "" [s ; ".dk"]))) in
      match !template with
      | None -> Format.printf "[Error] No translation template given\n"
      | Some trans when (String.equal trans "morphism") -> 
        List.iter (fun e -> List.iter (fun l -> Format.printf "%a" Pp.print_entry l) (morphism_entry e)) parsed_file
      | Some trans when (String.equal trans "relation") -> 
        List.iter (fun e -> List.iter (fun l -> Format.printf "%a" Pp.print_entry l) (relation_entry e)) parsed_file
      | Some trans when (String.equal trans "embedding") -> 
        List.iter (fun e -> List.iter (fun l -> Format.printf "%a" Pp.print_entry l) (mr_entry e)) parsed_file
      | _ -> Format.printf "[Error] The translation template given does not exist\n"))
;;