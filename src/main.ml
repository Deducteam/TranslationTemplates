module T = Kernel.Term
module B = Kernel.Basic
module S = Kernel.Subst
module R = Kernel.Rule
module E = Parsers.Entry
module P = Parsers.Parser
module Pp = Api.Pp.Default



(* MORPHISM *)

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

(* Morphism on option term ty *)
let rec morphism_option ty = 
  match ty with
  | None -> None
  | Some t -> Some (morphism_term t)
(* Morphism on term v *)
and morphism_term v = 
  match v with
  | T.App (t, u, l) -> T.mk_App (morphism_term t) (morphism_term u) (List.map (fun x -> morphism_term x) l)
  | Lam (lo, id, ty, t) -> T.mk_Lam lo (morphism_ident id) (morphism_option ty) (morphism_term t) 
  | Pi (lo, id, a, b) -> T.mk_Pi lo (morphism_ident id) (morphism_term a) (morphism_term b)
  | Kind -> v
  | Type _ -> v
  | DB (lo, id, n) -> T.mk_DB lo (morphism_ident id) n
  | Const (lo, n) -> T.mk_Const lo (B.mk_name (morphism_mident (B.md n)) (morphism_ident (B.id n)))
;;


(* Morphism on entry e *)
let morphism_entry e = 
  let todo lo = T.mk_Const lo (B.mk_name (B.mk_mident "module_todo") (B.mk_ident "TODO")) in
  match e with
  | E.Decl (lo, id, s1, _, t) -> [ E.Def (lo, morphism_ident id, s1, false, Some (morphism_term t), todo lo) ]
  | Def (lo, id, s, io, ty, t) -> [ E.Def (lo, morphism_ident id, s, io, morphism_option ty, morphism_term t) ]
  | Rules (_, _) -> []
  | Eval (_, _, _) -> []
  | Check (_, _, _, _) -> []
  | Infer (_, _, _) -> []
  | Print (_, _) -> []
  | DTree (_, _, _) -> []
  | Name (_, _) -> []
  | Require (lo, mid) -> [ Require (lo, morphism_mident mid) ]
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
    | Some t -> 
      (match !template with
      | None -> Format.printf "[Error] No translation template given\n"
      | Some trans when (String.equal trans "morphism") -> 
        (let parsed_file = P.(parse (input_from_file (String.concat "" [s ; ".dk"]))) in
        print_string (String.concat "" ["#REQUIRE " ; t ; ".\n\n"]) ;
        List.iter (fun e -> List.iter (fun l -> Format.printf "%a" Pp.print_entry l) (morphism_entry e)) parsed_file)
      | Some trans when (String.equal trans "relation") -> Format.printf "Not defined\n"
      | Some trans when (String.equal trans "embedding") -> Format.printf "Not defined\n"
      | _ -> Format.printf "[Error] The translation template given does not exist\n"))
      
;;