{
open Lexing
open Parser_simple

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }

let print_err_pos lexbuf =
  let pos = lexbuf.lex_curr_p in
  "input:" ^ string_of_int pos.pos_lnum ^ ":" ^ string_of_int (pos.pos_cnum - pos.pos_bol + 1)
}

let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = (alpha) (alpha|'-'|digit)*
let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read = parse
  | whitespace  { read lexbuf }
  | newline     { next_line lexbuf; read lexbuf }
  | "Type"      { TYPE }
  | "Bool"      { BOOL }
  | "True"      { TRUE }
  | "False"     { FALSE }
  | "lam"       { LAMBDA }
  | "λ"         { LAMBDA }
  | '.'         { DOT }
  | "let"       { LET }
  | "def"       { DEF }
  | '='         { EQ }
  | "in"        { IN }
  | ".1"        { FST }
  | ".2"        { SND }
  | "->"        { ARROW }
  | "→"         { ARROW }
  | '*'         { TIMES }
  | "×"         { TIMES }
  | '('         { LPAREN }
  | ')'         { RPAREN }
  | ':'         { COLON }
  | ','         { COMMA }
  | ident       { IDENT (Lexing.lexeme lexbuf) }
  | _           { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof         { EOF }

{

let parse_buf lexbuf =
  try Ok (Parser_simple.program read lexbuf) with
    | SyntaxError reason ->
      let msg = print_err_pos lexbuf ^ ": " ^ reason in
      Error msg
    | Error ->
      let msg = print_err_pos lexbuf ^ ": syntax error" in
      Error msg

let parse_str str =
  let lexbuf = Lexing.from_string str in
  parse_buf lexbuf

let parse_file file =
  let handle = open_in file in
  let lexbuf = Lexing.from_channel handle in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file };
  let res = parse_buf lexbuf in
  close_in handle;
  res
  
(*
let parse_file name =
  let handle = open_in name in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  parse_str s
  *)

}