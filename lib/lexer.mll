{
open Lexing
open Parser

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
let ident = (alpha) (alpha|'-'|digit|'\'')*
let unum = digit+
let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read = parse
  | whitespace  { read lexbuf }
  | newline     { next_line lexbuf; read lexbuf }
  | "(*"        { read_comment lexbuf }
  | '"'         { read_string (Buffer.create 17) lexbuf }
  | "#infer"    { STMT_INF }
  | "#eval"     { STMT_EVAL }
  | "#parse"    { STMT_PARSE }
  | "#exec"     { STMT_EXEC }
  | "#check"    { STMT_CHECK }
  | "#against"  { STMT_AGAINST }
  | "#conv"     { STMT_CONV }
  | "#and"      { STMT_AND }
  | "#at"       { STMT_AT }
  | "#import"   { STMT_IMPORT }
  | "Type"      { TYPE }
  | "Bool"      { BOOL }
  | "𝔹"         { BOOL }
  | "True"      { TRUE }
  | "False"     { FALSE }
  | "Nat"       { NAT }
  | "ℕ"         { NAT }
  | "Zero"      { ZERO }
  | "Succ"      { SUCC }
  | "towards"   { TOWARDS }
  | "if"        { IF }
  | "then"      { THEN }
  | "else"      { ELSE }
  | "rec"       { REC }
  | "at"        { AT }
  | "record"    { RECORD }
  | "sig"       { SIG }
  | "end"       { END }
  | "lam"       { LAMBDA }
  | "λ"         { LAMBDA }
  | '.'         { DOT }
  | "let"       { LET }
  | "def"       { DEF }
  | '='         { EQ }
  | "in"        { IN }
  | "->"        { ARROW }
  | "→"         { ARROW }
  | '('         { LPAREN }
  | ')'         { RPAREN }
  | '{'         { LCURLY }
  | '}'         { RCURLY }
  | ':'         { COLON }
  | '|'         { PIPE }
  | ';'         { SEP }
  | ','         { COMMA }
  | '_'         { IDENT "" }
  | ident       { IDENT (Lexing.lexeme lexbuf) }
  | unum        { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | _           { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof         { EOF }

(* TODO nested comments *)
and read_comment = parse
  | "*)"        { read lexbuf }
  | newline     { next_line lexbuf; read_comment lexbuf }
  | eof         { raise (SyntaxError "file ends before comment") }
  | _           { read_comment lexbuf }

and read_string buf = parse
  | '"'         { STRING (Buffer.contents buf) }
  | '\\' '/'    { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\'   { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'    { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'    { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'    { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'    { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'    { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }

{

let parse_buf lexbuf =
  try Ok (program read lexbuf) with
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

}