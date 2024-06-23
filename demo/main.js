import lex from "../assembler/lexer.js";
import compile from "../assembler/compiler.js";
import { put } from "../assembler/helpers.js";
import WabtModule from "./wabt.js";

const source = `
import "foo" as $foo of i32 -> f64                        | (implicit) type 1 (hidden)
define pointer table $opcodes with 100 as pointer $f      | $opcodes: pointer table
define variable i32 with 10
define constant pointer $pointer with $f

define memory bank

    utf8 "hello"

define function $f of type 0

    copy memory bank 0 to $data
    push f64 0                                            | (baseAddress + -#300_000.06/5)
    crash

define memory $data with 1

    @segment as push i32 #100
    u8 255

    @segment at 200
    u8 250, utf8 " foobar !! "

define function $func as invoke type 0 in $opcodes
define type $t as i32 -> i64                              | (explicit) type 0
`;

const wabt = await WabtModule();
const binary = new Uint8Array(compile({source}));
const module = wabt.readWasm(binary, {threads: true});

put(module.toText({}));

// for (const token of lex({source})) put(token);
