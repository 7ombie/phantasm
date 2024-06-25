import lex from "../assembler/lexer.js";
import compile from "../assembler/compiler.js";
import { put } from "../assembler/helpers.js";
import WabtModule from "./wabt.js";

const source = `
| asm define constant i32 $n with 10
| asm define memory with 1 as utf8 "spam and eggs"

import "foo" from "module" as $foo of i32 -> f64          | (implicit) type 1 (hidden)
define pointer table $opcodes with 100 as pointer $f      | $opcodes: pointer table
define variable i32 with 10
define constant pointer $pointer with $f

define memory bank

    utf8 "hello"
    u8 1 | asm as i32.const 10, get global $n, add i32

    u32 1 | asm in 1 as push 0, push 13

define function $f of type 0

    copy memory bank 0 to $data
    push f64 9_000_000
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
