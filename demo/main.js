import lex from "../assembler/lexer.js";
import compile from "../assembler/compiler.js";
import { put } from "../assembler/helpers.js";
import WabtModule from "./wabt.js";

const source = `
import "foo" from "module" as $foo of i32 -> f64          | (implicit) type 1 (hidden)
define pointer table $opcodes with 100 as pointer $f      | $opcodes: pointer table
define variable i32 with 10
define constant pointer $pointer with $f

define pointer table with 10

define memory bank

    utf8 "hello", i8 1, 2, 3, i32 1

define function $f of type 0

    copy memory bank 0 to $data
    push i32 #FFFF_FFFF
    crash

import "init" as initializer

define memory $data with #10000

    @segment as push i32 #100
    i8 -1
    | assemble i32 to i8

    @segment at 200
    i8 250, utf8 " foobar !! "

define function $func as invoke type 0 in $opcodes
define type $t as i32 -> i64                              | (explicit) type 0
`;

const wabt = await WabtModule();
const binary = new Uint8Array(compile({source}));
const module = wabt.readWasm(binary, {threads: true});

put(module.toText({}));

// for (const token of lex({source})) put(token);
