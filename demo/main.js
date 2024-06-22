import { put } from "../assembler/helpers.js"
import compiler from "../assembler/compiler.js"
import WabtModule from "./wabt.js"

const source = `
import "foo" as $foo of i32 -> f64                        | (implicit) type 1 (hidden)
define pointer table $opcodes with 100 thus pointer $f    | $opcodes: pointer table

define memory bank

    utf8 "hello"

define function of type 0

    copy memory bank 0 to $data
    crash

define memory $data with 1

    @segment #100
    u8 255

    @segment 200
    u8 250, utf8 " foobar !! "

define function $f thus invoke type 0 in $opcodes
define type $t as i32 -> i64                              | (explicit) type 0
`;

const wabt = await WabtModule();
const binary = new Uint8Array(compiler({source}));
const module = wabt.readWasm(binary, {threads: true});

put(module.toText({}));

