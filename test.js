import lex from "/static/lexer.js";
import parse from "/static/parser.js";
import compile from "/static/compiler.js";
import wabt from "/static/wabt.js";

import { put, not, iife, format, stack, encodeUTF8 } from "/static/lexer.js";

let source = `
define variable i32 $foo as 10

define variable i64 $score thus push pointer 1, get $foo

define constant f64 as 3.141

define type as f64, f32 -> pointer

define type $binop as i32, i32 -> i32

import "score" from "game::player" as variable i32

import "PI" from "mathlib" as constant f64 $PI

import "system.memory" as shared memory with 1 max

import "system.opcodes" as pointer table $opcodes with #1000 max

import "sum" as function of type $binop

import "tax" as function of type 12

import "pow" as $pow of f64, f64 -> f64

define memory with #20 to #30

define shared memory $RAM with 1 max

    i8 #10, #20, #30
    f64 0.0, 0.1, 0.2
    utf8 "hello world"

import "references" from "pipeline" as proxy table with #100

define mixed table $instructions with 100 to 1000

    pointer $nop, $brk, $jts, $rts

define mixed table with 20 thus pointer $foo, $bar, proxy $spam, $eggs

define pointer table $functions with #100 to #1000

define $lerp of f32 $x, f32 $y, f64 $position -> f32

    add i32, mul f64
    add f32, return, mul f32

define type $void as void -> void

define $func of void -> void

    push i32 1000
    push i32 100
    push i32 4\\6

define $inc of i32, i32 -> i32 thus push i32 1, add i32

define function of type 10 thus add i32, add i32

define start function of type 0

    unreachable
    add i32

    loop of type $foo

        return, add i32, is zero i64, loop of type 0
            return

    add i32

    branch $if of i32 -> void

        sub f64, div f64

    else

        add i32
        sub i64

    is zero i32, branch $b of i32 -> f64

        add i32, sub i32

    else

        unreachable

export "data" as memory
export "opcodes" as table 3

export "zero" as register 0

define variable proxy $p
define constant pointer as $lerp
define variable i32
define constant f64 $PI as 3.141
define variable i64 thus get $reg

define pointer table $pointers with 256 max

    $nop
    $brk

define variable pointer $handler thus push pointer $init

define mixed table with 10 max

define mixed bank $foo thus proxy 10, 20, 30

define proxy bank $allsorts

    $string, $array, $object
    $nop, $brk, $jsr, $rts

define memory bank

    utf8 "Hello, World!"
    i64 0, 1, 2, 3, 4, 5, 6, 7

define $f of i32 -> i32

    ;; spam and eggs ;;

    local i32 $x, $y, pointer $f
    local f64 $a, $b, $c, i32, i32

    block of void -> void

        not more s32
        add i32

    is zero i32
    not more u32
    push i32 1
    push pointer $f
    push null pointer

    put 0
    put $foo

    ctz i32
    clz i64
    nsa i32

    call 10
    call $foobar

    nearest f32
    ceiling f64
    floor f32
    neg f64
    abs f32
    root f32
    min f64
    max f32
    sign f64

    jump
    jump 0
    jump $x

    fork
    fork 1
    fork $branch

    exit 2
    exit $foo 0 1 $bar

    rotate i32 left
    rotate i64 right

    shift u32 right
    shift i64 left

    get 100
    get table $opcode
    set table

    grow table 3
    grow memory

    fill table $pointers
    fill memory

    size table
    size memory 0

    copy table $opcodes to $pointers
    copy memory to 5
    copy table $opcode
    copy table 1

    copy table bank $opcodes to $pointers
    copy memory bank 0 to 5
    copy table bank $opcode
    copy table bank 1

    call 1
    invoke type 10
    invoke type $opcodes

    select pointer
    select f64

    drop
    drop table bank 1
    drop memory bank $foo

    wrap i64 to i32
    promote f32 to f64
    demote f64 to f32

    lop f64 to s32
    lop f32 sop u64

    convert s64 to f32

    cast i32 to f32
    cast i64 to f64
    cast f32 to i32
    cast f64 to i64

    expand s8 to i32
    expand s16 to i64
    expand s32 to i64

    extend s32 to i64
    extend u32 to i64

    and i32
    xor i64
    or i32

    load i32
    load f64 in 1
    load i32 as s8
    load i64 as u32
    load i64 as s32

    load i32 in $ram offset 4
    load i32 as u8 offset 16
    load i64 as u32 offset 3
    load i64 as s32 offset 0

    store f64 in 3
    store i32
    store i32 as i8
    store i64 as i32 in $memory

    store i32 in $ram offset 0
    store i32 as i8 offset 1
    store i64 as i32 offset #FF\\3

    atomic load i32 as u8
    atomic load i32 as u16 in $ram
    atomic load i32
    atomic load i64 as u32
    atomic load i64 as u16
    atomic load i64 as u8 in 1 offset 3
    atomic load i64

    atomic store i32 as i8 offset 1
    atomic store i32 as i16 in $ram
    atomic store i32
    atomic store i64 as i8
    atomic store i64 as i16 in $ram offset 20
    atomic store i64 as i32 in 3
    atomic store i64

    atomic add i32 as u8 offset 1
    atomic sub i32 as u16 in $ram
    atomic and i32
    atomic fence
    atomic or i64 as u8
    atomic xor i64 as u16 in $ram offset 20
    atomic swap i64 as u32 in 3
    atomic broker i64
    atomic wait i32 offset 1
    atomic wait i64 in $ram
    atomic notify offset 1
    atomic notify

define pointer table with 1
    0, 1, 2
    segment thus push f64 -Infinity
    $foo, $bar
    $spam

define mixed table with 1
    pointer 0, 1, 2
    segment
        push i32 70, push null pointer, get 0
    proxy $foo, $bar
    $spam

define shared memory with 1 max
    i8 0
    segment at 70
    i8 0, 1, 2
    utf8 "hi"
    segment thus get $register
    utf8 "hello world"
`;








source = `
define type $binop as i32, i32 -> i32
define type $check as i64 -> i32
define type $testtype as void -> void

import "pow1" from "mathlib" as $foo of i32, i32 -> i32
import "pow2" from "mathlib" as $bar of type $check
import "int" from "numbers" as variable i32 $integer
import "spam" from "eggs" as shared memory $audio with 10 max
import "opcodes" as pointer table $opcodes with #100 to #400
import "helpers" as proxy table $helpers with 100 max
import "spam" as constant i32 $constant
import "start" as start function

define variable i32 $n thus push i32 1
define variable f32 $lowNumber as -22.123
define constant i32 $lowerNumber as -2987
define constant pointer $pointer thus push pointer 3
define constant proxy $proxy

define function of i32 $arg0, f32 $arg1 -> i64

    local i32, i64
    local f64 $high, f32 $real

    set local 3
    set $arg1
    set global $n
    set table

    drop
    drop table bank 0
    drop memory bank $memory.bank

define function of type 0

    local i32, i64, f64 $x, $y, $z

    add i32, add i64, add f32, add f64
    sub i32, sub i64, sub f32, sub f64
    mul i32, mul i64, mul f32, mul f64

    block $block with void

        loop of type 0

            set $x
            jump $block

        branch $branch of i32, f32 -> proxy

            add i32
            jump
            jump $branch
            jump $block

            loop with void

                jump 0

            fork
            fork $branch
            fork $block
            fork 1
            exit 1 $branch 0

        else

            sub i32
            add i32
            call 3
            call 0
            invoke type 0
            invoke type $binop via 0, call 0
            invoke i32, i32 -> f32, call 4
            invoke type $check via $opcodes

            is null

            is zero i32
            is zero i64

            is equal i32
            is equal i64
            is equal f32
            is equal f64

            is more s32
            is more u32
            is more s64
            is more u64
            is more f32
            is more f64

            is less s32
            is less u32
            is less s64
            is less u64
            is less f32
            is less f64

            not equal i32
            not equal i64
            not equal f32
            not equal f64

            not more s32
            not more u32
            not more s64
            not more u64
            not more f32
            not more f64

            not less s32
            not less u32
            not less s64
            not less u64
            not less f32
            not less f64

    push pointer $bar
    unreachable
    select
    select proxy
    drop
    nop
    return

    put $x
    put 0

    clz i32
    clz i64
    ctz i32
    ctz i64
    nsa i32
    nsa i64

    and i32
    and i64
    or i32
    or i64
    xor i32
    xor i64

    copy memory $audio to $audio
    copy memory bank 0
    copy table 1 to $opcodes
    copy table bank $p.bank to 1
    copy memory bank $memory.bank
    copy table bank 0 to $opcodes

    get global $proxy

    load i32 at 5, load i64 at 0
    load f32, load f64
    load i32 as s8, load i32 as u8
    load i32 as s16, load i32 as u16 at 4
    load i64 as s8, load i64 as u8
    load i64 as s16, load i64 as u16
    load i64 as s32, load i64 as u32 at 1

    store i32 at 5, store i64 at 0
    store f32, store f64
    store i32 as i8
    store i32 as i16 at 4
    store i64 as i8
    store i64 as i16
    store i64 as i32

    push 10
    push f64 1.5\\6

    div u32, div s32, div u64, div s64, div f32, div f64
    rem u32, rem s32, rem u64, rem s64

    grow memory
    grow table 1
    fill memory $audio
    fill table
    size memory
    size table $opcodes

    abs f32, abs f64, neg f32, neg f64
    ceiling f32, ceiling f64, floor f32, floor f64
    nearest f32, nearest f64, root f32, root f64
    min f32, min f64, max f32, max f64
    sign f32, sign f64
    wrap i64 to i32

    cast i32 to f32, cast i64 to f64
    cast f32 to i32, cast f64 to i64

    shift i32 left, shift i64 left
    shift s32 right, shift u32 right
    shift s64 right, shift u64 right

    rotate i32 left, rotate i64 left
    rotate i32 right, rotate i64 right

    promote f32 to f64, demote f64 to f32

    lop f32 to s32, lop f32 to u32
    lop f32 to s64, lop f32 to u64
    lop f64 to s32, lop f64 to u32
    lop f64 to s64, lop f64 to u64

    lop f32 sop s32, lop f32 sop u32
    lop f32 sop s64, lop f32 sop u64
    lop f64 sop s32, lop f64 sop u32
    lop f64 sop s64, lop f64 sop u64

    convert s32 to f32, convert u32 to f32
    convert s64 to f32, convert u64 to f32
    convert s32 to f64, convert u32 to f64
    convert s64 to f64, convert u64 to f64

    extend s32 to i64, extend u32 to i64

    expand i32 as s8, expand i32 as s16
    expand i64 as s8, expand i64 as s16, expand i64 as s32

    atomic fence, atomic notify in 0 at 2
    atomic wait i32, atomic wait i64

    atomic add i32, atomic add i64
    atomic add i32 as u8, atomic add i32 as u16
    atomic add i64 as u8, atomic add i64 as u16, atomic add i64 as u32

    atomic sub i32, atomic sub i64
    atomic sub i32 as u8, atomic sub i32 as u16
    atomic sub i64 as u8, atomic sub i64 as u16, atomic sub i64 as u32

    atomic and i32, atomic and i64
    atomic and i32 as u8, atomic and i32 as u16
    atomic and i64 as u8, atomic and i64 as u16, atomic and i64 as u32

    atomic or i32, atomic or i64
    atomic or i32 as u8, atomic or i32 as u16
    atomic or i64 as u8, atomic or i64 as u16, atomic or i64 as u32

    atomic xor i32, atomic xor i64
    atomic xor i32 as u8, atomic xor i32 as u16
    atomic xor i64 as u8, atomic xor i64 as u16, atomic xor i64 as u32

    atomic swap i32, atomic swap i64
    atomic swap i32 as u8, atomic swap i32 as u16
    atomic swap i64 as u8, atomic swap i64 as u16, atomic swap i64 as u32

    atomic broker i32, atomic broker i64
    atomic broker i32 as u8, atomic broker i32 as u16
    atomic broker i64 as u8, atomic broker i64 as u16, atomic broker i64 as u32

    atomic load i32, atomic load i64
    atomic load i32 as u8, atomic load i32 as u16
    atomic load i64 as u8, atomic load i64 as u16, atomic load i64 as u32

    atomic store i32, atomic store i64
    atomic store i32 as i8, atomic store i32 as i16
    atomic store i64 as i8, atomic store i64 as i16, atomic store i64 as i32

define memory $RAM with #100
define memory $ram with #100

    segment
        push i32 10
    u32 1, u16 2, u8 3
    utf8 "spam and eggs"

    segment thus get $constant
    f64 1, 2, 3

define memory bank $memory.bank

    u32 1, u16 2, u8 3
    utf8 "spam and eggs", "spam"

import "func" from "lib" as $lib.func of i32, i32 -> i32

define proxy table $t0 with #100 max
define pointer table $tab with #100 max

    segment at 10
    pointer $lib.func, 1, null, 2, 3

define pointer bank $p.bank

    pointer 0, 1, 2, 3, 4

export "function" as function $bar
export "register" as register $pointer
export "memory" as memory $audio
export "table" as table

`;


const configuration = {
    source,
    url: "/main.source",
};

const features = {
    readDebugNames: true,
    exceptions: false,
    mutable_globals: true,
    sat_float_to_int: true,
    sign_extension: true,
    simd: false,
    threads: true,
    multi_value: true,
    tail_call: true,
    bulk_memory: true,
    reference_types: true,
    annotations: false,
    gc: true
};

const options = {
    log: true,
    relocatable: false,
    canonicalize_lebs: true,
    write_debug_names: true,

};

// for (const token of lex(sconfiguration)) put(token);
// for (const statement of parse(configuration)) put(statement);
// for (const byte of compile(configuration)) put(byte);

const binary = new Uint8Array(compile(configuration));
// put(binary)

const WABT = await wabt();
const module = WABT.readWasm(binary, features);

document.querySelector("pre").innerText = module.toBinary(options).log;
put(module.toText({}));

// const instance = await WebAssembly.instantiate(binary, {
//     lib: {func: (x, y) => x + y },
//     system: {global: new WebAssembly.Global({value: "i32", mutable: false}, 786)},
//     numbers: {int: new WebAssembly.Global({value: "i32", mutable: true}, 123)}
// });

// module.generateNames();
// module.resolveNames();
// module.applyNames();
// module.validate();
