/* --{ THE PHANTASM LEXER }--{ /static/lexer.js }--------------------------- /*

This module implements the PHANTASM lexer, exporting a function named
`lex` as an entrypoint. */

import { not, iife, stack } from "/static/helpers.js";

/* --{ THE GLOBAL LEXER STATE }--------------------------------------------- */

let URL;            // used to store the url for the source file
let SOURCE;         // used to store the source string
let INDEX;          // the current character index
let CHARACTER;      // the current character
let TOKEN_STRING;   // used to build up token strings
let TOKEN_LINE;     // 1-indexed line number for start of token
let TOKEN_COLUMN;   // 1-indexed column number for start of token
let LINE_NUMBER;    // current line number (1-indexed)
let LINE_HEAD;      // the index of the first character in the current line
let INDENT_LEVEL;   // the current level of indentation
let LAST_TOKEN;     // tracks which type of token was last to be yielded

/* --{ A BUNCH OF USEFUL CONSTANTS }---------------------------------------- */

const [openBrace, closeBrace] = ["{", "}"];
const [plus, minus, dollar, circumflex] = ["+", "-", "$", "^"];
const [slash, backslash, underscore, dot] = ["/", "\\", "_", "."];
const [empty, space, newline, tab, quote] = ["", " ", "\n", "\t", "\""];
const [comma, semicolon, hash, atSign, zero] = [",", ";", "#", "@", "\0"];
const [backspace, formfeed, carriage, verticalTab] = ["\b", "\f", "\r", "\v"];

const arrow = "->";
const ellipsis = "...";
const decimals = "0123456789";
const specials = "[]{}(),;" + space + newline;
const numerics = plus + minus + hash + decimals;

const constants = [
    "Infinity", "+Infinity", "-Infinity", "NaN"
];

const primitives = [
    "utf8", "s8", "u8", "i8", "s16", "u16", "i16", "s32", "u32", "i32",
    "s64", "u64", "i64", "f32", "f64"
];

const components = [
    "variable", "constant", "register", "function", "memory", "table"
];

const qualifiers = [
    "pointer", "proxy", "mixed", "global", "local", "left", "right",
    "shared", "atomic"
];

const keywords = [
    "define", "import", "export", "type", "prime", "from", "max", "null",
    "start", "sop", "of", "with", "to", "zero", "equal", "less", "more",
    "thus", "bank", "segment", "at", "sop", "via", "in", "as"
];

const operations = [
    "get", "set", "put", "nop", "unreachable", "drop", "return", "add",
    "sub", "expand", "fork", "exit", "shift", "rotate", "sign", "grow",
    "fence", "min", "max", "load", "store", "and", "or", "xor", "swap",
    "abs", "nearest", "ceiling", "floor", "root", "invoke", "mul", "div",
    "rem", "block", "loop", "branch", "else", "is", "not", "push", "jump",
    "fill", "size", "copy", "extend", "select", "wrap", "promote", "demote",
    "lop", "convert", "cast", "notify", "broker", "ctz", "clz", "nsa", "call",
    "neg", "wait"
];

const escapees = {

    // the names and aliases for the ASCII characters...

    t: tab, tab,                                         // t | tab
    q: quote, quote,                                     // q | quote
    n: newline, newline,                                 // n | newline
    b: backspace, backspace,                             // b | backspace
    z: zero, null: zero, zero,                           // z | null | zero
    f: formfeed, ff: formfeed, formfeed,                 // f | ff | formfeed
    r: carriage, cr: carriage, return: carriage,         // r | cr | return
    v: verticalTab, vt: verticalTab, vtab: verticalTab,  // v | vt | vtab
    s: space, space,                                     // s | space

    // the names and aliases for the Unicode (specific) characters...

    divide: "\u{F7}",                       // division sign
    times: "\u{D7}", multiply: "\u{D7}",    // multiplication sign
    en: "\u{2013}", endash : "\u{2013}",    // en dash
    em: "\u{2014}", emdash : "\u{2014}",    // em dash
    paragraph: "\u{B6}",                    // paragraph marker
    section: "\u{A7}",                      // section marker
    check: "\u{2713}",                      // check mark
    cross: "\u{2717}",                      // cross mark
    left: "\u{2190}",                       // left arrow
    up: "\u{2191}",                         // up arrow
    right: "\u{2192}",                      // right arrow
    down: "\u{2193}",                       // down arrow
    ellipsis: "\u{2026}",                   // ellipsis character
    star: "\u{2606}",                       // five-pointed white star

    // note: see `en.wikibooks.org/wiki/Unicode/List_of_useful_symbols` as a
    // list of suggestions for names to provide as a starting point
};

/* --{ THE LEXER ERROR CLASSES }-------------------------------------------- */

export class PhantasmError extends SyntaxError {

    /* This is an abstract base class for PHANTASM compiler errors. Each stage
    of the compiler (`lex`, `parse` and `compile`) defines its own error class
    that replaces `Phantasm` with the stage name (`LexerError`, `ParserError`
    or `CompilerError`). The names are used to identify the stage in the error
    message. The classes are used to log an error, before completely aborting
    the current compilation process. */

    constructor (url, line, column, text) {

        super();

        const title = format(`{0.t} (Assembly Abandoned):`, this);
        const location = `${line}:${column} ${url}`;

        this.stack =  `${title}\n${text}\n${location}`;
    }
}

export class LexerError extends PhantasmError {

    /* This is the abstract class for all lexer errors. */

    constructor(text, nudge) {

        if (nudge) advanceToken();

        super(URL, TOKEN_LINE, TOKEN_COLUMN, text);
    }
}

class IllegalCharacterError extends LexerError {

    /* Thrown when an illegal character is found. */

    constructor(character, nudge) {

        /* The `character` argument is the illegal character, and `next` is a
        bool that determines if the function should advance the token before
        throwing an exception (affecting `TOKEN_LINE` and `TOKEN_COLUMN`). */

        const template = "Illegal character (`{0.s}`) found.";

        super(format(template, serialize(character)), nudge);
    }
}

class UnexpectedCharacterError extends LexerError {

    /* Thrown when an unexpected character is found. */

    constructor(character, context, nudge) {

        /* The `character` argument is the illegal character, and `next` is a
        bool that determines if the function should advance the token before
        throwing an exception (affecting `TOKEN_LINE` and `TOKEN_COLUMN`). */

        const template = "Unexpected {0.s} in {1.s}.";
        const text = format(template, serialize(character), context);

        super(text, nudge);
    }
}

class TrailingCommaError extends LexerError {

    /* Thrown when an indented line of code (that should be terminated
    implicitly) ends with a comma (which can look natural to people, if
    they are new to the grammar). */

    constructor() {

        /* This constructor requires no arguments, as the message is
        the same for all trailing commas, whatever the context. */

        super("Unexpected newline (trailing commas are illegal).", false);
    }
}

class StringError extends LexerError {

    /* Thrown when a problem is found in a string literal. There are a few
    possible problems, which are described by the caller. */

    constructor(description) {

        /* The `description` argument describes the problem.  */

        const text = format("Invalid {0.s} in string literal.", description);

        super(text, false);
    }
}

class UnrecognizedTokenError extends LexerError {

    /* Thrown when an invalid (unclassifiable) token has been parsed. */

    constructor(token) {

        /* The `token` argument is the invalid token value.  */

        const template = "Invalid (unclassifiable) token (`{0.s}`).";

        super(format(template, token), false);
    }
}

class InvalidContinuationError extends LexerError {

    /* Thrown when a continuation marker is not the last (printable)
    thing on the line, or the next line is improperly indented. */

    constructor(indentation) {

        /* The `indentation` argument is a bool. If truthy, the problem
        is invalid indentation, else the line continues after the marker. */

        let text;

        if (indentation) text = "A continuation must be properly indented.";
        else text = "A continuation marker must end its line.";

        super(text, false);
    }
}

class SuperIndentationError extends LexerError {

    /* Thrown when the indentation increases by more than one level. */

    constructor() {

        super("Indent increased by multiple levels.", false);
    }
}

class UnevenIndentationError extends LexerError {

    /* Thrown when the indentation level is not a multiple of four. */

    constructor() {

        const text = "Each indentation level must be exactly four spaces.";

        super(text, false);
    }
}

class NeverendingCommentError extends LexerError {

    /* Thrown when the indentation is not a multiple of four spaces. */

    constructor() {

        super("A multiline comment was opened, but never closed.", true);
    }
}


/* --{ ABSTRACT BASE CLASSES FOR THE LEXER TOKENS }------------------------- */

export class Node {

    /* This is the abstract base class for all AST nodes. It simply stores
    the location of the node in the source as a `{line, column}` hash. */

    constructor(location) { this.location = location }
}

export class Token extends Node {

    /* This is the abstract base class for all PHANTASM tokens. It stores the
    original token string and its location within the source. This class
    extends `Node` so that any instance of a `Token` subclass is also a
    valid AST node. */

    constructor(token=TOKEN_STRING, line=undefined, column=undefined) {

        super({
            line: line === undefined ? TOKEN_LINE : line,
            column: column === undefined ? TOKEN_COLUMN : column
        });

        this.value = token;
    }
}

export class Identity extends Token {}
export class Special extends Token {}
export class Delimiter extends Special {}
export class Indentation extends Special {}

/* --{ CONCRETE CLASSES FOR THE LEXER TOKENS }------------------------------ */

export class Comma extends Delimiter {}

export class Component extends Token {}
export class Operation extends Token {}
export class Primitive extends Token {}
export class SkinnyArrow extends Token {}
export class Keyword extends Token {}
export class Void extends Token {}
export class EOF extends Token {}

export class Indent extends Indentation {}
export class Dedent extends Indentation {}

export class Identifier extends Identity {}

export class Qualifier extends Token {}

export class ImplicitQualifier extends Token {

    /* This class is used to represent an implicit `global` or `local`
    qualifier in a `get` or `set` instruction. */

    constructor(value, location) {

        super(value, location.line, location.column);
    }
}

export class StringLiteral extends Token {}

export class ImplicitString extends StringLiteral {

    /* This class is used to represent an implicit string with a subclass
    of `StringLiteral`, permitting the parser stage to treat implicit and
    explicit strings as indistinct. It is used for implicit modulenames,
    passing the bytes for the string "host". */

    constructor(value, location) {

        super(value, location.line, location.column);
    }
}

export class NumberLiteral extends Identity {}

export class Constant extends NumberLiteral {}

export class ImplicitNumber extends NumberLiteral {

    /* This class is used to represent an implicit number with a subclass
    of `NumberLiteral`, permitting the parser stage to treat implicit and
    explicit numbers as indistinct. The `value` argument can be passed in
    as a Number, as it is converted to a string during instantiation. */

    constructor(value, location) {

        super(value, location.line, location.column);
        this.value = this.value.toString();
    }
}

export class Terminator extends Delimiter {

    /* This class implements the terminator token, which always has the
    same value. */

    constructor() { super("\u{23CE}") }
}

/* --{ THE LOCAL HELPER FUNCTIONS }----------------------------------------- */

export const format = function(string, ...args) {

    /* This function takes a `string` and an array of `args`. It uses `args`
    to format the string, returning the result. The formatting is tailored
    to the needs of the assembler.

    Escape sequences are wrapped in curly braces (and cannot be combined).
    Each sequence begins with an integer, followed by a dot, then a lower-
    case letter, eg: "{0.t}", and is replaced by a value taken from `args`.
    The integer is an index into `args`, and the letter indicates how to
    render the argument:

        + `t`: The argument type.
        + `v`: The value of the argument.
        + `V`: The value of the argument, wrapped in grave accents.
        + `f`: The argument, expressed with the syntax: Type(value)
        + `s`: The argument, converted to a string.

    The caller is responsible for ensuring that each argument supports the
    operations being performed on it (generally, args are `Token` instances
    (using `t`, `v`, `V` and `f`) or strings (using `s`).

    Note: The design of this function could be improved, but it works, and
    has all the features it needs, for now. */

    const replace = function(match) {

        /* This internal helper replaces one match. */

        const [arg, name] = match.split(".");
        const node = args[parseInt(arg)];
        const type = node.constructor.name || "";
        const literal = node instanceof StringLiteral;
        const value = literal ? `"${node.value}"` : `\`${node.value}\``;

        if (name === "t") return type;
        if (name === "s") return node;
        if (name === "V") return value;
        if (name === "v") return node.value;
        if (name === "f") return `${type}(${node.value})`;
    };

    for (const match of string.matchAll(/[^{\}]+(?=})/g)) {

        string = string.replace(`{${match[0]}}`, replace(match[0]));
    };

    return string;
};

export const encodeUTF8 = iife(function() {

    /* This IIFE sets up and returns the `encodeUTF8` function, enclosing
    the `TextEncoder` instance, so it can be reused for each string. The
    resulting function takes a string, and returns it as a `Uint8Array`
    of UTF-8 bytes. */

    const encoder = new TextEncoder();

    return string => encoder.encode(string)
});

export const normalizeNumberLiteral = iife(function() {

    /* This IIFE returns a function that takes a number literal string,
    converts hexadecimal digits to uppercase, and removes any separators,
    then returns the result (simplifying validation and encoding). */

    const strip = match => match.replace(underscore, empty);

    const regexes = [/[0-9]_[0-9]/g, /[0-9A-F]_[0-9A-F]/g];

    return function(string) {

        /* This function handles the actual normalization. It recursively
        invokes the `replaceAll` method, as it needs to match overlapping
        matches (like the `2` in a literal like  `1_2_3`, which is at the
        end of one match, and the start of another).

        Note: PHANTASM requires that every separator has a digit on either
        side of it. */

        const regex = regexes[string.includes(hash) * 1];

        string = string.toUpperCase();

        while (regex.test(string)) string = string.replaceAll(regex, strip);

        return string;
    };
});

const advance = function() {

    /* This function provides the lexer with a scanner that will move the
    global lexer state forward one character, then check the result. If the
    character is illegal (in an PHANTASM file), lexing is aborted. Otherwise,
    the character is returned.

    Note: The character will become `undefined` once the source is exhausted.
    The lexer uses this to indicate when to stop the loop and yield a final
    `EOF` token.

    The character is returned as a convenience, allowing the invocation to
    double as a predicate that can indicate when the source is exhausted. */

    CHARACTER = SOURCE[++INDEX];

    if (on(newline) || on(undefined)) return CHARACTER; // the special cases

    if (not(printable(CHARACTER))) {   // if `code` not an ASCII printable

        throw new IllegalCharacterError(CHARACTER, true);

    } else return CHARACTER;
};

const printable = function(character) {

    /* This helper takes a character and returns a bool that indicates
    whether the character is an ASCII printable or not. */

    const code = character.charCodeAt(0);

    return not(code < 0x20 || code > 0x7E);
};

const serialize = function(character) {

    /* This helper takes a character. If it is printable, the character is
    returned, else it is converted to its charcode (as a string), which is
    returned. This is used in error messages that interpolate characters. */

    if (printable(character)) return character;
    else return "0x" + character.charCodeAt(0).toString(16);
};

const note = function(token) {

    /* This function takes and returns a (new) token, making a note of it as
    the last token to be yielded by the lexer (permitting lookback). */

    return LAST_TOKEN = token;
};

const advanceLine = function() {

    /* This function updates the lexer state so it is ready to begin a
    new line. */

    LINE_HEAD = INDEX;
    LINE_NUMBER++;
};

const advanceToken = function() {

    /* This function updates the lexer state so it is ready to begin a
    new token. */

    TOKEN_LINE = LINE_NUMBER;
    TOKEN_COLUMN = INDEX - LINE_HEAD;
    TOKEN_STRING = CHARACTER;
};

const peek = function() {

    /* Peek at the next character in the source string, and return it. As
    the character could be invalid or `undefined`, the caller must allow
    for that (though this is normally unrequired or simple to handle). */

    return SOURCE[INDEX + 1];
};

const on = function(character) {

    /* Check whether the given character matches the current one, returning
    the result as a bool. */

    return character === CHARACTER;
};

const at = function(character) {

    /* Check whether the given character matches the next one, returning the
    result as a bool. */

    return character === peek();
};

const accept = function(character) {

    /* Take a character, check if it is next in the source, and return it if
    so (truthy for any character), returning `undefined` otherwise. */

    if (peek() === character) return advance();
};

const regulate = function() {

    /* Check that the next character exists and that it is not special, then
    return the result as a bool. */

    return peek() && not(specials.includes(peek()));
};

const gatherRegular = function(start=TOKEN_STRING) {

    /* Gather a token according to the longest-match rule, then return it,
    optionally taking a start string that replaces the current value of
    the `TOKEN_STRING` global before beginning. */

    TOKEN_STRING = start;

    while (regulate()) TOKEN_STRING += advance();

    return TOKEN_STRING;
};

const gatherString = function() {

    /* This helper gathers a string literal, handling any escape sequences
    and validating everything in the process. It returns the string that is
    expressed by the literal. */

    const gatherCharacters = stack(function(push) {

        /* This internal helper gathers the literal being parsed into a list
        of its characters, converting escape sequences as encountered, and
        ensuring everything is valid in the process. */

        let value;

        const unexpected = function(character, context) {

            /* Take the name of an unexpected character (in practice, either
            "eof" or "newline"), and the context it was found in ("literal"
            or "sequence"), and then complain, pointing to the specific
            character. */

            if (character === "eof") character = "string literal";
            else character = "newline";

            if (context === "literal") context = "end of file";
            else context = "escape sequence";

            throw new UnexpectedCharacterError(character, context, true);
        };

        const isName = function(expression) {

            /* Take an escape sequence expression and return `true` if it is a
            name (it contains at least one lowercase letter), else `false`. No
            check is performed here to ensure the name is actually defined. */

            return expression.toUpperCase() !== expression;
        };

        while (advance()) {

            if (on(quote)) return;
            else if (on(newline)) unexpected("newline", "literal");
            else if (on(closeBrace) && accept(closeBrace)) push(closeBrace);
            else if (on(openBrace) && accept(openBrace)) push(openBrace);
            else if (on(openBrace)) while (advance()) {

                if (on(space)) continue;
                if (on(closeBrace)) break;
                if (on(newline)) unexpected("newline", "sequence");
                if (on(undefined)) unexpected("eof", "sequence");

                advanceToken();
                gatherRegular(CHARACTER);

                if (isName(TOKEN_STRING)) {

                    if (TOKEN_STRING in escapees) push(escapees[TOKEN_STRING]);
                    else throw new StringError("named escape expression");

                } else {

                    try { value = BigInt("0x" + TOKEN_STRING) }
                    catch { throw new StringError("hex escape expression") }

                    try { push(String.fromCodePoint(Number(value))) }
                    catch { throw new StringError("Unicode code point") }
                }

            } else push(CHARACTER);

        } unexpected("eof", "literal"); // the loop exited without returning
    });

    return gatherCharacters().join(empty);
};

const classify = function() {

    /* This helper takes a token string and its location. It classifies the
    token (validating it where appropriate), before returning an instance of
    the corresponding `Token` subclass. If the token is unrecognized, a com-
    plaint is raised. */

    const token = TOKEN_STRING;

    if (token === "void") return new Void();

    if (token === arrow) return new SkinnyArrow();

    if (operations.includes(token)) return new Operation();

    if (keywords.includes(token)) return new Keyword();

    if (primitives.includes(token)) return new Primitive();

    if (qualifiers.includes(token)) return new Qualifier();

    if (components.includes(token)) return new Component();

    if (constants.includes(token)) return new Constant();

    if (token[0] === dollar && token[1]) return new Identifier(token.slice(1));

    if (numerics.includes(token[0])) return numerical(token);

    throw new UnrecognizedTokenError(token);
};

const numerical = iife(function() {

    /* This IIFE contains an array of decimal and hexadecimal regexes for
    matching PHANTASM number literals, and returns a function that deter-
    mines if its argument is a valid literal. */

    const regexes = [
        /^[+|-]?[0-9]+(\.[0-9]+)?([\/|\\][0-9]+)?$/,            // dec
        /^[+|-]?#[0-9A-F]+(\.[0-9A-F]+)?([\/|\\][0-9A-F]+)?$/   // hex
    ];

    return function(candidate) {

        /* This function takes a candidate string. If the string is a valid
        PHANTASM number literal, it is converted to a `NumberLiteral` and
        the instance is returned, else an error is raised. */

        const regex = regexes[candidate.includes(hash) * 1];
        const value = normalizeNumberLiteral(candidate);

        if (regex.test(value)) return new NumberLiteral(candidate);
        else throw new UnrecognizedTokenError(candidate);
    };
});

const handleNewline = stack(function(push, pop) {

    /* This helper is called on a Newline character. It implements significant
    whitespace. It uses `measureIndentation` to get (and validate) the absolute
    indent level, and will check the relative indent is not greater than one.

    Assuming valid indentation, an array is returned that contains an `Indent`
    if the level went up, and a `Terminator` if the level remained constant.
    If the level decreased, the returned array will contain one `Dedent`
    for each level (the `lex` function will then yield each token in
    the array).

    If the indentation has decreased (by any amount), and is now onside, an
    extra instance of `Terminator` is appended to the `Dedent` tokens. This
    allows the parser to validate that block-statements are terminated corr-
    ectly using the same logic as for regular statements (checking for a
    `Terminator`). */

    if (LAST_TOKEN instanceof Comma) throw new TrailingCommaError();

    const oldIndent = INDENT_LEVEL;
    const terminator = new Terminator();

    INDENT_LEVEL = measureIndentation();

    const delta = INDENT_LEVEL - oldIndent;

    if (delta === 0) return push(terminator);

    if (delta === 1) return push(new Indent("+1"));

    if (delta > 1) throw new SuperIndentationError();

    for (let i = 0; i > delta; i--) push(new Dedent("-1"));

    if (INDENT_LEVEL === 0) push(new Terminator());
});

const handleContinuation = function() {

    /* This helper is called on continuation markers. It validates that the
    next line (of code) is indented by one level, and advances the lexer state
    appropriately. It allows for whitespace after the continuation marker, and
    uses the `measureIndentation` helper to deal with any insignificant white-
    space below the marker and above the continuation line. */

    while (peek() !== newline && advance() === space) continue;

    if (peek() !== newline) throw new InvalidContinuationError(false);

    if (advance() && measureIndentation() === 1) return;
    else throw new InvalidContinuationError(true);
};

const handleCommentary = function() {

    /* This helper is called on a semicolon character, and gathers up either
    a multiline or an inline comment, depending on the next character. A com-
    plaint is raised if a multiline comment is left unclosed. Any gathered
    comment is discarded, and `undefined` is always returned. */

    if (peek() === semicolon) {                             // multiline

        const error = new NeverendingCommentError();

        advance(); advance(); // skip past the opening semicolons

        while (CHARACTER + advance() !== semicolon + semicolon) {

            if (on(newline)) advanceLine();
            else if (on(undefined)) throw error;
        }

    } else while (peek() && peek() !== newline) advance();  // inline
};

const measureIndentation = function() {

    /* This helper is called when the current character is a newline. It
    figures out how much indentation follows the newline, while ignoring
    empty lines and indented comments etc. If the indentation is valid,
    the helper returns the indentation level (in absolute terms) as an
    integer, else complaining.

    The lexer is left pointing to the last whitespace character it found
    (which may be the newline it began at). The helper also begins a new
    token before returning, so that any complaint (that may be raised by
    the caller on illegal indentation) will always point to the right
    place. */

    let spaces = 0;

    advanceLine();

    while(peek()) {

        spaces = 0;

        while (accept(newline)) advanceLine(); // skip over whitelines

        while (accept(space)) spaces++; // tally up the leading spaces

        if (peek() === newline) continue;
        else if (peek() === undefined) { spaces = 0; break }
        else if (peek() === semicolon) { advance(); handleCommentary() }
        else break;
    }

    advanceToken();

    if (spaces % 4) throw new UnevenIndentationError(spaces);
    else return spaces / 4;
};

const reset = function(configuration) {

    /* This is the generic reset helper for this module. It resets the lexer
    state, ready for a new source file. */

    INDENT_LEVEL = 0;
    URL = configuration.url;
    SOURCE = configuration.source;
    [INDEX, CHARACTER] = [-1, ""];
    [TOKEN_STRING, LAST_TOKEN] = ["", undefined];
    [TOKEN_LINE, TOKEN_COLUMN] = [1, 1];
    [LINE_NUMBER, LINE_HEAD] = [1, -1];
};

/* --{ THE LEXER ENTRYPOINT }----------------------------------------------- */

export const lex = function * (configuration) {

    /* This generator is the entrypoint for the PHANTASM lexer. It takes a
    configuration hash, and yields the tokens of the given source one by
    one, assuming no error is raised in the process. */

    reset(configuration);

    while (advance()) {

        advanceToken();

        if (on(space)) continue;

        if (on(newline)) for (let token of handleNewline()) yield note(token);

        else if (on(quote)) yield note(new StringLiteral(gatherString()));

        else if (on(semicolon)) handleCommentary();

        else if (specials.includes(CHARACTER)) {

            if (on(comma)) yield note(new Comma());
            else throw new IllegalCharacterError(CHARACTER, false);

        } else {

            gatherRegular();

            if (TOKEN_STRING === ellipsis) handleContinuation();
            else yield note(classify());
        }
    }

    for (let i = 0; i < INDENT_LEVEL; i++) yield note(new Dedent("-1"));

    if (not(LAST_TOKEN instanceof Terminator)) yield new Terminator();

    yield new EOF("(EOF)");
};

export default lex;
