/* --{ THE PHANTASM PARSER }--{ /static/parser.js }-------------------------- *

This module implements the PHANTASM parser, exporting a function named
`parse` as an entrypoint. */

import { not, iife, stack } from "/static/helpers.js";

import {
    lex, format, encodeUTF8, PhantasmError, Node, Token, Component,
    Keyword, Primitive, Qualifier, ImplicitQualifier, Void, SkinnyArrow,
    Identifier, Identity, normalizeNumberLiteral, EOF, Dedent, Delimiter,
    Operation, Indentation, Indent, StringLiteral, ImplicitString,
    Terminator, Comma, NumberLiteral, ImplicitNumber
} from "/static/lexer.js";

/* --{ THE GLOBAL PARSER STATE }-------------------------------------------- /*

This state is initialized by the `parse` function (at the end of the file)
every time that function is invoked to parse another file. They are global,
as they are referenced (and mutated) by various helper functions. */

let URL;             // the source file
let TOKENS;          // the token generator
let CURRENT_TOKEN;   // the current `Token` instance
let NEXT_TOKEN;      // the next `Token` instance
let FUTURE_TOKEN;    // the `Token` instance after the next `Token` instance
let GLOBAL_CONTEXT;  // tracks whether the context is global or not (local)
let START;           // tracks whether a start function has been defined yet

/* --{ USEFUL STRING CONSTANTS }-------------------------------------------- */

const [u8, s8, i8] = ["u8", "s8", "i8"];
const [u16, s16, i16] = ["u16", "s16", "i16"];
const [u32, s32, i32] = ["u32", "s32", "i32"];
const [u64, s64, i64] = ["u64", "s64", "i64"];
const [f32, f64, utf8] = ["f32", "f64", "utf8"];

const [shared, atomic] = ["shared", "atomic"];
const [pointer, proxy, mixed] = ["pointer", "proxy", "mixed"];
const [global, local, left, right] = ["global", "local", "left", "right"];

/* --{ THE PARSER ERROR CLASSES }------------------------------------------- */

class ParserError extends PhantasmError {

    /* The abstract base class for all parser errors. */

    constructor(arg) {

        /* This constructor can be invoked one of two ways, either passing a
        string or a hash of options. If the argument is a string, then it is
        used as the error message, while the location and URL are taken from
        the parser state. If the argument is a hash, then it must contain an
        error message, as a string, bound to its `text` property. The parser
        state can be overridden by assigning appropriate values to the `url`,
        `line` and `column` properties of the hash (in any combination). */

        if (typeof arg === "string") {

            const {line, column} = CURRENT_TOKEN.location;

            super(URL, line, column, arg);

        } else {

            const url = arg.url || URL;
            const line = arg.line || CURRENT_TOKEN.location.line;
            const column = arg.column || CURRENT_TOKEN.location.column;

            super(url, line, column, arg.text);
        }
    }
}

class UnexpectedTokenError extends ParserError {

    /* Thrown when an token is found with an unexpected token type. */

    constructor(expected, token) {

        /* The `expected` argument is a string describing the expected token
        classes, separated by the word *or* when there is more than one (for
        example "Reftype", "NumberLiteral or StringLiteral" etc), which must
        be created by the caller (in practice, the `require` helper). */

        super(format("Expected {0.s}, but found {1.f}.", expected, token));
    }
}

class ScopeError extends ParserError {

    /* Thrown when a global `get` or `set` instruction is explicitly local. */

    constructor(qualifier) {

        /* The `qualifier` argument is the invalid local `Qualifier` token. */

        const options = qualifier.location;

        options.text = "Global instructions cannot be explicitly local.";
        super(options);
    }
}

class MultipleStartFunctionsError extends ParserError {

    /* Thrown when the user attempts to define multiple start functions. */

    constructor(location) {

        super({
            text: "Cannot define multiple start functions.",
            line: location.line, column: location.column
        });
    }
}

class UnrecognizedStatementError extends ParserError {

    /* Thrown when a statement begins with a keyword that is not a primary
    keyword (one used to begin a statement). */

    constructor() {

        const text = "PHANTASM does not have a {0.v}-statement.";

        super(format(text, CURRENT_TOKEN));
    }
}

class SuperfluousTokenError extends ParserError {

    /* Thrown when a statement has been fully parsed, but there are still one
    or more tokens on the line (instead of the expected terminator). */

    constructor(node) {

        /* The `node` argument is the token that was found where a terminator
        was required. */

        const template = "Statement complete, but line continues with {0.f}.";

        super(format(template, node));
    }
}

class ProxyInitializerError extends ParserError {

    /* Thrown when a proxy register definition uses the as-shorthand (which is
    only valid for pointer and numtype registers). */

    constructor() {

        super("Cannot use `as` to initialize a proxy register.");
    }
}

class InvalidTestError extends ParserError {

    /* Thrown when an is-instruction or not-instruction specifies a test
    which is not valid (for example, `not zero i32` specifies the `zero`
    test, which is only supported by the is-instruction). */

    constructor(instruction) {

        /* The `instruction` argument is the instance of `IS` or `NOT` that
        includes the invalid test. */

        const name = nameInstruction(instruction, true);

        super(format("The {0.s} has no {1.V} test.", name, instruction.test));
    }
}

class InvalidPrimitiveError extends ParserError {

    /* Thrown when a primitive type is expected and found, but it is the
    wrong type of primitive. */

    constructor(description, node) {

        /* The `description` argument is a string that describes the type
        that was expected (something like "a sign-agnostic integer") that
        must be constructed by the caller. The `node` argument is the
        invalid primitive token. */

        const template = "Expected {0.s} type, not {1.V}.";

        super(format(template, description, node.type));
        this.location = node.type.location;
    }
}

class ExpectedKeywordError extends ParserError {

    /* Thrown when a keyword is expected, and some other class of token is
    found instead. */

    constructor(keyword, node) {

        /* The `keyword` argument is the expected keyword, as a string. The
        `node` argument is the invalid keyword token.*/

        super(format("Expected {0.s}-keyword, found {1.f}.", keyword, node));
    }
}

class UnexpectedKeywordError extends ParserError {

    /* Thrown when a specific keyword is expected, but some other keyword
    is found instead. */

    constructor(keyword) {

        /* The `keyword` argument is the expected keyword, as a string. */

        const template = "Expected {0.s}-keyword, found {1.v}-keyword.";

        super(format(template, keyword, CURRENT_TOKEN));
    }
}

class ExpectedComponentError extends ParserError {

    /* Thrown when a component is required (in a specifier or definition),
    but no valid component specifier can begin with the token found. */

    constructor(description, node) {

        /* The `description` argument is the descriptor name, as a string
        (one of "specifier" or "definition"). The `node` argument is the
        offending token. */

        const template = "Expected a component {0.s}, not {1.f}.";

        advance();
        super(format(template, description, node));
    }
}

class AtomicInstructionError extends ParserError {

    /* Thrown when the `atomic` qualfier is used with an instruction that
    cannot be atomic. */

    constructor(operation) {

        /* The `operation` argument is the offending `Operation` (actually a
        instance of a subclass). */

        super(format("The {0.v}-instruction cannot be atomic.", operation));
    }
}

class UnexpectedIndentError extends ParserError {

    /* Thrown when the indentation increases unexpectedly. */

    constructor() {

        super(format("Unexpected block (following {0.f}).", CURRENT_TOKEN));
    }
}

class ExpectedPrimitiveError extends ParserError {

    /* Thrown when a primitive token is expected, and some other type of token
    is found instead. */

    constructor() {

        super(format("Expected a Primitive type, not {0.f}.", advance()));
    }
}

class UnexpectedPrimitiveError extends ParserError {

    /* Thrown when a primitive token is expected and found, but it is not one
    of the expected primitive types. */

    constructor(description, token) {

        /* The `description` argument is a string that describes the expected
        types (for example, "a sign-agnostic integer"). The `token` argument
        is the unexpected `Primitive` instance. */

        super(format("Expected {0.s} type, not {1.V}.", description, token));
    }
}

class InvalidRegisterNameError extends ParserError {

    /* Thrown when a component name is required and a `Component` is found,
    but it is a register name that is not valid, given the context (using
    `variable` or `constant` in a reference, or using `register` in a
    specifier of definition). */

    constructor(reference, token) {

        /* The `reference` argument is a bool that is `true` when a reference
        was expected, and `false` when a specifier or definition was expected.
        The `token` argument is the token that was actually found. */

        const expected = reference ? "`register`" : "`constant` or `variable`";

        super(format("Expected {0.s}, found {1.V}.", expected, token));
    }
}

class ConstantIntegerError extends ParserError {

    /* Thrown when an integer is required, but the given literal uses a named
    constant (`Infinity`, `NaN` etc) that can only be expressed as a float. */

    constructor(token) {

        /* The `token` argument is the invalid number literal token. */

        const template = "Constants (like {0.V}) cannot express integers.";

        super(format(template, token));
    }
}

class MislabelledExitError extends ParserError {

    /* Thrown when an exit-instruction is found with an unexpected token type
    where the first label was expected. */

    constructor() {

        const ended = at(Terminator, Indentation);
        const ending = ended ? "." : format(", not {0.f}.", advance());

        super("The exit-instruction requires one or more labels" + ending);
    }
}

class InvertedLimitsError extends ParserError {

    /* Thrown when the maximum length of some limits `to <number-literal>` is
    given before the initial length `with <number-literal>` is specified. */

    constructor() {

        super("Maximum length found before initial length.");
    }
}

class InvalidTableQualifierError extends ParserError {

    /* Thrown when a table is specified (or defined) with an invalid
    qualifier. */

    constructor(qualifier) {

        /* The `qualifier` argument is the invalid `Qualifier` token. */

        super(format("Invalid table qualifier (${0.V}).", qualifier));
    }
}

class UnexpectedComponentError extends ParserError {

    /* Thrown when one or more components were expected, but a different
    component was found. */

    constructor(names) {

        /* The `names` argument is an array of strings that sets out the
        names of the expected components. */

        const template = "Expected {0.s} component, found {1.v} instead.";

        super(format(template, names.join(" or "), CURRENT_TOKEN));
    }
}

class ExpectedInlineBlockError extends ParserError {

    /* Thrown when an inline-block was expected (following `thus`), but the
    end of line was found. */

    constructor() {

        super("Expected an inline-block, but the line ended unexpectedly.");
    }
}

class UnexpectedInlineBlockError extends ParserError {

    /* Thrown when a block directive is found within an inline-block. */

    constructor() {

        super("Inline blocks cannot contain block-instructions.");
    }
}

class SegmentedBankError extends ParserError {

    /* Thrown when an segment-directive is found inside a bank primer. */

    constructor() {

        super("Bank primers cannot be segmented (banks are segments).");
    }
}

class BrokenDirectiveError extends ParserError {

    /* Thrown when a directive is illegally broken across multiple lines. */

    constructor() {

        super("Directives are terminated by the end of the line.");
    }
}

class EmptySegmentError extends ParserError {

    /* Thrown when a primer contains a segment-directive with no elements in
    the implied segment that follows the block. */

    constructor(token) {

        /* The `token` argument is the segment-keyword token instance. It is
        used to point the user to the beginning of the segment-block, which
        the parser is beyond (having parsed the block of instructions) by
        the time this error is discovered. */

        const options = token.location;

        options.text = "Primer segments must contain at least one element.";
        super(options);
    }
}

class ConstantError extends ParserError {

    /* Thrown when an instruction is found within a constant expression that
    is not constant. */

    constructor(instruction, description) {

        /* The `instruction` argument is the offending instruction node, and
        the `description` argument describes the issue, forming the beginning
        of a sentence that ends with "not valid in a constant expression". */

        const options = instruction.location;

        options.text = `${description} not valid in a constant expression.`;
        super(options);
    }
}

class UnqualifiedTableError extends ParserError {

    /* Thrown when a table is defined without its leading qualifier. */

    constructor() {

        super("Tables must be qualified (`mixed`, `pointer` or `proxy`).");
    }
}

class UnexpectedPrimerError extends ParserError {

    /* Thrown when a proxy or mixed table includes a primer (which is not
    currently permitted by the WebAssembly Specification). */

    constructor(qualifier) {

        super(`Only pointer (not ${qualifier}) tables can use primers.`);
    }
}

class MisqualifiedBankError extends ParserError {

    /* Thrown when table bank is qualified as anything other than `pointer`
    (the only type currently allowed in the spec). */

    constructor(qualifier) {

        /* The `qualifier` argument is the offending qualifier, as a string. */

        const template = "The Spec does not (currently) support {0.s} banks.";

        super(format(template, qualifier));
    }
}

class UnexpectedElseError extends ParserError {

    /* Thrown when an else-block is found without a preceding branch-block. */

    constructor() {

        super("Else-block found without preceding branch-block.");
    }
}

class BoundsError extends ParserError {

    /* Thrown on an integer that is outside its expected range. */

    constructor(literal, direction, width, signed) {

        /* The `literal` argument is the offending `NumberLiteral` instance.
        The `direction` argument (a string) describes the literal as being too
        "high" or "low". The `width` argument is the expected width (8, 16, 32
        or 64, in practice). The `signed` argument is a bool that is `true`
        for signed integers, and `false` for unsigned. */

        const bits = " " + width + "-bit ";
        const type = (signed ? "a signed" : "an unsigned") + bits + "integer";

        const template = `The value {0.V} is too ${direction} (for ${type}).`;

        super(format(template, literal, signed ? "signed" : "unsigned"));
    }
}

class UnspecifiedElementError extends ParserError {

    /* Thrown when a primer does not begin with the type of the first element
    (and it is not a primer for a typed table). */

    constructor(description) {

        /* The `description` argument describes the type of primer (either
        "memory" or "table", in practice). */

        const template = "Each element in a {0.s} primer " +
                         "must be part of a directive.";
        advance();
        super(format(template, description));
    }
}

class UntypedParameterError extends ParserError {

    /* Thrown when a signature does not begin with the type of its
    parameters. */

    constructor() {

        super("Signature parameters must specify a reftype.");
    }
}

class UntypedLocalError extends ParserError {

    /* Thrown when a local statement does not begin by specifying the type
    of the given locals. */

    constructor() {

        super("Local definitions must specify a reftype.");
    }
}

class SharedMemoryBankError extends ParserError {

    /* Thrown when the user specifies a `shared memory bank` (which does not
    exist). */

    constructor(qualifier) {

        /* The `component` argument is the `shared` Qualifier token, which is
        no longer the token the parser is on. */

        const options = qualifier.location;

        options.text = "Unknown component type (`shared memory bank`).";
        super(options);
    }
}

class ExpectedInlinePrimerError extends ParserError {

    /* Thrown when a primer was expected, but not found. */

    constructor(description) {

        /* The `description` argument is a string that describes the primer
        type ("memory" or "table"). */

        const text = "Expected inline-{0.s} primer (not a newline).";

        super(format(text, description));
    }
}

/* --{ ABSTRACT BASE CLASSES FOR AST NODES }-------------------------------- */

export class Statement extends Node {

    /* This is the abstract base class for all statements. It extends `Node`
    to add a `component` attribute that is used to store a component defini-
    tion, specification or reference, implemented by a `Component` subclass. */

    constructor(component, location) {

        super(location);
        this.component = component;
    }

    static parse(token) {

        const keyword = CURRENT_TOKEN.value;
        const location = CURRENT_TOKEN.location;

        if (keyword === "define") return new DefineStatement(location);
        else if (keyword === "import") return new ImportStatement(location);
        else if (keyword === "export") return new ExportStatement(location);
        else throw new UnrecognizedStatementError();
    }
}

export class Instruction extends Node {

    /* Abstract base class for all instructions. The simple, single-token
    instructions do not define their own `parse` function (or constructor),
    as this class does everything they need to do, but most instructions do
    override `parse`, so they can gather more tokens and add attributes.

    The `expression` argument is passed to the `parse` method, then a check
    is performed, and an error thrown if the instruction returns `undefined`
    and `expression` is truthy. Most instructions just ignore the argument,
    and return `undefined` (as they cannot appear in constant expressions).
    Those that are always valid in constant expressions just return `true`,
    skipping the check. Those instructions that may or may not be valid in
    constant expressions accept the argument and decide (within the `parse`
    method) what to do (either throwing an error or returing `true`).

    Note: The `block` attribute is conditionally intialized here (instead of
    within `BlockInstruction.constructor`) as we want `BlockInstruction` to
    subclass `Instruction`, though JavaScript prevents us from initializing
    `this.block` before we call `super`, and calling `super` will cause the
    block to be parsed before the array is even assigned to the instance. */

    constructor(operation, expression) {

        super(operation.location);
        this.operation = operation;

        if (this instanceof BlockInstruction) this.block = [];

        if (this.parse(expression) || not(expression)) return;

        const text = format("The {0.V} instruction is", operation);

        throw new ConstantError(this, text);
    }

    parse() { /* Used by plain instructions (like `nop` and `return`). */ }
}

export class MemoryInstruction extends Instruction {

    /* Abstract base class for all memory instructions. */

    parse() {

        /* This generic parse method works for all memory instructions, except
        the (atomic and non-atomic) `store` instructions, and the non-atomic
        `load` instruction, which each define their own `parse` methods. */

        this.type = requireIntegerNumtype();

        if (acceptKeyword("as")) {

            if (evaluate(this.type, i64)) {

                this.datatype = requireUnsignedDatatype();

            } else this.datatype = requireLesserUnsignedDatatype();

        } else this.datatype = undefined;

        this.resolveMemory();
        this.resolveOffset();
    }

    resolveMemory() {

        /* This helper method parses the optional `in <memory-identity>` part
        of a memory instruction. It returns the `NumberLiteral` instance, or
        an implicit zero instance, if no `in` keyword is found. */

        if (acceptKeyword("in")) this.memory = boundscheck(require(Identity));
        else this.memory = new ImplicitNumber(0, this.location);
    }

    resolveOffset() {

        /* This helper method parses the optional `at <offset>` part of a
        memory instruction. It returns the `NumberLiteral` instance, or an
        implicit zero instance, if no `at` keyword is found. */

        if (acceptKeyword("at")) {

            this.offset = boundscheck(require(NumberLiteral));

        } else this.offset = new ImplicitNumber(0, this.location);
    };
}

export class BlockInstruction extends Instruction {

    /* This class extends `Instruction` to add a generic `parse` method that
    works for all block instructions (`block`, `loop`, and `branch`). It also
    handles else-blocks (following branch-blocks). */

    parse() {

        this.identifier = accept(Identifier);

        if (acceptKeyword("with")) {

            if (at(Void)) this.type = advance();
            else this.type = requireValtype();

        } else {

            requireKeyword("of");
            this.type = requireType(true);
        }

        requireIndentedBlock(this);

        if (not(evaluate(this.operation, "branch"))) return;
        else if (not(atToken(Operation, "else"))) this.else = undefined;
        else this.else = requireIndentedBlock(new Else(advance()));
    }
}

class Else extends BlockInstruction {

    /* This is a concrete class for the else-block that optionally follows any
    branch-block. The class inherits everything it needs from its parents, and
    the `parse method of `BlockInstruction` will invoke `requireIndentedBlock`
    on any instance of `Else`, as soon it is instantiated, so there is nothing
    to do here, except prevent the `BlockInstruction.parse` method from being
    inherited (else it would be indirectly invoked again, recursively). */

    parse() {}
}

class RegisterAccessInstruction extends Instruction {

    /* This class extends `Instruction` to add a `parse` method that works for
    the `get` and `set` instructions (including `get/set.table`).

        get [<scope>] <identity>            <scope>.get <identity>
        set [<scope>] <identity>            <scope>.set <identity

    Note: In PHANTASM, `tee` is named `put`, and has no scope qualifier.

    All instructions have a `operation` property that stores the mnemonic (as
    a token instance), as well as having the `location` hash that is common to
    all `Node` subclasses). This class adds three more attributes:

    + `scope`: A `local` or `global` qualifier node, or a `table` component
       node, representing the target of the operation.
    + `global`: A bool that is `true` if the scope is global, and `false` if
       local (which may be defined explicitly or inferred).
    + `identity`: A `NumberLiteral` or `Identifier` node must be explicitly
       set, unless `scope` is `table`, where it can be implicitly zero.

    This method takes note of whether the context is a constant expression,
    as `get` is valid in expressions, but only if its scope is `global`. */

    parse(expression) {

        if (expression && evaluate(this.operation, "set")) return undefined;

        if (atToken(Component, "table")) { // `get table`...

            if (expression) {

                throw new ConstantError(this, "The `get table` operation");
            }

            this.scope = advance();
            this.global = GLOBAL_CONTEXT;
            this.identity = requireOptionalIdentity(this.scope.location);

            boundscheck(this.identity);

        } else { // `get local` or `get global`...

            if (this.scope = acceptQualifier(local, global)) {

                if (GLOBAL_CONTEXT && evaluate(this.scope, local)) {

                    throw new ScopeError(this.scope);

                } else this.global = this.scope.value === global;

            } else {

                const context = GLOBAL_CONTEXT ? "global" : "local";

                this.scope = new ImplicitQualifier(context, this.location);
                this.global = GLOBAL_CONTEXT;
            }

            this.identity = boundscheck(require(Identity));

            return true; // any issue would have been raised by now
        }
    }
}

class NumtypeInstruction extends Instruction {

    /* This class extends `Instruction` to add a `parse` method that works for
    all instructions (`add`, `sub` and `mul`) that specify a primitive numtype
    (i32, i64, f32 or f64). For example: `add i32`. */

    parse(expression) {

        this.type = requireNumtype();

        if (expression && [f32, f64].includes(this.type.value)) {

            throw new ConstantError(this, "Floating point operations are");

        } else return true;
    }
}

class IntegerNumtypeInstruction extends Instruction {

    /* This class extends `Instruction` to add a `parse` method that works for
    all instructions that specify a primtive integer type (i32 or i64). For
    example: `is zero i32` */

    parse() { this.type = requireIntegerNumtype() }
}

class FloatTypeInstruction extends Instruction {

    /* This class extends `Instruction` to add a `parse` method that works for
    all instructions that specify a signed primtive type (s32, u32, s64, u64,
    f32 or f64). */

    parse() { this.type = requireFloatType() }
}

class SignedTypeInstruction extends Instruction {

    /* This class extends `Instruction` to add a `parse` method that works for
    all instructions that specify a signed primtive type (s32, u32, s64, u64,
    f32 or f64). */

    parse() { this.type = requireGnosticNumtype() }
}

class ArrayReferenceInstruction extends Instruction {

    /* This class extends `Instruction` to add a `parse` method that works for
    all instructions that include a memory reference or table reference (`grow`
    `fill` and `size`). */

    parse() {

        this.component = requireComponent("memory", "table");
        this.identity = requireOptionalIdentity(this.component.location);

        boundscheck(this.identity);
    }
}

class ArrayTransferInstruction extends Instruction {

    /* This class extends `Instruction` to add a `parse` method that works for
    the (only) array-transfer-instruction, `copy`, which implements the WAT
    `copy` and `init` instructions. */

    parse() {

        this.component = requireComponent("memory", "table");
        this.bank = acceptKeyword("bank");

        const location = this.component.location;

        if (this.bank) this.identity = boundscheck(require(Identity));
        else this.identity = boundscheck(requireOptionalIdentity(location));

        if (acceptKeyword("to")) {

            this.destination = boundscheck(require(Identity));

        } else this.destination = new ImplicitNumber(0, location);
    }
}

class IdentifiedInstruction extends Instruction {

    /* This class extends `Instruction` to add a `parse` method that works for
    all instructions that specify an index as an identity (a number literal or
    an identifier bound to the index). */

    parse() {

        this.identity = boundscheck(require(Identity));
    }
}

class OptionallyIdentifiedInstruction extends Instruction {

    /* This class extends `Instruction` to add a `parse` method that works for
    all instructions that optionally specify an index as an identity (a number
    literal or an identifier bound to the index), defaulting to zero. */

    parse() {

        this.identity = boundscheck(requireOptionalIdentity(this.location));
    }
}

class MultiIdentifiedInstruction extends Instruction {

    /* This class extends `Instruction` to add a `parse` method that works for
    all instructions that optionally specify one or more indices as identities
    (each a number literal or an identifier bound to the index). */

    parse() {

        this.identities = requireIdentities().map(id => boundscheck(id));
    }
}

class CarouselInstruction extends Instruction {

    /* This class extends `Instruction` to add a `parse` method that works for
    the `rotate` and `shift` instructions. */

    parse() {

        const check = (description, ...types) => {

            if (evaluate(this.type, ...types)) return;
            else throw new InvalidPrimitiveError(description, this);
        };

        this.type = require(Primitive);
        this.qualifier = acceptQualifier(left, right);

        const qualifier = this.qualifier;

        // check that the mnemonic, type and qualifier are valid together...

        if (nameInstruction(this) === "rotate" || evaluate(qualifier, left)) {

            check("a sign-agnostic integer", i32, i64);

        } else check("a signed integer", u32, s32, u64, s64); // shift right
    }
}

/* --{ ABSTRACT BASE CLASSES FOR COMPONENT NODES --------------------------- */

class ComponentDescriptor extends Node {

    /* This is the abstract base class for component descriptors (specifiers,
    definitions and references). It exists as part of the type hierarchy. */
}

class ComponentDefinition extends ComponentDescriptor {

    /* This is the abstract base class for all component definitions, which
    are used by all define-statements. */

    constructor(location) {

        /* This constructor adds an `index` property to component definitions,
        which will be assigned an index by the compiler. */

        super(location);
        this.index = undefined;
    }

    static parse(location) {

        const name = nameNextComponent("definition");

        if (name === "function") return new FunctionDefinition(location);
        else if (name === "memory") return new MemoryDefinition(location);
        else if (name === "table") return new TableDefinition(location);
        else if (name === "type") return new TypeDefinition(location);
        else return new RegisterDefinition(location);
    }
}

class ComponentSpecifier extends ComponentDescriptor {

    /* An abstract base class for all component specifiers. */

    constructor(identifier, location) {

        /* This constructor adds an identifier attribute, and an index, to
        all component specifiers. The index is used by the compiler. */

        super(location);
        this.identifier = identifier;
        this.index = undefined;
    }

    static parse() {

        const name = nameNextComponent("specifier");
        const location = NEXT_TOKEN.location;

        if (name === "function") return new FunctionSpecifier(location);
        else if (name === "memory") return new MemorySpecifier(location);
        else if (name === "table") return new TableSpecifier(location);
        else return new RegisterSpecifier(location);
    }
}

class ComponentReference extends ComponentDescriptor {

    /* An abstract base class for all component references, which are used in
    all export-statements. */

    constructor(identity, name, location) {

        super(location);
        this.name = name;
        this.identity = boundscheck(identity);
    }

    static parse() {

        const component = require(Component);
        const location = component.location;
        const name = component.value;

        if (name === "register") return new RegisterReference(location);
        else if (name === "function") return new FunctionReference(location);
        else if (name === "memory") return new MemoryReference(location);
        else if (name === "table") return new TableReference(location);
        else throw new InvalidRegisterNameError(true, component);
    }
}

/* --{ CONCRETE CLASSES FOR STATEMENT NODES }------------------------------- */

export class DefineStatement extends Statement {

    /* The concrete class for define-statements. */

    constructor(location) {

        super(ComponentDefinition.parse(location), location);
    }
}

export class ImportStatement extends Statement {

    /* The concrete class for import-statements. */

    constructor(location) {

        const field = require(StringLiteral);
        const module = acceptPrefix("from", StringLiteral);

        requireKeyword("as");

        super(ComponentSpecifier.parse(), location);

        this.fieldname = field;
        this.modulename = module || new ImplicitString("host", location);
    }
}

export class ExportStatement extends Statement {

    /* The concrete class for export-statements. */

    constructor(location) {

        const field = require(StringLiteral);

        requireKeyword("as");

        super(ComponentReference.parse(), location);

        this.fieldname = field;
    }
}

/* --{ CONCRETE CLASSES FOR DEFINITION NODES }------------------------------ */

export class RegisterDefinition extends ComponentDefinition {

    /* Concrete class for registers definitions, which optionally define an
    identifier and initial value, and are either a `constant` or `variable`.

    The initializer can be implied by omission, defined with a single token,
    prefixed by the as-keyword (like `as 1` or `as $foo`), or defined by a
    constant expression. */

    constructor(location) {

        super(location);
        this.name = "register";
        this.constant = evaluate(advance(), "constant");
        this.type = requireValtype();
        this.identifier = accept(Identifier);
        this.block = [];

        if (acceptKeyword("as")) {

            if (evaluate(this.type, proxy)) throw new ProxyInitializerError();
            else if (evaluate(this.type, pointer)) {

                this.block.push(boundscheck(require(Identity)));

            } else {

                const number = require(NumberLiteral);
                const type = this.type.value;

                if (type === i32) boundscheck(number, 32, null);
                else if (type === i64) boundscheck(number, 64, null);

                this.block.push(number);
            }

        }
        else if (at(Terminator)) this.block.push(this.type)
        else requireBlock(this, true);
    }
}

export class LocalDefinition extends ComponentDefinition {

    /* Concrete class for each local register definition (usually combined
    into a larger `local` directive, defining multiple registers). */

    constructor(type, identifier, location) {

        super(location);
        this.type = type;
        this.identifier = identifier;
    }
}

export class FunctionDefinition extends ComponentDefinition {

    /* Concrete class for function definitions. */

    constructor(location) {

        const [start, identifier, type] = requireFunctionSpecifier();

        super(location);
        this.name = "function";
        this.identifier = identifier;
        this.start = start;
        this.type = type;
        this.locals = [];
        this.block = [];

        GLOBAL_CONTEXT = false; requireBlock(this); GLOBAL_CONTEXT = true;
    };
}

export class MemoryDefinition extends ComponentDefinition {

    /* Concrete class for memory and memory bank definitions. */

    constructor(location) {

        let min, max;

        super(location);
        this.shared = acceptQualifier(shared);

        const component = requireComponent("memory");

        if (acceptKeyword("bank")) {

            if (this.shared) throw new SharedMemoryBankError(this.shared);

            this.name = "memorybank";
            this.identifier = accept(Identifier);
            this.primer = requirePrimer("memory", true);
            this.bank = true;

        } else {

            this.identifier = accept(Identifier);

            if (this.shared) [min, max] = requireFullLimits()
            else [min, max] = requireLimits();

            this.name = "memory";
            this.primer = requireOptionalPrimer("memory", false);
            this.bank = false;
        }

        this.min = boundscheck(min);
        this.max = boundscheck(max);
    };
}

export class TableDefinition extends ComponentDefinition {

    /* Concrete class for table definitions. */

    constructor(location) {

        super(location);

        this.type = requireTableQualifier();

        if (atToken(Keyword, "bank") && not(evaluate(this.type, "pointer"))) {

            throw new MisqualifiedBankError(this.type.value);
        }

        if (acceptKeyword("bank")) {

            this.name = "tablebank";
            this.identifier = accept(Identifier);
            this.primer = requirePrimer(this.type.value, true);
            this.min = undefined;
            this.max = undefined;
            this.bank = true;

        } else {

            requireComponent("table");

            this.identifier = accept(Identifier);

            const [min, max] = requireLimits();

            this.name = "table";
            this.min = boundscheck(min);
            this.max = boundscheck(max);
            this.bank = false;

            const qualifier = this.type.value;

            if (qualifier !== "pointer") {

                if (not(at(Terminator))) {

                    throw new UnexpectedPrimerError(qualifier);

                } else this.primer = [];

            } else this.primer = requireOptionalPrimer(qualifier, false);
        }
    };
}

export class TypeDefinition extends ComponentDefinition {

    /* Concrete class for type definitions. */

    constructor(location) {

        super(location);
        this.name = "type";
        requireKeyword("type");
        this.identifier = accept(Identifier);
        requireKeyword("as");
        this.type = requireTypeExpression(true);
    };
}

/* --{ CONCRETE CLASSES FOR SPECIFIER NODES }------------------------------- */

export class RegisterSpecifier extends ComponentSpecifier {

    /* Concrete class for register specifiers. */

    constructor(location) {

        const constant = evaluate(advance(), "constant");
        const valtype = requireValtype();
        const identifier = accept(Identifier);

        super(identifier, location);
        this.name = "register";
        this.constant = constant;
        this.type = valtype;
    }
}

export class FunctionSpecifier extends ComponentSpecifier {

    /* Concrete class for function specifiers. */

    constructor(location) {

        const [start, identifier, type] = requireFunctionSpecifier();

        super(identifier, location);
        this.name = "function";
        this.start = start;
        this.type = type;
    }
}

export class MemorySpecifier extends ComponentSpecifier {

    /* Concrete class for memory specifiers. */

    constructor(location) {

        const qualifier = acceptQualifier(shared);

        requireComponent("memory");
        super(accept(Identifier), location);

        const [min, max] = qualifier ? requireFullLimits() : requireLimits();

        this.name = "memory";
        this.min = boundscheck(min);
        this.max = boundscheck(max);
        this.shared = qualifier;
    }
}

export class TableSpecifier extends ComponentSpecifier {

    /* Concrete class for table specifiers. */

    constructor(location) {

        const qualifier = requireTableQualifier();

        requireComponent("table");
        super(accept(Identifier), location);

        const [min, max] = requireLimits();

        this.name = "table";
        this.min = boundscheck(min);
        this.max = boundscheck(max);
        this.type = qualifier;
    };
}

/* --{ CONCRETE CLASSES FOR REFERENCE NODES }------------------------------- */

export class RegisterReference extends ComponentReference {

    /* Concrete class for register references. */

    constructor(location) {

        super(require(Identity), "register", location);
    }
}

export class FunctionReference extends ComponentReference {

    /* Concrete class for function references. */

    constructor(location) {

        super(require(Identity), "function", location);
    }
}

export class MemoryReference extends ComponentReference {

    /* Concrete class for memory references. */

    constructor(location) {

        super(requireOptionalIdentity(location), "memory", location);
    }
}

export class TableReference extends ComponentReference {

    /* Concrete class for table references. */

    constructor(location) {

        super(requireOptionalIdentity(location), "table", location);
    }
}

export class TypeReference extends ComponentReference {

    /* Concrete class for type references. */

    constructor(identity, location) {

        super(identity, "type", location);
    }
}

/* --{ CONCRETE CLASSES FOR ELEMENT NODES }--------------------------------- */

export class TypeExpression extends Node {

    /* Concrete class for a type expression or signature. */

    constructor(params, results, location) {

        super(location);
        this.params = params;
        this.results = results;
    }
}

export class ArityElement extends Node {

    /* Concrete class for an arity or result element (any element of a type
    expression that cannot have an identifier bound to it). */

    constructor(type) {

        super(type.location);
        this.type = type;
    }
}

export class ParamElement extends ArityElement {

    /* Concrete class for a param element (params are used in the arity
    parts of a signatures, and differ from `ArityElement`s by allowing
    an identifier to be bound to the element). */

    constructor(type, identifier) {

        super(type);
        this.type = type;
        this.identifier = identifier;
    }
}

export class TableElement extends Node {

    /* Concrete class for an element within a table primer. */

    constructor(type, explicit, value) {

        super(explicit ? type.location : value.location);
        this.type = type;
        this.value = value;

        if (not(evaluate(value, "null"))) boundscheck(value);
    }
}

export class MemoryElement extends Node {

    /* Concrete class for an element within a memory primer. */

    constructor(type, explicit, value) {

        const integers = [u8, u16, u32, u64];
        const lengths = {u8: 1, u16: 2, u32: 4, u64: 8, f32: 4, f64: 8};

        super(explicit ? type.location : value.location);
        this.length = lengths[type.value] || encodeUTF8(value.value).length;
        this.value = value;
        this.type = type;

        if (integers.includes(type.value)) boundscheck(value, this.length * 8);
    }
}

export class SegmentElement extends Node {

    /* Concrete class for the `segment` directives within primers, which are
    used to divide the primer into segments. */

    constructor() {

        /* This constructor parses `segment` directives. */

        super(CURRENT_TOKEN.location);
        this.block = [];

        if (acceptKeyword("at")) {              // at-integer shorthand

            this.block.push(boundscheck(require(NumberLiteral)));
            require(Terminator);

        } else if (acceptKeyword("thus")) {     // inline block expression

            requireInlineBlock(this);

            if (at(Dedent)) throw new EmptySegmentError(this);

            require(Terminator);

        } else requireIndentedBlock(this);      // indented block expression
    }
}

/* --{ INITIALIZE THE INSTRUCTIONS NAMESPACE }------------------------------ */

const instructions = Object.create(null);

instructions.atomic = Object.create(null);

instructions.nop = class NOP extends Instruction {}
instructions.unreachable = class UNREACHABLE extends Instruction {}
instructions.return = class RETURN extends Instruction {}

instructions.put = class PUT extends IdentifiedInstruction {}
instructions.call = class CALL extends IdentifiedInstruction {}

instructions.jump = class JUMP extends OptionallyIdentifiedInstruction {}
instructions.fork = class FORK extends OptionallyIdentifiedInstruction {}

instructions.exit = class EXIT extends MultiIdentifiedInstruction {}

instructions.block = class BLOCK extends BlockInstruction {}
instructions.branch = class BRANCH extends BlockInstruction {}
instructions.loop = class LOOP extends BlockInstruction {}

instructions.add = class ADD extends NumtypeInstruction {}
instructions.sub = class SUB extends NumtypeInstruction {}
instructions.mul = class MUL extends NumtypeInstruction {}

instructions.div = class DIV extends SignedTypeInstruction {}
instructions.rem = class REM extends SignedTypeInstruction {}

instructions.abs = class ABS extends FloatTypeInstruction {}
instructions.neg = class NEG extends FloatTypeInstruction {}
instructions.nearest = class NEAREST extends FloatTypeInstruction {}
instructions.ceiling = class CEILING extends FloatTypeInstruction {}
instructions.floor = class FLOOR extends FloatTypeInstruction {}
instructions.root = class ROOT extends FloatTypeInstruction {}
instructions.min = class MIN extends FloatTypeInstruction {}
instructions.max = class MAX extends FloatTypeInstruction {}
instructions.sign = class SIGN extends FloatTypeInstruction {}

instructions.grow = class GROW extends ArrayReferenceInstruction {}
instructions.fill = class FILL extends ArrayReferenceInstruction {}
instructions.size = class SIZE extends ArrayReferenceInstruction {}

instructions.copy = class COPY extends ArrayTransferInstruction {}

instructions.clz = class CLZ extends IntegerNumtypeInstruction {}
instructions.ctz = class CTZ extends IntegerNumtypeInstruction {}
instructions.nsa = class NSA extends IntegerNumtypeInstruction {}
instructions.and = class AND extends IntegerNumtypeInstruction {}
instructions.or = class OR extends IntegerNumtypeInstruction {}
instructions.xor = class XOR extends IntegerNumtypeInstruction {}

instructions.get = class GET extends RegisterAccessInstruction {}
instructions.set = class SET extends RegisterAccessInstruction {}

instructions.rotate = class ROTATE extends CarouselInstruction {}
instructions.shift = class SHIFT extends CarouselInstruction {}

instructions.select = class SELECT extends Instruction {

    /* This class implements the `select` instruction, which takes an
    optional valtype, just like WAT. */

    parse() { this.type = acceptValtype() }
}

instructions.load = class LOAD extends MemoryInstruction {

    /* This class implements the `load` mnemonic. */

    parse() {

        this.type = requireNumtype();

        const type = this.type.value;

        if ([i32, i64].includes(type) && acceptKeyword("as")) {

            if (type === i64) this.datatype = requireGnosticDatatype();
            else this.datatype = requireLesserGnosticDatatype();

        } else this.datatype = undefined;

        this.resolveMemory();
        this.resolveOffset();
    }
}

instructions.store = class STORE extends MemoryInstruction {

    /* This class implements the `store` mnemonic. */

    parse() {

        this.type = requireNumtype();

        const type = this.type.value;

        if ([i32, i64].includes(type) && acceptKeyword("as")) {

            if (type === i64) this.datatype = requireDatatype();
            else this.datatype = requireLesserDatatype();

        } else this.datatype = undefined;

        this.resolveMemory();
        this.resolveOffset();
    }
}

instructions.push = class PUSH extends Instruction {

    /* This class implements the `push` mnemonic, which takes an optional
    valtype, defaulting to `i32`, followed by an immediate value that is
    approriate for the given valtype. This implements the WAT `ref.null`
    and `ref.func` instructions, as well as the various `const`s:

        push <number-literal>               i32.const <number-literal>
        push <numtype> <number-literal>     <numtype>.const <number-literal>
        push pointer <identity>             ref.func <identity>
        push <reftype> null                 ref.null <reftype>

    Note: All `push` instructions are valid in a constant expression. */

    parse() {

        if (acceptReftype()) { // push <reftype>...

            this.name = CURRENT_TOKEN.value;

            if (this.name === pointer) {

                if (this.target = acceptKeyword("null")) /* done */;
                else this.target = boundscheck(require(Identity));

            } else this.target = requireKeyword("null");

        } else { // push [<numtype>]...

            if (this.target = accept(NumberLiteral)) this.name = i32;
            else {

                this.name = requireNumtype().value;
                this.target = require(NumberLiteral);
            }

            if (this.name === i32) boundscheck(this.target, 32, null);
            else if (this.name === i64) boundscheck(this.target, 64, null);
        }

        return true; // `push` is always valid in a constant expression
    }
}

instructions.invoke = class INVOKE extends Instruction {

    /* This class implements the `invoke` instruction (`call_indirect` in
    WAT). The instruction takes a required type immediate, followed by an
    optional table reference (which defaults to zero):

        invoke <type> [via <identity>]

    Even when the table is implicit, and the type uses a type expression that
    expresses its results with a list of comma-separated types (not void), it
    is still possible to group other instructions after this one (this is why
    the parser looks two tokens ahead). The `requireTypeExpression` function
    makes this work. */

    parse() {

        this.type = requireType(true);

        if (acceptKeyword("via")) this.table = require(Identity);
        else this.table = new ImplicitNumber(0, this.location);
    }
}

instructions.is = class IS extends Instruction {

    /* This class implements the `is` mnemonic, which is used for `is equal`,
    `is more`, `is less`, `is null` and `is zero` PHANTASM instructions. */

    parse() {

        this.test = require(Keyword);

        if (evaluate(this.test, "null")) {

            this.type = undefined;

        } else if (evaluate(this.test, "equal")) {

            this.type = requireNumtype();

        } else if (evaluate(this.test, "zero")) {

            this.type = requireIntegerNumtype();

        } else if (evaluate(this.test, "more", "less")) {

            this.type = requireGnosticNumtype();

        } else throw new InvalidTestError(this);
    }
}

instructions.not = class NOT extends Instruction {

    /* This class implements the `not` mnemonic, which is used for the
    `not equal`, `not more` and `not less` PHANTASM instructions. */

    parse() {

        this.test = require(Keyword);

        if (evaluate(this.test, "equal")) {

            this.type = requireNumtype();

        } else if (evaluate(this.test, "more", "less")) {

            this.type = requireGnosticNumtype();

        } else throw new InvalidTestError(this);
    }
}

instructions.drop = class DROP extends Instruction {

    /* This class implements the `drop` mnemonic, which is used for the WAT
    `drop`, `data.drop` and `elem.drop` instructions. */

    parse() {

        if (this.bank = acceptArrayName()) {

            requireKeyword("bank");
            this.identity = require(Identity);

        } else this.identity = undefined;
    }
}

instructions.wrap = class WRAP extends Instruction {

    /* This class implements the `wrap` mnemonic. */

    parse() {

        this.operand = requirePrimitiveType(i64);
        requireKeyword("to");
        this.result = requirePrimitiveType(i32);
    }
}

instructions.promote = class PROMOTE extends Instruction {

    /* This class implements the `promote` mnemonic. */

    parse() {

        this.operand = requirePrimitiveType(f32);
        requireKeyword("to");
        this.result = requirePrimitiveType(f64);
    }
}

instructions.demote = class DEMOTE extends Instruction {

    /* This class implements the `demote` mnemonic. */

    parse() {

        this.operand = requirePrimitiveType(f64);
        requireKeyword("to");
        this.result = requirePrimitiveType(f32);
    }
}

instructions.lop = class LOP extends Instruction {

    /* This class implements the `lop` mnemonic (`trunc` in Wasm), which
    includes the `sop` (`trunc_sat`) variant. */

    parse() {

        this.operand = requireFloatType();
        this.sop = Boolean(acceptKeyword("sop"));

        if (not(this.sop || acceptKeyword("to"))) this.result = undefined;
        else this.result = requireGnosticIntegerNumtype();
    }
}

instructions.convert = class CONVERT extends Instruction {

    /* This class implements the `convert` mnemonic. */

    parse() {

        this.operand = requireGnosticIntegerNumtype();
        requireKeyword("to");
        this.result = requireFloatType();
    }
}

instructions.cast = class CAST extends Instruction {

    /* This class implements the `cast` mnemonic (`reinterpret` in Wasm). */

    parse() {

        const map = {i32: f32, f32: i32, i64: f64, f64: i64};

        this.operand = requireNumtype();
        requireKeyword("to");
        this.result = requirePrimitiveType(map[this.operand.value]);
    }
}

instructions.expand = class EXPAND extends Instruction {

    /* This class implements the `expand` mnemonic, which covers those WAT
    `extend` instructions that have the same param and result type. These
    instructions sign-extend the lower bytes of the operand into the upper
    bytes. */

    parse() {

        this.datatype = requireSignedDatatype();
        requireKeyword("to");

        if (this.datatype.value === s32) this.type = requirePrimitiveType(i64);
        else this.type = requireIntegerNumtype();
    }
}

instructions.extend = class EXTEND extends Instruction {

    /* This class implements the `extend` mnemonic, which covers those WAT
    `extend` instructions that convert an `i32` to an `i64`. */

    parse() {

        this.operand = requireGnosticWordType();
        requireKeyword("to");
        this.result = requirePrimitiveType(i64);
    }
}

instructions.atomic.fence = class ATOMIC_FENCE extends Instruction {}

instructions.atomic.add = class ATOMIC_ADD extends MemoryInstruction {}
instructions.atomic.sub = class ATOMIC_SUB extends MemoryInstruction {}
instructions.atomic.and = class ATOMIC_AND extends MemoryInstruction {}
instructions.atomic.or = class ATOMIC_OR extends MemoryInstruction {}
instructions.atomic.xor = class ATOMIC_XOR extends MemoryInstruction {}
instructions.atomic.swap = class ATOMIC_SWAP extends MemoryInstruction {}
instructions.atomic.broker = class ATOMIC_BROKER extends MemoryInstruction {}
instructions.atomic.load = class ATOMIC_LOAD extends MemoryInstruction {}

instructions.atomic.store = class ATOMIC_STORE extends MemoryInstruction {

    /* This class implements the `atomic store` mnemonic. */

    parse() {

        this.type = requireIntegerNumtype();

        if (acceptKeyword("as")) {

            if (evaluate(this.type, i64)) {

                this.datatype = requireDatatype();

            } else this.datatype = requireLesserDatatype();

        } else this.datatype = undefined;

        this.resolveMemory();
        this.resolveOffset();
    }
}

instructions.atomic.wait = class ATOMIC_WAIT extends MemoryInstruction {

    /* This class implements the `atomic wait` mnemonic. */

    parse() {

        this.type = requireIntegerNumtype();
        this.resolveMemory();
        this.resolveOffset();
    }
}

instructions.atomic.notify = class ATOMIC_NOTIFY extends MemoryInstruction {

    /* This class implements the `atomic notify` mnemonic. */

    parse() {

        this.resolveMemory();
        this.resolveOffset();
    }
}

/* --{ HELPER FUNCTIONS }--------------------------------------------------- */

export const evaluateLiteral = function(token, integerMode=false) {

    /* This helper takes a number literal `token` instance and a bool named
    `integerMode` that defaults to `false`. It returns the value of the given
    literal, as a `BigInt` when the bool is truthy, and a `Number` otherwise.
    The helper uses integer arithmetic when `integerMode` is `true`, and uses
    floating point arithmetic otherwise (with the usual implications for the
    permitted ranges, and for rounding the results of exponentiation). There
    is an exception to this rule, when a literal uses floating point notation
    while `IntegerMode` is `true`. In that case, the floating point logic is
    employed, and the result is converted to a BigInt (using `Math.round`),
    just before it is returned (see the docs for more information). */

    const float = function(string) {

        /* Take a mantissa or an exponent, which can be a float or an integer,
        in decimal or hexadecimal notation, as a string, and return its value
        as an instance of `Number`. */

        const [beforeDot, afterDot] = string.replace("#", "0x").split(".");
        const integer = parseInt(beforeDot, radix);

        if (afterDot === undefined) return integer;

        const fraction = parseInt(afterDot, radix) / radix ** afterDot.length;

        return integer < 0 ? integer - fraction : integer + fraction;
    };

    const integer = function(string) {

        /* Take a mantissa or exponent, which must be an integer, in decimal
        or hexadecimal notation, as a string, and return its value as an
        instance of `BigInt`. */

        return BigInt(string.replace("#", "0x"));
    };

    const typecheck = function(number) {

        /* This helper takes and returns its only argument when the outer
        function is in Float Mode, and always raises an error in Integer
        Mode. It is used on constants to prevent an integer from evaluating
        to `Infinite`, `NaN` etc. */

        if (integerMode) throw new ConstantIntegerError(token);
        else return number;
    };

    const base = function(hexadecimal, integer) {

        /* This helper takes two bools. The first is `true` for hexadecimals,
        and `false` for decimals, and the second is `true` for integers, and
        `false` for floats. The helper returns the radix as a `BigInt` when
        `integer` is `true`, and a `Number` otherwise. */

        if (integer) return hexadecimal ? 16n : 10n;
        else return hexadecimal ? 16 : 10;
    };

    // return typechecked arg,if it is constant (`Infinity`, `NaN` etc)...

    if (["Infinity", "+Infinity"].includes(token.value)) {

        return typecheck(Infinity);

    } else if (token.value === "-Infinity") {

        return typecheck(-Infinity);

    } else if (token.value === "NaN") return typecheck(NaN);

    // otherwise, handle a regular literal (expressed using digits)...

    let result;

    const modes = {
        float: token.value.includes("."),
        hex: token.value.includes("#")
    };

    const parse = modes.float ? float : (integerMode ? integer : float);

    const radix = base(modes.hex, parse === integer);
    const value = normalizeNumberLiteral(token.value);

    if (value.includes("/")) {                  // lower magnitude

        const [mantissa, exponent] = value.split("/");

        result = parse(mantissa) / radix ** parse(exponent);

    } else if (value.includes("\\")) {          // raise magnitude

        const [mantissa, exponent] = value.split("\\");

        result = parse(mantissa) * radix ** parse(exponent);

    } else result = parse(value);               // direct mantissa

    if (integerMode && parse === float) return BigInt(Math.round(result));
    else return result;
}

const advance = function() {

    /* Advance the parser state by one token, always staying two steps
    ahead (the `parse` function advances an extra two times before it
    begins parsing to ensure all three globals are initialized). */

    CURRENT_TOKEN = NEXT_TOKEN;
    NEXT_TOKEN = FUTURE_TOKEN;
    FUTURE_TOKEN = TOKENS.next().value;

    return CURRENT_TOKEN;
};

const typecheck = function(token, ...types) {

    /* Take a token instance and one or more (token) classes, and return the
    token if it is of a given class (truthy), else `undefined` (falsey). */

    for (const type of types) if (token instanceof type) return token;
};

const boundscheck = function(identity, width=32, signed=false) {

    /* This helper takes an `identity` token, a `width` as a `Number` (which
    can be any valid width, and defaults to `32`) and a ternary named `signed`
    that is `true` for signed integers, `false` for unsigned, and `null` when
    the integer is sign-agnostic, defaulting to `false`. If `identity` is not
    a NumberLiteral, it is returned immediately. Otherwise, it is converted to
    a `BigInt`, then validated, using the arguments to define its range. It is
    assumed that `identity` is an integer (if it is a `NumberLiteral` at all),
    as floats just go to infinity, so are not boundschecked by the caller. If
    the value is in range, the original `identity` argument is returned, else
    an exception is raised. */

    if (identity instanceof Identifier) return identity;
    if (identity === undefined) return identity;

    let lower, upper;

    const e = 2n ** BigInt(width);
    const number = evaluateLiteral(identity, true);

    if (signed === true) [lower, upper] = [0n - e >> 1n, -1n + e >> 1n];
    else if (signed === false) [lower, upper] = [0n, e - 1n];
    else [lower, upper] = [0n - e >> 1n, e - 1n];

    if (number < lower || number > upper) {

        const issue = number < lower  ? "low" : "high";

        throw new BoundsError(identity, issue, width, signed);

    } else return identity;
};

const evaluate = function(token, ...values) {

    /* Return a bool indicating whether or not the given `token` has a `value`
    attribute string that matches one of the given `values` strings. */

    return token instanceof Token && values.includes(token.value);
};

const requirePrimitiveType = function(type) {

    /* This helper is used when a specific primitive type (like `s8`, `i32`
    or `utf8`) is required. It takes the type name as a string, and returns
    the Primitive instance if found, else raises an error. */

    if (not(evaluate(require(Primitive), type))) {

        const description = format("the `{0.s}`", type);

        throw new UnexpectedPrimitiveError(description, CURRENT_TOKEN);

    } else return CURRENT_TOKEN;
}

const on = function(...types) {

    /* Return the current token (truthy) if it is of a given type, else
    return `undefined` (falsey). */

    return typecheck(CURRENT_TOKEN, ...types);
};

const at = function(...types) {

    /* Return the next token (truthy) if it is of a given type, else return
    `undefined` (falsey). */

    return typecheck(NEXT_TOKEN, ...types);
};

const atToken = function(type, value) {

    /* Return the next token (truthy) if it is of a given type and has the
    given value, else return `undefined` (falsey). */

    if (at(type) && evaluate(NEXT_TOKEN, value)) return NEXT_TOKEN;
};

const accept = function(...types) {

    /* Advance and return the next token (truthy) if it is of a given type,
    else do not advance, and return `undefined` (falsey). */

    if (at(...types)) return advance();
};

const require = function(...types) {

    /* Advance and return the next token if it is of a given type, else
    raise the appropriate exception. */

    if (at(...types)) return advance();

    if (at(Indent)) throw new UnexpectedIndentError();

    let expected = types.map(type => type.name).join(" or ");

    if (expected === "Operation or Void") expected = "Instruction";

    throw new UnexpectedTokenError(expected, advance());
};

const atKeyword = function(keyword) {

    /* Return the next token, without advancing to it, if it is the keyword
    with the given name, else return `undefined`. */

    if (atToken(Keyword, keyword)) return NEXT_TOKEN;
};

const atValtype = function() {

    /* Return the next token, without advancing to it, if it a valtype, else
    return `undefined`. */

    if (not(at(Primitive, Qualifier))) return false;

    return [i32, i64, f32, f64, pointer, proxy].includes(NEXT_TOKEN.value);
};

const atReftype = function() {

    /* Return the next token, without advancing to it, if it a valtype, else
    return `undefined`. */

    if (not(at(Qualifier))) return false;

    return [pointer, proxy].includes(NEXT_TOKEN.value);
};

const acceptArrayName = function() {

    /* Accept and return the next token, if it is the `memory` or `table`
    component, else return `undefined`. */

    if (not(at(Component))) return;
    if (["memory", "table"].includes(NEXT_TOKEN.value)) return advance();
};

const acceptKeyword = function(keyword) {

    /* Advance and return the next token (truthy) if it is the keyword
    with the given spelling, else just return `undefined` (falsey). */

    if (atKeyword(keyword)) return advance();
};

const requireKeyword = function(keyword) {

    /* Check that the next token is the keyword with the given spelling. If
    so, advance and return the new token, else complain. */

    if (acceptKeyword(keyword)) return CURRENT_TOKEN;

    if (accept(Keyword)) throw new UnexpectedKeywordError(keyword);
    else throw new ExpectedKeywordError(keyword, advance());
};

const acceptQualifier = function(...qualifiers) {

    /* Advance and return the next token (truthy) if it is a qualifier
    with a given spelling, else just return `undefined` (falsey). */

    if (at(Qualifier) && evaluate(NEXT_TOKEN, ...qualifiers)) {

        return advance();
    }
};

const acceptPrefix = function(keyword, type) {

    /* This helper accepts a prefix construct (for example, `as i32`). If
    the given keyword is the next token, and the following token is of the
    correct type, this helper advances to the latter token, and returns it.
    The prefix being present makes the latter token required. If no prefix
    is found, `undefined` is returned. */

    if (acceptKeyword(keyword)) return require(type);
};

const requirePrefix = function(keyword, type) {

    /* This helper requires a prefix construct (for example, `as i32`). If
    the given keyword is the next token, and the following token is of the
    correct type, this helper advances to the latter token, and returns it.
    If no prefix is found, a complaint is raised. */

    if (requireKeyword(keyword)) return require(type);
};

const acceptMaxQualifier = function() {

    /* This helper returns the next token if it is the Operation token named
    `max`. This is used by the limits-parsing functions below, that overload
    `max` as a qualifier. */

    if (atToken(Operation, "max")) return advance();
};

const acceptLimits = function() {

    /* This helper accepts a limits definition for a memory or table. If a
    maximum is defined without an initial length, the helper complains, else
    it returns an array with the two number literal tokens (which may both be
    `undefined`), with the initial length followed by the maximum length. */

    let min = acceptPrefix("with", NumberLiteral);
    let max = acceptPrefix("to", NumberLiteral);

    if (max && not(min)) throw new InvertedLimitsError();
    else if (min && not(max) && acceptMaxQualifier()) return [min, min];
    else return [min, max];
};

const requireLimits = function() {

    /* This helper requires a limits definition for a memory or table, which
    must be present, but may or may not include a maximum length. It returns
    the two values as an array of number literal tokens, with the initial
    length followed by the maximum length or `undefined`. */

    const min = requirePrefix("with", NumberLiteral);

    if (acceptMaxQualifier()) return [min, min];
    else return [min, acceptPrefix("to", NumberLiteral)];
};

const requireFullLimits = function() {

    /* This helper requires a limits definition for a shared memory, which
    must be present, and must include a maximum length. It returns the two
    values as an array of number literal tokens, with the initial length
    followed by the maximum length. */

    const min = requirePrefix("with", NumberLiteral);

    if (acceptMaxQualifier()) return [min, min];
    else return [min, requirePrefix("to", NumberLiteral)];
};

const acceptValtype = function() {

    /* Accept and return a valtype token, else `undefined`. */

    if (atValtype()) return advance();
};

const requireValtype = function() {

    /* Require and return a valtype token, else complain. */

    if (atValtype()) return advance();
    else throw new UnexpectedTokenError("valtype", advance());
};

const acceptReftype = function() {

    /* Accept a reftype for a table element (one of `pointer` or `proxy`),
    else return `undefined`. */

    const qualifier = accept(Qualifier);

    if (qualifier && [pointer, proxy].includes(qualifier.value)) {

        return qualifier;
    }
};

const requireReftype = function() {

    /* Accept a reftype for a table element (one of `pointer` or `proxy`),
    else return `undefined`. */

    if (acceptReftype()) return CURRENT_TOKEN;
    else throw new UnexpectedTokenError("reftype", advance());
};

const acceptEncoding = function() {

    /* Accept any primitive type token that is a valid encoding for memory
    primers, then return it, else return `undefined`. */

    if (evaluate(NEXT_TOKEN, u8, u16, u32, u64, f32, f64, utf8)) {

        return advance();
    }
};

const requireGivenType = function(description, ...names) {

    /* This function takes a `description` string and zero or more primitive
    type names, also as strings. It returns a function that returns the next
    token, if it is of a given type, else complaining (passing `description`
    to the error constructor. */

    return function() {

        const token = accept(Primitive);

        if (token && names.includes(token.value)) return token;
        if (not(token)) throw new ExpectedPrimitiveError();
        else throw new UnexpectedPrimitiveError(description, token);
    };
};

const requireFloatType = requireGivenType(
    "a 32 or 64-bit, float",
    f32, f64
);

const requireNumtype = requireGivenType(
    "a 32 or 64-bit, float or agnostic integer",
    i32, i64, f32, f64
);

const requireGnosticNumtype = requireGivenType(
    "a 32 or 64-bit, float or gnostic integer",
    u32, s32, u64, s64, f32, f64
);

const requireIntegerNumtype = requireGivenType(
    "a 32 or 64-bit, agnostic integer",
    i32, i64
);

const requireGnosticIntegerNumtype = requireGivenType(
    "a 32 or 64-bit, gnostic integer",
    u32, s32, u64, s64
);

const requireGnosticWordType = requireGivenType(
    "the `s32` or `u32`",
    u32, s32
);

const requireDatatype = requireGivenType(
    "the `i8`, `i16` or `i32`",
    i8, i16, i32
);

const requireGnosticDatatype = requireGivenType(
    "an 8, 16 or 32-bit, gnostic integer",
    u8, s8, u16, s16, u32, s32
);

const requireLesserGnosticDatatype = requireGivenType(
    "an 8 or 16-bit, gnostic integer",
    u8, s8, u16, s16
);

const requireLesserDatatype = requireGivenType(
    "the `i8` or `i16`",
    i8, i16
);

const requireSignedDatatype = requireGivenType(
    "the `s8`, `s16` or `s32`",
    s8, s16, s32
);

const requireLesserSignedDatatype = requireGivenType(
    "the `s8` or `s16`",
    s8, s16
);

const requireUnsignedDatatype = requireGivenType(
    "the `u8`, `u16` or `u32`",
    u8, u16, u32
);

const requireLesserUnsignedDatatype = requireGivenType(
    "the `u8` or `u16`",
    u8, u16
);

const requireIdentities = stack(function(push) {

    /* This helper requires one or more identities, pushing each to the stack,
    complaining if none are found. The identities are not boundschecked, as it
    is left to the Node classes to validate bounds. */

    if (accept(Identity)) push(CURRENT_TOKEN);
    else throw new MislabelledExitError();

    while (accept(Identity)) push(CURRENT_TOKEN);
});

const requireOptionalIdentity = function(location) {

    /* This helper accepts an identity and returns it, else returning an
    implicit zero, with the given `location`, if no identity is found. */

    return accept(Identity) || new ImplicitNumber(0, location);
};

const requireTableQualifier = function() {

    /* Require a table qualifier (one of `pointer`, `proxy` or `mixed`), and
    return it, complaining otherwise. */

    const qualifier = require(Qualifier);

    if ([mixed, pointer, proxy].includes(qualifier.value)) return qualifier;
    else throw new InvalidTableQualifierError(qualifier);
};

const acceptComponent = function(...names) {

    /* Acccept the next token, if it has a given name, otherwise return
    `undefined`. */

    if (at(Component) && names.includes(NEXT_TOKEN.value)) return advance();
};

const requireComponent = function(...names) {

    /* Require that the next token has a given name, else complain. */

    if (acceptComponent(...names)) return CURRENT_TOKEN;
    else throw new UnexpectedComponentError(names);
};

const requireType = function(expression) {

    /* Require a type reference or a type expression (or signature, when the
    `expression` argument is falsey). Return whichever is found, complaining
    if neither is present. */

    return acceptTypeReference() || requireTypeExpression(expression);
};

const acceptTypeReference = function() {

    /* Accept a type reference, and return its identifier, or `undefined`,
    of no type reference is found. */

    if (not(atKeyword("type"))) return undefined;

    const location = requireKeyword("type").location;

    return new TypeReference(require(Identity), location);
};

const requireTypeExpression = function(signature) {

    /* This helper is used to gather a type expression (or signature, when
    the `expression` argument is falsey), then return it, complaining if
    neither is present. */

    const gatherTypes = stack(function(push) {

        /* This stack function gathers an array of types, which may be empty
        when `void` is found. This can be used for the arity or results of a
        type (but not for identifiable params - see below). */

        const done = function() {

            /* This helper is used to determine whether to gather another
            type (or return). It ensures that `gatherTypes` will not be
            confused by a comma used to group instructions after an in-
            struction that ends with a type expression (that does not
            have void results):

                invoke i32 -> i32, i32, add i32

            This is required to avoid an edgecase, where `invoke` can only
            have instructions nested after it in some situations and not
            others. */

            return not(at(Comma)) || typecheck(FUTURE_TOKEN, Operation);
        };

        if (not(accept(Void))) while (true) {

            push(new ArityElement(requireValtype()));

            if (done()) { return } else advance();
        }
    });

    const gatherParameters = stack(function(push) {

        /* This stack function gathers an array of identifiable params, which
        may be empty when `void` is found. */

        let type, typed, helper;

        if (not(accept(Void))) while (true) {

            type = (typed = acceptValtype()) || type;
            helper = typed ? accept : require;

            if (not(type)) throw new UntypedParameterError();
            else push(new ParamElement(type, helper(Identifier)));

            if (at(Comma)) { advance() } else return;
        }
    });

    const location = NEXT_TOKEN.location;
    const arity = signature ? gatherTypes() : gatherParameters();

    require(SkinnyArrow);

    return new TypeExpression(arity, gatherTypes(), location);
};

const requireLocals = function(parent) {

    /* Gather one line of locals definitions, pushing each to the parent
    node argument. This helper is called on the `local` keyword. When it
    is done, it checks for, consumes and returns the line-terminator. */

    let type, typed;

    advance();

    while (true) {

        type = (typed = acceptValtype()) || type;

        const identifier = (typed ? accept : require)(Identifier);
        const location = typed ? typed.location : identifier.location;

        if (not(type)) throw new UntypedLocalError();
        else parent.locals.push(
            new LocalDefinition(type, identifier, location)
        );

        if (at(Comma)) advance();
        else return require(Terminator);
    }
};

const requireBlock = function(...args) {

    /* This helper just decides whether to parse the require block as inline
    or indented, based on whether the next token is the `thus` keyword, and
    passing any arguments along, before returning the result. */

    if (acceptKeyword("thus")) return requireInlineBlock(...args);
    else return requireIndentedBlock(...args);
};

const resolveInstruction = function() {

    /* This helper is used to parse the operators that begin instructions,
    handling the `atomic` (and soon the `simd`) prefix. It also checks to
    ensure that the prefix is valid for the operator. The helper returns
    the instruction class and the operator token. */

    const atomize = acceptQualifier(atomic);
    const operation = accept(Operation);

    if (atomize) {

        const Class = instructions.atomic[operation.value];

        if (Class) return [Class, operation];
        else throw new AtomicInstructionError(operation);

    } else return [instructions[operation.value], operation];
};

const requireInlineBlock = function(parent, expression=false) {

    /* This helper is called on the `thus` keyword before an inline-block.
    It takes a `parent` node (a`FunctionDefinition` or `BlockInstruction`
    instance), and gathers a block of instructions, pushing each to the
    `parent.block` array. The `expression` argument is passed to the
    instruction constructor, and handled there. */

    while (not(at(Terminator, Indent))) {

        const [Class, token] = resolveInstruction();
        const block = Class.prototype instanceof BlockInstruction;

        if (block) throw new UnexpectedInlineBlockError();

        parent.block.push(new Class(token, expression));

        if (accept(Comma)) continue;
        else return parent;

    } throw new ExpectedInlineBlockError();
};

const requireIndentedBlock = function(parent, expression=false) {

    /* This helper takes a `parent` node (which will be a `FunctionDefinition`
    or `BlockInstruction`). It gathers an indented block, pushing each to the
    `parent.block`. The helper is called on the last token of the parent (of
    the block header). If the optional `expression` argument is truthy, only
    instructions permitted in constant expressions are allowed.

    Note: This function is always initially called by `definitions.function`,
    and then any recursive call will be made by `BlockInstruction.parse`. */

    require(Indent);

    if (parent instanceof FunctionDefinition) { // first, gather any locals...

        while (atToken(Qualifier, local)) requireLocals(parent);
    }

    while (true) { // then, (recursively) gather a block of instructions...

        const [Class, token] = resolveInstruction();

        if (Class === Else) throw new UnexpectedElseError();

        const instruction = new Class(token, expression);

        parent.block.push(instruction);

        if (accept(Dedent)) return parent;

        if (not(instruction instanceof BlockInstruction)) require(Delimiter);
    }
};

const requireFunctionSpecifier = function() {

    /* Require a function specifier, then return its start flag, any bound
    identifier (or `undefined`), and the function type, as a three element
    array: [start, identifier, type]. The function also checks and updates
    the global `START` boolean as required, and throws an exception if the
    current module defines more than one start function. */

    let identifier = undefined;

    if (acceptKeyword("start")) {

        const location = CURRENT_TOKEN.location;
        const type = new TypeExpression([], [], location);

        if (START) throw new MultipleStartFunctionsError(location);
        else START = true;

        requireComponent("function");

        return [true, accept(Identifier), type];
    }

    if (atToken(Component, "function")) advance();
    else identifier = require(Identifier);

    requireKeyword("of");

    return [false, identifier, requireType(false)];
};

const requireMemoryElement = function(push, context, newline) {

    /* This helper gathers a memory element (from a memory primer). These
    elements must always specify its encoding (explicitly or inherited). */

    const type = acceptEncoding();

    if (newline && not(type)) throw new BrokenDirectiveError(advance());

    context = type || context;

    if (not(context)) throw new UnspecifiedElementError("memory");

    if (context.value === "utf8") {

        push(new MemoryElement(context, type, require(StringLiteral)));

    } else push(new MemoryElement(context, type, require(NumberLiteral)));

    return context;
};

const requireTableElement = function(push, context, newline) {

    /* This helper gathers a table element (from a primer for a pointer table
    or pointer bank), which must always specify the element type (explicitly
    or inherited), currently always `pointer`, but this will be expanded in
    future. */

    const type = atToken(Qualifier, "pointer") ? advance() : undefined;

    if (newline && not(type)) throw new BrokenDirectiveError(advance());

    if (not(context = type || context)) {

        throw new UnspecifiedElementError("table");
    }

    const token = acceptKeyword("null") || require(Identity);

    push(new TableElement(context, type, token));

    return context;
};

const requirePrimer = function(name, bank) {

    /* This helper gathers and returns a primer for a memory or table. It will
    ensure that each element specifies its type (directly or inherited from a
    previous element). The first argument (`name`) is a string that is one of
    "memory" or "pointer" ("mixed" and "proxy" may be supported later, if the
    specification supports primers for those table types). The argument `bank`
    is a bool that indicates whether the primer belongs to a bank or not. */

    const push = item => segment.push(item);

    let [type, segment] = [undefined, []];

    const segments = [segment];
    const inline = acceptKeyword("thus");
    const parsers = [requireTableElement, requireMemoryElement];
    const requireElement = parsers[1 * (name === "memory")];

    requirePrimerStarter(inline, name);

    while (true) {

        if (not(on(Comma)) && acceptKeyword("segment")) {

            if (inline) throw new UnexpectedInlineBlockError(advance());
            else if (bank) throw new SegmentedBankError();
            else if (segment.length === 0) segment.push(new SegmentElement());
            else segments.push(segment = [new SegmentElement()]);

            type = undefined;
        }

        type = requireElement(push, type, not(on(Comma)));

        if (inline ? at(Terminator) : accept(Dedent)) return segments;
        else require(Delimiter);
    }
};

const requireOptionalPrimer = function(...args) {

    /* This helper wraps `requirePrimer` to make the primer lexically optional,
    but internally required (the helper always returns an array, though it may
    be implicitly empty). */

    return at(Terminator) ? [] : requirePrimer(...args);
};

const requirePrimerStarter = function(inline, context) {

    /* This helper is used by indented primer parsing functions to validate
    their blocks begin correctly. The `inline` argument is a bool that lets
    the helper know if the primer is inline or indented. The `context` arg
    is a string (either "memory" or "table") ), and is used in errors when
    inline primers end unexpectedly. */

    if (inline) {

        if (accept(Terminator, Indentation)) {

            throw new ExpectedInlinePrimerError(context);
        }

    } else require(Indent);
};

const nameNextComponent = function(description) {

    /* The parser methods that handle specifiers and definitions all defer to
    helpers, based on the type of component that is being parsed. While valid
    code ensures that the next token will always provide enough information to
    infer which helper to defer to (and when to throw an error), it is quite a
    complex predicate. This helper peeks at the next token, and if it is valid,
    returns the component name ("function", "variable", "constant", "memory",
    "table" or "type"). The argument is a string ("specifier" or "definition")
    used for ensuring "type" is only returned for definitions, and to create
    error messages when required. */

    const value = NEXT_TOKEN.value;

    if (at(Identifier)) {

        return "function";

    } else if (atToken(Keyword, "start") || atToken(Component, "function")) {

        return "function";

    } else if (at(Component) && ["variable", "constant"].includes(value)) {

        return value;

    } else if (atToken(Component, "memory") || atToken(Qualifier, shared)) {

        return "memory";

    } else if (at(Qualifier) && [mixed, pointer, proxy].includes(value)) {

        return "table";

    } else if (description === "definition" && atToken(Keyword, "type")) {

        return "type";
    }

    if (value === "table") throw new UnqualifiedTableError();
    else throw new ExpectedComponentError(description, NEXT_TOKEN);
};

const nameInstruction = function(instruction, full=false) {

    /* This helper takes an instruction node, and returns its name as a
    string. The name will be written in full (`foo-instruction`) if `full`
    is truthy, and without the suffix otherwise. */

    const suffix = full ? "-instruction" : "";

    return instruction.constructor.name.toLowerCase() + suffix;
};

const reset = function(configuration) {

    /* This is the generic reset helper for this module. It resets
    the parser state, ready for a new source. */

    URL = configuration.url;
    TOKENS = lex(configuration);
    [CURRENT_TOKEN, NEXT_TOKEN] = [undefined, undefined];
    [GLOBAL_CONTEXT, START] = [true, false];
};

/* --{ THE PARSER ENTRYPOINT }---------------------------------------------- */

export const parse = function * (configuration) {

    /* This generator is the netrypoint for the PHANTASM parser. It takes
    a configuration hash, parses the given source into an AST, and yields
    the nodes of the result, statement-wise. */

    reset(configuration);
    advance(); advance(); // initialize the current, next and future token

    while (require(Keyword, Terminator, EOF) && not(on(EOF))) {

        if (on(Terminator)) continue;
        else yield Statement.parse();

        if (accept(Terminator)) continue;
        else throw new SuperfluousTokenError(advance());
    }
};

export default parse;
