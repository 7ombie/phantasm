/* --{ THE PHANTASM COMPILER }--{ /assembler/compiler.js }------------------- *

This module implements the PHANTASM compiler, exporting a function named
`compile` as an entrypoint. */

import { not, iife, stack } from "/assembler/helpers.js";

import {
    format, encodeUTF8, Node, Identifier, Keyword, NumberLiteral,
    Primitive, Void, PhantasmError
} from "/assembler/lexer.js";

import {
    parse, evaluateLiteral,
    Instruction, BlockInstruction,
    TypeReference, TypeExpression, TypeDefinition,
    DefineStatement, ImportStatement, ExportStatement,
    ParamElement, SegmentElement, MemoryElement, TableElement,
    RegisterReference, FunctionReference, MemoryReference, TableReference,
    RegisterSpecifier, FunctionSpecifier, MemorySpecifier, TableSpecifier,
    RegisterDefinition, FunctionDefinition, MemoryDefinition, TableDefinition
} from "/assembler/parser.js";

/* --{ THE GLOBAL COMPILER STATE }------------------------------------------ */

let SOURCE, URL, INDEXSPACES, SECTIONS;

/* --{ USEFUL GLOBAL CONSTANTS }-------------------------------------------- */

const header = [
    0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00
];

const opcodes = {
    ref: {null: 0xD0, func: 0xD2},
    get: {global: 0x23, local: 0x20},
    const: {i32: 0x41, i64: 0x42, f32: 0x43, f64: 0x44}
};

const encodings = {
    function: 0x00, table: 0x01, memory: 0x02, register: 0x03,
    i32: 0x7F, i64: 0x7E, f32: 0x7D, f64: 0x7C,
    pointer: 0x70, proxy: 0x6F, mixed: 0x6E,
    type: 0x60, empty: 0x40, end: 0x0B
};

const sectionIDs = [1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 10, 11, 0];

const views = {
    u8: Uint8Array, u16: Uint16Array, u32: Uint32Array,
    u64: BigInt64Array, f32: Float32Array, f64: Float64Array,
};

/* --{ THE COMPILER ERROR CLASSES }----------------------------------------- */


class CompilerError extends PhantasmError {

    /* The abstract base class for all compiler errors. */

    constructor(node, text) {

        /* The `node` argument is the offending token, and the `text`
        argument contains the error message. */

        super(URL, node.location.line, node.location.column, text);
    }
}

class DuplicateTypeError extends CompilerError {

    /* Thrown when an explicitly defined type is a duplicate of another. */

    constructor(node) {

        /* The `node` argument is the offending `TypeDefinition` instance. */

        super(node, "Duplicate function types are not permitted.");
    }
}

class DuplicateIdentifierError extends CompilerError {

    /* Thrown when the user attempts to bind an identifier that is a
    duplicate of another identifier in the same indexspace. */

    constructor(node) {

        const template = "Reassigning an identifier (`${0.v}`) is illegal.";

        super(node, format(template, node));
    }
}

class DuplicateLabelError extends CompilerError {

    /* Thrown when the user attempts to bind a label that is a duplicate
    of another label within the same scope. */

    constructor(node) {

        const template = "Cannot rebind a label (`${0.v}`) within a scope.";

        super(node, format(template, node));
    }
}

class UnboundIdentifierError extends CompilerError {

    /* Thrown when the user attempts to reference an identifier that does
    not exist in the appropriate indexspace. */

    constructor(type, node) {

        /* The `type` argument is the name of the indexspace as a string,
        and the `node` argument is the offending identifier token. */

        const template = "The identifier `${1.v}` is not bound to a {0.s}."

        super(node, format(template, type, node));
    }
}

class UnboundLabelError extends CompilerError {

    /* Thrown when the user attempts to reference a label with an
    identifier that has not been bound to a (local) label. */

    constructor(node) {

        const template = "The given label (`${0.v}`) is not in scope."

        super(node, format(template, node));
    }
}

class UnboundIndexError extends CompilerError {

    /* Thrown when the user attempts to reference an index that is
    not bound to a component. */

    constructor(type, node) {

        /* The `type` argument is the name of the indexspace as a string,
        and the `node` argument is the offending number literal token. */

        const template = "The index `{1.v}` is not bound to a {0.s}."

        super(node, format(template, type, node));
    }
}

class LabelIndexError extends CompilerError {

    /* Thrown when the user attempts to target a block with an index
    that is greater then the depth of the instruction. */

    constructor(node) {

        /* The `node` argument is the number literal token that expresses
        the offending index. */

        const template = "The given block index ({0.V}) is too high."

        super(node, format(template, node));
    }
}

/* --{ THE LOCAL HELPER CLASSES }------------------------------------------- */

class Identity {

    /* This class is used in various places within the compiler to represent
    an identity (lexically, a number literal or an identifier that expresses
    a reference to a component by index) in an array of compiled bytes. Then,
    the `VectorSection.compile` method will compile each `Identity` instance
    to the bytes that encode the index (as it combines everything to compile
    the final output for a given section), once all of the indices have been
    finalized. */

    constructor(type, identity) {

        /* This constructor takes a component type as a string (as a key for
        the pair of hashes in `INDEXSPACES`), and an identity node (a number
        literal or identifier node), and simply stashes them for later. */

        this.type = type;
        this.identity = identity;
    }

    get bytes() {

        /* This computed property evaluates to the bytes required to encode
        the identity, by first resolving the identity (now that the indices
        have all been assigned) to an index, then Unsigned LEB128 encoding
        the result to an array of (`Number`) bytes, which is returned. */

        return ULEB128(resolveIdentity(this.type, this.identity));
    }
}

class Segment {

    /* A class for representing the state associated with a segment from a
    memory or table primer, or a bank. The parser just returns an array of
    segment arrays, which get bound to the `primer` attribute of whichever
    component the segment belongs to. This class restructures the data, so
    it can be passed into whatever section does the actual encoding. */

    constructor(segment) {

        /* This constructor stashes the segment (as `this.elements`), then
        initializes the `explicit` attribute to `false`, making it always
        `false` for banks, and leaving primers to change it as required. */

        this.elements = segment;
        this.explicit = false;
    }

    get expression() {

        /* This computed property evaluates to an array of bytes that encode
        the constant expression that locates the segment. When present, the
        explicit `segment` directive is encoded, else a `push i32 0` block
        is synthesized and returned instead.

        Note: This method is not used by banks (only primer segments). */

        const i32 = n => [opcodes.const.i32, ...SLEB128(n, 32), encodings.end];

        if (this.explicit) {

            const block = this.elements[0].block;

            if (block[0] instanceof NumberLiteral) return i32(block[0]);
            else return SECTIONS[10].encodeExpression(block);

        } else return i32(0);
    }

    get payload() {

        /* This computed attribute evaluates to an array containing all of
        the elements in the segment (excluding the initial segment-directive,
        when present). The elements are still represented as abstract nodes
        (not as bytes) at this point, ready to be encoded by the appropriate
        `encode` method (`DataSection.encode` or `ElementSection.encode`). */

        return this.elements.slice(1 * this.explicit);
    }
}

class ArraySegment extends Segment {

    /* This is a base class for memory and table segments (not banks). */

    constructor(index, segment, id) {

        /* This constructor takes the index of the parent memory or table,
        the segment that the class abstracts (an array of elements), and a
        section ID (either `9` or `11` - Element Section or Data Section).
        The method passes the segment to the base class (`Segment`), then
        stashes the index, notes whether this segment is explicitly located,
        before passing the instance on to the section that encodes it. */

        super(segment);
        this.index = index;
        this.explicit = segment[0] instanceof SegmentElement;
        SECTIONS[id].append(this);
    }
}

class MemorySegment extends ArraySegment {

    /* This helper class represents a segment from a memory primer (not a
    bank), which must be encoded within the Data Section (after any memory
    banks). */

    constructor(index, segment) {

        /* This constructor passes the given index and segment to `super`,
        with the ID for the Data Section (`11`). */

        super(index, segment, 11);
    }
}

class TableSegment extends ArraySegment {

    /* This helper class represents a segment from a table primer (not a
    bank), which must be encoded within the Element Section (after any
    table banks). */

    constructor(index, segment) {

        /* This constructor passes the given index and segment to `super`,
        with the ID for the Element Section (`9`). */

        super(index, segment, 9);
    }
}

class MemoryBankSegment extends Segment {

    /* This helper class represents a memory bank, which is encoded to a
    single segment in the Data Section (before any primer segments). */

    constructor(segment) {

        /* This constructor passes the only segment of the primer to the
        parent constructor (allowing this instance to be processed like a
        regular segment), before passing the instance to the Data Section. */

        super(segment[0]);
        SECTIONS[11].append(this);
    }
}

class TableBankSegment extends Segment {

    /* This helper class represents a table bank, which is encoded to a
    single segment in the Element Section (before any primer segments). */

    constructor(segment) {

        /* This constructor passes the only segment of the primer to the
        parent constructor (allowing this instance to be processedlike a
        regular segment), before passing the instance to the Element
        Section. */

        super(segment[0]);
        SECTIONS[9].append(this);
    }
}

/* --{ THE ABSTRACT BASE CLASSES FOR THE BINARY SECTIONS}------------------- */

class DatumSection {

    /* This is an abstract base class for those sections in the binary format
    which just define a single value as the payload (basically, the Start and
    Data Count sections). */

    constructor(id) {

        this.id = id;                   // the section ID
        this.payload = undefined;       // the payload value
    }

    compile() {

        /* This method compiles the instance to a complete section, including
        the section ID, its length in bytes and the payload, which will always
        be an Unsigned LEB128 encoded integer in practice. */

        if (this.payload === undefined) return []; // omit section, if unused

        const payload = ULEB128(this.payload);
        const bytes = ULEB128(payload.length);

        return [this.id].concat(bytes).concat(payload);
    }
}

class VectorSection {

    /* This is an abstract base class for those sections in the binary format
    which define a vector of items (every section, except for the Start and
    Data Count sections). Derived classes must define an `encode` method
    that can be invoked by the `append` method below. */

    constructor(id) {

        this.id = id;       // the section ID
        this.items = [];    // accumulates the items of the vector
        this.payload = [];  // accumulates the bytes of the encoded payload
    }

    append(item) {

        /* This method takes an item (statement or component etc), pushes it
        to the `items` array, and invokes the `encode` method of the derived
        class, which is responsible for encoding the item, then pushing each
        resulting byte to the `payload` array. */

        this.items.push(item);
        this.encode(item);
    }

    push(...bytes) {

        /* This method concatenates any number of argument bytes (represented
        as numbers between `0` and `255`) to the `payload` array, updating it
        in place. */

        this.payload = this.payload.concat(bytes);
    }

    pushVector(array, callback, bytewise=true) {

        /* This method takes an array and a callback, and encodes the array by
        passing each of its items through the callback, which returns an array
        of results. The results are flattened, before everything is encoded as
        a vector, then pushed to the `payload` array. The optional third argu-
        ment (`bytewise`) is a bool that determines whether the length of the
        vector will be the number of bytes in the compiled result (`true`) or
        the number of items in the input array (`false`). */

        const payload = array.map(item => callback(item)).flat();
        const length = bytewise ? payload.length : array.length;

        this.push(...ULEB128(length), ...payload);
    }

    pushExpression(block) {

        /* This method takes a `block` array containing a constant expression,
        and encodes it, updating the `payload` array. */

        this.push(...SECTIONS[10].encodeExpression(block));
    }

    pushUTF8(literal) {

        /* This method takes a `StringLiteral` token instance, Unsigned LEB128
        encodes the length of the string (in UTF-8 bytes), then pushes both the
        length of the string and its UTF-8 bytes to the `payload` array. This
        is how name strings are represented in the binary format. */

        const bytes = encodeUTF8(literal.value);

        this.push(...ULEB128(bytes.length));
        this.push(...bytes);
    }

    pushLimits(component, shared=false) {

        /* This method takes a component with `min` and `max` attributes that
        describe the limits of a memory or table, as well as an optional bool
        that is `true` for shared limits, and `false` otherwise. This method
        encodes the limits, then pushes the result to the `payload` array. */

        if (not(component.max)) this.push(0x00, ...ULEB128(component.min));
        else {

            this.push(shared ? 0x03 : 0x01);
            this.push(...ULEB128(component.min), ...ULEB128(component.max));
        }
    }

    compile() {

        /* This method compiles the instance to a complete section, including
        the section ID, the length (bytewise), and the payload vector. */

        if (this.items.length === 0) return []; // omit any empty sections

        const encode = item => item instanceof Identity ? item.bytes : item;

        const payload = this.payload.map(encode).flat();
        const vLength = ULEB128(this.items.length);
        const bLength = ULEB128(vLength.length + payload.length);

        return [this.id].concat(bLength).concat(vLength).concat(payload);
    }
}

/* --{ THE CONCRETE CLASSES FOR THE BINARY SECTIONS}------------------------ */

class StartSection extends DatumSection {

    /* This concrete class inherits everything it needs to implement the
    Start Section, where the payload is just a function index. */
}

class DataCountSection extends DatumSection {

    /* This class implements the DataCount Section, which stores a count of
    the items in the Data Section. */

    constructor(id) {

        super(id);
        this.payload = 0;
    }

    append(segment) {

        /* This method ignores it argument, but accepts one to be consistent
        with the `VectorSection.append` method. It increments the data count
        each time it is called. */

        this.payload++;
    }
}

class TypeSection extends VectorSection {

    /* A singleton class that implements the Type Section, which is a vector
    of type defintions. */

    constructor(id) {

        super(id);
        this.types = {}; // map each unique type expression to its type index
    }

    static serializeTypeExpression(type) {

        /* This static method takes a type expression node, serializes it in a
        deterministic way that is unique for each distinct type, then returns
        the resulting string. This is used to check whether the given type
        expression expresses a unique type. */

        const encode = param => param.type.value;
        const params = type.params.map(encode);
        const results = type.results.map(encode);

        return params.concat(["->"]).concat(results).join("");
    };

    static referenceType(reference, byIndex=false) {

        /* This method takes a type (either a reference or expression), then
        resolves it, and returns the `TypeExpression` node of the referenced
        type definition by default, or its index when the `byIndex` argument
        is truthy (assuming that everything is valid). If the reference uses
        an undefined identity or an index for an implicitly defined type, an
        exception is raised. */

        const index = resolveIdentity("type", reference.identity);
        const type = INDEXSPACES.components.type[index];

        if (type instanceof TypeDefinition) {

            return byIndex ? index : type.type;

        } else if (reference.identity instanceof Identifier) {

            throw new UnboundIdentifierError("type", reference.identity);

        } else throw new UnboundIndexError("type", reference.identity);
    };

    resolveType(component) {

        /* This method is used to resolve the type of a function specifier or
        definition, or any of the various instructions that are able to use a
        type reference or type expression to express their types.

        This method takes a component node and resolves its `type` attribute,
        returning the (possibly new) type index. If a type reference is used,
        the result is checked to ensure that the type was explicitly defined
        (not implicitly defined (by this method) for an earlier function or
        instruction), and raises an error if not. */

        if (component.type instanceof TypeExpression) {

            const type = TypeSection.serializeTypeExpression(component.type);

            if (type in this.types) return this.types[type];

            const index = registerComponent("type", component, false);

            this.pushType(component.type, type, index);
            this.items.push(component);

            return index;

        } else return TypeSection.referenceType(component.type, true);
    }

    pushType(type, string, index) {

        /* This method takes a type expression, the serialized representation
        of the expressed type (as returned by `serializeTypeExpression`), and
        its index (within the `type` indexspace). The helper encodes the type,
        pushing the bytes to the `payload` array, while noting the expressed
        type in the `types` hash. */

        this.push(encodings.type);
        this.pushVector(type.params, token => encodings[token.type.value]);
        this.pushVector(type.results, token => encodings[token.type.value]);
        this.types[string] = index;
    }

    encode(statement) {

        /* This method takes a statement that defines a new type. It updates
        the section instance accordingly, registering any identifier and the
        type, then pushing the encoded type to the `payload` array. */

        const component = statement.component;
        const string = TypeSection.serializeTypeExpression(component.type);

        if (string in this.types) throw new DuplicateTypeError(component);
        else this.pushType(component.type, string, component.index);
    }
}

class ImportSection extends VectorSection {

    /* A singleton class that implements the Import Section, which is a vector
    of component imports. */

    encode(statement) {

        /* This method takes an import-statement, encodes its module and field
        names, and passes the statement to the method (below) that corresponds
        to the component type (and that method handles the actual encoding). */

        this.pushUTF8(statement.modulename);
        this.pushUTF8(statement.fieldname);
        this["push_" + statement.component.name](statement);
    }

    push_function(statement) {

        /* This method takes a statement that imports a function. It encodes
        the function, updating the `payload` array, and updating the Start
        Section where required. */

        const component = statement.component;

        this.push(0x00, ...ULEB128(SECTIONS[1].resolveType(component)));

        if (component.start) SECTIONS[8].payload = component.index;
    }

    push_table(statement) {

        /* This method takes a statement that imports a table, encodes it, and
        pushes the result to the `payload` array. */

        this.push(0x01, encodings[statement.component.type.value]);
        this.pushLimits(statement.component);
    }

    push_memory(statement) {

        /* This method takes a statement that imports a memory, encodes it,
        and pushes the result to the `payload` array. */

        this.push(0x02);
        this.pushLimits(statement.component, statement.component.shared);
    }

    push_register(statement) {

        /* This method takes a statement that imports a register, encodes it,
        and pushes the result to the `payload` array. */

        this.push(0x03, encodings[statement.component.type.value]);
        this.push(Number(not(statement.component.constant)));
    }
}

class ExportSection extends VectorSection {

    /* A singleton class that implements the Export Section, which is a vector
    of exports, each encoded to its fieldname, component type and identity. */

    encode(statement) {

        /* This method takes an export statement, and encodes it, updating the
        `payload` array. */

        const {name, identity} = statement.component;

        this.pushUTF8(statement.fieldname);
        this.push(encodings[name], new Identity(name, identity));
    }
}

class FunctionSection extends VectorSection {

    /* A singleton class that implements the Function Section, a vector of
    type indicies, representing the function indexspace, with each function
    represented by its type (its locals and instructions are stored in the
    Code Section). */

    encode(statement) {

        /* This method encodes a function definition statement, updating the
        `payload` array with the function type, before passing the statement
        on to `CodeSection.append` to encode the locals and instructions. */

        this.push(...ULEB128(SECTIONS[1].resolveType(statement.component)));
        SECTIONS[10].append(statement);
    }
}

class GlobalSection extends VectorSection {

    /* A singleton class that implements the Global Section, which is a vector
    of registers, encoded to their type and constant expression initializer. */

    encode(statement) {

        /* This method takes a register definition statement, and encodes it,
        updating the `payload` array. The given statement will always include
        a constant expression, whether it is defined implicitly (and passed to
        `encodeInitializer`) or explicitly (and passed to `pushExpression`). */

        const block = statement.component.block;

        this.push(encodings[statement.component.type.value]);
        this.push(Number(not(statement.component.constant)));

        if (block[0] instanceof Instruction) this.pushExpression(block);
        else this.encodeInitializer(statement.component);
    }

    encodeInitializer(component) {

        /* This method takes a register definition that either has an implicit
        initializer, or uses the `as` prefix (instead of an explicit constant
        expression). The parser represents this sugar (in the `block` array)
        with tokens that are distinct from actual instructions.

        The method looks at the given component (especially the token stored
        in `block[0]`) to figure out which instruction is being implied, and
        encode it, before appending the `end` pseudo-instruction to finalize
        the implied constant expression.

        A register with an implicit initializer stores its valtype: Numtypes
        imply a zero constant, while reftypes imply null:

            define constant i32         push i32 0          i32.const 0
            define constant i64         push i64 0          i64.const 0
            define constant f32         push f32 0          f32.const 0
            define constant f64         push f64 0          f64.const 0
            define constant pointer     push null pointer   ref.null func
            define constant proxy       push null proxy     ref.null extern

        Numtype registers with an explicit initializer (which is expressed as
        a `NumberLiteral`) store the literal token:

            define constant i32 as 1      push i32 1        i32.const 1
            define constant i64 as 2      push i64 2        i64.const 2
            define constant f32 as 3.4    push f32 3.4      f32.const 3.4
            define constant f64 as 5.6    push f64 5.6      f64.const 5.6

        Pointer registers with an explicit initializer (which is expressed as
        an identity) store the `NumberLiteral` or `Identifier` instance. This
        implies a `ref.func` operation (excepting unbound identifiers):

            define constant pointer as 1    push pointer 1      ref.func 1
            define constant pointer as $p   push pointer $foo   ref.func $foo

        Proxy registers cannot use the `as` keyword, as there is nothing to
        imply with a number literal, identifier, type *et cetera* that would
        meaningfully express a proxy.

        Note: The parser already validated the instruction (in terms of its
        register type and implied instruction). */

        const encoders = {
            i32: n => SLEB128(n, 32), i64: n => SLEB128(n, 64),
            f32: n => IEEE754(n, 32), f64: n => IEEE754(n, 64),
            pointer: ULEB128,
        };

        const instruction = component.block[0];
        const valtype = component.type.value;
        const encode = encoders[valtype];

        if (instruction instanceof Primitive) {

            this.push(opcodes.const[valtype], ...encode(0));

        } else if (instruction instanceof Identifier) {

            const index = resolveIdentifier("function", instruction);

            this.push(opcodes.ref.func, ...ULEB128(index));

        } else if (instruction instanceof NumberLiteral) {

            if (valtype === "pointer") this.push(opcodes.ref.func);
            else this.push(opcodes.const[valtype]);

            this.push(...encode(instruction));

        } else this.push(opcodes.ref.null, encodings[valtype]);

        this.push(encodings.end);
    }
}

class CodeSection extends VectorSection {

    /* A singleton class that implements the Code Section, which is a vector
    of code entries, each encoding to a vector of its locals and its constant
    expression (that together represent the function implementation).

    This class includes a static generator method for encoding any instruction,
    and another for encoding a constant expression (a block of instructions),
    both yielding the encoded byte-stream.

    This class also implements the methods that compile each of the individual
    instructions. */

    constructor(id) {

        super(id);
        this.index = 0;             // the current function index
        this.localIndex = 0;        // the current local index
        this.locals = {};           // maps identifiers to local indices
        this.labels = [];           // stack that tracks the current labels
    }

    resolveLocal(identity) {

        /* This generator takes a local, and returns its index, assuming that
        it is currently within scope, throwing an exception otherwise. */

        if (identity instanceof NumberLiteral) {

            const index = evaluateLiteral(identity);

            if (index < this.localIndex) return index;
            else throw new UnboundIndexError("local register", identity);

        } else {

            const local = this.locals[identity.value];

            if (local !== undefined) return this.locals[identity.value];
            else throw new UnboundIdentifierError("local register", identity);
        }
    }

    resolveLabel(label) {

        /* This generator takes a label, and returns its index, assuming that
        it is currently within scope, throwing an exception otherwise. */

        if (label instanceof NumberLiteral) {

            if (evaluateLiteral(label) < this.labels.length) return label;
            else throw new LabelIndexError(label);

        } else if (this.labels.includes(label.value)) {

            return this.labels.length - this.labels.indexOf(label.value) - 1;

        } else throw new UnboundLabelError(label);
    }

    * encodeInstruction(instruction) {

        /* This method takes an instruction, and passes it to the appropriate
        method (bound to the instance of this class) for the given mnemonic,
        yielding each of the bytes that are yielded by that method. */

        yield * SECTIONS[10][instruction.constructor.name](instruction);
    }

    * encodeExpression(block) {

        /* This static helper method takes a block of instructions, encodes it
        to a constant expression, then yields each of the resulting bytes,
        including the byte for the `end` pseudo-instruction. */

        yield * block.map(function(instruction) {

            return Array.from(SECTIONS[10].encodeInstruction(instruction));

        }).flat().concat([encodings.end]);
    }

    * GETSET(instruction, set) {

        /* This helper is used by `GET` and `SET`. It takes the instruction to
        be encoded, and a bool that must be `true` for `set` instructions, and
        `false` for `get` instructions. */

        const {scope, identity} = instruction;

        if (scope.value === "local") {

            yield 0x20 + set;
            yield * ULEB128(this.resolveLocal(identity));

        } else if (scope.value === "global") {

            yield 0x23 + set;
            yield new Identity("register", identity);

        } else {

            yield 0x25 + set;
            yield new Identity("table", identity);
        }
    }

    * ISNOT(instruction, options) {

        /* This helper is used by `IS` and `NOT` (except when `is null`). It
        takes a reference to the instruction and a hash of options that maps
        each *test* ("more", "equal", "zero" *et cetera*) to a hash that has
        a pair of arrays, named `types` and `codes`, as its attributes.

        The opcode is returned, using the `test` and `type` properties of the
        instruction to map the index of the type (in the `types` array) to the
        opcode in the `codes` array, based on the test that the instruction
        performs. See `IS` and `NOT` for more information. */

        const option = options[instruction.test.value];

        yield option.codes[option.types.indexOf(instruction.type.value)];
    }

    * GROWFILLSIZE(instruction, opcode) {

        /* This helper is used by `GROW`, `FILL` and `SIZE` to encode the form
        common to those instructions that uses the 0xFC prefix and an Unsigned
        LEB128 encoded opcode, with a memory or table index. */

        const type = instruction.component.value;
        const identity = instruction.identity;

        yield * [0xFC, ...ULEB128(opcode), new Identity(type, identity)];
    }

    * ATOMICS(instruction, opcode) {

        /* This helper is used by all of the regular atomic instructions. It
        takes a reference to the instruction, and the opcode for its `i32`
        variant (the remaining opcodes are sequential and orderly). The
        compiled instruction is yielded bytewise. */

        const opcodes = {
            i32: [opcode, 0x02], i64: [opcode + 1, 0x03],
            i32u8: [opcode + 2, 0x00], i32u16: [opcode + 3, 0x01],
            i64u8: [opcode + 4, 0x00], i64u16: [opcode + 5, 0x01],
            i64u32: [opcode + 6, 0x02]
        };

        const {type, datatype, offset} = instruction;
        const key = type.value + (datatype?.value || "");

        yield * [0xFE, ...opcodes[key], ...ULEB128(offset)];
    }

    * BLOCKS(instruction, opcode) {

        /* This helper method compiles the block-instruction specified by the
        `opcode` argument (one of `block`, `loop` or `branch`).

        The `labels` stack is updated (either with the instruction identifier
        or `undefined`), recursively, pushing the label before the block is
        encoded, and popping the label afterwards.

        Note: Any `else` blocks of `branch` instructions are handled by the
        `BRANCH` method itself.

        Note: The type indices of block instructions (when used) are encoded
        using a 33-bit Signed LEB128 integer (to avoid clobbering the values
        used to encode block types that are empty or map a single valtype to
        an implicitly empty result). This is a corner-case in the spec. */

        const type = instruction.type;

        // pass the label to the name section and update the label stack...

        SECTIONS[0].appendLabel(this.index, instruction);

        if (instruction.identifier) {

            const value = instruction.identifier.value;

            if (not(this.labels.includes(value))) this.labels.push(value);
            else throw new DuplicateLabelError(instruction.identifier);

        } else this.labels.push(undefined);

        // encode the instruction, yielding each of its bytes...

        yield opcode;

        if (type instanceof Void) yield 0x40;
        else if (type instanceof Primitive) yield encodings[type.value];
        else yield * SLEB128(SECTIONS[1].resolveType(instruction), 33);

        yield * SECTIONS[10].encodeExpression(instruction.block);

        // now the block has been encoded, pop the label from the stack...

        this.labels.pop();
    }

    * UNREACHABLE(instruction) {

        /* The compiler for the `unreachable` mnemonic. */

        yield 0x00;
    }

    * NOP(instruction) {

        /* The compiler for the `nop` mnemonic. */

        yield 0x01;
    }

    * RETURN(instruction) {

        /* The compiler for the `return` mnemonic. */

        yield 0x0F;
    }

    * DROP(instruction) {

        /* The compiler for the `drop` mnemonic, which is used for the WAT
        instructions `drop`, `data.drop` and `elem.drop`. */

        if (instruction.bank) {

            yield 0xFC;

            if (instruction.bank.value === "memory") {

                yield ULEB128(9);
                yield new Identity("memorybank", instruction.identity);

            } else {

                yield ULEB128(13);
                yield new Identity("tablebank", instruction.identity);
            }

        } else yield 0x1A;
    }

    * PUSH(instruction) {

        /* The compiler for the `push` mnemonic, which is used for the WAT
        instructions `const`, `ref.func` and `ref.null`. */

        console.log(instruction);

        const {target, name} = instruction;

        if (target instanceof Keyword) { // push <reftype> null...

            yield opcodes.ref.null;
            yield encodings[name];

        } else if (name === "pointer") { // push pointer <identity>...

            yield opcodes.ref.func;
            yield new Identity("function", target);

        } else { // push [<numtype>] <number-literal>...

            yield opcodes.const[name];

            if (name === "i32") yield * SLEB128(target, 32);
            else if (name === "i64") yield * SLEB128(target, 64);
            else yield * IEEE754(target, "f32" === name ? 32 : 64);
        }
    }

    * GET(instruction) {

        /* The compiler for the `get` mnemonic. */

        yield * this.GETSET(instruction, false);
    }

    * SET(instruction) {

        /* The compiler for the `set` mnemonic. */

        yield * this.GETSET(instruction, true);
    }

    * PUT(instruction) {

        /* The compiler for the `put` instruction, which compiles
        to the WebAssembly `local.tee` instruction. */

        yield 0x22;
        yield * ULEB128(this.resolveLocal(instruction.identity));
    }

    * ADD(instruction) {

        /* The compiler for the `add` mnemonic. */

        const opcodes = {i32: 0x6A, i64: 0x7C, f32: 0x92, f64: 0xA0};

        yield opcodes[instruction.type.value];
    }

    * SUB(instruction) {

        /* The compiler for the `sub` mnemonic. */

        const opcodes = {i32: 0x6B, i64: 0x7D, f32: 0x93, f64: 0xA1};

        yield opcodes[instruction.type.value];
    }

    * MUL(instruction) {

        /* The compiler for the `mul` mnemonic. */

        const opcodes = {i32: 0x6C, i64: 0x7E, f32: 0x94, f64: 0xA2};

        yield opcodes[instruction.type.value];
    }

    * DIV (instruction) {

        /* The compiler for the `div` mnemonic. */

        const opcodes = {
            s32: 0x6D, u32: 0x6E, s64: 0x7F,
            u64: 0x80, f32: 0x95, f64: 0xA3
        };

        yield opcodes[instruction.type.value];
    }

    * REM(instruction) {

        /* The compiler for the `rem` mnemonic. */

        const opcodes = {s32: 0x6F, u32: 0x70, s64: 0x81, u64: 0x82};

        yield opcodes[instruction.type.value];
    }

    * ABS(instruction) {

        /* The compiler for the `abs` mnemonic. */

        yield {f32: 0x8B, f64: 0x99}[instruction.type.value];
    }

    * NEG(instruction) {

        /* The compiler for the `neg` mnemonic. */

        yield {f32: 0x8C, f64: 0x9A}[instruction.type.value];
    }

    * CEILING(instruction) {

        /* The compiler for the `ceiling` mnemonic (`ceil` in WAT). */

        yield {f32: 0x8D, f64: 0x9B}[instruction.type.value];
    }

    * FLOOR(instruction) {

        /* The compiler for the `floor` mnemonic. */

        yield {f32: 0x8E, f64: 0x9C}[instruction.type.value];
    }

    * NEAREST(instruction) {

        /* The compiler for the `nearest` mnemonic. */

        yield {f32: 0x90, f64: 0x9E}[instruction.type.value];
    }

    * ROOT(instruction) {

        /* The compiler for the `root` mnemonic (`sqrt` in WAT). */

        yield {f32: 0x91, f64: 0x9F}[instruction.type.value];
    }

    * MIN(instruction) {

        /* The compiler for the `min` mnemonic. */

        yield {f32: 0x96, f64: 0xA4}[instruction.type.value];
    }

    * MAX(instruction) {

        /* The compiler for the `max` mnemonic. */

        yield {f32: 0x97, f64: 0xA5}[instruction.type.value];
    }

    * SIGN(instruction) {

        /* The compiler for the `sign` mnemonic (`copysign` in WAT). */

        yield {f32: 0x98, f64: 0xA6}[instruction.type.value];
    }

    * BLOCK(instruction) {

        /* The compiler for the `block` instruction. */

        yield * this.BLOCKS(instruction, 0x02);
    }

    * LOOP(instruction) {

        /* The compiler for the `loop` instruction. */

        yield * this.BLOCKS(instruction, 0x03);
    }

    * BRANCH(instruction) {

        /* This method compiles the `branch` instruction, including any else-
        block when present. It uses the `BLOCKS` helper to compile the branch-
        block, while any else-block is compiled locally. This requires that
        the `end` pseudo-instruction (yielded by `BLOCKS`) is replaced with
        an `else` pseudo-instruction, before encoding the the else-block). */

        const block = this.BLOCKS(instruction, 0x04);

        if (instruction.else) {

            yield * Array.from(block).slice(0, -1).concat([0x05]);
            yield * SECTIONS[10].encodeExpression(instruction.else.block);

        } else yield * block;
    }

    * JUMP(instruction) {

        /* The compiler for the `jump` instruction (`br` in WAT). */

        yield 0x0C;
        yield * ULEB128(this.resolveLabel(instruction.identity));
    }

    * FORK(instruction) {

        /* The compiler for the `fork` instruction (`br_if` in WAT). */

        yield 0x0D;
        yield * ULEB128(this.resolveLabel(instruction.identity));
    }

    * EXIT(instruction) {

        /* The compiler for the `exit` instruction (`br_table` in WAT). */

        yield 0x0E;
        yield * ULEB128(instruction.identities.length - 1);

        for (const label of instruction.identities) {

            yield * ULEB128(this.resolveLabel(label));
        }
    }

    * CALL(instruction) {

        /* The compiler for the `call` instruction. */

        yield 0x10;
        yield new Identity("function", instruction.identity);
    }

    * INVOKE(instruction) {

        /* The compiler for the `invoke` instruction (`call_indirect` in
        WAT). */

        yield 0x11;
        yield * ULEB128(SECTIONS[1].resolveType(instruction));
        yield new Identity("table", instruction.table);
    }

    * LOAD(instruction) {

        /* The compiler for the (non-atomic) `load` mnemonic. */

        const codes = {
            i32: [0x28, 2], i64: [0x29, 3],
            f32: [0x2A, 2], f64: [0x2B, 3],
            i32s8: [0x2C, 0], i32u8: [0x2D, 0],
            i32s16: [0x2E, 1], i32u16: [0x2F, 1],
            i64s8: [0x30, 0], i64u8: [0x31, 0],
            i64s16: [0x32, 1], i64u16: [0x33, 1],
            i64s32: [0x34, 2], i64u32: [0x35, 2]
        };

        const datatype = instruction.datatype?.value || "";

        yield * codes[instruction.type.value + datatype];
        yield * ULEB128(instruction.offset);
    }

    * STORE(instruction) {

        /* The compiler for the (non-atomic) `store` mnemonic. */

        const codes = {
            i32: [0x36, 2], i64: [0x37, 3],
            f32: [0x38, 2], f64: [0x39, 3],
            i32i8: [0x3A, 0], i32i16: [0x3B, 1],
            i64i8: [0x3C, 0], i64i16: [0x3D, 1], i64i32: [0x3E, 2]
        };

        const datatype = instruction.datatype?.value || "";

        yield * codes[instruction.type.value + datatype];
        yield * ULEB128(instruction.offset);
    }

    * IS(instruction) {

        /* This is the compiler for the `is` mnemonic, which defers the actual
        compilation to the `ISNOT` helper, except the `is null` instruction,
        which is compiled locally. */

        if (instruction.test.value === "null") yield 0xD1;
        else yield * this.ISNOT(instruction, {
            zero: {
                types: ["i32", "i64"],
                codes: [0x45, 0x50]
            },
            equal: {
                types: ["i32", "i64", "f32", "f64"],
                codes: [0x46, 0x51, 0x5B, 0x61]
            },
            more: {
                types: ["s32", "u32", "s64","u64", "f32", "f64"],
                codes: [0x4A, 0x4B, 0x55, 0x56, 0x5E, 0x64]
            },
            less: {
                types: ["s32", "u32", "s64","u64", "f32", "f64"],
                codes: [0x48, 0x49, 0x53, 0x54, 0x5D, 0x63]
            }
        });
    }

    * NOT(instruction) {

        /* This is the compiler for the `not` mnemonic, which defers the actual
        compilation to the `ISNOT` helper. */

        yield * this.ISNOT(instruction, {
            equal: {
                types: ["i32", "i64", "f32", "f64"],
                codes: [0x47, 0x52, 0x5C, 0x62]
            },
            more: {
                types: ["s32", "u32", "s64","u64", "f32", "f64"],
                codes: [0x4C, 0x4D, 0x57, 0x58, 0x5F, 0x65]
            },
            less: {
                types: ["s32", "u32", "s64","u64", "f32", "f64"],
                codes: [0x4E, 0x4F, 0x59, 0x5A, 0x60, 0x66]
            }
        });
    }

    * SELECT(instruction) {

        /* This is the compiler for the `select` instruction, which takes one
        optional valtype immediate, encoded (when present) as a vector (to
        permit extension in future). The instruction uses two distinct
        opcodes, indicating whether the vector is included or not. */

        if (instruction.type === undefined) yield 0x1B;
        else yield * [0x1C, 0x01, encodings[instruction.type.value]];
    }

    * COPY(instruction) {

        /* This is the compiler for the `copy` mnemonic, which handles the
        WAT `memory.copy`, `table.copy`, `memory.init` and `table.init`
        instructions. */

        yield 0xFC;

        if (instruction.component.value === "memory") {

            if (instruction.bank) {

                yield * ULEB128(8);
                yield new Identity("memorybank", instruction.identity);
                yield new Identity("memory", instruction.destination);

            } else {

                yield * ULEB128(10);
                yield new Identity("memory", instruction.identity);
                yield new Identity("memory", instruction.destination);
            }

        } else { // tables...

            if (instruction.bank) {

                yield * ULEB128(12);
                yield new Identity("tablebank", instruction.identity);
                yield new Identity("table", instruction.destination);

            } else {

                yield * ULEB128(14);
                yield new Identity("table", instruction.identity);
                yield new Identity("table", instruction.destination);
            }
        }
    }

    * GROW(instruction) {

        /* This is the compiler for the `grow` mnemonic (for the WebAssembly
        instructions `memory.grow` and table.grow`). */

        if (instruction.component.value === "memory") {

            yield * [0x40, new Identity("memory", instruction.identity)];

        } else yield * this.GROWFILLSIZE(instruction, 15);
    }

    * FILL(instruction) {

        /* This is the compiler for the `fill` mnemonic (for the WebAssembly
        instructions `memory.fill` and table.fill`). */

        if (instruction.component.value === "memory") {

            yield * this.GROWFILLSIZE(instruction, 11);

        } else yield * this.GROWFILLSIZE(instruction, 17);
    }

    * SIZE(instruction) {

        /* This is the compiler for the `size` mnemonic (for the WebAssembly
        instructions `memory.size` and table.size`). */

        if (instruction.component.value === "memory") {

            yield * [0x3F, new Identity("memory", instruction.identity)];

        } else yield * this.GROWFILLSIZE(instruction, 16);
    }

    * CLZ(instruction) {

        /* This is the compiler for the `clz` instruction (count leading
        zeros). */

        yield instruction.type.value === "i32" ? 0x67 : 0x79;
    }

    * CTZ(instruction) {

        /* This is the compiler for the `ctz` instruction (count trailing
        zeros). */

        yield instruction.type.value === "i32" ? 0x68 : 0x7A;
    }

    * NSA(instruction) {

        /* This is the compiler for the `nsa` instruction (population count)
        (`popcnt` in WAT). */

        yield instruction.type.value === "i32" ? 0x69 : 0x7B;
    }

    * AND(instruction) {

        /* This is the compiler for the logicl `and` instruction. */

        yield instruction.type.value === "i32" ? 0x71 : 0x83;
    }

    * OR(instruction) {

        /* This is the compiler for the logical `or` instruction. */

        yield instruction.type.value === "i32" ? 0x72 : 0x84;
    }

    * XOR(instruction) {

        /* This is the compiler for the logical `xor` instruction. */

        yield instruction.type.value === "i32" ? 0x73 : 0x85;
    }

    * WRAP(instruction) {

        /* This is the compiler for the `wrap` instruction. */

        yield 0xA7;
    }

    * CAST(instruction) {

        /* This is the compiler for the `cast` mnemonic (`reinterpret` in
        WAT). */

        const opcodes = {i32: 0xBC, i64: 0xBD, f32: 0xBE, f64: 0xBF};

        yield opcodes[instruction.result.value];
    }

    * SHIFT(instruction) {

        /* This is the compiler for the `shift` mnemonic (`shr` and `shl` in
        WAT). */

        const opcodes = {
            left: {i32: 0x74, i64: 0x86},
            right: {s32: 0x75, u32: 0x76, s64: 0x87, u64: 0x88}
        };

        yield opcodes[instruction.qualifier.value][instruction.type.value];
    }

    * ROTATE(instruction) {

        /* This is the compiler for the `rotate` mnemonic (`rotr` and `rotl`
        in WAT). */

        const opcodes = {
            left: {i32: 0x77, i64: 0x89},
            right: {i32: 0x78, i64: 0x8A}
        };

        yield opcodes[instruction.qualifier.value][instruction.type.value];
    }

    * PROMOTE(instruction) {

        /* This is the compiler for the `promote` instruction. */

        yield 0xBB;
    }

    * DEMOTE(instruction) {

        /* This is the compiler for the `demote` instruction. */

        yield 0xB6;
    }

    * LOP(instruction) {

        /* This is the compiler for the `lop` and `lop sop` instructions
        (`trunc` and `trunc_sat` in WAT). */

        if (instruction.sop) {

            const type = instruction.operand.value + instruction.result.value;

            const opcodes = [
                "f32s32", "f32u32", "f64s32", "f64u32",
                "f32s64", "f32u64", "f64s64", "f64u64"
            ];

            yield * [0xFC, ...ULEB128(opcodes.indexOf(type))];

        } else if (instruction.result) {

            const opcodes = {
                f32: {s32: 0xA8, u32: 0xA9, s64: 0xAE, u64: 0xAF},
                f64: {s32: 0xAA, u32: 0xAB, s64: 0xB0, u64: 0xB1}
            };

            yield opcodes[instruction.operand.value][instruction.result.value];

        } else yield {f32: 0x8F, f64: 0x9D}[instruction.operand.value];
    }

    * CONVERT(instruction) {

        /* This is the compiler for the `convert` mnemonic. */

        const opcodes = {
            f32: {s32: 0xB2, u32: 0xB3, s64: 0xB4, u64: 0xB5},
            f64: {s32: 0xB7, u32: 0xB8, s64: 0xB9, u64: 0xBA}
        };

        yield opcodes[instruction.result.value][instruction.operand.value];
    }

    * EXPAND(instruction) {

        /* This is the compiler for the `expand` instruction
        (`i32.extend8_s`, `i32.extend16_s`, `i64.extend8_s`,
        `i64.extend16_s` and `i64.extend32_s` in WAT). */

        const opcodes = {
            i32: {s8: 0xC0, s16: 0xC1},
            i64: {s8: 0xC2, s16: 0xC3, s32: 0xC4}
        };

        yield opcodes[instruction.type.value][instruction.datatype.value];
    }

    * EXTEND(instruction) {

        /* This is the compiler for the `extend` instruction
        (`i64.extend_i32_s` and `i64.extend_i32_u` in WAT). */

        yield {s32: 0xAC, u32: 0xAD}[instruction.operand.value];
    }

    * ATOMIC_FENCE(instruction) {

        /* The compiler for the `atomic fence` instruction. */

        yield * [0xFE, 0x03, 0x00];
    }

    * ATOMIC_NOTIFY(instruction) {

        /* The compiler for the `atomic notify` instruction. */

        const {memory, offset} = instruction;

        yield * [0xFE, 0x00, 0x02, ...ULEB128(offset)];
    }

    * ATOMIC_WAIT(instruction) {

        /* The compiler for the `atomic wait` instructions. */

        const opcode = {i32: 0x01, i64: 0x02}[instruction.type.value];
        const optype = {i32: 0x02, i64: 0x03}[instruction.type.value];

        yield * [0xFE, opcode, optype, ...ULEB128(instruction.offset)];
    }

    * ATOMIC_ADD(instruction) {

        /* The compiler for the `atomic add` instruction. */

        yield * this.ATOMICS(instruction, 0x1E);
    }

    * ATOMIC_SUB(instruction) {

        /* The compiler for the `atomic sub` instruction. */

        yield * this.ATOMICS(instruction, 0x25);
    }

    * ATOMIC_AND(instruction) {

        /* The compiler for the `atomic and` instruction. */

        yield * this.ATOMICS(instruction, 0x2C);
    }

    * ATOMIC_OR(instruction) {

        /* The compiler for the `atomic or` instruction. */

        yield * this.ATOMICS(instruction, 0x33);
    }

    * ATOMIC_XOR(instruction) {

        /* The compiler for the `atomic xor` instruction. */

        yield * this.ATOMICS(instruction, 0x3A);
    }

    * ATOMIC_SWAP(instruction) {

        /* The compiler for the `atomic swap` instruction (`xchg` in WAT). */

        yield * this.ATOMICS(instruction, 0x41);
    }

    * ATOMIC_BROKER(instruction) {

        /* The compiler for the `atomic broker` instruction (`cmpxchg` in
        WAT). */

        yield * this.ATOMICS(instruction, 0x48);
    }

    * ATOMIC_LOAD(instruction) {

        /* This is the compiler for the `atomic load` instruction. */

        yield * this.ATOMICS(instruction, 0x10);
    }

    * ATOMIC_STORE(instruction) {

        /* This is the compiler for the `atomic store` instruction (which
        uses agnostic datatypes (`i8`, `i16` and `i32`), while the atomic
        instructions generally use unsigned datatypes (`u8`, u16` etc). */

        const opcodes = {
            i32: [0x17, 0x02], i64: [0x18, 0x03],
            i32i8: [0x19, 0x00], i32i16: [0x1A, 0x01],
            i64i8: [0x1B, 0x00], i64i16: [0x1C, 0x01], i64i32: [0x1D, 0x02]
        };

        const {type, datatype, offset} = instruction;
        const key = type.value + (datatype?.value || "");

        yield * [0xFE, ...opcodes[key], ...ULEB128(offset)];
    }

    encode(statement) {

        /* This method is invoked by the `FunctionSection.encode` method once
        that method has registered the function type of the given function def-
        inition statement. This method first registers the function (using the
        index to update the Name Section), then encodes the locals and body of
        the function definition (in this section) as a wasm-code-entry. */

        const registerLocalRegister = node => {

            /* This helper takes a `node` that defines a local register (that
            will be a `ParamElement` or `LocalDefinition`). The helper always
            increments the `localIndex` property, then copies any identifier
            over to the `locals` property, with its local index. */

            if (node.identifier === undefined) this.localIndex++;
            else if (this.locals[node.identifier.value] === undefined) {

                this.locals[node.identifier.value] = this.localIndex++;

            } else throw new DuplicateIdentifierError(node.identifier);
        };

        const component = statement.component;
        const payload = ULEB128(component.locals.length);
        const {type, block} = component;

        this.localIndex = 0;            // reset the length of the localspace
        this.locals = {};               // reset the hash of local identifiers
        this.index = component.index;   // update the function index

        if (component.start) SECTIONS[8].payload = this.index;

        // handle the type reference or expression (whichever is present), and
        // then handle any `local` directives (encoding them, and noting any
        // identifiers)...

        if (type instanceof TypeExpression) {

            type.params.forEach(registerLocalRegister);

        } else this.localIndex = TypeSection.referenceType(type).params.length;

        component.locals.forEach(function(local) {

            payload.push(0x01);
            payload.push(encodings[local.type.value]);
            registerLocalRegister(local);
        });

        SECTIONS[0].appendLocals(this.index, this.locals);

        // encode the expression block and add it to the local payload...

        const expression = SECTIONS[10].encodeExpression(block);
        const output = payload.concat(...expression);

        // convert the output to a vector and push to the section payload...

        this.push(...ULEB128(output.length), ...output);
    }
}

class TableSection extends VectorSection {

    /* A singleton class that implements the Table Section, which is a vector
    of tables, encoded to their tabletypes. This section only describes the
    tables themselves (not their contents). */

    encode(statement) {

        /* This method takes a table definition, and encodes the reftype and
        limits of the table, updating the `payload` array, before slicing any
        primer into one or more segments, and passing each of the segments to
        the Element Section for encoding. */

        const component = statement.component;
        const {type, primer, index} = component;

        this.push(encodings[type.value]);
        this.pushLimits(statement.component);

        for (const segment of primer) new TableSegment(index, segment);
    }
}

class MemorySection extends VectorSection {

    /* A singleton class that implements the Memory Section, which is a vector
    of memories, encoded to their memtypes. This section only describes the
    memories themselves (not their contents). */

    encode(statement) {

        /* This method takes a memory definition, encodes the limits of the
        memory, updating the `payload` array, before slicing any primer into
        one or more segments, and passing each segment to the Data Section
        for encoding. */

        const {shared, primer, index} = statement.component;

        this.pushLimits(statement.component, shared);

        for (const segment of primer) new MemorySegment(index, segment);
    }
}

class DataSection extends VectorSection {

    /* A singleton class that implements the Data Section, which is a vector
    of memory segments (both active and passive), encoded to the memory index,
    an offset into the memory (given as a constant expression), and the bytes,
    encoded to an internal vector. */

    encode(segment) {

        /* This method takes a data segment (unlike regular `encode` methods,
        which take a statement). The segment will be a `MemoryBankSegment` (a
        passive segment) or a `MemorySegment` from a memory primer (an active
        segment). The method encodes the segment, updating the `payload` array,
        before invoking the `append` method of `DataCountSection` to increment
        the data segment count. */

        if (segment instanceof MemoryBankSegment) this.push(0x01);
        else this.push(0x02, ...ULEB128(segment.index), ...segment.expression);

        this.pushVector(segment.payload, this.encodeElement);
        SECTIONS[12].append(this);
    }

    encodeElement(element) {

        /* This method is used as a callback (for passing to `pushVector`) that
        takes and encodes a memory element from a memory primer or memory bank
        segment. The resulting bytes are returned as an `Array` (so the array
        can be flattened by the `pushVector` method (typed arrays cannot be
        flattened in the same way)). */

        const {type, value, length} = element;

        if (type.value === "utf8") return Array.from(encodeUTF8(value.value));

        const buffer = new ArrayBuffer(length);
        const output = new Uint8Array(buffer);

        new views[type.value](buffer)[0] = evaluateLiteral(value);

        return Array.from(output);
    }
}

class ElementSection extends VectorSection {

    /* A singleton class that implements the Element Section. */

    encode(segment) {

        /* This method takes a table segment (unlike regular `encode` methods,
        which take a statement). The segment will be a `TableBankSegment` (a
        passive segment) or a `TableSegment` from a memory primer (an active
        segment). The method encodes the segment, updating the `payload`
        array. */

        if (segment instanceof TableBankSegment) this.push(0x05);
        else this.push(0x06, ...ULEB128(segment.index), ...segment.expression);

        this.push(encodings.pointer);
        this.pushVector(segment.payload, this.encodeElement, false);
    }

    encodeElement(element) {

        /* This helper method takes an element from a segment and returns the
        corresponding constant expression. Currently, the spec only permits
        pointers (which can be null) in table primers. */

        const nullref = ref => [opcodes.ref.null, ref, encodings.end];
        const funcref = ref => [opcodes.ref.func, ref, encodings.end];

        if (element.value.value === "null") return nullref(encodings.pointer);
        else return funcref(new Identity("function", element.value));
    }
}

class NameSection {

    /* This class implements the (extended) Custom Name section of the binary,
    which preserves the URL of the module and its identifiers. */

    constructor(id) {

        /* This constructor creates an empty `indexspaces` hash that is used
        to store data passed to the `append` method, and later used by the
        `compile` method to encode the section. The hash contains a hash for
        each component type, plus a pair of extra hashes that represent two
        indirect namemaps, one for locals, another for labels. */

        this.id = id;
        this.label = 0; // tracks the current label index

        this.indexspaces = {
            register: {}, function: {}, memory: {}, table: {}, type: {},
            memorybank: {}, tablebank: {}, locals: {}, labels: {}
        };
    }

    static encodeName(name) {

        /* This static method takes an arbitrary Unicode string, encodes it to
        a wasm-name (a vector of UTF-8 bytes), then returns the result. */

        const bytes = Array.from(encodeUTF8(name));

        return ULEB128(bytes.length).concat(bytes);
    }

    append(type, identifier, index) {

        /* This helper method takes a component type name and an identifier,
        both as strings, and the corresponding index. It updates the corre-
        sponding `indexspaces` hash, before returning `undefined`. */

        this.indexspaces[type][identifier] = index;
    }

    appendLocals(index, locals) {

        /* This helper takes a function index (`index`), and a hash (`locals`)
        that maps any identifiers that are bound to locals (including params)
        within the function to their corresponding indices. The helper updates
        the `indexspaces` hash accordingly. */

        this.indexspaces.locals[index] = locals;
    }

    appendLabel(index, instruction) {

        /* This helper method takes a function index and a block-instruction.
        If the given index has not been passed to a previous invocation, the
        helper will create a new hash for the current function in the `labels`
        space, and will reset the `labels` attribute to zero. Once that has
        been done, the instruction is checked for an identifier (a label),
        registers it when present, then increments the `label` attribute
        either way. */

        if (this.indexspaces.labels[index] === undefined) {

            this.indexspaces.labels[index] = {};
            this.label = 0;
        }

        if (instruction.identifier) {

            const labels = this.indexspaces.labels[index];

            labels[instruction.identifier.value] = this.label++;

        } else this.label++;
    }

    encodeSubsection(id, payload) {

        /* This helper method takes a subsection ID and a payload array. It
        encodes the arguments into a subsection, then returns the result. */

        return [id].concat(ULEB128(payload.length)).concat(payload);
    }

    encodeNameMap(id, type) {

        /* This helper method takes a subsection ID and a type name. It uses
        them to reference the approriate `indexspaces` entry, and encodes the
        stored data as a namemap, before returning the result. */

        const sortItems = (a, b) => a[1].index - b[1].index;

        const items = this.indexspaces[type];
        const length = Object.keys(items).length;

        if (length === 0) return []; // omit this section if it is empty

        const vector = ULEB128(length);
        const entries = Object.entries(items).sort(sortItems);

        for (const [identifier, index] of entries) {

            vector.push(ULEB128(index));
            vector.push(NameSection.encodeName(identifier));
        }

        return this.encodeSubsection(id, vector.flat());
    }

    encodeIndirectNameMap(id, type) {

        /* This helper method takes a subsection ID and a type name. It uses
        them to reference the approriate `indexspaces` entry, and encodes the
        stored data as an indirect namemap, before returning the result. */

        const sortItems = (a, b) => a[1] - b[1];
        const sortMaps = (a, b) => parseInt(a[0]) - parseInt(b[0]);

        const items = this.indexspaces[type];
        const length = Object.keys(items).length;

        if (length === 0) return []; // omit this section if it is empty

        const vector = ULEB128(length);
        const groups = Object.entries(items).sort(sortMaps);

        for (const [index, indices] of groups) {

            const entries = Object.entries(indices).sort(sortItems);

            vector.push(ULEB128(index));
            vector.push(ULEB128(Object.keys(entries).length));

            for (const [identifier, index] of entries) {

                vector.push(ULEB128(parseInt(index)));
                vector.push(NameSection.encodeName(identifier));
            }
        }

        return this.encodeSubsection(id, vector.flat());
    }

    compile() {

        /* This method compiles the instance to an array of bytes, which
        represents the Custom Name Section of the binary, then returns the
        result. */

        const data = [
            {id: 1, type: "function", direct: true},
            {id: 2, type: "locals", direct: false},
            {id: 3, type: "labels", direct: false},
            {id: 4, type: "type", direct: true},
            {id: 5, type: "table", direct: true},
            {id: 6, type: "memory", direct: true},
            {id: 7, type: "register", direct: true},
            {id: 8, type: "tablebank", direct: true},
            {id: 9, type: "memorybank", direct: true},
        ];

        let payload = [4, 110, 97, 109, 101]; // initialize with the header

        payload.push(this.encodeSubsection(0, NameSection.encodeName(URL)));

        for (const {id, type, direct} of data) {

            if (direct) payload.push(this.encodeNameMap(id, type));
            else payload.push(this.encodeIndirectNameMap(id, type));
        }

        payload = payload.flat();

        return [this.id].concat(ULEB128(payload.length)).concat(payload);
    }
}

/* --{ THE LOCAL HELPER FUNCTIONS }----------------------------------------- */

const registerComponent = function(type, component, bind=false) {

    /* This helper takes an indexspace name, a component node and a bool that
    defaults to `false`. The helper pushes the component to the appropriate
    indexspace, and if the bool is truthy, its identifier is also bound to the
    new index. In either case, the index is returned. This allows imports and
    definitions to register the different the types of component that they
    introduce, and optionally bind their identifiers. */

    const index = INDEXSPACES.components[type].push(component) - 1;

    if (bind) registerIdentifier(type, component.identifier, index);

    return index;
};

const resolveComponent = function(type, index) {

    /* This helper takes a indexspace name (`type`) and an index, and returns
    the corresponding component, or `undefined` if it does not exist. */

    return INDEXSPACES.components[type][index];
};

const registerIdentifier = function(type, node, index) {

    /* This helper takes an indexspace name (`type`), an identifier node (that
    may be `undefined`) and an index. If the identifier is defined and unique
    (within its indexspace), it is bound to the given index in the given space,
    and if the identifier is `undefined`, nothing happens. If the identifier
    is already bound (in the given indexspace), then an exception is raised.
    Otherwise, the function always returns `undefined`. */

    if (node === undefined) return;

    const indexspace = INDEXSPACES.identifiers[type];
    const identifier = node.value;

    if (indexspace[identifier] === undefined) indexspace[identifier] = index;
    else throw new DuplicateIdentifierError(node);

    SECTIONS[0].append(type, identifier, index); // update the name section
};

const resolveIdentifier = function(type, identifier) {

    /* This helper takes a indexspace name and an identifier, and then returns
    the corresponding index, or throws an exception if the identifer is not
    registered in the given indexspace. */

    const index = INDEXSPACES.identifiers[type][identifier.value];

    if (index === undefined) {

        throw new UnboundIdentifierError(type, identifier);

    } else return index;
};

const resolveIdentity = function(type, identity) {

    /* This helper takes a indecspace name (`type`) and an identity (an index
    or identifier). It returns the expressed index. */

    if (identity instanceof NumberLiteral) {

        const index = evaluateLiteral(identity);
        const bound = INDEXSPACES.components[type].length;

        if (index < bound) return index;
        else throw new UnboundIndexError(type, identity);

    } else return resolveIdentifier(type, identity);
}

const reset = function(configuration) {

    /* This is the generic reset helper for this module. It resets the
    compiler state, ready for a new source file to be compiled. */

    [SOURCE, URL] = [configuration.source, configuration.url];

    SECTIONS = [
        new NameSection(0),
        new TypeSection(1),
        new ImportSection(2),
        new FunctionSection(3),
        new TableSection(4),
        new MemorySection(5),
        new GlobalSection(6),
        new ExportSection(7),
        new StartSection(8),
        new ElementSection(9),
        new CodeSection(10),
        new DataSection(11),
        new DataCountSection(12)
    ];

    INDEXSPACES = {};

    INDEXSPACES.components = {
        register: [], function: [], type: [],
        memory: [], table: [], memorybank: [], tablebank: [],
    };

    INDEXSPACES.identifiers = {
        register: {}, function: {}, type: {},
        memory: {}, table: {}, memorybank: {}, tablebank: {},
    };
};

/* --{ THE NUMERIC ENCODERS }----------------------------------------------- */

const ULEB128 = stack(function(push, pop, input) {

    /* This stack function takes an positive integer as a BigInt, an integer
    Number or a NumberLiteral token instance, encodes it using the Unsigned
    LEB128 encoding, pushing each byte to the resulting array as a Number. */

    if (input instanceof NumberLiteral) input = evaluateLiteral(input, true);
    else input = BigInt(input);

    while(true) {

        const byte = input & 0x7Fn;

        input >>= 7n;

        if (input === 0n) return push(Number(byte));
        else push(Number(byte | 0x80n));
    }
});

const SLEB128 = stack(function(push, pop, input, agnostic=undefined) {

    /* This stack function takes an integer `Number` or `NumberLiteral`, and
    encodes it using the Signed LEB128 encoding, pushing each byte to the re-
    sulting array as a `Number`. The function also takes an optional argument,
    which is normally left `undefined` and ignored, but it can be set to `32`,
    `33` or `64` (as a `Number`) to indicate the width, which allows agnostic
    integers that are in range, but too high for the signed encoding, to be
    converted to their negative equivalents automatically. */

    const zero = () => input === 0n && (byte & 0x40n) === 0n;
    const ones = () => input === -1n && (byte & 0x40n) !== 0n;

    let byte;

    if (input instanceof NumberLiteral) input = evaluateLiteral(input, true);
    else input = BigInt(input);

    if (agnostic) {

        const width = BigInt(agnostic);
        const upperbound = 2n ** width;
        const decremented = width - 1n;

        if (input >= 2n ** decremented) input -= upperbound;
    }

    while (true) {

        byte = input & 0x7Fn;
        input >>= 7n;

        if (zero() || ones()) return push(Number(byte));
        else push(Number(byte | 0x80n));
    }
});

const IEEE754 = stack(function(push, pop, input, width) {

    /* This stack function takes a width (either `32` or `64`) and any `Number`
    or `NumberLiteral` instance, and encodes it using the IEEE floating point
    encoding for the given width, pushing each byte to the resulting array
    as a `Number`. */

    if (input instanceof NumberLiteral) input = evaluateLiteral(input, false);

    const FloatArray = width === 32 ? Float32Array : Float64Array;
    const buffer = new FloatArray([input]).buffer;
    const bytes = new Uint8Array(buffer, 0, width / 8);

    for (const byte of bytes) push(byte);
});

/* --{ THE COMPILER STAGES }------------------------------------------------ */

const stageZero = function(statements) {

    /* This helper implements Stage One of the compiler. It takes an instance
    of the `parse` generator, which it iterates over to access the statements
    of the current module. It sorts the statements into three arrays, one for
    definitions, one for imports and a third for exports, though type, memory
    bank and table bank definitions are handled immediately (not pushed to an
    array). The helper returns an array containing the three statement arrays,
    in the order: imports, definitions, exports. */

    const [imports, definitions, exports] = [[], [], []];

    for (const statement of statements) {

        const is = Class => statement instanceof Class;

        if (is(ImportStatement)) imports.push(statement);
        else if (is(ExportStatement)) exports.push(statement);
        else {

            const component = statement.component;
            const name = component.name;

            if (name === "type") {

                component.index = registerComponent(name, component, true);
                SECTIONS[1].append(statement);

            } else if (name === "memorybank") {

                component.index = registerComponent(name, component, true);
                new MemoryBankSegment(component.primer);

            } else if (name === "tablebank") {

                component.index = registerComponent(name, component, true);
                new TableBankSegment(component.primer);

            } else definitions.push(statement);
        }
    }

    return [imports, definitions, exports];
};

const stageOne = function(imports) {

    /* This helper implements Stage Two, which handles all of the import
    statements. It takes an array of import statements, compiles them and
    returns `undefined`. */

    for (const statement of imports) {

        const component = statement.component;

        component.index = registerComponent(component.name, component, true);
        SECTIONS[2].append(statement);
    }
};

const stageTwo = function(definitions) {

    /* This helper implements Stage Three, which handles all of the define
    statements. It takes an array of (the remaining) define statements, and
    compiles them, before returning `undefined`. */

    const sectionIDs = {function: 3, table: 4, memory: 5, register: 6};

    for (const statement of definitions) {

        const component = statement.component;
        const name = component.name;

        if (name in sectionIDs) {

            component.index = registerComponent(name, component, true);
            SECTIONS[sectionIDs[name]].append(statement);
        }
    }
};

const stageThree = function(exports) {

    /* This helper implements Stage Four, which handles all of the export
    statements. It takes an array of export statements, and compiles them,
    before returning `undefined`. */

    for (const statement of exports) SECTIONS[7].append(statement);
};

/* --{ THE COMPILER ENTRYPOINT }-------------------------------------------- */

export const compile = function * (configuration) {

    /* This is the entrypoint generator for the compiler, and generally for
    the assembler as a pipeline. It takes a configuration hash, and yields
    the given module bytewise, or throws a syntax error, if the source is
    invalid. */

    reset(configuration);

    const [imports, definitions, exports] = stageZero(parse(configuration));

    stageOne(imports); stageTwo(definitions); stageThree(exports);

    yield * header;

    for (const id of sectionIDs) yield * SECTIONS[id].compile();
};

export default compile;
