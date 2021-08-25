/* --{ THE PHANTASM COMPILER  }--{ /static/compiler.js }--------------------------------------------- *

This module implements the PHANTASM parser, exporting a function
named `compile` as an entrypoint. */

import {
    lex, put, not, iife, stack, format, encodeUTF8, Identifier, NumberLiteral, PhantasmError,
    Node, Primitive, Void
} from "./lexer.js";

import {
    parse, TypeReference, TypeExpression, ParamElement, evaluateLiteral, TypeDefinition,
    Instruction, BlockInstruction, DefineStatement, ImportStatement, ExportStatement,
    RegisterDefinition, FunctionDefinition, MemoryDefinition, TableDefinition,
    RegisterSpecifier, FunctionSpecifier, MemorySpecifier, TableSpecifier,
    RegisterReference, FunctionReference, MemoryReference, TableReference,
    SegmentElement, MemoryElement, TableElement
} from "./parser.js";

// global compiler state (updated by `compile` on each invocation)...

let SOURCE, URL, INDEXSPACES, SECTIONS;

// useful constants...

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

// compiler error classes...

class CompilerError extends PhantasmError {

    /* The abstract base class for all compiler errors. */

    constructor(node, text) {

        /* The `node` argument is the offending token, and the `text` argument
        contains the error message. */

        super(URL, node.location.line, node.location.column, text);
    }
}

class DuplicateTypeError extends CompilerError {

    /* Thrown when a type is explicitly defined, and is a duplicate of another
    explicitly defined type. */

    constructor(node) {

        /* The `node` argument is the `TypeDefinition` instance, which is the
        `component` attribute of the offending type definition statement. */

        super(node, "Duplicate function types are not permitted.");
    }
}

class DuplicateIdentifierError extends CompilerError {

    /* Thrown when the user attempts to bind an identifier that is a duplicate
    of another identifier in the same indexspace. */

    constructor(node) {

        const template = "Reassigning an identifier (`${0.v}`) is illegal.";

        super(node, format(template, node));
    }
}

class DuplicateLabelError extends CompilerError {

    /* Thrown when the user attempts to bind an label that is a duplicate
    of another label within the same scope. */

    constructor(node) {

        const template = "Cannot rebind a label (`${0.v}`) within a scope.";

        super(node, format(template, node));
    }
}

class UnboundIdentifierError extends CompilerError {

    /* Thrown when the user attempts to reference an identifier that does not
    exist in the appropriate indexspace. */

    constructor(type, node) {

        /* The `type` argument is the name of the indexspace as a string, and
        the `node` argument is the offending token. */

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

        /* The `type` argument is the name of the indexspace as a string, and
        the `node` argument is the offending token. */

        const template = "The index `{1.v}` is not bound to a {0.s}."

        super(node, format(template, type, node));
    }
}

class LabelIndexError extends CompilerError {

    /* Thrown when the user attempts to target a block with an index
    that is greater then the depth of the instruction. */

    constructor(node) {

        const template = "The given block index ({0.V}) is too high."

        super(node, format(template, node));
    }
}

// helper classes...

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

    /* A class for representing the state associated with a segment from a memory
    or table primer, or one of their banks. The parser just returns an array of
    segment arrays, bound to the `primer` attribute of the component, so this
    class is used to restructure the data, so it can be passed into whatever
    section does the actual encoding. */

    constructor(segment) {

        /* This constructor stashes the segment, then initializes the `explicit`
        attribute to `false`, making it always `false` for banks, while leaving
        primers to change it as required. */

        this.elements = segment;
        this.explicit = false;
    }

    get expression() {

        /* This computed attribute evaluates to an array of bytes that represent
        the constant expression required to locate the segment. If the instance
        starts with an explicit `segment` directive, then it is compiled and
        returned. Otherwise, a `push i32 0` block is returned instead.

        Note: This method is not used by banks (only segments of primers). */

        const i32const = n => [opcodes.const.i32, ...SLEB128(n), encodings.end];

        if (this.explicit) {

            const block = this.elements[0].block;

            if (block[0] instanceof NumberLiteral) return i32const(block[0]);
            else return SECTIONS[10].encodeExpression(block);

        } else return i32const(0);
    }

    get payload() {

        /* This computed attribute evaluates to an array containing all of the
        elements in the segment (excluding the initial segment-directive when
        present). The elements are still represented as abstract nodes (not as
        bytes), ready to be encoded by the appropriate `encode` method. */

        return this.elements.slice(1 * this.explicit);
    }
}

class ArraySegment extends Segment {

    /* This is a base class for memory and table segments (not banks). */

    constructor(index, segment, id) {

        /* This constructor takes the index of the parent memory or table,
        the segment that the class abstracts (an array of elements), and
        the section ID that this instance needs to be passed to (either `9`
        or `11` - Element Section or Data Section). The method passes the
        segment to the base class (`Segment`), stashes the index, and notes
        whether this segment is explicitly located, before passing the ins-
        tance on to the section that encodes it. */

        super(segment);
        this.index = index;
        this.explicit = segment[0] instanceof SegmentElement;
        SECTIONS[id].append(this);
    }
}

class MemorySegment extends ArraySegment {

    /* This helper class represents a segment from a memory primer (not a bank),
    which must be encoded within the Data Section (after any banks). */

    constructor(index, segment) {

        /* This constructor passes the given index and segment to `super`, with
        the ID for the Data Section (`11`). */

        super(index, segment, 11);
    }
}

class TableSegment extends ArraySegment {

    /* This helper class represents a segment from a table primer (not a bank),
    which must be encoded within the Element Section (after any banks). */

    constructor(index, segment) {

        /* This constructor passes the given index and segment to `super`, with
        the ID for the Element Section (`9`). */

        super(index, segment, 9);
    }
}

class MemoryBankSegment extends Segment {

    /* This helper class represents a memory bank, which is encoded to a single
    segment in the Data Section (before any memory primer segments). */

    constructor(segment) {

        /* This constructor passes the only segment of the primer to the parent
        constructor (allowing this instance to function like a regular segment),
        before passing the instance to the Data Section. */

        super(segment[0]);
        SECTIONS[11].append(this);
    }
}

class TableBankSegment extends Segment {

    /* This helper class represents a table bank, which is encoded to a single
    segment in the Element Section (before any table primer segments). */

    constructor(segment) {

        /* This constructor passes the only segment of the primer to the parent
        constructor (allowing this instance to function like a regular segment),
        before passing the instance to the Element Section. */

        super(segment[0]);
        SECTIONS[9].append(this);
    }
}

// abstract bases classes for the sections...

class DatumSection {

    /* This is an abstract base class for those sections in the binary format
    which just define a single value as the payload (basically, the Start and
    Data Count sections). */

    constructor(id) {

        this.id = id;                   // the section ID
        this.payload = undefined;       // the payload value
    }

    compile() {

        /* This method compiles the instance to a complete section, including the
        section ID, its length in bytes and the payload, which will always be an
        Unsigned LEB128 encoded integer. */

        if (this.payload === undefined) return []; // return no bytes if unused

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

        /* This method takes an item (statement, component etc), pushes it to
        the `items` array, and invokes the `encode` method of the derived class,
        which is responsible for encoding the item and pushing its bytes to the
        `payload` array. */

        this.items.push(item);
        this.encode(item);
    }

    push(...bytes) {

        /* This method concatenates any number of argument bytes (represented as
        Numbers between `0` and `255`) to the `payload` array, updating it in place.
        The method is provided as a convenience to derived classes. */

        this.payload = this.payload.concat(bytes);
    }

    pushVector(array, callback, bytewise=true) {

        /* This method takes an array and a callback, and encodes the array by passing each
        of its items through the callback, and flattening the results, before encoding the
        result as a vector, pushing its bytes to the `payload` array. The optional third
        arguemnt (`bytewise`) is a bool that determines whether the vector length will
        be the number of bytes in the compiled result (when `bytewise === true`) or
        the number of items in the input array (when `bytewise === false`). */

        const payload = array.map(item => callback(item)).flat();
        const length = bytewise ? payload.length : array.length;

        this.push(...ULEB128(length), ...payload);
    }

    pushExpression(block) {

        /* This helper method takes a `block` array that contains a constant expression
        that was expressed fully (as a block of one or more constant instructions), and
        encodes the instructions, updating the `payload` array. */

        this.push(...SECTIONS[10].encodeExpression(block));
    }

    pushUTF8(literal) {

        /*This method takes a StringLiteral token instance, pushes the Unsigned LEB128
        encoded length of the string (in UTF-8 bytes) to the `payload` array, and then
        pushes the bytes themselves. This is how strings are represented in the binary
        format. */

        const bytes = encodeUTF8(literal.value);

        this.push(...ULEB128(bytes.length));
        this.push(...bytes);
    }

    pushLimits(component, shared=false) {

        /* This method takes a component with `min` and `max` attributes that describe
        the limits of a memory or table, as well as an optional bool that is `true` for
        shared limits, and `false` otherwise. The method encodes the limits, and pushes
        them to the `payload` array. */

        if (not(component.max)) this.push(0x00, ...ULEB128(component.min));
        else {

            this.push(shared ? 0x03 : 0x01);
            this.push(...ULEB128(component.min), ...ULEB128(component.max));
        }
    }

    compile() {

        /* This method compiles the instance to a complete section, including the
        section ID, the length (bytewise), and the payload vector. */

        if (this.items.length === 0) return []; // return no bytes for an empty section

        const encode = item => item instanceof Identity ? item.bytes : item;

        const payload = this.payload.map(encode).flat();
        const vLength = ULEB128(this.items.length);                 // vector length
        const bLength = ULEB128(vLength.length + payload.length);   // bytewise length

        return [this.id].concat(bLength).concat(vLength).concat(payload);
    }
}

// concrete classes for the sections...

class StartSection extends DatumSection {

    /* This concrete class inherits everything it needs from its parent to implement
    the Start Section, where the payload is just a function index. */
}

class DataCountSection extends DatumSection {

    /* This class implements the DataCount Section, which is a datum section
    that stores the number of items in the Data Section. */

    constructor(id) {

        super(id);
        this.payload = 0;
    }

    append(segment) {

        /* This method ignores it argument, but accepts one to be consistent
        with the `Vector.append` method. It increments the data count each
        time it is called. */

        this.payload++;
    }
}

class TypeSection extends VectorSection {

    /* A singleton class that implements the Type Section, which is a vector of
    type defintions. */

    constructor(id) {

        super(id);
        this.types = {}; // map each unique type expression to its type index
    }

    static serializeTypeExpression(type) {

        /* This static method takes a type expression, serializes it in a deter-
        ministic way that is unique for any possible type expression, then returns
        the resulting string. This is used to check whether the given expression
        expresses a unique type. */

        const encode = param => param.type.value;
        const params = type.params.map(encode);
        const results = type.results.map(encode);

        return params.concat(["->"]).concat(results).join("");
    };

    static referenceType(reference, byIndex=false) {

        /* This helper takes a type reference, and resolves it, returning the
        `TypeExpression` node of the referenced type definition by default, or
        returns its index when the `byIndex` argument is truthy, assuming that
        everything is valid. If the reference uses an undefined identity or an
        index for an implicitly defined type, an exception is raised. */

        const index = resolveIdentity("type", reference.identity);
        const type = INDEXSPACES.components.type[index];

        if (type instanceof TypeDefinition) return byIndex ? index : type.type;

        if (reference.identity instanceof Identifier) {

            throw new UnboundIdentifierError("type", reference.identity);

        } else throw new UnboundIndexError("type", reference.identity);
    };

    resolveType(component) {

        /* This method is used to resolve the type of a function specifier or
        definition, or any of the various instructions that are able to use a
        type reference or type expression to express their types, with any
        parities implicitly registering the expressed type when it is unique.

        This method takes a node and resolves its `type` attribute, returning
        the (possibly new) type index.

        If a type reference is used, the result is checked to ensure that the
        type was explicitly defined (not implicitly defined by this method for
        an earlier function or instruction), raising an error otherwise. */

        if (component.type instanceof TypeExpression) {

            const string = TypeSection.serializeTypeExpression(component.type);

            if (string in this.types) return this.types[string];

            const index = registerComponent("type", component, false);

            this.encodeType(component.type, string, index);
            this.items.push(component);

            return index;

        } else return TypeSection.referenceType(component.type, true);
    }

    encodeType(type, string, index) {

        /* This helper method takes a type expression node, the corresponding type
        string, and the index of the type expressed by the type expression. The
        helper encodes the type, pushing the bytes to the `payload` array, and
        then notes the expressed type in the `types` hash. */

        this.push(encodings.type);
        this.pushVector(type.params, token => encodings[token.type.value]);
        this.pushVector(type.results, token => encodings[token.type.value]);
        this.types[string] = index;
    }

    encode(statement) {

        /* This method takes a statement node that defines a new function-type, and
        updates this section instance accordingly, registering the identifier (when
        one is present) and the type, then encoding the type, pushing the bytes
        to the `payload` array. */

        const component = statement.component;
        const string = TypeSection.serializeTypeExpression(component.type);

        if (string in this.types) throw new DuplicateTypeError(component);
        else this.encodeType(component.type, string, component.index);
    }
}

class ImportSection extends VectorSection {

    /* A singleton class that implements the Import Section, which is a vector of
    core component imports. */

    encode(statement) {

        /* This method takes an import-statement node, encodes the module and field
        names, then passes the encoding of the component to a type specific method,
        based on what is being imported. */

        this.pushUTF8(statement.modulename);
        this.pushUTF8(statement.fieldname);
        this["encode_" + statement.component.name](statement);
    }

    encode_function(statement) {

        /* This method takes the statement passed to `encode`, when the component is
        a function. It registers the function and any identifier, then encodes it and
        updates the `payload` array, as well as the Type Section and Start Section,
        where required. */

        const component = statement.component;

        this.push(0x00, ...ULEB128(SECTIONS[1].resolveType(component)));

        if (component.start) SECTIONS[8].payload = component.index;
    }

    encode_table(statement) {

        /* This method handles the statement passed to `encode`, when the component
        is a table. */

        this.push(0x01, encodings[statement.component.type.value]);
        this.pushLimits(statement.component);
    }

    encode_memory(statement) {

        /* This method handles the statement passed to `encode`, when the component
        is a memory. */

        this.push(0x02);
        this.pushLimits(statement.component, statement.component.shared);
    }

    encode_register(statement) {

        /* This method handles the statement passed to `encode`, when the component
        is a register. */

        this.push(0x03, encodings[statement.component.type.value]);
        this.push(Number(not(statement.component.constant)));
    }
}

class ExportSection extends VectorSection {

    /* A singleton class that implements the Export Section, which is a vector
    of exports, each encoded to its fieldname, component type and identity. */

    encode(statement) {

        /* This method takes an export statement, and encodes it. */

        const {name, identity} = statement.component;

        this.pushUTF8(statement.fieldname);
        this.push(encodings[name], new Identity(name, identity));
    }
}

class FunctionSection extends VectorSection {

    /* A singleton class that implements the Function Section, a vector of
    function-type indicies, one for each locally defined function. */

    encode(statement) {

        /* This method encodes a function definition statement, updating the
        payload with the function type, and passing the statement node on to
        the `append` method of the Function Section, which encodes the local
        registers and instructions. */

        this.push(...ULEB128(SECTIONS[1].resolveType(statement.component)));
        SECTIONS[10].append(statement);
    }
}

class GlobalSection extends VectorSection {

    /* A singleton class that implements the Global Section, which is a vector of
    registers, encoded to their type and their constant expression block. */

    encode(statement) {

        /* This method takes a `DefineStatement` instance for a register definition,
        and encodes it, updating the `payload` array. The given statement will always
        include a constant expression, whether it is defined implicitly (and passed to
        `encodeInitializer`) or expressed fully (and passed to `pushExpression`). */

        const block = statement.component.block;

        this.push(encodings[statement.component.type.value]);
        this.push(Number(not(statement.component.constant)));

        if (block[0] instanceof Instruction) this.pushExpression(block);
        else this.encodeInitializer(statement.component);
    }

    encodeInitializer(component) {

        /* This helper method takes a register definition that either uses an implicit
        initializer (by omission) or uses the `as` prefix (instead of a proper constant
        expression). The parser represents these expressions by storing a single token
        in the `block` array (instead of one or more instructions).

        This method looks at the component (and especially the token stored in `block[0]`)
        to figure out which instruction is being implied, and encode it, before appending
        the `end` pseudo-instruction, to finalize the implied constant expression.

        A register with an implicit initializer stores its valtype. Numtype registers
        imply zero (using `const` operations), while reftype registers imply null (and
        use `ref.null` operations):

            define constant i32                 push i32 0          i32.const 0
            define constant i64                 push i64 0          i64.const 0
            define constant f32                 push f32 0          f32.const 0
            define constant f64                 push f64 0          f64.const 0
            define constant pointer             push null pointer   ref.null func
            define constant proxy               push null proxy     ref.null extern

        Numtype registers with an explicit initializer (expressed as a `NumberLiteral`)
        store the literal token. This implies a `const` operation of the same numtype,
        and using the number expressed by the literal:

            define constant i32 as 1            push i32 1          i32.const 1
            define constant i64 as 2            push i64 2          i64.const 2
            define constant f32 as 3.4          push f32 3.4        f32.const 3.4
            define constant f64 as 5.6          push f64 5.6        f64.const 5.6

        Pointer registers that imply a function reference with a `NumberLiteral` or an
        `Identifier` store the `NumberLiteral` or `Identifier` instance. This implies
        a `ref.func` operation, using the index expressed by the literal or bound to
        the identifier as the reference (excepting unbound identifiers). This looks
        just like the previous numtype examples:

            define constant pointer as 1        push pointer 1      ref.func 1
            define constant pointer as $foo     push pointer $foo   ref.func $foo

        Proxy registers cannot use the `as` keyword, as there is nothing to imply with a
        number literal, identifier, type *et cetera* that would make intuitive sense, so
        anything like that will have been rejected by the parser already:

            define constant proxy as <any>      ProxyIdentityError

        Note: The parser already validated the instruction, so invalid permutations of
        register type and implied instruction are not possible at this stage. */

        const encoders = {
            i32: SLEB128, i64: SLEB128, pointer: ULEB128,
            f32: n => IEEE754(32, n), f64: n => IEEE754(64, n)
        };

        const instruction = component.block[0];
        const valtype = component.type.value;
        const encode = encoders[valtype];

        if (instruction instanceof Primitive) {                     // implicit numtype

            this.push(opcodes.const[valtype], ...encode(0));

        } else if (instruction instanceof Identifier) {             // identifier

            const index = resolveIdentifier("function", instruction);

            this.push(opcodes.ref.func, ...ULEB128(index));

        } else if (instruction instanceof NumberLiteral) {          // number literal

            if (valtype === "pointer") this.push(opcodes.ref.func);
            else this.push(opcodes.const[valtype]);

            this.push(...encode(instruction));

        } else this.push(opcodes.ref.null, encodings[valtype]);     // implicit reftype

        this.push(encodings.end);
    }
}

class CodeSection extends VectorSection {

    /* A singleton class that implements the Code Section, which is a vector of
    code entries, which each combine a vector of locals with a block expression
    that together represent a function implementation.

    This class includes a static generator method for encoding any instruction,
    and another for encoding a constant expression (a block of instructions),
    both yielding the encoded byte-stream.

    This class also provides static generator methods for compiling each of the
    individual instructions. */

    constructor(id) {

        super(id);
        this.index = 0;             // the current function index
        this.localIndex = 0;        // the current local index
        this.locals = {};           // maps identifiers to local indices
        this.labels = [];           // stack that tracks the current labels
    }

    resolveLocal(identity) {

        /* This helper works like `resolveIdentity`, except that it operates on
        local registers. It takes an identity, and tries to return the index of
        the local that the identity is bound to, raising the appropriate error
        otherwise. */

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

        /* This helper generator takes a label, and returns its index, assuming
        that its is currently within scope, throwing an exception otherwise. */

        if (label instanceof NumberLiteral) {

            if (evaluateLiteral(label) < this.labels.length) return label;
            else throw new LabelIndexError(label);

        } else if (this.labels.includes(label.value)) {

            return this.labels.length - this.labels.indexOf(label.value) - 1;

        } else throw new UnboundLabelError(label);
    }

    * encodeInstruction(instruction) {

        /* This static helper method takes an instruction, and passes it on to the
        appropriate generator method (bound to the singleton instance of this class),
        yielding each of the bytes that are yielded by that method (which actually
        compiles the given instruction). */

        yield * SECTIONS[10][instruction.constructor.name](instruction);
    }

    * encodeExpression(block) {

        /* This static helper method takes a block of instructions, and encodes it (to
        a wasm-expression), yielding each of the bytes, including the `end` byte. */

        yield * block.map(function(instruction) {

            return Array.from(SECTIONS[10].encodeInstruction(instruction));

        }).flat().concat([encodings.end]);
    }

    * GETSET(instruction, set) {

        /* This helper handles the `get` and `set` mnemonics. It takes a bool that
        must be `true` for `set` instructions, and `false` for `get`. */

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

        /* This helper compiles the `is` and `not` mnemonics (except `is null`).
        It takes a reference to the instruction and a hash of options that maps
        each *test* ("more", "equal", "zero" *et cetera*) to a hash containing a
        pair of arrays, named `types` and `codes` (see `IS` and `NOT` to review
        the actual data structures). The opcode is selected and returned, using
        the `test` and `type` properties of the instruction to map the index of
        the type in the `types` array to the opcode in the `codes` array, based
        on whichever test the instruction performs. */

        const option = options[instruction.test.value];

        yield option.codes[option.types.indexOf(instruction.type.value)];
    }

    * GROWFILLSIZE(instruction, opcode) {

        /* This helper is used by the `GROW`, `FILL` and `SIZE` methods to encode
        the form common to those three instructions, that uses the 0xFC prefix, an
        Unsigned LEB128 encoded integer and a memory or table index. */

        const type = instruction.component.value;
        const identity = instruction.identity;

        yield * [0xFC, ...ULEB128(opcode), new Identity(type, identity)];
    }

    * ATOMICS(instruction, opcode) {

        /* This helper is used for all of the regular atomic instructions. It
        takes a reference to the instruction, and the opcode for its `i32`
        variant (the remaining opcodes are sequential and orderly). The
        compiled instruction is yielded bytewise. */

        const opcodes = {
            i32: [opcode, 0x02], i64: [opcode + 1, 0x03],
            i32u8: [opcode + 2, 0x00], i32u16: [opcode + 3, 0x01],
            i64u8: [opcode + 4, 0x00], i64u16: [opcode + 5, 0x01],
            i64u32: [opcode + 6, 0x02]
        };

        const key = instruction.type.value + (instruction.datatype?.value || "");

        yield * [0xFE, ...opcodes[key], ...ULEB128(instruction.offset)];
    }

    * BLOCKS(instruction, opcode) {

        /* This helper method compiles the block-instruction specified by the
        `opcode` argument (one of `block`, `loop` or `branch`), except for any
        `else` blocks of `branch` instructions, which are handled by `BRANCH`.

        The `labels` stack is updated (either with the instruction identifier
        or `undefined`), effectively recursively, pushing a label before the
        block is encoded, and popping the label afterwards.

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
        else yield * SLEB128(SECTIONS[1].resolveType(instruction));

        yield * SECTIONS[10].encodeExpression(instruction.block);

        // now the block has been encoded, remove the label from the stack...

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

        /* The compiler for the `push` mnemonic. */

        const {target, name} = instruction;

        if (name === "null") {              // push null <reftype>
                                            // ref.null <reftype>
            yield opcodes.ref.null;
            yield encodings[target.value];

        } else if (name === "pointer") {    // push pointer <function>
                                            // ref.func <function>
            yield opcodes.ref.func;
            yield new Identity("function", target);

        } else {                            // push [<numtype>] <number-literal>
                                            // <numtype>.const <number-literal>
            yield opcodes.const[name];

            if (["i32", "i64"].includes(name)) yield * SLEB128(target);
            else yield * IEEE754("f32" === name ? 32 : 64, target);
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

        /* This method compiles the `branch` instruction, including its optional
        else-block. It uses the `BLOCKS` helper to compile the branch-block with
        its type and block, while any else-block is compiled locally (replacing
        the `end` pseudo-instruction with the `else` pseudo-instruction, before
        encoding the the else-block). */

        const block = this.BLOCKS(instruction, 0x04);

        if (instruction.else) {

            yield * Array.from(block).slice(0, -1).concat([0x05]);
            yield * SECTIONS[10].encodeExpression(instruction.else.block);

        } else yield * block;
    }

    * JUMP(instruction) {

        /* The compiler for the `jump` instruction, which encodes to its
        opcode (0x0C) and its label index. */

        yield 0x0C;
        yield * ULEB128(this.resolveLabel(instruction.identity));
    }

    * FORK(instruction) {

        /* The compiler for the `fork` instruction, which encodes to its
        opcode (0x0D) and its label index. */

        yield 0x0D;
        yield * ULEB128(this.resolveLabel(instruction.identity));
    }

    * EXIT(instruction) {

        /* The compiler for the `exit` instruction, which is compiled to its
        opcode (0x0E), followed by a vector of label indices, followed by a
        single label index. */

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

        /* The compiler for the `invoke` (`call_indirect`) instruction. */

        yield 0x11;
        yield * ULEB128(SECTIONS[1].resolveType(instruction));
        yield new Identity("table", instruction.table);
    }

    * LOAD(instruction) {

        /* This method implements the compiler for the (non-atomic) `load`
        mnemonic. */

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

        /* This method implements the compiler for the (non-atomic) `store`
        mnemonic. */

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

        /* This is the compiler for the `select` instruction, which takes one optional
        valtype immediate, encoded (when present) as a vector (to allow for any future
        extension). The instruction uses two distinct opcodes, indicating whether the
        vector is included or not. */

        if (instruction.type === undefined) yield 0x1B;
        else yield * [0x1C, 0x01, encodings[instruction.type.value]];
    }

    * COPY(instruction) {

        /* This is the compiler for the `copy` mnemonic, which handles the WebAssembly
        `memory.copy`, `table.copy`, `memory.init` and `table.init` instructions. */

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

        /* This is the compiler for the `clz` (count leading zeros) instruction. */

        yield instruction.type.value === "i32" ? 0x67 : 0x79;
    }

    * CTZ(instruction) {

        /* This is the compiler for the `ctz` (count trailing zeros) instruction. */

        yield instruction.type.value === "i32" ? 0x68 : 0x7A;
    }

    * NSA(instruction) {

        /* This is the compiler for the `nsa` (population count) instruction, known
        as `popcnt` in WAT. */

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

        /* This is the compiler for the `cast` mnemonic (`reinterpret` in WAT). */

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

        yield opcodes[instruction.result.value][instruction.operand.value];
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

        /* The compiler for the `atomic broker` instruction (`cmpxchg` in WAT). */

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

        const key = instruction.type.value + (instruction.datatype?.value || "");

        yield * [0xFE, ...opcodes[key], ...ULEB128(instruction.offset)];
    }

    encode(statement) {

        /* This method is invoked by the `FunctionSection.encode` method once
        that method has registered the function type of the given function def-
        inition statement. This method first registers the function (using the
        index to update the Name Section), then encodes the locals and body of
        the function definition (in this section) as a wasm-code-entry. */

        const registerLocalRegister = node => {

            /* This internal helper takes a `node` that defines a local register
            (either a `ParamElement` or `LocalDefinition`). It always increments
            the `localIndex` property, before copying any identifier over to the
            `locals` property, with its local index. */

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

        // handle the params or type reference (whichever is present), then handle
        // any `local` directives (encoding them, and noting any identifiers)...

        if (type instanceof TypeExpression) type.params.forEach(registerLocalRegister);
        else this.localIndex = TypeSection.referenceType(type).params.length;

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
        limits of the table into the table section payload, before slicing
        any primer into one or more segments, before passing each to the
        Element Section for encoding. */

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

        /* This method takes a memory definition, and encodes the limits of the
        memory into the memory section payload, before slicing any primer into
        one or more segments, and passing each to the Data Section for encoding. */

        const {shared, primer, index} = statement.component;

        this.pushLimits(statement.component, shared);

        for (const segment of primer) new MemorySegment(index, segment);
    }
}

class DataSection extends VectorSection {

    /* A singleton class that implements the Data Section, which is a vector of
    memory segments (both active and passive), encoded to the memory's index, an
    offset into the memory (given as a constant expression), and then the bytes,
    encoded to an internal vector. */

    encode(segment) {

        /* This method takes a data segment (unlike most sections, which take a
        statement). The segment will either be a `MemoryBankSegment` (a passive
        segment) or a `MemorySegment` from a memory primer (an active segment).
        The method encodes the segment, before invoking the `append` method of
        the `DataCountSection` to increment the data segment count. */

        if (segment instanceof MemoryBankSegment) this.push(0x01);
        else this.push(0x02, ...ULEB128(segment.index), ...segment.expression);

        this.pushVector(segment.payload, this.encodeElement);
        SECTIONS[12].append(this);
    }

    encodeElement(element) {

        /* This method is used as a callback (for passing to `pushVector`) that
        takes and encodes a memory element from a memory primer or memory bank
        segment. The resulting bytes are returned as an `Array` (so the array
        can be flattened by the `pushVector` method). */

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

        /* This method takes a segment (a `TableSegment` or `TableBankSegment`)
        from a primer for a pointer table or a pointer bank (rather than taking
        a statement, as most sections do). The method encodes the segment. */

        if (segment instanceof TableBankSegment) this.push(0x05);
        else this.push(0x06, ...ULEB128(segment.index), ...segment.expression);

        this.push(encodings.pointer);
        this.pushVector(segment.payload, this.encodeElement, false);
    }

    encodeElement(element) {

        /* This helper method takes an element from a segment and returns the
        corresponding constant expression. Currently, the spec only permits
        pointers (which can be null) in table primers. */

        const nullref = reference => [opcodes.ref.null, reference, encodings.end];
        const funcref = reference => [opcodes.ref.func, reference, encodings.end];

        if (element.value.value === "null") return nullref(encodings.pointer);
        else return funcref(new Identity("function", element.value));
    }
}

class NameSection {

    /* This concrete class implements the Custom Name section of the binary, which
    preserves the URL of the module and most of the identifiers (used for Wasm to
    WAT conversion). The Locals Subsection and Labels Subsection have not been
    implemented yet.

    Note: The plan is to use DWARF to support source-level debugging in DevTools
    (with breakpoints *et cetera*). However, the Name Section will still always
    be supported, as it is independently useful. */

    constructor(id) {

        /* This constructor creates an empty `indexspaces` hash that is used to store
        data passed to the `append` method, and later used by the `compile` method to
        encode the section. The hash contains a hash for each component type, plus an
        extra hash for an indirect namemap that represents the locals within each of
        the functions. */

        this.id = id;
        this.label = 0; // used by `appendLabel` to track the current label index

        this.indexspaces = {
            register: {}, function: {}, memory: {}, table: {}, type: {},
            memorybank: {}, tablebank: {}, locals: {}, labels: {}
        };
    }

    static encodeName(name) {

        /* This static helper method takes an arbitrary Unicode string, encodes it
        as a wasm-name (a wasm-vector of UTF-8 bytes), then returns the result. */

        const bytes = Array.from(encodeUTF8(name));

        return ULEB128(bytes.length).concat(bytes);
    }

    append(type, identifier, index) {

        /* This helper method takes a component type name and an identifier, both
        as strings, and the corresponding index. It updates the `indexspaces` hash,
        before returning `undefined`. */

        this.indexspaces[type][identifier] = index;
    }

    appendLocals(index, locals) {

        /* This helper takes a function index (`index`), and a hash (`locals`) that
        maps any identifiers that are bound to locals (including params) within the
        function to the corresponding indices. The helper updates the `indexspaces`
        hash accordingly. */

        this.indexspaces.locals[index] = locals;
    }

    appendLabel(index, instruction) {

        /* This helper method takes a function index and a block-instruction. If the
        given function index has not been passed to a previous invocation, the helper
        will create a new hash for the current function in `indexspaces.labels`, and
        will reset the `labels` attribute to zero. Once that has been done, the ins-
        truction is checked for an identifier (a label), registers it when present,
        then increments the `label` attribute either way. */

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

        /* This helper method takes a subsection ID and a payload array, encodes
        the arguments into a subsection, then returns the result. */

        return [id].concat(ULEB128(payload.length)).concat(payload);
    }

    encodeNameMap(id, type) {

        /* This helper method takes a subsection ID and a type name. It uses them to
        reference the approriate `indexspaces` entry, and encodes the stored data as
        a wasm-namemap, before returning the result. */

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

        /* This helper method takes a subsection ID and a type name. It uses them to
        reference the approriate `indexspaces` entry, and encodes the stored data as
        a wasm-indirect-namemap, before returning the result. */

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

        /* This method compiles the instance to an array of bytes that represent
        the Custom Name Section of the binary, then returns the result. */

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

// global compiler functions...

const registerComponent = function(type, component, bind=false) {

    /* This helper takes an indexspace name, a component node and a bool that defaults to
    `false`. The helper pushes the component to the appropriate indexspace, and if the bool
    is truthy, its identifier is also bound to the new index. In either case, the index is
    returned. This allows imports and definitions to register the different the types of
    component that they introduce, and optionally bind their identifiers. */

    const index = INDEXSPACES.components[type].push(component) - 1;

    if (bind) registerIdentifier(type, component.identifier, index);

    return index;
};

const resolveComponent = function(type, index) {

    /* This helper takes a indexspace name and an index, and returns the corresponding
    component, or `undefined` if it does not exist. */

    return INDEXSPACES.components[type][index];
};

const registerIdentifier = function(type, node, index) {

    /* This helper takes an indexspace name, an identifier node (that may be `undefined`)
    and an index (as a Number). If the identifier is defined and unique within its index-
    space, it is bound to the given index in the given indexspace, and if the identifier
    is `undefined`, nothing happens. If it is a duplicate identifier, then an exception
    is raised. Otherwise, the function always returns `undefined`. */

    if (node === undefined) return;

    const [indexspace, identifier] = [INDEXSPACES.identifiers[type], node.value];

    if (indexspace[identifier] === undefined) indexspace[identifier] = index;
    else throw new DuplicateIdentifierError(node);

    SECTIONS[0].append(type, identifier, index); // update the custom name section
};

const resolveIdentifier = function(type, identifier) {

    /* This helper takes a indexspace name and an identifier, and then returns the
    corresponding index, or throws an exception if the identifer is not registered
    in the given indexspace. */

    const index = INDEXSPACES.identifiers[type][identifier.value];

    if (index === undefined) throw new UnboundIdentifierError(type, identifier);
    else return index;
};

const resolveIdentity = function(type, identity) {

    /* This helper takes a type and an identity (either a number literal or
    an identifier), and returns the expressed index (as a `Number`). */

    if (identity instanceof NumberLiteral) {

        const index = evaluateLiteral(identity);
        const bound = INDEXSPACES.components[type].length;

        if (index < bound) return index;
        else throw new UnboundIndexError(type, identity);

    } else return resolveIdentifier(type, identity);
}

const reset = function(configuration) {

    /* This is the generic reset helper for this module. It resets
    the compiler state, ready for a new source. */

    [SOURCE, URL] = [configuration.source, configuration.url];

    INDEXSPACES = {
        components: {
            register: [], function: [], type: [],
            memory: [], table: [], memorybank: [], tablebank: [],
        },
        identifiers: {
            register: {}, function: {}, type: {},
            memory: {}, table: {}, memorybank: {}, tablebank: {},
        }
    };

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
};

// numeric helper functions...

const ULEB128 = stack(function(push, pop, input) {

    /* This stack function takes an positive integer as a BigInt, an integer
    Number or a NumberLiteral token instance, encodes it using Unsigned LEB128,
    pushing each byte to the resulting array as a Number. */

    if (input instanceof NumberLiteral) input = evaluateLiteral(input, true);
    else input = BigInt(input);

    while(true) {

        const byte = input & 0x7Fn;

        input >>= 7n;

        if (input === 0n) return push(Number(byte));
        else push(Number(byte | 0x80n));
    }
});

const SLEB128 = stack(function(push, pop, input) {

    /* This stack function takes an integer (positive or negative) as a BigInt,
    and integer Number or a NumberLiteral token instance, and encodes it using
    Signed LEB128, pushing each byte to the resulting array as a Number. */

    const zero = () => input === 0n && (byte & 0x40n) === 0n;
    const ones = () => input === -1n && (byte & 0x40n) !== 0n;

    let byte;

    if (input instanceof NumberLiteral) input = evaluateLiteral(input, true);
    else input = BigInt(input);

    while (true) {

        byte = input & 0x7Fn;
        input >>= 7n;

        if (zero() || ones()) return push(Number(byte));
        else push(Number(byte | 0x80n));
    }
});

const IEEE754 = stack(function(push, pop, width, input) {

    /* This stack function takes a width (either `32` or `64`) and any Number or
    NumberLiteral instance, and encodes it as an IEEE floating point number of the
    given width, pushing each byte to the resulting array as a Number. */

    if (input instanceof NumberLiteral) input = evaluateLiteral(input, false);

    const FloatArray = width === 32 ? Float32Array : Float64Array;
    const buffer = new FloatArray([input]).buffer;
    const bytes = new Uint8Array(buffer, 0, width / 8);

    for (const byte of bytes) push(byte);
});

// the compiler entrypoint (which needs completely refactoring, once done)...

export const compile = function * (configuration) {

    // Stage Zero...

    reset(configuration);

    // Stage One...

    const statements = {imports: [], definitions: [], exports: []};

    for (const statement of parse(configuration)) {

        const component = statement.component;

        if (statement instanceof ImportStatement) {

            statements.imports.push(statement);

        } else if (statement instanceof ExportStatement) {

            statements.exports.push(statement);

        } else {

            if (component.name === "type") {

                component.index = registerComponent("type", component, true);
                SECTIONS[1].append(statement);

            } else if (component.name === "memorybank") {

                component.index = registerComponent("memorybank", component, true);
                new MemoryBankSegment(component.primer);

            } else if (component.name === "tablebank") {

                component.index = registerComponent("tablebank", component, true);
                new TableBankSegment(component.primer);

            } else statements.definitions.push(statement);
        }
    }

    // Stage Two...

    for (const statement of statements.imports) {

        const component = statement.component;

        component.index = registerComponent(component.name, component, true);
        SECTIONS[2].append(statement);
    }

    // Stage Three...

    for (const statement of statements.definitions) {

        const component = statement.component;
        const sections = {function: 3, table: 4, memory: 5, register: 6};

        if (component.name in sections) {

            component.index = registerComponent(component.name, component, true);
            SECTIONS[sections[component.name]].append(statement);
        }
    }

    // Stage Four...

    for (const statement of statements.exports) SECTIONS[7].append(statement);

    // Stage Five...

    yield * header;

    for (const id of sectionIDs) yield * SECTIONS[id].compile();
};

export default compile;
