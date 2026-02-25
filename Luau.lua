-- https://github.com/luau-lang/luau/raw/master/Common/include/Luau/Bytecode.h

local CASE_MULTIPLIER = 227 -- 0xE3

-- lookup table for type strings
local TYPE_NAMES = {
	[0] = "nil",
	[1] = "boolean",
	[2] = "number",
	[3] = "string",
	[4] = "table",
	[5] = "function",
	[6] = "thread",
	[7] = "userdata",
	[8] = "Vector3",
	[9] = "buffer",
	[15] = "any",
}

-- lookup table for builtin function names
-- indices match luaubuiltinfunction enum values
local BUILTIN_NAMES = {
	[0] = "none",
	[1] = "assert",
	-- math
	[2] = "math.abs", [3] = "math.acos", [4] = "math.asin", [5] = "math.atan2",
	[6] = "math.atan", [7] = "math.ceil", [8] = "math.cosh", [9] = "math.cos",
	[10] = "math.deg", [11] = "math.exp", [12] = "math.floor", [13] = "math.fmod",
	[14] = "math.frexp", [15] = "math.ldexp", [16] = "math.log10", [17] = "math.log",
	[18] = "math.max", [19] = "math.min", [20] = "math.modf", [21] = "math.pow",
	[22] = "math.rad", [23] = "math.sinh", [24] = "math.sin", [25] = "math.sqrt",
	[26] = "math.tanh", [27] = "math.tan",
	-- bit32
	[28] = "bit32.arshift", [29] = "bit32.band", [30] = "bit32.bnot", [31] = "bit32.bor",
	[32] = "bit32.bxor", [33] = "bit32.btest", [34] = "bit32.extract", [35] = "bit32.lrotate",
	[36] = "bit32.lshift", [37] = "bit32.replace", [38] = "bit32.rrotate", [39] = "bit32.rshift",
	-- type
	[40] = "type",
	-- string
	[41] = "string.byte", [42] = "string.char", [43] = "string.len",
	-- typeof
	[44] = "typeof",
	-- string.sub
	[45] = "string.sub",
	-- math extra
	[46] = "math.clamp", [47] = "math.sign", [48] = "math.round",
	-- raw*
	[49] = "rawset", [50] = "rawget", [51] = "rawequal",
	-- table
	[52] = "table.insert", [53] = "unpack",
	-- vector ctor
	[54] = "Vector3.new",
	-- bit32.count
	[55] = "bit32.countlz", [56] = "bit32.countrz",
	-- select
	[57] = "select",
	-- rawlen
	[58] = "rawlen",
	-- bit32.extract(_, k, k)
	[59] = "bit32.extract",
	-- metatable
	[60] = "getmetatable", [61] = "setmetatable",
	-- tonumber/tostring
	[62] = "tonumber", [63] = "tostring",
	-- bit32.byteswap
	[64] = "bit32.byteswap",
	-- buffer
	[65] = "buffer.readi8", [66] = "buffer.readu8", [67] = "buffer.writeu8",
	[68] = "buffer.readi16", [69] = "buffer.readu16", [70] = "buffer.writeu16",
	[71] = "buffer.readi32", [72] = "buffer.readu32", [73] = "buffer.writeu32",
	[74] = "buffer.readf32", [75] = "buffer.writef32",
	[76] = "buffer.readf64", [77] = "buffer.writef64",
	-- vector functions
	[78] = "vector.magnitude", [79] = "vector.normalize", [80] = "vector.cross",
	[81] = "vector.dot", [82] = "vector.floor", [83] = "vector.ceil",
	[84] = "vector.abs", [85] = "vector.sign", [86] = "vector.clamp",
	[87] = "vector.min", [88] = "vector.max",
	-- lerp
	[89] = "math.lerp", [90] = "vector.lerp",
	-- math checks
	[91] = "math.isnan", [92] = "math.isinf", [93] = "math.isfinite",
}

local Luau = {
	-- Bytecode opcode, part of the instruction header
	OpCode = {
		-- NOP: noop
		{ ["name"] = "NOP", ["type"] = "none" },

		-- BREAK: debugger break
		{ ["name"] = "BREAK", ["type"] = "none" },

		-- LOADNIL: sets register to nil
		-- A: target register
		{ ["name"] = "LOADNIL", ["type"] = "A" },

		-- LOADB: sets register to boolean and jumps to a given short offset (used to compile comparison results into a boolean)
		-- A: target register
		-- B: value (0/1)
		-- C: jump offset
		{ ["name"] = "LOADB", ["type"] = "ABC" },

		-- LOADN: sets register to a number literal
		-- A: target register
		-- D: value (-32768..32767)
		{ ["name"] = "LOADN", ["type"] = "AsD" },

		-- LOADK: sets register to an entry from the constant table from the proto (number/vector/string)
		-- A: target register
		-- D: constant table index (0..32767)
		{ ["name"] = "LOADK", ["type"] = "AD" },

		-- MOVE: move (copy) value from one register to another
		-- A: target register
		-- B: source register
		{ ["name"] = "MOVE", ["type"] = "AB" },

		-- GETGLOBAL: load value from global table using constant string as a key
		-- A: target register
		-- C: predicted slot index (based on hash)
		-- AUX: constant table index
		{ ["name"] = "GETGLOBAL", ["type"] = "AC", ["aux"] = true },

		-- SETGLOBAL: set value in global table using constant string as a key
		-- A: source register
		-- C: predicted slot index (based on hash)
		-- AUX: constant table index
		{ ["name"] = "SETGLOBAL", ["type"] = "AC", ["aux"] = true },

		-- GETUPVAL: load upvalue from the upvalue table for the current function
		-- A: target register
		-- B: upvalue index
		{ ["name"] = "GETUPVAL", ["type"] = "AB" },

		-- SETUPVAL: store value into the upvalue table for the current function
		-- A: target register
		-- B: upvalue index
		{ ["name"] = "SETUPVAL", ["type"] = "AB" },

		-- CLOSEUPVALS: close (migrate to heap) all upvalues that were captured for registers >= target
		-- A: target register
		{ ["name"] = "CLOSEUPVALS", ["type"] = "A" },

		-- GETIMPORT: load imported global table global from the constant table
		-- A: target register
		-- D: constant table index (0..32767); we assume that imports are loaded into the constant table
		-- AUX: 3 10-bit indices of constant strings that, combined, constitute an import path; length of the path is set by the top 2 bits (1,2,3)
		{ ["name"] = "GETIMPORT", ["type"] = "AD", ["aux"] = true },

		-- GETTABLE: load value from table into target register using key from register
		-- A: target register
		-- B: table register
		-- C: index register
		{ ["name"] = "GETTABLE", ["type"] = "ABC" },

		-- SETTABLE: store source register into table using key from register
		-- A: source register
		-- B: table register
		-- C: index register
		{ ["name"] = "SETTABLE", ["type"] = "ABC" },

		-- GETTABLEKS: load value from table into target register using constant string as a key
		-- A: target register
		-- B: table register
		-- C: predicted slot index (based on hash)
		-- AUX: constant table index
		{ ["name"] = "GETTABLEKS", ["type"] = "ABC", ["aux"] = true },

		-- SETTABLEKS: store source register into table using constant string as a key
		-- A: source register
		-- B: table register
		-- C: predicted slot index (based on hash)
		-- AUX: constant table index
		{ ["name"] = "SETTABLEKS", ["type"] = "ABC", ["aux"] = true },

		-- GETTABLEN: load value from table into target register using small integer index as a key
		-- A: target register
		-- B: table register
		-- C: index-1 (index is 1..256)
		{ ["name"] = "GETTABLEN", ["type"] = "ABC" },

		-- SETTABLEN: store source register into table using small integer index as a key
		-- A: source register
		-- B: table register
		-- C: index-1 (index is 1..256)
		{ ["name"] = "SETTABLEN", ["type"] = "ABC" },

		-- NEWCLOSURE: create closure from a child proto; followed by a CAPTURE instruction for each upvalue
		-- A: target register
		-- D: child proto index (0..32767)
		{ ["name"] = "NEWCLOSURE", ["type"] = "AD" },

		-- NAMECALL: prepare to call specified method by name by loading function from source register using constant index into target register and copying source register into target register + 1
		-- A: target register
		-- B: source register
		-- C: predicted slot index (based on hash)
		-- AUX: constant table index
		-- Note that this instruction must be followed directly by CALL; it prepares the arguments
		-- This instruction is roughly equivalent to GETTABLEKS + MOVE pair, but we need a special instruction to support custom __namecall metamethod
		{ ["name"] = "NAMECALL", ["type"] = "ABC", ["aux"] = true },

		-- CALL: call specified function
		-- A: register where the function object lives, followed by arguments; results are placed starting from the same register
		-- B: argument count + 1, or 0 to preserve all arguments up to top (MULTRET)
		-- C: result count + 1, or 0 to preserve all values and adjust top (MULTRET)
		{ ["name"] = "CALL", ["type"] = "ABC" },

		-- RETURN: returns specified values from the function
		-- A: register where the returned values start
		-- B: number of returned values + 1, or 0 to return all values up to top (MULTRET)
		{ ["name"] = "RETURN", ["type"] = "AB" },

		-- JUMP: jumps to target offset
		-- D: jump offset (-32768..32767; 0 means "next instruction" aka "don't jump")
		{ ["name"] = "JUMP", ["type"] = "sD" },

		-- JUMPBACK: jumps to target offset; this is equivalent to JUMP but is used as a safepoint to be able to interrupt while/repeat loops
		-- D: jump offset (-32768..32767; 0 means "next instruction" aka "don't jump")
		{ ["name"] = "JUMPBACK", ["type"] = "sD" },

		-- JUMPIF: jumps to target offset if register is not nil/false
		-- A: source register
		-- D: jump offset (-32768..32767; 0 means "next instruction" aka "don't jump")
		{ ["name"] = "JUMPIF", ["type"] = "AsD" },

		-- JUMPIFNOT: jumps to target offset if register is nil/false
		-- A: source register
		-- D: jump offset (-32768..32767; 0 means "next instruction" aka "don't jump")
		{ ["name"] = "JUMPIFNOT", ["type"] = "AsD" },

		-- JUMPIFEQ, JUMPIFLE, JUMPIFLT, JUMPIFNOTEQ, JUMPIFNOTLE, JUMPIFNOTLT: jumps to target offset if the comparison is true (or false, for NOT variants)
		-- A: source register 1
		-- D: jump offset (-32768..32767; 1 means "next instruction" aka "don't jump")
		-- AUX: source register 2
		{ ["name"] = "JUMPIFEQ", ["type"] = "AsD", ["aux"] = true },
		{ ["name"] = "JUMPIFLE", ["type"] = "AsD", ["aux"] = true },
		{ ["name"] = "JUMPIFLT", ["type"] = "AsD", ["aux"] = true },
		{ ["name"] = "JUMPIFNOTEQ", ["type"] = "AsD", ["aux"] = true },
		{ ["name"] = "JUMPIFNOTLE", ["type"] = "AsD", ["aux"] = true },
		{ ["name"] = "JUMPIFNOTLT", ["type"] = "AsD", ["aux"] = true },

		-- ADD, SUB, MUL, DIV, MOD, POW: compute arithmetic operation between two source registers and put the result into target register
		-- A: target register
		-- B: source register 1
		-- C: source register 2
		{ ["name"] = "ADD", ["type"] = "ABC" },
		{ ["name"] = "SUB", ["type"] = "ABC" },
		{ ["name"] = "MUL", ["type"] = "ABC" },
		{ ["name"] = "DIV", ["type"] = "ABC" },
		{ ["name"] = "MOD", ["type"] = "ABC" },
		{ ["name"] = "POW", ["type"] = "ABC" },

		-- ADDK, SUBK, MULK, DIVK, MODK, POWK: compute arithmetic operation between the source register and a constant and put the result into target register
		-- A: target register
		-- B: source register
		-- C: constant table index (0..255); must refer to a number
		{ ["name"] = "ADDK", ["type"] = "ABC" },
		{ ["name"] = "SUBK", ["type"] = "ABC" },
		{ ["name"] = "MULK", ["type"] = "ABC" },
		{ ["name"] = "DIVK", ["type"] = "ABC" },
		{ ["name"] = "MODK", ["type"] = "ABC" },
		{ ["name"] = "POWK", ["type"] = "ABC" },

		-- AND, OR: perform `and` or `or` operation (selecting first or second register based on whether the first one is truthy) and put the result into target register
		-- A: target register
		-- B: source register 1
		-- C: source register 2
		{ ["name"] = "AND", ["type"] = "ABC" },
		{ ["name"] = "OR", ["type"] = "ABC" },

		-- ANDK, ORK: perform `and` or `or` operation (selecting source register or constant based on whether the source register is truthy) and put the result into target register
		-- A: target register
		-- B: source register
		-- C: constant table index (0..255)
		{ ["name"] = "ANDK", ["type"] = "ABC" },
		{ ["name"] = "ORK", ["type"] = "ABC" },

		-- CONCAT: concatenate all strings between B and C (inclusive) and put the result into A
		-- A: target register
		-- B: source register start
		-- C: source register end
		{ ["name"] = "CONCAT", ["type"] = "ABC" },

		-- NOT, MINUS, LENGTH: compute unary operation for source register and put the result into target register
		-- A: target register
		-- B: source register
		{ ["name"] = "NOT", ["type"] = "AB" },
		{ ["name"] = "MINUS", ["type"] = "AB" },
		{ ["name"] = "LENGTH", ["type"] = "AB" },

		-- NEWTABLE: create table in target register
		-- A: target register
		-- B: table size, stored as 0 for v=0 and ceil(log2(v))+1 for v!=0
		-- AUX: array size
		{ ["name"] = "NEWTABLE", ["type"] = "AB", ["aux"] = true },

		-- DUPTABLE: duplicate table using the constant table template to target register
		-- A: target register
		-- D: constant table index (0..32767)
		{ ["name"] = "DUPTABLE", ["type"] = "AD" },

		-- SETLIST: set a list of values to table in target register
		-- A: target register
		-- B: source register start
		-- C: value count + 1, or 0 to use all values up to top (MULTRET)
		-- AUX: table index to start from
		{ ["name"] = "SETLIST", ["type"] = "ABC", ["aux"] = true },

		-- FORNPREP: prepare a numeric for loop, jump over the loop if first iteration doesn't need to run
		-- A: target register; numeric for loops assume a register layout [limit, step, index, variable]
		-- D: jump offset (-32768..32767)
		-- limit/step are immutable, index isn't visible to user code since it's copied into variable
		{ ["name"] = "FORNPREP", ["type"] = "AsD" },

		-- FORNLOOP: adjust loop variables for one iteration, jump back to the loop header if loop needs to continue
		-- A: target register; see FORNPREP for register layout
		-- D: jump offset (-32768..32767)
		{ ["name"] = "FORNLOOP", ["type"] = "AsD" },

		-- FORGLOOP: adjust loop variables for one iteration of a generic for loop, jump back to the loop header if loop needs to continue
		-- A: target register; generic for loops assume a register layout [generator, state, index, variables...]
		-- D: jump offset (-32768..32767)
		-- AUX: variable count (1..255) in the low 8 bits, high bit indicates whether to use ipairs-style traversal in the fast path
		-- loop variables are adjusted by calling generator(state, index) and expecting it to return a tuple that's copied to the user variables
		-- the first variable is then copied into index; generator/state are immutable, index isn't visible to user code
		{ ["name"] = "FORGLOOP", ["type"] = "AsD", ["aux"] = true },

		-- FORGPREP_INEXT: prepare FORGLOOP with 2 output variables (no AUX encoding), assuming generator is luaB_inext, and jump to FORGLOOP
		-- A: target register (see FORGLOOP for register layout)
		-- D: jump offset (-32768..32767)
		{ ["name"] = "FORGPREP_INEXT", ["type"] = "AsD" },

		-- FASTCALL3: perform a fast call of a built-in function using 3 register arguments
		-- A: builtin function id (see LuauBuiltinFunction)
		-- B: source argument register
		-- C: jump offset to get to following CALL
		-- AUX: source register 2 in least-significant byte
		-- AUX: source register 3 in second least-significant byte
		{ ["name"] = "FASTCALL3", ["type"] = "ABC", ["aux"] = true },

		-- FORGPREP_NEXT: prepare FORGLOOP with 2 output variables (no AUX encoding), assuming generator is luaB_next, and jump to FORGLOOP
		-- A: target register (see FORGLOOP for register layout)
		-- D: jump offset (-32768..32767)
		{ ["name"] = "FORGPREP_NEXT", ["type"] = "AsD" },

		-- NATIVECALL: start executing new function in native code
		-- this is a pseudo-instruction that is never emitted by bytecode compiler, but can be constructed at runtime to accelerate native code dispatch
		{ ["name"] = "NATIVECALL", ["type"] = "none" },

		-- GETVARARGS: copy variables into the target register from vararg storage for current function
		-- A: target register
		-- B: variable count + 1, or 0 to copy all variables and adjust top (MULTRET)
		{ ["name"] = "GETVARARGS", ["type"] = "AB" },

		-- DUPCLOSURE: create closure from a pre-created function object (reusing it unless environments diverge)
		-- A: target register
		-- D: constant table index (0..32767)
		{ ["name"] = "DUPCLOSURE", ["type"] = "AD" },

		-- PREPVARARGS: prepare stack for variadic functions so that GETVARARGS works correctly
		-- A: number of fixed arguments
		{ ["name"] = "PREPVARARGS", ["type"] = "A" },

		-- LOADKX: sets register to an entry from the constant table from the proto (number/string)
		-- A: target register
		-- AUX: constant table index
		{ ["name"] = "LOADKX", ["type"] = "A", ["aux"] = true },

		-- JUMPX: jumps to the target offset; like JUMPBACK, supports interruption
		-- E: jump offset (-2^23..2^23; 0 means "next instruction" aka "don't jump")
		{ ["name"] = "JUMPX", ["type"] = "E" },

		-- FASTCALL: perform a fast call of a built-in function
		-- A: builtin function id (see LuauBuiltinFunction)
		-- C: jump offset to get to following CALL
		-- FASTCALL is followed by one of (GETIMPORT, MOVE, GETUPVAL) instructions and by CALL instruction
		-- This is necessary so that if FASTCALL can't perform the call inline, it can continue normal execution
		-- If FASTCALL *can* perform the call, it jumps over the instructions *and* over the next CALL
		-- Note that FASTCALL will read the actual call arguments, such as argument/result registers and counts, from the CALL instruction
		{ ["name"] = "FASTCALL", ["type"] = "AC" },

		-- COVERAGE: update coverage information stored in the instruction
		-- E: hit count for the instruction (0..2^23-1)
		-- The hit count is incremented by VM every time the instruction is executed, and saturates at 2^23-1
		{ ["name"] = "COVERAGE", ["type"] = "E" },

		-- CAPTURE: capture a local or an upvalue as an upvalue into a newly created closure; only valid after NEWCLOSURE
		-- A: capture type, see LuauCaptureType
		-- B: source register (for VAL/REF) or upvalue index (for UPVAL/UPREF)
		{ ["name"] = "CAPTURE", ["type"] = "AB" },

		-- SUBRK, DIVRK: compute arithmetic operation between the constant and a source register and put the result into target register
		-- A: target register
		-- B: constant table index (0..255); must refer to a number
		-- C: source register
		{ ["name"] = "SUBRK", ["type"] = "ABC" },
		{ ["name"] = "DIVRK", ["type"] = "ABC" },

		-- FASTCALL1: perform a fast call of a built-in function using 1 register argument
		-- A: builtin function id (see LuauBuiltinFunction)
		-- B: source argument register
		-- C: jump offset to get to following CALL
		{ ["name"] = "FASTCALL1", ["type"] = "ABC" },

		-- FASTCALL2: perform a fast call of a built-in function using 2 register arguments
		-- A: builtin function id (see LuauBuiltinFunction)
		-- B: source argument register
		-- C: jump offset to get to following CALL
		-- AUX: source register 2 in least-significant byte
		{ ["name"] = "FASTCALL2", ["type"] = "ABC", ["aux"] = true },

		-- FASTCALL2K: perform a fast call of a built-in function using 1 register argument and 1 constant argument
		-- A: builtin function id (see LuauBuiltinFunction)
		-- B: source argument register
		-- C: jump offset to get to following CALL
		-- AUX: constant index
		{ ["name"] = "FASTCALL2K", ["type"] = "ABC", ["aux"] = true },

		-- FORGPREP: prepare loop variables for a generic for loop, jump to the loop backedge unconditionally
		-- A: target register; generic for loops assume a register layout [generator, state, index, variables...]
		-- D: jump offset (-32768..32767)
		{ ["name"] = "FORGPREP", ["type"] = "AsD" },

		-- JUMPXEQKNIL, JUMPXEQKB: jumps to target offset if the comparison with constant is true (or false, see AUX)
		-- A: source register 1
		-- D: jump offset (-32768..32767; 1 means "next instruction" aka "don't jump")
		-- AUX: constant value (for boolean) in low bit, NOT flag (that flips comparison result) in high bit
		{ ["name"] = "JUMPXEQKNIL", ["type"] = "AsD", ["aux"] = true },
		{ ["name"] = "JUMPXEQKB", ["type"] = "AsD", ["aux"] = true },

		-- JUMPXEQKN, JUMPXEQKS: jumps to target offset if the comparison with constant is true (or false, see AUX)
		-- A: source register 1
		-- D: jump offset (-32768..32767; 1 means "next instruction" aka "don't jump")
		-- AUX: constant table index in low 24 bits, NOT flag (that flips comparison result) in high bit
		{ ["name"] = "JUMPXEQKN", ["type"] = "AsD", ["aux"] = true },
		{ ["name"] = "JUMPXEQKS", ["type"] = "AsD", ["aux"] = true },

		-- IDIV: compute floor division between two source registers and put the result into target register
		-- A: target register
		-- B: source register 1
		-- C: source register 2
		{ ["name"] = "IDIV", ["type"] = "ABC" },

		-- IDIVK compute floor division between the source register and a constant and put the result into target register
		-- A: target register
		-- B: source register
		-- C: constant table index (0..255)
		{ ["name"] = "IDIVK", ["type"] = "ABC" },

		-- Enum entry for number of opcodes, not a valid opcode by itself!
		{ ["name"] = "_COUNT", ["type"] = "none" }
	},
	-- bytecode tags, used internally for bytecode encoded as a string
	BytecodeTag = {
		-- bytecode version; runtime supports [MIN, MAX], compiler emits TARGET by default but may emit a higher version when flags are enabled
		LBC_VERSION_MIN = 3,
		LBC_VERSION_MAX = 6,
		LBC_VERSION_TARGET = 6,
		-- type encoding version
		LBC_TYPE_VERSION_MIN = 1,
		LBC_TYPE_VERSION_MAX = 3,
		LBC_TYPE_VERSION_TARGET = 3,
		-- types of constant table entries
		LBC_CONSTANT_NIL = 0,
		LBC_CONSTANT_BOOLEAN = 1,
		LBC_CONSTANT_NUMBER = 2,
		LBC_CONSTANT_STRING = 3,
		LBC_CONSTANT_IMPORT = 4,
		LBC_CONSTANT_TABLE = 5,
		LBC_CONSTANT_CLOSURE = 6,
		LBC_CONSTANT_VECTOR = 7
	},
	-- type table tags
	BytecodeType = {
		LBC_TYPE_NIL = 0,
		LBC_TYPE_BOOLEAN = 1,
		LBC_TYPE_NUMBER = 2,
		LBC_TYPE_STRING = 3,
		LBC_TYPE_TABLE = 4,
		LBC_TYPE_FUNCTION = 5,
		LBC_TYPE_THREAD = 6,
		LBC_TYPE_USERDATA = 7,
		LBC_TYPE_VECTOR = 8,
		LBC_TYPE_BUFFER = 9,

		LBC_TYPE_ANY = 15,

		LBC_TYPE_TAGGED_USERDATA_BASE = 64,
		LBC_TYPE_TAGGED_USERDATA_END = 64 + 32,

		LBC_TYPE_OPTIONAL_BIT = bit32.lshift(1, 7), -- 128

		LBC_TYPE_INVALID = 256
	},
	-- capture type, used in LOP_CAPTURE
	CaptureType = {
		LCT_VAL = 0,
		LCT_REF = 1,
		LCT_UPVAL = 2
	},
	-- builtin function ids, used in LOP_FASTCALL
	BuiltinFunction = {
		LBF_NONE = 0,
		LBF_ASSERT = 1,

		-- math
		LBF_MATH_ABS = 2,
		LBF_MATH_ACOS = 3,
		LBF_MATH_ASIN = 4,
		LBF_MATH_ATAN2 = 5,
		LBF_MATH_ATAN = 6,
		LBF_MATH_CEIL = 7,
		LBF_MATH_COSH = 8,
		LBF_MATH_COS = 9,
		LBF_MATH_DEG = 10,
		LBF_MATH_EXP = 11,
		LBF_MATH_FLOOR = 12,
		LBF_MATH_FMOD = 13,
		LBF_MATH_FREXP = 14,
		LBF_MATH_LDEXP = 15,
		LBF_MATH_LOG10 = 16,
		LBF_MATH_LOG = 17,
		LBF_MATH_MAX = 18,
		LBF_MATH_MIN = 19,
		LBF_MATH_MODF = 20,
		LBF_MATH_POW = 21,
		LBF_MATH_RAD = 22,
		LBF_MATH_SINH = 23,
		LBF_MATH_SIN = 24,
		LBF_MATH_SQRT = 25,
		LBF_MATH_TANH = 26,
		LBF_MATH_TAN = 27,

		-- bit32
		LBF_BIT32_ARSHIFT = 28,
		LBF_BIT32_BAND = 29,
		LBF_BIT32_BNOT = 30,
		LBF_BIT32_BOR = 31,
		LBF_BIT32_BXOR = 32,
		LBF_BIT32_BTEST = 33,
		LBF_BIT32_EXTRACT = 34,
		LBF_BIT32_LROTATE = 35,
		LBF_BIT32_LSHIFT = 36,
		LBF_BIT32_REPLACE = 37,
		LBF_BIT32_RROTATE = 38,
		LBF_BIT32_RSHIFT = 39,

		-- type
		LBF_TYPE = 40,

		-- string
		LBF_STRING_BYTE = 41,
		LBF_STRING_CHAR = 42,
		LBF_STRING_LEN = 43,

		-- typeof
		LBF_TYPEOF = 44,

		-- string.sub
		LBF_STRING_SUB = 45,

		-- math extra
		LBF_MATH_CLAMP = 46,
		LBF_MATH_SIGN = 47,
		LBF_MATH_ROUND = 48,

		-- raw*
		LBF_RAWSET = 49,
		LBF_RAWGET = 50,
		LBF_RAWEQUAL = 51,

		-- table
		LBF_TABLE_INSERT = 52,
		LBF_TABLE_UNPACK = 53,

		-- vector ctor
		LBF_VECTOR = 54,

		-- bit32.count
		LBF_BIT32_COUNTLZ = 55,
		LBF_BIT32_COUNTRZ = 56,

		-- select(_, ...)
		LBF_SELECT_VARARG = 57,

		-- rawlen
		LBF_RAWLEN = 58,

		-- bit32.extract(_, k, k)
		LBF_BIT32_EXTRACTK = 59,

		-- get/setmetatable
		LBF_GETMETATABLE = 60,
		LBF_SETMETATABLE = 61,

		-- tonumber/tostring
		LBF_TONUMBER = 62,
		LBF_TOSTRING = 63,

		-- bit32.byteswap
		LBF_BIT32_BYTESWAP = 64,

		-- buffer
		LBF_BUFFER_READI8 = 65,
		LBF_BUFFER_READU8 = 66,
		LBF_BUFFER_WRITEU8 = 67,
		LBF_BUFFER_READI16 = 68,
		LBF_BUFFER_READU16 = 69,
		LBF_BUFFER_WRITEU16 = 70,
		LBF_BUFFER_READI32 = 71,
		LBF_BUFFER_READU32 = 72,
		LBF_BUFFER_WRITEU32 = 73,
		LBF_BUFFER_READF32 = 74,
		LBF_BUFFER_WRITEF32 = 75,
		LBF_BUFFER_READF64 = 76,
		LBF_BUFFER_WRITEF64 = 77,

		-- vector functions
		LBF_VECTOR_MAGNITUDE = 78,
		LBF_VECTOR_NORMALIZE = 79,
		LBF_VECTOR_CROSS = 80,
		LBF_VECTOR_DOT = 81,
		LBF_VECTOR_FLOOR = 82,
		LBF_VECTOR_CEIL = 83,
		LBF_VECTOR_ABS = 84,
		LBF_VECTOR_SIGN = 85,
		LBF_VECTOR_CLAMP = 86,
		LBF_VECTOR_MIN = 87,
		LBF_VECTOR_MAX = 88,

		-- math.lerp
		LBF_MATH_LERP = 89,

		LBF_VECTOR_LERP = 90,

		-- math checks
		LBF_MATH_ISNAN = 91,
		LBF_MATH_ISINF = 92,
		LBF_MATH_ISFINITE = 93,
	},
	-- proto flag bitmask, stored in proto::flags
	ProtoFlag = {
		-- used to tag main proto for modules with --!native
		LPF_NATIVE_MODULE = bit32.lshift(1, 0),
		-- used to tag individual protos as not profitable to compile natively
		LPF_NATIVE_COLD = bit32.lshift(1, 1),
		-- used to tag main proto for modules that have at least one function with native attribute
		LPF_NATIVE_FUNCTION = bit32.lshift(1, 2)
	}
}

-- bytecode instruction header: it's always a 32-bit integer, with low byte (first byte in little endian) containing the opcode
-- some instruction types require more data and have more 32-bit integers following the header
function Luau:INSN_OP(insn)
	return bit32.band(insn, 0xFF)
end

-- ABC encoding: three 8-bit values, containing registers or small numbers
function Luau:INSN_A(insn)
	return bit32.band(bit32.rshift(insn, 8), 0xFF)
end
function Luau:INSN_B(insn)
	return bit32.band(bit32.rshift(insn, 16), 0xFF)
end
function Luau:INSN_C(insn)
	return bit32.band(bit32.rshift(insn, 24), 0xFF)
end

-- AD encoding: one 8-bit value, one signed 16-bit value
function Luau:INSN_D(insn) -- (0..32767)
	return bit32.rshift(insn, 16)
end
function Luau:INSN_sD(insn) -- (-32768..32767)
	local D = Luau:INSN_D(insn)
	local sD = D
	if D > 0x7FFF and D <= 0xFFFF then
		sD = (-(0xFFFF - D)) - 1
	end
	return sD
end

-- E encoding: one signed 24-bit value
function Luau:INSN_E(insn)
	return bit32.arshift(bit32.lshift(insn, 8), 8)
end

-- type to string for typeinfo
function Luau:GetBaseTypeString(type, checkOptional)
	local LuauBytecodeType = Luau.BytecodeType
	local tag = bit32.band(type, bit32.bnot(LuauBytecodeType.LBC_TYPE_OPTIONAL_BIT))

	local result = TYPE_NAMES[tag]

	if not result then
		error("Unhandled type in GetBaseTypeString", 2)
	end

	if checkOptional then
		local optional = bit32.band(type, LuauBytecodeType.LBC_TYPE_OPTIONAL_BIT) == 0 and "" or "?"
		result ..= optional
	end

	return result
end

-- Id provided by LOP_NAMECALL to function string representation
function Luau:GetBuiltinInfo(bfid)
	return BUILTIN_NAMES[bfid] or "none"
end

-- finalize
local function prepare(t)
	local function reconstruct(original, fn)
		local new = {}
		for i, v in original do
			fn(new, i, v)
		end
		return new
	end

	local LuauOpCode = t.OpCode

	-- assign opcodes their case number
	t.OpCode = reconstruct(LuauOpCode, function(self, i, v)
		local case = bit32.band((i - 1)*CASE_MULTIPLIER, 0xFF)
		self[case] = v
	end)

	return t
end

return prepare(Luau)
