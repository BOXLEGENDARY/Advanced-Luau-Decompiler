--!optimize 2
--!nolint UnknownGlobal

local ENABLED_REMARKS = {
	COLD_REMARK = false,
	INLINE_REMARK = false -- currently unused
}
------------------------------------------------------------------------------------------------------------------------------------------------------------------------
local DECOMPILER_TIMEOUT = 2 -- seconds
local READER_FLOAT_PRECISION = 7 -- up to 99
local DECOMPILER_MODE = "optdec" -- disasm/optdec
local SHOW_DEBUG_INFORMATION = true -- show trivial function and array allocation details
local SHOW_INSTRUCTION_LINES = true -- show lines as they are in the source code
local SHOW_OPERATION_NAMES = true
local SHOW_OPERATION_INDEX = true -- show instruction index. used in jumps #n.
local SHOW_TRIVIAL_OPERATIONS = true
local USE_TYPE_INFO = true -- allow adding types to function parameters (ex. p1: string, p2: number)
local LIST_USED_GLOBALS = true -- list all (non-Roblox!!) globals used in the script as a top comment
local RETURN_ELAPSED_TIME = true -- return time it took to finish processing the bytecode
local DECODE_AS_BASE64 = false -- Decodes the bytecode as base64 if it's returned as such.
local USE_IN_STUDIO = false -- Toggles Roblox Studio mode, which allows for this to be used in
------------------------------------------------------------------------------------------------------------------------------------------------------------------------

-- For studio, put your bytecode here.
local input = ``

local LoadFromUrl

if USE_IN_STUDIO then
	-- A bit of an annoying thing, but I don't want 2 separate names for this
	LoadFromUrl = function(moduleName)
		return require(workspace["Disassembler"][moduleName])
	end
else
	LoadFromUrl = function(x)
		local BASE_USER = "BOXLEGENDARY"
		local BASE_BRANCH = "main"
		local BASE_URL = "https://raw.githubusercontent.com/%s/Advanced-Luau-Decompiler/%s/%s.lua"

		local loadSuccess, loadResult = pcall(function()
			local formattedUrl = string.format(BASE_URL, BASE_USER, BASE_BRANCH, x)
			return game:HttpGet(formattedUrl, true)
		end)

		if not loadSuccess then
			warn(`({math.random()}) MОDULE FАILЕD ТO LOАD FRОM URL: {loadResult}.`)
			return
		end

		local success, result = pcall(loadstring, loadResult)
		if not success then
			warn(`({math.random()}) MОDULE FАILЕD ТO LOАDSТRING: {result}.`)
			return
		end

		if type(result) ~= "function" then
			warn(`MОDULE IS {tostring(result)} (function expected)`)
			return
		end

		return result()
	end
end
local Implementations = LoadFromUrl("Implementations")
local Reader = LoadFromUrl("Reader")
local Strings = LoadFromUrl("Strings")
local Luau = LoadFromUrl("Luau")
local Base64 = LoadFromUrl("Base64")

local function LoadFlag(name)
	local success, result = pcall(function()
		return game:GetFastFlag(name)
	end)

	if success then
		return result
	end

	return true -- assume the test ended and it was successful
end
local LuauCompileUserdataInfo = LoadFlag("LuauCompileUserdataInfo")

local LuauOpCode = Luau.OpCode
local LuauBytecodeTag = Luau.BytecodeTag
local LuauBytecodeType = Luau.BytecodeType
local LuauCaptureType = Luau.CaptureType
local LuauBuiltinFunction = Luau.BuiltinFunction
local LuauProtoFlag = Luau.ProtoFlag

local toBoolean = Implementations.toBoolean
local toEscapedString = Implementations.toEscapedString
local formatIndexString = Implementations.formatIndexString
local padLeft = Implementations.padLeft
local padRight = Implementations.padRight
local isGlobal = Implementations.isGlobal

Reader:Set(READER_FLOAT_PRECISION)

local function Decompile(bytecode)
	local bytecodeVersion, typeEncodingVersion

	local reader = Reader.new(bytecode)

	-- step 1: collect information from the bytecode
	local function disassemble()
		if bytecodeVersion >= 4 then
			-- type encoding did not exist before this version
			typeEncodingVersion = reader:nextByte()
		end

		local stringTable = {}
		local function readStringTable()
			local amountOfStrings = reader:nextVarInt() -- or, well, stringTable size.
			for i = 1, amountOfStrings do
				stringTable[i] = reader:nextString()
			end
		end

		local userdataTypes = {}
		local function readUserdataTypes()
			if LuauCompileUserdataInfo then
				while true do
					local index = reader:nextByte()
					if index == 0 then
						-- zero marks the end of type mapping
						break
					end

					local nameRef = reader:nextVarInt()
					userdataTypes[index] = nameRef
				end
			end
		end

		local protoTable = {}
		local function readProtoTable()
			local amountOfProtos = reader:nextVarInt() -- or protoTable size
			for i = 1, amountOfProtos do
				local protoId = i - 1 -- account for main proto

				local proto = {
					id = protoId,

					instructions = {},
					constants = {},
					captures = {}, -- upvalue references
					innerProtos = {},

					instructionLineInfo = {}
				}
				protoTable[protoId] = proto

				-- read header
				proto.maxStackSize = reader:nextByte()
				proto.numParams = reader:nextByte()
				proto.numUpvalues = reader:nextByte()
				proto.isVarArg = toBoolean(reader:nextByte())

				-- read flags and typeInfo if bytecode version includes that information
				if bytecodeVersion >= 4 then
					proto.flags = reader:nextByte()

					-- collect type info
					local resultTypedParams = {}
					local resultTypedUpvalues = {}
					local resultTypedLocals = {}

					-- refer to: https://github.com/luau-lang/luau/blob/0.655/Compiler/src/BytecodeBuilder.cpp#L752
					local allTypeInfoSize = reader:nextVarInt()

					local hasTypeInfo = allTypeInfoSize > 0 -- we don't have any type info if the size is zero.
					proto.hasTypeInfo = hasTypeInfo

					if hasTypeInfo then
						local totalTypedParams = allTypeInfoSize
						local totalTypedUpvalues = 0
						local totalTypedLocals = 0

						if typeEncodingVersion > 1 then
							-- much more info is encoded in next versions
							totalTypedParams = reader:nextVarInt()
							totalTypedUpvalues = reader:nextVarInt()
							totalTypedLocals = reader:nextVarInt()
						end

						local function readTypedParams()
							local typedParams = resultTypedParams
							if totalTypedParams > 0 then
								typedParams = reader:nextBytes(totalTypedParams) -- array of uint8
								-- first value is always "function"
								-- we don't care about that.
								table.remove(typedParams, 1)
								-- second value is the amount of typed params
								table.remove(typedParams, 1)
							end
							return typedParams
						end
						local function readTypedUpvalues()
							local typedUpvalues = resultTypedUpvalues
							if totalTypedUpvalues > 0 then
								for i = 1, totalTypedUpvalues do
									local upvalueType = reader:nextByte()

									-- info on the upvalue at index `i`
									local info = {
										type = upvalueType
									}
									typedUpvalues[i] = info
								end
							end
							return typedUpvalues
						end
						local function readTypedLocals()
							local typedLocals = resultTypedLocals
							if totalTypedLocals > 0 then
								for i = 1, totalTypedLocals do
									local localType = reader:nextByte()
									-- Register is locals' place in the stack
									local localRegister = reader:nextByte() -- accounts for function params!
									-- PC - Program Counter
									local localStartPC = reader:nextVarInt() + 1
									-- refer to: https://github.com/luau-lang/luau/blob/0.655/Compiler/src/BytecodeBuilder.cpp#L749
									-- if you want to know why we get endPC like that
									local localEndPC = reader:nextVarInt() + localStartPC - 1

									-- info on the local at index `i`
									local info = {
										type = localType,
										register = localRegister,
										startPC = localStartPC,
										endPC = localEndPC -- unused in the disassembler
									}
									typedLocals[i] = info
								end
							end
							return typedLocals
						end

						resultTypedParams = readTypedParams()
						resultTypedUpvalues = readTypedUpvalues()
						resultTypedLocals = readTypedLocals()
					end

					proto.typedParams = resultTypedParams
					proto.typedUpvalues = resultTypedUpvalues
					proto.typedLocals = resultTypedLocals
				end

				-- total number of instructions
				proto.sizeInstructions = reader:nextVarInt()
				for i = 1, proto.sizeInstructions do
					local encodedInstruction = reader:nextUInt32()
					proto.instructions[i] = encodedInstruction
				end

				-- total number of constants
				proto.sizeConstants = reader:nextVarInt()
				for i = 1, proto.sizeConstants do
					local constValue

					local constType = reader:nextByte()
					if constType == LuauBytecodeTag.LBC_CONSTANT_BOOLEAN then
						-- 1 = true, 0 = false
						constValue = toBoolean(reader:nextByte())
					elseif constType == LuauBytecodeTag.LBC_CONSTANT_NUMBER then
						constValue = reader:nextDouble()
					elseif constType == LuauBytecodeTag.LBC_CONSTANT_STRING then
						local stringId = reader:nextVarInt()
						constValue = stringTable[stringId]
					elseif constType == LuauBytecodeTag.LBC_CONSTANT_IMPORT then
						-- imports are globals from the environment
						-- examples: math.random, print, coroutine.wrap

						local id = reader:nextUInt32()

						local indexCount = bit32.rshift(id, 30)

						local cacheIndex1 = bit32.band(bit32.rshift(id, 20), 0x3FF)
						local cacheIndex2 = bit32.band(bit32.rshift(id, 10), 0x3FF)
						local cacheIndex3 = bit32.band(bit32.rshift(id, 0), 0x3FF)

						local importTag = ""

						if indexCount == 1 then
							local k1 = proto.constants[cacheIndex1 + 1]
							importTag ..= tostring(k1.value)
						elseif indexCount == 2 then
							local k1 = proto.constants[cacheIndex1 + 1]
							local k2 = proto.constants[cacheIndex2 + 1]
							importTag ..= tostring(k1.value) .. "."
							importTag ..= tostring(k2.value)
						elseif indexCount == 3 then
							local k1 = proto.constants[cacheIndex1 + 1]
							local k2 = proto.constants[cacheIndex2 + 1]
							local k3 = proto.constants[cacheIndex3 + 1]
							importTag ..= tostring(k1.value) .. "."
							importTag ..= tostring(k2.value) .. "."
							importTag ..= tostring(k3.value)
						end

						constValue = importTag
					elseif constType == LuauBytecodeTag.LBC_CONSTANT_TABLE then
						local sizeTable = reader:nextVarInt()
						local tableKeys = {}

						for i = 1, sizeTable do
							local keyStringId = reader:nextVarInt() + 1
							table.insert(tableKeys, keyStringId)
						end

						constValue = {
							size = sizeTable,
							keys = tableKeys
						}
					elseif constType == LuauBytecodeTag.LBC_CONSTANT_CLOSURE then
						local closureId = reader:nextVarInt() + 1
						constValue = closureId
					elseif constType == LuauBytecodeTag.LBC_CONSTANT_VECTOR then
						local x, y, z, w = reader:nextFloat(), reader:nextFloat(), reader:nextFloat(), reader:nextFloat()
						if w == 0 then
							constValue = "Vector3.new(".. x ..", ".. y ..", ".. z ..")"
						else
							constValue = "vector.create(".. x ..", ".. y ..", ".. z ..", ".. w ..")"
						end
					elseif constType ~= LuauBytecodeTag.LBC_CONSTANT_NIL then
						-- this is not supposed to happen. result is likely malformed
					end

					-- info on the constant at index `i`
					local info = {
						type = constType,
						value = constValue
					}
					proto.constants[i] = info
				end

				-- total number of protos inside this proto
				proto.sizeInnerProtos = reader:nextVarInt()
				for i = 1, proto.sizeInnerProtos do
					local protoId = reader:nextVarInt()
					proto.innerProtos[i] = protoTable[protoId]
				end

				-- lineDefined is the line function starts on
				proto.lineDefined = reader:nextVarInt()

				-- protoDebugNameId is the string id of the function's name if it is not unnamed
				local protoDebugNameId = reader:nextVarInt()
				proto.name = stringTable[protoDebugNameId]

				-- references:
				-- https://github.com/luau-lang/luau/blob/0.655/Compiler/src/BytecodeBuilder.cpp#L888
				-- https://github.com/uniquadev/LuauVM/blob/master/VM/luau/lobject.lua
				local hasLineInfo = toBoolean(reader:nextByte())
				proto.hasLineInfo = hasLineInfo

				if hasLineInfo then
					-- log2 of the line gap between instructions
					local lineGapLog2 = reader:nextByte()

					local baselineSize = bit32.rshift(proto.sizeInstructions - 1, lineGapLog2) + 1

					local lastOffset = 0
					local lastLine = 0

					-- line number as a delta from baseline for each instruction
					local smallLineInfo = {}
					-- one entry for each bit32.lshift(1, lineGapLog2) instructions
					local absLineInfo = {}
					-- ready to read line info
					local resultLineInfo = {}

					for i, instruction in proto.instructions do
						-- i don't understand how this works. we mostly need signed, but sometimes we need unsigned?
						-- help please. if you understand
						local byte = reader:nextSignedByte()

						-- line numbers unexpectedly dropped/increased by 255 (or 256?) because i set delta to just lastOffset + byte
						-- the solution: (lastOffset + byte) & 0xFF.
						-- shoutout to https://github.com/ActualMasterOogway/Iridium/ for finding this fix
						local delta = bit32.band(lastOffset + byte, 0xFF)
						smallLineInfo[i] = delta

						lastOffset = delta
					end

					for i = 1, baselineSize do
						-- if we read unsigned int32 here we're doomed!!!!!! for eternity!!!!!!!!!
						local largeLineChange = lastLine + reader:nextInt32()
						absLineInfo[i] = largeLineChange

						lastLine = largeLineChange
					end

					for i, line in smallLineInfo do
						local absIndex = bit32.rshift(i - 1, lineGapLog2) + 1

						local absLine = absLineInfo[absIndex]
						local resultLine = line + absLine

						resultLineInfo[i] = resultLine
					end

					proto.lineInfoSize = lineGapLog2
					proto.instructionLineInfo = resultLineInfo
				end

				-- debug info is not present in Roblox and that's sad
				-- no variable names...
				local hasDebugInfo = toBoolean(reader:nextByte())
				proto.hasDebugInfo = hasDebugInfo

				if hasDebugInfo then
					local totalDebugLocals = reader:nextVarInt()
					local function readDebugLocals()
						local debugLocals = {}

						for i = 1, totalDebugLocals do
							local localName = stringTable[reader:nextVarInt()]
							local localStartPC = reader:nextVarInt() + 1 -- PC is 1-based in our actions
							local localEndPC = reader:nextVarInt() + localStartPC - 1 -- Make it 1-based
							local localRegister = reader:nextByte()

							-- debug info on the local at index `i`
							local info = {
								name = localName,
								startPC = localStartPC,
								endPC = localEndPC,
								register = localRegister
							}
							debugLocals[i] = info
						end

						return debugLocals
					end
					proto.debugLocals = readDebugLocals()

					local totalDebugUpvalues = reader:nextVarInt()
					local function readDebugUpvalues()
						local debugUpvalues = {}

						for i = 1, totalDebugUpvalues do
							local upvalueName = stringTable[reader:nextVarInt()]

							-- debug info on the upvalue at index `i`
							local info = {
								name = upvalueName
							}
							debugUpvalues[i] = info
						end

						return debugUpvalues
					end
					proto.debugUpvalues = readDebugUpvalues()
				end
			end
		end

		-- read needs to be done in proper order
		readStringTable()
		if bytecodeVersion > 5 then
			readUserdataTypes()
		end
		readProtoTable()

		if #userdataTypes > 0 then
			warn("please send the bytecode to me so i can add support for userdata types. thanks!")
		end

		local mainProtoId = reader:nextVarInt()
		return mainProtoId, protoTable
	end
	-- step 2: organize information for decompilation
	local function organize()
		-- provides proto name and line along with the issue in a warning message
		local function reportProtoIssue(proto, issue)
			local protoIdentifier = `[{proto.name or "unnamed"}:{proto.lineDefined or -1}]`
			warn(protoIdentifier .. ": " .. issue)
		end

		local mainProtoId, protoTable = disassemble()

		local mainProto = protoTable[mainProtoId]
		mainProto.main = true

		-- collected operation data
		local registerActions = {}

		local function baseProto(proto)
			local protoRegisterActions = {}

			-- this needs to be done here.
			local protoActionData = {
				proto = proto,
				actions = protoRegisterActions
			}
			registerActions[proto.id] = protoActionData

			local instructions = proto.instructions
			local innerProtos = proto.innerProtos
			local constants = proto.constants
			local captures = proto.captures
			local flags = proto.flags

			-- collect all captures past the base instruction index
			local function collectCaptures(baseIndex, proto)
				local numUpvalues = proto.numUpvalues
				if numUpvalues > 0 then
					local _captures = proto.captures

					for i = 1, numUpvalues do
						local capture = instructions[baseIndex + i]

						local captureType = Luau:INSN_A(capture)
						local sourceRegister = Luau:INSN_B(capture)

						if captureType == LuauCaptureType.LCT_VAL or captureType == LuauCaptureType.LCT_REF then
							_captures[i - 1] = sourceRegister
						elseif captureType == LuauCaptureType.LCT_UPVAL then
							-- capture of a capture. haha..
							_captures[i - 1] = captures[sourceRegister]
						end
					end
				end
			end

			local function writeFlags()
				local decodedFlags = {}

				if proto.main then
					-- what we are dealing with here is mainFlags
					-- refer to: https://github.com/luau-lang/luau/blob/0.655/Compiler/src/Compiler.cpp#L4188

					--decodedFlags.native = toBoolean(bit32.band(flags, LuauProtoFlag.LPF_NATIVE_MODULE))
				else
					-- normal protoFlags
					-- refer to: https://github.com/luau-lang/luau/blob/0.655/Compiler/src/Compiler.cpp#L287

					--decodedFlags.native = toBoolean(bit32.band(flags, LuauProtoFlag.LPF_NATIVE_FUNCTION))
					--decodedFlags.cold = toBoolean(bit32.band(flags, LuauProtoFlag.LPF_NATIVE_COLD))
				end

				-- update flags entry
				flags = decodedFlags
				proto.flags = decodedFlags
			end
			local function writeInstructions()
				local auxSkip = false

				for index, instruction in instructions do
					if auxSkip then
						-- we are currently on an aux of a previous instruction
						-- there is no need to do any work here.
						auxSkip = false
						continue
					end

					local opCodeInfo = LuauOpCode[Luau:INSN_OP(instruction)]
					if not opCodeInfo then
						-- this is serious!
						reportProtoIssue(proto, `invalid instruction at index "{index}"!`)
						continue
					end

					local opCodeName = opCodeInfo.name
					local opCodeType = opCodeInfo.type
					local opCodeIsAux = opCodeInfo.aux == true

					-- information in the instruction that we will use
					local A, B, C
					local sD, D, E
					local aux

					-- creates an action from provided data and registers it.
					local function registerAction(usedRegisters, extraData, hide)
						local data = {
							usedRegisters = usedRegisters or {},
							extraData = extraData,
							opCode = opCodeInfo,
							hide = hide
						}
						table.insert(protoRegisterActions, data)
					end

					-- handle reading information based on the op code type
					if opCodeType == "A" then
						A = Luau:INSN_A(instruction)
					elseif opCodeType == "E" then
						E = Luau:INSN_E(instruction)
					elseif opCodeType == "AB" then
						A = Luau:INSN_A(instruction)
						B = Luau:INSN_B(instruction)
					elseif opCodeType == "AC" then
						A = Luau:INSN_A(instruction)
						C = Luau:INSN_C(instruction)
					elseif opCodeType == "ABC" then
						A = Luau:INSN_A(instruction)
						B = Luau:INSN_B(instruction)
						C = Luau:INSN_C(instruction)
					elseif opCodeType == "AD" then
						A = Luau:INSN_A(instruction)
						D = Luau:INSN_D(instruction)
					elseif opCodeType == "AsD" then
						A = Luau:INSN_A(instruction)
						sD = Luau:INSN_sD(instruction)
					elseif opCodeType == "sD" then
						sD = Luau:INSN_sD(instruction)
					end

					-- handle aux
					if opCodeIsAux then
						auxSkip = true

						-- empty action for aux
						registerAction(nil, nil, true)

						-- aux is the next instruction
						aux = instructions[index + 1]
					end

					-- it would be faster if we did this comparing opCode index
					-- rather than name, but it would be suffering to code and read
					if opCodeName == "NOP" or opCodeName == "BREAK" or opCodeName == "NATIVECALL" then
						-- empty action for these
						registerAction(nil, nil, not SHOW_TRIVIAL_OPERATIONS)
					elseif opCodeName == "LOADNIL" then
						registerAction({A})
					elseif opCodeName == "LOADB" then -- load boolean
						registerAction({A}, {B, C})
					elseif opCodeName == "LOADN" then -- load number literal
						registerAction({A}, {sD})
					elseif opCodeName == "LOADK" then -- load constant
						registerAction({A}, {D})
					elseif opCodeName == "MOVE" then
						registerAction({A, B})
					elseif opCodeName == "GETGLOBAL" or opCodeName == "SETGLOBAL" then
						-- we most likely will not ever use C here.
						registerAction({A}, {aux}) --({A}, {C, aux})
					elseif opCodeName == "GETUPVAL" or opCodeName == "SETUPVAL" then
						registerAction({A}, {B})
					elseif opCodeName == "CLOSEUPVALS" then
						registerAction({A}, nil, not SHOW_TRIVIAL_OPERATIONS)
					elseif opCodeName == "GETIMPORT" then
						registerAction({A}, {D, aux})
					elseif opCodeName == "GETTABLE" or opCodeName == "SETTABLE" then
						registerAction({A, B, C})
					elseif opCodeName == "GETTABLEKS" or opCodeName == "SETTABLEKS" then
						registerAction({A, B}, {C, aux})
					elseif opCodeName == "GETTABLEN" or opCodeName == "SETTABLEN" then
						registerAction({A, B}, {C})
					elseif opCodeName == "NEWCLOSURE" then
						registerAction({A}, {D})

						local proto = innerProtos[D + 1]
						collectCaptures(index, proto)
						baseProto(proto)
					elseif opCodeName == "DUPCLOSURE" then
						registerAction({A}, {D})

						local proto = protoTable[constants[D + 1].value - 1]
						collectCaptures(index, proto)
						baseProto(proto)
					elseif opCodeName == "NAMECALL" then -- must be followed by CALL
						registerAction({A, B}, {C, aux}, not SHOW_TRIVIAL_OPERATIONS)
					elseif opCodeName == "CALL" then
						registerAction({A}, {B, C})
					elseif opCodeName == "RETURN" then
						registerAction({A}, {B})
					elseif opCodeName == "JUMP" or opCodeName == "JUMPBACK" then
						registerAction({}, {sD})
					elseif opCodeName == "JUMPIF" or opCodeName == "JUMPIFNOT" then
						registerAction({A}, {sD})
					elseif
						opCodeName == "JUMPIFEQ" or opCodeName == "JUMPIFLE" or opCodeName == "JUMPIFLT" or
						opCodeName == "JUMPIFNOTEQ" or opCodeName == "JUMPIFNOTLE" or opCodeName == "JUMPIFNOTLT"
					then
						registerAction({A, aux}, {sD})
					elseif
						opCodeName == "ADD" or opCodeName == "SUB" or opCodeName == "MUL" or
						opCodeName == "DIV" or opCodeName == "MOD" or opCodeName == "POW"
					then
						registerAction({A, B, C})
					elseif
						opCodeName == "ADDK" or opCodeName == "SUBK" or opCodeName == "MULK" or
						opCodeName == "DIVK" or opCodeName == "MODK" or opCodeName == "POWK"
					then
						registerAction({A, B}, {C})
					elseif opCodeName == "AND" or opCodeName == "OR" then
						registerAction({A, B, C})
					elseif opCodeName == "ANDK" or opCodeName == "ORK" then
						registerAction({A, B}, {C})
					elseif opCodeName == "CONCAT" then
						local registers = {A}
						for reg = B, C do
							table.insert(registers, reg)
						end
						registerAction(registers)
					elseif opCodeName == "NOT" or opCodeName == "MINUS" or opCodeName == "LENGTH" then
						registerAction({A, B})
					elseif opCodeName == "NEWTABLE" then
						registerAction({A}, {B, aux})
					elseif opCodeName == "DUPTABLE" then
						registerAction({A}, {D})
					elseif opCodeName == "SETLIST" then
						if C ~= 0 then
							local registers = {A, B}
							for i = 1, C - 2 do -- account for target and source registers
								table.insert(registers, A + i)
							end
							registerAction(registers, {aux, C})
						else
							registerAction({A, B}, {aux, C})
						end
					elseif opCodeName == "FORNPREP" then
						registerAction({A, A+1, A+2}, {sD})
					elseif opCodeName == "FORNLOOP" then
						registerAction({A}, {sD})
					elseif opCodeName == "FORGLOOP" then
						local numVariableRegisters = bit32.band(aux, 0xFF)

						local registers = {}
						for regIndex = 1, numVariableRegisters do
							table.insert(registers, A + regIndex)
						end
						registerAction(registers, {sD, aux})
					elseif opCodeName == "FORGPREP_INEXT" or opCodeName == "FORGPREP_NEXT" then
						registerAction({A}, {sD})
					elseif opCodeName == "FORGPREP" then
						registerAction({A}, {sD})
					elseif opCodeName == "GETVARARGS" then
						if B ~= 0 then
							local registers = {A}
							-- i hope this works and it is not reg = 1
							for reg = 0, B - 1 do
								table.insert(registers, A + reg)
							end
							registerAction(registers, {B})
						else
							registerAction({A}, {B})
						end
					elseif opCodeName == "PREPVARARGS" then
						registerAction({}, {A}, not SHOW_TRIVIAL_OPERATIONS)
					elseif opCodeName == "LOADKX" then
						registerAction({A}, {aux})
					elseif opCodeName == "JUMPX" then
						registerAction({}, {E})
					elseif opCodeName == "COVERAGE" then
						registerAction({}, {E}, not SHOW_TRIVIAL_OPERATIONS)
					elseif
						opCodeName == "JUMPXEQKNIL" or opCodeName == "JUMPXEQKB" or
						opCodeName == "JUMPXEQKN" or opCodeName == "JUMPXEQKS"
					then
						registerAction({A}, {sD, aux})
					elseif opCodeName == "CAPTURE" then
						-- empty action here
						registerAction(nil, nil, not SHOW_TRIVIAL_OPERATIONS)
					elseif opCodeName == "SUBRK" or opCodeName == "DIVRK" then -- constant sub/div
						registerAction({A, C}, {B})
					elseif opCodeName == "IDIV" then -- floor division
						registerAction({A, B, C})
					elseif opCodeName == "IDIVK" then -- floor division with 1 constant argument
						registerAction({A, B}, {C})
					elseif opCodeName == "FASTCALL" then -- reads info from the CALL instruction
						registerAction({}, {A, C}, not SHOW_TRIVIAL_OPERATIONS)
					elseif opCodeName == "FASTCALL1" then -- 1 register argument
						registerAction({B}, {A, C}, not SHOW_TRIVIAL_OPERATIONS)
					elseif opCodeName == "FASTCALL2" then -- 2 register arguments
						local sourceArgumentRegister2 = bit32.band(aux, 0xFF)

						registerAction({B, sourceArgumentRegister2}, {A, C}, not SHOW_TRIVIAL_OPERATIONS)
					elseif opCodeName == "FASTCALL2K" then -- 1 register argument and 1 constant argument
						registerAction({B}, {A, C, aux}, not SHOW_TRIVIAL_OPERATIONS)
					elseif opCodeName == "FASTCALL3" then
						local sourceArgumentRegister2 = bit32.band(aux, 0xFF)
						local sourceArgumentRegister3 = bit32.rshift(sourceArgumentRegister2, 8)

						registerAction({B, sourceArgumentRegister2, sourceArgumentRegister3}, {A, C}, not SHOW_TRIVIAL_OPERATIONS)
					end
				end
			end

			writeFlags()
			writeInstructions()
		end
		baseProto(mainProto)

		return mainProtoId, registerActions, protoTable
	end
	-- step 3: turn the result into a string
	local function finalize(mainProtoId, registerActions, protoTable)
		local finalResult = ""

		local totalParameters = 0
		-- array of used globals for further output
		local usedGlobals = {}

		-- should `key` be logged in usedGlobals?
		local function isValidGlobal(key)
			return not table.find(usedGlobals, key) and not isGlobal(key)
		end

		-- received result. embed final things here.
		local function processResult(result)
			local embed = ""

			if LIST_USED_GLOBALS and #usedGlobals > 0 then
				embed ..= string.format(Strings.USED_GLOBALS, table.concat(usedGlobals, ", "))
			end

			return embed .. result
		end

		-- now proceed based off mode
		if DECOMPILER_MODE == "disasm" then -- disassembler
			local result = ""

			local function writeActions(protoActions)
				local actions = protoActions.actions
				local proto = protoActions.proto

				local instructionLineInfo = proto.instructionLineInfo
				local innerProtos = proto.innerProtos
				local constants = proto.constants
				local captures = proto.captures
				local flags = proto.flags

				local numParams = proto.numParams

				SHOW_INSTRUCTION_LINES = SHOW_INSTRUCTION_LINES and #instructionLineInfo > 0

				-- for proper `goto` handling
				local jumpMarkers = {}
				local function makeJumpMarker(index)
					index -= 1

					local numMarkers = jumpMarkers[index] or 0
					jumpMarkers[index] = numMarkers + 1
				end

				-- for easier parameter differentiation
				totalParameters += numParams

				-- support for mainFlags
				if proto.main then
					-- if there is a possible way to check for --!optimize please let me know
					if flags.native then
						result ..= "--!native" .. "\n"
					end
				end

				for i, action in actions do
					if action.hide then
						-- skip this action. either hidden or just aux that is needed for proper line info
						continue
					end

					local usedRegisters = action.usedRegisters
					local extraData = action.extraData
					local opCodeInfo = action.opCode

					local opCodeName = opCodeInfo.name

					local function handleJumpMarkers()
						local numJumpMarkers = jumpMarkers[i]
						if numJumpMarkers then
							jumpMarkers[i] = nil

							--if string.find(opCodeName, "JUMP") then
							-- it's much more complicated
							--	result ..= "else\n"

							--	local newJumpOffset = i + extraData[1] + 1
							--	makeJumpMarker(newJumpOffset)
							--else
							-- it's just a one way condition
							for i = 1, numJumpMarkers do
								result ..= "end\n"
							end
							--end
						end
					end

					local function writeHeader()
						local index
						if SHOW_OPERATION_INDEX then
							index = "[".. padLeft(i, "0", 3) .."]"
						else
							index = ""
						end

						local name
						if SHOW_OPERATION_NAMES then
							name = padRight(opCodeName, " ", 15)
						else
							name = ""
						end

						local line
						if SHOW_INSTRUCTION_LINES then
							line = ":".. padLeft(instructionLineInfo[i], "0", 3) ..":"
						else
							line = ""
						end

						result ..= index .." ".. line .. name
					end
					local function writeOperationBody()
						local function formatRegister(register)
							local parameterRegister = register + 1 -- parameter registers start from 0
							if parameterRegister < numParams + 1 then
								-- this means we are using preserved parameter register
								return "p".. ((totalParameters - numParams) + parameterRegister)
							end

							return "v".. (register - numParams)
						end

						local function formatUpvalue(register)
							return "u_v".. register
						end

						local function formatProto(proto)
							local name = proto.name
							local numParams = proto.numParams
							local isVarArg = proto.isVarArg
							local isTyped = proto.hasTypeInfo and USE_TYPE_INFO
							local flags = proto.flags
							local typedParams = proto.typedParams

							local protoBody = ""

							-- attribute support
							if flags.native then
								if flags.cold and ENABLED_REMARKS.COLD_REMARK then
									-- function is marked cold and is deemed not profitable to compile natively
									-- refer to: https://github.com/luau-lang/luau/blob/0.655/Compiler/src/Compiler.cpp#L285
									protoBody ..= string.format(Strings.DECOMPILER_REMARK, "This function is marked cold and is not compiled natively")
								end

								protoBody ..= "@native "
							end

							-- if function has a name, add it
							if name then
								protoBody = "local function ".. name
							else
								protoBody = "function"
							end

							-- now build parameters
							protoBody ..= "("

							for index = 1, numParams do
								local parameterBody = "p".. (totalParameters + index)
								-- if has type info, apply it
								if isTyped then
									local parameterType = typedParams[index]
									-- not sure if parameterType always exists
									if parameterType then
										parameterBody ..= ": ".. Luau:GetBaseTypeString(parameterType, true)
									end
								end
								-- if not last parameter
								if index ~= numParams then
									parameterBody ..= ", "
								end
								protoBody ..= parameterBody
							end

							if isVarArg then
								if numParams > 0 then
									-- top it off with ...
									protoBody ..= ", ..."
								else
									protoBody ..= "..."
								end
							end

							protoBody ..= ")\n"

							-- additional debug information
							if SHOW_DEBUG_INFORMATION then
								protoBody ..= "-- proto pool id: ".. proto.id .. "\n"
								protoBody ..= "-- num upvalues: ".. proto.numUpvalues .. "\n"
								protoBody ..= "-- num inner protos: ".. proto.sizeInnerProtos .. "\n"
								protoBody ..= "-- size instructions: ".. proto.sizeInstructions .. "\n"
								protoBody ..= "-- size constants: ".. proto.sizeConstants .. "\n"
								protoBody ..= "-- lineinfo gap: ".. proto.lineInfoSize .. "\n"
								protoBody ..= "-- max stack size: ".. proto.maxStackSize .. "\n"
								protoBody ..= "-- is typed: ".. tostring(proto.hasTypeInfo) .. "\n"
							end

							return protoBody
						end

						local function formatConstantValue(k)
							if k.type == LuauBytecodeTag.LBC_CONSTANT_VECTOR then
								return k.value
							else
								if type(tonumber(k.value)) == "number" then
									return tonumber(string.format(`%0.{READER_FLOAT_PRECISION}f`, k.value))
								else
									return toEscapedString(k.value)
								end
							end
						end

						local function writeProto(register, proto)
							local protoBody = formatProto(proto)

							local name = proto.name
							if name then
								result ..= "\n".. protoBody
								writeActions(registerActions[proto.id])
								result ..= "end\n".. formatRegister(register) .." = ".. name
							else
								result ..= formatRegister(register) .." = ".. protoBody
								writeActions(registerActions[proto.id])
								result ..= "end"
							end
						end

						if opCodeName == "LOADNIL" then
							local targetRegister = usedRegisters[1]

							result ..= formatRegister(targetRegister) .." = nil"
						elseif opCodeName == "LOADB" then -- load boolean
							local targetRegister = usedRegisters[1]

							local value = toBoolean(extraData[1])
							local jumpOffset = extraData[2]

							result ..= formatRegister(targetRegister) .." = ".. toEscapedString(value)

							if jumpOffset ~= 0 then
								-- skip over next LOADB?
								result ..= string.format(" +%i", jumpOffset)
							end
						elseif opCodeName == "LOADN" then -- load number literal
							local targetRegister = usedRegisters[1]

							local value = extraData[1]

							result ..= formatRegister(targetRegister) .." = ".. value
						elseif opCodeName == "LOADK" then -- load constant
							local targetRegister = usedRegisters[1]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. value
						elseif opCodeName == "MOVE" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister)
						elseif opCodeName == "GETGLOBAL" then
							local targetRegister = usedRegisters[1]

							-- formatConstantValue uses toEscapedString which we don't want here
							local globalKey = tostring(constants[extraData[1] + 1].value)

							if LIST_USED_GLOBALS and isValidGlobal(globalKey) then
								table.insert(usedGlobals, globalKey)
							end

							result ..= formatRegister(targetRegister) .." = ".. globalKey
						elseif opCodeName == "SETGLOBAL" then
							local sourceRegister = usedRegisters[1]

							local globalKey = tostring(constants[extraData[1] + 1].value)

							if LIST_USED_GLOBALS and isValidGlobal(globalKey) then
								table.insert(usedGlobals, globalKey)
							end

							result ..= globalKey .." = ".. formatRegister(sourceRegister)
						elseif opCodeName == "GETUPVAL" then
							local targetRegister = usedRegisters[1]

							local upvalueIndex = extraData[1]

							result ..= formatRegister(targetRegister) .." = ".. formatUpvalue(captures[upvalueIndex])
						elseif opCodeName == "SETUPVAL" then
							local targetRegister = usedRegisters[1]

							local upvalueIndex = extraData[1]

							result ..= formatUpvalue(captures[upvalueIndex]) .. " = " .. formatRegister(targetRegister)
						elseif opCodeName == "CLOSEUPVALS" then
							local targetRegister = usedRegisters[1]

							result ..= "-- clear captures from back until: ".. targetRegister
						elseif opCodeName == "GETIMPORT" then
							local targetRegister = usedRegisters[1]

							local importIndex = extraData[1]
							local importIndices = extraData[2]

							-- we load imports into constants
							local import = tostring(constants[importIndex + 1].value)

							local totalIndices = bit32.rshift(importIndices, 30)
							if totalIndices == 1 then
								if LIST_USED_GLOBALS and isValidGlobal(import) then
									-- it is a non-Roblox global that we need to log
									table.insert(usedGlobals, import)
								end
							end

							result ..= formatRegister(targetRegister) .." = ".. import
						elseif opCodeName == "GETTABLE" then
							local targetRegister = usedRegisters[1]
							local tableRegister = usedRegisters[2]
							local indexRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(tableRegister) .."[".. formatRegister(indexRegister) .."]"
						elseif opCodeName == "SETTABLE" then
							local sourceRegister = usedRegisters[1]
							local tableRegister = usedRegisters[2]
							local indexRegister = usedRegisters[3]

							result ..= formatRegister(tableRegister) .."[".. formatRegister(indexRegister) .."]" .." = ".. formatRegister(sourceRegister)
						elseif opCodeName == "GETTABLEKS" then
							local targetRegister = usedRegisters[1]
							local tableRegister = usedRegisters[2]

							--local slotIndex = extraData[1]
							local key = constants[extraData[2] + 1].value

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(tableRegister) .. formatIndexString(key)
						elseif opCodeName == "SETTABLEKS" then
							local sourceRegister = usedRegisters[1]
							local tableRegister = usedRegisters[2]

							--local slotIndex = extraData[1]
							local key = constants[extraData[2] + 1].value

							result ..= formatRegister(tableRegister) .. formatIndexString(key) .." = ".. formatRegister(sourceRegister)
						elseif opCodeName == "GETTABLEN" then
							local targetRegister = usedRegisters[1]
							local tableRegister = usedRegisters[2]

							local index = extraData[1] + 1

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(tableRegister) .."[".. index .."]"
						elseif opCodeName == "SETTABLEN" then
							local sourceRegister = usedRegisters[1]
							local tableRegister = usedRegisters[2]

							local index = extraData[1] + 1

							result ..= formatRegister(tableRegister) .."[".. index .."] = ".. formatRegister(sourceRegister)
						elseif opCodeName == "NEWCLOSURE" then
							local targetRegister = usedRegisters[1]

							local protoIndex = extraData[1] + 1
							local nextProto = innerProtos[protoIndex]

							writeProto(targetRegister, nextProto)
						elseif opCodeName == "DUPCLOSURE" then
							local targetRegister = usedRegisters[1]

							local protoIndex = extraData[1] + 1
							local nextProto = protoTable[constants[protoIndex].value - 1]

							writeProto(targetRegister, nextProto)
						elseif opCodeName == "NAMECALL" then -- must be followed by CALL
							--local targetRegister = usedRegisters[1]
							--local sourceRegister = usedRegisters[2]

							--local slotIndex = extraData[1]
							local method = tostring(constants[extraData[2] + 1].value)

							result ..= "-- :".. method
						elseif opCodeName == "CALL" then
							local baseRegister = usedRegisters[1]

							local numArguments = extraData[1] - 1
							local numResults = extraData[2] - 1

							-- NAMECALL instruction might provide us a method
							local namecallMethod = ""
							local argumentOffset = 0

							-- try searching for the NAMECALL instruction
							local precedingAction = actions[i - 1]
							if precedingAction then
								local precedingOpCode = precedingAction.opCode
								if precedingOpCode.name == "NAMECALL" then
									local precedingExtraData = precedingAction.extraData
									namecallMethod = ":".. tostring(constants[precedingExtraData[2] + 1].value)

									-- exclude self due to syntactic sugar
									numArguments -= 1
									argumentOffset += 1 -- but self still needs to be counted.
								end
							end

							-- beginning
							local callBody = ""

							if numResults == -1 then -- MULTRET
								callBody ..= "... = "
							elseif numResults > 0 then
								local resultsBody = ""
								for i = 1, numResults do
									resultsBody ..= formatRegister(baseRegister + i - 1)

									if i ~= numResults then
										resultsBody ..= ", "
									end
								end
								resultsBody ..= " = "

								callBody ..= resultsBody
							end

							-- middle phase
							callBody ..= formatRegister(baseRegister) .. namecallMethod .."("

							if numArguments == -1 then -- MULTCALL
								callBody ..= "..."
							elseif numArguments > 0 then
								local argumentsBody = ""
								for i = 1, numArguments do
									argumentsBody ..= formatRegister(baseRegister + i + argumentOffset)

									if i ~= numArguments then
										argumentsBody ..= ", "
									end
								end
								callBody ..= argumentsBody
							end

							-- finale
							callBody ..= ")"

							result ..= callBody
						elseif opCodeName == "RETURN" then
							local baseRegister = usedRegisters[1]

							local retBody = ""

							local totalValues = extraData[1] - 2
							if totalValues == -2 then -- MULTRET
								retBody ..= " ".. formatRegister(baseRegister) ..", ..."
							elseif totalValues > -1 then
								retBody ..= " "

								for i = 0, totalValues do
									retBody ..= formatRegister(baseRegister + i)

									if i ~= totalValues then
										retBody ..= ", "
									end
								end
							end

							result ..= "return".. retBody
						elseif opCodeName == "JUMP" then
							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							--makeJumpMarker(endIndex)

							result ..= "-- jump to #" .. endIndex
						elseif opCodeName == "JUMPBACK" then
							local jumpOffset = extraData[1] + 1

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							--makeJumpMarker(endIndex)

							result ..= "-- jump back to #" .. endIndex
						elseif opCodeName == "JUMPIF" then
							local sourceRegister = usedRegisters[1]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if not ".. formatRegister(sourceRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFNOT" then
							local sourceRegister = usedRegisters[1]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(sourceRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFEQ" then
							local leftRegister = usedRegisters[1]
							local rightRegister = usedRegisters[2]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(leftRegister) .." == ".. formatRegister(rightRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFLE" then
							local leftRegister = usedRegisters[1]
							local rightRegister = usedRegisters[2]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(leftRegister) .." => ".. formatRegister(rightRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFLT" then -- may be wrong
							local leftRegister = usedRegisters[1]
							local rightRegister = usedRegisters[2]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(leftRegister) .." > ".. formatRegister(rightRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFNOTEQ" then
							local leftRegister = usedRegisters[1]
							local rightRegister = usedRegisters[2]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(leftRegister) .." ~= ".. formatRegister(rightRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFNOTLE" then
							local leftRegister = usedRegisters[1]
							local rightRegister = usedRegisters[2]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(leftRegister) .." <= ".. formatRegister(rightRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPIFNOTLT" then
							local leftRegister = usedRegisters[1]
							local rightRegister = usedRegisters[2]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(leftRegister) .." < ".. formatRegister(rightRegister) .." then -- goto #".. endIndex
						elseif opCodeName == "ADD" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." + ".. formatRegister(rightRegister)
						elseif opCodeName == "SUB" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." - ".. formatRegister(rightRegister)
						elseif opCodeName == "MUL" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." * ".. formatRegister(rightRegister)
						elseif opCodeName == "DIV" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." / ".. formatRegister(rightRegister)
						elseif opCodeName == "MOD" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." % ".. formatRegister(rightRegister)
						elseif opCodeName == "POW" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." ^ ".. formatRegister(rightRegister)
						elseif opCodeName == "ADDK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." + ".. value
						elseif opCodeName == "SUBK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." - ".. value
						elseif opCodeName == "MULK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." * ".. value
						elseif opCodeName == "DIVK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." / ".. value
						elseif opCodeName == "MODK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." % ".. value
						elseif opCodeName == "POWK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." ^ ".. value
						elseif opCodeName == "AND" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." and ".. formatRegister(rightRegister)
						elseif opCodeName == "OR" then
							local targetRegister = usedRegisters[1]
							local leftRegister = usedRegisters[2]
							local rightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(leftRegister) .." or ".. formatRegister(rightRegister)
						elseif opCodeName == "ANDK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." and ".. value
						elseif opCodeName == "ORK" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." or ".. value
						elseif opCodeName == "CONCAT" then
							local targetRegister = table.remove(usedRegisters, 1)

							local totalRegisters = #usedRegisters

							local concatBody = ""
							for i = 1, totalRegisters do
								local register = usedRegisters[i]
								concatBody ..= formatRegister(register)

								if i ~= totalRegisters then
									concatBody ..= " .. "
								end
							end
							result ..= formatRegister(targetRegister) .." = ".. concatBody
						elseif opCodeName == "NOT" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							result ..= formatRegister(targetRegister) .." = not ".. formatRegister(sourceRegister)
						elseif opCodeName == "MINUS" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							result ..= formatRegister(targetRegister) .." = -".. formatRegister(sourceRegister)
						elseif opCodeName == "LENGTH" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							result ..= formatRegister(targetRegister) .." = #".. formatRegister(sourceRegister)
						elseif opCodeName == "NEWTABLE" then
							local targetRegister = usedRegisters[1]

							--local tableHashSize = extraData[1]
							local arraySize = extraData[2]

							result ..= formatRegister(targetRegister) .." = {}"

							if SHOW_DEBUG_INFORMATION and arraySize > 0 then
								result ..= " --[[".. arraySize .." preallocated indexes]]"
							end
						elseif opCodeName == "DUPTABLE" then
							local targetRegister = usedRegisters[1]

							local value = constants[extraData[1] + 1].value
							local kSize = value.size
							local kKeys = value.keys

							local tableBody = "{"
							for i = 1, kSize do
								local key = kKeys[i]
								local value = formatConstantValue(constants[key])

								tableBody ..= value

								if i ~= kSize then
									tableBody ..= ", "
								end
							end
							tableBody ..= "}"

							result ..= formatRegister(targetRegister) .." = {} -- ".. tableBody
						elseif opCodeName == "SETLIST" then
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local startIndex = extraData[1]
							local valueCount = extraData[2]

							local changeBody = ""
							if valueCount == 0 then -- MULTRET
								changeBody = formatRegister(targetRegister) .."[".. startIndex .."] = [...]"
							else
								local totalRegisters = #usedRegisters - 1
								for i = 1, totalRegisters do
									local register = usedRegisters[i]

									local offset = i - 1
									changeBody ..= formatRegister(register) .."[".. startIndex + offset .."] = ".. formatRegister(sourceRegister + offset)

									if i ~= totalRegisters then
										changeBody ..= "\n"
									end
								end
							end
							result ..= changeBody
						elseif opCodeName == "FORNPREP" then
							local targetRegister = usedRegisters[1]
							local stepRegister = usedRegisters[2]
							local indexRegister = usedRegisters[3]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							-- we have FORNLOOP
							--makeJumpMarker(endIndex)

							local numericStartBody = "for ".. formatRegister(indexRegister) .." = ".. formatRegister(indexRegister) ..", ".. formatRegister(targetRegister) ..", ".. formatRegister(stepRegister) .." do -- end at #".. endIndex
							result ..= numericStartBody
						elseif opCodeName == "FORNLOOP" then
							local targetRegister = usedRegisters[1]

							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							local numericEndBody = "end -- iterate + jump to #".. endIndex
							result ..= numericEndBody
						elseif opCodeName == "FORGLOOP" then
							local jumpOffset = extraData[1]
							--local aux = extraData[2]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							local genericEndBody = "end -- iterate + jump to #".. endIndex
							result ..= genericEndBody
						elseif opCodeName == "FORGPREP_INEXT" then
							local targetRegister = usedRegisters[1]
							
							local variablesBody = formatRegister(targetRegister + 2) ..", ".. formatRegister(targetRegister + 3)
							
							result ..= "for ".. variablesBody .." in ipairs(".. formatRegister(targetRegister) ..") do"
						elseif opCodeName == "FORGPREP_NEXT" then
							local targetRegister = usedRegisters[1]
							
							local variablesBody = formatRegister(targetRegister + 2) ..", ".. formatRegister(targetRegister + 3)

							result ..= "for ".. variablesBody .." in pairs(".. formatRegister(targetRegister) ..") do -- could be doing next, t"
						elseif opCodeName == "FORGPREP" then
							local targetRegister = usedRegisters[1]

							local jumpOffset = extraData[1] + 2

							-- where for FORGLOOP resides
							local endIndex = i + jumpOffset

							local endAction = actions[endIndex]
							local endUsedRegisters = endAction.usedRegisters

							local variablesBody = ""

							local totalRegisters = #endUsedRegisters
							for i, register in endUsedRegisters do
								variablesBody ..= formatRegister(register)

								if i ~= totalRegisters then
									variablesBody ..= ", "
								end
							end

							result ..= "for ".. variablesBody .." in ".. formatRegister(targetRegister) .." do -- end at #".. endIndex
						elseif opCodeName == "GETVARARGS" then
							local variableCount = extraData[1] - 1

							local retBody = ""
							if variableCount == -1 then -- MULTRET
								-- i don't know about this
								local targetRegister = usedRegisters[1]
								retBody = formatRegister(targetRegister)
							else
								for i = 1, variableCount do
									local register = usedRegisters[i]
									retBody ..= formatRegister(register)

									if i ~= variableCount then
										retBody ..= ", "
									end
								end
							end
							retBody ..= " = ..."

							result ..= retBody
						elseif opCodeName == "PREPVARARGS" then
							local numParams = extraData[1]

							result ..= "-- ... ; number of fixed args: ".. numParams
						elseif opCodeName == "LOADKX" then
							local targetRegister = usedRegisters[1]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. value
						elseif opCodeName == "JUMPX" then -- the cooler jump
							local jumpOffset = extraData[1]

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							--makeJumpMarker(endIndex)

							result ..= "-- jump to #" .. endIndex
						elseif opCodeName == "COVERAGE" then
							local hitCount = extraData[1]

							result ..= "-- coverage (".. hitCount ..")"
						elseif opCodeName == "JUMPXEQKNIL" then
							local sourceRegister = usedRegisters[1]

							local jumpOffset = extraData[1] -- if 1 then don't jump
							local aux = extraData[2]

							local reverse = bit32.rshift(aux, 0x1F) ~= 1
							local sign = if reverse then "~=" else "=="

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(sourceRegister) .." ".. sign .." nil then -- goto #".. endIndex
						elseif opCodeName == "JUMPXEQKB" then
							local sourceRegister = usedRegisters[1]

							local jumpOffset = extraData[1] -- if 1 then don't jump
							local aux = extraData[2]

							local value = tostring(toBoolean(bit32.band(aux, 1)))

							local reverse = bit32.rshift(aux, 0x1F) ~= 1
							local sign = if reverse then "~=" else "=="

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(sourceRegister) .." ".. sign .." ".. value .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPXEQKN" then
							local sourceRegister = usedRegisters[1]

							local jumpOffset = extraData[1] -- if 1 then don't jump
							local aux = extraData[2]

							local value = formatConstantValue(constants[bit32.band(aux, 0xFFFFFF) + 1])

							local reverse = bit32.rshift(aux, 0x1F) ~= 1
							local sign = if reverse then "~=" else "=="

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(sourceRegister) .." ".. sign .." ".. value .." then -- goto #".. endIndex
						elseif opCodeName == "JUMPXEQKS" then
							local sourceRegister = usedRegisters[1]

							local jumpOffset = extraData[1] -- if 1 then don't jump
							local aux = extraData[2]

							local value = formatConstantValue(constants[bit32.band(aux, 0xFFFFFF) + 1])

							local reverse = bit32.rshift(aux, 0x1F) ~= 1
							local sign = if reverse then "~=" else "=="

							-- where the script will go if the condition is met
							local endIndex = i + jumpOffset

							makeJumpMarker(endIndex)

							result ..= "if ".. formatRegister(sourceRegister) .." ".. sign .." ".. value .." then -- goto #".. endIndex
						elseif opCodeName == "CAPTURE" then
							result ..= "-- upvalue capture"
						elseif opCodeName == "SUBRK" then -- constant sub (reverse SUBK)
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. value .." - ".. formatRegister(sourceRegister)
						elseif opCodeName == "DIVRK" then -- constant div (reverse DIVK)
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. value .." / ".. formatRegister(sourceRegister)
						elseif opCodeName == "IDIV" then -- floor division
							local targetRegister = usedRegisters[1]
							local sourceLeftRegister = usedRegisters[2]
							local sourceRightRegister = usedRegisters[3]

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceLeftRegister) .." // ".. formatRegister(sourceRightRegister)
						elseif opCodeName == "IDIVK" then -- floor division with 1 constant argument
							local targetRegister = usedRegisters[1]
							local sourceRegister = usedRegisters[2]

							local value = formatConstantValue(constants[extraData[1] + 1])

							result ..= formatRegister(targetRegister) .." = ".. formatRegister(sourceRegister) .." // ".. value
						elseif opCodeName == "FASTCALL" then -- reads info from the CALL instruction
							local bfid = extraData[1] -- builtin function id
							--local jumpOffset = extraData[2]

							-- where for CALL resides
							--local callIndex = i + jumpOffset

							--local callAction = actions[callIndex]
							--local callUsedRegisters = callAction.usedRegisters
							--local callExtraData = callAction.extraData

							result ..= "-- FASTCALL; ".. Luau:GetBuiltinInfo(bfid) .."()"
						elseif opCodeName == "FASTCALL1" then -- 1 register argument
							local sourceArgumentRegister = usedRegisters[1]

							local bfid = extraData[1] -- builtin function id
							--local jumpOffset = extraData[2]

							result ..= "-- FASTCALL1; ".. Luau:GetBuiltinInfo(bfid) .."(".. formatRegister(sourceArgumentRegister) ..")"
						elseif opCodeName == "FASTCALL2" then -- 2 register arguments
							local sourceArgumentRegister = usedRegisters[1]
							local sourceArgumentRegister2 = usedRegisters[2]

							local bfid = extraData[1] -- builtin function id
							--local jumpOffset = extraData[2]

							result ..= "-- FASTCALL2; ".. Luau:GetBuiltinInfo(bfid) .."(".. formatRegister(sourceArgumentRegister) ..", ".. formatRegister(sourceArgumentRegister2) ..")"
						elseif opCodeName == "FASTCALL2K" then -- 1 register argument and 1 constant argument
							local sourceArgumentRegister = usedRegisters[1]

							local bfid = extraData[1] -- builtin function id
							--local jumpOffset = extraData[2]
							local value = formatConstantValue(constants[extraData[3] + 1])

							result ..= "-- FASTCALL2K; ".. Luau:GetBuiltinInfo(bfid) .."(".. formatRegister(sourceArgumentRegister) ..", ".. value ..")"
						elseif opCodeName == "FASTCALL3" then
							local sourceArgumentRegister = usedRegisters[1]
							local sourceArgumentRegister2 = usedRegisters[2]
							local sourceArgumentRegister3 = usedRegisters[3]

							local bfid = extraData[1] -- builtin function id

							result ..= "-- FASTCALL3; ".. Luau:GetBuiltinInfo(bfid) .."(".. formatRegister(sourceArgumentRegister) ..", ".. formatRegister(sourceArgumentRegister2) ..", ".. formatRegister(sourceArgumentRegister3) ..")"
						end
					end
					local function writeFooter()
						result ..= "\n"
					end

					writeHeader()
					writeOperationBody()
					writeFooter()

					handleJumpMarkers()
				end
			end
			writeActions(registerActions[mainProtoId])

			finalResult = processResult(result)
		else -- optdec
			local result = ""
			
			local function getIndent(level)
				return string.rep("    ", level)
			end

			local function formatConstant(k)
				if not k then return "nil" end
				if k.type == LuauBytecodeTag.LBC_CONSTANT_VECTOR then
					return string.format("Vector3.new(%g, %g, %g)", k.value.x, k.value.y, k.value.z)
				elseif k.type == LuauBytecodeTag.LBC_CONSTANT_STRING then
					return toEscapedString(k.value)
				elseif type(k.value) == "string" then
					return toEscapedString(k.value)
				else
					return tostring(k.value)
				end
			end
			
			local function decompileProto(protoId, indentLevel)
				local protoActions = registerActions[protoId]
				local proto = protoActions.proto
				local actions = protoActions.actions
				local constants = proto.constants
				local innerProtos = proto.innerProtos
				local captures = proto.captures
				
				local protoStr = ""
				
				local registerState = {} 
				local varVersionCounter = {} 
				local declaredLocals = {} 
				local localNameMap = {}
				local upvalueNameMap = {}

				if proto.hasDebugInfo then
					if proto.debugLocals then
						for _, loc in ipairs(proto.debugLocals) do
							if not localNameMap[loc.register] then localNameMap[loc.register] = {} end
							table.insert(localNameMap[loc.register], { name = loc.name, start = loc.startPC, stop = loc.endPC })
						end
					end
					if proto.debugUpvalues then
						for i, upv in ipairs(proto.debugUpvalues) do upvalueNameMap[i - 1] = upv.name end
					end
				end

				local function getBaseName(reg, pc)
					if localNameMap[reg] then
						for _, info in ipairs(localNameMap[reg]) do
							if pc >= info.start and pc <= info.stop then return info.name end
						end
					end
					return (reg < proto.numParams) and ("p" .. (reg + 1)) or ("v" .. (reg - proto.numParams + 1))
				end

				local function R_Read(reg, pc)
					return registerState[reg] or getBaseName(reg, pc)
				end

				local function R_Write(reg, pc, forceLocal)
					local base = getBaseName(reg, pc)
					local ver = (varVersionCounter[base] or 0) + 1
					varVersionCounter[base] = ver
					
					local name = base
					if ver > 1 and reg >= proto.numParams then 
						name = base .. "_" .. ver 
					end

					registerState[reg] = name
					
					if not declaredLocals[name] or forceLocal then
						declaredLocals[name] = true
						return "local " .. name
					end
					return name
				end

				local function formatUpval(idx) return upvalueNameMap[idx] or ("uv" .. idx) end

				local jumpTargets = {} -- [targetPC] = count
				local isLoopHeader = {} -- [pc] = true
				local loopEnds = {} -- [endPC] = startPC

				for i, action in ipairs(actions) do
					local op = action.opCode.name
					if string.find(op, "JUMP") then
						local offset = action.extraData[1]
						local target = i + offset + 1
						
						if not jumpTargets[target] then jumpTargets[target] = 0 end
						jumpTargets[target] = jumpTargets[target] + 1

						if offset < 0 then
							isLoopHeader[target] = true
							loopEnds[i] = target
						end
					end
				end

				local processedPC = {}

				local function decompileChunk(startPC, endPC, lvl)
					local chunk = ""
					local pc = startPC
					
					while pc < endPC do
						if processedPC[pc] then 
							pc = pc + 1 
							continue 
						end

						local action = actions[pc]
						local op = action.opCode.name
						local indent = getIndent(lvl)
						local regs = action.usedRegisters or {}
						local data = action.extraData or {}

						if isLoopHeader[pc] then
							local loopEndIdx = -1
							for j = pc, endPC do
								if loopEnds[j] == pc then loopEndIdx = j end
							end

							if loopEndIdx ~= -1 then
								chunk ..= indent .. "while true do\n"
								processedPC[pc] = true
								
								chunk ..= decompileChunk(pc + 1, loopEndIdx, lvl + 1)
								
								chunk ..= indent .. "end\n"
								pc = loopEndIdx + 1
								continue
							end
						end

						local isCondJump = (op == "JUMPIF" or op == "JUMPIFNOT" or string.find(op, "JUMPIF") or string.find(op, "JUMPXEQ"))
						if isCondJump then
							local offset = action.extraData[1]
							local target = pc + offset + 1
							
							local condStr = "???"
							if op == "JUMPIF" then condStr = "not " .. R_Read(regs[1], pc)
							elseif op == "JUMPIFNOT" then condStr = R_Read(regs[1], pc)
							elseif op == "JUMPIFEQ" then condStr = R_Read(regs[1], pc) .. " ~= " .. R_Read(regs[2], pc)
							elseif op == "JUMPIFNOTEQ" then condStr = R_Read(regs[1], pc) .. " == " .. R_Read(regs[2], pc)
							elseif op == "JUMPIFLE" then condStr = R_Read(regs[1], pc) .. " > " .. R_Read(regs[2], pc)
							elseif op == "JUMPIFLT" then condStr = R_Read(regs[1], pc) .. " >= " .. R_Read(regs[2], pc)
							elseif op == "JUMPIFNOTLE" then condStr = R_Read(regs[1], pc) .. " <= " .. R_Read(regs[2], pc)
							elseif op == "JUMPIFNOTLT" then condStr = R_Read(regs[1], pc) .. " < " .. R_Read(regs[2], pc)
							elseif string.find(op, "JUMPXEQ") then
								local aux = action.extraData[2]
								local sign = (bit32.rshift(aux, 0x1F) ~= 1) and "~=" or "=="
								local r1 = R_Read(regs[1], pc)
								local val = "nil"
								if op == "JUMPXEQKN" or op == "JUMPXEQKS" then 
									val = formatConstant(constants[bit32.band(aux, 0xFFFFFF) + 1])
								elseif op == "JUMPXEQKB" then
									val = tostring(toBoolean(bit32.band(aux, 1)))
								end
								condStr = r1 .. " " .. sign .. " " .. val
							end

							local elseStart = -1
							local ifEnd = target
							local preTargetAction = actions[target - 1]
							
							if preTargetAction and (preTargetAction.opCode.name == "JUMP" or preTargetAction.opCode.name == "JUMPX") then
								if preTargetAction.extraData[1] > 0 then
									elseStart = target
									ifEnd = target + preTargetAction.extraData[1] + 1
								end
							end

							chunk ..= indent .. "if " .. condStr .. " then\n"

							local trueBlockEnd = (elseStart ~= -1) and (elseStart - 1) or (target - 1)
							
							chunk ..= decompileChunk(pc + 1, trueBlockEnd + 1, lvl + 1)

							if elseStart ~= -1 then
								chunk ..= indent .. "else\n"
								chunk ..= decompileChunk(elseStart, ifEnd, lvl + 1)
								pc = ifEnd
							else
								pc = target
							end
							
							chunk ..= indent .. "end\n"
							continue
						end

						local line = indent
						
						if op == "MOVE" then
							line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc)
						elseif op == "LOADK" or op == "LOADKX" then
							line ..= R_Write(regs[1], pc) .. " = " .. formatConstant(constants[data[1] + 1])
						elseif op == "LOADN" then
							line ..= R_Write(regs[1], pc) .. " = " .. data[1]
						elseif op == "LOADB" then
							line ..= R_Write(regs[1], pc) .. " = " .. tostring(toBoolean(data[1]))
							if data[2] ~= 0 then pc = pc + data[2] end
						elseif op == "LOADNIL" then
							line ..= R_Write(regs[1], pc) .. " = nil"
						elseif op == "GETGLOBAL" then
							local gName = tostring(constants[data[1] + 1].value)
							if LIST_USED_GLOBALS and isValidGlobal(gName) then table.insert(usedGlobals, gName) end
							line ..= R_Write(regs[1], pc) .. " = " .. gName
						elseif op == "SETGLOBAL" then
							line ..= tostring(constants[data[1] + 1].value) .. " = " .. R_Read(regs[1], pc)
						elseif op == "GETUPVAL" then
							line ..= R_Write(regs[1], pc) .. " = " .. formatUpval(data[1])
						elseif op == "SETUPVAL" then
							line ..= formatUpval(data[1]) .. " = " .. R_Read(regs[1], pc)
						elseif op == "GETIMPORT" then
							local imp = tostring(constants[data[1] + 1].value)
							line ..= R_Write(regs[1], pc) .. " = " .. imp
						
						elseif op == "NEWTABLE" then
							line ..= R_Write(regs[1], pc) .. " = {}"
						elseif op == "DUPTABLE" then
							local tConst = constants[data[1] + 1].value
							line ..= R_Write(regs[1], pc) .. " = { --[[ DUPTABLE size: ".. tConst.size .." ]] }"
						elseif op == "SETLIST" then
							local base = regs[1]
							local src = regs[2]
							local startIdx = data[1]
							local count = data[2]
							line = ""
							if count == 0 then
								chunk ..= indent .. R_Read(base, pc) .. " = { ... } -- SETLIST MULTRET todo\n"
							else
								for k = 0, count - 2 do -- count includes base
									chunk ..= indent .. R_Read(base, pc) .. "[" .. (startIdx + k) .. "] = " .. R_Read(src + k, pc) .. "\n"
								end
							end
							
						elseif op == "GETTABLEKS" then
							line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. "." .. tostring(constants[data[2] + 1].value)
						elseif op == "SETTABLEKS" then
							line ..= R_Read(regs[2], pc) .. "." .. tostring(constants[data[2] + 1].value) .. " = " .. R_Read(regs[1], pc)
						elseif op == "GETTABLE" then
							line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. "[" .. R_Read(regs[3], pc) .. "]"
						elseif op == "SETTABLE" then
							line ..= R_Read(regs[2], pc) .. "[" .. R_Read(regs[3], pc) .. "] = " .. R_Read(regs[1], pc)

                        elseif op == "IDIV" then 
                            line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " // " .. R_Read(regs[3], pc)
                        elseif op == "IDIVK" then 
                            line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " // " .. formatConstant(constants[data[1] + 1])						

                        elseif op == "SUBRK" then 
                            line ..= R_Write(regs[1], pc) .. " = " .. formatConstant(constants[data[1] + 1]) .. " - " .. R_Read(regs[2], pc)
                        elseif op == "DIVRK" then 
                            line ..= R_Write(regs[1], pc) .. " = " .. formatConstant(constants[data[1] + 1]) .. " / " .. R_Read(regs[2], pc)

                        elseif string.find(op, "FASTCALL") then
                            line = ""

						elseif op == "ADD" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " + " .. R_Read(regs[3], pc)
						elseif op == "SUB" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " - " .. R_Read(regs[3], pc)
						elseif op == "MUL" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " * " .. R_Read(regs[3], pc)
						elseif op == "DIV" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " / " .. R_Read(regs[3], pc)
						elseif op == "POW" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " ^ " .. R_Read(regs[3], pc)
						elseif op == "MOD" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " % " .. R_Read(regs[3], pc)
						
						elseif op == "ADDK" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " + " .. formatConstant(constants[data[1] + 1])
						elseif op == "SUBK" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " - " .. formatConstant(constants[data[1] + 1])
						elseif op == "MULK" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " * " .. formatConstant(constants[data[1] + 1])
						elseif op == "DIVK" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " / " .. formatConstant(constants[data[1] + 1])
						elseif op == "MODK" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " % " .. formatConstant(constants[data[1] + 1])
						elseif op == "POWK" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " ^ " .. formatConstant(constants[data[1] + 1])

						elseif op == "NOT" then line ..= R_Write(regs[1], pc) .. " = not " .. R_Read(regs[2], pc)
						elseif op == "MINUS" then line ..= R_Write(regs[1], pc) .. " = -" .. R_Read(regs[2], pc)
						elseif op == "LENGTH" then line ..= R_Write(regs[1], pc) .. " = #" .. R_Read(regs[2], pc)
						elseif op == "AND" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " and " .. R_Read(regs[3], pc)
						elseif op == "OR" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " or " .. R_Read(regs[3], pc)
						elseif op == "ANDK" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " and " .. formatConstant(constants[data[1] + 1])
						elseif op == "ORK" then line ..= R_Write(regs[1], pc) .. " = " .. R_Read(regs[2], pc) .. " or " .. formatConstant(constants[data[1] + 1])

						elseif op == "CONCAT" then
							local s = ""
							for k = regs[2], regs[3] do
								s = s .. R_Read(k, pc) .. (k < regs[3] and " .. " or "")
							end
							line ..= R_Write(regs[1], pc) .. " = " .. s

						elseif op == "NEWCLOSURE" or op == "DUPCLOSURE" then
							local protoIndex
							if op == "NEWCLOSURE" then
								protoIndex = data[1] + 1
							else
								protoIndex = constants[data[1] + 1].value
							end
							
							local nextProto = (op == "NEWCLOSURE") and innerProtos[protoIndex] or protoTable[protoIndex - 1]
							
							local params = ""
							if nextProto.numParams > 0 then
								for p = 1, nextProto.numParams do
									params = params .. "p" .. (totalParameters + p) .. (p < nextProto.numParams and ", " or "")
								end
							end
							if nextProto.isVarArg then
								params = params .. (nextProto.numParams > 0 and ", ..." or "...")
							end

							line ..= R_Write(regs[1], pc) .. " = function(" .. params .. ")\n"
							line ..= decompileProto(nextProto.id, lvl + 1)
							line ..= indent .. "end"

						elseif op == "NAMECALL" then
							line = ""
						elseif op == "CALL" then
							local base = regs[1]
							local nArgs = data[1] - 1
							local nRet = data[2] - 1
							
							local isMethod = false
							local methodName = ""
							if pc > 1 and actions[pc-1].opCode.name == "NAMECALL" then
								isMethod = true
								methodName = tostring(constants[actions[pc-1].extraData[2] + 1].value)
							end

							local callStr = ""
							if isMethod then
								callStr = R_Read(base, pc) .. ":" .. methodName .. "("
								for k = 2, nArgs do
									callStr ..= R_Read(base + k, pc) .. (k < nArgs and ", " or "")
								end
							else
								callStr = R_Read(base, pc) .. "("
								for k = 1, nArgs do
									callStr ..= R_Read(base + k, pc) .. (k < nArgs and ", " or "")
								end
							end

							if nArgs == -1 then callStr ..= "..." end
							callStr ..= ")"
							
							if nRet == 0 then
								line ..= callStr
							else
								local rets = ""
								for k = 0, (nRet > 0 and nRet - 1 or 0) do
									rets ..= R_Write(base + k, pc) .. (k < (nRet-1) and ", " or "")
								end
								if nRet == -1 then rets = "..." end
								line ..= rets .. " = " .. callStr
							end
							
						elseif op == "RETURN" then
							line ..= "return "
							local nRet = data[1] - 2
							if nRet == -2 then -- MULTRET
								line ..= R_Read(regs[1], pc) .. ", ..."
							elseif nRet > -1 then
								for k = 0, nRet do
									line ..= R_Read(regs[1] + k, pc) .. (k < nRet and ", " or "")
								end
							end
						
						elseif op == "FORNPREP" then
							local jumpTo = pc + data[1] + 1
							local idx = regs[3]
							local limit = regs[1]
							local step = regs[2]
							line ..= "for " .. R_Write(idx, pc) .. " = " .. R_Read(idx, pc) .. ", " .. R_Read(limit, pc) .. ", " .. R_Read(step, pc) .. " do"
							chunk ..= line .. "\n"
							chunk ..= decompileChunk(pc + 1, jumpTo - 1, lvl + 1)
							chunk ..= indent .. "end\n"
							pc = jumpTo
							continue 
						elseif op == "FORNLOOP" then
							line = ""
						
						elseif op == "FORGPREP" or op == "FORGPREP_NEXT" or op == "FORGPREP_INEXT" then
							local jumpTo = pc + data[1] + 1
							local gen = regs[1]
							line ..= "for " .. R_Write(gen + 3, pc) .. ", " .. R_Write(gen + 4, pc) .. " in " .. ((op == "FORGPREP_INEXT") and "ipairs" or "pairs/next") .. "(" .. R_Read(gen, pc) .. ") do"
							
							chunk ..= line .. "\n"
							chunk ..= decompileChunk(pc + 1, jumpTo - 1, lvl + 1)
							chunk ..= indent .. "end\n"
							pc = jumpTo
							continue
						elseif op == "FORGLOOP" then
							line = ""

						elseif op == "JUMP" or op == "JUMPBACK" or op == "JUMPX" then
							 if data[1] > 0 then
								-- forward jump, maybe break or just skip?
								line ..= "-- jump to " .. (pc + data[1] + 1)
							 else
								line ..= "-- jump back " .. (pc + data[1] + 1)
							 end
						elseif op == "BREAK" then
							line ..= "break"
						else
							line ..= "-- " .. op
						end
						
						if line ~= indent and line ~= "" then
							chunk ..= line .. "\n"
						end
						
						pc = pc + 1
					end
					return chunk
				end

				protoStr ..= decompileChunk(1, #actions + 1, indentLevel)
				return protoStr
			end
			
			result ..= "\n"
			local mainProto = protoTable[mainProtoId]
			result ..= decompileProto(mainProtoId, 0)
			finalResult = processResult(result)
		end

		return finalResult
	end

	local function manager(proceed, issue)
		if proceed then
			local startTime
			local elapsedTime

			local result

			local function process()
				startTime = os.clock()
				result = finalize(organize())
				elapsedTime = os.clock() - startTime
			end
			task.spawn(process)

			-- I wish we could use coroutine.yield here
			while not result and (os.clock() - startTime) < DECOMPILER_TIMEOUT do
				task.wait()
			end

			if not result then
				return Strings.TIMEOUT
			end

			if RETURN_ELAPSED_TIME then
				return string.format(Strings.SUCCESS, result), elapsedTime
			else
				return string.format(Strings.SUCCESS, result)
			end
		else
			if issue == "COMPILATION_FAILURE" then
				local errorMessageLength = reader:len() - 1
				local errorMessage = reader:nextString(errorMessageLength)
				return string.format(Strings.COMPILATION_FAILURE, errorMessage)
			elseif issue == "UNSUPPORTED_LBC_VERSION" then
				return Strings.UNSUPPORTED_LBC_VERSION
			end
		end
	end

	bytecodeVersion = reader:nextByte()

	if bytecodeVersion == 0 then
		-- script errored
		return manager(false, "COMPILATION_FAILURE")
	elseif bytecodeVersion >= LuauBytecodeTag.LBC_VERSION_MIN and bytecodeVersion <= LuauBytecodeTag.LBC_VERSION_MAX then
		-- script uses supported bytecode version
		return manager(true)
	else
		return manager(false, "UNSUPPORTED_LBC_VERSION")
	end
end

if not USE_IN_STUDIO then
	local _ENV = (getgenv and getgenv()) or (getfenv and getfenv(1)) or _ENV
	_ENV.decompile = function(script)
		if not getscriptbytecode then
			error("Your tool is missing the function 'getscriptbytecode'")
			return
		end
		
		if typeof(script) ~= "Instance" then
			error("Invalid argument in parameter #1 'script'. Expected Instance, got " .. typeof(script))
		end
		
		local function isScriptValid()
			if script.ClassName == "Script" then
				return script.RunContext == Enum.RunContext.Client
			elseif script.ClassName == "LocalScript" 
				or script.ClassName == "ModuleScript" then
				return true
			end
		end
		
		local success, result = pcall(getscriptbytecode, script)
		if not success or type(result) ~= "string" then
			error(`Couldn't decompile bytecode: {tostring(result)}`, 2)
			return
		end
		
		local decomped, elapsedTime
		
		if DECODE_AS_BASE64 then
			local toDecode = buffer.fromstring(result)
			local decoded = Base64.decode(toDecode)
			decomped, elapsedTime = Decompile(result)
		else
			decomped, elapsedTime = Decompile(result)
		end
		
		if RETURN_ELAPSED_TIME then
			return decomped, elapsedTime
		else
			return decomped
		end
	end
else
	if DECODE_AS_BASE64 then
		local toDecode = buffer.fromstring(input)
		local decoded = Base64.decode(toDecode)
		local decomped, elapsedTime = Decompile(buffer.tostring(decoded))
		warn("done decompiling:", elapsedTime or 0)
		
		-- Some scripts like Criminality's GunClient are thousands of lines long, and directly setting string properties
		-- maxes out at 200000 characters. To get around this, we use a dummy LocalScript and use ScriptEditorService to
		-- dump the output into the dummy script, therefore bypassing Roblox's string regulations.
		game:GetService("ScriptEditorService"):UpdateSourceAsync(workspace["Disassembler"].LocalScript, function()
			return decomped
		end)
	else
		local decomped, elapsedTime = Decompile(input)
		warn("done decompiling:", elapsedTime or 0)
		
		game:GetService("ScriptEditorService"):UpdateSourceAsync(workspace["Disassembler"].LocalScript, function()
			return decomped
		end)
	end
end
