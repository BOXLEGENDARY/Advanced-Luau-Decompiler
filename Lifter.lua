--!optimize 2
--!strict

local Lifter = {}

local Luau
local Implementations

local FORMAT_PRECISION = 7 -- float precision
local INDENT_STRING = "\t" -- use tab for indentation

local table_insert = table.insert
local table_concat = table.concat
local string_format = string.format
local string_rep = string.rep
local math_floor = math.floor

function Lifter.init(luauModule, implementationsModule)
    Luau = luauModule
    Implementations = implementationsModule
    return Lifter
end

local Context = {}
Context.__index = Context

function Context.new(proto, protoId)
    local self = setmetatable({}, Context)

    self.proto = proto
    self.protoId = protoId
    self.instructions = proto.instructions
    self.constants = proto.constants
    self.innerProtos = proto.protos or proto.innerProtos -- handle structure variation

    self.lines = {}
    self.indentLevel = 0

    -- register state tracking
    self.registers = {} -- Map<RegisterIndex, ExpressionString>
    self.isRegisterInline = {} -- Map<RegisterIndex, Boolean>

    -- control flow
    self.pc = 1
    self.scopeEnds = {} -- Map<PC, Count> (End of block markers)
    self.loopEnds = {} -- Map<PC, PC> (Start -> End)  -- backward-compatible mapping

    -- CFG containers (populated after building blocks)
    self.blocks = nil
    self.pc2block = nil
    self.blockCount = 0

    -- dominator & loop info
    self.dominators = nil
    self.idom = nil
    self.loopHeaders = {} -- map headerBlockId -> { member block ids }

    return self
end

function Context:emit(text)
    local indentation = string_rep(INDENT_STRING, self.indentLevel)
    table_insert(self.lines, indentation .. text)
end

function Context:increaseIndent()
    self.indentLevel += 1
end

function Context:decreaseIndent()
    self.indentLevel = math.max(0, self.indentLevel - 1)
end

function Context:setRegister(reg, value, inline)
    self.registers[reg] = value
    self.isRegisterInline[reg] = inline or false
end

function Context:getRegister(reg)
    -- return the value if inline, otherwise return the variable name
    if self.isRegisterInline[reg] then
        return self.registers[reg]
    end
    return "v" .. reg
end

function Context:getConstant(kIndex)
    local const = self.constants[kIndex + 1]
    if not const then
        return "nil"
    end

    local cType = const.type
    local value = const.value

    if cType == Luau.BytecodeTag.LBC_CONSTANT_STRING then
        return Implementations.toEscapedString(value)
    elseif cType == Luau.BytecodeTag.LBC_CONSTANT_BOOLEAN then
        return tostring(value)
    elseif cType == Luau.BytecodeTag.LBC_CONSTANT_NUMBER then
        return tostring(value) -- simplified, Reader handles precision
    elseif cType == Luau.BytecodeTag.LBC_CONSTANT_VECTOR then
        return string_format("Vector3.new(%s, %s, %s)", value.x, value.y, value.z)
    elseif cType == Luau.BytecodeTag.LBC_CONSTANT_NIL then
        return "nil"
    elseif cType == Luau.BytecodeTag.LBC_CONSTANT_TABLE then
        return "{}" -- basic empty table, DUPTABLE handles content
    elseif cType == Luau.BytecodeTag.LBC_CONSTANT_IMPORT then
        return "import(" .. tostring(kIndex) .. ")" -- should be handled by GETIMPORT
    end

    return tostring(value)
end

function Context:getAux()
    local pc = self.pc
    local ins = self.instructions[pc + 1]
    return ins -- return raw instruction, handler decodes it
end

function Context:analyzeRegisterUsage()
    self.regUseCount = {} -- map reg -> read count
    local insCount = #self.instructions

    local function inc(r)
        if not r then return end
        local key = tonumber(r)
        if not key then return end
        self.regUseCount[key] = (self.regUseCount[key] or 0) + 1
    end

    for pc = 1, insCount do
        local ins = self.instructions[pc]
        local op = Luau:INSN_OP(ins)
        local opInfo = Luau.OpCode[op]
        if opInfo then
            local A = Luau:INSN_A(ins)
            local B = Luau:INSN_B(ins)
            local C = Luau:INSN_C(ins)
            if B then inc(B) end
            if C then inc(C) end
            if opInfo.name == "CALL" or opInfo.name == "FASTCALL" or opInfo.name == "FASTCALL1" then
                if A then inc(A) end
            end
            if opInfo.name == "MOVE" and B then inc(B) end
        end
    end
end

function Context:canInlineRegister(srcReg)
    if not self.isRegisterInline[srcReg] then return false end
    local expr = self.registers[srcReg]
    if not expr or expr == "" then return false end
    if tostring(expr):match("%(") then return false end
    if tostring(expr):match("^_G") then return false end
    local uses = (self.regUseCount and self.regUseCount[srcReg]) or 0
    if uses > 1 then
        if tostring(expr):match("^v%d+$") or tostring(expr):match('^".*"$') or tostring(expr):match("^%d+$") then
            return true
        end
        return false
    end
    return true
end

function Context:foldRegisterCopies()
    if not self.registers then return end
    local regs = {}
    for k, v in pairs(self.registers) do regs[k] = v end

    local function replaceRegToken(expr, fromReg, toExpr)
        if type(expr) ~= "string" then return expr end
        local token = "v" .. tostring(fromReg)
        local pattern = "([%W_])" .. token .. "([%W_])"
        local padded = "_" .. expr .. "_"
        local repl = "%1" .. toExpr .. "%2"
        local res = string.gsub(padded, pattern, repl)
        res = string.sub(res, 2, -2)
        if res == expr then
            if res:sub(1, #token) == token and (res:sub(#token+1,#token+1) or ""):match("[%W_]") then
                res = toExpr .. res:sub(#token+1)
            elseif res:sub(-#token) == token and (res:sub(-#token-1,-#token-1) or ""):match("[%W_]") then
                res = res:sub(1, -#token-1) .. toExpr
            end
        end
        return res
    end

    local changed = true
    local iter = 0
    while changed and iter < 32 do
        changed = false
        iter = iter + 1
        for src, expr in pairs(regs) do
            local srcMatch = tostring(expr):match("^v(%d+)$")
            if srcMatch then
                local ref = tonumber(srcMatch)
                if ref and self:canInlineRegister(ref) then
                    local replacement = tostring(self.registers[ref]) or ("v" .. ref)
                    for k, e in pairs(regs) do
                        if k ~= src and type(e) == "string" and e:find("v" .. ref, 1, true) then
                            local newe = replaceRegToken(e, ref, replacement)
                            if newe ~= e then
                                regs[k] = newe
                                changed = true
                            end
                        end
                    end
                    if self:canInlineRegister(ref) then
                        regs[src] = replacement
                        changed = true
                    end
                end
            else
                for candReg, candExpr in pairs(self.registers) do
                    if type(candExpr) == "string" and regs[src]:find("v" .. candReg, 1, true) and self:canInlineRegister(candReg) then
                        local newe = replaceRegToken(regs[src], candReg, tostring(candExpr))
                        if newe ~= regs[src] then
                            regs[src] = newe
                            changed = true
                        end
                    end
                end
            end
        end
    end

    for k, v in pairs(regs) do
        if self.registers[k] ~= v then
            self.registers[k] = v
            self.isRegisterInline[k] = true
        end
    end
end

function Context:runExpressionFolding()
    self:analyzeRegisterUsage()
    self:foldRegisterCopies()
end

function Context:buildBasicBlocks()
    local insCount = #self.instructions
    local leaders = {}

    local function mark(pc)
        if pc >= 1 and pc <= insCount then leaders[pc] = true end
    end

    mark(1)

    for i, ins in ipairs(self.instructions) do
        local op = Luau:INSN_OP(ins)
        local opInfo = Luau.OpCode[op]
        if opInfo then
            local sD = Luau:INSN_sD(ins) or 0
            if sD ~= 0 then
                local target = i + 1 + sD
                mark(target)
                mark(i + 1)
            end
            if opInfo.name == "FORNPREP" or opInfo.name == "FORGPREP" then
                local target = i + 1 + sD
                mark(target)
                mark(i + 1)
            end
            if opInfo.name:match("^JUMPIF") or opInfo.name:match("^JUMPX") then
                mark(i + 1)
            end
        else
            mark(i + 1)
        end
    end

    self.blocks = {}
    self.pc2block = {}
    local cur = nil
    for pc = 1, insCount do
        if leaders[pc] then
            cur = { id = #self.blocks + 1, startPc = pc, endPc = pc, instr = {}, succ = {}, pred = {} }
            table_insert(self.blocks, cur)
        end
        cur.endPc = pc
        table_insert(cur.instr, self.instructions[pc])
        self.pc2block[pc] = cur
    end
    self.blockCount = #self.blocks
end

function Context:buildCFG()
    if not self.blocks then return end

    local function addEdge(fromBlock, toPc)
        local toBlock = self.pc2block[toPc]
        if toBlock and not fromBlock.succ[toBlock.id] then
            fromBlock.succ[toBlock.id] = toBlock
            toBlock.pred[fromBlock.id] = fromBlock
        end
    end

    for _, block in ipairs(self.blocks) do
        local lastPc = block.endPc
        local ins = self.instructions[lastPc]
        local op = Luau:INSN_OP(ins)
        local opInfo = Luau.OpCode[op]

        if opInfo then
            local sD = Luau:INSN_sD(ins) or 0
            if sD ~= 0 then
                local targetPc = lastPc + 1 + sD
                addEdge(block, targetPc)
            end
            local isUncond = (opInfo.name == "JUMP" or opInfo.name == "JUMPBACK" or opInfo.name == "JUMPX")
            if not isUncond and lastPc + 1 <= #self.instructions then
                addEdge(block, lastPc + 1)
            end
        else
            if lastPc + 1 <= #self.instructions then addEdge(block, lastPc + 1) end
        end
    end
end

local function make_array(n, init)
    local a = {}
    for i = 1, n do a[i] = init end
    return a
end

function Context:computeDominators()
    local N = #self.blocks
    if N == 0 then return end

    local semi = make_array(N, 0)
    local idom = make_array(N, 0)
    local parent = make_array(N, 0)
    local vertex = make_array(N, 0)
    local ancestor = make_array(N, 0)
    local label = make_array(N, 0)
    local bucket = {}
    for i = 1, N do bucket[i] = {} end

    local dfsnum = {}
    local nodeByDfs = {}
    local visited = {}
    local time = 0

    local stack = { self.blocks[1] }
    while #stack > 0 do
        local node = stack[#stack]; stack[#stack] = nil
        if not visited[node.id] then
            visited[node.id] = true
            time += 1
            dfsnum[node.id] = time
            nodeByDfs[time] = node.id
            label[time] = time
            semi[time] = time
            vertex[time] = node.id
            for _, succ in pairs(node.succ) do
                if not visited[succ.id] then
                    parent[succ.id] = node.id
                    table_insert(stack, succ)
                end
            end
        end
    end

    local blockToIndex = {}
    for i = 1, time do blockToIndex[nodeByDfs[i]] = i end

    semi = make_array(time, 0)
    ancestor = make_array(time, 0)
    label = make_array(time, 0)
    vertex = make_array(time, 0)
    parent = make_array(time, 0)
    for i = 1, time do
        vertex[i] = nodeByDfs[i]
        semi[i] = i
        label[i] = i
        ancestor[i] = 0
    end
    bucket = {}
    for i = 1, time do bucket[i] = {} end

    for i = 2, time do
        local bId = vertex[i]
        local pId = parent[bId] or 1
        parent[i] = blockToIndex[pId]
    end

    local function compress(v)
        if ancestor[ancestor[v]] ~= 0 then
            compress(ancestor[v])
            if semi[label[ancestor[v]]] < semi[label[v]] then
                label[v] = label[ancestor[v]]
            end
            ancestor[v] = ancestor[ancestor[v]]
        end
    end

    local function eval(v)
        if ancestor[v] == 0 then return label[v] end
        compress(v)
        if semi[label[ancestor[v]]] >= semi[label[v]] then
            return label[v]
        else
            return label[ancestor[v]]
        end
    end

    local function link(v, w)
        ancestor[w] = v
    end

    for i = time, 2, -1 do
        local w = i
        local wBlockId = vertex[w]
        local b = self.blocks[ blockToIndex[wBlockId] ]
        for predId, _ in pairs(b.pred) do
            local v = blockToIndex[predId]
            if v then
                local u = eval(v)
                if semi[u] < semi[w] then semi[w] = semi[u] end
            end
        end
        table_insert(bucket[semi[w]], w)
        link(parent[w], w)
        for _, v in ipairs(bucket[parent[w]] or {}) do
            local u = eval(v)
            if semi[u] < semi[v] then idom[v] = u else idom[v] = parent[w] end
        end
        bucket[parent[w]] = {}
    end

    for i = 2, time do
        if idom[i] ~= semi[i] then idom[i] = idom[idom[i]] end
    end

    local idomBlock = {}
    for i = 1, time do
        local bId = vertex[i]
        if i == 1 then idomBlock[bId] = nil
        else
            local id = idom[i] or semi[i]
            if id and id >= 1 then idomBlock[bId] = vertex[id] else idomBlock[bId] = nil end
        end
    end

    self.idom = idomBlock
    self.dominators = {}
end

function Context:detectNaturalLoops()
    if not self.blocks or not self.idom then return end
    local blockIndex = {}
    for i, b in ipairs(self.blocks) do blockIndex[b.id] = i end

    for _, b in ipairs(self.blocks) do
        for succId, succ in pairs(b.succ) do
            local u = b.id
            local v = succ.id
            local cur = u
            local dominates = false
            while cur do
                if cur == v then dominates = true; break end
                cur = self.idom[cur]
            end
            if dominates then
                local header = v
                local loopSet = {}
                local stack = {u}
                loopSet[header] = true
                while #stack > 0 do
                    local n = stack[#stack]; stack[#stack] = nil
                    if not loopSet[n] then
                        loopSet[n] = true
                        local nb = self.blocks[ blockIndex[n] ]
                        for predId, _ in pairs(nb.pred) do table_insert(stack, predId) end
                    end
                end
                self.loopHeaders[header] = self.loopHeaders[header] or {}
                for k, _ in pairs(loopSet) do table_insert(self.loopHeaders[header], k) end
            end
        end
    end

    for headerId, nodes in pairs(self.loopHeaders) do
        local maxEndPc = 0
        for _, bid in ipairs(nodes) do
            local idx = blockIndex[bid]
            if idx then
                local b = self.blocks[idx]
                if b.endPc > maxEndPc then maxEndPc = b.endPc end
            end
        end
        local headerBlock = self.blocks[ blockIndex[headerId] ]
        if headerBlock then self.loopEnds[ headerBlock.startPc ] = maxEndPc end
    end
end

function Context:analyzeLoops()
    if not self.blocks then
        self:buildBasicBlocks()
        self:buildCFG()
    end
    self:computeDominators()
    self:detectNaturalLoops()
end

local OpHandlers = {}

function OpHandlers.LOADNIL(ctx, A, B)
    if B == 0 then
        ctx:emit(ctx:getRegister(A) .. " = nil")
    else
        local vars = {}
        for i = 0, B do table_insert(vars, ctx:getRegister(A + i)) end
        ctx:emit(table_concat(vars, ", ") .. " = nil")
    end
end

function OpHandlers.LOADB(ctx, A, B, C)
    local val = (B == 1) and "true" or "false"
    ctx:setRegister(A, val, true)
    if C ~= 0 then
        ctx:emit(string_format("if %s then -- +%d jump", val, C))
        ctx.pc += C
    end
end

function OpHandlers.LOADN(ctx, A, D) ctx:setRegister(A, tostring(D), true) end
function OpHandlers.LOADK(ctx, A, D) ctx:setRegister(A, ctx:getConstant(D), true) end
function OpHandlers.LOADKX(ctx, A)
    local aux = ctx:getAux()
    local ax = Luau:INSN_Ax(aux)
    ctx:setRegister(A, ctx:getConstant(ax), true)
    return 1
end

function OpHandlers.MOVE(ctx, A, B)
    ctx:setRegister(A, ctx:getRegister(B), ctx.isRegisterInline[B])
end

function OpHandlers.GETGLOBAL(ctx, A, C, auxVal)
    local constIndex = bit32.band(auxVal, 0xFFFFFF)
    local name = ctx:getConstant(constIndex):gsub('"', '')
    if name:match("^[%a_][%w_]*$") then
        ctx:setRegister(A, name, true)
    else
        ctx:setRegister(A, "_G" .. Implementations.formatIndexString(name), true)
    end
end

function OpHandlers.SETGLOBAL(ctx, A, C, auxVal)
    local constIndex = bit32.band(auxVal, 0xFFFFFF)
    local name = ctx:getConstant(constIndex):gsub('"', '')
    local val = ctx:getRegister(A)
    if name:match("^[%a_][%w_]*$") then
        ctx:emit(string_format("%s = %s", name, val))
    else
        ctx:emit(string_format("_G%s = %s", Implementations.formatIndexString(name), val))
    end
end

function OpHandlers.GETIMPORT(ctx, A, D, auxVal)
    local count = bit32.rshift(auxVal, 30)
    local id0 = bit32.band(bit32.rshift(auxVal, 20), 0x3FF)
    local id1 = bit32.band(bit32.rshift(auxVal, 10), 0x3FF)
    local id2 = bit32.band(auxVal, 0x3FF)
    local path = ctx:getConstant(id0):gsub('"', '')
    if count >= 2 then path ..= "." .. ctx:getConstant(id1):gsub('"', '') end
    if count >= 3 then path ..= "." .. ctx:getConstant(id2):gsub('"', '') end
    ctx:setRegister(A, path, true)
    return 1
end

function OpHandlers.GETTABLEKS(ctx, A, B, C, auxVal)
    local constIndex = bit32.band(auxVal, 0xFFFFFF)
    local key = ctx:getConstant(constIndex):gsub('"', '')
    local tableExpr = ctx:getRegister(B)
    ctx:setRegister(A, tableExpr .. Implementations.formatIndexString(key), true)
    return 1
end

function OpHandlers.SETTABLEKS(ctx, A, B, C, auxVal)
    local constIndex = bit32.band(auxVal, 0xFFFFFF)
    local key = ctx:getConstant(constIndex):gsub('"', '')
    local tableExpr = ctx:getRegister(B)
    local valueExpr = ctx:getRegister(A)
    ctx:emit(string_format("%s%s = %s", tableExpr, Implementations.formatIndexString(key), valueExpr))
    return 1
end

function OpHandlers.GETTABLE(ctx, A, B, C)
    ctx:setRegister(A, string_format("%s[%s]", ctx:getRegister(B), ctx:getRegister(C)), true)
end

function OpHandlers.SETTABLE(ctx, A, B, C)
    ctx:emit(string_format("%s[%s] = %s", ctx:getRegister(B), ctx:getRegister(C), ctx:getRegister(A)))
end

function OpHandlers.NEWCLOSURE(ctx, A, D)
    ctx:setRegister(A, "function_proto_" .. D, true)
end

function OpHandlers.NAMECALL(ctx, A, B, C, auxVal)
    local constIndex = bit32.band(auxVal, 0xFFFFFF)
    local methodName = ctx:getConstant(constIndex):gsub('"', '')
    local objExpr = ctx:getRegister(B)
    ctx.namecallInfo = { object = objExpr, method = methodName, reg = A }
    ctx:setRegister(A + 1, objExpr, true)
    return 1
end

function OpHandlers.CALL(ctx, A, B, C)
    local funcExpr
    local args = {}
    local startArg = A + 1

    if ctx.fastcallInfo then
        funcExpr = ctx.fastcallInfo.name
        ctx.fastcallInfo = nil
    elseif ctx.namecallInfo and ctx.namecallInfo.reg == A then
        funcExpr = string_format("%s:%s", ctx.namecallInfo.object, ctx.namecallInfo.method)
        startArg = A + 2
        ctx.namecallInfo = nil
    else
        funcExpr = ctx:getRegister(A)
    end

    if B > 1 then
        for i = 0, B - 2 do table_insert(args, ctx:getRegister(startArg + i)) end
    elseif B == 0 then
        table_insert(args, "...")
    end

    local callStr = string_format("%s(%s)", funcExpr, table_concat(args, ", "))

    if C > 1 then
        local results = {}
        for i = 0, C - 2 do
            local r = A + i
            local var = "v" .. r
            ctx:setRegister(r, var, false)
            table_insert(results, var)
        end
        ctx:emit(string_format("%s = %s", table_concat(results, ", "), callStr))
    elseif C == 0 then
        ctx:emit(string_format("%s = %s", "...", callStr))
    else
        ctx:emit(callStr)
    end
end

function OpHandlers.RETURN(ctx, A, B)
    local rets = {}
    if B > 1 then
        for i = 0, B - 2 do table_insert(rets, ctx:getRegister(A + i)) end
    elseif B == 0 then
        table_insert(rets, "...")
    end
    ctx:emit("return " .. table_concat(rets, ", "))
end

local function MakeArith(opSym)
    return function(ctx, A, B, C)
        local valB = ctx:getRegister(B)
        local valC = ctx:getRegister(C)
        ctx:setRegister(A, string_format("(%s %s %s)", valB, opSym, valC), true)
    end
end

local function MakeArithK(opSym)
    return function(ctx, A, B, C)
        local valB = ctx:getRegister(B)
        local valC = ctx:getConstant(C)
        ctx:setRegister(A, string_format("(%s %s %s)", valB, opSym, valC), true)
    end
end

OpHandlers.ADD = MakeArith("+")
OpHandlers.SUB = MakeArith("-")
OpHandlers.MUL = MakeArith("*")
OpHandlers.DIV = MakeArith("/")
OpHandlers.MOD = MakeArith("%")
OpHandlers.POW = MakeArith("^")
OpHandlers.ADDK = MakeArithK("+")
OpHandlers.SUBK = MakeArithK("-")
OpHandlers.MULK = MakeArithK("*")
OpHandlers.DIVK = MakeArithK("/")
OpHandlers.MODK = MakeArithK("%")
OpHandlers.POWK = MakeArithK("^")

function OpHandlers.JUMP(ctx, D)
    local target = ctx.pc + 1 + D
    ctx:emit(string_format("-- jump to #%d", target))
end

function OpHandlers.JUMPIF(ctx, A, D)
    local cond = ctx:getRegister(A)
    local target = ctx.pc + 1 + D
    ctx:emit(string_format("if not %s then -- goto #%d", cond, target))
    ctx:increaseIndent()
    ctx.scopeEnds[target] = (ctx.scopeEnds[target] or 0) + 1
end

function OpHandlers.JUMPIFNOT(ctx, A, D)
    local cond = ctx:getRegister(A)
    local target = ctx.pc + 1 + D
    ctx:emit(string_format("if %s then -- goto #%d", cond, target))
    ctx:increaseIndent()
    ctx.scopeEnds[target] = (ctx.scopeEnds[target] or 0) + 1
end

local function MakeCompJump(opSym)
    return function(ctx, A, D, auxVal)
        local valA = ctx:getRegister(A)
        local valB = ctx:getRegister(auxVal)
        local target = ctx.pc + 1 + D
        ctx:emit(string_format("if %s %s %s then -- goto #%d", valA, opSym, valB, target))
        ctx:increaseIndent()
        ctx.scopeEnds[target] = (ctx.scopeEnds[target] or 0) + 1
        return 1
    end
end

OpHandlers.JUMPIFEQ = MakeCompJump("==")
OpHandlers.JUMPIFNOTEQ = MakeCompJump("~=")
OpHandlers.JUMPIFLT = MakeCompJump("<")
OpHandlers.JUMPIFLE = MakeCompJump("<=")

function OpHandlers.FORNPREP(ctx, A, D)
    local limit = ctx:getRegister(A)
    local step = ctx:getRegister(A + 1)
    local idx = ctx:getRegister(A + 2)
    local target = ctx.pc + 1 + D
    ctx:emit(string_format("for %s = %s, %s, %s do", idx, idx, limit, step))
    ctx:increaseIndent()
    ctx.scopeEnds[target] = (ctx.scopeEnds[target] or 0) + 1
end

function OpHandlers.FORGLOOP(ctx, A, D, auxVal) return 1 end

function OpHandlers.FORGPREP_NEXT(ctx, A, D)
    local tbl = ctx:getRegister(A + 1)
    ctx:emit(string_format("for v%d, v%d in pairs(%s) do", A + 2, A + 3, tbl))
    ctx:increaseIndent()
    local target = ctx.pc + 1 + D
    ctx.scopeEnds[target] = (ctx.scopeEnds[target] or 0) + 1
end

function OpHandlers.FORGPREP_INEXT(ctx, A, D)
    local tbl = ctx:getRegister(A + 1)
    ctx:emit(string_format("for v%d, v%d in ipairs(%s) do", A + 2, A + 3, tbl))
    ctx:increaseIndent()
    local target = ctx.pc + 1 + D
    ctx.scopeEnds[target] = (ctx.scopeEnds[target] or 0) + 1
end

function OpHandlers.FASTCALL(ctx, A, D, auxVal)
    local builtinName = Luau:GetBuiltinInfo(A)
    ctx.fastcallInfo = { name = builtinName, targetReg = A }
    return 0
end

function OpHandlers.FASTCALL1(ctx, A, D, auxVal) return OpHandlers.FASTCALL(ctx, A, D, auxVal) end
function OpHandlers.FASTCALL2(ctx, A, D, auxVal) return OpHandlers.FASTCALL(ctx, A, D, auxVal) end
function OpHandlers.FASTCALL3(ctx, A, D, auxVal)
    local builtinName = Luau:GetBuiltinInfo(A)
    ctx.fastcallInfo = { name = builtinName, args = {bit32.band(auxVal, 0xFF), bit32.band(bit32.rshift(auxVal, 8), 0xFF)} }
    return 1
end

OpHandlers.NOT = function(ctx, A, B) ctx:setRegister(A, "not " .. ctx:getRegister(B), true) end
OpHandlers.MINUS = function(ctx, A, B) ctx:setRegister(A, "-" .. ctx:getRegister(B), true) end
OpHandlers.LENGTH = function(ctx, A, B) ctx:setRegister(A, "#" .. ctx:getRegister(B), true) end
OpHandlers.AND = MakeArith("and")
OpHandlers.OR = MakeArith("or")
OpHandlers.ANDK = MakeArithK("and")
OpHandlers.ORK = MakeArithK("or")

function OpHandlers.GETUPVAL(ctx, A, B) ctx:setRegister(A, "upval" .. B, true) end
function OpHandlers.SETUPVAL(ctx, A, B) ctx:emit(string_format("upval%d = %s", B, ctx:getRegister(A))) end

function OpHandlers.GETVARARGS(ctx, A, B)
    if B == 0 then
        ctx:emit(ctx:getRegister(A) .. " = ... -- multret")
    else
        local vars = {}
        for i = 0, B - 2 do table_insert(vars, ctx:getRegister(A + i)) end
        ctx:emit(table_concat(vars, ", ") .. " = ...")
    end
end

function OpHandlers.CONCAT(ctx, A, B, C)
    local parts = {}
    for i = B, C do table_insert(parts, ctx:getRegister(i)) end
    ctx:setRegister(A, table_concat(parts, " .. "), true)
end

local function MakeCompKJump(type)
    return function(ctx, A, D, auxVal)
        local valA = ctx:getRegister(A)
        local target = ctx.pc + 1 + D
        local isNot = bit32.band(bit32.rshift(auxVal, 31), 1) == 1
        local op = isNot and "~=" or "=="
        local kVal
        if type == "NIL" then kVal = "nil"
        elseif type == "B" then kVal = (bit32.band(auxVal, 1) == 1) and "true" or "false"
        else kVal = ctx:getConstant(bit32.band(auxVal, 0xFFFFFF)) end
        ctx:emit(string_format("if %s %s %s then -- goto #%d", valA, op, kVal, target))
        ctx:increaseIndent()
        ctx.scopeEnds[target] = (ctx.scopeEnds[target] or 0) + 1
        return 1
    end
end

OpHandlers.JUMPXEQKNIL = MakeCompKJump("NIL")
OpHandlers.JUMPXEQKB = MakeCompKJump("B")
OpHandlers.JUMPXEQKN = MakeCompKJump("N")
OpHandlers.JUMPXEQKS = MakeCompKJump("S")
OpHandlers.IDIV = MakeArith("//")
OpHandlers.IDIVK = MakeArithK("//")

function OpHandlers.SUBRK(ctx, A, B, C) ctx:setRegister(A, string_format("(%s - %s)", ctx:getConstant(B), ctx:getRegister(C)), true) end
function OpHandlers.DIVRK(ctx, A, B, C) ctx:setRegister(A, string_format("(%s / %s)", ctx:getConstant(B), ctx:getRegister(C)), true) end
function OpHandlers.GETTABLEN(ctx, A, B, C) ctx:setRegister(A, string_format("%s[%d]", ctx:getRegister(B), C + 1), true) end
function OpHandlers.SETTABLEN(ctx, A, B, C) ctx:emit(string_format("%s[%d] = %s", ctx:getRegister(B), C + 1, ctx:getRegister(A))) end
function OpHandlers.SETLIST(ctx, A, B, C, auxVal) ctx:emit(string_format("-- setlist v%d, start index %d", A, auxVal)); return 1 end
function OpHandlers.DUPTABLE(ctx, A, D) ctx:setRegister(A, "{}", true) end
function OpHandlers.JUMPBACK(ctx, D) ctx:emit(string_format("-- jump back to #%d", ctx.pc + 1 + D)) end
function OpHandlers.JUMPX(ctx, E) ctx:emit(string_format("-- jump long to #%d", ctx.pc + 1 + E)) end

function Lifter.decompile(proto, protoId)
    if not Luau then error("Lifter not initialized!", 2) end

    local ctx = Context.new(proto, protoId)
    ctx:analyzeLoops()
    ctx:runExpressionFolding()

    if ctx.innerProtos and #ctx.innerProtos > 0 then
        for i, subProto in ipairs(ctx.innerProtos) do
            local subId = protoId .. "_" .. (i - 1)
            ctx:emit(string_format("local function function_proto_%d(...)", i - 1))
            ctx:increaseIndent()
            ctx:emit(Lifter.decompile(subProto, subId))
            ctx:decreaseIndent()
            ctx:emit("end\n")
        end
    end

    local insCount = #ctx.instructions
    while ctx.pc <= insCount do
        local ends = ctx.scopeEnds[ctx.pc]
        if ends then
            for _ = 1, ends do
                ctx:decreaseIndent()
                ctx:emit("end")
            end
            ctx:emit("")
        end

        if ctx.loopEnds and ctx.loopEnds[ctx.pc] then
            local endPc = ctx.loopEnds[ctx.pc]
            ctx:emit(string_format("while -- loop header at #%d do", ctx.pc))
            ctx:increaseIndent()
            ctx.scopeEnds[endPc + 1] = (ctx.scopeEnds[endPc + 1] or 0) + 1
        end

        local ins = ctx.instructions[ctx.pc]
        local op = Luau:INSN_OP(ins)
        local opInfo = Luau.OpCode[op]

        if not opInfo then
            ctx:emit(string_format("-- UNKNOWN OPCODE: %d", op))
            ctx.pc += 1
            continue
        end

        local A = Luau:INSN_A(ins)
        local B = Luau:INSN_B(ins)
        local C = Luau:INSN_C(ins)
        local D = Luau:INSN_D(ins)
        local sD = Luau:INSN_sD(ins)

        local handler = OpHandlers[opInfo.name]
        local skip = 0

        if handler then
            local auxVal = opInfo.aux and ctx.instructions[ctx.pc + 1] or nil
            local result = handler(ctx, A, B or D, C, auxVal, sD)
            skip = result or (opInfo.aux and 1 or 0)
        else
            ctx:emit(string_format("-- %s A:%d B:%d C:%d", opInfo.name, A, B or 0, C or 0))
        end

        ctx.pc += 1 + skip
    end

    while ctx.indentLevel > 0 do
        ctx:decreaseIndent()
        ctx:emit("end -- forced close")
    end

    return table_concat(ctx.lines, "\n")
end

return Lifter
