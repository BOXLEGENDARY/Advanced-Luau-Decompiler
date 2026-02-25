-- Reader
local FLOAT_PRECISION = 24

local Reader = {}

function Reader.new(bytecode)
    local stream = buffer.fromstring(bytecode)
    local cursor = 0

    local self = {}

    local string_char = string.char
    local format = string.format
    local tonumber = tonumber
    local bor = bit32.bor
    local band = bit32.band
    local lshift = bit32.lshift
    local btest = bit32.btest
    local insert = table.insert

    function self:len()
        return buffer.len(stream)
    end

    function self:nextByte()
        local result = buffer.readu8(stream, cursor)
        cursor = cursor + 1
        return result
    end

    function self:nextSignedByte()
        local result = buffer.readi8(stream, cursor)
        cursor = cursor + 1
        return result
    end

    function self:nextBytes(count)
        local result = table.create(count)
        for i = 1, count do
            result[i] = self:nextByte()
        end
        return result
    end

    function self:nextChar()
        return string_char(self:nextByte())
    end

    function self:nextUInt32()
        local result = buffer.readu32(stream, cursor)
        cursor = cursor + 4
        return result
    end

    function self:nextInt32()
        local result = buffer.readi32(stream, cursor)
        cursor = cursor + 4
        return result
    end

    function self:nextFloat()
        local result = buffer.readf32(stream, cursor)
        cursor = cursor + 4
        return tonumber(format("%0." .. FLOAT_PRECISION .. "f", result))
    end

    function self:nextVarInt()
        local result = 0
        for i = 0, 4 do
            local b = self:nextByte()
            result = bor(result, lshift(band(b, 0x7F), i * 7))
            if not btest(b, 0x80) then
                break
            end
        end
        return result
    end

    function self:nextString(len)
        len = len or self:nextVarInt()
        if len == 0 then
            return ""
        else
            local result = buffer.readstring(stream, cursor, len)
            cursor = cursor + len
            return result
        end
    end

    function self:nextDouble()
        local result = buffer.readf64(stream, cursor)
        cursor = cursor + 8
        return result
    end

    return self
end

function Reader:Set(precision)
    FLOAT_PRECISION = precision
end

return Reader