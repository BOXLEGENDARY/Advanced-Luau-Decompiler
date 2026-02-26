--!strict
--!optimize 2
--!native

local PADDING = 61

local ALPHABET = buffer.create(64)
do
	local chars = {
		65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,
		81,82,83,84,85,86,87,88,89,90,
		97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,
		113,114,115,116,117,118,119,120,121,122,
		48,49,50,51,52,53,54,55,56,57,
		43,47
	}
	for i=0,63 do
		buffer.writeu8(ALPHABET, i, chars[i+1])
	end
end

local DECODE = buffer.create(256)
do
	for i=0,255 do
		buffer.writeu8(DECODE, i, 255)
	end
	for i=0,63 do
		local c = buffer.readu8(ALPHABET, i)
		buffer.writeu8(DECODE, c, i)
	end
	buffer.writeu8(DECODE, PADDING, 254)
end

local readu8 = buffer.readu8
local writeu8 = buffer.writeu8
local len = buffer.len
local create = buffer.create

local function Encode(input: buffer): buffer
	local inLen = len(input)
	if inLen == 0 then return create(0) end

	local out = create(((inLen + 2) // 3) * 4)

	local i = 0
	local o = 0

	while i + 2 < inLen do
		local b0 = readu8(input, i)
		local b1 = readu8(input, i+1)
		local b2 = readu8(input, i+2)

		local v = b0 * 65536 + b1 * 256 + b2

		writeu8(out, o,   readu8(ALPHABET, v // 262144))
		writeu8(out, o+1, readu8(ALPHABET, (v // 4096) % 64))
		writeu8(out, o+2, readu8(ALPHABET, (v // 64) % 64))
		writeu8(out, o+3, readu8(ALPHABET, v % 64))

		i += 3
		o += 4
	end

	local rem = inLen - i
	if rem == 1 then
		local b0 = readu8(input, i)
		writeu8(out, o,   readu8(ALPHABET, b0 // 4))
		writeu8(out, o+1, readu8(ALPHABET, (b0 % 4) * 16))
		writeu8(out, o+2, PADDING)
		writeu8(out, o+3, PADDING)
	elseif rem == 2 then
		local b0 = readu8(input, i)
		local b1 = readu8(input, i+1)

		writeu8(out, o,   readu8(ALPHABET, b0 // 4))
		writeu8(out, o+1, readu8(ALPHABET, ((b0 % 4) * 16) + (b1 // 16)))
		writeu8(out, o+2, readu8(ALPHABET, (b1 % 16) * 4))
		writeu8(out, o+3, PADDING)
	end

	return out
end

local function Decode(input: buffer): (buffer?, string?)
	local inLen = len(input)
	if inLen == 0 then return create(0) end

	if inLen % 4 ~= 0 then
		return nil, "Invalid Base64 length"
	end

	local pad = 0
	if readu8(input, inLen-1) == PADDING then
		pad += 1
		if readu8(input, inLen-2) == PADDING then
			pad += 1
		end
	end

	local out = create((inLen // 4) * 3 - pad)

	local i = 0
	local o = 0

	while i < inLen do
		local c0 = readu8(input, i)
		local c1 = readu8(input, i+1)
		local c2 = readu8(input, i+2)
		local c3 = readu8(input, i+3)

		local d0 = readu8(DECODE, c0)
		local d1 = readu8(DECODE, c1)
		local d2 = readu8(DECODE, c2)
		local d3 = readu8(DECODE, c3)

		if d0 >= 64 or d1 >= 64 then
			return nil, "Invalid Base64 character"
		end

		if c2 == PADDING then
			if c3 ~= PADDING or i + 4 ~= inLen then
				return nil, "Invalid padding"
			end
			local v = d0 * 262144 + d1 * 4096
			writeu8(out, o, v // 65536)
			break
		elseif c3 == PADDING then
			if i + 4 ~= inLen then
				return nil, "Invalid padding position"
			end
			if d2 >= 64 then
				return nil, "Invalid Base64 character"
			end
			local v = d0 * 262144 + d1 * 4096 + d2 * 64
			writeu8(out, o,     v // 65536)
			writeu8(out, o + 1, (v // 256) % 256)
			break
		else
			if d2 >= 64 or d3 >= 64 then
				return nil, "Invalid Base64 character"
			end
			local v = d0 * 262144 + d1 * 4096 + d2 * 64 + d3
			writeu8(out, o,     v // 65536)
			writeu8(out, o + 1, (v // 256) % 256)
			writeu8(out, o + 2, v % 256)
		end

		i += 4
		o += 3
	end

	return out
end

return {
	Encode = Encode,
	Decode = Decode
}