--!native
--!optimize 2

local lookupValueToCharacter = buffer.create(64)
local lookupCharacterToValue = buffer.create(256)

local alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
local padding = string.byte("=")

for index = 1, 64 do
	local value = index - 1
	local character = string.byte(alphabet, index)

	buffer.writeu8(lookupValueToCharacter, value, character)
	buffer.writeu8(lookupCharacterToValue, character, value)
end

local readu8, writeu8, readu32, create, len = buffer.readu8, buffer.writeu8, buffer.readu32, buffer.create, buffer.len
local lshift, rshift, band, bor, byteswap = bit32.lshift, bit32.rshift, bit32.band, bit32.bor, bit32.byteswap

local function encode(input: buffer): buffer
	local inputLength = len(input)
	local inputChunks = math.ceil(inputLength / 3)

	local outputLength = inputChunks * 4
	local output = create(outputLength)

	-- Since we use readu32 and chunks are 3 bytes large, we can't read the last chunk here
	for chunkIndex = 1, inputChunks - 1 do
		local inPos = (chunkIndex - 1) * 3
		local outPos = (chunkIndex - 1) * 4

		local chunk = byteswap(readu32(input, inPos))

		-- 8 + 24 - (6 * index)
		local value1 = rshift(chunk, 26)
		local value2 = band(rshift(chunk, 20), 0b111111)
		local value3 = band(rshift(chunk, 14), 0b111111)
		local value4 = band(rshift(chunk, 8), 0b111111)

		writeu8(output, outPos,     readu8(lookupValueToCharacter, value1))
		writeu8(output, outPos + 1, readu8(lookupValueToCharacter, value2))
		writeu8(output, outPos + 2, readu8(lookupValueToCharacter, value3))
		writeu8(output, outPos + 3, readu8(lookupValueToCharacter, value4))
	end

	local inputRemainder = inputLength % 3

	if inputRemainder == 1 then
		local chunk = readu8(input, inputLength - 1)

		local value1 = rshift(chunk, 2)
		local value2 = band(lshift(chunk, 4), 0b111111)

		writeu8(output, outputLength - 4, readu8(lookupValueToCharacter, value1))
		writeu8(output, outputLength - 3, readu8(lookupValueToCharacter, value2))
		writeu8(output, outputLength - 2, padding)
		writeu8(output, outputLength - 1, padding)
	elseif inputRemainder == 2 then
		local chunk = bor(
			lshift(readu8(input, inputLength - 2), 8),
			readu8(input, inputLength - 1)
		)

		local value1 = rshift(chunk, 10)
		local value2 = band(rshift(chunk, 4), 0b111111)
		local value3 = band(lshift(chunk, 2), 0b111111)

		writeu8(output, outputLength - 4, readu8(lookupValueToCharacter, value1))
		writeu8(output, outputLength - 3, readu8(lookupValueToCharacter, value2))
		writeu8(output, outputLength - 2, readu8(lookupValueToCharacter, value3))
		writeu8(output, outputLength - 1, padding)
	elseif inputRemainder == 0 and inputLength ~= 0 then
		local chunk = bor(
			lshift(readu8(input, inputLength - 3), 16),
			lshift(readu8(input, inputLength - 2), 8),
			readu8(input, inputLength - 1)
		)

		local value1 = rshift(chunk, 18)
		local value2 = band(rshift(chunk, 12), 0b111111)
		local value3 = band(rshift(chunk, 6), 0b111111)
		local value4 = band(chunk, 0b111111)

		writeu8(output, outputLength - 4, readu8(lookupValueToCharacter, value1))
		writeu8(output, outputLength - 3, readu8(lookupValueToCharacter, value2))
		writeu8(output, outputLength - 2, readu8(lookupValueToCharacter, value3))
		writeu8(output, outputLength - 1, readu8(lookupValueToCharacter, value4))
	end

	return output
end

local function decode(input: buffer): buffer
	local inputLength = len(input)
	local inputChunks = math.ceil(inputLength / 4)

	-- TODO: Support input without padding
	local inputPadding = 0
	if inputLength ~= 0 then
		if readu8(input, inputLength - 1) == padding then inputPadding += 1 end
		if readu8(input, inputLength - 2) == padding then inputPadding += 1 end
	end

	local outputLength = inputChunks * 3 - inputPadding
	local output = create(outputLength)

	for chunkIndex = 1, inputChunks - 1 do
		local inPos = (chunkIndex - 1) * 4
		local outPos = (chunkIndex - 1) * 3

		local value1 = readu8(lookupCharacterToValue, readu8(input, inPos))
		local value2 = readu8(lookupCharacterToValue, readu8(input, inPos + 1))
		local value3 = readu8(lookupCharacterToValue, readu8(input, inPos + 2))
		local value4 = readu8(lookupCharacterToValue, readu8(input, inPos + 3))

		local chunk = bor(
			lshift(value1, 18),
			lshift(value2, 12),
			lshift(value3, 6),
			value4
		)

		local character1 = rshift(chunk, 16)
		local character2 = band(rshift(chunk, 8), 0xFF)
		local character3 = band(chunk, 0xFF)

		writeu8(output, outPos,     character1)
		writeu8(output, outPos + 1, character2)
		writeu8(output, outPos + 2, character3)
	end

	if inputLength ~= 0 then
		local lastInPos = (inputChunks - 1) * 4
		local lastOutPos = (inputChunks - 1) * 3

		local lastValue1 = readu8(lookupCharacterToValue, readu8(input, lastInPos))
		local lastValue2 = readu8(lookupCharacterToValue, readu8(input, lastInPos + 1))
		local lastValue3 = readu8(lookupCharacterToValue, readu8(input, lastInPos + 2))
		local lastValue4 = readu8(lookupCharacterToValue, readu8(input, lastInPos + 3))

		local lastChunk = bor(
			lshift(lastValue1, 18),
			lshift(lastValue2, 12),
			lshift(lastValue3, 6),
			lastValue4
		)

		if inputPadding <= 2 then
			local lastCharacter1 = rshift(lastChunk, 16)
			writeu8(output, lastOutPos, lastCharacter1)

			if inputPadding <= 1 then
				local lastCharacter2 = band(rshift(lastChunk, 8), 0xFF)
				writeu8(output, lastOutPos + 1, lastCharacter2)

				if inputPadding == 0 then
					local lastCharacter3 = band(lastChunk, 0xFF)
					writeu8(output, lastOutPos + 2, lastCharacter3)
				end
			end
		end
	end

	return output
end

return {
	encode = encode,
	decode = decode,
}