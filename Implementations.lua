local _ENV = (getgenv or getfenv)()

local Implementations = {}

local type, tostring, string_find, string_rep = type, tostring, string.find, string.rep

-- from number to boolean
function Implementations.toBoolean(n)
	return n ~= 0
end

-- an easy way to escape string, most developers better code like this!!!!
function Implementations.toEscapedString(s)
	if type(s) == "string" then
		local hasQuotationMarks = string_find(s, '"')
		local hasApostrophes = string_find(s, "'")

		if hasQuotationMarks and hasApostrophes then
			return "[[" .. s .. "]]"
		elseif hasQuotationMarks then
			return "'" .. s .. "'"
		end

		return '"' .. s .. '"'
	end

	return tostring(s)
end

-- picks indexing method based on characters in a string
function Implementations.formatIndexString(s)
	if type(s) == "string" then
		if string_find(s, "^[%a_][%w_]*$") then
			return "." .. s
		end
		return `["{s}"]`
	end
	return tostring(s)
end

-- add left side character padding to x
function Implementations.padLeft(x, char, padding)
	local str = tostring(x)
	return string_rep(char, padding - #str) .. str
end

-- add right side character padding to x
function Implementations.padRight(x, char, padding)
	local str = tostring(x)
	return str .. string_rep(char, padding - #str)
end

-- returns true if passed string is a key pointing to a Roblox global
function Implementations.isGlobal(s)
	return _ENV[s] ~= nil
end

return Implementations