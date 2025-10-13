# Advanced Luau Decompiler
**Release — 06/16/2025**  
i just optimize a bit

---

## Loadstring
```lua
local Decompile do
	local Success, Decompile_Source = pcall(function()
		return game:HttpGet("https://raw.githubusercontent.com/BOXLEGENDARY/Advanced-Luau-Decompiler/refs/heads/main/init.lua", true)
	end)
	
	if Success then
		local CONSTANTS = [[
local ENABLED_REMARKS = {
	COLD_REMARK = false,
	INLINE_REMARK = false -- currently unused
}
------------------------------------------------------------------------------------------------------------------------------------------------------------------------
local DECOMPILER_TIMEOUT = 2 -- seconds
local READER_FLOAT_PRECISION = 7 -- up to 99
local DECOMPILER_MODE = "disasm" -- disasm/optdec
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
------------------------------------------------------------------------------------------------------------------------------------------------------------------------]]
		
		xpcall(function()
			return loadstring(
				string.gsub(
					string.gsub(
						Decompile_Source, "return %(x %% 2^32%) // %(2^disp%)", "return math.floor((x %% 2^32) / (2^disp))", 1
					), ";;CONSTANTS HERE;;", CONSTANTS
				), "Advanced-Luau-Decompiler"
			)()
		end, warn)
		
		local _ENV = getgenv and getgenv() or getfenv and getfenv(1) or _ENV
		Decompile = _ENV.decompile
	end
end
```

---

## Developer

by: `ZxL`

---

## Credits

[w.a.e](https://github.com/w-a-e) - Creator

[break-core](https://github.com/break-core) - Base64
