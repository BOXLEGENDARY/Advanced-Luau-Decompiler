local BaseStrings = {
    os.date("%Y-%m-%d %H:%M:%S"),
    "-- Decompiler By Advanced Luau Decompiler\n",
}

local CombinedBaseString = table.concat(BaseStrings, "\n")

local Strings = {
    SUCCESS                = ("-- %s\n%s"):format(CombinedBaseString, "%s"),
    TIMEOUT                = "-- DECOMPILER TIMEOUT",
    COMPILATION_FAILURE    = "-- SCRIPT FAILED TO COMPILE, ERROR:\n%s",
    UNSUPPORTED_LBC_VERSION= "-- PASSED BYTECODE IS TOO OLD OR UNSUPPORTED",
    USED_GLOBALS           = "-- USED GLOBALS: %s.\n\n",
    DECOMPILER_REMARK      = "-- DECOMPILER REMARK: %s\n"
}

return Strings