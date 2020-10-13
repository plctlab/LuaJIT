------------------------------------------------------------------------------
-- DynASM RISC-V module.
--
-- Copyright (C) 2005-2020 Mike Pall. All rights reserved.
-- See dynasm.lua for full copyright notice.
------------------------------------------------------------------------------
local riscv = riscv

-- Module information:
local _info = {
  arch =	"riscv",
  description =	"DynASM RISCV module",
  version =	"1.4.0",
  vernum =	 10400,
  release =	"2016-05-24",
  author =	"Mike Pall",
  license =	"MIT",
}

-- Exported glue functions for the arch-specific module.
local _M = { _info = _info }

-- Cache library functions.
local type, tonumber, pairs, ipairs = type, tonumber, pairs, ipairs
local assert, setmetatable = assert, setmetatable
local _s = string
local sub, format, byte, char = _s.sub, _s.format, _s.byte, _s.char
local match, gmatch = _s.match, _s.gmatch
local concat, sort = table.concat, table.sort
local bit = bit or require("bit")
local band, shl, shr, sar = bit.band, bit.lshift, bit.rshift, bit.arshift
local tohex = bit.tohex

-- Inherited tables and callbacks.
local g_opt, g_arch
local wline, werror, wfatal, wwarn

-- Action name list.
-- CHECK: Keep this in sync with the C code!
local action_names = {
  -- no args, no buffer pos, terminal action:
  "STOP", "SECTION", "ESC", "REL_EXT",
  "ALIGN", "REL_LG", "LABEL_LG",
  "REL_PC", "LABEL_PC", "IMM", "IMMS"
}

-- Maximum number of section buffer positions for dasm_put().
-- CHECK: Keep this in sync with the C code!
local maxsecpos = 25 -- Keep this low, to avoid excessively long C lines.

-- Action name -> action number.
local map_action = {}
for n,name in ipairs(action_names) do
  map_action[name] = n-1
end

-- Action list buffer.
local actlist = {}

-- Argument list for next dasm_put(). Start with offset 0 into action list.
local actargs = { 0 }

-- Current number of section buffer positions for dasm_put().
local secpos = 1

------------------------------------------------------------------------------

-- Dump action names and numbers.
local function dumpactions(out)
  out:write("DynASM encoding engine action codes:\n")
  for n,name in ipairs(action_names) do
    local num = map_action[name]
    out:write(format("  %-10s %02X  %d\n", name, num, num))
  end
  out:write("\n")
end

-- Write action list buffer as a huge static C array.
local function writeactions(out, name)
  local nn = #actlist
  if nn == 0 then nn = 1; actlist[0] = map_action.STOP end
  out:write("static const unsigned int ", name, "[", nn, "] = {\n")
  for i = 1,nn-1 do
    assert(out:write("0x", tohex(actlist[i]), ",\n"))
  end
  assert(out:write("0x", tohex(actlist[nn]), "\n};\n\n"))
end

------------------------------------------------------------------------------

-- Add word to action list.
local function wputxw(n)
  assert(n >= 0 and n <= 0xffffffff and n % 1 == 0, "word out of range")
  actlist[#actlist+1] = n
end

-- Add action to list with optional arg. Advance buffer pos, too.
local function waction(action, val, a, num)
  local w = assert(map_action[action], "bad action name `"..action.."'")
  wputxw(w * 0x100000 + (val or 0) * 16)
  if a then actargs[#actargs+1] = a end
  if a or num then secpos = secpos + (num or 1) end
end

-- Flush action list (intervening C code or buffer pos overflow).
local function wflush(term)
  if #actlist == actargs[1] then return end -- Nothing to flush.
  if not term then waction("STOP") end -- Terminate action list.
  wline(format("dasm_put(Dst, %s);", concat(actargs, ", ")), true)
  actargs = { #actlist } -- Actionlist offset is 1st arg to next dasm_put().
  secpos = 1 -- The actionlist offset occupies a buffer position, too.
end

-- Put escaped word.
local function wputw(n)
  if n >= 0xff000000 then waction("ESC") end
  wputxw(n)
end

-- Reserve position for word.
local function wpos()
  local pos = #actlist+1
  actlist[pos] = ""
  return pos
end

-- Store word to reserved position.
local function wputpos(pos, n)
  assert(n >= 0 and n <= 0xffffffff and n % 1 == 0, "word out of range")
  actlist[pos] = n
end

------------------------------------------------------------------------------

-- Global label name -> global label number. With auto assignment on 1st use.
local next_global = 20
local map_global = setmetatable({}, { __index = function(t, name)
  if not match(name, "^[%a_][%w_]*$") then werror("bad global label") end
  local n = next_global
  if n > 2047 then werror("too many global labels") end
  next_global = n + 1
  t[name] = n
  return n
end})

-- Dump global labels.
local function dumpglobals(out, lvl)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("Global labels:\n")
  for i=20,next_global-1 do
    out:write(format("  %s\n", t[i]))
  end
  out:write("\n")
end

-- Write global label enum.
local function writeglobals(out, prefix)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("enum {\n")
  for i=20,next_global-1 do
    out:write("  ", prefix, t[i], ",\n")
  end
  out:write("  ", prefix, "_MAX\n};\n")
end

-- Write global label names.
local function writeglobalnames(out, name)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("static const char *const ", name, "[] = {\n")
  for i=20,next_global-1 do
    out:write("  \"", t[i], "\",\n")
  end
  out:write("  (const char *)0\n};\n")
end

------------------------------------------------------------------------------

-- Extern label name -> extern label number. With auto assignment on 1st use.
local next_extern = 0
local map_extern_ = {}
local map_extern = setmetatable({}, { __index = function(t, name)
  -- No restrictions on the name for now.
  local n = next_extern
  if n > 2047 then werror("too many extern labels") end
  next_extern = n + 1
  t[name] = n
  map_extern_[n] = name
  return n
end})

-- Dump extern labels.
local function dumpexterns(out, lvl)
  out:write("Extern labels:\n")
  for i=0,next_extern-1 do
    out:write(format("  %s\n", map_extern_[i]))
  end
  out:write("\n")
end

-- Write extern label names.
local function writeexternnames(out, name)
  out:write("static const char *const ", name, "[] = {\n")
  for i=0,next_extern-1 do
    out:write("  \"", map_extern_[i], "\",\n")
  end
  out:write("  (const char *)0\n};\n")
end

------------------------------------------------------------------------------

-- Arch-specific maps.
local map_archdef = { sp="r2", ra="r1" } -- Ext. register name -> int. name.

local map_type = {}		-- Type name -> { ctype, reg }
local ctypenum = 0		-- Type number (for Dt... macros).

-- Reverse defines for registers.
function _M.revdef(s)
  if s == "r2" then return "sp"
  elseif s == "r1" then return "ra" end
  return s
end

------------------------------------------------------------------------------

-- Template strings for MIPS instructions.
local map_op = {

  -- RV32I
  lui_2 = "00000037DU",
  auipc_2 = "00000017DU",

  jal_2 = "0000006fDJ",
  jalr_3 = "00000067DRI",

  addi_3 = "00000013DRI",
  slti_3 = "00002013DRI",
  sltiu_3 = "00003013DRI",
  xori_3 = "00004013DRI",
  ori_3 = "00006013DRI",
  andi_3 = "00007013DRI",

  slli_3 = "00001013DRi",
  srli_3 = "00005013DRi",
  srai_3 = "40005013DRi",

  add_3 = "00000033DRr",
  sub_3 = "40000033DRr",
  sll_3 = "00001033DRr",
  slt_3 = "00002033DRr",
  sltu_3 = "00003033DRr",
  xor_3 = "00004033DRr",
  srl_3 = "00005033DRr",
  sra_3 = "40005033DRr",
  or_3 = "00006033DRr",
  and_3 = "00007033DRr",

  lb_2 = "00000003DL",
  lh_2 = "00001003DL",
  lw_2 = "00002003DL",
  lbu_2 = "00004003DL",
  lhu_2 = "00005003DL",

  sb_2 = "00000023rS",
  sh_2 = "00001023rS",
  sw_2 = "00002023rS",

  beq_3 = "00000063RrB",
  bne_3 = "00001063RrB",
  blt_3 = "00004063RrB",
  bge_3 = "00005063RrB",
  bltu_3 = "00006063RrB",
  bgeu_3 = "00007063RrB",

  nop_0 = "00000013",
  li_2 = "00000013DI",
  mv_2 = "00000013DR",
  not_2 = "fff04013DR",
  neg_2 = "40000033Dr",

  j_1 = "0000006fJ",
  jal_1 = "000000efJ",
  jr_1 = "00000067R",
  jalr_1 = "000000e7R",
  ret_0 = "00008067",
  bnez_2 = "00001063RB",
  beqz_2 = "00000063RB",
  blez_2 = "00005063rB",
  bgez_2 = "00005063RB",
  bltz_2 = "00004063RB",
  bgtz_2 = "00004063rB",

  seqz_2 = "00103013DR",
  snez_2 = "00003033Dr",
  sltz_2 = "00002033DR",
  sgtz_2 = "00002033Dr",

  ebreak_0 = "00100073",

  -- RV32M
  mul_3 = "02000033DRr",
  mulh_3 = "02001033DRr",
  mulhsu_3 = "02002033DRr",
  mulhu_3 = "02003033DRr",
  div_3 = "02004033DRr",
  divu_3 = "02005033DRr",
  rem_3 = "02006033DRr",
  remu_3 = "02007033DRr",

  -- RV32F
  ["flw_2"] = "00002007FL",
  ["fsw_2"] = "00002027gS",
  ["fadd.s_3"] = "00000053FGg",
  ["fsub.s_3"] = "08000053FGg",
  ["fmul.s_3"] = "10000053FGg",
  ["fdiv.s_3"] = "18000053FGg",
  ["fmadd.s_4"] = "00000043FGgH",
  ["fmsub.s_4"] = "00000047FGgH",
  ["fnmsub.s_4"] = "0000004bFGgH",
  ["fnmadd.s_4"] = "0000004fFGgH",
  ["fsqrt.s_2"] = "58000053FG",
  ["fsgnj.s_3"] = "20000053FGg",
  ["fsgnjn.s_3"] = "20001053FGg",
  ["fsgnjx.s_3"] = "20002053FGg",
  ["fmin.s_3"] = "28000053FGg",
  ["fmax.s_3"] = "28001053FGg",
  ["fcvt.w.s_2"] = "c0000053DG",
  ["fcvt.wu.s_2"] = "c0100053DG",
  ["fmv.x.w_2"] = "e0000053DG",
  ["feq.s_3"] = "a0002053DGg",
  ["flt.s_3"] = "a0001053DGg",
  ["fle.s_3"] = "a0000053DGg",
  ["fclass.s_2"] = "e0001053DG",
  ["fcvt.s.w_2"] = "d0000053FR",
  ["fcvt.s.wu_2"] = "d0100053FR",
  ["fmv.w.x_2"] = "f0000053FR",

  -- RV32D
  ["fld_2"] = "00003007FL",
  ["fsd_2"] = "00003027gS",
  ["fadd.d_3"] = "02007053FGg",
  ["fsub.d_3"] = "0a007053FGg",
  ["fmul.d_3"] = "12007053FGg",
  ["fdiv.d_3"] = "1a007053FGg",
  ["fmadd.d_4"] = "02007043FGgH",
  ["fmsub.d_4"] = "02007047FGgH",
  ["fnmsub.d_4"] = "0200704bFGgH",
  ["fnmadd.d_4"] = "0200704fFGgH",
  ["fsqrt.d_2"] = "5a007053FG",
  ["fsgnj.d_3"] = "22000053FGg",
  ["fsgnjn.d_3"] = "22001053FGg",
  ["fsgnjx.d_3"] = "22002053FGg",
  ["fmin.d_3"] = "2a000053FGg",
  ["fmax.d_3"] = "2a001053FGg",
  ["fcvt.s.d_2"] = "40100053FG",
  ["fcvt.d.s_2"] = "42000053FG",
  ["feq.d_3"] = "a2002053DGg",
  ["flt.d_3"] = "a2001053DGg",
  ["fle.d_3"] = "a2000053DGg",
  ["fclass.d_2"] = "e2001053DG",
  ["fcvt.w.d_2"] = "c2007053DG",
  ["fcvt.wu.d_2"] = "c2107053DG",
  ["fcvt.d.w_2"] = "d2007053FR",
  ["fcvt.d.wu_2"] = "d2107053FR",

  ["fmv.d_2"] = "22000053FY",
  ["fneg.d_2"] = "22001053FY",
  ["fabs.d_2"] = "22002053FY",

  ["fadd.d_4"] = "02000053FGgM",
  ["fsub.d_4"] = "0a000053FGgM",
  ["fmul.d_4"] = "12000053FGgM",
  ["fdiv.d_4"] = "1a000053FGgM",
  ["fmadd.d_5"] = "02000043FGgHM",
  ["fmsub.d_5"] = "02000047FGgHM",
  ["fnmsub.d_5"] = "0200004bFGgHM",
  ["fnmadd.d_5"] = "0200004fFGgHM",
  ["fsqrt.3_2"] = "5a000053FGM",
  ["fcvt.w.d_3"] = "c2000053DGM",
  ["fcvt.wu.d_3"] = "c2100053DGM",
  ["fcvt.d.w_3"] = "d2000053FRM",
  ["fcvt.d.wu_3"] = "d2100053FRM",

}

------------------------------------------------------------------------------

local function parse_gpr(expr)
  local tname, ovreg = match(expr, "^([%w_]+):(r[1-3]?[0-9])$")
  local tp = map_type[tname or expr]
  if tp then
    local reg = ovreg or tp.reg
    if not reg then
      werror("type `"..(tname or expr).."' needs a register override")
    end
    expr = reg
  end
  local r = match(expr, "^r([1-3]?[0-9])$")
  if r then
    r = tonumber(r)
    if r <= 31 then return r, tp end
  end
  werror("bad register name `"..expr.."'")
end

local function parse_fpr(expr)
  local r = match(expr, "^f([1-3]?[0-9])$")
  if r then
    r = tonumber(r)
    if r <= 31 then return r end
  end
  werror("bad register name `"..expr.."'")
end

local function parse_imm(imm, bits, shift, scale, signed, action)
  local n = tonumber(imm)
  if n then
    local m = sar(n, scale)
    if shl(m, scale) == n then
      if signed then
	local s = sar(m, bits-1)
	if s == 0 then return shl(m, shift)
	elseif s == -1 then return shl(m + shl(1, bits), shift) end
      else
	if sar(m, bits) == 0 then return shl(m, shift) end
      end
    end
    werror("out of range immediate `"..imm.."'")
  elseif match(imm, "^[rf]([1-3]?[0-9])$") or
	 match(imm, "^([%w_]+):([rf][1-3]?[0-9])$") then
    werror("expected immediate operand, got register")
  else
    waction(action or "IMM",
	    (signed and 32768 or 0)+shl(scale, 10)+shl(bits, 5)+shift, imm)
    return 0
  end
end

local function parse_imm_store(imm)
  local n = tonumber(imm)
  if n then
    if n >= -2048 and n < 2048 then
      local a = band(n, 0x1f)
      local b = band(n, 0xfe0)
      return shl(a, 7) + shl(b, 25-5)
    end
    werror("out of range immediate `"..imm.."'")
  elseif match(imm, "^[rf]([1-3]?[0-9])$") or
         match(imm, "^([%w_]+):([rf][1-3]?[0-9])$") then
    werror("expected immediate operand, got register")
  else
    waction(action or "IMMS", 0, imm)
    return 0
  end
end

local function parse_disp(disp, load)
  local imm, reg = match(disp, "^(.*)%(([%w_:]+)%)$")
  if imm then
    local r = shl(parse_gpr(reg), 15)
    local extname = match(imm, "^extern%s+(%S+)$")
    if extname then
      waction("REL_EXT", map_extern[extname], nil, 1)
      return r
    else
      if load then
	return r + parse_imm(imm, 12, 20, 0, true)
      else
	return r + parse_imm_store(imm)
      end
    end
  end
  local reg, tailr = match(disp, "^([%w_:]+)%s*(.*)$")
  if reg and tailr ~= "" then
    local r, tp = parse_gpr(reg)
    if tp then
      if load then
	waction("IMM", 32768+12*32+20, format(tp.ctypefmt, tailr))
      else
	waction("IMMS", 0, format(tp.ctypefmt, tailr))
      end
      return shl(r, 15)
    end
  end
  werror("bad displacement `"..disp.."'")
end

local function parse_index(idx)
  local rt, rs = match(idx, "^(.*)%(([%w_:]+)%)$")
  if rt then
    rt = parse_gpr(rt)
    rs = parse_gpr(rs)
    return shl(rt, 16) + shl(rs, 21)
  end
  werror("bad index `"..idx.."'")
end

local function parse_label(label, def)
  local prefix = sub(label, 1, 2)
  -- =>label (pc label reference)
  if prefix == "=>" then
    return "PC", 0, sub(label, 3)
  end
  -- ->name (global label reference)
  if prefix == "->" then
    return "LG", map_global[sub(label, 3)]
  end
  if def then
    -- [1-9] (local label definition)
    if match(label, "^[1-9]$") then
      return "LG", 10+tonumber(label)
    end
  else
    -- [<>][1-9] (local label reference)
    --io.write("Usao u parse_label <>\n")
    local dir, lnum = match(label, "^([<>])([1-9])$")
    if dir then -- Fwd: 1-9, Bkwd: 11-19.
      return "LG", lnum + (dir == ">" and 0 or 10)
    end
    -- extern label (extern label reference)
    local extname = match(label, "^extern%s+(%S+)$")
    if extname then
      return "EXT", map_extern[extname]
    end
  end
  werror("bad label `"..label.."'")
end

local rnd_mode = {
  rne = 0, rtz = 1, rdn = 2, rup = 3, rmm = 4, dyn = 7
}

------------------------------------------------------------------------------

-- Handle opcodes defined with template strings.
map_op[".template__"] = function(params, template, nparams)
  if not params then return sub(template, 9) end
  local op = tonumber(sub(template, 1, 8), 16)
  local n = 1
  -- Limit number of section buffer positions used by a single dasm_put().
  -- A single opcode needs a maximum of 2 positions (ins/ext).
  if secpos+2 > maxsecpos then wflush() end
  local pos = wpos()

  -- Process each character.
  for p in gmatch(sub(template, 9), ".") do
    if p == "D" then
      op = op + shl(parse_gpr(params[n]), 7); n = n + 1
    elseif p == "R" then
      op = op + shl(parse_gpr(params[n]), 15); n = n + 1
    elseif p == "r" then
      op = op + shl(parse_gpr(params[n]), 20); n = n + 1
    elseif p == "F" then
      op = op + shl(parse_fpr(params[n]), 7); n = n + 1
    elseif p == "G" then
      op = op + shl(parse_fpr(params[n]), 15); n = n + 1
    elseif p == "g" then
      op = op + shl(parse_fpr(params[n]), 20); n = n + 1
    elseif p == "H" then
      op = op + shl(parse_fpr(params[n]), 27); n = n + 1
    elseif p == "I" then
      op = op + parse_imm(params[n], 12, 20, 0, true); n = n + 1
    elseif p == "i" then
      op = op + parse_imm(params[n], 5, 20, 0, false); n = n + 1
    elseif p == "U" then
      op = op + parse_imm(params[n], 20, 12, 0, false); n = n + 1
    elseif p == "S" then
      op = op + parse_disp(params[n], false); n = n + 1
    elseif p == "L" then
      op = op + parse_disp(params[n], true); n = n + 1
    elseif p == "B" or p == "J" then
      local mode, m, s = parse_label(params[n], false)
      if p == "B" then m = m + 2048 end
      waction("REL_"..mode, m, s, 1)
      n = n + 1
    elseif p == "M" then  --rounding mode
      op = op + shl(rnd_mode[params[n]], 12); n = n + 1
    elseif p == "Y" then
      f = parse_fpr(params[n])
      op = op + shl(f, 15) + shl(f, 20); n = n + 1
    else
      assert(false)
    end
  end
  if (op < 0) then op = 0xffffffff + op + 1 end
  wputpos(pos, op)
end

------------------------------------------------------------------------------

-- Pseudo-opcode to mark the position where the action list is to be emitted.
map_op[".actionlist_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeactions(out, name) end)
end

-- Pseudo-opcode to mark the position where the global enum is to be emitted.
map_op[".globals_1"] = function(params)
  if not params then return "prefix" end
  local prefix = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeglobals(out, prefix) end)
end

-- Pseudo-opcode to mark the position where the global names are to be emitted.
map_op[".globalnames_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeglobalnames(out, name) end)
end

-- Pseudo-opcode to mark the position where the extern names are to be emitted.
map_op[".externnames_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeexternnames(out, name) end)
end

------------------------------------------------------------------------------

-- Label pseudo-opcode (converted from trailing colon form).
map_op[".label_1"] = function(params)
  if not params then return "[1-9] | ->global | =>pcexpr" end
  if secpos+1 > maxsecpos then wflush() end
  local mode, n, s = parse_label(params[1], true)
  if mode == "EXT" then werror("bad label definition") end
  waction("LABEL_"..mode, n, s, 1)
end

------------------------------------------------------------------------------

-- Pseudo-opcodes for data storage.
map_op[".long_*"] = function(params)
  if not params then return "imm..." end
  for _,p in ipairs(params) do
    local n = tonumber(p)
    if not n then werror("bad immediate `"..p.."'") end
    if n < 0 then n = n + 2^32 end
    wputw(n)
    if secpos+2 > maxsecpos then wflush() end
  end
end

-- Alignment pseudo-opcode.
map_op[".align_1"] = function(params)
  if not params then return "numpow2" end
  if secpos+1 > maxsecpos then wflush() end
  local align = tonumber(params[1])
  if align then
    local x = align
    -- Must be a power of 2 in the range (2 ... 256).
    for i=1,8 do
      x = x / 2
      if x == 1 then
	waction("ALIGN", align-1, nil, 1) -- Action byte is 2**n-1.
	return
      end
    end
  end
  werror("bad alignment")
end

------------------------------------------------------------------------------

-- Pseudo-opcode for (primitive) type definitions (map to C types).
map_op[".type_3"] = function(params, nparams)
  if not params then
    return nparams == 2 and "name, ctype" or "name, ctype, reg"
  end
  local name, ctype, reg = params[1], params[2], params[3]
  if not match(name, "^[%a_][%w_]*$") then
    werror("bad type name `"..name.."'")
  end
  local tp = map_type[name]
  if tp then
    werror("duplicate type `"..name.."'")
  end
  -- Add #type to defines. A bit unclean to put it in map_archdef.
  map_archdef["#"..name] = "sizeof("..ctype..")"
  -- Add new type and emit shortcut define.
  local num = ctypenum + 1
  map_type[name] = {
    ctype = ctype,
    ctypefmt = format("Dt%X(%%s)", num),
    reg = reg,
  }
  wline(format("#define Dt%X(_V) (int)(ptrdiff_t)&(((%s *)0)_V)", num, ctype))
  ctypenum = num
end
map_op[".type_2"] = map_op[".type_3"]

-- Dump type definitions.
local function dumptypes(out, lvl)
  local t = {}
  for name in pairs(map_type) do t[#t+1] = name end
  sort(t)
  out:write("Type definitions:\n")
  for _,name in ipairs(t) do
    local tp = map_type[name]
    local reg = tp.reg or ""
    out:write(format("  %-20s %-20s %s\n", name, tp.ctype, reg))
  end
  out:write("\n")
end

------------------------------------------------------------------------------

-- Set the current section.
function _M.section(num)
  waction("SECTION", num)
  wflush(true) -- SECTION is a terminal action.
end

------------------------------------------------------------------------------

-- Dump architecture description.
function _M.dumparch(out)
  out:write(format("DynASM %s version %s, released %s\n\n",
    _info.arch, _info.version, _info.release))
  dumpactions(out)
end

-- Dump all user defined elements.
function _M.dumpdef(out, lvl)
  dumptypes(out, lvl)
  dumpglobals(out, lvl)
  dumpexterns(out, lvl)
end

------------------------------------------------------------------------------

-- Pass callbacks from/to the DynASM core.
function _M.passcb(wl, we, wf, ww)
  wline, werror, wfatal, wwarn = wl, we, wf, ww
  return wflush
end

-- Setup the arch-specific module.
function _M.setup(arch, opt)
  g_arch, g_opt = arch, opt
end

-- Merge the core maps and the arch-specific maps.
function _M.mergemaps(map_coreop, map_def)
  setmetatable(map_op, { __index = map_coreop })
  setmetatable(map_def, { __index = map_archdef })
  return map_op, map_def
end

return _M

------------------------------------------------------------------------------

