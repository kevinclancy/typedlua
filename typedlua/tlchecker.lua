--[[
This file implements Typed Lua type checker
]]

if not table.unpack then table.unpack = unpack end

local tlchecker = {}

local tlast = require "typedlua.tlast"
local tlst = require "typedlua.tlst"
local tltype = require "typedlua.tltype"
local tlparser = require "typedlua.tlparser"
local tldparser = require "typedlua.tldparser"

local Value = tltype.Value()
local Any = tltype.Any()
local Nil = tltype.Nil()
local Self = tltype.Self()
local False = tltype.False()
local True = tltype.True()
local Boolean = tltype.Boolean()
local Number = tltype.Number()
local String = tltype.String()
local Integer = tltype.Integer(false)

local check_block, check_stm, check_exp, check_var, check_id

local function lineno (s, i)
  if i == 1 then return 1, 1 end
  local rest, num = s:sub(1,i):gsub("[^\n]*\n", "")
  local r = #rest
  return 1 + num, r ~= 0 and r or 1
end

local function typeerror (env, tag, msg, pos)
  local l, c = lineno(env.subject, pos)
  local error_msg = { tag = tag, filename = env.filename, msg = msg, l = l, c = c }
  table.insert(env.messages, error_msg)
end

local function set_type (node, t)
  node["type"] = t
end

local function get_type (node)
  return node and tltype.unfold(node["type"]) or Nil
end

local check_self_field

local function check_self (env, torig, t, pos)
  local msg = string.format("self type appearing in a place that is not a first parameter or a return type inside type '%s', replacing with 'any'", tltype.tostring(torig))
  if tltype.isSelf(t) then
    typeerror(env, "self", msg, pos)
    return tltype.Any()
  elseif tltype.isRecursive(t) then
    local r = tltype.Recursive(t[1], check_self(env, torig, t[2], pos))
    r.name = t.name
    return r
  elseif tltype.isUnion(t) or
         tltype.isUnionlist(t) or
         tltype.isTuple(t) then
   local r = { tag = t.tag, name = t.name }
   for k, v in ipairs(t) do
     r[k] = check_self(env, torig, v, pos)
   end
   return r
  elseif tltype.isFunction(t) then
    local r = tltype.Function(check_self(env, torig, t[1], pos),
                              check_self(env, torig, t[2], pos))
    r.name = t.name
    return r
  elseif tltype.isVararg(t) then
    local r = tltype.Vararg(check_self(env, torig, t[1], pos))
    r.name = t.name
    return r
  elseif tltype.isTable(t) then
    local l = {}
    for k, v in ipairs(t) do
      table.insert(l, tltype.Field(v.const, v[1], check_self_field(env, torig, v[2], pos)))
    end
    local r = tltype.Table(table.unpack(l))
    r.unique = t.unique
    r.open = t.open
    return r
  else
    return t
  end
end

function check_self_field(env, torig, t, pos)
  local msg = string.format("self type cannot appear in declaration of type '%s', replacing with 'any'", tltype.tostring(torig))
  if tltype.isRecursive(t) then
    local r = tltype.Recursive(t[1], check_self_field(env, torig, t[2], pos))
    r.name = t.name
    return r
  elseif tltype.isUnion(t) or
         tltype.isUnionlist(t) or
         tltype.isTuple(t) then
   local r = { tag = t.tag, name = t.name }
   for k, v in ipairs(t) do
     r[k] = check_self_field(env, torig, v, pos)
   end
   return r
  elseif tltype.isFunction(t) then
    local input = t[1]
    assert(tltype.isTuple(input), "BUG: function input type is not a tuple")
    if tltype.isSelf(input[1]) then -- method
      local ninput = { tag = input.tag, tltype.Self() }
      for i = 2, #input do
        ninput[i] = check_self(env, torig, input[i], pos)
      end
      local r = tltype.Function(ninput, t[2])
      r.name = t.name
      return r
    else
      local r = tltype.Function(check_self(env, torig, t[1], pos),
                                check_self(env, torig, t[2], pos))
      r.name = t.name
      return r
    end
  elseif tltype.isTable(t) then
    local l = {}
    for k, v in ipairs(t) do
      table.insert(l, tltype.Field(v.const, v[1], check_self_field(env, torig, v[2], pos)))
    end
    local r = tltype.Table(table.unpack(l))
    r.unique = t.unique
    r.open = t.open
    return r
  else
    return check_self(env, torig, t, pos)
  end
end

local function get_interface (env, name, pos)
  local t = tlst.get_interface(env, name)
  if not t then
    return tltype.GlobalVariable(env, name, pos, typeerror)
  else
    return t
  end
end

local function replace_names (env, t, pos, ignore)
  ignore = ignore or {}
  if tltype.isRecursive(t) then
    local link = ignore[t[1]]
    ignore[t[1]] = true
    local r = tltype.Recursive(t[1], replace_names(env, t[2], pos, ignore))
    r.name = t.name
    ignore[t[1]] = link
    return r
  elseif tltype.isLiteral(t) or
     tltype.isBase(t) or
     tltype.isNil(t) or
     tltype.isValue(t) or
     tltype.isAny(t) or
     tltype.isSelf(t) or
     tltype.isVoid(t) then
    return t
  elseif tltype.isUnion(t) or
         tltype.isUnionlist(t) or
         tltype.isTuple(t) then
    local r = { tag = t.tag, name = t.name }
    for k, v in ipairs(t) do
      r[k] = replace_names(env, t[k], pos, ignore)
    end
    return r
  elseif tltype.isFunction(t) then
    t[1] = replace_names(env, t[1], pos, ignore)
    t[2] = replace_names(env, t[2], pos, ignore)
    return t
  elseif tltype.isTable(t) then
    for k, v in ipairs(t) do
      t[k][2] = replace_names(env, t[k][2], pos, ignore)
    end
    return t
  elseif tltype.isVariable(t) then
    if not ignore[t[1]] then
      local r = replace_names(env, get_interface(env, t[1], pos), pos, ignore)
      r.name = t[1]
      return r
    else
      return t
    end
  elseif tltype.isVararg(t) then
    t[1] = replace_names(env, t[1], pos, ignore)
    return t
  else
    return t
  end
end

local function close_type (t)
  if tltype.isUnion(t) or
     tltype.isUnionlist(t) or
     tltype.isTuple(t) then
    for k, v in ipairs(t) do
      close_type(v)
    end
  else
    if t.open then t.open = nil end
  end
end

local function searchpath (name, path)
  if package.searchpath then
    return package.searchpath(name, path)
  else
    local error_msg = ""
    name = string.gsub(name, '%.', '/')
    for tldpath in string.gmatch(path, "([^;]*);") do
      tldpath = string.gsub(tldpath, "?", name)
      local f = io.open(tldpath, "r")
      if f then
        f:close()
        return tldpath
      else
        error_msg = error_msg .. string.format("no file '%s'\n", tldpath)
      end
    end
    return nil, error_msg
  end
end

local function infer_return_type (env)
  local l = tlst.get_return_type(env)
  if #l == 0 then
    if env.strict then
      return tltype.Void()
    else
      return tltype.Tuple({ Nil }, true)
    end
  else
    local r = tltype.Unionlist(table.unpack(l))
    if tltype.isAny(r) then r = tltype.Tuple({ Any }, true) end
    close_type(r)
    return r
  end
end

local function check_masking (env, local_name, pos)
  local masked_local = tlst.masking(env, local_name)
  if masked_local then
    local l, c = lineno(env.subject, masked_local.pos)
    msg = "masking previous declaration of local %s on line %d"
    msg = string.format(msg, local_name, l)
    typeerror(env, "mask", msg, pos)
  end
end

local function check_unused_locals (env)
  local l = tlst.unused(env)
  for k, v in pairs(l) do
    local msg = string.format("unused local '%s'", k)
    typeerror(env, "unused", msg, v.pos)
  end
end

local function check_tl (env, name, path, pos)
  local file = io.open(path, "r")
  local subject = file:read("*a")
  local s, f = env.subject, env.filename
  io.close(file)
  local ast, msg = tlparser.parse(subject, path, env.strict, env.integer)
  if not ast then
    typeerror(env, "syntax", msg, pos)
    return Any
  end
  env.subject = subject
  env.filename = path
  tlst.begin_function(env)
  check_block(env, ast)
  local t1 = tltype.first(infer_return_type(env))
  tlst.end_function(env)
  env.subject = s
  env.filename = f
  return t1
end

local function check_interface (env, stm)
  local name, t, is_local = stm[1], stm[2], stm.is_local
  if tlst.get_interface(env, name) then
    local msg = "attempt to redeclare interface '%s'"
    msg = string.format(msg, name)
    typeerror(env, "alias", msg, stm.pos)
  else
    check_self(env, t, t, stm.pos)
    local t = replace_names(env, t, stm.pos)
    t.name = name
    tlst.set_interface(env, name, t, is_local)
  end
  return false
end

local function check_parameters (env, parlist, selfimplicit, pos)
  local len = #parlist
  if len == 0 then
    if env.strict then
      return tltype.Void()
    else
      return tltype.Tuple({ Value }, true)
    end
  else
    local l = {}
    if parlist[1][1] == "self" and not parlist[1][2] and not selfimplicit then
      parlist[1][2] = Self
    end
    for i = 1, len do
      if not parlist[i][2] then parlist[i][2] = Any end
      l[i] = replace_names(env, parlist[i][2], pos)
    end
    if parlist[len].tag == "Dots" then
      local t = parlist[len][1] or Any
      l[len] = t
      tlst.set_vararg(env, t)
      return tltype.Tuple(l, true)
    else
      if env.strict then
        return tltype.Tuple(l)
      else
        l[len + 1] = Value
        return tltype.Tuple(l, true)
      end
    end
  end
end


local function check_userdata (env, stm)
  local name, t, is_local = stm[1], stm[2], stm.is_local
  if tlst.get_userdata(env, name) then
    local msg = "attempt to redeclare userdata '%s'"
    msg = string.format(msg, name)
    typeerror(env, "alias", msg, stm.pos)
  else
    tlst.set_userdata(env, name, t, is_local)
  end
end

local function check_tld (env, name, path, pos)
  local ast, msg = tldparser.parse(path, env.strict, env.integer)
  if not ast then
    typeerror(env, "syntax", msg, pos)
    return Any
  end
  local t = tltype.Table()
  for k, v in ipairs(ast) do
    local tag = v.tag
    if tag == "Id" then
      table.insert(t, tltype.Field(v.const, tltype.Literal(v[1]), v[2]))
    elseif tag == "Interface" then
      check_interface(env, v)
    elseif tag == "Userdata" then
      check_userdata(env, v)
    else
      error("trying to check a description item, but got a " .. tag)
    end
  end
  return t
end

local function check_require (env, name, pos, extra_path)
  extra_path = extra_path or ""
  if not env["loaded"][name] then
    local path = string.gsub(package.path..";", "[.]lua;", ".tl;")
    local filepath, msg1 = searchpath(extra_path .. name, path)
    if filepath then
      if string.find(filepath, env.parent) then
        env["loaded"][name] = Any
        typeerror(env, "load", "circular require", pos)
      else
        env["loaded"][name] = check_tl(env, name, filepath, pos)
      end
    else
      path = string.gsub(package.path..";", "[.]lua;", ".tld;")
      local filepath, msg2 = searchpath(extra_path .. name, path)
      if filepath then
        env["loaded"][name] = check_tld(env, name, filepath, pos)
      else
        env["loaded"][name] = Any
        local s, m = pcall(require, name)
        if not s then
          if string.find(m, "syntax error") then
            typeerror(env, "syntax", m, pos)
          else
            local msg = "could not load '%s'%s%s%s"
            msg = string.format(msg, name, msg1, msg2, m)
            typeerror(env, "load", msg, pos)
          end
        end
      end
    end
  end
  return env["loaded"][name]
end

local function check_arith (env, exp, op)
  local exp1, exp2 = exp[2], exp[3]
  check_exp(env, exp1)
  check_exp(env, exp2)
  local t1, t2 = tltype.first(get_type(exp1)), tltype.first(get_type(exp2))
  local msg = "attempt to perform arithmetic on a '%s'"
  if tltype.subtype(t1, tltype.Integer(true)) and
     tltype.subtype(t2, tltype.Integer(true)) then
    if op == "div" or op == "pow" then
      set_type(exp, Number)
    else
      set_type(exp, Integer)
    end
  elseif tltype.subtype(t1, Number) and tltype.subtype(t2, Number) then
    set_type(exp, Number)
    if op == "idiv" then
      local msg = "integer division on floats"
      typeerror(env, "arith", msg, exp1.pos)
    end
  elseif tltype.isAny(t1) then
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "any", msg, exp1.pos)
  elseif tltype.isAny(t2) then
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t2))
    typeerror(env, "any", msg, exp2.pos)
  else
    set_type(exp, Any)
    local wrong_type, wrong_pos = tltype.general(t1), exp1.pos
    if tltype.subtype(t1, Number) or tltype.isAny(t1) then
      wrong_type, wrong_pos = tltype.general(t2), exp2.pos
    end
    msg = string.format(msg, tltype.tostring(wrong_type))
    typeerror(env, "arith", msg, wrong_pos)
  end
end

local function check_bitwise (env, exp, op)
  local exp1, exp2 = exp[2], exp[3]
  check_exp(env, exp1)
  check_exp(env, exp2)
  local t1, t2 = tltype.first(get_type(exp1)), tltype.first(get_type(exp2))
  local msg = "attempt to perform bitwise on a '%s'"
  if tltype.subtype(t1, tltype.Integer(true)) and
     tltype.subtype(t2, tltype.Integer(true)) then
    set_type(exp, Integer)
  elseif tltype.isAny(t1) then
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "any", msg, exp1.pos)
  elseif tltype.isAny(t2) then
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t2))
    typeerror(env, "any", msg, exp2.pos)
  else
    set_type(exp, Any)
    local wrong_type, wrong_pos = tltype.general(t1), exp1.pos
    if tltype.subtype(t1, Number) or tltype.isAny(t1) then
      wrong_type, wrong_pos = tltype.general(t2), exp2.pos
    end
    msg = string.format(msg, tltype.tostring(wrong_type))
    typeerror(env, "arith", msg, wrong_pos)
  end
end

local function check_concat (env, exp)
  local exp1, exp2 = exp[2], exp[3]
  check_exp(env, exp1)
  check_exp(env, exp2)
  local t1, t2 = tltype.first(get_type(exp1)), tltype.first(get_type(exp2))
  local msg = "attempt to concatenate a '%s'"
  if tltype.subtype(t1, String) and tltype.subtype(t2, String) then
    set_type(exp, String)
  elseif tltype.isAny(t1) then
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "any", msg, exp1.pos)
  elseif tltype.isAny(t2) then
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t2))
    typeerror(env, "any", msg, exp2.pos)
  else
    set_type(exp, Any)
    local wrong_type, wrong_pos = tltype.general(t1), exp1.pos
    if tltype.subtype(t1, String) or tltype.isAny(t1) then
      wrong_type, wrong_pos = tltype.general(t2), exp2.pos
    end
    msg = string.format(msg, tltype.tostring(wrong_type))
    typeerror(env, "concat", msg, wrong_pos)
  end
end

local function check_equal (env, exp)
  local exp1, exp2 = exp[2], exp[3]
  check_exp(env, exp1)
  check_exp(env, exp2)
  set_type(exp, Boolean)
end

local function check_order (env, exp)
  local exp1, exp2 = exp[2], exp[3]
  check_exp(env, exp1)
  check_exp(env, exp2)
  local t1, t2 = tltype.first(get_type(exp1)), tltype.first(get_type(exp2))
  local msg = "attempt to compare '%s' with '%s'"
  if tltype.subtype(t1, Number) and tltype.subtype(t2, Number) then
    set_type(exp, Boolean)
  elseif tltype.subtype(t1, String) and tltype.subtype(t2, String) then
    set_type(exp, Boolean)
  elseif tltype.isAny(t1) then
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "any", msg, exp1.pos)
  elseif tltype.isAny(t2) then
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "any", msg, exp2.pos)
  else
    set_type(exp, Any)
    t1, t2 = tltype.general(t1), tltype.general(t2)
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "order", msg, exp.pos)
  end
end

local function check_and (env, exp)
  local exp1, exp2 = exp[2], exp[3]
  check_exp(env, exp1)
  check_exp(env, exp2)
  local t1, t2 = tltype.first(get_type(exp1)), tltype.first(get_type(exp2))
  if tltype.isNil(t1) or tltype.isFalse(t1) then
    set_type(exp, t1)
  elseif tltype.isUnion(t1, Nil) then
    set_type(exp, tltype.Union(t2, Nil))
  elseif tltype.isUnion(t1, False) then
    set_type(exp, tltype.Union(t2, False))
  elseif tltype.isBoolean(t1) then
    set_type(exp, tltype.Union(t2, False))
  else
    set_type(exp, tltype.Union(t1, t2))
  end
end

local function check_or (env, exp)
  local exp1, exp2 = exp[2], exp[3]
  check_exp(env, exp1)
  check_exp(env, exp2)
  local t1, t2 = tltype.first(get_type(exp1)), tltype.first(get_type(exp2))
  if tltype.isNil(t1) or tltype.isFalse(t1) then
    set_type(exp, t2)
  elseif tltype.isUnion(t1, Nil) then
    set_type(exp, tltype.Union(tltype.filterUnion(t1, Nil), t2))
  elseif tltype.isUnion(t1, False) then
    set_type(exp, tltype.Union(tltype.filterUnion(t1, False), t2))
  else
    set_type(exp, tltype.Union(t1, t2))
  end
end

local function check_binary_op (env, exp)
  local op = exp[1]
  if op == "add" or op == "sub" or
     op == "mul" or op == "idiv" or op == "div" or op == "mod" or
     op == "pow" then
    check_arith(env, exp, op)
  elseif op == "concat" then
    check_concat(env, exp)
  elseif op == "eq" then
    check_equal(env, exp)
  elseif op == "lt" or op == "le" then
    check_order(env, exp)
  elseif op == "and" then
    check_and(env, exp)
  elseif op == "or" then
    check_or(env, exp)
  elseif op == "band" or op == "bor" or op == "bxor" or
         op == "shl" or op == "shr" then
    check_bitwise(env, exp)
  else
    error("cannot type check binary operator " .. op)
  end
end

local function check_not (env, exp)
  local exp1 = exp[2]
  check_exp(env, exp1)
  set_type(exp, Boolean)
end

local function check_bnot (env, exp)
  local exp1 = exp[2]
  check_exp(env, exp1)
  local t1 = tltype.first(get_type(exp1))
  local msg = "attempt to perform bitwise on a '%s'"
  if tltype.subtype(t1, tltype.Integer(true)) then
    set_type(exp, Integer)
  elseif tltype.isAny(t1) then
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "any", msg, exp1.pos)
  else
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "bitwise", msg, exp1.pos)
  end
end

local function check_minus (env, exp)
  local exp1 = exp[2]
  check_exp(env, exp1)
  local t1 = tltype.first(get_type(exp1))
  local msg = "attempt to perform arithmetic on a '%s'"
  if tltype.subtype(t1, Integer) then
    set_type(exp, Integer)
  elseif tltype.subtype(t1, Number) then
    set_type(exp, Number)
  elseif tltype.isAny(t1) then
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "any", msg, exp1.pos)
  else
    set_type(exp, Any)
    t1 = tltype.general(t1)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "arith", msg, exp1.pos)
  end
end

local function check_len (env, exp)
  local exp1 = exp[2]
  check_exp(env, exp1)
  local t1 = tltype.first(get_type(exp1))
  local msg = "attempt to get length of a '%s'"
  if tltype.subtype(t1, String) or
     tltype.subtype(t1, tltype.Table()) then
    set_type(exp, Integer)
  elseif tltype.isAny(t1) then
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "any", msg, exp1.pos)
  else
    set_type(exp, Any)
    t1 = tltype.general(t1)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "len", msg, exp1.pos)
  end
end

local function check_unary_op (env, exp)
  local op = exp[1]
  if op == "not" then
    check_not(env, exp)
  elseif op == "bnot" then
    check_bnot(env, exp)
  elseif op == "unm" then
    check_minus(env, exp)
  elseif op == "len" then
    check_len(env, exp)
  else
    error("cannot type check unary operator " .. op)
  end
end

local function check_op (env, exp)
  if exp[3] then
    check_binary_op(env, exp)
  else
    check_unary_op(env, exp)
  end
end

local function check_paren (env, exp)
  local exp1 = exp[1]
  check_exp(env, exp1)
  local t1 = get_type(exp1)
  set_type(exp, tltype.first(t1))
end

local function check_explist (env, explist)
  for k, v in ipairs(explist) do
    check_exp(env, v)
  end
end

local function check_return_type (env, inf_type, dec_type, pos)
  local msg = "return type '%s' does not match '%s'"
  if tltype.isUnionlist(dec_type) then
    dec_type = tltype.unionlist2tuple(dec_type)
  end
  local dec_type = tltype.unfold(dec_type)
  if tltype.subtype(inf_type, dec_type) then
  elseif tltype.consistent_subtype(inf_type, dec_type) then
    msg = string.format(msg, tltype.tostring(inf_type), tltype.tostring(dec_type))
    typeerror(env, "any", msg, pos)
  else
    msg = string.format(msg, tltype.tostring(inf_type), tltype.tostring(dec_type))
    typeerror(env, "ret", msg, pos)
  end
end

local function check_function (env, exp)
  local idlist, ret_type, block = exp[1], replace_names(env, exp[2], exp.pos), exp[3]
  local infer_return = false
  if not block then
    block = ret_type
    ret_type = tltype.Tuple({ Nil }, true)
    infer_return = true
  end
  tlst.begin_function(env)
  tlst.begin_scope(env)
  local input_type = check_parameters(env, idlist, false, exp.pos)
  local t = tltype.Function(input_type, ret_type)
  local len = #idlist
  if len > 0 and idlist[len].tag == "Dots" then len = len - 1 end
  for k = 1, len do
    local v = idlist[k]
    v[2] = replace_names(env, v[2], exp.pos)
    set_type(v, v[2])
    check_masking(env, v[1], v.pos)
    tlst.set_local(env, v)
  end
  local r = check_block(env, block)
  if not r then tlst.set_return_type(env, tltype.Tuple({ Nil }, true)) end
  check_unused_locals(env)
  tlst.end_scope(env)
  local inferred_type = infer_return_type(env)
  if infer_return then
    ret_type = inferred_type
    t = tltype.Function(input_type, ret_type)
    set_type(exp, t)
  end
  check_return_type(env, inferred_type, ret_type, exp.pos)
  tlst.end_function(env)
  set_type(exp, t)
end


local function check_table (env, exp)
  local l = {}
  local i = 1
  local len = #exp
  for k, v in ipairs(exp) do
    local tag = v.tag
    local t1, t2
    if tag == "Pair" then
      local exp1, exp2 = v[1], v[2]
      check_exp(env, exp1)
      check_exp(env, exp2)
      t1, t2 = get_type(exp1), tltype.general(get_type(exp2))
      if tltype.subtype(Nil, t1) then
        t1 = Any
        local msg = "table index can be nil"
        typeerror(env, "table", msg, exp1.pos)
      elseif not (tltype.subtype(t1, Boolean) or
                  tltype.subtype(t1, Number) or
                  tltype.subtype(t1, String)) then
        t1 = Any
        local msg = "table index is dynamic"
        typeerror(env, "any", msg, exp1.pos)
      end
    else
      local exp1 = v
      check_exp(env, exp1)
      t1, t2 = tltype.Literal(i), tltype.general(get_type(exp1))
      if k == len and tltype.isVararg(t2) then
        t1 = Integer
      end
      i = i + 1
    end
    if t2.open then t2.open = nil end
    t2 = tltype.first(t2)
    l[k] = tltype.Field(v.const, t1, t2)
  end
  local t = tltype.Table(table.unpack(l))
  t.unique = true
  set_type(exp, t)
end

local function var2name (var)
  local tag = var.tag
  if tag == "Id" then
    return string.format("local '%s'", var[1])
  elseif tag == "Index" then
    if var[1].tag == "Id" and var[1][1] == "_ENV" and var[2].tag == "String" then
      return string.format("global '%s'", var[2][1])
    else
      return string.format("field '%s'", var[2][1])
    end
  else
    return "value"
  end
end

local function explist2typegen (explist)
  local len = #explist
  return function (i)
    if i <= len then
      local t = get_type(explist[i])
      return tltype.first(t)
    else
      local t = Nil
      if len > 0 then t = get_type(explist[len]) end
      if tltype.isTuple(t) then
        if i <= #t then
          t = t[i]
        else
          t = t[#t]
          if not tltype.isVararg(t) then t = Nil end
        end
      else
        t = Nil
      end
      if tltype.isVararg(t) then
        return tltype.first(t)
      else
        return t
      end
    end
  end
end

local function arglist2type (explist, strict)
  local len = #explist
  if len == 0 then
    if strict then
      return tltype.Void()
    else
      return tltype.Tuple({ Nil }, true)
    end
  else
    local l = {}
    for i = 1, len do
      l[i] = tltype.first(get_type(explist[i]))
    end
    if strict then
      return tltype.Tuple(l)
    else
      if not tltype.isVararg(explist[len]) then
        l[len + 1] = Nil
      end
      return tltype.Tuple(l, true)
    end
  end
end

local function check_arguments (env, func_name, dec_type, infer_type, pos)
  local msg = "attempt to pass '%s' to %s of input type '%s'"
  if tltype.subtype(infer_type, dec_type) then
  elseif tltype.consistent_subtype(infer_type, dec_type) then
    msg = string.format(msg, tltype.tostring(infer_type), func_name, tltype.tostring(dec_type))
    typeerror(env, "any", msg, pos)
  else
    msg = string.format(msg, tltype.tostring(infer_type), func_name, tltype.tostring(dec_type))
    typeerror(env, "args", msg, pos)
  end
end


local function check_call (env, exp)
  local exp1 = exp[1]
  local explist = {}
  for i = 2, #exp do
    explist[i - 1] = exp[i]
  end
  check_exp(env, exp1)
  check_explist(env, explist)
  if exp1.tag == "Index" and
     exp1[1].tag == "Id" and exp1[1][1] == "_ENV" and
     exp1[2].tag == "String" and exp1[2][1] == "setmetatable" then
    if explist[1] and explist[2] then
      local t1, t2 = get_type(explist[1]), get_type(explist[2])
      local t3 = tltype.getField(tltype.Literal("__index"), t2)
      if not tltype.isNil(t3) then
        if tltype.isTable(t3) then t3.open = true end
        set_type(exp, t3)
      else
        local msg = "second argument of setmetatable must be { __index = e }"
        typeerror(env, "call", msg, exp.pos)
        set_type(exp, Any)
      end
    else
      local msg = "setmetatable must have two arguments"
      typeerror(env, "call", msg, exp.pos)
      set_type(exp, Any)
    end
  elseif exp1.tag == "Index" and
         exp1[1].tag == "Id" and exp1[1][1] == "_ENV" and
         exp1[2].tag == "String" and exp1[2][1] == "require" then
    if explist[1] then
      local t1 = get_type(explist[1])
      if tltype.isStr(t1) then
        set_type(exp, check_require(env, explist[1][1], exp.pos))
      else
        local msg = "the argument of require must be a literal string"
        typeerror(env, "call", msg, exp.pos)
        set_type(exp, Any)
      end
    else
      local msg = "require must have one argument"
      typeerror(env, "call", msg, exp.pos)
      set_type(exp, Any)
    end
  else
    local t = tltype.first(get_type(exp1))
    local inferred_type = arglist2type(explist, env.strict)
    local msg = "attempt to call %s of type '%s'"
    if tltype.isFunction(t) then
      check_arguments(env, var2name(exp1), t[1], inferred_type, exp.pos)
      set_type(exp, t[2])
    elseif tltype.isAny(t) then
      set_type(exp, Any)
      msg = string.format(msg, var2name(exp1), tltype.tostring(t))
      typeerror(env, "any", msg, exp.pos)
    else
      set_type(exp, Nil)
      msg = string.format(msg, var2name(exp1), tltype.tostring(t))
      typeerror(env, "call", msg, exp.pos)
    end
  end
  return false
end

local function check_invoke (env, exp)
  local exp1, exp2 = exp[1], exp[2]
  local explist = {}
  for i = 3, #exp do
    explist[i - 2] = exp[i]
  end
  check_exp(env, exp1)
  check_exp(env, exp2)
  check_explist(env, explist)
  
  local t1, t2 = get_type(exp1), get_type(exp2)
  
  --replace first argument with Self for real method applications
  --TODO: maybe we need to unfold exp1.type for pseudo-method invocations
  if tltype.isTable(t1) then
    assert(tltype.isLiteral(t2) and type(t2[1]) == "string")
    local tfield = tltype.getField(t2,t1)
    if tfield and tltype.isFunction(tfield) and tltype.isSelf(tfield[1][1]) then
      table.insert(explist, 1, { type = Self })
    else
      table.insert(explist, 1, { type = exp1.type})
    end
  else
    table.insert(explist, 1, { type = exp1.type})
  end
  
  if tltype.isTable(t1) or
     tltype.isString(t1) or
     tltype.isStr(t1) then
    
    local inferred_type =  arglist2type(explist, env.strict)
    local t3
    if tltype.isTable(t1) then
      t3 = tltype.getField(t2, t1)
      --local s = env.self or Nil
      --if not tltype.subtype(s, t1) then env.self = t1 end
    else
      local string_userdata = env["loaded"]["string"] or tltype.Table()
      t3 = tltype.getField(t2, string_userdata)
      inferred_type[1] = String
    end
    local msg = "attempt to call method '%s' of type '%s'"
    if tltype.isFunction(t3) then
      check_arguments(env, "field", t3[1], inferred_type, exp.pos)
      set_type(exp, t3[2])
    elseif tltype.isAny(t3) then
      set_type(exp, Any)
      msg = string.format(msg, exp2[1], tltype.tostring(t3))
      typeerror(env, "any", msg, exp.pos)
    else
      set_type(exp, Nil)
      msg = string.format(msg, exp2[1], tltype.tostring(t3))
      typeerror(env, "invoke", msg, exp.pos)
    end
  elseif tltype.isAny(t1) then
    set_type(exp, Any)
    local msg = "attempt to index '%s' with '%s'"
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "any", msg, exp.pos)
  else
    set_type(exp, Nil)
    local msg = "attempt to index '%s' with '%s'"
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "index", msg, exp.pos)
  end
  return false
end

local function check_local_var (env, id, inferred_type, close_local)
  local local_name, local_type, pos = id[1], id[2], id.pos
  if tltype.isMethod(inferred_type) then
    local msg = "attempt to create a method reference"
    typeerror(env, "local", msg, pos)
    inferred_type = Nil
  end
  if not local_type then
    if tltype.isNil(inferred_type) then
      local_type = Any
    else
      local_type = tltype.general(inferred_type)
      if not local_type.name then local_type.name = local_name end
      if inferred_type.unique then
        local_type.unique = nil
        local_type.open = true
      end
      if close_local then local_type.open = nil end
    end
  else
    check_self(env, local_type, local_type, pos)
    local_type = replace_names(env, local_type, pos)
    local msg = "attempt to assign '%s' to '%s'"
    local local_type = tltype.unfold(local_type)
    msg = string.format(msg, tltype.tostring(inferred_type), tltype.tostring(local_type))
    if tltype.subtype(inferred_type, local_type) then
    elseif tltype.consistent_subtype(inferred_type, local_type) then
      typeerror(env, "any", msg, pos)
    else
      typeerror(env, "local", msg, pos)
    end
  end
  set_type(id, local_type)
  check_masking(env, id[1], id.pos)
  tlst.set_local(env, id)
end

local function unannotated_idlist (idlist)
  for k, v in ipairs(idlist) do
    if v[2] then return false end
  end
  return true
end

local function sized_unionlist (t)
  for i = 1, #t - 1 do
    if #t[i] ~= #t[i + 1] then return false end
  end
  return true
end

local function check_local (env, idlist, explist)
  check_explist(env, explist)
  if unannotated_idlist(idlist) and
     #explist == 1 and
     tltype.isUnionlist(get_type(explist[1])) and
     sized_unionlist(get_type(explist[1])) and
     #idlist == #get_type(explist[1])[1] - 1 then
    local t = get_type(explist[1])
    for k, v in ipairs(idlist) do
      set_type(v, t)
      v.i = k
      check_masking(env, v[1], v.pos)
      tlst.set_local(env, v)
    end
  else
    local tuple = explist2typegen(explist)
    for k, v in ipairs(idlist) do
      local t = tuple(k)
      local close_local = explist[k] and explist[k].tag == "Id" and tltype.isTable(t)
      check_local_var(env, v, t, close_local)
    end
  end
  return false
end

local function check_localrec (env, id, exp)
  local idlist, ret_type, block = exp[1], replace_names(env, exp[2], exp.pos), exp[3]
  local infer_return = false
  if not block then
    block = ret_type
    ret_type = tltype.Tuple({ Nil }, true)
    infer_return = true
  end
  tlst.begin_function(env)
  local input_type = check_parameters(env, idlist, false, exp.pos)
  local t = tltype.Function(input_type, ret_type)
  id[2] = t
  set_type(id, t)
  check_masking(env, id[1], id.pos)
  tlst.set_local(env, id)
  tlst.begin_scope(env)
  local len = #idlist
  if len > 0 and idlist[len].tag == "Dots" then len = len - 1 end
  for k = 1, len do
    local v = idlist[k]
    v[2] = replace_names(env, v[2], exp.pos)
    set_type(v, v[2])
    check_masking(env, v[1], v.pos)
    tlst.set_local(env, v)
  end
  local r = check_block(env, block)
  if not r then tlst.set_return_type(env, tltype.Tuple({ Nil }, true)) end
  check_unused_locals(env)
  tlst.end_scope(env)
  local inferred_type = infer_return_type(env)
  if infer_return then
    ret_type = inferred_type
    t = tltype.Function(input_type, ret_type)
    id[2] = t
    set_type(id, t)
    tlst.set_local(env, id)
    set_type(exp, t)
  end
  check_return_type(env, inferred_type, ret_type, exp.pos)
  tlst.end_function(env)
  return false
end

local function explist2typelist (explist)
  local len = #explist
  if len == 0 then
    return tltype.Tuple({ Nil }, true)
  else
    local l = {}
    for i = 1, len - 1 do
      table.insert(l, tltype.first(get_type(explist[i])))
    end
    local last_type = get_type(explist[len])
    if tltype.isUnionlist(last_type) then
      last_type = tltype.unionlist2tuple(last_type)
    end
    if tltype.isTuple(last_type) then
      for k, v in ipairs(last_type) do
        table.insert(l, tltype.first(v))
      end
    else
      table.insert(l, last_type)
    end
    if not tltype.isVararg(last_type) then
      table.insert(l, tltype.Vararg(Nil))
    end
    return tltype.Tuple(l)
  end
end

local function check_return (env, stm)
  if tlst.get_in_constructor(env) then
    local msg = "constructors should not return values."  
    typeerror(env,"ret",msg,stm.pos)
  end
  
  check_explist(env, stm)
  local t = explist2typelist(stm)
  tlst.set_return_type(env, tltype.general(t))
  return true
end

local function check_assignment (env, varlist, explist)
  check_explist(env, explist)
  local l = {}
  for k, v in ipairs(varlist) do
    check_var(env, v, explist[k])
    table.insert(l, get_type(v))
  end
  table.insert(l, tltype.Vararg(Value))
  local var_type, exp_type = tltype.Tuple(l), explist2typelist(explist)
  local msg = "attempt to assign '%s' to '%s'"
  if tltype.subtype(exp_type, var_type) then
  elseif tltype.consistent_subtype(exp_type, var_type) then
    msg = string.format(msg, tltype.tostring(exp_type), tltype.tostring(var_type))
    typeerror(env, "any", msg, varlist[1].pos)
  else
    msg = string.format(msg, tltype.tostring(exp_type), tltype.tostring(var_type))
    typeerror(env, "set", msg, varlist[1].pos)
  end
  for k, v in ipairs(varlist) do
    local tag = v.tag
    if tag == "Id" then
      local name = v[1]
      local l = tlst.get_local(env, name)
      local exp = explist[k]
      if exp and exp.tag == "Op" and exp[1] == "or" and
         exp[2].tag == "Id" and exp[2][1] == name and not l.assigned then
        local t1, t2 = get_type(exp), get_type(l)
        if tltype.subtype(t1, t2) then
          l.bkp = t2
          set_type(l, t1)
        end
      end
      l.assigned = true
    elseif tag == "Index" then
      local t1, t2 = get_type(v[1]), get_type(v[2])
      if tltype.isTable(t1) then
        local field = tltype.getFieldTable(t2,t1)
        if field and field.missing then
          field.missing = nil
        end
      end
    end
  end
  return false
end

local function check_while (env, stm)
  local exp1, stm1 = stm[1], stm[2]
  check_exp(env, exp1)
  local r, _, didgoto = check_block(env, stm1)
  return r, _, didgoto
end

local function check_repeat (env, stm)
  local stm1, exp1 = stm[1], stm[2]
  local r, _, didgoto = check_block(env, stm1)
  check_exp(env, exp1)
  return r, _, didgoto
end

local function tag2type (t)
  if tltype.isLiteral(t) then
    local tag = t[1]
    if tag == "nil" then
      return Nil
    elseif tag == "boolean" then
      return Boolean
    elseif tag == "number" then
      return Number
    elseif tag == "string" then
      return String
    elseif tag == "integer" then
      return Integer
    else
      return t
    end
  else
    return t
  end
end

local function get_index (u, t, i)
  if tltype.isUnionlist(u) then
    for k, v in ipairs(u) do
      if tltype.subtype(v[i], t) and tltype.subtype(t, v[i]) then
        return k
      end
    end
  end
end

local function is_global_function_call (exp, fn_name)
   return exp.tag == "Call" and exp[1].tag == "Index" and
          exp[1][1].tag == "Id" and exp[1][1][1] == "_ENV" and
          exp[1][2].tag == "String" and exp[1][2][1] == fn_name
end

local function check_if (env, stm)
  local l = {}
  local rl = {}
  local isallret = true
  for i = 1, #stm, 2 do
    local exp, block = stm[i], stm[i + 1]
    if block then
      check_exp(env, exp)
      if exp.tag == "Id" then
        local name = exp[1]
        local var = tlst.get_local(env, name)
        if not tltype.isUnionlist(get_type(var)) then
          if not var.bkp then var.bkp = get_type(var) end
          var.filter = Nil
          set_type(var, tltype.filterUnion(get_type(var), Nil))
          l[name] = var
        else
          local idx = get_index(get_type(var), Nil, var.i)
          if idx then
            var.filter = table.remove(get_type(var), idx)
            l[name] = var
          end
        end
      elseif exp.tag == "Op" and exp[1] == "not" and exp[2].tag == "Id" then
        local name = exp[2][1]
        local var = tlst.get_local(env, name)
        if not tltype.isUnionlist(get_type(var)) then
          if not var.bkp then var.bkp = get_type(var) end
          if not var.filter then
            var.filter = tltype.filterUnion(get_type(var), Nil)
          else
            var.filter = tltype.filterUnion(var.filter, Nil)
          end
          set_type(var, Nil)
          l[name] = var
        else
          local idx = get_index(get_type(var), Nil, var.i)
          if idx then
            var.filter = table.remove(get_type(var), idx)
            local bkp = table.remove(get_type(var))
            table.insert(get_type(var), var.filter)
            var.filter = bkp
            l[name] = var
          end
        end
      elseif exp.tag == "Op" and exp[1] == "eq" and
             is_global_function_call(exp[2], "type") and
             exp[2][2].tag == "Id" then
        local name = exp[2][2][1]
        local var = tlst.get_local(env, name)
        local t = tag2type(get_type(exp[3]))
        if not tltype.isUnionlist(get_type(var)) then
          if not var.bkp then var.bkp = get_type(var) end
          if not var.filter then
            var.filter = tltype.filterUnion(get_type(var), t)
          else
            var.filter = tltype.filterUnion(var.filter, t)
          end
          set_type(var, t)
          l[name] = var
        else
          local idx = get_index(get_type(var), t, var.i)
          if idx then
            var.filter = table.remove(get_type(var), idx)
            local bkp = table.remove(get_type(var))
            table.insert(get_type(var), var.filter)
            var.filter = bkp
            l[name] = var
          end
        end
      elseif exp.tag == "Op" and exp[1] == "not" and
             exp[2].tag == "Op" and exp[2][1] == "eq" and
             is_global_function_call(exp[2][2], "type") and
             exp[2][2][2].tag == "Id" then
        local name = exp[2][2][2][1]
        local var = tlst.get_local(env, name)
        local t = tag2type(get_type(exp[2][3]))
        if not tltype.isUnionlist(get_type(var)) then
          if not var.bkp then var.bkp = get_type(var) end
          var.filter = t
          set_type(var, tltype.filterUnion(get_type(var), t))
          l[name] = var
        else
          local idx = get_index(get_type(var), t, var.i)
          if idx then
            var.filter = table.remove(get_type(var), idx)
            l[name] = var
          end
        end
      end
    else
      block = exp
    end
    local r, isret = check_block(env, block)
    table.insert(rl, r)
    isallret = isallret and isret
    for k, v in pairs(l) do
      if not tltype.isTuple(v.filter) then
        set_type(v, v.filter)
      else
        local t = get_type(v)
        local bkp = table.remove(t)
        table.insert(t, v.filter)
        v.filter = bkp
      end
    end
  end
  if not isallret then
    for k, v in pairs(l) do
      if not tltype.isUnionlist(get_type(v)) then
        set_type(v, v.bkp)
      else
        table.insert(get_type(v), v.filter)
      end
    end
  end
  if #stm % 2 == 0 then table.insert(rl, false) end
  local r = true
  for k, v in ipairs(rl) do
    r = r and v
  end
  return r
end

local function infer_int(t)
  return tltype.isInt(t) or tltype.isInteger(t)
end

local function check_fornum (env, stm)
  local id, exp1, exp2, exp3, block = stm[1], stm[2], stm[3], stm[4], stm[5]
  check_exp(env, exp1)
  local t1 = get_type(exp1)
  local msg = "'for' initial value must be a number"
  if tltype.subtype(t1, Number) then
  elseif tltype.consistent_subtype(t1, Number) then
    typeerror(env, "any", msg, exp1.pos)
  else
    typeerror(env, "fornum", msg, exp1.pos)
  end
  check_exp(env, exp2)
  local t2 = get_type(exp2)
  msg = "'for' limit must be a number"
  if tltype.subtype(t2, Number) then
  elseif tltype.consistent_subtype(t2, Number) then
    typeerror(env, "any", msg, exp2.pos)
  else
    typeerror(env, "fornum", msg, exp2.pos)
  end
  local int_step = true
  if block then
    check_exp(env, exp3)
    local t3 = get_type(exp3)
    msg = "'for' step must be a number"
    if not infer_int(t3) then
      int_step = false
    end
    if tltype.subtype(t3, Number) then
    elseif tltype.consistent_subtype(t3, Number) then
      typeerror(env, "any", msg, exp3.pos)
    else
      typeerror(env, "fornum", msg, exp3.pos)
    end
  else
    block = exp3
  end
  tlst.begin_scope(env)
  tlst.set_local(env, id)
  if infer_int(t1) and infer_int(t2) and int_step then
    set_type(id, Integer)
  else
    set_type(id, Number)
  end
  local r, _, didgoto = check_block(env, block)
  check_unused_locals(env)
  tlst.end_scope(env)
  return r, _, didgoto
end

local function check_forin (env, idlist, explist, block)
  tlst.begin_scope(env)
  check_explist(env, explist)
  local t = tltype.first(get_type(explist[1]))
  local tuple = explist2typegen({})
  local msg = "attempt to iterate over %s"
  if tltype.isFunction(t) then
    local l = {}
    for k, v in ipairs(t[2]) do
      l[k] = {}
      set_type(l[k], v)
    end
    tuple = explist2typegen(l)
  elseif tltype.isAny(t) then
    msg = string.format(msg, tltype.tostring(t))
    typeerror(env, "any", msg, idlist.pos)
  else
    msg = string.format(msg, tltype.tostring(t))
    typeerror(env, "forin", msg, idlist.pos)
  end
  for k, v in ipairs(idlist) do
    local t = tltype.filterUnion(tuple(k), Nil)
    check_local_var(env, v, t, false)
  end
  local r, _, didgoto = check_block(env, block)
  check_unused_locals(env)
  tlst.end_scope(env)
  return r, _, didgoto
end

local function check_index (env, exp)
  local exp1, exp2 = exp[1], exp[2]
  check_exp(env, exp1)
  check_exp(env, exp2)
  local t1, t2 = tltype.first(get_type(exp1)), tltype.first(get_type(exp2))
  local msg = "attempt to index '%s' with '%s'"
  if tltype.isTable(t1) then
    -- FIX: methods should not leave objects, this is unsafe!
    local field_type = tltype.getField(t2, t1)
    if not tltype.isNil(field_type) then
      local field = tltype.getFieldTable(t2,t1)
      if field.missing then
        msg = "attempt to access missing field %s"
        msg = string.format(msg, tltype.tostring(t2))
        typeerror(env, "index", msg, exp.pos)
        set_type(exp, Nil)      
      end
      set_type(exp, field_type)
    else
      if exp1.tag == "Id" and exp1[1] == "_ENV" and exp2.tag == "String" then
        msg = "attempt to access undeclared global '%s'"
        msg = string.format(msg, exp2[1])
      else
        msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
      end
      typeerror(env, "index", msg, exp.pos)
      set_type(exp, Nil)
    end
  elseif tltype.isAny(t1) then
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "any", msg, exp.pos)
  else
    set_type(exp, Nil)
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "index", msg, exp.pos)
  end
end


-- returns constructors,methods,fields
-- where each returned value maps names to types
local function get_elem_types (env, elems)
    local constructors = {}
    local methods = {}
    local fields = {}
    
    local function check_redecl(name,pos)
        if fields[name] or methods[name] or constructors[name] then
          local msg = string.format("class element %s redeclared",name)
          typeerror(env, "self", msg, pos)
        end      
    end
    
    for _,elem in ipairs(elems) do
      if elem.tag == "ConcreteClassField" then
        local name = elem[1][1]
        check_redecl(name,elem.pos)
        fields[name] = elem[2]
      elseif elem.tag == "AbstractClassField" then
        local name,t = elem[1][1], elem[2]
        check_redecl(name,elem.pos)  
        --TODO: handle abstract vs. concrete fields
        fields[name] = t
      elseif elem.tag == "ConcreteClassMethod" then
        local name,parlist,tret = elem[1][1],elem[2],elem[3]
        check_redecl(name,elem.pos)         
        local t1 = check_parameters(env, parlist, false, elem.pos)
        local t2 = tret
        methods[name] = tltype.Function(t1, t2, true)
      elseif elem.tag == "AbstractClassMethod" then
        local name, t = elem[1][1], elem[2] 
        check_redecl(name,elem.pos)  
        methods[name] = t
      elseif elem.tag == "ClassConstructor" then
        local name,parlist = elem[1][1],elem[2]
        local t1 = check_parameters(env, parlist, false, elem.pos)
        constructors[name] = tltype.Function(t1, tltype.Void(), false)
      elseif elem.tag == "ClassFinalizer" then
        --nothing to do here
      else
        error("cannot type check class element " .. elem.tag)
      end
    end 
    
    return constructors,methods,fields
end

-- check_constructor_supercall : (env, parlist, id, explist, type) -> ()
local function check_constructor_supercall (env, supercons_name, superargs, tparent)
  local constructor = tltype.getField(tltype.Literal(supercons_name[1]), tparent)
  if not constructor then
    local msg = "superclass constructor %s called, but superclass %s does not have a constructor with that name."
    msg = string.format(msg, supercons_name[1], tltype.tostring(tparent))
    typeerror(env, "call", msg, supercons_name.pos)
  else
    check_explist(env, superargs)
    local t = tltype.first(constructor)
    local inferred_type = arglist2type(superargs, env.strict)
    check_arguments(env, supercons_name[1], t[1], inferred_type, supercons_name.pos)
  end
end

local function check_constructor_self (env, tself, pos)
  assert(tself.tag == "TTable" and tself.closed)
  local msg = "constructed self type '%s' missing field %s"
  for _,field in ipairs(tself) do
      if field.missing then
        local msg = string.format(msg, tltype.tostring(tself), tltype.tostring(field[1]))
        typeerror(env, "self", msg, pos)  
      end
  end
end

local function check_constructor (env, elem, instance_members, parent_members, parent)
  local name, idlist, supercons_name, superargs, body, pos = elem[1], elem[2], elem[3], elem[4], elem[5], elem.pos
  tlst.begin_function(env)
  tlst.set_in_constructor(env)
  tlst.begin_scope(env)  
  local input_type = check_parameters(env, idlist, true, idlist.pos)
  local output_type = tltype.Tuple({ Nil }, true)
  local t = tltype.Function(input_type,output_type)
  if superargs ~= "NoSuperCall" then
    if parent then 
      check_constructor_supercall(env,supercons_name,superargs,get_type(parent))
    else
      local msg = "called superclass constructor, but %s has no superclass"
      msg = string.format(msg, name[1])
      typeerror(env, "inheritance", msg,consname. pos)
    end
  end
  local tself = tltype.Table(table.unpack(instance_members))
  for _,field in ipairs(tself) do
    assert(tltype.isStr(field[1]))
    if superargs == "NoSuperCall" or not parent_members[field[1].name] then
      field.missing = true
    end
  end
  tself.closed = true    
        
  local len = #idlist
  if len > 0 and idlist[len].tag == "Dots" then len = len - 1 end
  for k = 1,len do
    local v = idlist[k]
    v[2] = replace_names(env, v[2], v.pos)
    set_type(v, v[2])
    check_masking(env, v[1], v.pos)
    tlst.set_local(env,v)
  end
  check_masking(env,"self",pos)
  tlst.set_local(env, { tag = "Id", pos = pos, [1] = "self", ["type"] = tself})
  local r = check_block(env,body)
  if not r then tlst.set_return_type(env, tltype.Tuple({ Nil }, true)) end
  check_unused_locals(env)
  check_constructor_self(env, tself, pos)
  tlst.end_scope(env)
  tlst.end_function(env)
end

local function check_method (env, idlist, tret, body, tself, pos)
  tlst.begin_function(env)
  tlst.begin_scope(env)  
  local input_type = check_parameters(env, idlist, true, idlist.pos)
  local output_type = replace_names(env,tret,tret.pos)
  local t = tltype.Function(input_type,output_type)
  local len = #idlist
  if len > 0 and idlist[len].tag == "Dots" then len = len - 1 end
  for k = 1,len do
    local v = idlist[k]
    v[2] = replace_names(env, v[2], v.pos)
    set_type(v, v[2])
    check_masking(env, v[1], v.pos)
    tlst.set_local(env,v)
  end
  check_masking(env,"self",pos)
  tlst.set_local(env, { tag = "Id", pos = pos, [1] = "self", ["type"] = tself})
  local r = check_block(env,body)
  if not r then tlst.set_return_type(env, tltype.Tuple({ Nil }, true)) end
  check_unused_locals(env)
  tlst.end_scope(env)
  local inferred_type = infer_return_type(env)
  check_return_type(env, inferred_type, tret, pos)
  tlst.end_function(env)
end

local function check_premethod_t(env,premethod,pos)
  local t1, t2 = premethod[1], premethod[2]
  if not tltype.isStr(t1) then
    local msg = "All fields of the __premethods table should have literal string keys. %s is not a literal string."
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "inheritance", msg, pos)
    return false
  elseif not premethod.const then
     local msg = "All fields of the __premethods table should be const, but %s is not."
     msg = string.format(msg, tltype.tostring(t1))
     typeerror(env, "inheritance", msg, pos)
     return false
  elseif not tltype.isFunction(t2) then
    local msg = "All fields of the __premethods table should be functions, but %s is a %s."
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "inheritance", msg, pos)
    return false
  elseif not tltype.isTuple(t2[1]) then
    local msg = "Premethod input type should be a tuple, but %s has input type %2."
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2[1]))
    typeerror(env, "inheritance", msg, pos)
    return false
  elseif not tltype.isTable(t2[1][1]) then
    local msg = "The first formal argument to a premethod should be a table, but %s has argument type %s."
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2[1][1]))
    typeerror(env, "inheritance", msg, pos)
    return false
  end
  return true 
end

local function premethod_from_method (method, tinstance)
  assert(method.const)
  
  local tkey = method[1]
  local tvalue = method[2]
  local tinput = tvalue[1]
  local toutput = tvalue[2]
  
  assert(tltype.isSelf(tinput[1]))
  
  local new_tinput = {}
  for k,v in pairs(tinput) do new_tinput[k] = v end
  new_tinput[1] = tinstance
  
  local new_function = tltype.Function(new_tinput,toutput)
  
  return tltype.Field(true, method[1], new_function)  
end


local function method_from_premethod (premethod)
  assert(premethod.const)
  
  local tkey = premethod[1]
  local tvalue = premethod[2]
  local tinput = tvalue[1]
  local toutput = tvalue[2]
  
  local new_tinput = {}
  for k,v in pairs(tinput) do new_tinput[k] = v end
  new_tinput[1] = Self
  
  local new_function = tltype.Function(new_tinput,toutput)
  
  return tltype.Field(true, premethod[1], new_function)
end

local function check_premethods_table(env,premethods,tinstance,constructor_name,tclass,pos)
  if not tltype.isTable(premethods) then
    local msg = "The __premethods field of a superclass type should be a table, but %s has a __premethods field of type %s"
    msg = string.format(msg, tltype.tostring(tclass), tltype.tostring(premethods))
    typeerror(env, "inheritance", msg, pos)
    return false            
  else
    --c
    for _,premethod in ipairs(premethods) do
      local well_formed = check_premethod_t(env,premethod,pos)
      if well_formed then
        -- the name of the current premethod
        local name = tltype.tostring(premethod[1])
        -- the first formal parameter type from the current premethod
        local premethod_tinstance = premethod[2][1][1]
        
        --check that premethod's first argument is consistent with tinstance
        if not tltype.consistent(tinstance,premethod_tinstance) then
          local msg = "premethod %s has a first argument type %s that is not consistent with the return type %s of constructor %s."
          local s1,s2 = name, tltype.tostring(premethod_tinstance)
          local s3,s4 = tltype.tostring(tinstance), constructor_name
          msg = string.format(msg,s1,s2,s3,s4)
          typeerror(env, "inheritance", msg, pos)
          return false        
        end
        
        --check that tinstance has a method corresponding to premethod
        assert(tltype.isTable(tinstance))
        --we expect the corresponding method of the instance type to be consistent with ttarget
        local ttarget = method_from_premethod(premethod)[2]
        local tmethod = tltype.getField(premethod[1],tinstance)
        if not tmethod then
          local msg = "return type of constructor %s (assumed to be the class instance type)"
          msg = msg .. "does not have a method corresponding to premethod %s."
          msg = string.format(msg,constructor_name,tltype.tostring(premethod[1]))
          typeerror(env, "inheritance", msg, pos)
          return false
        elseif not tltype.consistent(ttarget,tmethod) then
          local msg = "type %s of method %s not consistent with premethod type %s"
          msg = string.format(msg, tltype.tostring(tmethod), name, tltype.tostring(ttarget))
          typeerror(env, "inheritance", msg, pos)
          return false
        end
      end
    end
  end
  
  local members = {}
  local methods = {}
  local fields = {}
  for _,field in ipairs(tinstance) do
    local premethod = tltype.getFieldTable(field[1],premethods)
    local fieldname = tltype.tostring(field[1])
    if premethod then
      methods[fieldname] = premethod
    else
      members[fieldname] = field
    end
    fields[fieldname] = field
  end
  
  return true, members, methods, fields
end


--checks that t is a valid class type
local function class_check_tclass(env,t,pos)
  --this will be replaced with an instance type if one is found
  local tinstance = nil
  local tinstance_src_key = nil
  
  if not tltype.isTable(t) then
    local msg = "attempt to inherit from non-table %s"
    msg = string.format(msg, tltype.toString(t))
    typeerror(env, "inheritance", msg, pos)
    return false
  elseif not t.fixed then
    local msg = "attempt to inherit from non-fixed table %s"
    msg = string.format(msg, tltype.tostring(t))
    typeerror(env, "inheritance", msg,  pos)
    return false
  elseif not tltype.getField(tltype.Literal("__premethods"),t) then
    local msg = "attempt to inherit from table %s which has no __premethods field"
    msg = string.format(msg, tltype.toString(t))
    typeerror(env, "inheritance", msg, pos)
    return false
  elseif not (#t > 1) then
    local msg = "attempt to inherit from table %s with no constructor"
    msg = string.format(msg, tltype.tostring(tparent))
    typeerror(env, "inheritance", msg, pos)
    return false
  else
    for _,field in ipairs(t) do
      local tkey,tval = field[1], field[2]
      if tkey.tag ~= "TLiteral" then
        local msg = "Parent %s has key type %s, but inheritance is only allowed from tables with only literal string keys."
        msg = string.format(msg, tltype.tostring(t), tltype.tostring(tkey))
        typeerror(env, "inheritance", msg, pos)
        return false
      elseif type(tkey[1]) ~= "string" then
        local msg = "Parent %s has key type %s, but inheritance is only allowed from tables with only literal string keys."
        msg = string.format(msg, tltype.tostring(t), tltype.tostring(tkey))
        typeerror(env, "inheritance", msg, pos)
        return false
      elseif not field.const then
        local msg = "Field %s of %s is non-const, but superclass types may only contain non-const fields."
        msg = string.format(msg, tltype.tostring(tkey), tltype.tostring(tparent))
        typeerror(env, "inheritance", msg, pos)
        return false
      elseif tkey.name == "__premethods" then
        --we are processing constructors now. we will with premethods afterward.
      elseif not tltype.isFunction(tval) then
        local msg = "All fields of a class type except __premethods should be functions, but %s has type %s"
        msg = string.format(msg, tltype.tostring(tkey), tltype.tostring(tval))
        typeerror(env, "inheritance", msg, pos)
        return false      
      else 
        local tret = tltype.unfold(tval[2])
        if not tltype.isTable(tret) or tltype.isAny(tret) then
          local msg = "Constructors should return tables, but %s returns a %s" -- these actually might be recursive types
          msg = string.format(msg, tltype.tostring(tkey), tltype.tostring(tval[2][1]))
          typeerror(env, "inheritance", msg, pos)
          return false          
        else
          --this is a constructor. We need to take the result type as the instance type
          if tinstance == nil then
            --make sure it has one return value which is a table type.
            tinstance = tret
            tinstance_src_key = tkey 
          else
            if not tltype.consistent(tinstance,tret) then
              local msg = "Return type %s of constructor %s not consistent with return type %s of constructor %s"
              local inst_str, inst_key = tltype.tostring(tinstance), tltype.tostring(tinstance_src_key)
              local ret_str, ret_key = tltype.tostring(tret), tltype.tostring(tkey)
              msg = string.format(msg, inst_str, inst_key, ret_str, ret_key)
              typeerror(env, "inheritance", msg, pos)
              return false                      
            end
          end
        end
      end
    end
    
    assert(tinstance ~= nil)
    local premethods_table = tltype.getField(tltype.Literal("__premethods"), t)
    local succ, mems, methods, fields = check_premethods_table(env,premethods_table, tinstance, tltype.tostring(tinstance_src_key), t, pos)
    return succ, mems, methods, fields
  end
  assert(false)
end


local function check_class (env, stm)
  local name, isAbstract, elems, parent, is_local = stm[1], stm[2], stm[3], stm[4], stm.is_local
  if tlst.get_interface(env, name) then
    local msg = "attempt to redeclare type '%s'"
    msg = string.format(msg, name)
    typeerror(env, "alias", msg, stm.pos)
  else
    local constructors, methods, members = get_elem_types(env, elems)
    
    local parent_methods = {}
    local parent_fields = {}
    local parent_members = {}
    --handle inheritance
    if parent ~= "NoParent" then
      assert(parent.tag == "Id")
      check_id(env, parent)
      local tparent = get_type(parent)
      local success,members,methods,fields = class_check_tclass(env, tparent, parent.pos)
      if success then
        parent_methods = methods
        parent_fields = fields
        parent_members = members
      else
        return false
      end
    end
    
    --all instance fields, both members and methods
    local instance_fields = {}
    --instance fields only
    local instance_members = {}
    --instance methods only
    local instance_methods = {}
    
    for k,v in pairs(methods) do
      local parent_premethod = parent_methods[k]
      if parent_premethod then
        local parent_method = method_from_premethod(parent_premethod)
        if not tltype.consistent_subtype(v,parent_method[2]) then
          local msg = "method %s overridden with type %s, which is not a consistent-subtype of %s"
          msg = string.format(msg, k, tltype.tostring(v), tltype.tostring(parent_method[2]))
          typeerror(env, "inheritance", msg, stm.pos)
          return false
        end
      end
      
      local newelem = tltype.Field(true, tltype.Literal(k), v) 
      instance_fields[#instance_fields+1] = newelem
      instance_methods[#instance_methods+1] = newelem    
    end
    
    for k,v in pairs(parent_methods) do
      if not methods[k] then --don't add overridden methods
        instance_fields[#instance_fields+1] = method_from_premethod(v)
        instance_methods[#instance_methods+1] = method_from_premethod(v)
      end
    end
    
    for k,v in pairs(members) do 
      if parent_members[k] then
        local msg = "member %s declared twice: once in class %s and once in class %s"
        msg = string.format(msg, k, parent[1], name[1])
        typeerror(env, "inheritance", msg, v.pos)
        return false
      end
      
      local newelem = tltype.Field(false, tltype.Literal(k), v) 
      instance_fields[#instance_fields+1] = newelem
      instance_members[#instance_members+1] = newelem
    end
    
     for k,v in pairs(parent_members) do
      instance_fields[#instance_fields+1] = v
      instance_members[#instance_members+1] = v
    end   
    
    local t_instance = tltype.Table(table.unpack(instance_fields))
    t_instance.fixed = true
    t_instance.name = name
    
    for _,elem in ipairs(elems) do
      if elem.tag == "ConcreteClassMethod" then
        local name,parlist,tret,body = elem[1], elem[2], elem[3], elem[4]
        check_method(env,parlist,tret,body,t_instance,elem.pos)
      elseif elem.tag == "ClassConstructor" then
        check_constructor(env, elem, instance_members, parent_members, parent)
      elseif elem.tag == "ClassFinalizer" then
      
      end
    end
    
    local class_constructors = {}
    for k,v in pairs(constructors) do
      --overwrite constructor return value with instance type
      v[2] = t_instance
      class_constructors[#class_constructors + 1] = tltype.Field(true, tltype.Literal(k), v)
    end
  
    local t_methods = tltype.Table(table.unpack(instance_methods))
    for i,field in ipairs(t_methods) do t_methods[i] = premethod_from_method(field,t_instance) end
    local t_class = tltype.Table(table.unpack(class_constructors))
    t_class[#t_class + 1] = tltype.Field(true, tltype.Literal("__premethods"), t_methods)
    t_class.fixed = true
    
    tlst.set_interface(env, name, t_class, is_local)
    
    if is_local then
      set_type(name, t_class)
      check_masking(env, name[1], name.pos)
      tlst.set_local(env, name)
    else
    end
    
  end
end

function check_id (env, exp)
  local name = exp[1]
  local l = tlst.get_local(env, name)
  local t = get_type(l)
  if tltype.isUnionlist(t) and l.i then
    set_type(exp, tltype.unionlist2union(t, l.i))
  else
    set_type(exp, t)
  end
end

function check_var (env, var, exp)
  local tag = var.tag
  if tag == "Id" then
    local name = var[1]
    local l = tlst.get_local(env, name)
    local t = get_type(l)
    if exp and exp.tag == "Id" and tltype.isTable(t) then t.open = nil end
    set_type(var, t)
  elseif tag == "Index" then
    local exp1, exp2 = var[1], var[2]
    check_exp(env, exp1)
    check_exp(env, exp2)
    local t1, t2 = tltype.first(get_type(exp1)), tltype.first(get_type(exp2))
    local msg = "attempt to index '%s' with '%s'"
    if tltype.isTable(t1) then
      if exp1.tag == "Id" and exp1[1] ~= "_ENV" then env.self = t1 end
      local field_type = tltype.getField(t2, t1)
      if not tltype.isNil(field_type) then
        set_type(var, field_type)
      else
        if t1.open or t1.unique then
          if exp then
            local t3 = tltype.general(get_type(exp))
            local t = tltype.general(t1)
            table.insert(t, tltype.Field(var.const, t2, t3))
            if tltype.subtype(t, t1) then
              table.insert(t1, tltype.Field(var.const, t2, t3))
            else
              msg = "could not include field '%s'"
              msg = string.format(msg, tltype.tostring(t2))
              typeerror(env, "open", msg, var.pos)
            end
            if t3.open then t3.open = nil end
            set_type(var, t3)
          else
            set_type(var, Nil)
          end
        else
          if exp1.tag == "Id" and exp1[1] == "_ENV" and exp2.tag == "String" then
            msg = "attempt to access undeclared global '%s'"
            msg = string.format(msg, exp2[1])
          else
            msg = "attempt to use '%s' to index closed table"
            msg = string.format(msg, tltype.tostring(t2))
          end
          typeerror(env, "open", msg, var.pos)
          set_type(var, Nil)
        end
      end
    elseif tltype.isAny(t1) then
      set_type(var, Any)
      msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
      typeerror(env, "any", msg, var.pos)
    else
      set_type(var, Nil)
      msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
      typeerror(env, "index", msg, var.pos)
    end
  else
    error("cannot type check variable " .. tag)
  end
end

function check_exp (env, exp)
  local tag = exp.tag
  if tag == "Nil" then
    set_type(exp, Nil)
  elseif tag == "Dots" then
    set_type(exp, tltype.Vararg(tlst.get_vararg(env)))
  elseif tag == "True" then
    set_type(exp, True)
  elseif tag == "False" then
    set_type(exp, False)
  elseif tag == "Number" then
    set_type(exp, tltype.Literal(exp[1]))
  elseif tag == "String" then
    set_type(exp, tltype.Literal(exp[1]))
  elseif tag == "Function" then
    check_function(env, exp)
  elseif tag == "Table" then
    check_table(env, exp)
  elseif tag == "Op" then
    check_op(env, exp)
  elseif tag == "Paren" then
    check_paren(env, exp)
  elseif tag == "Call" then
    check_call(env, exp)
  elseif tag == "Invoke" then
    check_invoke(env, exp)
  elseif tag == "Id" then
    check_id(env, exp)
  elseif tag == "Index" then
    check_index(env, exp)
  else
    error("cannot type check expression " .. tag)
  end
end

function check_stm (env, stm)
  local tag = stm.tag
  if tag == "Do" then
    return check_block(env, stm)
  elseif tag == "Set" then
    return check_assignment(env, stm[1], stm[2])
  elseif tag == "While" then
    return check_while(env, stm)
  elseif tag == "Repeat" then
    return check_repeat(env, stm)
  elseif tag == "If" then
    return check_if(env, stm)
  elseif tag == "Fornum" then
    return check_fornum(env, stm)
  elseif tag == "Forin" then
    return check_forin(env, stm[1], stm[2], stm[3])
  elseif tag == "Local" then
    return check_local(env, stm[1], stm[2])
  elseif tag == "Localrec" then
    return check_localrec(env, stm[1][1], stm[2][1])
  elseif tag == "Goto" then
    return false, nil, true
  elseif tag == "Label" then
    return false
  elseif tag == "Return" then
    return check_return(env, stm)
  elseif tag == "Break" then
    return false
  elseif tag == "Call" then
    return check_call(env, stm)
  elseif tag == "Invoke" then
    return check_invoke(env, stm)
  elseif tag == "Interface" then
    return check_interface(env, stm)
  elseif tag == "Class" then
    return check_class(env,stm)
  else
    error("cannot type check statement " .. tag)
  end
end

local function is_exit_point (block)
  if #block == 0 then return false end
  local last = block[#block]
  return last.tag == "Return" or is_global_function_call(last, "error")
end

function check_block (env, block)
  tlst.begin_scope(env)
  local r = false
  local endswithret = true
  local didgoto, _ = false, nil
  for k, v in ipairs(block) do
    r, _, didgoto = check_stm(env, v)
    if didgoto then endswithret = false end
  end
  endswithret = endswithret and is_exit_point(block)
  check_unused_locals(env)
  tlst.end_scope(env)
  return r, endswithret, didgoto
end

local function load_lua_env (env)
  local path = "typedlua/"
  local l = {}
  if _VERSION == "Lua 5.1" then
    path = path .. "lsl51/"
    l = { "coroutine", "package", "string", "table", "math", "io", "os", "debug" }
  elseif _VERSION == "Lua 5.2" then
    path = path .. "lsl52/"
    l = { "coroutine", "package", "string", "table", "math", "bit32", "io", "os", "debug" }
  elseif _VERSION == "Lua 5.3" then
    path = path .. "lsl53/"
    l = { "coroutine", "package", "string", "utf8", "table", "math", "io", "os", "debug" }
  else
    error("Typed Lua does not support " .. _VERSION)
  end
  local t = check_require(env, "base", 0, path)
  for k, v in ipairs(l) do
    local t1 = tltype.Literal(v)
    local t2 = check_require(env, v, 0, path)
    local f = tltype.Field(false, t1, t2)
    table.insert(t, f)
  end
  t.open = true
  local lua_env = tlast.ident(0, "_ENV", t)
  set_type(lua_env, t)
  tlst.set_local(env, lua_env)
  tlst.get_local(env, "_ENV")
end

function tlchecker.typecheck (ast, subject, filename, strict, integer)
  assert(type(ast) == "table")
  assert(type(subject) == "string")
  assert(type(filename) == "string")
  assert(type(strict) == "boolean")
  local env = tlst.new_env(subject, filename, strict)
  if integer and _VERSION == "Lua 5.3" then
    Integer = tltype.Integer(true)
    env.integer = true
    tltype.integer = true
  end
  tlst.begin_function(env)
  tlst.begin_scope(env)
  tlst.set_vararg(env, String)
  load_lua_env(env)
  for k, v in ipairs(ast) do
    check_stm(env, v)
  end
  check_unused_locals(env)
  tlst.end_scope(env)
  tlst.end_function(env)
  return env.messages
end

function tlchecker.error_msgs (messages, warnings)
  assert(type(messages) == "table")
  assert(type(warnings) == "boolean")
  local l = {}
  local msg = "%s:%d:%d: %s, %s"
  local skip_error = { any = true,
    mask = true,
    unused = true,
  }
  for k, v in ipairs(messages) do
    local tag = v.tag
    if skip_error[tag] then
      if warnings then
        table.insert(l, string.format(msg, v.filename, v.l, v.c, "warning", v.msg))
      end
    else
      table.insert(l, string.format(msg, v.filename, v.l, v.c, "type error", v.msg))
    end
  end
  local n = #l
  if n == 0 then
    return nil, n
  else
    return table.concat(l, "\n"), n
  end
end

return tlchecker
