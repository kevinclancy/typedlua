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

local check_block, check_stm, check_exp, check_var, check_id, check_typedefs

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

local function set_type (env, node, t)
  node["type"] = tltype.simplifyUnion(env,t)
end

local function get_type (node)
  return node and node["type"] or Nil
end

local check_self_field

local directory_separator = string.sub(package.config,1,1)

-- filename_to_modulename : (string) -> (string)
local function filename_to_modulename (name)
  local s = string.gsub(name,directory_separator,'.')
  s = string.match(s, "[^%p].*")
  return string.sub(s,1,-3)
end

-- current_module : () -> (string)
local function current_modname (env)
  return filename_to_modulename(env.filename)
end

local function expand_typealias(env, t)
  assert(t.tag == "TSymbol")
  local name = t[1]
  local s = tlst.get_typealias(env, name)
  if s then
    t[1] = s
  end
end

-- insert a group of type variables into the environment
-- set_tpars : (env, {tpar}) -> ()
local function set_tpars(env, tpars)
  for _,tpar in ipairs(tpars) do
    local name, variance, tbound = tpar[1], tpar[2], tpar[3]
    tbound = (tbound == "NoBound") and Value or tbound
    local ti = tlst.typeinfo_Variable(tbound, variance)
    tlst.set_typeinfo(env, name, ti, true)
    tlst.set_typealias(env, name, name)
  end  
end

--kindchecks for proper arity, and also that all symbols are defined
--does *not* check subtyping restrictions on type operator arguments
local function kindcheck_arity (env, t)
  if type(t) == "boolean" then
    assert(false)
  end
  if t.tag == "TLiteral" then
    return true
  elseif t.tag == "TBase" then
    return true
  elseif t.tag == "TNil" then
    return true
  elseif t.tag == "TValue" then
    return true
  elseif t.tag == "TAny" then
    return true
  elseif t.tag == "TSelf" then
    return true
  elseif t.tag == "TVoid" then
    return true
  elseif t.tag == "TUnion" then
    for i,elem in ipairs(t) do
      if not kindcheck_arity(env, elem) then
        t[i] = Any
      end
    end
    return true
  elseif t.tag == "TVarArg" then
    if not kindcheck_arity(env, t[1]) then
      t[1] = Any
    end
    return true
  elseif t.tag == "TTuple" then
    for i,elem in ipairs(t) do
      if not kindcheck_arity(env,elem) then
        t[i] = Any
      end
    end
    return true
  elseif t.tag == "TUnionList" then
    for i,elem in ipairs(t) do
      if not kindcheck_arity(env,elem) then
        t[i] = Any
      end
    end
    return true
  elseif t.tag == "TFunction" then
    tlst.begin_scope(env)
    env.variance = env.variance * -1
    --check type arguments
    for i,tpar in ipairs(t[3]) do
      local name, variance, tbound = tpar[1], tpar[2], tpar[3]
      assert(variance == "Invariant")
      local ti = tlst.typeinfo_Variable(tbound, variance)
      env.set_typeinfo(env, name, ti, true)
    end
    for i,tpar in ipairs(t[3]) do
      local tbound = tpar[3]
      if not kindcheck_arity(env, tbound) then
        tpar[3] = Any
      end
    end  
    if not kindcheck_arity(env, t[1]) then
      t[1] = Any
    end
    env.variance = env.variance * -1
    if not kindcheck_arity(env, t[2]) then
      t[2] = Any
    end
    tlst.end_scope(env)
    return true
  elseif t.tag == "TField" then
    env.variance = env.variance * -1
    if not kindcheck_arity(env,t[1]) then
      t[1] = Any
    end
    env.variance = env.variance * -1
    if tltype.isConstField(t) then
      if not kindcheck_arity(env,t[2]) then
        t[2] = Any
      end
    else
      local orig_variance = env.variance
      env.variance = 0
      if not kindcheck_arity(env,t[2]) then
        t[2] = Any
      end
      env.variance = orig_variance      
    end
    return true
  elseif t.tag == "TTable" then
    for i,field in ipairs(t) do
      if not kindcheck_arity(env,field) then
        t[i] = Any
      end
    end
    return true
  elseif t.tag == "TSymbol" then
    expand_typealias(env, t)
    local name = t[1]
    local args = t[2]
    local ti = tlst.get_typeinfo(env, name)
    if not ti then
      local msg = string.format("Undeclared type %s", name)
      typeerror(env, "kind", msg, t.pos)
      return false
    else
      if ti.tag == "TINominal" then
        local tpars = ti[2]
        
        if #tpars ~= #args then
          local msg = string.format("%s expected %d arguments but received %d",name,#tpars,#args)
          typeerror(env, "kind", msg, t.pos)
          return false
        else
          for i,tpar in ipairs(tpars) do
            local variance = tpar[2]
            if variance == "Covariant" then
              kindcheck_arity(env,args[i])
            elseif variance == "Contravariant" then
              env.variance = env.variance * -1
              kindcheck_arity(env, args[i])
              env.variance = env.variance * -1
            elseif variance == "Invariant" then
              local orig_variance = env.variance
              env.variance = 0
              kindcheck_arity(env,args[i])
              env.variance = orig_variance
            end
          end
          return true
        end
      elseif ti.tag == "TIVariable" then
        if #args > 0 then
          local msg = string.format("Only class/interface types should be supplied type arguments")
          typeerror(env, "kind", msg, t.pos)
          return false
        end
        if ti[2] == "Covariant" and env.variance <= 0 then
          local msg = "Contravariant usage of covariant type variable %s"
          msg = string.format(msg, name)
          typeerror(env, "kind", msg, t.pos)
          return false
        elseif ti[2] == "Contravariant" and env.variance >= 0 then
          local msg = "Covariant usage of contravariant type variable %s"
          msg = string.format(msg, name)
          typeerror(env, "kind", msg, t.pos)
          return false
        end
        
        return true
      else
        if #args > 0 then
          local msg = string.format("Only class/interface types should be supplied type arguments")
          typeerror(env, "kind", msg, t.pos)
          return false
        else
          return true
        end
      end
    end
  elseif t.tag == "TVararg" then
    if not kindcheck_arity(env, t[1]) then
      t[1] = Any
    end
    return true
  else
    assert("kind checking error: expected type, got " .. t.tag) 
  end  
end


--full kindchecking, including arity, definedness, and type bounds on type operator arguments
local function kindcheck (env, t)
  if type(t) == "boolean" then
    assert(false)
  end
  if t.tag == "TLiteral" then
    return true
  elseif t.tag == "TBase" then
    return true
  elseif t.tag == "TNil" then
    return true
  elseif t.tag == "TValue" then
    return true
  elseif t.tag == "TAny" then
    return true
  elseif t.tag == "TSelf" then
    return true
  elseif t.tag == "TVoid" then
    return true
  elseif t.tag == "TUnion" then
    for i,elem in ipairs(t) do
      if not kindcheck(env, elem) then
        t[i] = Any
      end
    end
    return true
  elseif t.tag == "TVarArg" then
    if not kindcheck(env, t[1]) then
      t[1] = Any
    end
    return true
  elseif t.tag == "TTuple" then
    for i,elem in ipairs(t) do
      if not kindcheck(env,elem) then
        t[i] = Any
      end
    end
    return true
  elseif t.tag == "TUnionList" then
    for i,elem in ipairs(t) do
      if not kindcheck(env,elem) then
        t[i] = Any
      end
    end
    return true
  elseif t.tag == "TFunction" then
    tlst.begin_scope(env)
    env.variance = env.variance * -1
    --check type arguments
    for i,tpar in ipairs(t[3]) do
      local name, variance, tbound = tpar[1], tpar[2], tpar[3]
      assert(variance == "Invariant")
      local ti = tlst.typeinfo_Variable(tbound, variance)
      env.set_typeinfo(env, name, ti, true)
    end
    for i,tpar in ipairs(t[3]) do
      local tbound = tpar[3]
      if not kindcheck(env, tbound) then
        tpar[3] = Any
      end
    end  
    if not kindcheck(env, t[1]) then
      t[1] = Any
    end
    env.variance = env.variance * -1
    if not kindcheck(env, t[2]) then
      t[2] = Any
    end
    tlst.end_scope(env)
    return true
  elseif t.tag == "TField" then
    env.variance = env.variance * -1
    if not kindcheck(env,t[1]) then
      t[1] = Any
    end
    env.variance = env.variance * -1
    if tltype.isConstField(t) then
      if not kindcheck(env,t[2]) then
        t[2] = Any
      end
    else
      local orig_variance = env.variance
      env.variance = 0
      if not kindcheck(env,t[2]) then
        t[2] = Any
      end
      env.variance = orig_variance      
    end
    return true
  elseif t.tag == "TTable" then
    for i,field in ipairs(t) do
      if not kindcheck(env,field) then
        t[i] = Any
      end
    end
    return true
  elseif t.tag == "TSymbol" then
    expand_typealias(env, t)
    local name = t[1]
    local args = t[2]
    local ti = tlst.get_typeinfo(env, name)
    if not ti then
      local msg = string.format("Undeclared type %s", name)
      typeerror(env, "kind", msg, t.pos)
      return false
    else
      if ti.tag == "TINominal" then
        local tpars = ti[2]
        
        if #tpars ~= #args then
          local msg = string.format("%s expected %d arguments but received %d",name,#tpars,#args)
          typeerror(env, "kind", msg, t.pos)
          return false
        else
          local names = {}
          for i=1,#tpars do
            names[#names + 1] = tpars[i][1]
          end
              
          for i,tpar in ipairs(tpars) do
            local variance = tpar[2]
            if variance == "Covariant" then
              kindcheck(env,args[i])
            elseif variance == "Contravariant" then
              env.variance = env.variance * -1
              kindcheck(env, args[i])
              env.variance = env.variance * -1
            elseif variance == "Invariant" then
              local orig_variance = env.variance
              env.variance = 0
              kindcheck(env,args[i])
              env.variance = orig_variance
            end
            
            local bound = tpar[3] 
            if bound ~= "NoBound" then
              bound = tltype.substitutes(bound, names, args)
              local succ, explanation = tltype.consistent_subtype(env, args[i], bound) 
              if not succ then
                local msg = string.format("%s is not a subtype of %s", tltype.tostring(args[i]), tltype.tostring(bound))
                typeerror(env, "kind", msg .. "\n" .. explanation, args[i].pos)
                args[i] = Any
              end
            end
          end
          return true
        end
      elseif ti.tag == "TIVariable" then
        if #args > 0 then
          local msg = string.format("Only class/interface types should be supplied type arguments")
          typeerror(env, "kind", msg, t.pos)
          return false
        end
        if ti[2] == "Covariant" and env.variance <= 0 then
          local msg = "Contravariant usage of covariant type variable %s"
          msg = string.format(msg, name)
          typeerror(env, "kind", msg, t.pos)
          return false
        elseif ti[2] == "Contravariant" and env.variance >= 0 then
          local msg = "Covariant usage of contravariant type variable %s"
          msg = string.format(msg, name)
          typeerror(env, "kind", msg, t.pos)
          return false
        end
        
        return true
      else
        if #args > 0 then
          local msg = string.format("Only class/interface types should be supplied type arguments")
          typeerror(env, "kind", msg, t.pos)
          return false
        else
          return true
        end
      end
    end
  elseif t.tag == "TVararg" then
    if not kindcheck(env, t[1]) then
      t[1] = Any
    end
    return true
  else
    assert("kind checking error: expected type, got " .. t.tag) 
  end  
end

local function check_self (env, torig, t, pos)
  local msg = string.format("self type appearing in a place that is not a first parameter or a return type inside type '%s', replacing with 'any'", tltype.tostring(torig))
  if tltype.isSelf(t) then
    typeerror(env, "self", msg, pos)
    return tltype.Any()
  elseif tltype.isUnion(t) or
         tltype.isUnionlist(t) or
         tltype.isTuple(t) then
   local r = { tag = t.tag, name = t.name }
   for k, v in ipairs(t) do
     r[k] = check_self(env, torig, v, pos)
   end
   return r
  elseif tltype.isFunction(t) then
    local r = tltype.Function(t[3], check_self(env, torig, t[1], pos),
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
  if tltype.isUnion(t) or
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
      local r = tltype.Function(t[3], ninput, t[2])
      r.name = t.name
      return r
    else
      local r = tltype.Function(t[3], check_self(env, torig, t[1], pos),
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
  local new_env = tlst.new_env(subject, path, env.strict, env.genv) 
  new_env.subject = subject
  new_env.filename = path
  tlst.begin_function(new_env)
  check_block(new_env, ast)
  local t1 = tltype.first(infer_return_type(new_env))
  tlst.end_function(new_env)
  return t1
end

local function check_parameters (env, parlist, selfimplicit, pos, check_kinds)
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
      l[i] = parlist[i][2]
      env.variance = env.variance * -1
      if check_kinds and (not kindcheck(env, l[i])) then
        parlist[i][2] = Any
        l[i] = Any
      end
      env.variance = env.variance * -1
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
  if tlst.get_typeinfo(env, name) then
    local msg = "attempt to redeclare type '%s'"
    msg = string.format(msg, name)
    typeerror(env, "alias", msg, stm.pos)
  else
    tlst.set_typeinfo(env, name, tlst.typeinfo_Userdata(name,t), is_local)
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
    elseif tag == "TypeBundle" then
      check_typedefs(env, v)
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
  local genv = env.genv
  if not genv["loaded"][name] then
    local path = string.gsub(package.path..";", "[.]lua;", ".tl;")
    local filepath, msg1 = searchpath(extra_path .. name, path)
    if filepath then
      if string.find(filepath, env.parent) then
        genv["loaded"][name] = Any
        typeerror(env, "load", "circular require", pos)
      else
        genv["loaded"][name] = check_tl(env, name, filepath, pos)
      end
    else
      path = string.gsub(package.path..";", "[.]lua;", ".tld;")
      local filepath, msg2 = searchpath(extra_path .. name, path)
      if filepath then
        genv["loaded"][name] = check_tld(env, name, filepath, pos)
      else
        genv["loaded"][name] = Any
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
  return genv["loaded"][name]
end

local function check_arith (env, exp, op)
  local exp1, exp2 = exp[2], exp[3]
  check_exp(env, exp1)
  check_exp(env, exp2)
  local t1, t2 = tltype.first(get_type(exp1)), tltype.first(get_type(exp2))
  local msg = "attempt to perform arithmetic on a '%s'"
  if tltype.subtype(env, t1, tltype.Integer(true)) and
     tltype.subtype(env, t2, tltype.Integer(true)) then
    if op == "div" or op == "pow" then
      set_type(env, exp, Number)
    else
      set_type(env, exp, Integer)
    end
  elseif tltype.subtype(env, t1, Number) and tltype.subtype(env, t2, Number) then
    set_type(env, exp, Number)
    if op == "idiv" then
      local msg = "integer division on floats"
      typeerror(env, "arith", msg, exp1.pos)
    end
  elseif tltype.isAny(t1) then
    set_type(env, exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "any", msg, exp1.pos)
  elseif tltype.isAny(t2) then
    set_type(env, exp, Any)
    msg = string.format(msg, tltype.tostring(t2))
    typeerror(env, "any", msg, exp2.pos)
  else
    set_type(env, exp, Any)
    local wrong_type, wrong_pos = tltype.general(t1), exp1.pos
    if tltype.subtype(env, t1, Number) or tltype.isAny(t1) then
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
  if tltype.subtype(env, t1, tltype.Integer(true)) and
     tltype.subtype(env, t2, tltype.Integer(true)) then
    set_type(env, exp, Integer)
  elseif tltype.isAny(t1) then
    set_type(env, exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "any", msg, exp1.pos)
  elseif tltype.isAny(t2) then
    set_type(env, exp, Any)
    msg = string.format(msg, tltype.tostring(t2))
    typeerror(env, "any", msg, exp2.pos)
  else
    set_type(env, exp, Any)
    local wrong_type, wrong_pos = tltype.general(t1), exp1.pos
    if tltype.subtype(env, t1, Number) or tltype.isAny(t1) then
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
  if tltype.subtype(env, t1, String) and tltype.subtype(env, t2, String) then
    set_type(env, exp, String)
  elseif tltype.isAny(t1) then
    set_type(exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "any", msg, exp1.pos)
  elseif tltype.isAny(t2) then
    set_type(env, exp, Any)
    msg = string.format(msg, tltype.tostring(t2))
    typeerror(env, "any", msg, exp2.pos)
  else
    set_type(env, exp, Any)
    local wrong_type, wrong_pos = tltype.general(t1), exp1.pos
    if tltype.subtype(env, t1, String) or tltype.isAny(t1) then
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
  set_type(env, exp, Boolean)
end

local function check_order (env, exp)
  local exp1, exp2 = exp[2], exp[3]
  check_exp(env, exp1)
  check_exp(env, exp2)
  local t1, t2 = tltype.first(get_type(exp1)), tltype.first(get_type(exp2))
  local msg = "attempt to compare '%s' with '%s'"
  if tltype.subtype(env, t1, Number) and tltype.subtype(env, t2, Number) then
    set_type(env, exp, Boolean)
  elseif tltype.subtype(env, t1, String) and tltype.subtype(env, t2, String) then
    set_type(exp, Boolean)
  elseif tltype.isAny(t1) then
    set_type(env, exp, Any)
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "any", msg, exp1.pos)
  elseif tltype.isAny(t2) then
    set_type(env, exp, Any)
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "any", msg, exp2.pos)
  else
    set_type(env, exp, Any)
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
    set_type(env, exp, t1)
  elseif tltype.isUnion(t1, Nil) then
    set_type(env, exp, tltype.Union(t2, Nil))
  elseif tltype.isUnion(t1, False) then
    set_type(env, exp, tltype.Union(t2, False))
  elseif tltype.isBoolean(t1) then
    set_type(env, exp, tltype.Union(t2, False))
  else
    set_type(env, exp, tltype.Union(t1, t2))
  end
end

local function check_or (env, exp)
  local exp1, exp2 = exp[2], exp[3]
  check_exp(env, exp1)
  check_exp(env, exp2)
  local t1, t2 = tltype.first(get_type(exp1)), tltype.first(get_type(exp2))
  if tltype.isNil(t1) or tltype.isFalse(t1) then
    set_type(env, exp, t2)
  elseif tltype.isUnion(t1, Nil) then
    set_type(env, exp, tltype.Union(tltype.filterUnion(env, t1, Nil), t2))
  elseif tltype.isUnion(t1, False) then
    set_type(env, exp, tltype.Union(tltype.filterUnion(env, t1, False), t2))
  else
    set_type(env, exp, tltype.Union(t1, t2))
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
  set_type(env, exp, Boolean)
end

local function check_bnot (env, exp)
  local exp1 = exp[2]
  check_exp(env, exp1)
  local t1 = tltype.first(get_type(exp1))
  local msg = "attempt to perform bitwise on a '%s'"
  if tltype.subtype(env, t1, tltype.Integer(true)) then
    set_type(env, exp, Integer)
  elseif tltype.isAny(t1) then
    set_type(env, exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "any", msg, exp1.pos)
  else
    set_type(env, exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "bitwise", msg, exp1.pos)
  end
end

local function check_minus (env, exp)
  local exp1 = exp[2]
  check_exp(env, exp1)
  local t1 = tltype.first(get_type(exp1))
  local msg = "attempt to perform arithmetic on a '%s'"
  if tltype.subtype(env, t1, Integer) then
    set_type(env, exp, Integer)
  elseif tltype.subtype(env, t1, Number) then
    set_type(env, exp, Number)
  elseif tltype.isAny(t1) then
    set_type(env, exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "any", msg, exp1.pos)
  else
    set_type(env, exp, Any)
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
  if tltype.subtype(env, t1, String) or
     tltype.subtype(env, t1, tltype.Table()) then
    set_type(env, exp, Integer)
  elseif tltype.isAny(t1) then
    set_type(env, exp, Any)
    msg = string.format(msg, tltype.tostring(t1))
    typeerror(env, "any", msg, exp1.pos)
  else
    set_type(env, exp, Any)
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
  set_type(env, exp, tltype.first(t1))
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
  if tltype.subtype(env, inf_type, dec_type) then
  elseif tltype.consistent_subtype(env, inf_type, dec_type) then
    msg = string.format(msg, tltype.tostring(inf_type), tltype.tostring(dec_type))
    typeerror(env, "any", msg, pos)
  else
    msg = string.format(msg, tltype.tostring(inf_type), tltype.tostring(dec_type))
    typeerror(env, "ret", msg, pos)
  end
end

local function check_function (env, exp)
  local idlist, ret_type, block, tpars = exp[1], exp[2], exp[3], exp[4]
  if not kindcheck(env, ret_type) then
    ret_type = Any
    exp[2] = Any
  end
  local infer_return = false
  tlst.begin_function(env)
  tlst.begin_scope(env)
  -- add type params to environment
  for i,tpar in ipairs(tpars) do
    local name, variance, tbound = tpar[1], tpar[2], tpar[3]
    assert(variance == "Invariant")
    local ti = tlst.typeinfo_Variable(tbound, variance)
    env.set_typeinfo(env, name, ti, true)
  end
  -- kindcheck all type parameter bounds
  for i,tpar in ipairs(tpars) do
    local name, variance, tbound = tpar[1], tpar[2], tpar[3]
    if not kindcheck(env, tbound) then
      tpar[3] = Any
    end
  end  
  local input_type = check_parameters(env, idlist, false, exp.pos, true)
  local t = tltype.Function(tpars, input_type, ret_type)
  local len = #idlist
  if len > 0 and idlist[len].tag == "Dots" then len = len - 1 end
  for k = 1, len do
    local v = idlist[k]
    set_type(env, v, v[2])
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
    t = tltype.Function(tpars, input_type, ret_type)
    set_type(env, exp, t)
  end
  check_return_type(env, inferred_type, ret_type, exp.pos)
  tlst.end_function(env)
  set_type(env, exp, t)
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
      if tltype.subtype(env, Nil, t1) then
        t1 = Any
        local msg = "table index can be nil"
        typeerror(env, "table", msg, exp1.pos)
      elseif not (tltype.subtype(env, t1, Boolean) or
                  tltype.subtype(env, t1, Number) or
                  tltype.subtype(env, t1, String)) then
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
  set_type(env, exp, t)
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
  local sub_succ, sub_explanation = tltype.subtype(env, infer_type, dec_type) 
  if not sub_succ then
    local cs_succ, cs_explanation = tltype.consistent_subtype(env, infer_type, dec_type)
    if cs_succ then 
      msg = string.format(msg, tltype.tostring(infer_type), func_name, tltype.tostring(dec_type))
      msg = msg .. "\n" .. sub_explanation
      typeerror(env, "any", msg, pos)
    else
      msg = string.format(msg, tltype.tostring(infer_type), func_name, tltype.tostring(dec_type))
      msg = msg .. "\n" .. cs_explanation
      typeerror(env, "args", msg, pos)
    end
  end
end


local function check_call (env, exp)
  local exp1 = exp[1]
  local targs = exp[2]
  local explist = {}
  for _,targ in ipairs(targs) do
    kindcheck(env, targ)
  end
  for i = 3, #exp do
    explist[i - 2] = exp[i]
  end
  check_exp(env, exp1)
  check_explist(env, explist)
  if exp1.tag == "Index" and
     exp1[1].tag == "Id" and exp1[1][1] == "_ENV" and
     exp1[2].tag == "String" and exp1[2][1] == "setmetatable" and 
     #targs == 0 then
    if explist[1] and explist[2] then
      local t1, t2 = get_type(explist[1]), get_type(explist[2])
      local t3 = tltype.getField(env, tltype.Literal("__index"), t2)
      if not tltype.isNil(t3) then
        if tltype.isTable(t3) then t3.open = true end
        set_type(env, exp, t3)
      else
        local msg = "second argument of setmetatable must be { __index = e }"
        typeerror(env, "call", msg, exp.pos)
        set_type(env, exp, Any)
      end
    else
      local msg = "setmetatable must have two arguments"
      typeerror(env, "call", msg, exp.pos)
      set_type(env, exp, Any)
    end
  elseif exp1.tag == "Index" and
         exp1[1].tag == "Id" and exp1[1][1] == "_ENV" and
         exp1[2].tag == "String" and exp1[2][1] == "require" and 
         #targs == 0 then
    if explist[1] then
      local t1 = get_type(explist[1])
      if tltype.isStr(t1) then
        set_type(env, exp, check_require(env, explist[1][1], exp.pos))
      else
        local msg = "the argument of require must be a literal string"
        typeerror(env, "call", msg, exp.pos)
        set_type(env, exp, Any)
      end
    else
      local msg = "require must have one argument"
      typeerror(env, "call", msg, exp.pos)
      set_type(env, exp, Any)
    end
  else
    local t = tltype.first(get_type(exp1))
    local inferred_type = arglist2type(explist, env.strict)
    local msg = "attempt to call %s of type '%s'"
    if tltype.isFunction(t) then
      --todo substitute targs for t
      local tinput = t[1]
      local tret = t[2]
      local tparams = t[3]
      if #tparams ~= #targs then
        local msg = "expected %d type arguments but got %d"
        msg = string.format(msg, #tparams, #targs)
        typeerror(env, "call", msg, exp1.pos)
        set_type(env, exp, Any)
      else
        local substituted_bounds = {}
        
        local param_names = {}
        for i,par in ipairs(tparams) do param_names[i] = par[1] end
        
        -- substitute type args into bounds
        for i, tparam in ipairs(tparams) do
          local tbound = tltype.substitutes(tparam[3], param_names, targs)
          table.insert(substituted_bounds, tbound)
        end
           
        -- check that bounds are satisfied
        for i,tparam in ipairs(tparams) do
          local name, variance = tparam[1], tparam[2]
          assert(variance == "Invariant")
          if not tltype.subtype(env, targs[i], substituted_bounds[i]) then
            local msg = "type argument %s is not a subtype of bound %s"
            msg = string.format(msg, tltype.tostring(targs[i]), tltype.tostring(substituted_bounds[i]))
            typeerror(env, "call", msg, targs[i].pos)
            tinput = tltype.substitute(tinput, name, Any)
            tret = tltype.substitute(tret, name, Any)
          end
        end
        
        --substitute type arguments
        tinput = tltype.substitutes(tinput, param_names, targs)
        tret = tltype.substitutes(tret, param_names, targs)
      end
      check_arguments(env, var2name(exp1), tinput, inferred_type, exp.pos)
      set_type(env, exp, tret)      
    elseif tltype.isAny(t) then
      set_type(env, exp, Any)
      msg = string.format(msg, var2name(exp1), tltype.tostring(t))
      typeerror(env, "any", msg, exp.pos)
    else
      set_type(env, exp, Nil)
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
  local t1, t2 = tltype.unfold(env, get_type(exp1)), get_type(exp2)
  --TODO: maybe we need to unfold exp1.type for pseudo-method invocations
  if tltype.isTable(t1) then
    assert(tltype.isLiteral(t2) and type(t2[1]) == "string")
    local tfield = tltype.getField(env, t2, t1)
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
      t3 = tltype.getField(env, t2, t1)
    else
      local string_userdata = env["loaded"]["string"] or tltype.Table()
      t3 = tltype.getField(env, t2, string_userdata)
      inferred_type[1] = String
    end
    local msg = "attempt to call method '%s' of type '%s'"
    if tltype.isFunction(t3) then
      check_arguments(env, "field", t3[1], inferred_type, exp.pos)
      set_type(env, exp, t3[2])
    elseif tltype.isAny(t3) then
      set_type(env, exp, Any)
      msg = string.format(msg, exp2[1], tltype.tostring(t3))
      typeerror(env, "any", msg, exp.pos)
    else
      set_type(env, exp, Nil)
      msg = string.format(msg, exp2[1], tltype.tostring(t3))
      typeerror(env, "invoke", msg, exp.pos)
    end
  elseif tltype.isAny(t1) then
    set_type(env, exp, Any)
    local msg = "attempt to index '%s' with '%s'"
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "any", msg, exp.pos)
  else
    set_type(env, exp, Nil)
    local msg = "attempt to index '%s' with '%s'"
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "index", msg, exp.pos)
  end
  return false
end

local function check_superinvoke(env, exp)
  local tsuperclass_symbol = tlst.get_tsuper(env)
  if tsuperclass_symbol == "None" then
    local msg = "tried to invoke superclass method in a class which has no superclass"
    typeerror(env, "superinvoke", msg, exp.pos) 
    set_type(env, exp, Any)
    return
  end
  local tsuperclass = tltype.unfold(env, tsuperclass_symbol)
  local name_exp = exp[1]
  local explist = {}
  explist[1] = tlast.ident(0, "self")
  for i = 2, #exp do
    explist[i] = exp[i]
  end
  check_exp(env,name_exp)
  assert(tltype.isStr(get_type(name_exp)))
  check_explist(env, explist)
  if not tsuperclass then
    local msg = "superclass invocations can only occur inside definitions of classes with superclasses"
    typeerror(env, "superinvoke", msg, exp.pos)
    return false
  end
  
  local tpremethods = tltype.getField(env, tltype.Literal("__premethods"), tsuperclass)
  local tcalled_premethod = tltype.getField(env, tltype.Literal(name_exp[1]), tpremethods)
  if not tcalled_premethod then
    local msg = "superclass %s does not have a premethod called %s"
    msg = string.format(msg, tltype.tostring(tsuperclass), name_exp[1])
    typeerror(env, "superinvoke", msg, name_exp.pos)
    return false
  end
  assert(tltype.isFunction(tcalled_premethod))
  local tinput,toutput = tcalled_premethod[1], tcalled_premethod[2] 
  local inferred_input = arglist2type(explist, env.strict)
  check_arguments(env, name_exp[1], tinput, inferred_input, exp.pos)
  set_type(env, exp, toutput)
  return true
end

local function check_class_lookup(env, exp)
  local typeid = exp[1][1]
  local global_name = tlst.get_typealias(env, typeid)
  if global_name then exp[1][1] = global_name end
  local tclass = tlst.get_classtype(env, global_name or typeid)
  if not tclass then
    local msg = "%s is not a class or is not in scope"
    msg = string.format(msg, typeid)
    typeerror(env, "classlookup", msg, exp[1].pos)
    return
  end
  set_type(env, exp, tclass)
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
    local msg = "attempt to assign '%s' to '%s'"
    local local_type = tltype.unfold(env, local_type)
    msg = string.format(msg, tltype.tostring(inferred_type), tltype.tostring(local_type))
    if tltype.subtype(env, inferred_type, local_type) then
    elseif tltype.consistent_subtype(env, inferred_type, local_type) then
      typeerror(env, "any", msg, pos)
    else
      typeerror(env, "local", msg, pos)
    end
  end
  set_type(env, id, local_type)
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
  for _,id in ipairs(idlist) do
    if id[2] then
      if not kindcheck(env, id[2]) then
        id[2] = Any
      end
    end
  end
  if unannotated_idlist(idlist) and
     #explist == 1 and
     tltype.isUnionlist(get_type(explist[1])) and
     sized_unionlist(get_type(explist[1])) and
     #idlist == #get_type(explist[1])[1] - 1 then
    local t = get_type(explist[1])
    for k, v in ipairs(idlist) do
      set_type(env, v, t)
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
  local idlist, ret_type, block, tpars = exp[1], exp[2], exp[3], exp[4]
  if (ret_type == false) or (not kindcheck(env, ret_type)) then
    ret_type = tltype.Tuple({Any}, true)
    exp[2] = ret_type
  end
  local infer_return = false
  if not block then
    block = ret_type
    ret_type = tltype.Tuple({ Nil }, true)
    infer_return = true
  end
  tlst.begin_function(env)
  local input_type = check_parameters(env, idlist, false, exp.pos, true)  
  local t = tltype.Function(tpars, input_type, ret_type)
  id[2] = t
  set_type(env, id, t)
  check_masking(env, id[1], id.pos)
  tlst.set_local(env, id)
  tlst.begin_scope(env)
  for i,tpar in ipairs(tpars) do kindcheck(env, tpar[3]) end
  set_tpars(env, tpars)
  local len = #idlist
  if len > 0 and idlist[len].tag == "Dots" then len = len - 1 end
  for k = 1, len do
    local v = idlist[k]
    set_type(env, v, v[2])
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
    t = tltype.Function({}, input_type, ret_type)
    id[2] = t
    set_type(env, id, t)
    tlst.set_local(env, id)
    set_type(env, exp, t)
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
  if tltype.subtype(env, exp_type, var_type) then
  elseif tltype.consistent_subtype(env, exp_type, var_type) then
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
        if tltype.subtype(env, t1, t2) then
          l.bkp = t2
          set_type(env, l, t1)
        end
      end
      l.assigned = true
    elseif tag == "Index" then
      local t1, t2 = get_type(v[1]), get_type(v[2])
      if tltype.isTable(t1) then
        local field = tltype.getFieldTable(env, t2, t1)
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
      if tltype.subtype(env, v[i], t) and tltype.subtype(env, t, v[i]) then
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
          set_type(env, var, tltype.filterUnion(env, get_type(var), Nil))
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
            var.filter = tltype.filterUnion(env, get_type(var), Nil)
          else
            var.filter = tltype.filterUnion(env, var.filter, Nil)
          end
          set_type(env, var, Nil)
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
            var.filter = tltype.filterUnion(env, get_type(var), t)
          else
            var.filter = tltype.filterUnion(env, var.filter, t)
          end
          set_type(env, var, t)
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
          set_type(env, var, tltype.filterUnion(env, get_type(var), t))
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
        set_type(env, v, v.filter)
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
        set_type(env, v, v.bkp)
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
  if tltype.subtype(env, t1, Number) then
  elseif tltype.consistent_subtype(env, t1, Number) then
    typeerror(env, "any", msg, exp1.pos)
  else
    typeerror(env, "fornum", msg, exp1.pos)
  end
  check_exp(env, exp2)
  local t2 = get_type(exp2)
  msg = "'for' limit must be a number"
  if tltype.subtype(env, t2, Number) then
  elseif tltype.consistent_subtype(env, t2, Number) then
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
    if tltype.subtype(env, t3, Number) then
    elseif tltype.consistent_subtype(env, t3, Number) then
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
    set_type(env, id, Integer)
  else
    set_type(env, id, Number)
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
      set_type(env, l[k], v)
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
    local t = tltype.filterUnion(env, tuple(k), Nil)
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
  local t1 = t1 and tltype.unfold(env,t1)
  local msg = "attempt to index '%s' with '%s'"
  if tltype.isTable(t1) then
    -- FIX: methods should not leave objects, this is unsafe!
    local field_type = tltype.getField(env, t2, t1)
    if not tltype.isNil(field_type) then
      local field = tltype.getFieldTable(env, t2, t1)
      if field.missing then
        msg = "attempt to access missing field %s"
        msg = string.format(msg, tltype.tostring(t2))
        typeerror(env, "index", msg, exp.pos)
        set_type(env, exp, Nil)      
      end
      set_type(env, exp, field_type)
    else
      if exp1.tag == "Id" and exp1[1] == "_ENV" and exp2.tag == "String" then
        msg = "attempt to access undeclared global '%s'"
        msg = string.format(msg, exp2[1])
      else
        msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
      end
      typeerror(env, "index", msg, exp.pos)
      set_type(env, exp, Nil)
    end
  elseif tltype.isAny(t1) then
    set_type(env, exp, Any)
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "any", msg, exp.pos)
  else
    set_type(env, exp, Nil)
    msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
    typeerror(env, "index", msg, exp.pos)
  end
end

local function check_class_redecl (env, elems)
    local instance_fields = {}
    local class_fields = {}
    
    local function check_inst(name,pos)
      if instance_fields[name] then
        local msg = string.format("class element %s redeclared",name)
        typeerror(env, "self", msg, pos)
      end      
      instance_fields[name] = true
    end
    
    local function check_constructor(name,pos)
      if class_fields[name] then
        local msg = string.format("constructor %s redeclared",name)
        typeerror(env, "self", msg, pos)
      end      
      class_fields[name] = true
    end
    
    for i,elem in ipairs(elems) do
      if elem.tag == "ConcreteClassField" then
        local name = elem[1][1]
        check_inst(name,elem.pos)
      elseif elem.tag == "AbstractClassField" then
        local name = elem[1][1]
        check_inst(name,elem.pos)  
      elseif elem.tag == "ConcreteClassMethod" then
        local name = elem[1][1]
        check_inst(name,elem.pos)         
      elseif elem.tag == "AbstractClassMethod" then
        local name = elem[1][1] 
        check_inst(name,elem.pos)  
      elseif elem.tag == "ClassConstructor" then
        local name = elem[1][1]
        if name == "__premethods" then
          local msg = string.format("constructors named '__premethods' are not allowed. renaming to 'premethods",name)
          typeerror(env, "redeclaration", msg, elem.pos)
          elem[1][1] = "premethods"
        end
        check_constructor(elem[1][1], elem.pos)
      elseif elem.tag == "ClassFinalizer" then
        --nothing to do here
      else
        error("cannot type check class element " .. elem.tag)
      end
    end 
end


-- returns constructors,methods,members
-- where each returned value maps names to { id : string, ty : type } records 
local function get_elem_types (env, elems)
    local constructors = {}
    local methods = {}
    local members = {}
    
    for _,elem in ipairs(elems) do
      if elem.tag == "ConcreteClassField" then
        local name = elem[1][1]
        members[name] = { id = elem[1], ty = elem[2], const = elem.const }
      elseif elem.tag == "AbstractClassField" then
        local name,t = elem[1][1], elem[2]
        --TODO: handle abstract vs. concrete fields
        members[name] = { id = elem[1], ty = t, const = elem.const }
      elseif elem.tag == "ConcreteClassMethod" then
        local name,parlist,tret = elem[1][1],elem[2],elem[3]
        local t1 = check_parameters(env, parlist, false, elem.pos, false)
        local t2 = tret
        methods[name] = { id = elem[1], ty = tltype.Function({}, t1, t2, true) }
      elseif elem.tag == "AbstractClassMethod" then
        local name, t = elem[1][1], elem[2] 
        methods[name] = { id = elem[1], ty = t }
      elseif elem.tag == "ClassConstructor" then
        local name,parlist = elem[1][1],elem[2]
        local t1 = check_parameters(env, parlist, false, elem.pos, false)
        constructors[name] = { id = elem[1], ty = tltype.Function({}, t1, tltype.Void(), false) }
      elseif elem.tag == "ClassFinalizer" then
        --nothing to do here
      else
        error("cannot type check class element " .. elem.tag)
      end
    end 
    
    return constructors,methods,members
end

-- check_constructor_supercall : (env, id, explist, type) -> ()
local function check_constructor_supercall (env, supercons_name, super_args, tsuper_inst, tsuper_class)
  local constructor = tltype.getField(env, tltype.Literal(supercons_name[1]), tsuper_class)
  
  if not constructor then
    local msg = "superclass constructor %s called, but superclass %s does not have a constructor with that name."
    msg = string.format(msg, supercons_name[1], tltype.tostring(tsuper_inst))
    typeerror(env, "call", msg, supercons_name.pos)
  else
    check_explist(env, super_args)
    local t = tltype.first(constructor)
    local tpars = constructor[3]
    local tpar_names = {}
    for i,tpar in ipairs(tpars) do
      tpar_names[i] = tpar[1]
    end
    t = tltype.substitutes(t, tpar_names, tsuper_inst[2])
    local inferred_type = arglist2type(super_args, env.strict)
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

local function check_constructor (env, elem, instance_members, parent_members, tsuper_inst)
  local name, idlist, supercons_name, superargs, body, pos = elem[1], elem[2], elem[3], elem[4], elem[5], elem.pos
  tlst.begin_function(env)
  tlst.set_in_constructor(env)
  tlst.begin_scope(env)  
  local input_type = check_parameters(env, idlist, true, idlist.pos, true)
  local output_type = tltype.Tuple({ Nil }, true)
  local t = tltype.Function({}, input_type, output_type)
  
  local len = #idlist
  if len > 0 and idlist[len].tag == "Dots" then len = len - 1 end
  for k = 1,len do
    local v = idlist[k]
    set_type(env, v, v[2])
    check_masking(env, v[1], v.pos)
    tlst.set_local(env,v)
  end
  
  if superargs ~= "NoSuperCall" then
    if tsuper_inst then
      local tsuper_class = tlst.get_classtype(env, tsuper_inst[1])
      check_constructor_supercall(env, supercons_name, superargs, tsuper_inst, tsuper_class)
    else
      local msg = "called superclass constructor, but %s has no superclass"
      msg = string.format(msg, name[1])
      typeerror(env, "inheritance", msg, name.pos)
    end
  end
  local tself = tltype.Table()
  for k,v in pairs(parent_members) do
    tself[#tself + 1] = v
  end
  for k,v in pairs(instance_members) do
    if not parent_members[k] then
      tself[#tself + 1] = v
    end
  end
  for _,field in ipairs(tself) do
    assert(tltype.isStr(field[1]))
    if superargs == "NoSuperCall" or not parent_members[field[1].name] then
      field.missing = true
    end
  end
  tself.closed = true    
  
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
  local input_type = check_parameters(env, idlist, true, idlist.pos, true)
  local t = tltype.Function({}, input_type, tret)
  local len = #idlist
  if len > 0 and idlist[len].tag == "Dots" then len = len - 1 end
  for k = 1,len do
    local v = idlist[k]
    set_type(env, v, v[2])
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

local function premethod_from_method (method, tinstance)
  assert(method.const)
  
  local tkey = method[1]
  local tvalue = method[2]
  local tinput = tvalue[1]
  local toutput = tvalue[2]
  
  if not tinput then
    assert(false)
  end
  
  assert(tltype.isSelf(tinput[1]))
  
  local new_tinput = {}
  for k,v in pairs(tinput) do new_tinput[k] = v end
  new_tinput[1] = tinstance
  
  local new_function = tltype.Function({}, new_tinput, toutput)
  
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
  
  local new_function = tltype.Function({}, new_tinput, toutput)
  
  return tltype.Field(true, premethod[1], new_function)
end

--returns the object type of the class type t
local function object_type_from_class(t)
  for _,field in ipairs(t) do
    local tkey,tval = field[1], field[2]
    if tkey.name ~= "__premethods" then
      return tval[2]
    end
  end
  assert(false)
end

-- get_superclass_fields : (env, type) -> ({string => field}, {string => field}, {string => field}) 
local function get_superclass_fields (env, tsuper)
  assert(tsuper.tag == "TSymbol")
  
  local superargs = tsuper[2]
  local tsuperclass = tlst.get_classtype(env, tsuper[1])
  assert(tsuperclass)
  local premethods = tltype.getField(env, tltype.Literal("__premethods"), tsuperclass)
  local t_superobject_def = tltype.unfold(env, tsuper)
  
  local members = {}
  local methods = {}
  local fields = {}
  for _,field in ipairs(t_superobject_def) do
    local premethod = tltype.getFieldTable(env, field[1], premethods)
    local fieldname = tltype.tostring(field[1])
    if premethod then
      methods[fieldname] = field
    else
      members[fieldname] = field
    end
    fields[fieldname] = field
  end
  
  return members, methods, fields
end

local function kindcheck_arity_class_elems(env, elems)
  for _,elem in ipairs(elems) do
    if elem.tag == "ConcreteClassMethod" then
      local parlist,tret = elem[2], elem[3]
      env.variance = -1      
      for i,par in ipairs(parlist) do
        if not kindcheck_arity(env, par[2]) then
          par[2] = Any
        end
      end
      env.variance = 1
      if not kindcheck_arity(env, tret) then
        elem[3] = Any
      end
    elseif elem.tag == "AbstractClassMethod" then
      env.variance = 1
      local success = kindcheck_arity(env, elem[2])
      --method types are not symbols, and therefore cannot fail arity checking
      assert(success)
    elseif elem.tag == "ClassConstructor" then
      local parlist = elem[2]
      env.variance = -1
      for i,par in ipairs(parlist) do
        if not kindcheck_arity(env, par[2]) then
          par[2] = Any
        end
      end      
    elseif elem.tag == "ConcreteClassField" then
      local const, ty = elem.const, elem[2]
      if not const then
        env.variance = 0
      else
        env.variance = 1
      end
      if not kindcheck_arity(env, ty) then
        elem[2] = Any
      end
    else
      assert("expected class element, but got " .. elem.tag)
    end    
  end
end

--kindchecks the types ascribed to the provided class elements
local function kindcheck_class_elems(env, elems)
  for _,elem in ipairs(elems) do
    if elem.tag == "ConcreteClassMethod" then
      local parlist,tret = elem[2], elem[3]
      env.variance = env.variance * -1      
      for i,par in ipairs(parlist) do
        if not kindcheck(env, par[2]) then
          par[2] = Any
        end
      end
      env.variance = env.variance * -1
      if not kindcheck(env, tret) then
        elem[3] = Any
      end
    elseif elem.tag == "AbstractClassMethod" then
      env.variance = 1
      local success = kindcheck(env, elem[2])
      --method types are not symbols, and therefore cannot fail arity checking
      assert(success)      
    elseif elem.tag == "ClassConstructor" then
      local parlist = elem[2]
      env.variance = env.variance * -1
      for i,par in ipairs(parlist) do
        if not kindcheck(env, par[2]) then
          par[2] = Any
        end
      end      
      env.variance = env.variance * -1
    elseif elem.tag == "ConcreteClassField" then
      local const, ty = elem.const, elem[2]
      local orig_variance = env.variance
      if not const then
        env.variance = 0
      end
      if not kindcheck(env, ty) then
        elem[2] = Any
      end
      env.variance = orig_variance
    else
      assert("expected class element, but got " .. elem.tag)
    end    
  end
end

local function get_interface_type (env, def)
  local name, elems = def[1], def[3]
  local constructors, methods, members = get_elem_types(env, elems)
  assert(#constructors == 0 and #members == 0)
  local fields = {}
  for k,method in pairs(methods) do
    local newelem = tltype.Field(true, tltype.Literal(k), method.ty)
    fields[#fields + 1] = newelem
  end  
  local t_interface = tltype.Table(table.unpack(fields))
  t_interface.fixed = true
  t_interface.name = name[1]  
  return t_interface
end

local function get_class_types (env, def)
  local name, isAbstract, elems, superclass = def[1], def[2], def[3], def[4]
  local t_params, superargs = def[5], def[6]
  local constructors, methods, members = get_elem_types(env, elems)
  local superclass_members, superclass_methods, superclass_fields
  if superclass == "NoParent" then
    superclass_methods = {}
    superclass_members = {}
    superclass_fields = {}
  else
    superclass_members, superclass_methods, superclass_fields = get_superclass_fields(env, superclass)
  end
  
  local instance_members = {}
  for k,v in pairs(superclass_members) do 
    if not members[k] then
      instance_members[k] = v 
    end
  end
  local instance_methods = {}
  for k,v in pairs(superclass_methods) do 
    if not methods[k] then
      instance_methods[k] = v 
    end
  end
  local instance_fields = {}
  for k,v in pairs(superclass_fields) do 
    if (not members[k]) and (not methods[k]) then
      instance_fields[#instance_fields + 1] = v
    end
  end
  
  for k,member in pairs(members) do      
    assert(not superclass_fields[k]) --remove duplicates as part of a pre-processing step
    local newelem = tltype.Field(member.const, tltype.Literal(k), member.ty) 
    instance_members[k] = newelem
    instance_fields[#instance_fields + 1] = newelem
  end
  
  for k,method in pairs(methods) do
    assert(not superclass_members[k]) --this should be ruled out during an earlier check
    local newelem = tltype.Field(true, tltype.Literal(k), method.ty)
    instance_methods[k] = newelem
    instance_fields[#instance_fields + 1] = newelem
  end
  
  local t_instance = tltype.Table(table.unpack(instance_fields))
  t_instance.fixed = true
  t_instance.name = name[1]
  
  --construct a symbol to recursively refer to an applied type operator
  local param_symbols = {}
  for _,v in ipairs(t_params) do
    table.insert(param_symbols, tltype.Symbol(v[1]))
  end
  local t_class_symbol = tltype.Symbol(current_modname(env)..name[1], param_symbols)
  
  --create constructor types, which are functions whose type parameters mirror those of the class,
  --and which return t_class_symbol
  local class_constructors = {}
  for k,v in pairs(constructors) do
    local t_constructor = v.ty
    --overwrite constructor return value with instance type
    t_constructor[2] = t_class_symbol
    local constructor_t_params = {}
    for _,p in ipairs(t_params) do 
      local new_t_param = { tag = "TypeParam", [1] = p[1], [2] = "Invariant", [3] = p[3] }
      if new_t_param[3] ~= "NoBound" then new_t_param[3] = tltype.clone(new_t_param[3]) end
      table.insert(constructor_t_params, new_t_param)
    end
    t_constructor[3] = constructor_t_params
    class_constructors[#class_constructors + 1] = tltype.Field(true, tltype.Literal(k), t_constructor)
  end
  
  local t_premethods = tltype.Table()
  for _,field in pairs(instance_methods) do 
    t_premethods[#t_premethods + 1] = premethod_from_method(field,tltype.Symbol(name[1],t_params)) 
  end
  
  local t_class = tltype.Table(table.unpack(class_constructors))
  t_class[#t_class + 1] = tltype.Field(true, tltype.Literal("__premethods"), t_premethods)
  t_class.fixed = true
  t_class.class = true
  
  return t_instance, t_class, instance_members, superclass_members  
end

-- typechecks the inheritance clause. returns true iff it typechecks properly
local function check_inheritance_clause (env, tsuper)
  if not kindcheck(env, tsuper) then
    return false
  end
  local msg = "%s is not a class type"
  msg = string.format(msg, tltype.tostring(tsuper))
  if tsuper.tag ~= "TSymbol" then
    typeerror(env, "inheritance", msg, pos)
    return false
  end
  local tisuper = tlst.get_typeinfo(env, tsuper[1])
  if tisuper.tag ~= "TINominal" then
    typeerror(env, "inheritance", msg, pos)
    return false    
  end
  if not tisuper.class then
    typeerror(env, "inheritance", msg, pos)
    return false    
  end
  
  return true
end

local function check_class_code(env, elems, t_instance, instance_members, superclass_members, tsuper_inst)
  for _,elem in ipairs(elems) do
    if elem.tag == "ConcreteClassMethod" then
      local name,parlist,tret,body = elem[1], elem[2], elem[3], elem[4]
      check_method(env,parlist,tret,body,t_instance,elem.pos)
    elseif elem.tag == "ClassConstructor" then
      check_constructor(env, elem, instance_members, superclass_members, tsuper_inst)
    else
      assert("expected class element, but got " .. elem.tag)
    end
  end  
end

local function make_tmethod (parlist, rettype)
  local pars = {}
  for i,par in ipairs(parlist) do
    local t = par[2]
    pars[i] = t
  end
  local t1 = tltype.Tuple(pars)
  local t2 = tltype.Tuple({rettype})
  return tltype.Function({}, t1, t2, true)
end

local function check_typedefs (env, stm)
  assert(stm.tag == "TypeBundle")
  local defs = stm[1]
  
  local bundle_typenames = {}
  --collect typenames and check for duplicates
  for _,def in ipairs(defs) do
    local name 
    if def.tag == "Class" or def.tag == "Interface" then
      name = def[1][1]
    elseif def.tag == "Typedef" then
      name = def[1]
    end
    name = current_modname(env) .. name
    if tlst.get_typeinfo(env, name) or bundle_typenames[name] then
      local msg = "attempt to redeclare type '%s'"
      msg = string.format(msg, name)
      typeerror(env, "alias", msg, def.pos)
      return false
    else
      bundle_typenames[name] = true
    end
  end
  
  --kindcheck bounds on class and interface definitions
  for _,def in ipairs(defs) do
    if def.tag == "Class" or def.tag == "Interface" then
      do tlst.begin_scope(env) --parameter variables
      local tpars
      if def.tag == "Class" then tpars = def[5]
      elseif def.tag == "Interface" then tpars = def[2] end
      set_tpars(env, tpars)
      
      --kindcheck the arity of bounds, as well as whether the typenames occuring
      --in them have been defined (but don't check subtyping constraints, which might not be well-kinded)
      for _,tpar in ipairs(tpars) do
        local tbound = tpar[3]
        local orig_variance = env.variance
        env.variance = -1
        if tbound ~= "NoBound" and not kindcheck_arity(env, tbound) then
          tpar[3] = Any
        end
        env.variance = orig_variance
      end
     
      --now that we have transformed all bounds into well-kinded ones, we can perform boundchecking
      --on our tpe parameter bounds.
      for _,tpar in ipairs(tpars) do
        local tbound = tpar[3]
        local orig_variance = env.variance
        env.variance = -1
        if tbound ~= "NoBound" and not kindcheck(env, tbound) then
          tpar[3] = Any
        end
        env.variance = orig_variance
      end     
      
      tlst.end_scope(env) end -- class parameter variables 
    end
  end
  
  --check inheritance clauses
  for _,def in ipairs(defs) do
    if def.tag == "Class" then
      local tsuper = def[4]
      if tsuper ~= "NoParent" then
        tlst.begin_scope(env) --check inheritance clause
        set_tpars(env, def[5])
        
        --TODO: add an extra optional parameter to kindcheck which generates special
        --error for names defined by the bundle (bundle_typenames)
        --these will alert the programmer that we can't inherit from types involving those defined in the bundle
        --and likewise, we can't use them in class parameter bounds
        if not kindcheck(env, tsuper) then
          tlst.end_scope(env) --check inheritance clause
          -- we can't inherit from Any, so we just abort typechecking the budle if this happens,
          -- and leave the environment untouched by this bundle definitions
          return false
        end 
        tlst.end_scope(env) end --check inheritance clause
    end
  end
  
  -- insert type stubs for bundle definitions, for the purpose of arity kindchecking
  for _,def in ipairs(defs) do
    if def.tag == "Typedef" then
      local name = def[1]
      local typename = current_modname(env) .. name
      local ti = tlst.typeinfo_Structural(Any)
      tlst.set_typeinfo(env, typename, ti, env.scope > 1)
      tlst.set_typealias(env, name, typename)
    elseif def.tag == "Class" or def.tag == "Interface" then
      local name = def[1]
      local tparams = def.tag == "Class" and def[5] or def[2]
      local ti = tlst.typeinfo_Nominal(name, Any, tparams, true)
      local typename = current_modname(env) .. name[1]
      name.global_name = typename
      tlst.set_typeinfo(env, typename, ti, env.scope > 1)
      tlst.set_typealias(env, name[1], typename)
    end
  end
  
  --arity kindcheck the definitions of each type defined in the bundle
  for _,def in ipairs(defs) do
    if def.tag == "Typedef" then
      local t = def[2]
      if not kindcheck_arity(env, t) then
        def[2] = Any
      end
    elseif def.tag == "Class" or def.tag == "Interface" then
      do tlst.begin_scope(env) -- type parameters for the class definition.
      local elems = def[3] 
      local tpars = (def.tag == "Class" and def[5]) or (def.tag == "Interface" and def[2])
      set_tpars(env, tpars)
      kindcheck_arity_class_elems(env, elems)
      tlst.end_scope(env) end
    end
  end
  
  --add reflexive nominal edges and nominal edges for each inheritance clause in the bundle
  for _,def in ipairs(defs) do
    if def.tag == "Class" then
      local name, tsuper = def[1], def[4]
      local typename = current_modname(env) .. def[1][1]
      --tlst.add_nominal_edge(env, typename, typename, , tltype.substitutes, env.scope > 1)
      if tsuper ~= "NoParent" then
        tlst.add_nominal_edge(env, typename, tsuper[1], tsuper[2], tltype.substitutes, env.scope > 1)
      end
    end
  end
  
  -- replace bundle stubs with full type definitions, so that we can perform bound kindchecking
  -- and method covariance checking
  for _,def in ipairs(defs) do
    if def.tag == "Typedef" then
      local name,t = def[1],def[2]
      local typename = current_modname(env) .. name
      local ti = tlst.typeinfo_Structural(t)
      tlst.set_typeinfo(env, typename, ti, env.scope > 1)
    elseif def.tag == "Class" then
      local name, tparams = def[1], def[5]
      local typealias = name[1]
      local typename = current_modname(env) .. typealias      
      local t_instance, t_class, instance_members, superclass_members = get_class_types(env, def)
      local ti = tlst.typeinfo_Nominal(name, t_instance, tparams, true)
      tlst.set_typeinfo(env, typename, ti, env.scope > 1)
      tlst.set_classtype(env, typename, t_class, env.scope > 1)
    elseif def.tag == "Interface" then
      local name, tparams = def[1], def[2]
      local t_interface = get_interface_type(env, def)
      local typealias = name[1]
      local typename = current_modname(env) .. typealias      
      local ti = tlst.typeinfo_Nominal(name, t_interface, tparams, true)
      tlst.set_typeinfo(env, typename, ti, env.scope > 1)
    end
  end
    
  --check method covariance: note that the types involved do NOT need to be well-bounded for this
  --the parameter and return types of non-covariant methods are converted to Any
  for _,def in ipairs(defs) do
    if def.tag == "Class" then
      local tsuper = def[4]
      if tsuper ~= "NoParent" then
        do tlst.begin_scope(env) --check class methods covariant
        --insert type parameters
        local elems, tpars = def[3], def[5]
        set_tpars(env, tpars)
        --we need super elems
        local superclass_members, superclass_methods, superclass_fields = get_superclass_fields(env, tsuper)
            
        for _,elem in ipairs(elems) do
          if elem.tag == "ConcreteClassMethod" then
            local name, parlist, rettype = elem[1], elem[2], elem[3]
            local super_method = superclass_methods[name]
            if super_method then
              local tmethod = make_tmethod(parlist,rettype)
              local tsuper_method = super_method[2]
              
              if not tltype.consistent_subtype(env, tmethod, tsuper_method) then
                local msg = "method type %s of %s is not a subtype of super class method type %s"
                msg = string.format(msg, tltype.tostring(tmethod), name, tltype.tostring(tsuper_method))
                typeerror(env, "inheritance", msg, elem.pos)
                for i,par in ipairs(parlist) do
                  parlist[i][2] = Any 
                end
                parlist[#parlist][2] = tltype.Vararg(Any)
                elem[3] = Any
              end
            end
          end
        end
        tlst.end_scope(env) end --check class methods covariant
      end 
    end
  end
  
  -- boundcheck type definition bodies
  for _,def in ipairs(defs) do
    if def.tag == "Class" then
      local name, elems, tsuper, tpars = def[1], def[3], def[4], def[5]
      do tlst.begin_scope(env) -- class type parameters
      set_tpars(env, tpars)
      for _,elem in ipairs(elems) do
        if elem.tag == "ConcreteClassMethod" then
          local parlist, tret = elem[2], elem[3]
          for i,par in ipairs(parlist) do
            env.variance = -1
            if not kindcheck(env, par[2]) then
              parlist[i][2] = Any
            end
          end
          env.variance = 1
          if not kindcheck(env, tret) then
            elem[3] = Any
          end
        end
      end
      tlst.end_scope(env) end -- class type parameters
    elseif def.tag == "Interface" then
      local name, tpars, elems = def[1], def[2], def[3]
      do tlst.begin_scope(env) -- class type parameters
      set_tpars(env, tpars)
      for _,elem in ipairs(elems) do
        if elem.tag == "AbstractClassMethod" then
          local name, ty = elem[1], elem[2]
          env.variance = 1
          local success = kindcheck(env, ty)
          assert(success) --method types must be functions, so kindchecking will not fail at the top level
        else
          assert(false, "interfaces can only contain abstract methods")
        end
      end
      tlst.end_scope(env) end -- class type parameters      
    elseif def.tag == "Typedef" then
      if not kindcheck(env, def[2]) then
        def[2] = Any
      end
    end
  end

  --add 
  --kindcheck the implements clauses of each class
  for _,def in ipairs(defs) do
    if def.tag == "Class" then
      do tlst.begin_scope(env)
      local interfaces, tpars = def[6], def[5]
      set_tpars(env, tpars)
      local new_interfaces = {}
      local msg = "classes can only implement class and interface types, but %s is not one"
      for i,t in ipairs(interfaces) do
        if kindcheck(env, t) then
          if t.tag == "TSymbol" then
            local ti = tlst.get_typeinfo(env, t[1])
            if ti.tag == "TINominal" then
              new_interfaces[#new_interfaces + 1] = t
            else
              msg = string.format(msg, tltype.tostring(t))
              typeerror(env, "inheritance", msg, t.pos)              
            end
          else
            msg = string.format(msg, tltype.tostring(t))
            typeerror(env, "inheritance", msg, t.pos)            
          end
        end
      end
      def[6] = new_interfaces
      tlst.end_scope(env) end -- class type parameters
    end
  end
  
  --insert nominal subtyping edges for implements clauses
  for _,def in ipairs(defs) do
    if def.tag == "Class" then
      local name, tpars, interfaces = def[1], def[5], def[6]
      local typename = current_modname(env) .. name[1]
      do tlst.begin_scope(env) --class type parameters
      set_tpars(env, tpars)
      local t_instance,_,_,_ = get_class_types(env, def)
      for i,t in ipairs(interfaces) do
        assert(t.tag == "TSymbol")
        local succ, explanation = tltype.consistent_subtype(env, t_instance, tltype.unfold(env, t))
        if succ then
          env.scope = env.scope - 1 --add nominal edge to the scope above this class's scope
          tlst.add_nominal_edge(env, typename, t[1], t[2], tltype.substitutes, env.scope > 1)
          env.scope = env.scope + 1
        else
          local par_tsymbols = {}
          for i,v in ipairs(tpars) do par_tsymbols[i] = tltype.Symbol(v[1]) end
          local def_tsymbol = tltype.Symbol(current_modname(env) .. name[1], par_tsymbols)
          local msg = "%s is not a subtype of %s"
          msg = string.format(msg, tltype.tostring(def_tsymbol), tltype.tostring(t))
          typeerror(env, "inheritance", msg .. "\n" .. explanation, t.pos)
        end
      end
      tlst.end_scope(env) end -- class type parameters
    end
  end
  
  -- typecheck all class code
  for _, def in ipairs(defs) do
    if def.tag == "Class" then
      local elems, tsuper, tpars = def[3], def[4], def[5]
      --insert class type parameters
      for _,tpar in ipairs(tpars) do
        local name, variance, tbound = tpar[1], tpar[2], tpar[3]
        tbound = (tbound == "NoBound") and Value or tbound
        local ti = tlst.typeinfo_Variable(tbound, variance)
        tlst.set_typeinfo(env, name, ti, true)
      end
      local t_instance, t_class, instance_members, superclass_members = get_class_types(env, def)
      check_class_code(env, elems, t_instance, instance_members, superclass_members, tsuper)
    end
  end
  
  return true
end

function check_id (env, exp)
  local name = exp[1]
  local l = tlst.get_local(env, name)
  local t = get_type(l)
  if tltype.isUnionlist(t) and l.i then
    set_type(env, exp, tltype.unionlist2union(t, l.i))
  else
    set_type(env, exp, t)
  end
end

function check_var (env, var, exp)
  local tag = var.tag
  if tag == "Id" then
    local name = var[1]
    local l = tlst.get_local(env, name)
    local t = get_type(l)
    if exp and exp.tag == "Id" and tltype.isTable(t) then t.open = nil end
    set_type(env, var, t)
  elseif tag == "Index" then
    local exp1, exp2 = var[1], var[2]
    check_exp(env, exp1)
    check_exp(env, exp2)
    local t1, t2 = tltype.first(get_type(exp1)), tltype.first(get_type(exp2))
    local msg = "attempt to index '%s' with '%s'"
    if tltype.isTable(t1) then
      if exp1.tag == "Id" and exp1[1] ~= "_ENV" then env.self = t1 end
      local field_type = tltype.getField(env, t2, t1)
      if not tltype.isNil(field_type) then
        set_type(env, var, field_type)
      else
        if t1.open or t1.unique then
          if exp then
            local t3 = tltype.general(get_type(exp))
            local t = tltype.general(t1)
            table.insert(t, tltype.Field(var.const, t2, t3))
            if tltype.subtype(env, t, t1) then
              table.insert(t1, tltype.Field(var.const, t2, t3))
            else
              msg = "could not include field '%s'"
              msg = string.format(msg, tltype.tostring(t2))
              typeerror(env, "open", msg, var.pos)
            end
            if t3.open then t3.open = nil end
            set_type(env, var, t3)
          else
            set_type(env, var, Nil)
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
          set_type(env, var, Nil)
        end
      end
    elseif tltype.isAny(t1) then
      set_type(env, var, Any)
      msg = string.format(msg, tltype.tostring(t1), tltype.tostring(t2))
      typeerror(env, "any", msg, var.pos)
    else
      set_type(env, var, Nil)
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
    set_type(env, exp, Nil)
  elseif tag == "Dots" then
    set_type(env, exp, tltype.Vararg(tlst.get_vararg(env)))
  elseif tag == "True" then
    set_type(env, exp, True)
  elseif tag == "False" then
    set_type(env, exp, False)
  elseif tag == "Number" then
    set_type(env, exp, tltype.Literal(exp[1]))
  elseif tag == "String" then
    set_type(env, exp, tltype.Literal(exp[1]))
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
  elseif tag == "SuperInvoke" then
    check_superinvoke(env, exp)
  elseif tag == "Id" then
    check_id(env, exp)
  elseif tag == "Index" then
    check_index(env, exp)
  elseif tag == "ClassValueLookup" then
    check_class_lookup(env, exp)
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
  elseif tag == "TypeBundle" then
    return check_typedefs(env,stm)
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
  set_type(env, lua_env, t)
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
