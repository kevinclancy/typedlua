--[[
This module implements Typed Lua tltype.
]]

if not table.unpack then table.unpack = unpack end

local tltype = {}

local tlst = require "typedlua.tlst"

tltype.integer = false

-- literal types

-- Literal : (boolean|number|string) -> (type)
function tltype.Literal (l)
  return { tag = "TLiteral", [1] = l, name = tostring(l) }
end

function tltype.PLiteral (pos, l)
  local ret = tltype.Literal(l)
  ret.pos = pos
  return ret
end

-- False : () -> (type)
function tltype.False ()
  return tltype.Literal(false)
end

function tltype.PFalse (pos)
  return tltype.PLiteral(pos, false)
end

-- True : () -> (type)
function tltype.True ()
  return tltype.Literal(true)
end

function tltype.PTrue (pos)
  return tltype.PLiteral(pos, true)
end

-- Num : (number) -> (type)
function tltype.Num (n)
  return tltype.Literal(n)
end

function tltype.PNum (pos,n)
  return tltype.PLiteral(pos,n)
end


-- Str : (string) -> (type)
function tltype.Str (s)
  return tltype.Literal(s)
end

-- PStr : (number, string) -> (type)
function tltype.PStr (pos, s)
  return tltype.PLiteral(pos, s)
end

-- isLiteral : (type) -> (boolean)
function tltype.isLiteral (t)
  if not t then
    assert(false)
  end
  return t.tag == "TLiteral"
end

-- isFalse : (type) -> (boolean)
function tltype.isFalse (t)
  return tltype.isLiteral(t) and t[1] == false
end

-- isTrue : (type) -> (boolean)
function tltype.isTrue (t)
  return tltype.isLiteral(t) and t[1] == true
end

-- isNum : (type) -> (boolean)
function tltype.isNum (t)
  return tltype.isLiteral(t) and type(t[1]) == "number"
end

-- isFloat : (type) -> (boolean)
function tltype.isFloat (t)
  if _VERSION == "Lua 5.3" then
    return tltype.isLiteral(t) and math.type(t[1]) == "float"
  else
    return false
  end
end

-- isInt : (type) -> (boolean)
function tltype.isInt (t)
  if _VERSION == "Lua 5.3" then
    return tltype.isLiteral(t) and math.type(t[1]) == "integer"
  else
    return false
  end
end

-- isStr : (type) -> (boolean)
function tltype.isStr (t)
  return tltype.isLiteral(t) and type(t[1]) == "string"
end

-- base types

-- Base : ("boolean"|"number"|"string") -> (type)
function tltype.Base (s)
  return { tag = "TBase", [1] = s, name = s }
end

-- Base : (number, "boolean"|"number"|"string") -> (type)
function tltype.PBase (pos, s)
  local ret = tltype.Base(s)
  ret.pos = pos
  return ret
end

-- Boolean : () -> (type)
function tltype.Boolean ()
  return tltype.Base("boolean")
end

-- Boolean : (number) -> (type)
function tltype.PBoolean (pos)
  return tltype.PBase(pos,"boolean")
end

-- Number : () -> (type)
function tltype.Number ()
  return tltype.Base("number")
end

-- PNumber : (number) -> (type)
function tltype.PNumber (pos)
  return tltype.PBase(pos, "number")
end

-- String : () -> (type)
function tltype.String ()
  return tltype.Base("string")
end

-- PString : (number) -> (type)
function tltype.PString (pos)
  return tltype.PBase(pos, "string")
end

-- Integer : (boolean?) -> (type)
function tltype.Integer (i)
  if i then return tltype.Base("integer") else return tltype.Base("number") end
end

-- PInteger : (number, boolean?) -> (type)
function tltype.PInteger (pos, i)
  if i then return tltype.PBase(pos, "integer") else return tltype.PBase(pos, "number") end
end

-- isBase : (type) -> (boolean)
function tltype.isBase (t)
  return t.tag == "TBase"
end

-- isBoolean : (type) -> (boolean)
function tltype.isBoolean (t)
  return tltype.isBase(t) and t[1] == "boolean"
end

-- isNumber : (type) -> (boolean)
function tltype.isNumber (t)
  return tltype.isBase(t) and t[1] == "number"
end

-- isString : (type) -> (boolean)
function tltype.isString (t)
  return tltype.isBase(t) and t[1] == "string"
end

-- isInteger : (type) -> (boolean)
function tltype.isInteger (t)
  return tltype.isBase(t) and t[1] == "integer"
end

-- nil type

-- Nil : () -> (type)
function tltype.Nil ()
  return { tag = "TNil", name = "nil" }
end

-- PNil : () -> (type)
function tltype.PNil (pos)
  local ret = tltype.Nil()
  ret.pos = pos
  return ret
end


-- isNil : (type) -> (boolean)
function tltype.isNil (t)
  return t.tag == "TNil"
end

-- value type

-- Value : () -> (type)
function tltype.Value ()
  return { tag = "TValue", name = "value" }
end

-- PValue : (number) -> (type)
function tltype.PValue (pos)
  local ret = tltype.Value()
  ret.pos = pos
  return ret
end

-- isValue : (type) -> (boolean)
function tltype.isValue (t)
  return t.tag == "TValue"
end

-- dynamic type

-- Any : () -> (type)
function tltype.Any ()
  return { tag = "TAny", name = "any" }
end

-- PAny : (number) -> (type)
function tltype.PAny (pos)
  local ret = tltype.Any()
  ret.pos = pos
  return ret
end

-- isAny : (type) -> (boolean)
function tltype.isAny (t)
  return t.tag == "TAny"
end

-- self type

-- Self : () -> (type)
function tltype.Self ()
  return { tag = "TSelf", name = "self" }
end

-- PSelf : (number) -> (type)
function tltype.PSelf (pos)
  local ret = tltype.Self()
  ret.pos = pos
  return ret
end

-- isSelf : (type) -> (boolean)
function tltype.isSelf (t)
  return t.tag == "TSelf"
end

-- void type

-- Void : () -> (type)
function tltype.Void ()
  return { tag = "TVoid", name = "void" }
end

-- PVoid : (number) -> (type)
function tltype.PVoid (pos)
  local ret = tltype.Void()
  ret.pos = pos
  return ret
end

-- isVoid : (type) -> (boolean)
function tltype.isVoid (t)
  return t.tag == "TVoid"
end

-- union types

-- Union : (type*) -> (type)
function tltype.Union (...)
  local elements = { ... }
  if #elements == 1 then
    return elements[1]
  else
    return { tag = "TUnion", ... }
  end
end

-- PUnion : (number, type*) -> (type)
function tltype.PUnion (pos, ...)
  local ret = tltype.Union(...)
  ret.pos = pos
  return ret
end

function tltype.simplifyUnion (env, t)
  if t.tag == "TUnion" then
    local l1 = t
    -- remove unions of unions
    local l2 = {}
    for i = 1, #l1 do
      if tltype.isUnion(l1[i]) then
        for j = 1, #l1[i] do
          table.insert(l2, l1[i][j])
        end
      else
        table.insert(l2, l1[i])
      end
    end
    -- remove duplicated types
    local l3 = {}
    for i = 1, #l2 do
      local enter = true
      for j = i + 1, #l2 do
        if tltype.subtype(env, l2[i], l2[j]) and tltype.subtype(env, l2[j], l2[i]) then
          enter = false
          break
        end
      end
      if enter then table.insert(l3, l2[i]) end
    end
    -- simplify union, TODO: this seems broken, as (Any -> Any | Any -> Any) would incorrectly simplify to Any
    local ret = { tag = "TUnion", pos = t.pos }
    for i = 1, #l3 do
      local enter = true
      for j = 1, #l3 do
        if i ~= j and tltype.consistent_subtype(env, l3[i], l3[j]) then
          enter = false
          break
        end
      end
      if enter then table.insert(ret, l3[i]) end
    end
    if #ret == 0 then
      return tltype.PAny(t.pos)
    elseif #ret == 1 then
      return ret[1]
    else
      return ret
    end
  else
    return t
  end
end

-- isUnion : (type) -> (boolean)
function tltype.isUnion (t1)
  return t1.tag == "TUnion"
end

-- isUnionWith : (env,type,type) -> (boolean)
function tltype.isUnionWith(env,t1,t2)
  if t1.tag == "TUnion" then
    for k, v in ipairs(t1) do
      if tltype.subtype(env, t2, v) and tltype.subtype(env, v, t2) then
        return true
      end
    end
    return false
  else
    return false
  end
end

-- filterUnion : (type, type) -> (type)
function tltype.filterUnion (env, u, t)
  if tltype.isUnion(u) then
    local l = {}
    for k, v in ipairs(u) do
      if not (tltype.subtype(env, t, v) and tltype.subtype(env, v, t)) then
        table.insert(l, v)
      end
    end
    local ret = tltype.PUnion(u.pos, table.unpack(l))
    return tltype.simplifyUnion(env, ret)
  else
    return u
  end
end

-- UnionNil : (type, true?) -> (type)
function tltype.UnionNil (t, is_union_nil)
  if is_union_nil then
    return tltype.PUnion(t.pos, t, tltype.Nil())
  else
    return t
  end
end

-- PUnionNil : (number, type, true?) -> (type)
function tltype.PUnionNil (pos, t, is_union_nil)
  local ret = tltype.UnionNil (t, is_union_nil)
  ret.pos = pos
  return ret
end

-- vararg types

-- Vararg : (type) -> (type)
function tltype.Vararg (t)
  return { tag = "TVararg", [1] = t, name = t.name and t.name .. "*" }
end

-- PVararg : (number, type) -> (type)
function tltype.PVararg (pos, t)
  local ret = tltype.Vararg(t)
  ret.pos = pos
  return ret
end

-- isVararg : (type) -> (boolean)
function tltype.isVararg (t)
  return t.tag == "TVararg"
end

-- tuple types

-- Tuple : ({number:type}, true?) -> (type)
function tltype.Tuple (l, is_vararg)
  if is_vararg then
    l[#l] = tltype.Vararg(l[#l])
  end
  return { tag = "TTuple", table.unpack(l) }
end

-- PTuple : (pos, {number:type}, true?) -> (type)
function tltype.PTuple (pos, l, is_vararg)
  local ret = tltype.Tuple(l, is_vararg)
  ret.pos = pos
  return ret
end

-- inputTuple : (number, type?, boolean) -> (type)
function tltype.inputTuple (pos, t, strict)
  if not strict then
    if not t then
      return tltype.PTuple(pos, { tltype.Value() }, true)
    else
      if not tltype.isVararg(t[#t]) then
        table.insert(t, tltype.Vararg(tltype.Value()))
      end
      return t
    end
  else
    if not t then
      return tltype.Void()
    else
      return t
    end
  end
end

-- PinputTuple : (number, type?, boolean) -> (type)
function tltype.PinputTuple (pos, t, strict)
  local ret = tltype.inputTuple(t, strict)
  ret.pos = pos
  return ret
end

-- outputTuple : (number, type?, boolean) -> (type)
function tltype.outputTuple (t, strict)
  if not strict then
    if not t then
      return tltype.Tuple({ tltype.Nil() }, true)
    else
      if not tltype.isVararg(t[#t]) then
        table.insert(t, tltype.Vararg(tltype.Nil()))
      end
      return t
    end
  else
    if not t then
      return tltype.Void()
    else
      return t
    end
  end
end

-- PoutputTuple : (number, type?, boolean) -> (type)
function tltype.PoutputTuple (pos, t, strict)
  local ret = tltype.outputTuple(pos, t, strict)
  ret.pos = pos
  return ret
end



-- retType : (type, boolean) -> (type)
function tltype.retType (t, strict)
  return tltype.outputTuple(tltype.Tuple({ t }), strict)
end

-- PretType: (number, type, boolean) -> (type)
function tltype.PretType (pos, t, strict)
  local ret = tltype.retType(tltype.Tuple({ t }), strict)
  ret.pos = pos
  return ret
end

-- isTuple : (type) -> (boolean)
function tltype.isTuple (t)
  return t.tag == "TTuple"
end

-- union of tuple types

-- Unionlist : (type*) -> (type)
function tltype.Unionlist (...)
  local t = tltype.Union(...)
  if tltype.isUnion(t) then t.tag = "TUnionlist" end
  return t
end

-- PUnionlist : (number, type*) -> (type)
function tltype.PUnionlist (pos, ...)
  local ret = tltype.Unionlist(...)
  ret.pos = pos
  return ret
end

-- isUnionlist : (type) -> (boolean)
function tltype.isUnionlist (t)
  return t.tag == "TUnionlist"
end

-- UnionlistNil : (type, boolean?) -> (type)
function tltype.UnionlistNil (t, is_union_nil)
  if type(is_union_nil) == "boolean" then
    local u = tltype.Tuple({ tltype.Nil(), tltype.String() })
    return tltype.Unionlist(t, tltype.outputTuple(u, is_union_nil))
  else
    return t
  end
end

-- PUnionlistNil : (number, type, boolean?) -> (type)
function tltype.PUnionlistNil (pos, t, is_union_nil)
  local ret = tltype.UnionlistNil(t, is_union_nil)
  ret.pos = pos
  return ret
end

-- function types

-- Function : ({tpars}, type, type, true?) -> (type)
function tltype.Function (tparams, t1, t2, is_method)
  if is_method then
    if tltype.isVoid(t1) then
      t1 = tltype.Tuple({ tltype.Self() })
    else
      table.insert(t1, 1, tltype.Self())
    end
  end
  return { tag = "TFunction", [1] = t1, [2] = t2, [3] = tparams }
end

-- PFunction : (number, {tpars}, type, type, true?) -> (type)
function tltype.PFunction (pos, tparams, t1, t2, is_method)
  local ret = tltype.Function(tparams, t1, t2, is_method)
  ret.pos = pos
  return ret
end

function tltype.isFunction (t)
  return t.tag == "TFunction"
end

function tltype.isMethod (t)
  if tltype.isFunction(t) then
    for k, v in ipairs(t[1]) do
      if tltype.isSelf(v) then return true end
    end
    return false
  else
    return false
  end
end


-- table types

-- Field : (boolean, type, type) -> (field)
function tltype.Field (is_const, t1, t2)
  return { tag = "TField", const = is_const, [1] = t1, [2] = t2 }
end

-- isField : (field) -> (boolean)
function tltype.isField (f)
  return f.tag == "TField" and not f.const
end

-- isConstField : (field) -> (boolean)
function tltype.isConstField (f)
  return f.tag == "TField" and f.const
end

-- ArrayField : (boolean, type) -> (field)
function tltype.ArrayField (i, t)
  return tltype.Field(false, tltype.Integer(i), t)
end

-- Table : (field*) -> (type)
function tltype.Table (...)
  return { tag = "TTable", ... }
end

-- PTable : (number, field*) -> (type)
function tltype.PTable (pos, ...)
  local ret = tltype.Table(...)
  ret.pos = pos
  return ret
end

-- isTable : (type) -> (boolean)
function tltype.isTable (t)
  return t.tag == "TTable"
end

-- getField : (type, type) -> (type)
function tltype.getField (env, f, t)
  if tltype.isTable(t) then
    for k, v in ipairs(t) do
      if tltype.consistent_subtype(env, f, v[1]) then
        return v[2]
      end
    end
    return tltype.Nil()
  else
    return tltype.Nil()
  end
end

--rather than getting the value that corresponds to a field,
--get the table that represents the field
function tltype.getFieldTable(env, k, t)
  assert(tltype.isTable(t))
  for _, v in ipairs(t) do
    if tltype.consistent_subtype(env, k, v[1]) then
      return v
    end
  end
  return nil
end

-- fieldlist : ({ident}, type) -> (field*)
function tltype.fieldlist (idlist, t)
  local l = {}
  for k, v in ipairs(idlist) do
    table.insert(l, tltype.Field(v.const, tltype.Literal(v[1]), t))
  end
  return table.unpack(l)
end


-- type variables

-- Symbol: (string,{type}?) -> (type)
function tltype.Symbol (name,args)
  return { tag = "TSymbol", [1] = name, [2] = args or {} }
end

-- PSymbol: (number, string,{type}?) -> (type)
function tltype.PSymbol (pos, name, args)
  local ret = tltype.Symbol(name, args)
  ret.pos = pos
  return ret
end

-- isSymbol : (type) -> (boolean)
function tltype.isSymbol (t)
  return t.tag == "TSymbol"
end

-- checkTypeDec : (string, type) -> (true)?
function tltype.checkTypeDec (n, t)
  local predef_type = {
    ["boolean"] = true,
    ["number"] = true,
    ["string"] = true,
    ["value"] = true,
    ["any"] = true,
    ["self"] = true,
    ["const"] = true,
  }
  if not predef_type[n] then
    if tltype.isTable(t) then
      local namelist = {}
      for k, v in ipairs(t) do
        local f1, f2 = v[1], v[2]
        if tltype.isStr(f1) then
          local name = f1[1]
          if not namelist[name] then
            namelist[name] = true
          else
            local msg = "attempt to redeclare field '%s'"
            return nil, string.format(msg, name)
          end
        end
      end
      return true
    elseif tltype.isUnion(t) then
      return true
    else
      return nil, "attempt to name a type that is not a table"
    end
  else
    local msg = "attempt to redeclare type '%s'"
    return nil, string.format(msg, n)
  end
end


--type substitution

-- substitute : (type,{var},{type}) -> (type)
-- simultaneously substite the elements of x for the elements of s
function tltype.substitutes (t,x,s)
  if t.tag == "TLiteral" then
    return tltype.PLiteral(t.pos,t[1])
  elseif t.tag == "TBase" then
    return tltype.PBase(t.pos,t[1])
  elseif t.tag == "TNil" then
    return tltype.Nil(t.pos)
  elseif t.tag == "TValue" then
    return tltype.PValue(t.pos)
  elseif t.tag == "TAny" then
    return tltype.PAny(t.pos)
  elseif t.tag == "TSelf" then
    return tltype.PSelf(t.pos)
  elseif t.tag == "TVoid" then
    return tltype.PVoid(t.pos)
  elseif t.tag == "TUnion" then
    local res = {}
    for i,_ in ipairs(t) do
      res[i] = tltype.substitutes(t[i],x,s)
    end
    return tltype.PUnion(t.pos, table.unpack(res))
  elseif t.tag == "TVararg" then
    return tltype.PVararg(t.pos, tltype.substitutes(t[1],x,s))
  elseif t.tag == "TTuple" then
    local res = { tag = "TTuple", pos = t.pos }
    for i, tuple_element in ipairs(t) do
      res[i] = tltype.substitutes(t[i],x,s)
    end
    return res
  elseif t.tag == "TUnionList" then
    local res = {}
    for i,union_element in ipairs(t) do
      res[i] = tltype.substitutes(t[i],x,s)
    end
    return tltype.PUnionList(t.pos, res)  
  elseif t.tag == "TFunction" then
    local tin_res = tltype.substitutes(t[1],x,s)
    local tout_res = tltype.substitutes(t[2],x,s)
    
    --if type parameters mask substitution variable, return an
    --exact clone of t
    for i,tparam in pairs(t[3]) do
      local name = tparam[1]
      if name == x then
        return tltype.clone(t)
      end
    end
    
    local tparams_res = {}
    for i,tparam in pairs(t[3]) do
      table.insert(tparams_res, tltype.substitutes(tparam, x, s))
    end
    return tltype.PFunction(t.pos, tparams_res, tin_res, tout_res)
  elseif t.tag == "TField" then
    return { tag = "TField", const = t.const, [1] = tltype.substitutes(t[1],x,s), [2] = tltype.substitutes(t[2],x,s) }
  elseif t.tag == "TTable" then
    local res = {}
    for i,field in ipairs(t) do
      res[i] = tltype.substitutes(t[i],x,s)
    end
    return tltype.PTable(t.pos, table.unpack(res))      
  elseif t.tag == "TSymbol" then
    local name,args = t[1],t[2]
    for i=1,#x do
      if name == x[i] then
        assert(#args == 0)
        return s[i]
      end
    end
    local new_args = {}
    for i,arg in ipairs(args) do
      new_args[i] = tltype.substitutes(arg,x,s)
    end
    return tltype.PSymbol(t.pos, name, new_args)
  else
    assert("type substitution error: expected type, got " .. t.tag) 
  end
end

-- substitute : (type, string, type) -> (type)
function tltype.substitute (t,x,s)
  return tltype.substitutes(t, {x}, {s})
end


-- clone : (type) -> (type)
--return a type which is structurally identical to t, but totally
--disjoint from it on the heap
function tltype.clone(t)
  -- there should be no variables named '!'
  return tltype.substitute(t,"!",tltype.Void())
end

function tltype.unfold (env, t)
  if t == nil then
    assert(false)
  end
  if t.tag == "TSymbol" then
    local ti = tlst.get_typeinfo(env,t[1])
    if ti.tag == "TIUserdata" then
      return ti[1]
    elseif ti.tag == "TIStructural" then
      return ti[1]
    elseif ti.tag == "TIVariable" then
      return ti[1]
    elseif ti.tag == "TINominal" then
      local params = ti[2]
      local args = t[2]
      if #params == #args then
        local par_names = {}
        for i,par in ipairs(params) do par_names[i] = par[1] end
        return tltype.substitutes(ti[1], par_names, args)
      elseif (not args) and #params == 0 then
        return ti[1]
      else
        return tltype.Any()
      end
    end
  else
    return t
  end
end

local function check_recursive (t, name)
  if tltype.isLiteral(t) or
     tltype.isBase(t) or
     tltype.isNil(t) or
     tltype.isValue(t) or
     tltype.isAny(t) or
     tltype.isSelf(t) or
     tltype.isVoid(t) then
    return false
  elseif tltype.isUnion(t) or
         tltype.isUnionlist(t) or
         tltype.isTuple(t) then
    for k, v in ipairs(t) do
      if check_recursive(v, name) then
        return true
      end
    end
    return false
  elseif tltype.isFunction(t) then
    return check_recursive(t[1], name) or check_recursive(t[2], name)
  elseif tltype.isTable(t) then
    for k, v in ipairs(t) do
      if check_recursive(v[2], name) then
        return true
      end
    end
    return false
  elseif tltype.isSymbol(t) then
    return t[1] == name
  elseif tltype.isVararg(t) then
    return check_recursive(t[1], name)
  else
    return false
  end
end

-- checkRecursive : (type, string) -> (boolean)
function tltype.checkRecursive (t, name)
  return check_recursive(t, name)
end

-- subtyping and consistent-subtyping
local subtype

local function subtype_literal (assume, env, t1, t2)
  if tltype.isLiteral(t1) and tltype.isLiteral(t2) then
    return t1[1] == t2[1]
  elseif tltype.isLiteral(t1) and tltype.isBase(t2) then
    if tltype.isBoolean(t2) then
      return tltype.isFalse(t1) or tltype.isTrue(t1)
    elseif tltype.isNumber(t2) then
      return tltype.isNum(t1)
    elseif tltype.isString(t2) then
      return tltype.isStr(t1)
    elseif tltype.isInteger(t2) then
      return tltype.isInt(t1)
    else
      return false
    end
  else
    return false
  end
end

local function subtype_base (assume,env, t1, t2)
  if tltype.isBase(t1) and tltype.isBase(t2) then
    return t1[1] == t2[1] or (tltype.isInteger(t1) and tltype.isNumber(t2))
  else
    return false
  end
end

local function subtype_nil (assume, env, t1, t2)
  return tltype.isNil(t1) and tltype.isNil(t2)
end

local function subtype_top (assume, env, t1, t2)
  return tltype.isValue(t2)
end

local function subtype_any (assume, env, t1, t2, relation)
  if relation == "<:" then
    return tltype.isAny(t1) and tltype.isAny(t2)
  else
    return tltype.isAny(t1) or tltype.isAny(t2)
  end
end

local function subtype_self (assume, env, t1, t2)
  return tltype.isSelf(t1) and tltype.isSelf(t2)
end

local function subtype_union (assume, env, t1, t2, relation)
  if tltype.isUnion(t1) then
    for k, v in ipairs(t1) do
      if not subtype(assume, env, v, t2, relation) then
        return false
      end
    end
    return true
  elseif tltype.isUnion(t2) then
    for k, v in ipairs(t2) do
      if subtype(assume, env, t1, v, relation) then
        return true
      end
    end
    return false
  else
    return false
  end
end

local function subtype_function (assume, env, t1, t2, relation)
  if tltype.isFunction(t1) and tltype.isFunction(t2) then
    return subtype(assume, env, t2[1], t1[1], relation) and subtype(assume, env, t1[2], t2[2], relation)
  else
    return false
  end
end

local function subtype_field (assume, env, f1, f2, relation)
  if tltype.isField(f1) and tltype.isField(f2) then
    return subtype(assume, env, f2[1], f1[1], relation) and
           subtype(assume, env, f1[2], f2[2], relation) and
           subtype(assume, env, f2[2], f1[2], relation)
  elseif tltype.isField(f1) and tltype.isConstField(f2) then
    return subtype(assume, env, f2[1], f1[1], relation) and
           subtype(assume, env, f1[2], f2[2], relation)
  elseif tltype.isConstField(f1) and tltype.isConstField(f2) then
    return subtype(assume, env, f2[1], f1[1], relation) and
           subtype(assume, env, f1[2], f2[2], relation)
  else
    return false
  end
end

local function subtype_table (assume, env, t1, t2, relation)
  if tltype.isTable(t1) and tltype.isTable(t2) then
    if t1.unique then
      local m, n = #t1, #t2
      local k, l = 0, {}
      for i = 1, m do
        for j = 1, n do
          if subtype(assume, env, t1[i][1], t2[j][1], relation) then
            if subtype(assume, env, t1[i][2], t2[j][2], relation) then
              if not l[j] then
                k = k + 1
                l[j] = true
              end
            else
              return false
            end
          end
        end
      end
      if k == n then
        return true
      else
        for j = 1, n do
          if not l[j] then
            if not subtype(assume, env, tltype.Nil(), t2[j][2], relation) then
              return false
            end
          end
        end
      end
      return true
    elseif t1.open then
      local m, n = #t1, #t2
      local k, l = 0, {}
      for i = 1, m do
        for j = 1, n do
          if subtype(assume, env, t1[i][1], t2[j][1], relation) then
            if subtype_field(assume, env, t2[j], t1[i], relation) then
              if not l[j] then
                k = k + 1
                l[j] = true
              end
            else
              return false
            end
          end
        end
      end
      if k == n then
        return true
      else
        for j = 1, n do
          if not l[j] then
            if not subtype(assume, env, tltype.Nil(), t2[j][2], relation) then
              return false
            end
          end
        end
      end
      return true
    else
      local m, n = #t1, #t2
      for i = 1, n do
        local subtype = false
        for j = 1, m do
          if subtype_field(assume, env, t1[j], t2[i], relation) then
            subtype = true
            break
          end
        end
        if not subtype then return false end
      end
      return true
    end
  else
    return false
  end
end

local function subtype_symbol (assume, env, t1, t2, relation)
  local t1_symbol = tltype.isSymbol(t1)
  local t2_symbol = tltype.isSymbol(t2)
  
  local ti1 = t1_symbol and tlst.get_typeinfo(env,t1[1])
  local ti2 = t2_symbol and tlst.get_typeinfo(env,t2[1])
  
  if not ((not t1_symbol) or ti1) then
    assert(false)
  end
  
  -- handle bounded variables
  if t1_symbol and ti1.tag == "TIVariable" then
    if ti1 == ti2 then
      return true
    elseif ti1[1] ~= "NoBound" then
      return subtype(assume, env, ti1[1], t2, relation)  
    else
      return false
    end
  end
  if ti2 == nil then
    assert(false)
  end
  if t2_symbol and ti2.tag == "TIVariable" then
    return false
  end    
  
  --handle userdata
  if t1_symbol and ti1.tag == "TIUserdata" then
    return tltype.isSymbol(t2) and tlst.get_typeinfo(env,t2[1]) == ti1
  end 
  
  if t2_symbol and ti2.tag == "TIUserdata" then
    --we know t1 isn't a userdata, so the subtype relation does not hold
    return false
  end 
  
  --handle structural
  if t1_symbol and ti1.tag == "TIStructural" then
    return subtype(assume, env, ti1[1], t2, relation)
  end 
  
  if t2_symbol and ti2.tag == "TIStructural" then
    return subtype(assume, env, t1, ti2[1], relation)
  end 
  
  if t1_symbol and ti1.tag == "TINominal" and t2_symbol and ti2.tag == "TINominal" then
    local nominal_edges = {}
    tlst.get_nominal_edges(env,ti1,ti2,nominal_edges)
    
    local pars1 = ti1[2]
    local pars2 = ti2[2]

    for _,edge in ipairs(nominal_edges) do
      local path = edge.path
      local inst = edge.inst
      
      assert(#inst == #pars2)
      
      local par_names1 = {}
      for i,par in ipairs(pars1) do
        par_names1[i] = par[1]
      end
      
      local new_inst = {}
      for i,t in ipairs(inst) do
        new_inst[i] = inst[i]
        local args1 = t1[2]
        new_inst[i] = tltype.substitutes(new_inst[i],par_names1,args1)
      end
        
      local args2 = t2[2]
      local incompatible = false
      for i,arg in ipairs(args2) do
        local variance = pars2[i][2]
        if variance == "Covariant" then
          if not subtype(assume,env,new_inst[i],arg,relation) then
            incompatible = true
          end
        elseif variance == "Contravariant" then
          if not subtype(assume,env,arg,new_inst[i],relation) then
            incompatible = true
          end            
        elseif variance == "Invariant" then
          if not (subtype(assume,env,arg,new_inst[i],relation) and 
                  subtype(assume,env,new_inst[i],arg,relation)) then
            incompatible = true
          end
        end
      end
      if not incompatible then
        return true
      end
    end
    
    return false
  end

  if t1_symbol and ti1.tag == "TINominal" and #ti1[2] == 0 then
    --there is no type polymorphism, so we can allow equirecursive structural subtyping
    return subtype(assume, env, ti1[1], t2)
  end
  
  return false
end

local function subtype_tuple (assume, env, t1, t2, relation)
  if tltype.isTuple(t1) and tltype.isTuple(t2) then
    local len1, len2 = #t1, #t2
    if len1 < len2 then
      if not tltype.isVararg(t1[len1]) then return false end
      local i = 1
      while i < len1 do
        if not subtype(assume, env, t1[i], t2[i], relation) then
          return false
        end
        i = i + 1
      end
      local j = i
      while j <= len2 do
        if not subtype(assume, env, t1[i], t2[j], relation) then
          return false
        end
        j = j + 1
      end
      return true
    elseif len1 > len2 then
      if not tltype.isVararg(t2[len2]) then return false end
      local i = 1
      while i < len2 do
        if not subtype(assume, env, t1[i], t2[i], relation) then
          return false
        end
        i = i + 1
      end
      local j = i
      while j <= len1 do
        if not subtype(assume, env, t1[j], t2[i], relation) then
          return false
        end
        j = j + 1
      end
      return true
    else
      for k, v in ipairs(t1) do
        if not subtype(assume, env, t1[k], t2[k], relation) then
          return false
        end
      end
      return true
    end
  else
    return false
  end
end

function subtype (assume, env, t1, t2, relation)
  local key = tltype.tostring(t1) .. "@" .. tltype.tostring(t2)
  if assume[key] then return true end
  assume[key] = true
  if tltype.isVoid(t1) and tltype.isVoid(t2) then
    return true
  elseif tltype.isUnionlist(t1) then
    for k, v in ipairs(t1) do
      if not subtype(assume, env, v, t2, relation) then
        return false
      end
    end
    return true
  elseif tltype.isUnionlist(t2) then
    for k, v in ipairs(t2) do
      if subtype(assume, env, t1, v, relation) then
        return true
      end
    end
    return false
  elseif tltype.isTuple(t1) and tltype.isTuple(t2) then
    return subtype_tuple(assume, env, t1, t2, relation)
  elseif tltype.isTuple(t1) and not tltype.isTuple(t2) then
    return false
  elseif not tltype.isTuple(t1) and tltype.isTuple(t2) then
    return false
  elseif tltype.isVararg(t1) and tltype.isVararg(t2) then
    local t1_nil = tltype.Union(t1[1], tltype.Nil())
    local t2_nil = tltype.Union(t2[1], tltype.Nil())
    return subtype(assume, env, t1_nil, t2_nil, relation)
  elseif tltype.isVararg(t1) and not tltype.isVararg(t2) then
    local t1_nil = tltype.Union(t1[1], tltype.Nil())
    return subtype(assume,env, t1_nil, t2, relation)
  elseif not tltype.isVararg(t1) and tltype.isVararg(t2) then
    local t2_nil = tltype.Union(t2[1], tltype.Nil())
    return subtype(assume,env, t1, t2_nil, relation)
  else
    return subtype_literal(assume, env, t1, t2) or
           subtype_base(assume, env, t1, t2) or
           subtype_nil(assume, env, t1, t2) or
           subtype_top(assume, env, t1, t2) or
           subtype_any(assume, env, t1, t2, relation) or
           subtype_self(assume, env, t1, t2) or
           subtype_union(assume, env, t1, t2, relation) or
           subtype_function(assume, env, t1, t2, relation) or
           subtype_table(assume, env, t1, t2, relation) or
           subtype_symbol(assume, env, t1, t2)
  end
end

function tltype.subtype (env, t1, t2)
  return subtype({}, env, t1, t2, "<:")
end

function tltype.consistent_subtype (env, t1, t2)
  return subtype({}, env, t1, t2, "<~")
end

function tltype.consistent (env, t1, t2)
  return tltype.consistent_subtype(env, t1, t2) and tltype.consistent_subtype(env, t2, t1)
end

-- most general type

function tltype.general (t)
  if tltype.isFalse(t) or tltype.isTrue(t) then
    return tltype.Boolean()
  elseif tltype.isInt(t) and tltype.integer then
    return tltype.Integer(true)
  elseif tltype.isNum(t) then
    return tltype.Number()
  elseif tltype.isStr(t) then
    return tltype.String()
  elseif tltype.isUnion(t) then
    local l = {}
    for k, v in ipairs(t) do
      table.insert(l, tltype.general(v))
    end
    return tltype.Union(table.unpack(l))
  elseif tltype.isFunction(t) then
    local tparams_gen = {}
    for i,tparam in ipairs(t[3]) do
      local pos,name,variance,bound = tparam.pos, tparam[1], tparam[2], tparam[3]
      table.insert(tparams_gen, tlast.tparam(pos,name,variance,tltype.general(bound)))
    end
    return tltype.Function(tparams_gen, tltype.general(t[1]), tltype.general(t[2]))
  elseif tltype.isTable(t) then
    local l = {}
    for k, v in ipairs(t) do
      table.insert(l, tltype.Field(v.const, v[1], tltype.general(v[2])))
    end
    local n = tltype.Table(table.unpack(l))
    n.unique = t.unique
    n.open = t.open
    return n
  elseif tltype.isTuple(t) then
    local l = {}
    for k, v in ipairs(t) do
      table.insert(l, tltype.general(v))
    end
    return tltype.Tuple(l)
  elseif tltype.isUnionlist(t) then
    local l = {}
    for k, v in ipairs(t) do
      table.insert(l, tltype.general(v))
    end
    return tltype.Unionlist(table.unpack(l))
  elseif tltype.isVararg(t) then
    return tltype.Vararg(tltype.general(t[1]))
  else
    return t
  end
end

-- first level type

local function resize_tuple (t, n)
  local tuple = { tag = "TTuple", pos = t.pos }
  local vararg = t[#t][1]
  for i = 1, #t - 1 do
    tuple[i] = t[i]
  end
  for i = #t, n - 1 do
    if tltype.isNil(vararg) then
      tuple[i] = vararg
    else
      tuple[i] = tltype.Union(vararg, Nil)
    end
  end
  tuple[n] = tltype.Vararg(vararg)
  return tuple
end

function tltype.unionlist2tuple (t)
  local max = 1
  for i = 1, #t do
    if #t[i] > max then max = #t[i] end
  end
  local u = {}
  for i = 1, #t do
    if #t[i] < max then
      u[i] = resize_tuple(t[i], max)
    else
      u[i] = t[i]
    end
  end
  local l = {}
  for i = 1, #u do
    for j = 1, #u[i] do
      if not l[j] then l[j] = {} end
      table.insert(l[j], u[i][j])
    end
  end
  local n = { tag = "TTuple", pos = t.pos }
  for i = 1, #l do
    n[i] = tltype.Union(table.unpack(l[i]))
  end
  if not tltype.isVararg(n[#n]) then
    n[#n + 1] = tltype.Vararg(tltype.Nil())
  end
  return n
end

function tltype.unionlist2union (t, i)
  local l = {}
  for k, v in ipairs(t) do
    l[#l + 1] = v[i]
  end
  return tltype.PUnion(t.pos, table.unpack(l))
end

function tltype.first (t)
  if tltype.isTuple(t) then
    return tltype.first(t[1])
  elseif tltype.isUnionlist(t) then
    local l = {}
    for k, v in ipairs(t) do
      table.insert(l, tltype.first(v))
    end
    return tltype.Union(table.unpack(l))
  elseif tltype.isVararg(t) then
    return tltype.Union(t[1], tltype.Nil())
  else
    return t
  end
end

-- tostring

-- type2str (type) -> (string)
local function type2str (t, n)
  n = n or 0
  if n > 0 and t.name then
    return t.name
  elseif tltype.isLiteral(t) then
    return tostring(t[1])
  elseif tltype.isBase(t) then
    return t[1]
  elseif tltype.isNil(t) then
    return "nil"
  elseif tltype.isValue(t) then
    return "value"
  elseif tltype.isAny(t) then
    return "any"
  elseif tltype.isSelf(t) then
    return "self"
  elseif tltype.isUnion(t) or
         tltype.isUnionlist(t) then
    local l = {}
    for k, v in ipairs(t) do
      l[k] = type2str(v, n-1)
    end
    return "(" .. table.concat(l, " | ") .. ")"
  elseif tltype.isFunction(t) then
    return type2str(t[1], n-1) .. " -> " .. type2str(t[2], n-1)
  elseif tltype.isTable(t) then
    --if t.interface then return t.interface end
    local l = {}
    for k, v in ipairs(t) do
      if not v.missing then
        l[k] = type2str(v[1], n-1) .. ":" .. type2str(v[2], n-1)
        if tltype.isConstField(v) then
          l[k] = "const " .. l[k]
        end
      end
    end
    return "{" .. table.concat(l, ", ") .. "}"
  elseif tltype.isSymbol(t) then
    local ret = t[1]
    local targs = t[2]
    if #targs > 0 then
      ret = ret .. '<'
      ret = ret .. tltype.tostring(targs[1])
      for i=2,#targs do
        ret = ret .. ", " .. tltype.tostring(targs[i])
      end
      ret = ret .. '>'
    end
    return ret
  elseif tltype.isVoid(t) then
    return "(void)"
  elseif tltype.isTuple(t) then
    local l = {}
    for k, v in ipairs(t) do
      l[k] = type2str(v, n-1)
    end
    return "(" .. table.concat(l, ", ") .. ")"
  elseif tltype.isVararg(t) then
    return type2str(t[1], n-1) .. "*"
  else
    error("trying to convert type to string but got " .. t.tag)
  end
end

-- tostring : (type) -> (string)
function tltype.tostring (t, n)
  return type2str(t, n)
end

return tltype
