--[[
This module implements subtyping and type unfolding for Typed Lua.
]]

local tlsubtype = {}

local tltype = require "typedlua.tltype"
local tlst = require "typedlua.tlst"
local tlutils = require "typedlua.tlutils"

local subtype

local function unfold_aux (memo, env, t)
  local s = tltype.tostring(t)
  if memo[s] then return tltype.Any() end
  memo[s] = true
  if t.tag == "TSymbol" then
    local ti = tlst.get_typeinfo(env,t[1])
    if ti.tag == "TIUserdata" then
      return unfold_aux(memo, env, ti[1])
    elseif ti.tag == "TIStructural" then
      return unfold_aux(memo, env, ti[1])
    elseif ti.tag == "TIVariable" then
      return unfold_aux(memo, env, ti[1])
    elseif ti.tag == "TINominal" then
      local params = ti[2]
      local args = t[2]
      if #params == #args then
        local par_names = {}
        for i,par in ipairs(params) do par_names[i] = par[1] end
        local sub = tltype.substitutes(ti[1], par_names, args)
        return unfold_aux(memo, env, sub)
      elseif (not args) and #params == 0 then
        return unfold_aux(memo, env, ti[1])
      else
        return tltype.Any()
      end
    end
  else
    return t
  end
end

function tlsubtype.unfold (env, t)
  return unfold_aux({}, env, t)
end

local function subtype_literal (assume, env, t1, t2)
  if tltype.isLiteral(t1) and tltype.isLiteral(t2) and (t1[1] == t2[1]) then
    return true
  elseif tltype.isLiteral(t1) and tltype.isBase(t2) then
    if tltype.isBoolean(t2) and (tltype.isFalse(t1) or tltype.isTrue(t1)) then
      return true
    elseif tltype.isNumber(t2) and tltype.isNum(t1) then
      return true
    elseif tltype.isString(t2) and tltype.isStr(t1) then
      return true
    elseif tltype.isInteger(t2) and tltype.isInt(t1) then
      return true
    else
      return false, string.format("%s is not a subtype of %s", tltype.tostring(t1), tltype.tostring(t2))
    end
  else
    return false, string.format("%s is not a subtype of %s", tltype.tostring(t1), tltype.tostring(t2))
  end
end

local function subtype_base (assume,env, t1, t2)
  assert(tltype.isBase(t1) and tltype.isBase(t2))
  if t1[1] == t2[1] or (tltype.isInteger(t1) and tltype.isNumber(t2)) then
    return true
  else
    return false, string.format("%s is not a subtype of %s", tltype.tostring(t1), tltype.tostring(t2))
  end
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

local function subtype_union (assume, env, t1, t1_str, t2, t2_str, relation)
  if tltype.isUnion(t1) then
    for k, v in ipairs(t1) do
      local succ, msg = subtype(assume, env, v, t2, relation) 
      if not succ then
        return false, string.format("\n%s is not a subtype of %s", t1_str, t2_str) .. msg 
      end
    end
    return true
  elseif tltype.isUnion(t2) then
    local msgs = ""
    for k, v in ipairs(t2) do
      local succ, msg = subtype(assume, env, t1, v, relation)
      if succ then
        return true
      else
        msgs = msgs .. "\n " .. msg
      end
    end
    return false, string.format("%s is not a subtype of any element of %s", t1_str, t2_str) .. "\n" .. msgs
  else
    error("expected t1 or t2 to be a union")
  end
end

local function subtype_function (assume, env, t1, t1_str, t2, t2_str, relation)
  if tltype.isFunction(t1) and tltype.isFunction(t2) then
    local succ1, msg1 = subtype(assume, env, t2[1], t1[1], relation)
    if not succ1 then
      local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
      return false, problem .. "\n" .. msg1
    end
    local succ2, msg2 = subtype(assume, env, t1[2], t2[2], relation) 
    if not succ2 then
      local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
      return false, problem .. "\n" .. msg2
    end
    return true
  else
    return false, string.format("%s is not a subtype of %s", t1_str, t2_str)
  end
end

local function subtype_field (assume, env, f1, f2, relation)
  if tltype.isField(f1) and tltype.isField(f2) then
    local succ, explanation = subtype(assume, env, f2[1], f1[1], relation)
    if not succ then
      local problem = "%s is not a subtype of %s"
      local f1_str, f2_str = tltype.tostring(f1), tltype.tostring(f2)
      problem = string.format(problem, f1_str, f2_str)
      return false, problem .. "\n" .. explanation
    end
    
    succ, explanation = subtype(assume, env, f1[2], f2[2], relation)
    if not succ then
      local problem = "%s is not a subtype of %s"
      local f1_str, f2_str = tltype.tostring(f1), tltype.tostring(f2)
      problem = string.format(problem, f1_str, f2_str)
      return false, problem .. "\n" .. explanation
    end
    
    succ, explanation = subtype(assume, env, f2[2], f1[2], relation)
    if not succ then
      local problem = "%s is not a subtype of %s"
      local f1_str, f2_str = tltype.tostring(f1), tltype.tostring(f2)
      problem = string.format(problem, f1_str, f2_str)
      return false, problem .. "\n" .. explanation      
    end
    
    return true
  elseif tltype.isField(f1) and tltype.isConstField(f2) then
    local succ, explanation = subtype(assume, env, f2[1], f1[1], relation)
    if not succ then
      local problem = "%s is not a subtype of %s"
      local f1_str, f2_str = tltype.tostring(f1), tltype.tostring(f2)
      problem = string.format(problem, f1_str, f2_str)
      return false, problem .. "\n" .. explanation
    end
    
    succ, explanation = subtype(assume, env, f1[2], f2[2], relation)
    if not succ then
      local problem = "%s is not a subtype of %s"
      local f1_str, f2_str = tltype.tostring(f1), tltype.tostring(f2)
      problem = string.format(problem, f1_str, f2_str)
      return false, problem .. "\n" .. explanation
    end
    
    return true
  elseif tltype.isConstField(f1) and tltype.isConstField(f2) then
    local succ, explanation = subtype(assume, env, f2[1], f1[1], relation)
    if not succ then
      local problem = "%s is not a subtype of %s"
      local f1_str, f2_str = tltype.tostring(f1), tltype.tostring(f2)
      problem = string.format(problem, f1_str, f2_str)
      return false, problem .. "\n" .. explanation
    end
    
    succ, explanation = subtype(assume, env, f1[2], f2[2], relation)
    if not succ then
      local problem = "%s is not a subtype of %s"
      local f1_str, f2_str = tltype.tostring(f1), tltype.tostring(f2)
      problem = string.format(problem, f1_str, f2_str)
      return false, problem .. "\n" .. explanation
    end
    
    return true
  else
    local problem = "%s is not a subtype of %s"
    local f1_str, f2_str = tltype.tostring(f1), tltype.tostring(f2)
    problem = string.format(problem, f1_str, f2_str)
    local explanation = "%s is const and %s is not"
    explanation = string.format(explanation, f1_str, f2_str)
    return false, problem .. "\n" .. explanation
  end
end

local function subtype_table (assume, env, t1, t1_str, t2, t2_str, relation)
  if tltype.isTable(t1) and tltype.isTable(t2) then
    if t1.unique then
      local m, n = #t1, #t2
      local k, l = 0, {}
      for i = 1, m do
        for j = 1, n do
          local s1, s2 = tltype.tostring(t1[i][1]), tltype.tostring(t2[j][1])
          if s1 == "1" and s2 == "2" then
            local a = 5
            a = 4
          end
          if t1[i][1] == 1 and t2[j][1] == 2 then
            local a = 5
            a = 4
          end
          
          if subtype(assume, env, t1[i][1], t2[j][1], relation) then
            local succ, explanation = subtype(assume, env, t1[i][2], t2[j][2], relation) 
            if succ then
              if not l[j] then
                k = k + 1
                l[j] = true
              end
            else
              local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
              local s1, s2 = tltype.tostring(t1[i][1]), tltype.tostring(t2[j][1])
              local s3, s4 = tltype.tostring(t1[i][2]), tltype.tostring(t2[j][2])
              local msg = "%s is a subtype of %s, but %s is not a subtype of %s"
              msg = string.format(msg, s1, s2, s3, s4)
              return false, problem .. "\n" .. msg .. "\n" .. explanation
            end
          end
        end
      end
      if k == n then
        return true
      else
        for j = 1, n do
          if not l[j] then
            local succ, explanation = subtype(assume, env, tltype.Nil(), t2[j][2], relation) 
            if not succ then
              local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
              local msg = "%s does not have a field matching key %s, and nil is not a subtype of %s"
              msg = string.format(msg, t1_str, tltype.tostring(t2[j][1]), tltype.tostring(t2[j][2]))
              return false, problem .. "\n" .. msg .. "\n" .. explanation
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
          local s1, s2 = tltype.tostring(t1[i][1]), tltype.tostring(t2[j][1])
          if s1 == "1" and s2 == "2" then
            local a = 5
            a = 4
          end
          if t1[i][1] == 1 and t2[j][1] == 2 then
            local a = 5
            a = 4
          end          
          if subtype(assume, env, t1[i][1], t2[j][1], relation) then
            local succ, explanation = subtype_field(assume, env, t2[j], t1[i], relation) 
            if not succ then
              if not l[j] then
                k = k + 1
                l[j] = true
              end
            else
              local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
              local s1, s2 = tltype.tostring(t1[i][1]), tltype.tostring(t2[j][1])
              local s3, s4 = tltype.tostring(t2[j]), tltype.tostring(t1[i])
              local msg = "%s is a subtype of %s, but %s is not a subtype of %s"
              msg = string.format(msg, s1, s2, s3, s4)
              return false, problem .. "\n" .. msg .. "\n" .. explanation              
            end
          end
        end
      end
      if k == n then
        return true
      else
        for j = 1, n do
          if not l[j] then
            local succ, explanation = subtype(assume, env, tltype.Nil(), t2[j][2], relation) 
            if not succ then
              local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
              local msg = "%s does not have a field matching key %s, and nil is not a subtype of %s"
              msg = string.format(msg, t1_str, tltype.tostring(t2[j][1]), tltype.tostring(t2[j][2]))
              return false, problem .. "\n" .. msg .. "\n" .. explanation
            end
          end
        end
      end
      return true
    else
      local m, n = #t1, #t2
      for i = 1, n do
        local subtype = false
        local msgs = ""
        for j = 1, m do
          local succ, explanation = subtype_field(assume, env, t1[j], t2[i], relation)
          if succ then
            subtype = true
            break
          else
            msgs = msgs .. "\n" .. explanation
          end
        end
        if not subtype then 
          local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
          local msg = "field %s is not a supertype of any field of %s"
          msg = string.format(msg, tltype.tostring(t2[i]), t1_str)
          return false, problem .. "\n" .. msg .. msgs
        end
      end
      return true
    end
  else
    local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
    return false, problem
  end
  assert(false)
end

local function subtype_symbol (assume, env, t1, t1_str, t2, t2_str, relation)
  local t1_symbol = tltype.isSymbol(t1)
  local t2_symbol = tltype.isSymbol(t2)
  
  local ti1 = t1_symbol and tlst.get_typeinfo(env,t1[1])
  local ti2 = t2_symbol and tlst.get_typeinfo(env,t2[1])
  
  local problem = "%s is not a subtype of %s"
  problem = string.format(problem, t1_str, t2_str)    
      
  -- handle bounded variables
  if t1_symbol and ti1.tag == "TIVariable" then
    if ti2 and ti2.tag == "TIVariable" and ti1[3] == ti2[3] then
      return true --if names are equal then return true
    elseif ti1[1] ~= "NoBound" then
      return subtype(assume, env, ti1[1], t2, relation)  
    else
      return false, problem
    end
  end
  
  if t2_symbol and ti2.tag == "TIVariable" then
    return false, problem
  end    
  
  --handle userdata
  if t1_symbol and ti1.tag == "TIUserdata" then
    if tltype.isSymbol(t2) and tlst.get_typeinfo(env,t2[1]) == ti1 then
      return true
    else
      return false, problem
    end
  end 
  
  if t2_symbol and ti2.tag == "TIUserdata" then
    --we know t1 isn't a userdata, so the subtype relation does not hold
    return false, problem
  end 
  
  --handle structural
  if t1_symbol and ti1.tag == "TIStructural" then
    local succ, explanation = subtype(assume, env, ti1[1], t2, relation)
    if succ then
      return true
    else
      return false, problem .. "\n" .. explanation
    end
  end 
  
  if t2_symbol and ti2.tag == "TIStructural" then
    local succ, explanation = subtype(assume, env, t1, ti2[1], relation)
    if succ then
      return true
    else
      return false, problem .. "\n" .. explanation
    end
  end 
  
  if t1_symbol and ti1.tag == "TINominal" and t2_symbol and ti2.tag == "TINominal" then
    local nominal_edges = {}
    tlst.get_nominal_edges(env,t1[1],t2[1],nominal_edges)
    
    local pars1 = ti1[2]
    local pars2 = ti2[2]

    local par_names1 = {}
    for i,par in ipairs(pars1) do
      par_names1[i] = par[1]
    end
        
    local edge_explanations = ""
    for _,edge in ipairs(nominal_edges) do
      local path = edge.path
      local inst = edge.inst
      
      assert(#inst == #pars2)
      
      local new_inst = {}
      for i,t in ipairs(inst) do
        new_inst[i] = inst[i]
        local args1 = t1[2]
        new_inst[i] = tltype.substitutes(new_inst[i],par_names1,args1)
      end
        
      local args2 = t2[2]
      local incompatible = false
      local targ_msg = ""
      for i,arg in ipairs(args2) do
        local variance = pars2[i][2]
        if variance == "Covariant" then
          local succ, explanation = subtype(assume,env,new_inst[i],arg,relation)
          if not succ then
            targ_msg = targ_msg or explanation
            incompatible = true
          end
        elseif variance == "Contravariant" then
          local succ, explanation = subtype(assume,env,arg,new_inst[i],relation)
          if not succ then
            targ_msg = targ_msg or explanation
            incompatible = true          
          end            
        elseif variance == "Invariant" then
          local succ, explanation = subtype(assume,env,new_inst[i],arg,relation)
          if not succ then
            targ_msg = targ_msg or explanation
            incompatible = true
          end
          succ, explanation = subtype(assume,env,arg,new_inst[i],relation)
          if not succ then
            targ_msg = targ_msg or explanation
            incompatible = true     
          end         
        end
      end
      if not incompatible then
        return true
      else
        local t2_inst_tsymbol = tltype.tostring(tltype.Symbol(t2[1], new_inst))
        local edge_explanation = "%s is not a subtype of %s"
        edge_explanation = string.format(edge_explanation, t2_inst_tsymbol, t2_str)
        edge_explanations = edge_explanations .. "\n" .. edge_explanation .. "\n" .. targ_msg
      end
    end
    
    local num_edges_str = "%d nominal subtyping edges considered"
    num_edges_str = string.format(num_edges_str,#nominal_edges)
    return false, problem .. "\n" .. num_edges_str .. edge_explanations
  end

  if t1_symbol and ti1.tag == "TINominal" and #ti1[2] == 0 then
    --there is no type polymorphism, so we can allow equirecursive structural subtyping
    local succ, explanation = subtype(assume, env, ti1[1], t2)
    if succ then
      return true
    else
      return false, problem .. "\n" .. explanation
    end
  end
  
  return false, problem
end

local function subtype_tuple (assume, env, t1, t1_str, t2, t2_str, relation)
  assert(tltype.isTuple(t1) and tltype.isTuple(t2))
  local len1, len2 = #t1, #t2
  if len1 < len2 then
    if not tltype.isVararg(t1[len1]) then 
      local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
      return false, problem .. "\n" .. string.format("%s is shorter than %s", t1_str, t2_str) 
    end
    local i = 1
    while i < len1 do
      local succ, explanation = subtype(assume, env, t1[i], t2[i], relation)
      if not succ then
        local s1,s2 = tltype.tostring(t1[i]), tltype.tostring(t2[i])
        local ord = tlutils.order_description(i)
        local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
        local component = string.format("%dth component %s is not a subtype of %s", ord, s1, s2)
        local msg = problem .. "\n" .. component .. "\n" .. explanation
        return false, msg
      end
      i = i + 1
    end
    local j = i
    while j <= len2 do
      local succ, explanation = subtype(assume, env, t1[i], t2[j], relation)
      if not succ then
        local s1,s2 = tltype.tostring(t1[i]), tltype.tostring(t2[i])
        local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
        local ord = tlutils.order_description(j)
        local component = string.format("\nvararg type %s is not a subtype of %s component %s", s1, ord, s2)
        local msg = problem .. component .. "\n" .. explanation
        return false, msg
      end
      j = j + 1
    end
    return true
  elseif len1 > len2 then
    if not tltype.isVararg(t2[len2]) then 
      local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
      return false, problem .. string.format("\n%s is longer than %s", t1_str, t2_str)
    end
    local i = 1
    while i < len2 do
      local succ, explanation = subtype(assume, env, t1[i], t2[i], relation)
      if not succ then
        local s1,s2 = tltype.tostring(t1[i]), tltype.tostring(t2[i])
        local ord = tlutils.order_description(i)
        local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
        local component = string.format("\n%dth component %s is not a subtype of %s", ord, s1, s2)
        local msg = problem .. component .. "\n" .. explanation        
        return false, msg
      end
      i = i + 1
    end
    local j = i
    while j <= len1 do
      local succ, explanation = subtype(assume, env, t1[j], t2[i], relation)
      if not succ then
        local s1,s2 = tltype.tostring(t1[i]), tltype.tostring(t2[i])
        local ord = tlutils.order_description(j)
        local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
        local component = string.format("\n%sth component %s is not a subtype of vararg type %s", ord, s1, s2)
        local msg = problem .. component .. "\n" .. explanation          
        return false, msg
      end
      j = j + 1
    end
    return true
  else
    for k, v in ipairs(t1) do
      local succ, explanation = subtype(assume, env, t1[k], t2[k], relation)  
      if not succ then
        local s1,s2 = tltype.tostring(t1[k]), tltype.tostring(t2[k])
        local ord = tlutils.order_description(k)
        local problem = string.format("%s is not a subtype of %s", t1_str, t2_str)
        local component = string.format("%s component", ord, s1, s2)
        local msg = problem .. "\n" .. component .. "\n" .. explanation        
        return false, msg        
      end
    end
    return true
  end
  assert(false)
end

function subtype (assume, env, t1, t2, relation, verbose)  
  if relation == "<:" and tltype.isAny(t1) and tltype.isAny(t2) then
    return true
  elseif relation == "<:" and (tltype.isAny(t1) or tltype.isAny(t2)) then
    local t1_str, t2_str = tltype.tostring(t1), tltype.tostring(t2)
    return false, string.format("%s is not a subtype of %s", t1_str, t2_str)
  elseif tltype.isAny(t1) or tltype.isAny(t2) then
    return true
  elseif tltype.isValue(t2) then
    return true
  elseif tltype.isVoid(t1) and tltype.isVoid(t2) then
    return true
  elseif (tltype.isLiteral(t1) and tltype.isLiteral(t2)) or 
         (tltype.isLiteral(t1) and tltype.isBase(t2)) or 
         (tltype.isBase(t1) and tltype.isLiteral(t2)) then
    return subtype_literal(assume, env, t1, t2)
  elseif tltype.isBase(t1) and tltype.isBase(t2) then
    return subtype_base(assume, env, t1, t2)
  elseif tltype.isNil(t1) and tltype.isNil(t2) then
    return true
  elseif tltype.isSelf(t1) and tltype.isSelf(t2) then
    return true
  end
  
  local t1_str, t2_str = tltype.tostring(t1), tltype.tostring(t2)
  local key =  t1_str .. "@" .. t2_str
  if assume[key] then return true end
  assume[key] = true
    
  if tltype.isUnionlist(t1) then
    for k, v in ipairs(t1) do
      local succ, msg = subtype(assume, env, v, t2, relation)
      if not succ then
        local v_str = tltype.tostring(v)
        assume[key] = nil
        return false, string.format("%s is not a subtype of %s", v_str, t2_str) .. "\n" .. msg
      end
    end
    assume[key] = nil
    return true
  elseif tltype.isUnionlist(t2) then
    local msgs = ""    
    for k, v in ipairs(t2) do
      local succ, msg = subtype(assume, env, t1, v, relation) 
      if succ then
        assume[key] = nil
        return true
      else
        msgs = msgs .. "\n " .. msg
      end
    end
    assume[key] = nil
    return false, string.format("%s is not a subtype of any element of %s\n", t1_str, t2_str) .. msgs
  elseif tltype.isUnion(t1) or tltype.isUnion(t2) then
    local ret,msg = subtype_union(assume, env, t1, t1_str, t2, t2_str, relation)
    assume[key] = nil
    return ret, msg
  elseif tltype.isTuple(t1) and tltype.isTuple(t2) then
    local ret,msg = subtype_tuple(assume, env, t1, t1_str, t2, t2_str, relation)
    assume[key] = nil
    return ret, msg
  elseif tltype.isVararg(t1) and tltype.isVararg(t2) then
    local t1_nil = tltype.Union(t1[1], tltype.Nil())
    local t2_nil = tltype.Union(t2[1], tltype.Nil())
    local ret,msg = subtype(assume, env, t1_nil, t2_nil, relation)
    assume[key] = nil
    return ret,msg
  elseif tltype.isVararg(t1) and not tltype.isVararg(t2) then
    local t1_nil = tltype.Union(t1[1], tltype.Nil())
    local ret,msg = subtype(assume,env, t1_nil, t2, relation)
    assume[key] = nil
    return ret, msg
  elseif not tltype.isVararg(t1) and tltype.isVararg(t2) then
    local t2_nil = tltype.Union(t2[1], tltype.Nil())
    local ret,msg = subtype(assume,env, t1, t2_nil, relation)
    assume[key] = nil
    return ret, msg
  elseif tltype.isFunction(t1) or tltype.isFunction(t2) then
    local ret,msg = subtype_function(assume, env, t1, t1_str, t2, t2_str, relation)
      assume[key] = nil
      return ret, msg
  elseif tltype.isSymbol(t1) or tltype.isSymbol(t2) then
    local ret,msg = subtype_symbol(assume, env, t1, t1_str, t2, t2_str, relation, verbose)      
    assume[key] = nil
    return ret, msg
  elseif tltype.isTable(t1) or tltype.isTable(t2) then
    local ret,msg = subtype_table(assume, env, t1, t1_str, t2, t2_str, relation)
    assume[key] = nil
    return ret,msg
  elseif tltype.isSelf(t1) or tltype.isSelf(t2) then
    assume[key] = nil
    return false, string.format("%s is not a subtype of %s", t1_str, t2_str)
  elseif tltype.isTuple(t1) and not tltype.isTuple(t2) then
    assume[key] = nil
    return false, string.format("%s is a tuple and %s is not", t1_str, t2_str)
  elseif not tltype.isTuple(t1) and tltype.isTuple(t2) then
    assume[key] = nil
    return false, string.format("%s is not a tuple, but %s is", t1_str, t2_str)
  else
    assume[key] = nil
    return false, string.format("%s is not a subtype of %s", t1_str, t2_str)
  end
end

function tlsubtype.subtype (env, t1, t2)
  return subtype({}, env, t1, t2, "<:")
end

function tlsubtype.consistent_subtype (env, t1, t2)
  return subtype({}, env, t1, t2, "<~")
end

function tlsubtype.consistent (env, t1, t2)
  return tlsubtype.consistent_subtype(env, t1, t2) and tlsubtype.consistent_subtype(env, t2, t1)
end


-- getField : (type, type) -> (type)
function tlsubtype.getField (env, f, t)
  if tltype.isTable(t) then
    for k, v in ipairs(t) do
      if tlsubtype.consistent_subtype(env, f, v[1]) then
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
function tlsubtype.getFieldTable(env, k, t)
  assert(tltype.isTable(t))
  for _, v in ipairs(t) do
    if tlsubtype.consistent_subtype(env, k, v[1]) then
      return v
    end
  end
  return nil
end

function tlsubtype.simplifyUnion (env, t)
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
        if tlsubtype.subtype(env, l2[i], l2[j]) and tlsubtype.subtype(env, l2[j], l2[i]) then
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
        if i ~= j and tlsubtype.consistent_subtype(env, l3[i], l3[j]) then
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

-- filterUnion : (type, type) -> (type)
function tlsubtype.filterUnion (env, u, t)
  if tltype.isUnion(u) then
    local l = {}
    for k, v in ipairs(u) do
      if not (tlsubtype.subtype(env, t, v) and tlsubtype.subtype(env, v, t)) then
        table.insert(l, v)
      end
    end
    local ret = tltype.PUnion(u.pos, table.unpack(l))
    return tlsubtype.simplifyUnion(env, ret)
  else
    return u
  end
end



return tlsubtype