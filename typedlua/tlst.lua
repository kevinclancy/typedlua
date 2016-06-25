--[[
This module implements Typed Lua symbol table.
]]

local tlst = {}

-- new_env : (string, string, boolean) -> (env)
function tlst.new_env (subject, filename, strict)
  local env = {}
  env.subject = subject
  env.filename = filename
  env.parent = filename
  env.strict = strict
  env.integer = false
  env.messages = {}
  env.maxscope = 0
  env.tsuperclass = nil
  env.scope = 0
  env.fscope = 0
  env.loop = 0
  
  env.variance = 1
  
  env.nominal = {}
  env["function"] = {}
  
  --maps typenames to typeinfos
  --a typeinfo has a kind(field "kind"), a type(field "type"), a classifier (field "class") (userdata, nominal, or structural)
  env.types = {}
  
  --maps a typeinfo to a typeinfo,{type} pair. This should include all
  --nominal edges that have been transitively deduced in the global scope
  env.nominal_edges = {}

  env["loaded"] = {}
  return env
end

-- typeinfo constructors --

-- (string,type) -> (typeinfo)
function tlst.typeinfo_Userdata (name, t)
  return { tag = "TIUserdata", [1] = t }
end

-- (string,type) -> (typeinfo)
function tlst.typeinfo_Structural (name, t)
  return { tag = "TIStructural", [1] = t }
end

-- (string,type,kind) -> (typeinfo)
function tlst.typeinfo_Nominal (name, t, k)
  return { tag = "TINominal", [1] = t, [2] = k }
end

-- (type) -> (typeinfo)
function tlst.typeinfo_Variable (tbound, variance)
  return { tag = "TIVariable", [1] = tbound, [2] = variance }
end

function tlst.get_all_nominal_edges (env, tisource, edge_map_out)
  local scope = env.scope
  for s = scope, 1, -1 do
    if env[s].nominal_edges[tisource] then
      for _,edges in pairs(env[s].nominal_edges[tisource]) do
        for k,edge in ipairs(edges) do
          edge_map_out[k] = edge
        end
      end
    end
  end  
end

-- get_nominal_edges : (env,typeinfo,typeinfo,out {{type}}) -> ()
function tlst.get_nominal_edges (env, tisource, tidest, array_out)
  for i,_ in ipairs(array_out) do array_out[i] = nil end
  local scope = env.scope
  for s = scope, 1, -1 do
    if env[s].nominal_edges[tisource] then
      local edges = env[s].nominal_edges[tisource][tidest]
      if edges then
        for _,edge in ipairs(edges) do
          array_out[#array_out + 1] = edge
        end
      end
    end
  end  
end

-- (env, string, string, {type}, (type, string, type) -> (type)) -> ()
function tlst.add_nominal_edge (env, source, dest, instantiation, subst)
  local scope = env.scope
  
  local ti_source = tlst.get_typeinfo(env,source)
  local ti_dest = tlst.get_typeinfo(env,dest)
  assert(tisource ~= nil and ti_source.tag == "TINominal")
  assert(tidest ~= nil and ti_dest.tag == "TINominal")
  local ksource,kdest = ti_source.kind, ti_dest.kind
  local dest_param_names = kdest[1]
  assert(#instantiation == #dest_param_names)
  
  local dest_edges = {}
  tlst.get_all_nominal_edges(env, ti_dest, dest_edges)
  
  -- add direct edge
  if not env[s].nominal_edges[ti_source] then
    env[s].nominal_edges[ti_source] = {}
  end
  local src_edges = env[s].nominal_edges[ti_source]
  local src_dest_edges = src_edges[ti_dest]
  src_dest_edges[#src_dest_edges + 1] = { path = {ti_source}, inst = instantiation }
  
  -- add transitive edges
  for ti_parent,edge in ipairs(dest_edges) do
    local edges_to_parent = src_edges[ti_parent]
    
    --checking for cycles should be done externally
    assert(ti_parent ~= ti_source)
    
    local new_instantiation = {}
    for i=1,#dest_param_names do 
      local name = dest_param_names[i]
      local tinst = instantiation[i]
      
      local new_inst = {}
      for j,t in ipairs(edge.inst) do
        new_inst[j] = subst(t,name,tinst)
      end
      
      new_instantiation[j] = new_inst
    end
    
    local new_path = {tisource}
    for j,ti in ipairs(edge.path) do
      new_path[j+1] = ti
    end
    
    edges_to_parent[#edges_to_parent + 1] = { path = new_path, inst = new_instantiation }
  end
end

-- new_scope : () -> (senv)
local function new_scope ()
  local senv = {}
  senv["goto"] = {}
  senv["label"] = {}
  senv["local"] = {}
  senv["unused"] = {}
  senv.types = {}
  senv.nominal_edges = {}
  return senv
end

-- begin_scope : (env) -> ()
function tlst.begin_scope (env)
  local scope = env.scope
  if scope > 0 then
    for k, v in pairs(env[scope]["local"]) do
      if v["type"] and v["type"].open then
        v["type"].open = nil
        v["type"].reopen = true
      end
    end
  end
  env.scope = scope + 1
  env.maxscope = env.scope
  env[env.scope] = new_scope()
end

-- end_scope : (env) -> ()
function tlst.end_scope (env)
  env.scope = env.scope - 1
  local scope = env.scope
  if scope > 0 then
    for k, v in pairs(env[scope]["local"]) do
      if v.assigned and v.bkp then
        v["type"] = v.bkp
      end
      if v["type"] and v["type"].reopen then
        v["type"].reopen = nil
        v["type"].open = true
      end
    end
  end
end

-- set_pending_goto : (env, stm) -> ()
function tlst.set_pending_goto (env, stm)
  table.insert(env[env.scope]["goto"], stm)
end

-- get_pending_gotos : (env, number) -> ({number:stm})
function tlst.get_pending_gotos (env, scope)
  return env[scope]["goto"]
end

-- get_maxscope : (env) -> (number)
function tlst.get_maxscope (env)
  return env.maxscope
end

-- set_label : (env, string) -> (boolean)
function tlst.set_label (env, name)
  local scope = env.scope
  local label = env[scope]["label"][name]
  if not label then
    env[scope]["label"][name] = true
    return true
  else
    return false
  end
end

-- exist_label : (env, number, string) -> (boolean)
function tlst.exist_label (env, scope, name)
  for s = scope, 1, -1 do
    if env[s]["label"][name] then return true end
  end
  return false
end

-- set_local : (env, id) -> ()
function tlst.set_local (env, id)
  local scope = env.scope
  local local_name = id[1]
  env[scope]["local"][local_name] = id
  env[scope]["unused"][local_name] = id
end

-- set_tsuper : (env,type?) -> ()
function tlst.set_tsuper(env,t)
  env[env.scope].tsuper = t
end

-- get_tsuper : (env) -> (type?)
function tlst.get_tsuper(env)
  for s = scope, 1, -1 do
    local t = env[s].tsuper
    if t then return t end
  end
  return nil
end

-- get_local : (env, string) -> (id)
function tlst.get_local (env, local_name)
  local scope = env.scope
  for s = scope, 1, -1 do
    local l = env[s]["local"][local_name]
    if l then
      env[s]["unused"][local_name] = nil
      return l
    end
  end
  return nil
end

-- masking : (env, string) -> (id|nil)
function tlst.masking (env, local_name)
  local scope = env.scope
  return env[scope]["local"][local_name]
end

-- unused : (env) -> ({string:id})
function tlst.unused (env)
  local scope = env.scope
  return env[scope]["unused"]
end

-- set_typeinfo : (env,name,typeinfo,bool) -> ()
function tlst.set_typeinfo (env, name, ti, is_local)
  if is_local then
    local scope = env.scope
    env[scope].types[name] = ti
  else
    env.types[name] = ti
  end
end

-- get_typeinfo : (env,string) -> (typeinfo?)
function tlst.get_typeinfo (env, name)
  local scope = env.scope
  for s = scope, 1, -1 do
    local t = env[s].types[name]
    if t then return t end
  end
  return env.types[name]
end

-- new_fenv : () -> (fenv)
local function new_fenv ()
  local fenv = {}
  fenv["return_type"] = {}
  return fenv
end

-- begin_function : (env) -> ()
function tlst.begin_function (env)
  env.fscope = env.fscope + 1
  env["function"][env.fscope] = new_fenv()
end

-- end_function : (env) -> ()
function tlst.end_function (env)
  env.fscope = env.fscope - 1
end

-- set_vararg : (env, type) -> ()
function tlst.set_vararg (env, t)
  env["function"][env.fscope]["vararg"] = t
end

-- get_vararg : (env) -> (type?)
function tlst.get_vararg (env, t)
  return env["function"][env.fscope]["vararg"]
end

-- is_vararg : (env) -> (boolean)
function tlst.is_vararg (env)
  local t = tlst.get_vararg(env)
  if t then return true else return false end
end

-- set_in_constructor : (env) -> ()
function tlst.set_in_constructor(env)
  env["function"][env.fscope].in_constructor = true
end

-- get_in_constructor (env) -> (boolean)
function tlst.get_in_constructor(env)
  return env["function"][env.fscope].in_constructor
end


-- set_return_type : (env, type) -> ()
function tlst.set_return_type (env, t)
  table.insert(env["function"][env.fscope]["return_type"], t)
end

-- get_return_type : (env) -> ({type})
function tlst.get_return_type (env)
  return env["function"][env.fscope]["return_type"]
end

-- begin_loop : (env) -> ()
function tlst.begin_loop (env)
  env.loop = env.loop + 1
end

-- end_loop : (env) -> ()
function tlst.end_loop (env)
  env.loop = env.loop - 1
end

-- insideloop : (env) -> (boolean)
function tlst.insideloop (env)
  return env.loop > 0
end

return tlst
