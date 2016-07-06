--[[
This module implements Typed Lua symbol table.
]]

local tlst = {}

-- new_globalenv 
function tlst.new_globalenv()
  local genv = {}
  genv.nominal = {}
  genv.class_types = {}
  genv.types = {}
  genv.nominal_edges = {}
  genv.loaded = {}
  return genv
end

-- new_env : (string, string, boolean, genv?) -> (env)
function tlst.new_env (subject, filename, strict, genv)
  local env = {}
  env.subject = subject
  env.filename = filename
  env.parent = filename
  env.strict = strict
  env.integer = false
  env.messages = {}
  env.maxscope = 0
  env.scope = 0
  env.fscope = 0
  env.loop = 0
  env.variance = 1
  env["function"] = {}
  env.genv = genv or tlst.new_globalenv()
  return env
end

-- typeinfo constructors --

-- (string,type) -> (typeinfo)
function tlst.typeinfo_Userdata (t)
  return { tag = "TIUserdata", [1] = t }
end

-- (string,type) -> (typeinfo)
function tlst.typeinfo_Structural (t)
  return { tag = "TIStructural", [1] = t }
end

-- (string,type,{tpar}) -> (typeinfo)
function tlst.typeinfo_Nominal (name, t, tpars, is_class)
  return { tag = "TINominal", name = name, class = is_class, [1] = t, [2] = tpars }
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
  
  if env.genv.nominal_edges[tisource] then
    for _,edges in pairs(env.genv.nominal_edges[tisource]) do
      for k,edge in ipairs(edges) do
        edge_map_out[k] = edge
      end
    end    
  end
end

-- get_nominal_edges : (env,typeinfo,typeinfo,out {{type}}) -> ()
function tlst.get_nominal_edges (env, tisource, tidest, array_out)
  assert(tisource.tag == "TINominal" and tidest.tag == "TINominal")
  if tisource == tidest then
    local targs = {}
    local tpars = tisource[2]
    for _,tpar in ipairs(tpars) do
      local parname = tpar[1]
      targs[#targs + 1] = { tag = "TSymbol", [1] = parname, [2] = {} }
    end
    array_out[#array_out + 1] = { path = {}, inst = targs }
    return
  end
  
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
  
  if env.genv.nominal_edges[tisource] then
    local edges = env.genv.nominal_edges[tisource][tidest]
    if edges then
      for _,edge in ipairs(edges) do
        array_out[#array_out + 1] = edge
      end
    end    
  end
end

-- (env, string, string, {type}, (type, string, type) -> (type)) -> ()
function tlst.add_nominal_edge (env, source, dest, instantiation, subst, is_local)
  local s = env.scope
  
  local ti_source = tlst.get_typeinfo(env,source)
  local ti_dest = tlst.get_typeinfo(env,dest)
  assert(ti_source ~= nil and ti_source.tag == "TINominal")
  assert(ti_dest ~= nil and ti_dest.tag == "TINominal")
  local dest_params = ti_dest[2]
  assert(#instantiation == #dest_params)
  
  local dest_edges = {}
  tlst.get_all_nominal_edges(env, ti_dest, dest_edges)
  
  local nominal_edges = is_local and env[s].nominal_edges or env.genv.nominal_edges
  
  -- add direct edge
  nominal_edges[ti_source] = nominal_edges[ti_source] or {}
  local src_edges = nominal_edges[ti_source]
  src_edges[ti_dest] = src_edges[ti_dest] or {}
  local src_dest_edges = src_edges[ti_dest]
  src_dest_edges[#src_dest_edges + 1] = { path = {ti_source}, inst = instantiation }
  
  -- add transitive edges
  for ti_parent,edge in ipairs(dest_edges) do
    local edges_to_parent = src_edges[ti_dest]
    
    --checking for cycles should be done externally
    assert(ti_parent ~= ti_source)
    
    local new_instantiation = {}
    for i=1,#dest_params do 
      local name = dest_params[i][1]
      local tinst = instantiation[i]
      
      local new_inst = {}
      for j,t in ipairs(edge.inst) do
        new_inst[j] = subst(t,name,tinst)
      end
      
      new_instantiation[i] = new_inst
    end
    
    local new_path = {tisource}
    for j,ti in ipairs(edge.path) do
      new_path[j+1] = ti
    end
    
    edges_to_parent[#edges_to_parent + 1] = { path = new_path, inst = new_instantiation }
  end
end

-- get_classtype : (env, string) -> (type?)
function tlst.get_classtype (env, name)
  for s = env.scope, 1, -1 do
    local typename = env[s].class_types[name]
    if typename then return typename end
  end
  return env.genv.class_types[name]
end

--set_classtype : (env, string, type) -> ()
function tlst.set_classtype (env, name, t, is_local)
  assert(tlst.get_classtype(env, name) == nil)
  if is_local then
    env[env.scope].class_types[name] = t
  else
    env.genv.class_types[name] = t
  end
end

-- new_scope : () -> (senv)
local function new_scope ()
  local senv = {}
  senv["goto"] = {}
  senv["label"] = {}
  senv["local"] = {}
  senv["unused"] = {}
  --instance types
  senv.types = {}
  senv.tsuper = nil
  --class types
  senv.class_types = {}
  senv.type_aliases = {}
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

-- set_tsuper : (env,type|"None") -> ()
function tlst.set_tsuper(env,t)
  env[env.scope].tsuper = t
end

-- get_tsuper : (env) -> (type?)
function tlst.get_tsuper(env)
  for s = env.scope, 1, -1 do
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

-- set_typealias : (env, string, string) -> (string)
function tlst.set_typealias (env, alias, typename)
  env[env.scope].type_aliases[alias] = typename
end

-- get_typealias : (env, string) -> (string?)
function tlst.get_typealias (env, alias)
  for s = env.scope, 1, -1 do
    local typename = env[s].type_aliases[alias]
    if typename then return typename end
  end
  return nil
end

-- set_typeinfo : (env,name,typeinfo,bool) -> ()
function tlst.set_typeinfo (env, name, ti, is_local)
  if is_local then
    local scope = env.scope
    env[scope].types[name] = ti
  else
    env.genv.types[name] = ti
  end
end

-- get_typeinfo : (env,string) -> (typeinfo?)
function tlst.get_typeinfo (env, name)
  local scope = env.scope
  for s = scope, 1, -1 do
    local t = env[s].types[name]
    if t then return t end
  end
  return env.genv.types[name]
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
