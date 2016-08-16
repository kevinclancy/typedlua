--[[
This module implements Typed Lua symbol table.
]]

local tlst = {}

local tlutils = require "typedlua.tlutils"
local tlast = require "typedlua.tlast"
local tltype = require "typedlua.tltype"

-- new_globalenv 
function tlst.new_globalenv()
  local genv = {}
  genv.class_types = {}
  genv.types = {}
  --maps [typename1 .. str(i1)][typename2 .. str(i2)] to edge info,
  --as described in On Decidability of Nominal Subtyping with Variance, 
  --section 5.2, where i1 is the index of a parameter of typename1
  --and i2 is the index of a parameter of typename2
  genv.param_graph = {}
  genv.nominal_edges = {}
  genv.nominal_children = {}  
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
  env.variance = "Invariant"
  env.variance_barriers = { 1 }
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
function tlst.typeinfo_Nominal (name, t, tpars, is_shape)
  return { tag = "TINominal", name = name, is_shape = is_shape, [1] = t, [2] = tpars }
end

-- (type) -> (typeinfo)
function tlst.typeinfo_Variable (tbound, variance, name)
  return { tag = "TIVariable", [1] = tbound, [2] = variance, [3] = name }
end



-- appends all the children of the nominal type typename onto the end of
-- children_out
-- (env, string, {string}) -> ()
function tlst.get_nominal_children (env, typename, children_out)
  local scope = env.scope
  for s = scope, 1, -1 do
    if env[s].nominal_children[typename] then
      for _,descendant in pairs(env[s].nominal_children[typename]) do
        children_out[#children_out + 1] = descendant
      end
    end
  end  
  
  if env.genv.nominal_children[typename] then
    for _,descendant in pairs(env.genv.nominal_children[typename]) do
      children_out[#children_out + 1] = descendant
    end    
  end    
end

function tlst.get_param_successors(env, param_id)
  local scope = env.scope
  local successors = {}
  for s = scope, 1, -1 do
    local scope_successors = env[s].param_graph[param_id] 
    if scope_successors then
      for _,successor in ipairs(scope_successors) do
        successors[#successors + 1] = successor
      end
    end
  end  
  local global_successors = env.genv.param_graph[param_id]
  if global_successors and #global_successors > 0 then
    for _,successor in pairs(global_successors) do
      successors[#successors + 1] = successors
    end    
  end     
  return successors
end

-- returns an array of all of the nominal descendants of typename, inclusive
-- (env, string) -> ({string : boolean})
function tlst.get_nominal_descendants (env, typename)
  local visited_descendants = { [typename] = true }
  local to_visit = {}
  tlst.get_nominal_children(env, typename, to_visit)
  local i = 1
  while i <= #to_visit do
    local curr = to_visit[i]
    if not visited_descendants[curr] then
      visited_descendants[curr] = true
      tlst.get_nominal_children(env, curr, to_visit)
    end
    i = i + 1
  end
  return visited_descendants
end

function tlst.get_all_nominal_edges (env, source, edge_map_out)
  local scope = env.scope
  for s = scope, 1, -1 do
    if env[s].nominal_edges[source] then
      for k,edges in pairs(env[s].nominal_edges[source]) do
        edge_map_out[k] = edge_map_out[k] or {}
        for _,edge in ipairs(edges) do
          edge_map_out[k][#edge_map_out[k] + 1] = edge
        end
      end
    end
  end
  
  if env.genv.nominal_edges[source] then
    for k,edges in pairs(env.genv.nominal_edges[source]) do
      edge_map_out[k] = edge_map_out[k] or {}
      for _,edge in ipairs(edges) do
        edge_map_out[k][#edge_map_out[k] + 1] = edge
      end
    end    
  end
end

-- get_nominal_edges : (env,typeinfo,typeinfo,out {{type}}) -> ()
function tlst.get_nominal_edges (env, source, dest, array_out)
  local tisource = tlst.get_typeinfo(env, source)
  local tidest = tlst.get_typeinfo(env, dest)
  assert(tisource.tag == "TINominal" and tidest.tag == "TINominal")
  
  for i,_ in ipairs(array_out) do array_out[i] = nil end
  local scope = env.scope
  for s = scope, 1, -1 do
    if env[s].nominal_edges[source] then
      local edges = env[s].nominal_edges[source][dest]
      if edges then
        for _,edge in ipairs(edges) do
          array_out[#array_out + 1] = edge
        end
      end
    end
  end  
  
  if env.genv.nominal_edges[source] then
    local edges = env.genv.nominal_edges[source][dest]
    if edges then
      for _,edge in ipairs(edges) do
        array_out[#array_out + 1] = edge
      end
    end    
  end
end

-- insert a group of type variables into the environment
-- set_tpars : (env, {tpar}) -> ()
function tlst.set_tpars(env, tpars)
  for _,tpar in ipairs(tpars) do
    local name, variance, tbound = tpar[1], tpar[2], tpar[3]
    local ti = tlst.typeinfo_Variable(tbound, variance, name)
    tlst.set_typeinfo(env, name, ti, true)
    tlst.set_typealias(env, name, name)
  end  
end

local function nominal_edge_string(env, source, dest, instantiation)
  local ti_source = tlst.get_typeinfo(env,source)
  local ti_dest = tlst.get_typeinfo(env,dest)
  assert(ti_source ~= nil and ti_source.tag == "TINominal")
  assert(ti_dest ~= nil and ti_dest.tag == "TINominal")
  
  local ret = tlutils.abbreviate(source)
  local source_par_names = tlast.param_names(ti_source[2])
  ret = ret .. '<' .. table.concat(source_par_names, ',') .. '>'
  
  local instantiation_strings = {}
  for i,t in ipairs(instantiation) do
    instantiation_strings[#instantiation_strings + 1] = tltype.tostring(instantiation[i])
  end
  
  ret = ret .. ' <: ' .. tlutils.abbreviate(dest) 
  ret = ret .. '<' .. table.concat(instantiation_strings, ',') .. '>'

  return ret
end

-- adds all param graph edges (See On Decidability of Nominal Subtyping 
-- with Variance by Kennedy and Pierce, section 5.2) associated with the 
-- supplied nominal subtyping edge
--
-- returns an array of {src_param, dest_param, expansive} pairs for all edges added, where
-- src_param and dest_param are strings formatted as type_name@param_name, and
-- expansive is a boolean
local function add_param_edges (env, source, dest, instantiation, is_local)
  local senv = is_local and env[env.scope] or env.genv
  local ti_source = tlst.get_typeinfo(env,source)
  local ti_dest = tlst.get_typeinfo(env,dest)
  if ti_dest.is_shape then 
    return {} 
  end
  assert(ti_dest ~= nil and ti_dest.tag == "TINominal")
  assert(not ti_source.is_shape)
  assert(not ti_dest.is_shape)
  local edges_added = {}
  local src_par_names = tlast.param_names(ti_source[2])
  local dest_par_names = tlast.param_names(ti_dest[2])
  
  local edge_str = nominal_edge_string(env, source, dest, instantiation)
  
  tlst.begin_scope(env) --tpars
  tlst.set_tpars(env, ti_source[2])
  
  -- adding expansive edges for each variable occurrence in t
  local function traverse(dest_par_name, t, param_context)
    if t.tag == "TSymbol" then
      local ti = tlst.get_typeinfo(env, t[1])
      if ti.tag == "TIVariable" then
        local src_par_name = t[1]
        local src_par_id = source .. '@' .. src_par_name
        for i,dest_par_id in ipairs(param_context) do
          senv.param_graph[src_par_id] = senv.param_graph[src_par_id] or {} 
          local source_edges = senv.param_graph[src_par_id]
          source_edges[#source_edges + 1] = {
            from = src_par_id,
            to = dest_par_id,
            -- a description of the implements clause that created this edge
            edge_str = edge_str, 
            -- whether or not this edge is expansive
            expansive = (i ~= #param_context)
          }
          edges_added[#edges_added + 1] = { src_par_id, dest_par_id, false } 
        end
      end
      for i,s in ipairs(t[2]) do
        param_context[#param_context + 1] = t[1] .. '@' .. ti[2][i][1]
        traverse(dest_par_name, s, param_context)
        param_context[#param_context] = nil
      end
    end
  end
  
  local param_context = {}
  for i,tinst in ipairs(instantiation) do
    param_context[#param_context + 1] = dest .. '@' .. ti_dest[2][i][1]
    traverse(dest_par_names[i], tinst, param_context)
    param_context[#param_context] = nil
  end
  
  tlst.end_scope(env) 
  return edges_added
end

-- return true if adding all param graph edges from the implements 
-- clause (source, dest, instantiation) creates an expansive cycle
local function check_param_cycles (env, source, dest, instantiation)
  tlst.begin_scope(env)
  
  local senv = env[env.scope]
  local edges_added = add_param_edges(env, source, dest, instantiation, true)

  for _,edge in ipairs(edges_added) do
    local src_id, dest_id, expansive = edge[1], edge[2], edge[3]
    -- the set of all params that can be reached from dest 
    local dest_descendants = {}
    -- the set of all params that can be reached from dest via an expansive edge
    local dest_descendants_expansive = {}
    -- maps a param id to its parent edge in the dest param's dfs tree
    local dest_dfs_parent = {}
    local function traverse(expansive, param_id, parent_edge)
      if not expansive and dest_descendants[param_id] then
        return
      elseif expansive and dest_descendants_expansive[param_id] then
        return
      end
      dest_descendants[param_id] = true
      if expansive then
        dest_descendants_expansive[param_id] = true
      end
      dest_dfs_parent[param_id] = parent_edge      
      local edges = tlst.get_param_successors(env, param_id)
      for _,edge in ipairs(edges) do
        traverse(expansive or edge.expansive, edge.to, edge)
      end
    end
   
    traverse(expansive, dest_id, edge)
    
    if dest_descendants_expansive[src_id] then
      local ind = "  "
      local curr_node = src_id
      local param_edge_strings = {}
      repeat
        local edge_str = dest_dfs_parent[curr_node].edge_str
        local parent_node = dest_dfs_parent[curr_node].from
        param_edge_strings[#param_edge_strings + 1] = curr_node .. " -> " .. parent_node .. " from " .. dest_dfs_parent[curr_node].edge_str
        curr_node = parent_node
      until (curr_node == dest_id)
      
      local msg = "cannot add subtyping edge: expansive type parameter cycle has been detected"      
      for i=#param_edge_strings,1,-1 do
        msg = msg .. "\n" .. ind .. param_edge_strings[i]
      end
      tlst.end_scope(env)
      return false, msg
    end
  end
  
  tlst.end_scope(env)
  return true
end


-- adds edge and returns true if no cycles are detected. returns false, 
-- error message without adding edges otherwise
-- (env, string, string, {type}, (type, string, type) -> (type)) -> (boolean)
function tlst.add_nominal_edge (env, source, dest, instantiation, subst, is_local)  
  local ti_source = tlst.get_typeinfo(env,source)
  local ti_dest = tlst.get_typeinfo(env,dest)
  assert(ti_source ~= nil and ti_source.tag == "TINominal")
  assert(ti_dest ~= nil and ti_dest.tag == "TINominal")
  local source_params = ti_source[2]
  local dest_params = ti_dest[2]
  assert(#instantiation == #dest_params)
  local edge_str = nominal_edge_string(env, source, dest, instantiation)
  local dest_ancestors = {}
  tlst.get_all_nominal_edges(env, dest, dest_ancestors)
  local senv = is_local and env[env.scope] or env.genv
  local nominal_edges = senv.nominal_edges
  local source_descendants = tlst.get_nominal_descendants(env, source)
  
  --check for trivial cycles
  if source == dest then
    return false, "cannot introduce self edges to subtyping graph"
  end
  
  --check for non-trivial cycles
  for ancestor,edges in pairs(dest_ancestors) do
    if source_descendants[ancestor] then
      --edge would introduce a non-trivial cycle, report error and abort
      local dest_ancestor_path = edges[1].path
      
      local ancestor_src_edges = {}
      tlst.get_nominal_edges(env, ancestor, source, ancestor_src_edges)
      
      assert(#ancestor_src_edges > 0)
      local ancestor_src_path = ancestor_src_edges[1].path
      
      local loop_desc = ""
      local first = true
      for _,typename in ipairs(ancestor_src_path) do
        if first then
          loop_desc = loop_desc .. tlutils.abbreviate(typename)
        else
          loop_desc = loop_desc .. " -> " .. tlutils.abbreviate(typename)
        end
        first = false
      end
      for _,typename in ipairs(dest_ancestor_path) do
        if first then
          loop_desc = loop_desc .. tlutils.abbreviate(typename)
        else
          loop_desc = loop_desc .. " -> " .. tlutils.abbreviate(typename)
        end        
        first = false
      end
    
      local msg = "adding a subtyping edge from %s to %s would create the following cycle:\n"
      msg = msg .. loop_desc
      msg = string.format(msg, source, dest)
      return false, msg
    end
  end
  
  if not ti_dest.is_shape then
    local succ, msg = check_param_cycles(env, source, dest, instantiation)
    if not succ then
      return false, msg
    end
  end
  
  add_param_edges(env, source, dest, instantiation)
  
  local source_param_names = tlast.param_names(source_params)
  local dest_param_names = tlast.param_names(dest_params)
  
  for descendant,_ in pairs(source_descendants) do
    local desc_src_edges = {}
    tlst.get_nominal_edges(env, descendant, source, desc_src_edges)
    
    for ancestor,dest_ancestor_edges in pairs(dest_ancestors) do
      for _,desc_src_edge in ipairs(desc_src_edges) do
        for _,dest_ancestor_edge in ipairs(dest_ancestor_edges) do
          --create a new nominal edge going from  descendant to ancestor in two steps
          --1 - substitute descendant -> source instantiations into source -> dest instantiations
          local inst1 = {}
          for _,inst in ipairs(instantiation) do
            inst1[#inst1 + 1] = subst(inst, source_param_names, desc_src_edge.inst)
          end
          
          --2 - substitute resulting instantiations into dest -> ancestor instantiations
          local inst2 = {}
          for _, inst in ipairs(dest_ancestor_edge.inst) do
            inst2[#inst2 + 1] = subst(inst, dest_param_names, inst1)
          end
          
          local new_path = {}
          for j,typename in ipairs(desc_src_edge.path) do
            new_path[#new_path + 1] = typename
          end
          for j,typename in ipairs(dest_ancestor_edge.path) do
            new_path[#new_path + 1] = typename
          end
          
          senv.nominal_edges[descendant] = senv.nominal_edges[descendant] or {}
          senv.nominal_edges[descendant][ancestor] = senv.nominal_edges[descendant][ancestor] or {}
          local da_edges = senv.nominal_edges[descendant][ancestor]
          da_edges[#da_edges + 1] = { path = new_path, inst = inst2 }
        end
      end
    end
  end
  
  senv.nominal_children[dest] = senv.nominal_children[dest] or {}
  local dest_children = senv.nominal_children[dest]
  dest_children[#dest_children + 1] = source
    
  return true
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

function tlst.set_variance (env, variance)
  if not (variance == "Covariant" or variance == "Contravariant" or
         variance == "Invariant" or variance == "Bivariant") then
       assert(false)
  end
  assert(variance == "Covariant" or variance == "Contravariant" or
         variance == "Invariant" or variance == "Bivariant")
  
  env.variance = variance
end

function tlst.invert_variance (env)
  if env.variance == "Covariant" then
    env.variance = "Contravariant"
  elseif env.variance == "Contravariant" then
    env.variance = "Covariant"
  end
end

function tlst.is_contravariant (env)
  return env.variance == "Contravariant" or env.variance == "Bivariant"
end

function tlst.is_covariant (env)
  return env.variance == "Covariant" or env.variance == "Bivariant"
end

function tlst.is_bivariant (env)
  return env.variance == "Bivariant"
end

function tlst.push_variance_barrier(env)
  local barriers = env.variance_barriers
  barriers[#barriers + 1] = env.scope
end

function tlst.pop_variance_barrier(env)
  local barriers = env.variance_barriers
  barriers[#barriers] = nil
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
  --maps [typename1 .. str(i1)][typename2 .. str(i2)] to edge info,
  --as described in On Decidability of Nominal Subtyping with Variance, 
  --section 5.2, where i1 is the index of a parameter of typename1
  --and i2 is the index of a parameter of typename2
  senv.param_graph = {}
  --transpose of param_graph
  senv.param_graph_trans = {} 
  senv.nominal_edges = {}
  senv.nominal_children = {}
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

function tlst.add_reflexive_edge(env, name, tpars, is_local)
  local senv = is_local and env[env.scope] or env.genv
  local targs = {}
  for _,tpar in ipairs(tpars) do
    local parname = tpar[1]
    targs[#targs + 1] = { tag = "TSymbol", [1] = parname, [2] = {} }
  end
  senv.nominal_edges[name] = {}
  senv.nominal_edges[name][name] = { { path = {name}, inst = targs} }  
end

-- set_typeinfo : (env,name,typeinfo,bool) -> ()
function tlst.set_typeinfo (env, name, ti, is_local)
  local senv = is_local and env[env.scope] or env.genv
  senv.types[name] = ti
end

-- get_typeinfo : (env,string) -> (typeinfo?)
function tlst.get_typeinfo (env, name)
  local scope = env.scope
  local barriers = env.variance_barriers
  local top_barrier = barriers[#barriers]
  if top_barrier == nil then
    assert(false)
  end
  for s = scope, 1, -1 do
    local ti = env[s].types[name]
    if ti then 
      if ti.tag == "TIVariable" and s <= top_barrier then
          return tlst.typeinfo_Variable(ti[1], "Invariant", ti[3])
      else
        return ti
      end
    end
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
