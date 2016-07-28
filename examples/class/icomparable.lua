

 do if not (debug.getregistry()).classes then (debug.getregistry()).classes = {} end  (debug.getregistry()).classes['examples.class.icomparable.ComparablePair'] = { __premethods = {} }local class = (debug.getregistry()).classes['examples.class.icomparable.ComparablePair'] function class.new(x, y)local self = {} setmetatable(self, { __index = class.__premethods })











  self.x = x
  self.y = y
return self end function class.__premethods:leq(a)


  return self.x:leq(a.x) and self.y:leq(a.y)
end end



local function quicksort (x) 
  local function swap (i, j) 
    local temp = x[i]
    x[i] = x[j]
    x[j] = temp
  end

  local function partition (lo, hi) 
    local pivot = x[hi]



    local z = lo

    for i = 2, #(x) do 
      local xi = x[i]
      if xi then 
        if pivot then 
          if xi:leq(pivot) then 
            swap(i,z)
            z = z + 1
          end
        end
      else 
        error("array should be non-nil over its range")
      end
    end

    return z
  end

  local function sort (lo, hi) 
    if hi - lo <= 1 then 
      return nil
    end

    local p = partition(lo,hi)
    sort(lo,p - 1)
    sort(p + 1,hi)
  end

  sort(1,#(x))
end
 do if not (debug.getregistry()).classes then (debug.getregistry()).classes = {} end  (debug.getregistry()).classes['examples.class.icomparable.Factory'] = { __premethods = {} }local class = (debug.getregistry()).classes['examples.class.icomparable.Factory'] function class.new(cost)local self = {} setmetatable(self, { __index = class.__premethods })





  self.cost = cost
return self end function class.__premethods:leq(other)


  return self.cost <= other.cost
end end
 do if not (debug.getregistry()).classes then (debug.getregistry()).classes = {} end  (debug.getregistry()).classes['examples.class.icomparable.Office'] = { __premethods = {} }local class = (debug.getregistry()).classes['examples.class.icomparable.Office'] function class.new(cost)local self = {} setmetatable(self, { __index = class.__premethods })






  self.cost = cost
return self end function class.__premethods:leq(other)


  return self.cost <= other.cost
end end
 do if not (debug.getregistry()).classes then (debug.getregistry()).classes = {} end  (debug.getregistry()).classes['examples.class.icomparable.CompanyBuildings'] = { __premethods = {} }local class = (debug.getregistry()).classes['examples.class.icomparable.CompanyBuildings']local super = (debug.getregistry()).classes['examples.class.icomparable.ComparablePair'] for k,v in pairs(super.__premethods) do class.__premethods[k] = v end  function class.new(f, o)local self = super.new(f, o)  setmetatable(self, { __index = class.__premethods }) return self end end








local f =  (debug.getregistry()).classes['examples.class.icomparable.Factory']
local o =  (debug.getregistry()).classes['examples.class.icomparable.Office']
local cb =  (debug.getregistry()).classes['examples.class.icomparable.CompanyBuildings']

local factories = {f.new(1), f.new(2), f.new(3)}
local offices = {o.new(5), o.new(1), o.new(4)}
local buildingsets = {cb.new(f.new(1),o.new(5)), cb.new(f.new(2),o.new(1)), cb.new(f.new(3),o.new(4))}





quicksort(buildingsets)


