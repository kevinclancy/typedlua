

 do if not (debug.getregistry()).classes then (debug.getregistry()).classes = {} end  (debug.getregistry()).classes['examples.class.iequatable.Number'] = { __premethods = {} }local class = (debug.getregistry()).classes['examples.class.iequatable.Number'] function class.new(val)local self = {} setmetatable(self, { __index = class.__premethods })








  self.val = val
return self end function class.__premethods:eq(other)


  return self.val == other.val
end end
 do if not (debug.getregistry()).classes then (debug.getregistry()).classes = {} end  (debug.getregistry()).classes['examples.class.iequatable.Pair'] = { __premethods = {} }local class = (debug.getregistry()).classes['examples.class.iequatable.Pair'] function class.__premethods:eq(other)







  return other.a:eq(self.a) and other.b:eq(self.b)
end function class.new(a, b)local self = {} setmetatable(self, { __index = class.__premethods })


  self.a = a
  self.b = b
return self end end
 do if not (debug.getregistry()).classes then (debug.getregistry()).classes = {} end  (debug.getregistry()).classes['examples.class.iequatable.Noncomp'] = { __premethods = {} }local class = (debug.getregistry()).classes['examples.class.iequatable.Noncomp'] function class.new()local self = {} setmetatable(self, { __index = class.__premethods }) return self end end






local function CompareThese (x, y) 
  return x:eq(y)
end

local one =  (debug.getregistry()).classes['examples.class.iequatable.Number'].new(1)
local two =  (debug.getregistry()).classes['examples.class.iequatable.Number'].new(2)
local p =  (debug.getregistry()).classes['examples.class.iequatable.Pair'].new(one,two)
local r =  (debug.getregistry()).classes['examples.class.iequatable.Pair'].new(two,two)
local nc =  (debug.getregistry()).classes['examples.class.iequatable.Noncomp']
local q =  (debug.getregistry()).classes['examples.class.iequatable.Pair'].new(nc.new(),nc.new())

print(p:eq(r))
print(CompareThese(p,p))
print(CompareThese(q,q))


