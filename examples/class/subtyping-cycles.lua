
local Foo  do if not (debug.getregistry()).classes then (debug.getregistry()).classes = {} end  (debug.getregistry()).classes['examples.class.subtyping-cycles.Foo'] = { __premethods = {} }local class = (debug.getregistry()).classes['examples.class.subtyping-cycles.Foo'] function class.new()local self = {} setmetatable(self, { __index = class.__premethods })





  self.x = 1
return self end end Foo = (debug.getregistry()).classes['examples.class.subtyping-cycles.Foo'] 
local Bar  do if not (debug.getregistry()).classes then (debug.getregistry()).classes = {} end  (debug.getregistry()).classes['examples.class.subtyping-cycles.Bar'] = { __premethods = {} }local class = (debug.getregistry()).classes['examples.class.subtyping-cycles.Bar'] function class.one()local self = {} setmetatable(self, { __index = class.__premethods })






  self.x = 1
return self end function class.two()local self = {} setmetatable(self, { __index = class.__premethods })


  self.x = 2
return self end end Bar = (debug.getregistry()).classes['examples.class.subtyping-cycles.Bar'] 
local Baz  do if not (debug.getregistry()).classes then (debug.getregistry()).classes = {} end  (debug.getregistry()).classes['examples.class.subtyping-cycles.Baz'] = { __premethods = {} }local class = (debug.getregistry()).classes['examples.class.subtyping-cycles.Baz'] function class.new()local self = {} setmetatable(self, { __index = class.__premethods })






  self.x = 31
return self end end Baz = (debug.getregistry()).classes['examples.class.subtyping-cycles.Baz'] 








