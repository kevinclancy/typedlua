
typedef Foo = { 1 : string, 2 : Bar? }

and typedef Bar = { 1 : string, 2 : Foo?, 3 : Hello<number>?}

and class Hello<T>

  x : Foo
  y : Bar
  z : T

  method Action() : number
    self.x[2] = y
    return 42
  end

  constructor new(f : Foo, b : Bar, z : T)
    self.x = f
    self.y = b
    self.z = z
  end

end

local p : Foo = { "Test", { "Test", nil, nil } }
local q : Bar = { "Test", nil }

class(Hello).new<number>(p,q,3)
