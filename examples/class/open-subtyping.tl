
shape IOp<+X>
  method GetOp : () => (X)
end

class Foo<T,S>
  method GetOp() : Bar<T,S>
    return Bar.new<T,S>()
  end

  constructor new()
  end
end

and class Bar<T,S>
  method GetOp() : Foo<T,S>
    return Foo.new<T,S>()
  end
  
  constructor new()
  end
end

Foo<Z,Z> implements IOp< Bar<Z,Z> > --generates error
Foo implements IOp< Bar<T,S> > --generates error
number implements IOp< Bar<number, number> > -- generates error

class OpList< X <: IOp<Y>, Y <: IOp<X> >
  const contents : {X}
  
  method GetOp() : OpList<Y,X>
    local op_contents : {Y} = {}
    for i=1,#(self.contents) do
      local x = self.contents[i]
      if x then
        op_contents[i] = x:GetOp()
      end
    end
    return OpList.new<Y, X>(op_contents)
  end
  
  constructor new(contents : {X})
    self.contents = contents
  end
end

typedef Foo2 = Foo<number,number>
typedef Bar2 = Bar<number,number>

local foos : {Foo2} = {}

do
  local opList = OpList.new<Foo2,Bar2>(foos) --two errors

  Foo<Z,X> implements Op< Bar<Z,X> >

  local opList = OpList.new<Foo2,Bar2>(foos) --one error

  Bar<A,B> implements Op< Foo<A,B> >

  local opList = OpList.new<Foo2,Bar2>(foos) --no errors
end

local opList = OpList.new<Foo2,Bar2>(foos) --two errors


