
interface IEq<-T>
  method eq : (T) => (boolean)
end

class Number implements IEq<Number>
  const val : number
  
  constructor new(val : number)
    self.val = val
  end
  
  method eq(other : Number) : boolean
    return self.val == other.val
  end
end

class Pair<+A, +B> implements IEq< Pair< IEq<A>, IEq<B> > >
  const a : A
  const b : B
  
  method eq(other : Pair< IEq<A>, IEq<B> >) : boolean
    return other.a:eq(self.a) and other.b:eq(self.b)
  end
  
  constructor new(a : A, b : B)
    self.a = a
    self.b = b
  end
end

class Noncomp
  constructor new() end
end

local function CompareThese< T <: IEq<T> >(x : T, y : T)
  return x:eq(y)
end

local one = class(Number).new(1)
local two = Number.new(2)
local p = class(Pair).new<Number, Number>(one,two)
local r = Pair.new<Number, Number>(two,two)
local nc = class(Noncomp)
local q = class(Pair).new<Noncomp, Noncomp>(nc.new(), nc.new())

print(p:eq(r))
print( CompareThese< Pair<Number,Number> >(p, p) ) --this works
print( CompareThese< Pair<Noncomp,Noncomp> >(q, q) ) --this generates an error