
interface IEq<-T>
  method eq : (T) => (boolean)
end

class Number implements IEq<Number> --creates a type cycle, since IEq is not a shape
  const val : number
  
  constructor new(val : number)
    self.val = val
  end
  
  method eq(other : Number) : boolean
    return self.val == other.val
  end
end

--the following implements clause creates a type cycle and therefore generates
--an error
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

class Pale<A,B> 
  constructor new() end
end

Pale<A,B> implements IEq<A>