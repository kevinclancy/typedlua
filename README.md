# Typed Lua Class System

Typed Lua Class System
----------------------

The following code gives a sneak peak of the Lua Class system. While this code typechecks, the class system is still in the process of being debugged.

~~~

interface IComparable<-T>
  --returns true if self is less than or equal to argument
  method leq : (T) => (boolean)
end

--cartesian product of X and Y, using componentwise ordering
class ComparablePair< X <: IComparable<X>, Y <: IComparable<Y> > implements IComparable< ComparablePair<X, Y> >
  const x : X
  const y : Y
  
  constructor new(x : X, y : Y)
    self.x = x
    self.y = y
  end

  method leq(a : ComparablePair<X, Y>) : boolean
    return self.x:leq(a.x) and self.y:leq(a.y)
  end
end

local function quicksort< X <: IComparable<X> >(x : {X})
  local function swap(i : integer, j : integer)
    local temp = x[i]
    x[i] = x[j]
    x[j] = temp
  end
  
  local function partition(lo : integer, hi : integer) : integer
    local pivot = x[hi]
  
    --index after the contiguous chunk of all values 
    --encountered so far that are less than the pivot
    local z = lo
  
    for i=2,#x do
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
  
  local function sort(lo : integer, hi : integer)
    if hi - lo <= 1 then
      return
    end
    
    local p = partition(lo, hi)
    sort(lo,p-1)
    sort(p+1,hi)
  end

  sort(1,#x)
end

class Factory implements IComparable<Factory>
  cost : number
  
  constructor new(cost : number)
    self.cost = cost
  end

  method leq(other : Factory) : boolean
    return self.cost <= other.cost 
  end
end

class Office implements IComparable<Office>
  cost : number
  
  constructor new(cost : number)
    self.cost = cost
  end
  
  method leq(other : Office) : boolean
    return self.cost <= other.cost 
  end  
end

class CompanyBuildings extends ComparablePair<Factory,Office>
  constructor new(f : Factory, o : Office)
    super.new(f,o)
  end
end

local f = class(Factory)
local o = class(Office)
local cb = class(CompanyBuildings)

local factories : {Factory} = { f.new(1), f.new(2), f.new(3) }
local offices : {Office} = { o.new(5), o.new(1), o.new(4) }
local buildingsets : {CompanyBuildings} = { 
  cb.new( f.new(1), o.new(5) ),
  cb.new( f.new(2), o.new(1) ),
  cb.new( f.new(3), o.new(4) )
}
``
~~~
