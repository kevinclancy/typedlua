

interface Seq<ElemType>
  method map : <U>((ElemType) -> (U)) => (Seq<U>)
end

class Array<ElemType> implements Seq<ElemType>
  const elems : {ElemType}
  
  method map<U>(f : (ElemType) -> (U)) : Array<U>
    local mapped_elems : {U} = {}
    for i=1,#(self.elems) do
      local elem = self.elems[i]
      if elem then
        mapped_elems[i] = f(elem)
      end
    end
    
    return Array.new<U>(mapped_elems)
  end
  
  constructor new(elems : {ElemType})
    self.elems = elems
  end
end