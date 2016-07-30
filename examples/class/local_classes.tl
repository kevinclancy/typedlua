

local function DogFunction(a,b,c)
  class TestClass
    method Speak() : any
      print("woof")
    end
    
    method clone() : TestClass
      local x = class(TestClass).new()
      x:Speak()
      return x
    end
    
    constructor new()
    end
  end
  
  local function loose_woof()
    local dog = TestClass.new():clone()
    dog:Speak()
  end
  
  return loose_woof
end

local function CatFunction(a,b,c)
  class TestClass
    method Speak() : any
      print("meow")
    end
    
    method clone() : TestClass
      local x = class(TestClass).new()
      x:Speak()
      return x
    end
    
    constructor new()
    end
  end
  
  local dog = DogFunction()
  dog()
end

CatFunction() --should print "woof"



