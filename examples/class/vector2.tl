class Vector2
  x : number
  y : number

  constructor new(x : number, y : number)
    self.x = x
    self.y = y
  end

  method DotProduct(other : Vector2) : number
    return self.x*other.x + self.y*other.y
  end

  method Offset(offset : Vector2)
    self.x = self.x + offset.x
    self.y = self.y + offset.y
  end
end