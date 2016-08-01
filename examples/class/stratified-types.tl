


class First
  constructor new()
  end
end

class Second< X <: First > --nothing wrong here because First was defined in a previous bundle
  constructor new()
  end
end

and class Third< X <: Second<First> > --bounds can't reference types from same bundle
  constructor new()
  end
end

