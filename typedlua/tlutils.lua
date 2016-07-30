--[[
Miscellaneous utility functions
]]

local tlutils = {}

function tlutils.order_description(i)
  local s = tostring(i)
  local c = s[#s]
  if c == '0' then
    return s .. "th"
  elseif i == 1 then
    return s .. "st"
  elseif i == 2 then
    return s .. "nd"
  elseif i == 3 then
    return s .. "rd"
  else
    return s .. "th"
  end
end

return tlutils