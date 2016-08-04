--[[
Miscellaneous utility functions
]]

local tlutils = {}

function tlutils.abbreviate(typename)
  local rev = string.reverse(typename)
  local dotpos = string.find(rev, "%.")
  if dotpos == nil then
    return typename
  else
    local s =  string.sub(rev,1,dotpos-1)
    return string.reverse(s)
  end
end

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