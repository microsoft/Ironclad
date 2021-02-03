
module Math__power_s {

// TODO_MODULE: module Math__power_s {
function {:opaque} power(b:int, e:nat) : int
  decreases e
  // ensures b > 0 ==> 0<power(b,e)
{
  if (e==0) then
    1
  else
    b*power(b,e-1)
}

// TODO_MODULE: } import opened Math__power_s_ = Math__power_s

} 
