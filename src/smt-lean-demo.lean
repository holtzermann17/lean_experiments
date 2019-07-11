import smt.veriT

example {x y : ℤ} (h1 : ((x - y) = (x + (- y) + 1)))
 : false :=
begin
  veriT,
end
