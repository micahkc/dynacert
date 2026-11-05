function f input Real a; output Real b; algorithm b := 2*a; end f;
model function_call input Real d; Real x(start=0, fixed=true); equation der(x) = -f(x) + d; end function_call;
