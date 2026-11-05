package Bfile model M input Real d; Real x(start=0, fixed=true); equation der(x) = -A.f(x) + d; end M; end Bfile;
