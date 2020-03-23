
connectmodule Wreal2L(input wreal w, output wire l);
logic lval;

  parameter real vsup = 1.8;
       parameter real vth_hi = 0.7*vsup;
  parameter real vth_lo = 0.3*vsup;
  always begin
if( w >= vth_hi) lval = 1'b1;
    else if(w <= vth_lo) lval = 1'b0;
    else if(w === `wrealZState) lval = 1'bz;
    else lval = 1'bx;
    @(w);
end

assign l = lval;
   endconnectmodule

