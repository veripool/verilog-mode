// Issue 949 - Indenting SVA assert final block broken
module tb;
begin
a0: assert final (data0 == 1) else
$error;
end
endmodule


// Now check for other types of immediate assertion
module tb;
always @(abcd) begin

// simple immediate assert statement
assert (xyz) a = b;

// deferred immediate cover statement w/ #0
if(x)
cover #0 (efg)
$display("covered");

// deferred immedate assume statement w/ final
assume final (abcd) else
$display();
end

endmodule
