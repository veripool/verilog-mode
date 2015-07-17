// Issue 941 : The following operators should not be broken by auto-indents
module m;
initial begin
a = b;
a <= b;
a <<= b;
a <<<= b;
a >= b;
a >>= b;
a >>>= b;
a == b;
a != b;
a === b;
a !== b;
a ==? b;
a !=? b;
a <-> b;
a -> b;
a ->> b;
a |-> b;
a |=> b;
a #-# b;
a #=# b;
a := b;
a :/ b;
end

endmodule
