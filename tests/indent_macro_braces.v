// bug 433 - Check indentation around macro (uvm/ovm/vmm) with curly-brace
//           internals (these look like a constraint)

module m;
if(x)
`ovm_do_with(my,
{ y == 1;
z == 2; });
endmodule
