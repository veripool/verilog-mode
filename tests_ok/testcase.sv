`define moo 1
class foo;
   extern function void bar();
endclass: foo

function void foo::bar();
   int variable;
endfunction: bar

`define moo 1
class fu;
   extern function void br();
endclass: fu

function void fu::br();
   int variable;
endfunction: br
