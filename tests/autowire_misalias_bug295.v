interface my_interface ();
   logic [2:0] out2;
   logic [2:0] out3;
endinterface: my_interface

module foobar (input [2:0] in2, output [2:0] out2);
endmodule

module foo_autowire_fails (my_interface itf);
   /*AUTOWIRE*/
   assign itf.out2 = out2; // perhaps a namespace collision?
   foobar foobar0
     (/*AUTOINST*/);
endmodule   

module foo_autowire_works (my_interface itf);
   /*AUTOWIRE*/
   assign itf.out3 = out2;
   foobar foobar0
     (/*AUTOINST*/);
endmodule
