module dpi_test ();
   import "DPI-C" context task c_task (input  int i,
    output int o);
   logic [7:0] byte_array[1:20];
endmodule // dpi_test
