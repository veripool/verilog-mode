   import "DPI-C" function string fna (input string str1);
export "DPI" c_identifier = task task_identifier;
  import "DPI" context function string fnb (input string str1);

module testbench;

    import "DPI" function string fn1 (input string str1);
   import "DPI-C" function void dpiWriteArray (input bit[7:0] data[]);
      import "DPI-C" pure function void dpiReadArray (output bit[7:0] data[]);
 import "DPI-C" function void dpiAesSetKey ( int key_high_u int key_high_l,
                                               int key_low_u, int key_low_l );
  import "DPI-C" function void dpiAesSetIV (int iv_high_u, int iv_high_l,
                                             int iv_low_u, int iv_low_l);
    import "DPI-C" function void dpiAesSetSkip (int skip);
  import "DPI-C" function void dpiAesCBCEncrypt ();

   logic 					 a;
endmodule // testbench

/*
package ref_model;
   import "DPI-C" xx_write_bmp_file =
     function void write_bmp_file(input string filename);
        
   import "DPI-C" xx_demosaic =
     function void demosaic(regs regs,
                            inout pix_buf imgR, imgG, imgB);
endpackage 
*/
