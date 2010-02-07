module testbench;
 
   import "DPI-C" function void dpiWriteArray (input bit[7:0] data[]);
   import "DPI-C" function void dpiReadArray (output bit[7:0] data[]);
   import "DPI-C" function void dpiAesSetKey ( int key_high_u int key_high_l,
                                                     int key_low_u, int key_low_l );          
   import "DPI-C" function void dpiAesSetIV (int iv_high_u, int iv_high_l,
                                                      int iv_low_u, int iv_low_l);
   import "DPI-C" function void dpiAesSetSkip (int skip);
   import "DPI-C" function void dpiAesCBCEncrypt ();
                    
      endmodule // testbench
