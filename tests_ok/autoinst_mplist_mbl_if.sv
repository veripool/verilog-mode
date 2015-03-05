// Example interface definition with at least one modport.

interface autoinst_mplist_mbl_if ();
   
   logic        sof;
   logic        eof;
   logic [31:0] data;
   logic        ready;
   logic        valid;
   
   modport master(
                  output data,
                  output sof,
                  output eof,
                  output valid,
                  input  ready
                  );
   
   modport slave(
                 input  data,
                 input  sof,
                 input  eof,
                 input  valid,
                 output ready
                 );
   
endinterface
