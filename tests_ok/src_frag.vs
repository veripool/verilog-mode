module src_frag (
                 input logic        inp_signal_0, // Input Signal 0
                 input logic        inp_signal_1, // Input Signal 1
                 input logic        inp_signal_2, // Input Signal 2
                 input logic [10:0] inp_signal_3; // Input Signal 3
                 input logic        inp_signal_4, // Input Signal 4
                 output logic       outp_signal_0, // Output Signal 0
                 inout logic        test,
                 output logic       outp_signal_1 // Output Signal 1
                 );
   
   logic [7:0]        local_0; // Local Signal 0
   logic              local_1; // Local Signal 1
   logic              local_3; // Local Signal 3
   var logic          local_4; // Local Signal 4
   var logic          local_5; // Local Signal 5
   logic signed [1:0] local_6;
   
   logic              local_1; // Local Signal 1
   input logic        in_lg;
   inout logic        io_lg;
   output logic       o_lg;
   ref logic          r_lg;
   const logic        c_rg;
   static logic       s_rg;
   protected logic    p_lg;
   local logic        l_lg;
   localparam logic   lp_lg = 23;
   parameter logic    p_lg = 32;
   typedef logic      td_lg;
   input wire         foo;
   logic              local_3; // Local Signal 3
   var logic          local_5; // Local Signal 5
   byte               B;
   shortint           si;
   int                f;
   longint            li;
   integer            I;
   int unsigned       uI;
   time               t;
   bit                b;
   logic              l;
   reg                r;
   shortreal          sR;
   real               R;
   realtime           Rt;
   supply0            s0;
   supply1            s1;
   tri                tr;
   triand             tra;
   trior              tro;
   trireg             trr;
   tri0               tr0;
   tri1               tr1;
   uwire              uw;
   wire               w;
   wand               wa;
   wor                wo;
   string             s;
   event              e;
   chandle            ch;
   virtual            v;
   enum               en;
   genvar             g;
   struct             st;
   union              u;
   mailbox            mb;
   semaphore          sm;
   
   
   defparam v_lg  = 56;
   
endmodule // src_frag

// Local Variables:
// mode: Verilog
// End:
