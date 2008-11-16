module autoinst_bits_lba_gi

  // ==xxxxxxx==

  // xxxxxxxxx 1997-1998, xxxxx xxx.
  // xxx xxxxxx xxxxxxxx

  // ****************************************************************** /
  // ****************************************************************** /
  // xxxxx, xxxxxxxxxxxx
  // xxxxxxx:		xxx-4080
  // xxxxxx:  		xxx xxxxxxx
  // xxxxx:		xxxxxxx 16, 1998
  // ******************************************************************* /
  // ******************************************************************* /
  // xxxx xxxx:		xxx_xx.x
  // xxxxxxxx xxxxxxx:
  // $xxx: xxx_xx.x,x $
  // xxxxxxxx 1.3  1998/03/06 00:27:00  xxx
  // -- xxxxx xxxxxxx xx xx.xxxx xxx xxxxxxxx xxxxxxx.
  // -- xxxx xxxxxxxxxxxxx xx xx xxxxxxxxxxx xx xx.x xxx xx.x xx xxxxxxx xxx xxxxxxxxxxx.
  // -- xxxx xxxxx xxx xxxxxxxxxxxxx xxx1'x (xxxxxxx xx xxxxx) xx xx.x xxx xxxx xxxxxx
  //    xxxxxxxxxx.
  // -- xxxxx xxxxxxxxxx xxxxxxxx xx xxx xx xxxxxxxxxxx xxx xxxx xxxxxx xxxxxxxxxxxx xxxx.
  // -- xx xxx xxxxxxxxx xxx xxxxxx xx xx xx xxx xxxxx xxxxx xx xxxx xxxxxxxx xx xxxx.
  // -- xx xx xxxx xxxxxxx xxx xxx xxxx xxxxxx xxxxxx (xxx xxx xxxx) xxx xxx xxxx/xxxx
  //    xxxxxxxxxx xxxx xxxxxxx.
  //
  // xxxxxxxx 1.2  1998/03/04 18:58:55  xxx
  // xxxxx xxxxxxxxx xxx-xx xxxxxxx xxxxxxx xx xxxx xxxxx.
  //
  // xxxxxxxx 1.1  1998/02/23 19:31:52  xxx
  // xxxxx xxxxx xxxxxx xxx xxxx xxxxx xxxxx xxxxxxxxxx.
  //
  // ---------------------------------------------------------------
  //
  // xxxxxxx xxx xxxxxxxxx xxx xxxxx xxx xxxxxxx xxx
  //
  // xxxx xxxxxx xxxxx xxx xxxxx xxxxxx xxxxxxx/xxxx xxx xxxx
  //      xx.x xxx xx xx xxxxxxxxx xxxx xxxx.x xxxxxx xx
  //      xxxx xxx xxxxxxx xx xxx. xx xxxx xxxxates the
  //      bidir Foo Bus into a chip input for use by li.v
  //
  // This module also isolates for input to lbsm.v, and drives
  //       (if so indicated by lbsm.v) the bidir Fooileo Cmd bus.
  //
  //

  (
   CLK,
   WWADoe,
   WWCoe,
   WWCmdIfOE,
   WWADHold,
   iWWADO,
   WWCmdI,
   WWADI,
   WWADB,
   WWCmdB
   );

   /////////////////////////////////////////////////////////////////////
	 // inputs

   input		CLK;		// LBA clk

   // inputs from lbsm.v
   input		WWADoe;		// FooBus Addr/Data OE
   input		WWCoe;		// FooBus Cmd OE
   input [8:0] 		WWCmdIfOE;	// FooBus Cmd if enabled
   input		WWADHold;	// FooBus Addr hold

   // inputs from li.v
   input [31:0] 	iWWADO;		// FooBus Address/Data out next cycle


   /////////////////////////////////////////////////////////////////////
   // outputs

   // outputs to lbsm.v
   output [8:0] 	WWCmdI;		// FooBus Command in

   // outputs to li.v
   output [31:0] 	WWADI;		// FooBus Address/Data in


   /////////////////////////////////////////////////////////////////////
   // bidirs

   // bidirs to/from off-chip
   inout [31:0] 	WWADB;		// bidir FooBus addr/data
   inout [8:0] 		WWCmdB;		// bidir FooBus command

   /////////////////////////////////////////////////////////////////////
   // reg's for outputs (some flops, some not)

   /////////////////////////////////////////////////////////////////////
   // other flops

   reg [31:0] 		WWADIfOE;	// FooBus Addr/Data Out if enabled



endmodule


// Local Variables:
// eval:(if (fboundp `verilog-enable-indentation) (verilog-enable-indentation))
// End:
