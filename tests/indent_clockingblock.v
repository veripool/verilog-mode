class mipsbfm_trans extends vmm_data;
static vmm_log log = new ("mipsbfm_trans", "class") ;
logic [31:0] addr, data, mask, op;
function new();
super.new(this.log);
endfunction: new
endclass // mipsbfm_trans

interface mipsbfm_if(input clk);
logic [31:0] data;
logic [31:0] addr;
logic [31:0] mask;
logic [31:0] op;
logic 	valid;

clocking cb @(posedge clk);
output 	data;
output 	addr;
output 	mask;
output 	op;
output 	valid;
endclocking // cb

endinterface // mipsbfm_if


`vmm_channel(mipsbfm_trans);

//--------------------------------------------------------------
// MIPS BFM Master Xactor Class
//--------------------------------------------------------------

class mipsbfm_master extends vmm_xactor;
// Transaction channels
mipsbfm_trans_channel  in_chan ;

endclass // mipsbfm_master

