import avm_pkg::*;
import tinyalu_pkg::*;

module top;
   
   alu_operation req;
   string  msg;
   integer i;
   
   initial begin
      $display ("---- A or B inside {0,8'hFF} ----");
      for (i = 1; i<=5; i++) begin
         req  = new();
         assert( a() with {A} );
         req.randomize()
           with
             {
            A inside {0,8'hFF};
            B inside {0,8'hFF};
         };
         $sformat (msg,"ALU Request: %s", req.convert2string());
         avm_report_message("TOP",msg);
         $display;
         $display ("---- op  inside [add_op : mul_op] ----");
         
         for (i = 1; i<=10; i++) begin
            req  = new();
            assert(
                   req.randomize() with
                   {
                      op inside {[add_op : mul_op]};
                   }
                   );
            $sformat (msg,"ALU Request: %s", req.convert2string());
            avm_report_message("TOP",msg);
         end // for (i = 1; i<=10; i++)
      end // initial begin
      endmodule // req_reader


