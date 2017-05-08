module autoconstant_gooch
  (/*AUTOARG*/
   // Outputs
   out1, out2, out3,
   // Inputs
   in1, in2, in3
   );
   
   input [3:0]  in1;
   input [3:0]  in2;
   input [3:0]  in3;
   output [3:0] out1;
   reg [3:0]    out1;
   output [3:0] out2;
   reg [3:0]    out2;
   output [3:0] out3;
   reg [3:0]    out3;
   
   
   
   always @(/*AUTOSENSE*/in1 or in2 or in3)
     begin
        case (in1)
          4'b0001 :     begin
             out1 = in2;
          end
          4'b0010 :     begin
             out1 = in2 + in3;
          end
          4'b0100 :     begin
             out1 = in2 - in3;
          end
          4'b1000 :     begin
             out1 = in2;
          end
          default       :       begin
             out1 = {4{1'b0}};
          end
        endcase
     end
   
   
   always @(/*AUTOSENSE*/in1 or in2 or in3)
     begin
        case (in1)
          4'b0001 :     begin
             out2 = in2;
          end
          4'b0010 :     begin
             out2 = in2 + in3;
          end
          4'b0100 :     begin
             out2 = in2 - in3;
          end
          4'b1000 :     begin
             out2 = in2;
          end
          default       :       begin
             out2 = {4{1'b0}};
          end
        endcase
     end
   
   
   always @(/*AUTOSENSE*/in1 or in2 or in3)
     begin
        /* AUTO_CONSTANT( temp )*/
        /* AxxxUTO_CONSTANT temp */
        out3  = in1 + in2;
        temp2 = temp;
        
        // ERROR here - above constant definition is not
        // correct - no braces - and so parser keeps looking
        // for the first variable it finds between a pair of
        // braces - in this case, in2. This in2 is now a
        // "constant" and is removed from all sensitivity lists.
        // ( in2 )
        
        case (in1)
          4'b0001 :     begin
             out3 = in2;
          end
          4'b0010 :     begin
             out3 = in2 + in3;
          end
          4'b0100 :     begin
             out3 = in2 - in3;
          end
          4'b1000 :     begin
             out3 = in2;
          end
          default       :       begin
             out3 = {4{1'b0}};
          end
        endcase
     end
   
   
   
endmodule


