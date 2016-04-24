module sub(output logic [1:-1] oned,
           output logic [1:-1] [2:-1]        twod,
           output logic [1:-1] [2:-1] [3:-3] threed);
endmodule

module dut (
            );
   
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic [1:-1]              b_oned; // From subb of sub.v
   logic [3:-3]              b_threed; // From subb of sub.v
   logic [2:-1]              b_twod; // From subb of sub.v
   logic [1:-1]              c_oned; // From subc of sub.v
   logic [x][y] [3:-3]       c_threed; // From subc of sub.v
   logic [x] [2:-1]          c_twod; // From subc of sub.v
   logic [1:-1]              d_oned; // From subd of sub.v
   logic [1:-1][2:-1] [3:-3] d_threed; // From subd of sub.v
   logic [1:-1] [2:-1]       d_twod; // From subd of sub.v
   logic [1:-1]              oned; // From sub1 of sub.v
   logic [1:-1][2:-1] [3:-3] threed; // From sub1 of sub.v
   logic [1:-1] [2:-1]       twod;                      // From sub1 of sub.v
   // End of automatics
   
   /* sub AUTO_TEMPLATE ();
    */
   
   sub sub1 (/*AUTOINST*/
             // Outputs
             .oned                      (oned[1:-1]),
             .twod                      (twod/*[1:-1][2:-1]*/),
             .threed                    (threed/*[1:-1][2:-1][3:-3]*/));
   
   /* sub AUTO_TEMPLATE (
    .oned                       (b_oned[]),
    .twod                       (b_twod[]),
    .threed                     (b_threed[]));
    */
   
   // NOTE this results in the wrong declaration for b_twod/b_threed
   sub subb (/*AUTOINST*/
             // Outputs
             .oned                      (b_oned[1:-1]),          // Templated
             .twod                      (b_twod[2:-1]),          // Templated
             .threed                    (b_threed[3:-3]));       // Templated
   
   /* sub AUTO_TEMPLATE (
    .oned                       (c_oned[]),
    .twod                       (c_twod[x][]),
    .threed                     (c_threed[x][y][]));
    */
   
   sub subc (/*AUTOINST*/
             // Outputs
             .oned                      (c_oned[1:-1]),          // Templated
             .twod                      (c_twod[x][2:-1]),       // Templated
             .threed                    (c_threed[x][y][3:-3]));         // Templated
   
   /* sub AUTO_TEMPLATE (
    .oned                       (d_oned[][]),
    .twod                       (d_twod[][]),
    .threed                     (d_threed[][]));
    */
   
   sub subd (/*AUTOINST*/
             // Outputs
             .oned                      (d_oned[1:-1]),          // Templated
             .twod                      (d_twod/*[1:-1][2:-1]*/), // Templated
             .threed                    (d_threed/*[1:-1][2:-1][3:-3]*/)); // Templated
   
endmodule
