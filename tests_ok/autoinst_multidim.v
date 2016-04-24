module top;
   /*AUTOLOGIC*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic                               sig1; // From u_x of x.v
   logic [A-1:0]                       sig2; // From u_x of x.v
   logic [A-1:0] [B-1:0]               sig3; // From u_x of x.v
   logic [A-1:0][B-1:0] [C-1:0]        sig4; // From u_x of x.v
   logic [A-1:0][B-1:0][C-1:0] [D-1:0] sig5; // From u_x of x.v
   logic                               vsig1; // From u_x of x.v
   logic                               vsig2 [W-1:0]; // From u_x of x.v
   logic                               vsig3 [W-1:0][X-1:0]; // From u_x of x.v
   logic                               vsig4 [W-1:0][X-1:0][Y-1:0];// From u_x of x.v
   logic                               vsig5 [W-1:0][X-1:0][Y-1:0][Z-1:0];// From u_x of x.v
   logic                               zsig1; // From u_x of x.v
   logic [A-1:0]                       zsig2 [W-1:0]; // From u_x of x.v
   logic [A-1:0] [B-1:0]               zsig3 [W-1:0][X-1:0]; // From u_x of x.v
   logic [A-1:0][B-1:0] [C-1:0]        zsig4 [W-1:0][X-1:0][Y-1:0];// From u_x of x.v
   logic [A-1:0][B-1:0][C-1:0] [D-1:0] zsig5 [W-1:0][X-1:0][Y-1:0][Z-1:0];// From u_x of x.v
   // End of automatics
   
   x u_x (/*AUTOINST*/
          // Outputs
          .sig1                         (sig1),
          .sig2                         (sig2[A-1:0]),
          .sig3                         (sig3/*[A-1:0][B-1:0]*/),
          .sig4                         (sig4/*[A-1:0][B-1:0][C-1:0]*/),
          .sig5                         (sig5/*[A-1:0][B-1:0][C-1:0][D-1:0]*/),
          .vsig1                        (vsig1),
          .vsig2                        (vsig2/*.[W-1:0]*/),
          .vsig3                        (vsig3/*.[W-1:0][X-1:0]*/),
          .vsig4                        (vsig4/*.[W-1:0][X-1:0][Y-1:0]*/),
          .vsig5                        (vsig5/*.[W-1:0][X-1:0][Y-1:0][Z-1:0]*/),
          .zsig1                        (zsig1),
          .zsig2                        (zsig2/*[A-1:0].[W-1:0]*/),
          .zsig3                        (zsig3/*[A-1:0][B-1:0].[W-1:0][X-1:0]*/),
          .zsig4                        (zsig4/*[A-1:0][B-1:0][C-1:0].[W-1:0][X-1:0][Y-1:0]*/),
          .zsig5                        (zsig5/*[A-1:0][B-1:0][C-1:0][D-1:0].[W-1:0][X-1:0][Y-1:0][Z-1:0]*/));
endmodule // top

module x;
   output                              sig1;
   output [A-1:0]                      sig2;
   output [A-1:0][B-1:0]               sig3;
   output [A-1:0][B-1:0][C-1:0]        sig4;
   output [A-1:0][B-1:0][C-1:0][D-1:0] sig5;
   
   output                              vsig1;
   output                              vsig2 [W-1:0];
   output                              vsig3 [W-1:0][X-1:0];
   output                              vsig4 [W-1:0][X-1:0][Y-1:0];
   output                              vsig5 [W-1:0][X-1:0][Y-1:0][Z-1:0];
   
   output                              zsig1;
   output [A-1:0]                      zsig2 [W-1:0];
   output [A-1:0][B-1:0]               zsig3 [W-1:0][X-1:0];
   output [A-1:0][B-1:0][C-1:0]        zsig4 [W-1:0][X-1:0][Y-1:0];
   output [A-1:0][B-1:0][C-1:0][D-1:0] zsig5 [W-1:0][X-1:0][Y-1:0][Z-1:0];
endmodule
