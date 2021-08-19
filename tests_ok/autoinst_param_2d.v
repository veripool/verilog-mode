// bug981

module a(
         parameter                AUM=80;
         parameter                BUM=70;
         parameter                VUM=1;
         parameter                V2=2;
         input                    my_data_z;
         input                    my_data_v[VUM];
         input                    my_data_vv[VUM][V2];
         input [AUM-1:0]          my_data_av[VUM];
         input [AUM-1:0][BUM-1:0] my_data_ab;
         input [AUM-1:0][BUM-1:0] my_data_abv[VUM];
         
         input [XUM-1:0][YUM-1:0] my_data_xyz[ZUM];
         
         input                    PARAMS0__t params0 [1:0];
         input                    PARAMS1__t params1 [1:0];
         );
endmodule

module top (/*AUTOARG*/
            // Inputs
            TEST1_params1, TEST1_params0, TEST1_my_data_z, TEST1_my_data_xyz, TEST1_my_data_vv,
            TEST1_my_data_v, TEST1_my_data_av, TEST1_my_data_abv, TEST1_my_data_ab, TEST0_params1,
            TEST0_params0, TEST0_my_data_z, TEST0_my_data_xyz, TEST0_my_data_vv, TEST0_my_data_v,
            TEST0_my_data_av, TEST0_my_data_abv, TEST0_my_data_ab
            )
  /*AUTOINPUT*/
  // Beginning of automatic inputs (from unused autoinst inputs)
  input [TEST0_AUM-1:0] [TEST0_BUM-1:0] TEST0_my_data_ab;// To a_0 of a.v
   input [TEST0_AUM-1:0] [TEST0_BUM-1:0] TEST0_my_data_abv [TEST0_VUM];// To a_0 of a.v
   input [TEST0_AUM-1:0]                 TEST0_my_data_av [TEST0_VUM];// To a_0 of a.v
   input                                 TEST0_my_data_v [VUM]; // To a_0 of a.v
   input                                 TEST0_my_data_vv [VUM][V2];// To a_0 of a.v
   input [XUM-1:0] [YUM-1:0]             TEST0_my_data_xyz [ZUM];// To a_0 of a.v
   input                                 TEST0_my_data_z; // To a_0 of a.v
   input                                 PARAMS0__t TEST0_params0 [1:0]; // To a_0 of a.v
   input                                 PARAMS1__t TEST0_params1 [1:0]; // To a_0 of a.v
   input [TEST1_AUM-1:0] [TEST1_BUM-1:0] TEST1_my_data_ab;// To a_1 of a.v
   input [TEST1_AUM-1:0] [TEST1_BUM-1:0] TEST1_my_data_abv [TEST1_VUM];// To a_1 of a.v
   input [TEST1_AUM-1:0]                 TEST1_my_data_av [TEST1_VUM];// To a_1 of a.v
   input                                 TEST1_my_data_v [VUM]; // To a_1 of a.v
   input                                 TEST1_my_data_vv [VUM][V2];// To a_1 of a.v
   input [XUM-1:0] [YUM-1:0]             TEST1_my_data_xyz [ZUM];// To a_1 of a.v
   input                                 TEST1_my_data_z; // To a_1 of a.v
   input                                 PARAMS0__t TEST1_params0 [1:0]; // To a_1 of a.v
   input                                 PARAMS1__t TEST1_params1 [1:0];        // To a_1 of a.v
   // End of automatics
   /*AUTOOUTPUT*/
   /*AUTOWIRE*/
   
   /*
    a AUTO_TEMPLATE
    (
    .\(.*\) (TEST@_\1[][]),
    );
    */
   a #(/*AUTOINSTPARAM*/
       // Parameters
       .AUM                             (TEST0_AUM),             // Templated
       .BUM                             (TEST0_BUM),             // Templated
       .VUM                             (TEST0_VUM),             // Templated
       .V2                              (TEST0_V2))              // Templated
   a_0 (/*AUTOINST*/
        // Inputs
        .my_data_z                      (TEST0_my_data_z),       // Templated
        .my_data_v                      (TEST0_my_data_v/*.[VUM]*/), // Templated
        .my_data_vv                     (TEST0_my_data_vv/*.[VUM][V2]*/), // Templated
        .my_data_av                     (TEST0_my_data_av/*[TEST0_AUM-1:0].[TEST0_VUM]*/), // Templated
        .my_data_ab                     (TEST0_my_data_ab/*[TEST0_AUM-1:0][TEST0_BUM-1:0]*/), // Templated
        .my_data_abv                    (TEST0_my_data_abv/*[TEST0_AUM-1:0][TEST0_BUM-1:0].[TEST0_VUM]*/), // Templated
        .my_data_xyz                    (TEST0_my_data_xyz/*[XUM-1:0][YUM-1:0].[ZUM]*/), // Templated
        .params0                        (TEST0_params0/*.[1:0]*/), // Templated
        .params1                        (TEST0_params1/*.[1:0]*/)); // Templated
   
   
   a #(/*AUTOINSTPARAM*/
       // Parameters
       .AUM                             (TEST1_AUM),             // Templated
       .BUM                             (TEST1_BUM),             // Templated
       .VUM                             (TEST1_VUM),             // Templated
       .V2                              (TEST1_V2))              // Templated
   a_1 (/*AUTOINST*/
        // Inputs
        .my_data_z                      (TEST1_my_data_z),       // Templated
        .my_data_v                      (TEST1_my_data_v/*.[VUM]*/), // Templated
        .my_data_vv                     (TEST1_my_data_vv/*.[VUM][V2]*/), // Templated
        .my_data_av                     (TEST1_my_data_av/*[TEST1_AUM-1:0].[TEST1_VUM]*/), // Templated
        .my_data_ab                     (TEST1_my_data_ab/*[TEST1_AUM-1:0][TEST1_BUM-1:0]*/), // Templated
        .my_data_abv                    (TEST1_my_data_abv/*[TEST1_AUM-1:0][TEST1_BUM-1:0].[TEST1_VUM]*/), // Templated
        .my_data_xyz                    (TEST1_my_data_xyz/*[XUM-1:0][YUM-1:0].[ZUM]*/), // Templated
        .params0                        (TEST1_params0/*.[1:0]*/), // Templated
        .params1                        (TEST1_params1/*.[1:0]*/)); // Templated
   
endmodule

// Local Variables:
// verilog-auto-inst-param-value:t
// verilog-typedef-regexp: "_t$"
// End:
