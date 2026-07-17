// Sub module with various port types for unpacked-array AUTO_TEMPLATE tests.

module tpl_arr_sub
  (
   output [15:0] data,
   output [7:0]  addr,
   output        flag,
   output [3:0]  ctrl
   );
endmodule

// ============================================================
// Test: non-consecutive indexes produce separate declarations
// ============================================================

module tpl_arr_skip
  ();
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [7:0]  addr;     // From u_0 of tpl_arr_sub.v, ...
   wire [3:0]  ctrl;     // From u_0 of tpl_arr_sub.v, ...
   wire        flag;     // From u_0 of tpl_arr_sub.v, ...
   wire [15:0] s0 [0:4]; // From u_0 of tpl_arr_sub.v, ...
   // End of automatics
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (s0[].[@]),
    );
    */
   tpl_arr_sub u_0
     (/*AUTOINST*/
      // Outputs
      .data                             (s0[0]/*[15:0].[0]*/),   // Templated
      .addr                             (addr[7:0]),
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
   tpl_arr_sub u_2
     (/*AUTOINST*/
      // Outputs
      .data                             (s0[2]/*[15:0].[2]*/),   // Templated
      .addr                             (addr[7:0]),
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
   tpl_arr_sub u_4
     (/*AUTOINST*/
      // Outputs
      .data                             (s0[4]/*[15:0].[4]*/),   // Templated
      .addr                             (addr[7:0]),
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
endmodule

// ============================================================
// Test: descending port range [15:0] + ascending unpacked [0:N]
// ============================================================

module tpl_arr_desc
  ();
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [7:0]  addr;    // From u_0 of tpl_arr_sub.v, ...
   wire [3:0]  ctrl;    // From u_0 of tpl_arr_sub.v, ...
   wire [15:0] d [0:2]; // From u_0 of tpl_arr_sub.v, ...
   wire        flag;    // From u_0 of tpl_arr_sub.v, ...
   // End of automatics
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (d[].[@]),
    );
    */
   tpl_arr_sub u_0
     (/*AUTOINST*/
      // Outputs
      .data                             (d[0]/*[15:0].[0]*/),    // Templated
      .addr                             (addr[7:0]),
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
   tpl_arr_sub u_1
     (/*AUTOINST*/
      // Outputs
      .data                             (d[1]/*[15:0].[1]*/),    // Templated
      .addr                             (addr[7:0]),
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
   tpl_arr_sub u_2
     (/*AUTOINST*/
      // Outputs
      .data                             (d[2]/*[15:0].[2]*/),    // Templated
      .addr                             (addr[7:0]),
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
endmodule

// ============================================================
// Test: multiple ports using [].[@] in the same template
// ============================================================

module tpl_arr_multi
  ();
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [7:0]  addr;        // From u_0 of tpl_arr_sub.v, ...
   wire [3:0]  ctrl;        // From u_0 of tpl_arr_sub.v, ...
   wire [15:0] mdata [0:1]; // From u_0 of tpl_arr_sub.v, ...
   wire        mflag [0:1]; // From u_0 of tpl_arr_sub.v, ...
   // End of automatics
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (mdata[].[@]),
    .flag (mflag[].[@]),
    );
    */
   tpl_arr_sub u_0
     (/*AUTOINST*/
      // Outputs
      .data                             (mdata[0]/*[15:0].[0]*/), // Templated
      .addr                             (addr[7:0]),
      .flag                             (mflag[0]/*.[0]*/),      // Templated
      .ctrl                             (ctrl[3:0]));
   tpl_arr_sub u_1
     (/*AUTOINST*/
      // Outputs
      .data                             (mdata[1]/*[15:0].[1]*/), // Templated
      .addr                             (addr[7:0]),
      .flag                             (mflag[1]/*.[1]*/),      // Templated
      .ctrl                             (ctrl[3:0]));
endmodule

// ============================================================
// Test: mergeable numeric index + non-numeric index in one template
// ============================================================

module tpl_arr_mixed
  ();
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [3:0]  ctrl;         // From u_0 of tpl_arr_sub.v, ...
   wire        flag;         // From u_0 of tpl_arr_sub.v, ...
   wire [15:0] mx [0:1];     // From u_0 of tpl_arr_sub.v, ...
   wire [7:0]  mxaddr [IDX]; // From u_0 of tpl_arr_sub.v, ...
   // End of automatics
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (mx[].[@]),       // numeric indexes → merged
    .addr (mxaddr[].[IDX]), // non-numeric index → kept as-is
    );
    */
   tpl_arr_sub u_0
     (/*AUTOINST*/
      // Outputs
      .data                             (mx[0]/*[15:0].[0]*/),   // Templated
      .addr                             (mxaddr[IDX]/*[7:0].[IDX]*/), // Templated
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
   tpl_arr_sub u_1
     (/*AUTOINST*/
      // Outputs
      .data                             (mx[1]/*[15:0].[1]*/),   // Templated
      .addr                             (mxaddr[IDX]/*[7:0].[IDX]*/), // Templated
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
endmodule

// ============================================================
// Test: same signal name mapped to different hard-coded indexes;
// each port gets its own declaration, not merged.
// ============================================================

module tpl_arr_gap
  ();
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire        flag;    // From u_a of tpl_arr_sub.v, ...
   wire [15:0] g [0:7]; // From u_a of tpl_arr_sub.v, ..., Couldn't Merge
   // End of automatics
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (g[].[0]),
    .addr (g[].[3]),
    .ctrl (g[].[7]),
    );
    */
   tpl_arr_sub u_a
     (/*AUTOINST*/
      // Outputs
      .data                             (g[0]/*[15:0].[0]*/),    // Templated
      .addr                             (g[3]/*[7:0].[3]*/),     // Templated
      .flag                             (flag),
      .ctrl                             (g[7]/*[3:0].[7]*/));    // Templated
   tpl_arr_sub u_b
     (/*AUTOINST*/
      // Outputs
      .data                             (g[0]/*[15:0].[0]*/),    // Templated
      .addr                             (g[3]/*[7:0].[3]*/),     // Templated
      .flag                             (flag),
      .ctrl                             (g[7]/*[3:0].[7]*/));    // Templated
   tpl_arr_sub u_c
     (/*AUTOINST*/
      // Outputs
      .data                             (g[0]/*[15:0].[0]*/),    // Templated
      .addr                             (g[3]/*[7:0].[3]*/),     // Templated
      .flag                             (flag),
      .ctrl                             (g[7]/*[3:0].[7]*/));    // Templated
endmodule

// ============================================================
// Test: single instance → single-element unpacked range [N:N]
// ============================================================

module tpl_arr_single
  ();
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [7:0]  addr;       // From u_5 of tpl_arr_sub.v
   wire [3:0]  ctrl;       // From u_5 of tpl_arr_sub.v
   wire        flag;       // From u_5 of tpl_arr_sub.v
   wire [15:0] sing [5:5]; // From u_5 of tpl_arr_sub.v
   // End of automatics
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (sing[].[@]),
    );
    */
   tpl_arr_sub u_5
     (/*AUTOINST*/
      // Outputs
      .data                             (sing[5]/*[15:0].[5]*/), // Templated
      .addr                             (addr[7:0]),
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
endmodule

// ============================================================
// Test: descending instance-name order still produces ascending
// unpacked range (e.g. u_3, u_2, u_1 → [1:3])
// ============================================================

module tpl_arr_rev
  ();
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [7:0]  addr;      // From u_3 of tpl_arr_sub.v, ...
   wire [3:0]  ctrl;      // From u_3 of tpl_arr_sub.v, ...
   wire        flag;      // From u_3 of tpl_arr_sub.v, ...
   wire [15:0] rev [1:3]; // From u_3 of tpl_arr_sub.v, ...
   // End of automatics
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (rev[].[@]),
    );
    */
   tpl_arr_sub u_3
     (/*AUTOINST*/
      // Outputs
      .data                             (rev[3]/*[15:0].[3]*/),  // Templated
      .addr                             (addr[7:0]),
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
   tpl_arr_sub u_2
     (/*AUTOINST*/
      // Outputs
      .data                             (rev[2]/*[15:0].[2]*/),  // Templated
      .addr                             (addr[7:0]),
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
   tpl_arr_sub u_1
     (/*AUTOINST*/
      // Outputs
      .data                             (rev[1]/*[15:0].[1]*/),  // Templated
      .addr                             (addr[7:0]),
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
endmodule

// ============================================================
// Test: overlapping unpacked ranges — [0:2] and [1:4] merge to
// [0:4] via max/min; the overlap is not warned about.
// This is a known limitation, not intended behaviour.
// ============================================================

module tpl_arr_overlap
  ();
   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [7:0]  addr;     // From u_a of tpl_arr_sub.v, ...
   wire [3:0]  ctrl;     // From u_a of tpl_arr_sub.v, ...
   wire        flag;     // From u_a of tpl_arr_sub.v, ...
   wire [15:0] ov [0:4]; // From u_a of tpl_arr_sub.v, ..., Couldn't Merge
   // End of automatics
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (ov[].[0:2]),
    );
    */
   tpl_arr_sub u_a
     (/*AUTOINST*/
      // Outputs
      .data                             (ov[0:2]/*[15:0].[0:2]*/), // Templated
      .addr                             (addr[7:0]),
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
   
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (ov[].[1:4]),
    );
    */
   tpl_arr_sub u_b
     (/*AUTOINST*/
      // Outputs
      .data                             (ov[1:4]/*[15:0].[1:4]*/), // Templated
      .addr                             (addr[7:0]),
      .flag                             (flag),
      .ctrl                             (ctrl[3:0]));
endmodule
