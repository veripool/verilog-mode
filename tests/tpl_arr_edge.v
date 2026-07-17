// Sub module with various port types for unpacked-array AUTO_TEMPLATE tests.

module tpl_arr_sub
  (
   output [15:0] data,
   output [7:0]  addr,
   output        flag,
   output [3:0]  ctrl
   );
endmodule

// Sub modules used to test mixed unpacked-array range handling.
module tpl_arr_desc_numeric_sub
  (
   output [15:0] desc,
   output [15:0] numeric
   );
endmodule

module tpl_arr_symbolic_numeric_sub
  (
   output [15:0] symbolic,
   output [15:0] numeric
   );
endmodule

module tpl_arr_escaped_sub
  (
   output [15:0] data
   );
endmodule

// ============================================================
// Test: non-consecutive indexes produce one covering range
// ============================================================

module tpl_arr_skip
  ();
   /*AUTOWIRE*/
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (s0[].[@]),
    );
    */
   tpl_arr_sub u_0
     (/*AUTOINST*/);
   tpl_arr_sub u_2
     (/*AUTOINST*/);
   tpl_arr_sub u_4
     (/*AUTOINST*/);
endmodule

// ============================================================
// Test: descending port range [15:0] + ascending unpacked [0:N]
// ============================================================

module tpl_arr_desc
  ();
   /*AUTOWIRE*/
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (d[].[@]),
    );
    */
   tpl_arr_sub u_0
     (/*AUTOINST*/);
   tpl_arr_sub u_1
     (/*AUTOINST*/);
   tpl_arr_sub u_2
     (/*AUTOINST*/);
endmodule

// ============================================================
// Test: multiple ports using [].[@] in the same template
// ============================================================

module tpl_arr_multi
  ();
   /*AUTOWIRE*/
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (mdata[].[@]),
    .flag (mflag[].[@]),
    );
    */
   tpl_arr_sub u_0
     (/*AUTOINST*/);
   tpl_arr_sub u_1
     (/*AUTOINST*/);
endmodule

// ============================================================
// Test: mergeable numeric index + non-numeric index in one template
// ============================================================

module tpl_arr_mixed
  ();
   /*AUTOWIRE*/
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (mx[].[@]),       // numeric indexes → merged
    .addr (mxaddr[].[IDX]), // non-numeric index → kept as-is
    );
    */
   tpl_arr_sub u_0
     (/*AUTOINST*/);
   tpl_arr_sub u_1
     (/*AUTOINST*/);
endmodule

// ============================================================
// Test: same signal name mapped to different hard-coded indexes;
// each port gets its own declaration, not merged.
// ============================================================

module tpl_arr_gap
  ();
   /*AUTOWIRE*/
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (g[].[0]),
    .addr (g[].[3]),
    .ctrl (g[].[7]),
    );
    */

   tpl_arr_sub u_a
     (/*AUTOINST*/);
   tpl_arr_sub u_b
     (/*AUTOINST*/);
   tpl_arr_sub u_c
     (/*AUTOINST*/);
endmodule

// ============================================================
// Test: single instance → single-element unpacked range [N:N]
// ============================================================

module tpl_arr_single
  ();
   /*AUTOWIRE*/
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (sing[].[@]),
    );
    */
   tpl_arr_sub u_5
     (/*AUTOINST*/);
endmodule

// ============================================================
// Test: descending instance-name order still produces ascending
// unpacked range (e.g. u_3, u_2, u_1 → [1:3])
// ============================================================

module tpl_arr_rev
  ();
   /*AUTOWIRE*/
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (rev[].[@]),
    );
    */
   tpl_arr_sub u_3
     (/*AUTOINST*/);
   tpl_arr_sub u_2
     (/*AUTOINST*/);
   tpl_arr_sub u_1
     (/*AUTOINST*/);
endmodule

// ============================================================
// Test: overlapping unpacked ranges [0:2] and [1:4] merge to
// [0:4] and warn "Couldn't Merge".
// ============================================================

module tpl_arr_overlap
  ();
   /*AUTOWIRE*/
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (ov[].[0:2]),
    );
    */
   tpl_arr_sub u_a
     (/*AUTOINST*/);

   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (ov[].[1:4]),
    );
    */
   tpl_arr_sub u_b
     (/*AUTOINST*/);
endmodule

// ============================================================
// Test: signed unpacked ranges merge without expanding indexes
// ============================================================

module tpl_arr_signed
  ();
   /*AUTOWIRE*/
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (neg[].[-2:-1]),
    );
    */
   tpl_arr_sub u_low
     (/*AUTOINST*/);

   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (neg[].[0:2]),
    );
    */
   tpl_arr_sub u_high
     (/*AUTOINST*/);
endmodule

// ============================================================
// Test: a descending range wins over a numeric range for the
// same signal, and AUTOWIRE reports that they could not merge.
// ============================================================

module tpl_arr_mixed_direction
  ();
   /*AUTOWIRE*/
   /*
    tpl_arr_desc_numeric_sub AUTO_TEMPLATE
    (
    .desc    (mixed[].[3:0]),
    .numeric (mixed[].[@]),
    );
    */
   tpl_arr_desc_numeric_sub u_0
     (/*AUTOINST*/);
endmodule

// ============================================================
// Test: a symbolic range wins over a numeric range for the
// same signal, and AUTOWIRE reports that they could not merge.
// ============================================================

module tpl_arr_mixed_symbolic
  ();
   /*AUTOWIRE*/
   /*
    tpl_arr_symbolic_numeric_sub AUTO_TEMPLATE
    (
    .symbolic (sym[].[IDX]),
    .numeric  (sym[].[@]),
    );
    */
   tpl_arr_symbolic_numeric_sub u_0
     (/*AUTOINST*/);
endmodule

// ============================================================
// Test: a single negative index becomes a single-element range.
// ============================================================

module tpl_arr_signed_single
  ();
   /*AUTOWIRE*/
   /*
    tpl_arr_sub AUTO_TEMPLATE
    (
    .data (neg_one[].[-2]),
    );
    */
   tpl_arr_sub u_0
     (/*AUTOINST*/);
endmodule

// ============================================================
// Test: escaped identifiers are retained while unpacked ranges
// are recovered from an AUTO_TEMPLATE connection.
// ============================================================

module tpl_arr_escaped
  ();
   /*AUTOWIRE*/
   /*
    tpl_arr_escaped_sub AUTO_TEMPLATE
    (
    .data (\escaped_data [].[0:1]),
    );
    */
   tpl_arr_escaped_sub u_0
     (/*AUTOINST*/);
endmodule
