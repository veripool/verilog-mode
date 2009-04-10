module autoinst_wildcard;

   /*AUTOINOUT*/

   /* autoinst_wildcard_sub AUTO_TEMPLATE (
    .sd\([0-9]\)_\(.*\)\([0-9]+\)\(.*\)	(@"(uc \\"sd_\2\4[\1][\3]\\")"),
    ); */

   /*AUTOOUTPUT*/

   autoinst_wildcard_sub sub0
     (/*AUTOINST*/);

   /* autoinst_wildcard_sub AUTO_TEMPLATE (
    .sd\([0-9]\)_\(.*\)\([0-9]+\)\(.*\)	(sd_\2\4[\1][\3]),
    ); */

   /*AUTOOUTPUT*/

   autoinst_wildcard_sub sub1
     (/*AUTOINST*/);

endmodule

// Local Variables:
// eval:(defun uc (x) (upcase x))
// End:
