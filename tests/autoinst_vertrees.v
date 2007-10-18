module autoinst_vertrees
  (/*AUTOARG*/);

  /*AUTOINPUT*/

  /*AUTOOUTPUT*/

  /*AUTOWIRE*/

  /*
   autoinst_vertrees_slv AUTO_TEMPLATE "u_slv_\([a-z]\)"
    (.i2c_\(.*\) (i2c_@_\1),
     .slv_\(.*\) (slv_@_\1),
     .rpt_\(.*\) (rpt_@_\1),
     )
  */  
  autoinst_vertrees_slv u_slv_a
    (/*AUTOINST*/);   

  autoinst_vertrees_slv u_slv_b
    (/*AUTOINST*/); 

endmodule // ddc
