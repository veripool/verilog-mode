always
   @(w or c_int)
  begin
     if ((w == 1'b0) && ((status_register[7]) == 1'b1))
       begin
	  write_protect <= `TRUE ;
       end
     if (w == 1'b1)
       begin
	  write_protect <= `FALSE ;
       end
  end
   
