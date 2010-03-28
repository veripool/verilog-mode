module foo;
   always@(*)
     begin
	if(state==LBT_STATE)
	  begin
             if(something)
	       begin
	       end
	     else
	       begin
	       end
	  end
	else if(state==HS_0_STATE)
	  begin
	  end
	else if(state==STATE_4) 
	  begin
	  end
	else
	  begin
	  end
     end // always@ (*)
endmodule // foo
