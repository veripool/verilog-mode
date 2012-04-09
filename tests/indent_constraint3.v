//bug433

class data;
   rand integer data1;
   rand integer data2,data3;
   rand reg [31:0] foo;
    
   constraint basic_c {
		       //empty constraint
		       }
      
     constraint complex_c {
			   data1 <= 100;
			   foo inside {[40:999]};
			   if(foo < 87)
			   data2 == 10;
			   if(data2 == 76) {
	data3 == 8;
     }
			   }
	
       constraint implication_c {
	  data1 == 10 -> data3 >= -1;
       }
   
   function new();
      data1 = 0;
      data2 = 78;
   endfunction // new
endclass // data
