module foo;
   initial begin
      /* The function verilog-strip-comments should not change this line:*/
      $display("INFO :[PIPE LINK %d]: ///////////////////////////////////////////",PIPE_LINK);
      
      // to this:
      $display("INFO :[PIPE LINK %d]: ");
      
      /* The function verilog-strip-comments should not change this line:*/
      $display("INFO :[PIPE LINK %d]: /* ",PIPE_LINK); /* This comment should go away */
      // to this:
      $display("INFO :[PIPE LINK %d]: ");
      
      /* also this comment should not get eaten
       because of use of slashes // and such like
       */
      /*
       ugly hidded end comment // */
      $display("don't forget me agentina");
      // another hidden comment /*
      /**/
      
   end
   
endmodule // foo
