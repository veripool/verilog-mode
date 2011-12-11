module foo;
   
   // for each additional in-air txmacphy byte
   task nextTxByte();
      TxByteCnt++;
      TxLastByteTime  = $time;
   endtask // nextTxByte
   task automatic blah();
      t;
   endtask // blah
   function static foo();
      foo  = 1;
   endfunction // foo
   // start counting when txmacphy sees first in-air byte
   task firstTxByte();
      TxByteCnt        = 1;
      TxFirstByteTime  = $time;
      TxLastByteTime   = $time;
   endtask // firstTxByte
   
   // outputs the overall performance of the RX path in Mbps (MBits per second)
   task printRxPerformance();
      integer ibps;
      real    Mbps;
      if( RxByteCnt && systemTop.intMonitor.frgRxedCnt >= 2 ) begin
         ibps  = 
                 (RxByteCnt*8*1000000000)/(RxLastByteTime-RxFirstByteTime);
         Mbps  = ibps/1000000;
         $display("%t: %s - RX average performance: %fMbps (Mbits/sec)",
                  $time, myName, Mbps );
      end
      else
        $display("%t: %s - Requires >= 2 RX frames in order to measure performance", $time, myName);
      
   endtask // printRxPerformance
   
endmodule // foo

class a;
   virtual function void foo();
      foo  = 2;
   endfunction // void
   extern function void bar();
   function fred();
      aaa;
   endfunction // fred
   
   task foo;
   endtask // endtask
   
   virtual task foo;
   endtask // endtask
   
   generate g;
   endgenerate
   
   covergroup g;
   endgroup // g
   
   property p;
   endproperty
   
   sequence s;
   endsequence // s
   
   clocking c;
   endclocking // c
   
   function f;
   endfunction //
   
   virtual function f;
   endfunction //
   
   protected function f;
   endfunction //
   
endclass // a

