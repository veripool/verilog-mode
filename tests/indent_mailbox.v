class Driver;
   mailbox mbox;  // <= not highlighted.
   semaphore smtx;
   int id;
   virtual Rx_if Rx;
   
   function new(mailbox mbox, int id, virtual Rx_if.TB Rx);
      this.mbox = mbox;
      this.id = i;
      this.Rx = Rx;
   endfunction // new
endclass // Driver

