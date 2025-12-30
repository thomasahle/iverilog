// Test fork/join_none accessing 'this' in class tasks

class Counter;
   int value;
   string name;

   function new(string n);
      name = n;
      value = 0;
   endfunction

   task increment();
      $display("[%0t] %s: increment() called", $time, name);
      fork
         begin
            $display("[%0t] %s: forked increment starting, value=%0d", $time, name, value);
            #10;
            this.value = this.value + 1;
            $display("[%0t] %s: forked increment done, value=%0d", $time, name, this.value);
         end
      join_none
      $display("[%0t] %s: increment() returning immediately", $time, name);
   endtask

   task run_test();
      $display("[%0t] %s: run_test starting", $time, name);
      increment();
      #5;
      increment();
      #20;
      $display("[%0t] %s: run_test done, final value=%0d", $time, name, value);
   endtask
endclass

module test;
   Counter cnt;

   initial begin
      cnt = new("cnt");
      cnt.run_test();

      if (cnt.value == 2) begin
         $display("PASSED: value=%0d", cnt.value);
      end else begin
         $display("FAILED: expected value=2, got %0d", cnt.value);
      end
      $finish;
   end
endmodule
