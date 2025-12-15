// Test extern task declaration with out-of-body definition
// Tasks are different from functions - they can have delays and consume time

class Driver;
  int data_sent;

  extern function new();
  extern task send_data(input int data);
  extern task wait_cycles(input int n);
endclass

function Driver::new();
  data_sent = 0;
endfunction

task Driver::send_data(input int data);
  $display("[%0t] Sending data: %0d", $time, data);
  data_sent = data_sent + 1;
  #10;
  $display("[%0t] Data sent complete", $time);
endtask

task Driver::wait_cycles(input int n);
  repeat(n) #1;
endtask

module test;
  initial begin
    Driver drv;
    drv = new();

    if (drv.data_sent != 0) begin
      $display("FAILED: initial data_sent=%0d, expected 0", drv.data_sent);
      $finish;
    end

    drv.send_data(100);
    drv.send_data(200);

    if (drv.data_sent != 2) begin
      $display("FAILED: data_sent=%0d, expected 2", drv.data_sent);
      $finish;
    end

    drv.wait_cycles(5);

    $display("PASSED");
    $finish;
  end
endmodule
