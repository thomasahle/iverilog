// Test: class variable declarations inside interface
// This tests that class instances can be declared inside interfaces

class DataHolder;
  int data;
  function new(int d = 0);
    data = d;
  endfunction
endclass

interface TestIface;
  // Class variable inside interface
  DataHolder holder;
  logic [7:0] signal;

  initial begin
    holder = new(42);
  end
endinterface

module test;
  TestIface u_if();

  initial begin
    #1;  // Wait for interface initial block
    if (u_if.holder.data !== 42) begin
      $display("FAILED: holder.data=%0d, expected 42", u_if.holder.data);
      $finish;
    end
    u_if.signal = 8'hAB;
    if (u_if.signal !== 8'hAB) begin
      $display("FAILED: signal=%h, expected AB", u_if.signal);
      $finish;
    end
    $display("PASSED");
  end
endmodule
