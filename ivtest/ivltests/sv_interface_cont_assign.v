// Test interface member continuous assignment
// This tests that continuous assignment between interface members works correctly
// when the interface is accessed via a module port.

interface simple_if;
  logic sig_a;
  logic sig_b;
endinterface

module test_mod(simple_if intf);
  // Continuous assignment between interface members
  assign intf.sig_a = intf.sig_b;
endmodule

module main;
  simple_if my_if();
  test_mod dut(.intf(my_if));

  initial begin
    my_if.sig_b = 1'b0;
    #10;
    if (my_if.sig_a !== 1'b0) begin
      $display("FAILED: sig_a should be 0, got %b", my_if.sig_a);
      $finish;
    end

    my_if.sig_b = 1'b1;
    #10;
    if (my_if.sig_a !== 1'b1) begin
      $display("FAILED: sig_a should be 1, got %b", my_if.sig_a);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
