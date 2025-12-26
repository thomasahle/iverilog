// Test: object creation inside class tasks when class has virtual interface property
// Regression test for issue where fork_this_obj_ was incorrectly used for
// constructor's '@' variable, causing wrong class type to be used.

interface my_bfm(input bit clk);
  logic [7:0] data;
  initial data = 0;
endinterface

class inner_class;
  int value = 42;
endclass

class driver_class;
  virtual my_bfm vif_h = null;  // Having this vif property triggered the bug

  task run();
    automatic inner_class obj;
    // This constructor call was failing because driver_class instance
    // was used as 'this' instead of the inner_class instance
    obj = new();
    if (obj.value != 42) begin
      $display("FAILED: obj.value = %0d, expected 42", obj.value);
      $finish;
    end
    // Access vif to ensure it still works
    vif_h.data = 8'hAB;
    if (vif_h.data != 8'hAB) begin
      $display("FAILED: vif_h.data = %0h, expected AB", vif_h.data);
      $finish;
    end
  endtask
endclass

module test;
  bit clk = 0;
  my_bfm bfm_inst(clk);

  initial begin
    automatic driver_class drv = new();
    drv.vif_h = bfm_inst;
    drv.run();
    $display("PASSED");
    $finish;
  end
endmodule
