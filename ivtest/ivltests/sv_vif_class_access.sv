// Test: Access class variable inside interface through virtual interface from class task
// This is the pattern used in UVM drivers

class proxy_class;
  int transaction_count = 0;

  function void record_transaction();
    transaction_count++;
    $display("proxy: transaction_count = %0d", transaction_count);
  endfunction
endclass

interface driver_bfm(input bit clk);
  logic [7:0] data;
  proxy_class proxy_h;  // Class variable inside interface

  initial begin
    data = 0;
    proxy_h = null;
  end
endinterface

class driver_class;
  virtual driver_bfm vif_h = null;

  task run();
    // Access class variable through virtual interface
    if (vif_h.proxy_h == null) begin
      $display("run: proxy_h is null, creating new proxy");
      vif_h.proxy_h = new();
    end

    // Drive data through vif
    vif_h.data = 8'hAB;
    $display("run: drove data = 0x%0h", vif_h.data);

    // Call method on class variable through vif
    vif_h.proxy_h.record_transaction();
    vif_h.proxy_h.record_transaction();

    $display("run: final transaction_count = %0d", vif_h.proxy_h.transaction_count);
  endtask
endclass

module test;
  bit clk = 0;
  driver_bfm bfm_inst(clk);

  initial begin
    automatic driver_class drv = new();
    drv.vif_h = bfm_inst;

    $display("main: Calling drv.run()");
    drv.run();
    $display("main: drv.run() returned");

    if (bfm_inst.data == 8'hAB && bfm_inst.proxy_h.transaction_count == 2)
      $display("PASSED");
    else
      $display("FAILED: data=%0h, count=%0d", bfm_inst.data, bfm_inst.proxy_h.transaction_count);

    $finish;
  end
endmodule
