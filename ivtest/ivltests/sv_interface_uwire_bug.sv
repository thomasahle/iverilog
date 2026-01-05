// Test case for uwire multiple driver bug with interface instances
// This should work - each interface instance should have its own signals

interface simple_if;
  logic sig_o;  // This is internally a REG
  logic out_val;

  assign out_val = sig_o;  // Continuous assign using sig_o
endinterface

// Driver module with output port that drives the interface signal
module driver_bfm(output reg sig_o);
  initial begin
    sig_o = 0;
    #10 sig_o = 1;
  end
endmodule

// Monitor module with input port that reads the interface signal
module monitor_bfm(input sig_o);
  initial begin
    #15;
    $display("Monitor sees sig_o = %b", sig_o);
  end
endmodule

// Agent that connects both driver and monitor to the interface
module agent_bfm(simple_if intf);
  driver_bfm  drv(.sig_o(intf.sig_o));
  monitor_bfm mon(.sig_o(intf.sig_o));
endmodule

// Top level with TWO interface instances
module top;
  simple_if if_a();  // Instance A
  simple_if if_b();  // Instance B

  // Each interface gets its own agent
  // if_a.sig_o should only be driven by agent_a's driver
  // if_b.sig_o should only be driven by agent_b's driver
  agent_bfm agent_a(if_a);
  agent_bfm agent_b(if_b);

  initial begin
    #20;
    $display("if_a.sig_o = %b, if_b.sig_o = %b", if_a.sig_o, if_b.sig_o);
    $display("PASSED");
    $finish;
  end
endmodule
