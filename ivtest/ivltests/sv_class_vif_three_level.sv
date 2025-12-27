// Test three-level class property chain with virtual interface
// This tests patterns like: driver.config.vif.signal = value

interface apb_if(input logic clk);
  logic psel;
  logic penable;
  logic [31:0] paddr;
endinterface

class agent_config;
  virtual apb_if vif;
endclass

class driver;
  agent_config cfg;
endclass

module test;
  logic clk = 0;
  apb_if apb(clk);
  int errors = 0;

  initial begin
    automatic driver d;
    d = new();
    d.cfg = new();
    d.cfg.vif = apb;

    // Test three-level write
    d.cfg.vif.psel = 1;
    d.cfg.vif.penable = 1;
    d.cfg.vif.paddr = 32'hABCD1234;

    #1;

    // Verify writes went through
    if (apb.psel !== 1) begin
      $display("FAILED: psel expected 1, got %0d", apb.psel);
      errors++;
    end
    if (apb.penable !== 1) begin
      $display("FAILED: penable expected 1, got %0d", apb.penable);
      errors++;
    end
    if (apb.paddr !== 32'hABCD1234) begin
      $display("FAILED: paddr expected ABCD1234, got %08h", apb.paddr);
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
  end
endmodule
