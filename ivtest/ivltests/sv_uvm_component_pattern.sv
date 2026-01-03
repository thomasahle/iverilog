// Test: UVM-style component hierarchy with config passing

interface apb_if(input logic clk);
  logic psel;
  logic [31:0] paddr;
endinterface

class agent_config;
  virtual apb_if vif;
  int agent_id;
endclass

class driver_proxy;
  agent_config cfg;

  function void build();
    if (cfg == null)
      $display("ERROR: cfg is null");
    else if (cfg.vif == null)
      $display("ERROR: cfg.vif is null");
    else
      $display("build OK");
  endfunction

  task run();
    if (cfg != null && cfg.vif != null) begin
      cfg.vif.psel = 1;
      $display("drove transaction");
    end
  endtask
endclass

class agent;
  agent_config cfg;
  driver_proxy drv;

  function new();
    drv = new();
  endfunction

  function void build();
    if (cfg == null) begin
      $display("ERROR: agent cfg is null");
      return;
    end
    drv.cfg = cfg;
    drv.build();
  endfunction

  task run();
    drv.run();
  endtask
endclass

module test;
  logic clk = 0;
  apb_if apb(clk);

  initial begin
    automatic agent a;
    automatic agent_config cfg0;

    a = new();

    cfg0 = new();
    cfg0.vif = apb;
    cfg0.agent_id = 5;

    a.cfg = cfg0;
    a.build();

    if (a.drv.cfg == null) begin
      $display("FAILED: a.drv.cfg is null");
    end else if (a.drv.cfg.vif == null) begin
      $display("FAILED: a.drv.cfg.vif is null");
    end else begin
      $display("Driver config OK");
    end

    a.run();

    #1;
    if (apb.psel !== 1)
      $display("FAILED: psel not driven");
    else
      $display("PASSED");
  end
endmodule
