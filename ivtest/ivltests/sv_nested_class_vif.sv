// Minimal test for nested class with vif

interface myif(input logic clk);
  logic data;
endinterface

class cfg;
  virtual myif vif;
endclass

class drv;
  cfg my_cfg;
endclass

class agent;
  cfg my_cfg;
  drv my_drv;

  function new();
    my_drv = new();
  endfunction

  function void build();
    my_drv.my_cfg = my_cfg;
  endfunction
endclass

module test;
  logic clk;
  myif mif(clk);

  initial begin
    automatic agent a;
    automatic cfg c;

    a = new();
    c = new();
    c.vif = mif;

    a.my_cfg = c;
    a.build();

    if (a.my_drv.my_cfg == null)
      $display("FAILED: my_drv.my_cfg is null");
    else if (a.my_drv.my_cfg.vif == null)
      $display("FAILED: my_drv.my_cfg.vif is null");
    else
      $display("PASSED");
  end
endmodule
