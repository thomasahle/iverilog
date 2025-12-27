// Simplified test for property chain assignment

class my_config;
  int value = 99;
endclass

class my_child;
  my_config cfg_h;
endclass

class my_parent;
  my_child child_h;

  function new();
    child_h = new();
  endfunction

  function void set_child_config(my_config cfg);
    child_h.cfg_h = cfg;  // This is the critical assignment
  endfunction
endclass

module test;
  initial begin
    automatic my_parent p = new();
    automatic my_config cfg = new();

    cfg.value = 42;

    p.set_child_config(cfg);

    // Check the result
    if (p.child_h.cfg_h == null)
      $display("FAILED: cfg_h is NULL");
    else if (p.child_h.cfg_h.value != 42)
      $display("FAILED: wrong value %0d", p.child_h.cfg_h.value);
    else
      $display("PASSED");
  end
endmodule
