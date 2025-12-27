// Test: Property assignment to array element - like UVM component hierarchy
// Pattern: parent.children[i].config = configs[i];

class my_config;
  int value = 99;
endclass

class my_child;
  my_config cfg_h;
endclass

class my_parent;
  my_child children[];
  my_config configs[];

  function new();
    children = new[2];
    configs = new[2];
    foreach (children[i]) begin
      children[i] = new();
      configs[i] = new();
      configs[i].value = i * 10;
    end
  endfunction

  function void assign_configs();
    foreach (children[i]) begin
      $display("Assigning config[%0d] to child[%0d]", i, i);
      children[i].cfg_h = configs[i];
    end
  endfunction

  function void check();
    foreach (children[i]) begin
      if (children[i].cfg_h == null) begin
        $display("FAILED: children[%0d].cfg_h is NULL", i);
        return;
      end
      $display("children[%0d].cfg_h.value = %0d", i, children[i].cfg_h.value);
      if (children[i].cfg_h.value != i * 10) begin
        $display("FAILED: wrong value");
        return;
      end
    end
    $display("PASSED");
  endfunction
endclass

module test;
  initial begin
    automatic my_parent p = new();
    p.assign_configs();
    p.check();
  end
endmodule
