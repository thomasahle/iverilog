// Test uvm_config_db with dynamic array element destinations
// This tests the pattern: uvm_config_db#(T)::get(ctx, inst, name, darray[i])

class my_config;
  int value;
  function new();
    value = 0;
  endfunction
endclass

class my_container;
  my_config configs[];

  function new();
    configs = new[2];
    // Initialize elements (will be overwritten by config_db::get)
    configs[0] = null;
    configs[1] = null;
  endfunction
endclass

module test;
  initial begin
    automatic my_config cfg0, cfg1;
    automatic my_container container;

    // Create configs with different values
    cfg0 = new();
    cfg0.value = 42;
    cfg1 = new();
    cfg1.value = 99;

    // Store in config_db with different names
    uvm_config_db#(my_config)::set(null, "*", "config_0", cfg0);
    uvm_config_db#(my_config)::set(null, "*", "config_1", cfg1);

    // Create container with uninitialized darray elements
    container = new();

    // Get from config_db into darray elements
    if (!uvm_config_db#(my_config)::get(null, "*", "config_0", container.configs[0])) begin
      $display("FAILED: config_db::get for configs[0] returned 0");
      $finish;
    end

    if (!uvm_config_db#(my_config)::get(null, "*", "config_1", container.configs[1])) begin
      $display("FAILED: config_db::get for configs[1] returned 0");
      $finish;
    end

    // Verify the values were stored correctly
    if (container.configs[0] == null) begin
      $display("FAILED: configs[0] is null after get");
      $finish;
    end
    if (container.configs[1] == null) begin
      $display("FAILED: configs[1] is null after get");
      $finish;
    end

    if (container.configs[0].value != 42) begin
      $display("FAILED: configs[0].value=%0d, expected 42", container.configs[0].value);
      $finish;
    end
    if (container.configs[1].value != 99) begin
      $display("FAILED: configs[1].value=%0d, expected 99", container.configs[1].value);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
