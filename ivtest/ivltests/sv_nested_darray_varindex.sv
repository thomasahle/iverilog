// Test nested darray property access with variable index
// Pattern: for (int i = 0; i < N; i++) outer_h.items[i].value = x;
// This is common in UVM for initializing arrays of configuration objects

class Config;
  bit enabled;
  int prio;

  function new();
    enabled = 0;
    prio = 0;
  endfunction
endclass

class ConfigArray;
  Config configs[];

  function new(int size);
    configs = new[size];
    for (int i = 0; i < size; i++) begin
      configs[i] = new();
    end
  endfunction
endclass

class TopConfig;
  ConfigArray cfg_array;

  function new();
    cfg_array = new(4);
  endfunction

  function void init_with_loop();
    // Test writing to nested darray property with variable index
    for (int i = 0; i < 4; i++) begin
      if (i % 2 == 0)
        cfg_array.configs[i].enabled = 1;
      else
        cfg_array.configs[i].enabled = 0;
      cfg_array.configs[i].prio = i * 10;
    end
  endfunction

  function int verify();
    int errors = 0;
    bit expected_enabled;
    int expected_prio;

    // Test reading nested darray properties with variable index
    for (int i = 0; i < 4; i++) begin
      if (i % 2 == 0)
        expected_enabled = 1;
      else
        expected_enabled = 0;
      expected_prio = i * 10;

      if (cfg_array.configs[i].enabled !== expected_enabled) begin
        $display("FAILED: configs[%0d].enabled = %0d, expected %0d",
                 i, cfg_array.configs[i].enabled, expected_enabled);
        errors++;
      end
      if (cfg_array.configs[i].prio !== expected_prio) begin
        $display("FAILED: configs[%0d].prio = %0d, expected %0d",
                 i, cfg_array.configs[i].prio, expected_prio);
        errors++;
      end
    end

    return errors;
  endfunction
endclass

module test;
  TopConfig top;
  int errors;

  initial begin
    top = new();
    top.init_with_loop();
    errors = top.verify();

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED with %0d errors", errors);
  end
endmodule
