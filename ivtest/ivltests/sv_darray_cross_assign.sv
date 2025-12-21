// Test cross-assignment between darray elements
// Pattern: agents[i].config = configs[i]
// This is the UVM pattern where we have:
//   - Dynamic array of agent objects
//   - Dynamic array of config objects
//   - Each agent gets assigned a config from the config array

class Config;
  int id;
  string name;

  function new(int i = 0, string n = "");
    id = i;
    name = n;
  endfunction
endclass

class Agent;
  Config cfg;  // This is the property we're assigning to
  int active;

  function new();
    cfg = null;
    active = 1;
  endfunction
endclass

module test;
  Agent agents[];
  Config configs[];
  int i;
  Agent a;
  Config c;

  initial begin
    // Test 1: Basic cross-assignment pattern
    $display("Test 1: agents[i].cfg = configs[i]");

    // Create config array
    configs = new[3];
    for (i = 0; i < 3; i++) begin
      configs[i] = new(i + 100, $sformatf("config_%0d", i));
    end

    // Create agent array
    agents = new[3];
    for (i = 0; i < 3; i++) begin
      agents[i] = new();
    end

    // Cross-assign: This is the critical pattern
    for (i = 0; i < 3; i++) begin
      agents[i].cfg = configs[i];  // L-value: darray[i].prop, R-value: darray[i]
    end

    // Verify assignments worked
    for (i = 0; i < 3; i++) begin
      a = agents[i];
      if (a.cfg == null) begin
        $display("FAILED: agents[%0d].cfg is null after assignment", i);
        $finish;
      end
      if (a.cfg.id !== 100 + i) begin
        $display("FAILED: agents[%0d].cfg.id = %0d, expected %0d", i, a.cfg.id, 100 + i);
        $finish;
      end
    end
    $display("Test 1 PASSED");

    // Test 2: Verify independence (changing one config doesn't affect another)
    $display("Test 2: Independence check");
    configs[0].id = 999;
    a = agents[0];
    if (a.cfg.id !== 999) begin
      $display("FAILED: Test 2 - agents[0].cfg.id = %0d after changing configs[0], expected 999", a.cfg.id);
      $finish;
    end
    a = agents[1];
    if (a.cfg.id !== 101) begin
      $display("FAILED: Test 2 - agents[1].cfg.id = %0d, expected 101 (unchanged)", a.cfg.id);
      $finish;
    end
    $display("Test 2 PASSED");

    // Test 3: Reassignment
    $display("Test 3: Reassignment");
    c = new(500, "new_config");
    agents[1].cfg = c;

    a = agents[1];
    if (a.cfg.id !== 500) begin
      $display("FAILED: Test 3 - agents[1].cfg.id = %0d after reassignment, expected 500", a.cfg.id);
      $finish;
    end
    $display("Test 3 PASSED");

    // Test 4: Access property through direct darray access
    $display("Test 4: Direct darray access to nested property");
    // This tests: agents[i].cfg.id (chained property access through darray element)
    a = agents[0];
    if (a.cfg.id !== 999) begin
      $display("FAILED: Test 4 - Couldn't access agents[0].cfg.id");
      $finish;
    end
    $display("Test 4 PASSED");

    $display("PASSED");
  end
endmodule
