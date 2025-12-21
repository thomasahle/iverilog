// Test dynamic array element class property l-value assignment
// This tests the pattern: arr[i].prop = value
// which is critical for UVM config_db patterns

class ConfigItem;
  int id;
  string name;

  function new(int i = 0, string n = "");
    id = i;
    name = n;
  endfunction
endclass

class Agent;
  ConfigItem cfg;
  int active;

  function new();
    cfg = null;
    active = 1;
  endfunction
endclass

module test;
  Agent arr[];
  Agent a;
  ConfigItem cfg;
  int i;

  initial begin
    // Test 1: Basic darray[i].prop = value
    $display("Test 1: Basic darray element property assignment");
    arr = new[3];
    for (i = 0; i < 3; i++) begin
      arr[i] = new();
    end

    // The key l-value pattern - this is what we're testing
    for (i = 0; i < 3; i++) begin
      cfg = new(i + 100);
      arr[i].cfg = cfg;  // L-value: arr[i].cfg
    end

    // Verify by accessing through a temp variable
    a = arr[0];
    if (a.cfg == null) begin
      $display("FAILED: Test 1 - arr[0].cfg is null after assignment");
      $finish;
    end
    if (a.cfg.id !== 100) begin
      $display("FAILED: Test 1 - arr[0].cfg.id = %0d, expected 100", a.cfg.id);
      $finish;
    end
    a = arr[1];
    if (a.cfg.id !== 101) begin
      $display("FAILED: Test 1 - arr[1].cfg.id = %0d, expected 101", a.cfg.id);
      $finish;
    end
    a = arr[2];
    if (a.cfg.id !== 102) begin
      $display("FAILED: Test 1 - arr[2].cfg.id = %0d, expected 102", a.cfg.id);
      $finish;
    end
    $display("Test 1 PASSED");

    // Test 2: Integer property assignment
    $display("Test 2: Integer property assignment to darray element");
    for (i = 0; i < 3; i++) begin
      arr[i].active = i * 10;  // L-value: arr[i].active
    end

    a = arr[0];
    if (a.active !== 0) begin
      $display("FAILED: Test 2 - arr[0].active = %0d, expected 0", a.active);
      $finish;
    end
    a = arr[1];
    if (a.active !== 10) begin
      $display("FAILED: Test 2 - arr[1].active = %0d, expected 10", a.active);
      $finish;
    end
    a = arr[2];
    if (a.active !== 20) begin
      $display("FAILED: Test 2 - arr[2].active = %0d, expected 20", a.active);
      $finish;
    end
    $display("Test 2 PASSED");

    // Test 3: Reassignment
    $display("Test 3: Property reassignment");
    cfg = new(999);
    arr[1].cfg = cfg;  // Reassign arr[1].cfg

    a = arr[1];
    if (a.cfg.id !== 999) begin
      $display("FAILED: Test 3 - arr[1].cfg.id = %0d after reassignment, expected 999", a.cfg.id);
      $finish;
    end
    // Make sure arr[0] wasn't affected
    a = arr[0];
    if (a.cfg.id !== 100) begin
      $display("FAILED: Test 3 - arr[0].cfg.id = %0d, expected 100 (unchanged)", a.cfg.id);
      $finish;
    end
    $display("Test 3 PASSED");

    // Test 4: Assignment to null property
    $display("Test 4: Assignment to initially null property");
    arr = new[2];
    arr[0] = new();
    arr[1] = new();
    // cfg is initially null

    cfg = new(500);
    arr[0].cfg = cfg;

    a = arr[0];
    if (a.cfg == null) begin
      $display("FAILED: Test 4 - arr[0].cfg still null after assignment");
      $finish;
    end
    if (a.cfg.id !== 500) begin
      $display("FAILED: Test 4 - arr[0].cfg.id = %0d, expected 500", a.cfg.id);
      $finish;
    end
    $display("Test 4 PASSED");

    $display("PASSED");
  end
endmodule
