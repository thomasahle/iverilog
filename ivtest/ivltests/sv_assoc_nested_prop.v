// Test associative array methods on nested class properties
// This tests patterns like: outer_obj.inner_obj.assoc_array.method(key)

module test;

  // Inner class with associative array property
  class Config;
    bit [7:0] memory[int];  // Associative array with int keys
    string name;

    function new(string n);
      name = n;
    endfunction

    function void store(int addr, bit [7:0] data);
      memory[addr] = data;
    endfunction

    function bit [7:0] load(int addr);
      return memory[addr];
    endfunction
  endclass

  // Outer class containing Config object
  class Environment;
    Config cfg;

    function new();
      cfg = new("test_config");
    endfunction

    // Test exists through nested property
    function int check_exists(int addr);
      return cfg.memory.exists(addr);
    endfunction

    // Test num through nested property
    function int get_count();
      return cfg.memory.num();
    endfunction

    // Test size through nested property
    function int get_size();
      return cfg.memory.size();
    endfunction

    // Note: delete() through nested properties not yet supported as task call
  endclass

  Environment env;
  int passed;
  int result;

  initial begin
    passed = 1;
    env = new();

    $display("Testing associative array methods on nested class properties:");

    // Test num/size on empty nested array
    result = env.get_count();
    if (result != 0) begin
      $display("FAILED: get_count on empty should return 0, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: get_count on empty = %0d", result);

    result = env.get_size();
    if (result != 0) begin
      $display("FAILED: get_size on empty should return 0, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: get_size on empty = %0d", result);

    // Test exists on empty nested array
    result = env.check_exists(100);
    if (result != 0) begin
      $display("FAILED: check_exists(100) on empty should return 0, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: check_exists(100) on empty = %0d", result);

    // Add some entries through the inner object
    env.cfg.store(100, 8'hAA);
    env.cfg.store(200, 8'hBB);
    env.cfg.store(300, 8'hCC);

    // Test num after adding entries
    result = env.get_count();
    if (result != 3) begin
      $display("FAILED: get_count should return 3, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: get_count = %0d", result);

    // Test exists with existing key
    result = env.check_exists(200);
    if (result != 1) begin
      $display("FAILED: check_exists(200) should return 1, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: check_exists(200) = %0d", result);

    // Test exists with non-existing key
    result = env.check_exists(999);
    if (result != 0) begin
      $display("FAILED: check_exists(999) should return 0, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: check_exists(999) = %0d", result);

    // Test direct nested property access: env.cfg.memory.exists(key)
    result = env.cfg.memory.exists(100);
    if (result != 1) begin
      $display("FAILED: env.cfg.memory.exists(100) should return 1, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: env.cfg.memory.exists(100) = %0d", result);

    result = env.cfg.memory.num();
    if (result != 3) begin
      $display("FAILED: env.cfg.memory.num() should return 3, got %0d", result);
      passed = 0;
    end else
      $display("PASSED: env.cfg.memory.num() = %0d", result);

    $display("");
    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end

endmodule
