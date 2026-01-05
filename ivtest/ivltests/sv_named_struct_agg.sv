// Test named struct aggregate patterns
// SystemVerilog allows: '{member: value, ...} syntax for struct initialization

module test;
  typedef struct {
    int x;
    int y;
    int z;
  } point_t;

  typedef struct packed {
    logic [7:0] r;
    logic [7:0] g;
    logic [7:0] b;
  } color_t;

  typedef struct {
    string name;
    int value;
    bit valid;
  } config_t;

  point_t p1, p2, p3;
  color_t c1, c2;
  config_t cfg1, cfg2;

  initial begin
    // Test 1: Basic named struct aggregate
    $display("Test 1: Basic named struct aggregate");
    p1 = '{x: 10, y: 20, z: 30};
    if (p1.x !== 10 || p1.y !== 20 || p1.z !== 30) begin
      $display("FAILED: Test 1 - p1 = {%0d, %0d, %0d}", p1.x, p1.y, p1.z);
      $finish;
    end
    $display("Test 1 PASSED: p1 = {%0d, %0d, %0d}", p1.x, p1.y, p1.z);

    // Test 2: Different order of members
    $display("Test 2: Different member order");
    p2 = '{z: 300, x: 100, y: 200};
    if (p2.x !== 100 || p2.y !== 200 || p2.z !== 300) begin
      $display("FAILED: Test 2 - p2 = {%0d, %0d, %0d}", p2.x, p2.y, p2.z);
      $finish;
    end
    $display("Test 2 PASSED: p2 = {%0d, %0d, %0d}", p2.x, p2.y, p2.z);

    // Test 3: Packed struct with named aggregate
    $display("Test 3: Packed struct");
    c1 = '{r: 8'hFF, g: 8'h80, b: 8'h00};
    if (c1.r !== 8'hFF || c1.g !== 8'h80 || c1.b !== 8'h00) begin
      $display("FAILED: Test 3 - c1 = {%02x, %02x, %02x}", c1.r, c1.g, c1.b);
      $finish;
    end
    $display("Test 3 PASSED: c1 = {%02x, %02x, %02x}", c1.r, c1.g, c1.b);

    // Test 4: Using expressions in named aggregate
    $display("Test 4: Expressions in aggregate");
    p3 = '{x: 5 + 5, y: 10 * 2, z: 100 / 2};
    if (p3.x !== 10 || p3.y !== 20 || p3.z !== 50) begin
      $display("FAILED: Test 4 - p3 = {%0d, %0d, %0d}", p3.x, p3.y, p3.z);
      $finish;
    end
    $display("Test 4 PASSED: p3 = {%0d, %0d, %0d}", p3.x, p3.y, p3.z);

    // Test 5: Struct with string member
    $display("Test 5: Struct with string");
    cfg1 = '{name: "test_config", value: 42, valid: 1'b1};
    if (cfg1.value !== 42 || cfg1.valid !== 1'b1) begin
      $display("FAILED: Test 5 - cfg1.value = %0d, valid = %b", cfg1.value, cfg1.valid);
      $finish;
    end
    $display("Test 5 PASSED: cfg1 = {%s, %0d, %b}", cfg1.name, cfg1.value, cfg1.valid);

    // Test 6: Reassignment with named aggregate
    $display("Test 6: Reassignment");
    p1 = '{x: 1, y: 2, z: 3};
    p1 = '{x: 11, y: 22, z: 33};
    if (p1.x !== 11 || p1.y !== 22 || p1.z !== 33) begin
      $display("FAILED: Test 6 - p1 = {%0d, %0d, %0d}", p1.x, p1.y, p1.z);
      $finish;
    end
    $display("Test 6 PASSED: p1 = {%0d, %0d, %0d}", p1.x, p1.y, p1.z);

    $display("PASSED");
  end
endmodule
