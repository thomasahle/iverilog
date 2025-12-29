// Test that soft constraints don't cause randomize() to fail
// This tests that constraints are treated as soft by default,
// so randomize() returns success even if constraints aren't fully satisfied.

module test;
  int errors = 0;
  int pass_count = 0;

  // Class with simple soft constraints
  class simple_constrained;
    rand bit [7:0] value;
    rand bit [3:0] small_value;

    // Soft constraint - should not cause randomize to fail
    constraint value_range { soft value inside {[10:50]}; }
    constraint small_range { soft small_value < 8; }

    function new();
    endfunction
  endclass

  // Class with potentially unsatisfiable constraint (if hard)
  class tricky_constrained;
    rand bit [3:0] a;
    rand bit [3:0] b;

    // These constraints together are hard to satisfy randomly
    // but as soft constraints, randomize should still succeed
    constraint sum_constraint { soft a + b == 15; }
    constraint diff_constraint { soft a > b; }

    function new();
    endfunction
  endclass

  // Class with enum constraint
  class enum_constrained;
    typedef enum bit [1:0] { RED, GREEN, BLUE, YELLOW } color_e;
    rand color_e color;

    // Soft constraint to prefer certain values
    constraint prefer_primary { soft color inside {RED, GREEN, BLUE}; }

    function new();
    endfunction
  endclass

  initial begin
    simple_constrained sc;
    tricky_constrained tc;
    enum_constrained ec;
    int result;

    $display("=== Test 1: Simple soft constraints ===");
    sc = new();
    repeat(5) begin
      result = sc.randomize();
      if (result == 0) begin
        $display("FAILED: randomize() returned 0 for simple_constrained");
        errors++;
      end else begin
        pass_count++;
      end
    end
    $display("simple_constrained: %0d/5 randomize calls succeeded", pass_count);

    $display("");
    $display("=== Test 2: Tricky soft constraints ===");
    tc = new();
    pass_count = 0;
    repeat(5) begin
      result = tc.randomize();
      if (result == 0) begin
        $display("FAILED: randomize() returned 0 for tricky_constrained");
        errors++;
      end else begin
        pass_count++;
      end
    end
    $display("tricky_constrained: %0d/5 randomize calls succeeded", pass_count);

    $display("");
    $display("=== Test 3: Enum soft constraints ===");
    ec = new();
    pass_count = 0;
    repeat(5) begin
      result = ec.randomize();
      if (result == 0) begin
        $display("FAILED: randomize() returned 0 for enum_constrained");
        errors++;
      end else begin
        pass_count++;
      end
    end
    $display("enum_constrained: %0d/5 randomize calls succeeded", pass_count);

    $display("");
    $display("============================================");
    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
