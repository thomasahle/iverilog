// Test for pattern matching (SV 12.6)
module test;
  typedef union tagged {
    int Valid;
    void Invalid;
  } maybe_int;

  maybe_int m;
  int result;

  initial begin
    // Test pattern matching expression (returns boolean)
    if (1 matches 1)
      $display("Pattern match 1 matches 1: OK");

    // Test wildcard pattern
    if (5 matches .x)
      $display("Pattern match with wildcard: OK");

    // Test conditional pattern matching
    result = (1 matches 1) ? 10 : 20;
    if (result == 10)
      $display("Conditional pattern match: OK");

    $display("PASSED");
  end
endmodule
