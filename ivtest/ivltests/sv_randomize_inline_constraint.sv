// Test inline randomize constraint parsing
// The parser should accept randomize() with {...} syntax
// (Note: actual constraint enforcement is not yet implemented)
module test;
  class my_class;
    rand int x;
    int limit;
    int result;

    function new();
      limit = 10;
      result = 0;
    endfunction

    // Mock randomize method - constraints are parsed but not enforced
    function int randomize();
      result = $urandom % 100;
      x = result;
      return 1;
    endfunction

    function void test_constraints();
      int success;
      // Test 1: with space before {
      success = this.randomize() with { x < limit; };
      $display("Test 1: randomize() with space - success=%0d x=%0d", success, x);

      // Test 2: without space before {
      success = this.randomize() with{ x < limit; };
      $display("Test 2: randomize() without space - success=%0d x=%0d", success, x);

      // Test 3: empty constraint block
      success = this.randomize() with { };
      $display("Test 3: empty constraint - success=%0d x=%0d", success, x);
    endfunction
  endclass

  my_class obj;

  initial begin
    obj = new();
    obj.test_constraints();
    $display("PASSED");
  end
endmodule
