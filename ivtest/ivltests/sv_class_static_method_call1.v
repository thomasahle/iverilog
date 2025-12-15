// Test basic static method call using class::method() syntax
// This tests that class names defined at $unit scope are properly
// recognized as TYPE_IDENTIFIER when followed by ::

class helper;
  static int call_count = 0;

  static function void do_something(int a);
    $display("do_something(%0d)", a);
    call_count = call_count + 1;
  endfunction

  static function int get_count();
    return call_count;
  endfunction
endclass

module test;
  initial begin
    // Basic static method call - this is the key test case
    helper::do_something(10);

    if (helper::get_count() != 1) begin
      $display("FAILED: call_count=%0d, expected 1", helper::get_count());
      $finish;
    end

    helper::do_something(20);
    helper::do_something(30);

    if (helper::get_count() != 3) begin
      $display("FAILED: call_count=%0d, expected 3", helper::get_count());
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
