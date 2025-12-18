// Test extern constructor with static method declarations
// This tests that the static method flag is properly reset
// when parsing out-of-body constructor definitions.
package pkg;
  class converter;
    extern function new(string name = "converter");
    extern static function int do_convert(int val);
  endclass

  function converter::new(string name = "converter");
  endfunction

  function int converter::do_convert(int val);
    return val * 2;
  endfunction
endpackage

module test;
  import pkg::*;

  initial begin
    converter c;
    int result;
    c = new();
    result = converter::do_convert(21);
    $display("result=%0d", result);
    if (result == 42)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
