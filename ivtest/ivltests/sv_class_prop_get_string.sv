// Test get_string on class properties of various types
// This tests that VVP doesn't crash when trying to get string
// representation of different property types

class TestContainer;
  int    int_prop;
  bit [7:0] bit_prop;
  logic [15:0] logic_prop;
  real   real_prop;
  string string_prop;
  int    queue_prop[$];

  function new();
    int_prop = 42;
    bit_prop = 8'hAB;
    logic_prop = 16'h1234;
    real_prop = 3.14;
    string_prop = "hello";
    queue_prop.push_back(1);
    queue_prop.push_back(2);
  endfunction
endclass

module test;
  TestContainer tc;

  initial begin
    tc = new();

    // Access properties in various ways that may trigger get_string
    $display("int_prop = %0d", tc.int_prop);
    $display("bit_prop = %h", tc.bit_prop);
    $display("logic_prop = %h", tc.logic_prop);
    $display("real_prop = %f", tc.real_prop);
    $display("string_prop = %s", tc.string_prop);
    $display("queue_prop size = %0d", tc.queue_prop.size());

    // Use $sformatf which may call get_string
    begin
      string s;
      s = $sformatf("int=%0d, bit=%h", tc.int_prop, tc.bit_prop);
      $display("Formatted: %s", s);
    end

    $display("PASSED");
  end
endmodule
