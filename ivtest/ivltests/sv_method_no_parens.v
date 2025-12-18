// Test method call without parentheses
// SystemVerilog allows calling methods without () when they have no required args

class Packet;
  int data;

  function new(int d = 0);
    data = d;
  endfunction

  // Method with no required arguments (only 'this')
  function string sprint;
    return $sformatf("Packet{data=%0d}", data);
  endfunction

  // Method with no arguments at all (static-like but not static)
  function int get_data;
    return data;
  endfunction

  // Method with required argument - should NOT work without parens
  function int add(int x);
    return data + x;
  endfunction
endclass

module test;
  Packet pkt;
  string s;
  int val;

  initial begin
    pkt = new(42);

    // Call sprint without parentheses - should work
    s = pkt.sprint;
    $display("sprint result: %s", s);

    // Call get_data without parentheses - should work
    val = pkt.get_data;
    $display("get_data result: %0d", val);

    // Use in expression
    if (pkt.get_data == 42) begin
      $display("PASSED");
    end else begin
      $display("FAILED");
    end

    $finish;
  end
endmodule
