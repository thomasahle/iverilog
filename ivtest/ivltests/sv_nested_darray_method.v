// Test method calls on dynamic array elements accessed through properties
// Pattern: obj.darray_prop[i].method()

module test;

  // Class with a method
  class Config;
    string name;
    int value;

    function new(string n, int v);
      name = n;
      value = v;
    endfunction

    function string get_info();
      return $sformatf("%s=%0d", name, value);
    endfunction
  endclass

  // Container with dynamic array
  class Container;
    Config configs[];

    function new();
      configs = new[3];
      configs[0] = new("cfg0", 100);
      configs[1] = new("cfg1", 200);
      configs[2] = new("cfg2", 300);
    endfunction
  endclass

  Container c;
  string result;
  int passed;

  initial begin
    passed = 1;
    c = new();

    $display("Testing method calls on darray property elements:");

    // Test: c.configs[i].method()
    // Direct access to dynamic array property element and method call
    for (int i = 0; i < 3; i++) begin
      result = c.configs[i].get_info();
      $display("c.configs[%0d].get_info() = %s", i, result);
      case (i)
        0: if (result != "cfg0=100") begin $display("FAILED"); passed = 0; end
        1: if (result != "cfg1=200") begin $display("FAILED"); passed = 0; end
        2: if (result != "cfg2=300") begin $display("FAILED"); passed = 0; end
      endcase
    end

    $display("");
    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end

endmodule
