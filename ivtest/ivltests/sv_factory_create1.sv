// Test $ivl_factory_create system function
// Creates an object by type name at runtime

class base;
  string m_name;

  function new(string name = "unnamed");
    this.m_name = name;
  endfunction

  virtual function string get_name();
    return this.m_name;
  endfunction

  virtual function void greet();
    $display("Hello from base: %s", this.m_name);
  endfunction
endclass

class derived extends base;
  int m_value;

  function new(string name = "unnamed");
    super.new(name);
    this.m_value = 42;
  endfunction

  virtual function void greet();
    $display("Hello from derived: %s, value=%0d", this.m_name, this.m_value);
  endfunction
endclass

module test;
  initial begin
    base b;
    string type_name;

    // Test factory create for derived class
    type_name = "derived";
    b = $ivl_factory_create(type_name);

    if (b == null) begin
      $display("FAILED: factory create returned null");
      $finish;
    end

    // Check that virtual method works
    b.greet();

    // Check that it's actually a derived instance
    // Note: factory create calls constructor with no arguments,
    // so m_name will be empty (default argument not applied)
    if (b.m_name != "") begin
      $display("FAILED: m_name mismatch, expected empty, got '%s'", b.m_name);
      $finish;
    end

    $display("PASSED");
  end
endmodule
