// Test parameterized class property type override
// When a parameterized class is specialized (e.g., class<int> from class<T>),
// property types should be correctly overridden without duplicating indices.
// Methods compiled for the template should access the same property indices
// as direct property assignments.

module test;
  // Base class with some properties
  class base_class;
    int prop_a;
    string prop_b;

    function new();
      prop_a = 0;
      prop_b = "";
    endfunction
  endclass

  // Parameterized class extending base
  class param_class #(type T = int) extends base_class;
    T my_data;
    int prop_c;

    function new();
      super.new();
      prop_c = 0;
    endfunction

    // Method that accesses properties - compiled with template indices
    function void show_data();
      $display("my_data = %0d, prop_c = %0d", my_data, prop_c);
    endfunction

    function int get_data();
      return my_data;
    endfunction

    function int get_prop_c();
      return prop_c;
    endfunction
  endclass

  // Class extending a specialization
  class derived extends param_class #(int);
    int my_extra;

    function new();
      super.new();
      my_extra = 99;
    endfunction
  endclass

  // Another specialization with different type
  class string_derived extends param_class #(string);
    function new();
      super.new();
    endfunction
  endclass

  int errors = 0;

  initial begin
    derived d;
    string_derived sd;

    // Test 1: Basic parameterized class property access
    d = new();
    d.my_data = 42;
    d.prop_c = 100;

    // Verify method returns correct values (tests property index consistency)
    if (d.get_data() !== 42) begin
      $display("FAILED: get_data() returned %0d, expected 42", d.get_data());
      errors++;
    end

    if (d.get_prop_c() !== 100) begin
      $display("FAILED: get_prop_c() returned %0d, expected 100", d.get_prop_c());
      errors++;
    end

    // Test 2: Direct property access should match method access
    if (d.my_data !== 42) begin
      $display("FAILED: d.my_data = %0d, expected 42", d.my_data);
      errors++;
    end

    if (d.prop_c !== 100) begin
      $display("FAILED: d.prop_c = %0d, expected 100", d.prop_c);
      errors++;
    end

    // Test 3: Derived class's own properties work
    if (d.my_extra !== 99) begin
      $display("FAILED: d.my_extra = %0d, expected 99", d.my_extra);
      errors++;
    end

    // Test 4: Base class properties still accessible
    d.prop_a = 77;
    d.prop_b = "hello";
    if (d.prop_a !== 77) begin
      $display("FAILED: d.prop_a = %0d, expected 77", d.prop_a);
      errors++;
    end

    // Test 5: String specialization works
    sd = new();
    sd.my_data = "test string";
    sd.prop_c = 200;

    if (sd.get_prop_c() !== 200) begin
      $display("FAILED: sd.get_prop_c() returned %0d, expected 200", sd.get_prop_c());
      errors++;
    end

    // Summary
    if (errors == 0) begin
      $display("PASSED");
    end else begin
      $display("FAILED with %0d errors", errors);
    end

    $finish;
  end
endmodule
