// Test virtual method inheritance and dispatch
// This tests that virtual methods are correctly inherited from parent classes
// and that overridden methods are correctly dispatched

module test;
  int errors = 0;
  string results[$];

  // Base class with virtual methods
  class base_class;
    string name;

    function new(string n = "base");
      name = n;
    endfunction

    // Virtual method that will be inherited but not overridden by some classes
    virtual function void inherited_method();
      results.push_back($sformatf("%s.inherited_method (base)", name));
    endfunction

    // Virtual method that will be overridden
    virtual function void overridden_method();
      results.push_back($sformatf("%s.overridden_method (base)", name));
    endfunction

    // Non-virtual method for comparison
    function void non_virtual_method();
      results.push_back($sformatf("%s.non_virtual_method (base)", name));
    endfunction
  endclass

  // Middle class - overrides one method, inherits the other
  class middle_class extends base_class;
    function new(string n = "middle");
      super.new(n);
    endfunction

    // Override overridden_method
    virtual function void overridden_method();
      results.push_back($sformatf("%s.overridden_method (middle)", name));
    endfunction

    // inherited_method is NOT overridden - should use base_class version

    // Add a new method
    virtual function void middle_only_method();
      results.push_back($sformatf("%s.middle_only_method", name));
    endfunction
  endclass

  // Derived class - doesn't override anything, should inherit from middle
  class derived_class extends middle_class;
    function new(string n = "derived");
      super.new(n);
    endfunction

    // No overrides - all methods should be inherited
  endclass

  // Another derived class that overrides inherited_method
  class derived_override_class extends middle_class;
    function new(string n = "derived_override");
      super.new(n);
    endfunction

    // Override the method that middle_class inherited from base_class
    virtual function void inherited_method();
      results.push_back($sformatf("%s.inherited_method (derived_override)", name));
    endfunction
  endclass

  // Test wrapper class (like UVM component)
  class test_wrapper;
    base_class obj;

    function new(base_class o);
      obj = o;
    endfunction

    // Call methods through base class reference (tests virtual dispatch)
    function void call_all_methods();
      obj.inherited_method();
      obj.overridden_method();
      obj.non_virtual_method();
    endfunction
  endclass

  initial begin
    base_class b;
    middle_class m;
    derived_class d;
    derived_override_class do_obj;
    test_wrapper tw;

    // Test 1: Base class methods
    $display("Test 1: Base class methods");
    b = new("base_obj");
    tw = new(b);
    tw.call_all_methods();

    if (results[0] != "base_obj.inherited_method (base)") begin
      $display("FAILED: Expected 'base_obj.inherited_method (base)', got '%s'", results[0]);
      errors++;
    end else $display("PASSED: base inherited_method");

    if (results[1] != "base_obj.overridden_method (base)") begin
      $display("FAILED: Expected 'base_obj.overridden_method (base)', got '%s'", results[1]);
      errors++;
    end else $display("PASSED: base overridden_method");

    if (results[2] != "base_obj.non_virtual_method (base)") begin
      $display("FAILED: Expected 'base_obj.non_virtual_method (base)', got '%s'", results[2]);
      errors++;
    end else $display("PASSED: base non_virtual_method");

    results.delete();

    // Test 2: Middle class - inherited method from base, overridden method from middle
    $display("\nTest 2: Middle class methods");
    m = new("middle_obj");
    tw = new(m);
    tw.call_all_methods();

    if (results[0] != "middle_obj.inherited_method (base)") begin
      $display("FAILED: Expected 'middle_obj.inherited_method (base)', got '%s'", results[0]);
      errors++;
    end else $display("PASSED: middle inherited_method (from base)");

    if (results[1] != "middle_obj.overridden_method (middle)") begin
      $display("FAILED: Expected 'middle_obj.overridden_method (middle)', got '%s'", results[1]);
      errors++;
    end else $display("PASSED: middle overridden_method");

    results.delete();

    // Test 3: Derived class - should inherit everything from middle/base
    $display("\nTest 3: Derived class methods (no overrides)");
    d = new("derived_obj");
    tw = new(d);
    tw.call_all_methods();

    if (results[0] != "derived_obj.inherited_method (base)") begin
      $display("FAILED: Expected 'derived_obj.inherited_method (base)', got '%s'", results[0]);
      errors++;
    end else $display("PASSED: derived inherited_method (from base via middle)");

    if (results[1] != "derived_obj.overridden_method (middle)") begin
      $display("FAILED: Expected 'derived_obj.overridden_method (middle)', got '%s'", results[1]);
      errors++;
    end else $display("PASSED: derived overridden_method (from middle)");

    results.delete();

    // Test 4: Derived class with override
    $display("\nTest 4: Derived class with override");
    do_obj = new("do_obj");
    tw = new(do_obj);
    tw.call_all_methods();

    if (results[0] != "do_obj.inherited_method (derived_override)") begin
      $display("FAILED: Expected 'do_obj.inherited_method (derived_override)', got '%s'", results[0]);
      errors++;
    end else $display("PASSED: derived_override inherited_method (overridden)");

    if (results[1] != "do_obj.overridden_method (middle)") begin
      $display("FAILED: Expected 'do_obj.overridden_method (middle)', got '%s'", results[1]);
      errors++;
    end else $display("PASSED: derived_override overridden_method (from middle)");

    results.delete();

    // Test 5: Direct call on derived object (not through base reference)
    $display("\nTest 5: Direct call on derived object");
    d.inherited_method();
    d.overridden_method();
    m.middle_only_method();

    if (results[0] != "derived_obj.inherited_method (base)") begin
      $display("FAILED: Direct call inherited_method wrong");
      errors++;
    end else $display("PASSED: direct inherited_method call");

    if (results[1] != "derived_obj.overridden_method (middle)") begin
      $display("FAILED: Direct call overridden_method wrong");
      errors++;
    end else $display("PASSED: direct overridden_method call");

    if (results[2] != "middle_obj.middle_only_method") begin
      $display("FAILED: Direct call middle_only_method wrong");
      errors++;
    end else $display("PASSED: direct middle_only_method call");

    // Summary
    $display("\n============================================");
    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
