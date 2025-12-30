// Test that extra constructor arguments are silently ignored
// This supports UVM factory pattern where type_id::create() always passes
// (name, parent) but object constructors may only take (name)

class uvm_object_stub;
  string m_name;

  // Only 1 argument - typical for uvm_object subclasses
  function new(string name = "");
    m_name = name;
  endfunction

  function string get_name();
    return m_name;
  endfunction
endclass

class uvm_component_stub;
  string m_name;
  uvm_component_stub m_parent;

  // 2 arguments - typical for uvm_component subclasses
  function new(string name = "", uvm_component_stub parent = null);
    m_name = name;
    m_parent = parent;
  endfunction

  function string get_name();
    return m_name;
  endfunction
endclass

module test;
  uvm_object_stub obj;
  uvm_component_stub comp;
  int passed;

  initial begin
    passed = 1;

    // Test 1: Create object with extra arg (simulates type_id::create pattern)
    // This should work - extra parent arg is ignored
    obj = new("test_obj", null);
    if (obj.get_name() != "test_obj") begin
      $display("FAILED: Test 1 - obj.get_name() = %s, expected 'test_obj'", obj.get_name());
      passed = 0;
    end

    // Test 2: Create component with correct number of args
    comp = new("test_comp", null);
    if (comp.get_name() != "test_comp") begin
      $display("FAILED: Test 2 - comp.get_name() = %s, expected 'test_comp'", comp.get_name());
      passed = 0;
    end

    // Test 3: Create object with just name (normal case)
    obj = new("simple_obj");
    if (obj.get_name() != "simple_obj") begin
      $display("FAILED: Test 3 - obj.get_name() = %s, expected 'simple_obj'", obj.get_name());
      passed = 0;
    end

    if (passed)
      $display("PASSED");
    else
      $display("FAILED");
  end
endmodule
