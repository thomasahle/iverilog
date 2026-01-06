// Test string concatenation with method return values
// This tests that string concatenation correctly handles strings
// returned from class methods without mixing vec4/string stacks

class StringContainer;
  string name;

  function new(string n);
    name = n;
  endfunction

  function string get_name();
    return name;
  endfunction
endclass

module top;
  StringContainer obj;
  string child_name;
  string full_name;
  int pass_count = 0;

  initial begin
    // Test basic string property access
    obj = new("parent");
    child_name = "child";

    // Test 1: Direct property access in concatenation
    full_name = {obj.name, ".", child_name};
    if (full_name == "parent.child") begin
      $display("Test 1 PASSED: Property concat");
      pass_count++;
    end else begin
      $display("Test 1 FAILED: Got '%s', expected 'parent.child'", full_name);
    end

    // Test 2: Method call return value in concatenation
    full_name = {obj.get_name(), ".", child_name};
    if (full_name == "parent.child") begin
      $display("Test 2 PASSED: Method call concat");
      pass_count++;
    end else begin
      $display("Test 2 FAILED: Got '%s', expected 'parent.child'", full_name);
    end

    // Test 3: Multiple method calls in concatenation
    full_name = {obj.get_name(), "/", obj.get_name()};
    if (full_name == "parent/parent") begin
      $display("Test 3 PASSED: Multiple method calls");
      pass_count++;
    end else begin
      $display("Test 3 FAILED: Got '%s', expected 'parent/parent'", full_name);
    end

    // Test 4: Method call with string variables
    full_name = {child_name, ".", obj.get_name()};
    if (full_name == "child.parent") begin
      $display("Test 4 PASSED: Variable then method");
      pass_count++;
    end else begin
      $display("Test 4 FAILED: Got '%s', expected 'child.parent'", full_name);
    end

    // Summary
    if (pass_count == 4)
      $display("PASSED");
    else
      $display("FAILED: %0d/4 tests passed", pass_count);

    $finish;
  end
endmodule
