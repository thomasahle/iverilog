// Test inline constraints with variables from different scopes
// Tests: module scope, class properties, and local variables

class inner_class;
   rand int value;
   constraint c_default { value >= 0; value <= 1000; }
endclass

class outer_class;
   int my_bound;  // Class property
   inner_class inner;

   function new();
      inner = new();
      my_bound = 42;
   endfunction

   // Test: randomize with class property using ==
   function int test_with_class_prop_eq();
      int result;
      result = inner.randomize() with { value == my_bound; };
      if (result && inner.value == my_bound) return 1;
      return 0;
   endfunction

   // Test: randomize with local variable using ==
   function int test_with_local_var_eq();
      int local_val = 77;
      int result;
      result = inner.randomize() with { value == local_val; };
      if (result && inner.value == local_val) return 1;
      return 0;
   endfunction

   // Test: randomize with class property using <=
   function int test_with_class_prop_le();
      int result;
      my_bound = 50;
      result = inner.randomize() with { value <= my_bound; };
      if (result && inner.value <= my_bound) return 1;
      return 0;
   endfunction
endclass

module test;
   int module_val = 99;
   inner_class ic;
   outer_class oc;
   int passed = 0;
   int failed = 0;

   initial begin
      ic = new();
      oc = new();

      // Test 1: Module scope variable with ==
      begin
         int result;
         result = ic.randomize() with { value == module_val; };
         if (result && ic.value == module_val)
            passed++;
         else
            failed++;
      end

      // Test 2: Class property with ==
      if (oc.test_with_class_prop_eq())
         passed++;
      else
         failed++;

      // Test 3: Local variable with ==
      if (oc.test_with_local_var_eq())
         passed++;
      else
         failed++;

      // Test 4: Class property with <=
      if (oc.test_with_class_prop_le())
         passed++;
      else
         failed++;

      if (failed == 0)
         $display("PASSED");
      else
         $display("FAILED - %0d tests failed", failed);
   end
endmodule
