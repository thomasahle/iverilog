// Test $cast for class type checking and assignment

class Base;
   int value;
   function new();
      value = 100;
   endfunction
endclass

class Derived extends Base;
   string name;
   function new();
      super.new();
      name = "derived";
      value = 200;
   endfunction
endclass

class Other;
   int data;
   function new();
      data = 999;
   endfunction
endclass

module test;
   Base base_obj;
   Derived derived_obj;
   Other other_obj;
   Base cast_target;

   initial begin
      // Create objects
      derived_obj = new();
      other_obj = new();
      base_obj = new();

      // Test 1: Cast derived to base (should succeed)
      if ($cast(cast_target, derived_obj)) begin
         if (cast_target.value == 200) begin
            $display("Test 1 PASSED: Cast Derived->Base succeeded, value=%0d", cast_target.value);
         end else begin
            $display("Test 1 FAILED: Wrong value after cast");
            $finish;
         end
      end else begin
         $display("Test 1 FAILED: Cast Derived->Base should succeed");
         $finish;
      end

      // Test 2: Cast base to base (should succeed)
      if ($cast(cast_target, base_obj)) begin
         if (cast_target.value == 100) begin
            $display("Test 2 PASSED: Cast Base->Base succeeded, value=%0d", cast_target.value);
         end else begin
            $display("Test 2 FAILED: Wrong value after cast");
            $finish;
         end
      end else begin
         $display("Test 2 FAILED: Cast Base->Base should succeed");
         $finish;
      end

      // Note: $cast(base_type, other_type) - type checking at compile time
      // In SV, this would be caught at compile time in many cases.
      // For dynamic checking, we typically cast through a common base.

      $display("All tests PASSED");
      $finish;
   end
endmodule
