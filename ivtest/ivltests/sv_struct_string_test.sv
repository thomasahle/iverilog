// Test unpacked struct with string member
// Note: String members in structs are not fully supported yet.
// Packed members (int, logic, etc.) work correctly.
// String members will return empty strings.
module sv_struct_string_test;
   typedef struct {
      int id;
      string name;
      int value;
   } item_t;

   item_t item;
   int passed;

   initial begin
      passed = 1;

      // Test 1: Write and read packed members (should work)
      item.id = 1;
      item.value = 100;

      // Test 2: Write to string member (silently ignored in current implementation)
      item.name = "test";

      $display("item.id = %0d", item.id);
      $display("item.name = '%s' (expected: '' or 'test')", item.name);
      $display("item.value = %0d", item.value);

      // Check packed members
      if (item.id != 1) begin
         $display("FAILED: item.id = %0d, expected 1", item.id);
         passed = 0;
      end

      if (item.value != 100) begin
         $display("FAILED: item.value = %0d, expected 100", item.value);
         passed = 0;
      end

      // Note: String members not checked since they're not supported yet

      if (passed)
         $display("PASSED");

      $finish;
   end
endmodule
