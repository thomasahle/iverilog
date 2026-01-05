// Test that unpacked struct WITHOUT string member does NOT show warning
// sv_struct_string_member.sv

module sv_struct_string_member;
   // Struct without string member - should NOT trigger warning
   typedef struct {
      int id;
      int value;
      bit [7:0] data;
   } struct_without_string_t;

   struct_without_string_t item;

   initial begin
      item.id = 1;
      item.value = 100;
      item.data = 8'hAB;

      $display("item.id = %0d", item.id);
      $display("item.value = %0d", item.value);
      $display("item.data = %h", item.data);

      if (item.id == 1 && item.value == 100 && item.data == 8'hAB)
         $display("PASSED");
      else
         $display("FAILED");

      $finish;
   end

endmodule
