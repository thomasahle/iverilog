// Minimal test for unpacked struct with mixed members
module sv_struct_string_simple;
   typedef struct {
      int id;
      string name;
   } item_t;

   item_t item;
   int x;

   initial begin
      item.id = 42;
      x = item.id;  // rvalue access
      if (x == 42)
         $display("PASSED");
      else
         $display("FAILED: x=%0d, expected 42", x);
   end
endmodule
