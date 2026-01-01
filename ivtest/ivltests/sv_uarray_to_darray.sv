// Test assignment of unpacked fixed-size array to dynamic array
// This is allowed in SystemVerilog - the dynamic array is resized
// and elements are copied.

module test;

   typedef struct {
      bit [7:0] data[4];  // Fixed-size array
   } packet_t;

   class Transaction;
      bit [7:0] payload[];  // Dynamic array
   endclass

   initial begin
      packet_t pkt;
      Transaction tr;
      int pass = 1;

      // Initialize fixed-size array in struct
      pkt.data[0] = 8'hAA;
      pkt.data[1] = 8'hBB;
      pkt.data[2] = 8'hCC;
      pkt.data[3] = 8'hDD;

      // Create transaction and assign fixed-size array to dynamic array
      tr = new();
      tr.payload = pkt.data;  // This is the operation we're testing

      // Verify the copy
      if (tr.payload.size() != 4) begin
         $display("FAIL: payload size = %0d, expected 4", tr.payload.size());
         pass = 0;
      end
      if (tr.payload[0] !== 8'hAA) begin
         $display("FAIL: payload[0] = %h, expected AA", tr.payload[0]);
         pass = 0;
      end
      if (tr.payload[1] !== 8'hBB) begin
         $display("FAIL: payload[1] = %h, expected BB", tr.payload[1]);
         pass = 0;
      end
      if (tr.payload[2] !== 8'hCC) begin
         $display("FAIL: payload[2] = %h, expected CC", tr.payload[2]);
         pass = 0;
      end
      if (tr.payload[3] !== 8'hDD) begin
         $display("FAIL: payload[3] = %h, expected DD", tr.payload[3]);
         pass = 0;
      end

      if (pass)
         $display("PASSED");
      else
         $display("FAILED");
   end

endmodule
