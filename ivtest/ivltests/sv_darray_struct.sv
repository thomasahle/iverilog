// Test dynamic array of structs with direct member access
// Verifies: typedef struct with dynamic array operations
// Tests direct pkt_array[i].member access pattern

module test;
  typedef struct {
    bit [7:0] data;
    bit [3:0] addr;
    bit valid;
  } packet_t;

  packet_t pkt_array[];
  packet_t pkt;
  int i;

  initial begin
    // Allocate dynamic array
    pkt_array = new[3];

    // Assign values using temp variable
    pkt.data = 8'hAA;
    pkt.addr = 4'h1;
    pkt.valid = 1;
    pkt_array[0] = pkt;

    pkt.data = 8'hBB;
    pkt.addr = 4'h2;
    pkt.valid = 1;
    pkt_array[1] = pkt;

    pkt.data = 8'hCC;
    pkt.addr = 4'h3;
    pkt.valid = 0;
    pkt_array[2] = pkt;

    $display("Array size: %0d", pkt_array.size());

    // Test direct member access on dynamic array elements
    $display("pkt_array[0].data = %h", pkt_array[0].data);
    $display("pkt_array[0].addr = %h", pkt_array[0].addr);
    $display("pkt_array[1].data = %h", pkt_array[1].data);
    $display("pkt_array[1].addr = %h", pkt_array[1].addr);
    $display("pkt_array[2].data = %h", pkt_array[2].data);
    $display("pkt_array[2].valid = %b", pkt_array[2].valid);

    // Verify direct member access
    if (pkt_array[0].data !== 8'hAA) begin
      $display("FAILED: Expected pkt_array[0].data = AA, got %h", pkt_array[0].data);
      $finish;
    end

    if (pkt_array[1].addr !== 4'h2) begin
      $display("FAILED: Expected pkt_array[1].addr = 2, got %h", pkt_array[1].addr);
      $finish;
    end

    if (pkt_array[2].valid !== 0) begin
      $display("FAILED: Expected pkt_array[2].valid = 0, got %b", pkt_array[2].valid);
      $finish;
    end

    // Iterate using direct access
    for (i = 0; i < pkt_array.size(); i++) begin
      $display("pkt_array[%0d]: data=%h addr=%h valid=%b",
               i, pkt_array[i].data, pkt_array[i].addr, pkt_array[i].valid);
    end

    // Verify all values with combined condition
    if (pkt_array[0].data === 8'hAA && pkt_array[0].addr === 4'h1 &&
        pkt_array[1].data === 8'hBB && pkt_array[1].addr === 4'h2 &&
        pkt_array[2].data === 8'hCC && pkt_array[2].addr === 4'h3) begin
      $display("PASSED");
    end else begin
      $display("FAILED: Some values incorrect");
    end
    $finish;
  end
endmodule
