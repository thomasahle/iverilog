// Test queue of structs with direct member access
// Verifies: typedef struct with queue operations
// Tests direct pkt_queue[i].member access pattern

module test;

  typedef struct {
    bit [7:0] data;
    bit [3:0] addr;
    bit valid;
  } packet_t;

  packet_t pkt_queue[$];
  packet_t pkt;
  int i;

  initial begin
    // Push struct values onto queue
    pkt.data = 8'hAA;
    pkt.addr = 4'h1;
    pkt.valid = 1;
    pkt_queue.push_back(pkt);

    pkt.data = 8'hBB;
    pkt.addr = 4'h2;
    pkt.valid = 1;
    pkt_queue.push_back(pkt);

    pkt.data = 8'hCC;
    pkt.addr = 4'h3;
    pkt.valid = 0;
    pkt_queue.push_back(pkt);

    $display("Queue size: %0d", pkt_queue.size());
    if (pkt_queue.size() != 3) begin
      $display("FAILED: Expected size 3");
      $finish;
    end

    // Direct member access on queue elements
    $display("pkt_queue[0].data = %h", pkt_queue[0].data);
    $display("pkt_queue[0].addr = %h", pkt_queue[0].addr);
    $display("pkt_queue[1].data = %h", pkt_queue[1].data);
    $display("pkt_queue[1].addr = %h", pkt_queue[1].addr);
    $display("pkt_queue[2].data = %h", pkt_queue[2].data);
    $display("pkt_queue[2].valid = %b", pkt_queue[2].valid);

    // Verify direct member access
    if (pkt_queue[0].data !== 8'hAA) begin
      $display("FAILED: Expected pkt_queue[0].data = AA, got %h", pkt_queue[0].data);
      $finish;
    end

    if (pkt_queue[1].addr !== 4'h2) begin
      $display("FAILED: Expected pkt_queue[1].addr = 2, got %h", pkt_queue[1].addr);
      $finish;
    end

    if (pkt_queue[2].valid !== 0) begin
      $display("FAILED: Expected pkt_queue[2].valid = 0, got %b", pkt_queue[2].valid);
      $finish;
    end

    // Pop and verify
    pkt = pkt_queue.pop_front();
    if (pkt.data !== 8'hAA || pkt.addr !== 4'h1) begin
      $display("FAILED: pop_front returned wrong values");
      $finish;
    end

    // Verify $ index with direct member access
    $display("pkt_queue[$].data = %h", pkt_queue[$].data);
    if (pkt_queue[$].data !== 8'hCC) begin
      $display("FAILED: Expected pkt_queue[$].data = CC, got %h", pkt_queue[$].data);
      $finish;
    end

    // Iterate through remaining using direct access
    for (i = 0; i < pkt_queue.size(); i++) begin
      $display("pkt_queue[%0d]: data=%h addr=%h valid=%b",
               i, pkt_queue[i].data, pkt_queue[i].addr, pkt_queue[i].valid);
    end

    // Verify all values with combined condition
    if (pkt_queue[0].data === 8'hBB && pkt_queue[0].addr === 4'h2 &&
        pkt_queue[1].data === 8'hCC && pkt_queue[1].addr === 4'h3) begin
      $display("PASSED");
    end else begin
      $display("FAILED: Remaining queue values incorrect");
    end
    $finish;
  end

endmodule
