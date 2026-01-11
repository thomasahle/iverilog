// Test queue of structs
// Verifies: typedef struct with queue operations
// Note: Direct member access pkt_queue[i].member is limited - use temp variable

module test;

  typedef struct {
    bit [7:0] data;
    bit [3:0] addr;
    bit valid;
  } packet_t;

  packet_t pkt_queue[$];
  packet_t pkt;
  packet_t temp;
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

    // Access struct members via temp variable (workaround)
    temp = pkt_queue[0];
    if (temp.data != 8'hAA) begin
      $display("FAILED: Expected pkt_queue[0].data = AA, got %h", temp.data);
      $finish;
    end

    temp = pkt_queue[1];
    if (temp.addr != 4'h2) begin
      $display("FAILED: Expected pkt_queue[1].addr = 2");
      $finish;
    end

    temp = pkt_queue[2];
    if (temp.valid != 0) begin
      $display("FAILED: Expected pkt_queue[2].valid = 0");
      $finish;
    end

    // Pop and verify
    pkt = pkt_queue.pop_front();
    if (pkt.data != 8'hAA || pkt.addr != 4'h1) begin
      $display("FAILED: pop_front returned wrong values");
      $finish;
    end

    // Verify $ index via temp
    temp = pkt_queue[$];
    if (temp.data != 8'hCC) begin
      $display("FAILED: Expected pkt_queue[$].data = CC");
      $finish;
    end

    // Iterate through remaining
    for (i = 0; i < pkt_queue.size(); i++) begin
      temp = pkt_queue[i];
      $display("pkt_queue[%0d]: data=%h addr=%h valid=%b",
               i, temp.data, temp.addr, temp.valid);
    end

    $display("PASSED");
    $finish;
  end

endmodule
