// Test min/max with (item.field) clause for queues of packed structs
module test;

  typedef struct packed {
    bit [7:0] id;
    bit [7:0] prio;  // renamed from priority which is a keyword
  } task_t;

  task_t q[$];
  task_t result[$];
  task_t pkt;
  int pass;

  initial begin
    pass = 1;

    // Add elements with different priorities
    pkt.id = 8'h01; pkt.prio = 8'h50; q.push_back(pkt);  // prio 80
    pkt.id = 8'h02; pkt.prio = 8'h10; q.push_back(pkt);  // prio 16 - min
    pkt.id = 8'h03; pkt.prio = 8'hC0; q.push_back(pkt);  // prio 192 - max
    pkt.id = 8'h04; pkt.prio = 8'h30; q.push_back(pkt);  // prio 48
    pkt.id = 8'h05; pkt.prio = 8'h10; q.push_back(pkt);  // prio 16 - also min (tie)

    $display("Queue contents:");
    for (int i = 0; i < q.size(); i = i + 1) begin
      $display("  q[%0d]: id=0x%02h, prio=0x%02h", i, q[i].id, q[i].prio);
    end

    // Test min with (item.prio)
    result = q.min with (item.prio);
    $display("min with (item.prio): %0d element(s)", result.size());
    for (int i = 0; i < result.size(); i = i + 1) begin
      $display("  result[%0d]: id=0x%02h, prio=0x%02h", i, result[i].id, result[i].prio);
    end

    // Should return elements with prio 0x10 (id 0x02 and 0x05)
    if (result.size() != 2) begin
      $display("FAIL: Expected 2 min elements, got %0d", result.size());
      pass = 0;
    end else begin
      if (result[0].prio != 8'h10 || result[1].prio != 8'h10) begin
        $display("FAIL: Min elements should have prio 0x10");
        pass = 0;
      end
    end

    // Test max with (item.prio)
    result = q.max with (item.prio);
    $display("max with (item.prio): %0d element(s)", result.size());
    for (int i = 0; i < result.size(); i = i + 1) begin
      $display("  result[%0d]: id=0x%02h, prio=0x%02h", i, result[i].id, result[i].prio);
    end

    // Should return element with prio 0xC0 (id 0x03)
    if (result.size() != 1) begin
      $display("FAIL: Expected 1 max element, got %0d", result.size());
      pass = 0;
    end else begin
      if (result[0].id != 8'h03 || result[0].prio != 8'hC0) begin
        $display("FAIL: Max element should be id=0x03, prio=0xC0");
        pass = 0;
      end
    end

    // Test min with (item.id)
    result = q.min with (item.id);
    $display("min with (item.id): %0d element(s)", result.size());
    for (int i = 0; i < result.size(); i = i + 1) begin
      $display("  result[%0d]: id=0x%02h, prio=0x%02h", i, result[i].id, result[i].prio);
    end

    // Should return element with id 0x01
    if (result.size() != 1 || result[0].id != 8'h01) begin
      $display("FAIL: Min id element should be id=0x01");
      pass = 0;
    end

    // Test max with (item.id)
    result = q.max with (item.id);
    $display("max with (item.id): %0d element(s)", result.size());
    for (int i = 0; i < result.size(); i = i + 1) begin
      $display("  result[%0d]: id=0x%02h, prio=0x%02h", i, result[i].id, result[i].prio);
    end

    // Should return element with id 0x05
    if (result.size() != 1 || result[0].id != 8'h05) begin
      $display("FAIL: Max id element should be id=0x05");
      pass = 0;
    end

    // Test with empty queue
    q.delete();
    result = q.min with (item.prio);
    $display("min with empty queue: %0d element(s)", result.size());
    if (result.size() != 0) begin
      $display("FAIL: Min of empty queue should be empty");
      pass = 0;
    end

    result = q.max with (item.prio);
    $display("max with empty queue: %0d element(s)", result.size());
    if (result.size() != 0) begin
      $display("FAIL: Max of empty queue should be empty");
      pass = 0;
    end

    if (pass == 1)
      $display("PASSED");
    else
      $display("FAILED");

    $finish;
  end

endmodule
