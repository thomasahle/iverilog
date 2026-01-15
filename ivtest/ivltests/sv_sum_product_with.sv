// Test sum/product with (item.field) clause for queues of packed structs
module test;

  typedef struct packed {
    bit [7:0] id;
    bit [7:0] value;
  } item_t;

  item_t q[$];
  item_t pkt;
  int sum_val, sum_id, product_val, product_id;
  int pass;

  initial begin
    pass = 1;

    // Add elements
    pkt.id = 1; pkt.value = 10; q.push_back(pkt);
    pkt.id = 2; pkt.value = 20; q.push_back(pkt);
    pkt.id = 3; pkt.value = 30; q.push_back(pkt);

    $display("Queue contents:");
    for (int i = 0; i < q.size(); i = i + 1) begin
      $display("  q[%0d]: id=%0d, value=%0d", i, q[i].id, q[i].value);
    end

    // Test sum with (item.value) - should be 10+20+30 = 60
    sum_val = q.sum with (item.value);
    $display("q.sum with (item.value) = %0d (expected 60)", sum_val);
    if (sum_val != 60) begin
      $display("FAIL: sum with (item.value) should be 60");
      pass = 0;
    end

    // Test sum with (item.id) - should be 1+2+3 = 6
    sum_id = q.sum with (item.id);
    $display("q.sum with (item.id) = %0d (expected 6)", sum_id);
    if (sum_id != 6) begin
      $display("FAIL: sum with (item.id) should be 6");
      pass = 0;
    end

    // Test product with (item.value) - should be 10*20*30 = 6000
    product_val = q.product with (item.value);
    $display("q.product with (item.value) = %0d (expected 6000)", product_val);
    if (product_val != 6000) begin
      $display("FAIL: product with (item.value) should be 6000");
      pass = 0;
    end

    // Test product with (item.id) - should be 1*2*3 = 6
    product_id = q.product with (item.id);
    $display("q.product with (item.id) = %0d (expected 6)", product_id);
    if (product_id != 6) begin
      $display("FAIL: product with (item.id) should be 6");
      pass = 0;
    end

    // Test with empty queue
    q.delete();
    sum_val = q.sum with (item.value);
    $display("sum with empty queue = %0d (expected 0)", sum_val);
    if (sum_val != 0) begin
      $display("FAIL: sum of empty queue should be 0");
      pass = 0;
    end

    product_val = q.product with (item.value);
    $display("product with empty queue = %0d (expected 1)", product_val);
    if (product_val != 1) begin
      $display("FAIL: product of empty queue should be 1");
      pass = 0;
    end

    if (pass == 1)
      $display("PASSED");
    else
      $display("FAILED");

    $finish;
  end

endmodule
