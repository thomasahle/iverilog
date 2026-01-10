// Test unique constraint for arrays
// Ensures all elements in array have distinct values

class Item;
  rand bit [3:0] data [4];  // 4 elements, each 4 bits (0-15)

  constraint c_unique {
    unique { data };  // All elements must be different
  }
endclass

module test;
  Item item;
  int pass_count;
  int total;
  int all_unique;
  int i, j, k;

  initial begin
    item = new();
    pass_count = 0;
    total = 10;

    for (i = 0; i < total; i = i + 1) begin
      void'(item.randomize());

      // Check that all elements are unique
      all_unique = 1;
      for (j = 0; j < 4; j = j + 1) begin
        for (k = j + 1; k < 4; k = k + 1) begin
          if (item.data[j] == item.data[k]) begin
            all_unique = 0;
            $display("FAIL: data[%0d]=%0d == data[%0d]=%0d",
                     j, item.data[j], k, item.data[k]);
          end
        end
      end

      if (all_unique) begin
        pass_count = pass_count + 1;
      end
    end

    if (pass_count == total) begin
      $display("PASSED");
    end else begin
      $display("FAILED: %0d/%0d passed", pass_count, total);
    end
  end
endmodule
