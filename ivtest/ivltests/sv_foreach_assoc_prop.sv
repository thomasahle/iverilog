// Test foreach on associative array class property
// This tests the pattern: foreach(obj.assoc_prop[key]) { body }

class Config;
  bit [31:0] addr_map[int];

  function void add_entry(int idx, bit [31:0] addr);
    addr_map[idx] = addr;
  endfunction

  function void print_all();
    foreach(addr_map[i]) begin
      $display("addr_map[%0d] = 0x%08x", i, addr_map[i]);
    end
  endfunction

  function int count_entries();
    int count = 0;
    foreach(addr_map[i]) begin
      count++;
    end
    return count;
  endfunction
endclass

module test;
  initial begin
    Config cfg;
    int cnt;

    cfg = new();
    cfg.add_entry(10, 32'h1000);
    cfg.add_entry(20, 32'h2000);
    cfg.add_entry(30, 32'h3000);

    // Test foreach iteration
    cfg.print_all();

    // Test counting with foreach
    cnt = cfg.count_entries();
    if (cnt != 3) begin
      $display("FAILED: expected 3 entries, got %0d", cnt);
      $finish;
    end

    // Add more entries and verify
    cfg.add_entry(5, 32'h500);
    cfg.add_entry(100, 32'h10000);

    cnt = cfg.count_entries();
    if (cnt != 5) begin
      $display("FAILED: expected 5 entries, got %0d", cnt);
      $finish;
    end

    $display("PASSED");
  end
endmodule
