// Test associative array as class property
// Pattern: this.assoc_prop[key] = value

class Memory;
  int data[string];

  function void write(string addr, int value);
    data[addr] = value;
  endfunction

  function int read(string addr);
    return data[addr];
  endfunction

  function int size();
    return data.size();
  endfunction

  // Note: exists() with variable key not yet supported in Icarus
  // Use direct property access for testing instead
endclass

module test;
  initial begin
    Memory mem;
    int val;

    mem = new();

    // Test write
    mem.write("A000", 100);
    mem.write("B000", 200);
    mem.write("C000", 300);

    // Test read
    val = mem.read("A000");
    if (val != 100) begin
      $display("FAILED: read(A000) = %0d", val);
      $finish;
    end

    val = mem.read("B000");
    if (val != 200) begin
      $display("FAILED: read(B000) = %0d", val);
      $finish;
    end

    // Test size
    if (mem.size() != 3) begin
      $display("FAILED: size = %0d", mem.size());
      $finish;
    end

    // Test exists - using direct property access
    if (!mem.data.exists("C000")) begin
      $display("FAILED: data.exists(C000) = 0");
      $finish;
    end
    if (mem.data.exists("D000")) begin
      $display("FAILED: data.exists(D000) = 1");
      $finish;
    end

    $display("PASSED");
  end
endmodule
