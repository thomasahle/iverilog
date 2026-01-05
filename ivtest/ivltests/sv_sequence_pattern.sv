// Test UVM-style sequence pattern with nested sequences
// Inspired by AVIP sequence patterns

class seq_item;
  rand bit [7:0] addr;
  rand bit [7:0] data;
  bit rw;  // 0=read, 1=write (set explicitly, not randomized)

  function void display(string prefix);
    $display("%s %s addr=0x%02h data=0x%02h",
             prefix, rw ? "WRITE" : "READ", addr, data);
  endfunction
endclass

class sequence_base;
  string name;
  seq_item items[$];

  function new(string n);
    name = n;
  endfunction

  virtual task body();
    $display("sequence_base: body() should be overridden");
  endtask

  task start();
    $display("Starting sequence: %s", name);
    body();
    $display("Sequence %s complete, generated %0d items", name, items.size());
  endtask
endclass

class write_sequence extends sequence_base;
  int count;

  function new(string n, int c);
    super.new(n);
    count = c;
  endfunction

  virtual task body();
    seq_item item;
    for (int i = 0; i < count; i++) begin
      item = new();
      void'(item.randomize());
      item.rw = 1;  // Set write explicitly
      item.display($sformatf("  [%0d]", i));
      items.push_back(item);
      #10;
    end
  endtask
endclass

class read_sequence extends sequence_base;
  int count;

  function new(string n, int c);
    super.new(n);
    count = c;
  endfunction

  virtual task body();
    seq_item item;
    for (int i = 0; i < count; i++) begin
      item = new();
      void'(item.randomize());
      item.rw = 0;  // Set read explicitly
      item.display($sformatf("  [%0d]", i));
      items.push_back(item);
      #10;
    end
  endtask
endclass

class mixed_sequence extends sequence_base;
  write_sequence wr_seq;
  read_sequence rd_seq;

  function new(string n);
    super.new(n);
  endfunction

  virtual task body();
    $display("  Phase 1: Writes");
    wr_seq = new("wr_phase", 3);
    wr_seq.body();
    foreach (wr_seq.items[i]) items.push_back(wr_seq.items[i]);

    $display("  Phase 2: Reads");
    rd_seq = new("rd_phase", 2);
    rd_seq.body();
    foreach (rd_seq.items[i]) items.push_back(rd_seq.items[i]);
  endtask
endclass

module test;
  write_sequence wr_seq;
  read_sequence rd_seq;
  mixed_sequence mix_seq;

  int total_writes, total_reads;

  initial begin
    // Test 1: Simple write sequence
    $display("=== Test 1: Write Sequence ===");
    wr_seq = new("write_seq", 3);
    wr_seq.start();

    // Test 2: Simple read sequence
    $display("");
    $display("=== Test 2: Read Sequence ===");
    rd_seq = new("read_seq", 2);
    rd_seq.start();

    // Test 3: Mixed sequence (nested)
    $display("");
    $display("=== Test 3: Mixed Sequence ===");
    mix_seq = new("mixed_seq");
    mix_seq.start();

    // Count transaction types
    total_writes = 0;
    total_reads = 0;
    foreach (mix_seq.items[i]) begin
      if (mix_seq.items[i].rw) total_writes++;
      else total_reads++;
    end

    $display("");
    $display("Mixed sequence: %0d writes, %0d reads",
             total_writes, total_reads);

    if (wr_seq.items.size() == 3 &&
        rd_seq.items.size() == 2 &&
        mix_seq.items.size() == 5 &&
        total_writes == 3 && total_reads == 2)
      $display("PASSED");
    else
      $display("FAILED");

    $finish;
  end
endmodule
