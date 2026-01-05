// Test coverage pattern with manual tracking
// Inspired by AVIP coverage collector patterns

class transaction;
  rand bit [7:0] addr;
  rand bit [7:0] data;
  rand bit [1:0] size;  // 0=byte, 1=half, 2=word, 3=reserved
  rand bit       write;

  constraint c_size { size != 3; }  // No reserved size
endclass

class coverage_collector;
  // Use individual variables instead of arrays to avoid indexing issues
  int addr_range0, addr_range1, addr_range2, addr_range3;
  int size0, size1, size2, size3;
  int reads, writes;
  int total_samples;

  function new();
    total_samples = 0;
    addr_range0 = 0; addr_range1 = 0; addr_range2 = 0; addr_range3 = 0;
    size0 = 0; size1 = 0; size2 = 0; size3 = 0;
    reads = 0; writes = 0;
  endfunction

  function void sample(transaction t);
    // Track address range (0-63, 64-127, 128-191, 192-255)
    case (t.addr[7:6])
      0: addr_range0++;
      1: addr_range1++;
      2: addr_range2++;
      3: addr_range3++;
    endcase

    // Track size
    case (t.size)
      0: size0++;
      1: size1++;
      2: size2++;
      3: size3++;
    endcase

    // Track read/write
    if (t.write) writes++;
    else reads++;

    total_samples++;
  endfunction

  function int get_coverage_percent();
    int covered_bins;

    // Count non-zero bins
    covered_bins = 0;
    if (addr_range0 > 0) covered_bins++;
    if (addr_range1 > 0) covered_bins++;
    if (addr_range2 > 0) covered_bins++;
    if (addr_range3 > 0) covered_bins++;
    if (size0 > 0) covered_bins++;
    if (size1 > 0) covered_bins++;
    if (size2 > 0) covered_bins++;
    // size3 excluded (reserved)
    if (reads > 0) covered_bins++;
    if (writes > 0) covered_bins++;

    // Total valid bins: 4 addr + 3 sizes + 2 rw = 9
    return (covered_bins * 100) / 9;
  endfunction

  function void report();
    $display("Coverage Report:");
    $display("  Samples: %0d", total_samples);
    $display("  Address ranges: [0-63]=%0d [64-127]=%0d [128-191]=%0d [192-255]=%0d",
             addr_range0, addr_range1, addr_range2, addr_range3);
    $display("  Sizes: byte=%0d half=%0d word=%0d",
             size0, size1, size2);
    $display("  Operations: read=%0d write=%0d", reads, writes);
    $display("  Coverage: %0d%%", get_coverage_percent());
  endfunction
endclass

module test;
  coverage_collector cov;
  transaction tx;
  int coverage_pct;

  initial begin
    cov = new();
    tx = new();

    $display("Generating random transactions...");

    // Generate enough transactions to hit most bins
    repeat(50) begin
      void'(tx.randomize());
      cov.sample(tx);
    end

    $display("");
    cov.report();

    coverage_pct = cov.get_coverage_percent();

    // Expect at least 50% coverage (sizes + rw should hit)
    // Address distribution may be skewed depending on randomization
    if (coverage_pct >= 50)
      $display("PASSED: Coverage %0d%% meets threshold", coverage_pct);
    else
      $display("FAILED: Coverage %0d%% below threshold", coverage_pct);

    $finish;
  end
endmodule
