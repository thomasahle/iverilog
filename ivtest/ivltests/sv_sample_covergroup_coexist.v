// Test that 'sample' and 'option' can be used as identifiers
// even in the presence of covergroups (where they are context-sensitive keywords)

class DataCollector;
  int sample;  // 'sample' as property name
  int option;  // 'option' as property name
  int data;

  covergroup cg @(data);
    // In covergroup context, 'sample' and 'option' have special meaning
    option.per_instance = 1;
    cp_data: coverpoint data {
      bins low = {[0:49]};
      bins high = {[50:100]};
    }
  endgroup

  function new();
    sample = 0;
    option = 0;
    data = 0;
    // Note: cg = new() would instantiate covergroup, but covergroups
    // are currently stub implementations, so we skip that for now.
  endfunction

  // Method named 'sample' - different from covergroup's sample
  function void sample(int val);
    this.sample = val;  // Assign to property
    data = val;
    // Note: cg.sample() would call the covergroup's sample
  endfunction

  // Method named 'option' - different from covergroup's option
  function void option(int val);
    this.option = val;
  endfunction

  function int get_sample();
    return sample;
  endfunction

  function int get_option();
    return option;
  endfunction
endclass

module test;
  DataCollector dc;
  int errors;

  initial begin
    errors = 0;
    dc = new();

    dc.sample(42);
    dc.option(100);

    if (dc.get_sample() !== 42) begin
      $display("FAILED: sample = %0d, expected 42", dc.get_sample());
      errors++;
    end

    if (dc.get_option() !== 100) begin
      $display("FAILED: option = %0d, expected 100", dc.get_option());
      errors++;
    end

    if (errors == 0)
      $display("PASSED");

    $finish;
  end
endmodule
