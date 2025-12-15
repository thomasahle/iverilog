// Test that 'sample' and 'option' can be used as method names
// Previously these were global keywords which blocked their use as identifiers.
// Now they are only keywords in covergroup context.

class data_sampler;
  int sample_count;
  int option_count;
  int last_sample;

  function new();
    sample_count = 0;
    option_count = 0;
    last_sample = 0;
  endfunction

  // 'sample' as a method name - was blocked when it was a global keyword
  virtual function void sample(int value);
    sample_count++;
    last_sample = value;
  endfunction

  // 'option' as a method name - was blocked when it was a global keyword
  virtual function void option(int opt);
    option_count++;
  endfunction

  function int get_sample_count();
    return sample_count;
  endfunction

  function int get_option_count();
    return option_count;
  endfunction
endclass

// Derived class to test virtual dispatch with sample/option methods
class enhanced_sampler extends data_sampler;
  int multiplier;

  function new();
    super.new();
    multiplier = 2;
  endfunction

  // Override sample method
  virtual function void sample(int value);
    super.sample(value * multiplier);
  endfunction
endclass

module test;
  data_sampler ds;
  enhanced_sampler es;
  int errors;

  initial begin
    errors = 0;

    // Test base class
    ds = new();
    ds.sample(10);
    ds.sample(20);
    ds.option(1);

    if (ds.get_sample_count() != 2) begin
      $display("FAILED: base sample_count = %0d, expected 2", ds.get_sample_count());
      errors++;
    end
    if (ds.get_option_count() != 1) begin
      $display("FAILED: base option_count = %0d, expected 1", ds.get_option_count());
      errors++;
    end
    if (ds.last_sample != 20) begin
      $display("FAILED: base last_sample = %0d, expected 20", ds.last_sample);
      errors++;
    end

    // Test derived class with virtual dispatch
    es = new();
    es.sample(10);  // Should store 20 (10 * 2)
    es.option(1);

    if (es.get_sample_count() != 1) begin
      $display("FAILED: enhanced sample_count = %0d, expected 1", es.get_sample_count());
      errors++;
    end
    if (es.last_sample != 20) begin
      $display("FAILED: enhanced last_sample = %0d, expected 20", es.last_sample);
      errors++;
    end

    if (errors == 0) begin
      $display("PASSED");
    end
  end
endmodule
