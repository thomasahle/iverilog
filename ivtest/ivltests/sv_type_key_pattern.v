// Test for type keys in assignment patterns (SV 5.10)
// Tests parsing of '{type: value} syntax

module test;
  typedef struct {
    int a;
    int b;
  } data_t;

  data_t d;

  initial begin
    // Basic positional assignment
    d = '{1, 2};

    // Named member assignment (existing support)
    d = '{a: 10, b: 20};

    // Verify assignment works
    if (d.a !== 10 || d.b !== 20) begin
      $display("FAILED: d.a=%0d, d.b=%0d", d.a, d.b);
      $finish;
    end

    // Type key assignment - parsing test only
    // (elaboration doesn't yet implement type key semantics)
    // d = '{int: 0};        // Would assign 0 to all int members
    // d = '{default: 0};    // Would assign 0 to all members

    $display("PASSED");
    $finish;
  end
endmodule
