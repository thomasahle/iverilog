// Test binsof() with boolean operators && and || in cross coverage
// These are parsed but not functional - coverage is a stub

typedef enum {A, B, C, D} type_e;

class BoolBinsofTest;
  type_e val1;
  type_e val2;

  covergroup cg;
    option.per_instance = 1;

    VAL1_CP : coverpoint val1 {
      bins a_bin = {A};
      bins b_bin = {B};
      bins c_bin = {C};
      bins d_bin = {D};
    }

    VAL2_CP : coverpoint val2 {
      bins a_bin = {A};
      bins b_bin = {B};
      bins c_bin = {C};
      bins d_bin = {D};
    }

    // Cross with && operator
    CROSS_AND : cross VAL1_CP, VAL2_CP {
      ignore_bins and_ignore = binsof(VAL1_CP) intersect {A} && binsof(VAL2_CP) intersect {D};
    }

    // Cross with || operator
    CROSS_OR : cross VAL1_CP, VAL2_CP {
      ignore_bins or_ignore = binsof(VAL1_CP) intersect {A} || binsof(VAL2_CP) intersect {D};
    }

  endgroup

endclass

module test;
  initial begin
    $display("PASSED");
    $finish;
  end
endmodule
