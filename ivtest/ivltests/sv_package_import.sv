// Test package import
package pkg_a;
  typedef enum {RED, GREEN, BLUE} color_e;
  parameter int MAX_VALUE = 100;

  function automatic int double(int x);
    return x * 2;
  endfunction
endpackage

package pkg_b;
  typedef struct {
    int x;
    int y;
  } point_t;

  function automatic int distance_sq(point_t p);
    return p.x * p.x + p.y * p.y;
  endfunction
endpackage

module test;
  import pkg_a::*;
  import pkg_b::point_t;
  import pkg_b::distance_sq;

  color_e c;
  point_t pt;
  int errors = 0;

  initial begin
    // Test enum from package
    c = GREEN;
    if (c != 1) begin
      $display("FAILED: GREEN = %0d, expected 1", c);
      errors++;
    end

    // Test parameter from package
    if (MAX_VALUE != 100) begin
      $display("FAILED: MAX_VALUE = %0d", MAX_VALUE);
      errors++;
    end

    // Test function from package
    if (double(21) != 42) begin
      $display("FAILED: double(21) = %0d", double(21));
      errors++;
    end

    // Test struct from second package
    pt.x = 3;
    pt.y = 4;
    if (distance_sq(pt) != 25) begin
      $display("FAILED: distance_sq = %0d", distance_sq(pt));
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED: %0d errors", errors);
  end
endmodule
