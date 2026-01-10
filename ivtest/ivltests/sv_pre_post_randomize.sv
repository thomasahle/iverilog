// Test pre_randomize and post_randomize callbacks
// These methods are automatically called before and after randomize()

class Item;
  rand int x;
  int pre_called;
  int post_called;

  function void pre_randomize();
    pre_called++;
  endfunction

  function void post_randomize();
    post_called++;
    // Modify x after randomization - make it positive
    if (x < 0) x = -x;
  endfunction
endclass

// Test inheritance - derived class should inherit callbacks
class DerivedItem extends Item;
  rand int y;
  int derived_pre_called;
  int derived_post_called;

  function void pre_randomize();
    super.pre_randomize();  // Call base class version
    derived_pre_called++;
  endfunction

  function void post_randomize();
    super.post_randomize();  // Call base class version
    derived_post_called++;
    // Additional post-processing
    if (y < 0) y = -y;
  endfunction
endclass

module test;
  Item item;
  DerivedItem derived;

  initial begin
    // Test basic pre/post_randomize on base class
    item = new();

    // Callbacks should not be called yet
    if (item.pre_called != 0 || item.post_called != 0) begin
      $display("FAILED: callbacks should not be called yet");
      $finish;
    end

    // First randomize
    void'(item.randomize());

    if (item.pre_called != 1) begin
      $display("FAILED: pre_randomize not called, got %0d", item.pre_called);
      $finish;
    end

    if (item.post_called != 1) begin
      $display("FAILED: post_randomize not called, got %0d", item.post_called);
      $finish;
    end

    // Check that post_randomize modified the value to be positive
    if (item.x < 0) begin
      $display("FAILED: post_randomize should have made x positive, got %0d", item.x);
      $finish;
    end

    // Second randomize - counters should increment
    void'(item.randomize());

    if (item.pre_called != 2) begin
      $display("FAILED: pre_randomize should be called twice, got %0d", item.pre_called);
      $finish;
    end

    if (item.post_called != 2) begin
      $display("FAILED: post_randomize should be called twice, got %0d", item.post_called);
      $finish;
    end

    // Test derived class with inherited callbacks
    derived = new();

    void'(derived.randomize());

    // Base class callbacks should be called (via super.pre/post_randomize())
    if (derived.pre_called != 1) begin
      $display("FAILED: inherited pre_randomize not called, got %0d", derived.pre_called);
      $finish;
    end

    if (derived.post_called != 1) begin
      $display("FAILED: inherited post_randomize not called, got %0d", derived.post_called);
      $finish;
    end

    // Derived class callbacks should also be called
    if (derived.derived_pre_called != 1) begin
      $display("FAILED: derived pre_randomize not called, got %0d", derived.derived_pre_called);
      $finish;
    end

    if (derived.derived_post_called != 1) begin
      $display("FAILED: derived post_randomize not called, got %0d", derived.derived_post_called);
      $finish;
    end

    // Both x and y should be positive after post_randomize
    if (derived.x < 0) begin
      $display("FAILED: derived x should be positive, got %0d", derived.x);
      $finish;
    end

    if (derived.y < 0) begin
      $display("FAILED: derived y should be positive, got %0d", derived.y);
      $finish;
    end

    $display("PASSED");
  end
endmodule
