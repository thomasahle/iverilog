// Test $cast for class type checking and conversion
// Verifies: $cast(derived, base) for downcasting

module test;

  class Animal;
    string name;

    function new(string n);
      name = n;
    endfunction

    virtual function string speak();
      return "...";
    endfunction
  endclass

  class Dog extends Animal;
    int age;

    function new(string n, int a);
      super.new(n);
      age = a;
    endfunction

    virtual function string speak();
      return "Woof!";
    endfunction

    function void fetch();
      $display("%s is fetching!", name);
    endfunction
  endclass

  class Cat extends Animal;
    function new(string n);
      super.new(n);
    endfunction

    virtual function string speak();
      return "Meow!";
    endfunction
  endclass

  initial begin
    Animal a;
    Dog d, d2;
    Cat c;

    // Create objects
    d = new("Rex", 3);
    c = new("Whiskers");

    // Test upcast (always works)
    a = d;  // Dog to Animal
    $display("Animal speaks: %s", a.speak());  // Should say Woof! (virtual dispatch)

    // Test downcast with $cast
    if ($cast(d2, a)) begin
      $display("Cast successful: %s is %0d years old", d2.name, d2.age);
      d2.fetch();
    end else begin
      $display("FAILED: Cast should have succeeded");
      $finish;
    end

    // Test failed cast (Cat to Dog should fail)
    a = c;  // Cat to Animal
    if ($cast(d2, a)) begin
      $display("FAILED: Cast from Cat to Dog should have failed");
      $finish;
    end else begin
      $display("Cast correctly failed for Cat to Dog");
    end

    // Test cast to same type
    if ($cast(c, a)) begin
      $display("Cast to Cat succeeded: %s says %s", c.name, c.speak());
    end else begin
      $display("FAILED: Cast to Cat should have succeeded");
      $finish;
    end

    $display("PASSED");
    $finish;
  end

endmodule
