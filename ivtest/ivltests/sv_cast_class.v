// Test $cast system function for class types
// Tests dynamic type checking and casting between class types

class animal;
    string name;
    function new(string n);
        name = n;
    endfunction
endclass

class dog extends animal;
    int age;
    function new(string n, int a);
        super.new(n);
        age = a;
    endfunction
endclass

class cat extends animal;
    string color;
    function new(string n, string c);
        super.new(n);
        color = c;
    endfunction
endclass

module test;
    animal a;
    dog d, d2;
    cat c;
    int errors;

    initial begin
        errors = 0;

        // Create a dog and store as animal reference
        d = new("Buddy", 5);
        a = d;

        // Cast animal back to dog - should succeed
        if ($cast(d2, a)) begin
            if (d2.age != 5) begin
                $display("FAILED: d2.age=%0d, expected 5", d2.age);
                errors++;
            end
        end else begin
            $display("FAILED: $cast(dog, animal) should succeed when animal is dog");
            errors++;
        end

        // Try to cast animal (which is a dog) to cat - should fail
        if ($cast(c, a)) begin
            $display("FAILED: $cast(cat, animal) should fail when animal is dog");
            errors++;
        end

        // Create a cat
        c = new("Whiskers", "orange");
        a = c;

        // Try to cast animal (which is a cat) to dog - should fail
        if ($cast(d2, a)) begin
            $display("FAILED: $cast(dog, animal) should fail when animal is cat");
            errors++;
        end

        if (errors == 0) begin
            $display("PASSED");
        end else begin
            $display("FAILED: %0d errors", errors);
        end

        $finish;
    end
endmodule
