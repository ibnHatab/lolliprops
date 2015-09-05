defmodule FolderolTest do
  use ExUnit.Case
  import Folderol
  import Folderol.Parser



  @ill [
    {"(EXISTS x. P(x) | Q(x)) <->  (EXISTS x. P(x))  |  (EXISTS x. Q(x))",
     form do
       exists(x) do p(x) | q(x) end <> (exists(x) do p(x) end | exists(x) do q(x) end)
     end
    }
  ]

  @ tag skip: "integration test"
  test "check generator" do
    for {str, form} <- @ill, do: IO.puts str
  end

  test "simple expression" do
    f = form do
      exists(x) do p(x) | q(x) end <> (exists(x) do p(x) end | exists(x) do q(x) end)
    end
    # IO.puts ">> "
    # f |> IO.inspect
  end


  test "Scanning of identifiers and keywords" do
    assert {:Key, 'ALL'} == token_of('ALL')
    assert {:Key, 'EXISTS'} == token_of('EXISTS')
    assert {:Id, 'ANY'} == token_of('ANY')

    assert is_letter_or_digit(?c) == true
    assert is_letter_or_digit(?Z) == true
    assert is_letter_or_digit(?0) == true
    assert is_letter_or_digit(?9) == true

    assert is_letter_or_digit(?-) == false
    assert is_letter_or_digit(?_) == false

    assert scan_ident([], 'EXISTS') == {{:Key, 'EXISTS'}, []}
    assert scan_ident([], 'SOME123') == {{:Id, 'SOME123'}, []}
    assert scan_ident([], 'SOME123 OTHER') == {{:Id, 'SOME123'}, ' OTHER'}

    assert scan([{:Id, 'N1'}, {:Id, 'N2'}], []) == [{:Id, 'N2'}, {:Id, 'N1'}]
    assert scan([], ' --> ') == [{:Key, '-->'}]
    assert scan([], ' <-> P ') == [Key: '<->', Id: 'P']
  end

  test "Scanning, recognizing --> and <->, skipping blanks, etc." do

  end

  test "Parsing a list of tokens" do

  end

  test "Abstraction of a formula over t (containing no bound vars)." do
    # abstract
  end

  test "Replace (Bound 0) in formula with t (containing no bound vars)." do
    # subst_bound
  end

  test "Repeated parsing, returning the list of results" do
    # parse_repeat
  end

end

# quote do (exist x.( A || B ) ) end

# quote do
#   ( A + B || ^C)  >>> ( C && D * E ) |> G
# end

# quote do
#   (exists y.x.( p(x) | q(x) )) <> ((exists x.( p(x) )) | exists x.( q(x)))
# end |> IO.inspect |> Macro.to_string


# _= "(EXISTS x. P(x) | Q(x)) <->  (EXISTS x. P(x))  |  (EXISTS x. Q(x))"
# quote do
#   exists(x) do p(x) | q(x)  end <> (exists(x) do p(x) end | exists(x) do q(x) end) # iff
#   exists(x) do p(x) | q(x)  end >>> (exists(x) do p(x) end | exists(x) do q(x) end) # imply
#   exists(x) do p(x) | q(x)  end |> (exists(x) do p(x) end | exists(x) do q(x) end) # lolli
# end |> IO.inspect |> Macro.to_string

"""
empty  |-  (EXISTS x. P(x) | Q(x)) <-> (EXISTS x. P(x)) | (EXISTS x. Q(x))

> val it = () : unit
- the_goaltable
;
> val it =
    ref [[(2, Right,
           Conn("<->",
                [Quant("EXISTS", "x",
                       Conn("|",
                            [Pred("P", [Bound 0]), Pred("Q", [Bound 0])])),
                 Conn("|",
                      [Quant("EXISTS", "x", Pred("P", [Bound 0])),
                       Quant("EXISTS", "x", Pred("Q", [Bound 0]))])]))]] :
  (int * side/1 * form/2) list list ref
-
"""
