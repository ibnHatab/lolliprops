defmodule FolderolTest.Parser do
  use ExUnit.Case, async: false

  import Folderol
  import Folderol.Parser


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
    # scan([], explode"(EXISTS x. P(x) | Q(x)) <->  (EXISTS x. P(x))  |  (EXISTS x. Q(x))");
    # > val it =
    # it = [Key "(", Key "EXISTS", Id "x", Key ".", Id "P", Key "(", Id "x", Key ")",
    #  Key "|", Id "Q", Key "(", Id "x", Key ")", Key ")", Key "<->", Key "(",
    #  Key "EXISTS", Id "x", Key ".", Id "P", Key "(", Id "x", Key ")", Key ")",
    #  Key "|", Key "(", Key "EXISTS", Id "x", Key ".", Id "Q", Key "(", Id "x",
    #  Key ")", Key ")"]
    str = '(EXISTS x. P(x) | Q(x)) <->  (EXISTS x. P(x))  |  (EXISTS x. Q(x))'
    it = [{:Key, '('}, {:Key, 'EXISTS'}, {:Id, 'x'}, {:Key, '.'},
          {:Id, 'P'}, {:Key, '('}, {:Id, 'x'}, {:Key, ')'},
          {:Key, '|'},
          {:Id, 'Q'}, {:Key, '('}, {:Id, 'x'}, {:Key, ')'}, {:Key, ')'},
           {:Key, '<->'},
           {:Key, '('}, {:Key, 'EXISTS'}, {:Id, 'x'}, {:Key, '.'},
           {:Id, 'P'}, {:Key, '('}, {:Id, 'x'}, {:Key, ')'}, {:Key, ')'},
           {:Key, '|'},
           {:Key, '('}, {:Key, 'EXISTS'}, {:Id, 'x'}, {:Key, '.'},
           {:Id, 'Q'}, {:Key, '('}, {:Id, 'x'}, {:Key, ')'}, {:Key, ')'}]
    tokens = scan([], str)
    assert tokens == it
  end

  test "Parsing tokens" do
    assert {{:Conn, '~', [{:Pred, 'A', []}]}, []} == parse( scan( [], '~A'))
    assert {{:Pred, 'Q', [{:Fun, 'x', []}]}, []} == parse( scan( [], 'Q(x)'))
    assert {{:Conn, '|', [{:Pred, 'P', []}, {:Pred, 'Q', []}]}, []} == parse( scan( [], 'P | Q'))
    assert {{:Conn, '|',
             [{:Pred, 'P', [{:Fun, 'x', []}]},
              {:Pred, 'Q', [{:Fun, 'x', []}]}]}, []} == parse( scan( [], 'P(x) | Q(x)'))
    assert {{:Quant, 'EXISTS', 'x',
             {:Conn, '|', [{:Pred, 'P', [Bound: 0]},
                           {:Pred, 'Q', [Bound: 0]}]}}, []} == parse( scan( [], '(EXISTS x. P(x) | Q(x))'))
  end

  @run_goal [
    # (*absorptive laws of & and | *)
    'P & P <-> P',
    'P | P <-> P',
    # (*commutative laws of & and | *)
    'P & Q <-> Q & P',
    'P | Q <-> Q | P',
    # (*associative laws of & and | *)
    '(P & Q) & R <-> P & (Q & R)',
    '(P | Q) | R <-> P | (Q | R)',
    # (*distributive laws of & and | *)
    'P & Q | R <-> (P | R) & (Q | R)',
    'P | Q & R <-> P & R | Q & R',
    # (*Laws involving implication*)
    '(P | Q --> R) <-> (P --> R) & (Q --> R)',
    '(P & Q --> R) <-> (P --> (Q --> R))',
    '(P --> Q & R) <-> (P --> Q) & (P --> R)',
    # (*Classical theorems*)
    'P | Q --> P | ~P & Q',
    '((P-->Q)-->Q) <-> P|Q',
    '(P-->Q)&(~P-->R)  --> P & Q | R',
    'P&Q | ~P&R  <->  (P-->Q)&(~P-->R)',
    '(P-->Q) | (P-->R)  <->  (P --> Q | R)',
    '(P<->Q) <-> (Q<->P)',
    '(EXISTS x.EXISTS y.P(x,y))  <->  (EXISTS y.EXISTS x.P(x,y))',

    '(ALL x. P(x) & Q(x))  <->  (ALL x. P(x))  &  (ALL x. Q(x))',
    '(ALL x. P(x))  |  (ALL x. Q(x))   -->  (ALL x. P(x) | Q(x))',
    '(ALL x.P(x)) | Q  <->  (ALL x. P(x) | Q)',

    '(ALL x. P --> Q(x))  <->  (P --> (ALL x. Q(x)))',
    '(ALL x.P(x)-->Q)  <->  ((EXISTS x.P(x)) --> Q)',
    '(EXISTS x. P(x) | Q(x)) <->  (EXISTS x. P(x))  |  (EXISTS x. Q(x))',
    '(EXISTS x. P(x) & Q(x)) -->  (EXISTS x. P(x))  &  (EXISTS x. Q(x))',
    '(EXISTS x. P --> Q(x))  <->  (P --> (EXISTS x. Q(x)))',
    '(EXISTS x.P(x)-->Q)  <->  ((ALL x.P(x))-->Q)',
    # (*hard: needs multiple instantiation of ALL and may loop*)
    '(ALL x. P(x)-->P(f(x))) --> (ALL y. P(y) --> P(f(f(f(y)))))',
    # (*needs double instantiation of EXISTS*)
    'EXISTS x. P(x) --> P(f(x)) & P(g(x))',
    'ALL x. ALL y. EXISTS z. P(z) --> P(x) & P(y)',
    'EXISTS x. P(x) --> (ALL x. P(x))',
    # (*Principia Mathematica *11.53  *)
    '''
    (ALL x. ALL y. P(x) --> Q(y))
    <-> ((EXISTS x. P(x)) --> (ALL y. Q(y)))
    ''',
    # (*Principia Mathematica *11.55  *)
    '''
    (EXISTS x. EXISTS y. P(x) & Q(x,y))
    <-> (EXISTS x. P(x) & (EXISTS y. Q(x,y)))
    ''',
    # (*Principia Mathematica *11.61  *)
    '''
    (EXISTS y. ALL x. P(x) --> Q(x,y))
    --> (ALL x. P(x) --> (EXISTS y. Q(x,y)))
    ''',
    # (*Basic test of quantifier reasoning*)
    '(EXISTS y. ALL x. P(x,y))  -->  (ALL x. EXISTS y. P(x,y))',
    # (*various non-valid formulae*)
    '(ALL x. EXISTS y. P(x,y))  -->  (EXISTS y. ALL x. P(x,y))',
    # (*Should not be provable: different eigenvariables must be chosen*)
    '(EXISTS x.P(x)) --> (ALL x. P(x))',
    'P(?aaaa) --> (ALL x.P(x))',
    '(P(?aaaa) --> (ALL x.Q(x))) --> (ALL x. P(x) --> Q(x))',
    # (*Not provable, causes looping!  simplest example of Folderol's stupidity*)
    '(ALL x. P(x)) --> Q',
    '(ALL x. P(x))  -->  (EXISTS x. P(x))',
    '(ALL x. P(x)-->Q(x)) & (EXISTS x.P(x)) --> (EXISTS x.Q(x))',
    '(P--> (EXISTS x.Q(x))) & P--> (EXISTS x.Q(x))'
  ]
  test "Parsing a list of tokens" do
    for str <- @run_goal do
      tokens = scan([], str)
      {_ast, rest} = parse tokens
      assert rest == []
    end
  end

  def srink(str), do: Enum.filter(str, &(&1 != ?\s && &1 != ?\n))

  test "Printing: conversion of terms/formulae to strings" do

    for str <- @run_goal do
      form = read str
      repr = stringof(form) |> srink
      assert srink(str) == repr
    end
  end

end

defmodule FolderolTest.Logic do
  use ExUnit.Case
  import Folderol
  import Folderol.Parser

  test "Abstraction of a formula over t (containing no bound vars)." do
    # abstract
  end

  test "Replace (Bound 0) in formula with t (containing no bound vars)." do
    # subst_bound
  end

end

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

  @tag skip: "integration test"
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
