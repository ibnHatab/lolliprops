defmodule FolderolTest do
  use ExUnit.Case
  import Folderol



  @ill [
    {"(EXISTS x. P(x) | Q(x)) <->  (EXISTS x. P(x))  |  (EXISTS x. Q(x))",
     nil
     # form do
     #   exists(x) do p(x) | q(x) end <> (exists(x) do p(x) end | exists(x) do q(x) end)
     # end
    }
  ]

  test "check generator" do
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
