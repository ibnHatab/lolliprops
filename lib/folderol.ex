defmodule Folderol do
  @moduledoc """
  Folderol: a simple theorem prover
  Folderol works in classical first-order logic.
  """

  @typedoc """
  Basic data structures and operations
  (*TERMS AND FORMULAE*)

  datatype term =
    Var   of string
  | Param of string * string list
  | Bound of int
  | Fun   of string * term list;

  datatype form =
    Pred  of string * term list
  | Conn  of string * form list
  | Quant of string * string * form;

  """
  @type t :: logic_term | logic_form

  @type var_name :: String.t
  @type ctx :: Dict.t

  @type logic_term ::
  {:Var, var_name}
  | {:Param, var_name, [var_name]}
  | {:Bound, integer}
  | {:Fun, atom, [term]}

  @type logic_form ::
    {:Pred,  var_name, ctx, [logic_term]}
  | {:Conn,  atom, [logic_form]}
  | {:Quant, :forall | :exist, var_name, logic_form}

  @binary_ops [:>>>, :&, :|, :<>, :->]
  @unary_ops  [:^]

  @spec form(any) :: t
  defmacro form(do: block) do
    quote do
#      unquote(Macro.prewalk(block, &prewalk/1))
#      unquote(Macro.prewalk(block, &postwalk/1))
      unquote(Macro.postwalk(block, {:form, []}, &postwalk/2))
#      unquote(Macro.postwalk(block, &IO.inspect/1))
    end
    |> Macro.to_string |> IO.puts
  end


  # def prewalk({quant, ctx, args}) when quant in [:exists, :forall] do
  #   [{var, _ctx, nil}, [do: block]] = args
  #   IO.puts ">> :Quant #{quant} #{var}"
  #   quote do: {:Quant, unquote(quant), unquote(var), unquote(ctx), unquote(block)}
  # end
  def prewalk({op, ctx, [lhs, rhs]}) when op in @binary_ops do
    IO.puts ">> :Conn #{op}"
    quote do: {:Conn, unquote(op), unquote(ctx), unquote(lhs), unquote(rhs)}
  end
  def prewalk({pred, ctx, args}) do
    IO.puts ">> :Pred #{pred}"
    IO.inspect {pred, ctx, args}
    varlist = Enum.reduce(args, [], fn (bind, acc) ->
      case bind do
        {var, ctx, nil} ->
          [{:Bind, var, ctx} | acc]
        _ -> acc
      end
    end) |> Enum.reverse
    IO.inspect varlist
    quote do
      {:Pred, unquote(pred), unquote(ctx), unquote(varlist)}
    end
  end
  def prewalk(any), do: any # |> IO.inspect |> Macro.to_string


  # def postwalk({var, ctx, nil}) do
  #   IO.puts ">> :Var #{var}"
  #   quote do: {:Var, unquote(var), unquote(ctx)}
  # end


  defp unify_args(args, stack, ctx) do
    # Unify variables from the stack and ast function parameters
    {_, unified_vars} =
      args |> Enum.reverse |> Enum.zip(stack)
    |>  Enum.filter(
      fn({qx, qvar}) ->
        case {qx, qvar} do
          {{var, ctx, nil}, {:{}, [], [:Var, var, ctx]}} ->
            true
          {{var, ctx, nil}, _other} ->
            raise SyntaxError, description: "unification fail for: #{var}",
            line: Dict.get(ctx, :line), file: __ENV__.file
          _ ->
            raise SyntaxError, description: "unification fail around: " <> Macro.to_string(qx),
            line: Dict.get(ctx, :line), file: __ENV__.file
        end end)
    |> Enum.unzip

    Enum.reverse (unified_vars)
  end

  def postwalk({quant, ctx, args} = ast, {:form, acc}) when quant in [:exists, :forall] do
    [{var, _ctx, nil}, [do: block]] = args
    IO.puts ">> :Quant #{quant} #{var}"
    quote do: {:Quant, unquote(quant), unquote(var), unquote(ctx), unquote(block)}
  end
  def postwalk({conn, ctx, [_lhs, _rhs]} = ast, {:form, acc}) when conn in @binary_ops do
    IO.puts "$Conn #{conn}"
    [qrhs, qlhs | rest_acc] = acc # reversed head
    conn = quote do: {:Conn, unquote(conn), unquote(ctx), unquote(qlhs), unquote(qrhs)}
    {ast, {:form, [conn | rest_acc]}} #|> IO.inspect
  end
  def postwalk({pred, ctx, args} = ast, {:form, acc}) when is_atom(pred) and is_list(args) do
    IO.puts "$Pred: #{pred}"
    varlist = unify_args(args, acc, ctx)
    rest_acct = Enum.drop(acc, length(varlist))

    pred = quote do
      {:Pred, unquote(pred), unquote(ctx), unquote(varlist)}
    end
    {ast, {:form, [pred | rest_acct]}}
  end
  def postwalk({var, ctx, nil} = ast, {:form, acc}) do
    form = quote do: {:Var, unquote(var), unquote(ctx)}
    IO.puts "$Var: #{var}"
    {ast, {:form, [form | acc]}} #|> IO.inspect
  end
  def postwalk(term, {:form, acc}) when is_atom(term) do
    IO.puts "$Constant: #{term}"
    {term, {:form, [term | acc]}}
  end
  def postwalk(any, {:form, acc}) do
    IO.write ">> ANY: "
    any |> IO.inspect
    IO.write ">> acc: "
    acc |> Macro.to_string |> IO.puts
    {any, {:form, acc}}
  end
  # def postwalk(any, acc), do: {any, acc} |> IO.inspect


end

defmodule Folderol.Logic do
  import Folderol

  f = form do
#    exists(z) do p(x, y) end
    exists(z) do p(x, y) | false end
    #    exists(x) do p(x) | q(x) end <> (exists(x) do p(x) end | exists(x) do q(x) end)
  end


  IO.puts ">> "
  f |> Macro.to_string |> IO.inspect

end

defmodule Folderol.Parser do

end
