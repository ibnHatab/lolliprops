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

  @type var_name :: atom
  @type ctx :: Dict.t

  @type logic_term ::
  {:Var, var_name, ctx}
  | {:Param, var_name, [var_name]}
  | {:Bound, integer}
  | {:Fun, atom, [term]}

  @type logic_form ::
    {:Pred, atom, ctx, [var_name]}
  | {:Conn, atom, ctx, logic_form, logic_form}
  | {:Quant, :forall | :exist, [var_name], {:scope, [logic_form]}}

  @binary_ops [:>>>, :&, :|, :<>, :->]
  @unary_ops  [:^] # :FIXME not parsed yet

  @doc """
  Generate S-expression for first order logic from Elixir code
  Use stack and polosh notation (Post-DFS) to translate Elixir AST into Logic parse tree
  """
  @spec form(any) :: t
  defmacro form(do: block) do
    # prints AST   Macro.postwalk(block, &IO.inspect/1) |> IO.inspect
    {_ast, {:form, forms}} = Macro.postwalk(block, {:form, []}, &postwalk/2)
    quote do unquote_splicing(forms) end
  end


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

  def postwalk([do: _form] = ast, {:form, acc}) do
    # IO.puts "$[do: ]"
    {scope, acc1} = Enum.split_while(acc, &(&1 != :do))
    [:do | rest_acc] = acc1
    {ast, {:form, [{:scope, scope} | rest_acc]}} #|> IO.inspect
  end
  def postwalk({:do, _form} = ast, {:form, acc}) do
    # IO.puts "${:do}"
    {ast, {:form, acc}} # |> IO.inspect
  end
  def postwalk(:do = ast, {:form, acc}) do
    # IO.puts "$:do"
    {ast, {:form, [:do | acc]}} #|> IO.inspect
  end
  def postwalk({quant, ctx, args} = ast, {:form, acc}) when quant in [:exists, :forall] do
    # IO.puts "$Quant #{quant}"
    {vars, ast_scope} = Enum.split_while(args, &(case &1 do
                                               [do: _] -> false
                                               _ -> true
                                             end))
    if ast_scope == [] do
      raise  SyntaxError, description: "scope block missing: " <> Macro.to_string(ast),
      line: Dict.get(ctx, :line), file: __ENV__.file
    end

    [scope | args_acc] = acc
    varlist = unify_args(vars, args_acc, ctx)
    rest_acct = Enum.drop(args_acc, length(varlist))
    quant = quote do: {:Quant, unquote(quant), unquote(varlist), unquote(ctx), unquote(scope)}
    {ast, {:form, [quant | rest_acct]}} #|> IO.inspect
  end
  def postwalk({conn, ctx, [_lhs, _rhs]} = ast, {:form, acc}) when conn in @binary_ops do
    # IO.puts "$Conn #{conn}"
    [qrhs, qlhs | rest_acc] = acc # reversed head
    conn = quote do: {:Conn, unquote(conn), unquote(ctx), unquote(qlhs), unquote(qrhs)}
    {ast, {:form, [conn | rest_acc]}} #|> IO.inspect
  end
  def postwalk({pred, ctx, args} = ast, {:form, acc}) when is_atom(pred) and is_list(args) do
    # IO.puts "$Pred: #{pred}"
    varlist = unify_args(args, acc, ctx)
    rest_acct = Enum.drop(acc, length(varlist))

    pred = quote do
      {:Pred, unquote(pred), unquote(ctx), unquote(varlist)}
    end
    {ast, {:form, [pred | rest_acct]}}
  end
  def postwalk({var, ctx, nil} = ast, {:form, acc}) do
    form = quote do: {:Var, unquote(var), unquote(ctx)}
    # IO.puts "$Var: #{var}"
    {ast, {:form, [form | acc]}} #|> IO.inspect
  end
  def postwalk(term, {:form, acc}) when is_atom(term) do
    # IO.puts "$Constant: #{term}"
    {term, {:form, [{:Const, term} | acc]}}
  end
  def postwalk(any, acc), do: {any, acc} |> IO.inspect

end

defmodule Folderol.Logic do
  import Folderol


end

defmodule Folderol.Parser do



end
