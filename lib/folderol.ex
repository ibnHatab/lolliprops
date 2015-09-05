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
  | {:Fun, atom, [logic_term]}

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

  # (*Operations on terms and formulae*)

  @doc "Replace the atomic term u by new throughout a term"
  @spec replace_term({Folderol.logic_term, Folderol.logic_term},
                     Folderol.logic_term) :: Folderol.logic_term
  def replace_term({u,new}, t) do
    if t == u do new
    else case t do
           {:Fun, a, ts} -> {:Fun, a, Enum.map(ts, fn tt -> replace_term({u,new}, tt) end)}
           _ -> t
         end
    end
  end

  @doc "Abstraction of a formula over t (containing no bound vars)."
  @spec abstract(Folderol.logic_term, Folderol.logic_form) :: Folderol.logic_form
  def abstract(t, form) do
    do_abstract(t, 0, form)
  end
  defp do_abstract(t, i, {:Pred ,a, ts}), do: {:Pred, a, Enum.map(ts, &(replace_term({t, {:Bound, i}}, &1)))}
  defp do_abstract(t, i, {:Conn, b, as}), do: {:Conn, b, Enum.map(as, &(do_abstract(t, i, &1)))}
  defp do_abstract(t, i, {:Quant, q, b, a}), do: {:Quant, q, b, do_abstract(t, i+1, a)}


  @doc "Replace (Bound 0) in formula with t (containing no bound vars)."
  @spec subst_bound(Folderol.logic_term, Folderol.logic_form) :: Folderol.logic_form
  def subst_bound(t, form) do
    do_subst(t, 0, form)
  end

  defp do_subst(t, i, {:Pred,  a, ts}), do: {:Pred, a, Enum.map(ts, &(replace_term({{:Bound, i}, t}, &1)))}
  defp do_subst(t, i, {:Conn,  b, as}), do: {:Conn, b, Enum.map(as, &(do_subst(t, i, &1)))}
  defp do_subst(t, i, {:Quant, q, b, a}), do: {:Quant, q, b, do_subst(t, i+1, a)}

end

defmodule Folderol.Parser do
  import Folderol.Logic

  # Scanning of identifiers and keywords
  def token_of(a), do:  if a in ['ALL','EXISTS'], do: {:Key, a}, else: {:Id, a}
  def is_letter_or_digit(c), do: (c in ?A..?Z) or (c in ?a..?z) or (c in ?0..?9)

  def scan_ident(front, []), do: {token_of(Enum.reverse front), []};
  def scan_ident(front, [c | cs]) do
    if is_letter_or_digit(c), do: scan_ident([c | front], cs),
    else: {token_of(Enum.reverse front), [c | cs]}
  end

  @type token :: {:Key, [char]} | {:Id, [char]}

  @doc "Scanning, recognizing --> and <->, skipping blanks, etc."
  @spec scan([token], [char]) :: [token]
  def scan(front_toks, []), do: Enum.reverse front_toks #   (*end of char list*)
  #  (*long infix operators*)
  def scan(front_toks, [?-, ?-, ?> | cs]), do:  scan([{:Key, '-->'} | front_toks], cs)
  def scan(front_toks, [?<, ?-, ?> | cs]), do:  scan([{:Key, '<->'} | front_toks],  cs)
  def scan(front_toks, [c|cs]) when c in [?\s, ?\t, ?\n], do: scan(front_toks,  cs)
  def scan(front_toks, [c|cs]) do
    if is_letter_or_digit(c) do
      scannext(front_toks, scan_ident([c], cs))
    else scan([{:Key, [c]} | front_toks], cs) end
  end
  def scannext(front_toks, {tok, cs}), do: scan([tok|front_toks], cs)

  # Parsing a list of tokens
  # fun apfst f (x,toks) = (f x, toks);
  def apfst(f, {x, toks}) when is_function(f, 1), do: {f.(x), toks}
#  def apfst2(f, {x, toks}) when is_function(f, 2), do: {fn y -> f.(x, y) end, toks}
  # def apfst2(f, {x, toks}) when is_function(f, 1), do: {f.(x), toks}
  # def apfst3(f, {x, y, toks}) when is_function(f, 3), do: {fn xs -> f.(x, y, xs) end, toks}
  # (*Functions for constructing results*)
  def cons(x, xs), do: [x | xs];
  def makeFun(fu, ts), do: {:Fun, fu, ts}
  def makePred(id, ts), do: {:Pred, id, ts}
  def makeNeg(a), do:  {:Conn, '~', [a]}
  def makeConn(a, aa, b), do: {:Conn, a, [aa,b]}
  def makeQuant(q, b, a), do: {:Quant, q, b, abstract({:Fun, b, []}, a)}

  @doc "Repeated parsing, returning the list of results"
  def parse_repeat({a, parsefn}, [{:Key, b} | toks]) do  # (*    a<phrase>...a<phrase>  *)
          if a == b do parse_repeat1({a,parsefn}, toks)
          else {[], [{:Key, b} | toks]} end
  end
  def parse_repeat({_a, parsefn}, toks) when is_function(parsefn), do: {[], toks}

  def parse_repeat1({a,parsefn}, toks) do #          (*    <phrase>a...a<phrase>  *)
      {u, toks2} = parsefn.(toks)
      apfst(&(cons u, &1), parse_repeat({a, parsefn}, toks2))
  end

  def rightparen({x, [{:Key, ')'} | toks]}), do: {x, toks}
  def rightparen(_), do: raise %SyntaxError{description: "Symbol ) expected",
                                            line: __ENV__.line, file: __ENV__.file}

  def parse_term([{:Id, a}, {:Key, '('} | toks]) do
        apfst(&(makeFun a, &1), {rightparen(parse_repeat1(',', &parse_term/1)), toks})
  end
  def parse_term([{:Id, a} | toks]), do: {{:Fun,a,[]}, toks}
  def parse_term([{:Key, '?'}, {:Id, a} | toks]), do: {{:Var, a}, toks}
  def parse_term(_), do: raise %SyntaxError{description: "Syntax of term",
                                           line: __ENV__.line, file: __ENV__.file}

  @doc "Precedence table"
  def prec_of('~'),   do: 4
  def prec_of('&'),   do: 3
  def prec_of('|'),   do: 2
  def prec_of('<->'), do: 1
  def prec_of('-->'), do: 1
  def prec_of(_),     do: -1 #  (*means not an infix*);


  @doc """
  Parsing of formulae;  prec is the precedence of the operator to the left;
  parsing stops at an operator with lower precedence
  """
  def parse([{:Key, 'ALL'}, {:Id, a}, {:Key, '.'} | toks]) do
    apfst(&(makeQuant "ALL", a, &1), parse(toks)) end
  def parse([{:Key, 'EXISTS'}, {:Id, a}, {:Key, '.'} | toks]) do
    apfst(&(makeQuant "EXISTS", a, &1), parse(toks)) end
  def parse(toks), do: parsefix(0, parse_atom(toks))

  def parsefix(prec, {a, [{:Key, co} | toks]}) do
    IO.inspect co
    if prec_of(co) < prec do {a, [{:Key, co} | toks]}
    else parsefix(prec,
                  apfst(&(makeConn co, a, &1),
                        parsefix(prec_of(co), parse_atom(toks))))
    end
  end
  def parsefix(_prec, {a, toks}), do: {a, toks} |> IO.inspect

  def parse_atom([{:Key, '~'} | toks]), do: apfst(&makeNeg/1, parse_atom(toks))
  def parse_atom([{:Key, '('} | toks]), do: rightparen(parse(toks))
  def parse_atom([{:Id, pr}, {:Key, '('} | toks]) do
    apfst(&(makePred pr, &1), rightparen( parse_repeat1({',', &parse_term/1}, toks))) end
  def parse_atom([{:Id, pr} | toks]), do: {{Pred, pr, []}, toks}
  def parse_atom(_), do: raise %SyntaxError{description: "Syntax of formula",
                                            line: __ENV__.line, file: __ENV__.file}

  @doc "check that no tokens remain"
  def parse_end({x, []}), do: x
  def parse_end({_, [_|_]}), do: raise %SyntaxError{description: "Extra characters in formula",
                                                    line: __ENV__.line, file: __ENV__.file}

  def read(a), do: parse_end(parse(scan([], a)))

end

defmodule LocalTest do
  import Folderol.Parser
  tokens = scan [], '~A'
  {ast, rest} = parse tokens
  IO.inspect ast

end
