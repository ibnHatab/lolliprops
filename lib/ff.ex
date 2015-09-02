defmodule FF do

  def exist(x, y, args) do
    IO.inspect {x, y}
    IO.inspect args
  end


end

defmodule FFTest do
  import FF

  exist(1,2) do
    :ok
  end

end
