let bigger_than_10 x = x > 10

let [@contract] run
  (x : int [@pred bigger_than_10])
  : int [@pred bigger_than_10] =
  x
