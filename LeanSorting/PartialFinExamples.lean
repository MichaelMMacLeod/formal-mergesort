import LeanSorting.PartialFin

-- All of the following should evaluate to 'true'. We can't use 'example' here to test these
-- more nicely because 'mergeSortPartialFin' is, well, partial.

#eval #[].mergeSortPartialFin (α := Nat) = #[]
#eval #[0].mergeSortPartialFin = #[0]
#eval #[0, 1].mergeSortPartialFin = #[0, 1]
#eval #[1, 0].mergeSortPartialFin = #[0, 1]
#eval #[0, 0].mergeSortPartialFin = #[0, 0]
#eval #[1, 1].mergeSortPartialFin = #[1, 1]
#eval #[0, 1, 2].mergeSortPartialFin = #[0, 1, 2]
#eval #[0, 2, 1].mergeSortPartialFin = #[0, 1, 2]
#eval #[1, 0, 2].mergeSortPartialFin = #[0, 1, 2]
#eval #[1, 2, 0].mergeSortPartialFin = #[0, 1, 2]
#eval #[2, 0, 1].mergeSortPartialFin = #[0, 1, 2]
#eval #[2, 1, 0].mergeSortPartialFin = #[0, 1, 2]
#eval #[0, 0, 0].mergeSortPartialFin = #[0, 0, 0]
#eval #[1, 1, 1].mergeSortPartialFin = #[1, 1, 1]
#eval #[2, 2, 2].mergeSortPartialFin = #[2, 2, 2]
#eval #[10, 9, 8, 7, 6, 5, 4, 3, 2, 1].mergeSortPartialFin = #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
#eval #[10, 0, 100, 1, 200, 2].mergeSortPartialFin = #[0, 1, 2, 10, 100, 200]
