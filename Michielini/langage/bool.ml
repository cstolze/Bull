open Definitions

let vrai k =
	let x = var k
	and y = var (k+1) in
	MLambda (x, k, MLambda (y, k+1, MVar x))

let faux k =
	let x = var k
	and y = var (k+1) in
	MLambda (x, k, MLambda (y, k+1, MVar y))

let et k =
	let a = var k
	and b = var (k+1)
	and x = var (k+2)
	and y = var (k+3) in
	MLambda (a, k, MLambda (b, k+1, MLambda (x, k+2, MLambda (y, k+3, MApp (MApp (MVar a, MApp (MApp (MVar b, MVar x), MVar y)), MVar y)))))

let ou k =
	let a = var k
	and b = var (k+1)
	and x = var (k+2)
	and y = var (k+3) in
	MLambda (a, k, MLambda (b, k+1, MLambda (x, k+2, MLambda (y, k+3, MApp (MApp (MVar a, MVar x), MApp (MApp (MVar b, MVar x), MVar y))))))

let xor k =
	let a = var k
	and b = var (k+1)
	and x = var (k+2)
	and y = var (k+3) in
	MLambda (a, k, MLambda (b, k+1, MLambda (x, k+2, MLambda (y, k+3, MApp (MApp (MVar a, MApp (MApp (MVar b, MVar y), MVar x)), MApp (MApp (MVar b, MVar x), MVar y))))))

let non k =
	let a = var k
	and x = var (k+1)
	and y = var (k+2) in
	MLambda (a, k, MLambda (x, k+1, MLambda (y, k+2, MApp (MApp (MVar a, MVar y), MVar x))))

let ifthenelse k =
	let a = var k
	and x = var (k+1)
	and y = var (k+2) in
	MLambda (a, k, MLambda (x, k+1, MLambda (y, k+2, MApp (MApp (MVar a, MVar x), MVar y))))

