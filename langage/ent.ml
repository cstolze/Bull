open Pair
open Definitions

let rec n_to_lambda n =
	let k = ref 0 in
	let rec aux i k =
	if i = 0
		then
			let m = MLambda (var !k, !k, MLambda (var (!k+1), !k+1, MVar (var (!k+1)))) in
			k := !k + 2;
			m
		else
			let m' = aux (i-1) k in
			let x = var (!k+1)
			and f = var (!k) in
			let m = MLambda (f, !k, MLambda (x, !k+1, MApp (MVar f, MApp (MApp (m', MVar f), MVar x)))) in
			k := !k+2;
			m
	in
	!k, aux n k

let plus k =
	let n = var k
	and m = var (k+1)
	and x = var (k+3)
	and f = var (k+2) in
	MLambda (n, k, MLambda (m, k+1, MLambda (f, k+2, MLambda (x, k+3, MApp (MApp (MVar m, MVar f), MApp (MApp (MVar n, MVar f), MVar x))))))

let fois k =
	let n = var k
	and m = var (k+1)
	and f = var (k+2) in
	MLambda (n, k, MLambda (m, k+1, MLambda (f, k+2, MApp (MVar m, MApp (MVar n, MVar f)))))

let exp k =
	let n = var k	
	and m = var (k+1) in
	MLambda (n, k, MLambda (m, k+1, MApp (MVar m, MVar n)))

let pred k =
	let mnp = nextpair k
	and mp = pair k
	and mfst = fst k in
	let n = var (k+6)
	and f = var (k+7)
	and x = var (k+8) in
	MLambda (n, k+6, (MLambda (f, k+7, MLambda (x, k+8, MApp (mfst, MApp (MApp (MVar n, MApp (mnp, MVar f)), MApp (MApp (mp, MVar x), MVar x)))))))

let iszero k =
	let n = var k
	and x = var (k+1)
	and y = var (k+2)
	and a = var (k+3) in
	MLambda (n, k, MLambda (x, k+1, MLambda (y, k+2, MApp (MApp (MVar n, (MLambda (a, k+3, MVar y))), MVar x))))

let sub k =
	let mpred = pred k in
	let n = var (k+9)
	and m = var (k+10) in
	MLambda (n, k+9, MLambda (m, k+10, MApp (MApp (MVar m, mpred), MVar n)))

let lessthan k =
	let miz = iszero k
	and msb = sub k in
	let n = var (k+11)
	and m = var (k+12) in
	MLambda (n, k+11, MLambda (m, k+12, MApp (miz, (MApp (MApp (msb, MVar n), MVar m)))))
