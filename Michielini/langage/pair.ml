open Definitions

let pair k =
	let x = var k
	and y = var (k+1)
	and f = var (k+2) in
	MLambda (x, k, MLambda (y, k+1, MLambda (f, k+2, MApp (MApp (MVar f, MVar x), MVar y))))

let fst k =
	let p = var k
	and a = var (k+1)
	and b = var (k+2) in
	MLambda (p, k, MApp (MVar p, (MLambda (a, k+1, MLambda (b, k+2, MVar a)))))

let snd k =
	let p = var k
	and a = var (k+1)
	and b = var (k+2) in
	MLambda (p, k, MApp (MVar p, (MLambda (a, k+1, MLambda (b, k+2, MVar b)))))

let nextpair k =
	let mpair = pair k
	and msnd = snd k in
	let g = var (k+3)
	and p = var (k+4)
	and a = var (k+5) in
	MLambda (g, k+3, (MLambda (p, k+4, MApp (MLambda (a, k+5, MApp (MApp (mpair, MVar a), MApp (MVar g, MVar a))), MApp (msnd, MVar p)))))
