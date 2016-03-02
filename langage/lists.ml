open Definitions

let empty k =
	let f = var k
	and a = var (k+1) in
	MLambda (f, k, MLambda (a, k+1, MVar a))

let head k =
	let l = var k
	and a = var (k+1)
	and b = var (k+2)
	and c = var (k+3) in
	MLambda (l, k, MLambda (c, k+3, MApp (MApp (MVar l, MLambda (a, k+1, MLambda (b, k+2, MVar a))), MVar c)))

let cons k =
	let x = var k
	and l = var (k+1)
	and f = var (k+2)
	and a = var (k+3) in
	MLambda (x, k, MLambda (l, k+1, MLambda (f, k+2, MLambda (a, k+3, MApp (MApp (MVar f, MVar x), MApp (MApp (MVar l, MVar f), MVar a))))))

let map k =
	let g = var k
	and l = var (k+1)
	and f = var (k+2)
	and a = var (k+3)
	and b = var (k+4) in
	MLambda (g, k, MLambda (l, k+1, MLambda (f, k+2, MApp (MVar l, MLambda (a, k+3, MLambda (b, k+4, MApp (MApp (MVar f, MApp (MVar g, MVar a)), MVar b)))))))
