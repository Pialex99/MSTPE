Require Import FunInd.
From Src Require Import Tree.
From CPS Require Import Tree.
From Common Require Import Literal Primitive.



Fixpoint cps_rec (nf: nat) (t: Src.Tree.term) (ctx: (nat * CPS.Tree.atom) -> (nat * CPS.Tree.term)): nat * CPS.Tree.term :=
  match t with 
  | Src.Tree.Var n => ctx (nf, Var n)
  | Src.Tree.Const l => ctx (nf, Lit l)
  | Src.Tree.Let x t rest => 
      let (nf', rest') := cps_rec nf rest ctx in
      cps_rec nf' t (fun r => 
        let (nf'', n) := r in
        (nf'', CPS.Tree.LetU x Id n rest'))
  | Src.Tree.LetRec (Src.Tree.Func fname farg fbody) rest =>
      let retC := nf in
      let (nf', fbody') := cps_rec (nf + 1) fbody (fun r => 
        let (nf_f, f) := r in (nf_f, CPS.Tree.AppC1 retC f)) in
      let (nf'', rest') := cps_rec nf' rest ctx in 
      (nf'', CPS.Tree.LetF (Fnt fname retC farg fbody') rest')
  | Src.Tree.App f t =>
      let c := nf in
      let carg := nf + 1 in
      let (nf', cbody) := ctx (nf + 2, Var carg) in 
      cps_rec nf' f (fun r => 
        let (nf'', f') := r in
        cps_rec nf'' t (fun r' => 
          let (nf3, t') := r' in
            (nf3, CPS.Tree.LetC (Cnt1 c carg cbody) (AppF f' c t'))
          )
        )
  | Src.Tree.In => 
      let n := nf in
      let (nf', r) := ctx (nf + 1, Var n) in
      (nf', CPS.Tree.LetIn n r)
  | Src.Tree.Out t => 
      let n := nf in
      let (nf', rest) := ctx (nf + 1, Var n) in
      cps_rec nf' t (fun r => 
        let (nf'', t') := r in 
        (nf'', CPS.Tree.LetOut n t' rest)
      )
  | Src.Tree.Ite cond thent elset => 
      let c := nf in 
      let carg := nf + 1 in 
      let (nf', cbody) := ctx (nf + 2, Var carg) in 
      let thenc := nf' in 
      let (nf2, thent') := cps_rec (nf' + 1) thent (fun r => 
        let (nf3, t) := r in 
        (nf3, CPS.Tree.AppC1 c t)
      ) in 
      let elsec := nf2 in
      let (nf4, elset') := cps_rec (nf2 + 1) elset (fun r => 
        let (nf5, t) := r in 
        (nf5, CPS.Tree.AppC1 c t)
      ) in 
      cps_rec nf4 cond (fun r => 
        let (nf6, cond') := r in
        (nf6, CPS.Tree.LetC (Cnt1 c carg cbody) (
          CPS.Tree.LetC (Cnt0 thenc thent') (
            CPS.Tree.LetC (Cnt0 elsec elset') (
              CPS.Tree.Ite cond' thenc elsec
            )
          )
        ))
      )
  | Src.Tree.BinaryOp op t1 t2 => 
      let n := nf in
      cps_rec (nf + 1) t1 (fun r => 
        let (nf1, t1') := r in
        cps_rec nf1 t2 (fun r' =>
          let (nf2, t2') := r' in
          let (nf3, t) := ctx (nf2, Var n) in
          (nf3, CPS.Tree.LetB n op t1' t2' t)
        )  
      )
  | Src.Tree.UnaryOp op t =>
      let n := nf in
      cps_rec (nf + 1) t (fun r => 
        let (nf1, t') := r in
        let (nf2, rest) := ctx (nf1, Var n) in
        (nf2, CPS.Tree.LetU n op t' rest)
      )
  | Src.Tree.Match scrut (larg, lt) (rarg, rt) =>
      let c := nf in 
      let carg := nf + 1 in 
      let (nf1, cbody) := ctx (nf + 2, Var carg) in 
      let cnt := CPS.Tree.Cnt1 c carg cbody in
      let lc := nf1 in
      let (nf2, lbody) := cps_rec (nf1 + 1) lt (fun r => 
        let (nf3, lt') := r in
        (nf3, CPS.Tree.AppC1 c lt')
      ) in
      let lcnt := CPS.Tree.Cnt1 lc larg lbody in
      let rc := nf2 in
      let (nf4, rbody) := cps_rec (nf2 + 1) rt (fun r =>
        let (nf5, rt') := r in
        (nf5, CPS.Tree.AppC1 c rt')
      ) in
      let rcnt := CPS.Tree.Cnt1 rc rarg rbody in
      cps_rec nf4 scrut (fun r => 
        let (nf6, scrut') := r in
        (nf6, CPS.Tree.LetC cnt (
          CPS.Tree.LetC lcnt (
            CPS.Tree.LetC rcnt (
              CPS.Tree.Match scrut' lc rc
            )
          )
        ))
      )
  end.


