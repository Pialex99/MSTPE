Require Import FunInd.
From Src Require Import Tree Fun_sem.
From CPS Require Import Tree Fun_sem.
From Common Require Import Literal Primitive.
From Utils Require Import Env.

Open Scope list_scope.

Module ST := Src.Tree.
Module SV := Src.Fun_sem.
Module CT := CPS.Tree.
Module CV := CPS.Fun_sem.

Fixpoint cps_rec (nf: nat) (t: ST.term) (ctx: (nat * CT.atom) -> (nat * CT.term)): nat * CT.term :=
  match t with 
  | ST.Var n => ctx (nf, Var n)
  | ST.Const l => ctx (nf, CT.Lit l)
  | ST.Let x t rest => 
      let (nf', rest') := cps_rec nf rest ctx in
      cps_rec nf' t (fun r => 
        let (nf'', n) := r in
        (nf'', CT.LetU x Id n rest'))
  | ST.LetRec (ST.Fnt fname farg fbody) rest =>
      let retC := nf in
      let (nf', fbody') := cps_rec (nf + 1) fbody (fun r => 
        let (nf_f, f) := r in (nf_f, CT.AppC1 retC f)) in
      let (nf'', rest') := cps_rec nf' rest ctx in 
      (nf'', CT.LetF (Fnt fname retC farg fbody') rest')
  | ST.App f t =>
      let c := nf in
      let carg := nf + 1 in
      let (nf', cbody) := ctx (nf + 2, Var carg) in 
      cps_rec nf' f (fun r => 
        let (nf'', f') := r in
        cps_rec nf'' t (fun r' => 
          let (nf3, t') := r' in
            (nf3, CT.LetC (Cnt1 c carg cbody) (AppF f' c t'))
          )
        )
  | ST.In => 
      let n := nf in
      let (nf', r) := ctx (nf + 1, Var n) in
      (nf', CT.LetIn n r)
  | ST.Out t => 
      let n := nf in
      let (nf', rest) := ctx (nf + 1, Var n) in
      cps_rec nf' t (fun r => 
        let (nf'', t') := r in 
        (nf'', CT.LetOut n t' rest)
      )
  | ST.Ite cond thent elset => 
      let c := nf in 
      let carg := nf + 1 in 
      let (nf', cbody) := ctx (nf + 2, Var carg) in 
      let thenc := nf' in 
      let (nf2, thent') := cps_rec (nf' + 1) thent (fun r => 
        let (nf3, t) := r in 
        (nf3, CT.AppC1 c t)
      ) in 
      let elsec := nf2 in
      let (nf4, elset') := cps_rec (nf2 + 1) elset (fun r => 
        let (nf5, t) := r in 
        (nf5, CT.AppC1 c t)
      ) in 
      cps_rec nf4 cond (fun r => 
        let (nf6, cond') := r in
        (nf6, CT.LetC (Cnt1 c carg cbody) (
          CT.LetC (Cnt0 thenc thent') (
            CT.LetC (Cnt0 elsec elset') (
              CT.Ite cond' thenc elsec
            )
          )
        ))
      )
  | ST.BinaryOp op t1 t2 => 
      let n := nf in
      cps_rec (nf + 1) t1 (fun r => 
        let (nf1, t1') := r in
        cps_rec nf1 t2 (fun r' =>
          let (nf2, t2') := r' in
          let (nf3, t) := ctx (nf2, Var n) in
          (nf3, CT.LetB n op t1' t2' t)
        )  
      )
  | ST.UnaryOp op t =>
      let n := nf in
      cps_rec (nf + 1) t (fun r => 
        let (nf1, t') := r in
        let (nf2, rest) := ctx (nf1, Var n) in
        (nf2, CT.LetU n op t' rest)
      )
  | ST.Match scrut (larg, lt) (rarg, rt) =>
      let c := nf in 
      let carg := nf + 1 in 
      let (nf1, cbody) := ctx (nf + 2, Var carg) in 
      let cnt := CT.Cnt1 c carg cbody in
      let lc := nf1 in
      let (nf2, lbody) := cps_rec (nf1 + 1) lt (fun r => 
        let (nf3, lt') := r in
        (nf3, CT.AppC1 c lt')
      ) in
      let lcnt := CT.Cnt1 lc larg lbody in
      let rc := nf2 in
      let (nf4, rbody) := cps_rec (nf2 + 1) rt (fun r =>
        let (nf5, rt') := r in
        (nf5, CT.AppC1 c rt')
      ) in
      let rcnt := CT.Cnt1 rc rarg rbody in
      cps_rec nf4 scrut (fun r => 
        let (nf6, scrut') := r in
        (nf6, CT.LetC cnt (
          CT.LetC lcnt (
            CT.LetC rcnt (
              CT.Match scrut' lc rc
            )
          )
        ))
      )
  end.

Fixpoint cps_rec_v (nf : nat) (v : SV.value) {struct v} : nat * CV.value :=
  match v with 
  | SV.Lit l => (nf, CV.Lit l)
  | SV.Tuple v1 v2 => 
      let (nf1, v1') := cps_rec_v nf v1 in
      let (nf2, v2') := cps_rec_v nf v2 in
      (nf2, CV.Tuple v1' v2')
  | SV.Left v => 
      let (nf1, v') := cps_rec_v nf v in
      (nf1, CV.Left v')
  | SV.Right v => 
      let (nf1, v') := cps_rec_v nf v in
      (nf1, CV.Right v')
  | SV.Fun (ST.Fnt fname farg fbody) env => 
      let fix cps_rec_v_env nf env := 
        match env with
        | nil => (nf, nil)
        | (n, v) :: env => 
            let (nf', v') := cps_rec_v nf v in
            let (nf'', env') := cps_rec_v_env nf' env in
            (nf'', (n, v') :: env')
        end in
      let (nf', env') := cps_rec_v_env nf env in
      let retC := nf' in
      let (nf'', fbody') := cps_rec (nf' + 1) fbody (fun r =>
        let (nf0, res) := r in
        (nf0, CPS.Tree.AppC1 retC res)
      ) in
      (nf'', CV.Fun (CPS.Tree.Fnt fname retC farg fbody') env')
  end.
