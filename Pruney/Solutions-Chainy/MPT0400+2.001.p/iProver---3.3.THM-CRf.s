%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:01 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 152 expanded)
%              Number of clauses        :   24 (  31 expanded)
%              Number of leaves         :    7 (  41 expanded)
%              Depth                    :   17
%              Number of atoms          :  182 ( 679 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f9])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f16,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK2(X1,X4))
        & r2_hidden(sK2(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK1(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK1(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK2(X1,X4))
              & r2_hidden(sK2(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f16,f15])).

fof(f23,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK2(X1,X4),X1)
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f24,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(X4,sK2(X1,X4))
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(sK1(X0,X1),X3)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
     => r1_setfam_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_setfam_1(X1,X2)
          & r1_setfam_1(X0,X1) )
       => r1_setfam_1(X0,X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_setfam_1(X0,X2)
      & r1_setfam_1(X1,X2)
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_setfam_1(X0,X2)
      & r1_setfam_1(X1,X2)
      & r1_setfam_1(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_setfam_1(X0,X2)
        & r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
   => ( ~ r1_setfam_1(sK3,sK5)
      & r1_setfam_1(sK4,sK5)
      & r1_setfam_1(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_setfam_1(sK3,sK5)
    & r1_setfam_1(sK4,sK5)
    & r1_setfam_1(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f8,f18])).

fof(f28,plain,(
    r1_setfam_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    ~ r1_setfam_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    r1_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_6,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(sK2(X1,X2),X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_4,plain,
    ( r1_setfam_1(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_596,plain,
    ( ~ r1_setfam_1(X0,X1)
    | r1_setfam_1(X0,X2)
    | r2_hidden(sK2(X1,sK1(X0,X2)),X1) ),
    inference(resolution,[status(thm)],[c_6,c_4])).

cnf(c_5,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r1_tarski(X2,sK2(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_606,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r1_setfam_1(X1,X2)
    | r1_setfam_1(X0,X3)
    | r1_tarski(sK2(X1,sK1(X0,X3)),sK2(X2,sK2(X1,sK1(X0,X3)))) ),
    inference(resolution,[status(thm)],[c_596,c_5])).

cnf(c_965,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r1_setfam_1(X1,X2)
    | r1_setfam_1(X0,X3)
    | r2_hidden(X4,sK2(X2,sK2(X1,sK1(X0,X3))))
    | ~ r2_hidden(X4,sK2(X1,sK1(X0,X3))) ),
    inference(resolution,[status(thm)],[c_2,c_606])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1799,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r1_setfam_1(X1,X2)
    | r1_setfam_1(X0,X3)
    | ~ r2_hidden(sK0(X4,sK2(X2,sK2(X1,sK1(X0,X3)))),sK2(X1,sK1(X0,X3)))
    | r1_tarski(X4,sK2(X2,sK2(X1,sK1(X0,X3)))) ),
    inference(resolution,[status(thm)],[c_965,c_0])).

cnf(c_510,plain,
    ( ~ r1_setfam_1(X0,X1)
    | r1_setfam_1(X0,X2)
    | r1_tarski(sK1(X0,X2),sK2(X1,sK1(X0,X2))) ),
    inference(resolution,[status(thm)],[c_5,c_4])).

cnf(c_963,plain,
    ( ~ r1_setfam_1(X0,X1)
    | r1_setfam_1(X0,X2)
    | r2_hidden(X3,sK2(X1,sK1(X0,X2)))
    | ~ r2_hidden(X3,sK1(X0,X2)) ),
    inference(resolution,[status(thm)],[c_2,c_510])).

cnf(c_4468,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r1_setfam_1(X1,X2)
    | r1_setfam_1(X0,X3)
    | ~ r2_hidden(sK0(X4,sK2(X2,sK2(X1,sK1(X0,X3)))),sK1(X0,X3))
    | r1_tarski(X4,sK2(X2,sK2(X1,sK1(X0,X3)))) ),
    inference(resolution,[status(thm)],[c_1799,c_963])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_5934,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r1_setfam_1(X1,X2)
    | r1_setfam_1(X0,X3)
    | r1_tarski(sK1(X0,X3),sK2(X2,sK2(X1,sK1(X0,X3)))) ),
    inference(resolution,[status(thm)],[c_4468,c_1])).

cnf(c_3,plain,
    ( r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r1_tarski(sK1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_5948,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r1_setfam_1(X1,X2)
    | r1_setfam_1(X0,X3)
    | ~ r2_hidden(sK2(X2,sK2(X1,sK1(X0,X3))),X3) ),
    inference(resolution,[status(thm)],[c_5934,c_3])).

cnf(c_607,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r1_setfam_1(X1,X2)
    | r1_setfam_1(X0,X3)
    | r2_hidden(sK2(X2,sK2(X1,sK1(X0,X3))),X2) ),
    inference(resolution,[status(thm)],[c_596,c_6])).

cnf(c_6294,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r1_setfam_1(X1,X2)
    | r1_setfam_1(X0,X2) ),
    inference(resolution,[status(thm)],[c_5948,c_607])).

cnf(c_8,negated_conjecture,
    ( r1_setfam_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_6344,plain,
    ( ~ r1_setfam_1(X0,sK4)
    | r1_setfam_1(X0,sK5) ),
    inference(resolution,[status(thm)],[c_6294,c_8])).

cnf(c_6346,plain,
    ( ~ r1_setfam_1(sK3,sK4)
    | r1_setfam_1(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_6344])).

cnf(c_7,negated_conjecture,
    ( ~ r1_setfam_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_9,negated_conjecture,
    ( r1_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6346,c_7,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:11:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.69/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/0.98  
% 2.69/0.98  ------  iProver source info
% 2.69/0.98  
% 2.69/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.69/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/0.98  git: non_committed_changes: false
% 2.69/0.98  git: last_make_outside_of_git: false
% 2.69/0.98  
% 2.69/0.98  ------ 
% 2.69/0.98  ------ Parsing...
% 2.69/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.69/0.98  
% 2.69/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/0.98  ------ Proving...
% 2.69/0.98  ------ Problem Properties 
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  clauses                                 10
% 2.69/0.98  conjectures                             3
% 2.69/0.98  EPR                                     4
% 2.69/0.98  Horn                                    8
% 2.69/0.98  unary                                   3
% 2.69/0.98  binary                                  3
% 2.69/0.98  lits                                    21
% 2.69/0.98  lits eq                                 0
% 2.69/0.98  fd_pure                                 0
% 2.69/0.98  fd_pseudo                               0
% 2.69/0.98  fd_cond                                 0
% 2.69/0.98  fd_pseudo_cond                          0
% 2.69/0.98  AC symbols                              0
% 2.69/0.98  
% 2.69/0.98  ------ Input Options Time Limit: Unbounded
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  ------ 
% 2.69/0.98  Current options:
% 2.69/0.98  ------ 
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  ------ Proving...
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  % SZS status Theorem for theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  fof(f1,axiom,(
% 2.69/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f5,plain,(
% 2.69/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.69/0.98    inference(ennf_transformation,[],[f1])).
% 2.69/0.98  
% 2.69/0.98  fof(f9,plain,(
% 2.69/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.69/0.98    inference(nnf_transformation,[],[f5])).
% 2.69/0.98  
% 2.69/0.98  fof(f10,plain,(
% 2.69/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.69/0.98    inference(rectify,[],[f9])).
% 2.69/0.98  
% 2.69/0.98  fof(f11,plain,(
% 2.69/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.69/0.98    introduced(choice_axiom,[])).
% 2.69/0.98  
% 2.69/0.98  fof(f12,plain,(
% 2.69/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.69/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).
% 2.69/0.98  
% 2.69/0.98  fof(f20,plain,(
% 2.69/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f12])).
% 2.69/0.98  
% 2.69/0.98  fof(f2,axiom,(
% 2.69/0.98    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f6,plain,(
% 2.69/0.98    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 2.69/0.98    inference(ennf_transformation,[],[f2])).
% 2.69/0.98  
% 2.69/0.98  fof(f13,plain,(
% 2.69/0.98    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1)))),
% 2.69/0.98    inference(nnf_transformation,[],[f6])).
% 2.69/0.98  
% 2.69/0.98  fof(f14,plain,(
% 2.69/0.98    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 2.69/0.98    inference(rectify,[],[f13])).
% 2.69/0.98  
% 2.69/0.98  fof(f16,plain,(
% 2.69/0.98    ! [X4,X1] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) => (r1_tarski(X4,sK2(X1,X4)) & r2_hidden(sK2(X1,X4),X1)))),
% 2.69/0.98    introduced(choice_axiom,[])).
% 2.69/0.98  
% 2.69/0.98  fof(f15,plain,(
% 2.69/0.98    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK1(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK1(X0,X1),X0)))),
% 2.69/0.98    introduced(choice_axiom,[])).
% 2.69/0.98  
% 2.69/0.98  fof(f17,plain,(
% 2.69/0.98    ! [X0,X1] : ((r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK1(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK1(X0,X1),X0))) & (! [X4] : ((r1_tarski(X4,sK2(X1,X4)) & r2_hidden(sK2(X1,X4),X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 2.69/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f16,f15])).
% 2.69/0.98  
% 2.69/0.98  fof(f23,plain,(
% 2.69/0.98    ( ! [X4,X0,X1] : (r2_hidden(sK2(X1,X4),X1) | ~r2_hidden(X4,X0) | ~r1_setfam_1(X0,X1)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f17])).
% 2.69/0.98  
% 2.69/0.98  fof(f25,plain,(
% 2.69/0.98    ( ! [X0,X1] : (r1_setfam_1(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f17])).
% 2.69/0.98  
% 2.69/0.98  fof(f24,plain,(
% 2.69/0.98    ( ! [X4,X0,X1] : (r1_tarski(X4,sK2(X1,X4)) | ~r2_hidden(X4,X0) | ~r1_setfam_1(X0,X1)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f17])).
% 2.69/0.98  
% 2.69/0.98  fof(f22,plain,(
% 2.69/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f12])).
% 2.69/0.98  
% 2.69/0.98  fof(f21,plain,(
% 2.69/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f12])).
% 2.69/0.98  
% 2.69/0.98  fof(f26,plain,(
% 2.69/0.98    ( ! [X0,X3,X1] : (r1_setfam_1(X0,X1) | ~r1_tarski(sK1(X0,X1),X3) | ~r2_hidden(X3,X1)) )),
% 2.69/0.98    inference(cnf_transformation,[],[f17])).
% 2.69/0.98  
% 2.69/0.98  fof(f3,conjecture,(
% 2.69/0.98    ! [X0,X1,X2] : ((r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)) => r1_setfam_1(X0,X2))),
% 2.69/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.69/0.98  
% 2.69/0.98  fof(f4,negated_conjecture,(
% 2.69/0.98    ~! [X0,X1,X2] : ((r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)) => r1_setfam_1(X0,X2))),
% 2.69/0.98    inference(negated_conjecture,[],[f3])).
% 2.69/0.98  
% 2.69/0.98  fof(f7,plain,(
% 2.69/0.98    ? [X0,X1,X2] : (~r1_setfam_1(X0,X2) & (r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)))),
% 2.69/0.98    inference(ennf_transformation,[],[f4])).
% 2.69/0.98  
% 2.69/0.98  fof(f8,plain,(
% 2.69/0.98    ? [X0,X1,X2] : (~r1_setfam_1(X0,X2) & r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1))),
% 2.69/0.98    inference(flattening,[],[f7])).
% 2.69/0.98  
% 2.69/0.98  fof(f18,plain,(
% 2.69/0.98    ? [X0,X1,X2] : (~r1_setfam_1(X0,X2) & r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)) => (~r1_setfam_1(sK3,sK5) & r1_setfam_1(sK4,sK5) & r1_setfam_1(sK3,sK4))),
% 2.69/0.98    introduced(choice_axiom,[])).
% 2.69/0.98  
% 2.69/0.98  fof(f19,plain,(
% 2.69/0.98    ~r1_setfam_1(sK3,sK5) & r1_setfam_1(sK4,sK5) & r1_setfam_1(sK3,sK4)),
% 2.69/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f8,f18])).
% 2.69/0.98  
% 2.69/0.98  fof(f28,plain,(
% 2.69/0.98    r1_setfam_1(sK4,sK5)),
% 2.69/0.98    inference(cnf_transformation,[],[f19])).
% 2.69/0.98  
% 2.69/0.98  fof(f29,plain,(
% 2.69/0.98    ~r1_setfam_1(sK3,sK5)),
% 2.69/0.98    inference(cnf_transformation,[],[f19])).
% 2.69/0.98  
% 2.69/0.98  fof(f27,plain,(
% 2.69/0.98    r1_setfam_1(sK3,sK4)),
% 2.69/0.98    inference(cnf_transformation,[],[f19])).
% 2.69/0.98  
% 2.69/0.98  cnf(c_2,plain,
% 2.69/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.69/0.98      inference(cnf_transformation,[],[f20]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_6,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,X1)
% 2.69/0.98      | ~ r2_hidden(X2,X0)
% 2.69/0.98      | r2_hidden(sK2(X1,X2),X1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f23]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_4,plain,
% 2.69/0.98      ( r1_setfam_1(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.69/0.98      inference(cnf_transformation,[],[f25]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_596,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,X1)
% 2.69/0.98      | r1_setfam_1(X0,X2)
% 2.69/0.98      | r2_hidden(sK2(X1,sK1(X0,X2)),X1) ),
% 2.69/0.98      inference(resolution,[status(thm)],[c_6,c_4]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,X1)
% 2.69/0.98      | ~ r2_hidden(X2,X0)
% 2.69/0.98      | r1_tarski(X2,sK2(X1,X2)) ),
% 2.69/0.98      inference(cnf_transformation,[],[f24]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_606,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,X1)
% 2.69/0.98      | ~ r1_setfam_1(X1,X2)
% 2.69/0.98      | r1_setfam_1(X0,X3)
% 2.69/0.98      | r1_tarski(sK2(X1,sK1(X0,X3)),sK2(X2,sK2(X1,sK1(X0,X3)))) ),
% 2.69/0.98      inference(resolution,[status(thm)],[c_596,c_5]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_965,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,X1)
% 2.69/0.98      | ~ r1_setfam_1(X1,X2)
% 2.69/0.98      | r1_setfam_1(X0,X3)
% 2.69/0.98      | r2_hidden(X4,sK2(X2,sK2(X1,sK1(X0,X3))))
% 2.69/0.98      | ~ r2_hidden(X4,sK2(X1,sK1(X0,X3))) ),
% 2.69/0.98      inference(resolution,[status(thm)],[c_2,c_606]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_0,plain,
% 2.69/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f22]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1799,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,X1)
% 2.69/0.98      | ~ r1_setfam_1(X1,X2)
% 2.69/0.98      | r1_setfam_1(X0,X3)
% 2.69/0.98      | ~ r2_hidden(sK0(X4,sK2(X2,sK2(X1,sK1(X0,X3)))),sK2(X1,sK1(X0,X3)))
% 2.69/0.98      | r1_tarski(X4,sK2(X2,sK2(X1,sK1(X0,X3)))) ),
% 2.69/0.98      inference(resolution,[status(thm)],[c_965,c_0]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_510,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,X1)
% 2.69/0.98      | r1_setfam_1(X0,X2)
% 2.69/0.98      | r1_tarski(sK1(X0,X2),sK2(X1,sK1(X0,X2))) ),
% 2.69/0.98      inference(resolution,[status(thm)],[c_5,c_4]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_963,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,X1)
% 2.69/0.98      | r1_setfam_1(X0,X2)
% 2.69/0.98      | r2_hidden(X3,sK2(X1,sK1(X0,X2)))
% 2.69/0.98      | ~ r2_hidden(X3,sK1(X0,X2)) ),
% 2.69/0.98      inference(resolution,[status(thm)],[c_2,c_510]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_4468,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,X1)
% 2.69/0.98      | ~ r1_setfam_1(X1,X2)
% 2.69/0.98      | r1_setfam_1(X0,X3)
% 2.69/0.98      | ~ r2_hidden(sK0(X4,sK2(X2,sK2(X1,sK1(X0,X3)))),sK1(X0,X3))
% 2.69/0.98      | r1_tarski(X4,sK2(X2,sK2(X1,sK1(X0,X3)))) ),
% 2.69/0.98      inference(resolution,[status(thm)],[c_1799,c_963]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_1,plain,
% 2.69/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.69/0.98      inference(cnf_transformation,[],[f21]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5934,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,X1)
% 2.69/0.98      | ~ r1_setfam_1(X1,X2)
% 2.69/0.98      | r1_setfam_1(X0,X3)
% 2.69/0.98      | r1_tarski(sK1(X0,X3),sK2(X2,sK2(X1,sK1(X0,X3)))) ),
% 2.69/0.98      inference(resolution,[status(thm)],[c_4468,c_1]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_3,plain,
% 2.69/0.98      ( r1_setfam_1(X0,X1)
% 2.69/0.98      | ~ r2_hidden(X2,X1)
% 2.69/0.98      | ~ r1_tarski(sK1(X0,X1),X2) ),
% 2.69/0.98      inference(cnf_transformation,[],[f26]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_5948,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,X1)
% 2.69/0.98      | ~ r1_setfam_1(X1,X2)
% 2.69/0.98      | r1_setfam_1(X0,X3)
% 2.69/0.98      | ~ r2_hidden(sK2(X2,sK2(X1,sK1(X0,X3))),X3) ),
% 2.69/0.98      inference(resolution,[status(thm)],[c_5934,c_3]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_607,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,X1)
% 2.69/0.98      | ~ r1_setfam_1(X1,X2)
% 2.69/0.98      | r1_setfam_1(X0,X3)
% 2.69/0.98      | r2_hidden(sK2(X2,sK2(X1,sK1(X0,X3))),X2) ),
% 2.69/0.98      inference(resolution,[status(thm)],[c_596,c_6]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_6294,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,X1)
% 2.69/0.98      | ~ r1_setfam_1(X1,X2)
% 2.69/0.98      | r1_setfam_1(X0,X2) ),
% 2.69/0.98      inference(resolution,[status(thm)],[c_5948,c_607]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_8,negated_conjecture,
% 2.69/0.98      ( r1_setfam_1(sK4,sK5) ),
% 2.69/0.98      inference(cnf_transformation,[],[f28]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_6344,plain,
% 2.69/0.98      ( ~ r1_setfam_1(X0,sK4) | r1_setfam_1(X0,sK5) ),
% 2.69/0.98      inference(resolution,[status(thm)],[c_6294,c_8]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_6346,plain,
% 2.69/0.98      ( ~ r1_setfam_1(sK3,sK4) | r1_setfam_1(sK3,sK5) ),
% 2.69/0.98      inference(instantiation,[status(thm)],[c_6344]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_7,negated_conjecture,
% 2.69/0.98      ( ~ r1_setfam_1(sK3,sK5) ),
% 2.69/0.98      inference(cnf_transformation,[],[f29]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(c_9,negated_conjecture,
% 2.69/0.98      ( r1_setfam_1(sK3,sK4) ),
% 2.69/0.98      inference(cnf_transformation,[],[f27]) ).
% 2.69/0.98  
% 2.69/0.98  cnf(contradiction,plain,
% 2.69/0.98      ( $false ),
% 2.69/0.98      inference(minisat,[status(thm)],[c_6346,c_7,c_9]) ).
% 2.69/0.98  
% 2.69/0.98  
% 2.69/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/0.98  
% 2.69/0.98  ------                               Statistics
% 2.69/0.98  
% 2.69/0.98  ------ Selected
% 2.69/0.98  
% 2.69/0.98  total_time:                             0.191
% 2.69/0.98  
%------------------------------------------------------------------------------
