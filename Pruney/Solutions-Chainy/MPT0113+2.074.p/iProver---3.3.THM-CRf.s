%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:54 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   57 (  94 expanded)
%              Number of clauses        :   28 (  32 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 269 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK1,sK3)
        | ~ r1_tarski(sK1,sK2) )
      & r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( ~ r1_xboole_0(sK1,sK3)
      | ~ r1_tarski(sK1,sK2) )
    & r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f18])).

fof(f30,plain,(
    r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_9,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_539,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_545,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1024,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_539,c_545])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_537,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_544,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_857,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_537,c_544])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_541,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1305,plain,
    ( r1_xboole_0(X0,k4_xboole_0(sK2,sK3)) != iProver_top
    | r1_xboole_0(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_541])).

cnf(c_2129,plain,
    ( r1_xboole_0(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_1305])).

cnf(c_2135,plain,
    ( r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2129,c_545])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1175,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_2,c_5])).

cnf(c_1177,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,sK3))
    | ~ r2_hidden(X0,sK1) ),
    inference(resolution,[status(thm)],[c_2,c_11])).

cnf(c_1810,plain,
    ( r2_hidden(X0,sK2)
    | ~ r2_hidden(X0,sK1) ),
    inference(resolution,[status(thm)],[c_1175,c_1177])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_2000,plain,
    ( ~ r2_hidden(sK0(X0,sK2),sK1)
    | r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_1810,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_2010,plain,
    ( r1_tarski(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_2000,c_1])).

cnf(c_2011,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2010])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,plain,
    ( r1_xboole_0(sK1,sK3) != iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2135,c_2011,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.09/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/0.99  
% 3.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.09/0.99  
% 3.09/0.99  ------  iProver source info
% 3.09/0.99  
% 3.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.09/0.99  git: non_committed_changes: false
% 3.09/0.99  git: last_make_outside_of_git: false
% 3.09/0.99  
% 3.09/0.99  ------ 
% 3.09/0.99  ------ Parsing...
% 3.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.09/0.99  ------ Proving...
% 3.09/0.99  ------ Problem Properties 
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  clauses                                 12
% 3.09/0.99  conjectures                             2
% 3.09/0.99  EPR                                     3
% 3.09/0.99  Horn                                    11
% 3.09/0.99  unary                                   3
% 3.09/0.99  binary                                  7
% 3.09/0.99  lits                                    23
% 3.09/0.99  lits eq                                 1
% 3.09/0.99  fd_pure                                 0
% 3.09/0.99  fd_pseudo                               0
% 3.09/0.99  fd_cond                                 0
% 3.09/0.99  fd_pseudo_cond                          0
% 3.09/0.99  AC symbols                              0
% 3.09/0.99  
% 3.09/0.99  ------ Input Options Time Limit: Unbounded
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  ------ 
% 3.09/0.99  Current options:
% 3.09/0.99  ------ 
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  ------ Proving...
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  % SZS status Theorem for theBenchmark.p
% 3.09/0.99  
% 3.09/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.09/0.99  
% 3.09/0.99  fof(f6,axiom,(
% 3.09/0.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f29,plain,(
% 3.09/0.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f6])).
% 3.09/0.99  
% 3.09/0.99  fof(f2,axiom,(
% 3.09/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f10,plain,(
% 3.09/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.09/0.99    inference(ennf_transformation,[],[f2])).
% 3.09/0.99  
% 3.09/0.99  fof(f23,plain,(
% 3.09/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f10])).
% 3.09/0.99  
% 3.09/0.99  fof(f7,conjecture,(
% 3.09/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f8,negated_conjecture,(
% 3.09/0.99    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.09/0.99    inference(negated_conjecture,[],[f7])).
% 3.09/0.99  
% 3.09/0.99  fof(f13,plain,(
% 3.09/0.99    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.09/0.99    inference(ennf_transformation,[],[f8])).
% 3.09/0.99  
% 3.09/0.99  fof(f18,plain,(
% 3.09/0.99    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK1,sK3) | ~r1_tarski(sK1,sK2)) & r1_tarski(sK1,k4_xboole_0(sK2,sK3)))),
% 3.09/0.99    introduced(choice_axiom,[])).
% 3.09/0.99  
% 3.09/0.99  fof(f19,plain,(
% 3.09/0.99    (~r1_xboole_0(sK1,sK3) | ~r1_tarski(sK1,sK2)) & r1_tarski(sK1,k4_xboole_0(sK2,sK3))),
% 3.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f18])).
% 3.09/0.99  
% 3.09/0.99  fof(f30,plain,(
% 3.09/0.99    r1_tarski(sK1,k4_xboole_0(sK2,sK3))),
% 3.09/0.99    inference(cnf_transformation,[],[f19])).
% 3.09/0.99  
% 3.09/0.99  fof(f3,axiom,(
% 3.09/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f11,plain,(
% 3.09/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.09/0.99    inference(ennf_transformation,[],[f3])).
% 3.09/0.99  
% 3.09/0.99  fof(f24,plain,(
% 3.09/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f11])).
% 3.09/0.99  
% 3.09/0.99  fof(f5,axiom,(
% 3.09/0.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f12,plain,(
% 3.09/0.99    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.09/0.99    inference(ennf_transformation,[],[f5])).
% 3.09/0.99  
% 3.09/0.99  fof(f27,plain,(
% 3.09/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f12])).
% 3.09/0.99  
% 3.09/0.99  fof(f1,axiom,(
% 3.09/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f9,plain,(
% 3.09/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.09/0.99    inference(ennf_transformation,[],[f1])).
% 3.09/0.99  
% 3.09/0.99  fof(f14,plain,(
% 3.09/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.09/0.99    inference(nnf_transformation,[],[f9])).
% 3.09/0.99  
% 3.09/0.99  fof(f15,plain,(
% 3.09/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.09/0.99    inference(rectify,[],[f14])).
% 3.09/0.99  
% 3.09/0.99  fof(f16,plain,(
% 3.09/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.09/0.99    introduced(choice_axiom,[])).
% 3.09/0.99  
% 3.09/0.99  fof(f17,plain,(
% 3.09/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.09/0.99  
% 3.09/0.99  fof(f20,plain,(
% 3.09/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f17])).
% 3.09/0.99  
% 3.09/0.99  fof(f4,axiom,(
% 3.09/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f25,plain,(
% 3.09/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f4])).
% 3.09/0.99  
% 3.09/0.99  fof(f22,plain,(
% 3.09/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f17])).
% 3.09/0.99  
% 3.09/0.99  fof(f21,plain,(
% 3.09/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f17])).
% 3.09/0.99  
% 3.09/0.99  fof(f31,plain,(
% 3.09/0.99    ~r1_xboole_0(sK1,sK3) | ~r1_tarski(sK1,sK2)),
% 3.09/0.99    inference(cnf_transformation,[],[f19])).
% 3.09/0.99  
% 3.09/0.99  cnf(c_9,plain,
% 3.09/0.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 3.09/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_539,plain,
% 3.09/0.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_3,plain,
% 3.09/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.09/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_545,plain,
% 3.09/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.09/0.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1024,plain,
% 3.09/0.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_539,c_545]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_11,negated_conjecture,
% 3.09/0.99      ( r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
% 3.09/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_537,plain,
% 3.09/0.99      ( r1_tarski(sK1,k4_xboole_0(sK2,sK3)) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4,plain,
% 3.09/0.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.09/0.99      inference(cnf_transformation,[],[f24]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_544,plain,
% 3.09/0.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_857,plain,
% 3.09/0.99      ( k2_xboole_0(sK1,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,sK3) ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_537,c_544]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_7,plain,
% 3.09/0.99      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.09/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_541,plain,
% 3.09/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.09/0.99      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1305,plain,
% 3.09/0.99      ( r1_xboole_0(X0,k4_xboole_0(sK2,sK3)) != iProver_top
% 3.09/0.99      | r1_xboole_0(X0,sK1) = iProver_top ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_857,c_541]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2129,plain,
% 3.09/0.99      ( r1_xboole_0(sK3,sK1) = iProver_top ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_1024,c_1305]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2135,plain,
% 3.09/0.99      ( r1_xboole_0(sK1,sK3) = iProver_top ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_2129,c_545]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2,plain,
% 3.09/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.09/0.99      inference(cnf_transformation,[],[f20]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5,plain,
% 3.09/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.09/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1175,plain,
% 3.09/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.09/0.99      inference(resolution,[status(thm)],[c_2,c_5]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1177,plain,
% 3.09/0.99      ( r2_hidden(X0,k4_xboole_0(sK2,sK3)) | ~ r2_hidden(X0,sK1) ),
% 3.09/0.99      inference(resolution,[status(thm)],[c_2,c_11]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1810,plain,
% 3.09/0.99      ( r2_hidden(X0,sK2) | ~ r2_hidden(X0,sK1) ),
% 3.09/0.99      inference(resolution,[status(thm)],[c_1175,c_1177]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_0,plain,
% 3.09/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.09/0.99      inference(cnf_transformation,[],[f22]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2000,plain,
% 3.09/0.99      ( ~ r2_hidden(sK0(X0,sK2),sK1) | r1_tarski(X0,sK2) ),
% 3.09/0.99      inference(resolution,[status(thm)],[c_1810,c_0]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1,plain,
% 3.09/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.09/0.99      inference(cnf_transformation,[],[f21]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2010,plain,
% 3.09/0.99      ( r1_tarski(sK1,sK2) ),
% 3.09/0.99      inference(resolution,[status(thm)],[c_2000,c_1]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2011,plain,
% 3.09/0.99      ( r1_tarski(sK1,sK2) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_2010]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_10,negated_conjecture,
% 3.09/0.99      ( ~ r1_xboole_0(sK1,sK3) | ~ r1_tarski(sK1,sK2) ),
% 3.09/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_13,plain,
% 3.09/0.99      ( r1_xboole_0(sK1,sK3) != iProver_top
% 3.09/0.99      | r1_tarski(sK1,sK2) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(contradiction,plain,
% 3.09/0.99      ( $false ),
% 3.09/0.99      inference(minisat,[status(thm)],[c_2135,c_2011,c_13]) ).
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.09/0.99  
% 3.09/0.99  ------                               Statistics
% 3.09/0.99  
% 3.09/0.99  ------ Selected
% 3.09/0.99  
% 3.09/0.99  total_time:                             0.098
% 3.09/0.99  
%------------------------------------------------------------------------------
