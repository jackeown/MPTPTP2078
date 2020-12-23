%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:03 EST 2020

% Result     : CounterSatisfiable 1.77s
% Output     : Saturation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   22 (  30 expanded)
%              Number of clauses        :    6 (   7 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  62 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) )
   => ( r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( r1_xboole_0(sK0,sK1)
    & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f14,plain,(
    ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f14,f12])).

fof(f15,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_0,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_128,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X0,X2),X3)
    | ~ r1_tarski(X3,X1) ),
    inference(resolution,[status(thm)],[c_1,c_0])).

cnf(c_140,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X3)) ),
    inference(resolution,[status(thm)],[c_128,c_0])).

cnf(c_3,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_2,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:11:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.77/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.00  
% 1.77/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.77/1.00  
% 1.77/1.00  ------  iProver source info
% 1.77/1.00  
% 1.77/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.77/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.77/1.00  git: non_committed_changes: false
% 1.77/1.00  git: last_make_outside_of_git: false
% 1.77/1.00  
% 1.77/1.00  ------ 
% 1.77/1.00  ------ Parsing...
% 1.77/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.77/1.00  
% 1.77/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.77/1.00  
% 1.77/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.77/1.00  ------ Proving...
% 1.77/1.00  ------ Problem Properties 
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  clauses                                 4
% 1.77/1.00  conjectures                             2
% 1.77/1.00  EPR                                     2
% 1.77/1.00  Horn                                    4
% 1.77/1.00  unary                                   3
% 1.77/1.00  binary                                  0
% 1.77/1.00  lits                                    7
% 1.77/1.00  lits eq                                 0
% 1.77/1.00  fd_pure                                 0
% 1.77/1.00  fd_pseudo                               0
% 1.77/1.00  fd_cond                                 0
% 1.77/1.00  fd_pseudo_cond                          0
% 1.77/1.00  AC symbols                              0
% 1.77/1.00  
% 1.77/1.00  ------ Input Options Time Limit: Unbounded
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  ------ 
% 1.77/1.00  Current options:
% 1.77/1.00  ------ 
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  ------ Proving...
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 1.77/1.00  
% 1.77/1.00  % SZS output start Saturation for theBenchmark.p
% 1.77/1.00  
% 1.77/1.00  fof(f3,axiom,(
% 1.77/1.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f6,plain,(
% 1.77/1.00    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.77/1.00    inference(ennf_transformation,[],[f3])).
% 1.77/1.00  
% 1.77/1.00  fof(f7,plain,(
% 1.77/1.00    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.77/1.00    inference(flattening,[],[f6])).
% 1.77/1.00  
% 1.77/1.00  fof(f13,plain,(
% 1.77/1.00    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f7])).
% 1.77/1.00  
% 1.77/1.00  fof(f1,axiom,(
% 1.77/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f11,plain,(
% 1.77/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f1])).
% 1.77/1.00  
% 1.77/1.00  fof(f4,conjecture,(
% 1.77/1.00    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f5,negated_conjecture,(
% 1.77/1.00    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.77/1.00    inference(negated_conjecture,[],[f4])).
% 1.77/1.00  
% 1.77/1.00  fof(f8,plain,(
% 1.77/1.00    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.77/1.00    inference(ennf_transformation,[],[f5])).
% 1.77/1.00  
% 1.77/1.00  fof(f9,plain,(
% 1.77/1.00    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2))) => (r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 1.77/1.00    introduced(choice_axiom,[])).
% 1.77/1.00  
% 1.77/1.00  fof(f10,plain,(
% 1.77/1.00    r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 1.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 1.77/1.00  
% 1.77/1.00  fof(f14,plain,(
% 1.77/1.00    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 1.77/1.00    inference(cnf_transformation,[],[f10])).
% 1.77/1.00  
% 1.77/1.00  fof(f2,axiom,(
% 1.77/1.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.77/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.77/1.00  
% 1.77/1.00  fof(f12,plain,(
% 1.77/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.77/1.00    inference(cnf_transformation,[],[f2])).
% 1.77/1.00  
% 1.77/1.00  fof(f16,plain,(
% 1.77/1.00    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 1.77/1.00    inference(definition_unfolding,[],[f14,f12])).
% 1.77/1.00  
% 1.77/1.00  fof(f15,plain,(
% 1.77/1.00    r1_xboole_0(sK0,sK1)),
% 1.77/1.00    inference(cnf_transformation,[],[f10])).
% 1.77/1.00  
% 1.77/1.00  cnf(c_1,plain,
% 1.77/1.00      ( ~ r1_xboole_0(X0,X1)
% 1.77/1.00      | r1_xboole_0(X2,X3)
% 1.77/1.00      | ~ r1_tarski(X3,X1)
% 1.77/1.00      | ~ r1_tarski(X2,X0) ),
% 1.77/1.00      inference(cnf_transformation,[],[f13]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_0,plain,
% 1.77/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 1.77/1.00      inference(cnf_transformation,[],[f11]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_128,plain,
% 1.77/1.00      ( ~ r1_xboole_0(X0,X1)
% 1.77/1.00      | r1_xboole_0(k4_xboole_0(X0,X2),X3)
% 1.77/1.00      | ~ r1_tarski(X3,X1) ),
% 1.77/1.00      inference(resolution,[status(thm)],[c_1,c_0]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_140,plain,
% 1.77/1.00      ( ~ r1_xboole_0(X0,X1)
% 1.77/1.00      | r1_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X3)) ),
% 1.77/1.00      inference(resolution,[status(thm)],[c_128,c_0]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_3,negated_conjecture,
% 1.77/1.00      ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 1.77/1.00      inference(cnf_transformation,[],[f16]) ).
% 1.77/1.00  
% 1.77/1.00  cnf(c_2,negated_conjecture,
% 1.77/1.00      ( r1_xboole_0(sK0,sK1) ),
% 1.77/1.00      inference(cnf_transformation,[],[f15]) ).
% 1.77/1.00  
% 1.77/1.00  
% 1.77/1.00  % SZS output end Saturation for theBenchmark.p
% 1.77/1.00  
% 1.77/1.00  ------                               Statistics
% 1.77/1.00  
% 1.77/1.00  ------ Selected
% 1.77/1.00  
% 1.77/1.00  total_time:                             0.048
% 1.77/1.00  
%------------------------------------------------------------------------------
