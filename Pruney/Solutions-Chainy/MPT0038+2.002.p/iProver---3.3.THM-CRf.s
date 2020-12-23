%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:31 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   36 (  73 expanded)
%              Number of clauses        :   18 (  39 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 ( 115 expanded)
%              Number of equality atoms :   20 (  58 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0,X1,X2] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f7])).

fof(f11,plain,
    ( ? [X0,X1,X2] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))
   => ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f18,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_43,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_709,plain,
    ( X0 != k2_xboole_0(X1,X2)
    | k2_xboole_0(X2,X1) = X0 ),
    inference(resolution,[status(thm)],[c_43,c_0])).

cnf(c_4,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2107,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X2,X1)) ),
    inference(resolution,[status(thm)],[c_709,c_4])).

cnf(c_46,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_380,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(X3,k2_xboole_0(X2,X1))
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_46,c_0])).

cnf(c_2,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_504,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | X0 != k3_xboole_0(k2_xboole_0(X2,X1),X3) ),
    inference(resolution,[status(thm)],[c_380,c_2])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_520,plain,
    ( r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)) ),
    inference(resolution,[status(thm)],[c_504,c_1])).

cnf(c_540,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | X0 != k3_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_520,c_380])).

cnf(c_5151,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),X2),k2_xboole_0(X2,X1)) ),
    inference(resolution,[status(thm)],[c_2107,c_540])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5579,plain,
    ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
    | r1_tarski(k2_xboole_0(k3_xboole_0(X3,X1),X0),X2) ),
    inference(resolution,[status(thm)],[c_5151,c_3])).

cnf(c_5,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_10295,plain,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK2),sK1),k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_5579,c_5])).

cnf(c_10312,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10295,c_5151])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 17:41:45 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 3.29/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/0.99  
% 3.29/0.99  ------  iProver source info
% 3.29/0.99  
% 3.29/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.29/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/0.99  git: non_committed_changes: false
% 3.29/0.99  git: last_make_outside_of_git: false
% 3.29/0.99  
% 3.29/0.99  ------ 
% 3.29/0.99  ------ Parsing...
% 3.29/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.29/0.99  ------ Proving...
% 3.29/0.99  ------ Problem Properties 
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  clauses                                 6
% 3.29/0.99  conjectures                             1
% 3.29/0.99  EPR                                     1
% 3.29/0.99  Horn                                    6
% 3.29/0.99  unary                                   5
% 3.29/0.99  binary                                  0
% 3.29/0.99  lits                                    8
% 3.29/0.99  lits eq                                 3
% 3.29/0.99  fd_pure                                 0
% 3.29/0.99  fd_pseudo                               0
% 3.29/0.99  fd_cond                                 0
% 3.29/0.99  fd_pseudo_cond                          0
% 3.29/0.99  AC symbols                              0
% 3.29/0.99  
% 3.29/0.99  ------ Input Options Time Limit: Unbounded
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  ------ 
% 3.29/0.99  Current options:
% 3.29/0.99  ------ 
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  ------ Proving...
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  % SZS status Theorem for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99   Resolution empty clause
% 3.29/0.99  
% 3.29/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  fof(f1,axiom,(
% 3.29/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f13,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f1])).
% 3.29/0.99  
% 3.29/0.99  fof(f5,axiom,(
% 3.29/0.99    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f17,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 3.29/0.99    inference(cnf_transformation,[],[f5])).
% 3.29/0.99  
% 3.29/0.99  fof(f3,axiom,(
% 3.29/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f15,plain,(
% 3.29/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f3])).
% 3.29/0.99  
% 3.29/0.99  fof(f2,axiom,(
% 3.29/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f14,plain,(
% 3.29/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f2])).
% 3.29/0.99  
% 3.29/0.99  fof(f4,axiom,(
% 3.29/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f8,plain,(
% 3.29/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.29/0.99    inference(ennf_transformation,[],[f4])).
% 3.29/0.99  
% 3.29/0.99  fof(f9,plain,(
% 3.29/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.29/0.99    inference(flattening,[],[f8])).
% 3.29/0.99  
% 3.29/0.99  fof(f16,plain,(
% 3.29/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.29/0.99    inference(cnf_transformation,[],[f9])).
% 3.29/0.99  
% 3.29/0.99  fof(f6,conjecture,(
% 3.29/0.99    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 3.29/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.99  
% 3.29/0.99  fof(f7,negated_conjecture,(
% 3.29/0.99    ~! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 3.29/0.99    inference(negated_conjecture,[],[f6])).
% 3.29/0.99  
% 3.29/0.99  fof(f10,plain,(
% 3.29/0.99    ? [X0,X1,X2] : ~r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 3.29/0.99    inference(ennf_transformation,[],[f7])).
% 3.29/0.99  
% 3.29/0.99  fof(f11,plain,(
% 3.29/0.99    ? [X0,X1,X2] : ~r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) => ~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2))),
% 3.29/0.99    introduced(choice_axiom,[])).
% 3.29/0.99  
% 3.29/0.99  fof(f12,plain,(
% 3.29/0.99    ~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2))),
% 3.29/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 3.29/0.99  
% 3.29/0.99  fof(f18,plain,(
% 3.29/0.99    ~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2))),
% 3.29/0.99    inference(cnf_transformation,[],[f12])).
% 3.29/0.99  
% 3.29/0.99  cnf(c_43,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_0,plain,
% 3.29/0.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.29/0.99      inference(cnf_transformation,[],[f13]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_709,plain,
% 3.29/0.99      ( X0 != k2_xboole_0(X1,X2) | k2_xboole_0(X2,X1) = X0 ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_43,c_0]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_4,plain,
% 3.29/0.99      ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 3.29/0.99      inference(cnf_transformation,[],[f17]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2107,plain,
% 3.29/0.99      ( k2_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X2,X1)) ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_709,c_4]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_46,plain,
% 3.29/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.29/0.99      theory(equality) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_380,plain,
% 3.29/0.99      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 3.29/0.99      | r1_tarski(X3,k2_xboole_0(X2,X1))
% 3.29/0.99      | X3 != X0 ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_46,c_0]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2,plain,
% 3.29/0.99      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.29/0.99      inference(cnf_transformation,[],[f15]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_504,plain,
% 3.29/0.99      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 3.29/0.99      | X0 != k3_xboole_0(k2_xboole_0(X2,X1),X3) ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_380,c_2]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1,plain,
% 3.29/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.29/0.99      inference(cnf_transformation,[],[f14]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_520,plain,
% 3.29/0.99      ( r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)) ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_504,c_1]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_540,plain,
% 3.29/0.99      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 3.29/0.99      | X0 != k3_xboole_0(X3,k2_xboole_0(X1,X2)) ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_520,c_380]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_5151,plain,
% 3.29/0.99      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),X2),k2_xboole_0(X2,X1)) ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_2107,c_540]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3,plain,
% 3.29/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.29/0.99      inference(cnf_transformation,[],[f16]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_5579,plain,
% 3.29/0.99      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
% 3.29/0.99      | r1_tarski(k2_xboole_0(k3_xboole_0(X3,X1),X0),X2) ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_5151,c_3]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_5,negated_conjecture,
% 3.29/0.99      ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) ),
% 3.29/0.99      inference(cnf_transformation,[],[f18]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_10295,plain,
% 3.29/0.99      ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK2),sK1),k2_xboole_0(sK1,sK2)) ),
% 3.29/0.99      inference(resolution,[status(thm)],[c_5579,c_5]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_10312,plain,
% 3.29/0.99      ( $false ),
% 3.29/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_10295,c_5151]) ).
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  ------                               Statistics
% 3.29/0.99  
% 3.29/0.99  ------ Selected
% 3.29/0.99  
% 3.29/0.99  total_time:                             0.311
% 3.29/0.99  
%------------------------------------------------------------------------------
