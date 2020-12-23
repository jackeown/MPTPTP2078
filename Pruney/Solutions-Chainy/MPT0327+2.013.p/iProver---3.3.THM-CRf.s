%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:00 EST 2020

% Result     : Theorem 15.30s
% Output     : CNFRefutation 15.30s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 133 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 176 expanded)
%              Number of equality atoms :   52 ( 124 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f63,f58])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f92,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) ),
    inference(definition_unfolding,[],[f60,f77,f77,f58])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f84,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f77,f77])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f41])).

fof(f76,plain,(
    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3 ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f81])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f82])).

fof(f97,plain,(
    k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) != sK3 ),
    inference(definition_unfolding,[],[f76,f77,f58,f83,f83])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f77])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f74,f82])).

fof(f75,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_23,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) != sK3 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1023,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(superposition,[status(thm)],[c_0,c_23])).

cnf(c_55058,plain,
    ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
    inference(superposition,[status(thm)],[c_16,c_1023])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_819,plain,
    ( ~ r1_tarski(X0,sK3)
    | k5_xboole_0(X0,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))) = sK3 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1142,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0),sK3)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)))) = sK3 ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_1144,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)
    | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = sK3 ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_729,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(sK2,sK3)
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0),sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_731,plain,
    ( ~ r2_hidden(sK2,sK3)
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_55058,c_1144,c_731,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:04:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.30/2.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.30/2.47  
% 15.30/2.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.30/2.47  
% 15.30/2.47  ------  iProver source info
% 15.30/2.47  
% 15.30/2.47  git: date: 2020-06-30 10:37:57 +0100
% 15.30/2.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.30/2.47  git: non_committed_changes: false
% 15.30/2.47  git: last_make_outside_of_git: false
% 15.30/2.47  
% 15.30/2.47  ------ 
% 15.30/2.47  ------ Parsing...
% 15.30/2.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.30/2.47  
% 15.30/2.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.30/2.47  
% 15.30/2.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.30/2.47  
% 15.30/2.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.30/2.47  ------ Proving...
% 15.30/2.47  ------ Problem Properties 
% 15.30/2.47  
% 15.30/2.47  
% 15.30/2.47  clauses                                 24
% 15.30/2.47  conjectures                             2
% 15.30/2.47  EPR                                     4
% 15.30/2.47  Horn                                    19
% 15.30/2.47  unary                                   10
% 15.30/2.47  binary                                  7
% 15.30/2.47  lits                                    46
% 15.30/2.47  lits eq                                 13
% 15.30/2.47  fd_pure                                 0
% 15.30/2.47  fd_pseudo                               0
% 15.30/2.47  fd_cond                                 0
% 15.30/2.47  fd_pseudo_cond                          4
% 15.30/2.47  AC symbols                              0
% 15.30/2.47  
% 15.30/2.47  ------ Input Options Time Limit: Unbounded
% 15.30/2.47  
% 15.30/2.47  
% 15.30/2.47  ------ 
% 15.30/2.47  Current options:
% 15.30/2.47  ------ 
% 15.30/2.47  
% 15.30/2.47  
% 15.30/2.47  
% 15.30/2.47  
% 15.30/2.47  ------ Proving...
% 15.30/2.47  
% 15.30/2.47  
% 15.30/2.47  % SZS status Theorem for theBenchmark.p
% 15.30/2.47  
% 15.30/2.47  % SZS output start CNFRefutation for theBenchmark.p
% 15.30/2.47  
% 15.30/2.47  fof(f9,axiom,(
% 15.30/2.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.30/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.47  
% 15.30/2.47  fof(f60,plain,(
% 15.30/2.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.30/2.47    inference(cnf_transformation,[],[f9])).
% 15.30/2.47  
% 15.30/2.47  fof(f12,axiom,(
% 15.30/2.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.30/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.47  
% 15.30/2.47  fof(f63,plain,(
% 15.30/2.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.30/2.47    inference(cnf_transformation,[],[f12])).
% 15.30/2.47  
% 15.30/2.47  fof(f77,plain,(
% 15.30/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 15.30/2.48    inference(definition_unfolding,[],[f63,f58])).
% 15.30/2.48  
% 15.30/2.48  fof(f7,axiom,(
% 15.30/2.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.30/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.48  
% 15.30/2.48  fof(f58,plain,(
% 15.30/2.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.30/2.48    inference(cnf_transformation,[],[f7])).
% 15.30/2.48  
% 15.30/2.48  fof(f92,plain,(
% 15.30/2.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) )),
% 15.30/2.48    inference(definition_unfolding,[],[f60,f77,f77,f58])).
% 15.30/2.48  
% 15.30/2.48  fof(f1,axiom,(
% 15.30/2.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.30/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.48  
% 15.30/2.48  fof(f43,plain,(
% 15.30/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.30/2.48    inference(cnf_transformation,[],[f1])).
% 15.30/2.48  
% 15.30/2.48  fof(f84,plain,(
% 15.30/2.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 15.30/2.48    inference(definition_unfolding,[],[f43,f77,f77])).
% 15.30/2.48  
% 15.30/2.48  fof(f22,conjecture,(
% 15.30/2.48    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 15.30/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.48  
% 15.30/2.48  fof(f23,negated_conjecture,(
% 15.30/2.48    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 15.30/2.48    inference(negated_conjecture,[],[f22])).
% 15.30/2.48  
% 15.30/2.48  fof(f27,plain,(
% 15.30/2.48    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 15.30/2.48    inference(ennf_transformation,[],[f23])).
% 15.30/2.48  
% 15.30/2.48  fof(f41,plain,(
% 15.30/2.48    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3 & r2_hidden(sK2,sK3))),
% 15.30/2.48    introduced(choice_axiom,[])).
% 15.30/2.48  
% 15.30/2.48  fof(f42,plain,(
% 15.30/2.48    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3 & r2_hidden(sK2,sK3)),
% 15.30/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f27,f41])).
% 15.30/2.48  
% 15.30/2.48  fof(f76,plain,(
% 15.30/2.48    k2_xboole_0(k4_xboole_0(sK3,k1_tarski(sK2)),k1_tarski(sK2)) != sK3),
% 15.30/2.48    inference(cnf_transformation,[],[f42])).
% 15.30/2.48  
% 15.30/2.48  fof(f13,axiom,(
% 15.30/2.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.30/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.48  
% 15.30/2.48  fof(f64,plain,(
% 15.30/2.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.30/2.48    inference(cnf_transformation,[],[f13])).
% 15.30/2.48  
% 15.30/2.48  fof(f14,axiom,(
% 15.30/2.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.30/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.48  
% 15.30/2.48  fof(f65,plain,(
% 15.30/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.30/2.48    inference(cnf_transformation,[],[f14])).
% 15.30/2.48  
% 15.30/2.48  fof(f15,axiom,(
% 15.30/2.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.30/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.48  
% 15.30/2.48  fof(f66,plain,(
% 15.30/2.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.30/2.48    inference(cnf_transformation,[],[f15])).
% 15.30/2.48  
% 15.30/2.48  fof(f16,axiom,(
% 15.30/2.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.30/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.48  
% 15.30/2.48  fof(f67,plain,(
% 15.30/2.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.30/2.48    inference(cnf_transformation,[],[f16])).
% 15.30/2.48  
% 15.30/2.48  fof(f17,axiom,(
% 15.30/2.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.30/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.48  
% 15.30/2.48  fof(f68,plain,(
% 15.30/2.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.30/2.48    inference(cnf_transformation,[],[f17])).
% 15.30/2.48  
% 15.30/2.48  fof(f18,axiom,(
% 15.30/2.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 15.30/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.48  
% 15.30/2.48  fof(f69,plain,(
% 15.30/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 15.30/2.48    inference(cnf_transformation,[],[f18])).
% 15.30/2.48  
% 15.30/2.48  fof(f19,axiom,(
% 15.30/2.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 15.30/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.48  
% 15.30/2.48  fof(f70,plain,(
% 15.30/2.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 15.30/2.48    inference(cnf_transformation,[],[f19])).
% 15.30/2.48  
% 15.30/2.48  fof(f78,plain,(
% 15.30/2.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 15.30/2.48    inference(definition_unfolding,[],[f69,f70])).
% 15.30/2.48  
% 15.30/2.48  fof(f79,plain,(
% 15.30/2.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 15.30/2.48    inference(definition_unfolding,[],[f68,f78])).
% 15.30/2.48  
% 15.30/2.48  fof(f80,plain,(
% 15.30/2.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 15.30/2.48    inference(definition_unfolding,[],[f67,f79])).
% 15.30/2.48  
% 15.30/2.48  fof(f81,plain,(
% 15.30/2.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 15.30/2.48    inference(definition_unfolding,[],[f66,f80])).
% 15.30/2.48  
% 15.30/2.48  fof(f82,plain,(
% 15.30/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 15.30/2.48    inference(definition_unfolding,[],[f65,f81])).
% 15.30/2.48  
% 15.30/2.48  fof(f83,plain,(
% 15.30/2.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 15.30/2.48    inference(definition_unfolding,[],[f64,f82])).
% 15.30/2.48  
% 15.30/2.48  fof(f97,plain,(
% 15.30/2.48    k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) != sK3),
% 15.30/2.48    inference(definition_unfolding,[],[f76,f77,f58,f83,f83])).
% 15.30/2.48  
% 15.30/2.48  fof(f8,axiom,(
% 15.30/2.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.30/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.48  
% 15.30/2.48  fof(f26,plain,(
% 15.30/2.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.30/2.48    inference(ennf_transformation,[],[f8])).
% 15.30/2.48  
% 15.30/2.48  fof(f59,plain,(
% 15.30/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.30/2.48    inference(cnf_transformation,[],[f26])).
% 15.30/2.48  
% 15.30/2.48  fof(f91,plain,(
% 15.30/2.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 15.30/2.48    inference(definition_unfolding,[],[f59,f77])).
% 15.30/2.48  
% 15.30/2.48  fof(f21,axiom,(
% 15.30/2.48    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 15.30/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.30/2.48  
% 15.30/2.48  fof(f39,plain,(
% 15.30/2.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 15.30/2.48    inference(nnf_transformation,[],[f21])).
% 15.30/2.48  
% 15.30/2.48  fof(f40,plain,(
% 15.30/2.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 15.30/2.48    inference(flattening,[],[f39])).
% 15.30/2.48  
% 15.30/2.48  fof(f74,plain,(
% 15.30/2.48    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 15.30/2.48    inference(cnf_transformation,[],[f40])).
% 15.30/2.48  
% 15.30/2.48  fof(f94,plain,(
% 15.30/2.48    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 15.30/2.48    inference(definition_unfolding,[],[f74,f82])).
% 15.30/2.48  
% 15.30/2.48  fof(f75,plain,(
% 15.30/2.48    r2_hidden(sK2,sK3)),
% 15.30/2.48    inference(cnf_transformation,[],[f42])).
% 15.30/2.48  
% 15.30/2.48  cnf(c_16,plain,
% 15.30/2.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 15.30/2.48      inference(cnf_transformation,[],[f92]) ).
% 15.30/2.48  
% 15.30/2.48  cnf(c_0,plain,
% 15.30/2.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 15.30/2.48      inference(cnf_transformation,[],[f84]) ).
% 15.30/2.48  
% 15.30/2.48  cnf(c_23,negated_conjecture,
% 15.30/2.48      ( k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) != sK3 ),
% 15.30/2.48      inference(cnf_transformation,[],[f97]) ).
% 15.30/2.48  
% 15.30/2.48  cnf(c_1023,plain,
% 15.30/2.48      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k3_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
% 15.30/2.48      inference(superposition,[status(thm)],[c_0,c_23]) ).
% 15.30/2.48  
% 15.30/2.48  cnf(c_55058,plain,
% 15.30/2.48      ( k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) != sK3 ),
% 15.30/2.48      inference(superposition,[status(thm)],[c_16,c_1023]) ).
% 15.30/2.48  
% 15.30/2.48  cnf(c_15,plain,
% 15.30/2.48      ( ~ r1_tarski(X0,X1)
% 15.30/2.48      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
% 15.30/2.48      inference(cnf_transformation,[],[f91]) ).
% 15.30/2.48  
% 15.30/2.48  cnf(c_819,plain,
% 15.30/2.48      ( ~ r1_tarski(X0,sK3)
% 15.30/2.48      | k5_xboole_0(X0,k5_xboole_0(sK3,k3_xboole_0(sK3,X0))) = sK3 ),
% 15.30/2.48      inference(instantiation,[status(thm)],[c_15]) ).
% 15.30/2.48  
% 15.30/2.48  cnf(c_1142,plain,
% 15.30/2.48      ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0),sK3)
% 15.30/2.48      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)))) = sK3 ),
% 15.30/2.48      inference(instantiation,[status(thm)],[c_819]) ).
% 15.30/2.48  
% 15.30/2.48  cnf(c_1144,plain,
% 15.30/2.48      ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)
% 15.30/2.48      | k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(sK3,k3_xboole_0(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) = sK3 ),
% 15.30/2.48      inference(instantiation,[status(thm)],[c_1142]) ).
% 15.30/2.48  
% 15.30/2.48  cnf(c_20,plain,
% 15.30/2.48      ( ~ r2_hidden(X0,X1)
% 15.30/2.48      | ~ r2_hidden(X2,X1)
% 15.30/2.48      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 15.30/2.48      inference(cnf_transformation,[],[f94]) ).
% 15.30/2.48  
% 15.30/2.48  cnf(c_729,plain,
% 15.30/2.48      ( ~ r2_hidden(X0,sK3)
% 15.30/2.48      | ~ r2_hidden(sK2,sK3)
% 15.30/2.48      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0),sK3) ),
% 15.30/2.48      inference(instantiation,[status(thm)],[c_20]) ).
% 15.30/2.48  
% 15.30/2.48  cnf(c_731,plain,
% 15.30/2.48      ( ~ r2_hidden(sK2,sK3)
% 15.30/2.48      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
% 15.30/2.48      inference(instantiation,[status(thm)],[c_729]) ).
% 15.30/2.48  
% 15.30/2.48  cnf(c_24,negated_conjecture,
% 15.30/2.48      ( r2_hidden(sK2,sK3) ),
% 15.30/2.48      inference(cnf_transformation,[],[f75]) ).
% 15.30/2.48  
% 15.30/2.48  cnf(contradiction,plain,
% 15.30/2.48      ( $false ),
% 15.30/2.48      inference(minisat,[status(thm)],[c_55058,c_1144,c_731,c_24]) ).
% 15.30/2.48  
% 15.30/2.48  
% 15.30/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.30/2.48  
% 15.30/2.48  ------                               Statistics
% 15.30/2.48  
% 15.30/2.48  ------ Selected
% 15.30/2.48  
% 15.30/2.48  total_time:                             1.5
% 15.30/2.48  
%------------------------------------------------------------------------------
