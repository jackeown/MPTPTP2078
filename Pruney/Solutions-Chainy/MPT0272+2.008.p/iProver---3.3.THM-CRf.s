%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:12 EST 2020

% Result     : Theorem 15.42s
% Output     : CNFRefutation 15.42s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 156 expanded)
%              Number of clauses        :   19 (  21 expanded)
%              Number of leaves         :   15 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :   93 ( 193 expanded)
%              Number of equality atoms :   81 ( 181 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f58])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f60])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f61])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f52,f62,f62])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f30])).

fof(f55,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f70,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f55,f36,f62])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f56,f36,f62,f62])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_248,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1062,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_248])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_243,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1328,plain,
    ( k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1062,c_243])).

cnf(c_16,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_453,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_16])).

cnf(c_56506,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
    | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1328,c_453])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_56604,plain,
    ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_56506,c_10])).

cnf(c_56605,plain,
    ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_56604])).

cnf(c_15,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_452,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_0,c_15])).

cnf(c_58406,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_56605,c_452])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_58412,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_58406,c_8])).

cnf(c_58413,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_58412])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:39:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.42/2.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.42/2.50  
% 15.42/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.42/2.50  
% 15.42/2.50  ------  iProver source info
% 15.42/2.50  
% 15.42/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.42/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.42/2.50  git: non_committed_changes: false
% 15.42/2.50  git: last_make_outside_of_git: false
% 15.42/2.50  
% 15.42/2.50  ------ 
% 15.42/2.50  ------ Parsing...
% 15.42/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.42/2.50  
% 15.42/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.42/2.50  
% 15.42/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.42/2.50  
% 15.42/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.42/2.50  ------ Proving...
% 15.42/2.50  ------ Problem Properties 
% 15.42/2.50  
% 15.42/2.50  
% 15.42/2.50  clauses                                 17
% 15.42/2.50  conjectures                             2
% 15.42/2.50  EPR                                     0
% 15.42/2.50  Horn                                    16
% 15.42/2.50  unary                                   14
% 15.42/2.50  binary                                  2
% 15.42/2.50  lits                                    21
% 15.42/2.50  lits eq                                 13
% 15.42/2.50  fd_pure                                 0
% 15.42/2.50  fd_pseudo                               0
% 15.42/2.50  fd_cond                                 0
% 15.42/2.50  fd_pseudo_cond                          1
% 15.42/2.50  AC symbols                              1
% 15.42/2.50  
% 15.42/2.50  ------ Input Options Time Limit: Unbounded
% 15.42/2.50  
% 15.42/2.50  
% 15.42/2.50  ------ 
% 15.42/2.50  Current options:
% 15.42/2.50  ------ 
% 15.42/2.50  
% 15.42/2.50  
% 15.42/2.50  
% 15.42/2.50  
% 15.42/2.50  ------ Proving...
% 15.42/2.50  
% 15.42/2.50  
% 15.42/2.50  % SZS status Theorem for theBenchmark.p
% 15.42/2.50  
% 15.42/2.50   Resolution empty clause
% 15.42/2.50  
% 15.42/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.42/2.50  
% 15.42/2.50  fof(f1,axiom,(
% 15.42/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f32,plain,(
% 15.42/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.42/2.50    inference(cnf_transformation,[],[f1])).
% 15.42/2.50  
% 15.42/2.50  fof(f6,axiom,(
% 15.42/2.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f37,plain,(
% 15.42/2.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 15.42/2.50    inference(cnf_transformation,[],[f6])).
% 15.42/2.50  
% 15.42/2.50  fof(f21,axiom,(
% 15.42/2.50    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f28,plain,(
% 15.42/2.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 15.42/2.50    inference(nnf_transformation,[],[f21])).
% 15.42/2.50  
% 15.42/2.50  fof(f29,plain,(
% 15.42/2.50    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 15.42/2.50    inference(flattening,[],[f28])).
% 15.42/2.50  
% 15.42/2.50  fof(f52,plain,(
% 15.42/2.50    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 15.42/2.50    inference(cnf_transformation,[],[f29])).
% 15.42/2.50  
% 15.42/2.50  fof(f14,axiom,(
% 15.42/2.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f45,plain,(
% 15.42/2.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.42/2.50    inference(cnf_transformation,[],[f14])).
% 15.42/2.50  
% 15.42/2.50  fof(f15,axiom,(
% 15.42/2.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f46,plain,(
% 15.42/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.42/2.50    inference(cnf_transformation,[],[f15])).
% 15.42/2.50  
% 15.42/2.50  fof(f16,axiom,(
% 15.42/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f47,plain,(
% 15.42/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.42/2.50    inference(cnf_transformation,[],[f16])).
% 15.42/2.50  
% 15.42/2.50  fof(f17,axiom,(
% 15.42/2.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f48,plain,(
% 15.42/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.42/2.50    inference(cnf_transformation,[],[f17])).
% 15.42/2.50  
% 15.42/2.50  fof(f18,axiom,(
% 15.42/2.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f49,plain,(
% 15.42/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.42/2.50    inference(cnf_transformation,[],[f18])).
% 15.42/2.50  
% 15.42/2.50  fof(f19,axiom,(
% 15.42/2.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f50,plain,(
% 15.42/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 15.42/2.50    inference(cnf_transformation,[],[f19])).
% 15.42/2.50  
% 15.42/2.50  fof(f20,axiom,(
% 15.42/2.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f51,plain,(
% 15.42/2.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 15.42/2.50    inference(cnf_transformation,[],[f20])).
% 15.42/2.50  
% 15.42/2.50  fof(f57,plain,(
% 15.42/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 15.42/2.50    inference(definition_unfolding,[],[f50,f51])).
% 15.42/2.50  
% 15.42/2.50  fof(f58,plain,(
% 15.42/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 15.42/2.50    inference(definition_unfolding,[],[f49,f57])).
% 15.42/2.50  
% 15.42/2.50  fof(f59,plain,(
% 15.42/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 15.42/2.50    inference(definition_unfolding,[],[f48,f58])).
% 15.42/2.50  
% 15.42/2.50  fof(f60,plain,(
% 15.42/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 15.42/2.50    inference(definition_unfolding,[],[f47,f59])).
% 15.42/2.50  
% 15.42/2.50  fof(f61,plain,(
% 15.42/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 15.42/2.50    inference(definition_unfolding,[],[f46,f60])).
% 15.42/2.50  
% 15.42/2.50  fof(f62,plain,(
% 15.42/2.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 15.42/2.50    inference(definition_unfolding,[],[f45,f61])).
% 15.42/2.50  
% 15.42/2.50  fof(f68,plain,(
% 15.42/2.50    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 15.42/2.50    inference(definition_unfolding,[],[f52,f62,f62])).
% 15.42/2.50  
% 15.42/2.50  fof(f22,conjecture,(
% 15.42/2.50    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f23,negated_conjecture,(
% 15.42/2.50    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 15.42/2.50    inference(negated_conjecture,[],[f22])).
% 15.42/2.50  
% 15.42/2.50  fof(f27,plain,(
% 15.42/2.50    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 15.42/2.50    inference(ennf_transformation,[],[f23])).
% 15.42/2.50  
% 15.42/2.50  fof(f30,plain,(
% 15.42/2.50    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 15.42/2.50    introduced(choice_axiom,[])).
% 15.42/2.50  
% 15.42/2.50  fof(f31,plain,(
% 15.42/2.50    k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 15.42/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f30])).
% 15.42/2.50  
% 15.42/2.50  fof(f55,plain,(
% 15.42/2.50    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 15.42/2.50    inference(cnf_transformation,[],[f31])).
% 15.42/2.50  
% 15.42/2.50  fof(f5,axiom,(
% 15.42/2.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f36,plain,(
% 15.42/2.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 15.42/2.50    inference(cnf_transformation,[],[f5])).
% 15.42/2.50  
% 15.42/2.50  fof(f70,plain,(
% 15.42/2.50    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0),
% 15.42/2.50    inference(definition_unfolding,[],[f55,f36,f62])).
% 15.42/2.50  
% 15.42/2.50  fof(f12,axiom,(
% 15.42/2.50    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f43,plain,(
% 15.42/2.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 15.42/2.50    inference(cnf_transformation,[],[f12])).
% 15.42/2.50  
% 15.42/2.50  fof(f56,plain,(
% 15.42/2.50    k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)),
% 15.42/2.50    inference(cnf_transformation,[],[f31])).
% 15.42/2.50  
% 15.42/2.50  fof(f69,plain,(
% 15.42/2.50    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 15.42/2.50    inference(definition_unfolding,[],[f56,f36,f62,f62])).
% 15.42/2.50  
% 15.42/2.50  fof(f10,axiom,(
% 15.42/2.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 15.42/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.42/2.50  
% 15.42/2.50  fof(f41,plain,(
% 15.42/2.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.42/2.50    inference(cnf_transformation,[],[f10])).
% 15.42/2.50  
% 15.42/2.50  cnf(c_0,plain,
% 15.42/2.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.42/2.50      inference(cnf_transformation,[],[f32]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_4,plain,
% 15.42/2.50      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 15.42/2.50      inference(cnf_transformation,[],[f37]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_248,plain,
% 15.42/2.50      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 15.42/2.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_1062,plain,
% 15.42/2.50      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 15.42/2.50      inference(superposition,[status(thm)],[c_0,c_248]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_14,plain,
% 15.42/2.50      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 15.42/2.50      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 15.42/2.50      | k1_xboole_0 = X0 ),
% 15.42/2.50      inference(cnf_transformation,[],[f68]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_243,plain,
% 15.42/2.50      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 15.42/2.50      | k1_xboole_0 = X1
% 15.42/2.50      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 15.42/2.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_1328,plain,
% 15.42/2.50      ( k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 15.42/2.50      | k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k1_xboole_0 ),
% 15.42/2.50      inference(superposition,[status(thm)],[c_1062,c_243]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_16,negated_conjecture,
% 15.42/2.50      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_xboole_0 ),
% 15.42/2.50      inference(cnf_transformation,[],[f70]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_453,plain,
% 15.42/2.50      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k1_xboole_0 ),
% 15.42/2.50      inference(demodulation,[status(thm)],[c_0,c_16]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_56506,plain,
% 15.42/2.50      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
% 15.42/2.50      | k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 15.42/2.50      inference(superposition,[status(thm)],[c_1328,c_453]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_10,plain,
% 15.42/2.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.42/2.50      inference(cnf_transformation,[],[f43]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_56604,plain,
% 15.42/2.50      ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
% 15.42/2.50      | k1_xboole_0 != k1_xboole_0 ),
% 15.42/2.50      inference(demodulation,[status(thm)],[c_56506,c_10]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_56605,plain,
% 15.42/2.50      ( k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 15.42/2.50      inference(equality_resolution_simp,[status(thm)],[c_56604]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_15,negated_conjecture,
% 15.42/2.50      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 15.42/2.50      inference(cnf_transformation,[],[f69]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_452,plain,
% 15.42/2.50      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 15.42/2.50      inference(demodulation,[status(thm)],[c_0,c_15]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_58406,plain,
% 15.42/2.50      ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 15.42/2.50      inference(demodulation,[status(thm)],[c_56605,c_452]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_8,plain,
% 15.42/2.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.42/2.50      inference(cnf_transformation,[],[f41]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_58412,plain,
% 15.42/2.50      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 15.42/2.50      inference(demodulation,[status(thm)],[c_58406,c_8]) ).
% 15.42/2.50  
% 15.42/2.50  cnf(c_58413,plain,
% 15.42/2.50      ( $false ),
% 15.42/2.50      inference(equality_resolution_simp,[status(thm)],[c_58412]) ).
% 15.42/2.50  
% 15.42/2.50  
% 15.42/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.42/2.50  
% 15.42/2.50  ------                               Statistics
% 15.42/2.50  
% 15.42/2.50  ------ Selected
% 15.42/2.50  
% 15.42/2.50  total_time:                             1.763
% 15.42/2.50  
%------------------------------------------------------------------------------
