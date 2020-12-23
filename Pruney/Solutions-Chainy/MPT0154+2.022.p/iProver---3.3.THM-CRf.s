%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:54 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   79 (1482 expanded)
%              Number of clauses        :   41 ( 516 expanded)
%              Number of leaves         :   13 ( 403 expanded)
%              Depth                    :   25
%              Number of atoms          :   87 (1581 expanded)
%              Number of equality atoms :   77 (1454 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f28,f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f16])).

fof(f20,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f17])).

fof(f21,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f38,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f31,f39])).

fof(f50,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f38,f39,f41])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_45,plain,
    ( X0 != X1
    | k5_xboole_0(X0,k4_xboole_0(X2,X0)) != X3
    | k4_xboole_0(X1,k4_xboole_0(X1,X3)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_6])).

cnf(c_46,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(unflattening,[status(thm)],[c_45])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_276,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_46,c_0])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_124,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_281,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_276,c_124])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_273,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_46])).

cnf(c_519,plain,
    ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_273,c_0])).

cnf(c_126,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_128,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_126,c_5])).

cnf(c_185,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_128])).

cnf(c_521,plain,
    ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_519,c_185])).

cnf(c_630,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_521])).

cnf(c_662,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_630,c_0])).

cnf(c_669,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_662,c_185])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_795,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_669,c_2])).

cnf(c_799,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_795,c_5])).

cnf(c_2659,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_281,c_799])).

cnf(c_341,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_2675,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_2659,c_341])).

cnf(c_2686,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_2675,c_5])).

cnf(c_811,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_799,c_124])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_897,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_811,c_7])).

cnf(c_896,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_811,c_7])).

cnf(c_1126,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_811,c_896])).

cnf(c_810,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_799,c_128])).

cnf(c_1151,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1126,c_810])).

cnf(c_1153,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1151,c_896])).

cnf(c_1591,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_897,c_1153])).

cnf(c_1607,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1591,c_810])).

cnf(c_1640,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_1607,c_1607])).

cnf(c_2687,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2686,c_1640])).

cnf(c_9,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k1_tarski(sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_14175,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_2687,c_9])).

cnf(c_14176,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_14175])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.85/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.02  
% 3.85/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/1.02  
% 3.85/1.02  ------  iProver source info
% 3.85/1.02  
% 3.85/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.85/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/1.02  git: non_committed_changes: false
% 3.85/1.02  git: last_make_outside_of_git: false
% 3.85/1.02  
% 3.85/1.02  ------ 
% 3.85/1.02  ------ Parsing...
% 3.85/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/1.02  
% 3.85/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.85/1.02  
% 3.85/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/1.02  
% 3.85/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.85/1.02  ------ Proving...
% 3.85/1.02  ------ Problem Properties 
% 3.85/1.02  
% 3.85/1.02  
% 3.85/1.02  clauses                                 9
% 3.85/1.02  conjectures                             1
% 3.85/1.02  EPR                                     0
% 3.85/1.02  Horn                                    9
% 3.85/1.02  unary                                   9
% 3.85/1.02  binary                                  0
% 3.85/1.02  lits                                    9
% 3.85/1.02  lits eq                                 9
% 3.85/1.02  fd_pure                                 0
% 3.85/1.02  fd_pseudo                               0
% 3.85/1.02  fd_cond                                 0
% 3.85/1.02  fd_pseudo_cond                          0
% 3.85/1.02  AC symbols                              0
% 3.85/1.02  
% 3.85/1.02  ------ Input Options Time Limit: Unbounded
% 3.85/1.02  
% 3.85/1.02  
% 3.85/1.02  ------ 
% 3.85/1.02  Current options:
% 3.85/1.02  ------ 
% 3.85/1.02  
% 3.85/1.02  
% 3.85/1.02  
% 3.85/1.02  
% 3.85/1.02  ------ Proving...
% 3.85/1.02  
% 3.85/1.02  
% 3.85/1.02  % SZS status Theorem for theBenchmark.p
% 3.85/1.02  
% 3.85/1.02   Resolution empty clause
% 3.85/1.02  
% 3.85/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/1.02  
% 3.85/1.02  fof(f4,axiom,(
% 3.85/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.02  
% 3.85/1.02  fof(f19,plain,(
% 3.85/1.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.85/1.02    inference(ennf_transformation,[],[f4])).
% 3.85/1.02  
% 3.85/1.02  fof(f26,plain,(
% 3.85/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.85/1.02    inference(cnf_transformation,[],[f19])).
% 3.85/1.02  
% 3.85/1.02  fof(f6,axiom,(
% 3.85/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.02  
% 3.85/1.02  fof(f28,plain,(
% 3.85/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.85/1.02    inference(cnf_transformation,[],[f6])).
% 3.85/1.02  
% 3.85/1.02  fof(f47,plain,(
% 3.85/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.85/1.02    inference(definition_unfolding,[],[f26,f28])).
% 3.85/1.02  
% 3.85/1.02  fof(f7,axiom,(
% 3.85/1.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.02  
% 3.85/1.02  fof(f29,plain,(
% 3.85/1.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.85/1.02    inference(cnf_transformation,[],[f7])).
% 3.85/1.02  
% 3.85/1.02  fof(f9,axiom,(
% 3.85/1.02    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.02  
% 3.85/1.02  fof(f31,plain,(
% 3.85/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.85/1.02    inference(cnf_transformation,[],[f9])).
% 3.85/1.02  
% 3.85/1.02  fof(f48,plain,(
% 3.85/1.02    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 3.85/1.02    inference(definition_unfolding,[],[f29,f31])).
% 3.85/1.02  
% 3.85/1.02  fof(f3,axiom,(
% 3.85/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.02  
% 3.85/1.02  fof(f25,plain,(
% 3.85/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.85/1.02    inference(cnf_transformation,[],[f3])).
% 3.85/1.02  
% 3.85/1.02  fof(f43,plain,(
% 3.85/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.85/1.02    inference(definition_unfolding,[],[f25,f28])).
% 3.85/1.02  
% 3.85/1.02  fof(f2,axiom,(
% 3.85/1.02    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.02  
% 3.85/1.02  fof(f18,plain,(
% 3.85/1.02    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.85/1.02    inference(rectify,[],[f2])).
% 3.85/1.02  
% 3.85/1.02  fof(f24,plain,(
% 3.85/1.02    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.85/1.02    inference(cnf_transformation,[],[f18])).
% 3.85/1.02  
% 3.85/1.02  fof(f46,plain,(
% 3.85/1.02    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 3.85/1.02    inference(definition_unfolding,[],[f24,f28])).
% 3.85/1.02  
% 3.85/1.02  fof(f5,axiom,(
% 3.85/1.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.02  
% 3.85/1.02  fof(f27,plain,(
% 3.85/1.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.85/1.02    inference(cnf_transformation,[],[f5])).
% 3.85/1.02  
% 3.85/1.02  fof(f1,axiom,(
% 3.85/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.02  
% 3.85/1.02  fof(f23,plain,(
% 3.85/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.85/1.02    inference(cnf_transformation,[],[f1])).
% 3.85/1.02  
% 3.85/1.02  fof(f45,plain,(
% 3.85/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.85/1.02    inference(definition_unfolding,[],[f23,f28,f28])).
% 3.85/1.02  
% 3.85/1.02  fof(f8,axiom,(
% 3.85/1.02    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.02  
% 3.85/1.02  fof(f30,plain,(
% 3.85/1.02    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.85/1.02    inference(cnf_transformation,[],[f8])).
% 3.85/1.02  
% 3.85/1.02  fof(f16,conjecture,(
% 3.85/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.02  
% 3.85/1.02  fof(f17,negated_conjecture,(
% 3.85/1.02    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.85/1.02    inference(negated_conjecture,[],[f16])).
% 3.85/1.02  
% 3.85/1.02  fof(f20,plain,(
% 3.85/1.02    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 3.85/1.02    inference(ennf_transformation,[],[f17])).
% 3.85/1.02  
% 3.85/1.02  fof(f21,plain,(
% 3.85/1.02    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 3.85/1.02    introduced(choice_axiom,[])).
% 3.85/1.02  
% 3.85/1.02  fof(f22,plain,(
% 3.85/1.02    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 3.85/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 3.85/1.02  
% 3.85/1.02  fof(f38,plain,(
% 3.85/1.02    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 3.85/1.02    inference(cnf_transformation,[],[f22])).
% 3.85/1.02  
% 3.85/1.02  fof(f12,axiom,(
% 3.85/1.02    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 3.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.02  
% 3.85/1.02  fof(f34,plain,(
% 3.85/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 3.85/1.02    inference(cnf_transformation,[],[f12])).
% 3.85/1.02  
% 3.85/1.02  fof(f11,axiom,(
% 3.85/1.02    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 3.85/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.02  
% 3.85/1.02  fof(f33,plain,(
% 3.85/1.02    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 3.85/1.02    inference(cnf_transformation,[],[f11])).
% 3.85/1.02  
% 3.85/1.02  fof(f39,plain,(
% 3.85/1.02    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1)) )),
% 3.85/1.02    inference(definition_unfolding,[],[f33,f31])).
% 3.85/1.02  
% 3.85/1.02  fof(f41,plain,(
% 3.85/1.02    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2)) )),
% 3.85/1.02    inference(definition_unfolding,[],[f34,f31,f39])).
% 3.85/1.02  
% 3.85/1.02  fof(f50,plain,(
% 3.85/1.02    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k1_tarski(sK0)))),
% 3.85/1.02    inference(definition_unfolding,[],[f38,f39,f41])).
% 3.85/1.02  
% 3.85/1.02  cnf(c_4,plain,
% 3.85/1.02      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.85/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_6,plain,
% 3.85/1.02      ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 3.85/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_45,plain,
% 3.85/1.02      ( X0 != X1
% 3.85/1.02      | k5_xboole_0(X0,k4_xboole_0(X2,X0)) != X3
% 3.85/1.02      | k4_xboole_0(X1,k4_xboole_0(X1,X3)) = X1 ),
% 3.85/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_6]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_46,plain,
% 3.85/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
% 3.85/1.02      inference(unflattening,[status(thm)],[c_45]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_0,plain,
% 3.85/1.02      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.85/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_276,plain,
% 3.85/1.02      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,X0) ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_46,c_0]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_3,plain,
% 3.85/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.85/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_124,plain,
% 3.85/1.02      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_281,plain,
% 3.85/1.02      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X0) ),
% 3.85/1.02      inference(light_normalisation,[status(thm)],[c_276,c_124]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_5,plain,
% 3.85/1.02      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.85/1.02      inference(cnf_transformation,[],[f27]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_273,plain,
% 3.85/1.02      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_5,c_46]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_519,plain,
% 3.85/1.02      ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_273,c_0]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_126,plain,
% 3.85/1.02      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_128,plain,
% 3.85/1.02      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.85/1.02      inference(light_normalisation,[status(thm)],[c_126,c_5]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_185,plain,
% 3.85/1.02      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_5,c_128]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_521,plain,
% 3.85/1.02      ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.85/1.02      inference(light_normalisation,[status(thm)],[c_519,c_185]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_630,plain,
% 3.85/1.02      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_0,c_521]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_662,plain,
% 3.85/1.02      ( k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_630,c_0]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_669,plain,
% 3.85/1.02      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.85/1.02      inference(light_normalisation,[status(thm)],[c_662,c_185]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_2,plain,
% 3.85/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.85/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_795,plain,
% 3.85/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_669,c_2]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_799,plain,
% 3.85/1.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.85/1.02      inference(light_normalisation,[status(thm)],[c_795,c_5]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_2659,plain,
% 3.85/1.02      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 3.85/1.02      inference(light_normalisation,[status(thm)],[c_281,c_799]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_341,plain,
% 3.85/1.02      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_2675,plain,
% 3.85/1.02      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_2659,c_341]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_2686,plain,
% 3.85/1.02      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
% 3.85/1.02      inference(light_normalisation,[status(thm)],[c_2675,c_5]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_811,plain,
% 3.85/1.02      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.85/1.02      inference(demodulation,[status(thm)],[c_799,c_124]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_7,plain,
% 3.85/1.02      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.85/1.02      inference(cnf_transformation,[],[f30]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_897,plain,
% 3.85/1.02      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_811,c_7]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_896,plain,
% 3.85/1.02      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_811,c_7]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_1126,plain,
% 3.85/1.02      ( k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_811,c_896]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_810,plain,
% 3.85/1.02      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.85/1.02      inference(demodulation,[status(thm)],[c_799,c_128]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_1151,plain,
% 3.85/1.02      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.85/1.02      inference(light_normalisation,[status(thm)],[c_1126,c_810]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_1153,plain,
% 3.85/1.02      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 3.85/1.02      inference(demodulation,[status(thm)],[c_1151,c_896]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_1591,plain,
% 3.85/1.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_897,c_1153]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_1607,plain,
% 3.85/1.02      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 3.85/1.02      inference(demodulation,[status(thm)],[c_1591,c_810]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_1640,plain,
% 3.85/1.02      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 3.85/1.02      inference(superposition,[status(thm)],[c_1607,c_1607]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_2687,plain,
% 3.85/1.02      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k4_xboole_0(X1,X0) ),
% 3.85/1.02      inference(demodulation,[status(thm)],[c_2686,c_1640]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_9,negated_conjecture,
% 3.85/1.02      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k1_tarski(sK0))) ),
% 3.85/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_14175,plain,
% 3.85/1.02      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) ),
% 3.85/1.02      inference(demodulation,[status(thm)],[c_2687,c_9]) ).
% 3.85/1.02  
% 3.85/1.02  cnf(c_14176,plain,
% 3.85/1.02      ( $false ),
% 3.85/1.02      inference(theory_normalisation,[status(thm)],[c_14175]) ).
% 3.85/1.02  
% 3.85/1.02  
% 3.85/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/1.02  
% 3.85/1.02  ------                               Statistics
% 3.85/1.02  
% 3.85/1.02  ------ Selected
% 3.85/1.02  
% 3.85/1.02  total_time:                             0.49
% 3.85/1.02  
%------------------------------------------------------------------------------
