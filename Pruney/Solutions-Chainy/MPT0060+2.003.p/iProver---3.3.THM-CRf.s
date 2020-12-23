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
% DateTime   : Thu Dec  3 11:22:59 EST 2020

% Result     : Theorem 7.55s
% Output     : CNFRefutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 466 expanded)
%              Number of clauses        :   40 ( 222 expanded)
%              Number of leaves         :   10 ( 113 expanded)
%              Depth                    :   15
%              Number of atoms          :   72 ( 551 expanded)
%              Number of equality atoms :   64 ( 452 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f22,f21,f21])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f10])).

fof(f13,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f23,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_67,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_6,c_5])).

cnf(c_452,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) ),
    inference(superposition,[status(thm)],[c_5,c_67])).

cnf(c_453,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) ),
    inference(light_normalisation,[status(thm)],[c_452,c_5])).

cnf(c_454,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3))) ),
    inference(demodulation,[status(thm)],[c_453,c_5])).

cnf(c_7,negated_conjecture,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_70,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))))) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_7,c_5])).

cnf(c_33572,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)),sK2))) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_454,c_70])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_40,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k2_xboole_0(X3,X1) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_41,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_40])).

cnf(c_4,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_294,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_41,c_4])).

cnf(c_609,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_294,c_5])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_122,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_41])).

cnf(c_295,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_122])).

cnf(c_1248,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_295])).

cnf(c_291,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_321,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_291,c_122])).

cnf(c_1523,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_321,c_291])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_323,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_291,c_3])).

cnf(c_325,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_323,c_3])).

cnf(c_1526,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_1523,c_5,c_325,c_609])).

cnf(c_4145,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1248,c_1526])).

cnf(c_297,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_299,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_297,c_3])).

cnf(c_763,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_325,c_299])).

cnf(c_188,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_122,c_3])).

cnf(c_765,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_763,c_188])).

cnf(c_4154,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_765,c_1526])).

cnf(c_4146,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_321,c_1526])).

cnf(c_4214,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_4146,c_4154])).

cnf(c_4218,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
    inference(light_normalisation,[status(thm)],[c_4145,c_4154,c_4214])).

cnf(c_4610,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
    inference(superposition,[status(thm)],[c_4218,c_41])).

cnf(c_33573,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_33572,c_609,c_4610])).

cnf(c_33574,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_33573])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.55/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.55/1.51  
% 7.55/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.55/1.51  
% 7.55/1.51  ------  iProver source info
% 7.55/1.51  
% 7.55/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.55/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.55/1.51  git: non_committed_changes: false
% 7.55/1.51  git: last_make_outside_of_git: false
% 7.55/1.51  
% 7.55/1.51  ------ 
% 7.55/1.51  ------ Parsing...
% 7.55/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.55/1.51  
% 7.55/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.55/1.51  
% 7.55/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.55/1.51  
% 7.55/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.55/1.51  ------ Proving...
% 7.55/1.51  ------ Problem Properties 
% 7.55/1.51  
% 7.55/1.51  
% 7.55/1.51  clauses                                 7
% 7.55/1.51  conjectures                             1
% 7.55/1.51  EPR                                     0
% 7.55/1.51  Horn                                    7
% 7.55/1.51  unary                                   7
% 7.55/1.51  binary                                  0
% 7.55/1.51  lits                                    7
% 7.55/1.51  lits eq                                 7
% 7.55/1.51  fd_pure                                 0
% 7.55/1.51  fd_pseudo                               0
% 7.55/1.51  fd_cond                                 0
% 7.55/1.51  fd_pseudo_cond                          0
% 7.55/1.51  AC symbols                              0
% 7.55/1.51  
% 7.55/1.51  ------ Input Options Time Limit: Unbounded
% 7.55/1.51  
% 7.55/1.51  
% 7.55/1.51  ------ 
% 7.55/1.51  Current options:
% 7.55/1.51  ------ 
% 7.55/1.51  
% 7.55/1.51  
% 7.55/1.51  
% 7.55/1.51  
% 7.55/1.51  ------ Proving...
% 7.55/1.51  
% 7.55/1.51  
% 7.55/1.51  % SZS status Theorem for theBenchmark.p
% 7.55/1.51  
% 7.55/1.51   Resolution empty clause
% 7.55/1.51  
% 7.55/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.55/1.51  
% 7.55/1.51  fof(f6,axiom,(
% 7.55/1.51    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.55/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.51  
% 7.55/1.51  fof(f20,plain,(
% 7.55/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.55/1.51    inference(cnf_transformation,[],[f6])).
% 7.55/1.51  
% 7.55/1.51  fof(f8,axiom,(
% 7.55/1.51    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 7.55/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.51  
% 7.55/1.51  fof(f22,plain,(
% 7.55/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 7.55/1.51    inference(cnf_transformation,[],[f8])).
% 7.55/1.51  
% 7.55/1.51  fof(f7,axiom,(
% 7.55/1.51    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.55/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.51  
% 7.55/1.51  fof(f21,plain,(
% 7.55/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.55/1.51    inference(cnf_transformation,[],[f7])).
% 7.55/1.51  
% 7.55/1.51  fof(f24,plain,(
% 7.55/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 7.55/1.51    inference(definition_unfolding,[],[f22,f21,f21])).
% 7.55/1.51  
% 7.55/1.51  fof(f9,conjecture,(
% 7.55/1.51    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 7.55/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.51  
% 7.55/1.51  fof(f10,negated_conjecture,(
% 7.55/1.51    ~! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 7.55/1.51    inference(negated_conjecture,[],[f9])).
% 7.55/1.51  
% 7.55/1.51  fof(f12,plain,(
% 7.55/1.51    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 7.55/1.51    inference(ennf_transformation,[],[f10])).
% 7.55/1.51  
% 7.55/1.51  fof(f13,plain,(
% 7.55/1.51    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 7.55/1.51    introduced(choice_axiom,[])).
% 7.55/1.51  
% 7.55/1.51  fof(f14,plain,(
% 7.55/1.51    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 7.55/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 7.55/1.51  
% 7.55/1.51  fof(f23,plain,(
% 7.55/1.51    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 7.55/1.51    inference(cnf_transformation,[],[f14])).
% 7.55/1.51  
% 7.55/1.51  fof(f25,plain,(
% 7.55/1.51    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)))),
% 7.55/1.51    inference(definition_unfolding,[],[f23,f21])).
% 7.55/1.51  
% 7.55/1.51  fof(f2,axiom,(
% 7.55/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.55/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.51  
% 7.55/1.51  fof(f11,plain,(
% 7.55/1.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.55/1.51    inference(ennf_transformation,[],[f2])).
% 7.55/1.51  
% 7.55/1.51  fof(f16,plain,(
% 7.55/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.55/1.51    inference(cnf_transformation,[],[f11])).
% 7.55/1.51  
% 7.55/1.51  fof(f3,axiom,(
% 7.55/1.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.55/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.51  
% 7.55/1.51  fof(f17,plain,(
% 7.55/1.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.55/1.51    inference(cnf_transformation,[],[f3])).
% 7.55/1.51  
% 7.55/1.51  fof(f5,axiom,(
% 7.55/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.55/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.51  
% 7.55/1.51  fof(f19,plain,(
% 7.55/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.55/1.51    inference(cnf_transformation,[],[f5])).
% 7.55/1.51  
% 7.55/1.51  fof(f1,axiom,(
% 7.55/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.55/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.51  
% 7.55/1.51  fof(f15,plain,(
% 7.55/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.55/1.51    inference(cnf_transformation,[],[f1])).
% 7.55/1.51  
% 7.55/1.51  fof(f4,axiom,(
% 7.55/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.55/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.51  
% 7.55/1.51  fof(f18,plain,(
% 7.55/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.55/1.51    inference(cnf_transformation,[],[f4])).
% 7.55/1.51  
% 7.55/1.51  cnf(c_5,plain,
% 7.55/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.55/1.51      inference(cnf_transformation,[],[f20]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_6,plain,
% 7.55/1.51      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.55/1.51      inference(cnf_transformation,[],[f24]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_67,plain,
% 7.55/1.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.55/1.51      inference(demodulation,[status(thm)],[c_6,c_5]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_452,plain,
% 7.55/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_5,c_67]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_453,plain,
% 7.55/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) ),
% 7.55/1.51      inference(light_normalisation,[status(thm)],[c_452,c_5]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_454,plain,
% 7.55/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3))) ),
% 7.55/1.51      inference(demodulation,[status(thm)],[c_453,c_5]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_7,negated_conjecture,
% 7.55/1.51      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
% 7.55/1.51      inference(cnf_transformation,[],[f25]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_70,plain,
% 7.55/1.51      ( k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))))) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 7.55/1.51      inference(demodulation,[status(thm)],[c_7,c_5]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_33572,plain,
% 7.55/1.51      ( k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)),sK2))) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 7.55/1.51      inference(demodulation,[status(thm)],[c_454,c_70]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_1,plain,
% 7.55/1.51      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.55/1.51      inference(cnf_transformation,[],[f16]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_2,plain,
% 7.55/1.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.55/1.51      inference(cnf_transformation,[],[f17]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_40,plain,
% 7.55/1.51      ( X0 != X1 | k4_xboole_0(X0,X2) != X3 | k2_xboole_0(X3,X1) = X1 ),
% 7.55/1.51      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_41,plain,
% 7.55/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 7.55/1.51      inference(unflattening,[status(thm)],[c_40]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_4,plain,
% 7.55/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.55/1.51      inference(cnf_transformation,[],[f19]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_294,plain,
% 7.55/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_41,c_4]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_609,plain,
% 7.55/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X0) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_294,c_5]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_0,plain,
% 7.55/1.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.55/1.51      inference(cnf_transformation,[],[f15]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_122,plain,
% 7.55/1.51      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_0,c_41]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_295,plain,
% 7.55/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_4,c_122]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_1248,plain,
% 7.55/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_0,c_295]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_291,plain,
% 7.55/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_321,plain,
% 7.55/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_291,c_122]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_1523,plain,
% 7.55/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_321,c_291]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_3,plain,
% 7.55/1.51      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.55/1.51      inference(cnf_transformation,[],[f18]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_323,plain,
% 7.55/1.51      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_291,c_3]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_325,plain,
% 7.55/1.51      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.55/1.51      inference(light_normalisation,[status(thm)],[c_323,c_3]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_1526,plain,
% 7.55/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X1,X1) ),
% 7.55/1.51      inference(demodulation,[status(thm)],[c_1523,c_5,c_325,c_609]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_4145,plain,
% 7.55/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_1248,c_1526]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_297,plain,
% 7.55/1.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_299,plain,
% 7.55/1.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.55/1.51      inference(light_normalisation,[status(thm)],[c_297,c_3]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_763,plain,
% 7.55/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_325,c_299]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_188,plain,
% 7.55/1.51      ( k2_xboole_0(X0,X0) = X0 ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_122,c_3]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_765,plain,
% 7.55/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 7.55/1.51      inference(demodulation,[status(thm)],[c_763,c_188]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_4154,plain,
% 7.55/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_765,c_1526]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_4146,plain,
% 7.55/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X1,X0)) ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_321,c_1526]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_4214,plain,
% 7.55/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,X1) ),
% 7.55/1.51      inference(demodulation,[status(thm)],[c_4146,c_4154]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_4218,plain,
% 7.55/1.51      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
% 7.55/1.51      inference(light_normalisation,[status(thm)],[c_4145,c_4154,c_4214]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_4610,plain,
% 7.55/1.51      ( k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
% 7.55/1.51      inference(superposition,[status(thm)],[c_4218,c_41]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_33573,plain,
% 7.55/1.51      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 7.55/1.51      inference(demodulation,[status(thm)],[c_33572,c_609,c_4610]) ).
% 7.55/1.51  
% 7.55/1.51  cnf(c_33574,plain,
% 7.55/1.51      ( $false ),
% 7.55/1.51      inference(equality_resolution_simp,[status(thm)],[c_33573]) ).
% 7.55/1.51  
% 7.55/1.51  
% 7.55/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.55/1.51  
% 7.55/1.51  ------                               Statistics
% 7.55/1.51  
% 7.55/1.51  ------ Selected
% 7.55/1.51  
% 7.55/1.51  total_time:                             0.814
% 7.55/1.51  
%------------------------------------------------------------------------------
