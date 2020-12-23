%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:55 EST 2020

% Result     : Theorem 15.56s
% Output     : CNFRefutation 15.56s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 171 expanded)
%              Number of clauses        :   39 (  74 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :   20
%              Number of atoms          :   91 ( 274 expanded)
%              Number of equality atoms :   51 ( 129 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f25,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_408,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_183,plain,
    ( r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_187,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3427,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_183,c_187])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_681,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_4247,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(X0,sK2)) = k2_xboole_0(k3_xboole_0(X0,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3427,c_681])).

cnf(c_4249,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(X0,sK2)) = k3_xboole_0(X0,sK0) ),
    inference(demodulation,[status(thm)],[c_4247,c_3])).

cnf(c_5282,plain,
    ( k3_xboole_0(k1_xboole_0,sK0) = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_408,c_4249])).

cnf(c_5375,plain,
    ( k3_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5282,c_3427])).

cnf(c_6598,plain,
    ( k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK0)) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5375,c_681])).

cnf(c_6603,plain,
    ( k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6598,c_3])).

cnf(c_683,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_8241,plain,
    ( k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,sK0),X1),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6603,c_683])).

cnf(c_8273,plain,
    ( k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,sK0),X1),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k2_xboole_0(X0,sK0),X1) ),
    inference(demodulation,[status(thm)],[c_8241,c_3])).

cnf(c_63555,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0)) = k3_xboole_0(k2_xboole_0(X0,sK0),X0) ),
    inference(superposition,[status(thm)],[c_8273,c_681])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_185,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_186,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1806,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_185,c_186])).

cnf(c_63586,plain,
    ( k3_xboole_0(k2_xboole_0(X0,sK0),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_63555,c_3,c_1806])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_182,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1807,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
    inference(superposition,[status(thm)],[c_182,c_186])).

cnf(c_5306,plain,
    ( k3_xboole_0(sK1,sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_4249,c_1807])).

cnf(c_592,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_185])).

cnf(c_837,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X0,k2_xboole_0(X2,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_592])).

cnf(c_1163,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X2,X1),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_837])).

cnf(c_6484,plain,
    ( r1_tarski(sK0,k3_xboole_0(k2_xboole_0(X0,sK0),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5306,c_1163])).

cnf(c_67673,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_63586,c_6484])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_67673,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.56/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.56/2.49  
% 15.56/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.56/2.49  
% 15.56/2.49  ------  iProver source info
% 15.56/2.49  
% 15.56/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.56/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.56/2.49  git: non_committed_changes: false
% 15.56/2.49  git: last_make_outside_of_git: false
% 15.56/2.49  
% 15.56/2.49  ------ 
% 15.56/2.49  ------ Parsing...
% 15.56/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.56/2.49  
% 15.56/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.56/2.49  ------ Proving...
% 15.56/2.49  ------ Problem Properties 
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  clauses                                 10
% 15.56/2.49  conjectures                             3
% 15.56/2.49  EPR                                     2
% 15.56/2.49  Horn                                    10
% 15.56/2.49  unary                                   8
% 15.56/2.49  binary                                  2
% 15.56/2.49  lits                                    12
% 15.56/2.49  lits eq                                 6
% 15.56/2.49  fd_pure                                 0
% 15.56/2.49  fd_pseudo                               0
% 15.56/2.49  fd_cond                                 0
% 15.56/2.49  fd_pseudo_cond                          0
% 15.56/2.49  AC symbols                              0
% 15.56/2.49  
% 15.56/2.49  ------ Input Options Time Limit: Unbounded
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ 
% 15.56/2.49  Current options:
% 15.56/2.49  ------ 
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  ------ Proving...
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  % SZS status Theorem for theBenchmark.p
% 15.56/2.49  
% 15.56/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.56/2.49  
% 15.56/2.49  fof(f4,axiom,(
% 15.56/2.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 15.56/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.49  
% 15.56/2.49  fof(f20,plain,(
% 15.56/2.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.56/2.49    inference(cnf_transformation,[],[f4])).
% 15.56/2.49  
% 15.56/2.49  fof(f1,axiom,(
% 15.56/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.56/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.49  
% 15.56/2.49  fof(f17,plain,(
% 15.56/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.56/2.49    inference(cnf_transformation,[],[f1])).
% 15.56/2.49  
% 15.56/2.49  fof(f8,conjecture,(
% 15.56/2.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 15.56/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.49  
% 15.56/2.49  fof(f9,negated_conjecture,(
% 15.56/2.49    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 15.56/2.49    inference(negated_conjecture,[],[f8])).
% 15.56/2.49  
% 15.56/2.49  fof(f13,plain,(
% 15.56/2.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 15.56/2.49    inference(ennf_transformation,[],[f9])).
% 15.56/2.49  
% 15.56/2.49  fof(f14,plain,(
% 15.56/2.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 15.56/2.49    inference(flattening,[],[f13])).
% 15.56/2.49  
% 15.56/2.49  fof(f15,plain,(
% 15.56/2.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 15.56/2.49    introduced(choice_axiom,[])).
% 15.56/2.49  
% 15.56/2.49  fof(f16,plain,(
% 15.56/2.49    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 15.56/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 15.56/2.49  
% 15.56/2.49  fof(f25,plain,(
% 15.56/2.49    r1_xboole_0(sK0,sK2)),
% 15.56/2.49    inference(cnf_transformation,[],[f16])).
% 15.56/2.49  
% 15.56/2.49  fof(f3,axiom,(
% 15.56/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.56/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.49  
% 15.56/2.49  fof(f10,plain,(
% 15.56/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.56/2.49    inference(unused_predicate_definition_removal,[],[f3])).
% 15.56/2.49  
% 15.56/2.49  fof(f11,plain,(
% 15.56/2.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 15.56/2.49    inference(ennf_transformation,[],[f10])).
% 15.56/2.49  
% 15.56/2.49  fof(f19,plain,(
% 15.56/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 15.56/2.49    inference(cnf_transformation,[],[f11])).
% 15.56/2.49  
% 15.56/2.49  fof(f2,axiom,(
% 15.56/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.56/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.49  
% 15.56/2.49  fof(f18,plain,(
% 15.56/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.56/2.49    inference(cnf_transformation,[],[f2])).
% 15.56/2.49  
% 15.56/2.49  fof(f5,axiom,(
% 15.56/2.49    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 15.56/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.49  
% 15.56/2.49  fof(f21,plain,(
% 15.56/2.49    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 15.56/2.49    inference(cnf_transformation,[],[f5])).
% 15.56/2.49  
% 15.56/2.49  fof(f7,axiom,(
% 15.56/2.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.56/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.49  
% 15.56/2.49  fof(f23,plain,(
% 15.56/2.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.56/2.49    inference(cnf_transformation,[],[f7])).
% 15.56/2.49  
% 15.56/2.49  fof(f6,axiom,(
% 15.56/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.56/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.56/2.49  
% 15.56/2.49  fof(f12,plain,(
% 15.56/2.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.56/2.49    inference(ennf_transformation,[],[f6])).
% 15.56/2.49  
% 15.56/2.49  fof(f22,plain,(
% 15.56/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.56/2.49    inference(cnf_transformation,[],[f12])).
% 15.56/2.49  
% 15.56/2.49  fof(f24,plain,(
% 15.56/2.49    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 15.56/2.49    inference(cnf_transformation,[],[f16])).
% 15.56/2.49  
% 15.56/2.49  fof(f26,plain,(
% 15.56/2.49    ~r1_tarski(sK0,sK1)),
% 15.56/2.49    inference(cnf_transformation,[],[f16])).
% 15.56/2.49  
% 15.56/2.49  cnf(c_3,plain,
% 15.56/2.49      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.56/2.49      inference(cnf_transformation,[],[f20]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_0,plain,
% 15.56/2.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.56/2.49      inference(cnf_transformation,[],[f17]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_408,plain,
% 15.56/2.49      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_8,negated_conjecture,
% 15.56/2.49      ( r1_xboole_0(sK0,sK2) ),
% 15.56/2.49      inference(cnf_transformation,[],[f25]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_183,plain,
% 15.56/2.49      ( r1_xboole_0(sK0,sK2) = iProver_top ),
% 15.56/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_2,plain,
% 15.56/2.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.56/2.49      inference(cnf_transformation,[],[f19]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_187,plain,
% 15.56/2.49      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 15.56/2.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 15.56/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_3427,plain,
% 15.56/2.49      ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_183,c_187]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_1,plain,
% 15.56/2.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.56/2.49      inference(cnf_transformation,[],[f18]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_4,plain,
% 15.56/2.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.56/2.49      inference(cnf_transformation,[],[f21]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_681,plain,
% 15.56/2.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_4247,plain,
% 15.56/2.49      ( k3_xboole_0(sK0,k2_xboole_0(X0,sK2)) = k2_xboole_0(k3_xboole_0(X0,sK0),k1_xboole_0) ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_3427,c_681]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_4249,plain,
% 15.56/2.49      ( k3_xboole_0(sK0,k2_xboole_0(X0,sK2)) = k3_xboole_0(X0,sK0) ),
% 15.56/2.49      inference(demodulation,[status(thm)],[c_4247,c_3]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_5282,plain,
% 15.56/2.49      ( k3_xboole_0(k1_xboole_0,sK0) = k3_xboole_0(sK0,sK2) ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_408,c_4249]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_5375,plain,
% 15.56/2.49      ( k3_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
% 15.56/2.49      inference(light_normalisation,[status(thm)],[c_5282,c_3427]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_6598,plain,
% 15.56/2.49      ( k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK0)) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_5375,c_681]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_6603,plain,
% 15.56/2.49      ( k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 15.56/2.49      inference(demodulation,[status(thm)],[c_6598,c_3]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_683,plain,
% 15.56/2.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_8241,plain,
% 15.56/2.49      ( k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,sK0),X1),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(X1,k1_xboole_0)) ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_6603,c_683]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_8273,plain,
% 15.56/2.49      ( k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,sK0),X1),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k2_xboole_0(X0,sK0),X1) ),
% 15.56/2.49      inference(demodulation,[status(thm)],[c_8241,c_3]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_63555,plain,
% 15.56/2.49      ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0)) = k3_xboole_0(k2_xboole_0(X0,sK0),X0) ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_8273,c_681]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_6,plain,
% 15.56/2.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 15.56/2.49      inference(cnf_transformation,[],[f23]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_185,plain,
% 15.56/2.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 15.56/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_5,plain,
% 15.56/2.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.56/2.49      inference(cnf_transformation,[],[f22]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_186,plain,
% 15.56/2.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 15.56/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_1806,plain,
% 15.56/2.49      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_185,c_186]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_63586,plain,
% 15.56/2.49      ( k3_xboole_0(k2_xboole_0(X0,sK0),X0) = X0 ),
% 15.56/2.49      inference(demodulation,[status(thm)],[c_63555,c_3,c_1806]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_9,negated_conjecture,
% 15.56/2.49      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.56/2.49      inference(cnf_transformation,[],[f24]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_182,plain,
% 15.56/2.49      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 15.56/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_1807,plain,
% 15.56/2.49      ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_182,c_186]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_5306,plain,
% 15.56/2.49      ( k3_xboole_0(sK1,sK0) = sK0 ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_4249,c_1807]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_592,plain,
% 15.56/2.49      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_0,c_185]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_837,plain,
% 15.56/2.49      ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X0,k2_xboole_0(X2,X1))) = iProver_top ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_4,c_592]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_1163,plain,
% 15.56/2.49      ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X2,X1),X0)) = iProver_top ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_1,c_837]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_6484,plain,
% 15.56/2.49      ( r1_tarski(sK0,k3_xboole_0(k2_xboole_0(X0,sK0),sK1)) = iProver_top ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_5306,c_1163]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_67673,plain,
% 15.56/2.49      ( r1_tarski(sK0,sK1) = iProver_top ),
% 15.56/2.49      inference(superposition,[status(thm)],[c_63586,c_6484]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_7,negated_conjecture,
% 15.56/2.49      ( ~ r1_tarski(sK0,sK1) ),
% 15.56/2.49      inference(cnf_transformation,[],[f26]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(c_12,plain,
% 15.56/2.49      ( r1_tarski(sK0,sK1) != iProver_top ),
% 15.56/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.56/2.49  
% 15.56/2.49  cnf(contradiction,plain,
% 15.56/2.49      ( $false ),
% 15.56/2.49      inference(minisat,[status(thm)],[c_67673,c_12]) ).
% 15.56/2.49  
% 15.56/2.49  
% 15.56/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.56/2.49  
% 15.56/2.49  ------                               Statistics
% 15.56/2.49  
% 15.56/2.49  ------ Selected
% 15.56/2.49  
% 15.56/2.49  total_time:                             1.706
% 15.56/2.49  
%------------------------------------------------------------------------------
