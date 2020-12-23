%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:19 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 141 expanded)
%              Number of clauses        :   35 (  48 expanded)
%              Number of leaves         :   10 (  36 expanded)
%              Depth                    :   15
%              Number of atoms          :  105 ( 207 expanded)
%              Number of equality atoms :   63 ( 126 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f32,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f32,f27])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f30,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_57,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_109,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_57,c_10])).

cnf(c_110,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_109])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_557,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_110,c_9])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_558,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_5,c_9])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_148,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_5])).

cnf(c_593,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_558,c_148])).

cnf(c_594,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_593,c_5])).

cnf(c_596,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_557,c_594])).

cnf(c_1486,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_7,c_596])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_565,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_4])).

cnf(c_570,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_565,c_5,c_148])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_102,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_103,plain,
    ( k4_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_102])).

cnf(c_561,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_103,c_9])).

cnf(c_581,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,X0),sK0) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_561,c_5])).

cnf(c_1298,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_570,c_581])).

cnf(c_1637,plain,
    ( k4_xboole_0(sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_1486,c_1298])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_55,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_12,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_114,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_55,c_12])).

cnf(c_115,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_114])).

cnf(c_1639,plain,
    ( k4_xboole_0(sK0,sK0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1637,c_115])).

cnf(c_1640,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1639,c_148])).

cnf(c_1641,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1640])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:14:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.37/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.01  
% 2.37/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.37/1.01  
% 2.37/1.01  ------  iProver source info
% 2.37/1.01  
% 2.37/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.37/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.37/1.01  git: non_committed_changes: false
% 2.37/1.01  git: last_make_outside_of_git: false
% 2.37/1.01  
% 2.37/1.01  ------ 
% 2.37/1.01  ------ Parsing...
% 2.37/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.37/1.01  
% 2.37/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.37/1.01  
% 2.37/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.37/1.01  
% 2.37/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.37/1.01  ------ Proving...
% 2.37/1.01  ------ Problem Properties 
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  clauses                                 11
% 2.37/1.01  conjectures                             0
% 2.37/1.01  EPR                                     0
% 2.37/1.01  Horn                                    11
% 2.37/1.01  unary                                   11
% 2.37/1.01  binary                                  0
% 2.37/1.01  lits                                    11
% 2.37/1.01  lits eq                                 11
% 2.37/1.01  fd_pure                                 0
% 2.37/1.01  fd_pseudo                               0
% 2.37/1.01  fd_cond                                 0
% 2.37/1.01  fd_pseudo_cond                          0
% 2.37/1.01  AC symbols                              0
% 2.37/1.01  
% 2.37/1.01  ------ Input Options Time Limit: Unbounded
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  ------ 
% 2.37/1.01  Current options:
% 2.37/1.01  ------ 
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  ------ Proving...
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  % SZS status Theorem for theBenchmark.p
% 2.37/1.01  
% 2.37/1.01   Resolution empty clause
% 2.37/1.01  
% 2.37/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.37/1.01  
% 2.37/1.01  fof(f7,axiom,(
% 2.37/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f26,plain,(
% 2.37/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.37/1.01    inference(cnf_transformation,[],[f7])).
% 2.37/1.01  
% 2.37/1.01  fof(f8,axiom,(
% 2.37/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f27,plain,(
% 2.37/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.37/1.01    inference(cnf_transformation,[],[f8])).
% 2.37/1.01  
% 2.37/1.01  fof(f36,plain,(
% 2.37/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.37/1.01    inference(definition_unfolding,[],[f26,f27])).
% 2.37/1.01  
% 2.37/1.01  fof(f1,axiom,(
% 2.37/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f16,plain,(
% 2.37/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.37/1.01    inference(nnf_transformation,[],[f1])).
% 2.37/1.01  
% 2.37/1.01  fof(f19,plain,(
% 2.37/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.37/1.01    inference(cnf_transformation,[],[f16])).
% 2.37/1.01  
% 2.37/1.01  fof(f34,plain,(
% 2.37/1.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.37/1.01    inference(definition_unfolding,[],[f19,f27])).
% 2.37/1.01  
% 2.37/1.01  fof(f11,conjecture,(
% 2.37/1.01    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f12,negated_conjecture,(
% 2.37/1.01    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.37/1.01    inference(negated_conjecture,[],[f11])).
% 2.37/1.01  
% 2.37/1.01  fof(f15,plain,(
% 2.37/1.01    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 2.37/1.01    inference(ennf_transformation,[],[f12])).
% 2.37/1.01  
% 2.37/1.01  fof(f17,plain,(
% 2.37/1.01    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 2.37/1.01    introduced(choice_axiom,[])).
% 2.37/1.01  
% 2.37/1.01  fof(f18,plain,(
% 2.37/1.01    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 2.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 2.37/1.01  
% 2.37/1.01  fof(f32,plain,(
% 2.37/1.01    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 2.37/1.01    inference(cnf_transformation,[],[f18])).
% 2.37/1.01  
% 2.37/1.01  fof(f39,plain,(
% 2.37/1.01    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 2.37/1.01    inference(definition_unfolding,[],[f32,f27])).
% 2.37/1.01  
% 2.37/1.01  fof(f10,axiom,(
% 2.37/1.01    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f29,plain,(
% 2.37/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.37/1.01    inference(cnf_transformation,[],[f10])).
% 2.37/1.01  
% 2.37/1.01  fof(f38,plain,(
% 2.37/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 2.37/1.01    inference(definition_unfolding,[],[f29,f27])).
% 2.37/1.01  
% 2.37/1.01  fof(f5,axiom,(
% 2.37/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f24,plain,(
% 2.37/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.37/1.01    inference(cnf_transformation,[],[f5])).
% 2.37/1.01  
% 2.37/1.01  fof(f3,axiom,(
% 2.37/1.01    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f22,plain,(
% 2.37/1.01    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.37/1.01    inference(cnf_transformation,[],[f3])).
% 2.37/1.01  
% 2.37/1.01  fof(f35,plain,(
% 2.37/1.01    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.37/1.01    inference(definition_unfolding,[],[f22,f27])).
% 2.37/1.01  
% 2.37/1.01  fof(f4,axiom,(
% 2.37/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f23,plain,(
% 2.37/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.37/1.01    inference(cnf_transformation,[],[f4])).
% 2.37/1.01  
% 2.37/1.01  fof(f2,axiom,(
% 2.37/1.01    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.37/1.01  
% 2.37/1.01  fof(f13,plain,(
% 2.37/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 2.37/1.01    inference(unused_predicate_definition_removal,[],[f2])).
% 2.37/1.01  
% 2.37/1.01  fof(f14,plain,(
% 2.37/1.01    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 2.37/1.01    inference(ennf_transformation,[],[f13])).
% 2.37/1.01  
% 2.37/1.01  fof(f21,plain,(
% 2.37/1.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.37/1.01    inference(cnf_transformation,[],[f14])).
% 2.37/1.01  
% 2.37/1.01  fof(f31,plain,(
% 2.37/1.01    r1_tarski(sK0,sK2)),
% 2.37/1.01    inference(cnf_transformation,[],[f18])).
% 2.37/1.01  
% 2.37/1.01  fof(f20,plain,(
% 2.37/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.37/1.01    inference(cnf_transformation,[],[f16])).
% 2.37/1.01  
% 2.37/1.01  fof(f33,plain,(
% 2.37/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.37/1.01    inference(definition_unfolding,[],[f20,f27])).
% 2.37/1.01  
% 2.37/1.01  fof(f30,plain,(
% 2.37/1.01    ~r1_xboole_0(sK0,sK1)),
% 2.37/1.01    inference(cnf_transformation,[],[f18])).
% 2.37/1.01  
% 2.37/1.01  cnf(c_7,plain,
% 2.37/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.37/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1,plain,
% 2.37/1.01      ( ~ r1_xboole_0(X0,X1)
% 2.37/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 2.37/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_57,plain,
% 2.37/1.01      ( ~ r1_xboole_0(X0,X1)
% 2.37/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 2.37/1.01      inference(prop_impl,[status(thm)],[c_1]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_10,negated_conjecture,
% 2.37/1.01      ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 2.37/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_109,plain,
% 2.37/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 2.37/1.01      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
% 2.37/1.01      | sK0 != X0 ),
% 2.37/1.01      inference(resolution_lifted,[status(thm)],[c_57,c_10]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_110,plain,
% 2.37/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 2.37/1.01      inference(unflattening,[status(thm)],[c_109]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_9,plain,
% 2.37/1.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 2.37/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_557,plain,
% 2.37/1.01      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0) ),
% 2.37/1.01      inference(superposition,[status(thm)],[c_110,c_9]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_5,plain,
% 2.37/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.37/1.01      inference(cnf_transformation,[],[f24]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_558,plain,
% 2.37/1.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
% 2.37/1.01      inference(superposition,[status(thm)],[c_5,c_9]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_3,plain,
% 2.37/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.37/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_148,plain,
% 2.37/1.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.37/1.01      inference(light_normalisation,[status(thm)],[c_3,c_5]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_593,plain,
% 2.37/1.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
% 2.37/1.01      inference(light_normalisation,[status(thm)],[c_558,c_148]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_594,plain,
% 2.37/1.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
% 2.37/1.01      inference(demodulation,[status(thm)],[c_593,c_5]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_596,plain,
% 2.37/1.01      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,X0) ),
% 2.37/1.01      inference(demodulation,[status(thm)],[c_557,c_594]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1486,plain,
% 2.37/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK1) ),
% 2.37/1.01      inference(superposition,[status(thm)],[c_7,c_596]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_4,plain,
% 2.37/1.01      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 2.37/1.01      inference(cnf_transformation,[],[f23]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_565,plain,
% 2.37/1.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
% 2.37/1.01      inference(superposition,[status(thm)],[c_9,c_4]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_570,plain,
% 2.37/1.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 2.37/1.01      inference(demodulation,[status(thm)],[c_565,c_5,c_148]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_2,plain,
% 2.37/1.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.37/1.01      inference(cnf_transformation,[],[f21]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_11,negated_conjecture,
% 2.37/1.01      ( r1_tarski(sK0,sK2) ),
% 2.37/1.01      inference(cnf_transformation,[],[f31]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_102,plain,
% 2.37/1.01      ( k4_xboole_0(X0,X1) = k1_xboole_0 | sK2 != X1 | sK0 != X0 ),
% 2.37/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_103,plain,
% 2.37/1.01      ( k4_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 2.37/1.01      inference(unflattening,[status(thm)],[c_102]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_561,plain,
% 2.37/1.01      ( k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) ),
% 2.37/1.01      inference(superposition,[status(thm)],[c_103,c_9]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_581,plain,
% 2.37/1.01      ( k2_xboole_0(k4_xboole_0(sK0,X0),sK0) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) ),
% 2.37/1.01      inference(demodulation,[status(thm)],[c_561,c_5]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1298,plain,
% 2.37/1.01      ( k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = sK0 ),
% 2.37/1.01      inference(demodulation,[status(thm)],[c_570,c_581]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1637,plain,
% 2.37/1.01      ( k4_xboole_0(sK0,sK1) = sK0 ),
% 2.37/1.01      inference(demodulation,[status(thm)],[c_1486,c_1298]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_0,plain,
% 2.37/1.01      ( r1_xboole_0(X0,X1)
% 2.37/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 2.37/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_55,plain,
% 2.37/1.01      ( r1_xboole_0(X0,X1)
% 2.37/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 2.37/1.01      inference(prop_impl,[status(thm)],[c_0]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_12,negated_conjecture,
% 2.37/1.01      ( ~ r1_xboole_0(sK0,sK1) ),
% 2.37/1.01      inference(cnf_transformation,[],[f30]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_114,plain,
% 2.37/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 2.37/1.01      | sK1 != X1
% 2.37/1.01      | sK0 != X0 ),
% 2.37/1.01      inference(resolution_lifted,[status(thm)],[c_55,c_12]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_115,plain,
% 2.37/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 2.37/1.01      inference(unflattening,[status(thm)],[c_114]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1639,plain,
% 2.37/1.01      ( k4_xboole_0(sK0,sK0) != k1_xboole_0 ),
% 2.37/1.01      inference(demodulation,[status(thm)],[c_1637,c_115]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1640,plain,
% 2.37/1.01      ( k1_xboole_0 != k1_xboole_0 ),
% 2.37/1.01      inference(demodulation,[status(thm)],[c_1639,c_148]) ).
% 2.37/1.01  
% 2.37/1.01  cnf(c_1641,plain,
% 2.37/1.01      ( $false ),
% 2.37/1.01      inference(equality_resolution_simp,[status(thm)],[c_1640]) ).
% 2.37/1.01  
% 2.37/1.01  
% 2.37/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.37/1.01  
% 2.37/1.01  ------                               Statistics
% 2.37/1.01  
% 2.37/1.01  ------ Selected
% 2.37/1.01  
% 2.37/1.01  total_time:                             0.217
% 2.37/1.01  
%------------------------------------------------------------------------------
