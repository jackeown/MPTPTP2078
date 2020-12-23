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
% DateTime   : Thu Dec  3 11:38:31 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 182 expanded)
%              Number of clauses        :   31 (  37 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  118 ( 319 expanded)
%              Number of equality atoms :   86 ( 226 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f21,f25,f25])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
      & r2_hidden(sK3,sK0)
      & k3_xboole_0(sK1,sK2) = k1_tarski(sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
    & r2_hidden(sK3,sK0)
    & k3_xboole_0(sK1,sK2) = k1_tarski(sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).

fof(f33,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f43,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f33,f25,f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f34,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f23,f25,f25,f25,f25])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f32,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f35,f25,f38])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_8,negated_conjecture,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7,negated_conjecture,
    ( r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_69,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1
    | sK3 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_7])).

cnf(c_70,plain,
    ( k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) = sK0 ),
    inference(unflattening,[status(thm)],[c_69])).

cnf(c_113,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_8,c_70])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_75,plain,
    ( X0 != X1
    | k2_xboole_0(X0,X2) != X3
    | k4_xboole_0(X1,X3) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_76,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_75])).

cnf(c_226,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_113,c_76])).

cnf(c_280,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_226])).

cnf(c_2,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_401,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_280,c_2])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_445,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(demodulation,[status(thm)],[c_401,c_3])).

cnf(c_1279,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_0,c_445])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_81,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_82,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_81])).

cnf(c_1291,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_1279,c_82])).

cnf(c_1292,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(demodulation,[status(thm)],[c_1291,c_3])).

cnf(c_283,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_8])).

cnf(c_1471,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(demodulation,[status(thm)],[c_1292,c_283])).

cnf(c_139,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_94,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_128,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_138,plain,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_6,negated_conjecture,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1471,c_139,c_138,c_6])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.04/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/0.99  
% 3.04/0.99  ------  iProver source info
% 3.04/0.99  
% 3.04/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.04/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/0.99  git: non_committed_changes: false
% 3.04/0.99  git: last_make_outside_of_git: false
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  ------ Parsing...
% 3.04/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.04/0.99  ------ Proving...
% 3.04/0.99  ------ Problem Properties 
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  clauses                                 8
% 3.04/0.99  conjectures                             2
% 3.04/0.99  EPR                                     0
% 3.04/0.99  Horn                                    8
% 3.04/0.99  unary                                   8
% 3.04/0.99  binary                                  0
% 3.04/0.99  lits                                    8
% 3.04/0.99  lits eq                                 8
% 3.04/0.99  fd_pure                                 0
% 3.04/0.99  fd_pseudo                               0
% 3.04/0.99  fd_cond                                 0
% 3.04/0.99  fd_pseudo_cond                          0
% 3.04/0.99  AC symbols                              0
% 3.04/0.99  
% 3.04/0.99  ------ Input Options Time Limit: Unbounded
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  Current options:
% 3.04/0.99  ------ 
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ Proving...
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS status Theorem for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  fof(f1,axiom,(
% 3.04/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f21,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f1])).
% 3.04/0.99  
% 3.04/0.99  fof(f5,axiom,(
% 3.04/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f25,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f5])).
% 3.04/0.99  
% 3.04/0.99  fof(f39,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.04/0.99    inference(definition_unfolding,[],[f21,f25,f25])).
% 3.04/0.99  
% 3.04/0.99  fof(f12,conjecture,(
% 3.04/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f13,negated_conjecture,(
% 3.04/0.99    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 3.04/0.99    inference(negated_conjecture,[],[f12])).
% 3.04/0.99  
% 3.04/0.99  fof(f17,plain,(
% 3.04/0.99    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 3.04/0.99    inference(ennf_transformation,[],[f13])).
% 3.04/0.99  
% 3.04/0.99  fof(f18,plain,(
% 3.04/0.99    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 3.04/0.99    inference(flattening,[],[f17])).
% 3.04/0.99  
% 3.04/0.99  fof(f19,plain,(
% 3.04/0.99    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k3_xboole_0(sK1,sK2) = k1_tarski(sK3) & r1_tarski(sK0,sK1))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f20,plain,(
% 3.04/0.99    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k3_xboole_0(sK1,sK2) = k1_tarski(sK3) & r1_tarski(sK0,sK1)),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).
% 3.04/0.99  
% 3.04/0.99  fof(f33,plain,(
% 3.04/0.99    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 3.04/0.99    inference(cnf_transformation,[],[f20])).
% 3.04/0.99  
% 3.04/0.99  fof(f7,axiom,(
% 3.04/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f27,plain,(
% 3.04/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f7])).
% 3.04/0.99  
% 3.04/0.99  fof(f8,axiom,(
% 3.04/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f28,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f8])).
% 3.04/0.99  
% 3.04/0.99  fof(f9,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f29,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f9])).
% 3.04/0.99  
% 3.04/0.99  fof(f10,axiom,(
% 3.04/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f30,plain,(
% 3.04/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f10])).
% 3.04/0.99  
% 3.04/0.99  fof(f36,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.04/0.99    inference(definition_unfolding,[],[f29,f30])).
% 3.04/0.99  
% 3.04/0.99  fof(f37,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.04/0.99    inference(definition_unfolding,[],[f28,f36])).
% 3.04/0.99  
% 3.04/0.99  fof(f38,plain,(
% 3.04/0.99    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.04/0.99    inference(definition_unfolding,[],[f27,f37])).
% 3.04/0.99  
% 3.04/0.99  fof(f43,plain,(
% 3.04/0.99    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 3.04/0.99    inference(definition_unfolding,[],[f33,f25,f38])).
% 3.04/0.99  
% 3.04/0.99  fof(f11,axiom,(
% 3.04/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f16,plain,(
% 3.04/0.99    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 3.04/0.99    inference(ennf_transformation,[],[f11])).
% 3.04/0.99  
% 3.04/0.99  fof(f31,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f16])).
% 3.04/0.99  
% 3.04/0.99  fof(f41,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 3.04/0.99    inference(definition_unfolding,[],[f31,f38])).
% 3.04/0.99  
% 3.04/0.99  fof(f34,plain,(
% 3.04/0.99    r2_hidden(sK3,sK0)),
% 3.04/0.99    inference(cnf_transformation,[],[f20])).
% 3.04/0.99  
% 3.04/0.99  fof(f2,axiom,(
% 3.04/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f14,plain,(
% 3.04/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 3.04/0.99    inference(unused_predicate_definition_removal,[],[f2])).
% 3.04/0.99  
% 3.04/0.99  fof(f15,plain,(
% 3.04/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 3.04/0.99    inference(ennf_transformation,[],[f14])).
% 3.04/0.99  
% 3.04/0.99  fof(f22,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f15])).
% 3.04/0.99  
% 3.04/0.99  fof(f6,axiom,(
% 3.04/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f26,plain,(
% 3.04/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f6])).
% 3.04/0.99  
% 3.04/0.99  fof(f3,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f23,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f3])).
% 3.04/0.99  
% 3.04/0.99  fof(f40,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 3.04/0.99    inference(definition_unfolding,[],[f23,f25,f25,f25,f25])).
% 3.04/0.99  
% 3.04/0.99  fof(f4,axiom,(
% 3.04/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f24,plain,(
% 3.04/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.04/0.99    inference(cnf_transformation,[],[f4])).
% 3.04/0.99  
% 3.04/0.99  fof(f32,plain,(
% 3.04/0.99    r1_tarski(sK0,sK1)),
% 3.04/0.99    inference(cnf_transformation,[],[f20])).
% 3.04/0.99  
% 3.04/0.99  fof(f35,plain,(
% 3.04/0.99    k3_xboole_0(sK0,sK2) != k1_tarski(sK3)),
% 3.04/0.99    inference(cnf_transformation,[],[f20])).
% 3.04/0.99  
% 3.04/0.99  fof(f42,plain,(
% 3.04/0.99    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 3.04/0.99    inference(definition_unfolding,[],[f35,f25,f38])).
% 3.04/0.99  
% 3.04/0.99  cnf(c_0,plain,
% 3.04/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_8,negated_conjecture,
% 3.04/0.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.04/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5,plain,
% 3.04/0.99      ( ~ r2_hidden(X0,X1)
% 3.04/0.99      | k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 ),
% 3.04/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_7,negated_conjecture,
% 3.04/0.99      ( r2_hidden(sK3,sK0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_69,plain,
% 3.04/0.99      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1
% 3.04/0.99      | sK3 != X0
% 3.04/0.99      | sK0 != X1 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_7]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_70,plain,
% 3.04/0.99      ( k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) = sK0 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_69]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_113,plain,
% 3.04/0.99      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) = sK0 ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_8,c_70]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1,plain,
% 3.04/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.04/0.99      inference(cnf_transformation,[],[f22]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4,plain,
% 3.04/0.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_75,plain,
% 3.04/0.99      ( X0 != X1
% 3.04/0.99      | k2_xboole_0(X0,X2) != X3
% 3.04/0.99      | k4_xboole_0(X1,X3) = k1_xboole_0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_4]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_76,plain,
% 3.04/0.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_75]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_226,plain,
% 3.04/0.99      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) = k1_xboole_0 ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_113,c_76]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_280,plain,
% 3.04/0.99      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = k1_xboole_0 ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_0,c_226]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2,plain,
% 3.04/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 3.04/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_401,plain,
% 3.04/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_280,c_2]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3,plain,
% 3.04/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.04/0.99      inference(cnf_transformation,[],[f24]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_445,plain,
% 3.04/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_401,c_3]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1279,plain,
% 3.04/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_0,c_445]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_9,negated_conjecture,
% 3.04/0.99      ( r1_tarski(sK0,sK1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_81,plain,
% 3.04/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0 | sK1 != X1 | sK0 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_9]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_82,plain,
% 3.04/0.99      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_81]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1291,plain,
% 3.04/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_1279,c_82]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1292,plain,
% 3.04/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_1291,c_3]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_283,plain,
% 3.04/0.99      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_0,c_8]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1471,plain,
% 3.04/0.99      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_1292,c_283]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_139,plain,
% 3.04/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_94,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_128,plain,
% 3.04/0.99      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != X0
% 3.04/0.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X0
% 3.04/0.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_94]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_138,plain,
% 3.04/0.99      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
% 3.04/0.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
% 3.04/0.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_128]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6,negated_conjecture,
% 3.04/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.04/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(contradiction,plain,
% 3.04/0.99      ( $false ),
% 3.04/0.99      inference(minisat,[status(thm)],[c_1471,c_139,c_138,c_6]) ).
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  ------                               Statistics
% 3.04/0.99  
% 3.04/0.99  ------ Selected
% 3.04/0.99  
% 3.04/0.99  total_time:                             0.101
% 3.04/0.99  
%------------------------------------------------------------------------------
