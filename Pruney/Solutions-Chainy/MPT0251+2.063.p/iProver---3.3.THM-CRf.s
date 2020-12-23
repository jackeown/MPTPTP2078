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
% DateTime   : Thu Dec  3 11:33:12 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 353 expanded)
%              Number of clauses        :   33 (  51 expanded)
%              Number of leaves         :   17 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 ( 408 expanded)
%              Number of equality atoms :   78 ( 346 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).

fof(f43,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f35,f47,f47,f31])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f26,f47,f47])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f36,f31,f31,f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1 ),
    inference(definition_unfolding,[],[f44,f47,f48])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_235,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_236,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_238,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_623,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_236,c_238])).

cnf(c_1406,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_235,c_623])).

cnf(c_8,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1883,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_1406,c_8])).

cnf(c_5,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_0,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_629,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_9,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_877,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_629,c_9])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_239,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_471,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_239,c_238])).

cnf(c_886,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_877,c_471])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_237,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_472,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_237,c_238])).

cnf(c_1216,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_886,c_472])).

cnf(c_881,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_629,c_8])).

cnf(c_882,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_881,c_629])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1030,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_472,c_1])).

cnf(c_1213,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_882,c_1030])).

cnf(c_1217,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1216,c_1213])).

cnf(c_1888,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_1883,c_5,c_1217])).

cnf(c_11,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_628,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(demodulation,[status(thm)],[c_0,c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1888,c_628])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n010.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 18:40:44 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.49/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/0.92  
% 3.49/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/0.92  
% 3.49/0.92  ------  iProver source info
% 3.49/0.92  
% 3.49/0.92  git: date: 2020-06-30 10:37:57 +0100
% 3.49/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/0.92  git: non_committed_changes: false
% 3.49/0.92  git: last_make_outside_of_git: false
% 3.49/0.92  
% 3.49/0.92  ------ 
% 3.49/0.92  ------ Parsing...
% 3.49/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/0.92  
% 3.49/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.49/0.92  
% 3.49/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/0.92  
% 3.49/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.49/0.92  ------ Proving...
% 3.49/0.92  ------ Problem Properties 
% 3.49/0.92  
% 3.49/0.92  
% 3.49/0.92  clauses                                 12
% 3.49/0.92  conjectures                             2
% 3.49/0.92  EPR                                     4
% 3.49/0.92  Horn                                    12
% 3.49/0.92  unary                                   9
% 3.49/0.92  binary                                  2
% 3.49/0.92  lits                                    16
% 3.49/0.92  lits eq                                 8
% 3.49/0.92  fd_pure                                 0
% 3.49/0.92  fd_pseudo                               0
% 3.49/0.92  fd_cond                                 0
% 3.49/0.92  fd_pseudo_cond                          1
% 3.49/0.92  AC symbols                              0
% 3.49/0.92  
% 3.49/0.92  ------ Input Options Time Limit: Unbounded
% 3.49/0.92  
% 3.49/0.92  
% 3.49/0.92  ------ 
% 3.49/0.92  Current options:
% 3.49/0.92  ------ 
% 3.49/0.92  
% 3.49/0.92  
% 3.49/0.92  
% 3.49/0.92  
% 3.49/0.92  ------ Proving...
% 3.49/0.92  
% 3.49/0.92  
% 3.49/0.92  % SZS status Theorem for theBenchmark.p
% 3.49/0.92  
% 3.49/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/0.92  
% 3.49/0.92  fof(f16,conjecture,(
% 3.49/0.92    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f17,negated_conjecture,(
% 3.49/0.92    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.49/0.92    inference(negated_conjecture,[],[f16])).
% 3.49/0.92  
% 3.49/0.92  fof(f21,plain,(
% 3.49/0.92    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 3.49/0.92    inference(ennf_transformation,[],[f17])).
% 3.49/0.92  
% 3.49/0.92  fof(f24,plain,(
% 3.49/0.92    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1))),
% 3.49/0.92    introduced(choice_axiom,[])).
% 3.49/0.92  
% 3.49/0.92  fof(f25,plain,(
% 3.49/0.92    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1)),
% 3.49/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).
% 3.49/0.92  
% 3.49/0.92  fof(f43,plain,(
% 3.49/0.92    r2_hidden(sK0,sK1)),
% 3.49/0.92    inference(cnf_transformation,[],[f25])).
% 3.49/0.92  
% 3.49/0.92  fof(f14,axiom,(
% 3.49/0.92    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f18,plain,(
% 3.49/0.92    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 3.49/0.92    inference(unused_predicate_definition_removal,[],[f14])).
% 3.49/0.92  
% 3.49/0.92  fof(f20,plain,(
% 3.49/0.92    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 3.49/0.92    inference(ennf_transformation,[],[f18])).
% 3.49/0.92  
% 3.49/0.92  fof(f41,plain,(
% 3.49/0.92    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.49/0.92    inference(cnf_transformation,[],[f20])).
% 3.49/0.92  
% 3.49/0.92  fof(f10,axiom,(
% 3.49/0.92    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f37,plain,(
% 3.49/0.92    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.49/0.92    inference(cnf_transformation,[],[f10])).
% 3.49/0.92  
% 3.49/0.92  fof(f11,axiom,(
% 3.49/0.92    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f38,plain,(
% 3.49/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.49/0.92    inference(cnf_transformation,[],[f11])).
% 3.49/0.92  
% 3.49/0.92  fof(f12,axiom,(
% 3.49/0.92    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f39,plain,(
% 3.49/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.49/0.92    inference(cnf_transformation,[],[f12])).
% 3.49/0.92  
% 3.49/0.92  fof(f13,axiom,(
% 3.49/0.92    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f40,plain,(
% 3.49/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.49/0.92    inference(cnf_transformation,[],[f13])).
% 3.49/0.92  
% 3.49/0.92  fof(f45,plain,(
% 3.49/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.49/0.92    inference(definition_unfolding,[],[f39,f40])).
% 3.49/0.92  
% 3.49/0.92  fof(f46,plain,(
% 3.49/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.49/0.92    inference(definition_unfolding,[],[f38,f45])).
% 3.49/0.92  
% 3.49/0.92  fof(f48,plain,(
% 3.49/0.92    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.49/0.92    inference(definition_unfolding,[],[f37,f46])).
% 3.49/0.92  
% 3.49/0.92  fof(f53,plain,(
% 3.49/0.92    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.49/0.92    inference(definition_unfolding,[],[f41,f48])).
% 3.49/0.92  
% 3.49/0.92  fof(f6,axiom,(
% 3.49/0.92    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f19,plain,(
% 3.49/0.92    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.49/0.92    inference(ennf_transformation,[],[f6])).
% 3.49/0.92  
% 3.49/0.92  fof(f33,plain,(
% 3.49/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.49/0.92    inference(cnf_transformation,[],[f19])).
% 3.49/0.92  
% 3.49/0.92  fof(f8,axiom,(
% 3.49/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f35,plain,(
% 3.49/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.49/0.92    inference(cnf_transformation,[],[f8])).
% 3.49/0.92  
% 3.49/0.92  fof(f15,axiom,(
% 3.49/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f42,plain,(
% 3.49/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.49/0.92    inference(cnf_transformation,[],[f15])).
% 3.49/0.92  
% 3.49/0.92  fof(f47,plain,(
% 3.49/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.49/0.92    inference(definition_unfolding,[],[f42,f46])).
% 3.49/0.92  
% 3.49/0.92  fof(f4,axiom,(
% 3.49/0.92    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f31,plain,(
% 3.49/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.49/0.92    inference(cnf_transformation,[],[f4])).
% 3.49/0.92  
% 3.49/0.92  fof(f51,plain,(
% 3.49/0.92    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.49/0.92    inference(definition_unfolding,[],[f35,f47,f47,f31])).
% 3.49/0.92  
% 3.49/0.92  fof(f5,axiom,(
% 3.49/0.92    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f32,plain,(
% 3.49/0.92    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.49/0.92    inference(cnf_transformation,[],[f5])).
% 3.49/0.92  
% 3.49/0.92  fof(f50,plain,(
% 3.49/0.92    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 3.49/0.92    inference(definition_unfolding,[],[f32,f47])).
% 3.49/0.92  
% 3.49/0.92  fof(f1,axiom,(
% 3.49/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f26,plain,(
% 3.49/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.49/0.92    inference(cnf_transformation,[],[f1])).
% 3.49/0.92  
% 3.49/0.92  fof(f49,plain,(
% 3.49/0.92    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 3.49/0.92    inference(definition_unfolding,[],[f26,f47,f47])).
% 3.49/0.92  
% 3.49/0.92  fof(f9,axiom,(
% 3.49/0.92    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f36,plain,(
% 3.49/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.49/0.92    inference(cnf_transformation,[],[f9])).
% 3.49/0.92  
% 3.49/0.92  fof(f52,plain,(
% 3.49/0.92    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 3.49/0.92    inference(definition_unfolding,[],[f36,f31,f31,f47])).
% 3.49/0.92  
% 3.49/0.92  fof(f3,axiom,(
% 3.49/0.92    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f22,plain,(
% 3.49/0.92    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.49/0.92    inference(nnf_transformation,[],[f3])).
% 3.49/0.92  
% 3.49/0.92  fof(f23,plain,(
% 3.49/0.92    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.49/0.92    inference(flattening,[],[f22])).
% 3.49/0.92  
% 3.49/0.92  fof(f28,plain,(
% 3.49/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.49/0.92    inference(cnf_transformation,[],[f23])).
% 3.49/0.92  
% 3.49/0.92  fof(f56,plain,(
% 3.49/0.92    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.49/0.92    inference(equality_resolution,[],[f28])).
% 3.49/0.92  
% 3.49/0.92  fof(f7,axiom,(
% 3.49/0.92    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f34,plain,(
% 3.49/0.92    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.49/0.92    inference(cnf_transformation,[],[f7])).
% 3.49/0.92  
% 3.49/0.92  fof(f2,axiom,(
% 3.49/0.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.49/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.92  
% 3.49/0.92  fof(f27,plain,(
% 3.49/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.49/0.92    inference(cnf_transformation,[],[f2])).
% 3.49/0.92  
% 3.49/0.92  fof(f44,plain,(
% 3.49/0.92    k2_xboole_0(k1_tarski(sK0),sK1) != sK1),
% 3.49/0.92    inference(cnf_transformation,[],[f25])).
% 3.49/0.92  
% 3.49/0.92  fof(f54,plain,(
% 3.49/0.92    k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1),
% 3.49/0.92    inference(definition_unfolding,[],[f44,f47,f48])).
% 3.49/0.92  
% 3.49/0.92  cnf(c_12,negated_conjecture,
% 3.49/0.92      ( r2_hidden(sK0,sK1) ),
% 3.49/0.92      inference(cnf_transformation,[],[f43]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_235,plain,
% 3.49/0.92      ( r2_hidden(sK0,sK1) = iProver_top ),
% 3.49/0.92      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_10,plain,
% 3.49/0.92      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 3.49/0.92      inference(cnf_transformation,[],[f53]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_236,plain,
% 3.49/0.92      ( r2_hidden(X0,X1) != iProver_top
% 3.49/0.92      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 3.49/0.92      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_6,plain,
% 3.49/0.92      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.49/0.92      inference(cnf_transformation,[],[f33]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_238,plain,
% 3.49/0.92      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.49/0.92      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_623,plain,
% 3.49/0.92      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
% 3.49/0.92      | r2_hidden(X0,X1) != iProver_top ),
% 3.49/0.92      inference(superposition,[status(thm)],[c_236,c_238]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_1406,plain,
% 3.49/0.92      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 3.49/0.92      inference(superposition,[status(thm)],[c_235,c_623]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_8,plain,
% 3.49/0.92      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 3.49/0.92      inference(cnf_transformation,[],[f51]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_1883,plain,
% 3.49/0.92      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 3.49/0.92      inference(superposition,[status(thm)],[c_1406,c_8]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_5,plain,
% 3.49/0.92      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.49/0.92      inference(cnf_transformation,[],[f50]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_0,plain,
% 3.49/0.92      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
% 3.49/0.92      inference(cnf_transformation,[],[f49]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_629,plain,
% 3.49/0.92      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.49/0.92      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_9,plain,
% 3.49/0.92      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 3.49/0.92      inference(cnf_transformation,[],[f52]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_877,plain,
% 3.49/0.92      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 3.49/0.92      inference(superposition,[status(thm)],[c_629,c_9]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_4,plain,
% 3.49/0.92      ( r1_tarski(X0,X0) ),
% 3.49/0.92      inference(cnf_transformation,[],[f56]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_239,plain,
% 3.49/0.92      ( r1_tarski(X0,X0) = iProver_top ),
% 3.49/0.92      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_471,plain,
% 3.49/0.92      ( k3_xboole_0(X0,X0) = X0 ),
% 3.49/0.92      inference(superposition,[status(thm)],[c_239,c_238]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_886,plain,
% 3.49/0.92      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
% 3.49/0.92      inference(light_normalisation,[status(thm)],[c_877,c_471]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_7,plain,
% 3.49/0.92      ( r1_tarski(k1_xboole_0,X0) ),
% 3.49/0.92      inference(cnf_transformation,[],[f34]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_237,plain,
% 3.49/0.92      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.49/0.92      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_472,plain,
% 3.49/0.92      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.49/0.92      inference(superposition,[status(thm)],[c_237,c_238]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_1216,plain,
% 3.49/0.92      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.49/0.92      inference(light_normalisation,[status(thm)],[c_886,c_472]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_881,plain,
% 3.49/0.92      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 3.49/0.92      inference(superposition,[status(thm)],[c_629,c_8]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_882,plain,
% 3.49/0.92      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.49/0.92      inference(light_normalisation,[status(thm)],[c_881,c_629]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_1,plain,
% 3.49/0.92      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.49/0.92      inference(cnf_transformation,[],[f27]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_1030,plain,
% 3.49/0.92      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.49/0.92      inference(superposition,[status(thm)],[c_472,c_1]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_1213,plain,
% 3.49/0.92      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.49/0.92      inference(light_normalisation,[status(thm)],[c_882,c_1030]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_1217,plain,
% 3.49/0.92      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.49/0.92      inference(demodulation,[status(thm)],[c_1216,c_1213]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_1888,plain,
% 3.49/0.92      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 3.49/0.92      inference(demodulation,[status(thm)],[c_1883,c_5,c_1217]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_11,negated_conjecture,
% 3.49/0.92      ( k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1 ),
% 3.49/0.92      inference(cnf_transformation,[],[f54]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(c_628,plain,
% 3.49/0.92      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 3.49/0.92      inference(demodulation,[status(thm)],[c_0,c_11]) ).
% 3.49/0.92  
% 3.49/0.92  cnf(contradiction,plain,
% 3.49/0.92      ( $false ),
% 3.49/0.92      inference(minisat,[status(thm)],[c_1888,c_628]) ).
% 3.49/0.92  
% 3.49/0.92  
% 3.49/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/0.92  
% 3.49/0.92  ------                               Statistics
% 3.49/0.92  
% 3.49/0.92  ------ Selected
% 3.49/0.92  
% 3.49/0.92  total_time:                             0.106
% 3.49/0.92  
%------------------------------------------------------------------------------
