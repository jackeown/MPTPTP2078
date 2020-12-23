%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:03 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 329 expanded)
%              Number of clauses        :   33 (  51 expanded)
%              Number of leaves         :   17 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 ( 384 expanded)
%              Number of equality atoms :   78 ( 322 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).

fof(f44,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f35,f48,f48,f31])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f32,f48])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f37,f47,f47])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f36,f31,f31,f48])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1 ),
    inference(definition_unfolding,[],[f45,f48,f49])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_234,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_235,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_237,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_616,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_235,c_237])).

cnf(c_1357,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_234,c_616])).

cnf(c_7,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1828,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_1357,c_7])).

cnf(c_4,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_622,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_4])).

cnf(c_8,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_873,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_622,c_8])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_238,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_470,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_238,c_237])).

cnf(c_880,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_873,c_470])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_236,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_471,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_236,c_237])).

cnf(c_1161,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_880,c_471])).

cnf(c_875,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_622,c_7])).

cnf(c_876,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_875,c_622])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1025,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_471,c_0])).

cnf(c_1158,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_876,c_1025])).

cnf(c_1162,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1161,c_1158])).

cnf(c_1833,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_1828,c_4,c_1162])).

cnf(c_11,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_621,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(demodulation,[status(thm)],[c_9,c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1833,c_621])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:31:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.64/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/1.00  
% 3.64/1.00  ------  iProver source info
% 3.64/1.00  
% 3.64/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.64/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/1.00  git: non_committed_changes: false
% 3.64/1.00  git: last_make_outside_of_git: false
% 3.64/1.00  
% 3.64/1.00  ------ 
% 3.64/1.00  ------ Parsing...
% 3.64/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/1.00  
% 3.64/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/1.00  ------ Proving...
% 3.64/1.00  ------ Problem Properties 
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  clauses                                 12
% 3.64/1.00  conjectures                             2
% 3.64/1.00  EPR                                     4
% 3.64/1.00  Horn                                    12
% 3.64/1.00  unary                                   9
% 3.64/1.00  binary                                  2
% 3.64/1.00  lits                                    16
% 3.64/1.00  lits eq                                 8
% 3.64/1.00  fd_pure                                 0
% 3.64/1.00  fd_pseudo                               0
% 3.64/1.00  fd_cond                                 0
% 3.64/1.00  fd_pseudo_cond                          1
% 3.64/1.00  AC symbols                              0
% 3.64/1.00  
% 3.64/1.00  ------ Input Options Time Limit: Unbounded
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ 
% 3.64/1.00  Current options:
% 3.64/1.00  ------ 
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  ------ Proving...
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  % SZS status Theorem for theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  fof(f17,conjecture,(
% 3.64/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f18,negated_conjecture,(
% 3.64/1.00    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.64/1.00    inference(negated_conjecture,[],[f17])).
% 3.64/1.00  
% 3.64/1.00  fof(f22,plain,(
% 3.64/1.00    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 3.64/1.00    inference(ennf_transformation,[],[f18])).
% 3.64/1.00  
% 3.64/1.00  fof(f25,plain,(
% 3.64/1.00    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1))),
% 3.64/1.00    introduced(choice_axiom,[])).
% 3.64/1.00  
% 3.64/1.00  fof(f26,plain,(
% 3.64/1.00    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1)),
% 3.64/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).
% 3.64/1.00  
% 3.64/1.00  fof(f44,plain,(
% 3.64/1.00    r2_hidden(sK0,sK1)),
% 3.64/1.00    inference(cnf_transformation,[],[f26])).
% 3.64/1.00  
% 3.64/1.00  fof(f15,axiom,(
% 3.64/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f19,plain,(
% 3.64/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 3.64/1.00    inference(unused_predicate_definition_removal,[],[f15])).
% 3.64/1.00  
% 3.64/1.00  fof(f21,plain,(
% 3.64/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 3.64/1.00    inference(ennf_transformation,[],[f19])).
% 3.64/1.00  
% 3.64/1.00  fof(f42,plain,(
% 3.64/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f21])).
% 3.64/1.00  
% 3.64/1.00  fof(f11,axiom,(
% 3.64/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f38,plain,(
% 3.64/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f11])).
% 3.64/1.00  
% 3.64/1.00  fof(f12,axiom,(
% 3.64/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f39,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f12])).
% 3.64/1.00  
% 3.64/1.00  fof(f13,axiom,(
% 3.64/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f40,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f13])).
% 3.64/1.00  
% 3.64/1.00  fof(f14,axiom,(
% 3.64/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f41,plain,(
% 3.64/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f14])).
% 3.64/1.00  
% 3.64/1.00  fof(f46,plain,(
% 3.64/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.64/1.00    inference(definition_unfolding,[],[f40,f41])).
% 3.64/1.00  
% 3.64/1.00  fof(f47,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.64/1.00    inference(definition_unfolding,[],[f39,f46])).
% 3.64/1.00  
% 3.64/1.00  fof(f49,plain,(
% 3.64/1.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.64/1.00    inference(definition_unfolding,[],[f38,f47])).
% 3.64/1.00  
% 3.64/1.00  fof(f54,plain,(
% 3.64/1.00    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.64/1.00    inference(definition_unfolding,[],[f42,f49])).
% 3.64/1.00  
% 3.64/1.00  fof(f5,axiom,(
% 3.64/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f20,plain,(
% 3.64/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.64/1.00    inference(ennf_transformation,[],[f5])).
% 3.64/1.00  
% 3.64/1.00  fof(f33,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f20])).
% 3.64/1.00  
% 3.64/1.00  fof(f7,axiom,(
% 3.64/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f35,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.64/1.00    inference(cnf_transformation,[],[f7])).
% 3.64/1.00  
% 3.64/1.00  fof(f16,axiom,(
% 3.64/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f43,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.64/1.00    inference(cnf_transformation,[],[f16])).
% 3.64/1.00  
% 3.64/1.00  fof(f48,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.64/1.00    inference(definition_unfolding,[],[f43,f47])).
% 3.64/1.00  
% 3.64/1.00  fof(f3,axiom,(
% 3.64/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f31,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.64/1.00    inference(cnf_transformation,[],[f3])).
% 3.64/1.00  
% 3.64/1.00  fof(f51,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.64/1.00    inference(definition_unfolding,[],[f35,f48,f48,f31])).
% 3.64/1.00  
% 3.64/1.00  fof(f4,axiom,(
% 3.64/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f32,plain,(
% 3.64/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.64/1.00    inference(cnf_transformation,[],[f4])).
% 3.64/1.00  
% 3.64/1.00  fof(f50,plain,(
% 3.64/1.00    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 3.64/1.00    inference(definition_unfolding,[],[f32,f48])).
% 3.64/1.00  
% 3.64/1.00  fof(f10,axiom,(
% 3.64/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f37,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f10])).
% 3.64/1.00  
% 3.64/1.00  fof(f53,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 3.64/1.00    inference(definition_unfolding,[],[f37,f47,f47])).
% 3.64/1.00  
% 3.64/1.00  fof(f8,axiom,(
% 3.64/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f36,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f8])).
% 3.64/1.00  
% 3.64/1.00  fof(f52,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 3.64/1.00    inference(definition_unfolding,[],[f36,f31,f31,f48])).
% 3.64/1.00  
% 3.64/1.00  fof(f2,axiom,(
% 3.64/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f23,plain,(
% 3.64/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.64/1.00    inference(nnf_transformation,[],[f2])).
% 3.64/1.00  
% 3.64/1.00  fof(f24,plain,(
% 3.64/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.64/1.00    inference(flattening,[],[f23])).
% 3.64/1.00  
% 3.64/1.00  fof(f28,plain,(
% 3.64/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.64/1.00    inference(cnf_transformation,[],[f24])).
% 3.64/1.00  
% 3.64/1.00  fof(f57,plain,(
% 3.64/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.64/1.00    inference(equality_resolution,[],[f28])).
% 3.64/1.00  
% 3.64/1.00  fof(f6,axiom,(
% 3.64/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f34,plain,(
% 3.64/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f6])).
% 3.64/1.00  
% 3.64/1.00  fof(f1,axiom,(
% 3.64/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.64/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/1.00  
% 3.64/1.00  fof(f27,plain,(
% 3.64/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.64/1.00    inference(cnf_transformation,[],[f1])).
% 3.64/1.00  
% 3.64/1.00  fof(f45,plain,(
% 3.64/1.00    k2_xboole_0(k1_tarski(sK0),sK1) != sK1),
% 3.64/1.00    inference(cnf_transformation,[],[f26])).
% 3.64/1.00  
% 3.64/1.00  fof(f55,plain,(
% 3.64/1.00    k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1),
% 3.64/1.00    inference(definition_unfolding,[],[f45,f48,f49])).
% 3.64/1.00  
% 3.64/1.00  cnf(c_12,negated_conjecture,
% 3.64/1.00      ( r2_hidden(sK0,sK1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_234,plain,
% 3.64/1.00      ( r2_hidden(sK0,sK1) = iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_10,plain,
% 3.64/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 3.64/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_235,plain,
% 3.64/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.64/1.00      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_5,plain,
% 3.64/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.64/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_237,plain,
% 3.64/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_616,plain,
% 3.64/1.00      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
% 3.64/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_235,c_237]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1357,plain,
% 3.64/1.00      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_234,c_616]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_7,plain,
% 3.64/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 3.64/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1828,plain,
% 3.64/1.00      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_1357,c_7]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_4,plain,
% 3.64/1.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.64/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_9,plain,
% 3.64/1.00      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_622,plain,
% 3.64/1.00      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_9,c_4]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_8,plain,
% 3.64/1.00      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 3.64/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_873,plain,
% 3.64/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_622,c_8]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_3,plain,
% 3.64/1.00      ( r1_tarski(X0,X0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_238,plain,
% 3.64/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_470,plain,
% 3.64/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_238,c_237]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_880,plain,
% 3.64/1.00      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_873,c_470]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_6,plain,
% 3.64/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_236,plain,
% 3.64/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.64/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_471,plain,
% 3.64/1.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_236,c_237]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1161,plain,
% 3.64/1.00      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_880,c_471]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_875,plain,
% 3.64/1.00      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_622,c_7]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_876,plain,
% 3.64/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_875,c_622]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_0,plain,
% 3.64/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.64/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1025,plain,
% 3.64/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.64/1.00      inference(superposition,[status(thm)],[c_471,c_0]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1158,plain,
% 3.64/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.64/1.00      inference(light_normalisation,[status(thm)],[c_876,c_1025]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1162,plain,
% 3.64/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.64/1.00      inference(demodulation,[status(thm)],[c_1161,c_1158]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_1833,plain,
% 3.64/1.00      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 3.64/1.00      inference(demodulation,[status(thm)],[c_1828,c_4,c_1162]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_11,negated_conjecture,
% 3.64/1.00      ( k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1 ),
% 3.64/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(c_621,plain,
% 3.64/1.00      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 3.64/1.00      inference(demodulation,[status(thm)],[c_9,c_11]) ).
% 3.64/1.00  
% 3.64/1.00  cnf(contradiction,plain,
% 3.64/1.00      ( $false ),
% 3.64/1.00      inference(minisat,[status(thm)],[c_1833,c_621]) ).
% 3.64/1.00  
% 3.64/1.00  
% 3.64/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.64/1.00  
% 3.64/1.00  ------                               Statistics
% 3.64/1.00  
% 3.64/1.00  ------ Selected
% 3.64/1.00  
% 3.64/1.00  total_time:                             0.08
% 3.64/1.00  
%------------------------------------------------------------------------------
