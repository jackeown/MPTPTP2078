%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:26 EST 2020

% Result     : Theorem 23.78s
% Output     : CNFRefutation 23.78s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 171 expanded)
%              Number of clauses        :   20 (  22 expanded)
%              Number of leaves         :   16 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 201 expanded)
%              Number of equality atoms :   57 ( 160 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f53,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f56,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k3_enumset1(k3_enumset1(X0,X1,X2,X3,X4),k3_enumset1(X0,X1,X2,X3,X4),k3_enumset1(X0,X1,X2,X3,X4),k3_enumset1(X0,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f40,f54,f56])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k3_enumset1(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4))) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k3_enumset1(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X4))) ),
    inference(definition_unfolding,[],[f38,f54,f52,f53])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f39,f52,f52])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) )
   => ( ~ r2_hidden(sK0,sK2)
      & k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r2_hidden(sK0,sK2)
    & k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).

fof(f50,plain,(
    k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f69,plain,(
    k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f50,f55,f53,f53])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f32,f55])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f51,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_10,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_0,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X4))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_41982,plain,
    ( k3_enumset1(X0,X1,X2,X3,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_9,plain,
    ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_71,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)))) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_15,c_8,c_1])).

cnf(c_40747,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_tarski(k3_enumset1(sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1))))) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_9,c_71])).

cnf(c_74382,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_41982,c_40747])).

cnf(c_4,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_73,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))),X0) ),
    inference(theory_normalisation,[status(thm)],[c_4,c_8,c_1])).

cnf(c_40180,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_76086,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_74382,c_40180])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_40184,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_76600,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_76086,c_40184])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_16,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_76600,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:27:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.78/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.78/3.50  
% 23.78/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.78/3.50  
% 23.78/3.50  ------  iProver source info
% 23.78/3.50  
% 23.78/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.78/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.78/3.50  git: non_committed_changes: false
% 23.78/3.50  git: last_make_outside_of_git: false
% 23.78/3.50  
% 23.78/3.50  ------ 
% 23.78/3.50  ------ Parsing...
% 23.78/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  ------ Proving...
% 23.78/3.50  ------ Problem Properties 
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  clauses                                 16
% 23.78/3.50  conjectures                             2
% 23.78/3.50  EPR                                     1
% 23.78/3.50  Horn                                    16
% 23.78/3.50  unary                                   13
% 23.78/3.50  binary                                  2
% 23.78/3.50  lits                                    20
% 23.78/3.50  lits eq                                 11
% 23.78/3.50  fd_pure                                 0
% 23.78/3.50  fd_pseudo                               0
% 23.78/3.50  fd_cond                                 0
% 23.78/3.50  fd_pseudo_cond                          0
% 23.78/3.50  AC symbols                              1
% 23.78/3.50  
% 23.78/3.50  ------ Input Options Time Limit: Unbounded
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing...
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 23.78/3.50  Current options:
% 23.78/3.50  ------ 
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.78/3.50  
% 23.78/3.50  ------ Proving...
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  % SZS status Theorem for theBenchmark.p
% 23.78/3.50  
% 23.78/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.78/3.50  
% 23.78/3.50  fof(f17,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f45,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f17])).
% 23.78/3.50  
% 23.78/3.50  fof(f12,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f40,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f12])).
% 23.78/3.50  
% 23.78/3.50  fof(f18,axiom,(
% 23.78/3.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f46,plain,(
% 23.78/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 23.78/3.50    inference(cnf_transformation,[],[f18])).
% 23.78/3.50  
% 23.78/3.50  fof(f54,plain,(
% 23.78/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 23.78/3.50    inference(definition_unfolding,[],[f46,f53])).
% 23.78/3.50  
% 23.78/3.50  fof(f13,axiom,(
% 23.78/3.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f41,plain,(
% 23.78/3.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f13])).
% 23.78/3.50  
% 23.78/3.50  fof(f14,axiom,(
% 23.78/3.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f42,plain,(
% 23.78/3.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f14])).
% 23.78/3.50  
% 23.78/3.50  fof(f15,axiom,(
% 23.78/3.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f43,plain,(
% 23.78/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f15])).
% 23.78/3.50  
% 23.78/3.50  fof(f16,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f44,plain,(
% 23.78/3.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f16])).
% 23.78/3.50  
% 23.78/3.50  fof(f52,plain,(
% 23.78/3.50    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f43,f44])).
% 23.78/3.50  
% 23.78/3.50  fof(f53,plain,(
% 23.78/3.50    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f42,f52])).
% 23.78/3.50  
% 23.78/3.50  fof(f56,plain,(
% 23.78/3.50    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f41,f53])).
% 23.78/3.50  
% 23.78/3.50  fof(f57,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k3_enumset1(k3_enumset1(X0,X1,X2,X3,X4),k3_enumset1(X0,X1,X2,X3,X4),k3_enumset1(X0,X1,X2,X3,X4),k3_enumset1(X0,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X5,X5)))) )),
% 23.78/3.50    inference(definition_unfolding,[],[f40,f54,f56])).
% 23.78/3.50  
% 23.78/3.50  fof(f65,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k3_enumset1(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4)))) )),
% 23.78/3.50    inference(definition_unfolding,[],[f45,f57])).
% 23.78/3.50  
% 23.78/3.50  fof(f10,axiom,(
% 23.78/3.50    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f38,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f10])).
% 23.78/3.50  
% 23.78/3.50  fof(f58,plain,(
% 23.78/3.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k3_enumset1(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X4)))) )),
% 23.78/3.50    inference(definition_unfolding,[],[f38,f54,f52,f53])).
% 23.78/3.50  
% 23.78/3.50  fof(f11,axiom,(
% 23.78/3.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f39,plain,(
% 23.78/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f11])).
% 23.78/3.50  
% 23.78/3.50  fof(f64,plain,(
% 23.78/3.50    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f39,f52,f52])).
% 23.78/3.50  
% 23.78/3.50  fof(f20,conjecture,(
% 23.78/3.50    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f21,negated_conjecture,(
% 23.78/3.50    ~! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 23.78/3.50    inference(negated_conjecture,[],[f20])).
% 23.78/3.50  
% 23.78/3.50  fof(f24,plain,(
% 23.78/3.50    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1))),
% 23.78/3.50    inference(ennf_transformation,[],[f21])).
% 23.78/3.50  
% 23.78/3.50  fof(f27,plain,(
% 23.78/3.50    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)) => (~r2_hidden(sK0,sK2) & k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1))),
% 23.78/3.50    introduced(choice_axiom,[])).
% 23.78/3.50  
% 23.78/3.50  fof(f28,plain,(
% 23.78/3.50    ~r2_hidden(sK0,sK2) & k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1)),
% 23.78/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).
% 23.78/3.50  
% 23.78/3.50  fof(f50,plain,(
% 23.78/3.50    k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1)),
% 23.78/3.50    inference(cnf_transformation,[],[f28])).
% 23.78/3.50  
% 23.78/3.50  fof(f9,axiom,(
% 23.78/3.50    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f37,plain,(
% 23.78/3.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f9])).
% 23.78/3.50  
% 23.78/3.50  fof(f55,plain,(
% 23.78/3.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f37,f54])).
% 23.78/3.50  
% 23.78/3.50  fof(f69,plain,(
% 23.78/3.50    k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))) = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 23.78/3.50    inference(definition_unfolding,[],[f50,f55,f53,f53])).
% 23.78/3.50  
% 23.78/3.50  fof(f8,axiom,(
% 23.78/3.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f36,plain,(
% 23.78/3.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f8])).
% 23.78/3.50  
% 23.78/3.50  fof(f1,axiom,(
% 23.78/3.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f29,plain,(
% 23.78/3.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f1])).
% 23.78/3.50  
% 23.78/3.50  fof(f4,axiom,(
% 23.78/3.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f32,plain,(
% 23.78/3.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f4])).
% 23.78/3.50  
% 23.78/3.50  fof(f61,plain,(
% 23.78/3.50    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),X0)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f32,f55])).
% 23.78/3.50  
% 23.78/3.50  fof(f19,axiom,(
% 23.78/3.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 23.78/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.78/3.50  
% 23.78/3.50  fof(f25,plain,(
% 23.78/3.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 23.78/3.50    inference(nnf_transformation,[],[f19])).
% 23.78/3.50  
% 23.78/3.50  fof(f26,plain,(
% 23.78/3.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 23.78/3.50    inference(flattening,[],[f25])).
% 23.78/3.50  
% 23.78/3.50  fof(f47,plain,(
% 23.78/3.50    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 23.78/3.50    inference(cnf_transformation,[],[f26])).
% 23.78/3.50  
% 23.78/3.50  fof(f68,plain,(
% 23.78/3.50    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)) )),
% 23.78/3.50    inference(definition_unfolding,[],[f47,f53])).
% 23.78/3.50  
% 23.78/3.50  fof(f51,plain,(
% 23.78/3.50    ~r2_hidden(sK0,sK2)),
% 23.78/3.50    inference(cnf_transformation,[],[f28])).
% 23.78/3.50  
% 23.78/3.50  cnf(c_10,plain,
% 23.78/3.50      ( k3_tarski(k3_enumset1(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X4,X4,X4,X4))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 23.78/3.50      inference(cnf_transformation,[],[f65]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_0,plain,
% 23.78/3.50      ( k3_tarski(k3_enumset1(k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X0,X0,X0,X1,X2),k3_enumset1(X3,X3,X3,X3,X4))) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 23.78/3.50      inference(cnf_transformation,[],[f58]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_41982,plain,
% 23.78/3.50      ( k3_enumset1(X0,X1,X2,X3,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_9,plain,
% 23.78/3.50      ( k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0) ),
% 23.78/3.50      inference(cnf_transformation,[],[f64]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_15,negated_conjecture,
% 23.78/3.50      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
% 23.78/3.50      inference(cnf_transformation,[],[f69]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_8,plain,
% 23.78/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 23.78/3.50      inference(cnf_transformation,[],[f36]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_1,plain,
% 23.78/3.50      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 23.78/3.50      inference(cnf_transformation,[],[f29]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_71,negated_conjecture,
% 23.78/3.50      ( k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)))) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
% 23.78/3.50      inference(theory_normalisation,[status(thm)],[c_15,c_8,c_1]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_40747,plain,
% 23.78/3.50      ( k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_tarski(k3_enumset1(sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1))))) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_9,c_71]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_74382,plain,
% 23.78/3.50      ( k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
% 23.78/3.50      inference(demodulation,[status(thm)],[c_41982,c_40747]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_4,plain,
% 23.78/3.50      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),X0) ),
% 23.78/3.50      inference(cnf_transformation,[],[f61]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_73,plain,
% 23.78/3.50      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))),X0) ),
% 23.78/3.50      inference(theory_normalisation,[status(thm)],[c_4,c_8,c_1]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_40180,plain,
% 23.78/3.50      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))),X0) = iProver_top ),
% 23.78/3.50      inference(predicate_to_equality,[status(thm)],[c_73]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_76086,plain,
% 23.78/3.50      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) = iProver_top ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_74382,c_40180]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_13,plain,
% 23.78/3.50      ( r2_hidden(X0,X1) | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X2),X1) ),
% 23.78/3.50      inference(cnf_transformation,[],[f68]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_40184,plain,
% 23.78/3.50      ( r2_hidden(X0,X1) = iProver_top
% 23.78/3.50      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X2),X1) != iProver_top ),
% 23.78/3.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_76600,plain,
% 23.78/3.50      ( r2_hidden(sK0,sK2) = iProver_top ),
% 23.78/3.50      inference(superposition,[status(thm)],[c_76086,c_40184]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_14,negated_conjecture,
% 23.78/3.50      ( ~ r2_hidden(sK0,sK2) ),
% 23.78/3.50      inference(cnf_transformation,[],[f51]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(c_16,plain,
% 23.78/3.50      ( r2_hidden(sK0,sK2) != iProver_top ),
% 23.78/3.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.78/3.50  
% 23.78/3.50  cnf(contradiction,plain,
% 23.78/3.50      ( $false ),
% 23.78/3.50      inference(minisat,[status(thm)],[c_76600,c_16]) ).
% 23.78/3.50  
% 23.78/3.50  
% 23.78/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.78/3.50  
% 23.78/3.50  ------                               Statistics
% 23.78/3.50  
% 23.78/3.50  ------ Selected
% 23.78/3.50  
% 23.78/3.50  total_time:                             2.705
% 23.78/3.50  
%------------------------------------------------------------------------------
