%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:41 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 132 expanded)
%              Number of clauses        :   26 (  39 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :   20
%              Number of atoms          :  201 ( 372 expanded)
%              Number of equality atoms :  156 ( 283 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
    inference(definition_unfolding,[],[f40,f47,f43,f43])).

fof(f13,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f49,f43])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) != k1_setfam_1(k2_xboole_0(X0,X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k2_tarski(X0,X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f46,f43])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f33,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f70,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f60])).

fof(f71,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f70])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f22,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f28])).

fof(f50,plain,(
    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_14,plain,
    ( k1_setfam_1(k3_tarski(k2_tarski(X0,X1))) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1511,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | k1_setfam_1(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = k3_xboole_0(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_15,c_14])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k2_tarski(X0,X0),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_126,plain,
    ( ~ r2_hidden(X0,X1)
    | X1 != X2
    | k3_xboole_0(X3,X2) != k1_xboole_0
    | k2_tarski(X0,X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_127,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_126])).

cnf(c_873,plain,
    ( k3_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_127])).

cnf(c_1377,plain,
    ( k2_tarski(X0,X0) != k1_xboole_0
    | r2_hidden(X0,k2_tarski(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_873])).

cnf(c_12,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_875,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1087,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_875])).

cnf(c_1902,plain,
    ( k2_tarski(X0,X0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1377,c_1087])).

cnf(c_2466,plain,
    ( k1_setfam_1(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = k3_xboole_0(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1511,c_1902])).

cnf(c_2471,plain,
    ( k3_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X1))) = k1_setfam_1(k2_tarski(X0,X1))
    | k2_tarski(X1,X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_2466])).

cnf(c_2506,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2471,c_15])).

cnf(c_2768,plain,
    ( k1_setfam_1(k2_tarski(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2506,c_1902])).

cnf(c_2769,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(renaming,[status(thm)],[c_2768])).

cnf(c_16,negated_conjecture,
    ( k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2772,plain,
    ( k3_xboole_0(sK1,sK2) != k3_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_2769,c_16])).

cnf(c_718,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1002,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2772,c_1002])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:04:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.73/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/0.97  
% 1.73/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.73/0.97  
% 1.73/0.97  ------  iProver source info
% 1.73/0.97  
% 1.73/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.73/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.73/0.97  git: non_committed_changes: false
% 1.73/0.97  git: last_make_outside_of_git: false
% 1.73/0.97  
% 1.73/0.97  ------ 
% 1.73/0.97  
% 1.73/0.97  ------ Input Options
% 1.73/0.97  
% 1.73/0.97  --out_options                           all
% 1.73/0.97  --tptp_safe_out                         true
% 1.73/0.97  --problem_path                          ""
% 1.73/0.97  --include_path                          ""
% 1.73/0.97  --clausifier                            res/vclausify_rel
% 1.73/0.97  --clausifier_options                    --mode clausify
% 1.73/0.97  --stdin                                 false
% 1.73/0.97  --stats_out                             all
% 1.73/0.97  
% 1.73/0.97  ------ General Options
% 1.73/0.97  
% 1.73/0.97  --fof                                   false
% 1.73/0.97  --time_out_real                         305.
% 1.73/0.97  --time_out_virtual                      -1.
% 1.73/0.97  --symbol_type_check                     false
% 1.73/0.97  --clausify_out                          false
% 1.73/0.97  --sig_cnt_out                           false
% 1.73/0.97  --trig_cnt_out                          false
% 1.73/0.97  --trig_cnt_out_tolerance                1.
% 1.73/0.97  --trig_cnt_out_sk_spl                   false
% 1.73/0.97  --abstr_cl_out                          false
% 1.73/0.97  
% 1.73/0.97  ------ Global Options
% 1.73/0.97  
% 1.73/0.97  --schedule                              default
% 1.73/0.97  --add_important_lit                     false
% 1.73/0.97  --prop_solver_per_cl                    1000
% 1.73/0.97  --min_unsat_core                        false
% 1.73/0.97  --soft_assumptions                      false
% 1.73/0.97  --soft_lemma_size                       3
% 1.73/0.97  --prop_impl_unit_size                   0
% 1.73/0.97  --prop_impl_unit                        []
% 1.73/0.97  --share_sel_clauses                     true
% 1.73/0.97  --reset_solvers                         false
% 1.73/0.97  --bc_imp_inh                            [conj_cone]
% 1.73/0.97  --conj_cone_tolerance                   3.
% 1.73/0.97  --extra_neg_conj                        none
% 1.73/0.97  --large_theory_mode                     true
% 1.73/0.97  --prolific_symb_bound                   200
% 1.73/0.97  --lt_threshold                          2000
% 1.73/0.97  --clause_weak_htbl                      true
% 1.73/0.97  --gc_record_bc_elim                     false
% 1.73/0.97  
% 1.73/0.97  ------ Preprocessing Options
% 1.73/0.97  
% 1.73/0.97  --preprocessing_flag                    true
% 1.73/0.97  --time_out_prep_mult                    0.1
% 1.73/0.97  --splitting_mode                        input
% 1.73/0.97  --splitting_grd                         true
% 1.73/0.97  --splitting_cvd                         false
% 1.73/0.97  --splitting_cvd_svl                     false
% 1.73/0.97  --splitting_nvd                         32
% 1.73/0.97  --sub_typing                            true
% 1.73/0.97  --prep_gs_sim                           true
% 1.73/0.97  --prep_unflatten                        true
% 1.73/0.97  --prep_res_sim                          true
% 1.73/0.97  --prep_upred                            true
% 1.73/0.97  --prep_sem_filter                       exhaustive
% 1.73/0.97  --prep_sem_filter_out                   false
% 1.73/0.97  --pred_elim                             true
% 1.73/0.97  --res_sim_input                         true
% 1.73/0.97  --eq_ax_congr_red                       true
% 1.73/0.97  --pure_diseq_elim                       true
% 1.73/0.97  --brand_transform                       false
% 1.73/0.97  --non_eq_to_eq                          false
% 1.73/0.97  --prep_def_merge                        true
% 1.73/0.97  --prep_def_merge_prop_impl              false
% 1.73/0.97  --prep_def_merge_mbd                    true
% 1.73/0.97  --prep_def_merge_tr_red                 false
% 1.73/0.97  --prep_def_merge_tr_cl                  false
% 1.73/0.97  --smt_preprocessing                     true
% 1.73/0.97  --smt_ac_axioms                         fast
% 1.73/0.97  --preprocessed_out                      false
% 1.73/0.97  --preprocessed_stats                    false
% 1.73/0.97  
% 1.73/0.97  ------ Abstraction refinement Options
% 1.73/0.97  
% 1.73/0.97  --abstr_ref                             []
% 1.73/0.97  --abstr_ref_prep                        false
% 1.73/0.97  --abstr_ref_until_sat                   false
% 1.73/0.97  --abstr_ref_sig_restrict                funpre
% 1.73/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/0.97  --abstr_ref_under                       []
% 1.73/0.97  
% 1.73/0.97  ------ SAT Options
% 1.73/0.97  
% 1.73/0.97  --sat_mode                              false
% 1.73/0.97  --sat_fm_restart_options                ""
% 1.73/0.97  --sat_gr_def                            false
% 1.73/0.97  --sat_epr_types                         true
% 1.73/0.97  --sat_non_cyclic_types                  false
% 1.73/0.97  --sat_finite_models                     false
% 1.73/0.97  --sat_fm_lemmas                         false
% 1.73/0.97  --sat_fm_prep                           false
% 1.73/0.97  --sat_fm_uc_incr                        true
% 1.73/0.97  --sat_out_model                         small
% 1.73/0.97  --sat_out_clauses                       false
% 1.73/0.97  
% 1.73/0.97  ------ QBF Options
% 1.73/0.97  
% 1.73/0.97  --qbf_mode                              false
% 1.73/0.97  --qbf_elim_univ                         false
% 1.73/0.97  --qbf_dom_inst                          none
% 1.73/0.97  --qbf_dom_pre_inst                      false
% 1.73/0.97  --qbf_sk_in                             false
% 1.73/0.97  --qbf_pred_elim                         true
% 1.73/0.97  --qbf_split                             512
% 1.73/0.97  
% 1.73/0.97  ------ BMC1 Options
% 1.73/0.97  
% 1.73/0.97  --bmc1_incremental                      false
% 1.73/0.97  --bmc1_axioms                           reachable_all
% 1.73/0.97  --bmc1_min_bound                        0
% 1.73/0.97  --bmc1_max_bound                        -1
% 1.73/0.97  --bmc1_max_bound_default                -1
% 1.73/0.97  --bmc1_symbol_reachability              true
% 1.73/0.97  --bmc1_property_lemmas                  false
% 1.73/0.97  --bmc1_k_induction                      false
% 1.73/0.97  --bmc1_non_equiv_states                 false
% 1.73/0.97  --bmc1_deadlock                         false
% 1.73/0.97  --bmc1_ucm                              false
% 1.73/0.97  --bmc1_add_unsat_core                   none
% 1.73/0.97  --bmc1_unsat_core_children              false
% 1.73/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/0.97  --bmc1_out_stat                         full
% 1.73/0.97  --bmc1_ground_init                      false
% 1.73/0.97  --bmc1_pre_inst_next_state              false
% 1.73/0.97  --bmc1_pre_inst_state                   false
% 1.73/0.97  --bmc1_pre_inst_reach_state             false
% 1.73/0.97  --bmc1_out_unsat_core                   false
% 1.73/0.97  --bmc1_aig_witness_out                  false
% 1.73/0.97  --bmc1_verbose                          false
% 1.73/0.97  --bmc1_dump_clauses_tptp                false
% 1.73/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.73/0.97  --bmc1_dump_file                        -
% 1.73/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.73/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.73/0.97  --bmc1_ucm_extend_mode                  1
% 1.73/0.97  --bmc1_ucm_init_mode                    2
% 1.73/0.97  --bmc1_ucm_cone_mode                    none
% 1.73/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.73/0.97  --bmc1_ucm_relax_model                  4
% 1.73/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.73/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/0.97  --bmc1_ucm_layered_model                none
% 1.73/0.97  --bmc1_ucm_max_lemma_size               10
% 1.73/0.97  
% 1.73/0.97  ------ AIG Options
% 1.73/0.97  
% 1.73/0.97  --aig_mode                              false
% 1.73/0.97  
% 1.73/0.97  ------ Instantiation Options
% 1.73/0.97  
% 1.73/0.97  --instantiation_flag                    true
% 1.73/0.97  --inst_sos_flag                         false
% 1.73/0.97  --inst_sos_phase                        true
% 1.73/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/0.97  --inst_lit_sel_side                     num_symb
% 1.73/0.97  --inst_solver_per_active                1400
% 1.73/0.97  --inst_solver_calls_frac                1.
% 1.73/0.97  --inst_passive_queue_type               priority_queues
% 1.73/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/0.97  --inst_passive_queues_freq              [25;2]
% 1.73/0.97  --inst_dismatching                      true
% 1.73/0.97  --inst_eager_unprocessed_to_passive     true
% 1.73/0.97  --inst_prop_sim_given                   true
% 1.73/0.97  --inst_prop_sim_new                     false
% 1.73/0.97  --inst_subs_new                         false
% 1.73/0.97  --inst_eq_res_simp                      false
% 1.73/0.97  --inst_subs_given                       false
% 1.73/0.97  --inst_orphan_elimination               true
% 1.73/0.97  --inst_learning_loop_flag               true
% 1.73/0.97  --inst_learning_start                   3000
% 1.73/0.97  --inst_learning_factor                  2
% 1.73/0.97  --inst_start_prop_sim_after_learn       3
% 1.73/0.97  --inst_sel_renew                        solver
% 1.73/0.97  --inst_lit_activity_flag                true
% 1.73/0.97  --inst_restr_to_given                   false
% 1.73/0.97  --inst_activity_threshold               500
% 1.73/0.97  --inst_out_proof                        true
% 1.73/0.97  
% 1.73/0.97  ------ Resolution Options
% 1.73/0.97  
% 1.73/0.97  --resolution_flag                       true
% 1.73/0.97  --res_lit_sel                           adaptive
% 1.73/0.97  --res_lit_sel_side                      none
% 1.73/0.97  --res_ordering                          kbo
% 1.73/0.97  --res_to_prop_solver                    active
% 1.73/0.97  --res_prop_simpl_new                    false
% 1.73/0.97  --res_prop_simpl_given                  true
% 1.73/0.97  --res_passive_queue_type                priority_queues
% 1.73/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/0.97  --res_passive_queues_freq               [15;5]
% 1.73/0.97  --res_forward_subs                      full
% 1.73/0.97  --res_backward_subs                     full
% 1.73/0.97  --res_forward_subs_resolution           true
% 1.73/0.97  --res_backward_subs_resolution          true
% 1.73/0.97  --res_orphan_elimination                true
% 1.73/0.97  --res_time_limit                        2.
% 1.73/0.97  --res_out_proof                         true
% 1.73/0.97  
% 1.73/0.97  ------ Superposition Options
% 1.73/0.97  
% 1.73/0.97  --superposition_flag                    true
% 1.73/0.97  --sup_passive_queue_type                priority_queues
% 1.73/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.73/0.97  --demod_completeness_check              fast
% 1.73/0.97  --demod_use_ground                      true
% 1.73/0.97  --sup_to_prop_solver                    passive
% 1.73/0.97  --sup_prop_simpl_new                    true
% 1.73/0.97  --sup_prop_simpl_given                  true
% 1.73/0.97  --sup_fun_splitting                     false
% 1.73/0.97  --sup_smt_interval                      50000
% 1.73/0.97  
% 1.73/0.97  ------ Superposition Simplification Setup
% 1.73/0.97  
% 1.73/0.97  --sup_indices_passive                   []
% 1.73/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.97  --sup_full_bw                           [BwDemod]
% 1.73/0.97  --sup_immed_triv                        [TrivRules]
% 1.73/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.97  --sup_immed_bw_main                     []
% 1.73/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/0.97  
% 1.73/0.97  ------ Combination Options
% 1.73/0.97  
% 1.73/0.97  --comb_res_mult                         3
% 1.73/0.97  --comb_sup_mult                         2
% 1.73/0.97  --comb_inst_mult                        10
% 1.73/0.97  
% 1.73/0.97  ------ Debug Options
% 1.73/0.97  
% 1.73/0.97  --dbg_backtrace                         false
% 1.73/0.97  --dbg_dump_prop_clauses                 false
% 1.73/0.97  --dbg_dump_prop_clauses_file            -
% 1.73/0.97  --dbg_out_stat                          false
% 1.73/0.97  ------ Parsing...
% 1.73/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.73/0.97  
% 1.73/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.73/0.97  
% 1.73/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.73/0.97  
% 1.73/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.73/0.97  ------ Proving...
% 1.73/0.97  ------ Problem Properties 
% 1.73/0.97  
% 1.73/0.97  
% 1.73/0.97  clauses                                 16
% 1.73/0.97  conjectures                             1
% 1.73/0.97  EPR                                     0
% 1.73/0.97  Horn                                    13
% 1.73/0.97  unary                                   9
% 1.73/0.97  binary                                  1
% 1.73/0.97  lits                                    32
% 1.73/0.97  lits eq                                 23
% 1.73/0.97  fd_pure                                 0
% 1.73/0.97  fd_pseudo                               0
% 1.73/0.97  fd_cond                                 1
% 1.73/0.97  fd_pseudo_cond                          4
% 1.73/0.97  AC symbols                              0
% 1.73/0.97  
% 1.73/0.97  ------ Schedule dynamic 5 is on 
% 1.73/0.97  
% 1.73/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.73/0.97  
% 1.73/0.97  
% 1.73/0.97  ------ 
% 1.73/0.97  Current options:
% 1.73/0.97  ------ 
% 1.73/0.97  
% 1.73/0.97  ------ Input Options
% 1.73/0.97  
% 1.73/0.97  --out_options                           all
% 1.73/0.97  --tptp_safe_out                         true
% 1.73/0.97  --problem_path                          ""
% 1.73/0.97  --include_path                          ""
% 1.73/0.97  --clausifier                            res/vclausify_rel
% 1.73/0.97  --clausifier_options                    --mode clausify
% 1.73/0.97  --stdin                                 false
% 1.73/0.97  --stats_out                             all
% 1.73/0.97  
% 1.73/0.97  ------ General Options
% 1.73/0.97  
% 1.73/0.97  --fof                                   false
% 1.73/0.97  --time_out_real                         305.
% 1.73/0.97  --time_out_virtual                      -1.
% 1.73/0.97  --symbol_type_check                     false
% 1.73/0.97  --clausify_out                          false
% 1.73/0.97  --sig_cnt_out                           false
% 1.73/0.97  --trig_cnt_out                          false
% 1.73/0.97  --trig_cnt_out_tolerance                1.
% 1.73/0.97  --trig_cnt_out_sk_spl                   false
% 1.73/0.97  --abstr_cl_out                          false
% 1.73/0.97  
% 1.73/0.97  ------ Global Options
% 1.73/0.97  
% 1.73/0.97  --schedule                              default
% 1.73/0.97  --add_important_lit                     false
% 1.73/0.97  --prop_solver_per_cl                    1000
% 1.73/0.97  --min_unsat_core                        false
% 1.73/0.97  --soft_assumptions                      false
% 1.73/0.97  --soft_lemma_size                       3
% 1.73/0.97  --prop_impl_unit_size                   0
% 1.73/0.97  --prop_impl_unit                        []
% 1.73/0.97  --share_sel_clauses                     true
% 1.73/0.97  --reset_solvers                         false
% 1.73/0.97  --bc_imp_inh                            [conj_cone]
% 1.73/0.97  --conj_cone_tolerance                   3.
% 1.73/0.97  --extra_neg_conj                        none
% 1.73/0.97  --large_theory_mode                     true
% 1.73/0.97  --prolific_symb_bound                   200
% 1.73/0.97  --lt_threshold                          2000
% 1.73/0.97  --clause_weak_htbl                      true
% 1.73/0.97  --gc_record_bc_elim                     false
% 1.73/0.97  
% 1.73/0.97  ------ Preprocessing Options
% 1.73/0.97  
% 1.73/0.97  --preprocessing_flag                    true
% 1.73/0.97  --time_out_prep_mult                    0.1
% 1.73/0.97  --splitting_mode                        input
% 1.73/0.97  --splitting_grd                         true
% 1.73/0.97  --splitting_cvd                         false
% 1.73/0.97  --splitting_cvd_svl                     false
% 1.73/0.97  --splitting_nvd                         32
% 1.73/0.97  --sub_typing                            true
% 1.73/0.97  --prep_gs_sim                           true
% 1.73/0.97  --prep_unflatten                        true
% 1.73/0.97  --prep_res_sim                          true
% 1.73/0.97  --prep_upred                            true
% 1.73/0.97  --prep_sem_filter                       exhaustive
% 1.73/0.97  --prep_sem_filter_out                   false
% 1.73/0.97  --pred_elim                             true
% 1.73/0.97  --res_sim_input                         true
% 1.73/0.97  --eq_ax_congr_red                       true
% 1.73/0.97  --pure_diseq_elim                       true
% 1.73/0.97  --brand_transform                       false
% 1.73/0.97  --non_eq_to_eq                          false
% 1.73/0.97  --prep_def_merge                        true
% 1.73/0.97  --prep_def_merge_prop_impl              false
% 1.73/0.97  --prep_def_merge_mbd                    true
% 1.73/0.97  --prep_def_merge_tr_red                 false
% 1.73/0.97  --prep_def_merge_tr_cl                  false
% 1.73/0.97  --smt_preprocessing                     true
% 1.73/0.97  --smt_ac_axioms                         fast
% 1.73/0.97  --preprocessed_out                      false
% 1.73/0.97  --preprocessed_stats                    false
% 1.73/0.97  
% 1.73/0.97  ------ Abstraction refinement Options
% 1.73/0.97  
% 1.73/0.97  --abstr_ref                             []
% 1.73/0.97  --abstr_ref_prep                        false
% 1.73/0.97  --abstr_ref_until_sat                   false
% 1.73/0.97  --abstr_ref_sig_restrict                funpre
% 1.73/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/0.97  --abstr_ref_under                       []
% 1.73/0.97  
% 1.73/0.97  ------ SAT Options
% 1.73/0.97  
% 1.73/0.97  --sat_mode                              false
% 1.73/0.97  --sat_fm_restart_options                ""
% 1.73/0.97  --sat_gr_def                            false
% 1.73/0.97  --sat_epr_types                         true
% 1.73/0.97  --sat_non_cyclic_types                  false
% 1.73/0.97  --sat_finite_models                     false
% 1.73/0.97  --sat_fm_lemmas                         false
% 1.73/0.97  --sat_fm_prep                           false
% 1.73/0.97  --sat_fm_uc_incr                        true
% 1.73/0.97  --sat_out_model                         small
% 1.73/0.97  --sat_out_clauses                       false
% 1.73/0.97  
% 1.73/0.97  ------ QBF Options
% 1.73/0.97  
% 1.73/0.97  --qbf_mode                              false
% 1.73/0.97  --qbf_elim_univ                         false
% 1.73/0.97  --qbf_dom_inst                          none
% 1.73/0.97  --qbf_dom_pre_inst                      false
% 1.73/0.97  --qbf_sk_in                             false
% 1.73/0.97  --qbf_pred_elim                         true
% 1.73/0.97  --qbf_split                             512
% 1.73/0.97  
% 1.73/0.97  ------ BMC1 Options
% 1.73/0.97  
% 1.73/0.97  --bmc1_incremental                      false
% 1.73/0.97  --bmc1_axioms                           reachable_all
% 1.73/0.97  --bmc1_min_bound                        0
% 1.73/0.97  --bmc1_max_bound                        -1
% 1.73/0.97  --bmc1_max_bound_default                -1
% 1.73/0.97  --bmc1_symbol_reachability              true
% 1.73/0.97  --bmc1_property_lemmas                  false
% 1.73/0.97  --bmc1_k_induction                      false
% 1.73/0.97  --bmc1_non_equiv_states                 false
% 1.73/0.97  --bmc1_deadlock                         false
% 1.73/0.97  --bmc1_ucm                              false
% 1.73/0.97  --bmc1_add_unsat_core                   none
% 1.73/0.97  --bmc1_unsat_core_children              false
% 1.73/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/0.97  --bmc1_out_stat                         full
% 1.73/0.97  --bmc1_ground_init                      false
% 1.73/0.97  --bmc1_pre_inst_next_state              false
% 1.73/0.97  --bmc1_pre_inst_state                   false
% 1.73/0.97  --bmc1_pre_inst_reach_state             false
% 1.73/0.97  --bmc1_out_unsat_core                   false
% 1.73/0.97  --bmc1_aig_witness_out                  false
% 1.73/0.97  --bmc1_verbose                          false
% 1.73/0.97  --bmc1_dump_clauses_tptp                false
% 1.73/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.73/0.97  --bmc1_dump_file                        -
% 1.73/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.73/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.73/0.97  --bmc1_ucm_extend_mode                  1
% 1.73/0.97  --bmc1_ucm_init_mode                    2
% 1.73/0.97  --bmc1_ucm_cone_mode                    none
% 1.73/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.73/0.97  --bmc1_ucm_relax_model                  4
% 1.73/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.73/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/0.97  --bmc1_ucm_layered_model                none
% 1.73/0.97  --bmc1_ucm_max_lemma_size               10
% 1.73/0.97  
% 1.73/0.97  ------ AIG Options
% 1.73/0.97  
% 1.73/0.97  --aig_mode                              false
% 1.73/0.97  
% 1.73/0.97  ------ Instantiation Options
% 1.73/0.97  
% 1.73/0.97  --instantiation_flag                    true
% 1.73/0.97  --inst_sos_flag                         false
% 1.73/0.97  --inst_sos_phase                        true
% 1.73/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/0.97  --inst_lit_sel_side                     none
% 1.73/0.97  --inst_solver_per_active                1400
% 1.73/0.97  --inst_solver_calls_frac                1.
% 1.73/0.97  --inst_passive_queue_type               priority_queues
% 1.73/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/0.97  --inst_passive_queues_freq              [25;2]
% 1.73/0.97  --inst_dismatching                      true
% 1.73/0.97  --inst_eager_unprocessed_to_passive     true
% 1.73/0.97  --inst_prop_sim_given                   true
% 1.73/0.97  --inst_prop_sim_new                     false
% 1.73/0.97  --inst_subs_new                         false
% 1.73/0.97  --inst_eq_res_simp                      false
% 1.73/0.97  --inst_subs_given                       false
% 1.73/0.97  --inst_orphan_elimination               true
% 1.73/0.97  --inst_learning_loop_flag               true
% 1.73/0.97  --inst_learning_start                   3000
% 1.73/0.97  --inst_learning_factor                  2
% 1.73/0.97  --inst_start_prop_sim_after_learn       3
% 1.73/0.97  --inst_sel_renew                        solver
% 1.73/0.97  --inst_lit_activity_flag                true
% 1.73/0.97  --inst_restr_to_given                   false
% 1.73/0.97  --inst_activity_threshold               500
% 1.73/0.97  --inst_out_proof                        true
% 1.73/0.97  
% 1.73/0.97  ------ Resolution Options
% 1.73/0.97  
% 1.73/0.97  --resolution_flag                       false
% 1.73/0.97  --res_lit_sel                           adaptive
% 1.73/0.97  --res_lit_sel_side                      none
% 1.73/0.97  --res_ordering                          kbo
% 1.73/0.97  --res_to_prop_solver                    active
% 1.73/0.97  --res_prop_simpl_new                    false
% 1.73/0.97  --res_prop_simpl_given                  true
% 1.73/0.97  --res_passive_queue_type                priority_queues
% 1.73/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/0.97  --res_passive_queues_freq               [15;5]
% 1.73/0.97  --res_forward_subs                      full
% 1.73/0.97  --res_backward_subs                     full
% 1.73/0.97  --res_forward_subs_resolution           true
% 1.73/0.97  --res_backward_subs_resolution          true
% 1.73/0.97  --res_orphan_elimination                true
% 1.73/0.97  --res_time_limit                        2.
% 1.73/0.97  --res_out_proof                         true
% 1.73/0.97  
% 1.73/0.97  ------ Superposition Options
% 1.73/0.97  
% 1.73/0.97  --superposition_flag                    true
% 1.73/0.97  --sup_passive_queue_type                priority_queues
% 1.73/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.73/0.97  --demod_completeness_check              fast
% 1.73/0.97  --demod_use_ground                      true
% 1.73/0.97  --sup_to_prop_solver                    passive
% 1.73/0.97  --sup_prop_simpl_new                    true
% 1.73/0.97  --sup_prop_simpl_given                  true
% 1.73/0.97  --sup_fun_splitting                     false
% 1.73/0.97  --sup_smt_interval                      50000
% 1.73/0.97  
% 1.73/0.97  ------ Superposition Simplification Setup
% 1.73/0.97  
% 1.73/0.97  --sup_indices_passive                   []
% 1.73/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.97  --sup_full_bw                           [BwDemod]
% 1.73/0.97  --sup_immed_triv                        [TrivRules]
% 1.73/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.97  --sup_immed_bw_main                     []
% 1.73/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/0.97  
% 1.73/0.97  ------ Combination Options
% 1.73/0.97  
% 1.73/0.97  --comb_res_mult                         3
% 1.73/0.97  --comb_sup_mult                         2
% 1.73/0.97  --comb_inst_mult                        10
% 1.73/0.97  
% 1.73/0.97  ------ Debug Options
% 1.73/0.97  
% 1.73/0.97  --dbg_backtrace                         false
% 1.73/0.97  --dbg_dump_prop_clauses                 false
% 1.73/0.97  --dbg_dump_prop_clauses_file            -
% 1.73/0.97  --dbg_out_stat                          false
% 1.73/0.97  
% 1.73/0.97  
% 1.73/0.97  
% 1.73/0.97  
% 1.73/0.97  ------ Proving...
% 1.73/0.97  
% 1.73/0.97  
% 1.73/0.97  % SZS status Theorem for theBenchmark.p
% 1.73/0.97  
% 1.73/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.73/0.97  
% 1.73/0.97  fof(f4,axiom,(
% 1.73/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.73/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.97  
% 1.73/0.97  fof(f40,plain,(
% 1.73/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.73/0.97    inference(cnf_transformation,[],[f4])).
% 1.73/0.97  
% 1.73/0.97  fof(f11,axiom,(
% 1.73/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.73/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.97  
% 1.73/0.97  fof(f47,plain,(
% 1.73/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.73/0.97    inference(cnf_transformation,[],[f11])).
% 1.73/0.97  
% 1.73/0.97  fof(f7,axiom,(
% 1.73/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.73/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.97  
% 1.73/0.97  fof(f43,plain,(
% 1.73/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.73/0.97    inference(cnf_transformation,[],[f7])).
% 1.73/0.97  
% 1.73/0.97  fof(f52,plain,(
% 1.73/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 1.73/0.97    inference(definition_unfolding,[],[f40,f47,f43,f43])).
% 1.73/0.97  
% 1.73/0.97  fof(f13,axiom,(
% 1.73/0.97    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.73/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.97  
% 1.73/0.97  fof(f49,plain,(
% 1.73/0.97    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.73/0.97    inference(cnf_transformation,[],[f13])).
% 1.73/0.97  
% 1.73/0.97  fof(f65,plain,(
% 1.73/0.97    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 1.73/0.97    inference(definition_unfolding,[],[f49,f43])).
% 1.73/0.97  
% 1.73/0.97  fof(f12,axiom,(
% 1.73/0.97    ! [X0,X1] : ~(k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) != k1_setfam_1(k2_xboole_0(X0,X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.73/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.97  
% 1.73/0.97  fof(f21,plain,(
% 1.73/0.97    ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.73/0.97    inference(ennf_transformation,[],[f12])).
% 1.73/0.97  
% 1.73/0.97  fof(f48,plain,(
% 1.73/0.97    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.73/0.97    inference(cnf_transformation,[],[f21])).
% 1.73/0.97  
% 1.73/0.97  fof(f64,plain,(
% 1.73/0.97    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k2_tarski(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.73/0.97    inference(definition_unfolding,[],[f48,f47])).
% 1.73/0.97  
% 1.73/0.97  fof(f2,axiom,(
% 1.73/0.97    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.73/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.97  
% 1.73/0.97  fof(f16,plain,(
% 1.73/0.97    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.73/0.97    inference(rectify,[],[f2])).
% 1.73/0.97  
% 1.73/0.97  fof(f31,plain,(
% 1.73/0.97    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.73/0.97    inference(cnf_transformation,[],[f16])).
% 1.73/0.97  
% 1.73/0.97  fof(f1,axiom,(
% 1.73/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.73/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.97  
% 1.73/0.97  fof(f17,plain,(
% 1.73/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 1.73/0.97    inference(unused_predicate_definition_removal,[],[f1])).
% 1.73/0.97  
% 1.73/0.97  fof(f18,plain,(
% 1.73/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 1.73/0.97    inference(ennf_transformation,[],[f17])).
% 1.73/0.97  
% 1.73/0.97  fof(f30,plain,(
% 1.73/0.97    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.73/0.97    inference(cnf_transformation,[],[f18])).
% 1.73/0.97  
% 1.73/0.97  fof(f10,axiom,(
% 1.73/0.97    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.73/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.97  
% 1.73/0.97  fof(f20,plain,(
% 1.73/0.97    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.73/0.97    inference(ennf_transformation,[],[f10])).
% 1.73/0.97  
% 1.73/0.97  fof(f46,plain,(
% 1.73/0.97    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.73/0.97    inference(cnf_transformation,[],[f20])).
% 1.73/0.97  
% 1.73/0.97  fof(f63,plain,(
% 1.73/0.97    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k2_tarski(X0,X0),X1)) )),
% 1.73/0.97    inference(definition_unfolding,[],[f46,f43])).
% 1.73/0.97  
% 1.73/0.97  fof(f8,axiom,(
% 1.73/0.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.73/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.97  
% 1.73/0.97  fof(f44,plain,(
% 1.73/0.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.73/0.97    inference(cnf_transformation,[],[f8])).
% 1.73/0.97  
% 1.73/0.97  fof(f9,axiom,(
% 1.73/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.73/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.97  
% 1.73/0.97  fof(f45,plain,(
% 1.73/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.73/0.97    inference(cnf_transformation,[],[f9])).
% 1.73/0.97  
% 1.73/0.97  fof(f62,plain,(
% 1.73/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.73/0.97    inference(definition_unfolding,[],[f44,f45])).
% 1.73/0.97  
% 1.73/0.97  fof(f3,axiom,(
% 1.73/0.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.73/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.97  
% 1.73/0.97  fof(f19,plain,(
% 1.73/0.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.73/0.97    inference(ennf_transformation,[],[f3])).
% 1.73/0.97  
% 1.73/0.97  fof(f23,plain,(
% 1.73/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.73/0.97    inference(nnf_transformation,[],[f19])).
% 1.73/0.97  
% 1.73/0.97  fof(f24,plain,(
% 1.73/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.73/0.97    inference(flattening,[],[f23])).
% 1.73/0.97  
% 1.73/0.97  fof(f25,plain,(
% 1.73/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.73/0.97    inference(rectify,[],[f24])).
% 1.73/0.97  
% 1.73/0.97  fof(f26,plain,(
% 1.73/0.97    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 1.73/0.97    introduced(choice_axiom,[])).
% 1.73/0.97  
% 1.73/0.97  fof(f27,plain,(
% 1.73/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.73/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 1.73/0.97  
% 1.73/0.97  fof(f33,plain,(
% 1.73/0.97    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.73/0.97    inference(cnf_transformation,[],[f27])).
% 1.73/0.97  
% 1.73/0.97  fof(f60,plain,(
% 1.73/0.97    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.73/0.97    inference(definition_unfolding,[],[f33,f45])).
% 1.73/0.97  
% 1.73/0.97  fof(f70,plain,(
% 1.73/0.97    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 1.73/0.97    inference(equality_resolution,[],[f60])).
% 1.73/0.97  
% 1.73/0.97  fof(f71,plain,(
% 1.73/0.97    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 1.73/0.97    inference(equality_resolution,[],[f70])).
% 1.73/0.97  
% 1.73/0.97  fof(f14,conjecture,(
% 1.73/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.73/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.73/0.97  
% 1.73/0.97  fof(f15,negated_conjecture,(
% 1.73/0.97    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.73/0.97    inference(negated_conjecture,[],[f14])).
% 1.73/0.97  
% 1.73/0.97  fof(f22,plain,(
% 1.73/0.97    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 1.73/0.97    inference(ennf_transformation,[],[f15])).
% 1.73/0.97  
% 1.73/0.97  fof(f28,plain,(
% 1.73/0.97    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))),
% 1.73/0.97    introduced(choice_axiom,[])).
% 1.73/0.97  
% 1.73/0.97  fof(f29,plain,(
% 1.73/0.97    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))),
% 1.73/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f28])).
% 1.73/0.97  
% 1.73/0.97  fof(f50,plain,(
% 1.73/0.97    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))),
% 1.73/0.97    inference(cnf_transformation,[],[f29])).
% 1.73/0.97  
% 1.73/0.97  cnf(c_0,plain,
% 1.73/0.97      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
% 1.73/0.97      inference(cnf_transformation,[],[f52]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_15,plain,
% 1.73/0.97      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 1.73/0.97      inference(cnf_transformation,[],[f65]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_14,plain,
% 1.73/0.97      ( k1_setfam_1(k3_tarski(k2_tarski(X0,X1))) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
% 1.73/0.97      | k1_xboole_0 = X1
% 1.73/0.97      | k1_xboole_0 = X0 ),
% 1.73/0.97      inference(cnf_transformation,[],[f64]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_1511,plain,
% 1.73/0.97      ( k2_tarski(X0,X0) = k1_xboole_0
% 1.73/0.97      | k1_setfam_1(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = k3_xboole_0(X0,k1_setfam_1(X1))
% 1.73/0.97      | k1_xboole_0 = X1 ),
% 1.73/0.97      inference(superposition,[status(thm)],[c_15,c_14]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_3,plain,
% 1.73/0.97      ( k3_xboole_0(X0,X0) = X0 ),
% 1.73/0.97      inference(cnf_transformation,[],[f31]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_2,plain,
% 1.73/0.97      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 1.73/0.97      inference(cnf_transformation,[],[f30]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_13,plain,
% 1.73/0.97      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k2_tarski(X0,X0),X1) ),
% 1.73/0.97      inference(cnf_transformation,[],[f63]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_126,plain,
% 1.73/0.97      ( ~ r2_hidden(X0,X1)
% 1.73/0.97      | X1 != X2
% 1.73/0.97      | k3_xboole_0(X3,X2) != k1_xboole_0
% 1.73/0.97      | k2_tarski(X0,X0) != X3 ),
% 1.73/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_127,plain,
% 1.73/0.97      ( ~ r2_hidden(X0,X1)
% 1.73/0.97      | k3_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0 ),
% 1.73/0.97      inference(unflattening,[status(thm)],[c_126]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_873,plain,
% 1.73/0.97      ( k3_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0
% 1.73/0.97      | r2_hidden(X0,X1) != iProver_top ),
% 1.73/0.97      inference(predicate_to_equality,[status(thm)],[c_127]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_1377,plain,
% 1.73/0.97      ( k2_tarski(X0,X0) != k1_xboole_0
% 1.73/0.97      | r2_hidden(X0,k2_tarski(X0,X0)) != iProver_top ),
% 1.73/0.97      inference(superposition,[status(thm)],[c_3,c_873]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_12,plain,
% 1.73/0.97      ( k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 1.73/0.97      inference(cnf_transformation,[],[f62]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_10,plain,
% 1.73/0.97      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 1.73/0.97      inference(cnf_transformation,[],[f71]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_875,plain,
% 1.73/0.97      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 1.73/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_1087,plain,
% 1.73/0.97      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 1.73/0.97      inference(superposition,[status(thm)],[c_12,c_875]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_1902,plain,
% 1.73/0.97      ( k2_tarski(X0,X0) != k1_xboole_0 ),
% 1.73/0.97      inference(forward_subsumption_resolution,
% 1.73/0.97                [status(thm)],
% 1.73/0.97                [c_1377,c_1087]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_2466,plain,
% 1.73/0.97      ( k1_setfam_1(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) = k3_xboole_0(X0,k1_setfam_1(X1))
% 1.73/0.97      | k1_xboole_0 = X1 ),
% 1.73/0.97      inference(global_propositional_subsumption,
% 1.73/0.97                [status(thm)],
% 1.73/0.97                [c_1511,c_1902]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_2471,plain,
% 1.73/0.97      ( k3_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X1))) = k1_setfam_1(k2_tarski(X0,X1))
% 1.73/0.97      | k2_tarski(X1,X1) = k1_xboole_0 ),
% 1.73/0.97      inference(superposition,[status(thm)],[c_0,c_2466]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_2506,plain,
% 1.73/0.97      ( k2_tarski(X0,X0) = k1_xboole_0
% 1.73/0.97      | k1_setfam_1(k2_tarski(X1,X0)) = k3_xboole_0(X1,X0) ),
% 1.73/0.97      inference(demodulation,[status(thm)],[c_2471,c_15]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_2768,plain,
% 1.73/0.97      ( k1_setfam_1(k2_tarski(X1,X0)) = k3_xboole_0(X1,X0) ),
% 1.73/0.97      inference(global_propositional_subsumption,
% 1.73/0.97                [status(thm)],
% 1.73/0.97                [c_2506,c_1902]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_2769,plain,
% 1.73/0.97      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
% 1.73/0.97      inference(renaming,[status(thm)],[c_2768]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_16,negated_conjecture,
% 1.73/0.97      ( k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 1.73/0.97      inference(cnf_transformation,[],[f50]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_2772,plain,
% 1.73/0.97      ( k3_xboole_0(sK1,sK2) != k3_xboole_0(sK1,sK2) ),
% 1.73/0.97      inference(demodulation,[status(thm)],[c_2769,c_16]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_718,plain,( X0 = X0 ),theory(equality) ).
% 1.73/0.97  
% 1.73/0.97  cnf(c_1002,plain,
% 1.73/0.97      ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,sK2) ),
% 1.73/0.97      inference(instantiation,[status(thm)],[c_718]) ).
% 1.73/0.97  
% 1.73/0.97  cnf(contradiction,plain,
% 1.73/0.97      ( $false ),
% 1.73/0.97      inference(minisat,[status(thm)],[c_2772,c_1002]) ).
% 1.73/0.97  
% 1.73/0.97  
% 1.73/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.73/0.97  
% 1.73/0.97  ------                               Statistics
% 1.73/0.97  
% 1.73/0.97  ------ General
% 1.73/0.97  
% 1.73/0.97  abstr_ref_over_cycles:                  0
% 1.73/0.97  abstr_ref_under_cycles:                 0
% 1.73/0.97  gc_basic_clause_elim:                   0
% 1.73/0.97  forced_gc_time:                         0
% 1.73/0.97  parsing_time:                           0.008
% 1.73/0.97  unif_index_cands_time:                  0.
% 1.73/0.97  unif_index_add_time:                    0.
% 1.73/0.97  orderings_time:                         0.
% 1.73/0.97  out_proof_time:                         0.005
% 1.73/0.97  total_time:                             0.106
% 1.73/0.97  num_of_symbols:                         42
% 1.73/0.97  num_of_terms:                           4161
% 1.73/0.97  
% 1.73/0.97  ------ Preprocessing
% 1.73/0.97  
% 1.73/0.97  num_of_splits:                          0
% 1.73/0.97  num_of_split_atoms:                     0
% 1.73/0.97  num_of_reused_defs:                     0
% 1.73/0.97  num_eq_ax_congr_red:                    25
% 1.73/0.97  num_of_sem_filtered_clauses:            1
% 1.73/0.97  num_of_subtypes:                        0
% 1.73/0.97  monotx_restored_types:                  0
% 1.73/0.97  sat_num_of_epr_types:                   0
% 1.73/0.97  sat_num_of_non_cyclic_types:            0
% 1.73/0.97  sat_guarded_non_collapsed_types:        0
% 1.73/0.97  num_pure_diseq_elim:                    0
% 1.73/0.97  simp_replaced_by:                       0
% 1.73/0.97  res_preprocessed:                       80
% 1.73/0.97  prep_upred:                             0
% 1.73/0.97  prep_unflattend:                        46
% 1.73/0.97  smt_new_axioms:                         0
% 1.73/0.97  pred_elim_cands:                        1
% 1.73/0.97  pred_elim:                              1
% 1.73/0.97  pred_elim_cl:                           1
% 1.73/0.97  pred_elim_cycles:                       3
% 1.73/0.97  merged_defs:                            0
% 1.73/0.97  merged_defs_ncl:                        0
% 1.73/0.97  bin_hyper_res:                          0
% 1.73/0.97  prep_cycles:                            4
% 1.73/0.97  pred_elim_time:                         0.008
% 1.73/0.97  splitting_time:                         0.
% 1.73/0.97  sem_filter_time:                        0.
% 1.73/0.97  monotx_time:                            0.001
% 1.73/0.97  subtype_inf_time:                       0.
% 1.73/0.97  
% 1.73/0.97  ------ Problem properties
% 1.73/0.97  
% 1.73/0.97  clauses:                                16
% 1.73/0.97  conjectures:                            1
% 1.73/0.97  epr:                                    0
% 1.73/0.97  horn:                                   13
% 1.73/0.97  ground:                                 1
% 1.73/0.97  unary:                                  9
% 1.73/0.97  binary:                                 1
% 1.73/0.97  lits:                                   32
% 1.73/0.97  lits_eq:                                23
% 1.73/0.97  fd_pure:                                0
% 1.73/0.97  fd_pseudo:                              0
% 1.73/0.97  fd_cond:                                1
% 1.73/0.97  fd_pseudo_cond:                         4
% 1.73/0.97  ac_symbols:                             0
% 1.73/0.97  
% 1.73/0.97  ------ Propositional Solver
% 1.73/0.97  
% 1.73/0.97  prop_solver_calls:                      26
% 1.73/0.97  prop_fast_solver_calls:                 488
% 1.73/0.97  smt_solver_calls:                       0
% 1.73/0.97  smt_fast_solver_calls:                  0
% 1.73/0.97  prop_num_of_clauses:                    1028
% 1.73/0.97  prop_preprocess_simplified:             3849
% 1.73/0.97  prop_fo_subsumed:                       2
% 1.73/0.97  prop_solver_time:                       0.
% 1.73/0.97  smt_solver_time:                        0.
% 1.73/0.97  smt_fast_solver_time:                   0.
% 1.73/0.97  prop_fast_solver_time:                  0.
% 1.73/0.97  prop_unsat_core_time:                   0.
% 1.73/0.97  
% 1.73/0.97  ------ QBF
% 1.73/0.97  
% 1.73/0.97  qbf_q_res:                              0
% 1.73/0.97  qbf_num_tautologies:                    0
% 1.73/0.97  qbf_prep_cycles:                        0
% 1.73/0.97  
% 1.73/0.97  ------ BMC1
% 1.73/0.97  
% 1.73/0.97  bmc1_current_bound:                     -1
% 1.73/0.97  bmc1_last_solved_bound:                 -1
% 1.73/0.97  bmc1_unsat_core_size:                   -1
% 1.73/0.97  bmc1_unsat_core_parents_size:           -1
% 1.73/0.97  bmc1_merge_next_fun:                    0
% 1.73/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.73/0.97  
% 1.73/0.97  ------ Instantiation
% 1.73/0.97  
% 1.73/0.97  inst_num_of_clauses:                    369
% 1.73/0.97  inst_num_in_passive:                    106
% 1.73/0.97  inst_num_in_active:                     110
% 1.73/0.97  inst_num_in_unprocessed:                153
% 1.73/0.97  inst_num_of_loops:                      120
% 1.73/0.97  inst_num_of_learning_restarts:          0
% 1.73/0.97  inst_num_moves_active_passive:          9
% 1.73/0.97  inst_lit_activity:                      0
% 1.73/0.97  inst_lit_activity_moves:                0
% 1.73/0.97  inst_num_tautologies:                   0
% 1.73/0.97  inst_num_prop_implied:                  0
% 1.73/0.97  inst_num_existing_simplified:           0
% 1.73/0.97  inst_num_eq_res_simplified:             0
% 1.73/0.97  inst_num_child_elim:                    0
% 1.73/0.97  inst_num_of_dismatching_blockings:      70
% 1.73/0.97  inst_num_of_non_proper_insts:           278
% 1.73/0.97  inst_num_of_duplicates:                 0
% 1.73/0.97  inst_inst_num_from_inst_to_res:         0
% 1.73/0.97  inst_dismatching_checking_time:         0.
% 1.73/0.97  
% 1.73/0.97  ------ Resolution
% 1.73/0.97  
% 1.73/0.97  res_num_of_clauses:                     0
% 1.73/0.97  res_num_in_passive:                     0
% 1.73/0.97  res_num_in_active:                      0
% 1.73/0.97  res_num_of_loops:                       84
% 1.73/0.97  res_forward_subset_subsumed:            29
% 1.73/0.97  res_backward_subset_subsumed:           0
% 1.73/0.97  res_forward_subsumed:                   0
% 1.73/0.97  res_backward_subsumed:                  0
% 1.73/0.97  res_forward_subsumption_resolution:     0
% 1.73/0.97  res_backward_subsumption_resolution:    0
% 1.73/0.97  res_clause_to_clause_subsumption:       227
% 1.73/0.97  res_orphan_elimination:                 0
% 1.73/0.97  res_tautology_del:                      16
% 1.73/0.97  res_num_eq_res_simplified:              0
% 1.73/0.97  res_num_sel_changes:                    0
% 1.73/0.97  res_moves_from_active_to_pass:          0
% 1.73/0.97  
% 1.73/0.97  ------ Superposition
% 1.73/0.97  
% 1.73/0.97  sup_time_total:                         0.
% 1.73/0.97  sup_time_generating:                    0.
% 1.73/0.97  sup_time_sim_full:                      0.
% 1.73/0.97  sup_time_sim_immed:                     0.
% 1.73/0.97  
% 1.73/0.97  sup_num_of_clauses:                     33
% 1.73/0.97  sup_num_in_active:                      21
% 1.73/0.97  sup_num_in_passive:                     12
% 1.73/0.97  sup_num_of_loops:                       22
% 1.73/0.97  sup_fw_superposition:                   20
% 1.73/0.97  sup_bw_superposition:                   12
% 1.73/0.97  sup_immediate_simplified:               6
% 1.73/0.97  sup_given_eliminated:                   0
% 1.73/0.97  comparisons_done:                       0
% 1.73/0.97  comparisons_avoided:                    8
% 1.73/0.97  
% 1.73/0.97  ------ Simplifications
% 1.73/0.97  
% 1.73/0.97  
% 1.73/0.97  sim_fw_subset_subsumed:                 0
% 1.73/0.97  sim_bw_subset_subsumed:                 0
% 1.73/0.97  sim_fw_subsumed:                        2
% 1.73/0.97  sim_bw_subsumed:                        0
% 1.73/0.97  sim_fw_subsumption_res:                 1
% 1.73/0.97  sim_bw_subsumption_res:                 0
% 1.73/0.97  sim_tautology_del:                      0
% 1.73/0.97  sim_eq_tautology_del:                   3
% 1.73/0.97  sim_eq_res_simp:                        0
% 1.73/0.97  sim_fw_demodulated:                     2
% 1.73/0.97  sim_bw_demodulated:                     1
% 1.73/0.97  sim_light_normalised:                   3
% 1.73/0.97  sim_joinable_taut:                      0
% 1.73/0.97  sim_joinable_simp:                      0
% 1.73/0.97  sim_ac_normalised:                      0
% 1.73/0.97  sim_smt_subsumption:                    0
% 1.73/0.97  
%------------------------------------------------------------------------------
