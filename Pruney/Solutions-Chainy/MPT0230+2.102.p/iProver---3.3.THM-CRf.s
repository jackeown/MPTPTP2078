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
% DateTime   : Thu Dec  3 11:30:54 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 112 expanded)
%              Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  212 ( 371 expanded)
%              Number of equality atoms :  161 ( 286 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK2 != sK4
      & sK2 != sK3
      & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( sK2 != sK4
    & sK2 != sK3
    & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f36])).

fof(f70,plain,(
    r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f62,f74])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f100,plain,(
    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f70,f75,f74])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f73,f64,f75])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f97,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f60,f64,f64])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f101,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f87])).

fof(f102,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f101])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f64])).

fof(f107,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f72,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_152,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_284,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
    | k2_enumset1(sK2,sK2,sK2,sK2) != X1
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_152,c_26])).

cnf(c_285,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_0,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2305,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k1_xboole_0) = k2_enumset1(sK3,sK3,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_285,c_0])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4321,plain,
    ( k2_enumset1(sK3,sK3,sK4,sK2) = k2_enumset1(sK3,sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_2305,c_5])).

cnf(c_21,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4343,plain,
    ( k2_enumset1(sK3,sK3,sK4,sK2) = k2_enumset1(sK4,sK4,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_4321,c_21])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1959,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4530,plain,
    ( r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4343,c_1959])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2051,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(X0,X0,X1,sK3))
    | sK2 = X0
    | sK2 = X1
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2111,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(X0,X0,sK3,sK3))
    | sK2 = X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_2051])).

cnf(c_3037,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,sK3))
    | sK2 = sK3
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_3038,plain,
    ( sK2 = sK3
    | sK2 = sK4
    | r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3037])).

cnf(c_24,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f71])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4530,c_3038,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:44:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.63/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.00  
% 3.63/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/1.00  
% 3.63/1.00  ------  iProver source info
% 3.63/1.00  
% 3.63/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.63/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/1.00  git: non_committed_changes: false
% 3.63/1.00  git: last_make_outside_of_git: false
% 3.63/1.00  
% 3.63/1.00  ------ 
% 3.63/1.00  ------ Parsing...
% 3.63/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/1.00  
% 3.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/1.00  ------ Proving...
% 3.63/1.00  ------ Problem Properties 
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  clauses                                 26
% 3.63/1.00  conjectures                             2
% 3.63/1.00  EPR                                     2
% 3.63/1.00  Horn                                    22
% 3.63/1.00  unary                                   16
% 3.63/1.00  binary                                  1
% 3.63/1.00  lits                                    49
% 3.63/1.00  lits eq                                 35
% 3.63/1.00  fd_pure                                 0
% 3.63/1.00  fd_pseudo                               0
% 3.63/1.00  fd_cond                                 0
% 3.63/1.00  fd_pseudo_cond                          7
% 3.63/1.00  AC symbols                              0
% 3.63/1.00  
% 3.63/1.00  ------ Input Options Time Limit: Unbounded
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  ------ 
% 3.63/1.00  Current options:
% 3.63/1.00  ------ 
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  ------ Proving...
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  % SZS status Theorem for theBenchmark.p
% 3.63/1.00  
% 3.63/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.63/1.00  
% 3.63/1.00  fof(f1,axiom,(
% 3.63/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f25,plain,(
% 3.63/1.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.63/1.00    inference(nnf_transformation,[],[f1])).
% 3.63/1.00  
% 3.63/1.00  fof(f39,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f25])).
% 3.63/1.00  
% 3.63/1.00  fof(f2,axiom,(
% 3.63/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f40,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.63/1.00    inference(cnf_transformation,[],[f2])).
% 3.63/1.00  
% 3.63/1.00  fof(f79,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 3.63/1.00    inference(definition_unfolding,[],[f39,f40])).
% 3.63/1.00  
% 3.63/1.00  fof(f20,conjecture,(
% 3.63/1.00    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f21,negated_conjecture,(
% 3.63/1.00    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.63/1.00    inference(negated_conjecture,[],[f20])).
% 3.63/1.00  
% 3.63/1.00  fof(f24,plain,(
% 3.63/1.00    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.63/1.00    inference(ennf_transformation,[],[f21])).
% 3.63/1.00  
% 3.63/1.00  fof(f36,plain,(
% 3.63/1.00    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK2 != sK4 & sK2 != sK3 & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4)))),
% 3.63/1.00    introduced(choice_axiom,[])).
% 3.63/1.00  
% 3.63/1.00  fof(f37,plain,(
% 3.63/1.00    sK2 != sK4 & sK2 != sK3 & r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 3.63/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f36])).
% 3.63/1.00  
% 3.63/1.00  fof(f70,plain,(
% 3.63/1.00    r1_tarski(k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 3.63/1.00    inference(cnf_transformation,[],[f37])).
% 3.63/1.00  
% 3.63/1.00  fof(f12,axiom,(
% 3.63/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f62,plain,(
% 3.63/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f12])).
% 3.63/1.00  
% 3.63/1.00  fof(f75,plain,(
% 3.63/1.00    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.63/1.00    inference(definition_unfolding,[],[f62,f74])).
% 3.63/1.00  
% 3.63/1.00  fof(f13,axiom,(
% 3.63/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f63,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f13])).
% 3.63/1.00  
% 3.63/1.00  fof(f14,axiom,(
% 3.63/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f64,plain,(
% 3.63/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f14])).
% 3.63/1.00  
% 3.63/1.00  fof(f74,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.63/1.00    inference(definition_unfolding,[],[f63,f64])).
% 3.63/1.00  
% 3.63/1.00  fof(f100,plain,(
% 3.63/1.00    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4))),
% 3.63/1.00    inference(definition_unfolding,[],[f70,f75,f74])).
% 3.63/1.00  
% 3.63/1.00  fof(f11,axiom,(
% 3.63/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 3.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f61,plain,(
% 3.63/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f11])).
% 3.63/1.00  
% 3.63/1.00  fof(f7,axiom,(
% 3.63/1.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f45,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f7])).
% 3.63/1.00  
% 3.63/1.00  fof(f73,plain,(
% 3.63/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.63/1.00    inference(definition_unfolding,[],[f45,f40])).
% 3.63/1.00  
% 3.63/1.00  fof(f78,plain,(
% 3.63/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.63/1.00    inference(definition_unfolding,[],[f61,f73,f64,f75])).
% 3.63/1.00  
% 3.63/1.00  fof(f5,axiom,(
% 3.63/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f43,plain,(
% 3.63/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.63/1.00    inference(cnf_transformation,[],[f5])).
% 3.63/1.00  
% 3.63/1.00  fof(f10,axiom,(
% 3.63/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 3.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f60,plain,(
% 3.63/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 3.63/1.00    inference(cnf_transformation,[],[f10])).
% 3.63/1.00  
% 3.63/1.00  fof(f97,plain,(
% 3.63/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0)) )),
% 3.63/1.00    inference(definition_unfolding,[],[f60,f64,f64])).
% 3.63/1.00  
% 3.63/1.00  fof(f8,axiom,(
% 3.63/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/1.00  
% 3.63/1.00  fof(f23,plain,(
% 3.63/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.63/1.00    inference(ennf_transformation,[],[f8])).
% 3.63/1.00  
% 3.63/1.00  fof(f26,plain,(
% 3.63/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.63/1.00    inference(nnf_transformation,[],[f23])).
% 3.63/1.00  
% 3.63/1.00  fof(f27,plain,(
% 3.63/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.63/1.00    inference(flattening,[],[f26])).
% 3.63/1.00  
% 3.63/1.00  fof(f28,plain,(
% 3.63/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.63/1.00    inference(rectify,[],[f27])).
% 3.63/1.00  
% 3.63/1.00  fof(f29,plain,(
% 3.63/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.63/1.00    introduced(choice_axiom,[])).
% 3.63/1.00  
% 3.63/1.00  fof(f30,plain,(
% 3.63/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.63/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.63/1.00  
% 3.63/1.00  fof(f49,plain,(
% 3.63/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.63/1.00    inference(cnf_transformation,[],[f30])).
% 3.63/1.00  
% 3.63/1.00  fof(f87,plain,(
% 3.63/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.63/1.00    inference(definition_unfolding,[],[f49,f64])).
% 3.63/1.00  
% 3.63/1.00  fof(f101,plain,(
% 3.63/1.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 3.63/1.00    inference(equality_resolution,[],[f87])).
% 3.63/1.00  
% 3.63/1.00  fof(f102,plain,(
% 3.63/1.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 3.63/1.00    inference(equality_resolution,[],[f101])).
% 3.63/1.00  
% 3.63/1.00  fof(f46,plain,(
% 3.63/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.63/1.00    inference(cnf_transformation,[],[f30])).
% 3.63/1.00  
% 3.63/1.00  fof(f90,plain,(
% 3.63/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.63/1.00    inference(definition_unfolding,[],[f46,f64])).
% 3.63/1.00  
% 3.63/1.00  fof(f107,plain,(
% 3.63/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.63/1.00    inference(equality_resolution,[],[f90])).
% 3.63/1.00  
% 3.63/1.00  fof(f72,plain,(
% 3.63/1.00    sK2 != sK4),
% 3.63/1.00    inference(cnf_transformation,[],[f37])).
% 3.63/1.00  
% 3.63/1.00  fof(f71,plain,(
% 3.63/1.00    sK2 != sK3),
% 3.63/1.00    inference(cnf_transformation,[],[f37])).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1,plain,
% 3.63/1.00      ( ~ r1_tarski(X0,X1)
% 3.63/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.63/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_152,plain,
% 3.63/1.00      ( ~ r1_tarski(X0,X1)
% 3.63/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.63/1.00      inference(prop_impl,[status(thm)],[c_1]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_26,negated_conjecture,
% 3.63/1.00      ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.63/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_284,plain,
% 3.63/1.00      ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
% 3.63/1.00      | k2_enumset1(sK2,sK2,sK2,sK2) != X1
% 3.63/1.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k1_xboole_0 ),
% 3.63/1.00      inference(resolution_lifted,[status(thm)],[c_152,c_26]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_285,plain,
% 3.63/1.00      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK4))) = k1_xboole_0 ),
% 3.63/1.00      inference(unflattening,[status(thm)],[c_284]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_0,plain,
% 3.63/1.00      ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2)))) = k2_enumset1(X0,X1,X2,X3) ),
% 3.63/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2305,plain,
% 3.63/1.00      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k1_xboole_0) = k2_enumset1(sK3,sK3,sK4,sK2) ),
% 3.63/1.00      inference(superposition,[status(thm)],[c_285,c_0]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_5,plain,
% 3.63/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.63/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4321,plain,
% 3.63/1.00      ( k2_enumset1(sK3,sK3,sK4,sK2) = k2_enumset1(sK3,sK3,sK3,sK4) ),
% 3.63/1.00      inference(superposition,[status(thm)],[c_2305,c_5]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_21,plain,
% 3.63/1.00      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X2,X2,X1,X0) ),
% 3.63/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4343,plain,
% 3.63/1.00      ( k2_enumset1(sK3,sK3,sK4,sK2) = k2_enumset1(sK4,sK4,sK3,sK3) ),
% 3.63/1.00      inference(superposition,[status(thm)],[c_4321,c_21]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_11,plain,
% 3.63/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 3.63/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_1959,plain,
% 3.63/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_4530,plain,
% 3.63/1.00      ( r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,sK3)) = iProver_top ),
% 3.63/1.00      inference(superposition,[status(thm)],[c_4343,c_1959]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_14,plain,
% 3.63/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.63/1.00      | X0 = X1
% 3.63/1.00      | X0 = X2
% 3.63/1.00      | X0 = X3 ),
% 3.63/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2051,plain,
% 3.63/1.00      ( ~ r2_hidden(sK2,k2_enumset1(X0,X0,X1,sK3))
% 3.63/1.00      | sK2 = X0
% 3.63/1.00      | sK2 = X1
% 3.63/1.00      | sK2 = sK3 ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_2111,plain,
% 3.63/1.00      ( ~ r2_hidden(sK2,k2_enumset1(X0,X0,sK3,sK3))
% 3.63/1.00      | sK2 = X0
% 3.63/1.00      | sK2 = sK3 ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2051]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3037,plain,
% 3.63/1.00      ( ~ r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,sK3))
% 3.63/1.00      | sK2 = sK3
% 3.63/1.00      | sK2 = sK4 ),
% 3.63/1.00      inference(instantiation,[status(thm)],[c_2111]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_3038,plain,
% 3.63/1.00      ( sK2 = sK3
% 3.63/1.00      | sK2 = sK4
% 3.63/1.00      | r2_hidden(sK2,k2_enumset1(sK4,sK4,sK3,sK3)) != iProver_top ),
% 3.63/1.00      inference(predicate_to_equality,[status(thm)],[c_3037]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_24,negated_conjecture,
% 3.63/1.00      ( sK2 != sK4 ),
% 3.63/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(c_25,negated_conjecture,
% 3.63/1.00      ( sK2 != sK3 ),
% 3.63/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.63/1.00  
% 3.63/1.00  cnf(contradiction,plain,
% 3.63/1.00      ( $false ),
% 3.63/1.00      inference(minisat,[status(thm)],[c_4530,c_3038,c_24,c_25]) ).
% 3.63/1.00  
% 3.63/1.00  
% 3.63/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.63/1.00  
% 3.63/1.00  ------                               Statistics
% 3.63/1.00  
% 3.63/1.00  ------ Selected
% 3.63/1.00  
% 3.63/1.00  total_time:                             0.167
% 3.63/1.00  
%------------------------------------------------------------------------------
